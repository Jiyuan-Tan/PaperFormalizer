module
public import StatLean.TimeSeries.Mixing.Inequalities
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import StatLean.TimeSeries.Mixing.Relations
public import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# CLT for kernel-localized sums under α-mixing (FY §2.6.4, Theorem 2.22)

The triangular-array CLT behind kernel regression with dependent data: for a strictly
stationary bivariate series `(X_t, e_t)` with `E(e|X) = 0`, the localized sums
`S_n(x) = Σ_{t=1}^n e_t W((X_t − x)/h_n)` satisfy
`(n h_n)^{-1/2} S_n(x) →d N(0, σ²(x) p(x) ∫ W²)` under (C1)–(C5). This is FY's
template for Theorem 6.3 (local-polynomial fitting) and the ch. 10 results.

**Conditions, as formalized.**
* (C1) joint strict stationarity (finite-dimensional-distribution form);
  `E(e_1 | X_1) = 0`, `E(e_1² | X_1) = σ²(X_1)`, `E|e_1|^δ < ∞` (δ > 2); the marginal
  `X_1` has a Lebesgue density `p`; `σ²`, `p` continuous at `x`, `p(x) > 0`.
* (C2) **as printed**, in its operative integrated form: uniformly in the lag `j ≠ 0`,
  `E[|f(e_0, e_j)| g(X_0, X_j)] ≤ B · E|f(e_0, e_j)| · ∫∫ g` for **every** measurable `f`
  and every nonnegative measurable `g`. This is exactly what "the conditional density of
  `(X_1, X_j)` given `(e_1, e_j)` is bounded uniformly in `j`" gives: condition on the
  errors, bound the conditional density of the `X`-pair by `B`, integrate the errors back
  out. The single instance `f = e_0 e_j` (plus `2|ab| ≤ a² + b²` and stationarity, which
  replace `E|e_0 e_j|` by `E[e_0²]`) is the small-lag variance bound (2.76); the *other*
  instances are what steps (b)–(c) need, because the conditional recentring inside
  `truncErr` strips the error factors out of the small-lag covariance (see
  `tendsto_smallBlock_variance`).
* (C3) α-mixing of the bivariate series (`pairAlphaCoeff`) with
  `Σ_t t^λ α(t)^{1−2/δ} < ∞` for some `λ > 1 − 2/δ`.
* (C4) `W` bounded and measurable with `∫|W| < ∞`, `∫ W² < ∞`.
* (C5) **as corrected**: the printed display is inverted; we take the endorsed
  sufficient form `h_n → 0`, `h_n > 0`, `n h_n³ → ∞` (which implies the intended
  polynomial lower bound `n h_n^{(λ+2−2/δ)/(λ+2/δ)} → ∞`).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.4,
conditions (C1)–(C5) and Theorem 2.22 (pp. 76–77); proof §2.7.7 (pp. 85–87).
(`FY §2.6.4 Thm 2.22`.)

**Proof route (§2.7.7, for the closure session).** (a) variance asymptotics
(2.73)–(2.76): main diagonal term by continuity of `σ²·p` + substitution; small lags
`j ≤ m_n = [1/(h|log h|)]` by (C2'); large lags by Davydov (`abs_covariance_le_davydov`
with `p = q = δ`) + (C3). (b) Bernstein blocks `l_n = [√(nh)/log n]`,
`s_n = [(√(n/h) log n)^{(1−2/δ)/(λ+1)}]`; negligibility (2.79)–(2.81) via the variance
part. (c) truncation of `e` at level `L`; variance split (2.82)–(2.83).
(d) 4-term charFun telescope: truncation tail + Volkonskii–Rozanov
(`norm_integral_prod_sub_prod_integral_le`; `16(k_n − 1)α(s_n) → 0` by (2.78)) +
degenerate Lindeberg (`tendsto_charFun_rowSum_gaussian_of_uniformly_small`; the
truncated block summands have envelope `l_n L sup|W| / √(nh) → 0`) + `ν_L → ν`.
Sub-steps may be left as **named ledger-(a) debts** if the wave budget is hit.
[Print slips (recorded in the inventory): Term-1 of the telescope is missing a `½`
exponent; the final "(2.83)" should read "(2.84)".]

**Status of the ledger.** `kernel_localized_clt` is assembled (no `sorry` of its own)
from the two step-(d) inputs through the proved `tendsto_of_uniform_approx`. Proved in
full: the four analytic bricks (`integral_dilate_translate`,
`integral_comp_eq_integral_density`, `integral_bdd_comp_mul_eq_of_condExp`,
`tendsto_integral_dilate_of_bounded`), the repaired diagonal
`tendsto_localized_second_moment_of_bounded`, the small-lag bound (2.76)
`small_lag_covariance_bound`, the large-lag Davydov bound (2.75)
`large_lag_covariance_bound`, the pair-σ-algebra transport, and the `pairAlphaCoeff`
basics; and, under the authorized (C1) repair, the diagonal (2.73) itself
(`tendsto_localized_second_moment_debt`, with `nonneg_of_continuousAt_of_ae_nonneg`);
and the Volkonskii–Rozanov rate (2.78) `tendsto_blockCount_mul_pairAlpha`, with its
(C3) input `tendsto_weighted_antitone_of_summable`; and, under the authorized (2.74)
repair, **the whole of ledger (a)**: `var_localized_sum`, together with its apparatus
— the fdd-stationarity law transport (`map_pair_eq_of_stat`, `integral_comp_pair_eq`,
`map_pair2_eq_of_stat`, `integral_comp_pair2_eq`, `eLpNorm_comp_pair_eq`,
`memLp_comp_pair`), the stationary double-sum estimates `abs_double_sum_sub_diag_le` and
`abs_double_sum_subset_le`, the localized δ-moment `localized_delta_moment_le` (this is
(2.74) itself), the truncation-tail diagonal `sq_sub_clamp_le` /
`localized_trunc_residual_moment_le`, and the bandwidth limits
`tendsto_smallLagCut_mul_bandwidth`, `tendsto_rpow_mul_abs_log_rpow`.

**New this wave** — the *time-transport* apparatus that steps (b)–(c) need and ledger (a)
did not, all proved and axiom-clean:
* `map_fst_eq_of_stat`, `ae_comp_X_of_stat` — the `X`-marginal and a.e. statements about it
  move across time;
* `exists_condExp_repr_of_stat` — under fdd stationarity `E(φ(e_t) | X_t)` is the **same**
  measurable function of `X_t` at every `t` (Doob–Dynkin at `t = 0`, then the set-integral
  characterization transports because both sides are integrals of a fixed function of the
  pair);
* `condExp_eq_zero_of_stat` — (C1)'s `E(e | X) = 0` at *every* time, not just `t = 0`;
* `measurable_clampAt`, `abs_clampAt_le`, `exists_truncErr_repr` — one bounded measurable
  `mL` with `e^L_t = clamp_L(e_t) − mL(X_t)` a.e. simultaneously in `t`, so that the
  truncated covariance array is a function of the lag alone;
* `localized_weight_integral_le` — `E[G((X_0 − x)/h)] ≤ (C_p ∫G) h`, the `Y ≡ 1` case of the
  density change of variables (at `G = |W|^δ` it is the truncated summand's δ-th moment: no
  conditional moment is needed there, the error factor being bounded by `2L`).

The three former debts, each with its verified falsity witness and its
**Statement strengthening (documented)** paragraph in its own docstring. All three were
**false as frozen**; all three statements were **repaired**, and the repairs are exactly the
ones the witnesses prescribe. **All three are now PROVED, and the file is `sorry`-free**:
* `tendsto_smallBlock_variance` (2.79)–(2.81) — was hypothesis-free; now carries the full
  (C1)–(C5) package plus `0 < L`, and (C2) in its printed form (the second obstruction: the
  conditional recentring inside `truncErr` strips both error factors out of the small-lag
  covariance, so the *unweighted* instance `f ≡ 1` is what closes it). **PROVED (this wave),
  in the repaired form.** The route recorded here was run as written: (i) the covariance
  assembly for the truncated array — diagonal `|G_ζ(0)| ≤ 4L² C_p (∫W²) h` from
  `localized_weight_integral_le`, small lags from (C2) at `f ≡ 1`, large lags from Davydov
  (`large_lag_covariance_bound'`) as in ledger (a) — is `tendsto_truncIndex_variance`, stated
  for an *arbitrary* index family `I n ⊆ range n` with `|I n| / n → 0`; and (ii) the numerology
  `k_n s_n / n → 0` (`tendsto_blockCount_mul_smallBlockLen_div`) reduces to `s_n / l_n → 0` and
  thence to `n^{1−θ} h^{1+θ} / (log n)^{2+2θ} → ∞` with `θ = (1−2/δ)/(λ+1) < 1/2`; that in turn
  is `(n h³)^{(1+θ)/3} · n^{(2−4θ)/3} / (log n)^{2+2θ} → ∞`, i.e. exactly (C5) with room to
  spare.
* `charFun_locSum_sub_locTruncSum_le` (2.82)–(2.83) — was missing stationarity and every
  moment condition beyond time `0`; now carries the same package. **PROVED (this wave), in
  the repaired form**, by the route recorded below, run as written.
  Route: `‖e^{iuS} − e^{iuT}‖ ≤ |u| E|S − T|` and `|z| ≤ z²/(2c) + c/2` (no square root
  needed), then the residual array `ρ_t = (r_t − E(r_t|X_t)) W_t`, `r_t = e_t − clamp_L e_t`,
  with `E(e_t|X_t) = 0` supplied at every `t` by `condExp_eq_zero_of_stat`. Diagonal:
  `localized_trunc_residual_moment_le`, `O(L^{2−δ})` after the `h⁻¹`, uniformly in `n`.
  Small lags: (C2) at `f(z) = (|r(z.1)| + c)(|r(z.2)| + c)` with `c = L^{1−δ}M` (the pointwise
  bound `|r_0| ≤ L^{1−δ}|e_0|^δ` is what makes the recentring constant decay in `L`).
  Large lags: Davydov; note the δ-moment constant there does **not** decay in `L` under
  `heδc`, so the uniformity in `n` has to be obtained by splitting at some `N` (large `n`:
  the factor `h^{2/δ−1+λ}|log h|^λ` is itself small; small `n`: the crude bound
  `E|S_n − T_n| ≤ √(n/h_n) C_W · 2L^{1−δ}M` closes at fixed `n`). This is recorded because it
  is *not* a further silent reading — the frozen package suffices, but only after the split.
* `tendsto_charFun_locTruncSum` ((b) + (d) at fixed `L`, and (2.84)) — was refutable already
  for an iid series: at a fixed truncation level the limit needs continuity at `x` of the
  *truncated* conditional second moment `σ_L²·p`, which (C1) does not supply. Repaired by the
  `mL`/`sL` family with `hσLc`, `hσLb`, `hσL84`. **PROVED (this wave), in the repaired
  form.** The Bernstein-block core was run in full; see its docstring for the route and the
  private apparatus it required.

With that, the **headline** `kernel_localized_clt` — FY Theorem 2.22 — is proved outright.
What the three verdicts say is that FY §2.7.7's *route* to it needs four silent readings of
(C1) and (C2) as printed, not two.

**Note on `Mixing/Inequalities.lean`.** The sibling repair — making the frozen
`norm_integral_prod_sub_prod_integral_le` the `0 < k` statement (its `k = 0` corner is
false: `‖1 − 1‖ = 0 ≤ 16·(0−1)·a` fails for `a > 0`) — was attempted this wave and
**reverted**: `StatLean/TimeSeries/Mixing/LimitTheorems.lean:998`
(`norm_integral_prod_blocks_sub_prod_le`, private, and itself false at `k = 0` for the same
reason) consumes the frozen name at unconstrained `k`, and that file is outside this wave's
touch-set. The repair is one line in each of the two files; the content is already available
as `norm_integral_prod_sub_prod_integral_le_of_pos`.

**FALSE AS FROZEN (verified) — REPAIRS APPLIED.** FY (2.73)–(2.76) — hence Theorem 2.22
itself — does not follow from (C1)–(C5) *as formalized here*. Two independent gaps were
found and both counterexamples/obstructions stand; the authorized amendments of (C1) have
been applied to `kernel_localized_clt`, `tendsto_localized_second_moment_debt`,
`var_localized_sum` and `tendsto_charFun_locTruncSum`:

* the **second**-moment gap, repaired by `(hσm : Measurable σsq)` and
  `(hσpb : ∃ C, ∀ v, σsq v * p v ≤ C)`. Under them the diagonal (2.73) is **proved**
  (`tendsto_localized_second_moment_debt`); note that only the *upper* half of the bound is
  assumed — the lower half is derived from `σ²` being a conditional second moment. The
  record of the failure as frozen is below.
* the **δ**-th-moment gap, FY's implicit (2.74), repaired by
  `(heδc : μ[|e 0|^δ | σ(X 0)] ≤ᵐ M)` together with `(hpb : ∀ v, p v ≤ Cp)`. Under them
  ledger (a) `var_localized_sum` is **proved**. The obstruction proof — that no combination
  of the frozen inputs closes the large-lag sum for `λ ≤ 1`, which is the range (C3)
  actually allows — is kept in `var_localized_sum`'s docstring.

The record of the second-moment failure as frozen:

The diagonal term equals, identically,
`∫ (σ²·p)(x + h u) W²(u) du` (this identity is proved, inside
`tendsto_localized_second_moment_of_bounded`), and its convergence to `σ²(x)p(x)∫W²`
needs control of the range `|u| > M`, which continuity of `σ²·p` **at `x`** does not
give. (C2) forces only `σ·p` bounded, never `σ²·p`; and `σ²·p ∈ L¹` (`= E e_0² < ∞`) is
too weak against a merely-`L¹` weight `W²`. See
`tendsto_localized_second_moment_debt`'s docstring for the explicit spike/kernel
counterexample and the two possible repairs (compactly supported `W`, or `σ²·p`
bounded — the latter is the textbook's silent reading of (C1)). Note also that (C1) as
frozen carries **no measurability hypothesis on `σsq`**; only `hcv` constrains it, and
only `μ.map (X 0)`-a.e.

**Bibliographic comments.** Theorem 2.22 descends from Masry & Fan, *Local polynomial
estimation of regression functions for mixing processes* (Scand. J. Statist. 1997) and
Fan & Gijbels (1996) §6.5; the Bernstein-block scheme under (C3) follows Bosq (1998).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **bivariate past/future α-coefficient** (FY §2.6.4's mixing condition is on the
pair series `(X_t, e_t)`): α between `σ{(X_s, e_s) : s ≤ 0}` and
`σ{(X_s, e_s) : s ≥ n}`. -/
noncomputable def pairAlphaCoeff (X e : ℤ → Ω → ℝ) (μ : Measure Ω) (n : ℕ) : ℝ :=
  alphaMixCoeff μ
    (⨆ s ∈ Set.Iic (0 : ℤ),
      MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance)
    (⨆ s ∈ Set.Ici (n : ℤ),
      MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance)

/-! ### Elementary properties of `pairAlphaCoeff`

Transported from the `alphaMixCoeff` lemmas of `Mixing/Relations.lean`; the pair
σ-algebras are `⨆`-sups, so `iSup_le`/`le_iSup` do the monotonicity transport. -/

section PairAlpha

variable {X e : ℤ → Ω → ℝ}

/-- `pairAlphaCoeff` is nonnegative (FY §2.6.4). -/
theorem pairAlphaCoeff_nonneg [IsProbabilityMeasure μ] (X e : ℤ → Ω → ℝ) (n : ℕ) :
    0 ≤ pairAlphaCoeff X e μ n :=
  alphaMixCoeff_nonneg (mΩ := inferInstance)

/-- `pairAlphaCoeff ≤ 1` (FY §2.6.4). -/
theorem pairAlphaCoeff_le_one [IsProbabilityMeasure μ] (X e : ℤ → Ω → ℝ) (n : ℕ) :
    pairAlphaCoeff X e μ n ≤ 1 :=
  alphaMixCoeff_le_one (mΩ := inferInstance)

/-- `pairAlphaCoeff` is antitone in the lag: the future σ-algebra shrinks as the gap
grows, so the sup defining `α` is taken over a smaller set. -/
theorem pairAlphaCoeff_antitone [IsProbabilityMeasure μ] (X e : ℤ → Ω → ℝ) :
    Antitone (pairAlphaCoeff X e μ) := by
  intro m n hmn
  refine alphaMixCoeff_mono (mΩ := inferInstance) le_rfl ?_
  refine iSup₂_le fun s hs => le_iSup₂_of_le s ?_ le_rfl
  simp only [Set.mem_Ici] at hs ⊢
  exact le_trans (by exact_mod_cast hmn) hs

end PairAlpha

/-! ### Analytic bricks for the variance asymptotics (a)

Four reusable identities/limits behind FY (2.73): the affine change of variables
`v = x + h u`, the substitution of the `X`-marginal density `p`, the conditional
(tower) elimination of the errors against a bounded `X`-measurable weight, and the
dominated-convergence localization. All four are **proved**. -/

section Bricks

/-- **Affine change of variables** `v = x + h u` on Lebesgue measure:
`∫ F(u) g(x + h u) du = h⁻¹ ∫ F((v − x)/h) g(v) dv` for `h > 0`.
(Both sides use Mathlib's junk value `0` for non-integrable integrands, and the
identity holds regardless — `Measure.integral_comp_mul_left` is unconditional.) -/
theorem integral_dilate_translate (F g : ℝ → ℝ) (x : ℝ) {h : ℝ} (hh : 0 < h) :
    ∫ u, F u * g (x + h * u) = h⁻¹ * ∫ v, F ((v - x) / h) * g v := by
  set G : ℝ → ℝ := fun v => F ((v - x) / h) * g v with hG
  have h1 : ∫ u, G (x + h * u) = |h⁻¹| • ∫ w, G (x + w) :=
    MeasureTheory.Measure.integral_comp_mul_left (fun w => G (x + w)) h
  have h2 : ∫ w, G (x + w) = ∫ v, G v := integral_add_left_eq_self G x
  have h3 : ∀ u : ℝ, G (x + h * u) = F u * g (x + h * u) := by
    intro u
    simp [hG, add_sub_cancel_left, mul_div_cancel_left₀ _ hh.ne']
  calc ∫ u, F u * g (x + h * u) = ∫ u, G (x + h * u) := by simp_rw [h3]
    _ = |h⁻¹| • ∫ w, G (x + w) := h1
    _ = h⁻¹ * ∫ v, G v := by rw [h2, abs_of_pos (by positivity), smul_eq_mul]

/-- **Density substitution for the `X`-marginal** (FY (C1)): if `X` has Lebesgue
density `p`, then `E[F(X)] = ∫ p(v) F(v) dv`. -/
theorem integral_comp_eq_integral_density {Y : Ω → ℝ} (hY : Measurable Y)
    {p : ℝ → ℝ} (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map Y = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (F : ℝ → ℝ) (hF : Measurable F) :
    ∫ ω, F (Y ω) ∂μ = ∫ v, p v * F v := by
  rw [← integral_map hY.aemeasurable hF.aestronglyMeasurable, hpd,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun v => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hp0 v)]

/-- **Tower elimination against a bounded `σ(Y)`-measurable weight**: if
`μ[ζ | σ(Y)] =ᵐ Z` and `G` is bounded measurable, then `E[G(Y) ζ] = E[G(Y) Z]`.
Used twice: with `ζ = e₀` (giving mean zero of each localized summand, FY (C1)
`E(e|X) = 0`) and with `ζ = e₀²` (giving the `σ²(X)` form of the diagonal term). -/
theorem integral_bdd_comp_mul_eq_of_condExp [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (hY : Measurable Y) {Z ζ : Ω → ℝ} (hζ : Integrable ζ μ)
    (hce : μ[ζ | MeasurableSpace.comap Y inferInstance] =ᵐ[μ] Z)
    (G : ℝ → ℝ) (hG : Measurable G) {C : ℝ} (hGb : ∀ v, |G v| ≤ C) :
    ∫ ω, G (Y ω) * ζ ω ∂μ = ∫ ω, G (Y ω) * Z ω ∂μ := by
  have hmle : MeasurableSpace.comap Y inferInstance ≤ ‹MeasurableSpace Ω› := hY.comap_le
  have hYm : Measurable[MeasurableSpace.comap Y inferInstance] Y :=
    Measurable.of_comap_le le_rfl
  have hf : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] (fun ω => G (Y ω)) :=
    (hG.comp hYm).stronglyMeasurable
  have hpull := condExp_stronglyMeasurable_mul_of_bound (μ := μ)
    (m := MeasurableSpace.comap Y inferInstance) hmle hf hζ C
    (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hGb (Y ω))
  have h1 : ∫ ω, G (Y ω) * ζ ω ∂μ
      = ∫ ω, (μ[(fun ω => G (Y ω)) * ζ | MeasurableSpace.comap Y inferInstance]) ω ∂μ :=
    (integral_condExp hmle).symm
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [hpull, hce] with ω h1 h2
  simp only [Pi.mul_apply] at h1 ⊢
  rw [h1, h2]

/-- **Dominated-convergence localization**: for `g` measurable, globally bounded and
continuous at `x`, and a nonnegative integrable weight `Φ`,
`∫ g(x + h_n u) Φ(u) du → g(x) ∫ Φ` whenever `h_n → 0`.
This is the analytic core of FY (2.73). -/
theorem tendsto_integral_dilate_of_bounded {g : ℝ → ℝ} (hg : Measurable g) {x : ℝ}
    (hgc : ContinuousAt g x) {M : ℝ} (hgM : ∀ v, |g v| ≤ M)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ0 : ∀ u, 0 ≤ Φ u)
    (hΦ : Integrable Φ MeasureTheory.volume)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u, g (x + h n * u) * Φ u) atTop (𝓝 (g x * ∫ u, Φ u)) := by
  have hlim : ∫ u, g x * Φ u = g x * ∫ u, Φ u := integral_const_mul _ _
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (fun u => M * Φ u)
    (fun n => ((hg.comp (by fun_prop)).mul hΦm).aestronglyMeasurable)
    (hΦ.const_mul M) (fun n => Eventually.of_forall fun u => ?_)
    (Eventually.of_forall fun u => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hΦ0 u)]
    exact mul_le_mul_of_nonneg_right (hgM _) (hΦ0 u)
  · exact ((hgc.tendsto.comp (by simpa using (hh.mul_const u).const_add x)).mul
      tendsto_const_nhds)

/-- **FY (2.73), diagonal term — the TRUE form.** Under a *global bound* on `σ² · p`
(which FY's (C1) implicitly carries, and which the formalized (C1)–(C5) do **not**
supply — see `tendsto_localized_second_moment_debt`),
`h⁻¹ E[e₀² W²((X₀ − x)/h)] → σ²(x) p(x) ∫ W²`. -/
theorem tendsto_localized_second_moment_of_bounded [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0))
    {σsq p : ℝ → ℝ} (hmσ : Measurable σsq) (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {x : ℝ}
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (he2 : Integrable (fun ω => e 0 ω ^ 2) μ)
    (hgc : ContinuousAt (fun v => σsq v * p v) x)
    {M : ℝ} (hgM : ∀ v, |σsq v * p v| ≤ M)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) := by
  -- The `n`-th term equals `∫ (σ²·p)(x + h u) W²(u) du`.
  have hkey : ∀ n : ℕ, (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
      = ∫ u, (fun v => σsq v * p v) (x + h n * u) * W u ^ 2 := by
    intro n
    -- (i) tower: replace `e₀²` by `σ²(X₀)`.
    have hstep1 : ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
        = ∫ ω, (fun v => W ((v - x) / h n) ^ 2) (X 0 ω) * σsq (X 0 ω) ∂μ := by
      rw [← integral_bdd_comp_mul_eq_of_condExp hX he2 hcv
        (fun v => W ((v - x) / h n) ^ 2) (by fun_prop) (C := CW ^ 2)
        (fun v => by
          have hb := hWb ((v - x) / h n)
          rw [abs_pow]
          nlinarith [abs_nonneg (W ((v - x) / h n))])]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    -- (ii) density substitution.
    have hstep2 : ∫ ω, (fun v => W ((v - x) / h n) ^ 2) (X 0 ω) * σsq (X 0 ω) ∂μ
        = ∫ v, W ((v - x) / h n) ^ 2 * (σsq v * p v) := by
      rw [integral_comp_eq_integral_density hX hmp hp0 hpd
        (fun v => W ((v - x) / h n) ^ 2 * σsq v) (by fun_prop)]
      exact integral_congr_ae (Eventually.of_forall fun v => by ring)
    -- (iii) affine change of variables.
    have hstep3 := integral_dilate_translate (fun u => W u ^ 2)
      (fun v => σsq v * p v) x (hh0 n)
    rw [hstep1, hstep2, ← hstep3]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  simp only [hkey]
  have := tendsto_integral_dilate_of_bounded (g := fun v => σsq v * p v) (by fun_prop) hgc hgM
    (Φ := fun u => W u ^ 2) (by fun_prop) (fun u => sq_nonneg _) hW2 hh
  simpa [mul_assoc] using this

end Bricks

/-! ### The §2.7.7 ledger

The proof apparatus of FY §2.7.7, as named private declarations. `locSum` is the
statistic of Theorem 2.22 itself; `locTruncSum` is its truncated-and-recentred
companion of step (c); `bigBlockLen`/`smallBlockLen`/`blockCount`/`smallLagCut` are
FY's `l_n`, `s_n`, `k_n`, `m_n`.

**What is proved here**: the small-lag covariance bound (2.76) — the one ledger-(a)
item that the formalized (C2) delivers outright — and the abstract diagonal-limit
device that the four-term telescope of step (d) is squeezed through. The remaining
items are named debts, one per FY display. -/

section Ledger

/-- FY's localized statistic `(n h_n)^{-1/2} Σ_{t=1}^n e_t W((X_t − x)/h_n)`. -/
noncomputable def locSum (X e : ℤ → Ω → ℝ) (W : ℝ → ℝ) (x : ℝ) (h : ℕ → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt ((n : ℝ) * h n))⁻¹ *
    ∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)

/-- Two-sided clamp at level `L`. -/
noncomputable def clampAt (L z : ℝ) : ℝ := max (-L) (min L z)

/-- FY's truncated, conditionally recentred error `e^L_t = e_t^{(L)} − E(e_t^{(L)}|X_t)`
(step (c), (2.82)); the recentring keeps `E(e^L | X) = 0`, hence keeps every summand
of `locTruncSum` centred. -/
noncomputable def truncErr (X e : ℤ → Ω → ℝ) (μ : Measure Ω) (L : ℝ) (t : ℤ)
    (ω : Ω) : ℝ :=
  clampAt L (e t ω) -
    (μ[fun ω' => clampAt L (e t ω') | MeasurableSpace.comap (X t) inferInstance]) ω

/-- The truncated statistic of step (c). -/
noncomputable def locTruncSum (X e : ℤ → Ω → ℝ) (μ : Measure Ω) (W : ℝ → ℝ)
    (x : ℝ) (h : ℕ → ℝ) (L : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt ((n : ℝ) * h n))⁻¹ *
    ∑ t ∈ Finset.range n,
      truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)

/-- The clamp is measurable in the clamped variable. -/
theorem measurable_clampAt (L : ℝ) : Measurable (clampAt L) := by
  unfold clampAt; fun_prop

/-- The clamp is bounded by its level. -/
theorem abs_clampAt_le {L : ℝ} (hL : 0 ≤ L) (z : ℝ) : |clampAt L z| ≤ L := by
  unfold clampAt
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- FY's big-block length `l_n = [√(n h_n) / log n]` (step (b), (2.77)). -/
noncomputable def bigBlockLen (h : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈Real.sqrt ((n : ℝ) * h n) / Real.log n⌉₊

/-- FY's small-block length `s_n = [(√(n/h_n) log n)^{(1−2/δ)/(λ+1)}]` (step (b)). -/
noncomputable def smallBlockLen (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : ℕ :=
  ⌈(Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1))⌉₊

/-- FY's number of block pairs `k_n = [n / (l_n + s_n)]` (step (b)). -/
noncomputable def blockCount (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : ℕ :=
  n / (bigBlockLen h n + smallBlockLen h δ lam n)

/-- FY's small/large lag cut `m_n = [1 / (h_n |log h_n|)]` (step (a), before (2.75)). -/
noncomputable def smallLagCut (h : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈(h n * |Real.log (h n)|)⁻¹⌉₊

/-! #### σ-algebra transport for the pair series

The past/future σ-algebras of `pairAlphaCoeff` are `⨆`-sups over index sets; these three
lemmas are all the transport the Davydov step needs. -/

/-- Every pair σ-algebra sits below the ambient one. -/
theorem pairSigma_le {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t))
    (hmeasE : ∀ t, Measurable (e t)) (S : Set ℤ) :
    (⨆ s ∈ S, MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance) ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun s _ => sup_le (hmeasX s).comap_le (hmeasE s).comap_le

omit [MeasurableSpace Ω] in
/-- `X t` is measurable for the pair σ-algebra of any index set containing `t`. -/
theorem measurable_X_pairSigma {X e : ℤ → Ω → ℝ} {S : Set ℤ} {t : ℤ} (ht : t ∈ S) :
    Measurable[⨆ s ∈ S, MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance] (X t) :=
  (Measurable.of_comap_le le_rfl).mono (le_iSup₂_of_le t ht le_sup_left) le_rfl

omit [MeasurableSpace Ω] in
/-- `e t` is measurable for the pair σ-algebra of any index set containing `t`. -/
theorem measurable_e_pairSigma {X e : ℤ → Ω → ℝ} {S : Set ℤ} {t : ℤ} (ht : t ∈ S) :
    Measurable[⨆ s ∈ S, MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance] (e t) :=
  (Measurable.of_comap_le le_rfl).mono (le_iSup₂_of_le t ht le_sup_right) le_rfl

/-! #### Ledger (a): variance asymptotics (2.73)–(2.76) -/

/-- **FY (2.76), small-lag covariance bound — PROVED.** For every nonzero lag,
`|E[ξ_0 ξ_j]| ≤ B · E[e_0²] · (∫|W|)² · h²`, where `ξ_t = e_t W((X_t − x)/h)`. This is
exactly the operative content of (C2): bound `|ξ_0 ξ_j|` by `|e_0 e_j| g(X_0, X_j)`
with `g(v,w) = |W((v−x)/h)| |W((w−x)/h)|`, apply (C2), and evaluate
`∫∫ g = (h ∫|W|)²` by the affine change of variables. -/
theorem small_lag_covariance_bound {X e : ℤ → Ω → ℝ} {W : ℝ → ℝ} {x : ℝ}
    (hWm : Measurable W) {B : ℝ}
    (hC2 : ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {hn : ℝ} (hhn : 0 < hn) (j : ℤ) (hj : j ≠ 0) :
    |∫ ω, (e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn)) ∂μ|
      ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) * ((∫ v, |W v|) * hn) ^ 2 := by
  -- Step 1: pass to absolute values and factor the integrand as `|e₀ e_j| · g(X₀, X_j)`.
  have h0 := norm_integral_le_integral_norm (μ := μ)
    fun ω => (e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn))
  simp only [Real.norm_eq_abs] at h0
  have hcongr : ∫ ω, |(e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn))| ∂μ
      = ∫ ω, |e 0 ω * e j ω| *
          (fun z : ℝ × ℝ => |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|) (X 0 ω, X j ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by simp only [abs_mul]; ring)
  have h1 : |∫ ω, (e 0 ω * W ((X 0 ω - x) / hn)) * (e j ω * W ((X j ω - x) / hn)) ∂μ|
      ≤ ∫ ω, |e 0 ω * e j ω| *
          (fun z : ℝ × ℝ => |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|) (X 0 ω, X j ω) ∂μ :=
    hcongr ▸ h0
  -- Step 2: (C2) with that test function.
  refine h1.trans ((hC2 j hj
    (fun z : ℝ × ℝ => |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|)
    (by fun_prop) (fun z => by positivity)).trans (le_of_eq ?_))
  -- Step 3: the product integral factorizes, and each factor is `hn ∫|W|`.
  have hprod : ∫ z : ℝ × ℝ, |W ((z.1 - x) / hn)| * |W ((z.2 - x) / hn)|
        ∂(MeasureTheory.volume.prod MeasureTheory.volume)
      = (∫ v, |W ((v - x) / hn)|) * ∫ w, |W ((w - x) / hn)| :=
    integral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      (f := fun v => |W ((v - x) / hn)|) (g := fun w => |W ((w - x) / hn)|)
  have hone : ∫ v, |W ((v - x) / hn)| = hn * ∫ v, |W v| := by
    have := integral_dilate_translate (fun u => |W u|) (fun _ => (1 : ℝ)) x hhn
    simp only [mul_one] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hhn.ne', one_mul]
  rw [hprod, hone]
  ring

/-- **Continuity at a point upgrades an a.e. lower bound to a pointwise one.** If `g` is
continuous at `x` and `0 ≤ g` Lebesgue-a.e., then `0 ≤ g x`: otherwise `g < 0` on a whole
ball around `x`, which has positive Lebesgue measure. Used to evaluate the repaired
diagonal limit at the point `x` itself, where `σ²` is *not* pinned down by `hcv` (which
constrains it only `μ.map (X 0)`-a.e.). -/
theorem nonneg_of_continuousAt_of_ae_nonneg {g : ℝ → ℝ} {x : ℝ}
    (hgc : ContinuousAt g x)
    (hae : ∀ᵐ v ∂(MeasureTheory.volume : Measure ℝ), 0 ≤ g v) : 0 ≤ g x := by
  by_contra hx
  push_neg at hx
  have hlt : ∀ᶠ v in 𝓝 x, g v < 0 := hgc (Iio_mem_nhds hx)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hlt
  have hsub : Metric.ball x ε ⊆ {v : ℝ | 0 ≤ g v}ᶜ := fun v hv => not_le.2 (hball v hv)
  exact (Metric.measure_ball_pos MeasureTheory.volume x hε).ne'
    (measure_mono_null hsub (mem_ae_iff.1 hae))

/-- **FY (2.73), diagonal term — REPAIRED AND PROVED.**
`h⁻¹ E[e_0² W²((X_0 − x)/h)] = ∫ (σ²·p)(x + h u) W²(u) du` (an *identity*, proved
inside `tendsto_localized_second_moment_of_bounded`), and FY asserts the limit
`σ²(x) p(x) ∫ W²`.

**Status: PROVED, under the authorized repair** — the two hypotheses `hσm`/`hσpb` below
are the laptop-authorized amendment of (C1) (the textbook's silent reading; see the
module docstring's FALSE-AS-FROZEN section). The record of *why* the amendment is
necessary is kept verbatim below.

Note that `hσpb` is only a **one-sided** (upper) bound: the matching lower bound is not
assumed but *derived*, since `σ²` is a conditional second moment, hence `≥ 0` a.e. for
the law of `X_0`, hence `σ²·p ≥ 0` Lebesgue-a.e. (this is where `hσm` is spent — it makes
`{v | 0 ≤ σ²(v)}` measurable, so the a.e. statement transports through
`ae_map_iff`/`ae_withDensity_iff`). The proof then runs
`tendsto_localized_second_moment_of_bounded` on the clipped `max σ² 0`, which agrees with
`σ²` a.e.-`μ` under the conditional expectation, and agrees with it *at the point* `x` by
`nonneg_of_continuousAt_of_ae_nonneg`.

**Why the repair is needed.** The limit needs more than the formalized (C1)–(C5) supply
(this was verified in the previous wave). Continuity of
`σ²·p` at `x` controls the window `|u| ≤ M` (there `|h u| ≤ M h → 0`), but the tail
`|u| > M` is left uncontrolled: `(C2)` forces only `σ·p` to be bounded (take
`g = g₁ ⊗ g₂` in (C2) and let `g` concentrate), **not** `σ²·p`, and `σ²·p ∈ L¹` alone
(`= E e_0² < ∞`) is not enough against a merely-`L¹` weight `W²`. Concretely: with
`σ p ≡ B` on a sequence of spikes escaping to `v ≈ x + 1`, `σ²p = (σp)²/p` is
unbounded, and choosing `W² = 1` on intervals `J_k ≈ 2^k` of length `2^{-k}`
(so `W` is bounded, `∫|W| < ∞`, `∫W² < ∞`) makes
`∫ (σ²p)(x + h_k u) W²(u) du ≥ σ²(x)p(x)∫W² + 1` along `h_k = 2^{-k}` while `σ²`, `p`
stay continuous at `x`. Sparsifying the spike sequence keeps `h_n → 0` compatible with
`n h_n³ → ∞`, so (C5) does not rescue it.

**Repair (APPLIED).** Either strengthen (C4) to compactly supported `W` (then continuity
at `x` suffices and this lemma is `tendsto_localized_second_moment_of_bounded`'s window
argument), or strengthen (C1) to `σ²·p` bounded — which is what the textbook's
"(C1) with `σ²` and `p` bounded" silently supplies. The second route is the one taken:
`hσpb` below, together with the measurability `hσm` that the frozen (C1) also omitted
(only `hcv` constrains `σsq`, and only `μ.map (X 0)`-a.e.). -/
theorem tendsto_localized_second_moment_debt [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0)) {σsq p : ℝ → ℝ}
    -- USER-INPUT: σ² measurable (the frozen (C1) omits it); FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {x : ℝ}
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (he2 : Integrable (fun ω => e 0 ω ^ 2) μ)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
        (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) := by
  obtain ⟨C, hC⟩ := hσpb
  -- (1) `σ²` is a conditional second moment, hence `≥ 0` a.e.-`μ` along `X 0`.
  have hcond0 : (0 : Ω → ℝ)
      ≤ᵐ[μ] μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance] :=
    condExp_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
  have hσ0 : ∀ᵐ ω ∂μ, 0 ≤ σsq (X 0 ω) := by
    filter_upwards [hcond0, hcv] with ω h1 h2
    simpa [h2] using h1
  -- (2) hence `σ²·p ≥ 0` Lebesgue-a.e. (transport through the density of `X 0`).
  have hlaw : ∀ᵐ v ∂(μ.map (X 0)), 0 ≤ σsq v := by
    rw [ae_map_iff hX.aemeasurable (measurableSet_le measurable_const hσm)]
    exact hσ0
  rw [hpd, ae_withDensity_iff (by fun_prop)] at hlaw
  have hae : ∀ᵐ v ∂(MeasureTheory.volume : Measure ℝ), 0 ≤ σsq v * p v := by
    filter_upwards [hlaw] with v hv
    rcases (hp0 v).eq_or_lt with hz | hz
    · rw [← hz, mul_zero]
    · exact mul_nonneg (hv (ENNReal.ofReal_pos.2 hz).ne') (hp0 v)
  -- (3) the clipped `max σ² 0` satisfies the *two-sided* bound of the proved brick,
  -- and agrees with `σ²` both a.e.-`μ` (under `hcv`) and at the point `x`.
  have hcv' : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => max (σsq (X 0 ω)) 0 := by
    filter_upwards [hcv, hσ0] with ω h1 h2
    rw [h1, max_eq_left h2]
  have hbound : ∀ v : ℝ, |max (σsq v) 0 * p v| ≤ max C 0 := by
    intro v
    rw [abs_of_nonneg (mul_nonneg (le_max_right _ _) (hp0 v))]
    rcases le_or_gt 0 (σsq v) with hs | hs
    · rw [max_eq_left hs]; exact (hC v).trans (le_max_left _ _)
    · rw [max_eq_right hs.le, zero_mul]; exact le_max_right _ _
  have hend : max (σsq x) 0 * p x = σsq x * p x := by
    rcases le_or_gt 0 (σsq x) with hs | hs
    · rw [max_eq_left hs]
    · have hgx : 0 ≤ σsq x * p x :=
        nonneg_of_continuousAt_of_ae_nonneg (g := fun v => σsq v * p v)
          (hσc.mul hpc) hae
      have hpx0 : p x = 0 := by
        rcases (hp0 x).eq_or_lt with hz | hz
        · exact hz.symm
        · nlinarith
      rw [hpx0, mul_zero, mul_zero]
  have hmain := tendsto_localized_second_moment_of_bounded (X := X) (e := e) hX
    (σsq := fun v => max (σsq v) 0) (p := p) (hσm.max measurable_const) hmp hp0 hpd
    (x := x) hcv' he2 ((hσc.max continuousAt_const).mul hpc) (M := max C 0) hbound
    hWm hWb hW2 hh0 hh
  rw [hend] at hmain
  exact hmain

/-- **FY (2.75), large-lag covariance bound — PROVED.** Davydov
(`abs_covariance_le_davydov` at `p = q = δ`, so the exponent is `1 − 2/δ`) against the
pair α-coefficient: `|Cov(ξ_0, ξ_j)| ≤ 8 α_pair(j)^{1−2/δ} ‖ξ_0‖_δ ‖ξ_j‖_δ`. The
σ-algebra transport is `σ(X_0, e_0) ≤ ⨆_{s ≤ 0}` and `σ(X_j, e_j) ≤ ⨆_{s ≥ j}`.

What remains for ledger (a) — and is *not* part of this lemma — is the kernel
localization of the δ-norms, `‖ξ_0‖_δ² ≤ C h^{2/δ}`, and the summation
`Σ_{j > m_n} α^{1−2/δ}(j) ≤ m_n^{−λ} Σ_j j^λ α^{1−2/δ}(j)` from (C3), whose `h`-powers
close against (C5); those live in `var_localized_sum`'s assembly. -/
theorem large_lag_covariance_bound [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    {δ : ℝ} (hδ : 2 < δ) {W : ℝ → ℝ} {x : ℝ} (hWm : Measurable W)
    {hn : ℝ} (hhn : 0 < hn) (j : ℕ) (hj : 1 ≤ j)
    (hL0 : MemLp (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ)
    (hLj : MemLp (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn)) (ENNReal.ofReal δ) μ) :
    |cov[fun ω => e 0 ω * W ((X 0 ω - x) / hn),
        fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn); μ]|
      ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ)
        * (eLpNorm (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ).toReal
        * (eLpNorm (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn))
            (ENNReal.ofReal δ) μ).toReal := by
  have hpq : 1 / δ + 1 / δ < 1 := by
    have h2d : 1 / δ + 1 / δ = 2 / δ := by ring
    rw [h2d, div_lt_one (by linarith : (0 : ℝ) < δ)]; linarith
  have hf : Measurable[⨆ s ∈ Set.Iic (0 : ℤ), MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance]
      (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) :=
    (measurable_e_pairSigma (X := X) (e := e) (Set.mem_Iic.2 (le_refl (0 : ℤ)))).mul
      (hWm.comp (((measurable_X_pairSigma (X := X) (e := e)
        (Set.mem_Iic.2 (le_refl (0 : ℤ)))).sub measurable_const).div measurable_const))
  have hg : Measurable[⨆ s ∈ Set.Ici (j : ℤ), MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance]
      (fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / hn)) :=
    (measurable_e_pairSigma (X := X) (e := e) (Set.mem_Ici.2 (le_refl (j : ℤ)))).mul
      (hWm.comp (((measurable_X_pairSigma (X := X) (e := e)
        (Set.mem_Ici.2 (le_refl (j : ℤ)))).sub measurable_const).div measurable_const))
  have hdav := abs_covariance_le_davydov (pairSigma_le hmeasX hmeasE (Set.Iic (0 : ℤ)))
    (pairSigma_le hmeasX hmeasE (Set.Ici (j : ℤ))) hf hg (p := δ) (q := δ)
    (by linarith) (by linarith) hpq hL0 hLj
  have hexp : (1 : ℝ) - 1 / δ - 1 / δ = 1 - 2 / δ := by ring
  rw [hexp] at hdav
  exact hdav

/-! #### Law transport from the fdd form of stationarity

FY's (C1) is frozen here in its *finite-dimensional-distribution* form: the law of the
`k`-window `(X_{t+i}, e_{t+i})_{i<k}` does not depend on `t`. These four lemmas are the
only consequences ledger (a) needs — the one-time and two-time marginals, and the
transport of integrals, `eLpNorm`s and `MemLp` of a fixed function of the pair. Each is
obtained by pushing the `hstat` identity forward along a coordinate evaluation. -/

/-- One-time marginal transport: `(X_t, e_t) ~ (X_0, e_0)`. -/
theorem map_pair_eq_of_stat {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) :
    μ.map (fun ω => (X t ω, e t ω)) = μ.map (fun ω => (X 0 ω, e 0 ω)) := by
  have hmΦ : ∀ s : ℤ, Measurable (fun ω (i : Fin 1) => (X (s + (i : ℕ)) ω, e (s + (i : ℕ)) ω)) :=
    fun s => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hmΨ : Measurable (fun ω (i : Fin 1) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)) :=
    measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hev : Measurable (fun z : Fin 1 → ℝ × ℝ => z 0) := measurable_pi_apply 0
  have h := congrArg (fun ν : Measure (Fin 1 → ℝ × ℝ) => ν.map (fun z => z 0)) (hstat 1 t)
  rw [Measure.map_map hev (hmΦ t), Measure.map_map hev hmΨ] at h
  simpa [Function.comp] using! h

/-- Transport of a one-time integral: `E[F(X_t, e_t)] = E[F(X_0, e_0)]`. Used to move the
error moments off the time index — in particular `E e_t² = E e_0²`, which is what turns
FY's printed (C2) into the `E[e_0²]`-normalized instance (2.76) uses. -/
theorem integral_comp_pair_eq {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) {F : ℝ × ℝ → ℝ} (hF : Measurable F) :
    ∫ ω, F (X t ω, e t ω) ∂μ = ∫ ω, F (X 0 ω, e 0 ω) ∂μ := by
  have hmt : AEMeasurable (fun ω => (X t ω, e t ω)) μ :=
    ((hmeasX t).prodMk (hmeasE t)).aemeasurable
  have hm0 : AEMeasurable (fun ω => (X 0 ω, e 0 ω)) μ :=
    ((hmeasX 0).prodMk (hmeasE 0)).aemeasurable
  rw [← integral_map hmt hF.aestronglyMeasurable, map_pair_eq_of_stat hmeasX hmeasE hstat t,
    integral_map hm0 hF.aestronglyMeasurable]

/-- Two-time marginal transport: `((X_t, e_t), (X_{t+d}, e_{t+d})) ~ ((X_0, e_0), (X_d, e_d))`.
Obtained from the `(d+1)`-window by evaluating at the first and last coordinates. -/
theorem map_pair2_eq_of_stat {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) (d : ℕ) :
    μ.map (fun ω => ((X t ω, e t ω), (X (t + (d : ℤ)) ω, e (t + (d : ℤ)) ω)))
      = μ.map (fun ω => ((X 0 ω, e 0 ω), (X (d : ℤ) ω, e (d : ℤ) ω))) := by
  have hmΦ : ∀ s : ℤ,
      Measurable (fun ω (i : Fin (d + 1)) => (X (s + (i : ℕ)) ω, e (s + (i : ℕ)) ω)) :=
    fun s => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hmΨ : Measurable (fun ω (i : Fin (d + 1)) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)) :=
    measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hev : Measurable
      (fun z : Fin (d + 1) → ℝ × ℝ => (z 0, z (Fin.last d))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have h := congrArg
    (fun ν : Measure (Fin (d + 1) → ℝ × ℝ) => ν.map (fun z => (z 0, z (Fin.last d))))
    (hstat (d + 1) t)
  rw [Measure.map_map hev (hmΦ t), Measure.map_map hev hmΨ] at h
  simpa [Function.comp_def, Fin.val_last] using h

/-- Transport of a two-time integral: `E[G((X_t,e_t),(X_{t+d},e_{t+d}))] = E[G((X_0,e_0),(X_d,e_d))]`.
This is what turns the double covariance sum of ledger (a) into a single lag sum. -/
theorem integral_comp_pair2_eq {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) (d : ℕ) {G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ} (hG : Measurable G) :
    ∫ ω, G ((X t ω, e t ω), (X (t + (d : ℤ)) ω, e (t + (d : ℤ)) ω)) ∂μ
      = ∫ ω, G ((X 0 ω, e 0 ω), (X (d : ℤ) ω, e (d : ℤ) ω)) ∂μ := by
  have hmt : AEMeasurable
      (fun ω => ((X t ω, e t ω), (X (t + (d : ℤ)) ω, e (t + (d : ℤ)) ω))) μ :=
    (((hmeasX t).prodMk (hmeasE t)).prodMk
      ((hmeasX _).prodMk (hmeasE _))).aemeasurable
  have hm0 : AEMeasurable
      (fun ω => ((X 0 ω, e 0 ω), (X (d : ℤ) ω, e (d : ℤ) ω))) μ :=
    (((hmeasX 0).prodMk (hmeasE 0)).prodMk
      ((hmeasX _).prodMk (hmeasE _))).aemeasurable
  rw [← integral_map hmt hG.aestronglyMeasurable,
    map_pair2_eq_of_stat hmeasX hmeasE hstat t d, integral_map hm0 hG.aestronglyMeasurable]

/-- Transport of an `eLpNorm` of a fixed function of the pair. -/
theorem eLpNorm_comp_pair_eq {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) {F : ℝ × ℝ → ℝ} (hF : Measurable F) (q : ℝ≥0∞) :
    eLpNorm (fun ω => F (X t ω, e t ω)) q μ
      = eLpNorm (fun ω => F (X 0 ω, e 0 ω)) q μ := by
  have hmt : AEMeasurable (fun ω => (X t ω, e t ω)) μ :=
    ((hmeasX t).prodMk (hmeasE t)).aemeasurable
  have hm0 : AEMeasurable (fun ω => (X 0 ω, e 0 ω)) μ :=
    ((hmeasX 0).prodMk (hmeasE 0)).aemeasurable
  have h1 : eLpNorm F q (μ.map (fun ω => (X t ω, e t ω)))
      = eLpNorm (fun ω => F (X t ω, e t ω)) q μ :=
    eLpNorm_map_measure hF.aestronglyMeasurable hmt
  have h2 : eLpNorm F q (μ.map (fun ω => (X 0 ω, e 0 ω)))
      = eLpNorm (fun ω => F (X 0 ω, e 0 ω)) q μ :=
    eLpNorm_map_measure hF.aestronglyMeasurable hm0
  rw [← h1, ← h2, map_pair_eq_of_stat hmeasX hmeasE hstat t]

/-- Transport of `MemLp` of a fixed function of the pair. -/
theorem memLp_comp_pair {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) {F : ℝ × ℝ → ℝ} (hF : Measurable F) {q : ℝ≥0∞}
    (h0 : MemLp (fun ω => F (X 0 ω, e 0 ω)) q μ) :
    MemLp (fun ω => F (X t ω, e t ω)) q μ :=
  ⟨(hF.comp ((hmeasX t).prodMk (hmeasE t))).aestronglyMeasurable, by
    rw [eLpNorm_comp_pair_eq hmeasX hmeasE hstat t hF q]; exact h0.2⟩

/-- One-time marginal of `X` alone: `X_t ~ X_0`. -/
theorem map_fst_eq_of_stat {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) : μ.map (X t) = μ.map (X 0) := by
  have hpt : Measurable (fun ω => (X t ω, e t ω)) := (hmeasX t).prodMk (hmeasE t)
  have hp0 : Measurable (fun ω => (X 0 ω, e 0 ω)) := (hmeasX 0).prodMk (hmeasE 0)
  have h := congrArg (fun ν : Measure (ℝ × ℝ) => ν.map Prod.fst)
    (map_pair_eq_of_stat hmeasX hmeasE hstat t)
  rwa [Measure.map_map measurable_fst hpt, Measure.map_map measurable_fst hp0] at h

/-- An a.e. property of `X_0` is an a.e. property of `X_t`. -/
theorem ae_comp_X_of_stat {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (t : ℤ) {S : Set ℝ} (hS : MeasurableSet S) (h0 : ∀ᵐ ω ∂μ, X 0 ω ∈ S) :
    ∀ᵐ ω ∂μ, X t ω ∈ S := by
  have h1 : ∀ᵐ v ∂(μ.map (X 0)), v ∈ S :=
    (ae_map_iff (hmeasX 0).aemeasurable hS).2 h0
  rw [← map_fst_eq_of_stat hmeasX hmeasE hstat t] at h1
  exact (ae_map_iff (hmeasX t).aemeasurable hS).1 h1

/-- **Conditional expectations transport across time — PROVED.** Under the fdd form of
stationarity, the conditional expectation `E(φ(e_t) | X_t)` is, for *every* `t`, the same
measurable function `m` of `X_t`. This is the brick steps (b)–(c) need but ledger (a) did
not: `truncErr` is built from `E(clamp_L(e_t) | X_t)` at each time separately, so the
truncated array is a fixed function of the pair `(X_t, e_t)` only once these versions are
identified.

Two ingredients: Doob–Dynkin (`StronglyMeasurable.exists_eq_measurable_comp`) produces the
factorization `m` at `t = 0`, and the defining set-integral characterization of the
conditional expectation transports to time `t` because both sides of
`∫_{X_t ∈ A} m(X_t) = ∫_{X_t ∈ A} φ(e_t)` are integrals of a *fixed* function of the pair,
namely `Prod.fst ⁻¹' A`-indicators, so `integral_comp_pair_eq` applies to each. -/
theorem exists_condExp_repr_of_stat [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {φ : ℝ → ℝ} (hφ : Measurable φ) (hφi : Integrable (fun ω => φ (e 0 ω)) μ) :
    ∃ m : ℝ → ℝ, Measurable m ∧ ∀ t : ℤ,
      μ[fun ω => φ (e t ω) | MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => m (X t ω) := by
  classical
  have hsm : StronglyMeasurable[MeasurableSpace.comap (X 0) inferInstance]
      (μ[fun ω => φ (e 0 ω) | MeasurableSpace.comap (X 0) inferInstance]) :=
    stronglyMeasurable_condExp
  obtain ⟨m, hmsm, hmeq⟩ := MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp hsm
  refine ⟨m, hmsm.measurable, fun t => ?_⟩
  have hmle : MeasurableSpace.comap (X t) inferInstance ≤ ‹MeasurableSpace Ω› :=
    (hmeasX t).comap_le
  have hφt : Integrable (fun ω => φ (e t ω)) μ := by
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => φ z.2) (X 0 ω, e 0 ω)) 1 μ :=
      memLp_one_iff_integrable.2 hφi
    exact memLp_one_iff_integrable.1
      (memLp_comp_pair hmeasX hmeasE hstat t (hφ.comp measurable_snd) h0)
  have hmi0 : Integrable (fun ω => m (X 0 ω)) μ := by
    have := integrable_condExp (μ := μ) (m := MeasurableSpace.comap (X 0) inferInstance)
      (f := fun ω => φ (e 0 ω))
    rwa [hmeq] at this
  have hmit : Integrable (fun ω => m (X t ω)) μ := by
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => m z.1) (X 0 ω, e 0 ω)) 1 μ :=
      memLp_one_iff_integrable.2 hmi0
    exact memLp_one_iff_integrable.1
      (memLp_comp_pair hmeasX hmeasE hstat t (hmsm.measurable.comp measurable_fst) h0)
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hmle hφt
    (fun s _ _ => hmit.integrableOn) (fun s hs _ => ?_)
    ((hmsm.measurable.comp (Measurable.of_comap_le le_rfl)).aestronglyMeasurable)).symm
  obtain ⟨A, hA, rfl⟩ := hs
  set F1 : ℝ × ℝ → ℝ := Set.indicator (Prod.fst ⁻¹' A) (fun z => m z.1) with hF1def
  set F2 : ℝ × ℝ → ℝ := Set.indicator (Prod.fst ⁻¹' A) (fun z => φ z.2) with hF2def
  have hF1m : Measurable F1 :=
    (hmsm.measurable.comp measurable_fst).indicator (measurable_fst hA)
  have hF2m : Measurable F2 :=
    (hφ.comp measurable_snd).indicator (measurable_fst hA)
  have hind1 : ∀ s : ℤ, ∫ ω in X s ⁻¹' A, m (X s ω) ∂μ
      = ∫ ω, F1 (X s ω, e s ω) ∂μ := by
    intro s
    rw [← integral_indicator ((hmeasX s) hA)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : X s ω ∈ A <;> simp [hF1def, Set.mem_preimage, hω]
  have hind2 : ∀ s : ℤ, ∫ ω in X s ⁻¹' A, φ (e s ω) ∂μ
      = ∫ ω, F2 (X s ω, e s ω) ∂μ := by
    intro s
    rw [← integral_indicator ((hmeasX s) hA)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : X s ω ∈ A <;> simp [hF2def, Set.mem_preimage, hω]
  have hA0 : MeasurableSet[MeasurableSpace.comap (X 0) inferInstance] (X 0 ⁻¹' A) :=
    ⟨A, hA, rfl⟩
  have hcond : ∫ ω in X 0 ⁻¹' A, m (X 0 ω) ∂μ = ∫ ω in X 0 ⁻¹' A, φ (e 0 ω) ∂μ := by
    have hrw : ∀ ω, m (X 0 ω)
        = (μ[fun ω' => φ (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance]) ω := by
      intro ω; rw [hmeq]; rfl
    calc ∫ ω in X 0 ⁻¹' A, m (X 0 ω) ∂μ
        = ∫ ω in X 0 ⁻¹' A,
            (μ[fun ω' => φ (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ :=
          setIntegral_congr_fun ((hmeasX 0) hA) (fun ω _ => hrw ω)
      _ = ∫ ω in X 0 ⁻¹' A, φ (e 0 ω) ∂μ :=
          setIntegral_condExp ((hmeasX 0).comap_le) hφi hA0
  calc ∫ ω in X t ⁻¹' A, m (X t ω) ∂μ
      = ∫ ω, F1 (X t ω, e t ω) ∂μ := hind1 t
    _ = ∫ ω, F1 (X 0 ω, e 0 ω) ∂μ := integral_comp_pair_eq hmeasX hmeasE hstat t hF1m
    _ = ∫ ω in X 0 ⁻¹' A, m (X 0 ω) ∂μ := (hind1 0).symm
    _ = ∫ ω in X 0 ⁻¹' A, φ (e 0 ω) ∂μ := hcond
    _ = ∫ ω, F2 (X 0 ω, e 0 ω) ∂μ := hind2 0
    _ = ∫ ω, F2 (X t ω, e t ω) ∂μ := (integral_comp_pair_eq hmeasX hmeasE hstat t hF2m).symm
    _ = ∫ ω in X t ⁻¹' A, φ (e t ω) ∂μ := (hind2 t).symm

/-- **(C1)'s `E(e | X) = 0` holds at every time — PROVED.** The frozen (C1) states it at
`t = 0` only; `exists_condExp_repr_of_stat` plus the transport of a.e. statements along
`μ.map (X t) = μ.map (X 0)` propagates it. This is what keeps *every* summand of `locSum`
centred, and what makes `e_t − e^L_t = r_t − E(r_t | X_t)` with `r_t = e_t − clamp_L(e_t)`
— the identity the truncation tail (2.82) is built on. -/
theorem condExp_eq_zero_of_stat [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (he1 : Integrable (e 0) μ)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0) (t : ℤ) :
    μ[e t | MeasurableSpace.comap (X t) inferInstance] =ᵐ[μ] 0 := by
  obtain ⟨m, hm, hrep⟩ :=
    exists_condExp_repr_of_stat hmeasX hmeasE hstat (φ := fun z => z) measurable_id he1
  have hrep' : ∀ s : ℤ, μ[e s | MeasurableSpace.comap (X s) inferInstance]
      =ᵐ[μ] fun ω => m (X s ω) := fun s => hrep s
  have h0 : ∀ᵐ ω ∂μ, X 0 ω ∈ {v : ℝ | m v = 0} := by
    filter_upwards [hrep' 0, hce] with ω h1 h2
    show m (X 0 ω) = 0
    rw [← h1]; exact h2
  have hS : MeasurableSet {v : ℝ | m v = 0} := hm (measurableSet_singleton 0)
  filter_upwards [hrep' t, ae_comp_X_of_stat hmeasX hmeasE hstat t hS h0] with ω h1 h2
  have h2' : m (X t ω) = 0 := h2
  rw [h1, h2']
  rfl

/-- **`truncErr` is a fixed function of the pair, up to a null set — PROVED.** There is
one bounded measurable `mL` with `e^L_t = clamp_L(e_t) − mL(X_t)` a.e., simultaneously for
every `t`. This is what steps (b)–(c) need in order to run the ledger-(a) machinery on the
*truncated* array: the frozen `truncErr` is built from a separate conditional expectation at
each time, and without the identification its covariance array would not be a function of
the lag alone.

`exists_condExp_repr_of_stat` at `φ = clamp_L` gives a common measurable version `m`;
`|E(clamp_L e_0 | X_0)| ≤ L` a.e. (conditional monotonicity against the constants `±L`), so
re-clamping `m` at level `L` changes it on a null set only and makes the bound pointwise. -/
theorem exists_truncErr_repr [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {L : ℝ} (hL : 0 < L) :
    ∃ mL : ℝ → ℝ, Measurable mL ∧ (∀ v, |mL v| ≤ L) ∧
      ∀ t : ℤ, truncErr X e μ L t =ᵐ[μ] fun ω => clampAt L (e t ω) - mL (X t ω) := by
  classical
  have hcm : Measurable (clampAt L) := measurable_clampAt L
  have hbd : ∀ ω, |clampAt L (e 0 ω)| ≤ L := fun ω => abs_clampAt_le hL.le _
  have hint : Integrable (fun ω => clampAt L (e 0 ω)) μ := by
    refine (integrable_const L).mono' (hcm.comp (hmeasE 0)).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hbd ω
  obtain ⟨m, hm, hrep⟩ := exists_condExp_repr_of_stat hmeasX hmeasE hstat hcm hint
  refine ⟨clampAt L ∘ m, hcm.comp hm, fun v => abs_clampAt_le hL.le _, fun t => ?_⟩
  have hle0 : ∀ᵐ ω ∂μ, X 0 ω ∈ {v : ℝ | |m v| ≤ L} := by
    have hup : μ[fun ω' => clampAt L (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance]
        ≤ᵐ[μ] fun _ => L := by
      have h1 := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance) hint
        (integrable_const L)
        (Eventually.of_forall fun ω => (abs_le.1 (hbd ω)).2)
      rwa [condExp_const ((hmeasX 0).comap_le) L] at h1
    have hlo : (fun _ : Ω => -L)
        ≤ᵐ[μ] μ[fun ω' => clampAt L (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance] := by
      have h1 := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance)
        (integrable_const (-L)) hint
        (Eventually.of_forall fun ω => (abs_le.1 (hbd ω)).1)
      rwa [condExp_const ((hmeasX 0).comap_le) (-L)] at h1
    filter_upwards [hrep 0, hup, hlo] with ω h1 h2 h3
    show |m (X 0 ω)| ≤ L
    rw [← h1]; exact abs_le.2 ⟨h3, h2⟩
  have hS : MeasurableSet {v : ℝ | |m v| ≤ L} := measurableSet_le hm.abs measurable_const
  filter_upwards [hrep t, ae_comp_X_of_stat hmeasX hmeasE hstat t hS hle0] with ω h1 h2
  have h2' : |m (X t ω)| ≤ L := h2
  show clampAt L (e t ω) - _ = _
  rw [h1]
  have hcl : clampAt L (m (X t ω)) = m (X t ω) := by
    unfold clampAt
    rw [min_eq_right (abs_le.1 h2').2, max_eq_right (abs_le.1 h2').1]
  simp only [Function.comp_apply, hcl]

/-- **The stationary double sum, off the diagonal.** If a doubly-indexed array `c` depends
only on the lag (`c s (s+d) = c (s+d) s = g d`), then its full `n × n` sum differs from the
diagonal contribution `n · g 0` by at most `2 n Σ_{1 ≤ j < n} |g j|`. This is the purely
combinatorial half of FY (2.73): each row contributes `g 0` plus a lag sum in both
directions, each of which injects into `Finset.Ico 1 n`. -/
theorem abs_double_sum_sub_diag_le (n : ℕ) (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hc : ∀ s d : ℕ, c s (s + d) = g d) (hc' : ∀ s d : ℕ, c (s + d) s = g d) :
    |(∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, c s t) - n * g 0|
      ≤ 2 * n * ∑ j ∈ Finset.Ico 1 n, |g j| := by
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 n, |g j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hdiag : ∀ s : ℕ, c s s = g 0 := fun s => by simpa using hc s 0
  have key : ∀ s ∈ Finset.range n,
      |(∑ t ∈ Finset.range n, c s t) - g 0|
        ≤ 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by
    intro s hs
    simp only [Finset.mem_range] at hs
    have hsplit : (∑ t ∈ Finset.range n, c s t)
        = g 0 + ∑ t ∈ (Finset.range n).erase s, c s t := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hs), hdiag]
    rw [hsplit, add_sub_cancel_left]
    set A : Finset ℕ := (Finset.range n).filter (fun t => t < s) with hA
    set B : Finset ℕ := (Finset.range n).filter (fun t => s < t) with hB
    have hAB : (Finset.range n).erase s = A ∪ B := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, hA, hB,
        Finset.mem_filter]
      omega
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro t htA htB
      simp only [hA, hB, Finset.mem_filter] at htA htB
      omega
    calc |∑ t ∈ (Finset.range n).erase s, c s t|
        ≤ ∑ t ∈ (Finset.range n).erase s, |c s t| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = (∑ t ∈ A, |c s t|) + ∑ t ∈ B, |c s t| := by
          rw [hAB, Finset.sum_union hdisj]
      _ ≤ (∑ j ∈ Finset.Ico 1 n, |g j|) + ∑ j ∈ Finset.Ico 1 n, |g j| := by
          gcongr
          · have hinj : ∀ t₁ ∈ A, ∀ t₂ ∈ A, s - t₁ = s - t₂ → t₁ = t₂ := by
              intro t₁ h₁ t₂ h₂ he
              simp only [hA, Finset.mem_filter] at h₁ h₂
              omega
            have himg : A.image (fun t => s - t) ⊆ Finset.Ico 1 n := by
              intro j hj
              simp only [Finset.mem_image, hA, Finset.mem_filter, Finset.mem_range] at hj
              obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
              simp only [Finset.mem_Ico]
              omega
            have hval : ∀ t ∈ A, |c s t| = |g (s - t)| := by
              intro t ht
              simp only [hA, Finset.mem_filter] at ht
              have : t + (s - t) = s := by omega
              rw [← hc' t (s - t), this]
            have himgsum : ∑ j ∈ A.image (fun t => s - t), |g j| = ∑ t ∈ A, |g (s - t)| :=
              Finset.sum_image hinj
            rw [Finset.sum_congr rfl hval, ← himgsum]
            exact Finset.sum_le_sum_of_subset_of_nonneg himg
              fun j _ _ => abs_nonneg _
          · have hinj : ∀ t₁ ∈ B, ∀ t₂ ∈ B, t₁ - s = t₂ - s → t₁ = t₂ := by
              intro t₁ h₁ t₂ h₂ he
              simp only [hB, Finset.mem_filter] at h₁ h₂
              omega
            have himg : B.image (fun t => t - s) ⊆ Finset.Ico 1 n := by
              intro j hj
              simp only [Finset.mem_image, hB, Finset.mem_filter, Finset.mem_range] at hj
              obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
              simp only [Finset.mem_Ico]
              omega
            have hval : ∀ t ∈ B, |c s t| = |g (t - s)| := by
              intro t ht
              simp only [hB, Finset.mem_filter] at ht
              have : s + (t - s) = t := by omega
              rw [← hc s (t - s), this]
            have himgsum : ∑ j ∈ B.image (fun t => t - s), |g j| = ∑ t ∈ B, |g (t - s)| :=
              Finset.sum_image hinj
            rw [Finset.sum_congr rfl hval, ← himgsum]
            exact Finset.sum_le_sum_of_subset_of_nonneg himg
              fun j _ _ => abs_nonneg _
      _ = 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by ring
  have hrw : (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, c s t) - n * g 0
      = ∑ s ∈ Finset.range n, ((∑ t ∈ Finset.range n, c s t) - g 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hrw]
  calc |∑ s ∈ Finset.range n, ((∑ t ∈ Finset.range n, c s t) - g 0)|
      ≤ ∑ s ∈ Finset.range n, |(∑ t ∈ Finset.range n, c s t) - g 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range n, 2 * ∑ j ∈ Finset.Ico 1 n, |g j| :=
        Finset.sum_le_sum key
    _ = 2 * n * ∑ j ∈ Finset.Ico 1 n, |g j| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- **The stationary double sum over an arbitrary index set.** Same hypothesis as
`abs_double_sum_sub_diag_le` — the array `c` depends only on the lag — but the sum runs
over an arbitrary `I ⊆ range n` rather than over all of `range n`, and the diagonal is
kept on the right instead of being subtracted off:
`|Σ_{s,t ∈ I} c s t| ≤ |I| (|g 0| + 2 Σ_{1 ≤ j < n} |g j|)`.

This is the combinatorial half of the small-block estimate (2.79)–(2.81): there `I` is the
union of the `k_n` small blocks, of total length `N_n = k_n s_n` with `N_n / n → 0`, and
the two factors are exactly the ones ledger (a) already controls — the diagonal
`|g 0| = O(h)` and the lag sum `Σ_j |g j| = o(h)` — so that
`(n h_n)⁻¹ |Σ_{s,t ∈ I}| ≤ (N_n / n) · h_n⁻¹ (|g 0| + 2 Σ_j |g j|) → 0`. The proof is the
one of `abs_double_sum_sub_diag_le` with `range n` replaced by `I` in the row split; `hI`
is what keeps the two lag injections landing in `Ico 1 n`.

Note that this brick is *not* the obstruction to (2.79)–(2.81): the analytic half is (see
`tendsto_smallBlock_variance`, whose summands are the **truncated** ones, for which the
small-lag input `Σ_j |g j| = o(h)` needs (C2) in its unweighted form). -/
theorem abs_double_sum_subset_le {n : ℕ} (I : Finset ℕ) (hI : I ⊆ Finset.range n)
    (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hc : ∀ s d : ℕ, c s (s + d) = g d) (hc' : ∀ s d : ℕ, c (s + d) s = g d) :
    |∑ s ∈ I, ∑ t ∈ I, c s t|
      ≤ (I.card : ℝ) * (|g 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := by
  classical
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 n, |g j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hdiag : ∀ s : ℕ, c s s = g 0 := fun s => by simpa using hc s 0
  have key : ∀ s ∈ I, |∑ t ∈ I, c s t| ≤ |g 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by
    intro s hs
    have hsn : s < n := Finset.mem_range.1 (hI hs)
    have hsplit : (∑ t ∈ I, c s t) = g 0 + ∑ t ∈ I.erase s, c s t := by
      rw [← Finset.add_sum_erase _ _ hs, hdiag]
    set A : Finset ℕ := I.filter (fun t => t < s) with hA
    set B : Finset ℕ := I.filter (fun t => s < t) with hB
    have hAB : I.erase s = A ∪ B := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_union, hA, hB, Finset.mem_filter]
      constructor
      · rintro ⟨hts, htI⟩; rcases lt_or_gt_of_ne hts with h | h
        · exact Or.inl ⟨htI, h⟩
        · exact Or.inr ⟨htI, h⟩
      · rintro (⟨htI, h⟩ | ⟨htI, h⟩) <;> exact ⟨by omega, htI⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro t htA htB
      simp only [hA, hB, Finset.mem_filter] at htA htB
      omega
    have htail : |∑ t ∈ I.erase s, c s t| ≤ 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by
      calc |∑ t ∈ I.erase s, c s t|
          ≤ ∑ t ∈ I.erase s, |c s t| := Finset.abs_sum_le_sum_abs _ _
        _ = (∑ t ∈ A, |c s t|) + ∑ t ∈ B, |c s t| := by
            rw [hAB, Finset.sum_union hdisj]
        _ ≤ (∑ j ∈ Finset.Ico 1 n, |g j|) + ∑ j ∈ Finset.Ico 1 n, |g j| := by
            gcongr
            · have hinj : ∀ t₁ ∈ A, ∀ t₂ ∈ A, s - t₁ = s - t₂ → t₁ = t₂ := by
                intro t₁ h₁ t₂ h₂ he
                simp only [hA, Finset.mem_filter] at h₁ h₂
                omega
              have himg : A.image (fun t => s - t) ⊆ Finset.Ico 1 n := by
                intro j hj
                simp only [Finset.mem_image, hA, Finset.mem_filter] at hj
                obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
                simp only [Finset.mem_Ico]
                omega
              have hval : ∀ t ∈ A, |c s t| = |g (s - t)| := by
                intro t ht
                simp only [hA, Finset.mem_filter] at ht
                have : t + (s - t) = s := by omega
                rw [← hc' t (s - t), this]
              have himgsum : ∑ j ∈ A.image (fun t => s - t), |g j| = ∑ t ∈ A, |g (s - t)| :=
                Finset.sum_image hinj
              rw [Finset.sum_congr rfl hval, ← himgsum]
              exact Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => abs_nonneg _
            · have hinj : ∀ t₁ ∈ B, ∀ t₂ ∈ B, t₁ - s = t₂ - s → t₁ = t₂ := by
                intro t₁ h₁ t₂ h₂ he
                simp only [hB, Finset.mem_filter] at h₁ h₂
                omega
              have himg : B.image (fun t => t - s) ⊆ Finset.Ico 1 n := by
                intro j hj
                simp only [Finset.mem_image, hB, Finset.mem_filter] at hj
                obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
                have : t < n := Finset.mem_range.1 (hI ht1)
                simp only [Finset.mem_Ico]
                omega
              have hval : ∀ t ∈ B, |c s t| = |g (t - s)| := by
                intro t ht
                simp only [hB, Finset.mem_filter] at ht
                have : s + (t - s) = t := by omega
                rw [← hc s (t - s), this]
              have himgsum : ∑ j ∈ B.image (fun t => t - s), |g j| = ∑ t ∈ B, |g (t - s)| :=
                Finset.sum_image hinj
              rw [Finset.sum_congr rfl hval, ← himgsum]
              exact Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => abs_nonneg _
        _ = 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by ring
    calc |∑ t ∈ I, c s t| = |g 0 + ∑ t ∈ I.erase s, c s t| := by rw [hsplit]
      _ ≤ |g 0| + |∑ t ∈ I.erase s, c s t| := abs_add_le _ _
      _ ≤ |g 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by gcongr
  calc |∑ s ∈ I, ∑ t ∈ I, c s t|
      ≤ ∑ s ∈ I, |∑ t ∈ I, c s t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ I, (|g 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := Finset.sum_le_sum key
    _ = (I.card : ℝ) * (|g 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := by
        rw [Finset.sum_const, nsmul_eq_mul]


/-! #### FY's implicit (2.74): the localized δ-th moment

The one input FY uses without stating it. See `var_localized_sum`'s docstring for the
proof that it is not derivable from (C1)–(C5) as formalized. -/

/-- **The localized weight integral — PROVED.** `E[G((X_0 − x)/h)] ≤ (C_p ∫G) h` for a
nonnegative integrable weight `G`: the density substitution
(`integral_comp_eq_integral_density`) followed by the affine change of variables
(`integral_dilate_translate`), the factor `h` being the Jacobian. Used at `G = |W|^δ` (the
δ-th moment of the *truncated* localized summand, where the error factor is bounded by `2L`
and so contributes no conditional moment) and at `G = W²` (its variance). -/
theorem localized_weight_integral_le [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hX : Measurable (X 0))
    {p : ℝ → ℝ} (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {G : ℝ → ℝ} (hGm : Measurable G) (hG0 : ∀ v, 0 ≤ G v)
    (hGi : Integrable G MeasureTheory.volume) {x hn : ℝ} (hhn : 0 < hn) :
    ∫ ω, G ((X 0 ω - x) / hn) ∂μ ≤ (Cp * ∫ v, G v) * hn := by
  have hGxm : Measurable (fun v => G ((v - x) / hn)) :=
    hGm.comp ((measurable_id.sub measurable_const).div measurable_const)
  have hdens : ∫ ω, G ((X 0 ω - x) / hn) ∂μ = ∫ v, p v * G ((v - x) / hn) :=
    integral_comp_eq_integral_density hX hmp hp0 hpd (fun v => G ((v - x) / hn)) hGxm
  have hcov : ∫ u, G u * p (x + hn * u) = hn⁻¹ * ∫ v, G ((v - x) / hn) * p v :=
    integral_dilate_translate G p x hhn
  have hpint : ∫ v, p v * G ((v - x) / hn) = hn * ∫ u, G u * p (x + hn * u) := by
    rw [hcov, ← mul_assoc, mul_inv_cancel₀ hhn.ne', one_mul]
    exact integral_congr_ae (Eventually.of_forall fun v => by ring)
  have hlast : ∫ u, G u * p (x + hn * u) ≤ Cp * ∫ u, G u := by
    have hi : Integrable (fun u => G u * p (x + hn * u)) MeasureTheory.volume := by
      refine Integrable.mono (hGi.const_mul Cp)
        (hGm.mul (hmp.comp (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (hG0 u) (hp0 _)),
        abs_of_nonneg (mul_nonneg (le_trans (hp0 0) (hpb 0)) (hG0 u)), mul_comm Cp]
      exact mul_le_mul_of_nonneg_left (hpb _) (hG0 u)
    rw [← integral_const_mul]
    refine integral_mono hi (hGi.const_mul Cp) fun u => ?_
    rw [mul_comm Cp]
    exact mul_le_mul_of_nonneg_left (hpb _) (hG0 u)
  rw [hdens, hpint, mul_comm ((Cp * ∫ v, G v)) hn]
  exact mul_le_mul_of_nonneg_left hlast hhn.le

-- the tower/density/change-of-variables chain below is elaboration-heavy
set_option maxHeartbeats 400000 in
/-- **FY's implicit (2.74) — PROVED from the conditional δ-moment.** If
`E(|e_0|^δ | X_0) ≤ M` a.e. and the density `p` is bounded by `Cp`, then the
kernel-localized summand `ξ_0 = e_0 W((X_0 − x)/h)` obeys
`E|ξ_0|^δ ≤ (M · Cp · ∫|W|^δ) · h`, i.e. `E|ξ_0|^δ = O(h)`.

Three steps: pull `|W((X_0−x)/h)|^δ` out of the conditional expectation of `|e_0|^δ`
(`integral_bdd_comp_mul_eq_of_condExp`, legitimate because `|W|^δ ≤ CW^δ` is bounded),
substitute the density (`integral_comp_eq_integral_density`), and rescale
(`integral_dilate_translate`); the factor `h` is the Jacobian. Integrability of `|W|^δ`
comes from `|W|^δ ≤ CW^{δ−2} W²` — the only place `δ > 2` is used here. -/
theorem localized_delta_moment_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0))
    {p : ℝ → ℝ} (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {δ : ℝ} (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    {M : ℝ}
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {x hn : ℝ} (hhn : 0 < hn) :
    ∫ ω, |e 0 ω * W ((X 0 ω - x) / hn)| ^ δ ∂μ
      ≤ (M * Cp * ∫ v, |W v| ^ δ) * hn := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (hp0 0) (hpb 0)
  have hrp : Measurable (fun y : ℝ => y ^ δ) :=
    (Real.continuous_rpow_const hδ0.le).measurable
  have hWam : Measurable (fun v => |W v| ^ δ) := hrp.comp hWm.abs
  have hGm : Measurable (fun v => |W ((v - x) / hn)| ^ δ) :=
    hrp.comp ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).abs)
  -- `|W|^δ` is integrable: `|W|^δ ≤ CW^{δ-2} W²`
  have hWδ : Integrable (fun v => |W v| ^ δ) MeasureTheory.volume := by
    refine Integrable.mono (hW2.const_mul (CW ^ (δ - 2))) hWam.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    have hsplit : |W v| ^ δ = |W v| ^ (δ - 2) * |W v| ^ (2 : ℝ) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by intro hcon; linarith),
        show δ - 2 + 2 = δ from by ring]
    have h2 : |W v| ^ (2 : ℝ) = W v ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    have hle : |W v| ^ (δ - 2) ≤ CW ^ (δ - 2) :=
      Real.rpow_le_rpow (abs_nonneg _) (hWb v) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hsplit, h2,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ (δ - 2) * W v ^ 2)]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  have hG0 : ∀ v : ℝ, 0 ≤ |W ((v - x) / hn)| ^ δ := fun v => Real.rpow_nonneg (abs_nonneg _) _
  have hGb : ∀ v : ℝ, |(|W ((v - x) / hn)| ^ δ)| ≤ CW ^ δ := by
    intro v
    rw [abs_of_nonneg (hG0 v)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le
  -- `|e_0|^δ` is integrable
  have hζ : Integrable (fun ω => |e 0 ω| ^ δ) μ := by
    have hr := heLδ.integrable_norm_rpow (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0) ENNReal.ofReal_ne_top
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ0.le] using hr
  have hZ0 : (0 : Ω → ℝ)
      ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
    condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  have hM0 : (0 : ℝ) ≤ M := by
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  have hGXm : Measurable (fun ω => |W ((X 0 ω - x) / hn)| ^ δ) := hGm.comp hX
  -- tower: replace `|e_0|^δ` by its conditional expectation, then bound by `M`
  have htow : ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * |e 0 ω| ^ δ ∂μ
      = ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) *
          (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ :=
    integral_bdd_comp_mul_eq_of_condExp hX hζ (Filter.EventuallyEq.refl _ _)
      (fun v => |W ((v - x) / hn)| ^ δ) hGm hGb
  have hmono : ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ
      ≤ ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * M ∂μ := by
    refine integral_mono_ae
      (integrable_condExp.bdd_mul hGXm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _))
      ((integrable_const M).bdd_mul hGXm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _)) ?_
    filter_upwards [heδc] with ω hω
    exact mul_le_mul_of_nonneg_left hω (hG0 _)
  -- density substitution and the affine change of variables
  have hdens : ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * M ∂μ
      = M * ∫ v, p v * |W ((v - x) / hn)| ^ δ := by
    have hsub : ∫ ω, (fun v => |W ((v - x) / hn)| ^ δ * M) (X 0 ω) ∂μ
        = ∫ v, p v * (|W ((v - x) / hn)| ^ δ * M) :=
      integral_comp_eq_integral_density hX hmp hp0 hpd
        (fun v => |W ((v - x) / hn)| ^ δ * M) (hGm.mul_const M)
    have hpull : ∫ v, p v * (|W ((v - x) / hn)| ^ δ * M)
        = M * ∫ v, p v * |W ((v - x) / hn)| ^ δ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun v => by ring)
    rw [← hpull, ← hsub]
  have hcov : ∫ u, |W u| ^ δ * p (x + hn * u) = hn⁻¹ * ∫ v, |W ((v - x) / hn)| ^ δ * p v :=
    integral_dilate_translate (fun u => |W u| ^ δ) p x hhn
  have hpint : ∫ v, p v * |W ((v - x) / hn)| ^ δ
      = hn * ∫ u, |W u| ^ δ * p (x + hn * u) := by
    rw [hcov, ← mul_assoc, mul_inv_cancel₀ hhn.ne', one_mul]
    exact integral_congr_ae (Eventually.of_forall fun v => by ring)
  have hlast : ∫ u, |W u| ^ δ * p (x + hn * u) ≤ Cp * ∫ u, |W u| ^ δ := by
    have hi : Integrable (fun u => |W u| ^ δ * p (x + hn * u)) MeasureTheory.volume := by
      refine Integrable.mono (hWδ.const_mul Cp)
        (hWam.mul (hmp.comp (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hp0 _)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Cp * |W u| ^ δ), mul_comm Cp]
      exact mul_le_mul_of_nonneg_left (hpb _) (Real.rpow_nonneg (abs_nonneg _) _)
    rw [← integral_const_mul]
    refine integral_mono hi (hWδ.const_mul Cp) fun u => ?_
    rw [mul_comm Cp]
    exact mul_le_mul_of_nonneg_left (hpb _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hstart : ∫ ω, |e 0 ω * W ((X 0 ω - x) / hn)| ^ δ ∂μ
      = ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * |e 0 ω| ^ δ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change |e 0 ω * W ((X 0 ω - x) / hn)| ^ δ = |W ((X 0 ω - x) / hn)| ^ δ * |e 0 ω| ^ δ
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm]
  rw [hstart, htow]
  calc ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ
      ≤ ∫ ω, (|W ((X 0 ω - x) / hn)| ^ δ) * M ∂μ := hmono
    _ = M * ∫ v, p v * |W ((v - x) / hn)| ^ δ := hdens
    _ = M * (hn * ∫ u, |W u| ^ δ * p (x + hn * u)) := by rw [hpint]
    _ ≤ M * (hn * (Cp * ∫ u, |W u| ^ δ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hhn.le) hM0
    _ = (M * Cp * ∫ v, |W v| ^ δ) * hn := by ring

/-! #### FY (2.82)–(2.83): the truncation tail

Step (c) truncates `e` at level `L`; what the telescope needs is that the residual
`e_t − e^L_t` contributes a variance that vanishes as `L → ∞`, *uniformly in `n`*. The two
bricks below are the diagonal half of that estimate — the half that (C1)–(C5) as
formalized do support. (The lag half does not close; see `tendsto_smallBlock_variance`.) -/

/-- **Pointwise truncation residual — PROVED.** `(z − clamp_L z)² ≤ L^{2−δ} |z|^δ` for
`δ > 2`, `L > 0`. Below the clamp the left side is `0`; above it `|z − clamp_L z| ≤ |z|`
and `|z|² = |z|^{2−δ}|z|^δ ≤ L^{2−δ}|z|^δ`, the exponent `2 − δ` being negative. This is
where `δ > 2` buys the `L → ∞` decay of the truncation tail. -/
theorem sq_sub_clamp_le {δ L z : ℝ} (hδ : 2 < δ) (hL : 0 < L) :
    (z - clampAt L z) ^ 2 ≤ L ^ (2 - δ) * |z| ^ δ := by
  have hd : (0 : ℝ) < δ - 2 := by linarith
  have hLd : (0 : ℝ) < L ^ (2 - δ) := Real.rpow_pos_of_pos hL _
  rcases le_or_gt |z| L with hz | hz
  · have h1 : min L z = z := min_eq_right (le_trans (le_abs_self z) hz)
    have h2 : max (-L) z = z := max_eq_right (by
      have := neg_abs_le z; linarith)
    have hz0 : z - clampAt L z = 0 := by simp [clampAt, h1, h2]
    have hzz : ((0 : ℝ)) ^ 2 = 0 := by norm_num
    rw [hz0, hzz]
    positivity
  · have hzpos : (0 : ℝ) < |z| := lt_trans hL hz
    -- `|z − clamp| ≤ |z|`
    have hkey : (z - clampAt L z) ^ 2 ≤ |z| ^ (2 : ℝ) := by
      have h2 : |z| ^ (2 : ℝ) = z ^ 2 := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
      rw [h2]
      have habs : |z - clampAt L z| ≤ |z| := by
        rcases le_or_gt z 0 with hz0 | hz0
        · have hzneg : z < -L := by
            rw [abs_of_nonpos hz0] at hz; linarith
          have h1 : min L z = z := min_eq_right (by linarith)
          have h2 : max (-L) z = -L := max_eq_left (by linarith)
          simp only [clampAt, h1, h2]
          rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
          linarith
        · have hzpos' : L < z := by rw [abs_of_pos hz0] at hz; exact hz
          have h1 : min L z = L := min_eq_left (by linarith)
          have h2 : max (-L) L = L := max_eq_right (by linarith)
          simp only [clampAt, h1, h2]
          rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
          linarith
      have h3 : |z - clampAt L z| * |z - clampAt L z| ≤ |z| * |z| :=
        mul_le_mul habs habs (abs_nonneg _) (abs_nonneg _)
      calc (z - clampAt L z) ^ 2
          = |z - clampAt L z| * |z - clampAt L z| := by rw [← sq_abs, pow_two]
        _ ≤ |z| * |z| := h3
        _ = z ^ 2 := by rw [← pow_two, sq_abs]
    refine hkey.trans ?_
    have hstep : L ^ (δ - 2) ≤ |z| ^ (δ - 2) :=
      Real.rpow_le_rpow hL.le hz.le hd.le
    have hsplit : |z| ^ δ = |z| ^ (2 : ℝ) * |z| ^ (δ - 2) := by
      rw [← Real.rpow_add hzpos]; ring_nf
    have hmul : |z| ^ (2 : ℝ) * L ^ (δ - 2) ≤ |z| ^ δ := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg (abs_nonneg _) _)
    have hone : L ^ (2 - δ) * L ^ (δ - 2) = 1 := by
      rw [← Real.rpow_add hL]; norm_num
    have h4 := mul_le_mul_of_nonneg_left hmul hLd.le
    have h5 : L ^ (2 - δ) * (|z| ^ (2 : ℝ) * L ^ (δ - 2)) = |z| ^ (2 : ℝ) := by
      rw [← mul_assoc, mul_comm (L ^ (2 - δ)) (|z| ^ (2 : ℝ)), mul_assoc, hone, mul_one]
    linarith [h4, h5]

/-- **FY (2.82)–(2.83), the diagonal of the truncation tail — PROVED.** The localized
second moment of the truncation residual carries *both* small factors at once:
`E[(e_0 − clamp_L e_0)² W((X_0−x)/h)²] ≤ (M · C_p · ∫W²) · L^{2−δ} h`,
so after the `h⁻¹` of the normalization it is `O(L^{2−δ})` — vanishing as `L → ∞`
uniformly in `n` and in the bandwidth, which is exactly the uniformity (2.82) needs.

Same three steps as `localized_delta_moment_le`, with the weight `|W|^δ` replaced by `W²`:
dominate pointwise by `L^{2−δ} |e_0|^δ W²` (`sq_sub_clamp_le`), pull `W²` out of the
conditional expectation of `|e_0|^δ` and bound the latter by `M`
(`integral_bdd_comp_mul_eq_of_condExp` with `heδc`), then substitute the density
(`integral_comp_eq_integral_density`) and rescale (`integral_dilate_translate`), the factor
`h` being the Jacobian and `C_p` the density bound.

This bounds the residual *before* its conditional recentring; since
`e_t − e^L_t = r_t − E(r_t | X_t)` with `r_t = e_t − clamp_L(e_t)`, conditional Jensen
turns it into the same bound for the recentred residual at no cost. What it does **not**
give — and what blocks (2.82) as a whole — is the corresponding *lag* estimate; see
`tendsto_smallBlock_variance` for the proof that the frozen (C2) cannot supply it. -/
theorem localized_trunc_residual_moment_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hX : Measurable (X 0)) (hE : Measurable (e 0))
    {p : ℝ → ℝ} (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {δ : ℝ} (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    {M : ℝ}
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {x hn L : ℝ} (hhn : 0 < hn) (hL : 0 < L) :
    ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / hn) ^ 2 ∂μ
      ≤ (M * Cp * ∫ v, W v ^ 2) * (L ^ (2 - δ) * hn) := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hLd : (0 : ℝ) < L ^ (2 - δ) := Real.rpow_pos_of_pos hL _
  have hGm : Measurable (fun v => W ((v - x) / hn) ^ 2) :=
    ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).pow_const 2)
  have hG0 : ∀ v : ℝ, 0 ≤ W ((v - x) / hn) ^ 2 := fun v => sq_nonneg _
  have hGb : ∀ v : ℝ, |W ((v - x) / hn) ^ 2| ≤ CW ^ 2 := by
    intro v
    rw [abs_of_nonneg (hG0 v)]
    nlinarith [hWb ((v - x) / hn), abs_nonneg (W ((v - x) / hn)),
      sq_abs (W ((v - x) / hn))]
  have hGXm : Measurable (fun ω => W ((X 0 ω - x) / hn) ^ 2) := hGm.comp hX
  -- `|e_0|^δ` is integrable
  have hζ : Integrable (fun ω => |e 0 ω| ^ δ) μ := by
    have hr := heLδ.integrable_norm_rpow (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0) ENNReal.ofReal_ne_top
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ0.le] using hr
  have hZ0 : (0 : Ω → ℝ)
      ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
    condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  have hM0 : (0 : ℝ) ≤ M := by
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  -- Step 1: pointwise domination by `L^{2−δ} |e|^δ W²`
  have hdom' : Integrable (fun ω => W ((X 0 ω - x) / hn) ^ 2 * |e 0 ω| ^ δ) μ :=
    hζ.bdd_mul hGXm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _)
  have hdom : Integrable (fun ω => (|e 0 ω| ^ δ) * W ((X 0 ω - x) / hn) ^ 2) μ :=
    hdom'.congr (Eventually.of_forall fun ω => mul_comm _ _)
  have hint1 : Integrable
      (fun ω => (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / hn) ^ 2) μ := by
    refine Integrable.mono (hdom.const_mul (L ^ (2 - δ)))
      (((((hE.sub ((measurable_const.max (measurable_const.min hE))))).pow_const
        2)).mul hGXm).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ L ^ (2 - δ) *
        ((|e 0 ω| ^ δ) * W ((X 0 ω - x) / hn) ^ 2)), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (sq_sub_clamp_le hδ hL) (sq_nonneg _)
  have hstep1 : ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / hn) ^ 2 ∂μ
      ≤ L ^ (2 - δ) * ∫ ω, (|e 0 ω| ^ δ) * W ((X 0 ω - x) / hn) ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono hint1 (hdom.const_mul _) fun ω => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (sq_sub_clamp_le hδ hL) (sq_nonneg _)
  -- Step 2: tower + density + rescaling, exactly as in `localized_delta_moment_le`
  have htow : ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) * |e 0 ω| ^ δ ∂μ
      = ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) *
          (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ :=
    integral_bdd_comp_mul_eq_of_condExp hX hζ (Filter.EventuallyEq.refl _ _)
      (fun v => W ((v - x) / hn) ^ 2) hGm hGb
  have hmono : ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ
      ≤ ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) * M ∂μ := by
    refine integral_mono_ae
      (integrable_condExp.bdd_mul hGXm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _))
      ((integrable_const M).bdd_mul hGXm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hGb _)) ?_
    filter_upwards [heδc] with ω hω
    exact mul_le_mul_of_nonneg_left hω (hG0 _)
  have hdens : ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) * M ∂μ
      = M * ∫ v, p v * W ((v - x) / hn) ^ 2 := by
    have hsub : ∫ ω, (fun v => W ((v - x) / hn) ^ 2 * M) (X 0 ω) ∂μ
        = ∫ v, p v * (W ((v - x) / hn) ^ 2 * M) :=
      integral_comp_eq_integral_density hX hmp hp0 hpd
        (fun v => W ((v - x) / hn) ^ 2 * M) (hGm.mul_const M)
    have hpull : ∫ v, p v * (W ((v - x) / hn) ^ 2 * M)
        = M * ∫ v, p v * W ((v - x) / hn) ^ 2 := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun v => by ring)
    rw [← hpull, ← hsub]
  have hcov : ∫ u, W u ^ 2 * p (x + hn * u) = hn⁻¹ * ∫ v, W ((v - x) / hn) ^ 2 * p v :=
    integral_dilate_translate (fun u => W u ^ 2) p x hhn
  have hpint : ∫ v, p v * W ((v - x) / hn) ^ 2
      = hn * ∫ u, W u ^ 2 * p (x + hn * u) := by
    rw [hcov, ← mul_assoc, mul_inv_cancel₀ hhn.ne', one_mul]
    exact integral_congr_ae (Eventually.of_forall fun v => by ring)
  have hlast : ∫ u, W u ^ 2 * p (x + hn * u) ≤ Cp * ∫ u, W u ^ 2 := by
    have hi : Integrable (fun u => W u ^ 2 * p (x + hn * u)) MeasureTheory.volume := by
      refine Integrable.mono (hW2.const_mul Cp)
        (((hWm.pow_const 2)).mul (hmp.comp (measurable_const.add
          (measurable_const.mul measurable_id)))).aestronglyMeasurable
        (Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (hp0 _)),
        abs_of_nonneg (mul_nonneg (le_trans (hp0 0) (hpb 0)) (sq_nonneg _)), mul_comm Cp]
      exact mul_le_mul_of_nonneg_left (hpb _) (sq_nonneg _)
    rw [← integral_const_mul]
    refine integral_mono hi (hW2.const_mul Cp) fun u => ?_
    rw [mul_comm Cp]
    exact mul_le_mul_of_nonneg_left (hpb _) (sq_nonneg _)
  have hcomm : ∫ ω, (|e 0 ω| ^ δ) * W ((X 0 ω - x) / hn) ^ 2 ∂μ
      = ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) * |e 0 ω| ^ δ ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have hchain : ∫ ω, (|e 0 ω| ^ δ) * W ((X 0 ω - x) / hn) ^ 2 ∂μ
      ≤ (M * Cp * ∫ v, W v ^ 2) * hn := by
    rw [hcomm, htow]
    calc ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) *
          (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω ∂μ
        ≤ ∫ ω, (W ((X 0 ω - x) / hn) ^ 2) * M ∂μ := hmono
      _ = M * ∫ v, p v * W ((v - x) / hn) ^ 2 := hdens
      _ = M * (hn * ∫ u, W u ^ 2 * p (x + hn * u)) := by rw [hpint]
      _ ≤ M * (hn * (Cp * ∫ u, W u ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlast hhn.le) hM0
      _ = (M * Cp * ∫ v, W v ^ 2) * hn := by ring
  calc ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / hn) ^ 2 ∂μ
      ≤ L ^ (2 - δ) * ∫ ω, (|e 0 ω| ^ δ) * W ((X 0 ω - x) / hn) ^ 2 ∂μ := hstep1
    _ ≤ L ^ (2 - δ) * ((M * Cp * ∫ v, W v ^ 2) * hn) :=
        mul_le_mul_of_nonneg_left hchain hLd.le
    _ = (M * Cp * ∫ v, W v ^ 2) * (L ^ (2 - δ) * hn) := by ring


/-! #### Bandwidth limits behind the small/large lag split -/

/-- `h_n → 0⁺` in the punctured-right sense. -/
theorem tendsto_nhdsGT_of_pos {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) : Tendsto h atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within h hh
    (Eventually.of_forall fun n => hh0 n)

/-- `|log h_n| → ∞`. -/
theorem tendsto_abs_log_atTop {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => |Real.log (h n)|) atTop atTop :=
  tendsto_abs_atBot_atTop.comp
    (Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsGT_of_pos hh0 hh))

/-- **FY's `m_n h_n → 0`.** The small-lag cut `m_n = [1/(h|log h|)]` costs only
`1/|log h|` after multiplication by `h`; this is exactly why FY cuts there. -/
theorem tendsto_smallLagCut_mul_bandwidth {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => (smallLagCut h n : ℝ) * h n) atTop (𝓝 0) := by
  have hL := tendsto_abs_log_atTop hh0 hh
  have hLinv : Tendsto (fun n => |Real.log (h n)|⁻¹) atTop (𝓝 0) := hL.inv_tendsto_atTop
  refine squeeze_zero' (Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg _) (hh0 n).le) ?_
    (by simpa using hLinv.add hh)
  filter_upwards [hL.eventually_gt_atTop 0] with n hLn
  have hhn := hh0 n
  have hx : (0 : ℝ) ≤ (h n * |Real.log (h n)|)⁻¹ := by positivity
  have hceil : ((smallLagCut h n : ℕ) : ℝ) < (h n * |Real.log (h n)|)⁻¹ + 1 :=
    Nat.ceil_lt_add_one hx
  have hstep : ((smallLagCut h n : ℕ) : ℝ) * h n
      ≤ ((h n * |Real.log (h n)|)⁻¹ + 1) * h n :=
    mul_le_mul_of_nonneg_right hceil.le hhn.le
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- `h^a |log h|^λ → 0` for `a, λ > 0`: the large-lag remainder's shape. -/
theorem tendsto_rpow_mul_abs_log_rpow {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) {a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    Tendsto (fun n => h n ^ a * |Real.log (h n)| ^ lam) atTop (𝓝 0) := by
  -- the base sequence `h^{a/λ} |log h| → 0`
  have hφ : Tendsto (fun y : ℝ => y ^ (a / lam) * |Real.log y|) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => Real.log y * y ^ (a / lam)) (𝓝[>] 0) (𝓝 0) :=
      _root_.tendsto_log_mul_rpow_nhdsGT_zero (by positivity)
    have h2 : Tendsto (fun y : ℝ => |Real.log y * y ^ (a / lam)|) (𝓝[>] 0) (𝓝 0) := by
      simpa using h1.abs
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hy0.le _), mul_comm]
  have hbase : Tendsto (fun n => h n ^ (a / lam) * |Real.log (h n)|) atTop (𝓝 0) :=
    hφ.comp (tendsto_nhdsGT_of_pos hh0 hh)
  -- raise to the power `λ`
  have hcont : Tendsto (fun y : ℝ => y ^ lam) (𝓝 0) (𝓝 0) := by
    have hz : (0 : ℝ) ^ lam = 0 := Real.zero_rpow hlam.ne'
    have ht := (Real.continuousAt_rpow_const (0 : ℝ) lam (Or.inr hlam.le)).tendsto
    rw [hz] at ht
    exact ht
  have hcomp := hcont.comp hbase
  refine hcomp.congr fun n => ?_
  have hhn := hh0 n
  simp only [Function.comp_apply]
  rw [Real.mul_rpow (Real.rpow_nonneg hhn.le _) (abs_nonneg _), ← Real.rpow_mul hhn.le,
    div_mul_cancel₀ _ hlam.ne']

/-- **FY (2.73)–(2.76), the ledger-(a) headline — PROVED under the authorized (2.74)
repair.** `(n h_n)⁻¹ Var(S_n(x)) → σ²(x) p(x) ∫ W²`.

Assembled from three inputs: the diagonal (`tendsto_localized_second_moment_debt`, now
**proved** under the authorized (C1) repair), the small lags `1 ≤ j ≤ smallLagCut h n`
via `small_lag_covariance_bound` (total `m_n · h² / h = h/|log h| → 0`), and the large
lags `j > smallLagCut h n` via `large_lag_covariance_bound` + (C3)'s weighted summability
(`Σ_{j>m} α^{1−2/δ}(j) ≤ m^{−λ} Σ j^λ α^{1−2/δ}(j)`). Stationarity (`hstat`) turns the
double sum over `1 ≤ s, t ≤ n` into `n` times a single lag sum. Mean-zero of each summand
(from `hce` through `integral_bdd_comp_mul_eq_of_condExp`) is what lets the variance be
read off the second moment.

**Why the repair is needed — BLOCKED AS FROZEN (verified; a *separate* gap from the one
the `hσm`/`hσpb` repair fixes).** The large-lag half does not close under (C1)–(C5) as
formalized here,
for any `λ ≤ 1`. FY's step is `|Cov(ξ_0, ξ_j)| ≤ 8 α(j)^{1−2/δ} ‖ξ_0‖_δ ‖ξ_j‖_δ` with the
**kernel-localized δ-norm** `‖ξ_0‖_δ² = O(h^{2/δ})`, i.e. `E|ξ_0|^δ = O(h)`; then
`h⁻¹ · h^{2/δ} · m_n^{−λ} = h^{λ + 2/δ − 1} |log h|^λ → 0`, which is *exactly* (C3)'s
`λ > 1 − 2/δ`. But `E|ξ_0|^δ = E[|e_0|^δ |W((X_0−x)/h)|^δ]` factorizes only through a
**conditional** δ-moment `E(|e_0|^δ | X_0) ≤ M` (with `p` bounded), and the frozen (C1)
supplies only the *unconditional* `MemLp (e 0) δ` (`heLδ`), which gives merely
`‖ξ_0‖_δ ≤ CW ‖e_0‖_δ = O(1)` — no `h`-gain at all.

The gap is not repairable by interpolating the inputs that *are* available. Writing
`β = 1 − 2/δ`, what the file has is `‖ξ_0‖_2 = O(√h)` (this **is** new, and comes from the
authorized repair: `E ξ_0² = ∫ (σ²p)(x+hu)W(u)²du ≤ C h ∫W²`), `‖ξ_0‖_δ = O(1)`, and the
`(C2)` bound `|E[ξ_0 ξ_j]| = O(h²)` valid at *every* lag. Hölder interpolation at
`2 < q ≤ δ` gives `‖ξ_0‖_q = O(h^{θ/2})` with `1/q = θ/2 + (1−θ)/δ`, and the Davydov
exponent is then `1 − 2/q = β(1−θ)`, so the large-lag total is
`h^{θ−1} Σ_{j>m} α(j)^{β(1−θ)}`. With `s := 1 − θ`, `(C3)` gives only
`α(j)^β = o(j^{−λ})`, hence `α(j)^{βs} = o(j^{−λs})`, whose tail converges only when
`λ s > 1`; since `s ≤ 1` this forces `λ > 1`. Taking instead the `(C2)` bound on the same
range costs `n h → ∞`. So for `λ ∈ (1 − 2/δ, 1]` — the range (C3) actually allows —
every combination of the frozen inputs diverges.

**Missing input, precisely.** FY's implicit (2.74): `E|ξ_0|^δ ≤ K h` (equivalently:
`E(|e_0|^δ | X_0) ≤ M` a.e. together with `p` bounded). This is a *third* silent reading
of (C1), independent of the two already authorized (`hσm`, `hσpb` bound `σ²·p`, i.e. the
**second** conditional moment; they do not bound the δ-th).

**Statement strengthening (documented).** FY's (C1) as printed asserts only the
*unconditional* `E|e_1|^δ < ∞` (`heLδ`). We additionally assume its **conditional** form
`E(|e_0|^δ | X_0) ≤ M` a.e. (`heδc`) together with a bounded density (`hpb`) — FY's
implicit (2.74), the *third* silent reading of (C1). The paragraph above is the proof
that no weaker package built from the frozen hypotheses suffices: interpolating the
available `‖ξ_0‖_2 = O(√h)`, `‖ξ_0‖_δ = O(1)` and the (C2) bound leaves a large-lag tail
that converges only for `λ > 1`, whereas (C3) as frozen allows `λ ∈ (1 − 2/δ, 1]`. The two
hypotheses are spent in exactly one place, `localized_delta_moment_le`, which converts
them into `E|ξ_0|^δ ≤ (M · Cp · ∫|W|^δ) h`; nothing else in the proof sees them. They
propagate to `tendsto_charFun_locTruncSum` and to the Theorem 2.22 headline
`kernel_localized_clt`, which consume ledger (a). Note that `hnh` ((C5)'s `n h³ → ∞`),
`hpx`, and `hW1` are *not* needed for the variance asymptotics — only `h_n → 0` is — and
are kept because they are part of the frozen (C1)–(C5) package. -/
theorem var_localized_sum [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ x : ℝ}
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT (authorized (C1) repair): σ² measurable; FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {M Cp : ℝ}
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (hpb : ∀ v, p v ≤ Cp)
    -- (C2) USER-INPUT: (C2) as printed (conditional joint density bounded); FY §2.6.4
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ Finset.range n,
          e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
      atTop (𝓝 (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume)) := by
  obtain ⟨B, hB0, hC2gen⟩ := hC2
  -- (2.74), in the form FY actually uses it: `E|ξ_0|^δ ≤ K h`.
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ n : ℕ,
      ∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ ≤ K * h n :=
    ⟨M * Cp * ∫ v, |W v| ^ δ, fun n =>
      localized_delta_moment_le (hmeasX 0) hmp hp0 hpd hδ heLδ heδc hpb hWm hWb hW2 (hh0 n)⟩
  -- numerology
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hδ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hδ2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have he1 : Integrable (e 0) μ := heLδ.integrable hδ1
  have he2 : Integrable (fun ω => e 0 ω ^ 2) μ := (heLδ.mono_exponent hδ2).integrable_sq
  -- the localized summand, as a function of the pair `(X_t, e_t)`
  have hFm : ∀ hn : ℝ, Measurable (fun z : ℝ × ℝ => z.2 * W ((z.1 - x) / hn)) := by
    intro hn; fun_prop
  -- localized summands: measurability, L^δ and L²
  have hmξ : ∀ (hn : ℝ) (t : ℤ), Measurable (fun ω => e t ω * W ((X t ω - x) / hn)) := fun hn t =>
    (hmeasE t).mul (hWm.comp (((hmeasX t).sub measurable_const).div measurable_const))
  have hLδ0 : ∀ hn : ℝ, MemLp (fun ω => e 0 ω * W ((X 0 ω - x) / hn)) (ENNReal.ofReal δ) μ := by
    intro hn
    refine MemLp.of_le (heLδ.const_mul CW) (hmξ hn 0).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hCW0]
    nlinarith [hWb ((X 0 ω - x) / hn), abs_nonneg (e 0 ω), abs_nonneg (W ((X 0 ω - x) / hn))]
  have hLδt : ∀ (hn : ℝ) (t : ℤ),
      MemLp (fun ω => e t ω * W ((X t ω - x) / hn)) (ENNReal.ofReal δ) μ := fun hn t =>
    memLp_comp_pair hmeasX hmeasE hstat t (hFm hn) (hLδ0 hn)
  have hL2t : ∀ (hn : ℝ) (t : ℤ), MemLp (fun ω => e t ω * W ((X t ω - x) / hn)) 2 μ :=
    fun hn t => (hLδt hn t).mono_exponent hδ2
  have hint : ∀ (hn : ℝ) (s t : ℤ), Integrable (fun ω =>
      (e s ω * W ((X s ω - x) / hn)) * (e t ω * W ((X t ω - x) / hn))) μ := fun hn s t =>
    (hL2t hn s).integrable_mul (hL2t hn t)
  -- each localized summand is centred
  have hmean0 : ∀ hn : ℝ, ∫ ω, e 0 ω * W ((X 0 ω - x) / hn) ∂μ = 0 := by
    intro hn
    have hz := integral_bdd_comp_mul_eq_of_condExp (μ := μ) (hmeasX 0) he1 hce
      (fun v => W ((v - x) / hn)) (by fun_prop) (C := CW) (fun v => hWb _)
    calc ∫ ω, e 0 ω * W ((X 0 ω - x) / hn) ∂μ
        = ∫ ω, W ((X 0 ω - x) / hn) * e 0 ω ∂μ :=
          integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
      _ = ∫ ω, W ((X 0 ω - x) / hn) * (0 : Ω → ℝ) ω ∂μ := hz
      _ = 0 := by simp
  -- lag covariances and the pair covariance array
  set Gl : ℕ → ℕ → ℝ := fun n j =>
    ∫ ω, (e 0 ω * W ((X 0 ω - x) / h n)) *
      (e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / h n)) ∂μ with hGldef
  set Cl : ℕ → ℕ → ℕ → ℝ := fun n s t =>
    ∫ ω, (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
      (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ∂μ with hCldef
  have hCG : ∀ n s d : ℕ, Cl n s (s + d) = Gl n d := by
    intro n s d
    have hidx : ((s + d : ℕ) : ℤ) + 1 = ((s : ℤ) + 1) + (d : ℤ) := by push_cast; ring
    have htr : ∫ ω, (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
          (e (((s : ℤ) + 1) + (d : ℤ)) ω *
            W ((X (((s : ℤ) + 1) + (d : ℤ)) ω - x) / h n)) ∂μ
        = ∫ ω, (e 0 ω * W ((X 0 ω - x) / h n)) *
          (e ((d : ℕ) : ℤ) ω * W ((X ((d : ℕ) : ℤ) ω - x) / h n)) ∂μ :=
      integral_comp_pair2_eq hmeasX hmeasE hstat ((s : ℤ) + 1) d
        (G := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
          (z.1.2 * W ((z.1.1 - x) / h n)) * (z.2.2 * W ((z.2.1 - x) / h n)))
        (by fun_prop)
    simp only [hCldef, hGldef, hidx]
    exact htr
  have hCG' : ∀ n s d : ℕ, Cl n (s + d) s = Gl n d := by
    intro n s d
    have hsym : Cl n (s + d) s = Cl n s (s + d) := by
      simp only [hCldef]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsym, hCG]
  have hG0 : ∀ n : ℕ, Gl n 0 = ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
    intro n
    simp only [hGldef, Nat.cast_zero]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  -- the square of the localized sum expands into the covariance array
  have hexp : ∀ n : ℕ, ∫ ω, (∑ t ∈ Finset.range n,
        e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
      = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cl n s t := by
    intro n
    have hsq : ∀ ω : Ω, (∑ t ∈ Finset.range n,
          e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2
        = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
            (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
              (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) := by
      intro ω
      rw [sq, Finset.sum_mul_sum]
    simp only [hsq, hCldef]
    have h1 : ∫ ω, (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
          (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
            (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n))) ∂μ
        = ∑ s ∈ Finset.range n, ∫ ω, (∑ t ∈ Finset.range n,
            (e ((s : ℤ) + 1) ω * W ((X ((s : ℤ) + 1) ω - x) / h n)) *
              (e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n))) ∂μ :=
      integral_finset_sum _ (fun s _ =>
        integrable_finset_sum _ (fun t _ => hint (h n) ((s : ℤ) + 1) ((t : ℤ) + 1)))
    rw [h1]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact integral_finset_sum _ (fun t _ => hint (h n) ((s : ℤ) + 1) ((t : ℤ) + 1))
  -- the δ-th moment input (2.74), in eLpNorm form, at every time
  have hK0 : (0 : ℝ) ≤ K := by
    have h1 : (0 : ℝ) ≤ ∫ ω, |e 0 ω * W ((X 0 ω - x) / h 0)| ^ δ ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
    have h2 := hK 0
    have h3 := hh0 0
    nlinarith
  have hnormδ : ∀ (n : ℕ) (t : ℤ),
      (eLpNorm (fun ω => e t ω * W ((X t ω - x) / h n)) (ENNReal.ofReal δ) μ).toReal
        ≤ (K * h n) ^ (1 / δ) := by
    intro n t
    have hEq : eLpNorm (fun ω => e t ω * W ((X t ω - x) / h n)) (ENNReal.ofReal δ) μ
        = eLpNorm (fun ω => e 0 ω * W ((X 0 ω - x) / h n)) (ENNReal.ofReal δ) μ :=
      eLpNorm_comp_pair_eq hmeasX hmeasE hstat t (hFm (h n)) _
    rw [hEq]
    have hp1 : (ENNReal.ofReal δ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0
    have hform := (hLδ0 (h n)).eLpNorm_eq_integral_rpow_norm hp1 ENNReal.ofReal_ne_top
    have hbase : (0 : ℝ) ≤ ∫ a, ‖e 0 a * W ((X 0 a - x) / h n)‖ ^ δ ∂μ :=
      integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
    rw [hform]
    simp only [ENNReal.toReal_ofReal hδ0.le]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hbase _), ← one_div]
    have hnn : ∫ a, ‖e 0 a * W ((X 0 a - x) / h n)‖ ^ δ ∂μ ≤ K * h n := by
      simpa only [Real.norm_eq_abs] using hK n
    exact Real.rpow_le_rpow hbase hnn (by positivity)
  -- (C2) as printed, at the weight `f = e_0 e_j`: this is FY's (2.76) instance. The
  -- normalization `E|e_0 e_j| ≤ E e_0²` is `2|ab| ≤ a² + b²` plus stationarity.
  have hL2e : ∀ t : ℤ, MemLp (e t) 2 μ := by
    intro t
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => z.2) (X 0 ω, e 0 ω)) 2 μ :=
      heLδ.mono_exponent hδ2
    exact memLp_comp_pair hmeasX hmeasE hstat t measurable_snd h0
  have he2t : ∀ t : ℤ, ∫ ω, e t ω ^ 2 ∂μ = ∫ ω, e 0 ω ^ 2 ∂μ := fun t =>
    integral_comp_pair_eq hmeasX hmeasE hstat t
      (F := fun z : ℝ × ℝ => z.2 ^ 2) (by fun_prop)
  have hB : ∀ j : ℤ, j ≠ 0 → ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |e 0 ω * e j ω| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume) := by
    intro j hj g hgm hg0
    have hkey := hC2gen j hj (fun z : ℝ × ℝ => z.1 * z.2) (by fun_prop) g hgm hg0
    simp only at hkey
    refine hkey.trans ?_
    have hgint : (0 : ℝ) ≤ ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume) :=
      integral_nonneg hg0
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hB0) hgint
    have habs : Integrable (fun ω => |e 0 ω * e j ω|) μ :=
      ((hL2e 0).integrable_mul (hL2e j)).abs
    have hsq0 : Integrable (fun ω => e 0 ω ^ 2) μ := (hL2e 0).integrable_sq
    have hsqj : Integrable (fun ω => e j ω ^ 2) μ := (hL2e j).integrable_sq
    have hmid : ∫ ω, |e 0 ω * e j ω| ∂μ ≤ ∫ ω, (e 0 ω ^ 2 + e j ω ^ 2) / 2 ∂μ := by
      refine integral_mono habs ((hsq0.add hsqj).div_const 2) fun ω => ?_
      nlinarith [sq_nonneg (|e 0 ω| - |e j ω|), sq_abs (e 0 ω), sq_abs (e j ω),
        abs_mul (e 0 ω) (e j ω), abs_nonneg (e 0 ω), abs_nonneg (e j ω)]
    refine hmid.trans (le_of_eq ?_)
    rw [integral_div, integral_add hsq0 hsqj, he2t j]
    ring
  -- (2.76): the small-lag bound
  have hsmall : ∀ (n j : ℕ), 1 ≤ j →
      |Gl n j| ≤ B * (∫ ω, e 0 ω ^ 2 ∂μ) * ((∫ v, |W v|) * h n) ^ 2 := by
    intro n j hj
    have hjz : ((j : ℤ)) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    simp only [hGldef]
    exact small_lag_covariance_bound hWm hB (hh0 n) (j : ℤ) hjz
  -- (2.75): the large-lag bound, with the localized δ-norms
  have hlarge : ∀ (n j : ℕ), 1 ≤ j →
      |Gl n j| ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (K * h n) ^ (2 / δ) := by
    intro n j hj
    have hcov : cov[fun ω => e 0 ω * W ((X 0 ω - x) / h n),
        fun ω => e (j : ℤ) ω * W ((X (j : ℤ) ω - x) / h n); μ] = Gl n j := by
      rw [covariance_eq_sub (hL2t (h n) 0) (hL2t (h n) (j : ℤ)), hmean0 (h n), zero_mul,
        sub_zero]
      simp only [hGldef]
      rfl
    rw [← hcov]
    refine (large_lag_covariance_bound hmeasX hmeasE hδ hWm (hh0 n) j hj
      (hLδ0 (h n)) (hLδt (h n) (j : ℤ))).trans ?_
    have hα0 : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
      Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
    have hKh0 : (0 : ℝ) ≤ K * h n := mul_nonneg hK0 (hh0 n).le
    have hsum2 : (1 / δ) + (1 / δ) = 2 / δ := by ring
    have hprod : (K * h n) ^ (2 / δ) = (K * h n) ^ (1 / δ) * (K * h n) ^ (1 / δ) := by
      rw [← hsum2, Real.rpow_add' hKh0 (by rw [hsum2]; positivity)]
    rw [hprod, ← mul_assoc]
    gcongr
    · exact hnormδ n 0
    · exact hnormδ n (j : ℤ)
  -- constants
  set E2 : ℝ := ∫ ω, e 0 ω ^ 2 ∂μ with hE2def
  set IW : ℝ := ∫ v, |W v| with hIWdef
  set SA : ℝ := ∑' t : ℕ, (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) with hSAdef
  have hE20 : (0 : ℝ) ≤ E2 := integral_nonneg fun ω => sq_nonneg _
  have hIW0 : (0 : ℝ) ≤ IW := integral_nonneg fun v => abs_nonneg _
  have hαnn : ∀ t : ℕ, (0 : ℝ) ≤ (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) :=
    fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
      (Real.rpow_nonneg (pairAlphaCoeff_nonneg X e t) _)
  have hSA0 : (0 : ℝ) ≤ SA := tsum_nonneg hαnn
  -- FY's split of the lag sum at `m_n`
  have hsplit : ∀ n : ℕ, 1 ≤ smallLagCut h n →
      ∑ j ∈ Finset.Ico 1 n, |Gl n j|
        ≤ (smallLagCut h n : ℝ) * (B * E2 * (IW * h n) ^ 2)
          + 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
    intro n hm1
    have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
    have h1 : ∑ j ∈ Finset.Ico 1 n, |Gl n j|
        ≤ ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gl n j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (le_max_left _ _)) fun j _ _ => abs_nonneg _
    have h2 : (∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gl n j|)
          + ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gl n j|
        = ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gl n j| :=
      Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)
    have h3 : ∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gl n j|
        ≤ (smallLagCut h n : ℝ) * (B * E2 * (IW * h n) ^ 2) := by
      have hcard := Finset.sum_le_card_nsmul (Finset.Ico 1 (smallLagCut h n + 1))
        (fun j => |Gl n j|) (B * E2 * (IW * h n) ^ 2)
        (fun j hj => hsmall n j (Finset.mem_Ico.1 hj).1)
      simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
    have h4 : ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gl n j|
        ≤ 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
      have hKh : (0 : ℝ) ≤ (K * h n) ^ (2 / δ) :=
        Real.rpow_nonneg (mul_nonneg hK0 (hh0 n).le) _
      have hmneg : (0 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) := Real.rpow_nonneg hmR.le _
      have hstep : ∀ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)),
          |Gl n j| ≤ 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
            ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
        have hj1' : 1 ≤ j := by omega
        refine (hlarge n j hj1').trans ?_
        have hmj : (smallLagCut h n : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
          Real.rpow_le_rpow hmR.le (by exact_mod_cast (by omega : smallLagCut h n ≤ j)) hlam0.le
        have hαβ : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
          Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
        have hid : (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam = 1 := by
          rw [← Real.rpow_add hmR]; simp
        have hge1 : (1 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam := by
          calc (1 : ℝ) = (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam := hid.symm
            _ ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam :=
                mul_le_mul_of_nonneg_left hmj hmneg
        calc 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (K * h n) ^ (2 / δ)
            = 8 * (K * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * 1) := by ring
          _ ≤ 8 * (K * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) *
                ((smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam)) := by
              gcongr
          _ = 8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
                ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmneg)
        (mul_nonneg (by norm_num) hKh)
      exact hα.sum_le_tsum _ fun i _ => hαnn i
    linarith
  -- the two sequences of FY's decomposition
  set A : ℕ → ℝ := fun n => ((n : ℝ) * h n)⁻¹ *
    ∫ ω, (∑ t ∈ Finset.range n,
      e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ with hAdef
  set Dg : ℕ → ℝ := fun n =>
    (h n)⁻¹ * ∫ ω, e 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ with hDdef
  have hbound : ∀ n : ℕ, 1 ≤ n →
      |A n - Dg n| ≤ 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gl n j| := by
    intro n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hhn : 0 < h n := hh0 n
    have hAn : A n = ((n : ℝ) * h n)⁻¹ *
        (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cl n s t) := by
      simp only [hAdef]; rw [hexp n]
    have hDn : Dg n = ((n : ℝ) * h n)⁻¹ * ((n : ℝ) * Gl n 0) := by
      simp only [hDdef]; rw [← hG0 n]; field_simp
    rw [hAn, hDn, ← mul_sub, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) * h n)⁻¹)]
    calc ((n : ℝ) * h n)⁻¹ *
          |(∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cl n s t) - (n : ℝ) * Gl n 0|
        ≤ ((n : ℝ) * h n)⁻¹ * (2 * (n : ℝ) * ∑ j ∈ Finset.Ico 1 n, |Gl n j|) :=
          mul_le_mul_of_nonneg_left
            (abs_double_sum_sub_diag_le n (Cl n) (Gl n) (hCG n) (hCG' n)) (by positivity)
      _ = 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gl n j| := by field_simp
  -- the lag remainder vanishes
  have hRto0 : Tendsto (fun n : ℕ => 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gl n j|)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ =>
        (2 * B * E2 * IW ^ 2) * ((smallLagCut h n : ℝ) * h n)
          + (16 * SA * K ^ (2 / δ)) *
            (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam)) atTop (𝓝 0) := by
      have t1 := (tendsto_smallLagCut_mul_bandwidth hh0 hh).const_mul (2 * B * E2 * IW ^ 2)
      have t2 := (tendsto_rpow_mul_abs_log_rpow hh0 hh (a := 2 / δ - 1 + lam)
        (by linarith) hlam0).const_mul (16 * SA * K ^ (2 / δ))
      simpa using t1.add t2
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards with n
      have hhn := hh0 n
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    · filter_upwards [(tendsto_abs_log_atTop hh0 hh).eventually_gt_atTop 0] with n hLn
      have hhn : 0 < h n := hh0 n
      have hposL : (0 : ℝ) < h n * |Real.log (h n)| := by positivity
      have hm1 : 1 ≤ smallLagCut h n := Nat.ceil_pos.2 (by positivity)
      have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
      have hmge : (h n * |Real.log (h n)|)⁻¹ ≤ (smallLagCut h n : ℝ) := Nat.le_ceil _
      have hmlam : (0 : ℝ) < (smallLagCut h n : ℝ) ^ lam := Real.rpow_pos_of_pos hmR _
      have hmb : (smallLagCut h n : ℝ) ^ (-lam) ≤ (h n * |Real.log (h n)|) ^ lam := by
        have hprod1 : (1 : ℝ) ≤ (h n * |Real.log (h n)|) * (smallLagCut h n : ℝ) := by
          have h0 := mul_le_mul_of_nonneg_left hmge hposL.le
          rwa [mul_inv_cancel₀ hposL.ne'] at h0
        have h5 : (1 : ℝ) ≤ ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam := by
          have h5' := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hprod1 hlam0.le
          rwa [Real.one_rpow] at h5'
        have h6 : ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam
            = (h n * |Real.log (h n)|) ^ lam * (smallLagCut h n : ℝ) ^ lam :=
          Real.mul_rpow hposL.le hmR.le
        rw [Real.rpow_neg hmR.le]
        refine le_of_mul_le_mul_right ?_ hmlam
        rw [inv_mul_cancel₀ hmlam.ne', ← h6]
        exact h5
      have hS := hsplit n hm1
      refine (mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * (h n)⁻¹)).trans ?_
      rw [mul_add]
      have e1 : 2 * (h n)⁻¹ * ((smallLagCut h n : ℝ) * (B * E2 * (IW * h n) ^ 2))
          = (2 * B * E2 * IW ^ 2) * ((smallLagCut h n : ℝ) * h n) := by
        field_simp
      have hKrw : (K * h n) ^ (2 / δ) = K ^ (2 / δ) * (h n) ^ (2 / δ) :=
        Real.mul_rpow hK0 hhn.le
      have hLrw : (h n * |Real.log (h n)|) ^ lam
          = (h n) ^ lam * |Real.log (h n)| ^ lam := Real.mul_rpow hhn.le (abs_nonneg _)
      have hpow : (h n) ^ (2 / δ - 1 + lam) = (h n) ^ (2 / δ) * (h n)⁻¹ * (h n) ^ lam := by
        rw [show (2 / δ - 1 + lam) = (2 / δ) + (-1) + lam by ring,
          Real.rpow_add hhn, Real.rpow_add hhn, Real.rpow_neg hhn.le, Real.rpow_one]
      have hKh : (0 : ℝ) ≤ (K * h n) ^ (2 / δ) := Real.rpow_nonneg (mul_nonneg hK0 hhn.le) _
      have e2 : 2 * (h n)⁻¹ * (8 * (K * h n) ^ (2 / δ) *
            ((smallLagCut h n : ℝ) ^ (-lam) * SA))
          ≤ (16 * SA * K ^ (2 / δ)) *
            ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
        calc 2 * (h n)⁻¹ *
              (8 * (K * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA))
            ≤ 2 * (h n)⁻¹ * (8 * (K * h n) ^ (2 / δ) *
                ((h n * |Real.log (h n)|) ^ lam * SA)) := by gcongr
          _ = (16 * SA * K ^ (2 / δ)) *
                ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
              rw [hKrw, hLrw, hpow]; ring
      linarith
  -- assemble: the diagonal (2.73) plus a vanishing lag remainder
  have hDlim : Tendsto Dg atTop (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) :=
    tendsto_localized_second_moment_debt (hmeasX 0) hσm hmp hp0 hpd hcv he2 hσc hpc hσpb
      hWm hWb hW2 hh0 hh
  have hdiff : Tendsto (fun n => A n - Dg n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hRto0
    filter_upwards [eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs] using hbound n hn
  simpa using hdiff.add hDlim

/-! #### Ledger (b)–(c): Bernstein blocks and truncation -/

/-- **Antitone weighted summability gains one power — PROVED.** If `a` is nonnegative and
antitone and `Σ t^λ a(t)^β < ∞` (`λ, β > 0`), then `t^{λ+1} a(t)^β → 0`. Summability alone
gives only `t^λ a(t)^β → 0`; the extra power comes from the dyadic block
`Σ_{j ∈ [T/2, T)} j^λ a(j)^β ≥ (T/2)^{λ+1} a(T)^β`, whose left side is a difference of two
partial sums and hence vanishes. This is the form of (C3) that FY's (2.78) actually
uses. -/
theorem tendsto_weighted_antitone_of_summable {a : ℕ → ℝ} {lam beta : ℝ}
    (hlam : 0 < lam) (hbeta : 0 < beta)
    (ha0 : ∀ t, 0 ≤ a t) (hanti : Antitone a)
    (hsum : Summable fun t : ℕ => (t : ℝ) ^ lam * a t ^ beta) :
    Tendsto (fun t : ℕ => (t : ℝ) ^ (lam + 1) * a t ^ beta) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun t => (t : ℝ) ^ lam * a t ^ beta with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t =>
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (Real.rpow_nonneg (ha0 t) _)
  have hS : Tendsto (fun k => ∑ j ∈ Finset.range k, f j) atTop (𝓝 (∑' j, f j)) :=
    hsum.hasSum.tendsto_sum_nat
  have hdiv : Tendsto (fun T : ℕ => T / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b, fun a ha => by omega⟩
  have hg : Tendsto (fun T : ℕ =>
      (∑ j ∈ Finset.range T, f j) - ∑ j ∈ Finset.range (T / 2), f j) atTop (𝓝 0) := by
    have := hS.sub (hS.comp hdiv)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun t =>
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (Real.rpow_nonneg (ha0 t) _)) ?_
    (by simpa using hg.const_mul ((4 : ℝ) ^ (lam + 1)))
  filter_upwards [eventually_ge_atTop 2] with T hT
  set m : ℕ := T / 2 with hm
  have hmT : m ≤ T := Nat.div_le_self _ _
  have hm1 : 1 ≤ m := Nat.one_le_div_iff (by norm_num) |>.2 hT
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  -- each term of the block dominates `m ^ lam * a T ^ beta`
  have hterm : ∀ j ∈ Finset.Ico m T, (m : ℝ) ^ lam * a T ^ beta ≤ f j := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    have h1 : (m : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
      Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hj.1) hlam.le
    have h2 : a T ^ beta ≤ a j ^ beta :=
      Real.rpow_le_rpow (ha0 T) (hanti hj.2.le) hbeta.le
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (ha0 T) _)
      (Real.rpow_nonneg (Nat.cast_nonneg j) _)
  have hcard : m ≤ (Finset.Ico m T).card := by
    rw [Nat.card_Ico]
    omega
  have hblock : (m : ℝ) ^ (lam + 1) * a T ^ beta
      ≤ ∑ j ∈ Finset.Ico m T, f j := by
    have hcast : (m : ℝ) ≤ ((Finset.Ico m T).card : ℝ) := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ (m : ℝ) ^ lam * a T ^ beta :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (Real.rpow_nonneg (ha0 T) _)
    calc (m : ℝ) ^ (lam + 1) * a T ^ beta
        = (m : ℝ) * ((m : ℝ) ^ lam * a T ^ beta) := by
          rw [Real.rpow_add hmpos, Real.rpow_one, mul_comm ((m:ℝ)^lam), mul_assoc]
      _ ≤ ((Finset.Ico m T).card : ℝ) * ((m : ℝ) ^ lam * a T ^ beta) :=
          mul_le_mul_of_nonneg_right hcast hnn
      _ = (Finset.Ico m T).card • ((m : ℝ) ^ lam * a T ^ beta) := (nsmul_eq_mul _ _).symm
      _ ≤ ∑ j ∈ Finset.Ico m T, f j := Finset.card_nsmul_le_sum _ _ _ hterm
  -- and `T ≤ 4 m`
  have hT4 : (T : ℝ) ≤ 4 * (m : ℝ) := by
    have : T ≤ 4 * m := by omega
    exact_mod_cast this
  have hTle : (T : ℝ) ^ (lam + 1) ≤ (4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1) := by
    calc (T : ℝ) ^ (lam + 1) ≤ (4 * (m : ℝ)) ^ (lam + 1) :=
          Real.rpow_le_rpow (Nat.cast_nonneg T) hT4 (by linarith)
      _ = (4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1) :=
          Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)
  calc (T : ℝ) ^ (lam + 1) * a T ^ beta
      ≤ ((4 : ℝ) ^ (lam + 1) * (m : ℝ) ^ (lam + 1)) * a T ^ beta :=
        mul_le_mul_of_nonneg_right hTle (Real.rpow_nonneg (ha0 T) _)
    _ = (4 : ℝ) ^ (lam + 1) * ((m : ℝ) ^ (lam + 1) * a T ^ beta) := by ring
    _ ≤ (4 : ℝ) ^ (lam + 1) * ∑ j ∈ Finset.Ico m T, f j :=
        mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (by norm_num) _)
    _ = (4 : ℝ) ^ (lam + 1) *
          ((∑ j ∈ Finset.range T, f j) - ∑ j ∈ Finset.range m, f j) := by
        rw [Finset.sum_Ico_eq_sub _ hmT]

/-- **FY (2.78) — PROVED.** The Volkonskii–Rozanov error of step (d) vanishes:
`k_n · α_pair(s_n) → 0`.

The exponent arithmetic, with `β = 1 − 2/δ` and `A_n = √(n/h_n) log n`: the block count
obeys `k_n ≤ n/l_n ≤ A_n` (that is what `l_n = [√(n h_n)/log n]` is for), while
`s_n = [A_n^{β/(λ+1)}]` gives `A_n ≤ s_n^{(λ+1)/β}`. Hence
`(k_n α(s_n))^β ≤ A_n^β α(s_n)^β ≤ s_n^{λ+1} α(s_n)^β → 0`
by `tendsto_weighted_antitone_of_summable` (`s_n → ∞`), and `k_n α(s_n) → 0` follows by
continuity of `y ↦ y^{1/β}` at `0`.

Note that (C5) (`hnh`) is **not needed**: (2.78) holds for any bandwidth sequence with
`h_n → 0`. (C5) is what makes `s_n = o(l_n)`, which is used elsewhere in step (b), not
here. -/
theorem tendsto_blockCount_mul_pairAlpha [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ =>
        (blockCount h δ lam n : ℝ) * pairAlphaCoeff X e μ (smallBlockLen h δ lam n))
      atTop (𝓝 0) := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by
    rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hlam1 : (0 : ℝ) < lam + 1 := by linarith
  -- `A n = √(n/h n) · log n`, the upper bound for the block count `k_n`
  have hA : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) / h n) * Real.log n) atTop atTop := by
    have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hq : Tendsto (fun n : ℕ => (n : ℝ) / h n) atTop atTop := by
      refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
      filter_upwards [hh.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn
      calc (n : ℝ) = (n : ℝ) / 1 := by ring
        _ ≤ (n : ℝ) / h n := div_le_div_of_nonneg_left (Nat.cast_nonneg n) (hh0 n) hn
    exact (Real.tendsto_sqrt_atTop.comp hq).atTop_mul_atTop₀ hlog
  -- the small block length tends to infinity
  have hs_top : Tendsto (fun n : ℕ => smallBlockLen h δ lam n) atTop atTop := by
    refine tendsto_nat_ceil_atTop.comp ?_
    exact (tendsto_rpow_atTop (div_pos hβ0 hlam1)).comp hA
  -- `k_n ≤ A n`
  have hk_le : ∀ᶠ n : ℕ in atTop, (blockCount h δ lam n : ℝ)
      ≤ Real.sqrt ((n : ℝ) / h n) * Real.log n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogpos : 0 < Real.log n := Real.log_pos hn1
    have hbig : 0 < Real.sqrt ((n : ℝ) * h n) / Real.log n :=
      div_pos (Real.sqrt_pos.2 (mul_pos hnpos (hh0 n))) hlogpos
    have hl : Real.sqrt ((n : ℝ) * h n) / Real.log n ≤ (bigBlockLen h n : ℝ) :=
      Nat.le_ceil _
    have hlpos : (0 : ℝ) < (bigBlockLen h n : ℝ) := lt_of_lt_of_le hbig hl
    have hkey : (n : ℝ) / (Real.sqrt ((n : ℝ) * h n) / Real.log n)
        = Real.sqrt ((n : ℝ) / h n) * Real.log n := by
      have h1 : Real.sqrt ((n : ℝ) * h n) = Real.sqrt n * Real.sqrt (h n) :=
        Real.sqrt_mul hnpos.le _
      have h2 : Real.sqrt ((n : ℝ) / h n) = Real.sqrt n / Real.sqrt (h n) :=
        Real.sqrt_div hnpos.le _
      have h3 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
        Real.mul_self_sqrt hnpos.le
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnpos
      have hsh : (0 : ℝ) < Real.sqrt (h n) := Real.sqrt_pos.2 (hh0 n)
      rw [h1, h2]
      field_simp
      nlinarith [h3, hsn, hsh, hlogpos]
    calc (blockCount h δ lam n : ℝ)
        ≤ (n : ℝ) / ((bigBlockLen h n + smallBlockLen h δ lam n : ℕ) : ℝ) :=
          Nat.cast_div_le
      _ ≤ (n : ℝ) / (bigBlockLen h n : ℝ) := by
          rw [Nat.cast_add]
          exact div_le_div_of_nonneg_left hnpos.le hlpos
            (le_add_of_nonneg_right (Nat.cast_nonneg _))
      _ ≤ (n : ℝ) / (Real.sqrt ((n : ℝ) * h n) / Real.log n) :=
          div_le_div_of_nonneg_left hnpos.le hbig hl
      _ = Real.sqrt ((n : ℝ) / h n) * Real.log n := hkey
  -- the main pointwise bound
  have hmain : ∀ᶠ n : ℕ in atTop,
      (blockCount h δ lam n : ℝ) * pairAlphaCoeff X e μ (smallBlockLen h δ lam n)
        ≤ (((smallBlockLen h δ lam n : ℝ)) ^ (lam + 1) *
            pairAlphaCoeff X e μ (smallBlockLen h δ lam n) ^ (1 - 2 / δ)) ^ (1 / (1 - 2 / δ)) := by
    filter_upwards [hk_le, hA.eventually_gt_atTop 0] with n hk hA0
    have ha0 : 0 ≤ pairAlphaCoeff X e μ (smallBlockLen h δ lam n) :=
      pairAlphaCoeff_nonneg X e _
    have hspos : (0 : ℝ) ≤ (smallBlockLen h δ lam n : ℝ) := Nat.cast_nonneg _
    -- `A n ≤ s_n ^ ((lam+1)/β)`
    have hsge : (Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1))
        ≤ (smallBlockLen h δ lam n : ℝ) := Nat.le_ceil _
    have hs1 : Real.sqrt ((n : ℝ) / h n) * Real.log n
        ≤ (smallBlockLen h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) := by
      have hd2 : δ - 2 ≠ 0 := (by linarith : (0:ℝ) < δ - 2).ne'
      have hpq : ((1 - 2 / δ) / (lam + 1)) * ((lam + 1) / (1 - 2 / δ)) = 1 := by
        field_simp [hd2, hlam1.ne']
      have hid : ((Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1)))
            ^ ((lam + 1) / (1 - 2 / δ)) = Real.sqrt ((n : ℝ) / h n) * Real.log n := by
        rw [← Real.rpow_mul hA0.le, hpq, Real.rpow_one]
      calc Real.sqrt ((n : ℝ) / h n) * Real.log n
          = ((Real.sqrt ((n : ℝ) / h n) * Real.log n) ^ ((1 - 2 / δ) / (lam + 1)))
              ^ ((lam + 1) / (1 - 2 / δ)) := hid.symm
        _ ≤ (smallBlockLen h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hA0.le _) hsge (div_pos hlam1 hβ0).le
    -- the right-hand side splits
    have hrhs : (((smallBlockLen h δ lam n : ℝ)) ^ (lam + 1) *
          pairAlphaCoeff X e μ (smallBlockLen h δ lam n) ^ (1 - 2 / δ)) ^ (1 / (1 - 2 / δ))
        = (smallBlockLen h δ lam n : ℝ) ^ ((lam + 1) / (1 - 2 / δ)) *
            pairAlphaCoeff X e μ (smallBlockLen h δ lam n) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hspos _) (Real.rpow_nonneg ha0 _),
        ← Real.rpow_mul hspos, ← Real.rpow_mul ha0, mul_one_div, mul_one_div,
        div_self hβ0.ne', Real.rpow_one]
    rw [hrhs]
    exact mul_le_mul (hk.trans hs1) le_rfl ha0 (Real.rpow_nonneg hspos _)
  refine squeeze_zero' ?_ hmain ?_
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _) (pairAlphaCoeff_nonneg X e _)
  · have hcomp := (tendsto_weighted_antitone_of_summable (a := pairAlphaCoeff X e μ) hlam0 hβ0
      (fun t => pairAlphaCoeff_nonneg X e t) (pairAlphaCoeff_antitone X e) hα).comp hs_top
    have hcont : Tendsto (fun y : ℝ => y ^ (1 / (1 - 2 / δ))) (𝓝 0) (𝓝 0) := by
      have hpos : (0 : ℝ) < 1 / (1 - 2 / δ) := one_div_pos.2 hβ0
      have hz : (0 : ℝ) ^ (1 / (1 - 2 / δ)) = 0 := Real.zero_rpow hpos.ne'
      have ht := (Real.continuousAt_rpow_const (0 : ℝ) (1 / (1 - 2 / δ))
        (Or.inr hpos.le)).tendsto
      rw [hz] at ht
      exact ht
    exact hcont.comp hcomp

/-- `(log n)^β / n^α → 0` for `α, β > 0`. -/
theorem tendsto_log_rpow_div_rpow_atTop {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => Real.log n ^ β / (n : ℝ) ^ α) atTop (𝓝 0) := by
  have hh0 : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n => by positivity
  have hh : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hbase := tendsto_rpow_mul_abs_log_rpow hh0 hh (a := α) (lam := β) hα hβ
  have hkey : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) ^ β / ((n : ℝ) + 1) ^ α)
      atTop (𝓝 0) := by
    refine hbase.congr fun n => ?_
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : Real.log (((n : ℝ) + 1)⁻¹) = -Real.log ((n : ℝ) + 1) := Real.log_inv _
    rw [Real.inv_rpow h1.le, h2, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by linarith)), div_eq_mul_inv, mul_comm]
  refine (tendsto_add_atTop_iff_nat
    (f := fun n : ℕ => Real.log n ^ β / (n : ℝ) ^ α) 1).mp ?_
  refine hkey.congr fun n => ?_
  norm_num

/-- The block numerology `k_n s_n / n → 0`. -/
theorem tendsto_blockCount_mul_smallBlockLen_div {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam) :
    Tendsto (fun n : ℕ =>
        (blockCount h δ lam n : ℝ) * (smallBlockLen h δ lam n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hβ1 : (1 - 2 / δ) < 1 := by
    have : (0 : ℝ) < 2 / δ := by positivity
    linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  set θ : ℝ := (1 - 2 / δ) / (lam + 1) with hθdef
  have hL1 : (0 : ℝ) < lam + 1 := by linarith
  have hθ0 : 0 < θ := div_pos hβ0 hL1
  have hθ1 : θ < 1 / 2 := by
    rw [hθdef, div_lt_iff₀ hL1]
    linarith
  -- the majorant
  set maj : ℕ → ℝ := fun n =>
    Real.log n ^ (1 + θ) / (n : ℝ) ^ ((1 - 2 * θ) / 3)
      + Real.log n ^ (1 : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 3) with hmajdef
  have hmaj0 : Tendsto maj atTop (𝓝 0) := by
    have t1 := tendsto_log_rpow_div_rpow_atTop (α := (1 - 2 * θ) / 3) (β := 1 + θ)
      (by linarith) (by linarith)
    have t2 := tendsto_log_rpow_div_rpow_atTop (α := (1 : ℝ) / 3) (β := (1 : ℝ))
      (by norm_num) (by norm_num)
    simpa [hmajdef] using t1.add t2
  refine squeeze_zero' ?_ ?_ hmaj0
  · filter_upwards with n
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  filter_upwards [eventually_ge_atTop 2, hnh.eventually_ge_atTop 1] with n hn2 hPH3
  -- abbreviations
  set P : ℝ := (n : ℝ) with hPdef
  set H : ℝ := h n with hHdef
  set Λ : ℝ := Real.log n with hΛdef
  have hP1 : (1 : ℝ) ≤ P := by
    rw [hPdef]; exact_mod_cast Nat.one_le_of_lt hn2
  have hP0 : (0 : ℝ) < P := by linarith
  have hH0 : (0 : ℝ) < H := hh0 n
  have hΛ0 : (0 : ℝ) < Λ := Real.log_pos (by exact_mod_cast hn2)
  have hPH3' : (0 : ℝ) < P * H ^ 3 := by positivity
  -- the two elementary rpow factorizations
  have hlogP3 : Real.log (P * H ^ 3) = Real.log P + 3 * Real.log H := by
    rw [Real.log_mul hP0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hlogPH : Real.log (P * H) = Real.log P + Real.log H := Real.log_mul hP0.ne' hH0.ne'
  have hlogPdH : Real.log (P / H) = Real.log P - Real.log H := Real.log_div hP0.ne' hH0.ne'
  have hone3 : (1 : ℝ) ≤ (P * H ^ 3) ^ ((1 + θ) / 6) := by
    have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hPH3 (by linarith : (0:ℝ) ≤ (1 + θ) / 6)
    rwa [Real.one_rpow] at this
  have hone6 : (1 : ℝ) ≤ (P * H ^ 3) ^ ((1 : ℝ) / 6) := by
    have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hPH3 (by norm_num : (0:ℝ) ≤ (1:ℝ) / 6)
    rwa [Real.one_rpow] at this
  have hfact1 : (Real.sqrt (P / H)) ^ θ * P ^ ((1 - 2 * θ) / 3) * (P * H ^ 3) ^ ((1 + θ) / 6)
      = Real.sqrt (P * H) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (div_pos hP0 hH0).le,
      Real.rpow_def_of_pos (div_pos hP0 hH0), Real.rpow_def_of_pos hP0,
      Real.rpow_def_of_pos hPH3', Real.rpow_def_of_pos (mul_pos hP0 hH0),
      ← Real.exp_add, ← Real.exp_add, hlogPdH, hlogP3, hlogPH]
    congr 1
    ring
  have hfact2 : P ^ ((1 : ℝ) / 3) * (P * H ^ 3) ^ ((1 : ℝ) / 6) = Real.sqrt (P * H) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hP0, Real.rpow_def_of_pos hPH3',
      Real.rpow_def_of_pos (mul_pos hP0 hH0), ← Real.exp_add, hlogP3, hlogPH]
    congr 1
    ring
  have hcore1 : (Real.sqrt (P / H)) ^ θ * P ^ ((1 - 2 * θ) / 3) ≤ Real.sqrt (P * H) := by
    rw [← hfact1]
    exact le_mul_of_one_le_right (by positivity) hone3
  have hcore2 : P ^ ((1 : ℝ) / 3) ≤ Real.sqrt (P * H) := by
    rw [← hfact2]
    exact le_mul_of_one_le_right (by positivity) hone6
  -- the block lengths
  set A : ℝ := Real.sqrt (P / H) * Λ with hAdef
  have hA0 : 0 < A := mul_pos (Real.sqrt_pos.2 (div_pos hP0 hH0)) hΛ0
  set l : ℕ := bigBlockLen h n with hldef
  set s : ℕ := smallBlockLen h δ lam n with hsdef
  have hlge : Real.sqrt (P * H) / Λ ≤ (l : ℝ) := by
    rw [hldef]
    exact Nat.le_ceil _
  have hlpos : (0 : ℝ) < (l : ℝ) :=
    lt_of_lt_of_le (by positivity) hlge
  have hsle : (s : ℝ) ≤ A ^ θ + 1 := by
    have hEq : (s : ℝ) = (⌈A ^ θ⌉₊ : ℝ) := by
      rw [hsdef]; simp only [smallBlockLen, hAdef, hθdef, hPdef, hHdef, hΛdef]
    rw [hEq]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hA0.le θ))
  have hs0 : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
  -- step 1: `k s / n ≤ s / l`
  have hkle : (blockCount h δ lam n : ℝ) ≤ P / ((l : ℝ) + (s : ℝ)) := by
    rw [hPdef]
    have := Nat.cast_div_le (α := ℝ) (m := n) (n := l + s)
    simpa [blockCount, hldef, hsdef, Nat.cast_add] using this
  have hstep1 : (blockCount h δ lam n : ℝ) * (s : ℝ) / P ≤ (s : ℝ) / (l : ℝ) := by
    calc (blockCount h δ lam n : ℝ) * (s : ℝ) / P
        ≤ (P / ((l : ℝ) + (s : ℝ))) * (s : ℝ) / P := by gcongr
      _ = (s : ℝ) / ((l : ℝ) + (s : ℝ)) := by
          field_simp
      _ ≤ (s : ℝ) / (l : ℝ) :=
          div_le_div_of_nonneg_left hs0 hlpos (le_add_of_nonneg_right hs0)
  -- step 2: `s / l ≤ A^θ Λ / √(PH) + Λ / √(PH)`
  have hsq0 : (0 : ℝ) < Real.sqrt (P * H) := Real.sqrt_pos.2 (mul_pos hP0 hH0)
  have hstep2 : (s : ℝ) / (l : ℝ) ≤ A ^ θ * Λ / Real.sqrt (P * H) + Λ / Real.sqrt (P * H) := by
    calc (s : ℝ) / (l : ℝ) ≤ (A ^ θ + 1) / (l : ℝ) := by gcongr
      _ ≤ (A ^ θ + 1) / (Real.sqrt (P * H) / Λ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlge
      _ = A ^ θ * Λ / Real.sqrt (P * H) + Λ / Real.sqrt (P * H) := by
          field_simp
  -- step 3: the two rpow bounds
  have hAθ : A ^ θ = (Real.sqrt (P / H)) ^ θ * Λ ^ θ :=
    Real.mul_rpow (Real.sqrt_nonneg _) hΛ0.le
  have hΛsum : Λ ^ θ * Λ = Λ ^ (1 + θ) := by
    rw [add_comm, Real.rpow_add hΛ0, Real.rpow_one]
  have hb1 : A ^ θ * Λ / Real.sqrt (P * H) ≤ Λ ^ (1 + θ) / P ^ ((1 - 2 * θ) / 3) := by
    rw [div_le_div_iff₀ hsq0 (by positivity)]
    calc A ^ θ * Λ * P ^ ((1 - 2 * θ) / 3)
        = ((Real.sqrt (P / H)) ^ θ * P ^ ((1 - 2 * θ) / 3)) * Λ ^ (1 + θ) := by
          rw [hAθ, ← hΛsum]; ring
      _ ≤ Real.sqrt (P * H) * Λ ^ (1 + θ) := by
          gcongr
      _ = Λ ^ (1 + θ) * Real.sqrt (P * H) := by ring
  have hb2 : Λ / Real.sqrt (P * H) ≤ Λ ^ (1 : ℝ) / P ^ ((1 : ℝ) / 3) := by
    rw [Real.rpow_one]
    exact div_le_div_of_nonneg_left hΛ0.le (by positivity) hcore2
  calc (blockCount h δ lam n : ℝ) * (smallBlockLen h δ lam n : ℝ) / (n : ℝ)
      = (blockCount h δ lam n : ℝ) * (s : ℝ) / P := by rw [hsdef, hPdef]
    _ ≤ (s : ℝ) / (l : ℝ) := hstep1
    _ ≤ A ^ θ * Λ / Real.sqrt (P * H) + Λ / Real.sqrt (P * H) := hstep2
    _ ≤ Λ ^ (1 + θ) / P ^ ((1 - 2 * θ) / 3) + Λ ^ (1 : ℝ) / P ^ ((1 : ℝ) / 3) := by
        gcongr
    _ = maj n := by rw [hmajdef]

/-- Davydov for a fixed measurable function of the pair `(X_t, e_t)`. -/
theorem large_lag_covariance_bound' [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    {δ : ℝ} (hδ : 2 < δ) {F : ℝ × ℝ → ℝ} (hFm : Measurable F) (j : ℕ) (hj : 1 ≤ j)
    (hL0 : MemLp (fun ω => F (X 0 ω, e 0 ω)) (ENNReal.ofReal δ) μ)
    (hLj : MemLp (fun ω => F (X (j : ℤ) ω, e (j : ℤ) ω)) (ENNReal.ofReal δ) μ) :
    |cov[fun ω => F (X 0 ω, e 0 ω), fun ω => F (X (j : ℤ) ω, e (j : ℤ) ω); μ]|
      ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ)
        * (eLpNorm (fun ω => F (X 0 ω, e 0 ω)) (ENNReal.ofReal δ) μ).toReal
        * (eLpNorm (fun ω => F (X (j : ℤ) ω, e (j : ℤ) ω)) (ENNReal.ofReal δ) μ).toReal := by
  have hpq : 1 / δ + 1 / δ < 1 := by
    have h2d : 1 / δ + 1 / δ = 2 / δ := by ring
    rw [h2d, div_lt_one (by linarith : (0 : ℝ) < δ)]; linarith
  have hf : Measurable[⨆ s ∈ Set.Iic (0 : ℤ), MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance] (fun ω => F (X 0 ω, e 0 ω)) :=
    hFm.comp ((measurable_X_pairSigma (X := X) (e := e)
        (Set.mem_Iic.2 (le_refl (0 : ℤ)))).prodMk
      (measurable_e_pairSigma (X := X) (e := e) (Set.mem_Iic.2 (le_refl (0 : ℤ)))))
  have hg : Measurable[⨆ s ∈ Set.Ici (j : ℤ), MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance] (fun ω => F (X (j : ℤ) ω, e (j : ℤ) ω)) :=
    hFm.comp ((measurable_X_pairSigma (X := X) (e := e)
        (Set.mem_Ici.2 (le_refl (j : ℤ)))).prodMk
      (measurable_e_pairSigma (X := X) (e := e) (Set.mem_Ici.2 (le_refl (j : ℤ)))))
  have hdav := abs_covariance_le_davydov (pairSigma_le hmeasX hmeasE (Set.Iic (0 : ℤ)))
    (pairSigma_le hmeasX hmeasE (Set.Ici (j : ℤ))) hf hg (p := δ) (q := δ)
    (by linarith) (by linarith) hpq hL0 hLj
  have hexp : (1 : ℝ) - 1 / δ - 1 / δ = 1 - 2 / δ := by ring
  rw [hexp] at hdav
  exact hdav

set_option maxHeartbeats 1000000 in
/-- **The small-block variance estimate, over an arbitrary index family.** -/
theorem tendsto_truncIndex_variance [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hC2gen : ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L)
    (I : ℕ → Finset ℕ) (hIsub : ∀ n, I n ⊆ Finset.range n)
    (hIcard : Tendsto (fun n : ℕ => ((I n).card : ℝ) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  obtain ⟨mm, hmmM, hmmB, hmrep⟩ := exists_truncErr_repr hmeasX hmeasE hstat hL
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (hp0 0) (hpb 0)
  have hrp : Measurable (fun y : ℝ => y ^ δ) := (Real.continuous_rpow_const hδ0.le).measurable
  -- `|W|^δ` is integrable
  have hWam : Measurable (fun v => |W v| ^ δ) := hrp.comp hWm.abs
  have hWδ : Integrable (fun v => |W v| ^ δ) MeasureTheory.volume := by
    refine Integrable.mono (hW2.const_mul (CW ^ (δ - 2))) hWam.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    have hsplit : |W v| ^ δ = |W v| ^ (δ - 2) * |W v| ^ (2 : ℝ) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by intro hcon; linarith),
        show δ - 2 + 2 = δ from by ring]
    have h2 : |W v| ^ (2 : ℝ) = W v ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    have hle : |W v| ^ (δ - 2) ≤ CW ^ (δ - 2) :=
      Real.rpow_le_rpow (abs_nonneg _) (hWb v) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hsplit, h2,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ (δ - 2) * W v ^ 2)]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  -- the pair function and the truncated array
  set F : ℕ → ℝ × ℝ → ℝ := fun n z => (clampAt L z.2 - mm z.1) * W ((z.1 - x) / h n) with hFdef
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    exact (((measurable_clampAt L).comp measurable_snd).sub (hmmM.comp measurable_fst)).mul
      (hWm.comp ((measurable_fst.sub measurable_const).div measurable_const))
  have hbase : ∀ z : ℝ × ℝ, |clampAt L z.2 - mm z.1| ≤ 2 * L := by
    intro z
    have ha := abs_le.1 (abs_clampAt_le hL.le z.2)
    have hb := abs_le.1 (hmmB z.1)
    rw [abs_le]; constructor <;> linarith
  have hFb : ∀ (n : ℕ) (z : ℝ × ℝ), |F n z| ≤ 2 * L * CW := by
    intro n z
    have h1 := hbase z
    have h2 := hWb ((z.1 - x) / h n)
    simp only [hFdef, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [hL.le])
  set Z : ℕ → ℤ → Ω → ℝ := fun n t ω => F n (X t ω, e t ω) with hZdef
  have hZm : ∀ (n : ℕ) (t : ℤ), Measurable (Z n t) := fun n t =>
    (hFm n).comp ((hmeasX t).prodMk (hmeasE t))
  have hZb : ∀ (n : ℕ) (t : ℤ) (ω : Ω), |Z n t ω| ≤ 2 * L * CW := fun n t ω => hFb n _
  have hZmem : ∀ (n : ℕ) (t : ℤ) (q : ℝ≥0∞), MemLp (Z n t) q μ := fun n t q =>
    MemLp.of_bound (hZm n t).aestronglyMeasurable (2 * L * CW)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb n t ω)
  have hint : ∀ (n : ℕ) (s t : ℤ), Integrable (fun ω => Z n s ω * Z n t ω) μ :=
    fun n s t => (hZmem n s 2).integrable_mul (hZmem n t 2)
  have hZrep : ∀ (n : ℕ) (t : ℤ),
      (fun ω => truncErr X e μ L t ω * W ((X t ω - x) / h n)) =ᵐ[μ] Z n t := by
    intro n t
    filter_upwards [hmrep t] with ω hω
    simp only [hZdef, hFdef, hω]
  -- each summand is centred
  have hclampint : ∀ t : ℤ, Integrable (fun ω => clampAt L (e t ω)) μ := by
    intro t
    refine (integrable_const L).mono'
      (((measurable_clampAt L).comp (hmeasE t)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAt_le hL.le _
  have hcond : ∀ t : ℤ,
      μ[fun ω => clampAt L (e t ω) | MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => mm (X t ω) := by
    intro t
    filter_upwards [hmrep t] with ω hω
    simp only [truncErr] at hω
    linarith
  have hmean0 : ∀ (n : ℕ) (t : ℤ), ∫ ω, Z n t ω ∂μ = 0 := by
    intro n t
    have hz := integral_bdd_comp_mul_eq_of_condExp (μ := μ) (hmeasX t) (hclampint t) (hcond t)
      (fun v => W ((v - x) / h n)) (by fun_prop) (C := CW) (fun v => hWb _)
    have hi1 : Integrable (fun ω => W ((X t ω - x) / h n) * clampAt L (e t ω)) μ :=
      (hclampint t).bdd_mul
        ((hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWb _)
    have hi2 : Integrable (fun ω => W ((X t ω - x) / h n) * mm (X t ω)) μ := by
      refine (integrable_const (CW * L)).mono'
        (((hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)).mul
          (hmmM.comp (hmeasX t))).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hWb _) (hmmB _) (abs_nonneg _) hCW0
    have hsplit : ∫ ω, Z n t ω ∂μ
        = ∫ ω, W ((X t ω - x) / h n) * clampAt L (e t ω) ∂μ
          - ∫ ω, W ((X t ω - x) / h n) * mm (X t ω) ∂μ := by
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [hZdef, hFdef]; ring)
    rw [hsplit, hz, sub_self]
  -- the lag covariance array
  set Gz : ℕ → ℕ → ℝ := fun n d => ∫ ω, Z n 0 ω * Z n (d : ℤ) ω ∂μ with hGzdef
  set Cz : ℕ → ℕ → ℕ → ℝ := fun n s t => ∫ ω, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω ∂μ
    with hCzdef
  have hCG : ∀ n s d : ℕ, Cz n s (s + d) = Gz n d := by
    intro n s d
    have hidx : ((s + d : ℕ) : ℤ) + 1 = ((s : ℤ) + 1) + (d : ℤ) := by push_cast; ring
    have htr := integral_comp_pair2_eq hmeasX hmeasE hstat ((s : ℤ) + 1) d
      (G := fun z : (ℝ × ℝ) × (ℝ × ℝ) => F n z.1 * F n z.2)
      (((hFm n).comp measurable_fst).mul ((hFm n).comp measurable_snd))
    simp only [hCzdef, hGzdef, hZdef, hidx]
    exact htr
  have hCG' : ∀ n s d : ℕ, Cz n (s + d) s = Gz n d := by
    intro n s d
    have hsym : Cz n (s + d) s = Cz n s (s + d) := by
      simp only [hCzdef]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsym, hCG]
  -- the sum of squares expands
  have hexp : ∀ n : ℕ, ∫ ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ
      = ∑ s ∈ I n, ∑ t ∈ I n, Cz n s t := by
    intro n
    have hsq : ∀ ω : Ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2
        = ∑ s ∈ I n, ∑ t ∈ I n, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp only [hsq, hCzdef]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hint n _ _))]
    exact Finset.sum_congr rfl fun s _ =>
      integral_finset_sum _ (fun t _ => hint n _ _)
  -- diagonal
  have hdiag : ∀ n : ℕ, |Gz n 0| ≤ (4 * L ^ 2) * ((Cp * ∫ v, W v ^ 2) * h n) := by
    intro n
    have hWsqm : Measurable (fun ω => W ((X 0 ω - x) / h n) ^ 2) :=
      (hWm.comp (((hmeasX 0).sub measurable_const).div measurable_const)).pow_const 2
    have hGeq : Gz n 0 = ∫ ω, (Z n 0 ω) ^ 2 ∂μ := by
      simp only [hGzdef, Nat.cast_zero]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hnn : 0 ≤ Gz n 0 := by
      rw [hGeq]; exact integral_nonneg fun ω => sq_nonneg _
    have hi2 : Integrable (fun ω => 4 * L ^ 2 * W ((X 0 ω - x) / h n) ^ 2) μ := by
      refine (integrable_const (4 * L ^ 2 * CW ^ 2)).mono'
        (hWsqm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hb := hWb ((X 0 ω - x) / h n)
      have habs := abs_nonneg (W ((X 0 ω - x) / h n))
      have hsq : W ((X 0 ω - x) / h n) ^ 2 ≤ CW ^ 2 := by
        nlinarith [sq_abs (W ((X 0 ω - x) / h n))]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have hstep : ∫ ω, (Z n 0 ω) ^ 2 ∂μ ≤ (4 * L ^ 2) * ∫ ω, W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono (hZmem n 0 2).integrable_sq hi2 fun ω => ?_
      have hb := hbase (X 0 ω, e 0 ω)
      have hsq : (clampAt L (e 0 ω) - mm (X 0 ω)) ^ 2 ≤ 4 * L ^ 2 := by
        nlinarith [abs_nonneg (clampAt L (e 0 ω) - mm (X 0 ω)),
          sq_abs (clampAt L (e 0 ω) - mm (X 0 ω)), hL.le]
      simp only [hZdef, hFdef, mul_pow]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hloc := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => W v ^ 2) (hWm.pow_const 2) (fun v => sq_nonneg _) hW2 (x := x) (hh0 n)
    rw [abs_of_nonneg hnn, hGeq]
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_left hloc (by positivity)
  -- small lags
  have hIW0 : (0 : ℝ) ≤ ∫ v, |W v| := integral_nonneg fun v => abs_nonneg _
  have hsmall : ∀ (n j : ℕ), 1 ≤ j →
      |Gz n j| ≤ (4 * L ^ 2) * (B * ((∫ v, |W v|) * h n) ^ 2) := by
    intro n j hj
    have hjz : ((j : ℤ)) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    have hgm : Measurable (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|) := by
      fun_prop
    have hg0 : ∀ z : ℝ × ℝ, 0 ≤ |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)| :=
      fun z => by positivity
    have hgXm : Measurable (fun ω => |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) :=
      hgm.comp ((hmeasX 0).prodMk (hmeasX (j : ℤ)))
    have hgi : Integrable
        (fun ω => 4 * L ^ 2 * (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|)) μ := by
      refine (integrable_const (4 * L ^ 2 * (CW * CW))).mono'
        (hgXm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hWb ((X 0 ω - x) / h n)
      have h2 := hWb ((X (j : ℤ) ω - x) / h n)
      have h3 : |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ≤ CW * CW :=
        mul_le_mul h1 h2 (abs_nonneg _) hCW0
      nlinarith [sq_nonneg L]
    have hA : |Gz n j| ≤ (4 * L ^ 2) *
        ∫ ω, |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ∂μ := by
      have h0 := norm_integral_le_integral_norm (μ := μ) (fun ω => Z n 0 ω * Z n (j : ℤ) ω)
      simp only [Real.norm_eq_abs] at h0
      refine (le_trans h0 ?_)
      rw [← integral_const_mul]
      refine integral_mono (hint n 0 (j : ℤ)).abs hgi fun ω => ?_
      have hb0 := hbase (X 0 ω, e 0 ω)
      have hbj := hbase (X (j : ℤ) ω, e (j : ℤ) ω)
      simp only [hZdef, hFdef, abs_mul]
      have hL2 : (0 : ℝ) ≤ 2 * L := by linarith
      calc |clampAt L (e 0 ω) - mm (X 0 ω)| * |W ((X 0 ω - x) / h n)| *
              (|clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω)| * |W ((X (j : ℤ) ω - x) / h n)|)
          = (|clampAt L (e 0 ω) - mm (X 0 ω)| *
              |clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω)|) *
              (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by ring
        _ ≤ (4 * L ^ 2) * (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [abs_nonneg (clampAt L (e 0 ω) - mm (X 0 ω)),
              abs_nonneg (clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω))]
    have hC2 := hC2gen (j : ℤ) hjz (fun _ => (1 : ℝ)) measurable_const _ hgm hg0
    have hone : ∫ ω, |(fun _ : ℝ × ℝ => (1 : ℝ)) (e 0 ω, e (j : ℤ) ω)| ∂μ = 1 := by
      simp
    have hlhs : ∫ ω, |(fun _ : ℝ × ℝ => (1 : ℝ)) (e 0 ω, e (j : ℤ) ω)| *
          (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|)
            (X 0 ω, X (j : ℤ) ω) ∂μ
        = ∫ ω, |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ∂μ := by
      simp
    rw [hone, hlhs, mul_one] at hC2
    have hprod : ∫ z : ℝ × ℝ, |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|
          ∂(MeasureTheory.volume.prod MeasureTheory.volume)
        = (∫ v, |W ((v - x) / h n)|) * ∫ w, |W ((w - x) / h n)| :=
      integral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (f := fun v => |W ((v - x) / h n)|) (g := fun w => |W ((w - x) / h n)|)
    have honeW : ∫ v, |W ((v - x) / h n)| = h n * ∫ v, |W v| := by
      have := integral_dilate_translate (fun u => |W u|) (fun _ => (1 : ℝ)) x (hh0 n)
      simp only [mul_one] at this
      rw [this, ← mul_assoc, mul_inv_cancel₀ (hh0 n).ne', one_mul]
    rw [hprod, honeW] at hC2
    refine hA.trans ?_
    refine mul_le_mul_of_nonneg_left (hC2.trans (le_of_eq ?_)) (by positivity)
    ring
  -- the localized δ-th moment of the truncated array
  have hIWδ0 : (0 : ℝ) ≤ ∫ v, |W v| ^ δ :=
    integral_nonneg fun v => Real.rpow_nonneg (abs_nonneg _) _
  have hKzbd : ∀ n : ℕ,
      ∫ ω, |Z n 0 ω| ^ δ ∂μ ≤ ((2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ)) * h n := by
    intro n
    have hGm : Measurable (fun v => |W ((v - x) / h n)| ^ δ) :=
      hrp.comp ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).abs)
    have hGXm : Measurable (fun ω => |W ((X 0 ω - x) / h n)| ^ δ) := hGm.comp (hmeasX 0)
    have hdom : ∀ ω, |Z n 0 ω| ^ δ ≤ (2 * L) ^ δ * |W ((X 0 ω - x) / h n)| ^ δ := by
      intro ω
      simp only [hZdef, hFdef, abs_mul]
      rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      have h1 : |clampAt L (e 0 ω) - mm (X 0 ω)| ^ δ ≤ (2 * L) ^ δ :=
        Real.rpow_le_rpow (abs_nonneg _) (hbase (X 0 ω, e 0 ω)) hδ0.le
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg _) _)
    have hi1 : Integrable (fun ω => |Z n 0 ω| ^ δ) μ := by
      refine (integrable_const ((2 * L * CW) ^ δ)).mono'
        ((hrp.comp (hZm n 0).abs)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hZb n 0 ω) hδ0.le
    have hi2 : Integrable (fun ω => (2 * L) ^ δ * |W ((X 0 ω - x) / h n)| ^ δ) μ := by
      refine (integrable_const ((2 * L) ^ δ * CW ^ δ)).mono'
        (hGXm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le) (Real.rpow_nonneg (by linarith) _)
    have hstep : ∫ ω, |Z n 0 ω| ^ δ ∂μ
        ≤ (2 * L) ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono hi1 hi2 hdom
    have hloc := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => |W v| ^ δ) hWam (fun v => Real.rpow_nonneg (abs_nonneg _) _) hWδ
      (x := x) (hh0 n)
    refine hstep.trans ?_
    calc (2 * L) ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ
        ≤ (2 * L) ^ δ * ((Cp * ∫ v, |W v| ^ δ) * h n) :=
          mul_le_mul_of_nonneg_left hloc (Real.rpow_nonneg (by linarith) _)
      _ = ((2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ)) * h n := by ring
  -- the δ-norms of the truncated array, and Davydov
  set Kz : ℝ := (2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ) with hKzdef
  have hKz0 : (0 : ℝ) ≤ Kz :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (mul_nonneg hCp0 hIWδ0)
  have hnormδ : ∀ (n : ℕ) (t : ℤ),
      (eLpNorm (Z n t) (ENNReal.ofReal δ) μ).toReal ≤ (Kz * h n) ^ (1 / δ) := by
    intro n t
    have hEq : eLpNorm (Z n t) (ENNReal.ofReal δ) μ = eLpNorm (Z n 0) (ENNReal.ofReal δ) μ :=
      eLpNorm_comp_pair_eq hmeasX hmeasE hstat t (hFm n) _
    rw [hEq]
    have hp1 : (ENNReal.ofReal δ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0
    have hform := (hZmem n 0 (ENNReal.ofReal δ)).eLpNorm_eq_integral_rpow_norm hp1
      ENNReal.ofReal_ne_top
    have hb0 : (0 : ℝ) ≤ ∫ a, ‖Z n 0 a‖ ^ δ ∂μ :=
      integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
    rw [hform]
    simp only [ENNReal.toReal_ofReal hδ0.le]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hb0 _), ← one_div]
    have hnn : ∫ a, ‖Z n 0 a‖ ^ δ ∂μ ≤ Kz * h n := by
      simpa only [Real.norm_eq_abs] using hKzbd n
    exact Real.rpow_le_rpow hb0 hnn (by positivity)
  have hlarge : ∀ (n j : ℕ), 1 ≤ j →
      |Gz n j| ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kz * h n) ^ (2 / δ) := by
    intro n j hj
    have hcov : cov[Z n 0, Z n (j : ℤ); μ] = Gz n j := by
      rw [covariance_eq_sub (hZmem n 0 2) (hZmem n (j : ℤ) 2), hmean0 n 0, zero_mul, sub_zero]
      simp only [hGzdef]
      rfl
    rw [← hcov]
    refine (large_lag_covariance_bound' hmeasX hmeasE hδ (hFm n) j hj
      (hZmem n 0 (ENNReal.ofReal δ)) (hZmem n (j : ℤ) (ENNReal.ofReal δ))).trans ?_
    have hα0 : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
      Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
    have hKh0 : (0 : ℝ) ≤ Kz * h n := mul_nonneg hKz0 (hh0 n).le
    have hsum2 : (1 / δ) + (1 / δ) = 2 / δ := by ring
    have hprod : (Kz * h n) ^ (2 / δ) = (Kz * h n) ^ (1 / δ) * (Kz * h n) ^ (1 / δ) := by
      rw [← hsum2, Real.rpow_add' hKh0 (by rw [hsum2]; positivity)]
    rw [hprod, ← mul_assoc]
    gcongr
    · exact hnormδ n 0
    · exact hnormδ n (j : ℤ)
  -- the lag sum, split at `m_n`
  set IW : ℝ := ∫ v, |W v| with hIWdef
  set SA : ℝ := ∑' t : ℕ, (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) with hSAdef
  have hαnn : ∀ t : ℕ, (0 : ℝ) ≤ (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) :=
    fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
      (Real.rpow_nonneg (pairAlphaCoeff_nonneg X e t) _)
  have hSA0 : (0 : ℝ) ≤ SA := tsum_nonneg hαnn
  have hsplit : ∀ n : ℕ, 1 ≤ smallLagCut h n →
      ∑ j ∈ Finset.Ico 1 n, |Gz n j|
        ≤ (smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2))
          + 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
    intro n hm1
    have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
    have h1 : ∑ j ∈ Finset.Ico 1 n, |Gz n j|
        ≤ ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gz n j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (le_max_left _ _)) fun j _ _ => abs_nonneg _
    have h2 : (∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gz n j|)
          + ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gz n j|
        = ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gz n j| :=
      Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)
    have h3 : ∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gz n j|
        ≤ (smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2)) := by
      have hcard := Finset.sum_le_card_nsmul (Finset.Ico 1 (smallLagCut h n + 1))
        (fun j => |Gz n j|) ((4 * L ^ 2) * (B * (IW * h n) ^ 2))
        (fun j hj => hsmall n j (Finset.mem_Ico.1 hj).1)
      simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
    have h4 : ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gz n j|
        ≤ 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
      have hKh : (0 : ℝ) ≤ (Kz * h n) ^ (2 / δ) :=
        Real.rpow_nonneg (mul_nonneg hKz0 (hh0 n).le) _
      have hmneg : (0 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) := Real.rpow_nonneg hmR.le _
      have hstep : ∀ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)),
          |Gz n j| ≤ 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
            ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
        have hj1' : 1 ≤ j := by omega
        refine (hlarge n j hj1').trans ?_
        have hmj : (smallLagCut h n : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
          Real.rpow_le_rpow hmR.le (by exact_mod_cast (by omega : smallLagCut h n ≤ j)) hlam0.le
        have hαβ : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
          Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
        have hid : (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam = 1 := by
          rw [← Real.rpow_add hmR]; simp
        have hge1 : (1 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam := by
          calc (1 : ℝ) = (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam := hid.symm
            _ ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam :=
                mul_le_mul_of_nonneg_left hmj hmneg
        calc 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kz * h n) ^ (2 / δ)
            = 8 * (Kz * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * 1) := by ring
          _ ≤ 8 * (Kz * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) *
                ((smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam)) := by gcongr
          _ = 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
                ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmneg)
        (mul_nonneg (by norm_num) hKh)
      exact hα.sum_le_tsum _ fun i _ => hαnn i
    linarith
  have hRto0 : Tendsto (fun n : ℕ => 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ =>
        (2 * (4 * L ^ 2) * B * IW ^ 2) * ((smallLagCut h n : ℝ) * h n)
          + (16 * SA * Kz ^ (2 / δ)) *
            (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam)) atTop (𝓝 0) := by
      have t1 := (tendsto_smallLagCut_mul_bandwidth hh0 hh).const_mul
        (2 * (4 * L ^ 2) * B * IW ^ 2)
      have t2 := (tendsto_rpow_mul_abs_log_rpow hh0 hh (a := 2 / δ - 1 + lam)
        (by linarith) hlam0).const_mul (16 * SA * Kz ^ (2 / δ))
      simpa using t1.add t2
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards with n
      have hhn := hh0 n
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    · filter_upwards [(tendsto_abs_log_atTop hh0 hh).eventually_gt_atTop 0] with n hLn
      have hhn : 0 < h n := hh0 n
      have hposL : (0 : ℝ) < h n * |Real.log (h n)| := by positivity
      have hm1 : 1 ≤ smallLagCut h n := Nat.ceil_pos.2 (by positivity)
      have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
      have hmge : (h n * |Real.log (h n)|)⁻¹ ≤ (smallLagCut h n : ℝ) := Nat.le_ceil _
      have hmlam : (0 : ℝ) < (smallLagCut h n : ℝ) ^ lam := Real.rpow_pos_of_pos hmR _
      have hmb : (smallLagCut h n : ℝ) ^ (-lam) ≤ (h n * |Real.log (h n)|) ^ lam := by
        have hprod1 : (1 : ℝ) ≤ (h n * |Real.log (h n)|) * (smallLagCut h n : ℝ) := by
          have h0 := mul_le_mul_of_nonneg_left hmge hposL.le
          rwa [mul_inv_cancel₀ hposL.ne'] at h0
        have h5 : (1 : ℝ) ≤ ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam := by
          have h5' := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hprod1 hlam0.le
          rwa [Real.one_rpow] at h5'
        have h6 : ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam
            = (h n * |Real.log (h n)|) ^ lam * (smallLagCut h n : ℝ) ^ lam :=
          Real.mul_rpow hposL.le hmR.le
        rw [Real.rpow_neg hmR.le]
        refine le_of_mul_le_mul_right ?_ hmlam
        rw [inv_mul_cancel₀ hmlam.ne', ← h6]
        exact h5
      have hS := hsplit n hm1
      refine (mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * (h n)⁻¹)).trans ?_
      rw [mul_add]
      have e1 : 2 * (h n)⁻¹ * ((smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2)))
          = (2 * (4 * L ^ 2) * B * IW ^ 2) * ((smallLagCut h n : ℝ) * h n) := by
        field_simp
      have hKrw : (Kz * h n) ^ (2 / δ) = Kz ^ (2 / δ) * (h n) ^ (2 / δ) :=
        Real.mul_rpow hKz0 hhn.le
      have hLrw : (h n * |Real.log (h n)|) ^ lam
          = (h n) ^ lam * |Real.log (h n)| ^ lam := Real.mul_rpow hhn.le (abs_nonneg _)
      have hpow : (h n) ^ (2 / δ - 1 + lam) = (h n) ^ (2 / δ) * (h n)⁻¹ * (h n) ^ lam := by
        rw [show (2 / δ - 1 + lam) = (2 / δ) + (-1) + lam by ring,
          Real.rpow_add hhn, Real.rpow_add hhn, Real.rpow_neg hhn.le, Real.rpow_one]
      have hKh : (0 : ℝ) ≤ (Kz * h n) ^ (2 / δ) := Real.rpow_nonneg (mul_nonneg hKz0 hhn.le) _
      have e2 : 2 * (h n)⁻¹ * (8 * (Kz * h n) ^ (2 / δ) *
            ((smallLagCut h n : ℝ) ^ (-lam) * SA))
          ≤ (16 * SA * Kz ^ (2 / δ)) *
            ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
        calc 2 * (h n)⁻¹ *
              (8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA))
            ≤ 2 * (h n)⁻¹ * (8 * (Kz * h n) ^ (2 / δ) *
                ((h n * |Real.log (h n)|) ^ lam * SA)) := by gcongr
          _ = (16 * SA * Kz ^ (2 / δ)) *
                ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
              rw [hKrw, hLrw, hpow]; ring
      linarith
  -- assembly
  have hsumrep : ∀ n : ℕ,
      ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
        = ∫ ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    intro n
    refine integral_congr_ae ?_
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ I n,
        truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
          = Z n ((t : ℤ) + 1) ω :=
      (Filter.eventually_all_finset (I n)).2 (fun t _ => hZrep n ((t : ℤ) + 1))
    filter_upwards [hall] with ω hω
    rw [Finset.sum_congr rfl hω]
  refine squeeze_zero' ?_ ?_
    (?_ : Tendsto (fun n : ℕ => (((I n).card : ℝ) / (n : ℝ)) *
      ((4 * L ^ 2) * (Cp * ∫ v, W v ^ 2)
        + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)) atTop (𝓝 0))
  · filter_upwards with n
    have h1 : (0 : ℝ) ≤ ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
        W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have h2 : (0 : ℝ) ≤ ((n : ℝ) * h n)⁻¹ :=
      inv_nonneg.2 (mul_nonneg (Nat.cast_nonneg _) (hh0 n).le)
    exact mul_nonneg h2 h1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hhn : 0 < h n := hh0 n
    rw [hsumrep n, hexp n]
    have habs := abs_double_sum_subset_le (I n) (hIsub n) (Cz n) (Gz n) (hCG n) (hCG' n)
    have hSnn : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 n, |Gz n j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    have hdiagn : (h n)⁻¹ * |Gz n 0| ≤ (4 * L ^ 2) * (Cp * ∫ v, W v ^ 2) := by
      have h1 := hdiag n
      have h2 : (h n)⁻¹ * |Gz n 0|
          ≤ (h n)⁻¹ * ((4 * L ^ 2) * ((Cp * ∫ v, W v ^ 2) * h n)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      refine h2.trans (le_of_eq ?_)
      field_simp
    calc ((n : ℝ) * h n)⁻¹ * (∑ s ∈ I n, ∑ t ∈ I n, Cz n s t)
        ≤ ((n : ℝ) * h n)⁻¹ * |∑ s ∈ I n, ∑ t ∈ I n, Cz n s t| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ ((n : ℝ) * h n)⁻¹ *
            (((I n).card : ℝ) * (|Gz n 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = (((I n).card : ℝ) / (n : ℝ)) *
            ((h n)⁻¹ * |Gz n 0| + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) := by
          field_simp
      _ ≤ (((I n).card : ℝ) / (n : ℝ)) *
            ((4 * L ^ 2) * (Cp * ∫ v, W v ^ 2)
              + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) := by
          gcongr
  · have h1 : Tendsto (fun n : ℕ => (4 * L ^ 2) * (Cp * ∫ v, W v ^ 2)
        + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) atTop
        (𝓝 ((4 * L ^ 2) * (Cp * ∫ v, W v ^ 2) + 0)) := tendsto_const_nhds.add hRto0
    have h2 := hIcard.mul h1
    simpa using h2

/-- The small-block index set: the union of the `k_n` small blocks. -/
noncomputable def smallBlockIdx (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (blockCount h δ lam n)).biUnion fun i =>
    Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n)
      ((i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n))

/-- The small blocks are pairwise disjoint. -/
theorem smallBlockIdx_pairwiseDisjoint (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) :
    (↑(Finset.range (blockCount h δ lam n)) : Set ℕ).PairwiseDisjoint fun i =>
      Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n)
        ((i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)) := by
  set q : ℕ := bigBlockLen h n + smallBlockLen h δ lam n with hq
  set lb : ℕ := bigBlockLen h n with hlb
  have key : ∀ i i' : ℕ, i < i' →
      Disjoint (Finset.Ico (i * q + lb) ((i + 1) * q))
        (Finset.Ico (i' * q + lb) ((i' + 1) * q)) := by
    intro i i' hii
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_Ico] at ha ha'
    have h1 : (i + 1) * q ≤ i' * q := Nat.mul_le_mul_right _ (by omega)
    omega
  intro i _ i' _ hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i i' hlt
  · exact (key i' i hlt).symm

/-- The small blocks live inside `range n`. -/
theorem smallBlockIdx_subset (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) :
    smallBlockIdx h δ lam n ⊆ Finset.range n := by
  intro a ha
  simp only [smallBlockIdx, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico] at ha ⊢
  obtain ⟨i, hi, ha1, ha2⟩ := ha
  have h1 : (i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)
      ≤ blockCount h δ lam n * (bigBlockLen h n + smallBlockLen h δ lam n) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : blockCount h δ lam n * (bigBlockLen h n + smallBlockLen h δ lam n) ≤ n :=
    Nat.div_mul_le_self _ _
  omega

/-- The total small-block length is `k_n s_n`. -/
theorem smallBlockIdx_card (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) :
    (smallBlockIdx h δ lam n).card = blockCount h δ lam n * smallBlockLen h δ lam n := by
  classical
  rw [smallBlockIdx, Finset.card_biUnion (fun i hi i' hi' hne =>
    smallBlockIdx_pairwiseDisjoint h δ lam n (by simpa using hi) (by simpa using hi') hne)]
  have hcard : ∀ i : ℕ,
      (Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n)
        ((i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n))).card
        = smallBlockLen h δ lam n := by
    intro i
    rw [Nat.card_Ico]
    have : (i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)
        = i * (bigBlockLen h n + smallBlockLen h δ lam n)
          + (bigBlockLen h n + smallBlockLen h δ lam n) := by ring
    omega
  rw [Finset.sum_congr rfl (fun i _ => hcard i), Finset.sum_const, Finset.card_range,
    smul_eq_mul]


/-- **FY (2.79)–(2.81) — FALSE AS FROZEN (verified), REPAIRED.** The small blocks (and the
terminal remainder) are `L²`-negligible: their contribution to `locTruncSum` has variance
`→ 0`. The proof is ledger (a) applied to the small-block index sets, whose total length is
`N_n = k_n s_n` with `N_n / n → 0` by the choice of `l_n`, `s_n` (that ratio is
`s_n/(l_n+s_n) → 0`, which is exactly what (C5) buys).

**The statement as frozen carried no hypotheses at all** — `X`, `e`, `W`, `x`, `δ`, `lam`,
`h`, `L` were all free — so it was false, and not for a pathological reason: without
independence/mixing the small-block sum grows *quadratically* in its length instead of
linearly. Witness: `X ≡ 0` (so `σ(X_t)` is trivial), `e_t ≡ ξ` for a single Rademacher
`ξ`, `W ≡ 1`, `h ≡ 1`, `L ≥ 1`, `δ = 3`, `lam = 1`. Then
`truncErr = clamp_L ξ − E[clamp_L ξ] = ξ`, the double sum is `N_n · ξ` with
`N_n = k_n s_n`, the integral is `N_n²`, and the displayed quantity is `N_n²/n`. Here
`l_n = ⌈√n/log n⌉`, `s_n = ⌈(√n log n)^{1/6}⌉`, `k_n ≍ √n log n`, so
`N_n ≍ n^{7/12+o(1)}` and `N_n²/n ≍ n^{1/6} → ∞`.

**Second obstruction (verified): threading (C1)–(C5) as frozen is *not* sufficient
either.** The summands here are the **truncated** ones `ζ_t = e^L_t W((X_t − x)/h_n)` with
`e^L_t = clamp_L(e_t) − E(clamp_L(e_t) | X_t)`, and the ledger-(a) route needs the
small-lag bound `|E[ζ_0 ζ_j]| = O(h²)` (FY (2.76)) on the whole range `1 ≤ j ≤ m_n`. The
combinatorial half is fine — `abs_double_sum_subset_le` is `abs_double_sum_sub_diag_le`
with `range n` replaced by an arbitrary index set, which is all the small blocks need — and
the diagonal and large-lag halves go through unchanged (`|ζ_0| ≤ 2L |W_0|`, so
`‖ζ_0‖_δ = O(h^{1/δ})` by the density change of variables). The small-lag half is not.
Conditioning on `(X_0, X_j)` writes
`E[ζ_0 ζ_j] = E[ψ_L(X_0, X_j) · W((X_0−x)/h) W((X_j−x)/h)]` with `|ψ_L| ≤ 4 L²`: the
conditional recentring has removed **both** error factors, so what the estimate needs is
an *unweighted* bounded joint density for `(X_0, X_j)`. The **frozen** (C2) — the single
instance weighted by `|e_0 e_j|` — supplies only the weighted one, and does not imply it.
The two substitutes available from the frozen package both diverge over the small-lag
range: the crude `|E[ζ_0 ζ_j]| ≤ 4 L² C_W · E|W((X_0−x)/h)| = O(h)` (bounded density) gives
`h⁻¹ · m_n · O(h) = O(m_n) → ∞`, and Davydov gives `h^{2/δ−1} Σ_j α(j)^{1−2/δ} → ∞`
since `2/δ < 1`.

**Statement strengthening (documented).** Two repairs, both authorized:
(i) the whole (C1)–(C5) package is threaded, exactly as `var_localized_sum` carries it
(`hstat`, `hce`, `hcv`, `hδ`/`heLδ`, the (2.73)/(2.74) readings `hσm`/`hσpb`/`heδc`/`hpb`,
`hC2`, `hlam`/`hα`, `hWm`/`hWb`/`hW1`/`hW2`, `hh0`/`hh`/`hnh`), plus `0 < L`; the witness
above shows each of the mixing and moment inputs is load-bearing.
(ii) (C2) is now carried in FY's **printed** form — the bound at an arbitrary error weight
`f`, not just at `f = e_0 e_j` — which is exactly what the second obstruction identifies as
missing; see the module docstring. The instance used here is `f ≡ 1` (unweighted), together
with `f = ` the two singly-weighted ones produced by expanding the recentring.
As in `var_localized_sum`, `hpx`, `hσc`, `hσpb` and `hσm` are carried for uniformity with
the rest of the ledger and are not consumed by this estimate.

**Status: PROVED**, over `tendsto_truncIndex_variance` (the covariance assembly, at an
arbitrary index family) and `tendsto_blockCount_mul_smallBlockLen_div` (the numerology),
applied to the small-block index set `smallBlockIdx`. -/
theorem tendsto_smallBlock_variance [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    -- (C1) USER-INPUT: joint strict stationarity (fdd form); FY (C1)
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ x : ℝ}
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT (authorized (C1) repair): σ² measurable; FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {M Cp : ℝ}
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (hpb : ∀ v, p v ≤ Cp)
    -- (C2) USER-INPUT: (C2) as printed (conditional joint density bounded); FY §2.6.4
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    -- USER-INPUT: positive truncation level (the `L = 0` corner is degenerate); FY §2.6.4
    {L : ℝ} (hL : 0 < L) :
    Tendsto (fun n : ℕ =>
        ((n : ℝ) * h n)⁻¹ *
          ∫ ω, (∑ i ∈ Finset.range (blockCount h δ lam n),
              ∑ t ∈ Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n)
                    + bigBlockLen h n)
                ((i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)),
              truncErr X e μ L ((t : ℤ) + 1) ω *
                W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨B, hB0, hC2gen⟩ := hC2
  have hIcard : Tendsto (fun n : ℕ => ((smallBlockIdx h δ lam n).card : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    refine (tendsto_blockCount_mul_smallBlockLen_div hh0 hnh hδ hlam).congr fun n => ?_
    rw [smallBlockIdx_card]
    push_cast
    ring
  have hsum : ∀ (n : ℕ) (ω : Ω),
      (∑ t ∈ smallBlockIdx h δ lam n,
        truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n))
        = ∑ i ∈ Finset.range (blockCount h δ lam n),
            ∑ t ∈ Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n)
                  + bigBlockLen h n)
              ((i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)),
            truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n) := by
    intro n ω
    simp only [smallBlockIdx]
    exact Finset.sum_biUnion (smallBlockIdx_pairwiseDisjoint h δ lam n)
  refine (tendsto_truncIndex_variance (x := x) hmeasX hmeasE hstat hδ hmp hp0 hpd hpb hB0 hC2gen
    hlam hα hWm hWb hW1 hW2 hh0 hh hL (smallBlockIdx h δ lam)
    (smallBlockIdx_subset h δ lam) hIcard).congr fun n => ?_
  simp only [hsum n]


/-! #### Ledger (d): the four-term telescope -/

/-- **Abstract diagonal-limit device — PROVED.** If `f` is approximated uniformly in
`n` by a family `g L ·` indexed by a level `L → ∞`, each `g L ·` converges to `a L`,
and `a L → A`, then `f n → A`. This is the outer skeleton of FY's four-term telescope:
`L` is the truncation level, the uniform approximation is the truncation tail (2.82),
`a L` is the level-`L` Gaussian charFun, and `a L → A` is the variance continuity in
`L` (2.84). -/
theorem tendsto_of_uniform_approx {f : ℕ → ℂ} {g : ℝ → ℕ → ℂ} {a : ℝ → ℂ} {A : ℂ}
    (happrox : ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop, ∀ n, ‖f n - g L n‖ ≤ ε)
    (hg : ∀ L, Tendsto (g L) atTop (𝓝 (a L)))
    (ha : Tendsto a atTop (𝓝 A)) :
    Tendsto f atTop (𝓝 A) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨L, hL1, hL2⟩ :=
    ((happrox (ε / 3) hε3).and (ha.eventually (Metric.ball_mem_nhds A hε3))).exists
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hg L) (ε / 3) hε3
  refine ⟨N, fun n hn => ?_⟩
  have h1 : ‖f n - g L n‖ ≤ ε / 3 := hL1 n
  have h2 : ‖g L n - a L‖ < ε / 3 := by simpa [dist_eq_norm] using hN n hn
  have h3 : ‖a L - A‖ < ε / 3 := by simpa [Metric.mem_ball, dist_eq_norm] using hL2
  have hsplit : f n - A = f n - g L n + (g L n - a L) + (a L - A) := by ring
  rw [dist_eq_norm, hsplit]
  calc ‖f n - g L n + (g L n - a L) + (a L - A)‖
      ≤ ‖f n - g L n + (g L n - a L)‖ + ‖a L - A‖ := norm_add_le _ _
    _ ≤ ‖f n - g L n‖ + ‖g L n - a L‖ + ‖a L - A‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

/-! #### Ledger (d), step (c): the truncation residual

The private apparatus behind `charFun_locSum_sub_locTruncSum_le`: the pointwise
truncation residual `|z − clamp_L z| ≤ L^{1−δ}|z|^δ` (which is what makes the
recentring constant *decay* in `L`), the resulting decaying representation of
`truncErr`, the `L¹` Lipschitz bound for characteristic functions, the basic
`L²`/`L¹` facts about the residual at **every** `n`, and the uniform-in-`n`
variance bound assembled exactly as ledger (a) was. -/

/-- Pointwise truncation residual, linear form. -/
private theorem abs_sub_clamp_le {δ L z : ℝ} (hδ : 2 < δ) (hL : 0 < L) :
    |z - clampAt L z| ≤ L ^ (1 - δ) * |z| ^ δ := by
  rcases le_or_gt |z| L with hz | hz
  · have h1 : min L z = z := min_eq_right (le_trans (le_abs_self z) hz)
    have h2 : max (-L) z = z := max_eq_right (by have := neg_abs_le z; linarith)
    have hz0 : z - clampAt L z = 0 := by simp [clampAt, h1, h2]
    rw [hz0, abs_zero]
    positivity
  · have hzpos : (0 : ℝ) < |z| := lt_trans hL hz
    have habs : |z - clampAt L z| ≤ |z| := by
      rcases le_or_gt z 0 with hz0 | hz0
      · have hzneg : z < -L := by rw [abs_of_nonpos hz0] at hz; linarith
        have h1 : min L z = z := min_eq_right (by linarith)
        have h2 : max (-L) z = -L := max_eq_left (by linarith)
        simp only [clampAt, h1, h2]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
        linarith
      · have hzpos' : L < z := by rw [abs_of_pos hz0] at hz; exact hz
        have h1 : min L z = L := min_eq_left (by linarith)
        have h2 : max (-L) L = L := max_eq_right (by linarith)
        simp only [clampAt, h1, h2]
        rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
        linarith
    refine habs.trans ?_
    have h1 : L ^ (δ - 1) ≤ |z| ^ (δ - 1) := Real.rpow_le_rpow hL.le hz.le (by linarith)
    have hsplit : |z| ^ (δ - 1) * |z| = |z| ^ δ := by
      nth_rewrite 2 [← Real.rpow_one |z|]
      rw [← Real.rpow_add hzpos]
      ring_nf
    have hone : L ^ (1 - δ) * L ^ (δ - 1) = 1 := by
      rw [← Real.rpow_add hL]; norm_num
    calc |z| = (L ^ (1 - δ) * L ^ (δ - 1)) * |z| := by rw [hone, one_mul]
      _ ≤ (L ^ (1 - δ) * |z| ^ (δ - 1)) * |z| := by gcongr
      _ = L ^ (1 - δ) * (|z| ^ (δ - 1) * |z|) := by ring
      _ = L ^ (1 - δ) * |z| ^ δ := by rw [hsplit]

/-- The recentring constant of `truncErr` decays in `L`. -/
private theorem exists_truncErr_repr_decay [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {δ M : ℝ} (hδ : 2 < δ) (he1 : Integrable (e 0) μ)
    (heδi : Integrable (fun ω => |e 0 ω| ^ δ) μ)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    {L : ℝ} (hL : 0 < L) :
    ∃ mL : ℝ → ℝ, Measurable mL ∧ (∀ v, |mL v| ≤ M * L ^ (1 - δ)) ∧
      ∀ t : ℤ, truncErr X e μ L t =ᵐ[μ] fun ω => clampAt L (e t ω) - mL (X t ω) := by
  classical
  obtain ⟨m, hm, hmB, hrep⟩ := exists_truncErr_repr hmeasX hmeasE hstat hL
  have hM0 : (0 : ℝ) ≤ M := by
    have hZ0 : (0 : Ω → ℝ)
        ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
      condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  set c : ℝ := M * L ^ (1 - δ) with hcdef
  have hc0 : (0 : ℝ) ≤ c := mul_nonneg hM0 (Real.rpow_nonneg hL.le _)
  have hcli : Integrable (fun ω => clampAt L (e 0 ω)) μ := by
    refine (integrable_const L).mono'
      (((measurable_clampAt L).comp (hmeasE 0)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAt_le hL.le _
  have hdiffi : Integrable (fun ω => clampAt L (e 0 ω) - e 0 ω) μ := hcli.sub he1
  -- the conditional expectation of the residual is `m (X 0 ·)`
  have hsub : μ[fun ω => clampAt L (e 0 ω) - e 0 ω | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω =>
        (μ[fun ω' => clampAt L (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance]) ω
          - (μ[e 0 | MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_sub hcli he1 _
  have hkey : ∀ᵐ ω ∂μ,
      (μ[fun ω' => clampAt L (e 0 ω') - e 0 ω' |
        MeasurableSpace.comap (X 0) inferInstance]) ω = m (X 0 ω) := by
    filter_upwards [hsub, hrep 0, hce] with ω ha hb hc
    simp only [truncErr] at hb
    have hb' : (μ[fun ω' => clampAt L (e 0 ω') | MeasurableSpace.comap (X 0) inferInstance]) ω
        = m (X 0 ω) := by linarith
    have hc' : (μ[e 0 | MeasurableSpace.comap (X 0) inferInstance]) ω = 0 := hc
    rw [ha, hb', hc', sub_zero]
  -- and it is bounded by `c` in absolute value
  have hup := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance) hdiffi
    (heδi.const_mul (L ^ (1 - δ)))
    (Eventually.of_forall fun ω => le_trans (le_abs_self _) (by
      rw [abs_sub_comm]; exact abs_sub_clamp_le hδ hL))
  have hlo := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance)
    ((heδi.const_mul (L ^ (1 - δ))).neg) hdiffi
    (Eventually.of_forall fun ω => by
      have h2 : |clampAt L (e 0 ω) - e 0 ω| ≤ L ^ (1 - δ) * |e 0 ω| ^ δ := by
        rw [abs_sub_comm]; exact abs_sub_clamp_le hδ hL
      have h3 := neg_abs_le (clampAt L (e 0 ω) - e 0 ω)
      simp only [Pi.neg_apply]
      linarith)
  have hnegE : μ[-fun ω => L ^ (1 - δ) * |e 0 ω| ^ δ |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] -μ[fun ω => L ^ (1 - δ) * |e 0 ω| ^ δ |
        MeasurableSpace.comap (X 0) inferInstance] := condExp_neg _ _
  have hsm : μ[fun ω => L ^ (1 - δ) * |e 0 ω| ^ δ |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => L ^ (1 - δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_smul (𝕜 := ℝ) (L ^ (1 - δ)) (fun ω => |e 0 ω| ^ δ)
      (MeasurableSpace.comap (X 0) inferInstance)
  have hae : ∀ᵐ ω ∂μ, X 0 ω ∈ {v : ℝ | |m v| ≤ c} := by
    filter_upwards [hkey, hup, hlo, hnegE, hsm, heδc] with ω h0 h1 h2 h3 h4 h5
    show |m (X 0 ω)| ≤ c
    rw [← h0]
    have hMb : L ^ (1 - δ) *
        (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω
          ≤ M * L ^ (1 - δ) := by
      have := mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hL.le (1 - δ))
      calc L ^ (1 - δ) *
            (μ[fun ω' => |e 0 ω'| ^ δ | MeasurableSpace.comap (X 0) inferInstance]) ω
          ≤ L ^ (1 - δ) * M := this
        _ = M * L ^ (1 - δ) := by ring
    simp only [Pi.neg_apply] at h3
    rw [h4] at h1 h3
    rw [hcdef, abs_le]
    constructor
    · rw [h3] at h2; linarith
    · linarith
  have hS : MeasurableSet {v : ℝ | |m v| ≤ c} := measurableSet_le hm.abs measurable_const
  refine ⟨fun v => clampAt c (m v), (measurable_clampAt c).comp hm,
    fun v => abs_clampAt_le hc0 _, fun t => ?_⟩
  filter_upwards [hrep t, ae_comp_X_of_stat hmeasX hmeasE hstat t hS hae] with ω h1 h2
  have h2' : |m (X t ω)| ≤ c := h2
  have hcl : clampAt c (m (X t ω)) = m (X t ω) := by
    unfold clampAt
    rw [min_eq_right (abs_le.1 h2').2, max_eq_right (abs_le.1 h2').1]
  rw [h1, hcl]

/-- Charfun Lipschitz bound (a.e.-measurable form). -/
private theorem norm_charFun_map_sub_le' [IsProbabilityMeasure μ] {S T : Ω → ℝ}
    (hS : AEMeasurable S μ) (hT : AEMeasurable T μ)
    (hi : Integrable (fun ω => |S ω - T ω|) μ) (u : ℝ) :
    ‖charFun (μ.map S) u - charFun (μ.map T) u‖ ≤ |u| * ∫ ω, |S ω - T ω| ∂μ := by
  have hc : Continuous fun z : ℝ => Complex.exp ((u : ℂ) * (z : ℂ) * Complex.I) := by fun_prop
  have hbdd : ∀ (f : Ω → ℝ) (ω : Ω),
      ‖Complex.exp ((u : ℂ) * (f ω : ℂ) * Complex.I)‖ = 1 := by
    intro f ω
    rw [show ((u : ℂ) * (f ω : ℂ) * Complex.I) = ((u * f ω : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hint : ∀ f : Ω → ℝ, AEMeasurable f μ →
      Integrable (fun ω => Complex.exp ((u : ℂ) * (f ω : ℂ) * Complex.I)) μ := by
    intro f hf
    exact (integrable_const (1 : ℝ)).mono'
      (hc.measurable.comp_aemeasurable' hf).aestronglyMeasurable
      (Eventually.of_forall fun ω => le_of_eq (hbdd f ω))
  have hmapS : charFun (μ.map S) u
      = ∫ ω, Complex.exp ((u : ℂ) * (S ω : ℂ) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hS hc.aestronglyMeasurable]
  have hmapT : charFun (μ.map T) u
      = ∫ ω, Complex.exp ((u : ℂ) * (T ω : ℂ) * Complex.I) ∂μ := by
    rw [charFun_apply_real, integral_map hT hc.aestronglyMeasurable]
  rw [hmapS, hmapT, ← integral_sub (hint S hS) (hint T hT)]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono ((hint S hS).sub (hint T hT)).norm (hi.const_mul |u|) fun ω => ?_
  have hfac : Complex.exp ((u : ℂ) * (S ω : ℂ) * Complex.I)
        - Complex.exp ((u : ℂ) * (T ω : ℂ) * Complex.I)
      = Complex.exp ((u : ℂ) * (T ω : ℂ) * Complex.I) *
        (Complex.exp (Complex.I * ((u * (S ω - T ω) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [hfac, norm_mul, hbdd T ω, one_mul]
  refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
  rw [Real.norm_eq_abs, abs_mul]

set_option maxHeartbeats 1000000 in
-- the residual array carries a long chain of `MemLp`/`Integrable` side goals
/-- Basic facts about the truncation residual, valid at **every** `n` and `L > 0`:
square-integrability, a.e.-measurability of the truncated statistic, and the crude
`L¹` bound `√(n/h) C_W (E|e|^δ + M) L^{1−δ}`. -/
private theorem residual_basic [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {δ x : ℝ} (hδ : 2 < δ)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    {M : ℝ}
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    {h : ℕ → ℝ} (n : ℕ) {L : ℝ} (hL0 : 0 < L) :
    MemLp (fun ω => locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) 2 μ
      ∧ AEMeasurable (locTruncSum X e μ W x h L n) μ
      ∧ ∫ ω, |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω| ∂μ
          ≤ (Real.sqrt ((n : ℝ) * h n))⁻¹ * (n : ℝ) *
              (CW * ((∫ ω, |e 0 ω| ^ δ ∂μ) + M) * L ^ (1 - δ)) := by
  classical
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hδ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hδ2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have he1 : Integrable (e 0) μ := heLδ.integrable hδ1
  have heδi : Integrable (fun ω => |e 0 ω| ^ δ) μ := by
    have hr := heLδ.integrable_norm_rpow (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0) ENNReal.ofReal_ne_top
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ0.le] using hr
  have hM0 : (0 : ℝ) ≤ M := by
    have hZ0 : (0 : Ω → ℝ)
        ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
      condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  obtain ⟨mL, hmLm, hmLB, hmLrep⟩ :=
    exists_truncErr_repr_decay hmeasX hmeasE hstat hδ he1 heδi hce heδc hL0
  set c : ℝ := M * L ^ (1 - δ) with hcdef
  have hc0 : (0 : ℝ) ≤ c := mul_nonneg hM0 (Real.rpow_nonneg hL0.le _)
  set Eδ : ℝ := ∫ ω, |e 0 ω| ^ δ ∂μ with hEδdef
  have hEδ0 : (0 : ℝ) ≤ Eδ := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  -- the residual array
  set q : ℝ → ℝ := fun y => |y - clampAt L y| + c with hqdef
  have hqm : Measurable q := ((measurable_id.sub (measurable_clampAt L)).abs).add_const c
  have hq0 : ∀ y, 0 ≤ q y := fun y => by positivity
  set Fr : ℝ × ℝ → ℝ := fun z => (z.2 - clampAt L z.2 + mL z.1) * W ((z.1 - x) / h n)
    with hFrdef
  have hFrm : Measurable Fr :=
    (((measurable_snd.sub ((measurable_clampAt L).comp measurable_snd)).add
      (hmLm.comp measurable_fst))).mul
      (hWm.comp ((measurable_fst.sub measurable_const).div measurable_const))
  have hFrb : ∀ z : ℝ × ℝ, |Fr z| ≤ q z.2 * |W ((z.1 - x) / h n)| := by
    intro z
    rw [hFrdef]
    simp only [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |z.2 - clampAt L z.2 + mL z.1| ≤ |z.2 - clampAt L z.2| + |mL z.1| := abs_add_le _ _
      _ ≤ |z.2 - clampAt L z.2| + c := by
          have := hmLB z.1
          rw [hcdef] at this ⊢
          linarith
  set R : ℤ → Ω → ℝ := fun t ω => Fr (X t ω, e t ω) with hRdef
  have hRm : ∀ t : ℤ, Measurable (R t) := fun t =>
    hFrm.comp ((hmeasX t).prodMk (hmeasE t))
  have hRrep : ∀ t : ℤ, (fun ω => e t ω * W ((X t ω - x) / h n)
      - truncErr X e μ L t ω * W ((X t ω - x) / h n)) =ᵐ[μ] R t := by
    intro t
    filter_upwards [hmLrep t] with ω hω
    simp only [hRdef, hFrdef, hω]
    ring
  -- `L^δ` membership of the residual array
  have habsr : ∀ y : ℝ, |y - clampAt L y| ≤ |y| := by
    intro y
    rcases le_or_gt |y| L with hz | hz
    · have hmin : min L y = y := min_eq_right (le_trans (le_abs_self _) hz)
      have hmax : max (-L) y = y := max_eq_right (by have := neg_abs_le y; linarith)
      simp [clampAt, hmin, hmax]
    · rcases le_or_gt y 0 with hz0 | hz0
      · have hzneg : y < -L := by rw [abs_of_nonpos hz0] at hz; linarith
        have hmin : min L y = y := min_eq_right (by linarith)
        have hmax : max (-L) y = -L := max_eq_left (by linarith)
        simp only [clampAt, hmin, hmax]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
        linarith
      · have hzpos : L < y := by rw [abs_of_pos hz0] at hz; exact hz
        have hmin : min L y = L := min_eq_left (by linarith)
        have hmax : max (-L) L = L := max_eq_right (by linarith)
        simp only [clampAt, hmin, hmax]
        rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
        linarith
  have hMemq : MemLp (fun ω => CW * (‖e 0 ω‖ + c)) (ENNReal.ofReal δ) μ :=
    ((heLδ.norm).add (memLp_const c)).const_mul CW
  have hMemR0 : MemLp (R 0) (ENNReal.ofReal δ) μ := by
    refine MemLp.of_le hMemq (hRm 0).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs]
    have h1 := hFrb (X 0 ω, e 0 ω)
    have h2 : q (e 0 ω) ≤ |e 0 ω| + c := by
      have := habsr (e 0 ω)
      simp only [hqdef]
      linarith
    calc |Fr (X 0 ω, e 0 ω)| ≤ q (e 0 ω) * |W ((X 0 ω - x) / h n)| := h1
      _ ≤ (|e 0 ω| + c) * CW := by
          refine mul_le_mul h2 (hWb _) (abs_nonneg _) (by positivity)
      _ = |CW * (|e 0 ω| + c)| := by
          rw [abs_of_nonneg (mul_nonneg hCW0 (by positivity))]; ring
  have hMemRt : ∀ t : ℤ, MemLp (R t) (ENNReal.ofReal δ) μ := fun t =>
    memLp_comp_pair hmeasX hmeasE hstat t hFrm hMemR0
  have hMemR2 : ∀ t : ℤ, MemLp (R t) 2 μ := fun t => (hMemRt t).mono_exponent hδ2
  have hRi : ∀ t : ℤ, Integrable (R t) μ := fun t => (hMemR2 t).integrable (by norm_num)
  -- the a.e. identification of the difference
  have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range n,
      e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
        - truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
          = R ((t : ℤ) + 1) ω :=
    (Filter.eventually_all_finset _).2 (fun t _ => hRrep ((t : ℤ) + 1))
  have hdiff : (fun ω => locSum X e W x h n ω - locTruncSum X e μ W x h L n ω)
      =ᵐ[μ] fun ω => (Real.sqrt ((n : ℝ) * h n))⁻¹ *
        ∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω := by
    filter_upwards [hall] with ω hω
    simp only [locSum, locTruncSum]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hω]
  have hMemSum : MemLp (fun ω => (Real.sqrt ((n : ℝ) * h n))⁻¹ *
      ∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) 2 μ :=
    (memLp_finset_sum (f := fun t : ℕ => R ((t : ℤ) + 1)) (Finset.range n)
      (fun t _ => hMemR2 ((t : ℤ) + 1))).const_mul _
  have hMem2 : MemLp (fun ω => locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) 2 μ :=
    MemLp.ae_eq hdiff.symm hMemSum
  -- a.e.-measurability of the truncated statistic
  have hSm : Measurable (locSum X e W x h n) := by
    unfold locSum
    exact (Finset.measurable_sum _ fun t _ => (hmeasE _).mul
      (hWm.comp (((hmeasX _).sub measurable_const).div measurable_const))).const_mul _
  have hTaem : AEMeasurable (locTruncSum X e μ W x h L n) μ := by
    refine AEMeasurable.congr (f := fun ω => locSum X e W x h n ω -
      (Real.sqrt ((n : ℝ) * h n))⁻¹ * ∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) ?_ ?_
    · exact (hSm.sub ((Finset.measurable_sum _
        fun t _ => hRm _).const_mul _)).aemeasurable
    · filter_upwards [hdiff] with ω hω
      linarith
  refine ⟨hMem2, hTaem, ?_⟩
  -- the crude `L¹` bound
  have hqint0 : Integrable (fun ω => q (e 0 ω)) μ := by
    have hres1i : Integrable (fun ω => |e 0 ω - clampAt L (e 0 ω)|) μ := by
      refine Integrable.mono he1.abs
        (((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0))).abs).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp only [Real.norm_eq_abs, abs_abs]
      exact habsr (e 0 ω)
    simpa only [hqdef] using! hres1i.add (integrable_const c)
  have hqintt : ∀ t : ℤ, Integrable (fun ω => q (e t ω)) μ := by
    intro t
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => q z.2) (X 0 ω, e 0 ω)) 1 μ :=
      memLp_one_iff_integrable.2 hqint0
    exact memLp_one_iff_integrable.1
      (memLp_comp_pair hmeasX hmeasE hstat t (hqm.comp measurable_snd) h0)
  have hqeq : ∀ t : ℤ, ∫ ω, q (e t ω) ∂μ = ∫ ω, q (e 0 ω) ∂μ := fun t =>
    integral_comp_pair_eq hmeasX hmeasE hstat t
      (F := fun z : ℝ × ℝ => q z.2) (hqm.comp measurable_snd)
  have hq0bd : ∫ ω, q (e 0 ω) ∂μ ≤ (Eδ + M) * L ^ (1 - δ) := by
    have hres1i : Integrable (fun ω => |e 0 ω - clampAt L (e 0 ω)|) μ := by
      refine Integrable.mono he1.abs
        (((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0))).abs).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp only [Real.norm_eq_abs, abs_abs]
      exact habsr (e 0 ω)
    have hb : ∫ ω, q (e 0 ω) ∂μ = (∫ ω, |e 0 ω - clampAt L (e 0 ω)| ∂μ) + c := by
      simp only [hqdef]
      rw [integral_add hres1i (integrable_const c)]
      simp
    have hres1 : ∫ ω, |e 0 ω - clampAt L (e 0 ω)| ∂μ ≤ L ^ (1 - δ) * Eδ := by
      rw [hEδdef, ← integral_const_mul]
      exact integral_mono hres1i (heδi.const_mul _) fun ω => abs_sub_clamp_le hδ hL0
    rw [hb, hcdef]
    nlinarith [hres1]
  have hRabs : ∀ t : ℤ, ∫ ω, |R t ω| ∂μ ≤ CW * ((Eδ + M) * L ^ (1 - δ)) := by
    intro t
    have hstep : ∫ ω, |R t ω| ∂μ ≤ ∫ ω, CW * q (e t ω) ∂μ := by
      refine integral_mono (hRi t).abs ((hqintt t).const_mul CW) fun ω => ?_
      calc |R t ω| ≤ q (e t ω) * |W ((X t ω - x) / h n)| := hFrb (X t ω, e t ω)
        _ ≤ q (e t ω) * CW := mul_le_mul_of_nonneg_left (hWb _) (hq0 _)
        _ = CW * q (e t ω) := mul_comm _ _
    rw [integral_const_mul, hqeq t] at hstep
    exact hstep.trans (mul_le_mul_of_nonneg_left hq0bd hCW0)
  have hsq0 : (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) * h n))⁻¹ := by positivity
  have hfinal : ∫ ω, |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω| ∂μ
      = (Real.sqrt ((n : ℝ) * h n))⁻¹ *
        ∫ ω, |∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω| ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hdiff] with ω hω
    rw [hω, abs_mul, abs_of_nonneg hsq0]
  rw [hfinal]
  have hsumi : Integrable (fun ω => ∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) μ :=
    integrable_finset_sum _ fun t _ => hRi _
  have habsi : Integrable (fun ω => ∑ t ∈ Finset.range n, |R ((t : ℤ) + 1) ω|) μ :=
    integrable_finset_sum _ fun t _ => (hRi _).abs
  have hb1 : ∫ ω, |∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω| ∂μ
      ≤ ∑ t ∈ Finset.range n, ∫ ω, |R ((t : ℤ) + 1) ω| ∂μ := by
    have h1 : ∫ ω, |∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω| ∂μ
        ≤ ∫ ω, ∑ t ∈ Finset.range n, |R ((t : ℤ) + 1) ω| ∂μ :=
      integral_mono hsumi.abs habsi fun ω => Finset.abs_sum_le_sum_abs _ _
    rwa [integral_finset_sum _ (fun t _ => (hRi _).abs)] at h1
  have hb2 : ∑ t ∈ Finset.range n, ∫ ω, |R ((t : ℤ) + 1) ω| ∂μ
      ≤ (n : ℝ) * (CW * ((Eδ + M) * L ^ (1 - δ))) := by
    have := Finset.sum_le_card_nsmul (Finset.range n)
      (fun t => ∫ ω, |R ((t : ℤ) + 1) ω| ∂μ) (CW * ((Eδ + M) * L ^ (1 - δ)))
      (fun t _ => hRabs _)
    simpa [Finset.card_range, nsmul_eq_mul] using this
  calc (Real.sqrt ((n : ℝ) * h n))⁻¹ * ∫ ω, |∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω| ∂μ
      ≤ (Real.sqrt ((n : ℝ) * h n))⁻¹ * ((n : ℝ) * (CW * ((Eδ + M) * L ^ (1 - δ)))) := by
        exact mul_le_mul_of_nonneg_left (hb1.trans hb2) hsq0
    _ = (Real.sqrt ((n : ℝ) * h n))⁻¹ * (n : ℝ) * (CW * (Eδ + M) * L ^ (1 - δ)) := by ring


set_option maxHeartbeats 4000000 in
-- the full covariance assembly (diagonal + small lags + Davydov) in one proof
/-- **Uniform-in-`n` L²-bound for the truncation residual.** -/
private theorem residual_variance_bound [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {M Cp : ℝ}
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    (hpb : ∀ v, p v ≤ Cp)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hC2gen : ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    ∃ C1 C2 C3 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ 0 ≤ C3 ∧ ∀ᶠ n : ℕ in atTop, ∀ L : ℝ, 1 ≤ L →
      ∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ
        ≤ (C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ)) * (1 + (smallLagCut h n : ℝ) * h n)
          + C3 * (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
  classical
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (hp0 0) (hpb 0)
  have hrp : Measurable (fun y : ℝ => y ^ δ) := (Real.continuous_rpow_const hδ0.le).measurable
  have hWam : Measurable (fun v => |W v| ^ δ) := hrp.comp hWm.abs
  have hWδ : Integrable (fun v => |W v| ^ δ) MeasureTheory.volume := by
    refine Integrable.mono (hW2.const_mul (CW ^ (δ - 2))) hWam.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    have hsplit : |W v| ^ δ = |W v| ^ (δ - 2) * |W v| ^ (2 : ℝ) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by intro hcon; linarith),
        show δ - 2 + 2 = δ from by ring]
    have h2 : |W v| ^ (2 : ℝ) = W v ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    have hle : |W v| ^ (δ - 2) ≤ CW ^ (δ - 2) :=
      Real.rpow_le_rpow (abs_nonneg _) (hWb v) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hsplit, h2,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ (δ - 2) * W v ^ 2)]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  -- moments of `e 0`
  have hδ1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hδ2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have he1 : Integrable (e 0) μ := heLδ.integrable hδ1
  have heδi : Integrable (fun ω => |e 0 ω| ^ δ) μ := by
    have hr := heLδ.integrable_norm_rpow (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0) ENNReal.ofReal_ne_top
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hδ0.le] using hr
  have hM0 : (0 : ℝ) ≤ M := by
    have hZ0 : (0 : Ω → ℝ)
        ≤ᵐ[μ] μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance] :=
      condExp_nonneg (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    obtain ⟨ω, h1, h2⟩ := (hZ0.and heδc).exists
    exact le_trans h1 h2
  -- constants
  set IW2 : ℝ := ∫ v, W v ^ 2 with hIW2def
  set IW : ℝ := ∫ v, |W v| with hIWdef
  set IWδ : ℝ := ∫ v, |W v| ^ δ with hIWδdef
  set Eδ : ℝ := ∫ ω, |e 0 ω| ^ δ ∂μ with hEδdef
  set SA : ℝ := ∑' t : ℕ, (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) with hSAdef
  have hIW20 : (0 : ℝ) ≤ IW2 := integral_nonneg fun v => sq_nonneg _
  have hIW0 : (0 : ℝ) ≤ IW := integral_nonneg fun v => abs_nonneg _
  have hIWδ0 : (0 : ℝ) ≤ IWδ := integral_nonneg fun v => Real.rpow_nonneg (abs_nonneg _) _
  have hEδ0 : (0 : ℝ) ≤ Eδ := integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
  have hαnn : ∀ t : ℕ, (0 : ℝ) ≤ (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) :=
    fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
      (Real.rpow_nonneg (pairAlphaCoeff_nonneg X e t) _)
  have hSA0 : (0 : ℝ) ≤ SA := tsum_nonneg hαnn
  set Kρ : ℝ := (2 : ℝ) ^ δ * (M + M ^ δ) * (Cp * IWδ) with hKρdef
  have hKρ0 : (0 : ℝ) ≤ Kρ :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (by positivity)) (mul_nonneg hCp0 hIWδ0)
  refine ⟨2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ,
    2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2, 16 * SA * Kρ ^ (2 / δ),
    by positivity, by positivity, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_abs_log_atTop hh0 hh).eventually_gt_atTop 0] with n hn1 hlogn
  intro L hL
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨mL, hmLm, hmLB, hmLrep⟩ :=
    exists_truncErr_repr_decay hmeasX hmeasE hstat hδ he1 heδi hce heδc hL0
  set c : ℝ := M * L ^ (1 - δ) with hcdef
  have hc0 : (0 : ℝ) ≤ c := mul_nonneg hM0 (Real.rpow_nonneg hL0.le _)
  have hcM : c ≤ M := by
    have h1 : L ^ (1 - δ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith : (1 : ℝ) - δ ≤ 0)
    rw [hcdef]
    nlinarith
  -- the residual array
  set q : ℝ → ℝ := fun y => |y - clampAt L y| + c with hqdef
  have hqm : Measurable q := ((measurable_id.sub (measurable_clampAt L)).abs).add_const c
  have hq0 : ∀ y, 0 ≤ q y := fun y => by positivity
  set Fr : ℝ × ℝ → ℝ := fun z => (z.2 - clampAt L z.2 + mL z.1) * W ((z.1 - x) / h n)
    with hFrdef
  have hFrm : Measurable Fr :=
    (((measurable_snd.sub ((measurable_clampAt L).comp measurable_snd)).add
      (hmLm.comp measurable_fst))).mul
      (hWm.comp ((measurable_fst.sub measurable_const).div measurable_const))
  have hFrb : ∀ z : ℝ × ℝ, |Fr z| ≤ q z.2 * |W ((z.1 - x) / h n)| := by
    intro z
    rw [hFrdef]
    simp only [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |z.2 - clampAt L z.2 + mL z.1| ≤ |z.2 - clampAt L z.2| + |mL z.1| := abs_add_le _ _
      _ ≤ |z.2 - clampAt L z.2| + c := by
          have := hmLB z.1
          rw [hcdef] at this ⊢
          linarith
  set R : ℤ → Ω → ℝ := fun t ω => Fr (X t ω, e t ω) with hRdef
  have hRm : ∀ t : ℤ, Measurable (R t) := fun t =>
    hFrm.comp ((hmeasX t).prodMk (hmeasE t))
  have hRrep : ∀ t : ℤ, (fun ω => e t ω * W ((X t ω - x) / h n)
      - truncErr X e μ L t ω * W ((X t ω - x) / h n)) =ᵐ[μ] R t := by
    intro t
    filter_upwards [hmLrep t] with ω hω
    simp only [hRdef, hFrdef, hω]
    ring
  -- membership in `L^δ`
  have hMemq : MemLp (fun ω => CW * (‖e 0 ω‖ + c)) (ENNReal.ofReal δ) μ :=
    ((heLδ.norm).add (memLp_const c)).const_mul CW
  have hMemR0 : MemLp (R 0) (ENNReal.ofReal δ) μ := by
    refine MemLp.of_le hMemq (hRm 0).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    simp only [Real.norm_eq_abs]
    have h1 := hFrb (X 0 ω, e 0 ω)
    have h2 : q (e 0 ω) ≤ |e 0 ω| + c := by
      rw [hqdef]
      simp only
      have := abs_sub_clamp_le (δ := δ) (L := L) (z := e 0 ω) hδ hL0
      have h3 : |e 0 ω - clampAt L (e 0 ω)| ≤ |e 0 ω| := by
        rcases le_or_gt |e 0 ω| L with hz | hz
        · have hmin : min L (e 0 ω) = e 0 ω :=
            min_eq_right (le_trans (le_abs_self _) hz)
          have hmax : max (-L) (e 0 ω) = e 0 ω :=
            max_eq_right (by have := neg_abs_le (e 0 ω); linarith)
          simp [clampAt, hmin, hmax]
        · rcases le_or_gt (e 0 ω) 0 with hz0 | hz0
          · have hzneg : e 0 ω < -L := by rw [abs_of_nonpos hz0] at hz; linarith
            have hmin : min L (e 0 ω) = e 0 ω := min_eq_right (by linarith)
            have hmax : max (-L) (e 0 ω) = -L := max_eq_left (by linarith)
            simp only [clampAt, hmin, hmax]
            rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
            linarith
          · have hzpos : L < e 0 ω := by rw [abs_of_pos hz0] at hz; exact hz
            have hmin : min L (e 0 ω) = L := min_eq_left (by linarith)
            have hmax : max (-L) L = L := max_eq_right (by linarith)
            simp only [clampAt, hmin, hmax]
            rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
            linarith
      linarith
    calc |Fr (X 0 ω, e 0 ω)| ≤ q (e 0 ω) * |W ((X 0 ω - x) / h n)| := h1
      _ ≤ (|e 0 ω| + c) * CW := by
          refine mul_le_mul h2 (hWb _) (abs_nonneg _) (by positivity)
      _ = |CW * (|e 0 ω| + c)| := by
          rw [abs_of_nonneg (mul_nonneg hCW0 (by positivity))]; ring
  have hMemRt : ∀ t : ℤ, MemLp (R t) (ENNReal.ofReal δ) μ := fun t =>
    memLp_comp_pair hmeasX hmeasE hstat t hFrm hMemR0
  have hMemR2 : ∀ t : ℤ, MemLp (R t) 2 μ := fun t => (hMemRt t).mono_exponent hδ2
  have hintR : ∀ s t : ℤ, Integrable (fun ω => R s ω * R t ω) μ :=
    fun s t => (hMemR2 s).integrable_mul (hMemR2 t)
  -- each residual summand is centred
  have hclampint : ∀ t : ℤ, Integrable (fun ω => clampAt L (e t ω)) μ := by
    intro t
    refine (integrable_const L).mono'
      (((measurable_clampAt L).comp (hmeasE t)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAt_le hL0.le _
  have het : ∀ t : ℤ, Integrable (e t) μ := by
    intro t
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => z.2) (X 0 ω, e 0 ω)) 1 μ :=
      memLp_one_iff_integrable.2 he1
    exact memLp_one_iff_integrable.1
      (memLp_comp_pair hmeasX hmeasE hstat t measurable_snd h0)
  have hcondR : ∀ t : ℤ,
      μ[fun ω => e t ω - clampAt L (e t ω) | MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => -mL (X t ω) := by
    intro t
    have hsub : μ[fun ω => e t ω - clampAt L (e t ω) |
          MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => (μ[e t | MeasurableSpace.comap (X t) inferInstance]) ω
            - (μ[fun ω' => clampAt L (e t ω') |
                MeasurableSpace.comap (X t) inferInstance]) ω :=
      condExp_sub (het t) (hclampint t) _
    have hz := condExp_eq_zero_of_stat hmeasX hmeasE hstat he1 hce t
    filter_upwards [hsub, hz, hmLrep t] with ω h1 h2 h3
    simp only [truncErr] at h3
    have h3' : (μ[fun ω' => clampAt L (e t ω') |
        MeasurableSpace.comap (X t) inferInstance]) ω = mL (X t ω) := by linarith
    have h2' : (μ[e t | MeasurableSpace.comap (X t) inferInstance]) ω = 0 := h2
    rw [h1, h2', h3']
    ring
  have hWXm : ∀ t : ℤ, Measurable (fun ω => W ((X t ω - x) / h n)) := fun t =>
    hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)
  have hmeanR : ∀ t : ℤ, ∫ ω, R t ω ∂μ = 0 := by
    intro t
    have hζi : Integrable (fun ω => e t ω - clampAt L (e t ω)) μ := (het t).sub (hclampint t)
    have hz := integral_bdd_comp_mul_eq_of_condExp (μ := μ) (hmeasX t) hζi (hcondR t)
      (fun v => W ((v - x) / h n)) (by fun_prop) (C := CW) (fun v => hWb _)
    have hi1 : Integrable (fun ω => W ((X t ω - x) / h n) * (e t ω - clampAt L (e t ω))) μ :=
      hζi.bdd_mul (hWXm t).aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWb _)
    have hi2 : Integrable (fun ω => W ((X t ω - x) / h n) * mL (X t ω)) μ := by
      refine (integrable_const (CW * (M * L ^ (1 - δ)))).mono'
        (((hWXm t).mul (hmLm.comp (hmeasX t))).aestronglyMeasurable)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hWb _) (hmLB _) (abs_nonneg _) hCW0
    have hsplit : ∫ ω, R t ω ∂μ
        = ∫ ω, W ((X t ω - x) / h n) * (e t ω - clampAt L (e t ω)) ∂μ
          + ∫ ω, W ((X t ω - x) / h n) * mL (X t ω) ∂μ := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [hRdef, hFrdef]; ring)
    have hneg : ∫ ω, W ((X t ω - x) / h n) * (fun ω => -mL (X t ω)) ω ∂μ
        = -∫ ω, W ((X t ω - x) / h n) * mL (X t ω) ∂μ := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [hsplit, hz, hneg]
    ring
  -- the lag covariance array
  set Gr : ℕ → ℝ := fun d => ∫ ω, R 0 ω * R (d : ℤ) ω ∂μ with hGrdef
  set Cr : ℕ → ℕ → ℝ := fun s t => ∫ ω, R ((s : ℤ) + 1) ω * R ((t : ℤ) + 1) ω ∂μ with hCrdef
  have hCG : ∀ s d : ℕ, Cr s (s + d) = Gr d := by
    intro s d
    have hidx : ((s + d : ℕ) : ℤ) + 1 = ((s : ℤ) + 1) + (d : ℤ) := by push_cast; ring
    have htr := integral_comp_pair2_eq hmeasX hmeasE hstat ((s : ℤ) + 1) d
      (G := fun z : (ℝ × ℝ) × (ℝ × ℝ) => Fr z.1 * Fr z.2)
      ((hFrm.comp measurable_fst).mul (hFrm.comp measurable_snd))
    simp only [hCrdef, hGrdef, hRdef, hidx]
    exact htr
  have hCG' : ∀ s d : ℕ, Cr (s + d) s = Gr d := by
    intro s d
    have hsym : Cr (s + d) s = Cr s (s + d) := by
      simp only [hCrdef]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsym, hCG]
  have hexp : ∫ ω, (∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) ^ 2 ∂μ
      = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t := by
    have hsq2 : ∀ ω : Ω, (∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) ^ 2
        = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
            R ((s : ℤ) + 1) ω * R ((t : ℤ) + 1) ω := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp only [hsq2, hCrdef]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hintR _ _))]
    exact Finset.sum_congr rfl fun s _ => integral_finset_sum _ (fun t _ => hintR _ _)
  -- conversion of the goal
  have hsqinv : ((Real.sqrt ((n : ℝ) * h n))⁻¹) ^ 2 = ((n : ℝ) * h n)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) (hh0 n).le)]
  have hconv : ∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ
      = ((n : ℝ) * h n)⁻¹ * ∫ ω, (∑ t ∈ Finset.range n, R ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range n,
        e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
          - truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
            = R ((t : ℤ) + 1) ω :=
      (Filter.eventually_all_finset _).2 (fun t _ => hRrep ((t : ℤ) + 1))
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hall] with ω hω
    simp only [locSum, locTruncSum]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hω, mul_pow, hsqinv]
  -- pointwise facts about the clamp residual
  have habsr : ∀ y : ℝ, |y - clampAt L y| ≤ |y| := by
    intro y
    rcases le_or_gt |y| L with hz | hz
    · have hmin : min L y = y := min_eq_right (le_trans (le_abs_self _) hz)
      have hmax : max (-L) y = y := max_eq_right (by have := neg_abs_le y; linarith)
      simp [clampAt, hmin, hmax]
    · rcases le_or_gt y 0 with hz0 | hz0
      · have hzneg : y < -L := by rw [abs_of_nonpos hz0] at hz; linarith
        have hmin : min L y = y := min_eq_right (by linarith)
        have hmax : max (-L) y = -L := max_eq_left (by linarith)
        simp only [clampAt, hmin, hmax]
        rw [abs_of_nonpos (by linarith), abs_of_nonpos hz0]
        linarith
      · have hzpos : L < y := by rw [abs_of_pos hz0] at hz; exact hz
        have hmin : min L y = L := min_eq_left (by linarith)
        have hmax : max (-L) L = L := max_eq_right (by linarith)
        simp only [clampAt, hmin, hmax]
        rw [abs_of_nonneg (by linarith), abs_of_pos hz0]
        linarith
  have hc2 : c ^ 2 = M ^ 2 * L ^ (2 - 2 * δ) := by
    have hkey : (L ^ (1 - δ)) ^ (2 : ℕ) = L ^ (2 - 2 * δ) := by
      rw [← Real.rpow_natCast (L ^ (1 - δ)) 2, ← Real.rpow_mul hL0.le]
      norm_num
      ring_nf
    rw [hcdef, mul_pow, hkey]
  have he2 : Integrable (fun ω => e 0 ω ^ 2) μ := (heLδ.mono_exponent hδ2).integrable_sq
  -- diagonal
  have hiA : Integrable
      (fun ω => (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / h n) ^ 2) μ := by
    refine Integrable.mono ((heδi.const_mul (L ^ (2 - δ))).const_mul (CW ^ 2))
      ((((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0))).pow_const 2).mul
        ((hWXm 0).pow_const 2)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ 2 * (L ^ (2 - δ) * |e 0 ω| ^ δ))]
    have h1 := sq_sub_clamp_le (δ := δ) (L := L) (z := e 0 ω) hδ hL0
    have h2 : W ((X 0 ω - x) / h n) ^ 2 ≤ CW ^ 2 := by
      have := hWb ((X 0 ω - x) / h n)
      nlinarith [sq_abs (W ((X 0 ω - x) / h n)), abs_nonneg (W ((X 0 ω - x) / h n))]
    nlinarith [sq_nonneg (e 0 ω - clampAt L (e 0 ω)), sq_nonneg (W ((X 0 ω - x) / h n)),
      Real.rpow_nonneg (abs_nonneg (e 0 ω)) δ, Real.rpow_nonneg hL0.le (2 - δ)]
  have hiB : Integrable (fun ω => W ((X 0 ω - x) / h n) ^ 2) μ := by
    refine (integrable_const (CW ^ 2)).mono' ((hWXm 0).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have := hWb ((X 0 ω - x) / h n)
    nlinarith [sq_abs (W ((X 0 ω - x) / h n)), abs_nonneg (W ((X 0 ω - x) / h n))]
  have hres := localized_trunc_residual_moment_le (X := X) (e := e) (hmeasX 0) (hmeasE 0)
    hmp hp0 hpd hδ heLδ heδc hpb hWm hWb hW2 (x := x) (hn := h n) (hh0 n) hL0
  have hwt := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
    (G := fun v => W v ^ 2) (hWm.pow_const 2) (fun v => sq_nonneg _) hW2 (x := x) (hh0 n)
  have hdiagR : |Gr 0|
      ≤ (2 * (M * Cp * IW2) * L ^ (2 - δ) + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ))
        * h n := by
    have hGeq : Gr 0 = ∫ ω, (R 0 ω) ^ 2 ∂μ := by
      simp only [hGrdef, Nat.cast_zero]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hGnn : 0 ≤ Gr 0 := by rw [hGeq]; exact integral_nonneg fun ω => sq_nonneg _
    have hmaj : ∫ ω, (R 0 ω) ^ 2 ∂μ
        ≤ 2 * ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
          + 2 * c ^ 2 * ∫ ω, W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hiA.const_mul 2)
        (hiB.const_mul (2 * c ^ 2))]
      refine integral_mono (hMemR2 0).integrable_sq
        ((hiA.const_mul 2).add (hiB.const_mul (2 * c ^ 2))) fun ω => ?_
      have hb := hmLB (X 0 ω)
      have hb2 : mL (X 0 ω) ^ 2 ≤ c ^ 2 := by
        rw [hcdef] at hb ⊢
        nlinarith [abs_nonneg (mL (X 0 ω)), sq_abs (mL (X 0 ω))]
      simp only [hRdef, hFrdef, mul_pow]
      nlinarith [sq_nonneg (W ((X 0 ω - x) / h n)),
        sq_nonneg ((e 0 ω - clampAt L (e 0 ω)) - mL (X 0 ω)),
        sq_nonneg ((e 0 ω - clampAt L (e 0 ω)) + mL (X 0 ω))]
    rw [abs_of_nonneg hGnn, hGeq]
    refine hmaj.trans ?_
    have hstep1 : 2 * ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ
        ≤ 2 * ((M * Cp * IW2) * (L ^ (2 - δ) * h n)) := by
      have : (0 : ℝ) ≤ 2 := by norm_num
      exact mul_le_mul_of_nonneg_left hres this
    have hstep2 : 2 * c ^ 2 * ∫ ω, W ((X 0 ω - x) / h n) ^ 2 ∂μ
        ≤ 2 * c ^ 2 * ((Cp * IW2) * h n) :=
      mul_le_mul_of_nonneg_left hwt (by positivity)
    rw [hc2] at hstep2
    rw [hc2]
    refine le_trans (add_le_add hstep1 hstep2) (le_of_eq ?_)
    ring
  -- small lags
  have hqsqle : ∀ y : ℝ, q y ^ 2 ≤ 2 * (y - clampAt L y) ^ 2 + 2 * c ^ 2 := by
    intro y
    have h1 : q y = |y - clampAt L y| + c := rfl
    rw [h1]
    nlinarith [sq_abs (y - clampAt L y), sq_nonneg (|y - clampAt L y| - c)]
  have hqsqle2 : ∀ y : ℝ, q y ^ 2 ≤ 2 * y ^ 2 + 2 * c ^ 2 := by
    intro y
    refine (hqsqle y).trans ?_
    have h2 := habsr y
    nlinarith [sq_abs (y - clampAt L y), sq_abs y, abs_nonneg (y - clampAt L y), abs_nonneg y]
  have hiq2 : ∀ t : ℤ, Integrable (fun ω => q (e t ω) ^ 2) μ := by
    intro t
    have h0 : MemLp (fun ω => (fun z : ℝ × ℝ => q z.2 ^ 2) (X 0 ω, e 0 ω)) 1 μ := by
      refine memLp_one_iff_integrable.2 ?_
      refine Integrable.mono ((he2.const_mul 2).add (integrable_const (2 * c ^ 2)))
        (((hqm.comp (hmeasE 0)).pow_const 2)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * e 0 ω ^ 2 + 2 * c ^ 2)]
      exact hqsqle2 (e 0 ω)
    exact memLp_one_iff_integrable.1
      (memLp_comp_pair hmeasX hmeasE hstat t ((hqm.comp measurable_snd).pow_const 2) h0)
  have hq2eq : ∀ t : ℤ, ∫ ω, q (e t ω) ^ 2 ∂μ = ∫ ω, q (e 0 ω) ^ 2 ∂μ := fun t =>
    integral_comp_pair_eq hmeasX hmeasE hstat t
      (F := fun z : ℝ × ℝ => q z.2 ^ 2) ((hqm.comp measurable_snd).pow_const 2)
  have hressq : ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 ∂μ ≤ L ^ (2 - δ) * Eδ := by
    have hi1 : Integrable (fun ω => (e 0 ω - clampAt L (e 0 ω)) ^ 2) μ := by
      refine Integrable.mono he2
        ((((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0)))).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      have := habsr (e 0 ω)
      nlinarith [sq_abs (e 0 ω - clampAt L (e 0 ω)), sq_abs (e 0 ω),
        abs_nonneg (e 0 ω - clampAt L (e 0 ω)), abs_nonneg (e 0 ω)]
    have hi2 : Integrable (fun ω => L ^ (2 - δ) * |e 0 ω| ^ δ) μ := heδi.const_mul _
    calc ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 ∂μ
        ≤ ∫ ω, L ^ (2 - δ) * |e 0 ω| ^ δ ∂μ :=
          integral_mono hi1 hi2 (fun ω => sq_sub_clamp_le hδ hL0)
      _ = L ^ (2 - δ) * Eδ := by rw [integral_const_mul]
  have hq2int : ∫ ω, q (e 0 ω) ^ 2 ∂μ ≤ 2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2 := by
    have hi1 : Integrable (fun ω => (e 0 ω - clampAt L (e 0 ω)) ^ 2) μ := by
      refine Integrable.mono he2
        ((((hmeasE 0).sub ((measurable_clampAt L).comp (hmeasE 0)))).pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _)]
      have := habsr (e 0 ω)
      nlinarith [sq_abs (e 0 ω - clampAt L (e 0 ω)), sq_abs (e 0 ω),
        abs_nonneg (e 0 ω - clampAt L (e 0 ω)), abs_nonneg (e 0 ω)]
    have hi3 : Integrable (fun ω => 2 * (e 0 ω - clampAt L (e 0 ω)) ^ 2 + 2 * c ^ 2) μ :=
      (hi1.const_mul 2).add (integrable_const (2 * c ^ 2))
    calc ∫ ω, q (e 0 ω) ^ 2 ∂μ
        ≤ ∫ ω, (2 * (e 0 ω - clampAt L (e 0 ω)) ^ 2 + 2 * c ^ 2) ∂μ :=
          integral_mono (hiq2 0) hi3 (fun ω => hqsqle (e 0 ω))
      _ = 2 * ∫ ω, (e 0 ω - clampAt L (e 0 ω)) ^ 2 ∂μ + 2 * c ^ 2 := by
          rw [integral_add (hi1.const_mul 2) (integrable_const (2 * c ^ 2)),
            integral_const_mul]
          simp
      _ ≤ 2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2 := by linarith
  have hsmallR : ∀ j : ℕ, 1 ≤ j →
      |Gr j| ≤ B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2 := by
    intro j hj
    have hjz : ((j : ℤ)) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    have hfm : Measurable (fun z : ℝ × ℝ => q z.1 * q z.2) :=
      (hqm.comp measurable_fst).mul (hqm.comp measurable_snd)
    have hgm : Measurable
        (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|) := by fun_prop
    have hg0 : ∀ z : ℝ × ℝ, 0 ≤ |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)| :=
      fun z => by positivity
    have hRHSi : Integrable (fun ω => |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| *
        (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|)
          (X 0 ω, X (j : ℤ) ω)) μ := by
      refine Integrable.mono
        (((hiq2 0).const_mul (CW ^ 2)).add ((hiq2 (j : ℤ)).const_mul (CW ^ 2)))
        ((((hfm.comp ((hmeasE 0).prodMk (hmeasE (j : ℤ)))).abs).mul
          (hgm.comp ((hmeasX 0).prodMk (hmeasX (j : ℤ)))))).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]
      have hq00 : 0 ≤ q (e 0 ω) := hq0 _
      have hqj0 : 0 ≤ q (e (j : ℤ) ω) := hq0 _
      have hw0 := hWb ((X 0 ω - x) / h n)
      have hwj := hWb ((X (j : ℤ) ω - x) / h n)
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ |q (e 0 ω) * q (e (j : ℤ) ω)| *
        (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ 2 * q (e 0 ω) ^ 2 +
          CW ^ 2 * q (e (j : ℤ) ω) ^ 2),
        abs_of_nonneg (mul_nonneg hq00 hqj0)]
      have hprodW : |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ≤ CW ^ 2 := by
        nlinarith [abs_nonneg (W ((X 0 ω - x) / h n)), abs_nonneg (W ((X (j : ℤ) ω - x) / h n))]
      nlinarith [sq_nonneg (q (e 0 ω) - q (e (j : ℤ) ω)), mul_nonneg hq00 hqj0]
    have hA : |Gr j| ≤ ∫ ω, |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| *
        (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|)
          (X 0 ω, X (j : ℤ) ω) ∂μ := by
      have h0 := norm_integral_le_integral_norm (μ := μ) (fun ω => R 0 ω * R (j : ℤ) ω)
      simp only [Real.norm_eq_abs] at h0
      refine (le_trans h0 ?_)
      refine integral_mono (hintR 0 (j : ℤ)).abs hRHSi fun ω => ?_
      have hb0 := hFrb (X 0 ω, e 0 ω)
      have hbj := hFrb (X (j : ℤ) ω, e (j : ℤ) ω)
      simp only [hRdef, abs_mul]
      rw [abs_of_nonneg (hq0 (e 0 ω)), abs_of_nonneg (hq0 (e (j : ℤ) ω))]
      calc |Fr (X 0 ω, e 0 ω)| * |Fr (X (j : ℤ) ω, e (j : ℤ) ω)|
          ≤ (q (e 0 ω) * |W ((X 0 ω - x) / h n)|) *
            (q (e (j : ℤ) ω) * |W ((X (j : ℤ) ω - x) / h n)|) :=
            mul_le_mul hb0 hbj (abs_nonneg _) (by positivity)
        _ = q (e 0 ω) * q (e (j : ℤ) ω) *
            (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by ring
    have hC2 := hC2gen (j : ℤ) hjz (fun z : ℝ × ℝ => q z.1 * q z.2) hfm _ hgm hg0
    refine hA.trans (hC2.trans ?_)
    have hfint : ∫ ω, |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| ∂μ
        ≤ 2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2 := by
      have hi : Integrable (fun ω => |q (e 0 ω) * q (e (j : ℤ) ω)|) μ := by
        refine Integrable.mono (((hiq2 0).add (hiq2 (j : ℤ))).div_const 2)
          ((((hqm.comp (hmeasE 0)).mul (hqm.comp (hmeasE (j : ℤ)))).abs)).aestronglyMeasurable
          (Eventually.of_forall fun ω => ?_)
        simp only [Pi.add_apply, Real.norm_eq_abs]
        rw [abs_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤
          (q (e 0 ω) ^ 2 + q (e (j : ℤ) ω) ^ 2) / 2),
          abs_of_nonneg (mul_nonneg (hq0 _) (hq0 _))]
        nlinarith [sq_nonneg (q (e 0 ω) - q (e (j : ℤ) ω))]
      have hstep : ∫ ω, |q (e 0 ω) * q (e (j : ℤ) ω)| ∂μ
          ≤ ∫ ω, (q (e 0 ω) ^ 2 + q (e (j : ℤ) ω) ^ 2) / 2 ∂μ := by
        refine integral_mono hi (((hiq2 0).add (hiq2 (j : ℤ))).div_const 2) fun ω => ?_
        rw [abs_of_nonneg (mul_nonneg (hq0 _) (hq0 _))]
        nlinarith [sq_nonneg (q (e 0 ω) - q (e (j : ℤ) ω))]
      have heval : ∫ ω, (q (e 0 ω) ^ 2 + q (e (j : ℤ) ω) ^ 2) / 2 ∂μ
          = ∫ ω, q (e 0 ω) ^ 2 ∂μ := by
        rw [integral_div, integral_add (hiq2 0) (hiq2 (j : ℤ)), hq2eq (j : ℤ)]
        ring
      simp only
      rw [heval] at hstep
      exact hstep.trans hq2int
    have hprodg : ∫ z : ℝ × ℝ, |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|
          ∂(MeasureTheory.volume.prod MeasureTheory.volume)
        = (∫ v, |W ((v - x) / h n)|) * ∫ w, |W ((w - x) / h n)| :=
      integral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (f := fun v => |W ((v - x) / h n)|) (g := fun w => |W ((w - x) / h n)|)
    have honeW : ∫ v, |W ((v - x) / h n)| = h n * IW := by
      have := integral_dilate_translate (fun u => |W u|) (fun _ => (1 : ℝ)) x (hh0 n)
      simp only [mul_one] at this
      rw [hIWdef, this, ← mul_assoc, mul_inv_cancel₀ (hh0 n).ne', one_mul]
    rw [hprodg, honeW]
    have hnn : (0 : ℝ) ≤ (h n * IW) * (h n * IW) :=
      mul_nonneg (mul_nonneg (hh0 n).le hIW0) (mul_nonneg (hh0 n).le hIW0)
    have hB2 : (0 : ℝ) ≤ B := hB0
    calc B * (∫ ω, |(fun z : ℝ × ℝ => q z.1 * q z.2) (e 0 ω, e (j : ℤ) ω)| ∂μ)
          * ((h n * IW) * (h n * IW))
        ≤ B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * ((h n * IW) * (h n * IW)) := by
          gcongr
      _ = B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2 := by ring
  -- the localized δ-th moment of the residual array
  have hpow2 : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ δ ≤ 2 ^ δ * (a ^ δ + b ^ δ) := by
    intro a b ha hb
    have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ δ := Real.rpow_nonneg (by norm_num) _
    have h5a : (0 : ℝ) ≤ a ^ δ := Real.rpow_nonneg ha _
    have h5b : (0 : ℝ) ≤ b ^ δ := Real.rpow_nonneg hb _
    rcases le_total a b with hab | hab
    · have h1 : a + b ≤ 2 * b := by linarith
      have h3 := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ a + b) h1 hδ0.le
      rw [Real.mul_rpow (by norm_num) hb] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left h5a) h4)
    · have h1 : a + b ≤ 2 * a := by linarith
      have h3 := Real.rpow_le_rpow (by linarith : (0 : ℝ) ≤ a + b) h1 hδ0.le
      rw [Real.mul_rpow (by norm_num) ha] at h3
      exact h3.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right h5b) h4)
  have hGm2 : Measurable (fun v => |W ((v - x) / h n)| ^ δ) :=
    hrp.comp ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).abs)
  have hGXm2 : Measurable (fun ω => |W ((X 0 ω - x) / h n)| ^ δ) := hGm2.comp (hmeasX 0)
  have hiW1 : Integrable (fun ω => |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ) μ := by
    refine Integrable.mono (heδi.const_mul (CW ^ δ))
      ((hrp.comp (((hmeasE 0).mul (hWXm 0)).abs))).aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ δ * |e 0 ω| ^ δ), abs_mul,
      Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm (CW ^ δ)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le) (Real.rpow_nonneg (abs_nonneg _) _)
  have hiW2 : Integrable (fun ω => |W ((X 0 ω - x) / h n)| ^ δ) μ := by
    refine (integrable_const (CW ^ δ)).mono' hGXm2.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le
  have hdeltaR : ∫ ω, |R 0 ω| ^ δ ∂μ ≤ Kρ * h n := by
    have hbd : ∀ ω, |R 0 ω| ^ δ
        ≤ 2 ^ δ * (|e 0 ω * W ((X 0 ω - x) / h n)| ^ δ
            + M ^ δ * |W ((X 0 ω - x) / h n)| ^ δ) := by
      intro ω
      have h1 : |R 0 ω| ≤ (|e 0 ω| + M) * |W ((X 0 ω - x) / h n)| := by
        refine le_trans (hFrb (X 0 ω, e 0 ω)) ?_
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have h2 : q (e 0 ω) = |e 0 ω - clampAt L (e 0 ω)| + c := rfl
        have h3 := habsr (e 0 ω)
        rw [h2]; linarith
      have h4 : |R 0 ω| ^ δ ≤ ((|e 0 ω| + M) * |W ((X 0 ω - x) / h n)|) ^ δ :=
        Real.rpow_le_rpow (abs_nonneg _) h1 hδ0.le
      refine h4.trans ?_
      rw [Real.mul_rpow (by positivity) (abs_nonneg _)]
      have h5 := hpow2 (|e 0 ω|) M (abs_nonneg _) hM0
      have h6 : |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ
          = |e 0 ω| ^ δ * |W ((X 0 ω - x) / h n)| ^ δ := by
        rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      rw [h6]
      have h7 : (0 : ℝ) ≤ |W ((X 0 ω - x) / h n)| ^ δ := Real.rpow_nonneg (abs_nonneg _) _
      nlinarith [h5, h7]
    have hmaji : Integrable (fun ω => 2 ^ δ * (|e 0 ω * W ((X 0 ω - x) / h n)| ^ δ
        + M ^ δ * |W ((X 0 ω - x) / h n)| ^ δ)) μ :=
      (hiW1.add (hiW2.const_mul (M ^ δ))).const_mul (2 ^ δ)
    have hRi : Integrable (fun ω => |R 0 ω| ^ δ) μ := by
      refine Integrable.mono hmaji ((hrp.comp (hRm 0).abs)).aestronglyMeasurable
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ δ *
          (|e 0 ω * W ((X 0 ω - x) / h n)| ^ δ + M ^ δ * |W ((X 0 ω - x) / h n)| ^ δ))]
      exact hbd ω
    have hstep : ∫ ω, |R 0 ω| ^ δ ∂μ
        ≤ 2 ^ δ * (∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ
            + M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ) := by
      have := integral_mono hRi hmaji hbd
      rwa [integral_const_mul, integral_add hiW1 (hiW2.const_mul (M ^ δ)),
        integral_const_mul] at this
    have hd1 := localized_delta_moment_le (X := X) (e := e) (hmeasX 0) hmp hp0 hpd hδ heLδ
      heδc hpb hWm hWb hW2 (x := x) (hn := h n) (hh0 n)
    have hd2 := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => |W v| ^ δ) hWam (fun v => Real.rpow_nonneg (abs_nonneg _) _) hWδ
      (x := x) (hh0 n)
    refine hstep.trans ?_
    have h2δ : (0 : ℝ) ≤ (2 : ℝ) ^ δ := Real.rpow_nonneg (by norm_num) _
    have hMδ : (0 : ℝ) ≤ M ^ δ := Real.rpow_nonneg hM0 _
    rw [hKρdef]
    have hA : ∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ
          + M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ
        ≤ (M * Cp * IWδ) * h n + M ^ δ * ((Cp * IWδ) * h n) := by
      have hb1 : ∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ ≤ (M * Cp * IWδ) * h n := hd1
      have hb2 : M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ
          ≤ M ^ δ * ((Cp * IWδ) * h n) := mul_le_mul_of_nonneg_left hd2 hMδ
      linarith
    calc (2 : ℝ) ^ δ * (∫ ω, |e 0 ω * W ((X 0 ω - x) / h n)| ^ δ ∂μ
            + M ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ)
        ≤ 2 ^ δ * ((M * Cp * IWδ) * h n + M ^ δ * ((Cp * IWδ) * h n)) :=
          mul_le_mul_of_nonneg_left hA h2δ
      _ = 2 ^ δ * (M + M ^ δ) * (Cp * IWδ) * h n := by ring
  -- Davydov
  have hnormδR : ∀ t : ℤ, (eLpNorm (R t) (ENNReal.ofReal δ) μ).toReal ≤ (Kρ * h n) ^ (1 / δ) := by
    intro t
    have hEq : eLpNorm (R t) (ENNReal.ofReal δ) μ = eLpNorm (R 0) (ENNReal.ofReal δ) μ :=
      eLpNorm_comp_pair_eq hmeasX hmeasE hstat t hFrm _
    rw [hEq]
    have hp1 : (ENNReal.ofReal δ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0
    have hform := hMemR0.eLpNorm_eq_integral_rpow_norm hp1 ENNReal.ofReal_ne_top
    have hb0 : (0 : ℝ) ≤ ∫ a, ‖R 0 a‖ ^ δ ∂μ :=
      integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
    rw [hform]
    simp only [ENNReal.toReal_ofReal hδ0.le]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hb0 _), ← one_div]
    have hnn : ∫ a, ‖R 0 a‖ ^ δ ∂μ ≤ Kρ * h n := by
      simpa only [Real.norm_eq_abs] using hdeltaR
    exact Real.rpow_le_rpow hb0 hnn (by positivity)
  have hlargeR : ∀ j : ℕ, 1 ≤ j →
      |Gr j| ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kρ * h n) ^ (2 / δ) := by
    intro j hj
    have hcov : cov[R 0, R (j : ℤ); μ] = Gr j := by
      rw [covariance_eq_sub (hMemR2 0) (hMemR2 (j : ℤ)), hmeanR 0, zero_mul, sub_zero]
      simp only [hGrdef]
      rfl
    rw [← hcov]
    refine (large_lag_covariance_bound' hmeasX hmeasE hδ hFrm j hj
      (hMemRt 0) (hMemRt (j : ℤ))).trans ?_
    have hα0 : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
      Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
    have hKh0 : (0 : ℝ) ≤ Kρ * h n := mul_nonneg hKρ0 (hh0 n).le
    have hsum2 : (1 / δ) + (1 / δ) = 2 / δ := by ring
    have hprod : (Kρ * h n) ^ (2 / δ) = (Kρ * h n) ^ (1 / δ) * (Kρ * h n) ^ (1 / δ) := by
      rw [← hsum2, Real.rpow_add' hKh0 (by rw [hsum2]; positivity)]
    rw [hprod, ← mul_assoc]
    gcongr
    · exact hnormδR 0
    · exact hnormδR (j : ℤ)
  -- the lag-sum split at `m_n`
  have hposL : (0 : ℝ) < h n * |Real.log (h n)| := mul_pos (hh0 n) hlogn
  have hm1 : 1 ≤ smallLagCut h n := Nat.ceil_pos.2 (by positivity)
  have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
  have hlagsum : ∑ j ∈ Finset.Ico 1 n, |Gr j|
      ≤ (smallLagCut h n : ℝ) * (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2)
        + 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
    have h1 : ∑ j ∈ Finset.Ico 1 n, |Gr j|
        ≤ ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gr j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (le_max_left _ _)) fun j _ _ => abs_nonneg _
    have h2 : (∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gr j|)
          + ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gr j|
        = ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gr j| :=
      Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)
    have h3 : ∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gr j|
        ≤ (smallLagCut h n : ℝ) *
          (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2) := by
      have hcard := Finset.sum_le_card_nsmul (Finset.Ico 1 (smallLagCut h n + 1))
        (fun j => |Gr j|) (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2)
        (fun j hj => hsmallR j (Finset.mem_Ico.1 hj).1)
      simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
    have h4 : ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gr j|
        ≤ 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
      have hKh : (0 : ℝ) ≤ (Kρ * h n) ^ (2 / δ) :=
        Real.rpow_nonneg (mul_nonneg hKρ0 (hh0 n).le) _
      have hmneg : (0 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) := Real.rpow_nonneg hmR.le _
      have hstep : ∀ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)),
          |Gr j| ≤ 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
            ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
        have hj1' : 1 ≤ j := by omega
        refine (hlargeR j hj1').trans ?_
        have hmj : (smallLagCut h n : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
          Real.rpow_le_rpow hmR.le (by exact_mod_cast (by omega : smallLagCut h n ≤ j)) hlam0.le
        have hαβ : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
          Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
        have hid : (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam = 1 := by
          rw [← Real.rpow_add hmR]; simp
        have hge1 : (1 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam := by
          calc (1 : ℝ) = (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam := hid.symm
            _ ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam :=
                mul_le_mul_of_nonneg_left hmj hmneg
        calc 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kρ * h n) ^ (2 / δ)
            = 8 * (Kρ * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * 1) := by ring
          _ ≤ 8 * (Kρ * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) *
                ((smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam)) := by gcongr
          _ = 8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
                ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmneg)
        (mul_nonneg (by norm_num) hKh)
      exact hα.sum_le_tsum _ fun i _ => hαnn i
    linarith
  have hmb : (smallLagCut h n : ℝ) ^ (-lam) ≤ (h n * |Real.log (h n)|) ^ lam := by
    have hmge : (h n * |Real.log (h n)|)⁻¹ ≤ (smallLagCut h n : ℝ) := Nat.le_ceil _
    have hmlam : (0 : ℝ) < (smallLagCut h n : ℝ) ^ lam := Real.rpow_pos_of_pos hmR _
    have hprod1 : (1 : ℝ) ≤ (h n * |Real.log (h n)|) * (smallLagCut h n : ℝ) := by
      have h0 := mul_le_mul_of_nonneg_left hmge hposL.le
      rwa [mul_inv_cancel₀ hposL.ne'] at h0
    have h5 : (1 : ℝ) ≤ ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam := by
      have h5' := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hprod1 hlam0.le
      rwa [Real.one_rpow] at h5'
    have h6 : ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam
        = (h n * |Real.log (h n)|) ^ lam * (smallLagCut h n : ℝ) ^ lam :=
      Real.mul_rpow hposL.le hmR.le
    rw [Real.rpow_neg hmR.le]
    refine le_of_mul_le_mul_right ?_ hmlam
    rw [inv_mul_cancel₀ hmlam.ne', ← h6]
    exact h5
  -- final assembly
  rw [hconv, hexp]
  have habs := abs_double_sum_subset_le (n := n) (Finset.range n) (Finset.Subset.refl _)
    (Cr) (Gr) hCG hCG'
  rw [Finset.card_range] at habs
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hhn : 0 < h n := hh0 n
  have hkey : ((n : ℝ) * h n)⁻¹ * (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t)
      ≤ (h n)⁻¹ * |Gr 0| + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gr j| := by
    calc ((n : ℝ) * h n)⁻¹ * (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t)
        ≤ ((n : ℝ) * h n)⁻¹ * |∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, Cr s t| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      _ ≤ ((n : ℝ) * h n)⁻¹ *
            ((n : ℝ) * (|Gr 0| + 2 * ∑ j ∈ Finset.Ico 1 n, |Gr j|)) :=
          mul_le_mul_of_nonneg_left habs (by positivity)
      _ = (h n)⁻¹ * |Gr 0| + 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gr j| := by
          field_simp
  refine hkey.trans ?_
  have hLt1 : (0 : ℝ) ≤ L ^ (2 - δ) := Real.rpow_nonneg hL0.le _
  have hLt2 : (0 : ℝ) ≤ L ^ (2 - 2 * δ) := Real.rpow_nonneg hL0.le _
  have hx1 : (0 : ℝ) ≤ 4 * B * IW ^ 2 * Eδ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) (sq_nonneg IW)) hEδ0
  have hx2 : (0 : ℝ) ≤ 4 * B * IW ^ 2 * M ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0) (sq_nonneg IW)) (sq_nonneg M)
  have hA1 : (h n)⁻¹ * |Gr 0|
      ≤ (2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ) := by
    have h1 : (h n)⁻¹ * |Gr 0|
        ≤ (h n)⁻¹ * ((2 * (M * Cp * IW2) * L ^ (2 - δ)
            + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ)) * h n) :=
      mul_le_mul_of_nonneg_left hdiagR (by positivity)
    have h2 : (h n)⁻¹ * ((2 * (M * Cp * IW2) * L ^ (2 - δ)
          + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ)) * h n)
        = 2 * (M * Cp * IW2) * L ^ (2 - δ) + 2 * (M ^ 2 * (Cp * IW2)) * L ^ (2 - 2 * δ) := by
      field_simp
    rw [h2] at h1
    refine h1.trans ?_
    nlinarith [mul_nonneg hx1 hLt1, mul_nonneg hx2 hLt2]
  have hA2 : 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gr j|
      ≤ ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
          + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
          * ((smallLagCut h n : ℝ) * h n)
        + 16 * SA * Kρ ^ (2 / δ) * (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
    have hmul := mul_le_mul_of_nonneg_left hlagsum (by positivity : (0 : ℝ) ≤ 2 * (h n)⁻¹)
    refine hmul.trans ?_
    rw [mul_add]
    have e1 : 2 * (h n)⁻¹ * ((smallLagCut h n : ℝ) *
          (B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * (IW * h n) ^ 2))
        = (2 * B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * IW ^ 2) *
          ((smallLagCut h n : ℝ) * h n) := by
      field_simp
    have hmh : (0 : ℝ) ≤ (smallLagCut h n : ℝ) * h n := by positivity
    have e1' : (2 * B * (2 * (L ^ (2 - δ) * Eδ) + 2 * c ^ 2) * IW ^ 2) *
          ((smallLagCut h n : ℝ) * h n)
        ≤ ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
          + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
          * ((smallLagCut h n : ℝ) * h n) := by
      refine mul_le_mul_of_nonneg_right ?_ hmh
      rw [hc2]
      have hy1 : (0 : ℝ) ≤ 2 * M * Cp * IW2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM0) hCp0) hIW20
      have hy2 : (0 : ℝ) ≤ 2 * M ^ 2 * Cp * IW2 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) hCp0) hIW20
      nlinarith [mul_nonneg hy1 hLt1, mul_nonneg hy2 hLt2]
    have hKrw : (Kρ * h n) ^ (2 / δ) = Kρ ^ (2 / δ) * (h n) ^ (2 / δ) :=
      Real.mul_rpow hKρ0 hhn.le
    have hLrw : (h n * |Real.log (h n)|) ^ lam
        = (h n) ^ lam * |Real.log (h n)| ^ lam := Real.mul_rpow hhn.le (abs_nonneg _)
    have hpow : (h n) ^ (2 / δ - 1 + lam) = (h n) ^ (2 / δ) * (h n)⁻¹ * (h n) ^ lam := by
      rw [show (2 / δ - 1 + lam) = (2 / δ) + (-1) + lam by ring,
        Real.rpow_add hhn, Real.rpow_add hhn, Real.rpow_neg hhn.le, Real.rpow_one]
    have hKh : (0 : ℝ) ≤ (Kρ * h n) ^ (2 / δ) := Real.rpow_nonneg (mul_nonneg hKρ0 hhn.le) _
    have e2 : 2 * (h n)⁻¹ * (8 * (Kρ * h n) ^ (2 / δ) *
          ((smallLagCut h n : ℝ) ^ (-lam) * SA))
        ≤ 16 * SA * Kρ ^ (2 / δ) * ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
      calc 2 * (h n)⁻¹ *
            (8 * (Kρ * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA))
          ≤ 2 * (h n)⁻¹ * (8 * (Kρ * h n) ^ (2 / δ) *
              ((h n * |Real.log (h n)|) ^ lam * SA)) := by gcongr
        _ = 16 * SA * Kρ ^ (2 / δ) *
              ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
            rw [hKrw, hLrw, hpow]; ring
    rw [e1]
    linarith
  have hfinal : ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
        * (1 + (smallLagCut h n : ℝ) * h n)
      = ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
        + ((2 * M * Cp * IW2 + 4 * B * IW ^ 2 * Eδ) * L ^ (2 - δ)
        + (2 * M ^ 2 * Cp * IW2 + 4 * B * IW ^ 2 * M ^ 2) * L ^ (2 - 2 * δ))
          * ((smallLagCut h n : ℝ) * h n) := by ring
  rw [hfinal]
  linarith
/-- **FY (2.82)–(2.83), truncation tail — FALSE AS FROZEN (verified), REPAIRED.**
Uniformly in `n`, the charFun of the localized sum is within `ε` of the charFun of its
truncated companion once the truncation level `L` is large. Proof:
`|e^{iuS} − e^{iuS^L}| ≤ |u| E|S − S^L|`, and the variance of `S − S^L` obeys the
ledger-(a) bound with the factor `E[e²1_{|e|>L}]`, which vanishes as `L → ∞` by
`δ`-moment uniform integrability (`heLδ`, `δ > 2`).

**FALSE AS FROZEN (verified).** The frozen hypotheses omitted (C1)'s stationarity and
*every* moment condition beyond time `0`: `heLδ` constrains `e 0` only, and there was no
`hstat`, `hce`, `hcv`, `hC2` or `hα`. Witness: `x = 0`, `X ≡ 0`, `W = 1_{[0,1]}` (so
`W((X_t − x)/h_n) ≡ W 0 = 1`, and `W` is bounded, integrable and square-integrable as
(C4) demands), `h_n = n^{−1/4}` (so `h_n → 0` and `n h_n³ = n^{1/4} → ∞`, as (C5)
demands), `e_0 = 0` (so `heLδ` holds for every `δ`) and `e_t = t·ζ` for `t ≥ 1` with
`ζ ~ N(0,1)`. Then `locSum = n^{−3/8}·(n(n+1)/2)·ζ`, whose charFun `→ 0`; whereas
`clamp_L(tζ) → L·sign ζ` pointwise as `t → ∞`, so
`locTruncSum = n^{5/8} L · sign ζ + o(1)` a.s. and its charFun is
`cos(u n^{5/8} L) + o(1)`. The steps of `n ↦ u n^{5/8} L` tend to `0` while the sequence
diverges, so its residues mod `2π` are dense: `|cos| ≥ 1/2` for infinitely many `n`, at
**every** fixed `L`. So `ε = 1/4` admits no `L` at all.

**Statement strengthening (documented).** The full (C1)–(C5) package that
`var_localized_sum` carries is threaded — in particular `hstat`, which is what upgrades
`heLδ` from time `0` to *every* `t` (through `memLp_comp_pair`) and so kills the witness —
together with the (C2) repair (the printed form: the recentred residual
`e_t − e^L_t = r_t − E(r_t|X_t)` again has its error factors stripped by the conditioning,
so the small-lag half needs weights other than `f = e_0 e_j`; see
`tendsto_smallBlock_variance`). The `L¹` route then applies: the diagonal is
`localized_trunc_residual_moment_le` (`O(L^{2−δ} h)`, so `O(L^{2−δ})` after the `h⁻¹`,
uniformly in `n` — this is the half that (C1)–(C5) as frozen already supported), and the
lag halves are the (C2)/Davydov pair of ledger (a) applied to the residual array.

Note that the uniformity in `n` is genuine work: the small-lag and large-lag totals carry
the factors `m_n h_n` and `h_n^{2/δ−1+λ}|log h_n|^λ`, which tend to `0` but must be
*bounded over all `n`*, and the large-lag δ-moment constant does **not** decay in `L`
(`heδc` gives only `E(|e_0|^δ|X_0) ≤ M`, with no tail refinement), so the large-`n` and
small-`n` ranges have to be separated: for `n ≥ N` the large-lag factor is itself small,
and for the finitely many `n < N` the crude `L¹` bound
`E|S_n − S^L_n| ≤ √(n/h_n) C_W · 2 L^{1−δ} M` closes at fixed `n`.

**PROVED (this wave)**, exactly along that route. The apparatus is the private block above:
`abs_sub_clamp_le` (`|z − clamp_L z| ≤ L^{1−δ}|z|^δ`) feeds `exists_truncErr_repr_decay`,
which upgrades `exists_truncErr_repr` to a recentring constant `c = M L^{1−δ}` that *decays*
in `L`; `residual_basic` collects, at **every** `n` and `L > 0`, the `L²` membership of
`S_n − S^L_n`, the a.e.-measurability of `S^L_n` (through the same representation, the
conditional expectation inside `truncErr` never being touched directly) and the crude `L¹`
bound; `residual_variance_bound` is the uniform-in-`n` `L²` bound, assembled exactly as
ledger (a) was — diagonal from `localized_trunc_residual_moment_le` and
`localized_weight_integral_le`, small lags from (C2) at `f(z) = q(z₁)q(z₂)` with
`q(y) = |y − clamp_L y| + c`, large lags from `large_lag_covariance_bound'` — and
`norm_charFun_map_sub_le'` is the `L¹` Lipschitz bound for characteristic functions.
The split at `N` is the one described above: `N` is where `m_n h_n ≤ 1` and the Davydov
remainder `C₃ h_n^{2/δ−1+λ}|log h_n|^λ` has fallen below `κ²/2`, with `κ = ε/(|u| + 1)`; the
`L`-side then only has to kill `2(C₁L^{2−δ} + C₂L^{2−2δ})`, and the finitely many `n < N`
are closed by `Filter.eventually_all_finset` over `Finset.range N`. -/
theorem charFun_locSum_sub_locTruncSum_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    -- (C1) USER-INPUT: joint strict stationarity (fdd form); FY (C1)
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ x : ℝ}
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT (authorized (C1) repair): σ² measurable; FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {M Cp : ℝ}
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (hpb : ∀ v, p v ≤ Cp)
    -- (C2) USER-INPUT: (C2) as printed (conditional joint density bounded); FY §2.6.4
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) (u : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ L in atTop, ∀ n : ℕ,
      ‖charFun (μ.map (locSum X e W x h n)) u
        - charFun (μ.map (locTruncSum X e μ W x h L n)) u‖ ≤ ε := by
  classical
  obtain ⟨B, hB0, hC2gen⟩ := hC2
  obtain ⟨C1, C2, C3, hC1n, hC2n, hC3n, hev⟩ :=
    residual_variance_bound hmeasX hmeasE hstat hδ hce heLδ hmp hp0 hpd heδc hpb hB0 hC2gen
      hlam hα hWm hWb hW1 hW2 hh0 hh
  intro ε hε
  set κ : ℝ := ε / (|u| + 1) with hκdef
  have hκ0 : (0 : ℝ) < κ := div_pos hε (by positivity)
  have hδ0 : (0 : ℝ) < δ := by linarith
  have h2δ : 2 / δ < 1 := by rw [div_lt_one hδ0]; linarith
  have hane : (0 : ℝ) < 2 / δ - 1 + lam := by linarith
  have hlam0 : (0 : ℝ) < lam := by linarith
  set Eδ : ℝ := ∫ ω, |e 0 ω| ^ δ ∂μ with hEδdef
  -- the large-`n` variance bound, with the two `n`-dependent factors absorbed
  have hev2 : ∀ᶠ n : ℕ in atTop, ∀ L : ℝ, 1 ≤ L →
      ∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ
        ≤ 2 * (C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ)) + κ ^ 2 / 2 := by
    have h1 : ∀ᶠ n : ℕ in atTop, (smallLagCut h n : ℝ) * h n ≤ 1 :=
      ((tendsto_smallLagCut_mul_bandwidth hh0 hh).eventually_lt_const
        (by norm_num : (0 : ℝ) < 1)).mono fun n hn => hn.le
    have h2 : ∀ᶠ n : ℕ in atTop,
        C3 * (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) ≤ κ ^ 2 / 2 := by
      have ht : Tendsto (fun n : ℕ => C3 * (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam))
          atTop (𝓝 0) := by
        simpa using (tendsto_rpow_mul_abs_log_rpow hh0 hh hane hlam0).const_mul C3
      exact (ht.eventually_lt_const (by positivity : (0 : ℝ) < κ ^ 2 / 2)).mono
        fun n hn => hn.le
    filter_upwards [hev, h1, h2] with n hn hn1 hn2 L hL
    refine (hn L hL).trans ?_
    have hLt1 : (0 : ℝ) ≤ C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ) := by
      have hL0 : (0 : ℝ) < L := by linarith
      have : (0 : ℝ) ≤ L ^ (2 - δ) := Real.rpow_nonneg hL0.le _
      have : (0 : ℝ) ≤ L ^ (2 - 2 * δ) := Real.rpow_nonneg hL0.le _
      positivity
    have hstep : (C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ)) *
        (1 + (smallLagCut h n : ℝ) * h n)
          ≤ (C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ)) * 2 :=
      mul_le_mul_of_nonneg_left (by linarith) hLt1
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev2
  -- the `L`-side of the large-`n` range
  have hLA : ∀ᶠ L : ℝ in atTop, 2 * (C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ)) ≤ κ ^ 2 / 2 := by
    have a1 : Tendsto (fun L : ℝ => L ^ (2 - δ)) atTop (𝓝 0) := by
      have hh1 := tendsto_rpow_neg_atTop (y := δ - 2) (by linarith)
      simpa [show -(δ - 2) = 2 - δ by ring] using hh1
    have a2 : Tendsto (fun L : ℝ => L ^ (2 - 2 * δ)) atTop (𝓝 0) := by
      have hh1 := tendsto_rpow_neg_atTop (y := 2 * δ - 2) (by linarith)
      simpa [show -(2 * δ - 2) = 2 - 2 * δ by ring] using hh1
    have t1 : Tendsto (fun L : ℝ => 2 * (C1 * L ^ (2 - δ) + C2 * L ^ (2 - 2 * δ)))
        atTop (𝓝 0) := by
      simpa using ((a1.const_mul C1).add (a2.const_mul C2)).const_mul 2
    exact (t1.eventually_lt_const (by positivity : (0 : ℝ) < κ ^ 2 / 2)).mono fun L hL => hL.le
  -- the finitely many small `n`, closed by the crude `L¹` bound
  have hsmall : ∀ᶠ L : ℝ in atTop, ∀ n ∈ Finset.range N,
      ∫ ω, |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω| ∂μ ≤ κ := by
    refine (Filter.eventually_all_finset _).2 fun n _ => ?_
    have a1 : Tendsto (fun L : ℝ => L ^ (1 - δ)) atTop (𝓝 0) := by
      have hh1 := tendsto_rpow_neg_atTop (y := δ - 1) (by linarith)
      simpa [show -(δ - 1) = 1 - δ by ring] using hh1
    have hK : Tendsto (fun L : ℝ => (Real.sqrt ((n : ℝ) * h n))⁻¹ * (n : ℝ) *
        (CW * (Eδ + M) * L ^ (1 - δ))) atTop (𝓝 0) := by
      simpa using (a1.const_mul (CW * (Eδ + M))).const_mul
        ((Real.sqrt ((n : ℝ) * h n))⁻¹ * (n : ℝ))
    filter_upwards [(hK.eventually_lt_const hκ0).mono fun L hL => hL.le,
      eventually_gt_atTop (0 : ℝ)] with L hL1 hL2
    exact ((residual_basic (x := x) hmeasX hmeasE hstat hδ hce heLδ heδc hWm hWb
      n hL2).2.2).trans hL1
  filter_upwards [hLA, hsmall, eventually_ge_atTop (1 : ℝ)] with L hLA' hLB hL1
  intro n
  have hL0 : (0 : ℝ) < L := by linarith
  obtain ⟨hMem2, hTaem, hL1bd⟩ := residual_basic (x := x) hmeasX hmeasE hstat hδ hce heLδ
    heδc hWm hWb n hL0
  have hSm : Measurable (locSum X e W x h n) := by
    unfold locSum
    exact (Finset.measurable_sum _ fun t _ => (hmeasE _).mul
      (hWm.comp (((hmeasX _).sub measurable_const).div measurable_const))).const_mul _
  have hint : Integrable
      (fun ω => |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω|) μ :=
    (hMem2.integrable (by norm_num)).abs
  have hkey : ∫ ω, |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω| ∂μ ≤ κ := by
    by_cases hn : N ≤ n
    · have hsq : ∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ
          ≤ κ ^ 2 := by
        have := hN n hn L hL1
        have hκ2 : κ ^ 2 / 2 + κ ^ 2 / 2 = κ ^ 2 := by ring
        linarith
      have hi2 : Integrable
          (fun ω => (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2) μ :=
        hMem2.integrable_sq
      have hptw : ∀ ω, |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω|
          ≤ (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 / (2 * κ) + κ / 2 := by
        intro ω
        set z : ℝ := locSum X e W x h n ω - locTruncSum X e μ W x h L n ω with hzdef
        have hnum : (0 : ℝ) ≤ z ^ 2 + κ ^ 2 - 2 * κ * |z| := by
          nlinarith [sq_nonneg (|z| - κ), sq_abs z]
        have hid : z ^ 2 / (2 * κ) + κ / 2 - |z| = (z ^ 2 + κ ^ 2 - 2 * κ * |z|) / (2 * κ) := by
          field_simp
        have hdiv : (0 : ℝ) ≤ (z ^ 2 + κ ^ 2 - 2 * κ * |z|) / (2 * κ) :=
          div_nonneg hnum (by linarith)
        linarith
      have hmono : ∫ ω, |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω| ∂μ
          ≤ ∫ ω, ((locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 / (2 * κ)
            + κ / 2) ∂μ :=
        integral_mono hint ((hi2.div_const _).add (integrable_const _)) hptw
      have heval : ∫ ω, ((locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 / (2 * κ)
            + κ / 2) ∂μ
          = (∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ) / (2 * κ)
            + κ / 2 := by
        rw [integral_add (hi2.div_const _) (integrable_const _), integral_div, integral_const]
        simp
      rw [heval] at hmono
      have hfrac : (∫ ω, (locSum X e W x h n ω - locTruncSum X e μ W x h L n ω) ^ 2 ∂μ)
          / (2 * κ) ≤ κ / 2 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
        nlinarith
      linarith
    · exact hLB n (Finset.mem_range.2 (Nat.lt_of_not_le hn))
  calc ‖charFun (μ.map (locSum X e W x h n)) u
        - charFun (μ.map (locTruncSum X e μ W x h L n)) u‖
      ≤ |u| * ∫ ω, |locSum X e W x h n ω - locTruncSum X e μ W x h L n ω| ∂μ :=
        norm_charFun_map_sub_le' hSm.aemeasurable hTaem hint u
    _ ≤ |u| * κ := by
        exact mul_le_mul_of_nonneg_left hkey (abs_nonneg u)
    _ ≤ ε := by
        rw [hκdef, mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < |u| + 1)]
        nlinarith [abs_nonneg u, hε.le]

/-! #### Ledger (b)+(d): the Bernstein-block core

The private apparatus behind `tendsto_charFun_locTruncSum`: the truncated conditional
variance `σ_L² = sL L − (mL L)²` and the (2.73) diagonal for the truncated errors; the
truncated analogue of ledger (a) over an arbitrary index family (`truncArray_core`,
`tendsto_truncArray_variance`); the shift lemma for the *pair* α-coefficient, which the
blocks need and which `pairAlphaCoeff` (anchored at `0`) does not give directly; the
big-block index apparatus and its numerology; the Volkonskii–Rozanov factorization; and the
row-CLT in product-of-charFuns form, obtained by transporting the block charFuns to an
independent surrogate on the infinite product of their laws. -/

/-- The truncated conditional variance is `σ_L² = sL L − (mL L)²`. -/
private theorem condExp_truncErr_sq [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L))
    {L : ℝ} (hL : 0 < L)
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω)) :
    μ[fun ω => truncErr X e μ L 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => sL L (X 0 ω) - mL L (X 0 ω) ^ 2 := by
  have hmLv' : μ[fun ω => clampAt L (e 0 ω) | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) := hmLv
  have hsLv' : μ[fun ω => clampAt L (e 0 ω) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => sL L (X 0 ω) := hsLv
  have hle : MeasurableSpace.comap (X 0) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hmeasX 0).comap_le
  have hmLmeas : Measurable[MeasurableSpace.comap (X 0) inferInstance]
      (fun ω => mL L (X 0 ω)) := (hmLm L).comp (Measurable.of_comap_le le_rfl)
  have hmLsm : StronglyMeasurable[MeasurableSpace.comap (X 0) inferInstance]
      (fun ω => mL L (X 0 ω)) := hmLmeas.stronglyMeasurable
  have hclm : Measurable (fun ω => clampAt L (e 0 ω)) :=
    (measurable_clampAt L).comp (hmeasE 0)
  have hclb : ∀ ω, |clampAt L (e 0 ω)| ≤ L := fun ω => abs_clampAt_le hL.le _
  have hci : Integrable (fun ω => clampAt L (e 0 ω)) μ :=
    (integrable_const L).mono' hclm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hclb ω)
  have hcsqi : Integrable (fun ω => clampAt L (e 0 ω) ^ 2) μ :=
    (integrable_const (L ^ 2)).mono' (hclm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [hclb ω, abs_nonneg (clampAt L (e 0 ω)), sq_abs (clampAt L (e 0 ω))])
  -- `mL L (X 0 ·)` is a.e. bounded by `L`: it is a version of a conditional expectation
  -- of something bounded by `L`
  have hmLb : ∀ᵐ ω ∂μ, |mL L (X 0 ω)| ≤ L := by
    have hup := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance) hci
      (integrable_const L) (Eventually.of_forall fun ω => le_trans (le_abs_self _) (hclb ω))
    have hlo := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance)
      (integrable_const (-L)) hci
      (Eventually.of_forall fun ω => by have := hclb ω; rw [abs_le] at this; exact this.1)
    rw [condExp_const hle L] at hup
    rw [condExp_const hle (-L)] at hlo
    filter_upwards [hup, hlo, hmLv'] with ω h1 h2 h3
    rw [h3] at h1 h2
    rw [abs_le]
    exact ⟨h2, h1⟩
  have hmixi : Integrable (fun ω => mL L (X 0 ω) * clampAt L (e 0 ω)) μ := by
    refine (integrable_const (L * L)).mono'
      (((hmLm L).comp (hmeasX 0)).mul hclm).aestronglyMeasurable ?_
    filter_upwards [hmLb] with ω hω
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hω (hclb ω) (abs_nonneg _) hL.le
  have hmsqi : Integrable (fun ω => mL L (X 0 ω) ^ 2) μ := by
    refine (integrable_const (L * L)).mono'
      (((hmLm L).comp (hmeasX 0)).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hmLb] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (mL L (X 0 ω)), sq_abs (mL L (X 0 ω))]
  -- expand the square
  have hrep : (fun ω => truncErr X e μ L 0 ω ^ 2)
      =ᵐ[μ] fun ω => clampAt L (e 0 ω) ^ 2
        - 2 * (mL L (X 0 ω) * clampAt L (e 0 ω)) + mL L (X 0 ω) ^ 2 := by
    filter_upwards [hmLv'] with ω hω
    simp only [truncErr]
    rw [show (μ[fun ω' => clampAt L (e 0 ω') |
      MeasurableSpace.comap (X 0) inferInstance]) ω = mL L (X 0 ω) from hω]
    ring
  have hcongr := condExp_congr_ae (m := MeasurableSpace.comap (X 0) inferInstance) hrep
  have h1 : μ[fun ω => clampAt L (e 0 ω) ^ 2
        - 2 * (mL L (X 0 ω) * clampAt L (e 0 ω)) |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => (μ[fun ω' => clampAt L (e 0 ω') ^ 2 |
          MeasurableSpace.comap (X 0) inferInstance]) ω
        - (μ[fun ω' => 2 * (mL L (X 0 ω') * clampAt L (e 0 ω')) |
          MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_sub hcsqi (hmixi.const_mul 2) _
  have h2 : μ[fun ω => (clampAt L (e 0 ω) ^ 2
          - 2 * (mL L (X 0 ω) * clampAt L (e 0 ω))) + mL L (X 0 ω) ^ 2 |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => (μ[fun ω' => clampAt L (e 0 ω') ^ 2
          - 2 * (mL L (X 0 ω') * clampAt L (e 0 ω')) |
          MeasurableSpace.comap (X 0) inferInstance]) ω
        + (μ[fun ω' => mL L (X 0 ω') ^ 2 |
          MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_add (hcsqi.sub (hmixi.const_mul 2)) hmsqi _
  have h3 : μ[fun ω => 2 * (mL L (X 0 ω) * clampAt L (e 0 ω)) |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => 2 * (μ[fun ω' => mL L (X 0 ω') * clampAt L (e 0 ω') |
        MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_smul (𝕜 := ℝ) 2 (fun ω => mL L (X 0 ω) * clampAt L (e 0 ω))
      (MeasurableSpace.comap (X 0) inferInstance)
  have hpull : μ[fun ω => mL L (X 0 ω) * clampAt L (e 0 ω) |
        MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) * (μ[fun ω' => clampAt L (e 0 ω') |
        MeasurableSpace.comap (X 0) inferInstance]) ω :=
    condExp_mul_of_stronglyMeasurable_left hmLsm hmixi hci
  have hself : μ[fun ω => mL L (X 0 ω) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) ^ 2 := by
    rw [condExp_of_stronglyMeasurable hle (hmLmeas.pow_const 2).stronglyMeasurable hmsqi]
  filter_upwards [hcongr, h1, h2, h3, hpull, hself, hmLv', hsLv'] with ω k0 k1 k2 k3 k4 k5 k6 k7
  rw [k0, k2, k1, k3, k4, k5, k6, k7]
  ring

/-- A version of `E(clamp_L e_0 | X_0)` is bounded by `L`. -/
private theorem ae_abs_mL_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (mL : ℝ → ℝ → ℝ) {L : ℝ} (hL : 0 < L)
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω)) :
    ∀ᵐ ω ∂μ, |mL L (X 0 ω)| ≤ L := by
  have hmLv' : μ[fun ω => clampAt L (e 0 ω) | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) := hmLv
  have hle : MeasurableSpace.comap (X 0) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hmeasX 0).comap_le
  have hclm : Measurable (fun ω => clampAt L (e 0 ω)) :=
    (measurable_clampAt L).comp (hmeasE 0)
  have hclb : ∀ ω, |clampAt L (e 0 ω)| ≤ L := fun ω => abs_clampAt_le hL.le _
  have hci : Integrable (fun ω => clampAt L (e 0 ω)) μ :=
    (integrable_const L).mono' hclm.aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hclb ω)
  have hup := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance) hci
    (integrable_const L) (Eventually.of_forall fun ω => le_trans (le_abs_self _) (hclb ω))
  have hlo := condExp_mono (m := MeasurableSpace.comap (X 0) inferInstance)
    (integrable_const (-L)) hci
    (Eventually.of_forall fun ω => by have := hclb ω; rw [abs_le] at this; exact this.1)
  rw [condExp_const hle L] at hup
  rw [condExp_const hle (-L)] at hlo
  filter_upwards [hup, hlo, hmLv'] with ω h1 h2 h3
  rw [h3] at h1 h2
  rw [abs_le]
  exact ⟨h2, h1⟩

/-- The truncated statistic is `clamp_L(e_0) − mL L (X_0)` a.e., hence bounded by `2L`. -/
private theorem truncErr_zero_repr [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (mL : ℝ → ℝ → ℝ) {L : ℝ}
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω)) :
    truncErr X e μ L 0 =ᵐ[μ] fun ω => clampAt L (e 0 ω) - mL L (X 0 ω) := by
  have hmLv' : μ[fun ω => clampAt L (e 0 ω) | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => mL L (X 0 ω) := hmLv
  filter_upwards [hmLv'] with ω hω
  simp only [truncErr]
  rw [show (μ[fun ω' => clampAt L (e 0 ω') |
    MeasurableSpace.comap (X 0) inferInstance]) ω = mL L (X 0 ω) from hω]

/-- **The truncated diagonal (2.73)-for-`e^L`.** -/
private theorem tendsto_truncDiag [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    {p : ℝ → ℝ} {x : ℝ}
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L)) (hsLm : ∀ L : ℝ, Measurable (sL L))
    {L : ℝ} (hL : 0 < L)
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hpc : ContinuousAt p x) (hpx : 0 < p x)
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (h n)⁻¹ *
        ∫ ω, truncErr X e μ L 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ) atTop
      (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)) := by
  have hle : MeasurableSpace.comap (X 0) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (hmeasX 0).comap_le
  have hmLb := ae_abs_mL_le hmeasX hmeasE mL hL hmLv
  have hrep := truncErr_zero_repr (X := X) (e := e) mL hmLv
  have hclm : Measurable (fun ω => clampAt L (e 0 ω)) :=
    (measurable_clampAt L).comp (hmeasE 0)
  have hclb : ∀ ω, |clampAt L (e 0 ω)| ≤ L := fun ω => abs_clampAt_le hL.le _
  -- `σ_L²` is continuous at `x`, because `σ_L²·p` is and `p x > 0`
  have hpne : ∀ᶠ v in 𝓝 x, 0 < p v := hpc.eventually (eventually_gt_nhds hpx)
  have hσc : ContinuousAt (fun v => sL L v - mL L v ^ 2) x := by
    refine ContinuousAt.congr (hσLc.div hpc hpx.ne') ?_
    filter_upwards [hpne] with v hv
    simp only [Pi.div_apply]
    field_simp
  -- integrability of the truncated square
  have htm : AEStronglyMeasurable (truncErr X e μ L 0) μ :=
    (hclm.sub ((hmLm L).comp (hmeasX 0))).aestronglyMeasurable.congr hrep.symm
  have he2 : Integrable (fun ω => truncErr X e μ L 0 ω ^ 2) μ := by
    refine (integrable_const ((2 * L) ^ 2)).mono' (htm.pow 2) ?_
    filter_upwards [hrep, hmLb] with ω h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), h1]
    have hb : |clampAt L (e 0 ω) - mL L (X 0 ω)| ≤ 2 * L := by
      have := hclb ω
      rw [abs_le] at this h2 ⊢
      constructor <;> linarith [this.1, this.2, h2.1, h2.2]
    nlinarith [abs_nonneg (clampAt L (e 0 ω) - mL L (X 0 ω)),
      sq_abs (clampAt L (e 0 ω) - mL L (X 0 ω)), hL.le]
  exact tendsto_localized_second_moment_debt (X := X) (e := fun _ => truncErr X e μ L 0)
    (hmeasX 0) ((hsLm L).sub ((hmLm L).pow_const 2)) hmp hp0 hpd
    (condExp_truncErr_sq hmeasX hmeasE mL sL hmLm hL hmLv hsLv) he2 hσc hpc hσLb hWm hWb hW2
    hh0 hh

/-- Sub-diagonal form of `abs_double_sum_subset_le`. -/
private theorem abs_double_sum_subset_sub_diag_le {n : ℕ} (I : Finset ℕ) (hI : I ⊆ Finset.range n)
    (c : ℕ → ℕ → ℝ) (g : ℕ → ℝ)
    (hc : ∀ s d : ℕ, c s (s + d) = g d) (hc' : ∀ s d : ℕ, c (s + d) s = g d) :
    |(∑ s ∈ I, ∑ t ∈ I, c s t) - (I.card : ℝ) * g 0|
      ≤ (I.card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := by
  classical
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ Finset.Ico 1 n, |g j| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hdiag : ∀ s : ℕ, c s s = g 0 := fun s => by simpa using hc s 0
  have key : ∀ s ∈ I, |(∑ t ∈ I, c s t) - g 0| ≤ 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by
    intro s hs
    have hsn : s < n := Finset.mem_range.1 (hI hs)
    have hsplit : (∑ t ∈ I, c s t) - g 0 = ∑ t ∈ I.erase s, c s t := by
      rw [← Finset.add_sum_erase _ _ hs, hdiag]; ring
    set A : Finset ℕ := I.filter (fun t => t < s) with hA
    set B : Finset ℕ := I.filter (fun t => s < t) with hB
    have hAB : I.erase s = A ∪ B := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_union, hA, hB, Finset.mem_filter]
      constructor
      · rintro ⟨hts, htI⟩; rcases lt_or_gt_of_ne hts with h | h
        · exact Or.inl ⟨htI, h⟩
        · exact Or.inr ⟨htI, h⟩
      · rintro (⟨htI, h⟩ | ⟨htI, h⟩) <;> exact ⟨by omega, htI⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro t htA htB
      simp only [hA, hB, Finset.mem_filter] at htA htB
      omega
    rw [hsplit]
    calc |∑ t ∈ I.erase s, c s t|
        ≤ ∑ t ∈ I.erase s, |c s t| := Finset.abs_sum_le_sum_abs _ _
      _ = (∑ t ∈ A, |c s t|) + ∑ t ∈ B, |c s t| := by
          rw [hAB, Finset.sum_union hdisj]
      _ ≤ (∑ j ∈ Finset.Ico 1 n, |g j|) + ∑ j ∈ Finset.Ico 1 n, |g j| := by
          gcongr
          · have hinj : ∀ t₁ ∈ A, ∀ t₂ ∈ A, s - t₁ = s - t₂ → t₁ = t₂ := by
              intro t₁ h₁ t₂ h₂ he
              simp only [hA, Finset.mem_filter] at h₁ h₂
              omega
            have himg : A.image (fun t => s - t) ⊆ Finset.Ico 1 n := by
              intro j hj
              simp only [Finset.mem_image, hA, Finset.mem_filter] at hj
              obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
              simp only [Finset.mem_Ico]
              omega
            have hval : ∀ t ∈ A, |c s t| = |g (s - t)| := by
              intro t ht
              simp only [hA, Finset.mem_filter] at ht
              have : t + (s - t) = s := by omega
              rw [← hc' t (s - t), this]
            have himgsum : ∑ j ∈ A.image (fun t => s - t), |g j| = ∑ t ∈ A, |g (s - t)| :=
              Finset.sum_image hinj
            rw [Finset.sum_congr rfl hval, ← himgsum]
            exact Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => abs_nonneg _
          · have hinj : ∀ t₁ ∈ B, ∀ t₂ ∈ B, t₁ - s = t₂ - s → t₁ = t₂ := by
              intro t₁ h₁ t₂ h₂ he
              simp only [hB, Finset.mem_filter] at h₁ h₂
              omega
            have himg : B.image (fun t => t - s) ⊆ Finset.Ico 1 n := by
              intro j hj
              simp only [Finset.mem_image, hB, Finset.mem_filter] at hj
              obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hj
              have : t < n := Finset.mem_range.1 (hI ht1)
              simp only [Finset.mem_Ico]
              omega
            have hval : ∀ t ∈ B, |c s t| = |g (t - s)| := by
              intro t ht
              simp only [hB, Finset.mem_filter] at ht
              have : s + (t - s) = t := by omega
              rw [← hc s (t - s), this]
            have himgsum : ∑ j ∈ B.image (fun t => t - s), |g j| = ∑ t ∈ B, |g (t - s)| :=
              Finset.sum_image hinj
            rw [Finset.sum_congr rfl hval, ← himgsum]
            exact Finset.sum_le_sum_of_subset_of_nonneg himg fun j _ _ => abs_nonneg _
      _ = 2 * ∑ j ∈ Finset.Ico 1 n, |g j| := by ring
  have hrw : (∑ s ∈ I, ∑ t ∈ I, c s t) - (I.card : ℝ) * g 0
      = ∑ s ∈ I, ((∑ t ∈ I, c s t) - g 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [hrw]
  calc |∑ s ∈ I, ((∑ t ∈ I, c s t) - g 0)|
      ≤ ∑ s ∈ I, |(∑ t ∈ I, c s t) - g 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ I, (2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := Finset.sum_le_sum key
    _ = (I.card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |g j|) := by
        rw [Finset.sum_const, nsmul_eq_mul]

set_option maxHeartbeats 2000000 in
set_option maxHeartbeats 2000000 in
private theorem truncArray_core [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hC2gen : ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L)
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L))
    (hsLm : ∀ L : ℝ, Measurable (sL L))
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hpc : ContinuousAt p x) (hpx : 0 < p x)
    :
    ∃ (Zt : ℕ → ℤ → Ω → ℝ) (G : ℕ → ℕ → ℝ),
      (∀ (n : ℕ) (t : ℤ), Measurable (Zt n t))
      ∧ (∀ (n : ℕ) (t : ℤ),
          (fun ω => truncErr X e μ L t ω * W ((X t ω - x) / h n)) =ᵐ[μ] Zt n t)
      ∧ (∀ (n : ℕ) (s t : ℤ), Integrable (fun ω => Zt n s ω * Zt n t ω) μ)
      ∧ (∀ n s d : ℕ, ∫ ω, Zt n ((s : ℤ) + 1) ω * Zt n (((s + d : ℕ) : ℤ) + 1) ω ∂μ = G n d)
      ∧ (∀ n s d : ℕ, ∫ ω, Zt n (((s + d : ℕ) : ℤ) + 1) ω * Zt n ((s : ℤ) + 1) ω ∂μ = G n d)
      ∧ Tendsto (fun n : ℕ => (h n)⁻¹ * G n 0) atTop
          (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2))
      ∧ Tendsto (fun n : ℕ => 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |G n j|) atTop (𝓝 0)
      ∧ (∀ (n : ℕ) (t : ℤ) (ω : Ω), |Zt n t ω| ≤ 2 * L * CW)
      ∧ (∀ (n : ℕ) (t : ℤ), ∫ ω, Zt n t ω ∂μ = 0) := by
  classical
  obtain ⟨mm, hmmM, hmmB, hmrep⟩ := exists_truncErr_repr hmeasX hmeasE hstat hL
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  have hCp0 : (0 : ℝ) ≤ Cp := le_trans (hp0 0) (hpb 0)
  have hrp : Measurable (fun y : ℝ => y ^ δ) := (Real.continuous_rpow_const hδ0.le).measurable
  -- `|W|^δ` is integrable
  have hWam : Measurable (fun v => |W v| ^ δ) := hrp.comp hWm.abs
  have hWδ : Integrable (fun v => |W v| ^ δ) MeasureTheory.volume := by
    refine Integrable.mono (hW2.const_mul (CW ^ (δ - 2))) hWam.aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    have hsplit : |W v| ^ δ = |W v| ^ (δ - 2) * |W v| ^ (2 : ℝ) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by intro hcon; linarith),
        show δ - 2 + 2 = δ from by ring]
    have h2 : |W v| ^ (2 : ℝ) = W v ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    have hle : |W v| ^ (δ - 2) ≤ CW ^ (δ - 2) :=
      Real.rpow_le_rpow (abs_nonneg _) (hWb v) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), hsplit, h2,
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ CW ^ (δ - 2) * W v ^ 2)]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  -- the pair function and the truncated array
  set F : ℕ → ℝ × ℝ → ℝ := fun n z => (clampAt L z.2 - mm z.1) * W ((z.1 - x) / h n) with hFdef
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    exact (((measurable_clampAt L).comp measurable_snd).sub (hmmM.comp measurable_fst)).mul
      (hWm.comp ((measurable_fst.sub measurable_const).div measurable_const))
  have hbase : ∀ z : ℝ × ℝ, |clampAt L z.2 - mm z.1| ≤ 2 * L := by
    intro z
    have ha := abs_le.1 (abs_clampAt_le hL.le z.2)
    have hb := abs_le.1 (hmmB z.1)
    rw [abs_le]; constructor <;> linarith
  have hFb : ∀ (n : ℕ) (z : ℝ × ℝ), |F n z| ≤ 2 * L * CW := by
    intro n z
    have h1 := hbase z
    have h2 := hWb ((z.1 - x) / h n)
    simp only [hFdef, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith [hL.le])
  set Z : ℕ → ℤ → Ω → ℝ := fun n t ω => F n (X t ω, e t ω) with hZdef
  have hZm : ∀ (n : ℕ) (t : ℤ), Measurable (Z n t) := fun n t =>
    (hFm n).comp ((hmeasX t).prodMk (hmeasE t))
  have hZb : ∀ (n : ℕ) (t : ℤ) (ω : Ω), |Z n t ω| ≤ 2 * L * CW := fun n t ω => hFb n _
  have hZmem : ∀ (n : ℕ) (t : ℤ) (q : ℝ≥0∞), MemLp (Z n t) q μ := fun n t q =>
    MemLp.of_bound (hZm n t).aestronglyMeasurable (2 * L * CW)
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hZb n t ω)
  have hint : ∀ (n : ℕ) (s t : ℤ), Integrable (fun ω => Z n s ω * Z n t ω) μ :=
    fun n s t => (hZmem n s 2).integrable_mul (hZmem n t 2)
  have hZrep : ∀ (n : ℕ) (t : ℤ),
      (fun ω => truncErr X e μ L t ω * W ((X t ω - x) / h n)) =ᵐ[μ] Z n t := by
    intro n t
    filter_upwards [hmrep t] with ω hω
    simp only [hZdef, hFdef, hω]
  -- each summand is centred
  have hclampint : ∀ t : ℤ, Integrable (fun ω => clampAt L (e t ω)) μ := by
    intro t
    refine (integrable_const L).mono'
      (((measurable_clampAt L).comp (hmeasE t)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]; exact abs_clampAt_le hL.le _
  have hcond : ∀ t : ℤ,
      μ[fun ω => clampAt L (e t ω) | MeasurableSpace.comap (X t) inferInstance]
        =ᵐ[μ] fun ω => mm (X t ω) := by
    intro t
    filter_upwards [hmrep t] with ω hω
    simp only [truncErr] at hω
    linarith
  have hmean0 : ∀ (n : ℕ) (t : ℤ), ∫ ω, Z n t ω ∂μ = 0 := by
    intro n t
    have hz := integral_bdd_comp_mul_eq_of_condExp (μ := μ) (hmeasX t) (hclampint t) (hcond t)
      (fun v => W ((v - x) / h n)) (by fun_prop) (C := CW) (fun v => hWb _)
    have hi1 : Integrable (fun ω => W ((X t ω - x) / h n) * clampAt L (e t ω)) μ :=
      (hclampint t).bdd_mul
        ((hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hWb _)
    have hi2 : Integrable (fun ω => W ((X t ω - x) / h n) * mm (X t ω)) μ := by
      refine (integrable_const (CW * L)).mono'
        (((hWm.comp (((hmeasX t).sub measurable_const).div measurable_const)).mul
          (hmmM.comp (hmeasX t))).aestronglyMeasurable) (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hWb _) (hmmB _) (abs_nonneg _) hCW0
    have hsplit : ∫ ω, Z n t ω ∂μ
        = ∫ ω, W ((X t ω - x) / h n) * clampAt L (e t ω) ∂μ
          - ∫ ω, W ((X t ω - x) / h n) * mm (X t ω) ∂μ := by
      rw [← integral_sub hi1 hi2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by
        simp only [hZdef, hFdef]; ring)
    rw [hsplit, hz, sub_self]
  -- the lag covariance array
  set Gz : ℕ → ℕ → ℝ := fun n d => ∫ ω, Z n 0 ω * Z n (d : ℤ) ω ∂μ with hGzdef
  set Cz : ℕ → ℕ → ℕ → ℝ := fun n s t => ∫ ω, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω ∂μ
    with hCzdef
  have hCG : ∀ n s d : ℕ, Cz n s (s + d) = Gz n d := by
    intro n s d
    have hidx : ((s + d : ℕ) : ℤ) + 1 = ((s : ℤ) + 1) + (d : ℤ) := by push_cast; ring
    have htr := integral_comp_pair2_eq hmeasX hmeasE hstat ((s : ℤ) + 1) d
      (G := fun z : (ℝ × ℝ) × (ℝ × ℝ) => F n z.1 * F n z.2)
      (((hFm n).comp measurable_fst).mul ((hFm n).comp measurable_snd))
    simp only [hCzdef, hGzdef, hZdef, hidx]
    exact htr
  have hCG' : ∀ n s d : ℕ, Cz n (s + d) s = Gz n d := by
    intro n s d
    have hsym : Cz n (s + d) s = Cz n s (s + d) := by
      simp only [hCzdef]
      exact integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [hsym, hCG]
  -- diagonal
  have hdiag : ∀ n : ℕ, |Gz n 0| ≤ (4 * L ^ 2) * ((Cp * ∫ v, W v ^ 2) * h n) := by
    intro n
    have hWsqm : Measurable (fun ω => W ((X 0 ω - x) / h n) ^ 2) :=
      (hWm.comp (((hmeasX 0).sub measurable_const).div measurable_const)).pow_const 2
    have hGeq : Gz n 0 = ∫ ω, (Z n 0 ω) ^ 2 ∂μ := by
      simp only [hGzdef, Nat.cast_zero]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hnn : 0 ≤ Gz n 0 := by
      rw [hGeq]; exact integral_nonneg fun ω => sq_nonneg _
    have hi2 : Integrable (fun ω => 4 * L ^ 2 * W ((X 0 ω - x) / h n) ^ 2) μ := by
      refine (integrable_const (4 * L ^ 2 * CW ^ 2)).mono'
        (hWsqm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hb := hWb ((X 0 ω - x) / h n)
      have habs := abs_nonneg (W ((X 0 ω - x) / h n))
      have hsq : W ((X 0 ω - x) / h n) ^ 2 ≤ CW ^ 2 := by
        nlinarith [sq_abs (W ((X 0 ω - x) / h n))]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    have hstep : ∫ ω, (Z n 0 ω) ^ 2 ∂μ ≤ (4 * L ^ 2) * ∫ ω, W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono (hZmem n 0 2).integrable_sq hi2 fun ω => ?_
      have hb := hbase (X 0 ω, e 0 ω)
      have hsq : (clampAt L (e 0 ω) - mm (X 0 ω)) ^ 2 ≤ 4 * L ^ 2 := by
        nlinarith [abs_nonneg (clampAt L (e 0 ω) - mm (X 0 ω)),
          sq_abs (clampAt L (e 0 ω) - mm (X 0 ω)), hL.le]
      simp only [hZdef, hFdef, mul_pow]
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    have hloc := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => W v ^ 2) (hWm.pow_const 2) (fun v => sq_nonneg _) hW2 (x := x) (hh0 n)
    rw [abs_of_nonneg hnn, hGeq]
    refine hstep.trans ?_
    exact mul_le_mul_of_nonneg_left hloc (by positivity)
  -- small lags
  have hIW0 : (0 : ℝ) ≤ ∫ v, |W v| := integral_nonneg fun v => abs_nonneg _
  have hsmall : ∀ (n j : ℕ), 1 ≤ j →
      |Gz n j| ≤ (4 * L ^ 2) * (B * ((∫ v, |W v|) * h n) ^ 2) := by
    intro n j hj
    have hjz : ((j : ℤ)) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hj
    have hgm : Measurable (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|) := by
      fun_prop
    have hg0 : ∀ z : ℝ × ℝ, 0 ≤ |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)| :=
      fun z => by positivity
    have hgXm : Measurable (fun ω => |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) :=
      hgm.comp ((hmeasX 0).prodMk (hmeasX (j : ℤ)))
    have hgi : Integrable
        (fun ω => 4 * L ^ 2 * (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|)) μ := by
      refine (integrable_const (4 * L ^ 2 * (CW * CW))).mono'
        (hgXm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := hWb ((X 0 ω - x) / h n)
      have h2 := hWb ((X (j : ℤ) ω - x) / h n)
      have h3 : |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ≤ CW * CW :=
        mul_le_mul h1 h2 (abs_nonneg _) hCW0
      nlinarith [sq_nonneg L]
    have hA : |Gz n j| ≤ (4 * L ^ 2) *
        ∫ ω, |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ∂μ := by
      have h0 := norm_integral_le_integral_norm (μ := μ) (fun ω => Z n 0 ω * Z n (j : ℤ) ω)
      simp only [Real.norm_eq_abs] at h0
      refine (le_trans h0 ?_)
      rw [← integral_const_mul]
      refine integral_mono (hint n 0 (j : ℤ)).abs hgi fun ω => ?_
      have hb0 := hbase (X 0 ω, e 0 ω)
      have hbj := hbase (X (j : ℤ) ω, e (j : ℤ) ω)
      simp only [hZdef, hFdef, abs_mul]
      have hL2 : (0 : ℝ) ≤ 2 * L := by linarith
      calc |clampAt L (e 0 ω) - mm (X 0 ω)| * |W ((X 0 ω - x) / h n)| *
              (|clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω)| * |W ((X (j : ℤ) ω - x) / h n)|)
          = (|clampAt L (e 0 ω) - mm (X 0 ω)| *
              |clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω)|) *
              (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by ring
        _ ≤ (4 * L ^ 2) * (|W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)|) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            nlinarith [abs_nonneg (clampAt L (e 0 ω) - mm (X 0 ω)),
              abs_nonneg (clampAt L (e (j : ℤ) ω) - mm (X (j : ℤ) ω))]
    have hC2 := hC2gen (j : ℤ) hjz (fun _ => (1 : ℝ)) measurable_const _ hgm hg0
    have hone : ∫ ω, |(fun _ : ℝ × ℝ => (1 : ℝ)) (e 0 ω, e (j : ℤ) ω)| ∂μ = 1 := by
      simp
    have hlhs : ∫ ω, |(fun _ : ℝ × ℝ => (1 : ℝ)) (e 0 ω, e (j : ℤ) ω)| *
          (fun z : ℝ × ℝ => |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|)
            (X 0 ω, X (j : ℤ) ω) ∂μ
        = ∫ ω, |W ((X 0 ω - x) / h n)| * |W ((X (j : ℤ) ω - x) / h n)| ∂μ := by
      simp
    rw [hone, hlhs, mul_one] at hC2
    have hprod : ∫ z : ℝ × ℝ, |W ((z.1 - x) / h n)| * |W ((z.2 - x) / h n)|
          ∂(MeasureTheory.volume.prod MeasureTheory.volume)
        = (∫ v, |W ((v - x) / h n)|) * ∫ w, |W ((w - x) / h n)| :=
      integral_prod_mul (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
        (f := fun v => |W ((v - x) / h n)|) (g := fun w => |W ((w - x) / h n)|)
    have honeW : ∫ v, |W ((v - x) / h n)| = h n * ∫ v, |W v| := by
      have := integral_dilate_translate (fun u => |W u|) (fun _ => (1 : ℝ)) x (hh0 n)
      simp only [mul_one] at this
      rw [this, ← mul_assoc, mul_inv_cancel₀ (hh0 n).ne', one_mul]
    rw [hprod, honeW] at hC2
    refine hA.trans ?_
    refine mul_le_mul_of_nonneg_left (hC2.trans (le_of_eq ?_)) (by positivity)
    ring
  -- the localized δ-th moment of the truncated array
  have hIWδ0 : (0 : ℝ) ≤ ∫ v, |W v| ^ δ :=
    integral_nonneg fun v => Real.rpow_nonneg (abs_nonneg _) _
  have hKzbd : ∀ n : ℕ,
      ∫ ω, |Z n 0 ω| ^ δ ∂μ ≤ ((2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ)) * h n := by
    intro n
    have hGm : Measurable (fun v => |W ((v - x) / h n)| ^ δ) :=
      hrp.comp ((hWm.comp ((measurable_id.sub measurable_const).div measurable_const)).abs)
    have hGXm : Measurable (fun ω => |W ((X 0 ω - x) / h n)| ^ δ) := hGm.comp (hmeasX 0)
    have hdom : ∀ ω, |Z n 0 ω| ^ δ ≤ (2 * L) ^ δ * |W ((X 0 ω - x) / h n)| ^ δ := by
      intro ω
      simp only [hZdef, hFdef, abs_mul]
      rw [Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      have h1 : |clampAt L (e 0 ω) - mm (X 0 ω)| ^ δ ≤ (2 * L) ^ δ :=
        Real.rpow_le_rpow (abs_nonneg _) (hbase (X 0 ω, e 0 ω)) hδ0.le
      exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (abs_nonneg _) _)
    have hi1 : Integrable (fun ω => |Z n 0 ω| ^ δ) μ := by
      refine (integrable_const ((2 * L * CW) ^ δ)).mono'
        ((hrp.comp (hZm n 0).abs)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hZb n 0 ω) hδ0.le
    have hi2 : Integrable (fun ω => (2 * L) ^ δ * |W ((X 0 ω - x) / h n)| ^ δ) μ := by
      refine (integrable_const ((2 * L) ^ δ * CW ^ δ)).mono'
        (hGXm.const_mul _).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (hWb _) hδ0.le) (Real.rpow_nonneg (by linarith) _)
    have hstep : ∫ ω, |Z n 0 ω| ^ δ ∂μ
        ≤ (2 * L) ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ := by
      rw [← integral_const_mul]
      exact integral_mono hi1 hi2 hdom
    have hloc := localized_weight_integral_le (X := X) (hmeasX 0) hmp hp0 hpd hpb
      (G := fun v => |W v| ^ δ) hWam (fun v => Real.rpow_nonneg (abs_nonneg _) _) hWδ
      (x := x) (hh0 n)
    refine hstep.trans ?_
    calc (2 * L) ^ δ * ∫ ω, |W ((X 0 ω - x) / h n)| ^ δ ∂μ
        ≤ (2 * L) ^ δ * ((Cp * ∫ v, |W v| ^ δ) * h n) :=
          mul_le_mul_of_nonneg_left hloc (Real.rpow_nonneg (by linarith) _)
      _ = ((2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ)) * h n := by ring
  -- the δ-norms of the truncated array, and Davydov
  set Kz : ℝ := (2 * L) ^ δ * (Cp * ∫ v, |W v| ^ δ) with hKzdef
  have hKz0 : (0 : ℝ) ≤ Kz :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (mul_nonneg hCp0 hIWδ0)
  have hnormδ : ∀ (n : ℕ) (t : ℤ),
      (eLpNorm (Z n t) (ENNReal.ofReal δ) μ).toReal ≤ (Kz * h n) ^ (1 / δ) := by
    intro n t
    have hEq : eLpNorm (Z n t) (ENNReal.ofReal δ) μ = eLpNorm (Z n 0) (ENNReal.ofReal δ) μ :=
      eLpNorm_comp_pair_eq hmeasX hmeasE hstat t (hFm n) _
    rw [hEq]
    have hp1 : (ENNReal.ofReal δ) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hδ0
    have hform := (hZmem n 0 (ENNReal.ofReal δ)).eLpNorm_eq_integral_rpow_norm hp1
      ENNReal.ofReal_ne_top
    have hb0 : (0 : ℝ) ≤ ∫ a, ‖Z n 0 a‖ ^ δ ∂μ :=
      integral_nonneg fun a => Real.rpow_nonneg (norm_nonneg _) _
    rw [hform]
    simp only [ENNReal.toReal_ofReal hδ0.le]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hb0 _), ← one_div]
    have hnn : ∫ a, ‖Z n 0 a‖ ^ δ ∂μ ≤ Kz * h n := by
      simpa only [Real.norm_eq_abs] using hKzbd n
    exact Real.rpow_le_rpow hb0 hnn (by positivity)
  have hlarge : ∀ (n j : ℕ), 1 ≤ j →
      |Gz n j| ≤ 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kz * h n) ^ (2 / δ) := by
    intro n j hj
    have hcov : cov[Z n 0, Z n (j : ℤ); μ] = Gz n j := by
      rw [covariance_eq_sub (hZmem n 0 2) (hZmem n (j : ℤ) 2), hmean0 n 0, zero_mul, sub_zero]
      simp only [hGzdef]
      rfl
    rw [← hcov]
    refine (large_lag_covariance_bound' hmeasX hmeasE hδ (hFm n) j hj
      (hZmem n 0 (ENNReal.ofReal δ)) (hZmem n (j : ℤ) (ENNReal.ofReal δ))).trans ?_
    have hα0 : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
      Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
    have hKh0 : (0 : ℝ) ≤ Kz * h n := mul_nonneg hKz0 (hh0 n).le
    have hsum2 : (1 / δ) + (1 / δ) = 2 / δ := by ring
    have hprod : (Kz * h n) ^ (2 / δ) = (Kz * h n) ^ (1 / δ) * (Kz * h n) ^ (1 / δ) := by
      rw [← hsum2, Real.rpow_add' hKh0 (by rw [hsum2]; positivity)]
    rw [hprod, ← mul_assoc]
    gcongr
    · exact hnormδ n 0
    · exact hnormδ n (j : ℤ)
  -- the lag sum, split at `m_n`
  set IW : ℝ := ∫ v, |W v| with hIWdef
  set SA : ℝ := ∑' t : ℕ, (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) with hSAdef
  have hαnn : ∀ t : ℕ, (0 : ℝ) ≤ (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ) :=
    fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _)
      (Real.rpow_nonneg (pairAlphaCoeff_nonneg X e t) _)
  have hSA0 : (0 : ℝ) ≤ SA := tsum_nonneg hαnn
  have hsplit : ∀ n : ℕ, 1 ≤ smallLagCut h n →
      ∑ j ∈ Finset.Ico 1 n, |Gz n j|
        ≤ (smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2))
          + 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
    intro n hm1
    have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
    have h1 : ∑ j ∈ Finset.Ico 1 n, |Gz n j|
        ≤ ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gz n j| :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl (le_max_left _ _)) fun j _ _ => abs_nonneg _
    have h2 : (∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gz n j|)
          + ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gz n j|
        = ∑ j ∈ Finset.Ico 1 (max n (smallLagCut h n + 1)), |Gz n j| :=
      Finset.sum_Ico_consecutive _ (by omega) (le_max_right _ _)
    have h3 : ∑ j ∈ Finset.Ico 1 (smallLagCut h n + 1), |Gz n j|
        ≤ (smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2)) := by
      have hcard := Finset.sum_le_card_nsmul (Finset.Ico 1 (smallLagCut h n + 1))
        (fun j => |Gz n j|) ((4 * L ^ 2) * (B * (IW * h n) ^ 2))
        (fun j hj => hsmall n j (Finset.mem_Ico.1 hj).1)
      simpa [Nat.card_Ico, nsmul_eq_mul] using hcard
    have h4 : ∑ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)), |Gz n j|
        ≤ 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA) := by
      have hKh : (0 : ℝ) ≤ (Kz * h n) ^ (2 / δ) :=
        Real.rpow_nonneg (mul_nonneg hKz0 (hh0 n).le) _
      have hmneg : (0 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) := Real.rpow_nonneg hmR.le _
      have hstep : ∀ j ∈ Finset.Ico (smallLagCut h n + 1) (max n (smallLagCut h n + 1)),
          |Gz n j| ≤ 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
            ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.1 hj
        have hj1' : 1 ≤ j := by omega
        refine (hlarge n j hj1').trans ?_
        have hmj : (smallLagCut h n : ℝ) ^ lam ≤ (j : ℝ) ^ lam :=
          Real.rpow_le_rpow hmR.le (by exact_mod_cast (by omega : smallLagCut h n ≤ j)) hlam0.le
        have hαβ : (0 : ℝ) ≤ pairAlphaCoeff X e μ j ^ (1 - 2 / δ) :=
          Real.rpow_nonneg (pairAlphaCoeff_nonneg X e j) _
        have hid : (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam = 1 := by
          rw [← Real.rpow_add hmR]; simp
        have hge1 : (1 : ℝ) ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam := by
          calc (1 : ℝ) = (smallLagCut h n : ℝ) ^ (-lam) * (smallLagCut h n : ℝ) ^ lam := hid.symm
            _ ≤ (smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam :=
                mul_le_mul_of_nonneg_left hmj hmneg
        calc 8 * pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * (Kz * h n) ^ (2 / δ)
            = 8 * (Kz * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) * 1) := by ring
          _ ≤ 8 * (Kz * h n) ^ (2 / δ) * (pairAlphaCoeff X e μ j ^ (1 - 2 / δ) *
                ((smallLagCut h n : ℝ) ^ (-lam) * (j : ℝ) ^ lam)) := by gcongr
          _ = 8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) *
                ((j : ℝ) ^ lam * pairAlphaCoeff X e μ j ^ (1 - 2 / δ))) := by ring
      refine (Finset.sum_le_sum hstep).trans ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmneg)
        (mul_nonneg (by norm_num) hKh)
      exact hα.sum_le_tsum _ fun i _ => hαnn i
    linarith
  have hRto0 : Tendsto (fun n : ℕ => 2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ =>
        (2 * (4 * L ^ 2) * B * IW ^ 2) * ((smallLagCut h n : ℝ) * h n)
          + (16 * SA * Kz ^ (2 / δ)) *
            (h n ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam)) atTop (𝓝 0) := by
      have t1 := (tendsto_smallLagCut_mul_bandwidth hh0 hh).const_mul
        (2 * (4 * L ^ 2) * B * IW ^ 2)
      have t2 := (tendsto_rpow_mul_abs_log_rpow hh0 hh (a := 2 / δ - 1 + lam)
        (by linarith) hlam0).const_mul (16 * SA * Kz ^ (2 / δ))
      simpa using t1.add t2
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards with n
      have hhn := hh0 n
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => abs_nonneg _)
    · filter_upwards [(tendsto_abs_log_atTop hh0 hh).eventually_gt_atTop 0] with n hLn
      have hhn : 0 < h n := hh0 n
      have hposL : (0 : ℝ) < h n * |Real.log (h n)| := by positivity
      have hm1 : 1 ≤ smallLagCut h n := Nat.ceil_pos.2 (by positivity)
      have hmR : (0 : ℝ) < (smallLagCut h n : ℝ) := by exact_mod_cast hm1
      have hmge : (h n * |Real.log (h n)|)⁻¹ ≤ (smallLagCut h n : ℝ) := Nat.le_ceil _
      have hmlam : (0 : ℝ) < (smallLagCut h n : ℝ) ^ lam := Real.rpow_pos_of_pos hmR _
      have hmb : (smallLagCut h n : ℝ) ^ (-lam) ≤ (h n * |Real.log (h n)|) ^ lam := by
        have hprod1 : (1 : ℝ) ≤ (h n * |Real.log (h n)|) * (smallLagCut h n : ℝ) := by
          have h0 := mul_le_mul_of_nonneg_left hmge hposL.le
          rwa [mul_inv_cancel₀ hposL.ne'] at h0
        have h5 : (1 : ℝ) ≤ ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam := by
          have h5' := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hprod1 hlam0.le
          rwa [Real.one_rpow] at h5'
        have h6 : ((h n * |Real.log (h n)|) * (smallLagCut h n : ℝ)) ^ lam
            = (h n * |Real.log (h n)|) ^ lam * (smallLagCut h n : ℝ) ^ lam :=
          Real.mul_rpow hposL.le hmR.le
        rw [Real.rpow_neg hmR.le]
        refine le_of_mul_le_mul_right ?_ hmlam
        rw [inv_mul_cancel₀ hmlam.ne', ← h6]
        exact h5
      have hS := hsplit n hm1
      refine (mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ 2 * (h n)⁻¹)).trans ?_
      rw [mul_add]
      have e1 : 2 * (h n)⁻¹ * ((smallLagCut h n : ℝ) * ((4 * L ^ 2) * (B * (IW * h n) ^ 2)))
          = (2 * (4 * L ^ 2) * B * IW ^ 2) * ((smallLagCut h n : ℝ) * h n) := by
        field_simp
      have hKrw : (Kz * h n) ^ (2 / δ) = Kz ^ (2 / δ) * (h n) ^ (2 / δ) :=
        Real.mul_rpow hKz0 hhn.le
      have hLrw : (h n * |Real.log (h n)|) ^ lam
          = (h n) ^ lam * |Real.log (h n)| ^ lam := Real.mul_rpow hhn.le (abs_nonneg _)
      have hpow : (h n) ^ (2 / δ - 1 + lam) = (h n) ^ (2 / δ) * (h n)⁻¹ * (h n) ^ lam := by
        rw [show (2 / δ - 1 + lam) = (2 / δ) + (-1) + lam by ring,
          Real.rpow_add hhn, Real.rpow_add hhn, Real.rpow_neg hhn.le, Real.rpow_one]
      have hKh : (0 : ℝ) ≤ (Kz * h n) ^ (2 / δ) := Real.rpow_nonneg (mul_nonneg hKz0 hhn.le) _
      have e2 : 2 * (h n)⁻¹ * (8 * (Kz * h n) ^ (2 / δ) *
            ((smallLagCut h n : ℝ) ^ (-lam) * SA))
          ≤ (16 * SA * Kz ^ (2 / δ)) *
            ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
        calc 2 * (h n)⁻¹ *
              (8 * (Kz * h n) ^ (2 / δ) * ((smallLagCut h n : ℝ) ^ (-lam) * SA))
            ≤ 2 * (h n)⁻¹ * (8 * (Kz * h n) ^ (2 / δ) *
                ((h n * |Real.log (h n)|) ^ lam * SA)) := by gcongr
          _ = (16 * SA * Kz ^ (2 / δ)) *
                ((h n) ^ (2 / δ - 1 + lam) * |Real.log (h n)| ^ lam) := by
              rw [hKrw, hLrw, hpow]; ring
      linarith
  -- the diagonal, as the truncated second moment
  have hG0 : ∀ n : ℕ,
      Gz n 0 = ∫ ω, truncErr X e μ L 0 ω ^ 2 * W ((X 0 ω - x) / h n) ^ 2 ∂μ := by
    intro n
    simp only [hGzdef, Nat.cast_zero]
    refine integral_congr_ae ?_
    filter_upwards [hZrep n 0] with ω hω
    rw [← hω]
    ring
  have hdiaglim : Tendsto (fun n : ℕ => (h n)⁻¹ * Gz n 0) atTop
      (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)) := by
    simpa only [hG0] using tendsto_truncDiag hmeasX hmeasE hmp hp0 hpd mL sL hmLm hsLm hL
      hmLv hsLv hσLc hσLb hpc hpx hWm hWb hW2 hh0 hh
  refine ⟨Z, Gz, hZm, hZrep, hint, ?_, ?_, hdiaglim, hRto0, fun n t ω => hZb n t ω, hmean0⟩
  · intro n s d
    have := hCG n s d
    simpa only [hCzdef] using this
  · intro n s d
    have := hCG' n s d
    simpa only [hCzdef] using this

set_option maxHeartbeats 2000000 in
private theorem tendsto_truncArray_variance [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hC2gen : ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L)
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L))
    (hsLm : ∀ L : ℝ, Measurable (sL L))
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hpc : ContinuousAt p x) (hpx : 0 < p x)
    (I : ℕ → Finset ℕ) (hIsub : ∀ n, I n ⊆ Finset.range n) {a : ℝ}
    (hIcard : Tendsto (fun n : ℕ => ((I n).card : ℝ) / (n : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ) atTop
      (𝓝 (a * ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)))  := by
  obtain ⟨Z, Gz, hZm, hZrep, hint, hCG, hCG', hdiaglim, hRto0, hZb, hmean0⟩ :=
    truncArray_core hmeasX hmeasE hstat hδ hmp hp0 hpd hpb hB0 hC2gen hlam hα hWm hWb hW1 hW2
      hh0 hh hL mL sL hmLm hsLm hmLv hsLv hσLc hσLb hpc hpx
  set Cz : ℕ → ℕ → ℕ → ℝ := fun n s t => ∫ ω, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω ∂μ
    with hCzdef
  have hCGc : ∀ n s d : ℕ, Cz n s (s + d) = Gz n d := fun n s d => hCG n s d
  have hCGc' : ∀ n s d : ℕ, Cz n (s + d) s = Gz n d := fun n s d => hCG' n s d
  have hexp : ∀ n : ℕ, ∫ ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ
      = ∑ s ∈ I n, ∑ t ∈ I n, Cz n s t := by
    intro n
    have hsq : ∀ ω : Ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2
        = ∑ s ∈ I n, ∑ t ∈ I n, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp only [hsq, hCzdef]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hint n _ _))]
    exact Finset.sum_congr rfl fun s _ => integral_finset_sum _ (fun t _ => hint n _ _)
  have hsumrep : ∀ n : ℕ,
      ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
        = ∫ ω, (∑ t ∈ I n, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    intro n
    refine integral_congr_ae ?_
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ I n,
        truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
          = Z n ((t : ℤ) + 1) ω :=
      (Filter.eventually_all_finset (I n)).2 (fun t _ => hZrep n ((t : ℤ) + 1))
    filter_upwards [hall] with ω hω
    rw [Finset.sum_congr rfl hω]
  have hmain : Tendsto (fun n : ℕ => (((I n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0))
      atTop (𝓝 (a * ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2))) := hIcard.mul hdiaglim
  have herr : Tendsto (fun n : ℕ => ((n : ℝ) * h n)⁻¹ * (∑ s ∈ I n, ∑ t ∈ I n, Cz n s t)
      - (((I n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => (((I n).card : ℝ) / (n : ℝ)) *
        (2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)) atTop (𝓝 0) := by
      simpa using hIcard.mul hRto0
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hhn : 0 < h n := hh0 n
    have habs := abs_double_sum_subset_sub_diag_le (I n) (hIsub n) (Cz n) (Gz n)
      (hCGc n) (hCGc' n)
    have hid : ((n : ℝ) * h n)⁻¹ * (∑ s ∈ I n, ∑ t ∈ I n, Cz n s t)
        - (((I n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0)
        = ((n : ℝ) * h n)⁻¹ *
          ((∑ s ∈ I n, ∑ t ∈ I n, Cz n s t) - ((I n).card : ℝ) * Gz n 0) := by
      field_simp
    have hid2 : ((n : ℝ) * h n)⁻¹ *
        (((I n).card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |Gz n j|))
        = (((I n).card : ℝ) / (n : ℝ)) *
          (2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) := by
      field_simp
    rw [Real.norm_eq_abs, hid, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) * h n)⁻¹), ← hid2]
    exact mul_le_mul_of_nonneg_left habs (by positivity)
  have hconv : ∀ n : ℕ, ((n : ℝ) * h n)⁻¹ *
      ∫ ω, (∑ t ∈ I n, truncErr X e μ L ((t : ℤ) + 1) ω *
        W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
      = ((n : ℝ) * h n)⁻¹ * (∑ s ∈ I n, ∑ t ∈ I n, Cz n s t) := by
    intro n; rw [hsumrep n, hexp n]
  simp only [hconv]
  have hsum := hmain.add herr
  rw [add_zero] at hsum
  exact hsum.congr fun n => by ring


/-- A Borel isomorphism `ℝ × ℝ ≃ᵐ ℝ`, used to encode the pair series as a real series so
that the shift lemma of `Mixing/Relations.lean` applies to it. -/
private noncomputable def pairCode : (ℝ × ℝ) ≃ᵐ ℝ :=
  PolishSpace.measurableEquivOfNotCountable
    (Uncountable.not_countable) (Uncountable.not_countable)

/-- The coded pair series generates the same one-time σ-algebras as the pair. -/
private theorem comap_pairCode {X e : ℤ → Ω → ℝ} (t : ℤ) :
    MeasurableSpace.comap (fun ω => pairCode (X t ω, e t ω)) inferInstance
      = MeasurableSpace.comap (X t) inferInstance ⊔
        MeasurableSpace.comap (e t) inferInstance := by
  have h1 : MeasurableSpace.comap (fun ω => pairCode (X t ω, e t ω))
      (inferInstance : MeasurableSpace ℝ)
      = MeasurableSpace.comap (fun ω => (X t ω, e t ω))
        (MeasurableSpace.comap pairCode (inferInstance : MeasurableSpace ℝ)) :=
    (MeasurableSpace.comap_comp).symm
  have h2 : MeasurableSpace.comap (pairCode : ℝ × ℝ → ℝ) (inferInstance : MeasurableSpace ℝ)
      = (inferInstance : MeasurableSpace (ℝ × ℝ)) := by
    refine le_antisymm pairCode.measurable.comap_le ?_
    intro s hs
    refine ⟨pairCode.symm ⁻¹' s, pairCode.symm.measurable hs, ?_⟩
    ext z
    simp
  rw [h1, h2]
  show MeasurableSpace.comap (fun ω => (X t ω, e t ω))
      (MeasurableSpace.comap Prod.fst inferInstance ⊔
        MeasurableSpace.comap Prod.snd inferInstance) = _
  rw [MeasurableSpace.comap_sup, MeasurableSpace.comap_comp, MeasurableSpace.comap_comp]
  rfl

/-- Under fdd stationarity of the pair, arbitrary finite tuples of the pair are
shift-invariant in law. -/
private theorem map_tuple_shift {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (n : ℕ) (t : Fin n → ℤ) (a : ℤ) :
    μ.map (fun ω (i : Fin n) => (X (t i + a) ω, e (t i + a) ω))
      = μ.map (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω)) := by
  classical
  have hwin : ∀ (m : ℕ) (b : ℤ),
      Measurable (fun ω (i : Fin m) => (X (b + (i : ℕ)) ω, e (b + (i : ℕ)) ω)) :=
    fun m b => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  set M : ℕ := Finset.univ.sup (fun i : Fin n => (t i).natAbs) with hM
  have hMle : ∀ i : Fin n, (t i).natAbs ≤ M := fun i =>
    Finset.le_sup (f := fun i : Fin n => (t i).natAbs) (Finset.mem_univ i)
  have hj : ∀ i : Fin n, (t i + (M : ℤ)).toNat < 2 * M + 1 := by
    intro i; have := hMle i; omega
  set j : Fin n → Fin (2 * M + 1) := fun i => ⟨(t i + (M : ℤ)).toNat, hj i⟩ with hjdef
  set proj : (Fin (2 * M + 1) → ℝ × ℝ) → (Fin n → ℝ × ℝ) := fun z i => z (j i) with hprojdef
  have hprojm : Measurable proj := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hcomp : ∀ b : ℤ, (fun ω (i : Fin n) => (X (t i + b) ω, e (t i + b) ω))
      = proj ∘ (fun ω (i : Fin (2 * M + 1)) =>
          (X ((b - (M : ℤ)) + (i : ℕ)) ω, e ((b - (M : ℤ)) + (i : ℕ)) ω)) := by
    intro b
    funext ω i
    have hval : (b - (M : ℤ)) + (((j i : Fin (2 * M + 1)) : ℕ) : ℤ) = t i + b := by
      simp only [hjdef]
      have := hMle i
      omega
    simp only [hprojdef, Function.comp_apply, hval]
  have h0 : (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω))
      = (fun ω (i : Fin n) => (X (t i + 0) ω, e (t i + 0) ω)) := by simp
  rw [hcomp a, h0, hcomp 0,
    ← Measure.map_map hprojm (hwin (2 * M + 1) (a - (M : ℤ))),
    ← Measure.map_map hprojm (hwin (2 * M + 1) ((0 : ℤ) - (M : ℤ))),
    hstat (2 * M + 1) (a - (M : ℤ)), hstat (2 * M + 1) ((0 : ℤ) - (M : ℤ))]

/-- The coded pair series is strictly stationary. -/
private theorem isStrictlyStationary_pairCode {X e : ℤ → Ω → ℝ}
    (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω))) :
    IsStrictlyStationary (fun t ω => pairCode (X t ω, e t ω)) μ := by
  intro n t k
  have hm : ∀ b : ℤ, Measurable (fun ω (i : Fin n) => (X (t i + b) ω, e (t i + b) ω)) :=
    fun b => measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hm0 : Measurable (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω)) :=
    measurable_pi_lambda _ fun i => (hmeasX _).prodMk (hmeasE _)
  have hcode : Measurable (fun (z : Fin n → ℝ × ℝ) (i : Fin n) => pairCode (z i)) :=
    measurable_pi_lambda _ fun i => pairCode.measurable.comp (measurable_pi_apply i)
  have e1 : (fun ω (i : Fin n) => pairCode (X (t i + k) ω, e (t i + k) ω))
      = (fun (z : Fin n → ℝ × ℝ) (i : Fin n) => pairCode (z i))
        ∘ (fun ω (i : Fin n) => (X (t i + k) ω, e (t i + k) ω)) := rfl
  have e2 : (fun ω (i : Fin n) => pairCode (X (t i) ω, e (t i) ω))
      = (fun (z : Fin n → ℝ × ℝ) (i : Fin n) => pairCode (z i))
        ∘ (fun ω (i : Fin n) => (X (t i) ω, e (t i) ω)) := rfl
  show μ.map (fun ω (i : Fin n) => pairCode (X (t i + k) ω, e (t i + k) ω))
      = μ.map (fun ω (i : Fin n) => pairCode (X (t i) ω, e (t i) ω))
  rw [e1, e2, ← Measure.map_map hcode (hm k), ← Measure.map_map hcode hm0,
    map_tuple_shift hmeasX hmeasE hstat n t k]

/-- **Shift lemma for the pair series.** Under fdd stationarity the α-coefficient between
the pair past up to `k` and the pair future from `k + d` is `pairAlphaCoeff X e μ d`. -/
private theorem pairAlphaCoeff_shift [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    (k : ℤ) (d : ℕ) :
    alphaMixCoeff μ
        (⨆ s ∈ Set.Iic k, MeasurableSpace.comap (X s) inferInstance ⊔
          MeasurableSpace.comap (e s) inferInstance)
        (⨆ s ∈ Set.Ici (k + (d : ℤ)), MeasurableSpace.comap (X s) inferInstance ⊔
          MeasurableSpace.comap (e s) inferInstance)
      = pairAlphaCoeff X e μ d := by
  have hZm : ∀ t : ℤ, Measurable (fun ω => pairCode (X t ω, e t ω)) := fun t =>
    pairCode.measurable.comp ((hmeasX t).prodMk (hmeasE t))
  have hLE : ∀ c : ℤ, sigmaLE (fun t ω => pairCode (X t ω, e t ω)) c
      = ⨆ s ∈ Set.Iic c, MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance := fun c =>
    iSup_congr fun s => iSup_congr fun _ => comap_pairCode s
  have hGE : ∀ c : ℤ, sigmaGE (fun t ω => pairCode (X t ω, e t ω)) c
      = ⨆ s ∈ Set.Ici c, MeasurableSpace.comap (X s) inferInstance ⊔
        MeasurableSpace.comap (e s) inferInstance := fun c =>
    iSup_congr fun s => iSup_congr fun _ => comap_pairCode s
  have hsh := (isStrictlyStationary_pairCode hmeasX hmeasE hstat).alphaMixCoeff_shift hZm k d
  rw [hLE k, hGE (k + (d : ℤ))] at hsh
  rw [hsh]
  show alphaMixCoeff μ (sigmaLE (fun t ω => pairCode (X t ω, e t ω)) 0)
      (sigmaGE (fun t ω => pairCode (X t ω, e t ω)) (d : ℤ)) = _
  rw [hLE 0, hGE (d : ℤ)]
  rfl



/-- `l_n / n → 0`. -/
private theorem tendsto_bigBlockLen_div {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (bigBlockLen h n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹ + ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp
        (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
    have t2 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using t1.add t2
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with n
    positivity
  have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 3, hh.eventually_le_const (by norm_num : (0:ℝ) < 1),
    hlogtop.eventually_ge_atTop 1] with n hn3 hh1 hΛ1
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (3 : ℕ) ≤ n := hn3
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num) this
  have hsq : Real.sqrt ((n : ℝ) * h n) ≤ Real.sqrt (n : ℝ) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [(hh0 n).le, hn0.le]
  have hle : (bigBlockLen h n : ℝ) ≤ Real.sqrt ((n : ℝ) * h n) / Real.log n + 1 := by
    rw [bigBlockLen]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  rw [div_le_iff₀ hn0]
  have hstep : Real.sqrt ((n : ℝ) * h n) / Real.log n ≤ Real.sqrt (n : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.sqrt_nonneg (n : ℝ), hsq]
  have hsq0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hid : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt hn0.le
  calc (bigBlockLen h n : ℝ) ≤ Real.sqrt ((n : ℝ) * h n) / Real.log n + 1 := hle
    _ ≤ Real.sqrt (n : ℝ) + 1 := by linarith
    _ = ((Real.sqrt (n : ℝ))⁻¹ + ((n : ℝ))⁻¹) * (n : ℝ) := by
        field_simp
        nlinarith [hid]

/-- `s_n / n → 0`. -/
private theorem tendsto_smallBlockLen_div {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam) :
    Tendsto (fun n : ℕ => (smallBlockLen h δ lam n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hβ0 : (0 : ℝ) < 1 - 2 / δ := by rw [sub_pos, div_lt_one hδ0]; linarith
  have hlam0 : (0 : ℝ) < lam := lt_trans hβ0 hlam
  set θ : ℝ := (1 - 2 / δ) / (lam + 1) with hθdef
  have hL1 : (0 : ℝ) < lam + 1 := by linarith
  have hθ0 : 0 < θ := div_pos hβ0 hL1
  have hθ1 : θ < 1 / 2 := by
    rw [hθdef, div_lt_iff₀ hL1]
    have : (1 : ℝ) - 2 / δ < 1 := by
      have : (0 : ℝ) < 2 / δ := by positivity
      linarith
    linarith
  have hmaj0 : Tendsto (fun n : ℕ =>
      Real.log n ^ θ / (n : ℝ) ^ ((1 - 2 * θ) / 3) + ((n : ℝ))⁻¹) atTop (𝓝 0) := by
    have t1 := tendsto_log_rpow_div_rpow_atTop (α := (1 - 2 * θ) / 3) (β := θ)
      (by linarith) hθ0
    have t2 : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using t1.add t2
  refine squeeze_zero' ?_ ?_ hmaj0
  · filter_upwards with n
    positivity
  filter_upwards [eventually_ge_atTop 2, hnh.eventually_ge_atTop 1,
    hh.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn2 hPH3 hh1
  set P : ℝ := (n : ℝ) with hPdef
  set H : ℝ := h n with hHdef
  set Λ : ℝ := Real.log n with hΛdef
  have hP1 : (1 : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast Nat.one_le_of_lt hn2
  have hP0 : (0 : ℝ) < P := by linarith
  have hH0 : (0 : ℝ) < H := hh0 n
  have hΛ0 : (0 : ℝ) < Λ := Real.log_pos (by exact_mod_cast hn2)
  have hPH3' : (0 : ℝ) < P * H ^ 3 := by positivity
  have hlogP3 : Real.log (P * H ^ 3) = Real.log P + 3 * Real.log H := by
    rw [Real.log_mul hP0.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hlogPH : Real.log (P * H) = Real.log P + Real.log H := Real.log_mul hP0.ne' hH0.ne'
  have hlogPdH : Real.log (P / H) = Real.log P - Real.log H := Real.log_div hP0.ne' hH0.ne'
  have hone3 : (1 : ℝ) ≤ (P * H ^ 3) ^ ((1 + θ) / 6) := by
    have := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hPH3 (by linarith : (0:ℝ) ≤ (1 + θ) / 6)
    rwa [Real.one_rpow] at this
  have hfact1 : (Real.sqrt (P / H)) ^ θ * P ^ ((1 - 2 * θ) / 3) * (P * H ^ 3) ^ ((1 + θ) / 6)
      = Real.sqrt (P * H) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (div_pos hP0 hH0).le,
      Real.rpow_def_of_pos (div_pos hP0 hH0), Real.rpow_def_of_pos hP0,
      Real.rpow_def_of_pos hPH3', Real.rpow_def_of_pos (mul_pos hP0 hH0),
      ← Real.exp_add, ← Real.exp_add, hlogPdH, hlogP3, hlogPH]
    congr 1
    ring
  have hcore1 : (Real.sqrt (P / H)) ^ θ * P ^ ((1 - 2 * θ) / 3) ≤ Real.sqrt (P * H) := by
    rw [← hfact1]
    exact le_mul_of_one_le_right (by positivity) hone3
  set A : ℝ := Real.sqrt (P / H) * Λ with hAdef
  have hA0 : 0 < A := mul_pos (Real.sqrt_pos.2 (div_pos hP0 hH0)) hΛ0
  have hsle : (smallBlockLen h δ lam n : ℝ) ≤ A ^ θ + 1 := by
    have hEq : (smallBlockLen h δ lam n : ℝ) = (⌈A ^ θ⌉₊ : ℝ) := by
      simp only [smallBlockLen, hAdef, hθdef, hPdef, hHdef, hΛdef]
    rw [hEq]
    exact le_of_lt (Nat.ceil_lt_add_one (Real.rpow_nonneg hA0.le θ))
  have hAθ : A ^ θ = (Real.sqrt (P / H)) ^ θ * Λ ^ θ :=
    Real.mul_rpow (Real.sqrt_nonneg _) hΛ0.le
  -- `√(PH)/P ≤ 1`
  have hPH1 : Real.sqrt (P * H) ≤ P := by
    have h1 : P * H ≤ P * 1 := by nlinarith [hP0.le]
    have h2 : Real.sqrt (P * H) ≤ Real.sqrt (P * P) := by
      refine Real.sqrt_le_sqrt ?_
      nlinarith [hP0.le]
    rwa [Real.sqrt_mul_self hP0.le] at h2
  have hden : (0 : ℝ) < P ^ ((1 - 2 * θ) / 3) := Real.rpow_pos_of_pos hP0 _
  have hAθP : A ^ θ / P ≤ Λ ^ θ / P ^ ((1 - 2 * θ) / 3) := by
    rw [hAθ, div_le_div_iff₀ hP0 hden]
    have hs0 : (0 : ℝ) ≤ (Real.sqrt (P / H)) ^ θ := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hΛθ0 : (0 : ℝ) ≤ Λ ^ θ := Real.rpow_nonneg hΛ0.le _
    calc (Real.sqrt (P / H)) ^ θ * Λ ^ θ * P ^ ((1 - 2 * θ) / 3)
        = ((Real.sqrt (P / H)) ^ θ * P ^ ((1 - 2 * θ) / 3)) * Λ ^ θ := by ring
      _ ≤ Real.sqrt (P * H) * Λ ^ θ := by gcongr
      _ ≤ P * Λ ^ θ := by gcongr
      _ = Λ ^ θ * P := by ring
  rw [div_le_iff₀ hP0]
  have hmajP : (Real.log (n : ℝ) ^ θ / (n : ℝ) ^ ((1 - 2 * θ) / 3) + ((n : ℝ))⁻¹) * P
      = (Λ ^ θ / P ^ ((1 - 2 * θ) / 3)) * P + 1 := by
    rw [← hPdef, ← hΛdef, add_mul, inv_mul_cancel₀ hP0.ne']
  rw [hmajP]
  have h1 : A ^ θ ≤ (Λ ^ θ / P ^ ((1 - 2 * θ) / 3)) * P := by
    have := (div_le_iff₀ hP0).1 hAθP
    linarith
  linarith [hsle]

/-- The big-block index set: the union of the `k_n` big blocks. -/
private noncomputable def bigBlockIdx (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (blockCount h δ lam n)).biUnion fun i =>
    Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
      (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n)

/-- The big blocks are pairwise disjoint. -/
private theorem bigBlockIdx_pairwiseDisjoint (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) :
    (↑(Finset.range (blockCount h δ lam n)) : Set ℕ).PairwiseDisjoint fun i =>
      Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
        (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n) := by
  set q : ℕ := bigBlockLen h n + smallBlockLen h δ lam n with hq
  set lb : ℕ := bigBlockLen h n with hlb
  have key : ∀ i i' : ℕ, i < i' →
      Disjoint (Finset.Ico (i * q) (i * q + lb)) (Finset.Ico (i' * q) (i' * q + lb)) := by
    intro i i' hii
    rw [Finset.disjoint_left]
    intro a ha ha'
    rw [Finset.mem_Ico] at ha ha'
    have h1 : (i + 1) * q ≤ i' * q := Nat.mul_le_mul_right _ (by omega)
    have h2 : lb ≤ q := by rw [hq, hlb]; omega
    have h3 : (i + 1) * q = i * q + q := by ring
    omega
  intro i _ i' _ hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key i i' hlt
  · exact (key i' i hlt).symm

/-- The big blocks live inside `range n`. -/
private theorem bigBlockIdx_subset (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) :
    bigBlockIdx h δ lam n ⊆ Finset.range n := by
  intro a ha
  simp only [bigBlockIdx, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico] at ha ⊢
  obtain ⟨i, hi, ha1, ha2⟩ := ha
  have hlq : bigBlockLen h n
      ≤ bigBlockLen h n + smallBlockLen h δ lam n := Nat.le_add_right _ _
  have h1 : (i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)
      ≤ blockCount h δ lam n * (bigBlockLen h n + smallBlockLen h δ lam n) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : blockCount h δ lam n * (bigBlockLen h n + smallBlockLen h δ lam n) ≤ n :=
    Nat.div_mul_le_self _ _
  have h3 : (i + 1) * (bigBlockLen h n + smallBlockLen h δ lam n)
      = i * (bigBlockLen h n + smallBlockLen h δ lam n)
        + (bigBlockLen h n + smallBlockLen h δ lam n) := by ring
  omega

/-- The total big-block length is `k_n l_n`. -/
private theorem bigBlockIdx_card (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) :
    (bigBlockIdx h δ lam n).card = blockCount h δ lam n * bigBlockLen h n := by
  classical
  rw [bigBlockIdx, Finset.card_biUnion (fun i hi i' hi' hne =>
    bigBlockIdx_pairwiseDisjoint h δ lam n (by simpa using hi) (by simpa using hi') hne)]
  have hcard : ∀ i : ℕ,
      (Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
        (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n)).card
        = bigBlockLen h n := by
    intro i; rw [Nat.card_Ico]; omega
  rw [Finset.sum_congr rfl (fun i _ => hcard i), Finset.sum_const, Finset.card_range,
    smul_eq_mul]

/-- The block bookkeeping identity `k l + k s + (n mod (l+s)) = n`. -/
private theorem blockCount_identity (h : ℕ → ℝ) (δ lam : ℝ) (n : ℕ) :
    blockCount h δ lam n * bigBlockLen h n
      + blockCount h δ lam n * smallBlockLen h δ lam n
      + n % (bigBlockLen h n + smallBlockLen h δ lam n) = n := by
  have hdm := Nat.div_add_mod n (bigBlockLen h n + smallBlockLen h δ lam n)
  simp only [blockCount]
  nlinarith [hdm]

/-- The complement of the big blocks inside `range n` is negligible. -/
private theorem tendsto_restIdx_card {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam) :
    Tendsto (fun n : ℕ =>
        (((Finset.range n) \ bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hks := tendsto_blockCount_mul_smallBlockLen_div hh0 hnh hδ hlam
  have hl := tendsto_bigBlockLen_div hh0 hh
  have hs := tendsto_smallBlockLen_div hh0 hh hnh hδ hlam
  have hmaj : Tendsto (fun n : ℕ =>
      (blockCount h δ lam n : ℝ) * (smallBlockLen h δ lam n : ℝ) / (n : ℝ)
        + ((bigBlockLen h n : ℝ) / (n : ℝ) + (smallBlockLen h δ lam n : ℝ) / (n : ℝ)))
      atTop (𝓝 0) := by simpa using hks.add (hl.add hs)
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with n; positivity
  filter_upwards [eventually_ge_atTop 2] with n hn2
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hq1 : 1 ≤ bigBlockLen h n + smallBlockLen h δ lam n := by
    have hbl : 0 < bigBlockLen h n := by
      rw [bigBlockLen]
      refine Nat.ceil_pos.2 ?_
      have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
      have := hh0 n
      positivity
    omega
  have hsub := bigBlockIdx_subset h δ lam n
  have hcard : ((Finset.range n) \ bigBlockIdx h δ lam n).card
      = n - (bigBlockIdx h δ lam n).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, Finset.card_range]
  have hid := blockCount_identity h δ lam n
  have hcard2 : ((Finset.range n) \ bigBlockIdx h δ lam n).card
      = blockCount h δ lam n * smallBlockLen h δ lam n
        + n % (bigBlockLen h n + smallBlockLen h δ lam n) := by
    rw [hcard, bigBlockIdx_card]
    generalize blockCount h δ lam n * bigBlockLen h n = A at hid ⊢
    generalize blockCount h δ lam n * smallBlockLen h δ lam n = Bc at hid ⊢
    generalize n % (bigBlockLen h n + smallBlockLen h δ lam n) = C at hid ⊢
    omega
  have hmod : n % (bigBlockLen h n + smallBlockLen h δ lam n)
      ≤ bigBlockLen h n + smallBlockLen h δ lam n := (Nat.mod_lt _ hq1).le
  rw [hcard2, div_le_iff₀ hn0]
  push_cast
  have h1 : ((n % (bigBlockLen h n + smallBlockLen h δ lam n) : ℕ) : ℝ)
      ≤ (bigBlockLen h n : ℝ) + (smallBlockLen h δ lam n : ℝ) := by
    exact_mod_cast hmod
  have hexp : ((blockCount h δ lam n : ℝ) * (smallBlockLen h δ lam n : ℝ) / (n : ℝ)
      + ((bigBlockLen h n : ℝ) / (n : ℝ) + (smallBlockLen h δ lam n : ℝ) / (n : ℝ))) * (n : ℝ)
      = (blockCount h δ lam n : ℝ) * (smallBlockLen h δ lam n : ℝ)
        + ((bigBlockLen h n : ℝ) + (smallBlockLen h δ lam n : ℝ)) := by
    field_simp
  rw [hexp]
  linarith

/-- The big blocks fill `range n` asymptotically. -/
private theorem tendsto_bigBlockIdx_card {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam) :
    Tendsto (fun n : ℕ => ((bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
  have hrest := tendsto_restIdx_card hh0 hh hnh hδ hlam
  have hone : Tendsto (fun n : ℕ =>
      1 - (((Finset.range n) \ bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    simpa using hrest.const_sub (1 : ℝ)
  refine hone.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hsub := bigBlockIdx_subset h δ lam n
  have hcard : ((Finset.range n) \ bigBlockIdx h δ lam n).card
      = n - (bigBlockIdx h δ lam n).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, Finset.card_range]
  have hle : (bigBlockIdx h δ lam n).card ≤ n := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_range] at this
  have hcast : (((Finset.range n) \ bigBlockIdx h δ lam n).card : ℝ)
      = (n : ℝ) - ((bigBlockIdx h δ lam n).card : ℝ) := by
    rw [hcard, Nat.cast_sub hle]
  show 1 - (((Finset.range n) \ bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)
      = ((bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)
  rw [hcast]
  field_simp
  ring

set_option maxHeartbeats 2000000 in
private theorem tendsto_blockVar_sum [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hC2gen : ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L)
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L))
    (hsLm : ∀ L : ℝ, Measurable (sL L))
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hpc : ContinuousAt p x) (hpx : 0 < p x)
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (blockCount h δ lam n),
        ((n : ℝ) * h n)⁻¹ *
          ∫ ω, (∑ t ∈ Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
              (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n),
              truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
      atTop (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)) := by
  obtain ⟨Z, Gz, hZm, hZrep, hint, hCG, hCG', hdiaglim, hRto0, hZb, hmean0⟩ :=
    truncArray_core hmeasX hmeasE hstat hδ hmp hp0 hpd hpb hB0 hC2gen hlam hα hWm hWb hW1 hW2
      hh0 hh hL mL sL hmLm hsLm hmLv hsLv hσLc hσLb hpc hpx
  set Cz : ℕ → ℕ → ℕ → ℝ := fun n s t => ∫ ω, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω ∂μ
    with hCzdef
  have hCGc : ∀ n s d : ℕ, Cz n s (s + d) = Gz n d := fun n s d => hCG n s d
  have hCGc' : ∀ n s d : ℕ, Cz n (s + d) s = Gz n d := fun n s d => hCG' n s d
  set Bl : ℕ → ℕ → Finset ℕ := fun n i =>
    Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
      (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n) with hBldef
  have hBcard : ∀ n i : ℕ, (Bl n i).card = bigBlockLen h n := by
    intro n i; rw [hBldef]; simp only [Nat.card_Ico]; omega
  have hBsub : ∀ (n i : ℕ), i ∈ Finset.range (blockCount h δ lam n) →
      Bl n i ⊆ Finset.range n := by
    intro n i hi a ha
    refine bigBlockIdx_subset h δ lam n ?_
    simp only [bigBlockIdx, Finset.mem_biUnion]
    exact ⟨i, hi, ha⟩
  -- the sum of squares over one block
  have hexp : ∀ n i : ℕ, ∫ ω, (∑ t ∈ Bl n i, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ
      = ∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t := by
    intro n i
    have hsq : ∀ ω : Ω, (∑ t ∈ Bl n i, Z n ((t : ℤ) + 1) ω) ^ 2
        = ∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Z n ((s : ℤ) + 1) ω * Z n ((t : ℤ) + 1) ω := by
      intro ω; rw [sq, Finset.sum_mul_sum]
    simp only [hsq, hCzdef]
    rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun t _ => hint n _ _))]
    exact Finset.sum_congr rfl fun s _ => integral_finset_sum _ (fun t _ => hint n _ _)
  have hsumrep : ∀ n i : ℕ,
      ∫ ω, (∑ t ∈ Bl n i, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ
        = ∫ ω, (∑ t ∈ Bl n i, Z n ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    intro n i
    refine integral_congr_ae ?_
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Bl n i,
        truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)
          = Z n ((t : ℤ) + 1) ω :=
      (Filter.eventually_all_finset (Bl n i)).2 (fun t _ => hZrep n ((t : ℤ) + 1))
    filter_upwards [hall] with ω hω
    rw [Finset.sum_congr rfl hω]
  have hcards : ∀ n : ℕ, ∑ i ∈ Finset.range (blockCount h δ lam n), ((Bl n i).card : ℝ)
      = ((bigBlockIdx h δ lam n).card : ℝ) := by
    intro n
    rw [bigBlockIdx_card, Finset.sum_congr rfl (fun i _ => by rw [hBcard n i]),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hblock : ∀ n : ℕ, |(∑ i ∈ Finset.range (blockCount h δ lam n),
          ∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t)
        - ((bigBlockIdx h δ lam n).card : ℝ) * Gz n 0|
      ≤ ((bigBlockIdx h δ lam n).card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) := by
    intro n
    have hrw : (∑ i ∈ Finset.range (blockCount h δ lam n),
          ∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t)
        - ((bigBlockIdx h δ lam n).card : ℝ) * Gz n 0
        = ∑ i ∈ Finset.range (blockCount h δ lam n),
          ((∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t) - ((Bl n i).card : ℝ) * Gz n 0) := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hcards n]
    rw [hrw]
    calc |∑ i ∈ Finset.range (blockCount h δ lam n),
            ((∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t) - ((Bl n i).card : ℝ) * Gz n 0)|
        ≤ ∑ i ∈ Finset.range (blockCount h δ lam n),
            |(∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t) - ((Bl n i).card : ℝ) * Gz n 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (blockCount h δ lam n),
            ((Bl n i).card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) :=
          Finset.sum_le_sum fun i hi => abs_double_sum_subset_sub_diag_le (Bl n i)
            (hBsub n i hi) (Cz n) (Gz n) (hCGc n) (hCGc' n)
      _ = ((bigBlockIdx h δ lam n).card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) := by
          rw [← Finset.sum_mul, hcards n]
  -- assembly
  have hbig := tendsto_bigBlockIdx_card hh0 hh hnh hδ hlam
  have hmain : Tendsto (fun n : ℕ =>
      (((bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0)) atTop
      (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)) := by
    simpa using hbig.mul hdiaglim
  have herr : Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range (blockCount h δ lam n), ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ Bl n i, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
      - (((bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => (((bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) *
        (2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|)) atTop (𝓝 0) := by
      simpa using hbig.mul hRto0
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hhn : 0 < h n := hh0 n
    have hcollect : (∑ i ∈ Finset.range (blockCount h δ lam n), ((n : ℝ) * h n)⁻¹ *
        ∫ ω, (∑ t ∈ Bl n i, truncErr X e μ L ((t : ℤ) + 1) ω *
          W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
        = ((n : ℝ) * h n)⁻¹ * (∑ i ∈ Finset.range (blockCount h δ lam n),
            ∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [hsumrep n i, hexp n i]
    have hid : (∑ i ∈ Finset.range (blockCount h δ lam n), ((n : ℝ) * h n)⁻¹ *
          ∫ ω, (∑ t ∈ Bl n i, truncErr X e μ L ((t : ℤ) + 1) ω *
            W ((X ((t : ℤ) + 1) ω - x) / h n)) ^ 2 ∂μ)
        - (((bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) * ((h n)⁻¹ * Gz n 0)
        = ((n : ℝ) * h n)⁻¹ * ((∑ i ∈ Finset.range (blockCount h δ lam n),
            ∑ s ∈ Bl n i, ∑ t ∈ Bl n i, Cz n s t)
          - ((bigBlockIdx h δ lam n).card : ℝ) * Gz n 0) := by
      rw [hcollect]
      field_simp
    have hid2 : ((n : ℝ) * h n)⁻¹ *
        (((bigBlockIdx h δ lam n).card : ℝ) * (2 * ∑ j ∈ Finset.Ico 1 n, |Gz n j|))
        = (((bigBlockIdx h δ lam n).card : ℝ) / (n : ℝ)) *
          (2 * (h n)⁻¹ * ∑ j ∈ Finset.Ico 1 n, |Gz n j|) := by
      field_simp
    rw [Real.norm_eq_abs, hid, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) * h n)⁻¹), ← hid2]
    exact mul_le_mul_of_nonneg_left (hblock n) (by positivity)
  have hsum := hmain.add herr
  rw [add_zero] at hsum
  exact hsum.congr fun n => by ring




set_option maxHeartbeats 1000000 in
/-- **The row-CLT in product-of-charFuns form.** A uniformly negligible bounded array of
zero-mean rows with converging row variances has `∏ᵢ φ_{Y_{n,i}}(u) → φ_{N(0,σ²)}(u)`, with
**no independence assumed**: the product is transported to an independent surrogate on the
infinite product of the individual laws, where
`tendsto_charFun_rowSum_gaussian_of_uniformly_small` applies. -/
private theorem tendsto_prod_charFun_of_uniformly_small [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {Y : (n : ℕ) → Fin (k n) → Ω → ℝ}
    (hmeas : ∀ n i, Measurable (Y n i))
    (hmean : ∀ n i, ∫ ω, Y n i ω ∂μ = 0)
    (hL2 : ∀ n i, MemLp (Y n i) 2 μ)
    {b : ℕ → ℝ} (hbdd : ∀ n i, ∀ᵐ ω ∂μ, |Y n i ω| ≤ b n)
    (hb0 : Tendsto b atTop (𝓝 0))
    {σ2 : ℝ} (hvar : Tendsto (fun n => ∑ i, variance (Y n i) μ) atTop (𝓝 σ2)) (u : ℝ) :
    Tendsto (fun n => ∏ i, charFun (μ.map (Y n i)) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal σ2)) u)) := by
  classical
  set Yt : ℕ × ℕ → Ω → ℝ := fun z => if hz : z.2 < k z.1 then Y z.1 ⟨z.2, hz⟩ else 0
    with hYtdef
  have hYtm : ∀ z : ℕ × ℕ, Measurable (Yt z) := by
    intro z
    simp only [hYtdef]
    split
    · exact hmeas _ _
    · exact measurable_const
  set P : ℕ × ℕ → Measure ℝ := fun z => μ.map (Yt z) with hPdef
  haveI hPprob : ∀ z, IsProbabilityMeasure (P z) := fun z =>
    Measure.isProbabilityMeasure_map (hYtm z).aemeasurable
  set ν : Measure (ℕ × ℕ → ℝ) := Measure.infinitePi P with hνdef
  haveI : IsProbabilityMeasure ν := by rw [hνdef]; infer_instance
  set Z : (n : ℕ) → Fin (k n) → (ℕ × ℕ → ℝ) → ℝ := fun n i z => z (n, (i : ℕ)) with hZdef
  have hZm : ∀ (n : ℕ) (i : Fin (k n)), Measurable (Z n i) := fun n i => measurable_pi_apply _
  have hYteq : ∀ (n : ℕ) (i : Fin (k n)), Yt (n, (i : ℕ)) = Y n i := by
    intro n i
    simp only [hYtdef]
    rw [dif_pos i.2]
  have hlaw : ∀ (n : ℕ) (i : Fin (k n)), ν.map (Z n i) = μ.map (Y n i) := by
    intro n i
    have h1 : ν.map (fun z : ℕ × ℕ → ℝ => z (n, (i : ℕ))) = P (n, (i : ℕ)) := by
      rw [hνdef]; exact Measure.infinitePi_map_eval P (n, (i : ℕ))
    rw [hZdef]
    simp only
    rw [h1, hPdef]
    simp only
    rw [hYteq n i]
  -- independence of the coordinates
  have hindep : ∀ n : ℕ, iIndepFun (Z n) ν := by
    intro n
    have hall : iIndepFun (fun (z : ℕ × ℕ) (ω : ℕ × ℕ → ℝ) => ω z) ν :=
      ProbabilityTheory.iIndepFun_infinitePi (X := fun _ : ℕ × ℕ => (id : ℝ → ℝ))
        (fun _ => measurable_id)
    have hinj : Function.Injective (fun i : Fin (k n) => (n, (i : ℕ))) := by
      intro i j hij
      have : (i : ℕ) = (j : ℕ) := congrArg Prod.snd hij
      exact Fin.ext this
    exact hall.precomp hinj
  -- transport of the hypotheses
  have hmeanZ : ∀ (n : ℕ) (i : Fin (k n)), ∫ z, Z n i z ∂ν = 0 := by
    intro n i
    have h1 : ∫ y, y ∂(ν.map (Z n i)) = ∫ z, Z n i z ∂ν :=
      integral_map (hZm n i).aemeasurable (f := fun y : ℝ => y) aestronglyMeasurable_id
    have h2 : ∫ y, y ∂(μ.map (Y n i)) = ∫ ω, Y n i ω ∂μ :=
      integral_map (hmeas n i).aemeasurable (f := fun y : ℝ => y) aestronglyMeasurable_id
    rw [← h1, hlaw n i, h2, hmean n i]
  have hL2Z : ∀ (n : ℕ) (i : Fin (k n)), MemLp (Z n i) 2 ν := by
    intro n i
    have h1 : MemLp (fun y : ℝ => y) 2 (ν.map (Z n i)) := by
      rw [hlaw n i]
      exact (memLp_map_measure_iff aestronglyMeasurable_id
        (hmeas n i).aemeasurable).2 (hL2 n i)
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hZm n i).aemeasurable).1 h1
  have hbddZ : ∀ (n : ℕ) (i : Fin (k n)), ∀ᵐ z ∂ν, |Z n i z| ≤ b n := by
    intro n i
    have hset : MeasurableSet {y : ℝ | |y| ≤ b n} :=
      measurableSet_le measurable_id.abs measurable_const
    have h1 : ∀ᵐ y ∂(μ.map (Y n i)), |y| ≤ b n :=
      (ae_map_iff (hmeas n i).aemeasurable hset).2 (hbdd n i)
    rw [← hlaw n i] at h1
    exact (ae_map_iff (hZm n i).aemeasurable hset).1 h1
  have hvarZ : ∀ (n : ℕ) (i : Fin (k n)), variance (Z n i) ν = variance (Y n i) μ := by
    intro n i
    have h1 : variance (fun y : ℝ => y) (ν.map (Z n i)) = variance (Z n i) ν := by
      have := variance_map (X := fun y : ℝ => y) (Y := Z n i) (μ := ν)
        aemeasurable_id (hZm n i).aemeasurable
      simpa [Function.comp_def] using this
    have h2 : variance (fun y : ℝ => y) (μ.map (Y n i)) = variance (Y n i) μ := by
      have := variance_map (X := fun y : ℝ => y) (Y := Y n i) (μ := μ)
        aemeasurable_id (hmeas n i).aemeasurable
      simpa [Function.comp_def] using this
    rw [← h1, hlaw n i, h2]
  have hvarZ' : Tendsto (fun n => ∑ i, variance (Z n i) ν) atTop (𝓝 σ2) := by
    refine hvar.congr fun n => ?_
    exact (Finset.sum_congr rfl fun i _ => (hvarZ n i).symm)
  have hCLT := tendsto_charFun_rowSum_gaussian_of_uniformly_small (μ := ν) hZm hindep hmeanZ
    hL2Z hbddZ hb0 hvarZ' u
  refine hCLT.congr fun n => ?_
  rw [iIndepFun.charFun_map_fun_sum_eq_prod (fun i => (hZm n i).aemeasurable) (hindep n),
    Finset.prod_apply]
  exact Finset.prod_congr rfl fun i _ => by rw [hlaw n i]



set_option maxHeartbeats 1000000 in
/-- **FY's Volkonskii–Rozanov step (2.77).** The charFun of the sum of the big blocks is
within `16(k_n − 1) α_pair(s_n)` of the product of the block charFuns. -/
private theorem norm_charFun_blockSum_sub_prod_le [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {W : ℝ → ℝ} (hWm : Measurable W) {x : ℝ} {h : ℕ → ℝ} {L : ℝ} {δ lam : ℝ}
    (n : ℕ) (hk : 0 < blockCount h δ lam n) (u : ℝ) :
    ‖charFun (μ.map (fun ω => ∑ i : Fin (blockCount h δ lam n),
          (Real.sqrt ((n : ℝ) * h n))⁻¹ *
            ∑ t ∈ Finset.Ico ((i : ℕ) * (bigBlockLen h n + smallBlockLen h δ lam n))
              ((i : ℕ) * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n),
              truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n))) u
        - ∏ i : Fin (blockCount h δ lam n),
            charFun (μ.map (fun ω => (Real.sqrt ((n : ℝ) * h n))⁻¹ *
              ∑ t ∈ Finset.Ico ((i : ℕ) * (bigBlockLen h n + smallBlockLen h δ lam n))
                ((i : ℕ) * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n),
                truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n))) u‖
      ≤ 16 * ((blockCount h δ lam n : ℝ) - 1) *
          pairAlphaCoeff X e μ (smallBlockLen h δ lam n) := by
  classical
  set k : ℕ := blockCount h δ lam n with hkdef
  set q : ℕ := bigBlockLen h n + smallBlockLen h δ lam n with hqdef
  set lb : ℕ := bigBlockLen h n with hlbdef
  set sb : ℕ := smallBlockLen h δ lam n with hsbdef
  set V : Fin k → Ω → ℝ := fun i ω => (Real.sqrt ((n : ℝ) * h n))⁻¹ *
    ∑ t ∈ Finset.Ico ((i : ℕ) * q) ((i : ℕ) * q + lb),
      truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n) with hVdef
  set S : Fin k → Set ℤ := fun i =>
    Set.Icc (((i : ℕ) * q : ℕ) + 1 : ℤ) ((((i : ℕ) * q + lb : ℕ)) : ℤ) with hSdef
  set m : Fin k → MeasurableSpace Ω := fun i =>
    ⨆ s ∈ S i, MeasurableSpace.comap (X s) inferInstance ⊔
      MeasurableSpace.comap (e s) inferInstance with hmdef
  have hmle : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := fun i =>
    pairSigma_le hmeasX hmeasE (S i)
  -- each block statistic is measurable for its own σ-algebra
  have hVm : ∀ i : Fin k, Measurable[m i] (V i) := by
    intro i
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum _ fun t ht => ?_
    have hts : ((t : ℤ) + 1) ∈ S i := by
      simp only [hSdef, Set.mem_Icc]
      rw [Finset.mem_Ico] at ht
      omega
    have hXt : Measurable[m i] (X ((t : ℤ) + 1)) :=
      measurable_X_pairSigma (X := X) (e := e) hts
    have hEt : Measurable[m i] (e ((t : ℤ) + 1)) :=
      measurable_e_pairSigma (X := X) (e := e) hts
    have hcle : MeasurableSpace.comap (X ((t : ℤ) + 1)) inferInstance ≤ m i :=
      le_iSup₂_of_le ((t : ℤ) + 1) hts le_sup_left
    have hcond : Measurable[m i]
        (μ[fun ω' => clampAt L (e ((t : ℤ) + 1) ω') |
          MeasurableSpace.comap (X ((t : ℤ) + 1)) inferInstance]) :=
      (stronglyMeasurable_condExp.mono hcle).measurable
    have h1 : Measurable[m i] (truncErr X e μ L ((t : ℤ) + 1)) :=
      ((measurable_clampAt L).comp hEt).sub hcond
    exact h1.mul (hWm.comp ((hXt.sub measurable_const).div measurable_const))
  set ξ : Fin k → Ω → ℂ := fun i ω => Complex.exp ((u : ℂ) * (V i ω : ℂ) * Complex.I)
    with hξdef
  have hc : Continuous fun z : ℝ => Complex.exp ((u : ℂ) * (z : ℂ) * Complex.I) := by fun_prop
  have hξm : ∀ i, Measurable[m i] (ξ i) := fun i => hc.measurable.comp (hVm i)
  have hξb : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ 1 := by
    intro i
    filter_upwards with ω
    rw [hξdef]
    simp only
    rw [show ((u : ℂ) * (V i ω : ℂ) * Complex.I) = ((u * V i ω : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  -- the α-gap between the cumulative past and the next block
  have hgap : ∀ i : Fin k, ∀ _hi : (i : ℕ) + 1 < k,
      alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (i : ℕ), m j) (m ⟨(i : ℕ) + 1, ‹_›⟩)
        ≤ pairAlphaCoeff X e μ sb := by
    intro i hi
    set c : ℤ := (((i : ℕ) * q + lb : ℕ) : ℤ) with hcdef
    have hpast : (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (i : ℕ), m j)
        ≤ ⨆ s ∈ Set.Iic c, MeasurableSpace.comap (X s) inferInstance ⊔
          MeasurableSpace.comap (e s) inferInstance := by
      refine iSup₂_le fun j hj => ?_
      refine iSup₂_le fun s hs => ?_
      refine le_iSup₂_of_le s ?_ le_rfl
      simp only [hSdef, Set.mem_Icc] at hs
      simp only [Set.mem_Iic, hcdef]
      have hjq : (j : ℕ) * q + lb ≤ (i : ℕ) * q + lb := by
        have := Nat.mul_le_mul_right q hj
        omega
      have : ((((j : ℕ) * q + lb : ℕ)) : ℤ) ≤ ((((i : ℕ) * q + lb : ℕ)) : ℤ) := by
        exact_mod_cast hjq
      linarith [hs.2]
    have hfut : m ⟨(i : ℕ) + 1, hi⟩
        ≤ ⨆ s ∈ Set.Ici (c + (sb : ℤ)), MeasurableSpace.comap (X s) inferInstance ⊔
          MeasurableSpace.comap (e s) inferInstance := by
      refine iSup₂_le fun s hs => ?_
      refine le_iSup₂_of_le s ?_ le_rfl
      simp only [hSdef, Set.mem_Icc] at hs
      simp only [Set.mem_Ici, hcdef]
      have hstep : ((i : ℕ) * q + lb) + sb ≤ (((i : ℕ) + 1) * q) + 1 := by
        have hq : q = lb + sb := by rw [hqdef, hlbdef, hsbdef]
        have : ((i : ℕ) + 1) * q = (i : ℕ) * q + q := by ring
        omega
      have : ((((i : ℕ) * q + lb : ℕ)) : ℤ) + (sb : ℤ)
          ≤ (((((i : ℕ) + 1) * q : ℕ)) : ℤ) + 1 := by exact_mod_cast hstep
      have hs1 : ((((⟨(i : ℕ) + 1, hi⟩ : Fin k) : ℕ) * q : ℕ) : ℤ) + 1 ≤ s := hs.1
      simp only at hs1
      linarith
    calc alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (i : ℕ), m j) (m ⟨(i : ℕ) + 1, hi⟩)
        ≤ alphaMixCoeff μ
            (⨆ s ∈ Set.Iic c, MeasurableSpace.comap (X s) inferInstance ⊔
              MeasurableSpace.comap (e s) inferInstance)
            (⨆ s ∈ Set.Ici (c + (sb : ℤ)), MeasurableSpace.comap (X s) inferInstance ⊔
              MeasurableSpace.comap (e s) inferInstance) :=
          alphaMixCoeff_mono (mΩ := inferInstance) hpast hfut
      _ = pairAlphaCoeff X e μ sb := pairAlphaCoeff_shift hmeasX hmeasE hstat c sb
  have hVR := norm_integral_prod_sub_prod_integral_le_of_pos (μ := μ) hk hmle ξ hξm hξb
    (a := pairAlphaCoeff X e μ sb) (fun i hi => hgap i hi)
  -- identify the two sides
  have hVmeas : ∀ i : Fin k, Measurable (V i) := fun i => (hVm i).mono (hmle i) le_rfl
  have hsumm : Measurable (fun ω => ∑ i : Fin k, V i ω) :=
    Finset.measurable_sum _ fun i _ => hVmeas i
  have hprodξ : ∀ ω, ∏ i : Fin k, ξ i ω
      = Complex.exp ((u : ℂ) * ((∑ i : Fin k, V i ω : ℝ) : ℂ) * Complex.I) := by
    intro ω
    rw [hξdef]
    simp only
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
  have hleft : ∫ ω, ∏ i : Fin k, ξ i ω ∂μ
      = charFun (μ.map (fun ω => ∑ i : Fin k, V i ω)) u := by
    rw [charFun_apply_real, integral_map hsumm.aemeasurable hc.aestronglyMeasurable]
    exact (integral_congr_ae (Eventually.of_forall hprodξ))
  have hright : ∀ i : Fin k, ∫ ω, ξ i ω ∂μ = charFun (μ.map (V i)) u := by
    intro i
    rw [charFun_apply_real, integral_map (hVmeas i).aemeasurable hc.aestronglyMeasurable]
  rw [hleft, Finset.prod_congr rfl (fun i _ => hright i)] at hVR
  exact hVR



/-- `n h_n → ∞` under (C5). -/
private theorem tendsto_mul_bandwidth_atTop {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ => (n : ℝ) * h n) atTop atTop := by
  refine tendsto_atTop_mono' _ ?_ hnh
  filter_upwards [hh.eventually_le_const (by norm_num : (0:ℝ) < 1), eventually_ge_atTop 1]
    with n hh1 hn1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hhn := hh0 n
  have hh2 : h n ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hn0 hhn.le) (sub_nonneg.2 hh2)]

/-- The big-block envelope `l_n / √(n h_n) → 0` — this is what `l_n = [√(n h_n)/log n]`
is chosen for. -/
private theorem tendsto_bigBlockLen_div_sqrt {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) :
    Tendsto (fun n : ℕ => (Real.sqrt ((n : ℝ) * h n))⁻¹ * (bigBlockLen h n : ℝ))
      atTop (𝓝 0) := by
  have hnh' := tendsto_mul_bandwidth_atTop hh0 hh hnh
  have hsq : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) * h n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hnh'
  have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmaj : Tendsto (fun n : ℕ =>
      (Real.log n)⁻¹ + (Real.sqrt ((n : ℝ) * h n))⁻¹) atTop (𝓝 0) := by
    simpa using hlogtop.inv_tendsto_atTop.add hsq.inv_tendsto_atTop
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards with n; positivity
  filter_upwards [hlogtop.eventually_gt_atTop 0, hsq.eventually_gt_atTop 0] with n hlog hsqn
  have hle : (bigBlockLen h n : ℝ) ≤ Real.sqrt ((n : ℝ) * h n) / Real.log n + 1 := by
    rw [bigBlockLen]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hstep : (Real.sqrt ((n : ℝ) * h n))⁻¹ * (bigBlockLen h n : ℝ)
      ≤ (Real.sqrt ((n : ℝ) * h n))⁻¹ * (Real.sqrt ((n : ℝ) * h n) / Real.log n + 1) :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  refine hstep.trans (le_of_eq ?_)
  field_simp



/-- `truncErr` is measurable (the conditional expectation is `σ(X_t)`-measurable). -/
private theorem measurable_truncErr {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t))
    (hmeasE : ∀ t, Measurable (e t)) (L : ℝ) (t : ℤ) :
    Measurable (truncErr X e μ L t) :=
  ((measurable_clampAt L).comp (hmeasE t)).sub
    ((stronglyMeasurable_condExp.mono (hmeasX t).comap_le).measurable)

/-- `L²`-negligibility implies `L¹`-negligibility (via `|z| ≤ z²/(2c) + c/2`). -/
private theorem tendsto_integral_abs_of_tendsto_sq [IsProbabilityMeasure μ] {D : ℕ → Ω → ℝ}
    (hD : ∀ n, MemLp (D n) 2 μ)
    (h2 : Tendsto (fun n => ∫ ω, (D n ω) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |D n ω| ∂μ) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hc : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (h2.eventually_lt_const (by positivity : (0 : ℝ) < (ε / 2) ^ 2))
  refine ⟨N, fun n hn => ?_⟩
  have hi1 : Integrable (fun ω => |D n ω|) μ := ((hD n).integrable (by norm_num)).abs
  have hi2 : Integrable (fun ω => (D n ω) ^ 2) μ := (hD n).integrable_sq
  have hptw : ∀ ω, |D n ω| ≤ (D n ω) ^ 2 / (2 * (ε / 2)) + (ε / 2) / 2 := by
    intro ω
    set z : ℝ := D n ω with hzdef
    have hnum : (0 : ℝ) ≤ z ^ 2 + (ε / 2) ^ 2 - 2 * (ε / 2) * |z| := by
      nlinarith [sq_nonneg (|z| - ε / 2), sq_abs z]
    have hid : z ^ 2 / (2 * (ε / 2)) + (ε / 2) / 2 - |z|
        = (z ^ 2 + (ε / 2) ^ 2 - 2 * (ε / 2) * |z|) / (2 * (ε / 2)) := by
      field_simp
    have hdiv : (0 : ℝ) ≤ (z ^ 2 + (ε / 2) ^ 2 - 2 * (ε / 2) * |z|) / (2 * (ε / 2)) :=
      div_nonneg hnum (by linarith)
    linarith
  have hmono : ∫ ω, |D n ω| ∂μ
      ≤ ∫ ω, ((D n ω) ^ 2 / (2 * (ε / 2)) + (ε / 2) / 2) ∂μ :=
    integral_mono hi1 ((hi2.div_const _).add (integrable_const _)) hptw
  have heval : ∫ ω, ((D n ω) ^ 2 / (2 * (ε / 2)) + (ε / 2) / 2) ∂μ
      = (∫ ω, (D n ω) ^ 2 ∂μ) / (2 * (ε / 2)) + (ε / 2) / 2 := by
    rw [integral_add (hi2.div_const _) (integrable_const _), integral_div, integral_const]
    simp
  rw [heval] at hmono
  have hsq := hN n hn
  have hlt : (∫ ω, (D n ω) ^ 2 ∂μ) / (2 * (ε / 2)) < (ε / 2) / 2 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hnn : (0 : ℝ) ≤ ∫ ω, |D n ω| ∂μ := integral_nonneg fun ω => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith



/-- Eventually there is at least one block. -/
private theorem eventually_blockCount_pos {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n)
    (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    {δ lam : ℝ} (hδ : 2 < δ) (hlam : 1 - 2 / δ < lam) :
    ∀ᶠ n : ℕ in atTop, 0 < blockCount h δ lam n := by
  have hl := tendsto_bigBlockLen_div hh0 hh
  have hs := tendsto_smallBlockLen_div hh0 hh hnh hδ hlam
  filter_upwards [eventually_ge_atTop 2,
    hl.eventually_lt_const (by norm_num : (0:ℝ) < 1/3),
    hs.eventually_lt_const (by norm_num : (0:ℝ) < 1/3)] with n hn2 hln hsn
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) ≤ n := by omega
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hq1 : 1 ≤ bigBlockLen h n + smallBlockLen h δ lam n := by
    have hbl : 0 < bigBlockLen h n := by
      rw [bigBlockLen]
      refine Nat.ceil_pos.2 ?_
      have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn2)
      have := hh0 n
      positivity
    omega
  have hlR : (bigBlockLen h n : ℝ) < (n : ℝ) / 3 := by
    rw [div_lt_iff₀ hn0] at hln
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith
  have hsR : (smallBlockLen h δ lam n : ℝ) < (n : ℝ) / 3 := by
    rw [div_lt_iff₀ hn0] at hsn
    rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith
  have hqn : bigBlockLen h n + smallBlockLen h δ lam n ≤ n := by
    have : ((bigBlockLen h n + smallBlockLen h δ lam n : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  exact Nat.one_le_div_iff (by omega) |>.2 hqn

set_option maxHeartbeats 2000000 in
set_option maxHeartbeats 2000000 in
private theorem tendsto_charFun_locTruncSum_pos [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {p : ℝ → ℝ} {δ x : ℝ} (hδ : 2 < δ)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    {Cp : ℝ} (hpb : ∀ v, p v ≤ Cp)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hC2gen : ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    {L : ℝ} (hL : 0 < L)
    (mL sL : ℝ → ℝ → ℝ) (hmLm : ∀ L : ℝ, Measurable (mL L))
    (hsLm : ∀ L : ℝ, Measurable (sL L))
    (hmLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv :
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hpc : ContinuousAt p x) (hpx : 0 < p x)
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map (locTruncSum X e μ W x h L n)) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2))) u)) := by
  classical
  obtain ⟨Z, Gz, hZm, hZrep, hint, hCG, hCG', hdiaglim, hRto0, hZb, hmean0⟩ :=
    truncArray_core hmeasX hmeasE hstat hδ hmp hp0 hpd hpb hB0 hC2gen hlam hα hWm hWb hW1 hW2
      hh0 hh hL mL sL hmLm hsLm hmLv hsLv hσLc hσLb hpc hpx
  have hCW0 : (0 : ℝ) ≤ CW := le_trans (abs_nonneg _) (hWb 0)
  set ζ : ℕ → ℕ → Ω → ℝ := fun n t ω =>
    truncErr X e μ L ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n) with hζdef
  have hζm : ∀ n t : ℕ, Measurable (ζ n t) := fun n t =>
    (measurable_truncErr hmeasX hmeasE L _).mul
      (hWm.comp (((hmeasX _).sub measurable_const).div measurable_const))
  have hζZ : ∀ n t : ℕ, ζ n t =ᵐ[μ] Z n ((t : ℤ) + 1) := fun n t => hZrep n ((t : ℤ) + 1)
  have hζb : ∀ n t : ℕ, ∀ᵐ ω ∂μ, |ζ n t ω| ≤ 2 * L * CW := by
    intro n t
    filter_upwards [hζZ n t] with ω hω
    rw [hω]; exact hZb n _ ω
  have hζint : ∀ n t : ℕ, Integrable (ζ n t) μ := by
    intro n t
    refine (integrable_const (2 * L * CW)).mono' (hζm n t).aestronglyMeasurable ?_
    filter_upwards [hζb n t] with ω hω
    rwa [Real.norm_eq_abs]
  have hζmean : ∀ n t : ℕ, ∫ ω, ζ n t ω ∂μ = 0 := by
    intro n t
    rw [integral_congr_ae (hζZ n t)]
    exact hmean0 n _
  -- the block statistics
  set V : ℕ → ℕ → Ω → ℝ := fun n i ω => (Real.sqrt ((n : ℝ) * h n))⁻¹ *
    ∑ t ∈ Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
      (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n), ζ n t ω with hVdef
  set bn : ℕ → ℝ := fun n =>
    (Real.sqrt ((n : ℝ) * h n))⁻¹ * (bigBlockLen h n : ℝ) * (2 * L * CW) with hbndef
  have hsq0 : ∀ n : ℕ, (0 : ℝ) ≤ (Real.sqrt ((n : ℝ) * h n))⁻¹ := fun n => by positivity
  have hVm : ∀ n i : ℕ, Measurable (V n i) := fun n i =>
    (Finset.measurable_sum _ fun t _ => hζm n t).const_mul _
  have hVmean : ∀ n i : ℕ, ∫ ω, V n i ω ∂μ = 0 := by
    intro n i
    rw [hVdef]
    simp only
    rw [integral_const_mul, integral_finset_sum _ (fun t _ => hζint n t)]
    simp only [hζmean n]
    simp
  have hVb : ∀ n i : ℕ, ∀ᵐ ω ∂μ, |V n i ω| ≤ bn n := by
    intro n i
    have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
        (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n),
        |ζ n t ω| ≤ 2 * L * CW :=
      (Filter.eventually_all_finset _).2 fun t _ => hζb n t
    filter_upwards [hall] with ω hω
    have hcard : (Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
        (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n)).card
          = bigBlockLen h n := by rw [Nat.card_Ico]; omega
    have hsum : |∑ t ∈ Finset.Ico (i * (bigBlockLen h n + smallBlockLen h δ lam n))
        (i * (bigBlockLen h n + smallBlockLen h δ lam n) + bigBlockLen h n), ζ n t ω|
        ≤ (bigBlockLen h n : ℝ) * (2 * L * CW) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have := Finset.sum_le_card_nsmul _ (fun t => |ζ n t ω|) (2 * L * CW) hω
      simpa [hcard, nsmul_eq_mul] using this
    rw [hVdef]
    simp only [abs_mul, abs_of_nonneg (hsq0 n), hbndef]
    calc (Real.sqrt ((n : ℝ) * h n))⁻¹ * |∑ t ∈ _, ζ n t ω|
        ≤ (Real.sqrt ((n : ℝ) * h n))⁻¹ * ((bigBlockLen h n : ℝ) * (2 * L * CW)) :=
          mul_le_mul_of_nonneg_left hsum (hsq0 n)
      _ = (Real.sqrt ((n : ℝ) * h n))⁻¹ * (bigBlockLen h n : ℝ) * (2 * L * CW) := by ring
  have hVL2 : ∀ n i : ℕ, MemLp (V n i) 2 μ := by
    intro n i
    refine MemLp.of_bound (hVm n i).aestronglyMeasurable (bn n) ?_
    filter_upwards [hVb n i] with ω hω
    rwa [Real.norm_eq_abs]
  have hbn0 : Tendsto bn atTop (𝓝 0) := by
    have := (tendsto_bigBlockLen_div_sqrt hh0 hh hnh).mul_const (2 * L * CW)
    simpa [hbndef] using this
  -- the row variances
  have hVvar : Tendsto (fun n : ℕ =>
      ∑ i : Fin (blockCount h δ lam n), variance (V n i) μ) atTop
      (𝓝 ((sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2)) := by
    have hblk := tendsto_blockVar_sum hmeasX hmeasE hstat hδ hmp hp0 hpd hpb hB0 hC2gen hlam
      hα hWm hWb hW1 hW2 hh0 hh hL mL sL hmLm hsLm hmLv hsLv hσLc hσLb hpc hpx hnh
    refine hblk.congr fun n => ?_
    rw [Fin.sum_univ_eq_sum_range (fun i => variance (V n i) μ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hv : variance (V n i) μ = ∫ ω, (V n i ω) ^ 2 ∂μ := by
      rw [variance_eq_sub (hVL2 n i)]
      simp only [hVmean n i]
      norm_num
    have hinv : ((Real.sqrt ((n : ℝ) * h n))⁻¹) ^ 2 = ((n : ℝ) * h n)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) (hh0 n).le)]
    rw [hv, ← integral_const_mul]
    refine (integral_congr_ae (Eventually.of_forall fun ω => ?_)).symm
    rw [hVdef]
    simp only [mul_pow, hinv, hζdef]
  -- step 1: the product of block charFuns
  have hstep1 := tendsto_prod_charFun_of_uniformly_small (μ := μ)
    (Y := fun n (i : Fin (blockCount h δ lam n)) => V n (i : ℕ))
    (fun n i => hVm n i) (fun n i => hVmean n i) (fun n i => hVL2 n i)
    (fun n i => hVb n i) hbn0 hVvar u
  -- step 2: Volkonskii–Rozanov
  have hstep2 : Tendsto (fun n : ℕ =>
      ‖charFun (μ.map (fun ω => ∑ i : Fin (blockCount h δ lam n), V n (i : ℕ) ω)) u
        - ∏ i : Fin (blockCount h δ lam n), charFun (μ.map (V n (i : ℕ))) u‖)
      atTop (𝓝 0) := by
    have hα0 : ∀ n : ℕ, (0 : ℝ) ≤ pairAlphaCoeff X e μ (smallBlockLen h δ lam n) :=
      fun n => pairAlphaCoeff_nonneg X e _
    have hmaj : Tendsto (fun n : ℕ => 16 * ((blockCount h δ lam n : ℝ) *
        pairAlphaCoeff X e μ (smallBlockLen h δ lam n))) atTop (𝓝 0) := by
      simpa using (tendsto_blockCount_mul_pairAlpha hδ hlam hα hh0 hh hnh).const_mul 16
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmaj
    filter_upwards [eventually_blockCount_pos hh0 hh hnh hδ hlam] with n hkn
    refine (norm_charFun_blockSum_sub_prod_le hmeasX hmeasE hstat hWm (L := L) n hkn u).trans ?_
    have hk1 : (1 : ℝ) ≤ (blockCount h δ lam n : ℝ) := by exact_mod_cast hkn
    nlinarith [hα0 n]
  -- step 3: the discarded indices
  have hstep3 : Tendsto (fun n : ℕ =>
      ‖charFun (μ.map (locTruncSum X e μ W x h L n)) u
        - charFun (μ.map (fun ω => ∑ i : Fin (blockCount h δ lam n), V n (i : ℕ) ω)) u‖)
      atTop (𝓝 0) := by
    set R : ℕ → Finset ℕ := fun n => Finset.range n \ bigBlockIdx h δ lam n with hRdef
    set D : ℕ → Ω → ℝ := fun n ω =>
      (Real.sqrt ((n : ℝ) * h n))⁻¹ * ∑ t ∈ R n, ζ n t ω with hDdef
    have hDm : ∀ n, Measurable (D n) := fun n =>
      (Finset.measurable_sum _ fun t _ => hζm n t).const_mul _
    have hDrep : ∀ n : ℕ, ∀ ω,
        locTruncSum X e μ W x h L n ω
          - (∑ i : Fin (blockCount h δ lam n), V n (i : ℕ) ω) = D n ω := by
      intro n ω
      have hbig : ∑ i : Fin (blockCount h δ lam n), V n (i : ℕ) ω
          = (Real.sqrt ((n : ℝ) * h n))⁻¹ * ∑ t ∈ bigBlockIdx h δ lam n, ζ n t ω := by
        rw [Fin.sum_univ_eq_sum_range (fun i => V n i ω), hVdef]
        simp only
        rw [← Finset.mul_sum, bigBlockIdx]
        congr 1
        exact (Finset.sum_biUnion (bigBlockIdx_pairwiseDisjoint h δ lam n)).symm
      have hsplit : (∑ t ∈ R n, ζ n t ω) + (∑ t ∈ bigBlockIdx h δ lam n, ζ n t ω)
          = ∑ t ∈ Finset.range n, ζ n t ω :=
        Finset.sum_sdiff (bigBlockIdx_subset h δ lam n)
      rw [hbig, hDdef]
      simp only [locTruncSum, hζdef]
      rw [← hsplit]
      ring
    have hDL2 : ∀ n, MemLp (D n) 2 μ := by
      intro n
      refine MemLp.of_bound (hDm n).aestronglyMeasurable
        ((Real.sqrt ((n : ℝ) * h n))⁻¹ * ((R n).card : ℝ) * (2 * L * CW)) ?_
      have hall : ∀ᵐ ω ∂μ, ∀ t ∈ R n, |ζ n t ω| ≤ 2 * L * CW :=
        (Filter.eventually_all_finset _).2 fun t _ => hζb n t
      filter_upwards [hall] with ω hω
      have hsum : |∑ t ∈ R n, ζ n t ω| ≤ ((R n).card : ℝ) * (2 * L * CW) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        have := Finset.sum_le_card_nsmul _ (fun t => |ζ n t ω|) (2 * L * CW) hω
        simpa [nsmul_eq_mul] using this
      rw [Real.norm_eq_abs, hDdef]
      simp only [abs_mul, abs_of_nonneg (hsq0 n)]
      calc (Real.sqrt ((n : ℝ) * h n))⁻¹ * |∑ t ∈ R n, ζ n t ω|
          ≤ (Real.sqrt ((n : ℝ) * h n))⁻¹ * (((R n).card : ℝ) * (2 * L * CW)) :=
            mul_le_mul_of_nonneg_left hsum (hsq0 n)
        _ = (Real.sqrt ((n : ℝ) * h n))⁻¹ * ((R n).card : ℝ) * (2 * L * CW) := by ring
    have hDsq : Tendsto (fun n => ∫ ω, (D n ω) ^ 2 ∂μ) atTop (𝓝 0) := by
      have hIsub : ∀ n, R n ⊆ Finset.range n := fun n => Finset.sdiff_subset
      have hIcard := tendsto_restIdx_card hh0 hh hnh hδ hlam
      have hvar := tendsto_truncArray_variance hmeasX hmeasE hstat hδ hmp hp0 hpd hpb hB0
        hC2gen hlam hα hWm hWb hW1 hW2 hh0 hh hL mL sL hmLm hsLm hmLv hsLv hσLc hσLb hpc hpx
        R hIsub (a := 0) hIcard
      rw [zero_mul] at hvar
      refine hvar.congr fun n => ?_
      have hinv : ((Real.sqrt ((n : ℝ) * h n))⁻¹) ^ 2 = ((n : ℝ) * h n)⁻¹ := by
        rw [inv_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg n) (hh0 n).le)]
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      rw [hDdef]
      simp only [mul_pow, hinv, hζdef]
    have hL1 := tendsto_integral_abs_of_tendsto_sq hDL2 hDsq
    have hTm : ∀ n : ℕ, Measurable (locTruncSum X e μ W x h L n) := by
      intro n
      exact (Finset.measurable_sum _ fun t _ => hζm n t).const_mul _
    have hSm : ∀ n : ℕ, Measurable
        (fun ω => ∑ i : Fin (blockCount h δ lam n), V n (i : ℕ) ω) :=
      fun n => Finset.measurable_sum _ fun i _ => hVm n i
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      (by simpa using hL1.const_mul |u|)
    filter_upwards with n
    have hi : Integrable (fun ω => |locTruncSum X e μ W x h L n ω
        - (∑ i : Fin (blockCount h δ lam n), V n (i : ℕ) ω)|) μ := by
      have := ((hDL2 n).integrable (by norm_num)).abs
      refine this.congr ?_
      filter_upwards with ω
      rw [hDrep n ω]
    have := norm_charFun_map_sub_le' (hTm n).aemeasurable (hSm n).aemeasurable hi u
    refine this.trans (le_of_eq ?_)
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show |locTruncSum X e μ W x h L n ω
        - (∑ i : Fin (blockCount h δ lam n), V n (i : ℕ) ω)| = |D n ω|
    rw [hDrep n ω]
  -- combine
  have hcomb := (tendsto_zero_iff_norm_tendsto_zero.2 hstep3).add
    ((tendsto_zero_iff_norm_tendsto_zero.2 hstep2).add hstep1)
  rw [zero_add, zero_add] at hcomb
  refine hcomb.congr fun n => ?_
  ring

/-- **FY (2.77)–(2.81) + (2.84), the fixed-level limit — DEBT.** For each truncation
level `L` the truncated statistic is asymptotically `N(0, ν_L)`, and `ν_L → σ²(x) p(x) ∫W²`.

This is the Bernstein-block core of §2.7.7: split `locTruncSum` into `k_n` big blocks
of length `l_n`, `k_n` small blocks of length `s_n` and a remainder; the small blocks
and remainder are `L²`-negligible (`tendsto_smallBlock_variance`); the big blocks
factorize up to `16 (k_n − 1) α_pair(s_n) → 0` by Volkonskii–Rozanov
(`norm_integral_prod_sub_prod_integral_le` with `tendsto_blockCount_mul_pairAlpha`);
and the resulting product of block charFuns converges by the degenerate-Lindeberg
corollary `tendsto_charFun_rowSum_gaussian_of_uniformly_small` — applicable because the
truncated block summands carry the envelope `l_n L CW / √(n h_n) → 0`, which is exactly
why `l_n = [√(n h_n)/log n]` is chosen. The block-variance input is ledger (a).

**Status.** All three blocking inputs are cleared: (i) ledger (a) (`var_localized_sum`, and
its truncated analogue `tendsto_truncArray_variance` built here), (ii)
`tendsto_smallBlock_variance`, (iii) the Volkonskii–Rozanov factorization
(`norm_integral_prod_sub_prod_integral_le_of_pos` in `Mixing/Inequalities.lean`; the frozen
`norm_integral_prod_sub_prod_integral_le` keeps only its false `k = 0` corner, and every
consumer here has `k = k_n ≥ 1`). Its *rate* input (2.78) is
`tendsto_blockCount_mul_pairAlpha`.

**FALSE AS FROZEN (verified) — REPAIRED.** (This superseded the earlier "statement
survives the audit intact" verdict.) The obstruction is *independent* of inputs (i)–(iii): the
conclusion is refutable even for an **iid** series, where the Bernstein blocking is
unnecessary and every one of (i)–(iii) is trivial. The point is that the hypotheses
constrain the conditional law of `e_0` given `X_0` only through its first two moments
(`hce`, `hcv`) and a δ-th moment bound (`heδc`), whereas the conclusion at a **fixed**
truncation level `L` sees the conditional law of `clamp_L(e_0)` given `X_0` — a different
functional, on which no regularity at `x` has been assumed.

*Witness.* Take `(X_t, e_t)` iid (so `pairAlphaCoeff X e μ t = 0` for `t ≥ 1` and `hα`
holds for any `lam`; take `δ = 3`, `lam = 1`, so `hδ`, `hlam` hold), `X_0` uniform on
`[0,1]` (`p = 1_{[0,1]}`, `x = 1/2`: `hmp`, `hp0`, `hpd`, `hpc`, `hpx`, `hpb` with
`Cp = 1`), `W = 1_{[1,2]}` (`hWm`, `hWb` with `C_W = 1`, `hW1`, `hW2`, `∫W² = 1`), and let
the conditional law of `e_0` given `X_0 = v` be `±c(v)` with probability `q(v)/2` each and
`0` with probability `1 − q(v)`, where `q(v) ∈ [1/4, 1/2]` and `c(v) = q(v)^{−1/2}`. Then
`E(e_0|X_0) = 0` (`hce`); `E(e_0²|X_0) = c²q = 1`, so `σ² ≡ 1` (`hcv`, `hσm`, `hσc`, and
`hσpb` with `C = 1`); `E(|e_0|³|X_0) = c³q = q^{−1/2} ≤ 2` (`heLδ`, `heδc` with `M = 2`);
and (C2) holds with `B = 1`, since for `j ≠ 0` independence factorizes
`E[|e_0 e_j| g(X_0,X_j)] = ∫∫ m(v) p(v) m(w) p(w) g` with
`m(v) = E(|e_0| | X_0 = v) = q(v)^{1/2} ≤ 1` and `E[e_0²] = 1`.

Now fix `L = 1`. As `c(v) ≥ √2 > 1`, `clamp_1(e_0)` is `±1` with probability `q(v)` and
its conditional mean vanishes, so `truncErr` has conditional variance `σ_1²(v) = q(v)` —
a function the hypotheses pin down only up to `q ∈ [1/4, 1/2]`. The summands of
`locTruncSum … 1 n` are iid, centred, bounded by `1`, with common variance
`h_n ∫ q(x + h_n u) W(u)² du`, so `Var (locTruncSum … 1 n) = ∫_1^2 q(x + h_n u) du =: V(h_n)`
and, the array being uniformly bounded by `2/√(n h_n) → 0`, the Lindeberg CLT gives
`charFun (μ.map (locTruncSum X e μ W x h 1 n)) u − exp(−u² V(h_n)/2) → 0`. Choose
`q(v) = 3/8 + (1/8) cos(2π log₂ |v − x|)`. Along `h = 2^{−k}` the phase is an integer
multiple of `2π`, so `V = 3/8 + (1/8) I`; along `h = 2^{−k−1/2}` the cosine flips sign, so
`V = 3/8 − (1/8) I`; and
`I = ∫_1^2 cos(2π log₂ u) du = (log 2)² / ((log 2)² + 4π²) > 0`. Interleaving the two
scales along a bandwidth sequence with `h_n → 0` and `n h_n³ → ∞` (e.g. `h_n` the nearer
of `2^{−k}`, `2^{−k−1/2}` to `n^{−1/4}`, alternating on long blocks — (C5) constrains only
the *rate*, not the scale) makes `V(h_n)` oscillate between two distinct values. Hence
`charFun (μ.map (locTruncSum … 1 n)) u` has no limit at any `u ≠ 0`, and **no** value of
`vT 1` can satisfy the first conclusion.

**Missing input, precisely.** FY's step (c) silently needs the diagonal (2.73) *for the
truncated errors*: continuity at `x` of `σ_L² · p` for each `L`, where
`σ_L²(v) = Var(clamp_L(e_0) | X_0 = v)`. This is a **fourth** silent reading of (C1),
independent of `hσm`/`hσpb` (which regularize only `σ² = σ_∞²`) and of `heδc`/`hpb` (which
bound only a δ-th moment). The economical repair is to assume that the conditional law of
`e_0` given `X_0 = v` converges weakly to the one at `v = x` as `v → x`, together with
uniform square-integrability along that limit: this yields continuity at `x` of `σ_L² · p`
for every `L` *and* FY's (2.84) `σ_L²(x) → σ²(x)` as `L → ∞`, which is the second
conclusion. Note that the **headline** `kernel_localized_clt` is *not* damaged by this: it
is an artifact of the truncation route only, and the untruncated variance asymptotics
`var_localized_sum` — which is what the headline's Gaussian limit is read off — is proved.

**Statement strengthening (documented).** The repair applied is exactly the missing input
above, in its most economical Lean form: measurable versions `mL L`, `sL L` of
`v ↦ E(clamp_L e_0 | X_0 = v)` and `v ↦ E(clamp_L(e_0)² | X_0 = v)` — whose existence is
Doob–Dynkin (`StronglyMeasurable.exists_eq_measurable_comp`), not an assumption — together
with the three genuine hypotheses on `σ_L² := sL L − (mL L)²`:
`hσLc` (continuity at `x` of `σ_L²·p`, which is the (2.73)-for-truncated-errors that the
witness above refutes as underivable), `hσLb` (`σ_L²·p` bounded, the level-`L` form of the
already-authorized `hσpb`), and `hσL84` (FY's (2.84) `σ_L²(x) → σ²(x)`, which is the second
conclusion; it is *not* implied by `hσLc` — a.e.-in-`v` convergence `σ_L² → σ²` plus
continuity of each factor at `x` says nothing about the value at the single point `x`).
All three are consequences of the one conceptual repair the witness identifies, namely that
the conditional law of `e_0` given `X_0 = v` converges weakly to the one at `v = x` as
`v → x` with uniform square-integrability; they are stated directly because that weak-limit
formulation is heavier and buys nothing else. The two (2.74) hypotheses `heδc`/`hpb` are
carried here solely because this statement consumes ledger (a); see `var_localized_sum`'s
docstring for the proof that they are not derivable from (C1)–(C5) as formalized.

**PROVED (this wave), in the repaired form.** The Bernstein-block core was run in full. The
private apparatus, in the order it is built above, is:
* `condExp_truncErr_sq` — `E((e^L_0)² | X_0) = sL L(X_0) − mL L(X_0)²`, i.e. the truncated
  array's conditional variance really is the `σ_L²` of the repair; with `truncErr_zero_repr`
  and `ae_abs_mL_le` (`|mL L| ≤ L` a.e., since `mL L` is a version of a conditional
  expectation of something bounded by `L`).
* `tendsto_truncDiag` — the (2.73) diagonal *for the truncated errors*, obtained from the
  proved `tendsto_localized_second_moment_debt` at `σ_L²`; note that `hσLc` gives continuity
  of the **product** `σ_L²·p` only, and continuity of `σ_L²` itself is recovered from it by
  dividing by `p`, which is legitimate exactly because `p` is continuous at `x` with
  `p x > 0`.
* `truncArray_core` / `tendsto_truncArray_variance` — the truncated analogue of the whole of
  ledger (a), over an **arbitrary** index family `I n ⊆ range n` with `|I n|/n → a`, with
  limit `a · σ_L²(x) p(x) ∫W²`. It is `tendsto_truncIndex_variance` with the diagonal
  *retained* (`abs_double_sum_subset_sub_diag_le`) instead of discarded; at `a = 1` it is
  FY's (2.77) variance and at `a = 0` it is the negligibility of the discarded indices.
* `pairAlphaCoeff_shift` — the **anchor-independence** of the pair α-coefficient, which the
  blocks need and which `pairAlphaCoeff` (anchored at `0`) does not give: the pair series is
  coded into a *real* series by a Borel isomorphism `ℝ × ℝ ≃ᵐ ℝ` (`pairCode`), whose one-time
  comap σ-algebra is exactly `σ(X_t) ⊔ σ(e_t)`; fdd stationarity of the pair upgrades to
  `IsStrictlyStationary` of the coded series (`map_tuple_shift`: an arbitrary finite tuple is
  covered by one contiguous window), and `IsStrictlyStationary.alphaMixCoeff_shift` of
  `Mixing/Relations.lean` applies.
* the big-block apparatus `bigBlockIdx` (+ disjointness, `bigBlockIdx_card = k_n l_n`, the
  bookkeeping identity `k l + k s + n mod (l+s) = n`) with the two new ratio limits
  `l_n/n → 0` and `s_n/n → 0` (the latter from (C5) through
  `tendsto_log_rpow_div_rpow_atTop`, exactly as in `tendsto_blockCount_mul_smallBlockLen_div`),
  giving `|range n \ bigBlockIdx|/n → 0` and `|bigBlockIdx|/n → 1`.
* `tendsto_blockVar_sum` — `Σ_j Var(Y_{n,j}) → σ_L²(x) p(x) ∫W²` for the big-block statistics,
  by applying the sub-diagonal double-sum estimate blockwise (the cross-block covariances are
  absorbed by the *same* lag sum `h⁻¹ Σ_{d≥1}|G(d)| → 0`).
* `norm_charFun_blockSum_sub_prod_le` — Volkonskii–Rozanov on the big blocks; the gap
  hypothesis is `α(σ_pair(Iic (jq+l)), σ_pair(Ici ((j+1)q+1))) ≤ α_pair(s_n)`, which is where
  `pairAlphaCoeff_shift` is consumed.
* `tendsto_prod_charFun_of_uniformly_small` — the row CLT in **product-of-charFuns** form,
  with *no* independence assumed. `tendsto_charFun_rowSum_gaussian_of_uniformly_small` is only
  available in its `iIndepFun` form (its product-form core is `private` in
  `ForMathlib/Probability/TriangularCLT.lean`), so the product `∏_j φ_{Y_{n,j}}(u)` is
  transported to an independent surrogate on `Measure.infinitePi` of the individual laws,
  where the theorem applies verbatim.
* `tendsto_bigBlockLen_div_sqrt` — the envelope `l_n/√(n h_n) → 0` (with `n h_n → ∞` from
  (C5)), which is what makes the block array uniformly negligible; and the `L² ⇒ L¹` glue
  `tendsto_integral_abs_of_tendsto_sq`.

The degenerate truncation levels `L ≤ 0` are handled separately: there `clamp_L ≡ −L` is
constant, so `truncErr ≡ 0` and the statistic is a.s. `0`; `vT` is defined to be `0` there, and
`gaussianReal 0 0 = δ_0` matches. -/
theorem tendsto_charFun_locTruncSum [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ : ℝ} {x : ℝ}
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT (authorized (C1) repair): σ² measurable; FY §2.6.4
    (hσm : Measurable σsq)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {M Cp : ℝ}
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (hpb : ∀ v, p v ≤ Cp)
    -- USER-INPUT ((C1)-family — the **fourth** silent reading, identified by the witness
    -- in `tendsto_charFun_locTruncSum`'s docstring): the conditional law of `e_0` given
    -- `X_0 = v` is regular at `v = x` at *every* truncation level. `mL L` and `sL L` are
    -- measurable versions of `v ↦ E(clamp_L e_0 | X_0 = v)` and
    -- `v ↦ E(clamp_L(e_0)² | X_0 = v)` — their mere existence is Doob–Dynkin, not an
    -- assumption; the content is `hσLc` (continuity at `x` of `σ_L²·p`), `hσLb` (`σ_L²·p`
    -- bounded, the level-`L` form of `hσpb`) and `hσL84` (FY's (2.84)). FY §2.6.4
    (mL sL : ℝ → ℝ → ℝ)
    (hmLm : ∀ L : ℝ, Measurable (mL L)) (hsLm : ∀ L : ℝ, Measurable (sL L))
    (hmLv : ∀ L : ℝ, 0 < L →
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv : ∀ L : ℝ, 0 < L →
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ∀ L : ℝ, 0 < L → ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∀ L : ℝ, 0 < L → ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hσL84 : Tendsto (fun L : ℝ => sL L x - mL L x ^ 2) atTop (𝓝 (σsq x)))
    -- (C2) USER-INPUT: (C2) as printed (conditional joint density bounded); FY §2.6.4
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ} (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ} (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ} (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop) (u : ℝ) :
    ∃ vT : ℝ → ℝ,
      (∀ L : ℝ, Tendsto (fun n : ℕ => charFun (μ.map (locTruncSum X e μ W x h L n)) u)
          atTop (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (vT L))) u)))
      ∧ Tendsto (fun L : ℝ => charFun (gaussianReal 0 (Real.toNNReal (vT L))) u) atTop
          (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
            (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume))) u)) := by
  classical
  obtain ⟨B, hB0, hC2gen⟩ := hC2
  set vT : ℝ → ℝ := fun L =>
    if 0 < L then (sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2 else 0 with hvTdef
  refine ⟨vT, ?_, ?_⟩
  · intro L
    rcases lt_or_ge 0 L with hL | hL
    · have hpos := tendsto_charFun_locTruncSum_pos hmeasX hmeasE hstat hδ hmp hp0 hpd hpb
        hB0 hC2gen hlam hα hWm hWb hW1 hW2 hh0 hh hL mL sL hmLm hsLm (hmLv L hL) (hsLv L hL)
        (hσLc L hL) (hσLb L hL) hpc hpx hnh u
      rw [hvTdef]
      simpa only [if_pos hL] using hpos
    · -- degenerate truncation levels: the statistic vanishes
      have hclampconst : ∀ z : ℝ, clampAt L z = -L := by
        intro z
        unfold clampAt
        rcases le_or_gt z L with hz | hz
        · rw [min_eq_right hz]
          exact max_eq_left (by linarith)
        · rw [min_eq_left hz.le]
          exact max_eq_left (by linarith)
      have htr0 : ∀ t : ℤ, truncErr X e μ L t =ᵐ[μ] fun _ => (0 : ℝ) := by
        intro t
        have hfun : (fun ω' => clampAt L (e t ω')) = fun _ : Ω => -L :=
          funext fun ω' => hclampconst _
        have hce0 : μ[fun ω' => clampAt L (e t ω') |
            MeasurableSpace.comap (X t) inferInstance] = fun _ => -L := by
          rw [hfun, condExp_const (hmeasX t).comap_le]
        filter_upwards with ω
        have hdef : truncErr X e μ L t ω = clampAt L (e t ω)
            - (μ[fun ω' => clampAt L (e t ω') |
              MeasurableSpace.comap (X t) inferInstance]) ω := rfl
        rw [hdef, hce0, hclampconst]
        simp
      have hzero : ∀ n : ℕ, locTruncSum X e μ W x h L n =ᵐ[μ] fun _ => (0 : ℝ) := by
        intro n
        have hall : ∀ᵐ ω ∂μ, ∀ t ∈ Finset.range n, truncErr X e μ L ((t : ℤ) + 1) ω = 0 :=
          (Filter.eventually_all_finset _).2 fun t _ => htr0 ((t : ℤ) + 1)
        filter_upwards [hall] with ω hω
        have hs : ∑ t ∈ Finset.range n, truncErr X e μ L ((t : ℤ) + 1) ω *
            W ((X ((t : ℤ) + 1) ω - x) / h n) = 0 :=
          Finset.sum_eq_zero fun t ht => by rw [hω t ht, zero_mul]
        simp only [locTruncSum, hs, mul_zero]
      have hmap : ∀ n : ℕ, μ.map (locTruncSum X e μ W x h L n) = Measure.dirac (0 : ℝ) := by
        intro n
        rw [Measure.map_congr (hzero n)]
        simp
      have hvT0 : vT L = 0 := by rw [hvTdef]; simp only [if_neg (not_lt.2 hL)]
      rw [hvT0]
      have hgauss : charFun (gaussianReal 0 (Real.toNNReal (0 : ℝ))) u
          = charFun (Measure.dirac (0 : ℝ)) u := by
        rw [Real.toNNReal_zero, gaussianReal_zero_var]
      rw [hgauss]
      refine tendsto_const_nhds.congr fun n => ?_
      rw [hmap n]
  · -- (2.84): the level-`L` variance converges to `σ²(x) p(x) ∫W²`
    have hcont : Continuous (fun w : ℝ => charFun (gaussianReal 0 (Real.toNNReal w)) u) := by
      have hrw : (fun w : ℝ => charFun (gaussianReal 0 (Real.toNNReal w)) u)
          = fun w : ℝ => Complex.exp ((u : ℂ) * (0 : ℂ) * Complex.I
            - ((Real.toNNReal w : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
        funext w
        rw [charFun_gaussianReal]
        norm_num
      rw [hrw]
      fun_prop
    have hvTlim : Tendsto vT atTop (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) := by
      have hbase : Tendsto (fun L : ℝ => (sL L x - mL L x ^ 2) * p x * ∫ v, W v ^ 2) atTop
          (𝓝 (σsq x * p x * ∫ v, W v ^ 2)) :=
        (hσL84.mul_const (p x)).mul_const (∫ v, W v ^ 2)
      refine hbase.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [hvTdef]
      simp only [if_pos hL]
    exact (hcont.tendsto _).comp hvTlim

end Ledger

/-- **FY Theorem 2.22** (charFun form): under (C1)–(C5),
`(n h_n)^{-1/2} Σ_{t=1}^n e_t W((X_t − x)/h_n) →d N(0, σ²(x) p(x) ∫ W²)`.

**Statement strengthening (documented).** Four groups of hypotheses beyond the printed
(C1)–(C5) are carried, each a silent reading of (C1)–(C2) that FY's own proof uses, and
each documented with an explicit proof that it is *not* derivable from the frozen
conditions:
* `hσm` (`σ²` measurable — the printed (C1) constrains `σ²` only through `hcv`, hence only
  `μ.map (X 0)`-a.e.) and `hσpb` (`σ²·p` bounded), needed for the diagonal (2.73); see
  `tendsto_localized_second_moment_debt` (spike/kernel counterexample).
* `heδc`/`hpb` — FY's implicit (2.74), the *conditional* δ-th moment
  `E(|e_0|^δ | X_0) ≤ M` together with a bounded density — needed for the large-lag half of
  the variance asymptotics; see `var_localized_sum` (interpolation of the available inputs
  converges only for `λ > 1`, whereas (C3) allows `λ ∈ (1 − 2/δ, 1]`).
* (C2) is carried **as printed** — the integrated bounded-conditional-density inequality at
  an *arbitrary* error weight `f`, not just at `f = e_0 e_j`. The frozen single instance is
  strictly weaker and does not close steps (b)–(c): the conditional recentring inside
  `truncErr` strips both error factors out of the small-lag covariance. See
  `tendsto_smallBlock_variance` for the proof.
* `mL`/`sL` with `hσLc`, `hσLb`, `hσL84` — the *truncated* conditional second moment
  `σ_L² = sL L − (mL L)²` is regular at `x`, and FY's (2.84) holds. This is a **fourth**
  reading of (C1), independent of the first two (which regularize `σ² = σ_∞²` only), and it
  is what step (c) needs at each fixed truncation level; see
  `tendsto_charFun_locTruncSum` for the iid witness that refutes the statement without it.

Note that the *Gaussian limit itself* is untouched by the last item: it is read off the
untruncated variance asymptotics `var_localized_sum`, which is proved. -/
theorem kernel_localized_clt [IsProbabilityMeasure μ]
    {X e : ℤ → Ω → ℝ} (hmeasX : ∀ t, Measurable (X t)) (hmeasE : ∀ t, Measurable (e t))
    -- (C1) USER-INPUT: joint strict stationarity (fdd form); FY (C1)
    (hstat : ∀ (k : ℕ) (t : ℤ),
      μ.map (fun ω (i : Fin k) => (X (t + (i : ℕ)) ω, e (t + (i : ℕ)) ω))
        = μ.map (fun ω (i : Fin k) => (X ((i : ℕ) : ℤ) ω, e ((i : ℕ) : ℤ) ω)))
    {σsq p : ℝ → ℝ} {δ : ℝ} {x : ℝ}
    -- (C1) USER-INPUT: E(e₁ | X₁) = 0; FY (C1)
    (hce : μ[e 0 | MeasurableSpace.comap (X 0) inferInstance] =ᵐ[μ] 0)
    -- (C1) USER-INPUT: E(e₁² | X₁) = σ²(X₁); FY (C1)
    (hcv : μ[fun ω => e 0 ω ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
      =ᵐ[μ] fun ω => σsq (X 0 ω))
    -- (C1) USER-INPUT: δ-moment of the errors, δ > 2; FY (C1)
    (hδ : 2 < δ) (heLδ : MemLp (e 0) (ENNReal.ofReal δ) μ)
    -- (C1) USER-INPUT: σ² measurable (the frozen (C1) omits it); FY (C1)
    (hσm : Measurable σsq)
    -- (C1) USER-INPUT: X₁ has Lebesgue density p; FY (C1)
    (hmp : Measurable p) (hp0 : ∀ v, 0 ≤ p v)
    (hpd : μ.map (X 0) = MeasureTheory.volume.withDensity fun v => ENNReal.ofReal (p v))
    -- (C1) USER-INPUT: continuity at x and positivity; FY (C1)
    (hσc : ContinuousAt σsq x) (hpc : ContinuousAt p x) (hpx : 0 < p x)
    -- USER-INPUT: σ²·p bounded (the textbook's silent reading of (C1)); FY §2.6.4
    (hσpb : ∃ C : ℝ, ∀ v : ℝ, σsq v * p v ≤ C)
    {M Cp : ℝ}
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (heδc : μ[fun ω => |e 0 ω| ^ δ | MeasurableSpace.comap (X 0) inferInstance]
      ≤ᵐ[μ] fun _ => M)
    -- USER-INPUT: (2.74) δ-th conditional moment of the error, FY's silent reading of
    -- (C1); FY §2.6.4
    (hpb : ∀ v, p v ≤ Cp)
    -- USER-INPUT ((C1)-family — the **fourth** silent reading, identified by the witness
    -- in `tendsto_charFun_locTruncSum`'s docstring): the conditional law of `e_0` given
    -- `X_0 = v` is regular at `v = x` at *every* truncation level. `mL L` and `sL L` are
    -- measurable versions of `v ↦ E(clamp_L e_0 | X_0 = v)` and
    -- `v ↦ E(clamp_L(e_0)² | X_0 = v)` — their mere existence is Doob–Dynkin, not an
    -- assumption; the content is `hσLc` (continuity at `x` of `σ_L²·p`), `hσLb` (`σ_L²·p`
    -- bounded, the level-`L` form of `hσpb`) and `hσL84` (FY's (2.84)). FY §2.6.4
    (mL sL : ℝ → ℝ → ℝ)
    (hmLm : ∀ L : ℝ, Measurable (mL L)) (hsLm : ∀ L : ℝ, Measurable (sL L))
    (hmLv : ∀ L : ℝ, 0 < L →
      μ[fun ω => max (-L) (min L (e 0 ω)) | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => mL L (X 0 ω))
    (hsLv : ∀ L : ℝ, 0 < L →
      μ[fun ω => max (-L) (min L (e 0 ω)) ^ 2 | MeasurableSpace.comap (X 0) inferInstance]
        =ᵐ[μ] fun ω => sL L (X 0 ω))
    (hσLc : ∀ L : ℝ, 0 < L → ContinuousAt (fun v => (sL L v - mL L v ^ 2) * p v) x)
    (hσLb : ∀ L : ℝ, 0 < L → ∃ C : ℝ, ∀ v : ℝ, (sL L v - mL L v ^ 2) * p v ≤ C)
    (hσL84 : Tendsto (fun L : ℝ => sL L x - mL L x ^ 2) atTop (𝓝 (σsq x)))
    -- (C2) USER-INPUT: (C2) as printed (conditional joint density bounded); FY §2.6.4
    (hC2 : ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℤ, j ≠ 0 → ∀ f : ℝ × ℝ → ℝ, Measurable f →
      ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ v, 0 ≤ g v) →
      ∫ ω, |f (e 0 ω, e j ω)| * g (X 0 ω, X j ω) ∂μ
        ≤ B * (∫ ω, |f (e 0 ω, e j ω)| ∂μ) *
          ∫ v, g v ∂(MeasureTheory.volume.prod MeasureTheory.volume))
    {lam : ℝ}
    -- (C3) USER-INPUT: α-mixing rate of the pair series; FY (C3)
    (hlam : 1 - 2 / δ < lam)
    (hα : Summable fun t : ℕ => (t : ℝ) ^ lam * pairAlphaCoeff X e μ t ^ (1 - 2 / δ))
    {W : ℝ → ℝ} {CW : ℝ}
    -- (C4) USER-INPUT: bounded, integrable kernel with square-integrability; FY (C4)
    (hWm : Measurable W) (hWb : ∀ v, |W v| ≤ CW)
    (hW1 : Integrable W MeasureTheory.volume)
    (hW2 : Integrable (fun v => W v ^ 2) MeasureTheory.volume)
    {h : ℕ → ℝ}
    -- (C5) USER-INPUT (corrected form — printed display inverted): bandwidths
    -- positive, h → 0, n h³ → ∞; FY (C5)
    (hh0 : ∀ n, 0 < h n) (hh : Tendsto h atTop (𝓝 0))
    (hnh : Tendsto (fun n : ℕ => (n : ℝ) * h n ^ 3) atTop atTop)
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt ((n : ℝ) * h n))⁻¹ *
          ∑ t ∈ Finset.range n, e ((t : ℤ) + 1) ω * W ((X ((t : ℤ) + 1) ω - x) / h n)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σsq x * p x * ∫ v, W v ^ 2 ∂MeasureTheory.volume))) u)) := by
  -- Step (d): the four-term telescope, run through the abstract diagonal device.
  -- `L` is the truncation level; the uniform-in-`n` approximation is the truncation
  -- tail (2.82)–(2.83), the fixed-`L` limits are the Bernstein-block core
  -- (2.77)–(2.81), and their `L → ∞` limit is the variance continuity (2.84).
  obtain ⟨vT, hvT1, hvT2⟩ :=
    tendsto_charFun_locTruncSum hmeasX hmeasE hstat (σsq := σsq) (p := p) hce hcv hδ heLδ
      hσm hmp hp0 hpd hσc hpc hpx hσpb heδc hpb mL sL hmLm hsLm hmLv hsLv hσLc hσLb
      hσL84 hC2 hlam hα hWm hWb hW1 hW2 hh0 hh hnh u
  exact tendsto_of_uniform_approx
    (charFun_locSum_sub_locTruncSum_le hmeasX hmeasE hstat (σsq := σsq) (p := p) hce hcv hδ
      heLδ hσm hmp hp0 hpd hσc hpc hpx hσpb heδc hpb hC2 hlam hα hWm hWb hW1 hW2 hh0 hh hnh u)
    hvT1 hvT2

end StatLean.TimeSeries
