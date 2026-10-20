module
public import StatLean.TimeSeries.ARMA.Consistency
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.BrownCLT
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
-- Consumed only by the falsity witness `ls_yw_mle_equivalent_debt_false` below: the
-- coordinate white noise on `(ℤ → ℝ, ⊗ N(0,1))`.
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# Hannan's theorem: asymptotic normality of the ARMA Gaussian MLE (FY Theorem 3.2)

The head of the commissioned Hannan program (ledger (a), batches C–D): for a
stationary causal invertible ARMA(p, q) with **iid** noise and coprime minimal orders,
any measurable approximate-MLE sequence over a compact identifiable region satisfies

`√T (θ̂_T − θ₀) →d N(0, W)`, `W = (hannanVarZBack b₀ a₀)⁻¹` (FY eq. (3.14)),

where `hannanVarZBack` is the covariance of the score vector `Z_t = (U_{t−1−i},
V_{t−1−j})` — see FINDING 26 at `hannanScore_brownInputs` and the orientation repair
recorded there (wave `ts/f1c-hannan-orientation`): the file used to write the *forward*
Gram `hannanVarZ` here, which is a different quadratic form as soon as `p, q ≥ 1` and
`max (p, q) ≥ 2`.

Stated in Cramér–Wold/charFun form, together with `σ̂² →p σ²`. FY's remarks are
honored: **no fourth moment is required**, and the noise assumption is exactly iid
(the martingale-difference weakening is future work, not stated).

**The whole of that head has been removed** — see **Removed** immediately below. What
this module still delivers is `hannan_sigma2_consistent` (`σ̂² →p σ²`), the `samplePACF`
definition, and the machine-checked falsity witness `ls_yw_mle_equivalent_debt_false`.
Everything from the *Assembly plan* paragraph onwards is kept verbatim as the historical
record of the route and its findings; read it as history, not as an inventory of what the
file contains.

**Removed (2026-08-10, user directive).** The three sorried declarations of this module,
the two headline theorems proved from them, and — transitively — the 41 `private`
declarations left with no surviving consumer, were deleted. This is by far the largest
deletion of the sweep: the entire `ScoreCLT` section (the score martingale, the three
Brown inputs and the averaged Lindeberg condition) went with it, because every path out of
it ran through one of the two headlines.

*Sorried (the three listed in the directive):*
* `armaMLE_linearization` — the Taylor/sandwich linearization of the approximate MLE
  against the score sum, the analytic core of FY Thm 3.2.
* `samplePACF_linearization` — the delta-method linearization of the sample PACF, with
  its variance normalisation `dᵀ W_k d = 1`.
* `ls_yw_mle_equivalent_debt` — B&D Thm 10.8.2 / FY §3.3.2: LS, Yule–Walker and Gaussian
  MLE for a causal AR(p) are `√T`-asymptotically equivalent (repaired two-conjunct form).

*Headline consumers:*
* `hannan_mle_clt` — **FY Theorem 3.2 (Hannan)**, Cramér–Wold/charFun form:
  `√T (θ̂_T − θ₀) →d N(0, W)` with `W = (hannanVarZBack b₀ a₀)⁻¹`. Proved from
  `armaMLE_linearization`.
* `samplePACF_clt` — **FY Proposition 3.1**: `√T π̂(k) →d N(0, 1)` for a causal AR(p) at
  lag `k > p`. Proved from `samplePACF_linearization`.

*`private`, proved, and left without a consumer* (all grep-verified; a survivor-reference
audit confirmed the cut is clean): the charFun bricks `charFun_map_eq_integral`,
`integrable_cexp_mul_I`, `norm_cexp_sub_cexp_le`, `tendsto_charFun_of_tendstoInProb_sub`;
the filtration/linear-process bricks `comap_le_sigmaLT'`, `sigmaLT_le'`,
`measurable_sigmaLT'`, `sigmaLT_mono'`, `arPoly_neg'`, `noRootClosedDisc_neg'`,
`exists_adapted_isLinearProcessOf`, `sum_range_shiftSeq_mul`, `isLinearProcessOf_comb`,
`isLinearProcessOf_unique`; the score apparatus `scoreSeq`, `scoreVec`,
`scoreVec_eq_comb`, `measurable_scoreVec`, `isLinearProcessOf_scoreVec`,
`integral_noise_sq`, `condExp_noise_mul_sq`, `hannanScore_condVar_lln`,
`memLp_noise_mul_of_adapted`, `memLp_scoreSeqS`; the Lindeberg apparatus `lindTrunc`,
`lindTrunc_nonneg`, `lindTrunc_le_sq`, `measurable_lindTrunc`, `lindTrunc_mul_le`,
`setIntegral_sq_eq_integral_lindTrunc`, `tendsto_integral_lindTrunc`,
`identDistrib_of_isStrictlyStationary`, `lindeberg_noise_mul`, `hannanScore_lindeberg`;
the Brown inputs and the score CLT `hannanScore_brownInputs_back`,
`hannanScore_brownInputs`, `hannanScore_clt`; and the PACF helpers `sum_padCoeff`,
`arPoly_pad`, `measurable_samplePACF`.

*Kept:* `hannan_sigma2_consistent` and its three `private` inputs
(`armaContrastVar_self`, `armaProfileS_atTruth_tendstoInProb`,
`armaProfileS_equicontinuous`), the two measure-splitting bricks, the `samplePACF`
definition, `measurable_inv_mulVec`/`measurable_sampleACVF`, and the whole
`ls_yw_mle_equivalent_debt_false` witness block with its white-noise instance.

Recover from `bdc8143f`.

The two items that used to be listed here alongside the above — FY Proposition 3.1 and
the LS = YW = MLE equivalence (B&D Thm 10.8.2), together with the reciprocal-variance
identity `(Γ_k⁻¹)_{kk} = σ⁻²` for `k > p` — are exactly what went.

**Assembly plan** (lane prompt carries detail): consistency (`mle_consistent`) +
score MDS (`armaScore_condexp_zero` + Brown `mds_clt_sequence`) + Hessian/information
LLN + the standard Taylor/sandwich argument on the profiled criterion.

**Status of the assembly** (wave `ts/d-hannan-assembly`). All three headline theorems
are *assembled*: their proofs run end to end over named `private` debts, which are
listed here with their exact blockers.

* Proved outright: the charFun bricks (`tendsto_charFun_of_tendstoInProb_sub`, the
  charFun form of Slutsky), `exists_adapted_isLinearProcessOf` (conditional expectation
  turns a linear process into an *adapted* one — `exists_isLinearProcessOf` alone does
  not, and Brown's CLT needs adaptedness), `hannanScore_clt` (the Brown CLT genuinely
  wired along the noise filtration), the padding lemmas and measurability of
  `samplePACF`, and the three assemblies.
* The **variance algebra** of the sandwich is carried out symbolically in the
  `ScoreCLT` section docstring; it collapses to `W⁻¹ = (hannanVarZBack b₀ a₀)⁻¹`.
* Debts (after wave `ts/f1c-hannan-orientation`, 2026-08-09): `armaMLE_linearization`,
  `samplePACF_linearization`. **`hannanScore_brownInputs` is CLOSED** (see below).
  **FINDING 26 (wave `ts/f1b-arma-deep`, 2026-08-09): `hannanVarZ` is the covariance of
  the FORWARD auxiliary vector, while the score contracts the BACKWARD one `Z_t =
  (U_{t−1−i}, V_{t−1−j})`; the two Grams read the AR–MA cross-block at opposite lags and
  differ whenever `p, q ≥ 1` and `max (p, q) ≥ 2`** (machine witness:
  `ScoreAnalysis.hannanVarZ_quadForm_ne_back`, at ARMA(2,1)).
  **ORIENTATION REPAIR APPLIED (wave `ts/f1c-hannan-orientation`, 2026-08-09).** Every
  statement in the chain that asserted a `hannanVarZ` covariance for the score now
  asserts the `hannanVarZBack` one: `hannanScore_brownInputs`(2), `hannanScore_clt`,
  `armaMLE_linearization`, `samplePACF_linearization`, and the headline
  `hannan_mle_clt`, whose asymptotic covariance is now `(hannanVarZBack b₀ a₀)⁻¹`.
  `hannanVarZ` itself is untouched (it is a correct object — the forward Gram — and
  `hannanVarZ_posDef` stands); what the repair supplies is its twin
  `ScoreAnalysis.hannanVarZBack_posDef`, proved by re-running the Bézout/degree argument
  at the score's shifts. The pure-AR and pure-MA instantiations are unaffected either way
  (`hannanVarZ_eq_back_of_pure_ar`, `..._of_pure_ma`).
  **`hannanScore_brownInputs` is now PROVED**: items (1) and (2) are
  `hannanScore_brownInputs_back`, item (3) is the new `hannanScore_lindeberg`.
  **CLOSED**: `armaProfileS_atTruth_tendstoInProb` (a two-line corollary of Consistency's
  now-public `armaProfileS_tendstoInProb`) and `armaProfileS_equicontinuous` (a one-line
  corollary of `Consistency.armaProfileS_locallyEquicontinuous`).
  `ARMA/Consistency.lean` is now `sorry`-free — `mle_consistent` is PROVED — and it
  exports the generic one-filter LLN `linearProcess_avgSq_tendstoInProb`, which is the
  analytic brick all three remaining debts were blocked on. Each of them now carries a
  status note naming exactly what is left; the short version is: an `L²`-limit
  past-measurability step (score `L²` and the conditional-variance identity), the
  `private` `hannanVec`/`hannanVarZ_quadForm` chain in `ARMA/ScoreAnalysis.lean` (a new
  scope blocker), an identical-distribution transfer for the Lindeberg input, and the
  Taylor/delta-method bookkeeping of the last two debts.
  The "**pointwise ergodic theorem**" diagnosis is **WITHDRAWN** (2026-08-08/09):
  `ARMA/Consistency.lean`'s `armaResidualSS_tendstoInProb` proved the pointwise LLN
  ergodic-theorem-free, and the *uniform* half is a deterministic θ-modulus estimate,
  not an ergodic statement — see `armaProfileS_equicontinuous` below, where the
  geometric-bound brick and the `ℓ¹` modulus of `π` are now available as
  `Consistency.exists_uniform_geometric_bound_arma` and
  `Consistency.exists_armaPi_l1_modulus`.
  The scope blocker that used to sit here — `ARMA/ScoreAnalysis.lean`'s
  `indep_noise_sigmaLT`, `private` and hence not citeable — is **gone**: wave
  `ts/s1b-arma-finish` made it public. (Its replacement, narrower, is the still-`private`
  `hannanVarZ_quadForm` chain; see `hannanScore_brownInputs`.)

**Two findings reported by this wave.**
1. `criterion_tendsto_contrast` is *strictly weaker* than the `S_T/T`-level LLN the
   variance part needs: `Real.log 0 = 0`, so at `σ² = 1` the degenerate event
   `{S_T = 0}` is invisible at the `log` level and the `exp`-transfer fails. The
   project-level fix is to un-`private` Consistency's `armaProfileS_tendstoInProb`.
2. The commissioned Bartlett route to the PACF CLT was **closed**: `Process/SampleACF.lean`'s
   Bartlett debt (since removed) carried `MemLp (ε 0) 4 μ`, which the PACF CLT —
   correctly, FY Prop 3.1 needs two moments — did not assume. The martingale route
   taken instead was documented in the `PACF` section.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.3.2,
Theorem 3.2, eq. (3.14), Prop 3.1 (pp. 96–99); E. J. Hannan, J. Appl. Probab. 10
(1973) 130–145; Brockwell & Davis (1991) §8.7–§10.8. (`FY §3.3 Thm 3.2 / Hannan
1973`.)
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

section CharFunBricks

/-! ### Measure-splitting bricks

The section's charFun bricks (`charFun_map_eq_integral`, `integrable_cexp_mul_I`,
`norm_cexp_sub_cexp_le` and the charFun form of Slutsky,
`tendsto_charFun_of_tendstoInProb_sub`) went with the score-CLT assembly they served; see
**Removed** in the module docstring. What is left are the two measure-splitting bounds,
still used by `hannan_sigma2_consistent`. -/

/-- Splitting a bad event into two, at the level of the real-valued measure. -/
private lemma toReal_measure_le_of_subset_union [IsFiniteMeasure μ] {A B C : Set Ω}
    (hsub : A ⊆ B ∪ C) : (μ A).toReal ≤ (μ B).toReal + (μ C).toReal := by
  rw [← ENNReal.toReal_add (measure_ne_top μ B) (measure_ne_top μ C)]
  exact ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨measure_ne_top μ B, measure_ne_top μ C⟩)
    ((measure_mono hsub).trans (measure_union_le B C))

/-- The three-way version of `toReal_measure_le_of_subset_union`. -/
private lemma toReal_measure_le_of_subset_union₃ [IsFiniteMeasure μ] {A B C D : Set Ω}
    (hsub : A ⊆ B ∪ (C ∪ D)) :
    (μ A).toReal ≤ (μ B).toReal + ((μ C).toReal + (μ D).toReal) := by
  have h1 := toReal_measure_le_of_subset_union (μ := μ) hsub
  have h2 := toReal_measure_le_of_subset_union (μ := μ) (A := C ∪ D) (B := C) (C := D) subset_rfl
  linarith

end CharFunBricks

section Sigma2

/-! ### The two inputs of the variance part

`S(θ̂_T)/T = (S(θ̂_T)/T − S(θ₀)/T) + S(θ₀)/T`: the second term is the quadratic-form
LLN at the truth, the first is killed by consistency plus a local equicontinuity
estimate. Both are recorded as named debts below; everything else is proved. -/

/-- At the truth the composite filter is `δ₀`, so the contrast variance is `1`. This is
the convolution identity `π(θ₀) ∗ ψ(θ₀) = δ` (`armaPi_conv_armaPsi`) read off term by
term; unlike `armaContrastVar_eq_one_iff` it needs no coprimality hypothesis. -/
private lemma armaContrastVar_self {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ) :
    armaContrastVar b0 a0 b0 a0 = 1 := by
  have hterm : ∀ n : ℕ,
      (∑ jk ∈ Finset.range (n + 1), armaPi b0 a0 jk * armaPsi b0 a0 (n - jk)) ^ 2
        = if n = 0 then (1 : ℝ) else 0 := by
    intro n
    rw [armaPi_conv_armaPsi]
    split_ifs <;> norm_num
  rw [armaContrastVar, tsum_congr hterm]
  simpa using tsum_ite_eq (0 : ℕ) (1 : ℝ)

/-- **The quadratic-form LLN at the truth**: `T⁻¹ xᵀ Γ_T(θ₀)⁻¹ x →p σ²`.

This is **not a second copy** of Consistency's debt: it is exactly that lane's
`armaProfileS_tendstoInProb` specialised to `θ = θ₀`, where the contrast variance is
`1` (`armaContrastVar_self`, above — the coprimality-free half of
`armaContrastVar_eq_one_iff`). The public `criterion_tendsto_contrast` is **strictly
weaker** than what is needed here: it controls `log(S_T/T) + T⁻¹ log det Γ_T`, and
`Real.log` is not injective at Lean's junk value (`Real.log 0 = 0`), so at `σ² = 1` the
degenerate event `{S_T = 0}` is invisible at the `log` level and the `exp`-transfer back
to `S_T/T` fails.

The lemma cited was `private` to `ARMA/Consistency.lean` when this debt was recorded;
the project-level fix that note asked for — making it public — has now been applied, so
this statement is a two-line corollary and no longer carries any debt of its own. -/
private theorem armaProfileS_atTruth_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤
        |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal)
      atTop (𝓝 0) := by
  refine (armaProfileS_tendstoInProb h hiid hσ hB0 hB0 hcausal hmeas hη).congr fun T => ?_
  congr 1
  refine congrArg _ (Set.ext fun ω => ?_)
  simp only [Set.mem_setOf_eq, armaContrastVar_self, mul_one, div_eq_inv_mul]

/-- **Local stochastic equicontinuity of the profiled sum of squares — PROVED**
(2026-08-09, wave `ts/s1b-arma-finish`): the oscillation of `θ ↦ T⁻¹ S_T(θ)` over a small
ball around `θ₀` is uniformly (in `T`) negligible in probability. It is a one-line
corollary of `Consistency.armaProfileS_locallyEquicontinuous`, where the estimate is
carried out; the note below is kept because two of its predictions were **overturned**
there (see the last paragraph).

Hannan's ergodic route proves this together with the pointwise LLN: `T⁻¹ S_T(θ)` is,
up to the `O(1/T)` edge effect controlled by `logdet_armaToeplitz_vanishes`'s
whitened-Toeplitz factorisation, the time average `T⁻¹ Σ_t r_t(θ)²` of the squared
`θ`-residual process, and `θ ↦ r_t(θ)` is Lipschitz in `θ` on the compact `K ⊆ 𝓑`
with an `L²`-integrable Lipschitz constant (geometric decay of `∂π_j/∂θ`, uniform on
`K` by `exists_geometric_bound_armaPi`). The claim that the missing ingredient is "the
pointwise ergodic theorem, absent from Mathlib" is **WITHDRAWN** (2026-08-08): the
pointwise LLN it is paired with is now reduced, in Consistency, to the single
ergodic-theorem-free item (C) (`armaProfileS_tendstoInProb`'s `hCLLN`), and the
finite-`T` half of the *oscillation* statement is not an ergodic statement at all — it
is the `θ`-Lipschitz estimate above, uniform in `T`, which needs a locally uniform
geometric bound on `π(θ)` and on `∂π(θ)` over the compact `K`.

**The brick itself is now PROVED** (2026-08-09, wave `ts/s1-arma-endgame`):
`Consistency.exists_uniform_geometric_bound_arma` (public) gives, for any compact
`K ⊆ 𝓑`, one `(C, r)` with `r < 1` bounding `|armaPi θ n|` *and* `|armaPsi θ n|` by
`C rⁿ` uniformly in `θ ∈ K`. Two amendments to the recipe recorded above:

* the Lipschitz-in-`z` step is **unnecessary**. Pushing the radius past `1` is done by
  the polar parametrisation `z = s · w` (`‖w‖ ≤ 1`, `s ∈ [1, 2]`): the zero set of
  `(θ, w, s) ↦ aeval (s·w) (maPoly θ.2)` is compact, so the minimum of its
  `s`-coordinate is already `> 1`. The rest is `IsCompact.exists_isMinOn` /
  `exists_isMaxOn` for `inf |den|` and `sup |num|` on `K × closedBall 0 R`;
* the diagnosis that `exists_geometric_bound_armaPsi` cannot be used as a black box was
  correct — its Cauchy estimate is redone carrying the radius and the sup-bound
  (`Consistency.abs_armaPsi_le_of_disc_bounds`, via `norm_cauchyPowerSeries_le` plus
  uniqueness of power series).

**No `∂π/∂θ` companion is needed.** What the oscillation estimate actually consumes is a
*modulus of continuity*, `∀ ε > 0, ∃ ρ > 0, ∀ θ θ' ∈ K, dist θ θ' < ρ →
∑' n, |π_n(θ) − π_n(θ')| < ε`, and that is free from the brick plus compactness of
`K × K`: it is PROVED as `Consistency.exists_armaPi_l1_modulus` (public).

**AMENDMENT (2026-08-09).** The Gram-tail *difference* modulus asked for below is **not
needed**, and the two "shortcuts" declared dead below are indeed dead but irrelevant.
What the oscillation estimate actually consumes is a bound on the correction term
`T⁻¹uᵀG_T(θ)u` that is `o_p(1)` *uniformly over `θ ∈ K`* — and that is available from the
entrywise bound `|G_{ij}| ≤ (1−r²)⁻¹h_ih_j`, which factorises the quadratic form into a
square of a **`θ`-free** envelope (`Consistency.quadForm_gramTail_le_env`). One Markov
inequality then covers the whole supremum at rate `O(1/T)`. The superseded plan follows.

**What was thought to be left here** was the matching modulus for the Gram tail. Writing
`Γ_T(θ)⁻¹ = Π_Tᵀ(1 + G_T)⁻¹Π_T` and splitting

  `[Π−Π′]ᵀ(1+G)⁻¹Π  +  Π′ᵀ[(1+G)⁻¹−(1+G′)⁻¹]Π  +  Π′ᵀ(1+G′)⁻¹[Π−Π′]`,

the outer two terms are handled by `exists_armaPi_l1_modulus`, `(1+G)⁻¹ ⪯ 1` and the
Schur test (`rowSum_kernel_le`); the middle term needs
`∑_j |G_T(θ)_{ij} − G_T(θ′)_{ij}| ≤ L(ρ)` uniformly in `T` and `i`, i.e.
`trace_gramTail_le`'s estimate redone in difference form off the same modulus. The two
apparent shortcuts do not work: the pathwise bound `T⁻¹uᵀG u ≤ K P² · T⁻¹‖x‖²` is
`O_p(1)`, not `o_p(1)`, and using `(1+K)⁻¹ ⪯ (1+G)⁻¹` in the sandwich costs an additive
`O(1)` term `log(1+K)` in the criterion. -/
private theorem armaProfileS_equicontinuous [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun T : ℕ => (μ {ω | ∃ ba ∈ K, dist ba (b0, a0) < ρ ∧
          η ≤ |armaProfileS ba.1 ba.2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
            - armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T|}).toReal)
        atTop (𝓝 0) :=
  armaProfileS_locallyEquicontinuous h hiid hσ hB0 hcausal hmeas hK hKB hη

end Sigma2

/-- **FY Theorem 3.2, variance part**: the profiled variance estimator is consistent,
`σ̂²_T = S(θ̂_T)/T →p σ²`. -/
theorem hannan_sigma2_consistent [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    -- USER-INPUT: exact orders (see `hannanVarZ_posDef`); Hannan 1973 §2
    (hbdeg : (arPoly b0).natDegree = p) (hadeg : (maPoly a0).natDegree = q)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    -- USER-INPUT: the search region consists of minimal models (see `mle_consistent`'s
    -- docstring for the Lean witness showing this cannot be dropped); Hannan 1973 §2
    (hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2))
    (hK0 : (b0, a0) ∈ interior K)
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ)) (hθmeas : ∀ T, Measurable (θ T))
    {δT : ℕ → ℝ} (hδT0 : ∀ T, 0 ≤ δT T)
    (hδTfast : Tendsto (fun T : ℕ => (T : ℝ) * δT T) atTop (𝓝 0))
    (hargmin : ∀ (T : ℕ) (ω : Ω), θ T ω ∈ K ∧ ∀ ba ∈ K,
      armaProfileCriterion (θ T ω).1 (θ T ω).2
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        ≤ armaProfileCriterion ba.1 ba.2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |armaProfileS (θ T ω).1 (θ T ω).2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal)
      atTop (𝓝 0) := by
  classical
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  -- `hδTfast` (rate `o(1/T)`) certainly gives the plain `δ_T → 0` that consistency needs
  have hδT : Tendsto δT atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall hδT0) ?_ hδTfast
    filter_upwards [eventually_ge_atTop 1] with T hT
    have h1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    nlinarith [hδT0 T]
  -- the three inputs
  obtain ⟨ρ, hρ, hequi⟩ :=
    armaProfileS_equicontinuous h hiid hσ hB0 hcausal hmeas hK hKB hδ2
  have htruth := armaProfileS_atTruth_tendstoInProb h hiid hσ hB0 hcausal hmeas hδ2
  have hcons := mle_consistent h hiid hσ hB0 hcop hcausal hmeas hK hKB hcopK
    (interior_subset hK0) θ hθmeas hδT hδT0 hargmin hρ
  -- `|S(θ̂)/T − σ²| ≥ δ` forces either `|S(θ₀)/T − σ²| ≥ δ/2`, or `θ̂` far from `θ₀`,
  -- or an oscillation of size `δ/2` inside the `ρ`-ball
  have hg : Tendsto (fun T : ℕ =>
      (μ {ω | δ / 2 ≤
          |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|}).toReal
        + ((μ {ω | ρ ≤ dist (θ T ω) (b0, a0)}).toReal
          + (μ {ω | ∃ ba ∈ K, dist ba (b0, a0) < ρ ∧
              δ / 2 ≤ |armaProfileS ba.1 ba.2
                  (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
                - armaProfileS b0 a0
                    (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T|}).toReal))
      atTop (𝓝 0) := by
    simpa using htruth.add (hcons.add hequi)
  refine squeeze_zero (fun T => ENNReal.toReal_nonneg) (fun T => ?_) hg
  refine toReal_measure_le_of_subset_union₃ (fun ω hω => ?_)
  simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
  by_cases hB : δ / 2 ≤ |armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2|
  · exact Or.inl hB
  refine Or.inr ?_
  push_neg at hB
  by_cases hC : ρ ≤ dist (θ T ω) (b0, a0)
  · exact Or.inl hC
  push_neg at hC
  refine Or.inr ⟨θ T ω, (hargmin T ω).1, hC, ?_⟩
  have habs := abs_sub_abs_le_abs_sub
    (armaProfileS (θ T ω).1 (θ T ω).2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
    (armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
  have hrw : (armaProfileS (θ T ω).1 (θ T ω).2
        (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
      - (armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T - σ2)
      = armaProfileS (θ T ω).1 (θ T ω).2 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T
        - armaProfileS b0 a0 (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) / T := by ring
  rw [hrw] at habs
  linarith

/-- The **sample PACF** at order `k` (Yule–Walker form on the sample ACVF): the last
coordinate of the solution of the sample Yule–Walker system (junk `0` at `k = 0` or
when the sample Toeplitz matrix is singular, by the matrix-inverse convention). -/
noncomputable def samplePACF {T : ℕ} (x : Fin T → ℝ) (k : ℕ) : ℝ :=
  if hk : 0 < k then
    (((Matrix.of fun i j : Fin k =>
          sampleACVF x ((i : ℤ) - (j : ℤ)).natAbs)⁻¹)
        *ᵥ fun i : Fin k => sampleACVF x ((i : ℕ) + 1)) ⟨k - 1, by omega⟩
  else 0

section PACF

/-! ### Measurability bricks for the sample PACF

FY Proposition 3.1 (`samplePACF_clt`) and its linearization debt were removed (see
**Removed** in the module docstring); the padding lemmas that served only them went too.
These two measurability bricks are kept — they are consumed by `wnYW_measurable`, which
supports the `ls_yw_mle_equivalent_debt_false` witness below. -/

/-- Entrywise measurability of a matrix inverse with measurable entries (via
`A⁻¹ = (det A)⁻¹ • adj A`, both polynomial in the entries). -/
private lemma measurable_inv_mulVec {α : Type*} [MeasurableSpace α] {n : ℕ}
    {M : α → Matrix (Fin n) (Fin n) ℝ} {v : α → Fin n → ℝ}
    (hM : ∀ i j, Measurable fun x => M x i j) (hv : ∀ i, Measurable fun x => v x i)
    (i : Fin n) : Measurable fun x => ((M x)⁻¹ *ᵥ v x) i := by
  classical
  have hdet : ∀ N : α → Matrix (Fin n) (Fin n) ℝ, (∀ i j, Measurable fun x => N x i j) →
      Measurable fun x => (N x).det := by
    intro N hN
    simp only [Matrix.det_apply]
    exact Finset.measurable_sum _ fun σ _ =>
      (Finset.measurable_prod _ fun j _ => hN _ _).const_smul _
  have hadj : ∀ i' j' : Fin n, Measurable fun x => (M x).adjugate i' j' := by
    intro i' j'
    simp only [Matrix.adjugate_apply]
    refine hdet _ fun r s => ?_
    simp only [Matrix.updateRow_apply]
    rcases eq_or_ne r j' with rfl | hr
    · simp
    · simpa [hr] using hM r s
  have hexp : (fun x => ((M x)⁻¹ *ᵥ v x) i)
      = fun x => ∑ j, ((M x).det)⁻¹ * ((M x).adjugate i j * v x j) := by
    funext x
    simp [Matrix.mulVec, dotProduct, Matrix.inv_def, Ring.inverse_eq_inv', mul_assoc]
  rw [hexp]
  exact Finset.measurable_sum _ fun j _ =>
    ((hdet M hM).inv).mul ((hadj i j).mul (hv j))

/-- `sampleACVF` of the observation window is measurable. -/
private lemma measurable_sampleACVF {T : ℕ} {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (m : ℕ) : Measurable fun ω => sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) m := by
  classical
  have hmean : Measurable fun ω => sampleMean (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) := by
    simp only [sampleMean]
    exact (Finset.measurable_sum _ fun t _ => hmeas _).const_mul _
  simp only [sampleACVF]
  refine Measurable.const_mul (Finset.measurable_sum _ fun t _ => ?_) _
  rcases eq_or_ne (decide ((t : ℕ) + m < T)) true with hlt | hlt
  · have hlt' : (t : ℕ) + m < T := of_decide_eq_true hlt
    simpa [dif_pos hlt'] using! ((hmeas _).sub hmean).mul ((hmeas _).sub hmean)
  · have hlt' : ¬ ((t : ℕ) + m < T) := by simpa using hlt
    simp [dif_neg hlt']

end PACF

/-! ### The frozen `ls_yw_mle_equivalent_debt` statement is FALSE — a formalized witness

Found in wave `ts/s12-model-selection` (2026-08-09). The statement quantifies over an
**arbitrary measurable** `bMLE`: no hypothesis ties it to the Gaussian likelihood, to
least squares, or to the data at all (and no least-squares estimator appears anywhere,
despite the name). It therefore asserts `√T · dist(b̂_YW, bMLE) →p 0` for *every*
measurable sequence `bMLE`, which fails for the constant translate
`bMLE := b̂_YW + 1` as soon as `p ≥ 1`.

The witness below is axiom-clean: the instance is the causal AR(1) with zero coefficient
(`b(z) = 1`, so `X = ε`) driven by the coordinate white noise on `(ℤ → ℝ, ⊗ N(0,1))`,
and `bMLE` is the translate, whose measurability comes from `measurable_inv_mulVec` /
`measurable_sampleACVF` above.

**Repair.** B&D Thm 10.8.2 compares three *estimators*, so `bMLE` (and a least-squares
sequence `bLS`, currently absent) must carry their defining hypotheses — for `bMLE` the
`hargmin`/`hδTfast` pair of `hannan_mle_clt`, for `bLS` the normal equations. With those
in place the statement becomes a genuine `√T`-equivalence and the residue is the one
recorded at `armaMLE_linearization`.

**The repair is applied** to `ls_yw_mle_equivalent_debt` below (wave
`ts/s12b-model-repairs`, 2026-08-09); see the Statement-strengthening paragraph there.
This witness is kept verbatim, quantified over the *frozen* shape `H`, as the permanent
record. -/

private noncomputable def wnMeasure : Measure (ℤ → ℝ) :=
  Measure.infinitePi (fun _ : ℤ => gaussianReal 0 1)

private instance : IsProbabilityMeasure wnMeasure := by
  unfold wnMeasure; infer_instance

private def wnCoord (t : ℤ) (ω : ℤ → ℝ) : ℝ := ω t

private lemma wnCoord_measurable (t : ℤ) : Measurable (wnCoord t) := measurable_pi_apply t

private lemma wnMeasure_map_coord (t : ℤ) : wnMeasure.map (wnCoord t) = gaussianReal 0 1 :=
  Measure.infinitePi_map_eval _ t

private lemma wnCoord_identDistrib (t : ℤ) :
    IdentDistrib (wnCoord t) (id : ℝ → ℝ) wnMeasure (gaussianReal 0 1) :=
  ⟨(wnCoord_measurable t).aemeasurable, aemeasurable_id, by
    rw [Measure.map_id, wnMeasure_map_coord t]⟩

private lemma wn_isIIDNoise : IsIIDNoise wnCoord 1 wnMeasure := by
  refine ⟨wnCoord_measurable, ?_, ?_, ?_, ?_, ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ : ℤ => (id : ℝ → ℝ)) (fun _ => measurable_id)
  · exact fun s t => (wnCoord_identDistrib s).trans (wnCoord_identDistrib t).symm
  · exact (wnCoord_identDistrib 0).memLp_iff.2 (memLp_id_gaussianReal 2)
  · rw [(wnCoord_identDistrib 0).integral_eq]
    simp only [id_eq]
    exact (integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal)))
  · rw [(wnCoord_identDistrib 0).variance_eq, variance_id_gaussianReal]
    simp

/-- The zero AR(1) coefficient vector: `b(z) = 1`, so `X = ε` is a causal AR(1). -/
private def wnB : Fin 1 → ℝ := fun _ => 0

private lemma arPoly_wnB : arPoly wnB = 1 := by
  simp [arPoly, wnB]

private lemma wn_noRoot : NoRootClosedDisc wnB := by
  intro z _
  rw [arPoly_wnB]
  simp

private lemma armaPsi_wnB (n : ℕ) :
    armaPsi wnB (Fin.elim0 : Fin 0 → ℝ) n = if n = 0 then 1 else 0 := by
  have hma : (maPoly (Fin.elim0 : Fin 0 → ℝ)) = 1 := by simp [maPoly]
  unfold armaPsi
  rw [hma, arPoly_wnB]
  simp [PowerSeries.coeff_one]

private lemma wn_isAR : IsAR wnB 1 wnCoord wnCoord wnMeasure := by
  refine ⟨wnCoord_measurable, wn_isIIDNoise.isWhiteNoise, ?_⟩
  intro t
  filter_upwards with ω
  simp [wnB]

private lemma wn_isLinearProcess :
    IsLinearProcessOf (armaPsi wnB (Fin.elim0 : Fin 0 → ℝ)) wnCoord wnCoord wnMeasure := by
  intro t
  refine Tendsto.congr' ?_ tendsto_const_nhds (f₁ := fun _ : ℕ => (0 : ENNReal))
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hsum : ∀ ω : ℤ → ℝ,
      ∑ j ∈ Finset.range N, armaPsi wnB (Fin.elim0 : Fin 0 → ℝ) j * wnCoord (t - (j : ℕ)) ω
        = wnCoord t ω := by
    intro ω
    rw [Finset.sum_eq_single 0]
    · simp [armaPsi_wnB]
    · intro j _ hj; simp [armaPsi_wnB, hj]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  have : (fun ω => wnCoord t ω -
      ∑ j ∈ Finset.range N, armaPsi wnB (Fin.elim0 : Fin 0 → ℝ) j * wnCoord (t - (j : ℕ)) ω)
      = fun _ => (0 : ℝ) := by
    funext ω; rw [hsum ω]; ring
  rw [this]
  simp


/-- The Yule-Walker estimator of the frozen statement, at the white-noise instance. -/
private noncomputable def wnYW (T : ℕ) (ω : ℤ → ℝ) : Fin 1 → ℝ :=
  ((Matrix.of fun i' j : Fin 1 =>
      sampleACVF (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω)
        ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
    fun i' : Fin 1 => sampleACVF (fun t : Fin T => wnCoord (((t : ℕ) : ℤ) + 1) ω)
      ((i' : ℕ) + 1)

private lemma wnYW_measurable (T : ℕ) : Measurable (wnYW T) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_inv_mulVec (fun _ _ => measurable_sampleACVF wnCoord_measurable _)
    (fun _ => measurable_sampleACVF wnCoord_measurable _) i

private theorem ls_yw_mle_equivalent_debt_false
    (H : ∀ {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℕ}
      {b0 : Fin p → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ},
      IsAR b0 σ2 X ε μ → IsIIDNoise ε σ2 μ → 0 < σ2 → NoRootClosedDisc b0 →
      IsLinearProcessOf (armaPsi b0 (Fin.elim0 : Fin 0 → ℝ)) X ε μ →
      (∀ t, Measurable (X t)) →
      ∀ bYW : (T : ℕ) → Ω → Fin p → ℝ,
      (∀ (T : ℕ) (ω : Ω) (i : Fin p),
        bYW T ω i = (((Matrix.of fun i' j : Fin p =>
            sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
              ((i' : ℤ) - (j : ℤ)).natAbs)⁻¹) *ᵥ
          fun i' : Fin p => sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
            ((i' : ℕ) + 1)) i) →
      ∀ bMLE : (T : ℕ) → Ω → Fin p → ℝ, (∀ T, Measurable (bMLE T)) →
      ∀ {δ : ℝ}, 0 < δ →
      Tendsto (fun T : ℕ => (μ {ω | δ ≤
        Real.sqrt T * dist (bYW T ω) (bMLE T ω)}).toReal) atTop (𝓝 0)) :
    False := by
  classical
  have hmle : ∀ T : ℕ, Measurable (fun ω : ℤ → ℝ => fun i : Fin 1 => wnYW T ω i + 1) :=
    fun T => measurable_pi_lambda _ fun i =>
      ((measurable_pi_apply i).comp (wnYW_measurable T)).add measurable_const
  have key := H wn_isAR wn_isIIDNoise one_pos wn_noRoot wn_isLinearProcess
    wnCoord_measurable wnYW (fun _ _ _ => rfl)
    (fun T ω => fun i : Fin 1 => wnYW T ω i + 1) hmle (δ := 1) one_pos
  -- the two estimator sequences are at distance `≥ 1`, so the event is everything
  have hset : ∀ T : ℕ, 1 ≤ T → {ω : ℤ → ℝ | (1 : ℝ) ≤
      Real.sqrt T * dist (wnYW T ω) (fun i : Fin 1 => wnYW T ω i + 1)} = Set.univ := by
    intro T hT
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    have hd : (1 : ℝ) ≤ dist (wnYW T ω) (fun i : Fin 1 => wnYW T ω i + 1) := by
      have := dist_le_pi_dist (wnYW T ω) (fun i : Fin 1 => wnYW T ω i + 1) 0
      rw [Real.dist_eq] at this
      simpa using this
    have hs : (1 : ℝ) ≤ Real.sqrt T := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hT)
    nlinarith [Real.sqrt_nonneg (T : ℝ)]
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    refine key.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [hset T hT]
    simp
  have := tendsto_nhds_unique hconst tendsto_const_nhds
  norm_num at this

end StatLean.TimeSeries
