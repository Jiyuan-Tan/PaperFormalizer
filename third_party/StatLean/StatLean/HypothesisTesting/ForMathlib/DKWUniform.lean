module
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.ExponentialBounds
public import StatLean.ConcentrationInequalities.McDiarmid.McDiarmid
public import StatLean.ConcentrationInequalities.Symmetrization.Empirical
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Data.Fin.Tuple.Sort

public import Mathlib.Probability.Independence.Integration

@[expose] public section

/-!
# A uniform-in-`n` exponential tail for the empirical process

For an i.i.d. real sample `X₁, …, Xₙ` with law `μ` and distribution function `F`, the
Kolmogorov distance between the empirical and the population distribution function,
$$D_n \;=\; \sup_{t \in \mathbb R}\bigl|\hat F_n(t) - F(t)\bigr| ,$$
satisfies an exponential tail bound *with constants free of `n` and of `μ`*:
$$\mathbb P\bigl(\sqrt n\, D_n \ge d\bigr) \;\le\; C\,e^{-c\,d^2}
  \qquad (d \ge 0).$$
This is the finite-sample input needed to calibrate a distribution-free goodness-of-fit
test at a fixed threshold, without ever invoking the Kolmogorov limit law: a rejection
threshold `d_α` with `C e^{-c d_α²} ≤ α` gives a test of level `α` at *every* sample size.

## Main results

* `empCDF`, `ksDist` — the empirical distribution function of a finite sample and its
  Kolmogorov distance to a population law.
* `integral_ksDist_le` — the in-expectation bound `E Dₙ ≤ 2/√n`.
* `ksDist_concentration` — bounded-differences concentration of `Dₙ` around its mean.
* `dkw_uniform` — the tail bound, `P(√n Dₙ ≥ d) ≤ 4 e^{-d²/16}`.

**Constants (documented deviation).** The sharp form of this inequality has the constants
`C = 2`, `c = 2`, and those are *not* what the route formalised here delivers. We state the
strictly weaker `C = 4`, `c = 1/16`, which is exactly what the two ingredients below compose
to and which is implied by the sharp form, so the statement is true. Concretely:

* the mean bound `integral_ksDist_le` is proved at `√n · E Dₙ ≤ 4` (the true value is
  `≈ 0.87`, the mean of the Kolmogorov limit law `sup|B°|`), and
* the bounded-differences bound `ksDist_concentration` gives `exp(−2(d − 4)²)` for `d ≥ 4`.

Composing the two: `min_d [2(d − M)² − c d²] = −2cM²/(2 − c)`, so with `M = 4` the pair
`(C, c) = (4, 1/16)` is admissible as soon as `2 · 16 · c/(2 − c) ≤ log 4`, i.e. `c ≤ 0.083`;
at `c = 1/16` the left side is `1.032 ≤ log 4 = 1.386`, with slack. (The sharp arithmetic
constant is `32/31`, attained at `d = 128/31`; this is the numeral in the `dkw_uniform`
proof.) For `d ≤ 4√(log 4) = 4.709…` the envelope `4 e^{−d²/16}` exceeds `1` and the bound
is vacuous — in particular it covers the whole range `d ≤ 4` where the mean bound leaves
nothing to prove.

**Deviation from the frozen statement, and the coordinated edit it forced.** The frozen
statements were `√n · E Dₙ ≤ 2` and `4 e^{−d²/8}`. The mean constant `2` is *not* reachable
by any elementary route (see items 1–7 below); the route that is executable lands at `4`,
and `M = 4` provably breaks the frozen headline — `max_d [d²/8 − 2(d − 4)²] = 32/15 = 2.133 >
log 4 = 1.386` (at `d = 64/15`), while the vacuous regime of `4 e^{−d²/8}` only reaches
`d = √(8 log 4) = 3.330 < 4`, so the band `d ∈ (3.330, 4)` would be covered by neither
regime. Per the charter rule *state the constants that are actually provable*, the two
statements were amended to `4/√n` and `4 e^{−d²/16}`, and the single downstream consumer of
`c`, the numeral inside `ksThreshold` in `GoodnessOfFit/KSConsistency.lean`, was changed from
`√(8 log(4/α))` to `√(16 log(4/α))` (the deviation is recorded at that definition too).
Every statement in `KSConsistency.lean` and `KSLocalPower.lean` is phrased through
`ksThreshold` and re-derives its level from the defining equation `4 e^{−s²/16} = α`, so no
other edit was required: the calibrated thresholds are `√2` times larger, i.e. the tests are
more conservative, and all four headline theorems there hold verbatim.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.2 (The Kolmogorov–Smirnov Test), supporting material for Theorems 16.2.1 and 16.2.2:
a uniform-in-`n` exponential tail for the empirical process. (`TSH4 §16.2 Thm 16.2.1, Thm
16.2.2`.)

**Proof formalization notes.**
* The empirical distribution function is defined locally, as a plain average of indicators,
  rather than imported: this file sits in the bottom (`ForMathlib`) layer and must not
  depend on another area's concept layer.
* `ksDist` is an unrestricted real supremum over `t : ℝ`. Both `t ↦ empCDF X ω t` and the
  population `cdf μ` are right-continuous, so the supremum over `ℝ` coincides with the
  supremum over `ℚ`; that identity (a deterministic, pointwise statement) is what makes the
  event measurable and is the standard first step of the proof. The supremum is bounded by
  `1`, so no junk value of `⨆` is ever hit for `n ≥ 1`.
* `ksDist_concentration` is the bounded-differences inequality applied to
  `f(x₁,…,xₙ) = supₜ |n⁻¹ ∑ᵢ 1{xᵢ ≤ t} − F(t)|`, which changes by at most `1/n` when one
  coordinate is changed; with `cᵢ = 1/n` the bound `exp(-2s²/∑cᵢ²) = exp(-2ns²)` at
  `s = d/√n` is `exp(-2d²)`. The project's McDiarmid theorem
  (`StatLean.ConcentrationInequalities.McDiarmid`) is the engine.
* Events are stated with a closed inequality `d ≤ …`; this is the stronger form and the
  underlying sub-Gaussian Chernoff bound supplies it directly.

**Mean bound: how `integral_ksDist_le` is proved, and why the constant is `4`.**

1. *How much slack does the headline allow at a fixed `c`?* `dkw_uniform` composes a mean
   bound `√n · E Dₙ ≤ M` with the tail `exp(−2(d − M)²)`. Since
   `min_d [2(d − M)² − c d²] = −2cM²/(2 − c)`, the composition yields
   `P(√n Dₙ ≥ d) ≤ exp(2cM²/(2 − c)) · e^{−c d²}` for **every** `d ≥ 0`. At the frozen
   `c = 1/8` the headline `C = 4` survives only `M ≤ √(15 log 4/2) = 3.2245`; at the amended
   `c = 1/16` it survives every `M ≤ √(31 log 4/2) = 4.635`, so `M = 4` fits.

2. *Grid + union bound cannot give any constant.* With the quantile grid `t₁ < … < t_m`,
   monotonicity gives `Dₙ ≤ max_j |Δ(t_j)| + 1/m`, and each `Δ(t_j)` is `1/(4n)`-sub-Gaussian,
   so `E max_j |Δ(t_j)| ≤ √(log(2m)/(2n))` and
   `√n E Dₙ ≤ √(log(2m)/2) + √n/m`. Every choice of `m` leaves `√(log(2m)/2) ≥ √(log(2√n)/2)`,
   which diverges. The `√(log n)` factor is intrinsic to a *single-scale* union bound; only
   chaining or a martingale argument removes it.

3. *Generic VC chaining is available but too lossy.* `ConcentrationInequalities.glivenko_cantelli`
   bounds exactly this integrand by `5400/√n` (generic VC bound at `vcDim = 1`, for an i.i.d.
   *stream* `X : ℕ → Ξ → ℝ`; the finite sample here would first have to be transported to the
   canonical infinite product). By (1) that constant forces `c ≈ 4.8 · 10⁻⁸`, i.e. a
   statistically useless calibration, so it is not the route taken.

4. *The route actually formalised* (`M = 4`). Symmetrisation gives
   `E Dₙ ≤ 2 E supₜ |n⁻¹ ∑ᵢ εᵢ 1{Xᵢ ≤ t}|` with `ε` Rademacher and independent of `X`
   (`ConcentrationInequalities.empirical_symmetrization_countable`, instantiated at the
   countable class of half-lines `{x ≤ q}`, `q ∈ ℚ`; the reduction of the `ℝ`-supremum to the
   `ℚ`-supremum is `dkw_iSup_real_eq_iSup_rat`). **Conditionally on `X`, that supremum is
   exactly the maximum of a ±1 random walk**: as `t` sweeps `ℝ`, the index set `{i : Xᵢ ≤ t}`
   runs precisely through the prefixes of the sorted sample, so
   `supₜ |∑ᵢ εᵢ 1{Xᵢ ≤ t}| = max_{0 ≤ j ≤ n} |Sⱼ|` (`exists_dkwWalk_eq`, via `Tuple.sort` and
   the fact that a downward-closed subset of `Fin n` is an initial segment). Finally
   `E max_j |Sⱼ| ≤ 2 E|Sₙ| ≤ 2√n` (`integral_dkwMax_le`), whence `√n · E Dₙ ≤ 4`.

5. *The maximal step, in the form used here.* Rather than Doob's `L^p` inequality (absent from
   Mathlib at v4.29.1) the proof uses **Lévy's maximal inequality**
   `P(max_{j ≤ n} |Sⱼ| ≥ a) ≤ 2 P(|Sₙ| ≥ a)` (`dkw_levy`), proved by reflecting the increments
   after the first passage time: the reflection is the coordinatewise sign flip
   `s ↦ (c_j(i) · s_i)_i` with `c_j = 1` on the first `j` steps and `−1` after, and it preserves
   the sign law by `signVec_map_mul_pm`. The first-passage sets are invariant under it, and
   `|Sₙ| + |2Sⱼ − Sₙ| ≥ 2|Sⱼ| ≥ 2a` puts one of the two configurations in `{|Sₙ| ≥ a}`.
   The layer-cake formula (`lintegral_eq_lintegral_meas_le`) then turns this into
   `E max_j |Sⱼ| ≤ 2 E|Sₙ|`, and `E|Sₙ| ≤ √n` follows from `E Sₙ² = n` by the elementary
   `|x| ≤ (x² + c²)/(2c)` at `c = √n` (no Cauchy–Schwarz or `Lᵖ` interpolation needed).

6. *Why `4` and not less.* Inside this route the constant is not repairable: combining *every*
   elementary tail available for the `±1` walk — Kolmogorov `P ≤ n/a²`, Lévy plus Hoeffding
   `P ≤ 4e^{−a²/2n}`, and the trivial `P ≤ 1` — gives
   `E max_j |Sⱼ| ≤ ∫₀^∞ min(1, n/a², 4e^{−a²/2n}) da = 1.66185…·√n`, i.e. `M ≤ 3.3237`, still
   above the frozen `c = 1/8` budget `3.2245` of item (1); adding the fourth moment makes it
   worse (`1.7314·√n`). Only the exact reflection value `E max_j Sⱼ = E|Sₙ| = √(2n/π)(1+o(1))`,
   giving `M = 4√(2/π) = 3.19154`, crosses that line — the miss survives every standard
   refinement, so it is the *method*, not the bookkeeping, that is short. Hence the constant
   was amended rather than the route re-engineered.

7. *What would restore `c = 1/8`.* Under the quantile transform `u = F(t)` the empirical process
   `α(u) = ∑ᵢ (1{Uᵢ ≤ u} − u)` satisfies `E[α(u₂) ∣ ℱ_{u₁}] = ((1−u₂)/(1−u₁)) α(u₁)`, i.e.
   `M(u) := α(u)/(1−u)` is a **martingale** in `u`; hence `exp(θM)` is a submartingale, and
   Doob plus Hoeffding's mgf bound give `P(sup_{u ≤ 1/2} α ≥ x√n) ≤ e^{−x²/2}`. Four such pieces
   give `P(√n Dₙ > x) ≤ 4 e^{−x²/2}` and so `√n E Dₙ ≤ √(2 log 4) + 4∫_{√(2 log 4)}^∞ e^{−x²/2} dx
   ≤ 2.27`, inside the `c = 1/8` budget. Formalising it needs the martingale property of the
   empirical process along a countable dense set of levels (a discrete-time martingale for each
   finite grid, then monotone convergence), which is a self-contained project the repository does
   not have. It remains the only way back to the frozen exponent.

**Bibliographic comments.** The inequality is due to A. Dvoretzky, J. Kiefer, and
J. Wolfowitz, "Asymptotic minimax character of the sample distribution function and of the
classical multinomial estimator," *Ann. Math. Statist.* **27** (1956), 642–669, who
obtained it with an unspecified constant; the sharp constant `2` was established by
P. Massart, "The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality," *Ann.
Probab.* **18** (1990), 1269–1283. The concentration step is the bounded-differences
method of C. McDiarmid, "On the method of bounded differences," in *Surveys in
Combinatorics 1989*, LMS Lecture Note Series **141**, Cambridge Univ. Press, 1989,
148–188; the entropy/chaining bound for the expectation follows R. M. Dudley, "The sizes of
compact subsets of Hilbert space and continuity of Gaussian processes," *J. Funct. Anal.*
**1** (1967), 290–330. The statistic itself is A. N. Kolmogorov's, "Sulla determinazione
empirica di una legge di distribuzione," *Giorn. Ist. Ital. Attuari* **4** (1933), 83–91,
with the two-sample and tabulated forms due to N. V. Smirnov, "Table for estimating the
goodness of fit of empirical distributions," *Ann. Math. Statist.* **19** (1948), 279–281.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The **empirical distribution function** of a finite sample:
`F̂ₙ(t) = n⁻¹ #{i : Xᵢ ≤ t}`. For `n = 0` it is identically `0` (junk, excluded by the
side conditions of every statement below). -/
noncomputable def empCDF {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if X i ω ≤ t then (1 : ℝ) else 0

/-- The **Kolmogorov distance** between the empirical distribution function of a sample and
the distribution function of a law `μ`: `Dₙ = supₜ |F̂ₙ(t) − F(t)|`.

The supremum ranges over all of `ℝ`; by right-continuity of both functions it agrees with
the supremum over the rationals, which is how measurability of `Dₙ` is obtained. -/
noncomputable def ksDist {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure ℝ) (ω : Ω) : ℝ :=
  ⨆ t : ℝ, |empCDF X ω t - cdf μ t|

/-! ### Deterministic reduction to a rational supremum -/

/-- The step indicator `t ↦ 1{a ≤ t}` is right continuous. -/
private lemma dkw_rightCont_step (a s : ℝ) :
    Filter.Tendsto (fun t => if a ≤ t then (1 : ℝ) else 0)
      (nhdsWithin s (Set.Ioi s)) (nhds (if a ≤ s then (1 : ℝ) else 0)) := by
  have hl : (fun _ : ℝ => if a ≤ s then (1 : ℝ) else 0)
      =ᶠ[nhdsWithin s (Set.Ioi s)] (fun t => if a ≤ t then (1 : ℝ) else 0) := by
    by_cases h : a ≤ s
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [if_pos h, if_pos (h.trans ht.le)]
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.mp h))] with t ht
      rw [if_neg h, if_neg (not_le.mpr ht)]
  exact Filter.Tendsto.congr' hl tendsto_const_nhds

/-- A real supremum of a right-continuous function over `ℝ` agrees with the supremum over
the rationals. -/
private lemma dkw_iSup_real_eq_iSup_rat (g : ℝ → ℝ)
    (hrc : ∀ s, Filter.Tendsto g (nhdsWithin s (Set.Ioi s)) (nhds (g s))) :
    ⨆ t : ℝ, g t = ⨆ q : ℚ, g (q : ℝ) := by
  by_cases hbdd : BddAbove (Set.range fun q : ℚ => g (q : ℝ))
  · have hle : ∀ t : ℝ, g t ≤ ⨆ q : ℚ, g (q : ℝ) := by
      intro t
      obtain ⟨u, hu_gt, hu_lt⟩ : ∃ u : ℕ → ℚ,
          (∀ k, t < (u k : ℝ)) ∧ (∀ k, (u k : ℝ) < t + 1 / ((k : ℝ) + 1)) := by
        choose u hu using fun k : ℕ =>
          exists_rat_btwn (show t < t + 1 / ((k : ℝ) + 1) from
            lt_add_of_pos_right t (by positivity))
        exact ⟨u, fun k => (hu k).1, fun k => (hu k).2⟩
      have hupper : Filter.Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) Filter.atTop (nhds t) := by
        have := (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      have hnhds : Filter.Tendsto (fun k => (u k : ℝ)) Filter.atTop (nhds t) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
          (Filter.Eventually.of_forall fun k => (hu_gt k).le)
          (Filter.Eventually.of_forall fun k => (hu_lt k).le)
      have htend : Filter.Tendsto (fun k => (u k : ℝ)) Filter.atTop (nhdsWithin t (Set.Ioi t)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hnhds, Filter.Eventually.of_forall fun k => hu_gt k⟩
      exact le_of_tendsto ((hrc t).comp htend)
        (Filter.Eventually.of_forall fun k => le_ciSup hbdd (u k))
    have hbddR : BddAbove (Set.range g) :=
      ⟨⨆ q : ℚ, g (q : ℝ), by rintro _ ⟨t, rfl⟩; exact hle t⟩
    exact le_antisymm (ciSup_le hle) (ciSup_le fun q => le_ciSup hbddR (q : ℝ))
  · have hbddR : ¬ BddAbove (Set.range g) := by
      intro hR
      obtain ⟨M, hM⟩ := hR
      exact hbdd ⟨M, by rintro _ ⟨q, rfl⟩; exact hM ⟨(q : ℝ), rfl⟩⟩
    rw [ciSup_of_not_bddAbove hbddR, ciSup_of_not_bddAbove hbdd]

/-! ### The symmetrised sign process: Lévy's maximal inequality for the `±1` walk

This section supplies the second half of route (4) of the header: conditionally on the
sample, the Rademacher process over half-lines is the `±1` walk along the sorted sample,
and its running maximum has `L¹` norm at most `2√n`.  Everything here is elementary; the
sign randomisation lives on `StatLean.ConcentrationInequalities.signVec`. -/

section SignWalk

open StatLean.ConcentrationInequalities

variable {n : ℕ}

/-- The `σ`-prefix of size `j`: the indices whose `σ`-rank is `< j`. -/
private def dkwPre (σ : Equiv.Perm (Fin n)) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ((σ.symm i : ℕ) < j))

/-- The `±1` walk along the `σ`-order, stopped after `j` steps. -/
private def dkwWalk (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ dkwPre σ j, s i

/-- The running maximum of `|dkwWalk|` over the `n + 1` prefixes. -/
private noncomputable def dkwMax (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) : ℝ :=
  ⨆ j : Fin (n + 1), |dkwWalk σ s (j : ℕ)|

private lemma dkwPre_mono (σ : Equiv.Perm (Fin n)) {j j' : ℕ} (h : j ≤ j') :
    dkwPre σ j ⊆ dkwPre σ j' := by
  intro i hi
  simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_lt_of_le hi h

private lemma dkwPre_zero (σ : Equiv.Perm (Fin n)) : dkwPre σ 0 = ∅ := by
  simp [dkwPre]

private lemma dkwPre_full (σ : Equiv.Perm (Fin n)) : dkwPre σ n = Finset.univ := by
  ext i
  simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact (σ.symm i).isLt

private lemma dkwWalk_zero (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    dkwWalk σ s 0 = 0 := by
  simp [dkwWalk, dkwPre_zero]

private lemma measurable_dkwWalk (σ : Equiv.Perm (Fin n)) (j : ℕ) :
    Measurable (fun s : Fin n → ℝ => dkwWalk σ s j) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

private lemma measurable_dkwMax (σ : Equiv.Perm (Fin n)) :
    Measurable (dkwMax σ) :=
  Measurable.iSup fun j => (measurable_dkwWalk σ (j : ℕ)).abs

private lemma dkwWalk_le_dkwMax (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) {j : ℕ}
    (hj : j ≤ n) : |dkwWalk σ s j| ≤ dkwMax σ s := by
  refine le_ciSup (f := fun j : Fin (n + 1) => |dkwWalk σ s (j : ℕ)|) ?_ ⟨j, by omega⟩
  exact (Set.finite_range _).bddAbove

private lemma dkwMax_nonneg (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    0 ≤ dkwMax σ s :=
  le_trans (abs_nonneg _) (dkwWalk_le_dkwMax σ s (Nat.zero_le n))

private lemma exists_dkwMax_eq (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    ∃ j : Fin (n + 1), dkwMax σ s = |dkwWalk σ s (j : ℕ)| := by
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : Fin (n + 1) => |dkwWalk σ s (j : ℕ)|)
  refine ⟨j0, le_antisymm (ciSup_le hj0) ?_⟩
  exact dkwWalk_le_dkwMax σ s (Nat.lt_succ_iff.mp j0.isLt)

/-! ### The reflected sign pattern -/

private noncomputable def dkwSign (σ : Equiv.Perm (Fin n)) (j : ℕ) : Fin n → ℝ :=
  fun i => if i ∈ dkwPre σ j then 1 else -1

private lemma dkwSign_pm (σ : Equiv.Perm (Fin n)) (j : ℕ) (i : Fin n) :
    dkwSign σ j i = 1 ∨ dkwSign σ j i = -1 := by
  unfold dkwSign; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma dkwWalk_refl_le (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) {j l : ℕ}
    (hl : l ≤ j) :
    dkwWalk σ (fun i => dkwSign σ j i * s i) l = dkwWalk σ s l := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i ∈ dkwPre σ j := dkwPre_mono σ hl hi
  simp [dkwSign, this]

private lemma dkwWalk_refl_full (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (j : ℕ) :
    dkwWalk σ (fun i => dkwSign σ j i * s i) n
      = 2 * dkwWalk σ s j - dkwWalk σ s n := by
  have hj : dkwPre σ j ⊆ dkwPre σ n := by rw [dkwPre_full]; exact Finset.subset_univ _
  have hsplit : ∑ i ∈ dkwPre σ n, dkwSign σ j i * s i
      = ∑ i ∈ dkwPre σ n \ dkwPre σ j, dkwSign σ j i * s i
        + ∑ i ∈ dkwPre σ j, dkwSign σ j i * s i :=
    (Finset.sum_sdiff hj).symm
  have h1 : ∑ i ∈ dkwPre σ j, dkwSign σ j i * s i = dkwWalk σ s j :=
    Finset.sum_congr rfl fun i hi => by simp [dkwSign, hi]
  have hsub : dkwWalk σ s n - dkwWalk σ s j = ∑ i ∈ dkwPre σ n \ dkwPre σ j, s i := by
    simp only [dkwWalk]
    exact (Finset.sum_sdiff_eq_sub hj).symm
  have h2 : ∑ i ∈ dkwPre σ n \ dkwPre σ j, dkwSign σ j i * s i
      = -(dkwWalk σ s n - dkwWalk σ s j) := by
    rw [hsub, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ∉ dkwPre σ j := (Finset.mem_sdiff.mp hi).2
    simp [dkwSign, this]
  simp only [dkwWalk] at hsplit h1 h2 ⊢
  rw [hsplit, h1, h2]
  ring



namespace Levy

variable (σ : Equiv.Perm (Fin n))

/-- The first-passage level sets of the walk. -/
private def dkwPass (a : ℝ) (j : ℕ) : Set (Fin n → ℝ) :=
  {s | ∀ l < j, |dkwWalk σ s l| < a} ∩ {s | a ≤ |dkwWalk σ s j|}

private lemma measurableSet_dkwPass (a : ℝ) (j : ℕ) :
    MeasurableSet (dkwPass σ a j) := by
  have h1 : {s : Fin n → ℝ | ∀ l < j, |dkwWalk σ s l| < a}
      = ⋂ l ∈ (Set.Iio j : Set ℕ), {s : Fin n → ℝ | |dkwWalk σ s l| < a} := by
    ext s; simp [Set.mem_iInter]
  rw [dkwPass, h1]
  refine MeasurableSet.inter (MeasurableSet.biInter (Set.to_countable _) fun l _ => ?_) ?_
  · exact measurableSet_lt (measurable_dkwWalk σ l).abs measurable_const
  · exact measurableSet_le measurable_const (measurable_dkwWalk σ j).abs

private lemma dkwPass_disjoint (a : ℝ) :
    ((Finset.range (n + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint (dkwPass σ a) := by
  intro j _ j' _ hne
  refine Set.disjoint_left.mpr fun s hs hs' => ?_
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hs.2 (not_le.mpr (hs'.1 j h))
  · exact absurd hs'.2 (not_le.mpr (hs.1 j' h))

private lemma dkwMax_subset_iUnion {a : ℝ} :
    {s : Fin n → ℝ | a ≤ dkwMax σ s} ⊆ ⋃ j ∈ Finset.range (n + 1), dkwPass σ a j := by
  intro s hs
  obtain ⟨j0, hj0⟩ := exists_dkwMax_eq σ s
  have hex : ∃ l, a ≤ |dkwWalk σ s l| := ⟨(j0 : ℕ), hj0 ▸ hs⟩
  classical
  set j := Nat.find hex with hjdef
  have hjspec : a ≤ |dkwWalk σ s j| := Nat.find_spec hex
  have hjle : j ≤ n := le_trans (Nat.find_le (hj0 ▸ hs)) (Nat.lt_succ_iff.mp j0.isLt)
  refine Set.mem_biUnion (Finset.mem_range.mpr (by omega)) ⟨fun l hl => ?_, hjspec⟩
  exact not_le.mp (Nat.find_min hex hl)

private lemma signVec_dkwPass_le (a : ℝ) (ha : 0 < a) (j : ℕ) :
    signVec n (dkwPass σ a j)
      ≤ 2 * signVec n (dkwPass σ a j ∩ {s | a ≤ |dkwWalk σ s n|}) := by
  classical
  set R : (Fin n → ℝ) → (Fin n → ℝ) := fun s i => dkwSign σ j i * s i with hR
  have hRmeas : Measurable R :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _
  have hmap : (signVec n).map R = signVec n := signVec_map_mul_pm (dkwSign_pm σ j)
  set B : Set (Fin n → ℝ) := {s | a ≤ |dkwWalk σ s n|} with hB
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const (measurable_dkwWalk σ n).abs
  have hSmeas : MeasurableSet (dkwPass σ a j ∩ B) :=
    (measurableSet_dkwPass σ a j).inter hBmeas
  -- the reflection preserves the measure of the target set
  have hpre : signVec n (R ⁻¹' (dkwPass σ a j ∩ B)) = signVec n (dkwPass σ a j ∩ B) := by
    conv_rhs => rw [← hmap]
    rw [Measure.map_apply hRmeas hSmeas]
  -- coverage
  have hcover : dkwPass σ a j ⊆ (dkwPass σ a j ∩ B) ∪ (R ⁻¹' (dkwPass σ a j ∩ B)) := by
    intro s hs
    by_cases hb : a ≤ |dkwWalk σ s n|
    · exact Or.inl ⟨hs, hb⟩
    · push_neg at hb
      refine Or.inr ⟨⟨fun l hl => ?_, ?_⟩, ?_⟩
      · change |dkwWalk σ (fun i => dkwSign σ j i * s i) l| < a
        rw [dkwWalk_refl_le σ s (le_of_lt hl)]; exact hs.1 l hl
      · change a ≤ |dkwWalk σ (fun i => dkwSign σ j i * s i) j|
        rw [dkwWalk_refl_le σ s (le_refl j)]; exact hs.2
      · change a ≤ |dkwWalk σ (fun i => dkwSign σ j i * s i) n|
        rw [dkwWalk_refl_full σ s j]
        have h1 : a ≤ |dkwWalk σ s j| := hs.2
        have h2 : |2 * dkwWalk σ s j - dkwWalk σ s n|
            ≥ 2 * |dkwWalk σ s j| - |dkwWalk σ s n| := by
          have := abs_sub_abs_le_abs_sub (2 * dkwWalk σ s j) (dkwWalk σ s n)
          rw [abs_mul] at this
          simp only [abs_two] at this
          linarith
        linarith
  calc signVec n (dkwPass σ a j)
      ≤ signVec n ((dkwPass σ a j ∩ B) ∪ (R ⁻¹' (dkwPass σ a j ∩ B))) := measure_mono hcover
    _ ≤ signVec n (dkwPass σ a j ∩ B) + signVec n (R ⁻¹' (dkwPass σ a j ∩ B)) :=
        measure_union_le _ _
    _ = 2 * signVec n (dkwPass σ a j ∩ B) := by rw [hpre]; ring

/-- **Lévy's maximal inequality for the `±1` walk.** -/
private lemma dkw_levy {a : ℝ} (ha : 0 < a) :
    signVec n {s | a ≤ dkwMax σ s} ≤ 2 * signVec n {s | a ≤ |dkwWalk σ s n|} := by
  classical
  set B : Set (Fin n → ℝ) := {s | a ≤ |dkwWalk σ s n|} with hB
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const (measurable_dkwWalk σ n).abs
  have hdisj : ((Finset.range (n + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun j => dkwPass σ a j ∩ B) := fun j hj j' hj' hne =>
    Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (dkwPass_disjoint σ a hj hj' hne)
  calc signVec n {s : Fin n → ℝ | a ≤ dkwMax σ s}
      ≤ signVec n (⋃ j ∈ Finset.range (n + 1), dkwPass σ a j) :=
        measure_mono (dkwMax_subset_iUnion σ)
    _ ≤ ∑ j ∈ Finset.range (n + 1), signVec n (dkwPass σ a j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), 2 * signVec n (dkwPass σ a j ∩ B) :=
        Finset.sum_le_sum fun j _ => signVec_dkwPass_le σ a ha j
    _ = 2 * ∑ j ∈ Finset.range (n + 1), signVec n (dkwPass σ a j ∩ B) := by
        rw [Finset.mul_sum]
    _ = 2 * signVec n (⋃ j ∈ Finset.range (n + 1), (dkwPass σ a j ∩ B)) := by
        rw [measure_biUnion_finset hdisj
          (fun j _ => (measurableSet_dkwPass σ a j).inter hBmeas)]
    _ ≤ 2 * signVec n B := by
        refine mul_le_mul_right (measure_mono ?_) 2
        exact Set.iUnion₂_subset fun j _ => Set.inter_subset_right

end Levy


section Moments

variable (σ : Equiv.Perm (Fin n))

private lemma signVec_ae_abs_le : ∀ᵐ s ∂signVec n, ∀ i, |s i| ≤ 1 := by
  filter_upwards [signVec_ae_pm n] with s hs i
  rcases hs i with h | h <;> simp [h]

private lemma dkwWalk_abs_le {s : Fin n → ℝ} (hs : ∀ i, |s i| ≤ 1) (j : ℕ) :
    |dkwWalk σ s j| ≤ n := by
  calc |dkwWalk σ s j| ≤ ∑ i ∈ dkwPre σ j, |s i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ dkwPre σ j, (1 : ℝ) := Finset.sum_le_sum fun i _ => hs i
    _ = ((dkwPre σ j).card : ℝ) := by simp
    _ ≤ (n : ℝ) := by
        have := Finset.card_le_univ (dkwPre σ j)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this

private lemma dkwMax_abs_le {s : Fin n → ℝ} (hs : ∀ i, |s i| ≤ 1) :
    dkwMax σ s ≤ n := by
  obtain ⟨j, hj⟩ := exists_dkwMax_eq σ s
  rw [hj]; exact dkwWalk_abs_le σ hs _

private lemma integrable_dkwMax : Integrable (dkwMax σ) (signVec n) := by
  refine Integrable.mono' (integrable_const (n : ℝ))
    (measurable_dkwMax σ).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (dkwMax_nonneg σ s)]
  exact dkwMax_abs_le σ hs

private lemma integrable_dkwWalk (j : ℕ) :
    Integrable (fun s => dkwWalk σ s j) (signVec n) := by
  refine Integrable.mono' (integrable_const (n : ℝ))
    (measurable_dkwWalk σ j).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs]
  exact dkwWalk_abs_le σ hs j

private lemma integrable_dkwWalk_sq (j : ℕ) :
    Integrable (fun s => dkwWalk σ s j ^ 2) (signVec n) := by
  refine Integrable.mono' (integrable_const ((n : ℝ) ^ 2))
    ((measurable_dkwWalk σ j).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |dkwWalk σ s j| ≤ (n : ℝ) := dkwWalk_abs_le σ hs j
  have h0 : (0 : ℝ) ≤ |dkwWalk σ s j| := abs_nonneg _
  have h2 : dkwWalk σ s j ^ 2 = |dkwWalk σ s j| ^ 2 := (sq_abs _).symm
  rw [h2]
  nlinarith

/-! Coordinate moments of the sign vector. -/

private lemma integral_coord (i : Fin n) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ s, f (s i) ∂signVec n = ∫ x, f x ∂radLaw := by
  have hmp := measurePreserving_eval_signVec n i
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

private lemma integrable_coord (i : Fin n) :
    Integrable (fun s : Fin n → ℝ => s i) (signVec n) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_pi_apply i).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs]; exact hs i

private lemma integrable_coord_mul (i j : Fin n) :
    Integrable (fun s : Fin n → ℝ => s i * s j) (signVec n) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_pi_apply i).mul (measurable_pi_apply j))).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hs i
  have h2 := hs j
  nlinarith [abs_nonneg (s i), abs_nonneg (s j)]

private lemma integral_coord_id (i : Fin n) : ∫ s : Fin n → ℝ, s i ∂signVec n = 0 := by
  have h := integral_coord (n := n) i (f := fun x => x) measurable_id
  rw [h]; exact radLaw_integral_id

private lemma integral_coord_sq (i : Fin n) :
    ∫ s : Fin n → ℝ, s i * s i ∂signVec n = 1 := by
  have h := integral_coord (n := n) i (f := fun x => x * x)
    (measurable_id.mul measurable_id)
  rw [h, radLaw_integral]; norm_num

private lemma integral_coord_cross {i j : Fin n} (hij : i ≠ j) :
    ∫ s : Fin n → ℝ, s i * s j ∂signVec n = 0 := by
  have hind : IndepFun (fun s : Fin n → ℝ => s i) (fun s : Fin n → ℝ => s j) (signVec n) :=
    (iIndepFun_eval_signVec n).indepFun hij
  rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable]
  change (∫ s : Fin n → ℝ, s i ∂signVec n) * (∫ s : Fin n → ℝ, s j ∂signVec n) = 0
  rw [integral_coord_id, zero_mul]

private lemma integral_dkwWalk_sq_full :
    ∫ s, dkwWalk σ s n ^ 2 ∂signVec n = n := by
  classical
  have hW : (fun s : Fin n → ℝ => dkwWalk σ s n ^ 2)
      = fun s : Fin n → ℝ => ∑ i, ∑ j, s i * s j := by
    funext s
    simp only [dkwWalk, dkwPre_full]
    rw [sq, Finset.sum_mul_sum]
  rw [hW]
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => integrable_coord_mul i j))]
  have hrow : ∀ i : Fin n, ∫ s : Fin n → ℝ, ∑ j, s i * s j ∂signVec n = 1 := by
    intro i
    rw [integral_finset_sum _ (fun j _ => integrable_coord_mul i j)]
    rw [Finset.sum_eq_single i (fun j _ hji => integral_coord_cross (Ne.symm hji))
      (fun h => absurd (Finset.mem_univ i) h)]
    exact integral_coord_sq i
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  simp

private lemma integral_abs_dkwWalk_le (hn : 0 < n) :
    ∫ s, |dkwWalk σ s n| ∂signVec n ≤ Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hss : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have hpt : ∀ s : Fin n → ℝ,
      |dkwWalk σ s n| ≤ (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n) := by
    intro s
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|dkwWalk σ s n| - Real.sqrt n), sq_abs (dkwWalk σ s n)]
  have hint2 : Integrable (fun s : Fin n → ℝ =>
      (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n)) (signVec n) :=
    ((integrable_dkwWalk_sq σ n).add (integrable_const _)).div_const _
  calc ∫ s, |dkwWalk σ s n| ∂signVec n
      ≤ ∫ s, (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n) ∂signVec n :=
        integral_mono ((integrable_dkwWalk σ n).abs) hint2 hpt
    _ = ((∫ s, dkwWalk σ s n ^ 2 ∂signVec n) + (n : ℝ)) / (2 * Real.sqrt n) := by
        rw [integral_div, integral_add (integrable_dkwWalk_sq σ n) (integrable_const _)]
        simp
    _ = Real.sqrt n := by
        rw [integral_dkwWalk_sq_full σ]
        field_simp
        nlinarith [hss]

/-- **The `L¹` maximal bound**: `E max_j |S_j| ≤ 2 √n`. -/
private lemma integral_dkwMax_le (hn : 0 < n) :
    ∫ s, dkwMax σ s ∂signVec n ≤ 2 * Real.sqrt n := by
  have hAbsInt : Integrable (fun s => |dkwWalk σ s n|) (signVec n) :=
    (integrable_dkwWalk σ n).abs
  -- layer cake in `ℝ≥0∞`
  have hlc1 : ∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n
      = ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ dkwMax σ s} :=
    lintegral_eq_lintegral_meas_le _
      (Filter.Eventually.of_forall (dkwMax_nonneg σ)) (measurable_dkwMax σ).aemeasurable
  have hlc2 : ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n
      = ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ |dkwWalk σ s n|} :=
    lintegral_eq_lintegral_meas_le _
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (measurable_dkwWalk σ n).abs.aemeasurable
  have hmono : ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ dkwMax σ s}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), 2 * signVec n {s | t ≤ |dkwWalk σ s n|} := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact Levy.dkw_levy σ ht
  have hconst : ∫⁻ t in Set.Ioi (0 : ℝ), 2 * signVec n {s | t ≤ |dkwWalk σ s n|}
      = 2 * ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ |dkwWalk σ s n|} :=
    lintegral_const_mul' _ _ (by simp)
  have hkey : ∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n
      ≤ 2 * ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n := by
    rw [hlc1, hlc2]; exact hmono.trans_eq hconst
  -- transfer to the Bochner integral
  have hfin : ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n ≠ ⊤ := by
    have h := hAbsInt.hasFiniteIntegral
    have heq : ∀ s : Fin n → ℝ, ENNReal.ofReal |dkwWalk σ s n| = ‖|dkwWalk σ s n|‖ₑ :=
      fun s => (Real.enorm_eq_ofReal (abs_nonneg _)).symm
    simp_rw [heq]
    exact h.ne
  have he1 : ∫ s, dkwMax σ s ∂signVec n
      = (∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (dkwMax_nonneg σ))
      (measurable_dkwMax σ).aestronglyMeasurable
  have he2 : ∫ s, |dkwWalk σ s n| ∂signVec n
      = (∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (measurable_dkwWalk σ n).abs.aestronglyMeasurable
  calc ∫ s, dkwMax σ s ∂signVec n
      = (∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n).toReal := he1
    _ ≤ (2 * ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n).toReal := by
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hkey
    _ = 2 * ∫ s, |dkwWalk σ s n| ∂signVec n := by
        rw [he2, ENNReal.toReal_mul]; norm_num
    _ ≤ 2 * Real.sqrt n := by
        have := integral_abs_dkwWalk_le σ hn
        linarith

end Moments

/-! ### The sorted-prefix representation -/

section Sorting

/-- For a monotone tuple, the sublevel set at `c` is the initial segment of length
`#{l | y l ≤ c}`. -/
private lemma monotone_le_iff_lt_card {y : Fin n → ℝ} (hy : Monotone y) (c : ℝ) (l : Fin n) :
    y l ≤ c ↔ (l : ℕ) < (Finset.univ.filter (fun l : Fin n => y l ≤ c)).card := by
  classical
  set T : Finset (Fin n) := Finset.univ.filter (fun l : Fin n => y l ≤ c) with hT
  have hmemT : ∀ l' : Fin n, l' ∈ T ↔ y l' ≤ c := by intro l'; simp [hT]
  constructor
  · intro hl
    have hsub : Finset.Iic l ⊆ T := fun l' hl' =>
      (hmemT l').mpr (le_trans (hy (Finset.mem_Iic.mp hl')) hl)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    omega
  · intro hl
    by_contra hnot
    have hsub : T ⊆ Finset.Iio l := by
      intro l' hl'
      rw [Finset.mem_Iio]
      by_contra hge
      exact hnot (le_trans (hy (not_lt.mp hge)) ((hmemT l').mp hl'))
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    omega

/-- For every threshold `c`, the set of sample indices below `c` is a prefix of the
sorted order, so the signed count is a value of the `±1` walk. -/
private lemma exists_dkwWalk_eq (x : Fin n → ℝ) (s : Fin n → ℝ) (c : ℝ) :
    ∃ j ≤ n, ∑ i, s i * (if x i ≤ c then (1 : ℝ) else 0)
      = dkwWalk (Tuple.sort x) s j := by
  classical
  set σ : Equiv.Perm (Fin n) := Tuple.sort x with hσ
  have hy : Monotone (x ∘ σ) := Tuple.monotone_sort x
  set T : Finset (Fin n) := Finset.univ.filter (fun l : Fin n => (x ∘ σ) l ≤ c) with hT
  refine ⟨T.card, le_trans (Finset.card_le_univ T) (by simp), ?_⟩
  have hsum : ∑ i, s i * (if x i ≤ c then (1 : ℝ) else 0)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin n => x i ≤ c), s i := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hset : Finset.univ.filter (fun i : Fin n => x i ≤ c) = dkwPre σ T.card := by
    ext i
    simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and]
    have hpt := monotone_le_iff_lt_card hy c (σ.symm i)
    rw [← hT] at hpt
    simpa [Function.comp_def] using hpt
  rw [hsum, hset]
  rfl

private lemma abs_signed_count_le_dkwMax (x : Fin n → ℝ) (s : Fin n → ℝ) (c : ℝ) :
    |∑ i, s i * (if x i ≤ c then (1 : ℝ) else 0)| ≤ dkwMax (Tuple.sort x) s := by
  obtain ⟨j, hj, hval⟩ := exists_dkwWalk_eq x s c
  rw [hval]
  exact dkwWalk_le_dkwMax _ s hj

end Sorting

/-! ### The conditional sign integral -/

section SignIntegral

private lemma measurable_signSup (x : Fin n → ℝ) :
    Measurable (fun s : Fin n → ℝ =>
      ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|) := by
  refine Measurable.iSup fun q => Measurable.abs (Measurable.const_mul ?_ _)
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul measurable_const

private lemma signSup_le (x : Fin n → ℝ) (s : Fin n → ℝ) :
    (⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
      ≤ (n : ℝ)⁻¹ * dkwMax (Tuple.sort x) s := by
  refine ciSup_le fun q => ?_
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (abs_signed_count_le_dkwMax x s _) (by positivity)

private lemma signSup_bddAbove (x : Fin n → ℝ) (s : Fin n → ℝ) :
    BddAbove (Set.range fun q : ℚ =>
      |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|) := by
  refine ⟨(n : ℝ)⁻¹ * dkwMax (Tuple.sort x) s, ?_⟩
  rintro y ⟨q, rfl⟩
  dsimp only
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left (abs_signed_count_le_dkwMax x s _) (by positivity)

private lemma signSup_nonneg (x : Fin n → ℝ) (s : Fin n → ℝ) :
    0 ≤ ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)| :=
  le_ciSup_of_le (signSup_bddAbove x s) 0 (abs_nonneg _)

/-- **The conditional sign bound**: for every realisation `x` of the sample,
`E_ε sup_q |n⁻¹ ∑ᵢ εᵢ 1{xᵢ ≤ q}| ≤ 2/√n`. -/
private lemma integral_signSup_le (hn : 0 < n) (x : Fin n → ℝ) :
    ∫ s, (⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
        ∂signVec n ≤ 2 / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hss : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  set σ : Equiv.Perm (Fin n) := Tuple.sort x with hσ
  have hdom : Integrable (fun s => (n : ℝ)⁻¹ * dkwMax σ s) (signVec n) :=
    (integrable_dkwMax σ).const_mul _
  have hint : Integrable (fun s : Fin n → ℝ =>
      ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
      (signVec n) := by
    refine Integrable.mono' hdom (measurable_signSup x).aestronglyMeasurable ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (signSup_nonneg x s)]
    exact signSup_le x s
  calc ∫ s, (⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, s i * (if x i ≤ (q : ℝ) then (1 : ℝ) else 0)|)
        ∂signVec n
      ≤ ∫ s, (n : ℝ)⁻¹ * dkwMax σ s ∂signVec n :=
        integral_mono hint hdom (fun s => signSup_le x s)
    _ = (n : ℝ)⁻¹ * ∫ s, dkwMax σ s ∂signVec n := integral_const_mul _ _
    _ ≤ (n : ℝ)⁻¹ * (2 * Real.sqrt n) := by
        exact mul_le_mul_of_nonneg_left (integral_dkwMax_le σ hn) (by positivity)
    _ = 2 / Real.sqrt n := by
        field_simp
        nlinarith [hss]

end SignIntegral

end SignWalk

open StatLean.ConcentrationInequalities in
/-- **Mean of the Kolmogorov distance.** For an i.i.d. sample of size `n ≥ 1`,
`√n · E Dₙ ≤ 4`, uniformly in the sampling law.

Proved by symmetrisation (`empirical_symmetrization_countable`), the sorted-prefix walk
representation of the Rademacher process over half-lines, and Lévy's maximal inequality
plus the layer-cake formula (`integral_dkwMax_le`).  See the file header for why the
constant is `4` and not the sharp `0.87…`. -/
theorem integral_ksDist_le {n : ℕ}
    -- USER-INPUT: a nonempty sample (for `n = 0` the statement is false: `D₀ = supₜ F(t)`).
    (hn : 0 < n) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    -- USER-INPUT: the sample variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each observation has law `μ`.
    (hlaw : ∀ i, P.map (X i) = μ) :
    ∫ ω, ksDist X μ ω ∂P ≤ 4 / Real.sqrt n := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  set F : ℚ → ℝ → ℝ := fun q x => if x ≤ (q : ℝ) then (1 : ℝ) else 0 with hFdef
  have hFmeas : ∀ q, Measurable (F q) := fun q =>
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      measurable_const measurable_const
  have hFbdd : ∀ q x, |F q x| ≤ 1 := by
    intro q x; simp only [hFdef]; split_ifs <;> norm_num
  have hFmean : ∀ q : ℚ, ∫ x, F q x ∂μ = cdf μ (q : ℝ) := by
    intro q
    have hind : F q = Set.indicator (Set.Iic ((q : ℝ))) (fun _ => (1 : ℝ)) := by
      funext x
      simp [hFdef, Set.indicator_apply, Set.mem_Iic]
    rw [hind, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, mul_one,
      cdf_eq_real]
  -- Step 1: symmetrisation over the countable class of half-lines.
  have hsym := StatLean.ConcentrationInequalities.empirical_symmetrization_countable
    (μ := P) (P := μ) (X := X) (F := F) hmeas hindep hlaw hFmeas hFbdd
  -- Step 2: the left-hand side is the mean Kolmogorov distance.
  have hLHS : ∫ ω, ⨆ q : ℚ, |(n : ℝ)⁻¹ * (∑ i, F q (X i ω)) - ∫ x, F q x ∂μ| ∂P
      = ∫ ω, ksDist X μ ω ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hrat : ksDist X μ ω = ⨆ q : ℚ, |empCDF X ω (q : ℝ) - cdf μ (q : ℝ)| := by
      refine dkw_iSup_real_eq_iSup_rat (fun t => |empCDF X ω t - cdf μ t|) fun s => ?_
      have hempRC : Tendsto (fun t => empCDF X ω t) (nhdsWithin s (Set.Ioi s))
          (nhds (empCDF X ω s)) := by
        simp only [empCDF]
        exact (tendsto_finset_sum Finset.univ
          fun i _ => dkw_rightCont_step (X i ω) s).const_mul _
      have hcdfRC : Tendsto (fun t => cdf μ t) (nhdsWithin s (Set.Ioi s)) (nhds (cdf μ s)) :=
        ((cdf μ).right_continuous s).mono Set.Ioi_subset_Ici_self
      exact Filter.Tendsto.abs (hempRC.sub hcdfRC)
    rw [hrat]
    refine iSup_congr fun q => ?_
    rw [hFmean q]
    rfl
  -- Step 3: Fubini on the product with the sign randomisation.
  set G : Ω × (Fin n → ℝ) → ℝ :=
    fun p => ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)| with hGdef
  have hGmeas : Measurable G := by
    refine Measurable.iSup fun q => Measurable.abs (Measurable.const_mul ?_ _)
    refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
    · exact (measurable_pi_apply i).comp measurable_snd
    · exact (hFmeas q).comp ((hmeas i).comp measurable_fst)
  have hGbdd : ∀ p : Ω × (Fin n → ℝ), (∀ i, |p.2 i| ≤ 1) → |G p| ≤ 1 := by
    intro p hp
    have hb : ∀ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)| ≤ 1 := by
      intro q
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have h1 : |∑ i, p.2 i * F q (X i p.1)| ≤ (n : ℝ) := by
        calc |∑ i, p.2 i * F q (X i p.1)| ≤ ∑ i, |p.2 i * F q (X i p.1)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [abs_mul]
              exact mul_le_one₀ (hp i) (abs_nonneg _) (hFbdd q _)
          _ = (n : ℝ) := by simp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [inv_mul_le_iff₀ hn0]
      linarith
    have hbdd : BddAbove (Set.range fun q : ℚ => |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)|) :=
      ⟨1, by rintro y ⟨q, rfl⟩; exact hb q⟩
    rw [abs_of_nonneg (le_ciSup_of_le hbdd 0 (abs_nonneg _))]
    exact ciSup_le hb
  have hae : ∀ᵐ p ∂(P.prod (signVec n)), ∀ i, |p.2 i| ≤ 1 :=
    (Measure.quasiMeasurePreserving_snd).ae (signVec_ae_abs_le (n := n))
  have hGint : Integrable G (P.prod (signVec n)) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hGmeas.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    rw [Real.norm_eq_abs]
    exact hGbdd p hp
  have hfub : ∫ p, G p ∂(P.prod (signVec n)) = ∫ ω, ∫ s, G (ω, s) ∂signVec n ∂P :=
    integral_prod G hGint
  -- Step 4: the conditional sign bound, uniformly in the sample.
  have hinner : ∀ ω, ∫ s, G (ω, s) ∂signVec n ≤ 2 / Real.sqrt n := by
    intro ω
    have := integral_signSup_le (n := n) hn (fun i => X i ω)
    simpa [hGdef, hFdef] using this
  have hGnonneg : ∀ p : Ω × (Fin n → ℝ), 0 ≤ G p := by
    intro p
    refine le_ciSup_of_le ⟨(n : ℝ)⁻¹ * ∑ i, |p.2 i|, ?_⟩ 0 (abs_nonneg _)
    rintro y ⟨q, rfl⟩
    dsimp only
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ i, p.2 i * F q (X i p.1)| ≤ ∑ i, |p.2 i * F q (X i p.1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |p.2 i| := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hFbdd q _)
  have hinner0 : ∀ ω, 0 ≤ ∫ s, G (ω, s) ∂signVec n :=
    fun ω => integral_nonneg fun s => hGnonneg (ω, s)
  have hRHS : ∫ p, G p ∂(P.prod (signVec n)) ≤ 2 / Real.sqrt n := by
    rw [hfub]
    calc ∫ ω, ∫ s, G (ω, s) ∂signVec n ∂P
        ≤ ∫ _ω, 2 / Real.sqrt n ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall hinner0)
            (integrable_const _) (Filter.Eventually.of_forall hinner)
      _ = 2 / Real.sqrt n := by simp
  -- Assemble.
  rw [← hLHS]
  calc ∫ ω, ⨆ q : ℚ, |(n : ℝ)⁻¹ * (∑ i, F q (X i ω)) - ∫ x, F q x ∂μ| ∂P
      ≤ 2 * ∫ p, ⨆ q : ℚ, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F q (X i p.1)|
          ∂(P.prod (signVec n)) := hsym
    _ = 2 * ∫ p, G p ∂(P.prod (signVec n)) := rfl
    _ ≤ 2 * (2 / Real.sqrt n) := by linarith [hRHS]
    _ = 4 / Real.sqrt n := by ring

/-- The empirical distribution function as a function of the *sample vector*
`x : Fin n → ℝ`: `F̂ₙ(t) = n⁻¹ #{i : xᵢ ≤ t}`. Equal to `empCDF X ω` at `x = (Xᵢ ω)ᵢ`. -/
private noncomputable def dkwEmp {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, if x i ≤ t then (1 : ℝ) else 0

/-- The Kolmogorov distance as a function of the sample vector `x : Fin n → ℝ`.
Equal to `ksDist X μ ω` at `x = (Xᵢ ω)ᵢ`; the bounded-differences function of McDiarmid. -/
private noncomputable def dkwF {n : ℕ} (μ : Measure ℝ) (x : Fin n → ℝ) : ℝ :=
  ⨆ t : ℝ, |dkwEmp x t - cdf μ t|

/-- **Concentration of the Kolmogorov distance around its mean.**
Changing one observation moves `Dₙ` by at most `1/n`, so the bounded-differences inequality
with constants `cᵢ = 1/n` gives, for `d ≥ 0`,
`P(√n (Dₙ − E Dₙ) ≥ d) ≤ exp(−2 d²)`.

Only independence of the observations is used here; they need not be identically
distributed, and no property of `μ` enters. -/
theorem ksDist_concentration {n : ℕ}
    -- USER-INPUT: a nonempty sample.
    (hn : 0 < n) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    -- USER-INPUT: the sample variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun X P)
    -- USER-INPUT: a nonnegative deviation level.
    {d : ℝ} (hd : 0 ≤ d) :
    P {ω | d ≤ Real.sqrt n * (ksDist X μ ω - ∫ ω', ksDist X μ ω' ∂P)}
      ≤ ENNReal.ofReal (Real.exp (-2 * d ^ 2)) := by
  classical
  set mP : ℝ := ∫ ω, ksDist X μ ω ∂P with hmP_def
  -- `ksDist X μ ω` is the sample-vector Kolmogorov distance evaluated at `(Xᵢ ω)ᵢ`.
  have hksF : ∀ ω, ksDist X μ ω = dkwF μ (StatLean.ConcentrationInequalities.allVars X ω) := by
    intro ω; rfl
  -- basic `[0,1]` bounds on the empirical CDF and hence on the integrand
  have hsum_nonneg : ∀ (z : Fin n → ℝ) (t : ℝ),
      (0 : ℝ) ≤ ∑ i, if z i ≤ t then (1 : ℝ) else 0 :=
    fun z t => Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hsum_le : ∀ (z : Fin n → ℝ) (t : ℝ),
      (∑ i, if z i ≤ t then (1 : ℝ) else 0) ≤ n := fun z t => by
    calc (∑ i, if z i ≤ t then (1 : ℝ) else 0) ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by split_ifs <;> norm_num
      _ = n := by simp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hemp0 : ∀ (z : Fin n → ℝ) t, 0 ≤ dkwEmp z t := fun z t => by
    simp only [dkwEmp]; exact mul_nonneg (by positivity) (hsum_nonneg z t)
  have hemp1 : ∀ (z : Fin n → ℝ) t, dkwEmp z t ≤ 1 := fun z t => by
    simp only [dkwEmp]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact hsum_le z t
  have hA1 : ∀ (z : Fin n → ℝ) t, |dkwEmp z t - cdf μ t| ≤ 1 := fun z t => by
    rw [abs_le]
    exact ⟨by linarith [hemp0 z t, cdf_le_one μ t], by linarith [hemp1 z t, cdf_nonneg μ t]⟩
  have hbddAx : ∀ z : Fin n → ℝ,
      BddAbove (Set.range fun t => |dkwEmp z t - cdf μ t|) :=
    fun z => ⟨1, by rintro _ ⟨t, rfl⟩; exact hA1 z t⟩
  have hF0 : ∀ z, 0 ≤ dkwF μ z := fun z => by
    simp only [dkwF]
    exact le_ciSup_of_le (hbddAx z) 0 (abs_nonneg _)
  have hF1 : ∀ z, dkwF μ z ≤ 1 := fun z => by
    simp only [dkwF]; exact ciSup_le fun t => hA1 z t
  -- measurability of `dkwF μ` (reduce the real sup to a rational one)
  have hf : Measurable (dkwF (n := n) μ) := by
    have hFrat : ∀ x : Fin n → ℝ,
        dkwF μ x = ⨆ q : ℚ, |dkwEmp x (q : ℝ) - cdf μ (q : ℝ)| := by
      intro x
      refine dkw_iSup_real_eq_iSup_rat (fun t => |dkwEmp x t - cdf μ t|) fun s => ?_
      have hempRC : Tendsto (fun t => dkwEmp x t) (nhdsWithin s (Set.Ioi s))
          (nhds (dkwEmp x s)) := by
        simp only [dkwEmp]
        exact (tendsto_finset_sum Finset.univ
          fun i _ => dkw_rightCont_step (x i) s).const_mul _
      have hcdfRC : Tendsto (fun t => cdf μ t) (nhdsWithin s (Set.Ioi s)) (nhds (cdf μ s)) :=
        ((cdf μ).right_continuous s).mono Set.Ioi_subset_Ici_self
      exact Filter.Tendsto.abs (hempRC.sub hcdfRC)
    rw [show dkwF μ = fun x => ⨆ q : ℚ, |dkwEmp x (q : ℝ) - cdf μ (q : ℝ)| from funext hFrat]
    refine Measurable.iSup fun q : ℚ => Measurable.abs (Measurable.sub ?_ measurable_const)
    simp only [dkwEmp]
    exact (Finset.univ.measurable_sum fun i _ =>
      Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const)
        measurable_const measurable_const).const_mul _
  -- bounded differences: changing one coordinate moves `dkwF` by at most `n⁻¹`
  have hbd : ∀ (k : Fin n) (x : Fin n → ℝ) (y : ℝ),
      |dkwF μ x - dkwF μ (Function.update x k y)| ≤ (n : ℝ)⁻¹ := by
    intro k x y
    have hemp_diff : ∀ t, |dkwEmp (Function.update x k y) t - dkwEmp x t| ≤ (n : ℝ)⁻¹ := by
      intro t
      have hsum : (∑ i, if (Function.update x k y) i ≤ t then (1 : ℝ) else 0)
          - (∑ i, if x i ≤ t then (1 : ℝ) else 0)
          = (if y ≤ t then (1 : ℝ) else 0) - (if x k ≤ t then (1 : ℝ) else 0) := by
        rw [← Finset.sum_sub_distrib,
          Finset.sum_eq_single k
            (fun i _ hik => by rw [Function.update_of_ne hik, sub_self])
            (fun h => absurd (Finset.mem_univ k) h),
          Function.update_self]
      have hind : |(if y ≤ t then (1 : ℝ) else 0) - (if x k ≤ t then (1 : ℝ) else 0)| ≤ 1 := by
        by_cases hy : y ≤ t <;> by_cases hxk : x k ≤ t
        · rw [if_pos hy, if_pos hxk]; norm_num
        · rw [if_pos hy, if_neg hxk]; norm_num
        · rw [if_neg hy, if_pos hxk]; norm_num
        · rw [if_neg hy, if_neg hxk]; norm_num
      simp only [dkwEmp]
      rw [← mul_sub, hsum, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      calc (n : ℝ)⁻¹ * |(if y ≤ t then (1 : ℝ) else 0) - (if x k ≤ t then (1 : ℝ) else 0)|
          ≤ (n : ℝ)⁻¹ * 1 := mul_le_mul_of_nonneg_left hind (by positivity)
        _ = (n : ℝ)⁻¹ := mul_one _
    have hApt : ∀ t, |(|dkwEmp (Function.update x k y) t - cdf μ t|)
        - (|dkwEmp x t - cdf μ t|)| ≤ (n : ℝ)⁻¹ := by
      intro t
      have h1 : |(|dkwEmp (Function.update x k y) t - cdf μ t|) - (|dkwEmp x t - cdf μ t|)|
          ≤ |(dkwEmp (Function.update x k y) t - cdf μ t) - (dkwEmp x t - cdf μ t)| :=
        abs_abs_sub_abs_le_abs_sub _ _
      have h2 : (dkwEmp (Function.update x k y) t - cdf μ t) - (dkwEmp x t - cdf μ t)
          = dkwEmp (Function.update x k y) t - dkwEmp x t := by ring
      rw [h2] at h1
      exact h1.trans (hemp_diff t)
    have hle1 : dkwF μ (Function.update x k y) ≤ dkwF μ x + (n : ℝ)⁻¹ := by
      simp only [dkwF]
      refine ciSup_le fun t => ?_
      have hb : |dkwEmp x t - cdf μ t| ≤ ⨆ t', |dkwEmp x t' - cdf μ t'| := le_ciSup (hbddAx x) t
      have hh := hApt t; rw [abs_le] at hh
      linarith [hh.2, hb]
    have hle2 : dkwF μ x ≤ dkwF μ (Function.update x k y) + (n : ℝ)⁻¹ := by
      simp only [dkwF]
      refine ciSup_le fun t => ?_
      have hb : |dkwEmp (Function.update x k y) t - cdf μ t|
          ≤ ⨆ t', |dkwEmp (Function.update x k y) t' - cdf μ t'| := le_ciSup (hbddAx _) t
      have hh := hApt t; rw [abs_le] at hh
      linarith [hh.1, hb]
    rw [abs_le]
    exact ⟨by linarith [hle1], by linarith [hle2]⟩
  -- transfer to the standard-Borel product space `(Fin n → ℝ, Q)`, `Q = P.map (Xᵢ)ᵢ`
  set μi : Fin n → Measure ℝ := fun i => P.map (X i) with hμi
  haveI hμiP : ∀ i, IsProbabilityMeasure (μi i) := fun i => by
    rw [hμi]; exact Measure.isProbabilityMeasure_map (hmeas i).aemeasurable
  set Q : Measure (Fin n → ℝ) := Measure.pi μi with hQ
  have hmeasAV : Measurable (StatLean.ConcentrationInequalities.allVars X) :=
    measurable_pi_lambda _ fun i => hmeas i
  have hQeq : P.map (StatLean.ConcentrationInequalities.allVars X) = Q :=
    (iIndepFun_iff_map_fun_eq_pi_map fun i => (hmeas i).aemeasurable).1 hindep
  set Y : ∀ _ : Fin n, (Fin n → ℝ) → ℝ := fun i x => x i with hY_def
  have hYmeas : ∀ i, Measurable (Y i) := fun i => measurable_pi_apply i
  have hYindep : iIndepFun Y Q := by
    rw [hQ]; exact iIndepFun_pi (X := fun _ => id) fun i => aemeasurable_id
  have hAVYx : ∀ x, StatLean.ConcentrationInequalities.allVars Y x = x := fun _ => rfl
  have hFint : Integrable
      (dkwF μ ∘ StatLean.ConcentrationInequalities.allVars Y) Q := by
    have hInt : Integrable (dkwF μ) Q := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
      exact hF1 x
    simpa [Function.comp_def, hAVYx] using hInt
  -- the McDiarmid sub-Gaussian MGF bound and its Chernoff tail
  have hsg := StatLean.ConcentrationInequalities.mgf_sub_expectation_le
    Y hYmeas (dkwF μ) hf (fun _ => (n : ℝ)⁻¹) (fun _ => by positivity) hbd hYindep hFint
  set t : ℝ := d / Real.sqrt (n : ℝ) with ht_def
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have htge : (0 : ℝ) ≤ t := div_nonneg hd hsqrt_pos.le
  have hchern := hsg.measure_ge_le htge
  -- the sub-Gaussian proxy `∑ (‖n⁻¹‖₊/2)² = 1/(4n)`, giving the exponent `-2 d²`
  have hσcoe : ((∑ _k : Fin n, (‖(n : ℝ)⁻¹‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 1 / (4 * (n : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    field_simp
    ring
  have ht_sq : t ^ 2 = d ^ 2 / n := by
    rw [ht_def, div_pow, Real.sq_sqrt (by positivity)]
  have hexp : -t ^ 2 / (2 * ((∑ _k : Fin n, (‖(n : ℝ)⁻¹‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))
      = -2 * d ^ 2 := by
    rw [hσcoe, ht_sq]
    field_simp
    ring
  rw [hexp] at hchern
  -- rewrite the product-space tail back to the original space
  have hint_eq : (∫ x, dkwF μ x ∂Q) = mP := by
    rw [← hQeq, integral_map hmeasAV.aemeasurable hf.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hksF ω).symm)
  have hset_eq : Q {x | t ≤ dkwF μ (StatLean.ConcentrationInequalities.allVars Y x)
        - ∫ x', dkwF μ (StatLean.ConcentrationInequalities.allVars Y x') ∂Q}
      = P {ω | t ≤ ksDist X μ ω - mP} := by
    simp only [hAVYx]
    rw [hint_eq, ← hQeq,
      Measure.map_apply hmeasAV (measurableSet_le measurable_const (hf.fun_sub measurable_const))]
    rfl
  have hbound : Q {x | t ≤ dkwF μ (StatLean.ConcentrationInequalities.allVars Y x)
        - ∫ x', dkwF μ (StatLean.ConcentrationInequalities.allVars Y x') ∂Q}
      ≤ ENNReal.ofReal (Real.exp (-2 * d ^ 2)) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top Q _)]
    exact ENNReal.ofReal_le_ofReal hchern
  rw [hset_eq] at hbound
  -- finally match the target event via `d ≤ √n · z ↔ d/√n ≤ z`
  have hfinal : {ω | d ≤ Real.sqrt (n : ℝ) * (ksDist X μ ω - mP)}
      = {ω | t ≤ ksDist X μ ω - mP} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [ht_def, div_le_iff₀' hsqrt_pos]
  rw [hfinal]
  exact hbound

/-- **Uniform exponential tail for the empirical process.**
For an i.i.d. sample of size `n ≥ 1` from any law `μ` and any `d ≥ 0`,
$$\mathbb P\bigl(\sqrt n \sup_t |\hat F_n(t) - F(t)| \ge d\bigr) \;\le\; 4\,e^{-d^2/16} .$$
The constants are absolute: they depend neither on `n` nor on `μ`, which is what makes a
fixed rejection threshold distribution-free and valid at every sample size.

Obtained by composing `integral_ksDist_le` (`√n · E Dₙ ≤ 4`) with `ksDist_concentration`;
see the file header for the arithmetic and for the (documented) gap to the sharp constants
`C = 2`, `c = 2`. -/
theorem dkw_uniform {n : ℕ}
    -- USER-INPUT: a nonempty sample.
    (hn : 0 < n) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Fin n → Ω → ℝ)
    -- USER-INPUT: the sample variables are measurable (data regularity).
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each observation has law `μ`.
    (hlaw : ∀ i, P.map (X i) = μ)
    -- USER-INPUT: a nonnegative threshold.
    {d : ℝ} (hd : 0 ≤ d) :
    P {ω | d ≤ Real.sqrt n * ksDist X μ ω}
      ≤ ENNReal.ofReal (4 * Real.exp (-(d ^ 2) / 16)) := by
  -- `log 4 = 2 log 2 > 1.386`, comfortably above the `32/31 = 1.032…` the tail needs.
  have hlog4 : (32 / 31 : ℝ) ≤ Real.log 4 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      push_cast; ring
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [h4]; nlinarith
  by_cases hbig : 1 ≤ 4 * Real.exp (-(d ^ 2) / 16)
  · -- the envelope is `≥ 1`; the bound is vacuous
    calc P {ω | d ≤ Real.sqrt n * ksDist X μ ω}
        ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(d ^ 2) / 16)) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hbig
  · push_neg at hbig
    -- `4 e^{-d²/16} < 1` forces `d > 4`
    have hexp14 : Real.exp (-(d ^ 2) / 16) < 1 / 4 := by
      nlinarith [Real.exp_pos (-(d ^ 2) / 16)]
    have hdsq : 16 * Real.log 4 < d ^ 2 := by
      have h2 : -(d ^ 2) / 16 < Real.log (1 / 4) := by
        calc -(d ^ 2) / 16 = Real.log (Real.exp (-(d ^ 2) / 16)) := (Real.log_exp _).symm
          _ < Real.log (1 / 4) := Real.log_lt_log (Real.exp_pos _) hexp14
      rw [show (1 : ℝ) / 4 = 4⁻¹ by norm_num, Real.log_inv] at h2
      linarith
    have hd4 : 0 ≤ d - 4 := by nlinarith
    -- mean bound: `√n · E[Dₙ] ≤ 4`
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hEle : Real.sqrt (n : ℝ) * ∫ ω, ksDist X μ ω ∂P ≤ 4 := by
      calc Real.sqrt (n : ℝ) * ∫ ω, ksDist X μ ω ∂P
          ≤ Real.sqrt (n : ℝ) * (4 / Real.sqrt (n : ℝ)) :=
            mul_le_mul_of_nonneg_left (integral_ksDist_le hn μ X hmeas hindep hlaw)
              (le_of_lt hsqrt_pos)
        _ = 4 := by field_simp
    -- deviation event forces a bounded-differences deviation
    have hsub : {ω | d ≤ Real.sqrt (n : ℝ) * ksDist X μ ω}
        ⊆ {ω | d - 4 ≤ Real.sqrt (n : ℝ) * (ksDist X μ ω - ∫ ω', ksDist X μ ω' ∂P)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      rw [mul_sub]
      linarith
    have hconc := ksDist_concentration hn μ X hmeas hindep hd4
    calc P {ω | d ≤ Real.sqrt (n : ℝ) * ksDist X μ ω}
        ≤ P {ω | d - 4 ≤ Real.sqrt (n : ℝ) * (ksDist X μ ω - ∫ ω', ksDist X μ ω' ∂P)} :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-2 * (d - 4) ^ 2)) := hconc
      _ ≤ ENNReal.ofReal (4 * Real.exp (-(d ^ 2) / 16)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hkey : d ^ 2 / 16 - 2 * (d - 4) ^ 2 ≤ 32 / 31 := by
            nlinarith [sq_nonneg (31 * d - 128)]
          calc Real.exp (-2 * (d - 4) ^ 2)
              ≤ Real.exp (Real.log 4 + -(d ^ 2) / 16) := by
                exact Real.exp_le_exp.mpr (by linarith)
            _ = 4 * Real.exp (-(d ^ 2) / 16) := by
                rw [Real.exp_add, Real.exp_log (by norm_num)]

end StatLean.HypothesisTesting
