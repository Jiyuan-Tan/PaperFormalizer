module
public import StatLean.Bayesian.DirichletLaplace.ShellDecomposition
public import StatLean.Bayesian.DirichletLaplace.PriorMassRatio
public import StatLean.Bayesian.DirichletLaplace.PosteriorCompressibility
public import StatLean.Bayesian.DirichletLaplace.DenominatorLowerBound
public import StatLean.Bayesian.DirichletLaplace.TestingBound
public import StatLean.Bayesian.ForMathlib.ExpOfRealCalc
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Dirichlet–Laplace posterior contraction — BPPD Theorem 3.1 (C16)

Assembly of BPPD **Theorem 3.1**: in the normal-means model `y = θ + ε`, `ε ~ N(0, Iₙ)`, under the
Dirichlet–Laplace prior with scale `aₙ = n^{−(1+β)}` and the growth condition `‖θ₀‖² ≤ qₙ log⁴n`, the
posterior mass of `{ ‖θ − θ₀‖ > M√(qₙ log n) }` tends to `0` in `E_{θ₀}`.

Objects:
* `dl_contraction_engine` — the fixed-`n` bound with the Theorem 3.4 compressibility Chernoff bound
  *inlined* at the shared radius `r` (denominator event `K θ₀{D < dbar} ≤ e^{−r²/8}` with
  `dbar := e^{−r²}·Π(B(θ₀,r))` via `DenominatorLowerBound.measure_dlDenom_lt_le`, plus the summed
  shell bound via `ShellDecomposition.shell_ratio_le`). Suits the β-regime; kept standalone.
* `dl_contraction_engine'` — the **composed** fixed-`n` bound (BPPD §6 p. 15, D13 resolution): the
  compressibility term appears **abstractly** as the posterior mass of `{|supp_δ| > K}` (consumed from
  Theorem 3.4 as a black box, exactly as the paper does), so each regime can discharge it from the
  proven `dl_theorem34_beta`/`dl_theorem34_recip` while the shells/denominator run at `r² = qₙ log n`.
* `dl_shellSum_reduction` + shell-series machinery — structural reduction of the term-(iii) double
  series to two real tails (Type-I net count; Type-II via shell-disjointness + the box-route ball
  lower bound `dlPrior_closedBall_ge`), see D14.
* `dl_shellSum_tendsto_zero_generic` — the term-(iii) limit at `r² = qₙ log n` for any scale window
  covering both regimes; `dl_shellSum_tendsto_zero_beta` is its β-instance.
* `dl_theorem31` — the headline (rate `M√(qₙ log n)`, deviation D1).
* `dl_theorem31_ball` — the equivalent `𝓝 1` form (BPPD eq. (12)); reduces to `dl_theorem31`.
* `dl_theorem31_paper_rate` — under `qₙ ≤ n^{1−c}`, the paper's minimax rate `sₙ = √(qₙ log(n/qₙ))`;
  reduces to `dl_theorem31`.
* `dl_theorem31_recip` — the `aₙ = 1/n` companion under `qₙ ≥ C₀ log n`, via the composed route
  (D13 resolution).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.1 (statement p. 7, proof §6 pp. 14–16 with
Lemma 6.1); the §6 posterior-contraction assembly.

**Proof formalization notes.** The skeleton is *3.4-term + denominator event + Σ-shells* (the paper's
p. 15 composition, D13): split the complement of the ball into radial shells (`ShellDecomposition`),
bound each shell's posterior contribution by `shell_ratio_le`, and close the double series via
`dl_shellSum_reduction` — Type-I support-pattern count `Σ_{|S|≤K} 33^{|S|} ≤ (K+1)(33n)^K`
(`sum_pow_card_le_nat`) against the radial tail `tsum_ite_ge_exp_neg_sq_le`, Type-II via
shell-disjointness + `dlPrior_closedBall_ge` (D14). The asymptotics live only in the thin corollaries.

**Deviations.**
* **D1 (rate).** The paper states `sₙ² = qₙ log(n/qₙ)` but its proof fixes `rₙ² = qₙ log n` (p. 15) and
  only yields that. The headline `dl_theorem31` therefore states the rate `√(qₙ log n)`; the paper's
  `sₙ` is recovered as `dl_theorem31_paper_rate` under `qₙ ≤ n^{1−c}` (where `log(n/qₙ) ≍ log n`).
* **D2 (regime-dependent `r`).** Both Theorem 3.1 regimes use `r² = qₙ log n` for the shells and
  denominator (the paper, p. 15). The Theorem 3.4 term carries its own internal radius (`r'² = qₙ` in
  its proof, p. 19) — see D13.
* **D4 (net / test geometry).** Inherited from `ShellDecomposition`: `jr/4`-nets (`≤ 33^{|S|}`),
  pieces of radius `≤ (√5/4)jr`, two-parameter midpoint tests with errors `≤ e^{−j²r²/12}`.
* **D13 (two radii, composed — the `1/n` regime).** A single-radius engine that *inlines* the
  compressibility Chernoff bound (as `dl_contraction_engine` does) cannot prove the `aₙ = 1/n` case:
  the inlined compress term needs `r² = qₙ` while the shell series needs `r² = qₙ log n` (at `r² = qₙ`
  the Type-I net count `exp(Aqₙ·log 33n − J₀²qₙ/12) → +∞` for every fixed `J₀`; an intermediate lemma
  asserting otherwise was false and was removed). **Resolution — the paper's own structure (p. 15):**
  compose at the posterior-probability level. "Since `E_{θ₀}ℙ(|supp_{δₙ}(θ)| > Aqₙ | y) → 0` **by
  Theorem 3.4**, it is enough to work with `E_{θ₀}ℙ(‖θ−θ₀‖ > 2Mrₙ, supp ∈ 𝒮ₙ | y)`" — i.e. Theorem 3.4
  is a black box with its own internal radius, and only the sparse remainder runs at `rₙ² = qₙ log n`.
  `dl_contraction_engine'` formalizes exactly this composition; `dl_theorem31_recip` then consumes the
  proven `dl_theorem34_recip`.
* **D14 (coarse Type-II shell bookkeeping).** The paper bounds each net piece's prior-mass ratio
  `β_{S,j,i}` via Lemma 6.1 (eqs. 16–20, costing `(|S|+|S₀|) log n` for general `S`). We instead bound
  the summed Type-II contribution using only (a) shells with distinct support patterns are disjoint, so
  `Σ_S Π(shell_S) ≤ 1`, and (b) the box-route contraction-ball lower bound `dlPrior_closedBall_ge`
  (exponent `O(qₙ log n)` under `hnorm`). Coarser than the paper, same `√(qₙ log n)` rate; it also
  avoids the `θ₀ ⊆ S` constraint of `dlBetaRatio_le` (which stays in `PriorMassRatio` as the faithful
  Lemma 6.1 statement for `S ⊇ S₀`, no longer consumed by this assembly).

**Bibliographic comments.** Posterior contraction rates after Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); sparse-normal-means Bayesian contraction after Castillo and van
der Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

/-- **The denominator threshold** `dbar := e^{−r²}·Π(B(θ₀,r))` used throughout the engine. Below it,
the ratio is controlled by the denominator event (`measure_dlDenom_lt_le`); above it, each shell ratio
is bounded by `shell_ratio_le` (whose `Π(B(θ₀,r))` cancels into the mass ratio). -/
noncomputable def dbarVal {ι : Type*} [Fintype ι] (a r : ℝ) (θ₀ : EuclideanSpace ℝ ι) :
    ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(r ^ 2))) * (dlPrior a ι) (Metric.closedBall θ₀ r)

/-- `WithLp.toLp 2` as a measurable function (with the plain-function head, for `rw` into
`Measure.map_apply` — the `MeasurableEquiv` coercion does not match syntactically). -/
private lemma measurable_toLp {ι : Type*} [Fintype ι] :
    Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
  (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable

/-- The `δ`-support level set `{θ | (univ.filter (δ < |θ i|)) = S}` is measurable (a finite
intersection of measurable coordinate events). -/
private lemma measurableSet_dlSupp_eq {ι : Type*} [Fintype ι] (δ : ℝ) (S : Finset ι) :
    MeasurableSet {θ : EuclideanSpace ℝ ι | (Finset.univ.filter fun i => δ < |θ i|) = S} := by
  classical
  have hpre : {θ : EuclideanSpace ℝ ι | (Finset.univ.filter fun i => δ < |θ i|) = S}
      = ⋂ i : ι, (if i ∈ S then {θ : EuclideanSpace ℝ ι | δ < |θ i|}
          else {θ : EuclideanSpace ℝ ι | ¬ δ < |θ i|}) := by
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hS i
      by_cases hi : i ∈ S
      · simp only [hi, if_true, Set.mem_setOf_eq]
        have : i ∈ Finset.univ.filter fun i => δ < |θ i| := by rw [hS]; exact hi
        simpa [Finset.mem_filter] using this
      · simp only [hi, if_false, Set.mem_setOf_eq]
        intro hlt
        have : i ∈ Finset.univ.filter fun i => δ < |θ i| := by
          simp [Finset.mem_filter, hlt]
        rw [hS] at this; exact hi this
    · intro h
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := h i
      by_cases hiS : i ∈ S
      · simp only [hiS, if_true, Set.mem_setOf_eq] at hi
        simp [hiS, hi]
      · simp only [hiS, if_false, Set.mem_setOf_eq] at hi
        simp [hiS, hi]
  rw [hpre]
  refine MeasurableSet.iInter fun i => ?_
  have hmi : Measurable (fun θ : EuclideanSpace ℝ ι => |θ i|) :=
    ((measurable_pi_apply i).comp ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).measurable).abs
  by_cases hi : i ∈ S
  · simp only [hi, if_true]; exact measurableSet_lt measurable_const hmi
  · simp only [hi, if_false]
    exact (measurableSet_lt measurable_const hmi).compl

/-- The shell `dlShell θ₀ S j r δ` is measurable. -/
private lemma measurableSet_dlShell {ι : Type*} [Fintype ι] (θ₀ : EuclideanSpace ℝ ι)
    (S : Finset ι) (j : ℕ) (r δ : ℝ) : MeasurableSet (dlShell θ₀ S j r δ) := by
  have hnorm : Measurable (fun θ : EuclideanSpace ℝ ι => ‖θ - θ₀‖) :=
    (continuous_id.sub continuous_const).norm.measurable
  refine (measurableSet_dlSupp_eq δ S).inter (MeasurableSet.inter ?_ ?_)
  · exact measurableSet_le measurable_const hnorm
  · exact measurableSet_lt hnorm measurable_const

/-- **Fixed-`n` contraction bound** (BPPD Thm 3.1 engine, honest restatement). For a truth `θ₀`
supported on `S₀`, the `E_{θ₀}`-mean of the posterior mass of `{ ‖θ − θ₀‖ > M·r }` is bounded by three
pieces: the denominator event `e^{−r²/8}`, the Theorem 3.4 compressibility term (`compress_ratio_le_explicit`
on the `S₀ᶜ`-submodel), and the **honest shell double series** — over support patterns `S` (`|S| ≤ K`)
and radial shells `j ≥ J₀` — each term being exactly the `shell_ratio_le` bound
`33^{|S|}·e^{−j²r²/12} + Π(shell)·e^{−j²r²/12}/dbar`.

**Honest restatement (D12).** The previous RHS `… − (A−1)q log c + 3r² … + 2·e^{−M²r²/12}` is provably
false: the `3r²` folds the small-ball correction `2·card'·w` (false as `card' → ∞`), and the closed
`2·e^{−M²r²/12}` drops the net cardinality `33^{|S|}` and the mass ratio, which only vanish
asymptotically. The sum form below is the guaranteed-honest bound the closed bricks actually produce. -/
theorem dl_contraction_engine {ι : Type*} [Fintype ι] {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal.
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: δ-threshold window (dlBetaRatio / small-ball) and net radius control; engine-internal.
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδnet : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    -- LEAN-ONLY: 0 < r — contraction radius (rₙ); engine-internal.
    (hr : 0 < r) (θ₀ : EuclideanSpace ℝ ι) (S₀ : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S₀; engine-internal.
    (hθ₀ : ∀ i ∉ S₀, θ₀ i = 0)
    -- LEAN-ONLY: prior gives positive mass to the contraction ball (full support); engine-internal.
    (hBpos : 0 < (dlPrior a ι) (Metric.closedBall θ₀ r))
    -- LEAN-ONLY: 0 < M — contraction multiplier; engine-internal.
    (M : ℝ) (hM : 0 < M)
    -- LEAN-ONLY: support-count threshold K and radial floor J₀ = ⌈M/2⌉ ≥ 2; engine-internal.
    (K J₀ : ℕ) (hJ2 : 2 ≤ J₀) (hJ₀ : (J₀ : ℝ) ≤ M / 2)
    -- LEAN-ONLY: Chernoff cut `k` for the compress event `{K < |supp_δ|}`; engine-internal.
    (k : ℕ) (hk : (S₀.card : ℝ) + (k : ℝ) ≤ (K : ℝ))
    -- LEAN-ONLY: C3 δ-exceedance bound `z` and small-ball tail bound `w` (submodel); engine-internal.
    (z : ℝ) (hz : (dlMarginal a {x : ℝ | δ < |x|}).toReal ≤ z)
    (w : ℝ)
    (hw : (dlMarginal a
        {x : ℝ | min (r / Real.sqrt (Fintype.card {i : ι // i ∉ S₀} : ℝ)) (1 / 2) < |x|}).toReal ≤ w)
    (hw2 : w ≤ 1 / 2)
    -- LEAN-ONLY: 1 < c — Chernoff parameter; engine-internal.
    (c : ℝ) (hc : 1 < c) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y {θ | M * r < ‖θ - θ₀‖}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8))
          + (ENNReal.ofReal (Real.exp ((Fintype.card {i : ι // i ∉ S₀} : ℝ) * z * (c - 1)
                - (k : ℝ) * Real.log c + r ^ 2 + 2 * (Fintype.card {i : ι // i ∉ S₀} : ℝ) * w))
              + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)))
          + ∑ S ∈ (Finset.univ : Finset ι).powerset.filter (fun S => S.card ≤ K),
              ∑' j : ℕ, (if J₀ ≤ j then
                (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
                + (dlPrior a ι) (dlShell θ₀ S j r δ)
                    * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbarVal a r θ₀
                else 0) := by
  classical
  set π : Measure (EuclideanSpace ℝ ι) := dlPrior a ι with hπ
  set μ := gaussShiftKernel ι θ₀ with hμ
  set C : Set (EuclideanSpace ℝ ι) := {θ | M * r < ‖θ - θ₀‖} with hCdef
  set Cbad : Set (EuclideanSpace ℝ ι) := {θ | (K : ℝ) < (dlSuppCount δ θ : ℝ)} with hCbaddef
  set 𝒮 := (Finset.univ : Finset ι).powerset.filter (fun S => S.card ≤ K) with h𝒮def
  set dbar : ℝ≥0∞ := dbarVal a r θ₀ with hdbardef
  set U : Set (EuclideanSpace ℝ ι) := ⋃ S ∈ 𝒮, ⋃ (j : ℕ), ⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ
    with hUdef
  set G : Set (EuclideanSpace ℝ ι) := {y | dbar ≤ dlDenom θ₀ π y} with hGdef
  -- Basic facts.
  have hdbarpos : 0 < dbar := by
    rw [hdbardef, dbarVal]
    exact ENNReal.mul_pos (by simp [Real.exp_pos]) (ne_of_gt hBpos)
  have hCmeas : MeasurableSet C := by
    rw [hCdef]
    exact measurableSet_lt measurable_const ((continuous_id.sub continuous_const).norm.measurable)
  have hcast : Measurable (fun θ : EuclideanSpace ℝ ι => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hCbadmeas : MeasurableSet Cbad := by
    rw [hCbaddef]; exact measurableSet_lt measurable_const hcast
  have hGmeas : MeasurableSet G := by
    rw [hGdef]; exact measurableSet_le measurable_const (measurable_dlDenom θ₀ π)
  have hUmeas : MeasurableSet U := by
    rw [hUdef]
    refine MeasurableSet.biUnion (Finset.countable_toSet 𝒮) fun S _ => ?_
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => measurableSet_dlShell θ₀ S j r δ
  -- `dlNumer` as the `withDensity` measure of the parameter set (for subadditivity).
  have hν_eq : ∀ (y : EuclideanSpace ℝ ι) {D : Set (EuclideanSpace ℝ ι)}, MeasurableSet D →
      dlNumer θ₀ π D y = (π.withDensity (fun θ => dlLR θ₀ θ y)) D := by
    intro y D hD; rw [dlNumer, ← withDensity_apply _ hD]
  -- The geometric decomposition `C ⊆ Cbad ∪ U`.
  have hdecomp : C ⊆ Cbad ∪ U := by
    intro θ hθ
    rw [hCdef, Set.mem_setOf_eq] at hθ
    by_cases hbad : θ ∈ Cbad
    · exact Or.inl hbad
    · refine Or.inr ?_
      rw [hCbaddef, Set.mem_setOf_eq, not_lt] at hbad
      set S := Finset.univ.filter fun i => δ < |θ i| with hSdef
      have hScard : S.card ≤ K := by
        have : (dlSuppCount δ θ : ℝ) ≤ (K : ℝ) := hbad
        have hle : dlSuppCount δ θ ≤ K := by exact_mod_cast this
        rwa [dlSuppCount, ← hSdef] at hle
      have hSmem : S ∈ 𝒮 := by
        rw [h𝒮def, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.subset_univ _, hScard⟩
      have hd : 0 < ‖θ - θ₀‖ := lt_trans (by positivity) hθ
      set j := ⌊‖θ - θ₀‖ / (2 * r)⌋₊ with hjdef
      have hr2 : 0 < 2 * r := by linarith
      have hjle : (j : ℝ) ≤ ‖θ - θ₀‖ / (2 * r) := Nat.floor_le (by positivity)
      have hltj : ‖θ - θ₀‖ / (2 * r) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      have hJ0j : J₀ ≤ j := by
        rw [hjdef]
        apply Nat.le_floor
        rw [le_div_iff₀ hr2]
        have : (J₀ : ℝ) ≤ M / 2 := hJ₀
        nlinarith [hθ, hM, hr]
      rw [hUdef, Set.mem_iUnion₂]
      refine ⟨S, hSmem, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨j, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨hJ0j, ?_⟩
      rw [dlShell, Set.mem_setOf_eq]
      refine ⟨hSdef.symm, ?_, ?_⟩
      · calc 2 * (j : ℝ) * r = (j : ℝ) * (2 * r) := by ring
          _ ≤ (‖θ - θ₀‖ / (2 * r)) * (2 * r) := by
              apply mul_le_mul_of_nonneg_right hjle (by positivity)
          _ = ‖θ - θ₀‖ := by field_simp
      · calc ‖θ - θ₀‖ = (‖θ - θ₀‖ / (2 * r)) * (2 * r) := by field_simp
          _ < ((j : ℝ) + 1) * (2 * r) := by apply mul_lt_mul_of_pos_right hltj hr2
          _ = 2 * ((j : ℝ) + 1) * r := by ring
  -- Bridge to the ratio, then split the integral at the denominator threshold `G`.
  rw [lintegral_posterior_eq_lintegral_ratio θ₀ π hCmeas]
  rw [← lintegral_add_compl (μ := μ) (f := fun y => dlNumer θ₀ π C y / dlDenom θ₀ π y) hGmeas]
  -- The complement `Gᶜ` is the denominator event.
  have hGc : Gᶜ = {y | dlDenom θ₀ π y
      < ENNReal.ofReal (Real.exp (-(r ^ 2))) * π (Metric.closedBall θ₀ r)} := by
    rw [hGdef]; ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hdbardef, dbarVal, hπ]
  -- Term (i): the denominator event.
  have hi : ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
    calc ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
        ≤ ∫⁻ _ in Gᶜ, 1 ∂μ := by
          refine setLIntegral_mono (measurable_const) fun y _ => ?_
          exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact dlNumer_le_dlDenom θ₀ π C y)
      _ = μ Gᶜ := by rw [setLIntegral_one]
      _ ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
          rw [hGc, hμ, show (- r ^ 2 / 8 : ℝ) = -(r ^ 2 / 8) by ring]
          exact measure_dlDenom_lt_le π θ₀ hr
  -- Term over `G`: split numerator `C ⊆ Cbad ∪ U`.
  have hnumer_le : ∀ y, dlNumer θ₀ π C y ≤ dlNumer θ₀ π Cbad y + dlNumer θ₀ π U y := by
    intro y
    calc dlNumer θ₀ π C y ≤ dlNumer θ₀ π (Cbad ∪ U) y := dlNumer_mono θ₀ π hdecomp y
      _ = (π.withDensity (fun θ => dlLR θ₀ θ y)) (Cbad ∪ U) := hν_eq y (hCbadmeas.union hUmeas)
      _ ≤ (π.withDensity (fun θ => dlLR θ₀ θ y)) Cbad
            + (π.withDensity (fun θ => dlLR θ₀ θ y)) U := measure_union_le _ _
      _ = dlNumer θ₀ π Cbad y + dlNumer θ₀ π U y := by
          rw [hν_eq y hCbadmeas, hν_eq y hUmeas]
  have hGsplit : ∫⁻ y in G, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
        + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ := by
    rw [← lintegral_add_left ((measurable_dlNumer θ₀ π Cbad).fun_div (measurable_dlDenom θ₀ π))]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hnumer_le y) _
  -- Term (ii): the compressibility bound.
  have hii : ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card {i : ι // i ∉ S₀} : ℝ) * z * (c - 1)
            - (k : ℝ) * Real.log c + r ^ 2 + 2 * (Fintype.card {i : ι // i ∉ S₀} : ℝ) * w))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
    calc ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
        ≤ ∫⁻ y, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ y, ((gaussShiftKernel ι)†π) y Cbad ∂μ := by
          rw [hμ, lintegral_posterior_eq_lintegral_ratio θ₀ π hCbadmeas]
      _ ≤ ∫⁻ y, ((gaussShiftKernel ι)†π) y
              {θ | ((S₀.card : ℝ) + (k : ℝ)) < (dlSuppCount δ θ : ℝ)} ∂μ := by
          rw [hμ]
          refine lintegral_mono fun y => measure_mono fun θ hθ => ?_
          rw [hCbaddef, Set.mem_setOf_eq] at hθ
          rw [Set.mem_setOf_eq]; linarith [hk, hθ]
      _ ≤ _ := (dl_compress_reduction ha θ₀ S₀ hθ₀ k).trans
          (compress_ratio_le_explicit ha hr k z hz w hw hw2 c hc)
  -- Term (iii): the shell double series.
  have hiii : ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ
      ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
          (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
          + π (dlShell θ₀ S j r δ)
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbar else 0) := by
    -- Pointwise: `numer U / denom ≤ ∑_S ∑'_j (if J₀≤j then numer(shell)/denom else 0)`.
    have hUsub : ∀ y, dlNumer θ₀ π U y / dlDenom θ₀ π y
        ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
            dlNumer θ₀ π (dlShell θ₀ S j r δ) y / dlDenom θ₀ π y else 0) := by
      intro y
      have hUmass : dlNumer θ₀ π U y
          ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then dlNumer θ₀ π (dlShell θ₀ S j r δ) y else 0) := by
        rw [hν_eq y hUmeas, hUdef]
        refine le_trans (measure_biUnion_finset_le 𝒮 _) (Finset.sum_le_sum fun S _ => ?_)
        refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun j => ?_)
        by_cases hj : J₀ ≤ j
        · rw [if_pos hj]
          have : (⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ) = dlShell θ₀ S j r δ := by simp [hj]
          rw [this, ← hν_eq y (measurableSet_dlShell θ₀ S j r δ)]
        · rw [if_neg hj]
          have : (⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ) = ∅ := by simp [hj]
          rw [this, measure_empty]
      calc dlNumer θ₀ π U y / dlDenom θ₀ π y
          ≤ (∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then dlNumer θ₀ π (dlShell θ₀ S j r δ) y else 0))
              / dlDenom θ₀ π y := ENNReal.div_le_div_right hUmass _
        _ = ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
              dlNumer θ₀ π (dlShell θ₀ S j r δ) y / dlDenom θ₀ π y else 0) := by
            rw [div_eq_mul_inv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [← ENNReal.tsum_mul_right]
            refine tsum_congr fun j => ?_
            by_cases hj : J₀ ≤ j <;> simp [hj, div_eq_mul_inv]
    refine le_trans (setLIntegral_mono ?_ fun y _ => hUsub y) ?_
    · exact Finset.measurable_sum _ fun S _ =>
        Measurable.ennreal_tsum fun j => by
          by_cases hj : J₀ ≤ j
          · simp only [hj, if_true]
            exact (measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)
          · simp only [hj, if_false]; exact measurable_const
    -- Integrate the finite sum / countable series term by term.
    rw [lintegral_finset_sum _ fun S _ => Measurable.ennreal_tsum fun j => by
        by_cases hj : J₀ ≤ j
        · simp only [hj, if_true]
          exact (measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)
        · simp only [hj, if_false]; exact measurable_const]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [lintegral_tsum fun j => by
        by_cases hj : J₀ ≤ j
        · simp only [hj, if_true]
          exact ((measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)).aemeasurable
        · simp only [hj, if_false]; exact aemeasurable_const]
    refine ENNReal.tsum_le_tsum fun j => ?_
    by_cases hj : J₀ ≤ j
    · simp only [if_pos hj]
      have hj2 : 2 ≤ j := le_trans hJ2 hj
      exact shell_ratio_le θ₀ S hj2 ha hr hδnet dbar hdbarpos
    · simp only [if_neg hj]
      simp
  -- Assemble the three pieces `(i) + (ii) + (iii)`.
  have hfinal := add_le_add (add_le_add hi hii) hiii
  calc ∫⁻ y in G, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
        + ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ (∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
            + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ)
          + ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ :=
        add_le_add hGsplit le_rfl
    _ = (∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
            + ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ)
          + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ := by ring
    _ ≤ _ := hfinal

/-- **Fixed-`n` contraction bound, composed form** (BPPD §6 p. 15). The posterior mass of
`{‖θ − θ₀‖ > M·r}` is bounded by the posterior mass of the compressibility event
`{|supp_δ| > K}` — left **abstract**, exactly as the paper consumes Theorem 3.4 as a black box
("Since E_{θ₀}ℙ(|supp| > Aqₙ | y) → 0 by Theorem 3.4, it is enough to work with …", p. 15) with
its own internal radius — plus the denominator event `e^{−r²/8}` and the shell double series at
THIS `r`. Unlike `dl_contraction_engine` (which inlines the compressibility Chernoff bound at the
shared radius, making the `aₙ = 1/n` regime unprovable — the former D13 two-scale obstruction),
this composed form lets each regime discharge the 3.4-term from the proven
`dl_theorem34_beta`/`dl_theorem34_recip` directly (D13 resolution). -/
theorem dl_contraction_engine' {ι : Type*} [Fintype ι] {a δ r : ℝ}
    -- LEAN-ONLY: 0 < a — DL scale; engine-internal.
    (ha : 0 < a)
    -- LEAN-ONLY: 0 < δ — δ-threshold; engine-internal.
    (hδ0 : 0 < δ)
    -- LEAN-ONLY: √n·δ ≤ r — net radius control (D4); engine-internal.
    (hδnet : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    -- LEAN-ONLY: 0 < r — contraction radius; engine-internal.
    (hr : 0 < r) (θ₀ : EuclideanSpace ℝ ι)
    -- LEAN-ONLY: prior charges the contraction ball (dlPrior_closedBall_pos); engine-internal.
    (hBpos : 0 < (dlPrior a ι) (Metric.closedBall θ₀ r))
    -- LEAN-ONLY: 0 < M — contraction multiplier; engine-internal.
    (M : ℝ) (hM : 0 < M)
    -- LEAN-ONLY: support-count threshold K and radial floor J₀ ≤ M/2; engine-internal.
    (K J₀ : ℕ) (hJ2 : 2 ≤ J₀) (hJ₀ : (J₀ : ℝ) ≤ M / 2) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y {θ | M * r < ‖θ - θ₀‖}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y {θ | (K : ℝ) < (dlSuppCount δ θ : ℝ)}
            ∂(gaussShiftKernel ι θ₀)
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8))
          + ∑ S ∈ (Finset.univ : Finset ι).powerset.filter (fun S => S.card ≤ K),
              ∑' j : ℕ, (if J₀ ≤ j then
                (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
                + (dlPrior a ι) (dlShell θ₀ S j r δ)
                    * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbarVal a r θ₀
                else 0) := by
  classical
  set π : Measure (EuclideanSpace ℝ ι) := dlPrior a ι with hπ
  set μ := gaussShiftKernel ι θ₀ with hμ
  set C : Set (EuclideanSpace ℝ ι) := {θ | M * r < ‖θ - θ₀‖} with hCdef
  set Cbad : Set (EuclideanSpace ℝ ι) := {θ | (K : ℝ) < (dlSuppCount δ θ : ℝ)} with hCbaddef
  set 𝒮 := (Finset.univ : Finset ι).powerset.filter (fun S => S.card ≤ K) with h𝒮def
  set dbar : ℝ≥0∞ := dbarVal a r θ₀ with hdbardef
  set U : Set (EuclideanSpace ℝ ι) := ⋃ S ∈ 𝒮, ⋃ (j : ℕ), ⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ
    with hUdef
  set G : Set (EuclideanSpace ℝ ι) := {y | dbar ≤ dlDenom θ₀ π y} with hGdef
  -- Basic facts.
  have hdbarpos : 0 < dbar := by
    rw [hdbardef, dbarVal]
    exact ENNReal.mul_pos (by simp [Real.exp_pos]) (ne_of_gt hBpos)
  have hCmeas : MeasurableSet C := by
    rw [hCdef]
    exact measurableSet_lt measurable_const ((continuous_id.sub continuous_const).norm.measurable)
  have hcast : Measurable (fun θ : EuclideanSpace ℝ ι => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hCbadmeas : MeasurableSet Cbad := by
    rw [hCbaddef]; exact measurableSet_lt measurable_const hcast
  have hGmeas : MeasurableSet G := by
    rw [hGdef]; exact measurableSet_le measurable_const (measurable_dlDenom θ₀ π)
  have hUmeas : MeasurableSet U := by
    rw [hUdef]
    refine MeasurableSet.biUnion (Finset.countable_toSet 𝒮) fun S _ => ?_
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => measurableSet_dlShell θ₀ S j r δ
  -- `dlNumer` as the `withDensity` measure of the parameter set (for subadditivity).
  have hν_eq : ∀ (y : EuclideanSpace ℝ ι) {D : Set (EuclideanSpace ℝ ι)}, MeasurableSet D →
      dlNumer θ₀ π D y = (π.withDensity (fun θ => dlLR θ₀ θ y)) D := by
    intro y D hD; rw [dlNumer, ← withDensity_apply _ hD]
  -- The geometric decomposition `C ⊆ Cbad ∪ U`.
  have hdecomp : C ⊆ Cbad ∪ U := by
    intro θ hθ
    rw [hCdef, Set.mem_setOf_eq] at hθ
    by_cases hbad : θ ∈ Cbad
    · exact Or.inl hbad
    · refine Or.inr ?_
      rw [hCbaddef, Set.mem_setOf_eq, not_lt] at hbad
      set S := Finset.univ.filter fun i => δ < |θ i| with hSdef
      have hScard : S.card ≤ K := by
        have : (dlSuppCount δ θ : ℝ) ≤ (K : ℝ) := hbad
        have hle : dlSuppCount δ θ ≤ K := by exact_mod_cast this
        rwa [dlSuppCount, ← hSdef] at hle
      have hSmem : S ∈ 𝒮 := by
        rw [h𝒮def, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.subset_univ _, hScard⟩
      have hd : 0 < ‖θ - θ₀‖ := lt_trans (by positivity) hθ
      set j := ⌊‖θ - θ₀‖ / (2 * r)⌋₊ with hjdef
      have hr2 : 0 < 2 * r := by linarith
      have hjle : (j : ℝ) ≤ ‖θ - θ₀‖ / (2 * r) := Nat.floor_le (by positivity)
      have hltj : ‖θ - θ₀‖ / (2 * r) < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      have hJ0j : J₀ ≤ j := by
        rw [hjdef]
        apply Nat.le_floor
        rw [le_div_iff₀ hr2]
        have : (J₀ : ℝ) ≤ M / 2 := hJ₀
        nlinarith [hθ, hM, hr]
      rw [hUdef, Set.mem_iUnion₂]
      refine ⟨S, hSmem, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨j, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨hJ0j, ?_⟩
      rw [dlShell, Set.mem_setOf_eq]
      refine ⟨hSdef.symm, ?_, ?_⟩
      · calc 2 * (j : ℝ) * r = (j : ℝ) * (2 * r) := by ring
          _ ≤ (‖θ - θ₀‖ / (2 * r)) * (2 * r) := by
              apply mul_le_mul_of_nonneg_right hjle (by positivity)
          _ = ‖θ - θ₀‖ := by field_simp
      · calc ‖θ - θ₀‖ = (‖θ - θ₀‖ / (2 * r)) * (2 * r) := by field_simp
          _ < ((j : ℝ) + 1) * (2 * r) := by apply mul_lt_mul_of_pos_right hltj hr2
          _ = 2 * ((j : ℝ) + 1) * r := by ring
  -- Bridge to the ratio, then split the integral at the denominator threshold `G`.
  rw [lintegral_posterior_eq_lintegral_ratio θ₀ π hCmeas]
  rw [← lintegral_add_compl (μ := μ) (f := fun y => dlNumer θ₀ π C y / dlDenom θ₀ π y) hGmeas]
  -- The complement `Gᶜ` is the denominator event.
  have hGc : Gᶜ = {y | dlDenom θ₀ π y
      < ENNReal.ofReal (Real.exp (-(r ^ 2))) * π (Metric.closedBall θ₀ r)} := by
    rw [hGdef]; ext y
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hdbardef, dbarVal, hπ]
  -- Term (i): the denominator event.
  have hi : ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
    calc ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
        ≤ ∫⁻ _ in Gᶜ, 1 ∂μ := by
          refine setLIntegral_mono (measurable_const) fun y _ => ?_
          exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact dlNumer_le_dlDenom θ₀ π C y)
      _ = μ Gᶜ := by rw [setLIntegral_one]
      _ ≤ ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
          rw [hGc, hμ, show (- r ^ 2 / 8 : ℝ) = -(r ^ 2 / 8) by ring]
          exact measure_dlDenom_lt_le π θ₀ hr
  -- Term over `G`: split numerator `C ⊆ Cbad ∪ U`.
  have hnumer_le : ∀ y, dlNumer θ₀ π C y ≤ dlNumer θ₀ π Cbad y + dlNumer θ₀ π U y := by
    intro y
    calc dlNumer θ₀ π C y ≤ dlNumer θ₀ π (Cbad ∪ U) y := dlNumer_mono θ₀ π hdecomp y
      _ = (π.withDensity (fun θ => dlLR θ₀ θ y)) (Cbad ∪ U) := hν_eq y (hCbadmeas.union hUmeas)
      _ ≤ (π.withDensity (fun θ => dlLR θ₀ θ y)) Cbad
            + (π.withDensity (fun θ => dlLR θ₀ θ y)) U := measure_union_le _ _
      _ = dlNumer θ₀ π Cbad y + dlNumer θ₀ π U y := by
          rw [hν_eq y hCbadmeas, hν_eq y hUmeas]
  have hGsplit : ∫⁻ y in G, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
        + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ := by
    rw [← lintegral_add_left ((measurable_dlNumer θ₀ π Cbad).fun_div (measurable_dlDenom θ₀ π))]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hnumer_le y) _
  -- Term (ii): compressibility left ABSTRACT — truncated at the backwards-bridge (D13).
  have hii : ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
      ≤ ∫⁻ y, ((gaussShiftKernel ι)†π) y Cbad ∂μ := by
    calc ∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
        ≤ ∫⁻ y, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = ∫⁻ y, ((gaussShiftKernel ι)†π) y Cbad ∂μ := by
          rw [hμ, lintegral_posterior_eq_lintegral_ratio θ₀ π hCbadmeas]
  -- Term (iii): the shell double series.
  have hiii : ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ
      ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
          (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
          + π (dlShell θ₀ S j r δ)
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbar else 0) := by
    -- Pointwise: `numer U / denom ≤ ∑_S ∑'_j (if J₀≤j then numer(shell)/denom else 0)`.
    have hUsub : ∀ y, dlNumer θ₀ π U y / dlDenom θ₀ π y
        ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
            dlNumer θ₀ π (dlShell θ₀ S j r δ) y / dlDenom θ₀ π y else 0) := by
      intro y
      have hUmass : dlNumer θ₀ π U y
          ≤ ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then dlNumer θ₀ π (dlShell θ₀ S j r δ) y else 0) := by
        rw [hν_eq y hUmeas, hUdef]
        refine le_trans (measure_biUnion_finset_le 𝒮 _) (Finset.sum_le_sum fun S _ => ?_)
        refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun j => ?_)
        by_cases hj : J₀ ≤ j
        · rw [if_pos hj]
          have : (⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ) = dlShell θ₀ S j r δ := by simp [hj]
          rw [this, ← hν_eq y (measurableSet_dlShell θ₀ S j r δ)]
        · rw [if_neg hj]
          have : (⋃ (_ : J₀ ≤ j), dlShell θ₀ S j r δ) = ∅ := by simp [hj]
          rw [this, measure_empty]
      calc dlNumer θ₀ π U y / dlDenom θ₀ π y
          ≤ (∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then dlNumer θ₀ π (dlShell θ₀ S j r δ) y else 0))
              / dlDenom θ₀ π y := ENNReal.div_le_div_right hUmass _
        _ = ∑ S ∈ 𝒮, ∑' j : ℕ, (if J₀ ≤ j then
              dlNumer θ₀ π (dlShell θ₀ S j r δ) y / dlDenom θ₀ π y else 0) := by
            rw [div_eq_mul_inv, Finset.sum_mul]
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [← ENNReal.tsum_mul_right]
            refine tsum_congr fun j => ?_
            by_cases hj : J₀ ≤ j <;> simp [hj, div_eq_mul_inv]
    refine le_trans (setLIntegral_mono ?_ fun y _ => hUsub y) ?_
    · exact Finset.measurable_sum _ fun S _ =>
        Measurable.ennreal_tsum fun j => by
          by_cases hj : J₀ ≤ j
          · simp only [hj, if_true]
            exact (measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)
          · simp only [hj, if_false]; exact measurable_const
    -- Integrate the finite sum / countable series term by term.
    rw [lintegral_finset_sum _ fun S _ => Measurable.ennreal_tsum fun j => by
        by_cases hj : J₀ ≤ j
        · simp only [hj, if_true]
          exact (measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)
        · simp only [hj, if_false]; exact measurable_const]
    refine Finset.sum_le_sum fun S _ => ?_
    rw [lintegral_tsum fun j => by
        by_cases hj : J₀ ≤ j
        · simp only [hj, if_true]
          exact ((measurable_dlNumer θ₀ π _).div (measurable_dlDenom θ₀ π)).aemeasurable
        · simp only [hj, if_false]; exact aemeasurable_const]
    refine ENNReal.tsum_le_tsum fun j => ?_
    by_cases hj : J₀ ≤ j
    · simp only [if_pos hj]
      have hj2 : 2 ≤ j := le_trans hJ2 hj
      exact shell_ratio_le θ₀ S hj2 ha hr hδnet dbar hdbarpos
    · simp only [if_neg hj]
      simp
  -- Assemble the three pieces: `(posterior_Cbad) + (i) + (iii)` in the composed ordering.
  calc ∫⁻ y in G, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
        + ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ
      ≤ (∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
            + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ)
          + ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ :=
        add_le_add hGsplit le_rfl
    _ = (∫⁻ y in G, dlNumer θ₀ π Cbad y / dlDenom θ₀ π y ∂μ
            + ∫⁻ y in Gᶜ, dlNumer θ₀ π C y / dlDenom θ₀ π y ∂μ)
          + ∫⁻ y in G, dlNumer θ₀ π U y / dlDenom θ₀ π y ∂μ := by ring
    _ ≤ _ := add_le_add (add_le_add hii hi) hiii

/-- **Density positivity off the origin.** For `0 < a` and `x ≠ 0`, `dlDensity a x > 0` (the mixture
integral of a strictly positive integrand over `(0,∞)`). -/
private lemma dlDensity_pos {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≠ 0) : 0 < dlDensity a x := by
  rw [dlDensity_eq_ofReal_integral ha hx, ENNReal.ofReal_pos]
  -- The integrand is `> 0` on `Ioi 0`, and `Ioi 0` has positive measure.
  apply setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrable_dlDensity_integrand ha hx) |>.mpr
  · -- support ∩ Ioi 0 has positive measure: it is all of Ioi 0
    have hsupp : Function.support
        (fun ψ => dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ)) ∩ Set.Ioi (0:ℝ)
        = Set.Ioi (0:ℝ) := by
      ext ψ
      simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, Set.mem_Ioi]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro hψ
        refine ⟨?_, hψ⟩
        have : 0 < dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - |x| / ψ) := by
          apply mul_pos (mul_pos (dlNormConst_pos ha) (Real.rpow_pos_of_pos hψ _))
            (Real.exp_pos _)
        exact ne_of_gt this
    rw [hsupp]
    simp [Real.volume_Ioi]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun ψ (hψ : 0 < ψ) => ?_)
    exact le_of_lt (mul_pos (mul_pos (dlNormConst_pos ha) (Real.rpow_pos_of_pos hψ _))
      (Real.exp_pos _))

/-- **Marginal positivity on any interval.** For `0 < a`, the DL marginal charges every interval
`{x | |x − c| ≤ s}` of positive half-width `s > 0` with positive mass (the density is a.e. positive,
being `> 0` off the single origin). -/
private lemma dlMarginal_abs_sub_le_pos {a : ℝ} (ha : 0 < a) (c s : ℝ) (hs : 0 < s) :
    0 < dlMarginal a {x : ℝ | |x - c| ≤ s} := by
  have hset : {x : ℝ | |x - c| ≤ s} = Set.Icc (c - s) (c + s) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hmeas : MeasurableSet {x : ℝ | |x - c| ≤ s} := by
    rw [hset]; exact measurableSet_Icc
  rw [dlMarginal_eq_withDensity ha, withDensity_apply _ hmeas,
    setLIntegral_pos_iff measurable_dlDensity]
  -- `support (dlDensity a) ⊇ {x ≠ 0}`, so `support ∩ S ⊇ S \ {0}`, of positive volume.
  have hsub : {x : ℝ | |x - c| ≤ s} \ {0} ⊆ Function.support (dlDensity a) ∩ {x | |x - c| ≤ s} := by
    intro x hx
    obtain ⟨hxS, hx0⟩ := hx
    refine ⟨?_, hxS⟩
    simp only [Function.mem_support, ne_eq]
    exact ne_of_gt (dlDensity_pos ha (by simpa using hx0))
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [measure_diff_null (measure_singleton 0), hset, Real.volume_Icc]
  simp only [ENNReal.ofReal_pos]
  linarith


/-! ### Shell-series machinery (D14)

Ported from the `bay/dl-thm31-shellsum` closure work: the structural reduction of the term-(iii)
shell double series to two real tails, with Type-II handled by shell-disjointness (`Σ_S Π(shell_S)
≤ 1`) plus the box-route contraction-ball lower bound `dlPrior_closedBall_ge` — avoiding any
per-piece prior-mass ratio (and hence the `θ₀ ⊆ S` constraint of `dlBetaRatio_le`; the paper
instead pays `(|S|+|S₀|) log n` in Lemma 6.1, eqs. 17–20). -/

/-- Reindex a `≥ J₀`-restricted `ℕ`-`tsum` to a shifted full `tsum`. -/
private lemma tsum_ite_ge_shift {g : ℕ → ℝ≥0∞} (J₀ : ℕ) :
    ∑' j : ℕ, (if J₀ ≤ j then g j else 0) = ∑' j : ℕ, g (J₀ + j) := by
  calc ∑' j : ℕ, (if J₀ ≤ j then g j else 0)
      = ∑' j : ℕ, ({n : ℕ | J₀ ≤ n}.indicator g) j := by
        refine tsum_congr fun j => ?_
        rw [Set.indicator_apply]; simp only [Set.mem_setOf_eq]
    _ = ∑' x : {n : ℕ // J₀ ≤ n}, g x := (tsum_subtype {n : ℕ | J₀ ≤ n} g).symm
    _ = ∑' j : ℕ, g (J₀ + j) :=
        (Equiv.tsum_eq
          { toFun := fun j => (⟨J₀ + j, Nat.le_add_right _ _⟩ : {n : ℕ // J₀ ≤ n})
            invFun := fun x => x.1 - J₀
            left_inv := fun j => by simp
            right_inv := fun x => Subtype.ext (Nat.add_sub_cancel' x.2) }
          (fun x : {n : ℕ // J₀ ≤ n} => g x)).symm

/-- The `≥ J₀`-restricted Gaussian-tail series is bounded by twice its leading term. -/
private lemma tsum_ite_ge_exp_neg_sq_le (J₀ : ℕ) {ρ D : ℝ} (hD : 0 < D)
    (h1 : 1 ≤ (2 * (J₀ : ℝ) + 1) * ρ / D) :
    (∑' j : ℕ, (if J₀ ≤ j then ENNReal.ofReal (Real.exp (-(j : ℝ) ^ 2 * ρ / D)) else 0))
      ≤ 2 * ENNReal.ofReal (Real.exp (-(J₀ : ℝ) ^ 2 * ρ / D)) := by
  rw [tsum_ite_ge_shift]
  have hc : (0 : ℝ) < 1 / D := by positivity
  have hh : 1 ≤ (1 / D) * (2 * (J₀ : ℝ) + 1) * ρ := by
    rw [show (1 / D) * (2 * (J₀ : ℝ) + 1) * ρ = (2 * (J₀ : ℝ) + 1) * ρ / D by ring]; exact h1
  have hkey := tsum_ofReal_exp_neg_sq_le (1 / D) ρ J₀ hc hh
  calc (∑' j : ℕ, ENNReal.ofReal (Real.exp (-((J₀ + j : ℕ) : ℝ) ^ 2 * ρ / D)))
      = ∑' j : ℕ, ENNReal.ofReal (Real.exp (-(1 / D) * ((J₀ + j : ℕ) : ℝ) ^ 2 * ρ)) := by
        refine tsum_congr fun j => ?_; congr 2; ring
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-(1 / D) * (J₀ : ℝ) ^ 2 * ρ)) := hkey
    _ = 2 * ENNReal.ofReal (Real.exp (-(J₀ : ℝ) ^ 2 * ρ / D)) := by congr 2; ring

/-- Support-pattern count: `∑_{S ⊆ Fin n, |S| ≤ K} 33^{|S|} ≤ (K+1)·(33n)^K` (grouping by card,
`C(n,k) ≤ n^k`). -/
private lemma sum_pow_card_le_nat (n K : ℕ) (hn : 1 ≤ n) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ K), 33 ^ S.card)
      ≤ (K + 1) * (33 * n) ^ K := by
  classical
  have hset : (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ K)
      = (Finset.range (K + 1)).biUnion (fun k => (Finset.univ : Finset (Fin n)).powersetCard k) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard⟩; exact ⟨S.card, Nat.lt_succ_of_le hcard, hsub, rfl⟩
    · rintro ⟨k, _, hsub, hcard⟩; exact ⟨hsub, by omega⟩
  rw [hset, Finset.sum_biUnion]
  · calc ∑ k ∈ Finset.range (K + 1),
          ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, 33 ^ S.card
        = ∑ k ∈ Finset.range (K + 1),
            ((Finset.univ : Finset (Fin n)).powersetCard k).card * 33 ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have hc : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, (33 : ℕ) ^ S.card = 33 ^ k :=
            fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
          rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
      _ = ∑ k ∈ Finset.range (K + 1), n.choose k * 33 ^ k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∑ k ∈ Finset.range (K + 1), (33 * n) ^ K := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkK : k ≤ K := by rw [Finset.mem_range] at hk; omega
          calc n.choose k * 33 ^ k ≤ n ^ k * 33 ^ k :=
                Nat.mul_le_mul_right _ (Nat.choose_le_pow n k)
            _ = (33 * n) ^ k := by rw [mul_pow]; ring
            _ ≤ (33 * n) ^ K := Nat.pow_le_pow_right (by omega) hkK
      _ = (K + 1) * (33 * n) ^ K := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun S hSa hSb => ?_
    rw [Finset.mem_powersetCard] at hSa hSb
    exact hab (by rw [← hSa.2, ← hSb.2])

/-- **Per-coordinate interval lower bound.** The DL marginal charges `{x | |x − c| ≤ s}` with at
least (min density on the interval) × width `= 2s·(a/64)·exp(−3 − (7/2)√(|c|+s))`. -/
private lemma dlMarginal_abs_sub_le_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c s : ℝ) (hs : 0 < s) :
    ENNReal.ofReal (2 * s * ((a / 64) * Real.exp (-3 - (7 / 2) * Real.sqrt (|c| + s))))
      ≤ dlMarginal a {x : ℝ | |x - c| ≤ s} := by
  have hset : {x : ℝ | |x - c| ≤ s} = Set.Icc (c - s) (c + s) := by
    ext x; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  have hmeas : MeasurableSet {x : ℝ | |x - c| ≤ s} := by rw [hset]; exact measurableSet_Icc
  set C : ℝ := (a / 64) * Real.exp (-3 - (7 / 2) * Real.sqrt (|c| + s)) with hC
  have hCnn : 0 ≤ C := mul_nonneg (div_nonneg ha.le (by norm_num)) (Real.exp_pos _).le
  have hpt : ∀ x ∈ {x : ℝ | |x - c| ≤ s}, ENNReal.ofReal C ≤ dlDensity a x := by
    intro x hx
    have hxle : |x| ≤ |c| + s := by
      calc |x| = |c + (x - c)| := by ring_nf
        _ ≤ |c| + |x - c| := abs_add_le _ _
        _ ≤ |c| + s := by have := hx; simp only [Set.mem_setOf_eq] at this; linarith
    have hanti : dlDensity a (|c| + s) ≤ dlDensity a x :=
      dlDensity_anti (by rw [abs_of_nonneg (add_nonneg (abs_nonneg c) hs.le)]; exact hxle)
    refine le_trans ?_ hanti
    have hge := dlDensity_ge ha ha1 (|c| + s)
    rwa [abs_of_nonneg (by positivity : (0:ℝ) ≤ |c| + s)] at hge
  rw [dlMarginal_eq_withDensity ha, withDensity_apply _ hmeas]
  calc ENNReal.ofReal (2 * s * C)
      = ENNReal.ofReal C * ENNReal.ofReal (2 * s) := by
        rw [← ENNReal.ofReal_mul hCnn]; congr 1; ring
    _ = ∫⁻ _x in {x : ℝ | |x - c| ≤ s}, ENNReal.ofReal C := by
        rw [setLIntegral_const, hset, Real.volume_Icc]; congr 2; ring
    _ ≤ ∫⁻ x in {x : ℝ | |x - c| ≤ s}, dlDensity a x := setLIntegral_mono measurable_dlDensity hpt

/-- **Contraction-ball prior lower bound (box route).** The DL prior charges `closedBall θ₀ r` with at
least the coordinatewise box mass: support coordinates via `dlMarginal_abs_sub_le_ge`, zero coordinates
via the `1 − ζ ≥ e^{−2ζ}` small-ball bound. No volume/Γ factor (the box factorizes exactly). -/
private lemma dlPrior_closedBall_ge {ι : Type*} [Fintype ι] {a r ζ : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 < r) (θ₀ : EuclideanSpace ℝ ι)
    (hζ : dlMarginal a {x : ℝ | min (r / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2) < |x|}
      ≤ ENNReal.ofReal ζ)
    (hζ2 : ζ ≤ 1 / 2) (hζ0 : 0 ≤ ζ) :
    ENNReal.ofReal (Real.exp (
        ((Finset.univ.filter (fun j => θ₀ j ≠ 0)).card : ℝ)
            * (Real.log (2 * min (r / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2) * (a / 64)) - 3)
          - 7 / 2 * (∑ j ∈ Finset.univ.filter (fun j => θ₀ j ≠ 0),
              Real.sqrt (|θ₀ j| + min (r / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2)))
          - 2 * ζ * (Fintype.card ι : ℝ)))
      ≤ dlPrior a ι (Metric.closedBall θ₀ r) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Empty index: everything is a single point; the ball is `univ`.
    have huniv : Metric.closedBall θ₀ r = Set.univ := by
      ext θ; simp only [Metric.mem_closedBall, Set.mem_univ, iff_true]
      rw [Subsingleton.elim θ θ₀, dist_self]; exact hr.le
    have hfilt : (Finset.univ.filter (fun j => θ₀ j ≠ 0)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; exact fun j => (IsEmpty.false j).elim
    rw [huniv, measure_univ, hfilt]
    have hcard0 : Fintype.card ι = 0 := Fintype.card_eq_zero
    simp [hcard0]
  set m : ℝ := (Fintype.card ι : ℝ) with hm_def
  have hmpos : 0 < m := by rw [hm_def]; exact_mod_cast Fintype.card_pos
  set s : ℝ := min (r / Real.sqrt m) (1 / 2) with hs_def
  have hspos : 0 < s := by rw [hs_def]; exact lt_min (by positivity) (by norm_num)
  have hs_le : Real.sqrt m * s ≤ r := by
    calc Real.sqrt m * s ≤ Real.sqrt m * (r / Real.sqrt m) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.sqrt_nonneg _)
      _ = r := by
          rw [mul_div_cancel₀]; exact Real.sqrt_ne_zero'.mpr hmpos
  -- The box sits inside the ball.
  have hbox_sub : {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} ⊆ Metric.closedBall θ₀ r := by
    intro θ hθ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsum : ∑ j, (θ j - θ₀ j) ^ 2 ≤ m * s ^ 2 := by
      calc ∑ j, (θ j - θ₀ j) ^ 2 ≤ ∑ _j : ι, s ^ 2 :=
            Finset.sum_le_sum fun j _ => by nlinarith [hθ j, abs_nonneg (θ j - θ₀ j), sq_abs (θ j - θ₀ j)]
        _ = m * s ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm_def]
    have hnormsq : ‖θ - θ₀‖ ^ 2 = ∑ j, (θ j - θ₀ j) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (θ - θ₀) j = θ j - θ₀ j from rfl]
    calc ‖θ - θ₀‖ = Real.sqrt (‖θ - θ₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (∑ j, (θ j - θ₀ j) ^ 2) := by rw [hnormsq]
      _ ≤ Real.sqrt (m * s ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt m * s := by rw [Real.sqrt_mul hmpos.le, Real.sqrt_sq hspos.le]
      _ ≤ r := hs_le
  -- The box mass factorizes into per-coordinate marginals.
  have hbox_meas : MeasurableSet {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => measurableSet_le ?_ measurable_const
    exact (((measurable_pi_apply j).comp
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable).sub measurable_const).abs
  have hbox_eq : dlPrior a ι {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s}
      = ∏ j, dlMarginal a {x : ℝ | |x - θ₀ j| ≤ s} := by
    have hpre : (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹'
        {θ | ∀ j, |θ j - θ₀ j| ≤ s} = Set.univ.pi (fun j => {y : ℝ | |y - θ₀ j| ≤ s}) := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi, PiLp.toLp_apply]
    rw [dlPrior, Measure.map_apply measurable_toLp hbox_meas, hpre, Measure.pi_pi]
  -- Per-coordinate lower bound `exp(gexp (θ₀ j)) ≤ marginal`.
  set gexp : ℝ → ℝ := fun c =>
    if c = 0 then -2 * ζ else Real.log (2 * s * (a / 64)) - 3 - 7 / 2 * Real.sqrt (|c| + s) with hgexp
  have hcoord : ∀ j : ι, ENNReal.ofReal (Real.exp (gexp (θ₀ j)))
      ≤ dlMarginal a {x : ℝ | |x - θ₀ j| ≤ s} := by
    intro j
    by_cases hj : θ₀ j = 0
    · simp only [hgexp, hj, if_true]
      have hcompl : dlMarginal a {x : ℝ | |x| ≤ s} = 1 - dlMarginal a {x : ℝ | s < |x|} := by
        rw [show {x : ℝ | |x| ≤ s} = {x : ℝ | s < |x|}ᶜ by ext x; simp [not_lt],
          prob_compl_eq_one_sub (measurableSet_lt measurable_const continuous_abs.measurable)]
      have hexple : Real.exp (-2 * ζ) ≤ 1 - ζ := by
        have hpos : (0 : ℝ) < 1 + 2 * ζ := by linarith
        have hE : (1 : ℝ) + 2 * ζ ≤ Real.exp (2 * ζ) := by
          have := Real.add_one_le_exp (2 * ζ); linarith
        have hinv : Real.exp (-2 * ζ) ≤ 1 / (1 + 2 * ζ) := by
          rw [show (-2 * ζ : ℝ) = -(2 * ζ) from by ring, Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le hpos hE
        refine hinv.trans ?_
        rw [div_le_iff₀ hpos]; nlinarith [hζ0, hζ2]
      have hstep : ENNReal.ofReal (Real.exp (-2 * ζ)) ≤ dlMarginal a {x : ℝ | |x| ≤ s} := by
        rw [hcompl]
        calc ENNReal.ofReal (Real.exp (-2 * ζ)) ≤ ENNReal.ofReal (1 - ζ) :=
              ENNReal.ofReal_le_ofReal hexple
          _ = 1 - ENNReal.ofReal ζ := by
              rw [ENNReal.ofReal_sub _ hζ0, ENNReal.ofReal_one]
          _ ≤ 1 - dlMarginal a {x : ℝ | s < |x|} := by
              rw [hs_def] at hζ ⊢; exact tsub_le_tsub_left hζ 1
      simpa using hstep
    · simp only [hgexp, hj, if_false]
      have hpos : (0 : ℝ) < 2 * s * (a / 64) := by positivity
      have heq : Real.exp (Real.log (2 * s * (a / 64)) - 3 - 7 / 2 * Real.sqrt (|θ₀ j| + s))
          = 2 * s * ((a / 64) * Real.exp (-3 - 7 / 2 * Real.sqrt (|θ₀ j| + s))) := by
        rw [show Real.log (2 * s * (a / 64)) - 3 - 7 / 2 * Real.sqrt (|θ₀ j| + s)
              = Real.log (2 * s * (a / 64)) + (-3 - 7 / 2 * Real.sqrt (|θ₀ j| + s)) from by ring,
          Real.exp_add, Real.exp_log hpos]
        ring
      rw [heq]
      exact dlMarginal_abs_sub_le_ge ha ha1 (θ₀ j) s hspos
  -- Assemble the product bound and split by support.
  have hprod : ENNReal.ofReal (Real.exp (∑ j, gexp (θ₀ j)))
      ≤ dlPrior a ι (Metric.closedBall θ₀ r) := by
    refine le_trans ?_ (le_trans (le_of_eq hbox_eq.symm) (measure_mono hbox_sub))
    rw [Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le)]
    exact Finset.prod_le_prod' (fun j _ => hcoord j)
  refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) hprod
  -- `∑ⱼ gexp(θ₀ⱼ) ≥ LBexp`.
  rw [show (∑ j, gexp (θ₀ j))
      = ∑ j ∈ Finset.univ.filter (fun j => θ₀ j = 0), gexp (θ₀ j)
        + ∑ j ∈ Finset.univ.filter (fun j => θ₀ j ≠ 0), gexp (θ₀ j) from
      (Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => θ₀ j = 0) _).symm]
  have hzero_sum : ∑ j ∈ Finset.univ.filter (fun j => θ₀ j = 0), gexp (θ₀ j)
      = ((Finset.univ.filter (fun j => θ₀ j = 0)).card : ℝ) * (-2 * ζ) := by
    rw [Finset.sum_congr rfl (fun j hj => by
        simp only [hgexp]; rw [if_pos (Finset.mem_filter.mp hj).2]),
      Finset.sum_const, nsmul_eq_mul]
  have hsupp_sum : ∑ j ∈ Finset.univ.filter (fun j => θ₀ j ≠ 0), gexp (θ₀ j)
      = ((Finset.univ.filter (fun j => θ₀ j ≠ 0)).card : ℝ) * (Real.log (2 * s * (a / 64)) - 3)
        - 7 / 2 * (∑ j ∈ Finset.univ.filter (fun j => θ₀ j ≠ 0), Real.sqrt (|θ₀ j| + s)) := by
    rw [Finset.sum_congr rfl (fun j hj => show gexp (θ₀ j)
          = (Real.log (2 * s * (a / 64)) - 3) - 7 / 2 * Real.sqrt (|θ₀ j| + s) by
        simp only [hgexp]; rw [if_neg (Finset.mem_filter.mp hj).2]),
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [hzero_sum, hsupp_sum]
  have hcardle : ((Finset.univ.filter (fun j => θ₀ j = 0)).card : ℝ) ≤ m := by
    rw [hm_def]
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq Finset.card_univ
  have hprod2 : 2 * ζ * ((Finset.univ.filter (fun j => θ₀ j = 0)).card : ℝ) ≤ 2 * ζ * m :=
    mul_le_mul_of_nonneg_left hcardle (by linarith)
  linarith [hprod2]

/-- The shells `dlShell θ₀ S j r δ` for distinct support patterns `S` (at fixed `j, r, δ`) are disjoint
(a point has a unique `δ`-support), so their prior masses sum to at most `1`. -/
private lemma sum_dlPrior_dlShell_le_one {ι : Type*} [Fintype ι] (a : ℝ) (θ₀ : EuclideanSpace ℝ ι)
    (j : ℕ) (r δ : ℝ) (𝒮 : Finset (Finset ι)) :
    ∑ S ∈ 𝒮, dlPrior a ι (dlShell θ₀ S j r δ) ≤ 1 := by
  classical
  haveI : IsProbabilityMeasure (dlPrior a ι) := inferInstance
  have hdisj : (↑𝒮 : Set (Finset ι)).PairwiseDisjoint (fun S => dlShell θ₀ S j r δ) := by
    intro S _ S' _ hne
    refine Set.disjoint_left.mpr fun x hxS hxS' => ?_
    apply hne
    rw [← (show (Finset.univ.filter fun i => δ < |x i|) = S from hxS.1),
      ← (show (Finset.univ.filter fun i => δ < |x i|) = S' from hxS'.1)]
  calc ∑ S ∈ 𝒮, dlPrior a ι (dlShell θ₀ S j r δ)
      = dlPrior a ι (⋃ S ∈ 𝒮, dlShell θ₀ S j r δ) :=
        (measure_biUnion_finset hdisj (fun S _ => measurableSet_dlShell θ₀ S j r δ)).symm
    _ ≤ 1 := prob_le_one

/-- The clamped per-coordinate box half-width `min(rrₙ/√n, 1/2)` (β/recip regimes). -/
private noncomputable def dlBoxS (rr : ℕ → ℝ) (n : ℕ) : ℝ :=
  min (rr n / Real.sqrt (n : ℝ)) (1 / 2)

/-- The `C3` tail bound `ζ` for the contraction-ball prior lower bound (β/recip regimes). -/
private noncomputable def dlZeta (av rr : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.exp 1 * av n * (8 + 2 * Real.log (1 / dlBoxS rr n))

/-- The contraction-ball prior lower-bound exponent (`dlPrior_closedBall_ge` at `a = av n`, `r = rr n`,
`ζ = dlZeta`), specialized to `ι = Fin n` (`Fintype.card = n`). -/
private noncomputable def dlLBexp (av rr : ℕ → ℝ) (θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n))
    (n : ℕ) : ℝ :=
  ((Finset.univ.filter (fun j => θ₀ n j ≠ 0)).card : ℝ)
      * (Real.log (2 * dlBoxS rr n * (av n / 64)) - 3)
    - 7 / 2 * (∑ j ∈ Finset.univ.filter (fun j => θ₀ n j ≠ 0),
        Real.sqrt (|θ₀ n j| + dlBoxS rr n))
    - 2 * dlZeta av rr n * (n : ℝ)

/-- Squeeze to `0`: a nonnegative sequence dominated by `exp(K·rrₙ²)` with `K < 0` and `rrₙ² → ∞`. -/
private lemma tendsto_of_le_exp_neg {rr f : ℕ → ℝ} {K : ℝ} (hK : K < 0)
    (hrr : Tendsto (fun n => (rr n) ^ 2) atTop atTop)
    (hf0 : ∀ᶠ n in atTop, 0 ≤ f n)
    (hfle : ∀ᶠ n in atTop, f n ≤ Real.exp (K * (rr n) ^ 2)) :
    Tendsto f atTop (𝓝 0) := by
  have hg : Tendsto (fun n => Real.exp (K * (rr n) ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg hK hrr)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg hf0 hfle

/-- Sparse Cauchy–Schwarz: `∑_{j∈s} √|θⱼ| ≤ (card s)^{3/4}·‖θ‖^{1/2}` (uses only `∑_{j∈s}|θⱼ|² ≤ ‖θ‖²`). -/
private lemma sum_sqrt_abs_finset_le {ι : Type*} [Fintype ι] (s : Finset ι)
    (θ : EuclideanSpace ℝ ι) :
    ∑ j ∈ s, Real.sqrt |θ j| ≤ (s.card : ℝ) ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ) := by
  set c : ℝ := (s.card : ℝ) with hc_def
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hnn : 0 ≤ ∑ j ∈ s, Real.sqrt |θ j| := Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hsumsq_le : ∑ j ∈ s, |θ j| ^ 2 ≤ ‖θ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      Finset.sum_congr rfl (fun j _ => sq_abs (θ j) : ∀ j ∈ s, |θ j| ^ 2 = θ j ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) (fun i _ _ => sq_nonneg _)
  have stepA : (∑ j ∈ s, Real.sqrt |θ j|) ^ 2 ≤ c * ∑ j ∈ s, |θ j| := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun j => Real.sqrt |θ j|)
    simpa only [Real.sq_sqrt (abs_nonneg _), hc_def] using h
  have stepB : ∑ j ∈ s, |θ j| ≤ Real.sqrt c * ‖θ‖ := by
    have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun j => |θ j|)
    rw [← hc_def] at h
    have hsq : ∑ j ∈ s, |θ j| ^ 2 = ∑ j ∈ s, |θ j| ^ 2 := rfl
    have h2 : (∑ j ∈ s, |θ j|) ^ 2 ≤ c * ‖θ‖ ^ 2 :=
      h.trans (mul_le_mul_of_nonneg_left hsumsq_le hc)
    have hsnn : 0 ≤ ∑ j ∈ s, |θ j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq hsnn, show c * ‖θ‖ ^ 2 = (Real.sqrt c * ‖θ‖) ^ 2 by
        rw [mul_pow, Real.sq_sqrt hc], Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _)
        (norm_nonneg _))] at this
  have hmm : c ^ (3 / 2 : ℝ) = c * Real.sqrt c := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hc (by norm_num), Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hR : (c ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ)) ^ 2 = c ^ (3 / 2 : ℝ) * ‖θ‖ := by
    rw [mul_pow, ← Real.rpow_natCast (c ^ (3 / 4 : ℝ)) 2, ← Real.rpow_mul hc,
      ← Real.rpow_natCast (‖θ‖ ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  have key : (∑ j ∈ s, Real.sqrt |θ j|) ^ 2 ≤ (c ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ)) ^ 2 := by
    refine stepA.trans ((mul_le_mul_of_nonneg_left stepB hc).trans (le_of_eq ?_))
    rw [hR, hmm, ← mul_assoc]
  have hrhs_nn : 0 ≤ c ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hc _) (Real.rpow_nonneg (norm_nonneg _) _)
  have := Real.sqrt_le_sqrt key
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs_nn] at this

/-- **Structural reduction of the shell double series.** Given the regime abbreviations `av, rr, Kf`
and eventual per-`n` regularity, the term-(iii) double series is bounded by `ofReal RI + ofReal RII`,
where `RI` is the Type-I (net-count) tail and `RII` the Type-II (shell/denominator) tail; hence it
`→ 0` once both real tails do. Type II uses only `∑_S Π(shellₛ) ≤ 1` (disjointness) and the box-route
prior lower bound `dlPrior_closedBall_ge` — no per-piece `dlBetaRatio` (which would need `θ₀ ⊆ S`). -/
private lemma dl_shellSum_reduction {av rr : ℕ → ℝ} {Kf : ℕ → ℕ}
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)} (J₀ : ℕ) (hJ2 : 2 ≤ J₀)
    (hstruct : ∀ᶠ n in atTop, 1 ≤ n ∧ 0 < av n ∧ av n ≤ 1 ∧ 0 < rr n
      ∧ 1 ≤ (2 * (J₀ : ℝ) + 1) * (rr n) ^ 2 / 12
      ∧ 0 < rr n / Real.sqrt (n : ℝ)
      ∧ dlZeta av rr n ≤ 1 / 2)
    (hRI : Tendsto (fun n => 2 * ((Kf n : ℝ) + 1) * (33 * (n : ℝ)) ^ (Kf n)
        * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12)) atTop (𝓝 0))
    (hRII : Tendsto (fun n => 2 * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12
        + (rr n) ^ 2 - dlLBexp av rr θ₀ n)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ Kf n),
        ∑' j : ℕ, (if J₀ ≤ j then
          (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (-(j : ℝ) ^ 2 * (rr n) ^ 2 / 12))
          + (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n))
              * ENNReal.ofReal (Real.exp (-(j : ℝ) ^ 2 * (rr n) ^ 2 / 12))
              / dbarVal (av n) (rr n) (θ₀ n)
          else 0)) atTop (𝓝 0) := by
  classical
  have hUI : Tendsto (fun n => ENNReal.ofReal (2 * ((Kf n : ℝ) + 1) * (33 * (n : ℝ)) ^ (Kf n)
      * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hRI
  have hUII : Tendsto (fun n => ENNReal.ofReal (2 * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12
      + (rr n) ^ 2 - dlLBexp av rr θ₀ n))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hRII
  have hupper : Tendsto (fun n => ENNReal.ofReal (2 * ((Kf n : ℝ) + 1) * (33 * (n : ℝ)) ^ (Kf n)
        * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12))
      + ENNReal.ofReal (2 * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12
        + (rr n) ^ 2 - dlLBexp av rr θ₀ n))) atTop (𝓝 0) := by
    simpa using hUI.add hUII
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hstruct] with n hn
  obtain ⟨hn1, havp, hav1, hrrp, hthr, hδp, hζ2⟩ := hn
  have hδboxpos : 0 < dlBoxS rr n := by rw [dlBoxS]; exact lt_min hδp (by norm_num)
  have hδboxlt1 : dlBoxS rr n < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  set filt := (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ Kf n) with hfilt
  set E : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (Real.exp (-(j : ℝ) ^ 2 * (rr n) ^ 2 / 12)) with hE
  show (∑ S ∈ filt, ∑' j : ℕ, if J₀ ≤ j then
        (33 : ℝ≥0∞) ^ S.card * E j
        + (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n)) * E j
            / dbarVal (av n) (rr n) (θ₀ n) else 0)
      ≤ ENNReal.ofReal (2 * ((Kf n : ℝ) + 1) * (33 * (n : ℝ)) ^ (Kf n)
          * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12))
        + ENNReal.ofReal (2 * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12
            + (rr n) ^ 2 - dlLBexp av rr θ₀ n))
  -- Tail bound on `∑_{j ≥ J₀} E_j`.
  have hT : (∑' j : ℕ, if J₀ ≤ j then E j else 0)
      ≤ 2 * ENNReal.ofReal (Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12)) :=
    tsum_ite_ge_exp_neg_sq_le J₀ (by norm_num) hthr
  -- Split the summand into Type I + Type II.
  have hsplit : (fun S : Finset (Fin n) => ∑' j : ℕ, if J₀ ≤ j then
        (33 : ℝ≥0∞) ^ S.card * E j
        + (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n)) * E j
            / dbarVal (av n) (rr n) (θ₀ n) else 0)
      = fun S => (∑' j : ℕ, if J₀ ≤ j then (33 : ℝ≥0∞) ^ S.card * E j else 0)
        + (∑' j : ℕ, if J₀ ≤ j then
            (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n)) * E j
              / dbarVal (av n) (rr n) (θ₀ n) else 0) := by
    funext S; rw [← ENNReal.tsum_add]; refine tsum_congr fun j => ?_
    by_cases hj : J₀ ≤ j <;> simp [hj]
  rw [Finset.sum_congr rfl (fun S _ => congrFun hsplit S), Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · -- TypeI ≤ ofReal RI
    have hpull : ∀ S : Finset (Fin n),
        (∑' j : ℕ, if J₀ ≤ j then (33 : ℝ≥0∞) ^ S.card * E j else 0)
          = (33 : ℝ≥0∞) ^ S.card * (∑' j : ℕ, if J₀ ≤ j then E j else 0) := by
      intro S; rw [← ENNReal.tsum_mul_left]; refine tsum_congr fun j => ?_
      by_cases hj : J₀ ≤ j <;> simp [hj]
    rw [Finset.sum_congr rfl (fun S _ => hpull S), ← Finset.sum_mul]
    have hcount : (∑ S ∈ filt, (33 : ℝ≥0∞) ^ S.card)
        ≤ ENNReal.ofReal (((Kf n + 1) * (33 * n) ^ Kf n : ℕ) : ℝ) := by
      have hnat := sum_pow_card_le_nat n (Kf n) hn1
      calc (∑ S ∈ filt, (33 : ℝ≥0∞) ^ S.card)
          = (((∑ S ∈ filt, 33 ^ S.card : ℕ)) : ℝ≥0∞) := by rw [hfilt]; push_cast; rfl
        _ ≤ (((Kf n + 1) * (33 * n) ^ Kf n : ℕ) : ℝ≥0∞) := by exact_mod_cast hnat
        _ = ENNReal.ofReal (((Kf n + 1) * (33 * n) ^ Kf n : ℕ) : ℝ) := (ENNReal.ofReal_natCast _).symm
    calc (∑ S ∈ filt, (33 : ℝ≥0∞) ^ S.card) * (∑' j : ℕ, if J₀ ≤ j then E j else 0)
        ≤ ENNReal.ofReal (((Kf n + 1) * (33 * n) ^ Kf n : ℕ) : ℝ)
            * (2 * ENNReal.ofReal (Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12))) :=
          mul_le_mul' hcount hT
      _ = ENNReal.ofReal (2 * ((Kf n : ℝ) + 1) * (33 * (n : ℝ)) ^ (Kf n)
            * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12)) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; push_cast; ring
  · -- TypeII ≤ ofReal RII
    -- `∑_S Π(shell) ≤ 1` and the box-route denominator lower bound.
    have hζ0 : 0 ≤ dlZeta av rr n := by
      rw [dlZeta]
      have hlog : 0 ≤ Real.log (1 / dlBoxS rr n) :=
        Real.log_nonneg (by rw [le_div_iff₀ hδboxpos]; linarith [hδboxlt1])
      positivity
    have hζbound : dlMarginal (av n)
        {x : ℝ | min (rr n / Real.sqrt (Fintype.card (Fin n) : ℝ)) (1 / 2) < |x|}
          ≤ ENNReal.ofReal (dlZeta av rr n) := by
      rw [Fintype.card_fin, dlZeta]
      exact dlMarginal_abs_gt_le' havp hav1 hδboxpos hδboxlt1
    have hballge : ENNReal.ofReal (Real.exp (dlLBexp av rr θ₀ n))
        ≤ dlPrior (av n) (Fin n) (Metric.closedBall (θ₀ n) (rr n)) := by
      have h := dlPrior_closedBall_ge (a := av n) (r := rr n) (ζ := dlZeta av rr n)
        havp hav1 hrrp (θ₀ n) hζbound hζ2 hζ0
      rw [Fintype.card_fin] at h
      rw [dlLBexp]; exact h
    have hdbar_ge : ENNReal.ofReal (Real.exp (dlLBexp av rr θ₀ n - (rr n) ^ 2))
        ≤ dbarVal (av n) (rr n) (θ₀ n) := by
      rw [dbarVal]
      calc ENNReal.ofReal (Real.exp (dlLBexp av rr θ₀ n - (rr n) ^ 2))
          = ENNReal.ofReal (Real.exp (-(rr n) ^ 2)) * ENNReal.ofReal (Real.exp (dlLBexp av rr θ₀ n)) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
        _ ≤ ENNReal.ofReal (Real.exp (-(rr n) ^ 2)) * dlPrior (av n) (Fin n)
              (Metric.closedBall (θ₀ n) (rr n)) := mul_le_mul_right hballge _
    have hdbar_inv : (dbarVal (av n) (rr n) (θ₀ n))⁻¹
        ≤ ENNReal.ofReal (Real.exp ((rr n) ^ 2 - dlLBexp av rr θ₀ n)) := by
      refine le_trans (ENNReal.inv_le_inv.mpr hdbar_ge) (le_of_eq ?_)
      rw [← ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]; congr 1
      rw [← Real.exp_neg]; congr 1; ring
    -- Swap `∑_S` and `∑'_j`, bound `∑_S` by `1`, pull out `E_j / dbar`.
    rw [← Summable.tsum_finsetSum (fun S _ => ENNReal.summable)]
    have hstepj : ∀ j : ℕ,
        (∑ S ∈ filt, if J₀ ≤ j then
          (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n)) * E j
            / dbarVal (av n) (rr n) (θ₀ n) else 0)
        ≤ (if J₀ ≤ j then E j / dbarVal (av n) (rr n) (θ₀ n) else 0) := by
      intro j
      by_cases hj : J₀ ≤ j
      · simp only [hj, if_true]
        calc (∑ S ∈ filt, (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n)) * E j
              / dbarVal (av n) (rr n) (θ₀ n))
            = (∑ S ∈ filt, (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n)))
                * (E j / dbarVal (av n) (rr n) (θ₀ n)) := by
              rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun S _ => (mul_div_assoc _ _ _)
          _ ≤ 1 * (E j / dbarVal (av n) (rr n) (θ₀ n)) :=
              mul_le_mul_left (sum_dlPrior_dlShell_le_one _ _ _ _ _ _) _
          _ = E j / dbarVal (av n) (rr n) (θ₀ n) := one_mul _
      · simp only [hj, if_false, Finset.sum_const_zero, le_refl]
    calc (∑' j : ℕ, ∑ S ∈ filt, if J₀ ≤ j then
            (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rr n) (rr n / n)) * E j
              / dbarVal (av n) (rr n) (θ₀ n) else 0)
        ≤ ∑' j : ℕ, (if J₀ ≤ j then E j / dbarVal (av n) (rr n) (θ₀ n) else 0) :=
          ENNReal.tsum_le_tsum hstepj
      _ = (∑' j : ℕ, if J₀ ≤ j then E j else 0) * (dbarVal (av n) (rr n) (θ₀ n))⁻¹ := by
          rw [← ENNReal.tsum_mul_right]; refine tsum_congr fun j => ?_
          by_cases hj : J₀ ≤ j <;> simp [hj, div_eq_mul_inv]
      _ ≤ (2 * ENNReal.ofReal (Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12)))
            * ENNReal.ofReal (Real.exp ((rr n) ^ 2 - dlLBexp av rr θ₀ n)) :=
          mul_le_mul' hT hdbar_inv
      _ = ENNReal.ofReal (2 * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12
            + (rr n) ^ 2 - dlLBexp av rr θ₀ n)) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, mul_assoc,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 2; ring

/-- `n^{−p} → 0` along `ℕ` for `p > 0` (rpow, cast). -/
private lemma tendsto_natRpow_neg' {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-p)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop

/-- `log n · n^{−p} → 0` along `ℕ` for `p > 0` (polynomial beats logarithm). -/
private lemma tendsto_log_mul_natRpow_neg' {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
  have hlit := (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero
  have hcast := hlit.comp tendsto_natCast_atTop_atTop
  refine hcast.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  simp only [Function.comp_apply]
  rw [Real.rpow_neg hn0.le, div_eq_mul_inv]

/-- **Poly-beats-log envelope.** For `p > 0`, `(C + D·log n)·n^{−p} → 0`. -/
private lemma tendsto_affineLog_mul_natRpow_neg' {p : ℝ} (hp : 0 < p) (C D : ℝ) :
    Tendsto (fun n : ℕ => (C + D * Real.log n) * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
    simpa using (tendsto_natRpow_neg' hp).const_mul C
  have h2 : Tendsto (fun n : ℕ => D * (Real.log n * (n : ℝ) ^ (-p))) atTop (𝓝 0) := by
    simpa using (tendsto_log_mul_natRpow_neg' hp).const_mul D
  have h3 := h1.add h2
  simp only [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

set_option maxHeartbeats 1600000 in
/-- **Shell double-series limit (generic scale, D14).** The engine's term-(iii) shell double series
at radius `r = √(qₙ log n)`, support-count threshold `⌊A·qₙ⌋₊`, and ANY scale sequence `av` in the
window `0 < av ≤ 1/2 ∧ n·av ≤ 1` with a polynomial floor `av ≥ n^{−p}` — covering BOTH regimes
(`aₙ = n^{−(1+β)}` with `p = 1+β`, and `aₙ = 1/n` with `p = 1`) — tends to `0` for a suitable fixed
radial floor `J₀ ≥ 2`. This is BPPD §6's term-iii asymptotic at the paper's radius `rₙ² = qₙ log n`
(p. 15), proved via `dl_shellSum_reduction`: Type-I net-count tail + Type-II via shell-disjointness
and the box-route ball lower bound (coarser than the paper's per-piece Lemma 6.1, same rate). -/
private lemma dl_shellSum_tendsto_zero_generic {q : ℕ → ℕ} (hq1 : ∀ n, 1 ≤ q n)
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖ ^ 2 ≤ (q n : ℝ) * (Real.log n) ^ 4)
    (av : ℕ → ℝ)
    -- LEAN-ONLY: scale window covering both regimes (n·av ≤ 1 controls the C3 tail 2nζ); engine-internal.
    (hav : ∀ᶠ (n : ℕ) in atTop, 0 < av n ∧ av n ≤ 1 / 2 ∧ (n : ℝ) * av n ≤ 1)
    -- LEAN-ONLY: polynomial floor giving log(1/av) ≤ p·log n; p = 1+β resp. 1; engine-internal.
    (hav2 : ∃ p : ℝ, 0 < p ∧ ∀ᶠ (n : ℕ) in atTop, (n : ℝ) ^ (-p) ≤ av n)
    (A : ℝ) (hA : 0 < A) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧
      Tendsto (fun n =>
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter
            (fun S => S.card ≤ ⌊A * q n⌋₊),
          ∑' j : ℕ, (if J₀ ≤ j then
            (33 : ℝ≥0∞) ^ S.card
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * (Real.sqrt (q n * Real.log n)) ^ 2 / 12))
            + (dlPrior (av n) (Fin n))
                (dlShell (θ₀ n) S j (Real.sqrt (q n * Real.log n)) (Real.sqrt (q n * Real.log n) / n))
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * (Real.sqrt (q n * Real.log n)) ^ 2 / 12))
              / dbarVal (av n) (Real.sqrt (q n * Real.log n)) (θ₀ n)
            else 0))
        atTop (𝓝 0) := by
  classical
  obtain ⟨p, hp, hfloor⟩ := hav2
  -- Regime abbreviations for `dl_shellSum_reduction`.
  set rr : ℕ → ℝ := fun n => Real.sqrt ((q n : ℝ) * Real.log n) with hrr
  set Kf : ℕ → ℕ := fun n => ⌊A * (q n : ℝ)⌋₊ with hKf
  -- The Type-II bound constant and the (generous) radial floor.
  set C' : ℝ := (3 + Real.log 32 + 1 / 2 + p) + 7 + 18 * Real.exp 1 with hC'
  set Cbig : ℝ := A + C' + 2 with hCbig
  have hexp1 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hlog32 : (0 : ℝ) ≤ Real.log 32 := Real.log_nonneg (by norm_num)
  have hC'pos : 0 ≤ C' := by rw [hC']; positivity
  have hCbig_pos : 0 ≤ Cbig := by rw [hCbig]; positivity
  set J₀ : ℕ := ⌈Real.sqrt (12 * Cbig)⌉₊ + 2 with hJ₀def
  have hJ2 : 2 ≤ J₀ := by rw [hJ₀def]; omega
  have hJ₀sq : 12 * Cbig ≤ (J₀ : ℝ) ^ 2 := by
    have h1 : Real.sqrt (12 * Cbig) ≤ (⌈Real.sqrt (12 * Cbig)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.sqrt (12 * Cbig)⌉₊ : ℝ) ≤ (J₀ : ℝ) := by
      rw [hJ₀def]; push_cast; linarith
    have h3 : Real.sqrt (12 * Cbig) ≤ (J₀ : ℝ) := le_trans h1 h2
    have h4 : 0 ≤ Real.sqrt (12 * Cbig) := Real.sqrt_nonneg _
    calc 12 * Cbig = (Real.sqrt (12 * Cbig)) ^ 2 := by
            rw [Real.sq_sqrt (by positivity)]
      _ ≤ (J₀ : ℝ) ^ 2 := by nlinarith
  -- Key numerical facts about `J₀`.
  have hJ₀A : 12 * A < (J₀ : ℝ) ^ 2 := by
    have : 12 * A < 12 * Cbig := by rw [hCbig]; nlinarith
    linarith
  have hJ₀C : 12 * (1 + C') < (J₀ : ℝ) ^ 2 := by
    have : 12 * (1 + C') < 12 * Cbig := by rw [hCbig]; nlinarith
    linarith
  -- ===== base eventual facts =====
  have hlogtend : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hq1n : ∀ n, (1 : ℝ) ≤ (q n : ℝ) := fun n => by exact_mod_cast hq1 n
  have hlog1 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n := by
    filter_upwards [eventually_ge_atTop 3] with n hn3
    have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    have := Real.exp_one_lt_d9
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) (by linarith)
  have hn1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn; exact_mod_cast hn
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log n := hlog1.mono fun n h => by linarith
  have hKf_le : ∀ n, (Kf n : ℝ) ≤ A * (q n : ℝ) := by
    intro n; rw [hKf]; exact Nat.floor_le (by positivity)
  have hrrsq : ∀ᶠ n : ℕ in atTop, (rr n) ^ 2 = (q n : ℝ) * Real.log n := by
    filter_upwards [hlog0] with n hl
    rw [hrr]; exact Real.sq_sqrt (mul_nonneg (by linarith [hq1n n]) hl)
  have hrr_pos : ∀ᶠ n : ℕ in atTop, 0 < rr n := by
    filter_upwards [hlog1] with n hl
    rw [hrr]; exact Real.sqrt_pos.mpr (by nlinarith [hq1n n])
  have hrrsq_top : Tendsto (fun n => (rr n) ^ 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hlogtend
    filter_upwards [hrrsq, hlog0] with n he hl
    rw [he]; nlinarith [hq1n n]
  -- box lower/log bounds (mirror `hsv_ge`/`hlogsv_le`)
  have hbox_le : ∀ n, dlBoxS rr n ≤ 1 / 2 := fun n => by rw [dlBoxS]; exact min_le_right _ _
  have hbox_ge : ∀ᶠ n : ℕ in atTop, 1 / Real.sqrt n ≤ dlBoxS rr n := by
    filter_upwards [eventually_ge_atTop 4, hlog1] with n hn4 hl
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0 : ℝ) < n := by linarith
    have hrr1 : (1 : ℝ) ≤ rr n := by
      rw [hrr, show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by nlinarith [hq1n n])
    have hsqn2 : (2 : ℝ) ≤ Real.sqrt n := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn4)
    have hsqnpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    rw [dlBoxS]
    apply le_min
    · gcongr
    · exact one_div_le_one_div_of_le (by norm_num) hsqn2
  have hlogbox : ∀ᶠ n : ℕ in atTop, Real.log (1 / dlBoxS rr n) ≤ (1 / 2) * Real.log n := by
    filter_upwards [hbox_ge, eventually_ge_atTop 4] with n hge hn4
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0 : ℝ) < n := by linarith
    have hboxpos : 0 < dlBoxS rr n := lt_of_lt_of_le (by positivity) hge
    have h1le : 1 / dlBoxS rr n ≤ Real.sqrt n := by
      have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / Real.sqrt n) hge
      rwa [one_div_one_div] at h
    calc Real.log (1 / dlBoxS rr n) ≤ Real.log (Real.sqrt n) :=
            Real.log_le_log (by positivity) h1le
      _ = (1 / 2) * Real.log n := by rw [Real.log_sqrt hnpos.le]; ring
  refine ⟨J₀, hJ2, ?_⟩
  refine dl_shellSum_reduction (av := av) (rr := rr) (Kf := Kf) (θ₀ := θ₀) J₀ hJ2 ?_ ?_ ?_
  · -- hstruct
    have hZtend : Tendsto (fun n : ℕ => Real.exp 1 * (8 + Real.log n) * (n : ℝ) ^ (-1 : ℝ))
        atTop (𝓝 0) := by
      have h := tendsto_affineLog_mul_natRpow_neg' (p := 1) (by norm_num)
        (8 * Real.exp 1) (Real.exp 1)
      refine h.congr fun n => ?_; ring
    have hZsmall : ∀ᶠ n : ℕ in atTop,
        Real.exp 1 * (8 + Real.log n) * (n : ℝ) ^ (-1 : ℝ) < 1 / 2 :=
      hZtend.eventually (Iio_mem_nhds (by norm_num))
    filter_upwards [hav, hrr_pos, hlog1, hlogbox, hZsmall,
        eventually_ge_atTop 1, hrrsq_top.eventually_ge_atTop 12]
      with n hav' hrrp hl hlbox hzsm hnnat hrr2ge
    obtain ⟨havpos, havhalf, hnav⟩ := hav'
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnnat
    have hnpos : (0 : ℝ) < n := by linarith
    refine ⟨hnnat, havpos, by linarith, hrrp, ?_,
      div_pos hrrp (Real.sqrt_pos.mpr hnpos), ?_⟩
    · -- 1 ≤ (2J₀+1)(rr)²/12
      have hJ5 : (5 : ℝ) ≤ 2 * (J₀ : ℝ) + 1 := by
        have : (2 : ℝ) ≤ (J₀ : ℝ) := by exact_mod_cast hJ2
        linarith
      nlinarith [hrr2ge, hJ5]
    · -- dlZeta ≤ 1/2
      rw [dlZeta]
      have hav_le_inv : av n ≤ (n : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one, inv_eq_one_div, le_div_iff₀ hnpos]
        linarith [hnav, mul_comm (av n) (n : ℝ)]
      have h8 : (0 : ℝ) ≤ 8 + Real.log n := by linarith
      calc Real.exp 1 * av n * (8 + 2 * Real.log (1 / dlBoxS rr n))
          ≤ Real.exp 1 * av n * (8 + Real.log n) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [hlbox]
        _ = Real.exp 1 * (8 + Real.log n) * av n := by ring
        _ ≤ Real.exp 1 * (8 + Real.log n) * (n : ℝ) ^ (-1 : ℝ) :=
            mul_le_mul_of_nonneg_left hav_le_inv (by positivity)
        _ ≤ 1 / 2 := le_of_lt hzsm
  · -- hRI : 2(Kf+1)(33n)^{Kf} exp(-J₀²rr²/12) → 0
    have hcI : 0 < ((J₀ : ℝ) ^ 2 / 12 - A) / 2 := by
      have : A < (J₀ : ℝ) ^ 2 / 12 := by linarith [hJ₀A]
      linarith
    have hthr_I : ∀ᶠ n : ℕ in atTop,
        (2 * A + 1) + A * Real.log 33 ≤ ((J₀ : ℝ) ^ 2 / 12 - A) / 2 * Real.log n :=
      (hlogtend.const_mul_atTop hcI).eventually_ge_atTop _
    refine tendsto_of_le_exp_neg (rr := rr) (K := (A - (J₀ : ℝ) ^ 2 / 12) / 2)
      (by linarith [hJ₀A] : (A - (J₀ : ℝ) ^ 2 / 12) / 2 < 0) hrrsq_top
      (Eventually.of_forall fun n => by positivity) ?_
    filter_upwards [hrrsq, hlog0, hn1, hthr_I] with n he hl hnR hthr
    have hnpos : (0 : ℝ) < n := by linarith
    -- prefactor bounds
    have hb1 : (2 : ℝ) * ((Kf n : ℝ) + 1) ≤ Real.exp ((2 * A + 1) * (q n : ℝ)) := by
      have h1 : (2 : ℝ) * ((Kf n : ℝ) + 1) ≤ Real.exp (2 * (Kf n : ℝ) + 1) := by
        have := Real.add_one_le_exp (2 * (Kf n : ℝ) + 1); linarith
      have h2 : 2 * (Kf n : ℝ) + 1 ≤ (2 * A + 1) * (q n : ℝ) := by
        nlinarith [hKf_le n, hq1n n]
      exact h1.trans (Real.exp_le_exp.mpr h2)
    have hlog33n_nn : (0 : ℝ) ≤ Real.log 33 + Real.log n := by
      have : (0 : ℝ) ≤ Real.log 33 := Real.log_nonneg (by norm_num); linarith
    have hb2 : (33 * (n : ℝ)) ^ (Kf n) ≤ Real.exp (A * (q n : ℝ) * (Real.log 33 + Real.log n)) := by
      have hpow : (33 * (n : ℝ)) ^ (Kf n) = Real.exp ((Kf n : ℝ) * Real.log (33 * n)) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
      rw [hpow, Real.log_mul (by norm_num) (by positivity)]
      apply Real.exp_le_exp.mpr
      calc (Kf n : ℝ) * (Real.log 33 + Real.log n)
          ≤ (A * (q n : ℝ)) * (Real.log 33 + Real.log n) :=
            mul_le_mul_of_nonneg_right (hKf_le n) hlog33n_nn
        _ = A * (q n : ℝ) * (Real.log 33 + Real.log n) := by ring
    have hqpos : (0 : ℝ) ≤ (q n : ℝ) := by linarith [hq1n n]
    calc 2 * ((Kf n : ℝ) + 1) * (33 * (n : ℝ)) ^ (Kf n)
            * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12)
        = (2 * ((Kf n : ℝ) + 1)) * ((33 * (n : ℝ)) ^ (Kf n))
            * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12) := by ring
      _ ≤ Real.exp ((2 * A + 1) * (q n : ℝ)) * Real.exp (A * (q n : ℝ) * (Real.log 33 + Real.log n))
            * Real.exp (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12) := by gcongr
      _ = Real.exp ((2 * A + 1) * (q n : ℝ) + A * (q n : ℝ) * (Real.log 33 + Real.log n)
            + (-(J₀ : ℝ) ^ 2 * (rr n) ^ 2 / 12)) := by rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((A - (J₀ : ℝ) ^ 2 / 12) / 2 * (rr n) ^ 2) := by
          apply Real.exp_le_exp.mpr
          rw [he]
          have hslack : 0 ≤ ((J₀ : ℝ) ^ 2 / 12 - A) / 2 * Real.log n
              - ((2 * A + 1) + A * Real.log 33) := by linarith [hthr]
          nlinarith [mul_nonneg hqpos hslack]
  · -- hRII : 2 exp(-J₀²rr²/12 + rr² - dlLBexp) → 0
    -- CRUX: -dlLBexp ≤ C'·q log n eventually.
    have hneg_dlLB : ∀ᶠ n : ℕ in atTop,
        -dlLBexp av rr θ₀ n ≤ C' * ((q n : ℝ) * Real.log n) := by
      filter_upwards [hnorm, hav, hfloor, hlog1, hlogbox, hbox_ge, eventually_ge_atTop 1]
        with n hnorm_n hav_n hfloor_n hlog1_n hlogbox_n hbox_ge_n hnnat
      obtain ⟨havpos, havhalf, hnav⟩ := hav_n
      have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnnat
      have hnpos : (0 : ℝ) < n := by linarith
      have hlogn_nn : (0 : ℝ) ≤ Real.log n := by linarith [hlog1_n]
      have hqpos : (0 : ℝ) ≤ (q n : ℝ) := by linarith [hq1n n]
      have hqp : (0 : ℝ) < (q n : ℝ) := by linarith [hq1n n]
      have hbpos : 0 < dlBoxS rr n := lt_of_lt_of_le (by positivity) hbox_ge_n
      have hble : dlBoxS rr n ≤ 1 / 2 := hbox_le n
      have hlog32 : (0 : ℝ) ≤ Real.log 32 := Real.log_nonneg (by norm_num)
      rw [dlLBexp]
      set supp := Finset.univ.filter (fun j => θ₀ n j ≠ 0) with hsupp
      have hcard : (supp.card : ℝ) ≤ (q n : ℝ) := by
        have h := hθ₀ n; rw [← hsupp] at h; exact_mod_cast h
      -- log(1/av) ≤ p log n
      have hlogav : -Real.log (av n) ≤ p * Real.log n := by
        have hle : Real.log ((n : ℝ) ^ (-p)) ≤ Real.log (av n) :=
          Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hfloor_n
        rw [Real.log_rpow hnpos] at hle; linarith
      -- -log box ≤ ½ log n
      have hlogbox_neg : -Real.log (dlBoxS rr n) ≤ (1 / 2) * Real.log n := by
        rw [← Real.log_inv, ← one_div]; exact hlogbox_n
      -- log expansion of the density-floor term
      have hLexp : Real.log (2 * dlBoxS rr n * (av n / 64))
          = -Real.log 32 + Real.log (dlBoxS rr n) + Real.log (av n) := by
        rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hbpos))
              (div_ne_zero (ne_of_gt havpos) (by norm_num)),
            Real.log_mul (by norm_num) (ne_of_gt hbpos),
            Real.log_div (ne_of_gt havpos) (by norm_num)]
        have h64 : Real.log 64 = Real.log 32 + Real.log 2 := by
          rw [show (64 : ℝ) = 32 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        rw [h64]; ring
      -- P1: density-floor term
      have h3mL_bd : 3 - Real.log (2 * dlBoxS rr n * (av n / 64))
          ≤ (3 + Real.log 32) + (1 / 2) * Real.log n + p * Real.log n := by
        rw [hLexp]; linarith [hlogbox_neg, hlogav]
      have h3mL_nn : 0 ≤ 3 - Real.log (2 * dlBoxS rr n * (av n / 64)) := by
        rw [hLexp]
        have hb0 : Real.log (dlBoxS rr n) ≤ 0 := Real.log_nonpos hbpos.le (by linarith [hble])
        have ha0 : Real.log (av n) ≤ 0 := Real.log_nonpos havpos.le (by linarith [havhalf])
        linarith [hlog32]
      have hP1 : -((supp.card : ℝ) * (Real.log (2 * dlBoxS rr n * (av n / 64)) - 3))
          ≤ (3 + Real.log 32 + 1 / 2 + p) * ((q n : ℝ) * Real.log n) := by
        have e1 : -((supp.card : ℝ) * (Real.log (2 * dlBoxS rr n * (av n / 64)) - 3))
            = (supp.card : ℝ) * (3 - Real.log (2 * dlBoxS rr n * (av n / 64))) := by ring
        rw [e1]
        calc (supp.card : ℝ) * (3 - Real.log (2 * dlBoxS rr n * (av n / 64)))
            ≤ (q n : ℝ) * ((3 + Real.log 32) + (1 / 2) * Real.log n + p * Real.log n) :=
              mul_le_mul hcard h3mL_bd h3mL_nn hqpos
          _ ≤ (3 + Real.log 32 + 1 / 2 + p) * ((q n : ℝ) * Real.log n) := by
              nlinarith [mul_nonneg (mul_nonneg
                (by linarith [hlog32] : (0 : ℝ) ≤ 3 + Real.log 32) hqpos)
                (by linarith [hlog1_n] : (0 : ℝ) ≤ Real.log n - 1)]
      -- P2: the ∑√(|θ₀ⱼ|+box) term
      have hsqrt_split : ∀ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n)
          ≤ Real.sqrt |θ₀ n j| + Real.sqrt (dlBoxS rr n) := by
        intro j _
        rw [← Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sq_sqrt (abs_nonneg (θ₀ n j)), Real.sq_sqrt hbpos.le,
          Real.sqrt_nonneg (|θ₀ n j|), Real.sqrt_nonneg (dlBoxS rr n),
          mul_nonneg (Real.sqrt_nonneg (|θ₀ n j|)) (Real.sqrt_nonneg (dlBoxS rr n))]
      have hsum_split : (∑ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n))
          ≤ (∑ j ∈ supp, Real.sqrt |θ₀ n j|) + (supp.card : ℝ) * Real.sqrt (dlBoxS rr n) := by
        calc ∑ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n)
            ≤ ∑ j ∈ supp, (Real.sqrt |θ₀ n j| + Real.sqrt (dlBoxS rr n)) :=
              Finset.sum_le_sum hsqrt_split
          _ = (∑ j ∈ supp, Real.sqrt |θ₀ n j|) + (supp.card : ℝ) * Real.sqrt (dlBoxS rr n) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hB : (∑ j ∈ supp, Real.sqrt |θ₀ n j|) ≤ (q n : ℝ) * Real.log n := by
        have hss := sum_sqrt_abs_finset_le supp (θ₀ n)
        have hc34 : (supp.card : ℝ) ^ (3 / 4 : ℝ) ≤ (q n : ℝ) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hcard (by norm_num)
        have hnorm12 : ‖θ₀ n‖ ^ (1 / 2 : ℝ) ≤ (q n : ℝ) ^ (1 / 4 : ℝ) * Real.log n := by
          have h1 : ‖θ₀ n‖ ^ (1 / 2 : ℝ) = (‖θ₀ n‖ ^ 2) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast (‖θ₀ n‖) 2, ← Real.rpow_mul (norm_nonneg _)]; norm_num
          rw [h1]
          calc (‖θ₀ n‖ ^ 2) ^ (1 / 4 : ℝ)
              ≤ ((q n : ℝ) * (Real.log n) ^ 4) ^ (1 / 4 : ℝ) :=
                Real.rpow_le_rpow (by positivity) hnorm_n (by norm_num)
            _ = (q n : ℝ) ^ (1 / 4 : ℝ) * Real.log n := by
                rw [Real.mul_rpow hqpos (by positivity)]
                congr 1
                rw [← Real.rpow_natCast (Real.log n) 4, ← Real.rpow_mul hlogn_nn]
                norm_num
        calc (∑ j ∈ supp, Real.sqrt |θ₀ n j|)
            ≤ (supp.card : ℝ) ^ (3 / 4 : ℝ) * ‖θ₀ n‖ ^ (1 / 2 : ℝ) := hss
          _ ≤ (q n : ℝ) ^ (3 / 4 : ℝ) * ((q n : ℝ) ^ (1 / 4 : ℝ) * Real.log n) :=
              mul_le_mul hc34 hnorm12 (by positivity) (by positivity)
          _ = (q n : ℝ) * Real.log n := by
              rw [← mul_assoc, ← Real.rpow_add hqp, show (3 / 4 + 1 / 4 : ℝ) = 1 by norm_num,
                Real.rpow_one]
      have hCterm : (supp.card : ℝ) * Real.sqrt (dlBoxS rr n) ≤ (q n : ℝ) * Real.log n := by
        have hsb : Real.sqrt (dlBoxS rr n) ≤ 1 := by
          rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
          exact Real.sqrt_le_sqrt (by linarith [hble])
        calc (supp.card : ℝ) * Real.sqrt (dlBoxS rr n) ≤ (q n : ℝ) * 1 :=
              mul_le_mul hcard hsb (Real.sqrt_nonneg _) hqpos
          _ = (q n : ℝ) := by ring
          _ ≤ (q n : ℝ) * Real.log n := by nlinarith [hq1n n, hlog1_n]
      have hP2 : 7 / 2 * (∑ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n))
          ≤ 7 * ((q n : ℝ) * Real.log n) := by
        have hs2 : (∑ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n))
            ≤ 2 * ((q n : ℝ) * Real.log n) := by
          calc (∑ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n))
              ≤ (∑ j ∈ supp, Real.sqrt |θ₀ n j|)
                  + (supp.card : ℝ) * Real.sqrt (dlBoxS rr n) := hsum_split
            _ ≤ (q n : ℝ) * Real.log n + (q n : ℝ) * Real.log n := add_le_add hB hCterm
            _ = 2 * ((q n : ℝ) * Real.log n) := by ring
        linarith [hs2]
      -- P3: the 2·dlZeta·n term
      have hP3 : 2 * dlZeta av rr n * (n : ℝ)
          ≤ 18 * Real.exp 1 * ((q n : ℝ) * Real.log n) := by
        rw [dlZeta]
        have key1 : (8 + 2 * Real.log (1 / dlBoxS rr n)) ≤ 9 * Real.log n := by
          linarith [hlogbox_n, hlog1_n]
        have hlogbox_pos : 0 ≤ Real.log (1 / dlBoxS rr n) :=
          Real.log_nonneg (by rw [le_div_iff₀ hbpos]; linarith [hble])
        have hpp : ((n : ℝ) * av n) * (8 + 2 * Real.log (1 / dlBoxS rr n))
            ≤ 1 * (9 * Real.log n) :=
          mul_le_mul hnav key1 (by linarith [hlogbox_pos]) (by norm_num)
        calc 2 * (Real.exp 1 * av n * (8 + 2 * Real.log (1 / dlBoxS rr n))) * (n : ℝ)
            = (2 * Real.exp 1) * (((n : ℝ) * av n) * (8 + 2 * Real.log (1 / dlBoxS rr n))) := by ring
          _ ≤ (2 * Real.exp 1) * (1 * (9 * Real.log n)) :=
              mul_le_mul_of_nonneg_left hpp (by positivity)
          _ = 18 * Real.exp 1 * Real.log n := by ring
          _ ≤ 18 * Real.exp 1 * ((q n : ℝ) * Real.log n) := by
              nlinarith [mul_nonneg (mul_nonneg
                (by positivity : (0 : ℝ) ≤ 18 * Real.exp 1) hlogn_nn)
                (by linarith [hq1n n] : (0 : ℝ) ≤ (q n : ℝ) - 1)]
      -- assemble -dlLBexp = P1 + P2 + P3
      calc -((supp.card : ℝ) * (Real.log (2 * dlBoxS rr n * (av n / 64)) - 3)
              - 7 / 2 * (∑ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n))
              - 2 * dlZeta av rr n * (n : ℝ))
          = -((supp.card : ℝ) * (Real.log (2 * dlBoxS rr n * (av n / 64)) - 3))
              + 7 / 2 * (∑ j ∈ supp, Real.sqrt (|θ₀ n j| + dlBoxS rr n))
              + 2 * dlZeta av rr n * (n : ℝ) := by ring
        _ ≤ (3 + Real.log 32 + 1 / 2 + p) * ((q n : ℝ) * Real.log n)
              + 7 * ((q n : ℝ) * Real.log n) + 18 * Real.exp 1 * ((q n : ℝ) * Real.log n) :=
            add_le_add (add_le_add hP1 hP2) hP3
        _ = C' * ((q n : ℝ) * Real.log n) := by rw [hC']; ring
    -- squeeze to 0.
    have hK : (1 + C' - (J₀ : ℝ) ^ 2 / 12) < 0 := by linarith [hJ₀C]
    have hg : Tendsto (fun n => 2 * Real.exp ((1 + C' - (J₀ : ℝ) ^ 2 / 12) * (rr n) ^ 2))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => (1 + C' - (J₀ : ℝ) ^ 2 / 12) * (rr n) ^ 2) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg hK hrrsq_top
      have h1 := Real.tendsto_exp_atBot.comp h0
      simpa using h1.const_mul 2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
      (Eventually.of_forall fun n => by positivity) ?_
    filter_upwards [hneg_dlLB, hrrsq] with n hdlb he
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have h1 : -dlLBexp av rr θ₀ n ≤ C' * (rr n) ^ 2 := by rw [he]; exact hdlb
    nlinarith [h1]

/-- **Shell double-series limit (β-regime).** The engine's term (iii) shell double series, evaluated
at the β-regime instantiation (`a = n^{−(1+β)}`, `r = √(qₙ log n)`, `δ = r/n`), tends to `0` for a
suitable fixed radial floor `J₀ ≥ 2`. The β-instance of `dl_shellSum_tendsto_zero_generic`
(scale window: `n·n^{−(1+β)} = n^{−β} ≤ 1`, polynomial floor `p = 1+β`); statement kept verbatim so
the proven `dl_theorem31` wiring is untouched. -/
private lemma dl_shellSum_tendsto_zero_beta {β : ℝ} (hβ : 0 < β) {q : ℕ → ℕ} (hq1 : ∀ n, 1 ≤ q n)
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖ ^ 2 ≤ (q n : ℝ) * (Real.log n) ^ 4) :
    ∃ J₀ : ℕ, 2 ≤ J₀ ∧
      Tendsto (fun n =>
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter
            (fun S => S.card ≤ ⌊(3 + 2 / β) * q n⌋₊),
          ∑' j : ℕ, (if J₀ ≤ j then
            (33 : ℝ≥0∞) ^ S.card
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * (Real.sqrt (q n * Real.log n)) ^ 2 / 12))
            + (dlPrior ((n : ℝ) ^ (-(1 + β))) (Fin n))
                (dlShell (θ₀ n) S j (Real.sqrt (q n * Real.log n)) (Real.sqrt (q n * Real.log n) / n))
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * (Real.sqrt (q n * Real.log n)) ^ 2 / 12))
              / dbarVal ((n : ℝ) ^ (-(1 + β))) (Real.sqrt (q n * Real.log n)) (θ₀ n)
            else 0))
        atTop (𝓝 0) := by
  -- β-instance of the generic limit at `av n = n^{−(1+β)}`, `A = 3 + 2/β`, floor `p = 1+β`.
  have hav0 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 + β))) atTop (𝓝 0) :=
    tendsto_natRpow_neg' (by linarith)
  have hhalf : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(1 + β)) < 1 / 2 :=
    hav0.eventually (Iio_mem_nhds (by norm_num))
  have hav : ∀ᶠ n : ℕ in atTop,
      0 < (n : ℝ) ^ (-(1 + β)) ∧ (n : ℝ) ^ (-(1 + β)) ≤ 1 / 2
        ∧ (n : ℝ) * (n : ℝ) ^ (-(1 + β)) ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1, hhalf] with n hn hh
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    refine ⟨Real.rpow_pos_of_pos hnpos _, le_of_lt hh, ?_⟩
    have heq : (n : ℝ) * (n : ℝ) ^ (-(1 + β)) = (n : ℝ) ^ (-β) := by
      nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hnpos]; congr 1; ring
    rw [heq]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
  exact dl_shellSum_tendsto_zero_generic hq1 hqn hθ₀ hnorm (fun n => (n : ℝ) ^ (-(1 + β)))
    hav ⟨1 + β, by linarith, Eventually.of_forall fun n => le_refl _⟩ (3 + 2 / β)
    (by positivity)

/-- **Prior charges the contraction ball.** For `0 < a` and `0 < r`, the DL prior gives positive mass
to `closedBall θ₀ r`: a coordinatewise box `{θ | ∀ j, |θ j − θ₀ j| ≤ s}` with `s = r/√(card ι)` sits
inside the ball, and factorizes into a product of positive one-dimensional interval masses. -/
private lemma dlPrior_closedBall_pos {ι : Type*} [Fintype ι] {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (θ₀ : EuclideanSpace ℝ ι) : 0 < dlPrior a ι (Metric.closedBall θ₀ r) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Empty index: the space is a single point and the ball is everything.
    have : Metric.closedBall θ₀ r = Set.univ := by
      ext θ; simp only [Metric.mem_closedBall, Set.mem_univ, iff_true]
      rw [Subsingleton.elim θ θ₀, dist_self]; exact hr.le
    rw [this, measure_univ]; exact one_pos
  set m : ℝ := (Fintype.card ι : ℝ) with hm_def
  have hmpos : 0 < m := by
    rw [hm_def]; exact_mod_cast Fintype.card_pos
  set s : ℝ := r / Real.sqrt m with hs_def
  have hspos : 0 < s := by rw [hs_def]; positivity
  -- The box sits inside `closedBall θ₀ r`.
  have hbox_sub : {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} ⊆ Metric.closedBall θ₀ r := by
    intro θ hθ
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsum : ∑ j, (θ j - θ₀ j) ^ 2 ≤ m * s ^ 2 := by
      calc ∑ j, (θ j - θ₀ j) ^ 2 ≤ ∑ _j : ι, s ^ 2 :=
            Finset.sum_le_sum fun j _ => by nlinarith [hθ j, abs_nonneg (θ j - θ₀ j), sq_abs (θ j - θ₀ j)]
        _ = m * s ^ 2 := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm_def]
    have hnormsq : ‖θ - θ₀‖ ^ 2 = ∑ j, (θ j - θ₀ j) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show (θ - θ₀) j = θ j - θ₀ j from rfl]
    have hsm0 : Real.sqrt m ≠ 0 := Real.sqrt_ne_zero'.mpr hmpos
    have hsr : Real.sqrt m * s = r := by
      rw [hs_def]; field_simp
    calc ‖θ - θ₀‖ = Real.sqrt (‖θ - θ₀‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (∑ j, (θ j - θ₀ j) ^ 2) := by rw [hnormsq]
      _ ≤ Real.sqrt (m * s ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt m * s := by rw [Real.sqrt_mul hmpos.le, Real.sqrt_sq hspos.le]
      _ = r := hsr
  -- The box mass factorizes into positive one-dimensional masses.
  have hbox_meas : MeasurableSet {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} := by
    rw [Set.setOf_forall]
    refine MeasurableSet.iInter fun j => measurableSet_le ?_ measurable_const
    exact (((measurable_pi_apply j).comp
      (MeasurableEquiv.toLp 2 (ι → ℝ)).symm.measurable).sub measurable_const).abs
  have hbox_eq : dlPrior a ι {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s}
      = ∏ j, dlMarginal a {x : ℝ | |x - θ₀ j| ≤ s} := by
    have hpre : (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹'
        {θ | ∀ j, |θ j - θ₀ j| ≤ s}
        = Set.univ.pi (fun j => {y : ℝ | |y - θ₀ j| ≤ s}) := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi, PiLp.toLp_apply]
    rw [dlPrior, Measure.map_apply measurable_toLp hbox_meas, hpre, Measure.pi_pi]
  have hbox_pos : 0 < dlPrior a ι {θ : EuclideanSpace ℝ ι | ∀ j, |θ j - θ₀ j| ≤ s} := by
    rw [hbox_eq, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro j _
    exact (dlMarginal_abs_sub_le_pos ha (θ₀ j) s hspos).ne'
  exact lt_of_lt_of_le hbox_pos (measure_mono hbox_sub)


set_option maxHeartbeats 3200000 in
/-- **BPPD Theorem 3.1 (posterior contraction).** In the normal-means model with the Dirichlet–Laplace
prior at scale `aₙ = n^{−(1+β)}`, under the growth condition `‖θ₀‖² ≤ qₙ log⁴n`, there is a constant
`M > 0` such that the posterior mass of `{ θ : ‖θ − θ₀‖ > M√(qₙ log n) }` tends to `0` in `E_{θ₀}`.

**Deviation D1 (rate).** The stated rate is `√(qₙ log n)`, which is what the paper's proof (`rₙ² = qₙ
log n`, p. 15) yields; the paper's headline `sₙ = √(qₙ log(n/qₙ))` is recovered under `qₙ ≤ n^{1−c}` in
`dl_theorem31_paper_rate`. -/
theorem dl_theorem31 {β : ℝ}
    -- USER-INPUT: β > 0 (DL scale exponent aₙ = n^{−(1+β)}); BPPD Thm 3.1.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (nonempty approximate support; D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n) (sub-linear sparsity); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ is qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n (signal-size growth condition, BPPD (11)); BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  classical
  -- Radial floor `J₀` and the term-(iii) shell double series limit.
  obtain ⟨J₀, hJ2, hshell⟩ := dl_shellSum_tendsto_zero_beta hβ hq1 hqn hθ₀ hnorm
  -- Regime instantiation (mirrors `dl_theorem34_beta`); the threshold `δ = rₙ/n`.
  set A : ℝ := 3 + 2 / β with hA_def
  set S₀ : (n : ℕ) → Finset (Fin n) := fun n => Finset.univ.filter fun j => θ₀ n j ≠ 0 with hS₀
  set av : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 + β)) with hav
  set cv : ℕ → ℝ := fun n => (n : ℝ) ^ (β / 2) with hcv
  set rv : ℕ → ℝ := fun n => Real.sqrt ((q n : ℝ) * Real.log n) with hrv
  set δv : ℕ → ℝ := fun n => rv n / n with hδv
  set mv : ℕ → ℝ := fun n =>
    (letI := Classical.decEq (Fin n); (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ)) with hmv
  set zv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / δv n)) with hzv
  set sv : ℕ → ℝ := fun n => min (rv n / Real.sqrt (mv n)) (1 / 2) with hsv
  set wv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / sv n)) with hwv
  set kv : ℕ → ℕ := fun n => ⌊A * q n⌋₊ - (S₀ n).card with hkv
  set P : ℕ → ℝ := fun n => mv n * zv n * (cv n - 1) - (kv n : ℝ) * Real.log (cv n)
      + rv n ^ 2 + 2 * mv n * wv n with hP
  set M : ℝ := 2 * (J₀ : ℝ) with hM_def
  have hJ2R : (2 : ℝ) ≤ (J₀ : ℝ) := by exact_mod_cast hJ2
  have hMpos : 0 < M := by rw [hM_def]; linarith
  refine ⟨M, hMpos, ?_⟩
  -- ===== shared envelope facts (mirror `dl_theorem34_beta`) =====
  have hav_pos : ∀ᶠ n in atTop, 0 < av n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hmv_le : ∀ n, mv n ≤ (n : ℝ) := by
    intro n
    letI := Classical.decEq (Fin n)
    have h : Fintype.card {i : Fin n // i ∉ S₀ n} ≤ n :=
      (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
    show (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ) ≤ (n : ℝ)
    exact_mod_cast h
  have hqlt : ∀ᶠ n in atTop, (q n : ℝ) < n := by
    filter_upwards [hqn.eventually (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)),
      eventually_gt_atTop 0] with n hlt hn0
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    exact (div_lt_one hnpos).mp hlt
  have hmvpos : ∀ᶠ n in atTop, 0 < mv n := by
    filter_upwards [hqlt] with n hql
    letI := Classical.decEq (Fin n)
    have hcard : (S₀ n).card < n := lt_of_le_of_lt (hθ₀ n) (by exact_mod_cast hql)
    have hex : ∃ j : Fin n, j ∉ S₀ n := by
      by_contra hcon
      push_neg at hcon
      have huniv : S₀ n = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard; omega
    obtain ⟨j, hj⟩ := hex
    haveI : Nonempty {i : Fin n // i ∉ S₀ n} := ⟨j, hj⟩
    show (0 : ℝ) < (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ)
    exact_mod_cast Fintype.card_pos
  -- `δ = rₙ/n` lies in the window `[n^{−2}, 1/2]` eventually.
  have hδwin : ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^(-2 : ℝ) ≤ δv n ∧ δv n ≤ 1/2 := by
    filter_upwards [eventually_ge_atTop 3,
      hqn.eventually (Iio_mem_nhds (show (0:ℝ) < 1/8 by norm_num))] with n hn3 hqs
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn3)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hq1n : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
    have hlogn1 : (1:ℝ) ≤ Real.log n := by
      have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn3
      have := Real.exp_one_lt_d9
      have hle : Real.exp 1 ≤ n := by linarith
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) hle
    have hrv_pos : 0 < rv n := by
      rw [hrv]; exact Real.sqrt_pos.mpr (by nlinarith)
    have hrv_ge1 : (1:ℝ) ≤ rv n := by
      rw [hrv, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    refine ⟨?_, ?_⟩
    · -- n^{−2} ≤ rₙ/n
      have hmono : (n:ℝ)^(-2:ℝ) ≤ (n:ℝ)^(-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
      have hinv : (n:ℝ)^(-1:ℝ) = 1 / n := by
        rw [Real.rpow_neg_one]; exact (one_div _).symm
      calc (n:ℝ)^(-2:ℝ) ≤ (n:ℝ)^(-1:ℝ) := hmono
        _ = 1 / n := hinv
        _ ≤ rv n / n := by gcongr
    · -- rₙ/n ≤ 1/2
      have hlogle : Real.log n ≤ (n : ℝ) := by
        have := Real.log_le_sub_one_of_pos hnpos; linarith
      have hqle : (q n : ℝ) ≤ n / 8 := by
        have : (q n : ℝ) / n < 1/8 := hqs
        rw [div_lt_iff₀ hnpos] at this; linarith
      have h4 : 4 * rv n ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [hrv, Real.sq_sqrt (by nlinarith)]
        nlinarith [hqle, hlogle, hlogn0, hq1n, hnpos]
      have h2rv : 2 * rv n ≤ (n : ℝ) := by
        have hsq : Real.sqrt (4 * rv n ^ 2) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h4
        rwa [show 4 * rv n ^ 2 = (2 * rv n) ^ 2 by ring, Real.sqrt_sq (by positivity),
          Real.sqrt_sq hnpos.le] at hsq
      rw [hδv, div_le_iff₀ hnpos]; linarith
  have hzv_le : ∀ᶠ n in atTop, zv n ≤ Real.exp 1 * av n * (8 + 4 * Real.log n) := by
    filter_upwards [hδwin, eventually_ge_atTop 1, hav_pos] with n hδn hn1 hapos
    obtain ⟨hδlb, hδub⟩ := hδn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
    have h1 : Real.log (1 / δv n) ≤ 2 * Real.log n := by
      rw [one_div, Real.log_inv]
      have hle : Real.log ((n:ℝ)^(-2:ℝ)) ≤ Real.log (δv n) :=
        Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hδlb
      rw [Real.log_rpow hnpos] at hle; linarith
    rw [hzv]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsv_ge : ∀ᶠ (n : ℕ) in atTop, 1 / Real.sqrt n ≤ sv n := by
    filter_upwards [eventually_ge_atTop 4, hmvpos] with n hn4 hmvp
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn1 : (1:ℝ) ≤ Real.log n := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      exact Real.log_le_log (Real.exp_pos 1) (by
        have : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
        have h3 : (4:ℝ) ≤ n := by exact_mod_cast hn4
        linarith)
    have hrv1 : (1:ℝ) ≤ rv n := by
      rw [hrv, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt
      have hq1n : (1:ℝ) ≤ (q n:ℝ) := by exact_mod_cast hq1 n
      nlinarith [hlogn1, hq1n]
    have hsqn2 : (2:ℝ) ≤ Real.sqrt n := by
      rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt; exact_mod_cast hn4
    have hmvsqle : Real.sqrt (mv n) ≤ Real.sqrt n := Real.sqrt_le_sqrt (hmv_le n)
    have hmvsqpos : 0 < Real.sqrt (mv n) := Real.sqrt_pos.mpr hmvp
    rw [hsv]
    apply le_min
    · calc 1 / Real.sqrt n ≤ 1 / Real.sqrt (mv n) :=
              one_div_le_one_div_of_le hmvsqpos hmvsqle
        _ ≤ rv n / Real.sqrt (mv n) := by gcongr
    · exact one_div_le_one_div_of_le (by norm_num) hsqn2
  have hlogsv_le : ∀ᶠ (n : ℕ) in atTop, Real.log (1 / sv n) ≤ (1/2) * Real.log n := by
    filter_upwards [hsv_ge, eventually_ge_atTop 4] with n hsvge hn4
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
    have h1svle : 1 / sv n ≤ Real.sqrt n := by
      have h := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 1 / Real.sqrt n) hsvge
      rwa [one_div_one_div] at h
    calc Real.log (1 / sv n) ≤ Real.log (Real.sqrt n) :=
            Real.log_le_log (by positivity) h1svle
      _ = (1/2) * Real.log n := by rw [Real.log_sqrt hnpos.le]; ring
  have hwv_le : ∀ᶠ n in atTop, wv n ≤ Real.exp 1 * av n * (8 + Real.log n) := by
    filter_upwards [hlogsv_le, hav_pos] with n hlog hapos
    rw [hwv]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hWtend : Tendsto (fun n => Real.exp 1 * av n * (8 + Real.log n)) atTop (𝓝 0) := by
    have h := tendsto_affineLog_mul_natRpow_neg' (p := 1 + β) (by linarith)
      (8 * Real.exp 1) (Real.exp 1)
    refine h.congr fun n => ?_
    rw [hav]; ring
  have hw2 : ∀ᶠ n in atTop, wv n ≤ 1 / 2 := by
    have hev : ∀ᶠ n in atTop, Real.exp 1 * av n * (8 + Real.log n) ∈ Set.Iio (1/2 : ℝ) :=
      hWtend.eventually (Iio_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
    filter_upwards [hwv_le, hev] with n h1 h2
    have h2' : Real.exp 1 * av n * (8 + Real.log n) < 1 / 2 := h2
    linarith
  have hcv_gt1 : ∀ᶠ n in atTop, 1 < cv n := by
    filter_upwards [eventually_ge_atTop 2] with n hn2
    have hnpos : (0:ℝ) < n := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    rw [hcv]
    exact (Real.one_lt_rpow_iff_of_pos hnpos).mpr
      (Or.inl ⟨by exact_mod_cast hn2, by positivity⟩)
  -- ===== the three vanishing terms of the engine RHS =====
  have hlogtend : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hS1 : Tendsto (fun n => mv n * zv n * (cv n - 1)) atTop (𝓝 0) := by
    have hU1 : Tendsto (fun n : ℕ =>
        Real.exp 1 * (8 + 4 * Real.log n) * (n : ℝ) ^ (-(β / 2))) atTop (𝓝 0) := by
      have h := tendsto_affineLog_mul_natRpow_neg' (p := β / 2) (by linarith)
        (8 * Real.exp 1) (4 * Real.exp 1)
      refine h.congr fun n => ?_; ring
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU1 ?_ ?_
    · filter_upwards [hδwin, eventually_ge_atTop 1, hav_pos, hcv_gt1] with n hδn hn1 hapos hcvn
      obtain ⟨hδlb, hδub⟩ := hδn
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
      have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
      have hlogd : 0 ≤ Real.log (1 / δv n) :=
        Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
      have hzvnn : 0 ≤ zv n := by
        rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
      exact mul_nonneg (mul_nonneg hmvnn hzvnn) (by linarith [hcvn])
    · filter_upwards [hzv_le, eventually_ge_atTop 1, hav_pos, hcv_gt1, hδwin] with
        n hzvle hn1 hapos hcvn hδn
      obtain ⟨hδlb, hδub⟩ := hδn
      have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
      have hn1R : (1:ℝ) ≤ n := by exact_mod_cast hn1
      have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
      have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
      have hlogd : 0 ≤ Real.log (1 / δv n) :=
        Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
      have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
      have hzvnn : 0 ≤ zv n := by
        rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      have henv_nn : 0 ≤ Real.exp 1 * av n * (8 + 4 * Real.log n) :=
        mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      have hcvnn : 0 ≤ cv n - 1 := by linarith [hcvn]
      have hcvpos : 0 ≤ cv n := by rw [hcv]; positivity
      have hrpow : (n : ℝ) * av n * cv n = (n : ℝ) ^ (-(β / 2)) := by
        rw [mul_assoc, hav, hcv, ← Real.rpow_add hnpos]
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnpos]; congr 1; ring
      calc mv n * zv n * (cv n - 1)
          ≤ (n : ℝ) * (Real.exp 1 * av n * (8 + 4 * Real.log n)) * cv n := by
            apply mul_le_mul _ (by linarith [hcvn]) hcvnn
              (mul_nonneg (by positivity) henv_nn)
            exact mul_le_mul (hmv_le n) hzvle hzvnn (by positivity)
        _ = Real.exp 1 * (8 + 4 * Real.log n) * ((n : ℝ) * av n * cv n) := by ring
        _ = Real.exp 1 * (8 + 4 * Real.log n) * (n : ℝ) ^ (-(β / 2)) := by rw [hrpow]
  have hS2 : Tendsto (fun n => mv n * wv n) atTop (𝓝 0) := by
    have hU2 : Tendsto (fun n : ℕ =>
        Real.exp 1 * (8 + Real.log n) * (n : ℝ) ^ (-β)) atTop (𝓝 0) := by
      have h := tendsto_affineLog_mul_natRpow_neg' (p := β) hβ (8 * Real.exp 1) (Real.exp 1)
      refine h.congr fun n => ?_; ring
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU2 ?_ ?_
    · filter_upwards [hw2, eventually_ge_atTop 4, hsv_ge] with n hw2n hn4 hsvge
      have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
      have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
      have hwvnn : 0 ≤ wv n := by
        rw [hwv]
        have : 0 ≤ Real.log (1 / sv n) :=
          Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith [hsvge, show sv n ≤ 1 from le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by norm_num))])
        have hapos : 0 < av n := by
          rw [hav]; exact Real.rpow_pos_of_pos (by exact_mod_cast (le_trans (by norm_num) hn4)) _
        exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      exact mul_nonneg hmvnn hwvnn
    · filter_upwards [hwv_le, eventually_ge_atTop 4, hav_pos, hsv_ge] with
        n hwvle hn4 hapos hsvge
      have hn1R : (1:ℝ) ≤ n := by
        have : (4:ℝ) ≤ n := by exact_mod_cast hn4
        linarith
      have hnpos : (0:ℝ) < n := by linarith
      have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
      have hwvnn : 0 ≤ wv n := by
        rw [hwv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le)
          (by
            have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
            have : 0 ≤ Real.log (1 / sv n) :=
              Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith [hsvge, show sv n ≤ 1 from le_of_lt (lt_of_le_of_lt (min_le_right _ _) (by norm_num))])
            linarith)
      have hrpow : (n : ℝ) * av n = (n : ℝ) ^ (-β) := by
        rw [hav]
        nth_rewrite 1 [← Real.rpow_one (n : ℝ)]
        rw [← Real.rpow_add hnpos]; congr 1; ring
      calc mv n * wv n ≤ (n : ℝ) * (Real.exp 1 * av n * (8 + Real.log n)) := by
            exact mul_le_mul (hmv_le n) hwvle hwvnn (by positivity)
        _ = Real.exp 1 * (8 + Real.log n) * ((n : ℝ) * av n) := by ring
        _ = Real.exp 1 * (8 + Real.log n) * (n : ℝ) ^ (-β) := by rw [hrpow]
  have hbig : Tendsto (fun n => (kv n : ℝ) * Real.log (cv n) - rv n ^ 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => (β / 2) * Real.log n) ?_
      (hlogtend.const_mul_atTop (by positivity))
    filter_upwards [eventually_ge_atTop 4, hqlt] with n hn4 hql
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hq1n : (1:ℝ) ≤ q n := by exact_mod_cast hq1 n
    have hlogcv : Real.log (cv n) = (β / 2) * Real.log n := by rw [hcv, Real.log_rpow hnpos]
    have hrv2 : rv n ^ 2 = (q n : ℝ) * Real.log n := by
      rw [hrv]; exact Real.sq_sqrt (mul_nonneg (by positivity) hlogn)
    have hcard_le : (S₀ n).card ≤ ⌊A * (q n : ℝ)⌋₊ := by
      apply Nat.le_floor
      have h1 : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
      have h2 : (1:ℝ) ≤ A := by rw [hA_def]; nlinarith [show (0:ℝ) < 2 / β by positivity]
      nlinarith
    have hklb : (A - 1) * (q n : ℝ) - 1 ≤ (kv n : ℝ) := by
      rw [hkv, Nat.cast_sub hcard_le]
      have hfloor : A * (q n : ℝ) - 1 < ⌊A * (q n : ℝ)⌋₊ := by
        have := Nat.lt_floor_add_one (A * (q n : ℝ)); linarith
      have hcardle : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
      push_cast; nlinarith
    have hAm1 : A - 1 = 2 + 2 / β := by rw [hA_def]; ring
    have hkβ : 2 * (q n : ℝ) * β + 2 * (q n) - β ≤ (kv n : ℝ) * β := by
      have h := mul_le_mul_of_nonneg_right hklb hβ.le
      rw [hAm1] at h
      have hLHS : ((2 + 2 / β) * (q n : ℝ) - 1) * β = 2 * (q n) * β + 2 * (q n) - β := by
        field_simp
      rwa [hLHS] at h
    have hbr : (0:ℝ) ≤ (kv n : ℝ) * β - 2 * (q n) - β := by
      nlinarith [hkβ, mul_nonneg hβ.le (sub_nonneg.mpr hq1n)]
    rw [hlogcv, hrv2]
    nlinarith [mul_nonneg hlogn hbr, hlogn]
  have hε2 : Tendsto (fun n => rv n ^ 2 / 8) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => Real.log n / 8) ?_
      ((hlogtend).atTop_div_const (by norm_num))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hrv2 : rv n ^ 2 = (q n : ℝ) * Real.log n := by
      rw [hrv]; exact Real.sq_sqrt (mul_nonneg (by positivity) (Real.log_nonneg hn1))
    have hq1n : (1:ℝ) ≤ q n := by exact_mod_cast hq1 n
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [hrv2]; nlinarith
  have hf1 : Tendsto (fun n => ENNReal.ofReal (Real.exp (P n))) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun n => -(P n)) atTop atTop := by
      have hsmall : Tendsto (fun n => -(mv n * zv n * (cv n - 1)) - 2 * (mv n * wv n))
          atTop (𝓝 0) := by
        have h2S2 : Tendsto (fun n => 2 * (mv n * wv n)) atTop (𝓝 0) := by
          simpa using hS2.const_mul 2
        have hh := (hS1.neg).add (h2S2.neg)
        simpa [sub_eq_add_neg] using hh
      have hh := hbig.atTop_add hsmall
      refine hh.congr fun n => ?_
      rw [hP]; ring
    have hh := tendsto_ofReal_exp_neg hdiv
    refine hh.congr fun n => ?_; rw [neg_neg]
  have hf2 : Tendsto (fun n => ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8))) atTop (𝓝 0) := by
    have hh := tendsto_ofReal_exp_neg hε2
    refine hh.congr fun n => ?_; rw [neg_div]
  -- The term-(iii) shell double series, restated over the regime abbreviations (defeq to `hshell`).
  have hshellR : Tendsto (fun n =>
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ ⌊A * (q n : ℝ)⌋₊),
        ∑' j : ℕ, (if J₀ ≤ j then
          (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12))
          + (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rv n) (δv n))
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12)) / dbarVal (av n) (rv n) (θ₀ n)
          else 0)) atTop (𝓝 0) := hshell
  -- Assemble: the full engine RHS tends to `0`.
  have hRHS : Tendsto (fun n =>
      ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8))
      + (ENNReal.ofReal (Real.exp (P n)) + ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8)))
      + ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun S => S.card ≤ ⌊A * (q n : ℝ)⌋₊),
          ∑' j : ℕ, (if J₀ ≤ j then
            (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12))
            + (dlPrior (av n) (Fin n)) (dlShell (θ₀ n) S j (rv n) (δv n))
                * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * rv n ^ 2 / 12)) / dbarVal (av n) (rv n) (θ₀ n)
            else 0)) atTop (𝓝 0) := by
    have h := ((hf2.add (hf1.add hf2)).add hshellR)
    simpa only [add_zero, zero_add] using h
  -- Squeeze the posterior mass between `0` and the engine RHS.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS
    (Filter.Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hδwin, eventually_ge_atTop 4, hsv_ge, hw2, hcv_gt1, hav_pos] with
    n hδn hn4 hsvge hw2n hcvn hapos
  obtain ⟨hδlb, hδub⟩ := hδn
  have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
  have hnpos : (0:ℝ) < n := by linarith
  have hn2 : (1:ℝ) < n := by
    have : (4:ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hn2N : 2 ≤ n := by
    have : (4:ℝ) ≤ n := by exact_mod_cast hn4
    exact_mod_cast (by linarith : (2:ℝ) ≤ n)
  have ha_le1 : av n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
  have ha_le2 : av n ≤ 1/2 := by
    show (n:ℝ)^(-(1+β)) ≤ 1/2
    rw [Real.rpow_neg hnpos.le, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num]
    apply inv_anti₀ (by norm_num)
    calc (2:ℝ) ≤ n := by exact_mod_cast hn2N
      _ = (n:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (n:ℝ)^(1+β) := Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
  have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
  have hδlt1 : δv n ≤ 1 := le_trans hδub (by norm_num)
  have hlogn_pos : 0 < Real.log n := Real.log_pos hn2
  have hr_pos : 0 < rv n := by
    rw [hrv]; exact Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast hq1 n) hlogn_pos)
  have hsupp : ∀ i ∉ S₀ n, θ₀ n i = 0 := by
    intro i hi
    simp only [hS₀, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi
  -- `hδnet`: √(card)·δ ≤ r.
  have hδnet : Real.sqrt (Fintype.card (Fin n) : ℝ) * δv n ≤ rv n := by
    rw [Fintype.card_fin, hδv]
    have hsqn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n:ℝ)*(n:ℝ)) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = n := by rw [Real.sqrt_mul_self hnpos.le]
    calc Real.sqrt (n : ℝ) * (rv n / n) ≤ (n : ℝ) * (rv n / n) := by
          apply mul_le_mul_of_nonneg_right hsqn (by positivity)
      _ = rv n := by field_simp
  -- C3 tail discharges.
  have hδlt1' : δv n < 1 := lt_of_le_of_lt hδub (by norm_num)
  have hz : (dlMarginal (av n) {x : ℝ | δv n < |x|}).toReal ≤ zv n := by
    have hm := dlMarginal_abs_gt_le' hapos ha_le1 hδpos hδlt1'
    have hlogd : 0 ≤ Real.log (1 / δv n) :=
      Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
    have hznn : (0:ℝ) ≤ zv n := by
      rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
    calc (dlMarginal (av n) {x : ℝ | δv n < |x|}).toReal
        ≤ (ENNReal.ofReal (zv n)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
      _ = zv n := ENNReal.toReal_ofReal hznn
  have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
  have hsvlt1 : sv n < 1 := by
    rw [hsv]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hlogs : 0 ≤ Real.log (1 / sv n) :=
    Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith [hsvlt1])
  have hw : (dlMarginal (av n) {x : ℝ | sv n < |x|}).toReal ≤ wv n := by
    have hm := dlMarginal_abs_gt_le' hapos ha_le1 hsvpos hsvlt1
    have hwnn : (0:ℝ) ≤ wv n := by
      rw [hwv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
    calc (dlMarginal (av n) {x : ℝ | sv n < |x|}).toReal
        ≤ (ENNReal.ofReal (wv n)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
      _ = wv n := ENNReal.toReal_ofReal hwnn
  -- `hk`: the Chernoff cut inclusion.
  have hAqn : (0:ℝ) ≤ A * q n := by rw [hA_def]; positivity
  have hcard_le : (S₀ n).card ≤ ⌊A * (q n : ℝ)⌋₊ := by
    apply Nat.le_floor
    have h1 : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
    have h2 : (1:ℝ) ≤ A := by rw [hA_def]; have : 0 < 2 / β := by positivity
                              linarith
    have h3 : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
    nlinarith
  have hk : ((S₀ n).card : ℝ) + (kv n : ℝ) ≤ (⌊A * (q n : ℝ)⌋₊ : ℝ) := by
    rw [hkv, Nat.cast_sub hcard_le]; push_cast; linarith
  have hbBpos : 0 < (dlPrior (av n) (Fin n)) (Metric.closedBall (θ₀ n) (rv n)) :=
    dlPrior_closedBall_pos hapos hr_pos (θ₀ n)
  have hJ₀ : (J₀ : ℝ) ≤ M / 2 := by rw [hM_def]; linarith
  -- Apply the engine (its conclusion is exactly the RHS of the squeeze).
  exact dl_contraction_engine hapos ha_le2 hδpos hδlt1 hδnet hr_pos (θ₀ n) (S₀ n) hsupp hbBpos
    M hMpos (⌊A * (q n : ℝ)⌋₊) J₀ hJ2 hJ₀ (kv n) hk (zv n) hz (wv n) hw hw2n (cv n) hcvn

/-- **BPPD Theorem 3.1, ball / `𝓝 1` form** (BPPD eq. (12)). Equivalent restatement of `dl_theorem31`:
the posterior mass of the contraction ball `{ θ : ‖θ − θ₀‖ ≤ M√(qₙ log n) }` tends to `1` in
`E_{θ₀}`. -/
theorem dl_theorem31_ball {β : ℝ}
    -- USER-INPUT: β > 0; BPPD Thm 3.1.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | ‖θ - θ₀ n‖ ≤ M * Real.sqrt (q n * Real.log n)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 1) := by
  obtain ⟨M, hMpos, hlim⟩ := dl_theorem31 hβ hq1 hqn hθ₀ hnorm
  refine ⟨M, hMpos, ?_⟩
  -- Ball mass = 1 − complement mass, pointwise in `y`, then integrate.
  have hcongr : (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | ‖θ - θ₀ n‖ ≤ M * Real.sqrt (q n * Real.log n)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n)))
      = (fun n => 1 - ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) := by
    funext n
    set r : ℝ := M * Real.sqrt (q n * Real.log n) with hr
    set κ := (gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n)) with hκ
    set μ := gaussShiftKernel (Fin n) (θ₀ n) with hμ
    have hcompl_meas : MeasurableSet {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} :=
      measurableSet_lt measurable_const ((continuous_id.sub continuous_const).norm.measurable)
    have hg_meas : Measurable (fun y => κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}) :=
      Kernel.measurable_coe κ hcompl_meas
    have hball_eq : {θ : EuclideanSpace ℝ (Fin n) | ‖θ - θ₀ n‖ ≤ r}
        = {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}ᶜ := by
      ext θ; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have hpt : ∀ y, κ y {θ : EuclideanSpace ℝ (Fin n) | ‖θ - θ₀ n‖ ≤ r}
        = 1 - κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} := by
      intro y
      rw [hball_eq, measure_compl hcompl_meas (measure_ne_top _ _), measure_univ]
    have hgle : (fun y => κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}) ≤ᵐ[μ]
        (fun _ => (1 : ℝ≥0∞)) := ae_of_all _ fun y => prob_le_one
    have hgfin : ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [lintegral_one]; exact measure_ne_top μ _)
        (lintegral_mono_ae hgle)
    calc ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | ‖θ - θ₀ n‖ ≤ r} ∂μ
        = ∫⁻ y, ((1 : ℝ≥0∞) - κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖}) ∂μ :=
          lintegral_congr fun y => hpt y
      _ = (∫⁻ _, (1 : ℝ≥0∞) ∂μ)
            - ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} ∂μ :=
          lintegral_sub hg_meas hgfin hgle
      _ = 1 - ∫⁻ y, κ y {θ : EuclideanSpace ℝ (Fin n) | r < ‖θ - θ₀ n‖} ∂μ := by
          rw [lintegral_one, measure_univ]
  rw [hcongr]
  have := ((ENNReal.continuous_sub_left ENNReal.one_ne_top).continuousAt (x := 0)).tendsto.comp hlim
  simpa using! this

/-- **BPPD Theorem 3.1, paper rate** (D1 recovery). Under the polynomial-sparsity regime
`qₙ ≤ n^{1−c}` (so `log(n/qₙ) ≍ log n`), the posterior contracts at the paper's minimax rate
`sₙ = √(qₙ log(n/qₙ))`. -/
theorem dl_theorem31_paper_rate {β : ℝ}
    -- USER-INPUT: β > 0; BPPD Thm 3.1.
    (hβ : 0 < β) {c : ℝ}
    -- USER-INPUT: 0 < c < 1 (polynomial-sparsity exponent for qₙ ≤ n^{1−c}); BPPD Thm 3.1 / D1.
    (hc : 0 < c) (hc1 : c < 1) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4)
    -- USER-INPUT: qₙ ≤ n^{1−c} (polynomial sparsity, D1 — makes sₙ ≍ √(qₙ log n)); BPPD Thm 3.1.
    (hqpoly : ∀ᶠ n in Filter.atTop, (q n : ℝ) ≤ (n:ℝ)^(1-c)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log ((n:ℝ)/q n)) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  obtain ⟨M', hM'pos, hlim⟩ := dl_theorem31 hβ hq1 hqn hθ₀ hnorm
  have hsc : (0 : ℝ) < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨M' / Real.sqrt c, div_pos hM'pos hsc, ?_⟩
  -- Under `qₙ ≤ n^{1−c}`, the paper radius dominates the `√(qₙ log n)` radius, so its exceedance
  -- set is contained in the latter's and the posterior mass is monotone.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds (x := (0 : ℝ≥0∞))) hlim
    (Filter.Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hqpoly, eventually_ge_atTop 2] with n hqp hn2
  -- Radius domination `M' √(qₙ log n) ≤ (M'/√c) √(qₙ log(n/qₙ))`.
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn2
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hqpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hq1 n
  have hlogn : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  -- `n / qₙ ≥ n^c`.
  have hnq_ge : (n : ℝ) ^ c ≤ (n : ℝ) / q n := by
    rw [le_div_iff₀ hqpos]
    calc (n : ℝ) ^ c * q n ≤ (n : ℝ) ^ c * (n : ℝ) ^ (1 - c) :=
          mul_le_mul_of_nonneg_left hqp (by positivity)
      _ = (n : ℝ) := by rw [← Real.rpow_add hn0]; simp
  have hlogdom : c * Real.log n ≤ Real.log ((n : ℝ) / q n) := by
    calc c * Real.log n = Real.log ((n : ℝ) ^ c) := (Real.log_rpow hn0 c).symm
      _ ≤ Real.log ((n : ℝ) / q n) := Real.log_le_log (by positivity) hnq_ge
  -- Multiply by `qₙ ≥ 0` and take square roots.
  have hprod : c * ((q n : ℝ) * Real.log n) ≤ (q n : ℝ) * Real.log ((n : ℝ) / q n) := by
    have := mul_le_mul_of_nonneg_left hlogdom hqpos.le
    nlinarith [this]
  have hsqrt : Real.sqrt c * Real.sqrt ((q n : ℝ) * Real.log n)
      ≤ Real.sqrt ((q n : ℝ) * Real.log ((n : ℝ) / q n)) := by
    rw [← Real.sqrt_mul hc.le]
    exact Real.sqrt_le_sqrt hprod
  have hrad : M' * Real.sqrt ((q n : ℝ) * Real.log n)
      ≤ M' / Real.sqrt c * Real.sqrt ((q n : ℝ) * Real.log ((n : ℝ) / q n)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsc]
    calc M' * Real.sqrt ((q n : ℝ) * Real.log n) * Real.sqrt c
        = M' * (Real.sqrt c * Real.sqrt ((q n : ℝ) * Real.log n)) := by ring
      _ ≤ M' * Real.sqrt ((q n : ℝ) * Real.log ((n : ℝ) / q n)) :=
          mul_le_mul_of_nonneg_left hsqrt hM'pos.le
  -- Set inclusion + monotone posterior mass.
  refine lintegral_mono fun y => measure_mono fun θ hθ => ?_
  simp only [Set.mem_setOf_eq] at hθ ⊢
  exact lt_of_le_of_lt hrad hθ

/-- **BPPD Theorem 3.1, `1/n`-regime companion.** Same conclusion (rate `M√(qₙ log n)`) at scale
`aₙ = 1/n`, additionally requiring `qₙ ≥ C₀ log n` (the paper's "qₙ ≳ log n" clause, Thm 3.1 p. 7).
Proved by the paper's own composition (§6 p. 15, D13 resolution): the compressibility term is the
proven `dl_theorem34_recip` consumed as a black box (its own internal radius `r'² = qₙ`), while the
denominator event and shell series run at `r² = qₙ log n` through `dl_contraction_engine'`. -/
theorem dl_theorem31_recip {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.1.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.1.
    (hqn : Tendsto (fun n => (q n : ℝ)/n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.1.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    -- USER-INPUT: ‖θ₀‖² ≤ qₙ log⁴n; BPPD Thm 3.1.
    (hnorm : ∀ᶠ (n : ℕ) in atTop, ‖θ₀ n‖^2 ≤ (q n : ℝ) * (Real.log n)^4)
    -- USER-INPUT: qₙ ≥ C₀ log n (needed for the 1/n-regime denominator error, D2); BPPD Thm 3.1.
    (hqlog : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ (n : ℕ) in atTop, C₀ * Real.log n ≤ (q n : ℝ)) :
    ∃ M : ℝ, 0 < M ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)⁻¹) (Fin n))) y
          {θ | M * Real.sqrt (q n * Real.log n) < ‖θ - θ₀ n‖}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  -- COMPOSED ROUTE (BPPD §6 p. 15; resolves the former D13 two-scale obstruction — see header).
  -- The paper: "Since E_{θ₀}ℙ(|supp_{δₙ}(θ)| > Aqₙ | y) → 0 by Theorem 3.4, it is enough to work
  -- with E_{θ₀}ℙ(‖θ−θ₀‖ > 2Mrₙ, supp ∈ 𝒮ₙ | y)" — then rₙ² = qₙ log n for shells/denominator.
  -- Skeleton (mirror `dl_theorem31`'s proven envelope structure):
  --   1. rv n := √(q n * log n), δv n := rv n / n; hδwin : ∀ᶠ n^{−2} ≤ δv n ≤ 1/2 (as in dl_theorem31).
  --   2. obtain ⟨A', hA', h34⟩ := dl_theorem34_recip hq1 hqn hθ₀ hδwin hqlog  -- 3.4-term → 0.
  --   3. K n := ⌊(A' + 1) * q n⌋₊; (K n : ℝ) ≥ A'·q n (via q n ≥ 1), so
  --      {(K:ℝ) < supp} ⊆ {A'·q < supp} and the engine's abstract 3.4-term ≤ h34's quantity
  --      (lintegral_mono + measure_mono per y).
  --   4. obtain ⟨J₀, hJ2, hshell⟩ := dl_shellSum_tendsto_zero_generic hq1 hqn hθ₀ hnorm
  --        (fun n => (n:ℝ)⁻¹) hav ⟨1, one_pos, hav2⟩ (A' + 1) (by positivity)
  --      where hav : ∀ᶠ n, 0 < (n:ℝ)⁻¹ ∧ (n:ℝ)⁻¹ ≤ 1/2 ∧ n·(n:ℝ)⁻¹ ≤ 1 and hav2 : ∀ᶠ n, n^{-1} ≤ (n:ℝ)⁻¹.
  --   5. M := 2·(J₀:ℝ); squeeze `tendsto_of_tendsto_of_tendsto_of_le_of_le'` against
  --      `dl_contraction_engine'` at a = (n:ℝ)⁻¹, r = rv n, δ = δv n, K = K n, J₀
  --      (hBpos := dlPrior_closedBall_pos; hδnet via √n ≤ n; hJ₀ by M = 2J₀).
  --   6. RHS → 0: step-3 bound of the 3.4-term (h34) + ofReal(exp(−rv²/8)) → 0
  --      (`tendsto_ofReal_exp_neg`, rv² = q log n ≥ log n → ∞) + hshell; `Filter.Tendsto.add`.
  classical
  -- 1. Regime abbreviations (prior scale aₙ = 1/n; radius/threshold at rₙ² = qₙ log n).
  set rv : ℕ → ℝ := fun n => Real.sqrt ((q n : ℝ) * Real.log n) with hrv
  set δv : ℕ → ℝ := fun n => rv n / n with hδv
  -- The δ-window `[n^{−2}, 1/2]` (verbatim from `dl_theorem31`).
  have hδwin : ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^(-2 : ℝ) ≤ δv n ∧ δv n ≤ 1/2 := by
    filter_upwards [eventually_ge_atTop 3,
      hqn.eventually (Iio_mem_nhds (show (0:ℝ) < 1/8 by norm_num))] with n hn3 hqs
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn3)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
    have hq1n : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
    have hlogn1 : (1:ℝ) ≤ Real.log n := by
      have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn3
      have := Real.exp_one_lt_d9
      have hle : Real.exp 1 ≤ n := by linarith
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log n := Real.log_le_log (Real.exp_pos 1) hle
    have hrv_pos : 0 < rv n := by
      rw [hrv]; exact Real.sqrt_pos.mpr (by nlinarith)
    have hrv_ge1 : (1:ℝ) ≤ rv n := by
      rw [hrv, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      exact Real.sqrt_le_sqrt (by nlinarith)
    refine ⟨?_, ?_⟩
    · have hmono : (n:ℝ)^(-2:ℝ) ≤ (n:ℝ)^(-1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by norm_num)
      have hinv : (n:ℝ)^(-1:ℝ) = 1 / n := by
        rw [Real.rpow_neg_one]; exact (one_div _).symm
      calc (n:ℝ)^(-2:ℝ) ≤ (n:ℝ)^(-1:ℝ) := hmono
        _ = 1 / n := hinv
        _ ≤ rv n / n := by gcongr
    · have hlogle : Real.log n ≤ (n : ℝ) := by
        have := Real.log_le_sub_one_of_pos hnpos; linarith
      have hqle : (q n : ℝ) ≤ n / 8 := by
        have : (q n : ℝ) / n < 1/8 := hqs
        rw [div_lt_iff₀ hnpos] at this; linarith
      have h4 : 4 * rv n ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [hrv, Real.sq_sqrt (by nlinarith)]
        nlinarith [hqle, hlogle, hlogn0, hq1n, hnpos]
      have h2rv : 2 * rv n ≤ (n : ℝ) := by
        have hsq : Real.sqrt (4 * rv n ^ 2) ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h4
        rwa [show 4 * rv n ^ 2 = (2 * rv n) ^ 2 by ring, Real.sqrt_sq (by positivity),
          Real.sqrt_sq hnpos.le] at hsq
      rw [hδv, div_le_iff₀ hnpos]; linarith
  -- 2. Theorem 3.4 (1/n-regime): the support-count term → 0 at threshold `A'·qₙ`.
  obtain ⟨A', hA', h34⟩ := dl_theorem34_recip hq1 hqn hθ₀ hδwin hqlog
  -- 3. Chernoff threshold `K = ⌊(A'+1)qₙ⌋`; the engine's abstract 3.4-term is dominated by `h34`.
  set Kf : ℕ → ℕ := fun n => ⌊(A' + 1) * (q n : ℝ)⌋₊ with hKf
  have hA'q_le : ∀ n, A' * (q n : ℝ) ≤ (Kf n : ℝ) := by
    intro n
    have hq1n : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
    have hfl : (A' + 1) * (q n : ℝ) - 1 < (⌊(A' + 1) * (q n : ℝ)⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one ((A' + 1) * (q n : ℝ)); linarith
    have hle : A' * (q n : ℝ) ≤ (A' + 1) * (q n : ℝ) - 1 := by nlinarith
    simp only [hKf]; linarith
  have hterm34 : Tendsto (fun n => ∫⁻ y,
      ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)⁻¹) (Fin n))) y
        {θ | (Kf n : ℝ) < (dlSuppCount (δv n) θ : ℝ)}
      ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h34
      (Filter.Eventually.of_forall fun n => zero_le) (Filter.Eventually.of_forall fun n => ?_)
    refine lintegral_mono fun y => measure_mono fun θ hθ => ?_
    simp only [Set.mem_setOf_eq] at hθ ⊢
    exact lt_of_le_of_lt (hA'q_le n) hθ
  -- 4. Shell double series limit at the generic scale window `avₙ = 1/n`.
  have hav : ∀ᶠ (n : ℕ) in atTop, 0 < (n : ℝ)⁻¹ ∧ (n : ℝ)⁻¹ ≤ 1 / 2 ∧ (n : ℝ) * (n : ℝ)⁻¹ ≤ 1 := by
    filter_upwards [eventually_ge_atTop 2] with n hn2
    have hnpos : (0:ℝ) < n := by
      have : (2:ℝ) ≤ n := by exact_mod_cast hn2
      linarith
    refine ⟨inv_pos.mpr hnpos, ?_, le_of_eq (mul_inv_cancel₀ (ne_of_gt hnpos))⟩
    rw [show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hn2)
  have hav2 : ∃ p : ℝ, 0 < p ∧ ∀ᶠ (n : ℕ) in atTop, (n : ℝ) ^ (-p) ≤ (n : ℝ)⁻¹ := by
    refine ⟨1, one_pos, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnn : (0:ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
    have : (n:ℝ)^(-(1:ℝ)) = (n:ℝ)⁻¹ := by rw [Real.rpow_neg hnn, Real.rpow_one]
    exact le_of_eq this
  obtain ⟨J₀, hJ2, hshell⟩ := dl_shellSum_tendsto_zero_generic hq1 hqn hθ₀ hnorm
    (fun n => (n : ℝ)⁻¹) hav hav2 (A' + 1) (by linarith)
  -- 5. The geometric `exp(−rₙ²/8)` term vanishes (`rₙ² = qₙ log n ≥ log n → ∞`).
  have hlogtend : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hε2 : Tendsto (fun n => rv n ^ 2 / 8) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => Real.log n / 8) ?_
      ((hlogtend).atTop_div_const (by norm_num))
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hrv2 : rv n ^ 2 = (q n : ℝ) * Real.log n := by
      rw [hrv]; exact Real.sq_sqrt (mul_nonneg (by positivity) (Real.log_nonneg hn1))
    have hq1n : (1:ℝ) ≤ q n := by exact_mod_cast hq1 n
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    rw [hrv2]; nlinarith
  have hf2 : Tendsto (fun n => ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8))) atTop (𝓝 0) := by
    have hh := tendsto_ofReal_exp_neg hε2
    refine hh.congr fun n => ?_; rw [neg_div]
  -- 6. Assemble and squeeze the posterior mass between `0` and the engine RHS.
  set M : ℝ := 2 * (J₀ : ℝ) with hM_def
  have hJ2R : (2 : ℝ) ≤ (J₀ : ℝ) := by exact_mod_cast hJ2
  have hMpos : 0 < M := by rw [hM_def]; linarith
  refine ⟨M, hMpos, ?_⟩
  have hRHS := (hterm34.add hf2).add hshell
  simp only [add_zero] at hRHS
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hRHS
    (Filter.Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [hδwin, eventually_ge_atTop 4] with n hδn hn4
  obtain ⟨hδlb, hδub⟩ := hδn
  have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
  have hnpos : (0:ℝ) < n := by linarith
  have hn2 : (1:ℝ) < n := by
    have h4 : (4:ℝ) ≤ n := by exact_mod_cast hn4
    linarith
  have hlogn_pos : 0 < Real.log n := Real.log_pos hn2
  have hapos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hδpos : 0 < δv n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
  have hr_pos : 0 < rv n := by
    rw [hrv]; exact Real.sqrt_pos.mpr (mul_pos (by exact_mod_cast hq1 n) hlogn_pos)
  have hδnet : Real.sqrt (Fintype.card (Fin n) : ℝ) * δv n ≤ rv n := by
    rw [Fintype.card_fin, hδv]
    have hsqn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
      calc Real.sqrt (n : ℝ) ≤ Real.sqrt ((n:ℝ)*(n:ℝ)) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = n := by rw [Real.sqrt_mul_self hnpos.le]
    calc Real.sqrt (n : ℝ) * (rv n / n) ≤ (n : ℝ) * (rv n / n) := by
          apply mul_le_mul_of_nonneg_right hsqn (by positivity)
      _ = rv n := by field_simp
  have hBpos : 0 < (dlPrior ((n : ℝ)⁻¹) (Fin n)) (Metric.closedBall (θ₀ n) (rv n)) :=
    dlPrior_closedBall_pos hapos hr_pos (θ₀ n)
  have hJ₀ : (J₀ : ℝ) ≤ M / 2 := by rw [hM_def]; linarith
  -- Apply the composed engine (its conclusion is exactly the RHS of the squeeze).
  exact dl_contraction_engine' hapos hδpos hδnet hr_pos (θ₀ n) hBpos
    M hMpos (Kf n) J₀ hJ2 hJ₀
end StatLean.Bayesian
