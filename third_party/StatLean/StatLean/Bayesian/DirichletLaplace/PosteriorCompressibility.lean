module
public import StatLean.Bayesian.DirichletLaplace.CompressEngine
public import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
public import StatLean.Bayesian.DirichletLaplace.NormalMeansModel
public import StatLean.Bayesian.DirichletLaplace.DensityBounds
public import StatLean.Bayesian.ForMathlib.ExpOfRealCalc
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Dirichlet–Laplace posterior compressibility — BPPD Theorem 3.4 (C15)

Assembly of BPPD **Theorem 3.4**: in the normal-means model `y = θ + ε`, `ε ~ N(0, Iₙ)`, under the
Dirichlet–Laplace prior with scale `aₙ`, the posterior probability that more than `A·qₙ` coordinates
exceed `δₙ` in absolute value tends to `0` in `E_{θ₀}`.

Objects:
* `dl_compress_reduction` — the single passage from the abstract posterior `κ†Π` to the ratio
  functions (`NormalMeansModel` bridge) together with the count split `|supp_δ(θ)| ≤ q + |supp_δ|_{Sᶜ}`
  and the tensorization (BPPD eq. (26), `CoordinateSplit`): the general-`θ₀` compress event is bounded
  by the truth-`0` compress event on the `S₀ᶜ`-submodel.
* (A fixed-`n` `dl_theorem34_engine` intermediate was **removed** — its stub exponent was provably
  unattainable and it was orphaned; the headlines call `dl_compress_reduction ∘
  compress_ratio_le_explicit` directly. See the D12 note where it stood.)
* `dl_theorem34_beta` — the headline for the `β`-regime `aₙ = n^{−(1+β)}`, with internal choice
  `r² = qₙ log n`, `c` chosen so the Chernoff exponent dominates (`A > 2(C+2)/β`).
* `dl_theorem34_recip` — the companion for `aₙ = 1/n`, with internal `r² = qₙ` (which requires
  `qₙ ≥ C₀ log n → ∞` for the denominator error to vanish).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.4 (statement p. 9, proof pp. 18–19).

**Proof formalization notes.** The skeleton is *reduction → denominator event → Chernoff*: bridge the
posterior once (`dl_compress_reduction`), split the ratio integral at the denominator threshold
(`DenominatorLowerBound`), identify the numerator mean with the prior mass (`NormalMeansModel`), and
bound the prior mass of a large δ-support by the support-count Chernoff bound (`PriorSmallBall`,
`DensityBounds` for `ζ`). The asymptotics live only in the two thin corollaries.

**Deviations.**
* **D2 (regime-dependent `r`).** `dl_theorem34_beta` uses `r² = qₙ log n` (failure term needs only
  `qₙ ≥ 1`); `dl_theorem34_recip` uses `r² = qₙ` (failure term `e^{−qₙ}` vanishes only via
  `qₙ ≥ C₀ log n → ∞`). No single `r` serves both regimes — hence two corollaries off one engine.
* **D3 (`1 ≤ qₙ`).** Necessary: for `qₙ = 0` the δ-support of a continuous prior is everything, so
  Theorem 3.4 is false. Carried as the explicit `hq1` hypothesis (implicit in the paper).

**Bibliographic comments.** Posterior contraction after Ghosal, Ghosh, and van der Vaart
(*Ann. Statist.* 28 (2000), 500–531); sparse-sequence compressibility after Castillo and van der Vaart
(*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

/-- `n^{−p} → 0` along `ℕ` for `p > 0` (rpow, cast). -/
private lemma tendsto_natRpow_neg {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (-p)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop

/-- `log n · n^{−p} → 0` along `ℕ` for `p > 0` (polynomial beats logarithm). -/
private lemma tendsto_log_mul_natRpow_neg {p : ℝ} (hp : 0 < p) :
    Tendsto (fun n : ℕ => Real.log n * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
  have hlit := (isLittleO_log_rpow_atTop hp).tendsto_div_nhds_zero
  have hcast := hlit.comp tendsto_natCast_atTop_atTop
  refine hcast.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  simp only [Function.comp_apply]
  rw [Real.rpow_neg hn0.le, div_eq_mul_inv]

/-- **Poly-beats-log envelope.** For `p > 0`, `(C + D·log n)·n^{−p} → 0`. This is the shape of both
regimes' vanishing count/small-ball corrections. -/
private lemma tendsto_affineLog_mul_natRpow_neg {p : ℝ} (hp : 0 < p) (C D : ℝ) :
    Tendsto (fun n : ℕ => (C + D * Real.log n) * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-p)) atTop (𝓝 0) := by
    simpa using (tendsto_natRpow_neg hp).const_mul C
  have h2 : Tendsto (fun n : ℕ => D * (Real.log n * (n : ℝ) ^ (-p))) atTop (𝓝 0) := by
    simpa using (tendsto_log_mul_natRpow_neg hp).const_mul D
  have h3 := h1.add h2
  simp only [add_zero] at h3
  refine h3.congr fun n => ?_
  ring

/-- **Count split off the truth block.** At most `|S₀|` of the large coordinates of `θ` can sit in
`S₀`, so `|supp_δ(θ)| ≤ |S₀| + |supp_δ(projS S₀ᶜ θ)|`. -/
private lemma dlSuppCount_le_card_add_projS {ι : Type*} [Fintype ι] (δ : ℝ) (S₀ : Finset ι)
    (θ : EuclideanSpace ℝ ι) :
    dlSuppCount δ θ ≤ S₀.card + dlSuppCount δ (projS (↑S₀ : Set ι)ᶜ θ) := by
  classical
  -- The `S₀ᶜ`-submodel count equals the count of large coordinates outside `S₀`.
  have hBeq : dlSuppCount δ (projS (↑S₀ : Set ι)ᶜ θ)
      = (Finset.univ.filter (fun j : ι => δ < |θ j| ∧ j ∉ S₀)).card := by
    unfold dlSuppCount
    refine Finset.card_bij
      (fun (i : {j // j ∈ (↑S₀ : Set ι)ᶜ}) _ => (i : ι)) ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      have hval : (projS (↑S₀ : Set ι)ᶜ θ) a = θ a.val := rfl
      have hmem : (a : ι) ∉ S₀ := by
        have hp : (a : ι) ∈ (↑S₀ : Set ι)ᶜ := a.property
        rwa [Set.mem_compl_iff, Finset.mem_coe] at hp
      exact ⟨by rwa [hval] at ha, hmem⟩
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hmem : b ∈ (↑S₀ : Set ι)ᶜ := by
        rw [Set.mem_compl_iff, Finset.mem_coe]; exact hb.2
      refine ⟨⟨b, hmem⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hval : (projS (↑S₀ : Set ι)ᶜ θ) ⟨b, hmem⟩ = θ b := rfl
      rw [hval]; exact hb.1
  rw [hBeq]
  -- `|supp_δ θ| = |{large}∩S₀| + |{large}\S₀| ≤ |S₀| + |{large}\S₀|`.
  unfold dlSuppCount
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun j : ι => δ < |θ j|)) (p := fun j => j ∈ S₀)
  have hle : ((Finset.univ.filter (fun j : ι => δ < |θ j|)).filter (fun j => j ∈ S₀)).card
      ≤ S₀.card := by
    refine Finset.card_le_card ?_
    intro j hj
    simp only [Finset.mem_filter] at hj
    exact hj.2
  have hcompl : ((Finset.univ.filter (fun j : ι => δ < |θ j|)).filter
        (fun j => ¬ j ∈ S₀)).card
      = (Finset.univ.filter (fun j : ι => δ < |θ j| ∧ j ∉ S₀)).card := by
    rw [Finset.filter_filter]
  omega

/-- **Compressibility reduction** (BPPD §6, eq. (26)). The `E_{θ₀}`-mean of the posterior mass of
`{ |supp_δ(θ)| > |S₀| + k }` (for a truth `θ₀` supported on `S₀`) is bounded by the truth-`0`
compress-ratio integral on the `S₀ᶜ`-submodel: the posterior is bridged once
(`NormalMeansModel`), the count split off the `S₀` block, and the cylinder ratio tensorized
(`CoordinateSplit`). -/
theorem dl_compress_reduction {ι : Type*} [Fintype ι] {a δ : ℝ}
    -- LEAN-ONLY: 0 < a — DL scale at a junk-free index; engine-internal.
    (ha : 0 < a) (θ₀ : EuclideanSpace ℝ ι) (S₀ : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S₀; engine-internal (the truth's support, `= o(n)` in the assembly).
    (hθ₀ : ∀ i ∉ S₀, θ₀ i = 0) (k : ℕ) :
    ∫⁻ y, ((gaussShiftKernel ι)†(dlPrior a ι)) y
            {θ | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)}
          ∂(gaussShiftKernel ι θ₀)
      ≤ ∫⁻ y, dlNumer (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀}) (dlPrior a {i : ι // i ∉ S₀})
              {θ | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y
            / dlDenom (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀}) (dlPrior a {i : ι // i ∉ S₀}) y
          ∂(gaussShiftKernel {i : ι // i ∉ S₀} (0 : EuclideanSpace ℝ {i : ι // i ∉ S₀})) := by
  classical
  set S : Set ι := (↑S₀ : Set ι) with hSdef
  set π := dlPrior a ι with hπ
  -- The truth vanishes on `Sᶜ`.
  have hθ₀' : projS Sᶜ θ₀ = (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ}) := by
    ext i
    have hval : (projS Sᶜ θ₀) i = θ₀ i.val := rfl
    have hi : (i : ι) ∉ S₀ := i.property
    rw [hval, hθ₀ i.val hi]; rfl
  -- Measurability of the two count events.
  have hcast₁ : Measurable (fun θ : EuclideanSpace ℝ ι => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hCmeas : MeasurableSet
      {θ : EuclideanSpace ℝ ι | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)} :=
    measurableSet_lt measurable_const hcast₁
  have hcast₂ : Measurable
      (fun θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} => ((dlSuppCount δ θ : ℕ) : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (measurable_dlSuppCount δ)
  have hDmeas : MeasurableSet
      {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} :=
    measurableSet_lt measurable_const hcast₂
  -- The compress event sits inside the `Sᶜ`-cylinder over `{count > k}`.
  have hsub : {θ : EuclideanSpace ℝ ι | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)}
      ⊆ projS Sᶜ ⁻¹' {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} := by
    intro θ hθ
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hθ ⊢
    have hcount := dlSuppCount_le_card_add_projS δ S₀ θ
    have : ((S₀.card : ℝ) + k) < (S₀.card : ℝ) + (dlSuppCount δ (projS Sᶜ θ) : ℝ) :=
      lt_of_lt_of_le hθ (by exact_mod_cast hcount)
    linarith
  -- Numerator measurability on the submodel (for the change of variables).
  have hratio_meas : Measurable (fun y' : EuclideanSpace ℝ {j // j ∈ Sᶜ} =>
      dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
          {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
        / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) y') :=
    (measurable_dlNumer _ _ _).div (measurable_dlDenom _ _)
  have hmproj : Measurable (projS (ι := ι) Sᶜ) := by
    unfold projS
    exact (WithLp.measurable_toLp _ _).comp
      (measurable_pi_lambda _ fun i =>
        (measurable_pi_apply (i : ι)).comp (WithLp.measurable_ofLp 2 _))
  -- Assemble.
  rw [lintegral_posterior_eq_lintegral_ratio θ₀ π hCmeas]
  calc ∫⁻ y, dlNumer θ₀ π
            {θ : EuclideanSpace ℝ ι | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)} y
          / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀)
      ≤ ∫⁻ y, dlNumer θ₀ π
            (projS Sᶜ ⁻¹'
              {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)}) y
          / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀) := by
        refine lintegral_mono fun y => ?_
        exact ENNReal.div_le_div_right (dlNumer_mono θ₀ π hsub y) _
    _ = ∫⁻ y, dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
            {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} (projS Sᶜ y)
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y)
          ∂(gaussShiftKernel ι θ₀) := by
        refine lintegral_congr fun y => ?_
        exact dlRatio_cylinder a S θ₀ y hθ₀' hDmeas
    _ = ∫⁻ y', dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
            {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) y'
          ∂((gaussShiftKernel ι θ₀).map (projS Sᶜ)) := by
        rw [lintegral_map hratio_meas hmproj]
    _ = ∫⁻ y', dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ})
            {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) y'
          ∂(gaussShiftKernel {j // j ∈ Sᶜ} (projS Sᶜ θ₀)) := by
        rw [gaussShift_map_projS]
    _ = ∫⁻ y', dlNumer (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ}) (dlPrior a {j // j ∈ Sᶜ})
              {θ : EuclideanSpace ℝ {j // j ∈ Sᶜ} | (k : ℝ) < (dlSuppCount δ θ : ℝ)} y'
            / dlDenom (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ}) (dlPrior a {j // j ∈ Sᶜ}) y'
          ∂(gaussShiftKernel {j // j ∈ Sᶜ} (0 : EuclideanSpace ℝ {j // j ∈ Sᶜ})) := by
        rw [hθ₀']

set_option maxHeartbeats 1000000 in
/-- **Honest fixed-`n` composition** (reduction ∘ explicit ∘ event-monotonicity). Bounds the
`E_{θ₀}`-mean of the posterior mass of `{ |supp_δ(θ)| > Aq }` by the honest engine exponent
`card'·z·(c−1) − k·log c + r² + 2·card'·w` plus `e^{−r²/8}`, where `card' = |S₀ᶜ|`. This is the
shape actually produced by the two closed engine lemmas (cf. `compress_ratio_le_explicit`'s D2/D3
note); the asymptotic headlines drive `card'·w → 0` and the growing Chernoff parameter make it
vanish. -/
private lemma dl_thm34_reduce_explicit_event {n : ℕ} {a δ r : ℝ}
    (ha : 0 < a) (hr : 0 < r)
    (θ₀ : EuclideanSpace ℝ (Fin n)) (S₀ : Finset (Fin n)) (hθ₀ : ∀ i ∉ S₀, θ₀ i = 0) (k : ℕ)
    (z : ℝ) (hz : (dlMarginal a {x : ℝ | δ < |x|}).toReal ≤ z)
    (w : ℝ)
    (hw : (dlMarginal a
        {x : ℝ | min (r / Real.sqrt (Fintype.card {i : Fin n // i ∉ S₀} : ℝ)) (1 / 2) < |x|}).toReal
        ≤ w)
    (hw2 : w ≤ 1 / 2) (c : ℝ) (hc : 1 < c) (Aq : ℝ)
    (hk : (S₀.card : ℝ) + (k : ℝ) ≤ Aq) :
    ∫⁻ y, ((gaussShiftKernel (Fin n))†(dlPrior a (Fin n))) y
          {θ | Aq < (dlSuppCount δ θ : ℝ)} ∂(gaussShiftKernel (Fin n) θ₀)
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card {i : Fin n // i ∉ S₀} : ℝ) * z * (c - 1)
            - (k : ℝ) * Real.log c + r ^ 2
            + 2 * (Fintype.card {i : Fin n // i ∉ S₀} : ℝ) * w))
          + ENNReal.ofReal (Real.exp (- r ^ 2 / 8)) := by
  have hmono : ∫⁻ y, ((gaussShiftKernel (Fin n))†(dlPrior a (Fin n))) y
          {θ | Aq < (dlSuppCount δ θ : ℝ)} ∂(gaussShiftKernel (Fin n) θ₀)
      ≤ ∫⁻ y, ((gaussShiftKernel (Fin n))†(dlPrior a (Fin n))) y
          {θ | ((S₀.card : ℝ) + k) < (dlSuppCount δ θ : ℝ)} ∂(gaussShiftKernel (Fin n) θ₀) := by
    refine lintegral_mono fun y => measure_mono fun θ hθ => ?_
    simp only [Set.mem_setOf_eq] at hθ ⊢
    exact lt_of_le_of_lt hk hθ
  refine hmono.trans ((dl_compress_reduction ha θ₀ S₀ hθ₀ k).trans ?_)
  convert compress_ratio_le_explicit ha hr k z hz w hw hw2 c hc using 2 <;>
    first | rfl | congr!

/- **Fixed-`n` compressibility engine — REMOVED (orphaned + false stub).** The stub
`dl_theorem34_engine` claimed the compressibility posterior mass `≤ exp((card ι)·e·a·(8+2log(1/δ))·(c−1)
− (A−1)q·log c + 3r²) + e^{−r²/8}`. The `thm34-asym` closure session proved this exponent is **not
attainable**: (i) the `3r²` folds the honest small-ball correction `2·card'·w` into `2r²` via
`card'·w ≤ r²`, false for fixed `r` as `card' → ∞`; (ii) the Chernoff `−(A−1)q·log c` needs `k ≥ (A−1)q`
but `k = ⌊Aq⌋ − |S₀| ≥ (A−1)q − 1`, off by `log c`. The asymptotic headlines `dl_theorem34_beta` /
`dl_theorem34_recip` below **do not need it** — they call `dl_compress_reduction ∘
compress_ratio_le_explicit` (the honest fixed-`n` bricks, `CompressEngine`) directly. The `PosteriorContraction`
assembly likewise uses those bricks for its 3.4-term. So the intermediate is deleted rather than
restated (D12). -/

/-- **BPPD Theorem 3.4 (posterior compressibility, `β`-regime).** In the normal-means model with the
Dirichlet–Laplace prior at scale `aₙ = n^{−(1+β)}`, there is a threshold `A > 0` such that the
posterior probability of `{ θ : more than A·qₙ coordinates exceed δₙ }` tends to `0` in `E_{θ₀}`.
Internal radius `r² = qₙ log n` (D2). -/
theorem dl_theorem34_beta {β : ℝ}
    -- USER-INPUT: β > 0 (DL scale exponent aₙ = n^{−(1+β)}); BPPD Thm 3.4.
    (hβ : 0 < β) {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (nonempty approximate support; D3 — for qₙ = 0 Thm 3.4 is false); BPPD Thm 3.4.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n) (sparsity grows sub-linearly); BPPD Thm 3.4.
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ is qₙ-sparse (at most qₙ nonzero coordinates); BPPD Thm 3.4.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    {δ : ℕ → ℝ}
    -- USER-INPUT: δ-window n^{−2} ≤ δₙ ≤ 1/2 (thresholding level; D2 — supports the internal δ = rₙ/n); BPPD Thm 3.4.
    (hδ : ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^(-2 : ℝ) ≤ δ n ∧ δ n ≤ 1/2) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)^(-(1+β))) (Fin n))) y
          {θ | A * q n < (dlSuppCount (δ n) θ : ℝ)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  classical
  -- Chernoff/threshold constants: `A = 3 + 2/β` and growing MGF parameter `cₙ = n^{β/2}`.
  refine ⟨3 + 2 / β, by positivity, ?_⟩
  set A : ℝ := 3 + 2 / β with hA_def
  set S₀ : (n : ℕ) → Finset (Fin n) := fun n => Finset.univ.filter fun j => θ₀ n j ≠ 0 with hS₀
  set av : ℕ → ℝ := fun n => (n : ℝ) ^ (-(1 + β)) with hav
  set cv : ℕ → ℝ := fun n => (n : ℝ) ^ (β / 2) with hcv
  set rv : ℕ → ℝ := fun n => Real.sqrt ((q n : ℝ) * Real.log n) with hrv
  set mv : ℕ → ℝ := fun n => (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ) with hmv
  set zv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / δ n)) with hzv
  set sv : ℕ → ℝ := fun n => min (rv n / Real.sqrt (mv n)) (1 / 2) with hsv
  set wv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / sv n)) with hwv
  set kv : ℕ → ℕ := fun n => ⌊A * q n⌋₊ - (S₀ n).card with hkv
  -- Honest engine exponent and the resulting `ℝ≥0∞` upper bound.
  set P : ℕ → ℝ := fun n => mv n * zv n * (cv n - 1) - (kv n : ℝ) * Real.log (cv n)
      + rv n ^ 2 + 2 * mv n * wv n with hP
  set B : ℕ → ℝ≥0∞ := fun n =>
      ENNReal.ofReal (Real.exp (P n)) + ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8)) with hB
  -- ===== shared envelope facts =====
  have hav_pos : ∀ᶠ n in atTop, 0 < av n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  have hmv_le : ∀ n, mv n ≤ (n : ℝ) := by
    intro n
    have h : Fintype.card {i : Fin n // i ∉ S₀ n} ≤ n :=
      (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
    simp only [hmv]; exact_mod_cast h
  have hqlt : ∀ᶠ n in atTop, (q n : ℝ) < n := by
    filter_upwards [hqn.eventually (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)),
      eventually_gt_atTop 0] with n hlt hn0
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    have hlt' : (q n : ℝ) / n < 1 := hlt
    exact (div_lt_one hnpos).mp hlt'
  have hmvpos : ∀ᶠ n in atTop, 0 < mv n := by
    filter_upwards [hqlt] with n hql
    have hcard : (S₀ n).card < n := lt_of_le_of_lt (hθ₀ n) (by exact_mod_cast hql)
    have hex : ∃ j : Fin n, j ∉ S₀ n := by
      by_contra hcon
      push_neg at hcon
      have huniv : S₀ n = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard; omega
    obtain ⟨j, hj⟩ := hex
    have : Nonempty {i : Fin n // i ∉ S₀ n} := ⟨j, hj⟩
    simp only [hmv]
    exact_mod_cast Fintype.card_pos
  -- `zₙ ≤ e·aₙ·(8 + 4 log n)` from `δₙ ≥ n^{−2}`.
  have hzv_le : ∀ᶠ n in atTop, zv n ≤ Real.exp 1 * av n * (8 + 4 * Real.log n) := by
    filter_upwards [hδ, eventually_ge_atTop 1, hav_pos] with n hδn hn1 hapos
    obtain ⟨hδlb, hδub⟩ := hδn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hδpos : 0 < δ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
    have h1 : Real.log (1 / δ n) ≤ 2 * Real.log n := by
      rw [one_div, Real.log_inv]
      have hle : Real.log ((n:ℝ)^(-2:ℝ)) ≤ Real.log (δ n) :=
        Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hδlb
      rw [Real.log_rpow hnpos] at hle; linarith
    rw [hzv]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- `sₙ ≥ 1/√n`, hence `log(1/sₙ) ≤ ½ log n` and `wₙ ≤ e·aₙ·(8 + log n)`.
  have hsv_ge : ∀ᶠ (n : ℕ) in atTop, 1 / Real.sqrt n ≤ sv n := by
    filter_upwards [eventually_ge_atTop 4, hmvpos] with n hn4 hmvp
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hlogn1 : (1:ℝ) ≤ Real.log n := by
      rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
      exact Real.log_le_log (Real.exp_pos 1) (by
        have : Real.exp 1 ≤ 3 := by
          have := Real.exp_one_lt_d9; linarith
        have h3 : (4:ℝ) ≤ n := by exact_mod_cast hn4
        linarith)
    have hrv1 : (1:ℝ) ≤ rv n := by
      rw [hrv]
      rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt
      have hq1n : (1:ℝ) ≤ (q n:ℝ) := by exact_mod_cast hq1 n
      nlinarith [hlogn1, hq1n]
    have hsqn2 : (2:ℝ) ≤ Real.sqrt n := by
      rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt; exact_mod_cast hn4
    have hsqnpos : 0 < Real.sqrt n := by positivity
    have hmvsqle : Real.sqrt (mv n) ≤ Real.sqrt n := Real.sqrt_le_sqrt (hmv_le n)
    have hmvsqpos : 0 < Real.sqrt (mv n) := Real.sqrt_pos.mpr hmvp
    rw [hsv]
    apply le_min
    · -- 1/√n ≤ rv n / √(mv n)
      calc 1 / Real.sqrt n ≤ 1 / Real.sqrt (mv n) :=
              one_div_le_one_div_of_le hmvsqpos hmvsqle
        _ ≤ rv n / Real.sqrt (mv n) := by gcongr
    · -- 1/√n ≤ 1/2
      exact one_div_le_one_div_of_le (by norm_num) hsqn2
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
    have h := tendsto_affineLog_mul_natRpow_neg (p := 1 + β) (by linarith)
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
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => (0 : ℝ≥0∞)) (h := B)
    tendsto_const_nhds ?hbound (Filter.Eventually.of_forall fun n => zero_le) ?hle
  case hle =>
    filter_upwards [hδ, eventually_ge_atTop 4, hsv_ge, hw2, hcv_gt1, hav_pos]
      with n hδn hn4 hsvge hw2n hcvn hapos
    obtain ⟨hδlb, hδub⟩ := hδn
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hn2 : (1:ℝ) < n := by
      have : (4:ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    have ha_le1 : av n ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1R (by linarith)
    have hδpos : 0 < δ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
    have hδlt1 : δ n < 1 := lt_of_le_of_lt hδub (by norm_num)
    have hlogn_pos : 0 < Real.log n := Real.log_pos hn2
    have hr_pos : 0 < rv n := by
      rw [hrv]; apply Real.sqrt_pos.mpr
      exact mul_pos (by exact_mod_cast hq1 n) hlogn_pos
    have hsupp : ∀ i ∉ S₀ n, θ₀ n i = 0 := by
      intro i hi
      simp only [hS₀, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      exact hi
    -- `hz`: the δ-exceedance C3 bound.
    have hlogd : 0 ≤ Real.log (1 / δ n) := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
    have hz : (dlMarginal (av n) {x : ℝ | δ n < |x|}).toReal ≤ zv n := by
      have hm := dlMarginal_abs_gt_le' hapos ha_le1 hδpos hδlt1
      have hznn : (0:ℝ) ≤ zv n := by
        rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      calc (dlMarginal (av n) {x : ℝ | δ n < |x|}).toReal
          ≤ (ENNReal.ofReal (zv n)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
        _ = zv n := ENNReal.toReal_ofReal hznn
    -- `hw`: the small-ball C3 bound at the clamped threshold `sₙ`.
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
    -- `hk`: the event-inclusion threshold.
    have hAqn : (0:ℝ) ≤ A * q n := by
      rw [hA_def]; positivity
    have hcard_le : (S₀ n).card ≤ ⌊A * (q n : ℝ)⌋₊ := by
      apply Nat.le_floor
      have h1 : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
      have h2 : (1:ℝ) ≤ A := by
        rw [hA_def]; have : 0 < 2 / β := by positivity
        linarith
      have h3 : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
      nlinarith
    have hk : ((S₀ n).card : ℝ) + (kv n : ℝ) ≤ A * q n := by
      rw [hkv, Nat.cast_sub hcard_le]
      have hfl := Nat.floor_le hAqn
      push_cast
      linarith
    have hcvpos : (1 : ℝ) < cv n := hcvn
    exact dl_thm34_reduce_explicit_event hapos hr_pos (θ₀ n) (S₀ n) hsupp (kv n)
      (zv n) hz (wv n) hw hw2n (cv n) hcvpos (A * q n) hk
  case hbound =>
    have hlogtend : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    -- Small correction terms vanish (poly-beats-log envelopes).
    have hS1 : Tendsto (fun n => mv n * zv n * (cv n - 1)) atTop (𝓝 0) := by
      have hU1 : Tendsto (fun n : ℕ =>
          Real.exp 1 * (8 + 4 * Real.log n) * (n : ℝ) ^ (-(β / 2))) atTop (𝓝 0) := by
        have h := tendsto_affineLog_mul_natRpow_neg (p := β / 2) (by linarith)
          (8 * Real.exp 1) (4 * Real.exp 1)
        refine h.congr fun n => ?_; ring
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU1 ?_ ?_
      · filter_upwards [hδ, eventually_ge_atTop 1, hav_pos, hcv_gt1] with n hδn hn1 hapos hcvn
        obtain ⟨hδlb, hδub⟩ := hδn
        have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
        have hδpos : 0 < δ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
        have hlogd : 0 ≤ Real.log (1 / δ n) :=
          Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
        have hzvnn : 0 ≤ zv n := by
          rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
        have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
        have hcvnn : 0 ≤ cv n - 1 := by linarith [hcvn]
        exact mul_nonneg (mul_nonneg hmvnn hzvnn) hcvnn
      · filter_upwards [hzv_le, eventually_ge_atTop 1, hav_pos, hcv_gt1, hδ] with
          n hzvle hn1 hapos hcvn hδn
        obtain ⟨hδlb, hδub⟩ := hδn
        have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
        have hn1R : (1:ℝ) ≤ n := by exact_mod_cast hn1
        have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
        have hδpos : 0 < δ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
        have hlogd : 0 ≤ Real.log (1 / δ n) :=
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
        have h := tendsto_affineLog_mul_natRpow_neg (p := β) hβ (8 * Real.exp 1) (Real.exp 1)
        refine h.congr fun n => ?_; ring
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU2 ?_ ?_
      · filter_upwards [hw2, eventually_ge_atTop 4, hsv_ge] with n hw2n hn4 hsvge
        have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
        have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
        have hsvlt1 : sv n < 1 := by
          rw [hsv]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        have hwvnn : 0 ≤ wv n := by
          rw [hwv]
          have : 0 ≤ Real.log (1 / sv n) :=
            Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith)
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
        have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
        have hsvlt1 : sv n < 1 := by
          rw [hsv]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        have hlogs : 0 ≤ Real.log (1 / sv n) :=
          Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith)
        have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
        have hwvnn : 0 ≤ wv n := by
          rw [hwv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
        have henv_nn : 0 ≤ Real.exp 1 * av n * (8 + Real.log n) :=
          mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
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
      -- rewrite `log(cvₙ)` and `rvₙ²`.
      have hlogcv : Real.log (cv n) = (β / 2) * Real.log n := by rw [hcv, Real.log_rpow hnpos]
      have hrv2 : rv n ^ 2 = (q n : ℝ) * Real.log n := by
        rw [hrv]; exact Real.sq_sqrt (mul_nonneg (by positivity) hlogn)
      -- lower bound on `kₙ`.
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
      rw [hrv2]
      have hle : Real.log n ≤ (q n : ℝ) * Real.log n := by nlinarith
      linarith
    -- Assemble: `exp(P n) → 0` and `exp(−rₙ²/8) → 0`.
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
      refine hh.congr fun n => ?_
      rw [neg_neg]
    have hf2 : Tendsto (fun n => ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8))) atTop (𝓝 0) := by
      have hh := tendsto_ofReal_exp_neg hε2
      refine hh.congr fun n => ?_
      rw [neg_div]
    have hsum := hf1.add hf2
    rw [add_zero] at hsum
    exact hsum

set_option maxHeartbeats 1000000 in
/-- **BPPD Theorem 3.4 (posterior compressibility, `1/n`-regime).** Same conclusion with scale
`aₙ = 1/n`, additionally requiring `qₙ ≥ C₀ log n` so the internal `r² = qₙ` (D2) forces the
denominator error `e^{−qₙ}` to vanish. -/
theorem dl_theorem34_recip {q : ℕ → ℕ}
    -- USER-INPUT: qₙ ≥ 1 (D3); BPPD Thm 3.4.
    (hq1 : ∀ n, 1 ≤ q n)
    -- USER-INPUT: qₙ = o(n); BPPD Thm 3.4.
    (hqn : Tendsto (fun n => (q n : ℝ) / n) atTop (𝓝 0))
    {θ₀ : (n : ℕ) → EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: θ₀ qₙ-sparse; BPPD Thm 3.4.
    (hθ₀ : ∀ n, (Finset.univ.filter fun j => θ₀ n j ≠ 0).card ≤ q n)
    {δ : ℕ → ℝ}
    -- USER-INPUT: δ-window n^{−2} ≤ δₙ ≤ 1/2 (D2); BPPD Thm 3.4.
    (hδ : ∀ᶠ (n : ℕ) in atTop, (n : ℝ)^(-2 : ℝ) ≤ δ n ∧ δ n ≤ 1/2)
    -- USER-INPUT: qₙ ≥ C₀ log n (needed for the 1/n-regime denominator error, D2); BPPD Thm 3.4.
    (hqlog : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ (n : ℕ) in atTop, C₀ * Real.log n ≤ (q n : ℝ)) :
    ∃ A : ℝ, 0 < A ∧ Tendsto (fun n => ∫⁻ y,
        ((gaussShiftKernel (Fin n))†(dlPrior ((n : ℝ)⁻¹) (Fin n))) y
          {θ | A * q n < (dlSuppCount (δ n) θ : ℝ)}
        ∂(gaussShiftKernel (Fin n) (θ₀ n))) atTop (𝓝 0) := by
  classical
  obtain ⟨C₀, hC₀pos, hqlogev⟩ := hqlog
  -- `1/n`-regime: constant Chernoff `cₙ = e`, threshold `A = 3 + coef/C₀` with
  -- `coef = 4e(e−1) + 2e` (so the log-`n` coefficient of the count/small terms is exactly cancelled).
  have he1 : (1:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  have hcoef : (0:ℝ) ≤ (4 * Real.exp 1 * (Real.exp 1 - 1) + 2 * Real.exp 1) / C₀ :=
    div_nonneg (by nlinarith [Real.exp_pos 1]) hC₀pos.le
  refine ⟨3 + (4 * Real.exp 1 * (Real.exp 1 - 1) + 2 * Real.exp 1) / C₀, by linarith, ?_⟩
  set A : ℝ := 3 + (4 * Real.exp 1 * (Real.exp 1 - 1) + 2 * Real.exp 1) / C₀ with hA_def
  set S₀ : (n : ℕ) → Finset (Fin n) := fun n => Finset.univ.filter fun j => θ₀ n j ≠ 0 with hS₀
  set av : ℕ → ℝ := fun n => (n : ℝ)⁻¹ with hav
  set cv : ℕ → ℝ := fun _ => Real.exp 1 with hcv
  set rv : ℕ → ℝ := fun n => Real.sqrt (q n : ℝ) with hrv
  set mv : ℕ → ℝ := fun n => (Fintype.card {i : Fin n // i ∉ S₀ n} : ℝ) with hmv
  set zv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / δ n)) with hzv
  set sv : ℕ → ℝ := fun n => min (rv n / Real.sqrt (mv n)) (1 / 2) with hsv
  set wv : ℕ → ℝ := fun n => Real.exp 1 * av n * (8 + 2 * Real.log (1 / sv n)) with hwv
  set kv : ℕ → ℕ := fun n => ⌊A * q n⌋₊ - (S₀ n).card with hkv
  set P : ℕ → ℝ := fun n => mv n * zv n * (cv n - 1) - (kv n : ℝ) * Real.log (cv n)
      + rv n ^ 2 + 2 * mv n * wv n with hP
  set B : ℕ → ℝ≥0∞ := fun n =>
      ENNReal.ofReal (Real.exp (P n)) + ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8)) with hB
  -- ===== shared envelope facts =====
  have hav_pos : ∀ᶠ n in atTop, 0 < av n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0:ℝ) < n := by exact_mod_cast hn
    rw [hav]; positivity
  have hmv_le : ∀ n, mv n ≤ (n : ℝ) := by
    intro n
    have h : Fintype.card {i : Fin n // i ∉ S₀ n} ≤ n :=
      (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
    simp only [hmv]; exact_mod_cast h
  have hqlt : ∀ᶠ n in atTop, (q n : ℝ) < n := by
    filter_upwards [hqn.eventually (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num)),
      eventually_gt_atTop 0] with n hlt hn0
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn0
    have hlt' : (q n : ℝ) / n < 1 := hlt
    exact (div_lt_one hnpos).mp hlt'
  have hmvpos : ∀ᶠ n in atTop, 0 < mv n := by
    filter_upwards [hqlt] with n hql
    have hcard : (S₀ n).card < n := lt_of_le_of_lt (hθ₀ n) (by exact_mod_cast hql)
    have hex : ∃ j : Fin n, j ∉ S₀ n := by
      by_contra hcon
      push_neg at hcon
      have huniv : S₀ n = Finset.univ := Finset.eq_univ_of_forall hcon
      rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard; omega
    obtain ⟨j, hj⟩ := hex
    have : Nonempty {i : Fin n // i ∉ S₀ n} := ⟨j, hj⟩
    simp only [hmv]
    exact_mod_cast Fintype.card_pos
  have hzv_le : ∀ᶠ n in atTop, zv n ≤ Real.exp 1 * av n * (8 + 4 * Real.log n) := by
    filter_upwards [hδ, eventually_ge_atTop 1, hav_pos] with n hδn hn1 hapos
    obtain ⟨hδlb, hδub⟩ := hδn
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn1
    have hδpos : 0 < δ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
    have h1 : Real.log (1 / δ n) ≤ 2 * Real.log n := by
      rw [one_div, Real.log_inv]
      have hle : Real.log ((n:ℝ)^(-2:ℝ)) ≤ Real.log (δ n) :=
        Real.log_le_log (Real.rpow_pos_of_pos hnpos _) hδlb
      rw [Real.log_rpow hnpos] at hle; linarith
    rw [hzv]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsv_ge : ∀ᶠ (n : ℕ) in atTop, 1 / Real.sqrt n ≤ sv n := by
    filter_upwards [eventually_ge_atTop 4, hmvpos] with n hn4 hmvp
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hrv1 : (1:ℝ) ≤ rv n := by
      rw [hrv, show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
      apply Real.sqrt_le_sqrt; exact_mod_cast hq1 n
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
    have h := tendsto_affineLog_mul_natRpow_neg (p := 1) (by norm_num) (8 * Real.exp 1) (Real.exp 1)
    refine h.congr fun n => ?_
    rw [hav, Real.rpow_neg_one]; ring
  have hw2 : ∀ᶠ n in atTop, wv n ≤ 1 / 2 := by
    have hev : ∀ᶠ n in atTop, Real.exp 1 * av n * (8 + Real.log n) ∈ Set.Iio (1/2 : ℝ) :=
      hWtend.eventually (Iio_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
    filter_upwards [hwv_le, hev] with n h1 h2
    have h2' : Real.exp 1 * av n * (8 + Real.log n) < 1 / 2 := h2
    linarith
  have hcv_gt1 : ∀ᶠ n in atTop, 1 < cv n := by
    filter_upwards with n
    rw [hcv]; have := Real.add_one_le_exp (1:ℝ); linarith
  have hlogtend : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ => (0 : ℝ≥0∞)) (h := B)
    tendsto_const_nhds ?hbound (Filter.Eventually.of_forall fun n => zero_le) ?hle
  case hle =>
    filter_upwards [hδ, eventually_ge_atTop 4, hsv_ge, hw2, hcv_gt1, hav_pos]
      with n hδn hn4 hsvge hw2n hcvn hapos
    obtain ⟨hδlb, hδub⟩ := hδn
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
    have hnpos : (0:ℝ) < n := by linarith
    have hn2 : (1:ℝ) < n := by
      have : (4:ℝ) ≤ n := by exact_mod_cast hn4
      linarith
    have ha_le1 : av n ≤ 1 := by rw [hav]; rw [inv_le_one_iff₀]; right; exact hn1R
    have hδpos : 0 < δ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
    have hδlt1 : δ n < 1 := lt_of_le_of_lt hδub (by norm_num)
    have hr_pos : 0 < rv n := by
      rw [hrv]; apply Real.sqrt_pos.mpr; exact_mod_cast hq1 n
    have hsupp : ∀ i ∉ S₀ n, θ₀ n i = 0 := by
      intro i hi
      simp only [hS₀, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
      exact hi
    have hlogd : 0 ≤ Real.log (1 / δ n) := Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
    have hz : (dlMarginal (av n) {x : ℝ | δ n < |x|}).toReal ≤ zv n := by
      have hm := dlMarginal_abs_gt_le' hapos ha_le1 hδpos hδlt1
      have hznn : (0:ℝ) ≤ zv n := by
        rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
      calc (dlMarginal (av n) {x : ℝ | δ n < |x|}).toReal
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
    have hAqn : (0:ℝ) ≤ A * q n := by rw [hA_def]; positivity
    have hcard_le : (S₀ n).card ≤ ⌊A * (q n : ℝ)⌋₊ := by
      apply Nat.le_floor
      have h1 : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
      have h2 : (1:ℝ) ≤ A := by rw [hA_def]; linarith [hcoef]
      have h3 : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
      nlinarith
    have hk : ((S₀ n).card : ℝ) + (kv n : ℝ) ≤ A * q n := by
      rw [hkv, Nat.cast_sub hcard_le]
      have hfl := Nat.floor_le hAqn
      push_cast
      linarith
    have hcvpos : (1 : ℝ) < cv n := hcvn
    exact dl_thm34_reduce_explicit_event hapos hr_pos (θ₀ n) (S₀ n) hsupp (kv n)
      (zv n) hz (wv n) hw hw2n (cv n) hcvpos (A * q n) hk
  case hbound =>
    -- `exp(P n) → 0` via a direct lower bound `−P n ≥ C₀ log n − const₁ → ∞`.
    have hf1 : Tendsto (fun n => ENNReal.ofReal (Real.exp (P n))) atTop (𝓝 0) := by
      have hdiv : Tendsto (fun n => -(P n)) atTop atTop := by
        set const1 : ℝ := 1 + 8 * (Real.exp 1 * (Real.exp 1 - 1)) + 16 * Real.exp 1 with hconst1
        have htend : Tendsto (fun n : ℕ => C₀ * Real.log n - const1) atTop atTop := by
          have h := tendsto_atTop_add_const_right atTop (-const1)
            (hlogtend.const_mul_atTop hC₀pos)
          simpa [sub_eq_add_neg] using h
        apply tendsto_atTop_mono' atTop ?_ htend
        · filter_upwards [hδ, eventually_ge_atTop 4, hsv_ge, hzv_le, hwv_le, hqlogev, hav_pos]
            with n hδn hn4 hsvge hzvle hwvle hqlogn hapos
          obtain ⟨hδlb, hδub⟩ := hδn
          have hn1R : (1:ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) hn4)
          have hnpos : (0:ℝ) < n := by linarith
          have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1R
          have hnav : (n : ℝ) * av n = 1 := by rw [hav]; field_simp
          have hlogcv : Real.log (cv n) = 1 := by rw [hcv, Real.log_exp]
          have hrv2 : rv n ^ 2 = (q n : ℝ) := by rw [hrv]; exact Real.sq_sqrt (by positivity)
          have hmvnn : 0 ≤ mv n := by rw [hmv]; positivity
          have hδpos : 0 < δ n := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hδlb
          have hlogd : 0 ≤ Real.log (1 / δ n) :=
            Real.log_nonneg (by rw [le_div_iff₀ hδpos]; linarith)
          have hzvnn : 0 ≤ zv n := by
            rw [hzv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
          have hsvpos : 0 < sv n := lt_of_lt_of_le (by positivity) hsvge
          have hsvlt1 : sv n < 1 := by
            rw [hsv]; exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
          have hlogs : 0 ≤ Real.log (1 / sv n) :=
            Real.log_nonneg (by rw [le_div_iff₀ hsvpos]; linarith)
          have hwvnn : 0 ≤ wv n := by
            rw [hwv]; exact mul_nonneg (mul_nonneg (Real.exp_pos 1).le hapos.le) (by linarith)
          -- `mvₙ·zₙ ≤ e(8+4 log n)`, `mvₙ·wₙ ≤ e(8+log n)`.
          have hmvz : mv n * zv n ≤ Real.exp 1 * (8 + 4 * Real.log n) := by
            calc mv n * zv n ≤ (n : ℝ) * (Real.exp 1 * av n * (8 + 4 * Real.log n)) :=
                  mul_le_mul (hmv_le n) hzvle hzvnn (by positivity)
              _ = Real.exp 1 * (8 + 4 * Real.log n) * ((n : ℝ) * av n) := by ring
              _ = Real.exp 1 * (8 + 4 * Real.log n) := by rw [hnav, mul_one]
          have hmvw : mv n * wv n ≤ Real.exp 1 * (8 + Real.log n) := by
            calc mv n * wv n ≤ (n : ℝ) * (Real.exp 1 * av n * (8 + Real.log n)) :=
                  mul_le_mul (hmv_le n) hwvle hwvnn (by positivity)
              _ = Real.exp 1 * (8 + Real.log n) * ((n : ℝ) * av n) := by ring
              _ = Real.exp 1 * (8 + Real.log n) := by rw [hnav, mul_one]
          -- `kₙ ≥ (A−1) qₙ − 1`.
          have hAqn : (0:ℝ) ≤ A * q n := by rw [hA_def]; positivity
          have hcard_le : (S₀ n).card ≤ ⌊A * (q n : ℝ)⌋₊ := by
            apply Nat.le_floor
            have h1 : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
            have h2 : (1:ℝ) ≤ A := by rw [hA_def]; linarith [hcoef]
            have h3 : (1:ℝ) ≤ (q n : ℝ) := by exact_mod_cast hq1 n
            nlinarith
          have hklb : (A - 1) * (q n : ℝ) - 1 ≤ (kv n : ℝ) := by
            rw [hkv, Nat.cast_sub hcard_le]
            have hfloor : A * (q n : ℝ) - 1 < ⌊A * (q n : ℝ)⌋₊ := by
              have := Nat.lt_floor_add_one (A * (q n : ℝ)); linarith
            have hcardle : ((S₀ n).card : ℝ) ≤ q n := Nat.cast_le.mpr (hθ₀ n)
            push_cast; nlinarith
          -- Assemble the linear lower bound (the `log n` terms cancel by choice of `A`).
          have he0 : (0:ℝ) ≤ Real.exp 1 - 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
          have hA2 : (0:ℝ) ≤ A - 2 := by rw [hA_def]; linarith [hcoef]
          have hqm : (A - 2) * (C₀ * Real.log n) ≤ (A - 2) * (q n : ℝ) :=
            mul_le_mul_of_nonneg_left hqlogn hA2
          have hAC : (A - 2) * C₀ = C₀ + (4 * Real.exp 1 * (Real.exp 1 - 1) + 2 * Real.exp 1) := by
            rw [hA_def]; field_simp; ring
          have hPeq : P n = mv n * zv n * (cv n - 1) - (kv n : ℝ) + (q n : ℝ)
              + 2 * (mv n * wv n) := by simp only [hP]; rw [hlogcv, hrv2]; ring
          have hcvm1 : cv n - 1 = Real.exp 1 - 1 := by rw [hcv]
          -- Expanded (linear-in-atoms) forms so `linarith` can cancel the `log n` terms.
          have h_a : mv n * zv n * (cv n - 1)
              ≤ 8 * (Real.exp 1 * (Real.exp 1 - 1))
                + 4 * (Real.exp 1 * (Real.exp 1 - 1)) * Real.log n := by
            rw [hcvm1]
            have := mul_le_mul_of_nonneg_right hmvz he0
            nlinarith [this]
          have hmvw' : mv n * wv n ≤ 8 * Real.exp 1 + Real.exp 1 * Real.log n := by
            nlinarith [hmvw]
          have hqm' : C₀ * Real.log n + 4 * (Real.exp 1 * (Real.exp 1 - 1)) * Real.log n
              + 2 * Real.exp 1 * Real.log n ≤ (A - 2) * (q n : ℝ) := by
            have hid : (A - 2) * (C₀ * Real.log n)
                = C₀ * Real.log n + 4 * (Real.exp 1 * (Real.exp 1 - 1)) * Real.log n
                  + 2 * Real.exp 1 * Real.log n := by
              rw [show (A - 2) * (C₀ * Real.log n) = ((A - 2) * C₀) * Real.log n by ring, hAC]; ring
            rw [← hid]; exact hqm
          have hdist : (A - 1) * (q n : ℝ) - (q n : ℝ) = (A - 2) * (q n : ℝ) := by ring
          rw [hPeq, hconst1]
          linarith [hklb, h_a, hmvw', hqm', hdist, hlogn0]
      have hh := tendsto_ofReal_exp_neg hdiv
      refine hh.congr fun n => ?_
      rw [neg_neg]
    have hε2 : Tendsto (fun n => rv n ^ 2 / 8) atTop atTop := by
      apply tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => C₀ * Real.log n / 8) ?_
        ((hlogtend.const_mul_atTop hC₀pos).atTop_div_const (by norm_num))
      filter_upwards [eventually_ge_atTop 1, hqlogev] with n hn hqlogn
      have hrv2 : rv n ^ 2 = (q n : ℝ) := by rw [hrv]; exact Real.sq_sqrt (by positivity)
      rw [hrv2]; linarith
    have hf2 : Tendsto (fun n => ENNReal.ofReal (Real.exp (- rv n ^ 2 / 8))) atTop (𝓝 0) := by
      have hh := tendsto_ofReal_exp_neg hε2
      refine hh.congr fun n => ?_
      rw [neg_div]
    have hsum := hf1.add hf2
    rw [add_zero] at hsum
    exact hsum

end StatLean.Bayesian
