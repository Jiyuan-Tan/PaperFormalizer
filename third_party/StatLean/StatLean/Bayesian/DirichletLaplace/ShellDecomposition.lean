module
public import StatLean.Bayesian.DirichletLaplace.GaussianTests
public import StatLean.Bayesian.DirichletLaplace.CoveringNets
public import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
public import StatLean.Bayesian.DirichletLaplace.TestingBound

@[expose] public section

/-!
# Dirichlet–Laplace posterior contraction — shell/net decomposition (C13)

The geometric decomposition behind BPPD **Theorem 3.1** (§6 assembly). The complement of the
contraction ball `{ ‖θ − θ₀‖ > M r }` is partitioned into *shells* indexed by a δ-support pattern
`S` and a radial index `j`; each shell is covered by a finite `jr/4`-net, and a two-parameter
midpoint test controls the posterior mass of each net piece.

Objects:
* `dlShell θ₀ S j r δ` — the set of `θ` whose δ-support equals `S` and whose distance from `θ₀` lies
  in the `j`-th radial shell `[2jr, 2(j+1)r)` (band floor `2jr`; see the def's D4 note). Each admissible
  `θ` (with bounded δ-support) falls into exactly one shell, so the complement of the ball
  `{‖θ−θ₀‖ ≥ 2Mr}` is `⋃_{S} ⋃_{j ≥ M} dlShell θ₀ S j r δ`.
* `exists_shell_net` — a `jr/4`-net of `dlShell θ₀ S j r δ` of cardinality `≤ 33^{|S|}`
  (`CoveringNets`, volumetric covering of a `|S|`-dimensional ball) whose pieces have radius
  `≤ (√5/4)·jr` (using `√n·δ ≤ r` and `j ≥ 2`).
* `shell_ratio_le` — the per-shell posterior bound assembled from the midpoint tests
  (`GaussianTests`, Type I/II errors `≤ e^{−(d−ρ)²/8}` with margin `d − ρ ≥ (7/8)jr`, whence
  `≤ e^{−j²r²/12}`) and the testing→posterior conversion (`TestingBound`, `CoordinateSplit`).

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Theorem 3.1 (statement p. 7); the shell/test machinery
is the §6 posterior-contraction assembly, in the framework of Ghosal–Ghosh–van der Vaart.

**Proof formalization notes.** The skeleton is *shells → nets → per-piece tests → series*: cover each
shell by its net, test each net piece against `θ₀`, sum the Type I errors over the `≤ 33^{|S|}` pieces
and the Type II errors against the piece prior mass. The outer summation over `(S, j)` is closed in
`PosteriorContraction.lean` (`Nat.choose_le_pow` for the support patterns, `ExpOfRealCalc` for the radial
series).

**Deviations.**
* **D4 (net / test geometry).** The paper's `jr`-net with `2jr`-balls degenerates (a net point may
  coincide with `θ₀`), and a `(jr/2)`-net is inconsistent with a `d/3`-margin test. We use `jr/4`-nets
  (`≤ 33^{|S|}` points), pieces of radius `ρ ≤ (√5/4)jr` (from `√n·δ ≤ r`, `j ≥ 2`), and the
  two-parameter midpoint test `{ y | d(d−ρ)/2 ≤ ⟪y−θ₀, φ−θ₀⟫ }` with both errors `≤ e^{−(d−ρ)²/8}` and
  `d − ρ ≥ (7/8)jr ⇒ ≤ e^{−j²r²/12}`. The non-optimized `(1+β)` testing bound replaces the paper's
  `2√β`, avoiding Neyman–Pearson machinery at no bookkeeping cost.
* **D9 (degenerate index sets).** The `S = ∅` shell is covered by the singleton net `{0}`; handled
  proof-internally, not as a hypothesis.

**Bibliographic comments.** Sieve/net posterior-contraction testing after Ghosal, Ghosh, and van der
Vaart (*Ann. Statist.* 28 (2000), 500–531) and Castillo and van der Vaart (*Ann. Statist.* 40 (2012),
2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Contraction shell** (BPPD §6): the set of `θ` whose δ-support is exactly `S` and whose distance
from `θ₀` lies in the `j`-th radial band `[2jr, 2(j+1)r)`. The complement of the contraction ball is the
disjoint union of these over support patterns `S` and radial indices `j`. Degenerate inputs are not
special-cased in the definition (an empty band or `S` gives the empty shell).

**Formalization note (D4, radial-band factor 2).** The band floor is `2jr`, not the `jr` a literal
reading of the paper's "`jrₙ`-net / `2jrₙ`-balls" text might suggest. With a `jr` floor the two-parameter
midpoint test of `GaussianTests` is *degenerate*: a shell point sits at distance `d ≥ jr − ρ` from `θ₀`
while its covering net-point sits within `ρ = (√5/4)jr` of it, so the usable test margin
`d − ρ ≥ jr − 2ρ = (1 − √5/2)jr < 0` is negative and no consistent test exists. Doubling the floor to
`2jr` restores a positive margin `d − ρ ≥ 2jr − 2ρ = (2 − √5/2)jr ≥ (7/8)jr` (for `j ≥ 2`), which is
exactly what `shell_ratio_le`'s Type I/II error `e^{−j²r²/12}` needs. This is the geometry the paper's
`2jrₙ`-ball language actually intends; only the net *radius* `(√5/4)jr` and error *constant* `1/12`
differ from the paper's unspecified numerals (charter §1 "state the constants that are provable"). The
outer series in `PosteriorContraction` is unaffected: `⋃_{j ≥ M} [2jr, 2(j+1)r) = [2Mr, ∞)` still tiles the
complement of the contraction ball, with the ball radius rescaled by the harmless factor 2. -/
noncomputable def dlShell (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) (j : ℕ) (r δ : ℝ) :
    Set (EuclideanSpace ℝ ι) :=
  {θ | (Finset.univ.filter fun i => δ < |θ i|) = S ∧
       2 * (j : ℝ) * r ≤ ‖θ - θ₀‖ ∧ ‖θ - θ₀‖ < 2 * ((j : ℝ) + 1) * r}

/-! ### Private geometry helpers for `exists_shell_net` (D4) -/

/-- From `a² ≤ b²` and `0 ≤ b`, deduce `a ≤ b`. -/
private lemma le_of_sq_le_sq {a b : ℝ} (h : a ^ 2 ≤ b ^ 2) (hb : 0 ≤ b) : a ≤ b := by
  have habs : |a| ≤ |b| := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt h
  calc a ≤ |a| := le_abs_self a
    _ ≤ |b| := habs
    _ = b := abs_of_nonneg hb

/-- Local copy of `CoordinateSplit.projS_ofLp` (there `private`): the `i`-th coordinate of
`projS S θ` is `θ.ofLp i.val`. -/
private lemma projS_ofLp' (S : Set ι) [DecidablePred (· ∈ S)] (θ : EuclideanSpace ℝ ι)
    (i : {j // j ∈ S}) : (projS S θ).ofLp i = θ.ofLp i.val := rfl

/-- Local copy of `CoordinateSplit.projS_sub` (there `private`): `projS S` respects subtraction. -/
private lemma projS_sub' (S : Set ι) [DecidablePred (· ∈ S)] (a b : EuclideanSpace ℝ ι) :
    projS S (a - b) = projS S a - projS S b := by
  unfold projS
  rw [← WithLp.toLp_sub]
  congr 1

/-- `projS S` is norm-nonincreasing (Pythagoras drops the complementary block). -/
private lemma norm_projS_le (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (x : EuclideanSpace ℝ ι) : ‖projS S x‖ ≤ ‖x‖ := by
  have h := norm_sq_split S x
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  nlinarith [sq_nonneg (‖projS Sᶜ x‖)]

/-- `projS S` recovers the `S`-block of `extendS S u`, which is `u`. -/
private lemma projS_extendS_self (S : Set ι) [DecidablePred (· ∈ S)]
    (u : EuclideanSpace ℝ {j // j ∈ S}) : projS S (extendS S u) = u := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [projS_ofLp']
  unfold extendS
  rw [WithLp.ofLp_toLp, dif_pos i.property]

/-- The complementary block of `extendS S u` is zero. -/
private lemma projS_compl_extendS_self (S : Set ι) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Sᶜ)] (u : EuclideanSpace ℝ {j // j ∈ S}) :
    projS Sᶜ (extendS S u) = 0 := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [projS_ofLp']
  unfold extendS
  have hi : (i : ι) ∉ S := by have hp := i.property; rwa [Set.mem_compl_iff] at hp
  rw [WithLp.ofLp_toLp, dif_neg hi]
  simp

/-- If every coordinate of `θ` inside `T` is `≤ δ` in modulus, then the `T`-block has norm
`≤ √n·δ ≤ r`. (Kept generic over the `Set T` to fix one uniform `Subtype.fintype` instance.) -/
private lemma norm_projS_le_of_coords {T : Set ι} [DecidablePred (· ∈ T)]
    {θ : EuclideanSpace ℝ ι} {δ r : ℝ}
    (hr : 0 < r) (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    (hθ : ∀ i : {x // x ∈ T}, |θ.ofLp i.val| ≤ δ) :
    ‖projS T θ‖ ≤ r := by
  classical
  have hsum : ‖projS T θ‖ ^ 2 ≤ (Fintype.card ι : ℝ) * δ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [projS_ofLp']
    calc ∑ i : {x // x ∈ T}, (θ.ofLp (i : ι)) ^ 2
        ≤ ∑ _i : {x // x ∈ T}, δ ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          nlinarith [sq_abs (θ.ofLp (i : ι)), abs_nonneg (θ.ofLp (i : ι)), hθ i]
      _ = (Fintype.card {x // x ∈ T} : ℝ) * δ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Fintype.card ι : ℝ) * δ ^ 2 := by
          gcongr
          exact_mod_cast Fintype.card_subtype_le _
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := by positivity
  rcases le_or_gt (0 : ℝ) δ with hd | hd
  · have hr2 : (Fintype.card ι : ℝ) * δ ^ 2 ≤ r ^ 2 := by
      have hsd0 : 0 ≤ Real.sqrt (Fintype.card ι : ℝ) * δ := mul_nonneg (Real.sqrt_nonneg _) hd
      calc (Fintype.card ι : ℝ) * δ ^ 2
          = (Real.sqrt (Fintype.card ι : ℝ) * δ) ^ 2 := by rw [mul_pow, Real.sq_sqrt hcard]
        _ ≤ r ^ 2 := by nlinarith [hδ, hsd0, hr.le]
    exact le_of_sq_le_sq (le_trans hsum hr2) hr.le
  · have hempty : IsEmpty {x // x ∈ T} := by
      refine ⟨fun i => ?_⟩
      have := hθ i
      have := abs_nonneg (θ.ofLp (i : ι))
      linarith
    have hz : projS T θ = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero]; exact hr.le

/-- **Shell net** (BPPD §6, D4). Every contraction shell `dlShell θ₀ S j r δ` is covered by a finite
`(√5/4)·jr`-net of cardinality `≤ 33^{|S|}` living in the `|S|`-dimensional support coordinates
(`CoveringNets` volumetric covering + `CoordinateSplit`). The radius `(√5/4)jr` uses `√n·δ ≤ r` and
`j ≥ 2` (D4); the `S = ∅` case is the singleton net `{0}` (D9). -/
theorem exists_shell_net (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — radial index in the tested range; geometry regularity for the (√5/4)jr radius.
    (hj : 2 ≤ j) {r δ : ℝ}
    -- LEAN-ONLY: 0 < r — radial band width; engine-internal.
    (hr : 0 < r)
    -- LEAN-ONLY: √n·δ ≤ r — box-vs-radius control (δ = r/n regime); engine-internal (D4).
    (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r) :
    ∃ net : Finset (EuclideanSpace ℝ ι),
      net.card ≤ 33 ^ S.card ∧
      dlShell θ₀ S j r δ ⊆ ⋃ φ ∈ net, Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) := by
  classical
  set T : Set ι := (↑S : Set ι) with hTdef
  clear_value T
  set R : ℝ := 2 * ((j : ℝ) + 1) * r with hRdef
  set ε : ℝ := (j : ℝ) * r / 4 with hεdef
  have hj2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjr : (0 : ℝ) < (j : ℝ) := by linarith
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεR : ε < R := by rw [hRdef, hεdef]; nlinarith [hjr, hr, mul_pos hjr hr]
  obtain ⟨F₀, hF₀ball, hF₀cover, hF₀card⟩ :=
    exists_finset_net_closedBall (projS T θ₀) R ε hRpos hεpos hεR
  refine ⟨F₀.image (extendS T), ?_, ?_⟩
  · -- Cardinality bound `≤ 33^{|S|}`.
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ {j // j ∈ T}) = S.card := by
      rw [finrank_euclideanSpace, ← Set.toFinset_card, hTdef, Finset.toFinset_coe]
    have hbase : 1 + 2 * R / ε ≤ 33 := by
      have key : 2 * R / ε ≤ 32 := by
        rw [hRdef, hεdef, div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) * r / 4)]
        nlinarith [hj2, hr, mul_pos hjr hr,
          mul_nonneg hr.le (by linarith : (0 : ℝ) ≤ (j : ℝ) - 1)]
      linarith
    have hbnn : (0 : ℝ) ≤ 1 + 2 * R / ε := by positivity
    have hRℝ : ((F₀.image (extendS T)).card : ℝ) ≤ (33 : ℝ) ^ S.card := by
      calc ((F₀.image (extendS T)).card : ℝ)
          ≤ (F₀.card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ (1 + 2 * R / ε) ^ (Module.finrank ℝ (EuclideanSpace ℝ {j // j ∈ T})) := hF₀card
        _ = (1 + 2 * R / ε) ^ S.card := by rw [hfr]
        _ ≤ (33 : ℝ) ^ S.card := by exact pow_le_pow_left₀ hbnn hbase _
    have : ((F₀.image (extendS T)).card : ℝ) ≤ ((33 ^ S.card : ℕ) : ℝ) := by
      rw [Nat.cast_pow]; push_cast; exact hRℝ
    exact_mod_cast this
  · -- Covering: each shell point is within `√5/4·jr` of a lifted net point.
    intro θ hθmem
    obtain ⟨hfilter, hlow, hhigh⟩ := hθmem
    have hθcoord : ∀ i, i ∉ S → |θ.ofLp i| ≤ δ := by
      intro i hi
      have hnotmem : i ∉ Finset.univ.filter (fun k => δ < |θ.ofLp k|) := by rw [hfilter]; exact hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hnotmem
      exact hnotmem
    have hballmem : projS T θ ∈ Metric.closedBall (projS T θ₀) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, ← projS_sub']
      calc ‖projS T (θ - θ₀)‖
          ≤ ‖θ - θ₀‖ := norm_projS_le T (θ - θ₀)
        _ ≤ R := by rw [hRdef]; linarith [hhigh]
    obtain ⟨u, huF₀, hudist⟩ := hF₀cover (projS T θ) hballmem
    refine Set.mem_iUnion₂.mpr ⟨extendS T u, Finset.mem_image_of_mem _ huF₀, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    set c := extendS T u with hcdef
    have hSpart : projS T (θ - c) = projS T θ - u := by
      rw [projS_sub', hcdef, projS_extendS_self]
    have hScpart : projS Tᶜ (θ - c) = projS Tᶜ θ := by
      rw [projS_sub', hcdef, projS_compl_extendS_self, sub_zero]
    have hnormsq : ‖θ - c‖ ^ 2 = ‖projS T θ - u‖ ^ 2 + ‖projS Tᶜ θ‖ ^ 2 := by
      have hsplit := norm_sq_split T (θ - c)
      rw [hSpart, hScpart] at hsplit
      exact hsplit
    have hA : ‖projS T θ - u‖ ≤ ε := by rw [← dist_eq_norm]; exact hudist
    have hB : ‖projS Tᶜ θ‖ ≤ r := by
      refine norm_projS_le_of_coords hr hδ (fun i => ?_)
      have hi : (i : ι) ∉ S := by
        have hp : (i : ι) ∉ T := (Set.mem_compl_iff T _).mp i.property
        set k : ι := (i : ι) with hk
        clear_value k
        rw [hTdef, Finset.mem_coe] at hp
        exact hp
      exact hθcoord i.val hi
    have hA2 : ‖projS T θ - u‖ ^ 2 ≤ ε ^ 2 := by
      nlinarith [hA, norm_nonneg (projS T θ - u), hεpos.le]
    have hB2 : ‖projS Tᶜ θ‖ ^ 2 ≤ r ^ 2 := by
      nlinarith [hB, norm_nonneg (projS Tᶜ θ), hr.le]
    have hbnd : ‖θ - c‖ ^ 2 ≤ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2 := by
      have hεsq : ε ^ 2 = (j : ℝ) ^ 2 * r ^ 2 / 16 := by rw [hεdef]; ring
      have h5 : (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2 = 5 / 16 * ((j : ℝ) ^ 2 * r ^ 2) := by
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; ring
      rw [hnormsq, h5]
      have hj4 : (4 : ℝ) ≤ (j : ℝ) ^ 2 := by nlinarith [hj2]
      nlinarith [hA2, hB2, hεsq, hr, hj4, sq_nonneg r, mul_le_mul_of_nonneg_right hj4 (sq_nonneg r)]
    exact le_of_sq_le_sq hbnd (by positivity)

/-- **Per-shell posterior bound** (BPPD §6, D4). The `E_{θ₀}`-mean of the un-normalized posterior
ratio for a single shell is bounded by the sum over its `≤ 33^{|S|}` net pieces of the Type I test
error `e^{−j²r²/12}`, plus the shell prior mass weighted by the Type II error over the denominator
threshold `dbar`. Assembled from `GaussianTests` (the midpoint tests) and `TestingBound`. -/
theorem shell_ratio_le (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — tested radial range (margin d − ρ ≥ (7/8)jr needs j ≥ 2); engine-internal.
    (hj : 2 ≤ j) {a r δ : ℝ}
    -- LEAN-ONLY: 0 < a, 0 < r — DL scale and band width; engine-internal.
    (ha : 0 < a) (hr : 0 < r)
    -- LEAN-ONLY: √n·δ ≤ r — piece-radius control (D4); engine-internal.
    (hδ : Real.sqrt (Fintype.card ι : ℝ) * δ ≤ r)
    -- LEAN-ONLY: 0 < dbar — denominator lower threshold from `DenominatorLowerBound`; engine-internal.
    (dbar : ℝ≥0∞) (hdbar : 0 < dbar) :
    ∫⁻ y in {y | dbar ≤ dlDenom θ₀ (dlPrior a ι) y},
        dlNumer θ₀ (dlPrior a ι) (dlShell θ₀ S j r δ) y / dlDenom θ₀ (dlPrior a ι) y
        ∂(gaussShiftKernel ι θ₀)
      ≤ (33 : ℝ≥0∞) ^ S.card * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12))
          + (dlPrior a ι) (dlShell θ₀ S j r δ)
              * ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) / dbar := by
  -- PROOF RECIPE (now provable: `dlShell` band floor raised to `2jr`, ceiling to `2(j+1)r`, D4).
  --
  -- 1. `exists_shell_net θ₀ S hj hr hδ` gives a Finset `net`, `net.card ≤ 33^{|S|}`, with
  --      `dlShell θ₀ S j r δ ⊆ ⋃ φ ∈ net, closedBall φ ρ`,  `ρ := (√5/4)·jr`.
  -- 2. Disjointify: intersect each `closedBall φ ρ` with the shell and subtract predecessors to get a
  --    Finset-indexed DISJOINT family `P φ ⊆ closedBall φ ρ ∩ shell` with `⋃ P φ = shell`. Then
  --      `dlNumer θ₀ · (shell) = ∑ φ, dlNumer θ₀ · (P φ)`  (numer is a measure; `measure_biUnion_finset`)
  --      `dlPrior a ι shell    = ∑ φ, dlPrior a ι (P φ)`   (same).
  -- 3. Fix `φ` with `P φ ≠ ∅`; pick `θ✶ ∈ P φ ⊆ shell`, so `‖θ✶ − θ₀‖ ≥ 2jr` and `‖θ✶ − φ‖ ≤ ρ`, giving
  --      `d := ‖φ − θ₀‖ ≥ 2jr − ρ`  ⇒  margin  `d − ρ ≥ 2jr − 2ρ = (2 − √5/2)jr ≥ (7/8)jr > 0`  (j ≥ 2).
  -- 4. `measure_dlTestSet_typeI`/`_typeII` (GaussianTests, hypothesis `ρ < d` now holds) bound both errors
  --    by `exp(−(d−ρ)²/8) ≤ exp(−(7/8·jr)²/8) ≤ exp(−j²r²/12)`  (since (7/8)²/8 = 49/512 ≥ 1/12).
  -- 5. `lintegral_ratio_on_event_le_test` (TestingBound) on the event `{dbar ≤ dlDenom}` with test set
  --    `dlTestSet θ₀ φ ρ`, dominating measure `dbar`:
  --      `∫_{D≥dbar} dlNumer θ₀ · (P φ)/dlDenom ≤ (K θ₀)(test) + dlPrior a ι (P φ)·sup_θ (K θ)(testᶜ)/dbar`
  --                                            `≤ exp(−j²r²/12) + dlPrior a ι (P φ)·exp(−j²r²/12)/dbar`.
  -- 6. Sum over `φ ∈ net` (`Finset.sum_le_sum` + `ENNReal.sum_div`): the first term sums to
  --    `net.card · exp ≤ 33^{|S|}·exp`; the second, using `∑ φ, dlPrior a ι (P φ) = dlPrior a ι shell`
  --    (step 2, disjoint & exact — this is why disjointification, not the raw cover, is needed), sums to
  --    `dlPrior a ι shell · exp / dbar`.  ∎
  --
  -- Final error constant: `c = 1/12` (the frozen value; `(7/8)²/8 = 49/512 ≥ 1/12`). `exists_shell_net`
  -- was used unchanged (its statement and proof were not touched).
  classical
  obtain ⟨net, hcard, hcover⟩ := exists_shell_net θ₀ S hj hr hδ
  set π := dlPrior a ι with hπdef
  haveI hπprob : IsProbabilityMeasure π := by rw [hπdef]; infer_instance
  haveI : SFinite π := inferInstance
  set shell := dlShell θ₀ S j r δ with hshelldef
  set ρ : ℝ := Real.sqrt 5 / 4 * ((j : ℝ) * r) with hρdef
  set b : ℝ≥0∞ := ENNReal.ofReal (Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12)) with hbdef
  set E : Set (EuclideanSpace ℝ ι) := {y | dbar ≤ dlDenom θ₀ π y} with hEdef
  have hdbar_ne : dbar ≠ 0 := hdbar.ne'
  -- Measurability of numerator/denominator in the data `y` (local copies).
  have hnum_meas : ∀ (C : Set (EuclideanSpace ℝ ι)), Measurable (fun y => dlNumer θ₀ π C y) := by
    intro C
    have huc : Measurable (Function.uncurry (fun (y θ : EuclideanSpace ℝ ι) => dlLR θ₀ θ y)) := by
      unfold Function.uncurry dlLR; fun_prop
    show Measurable (fun y => ∫⁻ θ, dlLR θ₀ θ y ∂(π.restrict C))
    exact huc.lintegral_prod_right
  have hden_meas : Measurable (fun y => dlDenom θ₀ π y) := by
    have hEq : (fun y => dlDenom θ₀ π y) = (fun y => dlNumer θ₀ π Set.univ y) := by
      funext y; rw [dlDenom]
    rw [hEq]; exact hnum_meas Set.univ
  -- Measurability of the shell.
  have hshell_meas : MeasurableSet shell := by
    rw [hshelldef]
    have hcoord : ∀ i, Measurable (fun θ : EuclideanSpace ℝ ι => θ i) := fun i =>
      (measurable_pi_apply i).comp ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).measurable
    have hnormc : Continuous (fun θ : EuclideanSpace ℝ ι => ‖θ - θ₀‖) := by fun_prop
    have h2 : MeasurableSet {θ : EuclideanSpace ℝ ι | 2 * (j : ℝ) * r ≤ ‖θ - θ₀‖} :=
      measurableSet_le measurable_const hnormc.measurable
    have h3 : MeasurableSet {θ : EuclideanSpace ℝ ι | ‖θ - θ₀‖ < 2 * ((j : ℝ) + 1) * r} :=
      measurableSet_lt hnormc.measurable measurable_const
    have h1 : MeasurableSet
        {θ : EuclideanSpace ℝ ι | (Finset.univ.filter fun i => δ < |θ i|) = S} := by
      have hset : {θ : EuclideanSpace ℝ ι | (Finset.univ.filter fun i => δ < |θ i|) = S}
          = ⋂ i, {θ : EuclideanSpace ℝ ι | (δ < |θ i|) ↔ i ∈ S} := by
        ext θ
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, Finset.mem_filter,
          Finset.mem_univ, true_and]
      rw [hset]
      refine MeasurableSet.iInter (fun i => ?_)
      by_cases hiS : i ∈ S
      · have hrw : {θ : EuclideanSpace ℝ ι | (δ < |θ i|) ↔ i ∈ S}
            = {θ : EuclideanSpace ℝ ι | δ < |θ i|} := by
          ext θ; simp only [Set.mem_setOf_eq, hiS, iff_true]
        rw [hrw]; exact measurableSet_lt measurable_const (hcoord i).abs
      · have hrw : {θ : EuclideanSpace ℝ ι | (δ < |θ i|) ↔ i ∈ S}
            = {θ : EuclideanSpace ℝ ι | ¬ (δ < |θ i|)} := by
          ext θ; simp only [Set.mem_setOf_eq, hiS, iff_false]
        rw [hrw]; exact (measurableSet_lt measurable_const (hcoord i).abs).compl
    have hinter : (dlShell θ₀ S j r δ)
        = {θ : EuclideanSpace ℝ ι | (Finset.univ.filter fun i => δ < |θ i|) = S}
          ∩ {θ | 2 * (j : ℝ) * r ≤ ‖θ - θ₀‖} ∩ {θ | ‖θ - θ₀‖ < 2 * ((j : ℝ) + 1) * r} := by
      ext θ; simp only [dlShell, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [hinter]; exact (h1.inter h2).inter h3
  -- Enumeration of the net and the covering pieces.
  set enum : Fin net.card → EuclideanSpace ℝ ι :=
    fun m => (↑(net.equivFin.symm m) : EuclideanSpace ℝ ι) with henumdef
  set B : ℕ → Set (EuclideanSpace ℝ ι) :=
    fun k => if h : k < net.card then Metric.closedBall (enum ⟨k, h⟩) ρ ∩ shell else ∅ with hBdef
  have hB_meas : ∀ k, MeasurableSet (B k) := by
    intro k
    by_cases hk : k < net.card
    · rw [show B k = Metric.closedBall (enum ⟨k, hk⟩) ρ ∩ shell from by
        simp only [hBdef, dif_pos hk]]
      exact measurableSet_closedBall.inter hshell_meas
    · rw [show B k = (∅ : Set (EuclideanSpace ℝ ι)) from by simp only [hBdef, dif_neg hk]]
      exact MeasurableSet.empty
  -- Disjointified pieces.
  set P : ℕ → Set (EuclideanSpace ℝ ι) := disjointed B with hPdef
  have hP_meas : ∀ k, MeasurableSet (P k) := fun k => MeasurableSet.disjointed hB_meas k
  have hP_sub : ∀ k, P k ⊆ B k := fun k => disjointed_subset B k
  have hP_disj := disjoint_disjointed B
  have hP_pwd : (↑(Finset.range net.card) : Set ℕ).PairwiseDisjoint P := hP_disj.set_pairwise _
  have hP_union : (⋃ k, P k) = ⋃ k, B k := iUnion_disjointed
  have hPk_empty : ∀ k, net.card ≤ k → P k = ∅ := by
    intro k hk
    have hBk : B k = ∅ := by simp only [hBdef, dif_neg (not_lt.mpr hk)]
    exact Set.eq_empty_of_subset_empty (hBk ▸ hP_sub k)
  -- `⋃ k, B k = shell` (the cover, intersected with the shell).
  have hBunion : (⋃ k, B k) = shell := by
    apply le_antisymm
    · refine Set.iUnion_subset (fun k => ?_)
      by_cases hk : k < net.card
      · rw [show B k = Metric.closedBall (enum ⟨k, hk⟩) ρ ∩ shell from by
          simp only [hBdef, dif_pos hk]]
        exact Set.inter_subset_right
      · rw [show B k = (∅ : Set (EuclideanSpace ℝ ι)) from by simp only [hBdef, dif_neg hk]]
        exact Set.empty_subset _
    · intro x hx
      obtain ⟨ψ, hψ, hxψ⟩ := Set.mem_iUnion₂.mp (hcover hx)
      have hlt : ((net.equivFin ⟨ψ, hψ⟩ : Fin net.card) : ℕ) < net.card :=
        (net.equivFin ⟨ψ, hψ⟩).isLt
      refine Set.mem_iUnion.mpr ⟨(net.equivFin ⟨ψ, hψ⟩ : ℕ), ?_⟩
      have hBk : B (net.equivFin ⟨ψ, hψ⟩ : ℕ)
          = Metric.closedBall (enum ⟨(net.equivFin ⟨ψ, hψ⟩ : ℕ), hlt⟩) ρ ∩ shell := by
        simp only [hBdef, dif_pos hlt]
      have henumeq : enum ⟨(net.equivFin ⟨ψ, hψ⟩ : ℕ), hlt⟩ = ψ := by
        have hfe : (⟨(net.equivFin ⟨ψ, hψ⟩ : ℕ), hlt⟩ : Fin net.card) = net.equivFin ⟨ψ, hψ⟩ :=
          Fin.ext rfl
        simp only [henumdef, hfe, Equiv.symm_apply_apply]
      rw [hBk, henumeq]
      exact ⟨hxψ, hx⟩
  -- The finset-indexed disjoint union over `range net.card` also equals the shell.
  have hPfin_union : (⋃ k ∈ Finset.range net.card, P k) = shell := by
    rw [← hBunion, ← hP_union]
    ext x
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨k, _, hxk⟩; exact ⟨k, hxk⟩
    · rintro ⟨k, hxk⟩
      by_cases hk : k < net.card
      · exact ⟨k, hk, hxk⟩
      · rw [hPk_empty k (not_lt.mp hk)] at hxk; exact hxk.elim
  -- `dlNumer θ₀ π C y` as the withDensity measure of `C`.
  have hν_eq : ∀ (y : EuclideanSpace ℝ ι) (C : Set (EuclideanSpace ℝ ι)), MeasurableSet C →
      dlNumer θ₀ π C y = (π.withDensity (fun θ => dlLR θ₀ θ y)) C := by
    intro y C hC
    rw [withDensity_apply _ hC]; rfl
  -- Numerator and prior are additive over the disjoint pieces (exact equalities).
  have hnumer_sum : ∀ y, dlNumer θ₀ π shell y
      = ∑ k ∈ Finset.range net.card, dlNumer θ₀ π (P k) y := by
    intro y
    rw [hν_eq y shell hshell_meas, ← hPfin_union,
      measure_biUnion_finset hP_pwd (fun k _ => hP_meas k)]
    exact Finset.sum_congr rfl (fun k _ => (hν_eq y (P k) (hP_meas k)).symm)
  have hprior_sum : π shell = ∑ k ∈ Finset.range net.card, π (P k) := by
    rw [← hPfin_union, measure_biUnion_finset hP_pwd (fun k _ => hP_meas k)]
  have hdiv_sum : ∀ y, dlNumer θ₀ π shell y / dlDenom θ₀ π y
      = ∑ k ∈ Finset.range net.card, dlNumer θ₀ π (P k) y / dlDenom θ₀ π y := by
    intro y
    rw [hnumer_sum y]
    simp only [div_eq_mul_inv, Finset.sum_mul]
  have hsum2 : ∑ k ∈ Finset.range net.card, π (P k) * b / dbar = π shell * b / dbar := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← hprior_sum]
  have hcard_le : (net.card : ℝ≥0∞) ≤ (33 : ℝ≥0∞) ^ S.card := by exact_mod_cast hcard
  -- Global geometry facts (independent of the piece).
  have hjpos : (0 : ℝ) < (j : ℝ) := by
    have : 0 < j := by omega
    exact_mod_cast this
  have hjrpos : (0 : ℝ) < (j : ℝ) * r := mul_pos hjpos hr
  have hρ0 : 0 ≤ ρ := by
    rw [hρdef]; exact mul_nonneg (by positivity) hjrpos.le
  have h78pos : (0 : ℝ) < 7 / 8 * ((j : ℝ) * r) := mul_pos (by norm_num) hjrpos
  have hsqrt5 : Real.sqrt 5 ≤ 9 / 4 := by
    rw [show (9 / 4 : ℝ) = Real.sqrt ((9 / 4) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  -- Per-piece posterior bound.
  have hk_all : ∀ k ∈ Finset.range net.card,
      ∫⁻ y in E, dlNumer θ₀ π (P k) y / dlDenom θ₀ π y ∂(gaussShiftKernel ι θ₀)
        ≤ b + π (P k) * b / dbar := by
    intro k hk
    rcases eq_or_ne (P k) ∅ with hPk | hPk
    · -- Empty piece: the ratio integrand is identically zero.
      have hzero : (fun y => dlNumer θ₀ π (P k) y / dlDenom θ₀ π y)
          = fun _ => (0 : ℝ≥0∞) := by
        funext y; simp [dlNumer, hPk]
      rw [hzero, lintegral_zero]
      exact zero_le
    · -- Nonempty piece: test the true parameter against the net point `enum ⟨k, _⟩`.
      have hk_lt : k < net.card := Finset.mem_range.mp hk
      have hBk : B k = Metric.closedBall (enum ⟨k, hk_lt⟩) ρ ∩ shell := by
        simp only [hBdef, dif_pos hk_lt]
      obtain ⟨θs, hθs⟩ := Set.nonempty_iff_ne_empty.mpr hPk
      have hθsB : θs ∈ Metric.closedBall (enum ⟨k, hk_lt⟩) ρ ∩ shell := hBk ▸ hP_sub k hθs
      have hθs_ball : ‖θs - enum ⟨k, hk_lt⟩‖ ≤ ρ := by
        have h := hθsB.1; rwa [Metric.mem_closedBall, dist_eq_norm] at h
      have hmem : (Finset.univ.filter fun i => δ < |θs i|) = S
          ∧ 2 * (j : ℝ) * r ≤ ‖θs - θ₀‖ ∧ ‖θs - θ₀‖ < 2 * ((j : ℝ) + 1) * r := hθsB.2
      have hθs_shell : 2 * (j : ℝ) * r ≤ ‖θs - θ₀‖ := hmem.2.1
      have htri : ‖θs - θ₀‖ ≤ ‖θs - enum ⟨k, hk_lt⟩‖ + ‖enum ⟨k, hk_lt⟩ - θ₀‖ := by
        have h := dist_triangle θs (enum ⟨k, hk_lt⟩) θ₀
        simpa [dist_eq_norm] using h
      have hd_lb : 2 * (j : ℝ) * r - ρ ≤ ‖enum ⟨k, hk_lt⟩ - θ₀‖ := by
        linarith [htri, hθs_shell, hθs_ball]
      -- Positive test margin `d − ρ ≥ (7/8) j r` (uses `√5 ≤ 9/4` and `j ≥ 2`).
      have hmargin : 7 / 8 * ((j : ℝ) * r) ≤ ‖enum ⟨k, hk_lt⟩ - θ₀‖ - ρ := by
        have hprod : (0 : ℝ) ≤ (9 / 4 - Real.sqrt 5) * ((j : ℝ) * r) :=
          mul_nonneg (by linarith [hsqrt5]) hjrpos.le
        nlinarith [hd_lb, hprod, hρdef]
      have hρd : ρ < ‖enum ⟨k, hk_lt⟩ - θ₀‖ := by linarith [hmargin, h78pos]
      -- The two test errors both dominate `b = exp(−j²r²/12)`.
      have hexp_le : Real.exp (-((‖enum ⟨k, hk_lt⟩ - θ₀‖ - ρ) ^ 2 / 8))
          ≤ Real.exp (- (j : ℝ) ^ 2 * r ^ 2 / 12) := by
        apply Real.exp_le_exp.mpr
        have hMnn : (0 : ℝ) ≤ ‖enum ⟨k, hk_lt⟩ - θ₀‖ - ρ := le_trans h78pos.le hmargin
        have hsq : (7 / 8 * ((j : ℝ) * r)) * (7 / 8 * ((j : ℝ) * r))
            ≤ (‖enum ⟨k, hk_lt⟩ - θ₀‖ - ρ) * (‖enum ⟨k, hk_lt⟩ - θ₀‖ - ρ) :=
          mul_le_mul hmargin hmargin h78pos.le hMnn
        nlinarith [hsq, sq_nonneg ((j : ℝ) * r)]
      have hI : gaussShiftKernel ι θ₀ (dlTestSet θ₀ (enum ⟨k, hk_lt⟩) ρ) ≤ b :=
        (measure_dlTestSet_le θ₀ (enum ⟨k, hk_lt⟩) hρ0 hρd).trans
          (ENNReal.ofReal_le_ofReal hexp_le)
      have hbtest : ∀ θ ∈ P k, gaussShiftKernel ι θ (dlTestSet θ₀ (enum ⟨k, hk_lt⟩) ρ)ᶜ ≤ b := by
        intro θ hθ
        have hθB : θ ∈ Metric.closedBall (enum ⟨k, hk_lt⟩) ρ ∩ shell := hBk ▸ hP_sub k hθ
        have hθφ : ‖θ - enum ⟨k, hk_lt⟩‖ ≤ ρ := by
          have h := hθB.1; rwa [Metric.mem_closedBall, dist_eq_norm] at h
        exact (measure_compl_dlTestSet_le θ₀ (enum ⟨k, hk_lt⟩) θ hρ0 hρd hθφ).trans
          (ENNReal.ofReal_le_ofReal hexp_le)
      have hkbound := lintegral_ratio_on_event_le_test' θ₀ π (hP_meas k)
        (measurableSet_dlTestSet θ₀ (enum ⟨k, hk_lt⟩) ρ) hdbar_ne hbtest
      exact le_trans hkbound (add_le_add hI (le_refl _))
  -- Sum the per-piece bounds.
  simp_rw [hdiv_sum]
  rw [lintegral_finset_sum _ (fun k _ => (hnum_meas (P k)).fun_div hden_meas)]
  refine le_trans (Finset.sum_le_sum hk_all) ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum2]
  exact add_le_add (mul_le_mul_left hcard_le b) (le_refl _)

end StatLean.Bayesian
