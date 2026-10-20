module
public import StatLean.Bayesian.DirichletLaplace.PriorDensityBounds
public import StatLean.Bayesian.DirichletLaplace.PriorSmallBall
public import StatLean.Bayesian.DirichletLaplace.CoordinateSplit
public import StatLean.Bayesian.ForMathlib.GammaBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Dirichlet–Laplace posterior contraction — prior mass ratio (C14, BPPD Lemma 6.1)

The prior-mass bookkeeping behind BPPD **Theorem 3.1** (§6). To convert the per-shell test bounds
(`ShellDecomposition.lean`) into a summable series we need, for each net piece, the ratio

`β_{S,j} = Π(net piece ∩ { ∀ i ∈ S, |θᵢ| > δ }) / Π(B(θ₀, r))`

of piece mass to the mass of the contraction ball around the truth (BPPD Lemma 6.1). This file gives
the single consumer-facing bound `dlBetaRatio_le` on that ratio.

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*,
JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Lemma 6.1 (p. 15); Lemma 3.2 (density bounds (13)/(14),
p. 8).

## Formalization notes — corrected statement (D10, D11) and what the paper elides

The stub for this file originally carried FOUR lemmas, two of which (`dlPrior_ball_near_ge`,
`dlPrior_fullBall_near_truth_ge`) were **false as stated** and have been removed; a third
(`dlPrior_piece_le`) was an awkward intermediate folded into the proof of `dlBetaRatio_le`. The reasons,
and the corrected route, are the substance of this milestone:

* **D10 (no absolute lower bound on `Π(B(θ₀,r))`; the ratio is what matters).** The removed
  `dlPrior_fullBall_near_truth_ge` claimed `Π(B(θ₀,r)) ≥ exp(−E)` with `E` free of any `r → 0` blow-up
  term. That is false: `dlPrior` is atomless, so `Π(B(θ₀,r)) → 0` as `r → 0` while `exp(−E)` is a fixed
  positive constant (take `S = ∅`, forcing `θ₀ = 0`: the claim becomes `exp(−r²) ≤ Π(B(0,r))`, false for
  small `r`). It was believed to feed the denominator threshold `dbar`, but the assembly (`PosteriorContraction`)
  never needs an *absolute* denominator bound: with `dbar = e^{−r²}·Π(B(θ₀,r))` the shell contribution
  `Π(shell)·e^{−j²r²/12}/dbar = [Π(shell)/Π(B(θ₀,r))]·e^{−j²r²/12}·e^{r²}` has `Π(B(θ₀,r))` **cancel**
  into the ratio `β`. Only `dlBetaRatio_le` (a genuine `Π/Π`, with `r` cancelling) is consumed — no
  absolute ball-mass bound exists or is needed. Likewise the removed `dlPrior_ball_near_ge` (a
  centered-vs-offset ball comparison) was false for the same atomless/spike reason and unused.

* **D11 (the exponent depends on `‖θ₀‖`; the paper's Lemma 6.1 hides it in a constant).** The stub's
  exponent `|S|log(64j) + C(|S|+n)log n + C'r²` **omits any dependence on the truth `θ₀`**, which is
  incorrect: the denominator ball `B(θ₀,r)` charges less mass the larger `‖θ₀‖` is (the DL density
  decays like `exp(−(7/2)Σ√|θᵢ|)`, Lemma 3.2(14)), so `β` genuinely grows with `‖θ₀‖`. The honest
  exponent (below) carries a `|S|^{3/4}√‖θ₀‖` term. It is harmless in the assembly precisely because of
  Theorem 3.1's hypothesis `‖θ₀‖² ≤ q log⁴n`: then `|S|^{3/4}√‖θ₀‖ ≤ (A'q)^{3/4}(q log⁴n)^{1/4} =
  O(q log n) = O(r²)`, dominated by the shell decay. This is the role of `hnorm` in the paper's proof,
  left implicit there.

**Corrected route (block factorization, volume cancellation).** `β = Π(piece)/Π(B(θ₀,r))`. Factor both
over the support block `S` and its complement `Sᶜ` (`CoordinateSplit`), using
`B(θ₀,r) ⊇ B_S(θ₀_S, r/√2) × B_{Sᶜ}(0, r/√2)`:
* **`S`-block (|S| dims):** numerator `≤ (17aδ^{a−1})^{|S|}·vol_S(B_ρ)` (density upper on `{δ<|θ|}`,
  `PriorDensityBounds`), denominator `≥ exp(−[|S|log(1/a)+C|S|+(7/2)Σ√|θᵢ|])·vol_S(B_{r/√2})`
  (density lower, Lemma 3.2(14)). The Euclidean ball volumes share the `Γ(|S|/2+1)` factor, which
  **cancels**, leaving the radius ratio `(√2ρ/r)^{|S|} = (√10/4·j)^{|S|}`. The `a`-powers cancel
  (`17a·(1/a) = 17`). `Σ_{i∈S}√|θᵢ|` over the ball is controlled by Cauchy–Schwarz twice:
  `Σ√|θᵢ| ≤ |S|^{3/4}(‖θ₀‖+r)^{1/2} ≤ |S|^{3/4}(√‖θ₀‖+√r)` — the `√r` piece is `|S|^{3/4}√r = o(r²)`.
* **`Sᶜ`-block (card ι − |S| dims):** numerator `≤ 1` (probability), denominator
  `≥ exp(−2(card ι)w)` (`PriorSmallBall.dlPrior_ball_zero_ge` on the `Sᶜ` subtype), `w` a tail bound at
  the clamped radius. Under `a = n^{−(1+β)}` this term `→ 0`.

**Constants deviate from the paper (charter §1).** The radius-ratio constant is stated as `512` (roomy
for `√10/4·17·e^C`); the `4, 4, 2` multipliers are generous placeholders. A closure session **may
adjust these numerals and the precise form of the lower-order terms** to whatever the block bounds
actually deliver, provided the exponent keeps the shape `|S|·log(c·j) + (terms that PosteriorContraction bounds by
O(r²) or o(r²) or →0 under a=n^{−(1+β)}, δ≥n^{−2}, ‖θ₀‖²≤q log⁴n)`; report the final exponent so the
`PosteriorContraction` assembly can sum it.

**Deviations (density bounds).** D5 (P4 exponent `−(3/√2)√|x|`, absorbed by the `4·|S|^{3/4}√‖θ₀‖`
slack); D8 (`a ≤ 1/2` for the density upper bound, `a ≤ 1` for the lower — both carried, discharged
`aₙ → 0` in the assembly).

**Bibliographic comments.** Prior-mass / small-ball bookkeeping in the posterior-contraction program
of Ghosal, Ghosh, and van der Vaart (*Ann. Statist.* 28 (2000), 500–531) and Castillo and van der
Vaart (*Ann. Statist.* 40 (2012), 2069–2101).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- `projS` respects subtraction (local copy of the private `CoordinateSplit.projS_sub`). -/
private lemma projS_sub' (S : Set ι) [DecidablePred (· ∈ S)]
    (a b : EuclideanSpace ℝ ι) : projS S (a - b) = projS S a - projS S b := by
  unfold projS
  rw [← WithLp.toLp_sub]
  congr 1

/-- Coordinate restriction is norm-nonexpansive (from `norm_sq_split` / Pythagoras). -/
private lemma norm_projS_le (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ : EuclideanSpace ℝ ι) : ‖projS S θ‖ ≤ ‖θ‖ := by
  have h := norm_sq_split S θ
  have h2 : ‖projS S θ‖ ^ 2 ≤ ‖θ‖ ^ 2 := by nlinarith [sq_nonneg ‖projS Sᶜ θ‖]
  have := Real.sqrt_le_sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- A single Euclidean coordinate is measurable. -/
private lemma measurable_coord' {κ : Type*} [Fintype κ] (i : κ) :
    Measurable (fun u : EuclideanSpace ℝ κ => u i) :=
  (measurable_pi_apply i).comp (MeasurableEquiv.toLp 2 (κ → ℝ)).symm.measurable

/-- The δ-support cylinder `{ u | ∀ i, δ < |uᵢ| }` is measurable. -/
private lemma measurableSet_all_lt_abs {κ : Type*} [Fintype κ] (δ : ℝ) :
    MeasurableSet {u : EuclideanSpace ℝ κ | ∀ i, δ < |u i|} := by
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_lt measurable_const (measurable_coord' i).abs

/-- Subadditivity of `√`: `√(x+y) ≤ √x + √y` for `x, y ≥ 0`. -/
private lemma real_sqrt_add_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [show Real.sqrt x + Real.sqrt y = Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  rw [add_sq, Real.sq_sqrt hx, Real.sq_sqrt hy]
  nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

-- The nested log/exp/rpow algebra plus the several `nlinarith` calls exceed the default budget.
set_option maxHeartbeats 1000000 in
/-- **The core real-analysis inequality** behind `dlBetaRatio_le` (block-ratio, `Γ`-volumes cancelled).
`t` stands for `‖θ₀‖`, `d = |S|`, `n = card ι`. The `S`-block numerator constant
`(17·a·δ^{a−1})^d` times the net radius `(√5/4·jr)^d` is dominated by the density-lower constant
`(a/64)^d·exp(−3d−(7/2)·(d^{3/4}(√t+√r)))` times the denominator radius `(r/√2)^d` times the
`exp`-exponent; the `a`- and `r`-powers and the `Γ(d/2+1)` ball volume (elided) all cancel. -/
private lemma massRatio_real_ineq {a δ r t w : ℝ} {d n j : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hj : 2 ≤ j) :
    (17 * a * δ ^ (a - 1)) ^ d * (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d
      ≤ Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ)) + (d : ℝ) * Real.log (1 / δ)
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
            + 2 * (n : ℝ) * w)
          * ((a / 64) ^ d * Real.exp (-3 * (d : ℝ)
              - 7 / 2 * ((d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t
                        + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r)))
          * (r / Real.sqrt 2) ^ d * Real.exp (-2 * (n : ℝ) * w) := by
  have hjR : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hδpow : (0 : ℝ) < δ ^ (a - 1) := Real.rpow_pos_of_pos hδ _
  have hu0 : 0 ≤ (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t := by positivity
  have hv0 : 0 ≤ (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r := by positivity
  -- The collapsed base of the `d`-th power ratio.
  set CP : ℝ := 1088 * Real.sqrt 5 * Real.sqrt 2 / 4 with hCP
  have hCPpos : 0 < CP := by positivity
  set P : ℝ := CP * (j : ℝ) * δ ^ (a - 1) with hP
  have hPpos : 0 < P := by positivity
  -- Base identity: `(17aδ^{a-1})·(√5/4·jr) = P·((a/64)·(r/√2))`.
  have hbase : (17 * a * δ ^ (a - 1)) * (Real.sqrt 5 / 4 * ((j : ℝ) * r))
      = P * ((a / 64) * (r / Real.sqrt 2)) := by
    rw [hP, hCP]
    field_simp
    ring
  -- Rewrite the LHS as `P^d · ((a/64)^d · (r/√2)^d)`.
  have hLHS : (17 * a * δ ^ (a - 1)) ^ d * (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d
      = P ^ d * ((a / 64) ^ d * (r / Real.sqrt 2) ^ d) := by
    rw [← mul_pow, hbase, mul_pow P ((a / 64) * (r / Real.sqrt 2)) d,
      mul_pow (a / 64) (r / Real.sqrt 2) d]
  -- `log P = d·(log CP + log j + (a-1)·log δ)`.
  have hlogP : Real.log P = Real.log CP + Real.log (j : ℝ) + (a - 1) * Real.log δ := by
    rw [hP, Real.log_mul (by positivity) hδpow.ne', Real.log_mul hCPpos.ne' hjpos.ne',
      Real.log_rpow hδ]
  -- Numeric: `CP·e³ ≤ 20000`.
  have h5 : Real.sqrt 5 ≤ 2.24 := by
    rw [show (2.24 : ℝ) = Real.sqrt (2.24 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ≤ 1.42 := by
    rw [show (1.42 : ℝ) = Real.sqrt (1.42 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hexp1 : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have he3 : Real.exp 3 = Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have he : Real.exp 3 ≤ 20.2 := by
    rw [he3]
    calc Real.exp 1 * (Real.exp 1 * Real.exp 1) ≤ 2.72 * (2.72 * 2.72) := by gcongr
      _ ≤ 20.2 := by norm_num
  have hCPe : CP * Real.exp 3 ≤ 20000 := by
    have h52 : Real.sqrt 5 * Real.sqrt 2 ≤ 2.24 * 1.42 :=
      mul_le_mul h5 h2 (Real.sqrt_nonneg 2) (by norm_num)
    rw [hCP]
    nlinarith [h52, he, Real.exp_pos (3 : ℝ), mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 2)]
  -- Sub-bound A: `d·log CP + d·log j + 3d ≤ d·log(20000 j)`.
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hA : (d : ℝ) * Real.log CP + (d : ℝ) * Real.log (j : ℝ) + 3 * (d : ℝ)
      ≤ (d : ℝ) * Real.log (20000 * (j : ℝ)) := by
    have hcp3 : Real.log CP + 3 ≤ Real.log 20000 := by
      have h3 : (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
      rw [h3, ← Real.log_mul hCPpos.ne' (Real.exp_pos 3).ne']
      exact Real.log_le_log (by positivity) hCPe
    have hinner : Real.log CP + Real.log (j : ℝ) + 3 ≤ Real.log (20000 * (j : ℝ)) := by
      rw [Real.log_mul (by norm_num) hjpos.ne']; linarith
    nlinarith [mul_le_mul_of_nonneg_left hinner hd0]
  -- Sub-bound B: `d·(a-1)·log δ ≤ d·log(1/δ)`.
  have hB : (d : ℝ) * ((a - 1) * Real.log δ) ≤ (d : ℝ) * Real.log (1 / δ) := by
    have hloginv : Real.log (1 / δ) = - Real.log δ := by
      rw [one_div, Real.log_inv]
    have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos (by linarith) hδ1
    rw [hloginv]
    nlinarith [mul_nonneg (mul_nonneg hd0 ha.le) (neg_nonneg.2 hlogδ)]
  -- Assemble `P^d ≤ exp G`, with `G` the collapsed exponent.
  have hPd : P ^ d ≤ Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ)) + (d : ℝ) * Real.log (1 / δ)
        + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
        + 2 * (n : ℝ) * w
      - 3 * (d : ℝ) - 7 / 2 * ((d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t
                              + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r) - 2 * (n : ℝ) * w) := by
    rw [← Real.log_le_iff_le_exp (by positivity), Real.log_pow, hlogP]
    nlinarith [hA, hB, hu0, hv0, hd0]
  -- Combine.
  have hQpos : (0 : ℝ) ≤ (a / 64) ^ d * (r / Real.sqrt 2) ^ d := by positivity
  calc (17 * a * δ ^ (a - 1)) ^ d * (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d
      = P ^ d * ((a / 64) ^ d * (r / Real.sqrt 2) ^ d) := hLHS
    _ ≤ Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ)) + (d : ℝ) * Real.log (1 / δ)
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
            + 2 * (n : ℝ) * w
          - 3 * (d : ℝ) - 7 / 2 * ((d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t
                                  + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r) - 2 * (n : ℝ) * w)
          * ((a / 64) ^ d * (r / Real.sqrt 2) ^ d) :=
        mul_le_mul_of_nonneg_right hPd hQpos
    _ = Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ)) + (d : ℝ) * Real.log (1 / δ)
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
            + 2 * (n : ℝ) * w)
          * ((a / 64) ^ d * Real.exp (-3 * (d : ℝ)
              - 7 / 2 * ((d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t
                        + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r)))
          * (r / Real.sqrt 2) ^ d * Real.exp (-2 * (n : ℝ) * w) := by
        rw [show ((d : ℝ) * Real.log (20000 * (j : ℝ)) + (d : ℝ) * Real.log (1 / δ)
              + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
              + 2 * (n : ℝ) * w
            - 3 * (d : ℝ) - 7 / 2 * ((d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t
                                    + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r) - 2 * (n : ℝ) * w)
            = ((d : ℝ) * Real.log (20000 * (j : ℝ)) + (d : ℝ) * Real.log (1 / δ)
              + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
              + 2 * (n : ℝ) * w)
            + (-3 * (d : ℝ) - 7 / 2 * ((d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt t
                                      + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r))
            + (-2 * (n : ℝ) * w) from by ring, Real.exp_add, Real.exp_add]
        ring

-- Large block-factorization proof (product-measure transport + volume cancellation + real algebra).
set_option maxHeartbeats 2000000 in
/-- **Combined prior mass ratio** (BPPD Lemma 6.1, corrected — see the file header D10/D11). The ratio
of a net-piece mass (radius `ρ = (√5/4)jr`, intersected with `{ ∀ i ∈ S, |θᵢ| > δ }`) to the
contraction-ball mass `Π(B(θ₀, r))` is at most `exp` of

`|S|·log(512 j) + |S|·log(1/δ) + 4|S|^{3/4}(√‖θ₀‖ + √r) + 2·(card ι)·w`,

where `w` bounds the `Sᶜ`-block coordinate tail at the clamped denominator radius (mirroring
`PriorSmallBall.dlPrior_ball_zero_ge`; the assembly `PosteriorContraction` supplies `w` via the `C3` marginal-tail
bound and checks `w ≤ 1/2`). The radius `r` cancels between numerator and denominator (both carry the
same `Γ(|S|/2+1)` ball volume), so unlike the removed absolute bounds this ratio has no `r → 0`
pathology. Under the shape contract (`a = n^{−(1+β)}`, `δ ≥ n^{−2}`, `‖θ₀‖² ≤ q log⁴n`, `r² = q log n`)
every non-`j` term is `O(r²)`, `o(r²)`, or `→ 0`, and `|S|·log(512j)` sums against the shell decay
`e^{−j²r²/12}` — this is the exponent `PosteriorContraction.lean` sums. Constants are roomy placeholders adjustable
at proof-closure (charter §1). -/
theorem dlBetaRatio_le {a δ : ℝ}
    -- LEAN-ONLY: 0 < a ≤ 1/2 — DL scale range (both density bounds); engine-internal (BPPD Lemma 6.1).
    (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    -- LEAN-ONLY: 0 < δ ≤ 1 — δ-window at fixed n; engine-internal.
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (θ₀ : EuclideanSpace ℝ ι) (S : Finset ι)
    -- LEAN-ONLY: θ₀ supported on S — the truth's δ-support; engine-internal (`S₀` in the assembly).
    (hθ₀ : ∀ i ∉ S, θ₀ i = 0) (φ : EuclideanSpace ℝ ι) {j : ℕ}
    -- LEAN-ONLY: 2 ≤ j — tested radial range; engine-internal.
    (hj : 2 ≤ j) {r : ℝ}
    -- LEAN-ONLY: 0 < r — contraction radius; engine-internal.
    (hr : 0 < r)
    -- USER-INPUT: `w` bounds the `Sᶜ`-block coordinate tail at the clamped denominator radius `r/√2`
    -- (mirrors `dlPrior_ball_zero_ge`'s interface; `PosteriorContraction` discharges it via C3). BPPD Lemma 6.1.
    (w : ℝ)
    (hw : (dlMarginal a {x : ℝ |
        min (r / Real.sqrt 2 / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2) < |x|}).toReal ≤ w)
    -- USER-INPUT: `w ≤ 1/2` — unlocks the `Sᶜ` small-ball bound (deviation D7; `aₙ → 0` gives it).
    (hw2 : w ≤ 1 / 2) :
    (dlPrior a ι) (Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ∩ {θ | ∀ i ∈ S, δ < |θ i|})
          / (dlPrior a ι) (Metric.closedBall θ₀ r)
      ≤ ENNReal.ofReal (Real.exp (
            (S.card : ℝ) * Real.log (20000 * (j : ℝ))
          + (S.card : ℝ) * Real.log (1 / δ)
          + 4 * (S.card : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
          + 4 * (S.card : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r
          + 2 * (Fintype.card ι : ℝ) * w)) := by
  -- PROOF RECIPE (corrected route; the two false absolute lemmas are gone — see file header D10/D11).
  --
  -- Write `ρ := (√5/4)·jr` (numerator radius). Factor the L² ball `B(θ₀,r) ⊇ B_S(θ₀_S, r/√2) ×
  -- B_{Sᶜ}(0, r/√2)` and both measures over `S ⊔ Sᶜ` via `CoordinateSplit.dlPrior_prod_apply`:
  --   `Π(piece ∩ {δ<|θ_S|}) = Π_S(B_S(φ_S,ρ) ∩ {δ<|θ|}) · Π_{Sᶜ}(B_{Sᶜ}(φ_{Sᶜ},ρ))`,
  --   `Π(B(θ₀,r))          ≥ Π_S(B_S(θ₀_S, r/√2))       · Π_{Sᶜ}(B_{Sᶜ}(0, r/√2))`.
  -- Then `β ≤ [S-ratio] · [Sᶜ-ratio]`.
  --
  -- S-BLOCK (|S| dims; `PriorDensityBounds`, `EuclideanSpace.volume_closedBall`):
  --   • numerator `≤ (17a·δ^{a−1})^{|S|} · vol_S(B_ρ)`  (density upper, coords `>δ`);
  --   • denominator `≥ exp(−[|S|log(1/a) + C|S| + (7/2)·Σ_{i∈S}√|θᵢ|]) · vol_S(B_{r/√2})`
  --       (`prod_dlDensity_ge`, Lemma 3.2(14)); over the ball `Σ√|θᵢ| ≤ |S|^{3/4}(‖θ₀‖+r)^{1/2}
  --       ≤ |S|^{3/4}(√‖θ₀‖ + √r)` (Cauchy–Schwarz twice + `Real.sqrt_add_le`);
  --   • the `Γ(|S|/2+1)` in both volumes cancels ⇒ `vol_S(B_ρ)/vol_S(B_{r/√2}) = (√2ρ/r)^{|S|} =
  --       (√10/4·j)^{|S|}`; the `a`-powers cancel (`17a/a = 17`) ⇒
  --       `S-ratio ≤ exp(|S|log(17·√10/4·e^C·j) + (1−a)|S|log(1/δ) + (7/2)|S|^{3/4}(√‖θ₀‖+√r))`
  --       `                 ≤ exp(|S|log(512 j) + |S|log(1/δ) + 4|S|^{3/4}(√‖θ₀‖+√r))`.
  -- Sᶜ-BLOCK (card ι − |S| dims): numerator `≤ 1`; denominator `≥ exp(−2(card ι)w)` by
  --   `dlPrior_ball_zero_ge` on the `{i // i ∉ S}` subtype (hw, hw2) ⇒ `Sᶜ-ratio ≤ exp(2(card ι)w)`.
  -- Multiply (add exponents), `Real.exp_le_exp` + `ENNReal.ofReal` monotone. ∎
  --
  -- A closure session MAY tune the numeric constants (512→20000, 4, 4, 2) to whatever the block
  -- bounds deliver, keeping the shape; report the final exponent for the `PosteriorContraction` summation.
  -- Pin a single `DecidablePred` instance for `↑S`/`(↑S)ᶜ` so every `{j // j ∈ ↑S}` shares one
  -- `Fintype`/`Subtype.fintype` instance (avoids a `Fintype`-diamond in `projS`/`dlPrior`).
  letI instS : DecidablePred (· ∈ (↑S : Set ι)) := Classical.decPred _
  letI instSc : DecidablePred (· ∈ ((↑S : Set ι)ᶜ)) := Classical.decPred _
  letI : Fintype {j // j ∈ (↑S : Set ι)} := Subtype.fintype _
  letI : Fintype {j // j ∈ ((↑S : Set ι)ᶜ)} := Subtype.fintype _
  set d : ℕ := S.card with hddef
  set n : ℕ := Fintype.card ι with hndef
  -- The `S`-subtype `K` and its complement `Kc`, with cardinality/finrank bookkeeping.
  have hcardK : Fintype.card {j // j ∈ (↑S : Set ι)} = d := by
    rw [← Set.toFinset_card, Finset.toFinset_coe]
  have hfrK : Module.finrank ℝ (EuclideanSpace ℝ {j // j ∈ (↑S : Set ι)}) = d := by
    rw [finrank_euclideanSpace, hcardK]
  have hρ_nonneg : (0 : ℝ) ≤ Real.sqrt 5 / 4 * ((j : ℝ) * r) := by positivity
  have hr2_nonneg : (0 : ℝ) ≤ r / Real.sqrt 2 := by positivity
  have hw0 : (0 : ℝ) ≤ w := le_trans ENNReal.toReal_nonneg hw
  -- Abbreviation for the density-lower constant of the `S`-block.
  set CLr : ℝ := (a / 64) ^ d * Real.exp (-3 * (d : ℝ)
      - 7 / 2 * ((d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
                + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r)) with hCLr
  set Vol1 : ℝ≥0∞ := volume (Metric.ball (0 : EuclideanSpace ℝ {j // j ∈ (↑S : Set ι)}) 1) with hVol1
  -- ===== NUMERATOR: cylinder over-approximation and `S`-block density bound. =====
  have hA_meas : MeasurableSet (Metric.closedBall (projS (↑S : Set ι) φ) (Real.sqrt 5 / 4 * ((j : ℝ) * r))
      ∩ {u : EuclideanSpace ℝ {j // j ∈ (↑S : Set ι)} | ∀ i, δ < |u i|}) :=
    measurableSet_closedBall.inter (measurableSet_all_lt_abs δ)
  have hnum_sub : (Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r))
        ∩ {θ : EuclideanSpace ℝ ι | ∀ i ∈ S, δ < |θ i|})
      ⊆ projS (↑S : Set ι) ⁻¹' (Metric.closedBall (projS (↑S : Set ι) φ)
            (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ∩ {u | ∀ i, δ < |u i|})
        ∩ projS ((↑S : Set ι)ᶜ) ⁻¹' Metric.closedBall (projS ((↑S : Set ι)ᶜ) φ)
            (Real.sqrt 5 / 4 * ((j : ℝ) * r)) := by
    intro θ hθ
    obtain ⟨hball, hδc⟩ := hθ
    rw [Metric.mem_closedBall, dist_eq_norm] at hball
    have hsplit := norm_sq_split (↑S : Set ι) (θ - φ)
    rw [projS_sub', projS_sub'] at hsplit
    have hballsq : ‖θ - φ‖ ^ 2 ≤ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hball 2
    refine Set.mem_inter (Set.mem_preimage.mpr ⟨?_, ?_⟩) (Set.mem_preimage.mpr ?_)
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hX2 : ‖projS (↑S : Set ι) θ - projS (↑S : Set ι) φ‖ ^ 2
          ≤ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2 := by
        nlinarith [hsplit, sq_nonneg ‖projS ((↑S : Set ι)ᶜ) θ - projS ((↑S : Set ι)ᶜ) φ‖, hballsq]
      calc ‖projS (↑S : Set ι) θ - projS (↑S : Set ι) φ‖
          = Real.sqrt (‖projS (↑S : Set ι) θ - projS (↑S : Set ι) φ‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt ((Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2) := Real.sqrt_le_sqrt hX2
        _ = Real.sqrt 5 / 4 * ((j : ℝ) * r) := Real.sqrt_sq hρ_nonneg
    · intro i
      have hcoord : (projS (↑S : Set ι) θ) i = θ (i : ι) := by
        simp only [projS, PiLp.toLp_apply]
      rw [hcoord]
      exact hδc i.val (Finset.mem_coe.mp i.property)
    · rw [Metric.mem_closedBall, dist_eq_norm]
      have hY2 : ‖projS ((↑S : Set ι)ᶜ) θ - projS ((↑S : Set ι)ᶜ) φ‖ ^ 2
          ≤ (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2 := by
        nlinarith [hsplit, sq_nonneg ‖projS (↑S : Set ι) θ - projS (↑S : Set ι) φ‖, hballsq]
      calc ‖projS ((↑S : Set ι)ᶜ) θ - projS ((↑S : Set ι)ᶜ) φ‖
          = Real.sqrt (‖projS ((↑S : Set ι)ᶜ) θ - projS ((↑S : Set ι)ᶜ) φ‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt ((Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ 2) := Real.sqrt_le_sqrt hY2
        _ = Real.sqrt 5 / 4 * ((j : ℝ) * r) := Real.sqrt_sq hρ_nonneg
  have hnum_le : (dlPrior a ι) (Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r))
        ∩ {θ | ∀ i ∈ S, δ < |θ i|})
      ≤ (dlPrior a {j // j ∈ (↑S : Set ι)}) (Metric.closedBall (projS (↑S : Set ι) φ)
            (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ∩ {u | ∀ i, δ < |u i|})
        * (dlPrior a {j // j ∈ ((↑S : Set ι)ᶜ)}) (Metric.closedBall (projS ((↑S : Set ι)ᶜ) φ)
            (Real.sqrt 5 / 4 * ((j : ℝ) * r))) :=
    le_trans (measure_mono hnum_sub)
      (le_of_eq (dlPrior_prod_apply a (↑S : Set ι) hA_meas
        (measurableSet_closedBall : MeasurableSet (Metric.closedBall (projS ((↑S : Set ι)ᶜ) φ)
          (Real.sqrt 5 / 4 * ((j : ℝ) * r))))))
  have hnumSc_le_one : (dlPrior a {j // j ∈ ((↑S : Set ι)ᶜ)}) (Metric.closedBall
      (projS ((↑S : Set ι)ᶜ) φ) (Real.sqrt 5 / 4 * ((j : ℝ) * r))) ≤ 1 := prob_le_one
  have hnumS_le : (dlPrior a {j // j ∈ (↑S : Set ι)}) (Metric.closedBall (projS (↑S : Set ι) φ)
        (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ∩ {u | ∀ i, δ < |u i|})
      ≤ ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ d)
        * (ENNReal.ofReal ((Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d) * Vol1) := by
    have hdens : ∀ u ∈ Metric.closedBall (projS (↑S : Set ι) φ) (Real.sqrt 5 / 4 * ((j : ℝ) * r))
        ∩ {u : EuclideanSpace ℝ {j // j ∈ (↑S : Set ι)} | ∀ i, δ < |u i|},
        ∏ i, dlDensity a (u i) ≤ ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ d) := by
      intro u hu
      have hu' : ∀ i, δ < |u i| := hu.2
      calc ∏ i, dlDensity a (u i)
          ≤ ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ (Finset.univ.card)) :=
            prod_dlDensity_le ha ha2 hδ hδ1 (S := Finset.univ) (fun i _ => hu' i)
        _ = ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ d) := by rw [Finset.card_univ, hcardK]
    refine le_trans (dlPrior_le_of_subset ha hA_meas hdens) ?_
    refine mul_le_mul_right ?_ _
    calc volume (Metric.closedBall (projS (↑S : Set ι) φ) (Real.sqrt 5 / 4 * ((j : ℝ) * r))
            ∩ {u | ∀ i, δ < |u i|})
        ≤ volume (Metric.closedBall (projS (↑S : Set ι) φ) (Real.sqrt 5 / 4 * ((j : ℝ) * r))) :=
          measure_mono Set.inter_subset_left
      _ = ENNReal.ofReal ((Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d) * Vol1 := by
          rw [Measure.addHaar_closedBall volume _ hρ_nonneg, hfrK]
  -- ===== DENOMINATOR: cylinder under-approximation and block density bounds. =====
  have hθ₀c : projS ((↑S : Set ι)ᶜ) θ₀ = 0 := by
    have h0 : (fun i : {j // j ∈ ((↑S : Set ι)ᶜ)} => θ₀ (i : ι)) = fun _ => 0 := by
      funext i
      exact hθ₀ i.val (fun hmem => i.property (Finset.mem_coe.mpr hmem))
    simp only [projS, h0]
    rfl
  have hden_sup : (projS (↑S : Set ι) ⁻¹' Metric.closedBall (projS (↑S : Set ι) θ₀) (r / Real.sqrt 2)
        ∩ projS ((↑S : Set ι)ᶜ) ⁻¹' Metric.closedBall
            (0 : EuclideanSpace ℝ {j // j ∈ ((↑S : Set ι)ᶜ)}) (r / Real.sqrt 2))
      ⊆ Metric.closedBall θ₀ r := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := hθ
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] at h1
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsplit := norm_sq_split (↑S : Set ι) (θ - θ₀)
    rw [projS_sub', projS_sub', hθ₀c, sub_zero] at hsplit
    have hr2 : (r / Real.sqrt 2) ^ 2 = r ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hX2 : ‖projS (↑S : Set ι) θ - projS (↑S : Set ι) θ₀‖ ^ 2 ≤ r ^ 2 / 2 := by
      nlinarith [h1, norm_nonneg (projS (↑S : Set ι) θ - projS (↑S : Set ι) θ₀), hr2_nonneg, hr2]
    have hY2 : ‖projS ((↑S : Set ι)ᶜ) θ‖ ^ 2 ≤ r ^ 2 / 2 := by
      nlinarith [h2, norm_nonneg (projS ((↑S : Set ι)ᶜ) θ), hr2_nonneg, hr2]
    nlinarith [hsplit, hX2, hY2, norm_nonneg (θ - θ₀), hr.le]
  have hden_ge : (dlPrior a {j // j ∈ (↑S : Set ι)}) (Metric.closedBall (projS (↑S : Set ι) θ₀)
          (r / Real.sqrt 2))
        * (dlPrior a {j // j ∈ ((↑S : Set ι)ᶜ)}) (Metric.closedBall
          (0 : EuclideanSpace ℝ {j // j ∈ ((↑S : Set ι)ᶜ)}) (r / Real.sqrt 2))
      ≤ (dlPrior a ι) (Metric.closedBall θ₀ r) := by
    rw [← dlPrior_prod_apply a (↑S : Set ι)
      (measurableSet_closedBall : MeasurableSet (Metric.closedBall (projS (↑S : Set ι) θ₀)
        (r / Real.sqrt 2)))
      (measurableSet_closedBall : MeasurableSet (Metric.closedBall
        (0 : EuclideanSpace ℝ {j // j ∈ ((↑S : Set ι)ᶜ)}) (r / Real.sqrt 2)))]
    exact measure_mono hden_sup
  have hdenS_ge : ENNReal.ofReal CLr
        * (ENNReal.ofReal ((r / Real.sqrt 2) ^ d) * Vol1)
      ≤ (dlPrior a {j // j ∈ (↑S : Set ι)}) (Metric.closedBall (projS (↑S : Set ι) θ₀)
          (r / Real.sqrt 2)) := by
    have hvol : volume (Metric.closedBall (projS (↑S : Set ι) θ₀) (r / Real.sqrt 2))
        = ENNReal.ofReal ((r / Real.sqrt 2) ^ d) * Vol1 := by
      rw [Measure.addHaar_closedBall volume _ hr2_nonneg, hfrK]
    rw [← hvol]
    refine dlPrior_ball_ge_volume ha (projS (↑S : Set ι) θ₀) (r / Real.sqrt 2) ?_
    intro θ hθball
    rw [Metric.mem_closedBall, dist_eq_norm] at hθball
    have hnormθ : ‖θ‖ ≤ ‖θ₀‖ + r := by
      have hns := norm_sub_norm_le θ (projS (↑S : Set ι) θ₀)
      have h2 : ‖projS (↑S : Set ι) θ₀‖ ≤ ‖θ₀‖ := norm_projS_le (↑S : Set ι) θ₀
      have h3 : r / Real.sqrt 2 ≤ r :=
        div_le_self hr.le ((Real.one_le_sqrt).mpr (by norm_num))
      linarith [hns, h2, h3, hθball]
    have hsqrtθ : Real.sqrt ‖θ‖ ≤ Real.sqrt ‖θ₀‖ + Real.sqrt r :=
      (Real.sqrt_le_sqrt hnormθ).trans (real_sqrt_add_le _ _ (norm_nonneg _) hr.le)
    have hsum : (∑ jj, Real.sqrt |θ jj|)
        ≤ (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖ + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r := by
      calc (∑ jj, Real.sqrt |θ jj|)
          ≤ (Fintype.card {j // j ∈ (↑S : Set ι)} : ℝ) ^ ((3 : ℝ) / 4) * ‖θ‖ ^ ((1 : ℝ) / 2) :=
            sum_sqrt_abs_le θ
        _ = (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ‖ := by rw [hcardK, ← Real.sqrt_eq_rpow]
        _ ≤ (d : ℝ) ^ ((3 : ℝ) / 4) * (Real.sqrt ‖θ₀‖ + Real.sqrt r) :=
            mul_le_mul_of_nonneg_left hsqrtθ (by positivity)
        _ = (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖ + (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r := by
            ring
    refine le_trans ?_ (prod_dlDensity_ge ha (le_trans ha2 (by norm_num)) θ)
    rw [hCLr]
    apply ENNReal.ofReal_le_ofReal
    rw [hcardK]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply Real.exp_le_exp.mpr
    linarith [hsum]
  have hdenSc_ge : ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * w))
      ≤ (dlPrior a {j // j ∈ ((↑S : Set ι)ᶜ)}) (Metric.closedBall
          (0 : EuclideanSpace ℝ {j // j ∈ ((↑S : Set ι)ᶜ)}) (r / Real.sqrt 2)) := by
    rcases Nat.eq_zero_or_pos (Fintype.card {j // j ∈ ((↑S : Set ι)ᶜ)}) with hKc0 | hKcpos
    · haveI : IsEmpty {j // j ∈ ((↑S : Set ι)ᶜ)} := Fintype.card_eq_zero_iff.mp hKc0
      have hball_univ : Metric.closedBall (0 : EuclideanSpace ℝ {j // j ∈ ((↑S : Set ι)ᶜ)})
          (r / Real.sqrt 2) = Set.univ := by
        ext x
        simp only [Metric.mem_closedBall, Set.mem_univ, iff_true, dist_zero_right]
        have hx0 : ‖x‖ = 0 := by
          rw [EuclideanSpace.norm_eq]; simp [Finset.univ_eq_empty]
        rw [hx0]; positivity
      rw [hball_univ, measure_univ]
      refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
      have : (0 : ℝ) ≤ 2 * (n : ℝ) * w :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hw0
      linarith
    · have hle : (Fintype.card {j // j ∈ ((↑S : Set ι)ᶜ)} : ℝ) ≤ (n : ℝ) := by
        rw [hndef]; exact_mod_cast Fintype.card_subtype_le _
      have hwKc : (dlMarginal a {x : ℝ | min (r / Real.sqrt 2
            / Real.sqrt (Fintype.card {j // j ∈ ((↑S : Set ι)ᶜ)} : ℝ)) (1 / 2) < |x|}).toReal ≤ w := by
        refine le_trans (ENNReal.toReal_mono ?_ (measure_mono ?_)) hw
        · exact ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one
        · intro x hx
          simp only [Set.mem_setOf_eq] at hx ⊢
          refine lt_of_le_of_lt (min_le_min ?_ le_rfl) hx
          exact div_le_div_of_nonneg_left (by positivity)
            (Real.sqrt_pos.mpr (by exact_mod_cast hKcpos))
            (Real.sqrt_le_sqrt (by exact_mod_cast hle))
      have hzero := dlPrior_ball_zero_ge (ι := {j // j ∈ ((↑S : Set ι)ᶜ)}) (a := a)
        (r := r / Real.sqrt 2) (w := w) (by positivity) hwKc hw2
      refine le_trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)) hzero
      nlinarith [hle, hw0]
  -- ===== ASSEMBLE: `num ≤ ofReal(exp EXP) · den`. =====
  refine ENNReal.div_le_of_le_mul ?_
  -- The core real inequality (block ratio, volumes cancelled).
  have hreal := massRatio_real_ineq (a := a) (δ := δ) (r := r) (t := ‖θ₀‖) (w := w)
    (d := d) (n := n) (j := j) ha hδ hδ1 hr hj
  -- Coefficient inequality with `Vol1` pulled out on both sides.
  have hlow : (ENNReal.ofReal CLr * (ENNReal.ofReal ((r / Real.sqrt 2) ^ d) * Vol1))
        * ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * w))
      ≤ (dlPrior a {j // j ∈ (↑S : Set ι)}) (Metric.closedBall (projS (↑S : Set ι) θ₀)
            (r / Real.sqrt 2))
        * (dlPrior a {j // j ∈ ((↑S : Set ι)ᶜ)}) (Metric.closedBall
            (0 : EuclideanSpace ℝ {j // j ∈ ((↑S : Set ι)ᶜ)}) (r / Real.sqrt 2)) :=
    mul_le_mul' hdenS_ge hdenSc_ge
  have hC : ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ d)
        * ENNReal.ofReal ((Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d)
      ≤ ENNReal.ofReal (Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ)) + (d : ℝ) * Real.log (1 / δ)
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r + 2 * (n : ℝ) * w))
        * ENNReal.ofReal CLr * ENNReal.ofReal ((r / Real.sqrt 2) ^ d)
        * ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * w)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc (dlPrior a ι) (Metric.closedBall φ (Real.sqrt 5 / 4 * ((j : ℝ) * r))
          ∩ {θ | ∀ i ∈ S, δ < |θ i|})
      ≤ _ * _ := hnum_le
    _ ≤ _ * 1 := by gcongr
    _ = (dlPrior a {j // j ∈ (↑S : Set ι)}) (Metric.closedBall (projS (↑S : Set ι) φ)
          (Real.sqrt 5 / 4 * ((j : ℝ) * r)) ∩ {u | ∀ i, δ < |u i|}) := mul_one _
    _ ≤ ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ d)
          * (ENNReal.ofReal ((Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d) * Vol1) := hnumS_le
    _ = (ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ d)
          * ENNReal.ofReal ((Real.sqrt 5 / 4 * ((j : ℝ) * r)) ^ d)) * Vol1 := by ring
    _ ≤ (ENNReal.ofReal (Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ))
            + (d : ℝ) * Real.log (1 / δ) + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r + 2 * (n : ℝ) * w))
          * ENNReal.ofReal CLr * ENNReal.ofReal ((r / Real.sqrt 2) ^ d)
          * ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * w))) * Vol1 :=
        mul_le_mul_left hC Vol1
    _ = ENNReal.ofReal (Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ))
            + (d : ℝ) * Real.log (1 / δ) + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r + 2 * (n : ℝ) * w))
          * ((ENNReal.ofReal CLr * (ENNReal.ofReal ((r / Real.sqrt 2) ^ d) * Vol1))
            * ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * w))) := by ring
    _ ≤ ENNReal.ofReal (Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ))
            + (d : ℝ) * Real.log (1 / δ) + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r + 2 * (n : ℝ) * w))
          * ((dlPrior a {j // j ∈ (↑S : Set ι)}) (Metric.closedBall (projS (↑S : Set ι) θ₀)
                (r / Real.sqrt 2))
            * (dlPrior a {j // j ∈ ((↑S : Set ι)ᶜ)}) (Metric.closedBall
                (0 : EuclideanSpace ℝ {j // j ∈ ((↑S : Set ι)ᶜ)}) (r / Real.sqrt 2))) := by
        gcongr
    _ ≤ ENNReal.ofReal (Real.exp ((d : ℝ) * Real.log (20000 * (j : ℝ))
            + (d : ℝ) * Real.log (1 / δ) + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt ‖θ₀‖
            + 4 * (d : ℝ) ^ ((3 : ℝ) / 4) * Real.sqrt r + 2 * (n : ℝ) * w))
          * (dlPrior a ι) (Metric.closedBall θ₀ r) := by gcongr

end StatLean.Bayesian
