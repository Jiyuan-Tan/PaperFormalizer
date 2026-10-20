module
public import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
public import Mathlib.Data.Int.Log
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

/-!
# Dyadic nets and chain scaffolding

Purely metric chaining scaffolding (no probability): realizer Finset nets at
each dyadic scale $\varepsilon_k = 2^{-k}$ ($k \in \mathbb{Z}$), coarse-scale
selection via `Int.clog` (so that $2^{-\kappa} \in [\operatorname{diam} T,
2\operatorname{diam} T)$ and the $\kappa$-level net is a singleton), a
pseudometric-safe fine scale below the minimum positive distance of a finite
$T$, closest-point projections $\pi_k(t)$, the distance-filtered close-pair
Finsets over which per-level maxima are taken, the chain telescoping
$X_t - X_{\pi_\kappa(t)} = \sum_k (X_{\pi_{k+1}(t)} - X_{\pi_k(t)})$, and
sup-of-sum ≤ sum-of-sups. Shared by `DiscreteDudley`, `DudleyTail`, and
`GenericChaining`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Eqs. (8.4)–(8.10) (the chaining setup in
the proof of Theorem 8.1.4).

**Proof formalization notes.** Nets are realizer Finsets extracted from
`Metric.exists_set_encard_eq_coveringNumber` (the `≠ ⊤` discharge is
`coveringNumber ≤ encard < ⊤` for finite `T`). Scales are ℤ-dyadic with
`κ := −Int.clog 2 D` (via `Int.self_le_zpow_clog` /
`Int.zpow_pred_clog_lt_self`); levels are re-indexed by ℕ offsets so the
telescoping is literally `Finset.sum_range_sub`. In a PSEUDOmetric the finest
projection satisfies `dist t (π t) = 0` only — the a.e. identification
`X_{π t} = X_t` is done downstream via
`ae_eq_zero_of_subGaussianNorm_eq_zero`. Per-level maxima run over
`closePairs N M r` — the distance-FILTERED product Finset — so far-apart
pairs never enter the maximal inequality; `card ≤ |N|·|M|`. `netProj N x` is
total with junk value `x` for `N = ∅` (documented; all consumers supply
`N.Nonempty`). Pre-agreed >300-line split plan (design risk register): if
this file exceeds ~300 lines during proof closure, split into
`Chaining/DyadicScales.lean` (scale selection: `exists_coarse_scale`,
`exists_fine_scale`, covering-number facts) and
`Chaining/NetProjections.lean` (`netProj`, `closePairs`, telescoping,
sup-exchange) — the `def`s stay byte-identical, only lemma homes move.
Named-sorry fallback of this work item: `exists_finset_net` (the
encard-to-Finset plumbing).

**Bibliographic comments.** The dyadic-scale chaining construction goes back
to A. N. Kolmogorov (continuity criterion, unpublished lectures, 1930s) and
was developed for Gaussian processes by R. M. Dudley, "The sizes of compact
subsets of Hilbert space and continuity of Gaussian processes," *J. Funct.
Anal.* 1 (1967), 290–330; the ε-net vocabulary is Kolmogorov–Tikhomirov
(1959).
-/

open Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {E : Type*} [PseudoMetricSpace E]

/-- Realizer net at a finite covering number (HDP §8.1, Eq. (8.5)): any set
`T` with `𝒩(T, ε) ≠ ⊤` admits an internal Finset net at radius `ε > 0` whose
cardinality realizes the covering number (from
`Metric.exists_set_encard_eq_coveringNumber`). This is the general engine for
chaining over totally bounded index sets (faithful infinite-`T` Dudley); the
finite case is the corollary `exists_finset_net` below. -/
lemma exists_finset_net_of_cov_ne_top {T : Set E} {ε : ℝ}
    -- LEAN-ONLY: finite covering number at this radius (junk-guard: at
    -- 𝒩 = ⊤ no finite net exists); supplied by `hcov` in the assemblies
    (hcov : coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness so the net is nonempty
    (hne : T.Nonempty)
    -- LEAN-ONLY: positive radius; ε ≤ 0 is never used by chaining
    (hε : 0 < ε) :
    ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧ (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε) ∧
      (N.card : ℕ∞) = coveringNumber T ε := by
  obtain ⟨C, hCsub, hCfin, hCcov, hCenc⟩ := Metric.exists_set_encard_eq_coveringNumber hcov
  refine ⟨hCfin.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [Set.Finite.coe_toFinset]; exact hCsub
  · rw [← Finset.coe_nonempty, Set.Finite.coe_toFinset]; exact hCcov.nonempty hne
  · intro t ht
    obtain ⟨y, hyC, hy⟩ := hCcov ht
    refine ⟨y, hCfin.mem_toFinset.mpr hyC, ?_⟩
    exact (edist_le_ofReal hε.le).mp hy
  · rw [Set.Finite.encard_eq_coe_toFinset_card hCfin] at hCenc
    exact hCenc

/-- Realizer net (HDP §8.1, Eq. (8.5)), finite-`T` corollary of
`exists_finset_net_of_cov_ne_top` (the `≠ ⊤` discharge is
`coveringNumber ≤ encard < ⊤`). -/
lemma exists_finset_net {T : Set E}
    -- LEAN-ONLY: T finite (book WLOG, HDP p.227 footnote); realizer plumbing
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness so the net is nonempty
    (hne : T.Nonempty)
    -- LEAN-ONLY: positive radius; ε ≤ 0 is never used by chaining
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧ (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε) ∧
      (N.card : ℕ∞) = coveringNumber T ε :=
  exists_finset_net_of_cov_ne_top
    (ne_top_of_le_ne_top (by rw [Set.encard_ne_top_iff]; exact hfin)
      (Metric.coveringNumber_le_encard_self T)) hne hε

/-- Finite covering numbers at every positive radius from total boundedness
(the bridge Mathlib lacks at the pin: internal ε-nets from
`totallyBounded_iff` external ball covers by a center-swap into `T`).
Faithful infinite-`T` chaining consumes covering finiteness in exactly this
`hcov` shape. -/
theorem coveringNumber_ne_top_of_totallyBounded {T : Set E}
    -- USER-INPUT: T totally bounded — the book's standing finite-entropy
    -- setting for Dudley (HDP §8.1: the RHS is finite only for such T)
    (hTB : TotallyBounded T)
    -- LEAN-ONLY: positive radius (at ε ≤ 0 the covering number of an
    -- infinite T is genuinely ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    coveringNumber T ε ≠ ⊤ := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simp [coveringNumber]
  obtain ⟨x₀, hx₀⟩ := hTne
  haveI : Nonempty E := ⟨x₀⟩
  -- External `ε/2`-cover from total boundedness.
  obtain ⟨t, htfin, htcov⟩ := (Metric.totallyBounded_iff.mp hTB) (ε / 2) (by linarith)
  -- Center-swap: for each center `y` whose ball meets `T`, pick an internal
  -- witness `z y ∈ T ∩ ball y (ε/2)`.
  set P : E → Prop := fun y => ∃ z, z ∈ T ∧ z ∈ Metric.ball y (ε / 2) with hP
  have zchoose : ∀ y, P y → ∃ z, z ∈ T ∧ z ∈ Metric.ball y (ε / 2) := fun y h => h
  choose! z hzT hzB using zchoose
  set C : Set E := z '' {y | y ∈ t ∧ P y} with hCdef
  have hCsub : C ⊆ T := by
    rintro _ ⟨y, ⟨_, hy⟩, rfl⟩; exact hzT y hy
  have hCfin : C.Finite := (htfin.subset (fun y hy => hy.1)).image z
  have hCcov : Metric.IsCover (Real.toNNReal ε) T C := by
    intro x hx
    have hxU : x ∈ ⋃ y ∈ t, Metric.ball y (ε / 2) := htcov hx
    simp only [Set.mem_iUnion, exists_prop] at hxU
    obtain ⟨y, hyt, hxy⟩ := hxU
    have hPy : P y := ⟨x, hx, hxy⟩
    refine ⟨z y, ⟨y, ⟨hyt, hPy⟩, rfl⟩, ?_⟩
    have h1 : dist x y < ε / 2 := Metric.mem_ball.mp hxy
    have h2 : dist (z y) y < ε / 2 := Metric.mem_ball.mp (hzB y hPy)
    have hd : dist x (z y) < ε := by
      calc dist x (z y) ≤ dist x y + dist y (z y) := dist_triangle x y (z y)
        _ = dist x y + dist (z y) y := by rw [dist_comm y (z y)]
        _ < ε := by linarith
    exact (edist_le_ofReal hε.le).mpr hd.le
  exact ne_top_of_le_ne_top hCfin.encard_lt_top.ne
    (Metric.IsCover.coveringNumber_le_encard hCsub hCcov)

/-- Total boundedness from finite covering numbers at every positive radius
(converse bridge; internal nets are in particular external covers). -/
theorem totallyBounded_of_coveringNumber_ne_top {T : Set E}
    -- LEAN-ONLY: the `hcov` package carried by the general Dudley statements
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤) :
    TotallyBounded T := by
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · exact totallyBounded_empty
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨N, hNsub, hNne, hNcov, hNcard⟩ :=
    exists_finset_net_of_cov_ne_top (hcov (ε / 2) (by linarith)) hTne (by linarith)
  refine ⟨↑N, N.finite_toSet, fun x hx => ?_⟩
  obtain ⟨a, haN, ha⟩ := hNcov x hx
  exact Set.mem_biUnion (Finset.mem_coe.mpr haN)
    (Metric.mem_ball.mpr (lt_of_le_of_lt ha (by linarith)))

/-- Boundedness (hence an honest `Metric.diam`) from the `hcov` package:
route through `totallyBounded_of_coveringNumber_ne_top` and
`TotallyBounded.isBounded`. -/
theorem isBounded_of_coveringNumber_ne_top {T : Set E}
    -- LEAN-ONLY: the `hcov` package carried by the general Dudley statements
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤) :
    Bornology.IsBounded T :=
  (totallyBounded_of_coveringNumber_ne_top hcov).isBounded

/-- Above the diameter one center suffices (HDP §8.1, Eq. (8.6), the coarse
net): real-radius wrapper of `Metric.coveringNumber_eq_one_of_ediam_le`. -/
lemma coveringNumber_eq_one_of_diam_le {T : Set E}
    -- LEAN-ONLY: nonemptiness (empty T has covering number 0, not 1)
    (hne : T.Nonempty)
    -- LEAN-ONLY: boundedness so `Metric.diam` is meaningful (not junk 0)
    (hbd : Bornology.IsBounded T)
    -- LEAN-ONLY: nonnegative radius (negative radii clamp to 0)
    {ε : ℝ} (hε : 0 ≤ ε)
    -- LEAN-ONLY: radius above the diameter; HDP §8.1, Eq (8.6)
    (h : Metric.diam T ≤ ε) :
    coveringNumber T ε = 1 := by
  have hed : Metric.ediam T ≤ ENNReal.ofReal ε :=
    Metric.ediam_le_of_forall_dist_le
      (fun x hx y hy => (Metric.dist_le_diam_of_mem hbd hx hy).trans h)
  exact Metric.coveringNumber_eq_one_of_ediam_le hne hed

/-- Two far-apart points force at least two centers — the quantitative
`𝒩 ≥ 2` below `diam/2` device feeding the diameter lower bounds on the
entropy sum (HDP §8.1, Remark 8.1.6 absorption). -/
lemma one_lt_coveringNumber_of_two_mul_lt_dist {T : Set E} {ε : ℝ} {a b : E}
    -- LEAN-ONLY: nonnegative radius — REQUIRED (statement fix at the debt
    -- gate: for ε < 0 with a = b coincident the claim is false, e.g.
    -- T = {x₀}, ε = −1 gives 𝒩 = 1; the sole consumer supplies 0 < e)
    (hε : 0 ≤ ε)
    -- LEAN-ONLY: the two witnesses live in T
    (ha : a ∈ T) (hb : b ∈ T)
    -- LEAN-ONLY: separation 2ε < d(a,b); pure metric pigeonhole
    (h : 2 * ε < dist a b) :
    1 < coveringNumber T ε := by
  by_contra hle
  push_neg at hle
  have hnetop : Metric.coveringNumber (Real.toNNReal ε) T ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) hle
  obtain ⟨C, hCsub, hCfin, hCcov, hCenc⟩ := Metric.exists_set_encard_eq_coveringNumber hnetop
  have hsub : C.encard ≤ 1 := hCenc.le.trans hle
  rw [Set.encard_le_one_iff] at hsub
  obtain ⟨ya, hyaC, hya⟩ := hCcov ha
  obtain ⟨yb, hybC, hyb⟩ := hCcov hb
  have hyab : ya = yb := hsub ya yb hyaC hybC
  subst hyab
  -- Both projections are within ε, so dist a b ≤ 2ε — contradiction.
  have hda : dist a ya ≤ ε := (edist_le_ofReal hε).mp hya
  have hdb : dist b ya ≤ ε := (edist_le_ofReal hε).mp hyb
  have : dist a b ≤ dist a ya + dist ya b := dist_triangle a ya b
  rw [dist_comm ya b] at this
  linarith

/-- Coarse dyadic scale (HDP §8.1, Eqs. (8.4)/(8.6)): `κ := −Int.clog 2 D`
satisfies `D ≤ 2^{−κ} < 2D` (via `Int.self_le_zpow_clog` and
`Int.zpow_pred_clog_lt_self`). -/
lemma exists_coarse_scale {D : ℝ}
    -- LEAN-ONLY: positive diameter bound; the D = 0 corner is degenerate
    (hD : 0 < D) :
    ∃ κ : ℤ, D ≤ (2 : ℝ) ^ (-κ) ∧ (2 : ℝ) ^ (-κ) < 2 * D := by
  refine ⟨-Int.clog 2 D, ?_, ?_⟩
  · rw [neg_neg]
    simpa using! Int.self_le_zpow_clog (by norm_num) D
  · rw [neg_neg]
    have hpred := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 2) (by norm_num) hD
    simp only [Nat.cast_ofNat] at hpred
    have hstep : (2 : ℝ) ^ (Int.clog 2 D - 1) * 2 = (2 : ℝ) ^ (Int.clog 2 D) := by
      rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; field_simp
    have := mul_lt_mul_of_pos_right hpred (show (0 : ℝ) < 2 by norm_num)
    rw [hstep] at this
    linarith

/-- Fine dyadic scale (HDP §8.1, Eq. (8.6), the fine net), pseudometric-safe:
below the minimum POSITIVE distance of the finite `T`, dyadically-close
points are at pseudo-distance exactly `0`. -/
lemma exists_fine_scale {T : Set E}
    -- LEAN-ONLY: T finite so the minimum positive distance exists
    (hfin : T.Finite) (κ : ℤ) :
    ∃ n : ℕ, 0 < n ∧ ∀ s ∈ T, ∀ t ∈ T,
      dist s t ≤ (2 : ℝ) ^ (-(κ + n : ℤ)) → dist s t = 0 := by
  classical
  set D : Finset ℝ :=
    ((hfin.toFinset ×ˢ hfin.toFinset).image fun p => dist p.1 p.2).filter (fun d => 0 < d)
    with hDdef
  have hmemD : ∀ s ∈ T, ∀ t ∈ T, 0 < dist s t → dist s t ∈ D := by
    intro s hs t ht hpos
    rw [hDdef, Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr
      ⟨hfin.mem_toFinset.mpr hs, hfin.mem_toFinset.mpr ht⟩, rfl⟩, hpos⟩
  by_cases hDne : D.Nonempty
  · set m : ℝ := D.min' hDne with hm
    have hmpos : 0 < m := by
      have hmem : m ∈ D := D.min'_mem hDne
      rw [hDdef, Finset.mem_filter] at hmem
      exact hmem.2
    have hκpos : (0 : ℝ) < 2 ^ (-κ) := zpow_pos (by norm_num) _
    have h2κpos : (0 : ℝ) < 2 ^ κ := zpow_pos (by norm_num) _
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (x := m * 2 ^ κ)
      (mul_pos hmpos h2κpos) (show (1 : ℝ) / 2 < 1 by norm_num)
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    intro s hs t ht hst
    by_contra hne0
    have hpos : 0 < dist s t := lt_of_le_of_ne dist_nonneg (Ne.symm hne0)
    have hge : m ≤ dist s t := D.min'_le _ (hmemD s hs t ht hpos)
    have hlt : (2 : ℝ) ^ (-(κ + (↑(n + 1) : ℤ))) < m := by
      have ehalf : ((1 : ℝ) / 2) ^ (n + 1) = (2 : ℝ) ^ (-(↑(n + 1) : ℤ)) := by
        rw [zpow_neg, zpow_natCast, one_div, inv_pow]
      have e1 : (2 : ℝ) ^ (-(κ + (↑(n + 1) : ℤ))) = 2 ^ (-κ) * (1 / 2) ^ (n + 1) := by
        rw [ehalf, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1; push_cast; ring
      rw [e1]
      have hmono : ((1 : ℝ) / 2) ^ (n + 1) ≤ (1 / 2) ^ n := by
        rw [pow_succ]
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) n]
      calc (2 : ℝ) ^ (-κ) * (1 / 2) ^ (n + 1)
          ≤ 2 ^ (-κ) * (1 / 2) ^ n :=
            mul_le_mul_of_nonneg_left hmono hκpos.le
        _ < 2 ^ (-κ) * (m * 2 ^ κ) := mul_lt_mul_of_pos_left hn hκpos
        _ = m := by rw [zpow_neg]; field_simp
    linarith [hst.trans hlt.le]
  · refine ⟨1, one_pos, ?_⟩
    intro s hs t ht _
    by_contra hne0
    have hpos : 0 < dist s t := lt_of_le_of_ne dist_nonneg (Ne.symm hne0)
    exact hDne ⟨dist s t, hmemD s hs t ht hpos⟩

/-- **Closest-point projection** `π_N(x)` onto a Finset net (HDP §8.1, the
projections `π_k(t)` of Eq. (8.7)): a point of `N` minimizing the distance to
`x`. Edge behavior: junk value `x` itself when `N = ∅` (every consumer
supplies `N.Nonempty`). -/
noncomputable def netProj (N : Finset E) (x : E) : E :=
  if h : N.Nonempty then (N.exists_min_image (fun a => dist x a) h).choose else x

/-- The projection lands in the net (HDP §8.1, Eq. (8.7)). -/
lemma netProj_mem {N : Finset E}
    -- LEAN-ONLY: nonemptiness excludes the junk branch of `netProj`
    (hN : N.Nonempty) (x : E) :
    netProj N x ∈ N := by
  simp only [netProj, dif_pos hN]
  exact (N.exists_min_image (fun a => dist x a) hN).choose_spec.1

/-- The projection beats any witness: if some net point is `ε`-close to `x`,
so is `netProj N x` (HDP §8.1, Eq. (8.7)). -/
lemma dist_netProj_le {N : Finset E} {x : E} {ε : ℝ}
    -- LEAN-ONLY: a witness net point within ε (from the net property)
    (hx : ∃ a ∈ N, dist x a ≤ ε) :
    dist x (netProj N x) ≤ ε := by
  obtain ⟨a, haN, ha⟩ := hx
  have hN : N.Nonempty := ⟨a, haN⟩
  simp only [netProj, dif_pos hN]
  exact le_trans ((N.exists_min_image (fun a => dist x a) hN).choose_spec.2 a haN) ha

open Classical in
/-- **Close pairs** (HDP §8.1, proof of Theorem 8.1.4, Step 2): the
distance-filtered product Finset `{(a,b) ∈ N × M : d(a,b) ≤ r}` indexing one
chaining level, so far-apart pairs (whose increments are not ψ₂-small) never
enter the maximal inequality. Edge behavior: empty when `r < 0` in a genuine
metric space with `N`, `M` disjoint far apart — consumers re-establish
nonemptiness via `proj_pair_mem_closePairs`. -/
noncomputable def closePairs (N M : Finset E) (r : ℝ) : Finset (E × E) :=
  (N ×ˢ M).filter fun p => dist p.1 p.2 ≤ r

/-- Cardinality of a chaining level (HDP §8.1, Step 2:
`|T_k|·|T_{k−1}| ≤ |T_k|²`). -/
lemma card_closePairs_le (N M : Finset E) (r : ℝ) :
    (closePairs N M r).card ≤ N.card * M.card := by
  rw [closePairs, ← Finset.card_product]
  exact Finset.card_filter_le _ _

/-- Consecutive projections form a close pair (HDP §8.1, Step 2: the triangle
inequality `d(π_k t, π_{k−1} t) ≤ ε_k + ε_{k−1}`). -/
lemma proj_pair_mem_closePairs {N M : Finset E} {x : E} {ε δ : ℝ}
    -- LEAN-ONLY: projection quality at the two consecutive scales
    (hN : dist x (netProj N x) ≤ ε) (hM : dist x (netProj M x) ≤ δ)
    -- LEAN-ONLY: nonemptiness excludes the junk branches of `netProj`
    (hNne : N.Nonempty) (hMne : M.Nonempty) :
    (netProj N x, netProj M x) ∈ closePairs N M (ε + δ) := by
  rw [closePairs, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨netProj_mem hNne x, netProj_mem hMne x⟩, ?_⟩
  calc dist (netProj N x) (netProj M x)
      ≤ dist (netProj N x) x + dist x (netProj M x) := dist_triangle _ _ _
    _ = dist x (netProj N x) + dist x (netProj M x) := by rw [dist_comm (netProj N x) x]
    _ ≤ ε + δ := add_le_add hN hM

/-- Chain telescoping (HDP §8.1, Eqs. (8.8)/(8.9)): literally
`Finset.sum_range_sub`. -/
lemma chain_telescope {n : ℕ} (g : ℕ → ℝ) :
    g n - g 0 = ∑ i ∈ Finset.range n, (g (i + 1) - g i) :=
  (Finset.sum_range_sub g n).symm

/-- Sup-of-sum ≤ sum-of-sups over a finite index set (HDP §8.1, Eq. (8.10)). -/
lemma biSup_sum_le_sum_biSup {T : Set E}
    -- LEAN-ONLY: T finite so all real biSups are honest finite maxima
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty) {n : ℕ} (g : ℕ → E → ℝ) :
    (⨆ t ∈ T, ∑ i ∈ Finset.range n, g i t)
      ≤ ∑ i ∈ Finset.range n, ⨆ t ∈ T, g i t := by
  classical
  obtain ⟨t₀, ht₀⟩ := hne
  haveI : Nonempty E := ⟨t₀⟩
  -- The value `⨆ (_ : t ∈ T), h t` is `h t` when `t ∈ T` and `0` (via `sSup ∅`) otherwise.
  have inner_pos : ∀ (h : E → ℝ) {t : E}, t ∈ T → (⨆ _ : t ∈ T, h t) = h t := by
    intro h t ht; haveI : Nonempty (t ∈ T) := ⟨ht⟩; exact ciSup_const
  have inner_neg : ∀ (h : E → ℝ) {t : E}, t ∉ T → (⨆ _ : t ∈ T, h t) = 0 := by
    intro h t ht; haveI : IsEmpty (t ∈ T) := ⟨ht⟩; exact Real.iSup_of_isEmpty _
  -- Each per-level `biSup` is bounded above (its range lies in a finite set).
  have hbdd : ∀ h : E → ℝ, BddAbove (Set.range fun s => ⨆ _ : s ∈ T, h s) := by
    intro h
    apply Set.Finite.bddAbove
    apply Set.Finite.subset ((hfin.image h).insert 0)
    rintro _ ⟨s, rfl⟩
    change (⨆ _ : s ∈ T, h s) ∈ insert 0 (h '' T)
    by_cases hs : s ∈ T
    · rw [inner_pos h hs]; exact Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩
    · rw [inner_neg h hs]; exact Set.mem_insert _ _
  -- Each per-level `biSup` is ≥ 0 (the `sSup ∅ = 0` slot leaks in, or T = univ).
  have hle_biSup : ∀ (h : E → ℝ) {t : E}, t ∈ T → h t ≤ ⨆ s ∈ T, h s := by
    intro h t ht
    calc h t = ⨆ _ : t ∈ T, h t := (inner_pos h ht).symm
      _ ≤ ⨆ s ∈ T, h s := le_ciSup (hbdd h) t
  refine ciSup_le fun t => ?_
  by_cases ht : t ∈ T
  · rw [inner_pos (fun t => ∑ i ∈ Finset.range n, g i t) ht]
    exact Finset.sum_le_sum fun i _ => hle_biSup (g i) ht
  · rw [inner_neg (fun t => ∑ i ∈ Finset.range n, g i t) ht]
    refine Finset.sum_nonneg fun i _ => ?_
    calc (0 : ℝ) = ⨆ _ : t ∈ T, g i t := (inner_neg (g i) ht).symm
      _ ≤ ⨆ s ∈ T, g i s := le_ciSup (hbdd (g i)) t

end StatLean.ConcentrationInequalities
