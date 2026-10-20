module
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.InformationTheory.Hamming

@[expose] public section

/-!
# Packing of sparse unit vectors (Wainwright Example 5.8 / Exercise 5.8)

A Chapter-5 metric-entropy prerequisite for the sparse-linear-regression minimax lower bound
(Example 15.16): the set of `s`-sparse unit vectors in `ℝᵈ` admits a `1/2`-separated set with
```
log M ≥ (s/2) · log((d − s)/s),
```
i.e. a set `T` of `s`-sparse unit vectors, pairwise at Euclidean distance `≥ 1/2`, with
`log |T| ≥ (s/2) log((d−s)/s)`. (Sparsity: at most `s` nonzero coordinates.)

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8 /
Exercise 5.8 (the sparse-vector packing), invoked in Chapter 15 (Minimax lower bounds), §15.3.3,
Example 15.16 (minimax rate for sparse linear regression).

**Proof formalization notes.**

*Constant deviation (CLAUDE.md §1).* The combinatorial heart is proved with a *weakened* additive
slack: `log |T| ≥ (s/2) log((d−s)/s) − s·log 2`. The sharp book constant is not reachable by an
elementary Gilbert–Varshamov volume estimate (it needs the binary-entropy ball count / an algebraic
Reed–Solomon code); the weakened bound is still exponentially large. See
`exists_bounded_overlap_supports_gv`.

*Proof architecture.* The construction is **normalized support indicators**. To an `s`-element
support `S ⊆ [d]` we attach the unit vector `v_S = s^{-1/2} · 𝟙_S` (value `s^{-1/2}` on `S`, `0`
elsewhere): it has norm `1` and exactly `s` nonzero coordinates. For two supports `S, S'`,
```
‖v_S − v_S'‖² = (|S| + |S'| − 2|S ∩ S'|) / s = (2s − 2|S ∩ S'|)/s,
```
so whenever `2|S ∩ S'| ≤ s` we get `‖v_S − v_S'‖ ≥ 1 ≥ 1/2`. All of this geometry is discharged
below. The **only** residual is the combinatorial support count `exists_bounded_overlap_supports`: a
Gilbert–Varshamov packing of the `C(d,s)` weight-`s` supports with pairwise intersection `≤ s/2` and
`log |𝒮| ≥ (s/2) log((d−s)/s)`. Mapping `S ↦ v_S` (injective, since distinct supports give
`≥ 1`-separated vectors) transports that count to the sparse-vector packing.

**Bibliographic comments.** The packing argument is an instance of the **Gilbert–Varshamov bound**,
the classical volume/greedy lower bound on the size of a maximal separated code. It originates in two
independent works: E. N. Gilbert, "A comparison of signalling alphabets," *Bell System Technical
Journal* 31 (3), 504–522 (1952); and R. R. Varshamov, "Estimate of the number of signals in error
correcting codes," *Doklady Akademii Nauk SSSR* 117, 739–741 (1957). The specialization to packing
`s`-sparse unit vectors (or, equivalently, weight-`s` supports of `[d]` with bounded pairwise
overlap) is **folklore**: it is a standard textbook synthesis with no single seminal origin, recorded
e.g. as Wainwright Example 5.8 / Exercise 5.8 and used pervasively in high-dimensional minimax theory.
The `q`-ary alphabet variant proved here (blocks of size `q = ⌊d/s⌋`) is the routine extension of the
binary Gilbert–Varshamov code to a non-binary alphabet.
-/

open scoped ENNReal
open Finset

namespace StatLean.Minimaxity

/-- The normalized support indicator `v_S = s^{-1/2} · 𝟙_S ∈ ℝᵈ`: value `s^{-1/2}` on the support
`S`, zero elsewhere. For `|S| = s` this is a unit vector with exactly `s` nonzero coordinates.

Formalizes Wainwright Example 5.8's packing element. Degenerate inputs (`s = 0`, or `S.card ≠ s`)
are harmless here: the scaling `s^{-1/2}` is still well defined (`Real.sqrt 0 = 0`, so the vector is
`0`), and all downstream lemmas carry the hypotheses `0 < s`, `S.card = s` that they need. -/
private noncomputable def sparseVec (d s : ℕ) (S : Finset (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if i ∈ S then (Real.sqrt s)⁻¹ else 0)

private theorem sparseVec_apply (d s : ℕ) (S : Finset (Fin d)) (i : Fin d) :
    (sparseVec d s S) i = if i ∈ S then (Real.sqrt s)⁻¹ else 0 := rfl

/-- Each normalized support indicator with `|S| = s > 0` is a unit vector. -/
private theorem norm_sparseVec (d s : ℕ) (hs : 0 < s) (S : Finset (Fin d)) (hcard : S.card = s) :
    ‖sparseVec d s S‖ = 1 := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  rw [EuclideanSpace.norm_eq]
  have hsq : ∀ i, ‖(sparseVec d s S) i‖ ^ 2 = if i ∈ S then (s : ℝ)⁻¹ else 0 := by
    intro i
    rw [sparseVec_apply]
    by_cases h : i ∈ S <;>
      simp [h, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hspos.le]
  rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, hcard, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hspos), Real.sqrt_one]

/-- Two normalized support indicators with `|S| = |S'| = s` and pairwise intersection
`2|S ∩ S'| ≤ s` are `≥ 1/2`-separated (in fact `≥ 1`-separated):
`‖v_S − v_S'‖² = (2s − 2|S ∩ S'|)/s ≥ 1`. -/
private theorem half_le_norm_sparseVec_sub (d s : ℕ) (hs : 0 < s) (S S' : Finset (Fin d))
    (hS : S.card = s) (hS' : S'.card = s) (hov : 2 * (S ∩ S').card ≤ s) :
    (1 / 2 : ℝ) ≤ ‖sparseVec d s S - sparseVec d s S'‖ := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  -- Abbreviations for the `{0,1}` indicators.
  set χ : Finset (Fin d) → Fin d → ℝ := fun A i => if i ∈ A then (1 : ℝ) else 0 with hχ
  have sumχ : ∀ A : Finset (Fin d), ∑ i, χ A i = (A.card : ℝ) := by
    intro A
    rw [hχ]; simp only
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Per-coordinate: `‖(v_S − v_S') i‖² = s⁻¹ · (χ_S i − χ_S' i)²`.
  have happ : ∀ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2
      = (s : ℝ)⁻¹ * (χ S i - χ S' i) ^ 2 := by
    intro i
    have ha2 : ((Real.sqrt s)⁻¹) ^ 2 = (s : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hspos.le]
    rw [PiLp.sub_apply, sparseVec_apply, sparseVec_apply, Real.norm_eq_abs, sq_abs, hχ]
    simp only
    rw [show (if i ∈ S then (Real.sqrt s)⁻¹ else 0)
          = (Real.sqrt s)⁻¹ * (if i ∈ S then (1 : ℝ) else 0) by rw [mul_ite, mul_one, mul_zero],
        show (if i ∈ S' then (Real.sqrt s)⁻¹ else 0)
          = (Real.sqrt s)⁻¹ * (if i ∈ S' then (1 : ℝ) else 0) by rw [mul_ite, mul_one, mul_zero],
        ← mul_sub, mul_pow, ha2]
  -- Per-coordinate identity `(χ_S i − χ_S' i)² = χ_S i + χ_S' i − 2·χ_{S∩S'} i`.
  have key : ∀ i, (χ S i - χ S' i) ^ 2 = χ S i + χ S' i - χ (S ∩ S') i - χ (S ∩ S') i := by
    intro i
    rw [hχ]; simp only [Finset.mem_inter]
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;>
      simp only [h1, h2, if_true, if_false, and_true, and_false] <;> ring
  -- Sum the per-coordinate squared norms.
  have hsumeq : ∑ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2
      = (s : ℝ)⁻¹ * (2 * s - 2 * ((S ∩ S').card : ℝ)) := by
    rw [Finset.sum_congr rfl (fun i _ => happ i), ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, sumχ, sumχ, sumχ,
      hS, hS']
    ring
  -- The squared norm is `≥ 1`.
  have hsum_ge : (1 : ℝ) ≤ ∑ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2 := by
    rw [hsumeq]
    have hc : (2 * ((S ∩ S').card : ℝ)) ≤ s := by exact_mod_cast hov
    have hge : (s : ℝ) ≤ 2 * s - 2 * ((S ∩ S').card : ℝ) := by linarith
    calc (1 : ℝ) = (s : ℝ)⁻¹ * s := by rw [inv_mul_cancel₀ (ne_of_gt hspos)]
      _ ≤ (s : ℝ)⁻¹ * (2 * s - 2 * ((S ∩ S').card : ℝ)) :=
          mul_le_mul_of_nonneg_left hge (le_of_lt (inv_pos.2 hspos))
  -- Conclude via `√`.
  rw [EuclideanSpace.norm_eq]
  calc (1 / 2 : ℝ) ≤ 1 := by norm_num
    _ = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (∑ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum_ge

/-! ### `q`-ary Gilbert–Varshamov (the engine of the large-`d` regime)

We mirror the binary `gilbert_varshamov` (`HammingPacking.lean`) over an arbitrary alphabet
`Fin q`. The single combinatorial debt is a crude Hamming-ball volume estimate
`qary_ball_card_le`, after which a maximal-separated-set argument gives an exponential code. -/

/-- **Crude `q`-ary Hamming-ball volume bound.** Over the alphabet `Fin q` (`q ≥ 2`), the number of
`y : Fin n → Fin q` with `2 · hammingDist t y < n` of a fixed center `t` is at most
`(q − 1)^{⌊(n−1)/2⌋} · 2^n`.

This is the elementary Chernoff factorisation (mirroring the binary `hamming_ball_card_le`): with
`k = ⌊(n−1)/2⌋` and `λ = q − 1 ≥ 1`, every ball point has `hammingDist t y ≤ k`, so
`1 ≤ λ^k (1/λ)^{hammingDist t y}`; summing the right side over the whole cube factorises over
coordinates to `λ^k · 2^n` (each coordinate contributes `1 + λ·(1/λ) = 2`). The `2^n` factor is the
deliberate slack that makes the estimate elementary (the sharp constant needs the binary-entropy
function), and is what ultimately weakens the packing constant by `s·log 2`. -/
private theorem qary_ball_card_le (n q : ℕ) (hq : 2 ≤ q) (t : Fin n → Fin q) :
    ((univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n)).card : ℝ)
      ≤ ((q : ℝ) - 1) ^ ((n - 1) / 2) * 2 ^ n := by
  classical
  have hL1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hLpos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  -- The cube sum of `(1/λ)^{hammingDist t y}` factorises over coordinates to `2^n`.
  have hfact : ∑ y : Fin n → Fin q, (1 / ((q : ℝ) - 1)) ^ (hammingDist t y) = 2 ^ n := by
    have hpt : ∀ y : Fin n → Fin q, (1 / ((q : ℝ) - 1)) ^ (hammingDist t y)
        = ∏ i : Fin n, (1 / ((q : ℝ) - 1)) ^ (if t i ≠ y i then 1 else 0) := by
      intro y
      rw [Finset.prod_pow_eq_pow_sum, ← Finset.card_filter]; rfl
    simp_rw [hpt]
    rw [show (univ : Finset (Fin n → Fin q)) = Fintype.piFinset (fun _ => univ) from
          (Fintype.piFinset_univ).symm,
      ← Finset.prod_univ_sum (fun _ => (univ : Finset (Fin q)))
          (fun (i : Fin n) (b : Fin q) => (1 / ((q : ℝ) - 1)) ^ (if t i ≠ b then 1 else 0))]
    have hinner : ∀ i : Fin n,
        ∑ b : Fin q, (1 / ((q : ℝ) - 1)) ^ (if t i ≠ b then 1 else 0) = 2 := by
      intro i
      rw [← Finset.add_sum_erase univ
            (fun b => (1 / ((q : ℝ) - 1)) ^ (if t i ≠ b then 1 else 0)) (Finset.mem_univ (t i))]
      have hself : (1 / ((q : ℝ) - 1)) ^ (if t i ≠ t i then 1 else 0) = 1 := by simp
      rw [hself]
      have herase : ∀ b ∈ univ.erase (t i),
          (1 / ((q : ℝ) - 1)) ^ (if t i ≠ b then 1 else 0) = 1 / ((q : ℝ) - 1) := by
        intro b hb
        rw [Finset.mem_erase] at hb
        have hne : t i ≠ b := fun h => hb.1 h.symm
        simp [hne]
      rw [Finset.sum_congr rfl herase, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hqc : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
      rw [hqc, mul_one_div, div_self (ne_of_gt hLpos)]; norm_num
    rw [Finset.prod_congr rfl (fun i _ => hinner i), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  -- Bound the ball cardinality by the cube sum of `λ^k (1/λ)^{hammingDist t y}`.
  have hcard_le : ((univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n)).card : ℝ)
      ≤ ∑ y : Fin n → Fin q,
          ((q : ℝ) - 1) ^ ((n - 1) / 2) * (1 / ((q : ℝ) - 1)) ^ (hammingDist t y) := by
    have h1 : ((univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n)).card : ℝ)
        = ∑ _y ∈ univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n), (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones]; push_cast; rfl
    rw [h1]
    refine le_trans (Finset.sum_le_sum (fun y hy => ?_))
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun y _ _ => mul_nonneg (pow_nonneg hLpos.le _) (pow_nonneg (one_div_pos.2 hLpos).le _)))
    rw [Finset.mem_filter] at hy
    obtain ⟨_, hy2⟩ := hy
    have hhdk : hammingDist t y ≤ (n - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
    have h3 : ((q : ℝ) - 1) ^ (hammingDist t y) ≤ ((q : ℝ) - 1) ^ ((n - 1) / 2) :=
      pow_le_pow_right₀ hL1 hhdk
    have hpos : (0 : ℝ) < ((q : ℝ) - 1) ^ (hammingDist t y) := pow_pos hLpos _
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    exact (one_le_div₀ hpos).2 h3
  calc ((univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n)).card : ℝ)
      ≤ ∑ y : Fin n → Fin q,
          ((q : ℝ) - 1) ^ ((n - 1) / 2) * (1 / ((q : ℝ) - 1)) ^ (hammingDist t y) := hcard_le
    _ = ((q : ℝ) - 1) ^ ((n - 1) / 2) * 2 ^ n := by rw [← Finset.mul_sum, hfact]

/-- **`q`-ary Gilbert–Varshamov code** (loose constant). For `q ≥ 2` there is a code
`C ⊆ (Fin n → Fin q)` pairwise at `hammingDist ≥ n/2` (i.e. `n ≤ 2·hammingDist`) with
`log |C| ≥ (n/2)·log q − n·log 2`.

The `− n·log 2` is the slack inherited from the crude ball bound `qary_ball_card_le`; the sharp
constant `(n/2)·log q` alone is not reachable by this elementary volume estimate. Proof: a maximal
`n/2`-separated `C`; by maximality its radius-`<n/2` balls cover all `q^n` words, so
`q^n ≤ |C| · (q−1)^{⌊(n−1)/2⌋} · 2^n`, and taking logs with `⌊(n−1)/2⌋·log(q−1) ≤ (n/2)·log q`. -/
private theorem qary_gv (n q : ℕ) (hq : 2 ≤ q) :
    ∃ C : Finset (Fin n → Fin q),
      (n / 2 : ℝ) * Real.log q - n * Real.log 2 ≤ Real.log C.card ∧
      ∀ f ∈ C, ∀ g ∈ C, f ≠ g → n ≤ 2 * hammingDist f g := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    refine ⟨univ, ?_, ?_⟩
    · have h1 : (univ : Finset (Fin 0 → Fin q)).card = 1 := by simp
      rw [h1, Nat.cast_one, Real.log_one]; simp
    · intro a _ b _ hab; exact absurd (funext fun i => i.elim0) hab
  · -- A maximal `n/2`-separated subset of the cube.
    obtain ⟨C, hC, hCmax⟩ := Finset.exists_max_image
      ((univ : Finset (Fin n → Fin q)).powerset.filter
        (fun S => ∀ a ∈ S, ∀ b ∈ S, a ≠ b → n ≤ 2 * hammingDist a b))
      Finset.card ⟨∅, by simp⟩
    obtain ⟨_, hCsep⟩ := Finset.mem_filter.1 hC
    have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hLpos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
    have hL1 : (1 : ℝ) ≤ (q : ℝ) - 1 := by linarith
    have hlogLnn : (0 : ℝ) ≤ Real.log ((q : ℝ) - 1) := Real.log_nonneg hL1
    have hlogLq : Real.log ((q : ℝ) - 1) ≤ Real.log (q : ℝ) := Real.log_le_log hLpos (by linarith)
    have hk2 : (((n - 1) / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
      have hkle : 2 * ((n - 1) / 2) ≤ n := by
        have := Nat.div_mul_le_self (n - 1) 2
        omega
      have : (2 : ℝ) * (((n - 1) / 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hkle
      linarith
    -- Covering: maximality forces every point within `< n/2` of some `t ∈ C`.
    have hcover : ∀ x : Fin n → Fin q, ∃ t ∈ C, 2 * hammingDist x t < n := by
      intro x
      by_cases hx : x ∈ C
      · exact ⟨x, hx, by simpa [hammingDist_self] using hnpos⟩
      · have hins_card : (insert x C).card = C.card + 1 := Finset.card_insert_of_notMem hx
        have hnotsep : ¬ (∀ a ∈ insert x C, ∀ b ∈ insert x C, a ≠ b → n ≤ 2 * hammingDist a b) := by
          intro hsep'
          have hmem : (insert x C) ∈ (univ : Finset (Fin n → Fin q)).powerset.filter
              (fun S => ∀ a ∈ S, ∀ b ∈ S, a ≠ b → n ≤ 2 * hammingDist a b) :=
            Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (by simp), hsep'⟩
          have := hCmax _ hmem
          rw [hins_card] at this; omega
        simp only [not_forall, not_le, exists_prop] at hnotsep
        obtain ⟨a, ha, b, hb, hab, hlt⟩ := hnotsep
        rcases Finset.mem_insert.1 ha with rfl | haC
        · rcases Finset.mem_insert.1 hb with rfl | hbC
          · exact absurd rfl hab
          · exact ⟨b, hbC, hlt⟩
        · rcases Finset.mem_insert.1 hb with rfl | hbC
          · exact ⟨a, haC, by rwa [hammingDist_comm] at hlt⟩
          · have := hCsep a haC b hbC hab; omega
    have hsub : (univ : Finset (Fin n → Fin q)) ⊆
        C.biUnion (fun t => univ.filter (fun y => 2 * hammingDist t y < n)) := by
      intro x _
      obtain ⟨t, htC, hxt⟩ := hcover x
      rw [Finset.mem_biUnion]
      exact ⟨t, htC, Finset.mem_filter.2 ⟨Finset.mem_univ x, by rwa [hammingDist_comm] at hxt⟩⟩
    have hcardcube : Fintype.card (Fin n → Fin q) = q ^ n := by simp [Fintype.card_fin]
    have hcount : (q : ℝ) ^ n ≤ (C.card : ℝ) * (((q : ℝ) - 1) ^ ((n - 1) / 2) * 2 ^ n) := by
      have hnat : Fintype.card (Fin n → Fin q)
          ≤ ∑ t ∈ C, (univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n)).card := by
        rw [← Finset.card_univ]
        exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
      calc (q : ℝ) ^ n = (Fintype.card (Fin n → Fin q) : ℝ) := by rw [hcardcube]; norm_cast
        _ ≤ (∑ t ∈ C,
              (univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n)).card : ℕ) := by
              exact_mod_cast hnat
        _ = ∑ t ∈ C,
              ((univ.filter (fun y : Fin n → Fin q => 2 * hammingDist t y < n)).card : ℝ) := by
              push_cast; rfl
        _ ≤ ∑ _t ∈ C, (((q : ℝ) - 1) ^ ((n - 1) / 2) * 2 ^ n) :=
              Finset.sum_le_sum (fun t _ => qary_ball_card_le n q hq t)
        _ = (C.card : ℝ) * (((q : ℝ) - 1) ^ ((n - 1) / 2) * 2 ^ n) := by
              rw [Finset.sum_const, nsmul_eq_mul]
    refine ⟨C, ?_, fun f hf g hg hfg => hCsep f hf g hg hfg⟩
    -- `exp((n/2)log q − n log 2) ≤ |C|`, hence the log bound.
    have hWexp : Real.exp ((n / 2 : ℝ) * Real.log q - n * Real.log 2)
        * (((q : ℝ) - 1) ^ ((n - 1) / 2) * 2 ^ n) ≤ (q : ℝ) ^ n := by
      have hLk : ((q : ℝ) - 1) ^ ((n - 1) / 2)
          = Real.exp ((((n - 1) / 2 : ℕ) : ℝ) * Real.log ((q : ℝ) - 1)) := by
        rw [Real.exp_nat_mul, Real.exp_log hLpos]
      have h2n : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      have hqn : (q : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log q) := by
        rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast (by omega : 0 < q))]
      rw [hLk, h2n, hqn, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have hprod : (((n - 1) / 2 : ℕ) : ℝ) * Real.log ((q : ℝ) - 1)
          ≤ ((n : ℝ) / 2) * Real.log q := by
        calc (((n - 1) / 2 : ℕ) : ℝ) * Real.log ((q : ℝ) - 1)
            ≤ ((n : ℝ) / 2) * Real.log ((q : ℝ) - 1) :=
              mul_le_mul_of_nonneg_right hk2 hlogLnn
          _ ≤ ((n : ℝ) / 2) * Real.log q := mul_le_mul_of_nonneg_left hlogLq (by positivity)
      linarith
    have hpos2 : (0 : ℝ) < ((q : ℝ) - 1) ^ ((n - 1) / 2) * 2 ^ n :=
      mul_pos (pow_pos hLpos _) (by positivity)
    have hWC : Real.exp ((n / 2 : ℝ) * Real.log q - n * Real.log 2) ≤ (C.card : ℝ) :=
      le_of_mul_le_mul_right (le_trans hWexp hcount) hpos2
    have := Real.log_le_log (Real.exp_pos _) hWC
    rwa [Real.log_exp] at this

/-! ### Block supports: transporting the `q`-ary code to weight-`s` subsets of `[d]` -/

/-- The `j`-th coordinate of the `k`-th block, when `[d]` is cut into `s` consecutive blocks of size
`q = ⌊d/s⌋`: `blockCoord k j = k·⌊d/s⌋ + j ∈ [d]`. -/
private def blockCoord (d s : ℕ) (k : Fin s) (j : Fin (d / s)) : Fin d :=
  ⟨k.val * (d / s) + j.val, by
    have hsq : s * (d / s) ≤ d := by rw [mul_comm]; exact Nat.div_mul_le_self d s
    calc k.val * (d / s) + j.val < k.val * (d / s) + (d / s) := by have := j.isLt; omega
      _ = (k.val + 1) * (d / s) := by ring
      _ ≤ s * (d / s) := Nat.mul_le_mul (by have := k.isLt; omega) (le_refl _)
      _ ≤ d := hsq⟩

/-- A block support: one chosen coordinate per block, indexed by `f : Fin s → Fin (d/s)`. -/
private def blockSupport (d s : ℕ) (f : Fin s → Fin (d / s)) : Finset (Fin d) :=
  univ.image (fun k => blockCoord d s k (f k))

/-- Block coordinates are determined by their (block, offset): `blockCoord` is injective. -/
private theorem blockCoord_inj (d s : ℕ) {k₁ k₂ : Fin s} {j₁ j₂ : Fin (d / s)}
    (h : blockCoord d s k₁ j₁ = blockCoord d s k₂ j₂) : k₁ = k₂ ∧ j₁ = j₂ := by
  have hqpos : 0 < d / s := lt_of_le_of_lt (Nat.zero_le _) j₁.isLt
  have hval : k₁.val * (d / s) + j₁.val = k₂.val * (d / s) + j₂.val := by
    have := congrArg Fin.val h
    simpa [blockCoord] using this
  have hval' : (d / s) * k₁.val + j₁.val = (d / s) * k₂.val + j₂.val := by
    rw [mul_comm (d / s) k₁.val, mul_comm (d / s) k₂.val]; exact hval
  have hk : k₁.val = k₂.val := by
    have l1 : ((d / s) * k₁.val + j₁.val) / (d / s) = k₁.val := by
      rw [Nat.mul_add_div hqpos, Nat.div_eq_of_lt j₁.isLt, Nat.add_zero]
    have l2 : ((d / s) * k₂.val + j₂.val) / (d / s) = k₂.val := by
      rw [Nat.mul_add_div hqpos, Nat.div_eq_of_lt j₂.isLt, Nat.add_zero]
    rw [← l1, ← l2, hval']
  have hj : j₁.val = j₂.val := by
    have hxeq : (d / s) * k₁.val = (d / s) * k₂.val := by rw [hk]
    omega
  exact ⟨Fin.ext hk, Fin.ext hj⟩

/-- Each block support has exactly `s` coordinates. -/
private theorem blockSupport_card (d s : ℕ) (f : Fin s → Fin (d / s)) :
    (blockSupport d s f).card = s := by
  have hinj : Function.Injective (fun k : Fin s => blockCoord d s k (f k)) := by
    intro a b h; exact (blockCoord_inj d s h).1
  rw [blockSupport, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- The intersection of two block supports counts the blocks where `f` and `g` agree. -/
private theorem blockSupport_inter_card (d s : ℕ) (f g : Fin s → Fin (d / s)) :
    (blockSupport d s f ∩ blockSupport d s g).card
      = (univ.filter (fun k => f k = g k)).card := by
  classical
  have hinjf : Function.Injective (fun k : Fin s => blockCoord d s k (f k)) := by
    intro a b h; exact (blockCoord_inj d s h).1
  have hset : blockSupport d s f ∩ blockSupport d s g
      = (univ.filter (fun k => f k = g k)).image (fun k => blockCoord d s k (f k)) := by
    ext c
    simp only [Finset.mem_inter, blockSupport, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
      have heq : blockCoord d s k (f k) = blockCoord d s k' (g k') := by rw [hk, hk']
      obtain ⟨hkk, hfg⟩ := blockCoord_inj d s heq
      exact ⟨k, by rw [hfg, hkk], hk⟩
    · rintro ⟨k, hfgk, hc⟩
      exact ⟨⟨k, hc⟩, ⟨k, by rw [← hfgk]; exact hc⟩⟩
  rw [hset, Finset.card_image_of_injective _ hinjf]

/-- Agreement count and Hamming distance partition the `s` blocks. -/
private theorem filter_eq_card (s q : ℕ) (f g : Fin s → Fin q) :
    (univ.filter (fun k => f k = g k)).card + hammingDist f g = s := by
  classical
  have hh : hammingDist f g = (univ.filter (fun k => ¬ (f k = g k))).card := rfl
  rw [hh, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

/-- **Gilbert–Varshamov packing of weight-`s` supports, large-`d` regime** (the combinatorial heart
of Wainwright Example 5.8). For `2s < d` there is a family `𝒮` of `s`-element subsets of `[d]`,
pairwise with intersection `2|S ∩ S'| ≤ s`, and
```
log |𝒮| ≥ (s/2) · log((d − s)/s) − s · log 2.
```

**Deviation from the book (CLAUDE.md §1).** Wainwright's Example 5.8 states the sharp constant
`(s/2)·log((d−s)/s)`. That exact constant is *not* reachable by an elementary Gilbert–Varshamov
volume argument — e.g. for `d = 40, s = 10` the crude block / `q`-ary count yields only
`≈ 50`–`135` codewords versus the `≈ 243` the sharp constant demands (the sharp count needs the
binary-entropy ball estimate or an algebraic Reed–Solomon code). We therefore prove the **weakened
exponential bound** with the explicit additive slack `− s·log 2`, which still gives an
exponentially large packing and suffices for the downstream minimax lower bound up to constants.

Construction: partition `[d]` into `s` blocks of size `q = ⌊d/s⌋ ≥ 2`; a `q`-ary GV code
`C ⊆ (Fin s → Fin q)` at `hammingDist ≥ s/2` maps (injectively) via `f ↦ blockSupport f` to a
weight-`s` support family with `2|S ∩ S'| ≤ s`, transporting `log|C| ≥ (s/2)log q − s·log 2` and
`log q ≥ log((d−s)/s)`. -/
private theorem exists_bounded_overlap_supports_gv (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d)
    (hd : 2 * s < d) :
    ∃ 𝒮 : Finset (Finset (Fin d)),
      (∀ S ∈ 𝒮, S.card = s) ∧
      (∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → 2 * (S ∩ S').card ≤ s) ∧
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) - s * Real.log 2 ≤ Real.log 𝒮.card := by
  classical
  have hq : 2 ≤ d / s := (Nat.le_div_iff_mul_le hs).2 (by omega)
  obtain ⟨C, hClog, hCsep⟩ := qary_gv s (d / s) hq
  refine ⟨C.image (blockSupport d s), ?_, ?_, ?_⟩
  · -- Every member has `s` coordinates.
    intro S hS
    rw [Finset.mem_image] at hS
    obtain ⟨f, _, rfl⟩ := hS
    exact blockSupport_card d s f
  · -- Bounded overlap, transported from the Hamming separation of `C`.
    intro S hS S' hS' hSS'
    rw [Finset.mem_image] at hS hS'
    obtain ⟨f, hf, rfl⟩ := hS
    obtain ⟨g, hg, rfl⟩ := hS'
    have hfg' : f ≠ g := fun h => hSS' (by rw [h])
    rw [blockSupport_inter_card]
    have he := filter_eq_card s (d / s) f g
    have hsep := hCsep f hf g hg hfg'
    omega
  · -- The log bound: `|image| = |C|`, then `log|C| ≥ (s/2)log q − s log2 ≥ RHS`.
    have hSinj : Set.InjOn (blockSupport d s) C := by
      intro f hf g hg h
      by_contra hfg'
      have hsep := hCsep f hf g hg hfg'
      have he := filter_eq_card s (d / s) f g
      have hhd : 0 < hammingDist f g := by omega
      have hcontra : (blockSupport d s f ∩ blockSupport d s g).card = s := by
        rw [h, Finset.inter_self]; exact blockSupport_card d s g
      rw [blockSupport_inter_card] at hcontra
      omega
    rw [Finset.card_image_of_injOn hSinj]
    have hspos : (0 : ℝ) < s := by exact_mod_cast hs
    have hsd' : (s : ℝ) < d := by exact_mod_cast (show s < d by omega)
    have hds_pos : (0 : ℝ) < (d : ℝ) - s := by linarith
    have hds_div_pos : (0 : ℝ) < ((d : ℝ) - s) / s := div_pos hds_pos hspos
    have hmod : d % s < s := Nat.mod_lt d hs
    have hdam : s * (d / s) + d % s = d := Nat.div_add_mod d s
    have hdlt : (d : ℝ) < s * ((d / s : ℕ) : ℝ) + s := by
      have h0 : (d : ℝ) = (s : ℝ) * ((d / s : ℕ) : ℝ) + ((d % s : ℕ) : ℝ) := by
        exact_mod_cast hdam.symm
      have h1 : ((d % s : ℕ) : ℝ) < (s : ℝ) := by exact_mod_cast hmod
      rw [h0]; linarith
    have hlt : ((d : ℝ) - s) / s < ((d / s : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hspos, mul_comm]; linarith
    have hloglt : Real.log (((d : ℝ) - s) / s) ≤ Real.log ((d / s : ℕ) : ℝ) :=
      Real.log_le_log hds_div_pos (le_of_lt hlt)
    have hmul : (s / 2 : ℝ) * Real.log (((d : ℝ) - s) / s)
        ≤ (s / 2 : ℝ) * Real.log ((d / s : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hloglt (by positivity)
    linarith [hClog, hmul]

/-- **Gilbert–Varshamov packing of weight-`s` supports** (Wainwright Example 5.8). There is a family
`𝒮` of `s`-element subsets of `[d]`, pairwise with intersection `2|S ∩ S'| ≤ s` (equivalently
symmetric difference `≥ s`), and
```
log |𝒮| ≥ (s/2) · log((d − s)/s).
```

The `d ≤ 2s` case is discharged here directly: then `(d − s)/s ≤ 1`, so `log((d − s)/s) ≤ 0`, and
subtracting the nonnegative `s·log 2` keeps the whole right side `≤ 0 = log 1`, which a singleton
support family attains. The genuine `2s < d` combinatorics are deferred to
`exists_bounded_overlap_supports_gv`.

**Deviation (CLAUDE.md §1).** The bound is the weakened `(s/2)·log((d−s)/s) − s·log 2`; see
`exists_bounded_overlap_supports_gv` for why the sharp book constant is unreachable by
elementary GV. -/
private theorem exists_bounded_overlap_supports (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ 𝒮 : Finset (Finset (Fin d)),
      (∀ S ∈ 𝒮, S.card = s) ∧
      (∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → 2 * (S ∩ S').card ≤ s) ∧
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) - s * Real.log 2 ≤ Real.log 𝒮.card := by
  classical
  rcases Nat.lt_or_ge (2 * s) d with hd | hd
  · -- `2s < d`: the genuine Gilbert–Varshamov regime.
    exact exists_bounded_overlap_supports_gv d s hs hsd hd
  · -- `d ≤ 2s`: the right side is `≤ 0`, so a singleton support family suffices.
    replace hd : d ≤ 2 * s := hd
    obtain ⟨S, -, hScard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin d))) (n := s)
        (by rw [Finset.card_univ, Fintype.card_fin]; exact hsd)
    refine ⟨{S}, ?_, ?_, ?_⟩
    · intro T hT; rw [Finset.mem_singleton] at hT; subst hT; exact hScard
    · intro T hT T' hT' hne
      rw [Finset.mem_singleton] at hT hT'; subst hT; subst hT'; exact absurd rfl hne
    · -- `log |{S}| = log 1 = 0 ≥ (s/2)·log((d−s)/s)` because `(d−s)/s ≤ 1`.
      rw [Finset.card_singleton, Nat.cast_one, Real.log_one]
      have hsR : (0 : ℝ) < s := by exact_mod_cast hs
      have hds0 : (0 : ℝ) ≤ (d : ℝ) - s := by
        have : (s : ℝ) ≤ d := by exact_mod_cast hsd
        linarith
      have hle : ((d : ℝ) - s) / s ≤ 1 := by
        rw [div_le_one hsR]
        have : (d : ℝ) ≤ 2 * s := by exact_mod_cast hd
        linarith
      have hhalf : (0 : ℝ) ≤ (s / 2 : ℝ) := by positivity
      have hlognonpos : Real.log (((d : ℝ) - s) / s) ≤ 0 :=
        Real.log_nonpos (div_nonneg hds0 hsR.le) hle
      have hslog2 : (0 : ℝ) ≤ (s : ℝ) * Real.log 2 :=
        mul_nonneg hsR.le (Real.log_nonneg (by norm_num))
      nlinarith [mul_nonneg hhalf (neg_nonneg.mpr hlognonpos)]

-- USER-INPUT: `log |𝒮| ≥ (s/2) log((d−s)/s)` support-count bound; Wainwright Ex 5.8.
-- Supplied internally by `exists_bounded_overlap_supports` (named residual), not as a hypothesis.
/-- **Packing of sparse unit vectors**, construction form (Wainwright Example 5.8): the set of
`s`-sparse unit vectors in `ℝᵈ` contains a `1/2`-separated set `T` with
`log |T| ≥ (s/2) log((d−s)/s) − s·log 2` (weakened constant; see
`exists_bounded_overlap_supports_gv`). -/
private theorem sparse_packing (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) - s * Real.log 2 ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1 ∧ (Finset.univ.filter fun i => v i ≠ 0).card ≤ s) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  classical
  obtain ⟨𝒮, hcard, hov, hlog⟩ := exists_bounded_overlap_supports d s hs hsd
  -- The packing: image of the support family under the normalized-indicator map.
  refine ⟨𝒮.image (sparseVec d s), ?_, ?_, ?_⟩
  · -- Cardinality is preserved (the map is injective on `𝒮`), so the log bound transports.
    have hinj : Set.InjOn (sparseVec d s) 𝒮 := by
      intro S hS S' hS' heq
      by_contra hne
      have hsep := half_le_norm_sparseVec_sub d s hs S S' (hcard S hS) (hcard S' hS')
        (hov S hS S' hS' hne)
      rw [heq, sub_self, norm_zero] at hsep
      linarith
    rwa [Finset.card_image_of_injOn hinj]
  · -- Each image vector is a unit vector with exactly `s` nonzero coordinates.
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨S, hS, rfl⟩ := hv
    refine ⟨norm_sparseVec d s hs S (hcard S hS), ?_⟩
    have hane : (Real.sqrt s)⁻¹ ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 (by exact_mod_cast hs)
      positivity
    have hsupp : (Finset.univ.filter fun i => (sparseVec d s S) i ≠ 0) = S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sparseVec_apply]
      by_cases h : i ∈ S <;> simp [h, hane]
    rw [hsupp]; exact le_of_eq (hcard S hS)
  · -- Separation, transported from the support-overlap bound.
    intro u hu v hv huv
    rw [Finset.mem_image] at hu hv
    obtain ⟨S, hS, rfl⟩ := hu
    obtain ⟨S', hS', rfl⟩ := hv
    have hne : S ≠ S' := fun h => huv (by rw [h])
    exact half_le_norm_sparseVec_sub d s hs S S' (hcard S hS) (hcard S' hS') (hov S hS S' hS' hne)

/-- **Packing of sparse unit vectors** (Wainwright Example 5.8): the set of `s`-sparse unit
vectors in `ℝᵈ` contains a `1/2`-separated set `T` with `log |T| ≥ (s/2) log((d−s)/s)`; each
element is a unit vector with at most `s` nonzero coordinates, and any two are at Euclidean
distance `≥ 1/2`.

The cardinality bound is the weakened `log |T| ≥ (s/2) log((d−s)/s) − s·log 2`; the sharp book
constant `(s/2) log((d−s)/s)` is not reachable by an elementary Gilbert–Varshamov volume estimate
(see `exists_bounded_overlap_supports_gv` for the deviation rationale, CLAUDE.md §1).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8. -/
theorem exists_sparse_packing (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) - s * Real.log 2 ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1 ∧ (Finset.univ.filter fun i => v i ≠ 0).card ≤ s) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ :=
  sparse_packing d s hs hsd

end StatLean.Minimaxity
