module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.NestedPartition
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal
public import StatLean.AsymptoticStatistics.EmpiricalProcess.SupMeasurability
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
public import StatLean.AsymptoticStatistics.ForMathlib.SqrtLogProduct

@[expose] public section

/-!
# Chaining proof of vdV Lemma 19.34

This file formalizes the chaining argument at the heart of van der Vaart's
proof of Lemma 19.34 (*Asymptotic Statistics*, p.286-288): given a
`NestedBracketPartition` of a function class `F` (the combinatorial object
built in `NestedPartition.lean`), it produces the chaining bound with a
**universal** constant. The main theorem
`localizedChainBound_of_finiteEntropy` is stated over the localized difference
class.

## The book's argument (vdV p.287)

Fix levels `q₀ ≤ q`. For `f ∈ F`, with `π_q f` the level-`q` representative and
`Δ_q f` the level-`q` oscillation envelope, define the truncation indicators

* `A_q f = 1{Δ_{q₀}f ≤ √n·a_{q₀}, …, Δ_q f ≤ √n·a_q}` (the chain is still
  "small" through level `q`);
* `B_q f = 1{Δ_{q₀}f ≤ √n·a_{q₀}, …, Δ_{q-1}f ≤ √n·a_{q-1}, Δ_q f > √n·a_q}`
  (the first level whose oscillation crosses the threshold `√n·a_q` is exactly
  `q`),

where `a_q = a(2^{−(q−q₀)}δ) = 2^{−(q−q₀)}δ / √(log N_q)`. The head level
`q₀` sits at the coarsest scale `2^{−0}δ = δ`,
level `q₀+k` at `2^{−k}δ`, matching vdV's `2^{−q₀} ≈ δ`). The book's construction
ensures `A_{q₀} f = 1` pointwise. Then, pointwise in `x`,

```
f − π_{q₀}f = Σ_{q>q₀} (f − π_q f)·B_q f + Σ_{q>q₀} (π_q f − π_{q−1}f)·A_{q−1}f.
```

(verified as an algebraic telescope; see `chain_pointwise_decomposition`). Applying
`𝔾ₙ`, taking `supNormOver`, and bounding the two series separately:

* the **B-series** via the per-level finite-class bound (`tight_chain_level_bound`)
  on `{f − π_q f}` plus the envelope-tail truncation (`tight_envelope_truncation_bound`);
* the **A-series** via the per-level bound on the **jump classes**
  `{π_q f − π_{q−1}f}` (cardinality `≤ N_q·N_{q-1}`, sup-norm `≤ 2√n·a_{q-1}` by
  construction, `L²`-norm `≲ 2^{−(q−q₀)}δ` from `diam` + `Δ_L2_le` (offset scale)
  + refinement);
* the **head term** `π_{q₀}f` over `≤ N_{q₀}` functions via `finite_sup_bound`.

Composing with `dyadic_sum_le_bracketingEntropyIntegral` reassembles the
dyadic entropy series into `J_{[]}(δ, F, L²(P))`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.6,
p.286-288.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Jump-class extraction from a nested bracketing partition

The chaining argument's A-series is controlled by the per-level **jump classes**
`{π_q f − π_{q−1}(parent f)}`. We extract the data and bounds the per-level
maximal inequality needs: a parent map, the jump family itself, its cardinality
bookkeeping, measurability under a measurability hypothesis on the representatives,
and the key `L²` bound `‖jump‖_{P,2} ≲ 2^{−(q−q₀)}`. -/

variable {F : Set (Ω → ℝ)} {P : Measure Ω} {q₀ : ℕ} {C : ℝ}

/-- The **parent map** of a nested bracketing partition at level `q`: each
level-`(q+1)` cell sits inside a (chosen) level-`q` cell. This is the index of
that containing cell, extracted via `Classical.choose` from the `refines`
field. -/
noncomputable def NestedBracketPartition.parent
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq (q + 1))) : Fin (B.Nq q) :=
  (B.refines hq i).choose

lemma NestedBracketPartition.cell_succ_subset_parent
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq (q + 1))) :
    B.cell (q + 1) i ⊆ B.cell q (B.parent hq i) :=
  (B.refines hq i).choose_spec

/-- The **iterated ancestor map**: for a level-`q` cell `i` (with `q₀ ≤ q`) and any
intermediate level `p ∈ [q₀, q]`, the index of the level-`p` cell that contains
cell `q i`, obtained by iterating the one-step `parent` map `q − p` times. At
`p = q` it is `i`; at `p < q` it is `parent (ancestor at p+1)`.

This is the book's `Δ_p f` reading: for `f ∈ cell q i`, the level-`p` ancestor cell
is the cell of `f` at level `p`, so the per-`f` truncation indicators `A_q f` / `B_q f`
gate on `Δ_p (ancestor)` rather than on *all* cells `∀ j` (vdV pp.286-288). Defined
by recursion on `q`, with `Fin.cast` handling the boundary branches of the
dependent return type `Fin (B.Nq p)`. -/
noncomputable def NestedBracketPartition.ancestor
    (B : NestedBracketPartition F P q₀ C) :
    ∀ {q : ℕ}, q₀ ≤ q → Fin (B.Nq q) → ∀ p, q₀ ≤ p → p ≤ q → Fin (B.Nq p)
  | 0, _, i, p, _, hpq =>
      Fin.cast (congrArg B.Nq (Nat.le_zero.mp hpq).symm) i
  | q' + 1, _, i, p, hp₀, hpq =>
      if hpq' : p ≤ q' then
        B.ancestor (le_trans hp₀ hpq') (B.parent (le_trans hp₀ hpq') i) p hp₀ hpq'
      else
        Fin.cast (congrArg B.Nq (by omega : q' + 1 = p)) i

/-- At `p = q` the ancestor is the cell itself. -/
@[simp] lemma NestedBracketPartition.ancestor_self
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq q)) :
    B.ancestor hq i q hq le_rfl = i := by
  cases q with
  | zero => simp [NestedBracketPartition.ancestor]
  | succ q' =>
      rw [NestedBracketPartition.ancestor]
      simp only [Nat.succ_le_iff, lt_irrefl]
      rfl

/-- Stepping the ancestor down one level: the level-`p` ancestor of a level-`(q+1)`
cell `i` equals the level-`p` ancestor of its level-`q` parent, for `p ≤ q`. -/
lemma NestedBracketPartition.ancestor_succ_of_le
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq (q + 1))) (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p ≤ q) :
    B.ancestor (le_trans hq (Nat.le_succ q)) i p hp₀ (le_trans hpq (Nat.le_succ q))
      = B.ancestor hq (B.parent hq i) p hp₀ hpq := by
  rw [NestedBracketPartition.ancestor]
  rw [dif_pos hpq]

/-- **Iterated cell inclusion.** A level-`q` cell sits inside its level-`p` ancestor
cell for any `p ∈ [q₀, q]` (iterating `cell_succ_subset_parent`). -/
lemma NestedBracketPartition.cell_subset_ancestor
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq q)) (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p ≤ q) :
    B.cell q i ⊆ B.cell p (B.ancestor hq i p hp₀ hpq) := by
  induction q with
  | zero =>
      have hp0 : p = 0 := Nat.le_zero.mp hpq
      subst hp0
      simp [NestedBracketPartition.ancestor]
  | succ q' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hpq) with hlt | heq
      · -- p ≤ q': go through the parent
        have hpq' : p ≤ q' := Nat.lt_succ_iff.mp hlt
        have hq' : q₀ ≤ q' := le_trans hp₀ hpq'
        calc B.cell (q' + 1) i
            ⊆ B.cell q' (B.parent hq' i) := B.cell_succ_subset_parent hq' i
          _ ⊆ B.cell p (B.ancestor hq' (B.parent hq' i) p hp₀ hpq') :=
              ih hq' (B.parent hq' i) hpq'
          _ = B.cell p (B.ancestor hq i p hp₀ hpq) := by
              rw [B.ancestor_succ_of_le hq' i p hp₀ hpq']
      · -- p = q' + 1: ancestor is `i`
        subst heq
        rw [B.ancestor_self hq i]

/-- **Iterated oscillation domination.** The level-`q` cell oscillation envelope is
pointwise dominated by its level-`p` ancestor's envelope for any `p ∈ [q₀, q]`
(iterating `Δ_succ_le_parent`). -/
lemma NestedBracketPartition.Δ_le_ancestor
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq q)) (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p ≤ q) (x : Ω) :
    B.Δ q i x ≤ B.Δ p (B.ancestor hq i p hp₀ hpq) x := by
  induction q with
  | zero =>
      have hp0 : p = 0 := Nat.le_zero.mp hpq
      subst hp0
      simp [NestedBracketPartition.ancestor]
  | succ q' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hpq) with hlt | heq
      · -- p ≤ q': chain Δ_succ_le_parent then induction
        have hpq' : p ≤ q' := Nat.lt_succ_iff.mp hlt
        have hq' : q₀ ≤ q' := le_trans hp₀ hpq'
        calc B.Δ (q' + 1) i x
            ≤ B.Δ q' (B.parent hq' i) x := B.Δ_succ_le_parent hq' i x
          _ ≤ B.Δ p (B.ancestor hq' (B.parent hq' i) p hp₀ hpq') x :=
              ih hq' (B.parent hq' i) hpq'
          _ = B.Δ p (B.ancestor hq i p hp₀ hpq) x := by
              rw [B.ancestor_succ_of_le hq' i p hp₀ hpq']
      · -- p = q' + 1: ancestor is `i`
        subst heq
        rw [B.ancestor_self hq i]

/-- The **jump function** at level `q+1`, cell `i`: the difference between the
level-`(q+1)` representative and the representative of its parent level-`q`
cell, `π_{q+1} i − π_q (parent i)`. This is the book's chain link
`π_q f − π_{q−1}f` (shifted by one in the index convention). -/
noncomputable def NestedBracketPartition.jump
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq (q + 1))) : Ω → ℝ :=
  fun x => B.π (q + 1) i x - B.π q (B.parent hq i) x

/-- **Cardinality bookkeeping.** The number of level-`(q+1)` jump functions is
`N_{q+1}`, which by the partition's `card_le` is bounded by the product of the
per-level cover cardinalities up to `q+1`. (The cruder book bound
`N_{q+1} ≤ N_{q+1}·N_q` is implied; this product form is what feeds the entropy
comparison.) -/
lemma NestedBracketPartition.jump_card_le
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q + 1) :
    (B.Nq (q + 1) : ℕ) ≤ ∏ p ∈ Finset.Icc q₀ (q + 1), B.coverCard p :=
  B.card_le hq

/-- **Measurability.** Given measurability of every level representative,
each jump function is measurable (difference of two measurables). -/
lemma NestedBracketPartition.jump_measurable
    (B : NestedBracketPartition F P q₀ C)
    (hπ : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    {q : ℕ} (hq : q₀ ≤ q) (i : Fin (B.Nq (q + 1))) :
    Measurable (B.jump hq i) :=
  (hπ (le_trans hq (Nat.le_succ q)) i).sub (hπ hq (B.parent hq i))

/-- **Pointwise sup-norm of the jump in terms of the parent oscillation.**
Both `π_{q+1} i` and `π_q (parent i)` lie in the *same level-`q` cell*
`cell q (parent i)`: the former because `cell (q+1) i ⊆ cell q (parent i)` and
`π_{q+1} i ∈ cell (q+1) i`, the latter because `π_q (parent i) ∈ cell q (parent i)`.
Hence the `diam` field bounds their difference by the parent oscillation
`Δ q (parent i)`. -/
lemma NestedBracketPartition.jump_abs_le
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq (q + 1))) (x : Ω) :
    |B.jump hq i x| ≤ B.Δ q (B.parent hq i) x := by
  have hmem_succ : B.π (q + 1) i ∈ B.cell q (B.parent hq i) :=
    B.cell_succ_subset_parent hq i (B.π_mem (le_trans hq (Nat.le_succ q)) i)
  have hmem_par : B.π q (B.parent hq i) ∈ B.cell q (B.parent hq i) :=
    B.π_mem hq (B.parent hq i)
  exact B.diam hq (B.parent hq i) _ hmem_succ _ hmem_par x

/-- **Key `L²` bound: `‖jump‖_{P,2} ≤ C·2^{−(q − q₀)}`.**
By `jump_abs_le` the jump is pointwise dominated by `Δ q (parent i)`, so by
monotonicity of `eLpNorm` and the partition's `Δ_L2_le` field its `L²` size is
at most `C·2^{−(q − q₀)}` — the offset-scale form that lands the A-series jump at
series-offset `k = q − q₀` on the dyadic-series term `(1/2)^k·δ` (the book absorbs
the constant factor into the universal constant). The conclusion's scale tracks
the structure field `Δ_L2_le`. -/
lemma NestedBracketPartition.jump_L2_le
    (B : NestedBracketPartition F P q₀ C) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq (q + 1))) :
    eLpNorm (B.jump hq i) 2 P ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (q - q₀)) := by
  refine le_trans (eLpNorm_mono_ae_real ?_) (B.Δ_L2_le hq (B.parent hq i))
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_eq_abs]
  exact B.jump_abs_le hq i x

/-! ## The chaining theorem

The chaining bound on `∫⁻ supNormOver F (𝔾ₙ)` follows from a
`NestedBracketPartition`, in the `hChainBound_outer` existential form.

The proof combines envelope bounds, indicator algebra, and dyadic summation
with three substantive parts of the argument on pp.287–288:

* `chain_pointwise_decomposition` — the pointwise telescope identity (verified
  numerically; algebraic);
* `chain_B_series_bound` — the B-series maximal-inequality bound;
* `chain_A_series_bound` — the A-series (jump-class) maximal-inequality bound.

Together with the head-term bound `finite_sup_bound` and the
dyadic-entropy comparison `dyadic_sum_le_bracketingEntropyIntegral` compose
into `chainBound_of_nestedPartition`. -/

/-- **Per-`ξ` pointwise empirical-process bound for a class dominated by an integrable
envelope `Ψ`.** The pointwise (non-integrated) heart of
`supNormProcess_dominated_integral_bound`: the per-`ξ` sup over `𝒢` of the empirical
process is bounded by the EXPLICIT measurable function
`√n·(empAvg Ψ + ∫⁻ Ψ)`.  Exposed separately so the F→F̃ lift can dominate the
(non-measurable) excess sup by this measurable function and split the `lintegral`
via `lintegral_add_right'`, without requiring measurability of the excess supremum. -/
lemma supNormProcess_dominated_pointwise_bound
    {Ξ : Type*} [MeasurableSpace Ξ]
    {X : ℕ → Ξ → Ω}
    (𝒢 : Set (Ω → ℝ)) (Ψ : Ω → ℝ)
    (hdom : ∀ g ∈ 𝒢, ∀ x, |g x| ≤ Ψ x)
    (n : ℕ) (hn : 1 ≤ n) (ω : Ξ) :
    supNormOver 𝒢
        (fun g => empiricalProcess P n (fun j : Fin n => X j.val ω) g)
      ≤ ENNReal.ofReal (Real.sqrt n) *
          (ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ω))
            + ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P) := by
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : 0 ≤ Real.sqrt n := hsn_pos.le
  set T : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P with hT_def
  refine iSup₂_le ?_
  intro g hg
  have h_g_env : ∀ x, |g x| ≤ Ψ x := hdom g hg
  -- (a) `|empAvg g| ≤ empAvg Ψ`
  have h_avg_le : |empiricalAvg g n (fun j : Fin n => X j.val ω)|
      ≤ empiricalAvg Ψ n (fun j : Fin n => X j.val ω) := by
    unfold empiricalAvg
    rw [abs_mul, abs_inv, abs_of_pos hn_pos]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hn_pos.le)
    calc |∑ i : Fin n, g (X i.val ω)|
        ≤ ∑ i : Fin n, |g (X i.val ω)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, Ψ (X i.val ω) :=
          Finset.sum_le_sum (fun i _ => h_g_env (X i.val ω))
  have h_tri_ennreal :
      ENNReal.ofReal
          |empiricalAvg g n (fun j : Fin n => X j.val ω) - ∫ x, g x ∂P|
        ≤ ENNReal.ofReal |empiricalAvg g n (fun j : Fin n => X j.val ω)|
          + ENNReal.ofReal |∫ x, g x ∂P| :=
    le_trans (ENNReal.ofReal_le_ofReal (abs_sub _ _)) ENNReal.ofReal_add_le
  have h_avg_ennreal :
      ENNReal.ofReal |empiricalAvg g n (fun j : Fin n => X j.val ω)|
        ≤ ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) :=
    ENNReal.ofReal_le_ofReal h_avg_le
  have h_int_ennreal : ENNReal.ofReal |∫ x, g x ∂P| ≤ T := by
    have h1 : |∫ x, g x ∂P| ≤ (∫⁻ x, ENNReal.ofReal (|g x|) ∂P).toReal := by
      have hh := MeasureTheory.norm_integral_le_lintegral_norm (μ := P) g
      simpa [Real.norm_eq_abs] using hh
    calc ENNReal.ofReal |∫ x, g x ∂P|
        ≤ ENNReal.ofReal (∫⁻ x, ENNReal.ofReal (|g x|) ∂P).toReal :=
          ENNReal.ofReal_le_ofReal h1
      _ ≤ ∫⁻ x, ENNReal.ofReal (|g x|) ∂P := ENNReal.ofReal_toReal_le
      _ ≤ T := by
          rw [hT_def]
          exact MeasureTheory.lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (h_g_env x))
  have h_assemble :
      ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ω) g|
        = ENNReal.ofReal (Real.sqrt n) *
            ENNReal.ofReal
              |empiricalAvg g n (fun j : Fin n => X j.val ω) - ∫ x, g x ∂P| := by
    unfold empiricalProcess
    rw [abs_mul, abs_of_nonneg hsn_nn, ENNReal.ofReal_mul hsn_nn]
  rw [h_assemble]
  refine mul_le_mul_of_nonneg_left ?_ (zero_le)
  exact le_trans h_tri_ennreal (add_le_add h_avg_ennreal h_int_ennreal)

/-- **Integrated empirical-process bound for a class dominated by an integrable
envelope `Ψ`.** Generalises `tight_envelope_truncation_bound` (which is the special
case `Ψ = |Φ|·1_A`, `𝒢 = {f·1_A}`): if every member of `𝒢` is pointwise dominated by
the measurable nonneg `Ψ`, then the integrated sup of the empirical process over `𝒢`
is at most `4√n·∫⁻ Ψ`.  This uses the same
`signed-average triangle + IdentDistrib-Fubini` mechanism as
`tight_envelope_truncation_bound`, with `|g x| ≤ Ψ x` replacing the
indicator-envelope bound. -/
lemma supNormProcess_dominated_integral_bound
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (𝒢 : Set (Ω → ℝ)) (Ψ : Ω → ℝ) (hΨ_meas : Measurable Ψ) (hΨ_nn : ∀ x, 0 ≤ Ψ x)
    (hdom : ∀ g ∈ 𝒢, ∀ x, |g x| ≤ Ψ x)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ξ, supNormOver 𝒢
        (fun g => empiricalProcess P n (fun j : Fin n => X j.val ξ) g) ∂μ
      ≤ 4 * ENNReal.ofReal (Real.sqrt n) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
  -- Numerical setup.
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : 0 ≤ Real.sqrt n := hsn_pos.le
  set T : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P with hT_def
  set L : ℝ≥0∞ := ∫⁻ ω, supNormOver 𝒢
      (fun g => empiricalProcess P n (fun j : Fin n => X j.val ω) g) ∂μ with hL_def
  -- Step 1: pointwise bound on the supremum (the reusable pointwise lemma).
  have h_pt : ∀ ω : Ξ,
      supNormOver 𝒢
          (fun g => empiricalProcess P n (fun j : Fin n => X j.val ω) g)
        ≤ ENNReal.ofReal (Real.sqrt n) *
            (ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) + T) := by
    intro ω
    exact supNormProcess_dominated_pointwise_bound (P := P) 𝒢 Ψ hdom n hn ω
  -- Step 2: integrate the pointwise bound over μ.
  have hΨ_meas_avg : AEMeasurable
      (fun ω : Ξ => ENNReal.ofReal
        (empiricalAvg Ψ n (fun j : Fin n => X j.val ω))) μ := by
    refine Measurable.aemeasurable ?_
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΨ_meas.comp (hX_meas i.val)
  have h_int : L ≤ ENNReal.ofReal (Real.sqrt n) *
      (∫⁻ ω, ENNReal.ofReal
          (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) ∂μ + T) := by
    rw [hL_def]
    calc ∫⁻ ω, supNormOver 𝒢
            (fun g => empiricalProcess P n (fun j : Fin n => X j.val ω) g) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.sqrt n) *
            (ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) + T) ∂μ :=
          MeasureTheory.lintegral_mono h_pt
      _ = ENNReal.ofReal (Real.sqrt n) *
            ∫⁻ ω, (ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) + T) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ω, ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) ∂μ + ∫⁻ _, T ∂μ) := by
          rw [MeasureTheory.lintegral_add_left' hΨ_meas_avg]
      _ = ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ω, ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) ∂μ + T) := by
          rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
  -- Step 3: `∫⁻ empAvg Ψ dμ ≤ T` via IdentDistrib + Fubini.
  have hΨ_ofReal_meas : Measurable (fun x => ENNReal.ofReal (Ψ x)) := hΨ_meas.ennreal_ofReal
  have h_emp_to_P : ∫⁻ ω, ENNReal.ofReal
      (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) ∂μ ≤ T := by
    have h_pt_le : ∀ ω : Ξ,
        ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ω))
        ≤ ((n : ℝ≥0∞))⁻¹ * ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ω)) := by
      intro ω
      unfold empiricalAvg
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have hn_inv_eq : ENNReal.ofReal ((n : ℝ)⁻¹) = ((n : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
      rw [hn_inv_eq]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hΨ_nn _)]
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hn_pos_nat)
    have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
    calc ∫⁻ ω, ENNReal.ofReal
            (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) ∂μ
        ≤ ∫⁻ ω, ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ω)) ∂μ :=
          MeasureTheory.lintegral_mono h_pt_le
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ω)) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ hinv_ne_top]
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ∫⁻ ω, ENNReal.ofReal (Ψ (X i.val ω)) ∂μ := by
          congr 1
          rw [MeasureTheory.lintegral_finset_sum Finset.univ]
          intro i _
          exact hΨ_ofReal_meas.comp (hX_meas i.val)
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ _i : Fin n, ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have h_id : (μ.map (X i.val)) = P := by
            rw [← hX_law]; exact (hX_idem i.val).map_eq
          rw [← h_id]
          exact (MeasureTheory.lintegral_map hΨ_ofReal_meas (hX_meas i.val)).symm
      _ = ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞)) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      _ = T := by rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul, hT_def]
  -- Step 4: assemble `L ≤ 2√n·T ≤ 4√n·T`.
  calc L ≤ ENNReal.ofReal (Real.sqrt n) *
          (∫⁻ ω, ENNReal.ofReal
              (empiricalAvg Ψ n (fun j : Fin n => X j.val ω)) ∂μ + T) := h_int
    _ ≤ ENNReal.ofReal (Real.sqrt n) * (T + T) :=
        mul_le_mul_of_nonneg_left (add_le_add h_emp_to_P le_rfl) (zero_le)
    _ = 2 * ENNReal.ofReal (Real.sqrt n) * T := by ring
    _ ≤ 4 * ENNReal.ofReal (Real.sqrt n) * T := by gcongr; norm_num

/-- **`∫⁻ empiricalAvg Ψ ≤ ∫⁻ Ψ` via IdentDistrib-Fubini.** For a measurable nonneg `Ψ`
the `μ`-mean of the empirical average of `Ψ` over an iid sample equals the `P`-integral of
`Ψ`; the inequality form is the extracted heart of `supNormProcess_dominated_integral_bound`'s
`h_emp_to_P` (reused by the measurable-majorant chaining bound for the `Btrunc` integral). -/
lemma lintegral_empiricalAvg_le
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (Ψ : Ω → ℝ) (hΨ_meas : Measurable Ψ) (hΨ_nn : ∀ x, 0 ≤ Ψ x)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ξ, ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  set T : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P with hT_def
  have hΨ_ofReal_meas : Measurable (fun x => ENNReal.ofReal (Ψ x)) := hΨ_meas.ennreal_ofReal
  have h_pt_le : ∀ ξ : Ξ,
      ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))
      ≤ ((n : ℝ≥0∞))⁻¹ * ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) := by
    intro ξ
    unfold empiricalAvg
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    have hn_inv_eq : ENNReal.ofReal ((n : ℝ)⁻¹) = ((n : ℝ≥0∞))⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
    rw [hn_inv_eq]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hΨ_nn _)]
  have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hn_pos_nat)
  have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
  calc ∫⁻ ξ, ENNReal.ofReal
          (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ
      ≤ ∫⁻ ξ, ((n : ℝ≥0∞))⁻¹ *
          ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ :=
        MeasureTheory.lintegral_mono h_pt_le
    _ = ((n : ℝ≥0∞))⁻¹ *
          ∫⁻ ξ, ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ := by
        rw [MeasureTheory.lintegral_const_mul' _ _ hinv_ne_top]
    _ = ((n : ℝ≥0∞))⁻¹ *
          ∑ i : Fin n, ∫⁻ ξ, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ := by
        congr 1
        rw [MeasureTheory.lintegral_finset_sum Finset.univ]
        intro i _
        exact hΨ_ofReal_meas.comp (hX_meas i.val)
    _ = ((n : ℝ≥0∞))⁻¹ *
          ∑ _i : Fin n, ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have h_id : (μ.map (X i.val)) = P := by
          rw [← hX_law]; exact (hX_idem i.val).map_eq
        rw [← h_id]
        exact (MeasureTheory.lintegral_map hΨ_ofReal_meas (hX_meas i.val)).symm
    _ = ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞)) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
    _ = T := by rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul, hT_def]

section Assembly

variable {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}

/-- **Truncation threshold of the chaining argument** at level `q`, scale `δ`,
sample size `n`: `a_q = 2^{−(q − q₀)}·δ / (1 + √(log(1 + N_{q+1})))`, with
the regularizer cardinality at the next level `N_{q+1}`. The
dyadic factor is `(1/2)^(q − q₀)` so that the head level `q = q₀` sits at the
coarsest scale `δ` (matching vdV's *"fix `q₀` such that `4δ ≤ 2^{−q₀} ≤ 8δ`"*,
p.287), and level `q₀ + k` at `(1/2)^k·δ`, aligned with the dyadic-series term at
series-offset `k`. The `1 + √(log(1 + N_{q+1}))` regularizer is vdV's
`a_q = 2^{−q}/√Log N_{q+1}` indexing (p.287): the per-level threshold gating `Δ_q`
in the A-chain reads the *child* level's entropy `N_{q+1}`, the form the A-leaf
needs. Nat subtraction `q − q₀` is harmless: all callers have `q₀ ≤ q`. -/
noncomputable def chainThreshold (B : NestedBracketPartition F P q₀ C)
    (δ : ℝ) (q : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (q - q₀) * δ / (1 + Real.sqrt (Real.log (1 + B.Nq (q + 1))))

/-- **Global truncation threshold of the chaining argument** at scale `δ`, sample
size `n`: `a(δ) = δ / (1 + √(log(1 + N_{q₀})))` — the **head/envelope** scale,
whose regularizer card is the head level `N_{q₀}` (vdV p.286, the global
truncation `f · 1{F ≤ √n·a(δ)}`). Unlike `chainThreshold`, this carries no dyadic
offset (it sits at the coarsest scale `δ`) and reads the *head* level's entropy
`N_{q₀}` — exactly the finite-class card the head leaf `chain_head_dyadic_bound`
consumes. The global envelope truncation `truncRep` uses this scale. -/
noncomputable def globalThreshold (B : NestedBracketPartition F P q₀ C)
    (δ : ℝ) : ℝ :=
  δ / (1 + Real.sqrt (Real.log (1 + B.Nq q₀)))

/-- **B-series indicator** at level `q` for `f` in cell `i`: `1` iff `q` is the
*first* level *strictly above* `q₀` whose oscillation envelope `Δ` crosses the
truncation threshold `√n · a_q`. The leading `q₀ < q` conjunct encodes vdV's
`B_{q₀} = 0` (p.287: the head level never carries a B-term — its oscillation is
absorbed into the head finite-sup), so the B-series sums only `q > q₀`. The middle
clause is "all previous levels still small", the last is "level `q` crosses".

**Per-ancestor gate (vdV pp.286-288).** The "all previous levels small" clause reads
`f`'s OWN level-`p` cell-ancestor `B.ancestor … i p …` (the cell of `f` at level `p`),
NOT *all* cells `∀ j` at level `p`. The book's `B_q f` is constant per level-`q` cell
because it reads `Δ_p f` = the value of the level-`p` ancestor envelope; gating on all
cells is strictly stronger and makes the telescope link bound false. -/
noncomputable def chainB (B : NestedBracketPartition F P q₀ C)
    (δ : ℝ) (n q : ℕ) (i : Fin (B.Nq q)) (x : Ω) : Prop :=
  q₀ < q ∧
  (∀ p (hp₀ : q₀ ≤ p) (hpq : p < q),
      B.Δ p (B.ancestor (le_of_lt (lt_of_le_of_lt hp₀ hpq)) i p hp₀ (le_of_lt hpq)) x
        ≤ Real.sqrt n * chainThreshold B δ p) ∧
  (Real.sqrt n * chainThreshold B δ q < B.Δ q i x)

/-- **A-series indicator** at level `q` for `f` in cell `i`: `1` iff *all* levels
`q₀ ≤ p ≤ q` have `f`'s OWN level-`p` cell-ancestor oscillation envelope
`Δ_p (ancestor)` below the threshold `√n · a_p` (the chain is still "small" through
`q`).

**Per-ancestor gate (vdV pp.286-288).** Like `chainB`, this reads `f`'s level-`p`
cell-ancestor `B.ancestor … i p …` (the value `Δ_p f`), NOT all cells `∀ j`. The book's
`A_q f` is the per-`f` indicator constant on each level-`q` cell. -/
noncomputable def chainA (B : NestedBracketPartition F P q₀ C)
    (δ : ℝ) (n q : ℕ) (i : Fin (B.Nq q)) (x : Ω) : Prop :=
  ∀ p (hp₀ : q₀ ≤ p) (hpq : p ≤ q),
    B.Δ p (B.ancestor (le_trans hp₀ hpq) i p hp₀ hpq) x
      ≤ Real.sqrt n * chainThreshold B δ p

/-- **Envelope-truncated level-`m` representative** (vdV p.286, the global
truncation `f · 1{F ≤ √n·a(δ)}`).

The level-`m` representative `π_m i`, multiplied by the indicator of the *global
envelope-truncation set* `{|Φ| ≤ √n · a(δ)}` (where `a(δ) = globalThreshold B δ`
is the head/envelope-scale threshold, card `N_{q₀}`). On the truncation set the
representative is pointwise `L∞`-bounded by `√n · a(δ)` (since `π_m i ∈ F` is
dominated by the envelope `Φ`); off it the truncated representative is `0`. This is
exactly the bounded part that feeds the finite-class maximal inequality
(`tight_chain_level_bound`, whose `hg_bdd` needs a pointwise `L∞` bound that only
the truncated family provides); the unbounded part is the envelope-tail RHS term.
The envelope scale is the *global* `globalThreshold` (card `N_{q₀}`), not the
per-level `chainThreshold q₀` (whose card moved to `N_{q₀+1}`): keeping the head
leaf at card `N_{q₀}` is what makes its RHS an equation.

vdV §19.6 p.286: the global envelope truncation of the chaining argument. -/
noncomputable def truncRep (B : NestedBracketPartition F P q₀ C)
    (Φ : Ω → ℝ) (δ : ℝ) (n m : ℕ) (i : Fin (B.Nq m)) : Ω → ℝ :=
  fun x => B.π m i x
    * Set.indicator {y | |Φ y| ≤ Real.sqrt n * globalThreshold B δ} (1 : Ω → ℝ) x

/-- **A-indicator-gated level-`m` jump function** (vdV p.287, the chain link
`(π_q f − π_{q−1}f) · A_{q−1}f`).

The level-`(m+1)` jump function `B.jump hm i = π_{m+1} i − π_m (parent i)`,
multiplied by the real `0/1` indicator of the A-series event
`chainA B δ n m (B.parent hm i)` for the **level-`m` parent cell** of the
level-`(m+1)` jump index `i` (the chain along `f`'s own ancestor cells is still
"small" through level `m`; `chainA` reads a per-`f` cell index, so the gate uses
the parent cell that both `π_{m+1} i` and `π_m (parent i)` belong to). On the A-set
the jump is pointwise `L∞`-bounded by the parent oscillation `Δ_m ≤ √n · a_m` (via
`jump_abs_le` plus the A-indicator constraint `Δ_m (parent) ≤ √n · a_m`), so the gated
jump has the `L∞` bound `tight_chain_level_bound` consumes; off the A-set it is `0`.
The A-series of the chaining argument sums these gated jumps.

vdV §19.6 p.287: the per-level oscillation indicators `A_q` gating the chain links. -/
noncomputable def truncJump (B : NestedBracketPartition F P q₀ C)
    (δ : ℝ) (n : ℕ) {m : ℕ} (hm : q₀ ≤ m)
    (i : Fin (B.Nq (m + 1))) : Ω → ℝ :=
  fun x => B.jump hm i x
    * Set.indicator {y | chainA B δ n m (B.parent hm i) y} (1 : Ω → ℝ) x

/-- **B-series truncated cell-oscillation family** (vdV p.287, the B-series
envelope `Δ_q f · B_q f`).

The level-`q` oscillation envelope `B.Δ q i`, multiplied by the real `0/1`
indicator of the B-series event `chainB B δ n q i` (level `q` is the *first*
whose oscillation crosses the threshold `√n·a_q`). On the B-set the oscillation
is pointwise `L∞`-bounded by `√n·a_{q-1}` (the chain was still small through
`q-1`); its `L²`-size is `≤ C·2^{−(q−q₀)}` via `Δ_L2_le` (offset scale). This is
the correct
B-series envelope: unlike the representative `π_q i`, the oscillation `Δ_q`
*does* have a decaying `L²` bound, which is what the per-level finite-class
maximal inequality (`tight_chain_level_bound`, whose `hg_var` needs the `L²`
size) consumes for the B-series; off the B-set it is `0`.

vdV §19.6 p.287: the B-series envelope `Δ_q f · B_q f`. -/
noncomputable def truncOsc (B : NestedBracketPartition F P q₀ C)
    (δ : ℝ) (n q : ℕ) (i : Fin (B.Nq q)) : Ω → ℝ :=
  fun x => B.Δ q i x
    * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x

/-- **Pointwise telescope identity (vdV p.287), finite-truncation form.**

For a representative selection `r : ℕ → ℝ` with `r q = π_q f x` and a *break
level* `q₁ ≥ q₀` (the first level whose oscillation crosses the threshold, or any
upper cutoff in the "all small" case), the book's decomposition

```
f x − π_{q₀}f x = (f x − π_{q₁}f x) + Σ_{q=q₀+1}^{q₁} (π_q f x − π_{q−1}f x)
```

is the algebraic telescope: the single B-term `(f − π_{q₁})` at the break, plus
the A-telescope of chain links up to `q₁`, reassembles `f − π_{q₀}`.

This finite form is exactly what the chaining bound consumes pointwise (the two
series in the displayed decomposition are finite because, for each `x`, either
all `B_q = 0` or there is a unique `q₁` truncating them). Stated abstractly over
the real sequence `r` and value `fx` to isolate the telescope content.

vdV §19.6 p.287, the displayed decomposition. -/
theorem chain_pointwise_telescope (fx : ℝ) (r : ℕ → ℝ) {q₀ q₁ : ℕ} (hq : q₀ ≤ q₁) :
    fx - r q₀ = (fx - r q₁) + ∑ q ∈ Finset.Ioc q₀ q₁, (r q - r (q - 1)) := by
  -- The A-telescope `∑_{q∈Ioc q₀ q₁} (r q − r (q−1)) = r q₁ − r q₀`.
  have htel : ∑ q ∈ Finset.Ioc q₀ q₁, (r q - r (q - 1)) = r q₁ - r q₀ := by
    induction q₁ with
    | zero => simp [Nat.le_zero.mp hq]
    | succ m ih =>
      rcases Nat.lt_or_ge q₀ (m + 1) with hlt | hge
      · -- q₀ ≤ m, peel off the top term q = m+1
        have hq₀m : q₀ ≤ m := Nat.lt_succ_iff.mp hlt
        rw [Finset.sum_Ioc_succ_top hq₀m, ih hq₀m]
        simp
      · -- q₀ = m+1, empty range
        have : Finset.Ioc q₀ (m + 1) = ∅ := by
          rw [Finset.Ioc_eq_empty]; omega
        rw [this, Finset.sum_empty]
        have : q₀ = m + 1 := le_antisymm hq hge
        rw [this]; ring
  rw [htel]; ring

/-! ### Sub-additivity glue for `supNormOver`

The chaining decomposition writes the empirical-process evaluator `f ↦ 𝔾ₙ f`
as a finite sum of pieces (head + telescope links + remainder). Taking
`supNormOver F` of a sum is sub-additive because `supNormOver` is a supremum of
`ENNReal.ofReal |·|` and both `|·|` (triangle) and `ENNReal.ofReal` are
sub-additive. These two glue lemmas are theorem-agnostic facts about
`supNormOver`. -/

omit [MeasurableSpace Ω] in
/-- **Sub-additivity of `supNormOver` over a binary sum.**
`supNormOver F (z₁ + z₂) ≤ supNormOver F z₁ + supNormOver F z₂`, by the pointwise
triangle inequality `|z₁ f + z₂ f| ≤ |z₁ f| + |z₂ f|` lifted through
`ENNReal.ofReal` and bounded by the two suprema. -/
lemma supNormOver_add_le (F : Set (Ω → ℝ)) (z₁ z₂ : (Ω → ℝ) → ℝ) :
    supNormOver F (fun f => z₁ f + z₂ f)
      ≤ supNormOver F z₁ + supNormOver F z₂ := by
  refine iSup₂_le (fun f hf => ?_)
  calc ENNReal.ofReal |z₁ f + z₂ f|
      ≤ ENNReal.ofReal (|z₁ f| + |z₂ f|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ ≤ ENNReal.ofReal |z₁ f| + ENNReal.ofReal |z₂ f| := ENNReal.ofReal_add_le
    _ ≤ supNormOver F z₁ + supNormOver F z₂ :=
        add_le_add (le_supNormOver hf) (le_supNormOver hf)

omit [MeasurableSpace Ω] in
/-- **Sub-additivity of `supNormOver` over a finite sum.**
`supNormOver F (fun f => ∑ i ∈ s, z i f) ≤ ∑ i ∈ s, supNormOver F (z i)`.
Iterated `supNormOver_add_le` over the index `Finset`. -/
lemma supNormOver_sum_le {ι : Type*} (F : Set (Ω → ℝ)) (s : Finset ι)
    (z : ι → (Ω → ℝ) → ℝ) :
    supNormOver F (fun f => ∑ i ∈ s, z i f)
      ≤ ∑ i ∈ s, supNormOver F (z i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      -- `supNormOver F (fun _ => 0) = 0`
      refine iSup₂_le (fun f hf => ?_)
      simp
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      refine le_trans (supNormOver_add_le F (z a) (fun f => ∑ i ∈ s, z i f)) ?_
      exact add_le_add le_rfl ih

/-! ### Chaining bound in dyadic-series form (vdV p.287-288)

The genuine chaining bound of vdV Lemma 19.34, before substituting the dyadic
entropy series by the bracketing entropy integral. From a `NestedBracketPartition`
of `F` there is a **universal** constant `c` (independent of the envelope `Φ`, the
scale `δ`, and the sample size `n`) with

```
∫⁻ supNormOver F (𝔾ₙ) ≤ c·(dyadic entropy series at δ) + c·√n·(envelope tail at δ√n).
```

The universal constant is placed *outside* the `∀ Φ ∀ δ ∀ n` quantifiers. The
right-hand side is the sum of the book's three contributions:

* the **B-series** `Σ_q (f − π_q f)·B_q f`, bounded by `tight_chain_level_bound`
  (per-level finite-class bound on `{f − π_q f}`: cardinality `N_q`, sup-norm
  `≤ √n·a_q`, `L²`-norm `≤ 2·2^{−(q−q₀)}δ` offset scale)
  + `tight_envelope_truncation_bound`;
* the **A-series** `Σ_q (π_q f − π_{q−1}f)·A_{q−1}f`, bounded via
  `tight_chain_level_bound` on the **jump classes** `{π_q f − π_{q−1}f}` (using
  `jump_card_le`, `jump_measurable`, `jump_L2_le`) + `tight_chain_telescope_bound`;
* the **head term** `π_{q₀}f` over `≤ N_{q₀}` functions (`finite_sup_bound`).

The pointwise decomposition tying these together is `chain_pointwise_telescope`.

vdV §19.6 p.287-288. The substantive chaining content is split into four named
lemmas below — a pointwise-telescope/`supNormOver`/integrate **split**
(`chain_supnorm_le_three_part`) reducing the LHS to head + B-series + A-series
integral contributions, and three **dyadic-series bounds** (`chain_head_dyadic_bound`,
`chain_B_dyadic_bound`, `chain_A_dyadic_bound`) bounding each contribution by a
universal multiple of the dyadic entropy series (the head/A pieces) or the series
plus the envelope tail (the B piece). Combining the four constants gives the
stated bound. The dyadic-to-`J` comparison and the `n = 0` case are handled by
`hChainBound_outer_of_nestedPartition`. -/

/-- **Per-level finite-sup contribution at level `m`** (envelope-truncated).
`∫⁻ ξ, ⨆ i, |𝔾ₙ(truncRep i)| ∂μ` — the expected supremum of the empirical process
over the `N_m` *envelope-truncated* level-`m` representatives
`truncRep B Φ δ n m i = π_m i · 1{|Φ| ≤ √n·a(δ)}` (global scale `globalThreshold`,
card `N_{q₀}`). Truncation is baked in (gaining
the `Φ`/`δ` parameters) precisely so the per-level maximal inequality
`tight_chain_level_bound` can discharge its pointwise `L∞` hypothesis `hg_bdd`,
which the raw (un-truncated) representatives cannot supply. The chaining argument's
head (`m = q₀`) and link contributions are dominated by these per-level finite
sups. -/
noncomputable def levelRepSup (B : NestedBracketPartition F P q₀ C)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (X : ℕ → Ξ → Ω)
    (Φ : Ω → ℝ) (δ : ℝ) (n : ℕ) (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ ξ, ⨆ i : Fin (B.Nq m),
      ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (truncRep B Φ δ n m i)| ∂μ

/-- **Per-level jump-sup contribution at level `m`** (A-indicator-gated).
`∫⁻ ξ, ⨆ i, |𝔾ₙ(truncJump i)| ∂μ` — the expected supremum of the empirical process
over the `N_{m+1}` *A-gated* level-`(m+1)` jump functions
`truncJump B δ n hm i = (π_{m+1} i − π_m(parent i)) · 1{chainA B δ n m}`. The
A-indicator is baked in (gaining the `δ` parameter) so that
`tight_chain_level_bound`'s `hg_bdd` is dischargeable from `jump_abs_le` plus the
A-set constraint `Δ_m ≤ √n·a_m`. The A-series of the chaining argument sums these.
Unlike `levelRepSup`, no `Φ` parameter is carried: the A-indicator `chainA` is
defined purely from the partition oscillations `Δ`, independent of the envelope. -/
noncomputable def levelJumpSup (B : NestedBracketPartition F P q₀ C)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (X : ℕ → Ξ → Ω)
    (δ : ℝ) (n : ℕ) {m : ℕ} (hm : q₀ ≤ m) : ℝ≥0∞ :=
  ∫⁻ ξ, ⨆ i : Fin (B.Nq (m + 1)),
      ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (truncJump B δ n hm i)| ∂μ

/-- **Per-level oscillation-sup contribution at level `q`** (B-indicator-gated).
`∫⁻ ξ, ⨆ i, |𝔾ₙ(truncOsc i)| ∂μ` — the expected supremum of the empirical process
over the `N_q` *B-gated* level-`q` cell oscillations
`truncOsc B δ n q i = Δ_q i · 1{chainB B δ n q i}`. This is the correct B-series
envelope (vdV p.287): the cell oscillation `Δ_q` carries a decaying `L²` bound
(`Δ_L2_le`: `‖Δ_q‖_{P,2} ≤ C·2^{−(q−q₀)}`, offset scale) that the representatives
`π_q i` lack, so
`tight_chain_level_bound`'s `hg_var` (`L²` size) is dischargeable here for the
B-series — unlike `levelRepSup`, which is the HEAD family. The B-indicator
`chainB` is defined purely from the partition oscillations `Δ`, independent of
the envelope, so no `Φ` parameter is carried. -/
noncomputable def levelOscSup (B : NestedBracketPartition F P q₀ C)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (X : ℕ → Ξ → Ω)
    (δ : ℝ) (n q : ℕ) : ℝ≥0∞ :=
  ∫⁻ ξ, ⨆ i : Fin (B.Nq q),
      ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (truncOsc B δ n q i)| ∂μ

/-- **Head-term dyadic bound (vdV p.287).**

The head of the chain, `f ↦ 𝔾ₙ(π_{q₀}f)`, is dominated by the finite-class
supremum `⨆ i, |𝔾ₙ(π_{q₀} i)|` over the `N_{q₀}` level-`q₀` representatives
(`levelRepSup` at `m = q₀`). By the finite-class supremum bound
(`finite_sup_bound` / Lem 19.33) with truncation threshold `√n·a_{q₀}` (at the
offset scale `2^{−(q₀−q₀)}δ = δ`) and `L²`-size `≤ 2δ` (= `‖f‖ + ‖Δ_{q₀}‖ ≤
δ + C·(1/2)^0`, the offset `q₀−q₀ = 0`), its expected value lands on the **coarsest**
(series-offset `k = 0`) dyadic term `ofReal(δ)·entropyIntegrand(δ)`, dominated by
the full dyadic entropy series. The `coverCard → bracketingNumber` comparison at
`p = q₀` (`coverCard_le` at offset scale `(1/2)^0·δ = δ` + `Real.sqrt_log_prod_le_sum_one_add`
+ `entropyIntegrand` def) converts `√(log(1 + N_{q₀}))` to the integrand value at `δ`.

The head term is the only one of the three that reads vdV's two standing
parameters directly: `hF_L2` is the standing `‖f‖_{P,2} ≤ δ` (vdV's `Pf² ≤ δ²`,
p.286), used to bound
`‖π_{q₀}f‖_{P,2} ≤ ‖f‖ + ‖Δ_{q₀}‖`; `hq₀` is vdV's *"fix an integer `q₀` such that
`4δ ≤ 2^{−q₀} ≤ 8δ`"* (p.287), used to put the truncation threshold `√n·a_{q₀}` at
the right dyadic scale. `hF_ne` (`F.Nonempty`) supplies the `[Nonempty (Fin (B.Nq q₀))]`
that `tight_chain_level_bound`'s finite-class supremum needs.

vdV §19.6 p.287, the head term `π_{q₀}f`. -/
theorem chain_head_dyadic_bound
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : Set (Ω → ℝ)) (q₀ : ℕ) (C : ℝ) (B : NestedBracketPartition F P q₀ C)
        (_hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
        (_hF_ne : F.Nonempty),
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δ : ℝ}, 0 < δ → C = δ →
          (∀ f ∈ F, eLpNorm f 2 P ≤ ENNReal.ofReal δ) →
          (4 * δ ≤ (1 / 2 : ℝ) ^ q₀ ∧ (1 / 2 : ℝ) ^ q₀ ≤ 8 * δ) →
          ∀ (n : ℕ), 1 ≤ n →
            levelRepSup B μ X Φ δ n q₀
              ≤ ENNReal.ofReal c
                  * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                      * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
  classical
  -- Hoist the uniform finite-class chaining constant `K` before all the `∀`s.
  obtain ⟨K, hK_pos, hb⟩ :=
    tight_chain_level_bound_uniform P hX_meas hX_iindep hX_idem hX_law
  refine ⟨2 * K, by positivity, ?_⟩
  intro F q₀ C B hπ_meas hF_ne Φ hΦ_meas hΦ_env hΦ_memLp δ hδ hCδ hF_L2 hq₀ n hn
  -- A nonempty cell index at level `q₀` (the finite-class supremum needs it).
  have hNq_ne : Nonempty (Fin (B.Nq q₀)) := by
    obtain ⟨f, hf⟩ := hF_ne
    obtain ⟨i, _⟩ := B.cover (le_refl q₀) f hf
    exact ⟨i⟩
  -- The head family: the envelope-truncated level-`q₀` representatives.
  set g : Fin (B.Nq q₀) → Ω → ℝ := fun i => truncRep B Φ δ n q₀ i with hg_def
  -- Measurability of each `g i`.
  have hg_meas : ∀ i, Measurable (g i) := by
    intro i
    refine (hπ_meas (le_refl q₀) i).mul ?_
    exact measurable_one.indicator (measurableSet_le hΦ_meas.norm measurable_const)
  -- Card of the level-`q₀` index type.
  have hcard : Fintype.card (Fin (B.Nq q₀)) = B.Nq q₀ := Fintype.card_fin _
  -- Apply the uniform leaf with scale `ε = δ`.
  have hbnd := hb g hg_meas (ε := δ) hδ n hn ?_ ?_
  · -- Bridge `levelRepSup` (⨆ ofReal|·|) to the leaf LHS (ofReal (⨆ |·|)),
    -- then bound the leaf RHS by the `q = 0` term of the dyadic series.
    -- Here `levelRepSup = ∫⁻ ⨆ ofReal|𝔾ₙ(g i)|` by `hg_def` and `truncRep`,
    -- and `⨆ ofReal|·| ≤ ofReal(⨆ |·|)` pointwise, giving `levelRepSup ≤ hbnd LHS`.
    have hLHS : levelRepSup B μ X Φ δ n q₀
        ≤ ∫⁻ ω : Ξ,
            ENNReal.ofReal (⨆ i, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ := by
      refine lintegral_mono (fun ξ => ?_)
      refine iSup_le (fun i => ?_)
      refine ENNReal.ofReal_le_ofReal ?_
      exact le_ciSup (Finite.bddAbove_range
        (fun i : Fin (B.Nq q₀) =>
          |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|)) i
    refine hLHS.trans (hbnd.trans ?_)
    -- Bound the entropy weight `√log(1 + N_{q₀})` by `entropyIntegrand δ`.
    -- `(N_{q₀} : ℕ∞) ≤ coverCard q₀ ≤ bracketingNumber δ`, monotone through entropyWeight.
    have hweight_le :
        ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))))
          ≤ entropyIntegrand δ F P := by
      have hcard_le : (B.Nq q₀ : ℕ∞) ≤ (B.coverCard q₀ : ℕ∞) := by
        have h := B.card_le (le_refl q₀)
        rw [Finset.Icc_self, Finset.prod_singleton] at h
        exact_mod_cast h
      have hcover_le : (B.coverCard q₀ : ℕ∞) ≤ bracketingNumber δ F 2 P := by
        have h := B.coverCard_le (le_refl q₀)
        simpa [Nat.sub_self, pow_zero, one_mul, hCδ] using h
      calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))))
          = entropyWeight (B.Nq q₀ : ℕ∞) := (entropyWeight_coe _).symm
        _ ≤ entropyWeight (bracketingNumber δ F 2 P) :=
            entropyWeight_mono (le_trans hcard_le hcover_le)
        _ = entropyIntegrand δ F P := rfl
    -- The right-hand side `ofReal(K·δ·√log(1+N_{q₀}))` is below the `q = 0` series term
    -- `ofReal(δ)·entropyIntegrand(δ)` times `ofReal(2K)`, hence below the whole series.
    have hcard_eq : (Fintype.card (Fin (B.Nq q₀)) : ℝ) = (B.Nq q₀ : ℝ) := by
      rw [hcard]
    have hterm_le :
        ENNReal.ofReal (K * δ * Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq q₀)) : ℝ))))
          ≤ ENNReal.ofReal (2 * K)
              * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (0 : ℕ) * δ)
                  * entropyIntegrand ((1 / 2 : ℝ) ^ (0 : ℕ) * δ) F P) := by
      rw [hcard_eq]
      simp only [pow_zero, one_mul]
      -- `ofReal(K·δ·w) = ofReal(2K)·(ofReal δ · ofReal w)` then `ofReal w ≤ integrand`.
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      calc ENNReal.ofReal K * ENNReal.ofReal δ
              * ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ))))
          ≤ ENNReal.ofReal (2 * K) * ENNReal.ofReal δ * entropyIntegrand δ F P :=
            mul_le_mul'
              (mul_le_mul'
                (ENNReal.ofReal_le_ofReal (by linarith [hK_pos.le])) le_rfl)
              hweight_le
        _ = ENNReal.ofReal (2 * K) * (ENNReal.ofReal δ * entropyIntegrand δ F P) := by
            rw [mul_assoc]
    refine hterm_le.trans ?_
    gcongr
    exact ENNReal.le_tsum 0
  · -- hg_bdd : pointwise L∞ truncation bound.
    -- The RHS equals `√n · globalThreshold B δ` (the head/envelope scale at card
    -- `Nq q₀`, and `Fintype.card (Fin (Nq q₀)) = Nq q₀`); on the truncation set
    -- `g i = π_{q₀} i` is dominated by `|Φ| ≤ √n · globalThreshold`, off it is `0`.
    intro i ω
    have hπ_F : B.π q₀ i ∈ F :=
      B.cell_subset (le_refl q₀) i (B.π_mem (le_refl q₀) i)
    have hRHS_eq : Real.sqrt n * δ
          / (1 + Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq q₀)) : ℝ))))
        = Real.sqrt n * globalThreshold B δ := by
      rw [globalThreshold, hcard]
      ring
    rw [hRHS_eq, hg_def]
    simp only [truncRep]
    by_cases hω : ω ∈ {y | |Φ y| ≤ Real.sqrt n * globalThreshold B δ}
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      calc |B.π q₀ i ω| ≤ Φ ω := hΦ_env _ hπ_F ω
        _ ≤ |Φ ω| := le_abs_self _
        _ ≤ Real.sqrt n * globalThreshold B δ := hω
    · rw [Set.indicator_of_notMem hω, mul_zero, abs_zero]
      -- RHS `≥ 0`.
      have : 0 ≤ Real.sqrt n * globalThreshold B δ := by
        refine mul_nonneg (Real.sqrt_nonneg _) ?_
        rw [globalThreshold]
        positivity
      linarith
  · -- hg_var : L² size bound `≤ (2δ)²`.
    -- `g i = π_{q₀} i · 1{…}`, so `(g i)² ≤ (π_{q₀} i)²` pointwise (indicator ≤ 1);
    -- `π_{q₀} i ∈ F`, hence `‖π_{q₀} i‖_{P,2} ≤ δ` (hF_L2), giving `∫ (π_{q₀} i)² ≤ δ²`.
    intro i
    have hπ_F : B.π q₀ i ∈ F :=
      B.cell_subset (le_refl q₀) i (B.π_mem (le_refl q₀) i)
    -- `π_{q₀} i ∈ MemLp 2 P` from its finite eLpNorm and measurability.
    have hπ_memLp : MemLp (B.π q₀ i) 2 P := by
      refine ⟨(hπ_meas (le_refl q₀) i).aestronglyMeasurable, ?_⟩
      exact lt_of_le_of_lt (hF_L2 _ hπ_F) ENNReal.ofReal_lt_top
    -- `∫ (π_{q₀} i)² ≤ δ²` from `‖π_{q₀} i‖_{P,2} ≤ δ`.  Bridge `∫ f²` and the
    -- `eLpNorm` via `MemLp.eLpNorm_eq_integral_rpow_norm` (inlined: no cross-import
    -- of the QMD-specific `sqrt_integral_sq_eq_eLpNorm_toReal`).
    have hπ_sq_le : ∫ ω, (B.π q₀ i ω) ^ 2 ∂P ≤ δ ^ 2 := by
      have hnn : 0 ≤ ∫ ω, (B.π q₀ i ω) ^ 2 ∂P :=
        MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
      have hsqrt_eq : Real.sqrt (∫ ω, (B.π q₀ i ω) ^ 2 ∂P)
          = (eLpNorm (B.π q₀ i) 2 P).toReal := by
        rw [hπ_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
        have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
        have h_int_eq :
            (fun ω => ‖B.π q₀ i ω‖ ^ (2 : ℝ≥0∞).toReal) = (fun ω => B.π q₀ i ω ^ 2) := by
          funext ω; rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
        rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2,
          Real.sqrt_eq_rpow]
        norm_num
      have hsqrt_le : Real.sqrt (∫ ω, (B.π q₀ i ω) ^ 2 ∂P) ≤ δ := by
        rw [hsqrt_eq]
        calc (eLpNorm (B.π q₀ i) 2 P).toReal
            ≤ (ENNReal.ofReal δ).toReal := ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne
              (hF_L2 _ hπ_F)
          _ = δ := ENNReal.toReal_ofReal hδ.le
      nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, (B.π q₀ i ω) ^ 2 ∂P)]
    -- `∫ (g i)² ≤ ∫ (π_{q₀} i)²` by pointwise domination (indicator ≤ 1).
    have hgsq_le_πsq : ∫ ω, (g i ω) ^ 2 ∂P ≤ ∫ ω, (B.π q₀ i ω) ^ 2 ∂P := by
      refine MeasureTheory.integral_mono_of_nonneg
        (Eventually.of_forall (fun ω => sq_nonneg _)) (hπ_memLp.integrable_sq) ?_
      refine Eventually.of_forall (fun ω => ?_)
      rw [hg_def]
      simp only [truncRep]
      rcases Set.indicator_eq_zero_or_self
          {y | |Φ y| ≤ Real.sqrt n * globalThreshold B δ} (1 : Ω → ℝ) ω with h0 | h1
      · rw [h0, mul_zero]
        simpa using sq_nonneg (B.π q₀ i ω)
      · rw [h1, Pi.one_apply, mul_one]
    -- chain through `δ² ≤ (2δ)²`.
    refine hgsq_le_πsq.trans (hπ_sq_le.trans ?_)
    nlinarith [hδ.le]

/-- **B-series `∑' q, levelOscSup` dyadic bound (vdV p.287, the `Σ_{q>q₀}‖𝔾ₙ Δ_q f B_q f‖_F`
sum).**

The B-series proper: the sum over levels of the expected supremum of the
empirical process over the B-gated cell oscillations `truncOsc B δ n q i =
Δ_q i · 1{chainB B δ n q i}`. Per level `q`, vdV (p.287) applies Lemma 19.33
(`tight_chain_level_bound`) to the finite class `{truncOsc i : i : Fin (N_q)}`:

* cardinality `N_q ≤ ∏_{p∈[q₀,q]} coverCard p` (`B.card_le`), whose
  `√log(1 + N_q) ≤ Σ_p √log(1 + coverCard p) ≤ entropyIntegrand((1/2)^{q−q₀}·δ)`
  collapse uses `B.coverCard_le` (offset scale `(1/2)^{p−q₀}·C`) +
  `Real.sqrt_log_prod_le_sum_one_add` + `entropyWeight_mono`;
* `L∞`-bound `|truncOsc i x| ≤ √n·a_{q-1}`: *"because the partitions are nested,
  `Δ_q f B_q f ≤ Δ_{q-1}f B_q f ≤ √n a_{q-1}` trivially"* (vdV p.287, lines after
  the `A_q/B_q` display) — the chain was still small through `q-1` on the
  B-support, and the level-`q` oscillation is dominated by its parent's by
  nesting, using the constitutive field `B.Δ_succ_le_parent`;
* `L²`-bound `‖truncOsc i‖_{P,2} ≤ ‖Δ_q i‖_{P,2} ≤ C·2^{−(q−q₀)}` (`B.Δ_L2_le`,
  offset scale, `C = δ`, plus `eLpNorm_mono_ae_real` since the indicator is `≤ 1`).

Summing the per-level bounds and reindexing `q = q₀ + k`
(`ENNReal.tsum_pow_half_sum_Icc_le`) reassembles the dyadic entropy series
`Σ_k (1/2)^k·δ·entropyIntegrand((1/2)^k·δ)` (the offset `k = q − q₀` lands each
level on its matching series term).

The `L∞` nesting monotonicity `Δ_q i ≤ Δ_{q-1}(parent i)` is the constitutive
field `Δ_succ_le_parent`, established by the min-of-widths construction
`buildΔ` and `assignTuple_restrict`. The `1 +`-regularized cardinality estimate is
`Real.sqrt_log_prod_le_sum_one_add`; the per-level maximal inequality is vdV
Lemma 19.33 applied to `{truncOsc i}`.

vdV §19.6 p.287, the B-series `Σ_{q>q₀} ‖𝔾ₙ Δ_q f B_q f‖_F`. -/
private theorem chain_B_levelOscSup_dyadic_bound
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : Set (Ω → ℝ)) (q₀ : ℕ) (C : ℝ) (B : NestedBracketPartition F P q₀ C)
        (_hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
        (_hF_ne : F.Nonempty),
      ∀ {δ : ℝ}, 0 < δ → C = δ → ∀ (n : ℕ), 1 ≤ n →
        (∑' q : ℕ, levelOscSup B μ X δ n q)
          ≤ ENNReal.ofReal c
              * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                  * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
  classical
  -- Hoist the uniform finite-class chaining constant `K` before all the `∀`s.
  obtain ⟨K, hK_pos, hb⟩ :=
    tight_chain_level_bound_uniform P hX_meas hX_iindep hX_idem hX_law
  -- The universal constant is `4·K`; the `q₀`-dependence of the per-level scale
  -- `(1/2)^(q−q₀−1)` cancels against the `(2⁻¹)^{q₀}` gained in the reindex
  -- (`2^{q₀+1} · 2 · (1/2)^{q₀} = 4`).
  refine ⟨4 * K, by positivity, ?_⟩
  intro F q₀ C B hπ_meas hF_ne δ hδ hCδ n hn
  -- Series-coefficient family `b p = ofReal δ · entropyIntegrand((1/2)^{p−q₀}δ)`
  -- for `p ≥ q₀`, else `0`.  After the dyadic reindex `p = q₀ + j` it becomes the
  -- series term exactly (no antitonicity slack needed).
  set b : ℕ → ℝ≥0∞ := fun p =>
    if q₀ ≤ p then
      ENNReal.ofReal δ * entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P
    else 0 with hb_def
  -- A nonempty cell index at any level `q ≥ q₀` (the finite-class supremum needs it).
  have hNq_ne : ∀ {q : ℕ}, q₀ ≤ q → Nonempty (Fin (B.Nq q)) := by
    intro q hq
    obtain ⟨f, hf⟩ := hF_ne
    obtain ⟨i, _⟩ := B.cover hq f hf
    exact ⟨i⟩
  -- Numerical preliminaries.
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  -- `(2⁻¹ : ℝ≥0∞)^k = ofReal((1/2)^k)` (reused throughout the dyadic algebra).
  have hofpow : ∀ k : ℕ, (2⁻¹ : ℝ≥0∞) ^ k = ENNReal.ofReal ((1/2 : ℝ) ^ k) := by
    intro k
    rw [ENNReal.ofReal_pow (by norm_num), show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  -- =====================================================================
  -- STEP 1 — Per-level bound.
  -- For `q ≤ q₀` the summand vanishes (`chainB` has the false `q₀ < q` conjunct);
  -- for `q > q₀` the uniform leaf at scale `ε_q = (1/2)^{q−q₀−1}·δ` discharges it,
  -- and the cardinality `√log(1+N_q)` collapses to `∑_{p∈Icc q₀ q} b p`.
  -- =====================================================================
  have hlevel : ∀ q : ℕ,
      levelOscSup B μ X δ n q
        ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
            * ((2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, b p)) := by
    intro q
    by_cases hq0q : q₀ < q
    · -- `q > q₀`: the genuine per-level maximal inequality.  Write `q = m + 1` with
      -- `q₀ ≤ m` to make the parent level `m = q − 1` a syntactic predecessor (no casts).
      obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos
        (lt_of_le_of_lt q₀.zero_le hq0q)).symm⟩
      have hq0_le : q₀ ≤ m + 1 := le_of_lt hq0q
      have hq1_le : q₀ ≤ m := Nat.lt_succ_iff.mp hq0q
      have hNq_ne_q : Nonempty (Fin (B.Nq (m + 1))) := hNq_ne hq0_le
      -- The level-`(m+1)` B-gated oscillation family.
      set g : Fin (B.Nq (m + 1)) → Ω → ℝ := fun i => truncOsc B δ n (m + 1) i with hg_def
      -- Measurability of `{x | chainB …}` (inlined; under the per-ancestor gate each
      -- level `p < m+1` contributes ONE cell, `f`'s level-`p` ancestor, not all `∀ j`).
      have hchainB_meas : ∀ i : Fin (B.Nq (m + 1)),
          MeasurableSet {x | chainB B δ n (m + 1) i x} := by
        intro i
        have hset : {x | chainB B δ n (m + 1) i x}
            = {_x : Ω | q₀ < m + 1}
              ∩ ((⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p < m + 1),
                    {x | B.Δ p (B.ancestor (le_of_lt (lt_of_le_of_lt hp₀ hpq)) i p hp₀
                            (le_of_lt hpq)) x
                        ≤ Real.sqrt n * chainThreshold B δ p})
                ∩ {x | Real.sqrt n * chainThreshold B δ (m + 1) < B.Δ (m + 1) i x}) := by
          ext x
          simp only [chainB, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
        rw [hset]
        refine MeasurableSet.inter (MeasurableSet.const _) ?_
        refine MeasurableSet.inter ?_ (measurableSet_lt measurable_const (B.Δ_meas hq0_le i))
        refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
          MeasurableSet.iInter (fun hpq => ?_)))
        exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
      -- Measurability of each `g i`.
      have hg_meas : ∀ i, Measurable (g i) := by
        intro i
        rw [hg_def]
        refine (B.Δ_meas hq0_le i).mul ?_
        exact measurable_one.indicator (hchainB_meas i)
      -- Scale `ε = (1/2)^{(m+1)−q₀−1}·δ = (1/2)^{m−q₀}·δ`.
      set ε : ℝ := (1/2 : ℝ) ^ (m - q₀) * δ with hε_def
      have hε_pos : 0 < ε := by rw [hε_def]; positivity
      -- card = `N_{m+1}`.
      have hcard : Fintype.card (Fin (B.Nq (m + 1))) = B.Nq (m + 1) := Fintype.card_fin _
      -- Apply the uniform leaf.
      have hbnd := hb g hg_meas (ε := ε) hε_pos n hn ?_ ?_
      · -- Bridge `levelOscSup` to the leaf LHS, then collapse the RHS.
        have hLHS : levelOscSup B μ X δ n (m + 1)
            ≤ ∫⁻ ω : Ξ, ENNReal.ofReal
                (⨆ i, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ := by
          refine lintegral_mono (fun ξ => ?_)
          refine iSup_le (fun i => ?_)
          refine ENNReal.ofReal_le_ofReal ?_
          exact le_ciSup (Finite.bddAbove_range
            (fun i : Fin (B.Nq (m + 1)) =>
              |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|)) i
        refine hLHS.trans (hbnd.trans ?_)
        -- Leaf RHS = `ofReal(K·ε·√log(1+N_{m+1}))`.
        rw [hcard]
        -- `√log(1+N_{m+1}) ≤ ∑_{p∈Icc q₀ (m+1)} √log(1+coverCard p)`.
        have hsalvage :
            Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ)))
              ≤ ∑ p ∈ Finset.Icc q₀ (m + 1), Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))) := by
          have hcardle : (B.Nq (m + 1) : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by
            have h := B.card_le hq0_le
            calc (B.Nq (m + 1) : ℝ) ≤ ((∏ p ∈ Finset.Icc q₀ (m + 1), B.coverCard p : ℕ) : ℝ) := by
                  exact_mod_cast h
              _ = ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by push_cast; rfl
          have hle1 : 1 + (B.Nq (m + 1) : ℝ)
              ≤ 1 + ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by linarith
          have hpos1 : (0 : ℝ) < 1 + (B.Nq (m + 1) : ℝ) := by positivity
          refine le_trans (Real.sqrt_le_sqrt (Real.log_le_log hpos1 hle1)) ?_
          exact AsymptoticStatistics.ForMathlib.Real.sqrt_log_prod_le_sum_one_add
            ⟨m + 1, Finset.mem_Icc.mpr ⟨hq0_le, le_rfl⟩⟩ _
        -- `ofReal(K·ε·√log) ≤ ofReal(K·ε)·∑ ofReal(√log(coverCard p))`.
        have hstep1 :
            ENNReal.ofReal (K * ε * Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ))))
              ≤ ENNReal.ofReal (K * ε)
                  * ∑ p ∈ Finset.Icc q₀ (m + 1),
                      ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
          gcongr
        refine hstep1.trans ?_
        -- `ofReal(√log(1+coverCard p)) = entropyWeight(coverCard p) ≤ entropyIntegrand`.
        have hcover_term : ∀ p ∈ Finset.Icc q₀ (m + 1),
            ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
              ≤ entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := by
          intro p hp
          obtain ⟨hpq0, _⟩ := Finset.mem_Icc.mp hp
          have hco := B.coverCard_le hpq0
          have hscale : (1/2 : ℝ) ^ (p - q₀) * C = (1/2 : ℝ) ^ (p - q₀) * δ := by rw [hCδ]
          rw [hscale] at hco
          calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
              = entropyWeight (B.coverCard p : ℕ∞) := (entropyWeight_coe _).symm
            _ ≤ entropyWeight (bracketingNumber ((1/2 : ℝ) ^ (p - q₀) * δ) F 2 P) :=
                entropyWeight_mono hco
            _ = entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := rfl
        -- The dyadic identity `ofReal(K·ε) = ofReal(K·2^{q₀+1}) · (2⁻¹)^{m+1} · ofReal δ`.
        have hKε_eq :
            ENNReal.ofReal (K * ε)
              = ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2⁻¹ : ℝ≥0∞) ^ (m + 1)
                  * ENNReal.ofReal δ := by
          have hpoweq : (1/2 : ℝ) ^ (m - q₀) = (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m + 1) := by
            have hsum : (q₀ + 1) + (m - q₀) = m + 1 := by omega
            have hsplit : (1/2 : ℝ) ^ (m + 1)
                = (1/2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m - q₀) := by
              rw [← pow_add, hsum]
            have hprod : (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (q₀ + 1) = 1 := by
              rw [← mul_pow]; norm_num
            calc (1/2 : ℝ) ^ (m - q₀)
                = 1 * (1/2 : ℝ) ^ (m - q₀) := (one_mul _).symm
              _ = ((2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (q₀ + 1)) * (1/2 : ℝ) ^ (m - q₀) := by
                  rw [hprod]
              _ = (2 : ℝ) ^ (q₀ + 1) * ((1/2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m - q₀)) := by ring
              _ = (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m + 1) := by rw [← hsplit]
          have hexp : K * ε = K * (2 : ℝ) ^ (q₀ + 1) * (1/2 : ℝ) ^ (m + 1) * δ := by
            rw [hε_def, hpoweq]; ring
          rw [hexp, hofpow (m + 1),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        -- Combine the estimates at this level.
        rw [hKε_eq]
        -- `∑ b p = ofReal δ · ∑ entropyIntegrand` (each `p ∈ Icc` has `q₀ ≤ p`).
        have hb_sum :
            (∑ p ∈ Finset.Icc q₀ (m + 1), b p)
              = ENNReal.ofReal δ
                  * ∑ p ∈ Finset.Icc q₀ (m + 1),
                      entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p hp => ?_)
          obtain ⟨hpq0, _⟩ := Finset.mem_Icc.mp hp
          rw [hb_def]
          simp only [if_pos hpq0]
        calc ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2⁻¹ : ℝ≥0∞) ^ (m + 1)
                * ENNReal.ofReal δ
                * ∑ p ∈ Finset.Icc q₀ (m + 1),
                    ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
            ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2⁻¹ : ℝ≥0∞) ^ (m + 1)
                * ENNReal.ofReal δ
                * ∑ p ∈ Finset.Icc q₀ (m + 1),
                    entropyIntegrand ((1/2 : ℝ) ^ (p - q₀) * δ) F P := by
                gcongr with p hp
                exact hcover_term p hp
          _ = ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * ((2⁻¹ : ℝ≥0∞) ^ (m + 1)
                * (∑ p ∈ Finset.Icc q₀ (m + 1), b p)) := by
                rw [hb_sum]; ring
      · -- hg_bdd : `|g i ω| ≤ √n·ε / (1 + √log(1+N_{m+1}))`.
        -- On `{chainB …}`, `Δ_{m+1} i ≤ Δ_m(parent) ≤ √n·chainThreshold m`, and
        -- `chainThreshold m = (1/2)^{m−q₀}·δ / (1+√log(1+N_{m+1}))` = `ε / (…)`.
        intro i ω
        rw [hg_def]
        simp only [truncOsc]
        -- the RHS the leaf wants, in `chainThreshold m` form.
        have hthr_eq : Real.sqrt n * ε
              / (1 + Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq (m + 1))) : ℝ))))
            = Real.sqrt n * chainThreshold B δ m := by
          rw [hcard, chainThreshold, hε_def]; ring
        rw [hthr_eq]
        by_cases hω : ω ∈ {y | chainB B δ n (m + 1) i y}
        · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
          -- The middle clause pins `f`'s own level-`m`
          -- cell-ancestor envelope directly, `Δ_m (ancestor) ω ≤ √n·chainThreshold m`;
          -- nesting `Δ_{m+1} i ≤ Δ_m (ancestor)` is `Δ_le_ancestor`.
          have hΔ_nn : 0 ≤ B.Δ (m + 1) i ω :=
            le_trans (abs_nonneg (B.π (m + 1) i ω - B.π (m + 1) i ω)) (by
              simpa using B.diam hq0_le i (B.π (m + 1) i) (B.π_mem hq0_le i) (B.π (m + 1) i)
                (B.π_mem hq0_le i) ω)
          obtain ⟨_, hsmall, _⟩ := hω
          -- The gate at level `p = m` (the immediate predecessor of `m+1`).
          have hanc_small :
              B.Δ m (B.ancestor hq0_le i m hq1_le (Nat.le_succ m)) ω
                ≤ Real.sqrt n * chainThreshold B δ m :=
            hsmall m hq1_le (Nat.lt_succ_self m)
          have hΔ_le_anc :
              B.Δ (m + 1) i ω ≤ B.Δ m (B.ancestor hq0_le i m hq1_le (Nat.le_succ m)) ω :=
            B.Δ_le_ancestor hq0_le i m hq1_le (Nat.le_succ m) ω
          calc |B.Δ (m + 1) i ω| = B.Δ (m + 1) i ω := abs_of_nonneg hΔ_nn
            _ ≤ B.Δ m (B.ancestor hq0_le i m hq1_le (Nat.le_succ m)) ω := hΔ_le_anc
            _ ≤ Real.sqrt n * chainThreshold B δ m := hanc_small
        · rw [Set.indicator_of_notMem hω, mul_zero, abs_zero]
          have : 0 ≤ chainThreshold B δ m := by rw [chainThreshold]; positivity
          positivity
      · -- hg_var : `∫ (g i)² ≤ (2ε)²`.
        -- `‖g i‖₂ ≤ ‖Δ_{m+1} i‖₂ ≤ C·(1/2)^{(m+1)−q₀} = δ·(1/2)^{m+1−q₀} ≤ 2ε`.
        intro i
        have hΔ_memLp : MemLp (B.Δ (m + 1) i) 2 P := B.Δ_memLp hq0_le i
        -- `∫ (Δ_{m+1} i)² ≤ (C·(1/2)^{m+1−q₀})²`.
        have hΔ_sq_le : ∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P
            ≤ (C * (1/2 : ℝ) ^ (m + 1 - q₀)) ^ 2 := by
          have hnn : 0 ≤ ∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P :=
            MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
          have hCpow_nn : 0 ≤ C * (1/2 : ℝ) ^ (m + 1 - q₀) := by rw [hCδ]; positivity
          have hsqrt_eq : Real.sqrt (∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P)
              = (eLpNorm (B.Δ (m + 1) i) 2 P).toReal := by
            rw [hΔ_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
            have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
            have h_int_eq :
                (fun ω => ‖B.Δ (m + 1) i ω‖ ^ (2 : ℝ≥0∞).toReal)
                  = (fun ω => B.Δ (m + 1) i ω ^ 2) := by
              funext ω; rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
            rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2,
              Real.sqrt_eq_rpow]
            norm_num
          have hsqrt_le : Real.sqrt (∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P)
              ≤ C * (1/2 : ℝ) ^ (m + 1 - q₀) := by
            rw [hsqrt_eq]
            calc (eLpNorm (B.Δ (m + 1) i) 2 P).toReal
                ≤ (ENNReal.ofReal (C * (1/2 : ℝ) ^ (m + 1 - q₀))).toReal :=
                  ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (B.Δ_L2_le hq0_le i)
              _ = C * (1/2 : ℝ) ^ (m + 1 - q₀) := ENNReal.toReal_ofReal hCpow_nn
          nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P), hsqrt_le,
            hCpow_nn]
        -- `∫ (g i)² ≤ ∫ (Δ_{m+1} i)²` (indicator ≤ 1).
        have hgsq_le : ∫ ω, (g i ω) ^ 2 ∂P ≤ ∫ ω, (B.Δ (m + 1) i ω) ^ 2 ∂P := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Eventually.of_forall (fun ω => sq_nonneg _)) (hΔ_memLp.integrable_sq) ?_
          refine Eventually.of_forall (fun ω => ?_)
          rw [hg_def]
          simp only [truncOsc]
          rcases Set.indicator_eq_zero_or_self {y | chainB B δ n (m + 1) i y} (1 : Ω → ℝ) ω with
            h0 | h1
          · rw [h0, mul_zero]; simpa using sq_nonneg (B.Δ (m + 1) i ω)
          · rw [h1, Pi.one_apply, mul_one]
        refine hgsq_le.trans (hΔ_sq_le.trans ?_)
        -- `(C·(1/2)^{m+1−q₀})² ≤ (2ε)²`: `C = δ`, `(1/2)^{m+1−q₀} = (1/2)·(1/2)^{m−q₀}`.
        have hCeq : C * (1/2 : ℝ) ^ (m + 1 - q₀) ≤ 2 * ε := by
          rw [hCδ, hε_def]
          have hpow : (1/2 : ℝ) ^ (m + 1 - q₀) = (1/2 : ℝ) * (1/2 : ℝ) ^ (m - q₀) := by
            rw [← pow_succ']
            congr 1; omega
          rw [hpow]; ring_nf
          nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) (m - q₀), hδ.le]
        have hCnn : 0 ≤ C * (1/2 : ℝ) ^ (m + 1 - q₀) := by rw [hCδ]; positivity
        nlinarith [hCeq, hCnn, hε_pos.le]
    · -- `q ≤ q₀`: `chainB` false (`q₀ < q` fails) ⇒ `truncOsc = 0` ⇒ `levelOscSup = 0`.
      have hzero : levelOscSup B μ X δ n q = 0 := by
        rw [levelOscSup]
        have hpt : ∀ ξ : Ξ, (⨆ i : Fin (B.Nq q),
            ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) (truncOsc B δ n q i)|) = 0 := by
          intro ξ
          refine iSup_eq_zero.mpr (fun i => ?_)
          have hfun : truncOsc B δ n q i = (fun _ => (0 : ℝ)) := by
            funext x
            simp only [truncOsc]
            rw [Set.indicator_of_notMem, mul_zero]
            simp only [Set.mem_setOf_eq, chainB]
            exact fun h => hq0q h.1
          rw [hfun]
          have : empiricalProcess P n (fun k : Fin n => X k.val ξ) (fun _ => (0 : ℝ)) = 0 := by
            simp [empiricalProcess, empiricalAvg]
          rw [this, abs_zero, ENNReal.ofReal_zero]
        simp_rw [hpt]
        rw [lintegral_zero]
      rw [hzero]
      exact zero_le
  -- =====================================================================
  -- STEP 2 — Sum the per-level bounds and reindex.
  -- =====================================================================
  calc (∑' q : ℕ, levelOscSup B μ X δ n q)
      ≤ ∑' q : ℕ, ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
          * ((2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, b p)) :=
        ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
          * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc q₀ q, b p) := by
        rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
          * (2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * b p) := by
        gcongr
        exact AsymptoticStatistics.ForMathlib.ENNReal.tsum_pow_half_sum_Icc_le q₀ b
    _ = ENNReal.ofReal (4 * K)
          * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
        -- `∑'_p (2⁻¹)^p b p = (2⁻¹)^{q₀} · series` (reindex `p = q₀ + j`).
        have hreindex :
            (∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * b p)
              = (2⁻¹ : ℝ≥0∞) ^ q₀
                  * ∑' j : ℕ, ENNReal.ofReal ((1/2 : ℝ)^j * δ)
                      * entropyIntegrand ((1/2 : ℝ)^j * δ) F P := by
          -- support of `p ↦ (2⁻¹)^p b p` ⊆ range of `j ↦ q₀ + j`.
          have hinj : Function.Injective (fun j : ℕ => q₀ + j) :=
            fun a c h => by simpa using Nat.add_left_cancel h
          have hsupp : (Function.support fun p => (2⁻¹ : ℝ≥0∞) ^ p * b p)
              ⊆ Set.range (fun j : ℕ => q₀ + j) := by
            intro p hp
            simp only [Function.mem_support, ne_eq] at hp
            by_cases hpq0 : q₀ ≤ p
            · exact ⟨p - q₀, Nat.add_sub_cancel' hpq0⟩
            · exfalso; apply hp
              rw [hb_def]; simp only [if_neg hpq0, mul_zero]
          rw [← hinj.tsum_eq hsupp, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun j => ?_
          -- term `j`: `(2⁻¹)^{q₀+j} · b(q₀+j) = (2⁻¹)^{q₀}·(2⁻¹)^j·ofReal δ·integrand`.
          have hbj : b (q₀ + j)
              = ENNReal.ofReal δ * entropyIntegrand ((1/2 : ℝ) ^ j * δ) F P := by
            rw [hb_def]; simp only [if_pos (Nat.le_add_right q₀ j), Nat.add_sub_cancel_left]
          rw [hbj, pow_add, hofpow j]
          rw [show ((1/2 : ℝ) ^ j * δ) = (1/2 : ℝ) ^ j * δ from rfl,
            ENNReal.ofReal_mul (by positivity)]
          ring
        rw [hreindex]
        -- scalar `ofReal(K·2^{q₀+1}) · 2 · (2⁻¹)^{q₀} = ofReal(4K)`.
        have hofq0 : (2⁻¹ : ℝ≥0∞) ^ q₀ = ENNReal.ofReal ((1/2 : ℝ) ^ q₀) := hofpow q₀
        have hscalar :
            ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2 * (2⁻¹ : ℝ≥0∞) ^ q₀)
              = ENNReal.ofReal (4 * K) := by
          rw [hofq0, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : (2 : ℝ) ^ (q₀ + 1) * (2 * (1/2 : ℝ) ^ q₀) = 4 := by
            rw [pow_succ]
            have h2 : (2 : ℝ) ^ q₀ * (1/2 : ℝ) ^ q₀ = 1 := by
              rw [← mul_pow]; norm_num
            nlinarith [h2]
          nlinarith [this]
        calc ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1))
                * (2 * ((2⁻¹ : ℝ≥0∞) ^ q₀
                    * ∑' j : ℕ, ENNReal.ofReal ((1/2 : ℝ)^j * δ)
                        * entropyIntegrand ((1/2 : ℝ)^j * δ) F P))
            = (ENNReal.ofReal (K * (2 : ℝ) ^ (q₀ + 1)) * (2 * (2⁻¹ : ℝ≥0∞) ^ q₀))
                * ∑' j : ℕ, ENNReal.ofReal ((1/2 : ℝ)^j * δ)
                    * entropyIntegrand ((1/2 : ℝ)^j * δ) F P := by ring
          _ = ENNReal.ofReal (4 * K)
                * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                    * entropyIntegrand ((1/2 : ℝ)^q * δ) F P := by rw [hscalar]

/-- **B-series dyadic bound (vdV p.287-288).**

The B-series remainder `(f − π_q f)·B_q f`, where `B_q f` (`chainB`) is the
indicator that level `q` is the *first* to cross the threshold `√n·a_q`, plus the
envelope-tail piece where `f` itself exceeds the threshold. After taking
`supNormOver F` of the threshold-truncated empirical process and integrating, the
per-level finite-class bound (`tight_chain_level_bound`: cardinality `N_q`,
sup-norm `≤ √n·a_q`, `L²`-norm `≤ 2·2^{−(q−q₀)}δ`, offset scale) summed over levels
(`tight_chain_telescope_bound`) plus the envelope-tail correction
(`tight_envelope_truncation_bound`) gives `c·(dyadic series) + c·√n·(envelope
tail)`. The LHS is the integral of `supNormOver F` of the threshold-truncated
evaluator (the form `tight_envelope_truncation_bound` consumes).

`hF_ne` (`F.Nonempty`) supplies the `[Nonempty (Fin (B.Nq q))]` that the per-level
`tight_chain_level_bound` on `{f − π_q f}` needs; the per-level `L²` slice
(`‖f − π_q f‖_{P,2} ≲ 2^{−(q−q₀)}δ`) comes from the partition's `Δ_L2_le` (offset
scale, `C = δ`), so the standing `Pf² ≤ δ²` hypothesis is *not* needed here.

vdV §19.6 p.287-288, the B-series + envelope-tail. -/
theorem chain_B_dyadic_bound
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 4 ≤ c ∧
      ∀ (F : Set (Ω → ℝ)) (q₀ : ℕ) (C : ℝ) (B : NestedBracketPartition F P q₀ C)
        (_hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
        (_hF_ne : F.Nonempty),
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δ : ℝ}, 0 < δ → C = δ → ∀ (n : ℕ), 1 ≤ n →
          (∫⁻ ξ, supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
            + (∑' q : ℕ, levelOscSup B μ X δ n q)
            ≤ ENNReal.ofReal c
                * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                    * entropyIntegrand ((1/2 : ℝ)^q * δ) F P)
              + ENNReal.ofReal c *
                (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|} 1 ω ∂P) := by
  -- The B-series splits into two summands handled independently:
  --   (i)  the **envelope-tail** integral, closed by the public
  --        `tight_envelope_truncation_bound` (vdV p.287-288); its
  --        conclusion is exactly the second RHS term up to the constant `4`;
  --   (ii) the **`∑' q, levelOscSup`** B-series, bounded by
  --        `chain_B_levelOscSup_dyadic_bound` below.
  -- A universal constant `c = max 4 cB` dominates both pieces.
  obtain ⟨cB, hcB_pos, hcB⟩ :=
    chain_B_levelOscSup_dyadic_bound hX_meas hX_iindep hX_idem hX_law
  refine ⟨max 4 cB, le_max_left _ _, ?_⟩
  set c : ℝ := max 4 cB with hc_def
  have h4c : (4 : ℝ) ≤ c := le_max_left _ _
  have hcBc : cB ≤ c := le_max_right _ _
  intro F q₀ C B hπ_meas hF_ne Φ hΦ_meas hΦ_env hΦ_memLp δ hδ hCδ n hn
  -- (i) envelope-tail summand
  have hEnv :
      (∫⁻ ξ, supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => f x
              * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
        ≤ ENNReal.ofReal c
            * (ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                  * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|} 1 ω ∂P) := by
    refine le_trans
      (tight_envelope_truncation_bound P hX_meas hX_iindep hX_idem hX_law
        F Φ hΦ_env hΦ_meas (Real.sqrt n * globalThreshold B δ) n hn) ?_
    rw [mul_assoc]
    gcongr ?_ * _
    calc (4 : ℝ≥0∞) = ENNReal.ofReal 4 := by
            rw [ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal c := ENNReal.ofReal_le_ofReal h4c
  -- (ii) `∑' q, levelOscSup` summand
  have hOsc :
      (∑' q : ℕ, levelOscSup B μ X δ n q)
        ≤ ENNReal.ofReal c
            * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
    refine le_trans (hcB F q₀ C B hπ_meas hF_ne hδ hCδ n hn) ?_
    gcongr
  -- combine: LHS = ENV + ∑' ; RHS = c·S + c·tail (commute the two RHS terms)
  rw [add_comm (ENNReal.ofReal c * (∑' q : ℕ, _ * _))]
  exact add_le_add hEnv hOsc

/-- **Dyadic rearrangement with a one-level upper-limit shift** (A-series variant).
The A-series jump class at level `m = q₀ + q` has cardinality `N_{m+1}` bounded by a
product over `Icc q₀ (m+1)`, so the per-level entropy collapse produces an *inner sum
over `Icc 0 (q+1)`* (the offset range, one level longer than the outer index `q`).
Splitting `Icc 0 (q+1) = Icc 0 q ∪ {q+1}` reduces to
`ENNReal.tsum_pow_half_sum_Icc_le` (factor `2`) plus a `q ↦ q+1` reindexed tail
(factor `2`), giving the universal factor `4`. The constant is `q₀`-independent. -/
private lemma tsum_pow_half_sum_Icc_succ_le (a : ℕ → ℝ≥0∞) :
    (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p))
      ≤ 4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by
  -- Split `Icc 0 (q+1) = Icc 0 q + {q+1}` and distribute.
  have hsplit : ∀ q : ℕ,
      (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p)
        = (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p)
          + (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1) := by
    intro q
    rw [Finset.sum_Icc_succ_top (Nat.zero_le _), mul_add]
  calc (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 (q + 1), a p))
      = (∑' q : ℕ, ((2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p)
          + (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1))) := by
        exact tsum_congr hsplit
    _ = (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * (∑ p ∈ Finset.Icc 0 q, a p))
          + (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1)) := by
        rw [ENNReal.tsum_add]
    _ ≤ 2 * (∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p)
          + 2 * (∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p) := by
        refine add_le_add
          (AsymptoticStatistics.ForMathlib.ENNReal.tsum_pow_half_sum_Icc_le 0 a) ?_
        -- `∑'_q (2⁻¹)^q·a_(q+1) = 2·∑'_q (2⁻¹)^(q+1)·a_(q+1) ≤ 2·∑'_p (2⁻¹)^p·a_p`.
        have hreidx :
            (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1))
              ≤ ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p :=
          ENNReal.tsum_comp_le_tsum_of_injective
            (fun _ _ h => by simpa using h)
            (fun p => (2⁻¹ : ℝ≥0∞) ^ p * a p)
        have hhalf : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        calc (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ q * a (q + 1))
            = ∑' q : ℕ, 2 * ((2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1)) := by
              refine tsum_congr fun q => ?_
              have hpow : (2⁻¹ : ℝ≥0∞) ^ q = 2 * (2⁻¹ : ℝ≥0∞) ^ (q + 1) := by
                rw [pow_succ, ← mul_assoc, mul_comm (2 : ℝ≥0∞) _, mul_assoc, hhalf, mul_one]
              rw [hpow, mul_assoc]
          _ = 2 * (∑' q : ℕ, (2⁻¹ : ℝ≥0∞) ^ (q + 1) * a (q + 1)) := by
              rw [ENNReal.tsum_mul_left]
          _ ≤ 2 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by gcongr
    _ = 4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞) ^ p * a p := by ring

/-- **A-series dyadic bound (vdV p.287-288).**

The A-series `Σ_{q>q₀} (π_q f − π_{q−1}f)·A_{q−1}f`, where the chain links are the
jump functions `B.jump` (`π_{q+1} − π_q(parent)`, with `jump_card_le`,
`jump_measurable`, `jump_L2_le`). Summed as `levelJumpSup` over levels `q₀ + q`.
By the per-level finite-class bound on the jump classes (cardinality
`≤ ∏ coverCard ≤ N_q·N_{q-1}`, sup-norm `≤ 2√n·a_{q-1}`, `L²`-norm
`≲ 2^{−(q−q₀)}` offset scale) summed over levels (`tight_chain_telescope_bound`
+ `Real.sqrt_log_prod_le_sum_one_add` for the product cardinality + dyadic
rearrangement `ENNReal.tsum_pow_half_sum_Icc_le`), this is bounded by
`c·(dyadic series)`.

The final `√(log(1 + coverCard)) → entropyIntegrand((1/2)^{p−q₀}·C)` step uses the
partition's `coverCard_le` field — `(coverCard p : ℕ∞) ≤ bracketingNumber
((1/2)^{p−q₀}·C) F 2 P` (offset scale) — so `√log(1 + coverCard) ≤ entropyIntegrand`
via `entropyWeight_mono`. This is a constitutive field of `NestedBracketPartition`
and is discharged with equality by `nestedBracketPartition_of_finiteEntropy`,
using minimal covers from `minimalCoverData`. The `δ` scale is carried by the
partition's scale constant `C`
(the finiteEntropy construction sets `C = δ`, so `Δ_L2_le`'s `C·(1/2)^{q−q₀}` is
exactly the series-offset term `(1/2)^{q−q₀}·δ`).
`hF_ne` (`F.Nonempty`) supplies the `[Nonempty (Fin (B.Nq (q+1)))]` the jump-class
`tight_chain_level_bound` needs.

vdV §19.6 p.287-288, the A-series (jump classes). -/
theorem chain_A_dyadic_bound
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : Set (Ω → ℝ)) (q₀ : ℕ) (C : ℝ) (B : NestedBracketPartition F P q₀ C)
        (_hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
        (_hF_ne : F.Nonempty),
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δ : ℝ}, 0 < δ → C = δ → ∀ (n : ℕ), 1 ≤ n →
          (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q))
            ≤ ENNReal.ofReal c
                * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                    * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
  classical
  -- Hoist the uniform finite-class chaining constant `K` (= 288), then the dyadic
  -- factor `4` from `tsum_pow_half_sum_Icc_succ_le`; the universal constant is `4·K`.
  obtain ⟨K, hK_pos, hb⟩ :=
    tight_chain_level_bound_uniform P hX_meas hX_iindep hX_idem hX_law
  refine ⟨4 * K, by positivity, ?_⟩
  intro F q₀ C B hπ_meas hF_ne Φ _ _ _ δ hδ hCδ n hn
  -- Abbreviation: the (offset-coordinate) per-level entropy weight feeding the series.
  set a : ℕ → ℝ≥0∞ := fun k => entropyIntegrand ((1/2 : ℝ)^k * δ) F P with ha_def
  -- ===== Per-level bound =====
  -- For each level index `q` (book level `m = q₀ + q`), the jump-sup contribution
  -- is dominated by the leaf bound, whose entropy weight `√log(1 + N_{m+1})` collapses
  -- (via `jump_card_le` + `Real.sqrt_log_prod_le_sum_one_add` + `coverCard_le`) to the
  -- offset-range sum `∑_{k ∈ Icc 0 (q+1)} a k`.
  have hlevel : ∀ q : ℕ,
      levelJumpSup B μ X δ n (Nat.le_add_right q₀ q)
        ≤ ENNReal.ofReal K
            * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) := by
    intro q
    set m : ℕ := q₀ + q with hm_def
    have hm : q₀ ≤ m := Nat.le_add_right q₀ q
    have hmq : m - q₀ = q := by omega
    -- A nonempty level-`(m+1)` cell index.
    have hNq_ne : Nonempty (Fin (B.Nq (m + 1))) := by
      obtain ⟨f, hf⟩ := hF_ne
      obtain ⟨i, _⟩ := B.cover (le_trans hm (Nat.le_succ m)) f hf
      exact ⟨i⟩
    -- The A-gated jump family.
    set g : Fin (B.Nq (m + 1)) → Ω → ℝ := fun i => truncJump B δ n hm i with hg_def
    -- The A-set `{x | chainA B δ n m (parent i) x}` is, for
    -- each cell index, a countable intersection (over levels `p ≤ m`) of the
    -- single-cell sublevel sets `{x | Δ_p (ancestor) x ≤ √n·a_p}` (the `∀ j` layer is
    -- gone; each `p` contributes ONE cell, the parent's level-`p` ancestor).
    have hA_meas : ∀ i : Fin (B.Nq (m + 1)),
        MeasurableSet {x | chainA B δ n m (B.parent hm i) x} := by
      intro i
      have hset : {x | chainA B δ n m (B.parent hm i) x}
          = ⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p ≤ m),
              {x | B.Δ p (B.ancestor (le_trans hp₀ hpq) (B.parent hm i) p hp₀ hpq) x
                  ≤ Real.sqrt n * chainThreshold B δ p} := by
        ext x; simp only [chainA, Set.mem_setOf_eq, Set.mem_iInter]
      rw [hset]
      refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
        MeasurableSet.iInter (fun hpq => ?_)))
      exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const
    have hg_meas : ∀ i, Measurable (g i) := by
      intro i
      refine (B.jump_measurable hπ_meas hm i).mul ?_
      exact measurable_one.indicator (hA_meas i)
    have hcard : Fintype.card (Fin (B.Nq (m + 1))) = B.Nq (m + 1) := Fintype.card_fin _
    -- The leaf threshold matches `chainThreshold B δ m` exactly (card `N_{m+1}`).
    have hthr_eq :
        Real.sqrt n * ((1/2 : ℝ)^q * δ)
            / (1 + Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq (m + 1))) : ℝ))))
          = Real.sqrt n * chainThreshold B δ m := by
      rw [chainThreshold, hcard, hmq]
      ring
    -- Apply the uniform leaf with scale `ε = (1/2)^q·δ`.
    have hbnd := hb g hg_meas (ε := (1/2 : ℝ)^q * δ) (by positivity) n hn ?_ ?_
    · -- Bridge `levelJumpSup` to the leaf LHS, then collapse the leaf RHS.
      have hLHS : levelJumpSup B μ X δ n (Nat.le_add_right q₀ q)
          ≤ ∫⁻ ω : Ξ,
              ENNReal.ofReal
                (⨆ i, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ := by
        refine lintegral_mono (fun ξ => ?_)
        refine iSup_le (fun i => ?_)
        refine ENNReal.ofReal_le_ofReal ?_
        exact le_ciSup (Finite.bddAbove_range
          (fun i : Fin (B.Nq (m + 1)) =>
            |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|)) i
      refine hLHS.trans (hbnd.trans ?_)
      -- Collapse `√(log(1 + N_{m+1}))` to `∑_{k ∈ Icc 0 (q+1)} a k`.
      have hweight_le :
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (Fintype.card (Fin (B.Nq (m + 1))) : ℝ))))
            ≤ ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
        rw [hcard]
        -- `N_{m+1} ≤ ∏_{p ∈ Icc q₀ (m+1)} coverCard p` (`jump_card_le`).
        have hcard_prod :
            (B.Nq (m + 1) : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by
          have h := B.jump_card_le (q := m) (le_trans hm (Nat.le_succ m))
          calc (B.Nq (m + 1) : ℝ)
              ≤ ((∏ p ∈ Finset.Icc q₀ (m + 1), B.coverCard p : ℕ) : ℝ) := by exact_mod_cast h
            _ = ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) := by push_cast; rfl
        have hIcc_ne : (Finset.Icc q₀ (m + 1)).Nonempty :=
          ⟨q₀, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
        -- `√(log(1+N)) ≤ √(log(1+∏)) ≤ ∑_p √(log(1+coverCard p))`.
        have hsalvage :
            Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ)))
              ≤ ∑ p ∈ Finset.Icc q₀ (m + 1), Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))) := by
          refine le_trans (Real.sqrt_le_sqrt (Real.log_le_log (by positivity) ?_))
            (AsymptoticStatistics.ForMathlib.Real.sqrt_log_prod_le_sum_one_add hIcc_ne
              (fun p => B.coverCard p))
          have : (0 : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (m + 1), (B.coverCard p : ℝ) :=
            Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _)
          linarith [hcard_prod]
        -- Lift to `ℝ≥0∞`, distribute the sum, and dominate each term by `a (p - q₀)`.
        calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.Nq (m + 1) : ℝ))))
            ≤ ENNReal.ofReal
                (∑ p ∈ Finset.Icc q₀ (m + 1), Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))) :=
              ENNReal.ofReal_le_ofReal hsalvage
          _ = ∑ p ∈ Finset.Icc q₀ (m + 1),
                ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))) := by
              rw [ENNReal.ofReal_sum_of_nonneg (fun p _ => Real.sqrt_nonneg _)]
          _ ≤ ∑ p ∈ Finset.Icc q₀ (m + 1), a (p - q₀) := by
              -- Term-wise: `entropyWeight (coverCard p) ≤ entropyIntegrand ((1/2)^{p-q₀}·δ)`.
              refine Finset.sum_le_sum (fun p hp => ?_)
              have hqp : q₀ ≤ p := (Finset.mem_Icc.mp hp).1
              have hcc_le :
                  (B.coverCard p : ℕ∞)
                    ≤ bracketingNumber ((1/2 : ℝ)^(p - q₀) * δ) F 2 P := by
                have h := B.coverCard_le hqp
                rw [← hCδ]; exact h
              calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
                  = entropyWeight (B.coverCard p : ℕ∞) := (entropyWeight_coe _).symm
                _ ≤ entropyWeight (bracketingNumber ((1/2 : ℝ)^(p - q₀) * δ) F 2 P) :=
                    entropyWeight_mono hcc_le
                _ = a (p - q₀) := rfl
          _ = ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
              -- Reindex `Icc q₀ (m+1)` to `Icc 0 (q+1)` by `p ↦ p - q₀` (`k ↦ k + q₀`).
              refine Finset.sum_nbij' (fun p => p - q₀) (fun k => k + q₀) ?_ ?_ ?_ ?_ ?_
              · intro p hp
                simp only [hm_def, Finset.mem_Icc] at hp ⊢; omega
              · intro k hk
                simp only [hm_def, Finset.mem_Icc] at hk ⊢; omega
              · intro p hp
                simp only [hm_def, Finset.mem_Icc] at hp ⊢; omega
              · intro k hk
                simp only [Finset.mem_Icc] at hk ⊢; omega
              · intro p _; rfl
      -- Assemble: `ofReal(K·ε·w) ≤ ofReal K · (ofReal ε · ∑ a)`.
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]
      gcongr
    · -- hg_bdd : `|truncJump i ω| ≤ √n·chainThreshold B δ m`.
      intro i ω
      rw [hthr_eq, hg_def]
      simp only [truncJump]
      by_cases hω : ω ∈ {y | chainA B δ n m (B.parent hm i) y}
      · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
        -- Per-ancestor gate: `hω` at `p = m` pins the parent's level-`m` ancestor,
        -- which is the parent itself (`ancestor_self`).
        have hanc := hω m hm le_rfl
        rw [B.ancestor_self hm (B.parent hm i)] at hanc
        calc |B.jump hm i ω| ≤ B.Δ m (B.parent hm i) ω := B.jump_abs_le hm i ω
          _ ≤ Real.sqrt n * chainThreshold B δ m := hanc
      · rw [Set.indicator_of_notMem hω, mul_zero, abs_zero]
        have : 0 ≤ Real.sqrt n * chainThreshold B δ m := by
          refine mul_nonneg (Real.sqrt_nonneg _) ?_
          rw [chainThreshold]; positivity
        linarith
    · -- hg_var : `∫ (g i)² ≤ (2·ε)²`.
      intro i
      have hjump_memLp : MemLp (B.jump hm i) 2 P := by
        refine ⟨(B.jump_measurable hπ_meas hm i).aestronglyMeasurable, ?_⟩
        exact lt_of_le_of_lt (B.jump_L2_le hm i) ENNReal.ofReal_lt_top
      -- `∫ (jump)² ≤ (C·(1/2)^{m-q₀})²` from `‖jump‖_{P,2} ≤ C·(1/2)^{m-q₀}`.
      have hjump_sq_le :
          ∫ ω, (B.jump hm i ω) ^ 2 ∂P ≤ (C * (1/2 : ℝ)^(m - q₀)) ^ 2 := by
        have hnn : 0 ≤ ∫ ω, (B.jump hm i ω) ^ 2 ∂P :=
          MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
        have hC_nn : 0 ≤ C * (1/2 : ℝ)^(m - q₀) := by rw [hCδ]; positivity
        have hsqrt_eq : Real.sqrt (∫ ω, (B.jump hm i ω) ^ 2 ∂P)
            = (eLpNorm (B.jump hm i) 2 P).toReal := by
          rw [hjump_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
          have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
          have h_int_eq :
              (fun ω => ‖B.jump hm i ω‖ ^ (2 : ℝ≥0∞).toReal)
                = (fun ω => B.jump hm i ω ^ 2) := by
            funext ω; rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
          rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2,
            Real.sqrt_eq_rpow]
          norm_num
        have hsqrt_le : Real.sqrt (∫ ω, (B.jump hm i ω) ^ 2 ∂P) ≤ C * (1/2 : ℝ)^(m - q₀) := by
          rw [hsqrt_eq]
          calc (eLpNorm (B.jump hm i) 2 P).toReal
              ≤ (ENNReal.ofReal (C * (1/2 : ℝ)^(m - q₀))).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (B.jump_L2_le hm i)
            _ = C * (1/2 : ℝ)^(m - q₀) := ENNReal.toReal_ofReal hC_nn
        nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, (B.jump hm i ω) ^ 2 ∂P)]
      -- `∫ (g i)² ≤ ∫ (jump)²` (indicator ≤ 1), chain through `(C·(1/2)^{m-q₀})² ≤ (2ε)²`.
      have hgsq_le : ∫ ω, (g i ω) ^ 2 ∂P ≤ ∫ ω, (B.jump hm i ω) ^ 2 ∂P := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall (fun ω => sq_nonneg _)) (hjump_memLp.integrable_sq) ?_
        refine Eventually.of_forall (fun ω => ?_)
        rw [hg_def]
        simp only [truncJump]
        rcases Set.indicator_eq_zero_or_self {y | chainA B δ n m (B.parent hm i) y}
            (1 : Ω → ℝ) ω with h0 | h1
        · rw [h0, mul_zero]; simpa using sq_nonneg (B.jump hm i ω)
        · rw [h1, Pi.one_apply, mul_one]
      refine hgsq_le.trans (hjump_sq_le.trans ?_)
      -- `(C·(1/2)^{m-q₀})² ≤ (2·((1/2)^q·δ))²`: `C = δ`, `m - q₀ = q`.
      rw [hCδ, hmq]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) q, hδ.le,
        sq_nonneg ((1/2 : ℝ)^q * δ)]
  -- ===== Sum the per-level bounds and apply the dyadic rearrangement =====
  -- The recurring conversion `ofReal((1/2)^q·δ) = (2⁻¹)^q · ofReal δ`.
  have hofReal_half : ENNReal.ofReal (1/2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  have hpow_eq : ∀ q : ℕ,
      ENNReal.ofReal ((1/2 : ℝ)^q * δ) = (2⁻¹ : ℝ≥0∞)^q * ENNReal.ofReal δ := by
    intro q
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), hofReal_half]
  -- Abbreviation `w k = ofReal δ · a k` matching the dyadic-rearrangement input.
  set w : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal δ * a k with hw_def
  calc (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q))
      ≤ ∑' q : ℕ, ENNReal.ofReal K
          * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) :=
        ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal K
          * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞)^q * (∑ k ∈ Finset.Icc 0 (q + 1), w k) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun q => ?_
        rw [hpow_eq q, hw_def, ← Finset.mul_sum]
        ring
    _ ≤ ENNReal.ofReal K * (4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞)^p * w p) := by
        gcongr
        exact tsum_pow_half_sum_Icc_succ_le w
    _ = ENNReal.ofReal (4 * K)
          * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat]
        rw [show ENNReal.ofReal K * (4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞)^p * w p)
              = 4 * (ENNReal.ofReal K * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞)^p * w p) by ring,
          show (4 : ℝ≥0∞) * ENNReal.ofReal K
                * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                    * entropyIntegrand ((1/2 : ℝ)^q * δ) F P
              = 4 * (ENNReal.ofReal K
                  * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                      * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) by ring]
        refine congrArg (4 * ·) ?_
        refine congrArg (ENNReal.ofReal K * ·) ?_
        refine tsum_congr fun q => ?_
        rw [hpow_eq q, hw_def, ha_def]
        ring

/-! ### Telescope-to-three-part split (vdV p.287): the structural heart

The pointwise telescope `chain_pointwise_telescope` applied at each `ξ` to the
sequence `q ↦ π_q f`, combined with linearity of `empiricalProcess`
(`empiricalProcess_add`/`empiricalProcess_smul`) and sub-additivity of
`supNormOver` (`supNormOver_add_le`/`supNormOver_sum_le`), bounds the LHS
`∫⁻ supNormOver F 𝔾ₙ` by the sum of the head finite-sup (`levelRepSup` at `q₀`),
the B-series threshold-truncated contribution plus its per-level *cell-oscillation*
sups (`levelOscSup`), and the A-series jump sups (`levelJumpSup`).

### Measurability of the per-level finite-sup integrands

The `levelRepSup` / `levelOscSup` / `levelJumpSup` integrands are finite
`ℝ≥0∞`-suprema of `ξ ↦ ofReal|𝔾ₙ(g i)|`, hence measurable in the sample index
`ξ` whenever the underlying functions `g i : Ω → ℝ` are measurable. These
facts permit the applications of `lintegral_add` and `lintegral_tsum` in
`chain_supnorm_le_three_part`. -/

/-- `ξ ↦ ofReal|𝔾ₙ(g)|` is measurable when `g` is measurable. -/
private lemma measurable_ofReal_abs_empiricalProcess
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) {g : Ω → ℝ} (hg : Measurable g) :
    Measurable (fun ξ : Ξ =>
      ENNReal.ofReal
        |empiricalProcess P n (fun i : Fin n => X i.val ξ) g|) := by
  have hE : Measurable (fun ξ : Ξ =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
    unfold empiricalProcess empiricalAvg
    refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum Finset.univ (fun i _ => hg.comp (hX_meas i.val))
  have : (fun ξ : Ξ => |empiricalProcess P n (fun i : Fin n => X i.val ξ) g|)
      = (fun ξ : Ξ => ‖empiricalProcess P n (fun i : Fin n => X i.val ξ) g‖) := by
    funext ξ; exact (Real.norm_eq_abs _).symm
  exact Measurable.ennreal_ofReal (this ▸ hE.norm)

/-- The finite `ℝ≥0∞`-supremum `ξ ↦ ⨆ i:Fin k, ofReal|𝔾ₙ(g i)|` is measurable
when each `g i` is. -/
private lemma measurable_iSup_ofReal_abs_empiricalProcess
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (n k : ℕ) {g : Fin k → Ω → ℝ} (hg : ∀ i, Measurable (g i)) :
    Measurable (fun ξ : Ξ =>
      ⨆ i : Fin k, ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ) (g i)|) :=
  Measurable.iSup (fun i =>
    measurable_ofReal_abs_empiricalProcess (P := P) hX_meas n (hg i))

/-- The A-series event set `{x | chainA B δ n q i x}` is measurable: under the
**per-ancestor gate** it is a countable intersection (over levels `p` with
`q₀ ≤ p ≤ q`) of the sublevel sets `{x | Δ_p (ancestor) x ≤ √n·a_p}` of the
measurable cell oscillation `B.Δ p (B.ancestor … i p …)` (`measurableSet_le` +
`Δ_meas`). Each `p` contributes the single level-`p` ancestor cell of `f`. -/
private lemma chainA_measurableSet
    (B : NestedBracketPartition F P q₀ C) (δ : ℝ) (n q : ℕ) (i : Fin (B.Nq q)) :
    MeasurableSet {x | chainA B δ n q i x} := by
  have hset : {x | chainA B δ n q i x}
      = ⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p ≤ q),
          {x | B.Δ p (B.ancestor (le_trans hp₀ hpq) i p hp₀ hpq) x
              ≤ Real.sqrt n * chainThreshold B δ p} := by
    ext x; simp only [chainA, Set.mem_setOf_eq, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
    MeasurableSet.iInter (fun hpq => ?_)))
  exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const

/-- The B-series event set `{x | chainB B δ n q i x}` is measurable: the leading
`q₀ < q` conjunct does not depend on `x` (a constant set, `∅` or `univ`,
measurable by `measurableSet_const`), the "all small below `q`" conjunct is — under
the **per-ancestor gate** — a countable intersection (over levels `p < q`) of the
single-cell sublevel sets `{x | Δ_p (ancestor) x ≤ √n·a_p}` (the `∀ j` layer is
gone), and the "crosses at `q`" conjunct `{x | √n·a_q < Δ_q i x}` is measurable via
`measurableSet_lt` + `Δ_meas hq`. The condition `q₀ ≤ q` ensures that the
top-level oscillation `B.Δ q i` is measurable. -/
private lemma chainB_measurableSet
    (B : NestedBracketPartition F P q₀ C) {δ : ℝ} (n : ℕ) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (B.Nq q)) :
    MeasurableSet {x | chainB B δ n q i x} := by
  have hset : {x | chainB B δ n q i x}
      = {_x : Ω | q₀ < q}
        ∩ ((⋂ (p : ℕ) (hp₀ : q₀ ≤ p) (hpq : p < q),
              {x | B.Δ p (B.ancestor (le_of_lt (lt_of_le_of_lt hp₀ hpq)) i p hp₀
                      (le_of_lt hpq)) x
                  ≤ Real.sqrt n * chainThreshold B δ p})
          ∩ {x | Real.sqrt n * chainThreshold B δ q < B.Δ q i x}) := by
    ext x
    simp only [chainB, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.const _) ?_
  refine MeasurableSet.inter ?_ (measurableSet_lt measurable_const (B.Δ_meas hq i))
  refine MeasurableSet.iInter (fun p => MeasurableSet.iInter (fun hp₀ =>
    MeasurableSet.iInter (fun hpq => ?_)))
  exact measurableSet_le (B.Δ_meas hp₀ _) measurable_const

/-- **B-link mean split — pointwise (per-`ξ`) form (vdV p.287).**

The B-link mean split, stated *pointwise* in `ξ` before integration, bounds the
cell-grouped B-link supremum at level `q` by `3 ×`
the finite cell-oscillation sup `⨆ i, ofReal|𝔾ₙ(truncOsc i)|` plus the
**ξ-constant** deterministic `P`-side correction `4√n·⨆_i ∫⁻ Δ_q i·1{chainB} ∂P`:

```
⨆ i, ⨆ f ∈ cell q i, ofReal|𝔾ₙ((f − π_q i)·1{chainB i})|
  ≤ 3·(⨆ i, ofReal|𝔾ₙ(truncOsc i)|) + 4√n·⨆_i ∫⁻ Δ_q i·1{chainB i} ∂P.
```

The RHS, viewed as a function of `ξ`, is **measurable** (the first summand is a
finite `⨆_i` of `ofReal|𝔾ₙ(truncOsc i)|`, measurable by
`measurable_iSup_ofReal_abs_empiricalProcess`; the second is a `ξ`-constant), which
allows `chain_supnorm_le_decomposition` to dominate the uncountable per-cell
B-link supremum by a measurable envelope and split the integral without a
per-cell separability hypothesis. The integrated form is
`supNormOver_link_meanSplit_le`.

The signed-`𝔾ₙ` correction reasoning (why `+4√n·P(Δ·1{cB})`, why `⨆_i` not `Σ_i`)
is explained in the statement of `supNormOver_link_meanSplit_le` below. -/
theorem supNormOver_link_meanSplit_pointwise_le
    [IsProbabilityMeasure P]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    {δ : ℝ} (n : ℕ) {q : ℕ} (hq : q₀ ≤ q) (ξ : Ξ) :
    (⨆ i : Fin (B.Nq q), ⨆ (f : Ω → ℝ) (_ : f ∈ B.cell q i),
        ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ)
            (fun x => (f x - B.π q i x)
              * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x)|)
      ≤ 3 * (⨆ i : Fin (B.Nq q), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncOsc B δ n q i)|)
        + 4 * ENNReal.ofReal (Real.sqrt n)
            * ⨆ i : Fin (B.Nq q), ∫⁻ x, ENNReal.ofReal
                (B.Δ q i x
                  * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x) ∂P := by
  classical
  have hsn_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  -- Cell-`i` indicator of `chainB`, real-valued, measurable, in [0,1].
  have hcB_meas : ∀ i : Fin (B.Nq q),
      MeasurableSet {y | chainB B δ n q i y} :=
    fun i => chainB_measurableSet B n hq i
  have hχ_nn : ∀ (i : Fin (B.Nq q)) (x : Ω),
      (0 : ℝ) ≤ Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x := by
    intro i x
    by_cases hx : x ∈ {y | chainB B δ n q i y}
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hχ_le_one : ∀ (i : Fin (B.Nq q)) (x : Ω),
      Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x ≤ 1 := by
    intro i x
    by_cases hx : x ∈ {y | chainB B δ n q i y}
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- `Δ_q i ≥ 0` (from `diam` at `f = g = π_q i`).
  have hΔ_nn : ∀ (i : Fin (B.Nq q)) (x : Ω), 0 ≤ B.Δ q i x := by
    intro i x
    have := B.diam hq i (B.π q i) (B.π_mem hq i) (B.π q i) (B.π_mem hq i) x
    simpa using this
  -- `truncOsc i = Δ_q i · 1{chainB i}`, measurable and ≥ 0.
  set G : Fin (B.Nq q) → Ω → ℝ := fun i =>
    fun x => B.Δ q i x * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x
    with hG_def
  have hG_eq : ∀ i, G i = truncOsc B δ n q i := fun i => rfl
  have hG_nn : ∀ i x, 0 ≤ G i x := fun i x => mul_nonneg (hΔ_nn i x) (hχ_nn i x)
  have hG_meas : ∀ i, Measurable (G i) := by
    intro i
    exact (B.Δ_meas hq i).mul (measurable_const.indicator (hcB_meas i))
  have hG_int : ∀ i, Integrable (G i) P := by
    intro i
    have hmemLp : MemLp (G i) 2 P := by
      have hmono : ∀ᵐ x ∂P, ‖G i x‖ ≤ B.Δ q i x := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hG_nn i x)]
        calc G i x = B.Δ q i x * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x := rfl
          _ ≤ B.Δ q i x * 1 :=
              mul_le_mul_of_nonneg_left (hχ_le_one i x) (hΔ_nn i x)
          _ = B.Δ q i x := mul_one _
      exact MemLp.mono' (B.Δ_memLp hq i) (hG_meas i).aestronglyMeasurable hmono
    exact hmemLp.integrable (by norm_num)
  -- The cell-`i` correction `corr i ξ = √n·(empAvg(2 G i) + ∫ 2 G i dP)` is the
  -- per-`ξ` bound on `ofReal|𝔾ₙ(a − G i)|`, INDEPENDENT of `f`.
  set corr : Fin (B.Nq q) → Ξ → ℝ≥0∞ := fun i ξ =>
    ENNReal.ofReal (Real.sqrt n)
      * (ENNReal.ofReal (empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ))
        + ENNReal.ofReal (∫ x, 2 * G i x ∂P)) with hcorr_def
  -- ===== Per-`ξ`, per-cell-`i`, per-`f` triangle bound =====
  have h_cell_bound : ∀ (ξ : Ξ) (i : Fin (B.Nq q)) (f : Ω → ℝ),
      f ∈ B.cell q i →
        ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (fun x => (f x - B.π q i x)
                * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x)|
          ≤ ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|
            + corr i ξ := by
    intro ξ i f hf
    have hf_meas : Measurable f := hF_meas f (B.cell_subset hq i hf)
    set a : Ω → ℝ := fun x => (f x - B.π q i x)
      * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x with ha_def
    -- Measurability + the pointwise `|a − G i| ≤ 2 G i`.
    have ha_meas : Measurable a :=
      (hf_meas.sub (hπ_meas hq i)).mul (measurable_const.indicator (hcB_meas i))
    have hd_le : ∀ x, |a x - G i x| ≤ 2 * G i x := by
      intro x
      have hfdiam : |f x - B.π q i x| ≤ B.Δ q i x :=
        B.diam hq i f hf (B.π q i) (B.π_mem hq i) x
      by_cases hx : x ∈ {y | chainB B δ n q i y}
      · have hχ1 : Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x = 1 := by
          simp [Set.indicator_of_mem hx]
        rw [ha_def, hG_def]
        simp only [hχ1, mul_one]
        calc |f x - B.π q i x - B.Δ q i x|
            ≤ |f x - B.π q i x| + |B.Δ q i x| := abs_sub _ _
          _ ≤ B.Δ q i x + B.Δ q i x :=
              add_le_add hfdiam (le_of_eq (abs_of_nonneg (hΔ_nn i x)))
          _ = 2 * B.Δ q i x := by ring
      · have hχ0 : Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x = 0 := by
          simp [Set.indicator_of_notMem hx]
        rw [ha_def, hG_def]
        simp only [hχ0, mul_zero, sub_zero, abs_zero]
        positivity
    have ha_int : Integrable a P := by
      have hmono : ∀ᵐ x ∂P, ‖a x‖ ≤ 3 * G i x := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        have h1 : |a x| ≤ |a x - G i x| + |G i x| := by
          have h2 := abs_add_le (a x - G i x) (G i x); simpa using h2
        rw [abs_of_nonneg (hG_nn i x)] at h1
        rw [Real.norm_eq_abs]
        nlinarith [h1, hd_le x, hG_nn i x]
      exact Integrable.mono' ((hG_int i).const_mul 3) ha_meas.aestronglyMeasurable hmono
    -- `𝔾ₙ a = 𝔾ₙ(G i) + 𝔾ₙ(a − G i)`, triangle in `ofReal`.
    have hlin : empiricalProcess P n (fun k : Fin n => X k.val ξ) a
        = empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)
          + empiricalProcess P n (fun k : Fin n => X k.val ξ) (fun x => a x - G i x) := by
      rw [← empiricalProcess_add P n _ (G i) (fun x => a x - G i x)
        (hG_int i) (ha_int.sub (hG_int i))]
      congr 1
      funext x; ring
    rw [hlin]
    refine le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _)) ?_
    refine le_trans ENNReal.ofReal_add_le ?_
    refine add_le_add le_rfl ?_
    -- `ofReal|𝔾ₙ(a − G i)| ≤ √n·(empAvg|a − G i| + |∫(a − G i)dP|) ≤ corr i ξ`.
    have hsplit :
        ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) (fun x => a x - G i x)|
          = ENNReal.ofReal (Real.sqrt n)
              * ENNReal.ofReal
                  |empiricalAvg (fun x => a x - G i x) n (fun k : Fin n => X k.val ξ)
                    - ∫ x, (a x - G i x) ∂P| := by
      unfold empiricalProcess
      rw [abs_mul, abs_of_nonneg hsn_nn, ENNReal.ofReal_mul hsn_nn]
    rw [hsplit, hcorr_def]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    -- `|empAvg(a − G) − ∫(a − G)| ≤ empAvg(2 G) + |∫(a − G)|`, with `|∫(a − G)| ≤ ∫ 2 G`.
    have hpna : |empiricalAvg (fun x => a x - G i x) n (fun k : Fin n => X k.val ξ)|
        ≤ empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ) := by
      unfold empiricalAvg
      rw [abs_mul, abs_inv, Nat.abs_cast]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
      calc |∑ k : Fin n, (a (X k.val ξ) - G i (X k.val ξ))|
          ≤ ∑ k : Fin n, |a (X k.val ξ) - G i (X k.val ξ)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin n, 2 * G i (X k.val ξ) :=
            Finset.sum_le_sum (fun k _ => hd_le (X k.val ξ))
    have hP_le : |∫ x, (a x - G i x) ∂P| ≤ ∫ x, 2 * G i x ∂P := by
      have hint : Integrable (fun x => a x - G i x) P := ha_int.sub (hG_int i)
      calc |∫ x, (a x - G i x) ∂P|
          ≤ ∫ x, |a x - G i x| ∂P :=
            (abs_integral_le_integral_abs)
        _ ≤ ∫ x, 2 * G i x ∂P :=
            integral_mono hint.abs ((hG_int i).const_mul 2) hd_le
    calc ENNReal.ofReal
            |empiricalAvg (fun x => a x - G i x) n (fun k : Fin n => X k.val ξ)
              - ∫ x, (a x - G i x) ∂P|
        ≤ ENNReal.ofReal
            (empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ)
              + |∫ x, (a x - G i x) ∂P|) :=
          ENNReal.ofReal_le_ofReal ((abs_sub _ _).trans (add_le_add hpna le_rfl))
      _ ≤ ENNReal.ofReal
            (empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ))
            + ENNReal.ofReal |∫ x, (a x - G i x) ∂P| := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal
            (empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ))
            + ENNReal.ofReal (∫ x, 2 * G i x ∂P) :=
          add_le_add le_rfl (ENNReal.ofReal_le_ofReal hP_le)
  -- ===== Collapse the inner `⨆ f ∈ cell q i` to the single cell value + corr =====
  have h_inner : ∀ (ξ : Ξ) (i : Fin (B.Nq q)),
      (⨆ (f : Ω → ℝ) (_ : f ∈ B.cell q i),
        ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ)
            (fun x => (f x - B.π q i x)
              * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x)|)
        ≤ ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)| + corr i ξ := by
    intro ξ i
    exact iSup₂_le (fun f hf => h_cell_bound ξ i f hf)
  -- The deterministic per-cell mean correction `det i = √n·(2·∫⁻ ofReal(G i) dP)`
  -- (= `ofReal√n · ofReal(∫2 G i dP)`, the `f`-independent `P`-side of `corr i ξ`).
  set det : Fin (B.Nq q) → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (Real.sqrt n) * (2 * ∫⁻ x, ENNReal.ofReal (G i x) ∂P) with hdet_def
  -- `corr i ξ ≤ 2·ofReal|𝔾ₙ(G i)| + 2·det i` : the **maximal**-form replacement of the
  -- `Σ_i corr` over-count.  The random `empAvg` half of `corr i ξ` is centred onto
  -- `𝔾ₙ(2 G i)` (`√n·empAvg(2G i) = 𝔾ₙ(2G i) + √n·P(2G i) ≤ 2|𝔾ₙ(G i)| + √n·P(2G i)`),
  -- so the whole correction is dominated by the cell-sup `|𝔾ₙ(G i)|` plus the
  -- deterministic mean `det i` — both of which take `⨆_i` (not `Σ_i`).
  have hcorr_le : ∀ (ξ : Ξ) (i : Fin (B.Nq q)),
      corr i ξ ≤ 2 * ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|
          + 2 * det i := by
    intro ξ i
    -- `ofReal(∫2G i) = 2·∫⁻ ofReal(G i)` (nonneg integrand), so the deterministic
    -- half of `corr` equals `det i`.
    have hG_nn' : ∀ x, 0 ≤ G i x := hG_nn i
    have h2G_nn' : ∀ x, 0 ≤ 2 * G i x := fun x => by have := hG_nn' x; linarith
    have hP_eq : ENNReal.ofReal (∫ x, 2 * G i x ∂P) = 2 * ∫⁻ x, ENNReal.ofReal (G i x) ∂P := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal ((hG_int i).const_mul 2)
        (Filter.Eventually.of_forall h2G_nn')]
      rw [← MeasureTheory.lintegral_const_mul' 2 _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      refine MeasureTheory.lintegral_congr (fun x => ?_)
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; norm_num
    -- The pointwise real bound on the random `empAvg` half:
    -- `√n·empAvg(2G i)(ξ) ≤ 2|𝔾ₙ(G i)(ξ)| + √n·∫2G i dP`.
    have hrand_real :
        Real.sqrt n * empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ)
          ≤ 2 * |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|
            + Real.sqrt n * ∫ x, 2 * G i x ∂P := by
      -- `𝔾ₙ(2G i) = √n(empAvg(2G i) − ∫2G i)`, and `𝔾ₙ(2G i) = 2·𝔾ₙ(G i)`.
      have h2lin : empiricalProcess P n (fun k : Fin n => X k.val ξ) (fun x => 2 * G i x)
          = 2 * empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i) :=
        empiricalProcess_smul P n _ 2 (G i)
      have hgp : empiricalProcess P n (fun k : Fin n => X k.val ξ) (fun x => 2 * G i x)
          = Real.sqrt n
              * (empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ)
                  - ∫ x, 2 * G i x ∂P) := rfl
      have habs : |empiricalProcess P n (fun k : Fin n => X k.val ξ) (fun x => 2 * G i x)|
          = 2 * |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)| := by
        rw [h2lin, abs_mul]; norm_num
      have hle : Real.sqrt n
            * (empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ)
                - ∫ x, 2 * G i x ∂P)
          ≤ |empiricalProcess P n (fun k : Fin n => X k.val ξ) (fun x => 2 * G i x)| := by
        rw [hgp]; exact le_abs_self _
      rw [habs] at hle
      nlinarith [hle, hsn_nn]
    -- Lift to `ℝ≥0∞`.
    have hP2_nn : (0:ℝ) ≤ ∫ x, 2 * G i x ∂P :=
      MeasureTheory.integral_nonneg h2G_nn'
    calc corr i ξ
        = ENNReal.ofReal
              (Real.sqrt n * empiricalAvg (fun x => 2 * G i x) n (fun k : Fin n => X k.val ξ))
            + ENNReal.ofReal (Real.sqrt n) * ENNReal.ofReal (∫ x, 2 * G i x ∂P) := by
          simp only [hcorr_def]
          rw [mul_add]
          congr 1
          rw [ENNReal.ofReal_mul hsn_nn]
      _ ≤ ENNReal.ofReal
              (2 * |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|
                + Real.sqrt n * ∫ x, 2 * G i x ∂P)
            + ENNReal.ofReal (Real.sqrt n) * ENNReal.ofReal (∫ x, 2 * G i x ∂P) :=
          add_le_add (ENNReal.ofReal_le_ofReal hrand_real) le_rfl
      _ ≤ (ENNReal.ofReal (2 * |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|)
              + ENNReal.ofReal (Real.sqrt n * ∫ x, 2 * G i x ∂P))
            + ENNReal.ofReal (Real.sqrt n) * ENNReal.ofReal (∫ x, 2 * G i x ∂P) :=
          add_le_add ENNReal.ofReal_add_le le_rfl
      _ = 2 * ENNReal.ofReal |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|
            + 2 * det i := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_mul hsn_nn, hdet_def, hP_eq]
          rw [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 by simp]
          ring
  -- ===== Per-`ξ`, per-cell bound: `cell-sup_i ≤ 3·ofReal|𝔾ₙ G i| + 2·det i` =====
  have h_cell3 : ∀ (ξ : Ξ) (i : Fin (B.Nq q)),
      (⨆ (f : Ω → ℝ) (_ : f ∈ B.cell q i),
        ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ)
            (fun x => (f x - B.π q i x)
              * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x)|)
        ≤ 3 * ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|
            + 2 * det i := by
    intro ξ i
    refine (h_inner ξ i).trans ?_
    calc ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)| + corr i ξ
        ≤ ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|
            + (2 * ENNReal.ofReal
                |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)| + 2 * det i) :=
          add_le_add le_rfl (hcorr_le ξ i)
      _ = 3 * ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)| + 2 * det i := by ring
  -- ===== Per-`ξ` outer bound: `⨆ i (cell-sup) ≤ 3·⨆ i ofReal|𝔾ₙ G i| + 2·⨆ i det i` =====
  have h_pt :
      (⨆ i : Fin (B.Nq q), ⨆ (f : Ω → ℝ) (_ : f ∈ B.cell q i),
        ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ)
            (fun x => (f x - B.π q i x)
              * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x)|)
        ≤ 3 * (⨆ i : Fin (B.Nq q), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|)
          + 2 * ⨆ i : Fin (B.Nq q), det i := by
    refine iSup_le (fun i => ?_)
    refine le_trans (h_cell3 ξ i) ?_
    refine add_le_add ?_ ?_
    · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact le_iSup
        (fun i => ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ) (G i)|) i
    · exact mul_le_mul_of_nonneg_left (le_iSup (fun i => det i) i) (by norm_num)
  -- The deterministic correction collapses: `2·⨆_i det i = 4√n·⨆_i ∫⁻ ofReal(G i) dP`,
  -- and `∫⁻ ofReal(G i) = ∫⁻ ofReal(Δ_q i · 1{chainB})` by `hG_def`.
  have hdet_eq : (2 : ℝ≥0∞) * ⨆ i : Fin (B.Nq q), det i
      = 4 * ENNReal.ofReal (Real.sqrt n)
          * ⨆ i : Fin (B.Nq q), ∫⁻ x, ENNReal.ofReal
              (B.Δ q i x
                * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x) ∂P := by
    rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
    refine iSup_congr (fun i => ?_)
    rw [hdet_def, hG_def]
    ring
  -- Assemble: `h_pt` with `G i = truncOsc i` and `2·⨆det = 4√n·⨆∫⁻Δ·1{cB}`.
  refine h_pt.trans (le_of_eq ?_)
  simp only [hG_eq]
  rw [hdet_eq]

/-- **B-link mean split (vdV p.287, the `∫⁻` leaf).**

The integrated `ℝ≥0∞`-mean of the **cell-grouped B-link supremum** at level `q` is
dominated by `3 ×` the per-level cell-oscillation sup `⨆ i, ofReal|𝔾ₙ(truncOsc i)|`
plus a deterministic `P`-side correction `4√n·⨆_i P(Δ_q i · 1{chainB i})` — a
**maximum** (`⨆_i`) over cells, NOT a sum:

```
∫⁻ ξ, ⨆ i, ⨆ f ∈ cell q i, ofReal|𝔾ₙ((f − π_q i)·1{chainB i})| ∂μ
  ≤ 3·∫⁻ ξ, ⨆ i, ofReal|𝔾ₙ(truncOsc i)| ∂μ
    + 4·√n·⨆_i ∫⁻ x, Δ_q i x · 1{chainB i} x ∂P.
```

**The signed-process correction, in maximal form.** `𝔾ₙ` is a *signed* functional, so
the cell domination `|f − π_q f| ≤ Δ_q` (`B.diam`) does not give
`|𝔾ₙ((f − π_q f)·B_q)| ≤ |𝔾ₙ(Δ_q · B_q)|` directly: the corresponding
pointwise implication does not hold for a centred process. Instead, with
`a = (f − π_q i)·1{chainB i}`, `G i = Δ_q i·1{chainB i} = truncOsc i`, the difference
`a − G i` has `|a − G i| ≤ 2·G i` pointwise (from `|f − π_q i| ≤ Δ_q i` and `Δ_q i ≥ 0`),
and `𝔾ₙ a = 𝔾ₙ(G i) + 𝔾ₙ(a − G i)`.  The correction `𝔾ₙ(a − G i)` splits into a random
empirical-average half and a deterministic `P`-mean half:
`|𝔾ₙ(a − G i)| ≤ √n·empAvg(2G i) + √n·P(2G i)`.  The random half **re-centres** onto the
cell-oscillation process itself, `√n·empAvg(2G i) = 𝔾ₙ(2G i) + √n·P(2G i)
≤ 2|𝔾ₙ(G i)| + √n·P(2G i)`, so the whole per-cell bound is
`|𝔾ₙ a| ≤ 3|𝔾ₙ(G i)| + 4√n·P(G i)` — with both pieces `f`-independent within the cell.

**Why `⨆_i`, not `Σ_i`.** Because the per-cell correction `4√n·P(G i)` is deterministic
(f-independent) and the cell-oscillation `|𝔾ₙ(G i)|` is the integrand of `levelOscSup`,
the outer `⨆_i (3|𝔾ₙ G_i| + 4√n·P G_i)` distributes by sup-subadditivity
`⨆_i (a_i + b_i) ≤ ⨆_i a_i + ⨆_i b_i` into `3⨆_i|𝔾ₙ G_i| + 4√n·⨆_i P(G_i)`.  The
correction is therefore a **max** over cells (`⨆_i`, no `N_q` over-count), which is the
genuine vdV maximal bound that folds dyadically. A `Σ_i` bound would over-count
by `N_q` and would not yield the required dyadic estimate.

The estimate is necessarily at the mean level because the corresponding
pointwise inequality for the signed process does not hold. It uses only the cell
structure; see vdV §19.6 p.287 and the displayed
`𝔾ₙ((f − π_q f)·B_q f)` triangle + maximal inequality. -/
theorem supNormOver_link_meanSplit_le
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    {δ : ℝ} (n : ℕ) {q : ℕ} (hq : q₀ ≤ q) :
    ∫⁻ ξ, ⨆ i : Fin (B.Nq q), ⨆ (f : Ω → ℝ) (_ : f ∈ B.cell q i),
        ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ)
            (fun x => (f x - B.π q i x)
              * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x)| ∂μ
      ≤ 3 * (∫⁻ ξ, ⨆ i : Fin (B.Nq q), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncOsc B δ n q i)| ∂μ)
        + 4 * ENNReal.ofReal (Real.sqrt n)
            * ⨆ i : Fin (B.Nq q), ∫⁻ x, ENNReal.ofReal
                (B.Δ q i x
                  * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x) ∂P := by
  classical
  -- Integrate the per-`ξ` mean split (`supNormOver_link_meanSplit_pointwise_le`),
  -- then split off the `ξ`-constant deterministic correction (`lintegral_const`).
  calc ∫⁻ ξ, ⨆ i : Fin (B.Nq q), ⨆ (f : Ω → ℝ) (_ : f ∈ B.cell q i),
          ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (fun x => (f x - B.π q i x)
                * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x)| ∂μ
      ≤ ∫⁻ ξ, (3 * (⨆ i : Fin (B.Nq q), ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ)
                (truncOsc B δ n q i)|)
            + 4 * ENNReal.ofReal (Real.sqrt n)
                * ⨆ i : Fin (B.Nq q), ∫⁻ x, ENNReal.ofReal
                    (B.Δ q i x
                      * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x) ∂P) ∂μ :=
        MeasureTheory.lintegral_mono
          (fun ξ => supNormOver_link_meanSplit_pointwise_le B hπ_meas hF_meas n hq ξ)
    _ = 3 * (∫⁻ ξ, ⨆ i : Fin (B.Nq q), ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ)
                (truncOsc B δ n q i)| ∂μ)
          + 4 * ENNReal.ofReal (Real.sqrt n)
              * ⨆ i : Fin (B.Nq q), ∫⁻ x, ENNReal.ofReal
                  (B.Δ q i x
                    * Set.indicator {y | chainB B δ n q i y} (1 : Ω → ℝ) x) ∂P := by
        rw [MeasureTheory.lintegral_add_right' _ measurable_const.aemeasurable]
        rw [MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
        rw [MeasureTheory.lintegral_const, measure_univ, mul_one]

/-- **Linearity of `empiricalProcess` over a `Finset` sum.** For a family of
integrable functions `h : ι → Ω → ℝ`, `𝔾ₙ(Σ_{a∈s} h a) = Σ_{a∈s} 𝔾ₙ(h a)`. Proven by
`Finset.induction`, using the binary `empiricalProcess_add` (each partial sum stays
integrable as a finite sum of integrables). -/
lemma empiricalProcess_finset_sum {ι : Type*} (P : Measure Ω) (n : ℕ) (X : Fin n → Ω)
    (s : Finset ι) (h : ι → Ω → ℝ) (hint : ∀ a ∈ s, Integrable (h a) P) :
    empiricalProcess P n X (fun x => ∑ a ∈ s, h a x)
      = ∑ a ∈ s, empiricalProcess P n X (h a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [empiricalProcess]
  | insert a s ha ih =>
      have hint' : ∀ b ∈ s, Integrable (h b) P :=
        fun b hb => hint b (Finset.mem_insert_of_mem hb)
      have hsum_int : Integrable (fun x => ∑ b ∈ s, h b x) P :=
        integrable_finset_sum s hint'
      rw [Finset.sum_insert ha]
      have hsplit : (fun x => ∑ b ∈ insert a s, h b x)
          = (fun x => h a x + ∑ b ∈ s, h b x) := by
        funext x; rw [Finset.sum_insert ha]
      rw [hsplit,
        empiricalProcess_add P n X (h a) (fun x => ∑ b ∈ s, h b x)
          (hint a (Finset.mem_insert_self a s)) hsum_int,
        ih hint']

/-- **The cell chain of `f`.** For `f ∈ F` with chosen level-`q₀` cell `i₀`
(`f ∈ cell q₀ i₀`), the index of the level-`(q₀ + k)` cell containing `f`, defined by
recursion on `k`: at `k = 0` it is `i₀`; at `k + 1` it is a `cover`-chosen cell of `f`
at level `q₀ + (k + 1)`. The chain is the book's "cell of `f` at each level"; its
successive parents reconstruct the representative telescope `π_{q₀+k} f`. -/
noncomputable def cellChain (B : NestedBracketPartition F P q₀ C)
    {f : Ω → ℝ} (hf : f ∈ F) : (k : ℕ) → Fin (B.Nq (q₀ + k))
  | 0 => Fin.cast (by rw [Nat.add_zero]) (Classical.choose (B.cover le_rfl f hf))
  | k + 1 => Classical.choose (B.cover (Nat.le_add_right q₀ (k + 1)) f hf)

/-- `f` lies in its level-`(q₀ + k)` cell-chain cell. -/
lemma cellChain_mem (B : NestedBracketPartition F P q₀ C)
    {f : Ω → ℝ} (hf : f ∈ F) (k : ℕ) :
    f ∈ B.cell (q₀ + k) (cellChain B hf k) := by
  cases k with
  | zero =>
      simp only [cellChain]
      -- `cell (q₀+0) (Fin.cast _ c) = cell q₀ c` (the index is cast back along `q₀+0=q₀`)
      have h := Classical.choose_spec (B.cover (le_refl q₀) f hf)
      have hcast : B.cell (q₀ + 0)
            (Fin.cast (by rw [Nat.add_zero]) (Classical.choose (B.cover le_rfl f hf)))
          = B.cell q₀ (Classical.choose (B.cover le_rfl f hf)) := by
        congr 1
      rw [hcast]
      exact h
  | succ k =>
      simp only [cellChain]
      exact Classical.choose_spec (B.cover (Nat.le_add_right q₀ (k + 1)) f hf)

/-- **Disjointness ⟹ unique cell.** If `f` lies in two level-`q` cells, the indices
agree. -/
lemma cell_unique (B : NestedBracketPartition F P q₀ C)
    {q : ℕ} (hq : q₀ ≤ q) {f : Ω → ℝ} {i j : Fin (B.Nq q)}
    (hi : f ∈ B.cell q i) (hj : f ∈ B.cell q j) : i = j := by
  by_contra hne
  exact (B.disjoint hq i j hne).notMem_of_mem_left hi hj

/-- The level-`q₀` cell-chain cell is the chosen cell `i₀` (cast through `q₀ + 0 = q₀`):
both contain `f`, so they agree by uniqueness. -/
lemma cellChain_zero (B : NestedBracketPartition F P q₀ C)
    {f : Ω → ℝ} (hf : f ∈ F) (i₀ : Fin (B.Nq q₀)) (hi₀ : f ∈ B.cell q₀ i₀) :
    cellChain B hf 0 = Fin.cast (by rw [Nat.add_zero]) i₀ := by
  have hmem0 : f ∈ B.cell q₀ (Fin.cast (by rw [Nat.add_zero]) (cellChain B hf 0)) := by
    have h := cellChain_mem B hf 0
    have hcast : B.cell (q₀ + 0) (cellChain B hf 0)
        = B.cell q₀ (Fin.cast (by rw [Nat.add_zero]) (cellChain B hf 0)) := by
      congr 1
    rwa [hcast] at h
  have := cell_unique B (le_refl q₀) hmem0 hi₀
  -- `Fin.cast _ (cellChain 0) = i₀`  ⟹  `cellChain 0 = Fin.cast _ i₀`
  apply Fin.cast_injective (by rw [Nat.add_zero] : B.Nq (q₀ + 0) = B.Nq q₀)
  rw [Fin.cast_cast, Fin.cast_eq_self]
  exact this

/-- **Parent step of the cell chain.** The level-`(q₀ + k)` parent of the level-
`(q₀ + (k + 1))` cell-chain cell is the level-`(q₀ + k)` cell-chain cell:
`parent (cellChain (k+1)) = cellChain k`. By uniqueness of the cell containing `f`. -/
lemma cellChain_parent (B : NestedBracketPartition F P q₀ C)
    {f : Ω → ℝ} (hf : f ∈ F) (k : ℕ) :
    B.parent (Nat.le_add_right q₀ k) (cellChain B hf (k + 1)) = cellChain B hf k := by
  -- `f ∈ cell (q₀+k+1) (chain (k+1)) ⊆ cell (q₀+k) (parent (chain (k+1)))`
  have h1 : f ∈ B.cell (q₀ + k) (B.parent (Nat.le_add_right q₀ k) (cellChain B hf (k + 1))) :=
    B.cell_succ_subset_parent (Nat.le_add_right q₀ k) (cellChain B hf (k + 1))
      (cellChain_mem B hf (k + 1))
  have h2 : f ∈ B.cell (q₀ + k) (cellChain B hf k) := cellChain_mem B hf k
  exact cell_unique B (Nat.le_add_right q₀ k) h1 h2

/-- **Ancestor of the chain is the chain.** For `p = q₀ + j ≤ q₀ + k`, the level-`p`
ancestor of the cell-chain cell at level `q₀ + k` is the cell-chain cell at level `p`.
By induction on the step `k`, using `cellChain_parent` + `ancestor_succ_of_le`. -/
lemma cellChain_ancestor (B : NestedBracketPartition F P q₀ C)
    {f : Ω → ℝ} (hf : f ∈ F) (k j : ℕ) (hjk : j ≤ k) :
    B.ancestor (Nat.le_add_right q₀ k) (cellChain B hf k) (q₀ + j)
        (Nat.le_add_right q₀ j) (by omega)
      = cellChain B hf j := by
  induction k with
  | zero =>
      have hj0 : j = 0 := Nat.le_zero.mp hjk
      subst hj0
      -- ancestor at top level is the cell itself
      simp only [Nat.add_zero] at *
      rw [B.ancestor_self]
  | succ k ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hjk) with hlt | heq
      · -- j ≤ k: step down through the parent
        have hjk' : j ≤ k := Nat.lt_succ_iff.mp hlt
        have hstep := B.ancestor_succ_of_le (Nat.le_add_right q₀ k) (cellChain B hf (k + 1))
          (q₀ + j) (Nat.le_add_right q₀ j) (by omega)
        -- rewrite the ancestor of (k+1) as the ancestor of its parent = chain k
        calc B.ancestor (Nat.le_add_right q₀ (k + 1)) (cellChain B hf (k + 1)) (q₀ + j)
                (Nat.le_add_right q₀ j) (by omega)
            = B.ancestor (Nat.le_add_right q₀ k)
                (B.parent (Nat.le_add_right q₀ k) (cellChain B hf (k + 1))) (q₀ + j)
                (Nat.le_add_right q₀ j) (by omega) := hstep
          _ = B.ancestor (Nat.le_add_right q₀ k) (cellChain B hf k) (q₀ + j)
                (Nat.le_add_right q₀ j) (by omega) := by
              rw [cellChain_parent B hf k]
          _ = cellChain B hf j := ih hjk'
      · -- j = k + 1: ancestor is the cell itself
        subst heq
        rw [B.ancestor_self]

/-- **The chain-cell A-gate reduces to per-level smallness.** For the cell chain of
`f`, `chainA` at the level-`(q₀+k)` chain cell holds at `x` iff every step `j ≤ k` is
small (`Δ_{q₀+j}(chain j) x ≤ √n·a_{q₀+j}`), via `cellChain_ancestor` collapsing the
ancestor to the chain cell. -/
lemma chainA_chain_iff (B : NestedBracketPartition F P q₀ C)
    {f : Ω → ℝ} (hf : f ∈ F) (δ : ℝ) (n k : ℕ) (x : Ω) :
    chainA B δ n (q₀ + k) (cellChain B hf k) x
      ↔ ∀ j ≤ k, B.Δ (q₀ + j) (cellChain B hf j) x
            ≤ Real.sqrt n * chainThreshold B δ (q₀ + j) := by
  constructor
  · intro h j hjk
    have := h (q₀ + j) (Nat.le_add_right q₀ j) (by omega)
    rwa [cellChain_ancestor B hf k j hjk] at this
  · intro h p hp₀ hpq
    obtain ⟨j, rfl⟩ : ∃ j, p = q₀ + j := ⟨p - q₀, by omega⟩
    have hjk : j ≤ k := by omega
    rw [cellChain_ancestor B hf k j hjk]
    exact h j hjk

/-- **The chain-cell B-gate reduces to first-crossing.** For the cell chain of `f`,
`chainB` at the level-`(q₀+k)` chain cell holds at `x` iff `k > 0`, every earlier step
`j < k` is small, and step `k` crosses (`¬ small`). -/
lemma chainB_chain_iff (B : NestedBracketPartition F P q₀ C)
    {f : Ω → ℝ} (hf : f ∈ F) (δ : ℝ) (n k : ℕ) (x : Ω) :
    chainB B δ n (q₀ + k) (cellChain B hf k) x
      ↔ 0 < k
        ∧ (∀ j < k, B.Δ (q₀ + j) (cellChain B hf j) x
              ≤ Real.sqrt n * chainThreshold B δ (q₀ + j))
        ∧ ¬ (B.Δ (q₀ + k) (cellChain B hf k) x
              ≤ Real.sqrt n * chainThreshold B δ (q₀ + k)) := by
  unfold chainB
  constructor
  · rintro ⟨hlt, hsmall, hcross⟩
    refine ⟨by omega, ?_, by rw [not_le]; exact hcross⟩
    intro j hjk
    have := hsmall (q₀ + j) (Nat.le_add_right q₀ j) (by omega)
    rwa [cellChain_ancestor B hf k j (le_of_lt hjk)] at this
  · rintro ⟨hk, hsmall, hcross⟩
    refine ⟨by omega, ?_, by rw [not_le] at hcross; exact hcross⟩
    intro p hp₀ hpq
    obtain ⟨j, rfl⟩ : ∃ j, p = q₀ + j := ⟨p - q₀, by omega⟩
    have hjk : j < k := by omega
    rw [cellChain_ancestor B hf k j (le_of_lt hjk)]
    exact hsmall j hjk

omit [MeasurableSpace Ξ] in
/-- **Gated-telescope interchange (vdV p.287, the genuine chaining hand-wave).**

For a fixed sample point `ξ` and a function `f ∈ F` with `q₀`-cell `i₀`
(`f ∈ cell q₀ i₀`, so `π_{q₀}f = B.π q₀ i₀`), the centred empirical-process value
`𝔾ₙ(f − π_{q₀}f)(ξ)` is dominated, in `ℝ≥0∞`, by the two gated chaining series:

* the **B-link** series `∑'_q ⨆ᵢ ⨆_{g∈cell(q₀+q) i} ofReal|𝔾ₙ((g − π_{q₀+q} i)·1{chainB})|`;
* the **A-series** jump sups `∑'_q ⨆ᵢ ofReal|𝔾ₙ(truncJump i)|`.

This isolates vdV's genuine hand-wave (§19.6 p.287, *"q₁ possibly infinite"*):
the **gated telescope** `f − π_{q₀}f = Σ_{q≥q₀} (π_{q+1}f − π_q f)·A_q f +
Σ_{q>q₀} (f − π_q f)·B_q f` (each indicator gating its sum to a single relevant
term per `(f, x)`: at most one B-break level `q₁`, A-jumps up to it), and the
**interchange** `𝔾ₙ(f − π_{q₀}f) = Σ_q 𝔾ₙ(gated link_q)`. On the *crossing* branch
the telescope is finite (`chain_pointwise_telescope` at `q₁`); on the
*never-crossing* branch (all `Δ_q ≤ √n·a_q`) the tail closes by DCT: the sample
part `Pₙ(f − π_Q f) → 0` (finite-`i` sum, `π_Q f(Xᵢ) → f(Xᵢ)` since
`|f − π_Q f| ≤ Δ_Q ≤ √n·chainThreshold Q ≤ √n·(1/2)^{Q−q₀}δ → 0`), and the
population part `P(f − π_Q f) → 0` dominated by `Δ_{q₀} ∈ L¹` (`Δ_memLp ⊆ L¹` on a
probability space). The finite `Finset.Ioc` partial sum is dominated by the full
`∑'_q` series (`ENNReal` monotonicity, nonneg terms). vdV §19.6 p.287. -/
private theorem Gn_telescope_link_bound
    [IsProbabilityMeasure P]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n) (ξ : Ξ)
    {f : Ω → ℝ} (hf : f ∈ F) (i₀ : Fin (B.Nq q₀)) (hi₀ : f ∈ B.cell q₀ i₀)
    (hA_q0 : ∀ x, B.Δ q₀ i₀ x ≤ Real.sqrt n * chainThreshold B δ q₀) :
    ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ)
          (fun x => f x - B.π q₀ i₀ x)|
      ≤ (∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q)),
            ⨆ (g : Ω → ℝ) (_ : g ∈ B.cell (q₀ + q) i), ENNReal.ofReal
              |empiricalProcess P n (fun j : Fin n => X j.val ξ)
                (fun x => (g x - B.π (q₀ + q) i x)
                  * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x)|)
        + (∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q + 1)), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncJump B δ n (Nat.le_add_right q₀ q) i)|) := by
  classical
  set Y : Fin n → Ω := fun k : Fin n => X k.val ξ with hY_def
  have hsn_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  -- The chain representatives and the per-level smallness predicate.
  set c : (k : ℕ) → Fin (B.Nq (q₀ + k)) := fun k => cellChain B hf k with hc_def
  set r : ℕ → Ω → ℝ := fun k => B.π (q₀ + k) (c k) with hr_def
  -- `r 0 = π q₀ i₀`.
  have hr0 : r 0 = B.π q₀ i₀ := by
    simp only [hr_def, hc_def]
    rw [cellChain_zero B hf i₀ hi₀]
    congr 1
  -- The level-`(q₀+k)` cell oscillation envelope of the chain cell.
  set D : ℕ → Ω → ℝ := fun k => B.Δ (q₀ + k) (c k) with hD_def
  have hf_meas' : Measurable f := hF_meas f hf
  have hr_meas : ∀ k, Measurable (r k) := fun k => hπ_meas (Nat.le_add_right q₀ k) (c k)
  have hD_meas : ∀ k, Measurable (D k) := fun k => B.Δ_meas (Nat.le_add_right q₀ k) (c k)
  have hD_nn : ∀ k x, 0 ≤ D k x := by
    intro k x
    have := B.diam (Nat.le_add_right q₀ k) (c k) (B.π (q₀+k) (c k))
      (B.π_mem (Nat.le_add_right q₀ k) (c k)) (B.π (q₀+k) (c k))
      (B.π_mem (Nat.le_add_right q₀ k) (c k)) x
    simpa [hD_def] using this
  have hD_int : ∀ k, Integrable (D k) P :=
    fun k => (B.Δ_memLp (Nat.le_add_right q₀ k) (c k)).integrable (by norm_num)
  -- `f` lies in its chain cell, so `|f − r k| ≤ D k` pointwise (cell diam).
  have hf_mem : ∀ k, f ∈ B.cell (q₀ + k) (c k) := fun k => cellChain_mem B hf k
  have hfr_le : ∀ k x, |f x - r k x| ≤ D k x := by
    intro k x
    exact B.diam (Nat.le_add_right q₀ k) (c k) f (hf_mem k) (B.π (q₀+k) (c k))
      (B.π_mem (Nat.le_add_right q₀ k) (c k)) x
  -- `f · 1{measurable set}` shifted by `r k` is integrable: `|(f − r k)·1| ≤ D k ∈ L¹`.
  have hgated_int : ∀ (k : ℕ) (s : Set Ω), MeasurableSet s →
      Integrable (fun x => (f x - r k x) * Set.indicator s (1 : Ω → ℝ) x) P := by
    intro k s hs
    refine Integrable.mono' (hD_int k)
      ((hf_meas'.sub (hr_meas k)).mul (measurable_const.indicator hs)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    calc |f x - r k x| * |Set.indicator s (1 : Ω → ℝ) x|
        ≤ D k x * 1 := by
          refine mul_le_mul (hfr_le k x) ?_ (abs_nonneg _) (hD_nn k x)
          by_cases hx : x ∈ s
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
      _ = D k x := mul_one _
  -- The jump equals the representative difference, and is bounded by `D k`.
  have hjump_eq : ∀ k, B.jump (Nat.le_add_right q₀ k) (c (k+1))
      = (fun x => r (k+1) x - r k x) := by
    intro k; funext x
    simp only [NestedBracketPartition.jump, hr_def, hc_def]
    rw [cellChain_parent B hf k]
    rfl
  have hjump_le : ∀ k x, |B.jump (Nat.le_add_right q₀ k) (c (k+1)) x| ≤ D k x := by
    intro k x
    have := B.jump_abs_le (Nat.le_add_right q₀ k) (c (k+1)) x
    rwa [cellChain_parent B hf k] at this
  -- The A-gate / B-gate measurable sets and their indicators.
  set As : ℕ → Set Ω := fun k => {y | chainA B δ n (q₀ + k) (c k) y} with hAs_def
  set Bs : ℕ → Set Ω := fun k => {y | chainB B δ n (q₀ + k) (c k) y} with hBs_def
  have hAs_meas : ∀ k, MeasurableSet (As k) :=
    fun k => chainA_measurableSet B δ n (q₀ + k) (c k)
  have hBs_meas : ∀ k, MeasurableSet (Bs k) :=
    fun k => chainB_measurableSet B n (Nat.le_add_right q₀ k) (c k)
  -- The chain links: B-link at level `q₀+k`, A-jump from level `q₀+k` to `q₀+(k+1)`,
  -- and the remainder `R K` at level `q₀+K`.
  set linkB : ℕ → Ω → ℝ := fun k x =>
    (f x - r k x) * Set.indicator (Bs k) (1 : Ω → ℝ) x with hlinkB_def
  set linkJ : ℕ → Ω → ℝ := fun k x =>
    (r (k+1) x - r k x) * Set.indicator (As k) (1 : Ω → ℝ) x with hlinkJ_def
  set Rrem : ℕ → Ω → ℝ := fun K x =>
    (f x - r K x) * Set.indicator (As K) (1 : Ω → ℝ) x with hRrem_def
  -- Integrability of the three link families.
  have hlinkB_int : ∀ k, Integrable (linkB k) P :=
    fun k => hgated_int k (Bs k) (hBs_meas k)
  have hRrem_int : ∀ K, Integrable (Rrem K) P :=
    fun K => hgated_int K (As K) (hAs_meas K)
  have hlinkJ_int : ∀ k, Integrable (linkJ k) P := by
    intro k
    have hjeq : linkJ k = fun x => B.jump (Nat.le_add_right q₀ k) (c (k+1)) x
        * Set.indicator (As k) (1 : Ω → ℝ) x := by
      funext x; simp only [hlinkJ_def]; rw [hjump_eq k]
    rw [hjeq]
    refine Integrable.mono' (hD_int k)
      (((B.jump_measurable hπ_meas (Nat.le_add_right q₀ k) (c (k+1))).mul
        (measurable_const.indicator (hAs_meas k))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    calc |B.jump (Nat.le_add_right q₀ k) (c (k+1)) x| * |Set.indicator (As k) (1 : Ω → ℝ) x|
        ≤ D k x * 1 := by
          refine mul_le_mul (hjump_le k x) ?_ (abs_nonneg _) (hD_nn k x)
          by_cases hx : x ∈ As k
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]
      _ = D k x := mul_one _
  -- Per-level smallness predicate `small k x := D k x ≤ √n·a_{q₀+k}`.
  set small : ℕ → Ω → Prop := fun k x =>
    D k x ≤ Real.sqrt n * chainThreshold B δ (q₀ + k) with hsmall_def
  -- `small 0` always holds (this is exactly `hA_q0`, since `c 0 = i₀` and `D 0 = Δ_{q₀} i₀`).
  have hsmall0 : ∀ x, small 0 x := by
    intro x
    simp only [hsmall_def, hD_def, hc_def]
    rw [cellChain_zero B hf i₀ hi₀]
    have hcast : B.Δ (q₀ + 0) (Fin.cast (by rw [Nat.add_zero]) i₀) x = B.Δ q₀ i₀ x := by
      congr 1
    rw [hcast]
    have : Real.sqrt n * chainThreshold B δ (q₀ + 0) = Real.sqrt n * chainThreshold B δ q₀ := by
      norm_num
    rw [this]; exact hA_q0 x
  -- `x ∈ As k ↔ ∀ j ≤ k, small j x`.
  have hAs_iff : ∀ k x, x ∈ As k ↔ ∀ j ≤ k, small j x := by
    intro k x
    simp only [hAs_def, hc_def, Set.mem_setOf_eq]
    rw [chainA_chain_iff B hf δ n k x]
  -- `x ∈ Bs (k+1) ↔ (∀ j ≤ k, small j x) ∧ ¬ small (k+1) x`.
  have hBs_iff : ∀ k x, x ∈ Bs (k+1) ↔ (∀ j ≤ k, small j x) ∧ ¬ small (k+1) x := by
    intro k x
    simp only [hBs_def, hc_def, Set.mem_setOf_eq]
    rw [chainB_chain_iff B hf δ n (k+1) x]
    constructor
    · rintro ⟨_, hsm, hcr⟩
      exact ⟨fun j hj => hsm j (by omega), hcr⟩
    · rintro ⟨hsm, hcr⟩
      exact ⟨by omega, fun j hj => hsm j (by omega), hcr⟩
  -- The indicator value of `As k` at `x` (0/1, real).
  have hindA : ∀ k x, Set.indicator (As k) (1 : Ω → ℝ) x
      = if x ∈ As k then (1 : ℝ) else 0 := by
    intro k x; by_cases hx : x ∈ As k <;> simp [Set.indicator, hx]
  have hindB : ∀ k x, Set.indicator (Bs k) (1 : Ω → ℝ) x
      = if x ∈ Bs k then (1 : ℝ) else 0 := by
    intro k x; by_cases hx : x ∈ Bs k <;> simp [Set.indicator, hx]
  -- ===== THE FINITE TELESCOPE IDENTITY (pointwise in `x`, for each step count `K`). =====
  -- `f − r 0 = Rrem K + Σ_{k<K} linkJ k + Σ_{k<K} linkB (k+1)`.
  have htel : ∀ K x,
      f x - r 0 x
        = Rrem K x + (∑ k ∈ Finset.range K, linkJ k x)
            + (∑ k ∈ Finset.range K, linkB (k+1) x) := by
    intro K x
    induction K with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, add_zero]
        -- `Rrem 0 x = (f − r 0)·[As 0] = f − r 0` since `As 0` holds.
        have hA0 : x ∈ As 0 := (hAs_iff 0 x).mpr (fun j hj => by
          have : j = 0 := Nat.le_zero.mp hj
          subst this; exact hsmall0 x)
        simp only [hRrem_def, hindA, if_pos hA0, mul_one]
    | succ K ih =>
        -- Reduce to `Rrem (K+1) + linkJ K + linkB (K+1) = Rrem K`, then use `ih`.
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have hstep : Rrem (K+1) x + linkJ K x + linkB (K+1) x = Rrem K x := by
          -- Indicator values via the smallness reductions.
          have hAK : x ∈ As K ↔ ∀ j ≤ K, small j x := hAs_iff K x
          have hAK1 : x ∈ As (K+1) ↔ ∀ j ≤ K+1, small j x := hAs_iff (K+1) x
          have hBK1 : x ∈ Bs (K+1) ↔ (∀ j ≤ K, small j x) ∧ ¬ small (K+1) x := hBs_iff K x
          simp only [hRrem_def, hlinkJ_def, hlinkB_def, hindA, hindB]
          by_cases hAk : x ∈ As K
          · -- chain still small through K
            have hsmK : ∀ j ≤ K, small j x := hAK.mp hAk
            by_cases hsk1 : small (K+1) x
            · -- still small at K+1: As(K+1) holds, Bs(K+1) fails
              have hAk1 : x ∈ As (K+1) := hAK1.mpr (fun j hj => by
                rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hj) with h | h
                · exact hsmK j (by omega)
                · subst h; exact hsk1)
              have hBk1 : x ∉ Bs (K+1) := by
                rw [hBK1]; rintro ⟨_, hcr⟩; exact hcr hsk1
              simp only [if_pos hAk, if_pos hAk1, if_neg hBk1, mul_one, mul_zero, add_zero]
              ring
            · -- crosses at K+1: As(K+1) fails, Bs(K+1) holds
              have hAk1 : x ∉ As (K+1) := by
                rw [hAK1]; intro h; exact hsk1 (h (K+1) le_rfl)
              have hBk1 : x ∈ Bs (K+1) := hBK1.mpr ⟨hsmK, hsk1⟩
              simp only [if_pos hAk, if_neg hAk1, if_pos hBk1, mul_one, mul_zero, zero_add]
              ring
          · -- chain already crossed before K: all three indicators are 0
            have hAk1 : x ∉ As (K+1) := by
              rw [hAK1]; intro h; exact hAk (hAK.mpr (fun j hj => h j (by omega)))
            have hBk1 : x ∉ Bs (K+1) := by
              rw [hBK1]; rintro ⟨hsm, _⟩; exact hAk (hAK.mpr hsm)
            simp only [if_neg hAk, if_neg hAk1, if_neg hBk1, mul_zero, add_zero]
        -- Combine the split sums via `hstep` and the inductive hypothesis.
        rw [ih]
        -- rearrange so `hstep` applies
        have : Rrem (K+1) x + (∑ k ∈ Finset.range K, linkJ k x + linkJ K x)
              + (∑ k ∈ Finset.range K, linkB (k+1) x + linkB (K+1) x)
            = (Rrem (K+1) x + linkJ K x + linkB (K+1) x)
              + ((∑ k ∈ Finset.range K, linkJ k x) + (∑ k ∈ Finset.range K, linkB (k+1) x)) := by
          ring
        rw [this, hstep]
        ring
  -- ===== Apply `𝔾ₙ` to the telescope (linearity over the finite sum). =====
  -- `gn h := 𝔾ₙ h (ξ)`.
  set gn : (Ω → ℝ) → ℝ := fun h => empiricalProcess P n Y h with hgn_def
  have hgn_tel : ∀ K,
      gn (fun x => f x - r 0 x)
        = gn (Rrem K) + (∑ k ∈ Finset.range K, gn (linkJ k))
            + (∑ k ∈ Finset.range K, gn (linkB (k+1))) := by
    intro K
    -- Rewrite the integrand via the pointwise telescope identity.
    have hfun : (fun x => f x - r 0 x)
        = (fun x => Rrem K x
            + ((∑ k ∈ Finset.range K, linkJ k x) + (∑ k ∈ Finset.range K, linkB (k+1) x))) := by
      funext x; rw [htel K x]; ring
    rw [hfun]
    -- integrability of the two finite sums
    have hJsum_int : Integrable (fun x => ∑ k ∈ Finset.range K, linkJ k x) P :=
      integrable_finset_sum _ (fun k _ => hlinkJ_int k)
    have hBsum_int : Integrable (fun x => ∑ k ∈ Finset.range K, linkB (k+1) x) P :=
      integrable_finset_sum _ (fun k _ => hlinkB_int (k+1))
    simp only [hgn_def]
    rw [empiricalProcess_add P n Y (Rrem K)
        (fun x => (∑ k ∈ Finset.range K, linkJ k x) + (∑ k ∈ Finset.range K, linkB (k+1) x))
        (hRrem_int K) (hJsum_int.add hBsum_int)]
    rw [empiricalProcess_add P n Y (fun x => ∑ k ∈ Finset.range K, linkJ k x)
        (fun x => ∑ k ∈ Finset.range K, linkB (k+1) x) hJsum_int hBsum_int]
    rw [empiricalProcess_finset_sum P n Y (Finset.range K) linkJ (fun k _ => hlinkJ_int k)]
    rw [empiricalProcess_finset_sum P n Y (Finset.range K) (fun k => linkB (k+1))
        (fun k _ => hlinkB_int (k+1))]
    ring
  -- ===== Remainder bound: `|gn (Rrem K)| ≤ 2·n·(1/2)^K·δ → 0`. =====
  have hct_le : ∀ K, chainThreshold B δ (q₀ + K) ≤ (1/2 : ℝ)^K * δ := by
    intro K
    simp only [chainThreshold]
    rw [Nat.add_sub_cancel_left, div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ 1 + Real.sqrt (Real.log (1 + ↑(B.Nq (q₀ + K + 1)))) := by
      have := Real.sqrt_nonneg (Real.log (1 + ↑(B.Nq (q₀ + K + 1)))); linarith
    have hnum_nn : (0 : ℝ) ≤ (1/2 : ℝ)^K * δ :=
      mul_nonneg (pow_nonneg (by norm_num) K) hδ.le
    nlinarith [hnum_nn, h1]
  -- Pointwise uniform bound on `Rrem K`.
  set M : ℕ → ℝ := fun K => Real.sqrt n * ((1/2 : ℝ)^K * δ) with hM_def
  have hM_nn : ∀ K, 0 ≤ M K := fun K => by
    simp only [hM_def]; positivity
  have hRrem_bd : ∀ K x, |Rrem K x| ≤ M K := by
    intro K x
    simp only [hRrem_def]
    by_cases hx : x ∈ As K
    · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
      have hsmall_K : small K x := (hAs_iff K x).mp hx K le_rfl
      calc |f x - r K x| ≤ D K x := hfr_le K x
        _ ≤ Real.sqrt n * chainThreshold B δ (q₀ + K) := hsmall_K
        _ ≤ Real.sqrt n * ((1/2 : ℝ)^K * δ) :=
            mul_le_mul_of_nonneg_left (hct_le K) hsn_nn
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact hM_nn K
  -- `|gn (Rrem K)| ≤ 2·n·(1/2)^K·δ`.
  have hgnR_bd : ∀ K, |gn (Rrem K)| ≤ 2 * (n : ℝ) * ((1/2 : ℝ)^K * δ) := by
    intro K
    simp only [hgn_def, empiricalProcess]
    rw [abs_mul, abs_of_nonneg hsn_nn]
    -- `|empAvg − ∫| ≤ |empAvg| + |∫| ≤ M K + M K`
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hn
    have hempavg : |empiricalAvg (Rrem K) n Y| ≤ M K := by
      simp only [empiricalAvg]
      rw [abs_mul, abs_inv, Nat.abs_cast]
      have hsum_le : |∑ i, Rrem K (Y i)| ≤ (n : ℝ) * M K := by
        calc |∑ i, Rrem K (Y i)| ≤ ∑ i : Fin n, |Rrem K (Y i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, M K := Finset.sum_le_sum (fun i _ => hRrem_bd K (Y i))
          _ = (n : ℝ) * M K := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc (n : ℝ)⁻¹ * |∑ i, Rrem K (Y i)|
          ≤ (n : ℝ)⁻¹ * ((n : ℝ) * M K) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = M K := by rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
    have hintbd : |∫ x, Rrem K x ∂P| ≤ M K := by
      calc |∫ x, Rrem K x ∂P| ≤ ∫ x, |Rrem K x| ∂P := abs_integral_le_integral_abs
        _ ≤ ∫ _x, M K ∂P := by
            refine integral_mono ((hRrem_int K).abs) (integrable_const _) (fun x => hRrem_bd K x)
        _ = M K := by simp
    have hsqsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (by positivity)
    calc Real.sqrt n * |empiricalAvg (Rrem K) n Y - ∫ x, Rrem K x ∂P|
        ≤ Real.sqrt n * (M K + M K) := by
          refine mul_le_mul_of_nonneg_left ?_ hsn_nn
          calc |empiricalAvg (Rrem K) n Y - ∫ x, Rrem K x ∂P|
              ≤ |empiricalAvg (Rrem K) n Y| + |∫ x, Rrem K x ∂P| := abs_sub _ _
            _ ≤ M K + M K := add_le_add hempavg hintbd
      _ = 2 * (n : ℝ) * ((1/2 : ℝ)^K * δ) := by
          simp only [hM_def]
          linear_combination (2 * ((1/2 : ℝ)^K * δ)) * hsqsq
  -- `ofReal|gn (Rrem K)| → 0`, by squeeze under `ofReal (2 n (1/2)^K δ) → 0`.
  have hgnR_tendsto : Filter.Tendsto (fun K => ENNReal.ofReal |gn (Rrem K)|)
      Filter.atTop (𝓝 0) := by
    have hbd : Filter.Tendsto
        (fun K => ENNReal.ofReal (2 * (n : ℝ) * ((1/2 : ℝ)^K * δ))) Filter.atTop (𝓝 0) := by
      rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 by simp]
      refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
      have hgeom : Filter.Tendsto (fun K => (1/2 : ℝ)^K) Filter.atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have : Filter.Tendsto (fun K => 2 * (n : ℝ) * ((1/2 : ℝ)^K * δ)) Filter.atTop
          (𝓝 (2 * (n : ℝ) * (0 * δ))) := by
        exact (tendsto_const_nhds.mul ((hgeom.mul tendsto_const_nhds)))
      simpa using this
    -- ℝ≥0∞ squeeze: `0 ≤ ofReal|gn(Rrem K)| ≤ ofReal(2 n (1/2)^K δ) → 0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hbd (Filter.Eventually.of_forall (fun K => zero_le))
      (Filter.Eventually.of_forall (fun K => ?_))
    exact ENNReal.ofReal_le_ofReal (hgnR_bd K)
  -- ===== Per-`K` ENNReal triangle bound, then pass to the limit. =====
  -- The two target series (as `tsum`s of the per-level terms).
  set bTerm : ℕ → ℝ≥0∞ := fun q => ⨆ i : Fin (B.Nq (q₀ + q)),
      ⨆ (g : Ω → ℝ) (_ : g ∈ B.cell (q₀ + q) i), ENNReal.ofReal
        |empiricalProcess P n Y
          (fun x => (g x - B.π (q₀ + q) i x)
            * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x)| with hbTerm_def
  set jTerm : ℕ → ℝ≥0∞ := fun q => ⨆ i : Fin (B.Nq (q₀ + q + 1)), ENNReal.ofReal
      |empiricalProcess P n Y (truncJump B δ n (Nat.le_add_right q₀ q) i)| with hjTerm_def
  set Sb : ℝ≥0∞ := ∑' q : ℕ, bTerm q with hSb_def
  set Sj : ℝ≥0∞ := ∑' q : ℕ, jTerm q with hSj_def
  -- Each B-link lands in the `(k+1)`-th B-term, each A-jump in the `k`-th jump-term.
  have hlinkB_le : ∀ k, ENNReal.ofReal |gn (linkB (k+1))| ≤ bTerm (k+1) := by
    intro k
    rw [hbTerm_def]
    -- `linkB (k+1) = (f − π_{q₀+(k+1)} (c (k+1)))·1{chainB …}`; pick `g = f`, `i = c (k+1)`.
    refine le_trans (le_of_eq ?_) (le_iSup_of_le (c (k+1)) (le_iSup₂_of_le f (hf_mem (k+1)) le_rfl))
    simp only [hgn_def, hlinkB_def, hr_def, hc_def, hBs_def]
  have hlinkJ_le : ∀ k, ENNReal.ofReal |gn (linkJ k)| ≤ jTerm k := by
    intro k
    rw [hjTerm_def]
    refine le_iSup_of_le (c (k+1)) (le_of_eq ?_)
    -- `linkJ k = truncJump B δ n (Nat.le_add_right q₀ k) (c (k+1))`.
    have heq : linkJ k = truncJump B δ n (Nat.le_add_right q₀ k) (c (k+1)) := by
      funext x
      simp only [hlinkJ_def, truncJump]
      rw [hjump_eq k]
      congr 2
      simp only [hAs_def, hc_def]
      rw [cellChain_parent B hf k]
    rw [hgn_def, heq]
  -- Finite-sum ENNReal triangle: `ofReal|Σ a_k| ≤ Σ ofReal|a_k|`.
  have htri_fin : ∀ (s : Finset ℕ) (a : ℕ → ℝ),
      ENNReal.ofReal |∑ k ∈ s, a k| ≤ ∑ k ∈ s, ENNReal.ofReal |a k| := by
    intro s a
    induction s using Finset.induction with
    | empty => simp
    | insert b s hb ih =>
        rw [Finset.sum_insert hb, Finset.sum_insert hb]
        calc ENNReal.ofReal |a b + ∑ k ∈ s, a k|
            ≤ ENNReal.ofReal (|a b| + |∑ k ∈ s, a k|) :=
              ENNReal.ofReal_le_ofReal (abs_add_le _ _)
          _ ≤ ENNReal.ofReal |a b| + ENNReal.ofReal |∑ k ∈ s, a k| := ENNReal.ofReal_add_le
          _ ≤ ENNReal.ofReal |a b| + ∑ k ∈ s, ENNReal.ofReal |a k| := add_le_add le_rfl ih
  -- The per-`K` bound.
  have hperK : ∀ K, ENNReal.ofReal |gn (fun x => f x - B.π q₀ i₀ x)|
      ≤ ENNReal.ofReal |gn (Rrem K)| + (Sb + Sj) := by
    intro K
    have hrw : (fun x => f x - B.π q₀ i₀ x) = (fun x => f x - r 0 x) := by rw [hr0]
    rw [hrw, hgn_tel K]
    -- triangle (left-associated), then dominate the two finite sums by their tsums
    have hAbsA : ENNReal.ofReal |gn (Rrem K) + (∑ k ∈ Finset.range K, gn (linkJ k))
            + (∑ k ∈ Finset.range K, gn (linkB (k+1)))|
        ≤ ENNReal.ofReal |gn (Rrem K)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkJ k)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkB (k+1))| := by
      refine le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _)) ?_
      refine le_trans ENNReal.ofReal_add_le ?_
      refine add_le_add ?_ le_rfl
      refine le_trans (ENNReal.ofReal_le_ofReal (abs_add_le _ _)) ENNReal.ofReal_add_le
    have hJsum_le_Sj : ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkJ k)| ≤ Sj := by
      refine le_trans (htri_fin _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun k _ => hlinkJ_le k)) ?_
      rw [hSj_def]; exact ENNReal.sum_le_tsum _
    have hBsum_le_Sb : ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkB (k+1))| ≤ Sb := by
      refine le_trans (htri_fin _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun k _ => hlinkB_le k)) ?_
      rw [hSb_def]
      refine le_trans (le_of_eq ?_)
        (ENNReal.sum_le_tsum ((Finset.range K).map ⟨Nat.succ, Nat.succ_injective⟩))
      rw [Finset.sum_map]; rfl
    calc ENNReal.ofReal |gn (Rrem K) + (∑ k ∈ Finset.range K, gn (linkJ k))
            + (∑ k ∈ Finset.range K, gn (linkB (k+1)))|
        ≤ ENNReal.ofReal |gn (Rrem K)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkJ k)|
            + ENNReal.ofReal |∑ k ∈ Finset.range K, gn (linkB (k+1))| := hAbsA
      _ ≤ ENNReal.ofReal |gn (Rrem K)| + Sj + Sb :=
          add_le_add (add_le_add le_rfl hJsum_le_Sj) hBsum_le_Sb
      _ = ENNReal.ofReal |gn (Rrem K)| + (Sb + Sj) := by
          rw [add_assoc, add_comm Sj Sb]
  -- ===== Pass to the limit `K → ∞`: `LHS ≤ 0 + (Sb + Sj)`. =====
  have hlim : Filter.Tendsto (fun K => ENNReal.ofReal |gn (Rrem K)| + (Sb + Sj))
      Filter.atTop (𝓝 (Sb + Sj)) := by
    have := hgnR_tendsto.add (tendsto_const_nhds (x := Sb + Sj))
    rwa [zero_add] at this
  simp only [hgn_def] at hperK hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards with K
  simpa using hperK K

omit [MeasurableSpace Ξ] in
/-- **Per-`ξ` gated-telescope pointwise bound (vdV p.287, the genuine chaining
hand-wave).**

For each sample point `ξ`, the empirical-process supremum
`supNormOver F (𝔾ₙ ·)(ξ)` is pointwise dominated by the four chaining integrands
*before integration*:

* the **head** finite-sup `⨆ᵢ ofReal|𝔾ₙ(truncRep i)|`;
* the **threshold-truncated** evaluator sup `supNormOver F (𝔾ₙ(f·1{√n·a<|Φ|}))`;
* the **B-link** series `∑'_q ⨆ᵢ ⨆_{f∈cell} ofReal|𝔾ₙ((f − π_{q₀+q} i)·1{chainB})|`,
  in honest `f`-dependent form, with the signed-`𝔾ₙ` mean correction incorporated
  by `chain_supnorm_le_three_part`;
* the **A-series** jump sups `∑'_q ⨆ᵢ ofReal|𝔾ₙ(truncJump i)|`.

This is the **gated telescope**: for each `ξ` and `f ∈ F`, either every level's
oscillation stays below the threshold `√n·a_q` (the *never-crossing* branch, on
which `π_q f → f` is gate-forced: `chainThreshold q ≤ (1/2)^{q−q₀}δ → 0`, so
`Δ_q f(x) ≤ √n·chainThreshold q → 0` and `|f − π_Q f| ≤ Δ_Q f → 0`), or there is a
first crossing level `q₁` (the B-term break, `chain_pointwise_telescope` at `q₁`).
The head/envelope split proceeds as follows. For each `f ∈ F`
with `q₀`-cell `i₀`, the pointwise identity `f = π_{q₀}f·1{≤} + π_{q₀}f·1{>} +
(f − π_{q₀}f)` (complementary envelope indicators) lifts through `𝔾ₙ`-linearity
(`empiricalProcess_add`, all three pieces integrable since `|·| ≤ Φ ∈ L²(P) ⊆ L¹`
on a probability space) and `abs_add` to
`ofReal|𝔾ₙ f| ≤ ofReal|𝔾ₙ(truncRep i₀)| + ofReal|𝔾ₙ(π_{q₀}f·1{>})| + ofReal|𝔾ₙ(f − π_{q₀}f)|`.
The first piece is `≤ head` (`le_iSup` at `i₀`); the second is `≤ trunc` because
`π_{q₀}f = B.π q₀ i₀ ∈ F` (so it is captured by the `supNormOver F` of the
envelope-tail evaluator); the third is `≤ blink + jump` by
`Gn_telescope_link_bound`, the gated-telescope interchange corresponding to
vdV's *"q₁ possibly infinite"* argument. The assumptions
`[IsProbabilityMeasure P]`, `hΦ_meas`, `hπ_meas`, and `hF_meas` ensure the
integrability needed for the `𝔾ₙ`-linearity split. -/
private theorem chain_supnorm_le_pointwise
    [IsProbabilityMeasure P]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (hΦ_env : IsEnvelope F Φ) (hΦ_L2 : MemLp Φ 2 P)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n) (ξ : Ξ)
    (hΔq0_ptwise : ∀ (i : Fin (B.Nq q₀)) (x : Ω),
      B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δ q₀) :
    supNormOver F
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
      ≤ (⨆ i : Fin (B.Nq q₀), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncRep B Φ δ n q₀ i)|)
        + ((supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)))
            + (∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q)),
                ⨆ (f : Ω → ℝ) (_ : f ∈ B.cell (q₀ + q) i), ENNReal.ofReal
                  |empiricalProcess P n (fun j : Fin n => X j.val ξ)
                    (fun x => (f x - B.π (q₀ + q) i x)
                      * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x)|))
        + (∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q + 1)), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncJump B δ n (Nat.le_add_right q₀ q) i)|) := by
  classical
  -- Abbreviations for the four RHS pieces (constant in `f`).
  set head : ℝ≥0∞ := ⨆ i : Fin (B.Nq q₀), ENNReal.ofReal
      |empiricalProcess P n (fun k : Fin n => X k.val ξ)
        (truncRep B Φ δ n q₀ i)| with hhead_def
  set trunc : ℝ≥0∞ := supNormOver F
      (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun x => f x
          * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x))
    with htrunc_def
  set blink : ℝ≥0∞ := ∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q)),
      ⨆ (f : Ω → ℝ) (_ : f ∈ B.cell (q₀ + q) i), ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ)
          (fun x => (f x - B.π (q₀ + q) i x)
            * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x)|
    with hblink_def
  set jump : ℝ≥0∞ := ∑' q : ℕ, ⨆ i : Fin (B.Nq (q₀ + q + 1)), ENNReal.ofReal
      |empiricalProcess P n (fun k : Fin n => X k.val ξ)
        (truncJump B δ n (Nat.le_add_right q₀ q) i)| with hjump_def
  -- `supNormOver F G = ⨆_{f∈F} ofReal|G f|`; reduce to a per-`f` bound.
  refine iSup₂_le (fun f hf => ?_)
  -- The `q₀`-cell `i₀` of `f`, and `π_{q₀}f = B.π q₀ i₀`.
  obtain ⟨i₀, hi₀⟩ := B.cover (le_refl q₀) f hf
  -- `Φ ∈ L²(P) ⊆ L¹(P)` on a probability space, hence `f`, `π q₀ i₀`, and the
  -- envelope-indicator pieces are all integrable (dominated by `Φ`).
  have hΦ_int : Integrable Φ P := hΦ_L2.integrable one_le_two
  have hf_int : Integrable f P := by
    refine hΦ_int.mono' (hF_meas f hf).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa using (hΦ_env f hf x))
  -- `π_{q₀}f = B.π q₀ i₀ ∈ F`, hence measurable and integrable (dominated by `Φ`).
  have hπ_mem : B.π q₀ i₀ ∈ F := B.cell_subset (le_refl q₀) i₀ (B.π_mem (le_refl q₀) i₀)
  have hπ_meas₀ : Measurable (B.π q₀ i₀) := hπ_meas (le_refl q₀) i₀
  have hπ_int : Integrable (B.π q₀ i₀) P := by
    refine hΦ_int.mono' hπ_meas₀.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by
      simpa using (hΦ_env _ hπ_mem x))
  -- The two complementary envelope-truncation sets (measurable since `Φ` is).
  have hΦabs_meas : Measurable (fun y => |Φ y|) := continuous_abs.measurable.comp hΦ_meas
  have hsLE_meas : MeasurableSet {y | |Φ y| ≤ Real.sqrt n * globalThreshold B δ} :=
    measurableSet_le hΦabs_meas measurable_const
  have hsGT_meas : MeasurableSet {y | Real.sqrt n * globalThreshold B δ < |Φ y|} :=
    measurableSet_lt measurable_const hΦabs_meas
  -- `a := truncRep i₀ = π_{q₀}f·1{≤}`; `b := π_{q₀}f·1{>}`; both integrable (dominated
  -- by `|π_{q₀}f| ≤ Φ`), and `c := f − π_{q₀}f` integrable (`f`, `π` both integrable).
  have ha_int : Integrable (truncRep B Φ δ n q₀ i₀) P := by
    unfold truncRep
    exact (hπ_int.indicator hsLE_meas).congr
      (Filter.Eventually.of_forall (fun x => by
        by_cases hx : |Φ x| ≤ Real.sqrt n * globalThreshold B δ <;>
          simp [Set.indicator, hx]))
  have hb_int : Integrable
      (fun x => B.π q₀ i₀ x
        * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x) P := by
    exact (hπ_int.indicator hsGT_meas).congr
      (Filter.Eventually.of_forall (fun x => by
        by_cases hx : Real.sqrt n * globalThreshold B δ < |Φ x| <;>
          simp [Set.indicator, hx]))
  have hc_int : Integrable (fun x => f x - B.π q₀ i₀ x) P := hf_int.sub hπ_int
  -- Abbreviate the empirical-process evaluator at this fixed `ξ`.
  let G : (Ω → ℝ) → ℝ := fun g =>
    empiricalProcess P n (fun i : Fin n => X i.val ξ) g
  -- The head/envelope pointwise split identity: `f = a + b + c`.
  have hid : (fun x => f x) = (fun x => (truncRep B Φ δ n q₀ i₀ x
        + B.π q₀ i₀ x
          * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x)
        + (f x - B.π q₀ i₀ x)) := by
    funext x
    unfold truncRep
    by_cases hx : |Φ x| ≤ Real.sqrt n * globalThreshold B δ
    · have hx' : ¬ Real.sqrt n * globalThreshold B δ < |Φ x| := not_lt.mpr hx
      simp [Set.indicator, hx, hx']
    · have hx' : Real.sqrt n * globalThreshold B δ < |Φ x| := not_le.mp hx
      simp [Set.indicator, hx, hx']
  have hsplit : G f = G (truncRep B Φ δ n q₀ i₀)
      + G (fun x => B.π q₀ i₀ x
          * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x)
      + G (fun x => f x - B.π q₀ i₀ x) := by
    change empiricalProcess P n (fun i : Fin n => X i.val ξ) f = _
    rw [show (fun x => f x) = f from rfl] at hid
    conv_lhs => rw [hid]
    rw [empiricalProcess_add P n (fun i : Fin n => X i.val ξ)
        (fun x => truncRep B Φ δ n q₀ i₀ x
          + B.π q₀ i₀ x
            * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x)
        (fun x => f x - B.π q₀ i₀ x) (ha_int.add hb_int) hc_int,
      empiricalProcess_add P n (fun i : Fin n => X i.val ξ)
        (truncRep B Φ δ n q₀ i₀)
        (fun x => B.π q₀ i₀ x
          * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x)
        ha_int hb_int]
  -- Triangle inequality in `ℝ≥0∞`, then bound each of the three pieces.
  have htri : ENNReal.ofReal |G f|
      ≤ ENNReal.ofReal |G (truncRep B Φ δ n q₀ i₀)|
        + ENNReal.ofReal |G (fun x => B.π q₀ i₀ x
            * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x)|
        + ENNReal.ofReal |G (fun x => f x - B.π q₀ i₀ x)| := by
    rw [hsplit]
    refine le_trans (ENNReal.ofReal_le_ofReal (abs_add_three _ _ _)) ?_
    refine le_trans ENNReal.ofReal_add_le ?_
    exact add_le_add ENNReal.ofReal_add_le le_rfl
  -- Piece 1 (head): `ofReal|G(truncRep i₀)| ≤ head` by `le_iSup` at `i₀`.
  have hP1 : ENNReal.ofReal |G (truncRep B Φ δ n q₀ i₀)| ≤ head :=
    le_iSup (fun i => ENNReal.ofReal
      |empiricalProcess P n (fun k : Fin n => X k.val ξ) (truncRep B Φ δ n q₀ i)|) i₀
  -- Piece 2 (TRUNC): `π_{q₀}f = B.π q₀ i₀ ∈ F`, so the envelope-tail term is ≤ trunc.
  have hP2 : ENNReal.ofReal |G (fun x => B.π q₀ i₀ x
        * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x)| ≤ trunc :=
    le_supNormOver (z := fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ)
      (fun x => g x
        * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) hπ_mem
  -- Piece 3 (chain): the gated telescope interchange (the lifted hard core).
  -- The telescope's standing parameter `hA_q0` is the pointwise q₀-cell oscillation
  -- bound, supplied here at `f`'s own cell `i₀` from the carried `hΔq0_ptwise`.
  have hP3 : ENNReal.ofReal |G (fun x => f x - B.π q₀ i₀ x)| ≤ blink + jump := by
    rw [hblink_def, hjump_def]
    exact Gn_telescope_link_bound B hπ_meas hF_meas hδ n hn ξ hf i₀ hi₀
      (fun x => hΔq0_ptwise i₀ x)
  -- Assemble: `ofReal|Gf| ≤ head + trunc + (blink + jump) = head + (trunc + blink) + jump`.
  calc ENNReal.ofReal |(fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) f|
      = ENNReal.ofReal |G f| := rfl
    _ ≤ ENNReal.ofReal |G (truncRep B Φ δ n q₀ i₀)|
          + ENNReal.ofReal |G (fun x => B.π q₀ i₀ x
              * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} (1 : Ω → ℝ) x)|
          + ENNReal.ofReal |G (fun x => f x - B.π q₀ i₀ x)| := htri
    _ ≤ head + trunc + (blink + jump) := by
        refine add_le_add (add_le_add hP1 hP2) hP3
    _ = head + (trunc + blink) + jump := by
        rw [add_assoc, add_assoc, ← add_assoc trunc blink jump]

/-- **B-series mean-correction term.** Summing the per-level **maximal** mean corrections of
`supNormOver_link_meanSplit_le` over the B-series levels `q₀ + q`:
`Bmean := ∑'_q 4√n · ⨆_i ∫⁻ Δ_{q₀+q} i · 1{chainB} ∂P` — a **max** (`⨆_i`) over
cells, not a `Σ_i` sum. This is the price of keeping the B-link in its honest
`f`-dependent form (`𝔾ₙ` signed): the centred mean `√n·P((f−π_q f)·B_q − Δ_q·B_q)`
cannot be dropped pointwise, but lands on the integrable cell oscillation `Δ_q·B_q`,
and the **maximal** inequality `⨆_i (a_i + b_i) ≤
⨆_i a_i + ⨆_i b_i` keeps the correction a cell-max rather than a cell-sum (which
over-counted by `N_q`). It is `√n`-free after the threshold cancellation
(`chain_Bmean_dyadic_bound`): on `{chainB}`, `Δ_q > √n·a_q ⟹
√n·P(Δ_q·1{chainB}) ≤ ‖Δ_q‖₂²/a_q`, so `4√n·⨆_i P(Δ_q·1{cB}) ≤ 4·⨆_i‖Δ_q i‖₂²/a_q ≤
4δ(1/2)^q(1+√log(1+N_{q+1}))`, folding into the dyadic series. -/
noncomputable def Bmean (B : NestedBracketPartition F P q₀ C)
    (δ : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ∑' q : ℕ, 4 * ENNReal.ofReal (Real.sqrt n)
    * ⨆ i : Fin (B.Nq (q₀ + q)), ∫⁻ x, ENNReal.ofReal
        (B.Δ (q₀ + q) i x
          * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x) ∂P

/-- **Gated-telescope decomposition at the ∫⁻ mean level (vdV p.287, the chaining
core).**

The integrated supremum `∫⁻ supNormOver F (𝔾ₙ f)` is dominated by the four-piece
RHS — head + truncated-evaluator + (`3·∑levelOscSup` + `Bmean`) + A-series:

* the **head** finite-sup (`levelRepSup` at `q₀`): `∫⁻ ⨆ᵢ ofReal|𝔾ₙ(truncRep i)|`;
* the **threshold-truncated** evaluator integral
  `∫⁻ supNormOver F (𝔾ₙ (f·1{√n·a<|Φ|}))`;
* the **B-link** block: each per-level B-link
  `⨆ᵢ ⨆_{f∈cell} ofReal|𝔾ₙ((f − π_{q₀+q} i)·1{chainB})|` is bounded **pointwise in
  `ξ`** by `supNormOver_link_meanSplit_pointwise_le` — `3·(⨆ᵢ ofReal|𝔾ₙ(truncOsc i)|)`
  (a finite `⨆ᵢ`, MEASURABLE for free via `measurable_iSup_ofReal_abs_empiricalProcess`)
  plus the `ξ`-constant correction `4√n·⨆ᵢ ∫⁻ Δ·1{chainB} ∂P`.  This measurable
  pointwise envelope is what lets us split the `∫⁻` of the B-link series **without**
  any per-cell separability/measurability bridge (the `EmpProcSeparable`/`hF_sep`
  predicate is GONE: the uncountable `⨆_{f∈cell}` is never required measurable, only
  bounded by a measurable finite-`⨆ᵢ`).  Summed, the osc part gives `3·∑'levelOscSup`
  (after the injection `q ↦ q₀+q`) and the correction gives `Bmean` (vdV's signed-`𝔾ₙ`
  correction in maximal form);
* the **A-series** jump sups (`levelJumpSup`): the A-link
  `(π_{q+1}f − π_q f)·A_q f = jump_i · A_q` is a *fixed cell representative* (`f`
  enters only via its cell `i`), so its `⨆_f` collapses to `⨆_i` directly — no
  mean correction, finite-`⨆ᵢ` measurable.

This is the genuine substance of the chaining argument: the **gated telescope**
`f − π_{q₀}f = Σ_{q>q₀} (f − π_q f)·B_q f + Σ_{q≥q₀} (π_{q+1}f − π_q f)·A_q f`
(`chain_supnorm_le_pointwise` at the per-`ξ` break level), the envelope truncation
isolating the truncated-evaluator contribution, the per-`ξ` mean split of the
B-link, and the `∫⁻`-split of the resulting **measurable** four-piece envelope.

**No `EmpProcSeparable` (book-faithful, vdV Lemma 19.34).** vdV never forms a
measurable per-cell supremum — it bounds the per-link MEAN by the explicit
cell-diameter `Δ_q` (finite-indexed) inside `E*`.  The pointwise mean split realizes
exactly this: the only measurability used is the finite-`⨆ᵢ` of the explicit
`truncOsc i` (= `Δ_q i·1{chainB}`), measurable for free.  The non-measurable `trunc`
term is always peeled by the *other* (measurable) summand.

vdV §19.6 p.287, the displayed gated decomposition + truncation + mean split. -/
private theorem chain_supnorm_le_decomposition
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (hΦ_env : IsEnvelope F Φ) (hΦ_L2 : MemLp Φ 2 P)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n)
    (hΔq0_ptwise : ∀ (i : Fin (B.Nq q₀)) (x : Ω),
      B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δ q₀) :
    ∫⁻ ξ, supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ levelRepSup B μ X Φ δ n q₀
        + ((∫⁻ ξ, supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
            + 3 * (∑' q : ℕ, levelOscSup B μ X δ n q))
        + (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q))
        + Bmean B δ n := by
  classical
  -- ===== Per-`ξ` integrand abbreviations =====
  -- head: finite-`⨆ᵢ` of `truncRep`; jump_q: finite-`⨆ᵢ` of `truncJump`;
  -- TRUNC: uncountable `supNormOver F` of the envelope-truncated evaluator;
  -- blink_q: `⨆ᵢ ⨆_{f∈cell}` of the honest B-link (NEVER required measurable);
  -- oscDom_q: the MEASURABLE per-`ξ` envelope of blink_q from the mean split.
  set head : Ξ → ℝ≥0∞ := fun ξ => ⨆ i : Fin (B.Nq q₀), ENNReal.ofReal
      |empiricalProcess P n (fun k : Fin n => X k.val ξ) (truncRep B Φ δ n q₀ i)|
    with hhead_def
  set trunc : Ξ → ℝ≥0∞ := fun ξ => supNormOver F
      (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (fun x => f x
          * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x))
    with htrunc_def
  set blink : ℕ → Ξ → ℝ≥0∞ := fun q ξ => ⨆ i : Fin (B.Nq (q₀ + q)),
      ⨆ (f : Ω → ℝ) (_ : f ∈ B.cell (q₀ + q) i), ENNReal.ofReal
        |empiricalProcess P n (fun j : Fin n => X j.val ξ)
          (fun x => (f x - B.π (q₀ + q) i x)
            * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x)|
    with hblink_def
  set jump : ℕ → Ξ → ℝ≥0∞ := fun q ξ => ⨆ i : Fin (B.Nq (q₀ + q + 1)),
      ENNReal.ofReal |empiricalProcess P n (fun k : Fin n => X k.val ξ)
        (truncJump B δ n (Nat.le_add_right q₀ q) i)|
    with hjump_def
  -- The `ξ`-constant per-level B-mean correction (the `P`-side of the mean split).
  set bmeanConst : ℕ → ℝ≥0∞ := fun q =>
      4 * ENNReal.ofReal (Real.sqrt n)
        * ⨆ i : Fin (B.Nq (q₀ + q)), ∫⁻ x, ENNReal.ofReal
            (B.Δ (q₀ + q) i x
              * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x) ∂P
    with hbmeanConst_def
  -- The measurable per-`ξ` envelope of `blink q` (mean split RHS).
  set oscDom : ℕ → Ξ → ℝ≥0∞ := fun q ξ =>
      3 * (⨆ i : Fin (B.Nq (q₀ + q)), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncOsc B δ n (q₀ + q) i)|)
        + bmeanConst q
    with hoscDom_def
  -- ===== Measurability of the split pieces (all FINITE `⨆ᵢ`; no separability) =====
  have hhead_meas : Measurable head := by
    refine measurable_iSup_ofReal_abs_empiricalProcess hX_meas n _ (fun i => ?_)
    refine (hπ_meas (le_refl q₀) i).mul ?_
    exact measurable_one.indicator
      (measurableSet_le hΦ_meas.norm measurable_const)
  have hjump_meas : ∀ q, Measurable (jump q) := by
    intro q
    refine measurable_iSup_ofReal_abs_empiricalProcess hX_meas n _ (fun i => ?_)
    refine (B.jump_measurable hπ_meas (Nat.le_add_right q₀ q) i).mul ?_
    exact measurable_one.indicator
      (chainA_measurableSet B δ n (q₀ + q) (B.parent (Nat.le_add_right q₀ q) i))
  -- `oscDom q`: `3·(finite-⨆ᵢ of measurable truncOsc)` + a `ξ`-constant — measurable.
  have hoscDom_meas : ∀ q, Measurable (oscDom q) := by
    intro q
    refine Measurable.add ?_ measurable_const
    refine Measurable.const_mul ?_ 3
    refine measurable_iSup_ofReal_abs_empiricalProcess hX_meas n _ (fun i => ?_)
    exact (B.Δ_meas (Nat.le_add_right q₀ q) i).mul
      (measurable_const.indicator
        (chainB_measurableSet B n (Nat.le_add_right q₀ q) i))
  -- ===== Pointwise B-link envelope: `blink q ξ ≤ oscDom q ξ` =====
  have hblink_dom : ∀ q (ξ : Ξ), blink q ξ ≤ oscDom q ξ := by
    intro q ξ
    simpa only [hblink_def, hoscDom_def, hbmeanConst_def] using
      supNormOver_link_meanSplit_pointwise_le B hπ_meas hF_meas (X := X) n
        (Nat.le_add_right q₀ q) ξ
  -- ===== Step 1: pointwise gated-telescope bound + the `oscDom` envelope =====
  have hmono : ∫⁻ ξ, supNormOver F
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ ∫⁻ ξ, (head ξ + (trunc ξ + ∑' q, oscDom q ξ) + ∑' q, jump q ξ) ∂μ := by
    refine lintegral_mono (fun ξ => ?_)
    have hpt := chain_supnorm_le_pointwise B hπ_meas hF_meas (X := X) Φ hΦ_meas hΦ_env hΦ_L2
      hδ n hn ξ hΔq0_ptwise
    -- Unfold `head`/`trunc`/`jump` in the GOAL (matching `hpt`'s explicit forms);
    -- `oscDom q ξ` stays folded and dominates `blink q ξ` (`hblink_dom`).
    simp only [hhead_def, htrunc_def, hjump_def]
    refine hpt.trans ?_
    -- Replace `∑' blink` by `∑' oscDom` (pointwise monotone, `oscDom ≥ blink`).
    gcongr with q
    exact hblink_dom q ξ
  refine hmono.trans ?_
  -- ===== Step 2: split `∫⁻ (Σ measurable pieces) = Σ ∫⁻ pieces` =====
  have hoscDom_sum_meas : Measurable (fun ξ => ∑' q, oscDom q ξ) :=
    Measurable.ennreal_tsum hoscDom_meas
  have hjump_sum_meas : Measurable (fun ξ => ∑' q, jump q ξ) :=
    Measurable.ennreal_tsum hjump_meas
  rw [lintegral_add_right' _ hjump_sum_meas.aemeasurable,
    lintegral_add_left' hhead_meas.aemeasurable,
    lintegral_add_right' _ hoscDom_sum_meas.aemeasurable,
    lintegral_tsum (fun q => (hoscDom_meas q).aemeasurable),
    lintegral_tsum (fun q => (hjump_meas q).aemeasurable)]
  -- ===== Step 3: identify the integrals + fold the osc/correction series =====
  -- `∫⁻ head = levelRepSup`, `∫⁻ jump_q = levelJumpSup q`; `∫⁻ oscDom q =
  -- 3·levelOscSup (q₀+q) + bmeanConst q`.
  have hoscDom_int : ∀ q, ∫⁻ ξ, oscDom q ξ ∂μ
      = 3 * levelOscSup B μ X δ n (q₀ + q) + bmeanConst q := by
    intro q
    rw [hoscDom_def]
    rw [lintegral_add_right' _ measurable_const.aemeasurable]
    rw [lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
    rw [lintegral_const, measure_univ, mul_one]
    rfl
  -- Fold `∫⁻ head`, `∫⁻ jump_q`, and the `oscDom` series.
  simp only [hhead_def, htrunc_def, hjump_def, levelRepSup, levelJumpSup]
  rw [show (∑' q, ∫⁻ ξ, oscDom q ξ ∂μ)
        = 3 * (∑' q : ℕ, levelOscSup B μ X δ n (q₀ + q)) + Bmean B δ n by
    simp only [hoscDom_int]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hbmeanConst_def, Bmean]]
  -- Dominate `3·∑'levelOscSup (q₀+q) ≤ 3·∑'levelOscSup q` (injection `q ↦ q₀+q`).
  have hosc_inj : 3 * (∑' q : ℕ, levelOscSup B μ X δ n (q₀ + q))
      ≤ 3 * (∑' q : ℕ, levelOscSup B μ X δ n q) :=
    mul_le_mul_of_nonneg_left
      (ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective q₀)
        (levelOscSup B μ X δ n)) (zero_le)
  -- Assemble.
  calc levelRepSup B μ X Φ δ n q₀
        + ((∫⁻ ξ, supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
            + (3 * (∑' q : ℕ, levelOscSup B μ X δ n (q₀ + q)) + Bmean B δ n))
        + (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q))
      ≤ levelRepSup B μ X Φ δ n q₀
        + ((∫⁻ ξ, supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
            + (3 * (∑' q : ℕ, levelOscSup B μ X δ n q) + Bmean B δ n))
        + (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q)) := by
        gcongr
    _ = levelRepSup B μ X Φ δ n q₀
        + ((∫⁻ ξ, supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
            + 3 * (∑' q : ℕ, levelOscSup B μ X δ n q))
        + (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q))
        + Bmean B δ n := by ring

/-- **Telescope-to-three-part split (vdV p.287).**

Integrating `chain_pointwise_decomposition` over `ξ` and splitting the integral
reassembles the three-part RHS plus the B-series mean correction `Bmean`:

* the **head** finite-sup (`levelRepSup` at `q₀`);
* the **threshold-truncated** evaluator supremum;
* the **B-link** sups: each per-level B-link `∫⁻ ⨆ᵢ ⨆_{f∈cell} ofReal|𝔾ₙ((f−π)·B)|`
  is split at the **mean level** by `supNormOver_link_meanSplit_le` into
  the cell-oscillation sup `levelOscSup` plus the per-level √n-mean correction; the
  corrections sum to `Bmean`;
* the **A-series** jump sups (`levelJumpSup`): the A-link collapses `⨆_f → ⨆_i`
  directly (`f` enters only via its cell `i` because the jump is a fixed cell
  representative), no mean correction.

Because `𝔾ₙ` is signed, the B-link correction must be handled at the
`∫⁻` level by this mean split. The assumption `hF_meas` supplies the required
class measurability. See vdV §19.6 p.287. -/
theorem chain_supnorm_le_three_part
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (_hX_law : μ.map (X 0) = P)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (hΦ_env : IsEnvelope F Φ)
    (hΦ_L2 : MemLp Φ 2 P)
    {δ : ℝ} (hδ : 0 < δ) (n : ℕ) (hn : 1 ≤ n)
    (hΔq0_ptwise : ∀ (i : Fin (B.Nq q₀)) (x : Ω),
      B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δ q₀) :
    ∫⁻ ξ, supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ levelRepSup B μ X Φ δ n q₀
        + ((∫⁻ ξ, supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
            + 3 * (∑' q : ℕ, levelOscSup B μ X δ n q))
        + (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q))
        + Bmean B δ n :=
  -- The integrated gated telescope gives the three terms directly; the
  -- pointwise B-link mean split contributes `Bmean` without a separability
  -- assumption.
  chain_supnorm_le_decomposition B hπ_meas hF_meas hX_meas Φ hΦ_meas
    hΦ_env hΦ_L2 hδ n hn hΔq0_ptwise

/-- **B-series mean-correction dyadic bound (the √n-cancellation).**

`Bmean = ∑'_q 4√n·⨆_i ∫⁻ Δ_{q₀+q} i·1{chainB} ∂P` is the per-level **maximal** √n-mean
correction emitted by `supNormOver_link_meanSplit_le` (the `⨆_i`, not `Σ_i`,
form that avoids the `N_q` over-count). The cancellation (per level `Q = q₀+q`): on
`{chainB Q i}` the threshold is crossed, `√n·a_Q < Δ_Q i`, so
`Δ_Q i·1{chainB} ≤ Δ_Q i²/(√n·a_Q)` and `∫⁻ Δ_Q i·1{chainB} ≤ ‖Δ_Q i‖₂²/(√n·a_Q)`;
multiplying by `4√n` cancels the `√n`, landing per cell on
`4·‖Δ_Q i‖₂²/a_Q ≤ 4·δ·(1/2)^q·(1+√log(1+N_{Q+1}))` (`a_Q = (1/2)^q·δ/(1+√log(1+N_{Q+1}))`,
`‖Δ_Q i‖₂ ≤ δ·(1/2)^q` via `Δ_L2_le` at `C = δ`).  Because the bound is **uniform in
`i`**, the cell-max `⨆_i` is bounded by the single per-cell value — `√n`-free, no
`N_q` factor.

The `1 +` regularizer of `a_Q` splits as `1 + √log(1+N_{Q+1})`: the `√log` term
collapses over `Icc q₀ (Q+1)` into the entropy series exactly as the A-series
(`card_le` + `Real.sqrt_log_prod_le_sum_one_add` + `coverCard_le` + `entropyWeight_mono`),
and the bare `1` is absorbed by `1 ≤ (1/√log 2)·entropyIntegrand(δ)`
(`sqrt_log_two_le_entropyIntegrand`, using `F.Nonempty ⟹ N_{[]} ≥ 1`).  The resulting
per-level form `ofReal(K₀·δ·(1/2)^q)·∑_{p∈Icc q₀ (Q+1)} entropyIntegrand` folds via
`tsum_pow_half_sum_Icc_succ_le` (factor `4`) and the `p ↦ p−q₀` reindex, mirroring
`chain_B_levelOscSup_dyadic_bound` / `chain_A_dyadic_bound`. Universal constant.

vdV §19.6 p.287-288, the B-link mean-correction (the `√n·a_q` threshold cancels). -/
private theorem chain_Bmean_dyadic_bound
    [IsProbabilityMeasure P] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F : Set (Ω → ℝ)) (q₀ : ℕ) (C : ℝ) (B : NestedBracketPartition F P q₀ C)
        (_hF_ne : F.Nonempty),
      ∀ {δ : ℝ}, 0 < δ → C = δ → ∀ (n : ℕ), 1 ≤ n →
        Bmean B δ n
          ≤ ENNReal.ofReal c
              * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                  * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
  classical
  -- `√log 2 > 0` (since `2 > 1`); the per-level constant is `K₀ = 4·(1 + 1/√log 2)`,
  -- the overall universal constant `4·K₀` (the dyadic-rearrangement factor `4`).
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrtlog2_pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr hlog2_pos
  set K₀ : ℝ := 4 * (1 + 1 / Real.sqrt (Real.log 2)) with hK₀_def
  have hK₀_pos : 0 < K₀ := by rw [hK₀_def]; positivity
  clear_value K₀
  refine ⟨4 * K₀, by positivity, ?_⟩
  intro F q₀ C B hF_ne δ hδ hCδ n hn
  -- Numerical preliminaries.
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : (0 : ℝ) ≤ Real.sqrt n := hsn_pos.le
  -- The dyadic entropy coefficient `a k = entropyIntegrand((1/2)^k·δ)`.
  set a : ℕ → ℝ≥0∞ := fun k => entropyIntegrand ((1/2 : ℝ)^k * δ) F P with ha_def
  -- `ofReal((1/2)^q·δ) = (2⁻¹)^q · ofReal δ` (recurring conversion).
  have hofReal_half : ENNReal.ofReal (1/2 : ℝ) = (2⁻¹ : ℝ≥0∞) := by
    rw [show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  have hpow_eq : ∀ q : ℕ,
      ENNReal.ofReal ((1/2 : ℝ)^q * δ) = (2⁻¹ : ℝ≥0∞)^q * ENNReal.ofReal δ := by
    intro q
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), hofReal_half]
  -- =====================================================================
  -- STEP 1 — Per-level bound:
  --   `Bmean_q ≤ ofReal(K₀·(1/2)^q·δ) · (∑_{p ∈ Icc q₀ (Q+1)} entropyIntegrand)`,
  -- where the inner sum (re-indexed) becomes `∑_{k ∈ Icc 0 (q+1)} a k`.
  -- =====================================================================
  have hlevel : ∀ q : ℕ,
      4 * ENNReal.ofReal (Real.sqrt n)
          * ⨆ i : Fin (B.Nq (q₀ + q)), ∫⁻ x, ENNReal.ofReal
              (B.Δ (q₀ + q) i x
                * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x) ∂P
        ≤ ENNReal.ofReal K₀
            * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) := by
    intro q
    set Q : ℕ := q₀ + q with hQ_def
    have hQ : q₀ ≤ Q := Nat.le_add_right q₀ q
    have hQq : Q - q₀ = q := by omega
    -- The per-cell L² bound `‖Δ_Q i‖₂² ≤ (δ·(1/2)^q)²`.
    have hΔsq_le : ∀ i : Fin (B.Nq Q),
        ∫ x, (B.Δ Q i x) ^ 2 ∂P ≤ (δ * (1/2 : ℝ)^q) ^ 2 := by
      intro i
      have hΔ_memLp : MemLp (B.Δ Q i) 2 P := B.Δ_memLp hQ i
      have hnn : 0 ≤ ∫ x, (B.Δ Q i x) ^ 2 ∂P :=
        MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
      have hCpow_nn : 0 ≤ C * (1/2 : ℝ) ^ (Q - q₀) := by rw [hCδ]; positivity
      have hsqrt_eq : Real.sqrt (∫ x, (B.Δ Q i x) ^ 2 ∂P)
          = (eLpNorm (B.Δ Q i) 2 P).toReal := by
        rw [hΔ_memLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
        have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
        have h_int_eq :
            (fun x => ‖B.Δ Q i x‖ ^ (2 : ℝ≥0∞).toReal)
              = (fun x => B.Δ Q i x ^ 2) := by
          funext x; rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
        rw [h_int_eq, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), h2, Real.sqrt_eq_rpow]
        norm_num
      have hsqrt_le : Real.sqrt (∫ x, (B.Δ Q i x) ^ 2 ∂P) ≤ δ * (1/2 : ℝ)^q := by
        rw [hsqrt_eq]
        calc (eLpNorm (B.Δ Q i) 2 P).toReal
            ≤ (ENNReal.ofReal (C * (1/2 : ℝ) ^ (Q - q₀))).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (B.Δ_L2_le hQ i)
          _ = C * (1/2 : ℝ) ^ (Q - q₀) := ENNReal.toReal_ofReal hCpow_nn
          _ = δ * (1/2 : ℝ)^q := by rw [hCδ, hQq]
      nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ x, (B.Δ Q i x) ^ 2 ∂P), hsqrt_le,
        mul_nonneg hδ.le (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) q)]
    -- `a_Q = chainThreshold B δ Q > 0`, with denominator `D = 1 + √log(1+N_{Q+1})`.
    set D : ℝ := 1 + Real.sqrt (Real.log (1 + (B.Nq (Q + 1) : ℝ))) with hD_def
    have hD_pos : 0 < D := by rw [hD_def]; positivity
    have haQ_eq : chainThreshold B δ Q = (1/2 : ℝ)^q * δ / D := by
      rw [chainThreshold, hQq, hD_def]
    have haQ_pos : 0 < chainThreshold B δ Q := by
      rw [haQ_eq]; positivity
    -- Per-cell: `∫⁻ Δ_Q i·1{chainB} ≤ ‖Δ_Q i‖₂²/(√n·a_Q)`, so
    -- `4√n·(that) ≤ 4·(δ(1/2)^q)²·D/((1/2)^q·δ) = ofReal(4δ(1/2)^q·D)`.
    have hcell : ∀ i : Fin (B.Nq Q),
        4 * ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ x, ENNReal.ofReal
                (B.Δ Q i x
                  * Set.indicator {y | chainB B δ n Q i y} (1 : Ω → ℝ) x) ∂P
          ≤ ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * D) := by
      intro i
      -- The pointwise integrand bound `Δ_Q i·1{cB} ≤ Δ_Q i²/(√n·a_Q)` (`x`-wise, in ℝ≥0∞).
      have hpt : ∀ x : Ω,
          ENNReal.ofReal (B.Δ Q i x * Set.indicator {y | chainB B δ n Q i y} (1 : Ω → ℝ) x)
            ≤ ENNReal.ofReal (1 / (Real.sqrt n * chainThreshold B δ Q))
                * ENNReal.ofReal ((B.Δ Q i x) ^ 2) := by
        intro x
        by_cases hx : x ∈ {y | chainB B δ n Q i y}
        · rw [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
          -- On `{chainB}`: `√n·a_Q < Δ_Q i x`, and `Δ_Q i x ≥ 0`.
          obtain ⟨_, _, hcross⟩ := hx
          have hΔnn : 0 ≤ B.Δ Q i x := by
            have := B.diam hQ i (B.π Q i) (B.π_mem hQ i) (B.π Q i) (B.π_mem hQ i) x
            simpa using this
          have hthr_pos : 0 < Real.sqrt n * chainThreshold B δ Q := by positivity
          have hΔ_le : B.Δ Q i x
              ≤ 1 / (Real.sqrt n * chainThreshold B δ Q) * (B.Δ Q i x) ^ 2 := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hthr_pos]
            nlinarith [hcross.le, hΔnn, sq_nonneg (B.Δ Q i x)]
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal hΔ_le
        · rw [Set.indicator_of_notMem hx, mul_zero, ENNReal.ofReal_zero]
          exact zero_le
      -- Integrate the pointwise bound; `∫⁻ ofReal(Δ²) = ofReal(∫Δ²)`.
      have hΔ_memLp : MemLp (B.Δ Q i) 2 P := B.Δ_memLp hQ i
      have hΔsq_int : Integrable (fun x => (B.Δ Q i x) ^ 2) P := hΔ_memLp.integrable_sq
      have hlint_sq : ∫⁻ x, ENNReal.ofReal ((B.Δ Q i x) ^ 2) ∂P
          = ENNReal.ofReal (∫ x, (B.Δ Q i x) ^ 2 ∂P) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΔsq_int
          (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
      calc 4 * ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ x, ENNReal.ofReal
                  (B.Δ Q i x
                    * Set.indicator {y | chainB B δ n Q i y} (1 : Ω → ℝ) x) ∂P
          ≤ 4 * ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ x, ENNReal.ofReal (1 / (Real.sqrt n * chainThreshold B δ Q))
                  * ENNReal.ofReal ((B.Δ Q i x) ^ 2) ∂P :=
            mul_le_mul_of_nonneg_left (lintegral_mono hpt) (zero_le)
        _ = 4 * ENNReal.ofReal (Real.sqrt n)
              * (ENNReal.ofReal (1 / (Real.sqrt n * chainThreshold B δ Q))
                  * ENNReal.ofReal (∫ x, (B.Δ Q i x) ^ 2 ∂P)) := by
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlint_sq]
        _ ≤ ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * D) := by
            rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
              ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
              ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            apply ENNReal.ofReal_le_ofReal
            -- `4·√n·(1/(√n·a_Q)·∫Δ²) = 4·(∫Δ²)/a_Q`, then `∫Δ²≤(δ(1/2)^q)²` and
            -- `1/a_Q = D/((1/2)^q·δ)`.
            have hint_nn : 0 ≤ ∫ x, (B.Δ Q i x) ^ 2 ∂P :=
              MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
            have hcancel : 4 * Real.sqrt n
                * (1 / (Real.sqrt n * chainThreshold B δ Q) * (∫ x, (B.Δ Q i x) ^ 2 ∂P))
                = 4 * (∫ x, (B.Δ Q i x) ^ 2 ∂P) / chainThreshold B δ Q := by
              field_simp
            rw [hcancel, div_le_iff₀ haQ_pos]
            calc 4 * (∫ x, (B.Δ Q i x) ^ 2 ∂P)
                ≤ 4 * (δ * (1/2 : ℝ)^q) ^ 2 :=
                  mul_le_mul_of_nonneg_left (hΔsq_le i) (by norm_num)
              _ = 4 * (δ * (1/2 : ℝ)^q) * D * chainThreshold B δ Q := by
                  rw [haQ_eq]; field_simp
    -- The cell-max is bounded by the (uniform) per-cell value.
    have hsup_le :
        4 * ENNReal.ofReal (Real.sqrt n)
            * ⨆ i : Fin (B.Nq Q), ∫⁻ x, ENNReal.ofReal
                (B.Δ Q i x
                  * Set.indicator {y | chainB B δ n Q i y} (1 : Ω → ℝ) x) ∂P
          ≤ ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * D) := by
      rw [ENNReal.mul_iSup]
      exact iSup_le (fun i => hcell i)
    refine hsup_le.trans ?_
    -- `ofReal(4δ(1/2)^q·D) ≤ ofReal(K₀(1/2)^q δ)·∑_{k∈Icc 0 (q+1)} a k`.
    -- `D = 1 + √log(1+N_{Q+1}) ≤ (1 + 1/√log2)·∑_{p∈Icc q₀ (Q+1)} entropyIntegrand`.
    -- `√log(1+N_{Q+1}) ≤ ∑_{p∈Icc q₀ (Q+1)} √log(1+coverCard p)`.
    have hIcc_ne : (Finset.Icc q₀ (Q + 1)).Nonempty :=
      ⟨q₀, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
    have hcard_prod :
        (B.Nq (Q + 1) : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (Q + 1), (B.coverCard p : ℝ) := by
      have h := B.card_le (q := Q + 1) (le_trans hQ (Nat.le_succ Q))
      calc (B.Nq (Q + 1) : ℝ)
          ≤ ((∏ p ∈ Finset.Icc q₀ (Q + 1), B.coverCard p : ℕ) : ℝ) := by exact_mod_cast h
        _ = ∏ p ∈ Finset.Icc q₀ (Q + 1), (B.coverCard p : ℝ) := by push_cast; rfl
    have hsalvage :
        Real.sqrt (Real.log (1 + (B.Nq (Q + 1) : ℝ)))
          ≤ ∑ p ∈ Finset.Icc q₀ (Q + 1), Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))) := by
      refine le_trans (Real.sqrt_le_sqrt (Real.log_le_log (by positivity) ?_))
        (AsymptoticStatistics.ForMathlib.Real.sqrt_log_prod_le_sum_one_add hIcc_ne
          (fun p => B.coverCard p))
      have : (0 : ℝ) ≤ ∏ p ∈ Finset.Icc q₀ (Q + 1), (B.coverCard p : ℝ) :=
        Finset.prod_nonneg (fun p _ => Nat.cast_nonneg _)
      linarith [hcard_prod]
    -- `∑_{p∈Icc q₀ (Q+1)} ofReal(√log(1+coverCard p)) ≤ ∑_{p} entropyIntegrand((1/2)^{p-q₀}δ)`
    -- `= ∑_{k∈Icc 0 (q+1)} a k` (reindex `p ↦ p − q₀`).
    have hcover_sum :
        (∑ p ∈ Finset.Icc q₀ (Q + 1),
            ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))))
          ≤ ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
      have hterm : ∀ p ∈ Finset.Icc q₀ (Q + 1),
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
            ≤ entropyIntegrand ((1/2 : ℝ)^(p - q₀) * δ) F P := by
        intro p hp
        obtain ⟨hpq0, _⟩ := Finset.mem_Icc.mp hp
        have hco := B.coverCard_le hpq0
        have hscale : (1/2 : ℝ) ^ (p - q₀) * C = (1/2 : ℝ) ^ (p - q₀) * δ := by rw [hCδ]
        rw [hscale] at hco
        calc ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ))))
            = entropyWeight (B.coverCard p : ℕ∞) := (entropyWeight_coe _).symm
          _ ≤ entropyWeight (bracketingNumber ((1/2 : ℝ)^(p - q₀) * δ) F 2 P) :=
              entropyWeight_mono hco
          _ = entropyIntegrand ((1/2 : ℝ)^(p - q₀) * δ) F P := rfl
      calc (∑ p ∈ Finset.Icc q₀ (Q + 1),
              ENNReal.ofReal (Real.sqrt (Real.log (1 + (B.coverCard p : ℝ)))))
          ≤ ∑ p ∈ Finset.Icc q₀ (Q + 1), entropyIntegrand ((1/2 : ℝ)^(p - q₀) * δ) F P :=
            Finset.sum_le_sum hterm
        _ = ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
            refine Finset.sum_nbij' (fun p => p - q₀) (fun k => k + q₀) ?_ ?_ ?_ ?_ ?_
            · intro p hp; simp only [hQ_def, Finset.mem_Icc] at hp ⊢; omega
            · intro k hk; simp only [hQ_def, Finset.mem_Icc] at hk ⊢; omega
            · intro p hp; simp only [hQ_def, Finset.mem_Icc] at hp ⊢; omega
            · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
            · intro p _; rw [ha_def]
    -- `entropyIntegrand(δ) ≥ ofReal(√log2)` is in the sum (`k = 0` term).
    have hone_le_sum :
        ENNReal.ofReal (Real.sqrt (Real.log 2)) ≤ ∑ k ∈ Finset.Icc 0 (q + 1), a k := by
      have h0mem : (0 : ℕ) ∈ Finset.Icc 0 (q + 1) := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      refine le_trans ?_ (Finset.single_le_sum (f := a) (fun k _ => zero_le) h0mem)
      rw [ha_def]; simp only [pow_zero, one_mul]
      exact sqrt_log_two_le_entropyIntegrand hF_ne δ
    -- `ofReal D = ofReal 1 + ofReal(√log(1+N_{Q+1})) ≤ (1 + 1/√log2)·∑ a k`.
    have hsqrtlog2_ne : ENNReal.ofReal (Real.sqrt (Real.log 2)) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hsqrtlog2_pos
    set Sum : ℝ≥0∞ := ∑ k ∈ Finset.Icc 0 (q + 1), a k with hSum_def
    have hD_le : ENNReal.ofReal D
        ≤ ENNReal.ofReal (1 + 1 / Real.sqrt (Real.log 2)) * Sum := by
      -- `ofReal(1+1/√log2)·Sum = (ofReal√log2)⁻¹·Sum + Sum`.
      have hRHS : ENNReal.ofReal (1 + 1 / Real.sqrt (Real.log 2)) * Sum
          = (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹ * Sum + Sum := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
          ENNReal.ofReal_div_of_pos hsqrtlog2_pos, ENNReal.ofReal_one, one_div, add_mul,
          one_mul, add_comm]
      rw [hRHS, hD_def,
        ENNReal.ofReal_add (by norm_num) (Real.sqrt_nonneg _), ENNReal.ofReal_one]
      refine add_le_add ?_ ?_
      · -- `1 ≤ (ofReal√log2)⁻¹·Sum` since `ofReal√log2 ≤ Sum`.
        calc (1 : ℝ≥0∞)
            = (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹
                * ENNReal.ofReal (Real.sqrt (Real.log 2)) :=
              (ENNReal.inv_mul_cancel hsqrtlog2_ne ENNReal.ofReal_ne_top).symm
          _ ≤ (ENNReal.ofReal (Real.sqrt (Real.log 2)))⁻¹ * Sum :=
              mul_le_mul_of_nonneg_left hone_le_sum (zero_le)
      · -- `ofReal(√log(1+N_{Q+1})) ≤ ∑_{p} ofReal(√log(1+coverCard p)) ≤ Sum`.
        refine le_trans ?_ hcover_sum
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Real.sqrt_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hsalvage
    -- Assemble: `ofReal(4δ(1/2)^q·D) ≤ ofReal(K₀(1/2)^q δ)·∑ a k`.
    calc ENNReal.ofReal (4 * (δ * (1/2 : ℝ)^q) * D)
        = ENNReal.ofReal (4 * ((1/2 : ℝ)^q * δ)) * ENNReal.ofReal D := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
      _ ≤ ENNReal.ofReal (4 * ((1/2 : ℝ)^q * δ))
            * (ENNReal.ofReal (1 + 1 / Real.sqrt (Real.log 2)) * Sum) :=
          mul_le_mul_of_nonneg_left hD_le (zero_le)
      _ = ENNReal.ofReal K₀
            * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * Sum) := by
          rw [hK₀_def,
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
            ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
          ring
  -- =====================================================================
  -- STEP 2 — Sum the per-level bounds and apply the dyadic rearrangement.
  -- =====================================================================
  rw [Bmean]
  calc (∑' q : ℕ, 4 * ENNReal.ofReal (Real.sqrt n)
          * ⨆ i : Fin (B.Nq (q₀ + q)), ∫⁻ x, ENNReal.ofReal
              (B.Δ (q₀ + q) i x
                * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x) ∂P)
      ≤ ∑' q : ℕ, ENNReal.ofReal K₀
          * (ENNReal.ofReal ((1/2 : ℝ)^q * δ) * (∑ k ∈ Finset.Icc 0 (q + 1), a k)) :=
        ENNReal.tsum_le_tsum hlevel
    _ = ENNReal.ofReal K₀
          * ∑' q : ℕ, (2⁻¹ : ℝ≥0∞)^q * (∑ k ∈ Finset.Icc 0 (q + 1),
              ENNReal.ofReal δ * a k) := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun q => ?_
        rw [hpow_eq q, ← Finset.mul_sum]
        ring
    _ ≤ ENNReal.ofReal K₀ * (4 * ∑' p : ℕ, (2⁻¹ : ℝ≥0∞)^p * (ENNReal.ofReal δ * a p)) := by
        gcongr
        exact tsum_pow_half_sum_Icc_succ_le (fun k => ENNReal.ofReal δ * a k)
    _ = ENNReal.ofReal K₀
          * (4 * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyIntegrand ((1/2 : ℝ)^q * δ) F P)) := by
        congr 1
        congr 1
        refine tsum_congr fun p => ?_
        rw [hpow_eq p, ha_def]
        ring
    _ = ENNReal.ofReal (4 * K₀)
          * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyIntegrand ((1/2 : ℝ)^q * δ) F P) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4),
          show (ENNReal.ofReal 4 : ℝ≥0∞) = 4 by simp]
        ring

/-- **Partition-uniform form of `chain_supnorm_dyadic_bound`.** The same dyadic
chaining bound, but with the universal constant `c` hoisted *before* the partition
`B`: `∃ c, 0 < c ∧ ∀ B …`. This is exactly what the localized chaining bound needs,
since it builds a *fresh* partition `B(δq, n)` per scale/sample-size and must share a
single constant across all of them.

Soundness of the hoist: the four sub-bound constants
(`chain_head_dyadic_bound` `= 2K`, `chain_B_dyadic_bound` `= max 4 (4K)`,
`chain_A_dyadic_bound` `= 4K`, `chain_Bmean_dyadic_bound` `= 4K₀`) are all derived
from the **partition-free** `tight_chain_level_bound_uniform P hX_*` constant `K`
(and the pure numeral `K₀`); none reads `B`.  Obtaining `K` once before `∀ B` and
re-running the four sub-bounds per `B` therefore reproduces the *same* `c` for every
partition (definitionally through the shared `Classical.choose`). -/
theorem chain_supnorm_dyadic_bound_uniform
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ (F : Set (Ω → ℝ)) (q₀ : ℕ) (C : ℝ) (B : NestedBracketPartition F P q₀ C)
        (_hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
        (_hF_ne : F.Nonempty)
        (_hF_meas : ∀ f ∈ F, Measurable f),
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δ : ℝ}, 0 < δ → C = δ →
          (∀ f ∈ F, eLpNorm f 2 P ≤ ENNReal.ofReal δ) →
          (4 * δ ≤ (1 / 2 : ℝ) ^ q₀ ∧ (1 / 2 : ℝ) ^ q₀ ≤ 8 * δ) →
          ∀ (n : ℕ), 1 ≤ n →
            (∀ (i : Fin (B.Nq q₀)) (x : Ω),
                B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δ q₀) →
            ∫⁻ ξ, supNormOver F
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
              ≤ ENNReal.ofReal c
                  * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                      * entropyIntegrand ((1/2 : ℝ)^q * δ) F P)
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|}
                            1 ω ∂P) := by
  classical
  -- The four constants are uniform over the class, base level, and scale;
  -- their sum is therefore uniform in `(F, q₀, C, B)`.
  obtain ⟨cH, hcH_pos, hH⟩ :=
    chain_head_dyadic_bound hX_meas hX_iindep hX_idem hX_law
  obtain ⟨cB, hcB_pos, hBb⟩ :=
    chain_B_dyadic_bound hX_meas hX_iindep hX_idem hX_law
  obtain ⟨cA, hcA_pos, hAb⟩ :=
    chain_A_dyadic_bound hX_meas hX_iindep hX_idem hX_law
  obtain ⟨cM, hcM_pos, hMb⟩ :=
    chain_Bmean_dyadic_bound (P := P)
  -- Universal constant: the sum of the four (independent of F, q₀, C, Φ, δ, n); the
  -- B-link contribution carries a factor `3` because the maximal-form mean split
  -- emits `3·levelOscSup` (the random empirical-average half re-centres onto the
  -- cell-oscillation process, costing two extra copies of `levelOscSup`).
  refine ⟨cH + 3 * cB + cA + cM, by nlinarith [hcH_pos, hcA_pos, hcM_pos, hcB_pos], ?_⟩
  intro F q₀ C B hπ_meas hF_ne hF_meas
  have hH := hH F q₀ C B hπ_meas hF_ne
  have hBb := hBb F q₀ C B hπ_meas hF_ne
  have hAb := hAb F q₀ C B hπ_meas hF_ne
  intro Φ hΦ_meas hΦ_env hΦ_L2 δ hδ hCδ hF_L2 hq₀ n hn hΔq0_ptwise
  -- Abbreviations for the dyadic series and the envelope tail.
  set S : ℝ≥0∞ := ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
      * entropyIntegrand ((1/2 : ℝ)^q * δ) F P with hS_def
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt n)
      * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|} 1 ω ∂P with hT_def
  -- Specialise the four dyadic bounds.
  have hHδ := hH Φ hΦ_meas hΦ_env hΦ_L2 hδ hCδ hF_L2 hq₀ n hn
  have hBδ := hBb Φ hΦ_meas hΦ_env hΦ_L2 hδ hCδ n hn
  have hAδ := hAb Φ hΦ_meas hΦ_env hΦ_L2 hδ hCδ n hn
  have hMδ := hMb F q₀ C B hF_ne hδ hCδ n hn
  rw [← hS_def] at hHδ hAδ hMδ
  rw [← hS_def, ← hT_def] at hBδ
  -- Split the left-hand side, including the `Bmean` correction.
  have hsplit := chain_supnorm_le_three_part B hπ_meas hF_meas hX_meas hX_iindep hX_idem
    hX_law Φ hΦ_meas hΦ_env hΦ_L2 hδ n hn hΔq0_ptwise
  -- Assemble: LHS ≤ head + (TRUNC + Bseries) + Aseries + Bmean
  --                ≤ (cH+cB+cA+cM)·S + (cH+cB+cA+cM)·T.
  refine hsplit.trans ?_
  -- The B-link block carries `3·∑ levelOscSup`; dominate
  -- `trunc + 3·∑osc ≤ 3·(trunc + ∑osc) ≤ 3cB·(S + T)`.
  have h3Bδ :
      (∫⁻ ξ, supNormOver F
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun x => f x
                * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
          + 3 * (∑' q : ℕ, levelOscSup B μ X δ n q)
        ≤ ENNReal.ofReal (3 * cB) * S + ENNReal.ofReal (3 * cB) * T := by
    -- `ofReal(3cB) = 3·ofReal cB`.
    have h3cB : ENNReal.ofReal (3 * cB) = 3 * ENNReal.ofReal cB := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
        show (ENNReal.ofReal 3 : ℝ≥0∞) = 3 by simp]
    rw [h3cB]
    -- `trunc + 3∑osc ≤ 3·trunc + 3∑osc = 3·(trunc + ∑osc) ≤ 3·(cB S + cB T)`.
    set trunc : ℝ≥0∞ := ∫⁻ ξ, supNormOver F
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun x => f x
            * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ with htrunc_def
    have hosc : trunc + (∑' q : ℕ, levelOscSup B μ X δ n q) ≤ ENNReal.ofReal cB * S
        + ENNReal.ofReal cB * T := hBδ
    calc trunc + 3 * (∑' q : ℕ, levelOscSup B μ X δ n q)
        ≤ 3 * trunc + 3 * (∑' q : ℕ, levelOscSup B μ X δ n q) := by
          gcongr
          exact le_mul_of_one_le_left (zero_le) (by norm_num)
      _ = 3 * (trunc + (∑' q : ℕ, levelOscSup B μ X δ n q)) := by ring
      _ ≤ 3 * (ENNReal.ofReal cB * S + ENNReal.ofReal cB * T) := by gcongr
      _ = 3 * ENNReal.ofReal cB * S + 3 * ENNReal.ofReal cB * T := by ring
  -- Sum the four dyadic bounds (head: cH·S ; B-block: 3cB·S + 3cB·T ;
  -- A: cA·S ; Bmean: cM·S).
  have hsum :
      levelRepSup B μ X Φ δ n q₀
        + ((∫⁻ ξ, supNormOver F
              (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => f x
                  * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x)) ∂μ)
            + 3 * (∑' q : ℕ, levelOscSup B μ X δ n q))
        + (∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q))
        + Bmean B δ n
        ≤ (ENNReal.ofReal cH * S)
          + (ENNReal.ofReal (3 * cB) * S + ENNReal.ofReal (3 * cB) * T)
          + ENNReal.ofReal cA * S
          + ENNReal.ofReal cM * S := by
    exact add_le_add (add_le_add (add_le_add hHδ h3Bδ) hAδ) hMδ
  refine hsum.trans ?_
  -- Numerical rearrangement of constants: (cH+3cB+cA+cM)·S + (cH+3cB+cA+cM)·T dominates.
  have hcsum : ENNReal.ofReal (cH + 3 * cB + cA + cM)
      = ENNReal.ofReal cH + ENNReal.ofReal (3 * cB) + ENNReal.ofReal cA + ENNReal.ofReal cM := by
    rw [ENNReal.ofReal_add (by positivity) hcM_pos.le,
      ENNReal.ofReal_add (by positivity) hcA_pos.le,
      ENNReal.ofReal_add hcH_pos.le (by positivity)]
  rw [hcsum]
  -- Distribute and drop slack: only the B contribution carries a T term, so adding
  -- `(ofReal cH + ofReal cA + ofReal cM) * T` on the RHS only weakens the bound.
  calc (ENNReal.ofReal cH * S)
          + (ENNReal.ofReal (3 * cB) * S + ENNReal.ofReal (3 * cB) * T)
          + ENNReal.ofReal cA * S
          + ENNReal.ofReal cM * S
      = (ENNReal.ofReal cH * S + ENNReal.ofReal (3 * cB) * S + ENNReal.ofReal cA * S
            + ENNReal.ofReal cM * S)
          + ENNReal.ofReal (3 * cB) * T := by ring
    _ ≤ (ENNReal.ofReal cH * S + ENNReal.ofReal (3 * cB) * S + ENNReal.ofReal cA * S
            + ENNReal.ofReal cM * S)
          + (ENNReal.ofReal cH * T + ENNReal.ofReal (3 * cB) * T + ENNReal.ofReal cA * T
            + ENNReal.ofReal cM * T) := by
        gcongr
        calc ENNReal.ofReal (3 * cB) * T
            ≤ ENNReal.ofReal cH * T + ENNReal.ofReal (3 * cB) * T := le_add_self
          _ ≤ ENNReal.ofReal cH * T + ENNReal.ofReal (3 * cB) * T + ENNReal.ofReal cA * T :=
              le_add_of_nonneg_right (zero_le)
          _ ≤ ENNReal.ofReal cH * T + ENNReal.ofReal (3 * cB) * T + ENNReal.ofReal cA * T
                + ENNReal.ofReal cM * T :=
              le_add_of_nonneg_right (zero_le)
    _ = (ENNReal.ofReal cH + ENNReal.ofReal (3 * cB) + ENNReal.ofReal cA
            + ENNReal.ofReal cM) * S
          + (ENNReal.ofReal cH + ENNReal.ofReal (3 * cB) + ENNReal.ofReal cA
              + ENNReal.ofReal cM) * T := by
        rw [add_mul, add_mul, add_mul, add_mul, add_mul, add_mul]

/-- **Measurable-majorant form of the uniform dyadic chaining bound.**

Same hypotheses and same RHS as `chain_supnorm_dyadic_bound_uniform`, but instead of
bounding the (non-measurable) integrand `g_F' ξ := supNormOver F (𝔾ₙ ξ)` directly, it
produces a MEASURABLE `Maj : Ξ → ℝ≥0∞` with `g_F' ≤ Maj` pointwise and `∫⁻ Maj ≤ RHS`.

The majorant is the pointwise gated-telescope decomposition of `chain_supnorm_le_pointwise`
(`g_F' ξ ≤ head ξ + trunc ξ + (∑ q, oscDom q ξ) + (∑ q, jump q ξ)`) with the ONLY
non-measurable summand `trunc` replaced by its measurable dominator `Btrunc`
(`supNormProcess_dominated_pointwise_bound`, with `Ψ := |Φ|·1{√n·globalThreshold B δ<|Φ|}`).
`head`, `oscDom q`, `jump q` are measurable for free (the finite-`⨆ᵢ` measurability lemma),
so `Maj := head + Btrunc + (∑ q, oscDom q) + (∑ q, jump q)` is measurable; the integral bound
re-runs the SAME four-dyadic-bound arithmetic as `chain_supnorm_dyadic_bound_uniform`, except
the `∫⁻ trunc ≤ 4√n·∫⁻Ψ` step (`tight_envelope_truncation_bound`) is replaced by the identical
`∫⁻ Btrunc ≤ 4√n·∫⁻Ψ` step (`supNormProcess_dominated_integral_bound`) — same constant `c`. -/
theorem chain_supnorm_measurableMajorant_dyadic_bound_uniform
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ (F : Set (Ω → ℝ)) (q₀ : ℕ) (C : ℝ) (B : NestedBracketPartition F P q₀ C)
        (_hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
        (_hF_ne : F.Nonempty)
        (_hF_meas : ∀ f ∈ F, Measurable f),
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δ : ℝ}, 0 < δ → C = δ →
          (∀ f ∈ F, eLpNorm f 2 P ≤ ENNReal.ofReal δ) →
          (4 * δ ≤ (1 / 2 : ℝ) ^ q₀ ∧ (1 / 2 : ℝ) ^ q₀ ≤ 8 * δ) →
          ∀ (n : ℕ), 1 ≤ n →
            (∀ (i : Fin (B.Nq q₀)) (x : Ω),
                B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δ q₀) →
            ∃ Maj : Ξ → ℝ≥0∞, Measurable Maj ∧
              (∀ ξ, supNormOver F
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ≤ Maj ξ) ∧
              ∫⁻ ξ, Maj ξ ∂μ
                ≤ ENNReal.ofReal c
                    * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                        * entropyIntegrand ((1/2 : ℝ)^q * δ) F P)
                  + ENNReal.ofReal c *
                    (ENNReal.ofReal (Real.sqrt n)
                      * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                          * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|}
                              1 ω ∂P) := by
  classical
  obtain ⟨cH, hcH_pos, hH⟩ :=
    chain_head_dyadic_bound hX_meas hX_iindep hX_idem hX_law
  obtain ⟨cOsc, hcOsc_pos, hOscb⟩ :=
    chain_B_levelOscSup_dyadic_bound hX_meas hX_iindep hX_idem hX_law
  obtain ⟨cA, hcA_pos, hAb⟩ :=
    chain_A_dyadic_bound hX_meas hX_iindep hX_idem hX_law
  obtain ⟨cM, hcM_pos, hMb⟩ :=
    chain_Bmean_dyadic_bound (P := P)
  -- universal constant: `cH + 3·cOsc + cA + cM` carries the dyadic series (`S`), plus `+4`
  -- to absorb the `Btrunc` tail `∫⁻Btrunc ≤ 4√n·∫⁻Ψ = 4·T` (the same `4` as the
  -- `tight_envelope_truncation_bound`, here via `supNormProcess_dominated_integral_bound`).
  refine ⟨cH + 3 * cOsc + cA + cM + 4,
    by nlinarith [hcH_pos, hcA_pos, hcM_pos, hcOsc_pos], ?_⟩
  intro F q₀ C B hπ_meas hF_ne hF_meas
  have hH := hH F q₀ C B hπ_meas hF_ne
  have hAb := hAb F q₀ C B hπ_meas hF_ne
  intro Φ hΦ_meas hΦ_env hΦ_L2 δ hδ hCδ hF_L2 hq₀ n hn hΔq0_ptwise
  -- ===== Per-`ξ` measurable majorant pieces (mirror `chain_supnorm_le_decomposition`) =====
  set head : Ξ → ℝ≥0∞ := fun ξ => ⨆ i : Fin (B.Nq q₀), ENNReal.ofReal
      |empiricalProcess P n (fun k : Fin n => X k.val ξ) (truncRep B Φ δ n q₀ i)|
    with hhead_def
  set jump : ℕ → Ξ → ℝ≥0∞ := fun q ξ => ⨆ i : Fin (B.Nq (q₀ + q + 1)),
      ENNReal.ofReal |empiricalProcess P n (fun k : Fin n => X k.val ξ)
        (truncJump B δ n (Nat.le_add_right q₀ q) i)|
    with hjump_def
  set bmeanConst : ℕ → ℝ≥0∞ := fun q =>
      4 * ENNReal.ofReal (Real.sqrt n)
        * ⨆ i : Fin (B.Nq (q₀ + q)), ∫⁻ x, ENNReal.ofReal
            (B.Δ (q₀ + q) i x
              * Set.indicator {y | chainB B δ n (q₀ + q) i y} (1 : Ω → ℝ) x) ∂P
    with hbmeanConst_def
  set oscDom : ℕ → Ξ → ℝ≥0∞ := fun q ξ =>
      3 * (⨆ i : Fin (B.Nq (q₀ + q)), ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ)
              (truncOsc B δ n (q₀ + q) i)|)
        + bmeanConst q
    with hoscDom_def
  -- The threshold-truncation envelope `Ψ` and the measurable `Btrunc` dominator of `trunc`.
  set Ψ : Ω → ℝ := fun x =>
      |Φ x| * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x with hΨ_def
  set Btrunc : Ξ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Real.sqrt n) *
      (ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))
        + ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P) with hBtrunc_def
  -- The dominated class (= the trunc evaluator family) and the domination `|·| ≤ Ψ`.
  set 𝒢 : Set (Ω → ℝ) :=
      {g | ∃ f ∈ F, g = fun x => f x
        * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x} with h𝒢_def
  have hΨ_meas : Measurable Ψ := by
    refine hΦ_meas.norm.mul ?_
    exact measurable_const.indicator
      (measurableSet_lt measurable_const hΦ_meas.norm)
  have hΨ_nn : ∀ x, 0 ≤ Ψ x := by
    intro x
    refine mul_nonneg (abs_nonneg _) ?_
    by_cases hx : x ∈ {y | Real.sqrt n * globalThreshold B δ < |Φ y|} <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hdom : ∀ g ∈ 𝒢, ∀ x, |g x| ≤ Ψ x := by
    rintro g ⟨f, hf, rfl⟩ x
    change |f x * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x|
        ≤ |Φ x| * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x
    by_cases hx : x ∈ {y | Real.sqrt n * globalThreshold B δ < |Φ y|}
    · rw [Set.indicator_of_mem hx]
      simp only [Pi.one_apply, mul_one]
      exact (hΦ_env f hf x).trans (le_abs_self _)
    · rw [Set.indicator_of_notMem hx]
      simp
  -- The assembled measurable majorant.
  set Maj : Ξ → ℝ≥0∞ := fun ξ =>
      head ξ + Btrunc ξ + (∑' q, oscDom q ξ) + (∑' q, jump q ξ) with hMaj_def
  -- ===== Measurability of `Maj` =====
  have hhead_meas : Measurable head := by
    refine measurable_iSup_ofReal_abs_empiricalProcess hX_meas n _ (fun i => ?_)
    refine (hπ_meas (le_refl q₀) i).mul ?_
    exact measurable_one.indicator
      (measurableSet_le hΦ_meas.norm measurable_const)
  have hjump_meas : ∀ q, Measurable (jump q) := by
    intro q
    refine measurable_iSup_ofReal_abs_empiricalProcess hX_meas n _ (fun i => ?_)
    refine (B.jump_measurable hπ_meas (Nat.le_add_right q₀ q) i).mul ?_
    exact measurable_one.indicator
      (chainA_measurableSet B δ n (q₀ + q) (B.parent (Nat.le_add_right q₀ q) i))
  have hoscDom_meas : ∀ q, Measurable (oscDom q) := by
    intro q
    refine Measurable.add ?_ measurable_const
    refine Measurable.const_mul ?_ 3
    refine measurable_iSup_ofReal_abs_empiricalProcess hX_meas n _ (fun i => ?_)
    exact (B.Δ_meas (Nat.le_add_right q₀ q) i).mul
      (measurable_const.indicator
        (chainB_measurableSet B n (Nat.le_add_right q₀ q) i))
  have hBtrunc_meas : Measurable Btrunc := by
    refine Measurable.const_mul ?_ _
    refine Measurable.fun_add ?_ measurable_const
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΨ_meas.comp (hX_meas i.val)
  have hMaj_meas : Measurable Maj := by
    refine (((hhead_meas.add hBtrunc_meas).add ?_).add ?_)
    · exact Measurable.ennreal_tsum hoscDom_meas
    · exact Measurable.ennreal_tsum hjump_meas
  -- ===== Pointwise: `g_F' ξ ≤ Maj ξ` =====
  have hptwise : ∀ ξ, supNormOver F
      (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ≤ Maj ξ := by
    intro ξ
    have hpt := chain_supnorm_le_pointwise B hπ_meas hF_meas (X := X) Φ hΦ_meas hΦ_env hΦ_L2
      hδ n hn ξ hΔq0_ptwise
    refine hpt.trans ?_
    -- the trunc evaluator sup `= supNormOver 𝒢 (𝔾ₙ)` (reindexing), dominated by `Btrunc`.
    have htrunc_le : supNormOver F
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (fun x => f x
            * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x))
          ≤ Btrunc ξ := by
      have heq : supNormOver F
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (fun x => f x
              * Set.indicator {y | Real.sqrt n * globalThreshold B δ < |Φ y|} 1 x))
          = supNormOver 𝒢
              (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
        unfold supNormOver
        refine le_antisymm ?_ ?_
        · refine iSup₂_le fun f hf => ?_
          exact le_iSup₂_of_le _ ⟨f, hf, rfl⟩ le_rfl
        · refine iSup₂_le fun g hg => ?_
          obtain ⟨f, hf, rfl⟩ := hg
          exact le_iSup₂_of_le f hf le_rfl
      rw [heq]
      exact supNormProcess_dominated_pointwise_bound (P := P) 𝒢 Ψ hdom n hn ξ
    -- assemble: head + (trunc + (blink' folded into oscDom)) + jump ≤ Maj
    simp only [hMaj_def]
    -- The pointwise lemma's RHS is `head + (trunc + ∑blink) + ∑jump`; we bound
    -- `trunc ≤ Btrunc` and `∑blink ≤ ∑oscDom`, then reassociate to `Maj`.
    rw [show head ξ + Btrunc ξ + (∑' (q : ℕ), oscDom q ξ) + ∑' (q : ℕ), jump q ξ
          = head ξ + (Btrunc ξ + ∑' (q : ℕ), oscDom q ξ) + ∑' (q : ℕ), jump q ξ by ring]
    refine add_le_add (add_le_add le_rfl (add_le_add htrunc_le ?_)) le_rfl
    refine ENNReal.tsum_le_tsum (fun q => ?_)
    simpa only [hoscDom_def, hbmeanConst_def] using
      supNormOver_link_meanSplit_pointwise_le B hπ_meas hF_meas (X := X) n
        (Nat.le_add_right q₀ q) ξ
  refine ⟨Maj, hMaj_meas, hptwise, ?_⟩
  -- ===== Integral bound `∫⁻ Maj ≤ RHS` (same arithmetic as the uniform bound) =====
  -- Abbreviate the dyadic series by `S` and the envelope tail by `T`.
  set S : ℝ≥0∞ := ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
      * entropyIntegrand ((1/2 : ℝ)^q * δ) F P with hS_def
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt n)
      * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|} 1 ω ∂P with hT_def
  -- `∫⁻ Ψ = ∫⁻ ofReal|Φ|·1{...}` (the indicator pulled out of `ofReal`), so `T = √n·∫⁻Ψ`.
  have hΨ_int_eq : ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P
      = ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|} 1 ω ∂P := by
    refine lintegral_congr (fun x => ?_)
    rw [hΨ_def]
    by_cases hx : x ∈ {y | Real.sqrt n * globalThreshold B δ < |Φ y|}
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- ===== Integral identities for the measurable pieces =====
  -- `∫⁻ head = levelRepSup` (definitional).
  have hhead_int : ∫⁻ ξ, head ξ ∂μ = levelRepSup B μ X Φ δ n q₀ := rfl
  -- `∫⁻ jump q = levelJumpSup q` (definitional).
  have hjump_int : ∀ q, ∫⁻ ξ, jump q ξ ∂μ
      = levelJumpSup B μ X δ n (Nat.le_add_right q₀ q) := fun q => rfl
  -- `∫⁻ oscDom q = 3·levelOscSup (q₀+q) + bmeanConst q`.
  have hoscDom_int : ∀ q, ∫⁻ ξ, oscDom q ξ ∂μ
      = 3 * levelOscSup B μ X δ n (q₀ + q) + bmeanConst q := by
    intro q
    rw [hoscDom_def]
    rw [lintegral_add_right' _ measurable_const.aemeasurable]
    rw [lintegral_const_mul' _ _ (by norm_num : (3 : ℝ≥0∞) ≠ ⊤)]
    rw [lintegral_const, measure_univ, mul_one]
    rfl
  -- ===== `∫⁻ Btrunc ≤ 4·T` =====
  have hBtrunc_int : ∫⁻ ξ, Btrunc ξ ∂μ ≤ 4 * T := by
    have hΨ_meas_avg : AEMeasurable
        (fun ξ : Ξ => ENNReal.ofReal
          (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))) μ := by
      refine Measurable.aemeasurable ?_
      refine Measurable.ennreal_ofReal ?_
      unfold empiricalAvg
      refine Measurable.const_mul ?_ _
      refine Finset.measurable_sum Finset.univ ?_
      intro i _
      exact hΨ_meas.comp (hX_meas i.val)
    have hemp_le := lintegral_empiricalAvg_le (P := P) hX_meas hX_idem hX_law Ψ hΨ_meas hΨ_nn n hn
    rw [hBtrunc_def]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left' hΨ_meas_avg,
      lintegral_const, measure_univ, mul_one]
    calc ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ξ, ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ
              + ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P)
        ≤ ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ x, ENNReal.ofReal (Ψ x) ∂P + ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P) :=
          mul_le_mul_of_nonneg_left (add_le_add hemp_le le_rfl) (zero_le)
      _ = 2 * (ENNReal.ofReal (Real.sqrt n) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P) := by ring
      _ = 2 * T := by rw [hT_def, hΨ_int_eq]
      _ ≤ 4 * T := by gcongr; norm_num
  -- ===== Split `∫⁻ Maj` into the four measurable pieces =====
  have hoscDom_sum_meas : Measurable (fun ξ => ∑' q, oscDom q ξ) :=
    Measurable.ennreal_tsum hoscDom_meas
  have hjump_sum_meas : Measurable (fun ξ => ∑' q, jump q ξ) :=
    Measurable.ennreal_tsum hjump_meas
  have hMaj_split : ∫⁻ ξ, Maj ξ ∂μ
      = (∫⁻ ξ, head ξ ∂μ) + (∫⁻ ξ, Btrunc ξ ∂μ)
        + (∑' q, ∫⁻ ξ, oscDom q ξ ∂μ) + (∑' q, ∫⁻ ξ, jump q ξ ∂μ) := by
    rw [hMaj_def]
    rw [lintegral_add_right' _ hjump_sum_meas.aemeasurable,
      lintegral_add_right' _ hoscDom_sum_meas.aemeasurable,
      lintegral_add_left' hhead_meas.aemeasurable,
      lintegral_tsum (fun q => (hoscDom_meas q).aemeasurable),
      lintegral_tsum (fun q => (hjump_meas q).aemeasurable)]
  -- ===== Specialise the dyadic sub-bounds =====
  have hHδ := hH Φ hΦ_meas hΦ_env hΦ_L2 hδ hCδ hF_L2 hq₀ n hn
  have hOscδ := hOscb F q₀ C B hπ_meas hF_ne hδ hCδ n hn
  have hAδ := hAb Φ hΦ_meas hΦ_env hΦ_L2 hδ hCδ n hn
  have hMδ := hMb F q₀ C B hF_ne hδ hCδ n hn
  rw [← hS_def] at hHδ hOscδ hAδ hMδ
  -- fold `∑' oscDom = 3·∑levelOscSup(q₀+q) + Bmean`.
  have hosc_sum : (∑' q, ∫⁻ ξ, oscDom q ξ ∂μ)
      = 3 * (∑' q : ℕ, levelOscSup B μ X δ n (q₀ + q)) + Bmean B δ n := by
    simp only [hoscDom_int]
    rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hbmeanConst_def, Bmean]
  have hosc_inj : 3 * (∑' q : ℕ, levelOscSup B μ X δ n (q₀ + q))
      ≤ 3 * (∑' q : ℕ, levelOscSup B μ X δ n q) :=
    mul_le_mul_of_nonneg_left
      (ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective q₀)
        (levelOscSup B μ X δ n)) (zero_le)
  have hjump_sum_eq : (∑' q, ∫⁻ ξ, jump q ξ ∂μ)
      = ∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q) := by
    simp only [hjump_int]
  -- numeral facts for the constant.
  set c : ℝ := cH + 3 * cOsc + cA + cM + 4 with hc_def
  have hcsplit : ENNReal.ofReal c
      = ENNReal.ofReal cH + ENNReal.ofReal (3 * cOsc) + ENNReal.ofReal cA
          + ENNReal.ofReal cM + 4 := by
    rw [hc_def, ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_add (by positivity) hcM_pos.le,
      ENNReal.ofReal_add (by positivity) hcA_pos.le,
      ENNReal.ofReal_add hcH_pos.le (by positivity),
      show (ENNReal.ofReal 4 : ℝ≥0∞) = 4 by rw [ENNReal.ofReal_ofNat]]
  have h3cOsc : ENNReal.ofReal (3 * cOsc) = 3 * ENNReal.ofReal cOsc := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
      show (ENNReal.ofReal 3 : ℝ≥0∞) = 3 by simp]
  -- ===== Assemble =====
  rw [hMaj_split, hhead_int, hosc_sum, hjump_sum_eq]
  calc (levelRepSup B μ X Φ δ n q₀) + (∫⁻ ξ, Btrunc ξ ∂μ)
          + (3 * (∑' q : ℕ, levelOscSup B μ X δ n (q₀ + q)) + Bmean B δ n)
          + ∑' q : ℕ, levelJumpSup B μ X δ n (Nat.le_add_right q₀ q)
      ≤ (ENNReal.ofReal cH * S) + (4 * T)
          + (3 * (ENNReal.ofReal cOsc * S) + ENNReal.ofReal cM * S)
          + ENNReal.ofReal cA * S := by
        refine add_le_add (add_le_add (add_le_add hHδ hBtrunc_int) ?_) hAδ
        refine add_le_add (hosc_inj.trans ?_) hMδ
        exact mul_le_mul_of_nonneg_left hOscδ (zero_le)
    _ = (ENNReal.ofReal cH + 3 * ENNReal.ofReal cOsc + ENNReal.ofReal cA
            + ENNReal.ofReal cM) * S + 4 * T := by ring
    _ ≤ ENNReal.ofReal c * S + ENNReal.ofReal c * T := by
        rw [hcsplit, h3cOsc]
        refine add_le_add (mul_le_mul_of_nonneg_right ?_ (zero_le))
          (mul_le_mul_of_nonneg_right ?_ (zero_le))
        · exact le_add_of_nonneg_right (zero_le)
        · exact le_add_of_nonneg_left (zero_le)

/-- **Integrated dyadic chaining bound for `∫⁻ supNormOver F (𝔾ₙ)`**
(vdV Lemma 19.34).

No `EmpProcSeparable`/`hF_sep` hypothesis is needed. Splitting the integral with
`chain_supnorm_le_decomposition` and `chain_supnorm_le_three_part` bounds the
uncountable per-cell B-link supremum by the measurable finite-`⨆ᵢ` envelope
of the explicit cell oscillation `truncOsc i` (via the per-`ξ` mean split
`supNormOver_link_meanSplit_pointwise_le`), so no per-cell separability bridge is
needed. The per-level dyadic components (head / A / B / B-mean dyadic bounds
`chain_head_dyadic_bound`, `chain_A_dyadic_bound`, `chain_B_dyadic_bound`,
`chain_Bmean_dyadic_bound`) and the telescope give the resulting estimate. -/
theorem chain_supnorm_dyadic_bound
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
        ∀ {δ : ℝ}, 0 < δ → C = δ →
          (∀ f ∈ F, eLpNorm f 2 P ≤ ENNReal.ofReal δ) →
          (4 * δ ≤ (1 / 2 : ℝ) ^ q₀ ∧ (1 / 2 : ℝ) ^ q₀ ≤ 8 * δ) →
          ∀ (n : ℕ), 1 ≤ n →
            (∀ (i : Fin (B.Nq q₀)) (x : Ω),
                B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δ q₀) →
            ∫⁻ ξ, supNormOver F
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
              ≤ ENNReal.ofReal c
                  * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                      * entropyIntegrand ((1/2 : ℝ)^q * δ) F P)
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|}
                            1 ω ∂P) :=
  -- Specialise the class/level/scale-uniform form to `F`, `q₀`, `C`, and `B`.
  let ⟨c, hc_pos, hbound⟩ :=
    chain_supnorm_dyadic_bound_uniform hX_meas hX_iindep hX_idem hX_law
  ⟨c, lt_of_lt_of_le one_pos hc_pos, hbound F q₀ C B hπ_meas hF_ne hF_meas⟩

end Assembly

/-! ## The bound `hChainBound_outer`

The following lemma states the chaining estimate in the existential form used
with `nestedBracketPartition_of_covers` and
`dyadic_sum_le_bracketingEntropyIntegral`. -/

/-- **The bound `hChainBound_outer` from a nested bracketing partition.**

Given a `NestedBracketPartition` of `F`, this gives the universal-constant
chaining bound in the existential form `hChainBound_outer` used in
`DonskerBracketing.lean`. The B-series and A-series bounds sum to
`c'·(dyadic entropy series)
+ c'·√n·tail`; the dyadic-entropy comparison `dyadic_sum_le_bracketingEntropyIntegral`
replaces the dyadic series by `2·J_{[]}(δ, F, L²(P))`, yielding the universal
`c = 2c'`.

vdV §19.6 p.286-288. The substantive content is in `chain_supnorm_dyadic_bound`;
this lemma substitutes the dyadic series by `J` and handles the `n = 0` case,
where the empirical process vanishes. -/
theorem hChainBound_outer_of_nestedPartition
    [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (B : NestedBracketPartition F P q₀ C)
    (hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i))
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F Φ → MemLp Φ 2 P →
      ∀ {δq : ℝ}, 0 < δq → C = δq →
        (∀ f ∈ F, eLpNorm f 2 P ≤ ENNReal.ofReal δq) →
        (4 * δq ≤ (1 / 2 : ℝ) ^ q₀ ∧ (1 / 2 : ℝ) ^ q₀ ≤ 8 * δq) →
        ∀ (n : ℕ),
          (∀ (i : Fin (B.Nq q₀)) (x : Ω),
              B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δq q₀) →
          ∫⁻ ξ, supNormOver F
                (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
            ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
              + ENNReal.ofReal c *
                (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | Real.sqrt n * globalThreshold B δq < |Φ x|} 1 ω ∂P) :=
  by
  -- Use the universal constant from the dyadic-series bound.
  obtain ⟨c₀, hc₀_pos, hbound⟩ :=
    chain_supnorm_dyadic_bound B hπ_meas hF_ne hF_meas hX_meas hX_iindep hX_idem hX_law
  -- The outer universal constant absorbs the factor 2 from `dyadic ≤ 2·J`.
  refine ⟨2 * c₀, by positivity, ?_⟩
  intro Φ hΦ_meas hΦ_env hΦ_L2 δq hδq hCδ hF_L2 hq₀ n hΔq0_ptwise
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · -- `n = 0`: the empirical process is identically 0, so the LHS integral is 0.
    subst hn0
    have h_lhs : ∫⁻ ξ, supNormOver F
          (fun f => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) f) ∂μ = 0 := by
      have h_sup0 : ∀ ξ : Ξ, supNormOver F
          (fun f => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) f) = 0 := by
        intro ξ
        simp only [supNormOver, empiricalProcess_zero, abs_zero, ENNReal.ofReal_zero]
        exact le_antisymm (by simp) (by positivity)
      simp only [h_sup0, lintegral_zero]
    rw [h_lhs]; exact zero_le
  -- `n ≥ 1`: apply the dyadic bound, then substitute `dyadic ≤ 2·J`.
  have hn1 : 1 ≤ n := hn_pos
  have hdyadic := hbound Φ hΦ_meas hΦ_env hΦ_L2 hδq hCδ hF_L2 hq₀ n hn1 hΔq0_ptwise
  -- The dyadic entropy series is at most `2 · J_{[]}(δq, F, L²(P))`.
  have hL5 :
      (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δq)
          * entropyIntegrand ((1/2 : ℝ)^q * δq) F P)
        ≤ 2 * bracketingEntropyIntegral δq F P :=
    dyadic_sum_le_bracketingEntropyIntegral hδq
  -- Numerical rewrite: `ofReal (2*c₀) = 2 * ofReal c₀`.
  have h2c : ENNReal.ofReal (2 * c₀) = 2 * ENNReal.ofReal c₀ := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  refine hdyadic.trans ?_
  -- `c₀·dyadic + c₀·tail ≤ 2c₀·J + 2c₀·tail`.
  rw [h2c]
  refine add_le_add ?_ ?_
  · -- `ofReal c₀ * dyadic ≤ 2 * ofReal c₀ * J`
    calc ENNReal.ofReal c₀
            * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δq)
                * entropyIntegrand ((1/2 : ℝ)^q * δq) F P)
          ≤ ENNReal.ofReal c₀ * (2 * bracketingEntropyIntegral δq F P) := by gcongr
      _ = 2 * ENNReal.ofReal c₀ * bracketingEntropyIntegral δq F P := by ring
  · -- `ofReal c₀ * tail ≤ 2 * ofReal c₀ * tail`
    have h_le : ENNReal.ofReal c₀ ≤ 2 * ENNReal.ofReal c₀ := by
      calc ENNReal.ofReal c₀ = 1 * ENNReal.ofReal c₀ := (one_mul _).symm
        _ ≤ 2 * ENNReal.ofReal c₀ := by gcongr; norm_num
    exact mul_le_mul_of_nonneg_right h_le (zero_le)

/-! ## Localized chaining bound (vdV §19.2)

The genuine vdV §19.2 localized chaining bound: bounds
`∫⁻ supNormOver (localizedDifferenceClass F P δq) (𝔾ₙ)` (the δq-shrunk difference
class, whose supremum vanishes with `δq`) rather than the unlocalized full-class
supremum.

The construction applies `chain_supnorm_dyadic_bound` to a
**clamped truncated** version of the localized difference class
`G := localizedDifferenceClass F P δq`, then lifts back from
`truncateClass G M` to `G` via `empiricalProcess_add` + `tight_envelope_truncation_bound`.
The localized class satisfies `hF_L2` at scale `δq` by
construction (`localizedDifferenceClass_hF_L2` and clamp-shrinks-L²). -/

/-- **Dyadic-scale `q₀` exists for small `δ`.** For `0 < δ ≤ 1/4` there is a natural
number `q₀` with `4δ ≤ (1/2)^{q₀} ≤ 8δ`: the dyadic powers `(1/2)^q` step by ratio `2`,
and the target window `[4δ, 8δ]` (also ratio `2`) sits inside `(0, 1]` when `δ ≤ 1/4`,
so one power lands inside. vdV p.287 ("fix an integer `q₀` such that `4δ ≤ 2^{−q₀} ≤ 8δ`").
The `δ ≤ 1/4` constraint is the localization regime in which the
radius `δq → 0`; large `δq` is handled separately by a trivial bound in the main
theorem. -/
lemma exists_q0_window {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ q₀ : ℕ, 4 * δ ≤ (1 / 2 : ℝ) ^ q₀ ∧ (1 / 2 : ℝ) ^ q₀ ≤ 8 * δ := by
  classical
  -- Least index `q₀` with `(1/2)^q ≤ 8δ` exists (powers → 0).
  have hhalf_lt : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < 8 * δ) hhalf_lt
  have hexists : ∃ q : ℕ, (1 / 2 : ℝ) ^ q ≤ 8 * δ := ⟨q, hq.le⟩
  set q₀ := Nat.find hexists with hq₀_def
  have hq₀_le : (1 / 2 : ℝ) ^ q₀ ≤ 8 * δ := Nat.find_spec hexists
  refine ⟨q₀, ?_, hq₀_le⟩
  rcases Nat.eq_zero_or_pos q₀ with hq0 | hq0
  · -- `q₀ = 0`: `(1/2)^0 = 1`, and `δ ≤ 1/4 ⟹ 4δ ≤ 1`.
    rw [hq0, pow_zero]; linarith
  · -- `q₀ ≥ 1`: minimality gives `(1/2)^{q₀-1} > 8δ`, halve ⟹ `(1/2)^{q₀} > 4δ`.
    have hmin : ¬ ((1 / 2 : ℝ) ^ (q₀ - 1) ≤ 8 * δ) :=
      Nat.find_min hexists (by omega : q₀ - 1 < q₀)
    push Not at hmin
    have hpow_succ : (1 / 2 : ℝ) ^ q₀ = (1 / 2 : ℝ) ^ (q₀ - 1) * (1 / 2 : ℝ) := by
      rw [← pow_succ]; congr 1; omega
    rw [hpow_succ]; nlinarith [hmin]

/-- **Finite bracketing entropy of the difference class.** From `J_{[]}(1, F) < ⊤`,
the difference class also has finite entropy: `J_{[]}(1, F − F) ≤ 2√2·J_{[]}(1, F) < ⊤`
(vdV Lemma 19.31, via `bracketingEntropyIntegral_diff_le_class`, whose per-scale cover
hypothesis is discharged from `h_int` by `hasFiniteBracketingCover_of_entropyIntegral_lt_top`). -/
lemma bracketingEntropyIntegral_differenceClass_lt_top
    [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    bracketingEntropyIntegral 1 (differenceClass F) P < ⊤ := by
  have hcover : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F (ε / 2) 2 P :=
    fun ε hε => hasFiniteBracketingCover_of_entropyIntegral_lt_top h_int (by positivity)
  refine lt_of_le_of_lt
    (bracketingEntropyIntegral_diff_le_class (by norm_num : (0:ℝ) ≤ 1) hcover) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h_int

/-- **Per-level finite bracketing covers of the localized difference class.**
From `J_{[]}(1, F) < ⊤`, every positive offset dyadic scale admits a finite bracketing
cover of `localizedDifferenceClass F P δq`. The chain is: `differenceClass F` has finite
entropy (`bracketingEntropyIntegral_differenceClass_lt_top`) ⟹ finite covers at every
scale (`hasFiniteBracketingCover_of_entropyIntegral_lt_top`) ⟹ covers of the localized
slice by monotonicity (`HasFiniteBracketingCover.mono`, `localizedDifferenceClass_subset`).
The clamped-partition constructor truncates these internally, so this (un-truncated) cover
is exactly its `hcov` input. -/
lemma hasFiniteBracketingCover_localized
    [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    (δq : ℝ) {q₀' : ℕ} {δ' : ℝ} (hδ' : 0 < δ') :
    ∀ p, q₀' ≤ p →
      HasFiniteBracketingCover
        (localizedDifferenceClass F P δq)
        ((1 / 2 : ℝ) ^ (p - q₀') * δ') 2 P := by
  intro p _hp
  have hdiff_int := bracketingEntropyIntegral_differenceClass_lt_top h_int
  have hscale : 0 < (1 / 2 : ℝ) ^ (p - q₀') * δ' := by positivity
  have hcov_diff :
      HasFiniteBracketingCover (differenceClass F) ((1 / 2 : ℝ) ^ (p - q₀') * δ') 2 P :=
    hasFiniteBracketingCover_of_entropyIntegral_lt_top hdiff_int hscale
  exact hcov_diff.mono localizedDifferenceClass_subset

/-- **Bracketing number of a truncated class ≤ that of the class.** Every ε-bracketing
cover `(l, u)` of `G` clamps to an ε-bracketing cover `(clampFn M l, clampFn M u)` of the
*same cardinality* of `truncateClass G M` (`isEpsBracket_clamp` keeps the brackets, the
cover transports via `clampReal` monotonicity), so the infimum defining
`bracketingNumber (truncateClass G M)` ranges over a superset of admissible sizes. -/
lemma bracketingNumber_truncateClass_le {G : Set (Ω → ℝ)} {ε : ℝ} {M : ℝ} (hM : 0 ≤ M) :
    bracketingNumber ε (truncateClass G M) 2 P ≤ bracketingNumber ε G 2 P := by
  unfold bracketingNumber
  refine iInf_mono fun k => ?_
  refine iInf_mono' fun hk => ?_
  obtain ⟨l, u, hbr, hcov⟩ := hk
  refine ⟨⟨fun i => clampFn M (l i), fun i => clampFn M (u i),
    fun i => isEpsBracket_clamp hM (hbr i), ?_⟩, le_rfl⟩
  -- transport the cover: `g' = clampFn M g`, `g ∈ G`; the bracket of `g` clamps to one of `g'`.
  rintro g' ⟨g, hgG, rfl⟩
  obtain ⟨i, hi⟩ := hcov g hgG
  refine ⟨i, fun x => ?_⟩
  exact ⟨clampReal_mono M (hi x).1, clampReal_mono M (hi x).2⟩

/-- **Entropy integral of a truncated class ≤ that of the class.** Integrate
`bracketingNumber_truncateClass_le` through `entropyWeight` (`entropyWeight_mono`) over
`Ioc 0 δ` (`setLIntegral_mono'`). -/
lemma bracketingEntropyIntegral_truncateClass_le {G : Set (Ω → ℝ)} {δ : ℝ} {M : ℝ}
    (hM : 0 ≤ M) :
    bracketingEntropyIntegral δ (truncateClass G M) P ≤ bracketingEntropyIntegral δ G P := by
  rw [bracketingEntropyIntegral_eq_setLIntegral, bracketingEntropyIntegral_eq_setLIntegral]
  refine setLIntegral_mono' measurableSet_Ioc (fun ε _ => ?_)
  exact entropyWeight_mono (bracketingNumber_truncateClass_le hM)

/-! ## Localized chaining bound — helper lemmas

The localized bound is proved over a clamped truncation of the localized
difference class. Two facts are used:

* `localized_clamp_Δq0_discharge` — the `hΔq0_ptwise` discharge (vdV `A_{q₀} f = 1`).
  The clamped partition's oscillation envelope satisfies `Δ_{q₀} ≤ 2M`
  (`nestedBracketPartition_of_finiteEntropy_clamped_Δ_le`); choosing the clamp level
  `M = √n · chainThreshold B δq q₀ / 2` would make `2M = √n · chainThreshold B δq q₀`
  exactly, except that `chainThreshold B δq q₀` reads `B.Nq (q₀+1)`, which itself
  depends on `M` (the truncated-class cover cardinality), creating a self-reference.
  The book breaks this by an `M`-independent **upper** bound on the truncated class's
  bracketing number (`N_{[]}(·, truncate(localized)) ≤ N_{[]}(·, F − F)`, since every
  `F − F` cover clamps to a truncated-localized cover of the same cardinality), which
  lower-bounds `chainThreshold` independently of `M`; one then picks `M` from that
  `M`-independent bound.

* `localized_dyadic_to_J` — the dyadic-series → `J_{[]}(δq, F)` reduction. By
  `dyadic_sum_le_bracketingEntropyIntegral`, the dyadic series over
  `truncateClass (localized) M` is bounded by `2·J_{[]}(δq, truncate(localized))`,
  then by `2·J_{[]}(δq, F − F)` (entropy monotone in the class), then by
  `2 · 2√2 · J_{[]}(δq, F)` (`bracketingEntropyIntegral_diff_le_class`). -/

/-- **`M`-free lower bound on the clamped partition's chain threshold.** To avoid
the `M`-fixed-point self-reference, observe that `chainThreshold (B(M))
δq q₀ = δq / (1 + √log(1 + B(M).Nq(q₀+1)))` reads the truncated-class cover card
`B(M).Nq(q₀+1)`, which depends on `M`; but it is bounded *above* by the `M`-free product
`NB_{q₀}·NB_{q₀+1}` of bracketing numbers of the (un-truncated) localized class `G`
(via `card_le` ⟹ `coverCard_le` ⟹ `bracketingNumber_truncateClass_le`).  Hence
`chainThreshold (B(M)) δq q₀ ≥ θ := δq / (1 + √log(1 + (NB_{q₀}·NB_{q₀+1} : ℝ)))`, an
`M`-free positive constant, for **every** clamp level `M ≥ 0`.  Choosing `Mc := √n·θ/2`
then makes `2·Mc = √n·θ ≤ √n·chainThreshold (B(Mc))` self-consistently. -/
lemma localized_chainThreshold_lower_bound
    [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {δq : ℝ} (hδq : 0 < δq)
    (hF_diff_meas : ∀ h ∈ localizedDifferenceClass F P δq, Measurable h)
    {q₀ : ℕ} :
    ∃ θ : ℝ, 0 < θ ∧ (∃ cθ : ℝ, 0 < cθ ∧ cθ * δq ≤ θ) ∧
      (∀ N : ℕ,
          bracketingNumber δq (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
          bracketingNumber (δq / 2) (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
          δq / (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ)))) ≤ θ) ∧
      ∀ (M : ℝ) (hM : 0 ≤ M),
        θ ≤ chainThreshold (nestedBracketPartition_of_finiteEntropy_clamped
              (G := localizedDifferenceClass F P δq) q₀ hδq M hM
              (hasFiniteBracketingCover_localized h_int δq hδq)
              hF_diff_meas) δq q₀ := by
  classical
  set G := localizedDifferenceClass F P δq with hG_def
  -- `M`-free finite bracketing numbers of the (un-truncated) localized class at the two
  -- relevant offset scales `(1/2)^0·δq = δq` and `(1/2)^1·δq`.
  have hcov0 : HasFiniteBracketingCover G ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) 2 P :=
    hasFiniteBracketingCover_localized h_int δq hδq q₀ le_rfl
  have hcov1 : HasFiniteBracketingCover G ((1 / 2 : ℝ) ^ ((q₀ + 1) - q₀) * δq) 2 P :=
    hasFiniteBracketingCover_localized h_int δq hδq (q₀ + 1) (Nat.le_succ q₀)
  set NB0 : ℕ := (bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) G 2 P).toNat with hNB0_def
  set NB1 : ℕ := (bracketingNumber ((1 / 2 : ℝ) ^ ((q₀ + 1) - q₀) * δq) G 2 P).toNat with hNB1_def
  have hbn0_lt : bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) G 2 P < ⊤ :=
    bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mpr hcov0
  have hbn1_lt : bracketingNumber ((1 / 2 : ℝ) ^ ((q₀ + 1) - q₀) * δq) G 2 P < ⊤ :=
    bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mpr hcov1
  set Nbound : ℕ := NB0 * NB1 with hNbound_def
  refine ⟨δq / (1 + Real.sqrt (Real.log (1 + (Nbound : ℝ)))), ?_,
    ⟨1 / (1 + Real.sqrt (Real.log (1 + (Nbound : ℝ)))), ?_, ?_⟩, ?_, ?_⟩
  · -- positivity of `θ`
    have hden : 0 < 1 + Real.sqrt (Real.log (1 + (Nbound : ℝ))) := by positivity
    positivity
  · -- positivity of the reciprocal factor `cθ = 1 / (1 + √log(1 + Nbound))`
    have hden : 0 < 1 + Real.sqrt (Real.log (1 + (Nbound : ℝ))) := by positivity
    positivity
  · -- `cθ * δq ≤ θ` (equality: `θ = δq / (1 + √log(1 + Nbound)) = cθ · δq`)
    exact le_of_eq (by ring)
  · -- **NEW**: for any common upper bound `N` on the two bracketing numbers,
    -- `δq / (1 + √log(1 + N²)) ≤ θ` (monotone: `Nbound = NB0·NB1 ≤ N·N`).
    intro N hN0 hN1
    have hNB0_le : NB0 ≤ N := by
      have hscale : (1 / 2 : ℝ) ^ (q₀ - q₀) * δq = δq := by
        rw [Nat.sub_self, pow_zero, one_mul]
      rw [hNB0_def, hscale]
      simpa using ENat.toNat_le_toNat hN0 (by simp)
    have hNB1_le : NB1 ≤ N := by
      have hscale : (1 / 2 : ℝ) ^ ((q₀ + 1) - q₀) * δq = δq / 2 := by
        rw [Nat.add_sub_cancel_left, pow_one]; ring
      rw [hNB1_def, hscale]
      simpa using ENat.toNat_le_toNat hN1 (by simp)
    have hNbound_le : Nbound ≤ N * N := by
      rw [hNbound_def]; exact Nat.mul_le_mul hNB0_le hNB1_le
    apply div_le_div_of_nonneg_left hδq.le (by positivity)
    have hle : (Nbound : ℝ) ≤ ((N * N : ℕ) : ℝ) := by exact_mod_cast hNbound_le
    have hlog : Real.log (1 + (Nbound : ℝ)) ≤ Real.log (1 + ((N * N : ℕ) : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have hsqrt := Real.sqrt_le_sqrt hlog
    linarith
  · intro M hM
    set B := nestedBracketPartition_of_finiteEntropy_clamped
      (G := G) q₀ hδq M hM (hasFiniteBracketingCover_localized h_int δq hδq)
      hF_diff_meas with hB_def
    -- `B.Nq(q₀+1) ≤ Nbound`, `M`-free.
    have hcc : ∀ p, q₀ ≤ p →
        (B.coverCard p : ℕ) ≤ (bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δq) G 2 P).toNat := by
      intro p hp
      have h1 : (B.coverCard p : ℕ∞)
          ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δq) (truncateClass G M) 2 P := by
        have := B.coverCard_le hp; simpa using this
      have h2 : bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δq) (truncateClass G M) 2 P
          ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δq) G 2 P :=
        bracketingNumber_truncateClass_le hM
      have h3 : (B.coverCard p : ℕ∞)
          ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δq) G 2 P := le_trans h1 h2
      have hne : bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δq) G 2 P ≠ ⊤ := by
        exact (bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mpr
          (hasFiniteBracketingCover_localized h_int δq hδq p hp)).ne
      have := ENat.toNat_le_toNat h3 hne
      simpa using this
    have hNq_le : (B.Nq (q₀ + 1) : ℕ) ≤ Nbound := by
      have hcard := B.card_le (Nat.le_succ q₀)
      have hIcc : (∏ p ∈ Finset.Icc q₀ (q₀ + 1), B.coverCard p)
          = B.coverCard q₀ * B.coverCard (q₀ + 1) := by
        rw [Finset.prod_Icc_succ_top (Nat.le_succ q₀), Finset.Icc_self, Finset.prod_singleton]
      rw [hIcc] at hcard
      have h0 := hcc q₀ le_rfl
      have h1 := hcc (q₀ + 1) (Nat.le_succ q₀)
      calc (B.Nq (q₀ + 1) : ℕ) ≤ B.coverCard q₀ * B.coverCard (q₀ + 1) := hcard
        _ ≤ NB0 * NB1 := by
            apply Nat.mul_le_mul
            · simpa [hNB0_def, Nat.sub_self] using h0
            · simpa [hNB1_def, Nat.add_sub_cancel] using h1
        _ = Nbound := rfl
    -- monotonicity of `chainThreshold` in the cover card.
    unfold chainThreshold
    rw [Nat.sub_self, pow_zero, one_mul]
    apply div_le_div_of_nonneg_left hδq.le
    · positivity
    · -- denominator monotone: `1 + √log(1 + Nq(q₀+1)) ≤ 1 + √log(1 + Nbound)`
      have hle : (B.Nq (q₀ + 1) : ℝ) ≤ (Nbound : ℝ) := by exact_mod_cast hNq_le
      have hlog : Real.log (1 + (B.Nq (q₀ + 1) : ℝ)) ≤ Real.log (1 + (Nbound : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      have hsqrt : Real.sqrt (Real.log (1 + (B.Nq (q₀ + 1) : ℝ)))
          ≤ Real.sqrt (Real.log (1 + (Nbound : ℝ))) := Real.sqrt_le_sqrt hlog
      linarith

/-- **`M`-free lower bound on the clamped partition's `globalThreshold`.** Sibling of
`localized_chainThreshold_lower_bound`: `globalThreshold (B(M)) δq = δq / (1 + √log(1 +
B(M).Nq q₀))` reads the truncated-class head-level cover card `B(M).Nq q₀`, which depends
on `M` but is bounded *above* by the `M`-free head bracketing number
`NB₀ := bracketingNumber (δq) (localizedDifferenceClass F P δq)`.  Hence
`globalThreshold (B(M)) δq ≥ θ' := δq / (1 + √log(1 + (NB₀ : ℝ)))`, an `M`-free positive
constant, for **every** clamp level `M ≥ 0`.  (Same `card_le` ⟹ `coverCard_le` ⟹
`bracketingNumber_truncateClass_le` chain as the `chainThreshold` sibling, applied at the
head level `q₀` where `Nq q₀ ≤ coverCard q₀ ≤ NB₀`.) -/
lemma localized_globalThreshold_lower_bound
    [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {δq : ℝ} (hδq : 0 < δq)
    (hF_diff_meas : ∀ h ∈ localizedDifferenceClass F P δq, Measurable h)
    {q₀ : ℕ} :
    ∃ θ : ℝ, 0 < θ ∧ (∃ cθ : ℝ, 0 < cθ ∧ cθ * δq ≤ θ) ∧
      (∀ N : ℕ,
          bracketingNumber δq (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
          δq / (1 + Real.sqrt (Real.log (1 + (N : ℝ)))) ≤ θ) ∧
      ∀ (M : ℝ) (hM : 0 ≤ M),
        θ ≤ globalThreshold (nestedBracketPartition_of_finiteEntropy_clamped
              (G := localizedDifferenceClass F P δq) q₀ hδq M hM
              (hasFiniteBracketingCover_localized h_int δq hδq)
              hF_diff_meas) δq := by
  classical
  set G := localizedDifferenceClass F P δq with hG_def
  have hcov0 : HasFiniteBracketingCover G ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) 2 P :=
    hasFiniteBracketingCover_localized h_int δq hδq q₀ le_rfl
  set NB0 : ℕ := (bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) G 2 P).toNat with hNB0_def
  refine ⟨δq / (1 + Real.sqrt (Real.log (1 + (NB0 : ℝ)))), ?_,
    ⟨1 / (1 + Real.sqrt (Real.log (1 + (NB0 : ℝ)))), ?_, ?_⟩, ?_, ?_⟩
  · have hden : 0 < 1 + Real.sqrt (Real.log (1 + (NB0 : ℝ))) := by positivity
    positivity
  · -- positivity of the reciprocal factor `cθ = 1 / (1 + √log(1 + NB0))`
    have hden : 0 < 1 + Real.sqrt (Real.log (1 + (NB0 : ℝ))) := by positivity
    positivity
  · -- `cθ * δq ≤ θ` (equality)
    exact le_of_eq (by ring)
  · -- **NEW**: for any upper bound `N` on the head bracketing number,
    -- `δq / (1 + √log(1 + N)) ≤ θ` (monotone: `NB0 ≤ N`).
    intro N hN0
    have hNB0_le : NB0 ≤ N := by
      have hscale : (1 / 2 : ℝ) ^ (q₀ - q₀) * δq = δq := by
        rw [Nat.sub_self, pow_zero, one_mul]
      rw [hNB0_def, hscale]
      simpa using ENat.toNat_le_toNat hN0 (by simp)
    apply div_le_div_of_nonneg_left hδq.le (by positivity)
    have hle : (NB0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNB0_le
    have hlog : Real.log (1 + (NB0 : ℝ)) ≤ Real.log (1 + (N : ℝ)) :=
      Real.log_le_log (by positivity) (by linarith)
    have hsqrt := Real.sqrt_le_sqrt hlog
    linarith
  · intro M hM
    set B := nestedBracketPartition_of_finiteEntropy_clamped
      (G := G) q₀ hδq M hM (hasFiniteBracketingCover_localized h_int δq hδq)
      hF_diff_meas with hB_def
    -- `B.Nq q₀ ≤ NB0`, `M`-free.
    have hcc0 : (B.coverCard q₀ : ℕ)
        ≤ (bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) G 2 P).toNat := by
      have h1 : (B.coverCard q₀ : ℕ∞)
          ≤ bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) (truncateClass G M) 2 P := by
        have := B.coverCard_le (le_rfl : q₀ ≤ q₀); simpa using this
      have h2 : bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) (truncateClass G M) 2 P
          ≤ bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) G 2 P :=
        bracketingNumber_truncateClass_le hM
      have hne : bracketingNumber ((1 / 2 : ℝ) ^ (q₀ - q₀) * δq) G 2 P ≠ ⊤ :=
        (bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mpr hcov0).ne
      have := ENat.toNat_le_toNat (le_trans h1 h2) hne
      simpa using this
    have hNq_le : (B.Nq q₀ : ℕ) ≤ NB0 := by
      have hcard := B.card_le (le_rfl : q₀ ≤ q₀)
      rw [Finset.Icc_self, Finset.prod_singleton] at hcard
      calc (B.Nq q₀ : ℕ) ≤ B.coverCard q₀ := hcard
        _ ≤ NB0 := by simpa [hNB0_def, Nat.sub_self] using hcc0
    -- monotonicity of `globalThreshold` in the cover card.
    unfold globalThreshold
    apply div_le_div_of_nonneg_left hδq.le
    · positivity
    · have hle : (B.Nq q₀ : ℝ) ≤ (NB0 : ℝ) := by exact_mod_cast hNq_le
      have hlog : Real.log (1 + (B.Nq q₀ : ℝ)) ≤ Real.log (1 + (NB0 : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      have hsqrt : Real.sqrt (Real.log (1 + (B.Nq q₀ : ℝ)))
          ≤ Real.sqrt (Real.log (1 + (NB0 : ℝ))) := Real.sqrt_le_sqrt hlog
      linarith

/-- **`hΔq0_ptwise` discharge for the clamped localized partition (vdV `A_{q₀} f = 1`).**
With clamp level `M := √n · chainThreshold B δq q₀ / 2`, the `Δ ≤ 2M` envelope bound
(`nestedBracketPartition_of_finiteEntropy_clamped_Δ_le`) gives exactly
`Δ_{q₀} i x ≤ √n · chainThreshold B δq q₀`. The genuine content (lifted) is that such an
`M` is well-defined despite `chainThreshold` reading `B.Nq (q₀+1)` (the truncated-class
cover card) — broken by the `M`-independent bracketing-number bound described in the
section docstring. -/
lemma localized_clamp_Δq0_discharge
    [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {δq : ℝ} (hδq : 0 < δq)
    (hF_diff_meas : ∀ h ∈ localizedDifferenceClass F P δq, Measurable h)
    {q₀ : ℕ}
    (M : ℝ) (hM : 0 ≤ M)
    (n : ℕ)
    -- the `M`-fixed-point inequality: `2M ≤ √n · chainThreshold B δq q₀` where `B` is the
    -- clamped partition built at `(M, hM)`. The genuine content (lifted) is that some
    -- positive `M` satisfies this despite `chainThreshold B` reading `B.Nq (q₀+1)` (an
    -- `M`-dependent cover card); broken by the `M`-independent bracketing-number bound.
    (hfix : 2 * M ≤ Real.sqrt n *
        chainThreshold (nestedBracketPartition_of_finiteEntropy_clamped
          (G := localizedDifferenceClass F P δq) q₀ hδq M hM
          (hasFiniteBracketingCover_localized h_int δq hδq)
          hF_diff_meas) δq q₀) :
    ∀ (i : Fin ((nestedBracketPartition_of_finiteEntropy_clamped
          (G := localizedDifferenceClass F P δq) q₀ hδq M hM
          (hasFiniteBracketingCover_localized h_int δq hδq)
          hF_diff_meas).Nq q₀))
        (x : Ω),
        (nestedBracketPartition_of_finiteEntropy_clamped
            (G := localizedDifferenceClass F P δq) q₀ hδq M hM
            (hasFiniteBracketingCover_localized h_int δq hδq)
            hF_diff_meas).Δ q₀ i x
          ≤ Real.sqrt n *
              chainThreshold (nestedBracketPartition_of_finiteEntropy_clamped
                (G := localizedDifferenceClass F P δq) q₀ hδq M hM
                (hasFiniteBracketingCover_localized h_int δq hδq)
                hF_diff_meas) δq q₀ := by
  -- `Δ_{q₀} i x ≤ 2M ≤ √n · chainThreshold B δq q₀` (the first via the clamp envelope
  -- bound, the second via the `M`-fixed-point inequality `hfix`).
  intro i x
  refine le_trans (nestedBracketPartition_of_finiteEntropy_clamped_Δ_le
    (G := localizedDifferenceClass F P δq) q₀ hδq M hM
    (hasFiniteBracketingCover_localized h_int δq hδq)
    hF_diff_meas le_rfl i x) hfix

/-- **Dyadic-series → `J_{[]}(δq, F)` for the clamped localized partition.** The
dyadic entropy series over the truncated localized class is bounded by `cJ · J_{[]}(δq, F)`
with `cJ = 4√2`, via the chain:

`∑' ... entropyIntegrand(truncate(localized)) ≤ 2·J(δq, truncate(localized))`
(`dyadic_sum_le_bracketingEntropyIntegral`)
`≤ 2·J(δq, localized)` (`bracketingEntropyIntegral_truncateClass_le`)
`≤ 2·J(δq, F − F)` (`bracketingEntropyIntegral_mono_class`, `localizedDifferenceClass_subset`)
`≤ 2·(2√2)·J(δq, F)` (`bracketingEntropyIntegral_diff_le_class`, vdV Lemma 19.31). -/
lemma localized_dyadic_to_J
    [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {δq : ℝ} (hδq : 0 < δq) (M : ℝ) (hM : 0 ≤ M) :
    ∃ cJ : ℝ, 0 < cJ ∧
      (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δq)
          * entropyIntegrand ((1/2 : ℝ)^q * δq)
              (truncateClass (localizedDifferenceClass F P δq) M) P)
        ≤ ENNReal.ofReal cJ * bracketingEntropyIntegral δq F P := by
  -- `hcover` for vdV Lemma 19.31, discharged from `h_int`.
  have hcover : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F (ε / 2) 2 P :=
    fun ε hε => hasFiniteBracketingCover_of_entropyIntegral_lt_top h_int (by positivity)
  refine ⟨4 * Real.sqrt 2, by positivity, ?_⟩
  -- The dyadic series over the truncated localized class is at most twice its entropy integral.
  refine (dyadic_sum_le_bracketingEntropyIntegral (F := truncateClass
      (localizedDifferenceClass F P δq) M) hδq).trans ?_
  -- Chain the three entropy-class comparisons.
  have h1 : bracketingEntropyIntegral δq (truncateClass (localizedDifferenceClass F P δq) M) P
      ≤ bracketingEntropyIntegral δq (localizedDifferenceClass F P δq) P :=
    bracketingEntropyIntegral_truncateClass_le hM
  have h2 : bracketingEntropyIntegral δq (localizedDifferenceClass F P δq) P
      ≤ bracketingEntropyIntegral δq (differenceClass F) P :=
    bracketingEntropyIntegral_mono_class localizedDifferenceClass_subset
  have h3 : bracketingEntropyIntegral δq (differenceClass F) P
      ≤ ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δq F P :=
    bracketingEntropyIntegral_diff_le_class hδq.le hcover
  -- `2 · J(truncate) ≤ 2 · (2√2) · J(F) = 4√2 · J(F)`.
  calc 2 * bracketingEntropyIntegral δq (truncateClass (localizedDifferenceClass F P δq) M) P
      ≤ 2 * (ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δq F P) := by
        gcongr; exact (h1.trans h2).trans h3
    _ = ENNReal.ofReal (4 * Real.sqrt 2) * bracketingEntropyIntegral δq F P := by
        rw [show ENNReal.ofReal (4 * Real.sqrt 2)
              = 2 * ENNReal.ofReal (2 * Real.sqrt 2) by
          rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring]
        ring

/-- **Reindexing the clamped sup as a sup over the truncated class.** For any
evaluator `z`, the supremum of `z (clampFn M h)` over `h ∈ G` equals the supremum of
`z g'` over the truncated class `truncateClass G M = clampFn M '' G`. Pure reindex of
the `iSup` along the clamp image. -/
lemma supNormOver_clamp_image_eq {G : Set (Ω → ℝ)} (M : ℝ) (z : (Ω → ℝ) → ℝ) :
    supNormOver G (fun h => z (clampFn M h))
      = supNormOver (truncateClass G M) z := by
  unfold supNormOver truncateClass
  apply le_antisymm
  · refine iSup₂_le fun h hh => ?_
    exact le_iSup₂_of_le (clampFn M h) ⟨h, hh, rfl⟩ le_rfl
  · refine iSup₂_le fun g' hg' => ?_
    obtain ⟨h, hh, rfl⟩ := hg'
    exact le_iSup₂_of_le h hh le_rfl


/-- **F→F̃ lift: bound the localized sup by the clamped sup plus the truncation excess.**
For the localized difference class `G := localizedDifferenceClass F P δq` with envelope
`Φ` of `differenceClass F` (hence of `G ⊆ differenceClass F`) and clamp level `Mc ≥ 0`,
the integrated sup of the empirical process over `G` is bounded by the integrated sup over
`truncateClass G Mc` plus the `√n`-truncation excess at threshold `Mc`:

`∫⁻ supNormOver G 𝔾ₙ ≤ ∫⁻ supNormOver (truncate G Mc) 𝔾ₙ + 4√n·∫⁻ |Φ|·1{Mc<|Φ|}`.

Pointwise per `ξ`: `𝔾ₙ h = 𝔾ₙ(clampFn Mc h) + 𝔾ₙ(h − clampFn Mc h)` (`empiricalProcess_add`,
both pieces integrable since `|·| ≤ Φ ∈ L²(P) ⊆ L¹(P)`); `supNormOver` is subadditive; the
clamped sup reindexes to `truncateClass G Mc` (`supNormOver_clamp_image_eq`); the excess
class `{h − clampFn Mc h : h ∈ G}` is pointwise dominated by `Ψ = |Φ|·1{Mc<|Φ|}` (the clamp
is the identity on `{|h| ≤ Mc}` and `|h − clampFn Mc h| ≤ |h| ≤ Φ` on `{|h| > Mc} ⊆ {Φ > Mc}`),
so the excess integral is closed by `supNormProcess_dominated_integral_bound`. -/
lemma localized_supNorm_lift
    [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {δq : ℝ}
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (hΦ_env : IsEnvelope (differenceClass F) Φ)
    (hF_diff_meas : ∀ h ∈ localizedDifferenceClass F P δq, Measurable h)
    (hΦ_int : Integrable Φ P)
    (Mc : ℝ) (hMc : 0 ≤ Mc)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
          (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
      ≤ (∫⁻ ξ, supNormOver (truncateClass (localizedDifferenceClass F P δq) Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
        + 4 * ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ x, ENNReal.ofReal (|Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x) ∂P := by
  classical
  set G := localizedDifferenceClass F P δq with hG_def
  -- envelope of `G` (subset of difference class)
  have hΦ_envG : IsEnvelope G Φ := hΦ_env.mono localizedDifferenceClass_subset
  -- the excess class and its envelope `Ψ`
  set Ψ : Ω → ℝ := fun x => |Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x with hΨ_def
  set 𝒢 : Set (Ω → ℝ) := {g | ∃ h ∈ G, g = fun x => h x - clampFn Mc h x} with h𝒢_def
  have hΦ_abs_meas : Measurable (fun x => |Φ x|) := hΦ_meas.norm
  have hset_meas : MeasurableSet {y | Mc < |Φ y|} :=
    hΦ_abs_meas measurableSet_Ioi
  have hΨ_meas : Measurable Ψ := by
    refine hΦ_meas.norm.mul ?_
    exact measurable_const.indicator hset_meas
  have hΨ_nn : ∀ x, 0 ≤ Ψ x := by
    intro x
    refine mul_nonneg (abs_nonneg _) ?_
    by_cases hx : x ∈ {y | Mc < |Φ y|} <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  -- domination of every excess member by `Ψ`
  have hdom : ∀ g ∈ 𝒢, ∀ x, |g x| ≤ Ψ x := by
    rintro g ⟨h, hhG, rfl⟩ x
    have hhΦ : |h x| ≤ Φ x := hΦ_envG h hhG x
    show |h x - clampFn Mc h x| ≤ |Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x
    by_cases hx : x ∈ {y | Mc < |Φ y|}
    · -- on `{Mc < |Φ|}`: `|h − clamp h| ≤ |h| ≤ |Φ| = |Φ|·1`
      rw [Set.indicator_of_mem hx]
      simp only [Pi.one_apply, mul_one]
      have h1 : |h x - clampFn Mc h x| ≤ |h x| := by
        unfold clampFn clampReal
        rcases le_total (h x) Mc with hle | hle <;>
          rcases le_total (-Mc) (h x) with hle2 | hle2 <;>
          rw [max_def, min_def] <;> split_ifs <;>
          rcases abs_cases (h x) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
          rw [e2] <;>
          rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact le_trans h1 (le_trans hhΦ (le_abs_self _))
    · -- off `{Mc < |Φ|}`: `|h| ≤ |Φ| ≤ Mc`, so clamp is identity and excess is 0
      rw [Set.indicator_of_notMem hx]
      simp only [mul_zero]
      have hΦle : |Φ x| ≤ Mc := not_lt.mp (by simpa using hx)
      have hhle : |h x| ≤ Mc := le_trans (le_trans hhΦ (le_abs_self _)) hΦle
      have hcl : clampFn Mc h x = h x := by unfold clampFn; exact clampReal_of_mem hhle
      rw [hcl]; simp
  -- integrability of `Ψ`
  have hΨ_int : ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P = ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := rfl
  -- integrability of `Φ`-dominated functions (members of `G`, their clamps, the excess)
  have hint_of_dom : ∀ {g : Ω → ℝ}, Measurable g → (∀ x, |g x| ≤ Φ x) → Integrable g P := by
    intro g hg_meas hg_dom
    refine Integrable.mono' hΦ_int hg_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hg_dom x)
  -- per-ξ split: bound `supNormOver G 𝔾ₙ` by clamp-sup + excess-sup
  have h_pt : ∀ ξ : Ξ,
      supNormOver G (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
        ≤ supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
          + supNormOver 𝒢
              (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
    intro ξ
    refine iSup₂_le fun h hhG => ?_
    -- `h` is measurable and `Φ`-dominated; so is `clampFn Mc h`; so the split is valid.
    have hh_meas : Measurable h := hF_diff_meas h hhG
    have hh_dom : ∀ x, |h x| ≤ Φ x := hΦ_envG h hhG
    have hclamp_meas : Measurable (clampFn Mc h) := clampFn_measurable hh_meas
    have hclamp_dom : ∀ x, |clampFn Mc h x| ≤ Φ x :=
      fun x => le_trans (abs_clampReal_le Mc hMc (h x)) (hh_dom x)
    have hh_int : Integrable h P := hint_of_dom hh_meas hh_dom
    have hclamp_int : Integrable (clampFn Mc h) P := hint_of_dom hclamp_meas hclamp_dom
    -- `𝔾ₙ h = 𝔾ₙ(clamp h) + 𝔾ₙ(excess h)`
    have hsplit : empiricalProcess P n (fun i : Fin n => X i.val ξ) h
        = empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)
          + empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun x => h x - clampFn Mc h x) := by
      rw [← empiricalProcess_add P n _ (clampFn Mc h) (fun x => h x - clampFn Mc h x)
        hclamp_int (hh_int.sub hclamp_int)]
      congr 1; funext x; ring
    simp only []
    rw [hsplit]
    calc ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)
            + empiricalProcess P n (fun i : Fin n => X i.val ξ) (fun x => h x - clampFn Mc h x)|
        ≤ ENNReal.ofReal
              (|empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)|
                + |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun x => h x - clampFn Mc h x)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)|
            + ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => h x - clampFn Mc h x)| := ENNReal.ofReal_add_le
      _ ≤ supNormOver (truncateClass G Mc)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
            + supNormOver 𝒢
                (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
        refine add_le_add ?_ ?_
        · exact le_supNormOver (z := fun h => empiricalProcess P n
            (fun i : Fin n => X i.val ξ) h) ⟨h, hhG, rfl⟩
        · exact le_supNormOver (z := fun g => empiricalProcess P n
            (fun i : Fin n => X i.val ξ) g) ⟨h, hhG, rfl⟩
  -- Measurability-free split: dominate the (non-measurable) excess sup `supNormOver 𝒢`
  -- by the EXPLICIT measurable process `Bproc ξ = √n·(empAvg Ψ ξ + ∫⁻Ψ)`
  -- (`supNormProcess_dominated_pointwise_bound`), then split via `lintegral_add_right'`
  -- (which needs only the measurable right summand `Bproc`; the clamped-class supremum
  -- need not be measurable).
  set T : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P with hT_def
  set Bproc : Ξ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Real.sqrt n) *
      (ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) + T) with hBproc_def
  have hBproc_meas : Measurable Bproc := by
    refine Measurable.const_mul ?_ _
    refine Measurable.fun_add ?_ measurable_const
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΨ_meas.comp (hX_meas i.val)
  have h_excess_le : ∀ ξ : Ξ, supNormOver 𝒢
        (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) ≤ Bproc ξ := by
    intro ξ
    exact supNormProcess_dominated_pointwise_bound (P := P) 𝒢 Ψ hdom n hn ξ
  -- `∫⁻ Bproc ≤ 4√n·∫⁻ Ψ` (IdentDistrib-Fubini; same as the integral lemma's tail).
  have hΨ_ofReal_meas : Measurable (fun x => ENNReal.ofReal (Ψ x)) := hΨ_meas.ennreal_ofReal
  have hΨ_meas_avg : AEMeasurable
      (fun ξ : Ξ => ENNReal.ofReal
        (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))) μ := by
    refine Measurable.aemeasurable ?_
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΨ_meas.comp (hX_meas i.val)
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have h_emp_to_P : ∫⁻ ξ, ENNReal.ofReal
      (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ ≤ T := by
    have h_pt_le : ∀ ξ : Ξ,
        ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))
        ≤ ((n : ℝ≥0∞))⁻¹ * ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) := by
      intro ξ
      unfold empiricalAvg
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have hn_inv_eq : ENNReal.ofReal ((n : ℝ)⁻¹) = ((n : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
      rw [hn_inv_eq]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hΨ_nn _)]
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hn_pos_nat)
    have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
    calc ∫⁻ ξ, ENNReal.ofReal
            (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ
        ≤ ∫⁻ ξ, ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ :=
          MeasureTheory.lintegral_mono h_pt_le
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∫⁻ ξ, ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ hinv_ne_top]
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ∫⁻ ξ, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ := by
          congr 1
          rw [MeasureTheory.lintegral_finset_sum Finset.univ]
          intro i _
          exact hΨ_ofReal_meas.comp (hX_meas i.val)
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ _i : Fin n, ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have h_id : (μ.map (X i.val)) = P := by
            rw [← hX_law]; exact (hX_idem i.val).map_eq
          rw [← h_id]
          exact (MeasureTheory.lintegral_map hΨ_ofReal_meas (hX_meas i.val)).symm
      _ = ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞)) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      _ = T := by rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul, hT_def]
  have hBproc_int_le : ∫⁻ ξ, Bproc ξ ∂μ
      ≤ 4 * ENNReal.ofReal (Real.sqrt n) * T := by
    rw [hBproc_def]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      MeasureTheory.lintegral_add_left' hΨ_meas_avg,
      MeasureTheory.lintegral_const, measure_univ, mul_one]
    calc ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ξ, ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ + T)
        ≤ ENNReal.ofReal (Real.sqrt n) * (T + T) :=
          mul_le_mul_of_nonneg_left (add_le_add h_emp_to_P le_rfl) (zero_le)
      _ = 2 * ENNReal.ofReal (Real.sqrt n) * T := by ring
      _ ≤ 4 * ENNReal.ofReal (Real.sqrt n) * T := by gcongr; norm_num
  -- assemble the split
  calc ∫⁻ ξ, supNormOver G
          (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
      ≤ ∫⁻ ξ, (supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
          + Bproc ξ) ∂μ := by
        refine MeasureTheory.lintegral_mono (fun ξ => ?_)
        exact le_trans (h_pt ξ) (add_le_add le_rfl (h_excess_le ξ))
    _ = (∫⁻ ξ, supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
        + ∫⁻ ξ, Bproc ξ ∂μ :=
        MeasureTheory.lintegral_add_right' _ hBproc_meas.aemeasurable
    _ ≤ (∫⁻ ξ, supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
        + 4 * ENNReal.ofReal (Real.sqrt n) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
        have := hBproc_int_le
        rw [hT_def] at this
        gcongr

/-- **Per-scale localized chaining construction.**
For fixed `Φ, δq, n`, the clamped-localized construction produces a clamp level
`M ≥ 0` and the localized bound with constant `c₀·cJ + 4·c₀`.

* **M-fixed-point**: a clamp level `Mc = √n·M` with
  `2·Mc ≤ √n·chainThreshold (B(Mc)) δq q₀` (so `localized_clamp_Δq0_discharge` fires)
  AND `Mc ≤ √n·globalThreshold (B(Mc)) δq` (so the `globalThreshold` tail is bounded
  into the conclusion's `√n·M = Mc` tail).  Self-referential because `chainThreshold` /
  `globalThreshold` read `B(Mc)`'s cover cardinalities. Here
  `chainThreshold B δq q₀ = δq / (1 + √log(1 + B.Nq(q₀+1)))` and
  `B(Mc).Nq(q₀+1) = coverCard q₀ · coverCard (q₀+1) ≤ N₀²` where
  `N₀ := bracketingNumber ((1/2)^0·δq) (differenceClass F) 2 P` is **`Mc`-free** (via
  `B.coverCard_le` + `bracketingNumber_truncateClass_le` + `localizedDifferenceClass_subset`-
  monotonicity, since the clamped cover of `truncateClass G Mc` has card
  `≤ bracketingNumber (truncateClass G Mc) ≤ bracketingNumber G ≤ bracketingNumber (F−F)`).
  Hence `chainThreshold (B(Mc)) ≥ θ := δq / (1 + √log(1 + N₀²))`, `Mc`-free; choosing
  `Mc := √n·θ/2` gives `2·Mc = √n·θ ≤ √n·chainThreshold (B(Mc))` and the `globalThreshold`
  bound analogously (`globalThreshold` reads `Nq q₀ ≤ N₀`, so `globalThreshold ≥ θ' ≥ θ/2`
  for a suitable `Mc`-free `θ'`).
* **Clamped-class measurability** follows from measurability of `F`, by taking
  differences and applying the measurable clamp.
* **δq ≤ 1/4**: in this localization regime the dyadic `q₀`-window always exists,
  and the construction returns the positive
  `M = min(θ/2, θ') > 0`.

The proof combines the estimate over `truncateClass`, `localized_supNorm_lift`,
`localized_dyadic_to_J`, and the two tail bounds. -/
lemma localized_core_construction
    [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (c₀ : ℝ) (hc₀ : 1 ≤ c₀)
    -- the chaining bound, uniform over the class, base level, and scale (applied to
    -- `truncateClass (localized) Mc` with the freshly-chosen `q₀(δq)` and `C = δq`)
    (hengine : ∀ (F' : Set (Ω → ℝ)) (q₀' : ℕ) (C' : ℝ)
        (B : NestedBracketPartition F' P q₀' C')
        (_hπ_meas : ∀ {q : ℕ}, q₀' ≤ q → ∀ i, Measurable (B.π q i))
        (_hF'_ne : F'.Nonempty) (_hF'_meas : ∀ f ∈ F', Measurable f),
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope F' Φ → MemLp Φ 2 P →
        ∀ {δ : ℝ}, 0 < δ → C' = δ →
          (∀ f ∈ F', eLpNorm f 2 P ≤ ENNReal.ofReal δ) →
          (4 * δ ≤ (1 / 2 : ℝ) ^ q₀' ∧ (1 / 2 : ℝ) ^ q₀' ≤ 8 * δ) →
          ∀ (n : ℕ), 1 ≤ n →
            (∀ (i : Fin (B.Nq q₀')) (x : Ω),
                B.Δ q₀' i x ≤ Real.sqrt n * chainThreshold B δ q₀') →
            ∫⁻ ξ, supNormOver F'
                  (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
              ≤ ENNReal.ofReal c₀
                  * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                      * entropyIntegrand ((1/2 : ℝ)^q * δ) F' P)
                + ENNReal.ofReal c₀ *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * globalThreshold B δ < |Φ x|}
                            1 ω ∂P)) :
    ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
      ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
        ∃ M : ℝ, 0 < M ∧ (∃ cM : ℝ, 0 < cM ∧ cM * δq ≤ M) ∧
        (∀ N : ℕ,
            bracketingNumber δq (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
            bracketingNumber (δq / 2) (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
            min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ))))))
                (1 / (1 + Real.sqrt (Real.log (1 + (N : ℝ))))) * δq ≤ M) ∧
        ∀ (n : ℕ), 1 ≤ n →
        ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
          ≤ ENNReal.ofReal (c₀ * (4 * Real.sqrt 2) + 4 * c₀)
              * bracketingEntropyIntegral δq F P
            + ENNReal.ofReal (c₀ * (4 * Real.sqrt 2) + 4 * c₀)
                * (ENNReal.ofReal (Real.sqrt n)
                * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                    * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P) := by
  classical
  intro Φ hΦ_meas hΦ_env hΦ_L2 δq hδq hδq4
  set C : ℝ := c₀ * (4 * Real.sqrt 2) + 4 * c₀ with hC_def
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le one_pos hc₀
  have hC_pos : 0 < C := by rw [hC_def]; positivity
  -- envelope `Φ` of the localized class and its integrability.
  set G := localizedDifferenceClass F P δq with hG_def
  have hΦ_envG : IsEnvelope G Φ := hΦ_env.mono localizedDifferenceClass_subset
  have hΦ_int : Integrable Φ P := hΦ_L2.integrable (by norm_num)
  -- members of `G` are measurable (`f − g`, `f, g ∈ F`).
  have hF_diff_meas : ∀ h ∈ G, Measurable h := by
    rintro h ⟨f, hf, g, hg, rfl, _⟩
    exact (hF_meas f hf).sub (hF_meas g hg)
  -- The uniform clamp level `M` is chosen **outside** the `∀ n` (independent of `n`); in
  -- the chaining regime it is the `M`-free positive `θ/2` (`localized_chainThreshold_lower_bound`),
  -- so the per-`n` clamp `Mc := √n·M` makes `2·Mc = √n·θ ≤ √n·chainThreshold` self-consistently.
  -- The hypothesis `δq ≤ 1/4` ensures that the chaining regime produces the
  -- positive clamp level `M = min(θ/2, θ')`.
  · -- main chaining branch (`δq ≤ 1/4`)
    -- vdV's dyadic window `q₀` with `4δq ≤ (1/2)^{q₀} ≤ 8δq` (p.287).
    obtain ⟨q₀, hq₀⟩ := exists_q0_window hδq hδq4
    -- `M`-free positive lower bounds on the two thresholds of the clamped partition.
    obtain ⟨θ, hθ_pos, ⟨cθ, hcθ_pos, hcθ_le⟩, hθ_Nbd, hθ_le⟩ :=
      localized_chainThreshold_lower_bound (F := F) h_int hδq hF_diff_meas (q₀ := q₀)
    obtain ⟨θ', hθ'_pos, ⟨cθ', hcθ'_pos, hcθ'_le⟩, hθ'_Nbd, hθ'_le⟩ :=
      localized_globalThreshold_lower_bound (F := F) h_int hδq hF_diff_meas (q₀ := q₀)
    -- Uniform clamp level: `M ≤ θ/2` and `M ≤ θ'`.
    set M : ℝ := min (θ / 2) θ' with hM_def
    have hM_pos : 0 < M := lt_min (by positivity) hθ'_pos
    have hM_nonneg : 0 ≤ M := hM_pos.le
    have hM_le_θ2 : M ≤ θ / 2 := min_le_left _ _
    have hM_le_θ' : M ≤ θ' := min_le_right _ _
    -- Quantitative lower bound `cM · δq ≤ M`: since `θ = cθ · δq` and `θ' = cθ' · δq`
    -- (`cθ, cθ'` the reciprocal regularizer factors `1/(1+√log(1+N))` from the threshold
    -- lower bounds), `M = min(θ/2, θ') ≥ min(cθ/2, cθ') · δq`.  `cM := min(cθ/2, cθ') > 0`.
    -- (`cM` is `δq`-dependent — the bracketing counts `N` are of the `δq`-localized class.)
    have hcM_pos : 0 < min (cθ / 2) cθ' := lt_min (div_pos hcθ_pos (by norm_num)) hcθ'_pos
    have hcM_le : min (cθ / 2) cθ' * δq ≤ M := by
      rw [hM_def]
      apply le_min
      · calc min (cθ / 2) cθ' * δq
            ≤ cθ / 2 * δq := mul_le_mul_of_nonneg_right (min_le_left _ _) hδq.le
          _ = cθ * δq / 2 := by ring
          _ ≤ θ / 2 := by linarith [hcθ_le]
      · calc min (cθ / 2) cθ' * δq
            ≤ cθ' * δq := mul_le_mul_of_nonneg_right (min_le_right _ _) hδq.le
          _ ≤ θ' := hcθ'_le
    -- `G` is nonempty (`0 = f − f` has `L²`-radius `0 ≤ δq`).
    have hG_ne : G.Nonempty := by
      obtain ⟨f, hf⟩ := hF_ne
      refine ⟨fun x => f x - f x, ?_⟩
      refine ⟨f, hf, f, hf, rfl, ?_⟩
      simp only [sub_self]
      rw [show (fun _ : Ω => (0 : ℝ)) = (0 : Ω → ℝ) from rfl, eLpNorm_zero]
      exact zero_le
    -- The two localized-difference bracketing numbers give an explicit
    -- lower bound on `M` in terms of `δq`.
    have hM_Nbd : ∀ N : ℕ,
        bracketingNumber δq (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
        bracketingNumber (δq / 2) (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
        min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ))))))
            (1 / (1 + Real.sqrt (Real.log (1 + (N : ℝ))))) * δq ≤ M := by
      intro N hN0 hN1
      have hb1 := hθ_Nbd N hN0 hN1
      have hb2 := hθ'_Nbd N hN0
      rw [hM_def]
      apply le_min
      · calc min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ))))))
                (1 / (1 + Real.sqrt (Real.log (1 + (N : ℝ))))) * δq
            ≤ 1 / (2 * (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ))))) * δq :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hδq.le
          _ = δq / (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ)))) / 2 := by
              rw [div_div]; ring
          _ ≤ θ / 2 := by linarith [hb1]
      · calc min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ))))))
                (1 / (1 + Real.sqrt (Real.log (1 + (N : ℝ))))) * δq
            ≤ 1 / (1 + Real.sqrt (Real.log (1 + (N : ℝ)))) * δq :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hδq.le
          _ = δq / (1 + Real.sqrt (Real.log (1 + (N : ℝ)))) := by ring
          _ ≤ θ' := hb2
    refine ⟨M, hM_pos, ⟨min (cθ / 2) cθ', hcM_pos, hcM_le⟩, hM_Nbd, fun n hn => ?_⟩
    -- per-`n` clamp level `Mc := √n·M`.
    have hsn_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hn1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
    set Mc : ℝ := Real.sqrt n * M with hMc_def
    have hMc_nonneg : 0 ≤ Mc := mul_nonneg hsn_nonneg hM_nonneg
    -- Let `F' := truncateClass G Mc` before defining `B`, so the definitional
    -- link to the constructor survives — `set` on `B` would otherwise re-abstract this).
    set F' : Set (Ω → ℝ) := truncateClass G Mc with hF'_def
    -- the clamped partition over the truncated localized class.
    set B := nestedBracketPartition_of_finiteEntropy_clamped
      (G := G) q₀ hδq Mc hMc_nonneg (hasFiniteBracketingCover_localized h_int δq hδq)
      hF_diff_meas with hB_def
    -- `F'` is nonempty, measurable, `Φ`-enveloped, and `L²`-bounded at scale `δq`.
    have hF'_ne : F'.Nonempty := by
      obtain ⟨g, hg⟩ := hG_ne
      exact ⟨clampFn Mc g, g, hg, rfl⟩
    have hF'_meas : ∀ f ∈ F', Measurable f := by
      rintro _ ⟨g, hg, rfl⟩; exact clampFn_measurable (hF_diff_meas g hg)
    have hΦ_envF' : IsEnvelope F' Φ := by
      rintro _ ⟨g, hg, rfl⟩ x
      exact (abs_clampReal_le Mc hMc_nonneg (g x)).trans (hΦ_envG g hg x)
    have hF'_L2 : ∀ f ∈ F', eLpNorm f 2 P ≤ ENNReal.ofReal δq := by
      rintro _ ⟨g, hg, rfl⟩
      refine le_trans (eLpNorm_mono (fun x => ?_)) (localizedDifferenceClass_hF_L2 hg)
      simpa [clampFn, Real.norm_eq_abs] using abs_clampReal_le Mc hMc_nonneg (g x)
    -- Measurability of the partition representatives.
    have hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i) :=
      fun {q} hq i => B.π_meas hq i
    -- discharge `hΔq0_ptwise` via the clamp envelope `Δ ≤ 2Mc` and the fixed-point
    -- inequality `2Mc = 2√n·M ≤ √n·θ ≤ √n·chainThreshold(B)`.
    have hfix : 2 * Mc ≤ Real.sqrt n * chainThreshold B δq q₀ := by
      have h1 : θ ≤ chainThreshold B δq q₀ := by
        rw [hB_def]; exact hθ_le Mc hMc_nonneg
      calc 2 * Mc = Real.sqrt n * (2 * M) := by rw [hMc_def]; ring
        _ ≤ Real.sqrt n * θ := by
            apply mul_le_mul_of_nonneg_left _ hsn_nonneg; linarith [hM_le_θ2]
        _ ≤ Real.sqrt n * chainThreshold B δq q₀ :=
            mul_le_mul_of_nonneg_left h1 hsn_nonneg
    have hΔq0 : ∀ (i : Fin (B.Nq q₀)) (x : Ω),
        B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δq q₀ := by
      rw [hB_def]
      exact localized_clamp_Δq0_discharge (F := F) h_int hδq hF_diff_meas
        (q₀ := q₀) Mc hMc_nonneg n hfix
    -- Apply the uniform chaining bound to `F'` at scale `δq`.
    have heng := hengine F' q₀ δq B hπ_meas hF'_ne hF'_meas Φ hΦ_meas hΦ_envF' hΦ_L2
      hδq rfl hF'_L2 hq₀ n hn hΔq0
    -- the `F → F̃` lift: localized sup ≤ clamped sup + truncation excess at `Mc`.
    have hlift := localized_supNorm_lift (F := F) hX_meas hX_idem hX_law
      (δq := δq) Φ hΦ_meas hΦ_env hF_diff_meas hΦ_int Mc hMc_nonneg n hn
    -- dyadic series over `F'` ≤ `4√2 · J(δq, F)` (explicit constant via `localized_dyadic_to_J`'s
    -- entropy chain; inlined so the constant `4√2` is exposed for the constant comparison below).
    have hdyadic : (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δq)
          * entropyIntegrand ((1/2 : ℝ)^q * δq) F' P)
        ≤ ENNReal.ofReal (4 * Real.sqrt 2) * bracketingEntropyIntegral δq F P := by
      have hcover : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F (ε / 2) 2 P :=
        fun ε hε => hasFiniteBracketingCover_of_entropyIntegral_lt_top h_int (by positivity)
      refine (dyadic_sum_le_bracketingEntropyIntegral (F := F') hδq).trans ?_
      have h1 : bracketingEntropyIntegral δq F' P
          ≤ bracketingEntropyIntegral δq (localizedDifferenceClass F P δq) P :=
        bracketingEntropyIntegral_truncateClass_le hMc_nonneg
      have h2 : bracketingEntropyIntegral δq (localizedDifferenceClass F P δq) P
          ≤ bracketingEntropyIntegral δq (differenceClass F) P :=
        bracketingEntropyIntegral_mono_class localizedDifferenceClass_subset
      have h3 : bracketingEntropyIntegral δq (differenceClass F) P
          ≤ ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δq F P :=
        bracketingEntropyIntegral_diff_le_class hδq.le hcover
      calc 2 * bracketingEntropyIntegral δq F' P
          ≤ 2 * (ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δq F P) := by
            gcongr; exact (h1.trans h2).trans h3
        _ = ENNReal.ofReal (4 * Real.sqrt 2) * bracketingEntropyIntegral δq F P := by
            rw [show ENNReal.ofReal (4 * Real.sqrt 2)
                  = 2 * ENNReal.ofReal (2 * Real.sqrt 2) by
              rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num)]
              congr 1; ring]
            ring
    -- Abbreviations for the concluding estimate.
    set J : ℝ≥0∞ := bracketingEntropyIntegral δq F P with hJ_def
    set sn : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt n) with hsn_def
    set Tail : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal |Φ ω|
        * Set.indicator {x | Mc < |Φ x|} 1 ω ∂P with hTail_def
    -- the truncation-excess integral equals the conclusion tail `Tail` (indicator pull-out).
    have hexc_eq : ∫⁻ x, ENNReal.ofReal (|Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x) ∂P
        = Tail := by
      rw [hTail_def]
      refine lintegral_congr (fun x => ?_)
      by_cases hx : x ∈ {y | Mc < |Φ y|}
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    -- The tail at threshold `√n·globalThreshold B` is bounded by `Tail` at threshold `Mc`,
    -- since `Mc = √n·M ≤ √n·θ' ≤ √n·globalThreshold B` ⟹ `{√n·gt<|Φ|} ⊆ {Mc<|Φ|}`.
    have hMc_le_gt : Mc ≤ Real.sqrt n * globalThreshold B δq := by
      have hg : θ' ≤ globalThreshold B δq := by rw [hB_def]; exact hθ'_le Mc hMc_nonneg
      calc Mc = Real.sqrt n * M := hMc_def
        _ ≤ Real.sqrt n * θ' := mul_le_mul_of_nonneg_left hM_le_θ' hsn_nonneg
        _ ≤ Real.sqrt n * globalThreshold B δq := mul_le_mul_of_nonneg_left hg hsn_nonneg
    have hEngTail_le : ∫⁻ ω, ENNReal.ofReal |Φ ω|
          * Set.indicator {x | Real.sqrt n * globalThreshold B δq < |Φ x|} 1 ω ∂P ≤ Tail := by
      rw [hTail_def]
      refine lintegral_mono (fun ω => ?_)
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      refine Set.indicator_le_indicator_of_subset ?_ (fun _ => zero_le) ω
      intro x hx
      exact lt_of_le_of_lt hMc_le_gt hx
    -- assemble: `LHS_G ≤ LHS_F' + 4·sn·Tail ≤ (c₀·dyadic + c₀·sn·EngTail) + 4·sn·Tail`
    --                  ≤ c₀·(4√2)·J + c₀·sn·Tail + 4·sn·Tail ≤ C·J + C·sn·Tail`.
    calc ∫⁻ ξ, supNormOver G
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
        ≤ (∫⁻ ξ, supNormOver F'
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
            + 4 * sn * Tail := by
          rw [hsn_def, ← hexc_eq]; exact hlift
      _ ≤ (ENNReal.ofReal c₀ * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δq)
                * entropyIntegrand ((1/2 : ℝ)^q * δq) F' P)
            + ENNReal.ofReal c₀ * (sn * ∫⁻ ω, ENNReal.ofReal |Φ ω|
                * Set.indicator {x | Real.sqrt n * globalThreshold B δq < |Φ x|} 1 ω ∂P))
            + 4 * sn * Tail := by
          rw [hsn_def]; exact add_le_add heng le_rfl
      _ ≤ (ENNReal.ofReal c₀ * (ENNReal.ofReal (4 * Real.sqrt 2) * J)
            + ENNReal.ofReal c₀ * (sn * Tail)) + 4 * sn * Tail := by
          refine add_le_add (add_le_add ?_ ?_) le_rfl
          · exact mul_le_mul_of_nonneg_left hdyadic (zero_le)
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hEngTail_le (zero_le)) (zero_le)
      _ = ENNReal.ofReal (c₀ * (4 * Real.sqrt 2)) * J
            + (ENNReal.ofReal c₀ + 4) * (sn * Tail) := by
          rw [ENNReal.ofReal_mul hc₀_pos.le]; ring
      _ ≤ ENNReal.ofReal C * J + ENNReal.ofReal C * (sn * Tail) := by
          have hCfact : ENNReal.ofReal C
              = ENNReal.ofReal (c₀ * (4 * Real.sqrt 2)) + ENNReal.ofReal (4 * c₀) := by
            rw [hC_def, ENNReal.ofReal_add (by positivity) (by positivity)]
          -- `√2 ≥ 1` so `c₀·4√2 ≤ C`; and `c₀ ≥ 1` so `4 ≤ 4c₀ ≤ C`.
          have hsqrt2_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
            rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
          refine add_le_add ?_ ?_
          · gcongr
            rw [hC_def]; nlinarith [hc₀, hsqrt2_ge]
          · rw [hCfact]
            refine mul_le_mul_of_nonneg_right ?_ (zero_le)
            -- `ofReal c₀ + 4 ≤ ofReal(c₀·4√2) + ofReal(4c₀)`
            have hh1 : ENNReal.ofReal c₀ ≤ ENNReal.ofReal (c₀ * (4 * Real.sqrt 2)) := by
              apply ENNReal.ofReal_le_ofReal
              nlinarith [hc₀, hsqrt2_ge]
            have hh2 : (4 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * c₀) := by
              rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp]
              exact ENNReal.ofReal_le_ofReal (by nlinarith [hc₀])
            exact add_le_add hh1 hh2

lemma localizedChainBound_pos_core
    [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
      ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
        ∃ M : ℝ, 0 < M ∧ (∃ cM : ℝ, 0 < cM ∧ cM * δq ≤ M) ∧
        (∀ N : ℕ,
            bracketingNumber δq (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
            bracketingNumber (δq / 2) (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
            min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ))))))
                (1 / (1 + Real.sqrt (Real.log (1 + (N : ℝ))))) * δq ≤ M) ∧
        ∀ (n : ℕ), 1 ≤ n →
        ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
          ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
            + ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                    * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P) := by
  -- Use the uniform chaining constant `c₀`, independent of `F`, `q₀`, and
  -- `C`, so a single `c` serves every scale `δq`.
  obtain ⟨c₀, hc₀_pos, hengine⟩ :=
    chain_supnorm_dyadic_bound_uniform (P := P) (μ := μ)
      hX_meas hX_iindep hX_idem hX_law
  -- The localized constant combines `c₀` with the dyadic-to-integral factor
  -- `cJ = 4√2` (`localized_dyadic_to_J`) and the F→F̃ excess factor `4` (`localized_supNorm_lift`).
  have hc₀_pos' : 0 < c₀ := lt_of_lt_of_le one_pos hc₀_pos
  refine ⟨c₀ * (4 * Real.sqrt 2) + 4 * c₀, by positivity, ?_⟩
  exact localized_core_construction hF_ne hF_meas h_int μ X
    hX_meas hX_iindep hX_idem hX_law c₀ hc₀_pos hengine

/-- **Lemma 19.34: localized chaining bound.**

Bounds `∫⁻ supNormOver (localizedDifferenceClass F P δq) (𝔾ₙ)` — the δq-shrunk
difference class whose supremum vanishes with `δq` — by
`c·J_{[]}(δq, F)` plus an envelope tail. This is the localized form used in
the proof of the Donsker theorem.

**Uniform positive clamp level.** The clamp level `M` is chosen
**before** quantifying over `n` (the existential `∃ M, 0 < M ∧ ∀ n …` has `M` outside
the `∀ n`). In the chaining regime `δq ≤ 1/4`, `M = min(θ/2, θ') > 0`
is built from the `M`-free positive lower bounds on `chainThreshold`
(`localized_chainThreshold_lower_bound`) and `globalThreshold`
(`localized_globalThreshold_lower_bound`), and the per-`n` clamp is
`Mc := √n · M`, so `2·Mc = √n·θ ≤ √n·chainThreshold` self-consistently.  The genuine
positivity `0 < M` is needed for equicontinuity: a
possibly-zero `M` would make the tail `√n·∫⁻|Φ|·1{√n·M<|Φ|} = √n·E|Φ|` fail to vanish.

**Tail threshold `√n · M`.** Both the `globalThreshold` tail and the
truncation excess are bounded by the tail at threshold `√n · M`. A linear
threshold `(n:ℝ)·M`
cannot be obtained because the clamp level is bounded by
`Mc ≤ √n·δq/2` (because `chainThreshold ≤ δq`), so every threshold the conclusion can be
folded under is at most `√n`-growing. `√n · M` is exactly vdV's truncation scale
`√n · a(δ)` (p.286); dominated convergence absorbs any positive-constant `√n` threshold
equally (`√n·E[|Φ|·1{|Φ|>√n·M}] → 0` for `Φ ∈ L²`), so this is sound.

The `n = 0` edge (empirical process ≡ 0 ⟹ LHS = 0) holds for the same uniform positive `M`;
the `n ≥ 1` core is `localizedChainBound_pos_core`.  The hypothesis `δq ≤ 1/4` restricts to
the chaining regime `δq ↓ 0`, where `M = min(θ/2, θ') > 0`; the
large-`δq` case is excluded by the hypothesis.

The assumptions are nonemptiness and measurability of `F`, together with
finiteness of its bracketing entropy integral. -/
theorem localizedChainBound_of_finiteEntropy
    [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
      ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
        ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
        ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
          ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
            + ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                    * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P) := by
  -- The universal constant `c` and the uniform clamp level `M` (outside `∀ n`) come from
  -- the `n ≥ 1` core; the `n = 0` edge (empirical process ≡ 0 ⟹ LHS integral = 0) holds for
  -- the same positive `M` and any `c > 0`.
  obtain ⟨c, hc_pos, hcore⟩ := localizedChainBound_pos_core hF_ne hF_meas h_int
    μ X hX_meas hX_iindep hX_idem hX_law
  refine ⟨c, hc_pos, ?_⟩
  intro Φ hΦ_meas hΦ_env hΦ_L2 δq hδq hδq4
  -- Reuse the core's uniform positive `M` for the `n = 0` edge.
  obtain ⟨M, hM, _, _, hbound⟩ := hcore Φ hΦ_meas hΦ_env hΦ_L2 hδq hδq4
  refine ⟨M, hM, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · -- `n = 0`: the empirical process is identically `0`, so the LHS integral is `0`.
    subst hn0
    have h_lhs : ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
          (fun h => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) h) ∂μ = 0 := by
      have h_sup0 : ∀ ξ : Ξ, supNormOver (localizedDifferenceClass F P δq)
          (fun h => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) h) = 0 := by
        intro ξ
        simp only [supNormOver, empiricalProcess_zero, abs_zero, ENNReal.ofReal_zero]
        exact le_antisymm (by simp) (by positivity)
      simp only [h_sup0, lintegral_zero]
    rw [h_lhs]; exact zero_le
  · exact hbound n hn_pos
/-- **M-lower-bound variant of `localizedChainBound_of_finiteEntropy`.**

This has the same hypotheses and right-hand side as
`localizedChainBound_of_finiteEntropy`, and additionally states a
**bracketing-explicit lower bound on the clamp level** `M`: for any common upper
bound `N` on the two localized-difference bracketing numbers at scales `δq`, `δq/2`,

    min ( 1/(2·(1 + √log(1 + N²))) , 1/(1 + √log(1 + N)) ) · δq ≤ M.

This lower bound yields the quantitative modulus in `LipschitzShellModulus`: the
Chebyshev envelope tail `≈ δq² / M` can only be folded to `≤ C · δq` once `M` is bounded below by
a positive multiple of `δq`; the bare `∃ M > 0` of the base theorem is insufficient.

**Construction.** `M = min(θ/2, θ')` where `θ, θ'` are the two threshold lower bounds
(`localized_chainThreshold_lower_bound` / `localized_globalThreshold_lower_bound`), each exactly of
the form `δq / (1 + √log(1 + N))`.  Because those lower bounds are *monotone in an upper bound on
the bracketing count*, the clause holds for **any** `N` dominating both bracketing numbers.

**Role of the explicit form.** The bracketing counts `NB₀`, `NB₁` are of the
`δq`-*localized* difference class `localizedDifferenceClass F P δq`, so an opaque `cM` is
`δq`-dependent.  A `δq`-uniform `cM` requires a **relative-bracketing** upper bound
`N(δq, localized(δq)) ≤ N_uniform`. The clause
`∀ N, (bracketing ≤ N) → cM(N)·δq ≤ M` combines with any such `δ`-free relative
bracketing bound to give a `δ`-free `cM`. -/
theorem localizedChainBound_of_finiteEntropy_MLower
    [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
      ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
        ∃ M : ℝ, 0 < M ∧
        (∀ N : ℕ,
            bracketingNumber δq (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
            bracketingNumber (δq / 2) (localizedDifferenceClass F P δq) 2 P ≤ (N : ℕ∞) →
            min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((N * N : ℕ) : ℝ))))))
                (1 / (1 + Real.sqrt (Real.log (1 + (N : ℝ))))) * δq ≤ M) ∧
        ∀ (n : ℕ),
        ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
          ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
            + ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                    * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P) := by
  -- Retain the bracketing-explicit lower-bound conjunct and handle the same `n = 0` edge.
  obtain ⟨c, hc_pos, hcore⟩ := localizedChainBound_pos_core hF_ne hF_meas h_int
    μ X hX_meas hX_iindep hX_idem hX_law
  refine ⟨c, hc_pos, ?_⟩
  intro Φ hΦ_meas hΦ_env hΦ_L2 δq hδq hδq4
  obtain ⟨M, hM, _, hM_Nbd, hbound⟩ := hcore Φ hΦ_meas hΦ_env hΦ_L2 hδq hδq4
  refine ⟨M, hM, hM_Nbd, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · -- `n = 0`: the empirical process is identically `0`, so the LHS integral is `0`.
    subst hn0
    have h_lhs : ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
          (fun h => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) h) ∂μ = 0 := by
      have h_sup0 : ∀ ξ : Ξ, supNormOver (localizedDifferenceClass F P δq)
          (fun h => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) h) = 0 := by
        intro ξ
        simp only [supNormOver, empiricalProcess_zero, abs_zero, ENNReal.ofReal_zero]
        exact le_antisymm (by simp) (by positivity)
      simp only [h_sup0, lintegral_zero]
    rw [h_lhs]; exact zero_le
  · exact hbound n hn_pos

/-- **Measurable-majorant form of the localized chaining bound.**

Same hypotheses and same RHS as `localizedChainBound_of_finiteEntropy`, but instead of
bounding the (non-measurable) integrand
`g ξ := supNormOver (localizedDifferenceClass F P δq) (𝔾ₙ ξ)` directly inside the `∫⁻`, it
produces a MEASURABLE `Maj : Ξ → ℝ≥0∞` with `g ≤ Maj` pointwise and `∫⁻ Maj ≤ RHS`.  This
is suitable for equicontinuity and outer-expectation arguments:
`outerExpectation g ≤ ∫⁻ Maj` (the upper integral of a non-measurable `g` is bounded by the
integral of any measurable majorant).

The theorem `chain_supnorm_measurableMajorant_dyadic_bound_uniform` supplies
`Maj_F'` over the clamped class `F' = truncateClass G Mc` with
`supNormOver F' (𝔾ₙ) ≤ Maj_F'` and the corresponding integral bound. The `F → F̃`
split bounds the localized
sup by `supNormOver F' (𝔾ₙ) + Bproc` (`Bproc` the measurable excess dominator,
`supNormProcess_dominated_pointwise_bound`), so `Maj := Maj_F' + Bproc` is measurable, dominates
`g` pointwise, and `∫⁻ Maj = ∫⁻ Maj_F' + ∫⁻ Bproc` folds to the SAME `C·J + C·√n·Tail` RHS via
the SAME two tail folds (`hexc_eq` / `hEngTail_le`) as the integral version. -/
theorem localizedChainBound_measurableMajorant_of_finiteEntropy
    [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
      ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
        ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
        ∃ Maj : Ξ → ℝ≥0∞, Measurable Maj ∧
          (∀ ξ, supNormOver (localizedDifferenceClass F P δq)
                (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ≤ Maj ξ) ∧
          ∫⁻ ξ, Maj ξ ∂μ
            ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
              + ENNReal.ofReal c * (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                      * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P) := by
  classical
  -- Use the measurable majorant with a constant independent of class, level,
  -- and scale.
  obtain ⟨c₀, hc₀, hengineMaj⟩ :=
    chain_supnorm_measurableMajorant_dyadic_bound_uniform (P := P) (μ := μ)
      hX_meas hX_iindep hX_idem hX_law
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le one_pos hc₀
  set C : ℝ := c₀ * (4 * Real.sqrt 2) + 4 * c₀ with hC_def
  have hC_pos : 0 < C := by rw [hC_def]; positivity
  refine ⟨C, hC_pos, ?_⟩
  intro Φ hΦ_meas hΦ_env hΦ_L2 δq hδq hδq4
  -- envelope / integrability / measurability of the localized class (as in the core).
  set G := localizedDifferenceClass F P δq with hG_def
  have hΦ_envG : IsEnvelope G Φ := hΦ_env.mono localizedDifferenceClass_subset
  have hΦ_int : Integrable Φ P := hΦ_L2.integrable (by norm_num)
  have hF_diff_meas : ∀ h ∈ G, Measurable h := by
    rintro h ⟨f, hf, g, hg, rfl, _⟩
    exact (hF_meas f hf).sub (hF_meas g hg)
  -- dyadic window + the `Mc`-free positive threshold lower bounds → uniform clamp level `M`.
  obtain ⟨q₀, hq₀⟩ := exists_q0_window hδq hδq4
  obtain ⟨θ, hθ_pos, _, _, hθ_le⟩ :=
    localized_chainThreshold_lower_bound (F := F) h_int hδq hF_diff_meas (q₀ := q₀)
  obtain ⟨θ', hθ'_pos, _, _, hθ'_le⟩ :=
    localized_globalThreshold_lower_bound (F := F) h_int hδq hF_diff_meas (q₀ := q₀)
  set M : ℝ := min (θ / 2) θ' with hM_def
  have hM_pos : 0 < M := lt_min (by positivity) hθ'_pos
  have hM_nonneg : 0 ≤ M := hM_pos.le
  have hM_le_θ2 : M ≤ θ / 2 := min_le_left _ _
  have hM_le_θ' : M ≤ θ' := min_le_right _ _
  have hG_ne : G.Nonempty := by
    obtain ⟨f, hf⟩ := hF_ne
    refine ⟨fun x => f x - f x, ?_⟩
    refine ⟨f, hf, f, hf, rfl, ?_⟩
    simp only [sub_self]
    rw [show (fun _ : Ω => (0 : ℝ)) = (0 : Ω → ℝ) from rfl, eLpNorm_zero]
    exact zero_le
  refine ⟨M, hM_pos, fun n => ?_⟩
  -- `n = 0`: the empirical process is `0`, so `g ≡ 0`; take `Maj := 0`.
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · subst hn0
    refine ⟨fun _ => 0, measurable_const, fun ξ => ?_, ?_⟩
    · have h0 : supNormOver (localizedDifferenceClass F P δq)
          (fun h => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) h) = 0 := by
        simp only [supNormOver, empiricalProcess_zero, abs_zero, ENNReal.ofReal_zero]
        exact le_antisymm (by simp) (by positivity)
      rw [h0]
    · rw [lintegral_zero]; exact zero_le
  -- `n ≥ 1`: build the per-scale localized majorant.
  have hn : 1 ≤ n := hn_pos
  have hsn_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  set Mc : ℝ := Real.sqrt n * M with hMc_def
  have hMc_nonneg : 0 ≤ Mc := mul_nonneg hsn_nonneg hM_nonneg
  set F' : Set (Ω → ℝ) := truncateClass G Mc with hF'_def
  set B := nestedBracketPartition_of_finiteEntropy_clamped
    (G := G) q₀ hδq Mc hMc_nonneg (hasFiniteBracketingCover_localized h_int δq hδq)
    hF_diff_meas with hB_def
  have hF'_ne : F'.Nonempty := by
    obtain ⟨g, hg⟩ := hG_ne
    exact ⟨clampFn Mc g, g, hg, rfl⟩
  have hF'_meas : ∀ f ∈ F', Measurable f := by
    rintro _ ⟨g, hg, rfl⟩; exact clampFn_measurable (hF_diff_meas g hg)
  have hΦ_envF' : IsEnvelope F' Φ := by
    rintro _ ⟨g, hg, rfl⟩ x
    exact (abs_clampReal_le Mc hMc_nonneg (g x)).trans (hΦ_envG g hg x)
  have hF'_L2 : ∀ f ∈ F', eLpNorm f 2 P ≤ ENNReal.ofReal δq := by
    rintro _ ⟨g, hg, rfl⟩
    refine le_trans (eLpNorm_mono (fun x => ?_)) (localizedDifferenceClass_hF_L2 hg)
    simpa [clampFn, Real.norm_eq_abs] using abs_clampReal_le Mc hMc_nonneg (g x)
  have hπ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (B.π q i) :=
    fun {q} hq i => B.π_meas hq i
  have hfix : 2 * Mc ≤ Real.sqrt n * chainThreshold B δq q₀ := by
    have h1 : θ ≤ chainThreshold B δq q₀ := by
      rw [hB_def]; exact hθ_le Mc hMc_nonneg
    calc 2 * Mc = Real.sqrt n * (2 * M) := by rw [hMc_def]; ring
      _ ≤ Real.sqrt n * θ := by
          apply mul_le_mul_of_nonneg_left _ hsn_nonneg; linarith [hM_le_θ2]
      _ ≤ Real.sqrt n * chainThreshold B δq q₀ :=
          mul_le_mul_of_nonneg_left h1 hsn_nonneg
  have hΔq0 : ∀ (i : Fin (B.Nq q₀)) (x : Ω),
      B.Δ q₀ i x ≤ Real.sqrt n * chainThreshold B δq q₀ := by
    rw [hB_def]
    exact localized_clamp_Δq0_discharge (F := F) h_int hδq hF_diff_meas
      (q₀ := q₀) Mc hMc_nonneg n hfix
  -- The measurable majorant `Maj_F'` over `F' = truncateClass G Mc`.
  obtain ⟨MajF', hMajF'_meas, hMajF'_dom, hMajF'_int⟩ :=
    hengineMaj F' q₀ δq B hπ_meas hF'_ne hF'_meas Φ hΦ_meas hΦ_envF' hΦ_L2
      hδq rfl hF'_L2 hq₀ n hn hΔq0
  -- ===== F→F̃ per-`ξ` lift: `g ξ ≤ supNormOver F' (𝔾ₙ) ξ + Bproc ξ`, then `≤ MajF' + Bproc`. =====
  set Ψ : Ω → ℝ := fun x => |Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x with hΨ_def
  set 𝒢 : Set (Ω → ℝ) := {g | ∃ h ∈ G, g = fun x => h x - clampFn Mc h x} with h𝒢_def
  have hΦ_abs_meas : Measurable (fun x => |Φ x|) := hΦ_meas.norm
  have hset_meas : MeasurableSet {y | Mc < |Φ y|} := hΦ_abs_meas measurableSet_Ioi
  have hΨ_meas : Measurable Ψ := hΦ_meas.norm.mul (measurable_const.indicator hset_meas)
  have hΨ_nn : ∀ x, 0 ≤ Ψ x := by
    intro x
    refine mul_nonneg (abs_nonneg _) ?_
    by_cases hx : x ∈ {y | Mc < |Φ y|} <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hdom : ∀ g ∈ 𝒢, ∀ x, |g x| ≤ Ψ x := by
    rintro g ⟨h, hhG, rfl⟩ x
    have hhΦ : |h x| ≤ Φ x := hΦ_envG h hhG x
    change |h x - clampFn Mc h x| ≤ |Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x
    by_cases hx : x ∈ {y | Mc < |Φ y|}
    · rw [Set.indicator_of_mem hx]
      simp only [Pi.one_apply, mul_one]
      have h1 : |h x - clampFn Mc h x| ≤ |h x| := by
        unfold clampFn clampReal
        rcases le_total (h x) Mc with hle | hle <;>
          rcases le_total (-Mc) (h x) with hle2 | hle2 <;>
          rw [max_def, min_def] <;> split_ifs <;>
          rcases abs_cases (h x) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
          rw [e2] <;>
          rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact le_trans h1 (le_trans hhΦ (le_abs_self _))
    · rw [Set.indicator_of_notMem hx]
      simp only [mul_zero]
      have hΦle : |Φ x| ≤ Mc := not_lt.mp (by simpa using hx)
      have hhle : |h x| ≤ Mc := le_trans (le_trans hhΦ (le_abs_self _)) hΦle
      have hcl : clampFn Mc h x = h x := by unfold clampFn; exact clampReal_of_mem hhle
      rw [hcl]; simp
  -- the measurable excess dominator `Bproc ξ = √n·(empAvg Ψ + ∫⁻Ψ)`.
  set Bproc : Ξ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Real.sqrt n) *
      (ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))
        + ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P) with hBproc_def
  have hBproc_meas : Measurable Bproc := by
    refine Measurable.const_mul ?_ _
    refine Measurable.fun_add ?_ measurable_const
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΨ_meas.comp (hX_meas i.val)
  have hΦ_envG' : IsEnvelope G Φ := hΦ_envG
  have hint_of_dom : ∀ {g : Ω → ℝ}, Measurable g → (∀ x, |g x| ≤ Φ x) → Integrable g P := by
    intro g hg_meas hg_dom
    refine Integrable.mono' hΦ_int hg_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hg_dom x)
  -- per-`ξ` split of the localized sup (clamp + excess), copied from `localized_supNorm_lift`.
  have h_pt : ∀ ξ : Ξ,
      supNormOver G (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
        ≤ supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
          + supNormOver 𝒢
              (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
    intro ξ
    refine iSup₂_le fun h hhG => ?_
    have hh_meas : Measurable h := hF_diff_meas h hhG
    have hh_dom : ∀ x, |h x| ≤ Φ x := hΦ_envG h hhG
    have hclamp_meas : Measurable (clampFn Mc h) := clampFn_measurable hh_meas
    have hclamp_dom : ∀ x, |clampFn Mc h x| ≤ Φ x :=
      fun x => le_trans (abs_clampReal_le Mc hMc_nonneg (h x)) (hh_dom x)
    have hh_int : Integrable h P := hint_of_dom hh_meas hh_dom
    have hclamp_int : Integrable (clampFn Mc h) P := hint_of_dom hclamp_meas hclamp_dom
    have hsplit : empiricalProcess P n (fun i : Fin n => X i.val ξ) h
        = empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)
          + empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun x => h x - clampFn Mc h x) := by
      rw [← empiricalProcess_add P n _ (clampFn Mc h) (fun x => h x - clampFn Mc h x)
        hclamp_int (hh_int.sub hclamp_int)]
      congr 1; funext x; ring
    simp only []
    rw [hsplit]
    calc ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)
            + empiricalProcess P n (fun i : Fin n => X i.val ξ) (fun x => h x - clampFn Mc h x)|
        ≤ ENNReal.ofReal
              (|empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)|
                + |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun x => h x - clampFn Mc h x)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)|
            + ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => h x - clampFn Mc h x)| := ENNReal.ofReal_add_le
      _ ≤ supNormOver (truncateClass G Mc)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
            + supNormOver 𝒢
                (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
        refine add_le_add ?_ ?_
        · exact le_supNormOver (z := fun h => empiricalProcess P n
            (fun i : Fin n => X i.val ξ) h) ⟨h, hhG, rfl⟩
        · exact le_supNormOver (z := fun g => empiricalProcess P n
            (fun i : Fin n => X i.val ξ) g) ⟨h, hhG, rfl⟩
  have h_excess_le : ∀ ξ : Ξ, supNormOver 𝒢
        (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) ≤ Bproc ξ := by
    intro ξ
    exact supNormProcess_dominated_pointwise_bound (P := P) 𝒢 Ψ hdom n hn ξ
  -- assemble the localized majorant.
  set Maj : Ξ → ℝ≥0∞ := fun ξ => MajF' ξ + Bproc ξ with hMaj_def
  have hMaj_meas : Measurable Maj := hMajF'_meas.add hBproc_meas
  have hMaj_dom : ∀ ξ, supNormOver G
      (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ≤ Maj ξ := by
    intro ξ
    refine (h_pt ξ).trans ?_
    exact add_le_add (hMajF'_dom ξ) (h_excess_le ξ)
  refine ⟨Maj, hMaj_meas, hMaj_dom, ?_⟩
  -- ===== integral bound `∫⁻ Maj ≤ C·J + C·√n·Tail` (mirrors `localized_core_construction`). =====
  set J : ℝ≥0∞ := bracketingEntropyIntegral δq F P with hJ_def
  set sn : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt n) with hsn_def
  set Tail : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal |Φ ω|
      * Set.indicator {x | Mc < |Φ x|} 1 ω ∂P with hTail_def
  -- `∫⁻ Bproc ≤ 4·sn·∫⁻Ψ`, and `∫⁻Ψ = Tail` (indicator pull-out).
  have hΨ_int_eq : ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P = Tail := by
    rw [hTail_def]
    refine lintegral_congr (fun x => ?_)
    rw [hΨ_def]
    by_cases hx : x ∈ {y | Mc < |Φ y|}
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hBproc_int : ∫⁻ ξ, Bproc ξ ∂μ ≤ 4 * sn * Tail := by
    have hΨ_meas_avg : AEMeasurable
        (fun ξ : Ξ => ENNReal.ofReal
          (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))) μ := by
      refine Measurable.aemeasurable ?_
      refine Measurable.ennreal_ofReal ?_
      unfold empiricalAvg
      refine Measurable.const_mul ?_ _
      refine Finset.measurable_sum Finset.univ ?_
      intro i _
      exact hΨ_meas.comp (hX_meas i.val)
    have hemp_le := lintegral_empiricalAvg_le (P := P) hX_meas hX_idem hX_law Ψ hΨ_meas hΨ_nn n hn
    rw [hBproc_def]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left' hΨ_meas_avg,
      lintegral_const, measure_univ, mul_one]
    calc ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ξ, ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ
              + ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P)
        ≤ ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ x, ENNReal.ofReal (Ψ x) ∂P + ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P) :=
          mul_le_mul_of_nonneg_left (add_le_add hemp_le le_rfl) (zero_le)
      _ = 2 * sn * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by rw [hsn_def]; ring
      _ = 2 * sn * Tail := by rw [hΨ_int_eq]
      _ ≤ 4 * sn * Tail := by gcongr; norm_num
  -- Its integral over `F'` is at most `c₀·dyadic + c₀·sn·EngTail`.
  -- dyadic series over `F'` ≤ `4√2·J` (same chain as `localized_core_construction`).
  have hdyadic : (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δq)
        * entropyIntegrand ((1/2 : ℝ)^q * δq) F' P)
      ≤ ENNReal.ofReal (4 * Real.sqrt 2) * J := by
    have hcover : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F (ε / 2) 2 P :=
      fun ε hε => hasFiniteBracketingCover_of_entropyIntegral_lt_top h_int (by positivity)
    refine (dyadic_sum_le_bracketingEntropyIntegral (F := F') hδq).trans ?_
    have h1 : bracketingEntropyIntegral δq F' P
        ≤ bracketingEntropyIntegral δq (localizedDifferenceClass F P δq) P :=
      bracketingEntropyIntegral_truncateClass_le hMc_nonneg
    have h2 : bracketingEntropyIntegral δq (localizedDifferenceClass F P δq) P
        ≤ bracketingEntropyIntegral δq (differenceClass F) P :=
      bracketingEntropyIntegral_mono_class localizedDifferenceClass_subset
    have h3 : bracketingEntropyIntegral δq (differenceClass F) P
        ≤ ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δq F P :=
      bracketingEntropyIntegral_diff_le_class hδq.le hcover
    calc 2 * bracketingEntropyIntegral δq F' P
        ≤ 2 * (ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δq F P) := by
          gcongr; exact (h1.trans h2).trans h3
      _ = ENNReal.ofReal (4 * Real.sqrt 2) * J := by
          rw [hJ_def, show ENNReal.ofReal (4 * Real.sqrt 2)
                = 2 * ENNReal.ofReal (2 * Real.sqrt 2) by
            rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring]
          ring
  -- The tail at threshold `√n·globalThreshold B` is bounded by `Tail` at
  -- threshold `Mc`.
  have hMc_le_gt : Mc ≤ Real.sqrt n * globalThreshold B δq := by
    have hg : θ' ≤ globalThreshold B δq := by rw [hB_def]; exact hθ'_le Mc hMc_nonneg
    calc Mc = Real.sqrt n * M := hMc_def
      _ ≤ Real.sqrt n * θ' := mul_le_mul_of_nonneg_left hM_le_θ' hsn_nonneg
      _ ≤ Real.sqrt n * globalThreshold B δq := mul_le_mul_of_nonneg_left hg hsn_nonneg
  have hEngTail_le : ∫⁻ ω, ENNReal.ofReal |Φ ω|
        * Set.indicator {x | Real.sqrt n * globalThreshold B δq < |Φ x|} 1 ω ∂P ≤ Tail := by
    rw [hTail_def]
    refine lintegral_mono (fun ω => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    refine Set.indicator_le_indicator_of_subset ?_ (fun _ => zero_le) ω
    intro x hx
    exact lt_of_le_of_lt hMc_le_gt hx
  -- assemble: `∫⁻ Maj = ∫⁻ MajF' + ∫⁻ Bproc`, then the two tail folds give `C·J + C·sn·Tail`.
  have hMaj_int_split : ∫⁻ ξ, Maj ξ ∂μ = (∫⁻ ξ, MajF' ξ ∂μ) + ∫⁻ ξ, Bproc ξ ∂μ := by
    rw [hMaj_def]; exact lintegral_add_right' _ hBproc_meas.aemeasurable
  rw [hMaj_int_split]
  calc (∫⁻ ξ, MajF' ξ ∂μ) + ∫⁻ ξ, Bproc ξ ∂μ
      ≤ (ENNReal.ofReal c₀ * (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δq)
              * entropyIntegrand ((1/2 : ℝ)^q * δq) F' P)
          + ENNReal.ofReal c₀ * (sn * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
              * Set.indicator {x | Real.sqrt n * globalThreshold B δq < |Φ x|} 1 ω ∂P))
          + 4 * sn * Tail := by
        rw [hsn_def]; exact add_le_add hMajF'_int hBproc_int
    _ ≤ (ENNReal.ofReal c₀ * (ENNReal.ofReal (4 * Real.sqrt 2) * J)
          + ENNReal.ofReal c₀ * (sn * Tail)) + 4 * sn * Tail := by
        refine add_le_add (add_le_add ?_ ?_) le_rfl
        · exact mul_le_mul_of_nonneg_left hdyadic (zero_le)
        · exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEngTail_le (zero_le)) (zero_le)
    _ = ENNReal.ofReal (c₀ * (4 * Real.sqrt 2)) * J
          + (ENNReal.ofReal c₀ + 4) * (sn * Tail) := by
        rw [ENNReal.ofReal_mul hc₀_pos.le]; ring
    _ ≤ ENNReal.ofReal C * J + ENNReal.ofReal C * (sn * Tail) := by
        have hCfact : ENNReal.ofReal C
            = ENNReal.ofReal (c₀ * (4 * Real.sqrt 2)) + ENNReal.ofReal (4 * c₀) := by
          rw [hC_def, ENNReal.ofReal_add (by positivity) (by positivity)]
        have hsqrt2_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
          rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
        refine add_le_add ?_ ?_
        · gcongr
          rw [hC_def]; nlinarith [hc₀, hsqrt2_ge]
        · rw [hCfact]
          refine mul_le_mul_of_nonneg_right ?_ (zero_le)
          have hh1 : ENNReal.ofReal c₀ ≤ ENNReal.ofReal (c₀ * (4 * Real.sqrt 2)) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith [hc₀, hsqrt2_ge]
          have hh2 : (4 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * c₀) := by
            rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp]
            exact ENNReal.ofReal_le_ofReal (by nlinarith [hc₀])
          exact add_le_add hh1 hh2

end AsymptoticStatistics.EmpiricalProcess
