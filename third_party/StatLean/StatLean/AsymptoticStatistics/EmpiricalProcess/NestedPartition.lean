module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.PointwiseDense

@[expose] public section

/-!
# Nested bracketing partitions for the chaining argument

This file packages the combinatorial object at the heart of the chaining
proof of vdV Lemma 19.34 (van der Vaart, *Asymptotic Statistics*, p.286-287):
a **nested sequence of partitions** of a function class `F`, indexed by a
scale `q ≥ q₀`, together with a chosen representative `π q i` of each cell
and an envelope `Δ q i` controlling the oscillation of `F` over the cell.

vdV p.286: *"There exists a nested sequence of partitions `F = ⋃ᵢ F_{qi}` of
`F`, indexed by the integers `q ≥ q₀`, into `N_q` disjoint subsets and
measurable functions `Δ_{qi} ≤ 2F` such that `sup_{f,g ∈ F_{qi}} |f − g| ≤
Δ_{qi}` and `‖Δ_{qi}‖_{P,2} ≤ 2^{−q} a(δ) ⋯`."*

The construction (`nestedBracketPartition_of_covers`) takes, for each level
`p` in `[q₀, q]`, a finite `L²(P)`-bracketing cover of `F` at size `2^{−p}`
(`HasFiniteBracketingCover`), and builds the partition by disjointifying,
intersecting across levels, and removing empty cells.

Principal declarations: `NestedBracketPartition`, `nestedBracketPartition_of_covers`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A **nested bracketing partition** of a function class `F ⊆ (Ω → ℝ)`,
relative to a measure `P`, starting at scale index `q₀`.

For each level `q`, the class `F` is partitioned into `Nq q` cells
`cell q i` (`i : Fin (Nq q)`); `π q i` is a distinguished member of cell `i`
(the book's `f_{qi}`), and `Δ q i` is a measurable `L²(P)` envelope of the
oscillation of `F` over cell `i`.

Constitutive (vdV §19.6 p.286): the fields `cover`, `disjoint`, `refines`,
`diam`, and `Δ_L2_le` are exactly the four bulleted conditions of the
nested-partition paragraph; removing any one makes this not the book's
`{F_{qi}, Δ_{qi}}`. The bound `Δ_L2_le` carries the scale constant `C`
(the book's `a(δ)` times an absolute factor), kept as a structure parameter
so the salvage `(∑ log N_p)^{1/2} ≤ ∑ (log N_p)^{1/2}` step (a sibling lemma)
can be threaded through. -/
structure NestedBracketPartition (F : Set (Ω → ℝ)) (P : Measure Ω)
    (q₀ : ℕ) (C : ℝ) where
  /-- The number of cells at level `q`. -/
  Nq : ℕ → ℕ
  /-- The cardinality of the per-level `2^{−p}`-bracketing cover used at level
  `p` (the book's `N_p`); `Nq q` is bounded by the product of these. -/
  coverCard : ℕ → ℕ
  /-- The cells of the level-`q` partition. -/
  cell : (q : ℕ) → Fin (Nq q) → Set (Ω → ℝ)
  /-- A chosen representative of each cell (the book's `f_{qi}`). -/
  π : (q : ℕ) → Fin (Nq q) → (Ω → ℝ)
  /-- The oscillation envelope `Δ_{qi}` of each cell. -/
  Δ : (q : ℕ) → Fin (Nq q) → (Ω → ℝ)
  /-- The cells cover `F`. -/
  cover : ∀ {q : ℕ}, q₀ ≤ q → ∀ f ∈ F, ∃ i, f ∈ cell q i
  /-- Each cell is a subset of `F`. -/
  cell_subset : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, cell q i ⊆ F
  /-- Cells at a given level are pairwise disjoint. -/
  disjoint : ∀ {q : ℕ}, q₀ ≤ q → ∀ i j, i ≠ j → Disjoint (cell q i) (cell q j)
  /-- Every cell is nonempty. -/
  cell_nonempty : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, (cell q i).Nonempty
  /-- The partitions are successive refinements: each level-`(q + 1)` cell is
  contained in some level-`q` cell. -/
  refines : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, ∃ j, cell (q + 1) i ⊆ cell q j
  /-- The chosen representative lies in its cell. -/
  π_mem : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, π q i ∈ cell q i
  /-- The chosen representative is measurable.
  Constitutive (vdV §19.6 p.286): the representatives `f_{qi}` are members of the
  function class `F`, every member of which is a measurable function (the empirical
  process `𝔾ₙ f` is only defined for measurable `f`). The chosen-member abstraction
  `π q i = (cell q i).Nonempty.choose` loses this through `Classical.choose`, so the
  fact must be carried as a field; the constructors discharge it from the
  measurability of `F`'s members. -/
  π_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (π q i)
  /-- `Δ_{qi}` dominates the oscillation of `F` over the cell. -/
  diam : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, ∀ f ∈ cell q i, ∀ g ∈ cell q i, ∀ x,
    |f x - g x| ≤ Δ q i x
  /-- `Δ_{qi}` is measurable. -/
  Δ_meas : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, Measurable (Δ q i)
  /-- `Δ_{qi}` is in `L²(P)`. -/
  Δ_memLp : ∀ {q : ℕ}, q₀ ≤ q → ∀ i, MemLp (Δ q i) 2 P
  /-- The `L²(P)`-size of `Δ_{qi}` is at most `C · 2^{−(q − q₀)}` (the **offset**
  scale: partition level `q₀` sits at the coarsest scale `C = δ`, level
  `q₀ + k` at `(1/2)^k·δ`, matching vdV's "*first cover `F` with brackets of size
  `2^{-q}`*" with `2^{-q₀} ≈ δ`). The series-offset `k = q − q₀` therefore lands on
  the dyadic-series term `(1/2)^k·δ`. -/
  Δ_L2_le : ∀ {q : ℕ}, q₀ ≤ q → ∀ i,
    eLpNorm (Δ q i) 2 P ≤ ENNReal.ofReal (C * (1 / 2 : ℝ) ^ (q - q₀))
  /-- **Oscillation nesting monotonicity** (Constitutive, vdV §19.6 p.287
  *"because the partitions are nested, `Δ_q B_q ≤ Δ_{q-1} B_q`"*). The level-`(q+1)`
  cell oscillation is pointwise dominated by the oscillation of its parent cell
  `(refines hq i).choose` at level `q`. This is the parent map used by
  `NestedBracketPartition.parent`, so
  `B.Δ_succ_le_parent hq i x : B.Δ (q+1) i x ≤ B.Δ q (B.parent hq i) x` holds by
  `rfl` on the parent index. This monotonicity is stronger than the bare `diam`
  bound and yields the truncation estimate `Δ_q ≤ √n·a_{q-1}`. -/
  Δ_succ_le_parent : ∀ {q : ℕ} (hq : q₀ ≤ q) (i : Fin (Nq (q + 1))) (x : Ω),
    Δ (q + 1) i x ≤ Δ q (refines hq i).choose x
  /-- `N_q` is bounded by the product `∏_{p=q₀}^{q} N_p` of the per-level
  cover cardinalities (vdV p.287: *"partitions into `N_q ≤ ∏ N_p` sets"*).
  The product is written over `Finset.Icc q₀ q`. -/
  card_le : ∀ {q : ℕ}, q₀ ≤ q →
    (Nq q : ℕ) ≤ ∏ p ∈ Finset.Icc q₀ q, coverCard p
  /-- Each per-level cover cardinality `coverCard p` is bounded by the
  *bracketing number* of `F` at the **offset** dyadic scale `(1/2)^(p − q₀) · C`
  (at `p = q₀` the scale is `C = δ`, while at `p = q₀ + k` it is `(1/2)^k·δ`).
  With the `C = δ` convention (the structure's scale constant doubles as the
  entropy integral's upper cutoff `δ`), this is exactly vdV's requirement that the
  partition be built from **minimal** `(1/2)^(p−q₀)·δ`-bracketing covers, so that
  `√(log N_p) ≤ √(log N_{[]}((1/2)^(p−q₀)·δ, F, L²(P)))` feeds the entropy integral
  at the matching series offset.
  Constitutive (vdV §19.6 p.287): without the minimal-cover bound the dyadic
  series cannot be dominated by `J_{[]}(δ, F, L²(P))`. -/
  coverCard_le : ∀ {p : ℕ}, q₀ ≤ p →
    (coverCard p : ℕ∞) ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * C) F 2 P

/-!
## Construction from per-level bracketing covers

We build a `NestedBracketPartition` from a family of finite `L²(P)`-bracketing
covers, one per level `p ≥ q₀`, of `F` at size `2^{−p}`. Each cover is encoded
by its data: a size `k p`, lower/upper bracket families `lb p, ub p : Fin (k p)
→ Ω → ℝ`, the `IsEpsBracket` witnesses, and the covering property.

The cells are the joint fibers of a per-level *assignment* map: for each level
`p` we pick, for every `f ∈ F`, the first bracket index containing `f`
(`assignIdx`). A level-`q` cell is the set of `f ∈ F` whose assignment tuple
over `[q₀, q]` equals a fixed nonempty tuple. This realizes the book's
*disjointify + intersect across levels + prune empty cells*: fibers of a
single-valued assignment are automatically disjoint, their union is `F`, the
restriction of the tuple yields successive refinements, and empty fibers are
pruned by indexing over nonempty tuples only.
-/

variable {F : Set (Ω → ℝ)} {P : Measure Ω}

/-- Bundled data of a finite `L²(P)`-bracketing cover of `F` at size `ε`:
size `k`, bracket families `lb, ub`, the bracket witnesses, and the covering
property. Extracted (non-canonically, via choice) from
`HasFiniteBracketingCover`. -/
structure BracketingCoverData (F : Set (Ω → ℝ)) (ε : ℝ) (P : Measure Ω) where
  k : ℕ
  lb : Fin k → Ω → ℝ
  ub : Fin k → Ω → ℝ
  bracket : ∀ i, IsEpsBracket ε (lb i) (ub i) 2 P
  covers : ∀ f ∈ F, ∃ i, ∀ x, lb i x ≤ f x ∧ f x ≤ ub i x

namespace BracketingCoverData

variable {ε : ℝ}

/-- Recover the bundled cover data from a `HasFiniteBracketingCover` proof. -/
noncomputable def ofHasFiniteCover (h : HasFiniteBracketingCover F ε 2 P) :
    BracketingCoverData F ε P :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.choose_spec.2⟩

/-- A cover at scale `ε₁` is a cover at any larger scale `ε₂ ≥ ε₁`: each
`ε₁`-bracket is an `ε₂`-bracket (`IsEpsBracket.mono_eps`), and the same brackets
still cover `F`. Used to fill the `p < q₀` slots of the cover family in
`nestedBracketPartition_of_finiteEntropy` (those slots are never read by any
field proof, but the cover family must be a total function `ℕ → …`). -/
def monoEps {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (cov : BracketingCoverData F ε₁ P) :
    BracketingCoverData F ε₂ P :=
  ⟨cov.k, cov.lb, cov.ub, fun i => (cov.bracket i).mono_eps hε, cov.covers⟩

@[simp] lemma monoEps_k {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (cov : BracketingCoverData F ε₁ P) :
    (cov.monoEps hε).k = cov.k := rfl

end BracketingCoverData

section Construction

variable {q₀ : ℕ}

/-- The chosen bracket index of `f` at level `p`, as a natural number: the
canonical `i.1` for the first bracket `i` of `cov` containing `f` (junk `0`
when no bracket contains `f`, e.g. outside `F`). Returning into `ℕ` avoids the
`Fin (cov.k)`-emptiness obstruction; the bound `< cov.k` is recovered on `F`
by `assignIdx_lt`. This single-valued *assignment* has the cells as its joint
fibers. -/
noncomputable def assignIdx {ε : ℝ} (cov : BracketingCoverData F ε P)
    (f : Ω → ℝ) : ℕ := by
  classical
  exact if h : ∃ i, ∀ x, cov.lb i x ≤ f x ∧ f x ≤ cov.ub i x then (h.choose : Fin cov.k).1
    else 0

lemma assignIdx_spec {ε : ℝ} (cov : BracketingCoverData F ε P) {f : Ω → ℝ}
    (hf : ∃ i, ∀ x, cov.lb i x ≤ f x ∧ f x ≤ cov.ub i x) :
    ∃ i : Fin cov.k, i.1 = assignIdx cov f ∧
      (∀ x, cov.lb i x ≤ f x ∧ f x ≤ cov.ub i x) := by
  classical
  refine ⟨hf.choose, ?_, hf.choose_spec⟩
  unfold assignIdx
  rw [dif_pos hf]

lemma assignIdx_lt {ε : ℝ} (cov : BracketingCoverData F ε P) {f : Ω → ℝ}
    (hf : ∃ i, ∀ x, cov.lb i x ≤ f x ∧ f x ≤ cov.ub i x) :
    assignIdx cov f < cov.k := by
  obtain ⟨i, hi, _⟩ := assignIdx_spec cov hf
  rw [← hi]; exact i.2

/-- On `F`, `assignIdx` selects a genuine bracket containing `f`. -/
lemma assignIdx_mem_bracket {ε : ℝ} (cov : BracketingCoverData F ε P)
    {f : Ω → ℝ} (hf : f ∈ F) (x : Ω) :
    cov.lb ⟨assignIdx cov f, assignIdx_lt cov (cov.covers f hf)⟩ x ≤ f x ∧
      f x ≤ cov.ub ⟨assignIdx cov f, assignIdx_lt cov (cov.covers f hf)⟩ x := by
  obtain ⟨i, hi, hbr⟩ := assignIdx_spec cov (cov.covers f hf)
  have : (⟨assignIdx cov f, assignIdx_lt cov (cov.covers f hf)⟩ : Fin cov.k) = i := by
    apply Fin.ext; rw [hi]
  rw [this]; exact hbr x

/- A per-level *scale* `scale p` indexing the bracketing-cover data at level
`p`. Instantiated `scale p = (1/2)^p` by `nestedBracketPartition_of_covers` and
`scale p = (1/2)^p · δ` by `nestedBracketPartition_of_finiteEntropy`. The
combinatorial construction below never uses the value of `scale p`; only
`buildΔ_L2_le` reads it back, via the bracket size bound `< ofReal (scale q)`. -/
variable {scale : ℕ → ℝ}

/-- The level-`q` index type: a choice of bracket at every level
`p ∈ [q₀, q]`. A finite product of `Fin (cov p).k`'s. -/
abbrev LevelTuple (cov : (p : ℕ) → BracketingCoverData F (scale p) P)
    (q₀ q : ℕ) : Type _ :=
  (p : ↥(Finset.Icc q₀ q)) → Fin (cov p.1).k

/-- The assignment tuple of `f ∈ F` at level `q`: at each level
`p ∈ [q₀, q]`, the bracket index `assignIdx`. -/
noncomputable def assignTuple (cov : (p : ℕ) → BracketingCoverData F (scale p) P)
    (q₀ q : ℕ) {f : Ω → ℝ} (hf : f ∈ F) : LevelTuple cov q₀ q :=
  fun p => ⟨assignIdx (cov p.1) f, assignIdx_lt (cov p.1) ((cov p.1).covers f hf)⟩

/-- The set of level-`q` tuples actually achieved by some `f ∈ F`. As a
subtype of the finite `LevelTuple`, it is a `Fintype`; its cardinality is
`Nq q`. -/
def AchievedTuple (cov : (p : ℕ) → BracketingCoverData F (scale p) P)
    (q₀ q : ℕ) : Type _ :=
  {t : LevelTuple cov q₀ q // ∃ f, ∃ hf : f ∈ F, assignTuple cov q₀ q hf = t}

noncomputable instance (cov : (p : ℕ) → BracketingCoverData F (scale p) P)
    (q₀ q : ℕ) : Fintype (AchievedTuple cov q₀ q) := by
  classical
  unfold AchievedTuple
  infer_instance

variable (cov : (p : ℕ) → BracketingCoverData F (scale p) P)

/-- Number of cells at level `q`: the count of achieved level-`q` tuples. -/
noncomputable def buildNq (q : ℕ) : ℕ := Fintype.card (AchievedTuple cov q₀ q)

/-- Decode a cell index `i : Fin (buildNq q)` to its achieved tuple. -/
noncomputable def decode (q : ℕ) (i : Fin (buildNq cov (q₀ := q₀) q)) :
    AchievedTuple cov q₀ q :=
  (Fintype.equivFin (AchievedTuple cov q₀ q)).symm i

/-- The level-`q` cell indexed by `i`: the set of `f ∈ F` whose level-`q`
assignment tuple equals the `i`-th achieved tuple. -/
noncomputable def buildCell (q : ℕ) (i : Fin (buildNq cov (q₀ := q₀) q)) :
    Set (Ω → ℝ) :=
  {f | ∃ hf : f ∈ F, assignTuple cov q₀ q hf = (decode cov (q₀ := q₀) q i).1}

/-- Membership in `buildCell` unfolded. -/
lemma mem_buildCell {q : ℕ} {i : Fin (buildNq cov (q₀ := q₀) q)} {f : Ω → ℝ} :
    f ∈ buildCell cov (q₀ := q₀) q i ↔
      ∃ hf : f ∈ F, assignTuple cov q₀ q hf = (decode cov (q₀ := q₀) q i).1 :=
  Iff.rfl

/-- The level-`q` (top-level) bracket index of cell `i`: the `q`-coordinate of
its achieved tuple. Requires `q₀ ≤ q` so that `q ∈ Icc q₀ q`. -/
noncomputable def topIdx {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (buildNq cov (q₀ := q₀) q)) : Fin (cov q).k :=
  (decode cov (q₀ := q₀) q i).1 ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩⟩

/-- The chosen bracket index of cell `i` at level `p ∈ [q₀, q]`: the `p`-coordinate
of the cell's achieved tuple `(decode … q i).1`. -/
noncomputable def cellIdx {q : ℕ} (i : Fin (buildNq cov (q₀ := q₀) q))
    (p : ↥(Finset.Icc q₀ q)) : Fin (cov p.1).k :=
  (decode cov (q₀ := q₀) q i).1 p

/-- The `Icc q₀ q` subtype is nonempty (it contains `q` when `q₀ ≤ q`), so its
universal `Finset` is nonempty: the index set of the min-of-widths below. -/
lemma univ_Icc_nonempty {q : ℕ} (hq : q₀ ≤ q) :
    (Finset.univ : Finset ↥(Finset.Icc q₀ q)).Nonempty :=
  ⟨⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩⟩, Finset.mem_univ _⟩

/-- The width `ub − lb` of cell `i`'s chosen bracket at level `p ∈ [q₀, q]`. -/
noncomputable def cellWidth {q : ℕ} (i : Fin (buildNq cov (q₀ := q₀) q))
    (p : ↥(Finset.Icc q₀ q)) (x : Ω) : ℝ :=
  (cov p.1).ub (cellIdx cov i p) x - (cov p.1).lb (cellIdx cov i p) x

/-- `Δ q i` is the **min over the cell's whole tuple `[q₀, q]`** of the per-level
bracket widths, using the minimum of the intersected widths. The cell is the
intersection of its chosen brackets across levels `q₀ … q`, so its oscillation is
dominated by *every* level's width, hence by the minimum. Re-indexing to the
offset scale, the level-`q` width is itself a `(1/2)^(q−q₀)·δ`-bracket, so
the min — being `≤` that width — inherits the offset `L²`-decay. -/
noncomputable def buildΔ {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (buildNq cov (q₀ := q₀) q)) : Ω → ℝ :=
  fun x => (Finset.univ : Finset ↥(Finset.Icc q₀ q)).inf' (univ_Icc_nonempty hq)
    (fun p => cellWidth cov i p x)

/-- Every cell is nonempty: it is the image of an achieved tuple. -/
lemma buildCell_nonempty {q : ℕ} (i : Fin (buildNq cov (q₀ := q₀) q)) :
    (buildCell cov (q₀ := q₀) q i).Nonempty := by
  obtain ⟨f, hf, hft⟩ := (decode cov (q₀ := q₀) q i).2
  exact ⟨f, hf, hft⟩

/-- A chosen representative of cell `i`. -/
noncomputable def buildπ {q : ℕ} (i : Fin (buildNq cov (q₀ := q₀) q)) : Ω → ℝ :=
  (buildCell_nonempty cov (q₀ := q₀) i).choose

lemma buildπ_mem {q : ℕ} (i : Fin (buildNq cov (q₀ := q₀) q)) :
    buildπ cov (q₀ := q₀) i ∈ buildCell cov (q₀ := q₀) q i :=
  (buildCell_nonempty cov (q₀ := q₀) i).choose_spec

/-- A cell is contained in `F`. -/
lemma buildCell_subset {q : ℕ} (i : Fin (buildNq cov (q₀ := q₀) q)) :
    buildCell cov (q₀ := q₀) q i ⊆ F := by
  rintro f ⟨hf, -⟩; exact hf

/-- The chosen representative is measurable, given that every member of `F` is.
The representative is a member of its cell, hence of `F` (`buildπ_mem` +
`buildCell_subset`), so measurability is inherited from `hF_meas`. -/
lemma buildπ_meas (hF_meas : ∀ f ∈ F, Measurable f) {q : ℕ}
    (i : Fin (buildNq cov (q₀ := q₀) q)) :
    Measurable (buildπ cov (q₀ := q₀) i) :=
  hF_meas _ (buildCell_subset cov i (buildπ_mem cov i))

/-- Every `f ∈ F` lies in some level-`q` cell (its own assignment tuple is
achieved, hence indexed by some `i`). -/
lemma buildCell_cover {q : ℕ} (_hq : q₀ ≤ q) {f : Ω → ℝ} (hf : f ∈ F) :
    ∃ i, f ∈ buildCell cov (q₀ := q₀) q i := by
  -- the tuple `assignTuple … hf` is achieved (by `f`), so it is in `AchievedTuple`;
  -- its `equivFin` image is the desired index.
  set t : AchievedTuple cov q₀ q := ⟨assignTuple cov q₀ q hf, f, hf, rfl⟩ with ht
  refine ⟨Fintype.equivFin (AchievedTuple cov q₀ q) t, ?_⟩
  refine (mem_buildCell cov).mpr ⟨hf, ?_⟩
  -- decode (equivFin t) = t
  show assignTuple cov q₀ q hf = (decode cov (q₀ := q₀) q
      (Fintype.equivFin (AchievedTuple cov q₀ q) t)).1
  unfold decode
  rw [Equiv.symm_apply_apply]

/-- The cell that contains `f ∈ F` is determined by `f`'s assignment tuple:
two cells containing the same `f` have the same achieved tuple. This gives
pairwise disjointness. -/
lemma buildCell_disjoint {q : ℕ} (i j : Fin (buildNq cov (q₀ := q₀) q))
    (hij : i ≠ j) :
    Disjoint (buildCell cov (q₀ := q₀) q i) (buildCell cov (q₀ := q₀) q j) := by
  rw [Set.disjoint_left]
  rintro f ⟨hf, hfi⟩ ⟨hf', hfj⟩
  -- both decode-tuples equal assignTuple … hf, so the two achieved tuples are equal,
  -- hence i = j via the equiv, contradiction.
  apply hij
  have htup : (decode cov (q₀ := q₀) q i).1 = (decode cov (q₀ := q₀) q j).1 := by
    rw [← hfi, ← hfj]
  have hdec : decode cov (q₀ := q₀) q i = decode cov (q₀ := q₀) q j :=
    Subtype.ext htup
  unfold decode at hdec
  exact (Fintype.equivFin (AchievedTuple cov q₀ q)).symm.injective hdec

/-- An element of cell `i` lies inside the cell's chosen bracket at **every** level
`p ∈ [q₀, q]`: at level `p`, `f`'s assigned bracket is exactly `cellIdx … p`. This
is the intersection-of-brackets property of the cell: the cell is the
joint fiber of the assignment tuple, so every member sits in each level's bracket. -/
lemma buildCell_in_bracket {q : ℕ}
    {i : Fin (buildNq cov (q₀ := q₀) q)} {f : Ω → ℝ}
    (hf : f ∈ buildCell cov (q₀ := q₀) q i) (p : ↥(Finset.Icc q₀ q)) (x : Ω) :
    (cov p.1).lb (cellIdx cov i p) x ≤ f x ∧ f x ≤ (cov p.1).ub (cellIdx cov i p) x := by
  obtain ⟨hfF, hft⟩ := hf
  -- the p-coordinate of `assignTuple … hfF` equals the p-coordinate of the cell tuple
  have hp_coord : assignTuple cov q₀ q hfF p = cellIdx cov i p := by
    rw [hft]; rfl
  have hbr := assignIdx_mem_bracket (cov p.1) hfF x
  have hidx : (⟨assignIdx (cov p.1) f, assignIdx_lt (cov p.1) ((cov p.1).covers f hfF)⟩ :
      Fin (cov p.1).k) = cellIdx cov i p := by
    have := hp_coord
    unfold assignTuple at this
    exact this
  rw [hidx] at hbr
  exact hbr

/-- An element of cell `i` lies inside the cell's top-level bracket: at level
`q`, `f`'s chosen bracket is exactly `topIdx`. Special case of
`buildCell_in_bracket` at `p = ⟨q, …⟩` (where `cellIdx … ⟨q, …⟩ = topIdx`). -/
lemma buildCell_in_top_bracket {q : ℕ} (hq : q₀ ≤ q)
    {i : Fin (buildNq cov (q₀ := q₀) q)} {f : Ω → ℝ}
    (hf : f ∈ buildCell cov (q₀ := q₀) q i) (x : Ω) :
    (cov q).lb (topIdx cov hq i) x ≤ f x ∧ f x ≤ (cov q).ub (topIdx cov hq i) x :=
  buildCell_in_bracket cov hf ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩⟩ x

/-- `Δ q i` dominates the oscillation of `F` over cell `i`: both `f` and `g` lie in
*every* level's bracket, so `|f − g| ≤ width_p` for each `p ∈ [q₀, q]`, hence `≤`
the minimum `Δ q i = inf'_p width_p`. -/
lemma buildΔ_diam {q : ℕ} (hq : q₀ ≤ q) (i : Fin (buildNq cov (q₀ := q₀) q))
    {f g : Ω → ℝ} (hf : f ∈ buildCell cov (q₀ := q₀) q i)
    (hg : g ∈ buildCell cov (q₀ := q₀) q i) (x : Ω) :
    |f x - g x| ≤ buildΔ cov hq i x := by
  unfold buildΔ
  refine Finset.le_inf' _ _ (fun p _ => ?_)
  obtain ⟨hlf, huf⟩ := buildCell_in_bracket cov hf p x
  obtain ⟨hlg, hug⟩ := buildCell_in_bracket cov hg p x
  unfold cellWidth
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The per-level width `cellWidth cov i p` is measurable (difference of the two
measurable bracket bounds). -/
lemma cellWidth_meas {q : ℕ} (i : Fin (buildNq cov (q₀ := q₀) q))
    (p : ↥(Finset.Icc q₀ q)) :
    Measurable (fun x => cellWidth cov i p x) :=
  ((cov p.1).bracket (cellIdx cov i p)).measurable_upper.sub
    ((cov p.1).bracket (cellIdx cov i p)).measurable_lower

/-- `Δ q i` is measurable: a finite `inf'` of the measurable per-level widths.
We move the `inf'` outside the pointwise evaluation (`Finset.inf'_apply`) and run
`Finset.inf'_induction` with the `Measurable` predicate (closed under binary `⊓` by
`Measurable.inf'`, and each leaf `cellWidth cov i p` is measurable). -/
lemma buildΔ_meas {q : ℕ} (hq : q₀ ≤ q) (i : Fin (buildNq cov (q₀ := q₀) q)) :
    Measurable (buildΔ cov hq i) := by
  have hrw : buildΔ cov hq i
      = (Finset.univ : Finset ↥(Finset.Icc q₀ q)).inf' (univ_Icc_nonempty hq)
          (fun p => (fun x => cellWidth cov i p x)) := by
    funext x
    rw [Finset.inf'_apply]
    rfl
  rw [hrw]
  refine Finset.inf'_induction (p := fun g : Ω → ℝ => Measurable g) _ _
    (fun (a : Ω → ℝ) (ha : Measurable a) (b : Ω → ℝ) (hb : Measurable b) =>
      Measurable.inf' ha hb)
    (fun p _ => cellWidth_meas cov i p)

/-- `Δ q i ∈ L²(P)`: the `inf'` is pointwise sandwiched `0 ≤ Δ q i ≤ width_q`
(the top-level width), and the top-level width is in `L²(P)`. We bound `|Δ q i|`
pointwise by `width_q` and conclude via `MemLp.mono`. -/
lemma buildΔ_memLp {q : ℕ} (hq : q₀ ≤ q) (i : Fin (buildNq cov (q₀ := q₀) q)) :
    MemLp (buildΔ cov hq i) 2 P := by
  set pq : ↥(Finset.Icc q₀ q) := ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩⟩ with hpq
  -- the top-level width is in L²
  have htop : MemLp (fun x => cellWidth cov i pq x) 2 P :=
    ((cov q).bracket (cellIdx cov i pq)).memLp_upper.sub
      ((cov q).bracket (cellIdx cov i pq)).memLp_lower
  refine MemLp.mono htop ((buildΔ_meas cov hq i).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- `0 ≤ Δ q i x ≤ width_q x`, both nonneg (bracket lower ≤ upper)
  have hle_top : buildΔ cov hq i x ≤ cellWidth cov i pq x := by
    unfold buildΔ
    exact Finset.inf'_le _ (Finset.mem_univ pq)
  have hnonneg : 0 ≤ buildΔ cov hq i x := by
    unfold buildΔ
    refine Finset.le_inf' _ _ (fun p _ => ?_)
    unfold cellWidth
    have := ((cov p.1).bracket (cellIdx cov i p)).isBracket x
    linarith [this]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hwnonneg : 0 ≤ cellWidth cov i pq x := le_trans hnonneg hle_top
  rw [abs_of_nonneg hwnonneg]
  exact hle_top

/-- The `L²(P)`-size bound: `‖Δ q i‖_{P,2} ≤ scale q`. The min-of-widths `Δ q i` is
pointwise `≤` the top-level width `width_q` (and `≥ 0`), and the top-level bracket is
a `scale q`-bracket (`size_lt`). So `eLpNorm (Δ q i) ≤ eLpNorm width_q < ofReal (scale q)`
via `eLpNorm_mono_ae_real`. With the offset scale `scale q = (1/2)^(q−q₀)·δ` fed by the
constructors, this is the offset `L²`-decay. -/
lemma buildΔ_L2_le {q : ℕ} (hq : q₀ ≤ q) (i : Fin (buildNq cov (q₀ := q₀) q)) :
    eLpNorm (buildΔ cov hq i) 2 P ≤ ENNReal.ofReal (scale q) := by
  -- `Δ q i ≤ width_q` pointwise (in absolute value, both nonneg), then `width_q`'s
  -- `eLpNorm` is `< ofReal (scale q)` by `size_lt` (note `cellWidth cov i ⟨q,…⟩ = ub − lb`
  -- of the top-level bracket, since `cellIdx cov i ⟨q,…⟩ = topIdx cov hq i` by `rfl`).
  have hbound : eLpNorm (buildΔ cov hq i) 2 P
      ≤ eLpNorm (fun x => (cov q).ub (topIdx cov hq i) x
          - (cov q).lb (topIdx cov hq i) x) 2 P := by
    refine eLpNorm_mono_ae_real (Filter.Eventually.of_forall (fun x => ?_))
    have hle_top : buildΔ cov hq i x
        ≤ cellWidth cov i ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩⟩ x :=
      Finset.inf'_le _ (Finset.mem_univ _)
    have hnonneg : 0 ≤ buildΔ cov hq i x := by
      refine Finset.le_inf' _ _ (fun p _ => ?_)
      unfold cellWidth
      have := ((cov p.1).bracket (cellIdx cov i p)).isBracket x
      linarith [this]
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle_top
  exact le_trans hbound (le_of_lt ((cov q).bracket (topIdx cov hq i)).size_lt)

/-- The assignment tuple at level `q` is the restriction of the tuple at level
`q+1`: the bracket index `assignIdx (cov p)` depends only on `p`, never on the
level `q`. The membership coercion `Icc q₀ q → Icc q₀ (q + 1)` is by transitivity
through `le_succ`. -/
lemma assignTuple_restrict {q : ℕ} {f : Ω → ℝ} (hf : f ∈ F)
    (p : ↥(Finset.Icc q₀ q)) :
    assignTuple cov q₀ (q + 1) hf
        ⟨p.1, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp p.2).1,
          le_trans (Finset.mem_Icc.mp p.2).2 (Nat.le_succ q)⟩⟩
      = assignTuple cov q₀ q hf p := rfl

/-- The partitions are successive refinements: each level-`(q + 1)` cell is
contained in some level-`q` cell. -/
lemma buildCell_refines {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (buildNq cov (q₀ := q₀) (q + 1))) :
    ∃ j, buildCell cov (q₀ := q₀) (q + 1) i ⊆ buildCell cov (q₀ := q₀) q j := by
  -- pick a witness `f₀` of the (q + 1)-cell, take its level-q index `j` via cover
  obtain ⟨f₀, hf₀, hf₀t⟩ := (decode cov (q₀ := q₀) (q + 1) i).2
  obtain ⟨j, hj⟩ := buildCell_cover cov hq hf₀
  refine ⟨j, ?_⟩
  rintro f ⟨hfF, hft⟩
  rw [mem_buildCell]
  refine ⟨hfF, ?_⟩
  -- `f` and `f₀` share the (q + 1)-tuple, hence share the level-q restriction,
  -- which equals the cell-`j` tuple (witnessed by `f₀` via `hj`).
  obtain ⟨hf₀F, hf₀j⟩ := hj
  -- assignTuple q f = assignTuple q f₀, because both restrict from the (q + 1)-tuple
  -- which both share.
  have hshare : ∀ p : ↥(Finset.Icc q₀ (q + 1)),
      assignTuple cov q₀ (q + 1) hfF p = assignTuple cov q₀ (q + 1) hf₀ p := by
    intro p
    rw [hft, hf₀t]
  -- restrict to level q
  funext p
  calc assignTuple cov q₀ q hfF p
      = assignTuple cov q₀ (q + 1) hfF ⟨p.1, Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp p.2).1, le_trans (Finset.mem_Icc.mp p.2).2 (Nat.le_succ q)⟩⟩ :=
        (assignTuple_restrict cov hfF p).symm
    _ = assignTuple cov q₀ (q + 1) hf₀ ⟨p.1, Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp p.2).1, le_trans (Finset.mem_Icc.mp p.2).2 (Nat.le_succ q)⟩⟩ :=
        hshare _
    _ = assignTuple cov q₀ q hf₀ p := assignTuple_restrict cov hf₀ p
    _ = (decode cov (q₀ := q₀) q j).1 p := by rw [hf₀j]

/-- **Cell-tuple restriction across one refinement step.** If the level-`(q+1)`
cell `i` sits inside the level-`q` cell `j`, then for every level `p ∈ [q₀, q]` the
two cells choose the **same** bracket index: `cellIdx (q+1) i` restricted to `[q₀,q]`
equals `cellIdx q j`. This is the index form of `assignTuple_restrict` lifted to the
decoded cell tuples, and is the combinatorial core of `buildΔ_succ_le_parent`. -/
lemma cellIdx_succ_restrict {q : ℕ}
    (i : Fin (buildNq cov (q₀ := q₀) (q + 1))) {j : Fin (buildNq cov (q₀ := q₀) q)}
    (hsub : buildCell cov (q₀ := q₀) (q + 1) i ⊆ buildCell cov (q₀ := q₀) q j)
    (p : ↥(Finset.Icc q₀ q)) :
    cellIdx cov i ⟨p.1, Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp p.2).1, le_trans (Finset.mem_Icc.mp p.2).2 (Nat.le_succ q)⟩⟩
      = cellIdx cov j p := by
  -- a witness `f₀` of cell `(q+1) i` (whose tuple is the decoded cell-`i` tuple);
  -- it lies in cell `q j` by `hsub`, so its level-`q` tuple is the cell-`j` tuple.
  obtain ⟨f₀, hf₀, hf₀t⟩ := (decode cov (q₀ := q₀) (q + 1) i).2
  have hf₀i : f₀ ∈ buildCell cov (q₀ := q₀) (q + 1) i := ⟨hf₀, hf₀t⟩
  obtain ⟨hf₀F, hf₀j⟩ := hsub hf₀i
  -- unfold both `cellIdx`s through the witness's assignment tuple.
  unfold cellIdx
  rw [← hf₀t, ← hf₀j]
  exact assignTuple_restrict cov hf₀F p

/-- **Oscillation nesting monotonicity.**
`buildΔ (q+1) i ≤ buildΔ q j` pointwise whenever `cell (q+1) i ⊆ cell q j`: the
child's min ranges over `[q₀, q+1]`, which (by `cellIdx_succ_restrict`) contains the
exact same per-level widths as the parent's min over `[q₀, q]` *plus* the extra
level-`(q+1)` width. A min over more terms is `≤` a min over fewer, so the child's
min is `≤` the parent's. The structure field `Δ_succ_le_parent` is this lemma at
`j = (refines hq i).choose`. -/
lemma buildΔ_succ_le_parent {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin (buildNq cov (q₀ := q₀) (q + 1)))
    {j : Fin (buildNq cov (q₀ := q₀) q)}
    (hsub : buildCell cov (q₀ := q₀) (q + 1) i ⊆ buildCell cov (q₀ := q₀) q j)
    (x : Ω) :
    buildΔ cov (Nat.le_succ_of_le hq) i x ≤ buildΔ cov hq j x := by
  unfold buildΔ
  -- bound the parent's min from below by the child's min, term by term: every
  -- parent level `p ∈ [q₀,q]` embeds into `[q₀,q+1]` with the SAME width
  -- (`cellIdx_succ_restrict`), and the child's `inf'` is ≤ each of its terms.
  refine Finset.le_inf' _ _ (fun p _ => ?_)
  -- the embedded index of `p` into `Icc q₀ (q+1)`
  set p' : ↥(Finset.Icc q₀ (q + 1)) := ⟨p.1, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp p.2).1, le_trans (Finset.mem_Icc.mp p.2).2 (Nat.le_succ q)⟩⟩
    with hp'
  -- child's min ≤ its p'-term
  refine le_trans (Finset.inf'_le _ (Finset.mem_univ p')) ?_
  -- the p'-term of the child equals the p-term of the parent (same width):
  -- `cellIdx cov i p' = cellIdx cov j p` and `p'.1 = p.1` (defeq).
  have hidx : cellIdx cov i p' = cellIdx cov j p := cellIdx_succ_restrict cov i hsub p
  have heq : cellWidth cov i p' x = cellWidth cov j p x := by
    unfold cellWidth; rw [hidx]
  exact le_of_eq heq

/-- `Nq q ≤ ∏_{p ∈ [q₀, q]} (cov p).k`: the achieved tuples are a subset of all
tuples, whose count is the product of the per-level bracket counts. -/
lemma buildNq_card_le (q : ℕ) :
    buildNq cov (q₀ := q₀) q ≤ ∏ p ∈ Finset.Icc q₀ q, (cov p).k := by
  classical
  have h1 : buildNq cov (q₀ := q₀) q ≤ Fintype.card (LevelTuple cov q₀ q) := by
    unfold buildNq AchievedTuple
    exact Fintype.card_subtype_le _
  refine le_trans h1 ?_
  -- card of the Pi type
  have h2 : Fintype.card (LevelTuple cov q₀ q)
      = ∏ p : ↥(Finset.Icc q₀ q), (cov p.1).k := by
    unfold LevelTuple
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
  rw [h2]
  -- convert product over subtype to product over the Finset
  rw [Finset.prod_coe_sort (Finset.Icc q₀ q) (fun p => (cov p).k)]

/-- **Construction of a nested bracketing partition from per-level covers.**

Given, for each level `p`, the bundled data of a finite `L²(P)`-bracketing
cover of `F` at size `2^{−p}`, the joint-fiber construction above assembles a
`NestedBracketPartition` with scale constant `C = 1`: cells are fibers of the
single-valued per-level assignment, so they are disjoint and cover `F`; each
cell sits inside its top-level bracket, giving the oscillation envelope
`Δ = ub − lb` with `‖Δ‖_{P,2} ≤ 2^{−q}`; restriction of the assignment tuple
makes the partitions successive refinements; and the achieved tuples number at
most `∏_{p=q₀}^{q} N_p`.

The hypothesis `hmin` records that the supplied per-level cover is *minimal*
(size `≤ N_{[]}((1/2)^(p−q₀), F, L²(P))`, at the **offset** scale),
which the `coverCard_le` structure field requires; arbitrary covers cannot
satisfy it (the cover size only bounds the bracketing number from *above*). For
the canonical construction from a finite-entropy hypothesis,
`nestedBracketPartition_of_finiteEntropy` discharges `hmin` automatically by
feeding minimal covers from `exists_minimal_bracketingCover`.

The per-level cover is supplied at the **offset** scale `(1/2)^(p−q₀)`:
level `q₀` sits at scale `1`, level `q₀ + k` at scale `(1/2)^k`, so the
oscillation envelope `Δ = inf'_p (ub − lb)` has `‖Δ‖_{P,2} ≤ (1/2)^(q−q₀)`.

vdV §19.6 p.286-287: the nested-partition paragraph in the proof of
Lemma 19.34. -/
noncomputable def nestedBracketPartition_of_covers (q₀ : ℕ)
    (cov : (p : ℕ) → BracketingCoverData F ((1 / 2 : ℝ) ^ (p - q₀)) P)
    (hmin : ∀ {p : ℕ}, q₀ ≤ p →
      ((cov p).k : ℕ∞) ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀)) F 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    NestedBracketPartition F P q₀ 1 where
  Nq q := buildNq cov (q₀ := q₀) q
  coverCard p := (cov p).k
  cell q i := buildCell cov (q₀ := q₀) q i
  π q i := buildπ cov (q₀ := q₀) i
  Δ q i := if hq : q₀ ≤ q then buildΔ cov hq i else 0
  cover hq f hf := buildCell_cover cov hq hf
  cell_subset _ i := buildCell_subset cov i
  disjoint _ i j hij := buildCell_disjoint cov i j hij
  cell_nonempty _ i := buildCell_nonempty cov i
  refines hq i := buildCell_refines cov hq i
  π_mem _ i := buildπ_mem cov i
  π_meas _ i := buildπ_meas cov hF_meas i
  diam hq i f hf g hg x := by
    rw [dif_pos hq]; exact buildΔ_diam cov hq i hf hg x
  Δ_meas hq i := by rw [dif_pos hq]; exact buildΔ_meas cov hq i
  Δ_memLp hq i := by rw [dif_pos hq]; exact buildΔ_memLp cov hq i
  Δ_L2_le hq i := by
    rw [dif_pos hq]
    -- `scale q = (1/2)^(q−q₀)`; the field wants `1·(1/2)^(q−q₀)`.
    refine le_trans (buildΔ_L2_le (scale := fun p => (1 / 2 : ℝ) ^ (p - q₀)) cov hq i) ?_
    apply ENNReal.ofReal_le_ofReal
    rw [one_mul]
  Δ_succ_le_parent hq i x := by
    rw [dif_pos (Nat.le_succ_of_le hq), dif_pos hq]
    exact buildΔ_succ_le_parent cov hq i (buildCell_refines cov hq i).choose_spec x
  card_le hq := buildNq_card_le cov _
  coverCard_le hp := by
    -- scale constant `C = 1`, so `(1/2)^(p−q₀) * 1 = (1/2)^(p−q₀)`.
    rw [mul_one]; exact hmin hp

/-- A **minimal** finite `L²(P)`-bracketing cover of `F` at scale `ε`, packaged
as `BracketingCoverData`, whose size equals `bracketingNumber ε F 2 P`. Built by
choosing the achieving cover of `exists_minimal_bracketingCover`. -/
noncomputable def minimalCoverData (ε : ℝ) (h : HasFiniteBracketingCover F ε 2 P) :
    BracketingCoverData F ε P :=
  ⟨(exists_minimal_bracketingCover h).choose,
    (exists_minimal_bracketingCover h).choose_spec.choose,
    (exists_minimal_bracketingCover h).choose_spec.choose_spec.choose,
    (exists_minimal_bracketingCover h).choose_spec.choose_spec.choose_spec.1,
    (exists_minimal_bracketingCover h).choose_spec.choose_spec.choose_spec.2.1⟩

/-- The size of the minimal cover equals the bracketing number. -/
lemma minimalCoverData_k (ε : ℝ) (h : HasFiniteBracketingCover F ε 2 P) :
    ((minimalCoverData ε h).k : ℕ∞) = bracketingNumber ε F 2 P :=
  ((exists_minimal_bracketingCover h).choose_spec.choose_spec.choose_spec.2.2).symm

/-- **Construction of a nested bracketing partition from a finite-entropy
hypothesis.**

Given `δ > 0` and, for every level `p ≥ q₀`, a finite `L²(P)`-bracketing cover of
`F` at scale `(1/2)^p·δ`, this assembles a `NestedBracketPartition` with scale
constant `C = δ` whose per-level cover cardinalities are *minimal* — equal to
`bracketingNumber ((1/2)^p·δ, F, L²(P))`. It does so by feeding the minimal covers
`minimalCoverData` (whose size is exactly the bracketing number) to the joint-fiber
construction. The `coverCard_le` field then holds *with equality* on `p ≥ q₀`.

The `p < q₀` slots of the cover family are never read by any field proof (every
field is guarded by `q₀ ≤ q` / `q₀ ≤ p`); they are filled by weakening the
level-`q₀` cover (at scale `(1/2)^0·δ = δ`) to the larger scale `(1/2)^(p−q₀)·δ`
via `BracketingCoverData.monoEps` (a smaller-scale cover is a fortiori a
larger-scale one; here `p < q₀ ⇒ q₀ − q₀ = 0 ≤ p − q₀ = 0`, so the scale is the
same `δ` and the weakening is `le_rfl`), purely to make the family a total
function `ℕ → BracketingCoverData F ((1/2)^(p−q₀)·δ) P`.

The cover is supplied at the **offset** scale `(1/2)^(p−q₀)·δ`, so the
`coverCard_le` field holds with equality at the offset bracketing number and
`Δ_L2_le` carries the offset `(1/2)^(q−q₀)·δ` decay matching the dyadic series.

vdV §19.6 p.286-287: the nested-partition paragraph, built from the book's
*minimal* covers so that `√(log N_p)` is dominated by the entropy integrand. -/
noncomputable def nestedBracketPartition_of_finiteEntropy (q₀ : ℕ) {δ : ℝ}
    (_hδ : 0 < δ)
    (hcov : ∀ p, q₀ ≤ p → HasFiniteBracketingCover F ((1 / 2 : ℝ) ^ (p - q₀) * δ) 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    NestedBracketPartition F P q₀ δ :=
  -- The per-level cover family, minimal on `p ≥ q₀`, junk-but-typed on `p < q₀`.
  -- On `p < q₀` we have `p − q₀ = 0 = q₀ − q₀` (Nat truncated subtraction), so the
  -- scale `(1/2)^(p−q₀)·δ = δ` equals the level-`q₀` scale; the weakening is `le_rfl`.
  let cov : (p : ℕ) → BracketingCoverData F ((1 / 2 : ℝ) ^ (p - q₀) * δ) P := fun p =>
    if hp : q₀ ≤ p then minimalCoverData _ (hcov p hp)
    else (minimalCoverData _ (hcov q₀ le_rfl)).monoEps
      (by
        -- `q₀ − q₀ = 0` and `p − q₀ = 0` (since `p < q₀`), so both scales are `δ`.
        have h1 : q₀ - q₀ = 0 := Nat.sub_self q₀
        have h2 : p - q₀ = 0 := Nat.sub_eq_zero_of_le (le_of_lt (lt_of_not_ge hp))
        rw [h1, h2])
  { Nq := fun q => buildNq cov (q₀ := q₀) q
    coverCard := fun p => (cov p).k
    cell := fun q i => buildCell cov (q₀ := q₀) q i
    π := fun q i => buildπ cov (q₀ := q₀) i
    Δ := fun q i => if hq : q₀ ≤ q then buildΔ cov hq i else 0
    cover := fun hq f hf => buildCell_cover cov hq hf
    cell_subset := fun _ i => buildCell_subset cov i
    disjoint := fun _ i j hij => buildCell_disjoint cov i j hij
    cell_nonempty := fun _ i => buildCell_nonempty cov i
    refines := fun hq i => buildCell_refines cov hq i
    π_mem := fun _ i => buildπ_mem cov i
    π_meas := fun _ i => buildπ_meas cov hF_meas i
    diam := fun hq i f hf g hg x => by
      rw [dif_pos hq]; exact buildΔ_diam cov hq i hf hg x
    Δ_meas := fun hq i => by rw [dif_pos hq]; exact buildΔ_meas cov hq i
    Δ_memLp := fun hq i => by rw [dif_pos hq]; exact buildΔ_memLp cov hq i
    Δ_L2_le := fun hq i => by
      rw [dif_pos hq]
      refine le_trans
        (buildΔ_L2_le (scale := fun p => (1 / 2 : ℝ) ^ (p - q₀) * δ) cov hq i) ?_
      apply ENNReal.ofReal_le_ofReal
      -- `buildΔ_L2_le` gives `scale q = (1/2)^(q−q₀)·δ`; the field wants `δ·(1/2)^(q−q₀)`.
      rw [mul_comm]
    Δ_succ_le_parent := fun hq i x => by
      rw [dif_pos (Nat.le_succ_of_le hq), dif_pos hq]
      exact buildΔ_succ_le_parent cov hq i (buildCell_refines cov hq i).choose_spec x
    card_le := fun hq => buildNq_card_le cov _
    coverCard_le := fun {p} hp => by
      -- on `p ≥ q₀`, the cover is the minimal one, so its size = bracketingNumber.
      show ((cov p).k : ℕ∞) ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δ) F 2 P
      have hcovp : cov p = minimalCoverData _ (hcov p hp) := dif_pos hp
      rw [hcovp, minimalCoverData_k] }

/-!
## Clamped construction over the truncated class

For the chaining argument's *envelope-truncation regime* (vdV p.286), one builds the
nested partition not over `G` itself but over the **truncated class**
`truncateClass G M` whose members are clamped into `[−M, M]`, with all brackets
likewise clamped at `±M`. This gives a uniform `Δ ≤ 2M` envelope bound (needed to
control the truncated empirical process) while preserving every nested-partition
structure field.

**Why projection, not zero-out.** The truncation here is the *projection*
`clampFn M g x = max (min (g x) M) (−M)` (clamp `g x` into `[−M, M]`), **not** the
indicator zero-out `g · 1{|g| ≤ M}`. Clamping the supplied `G`-brackets at `±M`
cannot simultaneously satisfy `IsBracket` (`lb' ≤ ub'`), the covering property, and
the width-shrink `ub' − lb' ≤ ub − lb` (hence `size_lt`) for the indicator
truncation: a bracket `[0.9M, 1.1M]` straddling the truncation boundary must, after
clamping, contain both `0` (the truncated value of points where `g > M`) and the
range `[0.9M, M]` (truncated values of points where `g ≤ M`), forcing clamped width
`≥ M` while the original width is only `0.2M`. The **projection** truncation has no
such obstruction: `clampFn M` is monotone, `1`-Lipschitz, and `[−M, M]`-valued, so
clamping both bracket endpoints by the same `clampFn M` shrinks width, preserves
order, and keeps `g'` inside its clamped bracket. -/
section Clamp

variable {G : Set (Ω → ℝ)}

/-- Clamp a real number into `[−M, M]` (projection onto the interval). -/
def clampReal (M t : ℝ) : ℝ := max (min t M) (-M)

/-- `clampReal` is monotone in its argument (projection onto an interval is
order-preserving). -/
lemma clampReal_mono (M : ℝ) {a b : ℝ} (hab : a ≤ b) :
    clampReal M a ≤ clampReal M b := by
  unfold clampReal
  rcases le_total a M with h1 | h1 <;> rcases le_total b M with h2 | h2 <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- The clamped width shrinks: `clampReal M b − clampReal M a ≤ b − a` for `a ≤ b`
(projection onto an interval is `1`-Lipschitz, and monotone, so the gap cannot
grow). -/
lemma clampReal_width_le (M : ℝ) {a b : ℝ} (hab : a ≤ b) :
    clampReal M b - clampReal M a ≤ b - a := by
  unfold clampReal
  rcases le_total a M with h1 | h1 <;> rcases le_total b M with h2 | h2 <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- Projection onto `[-M, M]` is `1`-Lipschitz. -/
lemma abs_clampReal_sub_clampReal_le (M a b : ℝ) :
    |clampReal M a - clampReal M b| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · have hmono := clampReal_mono M hab
    rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using clampReal_width_le M hab
  · have hmono := clampReal_mono M hba
    rw [abs_of_nonneg (sub_nonneg.mpr hmono), abs_of_nonneg (sub_nonneg.mpr hba)]
    exact clampReal_width_le M hba

/-- The clamped width is at most `2M`: both clamped endpoints lie in `[−M, M]`. -/
lemma clampReal_width_le_two (M : ℝ) (hM : 0 ≤ M) (a b : ℝ) :
    clampReal M b - clampReal M a ≤ 2 * M := by
  unfold clampReal
  rcases le_total b M with h2 | h2 <;> rcases le_total a M with h1 | h1 <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- `clampReal` is a contraction toward `0`: `|clampReal M t| ≤ |t|` when `0 ≤ M`. -/
lemma abs_clampReal_le (M : ℝ) (hM : 0 ≤ M) (t : ℝ) : |clampReal M t| ≤ |t| := by
  rw [abs_le]
  unfold clampReal
  rcases le_total t M with h1 | h1 <;> rcases le_total (-M) t with h2 | h2 <;>
    rw [max_def, min_def] <;> split_ifs <;> constructor <;>
    rcases abs_cases t with ⟨e, _⟩ | ⟨e, _⟩ <;> rw [e] <;> linarith

/-- The **projection truncation** of `g` at level `M`: clamp each value into
`[−M, M]`. -/
def clampFn (M : ℝ) (g : Ω → ℝ) : Ω → ℝ := fun x => clampReal M (g x)

/-- The **truncated class**: every member of `G`, projected into `[−M, M]`. -/
def truncateClass (G : Set (Ω → ℝ)) (M : ℝ) : Set (Ω → ℝ) :=
  {g' | ∃ g ∈ G, g' = clampFn M g}

/-- A value already in `[−M, M]` is fixed by `clampReal`. -/
lemma clampReal_of_mem {M t : ℝ} (h : |t| ≤ M) : clampReal M t = t := by
  rw [abs_le] at h
  unfold clampReal
  rw [min_eq_left h.2, max_eq_left h.1]

/-- `clampFn M g` is measurable when `g` is. -/
lemma clampFn_measurable {M : ℝ} {g : Ω → ℝ} (hg : Measurable g) :
    Measurable (clampFn M g) :=
  (hg.min measurable_const).max measurable_const

omit [MeasurableSpace Ω] in
/-- Every member of the truncated class `truncateClass G M` is `[−M, M]`-valued. -/
lemma truncateClass_abs_le {M : ℝ} (hM : 0 ≤ M) {g' : Ω → ℝ}
    (hg' : g' ∈ truncateClass G M) (x : Ω) : |g' x| ≤ M := by
  obtain ⟨g, _, rfl⟩ := hg'
  rw [abs_le]
  refine ⟨le_max_right _ _, ?_⟩
  change max (min (g x) M) (-M) ≤ M
  exact max_le (min_le_right _ _) (by linarith)

/-- `clampFn M g ∈ L²(P)` when `g ∈ L²(P)` (the projection is a contraction
toward `0`, so `|clampFn M g| ≤ |g|` pointwise). -/
lemma clampFn_memLp {M : ℝ} (hM : 0 ≤ M) {g : Ω → ℝ} (hg : MemLp g 2 P) :
    MemLp (clampFn M g) 2 P := by
  refine hg.mono ?_ (Filter.Eventually.of_forall (fun x => ?_))
  · exact (((hg.aestronglyMeasurable.aemeasurable.min aemeasurable_const).max
      aemeasurable_const).aestronglyMeasurable)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs]; exact abs_clampReal_le M hM (g x)

/-- Clamping the lower/upper bounds of an `ε`-bracket at `±M` yields an `ε`-bracket
of the clamped functions: `IsBracket` is preserved by monotonicity of `clampReal`,
the width shrinks (so `size_lt` survives), and measurability/`MemLp` are inherited
through the contraction bound. -/
lemma isEpsBracket_clamp {ε : ℝ} {l u : Ω → ℝ} (hM : 0 ≤ M)
    (h : IsEpsBracket ε l u 2 P) :
    IsEpsBracket ε (clampFn M l) (clampFn M u) 2 P := by
  refine ⟨fun x => clampReal_mono M (h.isBracket x),
    clampFn_measurable h.measurable_lower, clampFn_measurable h.measurable_upper,
    clampFn_memLp hM h.memLp_lower, clampFn_memLp hM h.memLp_upper, ?_⟩
  refine lt_of_le_of_lt ?_ h.size_lt
  refine eLpNorm_mono_ae_real (Filter.Eventually.of_forall (fun x => ?_))
  -- `0 ≤ clampFn M u x − clampFn M l x ≤ u x − l x`.
  have hbr : l x ≤ u x := h.isBracket x
  change |clampReal M (u x) - clampReal M (l x)| ≤ u x - l x
  have hnn : 0 ≤ clampReal M (u x) - clampReal M (l x) :=
    sub_nonneg.mpr (clampReal_mono M hbr)
  rw [abs_of_nonneg hnn]
  exact clampReal_width_le M hbr

/-- `clampReal M` is continuous (it is `max (min · M) (−M)`, a composition of the
continuous lattice operations). -/
lemma continuous_clampReal (M : ℝ) : Continuous (clampReal M) := by
  unfold clampReal
  exact (continuous_id.min continuous_const).max continuous_const

/-- **Pointwise-density is inherited by the truncated (clamped) class.**

If `G` is `EmpProcPointwiseDense` and `0 ≤ M`, then so is `truncateClass G M`.
The countable separant is the clamp-image `clampFn M '' G'` of `G`'s separant
`G'`; pointwise density transports through the continuity of `clampReal M`
(`φₘ x → g x` gives `clampReal M (φₘ x) → clampReal M (g x)`); and the original
integrable envelope `Φ` still dominates, since the clamp is a contraction toward
`0` (`|clampReal M t| ≤ |t|`). This transports the density input used by
uniform-entropy maximal inequalities to their clamped classes. -/
theorem EmpProcPointwiseDense_truncateClass {G : Set (Ω → ℝ)} {M : ℝ}
    (hM : 0 ≤ M) (h : EmpProcPointwiseDense G P) :
    EmpProcPointwiseDense (truncateClass G M) P := by
  obtain ⟨G', hG'sub, hG'ct, hApprox, Φ, hΦint, hΦdom⟩ := h
  -- countable separant: the clamp-image of `G'`
  refine ⟨clampFn M '' G', ?_, hG'ct.image _, ?_, Φ, hΦint, ?_⟩
  · -- `clampFn M '' G' ⊆ truncateClass G M`
    rintro _ ⟨g', hg', rfl⟩
    exact ⟨g', hG'sub hg', rfl⟩
  · -- density: each clamped `g' ∈ truncateClass G M` is a pointwise limit
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨φ, hφmem, hφlim⟩ := hApprox g hg
    refine ⟨fun m => clampFn M (φ m), fun m => ⟨φ m, hφmem m, rfl⟩, fun x => ?_⟩
    exact ((continuous_clampReal M).tendsto (g x)).comp (hφlim x)
  · -- envelope: the clamp contracts toward `0`, so `Φ` still dominates
    rintro _ ⟨g, hg, rfl⟩ x
    exact (abs_clampReal_le M hM (g x)).trans (hΦdom g hg x)

end Clamp

/-- Clamp a `BracketingCoverData` of `G` at `±M` into a `BracketingCoverData` of the
truncated class `truncateClass G M`: each bracket `[lb i, ub i]` becomes
`[clampFn M (lb i), clampFn M (ub i)]`, of the same cardinality. The clamped
brackets are genuine `ε`-brackets (`isEpsBracket_clamp`) and still cover the
truncated class: for `g' = clampFn M g` with `g ∈ G`, the original bracket of `g`
clamps to a bracket containing `g'` (monotonicity of `clampReal`). -/
noncomputable def BracketingCoverData.clamp {G : Set (Ω → ℝ)} {ε : ℝ} (M : ℝ)
    (hM : 0 ≤ M) (cov : BracketingCoverData G ε P) :
    BracketingCoverData (truncateClass G M) ε P where
  k := cov.k
  lb i := clampFn M (cov.lb i)
  ub i := clampFn M (cov.ub i)
  bracket i := isEpsBracket_clamp hM (cov.bracket i)
  covers := by
    rintro g' ⟨g, hgG, rfl⟩
    obtain ⟨i, hi⟩ := cov.covers g hgG
    refine ⟨i, fun x => ?_⟩
    -- `clampFn M (lb i) x ≤ clampFn M g x ≤ clampFn M (ub i) x` by monotonicity,
    -- since `lb i x ≤ g x ≤ ub i x`.
    exact ⟨clampReal_mono M (hi x).1, clampReal_mono M (hi x).2⟩

/-- A finite `ε`-bracketing cover of `G` clamps to a finite `ε`-bracketing cover of
the truncated class `truncateClass G M`. Existence form, used to feed the truncated
class to `minimalCoverData`. -/
lemma hasFiniteBracketingCover_truncateClass {G : Set (Ω → ℝ)} {ε : ℝ} (M : ℝ)
    (hM : 0 ≤ M) (h : HasFiniteBracketingCover G ε 2 P) :
    HasFiniteBracketingCover (truncateClass G M) ε 2 P := by
  set cov := (BracketingCoverData.ofHasFiniteCover h).clamp M hM with hcov
  exact ⟨cov.k, cov.lb, cov.ub, cov.bracket, cov.covers⟩

/-- **Clamp the brackets of a cover of `truncateClass G M`, keeping the same class.**
Given any cover of the truncated class, clamping all bracket endpoints at `±M`
yields another cover of the *same* truncated class (members are already
`[−M, M]`-valued, so clamping the brackets still contains them: `clampReal M (g' x)
= g' x` by `clampReal_of_mem`), with every bracket width `≤ 2M`. The cardinality
is preserved (same `k`). This is the key step letting the *minimal* truncated-class
cover (whose cardinality is the bracketing number) acquire the uniform `≤ 2M` width
bound that the envelope lemma needs. -/
noncomputable def BracketingCoverData.clampBrackets {G : Set (Ω → ℝ)} {ε : ℝ} (M : ℝ)
    (hM : 0 ≤ M) (cov : BracketingCoverData (truncateClass G M) ε P) :
    BracketingCoverData (truncateClass G M) ε P where
  k := cov.k
  lb i := clampFn M (cov.lb i)
  ub i := clampFn M (cov.ub i)
  bracket i := isEpsBracket_clamp hM (cov.bracket i)
  covers := by
    intro g' hg'
    obtain ⟨i, hi⟩ := cov.covers g' hg'
    refine ⟨i, fun x => ?_⟩
    -- `g' x ∈ [−M, M]`, so `clampReal M (g' x) = g' x`; monotonicity gives the bound.
    have hfix : clampReal M (g' x) = g' x :=
      clampReal_of_mem (truncateClass_abs_le hM hg' x)
    refine ⟨?_, ?_⟩
    · have := clampReal_mono M (hi x).1; rwa [hfix] at this
    · have := clampReal_mono M (hi x).2; rwa [hfix] at this

/-- `clampBrackets` preserves cardinality. -/
@[simp] lemma BracketingCoverData.clampBrackets_k {G : Set (Ω → ℝ)} {ε : ℝ} (M : ℝ)
    (hM : 0 ≤ M) (cov : BracketingCoverData (truncateClass G M) ε P) :
    (cov.clampBrackets M hM).k = cov.k := rfl

/-- Every bracket of a `clampBrackets`-clamped cover has width `≤ 2M`: its `ub`/`lb`
are `clampFn M …`, and both clamped endpoints lie in `[−M, M]`. -/
lemma BracketingCoverData.clampBrackets_width_le_two {G : Set (Ω → ℝ)} {ε : ℝ} (M : ℝ)
    (hM : 0 ≤ M) (cov : BracketingCoverData (truncateClass G M) ε P)
    (j : Fin (cov.clampBrackets M hM).k) (x : Ω) :
    (cov.clampBrackets M hM).ub j x - (cov.clampBrackets M hM).lb j x ≤ 2 * M :=
  clampReal_width_le_two M hM _ _

section ClampedConstruction

variable {q₀ : ℕ}

/-- The per-level clamped cover family over the truncated class `truncateClass G M`:
at level `p ≥ q₀`, the *minimal* `(1/2)^(p−q₀)·δ`-bracketing cover of the truncated
class (from clamping `G`'s cover), then clamped at `±M` so every bracket width is
`≤ 2M`; at `p < q₀`, the level-`q₀` minimal cover weakened to the (equal) scale.
Named (not a `let`) so the constructor and the `..._Δ_le` envelope lemma share the
same `cov`. -/
noncomputable def clampedCoverFamily (q₀ : ℕ) {δ : ℝ} (M : ℝ) (hM : 0 ≤ M)
    (hcov' : ∀ p, q₀ ≤ p →
      HasFiniteBracketingCover (truncateClass G M) ((1 / 2 : ℝ) ^ (p - q₀) * δ) 2 P) :
    (p : ℕ) → BracketingCoverData (truncateClass G M) ((1 / 2 : ℝ) ^ (p - q₀) * δ) P :=
  fun p =>
    if hp : q₀ ≤ p
    then (minimalCoverData _ (hcov' p hp)).clampBrackets M hM
    else (minimalCoverData _ (hcov' q₀ le_rfl)).monoEps
      (by
        have h1 : q₀ - q₀ = 0 := Nat.sub_self q₀
        have h2 : p - q₀ = 0 := Nat.sub_eq_zero_of_le (le_of_lt (lt_of_not_ge hp))
        rw [h1, h2])

/-- On `p ≥ q₀`, the clamped cover family is the bracket-clamped minimal cover. -/
lemma clampedCoverFamily_of_le (q₀ : ℕ) {δ : ℝ} (M : ℝ) (hM : 0 ≤ M)
    {hcov' : ∀ p, q₀ ≤ p →
      HasFiniteBracketingCover (truncateClass G M) ((1 / 2 : ℝ) ^ (p - q₀) * δ) 2 P}
    {p : ℕ} (hp : q₀ ≤ p) :
    clampedCoverFamily q₀ M hM hcov' p = (minimalCoverData _ (hcov' p hp)).clampBrackets M hM :=
  dif_pos hp

/-- **Construction of a nested bracketing partition over the truncated class.**

Given `δ > 0`, a clamp level `M ≥ 0`, and, for every level `p ≥ q₀`, a finite
`L²(P)`-bracketing cover of `G` at scale `(1/2)^(p−q₀)·δ`, this builds a
`NestedBracketPartition` of the **truncated class** `truncateClass G M`. The
per-level cover is obtained by clamping `G`'s minimal cover at `±M` (via
`BracketingCoverData.clamp`); this keeps the cardinality equal to the minimal
truncated-class cover (so `coverCard_le` holds with equality at
`bracketingNumber (truncateClass G M)`) and clamps all bracket widths to `≤ 2M`
(so the separate `..._Δ_le` lemma gives the uniform `Δ ≤ 2M` envelope bound).

The construction is otherwise identical to `nestedBracketPartition_of_finiteEntropy`:
all six structure fields transfer through the clamped covers, the projection
truncation guaranteeing `IsBracket`, `covers`, and the width-shrink simultaneously.

vdV §19.6 p.286: the envelope-truncated chaining regime. -/
noncomputable def nestedBracketPartition_of_finiteEntropy_clamped (q₀ : ℕ) {δ : ℝ}
    (_hδ : 0 < δ) (M : ℝ) (hM : 0 ≤ M)
    (hcov : ∀ p, q₀ ≤ p → HasFiniteBracketingCover G ((1 / 2 : ℝ) ^ (p - q₀) * δ) 2 P)
    (hG_meas : ∀ g ∈ G, Measurable g) :
    NestedBracketPartition (truncateClass G M) P q₀ δ :=
  -- the truncated class admits a clamped cover at every level `p ≥ q₀`.
  let hcov' : ∀ p, q₀ ≤ p →
      HasFiniteBracketingCover (truncateClass G M) ((1 / 2 : ℝ) ^ (p - q₀) * δ) 2 P :=
    fun p hp => hasFiniteBracketingCover_truncateClass M hM (hcov p hp)
  -- members of the truncated class are measurable (clamp of a measurable `g`).
  let hT_meas : ∀ g' ∈ truncateClass G M, Measurable g' := by
    rintro g' ⟨g, hgG, rfl⟩; exact clampFn_measurable (hG_meas g hgG)
  -- the per-level cover family over the truncated class: clamp `G`'s minimal cover,
  -- so cardinality = bracketingNumber (truncateClass) AND every bracket width ≤ 2M.
  let cov : (p : ℕ) →
      BracketingCoverData (truncateClass G M) ((1 / 2 : ℝ) ^ (p - q₀) * δ) P :=
    clampedCoverFamily q₀ M hM hcov'
  { Nq := fun q => buildNq cov (q₀ := q₀) q
    coverCard := fun p => (cov p).k
    cell := fun q i => buildCell cov (q₀ := q₀) q i
    π := fun q i => buildπ cov (q₀ := q₀) i
    Δ := fun q i => if hq : q₀ ≤ q then buildΔ cov hq i else 0
    cover := fun hq f hf => buildCell_cover cov hq hf
    cell_subset := fun _ i => buildCell_subset cov i
    disjoint := fun _ i j hij => buildCell_disjoint cov i j hij
    cell_nonempty := fun _ i => buildCell_nonempty cov i
    refines := fun hq i => buildCell_refines cov hq i
    π_mem := fun _ i => buildπ_mem cov i
    π_meas := fun _ i => buildπ_meas cov hT_meas i
    diam := fun hq i f hf g hg x => by
      rw [dif_pos hq]; exact buildΔ_diam cov hq i hf hg x
    Δ_meas := fun hq i => by rw [dif_pos hq]; exact buildΔ_meas cov hq i
    Δ_memLp := fun hq i => by rw [dif_pos hq]; exact buildΔ_memLp cov hq i
    Δ_L2_le := fun hq i => by
      rw [dif_pos hq]
      refine le_trans
        (buildΔ_L2_le (scale := fun p => (1 / 2 : ℝ) ^ (p - q₀) * δ) cov hq i) ?_
      apply ENNReal.ofReal_le_ofReal
      rw [mul_comm]
    Δ_succ_le_parent := fun hq i x => by
      rw [dif_pos (Nat.le_succ_of_le hq), dif_pos hq]
      exact buildΔ_succ_le_parent cov hq i (buildCell_refines cov hq i).choose_spec x
    card_le := fun hq => buildNq_card_le cov _
    coverCard_le := fun {p} hp => by
      -- on `p ≥ q₀`, the cover is the clamped minimal cover of the truncated class,
      -- so its size = (minimal cover size) = bracketingNumber (truncateClass G M).
      show ((cov p).k : ℕ∞)
        ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δ) (truncateClass G M) 2 P
      have hcovp : cov p = (minimalCoverData _ (hcov' p hp)).clampBrackets M hM :=
        clampedCoverFamily_of_le q₀ M hM hp
      rw [hcovp]
      change ((minimalCoverData _ (hcov' p hp)).k : ℕ∞)
        ≤ bracketingNumber ((1 / 2 : ℝ) ^ (p - q₀) * δ) (truncateClass G M) 2 P
      rw [minimalCoverData_k] }

/-- **The uniform `Δ ≤ 2M` envelope bound for the clamped partition.** Because every
bracket of the clamped cover has width `clampReal M (ub) − clampReal M (lb) ≤ 2M`
(both clamped endpoints lie in `[−M, M]`), the oscillation envelope
`Δ q i = inf'_p width_p` is pointwise `≤ 2M`. This is a *separate* lemma, not a
structure field, because the clamp level `M` is `n`-dependent in the chaining
application (`M = √n · a'`). -/
lemma nestedBracketPartition_of_finiteEntropy_clamped_Δ_le (q₀ : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (M : ℝ) (hM : 0 ≤ M)
    (hcov : ∀ p, q₀ ≤ p → HasFiniteBracketingCover G ((1 / 2 : ℝ) ^ (p - q₀) * δ) 2 P)
    (hG_meas : ∀ g ∈ G, Measurable g) {q : ℕ} (hq : q₀ ≤ q)
    (i : Fin ((nestedBracketPartition_of_finiteEntropy_clamped q₀ hδ M hM hcov hG_meas).Nq q))
    (x : Ω) :
    (nestedBracketPartition_of_finiteEntropy_clamped q₀ hδ M hM hcov hG_meas).Δ q i x
      ≤ 2 * M := by
  -- the internal cover family of the constructor (matches the `let hcov'` / `let cov`).
  set hcov' : ∀ p, q₀ ≤ p →
      HasFiniteBracketingCover (truncateClass G M) ((1 / 2 : ℝ) ^ (p - q₀) * δ) 2 P :=
    fun p hp => hasFiniteBracketingCover_truncateClass M hM (hcov p hp) with hhcov'
  set cov := clampedCoverFamily q₀ M hM hcov' with hcovdef
  -- unfold the structure `Δ` to `buildΔ cov`, then bound by the `p = q` term.
  change (if hq' : q₀ ≤ q then buildΔ cov hq' i else 0) x ≤ 2 * M
  rw [dif_pos hq]
  unfold buildΔ
  set pq : ↥(Finset.Icc q₀ q) := ⟨q, Finset.mem_Icc.mpr ⟨hq, le_rfl⟩⟩ with hpq
  refine le_trans (Finset.inf'_le _ (Finset.mem_univ pq)) ?_
  -- the `pq`-width is `clampReal M (ub) − clampReal M (lb) ≤ 2M`.
  unfold cellWidth
  -- `↑pq = q` (defeq), and on `p = q ≥ q₀` the cover is the bracket-clamped minimal
  -- cover. Bound every `cov q`-width by `2M` (universally in the index, so no
  -- dependent rewrite on the specific `cellIdx`).
  have hwidth : ∀ j : Fin (cov q).k, (cov q).ub j x - (cov q).lb j x ≤ 2 * M := by
    have hcovq : cov q = (minimalCoverData _ (hcov' q hq)).clampBrackets M hM :=
      clampedCoverFamily_of_le q₀ M hM hq
    rw [hcovq]
    exact fun j => BracketingCoverData.clampBrackets_width_le_two M hM _ j x
  exact hwidth (cellIdx cov i pq)

end ClampedConstruction

end Construction

end AsymptoticStatistics.EmpiricalProcess
