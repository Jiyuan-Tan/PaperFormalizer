module
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

@[expose] public section

/-!
# Linear separation of labeled data in a real Hilbert space

Binary classification background for the maximal margin classifier: labeled data
`(x i, λ i)` with `λ i ∈ {±1}` is **linearly separated** by the affine hyperplane
`{y | ⟪y, v⟫ = c}` when every point lies strictly on its label's side, i.e.
`0 < λ i · (⟪x i, v⟫ − c)`.  We prove:

* the distance of a point to the hyperplane is `|⟪p, v⟫ − c| / ‖v‖`;
* a separating normal vector can always be replaced by its orthogonal projection onto
  the span of the data, without changing any of the constraint values.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 8, §§8.3–8.4, Definition 8.1 (linearly separable data), Lemma 8.2 (distance to an
affine hyperplane), Proposition 8.3 (the separating normal can be taken in the span of the data).

**Proof formalization notes.** Separation is encoded as $0 < \lambda_i(\langle x_i, v\rangle -
c)$, uniform over labels. `SeparatesData.ne_zero` requires *both* label signs to occur: with a
single sign the degenerate normal $v = 0$ (with a suitable offset) vacuously separates — e.g. all
labels $+1$ and $c = -1$ — so the book's implicit two-nonempty-classes assumption is made an
explicit hypothesis. The distance formula is proved via the orthogonal projection onto the span of
the normal, and span-reduction via `starProjection` identities on any closed subspace containing
the data.

**Bibliographic comments.** The geometry of separating hyperplanes for classification
goes back to R. A. Fisher (1936) and F. Rosenblatt's perceptron (1958); the Hilbert-space
formulation is standard in statistical learning theory, cf. V. N. Vapnik, *The Nature of
Statistical Learning Theory* (Springer, 1995).
-/

open scoped RealInnerProductSpace

namespace StatLean.NonparametricStatistics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (v : E) (c : ℝ) in
/-- The affine hyperplane `{y | ⟪y, v⟫ = c}` with normal vector `v` and offset `c`. -/
def hyperplane : Set E := {y : E | ⟪y, v⟫ = c}

/-- `(v, c)` **separates** the labeled data `(x, lab)`: every point lies strictly on the
side of the hyperplane prescribed by its `±1` label. -/
def SeparatesData {ι : Type*} (v : E) (c : ℝ) (x : ι → E) (lab : ι → ℝ) : Prop :=
  ∀ i, 0 < lab i * (⟪x i, v⟫ - c)

/-- Labeled data is **linearly separable** if some affine hyperplane separates it. -/
def LinearlySeparable {ι : Type*} (x : ι → E) (lab : ι → ℝ) : Prop :=
  ∃ (v : E) (c : ℝ), SeparatesData v c x lab

/-- A normal vector separating two *nonempty* classes is necessarily nonzero.  (With
only one label sign present, `v = 0` with a suitable offset vacuously "separates".) -/
theorem SeparatesData.ne_zero {ι : Type*} {v : E} {c : ℝ} {x : ι → E}
    {lab : ι → ℝ} (h : SeparatesData v c x lab) {iPos iNeg : ι}
    -- USER-INPUT: both classes are nonempty (a positive and a negative label occur)
    (hPos : 0 < lab iPos) (hNeg : lab iNeg < 0) : v ≠ 0 := by
  rintro rfl
  have h1 := h iPos
  have h2 := h iNeg
  rw [inner_zero_right, zero_sub] at h1 h2
  -- `h1` forces `c < 0`, `h2` forces `0 < c`.
  nlinarith

/-- **Distance to an affine hyperplane**: for `v ≠ 0`,
`d(p, {⟪·, v⟫ = c}) = |⟪p, v⟫ − c| / ‖v‖`. -/
theorem infDist_hyperplane [CompleteSpace E] (p : E) {v : E}
    -- LEAN-ONLY: nondegenerate normal vector; for `v = 0` the "hyperplane" is `∅` or `E`
    (hv : v ≠ 0) (c : ℝ) :
    Metric.infDist p (hyperplane v c) = |⟪p, v⟫ - c| / ‖v‖ := by
  have hv2 : (0 : ℝ) < ‖v‖ ^ 2 := by positivity
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  -- the foot of the perpendicular from `p`
  set t : ℝ := (⟪p, v⟫ - c) / ‖v‖ ^ 2 with ht
  set q : E := p - t • v with hq
  have hqmem : q ∈ hyperplane v c := by
    have : ⟪q, v⟫ = ⟪p, v⟫ - t * ‖v‖ ^ 2 := by
      rw [hq, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    change ⟪q, v⟫ = c
    rw [this, ht, div_mul_cancel₀ _ (ne_of_gt hv2)]
    ring
  have hdist : dist p q = |⟪p, v⟫ - c| / ‖v‖ := by
    have : p - q = t • v := by rw [hq]; abel
    rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, ht, abs_div, abs_of_pos hv2]
    field_simp
  refine le_antisymm ?_ ?_
  · exact hdist ▸ Metric.infDist_le_dist_of_mem hqmem
  · rw [Metric.le_infDist ⟨q, hqmem⟩]
    intro y hy
    have hyv : ⟪y, v⟫ = c := hy
    have hcs : |⟪p - y, v⟫| ≤ ‖p - y‖ * ‖v‖ := by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (p - y) v
    have hpy : ⟪p - y, v⟫ = ⟪p, v⟫ - c := by rw [inner_sub_left, hyv]
    rw [div_le_iff₀ hvn, dist_eq_norm]
    rw [hpy] at hcs
    exact hcs

/-- Inner products against members of a subspace see only the subspace component of the
other vector: `⟪m, P_M v⟫ = ⟪m, v⟫` for `m ∈ M`. -/
theorem inner_starProjection_of_mem {M : Submodule ℝ E} [M.HasOrthogonalProjection]
    {m : E} (hm : m ∈ M) (v : E) :
    ⟪m, M.starProjection v⟫ = ⟪m, v⟫ := by
  have h0 : ⟪v - M.starProjection v, m⟫ = 0 :=
    Submodule.starProjection_inner_eq_zero (K := M) v m hm
  have h0' : ⟪m, v - M.starProjection v⟫ = 0 := by
    rw [real_inner_comm]; exact h0
  rw [inner_sub_right] at h0'
  linarith

/-- **The separating normal can be chosen in the span of the data**: projecting `v` onto
any closed subspace containing the data preserves all constraint values, hence preserves
separation. -/
theorem SeparatesData.starProjection {ι : Type*} {v : E} {c : ℝ} {x : ι → E}
    {lab : ι → ℝ} {M : Submodule ℝ E} [M.HasOrthogonalProjection]
    -- LEAN-ONLY: the subspace contains the data; instantiated with the closed span
    (hxM : ∀ i, x i ∈ M)
    (h : SeparatesData v c x lab) :
    SeparatesData (M.starProjection v) c x lab := by
  intro i
  rw [inner_starProjection_of_mem (hxM i) v]
  exact h i

end StatLean.NonparametricStatistics
