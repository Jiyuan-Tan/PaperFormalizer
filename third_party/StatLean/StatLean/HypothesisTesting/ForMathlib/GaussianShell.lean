module
/-
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Topology.MetricSpace.Thickening

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-!
# The Gaussian boundary-shell bound for convex sets

For the standard Gaussian `γ = N(0, I_k)` on `EuclideanSpace ℝ (Fin k)` and a convex set `B`,
the mass of the `ε`-boundary shell of `B` is `O_k(ε)`:

`γ(Bᵋ) ≤ γ(B) + C_k ε`  and  `γ(B) ≤ γ(B_{-ε}) + C_k ε`,

where `Bᵋ` is the `ε`-thickening and `B_{-ε}` the `ε`-erosion. This is the missing ingredient of
the elementary convex Berry–Esseen bound
`StatLean.HypothesisTesting.berryEsseen_convex_elementary`, where the *sharp* form of the constant
(K. Ball's `4 k^{1/4}` bound on the Gaussian surface area of a convex body) is what produces the
dimension factor `k^{1/4}` of Bentkus (2003). The elementary assembly only needs *finiteness* of
`C_k` at fixed `k`; what is proved here is the explicit constant

`C_k = 4 e² √k` (`gaussianShellConst`),

i.e. the dimension factor `√k`. Ball's `k^{1/4}` is not reached, but the crude `k^{3/2}` of the
coordinate-slice cover is improved by a full factor `k` (wave 22).

## The argument

Everything rests on one elementary observation about convex sets and *lines*.

* (Support) If `V` is convex and `x ∉ interior V` then some `u ≠ 0` supports `V` at `x`:
  `⟪u, w - x⟫ ≤ 0` for all `w ∈ V` (`exists_inner_le_zero_of_notMem_interior`). For
  `interior V ≠ ∅` this is `geometric_hahn_banach_open_point` applied to `interior V`, extended to
  `closure (interior V) = closure V ⊇ V`; for `interior V = ∅` the affine span of `V` is a proper
  affine subspace and `u` is taken orthogonal to its direction.
* (Escape) Some coordinate of a unit vector is at least `1/√k` in absolute value, so moving from
  `x` by `± c` along that coordinate axis moves *away* from the supporting hyperplane by at least
  `c/√k`; hence `infDist (x ± c • eᵢ) V ≥ c/√k` (`infDist_add_smul_single_ge`).
* (Slice) For a convex `V` and a coordinate `i`, the set `{x ∈ V : x + c • eᵢ ∉ V}` meets every
  line parallel to `eᵢ` in a set of diameter `≤ |c|` — because the trace of `V` on such a line is
  an interval. Its Gaussian mass is therefore at most `2|c|/√(2π)`, by Fubini for
  `γ = ⨂ N(0,1)` (`map_pi_eq_stdGaussian`) and the `1/√(2π)` bound on the one-dimensional
  Gaussian density (`gaussian_mem_notMem_shift_le`). This step is where the Gaussian enters, and
  the bound is *dimension-free*. Rotation invariance of `γ` (`stdGaussian_map` along the isometry
  produced by `exists_isometry_apply_single`) upgrades it to an **arbitrary** shift direction:
  `gaussian_mem_notMem_vadd_le`.

The wave-3 covering combined these by unioning the `2k` sets `{x ∈ Bᵋ : x ± c • eᵢ ∉ Bᵋ}` with
`c = 2ε√k`, giving `γ(shell) ≤ 2k · 2c/√(2π) ∼ k^{3/2} ε`: a factor `k` from the union and a
factor `√k` from the escape step. The `k` is an artefact of the coordinate cover, and wave 22
removes it (`gaussian_le_of_gaussian_shift_cover`): take a **single** random shift `w = 2ε Z`
with `Z ∼ N(0, I_k)` and integrate the two sides of

`1_{S}(x) · 1{x + w ∉ V}`

against `γ ⊗ γ` in the two orders.

* Integrating in `w` first (at fixed `x`, so **no measurable selection of the supporting normal
  is needed**) the escape event contains `{z : ⟪u, z⟫ ≥ 1}`, whose probability is the standard
  normal tail `P(Z ≥ 1) ≥ e^{-2}/√(2π)`, a dimension-free constant.
* Integrating in `x` first gives the directional slice bound `2‖w‖/√(2π)`, whose `w`-average is
  `2 · 2ε · E‖Z‖/√(2π) ≤ 4ε√k/√(2π)`.

Dividing, `γ(shell) ≤ 4 e² √k ε = C_k ε`. Only `E‖Z‖ ≤ √k` carries a dimension factor.

The old coordinate covering with `c → 0` still shows `γ(V \ interior V) = 0` for every convex `V`
(`gaussian_diff_interior_eq_zero`), which is the degenerate case (`interior B = ∅`, i.e. `B` inside
a hyperplane) of the erosion bound.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped InnerProductSpace ENNReal NNReal Real

namespace StatLean.HypothesisTesting

section GaussianShell

variable {k : ℕ}

/-! ### One-dimensional density bounds -/

/-- The standard normal law is dominated by `(2π)^{-1/2}` times Lebesgue measure: its density is
bounded by the peak value `(2π)^{-1/2}`. -/
lemma gaussianReal_le_smul_volume (A : Set ℝ) :
    gaussianReal 0 1 A ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := by
  have hbound : ∀ x : ℝ, gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * π))⁻¹ := by
    intro x
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (x - 0)]
    have hpos : (0 : ℝ) ≤ (Real.sqrt (2 * π * 1))⁻¹ := by positivity
    calc gaussianPDFReal 0 1 x
        = (Real.sqrt (2 * π * 1))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * 1)) := rfl
      _ ≤ (Real.sqrt (2 * π * 1))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hpos
      _ = (Real.sqrt (2 * π))⁻¹ := by norm_num
  rw [gaussianReal_apply 0 one_ne_zero A]
  calc ∫⁻ x in A, gaussianPDF 0 1 x
      ≤ ∫⁻ _ in A, ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ := by
        refine lintegral_mono fun x => ?_
        exact ENNReal.ofReal_le_ofReal (hbound x)
    _ = ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := by
        rw [setLIntegral_const]

/-- A set of diameter at most `c` has standard normal mass at most `2c/√(2π)`. -/
lemma gaussianReal_le_of_diam_le {A : Set ℝ} {c : ℝ}
    (h : ∀ s ∈ A, ∀ t ∈ A, |s - t| ≤ c) :
    gaussianReal 0 1 A ≤ ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  · have hsub : A ⊆ Set.Icc (t₀ - c) (t₀ + c) := by
      intro s hs
      have := h s hs t₀ ht₀
      rw [abs_le] at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    calc gaussianReal 0 1 A
        ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := gaussianReal_le_smul_volume A
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume (Set.Icc (t₀ - c) (t₀ + c)) := by
          gcongr
      _ = ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : t₀ + c - (t₀ - c) = 2 * c := by ring
          rw [this]
          field_simp

/-! ### The Gaussian as a product measure -/

/-- `N(0, I_k)` is the pushforward of the `k`-fold product of `N(0,1)` under the (identity)
`toLp` map. This is `map_pi_eq_stdGaussian` combined with `multivariateGaussian_zero_one`. -/
lemma multivariateGaussian_eq_map_pi (k : ℕ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (WithLp.toLp 2) := by
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]

/-! ### The coordinate-slice bound

The Gaussian input of the whole file: for convex `V` and a coordinate direction `eᵢ`, the set of
points of `V` that leave `V` after a shift by `c • eᵢ` has Gaussian mass at most `2|c|/√(2π)`,
with **no dimension factor**. Its trace on each line parallel to `eᵢ` has diameter `≤ |c|`
because the trace of `V` on that line is an interval; Fubini for the product form of `N(0, I_k)`
then costs nothing. -/

/-- If `J ⊆ ℝ` is convex then the set of points of `J` whose `c`-shift leaves `J` has diameter at
most `|c|`: two such points further apart would have the shift of one of them strictly between
them, hence inside `J`. -/
private lemma diam_shift_le_of_convex {J : Set ℝ} (hJ : Convex ℝ J) (c : ℝ) :
    ∀ s ∈ {t | t ∈ J ∧ t + c ∉ J}, ∀ t ∈ {t | t ∈ J ∧ t + c ∉ J}, |s - t| ≤ |c| := by
  have hoc : J.OrdConnected := convex_iff_ordConnected.mp hJ
  have key : ∀ s ∈ {t | t ∈ J ∧ t + c ∉ J}, ∀ t ∈ {t | t ∈ J ∧ t + c ∉ J},
      s ≤ t → t - s ≤ |c| := by
    intro s hs t ht hst
    by_contra hcon
    rw [not_le] at hcon
    rcases le_or_gt 0 c with hc | hc
    · rw [abs_of_nonneg hc] at hcon
      exact hs.2 (hoc.out hs.1 ht.1 ⟨by linarith, by linarith⟩)
    · rw [abs_of_neg hc] at hcon
      exact ht.2 (hoc.out hs.1 ht.1 ⟨by linarith, by linarith⟩)
  intro s hs t ht
  rcases le_total s t with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s)]
    exact key s hs t ht h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]
    exact key t ht s hs h

/-- Inserting an affine combination in the `i`-th slot is the affine combination of the
insertions: `t ↦ i.insertNth t y` is an affine map `ℝ → (Fin (m+1) → ℝ)`. -/
private lemma insertNth_affine {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) {a b s r : ℝ}
    (hsr : s + r = 1) :
    Fin.insertNth (α := fun _ => ℝ) i (s * a + r * b) y
      = s • Fin.insertNth (α := fun _ => ℝ) i a y
        + r • Fin.insertNth (α := fun _ => ℝ) i b y := by
  refine funext ((Fin.forall_iff_succAbove i).2 ⟨by simp, fun j => ?_⟩)
  simp only [Fin.insertNth_apply_succAbove, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(y j)) * hsr

/-- Shifting the inserted coordinate by `c` is adding `c • Pi.single i 1`. -/
private lemma insertNth_add_single {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) (t c : ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i (t + c) y
      = Fin.insertNth (α := fun _ => ℝ) i t y
        + c • (Pi.single i (1 : ℝ) : Fin (m + 1) → ℝ) := by
  refine funext ((Fin.forall_iff_succAbove i).2 ⟨by simp, fun j => ?_⟩)
  simp [Fin.insertNth_apply_succAbove]

/-- **Coordinate-slice anti-concentration.** For a convex measurable `V` and a coordinate `i`,
the standard Gaussian mass of `{x ∈ V : x + c • eᵢ ∉ V}` is at most `2|c|/√(2π)`. The constant is
dimension-free. -/
lemma gaussian_mem_notMem_shift_le (hk : 0 < k) (i : Fin k) (c : ℝ)
    {V : Set (EuclideanSpace ℝ (Fin k))} (hVm : MeasurableSet V) (hVc : Convex ℝ V) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
        {x | x ∈ V ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ V}
      ≤ ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  set L : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 with hLdef
  have hLmeas : Measurable L := by rw [hLdef]; fun_prop
  set T : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    {x | x ∈ V ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ V} with hTdef
  have hTm : MeasurableSet T := by
    have hmap : Measurable (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        x + c • EuclideanSpace.single i (1 : ℝ)) := by fun_prop
    exact hVm.inter (hmap hVm.compl)
  rw [multivariateGaussian_eq_map_pi, Measure.map_apply hLmeas hTm]
  -- the peeled product form
  set μ : Fin (m + 1) → Measure ℝ := fun _ => gaussianReal 0 1 with hμdef
  set e : ((_ : Fin (m + 1)) → ℝ) ≃ᵐ ℝ × ((_ : Fin m) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i with hedef
  have hmp : MeasurePreserving e (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : Fin m => μ (i.succAbove j))) :=
    measurePreserving_piFinSuccAbove μ i
  set S : Set (ℝ × ((_ : Fin m) → ℝ)) := e.symm ⁻¹' (L ⁻¹' T) with hSdef
  have hSm : MeasurableSet S := e.symm.measurable (hLmeas hTm)
  have hpre : e ⁻¹' S = L ⁻¹' T := by
    ext x; simp [hSdef]
  have hkey : Measure.pi μ (L ⁻¹' T)
      = ((μ i).prod (Measure.pi fun j : Fin m => μ (i.succAbove j))) S := by
    rw [← hpre]; exact hmp.measure_preimage hSm.nullMeasurableSet
  rw [hkey, Measure.prod_apply_symm hSm]
  -- each line slice has diameter `≤ |c|`
  have hslice : ∀ y : Fin m → ℝ, (μ i) ((fun t => (t, y)) ⁻¹' S)
      ≤ ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π)) := by
    intro y
    set J : Set ℝ := {t : ℝ | L (Fin.insertNth (α := fun _ => ℝ) i t y) ∈ V} with hJdef
    have hJconv : Convex ℝ J := by
      intro a ha b hb s r hs hr hsr
      have hins := insertNth_affine i y (a := a) (b := b) hsr
      have : L (Fin.insertNth (α := fun _ => ℝ) i (s * a + r * b) y)
          = s • L (Fin.insertNth (α := fun _ => ℝ) i a y)
            + r • L (Fin.insertNth (α := fun _ => ℝ) i b y) := by rw [hins]; rfl
      simpa [hJdef, this] using hVc ha hb hs hr hsr
    have hsym : ∀ t : ℝ, e.symm (t, y) = Fin.insertNth (α := fun _ => ℝ) i t y := fun _ => rfl
    have hset : (fun t => (t, y)) ⁻¹' S = {t | t ∈ J ∧ t + c ∉ J} := by
      ext t
      have hshift : L (Fin.insertNth (α := fun _ => ℝ) i (t + c) y)
          = L (Fin.insertNth (α := fun _ => ℝ) i t y)
            + c • EuclideanSpace.single i (1 : ℝ) := by
        rw [insertNth_add_single]; rfl
      simp only [Set.mem_preimage, hSdef, hsym, hTdef, Set.mem_setOf_eq, hJdef, hshift]
    rw [hset, hμdef]
    exact gaussianReal_le_of_diam_le (diam_shift_le_of_convex hJconv c)
  calc ∫⁻ y, (μ i) ((fun t => (t, y)) ⁻¹' S)
          ∂(Measure.pi fun j : Fin m => μ (i.succAbove j))
      ≤ ∫⁻ _, ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π))
          ∂(Measure.pi fun j : Fin m => μ (i.succAbove j)) := lintegral_mono hslice
    _ = ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π)) := by
        rw [lintegral_const, hμdef]
        simp

/-! ### Supporting functionals and the escape direction -/

/-- **Supporting hyperplane at a non-interior point.** If `V` is convex and `x ∉ interior V`,
some `u ≠ 0` supports `V` at `x`, i.e. `⟪u, w - x⟫ ≤ 0` for all `w` in the *closure* of `V`.

If `interior V ≠ ∅` this is `geometric_hahn_banach_open_point` applied to the open convex set
`interior V`, whose closure is `closure V`. If `interior V = ∅` then `V` spans a proper affine
subspace (`Convex.interior_nonempty_iff_affineSpan_eq_top`) and any `u ≠ 0` orthogonal to its
direction makes `⟪u, · - x⟫` constant on `V`; one of `±u` then works. -/
lemma exists_inner_le_zero_of_notMem_interior (hk : 0 < k)
    {V : Set (EuclideanSpace ℝ (Fin k))} (hV : Convex ℝ V)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∉ interior V) :
    ∃ u : EuclideanSpace ℝ (Fin k), u ≠ 0 ∧ ∀ w ∈ closure V, ⟪u, w - x⟫_ℝ ≤ 0 := by
  suffices h : ∃ u : EuclideanSpace ℝ (Fin k), u ≠ 0 ∧ ∀ w ∈ V, ⟪u, w - x⟫_ℝ ≤ 0 by
    obtain ⟨u, hu0, hu⟩ := h
    refine ⟨u, hu0, ?_⟩
    have hclosed : IsClosed {w : EuclideanSpace ℝ (Fin k) | ⟪u, w - x⟫_ℝ ≤ 0} :=
      isClosed_le (Continuous.inner continuous_const (continuous_id.sub continuous_const))
        continuous_const
    exact fun w hw => hclosed.closure_subset_iff.mpr hu hw
  rcases (interior V).eq_empty_or_nonempty with hint | hint
  · -- degenerate case: `V` lies in a proper affine subspace
    rcases V.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
    · obtain ⟨i⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
      exact ⟨EuclideanSpace.single i 1, by simp, by simp⟩
    · have hspan : affineSpan ℝ V ≠ ⊤ := by
        intro h
        have hne : (interior V).Nonempty := hV.interior_nonempty_iff_affineSpan_eq_top.2 h
        rw [hint] at hne
        exact Set.not_nonempty_empty hne
      have hvs : vectorSpan ℝ V ≠ ⊤ := fun h =>
        hspan ((AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ
          (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) ⟨w₀, hw₀⟩).mpr h)
      have hbot : (vectorSpan ℝ V)ᗮ ≠ ⊥ := fun h => hvs (Submodule.orthogonal_eq_bot_iff.mp h)
      obtain ⟨u, hu, hune⟩ := Submodule.ne_bot_iff _ |>.mp hbot
      have hconst : ∀ w ∈ V, ⟪u, w - x⟫_ℝ = ⟪u, w₀ - x⟫_ℝ := by
        intro w hw
        have hmem : w - w₀ ∈ vectorSpan ℝ V := by
          simpa using vsub_mem_vectorSpan ℝ hw hw₀
        have hzero : ⟪u, w - w₀⟫_ℝ = 0 := by
          rw [real_inner_comm]
          exact (Submodule.mem_orthogonal _ u).1 hu _ hmem
        have hsplit : w - x = (w - w₀) + (w₀ - x) := by abel
        rw [hsplit, inner_add_right, hzero, zero_add]
      rcases le_or_gt (⟪u, w₀ - x⟫_ℝ) 0 with h0 | h0
      · exact ⟨u, hune, fun w hw => (hconst w hw).le.trans h0⟩
      · refine ⟨-u, neg_ne_zero.mpr hune, fun w hw => ?_⟩
        rw [inner_neg_left, hconst w hw]
        linarith
  · -- main case: separate the open convex set `interior V` from the point `x`
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hV.interior isOpen_interior hx
    obtain ⟨a, ha⟩ := hint
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm f, ?_, ?_⟩
    · intro h0
      have hlt : f a < f x := hf a ha
      have hfa : f a = 0 := by
        rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := f) (x := a), h0, inner_zero_left]
      have hfx : f x = 0 := by
        rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := f) (x := x), h0, inner_zero_left]
      rw [hfa, hfx] at hlt
      exact lt_irrefl _ hlt
    · intro w hw
      have hVsub : V ⊆ closure (interior V) := by
        rw [hV.closure_interior_eq_closure_of_nonempty_interior ⟨a, ha⟩]
        exact subset_closure
      have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin k) | f y ≤ f x} :=
        isClosed_le f.continuous continuous_const
      have hle : f w ≤ f x :=
        hclosed.closure_subset_iff.mpr (fun y hy => (hf y hy).le) (hVsub hw)
      rw [InnerProductSpace.toDual_symm_apply, map_sub]
      linarith

/-- **Escape direction.** If `u ≠ 0` supports `V` at `x`, then some coordinate satisfies
`|uᵢ| ≥ ‖u‖/√k`, and moving from `x` by `±c` along that axis (sign chosen to increase `⟪u, ·⟫`)
lands at distance at least `c/√k` from every point of `V`. -/
lemma exists_dist_ge_of_inner_le_zero (hk : 0 < k)
    {V : Set (EuclideanSpace ℝ (Fin k))} {x u : EuclideanSpace ℝ (Fin k)} (hu : u ≠ 0)
    (hsupp : ∀ w ∈ V, ⟪u, w - x⟫_ℝ ≤ 0) {c : ℝ} (hc : 0 ≤ c) :
    ∃ (i : Fin k) (d : ℝ), |d| = c ∧
      ∀ w ∈ V, c / Real.sqrt k ≤ dist (x + d • EuclideanSpace.single i (1 : ℝ)) w := by
  classical
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.mp hk)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |u j|) hne
  have hkr : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hk)
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu
  -- the largest coordinate carries at least `‖u‖/√k`
  have hcoord : ‖u‖ ≤ Real.sqrt k * |u i| := by
    have hsum : ∑ j, ‖u j‖ ^ 2 ≤ (k : ℝ) * |u i| ^ 2 := by
      calc ∑ j : Fin k, ‖u j‖ ^ 2 ≤ ∑ _j : Fin k, |u i| ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have := hi j (Finset.mem_univ j)
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = (k : ℝ) * |u i| ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ j, ‖u j‖ ^ 2) ≤ Real.sqrt ((k : ℝ) * |u i| ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt k * |u i| := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (abs_nonneg _)]
  refine ⟨i, if 0 ≤ u i then c else -c, by split_ifs <;> simp [abs_of_nonneg hc], ?_⟩
  intro w hw
  set d : ℝ := if 0 ≤ u i then c else -c with hd
  have hdu : d * u i = c * |u i| := by
    rw [hd]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set y : EuclideanSpace ℝ (Fin k) := x + d • EuclideanSpace.single i (1 : ℝ) with hy
  have hinner : ⟪u, y - w⟫_ℝ = d * u i - ⟪u, w - x⟫_ℝ := by
    have hsplit : y - w = d • EuclideanSpace.single i (1 : ℝ) - (w - x) := by rw [hy]; abel
    have hsingle : ⟪u, EuclideanSpace.single i (1 : ℝ)⟫_ℝ = u i := by
      simpa using EuclideanSpace.inner_single_right i (1 : ℝ) u
    rw [hsplit, inner_sub_right, real_inner_smul_right, hsingle]
  have hlow : c * |u i| ≤ ⟪u, y - w⟫_ℝ := by
    rw [hinner, hdu]
    linarith [hsupp w hw]
  have hcs : ⟪u, y - w⟫_ℝ ≤ ‖u‖ * ‖y - w‖ := real_inner_le_norm u (y - w)
  have hstep : c * ‖u‖ / Real.sqrt k ≤ ‖u‖ * ‖y - w‖ := by
    have : c * ‖u‖ / Real.sqrt k ≤ c * |u i| := by
      rw [div_le_iff₀ hkr]
      calc c * ‖u‖ ≤ c * (Real.sqrt k * |u i|) := by
            exact mul_le_mul_of_nonneg_left hcoord hc
        _ = c * |u i| * Real.sqrt k := by ring
    linarith
  rw [dist_eq_norm, div_le_iff₀ hkr]
  rw [div_le_iff₀ hkr] at hstep
  have hmul : ‖u‖ * c ≤ ‖u‖ * (‖y - w‖ * Real.sqrt k) := by
    calc ‖u‖ * c = c * ‖u‖ := mul_comm _ _
      _ ≤ ‖u‖ * ‖y - w‖ * Real.sqrt k := hstep
      _ = ‖u‖ * (‖y - w‖ * Real.sqrt k) := by ring
  exact le_of_mul_le_mul_left hmul hunorm

/-! ### The covering bookkeeping -/

/-- The `2k` coordinate shifts cover: if every point of `S` sits in the convex measurable set `W`
and leaves `W` after a shift by `±c` along some coordinate axis, then `γ S ≤ 4kc/√(2π)`. -/
private lemma gaussian_le_of_shift_cover (hk : 0 < k)
    {W S : Set (EuclideanSpace ℝ (Fin k))} (hWm : MeasurableSet W) (hWc : Convex ℝ W)
    {c : ℝ} (hc : 0 ≤ c)
    (hcover : ∀ x ∈ S, ∃ (i : Fin k) (d : ℝ), |d| = c ∧ x ∈ W ∧
      x + d • EuclideanSpace.single i (1 : ℝ) ∉ W) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 S
      ≤ ENNReal.ofReal (4 * k * c / Real.sqrt (2 * π)) := by
  classical
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 with hγ
  set A : Fin k → Set (EuclideanSpace ℝ (Fin k)) := fun i =>
    {x | x ∈ W ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ W} ∪
      {x | x ∈ W ∧ x + (-c) • EuclideanSpace.single i (1 : ℝ) ∉ W} with hA
  have hsub : S ⊆ ⋃ i, A i := by
    intro x hx
    obtain ⟨i, d, hd, hxW, hout⟩ := hcover x hx
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rcases (abs_eq hc).mp hd with rfl | rfl
    · exact Or.inl ⟨hxW, hout⟩
    · exact Or.inr ⟨hxW, hout⟩
  have hpiece : ∀ i : Fin k, γ (A i) ≤ ENNReal.ofReal (4 * c / Real.sqrt (2 * π)) := by
    intro i
    have h1 := gaussian_mem_notMem_shift_le hk i c hWm hWc
    have h2 := gaussian_mem_notMem_shift_le hk i (-c) hWm hWc
    rw [abs_of_nonneg hc, ← hγ] at h1
    rw [abs_neg, abs_of_nonneg hc, ← hγ] at h2
    calc γ (A i) ≤ γ {x | x ∈ W ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ W}
          + γ {x | x ∈ W ∧ x + (-c) • EuclideanSpace.single i (1 : ℝ) ∉ W} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * c / Real.sqrt (2 * π))
          + ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := add_le_add h1 h2
      _ = ENNReal.ofReal (4 * c / Real.sqrt (2 * π)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  calc γ S ≤ γ (⋃ i, A i) := measure_mono hsub
    _ ≤ ∑ i, γ (A i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin k, ENNReal.ofReal (4 * c / Real.sqrt (2 * π)) :=
        Finset.sum_le_sum fun i _ => hpiece i
    _ = ENNReal.ofReal (4 * k * c / Real.sqrt (2 * π)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### The sharp cover: a single Gaussian shift

The `2k` coordinate shifts above cost a factor `k` on top of the `√k` lost in the escape step,
giving `C_k ∼ k^{3/2}`. Replacing the coordinate cover by **one** random shift `w = 2ε Z`,
`Z ∼ N(0, I_k)`, removes the `k` entirely and leaves only `E‖Z‖ ≤ √k`, so `C_k ∼ √k`. Three
ingredients: rotation invariance of `γ` (to run the slice bound along `w` rather than along a
coordinate axis), the first absolute moment of `γ`, and a lower bound on the standard normal
tail. -/

/-- Every unit vector is the image of a coordinate vector under a linear isometry of
`EuclideanSpace ℝ (Fin k)`: complete `u` to an orthonormal basis and transport the standard
basis onto it. -/
private lemma exists_isometry_apply_single (hk : 0 < k) {u : EuclideanSpace ℝ (Fin k)}
    (hu : ‖u‖ = 1) :
    ∃ (i : Fin k) (R : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)),
      R (EuclideanSpace.single i (1 : ℝ)) = u := by
  classical
  obtain ⟨i⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = Fintype.card (Fin k) := by simp
  have horth : Orthonormal ℝ (({i} : Set (Fin k)).restrict (fun _ : Fin k => u)) := by
    constructor
    · intro x; simpa using! hu
    · intro x y hxy
      exact absurd (Subtype.ext (x.2.trans y.2.symm)) hxy
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  refine ⟨i, (EuclideanSpace.basisFun (Fin k) ℝ).equiv b (Equiv.refl _), ?_⟩
  rw [← EuclideanSpace.basisFun_apply, OrthonormalBasis.equiv_apply_basis]
  simpa using hb i rfl

/-- **Directional slice anti-concentration.** The coordinate-slice bound
`gaussian_mem_notMem_shift_le` holds for a shift along an *arbitrary* vector `w`, with the same
dimension-free constant: the standard Gaussian is invariant under the linear isometry carrying a
coordinate axis onto `w`, and that isometry carries a convex set to a convex set. -/
lemma gaussian_mem_notMem_vadd_le (hk : 0 < k) (w : EuclideanSpace ℝ (Fin k))
    {V : Set (EuclideanSpace ℝ (Fin k))} (hVm : MeasurableSet V) (hVc : Convex ℝ V) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 {x | x ∈ V ∧ x + w ∉ V}
      ≤ ENNReal.ofReal (2 * ‖w‖ / Real.sqrt (2 * π)) := by
  rcases eq_or_ne w 0 with rfl | hw
  · have hempty : {x : EuclideanSpace ℝ (Fin k) | x ∈ V ∧ x + 0 ∉ V} = ∅ := by
      ext x
      simp only [add_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun h => h
    rw [hempty]
    simp
  · have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hunit : ‖(‖w‖⁻¹ • w : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnw)]
      field_simp
    obtain ⟨i, R, hR⟩ := exists_isometry_apply_single hk hunit
    have hRw : R (‖w‖ • EuclideanSpace.single i (1 : ℝ)) = w := by
      rw [map_smul, hR, smul_smul, mul_inv_cancel₀ hnw.ne', one_smul]
    have hRmeas : Measurable (R : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) :=
      R.continuous.measurable
    set V' : Set (EuclideanSpace ℝ (Fin k)) := R ⁻¹' V with hV'def
    have hV'm : MeasurableSet V' := hRmeas hVm
    have hV'c : Convex ℝ V' := by
      intro x hx y hy s r hs hr hsr
      simp only [hV'def, Set.mem_preimage] at hx hy ⊢
      have hlin : R (s • x + r • y) = s • R x + r • R y := by
        rw [map_add, map_smul, map_smul]
      rw [hlin]
      exact hVc hx hy hs hr hsr
    have hpre : (R : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) ⁻¹'
        {x | x ∈ V ∧ x + w ∉ V}
        = {y | y ∈ V' ∧ y + ‖w‖ • EuclideanSpace.single i (1 : ℝ) ∉ V'} := by
      ext y
      have hadd : R (y + ‖w‖ • EuclideanSpace.single i (1 : ℝ)) = R y + w := by
        rw [map_add, hRw]
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hV'def, hadd]
    have hinvar : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
        {x | x ∈ V ∧ x + w ∉ V}
        = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
            {y | y ∈ V' ∧ y + ‖w‖ • EuclideanSpace.single i (1 : ℝ) ∉ V'} := by
      have hTm : MeasurableSet {x : EuclideanSpace ℝ (Fin k) | x ∈ V ∧ x + w ∉ V} :=
        hVm.inter ((measurable_id.add_const w) hVm.compl)
      have hmap : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1).map R
          = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 := by
        rw [multivariateGaussian_zero_one]
        exact stdGaussian_map R
      conv_lhs => rw [← hmap]
      rw [Measure.map_apply hRmeas hTm, hpre]
    rw [hinvar]
    have h := gaussian_mem_notMem_shift_le hk i ‖w‖ hV'm hV'c
    rwa [abs_of_pos hnw] at h

/-- The one-dimensional marginal of `N(0, I_k)` along a unit vector. -/
lemma gaussian_map_inner_unit (hk : 0 < k) {u : EuclideanSpace ℝ (Fin k)} (hu : ‖u‖ = 1) :
    Measure.map (fun z => ⟪u, z⟫_ℝ) (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)
      = gaussianReal 0 1 := by
  obtain ⟨i, R, hR⟩ := exists_isometry_apply_single hk hu
  have hfun : (fun z : EuclideanSpace ℝ (Fin k) => ⟪u, z⟫_ℝ)
      = (fun y : EuclideanSpace ℝ (Fin k) => y i) ∘ (R.symm : _ → _) := by
    funext z
    have h : ⟪u, z⟫_ℝ = ⟪R (EuclideanSpace.single i (1 : ℝ)), R (R.symm z)⟫_ℝ := by
      rw [hR, R.apply_symm_apply]
    rw [h, R.inner_map_map]
    simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) (R.symm z)
  have hinv : (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1).map
      (R.symm : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      = multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    rw [multivariateGaussian_zero_one]
    exact stdGaussian_map R.symm
  have heval := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin k))) (S := (1 : Matrix (Fin k) (Fin k) ℝ))
    Matrix.PosSemidef.one (i := i)
  rw [hfun, ← Measure.map_map (by fun_prop) R.symm.continuous.measurable, hinv]
  simpa using heval.map_eq

/-- The second moment of the standard one-dimensional Gaussian. -/
private lemma integral_sq_gaussianReal_std : (∫ t : ℝ, t ^ 2 ∂(gaussianReal 0 1)) = 1 := by
  have hmem : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have h := variance_eq_sub (μ := gaussianReal 0 1) hmem
  rw [variance_id_gaussianReal] at h
  simp only [id_eq, Pi.pow_apply] at h
  rw [integral_id_gaussianReal] at h
  push_cast at h
  nlinarith [h]

/-- `∫ ‖z‖² dγ = k`. -/
private lemma integral_normSq_gaussian (k : ℕ) :
    (∫ z, ‖z‖ ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)) = (k : ℝ) := by
  have hmp : ∀ i : Fin k, MeasurePreserving (fun z : EuclideanSpace ℝ (Fin k) => z i)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) (gaussianReal 0 1) := by
    intro i
    have h := measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ (Fin k))) (S := (1 : Matrix (Fin k) (Fin k) ℝ))
      Matrix.PosSemidef.one (i := i)
    simpa using h
  have hint : ∀ i : Fin k, Integrable
      (fun z : EuclideanSpace ℝ (Fin k) => z i ^ 2)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) := by
    intro i
    have hsq : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
    rw [← (hmp i).map_eq] at hsq
    exact (integrable_map_measure (by fun_prop) (by fun_prop)).1 hsq
  have hcoord : ∀ i : Fin k,
      (∫ z : EuclideanSpace ℝ (Fin k), z i ^ 2
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)) = 1 := by
    intro i
    rw [← integral_sq_gaussianReal_std, ← (hmp i).map_eq,
      integral_map (by fun_prop) (by fun_prop)]
  have hnormsq : ∀ z : EuclideanSpace ℝ (Fin k), ‖z‖ ^ 2 = ∑ i, z i ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
  calc (∫ z, ‖z‖ ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1))
      = ∫ z, ∑ i, z i ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
        integral_congr_ae (ae_of_all _ fun z => hnormsq z)
    _ = ∑ i, ∫ z, z i ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
        integral_finset_sum _ fun i _ => hint i
    _ = (k : ℝ) := by rw [Finset.sum_congr rfl fun i _ => hcoord i]; simp

private lemma integrable_norm_gaussian (k : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
  (IsGaussian.integrable_id (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)).norm

/-- `E‖Z‖ ≤ √k`: Cauchy–Schwarz against `E‖Z‖² = k`. -/
private lemma integral_norm_gaussian_le (k : ℕ) :
    (∫ z, ‖z‖ ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)) ≤ Real.sqrt (k : ℝ) := by
  have hmem : MemLp (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    (IsGaussian.memLp_two_id
      (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)).norm
  have hvar := variance_eq_sub (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) hmem
  have hnn : 0 ≤ variance (fun z : EuclideanSpace ℝ (Fin k) => ‖z‖)
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) := variance_nonneg _ _
  have hsq : (∫ z, ((fun z : EuclideanSpace ℝ (Fin k) => ‖z‖) ^ 2) z
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)) = (k : ℝ) := by
    simp only [Pi.pow_apply]
    exact integral_normSq_gaussian k
  rw [hsq] at hvar
  have hle : (∫ z, ‖z‖ ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1)) ^ 2
      ≤ (k : ℝ) := by linarith
  have h0 : 0 ≤ ∫ z, ‖z‖ ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1) :=
    integral_nonneg fun z => norm_nonneg z
  exact (Real.le_sqrt h0 (by positivity)).2 hle

/-- A crude but explicit lower bound on the standard normal tail `P(Z ≥ 1)`. -/
private lemma gaussianReal_Ici_one_ge :
    ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * π))
      ≤ gaussianReal 0 1 (Set.Ici (1 : ℝ)) := by
  have hsub : Set.Icc (1 : ℝ) 2 ⊆ Set.Ici (1 : ℝ) := fun x hx => hx.1
  refine le_trans ?_ (measure_mono hsub)
  rw [gaussianReal_apply 0 one_ne_zero (Set.Icc (1 : ℝ) 2)]
  have hlow : ∀ x ∈ Set.Icc (1 : ℝ) 2,
      ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * π)) ≤ gaussianPDF 0 1 x := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal ?_
    have hx2 : x ^ 2 ≤ 4 := by nlinarith [hx.1, hx.2]
    have hexp : Real.exp (-2) ≤ Real.exp (-(x - 0) ^ 2 / (2 * 1)) := by
      apply Real.exp_le_exp.2
      nlinarith [hx2]
    have hpos : (0 : ℝ) < Real.sqrt (2 * π * 1) := by
      apply Real.sqrt_pos.2; positivity
    have hval : gaussianPDFReal 0 1 x
        = (Real.sqrt (2 * π * 1))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * 1)) := rfl
    rw [hval]
    have hs : Real.sqrt (2 * π * 1) = Real.sqrt (2 * π) := by norm_num
    rw [hs, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  calc ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * π))
      = ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * π)) * volume (Set.Icc (1 : ℝ) 2) := by
        rw [Real.volume_Icc]
        norm_num
    _ = ∫⁻ _ in Set.Icc (1 : ℝ) 2, ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * π)) :=
        (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in Set.Icc (1 : ℝ) 2, gaussianPDF 0 1 x :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hlow))

/-- **The Gaussian-shift cover.** If every point of the measurable set `S ⊆ V` (`V` measurable
convex) escapes `V` under every shift `w` with `⟪u, w⟫ ≥ 2ε` for some *unit* `u` depending on the
point, then `γ S ≤ 4 e² √k ε`.

This replaces the `2k`-fold coordinate cover of `gaussian_le_of_shift_cover` by a **single random
shift** `w = 2ε Z`, `Z ∼ N(0, I_k)`, and costs only `√k` instead of `k^{3/2}`:

* the *upper* estimate integrates the directional slice bound `2‖w‖/√(2π)` against the law of
  `w`, which costs `E‖Z‖ ≤ √k` (`integral_norm_gaussian_le`);
* the *lower* estimate is dimension-free: for each fixed `x` the escape event contains
  `{z : ⟪u, z⟫ ≥ 1}`, whose probability is the standard normal tail `P(Z ≥ 1) ≥ e^{-2}/√(2π)`,
  independent of `x` — and, crucially, no measurable selection of `u` is needed, because the
  bound is applied inside the inner integral at fixed `x`. -/
private lemma gaussian_le_of_gaussian_shift_cover (hk : 0 < k)
    {V S : Set (EuclideanSpace ℝ (Fin k))} (hVm : MeasurableSet V) (hVc : Convex ℝ V)
    (hSm : MeasurableSet S) (hSV : S ⊆ V) {ε : ℝ} (hε : 0 < ε)
    (hcover : ∀ x ∈ S, ∃ u : EuclideanSpace ℝ (Fin k), ‖u‖ = 1 ∧
      ∀ w : EuclideanSpace ℝ (Fin k), 2 * ε ≤ ⟪u, w⟫_ℝ → x + w ∉ V) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 S
      ≤ ENNReal.ofReal (4 * Real.exp 2 * Real.sqrt (k : ℝ) * ε) := by
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 with hγ
  set A : Set (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) :=
    {p | p.1 ∈ S ∧ p.1 + (2 * ε) • p.2 ∉ V} with hA
  have hAm : MeasurableSet A := by
    have h1 : MeasurableSet
        {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) | p.1 ∈ S} :=
      measurable_fst hSm
    have h2 : MeasurableSet
        {p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) |
          p.1 + (2 * ε) • p.2 ∉ V} :=
      (by fun_prop : Measurable fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) =>
        p.1 + (2 * ε) • p.2) hVm.compl
    exact h1.inter h2
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2) / Real.sqrt (2 * π)) with hc₀
  have hc₀ne : c₀ ≠ 0 := by
    rw [hc₀, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hc₀top : c₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  -- lower estimate, via Fubini in the shift variable
  have hlow : c₀ * γ S ≤ (γ.prod γ) A := by
    rw [Measure.prod_apply hAm]
    have hpt : ∀ x, S.indicator (fun _ => c₀) x ≤ γ (Prod.mk x ⁻¹' A) := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        obtain ⟨u, hu, hesc⟩ := hcover x hx
        have hsub : (fun z => ⟪u, z⟫_ℝ) ⁻¹' (Set.Ici (1 : ℝ)) ⊆ Prod.mk x ⁻¹' A := by
          intro z hz
          have hz1 : (1 : ℝ) ≤ ⟪u, z⟫_ℝ := hz
          refine ⟨hx, hesc _ ?_⟩
          rw [real_inner_smul_right]
          nlinarith
        calc c₀ ≤ gaussianReal 0 1 (Set.Ici (1 : ℝ)) := gaussianReal_Ici_one_ge
          _ = γ ((fun z => ⟪u, z⟫_ℝ) ⁻¹' (Set.Ici (1 : ℝ))) := by
              rw [hγ, ← Measure.map_apply (by fun_prop) measurableSet_Ici,
                gaussian_map_inner_unit hk hu]
          _ ≤ γ (Prod.mk x ⁻¹' A) := measure_mono hsub
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    calc c₀ * γ S = ∫⁻ x, S.indicator (fun _ => c₀) x ∂γ := by
          rw [lintegral_indicator hSm, setLIntegral_const]
      _ ≤ ∫⁻ x, γ (Prod.mk x ⁻¹' A) ∂γ := lintegral_mono hpt
  -- upper estimate, via Fubini in the point variable
  have hupp : (γ.prod γ) A
      ≤ ENNReal.ofReal (2 * (2 * ε) * Real.sqrt (k : ℝ) / Real.sqrt (2 * π)) := by
    rw [Measure.prod_apply_symm hAm]
    have hpt : ∀ z, γ ((fun x => (x, z)) ⁻¹' A)
        ≤ ENNReal.ofReal ((2 * (2 * ε) / Real.sqrt (2 * π)) * ‖z‖) := by
      intro z
      have hsub : (fun x => (x, z)) ⁻¹' A
          ⊆ {x | x ∈ V ∧ x + (2 * ε) • z ∉ V} := fun x hx => ⟨hSV hx.1, hx.2⟩
      calc γ ((fun x => (x, z)) ⁻¹' A)
          ≤ γ {x | x ∈ V ∧ x + (2 * ε) • z ∉ V} := measure_mono hsub
        _ ≤ ENNReal.ofReal (2 * ‖(2 * ε) • z‖ / Real.sqrt (2 * π)) :=
            gaussian_mem_notMem_vadd_le hk _ hVm hVc
        _ = ENNReal.ofReal ((2 * (2 * ε) / Real.sqrt (2 * π)) * ‖z‖) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
            congr 1
            ring
    have hInt : Integrable
        (fun z : EuclideanSpace ℝ (Fin k) => (2 * (2 * ε) / Real.sqrt (2 * π)) * ‖z‖) γ :=
      (integrable_norm_gaussian k).const_mul _
    have hnn : 0 ≤ᵐ[γ]
        fun z : EuclideanSpace ℝ (Fin k) => (2 * (2 * ε) / Real.sqrt (2 * π)) * ‖z‖ := by
      filter_upwards with z
      have : (0 : ℝ) ≤ 2 * (2 * ε) / Real.sqrt (2 * π) := by positivity
      exact mul_nonneg this (norm_nonneg z)
    have hival : (∫ z, (2 * (2 * ε) / Real.sqrt (2 * π)) * ‖z‖ ∂γ)
        = (2 * (2 * ε) / Real.sqrt (2 * π)) * ∫ z, ‖z‖ ∂γ := integral_const_mul _ _
    calc ∫⁻ z, γ ((fun x => (x, z)) ⁻¹' A) ∂γ
        ≤ ∫⁻ z, ENNReal.ofReal ((2 * (2 * ε) / Real.sqrt (2 * π)) * ‖z‖) ∂γ :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (∫ z, (2 * (2 * ε) / Real.sqrt (2 * π)) * ‖z‖ ∂γ) :=
          (ofReal_integral_eq_lintegral_ofReal hInt hnn).symm
      _ ≤ ENNReal.ofReal (2 * (2 * ε) * Real.sqrt (k : ℝ) / Real.sqrt (2 * π)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hival]
          have hb := integral_norm_gaussian_le k
          have hc : (0 : ℝ) ≤ 2 * (2 * ε) / Real.sqrt (2 * π) := by positivity
          calc (2 * (2 * ε) / Real.sqrt (2 * π)) * ∫ z, ‖z‖ ∂γ
              ≤ (2 * (2 * ε) / Real.sqrt (2 * π)) * Real.sqrt (k : ℝ) :=
                mul_le_mul_of_nonneg_left hb hc
            _ = 2 * (2 * ε) * Real.sqrt (k : ℝ) / Real.sqrt (2 * π) := by ring
  -- combine
  have hkey : c₀ * γ S ≤ c₀ * ENNReal.ofReal (4 * Real.exp 2 * Real.sqrt (k : ℝ) * ε) := by
    refine le_trans (le_trans hlow hupp) (le_of_eq ?_)
    rw [hc₀, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have he : Real.exp (-2) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    field_simp
    nlinarith [he, hsq]
  exact (ENNReal.mul_le_mul_iff_right hc₀ne hc₀top).1 hkey

/-! ### The shell bounds -/

/-- The constant of the Gaussian shell bound, `C_k = 4 e² √k` (wave 22; the wave-3 coordinate
cover gave `8 k^{3/2}/√(2π)`, a factor `k` worse). Ball's sharp constant is `4 k^{1/4}`; the
`√k` here is what the single-Gaussian-shift cover of `gaussian_le_of_gaussian_shift_cover`
provably gives, and per the provable-constants rule that is what is recorded. -/
noncomputable def gaussianShellConst (k : ℕ) : ℝ := 4 * Real.exp 2 * Real.sqrt k

lemma gaussianShellConst_pos (hk : 0 < k) : 0 < gaussianShellConst k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : 0 < Real.sqrt k := Real.sqrt_pos.2 hk'
  unfold gaussianShellConst
  positivity

/-- **A convex set differs from its interior by a Gaussian-null set.** Every non-interior point of
a convex `V` carries a supporting functional, so it leaves `V` after an arbitrarily small
coordinate shift; the slice bound then gives mass `≤ 4kc/√(2π)` for every `c > 0`. -/
theorem gaussian_diff_interior_eq_zero (hk : 0 < k)
    {V : Set (EuclideanSpace ℝ (Fin k))} (hVm : MeasurableSet V) (hVc : Convex ℝ V) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (V \ interior V) = 0 := by
  have hkr : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hk)
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hk' : (0 : ℝ) < 4 * k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hle : ∀ c : ℝ, 0 < c →
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (V \ interior V)
        ≤ ENNReal.ofReal (4 * k * c / Real.sqrt (2 * π)) := by
    intro c hc
    refine gaussian_le_of_shift_cover hk hVm hVc hc.le fun x hx => ?_
    obtain ⟨u, hu0, hu⟩ := exists_inner_le_zero_of_notMem_interior hk hVc hx.2
    obtain ⟨i, d, hd, hdist⟩ := exists_dist_ge_of_inner_le_zero hk hu0
      (fun w hw => hu w (subset_closure hw)) hc.le
    refine ⟨i, d, hd, hx.1, fun hmem => ?_⟩
    have hzero := hdist _ hmem
    rw [dist_self] at hzero
    exact absurd hzero (not_le.2 (div_pos hc hkr))
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le)
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hcpos : 0 < (ε : ℝ) * Real.sqrt (2 * π) / (4 * k) := by positivity
  have hval : 4 * (k : ℝ) * ((ε : ℝ) * Real.sqrt (2 * π) / (4 * k)) / Real.sqrt (2 * π)
      = (ε : ℝ) := by
    field_simp
  have := hle _ hcpos
  rw [hval, ENNReal.ofReal_coe_nnreal] at this
  simpa using this

/-- **Outer shell bound.** For convex `B`, the `ε`-thickening adds at most `C_k ε` Gaussian
mass, `C_k = 4 e² √k`.

A point of `Bᵋ \ interior B` carries a unit supporting functional `u` of `B`, and any shift `w`
with `⟪u, w⟫ ≥ 2ε` moves it out of `Bᵋ` altogether (it would otherwise be within `ε` of some
`b ∈ B`, forcing `2ε ≤ ⟪u, x + w − b⟫ ≤ ‖x + w − b‖ < ε`). `Bᵋ` is convex and open, so
`gaussian_le_of_gaussian_shift_cover` applies to it. -/
theorem gaussian_thickening_le (hk : 0 < k) {B : Set (EuclideanSpace ℝ (Fin k))}
    (hBc : Convex ℝ B) {ε : ℝ} (hε : 0 < ε) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (Metric.thickening ε B)
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
        + ENNReal.ofReal (gaussianShellConst k * ε) := by
  rw [gaussianShellConst]
  set W := Metric.thickening ε B with hW
  have hWopen : IsOpen W := Metric.isOpen_thickening
  have hWconv : Convex ℝ W := hBc.thickening ε
  have hSm : MeasurableSet (W \ interior B) :=
    hWopen.measurableSet.diff isOpen_interior.measurableSet
  have hshell : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (W \ interior B)
      ≤ ENNReal.ofReal (4 * Real.exp 2 * Real.sqrt (k : ℝ) * ε) := by
    refine gaussian_le_of_gaussian_shift_cover hk hWopen.measurableSet hWconv hSm
      (fun x hx => hx.1) hε ?_
    intro x hx
    obtain ⟨u₀, hu₀, hu⟩ := exists_inner_le_zero_of_notMem_interior hk hBc hx.2
    have hn : 0 < ‖u₀‖ := norm_pos_iff.2 hu₀
    have hunit : ‖(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)]
      field_simp
    refine ⟨‖u₀‖⁻¹ • u₀, hunit, ?_⟩
    intro w hw hmem
    obtain ⟨b, hbB, hlt⟩ := Metric.mem_thickening_iff.1 hmem
    have h1 : ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), b - x⟫_ℝ ≤ 0 := by
      rw [real_inner_smul_left]
      have h := hu b (subset_closure hbB)
      have hinv : 0 < ‖u₀‖⁻¹ := inv_pos.2 hn
      nlinarith
    have hsplit : x + w - b = w - (b - x) := by abel
    have h3 : ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), x + w - b⟫_ℝ
        = ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), w⟫_ℝ
          - ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), b - x⟫_ℝ := by
      rw [hsplit, inner_sub_right]
    have h2 : ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), x + w - b⟫_ℝ ≤ ‖x + w - b‖ := by
      calc ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), x + w - b⟫_ℝ
          ≤ ‖(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k))‖ * ‖x + w - b‖ := real_inner_le_norm _ _
        _ = ‖x + w - b‖ := by rw [hunit, one_mul]
    have hdist : ‖x + w - b‖ < ε := by
      rw [← dist_eq_norm]
      exact hlt
    linarith
  calc multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 W
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (B ∪ (W \ interior B)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxB : x ∈ B
        · exact Or.inl hxB
        · exact Or.inr ⟨hx, fun h => hxB (interior_subset h)⟩
    _ ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
        + multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (W \ interior B) :=
        measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hshell

/-! ### The erosion (inner parallel body) -/

/-- The open `ε`-erosion of `B`: the points whose closed `ε`-ball lies in the interior of `B`.
It is open and convex, and its `ε`-thickening is contained in `B`. -/
def erosion (ε : ℝ) (B : Set (EuclideanSpace ℝ (Fin k))) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | Metric.closedBall x ε ⊆ interior B}

lemma isOpen_erosion (ε : ℝ) (B : Set (EuclideanSpace ℝ (Fin k))) : IsOpen (erosion ε B) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨δ, hδ, hsub⟩ :=
    (isCompact_closedBall x ε).exists_thickening_subset_open isOpen_interior hx
  refine ⟨δ, hδ, ?_⟩
  intro x' hx'
  simp only [erosion, Set.mem_setOf_eq]
  intro y hy
  refine hsub (Metric.mem_thickening_iff.2 ⟨y + (x - x'), ?_, ?_⟩)
  · simp only [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    have hrw : y + (x - x') - x = y - x' := by abel
    rw [hrw]
    exact hy
  · simp only [dist_eq_norm]
    have hrw : y - (y + (x - x')) = x' - x := by abel
    rw [hrw]
    have := Metric.mem_ball.1 hx'
    rw [dist_eq_norm] at this
    exact this

lemma convex_erosion {ε : ℝ} {B : Set (EuclideanSpace ℝ (Fin k))} (hB : Convex ℝ B) :
    Convex ℝ (erosion ε B) := by
  intro x hx y hy s r hs hr hsr
  simp only [erosion, Set.mem_setOf_eq] at hx hy ⊢
  intro z hz
  set v := z - (s • x + r • y) with hv
  have hvnorm : ‖v‖ ≤ ε := by
    rw [hv]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hzx : x + v ∈ interior B := by
    refine hx ?_
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hvnorm
  have hzy : y + v ∈ interior B := by
    refine hy ?_
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hvnorm
  have hzeq : s • (x + v) + r • (y + v) = z := by
    have hv' : s • v + r • v = v := by rw [← add_smul, hsr, one_smul]
    rw [smul_add, smul_add]
    have hrw : s • x + s • v + (r • y + r • v) = s • x + r • y + (s • v + r • v) := by abel
    rw [hrw, hv', hv]
    abel
  rw [← hzeq]
  exact hB.interior hzx hzy hs hr hsr

lemma thickening_erosion_subset (ε : ℝ) (B : Set (EuclideanSpace ℝ (Fin k))) :
    Metric.thickening ε (erosion ε B) ⊆ B := by
  intro y hy
  obtain ⟨a, ha, hlt⟩ := Metric.mem_thickening_iff.1 hy
  exact interior_subset (ha (Metric.mem_closedBall.2 hlt.le))

/-- **Inner shell bound.** For convex measurable `B`, eroding by `ε` costs at most `C_k ε` of
Gaussian mass. A point `x` of `B` outside the erosion has a point `z` within `ε` that is not
interior to `B`; the unit functional `u` supporting `B` at `z` satisfies
`⟪u, (x + w) − z⟫ ≥ ⟪u, w⟫ − ‖x − z‖ ≥ 2ε − ε > 0` for every shift `w` with `⟪u, w⟫ ≥ 2ε`, so
`x + w ∉ B`. -/
theorem gaussian_le_erosion_add (hk : 0 < k) {B : Set (EuclideanSpace ℝ (Fin k))}
    (hBm : MeasurableSet B) (hBc : Convex ℝ B) {ε : ℝ} (hε : 0 < ε) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (erosion ε B)
        + ENNReal.ofReal (gaussianShellConst k * ε) := by
  rw [gaussianShellConst]
  have hSm : MeasurableSet (B \ erosion ε B) :=
    hBm.diff (isOpen_erosion ε B).measurableSet
  have hshell : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (B \ erosion ε B)
      ≤ ENNReal.ofReal (4 * Real.exp 2 * Real.sqrt (k : ℝ) * ε) := by
    refine gaussian_le_of_gaussian_shift_cover hk hBm hBc hSm (fun x hx => hx.1) hε ?_
    intro x hx
    obtain ⟨z, hzball, hzint⟩ :=
      Set.not_subset.1 (hx.2 : ¬ (Metric.closedBall x ε ⊆ interior B))
    obtain ⟨u₀, hu₀, hu⟩ := exists_inner_le_zero_of_notMem_interior hk hBc hzint
    have hn : 0 < ‖u₀‖ := norm_pos_iff.2 hu₀
    have hunit : ‖(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k))‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hn)]
      field_simp
    refine ⟨‖u₀‖⁻¹ • u₀, hunit, ?_⟩
    intro w hw hmem
    have h1 : ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), (x + w) - z⟫_ℝ ≤ 0 := by
      rw [real_inner_smul_left]
      have h := hu (x + w) (subset_closure hmem)
      have hinv : 0 < ‖u₀‖⁻¹ := inv_pos.2 hn
      nlinarith
    have hsplit : (x + w) - z = w + (x - z) := by abel
    have h3 : ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), (x + w) - z⟫_ℝ
        = ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), w⟫_ℝ
          + ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), x - z⟫_ℝ := by
      rw [hsplit, inner_add_right]
    have h2 : -‖x - z‖ ≤ ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), x - z⟫_ℝ := by
      have hcs : ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), z - x⟫_ℝ ≤ ‖z - x‖ := by
        have h := real_inner_le_norm (‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)) (z - x)
        rwa [hunit, one_mul] at h
      rw [norm_sub_rev] at hcs
      have hneg : ⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), x - z⟫_ℝ
          = -⟪(‖u₀‖⁻¹ • u₀ : EuclideanSpace ℝ (Fin k)), z - x⟫_ℝ := by
        rw [← inner_neg_right]
        congr 1
        abel
      rw [hneg]
      linarith
    have hdz : ‖x - z‖ ≤ ε := by
      have h := Metric.mem_closedBall.1 hzball
      rw [dist_eq_norm] at h
      rwa [norm_sub_rev] at h
    linarith
  calc multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
          (erosion ε B ∪ (B \ erosion ε B)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ erosion ε B
        · exact Or.inl hxA
        · exact Or.inr ⟨hx, hxA⟩
    _ ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (erosion ε B)
        + multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (B \ erosion ε B) :=
        measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hshell

end GaussianShell

end StatLean.HypothesisTesting
