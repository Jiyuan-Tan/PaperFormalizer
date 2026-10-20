module
public import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Covering number of the ℓ²-unit ball

For a dimension `d ≥ 1` and a radius `ε ∈ (0, 1)`, the covering number of the closed Euclidean
unit ball `B = {x ∈ ℝ^d : ‖x‖₂ ≤ 1}` — the minimum number of Euclidean balls of radius `ε`
needed to cover `B` — is bounded by

  `N(B, ‖·‖₂, ε) ≤ (1 + 2/ε)^d`.

This is the standard volume/packing estimate for the ℓ² ball. In the formalization the bound is
stated with the floor on the right-hand side, `N(B, ‖·‖₂, ε) ≤ ⌊(1 + 2/ε)^d⌋`, because the
covering number is an extended-natural-number quantity.

The argument is a packing bound. Take any ε-separated subset `C ⊆ B` (any two distinct points are
at distance `> ε`). The open balls of radius `ε/2` centered at the points of `C` are pairwise
disjoint, and they are all contained in the ball of radius `1 + ε/2` about the origin. Comparing
(Haar/Lebesgue) volumes gives `|C| · (ε/2)^d · Vol(B₀¹) ≤ (1 + ε/2)^d · Vol(B₀¹)`, hence
`|C| ≤ (1 + 2/ε)^d`. Since the covering number is bounded by the packing number, the same bound
holds for `N(B, ‖·‖₂, ε)`.

## Main results

* `card_le_of_isSeparated_ball` — volume packing bound: any finite ε-separated subset of
  `closedBall 0 1` has cardinality ≤ `(1 + 2/ε)^d`.
* `coveringNumber_closedBall_le` — main theorem.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 6 (Bernstein and Maximal Inequalities),
§6.2, Lemma 6.1 (Covering Number) ("Covering number of the
ℓ₂-ball"). The book states the bound for `ε ∈ (0, 1)`; this hypothesis (`hε₁ : ε < 1`) is carried
to match the text but is not needed in the proof — the volume packing bound holds for all `ε > 0`.

**Proof formalization notes.** The proof follows Lu §6.2 via the volume argument. Take any
ε-separated set `C` inside the ball; the open balls `ball(x, ε/2)` for `x ∈ C` are pairwise
disjoint and all contained in `ball(0, 1 + ε/2)`. Comparing Haar measures via
`Measure.addHaar_ball_of_pos` gives `|C| · (ε/2)^d ≤ (1 + ε/2)^d`, which rearranges to
`|C| ≤ (1 + 2/ε)^d`. The main theorem then uses `coveringNumber ≤ packingNumber`
(`Metric.coveringNumber_le_packingNumber`) and bounds the packing number by the above. Whereas the
book argues that the ε-net itself induces a cover whose dilated balls contain `B`, the Lean proof
runs the dual (separated-set / packing) version, which is equivalent and meshes with Mathlib's
`coveringNumber ≤ packingNumber` API; the resulting constant `(1 + 2/ε)^d` is identical to the
book's.

**Bibliographic comments.** This is a folklore volume/packing estimate with no single seminal
origin; it is a standard tool in high-dimensional geometry and the analysis of empirical processes.
The volume-comparison technique underlying it goes back to the classical bounds on metric entropy of
convex bodies (see e.g. A. N. Kolmogorov and V. M. Tikhomirov, "ε-entropy and ε-capacity of sets
in function spaces," *Uspekhi Mat. Nauk* 14 (1959), no. 2, 3–86).
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

/-! ### Volume-based packing bound -/

/-- **Packing bound for the ℓ²-unit ball** (Lu-BDA §6.2, helper).

Any *finite* ε-separated subset `C` of the closed unit ball in `EuclideanSpace ℝ (Fin d)` has
cardinality `(C.ncard : ℝ) ≤ (1 + 2/ε)^d`.

Proof: the open balls `ball(x, ε/2)` for `x ∈ C` are pairwise disjoint (ε-separation) and all
contained in `ball(0, 1 + ε/2)`.  Comparing Haar measures via `Measure.addHaar_ball_of_pos`
gives `|C| · (ε/2)^d · vol(B₀¹) ≤ (1 + ε/2)^d · vol(B₀¹)`; dividing by `vol(B₀¹) > 0` and
`(ε/2)^d > 0` yields the claim. -/
lemma card_le_of_isSeparated_ball {d : ℕ} [NeZero d] {ε : ℝ} (hε₀ : 0 < ε)
    {C : Set (EuclideanSpace ℝ (Fin d))}
    (hfin : C.Finite)
    (hC : C ⊆ Metric.closedBall 0 1)
    (hsep : Metric.IsSeparated (ENNReal.ofReal ε) C) :
    (C.ncard : ℝ) ≤ (1 + 2 / ε) ^ d := by
  -- Work with the finset F = hfin.toFinset.
  haveI : Fintype C := hfin.fintype
  set F := hfin.toFinset with hF_def
  have hFC : (F : Set _) = C := hfin.coe_toFinset
  have hncard : C.ncard = F.card := by rw [← hFC, Set.ncard_coe_finset]
  rw [hncard]
  -- Set up the Haar measure on EuclideanSpace ℝ (Fin d).
  haveI hHaar : Measure.IsAddHaarMeasure (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    have hb : Measure.IsAddHaarMeasure ((EuclideanSpace.basisFun (Fin d) ℝ).toBasis.addHaar) :=
      isAddHaarMeasure_basis_addHaar _
    rwa [(EuclideanSpace.basisFun (Fin d) ℝ).addHaar_eq_volume] at hb
  haveI hProper : ProperSpace (EuclideanSpace ℝ (Fin d)) := FiniteDimensional.proper ℝ _
  haveI hFinComp : IsFiniteMeasureOnCompacts (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  -- Abbreviate the measure.
  set μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))
  -- finrank ℝ (EuclideanSpace ℝ (Fin d)) = d.
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  -- Volume of each small ball ball(x, ε/2).
  have hsmall : ∀ x : EuclideanSpace ℝ (Fin d),
      μ (Metric.ball x (ε / 2)) =
      ENNReal.ofReal ((ε / 2) ^ d) * μ (Metric.ball 0 1) := by
    intro x
    rw [Measure.addHaar_ball_of_pos μ x (half_pos hε₀), hfr]
  -- Volume of the large ball ball(0, 1 + ε/2).
  have hlarge : μ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 + ε / 2)) =
      ENNReal.ofReal ((1 + ε / 2) ^ d) * μ (Metric.ball 0 1) := by
    rw [Measure.addHaar_ball_of_pos μ 0 (by linarith), hfr]
  -- Pairwise disjointness of balls ball(x, ε/2) for x ∈ F.
  have hdisj : Set.PairwiseDisjoint (F : Set (EuclideanSpace ℝ (Fin d)))
      (fun x => Metric.ball x (ε / 2)) := by
    intro x hxF y hyF hne
    simp only [Function.onFun]
    apply Metric.ball_disjoint_ball
    have hsep_xy : ENNReal.ofReal ε < edist x y := hsep (hFC ▸ hxF) (hFC ▸ hyF) hne
    rw [edist_dist] at hsep_xy
    have hdist : ε < dist x y := (ENNReal.ofReal_lt_ofReal_iff'.mp hsep_xy).1
    linarith
  -- Measurability of balls.
  have hmeas : ∀ b ∈ F, MeasurableSet (Metric.ball b (ε / 2)) :=
    fun _ _ => isOpen_ball.measurableSet
  -- Containment: ⋃ x ∈ F, ball(x, ε/2) ⊆ ball(0, 1 + ε/2).
  have hcont : (⋃ x ∈ F, Metric.ball x (ε / 2)) ⊆
      Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 + ε / 2) := by
    intro y hy
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨x, hxF, hyx⟩ := hy
    have hxC : x ∈ C := hFC ▸ Finset.mem_coe.mpr hxF
    rw [Metric.mem_ball] at hyx ⊢
    have hx1 : dist x 0 ≤ 1 := Metric.mem_closedBall.mp (hC hxC)
    calc dist y 0
        ≤ dist y x + dist x 0 := dist_triangle y x 0
      _ < ε / 2 + 1 := by linarith
      _ = 1 + ε / 2 := by ring
  -- Positivity and finiteness of μ(ball 0 1).
  have hv_pos : 0 < μ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    measure_ball_pos μ 0 one_pos
  have hv_lt_top : μ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤ :=
    measure_ball_lt_top
  -- Main ENNReal chain.
  have hmeasure_chain :
      (F.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d) * μ (Metric.ball 0 1) ≤
      ENNReal.ofReal ((1 + ε / 2) ^ d) * μ (Metric.ball 0 1) := by
    calc (F.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d) * μ (Metric.ball 0 1)
        = ∑ _x ∈ F, ENNReal.ofReal ((ε / 2) ^ d) * μ (Metric.ball 0 1) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = ∑ x ∈ F, μ (Metric.ball x (ε / 2)) := by simp_rw [hsmall]
      _ = μ (⋃ x ∈ F, Metric.ball x (ε / 2)) := (measure_biUnion_finset hdisj hmeas).symm
      _ ≤ μ (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) (1 + ε / 2)) := measure_mono hcont
      _ = ENNReal.ofReal ((1 + ε / 2) ^ d) * μ (Metric.ball 0 1) := hlarge
  -- Cancel μ(ball 0 1) from both sides.
  have hcancel :
      (F.card : ℝ≥0∞) * ENNReal.ofReal ((ε / 2) ^ d) ≤ ENNReal.ofReal ((1 + ε / 2) ^ d) :=
    (ENNReal.mul_le_mul_iff_left hv_pos.ne' hv_lt_top.ne).mp hmeasure_chain
  -- Convert to ℝ.
  have hreal : (F.card : ℝ) * (ε / 2) ^ d ≤ (1 + ε / 2) ^ d := by
    have h := (ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top).mpr hcancel
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
         ENNReal.toReal_ofReal (pow_nonneg (by linarith) d),
         ENNReal.toReal_ofReal (pow_nonneg (by linarith) d)] at h
  -- Divide by (ε/2)^d > 0 and simplify.
  have hε2_pos : 0 < (ε / 2) ^ d := by positivity
  calc (F.card : ℝ)
      ≤ (1 + ε / 2) ^ d / (ε / 2) ^ d := (le_div_iff₀ hε2_pos).mpr hreal
    _ = ((1 + ε / 2) / (ε / 2)) ^ d := (div_pow _ _ d).symm
    _ = (1 + 2 / ε) ^ d := by congr 1; field_simp; ring

/-! ### Main theorem -/

/-- **Covering number of the ℓ²-unit ball** (Lu-BDA §6.2, Lemma 6.1 (Covering Number)).

For `0 < ε < 1` and `d ≥ 1`, the covering number of the closed unit ball satisfies
`coveringNumber (closedBall 0 1) ε ≤ ⌊(1 + 2/ε)^d⌋₊`.

Proof: covering number ≤ packing number (`Metric.coveringNumber_le_packingNumber`); every
ε-separated subset is finite with ncard ≤ `(1 + 2/ε)^d` by `card_le_of_isSeparated_ball`.

Note: `hε₁ : ε < 1` matches Lu §6.2 but is not used in the proof body; the bound holds for
all `0 < ε`. -/
theorem coveringNumber_closedBall_le {d : ℕ} [NeZero d] {ε : ℝ}
    -- USER-INPUT: ε > 0; Lu-BDA §6.2, Lemma 6.1 (Covering Number)
    (hε₀ : 0 < ε)
    -- USER-INPUT: ε < 1; Lu-BDA §6.2, Lemma 6.1 (Covering Number)
    (hε₁ : ε < 1) :
    coveringNumber (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ε ≤
    (⌊(1 + 2 / ε) ^ d⌋₊ : ℕ∞) := by
  -- Unfold our wrapper to Mathlib's coveringNumber.
  unfold coveringNumber
  -- coveringNumber ε B ≤ packingNumber ε B ≤ ⌊(1+2/ε)^d⌋₊.
  apply (Metric.coveringNumber_le_packingNumber (Real.toNNReal ε) _).trans
  -- Bound packingNumber: for every ε-separated C ⊆ B, C.encard ≤ ⌊(1+2/ε)^d⌋₊.
  simp only [Metric.packingNumber, iSup_le_iff]
  intro C hCB hsep
  -- Goal: C.encard ≤ (⌊(1+2/ε)^d⌋₊ : ℕ∞).
  rw [Set.encard_le_coe_iff_finite_ncard_le]
  -- Step 1: C is finite.
  have hfin : C.Finite := by
    by_contra hinf
    have hinf' : C.Infinite := Set.not_finite.mp hinf
    set n := ⌊(1 + 2 / ε) ^ d⌋₊ + 1
    obtain ⟨C', hC'_sub, hC'_fin, hC'_ncard⟩ := hinf'.exists_subset_ncard_eq n
    -- C' ⊆ closedBall 0 1 and ε-separated.
    -- hsep : IsSeparated (↑(Real.toNNReal ε) : ℝ≥0∞) C
    -- = IsSeparated (ENNReal.ofReal ε) C by definition (ENNReal.ofReal r := ↑(toNNReal r)).
    have hC'_sep : Metric.IsSeparated (ENNReal.ofReal ε) C' := hsep.subset hC'_sub
    have hle := card_le_of_isSeparated_ball hε₀ hC'_fin (hC'_sub.trans hCB) hC'_sep
    rw [hC'_ncard] at hle
    have hfloor : (1 + 2 / ε) ^ d < (n : ℝ) := by
      push_cast [n]; linarith [Nat.lt_floor_add_one ((1 + 2 / ε) ^ d)]
    linarith
  -- Step 2: C.ncard ≤ ⌊(1+2/ε)^d⌋₊.
  refine ⟨hfin, ?_⟩
  -- hsep : IsSeparated (↑(Real.toNNReal ε)) C = IsSeparated (ENNReal.ofReal ε) C (def. eq.)
  have hle := card_le_of_isSeparated_ball hε₀ hfin hCB hsep
  exact Nat.le_floor hle

end StatLean.ConcentrationInequalities
