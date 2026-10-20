module
public import StatLean.ConcentrationInequalities.Maximal.CoveringBall
public import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Finite ε-nets of Euclidean balls, as `Finset`s (C10)

The shell decomposition of the DL contraction proof (`ShellDecomposition`) needs, for each support
set `S`, an explicit **finite** ε-net of a Euclidean ball together with a cardinality bound. Mathlib
and the concentration-inequalities area already provide the volumetric covering-number estimate
`coveringNumber (closedBall 0 1) ε ≤ ⌊(1 + 2/ε)^d⌋` (`CoveringBall.lean`, Lu-BDA §6.2). This file
repackages it into the ready-to-use existential form — a `Finset F` of centres, each in the ball,
covering the ball to accuracy `ε`, with `|F| ≤ (1 + 2/ε)^d` — and lifts it from the unit ball to an
arbitrary ball `B(x₀, R)` in any finite-dimensional real inner-product space (cardinality bound
`(1 + 2R/ε)^{finrank}`).

Both statements reuse the covering bricks; no new geometry is proved here. The unit-ball extraction
mirrors `HighDimensionalStatistics/CompressedSensing/RandomRIP.lean`'s `exists_quarter_net`
(minimal-cover / `encard` idiom). This cross-area import of the concentration-inequalities concept
layer follows that established precedent.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 6 (Bernstein and Maximal Inequalities), §6.2 — Definition 6.2
(ε-Net) and Lemma 6.1 (Covering Number). Used in BPPD §6 as the sieve/net over each support shell.

**Proof formalization notes.** `exists_finset_net_unitBall`: instantiate
`coveringNumber_closedBall_le` at radius `ε`, then extract a `Finset` from the finite
`Metric.minimalCover` exactly as `exists_quarter_net` does (`Metric.finite_minimalCover`,
`Metric.encard_minimalCover`, `Metric.isCover_minimalCover`, `Set.Finite.toFinset`).
`exists_finset_net_closedBall`: transport an orthonormal-basis isometry `E ≃ₗᵢ EuclideanSpace ℝ (Fin
(finrank))` (`stdOrthonormalBasis`) to reduce to `EuclideanSpace ℝ (Fin d)`, then scale by `R` and
translate by `x₀` (a net of `B(0,1)` at accuracy `ε/R` dilates to a net of `B(x₀, R)` at accuracy
`ε`, with the cardinality bound `(1 + 2/(ε/R))^d = (1 + 2R/ε)^{finrank}`).
-/

open MeasureTheory Metric
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

open StatLean.ConcentrationInequalities

variable {ι : Type*} [Fintype ι]

/-- **Explicit finite ε-net of the Euclidean unit ball** (Lu-BDA §6.2, `Finset` packaging).

For `0 < ε < 1` and `d ≥ 1` there is a finite set `F ⊆ B(0, 1) ⊆ ℝ^d` of centres, covering the
closed unit ball to accuracy `ε` (every point is within `ε` of some centre), with
`|F| ≤ (1 + 2/ε)^d`. This is the existential/`Finset` form of `coveringNumber_closedBall_le`. -/
lemma exists_finset_net_unitBall (d : ℕ) [NeZero d] {ε : ℝ}
    -- USER-INPUT: 0 < ε (net accuracy positive); Lu-BDA §6.2, Lemma 6.1
    (hε : 0 < ε)
    -- USER-INPUT: ε < 1 (matches the book's covering-number regime); Lu-BDA §6.2, Lemma 6.1
    (hε1 : ε < 1) :
    ∃ F : Finset (EuclideanSpace ℝ (Fin d)),
      ↑F ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ∃ c ∈ F, dist x c ≤ ε) ∧
      (F.card : ℝ) ≤ (1 + 2 / ε) ^ d := by
  classical
  have hcn := coveringNumber_closedBall_le (d := d) hε hε1
  have hcn' : Metric.coveringNumber (Real.toNNReal ε)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ (⌊(1 + 2 / ε) ^ d⌋₊ : ℕ∞) := hcn
  have hne : Metric.coveringNumber (Real.toNNReal ε)
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) hcn'
  set C := Metric.minimalCover (Real.toNNReal ε)
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) with hCdef
  have hCfin : C.Finite := Metric.finite_minimalCover
  have hencard : C.encard ≤ (⌊(1 + 2 / ε) ^ d⌋₊ : ℕ∞) := by
    rw [hCdef, Metric.encard_minimalCover hne]; exact hcn'
  obtain ⟨_, hncard⟩ := Set.encard_le_coe_iff_finite_ncard_le.mp hencard
  refine ⟨hCfin.toFinset, ?_, ?_, ?_⟩
  · intro v hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hv
    exact Metric.minimalCover_subset hv
  · intro x hx
    obtain ⟨y, hyC, hxy⟩ := Metric.isCover_minimalCover hne hx
    refine ⟨y, Set.Finite.mem_toFinset hCfin |>.mpr hyC, ?_⟩
    rw [← edist_le_ofReal hε.le]
    exact hxy
  · rw [← Set.ncard_eq_toFinset_card C hCfin]
    calc (C.ncard : ℝ) ≤ (⌊(1 + 2 / ε) ^ d⌋₊ : ℝ) := by exact_mod_cast hncard
      _ ≤ (1 + 2 / ε) ^ d := Nat.floor_le (by positivity)

/-- **Explicit finite ε-net of an arbitrary Euclidean ball** (Lu-BDA §6.2, general form).

In any finite-dimensional real inner-product space `E`, the closed ball `B(x₀, R)` (with `0 < ε < R`)
has a finite ε-net `F ⊆ B(x₀, R)` with `|F| ≤ (1 + 2R/ε)^{finrank ℝ E}`. Obtained from the unit-ball
net by an orthonormal-basis isometry to `EuclideanSpace ℝ (Fin (finrank))`, scaling by `R`, and
translating by `x₀`. -/
lemma exists_finset_net_closedBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x₀ : E) (R ε : ℝ)
    -- USER-INPUT: 0 < R (ball radius positive); Lu-BDA §6.2, Lemma 6.1
    (hR : 0 < R)
    -- USER-INPUT: 0 < ε (net accuracy positive); Lu-BDA §6.2, Lemma 6.1
    (hε : 0 < ε)
    -- USER-INPUT: ε < R (net finer than the ball); Lu-BDA §6.2, Lemma 6.1
    (hεR : ε < R) :
    ∃ F : Finset E,
      ↑F ⊆ Metric.closedBall x₀ R ∧
      (∀ x ∈ Metric.closedBall x₀ R, ∃ c ∈ F, dist x c ≤ ε) ∧
      (F.card : ℝ) ≤ (1 + 2 * R / ε) ^ (Module.finrank ℝ E) := by
  classical
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn0 | hnpos
  · -- Trivial space: `E` is a subsingleton, `closedBall x₀ R = {x₀}`.
    have hall : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hn0
    refine ⟨{x₀}, ?_, ?_, ?_⟩
    · intro c hc
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hc
      subst hc
      simp [Metric.mem_closedBall, hR.le]
    · intro x _
      refine ⟨x₀, Finset.mem_singleton_self _, ?_⟩
      have hxx : x = x₀ := by rw [hall x, hall x₀]
      rw [hxx, dist_self]; exact hε.le
    · rw [hn0, pow_zero]; simp
  · -- Nontrivial space: transport the unit-ball net through the orthonormal isometry.
    haveI : NeZero (Module.finrank ℝ E) := ⟨hnpos.ne'⟩
    set e := (stdOrthonormalBasis ℝ E).repr with he
    have hεR' : ε / R < 1 := (div_lt_one hR).mpr hεR
    have hεR0 : 0 < ε / R := div_pos hε hR
    obtain ⟨F₀, hF₀ball, hF₀cover, hF₀card⟩ :=
      exists_finset_net_unitBall (Module.finrank ℝ E) hεR0 hεR'
    set φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E :=
      fun u => x₀ + R • e.symm u with hφ
    have hφ0 : φ 0 = x₀ := by simp [hφ]
    have hdist : ∀ u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
        dist (φ u) (φ v) = R * dist u v := by
      intro u v
      simp only [hφ, dist_eq_norm]
      have hsub : (x₀ + R • e.symm u) - (x₀ + R • e.symm v) = R • (e.symm u - e.symm v) := by
        rw [smul_sub]; abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hR, ← e.symm.map_sub, e.symm.norm_map]
    refine ⟨F₀.image φ, ?_, ?_, ?_⟩
    · -- The net sits inside `closedBall x₀ R`.
      intro y hy
      rw [Finset.coe_image, Set.mem_image] at hy
      obtain ⟨c, hcF₀, rfl⟩ := hy
      rw [Metric.mem_closedBall]
      have hc1 : dist c 0 ≤ 1 := Metric.mem_closedBall.mp (hF₀ball hcF₀)
      have hdc0 : dist (φ c) x₀ = R * dist c 0 := by rw [← hφ0]; exact hdist c 0
      rw [hdc0]
      calc R * dist c 0 ≤ R * 1 := mul_le_mul_of_nonneg_left hc1 hR.le
        _ = R := mul_one R
    · -- Every ball point is within `ε` of a net point.
      intro x hx
      set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := R⁻¹ • e (x - x₀) with hu
      have hφu : φ u = x := by
        simp only [hφ, hu, map_smul, e.symm_apply_apply]
        rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
        abel
      have hxx0 : dist x x₀ ≤ R := Metric.mem_closedBall.mp hx
      have hu1 : dist u 0 ≤ 1 := by
        rw [dist_zero_right, hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
            e.norm_map, ← dist_eq_norm]
        calc R⁻¹ * dist x x₀ ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hxx0 (inv_pos.mpr hR).le
          _ = 1 := inv_mul_cancel₀ hR.ne'
      obtain ⟨c, hcF₀, hdc⟩ := hF₀cover u (Metric.mem_closedBall.mpr hu1)
      refine ⟨φ c, Finset.mem_image_of_mem φ hcF₀, ?_⟩
      rw [← hφu, hdist]
      calc R * dist u c ≤ R * (ε / R) := mul_le_mul_of_nonneg_left hdc hR.le
        _ = ε := by field_simp
    · -- Cardinality bound: `|F| ≤ |F₀| ≤ (1 + 2R/ε)^{finrank}`.
      calc ((F₀.image φ).card : ℝ) ≤ (F₀.card : ℝ) := by exact_mod_cast Finset.card_image_le
        _ ≤ (1 + 2 / (ε / R)) ^ (Module.finrank ℝ E) := hF₀card
        _ = (1 + 2 * R / ε) ^ (Module.finrank ℝ E) := by rw [div_div_eq_mul_div]

end StatLean.Bayesian
