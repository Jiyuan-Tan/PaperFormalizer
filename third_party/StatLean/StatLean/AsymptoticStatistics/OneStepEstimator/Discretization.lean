module
public import StatLean.AsymptoticStatistics.OneStepEstimator.Linearization

@[expose] public section

/-!
# Root-n grids for discretized one-step estimation

The finite-grid step used in vdV Theorem 5.48.
-/

open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator

namespace AsymptoticStatistics.OneStepEstimator

/-- Canonical coordinatewise floor rounding to the root-`n` grid. For `n > 0`, the
displayed integer vector gives grid coordinates and the rounded point is within
`√k / √n` in Euclidean norm. No claim is made at the degenerate scale `n = 0`. -/
theorem rootNGridRound_spec {k : ℕ} (n : ℕ) (hn : 0 < n) (θ : E k) :
    let z : Fin k → ℤ := fun j => Int.floor (Real.sqrt n * θ j)
    let rounded : E k := (WithLp.equiv 2 (Fin k → ℝ)).symm
      (fun j => (z j : ℝ) / Real.sqrt n)
    (∀ j, rounded j = (z j : ℝ) / Real.sqrt n) ∧
      ‖rounded - θ‖ ≤ Real.sqrt k / Real.sqrt n := by
  dsimp only
  constructor
  · intro j; rfl
  · have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hcoord : ∀ j : Fin k,
        ‖((Int.floor (Real.sqrt n * θ j) : ℤ) : ℝ) / Real.sqrt n - θ j‖ ≤
          1 / Real.sqrt n := by
      intro j
      rw [Real.norm_eq_abs]
      have hfloor :
          |((Int.floor (Real.sqrt n * θ j) : ℤ) : ℝ) - Real.sqrt n * θ j| ≤ 1 := by
        rw [abs_le]; constructor
        · linarith [Int.sub_one_lt_floor (Real.sqrt n * θ j)]
        · linarith [Int.floor_le (Real.sqrt n * θ j)]
      rw [show ((Int.floor (Real.sqrt n * θ j) : ℤ) : ℝ) / Real.sqrt n - θ j =
          (((Int.floor (Real.sqrt n * θ j) : ℤ) : ℝ) - Real.sqrt n * θ j) /
            Real.sqrt n by field_simp]
      rw [abs_div, abs_of_pos hsqrt]
      exact (div_le_div_iff_of_pos_right hsqrt).2 hfloor
    rw [← sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hsqrt.le),
      EuclideanSpace.real_norm_sq_eq, div_pow, Real.sq_sqrt (by positivity)]
    calc
      ∑ j : Fin k, (((WithLp.equiv 2 (Fin k → ℝ)).symm
          (fun j => ((Int.floor (Real.sqrt n * θ j) : ℤ) : ℝ) / Real.sqrt n) - θ) j) ^ 2
          ≤ ∑ _j : Fin k, (1 / Real.sqrt n) ^ 2 := by
            apply Finset.sum_le_sum
            intro j _hj
            have hj := hcoord j
            change (((Int.floor (Real.sqrt n * θ j) : ℤ) : ℝ) / Real.sqrt n - θ j) ^ 2 ≤
              (1 / Real.sqrt n) ^ 2
            rw [← sq_abs]
            exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
              (by simpa [Real.norm_eq_abs] using hj)
      _ = (k : ℝ) / (Real.sqrt n) ^ 2 := by simp [div_eq_mul_inv]

private theorem gridCode_mem_Icc {k n : ℕ} (hn : 0 < n) (θ0 θ : E k)
    (M : ℝ) (hM : 0 ≤ M) (z : Fin k → ℤ)
    (hz : ∀ j, θ j = (z j : ℝ) / Real.sqrt n)
    (hlocal : Real.sqrt n * ‖θ - θ0‖ ≤ M) (j : Fin k) :
    z j - Int.floor (Real.sqrt n * θ0 j) ∈
      Finset.Icc (-Int.ceil (max M 0 + 1)) (Int.ceil (max M 0 + 1)) := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hscale : Real.sqrt n * θ j = (z j : ℝ) := by rw [hz j]; field_simp
  have hcoord : ‖(θ - θ0) j‖ ≤ ‖θ - θ0‖ := PiLp.norm_apply_le _ _
  simp only [PiLp.sub_apply, Real.norm_eq_abs] at hcoord
  have hzclose : |(z j : ℝ) - Real.sqrt n * θ0 j| ≤ M := by
    calc
      |(z j : ℝ) - Real.sqrt n * θ0 j| = Real.sqrt n * |θ j - θ0 j| := by
        rw [← hscale, ← mul_sub, abs_mul, abs_of_pos hsqrt]
      _ ≤ Real.sqrt n * ‖θ - θ0‖ := mul_le_mul_of_nonneg_left hcoord hsqrt.le
      _ ≤ M := hlocal
  have hfloor_lo := Int.sub_one_lt_floor (Real.sqrt n * θ0 j)
  have hfloor_hi := Int.floor_le (Real.sqrt n * θ0 j)
  have hceil : M + 1 ≤ ((Int.ceil (max M 0 + 1) : ℤ) : ℝ) := by
    simpa [max_eq_left hM] using Int.le_ceil (M + 1)
  simp only [Finset.mem_Icc]
  constructor
  · exact_mod_cast (show -((Int.ceil (max M 0 + 1) : ℤ) : ℝ) ≤
        (z j : ℝ) - ((Int.floor (Real.sqrt n * θ0 j) : ℤ) : ℝ) by
      rcases abs_le.mp hzclose with ⟨hzlo, _⟩; nlinarith)
  · exact_mod_cast (show
        (z j : ℝ) - ((Int.floor (Real.sqrt n * θ0 j) : ℤ) : ℝ) ≤
          ((Int.ceil (max M 0 + 1) : ℤ) : ℝ) by
      rcases abs_le.mp hzclose with ⟨_, hzhi⟩; nlinarith)

/-- In every root-`n` neighborhood, the root-`n` grid has a finite local slice whose
cardinality is bounded uniformly in `n`. This is the finite-sum input in vdV 5.48. -/
theorem rootNGrid_localFinite_uniformCard {k : ℕ} (θ0 : E k) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℕ, ∀ n : ℕ, 0 < n → ∃ S : Finset (E k), S.card ≤ C ∧
      ∀ θ : E k,
        (∃ z : Fin k → ℤ, ∀ j, θ j = (z j : ℝ) / Real.sqrt n) →
        Real.sqrt n * ‖θ - θ0‖ ≤ M → θ ∈ S := by
  classical
  let R : ℤ := Int.ceil (max M 0 + 1)
  let codes := (Finset.univ : Finset (Fin k)).pi (fun _ => Finset.Icc (-R) R)
  refine ⟨codes.card, fun n hn => ?_⟩
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  let point : (∀ j : Fin k, j ∈ (Finset.univ : Finset (Fin k)) → ℤ) → E k :=
    fun d => (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j =>
      (((Int.floor (Real.sqrt n * θ0 j) : ℤ) + d j (Finset.mem_univ j) : ℤ) : ℝ) /
        Real.sqrt n)
  let S : Finset (E k) := codes.image point
  refine ⟨S, Finset.card_image_le, fun θ hθgrid hθlocal => ?_⟩
  obtain ⟨z, hz⟩ := hθgrid
  let d : ∀ j : Fin k, j ∈ (Finset.univ : Finset (Fin k)) → ℤ :=
    fun j _ => z j - Int.floor (Real.sqrt n * θ0 j)
  have hd : d ∈ codes := by
    rw [Finset.mem_pi]; intro j _hj
    exact gridCode_mem_Icc hn θ0 θ M hM z hz hθlocal j
  have hpoint : point d = θ := by
    ext j
    dsimp only [point, d]
    change ((((Int.floor (Real.sqrt n * θ0 j) : ℤ) +
      (z j - Int.floor (Real.sqrt n * θ0 j)) : ℤ) : ℝ) / Real.sqrt n) = θ j
    rw [hz j]; congr 1; push_cast; ring
  exact Finset.mem_image.mpr ⟨d, hd, hpoint⟩

/-- Condition (5.47), evaluated at a root-`n` bounded preliminary estimator lying on
the exact root-`n` grid. The proof obligation is the uniformly finite local-grid argument
of vdV 5.48, not the uniform condition (5.44). -/
theorem pointwiseLinearization_at_discretized
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {k : ℕ} (Ψ : ℕ → Ξ → E k → E k) (pre : ℕ → Ξ → E k)
    (θ0 : E k) (V0 : Matrix (Fin k) (Fin k) ℝ)
    -- vdV condition (5.47), with its complete deterministic-sequence quantifier.
    (h47 : ∀ θn : ℕ → E k,
      (∃ M : ℝ, ∀ᶠ n : ℕ in atTop, Real.sqrt n * ‖θn n - θ0‖ ≤ M) →
      TendstoInProbZero (fun _ : ℕ => μ)
        (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (θn n)))
    -- root-`n` boundedness of the preliminary estimator.
    (hpre : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (pre n ξ - θ0)))
    -- exact root-`n` grid condition from vdV Theorem 5.48.
    (hgrid : ∀ n, 0 < n → ∀ ξ, ∃ z : Fin k → ℤ, ∀ j,
      pre n ξ j = (z j : ℝ) / Real.sqrt n) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)) := by
  classical
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨M0, hM0⟩ := hpre (η / 2) (by positivity)
  let M : ℝ := max M0 0
  have hM_nonneg : 0 ≤ M := le_max_right _ _
  have hM0M : M0 ≤ M := le_max_left _ _
  let R : ℤ := Int.ceil (max M 0 + 1)
  let codes := (Finset.univ : Finset (Fin k)).pi (fun _ => Finset.Icc (-R) R)
  let point : ℕ → (∀ j : Fin k, j ∈ (Finset.univ : Finset (Fin k)) → ℤ) → E k :=
    fun n d => if n = 0 then θ0 else
      (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j =>
        (((Int.floor (Real.sqrt n * θ0 j) : ℤ) + d j (Finset.mem_univ j) : ℤ) : ℝ) /
          Real.sqrt n)
  have hpoint_bounded
      (d : ∀ j : Fin k, j ∈ (Finset.univ : Finset (Fin k)) → ℤ) :
      ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, Real.sqrt n * ‖point n d - θ0‖ ≤ B := by
    let offset : E k := (WithLp.equiv 2 (Fin k → ℝ)).symm
      (fun j => (d j (Finset.mem_univ j) : ℝ))
    refine ⟨Real.sqrt k + ‖offset‖, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
    have hnpos : 0 < n := Nat.zero_lt_of_lt hn
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
    let rounded : E k := (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j =>
      ((Int.floor (Real.sqrt n * θ0 j) : ℤ) : ℝ) / Real.sqrt n)
    have hround : ‖rounded - θ0‖ ≤ Real.sqrt k / Real.sqrt n :=
      (rootNGridRound_spec n hnpos θ0).2
    have hpoint : point n d = rounded + (1 / Real.sqrt n) • offset := by
      ext j
      simp only [point, if_neg hnpos.ne', rounded, offset, PiLp.add_apply, PiLp.smul_apply]
      change (((((Int.floor (Real.sqrt n * θ0 j) : ℤ) +
        d j (Finset.mem_univ j) : ℤ) : ℝ) / Real.sqrt n)) =
          ((Int.floor (Real.sqrt n * θ0 j) : ℤ) : ℝ) / Real.sqrt n +
            (1 / Real.sqrt n) * (d j (Finset.mem_univ j) : ℝ)
      rw [Int.cast_add]; ring
    rw [hpoint]
    calc
      Real.sqrt n * ‖rounded + (1 / Real.sqrt n) • offset - θ0‖
          ≤ Real.sqrt n * (‖rounded - θ0‖ + ‖(1 / Real.sqrt n) • offset‖) := by
            gcongr
            rw [show rounded + (1 / Real.sqrt n) • offset - θ0 =
              (rounded - θ0) + (1 / Real.sqrt n) • offset by abel]
            exact norm_add_le _ _
      _ ≤ Real.sqrt n * (Real.sqrt k / Real.sqrt n +
          (1 / Real.sqrt n) * ‖offset‖) := by
            gcongr; simp [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt]
      _ = Real.sqrt k + ‖offset‖ := by field_simp
  have hcode (d : ∀ j : Fin k, j ∈ (Finset.univ : Finset (Fin k)) → ℤ) :
      TendstoInProbZero (fun _ : ℕ => μ)
        (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (point n d)) :=
    h47 (fun n => point n d) (hpoint_bounded d)
  have hsum : Tendsto (fun n => ∑ d ∈ codes,
      μ.real {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (point n d)‖})
      atTop (𝓝 0) := by
    simpa using tendsto_finset_sum codes (fun d _hd => hcode d ε hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum (η / 2) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le ((le_max_right N 1).trans hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hcover :
      {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)‖} ⊆
        {ξ | M < ‖Real.sqrt n • (pre n ξ - θ0)‖} ∪
          ⋃ d ∈ codes, {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (point n d)‖} := by
    intro ξ hξ
    by_cases hout : M < ‖Real.sqrt n • (pre n ξ - θ0)‖
    · exact Or.inl hout
    · right
      have hin : ‖Real.sqrt n • (pre n ξ - θ0)‖ ≤ M := not_lt.mp hout
      have hin' : Real.sqrt n * ‖pre n ξ - θ0‖ ≤ M := by
        simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt] using hin
      obtain ⟨z, hz⟩ := hgrid n hnpos ξ
      let d : ∀ j : Fin k, j ∈ (Finset.univ : Finset (Fin k)) → ℤ :=
        fun j _ => z j - Int.floor (Real.sqrt n * θ0 j)
      have hd : d ∈ codes := by
        rw [Finset.mem_pi]; intro j _hj
        exact gridCode_mem_Icc hnpos θ0 (pre n ξ) M hM_nonneg z hz hin' j
      have hpoint : point n d = pre n ξ := by
        ext j
        simp only [point, if_neg hnpos.ne', d]
        change ((((Int.floor (Real.sqrt n * θ0 j) : ℤ) +
          (z j - Int.floor (Real.sqrt n * θ0 j)) : ℤ) : ℝ) / Real.sqrt n) = pre n ξ j
        rw [hz j]; congr 1; push_cast; ring
      change ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)‖ at hξ
      rw [← hpoint] at hξ
      exact Set.mem_iUnion_of_mem d (Set.mem_iUnion_of_mem hd hξ)
  have hescape : μ.real {ξ | M < ‖Real.sqrt n • (pre n ξ - θ0)‖} ≤ η / 2 :=
    (measureReal_mono (fun ξ hξ => lt_of_le_of_lt hM0M hξ)).trans (hM0 n)
  have hunion : μ.real (⋃ d ∈ codes,
      {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (point n d)‖}) ≤
      ∑ d ∈ codes, μ.real {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (point n d)‖} :=
    measureReal_biUnion_finset_le _ _
  have hsum_small :
      ∑ d ∈ codes, μ.real {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (point n d)‖} <
        η / 2 := by
    have := hN n hnN
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg)] at this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc
    μ.real {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)‖}
        ≤ μ.real {ξ | M < ‖Real.sqrt n • (pre n ξ - θ0)‖} +
            μ.real (⋃ d ∈ codes,
              {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (point n d)‖}) :=
          (measureReal_mono hcover).trans (measureReal_union_le _ _)
    _ ≤ η / 2 +
          ∑ d ∈ codes, μ.real {ξ | ε ≤ ‖oneStepResidual Ψ θ0 V0 n ξ (point n d)‖} :=
      add_le_add hescape hunion
    _ < η := by linarith

end AsymptoticStatistics.OneStepEstimator
