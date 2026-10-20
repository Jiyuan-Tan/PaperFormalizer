module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker

@[expose] public section

/-!
# Chebyshev bounds for iid empirical-process marginals

This file proves the fixed-function `L²(P)` tail bound for the empirical process
under iid sampling. It also proves the corresponding
bound for a difference of two fixed `L²(P)` functions in terms of `distL2`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal

/-- **Chebyshev tail of one empirical-process marginal.** For an iid sample of
law `P` and `f ∈ L²(P)`, the centered empirical process satisfies
`P(|𝔾ₙf| ≥ M) ≤ P(f²) / M²`.

The bound is valid also at `n = 0`, where the empirical process vanishes. -/
theorem empiricalProcess_chebyshev_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (n : ℕ) (f : Ω → ℝ) (hf_L2 : MemLp f 2 P) {M : ℝ} (hM : 0 < M) :
    μ {ξ | M ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) f|}
      ≤ ENNReal.ofReal ((∫ x, (f x) ^ 2 ∂P) / M ^ 2) := by
  classical
  -- Centre `f`: `c = Pf`, `g = f − c` (mean-zero under `P`).
  set c : ℝ := ∫ x, f x ∂P with hc
  set g : Ω → ℝ := fun x => f x - c with hg
  have hf_int : Integrable f P := hf_L2.integrable one_le_two
  have hg_L2 : MemLp g 2 P := hf_L2.sub (memLp_const c)
  have hg_aem : AEMeasurable g P := hg_L2.aestronglyMeasurable.aemeasurable
  have hg_int : Integrable g P := hg_L2.integrable one_le_two
  have hg_mean : ∫ x, g x ∂P = 0 := by
    simp only [hg]
    rw [integral_sub hf_int (integrable_const c), integral_const, probReal_univ,
      one_smul, hc, sub_self]
  -- Per-index map facts: `μ.map (X i) = P`, so `g ∘ Xᵢ` is `L²` / mean-zero / iid.
  have hX_aem : ∀ i, AEMeasurable (X i) μ := fun i => (hX_meas i).aemeasurable
  have hmap : ∀ i, μ.map (X i) = P := fun i => (hX_id i).map_eq.trans hX_law
  have hg_aem_map : ∀ i, AEMeasurable g (μ.map (X i)) := by
    intro i; rw [hmap i]; exact hg_aem
  have hgX_L2 : ∀ i, MemLp (g ∘ X i) 2 μ := by
    intro i
    have hgm : MemLp g 2 (μ.map (X i)) := by rw [hmap i]; exact hg_L2
    exact hgm.comp_of_map (hX_aem i)
  have hgX_indep : ProbabilityTheory.iIndepFun (fun i => g ∘ X i) μ :=
    hX_indep.comp₀ (fun _ => g) hX_aem hg_aem_map
  have hgX_idem : ∀ i, ProbabilityTheory.IdentDistrib (g ∘ X i) (g ∘ X 0) μ μ :=
    fun i => (hX_id i).comp_of_aemeasurable (hg_aem_map i)
  have hX0_aem : AEMeasurable (X 0) μ := hX_aem 0
  have hgX0_mean : ∫ ξ, g (X 0 ξ) ∂μ = 0 := by
    have hg_asm_map : AEStronglyMeasurable g (μ.map (X 0)) := by
      rw [hmap 0]; exact hg_L2.aestronglyMeasurable
    have h_int : ∫ ξ, g (X 0 ξ) ∂μ = ∫ x, g x ∂(μ.map (X 0)) :=
      (integral_map hX0_aem hg_asm_map).symm
    rw [h_int, hmap 0, hg_mean]
  have hgX_mean : ∀ i, ∫ ξ, g (X i ξ) ∂μ = 0 := by
    intro i
    have h_eq : ∫ ξ, (g ∘ X i) ξ ∂μ = ∫ ξ, (g ∘ X 0) ξ ∂μ := (hgX_idem i).integral_eq
    simpa [Function.comp_apply] using h_eq.trans hgX0_mean
  -- `V = ∫ g² ∂P`; equals `variance (g ∘ Xᵢ)`, and is at most `∫ f² ∂P`.
  set V : ℝ := ∫ x, (g x) ^ 2 ∂P with hV
  have hgX0_var : ProbabilityTheory.variance (g ∘ X 0) μ = V := by
    have h_aem : AEMeasurable (g ∘ X 0) μ := (hgX_L2 0).aestronglyMeasurable.aemeasurable
    rw [ProbabilityTheory.variance_eq_integral h_aem,
      show (∫ ω, (g ∘ X 0) ω ∂μ) = 0 from hgX0_mean]
    simp only [sub_zero, Function.comp_apply]
    have hg_sq_asm_map : AEStronglyMeasurable (fun x : Ω => (g x) ^ 2) (μ.map (X 0)) := by
      rw [hmap 0]; exact (hg_aem.pow_const 2).aestronglyMeasurable
    have h_int : ∫ ξ, (g (X 0 ξ)) ^ 2 ∂μ = ∫ x, (g x) ^ 2 ∂(μ.map (X 0)) :=
      (integral_map hX0_aem hg_sq_asm_map).symm
    rw [h_int, hmap 0]
  have hgXi_var : ∀ i, ProbabilityTheory.variance (g ∘ X i) μ = V :=
    fun i => (hgX_idem i).variance_eq.trans hgX0_var
  have hVle : V ≤ ∫ x, (f x) ^ 2 ∂P := by
    have e1 : V = ProbabilityTheory.variance g P := by
      rw [ProbabilityTheory.variance_eq_sub hg_L2, hg_mean, hV]; simp [Pi.pow_apply]
    have e2 : ProbabilityTheory.variance g P = ProbabilityTheory.variance f P :=
      ProbabilityTheory.variance_sub_const hf_L2.aestronglyMeasurable c
    have e3 : ProbabilityTheory.variance f P = (∫ x, (f x) ^ 2 ∂P) - c ^ 2 := by
      rw [ProbabilityTheory.variance_eq_sub hf_L2, ← hc]; simp [Pi.pow_apply]
    rw [e1, e2, e3]; linarith [sq_nonneg c]
  -- `n = 0`: the empirical process is `0`, so the `M`-event is empty.
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hset : {ξ : Ξ | M ≤ |empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) f|} = ∅ := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le,
        empiricalProcess_zero, abs_zero]
      exact hM
    rw [hset, measure_empty]; exact zero_le
  -- `n > 0`: `EP = (√n)⁻¹ · ∑ᵢ g(Xᵢ)`, mean `0`, variance `V`; apply Chebyshev.
  · have hsq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := hsqrt_pos.ne'
    have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    set Y : Ξ → ℝ := fun ξ => ∑ i : Fin n, g (X i.val ξ) with hYdef
    have hY_eq : Y = ∑ i : Fin n, (g ∘ X i.val) := by
      funext ξ; simp only [hYdef, Finset.sum_apply, Function.comp_apply]
    have hY_L2 : ∀ i : Fin n, MemLp (g ∘ X i.val) 2 μ := fun i => hgX_L2 i.val
    have hY_pairwise : Set.Pairwise (↑(Finset.univ : Finset (Fin n)) : Set (Fin n))
        (fun i j => ProbabilityTheory.IndepFun (g ∘ X i.val) (g ∘ X j.val) μ) := by
      intro i _ j _ hij
      exact hgX_indep.indepFun (fun h => hij (Fin.ext h))
    have hY_var : ProbabilityTheory.variance Y μ = (n : ℝ) * V := by
      rw [hY_eq, ProbabilityTheory.IndepFun.variance_sum (fun i _ => hY_L2 i) hY_pairwise,
        Finset.sum_congr rfl (fun i _ => hgXi_var i.val)]
      simp [Finset.sum_const, Finset.card_univ]
    have hY_memLp : MemLp Y 2 μ := by
      rw [hY_eq]; exact memLp_finset_sum' _ (fun i _ => hY_L2 i)
    have hEP_eq : (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
        = fun ξ => (Real.sqrt n)⁻¹ * Y ξ := by
      funext ξ
      have h_a : Real.sqrt (n : ℝ) * (n : ℝ)⁻¹ = (Real.sqrt (n : ℝ))⁻¹ := by
        nth_rewrite 2 [← hsq]
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hsqrt_ne, one_mul]
      have h_b : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
        nth_rewrite 2 [← hsq]
        rw [← mul_assoc, inv_mul_cancel₀ hsqrt_ne, one_mul]
      simp only [hYdef, hg]
      unfold empiricalProcess empiricalAvg
      rw [← hc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      linear_combination (∑ i : Fin n, f (X i.val ξ)) * h_a + c * h_b
    have hEP_memLp : MemLp
        (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) 2 μ := by
      rw [hEP_eq]; exact hY_memLp.const_mul _
    have hEP_mean : ∫ ξ, empiricalProcess P n (fun i : Fin n => X i.val ξ) f ∂μ = 0 := by
      rw [show (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
          = fun ξ => (Real.sqrt n)⁻¹ * Y ξ from hEP_eq, integral_const_mul]
      have hY_int : ∫ ξ, Y ξ ∂μ = 0 := by
        rw [hY_eq]
        simp_rw [Finset.sum_apply]
        rw [integral_finset_sum _ (fun i _ => (hY_L2 i).integrable one_le_two)]
        simp only [Function.comp_apply, hgX_mean, Finset.sum_const_zero]
      rw [hY_int, mul_zero]
    have hEP_var : ProbabilityTheory.variance
        (fun ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) μ = V := by
      rw [hEP_eq, ProbabilityTheory.variance_const_mul, hY_var, inv_pow]
      rw [show (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) from by rw [sq]; exact hsq]
      field_simp
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hEP_memLp hM
    simp only [hEP_var, hEP_mean, sub_zero] at hcheb
    refine hcheb.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr

/-- **Chebyshev tail for a fixed empirical-process difference.** For two
`L²(P)` functions, the iid empirical-process increment is bounded by the
squared intrinsic semidistance:
`P(|𝔾ₙf - 𝔾ₙg| ≥ M) ≤ distL2(P,f,g)² / M²`. -/
theorem empiricalProcess_sub_chebyshev_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (n : ℕ) (f g : Ω → ℝ) (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    {M : ℝ} (hM : 0 < M) :
    μ {ξ | M ≤ |empiricalProcess P n (fun i : Fin n => X i.val ξ) f -
        empiricalProcess P n (fun i : Fin n => X i.val ξ) g|}
      ≤ ENNReal.ofReal (distL2 P f g ^ 2 / M ^ 2) := by
  have hf_int := hf.integrable one_le_two
  have hg_int := hg.integrable one_le_two
  have htail := empiricalProcess_chebyshev_tail P μ X hX_meas hX_indep hX_id hX_law n
    (fun x => f x - g x) (hf.sub hg) hM
  simp_rw [empiricalProcess_sub P n _ f g hf_int hg_int] at htail
  refine htail.trans (ENNReal.ofReal_le_ofReal ?_)
  set I : ℝ := ∫ x, (f x - g x) ^ 2 ∂P with hI
  have hI_nonneg : 0 ≤ I := by rw [hI]; exact integral_nonneg fun _ => sq_nonneg _
  have hsqrt_le : Real.sqrt I ≤ distL2 P f g := by
    apply le_distL2_of_integral_sq_ge
    rw [Real.sq_sqrt hI_nonneg, hI]
  have hI_le : I ≤ distL2 P f g ^ 2 := by
    rw [← Real.sq_sqrt hI_nonneg]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_le 2
  rw [hI]
  exact div_le_div_of_nonneg_right hI_le (sq_nonneg M)

end AsymptoticStatistics.EmpiricalProcess
