module
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.MovingProductLikelihood

@[expose] public section

/-!
# LAN for moving local product experiments

The moving-sequence form of the one-dimensional log-likelihood consequence of
local asymptotic normality.  Both the parameter and the sample size may vary,
with the scaled displacement converging to a fixed local direction.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace AsymptoticStatistics
namespace AsymptoticRepresentation

variable {k : ℕ}
variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **Moving-path log-likelihood asymptotic normality.**

If `m` is strictly increasing and
`√(m n) • (θ n - θ₀) → h`, then under the base `m n`-fold product law the
moving log-likelihood ratio converges weakly to
`N(-Iθ₀(h,h)/2, Iθ₀(h,h))`.

The proof extends the scaled directions from the range of the strictly
monotone `m`, applies LAN clause (iii) along `m`, combines the score CLT along
`m` with Slutsky, and uses the moving-product likelihood comparison for the
product laws. No common-support or absolute-continuity assumption is required.
-/
theorem movingLogLikelihood_weaklyConverges
    -- the parametric family under study.
    (M : ParametricFamily 𝒳 (Θ k))
    -- a dominating measure for the supplied densities.
    (μ : Measure 𝒳)
    -- the base parameter.
    (θ₀ : Θ k)
    -- the DQM score at the base parameter.
    (ℓ : 𝒳 → Θ k)
    -- every family member is a probability density with respect to `μ`.
    (hPDF : IsPDFOf M μ)
    -- measurability of the supplied score.
    (hℓ : Measurable ℓ)
    -- differentiability in quadratic mean at `θ₀` with score `ℓ`.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- sample sizes along the moving local path.
    (m : ℕ → ℕ)
    -- strict monotonicity packages divergence and an injective range for extension.
    (hm : StrictMono m)
    -- the moving parameter sequence.
    (θ : ℕ → Θ k)
    -- the limiting local direction.
    (h : Θ k)
    -- convergence of the sample-size-scaled displacement.
    (hθ : Tendsto (fun n => Real.sqrt (m n) • (θ n - θ₀)) atTop (nhds h)) :
    let P : ∀ n, Measure (Fin (m n) → 𝒳) :=
      fun n => productMeasure M μ θ₀ (m n)
    let L : ∀ n, (Fin (m n) → 𝒳) → ℝ :=
      fun n => movingLogLikelihood M θ₀ m θ n
    let v : NNReal := (fisherInformation M μ θ₀ ℓ h h).toNNReal
    WeakConverges (fun n => (P n).map (L n))
      (gaussianReal (-(v : ℝ) / 2) v) := by
  classical
  dsimp only
  have h_one := hPDF.density_integral_eq_one θ₀
  have hint := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : Θ k, ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun _ _ => hPDF.density_integral_eq_one _
  have hint_perturb : ∀ t : ℝ, ∀ u : Θ k, Integrable (M.density (θ₀ + t • u)) μ :=
    fun _ _ => hPDF.density_integrable _
  let hFull : ℕ → Θ k := fun r =>
    if hr : ∃ n, m n = r then Real.sqrt r • (θ (Nat.find hr) - θ₀) else h
  have hFull_m (n : ℕ) : hFull (m n) = Real.sqrt (m n) • (θ n - θ₀) := by
    let hr : ∃ q, m q = m n := ⟨n, rfl⟩
    rw [show hFull (m n) = if _hr : ∃ q, m q = m n then
      Real.sqrt (m n) • (θ (Nat.find _hr) - θ₀) else h from rfl, dif_pos hr]
    rw [hm.injective (Nat.find_spec hr)]
  have hFull_tendsto : Tendsto hFull atTop (nhds h) := by
    rw [Filter.tendsto_atTop'] at hθ ⊢
    intro s hs
    obtain ⟨N, hN⟩ := hθ s hs
    refine ⟨m N, fun r hr => ?_⟩
    simp only [hFull]
    split_ifs with hre
    · have hNq : N ≤ Nat.find hre :=
        (hm.le_iff_le).mp ((Nat.find_spec hre).trans_ge hr)
      simpa [Nat.find_spec hre] using hN (Nat.find hre) hNq
    · exact mem_of_mem_nhds hs
  set ν : Measure 𝒳 := μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x) with hν
  haveI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (M.density_nonneg θ₀)), h_one, ENNReal.ofReal_one]
  let Pinf : Measure (ℕ → 𝒳) := Measure.infinitePi (fun _ : ℕ => ν)
  haveI : IsProbabilityMeasure Pinf := inferInstance
  let X : ℕ → (ℕ → 𝒳) → 𝒳 := fun i ω => ω i
  have hXmeas : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hXiid : iIndepFun X Pinf :=
    iIndepFun_infinitePi (X := fun (_ : ℕ) (x : 𝒳) => x) (fun _ => measurable_id)
  have hXlaw : ∀ i, Pinf.map (X i) = ν := fun i => Measure.infinitePi_map_eval _ i
  have hXident : ∀ i, IdentDistrib (X i) (X 0) Pinf Pinf := fun i =>
    ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, by rw [hXlaw i, hXlaw 0]⟩
  have hLAN := LANExpansion.LAN_expansion_iii Pinf M μ θ₀ ℓ hℓ h_one hint
    h_one_perturb hint_perturb hDQM h hFull hFull_tendsto X hXmeas
    (fun _ _ hij => hXiid.indepFun hij) hXident (hXlaw 0)
  let Y : ℕ → (ℕ → 𝒳) → ℝ := fun i ω => ⟪h, ℓ (ω i)⟫
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    (Measurable.const_inner (c := h) hℓ).comp (measurable_pi_apply i)
  have hYiid : iIndepFun Y Pinf := hXiid.comp
    (g := fun _ x => ⟪h, ℓ x⟫) (fun _ => Measurable.const_inner hℓ)
  have hYlaw : ∀ i, Pinf.map (Y i) = ν.map (fun x => ⟪h, ℓ x⟫) := by
    intro i
    rw [show Y i = (fun x => ⟪h, ℓ x⟫) ∘ X i from rfl,
      ← Measure.map_map (Measurable.const_inner hℓ) (hXmeas i), hXlaw i]
  have hYident : ∀ i, IdentDistrib (Y i) (Y 0) Pinf Pinf := fun i =>
    ⟨(hYmeas i).aemeasurable, (hYmeas 0).aemeasurable, by rw [hYlaw i, hYlaw 0]⟩
  have hFisher := dqm_fisher_integrable M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  have hgL2 : MemLp (fun x => ⟪h, ℓ x⟫) 2 ν := by
    rw [memLp_two_iff_integrable_sq
      (Measurable.const_inner (c := h) hℓ).aestronglyMeasurable, hν,
      integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal, M.density_nonneg] using hFisher
  have hYL2 : MemLp (Y 0) 2 Pinf := by
    have hg : MemLp (fun x => ⟪h, ℓ x⟫) 2 (Pinf.map (X 0)) := by
      rw [hXlaw 0]; exact hgL2
    exact hg.comp_of_map (hXmeas 0).aemeasurable
  have hmeanν : ∫ x, ⟪h, ℓ x⟫ ∂ν = 0 := by
    rw [hν, integral_withDensity_eq_integral_toReal_smul
      (M.density_meas θ₀).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hz := LANExpansion.score_mean_zero M μ θ₀ ℓ hℓ h_one hint
      h_one_perturb hint_perturb hDQM h
    simpa only [ENNReal.toReal_ofReal, M.density_nonneg, smul_eq_mul, mul_comm] using hz
  have hYmean : ∫ ω, Y 0 ω ∂Pinf = 0 := by
    have hmapi := integral_map (hXmeas 0).aemeasurable
      ((Measurable.const_inner (c := h) hℓ).aestronglyMeasurable :
        AEStronglyMeasurable (fun x => ⟪h, ℓ x⟫) (Pinf.map (X 0)))
    rw [hXlaw 0] at hmapi
    exact hmapi.symm.trans hmeanν
  have hvar : Var[Y 0; Pinf] = fisherInformation M μ θ₀ ℓ h h := by
    rw [variance_of_integral_eq_zero (hYmeas 0).aemeasurable hYmean]
    have hmapi := integral_map (hXmeas 0).aemeasurable
      (((Measurable.const_inner (c := h) hℓ).pow_const 2).aestronglyMeasurable :
        AEStronglyMeasurable (fun x => ⟪h, ℓ x⟫ ^ 2) (Pinf.map (X 0)))
    rw [hXlaw 0] at hmapi
    rw [hmapi.symm, hν, integral_withDensity_eq_integral_toReal_smul
      (M.density_meas θ₀).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal, M.density_nonneg, smul_eq_mul, fisherInformation]
    congr 1; funext x; ring
  have hTID := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (X := Y) (Y := id) (P := Pinf)
    (P' := gaussianReal 0 (fisherInformation M μ θ₀ ℓ h h).toNNReal)
    (by rw [hvar]; exact HasLaw.id) hYL2 hYiid hYident
  have hScore : WeakConverges
      (fun r => Pinf.map (fun ω => (Real.sqrt r)⁻¹ *
        ∑ i ∈ Finset.range r, ⟪h, ℓ (ω i)⟫))
      (gaussianReal 0 (fisherInformation M μ θ₀ ℓ h h).toNNReal) := by
    intro f
    have ht := hTID.tendsto
    replace ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht
    have hmap : ∀ n : ℕ, Pinf.map (fun ω => (Real.sqrt n)⁻¹ *
          (∑ i ∈ Finset.range n, Y i ω - (n : ℝ) * ∫ x, Y 0 x ∂Pinf)) =
        Pinf.map (fun ω => (Real.sqrt n)⁻¹ *
          ∑ i ∈ Finset.range n, ⟪h, ℓ (ω i)⟫) := by
      intro n
      congr 1
      funext ω
      simp only [hYmean, mul_zero, sub_zero, Y]
    simp_rw [← hmap]
    rw [← (Measure.map_id : (gaussianReal 0 (fisherInformation M μ θ₀ ℓ h h).toNNReal).map id = _)]
    exact ht f
  let S : ℕ → (ℕ → 𝒳) → ℝ := fun n ω => (Real.sqrt (m n))⁻¹ *
    ∑ i ∈ Finset.range (m n), ⟪h, ℓ (ω i)⟫
  let A : ℕ → (ℕ → 𝒳) → ℝ := fun n ω => S n ω -
    ((fisherInformation M μ θ₀ ℓ h h).toNNReal : ℝ) / 2
  let B : ℕ → (ℕ → 𝒳) → ℝ := fun n ω =>
    ∑ i ∈ Finset.range (m n),
      Real.log (M.density (θ n) (ω i) / M.density θ₀ (ω i))
  have hS : WeakConverges (fun n => Pinf.map (S n))
      (gaussianReal 0 (fisherInformation M μ θ₀ ℓ h h).toNNReal) := by
    simpa only [S] using hScore.comp hm
  have hSmeas : ∀ n, Measurable (S n) := fun n =>
    Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      (Measurable.const_inner (c := h) hℓ).comp (measurable_pi_apply i)) _
  have hAmeas : ∀ n, Measurable (A n) := fun n => (hSmeas n).sub_const _
  have hBmeas : ∀ n, Measurable (B n) := by
    intro n
    exact Finset.measurable_sum _ fun i _ => Measurable.log
      (((M.density_meas _).comp (measurable_pi_apply i)).div
        ((M.density_meas _).comp (measurable_pi_apply i)))
  have hA : WeakConverges (fun n => Pinf.map (A n))
      (gaussianReal (-((fisherInformation M μ θ₀ ℓ h h).toNNReal : ℝ) / 2)
        (fisherInformation M μ θ₀ ℓ h h).toNNReal) := by
    have hmap := hS.map
      (f := fun y : ℝ => y - ((fisherInformation M μ θ₀ ℓ h h).toNNReal : ℝ) / 2)
      (by fun_prop) (by fun_prop)
    have hcomp : (fun n => (Pinf.map (S n)).map
        (fun y : ℝ => y - ((fisherInformation M μ θ₀ ℓ h h).toNNReal : ℝ) / 2)) =
        (fun n => Pinf.map (A n)) := by
      funext n
      rw [Measure.map_map (by fun_prop) (hSmeas n)]
      rfl
    rw [hcomp, gaussianReal_map_sub_const, zero_sub, ← neg_div] at hmap
    exact hmap
  have hdist : ∀ ε > 0, Tendsto (fun n => Pinf.real
      {ω | ε ≤ dist (A n ω) (B n ω)}) atTop (nhds 0) := by
    rw [tendstoInMeasure_iff_norm] at hLAN
    intro ε hε
    have ht := (hLAN ε hε).comp hm.tendsto_atTop
    have heq : ∀ᶠ n : ℕ in atTop,
        Pinf {ω | ε ≤ ‖(∑ i ∈ Finset.range (m n),
            Real.log (M.density (θ₀ + (Real.sqrt (m n))⁻¹ • hFull (m n)) (X i ω) /
              M.density θ₀ (X i ω)) -
            (Real.sqrt (m n))⁻¹ * ∑ i ∈ Finset.range (m n), ⟪h, ℓ (X i ω)⟫ +
            (1 / 2 : ℝ) * fisherInformation M μ θ₀ ℓ h h) - 0‖} =
          Pinf {ω | ε ≤ dist (A n ω) (B n ω)} := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hmn : 0 < m n := lt_of_lt_of_le hn (hm.id_le n)
      have hsqrt : Real.sqrt (m n) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
      have hparam : θ₀ + (Real.sqrt (m n))⁻¹ • hFull (m n) = θ n := by
        rw [hFull_m]
        simp [smul_smul, hsqrt]
      apply congrArg Pinf
      ext ω
      simp only [Set.mem_setOf_eq, sub_zero, Real.dist_eq, Real.norm_eq_abs,
        A, B, S, X, hparam]
      have hnonneg : 0 ≤ fisherInformation M μ θ₀ ℓ h h := by
        apply integral_nonneg
        intro x
        exact mul_nonneg (mul_self_nonneg _) (M.density_nonneg _ _)
      rw [Real.coe_toNNReal _ hnonneg]
      rw [abs_sub_comm]
      ring_nf
    apply (ENNReal.tendsto_toReal_zero_iff fun n => measure_ne_top Pinf _).mpr
    simpa only [Measure.real_def] using ht.congr' heq
  have hB : WeakConverges (fun n => Pinf.map (B n))
      (gaussianReal (-((fisherInformation M μ θ₀ ℓ h h).toNNReal : ℝ) / 2)
        (fisherInformation M μ θ₀ ℓ h h).toNNReal) :=
    WeakConverges.slutsky_of_tendstoInMeasure_dist
      (fun n => (hAmeas n).aemeasurable) (fun n => (hBmeas n).aemeasurable) hA hdist
  have hlaw : ∀ n, (productMeasure M μ θ₀ (m n)).map
      (movingLogLikelihood M θ₀ m θ n) = Pinf.map (B n) := by
    intro n
    let R : (ℕ → 𝒳) → (Fin (m n) → 𝒳) := fun ω i => ω i.val
    have hR : Measurable R := measurable_pi_lambda _ fun i => measurable_pi_apply i.val
    have hprod : Pinf.map R = productMeasure M μ θ₀ (m n) := by
      change (Measure.infinitePi (fun _ : ℕ => ν)).map R = Measure.pi (fun _ : Fin (m n) => ν)
      exact (AsymptoticStatistics.pi_const_eq_infinitePi_map ν (m n)).symm
    rw [← hprod, Measure.map_map (movingLogLikelihood_measurable M θ₀ m θ n) hR]
    congr 1
    funext ω
    simp only [Function.comp_apply, movingLogLikelihood, B, R]
    exact Fin.sum_univ_eq_sum_range
      (fun i => Real.log (M.density (θ n) (ω i) / M.density θ₀ (ω i))) (m n)
  intro f
  simp_rw [hlaw]
  exact hB f

end AsymptoticRepresentation
end AsymptoticStatistics
