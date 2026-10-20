module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyChaining
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyLimitTheorems
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.DonskerProcessData

@[expose] public section

/-!
# Gaussian bridge and full outer weak convergence from uniform entropy

Gaussian results for van der Vaart Theorem 19.14. The
bridge, asymptotic equicontinuity, and full `LinfF` convergence are constructed
from the theorem's assumptions.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, Theorem 19.14,
book p.274.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ProbabilityTheory IsonormalProcess
open scoped ENNReal Topology

open UniformEntropyStructural

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem outerLpNorm_eq_eLpNorm_of_measurable (Q : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) :
    outerLpNorm Q f 2 = eLpNorm f 2 Q := by
  have hpow : Measurable (fun x => ENNReal.ofReal |f x| ^ (2 : ℝ)) := by fun_prop
  have h : outerLpNorm Q f 2 = eLpNorm f (ENNReal.ofReal (2 : ℝ)) Q := by
    rw [outerLpNorm, outerExpectation_eq_lintegral hpow,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top]
    simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2), one_div,
      Real.enorm_eq_ofReal_abs]
  convert h using 1
  all_goals norm_num

private theorem outerLpNorm_mono_abs (Q : Measure Ω) (f g : Ω → ℝ)
    (hfg : ∀ x, |f x| ≤ |g x|) : outerLpNorm Q f 2 ≤ outerLpNorm Q g 2 := by
  unfold outerLpNorm
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply outerExpectation_mono
  intro x
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hfg x)) (by norm_num)

/-- A relative uniform-entropy schedule yields an ordinary dyadic net for
`distL2 P`.  The zero-envelope-norm branch uses a singleton net; otherwise a
fixed scale shift absorbs the relative factor `‖G‖*_{P,2}`. -/
private theorem uniformEntropy_exists_dudleyNet
    (F : Set (Ω → ℝ)) (hFne : F.Nonempty) (G : Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG2 : outerLpNorm P G 2 < ⊤)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) :
    ∃ net : ℕ → Finset ↥F,
      (∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
        distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ))) ∧
      Monotone net ∧
      Summable (fun j : ℕ =>
        (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card))) := by
  classical
  let c := outerLpNorm P G 2
  by_cases hc : c = 0
  · obtain ⟨f₀, hf₀⟩ := hFne
    let net : ℕ → Finset ↥F := fun _ => {⟨f₀, hf₀⟩}
    refine ⟨net, ?_, fun _ _ _ => by simp [net], ?_⟩
    · intro j f
      refine ⟨⟨f₀, hf₀⟩, by simp [net], ?_⟩
      have hf0 : eLpNorm (f : Ω → ℝ) 2 P = 0 := by
        rw [← outerLpNorm_eq_eLpNorm_of_measurable P f (hFmeas f f.2)]
        apply le_antisymm
        · exact (outerLpNorm_mono_abs P f G (fun x =>
            (hEnv.2 f f.2 x).trans (le_abs_self _))).trans_eq hc
        · exact bot_le
      have hf₀0 : eLpNorm f₀ 2 P = 0 := by
        rw [← outerLpNorm_eq_eLpNorm_of_measurable P f₀ (hFmeas f₀ hf₀)]
        apply le_antisymm
        · exact (outerLpNorm_mono_abs P f₀ G (fun x =>
            (hEnv.2 f₀ hf₀ x).trans (le_abs_self _))).trans_eq hc
        · exact bot_le
      have haf : (f : Ω → ℝ) =ᵐ[P] 0 :=
        (eLpNorm_eq_zero_iff (hFmeas f f.2).aestronglyMeasurable (by norm_num)).mp hf0
      have haf₀ : f₀ =ᵐ[P] 0 :=
        (eLpNorm_eq_zero_iff (hFmeas f₀ hf₀).aestronglyMeasurable (by norm_num)).mp hf₀0
      rw [distL2, eLpNorm_eq_zero_of_ae_zero ((haf.sub haf₀).trans (by simp)),
        ENNReal.toReal_zero]
      positivity
    · have hs : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log 2)) :=
        summable_geometric_two.mul_right _
      apply hs.congr
      intro j
      simp only [net, Finset.card_singleton, Nat.cast_one, mul_one]
      congr 1
      rw [zpow_neg, zpow_natCast]
      simp
  · have hcpos : 0 < c := (bot_lt_iff_ne_bot.mpr hc)
    have hQ : IsAdmissibleMeasure G 2 P := ⟨inferInstance, hcpos, hG2⟩
    let S := uniformDudleySchedule_of_uniformEntropy hJ
    have hcRpos : 0 < c.toReal := ENNReal.toReal_pos hcpos.ne' hG2.ne
    obtain ⟨J, hJsmall⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hcRpos)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have hscale : c.toReal * (1 / 2 : ℝ) ^ J < 1 := by
      calc
        c.toReal * (1 / 2 : ℝ) ^ J = (1 / 2 : ℝ) ^ J * c.toReal := mul_comm _ _
        _ < c.toReal⁻¹ * c.toReal := mul_lt_mul_of_pos_right hJsmall hcRpos
        _ = 1 := inv_mul_cancel₀ hcRpos.ne'
    let net : ℕ → Finset ↥F := fun j => S.net P hQ (j + J)
    refine ⟨net, ?_, ?_, ?_⟩
    · intro j f
      obtain ⟨g, hg, hfg⟩ := S.covers P hQ (j + J) f
      refine ⟨g, hg, ?_⟩
      have hrhs : ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + J)) * c ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG2.ne
      have hreal := ENNReal.toReal_strict_mono hrhs hfg
      rw [show outerLpNorm P ((f : Ω → ℝ) - (g : Ω → ℝ)) 2 =
          eLpNorm ((f : Ω → ℝ) - (g : Ω → ℝ)) 2 P by
            simpa only [Pi.sub_apply] using
              outerLpNorm_eq_eLpNorm_of_measurable P _
                ((hFmeas f f.2).sub (hFmeas g g.2)),
        ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)] at hreal
      rw [distL2, zpow_neg, zpow_natCast]
      calc
        (eLpNorm ((f : Ω → ℝ) - (g : Ω → ℝ)) 2 P).toReal
            < (1 / 2 : ℝ) ^ (j + J) * c.toReal := hreal
        _ = (1 / 2 : ℝ) ^ j * ((1 / 2 : ℝ) ^ J * c.toReal) := by
          rw [pow_add]
          ring
        _ < (1 / 2 : ℝ) ^ j * 1 := by
          gcongr
          simpa [mul_comm] using hscale
        _ = (1 / 2 : ℝ) ^ j := mul_one _
        _ = (2 ^ j : ℝ)⁻¹ := by simp
    · change Monotone (fun j => S.net P hQ (j + J))
      exact monotone_nat_of_le_succ (fun j => by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          S.nested P hQ (j + J))
    · have hs := S.entropySummable P hQ
      have htail : Summable (fun j : ℕ =>
          (1 / 2 : ℝ) ^ (j + J) *
            Real.sqrt (Real.log (2 * (S.net P hQ (j + J)).card))) :=
        (_root_.summable_nat_add_iff J).2 hs
      have hscaled := htail.mul_left (((1 / 2 : ℝ) ^ J)⁻¹)
      apply hscaled.congr
      intro j
      simp only [net]
      rw [zpow_neg, zpow_natCast, pow_add]
      field_simp
      rw [mul_assoc, mul_comm (Real.sqrt _) _, ← mul_assoc, ← mul_pow]
      norm_num

private theorem totallyBounded_F_of_dudleyNet
    {F : Set (Ω → ℝ)} {P : Measure Ω} {H : Ω → ℝ}
    (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ))) :
    letI inst := distL2PseudoMetric hHenv hH2 hFmeas
    @TotallyBounded ↥F inst.toUniformSpace Set.univ := by
  letI inst := distL2PseudoMetric hHenv hH2 hFmeas
  rw [@Metric.totallyBounded_iff ↥F inst]
  intro ε hε
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨(net j : Set ↥F), (net j).finite_toSet, ?_⟩
  intro f _
  obtain ⟨g, hg, hfg⟩ := hnet j f
  refine Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, ?_⟩⟩
  rw [@Metric.mem_ball ↥F inst]
  change distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < ε
  exact hfg.trans (by simpa [zpow_neg, zpow_natCast] using hj)

private theorem separableSpace_gpH_of_dudleyNet
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ}
    (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ))) :
    TopologicalSpace.SeparableSpace
      ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas) := by
  classical
  let hFenv : ∃ H, EmpiricalProcess.IsEnvelope F H ∧ MemLp H 2 P :=
    ⟨H, hHenv, hH2⟩
  set R : Set (Lp ℝ 2 P) :=
    Set.range (fun f : ↥F => centredLp hFenv hFmeas f)
  letI inst := distL2PseudoMetric hHenv hH2 hFmeas
  have hFtb : @TotallyBounded ↥F inst.toUniformSpace Set.univ :=
    totallyBounded_F_of_dudleyNet hHenv hH2 hFmeas net hnet
  have hLip : @LipschitzWith ↥F (Lp ℝ 2 P) inst.toPseudoEMetricSpace _ 1
      (fun f : ↥F => centredLp hFenv hFmeas f) := by
    rw [@lipschitzWith_iff_dist_le_mul ↥F (Lp ℝ 2 P) inst _ _ _]
    intro s t
    rw [NNReal.coe_one, one_mul, dist_eq_norm]
    have hcoe : (centredLp hFenv hFmeas s - centredLp hFenv hFmeas t : Lp ℝ 2 P)
        = ((gpEmbed hFenv hFmeas s - gpEmbed hFenv hFmeas t :
            ↥(gpH hFenv hFmeas)) : Lp ℝ 2 P) := by
      rw [Submodule.coe_sub, coe_gpEmbed, coe_gpEmbed]
    rw [hcoe, ← Submodule.coe_norm]
    exact norm_gpEmbed_sub_le hFenv hFmeas s t
  have hRtb : TotallyBounded R := by
    have hi := @TotallyBounded.image ↥F (Lp ℝ 2 P) inst.toUniformSpace _ _ _
      hFtb hLip.uniformContinuous
    simpa only [Set.image_univ] using hi
  have hspan : TopologicalSpace.IsSeparable
      (↑(Submodule.span ℝ R) : Set (Lp ℝ 2 P)) := hRtb.isSeparable.span
  have hgpH : TopologicalSpace.IsSeparable
      (↑(gpH hFenv hFmeas) : Set (Lp ℝ 2 P)) := by
    have heq : (↑(gpH hFenv hFmeas) : Set (Lp ℝ 2 P)) =
        closure (↑(Submodule.span ℝ R) : Set (Lp ℝ 2 P)) := by
      rw [gpH, Submodule.topologicalClosure_coe]
    rw [heq]
    exact hspan.closure
  exact hgpH.separableSpace

private noncomputable def ueNetRep {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (f : ↥F) : ↥F := (hnet j f).choose

private theorem ueNetRep_mem {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (f : ↥F) : ueNetRep net hnet j f ∈ net j :=
  (hnet j f).choose_spec.1

private theorem ueNetRep_close {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (f : ↥F) :
    distL2 P (f : Ω → ℝ) (ueNetRep net hnet j f : Ω → ℝ) <
      (2 : ℝ) ^ (-(j : ℤ)) :=
  (hnet j f).choose_spec.2

private noncomputable def ueNetLin {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (x : ↥(net j) → ℝ) : LinfF F :=
  ⟨fun f => x ⟨ueNetRep net hnet j f, ueNetRep_mem net hnet j f⟩, by
    change Memℓp _ ∞
    rw [memℓp_infty_iff]
    refine (Set.Finite.bddAbove (Set.finite_range (fun g => ‖x g‖))).mono ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨ueNetRep net hnet j f, ueNetRep_mem net hnet j f⟩, rfl⟩⟩

private theorem ueNetLin_lipschitz {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) : LipschitzWith 1 (ueNetLin net hnet j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply lp.norm_le_of_forall_le dist_nonneg
  intro f
  rw [lp.coeFn_sub, Pi.sub_apply]
  change ‖x ⟨ueNetRep net hnet j f, _⟩ - y ⟨ueNetRep net hnet j f, _⟩‖ ≤ dist x y
  rw [← dist_eq_norm]
  exact dist_le_pi_dist x y _

private noncomputable def ueNetTuple
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F) (j : ℕ) (ω : ℕ → ℝ) : ↥(net j) → ℝ :=
  fun g => gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep (g : ↥F) ω

private noncomputable def ueNetApprox
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) (ω : ℕ → ℝ) : LinfF F :=
  ueNetLin net hnet j (ueNetTuple hHenv hH2 hFmeas hHinf hHsep net j ω)

private theorem ueNetApprox_stronglyMeasurable
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (j : ℕ) : StronglyMeasurable
      (ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet j) := by
  apply Continuous.comp_stronglyMeasurable (ueNetLin_lipschitz net hnet j).continuous
  apply Measurable.stronglyMeasurable
  rw [measurable_pi_iff]
  intro g
  exact gpX_measurable ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep (g : ↥F)

private def ueSkeleton {F : Set (Ω → ℝ)} (net : ℕ → Finset ↥F) : Set ↥F :=
  ⋃ j : ℕ, (↑(net j) : Set ↥F)

private theorem ueSkeleton_spec
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (hmono : Monotone net)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    letI inst := distL2PseudoMetric hHenv hH2 hFmeas
    (ueSkeleton net).Countable ∧ @Dense ↥F inst.toUniformSpace.toTopologicalSpace
      (ueSkeleton net) ∧
      (∀ᵐ ω ∂(iidStdGaussian : Measure (ℕ → ℝ)),
        BddAbove (Set.range (fun t : ueSkeleton net =>
          |gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep t ω|)) ∧
        @UniformContinuousOn ↥F ℝ inst.toUniformSpace _
          (fun t => gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep t ω)
          (ueSkeleton net)) := by
  letI inst := distL2PseudoMetric hHenv hH2 hFmeas
  exact _root_.GaussianChaining.gaussianChaining_UC_iUnion
    (μ := (iidStdGaussian : Measure (ℕ → ℝ))) (K := 1)
    zero_le_one (gpX_measurable ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep)
    net hnet hmono
    (fun s t => (gpX_subgaussian_increment ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep s t).mono_proxy
      (by
        refine NNReal.coe_le_coe.mp ?_
        change distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 * dist s t ^ 2
        rw [one_pow, one_mul]
        change distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2 ≤
          distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2
        exact le_rfl)) hDudley

private noncomputable def ueBridgePath
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (ω : ℕ → ℝ) : LinfF F := by
  letI : Nonempty (LinfF F) := ⟨0⟩
  exact limUnder atTop
    (fun j => ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet j ω)

private theorem ueNetApprox_cauchy_of_uc
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    {ω : ℕ → ℝ}
    (huc : letI inst := distL2PseudoMetric hHenv hH2 hFmeas
      @UniformContinuousOn ↥F ℝ inst.toUniformSpace _
        (fun t => gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep t ω)
        (ueSkeleton net)) :
    CauchySeq (fun j => ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet j ω) := by
  letI inst := distL2PseudoMetric hHenv hH2 hFmeas
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδuc⟩ := huc (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (half_pos hδ)
    (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  calc
    ‖ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet m ω -
        ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet n ω‖
        ≤ ε / 2 := by
          apply lp.norm_le_of_forall_le (le_of_lt (half_pos hε))
          intro f
          rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, ← Real.dist_eq]
          apply le_of_lt
          apply hδuc
          · exact Set.mem_iUnion.mpr ⟨m, ueNetRep_mem net hnet m f⟩
          · exact Set.mem_iUnion.mpr ⟨n, ueNetRep_mem net hnet n f⟩
          · change distL2 P (ueNetRep net hnet m f : Ω → ℝ)
                (ueNetRep net hnet n f : Ω → ℝ) < δ
            calc
              distL2 P (ueNetRep net hnet m f : Ω → ℝ)
                    (ueNetRep net hnet n f : Ω → ℝ)
                  ≤ distL2 P (ueNetRep net hnet m f : Ω → ℝ) (f : Ω → ℝ) +
                      distL2 P (f : Ω → ℝ) (ueNetRep net hnet n f : Ω → ℝ) :=
                distL2_triangle hHenv hH2 hFmeas
                  (ueNetRep net hnet m f).2 f.2 (ueNetRep net hnet n f).2
              _ < (1 / 2 : ℝ) ^ m + (1 / 2 : ℝ) ^ n :=
                add_lt_add (by simpa [distL2_comm, zpow_neg, zpow_natCast] using
                  ueNetRep_close net hnet m f)
                  (by simpa [zpow_neg, zpow_natCast] using ueNetRep_close net hnet n f)
              _ ≤ (1 / 2 : ℝ) ^ N + (1 / 2 : ℝ) ^ N := by
                exact add_le_add
                  (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm)
                  (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn)
              _ < δ := by linarith
    _ < ε := by linarith

private theorem ueBridgePath_tendsto_of_uc
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    {ω : ℕ → ℝ}
    (huc : letI inst := distL2PseudoMetric hHenv hH2 hFmeas
      @UniformContinuousOn ↥F ℝ inst.toUniformSpace _
        (fun t => gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep t ω)
        (ueSkeleton net)) :
    Tendsto (fun j => ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet j ω)
      atTop (𝓝 (ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω)) :=
  by
    letI : Nonempty (LinfF F) := ⟨0⟩
    simpa only [ueBridgePath] using
      (ueNetApprox_cauchy_of_uc hHenv hH2 hFmeas hHinf hHsep net hnet huc).tendsto_limUnder

private theorem ueBridgePath_aestronglyMeasurable
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (hmono : Monotone net)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    AEStronglyMeasurable
      (ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet)
      (iidStdGaussian : Measure (ℕ → ℝ)) := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun j =>
      (ueNetApprox_stronglyMeasurable hHenv hH2 hFmeas hHinf hHsep net
        hnet j).aestronglyMeasurable) ?_
  filter_upwards [(ueSkeleton_spec hHenv hH2 hFmeas hHinf hHsep net hnet hmono
    hDudley).2.2] with ω hω
  exact ueBridgePath_tendsto_of_uc hHenv hH2 hFmeas hHinf hHsep net hnet hω.2

private theorem ueBridgePath_aeeq_coord
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (hmono : Monotone net)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card))))
    (f : ↥F) :
    (fun ω => ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω f) =ᵐ[
      (iidStdGaussian : Measure (ℕ → ℝ))]
      gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep f := by
  have hscale : Tendsto (fun j : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ j)) atTop (𝓝 0) := by
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hpow
  have help : Tendsto (fun j => eLpNorm
      (fun ω => gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep (ueNetRep net hnet j f) ω -
        gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep f ω) 2
      (iidStdGaussian : Measure (ℕ → ℝ))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
      (Filter.Eventually.of_forall (fun _ => zero_le))
      (Filter.Eventually.of_forall (fun j => ?_))
    refine (eLpNorm_gpX_sub_le ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep
      (ueNetRep net hnet j f) f).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hc := ueNetRep_close (P := P) net hnet j f
    exact le_of_lt (by simpa [distL2_comm, zpow_neg, zpow_natCast] using hc)
  have htim : TendstoInMeasure (iidStdGaussian : Measure (ℕ → ℝ))
      (fun j => gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep (ueNetRep net hnet j f)) atTop
      (gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep f) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun j => (gpX_measurable ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep
        (ueNetRep net hnet j f)).aestronglyMeasurable)
      (gpX_measurable ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep f).aestronglyMeasurable help
  obtain ⟨ns, hns, hsub⟩ := htim.exists_seq_tendsto_ae
  filter_upwards [(ueSkeleton_spec hHenv hH2 hFmeas hHinf hHsep net hnet hmono
      hDudley).2.2, hsub] with ω hω hsubω
  have hpath := ueBridgePath_tendsto_of_uc hHenv hH2 hFmeas hHinf hHsep net hnet hω.2
  have heval : Tendsto (fun j =>
      ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet j ω f) atTop
      (𝓝 (ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω f)) :=
    ((continuous_linfF_eval f).tendsto
      (ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω)).comp hpath
  have hevalsub := heval.comp hns.tendsto_atTop
  exact tendsto_nhds_unique hevalsub hsubω

private theorem ueBridgePath_uc_ae
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (hmono : Monotone net)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    ∀ᵐ ω ∂(iidStdGaussian : Measure (ℕ → ℝ)), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ →
        |ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω f -
          ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω g| < ε := by
  letI inst := distL2PseudoMetric hHenv hH2 hFmeas
  filter_upwards [(ueSkeleton_spec hHenv hH2 hFmeas hHinf hHsep net hnet hmono
    hDudley).2.2] with ω hω
  intro ε hε
  have huc := hω.2
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηuc⟩ := huc (ε / 3) (by positivity)
  have hpath := ueBridgePath_tendsto_of_uc hHenv hH2 hFmeas hHinf hHsep net hnet hω.2
  have hevpath : ∀ᶠ j in atTop,
      dist (ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet j ω)
        (ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω) < ε / 3 :=
    hpath.eventually (Metric.ball_mem_nhds _ (by positivity))
  rw [eventually_atTop] at hevpath
  obtain ⟨N₁, hN₁⟩ := hevpath
  obtain ⟨N₂, hN₂⟩ := exists_pow_lt_of_lt_one (show 0 < η / 3 by positivity)
    (by norm_num : (1 / 2 : ℝ) < 1)
  let J := max N₁ N₂
  have hJpath := hN₁ J (le_max_left _ _)
  have hJscale : (1 / 2 : ℝ) ^ J < η / 3 :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right N₁ N₂)).trans_lt hN₂
  refine ⟨η / 3, by positivity, fun f g hfg => ?_⟩
  have hfJ : distL2 P (ueNetRep net hnet J f : Ω → ℝ) (f : Ω → ℝ) <
      (1 / 2 : ℝ) ^ J := by
    have hc := ueNetRep_close (P := P) net hnet J f
    simpa [distL2_comm, zpow_neg, zpow_natCast] using hc
  have hgJ : distL2 P (g : Ω → ℝ) (ueNetRep net hnet J g : Ω → ℝ) <
      (1 / 2 : ℝ) ^ J := by
    have hc := ueNetRep_close (P := P) net hnet J g
    simpa [zpow_neg, zpow_natCast] using hc
  have hreps : distL2 P (ueNetRep net hnet J f : Ω → ℝ)
      (ueNetRep net hnet J g : Ω → ℝ) < η := by
    calc
      distL2 P (ueNetRep net hnet J f : Ω → ℝ)
          (ueNetRep net hnet J g : Ω → ℝ)
          ≤ distL2 P (ueNetRep net hnet J f : Ω → ℝ) (f : Ω → ℝ) +
              distL2 P (f : Ω → ℝ) (ueNetRep net hnet J g : Ω → ℝ) :=
        distL2_triangle hHenv hH2 hFmeas (ueNetRep net hnet J f).2 f.2
          (ueNetRep net hnet J g).2
      _ ≤ distL2 P (ueNetRep net hnet J f : Ω → ℝ) (f : Ω → ℝ) +
            (distL2 P (f : Ω → ℝ) (g : Ω → ℝ) +
              distL2 P (g : Ω → ℝ) (ueNetRep net hnet J g : Ω → ℝ)) := by
        gcongr
        exact distL2_triangle hHenv hH2 hFmeas f.2 g.2 (ueNetRep net hnet J g).2
      _ < (1 / 2 : ℝ) ^ J + (η / 3 + (1 / 2 : ℝ) ^ J) := by
        exact add_lt_add hfJ (add_lt_add hfg hgJ)
      _ < η := by linarith [hJscale]
  have hmid : |ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω f -
      ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω g| < ε / 3 := by
    rw [← Real.dist_eq]
    exact hηuc _ (Set.mem_iUnion.mpr ⟨J, ueNetRep_mem net hnet J f⟩)
      _ (Set.mem_iUnion.mpr ⟨J, ueNetRep_mem net hnet J g⟩) hreps
  rw [dist_eq_norm] at hJpath
  have hleft : |ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω f -
      ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω f| < ε / 3 := by
    calc
      |_ - _| = ‖(ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω -
          ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω) f‖ := by
            rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω -
          ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω‖ :=
        lp.norm_apply_le_norm ENNReal.top_ne_zero _ f
      _ = ‖ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω -
          ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω‖ := norm_sub_rev _ _
      _ < ε / 3 := hJpath
  have hright : |ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω g -
      ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω g| < ε / 3 := by
    calc
      |_ - _| = ‖(ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω -
          ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω) g‖ := by
            rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
      _ ≤ ‖ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω -
          ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω‖ :=
        lp.norm_apply_le_norm ENNReal.top_ne_zero _ g
      _ < ε / 3 := hJpath
  let A := ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω f
  let B := ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω f
  let D := ueNetApprox hHenv hH2 hFmeas hHinf hHsep net hnet J ω g
  let E := ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet ω g
  change |A - E| < ε
  change |A - B| < ε / 3 at hleft
  change |B - D| < ε / 3 at hmid
  change |D - E| < ε / 3 at hright
  calc
    |A - E| = |(A - B) + (B - D) + (D - E)| := by congr 1; ring
    _ ≤ |(A - B) + (B - D)| + |D - E| := abs_add_le _ _
    _ ≤ |A - B| + |B - D| + |D - E| := by
      linarith [abs_add_le (A - B) (B - D)]
    _ < ε := by linarith

private theorem isTightMeasureSet_map_of_aestronglyMeasurable
    {Ξ E : Type*} [MeasurableSpace Ξ] [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (X : Ξ → E)
    (hX : AEStronglyMeasurable X μ) :
    IsTightMeasureSet ({μ.map X} : Set (Measure E)) := by
  let Y : Ξ → E := hX.mk X
  have hY : StronglyMeasurable Y := hX.stronglyMeasurable_mk
  let C : Set E := closure (Set.range Y)
  have hCsep : TopologicalSpace.IsSeparable C := hY.isSeparable_range.closure
  letI : SecondCountableTopology C := hCsep.secondCountableTopology
  letI : CompleteSpace C := isClosed_closure.completeSpace_coe
  let Ys : Ξ → C := fun ξ => ⟨Y ξ, subset_closure (Set.mem_range_self ξ)⟩
  have hYs : StronglyMeasurable Ys := hY.measurable.subtype_mk.stronglyMeasurable
  letI : IsProbabilityMeasure (μ.map Ys) :=
    Measure.isProbabilityMeasure_map hYs.aemeasurable
  have hsrc : IsTightMeasureSet ({μ.map Ys} : Set (Measure C)) :=
    isTightMeasureSet_singleton
  have himg := hsrc.map (continuous_subtype_val : Continuous (fun z : C => (z : E)))
  have hmap : (μ.map Ys).map (fun z : C => (z : E)) = μ.map Y := by
    rw [Measure.map_map continuous_subtype_val.measurable hYs.measurable]
    rfl
  have hXY : μ.map X = μ.map Y := Measure.map_congr hX.ae_eq_mk
  simpa only [Set.image_singleton, hmap, ← hXY] using himg

private theorem uniformEntropy_infinite_pBrownianBridge
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHinf : ¬ FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas))
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (hmono : Monotone net)
    (hDudley : Summable (fun j : ℕ =>
      (2 : ℝ) ^ (-(j : ℤ)) * Real.sqrt (Real.log (2 * (net j).card)))) :
    IsPBrownianBridge F P ((iidStdGaussian : Measure (ℕ → ℝ)).map
      (ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet)) := by
  let path := ueBridgePath hHenv hH2 hFmeas hHinf hHsep net hnet
  have hpath : AEStronglyMeasurable path (iidStdGaussian : Measure (ℕ → ℝ)) :=
    ueBridgePath_aestronglyMeasurable hHenv hH2 hFmeas hHinf hHsep net hnet hmono hDudley
  refine
    { isProbabilityMeasure := Measure.isProbabilityMeasure_map hpath.aemeasurable
      cov := ?_
      mean := ?_
      isGaussian_fdd := ?_
      tight := ?_
      ucPaths := ?_ }
  · intro f g
    have hint : AEStronglyMeasurable (fun z : LinfF F => z f * z g)
        ((iidStdGaussian : Measure (ℕ → ℝ)).map path) :=
      (((continuous_linfF_eval f).mul
        (continuous_linfF_eval g)).stronglyMeasurable).aestronglyMeasurable
    rw [integral_map hpath.aemeasurable hint]
    have hae : (fun ω => path ω f * path ω g) =ᵐ[
        (iidStdGaussian : Measure (ℕ → ℝ))]
        (fun ω => gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep f ω *
          gpX ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep g ω) := by
      filter_upwards [ueBridgePath_aeeq_coord hHenv hH2 hFmeas hHinf hHsep net hnet
        hmono hDudley f, ueBridgePath_aeeq_coord hHenv hH2 hFmeas hHinf hHsep net hnet
        hmono hDudley g] with ω hf hg
      rw [hf, hg]
    rw [integral_congr_ae hae]
    exact gpX_cov ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep f g
  · intro f
    have hint : AEStronglyMeasurable (fun z : LinfF F => z f)
        ((iidStdGaussian : Measure (ℕ → ℝ)).map path) :=
      (continuous_linfF_eval f).stronglyMeasurable.aestronglyMeasurable
    rw [integral_map hpath.aemeasurable hint]
    have hae : (fun ω => path ω f) =ᵐ[(iidStdGaussian : Measure (ℕ → ℝ))]
        (fun ω => isonormal (gpBasis ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep)
          (gpEmbed ⟨H, hHenv, hH2⟩ hFmeas f) ω) := by
      filter_upwards [ueBridgePath_aeeq_coord hHenv hH2 hFmeas hHinf hHsep net hnet
          hmono hDudley f,
        gpX_aeeq ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep f] with ω h1 h2
      rw [h1, h2]
    rw [integral_congr_ae hae]
    set W := isonormal (gpBasis ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep)
      (gpEmbed ⟨H, hHenv, hH2⟩ hFmeas f)
    have hmap : ∫ a, (W : (ℕ → ℝ) → ℝ) a ∂(iidStdGaussian : Measure (ℕ → ℝ)) =
        ∫ x : ℝ, x ∂((iidStdGaussian : Measure (ℕ → ℝ)).map (W : (ℕ → ℝ) → ℝ)) :=
      (integral_map (Lp.aestronglyMeasurable W).aemeasurable
        aestronglyMeasurable_id).symm
    rw [hmap, isonormal_map_eq_gaussianReal]
    exact integral_id_gaussianReal
  · intro m φ
    have hR : Measurable (fun z : LinfF F => (fun k => z (φ k))) :=
      measurable_pi_lambda _ (fun k => (continuous_linfF_eval (φ k)).measurable)
    have hae : (fun ω => (fun k => path ω (φ k))) =ᵐ[
        (iidStdGaussian : Measure (ℕ → ℝ))]
        (fun ω => (fun k => isonormal
          (gpBasis ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep)
          (gpEmbed ⟨H, hHenv, hH2⟩ hFmeas (φ k)) ω)) := by
      have hc : ∀ k : Fin m, (fun ω => path ω (φ k)) =ᵐ[
          (iidStdGaussian : Measure (ℕ → ℝ))]
          (fun ω => isonormal (gpBasis ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep)
            (gpEmbed ⟨H, hHenv, hH2⟩ hFmeas (φ k)) ω) := by
        intro k
        filter_upwards [ueBridgePath_aeeq_coord hHenv hH2 hFmeas hHinf hHsep net hnet
            hmono hDudley (φ k),
          gpX_aeeq ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep (φ k)] with ω h1 h2
        rw [h1, h2]
      filter_upwards [ae_all_iff.mpr hc] with ω hω
      funext k
      exact hω k
    have htuple : HasGaussianLaw (fun ω => (fun k => path ω (φ k)))
        (iidStdGaussian : Measure (ℕ → ℝ)) :=
      (isonormal_hasGaussianLaw_tuple
        (gpBasis ⟨H, hHenv, hH2⟩ hFmeas hHinf hHsep)
        (fun k => gpEmbed ⟨H, hHenv, hH2⟩ hFmeas (φ k))).congr hae.symm
    refine ⟨?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable hR.aemeasurable hpath.aemeasurable]
    exact htuple.isGaussian_map
  · exact isTightMeasureSet_map_of_aestronglyMeasurable
      (iidStdGaussian : Measure (ℕ → ℝ)) path hpath
  · rw [ae_map_iff hpath.aemeasurable pBridge_ucPaths_measurableSet]
    exact ueBridgePath_uc_ae hHenv hH2 hFmeas hHinf hHsep net hnet hmono hDudley

private noncomputable def ueFiniteProj {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (m : ℕ) (z : LinfF F) : LinfF F :=
  ueNetLin net hnet m (fun g => z (g : ↥F))

private theorem ueFiniteProj_apply {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (m : ℕ) (z : LinfF F) (f : ↥F) :
    ueFiniteProj net hnet m z f = z (ueNetRep net hnet m f) := rfl

private theorem ueFiniteProj_lipschitz {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (m : ℕ) : LipschitzWith 1 (ueFiniteProj net hnet m) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  apply lp.norm_le_of_forall_le dist_nonneg
  intro f
  rw [lp.coeFn_sub, Pi.sub_apply, ueFiniteProj_apply, ueFiniteProj_apply]
  simpa only [lp.coeFn_sub, Pi.sub_apply, dist_eq_norm] using
    (lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w)
      (ueNetRep net hnet m f))

private theorem ueFiniteProj_measurable {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (m : ℕ) : Measurable (ueFiniteProj net hnet m) :=
  (ueFiniteProj_lipschitz net hnet m).continuous.measurable

private theorem tendsto_ueFiniteProj_of_ucPath
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (z : LinfF F)
    (hz : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f g : ↥F,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| < ε) :
    Tendsto (fun m => ueFiniteProj net hnet m z) atTop (𝓝 z) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδuc⟩ := hz (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm]
  calc
    ‖ueFiniteProj net hnet m z - z‖ ≤ ε / 2 := by
      apply lp.norm_le_of_forall_le (le_of_lt (half_pos hε))
      intro f
      rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs, ueFiniteProj_apply]
      have hc : distL2 P (ueNetRep net hnet m f : Ω → ℝ) (f : Ω → ℝ) <
          (1 / 2 : ℝ) ^ m := by
        simpa [distL2_comm, zpow_neg, zpow_natCast] using ueNetRep_close net hnet m f
      exact le_of_lt (hδuc _ _ (hc.trans
        ((pow_le_pow_of_le_one (by norm_num) (by norm_num) hm).trans_lt hN)))
    _ < ε := by linarith

private theorem ueMarginalCovMatrix_posSemidef
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f) {k : ℕ} (φ : Fin k → ↥F) :
    (marginalCovMatrix P (fun i => (φ i : Ω → ℝ))).PosSemidef := by
  classical
  have hgram : marginalCovMatrix P (fun i => (φ i : Ω → ℝ)) =
      Matrix.gram ℝ (fun i => centredLp ⟨H, hHenv, hH2⟩ hFmeas (φ i)) := by
    ext i j
    rw [Matrix.gram_apply, inner_centredLp]
    rfl
  rw [hgram]
  exact Matrix.posSemidef_gram ℝ _

/-- Every finite coordinate readout of an arbitrary `P`-Brownian bridge is the
centred marginal Gaussian with the book covariance matrix. -/
private theorem pBrownianBridge_readout_eq_multivariateGaussian_ue
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (nu : Measure (LinfF F)) (hnu : IsPBrownianBridge F P nu)
    {k : ℕ} (φ : Fin k → ↥F) :
    nu.map (fun z : LinfF F => (WithLp.toLp 2 (fun i => z (φ i)) :
        EuclideanSpace ℝ (Fin k))) =
      multivariateGaussian 0 (marginalCovMatrix P (fun i => (φ i : Ω → ℝ))) := by
  classical
  let R : LinfF F → EuclideanSpace ℝ (Fin k) :=
    fun z => (WithLp.toLp 2 (fun i => z (φ i)) : EuclideanSpace ℝ (Fin k))
  let L : (Fin k → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin k) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin k => ℝ)).symm
  have hRgauss : HasGaussianLaw R nu := by
    have h := (hnu.isGaussian_fdd k φ).map_equiv L
    have hcomp : L ∘ (fun z : LinfF F => fun i => z (φ i)) = R := rfl
    rwa [hcomp] at h
  haveI : IsProbabilityMeasure nu := hnu.isProbabilityMeasure
  haveI : ProbabilityTheory.IsGaussian (nu.map R) := hRgauss.isGaussian_map
  have hRmem : MemLp R 2 nu := hRgauss.memLp_two
  have hRmeas : Measurable R := by
    exact ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi (fun i => continuous_linfF_eval (φ i)))).measurable
  change nu.map R = multivariateGaussian 0
    (marginalCovMatrix P (fun i => (φ i : Ω → ℝ)))
  refine ProbabilityTheory.IsGaussian.ext ?_ ?_
  · have hmeanR : ∫ z, R z ∂nu = 0 := by
      apply PiLp.ext
      intro i
      have hproj := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
        (hRmem.integrable (by norm_num))
      have hcoord : (fun z => (EuclideanSpace.proj (𝕜 := ℝ) i) (R z)) =
          fun z : LinfF F => z (φ i) := by
        funext z
        rfl
      rw [show (0 : EuclideanSpace ℝ (Fin k)).ofLp i = 0 from rfl]
      change (EuclideanSpace.proj (𝕜 := ℝ) i) (∫ z, R z ∂nu) = 0
      rw [← hproj]
      simpa only [hcoord] using hnu.mean (φ i)
    rw [integral_id_multivariateGaussian']
    rw [integral_map hRmeas.aemeasurable aestronglyMeasurable_id]
    simpa only [id_eq] using hmeanR
  · have hS : (marginalCovMatrix P
        (fun i => (φ i : Ω → ℝ))).PosSemidef :=
      ueMarginalCovMatrix_posSemidef hHenv hH2 hFmeas φ
    have hMemMap : MemLp id 2 (nu.map R) := IsGaussian.memLp_two_id
    have hbasis : ∀ i : Fin k,
        (fun u : EuclideanSpace ℝ (Fin k) =>
          (inner ℝ ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis i) u : ℝ)) =
          fun u => u.ofLp i := by
      intro i
      funext u
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply]
      have hpt : ∀ x : Fin k,
          (inner ℝ ((EuclideanSpace.single i (1 : ℝ)).ofLp x) (u.ofLp x) : ℝ) =
            u.ofLp x * (if x = i then (1 : ℝ) else 0) := by
        intro x
        rw [PiLp.single_apply]
        rfl
      simp_rw [hpt]
      simp [Finset.sum_ite_eq']
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      ProbabilityTheory.covarianceBilin_apply_eq_cov (μ := nu.map R) hMemMap,
      ProbabilityTheory.covarianceBilin_apply_eq_cov
        (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
          (marginalCovMatrix P (fun q => (φ q : Ω → ℝ)))) IsGaussian.memLp_two_id,
      hbasis i, hbasis j,
      ProbabilityTheory.covariance_eval_multivariateGaussian hS]
    have hcoord_meas : ∀ q : Fin k,
        AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin k) => u.ofLp q)
          (nu.map R) :=
      fun q => (EuclideanSpace.proj (𝕜 := ℝ) q).continuous.measurable.aestronglyMeasurable
    rw [ProbabilityTheory.covariance_map (hcoord_meas i) (hcoord_meas j)
      hRmeas.aemeasurable]
    have hcoord : ∀ q : Fin k,
        ((fun u : EuclideanSpace ℝ (Fin k) => u.ofLp q) ∘ R) =
          fun z : LinfF F => z (φ q) := by
      intro q
      funext z
      rfl
    have hcoord_mem : ∀ q : Fin k, MemLp (fun z : LinfF F => z (φ q)) 2 nu := by
      intro q
      rw [← hcoord q]
      exact (EuclideanSpace.proj (𝕜 := ℝ) q).lipschitz.comp_memLp
        (map_zero _) hRmem
    rw [hcoord i, hcoord j]
    rw [ProbabilityTheory.covariance_eq_sub (hcoord_mem i) (hcoord_mem j),
      hnu.mean (φ i), hnu.mean (φ j)]
    simp only [Pi.mul_apply, mul_zero, sub_zero]
    rw [hnu.cov (φ i) (φ j)]
    rfl

private noncomputable def ueNetEnum {F : Set (Ω → ℝ)}
    (net : ℕ → Finset ↥F) (m : ℕ) :
    ↥(net m) ≃ Fin (Fintype.card ↥(net m)) :=
  Fintype.equivFin _

private noncomputable def ueNetPhi {F : Set (Ω → ℝ)}
    (net : ℕ → Finset ↥F) (m : ℕ) : Fin (Fintype.card ↥(net m)) → ↥F :=
  fun i => ((ueNetEnum net m).symm i : ↥F)

private noncomputable def ueStdRecon {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (m : ℕ) (y : EuclideanSpace ℝ (Fin (Fintype.card ↥(net m)))) : LinfF F :=
  ueNetLin net hnet m (fun g => y ((ueNetEnum net m) g))

private theorem continuous_ueStdRecon {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (m : ℕ) : Continuous (ueStdRecon net hnet m) := by
  apply (ueNetLin_lipschitz net hnet m).continuous.comp
  exact continuous_pi (fun g => (EuclideanSpace.proj (𝕜 := ℝ)
    ((ueNetEnum net m) g)).continuous)

private theorem ueStdRecon_readout {F : Set (Ω → ℝ)} {P : Measure Ω}
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (m : ℕ) (z : LinfF F) :
    ueStdRecon net hnet m
        (WithLp.toLp 2 (fun i => z (ueNetPhi net m i)) :
          EuclideanSpace ℝ (Fin (Fintype.card ↥(net m)))) =
      ueFiniteProj net hnet m z := by
  apply lp.ext
  funext f
  change z ((ueNetEnum net m).symm
      ((ueNetEnum net m) ⟨ueNetRep net hnet m f, ueNetRep_mem net hnet m f⟩) : ↥F) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Algebraic identity between empirical-process coordinates and the
standardised-sum vector used by `IsMarginalCLT.fdd`. -/
private theorem ueReadout_empirical_eq_std
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f) (hclt : IsMarginalCLT F P)
    {k : ℕ} (φ : Fin k → ↥F)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXlaw : μ.map (X 0) = P) (n : ℕ) (ξ : Ξ) :
    (WithLp.toLp 2 (fun i =>
        (empiricalProcessLinf (fun j : Fin n => X j.val ξ)
          (memℓp_empiricalProcess
            ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun j : Fin n => X j.val ξ))) (φ i)) :
      EuclideanSpace ℝ (Fin k)) =
      (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n,
        tupleVec (fun q => (φ q : Ω → ℝ)) (X i ξ) -
        n • ∫ ζ, tupleVec (fun q => (φ q : Ω → ℝ)) (X 0 ζ) ∂μ) := by
  classical
  let φ' : Fin k → Ω → ℝ := fun i => (φ i : Ω → ℝ)
  have hφmem : ∀ i, φ' i ∈ F := fun i => (φ i).2
  have hφmeas : ∀ i, Measurable (φ' i) := fun i => hFmeas _ (hφmem i)
  have htvmeas : Measurable (tupleVec φ') := by
    have hpi : Measurable (fun ω => (fun i => φ' i ω) : Ω → (Fin k → ℝ)) :=
      measurable_pi_iff.mpr hφmeas
    exact (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.measurable.comp hpi
  have htvintP : Integrable (tupleVec φ') P := by
    have hLp : MemLp (tupleVec φ') 2 P := by
      refine memLp_piLp_iff.mpr (fun i => ?_)
      exact hclt.1 _ (hφmem i)
    exact hLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htvint : Integrable (fun ζ => tupleVec φ' (X 0 ζ)) μ := by
    have hc : Integrable (tupleVec φ' ∘ X 0) μ :=
      (integrable_map_measure htvmeas.aestronglyMeasurable
        (hXmeas 0).aemeasurable).mp (by rw [hXlaw]; exact htvintP)
    exact hc
  apply PiLp.ext
  intro i
  have hproj : ∀ ω, (EuclideanSpace.proj i) (tupleVec φ' ω) = φ' i ω := by
    intro ω
    rw [EuclideanSpace.coe_proj]
    rfl
  have hinti : (EuclideanSpace.proj i)
      (∫ ζ, tupleVec φ' (X 0 ζ) ∂μ) = ∫ ζ, φ' i (X 0 ζ) ∂μ := by
    rw [← ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i) htvint]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ζ => hproj (X 0 ζ)))
  have hrhs : (((Real.sqrt n)⁻¹ • (∑ j ∈ Finset.range n,
        tupleVec φ' (X j ξ) - n • ∫ ζ, tupleVec φ' (X 0 ζ) ∂μ)) :
      EuclideanSpace ℝ (Fin k)) i =
      (Real.sqrt n)⁻¹ * ((∑ j ∈ Finset.range n, φ' i (X j ξ)) -
        n * ∫ ζ, φ' i (X 0 ζ) ∂μ) := by
    have hkey : (EuclideanSpace.proj i)
        ((Real.sqrt n)⁻¹ • (∑ j ∈ Finset.range n,
          tupleVec φ' (X j ξ) - n • ∫ ζ, tupleVec φ' (X 0 ζ) ∂μ)) =
        (Real.sqrt n)⁻¹ * ((∑ j ∈ Finset.range n, φ' i (X j ξ)) -
          n * ∫ ζ, φ' i (X 0 ζ) ∂μ) := by
      rw [map_smul, map_sub, map_sum, map_nsmul, hinti]
      simp only [hproj, smul_eq_mul, nsmul_eq_mul]
    rw [← hkey, EuclideanSpace.coe_proj]
  rw [hrhs]
  change empiricalProcess P n (fun j : Fin n => X j.val ξ) (φ' i) = _
  have hintlaw : ∫ ζ, φ' i (X 0 ζ) ∂μ = ∫ x, φ' i x ∂P := by
    rw [← hXlaw, integral_map (hXmeas 0).aemeasurable
      (hφmeas i).aestronglyMeasurable]
  rw [hintlaw]
  have hsum : ∑ j ∈ Finset.range n, φ' i (X j ξ) =
      ∑ j : Fin n, φ' i (X j.val ξ) := by
    rw [Finset.sum_range fun j => φ' i (X j ξ)]
  rw [empiricalProcess, empiricalAvg, hsum]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hsqrtne : Real.sqrt n ≠ 0 := hsqrtpos.ne'
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have h1 : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      field_simp
      linear_combination hsq
    have h2 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
      rw [inv_mul_eq_div, eq_comm, eq_div_iff hsqrtne, hsq]
    set A := ∑ j : Fin n, φ' i (X j.val ξ)
    set B := ∫ x, φ' i x ∂P
    linear_combination A * h1 + B * h2

/-- Marginal CLT transported through one finite uniform-net projection. -/
private theorem weakConvergesOuter_ueFiniteProj
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (nu : Measure (LinfF F)) (hnu : IsPBrownianBridge F P nu)
    (hclt : IsMarginalCLT F P) (m : ℕ)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => ueFiniteProj net hnet m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ))))
      (nu.map (ueFiniteProj net hnet m)) := by
  classical
  let φ : Fin (Fintype.card ↥(net m)) → ↥F := ueNetPhi net m
  let φ' : Fin (Fintype.card ↥(net m)) → Ω → ℝ := fun i => (φ i : Ω → ℝ)
  let stdVec : ℕ → Ξ → EuclideanSpace ℝ (Fin (Fintype.card ↥(net m))) :=
    fun n ξ => (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec φ' (X i ξ) -
      n • ∫ ζ, tupleVec φ' (X 0 ζ) ∂μ)
  have hφmem : ∀ i, φ' i ∈ F := fun i => (φ i).2
  obtain ⟨Y, hY, htid⟩ :=
    hclt.2 μ X hXmeas hXindep hXid hXlaw φ' hφmem
  have hweak : WeakConverges (fun n => μ.map (stdVec n))
      (multivariateGaussian 0 (marginalCovMatrix P φ')) := by
    have hlim :
        (⟨(multivariateGaussian 0 (marginalCovMatrix P φ')).map Y,
          Measure.isProbabilityMeasure_map htid.aemeasurable_limit⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin (Fintype.card ↥(net m))))) =
        ⟨multivariateGaussian 0 (marginalCovMatrix P φ'), inferInstance⟩ :=
      Subtype.ext hY.map_eq
    intro g
    exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hlim ▸ htid.tendsto)) g
  have hstdmeas : ∀ n, Measurable (stdVec n) := by
    intro n
    have htv : Measurable (tupleVec φ') := by
      have hpi : Measurable (fun ω => (fun i => φ' i ω) :
          Ω → (Fin (Fintype.card ↥(net m)) → ℝ)) :=
        measurable_pi_iff.mpr (fun i => hFmeas _ (hφmem i))
      exact (EuclideanSpace.equiv _ ℝ).symm.continuous.measurable.comp hpi
    exact Measurable.const_smul
      ((Finset.measurable_sum _ (fun i _ => htv.comp (hXmeas i))).sub measurable_const)
      ((Real.sqrt (n : ℝ))⁻¹)
  have hpoint : ∀ n ξ, ueStdRecon net hnet m (stdVec n ξ) =
      ueFiniteProj net hnet m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ))) := by
    intro n ξ
    rw [← ueStdRecon_readout net hnet m]
    congr 1
    exact (ueReadout_empirical_eq_std hHenv hH2 hFmeas hclt φ μ X hXmeas
      hXlaw n ξ).symm
  have hseq : ∀ n,
      (μ.map (stdVec n)).map (ueStdRecon net hnet m) =
        μ.map (fun ξ => ueFiniteProj net hnet m
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ)))) := by
    intro n
    rw [Measure.map_map (continuous_ueStdRecon net hnet m).measurable (hstdmeas n)]
    exact Measure.map_congr (Filter.Eventually.of_forall (hpoint n))
  have hlimit :
      (multivariateGaussian 0 (marginalCovMatrix P φ')).map
          (ueStdRecon net hnet m) = nu.map (ueFiniteProj net hnet m) := by
    have hgauss := pBrownianBridge_readout_eq_multivariateGaussian_ue
      hHenv hH2 hFmeas nu hnu φ
    change nu.map (fun z : LinfF F =>
      (WithLp.toLp 2 (fun i => z (φ i)) :
        EuclideanSpace ℝ (Fin (Fintype.card ↥(net m))))) =
      multivariateGaussian 0 (marginalCovMatrix P φ') at hgauss
    rw [← hgauss]
    have hread : Measurable (fun z : LinfF F =>
        (WithLp.toLp 2 (fun i => z (φ i)) :
          EuclideanSpace ℝ (Fin (Fintype.card ↥(net m))))) :=
      ((PiLp.continuous_toLp 2 _).comp
        (continuous_pi (fun i => continuous_linfF_eval (φ i)))).measurable
    rw [Measure.map_map (continuous_ueStdRecon net hnet m).measurable hread]
    exact Measure.map_congr (Filter.Eventually.of_forall
      (fun z => ueStdRecon_readout net hnet m z))
  have hprojweak : WeakConverges
      (fun n => μ.map (fun ξ => ueFiniteProj net hnet m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))))
      (nu.map (ueFiniteProj net hnet m)) := by
    have hmap := hweak.map (continuous_ueStdRecon net hnet m)
      (continuous_ueStdRecon net hnet m).measurable
    rw [funext hseq, hlimit] at hmap
    exact hmap
  rw [weakConvergesOuter_of_measurable (fun n => by
    have heq : (fun ξ => ueFiniteProj net hnet m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))) = ueStdRecon net hnet m ∘ stdVec n := by
      funext ξ
      exact (hpoint n ξ).symm
    rw [heq]
    exact (continuous_ueStdRecon net hnet m).measurable.comp (hstdmeas n))]
  exact hprojweak

/-- Equicontinuity makes the empirical process uniformly close to its dyadic
uniform-net projection, in outer probability and uniformly in the sample-size
limsup. -/
private theorem ueEmpirical_proj_error_outer
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (heq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun m => limsup (fun n => μ.outerMeasureStar
      {ξ | ε < ‖empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)) -
        ueFiniteProj net hnet m
          (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ)))‖}) atTop) atTop (nhds 0) := by
  let 𝔾 : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ))
  change Tendsto (fun m => limsup (fun n => μ.outerMeasureStar
    {ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}) atTop) atTop (nhds 0)
  rw [ENNReal.tendsto_nhds_zero]
  intro η₀ hη₀
  obtain ⟨a, ha0, haη⟩ := exists_between hη₀
  have hane : a ≠ ⊤ := (lt_of_lt_of_le haη le_top).ne
  let η : ℝ := a.toReal
  have hηpos : 0 < η := ENNReal.toReal_pos ha0.ne' hane
  have hofReal : ENNReal.ofReal η = a := ENNReal.ofReal_toReal hane
  obtain ⟨δ, hδpos, hδ⟩ :=
    heq μ X hXmeas hXindep hXid hXlaw ε η hε hηpos
  obtain ⟨N, hN0⟩ := exists_pow_lt_of_lt_one hδpos
    (by norm_num : (2⁻¹ : ℝ) < 1)
  have hN : ∀ m ≥ N, (2 : ℝ) ^ (-(m : ℤ)) < δ := by
    intro m hm
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm) hN0
  refine Filter.eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  have hsubset : ∀ n,
      {ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖} ⊆
        {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
          ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ) -
            empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    have hne : Nonempty ↥F := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      rw [lp.eq_zero' (𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)), norm_zero] at hξ
      exact absurd hξ (not_lt.2 hε.le)
    obtain ⟨c, ⟨t, rfl⟩, hct⟩ :=
      (lt_isLUB_iff (lp.isLUB_norm
        (𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)))).1 hξ
    have hcoord : (𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)) t =
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ)
            (ueNetRep net hnet m t : Ω → ℝ) := by
      rw [lp.coeFn_sub, Pi.sub_apply, ueFiniteProj_apply]
      rfl
    refine ⟨t, ueNetRep net hnet m t,
      lt_trans (ueNetRep_close net hnet m t) (hN m hm), ?_⟩
    rw [← Real.norm_eq_abs, ← hcoord]
    exact hct
  calc
    limsup (fun n => μ.outerMeasureStar
        {ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}) atTop
        ≤ limsup (fun n => μ.outerMeasureStar
          {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
            ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ) -
              empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}) atTop :=
      limsup_le_limsup (Filter.Eventually.of_forall fun n =>
        outerMeasureStar_mono μ (hsubset n))
    _ ≤ ENNReal.ofReal η := hδ
    _ = a := hofReal
    _ ≤ η₀ := haη.le

private theorem ueLimit_proj_error
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (nu : Measure (LinfF F)) (hnu : IsPBrownianBridge F P nu)
    (f : BoundedContinuousFunction (LinfF F) ℝ) :
    Tendsto (fun m => ∫ z, |f (ueFiniteProj net hnet m z) - f z| ∂nu)
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure nu := hnu.isProbabilityMeasure
  let Φ : ℕ → LinfF F → ℝ :=
    fun m z => |f (ueFiniteProj net hnet m z) - f z|
  have hzero : (0 : ℝ) = ∫ _ : LinfF F, (0 : ℝ) ∂nu := by simp
  rw [hzero]
  apply tendsto_integral_of_dominated_convergence (fun _ => 2 * ‖f‖)
  · intro m
    have h1 : Measurable (fun z : LinfF F => f (ueFiniteProj net hnet m z)) :=
      f.continuous.measurable.comp (ueFiniteProj_measurable net hnet m)
    exact ((h1.sub f.continuous.measurable).abs).aestronglyMeasurable
  · exact integrable_const _
  · intro m
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    calc
      |f (ueFiniteProj net hnet m z) - f z| ≤
          |f (ueFiniteProj net hnet m z)| + |f z| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := by
        apply add_le_add <;> rw [← Real.norm_eq_abs] <;> exact f.norm_coe_le_norm _
      _ = 2 * ‖f‖ := by ring
  · filter_upwards [hnu.ucPaths] with z hz
    have ht : Tendsto (fun m => ueFiniteProj net hnet m z) atTop (nhds z) :=
      tendsto_ueFiniteProj_of_ucPath net hnet z hz
    have hf : Tendsto (fun m => f (ueFiniteProj net hnet m z)) atTop (nhds (f z)) :=
      (f.continuous.tendsto z).comp ht
    have hsub : Tendsto (fun m => f (ueFiniteProj net hnet m z) - f z)
        atTop (nhds (0 : ℝ)) := by
      simpa using hf.sub (tendsto_const_nhds (x := f z))
    simpa [Φ] using! (continuous_abs.tendsto (0 : ℝ)).comp hsub

private theorem ueEmpirical_readout_tail_outer
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (heq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P)
    (f : BoundedContinuousFunction (LinfF F) ℝ)
    (hflip : ∃ K, LipschitzWith K f) :
    Tendsto (fun m => limsup (fun n =>
      (outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ))) -
          f (ueFiniteProj net hnet m
            (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
              (memℓp_empiricalProcess
                ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ))))|)).toReal) atTop) atTop (nhds 0) := by
  letI : Nonempty (LinfF F) := ⟨0⟩
  obtain ⟨K, hK⟩ := hflip
  let 𝔾 : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ))
  let D : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal
      |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|)).toReal
  change Tendsto (fun m => limsup (fun n => D m n) atTop) atTop (nhds 0)
  refine NormedAddGroup.tendsto_nhds_zero.2 (fun ε' hε' => ?_)
  let Kr : ℝ := (K : ℝ)
  have hKr : 0 ≤ Kr := by positivity
  obtain ⟨ε, hε, hKε⟩ : ∃ ε : ℝ, 0 < ε ∧ Kr * ε < ε' / 2 := by
    refine ⟨(ε' / 2) / (Kr + 1), by positivity, ?_⟩
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    have hle : Kr * (ε' / 2) ≤ (Kr + 1) * (ε' / 2) := by nlinarith
    nlinarith [hε']
  have hS3 := ueEmpirical_proj_error_outer hHenv hH2 net hnet heq μ X hXmeas
    hXindep hXid hXlaw ε hε
  let S : ℕ → ℕ → ℝ≥0∞ := fun m n => μ.outerMeasureStar
    {ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}
  have hS3' : Tendsto (fun m => limsup (fun n => S m n) atTop)
      atTop (nhds 0) := by
    exact hS3
  have hSle : ∀ m n, S m n ≤ 1 := by
    intro m n
    unfold S Measure.outerMeasureStar
    calc
      outerExpectation μ (Set.indicator _ 1) ≤
          outerExpectation μ (fun _ => (1 : ℝ≥0∞)) := by
        refine outerExpectation_mono (fun ξ => ?_)
        rw [Set.indicator_apply]
        split_ifs <;> simp
      _ = 1 := by rw [outerExpectation_const, measure_univ, mul_one]
  have hDbound : ∀ m n,
      D m n ≤ Kr * ε + 2 * ‖f‖ * (S m n).toReal := by
    intro m n
    have hpt : ∀ ξ, ENNReal.ofReal
        |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))| ≤
        ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) *
          ({ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}.indicator
            (1 : Ξ → ℝ≥0∞) ξ) := by
      intro ξ
      let a := 𝔾 n ξ
      let b := ueFiniteProj net hnet m (𝔾 n ξ)
      have hlip : |f a - f b| ≤ Kr * ‖a - b‖ := by
        have hh := hK.dist_le_mul a b
        rwa [Real.dist_eq, dist_eq_norm] at hh
      have hbdd : |f a - f b| ≤ 2 * ‖f‖ := by
        have ha := abs_le.1 (f.norm_coe_le_norm a)
        have hb := abs_le.1 (f.norm_coe_le_norm b)
        rw [abs_le]
        constructor <;> [linarith [ha.1, hb.2]; linarith [ha.2, hb.1]]
      by_cases hbad : ε < ‖a - b‖
      · have hmem : ξ ∈
            {ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖} := hbad
        rw [Set.indicator_of_mem hmem]
        calc
          ENNReal.ofReal |f a - f b| ≤ ENNReal.ofReal (2 * ‖f‖) :=
            ENNReal.ofReal_le_ofReal hbdd
          _ ≤ ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * 1 := by
            rw [mul_one]
            exact le_add_self
      · rw [not_lt] at hbad
        have hgood : |f a - f b| ≤ Kr * ε :=
          hlip.trans (mul_le_mul_of_nonneg_left hbad hKr)
        calc
          ENNReal.ofReal |f a - f b| ≤ ENNReal.ofReal (Kr * ε) :=
            ENNReal.ofReal_le_ofReal hgood
          _ ≤ ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) *
              ({ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}.indicator
                (1 : Ξ → ℝ≥0∞) ξ) := le_self_add
    have hE : outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|) ≤
        ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * S m n := by
      calc
        outerExpectation μ (fun ξ => ENNReal.ofReal
            |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|) ≤
          outerExpectation μ (fun ξ => ENNReal.ofReal (Kr * ε) +
            ENNReal.ofReal (2 * ‖f‖) *
              ({ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}.indicator
                (1 : Ξ → ℝ≥0∞) ξ)) := outerExpectation_mono hpt
        _ ≤ outerExpectation μ (fun _ => ENNReal.ofReal (Kr * ε)) +
            outerExpectation μ (fun ξ => ENNReal.ofReal (2 * ‖f‖) *
              ({ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}.indicator
                (1 : Ξ → ℝ≥0∞) ξ)) := outerExpectation_add_le _ _
        _ = ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * S m n := by
          rw [outerExpectation_const, measure_univ, mul_one]
          congr 1
          have hc := outerExpectation_const_smul (μ := μ)
            (ENNReal.ofReal (2 * ‖f‖)) ENNReal.ofReal_ne_top
            ({ξ | ε < ‖𝔾 n ξ - ueFiniteProj net hnet m (𝔾 n ξ)‖}.indicator
              (1 : Ξ → ℝ≥0∞))
          simpa only [Pi.smul_apply, smul_eq_mul, S, Measure.outerMeasureStar] using! hc
    change (outerExpectation μ (fun ξ => ENNReal.ofReal
      |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|)).toReal ≤ _
    have hfin : ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * S m n ≠ ⊤ := by
      apply ENNReal.add_ne_top.2
      refine ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
      exact ne_top_of_le_ne_top (by norm_num) (hSle m n)
    calc
      (outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|)).toReal ≤
          (ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * S m n).toReal :=
        ENNReal.toReal_mono hfin hE
      _ = Kr * ε + 2 * ‖f‖ * (S m n).toReal := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ne_top_of_le_ne_top (by norm_num) (hSle m n))),
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
          ENNReal.toReal_ofReal (by positivity)]
  have hDnonneg : ∀ m n, 0 ≤ D m n := fun m n => by
    change 0 ≤ (outerExpectation μ (fun ξ => ENNReal.ofReal
      |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|)).toReal
    exact ENNReal.toReal_nonneg
  let ψ : ℝ → ℝ := fun x => Kr * ε + 2 * ‖f‖ * x
  have hψmono : Monotone ψ := by
    intro x y hxy
    dsimp [ψ]
    gcongr
  have hψcont : Continuous ψ := by
    dsimp [ψ]
    fun_prop
  have hStoReal : ∀ m n, (S m n).toReal ≤ 1 := fun m n =>
    ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by rw [ENNReal.ofReal_one]; exact hSle m n)
  have hSbdd : ∀ m, IsBoundedUnder (· ≤ ·) atTop (fun n => (S m n).toReal) :=
    fun m => ⟨1, by rw [eventually_map]; exact Eventually.of_forall (hStoReal m)⟩
  have hScobdd : ∀ m, IsCoboundedUnder (· ≤ ·) atTop (fun n => (S m n).toReal) :=
    fun m => Filter.isCoboundedUnder_le_of_le atTop (x := 0)
      (fun n => ENNReal.toReal_nonneg)
  have hDbdd : ∀ m, IsBoundedUnder (· ≤ ·) atTop (fun n => D m n) :=
    fun m => ⟨ψ 1, by
      rw [eventually_map]
      exact Eventually.of_forall (fun n => (hDbound m n).trans
        (hψmono (hStoReal m n)))⟩
  have hDcobdd : ∀ m, IsCoboundedUnder (· ≤ ·) atTop (fun n => D m n) :=
    fun m => Filter.isCoboundedUnder_le_of_le atTop (x := 0) (hDnonneg m)
  have hlimsup : ∀ m, limsup (fun n => D m n) atTop ≤
      ψ ((limsup (fun n => S m n) atTop).toReal) := by
    intro m
    have htoReal : limsup (fun n => (S m n).toReal) atTop =
        (limsup (fun n => S m n) atTop).toReal :=
      ENNReal.limsup_toReal_eq ENNReal.one_ne_top
        (Eventually.of_forall (hSle m))
    have hψSbdd : IsBoundedUnder (· ≤ ·) atTop (fun n => ψ ((S m n).toReal)) :=
      ⟨ψ 1, by
        rw [eventually_map]
        exact Eventually.of_forall (fun n => hψmono (hStoReal m n))⟩
    calc
      limsup (fun n => D m n) atTop ≤
          limsup (fun n => ψ ((S m n).toReal)) atTop :=
        limsup_le_limsup (Eventually.of_forall (hDbound m)) (hDcobdd m) hψSbdd
      _ = ψ (limsup (fun n => (S m n).toReal) atTop) :=
        (hψmono.map_limsup_of_continuousAt (fun n => (S m n).toReal)
          hψcont.continuousAt (hSbdd m) (hScobdd m)).symm
      _ = ψ ((limsup (fun n => S m n) atTop).toReal) := by rw [htoReal]
  have hmtail : Tendsto (fun m => ψ ((limsup (fun n => S m n) atTop).toReal))
      atTop (nhds (Kr * ε)) := by
    have hzero : Tendsto (fun m => (limsup (fun n => S m n) atTop).toReal)
        atTop (nhds 0) := by
      simpa using! (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hS3'
    have hh := (hψcont.tendsto 0).comp hzero
    simpa [ψ] using! hh
  have hlt : Kr * ε < ε' := lt_trans hKε (by linarith)
  have hclose : ∀ᶠ m in atTop,
      ψ ((limsup (fun n => S m n) atTop).toReal) < ε' :=
    hmtail.eventually (eventually_lt_nhds hlt)
  refine hclose.mono (fun m hm => ?_)
  have hnonneg : 0 ≤ limsup (fun n => D m n) atTop :=
    le_limsup_of_le (hDbdd m) (fun b hb => by
      obtain ⟨n, hn⟩ := hb.exists
      exact (hDnonneg m n).trans hn)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact (hlimsup m).trans_lt hm

private theorem ueWeakConvergesOuter_readout
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (nu : Measure (LinfF F)) (hnu : IsPBrownianBridge F P nu)
    (hclt : IsMarginalCLT F P) (heq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P)
    (f : BoundedContinuousFunction (LinfF F) ℝ)
    (hflip : ∃ K, LipschitzWith K f) :
    Tendsto (fun n =>
      (outerExpectation μ (fun ξ => ENNReal.ofReal
        (f (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ))) + ‖f‖))).toReal -
        ‖f‖ * (μ Set.univ).toReal) atTop (nhds (∫ y, f y ∂nu)) := by
  letI : Nonempty (LinfF F) := ⟨0⟩
  let 𝔾 : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ))
  let R : ℕ → ℝ := fun n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal (f (𝔾 n ξ) + ‖f‖))).toReal -
      ‖f‖ * (μ Set.univ).toReal
  let Rproj : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal
      (f (ueFiniteProj net hnet m (𝔾 n ξ)) + ‖f‖))).toReal -
      ‖f‖ * (μ Set.univ).toReal
  let Lproj : ℕ → ℝ := fun m => ∫ z, f (ueFiniteProj net hnet m z) ∂nu
  let L : ℝ := ∫ y, f y ∂nu
  let Dtail : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal
      |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|)).toReal
  change Tendsto R atTop (nhds L)
  refine tendsto_outerReadout_of_pieces R Rproj Lproj L Dtail
    ?_ ?_ ?_ ?_ ?_
  · intro m
    have hS2 := weakConvergesOuter_ueFiniteProj hHenv hH2 hFmeas net hnet nu hnu
      hclt m μ X hXmeas hXindep hXid hXlaw f
    have hmap : ∫ y, f y ∂(nu.map (ueFiniteProj net hnet m)) = Lproj m := by
      rw [integral_map (ueFiniteProj_measurable net hnet m).aemeasurable
        f.continuous.aestronglyMeasurable]
    change Tendsto (fun n =>
      (outerExpectation μ (fun ξ => ENNReal.ofReal
        (f (ueFiniteProj net hnet m (𝔾 n ξ)) + ‖f‖))).toReal -
          ‖f‖ * (μ Set.univ).toReal) atTop (nhds (Lproj m))
    rw [← hmap]
    convert hS2 using 2
  · have hS4 := ueLimit_proj_error net hnet nu hnu f
    letI : IsProbabilityMeasure nu := hnu.isProbabilityMeasure
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound : ∀ m, dist (Lproj m) L ≤
        ∫ z, |f (ueFiniteProj net hnet m z) - f z| ∂nu := by
      intro m
      change dist (∫ z, f (ueFiniteProj net hnet m z) ∂nu)
        (∫ z, f z ∂nu) ≤ _
      rw [Real.dist_eq]
      have hfint : Integrable f nu := f.integrable _
      have hpint : Integrable (fun z => f (ueFiniteProj net hnet m z)) nu :=
        Integrable.of_bound
          (f.continuous.measurable.comp
            (ueFiniteProj_measurable net hnet m)).aestronglyMeasurable
          ‖f‖ (Eventually.of_forall (fun z => f.norm_coe_le_norm _))
      rw [← integral_sub hpint hfint]
      exact abs_integral_le_integral_abs
    exact squeeze_zero (fun m => dist_nonneg) hbound hS4
  · intro m n
    have hb := abs_outerReadout_diff_le_readout_abs μ f (𝔾 n)
      (fun ξ => ueFiniteProj net hnet m (𝔾 n ξ))
    change |((outerExpectation μ (fun ξ => ENNReal.ofReal
      (f (𝔾 n ξ) + ‖f‖))).toReal - ‖f‖ * (μ Set.univ).toReal) -
      ((outerExpectation μ (fun ξ => ENNReal.ofReal
        (f (ueFiniteProj net hnet m (𝔾 n ξ)) + ‖f‖))).toReal -
          ‖f‖ * (μ Set.univ).toReal)| ≤ _
    have hcancel :
        ((outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (𝔾 n ξ) + ‖f‖))).toReal - ‖f‖ * (μ Set.univ).toReal) -
        ((outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (ueFiniteProj net hnet m (𝔾 n ξ)) + ‖f‖))).toReal -
            ‖f‖ * (μ Set.univ).toReal) =
        (outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (𝔾 n ξ) + ‖f‖))).toReal -
        (outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (ueFiniteProj net hnet m (𝔾 n ξ)) + ‖f‖))).toReal := by ring
    rw [hcancel]
    exact hb
  · exact ueEmpirical_readout_tail_outer hHenv hH2 net hnet heq μ X hXmeas
      hXindep hXid hXlaw f hflip
  · intro m
    refine Filter.isBoundedUnder_of ⟨2 * ‖f‖, fun n => ?_⟩
    change (outerExpectation μ (fun ξ => ENNReal.ofReal
      |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|)).toReal ≤
        2 * ‖f‖
    have hE : outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|) ≤
        ENNReal.ofReal (2 * ‖f‖) := by
      calc
        outerExpectation μ (fun ξ => ENNReal.ofReal
          |f (𝔾 n ξ) - f (ueFiniteProj net hnet m (𝔾 n ξ))|) ≤
            outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) := by
          refine outerExpectation_mono (fun ξ => ENNReal.ofReal_le_ofReal ?_)
          have ha := abs_le.1 (f.norm_coe_le_norm (𝔾 n ξ))
          have hb := abs_le.1 (f.norm_coe_le_norm
            (ueFiniteProj net hnet m (𝔾 n ξ)))
          rw [abs_le]
          constructor <;> [linarith [ha.1, hb.2]; linarith [ha.2, hb.1]]
        _ = ENNReal.ofReal (2 * ‖f‖) := by
          rw [outerExpectation_const, measure_univ, mul_one]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hE).trans_eq
      (ENNReal.toReal_ofReal (by positivity))

private theorem ueWeakConvergesOuter_withBridge
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    {H : Ω → ℝ} (hHenv : EmpiricalProcess.IsEnvelope F H) (hH2 : MemLp H 2 P)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (net : ℕ → Finset ↥F)
    (hnet : ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)))
    (nu : Measure (LinfF F)) (hnu : IsPBrownianBridge F P nu)
    (hclt : IsMarginalCLT F P) (heq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
        (memℓp_empiricalProcess
          ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
          (fun i : Fin n => X i.val ξ))) nu := by
  letI : IsProbabilityMeasure nu := hnu.isProbabilityMeasure
  exact weakConvergesOuter_of_lipschitz_readout
    (μ := fun _ => μ)
    (Xn := fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ)))
    (νD := nu)
    (fun f hflip => ueWeakConvergesOuter_readout hHenv hH2 hFmeas net hnet
      nu hnu hclt heq μ X hXmeas hXindep hXid hXlaw f hflip)

/-- A tight `P`-Brownian bridge from uniform entropy. The measurable
majorant, separable Gaussian carrier, finite/infinite-dimensional split, and
tight uniformly-`distL2`-continuous path law are constructed from the book
inputs.

Edge behavior: `F = ∅` and zero envelope norm yield the degenerate zero bridge.
The supplied envelope itself need not be measurable. -/
theorem uniformEntropy_exists_pBrownianBridge
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
      -- vdV 19.14 measurable class members.
    (hPM : IsPointwiseMeasurable F)
      -- vdV 19.14 suitable measurability/separability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV 19.14 possibly nonmeasurable envelope.
    (hG2 : outerLpNorm P G 2 < ⊤)
      -- vdV 19.14 finite outer squared-envelope moment.
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
      -- vdV 19.14 uniform entropy integral.
    : ∃ ν : Measure (LinfF F), IsPBrownianBridge F P ν := by
  classical
  by_cases hF : F.Nonempty
  swap
  · have hFe : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    subst F
    exact ⟨Measure.dirac 0, emptyClass_pBrownianBridge P⟩
  obtain ⟨H, hHmeas, hHs, hH2⟩ :=
    exists_measurable_l2_envelope hFmeas hPM hEnv hG2
  have hHenv : EmpiricalProcess.IsEnvelope F H := hHs.2
  obtain ⟨net, hnet, hmono, hDudley⟩ :=
    uniformEntropy_exists_dudleyNet F hF G P hFmeas hEnv hG2 hJ
  have hHsep : TopologicalSpace.SeparableSpace ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas) :=
    separableSpace_gpH_of_dudleyNet hHenv hH2 hFmeas net hnet
  by_cases hfin : FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas)
  · letI : FiniteDimensional ℝ ↥(gpH ⟨H, hHenv, hH2⟩ hFmeas) := hfin
    exact ⟨finiteGaussianPBridge hHenv hH2 hFmeas,
      isPBrownianBridge_finiteGaussianPBridge hHenv hH2 hFmeas⟩
  · exact ⟨(iidStdGaussian : Measure (ℕ → ℝ)).map
        (ueBridgePath hHenv hH2 hFmeas hfin hHsep net hnet),
      uniformEntropy_infinite_pBrownianBridge hHenv hH2 hFmeas hfin hHsep net hnet
        hmono hDudley⟩

/-- The canonical bridge law selected by
`uniformEntropy_exists_pBrownianBridge`.

This selects the tight `P`-Brownian bridge constructed by the preceding theorem.
Edge behavior is inherited from
`uniformEntropy_exists_pBrownianBridge`, including the empty/zero degenerate
bridge. -/
noncomputable def uniformEntropyPBrownianBridge
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f) (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG2 : outerLpNorm P G 2 < ⊤)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) : Measure (LinfF F) :=
  (uniformEntropy_exists_pBrownianBridge F G P hFmeas hPM hEnv hG2 hJ).choose

/-- Uniform-net full `LinfF` outer weak convergence. For every iid
`P` sample, the complete empirical-process path is bounded and converges in
outer weak distribution to the internally selected tight bridge.

The proof combines the marginal CLT, asymptotic equicontinuity, and uniform-net
discretization;
pointwise or finite-dimensional convergence alone does not discharge this
statement. No bridge, equicontinuity, Donsker, or Dudley object is a hypothesis. -/
theorem uniformEntropy_empiricalProcess_weakConvergesOuter
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
      -- vdV 19.14 measurable class members.
    (hPM : IsPointwiseMeasurable F)
      -- vdV 19.14 suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV 19.14 envelope condition.
    (hG2 : outerLpNorm P G 2 < ⊤)
      -- vdV 19.14 finite outer squared-envelope moment.
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
      -- vdV 19.14 uniform entropy integral.
    : ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
        [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
        (∀ i, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X μ →
        (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
        μ.map (X 0) = P →
        ∃ hmem : ∀ n ξ, Memℓp
            (fun f : ↥F => empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (f : Ω → ℝ)) ∞,
          WeakConvergesOuter (fun _ => μ)
            (fun n ξ => empiricalProcessLinf
              (fun i : Fin n => X i.val ξ) (hmem n ξ))
            (uniformEntropyPBrownianBridge F G P hFmeas hPM hEnv hG2 hJ) := by
  classical
  intro Ξ _ μ _ X hXmeas hXindep hXid hXlaw
  obtain ⟨H, hHmeas, hHs, hH2⟩ :=
    exists_measurable_l2_envelope hFmeas hPM hEnv hG2
  have hHenv : EmpiricalProcess.IsEnvelope F H := hHs.2
  obtain ⟨net, hnet⟩ : ∃ net : ℕ → Finset ↥F,
      ∀ (j : ℕ) (f : ↥F), ∃ g ∈ net j,
        distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < (2 : ℝ) ^ (-(j : ℤ)) := by
    by_cases hF : F.Nonempty
    · obtain ⟨net, hnet, _, _⟩ :=
        uniformEntropy_exists_dudleyNet F hF G P hFmeas hEnv hG2 hJ
      exact ⟨net, hnet⟩
    · refine ⟨fun _ => ∅, fun j f => ?_⟩
      exact (hF ⟨(f : Ω → ℝ), f.2⟩).elim
  have hnu : IsPBrownianBridge F P
      (uniformEntropyPBrownianBridge F G P hFmeas hPM hEnv hG2 hJ) := by
    simpa only [uniformEntropyPBrownianBridge] using
      (uniformEntropy_exists_pBrownianBridge F G P hFmeas hPM hEnv hG2 hJ).choose_spec
  have hclt : IsMarginalCLT F P := isMarginalCLT_of_memLp
    (fun _ hf => memLp_of_mem_F hHenv hH2 hFmeas hf)
  have heq : IsAsymptoticallyEquicontinuous F P :=
    uniformEntropy_asymptoticallyEquicontinuous F G P hFmeas hPM hEnv hG2 hJ
  let hmem : ∀ n ξ, Memℓp
      (fun f : ↥F => empiricalProcess P n (fun i : Fin n => X i.val ξ)
        (f : Ω → ℝ)) ∞ := fun n ξ =>
    memℓp_empiricalProcess
      ⟨H, hHenv, hH2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
      (fun i : Fin n => X i.val ξ)
  refine ⟨hmem, ?_⟩
  simpa only [hmem] using
    (ueWeakConvergesOuter_withBridge hHenv hH2 hFmeas net hnet
      (uniformEntropyPBrownianBridge F G P hFmeas hPM hEnv hG2 hJ) hnu
      hclt heq μ X hXmeas hXindep hXid hXlaw)

/-- Theorem 19.14 Donsker package. The measurable class, marginal CLT,
asymptotic equicontinuity, and full-path bridge law are all constructed from
the book hypotheses and packaged as `PDonskerProcessData`.

The empty-class and zero-envelope branches are included, and equicontinuity,
the bridge, Donsker data, and a Dudley schedule follow from the assumptions. -/
theorem uniformEntropy_pdonskerProcessData_core
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    -- LEAN-ONLY: explicit measurability of the class members.
    (hFmeas : ∀ f ∈ F, Measurable f)
    -- USER-INPUT: pointwise measurability, a finite-`L²` envelope, and finite
    -- uniform entropy integral; vdV Theorem 19.14.
    (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG2 : outerLpNorm P G 2 < ⊤)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
    : PDonskerProcessData F P := by
  refine
    { measurable := hFmeas
      operational := ⟨uniformEntropy_marginalCLT hFmeas hEnv hG2,
        uniformEntropy_asymptoticallyEquicontinuous F G P hFmeas hPM hEnv hG2 hJ⟩
      literal := ?_ }
  refine ⟨uniformEntropyPBrownianBridge F G P hFmeas hPM hEnv hG2 hJ,
    (uniformEntropy_exists_pBrownianBridge F G P hFmeas hPM hEnv hG2 hJ).choose_spec, ?_⟩
  intro Ξ _ μ _ X hXmeas hXindep hXid hXlaw
  exact uniformEntropy_empiricalProcess_weakConvergesOuter
    F G P hFmeas hPM hEnv hG2 hJ μ X hXmeas hXindep hXid hXlaw

end AsymptoticStatistics.EmpiricalProcess
