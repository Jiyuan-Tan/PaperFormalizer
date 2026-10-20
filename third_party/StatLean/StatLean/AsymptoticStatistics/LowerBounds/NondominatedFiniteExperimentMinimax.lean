module
public import StatLean.AsymptoticStatistics.Experiment.FiniteRiskCompactification
public import StatLean.AsymptoticStatistics.LowerBounds.GaussianConeMinimax
public import StatLean.AsymptoticStatistics.Core.NondominatedPathwise
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird
public import StatLean.AsymptoticStatistics.LowerBounds.NondominatedOperationalEfficiencyAnalytic
public import StatLean.AsymptoticStatistics.ForMathlib.CramerWoldEuclidean
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
public import StatLean.AsymptoticStatistics.ForMathlib.DiagonalSubseqLimSupFinset
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! # Finite-experiment minimax transfer for nondominated selected paths -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.NondominatedFiniteExperimentMinimax

open AsymptoticStatistics
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedTangent
open AsymptoticStatistics.Core.NondominatedPathwise
open AsymptoticStatistics.Core.NondominatedQMDPath
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.LowerBounds.GaussianConeBayes
open AsymptoticStatistics.LowerBounds.GaussianConeMinimax
open AsymptoticStatistics.LowerBounds.T6_FinDimLAN.NondominatedQMDLeCamThird
open AsymptoticStatistics.LowerBounds.NondominatedOperationalEfficiencyAnalytic

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Selected-path local asymptotic minimax left-hand side. The finite sets range over
the subtype carrier of the nondominated tangent cone, and every local law is
the independently selected path stored in `C.selectedPath`. -/
noncomputable def selectedPathCanonicalLHSVec {d : ℕ}
    (C : NondominatedTangentCone P)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
    Filter.liminf (fun n : ℕ => I.sup (fun g =>
      ∫⁻ X : Fin n → Ω, ℓ (Real.sqrt n • (T_n n X -
          ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))
        ∂(Measure.pi (fun _ : Fin n =>
          (C.selectedPath g).curve ((Real.sqrt n)⁻¹))))) atTop

/-- Selected-path LAM risk is monotone in the loss.

Proof idea: monotonicity of `lintegral`, `Finset.sup`, `liminf`, and `iSup`. -/
theorem selectedPathCanonicalLHSVec_mono {d : ℕ}
    (C : NondominatedTangentCone P)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    {f g : EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (_hfg : ∀ x, f x ≤ g x) :
    selectedPathCanonicalLHSVec C T_n ψ f ≤
      selectedPathCanonicalLHSVec C T_n ψ g := by
  unfold selectedPathCanonicalLHSVec
  refine iSup_mono ?_
  intro I
  refine Filter.liminf_le_liminf
    (Filter.Eventually.of_forall (fun n => ?_))
  refine Finset.sup_mono_fun (fun h _ => ?_)
  exact lintegral_mono fun X => _hfg _

/-- Covariance of the finite score experiment indexed by carrier points. -/
noncomputable def finiteCarrierScoreCovariance
    (C : NondominatedTangentCone P)
    (I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier}) :
    Matrix (Fin I.card) (Fin I.card) ℝ :=
  Matrix.gram ℝ (fun j : Fin I.card =>
    ((I.equivFin).symm j).1.1)

/-- Mean coordinates of a carrier score in its finite score experiment. -/
noncomputable def finiteCarrierScoreMean
    (C : NondominatedTangentCone P)
    (I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier})
    (g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier}) :
    EuclideanSpace ℝ (Fin I.card) :=
  (WithLp.equiv 2 _).symm (fun j =>
    ⟪(((I.equivFin).symm j).1 : ↥(L2ZeroMean P)),
      (g : ↥(L2ZeroMean P))⟫_ℝ)

private theorem finiteCarrierScoreMean_selected_eq {C : NondominatedTangentCone P}
    (I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier}) (j : Fin I.card) :
    finiteCarrierScoreMean C I ((I.equivFin).symm j) =
      ((Matrix.toEuclideanCLM (𝕜 := ℝ)) (finiteCarrierScoreCovariance C I))
        (WithLp.toLp 2 (Pi.single j (1 : ℝ))) := by
  ext i
  change ⟪(((I.equivFin).symm i).1 : ↥(L2ZeroMean P)),
      (((I.equivFin).symm j).1 : ↥(L2ZeroMean P))⟫_ℝ = _
  rw [Matrix.toEuclideanCLM_toLp, Matrix.mulVec_single_one]
  rfl

private lemma integral_l2ZeroMean_eq_zero'
    (u : ↥(L2ZeroMean P)) :
    ∫ x, (u : Ω → ℝ) x ∂P = 0 := by
  have hu : integralL2 P (u : Lp ℝ 2 P) = 0 := by
    have hmem : (u : Lp ℝ 2 P) ∈ L2ZeroMean P := u.2
    change (u : Lp ℝ 2 P) ∈ LinearMap.ker (integralL2 P).toLinearMap at hmem
    rw [LinearMap.mem_ker] at hmem
    exact hmem
  change ⟪oneL2 P, (u : Lp ℝ 2 P)⟫_ℝ = 0 at hu
  rw [MeasureTheory.L2.inner_def] at hu
  have hone : (oneL2 P : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  rw [integral_congr_ae (hone.mono fun x hx => by
    change (u : Ω → ℝ) x * (oneL2 P : Ω → ℝ) x = (u : Ω → ℝ) x
    rw [hx, mul_one])] at hu
  exact hu

private lemma integral_l2ZeroMean_mul'
    (u v : ↥(L2ZeroMean P)) :
    ∫ x, (u : Ω → ℝ) x * (v : Ω → ℝ) x ∂P = ⟪u, v⟫_ℝ := by
  change ∫ x, (u : Ω → ℝ) x * (v : Ω → ℝ) x ∂P =
    ⟪(u : Lp ℝ 2 P), (v : Lp ℝ 2 P)⟫_ℝ
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with x
  change (u : Ω → ℝ) x * (v : Ω → ℝ) x =
    (v : Ω → ℝ) x * (u : Ω → ℝ) x
  ring_nf

private noncomputable def finiteScoreAtom {r : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) (x : Ω) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun i => ((v i : Lp ℝ 2 P) : Ω → ℝ) x)

private lemma measurable_finiteScoreAtom {r : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) :
    Measurable (finiteScoreAtom (P := P) v) := by
  unfold finiteScoreAtom
  refine (WithLp.measurable_toLp 2 (Fin r → ℝ)).comp ?_
  exact measurable_pi_lambda _ fun i =>
    (Lp.stronglyMeasurable (v i : Lp ℝ 2 P)).measurable

private lemma inner_finiteScoreAtom {r : ℕ}
    (v : Fin r → ↥(L2ZeroMean P))
    (a : EuclideanSpace ℝ (Fin r)) (x : Ω) :
    ⟪a, finiteScoreAtom v x⟫_ℝ = ∑ i, a i * (v i : Ω → ℝ) x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (v i : Ω → ℝ) x * a i = a i * (v i : Ω → ℝ) x
  ring_nf

private lemma measurable_normalizedScoreSum' (u : ↥(L2ZeroMean P)) (n : ℕ) :
    Measurable (normalizedScoreSum u n) := by
  unfold normalizedScoreSum
  exact Measurable.const_mul
    (Finset.measurable_sum _ fun i _ =>
      (Lp.stronglyMeasurable (u : Lp ℝ 2 P)).measurable.comp
        (measurable_pi_apply i)) _

/-- Baseline CLT for an arbitrary finite vector of `L²₀(P)` scores. -/
private theorem weakConverges_finiteScore_under_pi {r : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) :
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n => P)).map
        (fun X => WithLp.toLp 2 (fun j => normalizedScoreSum (v j) n X)))
      (multivariateGaussian 0 (Matrix.gram ℝ v)) := by
  classical
  let Pinf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P)
  let Y : ℕ → (ℕ → Ω) → EuclideanSpace ℝ (Fin r) :=
    fun i X => finiteScoreAtom v (X i)
  haveI : IsProbabilityMeasure Pinf := by dsimp [Pinf]; infer_instance
  have hYmeas : ∀ i, Measurable (Y i) := fun i =>
    (measurable_finiteScoreAtom v).comp (measurable_pi_apply i)
  have hiid : iIndepFun Y Pinf := by
    have heval : iIndepFun (fun i (X : ℕ → Ω) => X i) Pinf := by
      dsimp only [Pinf]
      exact iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
    exact heval.comp (g := fun _ => finiteScoreAtom v)
      fun _ => measurable_finiteScoreAtom v
  have hevalLaw : ∀ i, Pinf.map (fun X : ℕ → Ω => X i) = P := fun i => by
    dsimp only [Pinf]
    exact Measure.infinitePi_map_eval (fun _ : ℕ => P) i
  have hYlaw : ∀ i, Pinf.map (Y i) = P.map (finiteScoreAtom v) := fun i => by
    rw [show Y i = finiteScoreAtom v ∘ fun X : ℕ → Ω => X i from rfl,
      ← Measure.map_map (measurable_finiteScoreAtom v) (measurable_pi_apply i),
      hevalLaw]
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) Pinf Pinf := fun i =>
    ⟨(hYmeas i).aemeasurable, (hYmeas 0).aemeasurable, by rw [hYlaw i, hYlaw 0]⟩
  have hzero : ∀ a : EuclideanSpace ℝ (Fin r),
      ∫ X, ⟪a, Y 0 X⟫_ℝ ∂Pinf = 0 := by
    intro a
    have hasm : AEStronglyMeasurable
        (fun x : Ω => ⟪a, finiteScoreAtom v x⟫_ℝ)
        (Pinf.map (fun X : ℕ → Ω => X 0)) := by
      rw [hevalLaw 0]
      exact (((continuous_const.inner continuous_id).measurable.comp
        (measurable_finiteScoreAtom v)).aestronglyMeasurable)
    have hmap :
        ∫ x, ⟪a, finiteScoreAtom v x⟫_ℝ
            ∂(Pinf.map (fun X : ℕ → Ω => X 0)) =
          ∫ X, ⟪a, finiteScoreAtom v (X 0)⟫_ℝ ∂Pinf :=
      MeasureTheory.integral_map (measurable_pi_apply (0 : ℕ)).aemeasurable hasm
    rw [hevalLaw 0] at hmap
    rw [← hmap, integral_congr_ae
      (Filter.Eventually.of_forall fun x => inner_finiteScoreAtom v a x)]
    rw [MeasureTheory.integral_finset_sum _]
    · simp [MeasureTheory.integral_const_mul, integral_l2ZeroMean_eq_zero']
    · intro i _
      exact ((Lp.memLp (v i : Lp ℝ 2 P)).integrable (by norm_num)).const_mul (a i)
  have hcov : ∀ a b : EuclideanSpace ℝ (Fin r),
      ∫ X, ⟪a, Y 0 X⟫_ℝ * ⟪b, Y 0 X⟫_ℝ ∂Pinf =
        a.ofLp ⬝ᵥ (Matrix.gram ℝ v).mulVec b.ofLp := by
    intro a b
    have hasm : AEStronglyMeasurable
        (fun x : Ω => ⟪a, finiteScoreAtom v x⟫_ℝ * ⟪b, finiteScoreAtom v x⟫_ℝ)
        (Pinf.map (fun X : ℕ → Ω => X 0)) := by
      rw [hevalLaw 0]
      exact (((((continuous_const.inner continuous_id).measurable.comp
          (measurable_finiteScoreAtom v))).mul
        (((continuous_const.inner continuous_id).measurable.comp
          (measurable_finiteScoreAtom v)))).aestronglyMeasurable)
    have hmap :
        ∫ x, ⟪a, finiteScoreAtom v x⟫_ℝ * ⟪b, finiteScoreAtom v x⟫_ℝ
            ∂(Pinf.map (fun X : ℕ → Ω => X 0)) =
          ∫ X, ⟪a, finiteScoreAtom v (X 0)⟫_ℝ *
            ⟪b, finiteScoreAtom v (X 0)⟫_ℝ ∂Pinf :=
      MeasureTheory.integral_map (measurable_pi_apply (0 : ℕ)).aemeasurable hasm
    rw [hevalLaw 0] at hmap
    rw [← hmap]
    have hpw :
        (fun x => ⟪a, finiteScoreAtom v x⟫_ℝ * ⟪b, finiteScoreAtom v x⟫_ℝ) =
          fun x => ∑ i, ∑ j,
            (a i * b j) * ((v i : Ω → ℝ) x * (v j : Ω → ℝ) x) := by
      funext x
      rw [inner_finiteScoreAtom v a x, inner_finiteScoreAtom v b x,
        Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring_nf
    have hint : ∀ i j : Fin r, Integrable
        (fun x : Ω => (a i * b j) *
          ((v i : Ω → ℝ) x * (v j : Ω → ℝ) x)) P := by
      intro i j
      exact ((Lp.memLp (v i : Lp ℝ 2 P)).integrable_mul
        (Lp.memLp (v j : Lp ℝ 2 P))).const_mul (a i * b j)
    rw [hpw, MeasureTheory.integral_finset_sum _]
    · simp only [dotProduct, Matrix.mulVec]
      apply Finset.sum_congr rfl
      intro i _
      rw [MeasureTheory.integral_finset_sum _ (fun j _ => hint i j)]
      simp_rw [MeasureTheory.integral_const_mul, integral_l2ZeroMean_mul']
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Matrix.gram_apply]
      ring_nf
    · intro i _
      apply MeasureTheory.integrable_finset_sum
      intro j _
      exact hint i j
  have hL2atom : MemLp (finiteScoreAtom v) 2 P := by
    apply MemLp.of_eval_piLp
    intro i
    exact Lp.memLp (v i : Lp ℝ 2 P)
  have hL2 : MemLp (Y 0) 2 Pinf := by
    change MemLp (finiteScoreAtom v ∘ fun X : ℕ → Ω => X 0) 2 Pinf
    refine (MeasureTheory.memLp_map_measure_iff ?_
      (measurable_pi_apply (0 : ℕ)).aemeasurable).mp ?_
    · rw [hevalLaw 0]
      exact (measurable_finiteScoreAtom v).aestronglyMeasurable
    · rw [hevalLaw 0]
      exact hL2atom
  have hclt := AsymptoticStatistics.ScoreCLT.clt_finDim Pinf Y hYmeas hiid hident
    hzero (Matrix.gram ℝ v) (Matrix.posSemidef_gram ℝ v) hcov hL2
  let V : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin r) := fun n X =>
    WithLp.toLp 2 (fun i => normalizedScoreSum (v i) n X)
  have hVmeas : ∀ n, Measurable (V n) := fun n => by
    dsimp only [V, normalizedScoreSum]
    refine (WithLp.measurable_toLp 2 (Fin r → ℝ)).comp ?_
    exact measurable_pi_lambda _ fun i => Measurable.const_mul
      (Finset.measurable_sum _ fun j _ =>
        (Lp.stronglyMeasurable (v i : Lp ℝ 2 P)).measurable.comp
          (measurable_pi_apply j)) _
  have hrestrict : ∀ n, Measurable (fun X : ℕ → Ω => fun i : Fin n => X i.val) :=
    fun n => measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have heq : ∀ n, (Measure.pi (fun _ : Fin n => P)).map (V n) =
      Pinf.map (fun X => (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, Y i X) := by
    intro n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n,
      Measure.map_map (hVmeas n) (hrestrict n)]
    congr 1
    funext X
    apply (WithLp.equiv 2 (Fin r → ℝ)).injective
    funext i
    change (Real.sqrt n)⁻¹ * ∑ j : Fin n, (v i : Ω → ℝ) (X j.val) =
      (((Real.sqrt n)⁻¹ • ∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin r)).ofLp) i
    have hsum : (((∑ j ∈ Finset.range n, Y j X) :
        EuclideanSpace ℝ (Fin r)).ofLp) i =
        ∑ j ∈ Finset.range n, ((Y j X : EuclideanSpace ℝ (Fin r)).ofLp) i := by
      have hlin : (((∑ j ∈ Finset.range n, Y j X) :
          EuclideanSpace ℝ (Fin r)).ofLp) =
          ∑ j ∈ Finset.range n, ((Y j X : EuclideanSpace ℝ (Fin r)).ofLp) :=
        map_sum (WithLp.linearEquiv 2 ℝ (Fin r → ℝ)).toLinearMap _ _
      rw [hlin]
      exact Finset.sum_apply i _ _
    rw [show (((Real.sqrt n)⁻¹ • ∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin r)).ofLp) i =
      (Real.sqrt n)⁻¹ * (((∑ j ∈ Finset.range n, Y j X :
        EuclideanSpace ℝ (Fin r)).ofLp) i) from rfl, hsum]
    change (Real.sqrt n)⁻¹ * ∑ j : Fin n, (v i : Ω → ℝ) (X j.val) =
      (Real.sqrt n)⁻¹ * ∑ j ∈ Finset.range n, (v i : Ω → ℝ) (X j)
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun j => ((v i : Lp ℝ 2 P) : Ω → ℝ) (X j)) n
  change WeakConverges
    (fun n => (Measure.pi (fun _ : Fin n => P)).map (V n))
    (multivariateGaussian 0 (Matrix.gram ℝ v))
  intro f
  simpa only [heq] using hclt f

private lemma exp_affine_score_integrable_and_integral_euclidean {k : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin k) × ℝ)) [IsProbabilityMeasure π]
    (γ : NondominatedQMDPath P) (a : ℝ)
    (hsnd : π.map Prod.snd =
      gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) :
    let tiltMap : EuclideanSpace ℝ (Fin k) × ℝ →
        EuclideanSpace ℝ (Fin k) × ℝ := fun q =>
      (q.1, a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)
    Integrable (fun q => Real.exp q.2) (π.map tiltMap) ∧
      ∫ q, Real.exp q.2 ∂(π.map tiltMap) = 1 := by
  dsimp only
  let c : ℝ := (a ^ 2 / 2) * ‖γ.score‖ ^ 2
  let g : ℝ → ℝ := fun x => Real.exp (a * x - c)
  let tiltMap : EuclideanSpace ℝ (Fin k) × ℝ →
      EuclideanSpace ℝ (Fin k) × ℝ := fun q => (q.1, a * q.2 - c)
  have hg_meas : Measurable g := by fun_prop
  have htilt : Measurable tiltMap := by fun_prop
  have hgauss : Integrable g
      (gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) := by
    have hbase := ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := (0 : ℝ)) (v := ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) a
    have hmul := hbase.mul_const (Real.exp (-c))
    exact hmul.congr (Filter.Eventually.of_forall fun x => by
      dsimp only [g]
      rw [sub_eq_add_neg, Real.exp_add])
  have hgauss_int : ∫ x, g x
        ∂(gaussianReal 0 (NNReal.mk (‖γ.score‖ ^ 2) (sq_nonneg _))) = 1 := by
    dsimp only [g]
    simp_rw [sub_eq_add_neg, Real.exp_add]
    rw [integral_mul_const,
      ProbabilityTheory.integral_exp_mul_gaussianReal]
    dsimp only [c]
    rw [← Real.exp_add]
    simp
    ring_nf
  have hpull : Integrable
      (fun q : EuclideanSpace ℝ (Fin k) × ℝ => g q.2) π := by
    rw [← hsnd] at hgauss
    exact hgauss.comp_measurable measurable_snd
  constructor
  · refine (integrable_map_measure (by fun_prop) htilt.aemeasurable).mpr ?_
    simpa only [Function.comp_apply, tiltMap, g] using! hpull
  · rw [integral_map htilt.aemeasurable (by fun_prop)]
    change ∫ q, g q.2 ∂π = 1
    calc
      _ = ∫ x, g x ∂(π.map Prod.snd) := by
        rw [integral_map measurable_snd.aemeasurable (by
          rw [hsnd]
          exact hgauss.aestronglyMeasurable)]
      _ = 1 := by rw [hsnd]; exact hgauss_int

/-- Euclidean-valued selected-path Le Cam third lemma, obtained from the scalar
theorem by Cramér--Wold.  The joint law is derived in the proof, without a
common dominating measure. -/
private theorem qmd_lecamThird_euclidean_along_subseq {k : ℕ}
    (γ : NondominatedQMDPath P) (a : ℝ) (ha : 0 ≤ a)
    (Y : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (hY : ∀ n, Measurable (Y n))
    (χ : ℕ → ℕ) (hχ : StrictMono χ)
    (π : Measure (EuclideanSpace ℝ (Fin k) × ℝ)) [IsProbabilityMeasure π]
    (hπ : WeakConverges
      (fun m => (Measure.pi (fun _ : Fin (χ m) => P)).map
        (fun X => (Y (χ m) X, normalizedScoreSum γ.score (χ m) X))) π) :
    WeakConverges
      (fun m => (Measure.pi (fun _ : Fin (χ m) =>
        γ.curve (a * (Real.sqrt (χ m))⁻¹))).map (Y (χ m)))
      ((π.withDensity (fun q => ENNReal.ofReal (Real.exp
        (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst) := by
  have hpairMeas : ∀ m, Measurable (fun X : Fin (χ m) → Ω =>
      (Y (χ m) X, normalizedScoreSum γ.score (χ m) X)) := fun m =>
    (hY (χ m)).prodMk (measurable_normalizedScoreSum' γ.score (χ m))
  have hscore_sub : WeakConverges
      (fun m => (Measure.pi (fun _ : Fin (χ m) => P)).map
        (normalizedScoreSum γ.score (χ m)))
      (gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) := by
    simpa only [zero_mul, γ.curve_at_zero] using
      (qmd_local_score_clt γ 0 le_rfl γ.score).comp hχ
  have hscore_as_snd : WeakConverges
      (fun m => ((Measure.pi (fun _ : Fin (χ m) => P)).map
        (fun X => (Y (χ m) X, normalizedScoreSum γ.score (χ m) X))).map Prod.snd)
      (gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩) := by
    simpa only [Measure.map_map measurable_snd (hpairMeas _)] using! hscore_sub
  have hπsnd : π.map Prod.snd =
      gaussianReal 0 ⟨‖γ.score‖ ^ 2, sq_nonneg _⟩ :=
    WeakConverges.snd_eq hπ hscore_as_snd
  let tiltMap : EuclideanSpace ℝ (Fin k) × ℝ →
      EuclideanSpace ℝ (Fin k) × ℝ := fun q =>
    (q.1, a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)
  have hmgf := exp_affine_score_integrable_and_integral_euclidean
    (P := P) π γ a hπsnd
  have htilt_meas : Measurable tiltMap := by fun_prop
  have hdens_meas : Measurable
      (fun q : EuclideanSpace ℝ (Fin k) × ℝ =>
        ENNReal.ofReal (Real.exp
          (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2))) := by fun_prop
  let ν : Measure (EuclideanSpace ℝ (Fin k)) :=
    (π.withDensity (fun q => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst
  have hraw_int : Integrable (fun q : EuclideanSpace ℝ (Fin k) × ℝ =>
      Real.exp (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)) π := by
    exact (integrable_map_measure hmgf.1.aestronglyMeasurable
      htilt_meas.aemeasurable).mp hmgf.1
  have hraw_integral : ∫ q : EuclideanSpace ℝ (Fin k) × ℝ,
      Real.exp (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2) ∂π = 1 := by
    calc
      _ = ∫ q, Real.exp q.2 ∂(π.map tiltMap) := by
        rw [integral_map htilt_meas.aemeasurable hmgf.1.aestronglyMeasurable]
      _ = 1 := hmgf.2
  have hmass : (π.withDensity (fun q => ENNReal.ofReal (Real.exp
      (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))) Set.univ = 1 := by
    rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      MeasureTheory.setLIntegral_univ]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hraw_int
      (Filter.Eventually.of_forall (fun q => (Real.exp_pos _).le))]
    rw [hraw_integral, ENNReal.ofReal_one]
  haveI htilt_prob : IsProbabilityMeasure
      (π.withDensity (fun q => ENNReal.ofReal (Real.exp
        (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))) := ⟨hmass⟩
  haveI hνprob : IsProbabilityMeasure ν := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : ∀ m, IsProbabilityMeasure
      (Measure.pi (fun _ : Fin (χ m) =>
        γ.curve (a * (Real.sqrt (χ m))⁻¹))) := fun m => by
    letI : IsProbabilityMeasure
        (γ.curve (a * (Real.sqrt (χ m))⁻¹)) :=
      γ.curve_isProbability _
        (mul_nonneg ha (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    infer_instance
  letI : ∀ m, IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin (χ m) =>
        γ.curve (a * (Real.sqrt (χ m))⁻¹))).map (Y (χ m))) := fun m =>
    Measure.isProbabilityMeasure_map (hY (χ m)).aemeasurable
  change WeakConverges
    (fun m => (Measure.pi (fun _ : Fin (χ m) =>
      γ.curve (a * (Real.sqrt (χ m))⁻¹))).map (Y (χ m))) ν
  apply AsymptoticStatistics.ForMathlib.cramerWold_weakConverges_euclidean
  intro lam
  let proj : EuclideanSpace ℝ (Fin k) → ℝ := fun y => @inner ℝ _ _ lam y
  let pairMap : EuclideanSpace ℝ (Fin k) × ℝ → ℝ × ℝ :=
    fun q => (proj q.1, q.2)
  have hproj_cont : Continuous proj := by fun_prop
  have hproj_meas : Measurable proj := hproj_cont.measurable
  have hpairMap_cont : Continuous pairMap := by fun_prop
  have hpairMap_meas : Measurable pairMap := hpairMap_cont.measurable
  letI : IsProbabilityMeasure (π.map pairMap) :=
    Measure.isProbabilityMeasure_map hpairMap_meas.aemeasurable
  have hπlam0 := hπ.map hpairMap_cont hpairMap_meas
  have hπlam : WeakConverges
      (fun m => (Measure.pi (fun _ : Fin (χ m) => P)).map
        (fun X => (proj (Y (χ m) X),
          normalizedScoreSum γ.score (χ m) X)))
      (π.map pairMap) := by
    change WeakConverges
      (fun m => ((Measure.pi (fun _ : Fin (χ m) => P)).map
        (fun X => (Y (χ m) X,
          normalizedScoreSum γ.score (χ m) X))).map pairMap) _ at hπlam0
    simpa only [Measure.map_map hpairMap_meas (hpairMeas _),
      Function.comp_apply, pairMap] using! hπlam0
  have hscalar := qmd_lecamThird_along_subseq γ a ha
    (fun n X => proj (Y n X))
    (fun n => hproj_meas.comp (hY n)) χ hχ (π.map pairMap) hπlam
  have htarget :
      (((π.map pairMap).withDensity (fun q => ENNReal.ofReal (Real.exp
        (a * q.2 - (a ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst) =
      ν.map proj := by
    rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      π pairMap hpairMap_meas _ (by fun_prop)]
    rw [Measure.map_map measurable_fst hpairMap_meas,
      Measure.map_map hproj_meas measurable_fst]
    rfl
  rw [← htarget]
  change WeakConverges
    (fun m => ((Measure.pi (fun _ : Fin (χ m) =>
      γ.curve (a * (Real.sqrt (χ m))⁻¹))).map (Y (χ m))).map proj) _
  simpa only [Measure.map_map hproj_meas (hY _), Function.comp_apply] using! hscalar

/-- Joint compactness for a finite baseline score vector and a bounded loss
profile, obtained directly from the finite experiment. -/
private theorem finiteScoreProfile_joint_subsequence {r d : ℕ}
    (v : Fin r → ↥(L2ZeroMean P))
    (action : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (haction : ∀ n, Measurable (action n))
    (center : Fin r → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hfinite : ∀ x, ℓ x ≠ ∞)
    (hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (huc : UniformContinuous fun x => (ℓ x).toReal)
    (χ : ℕ → ℕ) (hχ : StrictMono χ) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧
      ∃ π : Measure (EuclideanSpace ℝ (Fin r) ×
          EuclideanSpace ℝ (Fin r)), IsProbabilityMeasure π ∧
        WeakConverges
          (fun k => (Measure.pi (fun _ : Fin (χ (τ k)) => P)).map
            (fun X =>
              (WithLp.toLp 2 (fun j => normalizedScoreSum (v j) (χ (τ k)) X),
                Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ
                  (action (χ (τ k)) X)))) π ∧
        π.map Prod.fst = multivariateGaussian 0 (Matrix.gram ℝ v) ∧
        (π.map Prod.snd)
          (closure (Set.range
            (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ))) = 1 := by
  classical
  let score : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin r) := fun n X =>
    WithLp.toLp 2 (fun j => normalizedScoreSum (v j) n X)
  let profile := Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ
  have hscore : ∀ n, Measurable (score n) := fun n => by
    dsimp only [score]
    refine (WithLp.measurable_toLp 2 (Fin r → ℝ)).comp ?_
    exact measurable_pi_lambda _ fun j => measurable_normalizedScoreSum' (v j) n
  have hprofile : Measurable profile :=
    (Experiment.FiniteRiskCompactification.finiteLossProfile_uniform_center
      center ℓ hfinite hbdd huc).1.continuous.measurable
  obtain ⟨_, K, hK, hrangeK⟩ :=
    Experiment.FiniteRiskCompactification.finiteLossProfile_uniform_center
      center ℓ hfinite hbdd huc
  have hclosureK : closure (Set.range profile) ⊆ K :=
    closure_minimal hrangeK hK.isClosed
  have hprofileCompact : IsCompact (closure (Set.range profile)) :=
    hK.of_isClosed_subset isClosed_closure hclosureK
  let joint : ℕ → Measure (EuclideanSpace ℝ (Fin r) ×
      EuclideanSpace ℝ (Fin r)) := fun k =>
    (Measure.pi (fun _ : Fin (χ k) => P)).map
      (fun X => (score (χ k) X, profile (action (χ k) X)))
  have hjointMeas : ∀ k, Measurable (fun X : Fin (χ k) → Ω =>
      (score (χ k) X, profile (action (χ k) X))) := fun k =>
    (hscore (χ k)).prodMk (hprofile.comp (haction (χ k)))
  letI : ∀ k, IsProbabilityMeasure (joint k) := fun k =>
    Measure.isProbabilityMeasure_map (hjointMeas k).aemeasurable
  have hfst (k : ℕ) : (joint k).map Prod.fst =
      (Measure.pi (fun _ : Fin (χ k) => P)).map (score (χ k)) := by
    dsimp only [joint]
    rw [Measure.map_map measurable_fst (hjointMeas k)]
    rfl
  have hsnd (k : ℕ) : (joint k).map Prod.snd =
      (Measure.pi (fun _ : Fin (χ k) => P)).map
        (fun X => profile (action (χ k) X)) := by
    dsimp only [joint]
    rw [Measure.map_map measurable_snd (hjointMeas k)]
    rfl
  have hscoreWeak : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (χ k) => P)).map (score (χ k)))
      (multivariateGaussian 0 (Matrix.gram ℝ v)) := by
    simpa only [score] using (weakConverges_finiteScore_under_pi v).comp hχ
  letI : ∀ k, IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin (χ k) => P)).map (score (χ k))) := fun k =>
    Measure.isProbabilityMeasure_map (hscore (χ k)).aemeasurable
  have hfstTight : IsTightMeasureSet
      ((fun ρ : Measure (EuclideanSpace ℝ (Fin r) ×
        EuclideanSpace ℝ (Fin r)) => ρ.map Prod.fst) '' Set.range joint) := by
    have himage :
        ((fun ρ : Measure (EuclideanSpace ℝ (Fin r) ×
          EuclideanSpace ℝ (Fin r)) => ρ.map Prod.fst) '' Set.range joint) =
        Set.range (fun k =>
          (Measure.pi (fun _ : Fin (χ k) => P)).map (score (χ k))) := by
      ext ρ
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨k, (hfst k).symm⟩
      · rintro ⟨k, rfl⟩
        exact ⟨joint k, ⟨k, rfl⟩, hfst k⟩
    rw [himage]
    exact Prohorov.weakConverges_range_tight _ _ hscoreWeak
  have hsndSupport (k : ℕ) : ((joint k).map Prod.snd)
      (closure (Set.range profile)) = 1 := by
    rw [hsnd k]
    rw [Measure.map_apply (f := fun X => profile (action (χ k) X))
      (hprofile.comp (haction (χ k))) isClosed_closure.measurableSet]
    have hpre : (fun X => profile (action (χ k) X)) ⁻¹'
        closure (Set.range profile) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro X
      exact subset_closure ⟨action (χ k) X, rfl⟩
    rw [hpre]
    simp
  have hsndTight : IsTightMeasureSet
      ((fun ρ : Measure (EuclideanSpace ℝ (Fin r) ×
        EuclideanSpace ℝ (Fin r)) => ρ.map Prod.snd) '' Set.range joint) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro e he
    refine ⟨closure (Set.range profile), hprofileCompact, ?_⟩
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    letI : IsProbabilityMeasure ((joint k).map Prod.snd) :=
      Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    rw [(prob_compl_eq_zero_iff isClosed_closure.measurableSet).2 (hsndSupport k)]
    exact bot_le
  have hjointTight : IsTightMeasureSet (Set.range joint) :=
    Prohorov.tight_prod_of_tight_marginals _ hfstTight hsndTight
  obtain ⟨τ, hτ, π, hπprob, hπweak⟩ :=
    Prohorov.extract_weak_subseq joint hjointTight
  letI : IsProbabilityMeasure π := hπprob
  have hfstWeak : WeakConverges
      (fun k => (joint (τ k)).map Prod.fst)
      (multivariateGaussian 0 (Matrix.gram ℝ v)) := by
    simpa only [hfst] using hscoreWeak.comp hτ
  have hπfst : π.map Prod.fst = multivariateGaussian 0 (Matrix.gram ℝ v) :=
    WeakConverges.unique (hπweak.map continuous_fst measurable_fst) hfstWeak
  have hπsndSupport : (π.map Prod.snd) (closure (Set.range profile)) = 1 := by
    let Pn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin r)) := fun k =>
      ⟨(joint (τ k)).map Prod.snd,
        Measure.isProbabilityMeasure_map measurable_snd.aemeasurable⟩
    let Pπ : ProbabilityMeasure (EuclideanSpace ℝ (Fin r)) :=
      ⟨π.map Prod.snd, Measure.isProbabilityMeasure_map measurable_snd.aemeasurable⟩
    have htend : Tendsto Pn atTop (nhds Pπ) := by
      apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
      simpa [Pn, Pπ] using! hπweak.map continuous_snd measurable_snd
    have hclosed := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      (F := closure (Set.range profile)) htend isClosed_closure
    have hlimsup : limsup (fun k => ((Pn k : ProbabilityMeasure
        (EuclideanSpace ℝ (Fin r))) : Measure _) (closure (Set.range profile)))
        atTop = 1 := by
      simp [Pn, hsndSupport]
    have hone : (1 : ℝ≥0∞) ≤ (π.map Prod.snd) (closure (Set.range profile)) := by
      simpa [Pπ, hlimsup] using hclosed
    have hle : (π.map Prod.snd) (closure (Set.range profile)) ≤
        (π.map Prod.snd) Set.univ := measure_mono (Set.subset_univ _)
    have huniv : (π.map Prod.snd) Set.univ = 1 := by
      rw [Measure.map_apply measurable_snd MeasurableSet.univ]
      exact IsProbabilityMeasure.measure_univ
    exact le_antisymm (hle.trans_eq huniv) hone
  refine ⟨τ, hτ, π, hπprob, ?_, hπfst, ?_⟩
  · simpa only [joint, score, profile] using hπweak
  · simpa only [profile] using hπsndSupport

/-- A single selected path tilts the extracted finite score/profile law in
the corresponding score coordinate.  The result is proved from the scalar
nondominated third lemma through the Euclidean Cramér--Wold helper above. -/
private theorem finiteScoreProfile_selected_tilt {r : ℕ}
    (γ : NondominatedQMDPath P)
    (v : Fin r → ↥(L2ZeroMean P)) (j : Fin r) (hγscore : γ.score = v j)
    (profile : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin r))
    (hprofile : ∀ n, Measurable (profile n))
    (η : ℕ → ℕ) (hη : StrictMono η)
    (π : Measure (EuclideanSpace ℝ (Fin r) ×
      EuclideanSpace ℝ (Fin r))) [IsProbabilityMeasure π]
    (hπ : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (η k) => P)).map
        (fun X =>
          (WithLp.toLp 2 (fun i => normalizedScoreSum (v i) (η k) X),
            profile (η k) X))) π) :
    WeakConverges
      (fun k => Measure.map (profile (η k))
        (Measure.pi (fun _ : Fin (η k) =>
          γ.curve ((Real.sqrt (η k))⁻¹))))
      (Measure.map Prod.snd (π.withDensity (fun q =>
        ENNReal.ofReal (Real.exp (q.1 j - ‖γ.score‖ ^ 2 / 2))))) := by
  let score : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin r) := fun n X =>
    WithLp.toLp 2 (fun i => normalizedScoreSum (v i) n X)
  let enc : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) →
      EuclideanSpace ℝ (Fin (r + r)) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm
  let decProfile : EuclideanSpace ℝ (Fin (r + r)) →
      EuclideanSpace ℝ (Fin r) := fun z =>
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) z).2
  let Y : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin (r + r)) :=
    fun n X => enc (score n X, profile n X)
  have hscore : ∀ n, Measurable (score n) := fun n => by
    dsimp only [score]
    refine (WithLp.measurable_toLp 2 (Fin r → ℝ)).comp ?_
    exact measurable_pi_lambda _ fun i => measurable_normalizedScoreSum' (v i) n
  have henc_cont : Continuous enc :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).symm.continuous
  have henc_meas : Measurable enc := henc_cont.measurable
  have hY : ∀ n, Measurable (Y n) := fun n =>
    henc_meas.comp ((hscore n).prodMk (hprofile n))
  have hdec_cont : Continuous decProfile :=
    continuous_snd.comp (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).continuous
  have hdec_meas : Measurable decProfile := hdec_cont.measurable
  have hdecode (q : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) :
      decProfile (enc q) = q.2 := by
    exact congrArg Prod.snd
      ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).apply_symm_apply q)
  let pairMap : (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) →
      EuclideanSpace ℝ (Fin (r + r)) × ℝ := fun q => (enc q, q.1 j)
  have hpairMap_cont : Continuous pairMap := by
    exact henc_cont.prodMk
      ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin r => ℝ) j).comp
        continuous_fst)
  have hpairMap_meas : Measurable pairMap := hpairMap_cont.measurable
  letI : IsProbabilityMeasure (π.map pairMap) :=
    Measure.isProbabilityMeasure_map hpairMap_meas.aemeasurable
  have hπpair0 := hπ.map hpairMap_cont hpairMap_meas
  have hπpair : WeakConverges
      (fun k => (Measure.pi (fun _ : Fin (η k) => P)).map
        (fun X => (Y (η k) X, normalizedScoreSum γ.score (η k) X)))
      (π.map pairMap) := by
    change WeakConverges
      (fun k => ((Measure.pi (fun _ : Fin (η k) => P)).map
        (fun X => (score (η k) X, profile (η k) X))).map pairMap) _ at hπpair0
    simpa only [Measure.map_map hpairMap_meas
      ((hscore _).prodMk (hprofile _)), Function.comp_apply, pairMap, Y,
      score, hγscore] using! hπpair0
  have htilt := qmd_lecamThird_euclidean_along_subseq γ 1 zero_le_one
    Y hY η hη (π.map pairMap) hπpair
  have htiltProfile := htilt.map hdec_cont hdec_meas
  have htarget :
      ((((π.map pairMap).withDensity (fun q => ENNReal.ofReal (Real.exp
        (1 * q.2 - (1 ^ 2 / 2) * ‖γ.score‖ ^ 2)))).map Prod.fst).map decProfile) =
      (π.withDensity (fun q =>
        ENNReal.ofReal (Real.exp (q.1 j - ‖γ.score‖ ^ 2 / 2)))).map Prod.snd := by
    rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      π pairMap hpairMap_meas _ (by fun_prop)]
    have hdens :
        ((fun q : EuclideanSpace ℝ (Fin (r + r)) × ℝ => ENNReal.ofReal
          (Real.exp (1 * q.2 - (1 ^ 2 / 2) * ‖γ.score‖ ^ 2))) ∘ pairMap) =
        (fun q : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) =>
          ENNReal.ofReal (Real.exp (q.1 j - ‖γ.score‖ ^ 2 / 2))) := by
      funext q
      simp only [Function.comp_apply, pairMap, one_mul, one_pow]
      congr 2
      ring
    rw [hdens]
    rw [Measure.map_map hdec_meas measurable_fst,
      Measure.map_map (hdec_meas.comp measurable_fst) hpairMap_meas]
    congr 1
    funext q
    exact hdecode q
  rw [← htarget]
  convert htiltProfile using 1
  funext k
  rw [Measure.map_map hdec_meas (hY (η k))]
  congr 1
  · funext X
    exact (hdecode (score (η k) X, profile (η k) X)).symm
  · congr 2
    funext i
    rw [one_mul]

private noncomputable def secondKernelOfJoint {r s : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin s)))
    [IsFiniteMeasure π] :
    Kernel (EuclideanSpace ℝ (Fin r)) (EuclideanSpace ℝ (Fin s)) := by
  letI : IsFiniteMeasure (π.map Prod.swap) := Measure.isFiniteMeasure_map π Prod.swap
  exact ProbabilityTheory.condDistrib Prod.fst Prod.snd (π.map Prod.swap)

/-- Disintegrating the swapped baseline score/profile law turns its coordinate
exponential tilt into the corresponding (possibly singular) Gram-Gaussian
shift followed by one profile kernel. -/
private theorem secondKernelOfJoint_tilt_eq_gaussian_bind {r s : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) (j : Fin r)
    (π : Measure (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin s)))
    [IsProbabilityMeasure π]
    (hπfst : π.map Prod.fst = multivariateGaussian 0 (Matrix.gram ℝ v)) :
    let ej : EuclideanSpace ℝ (Fin r) :=
      WithLp.toLp 2 (Pi.single j (1 : ℝ))
    (π.withDensity (fun q => ENNReal.ofReal
      (Real.exp (q.1 j - ‖v j‖ ^ 2 / 2)))).map Prod.snd =
      (multivariateGaussian
        (((Matrix.toEuclideanCLM (𝕜 := ℝ)) (Matrix.gram ℝ v)) ej)
          (Matrix.gram ℝ v)).bind
        (secondKernelOfJoint π) := by
  classical
  dsimp only
  let S : Matrix (Fin r) (Fin r) ℝ := Matrix.gram ℝ v
  let ej : EuclideanSpace ℝ (Fin r) :=
    WithLp.toLp 2 (Pi.single j (1 : ℝ))
  let f : EuclideanSpace ℝ (Fin r) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (y j - ‖v j‖ ^ 2 / 2))
  have hf : Measurable f := by fun_prop
  have hej_inner (y : EuclideanSpace ℝ (Fin r)) : @inner ℝ _ _ ej y = y j := by
    change @inner ℝ _ _ (EuclideanSpace.single j (1 : ℝ)) y = y j
    simpa using (EuclideanSpace.inner_single_left (𝕜 := ℝ) j (1 : ℝ) y)
  have hej_quad : ej.ofLp ⬝ᵥ S.mulVec ej.ofLp = ‖v j‖ ^ 2 := by
    rw [show ej.ofLp = Pi.single j (1 : ℝ) from rfl,
      Matrix.mulVec_single_one]
    simp only [dotProduct, Matrix.col_apply]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, one_mul]
      change (Matrix.gram ℝ v) j j = _
      rw [Matrix.gram_apply, real_inner_self_eq_norm_sq]
    · intro i _ hij
      rw [Pi.single_eq_of_ne hij, zero_mul]
    · simp
  have hgaussTilt :
      ((multivariateGaussian 0 S).withDensity f) =
        multivariateGaussian (((Matrix.toEuclideanCLM (𝕜 := ℝ)) S) ej) S := by
    have h := ProbabilityTheory.multivariateGaussian_withDensity_exp_shift
      (Matrix.posSemidef_gram ℝ v) ej
    have hf_eq : f = fun y => ENNReal.ofReal (Real.exp
        (@inner ℝ _ _ ej y - ej.ofLp ⬝ᵥ S.mulVec ej.ofLp / 2)) := by
      funext y
      dsimp only [f]
      rw [hej_inner, hej_quad]
    rw [hf_eq]
    simpa only [S] using h
  let swapπ : Measure (EuclideanSpace ℝ (Fin s) ×
      EuclideanSpace ℝ (Fin r)) := π.map Prod.swap
  have hswapMeas : Measurable
      (Prod.swap : (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin s)) → _) :=
    measurable_snd.prodMk measurable_fst
  have hswapSnd : swapπ.map Prod.snd = π.map Prod.fst := by
    dsimp only [swapπ]
    rw [Measure.map_map measurable_snd hswapMeas]
    rfl
  have hswapTilt :
      (swapπ.withDensity (fun q => f q.2)).map Prod.fst =
        (π.withDensity (fun q => f q.1)).map Prod.snd := by
    dsimp only [swapπ]
    change ((π.map Prod.swap).withDensity (f ∘ Prod.snd)).map Prod.fst =
      (π.withDensity (f ∘ Prod.fst)).map Prod.snd
    rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      π Prod.swap hswapMeas _ (hf.comp measurable_snd)]
    rw [Measure.map_map measurable_fst hswapMeas]
    rfl
  haveI : IsFiniteMeasure swapπ := by dsimp only [swapπ]; infer_instance
  let κ : Kernel (EuclideanSpace ℝ (Fin r)) (EuclideanSpace ℝ (Fin s)) :=
    ProbabilityTheory.condDistrib Prod.fst Prod.snd swapπ
  have hbridge := AsymptoticStatistics.Measure.withDensity_bind_condDistrib
    swapπ f hf
  change (π.withDensity (fun q => f q.1)).map Prod.snd =
    (multivariateGaussian (((Matrix.toEuclideanCLM (𝕜 := ℝ)) S) ej) S).bind κ
  calc
    (π.withDensity (fun q => f q.1)).map Prod.snd =
        (swapπ.withDensity (fun q => f q.2)).map Prod.fst := hswapTilt.symm
    _ = ((swapπ.map Prod.snd).withDensity f).bind κ := hbridge.symm
    _ = ((π.map Prod.fst).withDensity f).bind κ := by rw [hswapSnd]
    _ = ((multivariateGaussian 0 S).withDensity f).bind κ := by rw [hπfst]
    _ = (multivariateGaussian (((Matrix.toEuclideanCLM (𝕜 := ℝ)) S) ej) S).bind κ := by
      rw [hgaussTilt]

/-- The derivative on the closed nondominated tangent space has a vector
Riesz representer.  This also covers the rank-zero and `d = 0` cases. -/
private theorem exists_nondominatedEIFVec {d : ℕ}
    (C : NondominatedTangentCone P)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ) :
    ∃ φ : Fin d → ↥(L2ZeroMean P),
      IsEfficientInfluenceFunction_vec hpd.derivative φ := by
  classical
  haveI : IsUniformAddGroup ↥(L2ZeroMean P) :=
    (L2ZeroMean P).toAddSubgroup.isUniformAddGroup
  have hclosed : IsClosed
      (tangentSpace C : Set ↥(L2ZeroMean P)) := by
    rw [tangentSpace]
    exact Submodule.isClosed_topologicalClosure _
  have hcompleteL2 : CompleteSpace ↥(L2ZeroMean P) :=
    (L2ZeroMean_isClosed P).completeSpace_coe
  have hcompleteT : CompleteSpace ↥(tangentSpace C) :=
    @IsClosed.completeSpace_coe _ _ hcompleteL2 _ hclosed
  let hIP : InnerProductSpace ℝ ↥(tangentSpace C) :=
    Submodule.innerProductSpace (tangentSpace C)
  letI : InnerProductSpace ℝ ↥(tangentSpace C) := hIP
  let di : Fin d → (↥(tangentSpace C) →L[ℝ] ℝ) := fun i =>
    EuclideanSpace.proj i ∘L hpd.derivative
  let q : Fin d → ↥(tangentSpace C) := fun i =>
    (@InnerProductSpace.toDual ℝ ↥(tangentSpace C) _ _ hIP hcompleteT).symm (di i)
  have hq (i : Fin d) (g : ↥(tangentSpace C)) :
      di i g = ⟪q i, g⟫_ℝ := by
    have hsym :
        (@InnerProductSpace.toDual ℝ ↥(tangentSpace C) _ _ hIP hcompleteT) (q i) =
          di i :=
      LinearIsometryEquiv.apply_symm_apply _ _
    calc
      di i g =
          (@InnerProductSpace.toDual ℝ ↥(tangentSpace C) _ _ hIP hcompleteT) (q i) g := by
        exact congrArg (fun F : ↥(tangentSpace C) →L[ℝ] ℝ => F g) hsym.symm
      _ = ⟪q i, g⟫_ℝ := rfl
  refine ⟨fun i => (q i : ↥(L2ZeroMean P)), fun i => ?_⟩
  apply AsymptoticStatistics.Core.EIF.eif_of_representation_and_membership
  · intro g
    simpa only [di] using! (hq i g).symm
  · exact (q i).property

private noncomputable def firstBlockMatrix (r d : ℕ) :
    Matrix (Fin r) (Fin (r + d)) ℝ := fun i k =>
  if k = Fin.castAdd d i then 1 else 0

private noncomputable def secondBlockMatrix (r d : ℕ) :
    Matrix (Fin d) (Fin (r + d)) ℝ := fun i k =>
  if k = Fin.natAdd r i then 1 else 0

private theorem firstBlockMatrix_apply {r d : ℕ}
    (z : EuclideanSpace ℝ (Fin (r + d))) :
    matrixToEuclideanCLMRect (firstBlockMatrix r d) z =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) z).1 := by
  classical
  ext i
  rw [ofLp_matrixToEuclideanCLMRect]
  simp [firstBlockMatrix, Matrix.mulVec, dotProduct]

private theorem secondBlockMatrix_apply {r d : ℕ}
    (z : EuclideanSpace ℝ (Fin (r + d))) :
    matrixToEuclideanCLMRect (secondBlockMatrix r d) z =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) z).2 := by
  classical
  ext i
  rw [ofLp_matrixToEuclideanCLMRect]
  simp [secondBlockMatrix, Matrix.mulVec, dotProduct]

private theorem firstBlockMatrix_gram {r d : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) (φ : Fin d → ↥(L2ZeroMean P)) :
    firstBlockMatrix r d * Matrix.gram ℝ (Fin.addCases v φ) *
        (firstBlockMatrix r d).transpose = Matrix.gram ℝ v := by
  classical
  ext i i'
  simp [Matrix.mul_apply, firstBlockMatrix, Matrix.gram_apply]

private theorem secondBlockMatrix_gram {r d : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) (φ : Fin d → ↥(L2ZeroMean P)) :
    secondBlockMatrix r d * Matrix.gram ℝ (Fin.addCases v φ) *
        (secondBlockMatrix r d).transpose = Matrix.gram ℝ φ := by
  classical
  ext i i'
  simp [Matrix.mul_apply, secondBlockMatrix, Matrix.gram_apply]

private theorem secondBlockMatrix_jointShift {r d : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) (φ : Fin d → ↥(L2ZeroMean P))
    (j : Fin r) :
    matrixToEuclideanCLMRect (secondBlockMatrix r d)
        (((Matrix.toEuclideanCLM (𝕜 := ℝ))
            (Matrix.gram ℝ (Fin.addCases v φ)))
          (WithLp.toLp 2 (Pi.single (Fin.castAdd d j) (1 : ℝ)))) =
      WithLp.toLp 2 (fun i => ⟪φ i, v j⟫_ℝ) := by
  classical
  ext i
  rw [ofLp_matrixToEuclideanCLMRect, Matrix.toEuclideanCLM_toLp]
  rw [Matrix.mulVec_single]
  simp only [MulOpposite.op_one, one_smul, Submodule.coe_inner]
  simp only [Matrix.mulVec, dotProduct, secondBlockMatrix, Matrix.col_apply,
    Matrix.gram_apply]
  rw [Finset.sum_eq_single (Fin.natAdd r i)]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

/-- The Gram Gaussian of the concatenated raw-score/EIF tuple has the
expected raw marginal, and an exponential tilt in a raw coordinate shifts
the EIF marginal by the raw--EIF cross covariance.  No inverse covariance is
used, so the statement includes singular matrices and zero dimensions. -/
private theorem jointGramGaussian_fst_and_tilt_snd {r d : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) (φ : Fin d → ↥(L2ZeroMean P))
    (j : Fin r) :
    let G := Matrix.gram ℝ (Fin.addCases v φ)
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ)
    let π := (multivariateGaussian 0 G).map split
    π.map Prod.fst = multivariateGaussian 0 (Matrix.gram ℝ v) ∧
      (π.withDensity (fun q => ENNReal.ofReal
        (Real.exp (q.1 j - ‖v j‖ ^ 2 / 2)))).map Prod.snd =
        multivariateGaussian (WithLp.toLp 2 (fun i => ⟪φ i, v j⟫_ℝ))
          (Matrix.gram ℝ φ) := by
  classical
  dsimp only
  let w : Fin (r + d) → ↥(L2ZeroMean P) := Fin.addCases v φ
  let G : Matrix (Fin (r + d)) (Fin (r + d)) ℝ := Matrix.gram ℝ w
  let split : EuclideanSpace ℝ (Fin (r + d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin d) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ)
  let π : Measure (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin d)) :=
    (multivariateGaussian 0 G).map split
  let f : (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin d)) → ℝ≥0∞ :=
    fun q => ENNReal.ofReal (Real.exp (q.1 j - ‖v j‖ ^ 2 / 2))
  let ej : EuclideanSpace ℝ (Fin (r + d)) :=
    WithLp.toLp 2 (Pi.single (Fin.castAdd d j) (1 : ℝ))
  have hG : G.PosSemidef := by
    exact Matrix.posSemidef_gram ℝ w
  have hsplit : Measurable split :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ)).continuous.measurable
  have hf : Measurable f := by fun_prop
  have hfirstFun : Prod.fst ∘ split =
      matrixToEuclideanCLMRect (firstBlockMatrix r d) := by
    funext z
    exact (firstBlockMatrix_apply z).symm
  have hsecondFun : Prod.snd ∘ split =
      matrixToEuclideanCLMRect (secondBlockMatrix r d) := by
    funext z
    exact (secondBlockMatrix_apply z).symm
  have hfst : π.map Prod.fst =
      multivariateGaussian 0 (Matrix.gram ℝ v) := by
    dsimp only [π]
    rw [Measure.map_map measurable_fst hsplit, hfirstFun,
      multivariateGaussian_map_rectangular (firstBlockMatrix r d) 0 hG,
      (matrixToEuclideanCLMRect (firstBlockMatrix r d)).map_zero,
      firstBlockMatrix_gram v φ]
  have hej_inner (z : EuclideanSpace ℝ (Fin (r + d))) :
      @inner ℝ _ _ ej z = (split z).1 j := by
    change @inner ℝ _ _ (EuclideanSpace.single (Fin.castAdd d j) (1 : ℝ)) z = _
    calc
      @inner ℝ _ _ (EuclideanSpace.single (Fin.castAdd d j) (1 : ℝ)) z =
          z (Fin.castAdd d j) := by
        simpa using (EuclideanSpace.inner_single_left (𝕜 := ℝ)
          (Fin.castAdd d j) (1 : ℝ) z)
      _ = (split z).1 j := by simp [split]
  have hej_quad : ej.ofLp ⬝ᵥ G.mulVec ej.ofLp = ‖v j‖ ^ 2 := by
    rw [show ej.ofLp = Pi.single (Fin.castAdd d j) (1 : ℝ) from rfl,
      Matrix.mulVec_single_one]
    simp only [dotProduct, Matrix.col_apply]
    rw [Finset.sum_eq_single (Fin.castAdd d j)]
    · rw [Pi.single_eq_same, one_mul]
      change (Matrix.gram ℝ w) (Fin.castAdd d j) (Fin.castAdd d j) = _
      simp only [Matrix.gram_apply, w, Fin.addCases_left]
      rw [real_inner_self_eq_norm_sq]
    · intro k _ hk
      rw [Pi.single_eq_of_ne hk, zero_mul]
    · simp
  have hpull : f ∘ split = fun z => ENNReal.ofReal (Real.exp
      (@inner ℝ _ _ ej z - ej.ofLp ⬝ᵥ G.mulVec ej.ofLp / 2)) := by
    funext z
    dsimp only [Function.comp_apply, f]
    rw [hej_inner, hej_quad]
  have htiltJoint : (multivariateGaussian 0 G).withDensity (f ∘ split) =
      multivariateGaussian
        (((Matrix.toEuclideanCLM (𝕜 := ℝ)) G) ej) G := by
    rw [hpull]
    exact multivariateGaussian_withDensity_exp_shift hG ej
  have hsnd : (π.withDensity f).map Prod.snd =
      multivariateGaussian (WithLp.toLp 2 (fun i => ⟪φ i, v j⟫_ℝ))
        (Matrix.gram ℝ φ) := by
    dsimp only [π]
    rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity
      (multivariateGaussian 0 G) split hsplit f hf]
    rw [Measure.map_map measurable_snd hsplit, hsecondFun, htiltJoint,
      multivariateGaussian_map_rectangular (secondBlockMatrix r d)
        (((Matrix.toEuclideanCLM (𝕜 := ℝ)) G) ej) hG]
    rw [show matrixToEuclideanCLMRect (secondBlockMatrix r d)
          (((Matrix.toEuclideanCLM (𝕜 := ℝ)) G) ej) =
        WithLp.toLp 2 (fun i => ⟪φ i, v j⟫_ℝ) by
          simpa only [G, w] using secondBlockMatrix_jointShift v φ j,
      show secondBlockMatrix r d * G * (secondBlockMatrix r d).transpose =
          Matrix.gram ℝ φ by
        simpa only [G, w] using secondBlockMatrix_gram v φ]
  exact ⟨hfst, hsnd⟩

private theorem rawGaussian_bind_eifKernel {r d : ℕ}
    (v : Fin r → ↥(L2ZeroMean P)) (φ : Fin d → ↥(L2ZeroMean P))
    (j : Fin r) :
    let G := Matrix.gram ℝ (Fin.addCases v φ)
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ)
    let π := (multivariateGaussian 0 G).map split
    (multivariateGaussian
        (((Matrix.toEuclideanCLM (𝕜 := ℝ)) (Matrix.gram ℝ v))
          (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        (Matrix.gram ℝ v)).bind (secondKernelOfJoint π) =
      multivariateGaussian (WithLp.toLp 2 (fun i => ⟪φ i, v j⟫_ℝ))
        (Matrix.gram ℝ φ) := by
  classical
  dsimp only
  let G : Matrix (Fin (r + d)) (Fin (r + d)) ℝ :=
    Matrix.gram ℝ (Fin.addCases v φ)
  let split : EuclideanSpace ℝ (Fin (r + d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin d) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ)
  let π : Measure (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin d)) :=
    (multivariateGaussian 0 G).map split
  letI : IsProbabilityMeasure π := by
    dsimp only [π]
    exact Measure.isProbabilityMeasure_map split.continuous.measurable.aemeasurable
  have hjoint := jointGramGaussian_fst_and_tilt_snd v φ j
  have hbridge := secondKernelOfJoint_tilt_eq_gaussian_bind v j π hjoint.1
  calc
    _ = (π.withDensity (fun q => ENNReal.ofReal
          (Real.exp (q.1 j - ‖v j‖ ^ 2 / 2)))).map Prod.snd := hbridge.symm
    _ = multivariateGaussian (WithLp.toLp 2 (fun i => ⟪φ i, v j⟫_ℝ))
          (Matrix.gram ℝ φ) := hjoint.2

private theorem centered_multivariateGaussian_lintegral {d : ℕ}
    (c : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hℓ : Measurable ℓ) :
    (∫⁻ a, ℓ (a - c) ∂(multivariateGaussian c S)) =
      ∫⁻ y, ℓ y ∂(multivariateGaussian 0 S) := by
  have hmap : (multivariateGaussian 0 S).map (fun y => c + y) =
      multivariateGaussian c S := by
    unfold multivariateGaussian
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext x
    simp only [Function.comp_apply, zero_add]
  have hshiftMeas : Measurable
      (fun a : EuclideanSpace ℝ (Fin d) => ℓ (a - c)) := by fun_prop
  have haddMeas : Measurable
      (fun y : EuclideanSpace ℝ (Fin d) => c + y) := by fun_prop
  rw [← hmap, lintegral_map hshiftMeas haddMeas]
  simp

set_option maxHeartbeats 800000 in
-- The nested finite-experiment `iSup`/`iInf` term and dependent carrier
-- equivalence require a larger elaboration budget.
/-- Every finite raw-score experiment is a randomization of the Gaussian EIF
experiment.  Consequently its minimax risk is at most the centered EIF risk.
The empty carrier is discharged separately. -/
private theorem finiteCarrierBenchmark_le_eifRisk {d : ℕ}
    (C : NondominatedTangentCone P)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (φ : Fin d → ↥(L2ZeroMean P))
    (hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (hℓ : Measurable ℓ) :
    (⨆ I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
      ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ g ∈ I, ∫⁻ a, ℓ (a -
            hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
          ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
            (finiteCarrierScoreCovariance C I)).bind κ.1)) ≤
      ∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
  classical
  apply iSup_le
  intro I
  by_cases hI : I = ∅
  · subst I
    let κ0Kernel : Kernel (EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin d)) :=
      Kernel.deterministic (fun _ => 0) measurable_const
    letI : IsMarkovKernel κ0Kernel := by dsimp only [κ0Kernel]; infer_instance
    let κ0 : MarkovDecision (EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin d)) := ⟨κ0Kernel, inferInstance⟩
    refine (iInf_le (fun κ : MarkovDecision (EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin d)) =>
          ⨆ g ∈ (∅ : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier}),
            ∫⁻ a, ℓ (a - hpd.derivative
              ⟨g, selected_mem_tangentSpace C g⟩)
              ∂((multivariateGaussian (finiteCarrierScoreMean C ∅ g)
                (finiteCarrierScoreCovariance C ∅)).bind κ.1)) κ0).trans ?_
    simp
  have hcard : 0 < I.card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
  letI : Nonempty (Fin I.card) := Fin.pos_iff_nonempty.mp hcard
  let v : Fin I.card → ↥(L2ZeroMean P) := fun j =>
    (((I.equivFin).symm j).1 : ↥(L2ZeroMean P))
  let G : Matrix (Fin (I.card + d)) (Fin (I.card + d)) ℝ :=
    Matrix.gram ℝ (Fin.addCases v φ)
  let split : EuclideanSpace ℝ (Fin (I.card + d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin I.card) × EuclideanSpace ℝ (Fin d) :=
    EuclideanSpace.finAddEquivProd (𝕜 := ℝ)
  let π : Measure (EuclideanSpace ℝ (Fin I.card) ×
      EuclideanSpace ℝ (Fin d)) := (multivariateGaussian 0 G).map split
  letI : IsProbabilityMeasure π := by
    dsimp only [π]
    exact Measure.isProbabilityMeasure_map split.continuous.measurable.aemeasurable
  have hκMarkov : IsMarkovKernel (secondKernelOfJoint π) := by
    change IsMarkovKernel
      (ProbabilityTheory.condDistrib Prod.fst Prod.snd (π.map Prod.swap))
    letI : IsFiniteMeasure (π.map Prod.swap) :=
      Measure.isFiniteMeasure_map π Prod.swap
    infer_instance
  let κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
      (EuclideanSpace ℝ (Fin d)) := ⟨secondKernelOfJoint π, hκMarkov⟩
  refine (iInf_le (fun κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
      (EuclideanSpace ℝ (Fin d)) =>
        ⨆ g ∈ I, ∫⁻ a, ℓ (a -
          hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
          ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
            (finiteCarrierScoreCovariance C I)).bind κ.1)) κ).trans ?_
  apply iSup_le
  intro g
  apply iSup_le
  intro hg
  let j : Fin I.card := I.equivFin ⟨g, hg⟩
  have hj : (I.equivFin).symm j = ⟨g, hg⟩ :=
    I.equivFin.symm_apply_apply ⟨g, hg⟩
  have hcenter : WithLp.toLp 2 (fun i => ⟪φ i, v j⟫_ℝ) =
      hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩ := by
    ext i
    have hi := (hEIF i).1 ⟨g, selected_mem_tangentSpace C g⟩
    change ⟪φ i, (g : ↥(L2ZeroMean P))⟫_ℝ =
      (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩) i at hi
    simpa only [v, j, hj] using hi
  have hbind :
      (multivariateGaussian (finiteCarrierScoreMean C I g)
        (finiteCarrierScoreCovariance C I)).bind κ.1 =
        multivariateGaussian
          (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
          (Matrix.gram ℝ φ) := by
    have hraw := rawGaussian_bind_eifKernel v φ j
    have hmean := finiteCarrierScoreMean_selected_eq (C := C) I j
    have hcarrier : ((I.equivFin).symm j).1 = g := by
      exact congrArg Subtype.val hj
    have htangent :
        (⟨((I.equivFin).symm j).1,
            selected_mem_tangentSpace C ((I.equivFin).symm j)⟩ : tangentSpace C) =
          ⟨g, selected_mem_tangentSpace C g⟩ := by
      exact Subtype.ext (congrArg
        (fun x : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} =>
          (x : ↥(L2ZeroMean P))) hcarrier)
    dsimp only [κ]
    rw [← hcarrier, hmean]
    change (multivariateGaussian
        (((Matrix.toEuclideanCLM (𝕜 := ℝ)) (Matrix.gram ℝ v))
          (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        (Matrix.gram ℝ v)).bind (secondKernelOfJoint π) = _
    dsimp only [π, G, split]
    rw [hraw, hcenter, htangent]
  rw [hbind]
  exact (centered_multivariateGaussian_lintegral
    (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
    (Matrix.gram ℝ φ) ℓ hℓ).le

/-- On laws supported by the compact closure of genuine bounded loss profiles,
weak convergence also tests the (a priori unbounded) coordinate projection. -/
private theorem finiteLossProfile_coordinate_integral_tendsto {d r : ℕ}
    (center : Fin r → EuclideanSpace ℝ (Fin d))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hfinite : ∀ x, ℓ x ≠ ∞)
    (hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (μn : ℕ → Measure (EuclideanSpace ℝ (Fin r)))
    (μ : Measure (EuclideanSpace ℝ (Fin r)))
    [∀ n, IsProbabilityMeasure (μn n)] [IsProbabilityMeasure μ]
    (hweak : WeakConverges μn μ)
    (hsuppn : ∀ n, μn n
      (closure (Set.range
        (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ))) = 1)
    (hsupp : μ
      (closure (Set.range
        (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ))) = 1)
    (j : Fin r) :
    Tendsto (fun n => ∫ z, z j ∂(μn n)) atTop (nhds (∫ z, z j ∂μ)) := by
  classical
  let profile := Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ
  obtain ⟨B, hBtop, hB⟩ := hbdd
  have hBreal : ∀ x, (ℓ x).toReal ≤ B.toReal := fun x =>
    (ENNReal.toReal_le_toReal (hfinite x) hBtop.ne).2 (hB x)
  have hrange : Set.range profile ⊆
      {z : EuclideanSpace ℝ (Fin r) | 0 ≤ z j ∧ z j ≤ B.toReal} := by
    rintro _ ⟨a, rfl⟩
    exact ⟨ENNReal.toReal_nonneg, hBreal _⟩
  have hclosed : IsClosed
      {z : EuclideanSpace ℝ (Fin r) | 0 ≤ z j ∧ z j ≤ B.toReal} :=
    (isClosed_le continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin r => ℝ) j)).inter
      (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin r => ℝ) j)
        continuous_const)
  have hclosure : closure (Set.range profile) ⊆
      {z : EuclideanSpace ℝ (Fin r) | 0 ≤ z j ∧ z j ≤ B.toReal} :=
    closure_minimal hrange hclosed
  let clip : BoundedContinuousFunction (EuclideanSpace ℝ (Fin r)) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z => min (max (z j) 0) B.toReal)
      (((PiLp.continuous_apply 2 (fun _ : Fin r => ℝ) j).max
        continuous_const).min continuous_const)
      B.toReal
      (fun z => by
        rw [Real.norm_eq_abs]
        have hz0 : 0 ≤ min (max (z j) 0) B.toReal :=
          le_min (le_max_right _ _) ENNReal.toReal_nonneg
        rw [abs_of_nonneg hz0]
        exact min_le_right _ _)
  have hclip (z : EuclideanSpace ℝ (Fin r))
      (hz : z ∈ closure (Set.range profile)) : clip z = z j := by
    have hz' := hclosure hz
    change min (max (z j) 0) B.toReal = z j
    rw [max_eq_left hz'.1, min_eq_left hz'.2]
  have hleft (n : ℕ) : ∫ z, z j ∂(μn n) = ∫ z, clip z ∂(μn n) := by
    apply integral_congr_ae
    have hae : ∀ᵐ z ∂(μn n), z ∈ closure (Set.range profile) := by
      apply (ae_mem_iff_measure_eq isClosed_closure.measurableSet.nullMeasurableSet).2
      simpa only [profile, measure_univ] using hsuppn n
    filter_upwards [hae] with z hz
    exact (hclip z hz).symm
  have hright : ∫ z, z j ∂μ = ∫ z, clip z ∂μ := by
    apply integral_congr_ae
    have hae : ∀ᵐ z ∂μ, z ∈ closure (Set.range profile) := by
      apply (ae_mem_iff_measure_eq isClosed_closure.measurableSet.nullMeasurableSet).2
      simpa only [profile, measure_univ] using hsupp
    filter_upwards [hae] with z hz
    exact (hclip z hz).symm
  simpa only [hleft, hright] using hweak clip

/-- A finite bounded loss can be moved exactly between its ENNReal lintegral
and the real integral of its `toReal` representative. -/
private theorem lintegral_loss_eq_ofReal_integral {d : ℕ}
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hfinite : ∀ x, ℓ x ≠ ∞)
    (hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (huc : UniformContinuous fun x => (ℓ x).toReal)
    (c : EuclideanSpace ℝ (Fin d))
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    (∫⁻ a, ℓ (a - c) ∂μ) = ENNReal.ofReal (∫ a, (ℓ (a - c)).toReal ∂μ) := by
  obtain ⟨B, hBtop, hB⟩ := hbdd
  have hint : Integrable (fun a => (ℓ (a - c)).toReal) μ := by
    refine Integrable.of_bound
      ((huc.continuous.measurable.comp
        (measurable_id.sub measurable_const)).aestronglyMeasurable) B.toReal ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_le_toReal (hfinite _) hBtop.ne).2 (hB _)
  calc
    (∫⁻ a, ℓ (a - c) ∂μ) =
        ∫⁻ a, ENNReal.ofReal ((ℓ (a - c)).toReal) ∂μ := by
      apply lintegral_congr
      intro a
      exact (ENNReal.ofReal_toReal (hfinite _)).symm
    _ = ENNReal.ofReal (∫ a, (ℓ (a - c)).toReal ∂μ) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm

private theorem closed_support_eq_one_of_weakConverges
    {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
    (μn : ℕ → Measure X) (μ : Measure X)
    [∀ n, IsProbabilityMeasure (μn n)] [IsProbabilityMeasure μ]
    (hweak : WeakConverges μn μ) (F : Set X) (hF : IsClosed F)
    (hsupp : ∀ n, μn n F = 1) : μ F = 1 := by
  let Pn : ℕ → ProbabilityMeasure X := fun n => ⟨μn n, inferInstance⟩
  let Pμ : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  have htend : Tendsto Pn atTop (nhds Pμ) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    simpa only [Pn, Pμ] using! hweak
  have hclosed := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    htend hF
  have hlimsup : limsup (fun n => ((Pn n : ProbabilityMeasure X) : Measure X) F)
      atTop = 1 := by
    simp [Pn, hsupp]
  have hone : (1 : ℝ≥0∞) ≤ μ F := by
    simpa only [Pμ, hlimsup] using! hclosed
  have hle : μ F ≤ μ Set.univ := measure_mono (Set.subset_univ F)
  rw [measure_univ] at hle
  exact le_antisymm hle hone

/-- Uniform continuity makes deterministic center perturbations negligible in
expectation, uniformly over an arbitrary varying sequence of probability laws. -/
private theorem integral_loss_center_difference_tendsto_zero {d : ℕ}
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hfinite : ∀ x, ℓ x ≠ ∞)
    (hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (huc : UniformContinuous fun x => (ℓ x).toReal)
    (c : ℕ → EuclideanSpace ℝ (Fin d)) (c₀ : EuclideanSpace ℝ (Fin d))
    (hc : Tendsto c atTop (nhds c₀))
    (μn : ℕ → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ n, IsProbabilityMeasure (μn n)] :
    Tendsto (fun n =>
      (∫ a, (ℓ (a - c n)).toReal ∂(μn n)) -
        ∫ a, (ℓ (a - c₀)).toReal ∂(μn n)) atTop (nhds 0) := by
  obtain ⟨B, hBtop, hB⟩ := hbdd
  have hint (n : ℕ) (q : EuclideanSpace ℝ (Fin d)) :
      Integrable (fun a => (ℓ (a - q)).toReal) (μn n) := by
    refine Integrable.of_bound
      ((huc.continuous.measurable.comp
        (measurable_id.sub measurable_const)).aestronglyMeasurable) B.toReal ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (ENNReal.toReal_le_toReal (hfinite _) hBtop.ne).2 (hB _)
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hmod⟩ := huc (ε / 2) (half_pos hε)
  have hcδ : ∀ᶠ n in atTop, dist (c n) c₀ < δ :=
    (Metric.tendsto_nhds.mp hc) δ hδ
  filter_upwards [hcδ] with n hn
  have hpw : ∀ a : EuclideanSpace ℝ (Fin d),
      dist ((ℓ (a - c n)).toReal) ((ℓ (a - c₀)).toReal) < ε / 2 := by
    intro a
    apply hmod
    have hsub : (a - c n) - (a - c₀) = -(c n - c₀) := by abel
    simpa only [dist_eq_norm, hsub, norm_neg] using hn
  rw [dist_zero_right, Real.norm_eq_abs,
    ← integral_sub (hint n (c n)) (hint n c₀)]
  calc
    |∫ a, (ℓ (a - c n)).toReal - (ℓ (a - c₀)).toReal ∂(μn n)|
        ≤ ∫ _ : EuclideanSpace ℝ (Fin d), ε / 2 ∂(μn n) := by
      change ‖∫ a, (ℓ (a - c n)).toReal - (ℓ (a - c₀)).toReal ∂(μn n)‖ ≤ _
      apply norm_integral_le_of_norm_le (integrable_const (ε / 2))
      exact Filter.Eventually.of_forall fun a => by
        simpa only [Real.norm_eq_abs, Real.dist_eq] using (hpw a).le
    _ = ε / 2 := by simp
    _ < ε := half_lt_self hε

private theorem selectedPath_center_tendsto {d : ℕ}
    (C : NondominatedTangentCone P)
    {psi : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C psi)
    (g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier}) :
    Tendsto (fun n : ℕ => Real.sqrt n •
        (psi ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)) - psi P))
      atTop
      (nhds (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)) := by
  have hinv0 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hinvpos : ∀ᶠ n : ℕ in atTop, 0 < (Real.sqrt n)⁻¹ := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact inv_pos.mpr (Real.sqrt_pos.mpr hnpos)
  have hright : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hinv0, hinvpos⟩
  have hquot := (hpd.derivative_spec g).comp hright
  refine hquot.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hsqrt : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hnpos).ne'
  change ((Real.sqrt n)⁻¹)⁻¹ •
      (psi ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)) - psi P) =
    Real.sqrt n •
      (psi ((C.selectedPath g).curve ((Real.sqrt n)⁻¹)) - psi P)
  rw [inv_inv]

set_option maxHeartbeats 1600000 in
-- The dependent finite-span/basis construction and its minimax comparison
-- elaborate as one large term.
/-- Finite carrier charts exhaust the raw EIF Gram benchmark, including
singular Gram matrices, `d = 0`, and the zero influence tuple.

Proof idea: exhaust the closed linear span by finite carrier-generated
subspaces, identify each finite score experiment, apply the full-span vector
Gaussian-cone minimax theorem after quotienting its null directions, and pass
to the lsc Gaussian limit. -/
theorem finiteCarrierChart_exhausts_eifGram {d : ℕ}
    (C : NondominatedTangentCone P) (_hconv : Convex ℝ C.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    {φ : Fin d → ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction_vec hpd.derivative φ)
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ) :
    (∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ))) ≤
      ⨆ I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
        ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
            (EuclideanSpace ℝ (Fin d)),
          ⨆ g ∈ I, ∫⁻ a, ℓ (a -
              hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
            ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
              (finiteCarrierScoreCovariance C I)).bind κ.1) := by
  classical
  haveI hUG_L2 : IsUniformAddGroup ↥(L2ZeroMean P) :=
    (L2ZeroMean P).toAddSubgroup.isUniformAddGroup
  have hmem : ∀ i : Fin d, φ i ∈ tangentSpace C := fun i => (_hEIF i).2
  have hseq : ∀ i : Fin d,
      ∃ V : ℕ → Submodule ℝ ↥(L2ZeroMean P),
      ∃ p : ℕ → ↥(L2ZeroMean P),
        (∀ m, FiniteDimensional ℝ (V m)) ∧
        (∀ m, ∃ S : Finset ↥(L2ZeroMean P),
          (↑S : Set ↥(L2ZeroMean P)) ⊆ C.carrier ∧
          V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P))) ∧
        (∀ m, p m ∈ V m ∧ φ i - p m ∈ (V m)ᗮ) ∧
        Tendsto (fun m => ‖p m - φ i‖) atTop (nhds 0) := by
    intro i
    obtain ⟨V, p, _hVle, _hVinc, hVfd, hVspan, hproj, htend⟩ :=
      proj_seq_to_eif_nd C (hmem i)
    exact ⟨V, p, hVfd, hVspan, hproj, htend⟩
  choose Vc pc hVcfd hVcspan hVcproj hVctend using hseq
  choose Sc hScsub hSceq using hVcspan
  let S : ℕ → Finset ↥(L2ZeroMean P) := fun m =>
    Finset.univ.biUnion (fun i : Fin d => Sc i m)
  let V : ℕ → Submodule ℝ ↥(L2ZeroMean P) := fun m =>
    Submodule.span ℝ (↑(S m) : Set ↥(L2ZeroMean P))
  have hSsub : ∀ m, (↑(S m) : Set ↥(L2ZeroMean P)) ⊆ C.carrier := by
    intro m x hx
    rw [Finset.mem_coe, Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact hScsub i m hxi
  have hVcle : ∀ i m, Vc i m ≤ V m := by
    intro i m
    rw [hSceq i m]
    refine Submodule.span_mono ?_
    intro x hx
    rw [Finset.mem_coe, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, hx⟩
  have hVfd : ∀ m, FiniteDimensional ℝ (V m) := fun m =>
    FiniteDimensional.span_finset ℝ (S m)
  have hVcomplete : ∀ m, CompleteSpace (V m) := fun m =>
    haveI := hVfd m
    haveI : IsUniformAddGroup ↥(V m) := (V m).toAddSubgroup.isUniformAddGroup
    @FiniteDimensional.complete ℝ ↥(V m) _ _ _ _ _ _ _ _ _
  have hVproj : ∀ m, (V m).HasOrthogonalProjection := fun m =>
    @Submodule.HasOrthogonalProjection.ofCompleteSpace _ _ _ _ _ (V m)
      (hVcomplete m)
  let p : ℕ → Fin d → ↥(L2ZeroMean P) := fun m i =>
    haveI := hVproj m
    (V m).starProjection (φ i)
  have hptend : ∀ i : Fin d,
      Tendsto (fun m => ‖p m i - φ i‖) atTop (nhds 0) := by
    intro i
    refine squeeze_zero (fun _ => norm_nonneg _) ?_ (hVctend i)
    intro m
    haveI := hVproj m
    have hpc : pc i m ∈ V m := hVcle i m (hVcproj i m).1
    rw [norm_sub_rev (p m i), norm_sub_rev (pc i m)]
    rw [show p m i = (V m).starProjection (φ i) from rfl,
      Submodule.starProjection_minimal (φ i)]
    refine ciInf_le ⟨0, ?_⟩ (⟨pc i m, hpc⟩ : V m)
    rintro _ ⟨x, rfl⟩
    exact norm_nonneg _
  let r : ℕ → ℕ := fun m => Module.finrank ℝ ↥(V m)
  let b : ∀ m, OrthonormalBasis (Fin (r m)) ℝ ↥(V m) := fun m =>
    haveI := hVfd m
    stdOrthonormalBasis ℝ ↥(V m)
  let A : ∀ m, Matrix (Fin d) (Fin (r m)) ℝ := fun m i j =>
    ⟪φ i, ((b m j : V m) : ↥(L2ZeroMean P))⟫_ℝ
  have hp_mem : ∀ m i, p m i ∈ V m := by
    intro m i
    haveI := hVproj m
    exact (V m).starProjection_apply_mem (φ i)
  have hSigmaEntry : ∀ m i i',
      (A m * (A m).transpose) i i' = ⟪p m i, p m i'⟫_ℝ := by
    intro m i i'
    haveI := hVfd m
    haveI := hVproj m
    rw [Matrix.mul_apply]
    have hswap : ∀ i0 k,
        ⟪φ i0, ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ =
          ⟪p m i0, ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ := by
      intro i0 k
      have hperp := (V m).sub_starProjection_mem_orthogonal (φ i0)
      have hz := (Submodule.mem_orthogonal _ _).mp hperp (b m k) (b m k).2
      have hz' : ⟪φ i0 - p m i0,
          ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
        rw [real_inner_comm]
        exact hz
      rw [inner_sub_left (𝕜 := ℝ) (φ i0) (p m i0)
        ((b m k : V m) : ↥(L2ZeroMean P))] at hz'
      exact sub_eq_zero.mp hz'
    simp only [Matrix.transpose_apply]
    simp only [A]
    simp_rw [hswap]
    let qi : V m := ⟨p m i, hp_mem m i⟩
    let qj : V m := ⟨p m i', hp_mem m i'⟩
    have hparseval := (b m).sum_inner_mul_inner qi qj
    rw [show
        (∑ k, ⟪p m i, ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ *
          ⟪p m i', ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ) =
        ∑ k, ⟪qi, b m k⟫_ℝ * ⟪b m k, qj⟫_ℝ by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      change ⟪p m i, ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ *
          ⟪p m i', ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ =
        ⟪p m i, ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ *
          ⟪((b m k : V m) : ↥(L2ZeroMean P)), p m i'⟫_ℝ
      rw [real_inner_comm (p m i')]]
    rw [hparseval]
    rfl
  have hSigmaPSD : ∀ m, (A m * (A m).transpose).PosSemidef := by
    intro m
    rw [show (A m).transpose = (A m).conjTranspose from
      (Matrix.conjTranspose_eq_transpose_of_trivial _).symm]
    exact Matrix.posSemidef_self_mul_conjTranspose _
  have hGramPSD : (Matrix.gram ℝ φ).PosSemidef :=
    Matrix.posSemidef_gram ℝ φ
  have hSigmaTend : Tendsto (fun m => A m * (A m).transpose) atTop
      (nhds (Matrix.gram ℝ φ)) := by
    refine tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun i' => ?_))
    rw [show (Matrix.gram ℝ φ) i i' = ⟪φ i, φ i'⟫_ℝ from rfl]
    have hpi : Tendsto (fun m => p m i) atTop (nhds (φ i)) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr (hptend i)
    have hpj : Tendsto (fun m => p m i') atTop (nhds (φ i')) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr (hptend i')
    have hinner : Tendsto (fun m => ⟪p m i, p m i'⟫_ℝ) atTop
        (nhds ⟪φ i, φ i'⟫_ℝ) :=
      continuous_inner.tendsto _ |>.comp (hpi.prodMk_nhds hpj)
    exact hinner.congr' (Filter.Eventually.of_forall fun m => (hSigmaEntry m i i').symm)
  have hperM : ∀ m,
      (∫⁻ y, ℓ y ∂(multivariateGaussian 0 (A m * (A m).transpose))) ≤
        ⨆ I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
          ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
              (EuclideanSpace ℝ (Fin d)),
            ⨆ g ∈ I, ∫⁻ a, ℓ (a -
                hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
              ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
                (finiteCarrierScoreCovariance C I)).bind κ.1) := by
    intro m
    haveI := hVfd m
    let e : ↥(V m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r m)) := (b m).repr
    let scoreOf : EuclideanSpace ℝ (Fin (r m)) →ₗ[ℝ] ↥(L2ZeroMean P) :=
      (V m).subtype.comp e.symm.toLinearEquiv.toLinearMap
    let D : Set (EuclideanSpace ℝ (Fin (r m))) := scoreOf ⁻¹' C.carrier
    have hscoreInj : Function.Injective scoreOf := by
      intro x y hxy
      apply e.symm.injective
      apply Subtype.ext
      exact hxy
    have hD0 : (0 : EuclideanSpace ℝ (Fin (r m))) ∈ D := by
      change scoreOf 0 ∈ C.carrier
      rw [map_zero]
      exact zero_mem C
    have hDconv : Convex ℝ D := _hconv.linear_preimage scoreOf
    have hDcone : ∀ x ∈ D, ∀ t : ℝ, 0 ≤ t → t • x ∈ D := by
      intro x hx t ht
      change scoreOf (t • x) ∈ C.carrier
      rw [map_smul]
      exact C.nonneg_smul_mem ht hx
    have hDspan : Submodule.span ℝ D = ⊤ := by
      rw [eq_top_iff]
      intro h _
      have hv : ((e.symm h : V m) : ↥(L2ZeroMean P)) ∈
          Submodule.span ℝ (↑(S m) : Set ↥(L2ZeroMean P)) := (e.symm h).2
      let q : ∀ x : ↥(L2ZeroMean P),
          x ∈ Submodule.span ℝ (↑(S m) : Set ↥(L2ZeroMean P)) →
            EuclideanSpace ℝ (Fin (r m)) := fun x hx => e ⟨x, hx⟩
      have hq : q ((e.symm h : V m) : ↥(L2ZeroMean P)) hv ∈
          Submodule.span ℝ D := by
        refine Submodule.span_induction (p := fun x hx => q x hx ∈ Submodule.span ℝ D)
          ?_ ?_ ?_ ?_ hv
        · intro x hx
          apply Submodule.subset_span
          change scoreOf (q x (Submodule.subset_span hx)) ∈ C.carrier
          change ((e.symm (e ⟨x, Submodule.subset_span hx⟩) : V m) :
            ↥(L2ZeroMean P)) ∈ C.carrier
          rw [e.symm_apply_apply]
          exact hSsub m hx
        · change e (0 : V m) ∈ Submodule.span ℝ D
          rw [e.map_zero]
          exact (Submodule.span ℝ D).zero_mem
        · intro x y hx hy hx' hy'
          change e (⟨x + y, Submodule.add_mem _ hx hy⟩ : V m) ∈
            Submodule.span ℝ D
          rw [show (⟨x + y, Submodule.add_mem _ hx hy⟩ : V m) =
            (⟨x, hx⟩ : V m) + ⟨y, hy⟩ by rfl, map_add]
          exact (Submodule.span ℝ D).add_mem hx' hy'
        · intro t x hx hx'
          change e (⟨t • x, Submodule.smul_mem _ t hx⟩ : V m) ∈
            Submodule.span ℝ D
          rw [show (⟨t • x, Submodule.smul_mem _ t hx⟩ : V m) =
            t • (⟨x, hx⟩ : V m) by rfl, map_smul]
          exact (Submodule.span ℝ D).smul_mem t hx'
      simpa only [q, e.apply_symm_apply] using hq
    have hG6 := gaussianCone_minimax_vec_fullSpan D hD0 hDconv hDcone hDspan
      (A m) ℓ _hbowl _hlsc
    exact hG6.trans (by
      apply iSup_le
      intro J
      let carrierEmb : {h // h ∈ (J : Finset (EuclideanSpace ℝ (Fin (r m))))} ↪
          {g : ↥(L2ZeroMean P) // g ∈ C.carrier} :=
        { toFun := fun h => ⟨scoreOf h, J.property h.property⟩
          inj' := by
            intro x y hxy
            apply Subtype.ext
            apply hscoreInj
            exact congrArg (fun z : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} =>
              (z : ↥(L2ZeroMean P))) hxy }
      let I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier} :=
        J.1.attach.map carrierEmb
      have hImem : ∀ h (hh : h ∈ (J : Finset _)),
          carrierEmb ⟨h, hh⟩ ∈ I := by
        intro h hh
        exact Finset.mem_map.mpr ⟨⟨h, hh⟩, Finset.mem_attach _ _, rfl⟩
      have hIV : ∀ g ∈ I, (g : ↥(L2ZeroMean P)) ∈ V m := by
        intro g hg
        obtain ⟨q, _hq, hqg⟩ := Finset.mem_map.mp hg
        rw [← hqg]
        exact (e.symm (q : EuclideanSpace ℝ (Fin (r m)))).2
      let rawCoord : Fin I.card → EuclideanSpace ℝ (Fin (r m)) := fun j =>
        e ⟨(((I.equivFin).symm j).1 : ↥(L2ZeroMean P)),
          hIV _ ((I.equivFin).symm j).2⟩
      let B : Matrix (Fin I.card) (Fin (r m)) ℝ := fun j k => rawCoord j k
      have hrow : ∀ j,
          scoreOf (rawCoord j) =
            ((((I.equivFin).symm j).1 : ↥(L2ZeroMean P))) := by
        intro j
        change (((e.symm (e ⟨(((I.equivFin).symm j).1 : ↥(L2ZeroMean P)),
          hIV _ ((I.equivFin).symm j).2⟩) : V m) : ↥(L2ZeroMean P))) = _
        rw [e.symm_apply_apply]
      have hBmean : ∀ g (hg : g ∈ I),
          finiteCarrierScoreMean C I g =
            matrixToEuclideanCLMRect B
              (e ⟨(g : ↥(L2ZeroMean P)), hIV g hg⟩) := by
        intro g hg
        ext j
        change ⟪(((I.equivFin).symm j).1 : ↥(L2ZeroMean P)),
            (g : ↥(L2ZeroMean P))⟫_ℝ =
          ∑ k, B j k * (e ⟨(g : ↥(L2ZeroMean P)), hIV g hg⟩) k
        let qj : V m := ⟨(((I.equivFin).symm j).1 : ↥(L2ZeroMean P)),
          hIV _ ((I.equivFin).symm j).2⟩
        let qg : V m := ⟨(g : ↥(L2ZeroMean P)), hIV g hg⟩
        have heinner : ⟪e qj, e qg⟫_ℝ = ⟪qj, qg⟫_ℝ :=
          LinearIsometryEquiv.inner_map_map (𝕜 := ℝ) e qj qg
        rw [PiLp.inner_apply] at heinner
        change ⟪qj, qg⟫_ℝ = ∑ k, (e qj) k * (e qg) k
        rw [← heinner]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        change (e qg) k * (e qj) k = (e qj) k * (e qg) k
        ring
      have hBcov : finiteCarrierScoreCovariance C I = B * B.transpose := by
        ext j j'
        rw [Matrix.mul_apply]
        change ⟪(((I.equivFin).symm j).1 : ↥(L2ZeroMean P)),
            (((I.equivFin).symm j').1 : ↥(L2ZeroMean P))⟫_ℝ =
          ∑ k, B j k * B j' k
        let qj : V m := ⟨(((I.equivFin).symm j).1 : ↥(L2ZeroMean P)),
          hIV _ ((I.equivFin).symm j).2⟩
        let qj' : V m := ⟨(((I.equivFin).symm j').1 : ↥(L2ZeroMean P)),
          hIV _ ((I.equivFin).symm j').2⟩
        have heinner : ⟪e qj, e qj'⟫_ℝ = ⟪qj, qj'⟫_ℝ :=
          LinearIsometryEquiv.inner_map_map (𝕜 := ℝ) e qj qj'
        rw [PiLp.inner_apply] at heinner
        change ⟪qj, qj'⟫_ℝ = ∑ k, (e qj) k * (e qj') k
        rw [← heinner]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        change (e qj') k * (e qj) k = (e qj) k * (e qj') k
        ring
      have hBcenter : ∀ g (hg : g ∈ I),
          hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩ =
            matrixActionVec (A m)
              (e ⟨(g : ↥(L2ZeroMean P)), hIV g hg⟩) := by
        intro g hg
        ext i
        have hEIFi := (_hEIF i).1 ⟨g, selected_mem_tangentSpace C g⟩
        change ⟪φ i, (g : ↥(L2ZeroMean P))⟫_ℝ =
          (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩) i at hEIFi
        change (hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩) i =
          ∑ k, A m i k * (e ⟨(g : ↥(L2ZeroMean P)), hIV g hg⟩) k
        rw [← hEIFi]
        let qg : V m := ⟨(g : ↥(L2ZeroMean P)), hIV g hg⟩
        let qp : V m := ⟨p m i, hp_mem m i⟩
        have hswapg : ⟪φ i, (g : ↥(L2ZeroMean P))⟫_ℝ =
            ⟪p m i, (g : ↥(L2ZeroMean P))⟫_ℝ := by
          have hperp := (V m).sub_starProjection_mem_orthogonal (φ i)
          have hz := (Submodule.mem_orthogonal _ _).mp hperp qg qg.2
          have hz' : ⟪φ i - p m i, (g : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
            rw [real_inner_comm]
            exact hz
          rw [inner_sub_left (𝕜 := ℝ) (φ i) (p m i)
            (g : ↥(L2ZeroMean P))] at hz'
          exact sub_eq_zero.mp hz'
        have hAcoord : ∀ k, A m i k = (e qp) k := by
          intro k
          have hperp := (V m).sub_starProjection_mem_orthogonal (φ i)
          have hz := (Submodule.mem_orthogonal _ _).mp hperp (b m k) (b m k).2
          have hz' : ⟪φ i - p m i,
              ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
            rw [real_inner_comm]
            exact hz
          rw [inner_sub_left (𝕜 := ℝ) (φ i) (p m i)
            ((b m k : V m) : ↥(L2ZeroMean P))] at hz'
          have hswap := sub_eq_zero.mp hz'
          rw [show A m i k =
            ⟪φ i, ((b m k : V m) : ↥(L2ZeroMean P))⟫_ℝ from rfl,
            hswap, (b m).repr_apply_apply qp k, real_inner_comm]
          rfl
        have heinner : ⟪e qp, e qg⟫_ℝ = ⟪qp, qg⟫_ℝ :=
          LinearIsometryEquiv.inner_map_map (𝕜 := ℝ) e qp qg
        rw [PiLp.inner_apply] at heinner
        calc
          ⟪φ i, (g : ↥(L2ZeroMean P))⟫_ℝ =
              ⟪p m i, (g : ↥(L2ZeroMean P))⟫_ℝ := hswapg
          _ = ∑ k, A m i k * (e qg) k := by
            change ⟪qp, qg⟫_ℝ = _
            rw [← heinner]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            change (e qg) k * (e qp) k = A m i k * (e qg) k
            rw [hAcoord]
            ring
      refine le_iSup_of_le I ?_
      refine le_iInf fun κraw => ?_
      let fB : EuclideanSpace ℝ (Fin (r m)) →
          EuclideanSpace ℝ (Fin I.card) := matrixToEuclideanCLMRect B
      have hfB : Measurable fB :=
        (matrixToEuclideanCLMRect B).continuous.measurable
      letI : IsMarkovKernel κraw.1 := κraw.2
      let κstdKernel : Kernel (EuclideanSpace ℝ (Fin (r m)))
          (EuclideanSpace ℝ (Fin d)) := κraw.1.comap fB hfB
      letI : IsMarkovKernel κstdKernel :=
        Kernel.IsMarkovKernel.comap κraw.1 hfB
      let κstd : MarkovDecision (EuclideanSpace ℝ (Fin (r m)))
          (EuclideanSpace ℝ (Fin d)) := ⟨κstdKernel, inferInstance⟩
      refine iInf_le_of_le κstd ?_
      apply iSup_le
      intro h
      apply iSup_le
      intro hh
      let g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier} :=
        carrierEmb ⟨h, hh⟩
      have hgI : g ∈ I := hImem h hh
      have hcoord : e ⟨(g : ↥(L2ZeroMean P)), hIV g hgI⟩ = h := by
        change e (e.symm h) = h
        exact e.apply_symm_apply h
      have hgauss :
          (multivariateGaussian h (1 : Matrix (Fin (r m)) (Fin (r m)) ℝ)).map fB =
            multivariateGaussian (finiteCarrierScoreMean C I g)
              (finiteCarrierScoreCovariance C I) := by
        rw [show fB = matrixToEuclideanCLMRect B from rfl,
          multivariateGaussian_map_rectangular B h Matrix.PosSemidef.one,
          Matrix.mul_one, ← hBcov, hBmean g hgI, hcoord]
      have hbind :
          (multivariateGaussian h (1 : Matrix (Fin (r m)) (Fin (r m)) ℝ)).bind
              κstdKernel =
            (multivariateGaussian (finiteCarrierScoreMean C I g)
              (finiteCarrierScoreCovariance C I)).bind κraw.1 := by
        rw [← hgauss, Measure.bind_map_eq_bind_comap]
      calc
        gaussianShiftKernelRiskVec (A m) ℓ κstd h =
            ∫⁻ a, ℓ (a - hpd.derivative
                ⟨g, selected_mem_tangentSpace C g⟩)
              ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
                (finiteCarrierScoreCovariance C I)).bind κraw.1) := by
          unfold gaussianShiftKernelRiskVec
          rw [hBcenter g hgI, hcoord, hbind]
        _ ≤ ⨆ g ∈ I, ∫⁻ a, ℓ (a -
              hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
            ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
              (finiteCarrierScoreCovariance C I)).bind κraw.1) :=
          le_iSup_of_le g (le_iSup_of_le hgI le_rfl))
  have hlsc :=
    AsymptoticStatistics.multivariateGaussian_lintegral_le_liminf_of_tendsto
      hGramPSD hSigmaPSD hSigmaTend _hlsc
  refine hlsc.trans ?_
  refine Filter.liminf_le_of_le ?_ ?_
  · exact ⟨0, Filter.Eventually.of_forall (fun _ => zero_le)⟩
  · intro q hq
    obtain ⟨m, hm⟩ :=
      (hq.and (Filter.Eventually.of_forall (fun m => hperM m))).exists
    exact hm.1.trans hm.2

set_option maxHeartbeats 1600000 in
-- Simultaneous finite loss-profile compactification and rounding elaborate as
-- one large dependent term over the carrier chart.
private theorem gaussianConeKernelRisk_le_selectedPathCanonicalLHSVec_bounded {d : ℕ}
    (C : NondominatedTangentCone P)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (hT : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (hfinite : ∀ x, ℓ x ≠ ∞)
    (hbdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, ℓ x ≤ B)
    (huc : UniformContinuous fun x => (ℓ x).toReal) :
    (⨆ I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
      ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ g ∈ I, ∫⁻ a, ℓ (a -
            hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
          ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
            (finiteCarrierScoreCovariance C I)).bind κ.1)) ≤
      selectedPathCanonicalLHSVec C T_n ψ ℓ := by
  classical
  unfold selectedPathCanonicalLHSVec
  apply iSup_le
  intro I
  refine le_iSup_of_le I ?_
  by_cases hI : I = ∅
  · subst I
    let κ0Kernel : Kernel (EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin d)) :=
      Kernel.deterministic (fun _ => 0) measurable_const
    letI : IsMarkovKernel κ0Kernel := by dsimp only [κ0Kernel]; infer_instance
    let κ0 : MarkovDecision (EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin d)) := ⟨κ0Kernel, inferInstance⟩
    calc
      (⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin 0))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ g ∈ (∅ : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier}),
          ∫⁻ a, ℓ (a - hpd.derivative
            ⟨g, selected_mem_tangentSpace C g⟩)
            ∂((multivariateGaussian (finiteCarrierScoreMean C ∅ g)
              (finiteCarrierScoreCovariance C ∅)).bind κ.1))
          ≤ ⨆ g ∈ (∅ : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier}),
          ∫⁻ a, ℓ (a - hpd.derivative
            ⟨g, selected_mem_tangentSpace C g⟩)
            ∂((multivariateGaussian (finiteCarrierScoreMean C ∅ g)
              (finiteCarrierScoreCovariance C ∅)).bind κ0.1) := iInf_le _ κ0
      _ = 0 := by
        apply le_antisymm
        · apply iSup_le
          intro g
          apply iSup_le
          intro hg
          simp at hg
        · exact bot_le
      _ = liminf (fun n =>
          (∅ : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier}).sup fun g =>
            ∫⁻ X : Fin n → Ω, ℓ (Real.sqrt n • (T_n n X -
              ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))
              ∂(Measure.pi fun _ : Fin n =>
                (C.selectedPath g).curve ((Real.sqrt n)⁻¹))) atTop := by
        simp only [Finset.sup_empty, Filter.liminf_const, ENNReal.bot_eq_zero]
  have hcard : 0 < I.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
  letI : Nonempty (Fin I.card) := Fin.pos_iff_nonempty.mp hcard
  let v : Fin I.card → ↥(L2ZeroMean P) := fun j =>
    (((I.equivFin).symm j).1 : ↥(L2ZeroMean P))
  let center : Fin I.card → EuclideanSpace ℝ (Fin d) := fun j =>
    hpd.derivative ⟨(I.equivFin).symm j,
      selected_mem_tangentSpace C ((I.equivFin).symm j)⟩
  let action : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) := fun n X =>
    Real.sqrt n • (T_n n X - ψ P)
  let profile : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin I.card) := fun n X =>
    Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ (action n X)
  have haction : ∀ n, Measurable (action n) := fun n =>
    (hT n).sub_const (ψ P) |>.const_smul (Real.sqrt n)
  have hprofile : ∀ n, Measurable (profile n) := fun n =>
    (Experiment.FiniteRiskCompactification.finiteLossProfile_uniform_center
      center ℓ hfinite hbdd huc).1.continuous.measurable.comp (haction n)
  let u : ℕ → ℝ≥0∞ := fun n => I.sup (fun g =>
    ∫⁻ X : Fin n → Ω, ℓ (Real.sqrt n • (T_n n X -
        ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))
      ∂(Measure.pi (fun _ : Fin n =>
        (C.selectedPath g).curve ((Real.sqrt n)⁻¹))))
  obtain ⟨χ, hχ, hχlim⟩ :=
    AsymptoticStatistics.Prohorov.exists_strictMono_tendsto_liminf_ennreal u
  obtain ⟨τ, hτ, π, hπprob, hπweak, hπfst, hπsupp⟩ :=
    finiteScoreProfile_joint_subsequence v action haction center ℓ
      hfinite hbdd huc χ hχ
  letI : IsProbabilityMeasure π := hπprob
  let η : ℕ → ℕ := χ ∘ τ
  have hη : StrictMono η := hχ.comp hτ
  have hηlim : Tendsto (u ∘ η) atTop (nhds (liminf u atTop)) := by
    simpa only [η, Function.comp_assoc] using hχlim.comp hτ.tendsto_atTop
  have hκProfileMarkov : IsMarkovKernel (secondKernelOfJoint π) := by
    change IsMarkovKernel
      (ProbabilityTheory.condDistrib Prod.fst Prod.snd (π.map Prod.swap))
    letI : IsFiniteMeasure (π.map Prod.swap) := Measure.isFiniteMeasure_map π Prod.swap
    infer_instance
  let κProfile : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
      (EuclideanSpace ℝ (Fin I.card)) := ⟨secondKernelOfJoint π, hκProfileMarkov⟩
  let μ : Fin I.card → Measure (EuclideanSpace ℝ (Fin I.card)) := fun j =>
    multivariateGaussian (finiteCarrierScoreMean C I ((I.equivFin).symm j))
      (finiteCarrierScoreCovariance C I)
  let γ : Fin I.card → NondominatedQMDPath P := fun j =>
    C.selectedPath ((I.equivFin).symm j)
  have hcurveProb (j : Fin I.card) (n : ℕ) :
      IsProbabilityMeasure ((γ j).curve ((Real.sqrt n)⁻¹)) := by
    exact (γ j).curve_isProbability _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  let alt : (j : Fin I.card) → (n : ℕ) → Measure (Fin n → Ω) := fun j n =>
    letI := hcurveProb j n
    Measure.pi (fun _ : Fin n => (γ j).curve ((Real.sqrt n)⁻¹))
  letI hAltProb (j : Fin I.card) (n : ℕ) : IsProbabilityMeasure (alt j n) := by
    dsimp only [alt]
    letI := hcurveProb j n
    infer_instance
  have hcov : Matrix.gram ℝ v = finiteCarrierScoreCovariance C I := rfl
  have hγscore (j : Fin I.card) : (γ j).score = v j := by
    exact C.selectedPath_score ((I.equivFin).symm j)
  have hμprob (j : Fin I.card) : IsProbabilityMeasure (μ j) := by
    dsimp only [μ]
    infer_instance
  letI hμprobI (j : Fin I.card) : IsProbabilityMeasure (μ j) := hμprob j
  have hAltWeak (j : Fin I.card) : WeakConverges
      (fun k => (alt j (η k)).map (profile (η k)))
      ((μ j).bind κProfile.1) := by
    have ht := finiteScoreProfile_selected_tilt (γ j) v j (hγscore j)
      profile hprofile η hη π hπweak
    have heq := secondKernelOfJoint_tilt_eq_gaussian_bind v j π hπfst
    rw [hγscore j] at ht
    rw [heq] at ht
    simpa only [alt, μ, κProfile, γ, hcov,
      finiteCarrierScoreMean_selected_eq I j] using ht
  letI hProfileLawProb (j : Fin I.card) (k : ℕ) :
      IsProbabilityMeasure ((alt j (η k)).map (profile (η k))) :=
    Measure.isProbabilityMeasure_map (hprofile (η k)).aemeasurable
  have hpreSupp (j : Fin I.card) (k : ℕ) :
      ((alt j (η k)).map (profile (η k)))
        (closure (Set.range
          (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ))) = 1 := by
    rw [Measure.map_apply (hprofile (η k)) isClosed_closure.measurableSet]
    have hpre : (profile (η k)) ⁻¹'
        closure (Set.range
          (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ)) =
        Set.univ := by
      apply Set.eq_univ_of_forall
      intro X
      exact subset_closure ⟨action (η k) X, rfl⟩
    rw [hpre]
    simp
  have hlimitSupp (j : Fin I.card) :
      ((μ j).bind κProfile.1)
        (closure (Set.range
          (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ))) = 1 :=
    closed_support_eq_one_of_weakConverges
      (fun k => (alt j (η k)).map (profile (η k)))
      ((μ j).bind κProfile.1) (hAltWeak j) _ isClosed_closure (hpreSupp j)
  have hℓmeas : Measurable ℓ := by
    have heq : ℓ = fun x => ENNReal.ofReal (ℓ x).toReal := by
      funext x
      exact (ENNReal.ofReal_toReal (hfinite x)).symm
    rw [heq]
    exact ENNReal.continuous_ofReal.measurable.comp huc.continuous.measurable
  have hprofileLimit (j : Fin I.card) : Tendsto
      (fun k => ∫ z, z j ∂((alt j (η k)).map (profile (η k)))) atTop
      (nhds (∫ z, z j ∂((μ j).bind κProfile.1))) :=
    finiteLossProfile_coordinate_integral_tendsto center ℓ hfinite hbdd
      (fun k => (alt j (η k)).map (profile (η k)))
      ((μ j).bind κProfile.1) (hAltWeak j) (hpreSupp j) (hlimitSupp j) j
  let centerN : Fin I.card → ℕ → EuclideanSpace ℝ (Fin d) := fun j n =>
    Real.sqrt n • (ψ ((γ j).curve ((Real.sqrt n)⁻¹)) - ψ P)
  have hcenterN (j : Fin I.card) : Tendsto (centerN j) atTop (nhds (center j)) := by
    simpa only [centerN, center, γ] using
      selectedPath_center_tendsto C hpd ((I.equivFin).symm j)
  let actionLaw : Fin I.card → ℕ → Measure (EuclideanSpace ℝ (Fin d)) := fun j k =>
    (alt j (η k)).map (action (η k))
  letI hActionLawProb (j : Fin I.card) (k : ℕ) :
      IsProbabilityMeasure (actionLaw j k) := by
    dsimp only [actionLaw]
    exact Measure.isProbabilityMeasure_map (haction (η k)).aemeasurable
  have hcenterDiff (j : Fin I.card) : Tendsto (fun k =>
      (∫ a, (ℓ (a - centerN j (η k))).toReal ∂(actionLaw j k)) -
        ∫ a, (ℓ (a - center j)).toReal ∂(actionLaw j k))
      atTop (nhds 0) :=
    integral_loss_center_difference_tendsto_zero ℓ hfinite hbdd huc
      (fun k => centerN j (η k)) (center j)
        ((hcenterN j).comp hη.tendsto_atTop)
      (actionLaw j)
  have hfixedEq (j : Fin I.card) (k : ℕ) :
      ∫ z, z j ∂((alt j (η k)).map (profile (η k))) =
        ∫ a, (ℓ (a - center j)).toReal ∂(actionLaw j k) := by
    calc
      ∫ z, z j ∂((alt j (η k)).map (profile (η k))) =
          ∫ X, (profile (η k) X) j ∂(alt j (η k)) :=
        MeasureTheory.integral_map (hprofile (η k)).aemeasurable
          (PiLp.continuous_apply 2 (fun _ : Fin I.card => ℝ) j).aestronglyMeasurable
      _ = ∫ X, (ℓ (action (η k) X - center j)).toReal ∂(alt j (η k)) := by
        rfl
      _ = ∫ a, (ℓ (a - center j)).toReal ∂(actionLaw j k) := by
        exact (MeasureTheory.integral_map (haction (η k)).aemeasurable
          ((huc.continuous.measurable.comp
            (measurable_id.sub measurable_const)).aestronglyMeasurable)).symm
  have hactualReal (j : Fin I.card) : Tendsto (fun k =>
      ∫ a, (ℓ (a - centerN j (η k))).toReal ∂(actionLaw j k)) atTop
      (nhds (∫ z, z j ∂((μ j).bind κProfile.1))) := by
    have hsum := (hcenterDiff j).add (hprofileLimit j)
    simpa only [zero_add] using hsum.congr' (Filter.Eventually.of_forall fun k => by
      rw [hfixedEq j k]
      simp only [sub_add_cancel])
  have hactualENN_eq (j : Fin I.card) (k : ℕ) :
      ENNReal.ofReal (∫ a, (ℓ (a - centerN j (η k))).toReal ∂(actionLaw j k)) =
        ∫⁻ X : Fin (η k) → Ω,
          ℓ (Real.sqrt (η k) • (T_n (η k) X -
            ψ ((γ j).curve ((Real.sqrt (η k))⁻¹)))) ∂(alt j (η k)) := by
    rw [← lintegral_loss_eq_ofReal_integral ℓ hfinite hbdd huc
      (centerN j (η k)) (actionLaw j k)]
    calc
      (∫⁻ a, ℓ (a - centerN j (η k))
          ∂((alt j (η k)).map (action (η k)))) =
          ∫⁻ X, ℓ (action (η k) X - centerN j (η k)) ∂(alt j (η k)) :=
        MeasureTheory.lintegral_map
          (hℓmeas.comp (measurable_id.sub measurable_const)) (haction (η k))
      _ = ∫⁻ X : Fin (η k) → Ω,
          ℓ (Real.sqrt (η k) • (T_n (η k) X -
            ψ ((γ j).curve ((Real.sqrt (η k))⁻¹)))) ∂(alt j (η k)) := by
        apply lintegral_congr
        intro X
        congr 2
        dsimp only [action, centerN]
        module
  have hactualLe (j : Fin I.card) :
      ENNReal.ofReal (∫ z, z j ∂((μ j).bind κProfile.1)) ≤ liminf u atTop := by
    have htActual := ENNReal.tendsto_ofReal (hactualReal j)
    apply le_of_tendsto_of_tendsto htActual hηlim
    exact Filter.Eventually.of_forall fun k => by
      change ENNReal.ofReal
        (∫ a, (ℓ (a - centerN j (η k))).toReal ∂(actionLaw j k)) ≤ u (η k)
      rw [hactualENN_eq j k]
      change (∫⁻ X : Fin (η k) → Ω,
        ℓ (Real.sqrt (η k) • (T_n (η k) X -
          ψ ((C.selectedPath ((I.equivFin).symm j)).curve
            ((Real.sqrt (η k))⁻¹))))
          ∂(Measure.pi fun _ : Fin (η k) =>
            (C.selectedPath ((I.equivFin).symm j)).curve
              ((Real.sqrt (η k))⁻¹))) ≤ u (η k)
      dsimp only [u]
      apply Finset.le_sup (f := fun g =>
        ∫⁻ X : Fin (η k) → Ω, ℓ (Real.sqrt (η k) • (T_n (η k) X -
            ψ ((C.selectedPath g).curve ((Real.sqrt (η k))⁻¹))))
          ∂(Measure.pi (fun _ : Fin (η k) =>
            (C.selectedPath g).curve ((Real.sqrt (η k))⁻¹))))
      exact ((I.equivFin).symm j).2
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlimtop => ?_
  have hεreal : 0 < (ε : ℝ≥0∞).toReal := by simpa using hε
  obtain ⟨κ, hκ⟩ :=
    Experiment.FiniteRiskCompactification.actionKernel_approx_of_lossProfileKernel
      μ hμprob center ℓ hfinite hbdd huc κProfile hlimitSupp ε.toReal hεreal
  letI : IsMarkovKernel κ.1 := κ.2
  refine (iInf_le (fun κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
      (EuclideanSpace ℝ (Fin d)) =>
        ⨆ g ∈ I, ∫⁻ a, ℓ (a -
          hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
        ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
          (finiteCarrierScoreCovariance C I)).bind κ.1)) κ).trans ?_
  apply iSup_le
  intro g
  apply iSup_le
  intro hg
  let j : Fin I.card := I.equivFin ⟨g, hg⟩
  have hj : (I.equivFin).symm j = ⟨g, hg⟩ := I.equivFin.symm_apply_apply ⟨g, hg⟩
  have hround := (hκ j j).le
  have hreal :
      ∫ a, (ℓ (a - center j)).toReal ∂((μ j).bind κ.1) ≤
        (liminf u atTop).toReal + ε.toReal := by
    have htarget : ∫ z, z j ∂((μ j).bind κProfile.1) ≤
        (liminf u atTop).toReal := by
      have hnonneg : 0 ≤ ∫ z, z j ∂((μ j).bind κProfile.1) := by
        have hsuppj := hlimitSupp j
        have hae : ∀ᵐ z ∂((μ j).bind κProfile.1),
            z ∈ closure (Set.range
              (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ)) := by
          apply (ae_mem_iff_measure_eq
            isClosed_closure.measurableSet.nullMeasurableSet).2
          simpa only [measure_univ] using hsuppj
        apply integral_nonneg_of_ae
        filter_upwards [hae] with z hz
        obtain ⟨B, hBtop, hB⟩ := hbdd
        have hrange : Set.range
            (Experiment.FiniteRiskCompactification.finiteLossProfile center ℓ) ⊆
            {z : EuclideanSpace ℝ (Fin I.card) | 0 ≤ z j} := by
          rintro _ ⟨a, rfl⟩
          exact ENNReal.toReal_nonneg
        exact closure_minimal hrange
          (isClosed_le continuous_const
            (PiLp.continuous_apply 2 (fun _ : Fin I.card => ℝ) j)) hz
      have hto := ENNReal.toReal_mono hlimtop.ne (hactualLe j)
      rw [ENNReal.toReal_ofReal hnonneg] at hto
      exact hto
    have habs := hround
    rw [abs_le] at habs
    linarith
  letI : IsProbabilityMeasure ((μ j).bind κ.1) := by
    refine isProbabilityMeasure_bind κ.1.measurable.aemeasurable ?_
    exact Filter.Eventually.of_forall fun _ => inferInstance
  have hriskEq :
      (∫⁻ a, ℓ (a - hpd.derivative
          ⟨g, selected_mem_tangentSpace C g⟩)
        ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
          (finiteCarrierScoreCovariance C I)).bind κ.1)) =
        ENNReal.ofReal
          (∫ a, (ℓ (a - center j)).toReal ∂((μ j).bind κ.1)) := by
    have hcenterEq : hpd.derivative
        ⟨g, selected_mem_tangentSpace C g⟩ = center j := by
      simp only [center, j, hj]
    have hmeasureEq : (multivariateGaussian (finiteCarrierScoreMean C I g)
        (finiteCarrierScoreCovariance C I)).bind κ.1 = (μ j).bind κ.1 := by
      simp only [μ, j, hj]
    rw [hcenterEq, hmeasureEq,
      lintegral_loss_eq_ofReal_integral ℓ hfinite hbdd huc]
  rw [hriskEq]
  calc
    ENNReal.ofReal (∫ a, (ℓ (a - center j)).toReal ∂((μ j).bind κ.1)) ≤
        ENNReal.ofReal ((liminf u atTop).toReal + ε.toReal) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = liminf u atTop + ε := by
      rw [ENNReal.ofReal_add (ENNReal.toReal_nonneg : 0 ≤ (liminf u atTop).toReal)
          (by positivity),
        ENNReal.ofReal_toReal hlimtop.ne]
      simp only [ENNReal.ofReal_coe_nnreal]
      change liminf u atTop + ε = liminf u atTop + ε
      rfl

/-- Every finite Gaussian carrier-experiment kernel risk is bounded by the
selected-path local asymptotic risk of the original estimator sequence.

Proof idea: apply finite loss-profile compactification jointly over `I`, use
`qmd_lecamThird_along_subseq` and `qmd_local_score_clt` on the selected paths,
and prove finite joint-vector convergence by finite-dimensional
Cramér--Wold.  Then disintegrate the profile limit and approximate it by an
action kernel.  No global modified estimator sequence is constructed. -/
theorem gaussianConeKernelRisk_le_selectedPathCanonicalLHSVec {d : ℕ}
    (C : NondominatedTangentCone P) (_hconv : Convex ℝ C.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hpd : NondominatedPathwiseDifferentiableAtVec P C ψ)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (_hT : ∀ n, Measurable (T_n n))
    (ℓ : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (_hbowl : BowlShaped ℓ) (_hlsc : LowerSemicontinuous ℓ) :
    (⨆ I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
      ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
          (EuclideanSpace ℝ (Fin d)),
        ⨆ g ∈ I, ∫⁻ a, ℓ (a -
            hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
          ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
            (finiteCarrierScoreCovariance C I)).bind κ.1)) ≤
      selectedPathCanonicalLHSVec C T_n ψ ℓ := by
  obtain ⟨φ, hEIF⟩ := exists_nondominatedEIFVec C hpd
  have hupper := finiteCarrierBenchmark_le_eifRisk C hpd φ hEIF ℓ _hbowl.measurable
  refine hupper.trans ?_
  rcases AsymptoticStatistics.LowerBounds.BowlShapedUCApprox.bowlShaped_uc_approx_vec
      ℓ _hbowl _hlsc with
    ⟨ℓn, hbowl, hfinite, hbdd, huc, hmono, htend⟩
  have hle (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℓn n x ≤ ℓ x := by
    apply ge_of_tendsto (htend x)
    exact Filter.eventually_atTop.2 ⟨n, fun k hk => hmono x hk⟩
  have hcont (n : ℕ) : Continuous (ℓn n) := by
    have h := ENNReal.continuous_ofReal.comp (huc n).continuous
    convert! h using 1
    funext x
    exact (ENNReal.ofReal_toReal (hfinite n x)).symm
  have hbounded (n : ℕ) :
      (∫⁻ y, ℓn n y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ))) ≤
        selectedPathCanonicalLHSVec C T_n ψ ℓ := by
    calc
      (∫⁻ y, ℓn n y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ))) ≤
          ⨆ I : Finset {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
            ⨅ κ : MarkovDecision (EuclideanSpace ℝ (Fin I.card))
                (EuclideanSpace ℝ (Fin d)),
              ⨆ g ∈ I, ∫⁻ a, ℓn n (a -
                  hpd.derivative ⟨g, selected_mem_tangentSpace C g⟩)
                ∂((multivariateGaussian (finiteCarrierScoreMean C I g)
                  (finiteCarrierScoreCovariance C I)).bind κ.1) :=
        finiteCarrierChart_exhausts_eifGram C _hconv hpd hEIF (ℓn n)
          (hbowl n) (hcont n).lowerSemicontinuous
      _ ≤ selectedPathCanonicalLHSVec C T_n ψ (ℓn n) :=
        gaussianConeKernelRisk_le_selectedPathCanonicalLHSVec_bounded
          C hpd T_n _hT (ℓn n) (hfinite n) (hbdd n) (huc n)
      _ ≤ selectedPathCanonicalLHSVec C T_n ψ ℓ :=
        selectedPathCanonicalLHSVec_mono C T_n ψ (hle n)
  have hsup (x : EuclideanSpace ℝ (Fin d)) : (⨆ n, ℓn n x) = ℓ x := by
    apply le_antisymm
    · exact iSup_le fun n => hle n x
    · apply le_of_tendsto (htend x)
      exact Filter.Eventually.of_forall fun n => le_iSup (fun k => ℓn k x) n
  calc
    (∫⁻ y, ℓ y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ))) =
        ∫⁻ y, ⨆ n, ℓn n y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
      apply lintegral_congr
      exact fun x => (hsup x).symm
    _ = ⨆ n, ∫⁻ y, ℓn n y ∂(multivariateGaussian 0 (Matrix.gram ℝ φ)) := by
      rw [lintegral_iSup]
      · exact fun n => (hbowl n).measurable
      · exact fun _ _ h => fun x => hmono x h
    _ ≤ selectedPathCanonicalLHSVec C T_n ψ ℓ := iSup_le hbounded

end AsymptoticStatistics.LowerBounds.NondominatedFiniteExperimentMinimax
