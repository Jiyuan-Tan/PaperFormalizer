module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import StatLean.AsymptoticStatistics.ForMathlib.Prohorov
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianConv

@[expose] public section

/-!
Lévy m-pass for multivariate Gaussian convolution decomposition.

This file proves the vector analogue of `ParametricBridge.levyMpass`. Given a
sequence of per-m Gaussian-convolution decompositions `L = multivariateGaussian 0 (Σ_m) ⋆ M_m`
where the covariance matrices `Σ_m` converge entrywise to a limit matrix `G`,
we construct a single probability measure `M` such that
`L = multivariateGaussian 0 G ⋆ M`.

The proof follows the same 4-step skeleton as the scalar version:
1. Define the char-fn quotient `f(t) := charFun L t / charFun (multivariateGaussian 0 G) t`.
2. Show that `charFun (M_m m) t → f t` pointwise via the decomposition and
   matrix convergence.
3. Apply `isTightMeasureSet_of_tendsto_charFun` to establish tightness of `{M_m m}`.
4. Extract a weakly convergent subsequence via Prokhorov, identify the limit by
   char-fn injectivity, and assemble the final convolution.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal Matrix

namespace AsymptoticStatistics.ForMathlib.LevyMpassVec

/-- **Step 2b:** Multivariate Gaussian characteristic function is continuous and
converges with the covariance matrix.

When the covariance matrices `Σ_m` converge to `G` (both PSD), the characteristic
function of the corresponding multivariate Gaussians converges for each `t`. -/
theorem multivariateGaussian_charFun_continuous_tendsto
    {k : ℕ}
    (G : Matrix (Fin k) (Fin k) ℝ) (hG_psd : G.PosSemidef)
    (Sigma_m : ℕ → Matrix (Fin k) (Fin k) ℝ)
    (hSigma_psd : ∀ m, (Sigma_m m).PosSemidef)
    (hSigma_tendsto : Filter.Tendsto Sigma_m Filter.atTop (𝓝 G))
    (t : EuclideanSpace ℝ (Fin k)) :
    Filter.Tendsto
      (fun m => MeasureTheory.charFun
        (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (Sigma_m m)) t)
      Filter.atTop
      (𝓝 (MeasureTheory.charFun
        (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) G) t)) := by
  -- Step 1: rewrite each side via the closed-form `charFun_multivariateGaussian`
  -- evaluated at `μ = 0`, where `⟪t, 0⟫ = 0`. Use `t.ofLp` (the `EuclideanSpace`
  -- coercion exposed by simp) so the rewrite lands on the same term we converge
  -- against below.
  have h_eq : ∀ S : Matrix (Fin k) (Fin k) ℝ, S.PosSemidef →
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) S) t =
        Complex.exp (-((t.ofLp ⬝ᵥ S *ᵥ t.ofLp : ℝ) : ℂ) / 2) := by
    intro S hS
    rw [charFun_multivariateGaussian hS]
    simp
    ring_nf
  rw [h_eq G hG_psd]
  simp_rw [h_eq _ (hSigma_psd _)]
  -- Step 2: entrywise convergence of `Sigma_m → G` yields `Sigma_m *ᵥ t.ofLp → G *ᵥ t.ofLp`.
  have h_mulVec :
      Filter.Tendsto (fun m => (Sigma_m m) *ᵥ t.ofLp) Filter.atTop (𝓝 (G *ᵥ t.ofLp)) :=
    (Continuous.matrix_mulVec continuous_id continuous_const).tendsto G |>.comp hSigma_tendsto
  -- Step 3: continuity of `⟨t.ofLp, ·⟩` lifts this to convergence of the dot-product scalar.
  have h_dot :
      Filter.Tendsto (fun m => (t.ofLp ⬝ᵥ (Sigma_m m) *ᵥ t.ofLp : ℝ)) Filter.atTop
        (𝓝 (t.ofLp ⬝ᵥ G *ᵥ t.ofLp : ℝ)) :=
    (Continuous.dotProduct continuous_const continuous_id).tendsto (G *ᵥ t.ofLp) |>.comp h_mulVec
  -- Step 4: lift the real scalar to ℂ.
  have h_dot_complex :
      Filter.Tendsto (fun m => ((t.ofLp ⬝ᵥ (Sigma_m m) *ᵥ t.ofLp : ℝ) : ℂ)) Filter.atTop
        (𝓝 ((t.ofLp ⬝ᵥ G *ᵥ t.ofLp : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h_dot
  -- Step 5: arithmetic (negation + division) preserves convergence on ℂ.
  have h_arg :
      Filter.Tendsto (fun m => -((t.ofLp ⬝ᵥ (Sigma_m m) *ᵥ t.ofLp : ℝ) : ℂ) / 2) Filter.atTop
        (𝓝 (-((t.ofLp ⬝ᵥ G *ᵥ t.ofLp : ℝ) : ℂ) / 2)) :=
    h_dot_complex.neg.div_const 2
  -- Step 6: apply `Complex.exp` continuity to close.
  exact (Complex.continuous_exp.tendsto _).comp h_arg

/-- **Step 4a:** Tight coercion from measures to probability measures.

When a family of measures forms a tight set, the corresponding probability measures
(obtained via coercion) also form a tight set. -/
theorem isTightMeasureSet_probabilityMeasure_coercion
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    (M_m : ℕ → MeasureTheory.Measure E)
    [∀ m, MeasureTheory.IsProbabilityMeasure (M_m m)]
    (hTight : MeasureTheory.IsTightMeasureSet (Set.range M_m))
    (PM_m : ℕ → MeasureTheory.ProbabilityMeasure E)
    (hPM : ∀ m, (PM_m m : MeasureTheory.Measure E) = M_m m) :
    MeasureTheory.IsTightMeasureSet {x | ∃ μ ∈ Set.range PM_m, (μ : MeasureTheory.Measure E) = x} :=
        by
  -- Rewrite the set comprehension as a range
  have h_set_eq : {x | ∃ μ ∈ Set.range PM_m, (μ : MeasureTheory.Measure E) = x} =
      Set.range (fun m => (PM_m m : MeasureTheory.Measure E)) := by
    ext x
    simp only [Set.mem_setOf, Set.mem_range]
    constructor
    · intro ⟨μ, ⟨m, hm⟩, hx⟩
      exact ⟨m, hm ▸ hx⟩
    · intro ⟨m, hx⟩
      exact ⟨PM_m m, ⟨m, rfl⟩, hx⟩
  rw [h_set_eq]
  -- Now the range of the coercion equals the range of M_m by hPM
  have h_range_eq : Set.range (fun m => (PM_m m : MeasureTheory.Measure E)) = Set.range M_m := by
    ext x
    simp only [Set.mem_range]
    constructor
    · intro ⟨m, hx⟩
      exact ⟨m, (hPM m).symm ▸ hx⟩
    · intro ⟨m, hx⟩
      exact ⟨m, (hPM m) ▸ hx⟩
  rw [h_range_eq]
  exact hTight

/-- **Step 6:** Final algebraic identity.

For the characteristic function identity `a = b * (a / b)` when `b ≠ 0`. -/
theorem charFun_eq_mul_div_self
    {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
    (μ ν : MeasureTheory.Measure E) (t : E)
    (h_ne : MeasureTheory.charFun ν t ≠ 0) :
    MeasureTheory.charFun μ t = MeasureTheory.charFun ν t *
      (MeasureTheory.charFun μ t / MeasureTheory.charFun ν t) := by
  field_simp [h_ne]

/-- **Vector Lévy m-pass:** construct the limit Gaussian factor in a Gaussian
convolution decomposition via tightness and weak convergence of the residual
probability measures.

Given per-m decompositions `L = multivariateGaussian 0 (Σ_m) ⋆ M_m` where the
covariance matrices `Σ_m : ℕ → Matrix (Fin k) (Fin k) ℝ` are PSD and converge
entrywise to a limit PSD matrix `G`, there exists a probability measure `M`
such that `L = multivariateGaussian 0 G ⋆ M`.

This is the vector analogue of `ParametricBridge.levyMpass` for `EuclideanSpace ℝ (Fin k)`.
The proof structure (quotient, tightness, Prokhorov, char-fn identity) is identical
to the scalar case; only the domain changes. -/
theorem levyMpass_vec
    {k : ℕ}
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L]
    (M_m : ℕ → Measure (EuclideanSpace ℝ (Fin k)))
    [∀ m, IsProbabilityMeasure (M_m m)]
    (Sigma_m : ℕ → Matrix (Fin k) (Fin k) ℝ)
    (hSigma_psd : ∀ m, (Sigma_m m).PosSemidef)
    (G : Matrix (Fin k) (Fin k) ℝ) (hG_psd : G.PosSemidef)
    (hL_decomp : ∀ m,
      L = (multivariateGaussian 0 (Sigma_m m)) ∗ (M_m m))
    (hSigma_tendsto : Filter.Tendsto Sigma_m Filter.atTop (𝓝 G)) :
    ∃ M : Measure (EuclideanSpace ℝ (Fin k)),
      IsProbabilityMeasure M ∧
      L = (multivariateGaussian 0 G) ∗ M := by
  
  -- Step 0: The Gaussian charFn never vanishes.
  have hGauss_ne : ∀ (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosSemidef) (t : EuclideanSpace ℝ (Fin
      k)),
      charFun (multivariateGaussian 0 S) t ≠ 0 := by
    intro S hS t
    exact (charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin k))) hS t).symm ▸
      Complex.exp_ne_zero _
  
  -- Step 1: Define the char-fn quotient f(t).
  set f : EuclideanSpace ℝ (Fin k) → ℂ := fun t =>
    charFun L t / charFun (multivariateGaussian 0 G) t
  
  -- f is continuous.
  have hf_cont : Continuous f := by
    refine Continuous.div continuous_charFun continuous_charFun ?_
    intro t; exact hGauss_ne G hG_psd t
  have hf_cont0 : ContinuousAt f 0 := hf_cont.continuousAt
  
  -- Step 2: Per-m equation and convergence.
  haveI : ∀ m, IsProbabilityMeasure (M_m m) := fun m => inferInstance
  
  have hCharFn_conv : ∀ m (t : EuclideanSpace ℝ (Fin k)),
      charFun L t =
        charFun (multivariateGaussian 0 (Sigma_m m)) t * charFun (M_m m) t := by
    intro m t
    rw [hL_decomp m]
    exact charFun_conv (μ := multivariateGaussian 0 (Sigma_m m)) (ν := M_m m) t
  
  have hCharFn_M : ∀ m (t : EuclideanSpace ℝ (Fin k)),
      charFun (M_m m) t =
        charFun L t / charFun (multivariateGaussian 0 (Sigma_m m)) t := by
    intro m t
    field_simp [hGauss_ne (Sigma_m m) (hSigma_psd m) t]
    linear_combination (hCharFn_conv m t).symm
  
  -- Pointwise convergence of charFn (M_m m) to f
  have hCharFn_M_lim : ∀ t : EuclideanSpace ℝ (Fin k),
      Filter.Tendsto (fun m => charFun (M_m m) t) Filter.atTop (𝓝 (f t)) := by
    intro t
    have h_denom :
        Filter.Tendsto (fun m => charFun (multivariateGaussian 0 (Sigma_m m)) t)
          Filter.atTop (𝓝 (charFun (multivariateGaussian 0 G) t)) := by
      exact multivariateGaussian_charFun_continuous_tendsto G hG_psd Sigma_m hSigma_psd
          hSigma_tendsto t
    have h_target :
        Filter.Tendsto (fun m =>
          charFun L t / charFun (multivariateGaussian 0 (Sigma_m m)) t)
          Filter.atTop (𝓝 (charFun L t / charFun (multivariateGaussian 0 G) t)) :=
      tendsto_const_nhds.div h_denom (hGauss_ne G hG_psd t)
    change Filter.Tendsto (fun m => charFun (M_m m) t) Filter.atTop (𝓝 (f t))
    convert h_target using 2 with m
    exact hCharFn_M m t
  
  -- Step 3: Tightness.
  have hTight : IsTightMeasureSet (Set.range M_m) :=
    isTightMeasureSet_of_tendsto_charFun hf_cont0 hCharFn_M_lim
  
  -- Step 4: Prokhorov extraction on the tight family.
  let PM_m : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    fun m => ⟨M_m m, inferInstance⟩
  
  have hCompact : IsCompact (closure (Set.range PM_m)) := by
    apply isCompact_closure_of_isTightMeasureSet
    exact isTightMeasureSet_probabilityMeasure_coercion M_m hTight PM_m (fun _ => rfl)
  
  obtain ⟨M_PM, hM_PM_in_closure, φ, hφ_mono, hφ_tendsto⟩ :=
    hCompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  
  let M := (M_PM : Measure (EuclideanSpace ℝ (Fin k)))
  
  -- Step 5: Identify charFun M = f via weak convergence.
  have hCharFn_M_eq :
      ∀ t : EuclideanSpace ℝ (Fin k),
        charFun M t = f t := by
    intro t
    have h_sub_to_f :
        Filter.Tendsto
          (fun k => charFun ((PM_m (φ k) : Measure _)) t)
          Filter.atTop (𝓝 (f t)) := by
      have : Filter.Tendsto (fun k => charFun (M_m (φ k)) t) Filter.atTop (𝓝 (f t)) :=
        (hCharFn_M_lim t).comp hφ_mono.tendsto_atTop
      simpa [PM_m] using this
    
    have h_sub_to_M :
        Filter.Tendsto
          (fun k => charFun ((PM_m (φ k) : Measure _)) t)
          Filter.atTop (𝓝 (charFun M t)) :=
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hφ_tendsto) t
    
    exact tendsto_nhds_unique h_sub_to_M h_sub_to_f
  
  -- Step 6: Conclude via char-fn uniqueness.
  refine ⟨M, inferInstance, ?_⟩
  
  refine Measure.ext_of_charFun ?_
  ext t
  
  rw [charFun_conv, hCharFn_M_eq t]
  -- Goal: charFun L t = charFun (multivariateGaussian 0 G) t * f t
  -- where f t = charFun L t / charFun (multivariateGaussian 0 G) t
  exact charFun_eq_mul_div_self L (multivariateGaussian 0 G) t (hGauss_ne G hG_psd t)

end AsymptoticStatistics.ForMathlib.LevyMpassVec
