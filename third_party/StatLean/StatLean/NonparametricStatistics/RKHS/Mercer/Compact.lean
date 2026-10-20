module
public import StatLean.NonparametricStatistics.RKHS.Mercer.Basic
public import Mathlib.Analysis.Normed.Operator.Compact

@[expose] public section

/-!
# Compactness of the Mercer integral operator

The integral operator of a Mercer kernel is a compact operator on `L²(X, μ)`.  Route:
truncating the uniformly convergent basis expansion of `K`
(`tendstoUniformly_scalarKernel`) yields finite-rank integral operators converging to
`T_K` in operator norm, and the space of compact operators is closed
(`isCompactOperator_of_tendsto`).

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 11, §11.3 (compactness of the Mercer integral operator — implicit in the book's
proof of Theorem 11.15 via Arzelà–Ascoli).

**Proof formalization notes.** Compactness is obtained without Arzelà–Ascoli: truncating the
uniformly convergent basis expansion of $K$ gives finite-rank integral operators (sums of rank-one
operators) with $\|T_K - T_{K_s}\| \le \mu(X)\,\sup|K - K_s| \to 0$, and the space of compact
operators is closed (`isCompactOperator_of_tendsto`).

**Bibliographic comments.** Compactness of integral operators with continuous kernels
is due to D. Hilbert (1904) and E. Schmidt (1907); the finite-rank approximation
argument is standard, cf. F. Smithies, *Integral Equations* (CUP, 1958), Ch. 7.
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

/-- Integral operators of kernels that are uniformly small have small operator norm:
`‖T_S‖ ≤ μ(X) · sup ‖S‖` for continuous symbols on a compact space. -/
theorem norm_mercerCLM_le_of_bounded {S : X → X → 𝕜}
    (hSc : Continuous fun p : X × X => S p.1 p.2) {C : ℝ}
    -- USER-INPUT: uniform bound on the symbol
    (hC : ∀ x y, ‖S x y‖ ≤ C) :
    ‖mercerCLM μ hSc‖ ≤ (μ Set.univ).toReal * C := by
  have hμ0 : (0 : ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
  have hprod : (0 : ℝ) ≤ (μ Set.univ).toReal * C := by
    rcases isEmpty_or_nonempty X with hX | hX
    · rw [Set.univ_eq_empty_iff.mpr hX, measure_empty]
      simp
    · exact mul_nonneg hμ0 (le_trans (norm_nonneg _) (hC hX.some hX.some))
  refine le_trans (norm_mercerCLM_le hSc) ?_
  have hin : ∀ x : X, ∫ y, ‖S x y‖ ^ 2 ∂μ ≤ (μ Set.univ).toReal * C ^ 2 := by
    intro x
    calc ∫ y, ‖S x y‖ ^ 2 ∂μ ≤ ∫ _y : X, C ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
            (integrable_const _)
            (Filter.Eventually.of_forall fun y => pow_le_pow_left₀ (norm_nonneg _) (hC x y) 2)
      _ = (μ Set.univ).toReal * C ^ 2 := by
          rw [integral_const, smul_eq_mul, measureReal_def]
  have hout : ∫ x, ∫ y, ‖S x y‖ ^ 2 ∂μ ∂μ ≤ ((μ Set.univ).toReal * C) ^ 2 := by
    calc ∫ x, ∫ y, ‖S x y‖ ^ 2 ∂μ ∂μ
        ≤ ∫ _x : X, (μ Set.univ).toReal * C ^ 2 ∂μ :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => integral_nonneg fun y => by positivity)
            (integrable_const _) (Filter.Eventually.of_forall hin)
      _ = (μ Set.univ).toReal * ((μ Set.univ).toReal * C ^ 2) := by
          rw [integral_const, smul_eq_mul, measureReal_def]
      _ = ((μ Set.univ).toReal * C) ^ 2 := by ring
  calc Real.sqrt (∫ x, ∫ y, ‖S x y‖ ^ 2 ∂μ ∂μ)
      ≤ Real.sqrt (((μ Set.univ).toReal * C) ^ 2) := Real.sqrt_le_sqrt hout
    _ = (μ Set.univ).toReal * C := Real.sqrt_sq hprod

private theorem coeFn_finset_sum_smul {ι : Type*} (s : Finset ι) (c : ι → 𝕜)
    (F : ι → Lp 𝕜 2 μ) :
    ((∑ i ∈ s, c i • F i : Lp 𝕜 2 μ) : X → 𝕜)
      =ᵐ[μ] fun x => ∑ i ∈ s, c i * (F i : X → 𝕜) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! Lp.coeFn_zero 𝕜 2 μ
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (c a • F a) (∑ i ∈ t, c i • F i),
        Lp.coeFn_smul (c a) (F a), ih] with x h1 h2 h3
      rw [h1]
      simp only [Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_insert ha]

private theorem isCompactOperator_finset_sum {ι : Type*} (s : Finset ι)
    (A : ι → (Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)) (hA : ∀ i, IsCompactOperator (A i)) :
    IsCompactOperator ((∑ i ∈ s, A i : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) : Lp 𝕜 2 μ → Lp 𝕜 2 μ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCompactOperator_zero (M₁ := Lp 𝕜 2 μ) (M₂ := Lp 𝕜 2 μ)
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      have : ((A a + ∑ i ∈ t, A i : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) : Lp 𝕜 2 μ → Lp 𝕜 2 μ)
          = (A a : Lp 𝕜 2 μ → Lp 𝕜 2 μ) + ((∑ i ∈ t, A i : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
            Lp 𝕜 2 μ → Lp 𝕜 2 μ) := rfl
      rw [this]
      exact (hA a).add ih

private theorem isCompactOperator_rankOne (u v : Lp 𝕜 2 μ) :
    IsCompactOperator (((innerSL 𝕜 u).smulRight v : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
      Lp 𝕜 2 μ → Lp 𝕜 2 μ) := by
  have h1 : IsCompactOperator
      (((ContinuousLinearMap.id 𝕜 𝕜).smulRight v : 𝕜 →L[𝕜] Lp 𝕜 2 μ) : 𝕜 → Lp 𝕜 2 μ) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  exact h1.comp_clm (innerSL 𝕜 u)

/-- The integral operator of a finite-rank symbol `∑_{i ∈ s} fᵢ(x) conj (gᵢ(y))` has
finite-dimensional range, hence is a compact operator. -/
theorem isCompactOperator_mercerCLM_finiteRank {ι : Type*} (s : Finset ι)
    (f g : ι → C(X, 𝕜))
    -- LEAN-ONLY: continuity of the finite-rank symbol; derivable, kept to name the operator
    (hc : Continuous fun p : X × X => ∑ i ∈ s, f i p.1 * conj (g i p.2)) :
    IsCompactOperator
      (mercerCLM (K := fun x y => ∑ i ∈ s, f i x * conj (g i y)) μ hc) := by
  classical
  have hfae : ∀ i : ι, ((ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (f i) : Lp 𝕜 2 μ) : X → 𝕜)
      =ᵐ[μ] fun x => (f i) x :=
    fun i => ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (𝕜 := 𝕜) μ (f i)
  have hgae : ∀ i : ι, ((ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i) : Lp 𝕜 2 μ) : X → 𝕜)
      =ᵐ[μ] fun x => (g i) x :=
    fun i => ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (𝕜 := 𝕜) μ (g i)
  have hgmem : ∀ i : ι, MemLp (fun y => conj ((g i) y)) 2 μ := fun i =>
    ((Lp.memLp (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i))).ae_eq (hgae i)).star
  have hEq : ((mercerCLM (K := fun x y => ∑ i ∈ s, f i x * conj (g i y)) μ hc) :
        Lp 𝕜 2 μ → Lp 𝕜 2 μ)
      = ((∑ i ∈ s, ((innerSL 𝕜 (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i))).smulRight
          (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (f i))) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
        Lp 𝕜 2 μ → Lp 𝕜 2 μ) := by
    funext h
    have hcoefg : ∀ i : ι, ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i), h⟫_𝕜
        = ∫ y, conj ((g i) y) * (h : X → 𝕜) y ∂μ := by
      intro i
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hgae i] with y hy
      rw [RCLike.inner_apply, hy]
      ring
    have hint : ∀ x : X,
        integralOp μ (fun x y => ∑ i ∈ s, (f i) x * conj ((g i) y)) h x
          = ∑ i ∈ s, (f i) x * ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i), h⟫_𝕜 := by
      intro x
      have hre : ∀ y : X, (∑ i ∈ s, (f i) x * conj ((g i) y)) * (h : X → 𝕜) y
          = ∑ i ∈ s, (f i) x * (conj ((g i) y) * (h : X → 𝕜) y) := by
        intro y
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hintg : ∀ i ∈ s,
          Integrable (fun y => (f i) x * (conj ((g i) y) * (h : X → 𝕜) y)) μ := fun i _ =>
        ((hgmem i).integrable_mul (Lp.memLp h)).const_mul ((f i) x)
      rw [integralOp, integral_congr_ae (Filter.Eventually.of_forall hre),
        integral_finset_sum s hintg]
      exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul, hcoefg]
    have hRHS : ((∑ i ∈ s, ((innerSL 𝕜 (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i))).smulRight
          (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (f i))) : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)) h
        = ∑ i ∈ s, (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i), h⟫_𝕜) •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (f i) := by
      rw [ContinuousLinearMap.sum_apply]
      exact Finset.sum_congr rfl fun i _ => rfl
    refine Lp.ext ?_
    rw [hRHS]
    filter_upwards [mercerCLM_coeFn_ae (K := fun x y => ∑ i ∈ s, (f i) x * conj ((g i) y)) hc h,
      coeFn_finset_sum_smul s (fun i => ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (g i), h⟫_𝕜)
        (fun i => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (f i)),
      (Filter.eventually_all_finset s).mpr (fun i _ => hfae i)] with x h1 h2 h3
    rw [h1, h2, hint x]
    exact Finset.sum_congr rfl fun i hi => by rw [h3 i hi]; ring
  rw [hEq]
  exact isCompactOperator_finset_sum s _ fun i => isCompactOperator_rankOne _ _


private theorem mercerCLM_sub {K₁ K₂ : X → X → 𝕜}
    (h₁ : Continuous fun p : X × X => K₁ p.1 p.2)
    (h₂ : Continuous fun p : X × X => K₂ p.1 p.2)
    (h₁₂ : Continuous fun p : X × X => K₁ p.1 p.2 - K₂ p.1 p.2) :
    mercerCLM μ h₁ - mercerCLM μ h₂
      = mercerCLM (K := fun x y => K₁ x y - K₂ x y) μ h₁₂ := by
  refine ContinuousLinearMap.ext fun g => ?_
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (mercerCLM μ h₁ g) (mercerCLM μ h₂ g),
    mercerCLM_coeFn_ae h₁ g, mercerCLM_coeFn_ae h₂ g,
    mercerCLM_coeFn_ae (K := fun x y => K₁ x y - K₂ x y) h₁₂ g] with x hx hx1 hx2 hx3
  rw [ContinuousLinearMap.sub_apply, hx, hx3]
  simp only [Pi.sub_apply, hx1, hx2]
  have i1 : Integrable (fun y => K₁ x y * (g : X → 𝕜) y) μ :=
    (isL2Symbol_of_continuous h₁ x).integrable_mul (Lp.memLp _)
  have i2 : Integrable (fun y => K₂ x y * (g : X → 𝕜) y) μ :=
    (isL2Symbol_of_continuous h₂ x).integrable_mul (Lp.memLp _)
  rw [integralOp, integralOp, integralOp, ← integral_sub i1 i2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

/-- **The Mercer integral operator is compact.** -/
theorem isCompactOperator_mercerCLM {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K) :
    IsCompactOperator (mercerCLM μ hK.continuous) := by
  classical
  obtain ⟨H₀, _, _, _, _, hKH⟩ := hK.isKernelFun.exists_rkhs
  obtain ⟨w, e, -⟩ := exists_hilbertBasis 𝕜 H₀
  have hKsc : Continuous fun p : X × X => scalarKernel H₀ p.1 p.2 := by
    rw [hKH]; exact hK.continuous
  set φ : w → C(X, 𝕜) := fun i =>
    ⟨((e i : H₀) : X → 𝕜), continuous_coe_of_continuous_scalarKernel hKsc _⟩ with hφ
  have hc : ∀ s : Finset w,
      Continuous fun p : X × X => ∑ i ∈ s, (φ i) p.1 * conj ((φ i) p.2) := by
    intro s
    refine continuous_finset_sum s fun i _ => ?_
    exact ((φ i).continuous.comp' continuous_fst).mul
      (RCLike.continuous_conj.comp' ((φ i).continuous.comp' continuous_snd))
  have hsub : ∀ s : Finset w, Continuous fun p : X × X =>
      (∑ i ∈ s, (φ i) p.1 * conj ((φ i) p.2)) - K p.1 p.2 := fun s => (hc s).sub hK.continuous
  refine isCompactOperator_of_tendsto (l := Filter.atTop)
    (F := fun s : Finset w => mercerCLM
      (K := fun x y => ∑ i ∈ s, (φ i) x * conj ((φ i) y)) μ (hc s)) ?_ ?_
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have hμ0 : (0 : ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
    have hε' : (0 : ℝ) < ε / ((μ Set.univ).toReal + 1) := by positivity
    have huc := Metric.tendstoUniformly_iff.mp
      (tendstoUniformly_scalarKernel (H := H₀) hK hKH e) _ hε'
    obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp huc
    refine ⟨s₀, fun s hs => ?_⟩
    have hbnd : ∀ x y : X,
        ‖(∑ i ∈ s, (φ i) x * conj ((φ i) y)) - K x y‖
          ≤ ε / ((μ Set.univ).toReal + 1) := by
      intro x y
      have h := hs₀ s hs (x, y)
      rw [dist_eq_norm] at h
      have hcomm : (∑ i ∈ s, conj ((e i : H₀) y) * (e i : H₀) x)
          = ∑ i ∈ s, (φ i) x * conj ((φ i) y) :=
        Finset.sum_congr rfl fun i _ => by rw [hφ]; exact mul_comm _ _
      rw [hcomm] at h
      rw [← norm_neg]
      simpa using h.le
    rw [dist_eq_norm, mercerCLM_sub (hc s) hK.continuous (hsub s)]
    refine lt_of_le_of_lt (norm_mercerCLM_le_of_bounded (hsub s) hbnd) ?_
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [hμ0, hε]
  · filter_upwards with s
    exact isCompactOperator_mercerCLM_finiteRank s φ φ (hc s)


end StatLean.NonparametricStatistics
