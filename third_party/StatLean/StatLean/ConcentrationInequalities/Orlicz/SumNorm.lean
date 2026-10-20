module
public import StatLean.ConcentrationInequalities.Orlicz.SubGaussianMGF
public import StatLean.ConcentrationInequalities.Orlicz.TailToNorm

@[expose] public section

/-!
# ψ₂-norm of independent sums

For independent, mean-zero $X_1, \dots, X_n$ with $\|X_i\|_{\psi_2} \le K_i$
and weights $v \in \mathbb{R}^n$,
$$ \Bigl\|\sum_{i=1}^{n} v_i X_i\Bigr\|_{\psi_2}^2
   \;\le\; 18 \sum_{i=1}^{n} v_i^2 K_i^2. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.7, Proposition 2.7.1 (weighted form; the
unweighted display is the $v \equiv 1$ instance).

**Proof formalization notes.** Constant frozen: `C = 18 = 6 · 3` — the
composite of bridge B2 (`hasSubgaussianMGF_of_subGaussianNorm_le`, proxy
`3K²`, R1 freeze) routed through Mathlib's
`HasSubgaussianMGF.sum_of_iIndepFun` (proxies add) and back through bridge
B3 (`subGaussianNorm_le_of_isSubGaussian`, factor `√6`). The book's absolute
constant `C` is thus explicit; the deviation from any sharper constant is
documented here per the batch's formula+numeral rule. `hK : ∀ i, 0 < K i` is
a mild LEAN-ONLY strengthening (zero bound forces `Xᵢ = 0` a.e.). Consumed by
`Orlicz/VectorNorm.lean` (Lemma 3.4.2 upper bound, `∑ vᵢ² = ‖v‖² = 1`).
Work-item fallback: this file belongs to `hdp-orlicz-vector`, whose single
named-sorry fallback is `subGaussianVecNorm_le_of_indep` in
`Orlicz/VectorNorm.lean` — everything here must close.

**Bibliographic comments.** The rotation-invariance-style additivity of
sub-Gaussian norms under independent sums is classical (Hoeffding/Kahane);
the ψ₂-norm packaging follows Buldygin–Kozachenko (AMS 2000, Ch. 1).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Weighted independent sums keep sub-Gaussian MGF with additive proxies
(LEAN-ONLY composite of B2 + `mgf` scaling + `sum_of_iIndepFun`; HDP §2.7
machinery). Proxy: `∑ vᵢ² · (3 Kᵢ²)` with the R1-frozen B2 factor `3`. -/
theorem hasSubgaussianMGF_weighted_sum
    -- LEAN-ONLY: probability measure; MGF machinery
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    (v : Fin n → ℝ)
    -- LEAN-ONLY: measurability of each coordinate
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Prop 2.7.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero coordinates; HDP Prop 2.7.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening, see module notes)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₂} ≤ Kᵢ; HDP Prop 2.7.1
    (hnorm : ∀ i, subGaussianNorm (X i) μ ≤ K i) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => ∑ i, v i * X i ω)
      (∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * (3 * (K i) ^ 2)) μ := by
  -- B2 per coordinate: mean-zero + ψ₂ bound give a sub-Gaussian MGF (proxy 3Kᵢ²).
  have hB2 : ∀ i, ProbabilityTheory.HasSubgaussianMGF (X i) (3 * (K i) ^ 2) μ := fun i =>
    hasSubgaussianMGF_of_subGaussianNorm_le (hmeas i).aemeasurable (hK i) (hnorm i) (hmean i)
  -- Scale each coordinate by the weight vᵢ (Mathlib `const_mul`: proxy vᵢ²·(3Kᵢ²)).
  have hscaled : ∀ i, ProbabilityTheory.HasSubgaussianMGF (fun ω => v i * X i ω)
      (⟨(v i) ^ 2, sq_nonneg _⟩ * (3 * (K i) ^ 2)) μ :=
    fun i => (hB2 i).const_mul (v i)
  -- Independence is preserved under the coordinatewise measurable maps `x ↦ vᵢ·x`.
  have hindep' : ProbabilityTheory.iIndepFun (fun i ω => v i * X i ω) μ :=
    hindep.comp (fun i (x : ℝ) => v i * x) (fun i => measurable_id.const_mul (v i))
  -- Sum the per-index proxies via Mathlib's independent-sum MGF lemma.
  have hsum := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hindep'
    (s := Finset.univ) (fun i _ => hscaled i)
  simpa using hsum

/-- **ψ₂-norm of a weighted independent sum** (HDP Proposition 2.7.1,
weighted; frozen constant `C = 18 = 6·3` from B3 ∘ B2). -/
theorem subGaussianNorm_weighted_sum_le
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    (v : Fin n → ℝ)
    -- LEAN-ONLY: measurability of each coordinate
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Prop 2.7.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero coordinates; HDP Prop 2.7.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₂} ≤ Kᵢ; HDP Prop 2.7.1
    (hnorm : ∀ i, subGaussianNorm (X i) μ ≤ K i) :
    subGaussianNorm (fun ω => ∑ i, v i * X i ω) μ ≤
      (NNReal.sqrt (18 * ∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * (K i) ^ 2) :
        ℝ≥0∞) := by
  -- The weighted sum has a sub-Gaussian MGF with proxy σ² = ∑ vᵢ²·(3Kᵢ²).
  have hmgf := hasSubgaussianMGF_weighted_sum v hmeas hindep hmean hK hnorm
  -- B3: convert the MGF bound to a ψ₂-norm bound `≤ √(6σ²)`.
  have hnorm' := subGaussianNorm_le_of_hasSubgaussianMGF hmgf
  -- Fold the constant: 6·(∑ vᵢ²·3Kᵢ²) = 18·∑ vᵢ²·Kᵢ².
  have hσeq : (6 : ℝ≥0) * (∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * (3 * (K i) ^ 2))
      = 18 * ∑ i, ⟨(v i) ^ 2, sq_nonneg _⟩ * (K i) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (fun a b => by ring : ∀ a b : ℝ≥0, 6 * (a * (3 * b)) = 18 * (a * b)) _ _
  rwa [hσeq] at hnorm'

/-- **ψ₂-norm of an independent sum** (HDP Proposition 2.7.1, the `v ≡ 1`
instance): `‖∑ Xᵢ‖_{ψ₂} ≤ √(18 ∑ Kᵢ²)`. -/
theorem subGaussianNorm_sum_le
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    -- LEAN-ONLY: measurability of each coordinate
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Prop 2.7.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero coordinates; HDP Prop 2.7.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₂} ≤ Kᵢ; HDP Prop 2.7.1
    (hnorm : ∀ i, subGaussianNorm (X i) μ ≤ K i) :
    subGaussianNorm (fun ω => ∑ i, X i ω) μ ≤
      (NNReal.sqrt (18 * ∑ i, (K i) ^ 2) : ℝ≥0∞) := by
  -- The `v ≡ 1` instance of the weighted bound.
  have h := subGaussianNorm_weighted_sum_le (fun _ => (1 : ℝ)) hmeas hindep hmean hK hnorm
  have h1 : NNReal.mk ((1 : ℝ) ^ 2) (sq_nonneg (1 : ℝ)) = 1 := NNReal.eq (by simp)
  have hs : (∑ i, NNReal.mk ((1 : ℝ) ^ 2) (sq_nonneg (1 : ℝ)) * (K i) ^ 2) = ∑ i, (K i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [h1, one_mul]
  simp only [one_mul] at h
  refine h.trans_eq ?_
  exact congrArg (fun s : ℝ≥0 => ((NNReal.sqrt (18 * s) : ℝ≥0) : ℝ≥0∞)) hs

end StatLean.ConcentrationInequalities
