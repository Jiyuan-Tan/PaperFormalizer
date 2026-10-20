module
public import StatLean.ConcentrationInequalities.Orlicz.SubExponentialMGF

@[expose] public section

/-!
# Bernstein's inequality for sub-exponential sums (ψ₁-norm form)

For independent, mean-zero, sub-exponential $X_1, \dots, X_n$,
$$ \mathbb{P}\Bigl\{ \Bigl|\sum_{i=1}^{n} X_i\Bigr| \ge t \Bigr\}
   \;\le\; 2 \exp\Bigl[ -c \cdot \min\Bigl(
     \frac{t^2}{\sum_i \|X_i\|_{\psi_1}^2},
     \frac{t}{\max_i \|X_i\|_{\psi_1}} \Bigr) \Bigr], \qquad t \ge 0. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §2.9, Theorem 2.9.1 (and Corollary 2.9.2 for the
weighted form).

**Proof formalization notes.** Constants are explicit (formula + frozen
numeral): the exponent is $\min\bigl(t^2/(16\sum K_i^2),\, t/(4\max K_i)\bigr)$
— i.e. the book's absolute constant $c$ is realized as $c = 1/16$ in the
quadratic regime and $1/4$ in the linear regime, coming from the restricted
MGF bound `mgf_le_of_lintegral_exp_abs_le_two` ($E e^{\lambda X}
\le e^{4\lambda^2 K^2}$ for $|\lambda| \le 1/(2K)$, HDP Prop 2.8.1(iv) with
$K_4 = 2K$) via Chernoff and the optimization
$\lambda^\* = \min\bigl(t/(8\sum K_i^2),\, 1/(2\max K_i)\bigr)$. One-sided
engine first (`measure_sum_ge_le_of_subExponentialNorm_le`), two-sided by the
`X ↦ −X` symmetry of the ψ₁ norm and a union bound. `hK : ∀ i, 0 < K i` is a
mild strengthening over the book (a zero bound forces the degenerate
`X_i = 0` a.e., removable by reindexing); documented, not laundered. The
work item's single named-sorry fallback is the **bonus** weighted Corollary
2.9.2 (`bernstein_subexponential_weighted`); Theorem 2.9.1 itself must close.

**Bibliographic comments.** Bernstein-type inequalities for unbounded
variables under exponential-moment conditions go back to S. N. Bernstein
(1920s–1930s); the ψ₁-norm formulation is the modern synthesis due to
Vershynin. The moment-condition
variant is formalized separately in `Bernstein/Bernstein.lean` (Lu-BDA); the
two are deliberately distinct results.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- One-sided ψ₁-Bernstein engine (HDP Theorem 2.9.1, upper tail):
Chernoff + `iIndepFun.mgf_sum` + the per-`i` restricted MGF bound of
Prop 2.8.1(iv), optimized at
`λ* = min (t / (8 ∑ Kᵢ²)) (1 / (2 max Kᵢ))`. Exponent frozen:
`min (t²/(16 ∑ Kᵢ²)) (t/(4 max Kᵢ))`. -/
theorem measure_sum_ge_le_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; Chernoff/MGF machinery requires it
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    -- LEAN-ONLY: nonempty sum so max Kᵢ is well-defined; n = 0 is vacuous
    (hn : 0 < n)
    -- LEAN-ONLY: measurability of each summand; MGF regularity
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the Xᵢ; HDP Thm 2.9.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero summands; HDP Thm 2.9.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (zero forces Xᵢ = 0 a.e.; removable
    -- by reindexing — documented mild strengthening)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: sub-exponential norm bounds ‖Xᵢ‖_{ψ₁} ≤ Kᵢ; HDP Thm 2.9.1
    (hnorm : ∀ i, subExponentialNorm (X i) μ ≤ K i)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Thm 2.9.1
    (ht : 0 ≤ t) :
    μ {ω | t ≤ ∑ i, X i ω} ≤
      ENNReal.ofReal (Real.exp (-(min (t ^ 2 / (16 * ∑ i, (K i : ℝ) ^ 2))
        (t / (4 * ((Finset.univ.sup K : ℝ≥0) : ℝ))))))  := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Abbreviations for the two scale aggregates appearing in the exponent.
  set sumK2 : ℝ := ∑ i, (K i : ℝ) ^ 2 with hsumK2def
  set maxK : ℝ := ((Finset.univ.sup K : ℝ≥0) : ℝ) with hmaxKdef
  -- Positivity bookkeeping.
  have hKpos_r : ∀ i, (0 : ℝ) < (K i : ℝ) := fun i => NNReal.coe_pos.mpr (hK i)
  have hKle : ∀ i, (K i : ℝ) ≤ maxK := fun i =>
    NNReal.coe_le_coe.mpr (Finset.le_sup (Finset.mem_univ i))
  have hmaxK_pos : 0 < maxK := lt_of_lt_of_le (hKpos_r ⟨0, hn⟩) (hKle ⟨0, hn⟩)
  have hsumK2_pos : 0 < sumK2 := by
    rw [hsumK2def]
    exact Finset.sum_pos (fun i _ => by have := hKpos_r i; positivity) Finset.univ_nonempty
  have hs0 : sumK2 ≠ 0 := ne_of_gt hsumK2_pos
  have hm0 : maxK ≠ 0 := ne_of_gt hmaxK_pos
  have h8s : (0 : ℝ) < 8 * sumK2 := by have := hsumK2_pos; linarith
  have h2m : (0 : ℝ) < 2 * maxK := by have := hmaxK_pos; linarith
  have h4m2 : (0 : ℝ) < 4 * maxK ^ 2 := by nlinarith [mul_pos hmaxK_pos hmaxK_pos]
  -- The optimizer.
  set lam : ℝ := min (t / (8 * sumK2)) (1 / (2 * maxK)) with hlam
  have hlam_nonneg : 0 ≤ lam := by
    rw [hlam]
    exact le_min (div_nonneg ht (le_of_lt h8s)) (le_of_lt (one_div_pos.mpr h2m))
  -- `|λ*| ≤ 1/(2 Kᵢ)` for the per-`i` MGF bound.
  have hlam_le_i : ∀ i, |lam| ≤ 1 / (2 * (K i : ℝ)) := by
    intro i
    rw [abs_of_nonneg hlam_nonneg]
    have h1 : lam ≤ 1 / (2 * maxK) := by rw [hlam]; exact min_le_right _ _
    have h2 : (1 : ℝ) / (2 * maxK) ≤ 1 / (2 * (K i : ℝ)) := by
      apply one_div_le_one_div_of_le
      · have := hKpos_r i; linarith
      · have := hKle i; linarith
    linarith
  -- `|λ*| ≤ 1/Kᵢ` for the per-`i` integrability of `exp(λ*Xᵢ)`.
  have hlam_le1_i : ∀ i, |lam| ≤ 1 / (K i : ℝ) := by
    intro i
    rw [abs_of_nonneg hlam_nonneg]
    have h1 : lam ≤ 1 / (2 * maxK) := by rw [hlam]; exact min_le_right _ _
    have h2 : (1 : ℝ) / (2 * maxK) ≤ 1 / (K i : ℝ) := by
      apply one_div_le_one_div_of_le
      · have := hKpos_r i; linarith
      · have := hKle i; have := hmaxK_pos; linarith
    linarith
  -- Per-`i` restricted MGF bound (Prop 2.8.1(iv)) and integrability.
  have hcond_i : ∀ i, ∫⁻ ω, ENNReal.ofReal (Real.exp (|X i ω| / (K i : ℝ))) ∂μ ≤ 2 :=
    fun i => lintegral_exp_abs_le_two_of_subExponentialNorm_le (hmeas i).aemeasurable (hK i)
      (hnorm i)
  have hmgf_i : ∀ i, mgf (X i) μ lam ≤ Real.exp (4 * lam ^ 2 * (K i : ℝ) ^ 2) :=
    fun i => mgf_le_of_subExponentialNorm_le (hmeas i).aemeasurable (hK i) (hnorm i) (hmean i)
      (hlam_le_i i)
  have hint_i : ∀ i, Integrable (fun ω => Real.exp (lam * X i ω)) μ :=
    fun i => integrable_exp_mul_of_lintegral_exp_abs_le_two (hmeas i).aemeasurable (hK i)
      (hcond_i i) (hlam_le1_i i)
  -- MGF of the sum factorizes and is bounded by `exp(4 λ*² ∑ Kᵢ²)`.
  have hmgf_sum : mgf (∑ i, X i) μ lam = ∏ i, mgf (X i) μ lam :=
    hindep.mgf_sum (t := lam) hmeas Finset.univ
  have hprod_le : ∏ i, mgf (X i) μ lam ≤ ∏ i, Real.exp (4 * lam ^ 2 * (K i : ℝ) ^ 2) :=
    Finset.prod_le_prod (fun i _ => mgf_nonneg) (fun i _ => hmgf_i i)
  have hprod_eq : ∏ i, Real.exp (4 * lam ^ 2 * (K i : ℝ) ^ 2) = Real.exp (4 * lam ^ 2 * sumK2) := by
    rw [← Real.exp_sum, hsumK2def, Finset.mul_sum]
  have hmgf_sum_le : mgf (∑ i, X i) μ lam ≤ Real.exp (4 * lam ^ 2 * sumK2) := by
    rw [hmgf_sum]; exact le_trans hprod_le (le_of_eq hprod_eq)
  -- Integrability of `exp(λ* ∑Xᵢ)` for Chernoff.
  have hint_sum : Integrable (fun ω => Real.exp (lam * (∑ i, X i) ω)) μ :=
    hindep.integrable_exp_mul_sum (t := lam) hmeas (s := Finset.univ) (fun i _ => hint_i i)
  -- Chernoff bound.
  have chern := measure_ge_le_exp_mul_mgf (μ := μ) (X := (∑ i, X i)) (t := lam) (ε := t)
    hlam_nonneg hint_sum
  -- The optimization: `min(...) ≤ λ*t − 4λ*²∑Kᵢ²`.
  have hkey : min (t ^ 2 / (16 * sumK2)) (t / (4 * maxK)) ≤ lam * t - 4 * lam ^ 2 * sumK2 := by
    rw [hlam]
    rcases le_total (t / (8 * sumK2)) (1 / (2 * maxK)) with hAB | hAB
    · rw [min_eq_left hAB]
      have heq : t / (8 * sumK2) * t - 4 * (t / (8 * sumK2)) ^ 2 * sumK2
          = t ^ 2 / (16 * sumK2) := by field_simp; ring
      rw [heq]; exact min_le_left _ _
    · rw [min_eq_right hAB]
      refine le_trans (min_le_right _ _) ?_
      have hAB' := hAB
      rw [div_le_div_iff₀ h2m h8s] at hAB'
      have hsumbound : 4 * sumK2 ≤ t * maxK := by nlinarith [hAB']
      have hdiff : 1 / (2 * maxK) * t - 4 * (1 / (2 * maxK)) ^ 2 * sumK2 - t / (4 * maxK)
          = (t * maxK - 4 * sumK2) / (4 * maxK ^ 2) := by field_simp; ring
      have hpos : (0 : ℝ) ≤ (t * maxK - 4 * sumK2) / (4 * maxK ^ 2) :=
        div_nonneg (by linarith [hsumbound]) (le_of_lt h4m2)
      linarith [hdiff, hpos]
  -- Assemble the real-valued exponent bound.
  have hRHS : Real.exp (-lam * t) * mgf (∑ i, X i) μ lam
      ≤ Real.exp (-(min (t ^ 2 / (16 * sumK2)) (t / (4 * maxK)))) := by
    have hstep : Real.exp (-lam * t) * mgf (∑ i, X i) μ lam
        ≤ Real.exp (-lam * t) * Real.exp (4 * lam ^ 2 * sumK2) :=
      mul_le_mul_of_nonneg_left hmgf_sum_le (Real.exp_nonneg _)
    rw [← Real.exp_add] at hstep
    refine le_trans hstep ?_
    apply Real.exp_le_exp.mpr
    linarith [hkey]
  -- Convert to `ENNReal` and conclude.
  have hset : {ω | t ≤ ∑ i, X i ω} = {ω | t ≤ (∑ i, X i) ω} := by
    ext ω; simp only [Finset.sum_apply]
  rw [hset, ← ENNReal.ofReal_toReal (measure_ne_top μ {ω | t ≤ (∑ i, X i) ω})]
  apply ENNReal.ofReal_le_ofReal
  calc (μ {ω | t ≤ (∑ i, X i) ω}).toReal
      = μ.real {ω | t ≤ (∑ i, X i) ω} := rfl
    _ ≤ Real.exp (-lam * t) * mgf (∑ i, X i) μ lam := chern
    _ ≤ Real.exp (-(min (t ^ 2 / (16 * sumK2)) (t / (4 * maxK)))) := hRHS

/-- **Bernstein's inequality, ψ₁-norm form** (HDP §2.9, Theorem 2.9.1; the
book's absolute constant realized as `c = 1/16` quadratic / `1/4` linear):
two-sided tail for sums of independent mean-zero sub-exponential variables.
Name avoids the taken `bernstein_inequality` (moment-condition version in
`Bernstein/Bernstein.lean`). -/
theorem bernstein_subexponential
    -- LEAN-ONLY: probability measure; Chernoff/MGF machinery requires it
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : Fin n → ℝ≥0}
    -- LEAN-ONLY: nonempty sum so max Kᵢ is well-defined
    (hn : 0 < n)
    -- LEAN-ONLY: measurability of each summand
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Thm 2.9.1
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero; HDP Thm 2.9.1
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive norm bounds (mild strengthening, see module notes)
    (hK : ∀ i, 0 < K i)
    -- USER-INPUT: ‖Xᵢ‖_{ψ₁} ≤ Kᵢ; HDP Thm 2.9.1
    (hnorm : ∀ i, subExponentialNorm (X i) μ ≤ K i)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Thm 2.9.1
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(min (t ^ 2 / (16 * ∑ i, (K i : ℝ) ^ 2))
        (t / (4 * ((Finset.univ.sup K : ℝ≥0) : ℝ))))))  := by
  -- Upper tail via the one-sided engine.
  have hEngine := measure_sum_ge_le_of_subExponentialNorm_le hn hmeas hindep hmean hK hnorm ht
  -- Lower tail: apply the engine to `−X` (ψ₁ norm is sign-invariant).
  have hmeasY : ∀ i, Measurable (fun ω => -(X i ω)) := fun i => (hmeas i).neg
  have hindepY : iIndepFun (fun i ω => -(X i ω)) μ := by
    have := hindep.comp (fun _ : Fin n => (Neg.neg : ℝ → ℝ)) (fun _ => measurable_neg)
    exact this
  have hmeanY : ∀ i, ∫ x, -(X i x) ∂μ = 0 := by
    intro i; rw [integral_neg, hmean i, neg_zero]
  have hnormY : ∀ i, subExponentialNorm (fun ω => -(X i ω)) μ ≤ K i := by
    intro i
    rw [subExponentialNorm_def, orliczNorm_neg, ← subExponentialNorm_def]
    exact hnorm i
  have hEngineY := measure_sum_ge_le_of_subExponentialNorm_le (X := fun i ω => -(X i ω))
    hn hmeasY hindepY hmeanY hK hnormY ht
  -- `{t ≤ |∑X|} ⊆ {t ≤ ∑X} ∪ {t ≤ ∑(−Xᵢ)}`.
  have hsub : {ω | t ≤ |∑ i, X i ω|}
      ⊆ {ω | t ≤ ∑ i, X i ω} ∪ {ω | t ≤ ∑ i, -(X i ω)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq, Finset.sum_neg_distrib]
      exact h
  calc μ {ω | t ≤ |∑ i, X i ω|}
      ≤ μ ({ω | t ≤ ∑ i, X i ω} ∪ {ω | t ≤ ∑ i, -(X i ω)}) := measure_mono hsub
    _ ≤ μ {ω | t ≤ ∑ i, X i ω} + μ {ω | t ≤ ∑ i, -(X i ω)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(min (t ^ 2 / (16 * ∑ i, (K i : ℝ) ^ 2))
          (t / (4 * ((Finset.univ.sup K : ℝ≥0) : ℝ))))))
        + ENNReal.ofReal (Real.exp (-(min (t ^ 2 / (16 * ∑ i, (K i : ℝ) ^ 2))
          (t / (4 * ((Finset.univ.sup K : ℝ≥0) : ℝ)))))) := add_le_add hEngine hEngineY
    _ = ENNReal.ofReal (2 * Real.exp (-(min (t ^ 2 / (16 * ∑ i, (K i : ℝ) ^ 2))
          (t / (4 * ((Finset.univ.sup K : ℝ≥0) : ℝ)))))) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]; congr 1; ring

/-- **Weighted Bernstein** (HDP Corollary 2.9.2; BONUS — this file's allowed
named-sorry debt): tail for `∑ aᵢ Xᵢ` with uniform ψ₁ bound `K`, exponent
`min (t²/(16 K² ‖a‖₂²)) (t/(4 K ‖a‖_∞))`. -/
theorem bernstein_subexponential_weighted
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin n → Ω → ℝ} {K : ℝ≥0}
    (a : Fin n → ℝ)
    -- LEAN-ONLY: nonempty sum
    (hn : 0 < n)
    -- LEAN-ONLY: nonzero weights (zero weights removable by reindexing)
    (ha : ∀ i, a i ≠ 0)
    -- LEAN-ONLY: measurability of each summand
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: independence; HDP Cor 2.9.2
    (hindep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: mean-zero; HDP Cor 2.9.2
    (hmean : ∀ i, ∫ x, X i x ∂μ = 0)
    -- LEAN-ONLY: positive uniform norm bound
    (hKpos : 0 < K)
    -- USER-INPUT: uniform ψ₁ bound ‖Xᵢ‖_{ψ₁} ≤ K; HDP Cor 2.9.2
    (hnorm : ∀ i, subExponentialNorm (X i) μ ≤ K)
    {t : ℝ}
    -- USER-INPUT: nonnegative threshold; HDP Cor 2.9.2
    (ht : 0 ≤ t) :
    μ {ω | t ≤ |∑ i, a i * X i ω|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-(min (t ^ 2 / (16 * (K : ℝ) ^ 2 * ∑ i, (a i) ^ 2))
          (t / (4 * (K : ℝ) *
            ((Finset.univ.sup fun i => ‖a i‖₊ : ℝ≥0) : ℝ)))))) := by
  -- Reduce to Theorem 2.9.1 for `Yᵢ = aᵢ Xᵢ` with scale `Kᵢ' = ‖aᵢ‖₊·K`.
  have hmeasY : ∀ i, Measurable (fun ω => a i * X i ω) := fun i => (hmeas i).const_mul (a i)
  have hindepY : iIndepFun (fun i ω => a i * X i ω) μ := by
    have := hindep.comp (fun i : Fin n => fun x : ℝ => a i * x)
      (fun i => measurable_id.const_mul (a i))
    exact this
  have hmeanY : ∀ i, ∫ x, a i * X i x ∂μ = 0 := by
    intro i; rw [integral_const_mul, hmean i, mul_zero]
  have hK' : ∀ i, 0 < ‖a i‖₊ * K := fun i => mul_pos (nnnorm_pos.mpr (ha i)) hKpos
  have hnormY : ∀ i, subExponentialNorm (fun ω => a i * X i ω) μ
      ≤ ((‖a i‖₊ * K : ℝ≥0) : ℝ≥0∞) := by
    intro i
    rw [subExponentialNorm_const_mul (ha i), ENNReal.coe_mul]
    exact mul_le_mul_right (hnorm i) _
  have hbern := bernstein_subexponential (X := fun i ω => a i * X i ω)
    (K := fun i => ‖a i‖₊ * K) hn hmeasY hindepY hmeanY hK' hnormY ht
  -- Rewrite the two aggregate scales into the corollary's ‖a‖₂, ‖a‖∞ form.
  have hcoe : ∀ i, ((‖a i‖₊ * K : ℝ≥0) : ℝ) ^ 2 = (K : ℝ) ^ 2 * (a i) ^ 2 := by
    intro i
    rw [NNReal.coe_mul, mul_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs]; ring
  have hsum_eq : (16 : ℝ) * ∑ i, ((‖a i‖₊ * K : ℝ≥0) : ℝ) ^ 2
      = 16 * (K : ℝ) ^ 2 * ∑ i, (a i) ^ 2 := by
    have hs : ∑ i, ((‖a i‖₊ * K : ℝ≥0) : ℝ) ^ 2 = (K : ℝ) ^ 2 * ∑ i, (a i) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => hcoe i)
    rw [hs]; ring
  have hsup_eq : (4 : ℝ) * ((Finset.univ.sup (fun i => ‖a i‖₊ * K) : ℝ≥0) : ℝ)
      = 4 * (K : ℝ) * ((Finset.univ.sup (fun i => ‖a i‖₊) : ℝ≥0) : ℝ) := by
    have hnn : Finset.univ.sup (fun i => ‖a i‖₊ * K)
        = (Finset.univ.sup (fun i => ‖a i‖₊)) * K := by rw [← NNReal.finset_sup_mul]
    rw [hnn, NNReal.coe_mul]; ring
  rw [hsum_eq, hsup_eq] at hbern
  exact hbern

end StatLean.ConcentrationInequalities
