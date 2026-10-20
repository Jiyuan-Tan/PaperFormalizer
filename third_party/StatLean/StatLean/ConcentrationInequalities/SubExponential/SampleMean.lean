module
public import StatLean.ConcentrationInequalities.SubExponential.Defs

@[expose] public section

/-!
# Sample-mean concentration of i.i.d. sub-exponentials (two-regime Bernstein bound)

Let $X_1, \dots, X_n$ be independent sub-exponential random variables with common
parameter $\alpha > 0$ and common mean $\mu_0$, and write
$\bar X_n = \tfrac1n \sum_{i=1}^n X_i$ for the sample mean. Then the upper tail of
the centered sample mean splits into two regimes around the threshold $t = \alpha$:

* **Quadratic regime** ($0 \le t \le \alpha$, `measure_sampleMean_lt_le_quadratic`):
  $$\Pr\bigl(\bar X_n - \mu_0 > t\bigr) \;\le\; \exp\!\Bigl(-\tfrac{n\,t^2}{2\alpha^2}\Bigr).$$
* **Linear regime** ($\alpha \le t$, `measure_sampleMean_lt_le_linear`):
  $$\Pr\bigl(\bar X_n - \mu_0 > t\bigr) \;\le\; \exp\!\Bigl(-\tfrac{n\,t}{2\alpha}\Bigr).$$

This is the classical Bernstein-type two-regime concentration bound for averages of
sub-exponential variables: Gaussian-like decay for small deviations and exponential
decay for large deviations.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 5 (Sub-exponential Random Variables), §5.2,
Theorem 5.2 (Sub-exponential Tail Probability).

**Proof formalization notes.** Chernoff route (book §5.2): decompose
$\bar X_n - \mu_0 = \sum_i \tfrac1n (X_i - \mu_0)$. By `iIndepFun.mgf_sum` the
moment generating function factors, and the per-variable sub-exponential bound on
each factor gives $\mathbb{E}[\exp(\lambda(\bar X_n - \mu_0))] \le \exp(\lambda^2\alpha^2/(2n))$
for $|\lambda| \le n/\alpha$. Minimising the Chernoff upper bound over $\lambda$
yields both regimes:
- Quadratic ($t \le \alpha$): optimal $\lambda = nt/\alpha^2$ gives $\exp(-nt^2/(2\alpha^2))$.
- Linear ($t \ge \alpha$): clamped $\lambda = n/\alpha$ gives
  $\exp(-nt/\alpha + n/2) \le \exp(-nt/(2\alpha))$ (using $n/2 \le nt/(2\alpha)$ since $t \ge \alpha$).

Deviation from book: Lu requires $t > 0$ (quadratic regime) and $t > \alpha$ (linear
regime); we prove the slightly stronger forms allowing $t = 0$ and $t = \alpha$
respectively. The strict `>` on the event matches the book; the underlying Chernoff
brick yields a `≥` bound, absorbed via the inclusion $\{t < Y\} \subseteq \{t \le Y\}$.

**Bibliographic comments.** This is a folklore result — a Bernstein-type
two-regime concentration inequality with no single seminal origin. Its lineage traces
to Bernstein's exponential moment inequalities (S. N. Bernstein, *Theory of
Probability*, 1927) and, in the modern sub-exponential / Orlicz-norm formulation, to
M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge
University Press, 2019 (Prop 2.9, sub-exponential tail bound). The two-regime split —
Gaussian decay for $t \lesssim \alpha$ and exponential decay for $t \gtrsim \alpha$ — is
the standard packaging of these results.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Product of `n` non-negative real factors, each bounded by `C`, is ≤ `C ^ n`. -/
private lemma prod_le_pow_of_le {n : ℕ} {f : Fin n → ℝ} {C : ℝ}
    (hf : ∀ i, 0 ≤ f i) (hfC : ∀ i, f i ≤ C) (hC : 0 ≤ C) :
    ∏ i : Fin n, f i ≤ C ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, pow_succ]
    exact mul_le_mul (ih (fun i => hf i.castSucc) (fun i => hfC i.castSucc))
      (hfC (Fin.last n)) (hf (Fin.last n)) (pow_nonneg hC n)

/-- **MGF bound for the sample mean** (intermediate lemma): for Chernoff parameter
`λ ∈ [0, n/α]`, `E[exp(λ (X̄ₙ − μ₀))] ≤ exp(λ² α² / (2n))`.

Proof: `X̄ₙ − μ₀ = ∑ᵢ (1/n)(Xᵢ − μ₀)`. By `iIndepFun.mgf_sum`, the MGF equals
`∏ᵢ mgf((1/n)(Xᵢ − μ₀), λ) = ∏ᵢ mgf(Xᵢ − μ₀, λ/n)`. Applying the sub-exponential
bound to each factor (valid since `|λ/n| ≤ 1/α`) and collecting the product yields
`exp(n · (λ/n)² α²/2) = exp(λ² α²/(2n))`. -/
private lemma mgf_sampleMean_le
    {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω} {μ₀ : ℝ}
    -- USER-INPUT: each X i is sub-exponential with parameter α; Lu-BDA §5.2
    (hX : ∀ i, IsSubExponential (X i) α μ)
    -- USER-INPUT: common mean μ₀; Lu-BDA §5.2
    (hμ₀ : ∀ i, ∫ ω, X i ω ∂μ = μ₀)
    -- USER-INPUT: the X i are mutually independent; Lu-BDA §5.2
    (hindep : iIndepFun X μ)
    -- USER-INPUT: α > 0; Lu-BDA §5.2
    (hα : 0 < (α : ℝ))
    -- LEAN-ONLY: measurability of each X i; required by iIndepFun.mgf_sum
    (hmeas : ∀ i, Measurable (X i))
    {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ (n : ℝ) / (α : ℝ)) :
    mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam
      ≤ Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ))) := by
  haveI hprob : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  haveI : IsFiniteMeasure μ := inferInstance
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  -- lam / n is in the valid sub-exponential range [0, 1/α]
  have h_lam_n_nn : 0 ≤ lam / (n : ℝ) := div_nonneg hlam_nn hn_pos.le
  have h_lam_n_le : lam / (n : ℝ) ≤ 1 / (α : ℝ) := by
    rw [div_le_div_iff₀ hn_pos hα, one_mul]
    exact (le_div_iff₀ hα).mp hlam_le
  -- Independence of scaled centered variables Y i ω = (1/n) * (X i ω − μ₀)
  have hindep_Y : iIndepFun (fun i ω => (1 / (n : ℝ)) * (X i ω - μ₀)) μ := by
    have h := hindep.comp (fun _ (x : ℝ) => (1 / (n : ℝ)) * (x - μ₀))
      (fun _ => measurable_const.mul (measurable_id.sub measurable_const))
    simpa [Function.comp_def] using h
  -- Measurability of Y i
  have hmeas_Y : ∀ i, Measurable (fun ω => (1 / (n : ℝ)) * (X i ω - μ₀)) :=
    fun i => measurable_const.mul ((hmeas i).sub measurable_const)
  -- MGF factorisation: mgf (∑ᵢ Y i) μ lam = ∏ᵢ mgf (Y i) μ lam
  have hfact : mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam
      = ∏ i : Fin n, mgf (fun ω => (1 / (n : ℝ)) * (X i ω - μ₀)) μ lam := by
    have h := hindep_Y.mgf_sum (t := lam) hmeas_Y (Finset.univ : Finset (Fin n))
    convert h using 2
    funext ω
    simp [Finset.sum_apply]
  -- Per-factor MGF bound: mgf (Y i) μ lam ≤ exp((lam/n)² α²/2)
  have hfactor_bound : ∀ i : Fin n,
      mgf (fun ω => (1 / (n : ℝ)) * (X i ω - μ₀)) μ lam
        ≤ Real.exp ((lam / (n : ℝ)) ^ 2 * (α : ℝ) ^ 2 / 2) := by
    intro i
    -- mgf ((1/n) • Z) μ lam = mgf Z μ ((1/n) * lam)
    rw [show (fun ω => (1 / (n : ℝ)) * (X i ω - μ₀)) =
          (1 / (n : ℝ)) • (fun ω => X i ω - μ₀) from funext (fun ω => by simp [smul_eq_mul])]
    rw [mgf_smul_left]
    -- X i ω - μ₀ = X i ω - ∫ X i ∂μ (by hμ₀ i)
    rw [show (fun ω => X i ω - μ₀) = (fun ω => X i ω - ∫ x, X i x ∂μ) from
          funext (fun ω => by rw [hμ₀ i])]
    -- Apply sub-exponential bound at λ/n
    have hval : (1 / (n : ℝ)) * lam = lam / (n : ℝ) := by ring
    rw [hval]
    exact (hX i).mgf_le_of_mem_Icc h_lam_n_nn h_lam_n_le
  -- Combine: product ≤ exp((lam/n)² α²/2)^n = exp(lam² α²/(2n))
  rw [hfact]
  calc ∏ i : Fin n, mgf (fun ω => (1 / (n : ℝ)) * (X i ω - μ₀)) μ lam
      ≤ Real.exp ((lam / (n : ℝ)) ^ 2 * (α : ℝ) ^ 2 / 2) ^ n :=
        prod_le_pow_of_le (fun _ => mgf_nonneg) hfactor_bound (Real.exp_pos _).le
    _ = Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp

/-- **Integrability of exp(λ (X̄ₙ − μ₀))** for `λ ∈ [0, n/α]`, from independence and
the per-variable integrability supplied by `IsSubExponential.integrable_exp_mul`. -/
private lemma integrable_exp_sampleMean
    {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω} {μ₀ : ℝ}
    (hX : ∀ i, IsSubExponential (X i) α μ)
    (hμ₀ : ∀ i, ∫ ω, X i ω ∂μ = μ₀)
    (hindep : iIndepFun X μ)
    (hα : 0 < (α : ℝ))
    (hmeas : ∀ i, Measurable (X i))
    {lam : ℝ} (hlam_nn : 0 ≤ lam) (hlam_le : lam ≤ (n : ℝ) / (α : ℝ)) :
    Integrable (fun ω => Real.exp (lam * ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀)))) μ := by
  haveI hprob : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  haveI hfin : IsFiniteMeasure μ := inferInstance
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_lam_n_nn : 0 ≤ lam / (n : ℝ) := div_nonneg hlam_nn hn_pos.le
  have h_lam_n_le : lam / (n : ℝ) ≤ 1 / (α : ℝ) := by
    rw [div_le_div_iff₀ hn_pos hα, one_mul]
    exact (le_div_iff₀ hα).mp hlam_le
  -- Scaled centered Y i
  have hindep_Y : iIndepFun (fun i ω => (1 / (n : ℝ)) * (X i ω - μ₀)) μ := by
    have h := hindep.comp (fun _ (x : ℝ) => (1 / (n : ℝ)) * (x - μ₀))
      (fun _ => measurable_const.mul (measurable_id.sub measurable_const))
    simpa [Function.comp_def] using h
  have hmeas_Y : ∀ i, Measurable (fun ω => (1 / (n : ℝ)) * (X i ω - μ₀)) :=
    fun i => measurable_const.mul ((hmeas i).sub measurable_const)
  -- Individual integrability: exp(lam * Y i) = exp((lam/n) * (X i - ∫ X i))
  have h_int_i : ∀ i : Fin n,
      Integrable (fun ω => Real.exp (lam * ((1 / (n : ℝ)) * (X i ω - μ₀)))) μ := by
    intro i
    have hrw : (fun ω => Real.exp (lam * ((1 / (n : ℝ)) * (X i ω - μ₀)))) =
        fun ω => Real.exp ((lam / (n : ℝ)) * (X i ω - ∫ x, X i x ∂μ)) := by
      ext ω; congr 1; rw [← hμ₀ i]; ring
    rw [hrw]
    exact (hX i).integrable_exp_mul (lam / (n : ℝ))
      (by rwa [abs_of_nonneg h_lam_n_nn])
  -- Sum integrability from independence + individual integrabilities
  have h_sum := hindep_Y.integrable_exp_mul_sum hmeas_Y (s := Finset.univ)
    (fun i _ => h_int_i i)
  -- Match the form: exp(lam * ∑ i, Y i ω) vs exp(lam * (∑ i, Y i) ω)
  simp only [Finset.sum_apply] at h_sum
  exact h_sum

/-- **Quadratic-regime sample-mean concentration** (Lu-BDA §5.2, quadratic case).

For `n` independent sub-exponential `(α)` variables `X 1, …, X n` with common
mean `μ₀` and `0 ≤ t ≤ α`,
`μ {(1/n) ∑ᵢ Xᵢ − μ₀ > t} ≤ exp(−n t² / (2α²))`.

Deviation from book: Lu requires `t > 0`; we prove the stronger form with `t ≥ 0`.
The strict `<` on the event is faithful to the book; the Chernoff brick gives `≤`,
absorbed via `{t < Y} ⊆ {t ≤ Y}`. -/
theorem measure_sampleMean_lt_le_quadratic
    {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω} {μ₀ : ℝ}
    -- USER-INPUT: each X i is sub-exponential with parameter α; Lu-BDA §5.2
    (hX : ∀ i, IsSubExponential (X i) α μ)
    -- USER-INPUT: common mean μ₀; Lu-BDA §5.2
    (hμ₀ : ∀ i, ∫ ω, X i ω ∂μ = μ₀)
    -- USER-INPUT: the X i are mutually independent; Lu-BDA §5.2
    (hindep : iIndepFun X μ)
    -- USER-INPUT: α > 0; Lu-BDA §5.2
    (hα : 0 < (α : ℝ))
    -- LEAN-ONLY: measurability of each X i; required by iIndepFun.mgf_sum
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: 0 ≤ t; Lu-BDA §5.2
    {t : ℝ} (ht : 0 ≤ t)
    -- USER-INPUT: t ≤ α (quadratic regime); Lu-BDA §5.2
    (htα : t ≤ (α : ℝ)) :
    μ {ω | t < (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ₀}
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (2 * (α : ℝ) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  haveI hfin : IsFiniteMeasure μ := inferInstance
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  -- Algebraic identity: (1/n) ∑ X i - μ₀ = ∑ (1/n) * (X i - μ₀)
  have halg : ∀ ω, (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ₀ =
      ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀)) := by
    intro ω
    rw [Finset.mul_sum]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    field_simp
  -- Rewrite event
  have hset_eq : {ω | t < (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ₀} =
      {ω | t < ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))} :=
    Set.ext (fun ω => by simp only [Set.mem_setOf_eq, halg ω])
  rw [hset_eq]
  -- Chernoff parameter: λ = n·t/α² (optimal; lies in [0, n/α] since t ≤ α)
  set lam := (n : ℝ) * t / (α : ℝ) ^ 2 with hlam_def
  have hlam_nn : 0 ≤ lam := div_nonneg (mul_nonneg hn_pos.le ht) (sq_nonneg _)
  have hlam_le : lam ≤ (n : ℝ) / (α : ℝ) := by
    rw [hlam_def, div_le_div_iff₀ (sq_pos_of_pos hα) hα]
    nlinarith [mul_nonneg hn_pos.le hα.le]
  -- Integrability of exp(lam · (X̄ₙ − μ₀))
  have h_int : Integrable (fun ω => Real.exp (lam * ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀)))) μ :=
    integrable_exp_sampleMean hn hX hμ₀ hindep hα hmeas hlam_nn hlam_le
  -- Chernoff brick: μ.real {t ≤ Z} ≤ exp(-lam · t) · mgf Z μ lam
  have hchernoff :
      μ.real {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
        ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam :=
    measure_ge_le_exp_mul_mgf t hlam_nn h_int
  -- MGF bound
  have hmgf : mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam
      ≤ Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ))) :=
    mgf_sampleMean_le hn hX hμ₀ hindep hα hmeas hlam_nn hlam_le
  -- Arithmetic: exp(-lam·t) · exp(lam²α²/(2n)) = exp(-nt²/(2α²))  (lam = nt/α²)
  have hexp_eq : Real.exp (-lam * t) * Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ)))
      = Real.exp (-(n : ℝ) * t ^ 2 / (2 * (α : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [hlam_def]
    field_simp; ring
  -- Combine into the real-valued bound
  have hbrick : μ.real {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
      ≤ Real.exp (-(n : ℝ) * t ^ 2 / (2 * (α : ℝ) ^ 2)) :=
    calc μ.real {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
        ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam :=
          hchernoff
      _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-(n : ℝ) * t ^ 2 / (2 * (α : ℝ) ^ 2)) := hexp_eq
  -- Lift from μ.real to μ via strict ⊆ and ENNReal bridge
  have hsub : {ω | t < ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
      ⊆ {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))} := by
    intro ω hω; exact (Set.mem_setOf_eq.mp hω).le
  calc μ {ω | t < ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
      ≤ μ {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (2 * (α : ℝ) ^ 2))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal hbrick

/-- **Linear-regime sample-mean concentration** (Lu-BDA §5.2, linear case).

For `n` independent sub-exponential `(α)` variables `X 1, …, X n` with common
mean `μ₀` and `α ≤ t`,
`μ {(1/n) ∑ᵢ Xᵢ − μ₀ > t} ≤ exp(−n t / (2α))`.

Proof: Chernoff at the clamped `λ = n/α` gives `exp(−nt/α + n/2)`;
since `α ≤ t` implies `n/2 ≤ nt/(2α)`, we obtain `exp(−nt/α + n/2) ≤ exp(−nt/(2α))`.

Deviation from book: Lu uses strict `t > α`; we allow equality. -/
theorem measure_sampleMean_lt_le_linear
    {n : ℕ} (hn : 0 < n)
    {X : Fin n → Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω} {μ₀ : ℝ}
    -- USER-INPUT: each X i is sub-exponential with parameter α; Lu-BDA §5.2
    (hX : ∀ i, IsSubExponential (X i) α μ)
    -- USER-INPUT: common mean μ₀; Lu-BDA §5.2
    (hμ₀ : ∀ i, ∫ ω, X i ω ∂μ = μ₀)
    -- USER-INPUT: the X i are mutually independent; Lu-BDA §5.2
    (hindep : iIndepFun X μ)
    -- USER-INPUT: α > 0; Lu-BDA §5.2
    (hα : 0 < (α : ℝ))
    -- LEAN-ONLY: measurability of each X i; required by iIndepFun.mgf_sum
    (hmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: α ≤ t (linear regime); Lu-BDA §5.2
    {t : ℝ} (htα : (α : ℝ) ≤ t) :
    μ {ω | t < (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ₀}
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t / (2 * (α : ℝ)))) := by
  haveI hprob : IsProbabilityMeasure μ := hindep.isProbabilityMeasure
  haveI hfin : IsFiniteMeasure μ := inferInstance
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have ht : 0 ≤ t := le_trans hα.le htα
  -- Algebraic identity
  have halg : ∀ ω, (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ₀ =
      ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀)) := by
    intro ω
    rw [Finset.mul_sum]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    field_simp
  have hset_eq : {ω | t < (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ₀} =
      {ω | t < ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))} :=
    Set.ext (fun ω => by simp only [Set.mem_setOf_eq, halg ω])
  rw [hset_eq]
  -- Chernoff parameter: λ = n/α (clamped at the boundary of the valid range)
  set lam := (n : ℝ) / (α : ℝ) with hlam_def
  have hlam_nn : 0 ≤ lam := div_nonneg hn_pos.le hα.le
  have hlam_le : lam ≤ (n : ℝ) / (α : ℝ) := le_refl _
  -- Integrability
  have h_int : Integrable (fun ω => Real.exp (lam * ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀)))) μ :=
    integrable_exp_sampleMean hn hX hμ₀ hindep hα hmeas hlam_nn hlam_le
  -- Chernoff brick
  have hchernoff :
      μ.real {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
        ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam :=
    measure_ge_le_exp_mul_mgf t hlam_nn h_int
  -- MGF bound
  have hmgf : mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam
      ≤ Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ))) :=
    mgf_sampleMean_le hn hX hμ₀ hindep hα hmeas hlam_nn hlam_le
  -- Arithmetic: exp(-lam·t) · exp(lam²α²/(2n)) ≤ exp(-nt/(2α))
  -- With lam = n/α: LHS = exp(-nt/α + n/2); since α ≤ t, n/2 ≤ nt/(2α), so LHS ≤ exp(-nt/(2α))
  have hexp_le : Real.exp (-lam * t) * Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ)))
      ≤ Real.exp (-(n : ℝ) * t / (2 * (α : ℝ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- Simplify LHS exponent: with lam = n/α: -(n/α)·t + (n/α)²·α²/(2n) = -nt/α + n/2
    have hLHS : -lam * t + lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ))
        = -(t / (α : ℝ)) * (n : ℝ) + (n : ℝ) / 2 := by
      simp only [hlam_def]; field_simp
    -- Simplify RHS exponent: -(n·t)/(2α) = -(t/α)·n/2
    have hRHS : -(n : ℝ) * t / (2 * (α : ℝ)) = -(t / (α : ℝ)) * (n : ℝ) / 2 := by ring
    rw [hLHS, hRHS]
    -- Goal: -(t/α)·n + n/2 ≤ -(t/α)·n/2, i.e., n/2 ≤ (t/α)·n/2, i.e., 1 ≤ t/α
    have htdivα : 1 ≤ t / (α : ℝ) := by
      rw [le_div_iff₀ hα]; linarith
    nlinarith [mul_nonneg hn_pos.le (div_nonneg ht hα.le)]
  -- Combine
  have hbrick : μ.real {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
      ≤ Real.exp (-(n : ℝ) * t / (2 * (α : ℝ))) :=
    calc μ.real {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
        ≤ Real.exp (-lam * t) * mgf (fun ω => ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))) μ lam :=
          hchernoff
      _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * (α : ℝ) ^ 2 / (2 * (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ ≤ Real.exp (-(n : ℝ) * t / (2 * (α : ℝ))) := hexp_le
  -- ENNReal bridge
  have hsub : {ω | t < ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
      ⊆ {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))} := by
    intro ω hω; exact (Set.mem_setOf_eq.mp hω).le
  calc μ {ω | t < ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))}
      ≤ μ {ω | t ≤ ∑ i : Fin n, ((1 / (n : ℝ)) * (X i ω - μ₀))} :=
        measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t / (2 * (α : ℝ)))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal hbrick

end StatLean.ConcentrationInequalities
