module
public import StatLean.ConcentrationInequalities.SubExponential.Defs

@[expose] public section

/-!
# Sub-Exponential Tail Probability

Let $X$ be a sub-exponential random variable with parameter $\alpha > 0$, and write
$Y = X - \mathbb{E}[X]$ for its centering. The sub-exponential tail probability exhibits
two regimes governed by the deviation level $t$ relative to $\alpha$:

* **Quadratic regime** (small deviations, $0 \le t \le \alpha$):
  $$\mathbb{P}\bigl(Y > t\bigr) \le \exp\!\left(-\frac{t^2}{2\alpha^2}\right).$$
* **Linear regime** (large deviations, $t \ge \alpha$):
  $$\mathbb{P}\bigl(Y > t\bigr) \le \exp\!\left(-\frac{t}{2\alpha}\right).$$

For small deviations the tail decays like that of a sub-Gaussian variable (Gaussian
$\exp(-t^2/2\alpha^2)$ shape); for large deviations the lighter, purely exponential
$\exp(-t/2\alpha)$ decay takes over. The crossover occurs at $t = \alpha$, where the two
bounds agree.

Formalized here as:

* `IsSubExponential.measure_sub_integral_lt_le_quadratic` — quadratic regime
  $\mu\{t < Y\} \le \exp(-t^2/2\alpha^2)$ for $0 \le t \le \alpha$.
* `IsSubExponential.measure_sub_integral_lt_le_linear` — linear regime
  $\mu\{t < Y\} \le \exp(-t/2\alpha)$ for $\alpha \le t$.

**Added hypotheses / changed constants.** We require $\alpha > 0$ explicitly. In the
quadratic regime we allow $t = 0$ (the book states $t > 0$); the bound is then the trivial
$\mu(\cdot) \le 1$. In the linear regime we allow the equality $t = \alpha$ (the book uses
strict $t > \alpha$); this yields the same value as the quadratic bound at the crossing
point. The events use a strict inequality $t < Y$, faithful to the textbook; the Chernoff
brick supplies the bound on $\{t \le Y\} \supseteq \{t < Y\}$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 5 (Sub-exponential Random Variables), §5.2,
Theorem 5.2 (Sub-exponential Tail Probability).

**Proof formalization notes.** Both bounds follow from the one-sided Chernoff bound
  $\mu\{t < Y\} \le \exp(-\lambda t)\,\mathrm{MGF}_Y(\lambda) \le \exp(-\lambda t + \lambda^2\alpha^2/2)$
using `mgf_le_of_mem_Icc`, then optimizing the free parameter $\lambda \in [0, 1/\alpha]$:
- Quadratic regime: the optimal $\lambda = t/\alpha^2$ lies in range when $t \le \alpha$; gives $\exp(-t^2/2\alpha^2)$.
- Linear regime: clamp $\lambda = 1/\alpha$; the residual $1/2 \le t/(2\alpha)$ (from $\alpha \le t$) absorbs the slack.

Mathlib brick: `ProbabilityTheory.measure_ge_le_exp_mul_mgf`
(in `Mathlib.Probability.Moments.Basic`, transitively via `SubGaussian`).

`IsFiniteMeasure μ` is derived privately from `integrable_exp_mul` at `l = 0`,
mirroring the pattern in `SubGaussian/TailBounds.lean`.

**Bibliographic comments.** The two-regime sub-exponential tail bound is folklore
with no single seminal origin; it is the standard packaging of the sub-exponential MGF
condition into a deviation inequality via the Chernoff method. A standard modern reference
giving precisely this two-regime ($\exp(-ct^2)$ for small $t$, $\exp(-ct)$ for large $t$)
statement is M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic
Viewpoint*, Cambridge University Press, 2019, §2.1.3 (Proposition 2.9, sub-exponential tail
bound). The underlying Chernoff bounding technique originates with H. Chernoff, "A measure
of asymptotic efficiency for tests of a hypothesis based on the sum of observations,"
*Annals of Mathematical Statistics* 23(4):493–507, 1952.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsSubExponential` forces the underlying measure to be finite: the
integrability of `exp(0 · (X − E[X])) = 1` bundled in `integrable_exp_mul`
is equivalent to `IsFiniteMeasure μ`. -/
private lemma IsSubExponential.isFiniteMeasure
    {X : Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω} (hX : IsSubExponential X α μ) :
    IsFiniteMeasure μ := by
  have h0 : |(0 : ℝ)| ≤ 1 / (α : ℝ) := by
    rw [abs_zero]
    exact div_nonneg zero_le_one (NNReal.coe_nonneg α)
  have h := hX.integrable_exp_mul 0 h0
  simp only [zero_mul, Real.exp_zero] at h
  exact (integrable_const_iff_isFiniteMeasure (one_ne_zero)).mp h

/-- **Quadratic-regime sub-exponential tail bound** (Lu-BDA §5.2, Theorem 5.2
(Sub-exponential Tail Probability), quadratic case).

If `X` is sub-exponential with parameter `α > 0` under `μ`, then for `0 ≤ t ≤ α`,
`μ {ω | t < X ω − ∫ X dμ} ≤ exp(−t²/(2α²))`.

Proof: Chernoff at the optimal `λ = t/α²` (lies in `[0, 1/α]` since `t ≤ α`);
the MGF field gives `exp(−λt + λ²α²/2) = exp(−t²/(2α²))`.

Deviation from book: Lu requires `t > 0`; we allow `t = 0` (the bound is trivially
`μ(·) ≤ 1`, which follows from `exp(0) = 1` and total mass `≤ 1`). The strict `<`
on the event is faithful; the Chernoff brick gives `≤`, absorbed via `{t < Y} ⊆ {t ≤ Y}`. -/
theorem IsSubExponential.measure_sub_integral_lt_le_quadratic
    {X : Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω}
    (hX : IsSubExponential X α μ)
    -- USER-INPUT: α > 0; Lu-BDA §5.2 Theorem 5.2
    (hα : 0 < (α : ℝ))
    -- USER-INPUT: 0 ≤ t; Lu-BDA §5.2 Theorem 5.2
    {t : ℝ} (ht : 0 ≤ t)
    -- USER-INPUT: t ≤ α (quadratic regime); Lu-BDA §5.2 Theorem 5.2
    (htα : t ≤ (α : ℝ)) :
    μ {ω | t < X ω - ∫ x, X x ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (α : ℝ) ^ 2))) := by
  haveI := hX.isFiniteMeasure
  -- Chernoff parameter: λ = t / α²  (the unconstrained optimizer)
  set s := t / (α : ℝ) ^ 2 with hs_def
  have hs_nn : 0 ≤ s := div_nonneg ht (sq_nonneg _)
  -- λ ≤ 1/α holds because t ≤ α
  have hs_le : s ≤ 1 / (α : ℝ) := by
    rw [hs_def, div_le_div_iff₀ (sq_pos_of_pos hα) hα]
    calc t * (α : ℝ) ≤ (α : ℝ) * (α : ℝ) := mul_le_mul_of_nonneg_right htα hα.le
      _ = 1 * (α : ℝ) ^ 2 := by ring
  -- Chernoff brick: μ.real {t ≤ Y} ≤ exp(−λt) · mgf Y λ
  have hchernoff :
      μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ}
        ≤ Real.exp (-s * t) * mgf (fun ω => X ω - ∫ x, X x ∂μ) μ s :=
    measure_ge_le_exp_mul_mgf t hs_nn
      (hX.integrable_exp_mul s (by rwa [abs_of_nonneg hs_nn]))
  -- MGF bound: mgf Y λ ≤ exp(λ²α²/2)
  have hmgf : mgf (fun ω => X ω - ∫ x, X x ∂μ) μ s
      ≤ Real.exp (s ^ 2 * (α : ℝ) ^ 2 / 2) :=
    hX.mgf_le_of_mem_Icc hs_nn hs_le
  -- Arithmetic: exp(−λt) · exp(λ²α²/2) = exp(−t²/(2α²))   (λ = t/α²)
  have hexp_eq : Real.exp (-s * t) * Real.exp (s ^ 2 * (α : ℝ) ^ 2 / 2)
      = Real.exp (-t ^ 2 / (2 * (α : ℝ) ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [hs_def]
    field_simp [hα.ne']
    ring
  -- Combine: μ.real {t ≤ Y} ≤ exp(−t²/(2α²))
  have hbrick : μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ}
      ≤ Real.exp (-t ^ 2 / (2 * (α : ℝ) ^ 2)) :=
    calc μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ}
        ≤ Real.exp (-s * t) * mgf (fun ω => X ω - ∫ x, X x ∂μ) μ s := hchernoff
      _ ≤ Real.exp (-s * t) * Real.exp (s ^ 2 * (α : ℝ) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-t ^ 2 / (2 * (α : ℝ) ^ 2)) := hexp_eq
  -- Lift from μ.real to μ (strict ⊆ non-strict; ENNReal bridge)
  have hsub : {ω | t < X ω - ∫ x, X x ∂μ}
      ⊆ {ω | t ≤ X ω - ∫ x, X x ∂μ} := by
    intro ω hω
    have hω' : t < X ω - ∫ x, X x ∂μ := hω
    exact hω'.le
  calc μ {ω | t < X ω - ∫ x, X x ∂μ}
      ≤ μ {ω | t ≤ X ω - ∫ x, X x ∂μ} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (α : ℝ) ^ 2))) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
          exact ENNReal.ofReal_le_ofReal hbrick

/-- **Linear-regime sub-exponential tail bound** (Lu-BDA §5.2, Theorem 5.2
(Sub-exponential Tail Probability), linear case).

If `X` is sub-exponential with parameter `α > 0` under `μ`, then for `α ≤ t`,
`μ {ω | t < X ω − ∫ X dμ} ≤ exp(−t/(2α))`.

Proof: Chernoff at the clamped `λ = 1/α` gives `exp(−t/α + 1/2)`;
since `α ≤ t` implies `1/2 ≤ t/(2α)`, we conclude `exp(−t/α + 1/2) ≤ exp(−t/(2α))`.

Deviation from book: the book uses strict `t > α`; we allow equality `t = α` (yields
the same bound as the quadratic regime at the crossing point). -/
theorem IsSubExponential.measure_sub_integral_lt_le_linear
    {X : Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω}
    (hX : IsSubExponential X α μ)
    -- USER-INPUT: α > 0; Lu-BDA §5.2 Theorem 5.2
    (hα : 0 < (α : ℝ))
    -- USER-INPUT: α ≤ t (linear regime); Lu-BDA §5.2 Theorem 5.2
    {t : ℝ} (htα : (α : ℝ) ≤ t) :
    μ {ω | t < X ω - ∫ x, X x ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-t / (2 * (α : ℝ)))) := by
  haveI := hX.isFiniteMeasure
  have ht : 0 ≤ t := le_trans hα.le htα
  -- Chernoff parameter: λ = 1/α  (clamped at the boundary of the valid range)
  set s := 1 / (α : ℝ) with hs_def
  have hs_nn : 0 ≤ s := div_nonneg zero_le_one hα.le
  have hs_le : s ≤ 1 / (α : ℝ) := le_refl _
  -- Chernoff brick: μ.real {t ≤ Y} ≤ exp(−λt) · mgf Y λ
  have hchernoff :
      μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ}
        ≤ Real.exp (-s * t) * mgf (fun ω => X ω - ∫ x, X x ∂μ) μ s :=
    measure_ge_le_exp_mul_mgf t hs_nn
      (hX.integrable_exp_mul s (by rw [abs_of_nonneg hs_nn]))
  -- MGF bound: mgf Y λ ≤ exp(λ²α²/2) = exp(1/2)
  have hmgf : mgf (fun ω => X ω - ∫ x, X x ∂μ) μ s
      ≤ Real.exp (s ^ 2 * (α : ℝ) ^ 2 / 2) :=
    hX.mgf_le_of_mem_Icc hs_nn hs_le
  -- Arithmetic: exp(−λt) · exp(λ²α²/2) ≤ exp(−t/(2α))
  -- With λ=1/α: LHS = exp(−t/α + 1/2); need −t/α + 1/2 ≤ −t/(2α), i.e., 1/2 ≤ t/(2α)
  have hexp_le : Real.exp (-s * t) * Real.exp (s ^ 2 * (α : ℝ) ^ 2 / 2)
      ≤ Real.exp (-t / (2 * (α : ℝ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    -- Simplify LHS to −t/α + 1/2
    have h1 : (1 / (α : ℝ)) ^ 2 * (α : ℝ) ^ 2 = 1 := by field_simp
    have hLHS : -s * t + s ^ 2 * (α : ℝ) ^ 2 / 2 = -(t / (α : ℝ)) + 1 / 2 := by
      simp only [hs_def]; rw [h1]; ring
    -- Rewrite RHS as −(t/α)/2
    have hRHS : -t / (2 * (α : ℝ)) = -(t / (α : ℝ)) / 2 := by ring
    rw [hLHS, hRHS]
    -- Goal: −(t/α) + 1/2 ≤ −(t/α)/2
    -- Equivalently: 1/2 ≤ (t/α)/2, i.e., 1 ≤ t/α
    have htdivα : 1 ≤ t / (α : ℝ) := by
      rw [le_div_iff₀ hα]; linarith
    linarith
  -- Combine: μ.real {t ≤ Y} ≤ exp(−t/(2α))
  have hbrick : μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ}
      ≤ Real.exp (-t / (2 * (α : ℝ))) :=
    calc μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ}
        ≤ Real.exp (-s * t) * mgf (fun ω => X ω - ∫ x, X x ∂μ) μ s := hchernoff
      _ ≤ Real.exp (-s * t) * Real.exp (s ^ 2 * (α : ℝ) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ ≤ Real.exp (-t / (2 * (α : ℝ))) := hexp_le
  -- Lift from μ.real to μ (strict ⊆ non-strict; ENNReal bridge)
  have hsub : {ω | t < X ω - ∫ x, X x ∂μ}
      ⊆ {ω | t ≤ X ω - ∫ x, X x ∂μ} := by
    intro ω hω
    have hω' : t < X ω - ∫ x, X x ∂μ := hω
    exact hω'.le
  calc μ {ω | t < X ω - ∫ x, X x ∂μ}
      ≤ μ {ω | t ≤ X ω - ∫ x, X x ∂μ} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-t / (2 * (α : ℝ)))) := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
          exact ENNReal.ofReal_le_ofReal hbrick

end StatLean.ConcentrationInequalities
