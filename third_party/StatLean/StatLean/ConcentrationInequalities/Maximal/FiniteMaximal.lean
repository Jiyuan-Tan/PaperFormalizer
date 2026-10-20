module
public import StatLean.ConcentrationInequalities.SubGaussian.TailBounds
public import Mathlib.Data.Fintype.Order
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# Finite Maximal Inequality for Sub-Gaussian Variables

Let $X_1, \dots, X_d$ ($d \ge 1$) be (not necessarily independent) sub-Gaussian random
variables with variance proxy $\sigma^2$ and mean zero, $\mathbb{E}[X_j] = 0$ for every
$j$. Then:

* **Tail bound.** For every $t \ge 0$,
  $$\mathbb{P}\!\Big(\max_{1 \le j \le d} X_j > t\Big) \le d\, e^{-t^2/(2\sigma^2)}.$$
* **Expectation bound.** Under a probability measure,
  $$\mathbb{E}\!\Big[\max_{1 \le j \le d} X_j\Big] \le \sigma\sqrt{2\log d}.$$

In the Lean statements the finite maximum is written as the supremum
$\bigvee_{j} X_j$ over the index set $\{1, \dots, d\}$ (the supremum equals the
pointwise maximum once $d \ge 1$), and $\sigma$ is recovered as $\sqrt{\sigma^2}$.

**Deviation from the book.** The book states the tail bound for $t > 0$; we allow
$t \ge 0$ throughout, which is strictly stronger. The book's high-probability form
"$\max_j X_j \le \sigma\sqrt{2\log(d/\delta)}$ with probability at least $1-\delta$" is
the same statement as the tail bound after substituting $\delta = d\,e^{-t^2/(2\sigma^2)}$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 6 (Bernstein and Maximal Inequalities), §6.2,
Theorem 6.2 (Finite Maximal Inequality).
The expectation bound is the first display of the theorem; the tail bound is the union
bound established in its proof.

**Proof formalization notes.**

The tail bound (`tail_max_le`) is proved via a union bound: the event
$\{\max_j X_j > t\}$ is the union of the events $\{X_j > t\}$, each bounded by
$e^{-t^2/(2\sigma^2)}$ via `IsSubGaussian.measure_sub_integral_lt_le` (centeredness
kills the $-\int X_j$ shift).

The expectation bound (`expectation_max_le`) uses the Jensen + MGF argument: for
$\lambda > 0$,
$$e^{\lambda\,\mathbb{E}[\max]} \le \mathbb{E}[e^{\lambda\max}]
  \le \sum_j \mathbb{E}[e^{\lambda X_j}] \le d\, e^{\sigma^2\lambda^2/2}.$$
Taking logs and dividing by $\lambda$ gives
$\mathbb{E}[\max] \le \tfrac{\log d}{\lambda} + \tfrac{\sigma^2\lambda}{2}$; optimising
at $\lambda^\star = \sqrt{2\log d / \sigma^2}$ yields $\sigma\sqrt{2\log d}$. Two corner
cases are handled separately: $\sigma^2 = 0$ forces each $X_j = 0$ a.e. (sub-Gaussian
with proxy $0$), and $d = 1$ gives $\max = X_0$ with $\mathbb{E}[X_0] = 0$ and
$\sqrt{2\log 1} = 0$; both reduce to $0 \le 0$.

**Bibliographic comments.** This is a folklore result with no single seminal origin; it
is the prototype of the maximal-inequality-via-MGF argument. A standard modern
reference is S. Boucheron, G. Lugosi, and P. Massart, *Concentration Inequalities: A
Nonasymptotic Theory of Independence*, Oxford University Press, 2013, §2.5 (the maximal
inequality $\mathbb{E}[\max_j X_j] \le \sqrt{2v\log d}$ for sub-Gaussian variables with
variance factor $v$). The same bound appears in P. Massart, *Concentration Inequalities
and Model Selection*, Lecture Notes in Mathematics 1896, Springer, 2007. The argument
goes back to the classical Cramér–Chernoff method applied to the maximum and is not
attributable to a single research paper.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Tail bound -/

/-- **Finite Maximal Inequality — tail bound** (Lu-BDA §6.2, Theorem 6.2).

Given `d ≥ 1` random variables, each sub-Gaussian with variance proxy `σ²` and
centered (`E[X_j] = 0`), and `t ≥ 0`:
```
μ {ω | t < ⨆ j : Fin d, X j ω} ≤ ENNReal.ofReal (d · exp(−t²/(2σ²)))
```

The finite max is expressed as `⨆ j : Fin d, X j ω` (the `iSup` equals the pointwise
maximum for `d ≥ 1`).

Proof: union bound (`measure_iUnion_fintype_le`) + per-`j` sub-Gaussian Chernoff tail
(`IsSubGaussian.measure_sub_integral_lt_le`; centeredness kills the `−∫ X_j` shift). -/
theorem tail_max_le
    {d : ℕ} [NeZero d] {μ : Measure Ω} {σ2 : ℝ≥0}
    {X : Fin d → Ω → ℝ}
    -- USER-INPUT: E[X_j] = 0; Lu-BDA §6.2, Theorem 6.2
    (hcenter : ∀ j, ∫ x, X j x ∂μ = 0)
    -- USER-INPUT: X_j is sub-Gaussian with variance proxy σ²; Lu-BDA §6.2, Theorem 6.2
    (hX : ∀ j, IsSubGaussian (X j) σ2 μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §6.2, Theorem 6.2
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < ⨆ j, X j ω}
      ≤ ENNReal.ofReal ((d : ℝ) * Real.exp (-t ^ 2 / (2 * ↑σ2))) := by
  -- `Fin d` is nonempty since d ≥ 1.
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero d)
  -- The range of `j ↦ X j ω` is finite hence bounded above, for every fixed `ω`.
  have hbdd : ∀ ω, BddAbove (Set.range (fun j => X j ω)) := fun ω =>
    Finite.bddAbove_range _
  -- Step 1: Rewrite `{ω | t < ⨆ j, X j ω}` as the union `⋃ j, {ω | t < X j ω}`.
  have heq : {ω | t < ⨆ j, X j ω} = ⋃ j, {ω | t < X j ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun h => (lt_ciSup_iff (hbdd ω)).mp h,
           fun ⟨j, hj⟩ => lt_of_lt_of_le hj (le_ciSup (hbdd ω) j)⟩
  rw [heq]
  -- Step 2: Union bound + per-j Chernoff tail.
  calc μ (⋃ j, {ω | t < X j ω})
      ≤ ∑ j : Fin d, μ {ω | t < X j ω} :=
          measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * ↑σ2))) := by
          apply Finset.sum_le_sum
          intro j _
          -- Centeredness: X j ω - ∫ X j ∂μ = X j ω - 0 = X j ω.
          have hj := (hX j).measure_sub_integral_lt_le ht
          simp only [hcenter j, sub_zero] at hj
          exact hj
    _ = ENNReal.ofReal ((d : ℝ) * Real.exp (-t ^ 2 / (2 * ↑σ2))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          -- d • ENNReal.ofReal e = ENNReal.ofReal (d * e)
          rw [← ENNReal.ofReal_nsmul, nsmul_eq_mul]

/-! ### Expectation bound — private helpers -/

/-- The pointwise finite iSup of integrable functions is integrable, dominated by
the sum of absolute values. -/
private lemma integrable_ciSup_fin
    {d : ℕ} [NeZero d] {μ : Measure Ω}
    {X : Fin d → Ω → ℝ} (hX : ∀ j, Integrable (X j) μ) :
    Integrable (fun ω => ⨆ j, X j ω) μ := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero d)
  apply Integrable.mono' (g := fun ω => ∑ j : Fin d, ‖X j ω‖)
  · exact integrable_finset_sum _ (fun j _ => (hX j).norm)
  · exact (AEMeasurable.iSup
      (fun j => (hX j).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  · filter_upwards with ω
    simp only [Real.norm_eq_abs]
    have hbdd : BddAbove (Set.range (fun j => X j ω)) := Finite.bddAbove_range _
    have h1 : ⨆ j, X j ω ≤ ∑ j : Fin d, |X j ω| :=
      ciSup_le fun j =>
        (le_abs_self _).trans
          (Finset.single_le_sum (f := fun k => |X k ω|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))
    have h2 : -(⨆ j, X j ω) ≤ ∑ j : Fin d, |X j ω| :=
      calc -(⨆ j, X j ω)
          ≤ -(X 0 ω) := neg_le_neg (le_ciSup hbdd 0)
        _ ≤ |X 0 ω| := by rw [← abs_neg]; exact le_abs_self _
        _ ≤ ∑ j : Fin d, |X j ω| :=
            Finset.single_le_sum (f := fun k => |X k ω|) (fun _ _ => abs_nonneg _) (Finset.mem_univ 0)
    exact abs_le.mpr ⟨by linarith, h1⟩

/-- For `lam > 0` and any function `f : Fin d → ℝ`, `exp(lam · sup_j f j) ≤ ∑_j exp(lam · f j)`.
The max is achieved at some `j₀`, and one term in the sum equals it while all others are positive. -/
private lemma exp_mul_ciSup_le_sum_exp
    {d : ℕ} [NeZero d] {lam : ℝ} (hlam : 0 < lam) (f : Fin d → ℝ) :
    Real.exp (lam * ⨆ j, f j) ≤ ∑ j : Fin d, Real.exp (lam * f j) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero d)
  obtain ⟨j0, _, hj0⟩ := Finset.exists_max_image Finset.univ f ⟨0, Finset.mem_univ _⟩
  have hmax : ⨆ j, f j = f j0 := le_antisymm
    (ciSup_le fun j => hj0 j (Finset.mem_univ j))
    (le_ciSup (Finite.bddAbove_range _) j0)
  rw [hmax]
  exact Finset.single_le_sum (f := fun j => Real.exp (lam * f j)) (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ j0)

/-! ### Expectation bound -/

/-- **Finite Maximal Inequality — expectation bound** (Lu-BDA §6.2, Theorem 6.2).

Given `d ≥ 1` centered sub-Gaussian random variables with variance proxy `σ²` under a
probability measure `μ`:
```
E[⨆ j : Fin d, X j] ≤ √σ² · √(2 log d)
```

Proof (Lu §6.2): for any `lam > 0`, by Jensen (exp convex, μ probability):
`exp(lam · E[max]) ≤ E[exp(lam · max)] ≤ E[∑_j exp(lam X_j)] = ∑_j mgf(X_j, lam)`;
sub-Gaussian MGF gives `∑_j mgf(X_j, lam) ≤ d · exp(σ² lam²/2)`. Taking log and dividing by
`lam` yields `E[max] ≤ log d / lam + σ² lam / 2`; optimising at `lam* = √(2 log d / σ²)` gives
`σ · √(2 log d)`.

Corner cases: `σ² = 0` → each `X_j = 0` a.e. (sub-Gaussian with proxy 0); `d = 1` → max = X₀ with
`E X₀ = 0` and `√(2 log 1) = 0`. Both give `0 ≤ 0`. -/
theorem expectation_max_le
    {d : ℕ} [NeZero d] {μ : Measure Ω} [IsProbabilityMeasure μ] {σ2 : ℝ≥0}
    {X : Fin d → Ω → ℝ}
    -- USER-INPUT: E[X_j] = 0; Lu-BDA §6.2, Theorem 6.2
    (hcenter : ∀ j, ∫ x, X j x ∂μ = 0)
    -- USER-INPUT: X_j is sub-Gaussian with variance proxy σ²; Lu-BDA §6.2, Theorem 6.2
    (hX : ∀ j, IsSubGaussian (X j) σ2 μ) :
    ∫ ω, ⨆ j, X j ω ∂μ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log d) := by
  -- Convert IsSubGaussian to HasSubgaussianMGF (centering kills the mean shift).
  have hsg : ∀ j, HasSubgaussianMGF (X j) σ2 μ := fun j => by
    have h := isSubGaussian_iff.mp (hX j)
    simp only [hcenter j, sub_zero] at h
    exact h
  -- *** Corner case A: σ² = 0 ***
  -- Each X_j = 0 a.e., so ⨆_j X_j = 0 a.e., and RHS = 0.
  by_cases hσ0 : σ2 = 0
  · have hX0 : ∀ j, X j =ᵐ[μ] 0 := fun j =>
      HasSubgaussianMGF.ae_eq_zero_of_hasSubgaussianMGF_zero (hσ0 ▸ hsg j)
    have hsupr0 : (fun ω => ⨆ j : Fin d, X j ω) =ᵐ[μ] fun _ => (0 : ℝ) := by
      haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero d)
      have hall : ∀ᵐ ω ∂μ, ∀ j : Fin d, X j ω = 0 := ae_all_iff.mpr hX0
      filter_upwards [hall] with ω hω
      simp_rw [hω]
      exact ciSup_const
    simp only [hσ0, NNReal.coe_zero, Real.sqrt_zero, zero_mul]
    have : ∫ ω, ⨆ j : Fin d, X j ω ∂μ = 0 :=
      integral_eq_zero_of_ae hsupr0
    linarith
  -- *** Corner case B: log d ≤ 0 (i.e., d = 1) ***
  -- Max over Fin 1 equals X 0, whose mean is 0. RHS = σ · √(2·0) = 0.
  rcases le_or_gt (Real.log (d : ℝ)) 0 with hlog | hlog
  · have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero d)
    have hd_le_one : (d : ℝ) ≤ 1 := by
      rwa [← Real.log_le_log_iff hd_pos one_pos, Real.log_one]
    have hd1 : d = 1 :=
      Nat.le_antisymm (by exact_mod_cast hd_le_one) (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
    subst hd1
    simp only [Nat.cast_one, Real.log_one, mul_zero, Real.sqrt_zero, mul_zero]
    have : ∀ ω, ⨆ j : Fin 1, X j ω = X 0 ω := fun ω => by
      simp [ciSup_unique]
    simp_rw [this]; linarith [hcenter 0]
  -- *** Main case: log d > 0 and σ² > 0 ***
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero d)
  have hσ_pos : (0 : ℝ) < (σ2 : ℝ) :=
    NNReal.coe_pos.mpr (lt_of_le_of_ne (zero_le) (Ne.symm hσ0))
  -- Integrability pieces not depending on lam.
  have hint_Xj : ∀ j, Integrable (X j) μ := fun j => (hsg j).integrable
  have hint_max : Integrable (fun ω => ⨆ j, X j ω) μ :=
    integrable_ciSup_fin hint_Xj
  -- Choose the optimal multiplier lam = √(2 log d / σ²) > 0.
  -- We parameterise by two helper variables a = √σ², b = √(2 log d) so that lam = b/a.
  set a := Real.sqrt (σ2 : ℝ) with ha_def
  set b := Real.sqrt (2 * Real.log (d : ℝ)) with hb_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hσ_pos
  have hb_pos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha_sq : a ^ 2 = σ2 := Real.sq_sqrt hσ_pos.le
  have hb_sq : b ^ 2 = 2 * Real.log (d : ℝ) := Real.sq_sqrt (by linarith)
  set lam := b / a with hlam_def
  have hlam_pos : 0 < lam := div_pos hb_pos ha_pos
  -- Integrability pieces depending on lam.
  have hint_exp_Xj : ∀ j, Integrable (fun ω => Real.exp (lam * X j ω)) μ :=
    fun j => (hsg j).integrable_exp_mul lam
  -- Integrability of exp(lam · max): dominated by sum of exp(lam · X_j).
  have hint_sum_exp : Integrable (fun ω => ∑ j : Fin d, Real.exp (lam * X j ω)) μ :=
    integrable_finset_sum _ (fun j _ => hint_exp_Xj j)
  have hint_exp_max : Integrable (fun ω => Real.exp (lam * ⨆ j, X j ω)) μ := by
    apply Integrable.mono' hint_sum_exp
    · exact continuous_exp.comp_aestronglyMeasurable
        ((hint_max.const_mul lam).aestronglyMeasurable)
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact exp_mul_ciSup_le_sum_exp hlam_pos (fun j => X j ω)
  -- ** Step 1: Jensen's inequality ** exp(lam · E[max]) ≤ E[exp(lam · max)]
  have hJensen : Real.exp (lam * ∫ ω, ⨆ j, X j ω ∂μ) ≤
      ∫ ω, Real.exp (lam * ⨆ j, X j ω) ∂μ := by
    have h := convexOn_exp.map_integral_le Real.continuousOn_exp isClosed_univ
      (Filter.Eventually.of_forall fun ω => Set.mem_univ _)
      (hint_max.const_mul lam) hint_exp_max
    rwa [integral_const_mul] at h
  -- ** Step 2: max ≤ sum bound ** E[exp(lam · max)] ≤ ∑_j E[exp(lam · X_j)]
  have h_int_bound : ∫ ω, Real.exp (lam * ⨆ j, X j ω) ∂μ ≤
      ∑ j : Fin d, ∫ ω, Real.exp (lam * X j ω) ∂μ := by
    rw [← integral_finset_sum _ (fun j _ => hint_exp_Xj j)]
    exact integral_mono hint_exp_max hint_sum_exp
      (fun ω => exp_mul_ciSup_le_sum_exp hlam_pos (fun j => X j ω))
  -- ** Step 3: MGF bound ** ∑_j E[exp(lam · X_j)] ≤ d · exp(σ² lam² / 2)
  have h_mgf : ∀ j, ∫ ω, Real.exp (lam * X j ω) ∂μ ≤
      Real.exp ((σ2 : ℝ) * lam ^ 2 / 2) := fun j => (hsg j).mgf_le lam
  have h_upper : Real.exp (lam * ∫ ω, ⨆ j, X j ω ∂μ) ≤
      (d : ℝ) * Real.exp ((σ2 : ℝ) * lam ^ 2 / 2) :=
    calc Real.exp (lam * ∫ ω, ⨆ j, X j ω ∂μ)
        ≤ ∫ ω, Real.exp (lam * ⨆ j, X j ω) ∂μ := hJensen
      _ ≤ ∑ j : Fin d, ∫ ω, Real.exp (lam * X j ω) ∂μ := h_int_bound
      _ ≤ ∑ _j : Fin d, Real.exp ((σ2 : ℝ) * lam ^ 2 / 2) :=
          Finset.sum_le_sum (fun j _ => h_mgf j)
      _ = (d : ℝ) * Real.exp ((σ2 : ℝ) * lam ^ 2 / 2) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- ** Step 4: Take log ** lam · E[max] ≤ log d + σ² lam² / 2
  have h_log_bound : lam * ∫ ω, ⨆ j, X j ω ∂μ ≤
      Real.log (d : ℝ) + (σ2 : ℝ) * lam ^ 2 / 2 := by
    have hrhs : (d : ℝ) * Real.exp ((σ2 : ℝ) * lam ^ 2 / 2) =
        Real.exp (Real.log (d : ℝ) + (σ2 : ℝ) * lam ^ 2 / 2) := by
      rw [Real.exp_add, Real.exp_log hd_pos]
    rw [hrhs] at h_upper
    exact Real.exp_le_exp.mp h_upper
  -- ** Step 5: Divide by lam ** E[max] ≤ log d / lam + σ² lam / 2
  have h_div_bound : ∫ ω, ⨆ j, X j ω ∂μ ≤
      Real.log (d : ℝ) / lam + (σ2 : ℝ) * lam / 2 := by
    rw [show Real.log (d : ℝ) / lam + (σ2 : ℝ) * lam / 2 =
        (Real.log (d : ℝ) + (σ2 : ℝ) * lam ^ 2 / 2) / lam from by
      field_simp [hlam_pos.ne']]
    exact (le_div_iff₀ hlam_pos).mpr (by linarith [mul_comm lam (∫ ω, ⨆ j, X j ω ∂μ)])
  -- ** Step 6: Algebra ** log d / lam + σ² lam / 2 = a · b = √σ² · √(2 log d)
  -- With lam = b/a: log d/(b/a) + σ²·(b/a)/2 = (b²/2)·a/b + a²·(b/a)/2 = ab/2+ab/2 = ab.
  have h_alg : Real.log (d : ℝ) / lam + (σ2 : ℝ) * lam / 2 = a * b := by
    rw [hlam_def]
    have ha_ne : a ≠ 0 := ha_pos.ne'
    have hb_ne : b ≠ 0 := hb_pos.ne'
    have hlog_eq : Real.log (d : ℝ) = b ^ 2 / 2 := by linarith [hb_sq]
    have hσ_eq : (σ2 : ℝ) = a ^ 2 := by linarith [ha_sq]
    rw [hlog_eq, hσ_eq]
    field_simp [ha_ne, hb_ne]
    ring
  -- ** Conclusion **
  calc ∫ ω, ⨆ j, X j ω ∂μ
      ≤ Real.log (d : ℝ) / lam + (σ2 : ℝ) * lam / 2 := h_div_bound
    _ = a * b := h_alg
    _ = Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log ↑d) := rfl

end StatLean.ConcentrationInequalities
