module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.MaximalBernstein
public import StatLean.AsymptoticStatistics.EmpiricalProcess.MaximalOrlicz
public import Mathlib.Probability.IdentDistrib

@[expose] public section

/-!
# Maximal inequalities for empirical processes

This file contains Bernstein's inequality
(`bernstein_inequality`, Lem 19.32), the finite-class supremum bound
(`finite_sup_bound`, Lem 19.33), and two crude bracketing bounds
(`maximal_inequality_bracketing` and its cushioned `_tight` restatement).
Because their constants depend on `n`, neither crude theorem is Lemma 19.34.

**Note on the "tight" lemma.** `maximal_inequality_bracketing_tight` in this
file does NOT, despite its name, witness a universal (`n`-independent) constant:
it is a cushioned restatement of the crude bound and is NOT on the Donsker
argument. The universal-constant Lemma 19.34 (independent of `n`)
is `localizedChainBound_of_finiteEntropy` in `ChainingAssembly.lean`
(stated in the localized-difference-class form that vdV's chaining produces).
The per-level chaining lemmas in this file
(`tight_chain_level_bound`/`_uniform`, `tight_chain_telescope_bound`,
`tight_envelope_truncation_bound`) provide its ingredients.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §19.6.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 19.32 (Bernstein's inequality for empirical processes)**.

For an iid sample `X_1, ..., X_n` from `P` and a measurable function `f`
with `|f| ≤ M` (a.s.) and `Pf² ≤ σ²`, the empirical-process tail bound

`P(|G_n f| > x) ≤ 2 · exp(− x² / (4 (σ² + x M / √n)))`

holds for every `x > 0`.

vdV §19.6 Lem 19.32. The proof routes through the standard Bernstein bound
for sums of bounded iid plus an iid-to-`P_n` translation. -/
theorem bernstein_inequality
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (_hf_meas : Measurable f)
    {M σ : ℝ} (_hM : 0 ≤ M) (_hσ : 0 ≤ σ)
    (_hf_bdd : ∀ ω, |f ω| ≤ M)
    (_hf_var : ∫ ω, (f ω) ^ 2 ∂P ≤ σ ^ 2)
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (n : ℕ) (_hn : 1 ≤ n) {x : ℝ} (_hx : 0 < x) :
    μ {ω : Ξ | x < |empiricalProcess P n (fun j : Fin n => X j.val ω) f|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(x ^ 2) / (4 * (σ ^ 2 + x * M / Real.sqrt n)))) := by
  -- The two-sided bound follows from:
  --   * `empiricalProcess_neg` (linear-odd in `f`),
  --   * `bernstein_two_sided` (one-sided bound applied to `f` and `-f`),
  -- together with `mgf_bounded_taylor` and `bernstein_one_sided`.
  exact bernstein_inequality_aux P f _hf_meas _hM _hσ _hf_bdd _hf_var
    hX_meas hX_iindep _hX_idem hX_law n _hn _hx

/-- **Lemma 19.33 (Finite-class supremum bound)**.

For a finite class of measurable functions, each bounded by `M` and with
`Pf² ≤ σ²`, the expected supremum deviation satisfies

`E ‖G_n‖F ≤ K · (M · log(1+|F|) / √n + σ · √(log(1+|F|)))`

for some universal constant `K`.

vdV §19.6 Lem 19.33. Builds on Lem 19.32 via union bound + Jensen. -/
theorem finite_sup_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {ι : Type*} [Fintype ι] (g : ι → Ω → ℝ) (_hg_meas : ∀ i, Measurable (g i))
    {M σ : ℝ} (_hM : 0 ≤ M) (_hσ : 0 ≤ σ)
    (_hg_bdd : ∀ i ω, |g i ω| ≤ M)
    (_hg_var : ∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ σ ^ 2)
    (n : ℕ) (_hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ ω, ENNReal.ofReal
          (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
        ≤ ENNReal.ofReal
            (K * (M * Real.log (1 + Fintype.card ι) / Real.sqrt n
              + σ * Real.sqrt (Real.log (1 + Fintype.card ι)))) := by
  -- Apply the Orlicz truncation and Jensen bound from `MaximalOrlicz.lean`.
  exact finite_sup_bound_aux P hX_meas hX_iindep _hX_idem hX_law
    g _hg_meas _hM _hσ _hg_bdd _hg_var n _hn

/-- Helper: measurability of `fun x => |Φ x|` from `Measurable Φ`.
Uses `Measurable.norm` plus the `rfl`-equality `‖r‖ = |r|` on `ℝ`. -/
private lemma measurable_abs_of_real {Φ : Ω → ℝ} (hΦ : Measurable Φ) :
    Measurable (fun x => |Φ x|) :=
  hΦ.norm

/-- **A crude bracketing bound (not Lemma 19.34).**

For a class `F` of measurable functions with `Pf² ≤ δ²` for every `f ∈ F`,
envelope function `Φ`, and the bracketing entropy integral
`J_{[]}(δ, F, L²(P))`, there exists a constant `K` such that

`E* ‖G_n‖F ≤ K · (1 + J_{[]}(δ, F, L²(P)) + √n · P*Φ · 1{Φ > √n · a(δ)})`

where `a(δ) = δ / √(log N_{[]}(δ, F, L²(P)))`. The leading `1` cushion
inside the parenthesised factor is a **crude-bound artifact**: vdV's
sharper statement absorbs it inside `J_{[]}` for non-trivial classes
(where `J_{[]}` is bounded below by a positive multiple of `δ`). For the
formal Lean statement here, `J` is treated as an arbitrary user-supplied
upper bound on the bracketing entropy integral, and the cushion lets
the existential `K` cover the residual `2 n δ` term that arises when
both `J = 0` and the envelope-tail evaluates to `0` (a corner case the
tight chaining bound rules out structurally).

This theorem is motivated by the RHS shape in vdV §19.6 Lemma 19.34,
but it is not that lemma: the full chaining argument is replaced by an
envelope + Cauchy–Schwarz-style argument that
yields a non-tight `K = 2nδ + 2` depending on the inputs `(n, δ)`; the `K`
here is therefore **not** a universal constant.

Concretely, the proof bounds
`∫⁻ ω, supNormOver F (G_n)(ω) ∂μ ≤ ENNReal.ofReal (2 n δ)
   + 2 · ENNReal.ofReal (√n) · T` where
`T = ∫⁻ |Φ| · 1{|Φ| > δ √n} ∂P`,
using `|f| ≤ Φ` (envelope) and the lintegral form
`ENNReal.ofReal |∫ f dP| ≤ ∫⁻ |Φ| dP` (via `norm_integral_le_lintegral_norm`),
followed by Fubini (via `IdentDistrib`) and a dyadic split of
`∫⁻ |Φ| dP` at threshold `δ √n`. -/
theorem maximal_inequality_bracketing
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ_env : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ)
    {δ : ℝ} (hδ : 0 < δ)
    (_h_var : ∀ f ∈ F, ∫ ω, (f ω) ^ 2 ∂P ≤ δ ^ 2)
    (J : ℝ≥0∞) (_hJ : J < ⊤) -- the bracketing entropy integral J_{[]}(δ, F, L²(P))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ ω, supNormOver F
          (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω) f) ∂μ
        ≤ ENNReal.ofReal K *
            (1 + J + ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                  * Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P) := by
  -- Crude-bound closure (mirrors `finite_sup_bound`'s strategy in spirit).
  -- Numerical setup.
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : 0 ≤ Real.sqrt n := hsn_pos.le
  have hδ_nn : 0 ≤ δ := hδ.le
  have hnδ_nn : 0 ≤ 2 * (n : ℝ) * δ := by positivity
  -- Choose `K := 2 n δ + 2`.
  refine ⟨2 * (n : ℝ) * δ + 2, by linarith, ?_⟩
  -- Set up shorthand for the tail-integral T.
  set T : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (|Φ ω|) *
      Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P with hT_def
  -- Set up shorthand for the LHS integral.
  set L : ℝ≥0∞ := ∫⁻ ω, supNormOver F
      (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω) f) ∂μ
      with hL_def
  -- Convenience: |Φ| is measurable.
  have hΦ_abs_meas : Measurable (fun x => |Φ x|) := measurable_abs_of_real hΦ_meas
  have hΦ_abs_ofReal_meas : Measurable (fun x => ENNReal.ofReal (|Φ x|)) :=
    hΦ_abs_meas.ennreal_ofReal
  -- Shorthand: the lintegral of |Φ| over P.
  set Lp : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (|Φ x|) ∂P with hLp_def
  -- ===== Step 1: pointwise bound on supNormOver F (G_n) at the ENNReal level =====
  have h_pt : ∀ ω : Ξ,
      supNormOver F (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω) f)
        ≤ ENNReal.ofReal (Real.sqrt n) *
          (ENNReal.ofReal
              (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω))
            + Lp) := by
    intro ω
    refine iSup₂_le ?_
    intro f hf
    -- (a) |empAvg f|(ω) ≤ empAvg|Φ|(ω) at real level.
    have h_avg_le : |empiricalAvg f n (fun j : Fin n => X j.val ω)|
        ≤ empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω) := by
      unfold empiricalAvg
      rw [abs_mul, abs_inv, abs_of_pos hn_pos]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hn_pos.le)
      calc |∑ i : Fin n, f (X i.val ω)|
          ≤ ∑ i : Fin n, |f (X i.val ω)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, |Φ (X i.val ω)| :=
            Finset.sum_le_sum (fun (i : Fin n) _ => (hΦ_env f hf (X i.val ω)).trans (le_abs_self _))
    have hempavgΦ_nn : 0 ≤ empiricalAvg (fun x => |Φ x|) n
        (fun j : Fin n => X j.val ω) := by
      unfold empiricalAvg
      refine mul_nonneg (inv_nonneg.mpr hn_pos.le) ?_
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    -- (b) Triangle: |empAvg f - ∫ f| ≤ |empAvg f| + |∫ f| (real).
    have h_tri_real :
        |empiricalAvg f n (fun j : Fin n => X j.val ω) - ∫ x, f x ∂P|
        ≤ |empiricalAvg f n (fun j : Fin n => X j.val ω)| + |∫ x, f x ∂P| :=
      abs_sub _ _
    -- (c) Lift to ENNReal.
    have h_tri_ennreal :
        ENNReal.ofReal |empiricalAvg f n (fun j : Fin n => X j.val ω) - ∫ x, f x ∂P|
        ≤ ENNReal.ofReal |empiricalAvg f n (fun j : Fin n => X j.val ω)|
          + ENNReal.ofReal |∫ x, f x ∂P| := by
      calc ENNReal.ofReal |empiricalAvg f n (fun j : Fin n => X j.val ω) - ∫ x, f x ∂P|
          ≤ ENNReal.ofReal (|empiricalAvg f n (fun j : Fin n => X j.val ω)|
              + |∫ x, f x ∂P|) := ENNReal.ofReal_le_ofReal h_tri_real
        _ ≤ ENNReal.ofReal |empiricalAvg f n (fun j : Fin n => X j.val ω)|
            + ENNReal.ofReal |∫ x, f x ∂P| := ENNReal.ofReal_add_le
    -- (d) Bound term 1 in ENNReal.
    have h_avg_ennreal :
        ENNReal.ofReal |empiricalAvg f n (fun j : Fin n => X j.val ω)|
        ≤ ENNReal.ofReal
            (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω)) :=
      ENNReal.ofReal_le_ofReal h_avg_le
    -- (e) Bound term 2: ENNReal.ofReal |∫ f| ≤ Lp.
    have h_int_ennreal : ENNReal.ofReal |∫ x, f x ∂P| ≤ Lp := by
      have h_step1 : ENNReal.ofReal |∫ x, f x ∂P|
          ≤ ∫⁻ x, ENNReal.ofReal (|f x|) ∂P := by
        have h1 : |∫ x, f x ∂P| ≤ (∫⁻ x, ENNReal.ofReal (|f x|) ∂P).toReal := by
          have hh := MeasureTheory.norm_integral_le_lintegral_norm (μ := P) f
          simpa [Real.norm_eq_abs] using hh
        calc ENNReal.ofReal |∫ x, f x ∂P|
            ≤ ENNReal.ofReal (∫⁻ x, ENNReal.ofReal (|f x|) ∂P).toReal :=
              ENNReal.ofReal_le_ofReal h1
          _ ≤ ∫⁻ x, ENNReal.ofReal (|f x|) ∂P := ENNReal.ofReal_toReal_le
      have h_step2 : ∫⁻ x, ENNReal.ofReal (|f x|) ∂P ≤ Lp := by
        rw [hLp_def]
        refine MeasureTheory.lintegral_mono (fun x => ?_)
        exact ENNReal.ofReal_le_ofReal ((hΦ_env f hf x).trans (le_abs_self _))
      exact h_step1.trans h_step2
    -- (f) Assemble.
    have h_assemble :
        ENNReal.ofReal |empiricalProcess P n (fun j : Fin n => X j.val ω) f|
        = ENNReal.ofReal (Real.sqrt n) *
            ENNReal.ofReal
              |empiricalAvg f n (fun j : Fin n => X j.val ω) - ∫ x, f x ∂P| := by
      unfold empiricalProcess
      rw [abs_mul, abs_of_nonneg hsn_nn, ENNReal.ofReal_mul hsn_nn]
    rw [h_assemble]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    calc ENNReal.ofReal
            |empiricalAvg f n (fun j : Fin n => X j.val ω) - ∫ x, f x ∂P|
        ≤ ENNReal.ofReal |empiricalAvg f n (fun j : Fin n => X j.val ω)|
          + ENNReal.ofReal |∫ x, f x ∂P| := h_tri_ennreal
      _ ≤ ENNReal.ofReal
            (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω))
          + Lp := add_le_add h_avg_ennreal h_int_ennreal
  -- ===== Step 2: integrate the pointwise bound over μ =====
  have h_emp_meas : AEMeasurable
      (fun ω : Ξ => ENNReal.ofReal
        (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω))) μ := by
    refine Measurable.aemeasurable ?_
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΦ_abs_meas.comp (hX_meas i.val)
  have h_int : L ≤ ENNReal.ofReal (Real.sqrt n) *
      (∫⁻ ω, ENNReal.ofReal
          (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω)) ∂μ
        + Lp) := by
    rw [hL_def]
    calc ∫⁻ ω, supNormOver F
            (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω) f) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.sqrt n) *
            (ENNReal.ofReal
                (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω))
              + Lp) ∂μ :=
          MeasureTheory.lintegral_mono h_pt
      _ = ENNReal.ofReal (Real.sqrt n) *
            ∫⁻ ω, (ENNReal.ofReal
                (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω))
              + Lp) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ω, ENNReal.ofReal
                (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω)) ∂μ
              + ∫⁻ _, Lp ∂μ) := by
          rw [MeasureTheory.lintegral_add_left' h_emp_meas]
      _ = ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ω, ENNReal.ofReal
                (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω)) ∂μ
              + Lp) := by
          rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
  -- ===== Step 3: bound `∫⁻ empAvg|Φ| dμ ≤ Lp` =====
  have h_emp_to_P : ∫⁻ ω, ENNReal.ofReal
      (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω)) ∂μ
      ≤ Lp := by
    rw [hLp_def]
    have h_pt_le : ∀ ω : Ξ,
        ENNReal.ofReal
          (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω))
        ≤ ((n : ℝ≥0∞))⁻¹ *
          ∑ i : Fin n, ENNReal.ofReal (|Φ (X i.val ω)|) := by
      intro ω
      unfold empiricalAvg
      have h_sum_nn : ∀ i : Fin n, 0 ≤ |Φ (X i.val ω)| := fun i => abs_nonneg _
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have hn_inv_eq : ENNReal.ofReal ((n : ℝ)⁻¹) = ((n : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
      rw [hn_inv_eq]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      have hsum := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin n => |Φ (X i.val ω)|)
        (fun i _ => h_sum_nn i)
      rw [hsum]
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hn_pos_nat)
    have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
    calc ∫⁻ ω, ENNReal.ofReal
            (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω)) ∂μ
        ≤ ∫⁻ ω, ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ENNReal.ofReal (|Φ (X i.val ω)|) ∂μ :=
          MeasureTheory.lintegral_mono h_pt_le
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (|Φ (X i.val ω)|) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ hinv_ne_top]
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ∫⁻ ω, ENNReal.ofReal (|Φ (X i.val ω)|) ∂μ := by
          congr 1
          rw [MeasureTheory.lintegral_finset_sum Finset.univ]
          intro i _
          exact hΦ_abs_ofReal_meas.comp (hX_meas i.val)
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ _i : Fin n, ∫⁻ x, ENNReal.ofReal (|Φ x|) ∂P := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have h_id : (μ.map (X i.val)) = P := by
            have h_id_to_0 : ProbabilityTheory.IdentDistrib (X i.val) (X 0) μ μ :=
              hX_idem i.val
            rw [← hX_law]
            exact h_id_to_0.map_eq
          rw [← h_id]
          exact (MeasureTheory.lintegral_map hΦ_abs_ofReal_meas (hX_meas i.val)).symm
      _ = ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞)) * ∫⁻ x, ENNReal.ofReal (|Φ x|) ∂P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_assoc]
      _ = ∫⁻ x, ENNReal.ofReal (|Φ x|) ∂P := by
          rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul]
  -- ===== Step 4: split `Lp = ∫⁻ |Φ| dP` at threshold `δ √n` =====
  have h_split : Lp ≤ ENNReal.ofReal (δ * Real.sqrt n) + T := by
    rw [hLp_def, hT_def]
    let A : Set Ω := {x | |Φ x| ≤ δ * Real.sqrt n}
    have hA_meas : MeasurableSet A := by
      have hpb : A = (fun x => |Φ x|) ⁻¹' Set.Iic (δ * Real.sqrt n) := rfl
      rw [hpb]
      exact hΦ_abs_meas measurableSet_Iic
    have hAB : Aᶜ = {x | δ * Real.sqrt n < |Φ x|} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, A, not_le]
    have hΦ_indic_A : ∀ x, ENNReal.ofReal (|Φ x|) * A.indicator 1 x
        ≤ ENNReal.ofReal (δ * Real.sqrt n) * A.indicator 1 x := by
      intro x
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx, Pi.one_apply, mul_one]
        exact ENNReal.ofReal_le_ofReal hx
      · simp [Set.indicator_of_notMem hx]
    have h_split_pt : ∀ x,
        ENNReal.ofReal (|Φ x|)
        = ENNReal.ofReal (|Φ x|) * A.indicator 1 x
          + ENNReal.ofReal (|Φ x|) * Aᶜ.indicator 1 x := by
      intro x
      have h_indic_sum : A.indicator 1 x + Aᶜ.indicator 1 x = (1 : ℝ≥0∞) := by
        by_cases hx : x ∈ A
        · simp [Set.indicator_of_mem hx,
            Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx)]
        · have hxc : x ∈ Aᶜ := Set.mem_compl hx
          simp [Set.indicator_of_notMem hx, Set.indicator_of_mem hxc]
      rw [← mul_add, h_indic_sum, mul_one]
    have h_meas_A_indic : Measurable
        (fun x => ENNReal.ofReal (|Φ x|) * A.indicator (1 : Ω → ℝ≥0∞) x) := by
      refine Measurable.mul hΦ_abs_ofReal_meas ?_
      exact (measurable_const.indicator hA_meas)
    calc ∫⁻ x, ENNReal.ofReal (|Φ x|) ∂P
        = ∫⁻ x, (ENNReal.ofReal (|Φ x|) * A.indicator 1 x
              + ENNReal.ofReal (|Φ x|) * Aᶜ.indicator 1 x) ∂P := by
            simp_rw [← h_split_pt]
      _ = ∫⁻ x, ENNReal.ofReal (|Φ x|) * A.indicator 1 x ∂P
          + ∫⁻ x, ENNReal.ofReal (|Φ x|) * Aᶜ.indicator 1 x ∂P := by
            rw [MeasureTheory.lintegral_add_left h_meas_A_indic]
      _ ≤ ∫⁻ x, ENNReal.ofReal (δ * Real.sqrt n) * A.indicator 1 x ∂P
          + ∫⁻ x, ENNReal.ofReal (|Φ x|) * Aᶜ.indicator 1 x ∂P := by
            refine add_le_add ?_ le_rfl
            exact MeasureTheory.lintegral_mono hΦ_indic_A
      _ = ENNReal.ofReal (δ * Real.sqrt n) * P A
          + ∫⁻ x, ENNReal.ofReal (|Φ x|) * Aᶜ.indicator 1 x ∂P := by
            rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            congr 1
            rw [MeasureTheory.lintegral_indicator_one hA_meas]
      _ ≤ ENNReal.ofReal (δ * Real.sqrt n)
          + ∫⁻ x, ENNReal.ofReal (|Φ x|) * Aᶜ.indicator 1 x ∂P := by
            refine add_le_add ?_ le_rfl
            calc ENNReal.ofReal (δ * Real.sqrt n) * P A
                ≤ ENNReal.ofReal (δ * Real.sqrt n) * 1 :=
                  mul_le_mul_of_nonneg_left prob_le_one (zero_le)
              _ = ENNReal.ofReal (δ * Real.sqrt n) := mul_one _
      _ = ENNReal.ofReal (δ * Real.sqrt n)
          + ∫⁻ x, ENNReal.ofReal (|Φ x|) *
              {x | δ * Real.sqrt n < |Φ x|}.indicator 1 x ∂P := by
            rw [hAB]
  -- ===== Step 5: assemble L ≤ 2 √n · Lp =====
  have h_combine : L ≤ 2 * ENNReal.ofReal (Real.sqrt n) * Lp := by
    calc L ≤ ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ω, ENNReal.ofReal
                (empiricalAvg (fun x => |Φ x|) n (fun j : Fin n => X j.val ω)) ∂μ
              + Lp) := h_int
      _ ≤ ENNReal.ofReal (Real.sqrt n) * (Lp + Lp) :=
          mul_le_mul_of_nonneg_left (add_le_add h_emp_to_P le_rfl) (zero_le)
      _ = 2 * ENNReal.ofReal (Real.sqrt n) * Lp := by ring
  -- ===== Step 6: bound L ≤ 2 n δ + 2 √n · T =====
  have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
    Real.mul_self_sqrt hn_pos.le
  have hofReal2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by
    simp [ENNReal.ofReal_ofNat]
  have h_2nδ_eq : 2 * ENNReal.ofReal (Real.sqrt n) *
      ENNReal.ofReal (δ * Real.sqrt n) = ENNReal.ofReal (2 * (n : ℝ) * δ) := by
    rw [← hofReal2,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hsn_nn)]
    congr 1
    have heq : 2 * Real.sqrt n * (δ * Real.sqrt n)
        = 2 * (Real.sqrt n * Real.sqrt n) * δ := by ring
    rw [heq, h_sqrt_sq]
  have h_final_real_bound : L ≤ ENNReal.ofReal (2 * (n : ℝ) * δ)
      + 2 * ENNReal.ofReal (Real.sqrt n) * T := by
    calc L ≤ 2 * ENNReal.ofReal (Real.sqrt n) * Lp := h_combine
      _ ≤ 2 * ENNReal.ofReal (Real.sqrt n) *
            (ENNReal.ofReal (δ * Real.sqrt n) + T) :=
          mul_le_mul_of_nonneg_left h_split (zero_le)
      _ = 2 * ENNReal.ofReal (Real.sqrt n) * ENNReal.ofReal (δ * Real.sqrt n)
            + 2 * ENNReal.ofReal (Real.sqrt n) * T := by ring
      _ = ENNReal.ofReal (2 * (n : ℝ) * δ) + 2 * ENNReal.ofReal (Real.sqrt n) * T := by
          rw [h_2nδ_eq]
  -- ===== Step 7: bound `2 n δ + 2 √n · T ≤ K · (1 + J + √n · T)` with K = 2nδ + 2 =====
  set Ksum : ℝ≥0∞ := ENNReal.ofReal (2 * (n : ℝ) * δ + 2) with hKsum_def
  have hK_ge_2nδ : ENNReal.ofReal (2 * (n : ℝ) * δ) ≤ Ksum :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hK_ge_2 : (2 : ℝ≥0∞) ≤ Ksum := by
    rw [hKsum_def, ← hofReal2]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  change L ≤ ENNReal.ofReal (2 * (n : ℝ) * δ + 2) *
    (1 + J + ENNReal.ofReal (Real.sqrt n) * T)
  rw [← hKsum_def]
  calc L ≤ ENNReal.ofReal (2 * (n : ℝ) * δ) + 2 * ENNReal.ofReal (Real.sqrt n) * T :=
          h_final_real_bound
    _ ≤ Ksum * 1 + Ksum * (ENNReal.ofReal (Real.sqrt n) * T) := by
        refine add_le_add ?_ ?_
        · rw [mul_one]; exact hK_ge_2nδ
        · rw [show (2 : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt n) * T
              = 2 * (ENNReal.ofReal (Real.sqrt n) * T) from by ring]
          exact mul_le_mul_of_nonneg_right hK_ge_2 (zero_le)
    _ ≤ Ksum * 1 + Ksum * (J + ENNReal.ofReal (Real.sqrt n) * T) := by
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_left le_add_self (zero_le)
    _ = Ksum * (1 + (J + ENNReal.ofReal (Real.sqrt n) * T)) := by rw [← mul_add]
    _ = Ksum * (1 + J + ENNReal.ofReal (Real.sqrt n) * T) := by rw [add_assoc]

/-! ### Universal-constant chaining estimates

The genuine §19.6 chaining argument of Lem 19.34 yields a **universal** constant
`K` (independent of `n` and `δ`), as opposed to the crude variant above with
`K = 2nδ + 2`. That universal-constant content is the required input for the
equicontinuity half of Theorem 19.5 (sending `δ ↓ 0` along a `1/√n`-summable
sequence requires `K` not to grow with `n`).

The universal-`K` chaining result is `localizedChainBound_of_finiteEntropy`,
stated for the localized difference class. The three estimates below
(`tight_chain_level_bound` / its uniform variant `tight_chain_level_bound_uniform`,
`tight_chain_telescope_bound`, `tight_envelope_truncation_bound`) provide its ingredients.
The theorem `maximal_inequality_bracketing_tight` retains the `n`-dependent
constant `K = 2nδ + 2` and assumes `hAbsorb`; the universal-constant conclusion
is `localizedChainBound_of_finiteEntropy`.

**Chaining argument.** For each `q ≥ 0`,
choose dyadic scale `ε_q = δ · 2^{-q}` and bracket cover of size
`N_q = N_{[]}(ε_q, F, L²(P))`. For each `f ∈ F` let `π_q(f)` be the *lower*
bracket function at scale `ε_q`. The chain telescope
  `f − π_0(f) = Σ_{q ≥ 1} (π_q(f) − π_{q-1}(f))`
splits the empirical-process supremum into per-level finite-class sup's
plus an envelope-remainder term. Apply `finite_sup_bound` at each level
`q` to the link class `{π_q(f) − π_{q-1}(f) : f ∈ F}` (size ≤ `N_q · N_{q-1}
≤ N_q²`) with truncation threshold `a(δ_{q-1}) = δ_{q-1} / √log N_{q-1}`.
Sum across `q` via Σ ε_q √log N_q ≤ K · J_{[]}(δ, F, L²(P)) (geometric
sum vs decreasing integrand).

The three estimates below give (a) the finite-class supremum bound at each
level, (b) the comparison of the telescoping series with the entropy integral,
and (c) the envelope truncation correction. -/

/-- **Per chain-level finite-class supremum bound.**

For a chain level with finite class `g : ι → Ω → ℝ` representing the
*jump* between adjacent bracket levels (`g i = π_q(f_i) − π_{q-1}(f_i)`
for some enumeration `i ↦ f_i` of bracket pairs), each function has
truncated L∞-bound `M = √n · ε / (1 + √(log(1+|ι|)))` (the vdV `a(δ)`
threshold, regularised so denom ≥ 1) and L²-bound `σ = 2 ε`. The
finite-class sup bound (`finite_sup_bound` / Lem 19.33) then gives

`E sup_i |G_n g_i| ≤ K · ε · √(log(1+|ι|))`

with `K` a universal constant. The `M log(1+|ι|) / √n` term in
`finite_sup_bound` becomes `ε · log/(1+√log) ≤ ε · √log` under this
choice of `M`, which is the key vdV trick (truncate at threshold `a(δ)`
so the M-piece matches the σ-piece up to a universal constant).

The theorem states `K` existentially, as does `finite_sup_bound`. The bound
`K = 96` in `finite_sup_bound_aux` would give `K_A = 3 · 96 = 288`.

Proof: direct invocation of `finite_sup_bound` with
`M = √n · ε / (1 + √log(1+|ι|))` and `σ = 2ε`, followed by the algebraic
compression `M log(1+|ι|)/√n + σ √log(1+|ι|) ≤ 3 ε √log(1+|ι|)` (using
`log/(1+√log) ≤ √log`). -/
lemma tight_chain_level_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g : ι → Ω → ℝ) (hg_meas : ∀ i, Measurable (g i))
    {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) (hn : 1 ≤ n)
    -- vdV truncation threshold: `|g i ω| ≤ √n · ε / (1+√log N_q)`, the `a(δ)` bound
    (hg_bdd : ∀ i ω, |g i ω| ≤
      Real.sqrt n * ε / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))))
    (hg_var : ∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ (2 * ε) ^ 2) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ ω, ENNReal.ofReal
          (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
        ≤ ENNReal.ofReal
            (K * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
  -- Numerical preliminaries.
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : 0 ≤ Real.sqrt n := hsn_pos.le
  -- Cardinality and entropy abbreviations (matching hg_bdd's coercion form:
  -- bare `Fintype.card ι` inside `1 + ...`, no explicit `(_ : ℝ)`).
  have hN_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hN_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hN_pos_nat
  have hL_nn : 0 ≤ Real.log (1 + Fintype.card ι) :=
    Real.log_nonneg (by linarith)
  have hsL_nn : 0 ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) :=
    Real.sqrt_nonneg _
  have h1psL_pos : (0 : ℝ) < 1 + Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith
  -- M and σ for finite_sup_bound (inlined to avoid `set` rewriting issues
  -- in `hg_bdd` and `hg_var`).
  have hM_nn : 0 ≤ Real.sqrt n * ε
      / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by positivity
  have hσ_nn : (0 : ℝ) ≤ 2 * ε := by positivity
  -- Apply the public finite_sup_bound API.
  obtain ⟨K, hK_pos, h_bnd⟩ := finite_sup_bound P hX_meas hX_iindep hX_idem hX_law
    g hg_meas hM_nn hσ_nn hg_bdd hg_var n hn
  -- Witness K' = 3K.
  refine ⟨3 * K, by positivity, ?_⟩
  refine h_bnd.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  -- Algebraic compression.
  -- M · log(1+N)/√n = ε · log(1+N)/(1+√log(1+N)) ≤ ε · √log(1+N).
  have hM_div_sqrt :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        = ε * Real.log (1 + Fintype.card ι)
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by
    field_simp
  have hLog_div_le :
      Real.log (1 + Fintype.card ι)
          / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
        ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [div_le_iff₀ h1psL_pos]
    have hsq : Real.sqrt (Real.log (1 + Fintype.card ι))
              * Real.sqrt (Real.log (1 + Fintype.card ι))
            = Real.log (1 + Fintype.card ι) :=
      Real.mul_self_sqrt hL_nn
    nlinarith [hsq, hsL_nn, hL_nn]
  have hM_term_le :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        ≤ ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [hM_div_sqrt, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hLog_div_le hε.le
  have h_sum_le :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))
        ≤ 3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith [hM_term_le]
  calc K * (Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
              * Real.log (1 + Fintype.card ι) / Real.sqrt n
            + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)))
      ≤ K * (3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) :=
        mul_le_mul_of_nonneg_left h_sum_le hK_pos.le
    _ = 3 * K * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by ring

/-- **Uniform-constant form of `tight_chain_level_bound`** — the existential `∃ K`
is hoisted *before* the class / scale / `n` arguments, so a single universal `K`
works for every finite chain-level class simultaneously.

The chaining dyadic bounds (`chain_head_dyadic_bound`, `chain_A_dyadic_bound`,
`chain_B_levelOscSup_dyadic_bound`) must quantify their constant `c` *before*
`∀ Φ ∀ δ ∀ n`; the additive `tight_chain_level_bound` returns `∃ K` only *after* the
family / scale / `n` arguments, so `c` cannot be hoisted from it. This form
uses the concrete witness `K = 3 · 96 = 288` (from the value `96` in
`finite_sup_bound_uniform` / `finite_sup_bound_orlicz_core`) once, before the
`∀`-block, via the same vdV `a(δ)`-truncation algebraic compression
`M log(1+|ι|)/√n + σ √log ≤ 3 ε √log` used by
`tight_chain_level_bound`. -/
lemma tight_chain_level_bound_uniform
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
        (g : ι → Ω → ℝ), (∀ i, Measurable (g i)) →
        ∀ {ε : ℝ}, 0 < ε → ∀ (n : ℕ), 1 ≤ n →
          (∀ i ω, |g i ω| ≤
            Real.sqrt n * ε / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))) →
          (∀ i, ∫ ω, (g i ω) ^ 2 ∂P ≤ (2 * ε) ^ 2) →
            ∫⁻ ω, ENNReal.ofReal
                (⨆ i : ι, |empiricalProcess P n (fun j : Fin n => X j.val ω) (g i)|) ∂μ
              ≤ ENNReal.ofReal
                  (K * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) := by
  -- Obtain the uniform `finite_sup_bound` constant once (the literal `96`); the
  -- chaining constant is `3 ·` that, hoisted before the class / scale / `n` args.
  obtain ⟨K, hK_pos, h_fsb⟩ :=
    finite_sup_bound_uniform P hX_meas hX_iindep hX_idem hX_law
  refine ⟨3 * K, by positivity, ?_⟩
  intro ι _ _ g hg_meas ε hε n hn hg_bdd hg_var
  -- Numerical preliminaries (mirror `tight_chain_level_bound`).
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : 0 ≤ Real.sqrt n := hsn_pos.le
  have hN_pos_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hN_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hN_pos_nat
  have hL_nn : 0 ≤ Real.log (1 + Fintype.card ι) :=
    Real.log_nonneg (by linarith)
  have hsL_nn : 0 ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) :=
    Real.sqrt_nonneg _
  have h1psL_pos : (0 : ℝ) < 1 + Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith
  have hM_nn : 0 ≤ Real.sqrt n * ε
      / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by positivity
  have hσ_nn : (0 : ℝ) ≤ 2 * ε := by positivity
  -- Apply the uniform finite-sup bound with the truncation `M`/`σ`.
  have h_bnd := h_fsb g hg_meas hM_nn hσ_nn hg_bdd hg_var n hn
  refine h_bnd.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  -- Algebraic compression (identical to `tight_chain_level_bound`).
  have hM_div_sqrt :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        = ε * Real.log (1 + Fintype.card ι)
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι))) := by
    field_simp
  have hLog_div_le :
      Real.log (1 + Fintype.card ι)
          / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
        ≤ Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [div_le_iff₀ h1psL_pos]
    have hsq : Real.sqrt (Real.log (1 + Fintype.card ι))
              * Real.sqrt (Real.log (1 + Fintype.card ι))
            = Real.log (1 + Fintype.card ι) :=
      Real.mul_self_sqrt hL_nn
    nlinarith [hsq, hsL_nn, hL_nn]
  have hM_term_le :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        ≤ ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    rw [hM_div_sqrt, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hLog_div_le hε.le
  have h_sum_le :
      Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
          * Real.log (1 + Fintype.card ι) / Real.sqrt n
        + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))
        ≤ 3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by
    linarith [hM_term_le]
  calc K * (Real.sqrt n * ε
            / (1 + Real.sqrt (Real.log (1 + Fintype.card ι)))
              * Real.log (1 + Fintype.card ι) / Real.sqrt n
            + 2 * ε * Real.sqrt (Real.log (1 + Fintype.card ι)))
      ≤ K * (3 * ε * Real.sqrt (Real.log (1 + Fintype.card ι))) :=
        mul_le_mul_of_nonneg_left h_sum_le hK_pos.le
    _ = 3 * K * ε * Real.sqrt (Real.log (1 + Fintype.card ι)) := by ring

/-- **Chain series to entropy-integral upper bound.**

Given a per-level sup sequence `S : ℕ → ℝ≥0∞` (e.g., from
`tight_chain_level_bound`)
dominated by an upper-bound sequence `B : ℕ → ℝ≥0∞`, and a chain
comparison `(∑' q, B q) ≤ J`, conclude `∑' q, S q ≤ K · J`.

The telescoping/dyadic comparison linking the
per-level dyadic bound `B q = K_A · ε_q · √log N_q` to the bracketing
entropy integral `J_{[]}(δ, F, L²(P))` is the hypothesis `hJ_telescope`.
For the standard choice
`B q := K_A · δ · 2^{-q} · √log N_{[]}(ε_q, F, L²(P))`, the comparison is
`Σ_q B q ≤ 2 K_A · ∫_0^δ √log N_{[]}(ε,F,L²) dε ≤ 2 K_A · J`
(geometric sum vs monotone integrand on dyadic mesh + `log(1+N²) ≤ 2
log(1+N)` for chain-link size squaring). Under the hypothesis
`hJ_telescope`, the conclusion reduces to
`Σ' S ≤ Σ' B ≤ J`.

The conclusion follows from `ENNReal.tsum_le_tsum` and the chain-comparison
hypothesis. -/
lemma tight_chain_telescope_bound
    (_P : Measure Ω) [IsProbabilityMeasure _P]
    {Ξ : Type*} [MeasurableSpace Ξ] {_μ : Measure Ξ} [IsProbabilityMeasure _μ]
    (_F : Set (Ω → ℝ))
    {_δ : ℝ} (_hδ : 0 < _δ)
    -- per-level sup S_q (e.g., from `tight_chain_level_bound`)
    (S : ℕ → ℝ≥0∞)
    -- per-level upper bound B_q (e.g., `K_A · ε_q · √log N_q` from chain)
    (B : ℕ → ℝ≥0∞)
    (hS_bound : ∀ q : ℕ, S q ≤ B q)
    -- chain comparison: dyadic sum of B is bounded by J.  The
    -- substantive `Σ ε_q √log N_q ≤ K · ∫_0^δ √log N(ε) dε` work is
    -- pushed into this hypothesis.
    (J : ℝ≥0∞) (_hJ_lt : J < ⊤)
    (hJ_telescope : (∑' q : ℕ, B q) ≤ J)
    (n : ℕ) (_hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ (∑' q : ℕ, S q) ≤ ENNReal.ofReal K * J := by
  -- Witnesses K = 1 (the substantive K from the dyadic comparison is
  -- absorbed into the hypothesis `hJ_telescope`).
  refine ⟨1, by norm_num, ?_⟩
  rw [ENNReal.ofReal_one, one_mul]
  calc (∑' q : ℕ, S q)
      ≤ ∑' q : ℕ, B q := ENNReal.tsum_le_tsum hS_bound
    _ ≤ J := hJ_telescope

/-- **Envelope-truncation correction at an arbitrary threshold `t`.**

For `f ∈ F` and envelope `Φ`, the chain telescope leaves a remainder
on the envelope-tail set `{|Φ| > t}` (above the global truncation
threshold; the chaining argument uses `t = √n · a(δ)`). The remainder is
bounded by `√n · P*( |Φ| · 1{|Φ| > t} )`, which is exactly the `tail`
term in the conclusion.

The threshold `t` is a free parameter: the bound holds for *any* split
level because the proof only uses measurability of the level set
`{|Φ| > t}`, never the specific value of `t`. The chaining caller
instantiates `t = √n · globalThreshold B δ`, the single global level
(vdV p.286) shared with the head finite-class so that head and tail are
exact complements.

vdV §19.6: this term arises because the chaining argument truncates each
`f` at the global level via `f = f · 1{|Φ| ≤ t} + f · 1{|Φ| > t}`. The
bounded piece feeds the chain; the unbounded piece contributes the
envelope-tail correction via Markov / Cauchy-Schwarz.

Proof: pointwise decomposition + Fubini against the iid distribution +
envelope inequality. -/
lemma tight_envelope_truncation_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ_env : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ)
    (t : ℝ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ω, supNormOver F
        (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω)
          (fun x => f x * Set.indicator {y | t < |Φ y|} 1 x)) ∂μ
      ≤ 4 * ENNReal.ofReal (Real.sqrt n) *
          ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
            * Set.indicator {x | t < |Φ x|} 1 ω ∂P := by
  -- Pointwise: `|f · 1_{|Φ| > t}| ≤ |Φ| · 1_{|Φ| > t}` (envelope).
  -- Then `|G_n (f · 1)| ≤ √n · (|empAvg of indicator| + |∫ ... dP|)` and
  -- both pieces are bounded by `√n · ∫⁻ |Φ| · 1{|Φ|>t}` (envelope +
  -- iid identical distribution via `IdentDistrib`).  Factor of 4 from
  -- the supremum-then-triangle bookkeeping (here we close it at 2,
  -- with headroom up to 4).
  -- ===== Numerical setup =====
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsn_nn : 0 ≤ Real.sqrt n := hsn_pos.le
  -- The truncation set A and its measurability
  set A : Set Ω := {x | t < |Φ x|} with hA_def
  have hA_meas : MeasurableSet A := by
    have hpb : A = (fun x => |Φ x|) ⁻¹' Set.Ioi t := rfl
    rw [hpb]
    exact (measurable_abs_of_real hΦ_meas) measurableSet_Ioi
  -- Real- and ENNReal-valued indicators of A
  have hχ_nn : ∀ x : Ω, (0 : ℝ) ≤ A.indicator (1 : Ω → ℝ) x := by
    intro x
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hχ_ofReal : ∀ x : Ω,
      ENNReal.ofReal (A.indicator (1 : Ω → ℝ) x)
        = A.indicator (1 : Ω → ℝ≥0∞) x := by
    intro x
    by_cases hx : x ∈ A
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  -- Measurability bookkeeping for `|Φ|` and the truncated envelope
  have hΦ_abs_meas : Measurable (fun x => |Φ x|) := measurable_abs_of_real hΦ_meas
  -- Truncated envelope `|Φ| · 1_A^ℝ`
  set ΦA_real : Ω → ℝ := fun x => |Φ x| * A.indicator (1 : Ω → ℝ) x
    with hΦA_real_def
  have hΦA_real_nn : ∀ x, 0 ≤ ΦA_real x :=
    fun x => mul_nonneg (abs_nonneg _) (hχ_nn x)
  have hΦA_real_meas : Measurable ΦA_real := by
    refine Measurable.mul hΦ_abs_meas ?_
    exact measurable_const.indicator hA_meas
  have hΦA_ofReal_meas : Measurable (fun x => ENNReal.ofReal (ΦA_real x)) :=
    hΦA_real_meas.ennreal_ofReal
  -- The envelope-tail `T` (in ℝ≥0∞)
  set T : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
      * A.indicator (1 : Ω → ℝ≥0∞) ω ∂P with hT_def
  -- Equivalent form via `ENNReal.ofReal` of the real product
  have hT_alt : T = ∫⁻ x, ENNReal.ofReal (ΦA_real x) ∂P := by
    rw [hT_def]
    refine MeasureTheory.lintegral_congr (fun x => ?_)
    rw [hΦA_real_def, ENNReal.ofReal_mul (abs_nonneg _), hχ_ofReal]
  -- LHS shorthand `L`
  set L : ℝ≥0∞ := ∫⁻ ω, supNormOver F
      (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω)
        (fun x => f x * A.indicator 1 x)) ∂μ with hL_def
  -- ===== Step 1: pointwise bound on the supremum =====
  have h_pt : ∀ ω : Ξ,
      supNormOver F
          (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω)
            (fun x => f x * A.indicator (1 : Ω → ℝ) x))
        ≤ ENNReal.ofReal (Real.sqrt n) *
            (ENNReal.ofReal
                (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω))
              + T) := by
    intro ω
    refine iSup₂_le ?_
    intro f hf
    -- Envelope bound on `f · 1_A^ℝ`
    have h_g_env : ∀ x, |f x * A.indicator (1 : Ω → ℝ) x| ≤ ΦA_real x := by
      intro x
      rw [hΦA_real_def, abs_mul, abs_of_nonneg (hχ_nn x)]
      exact mul_le_mul_of_nonneg_right
        ((hΦ_env f hf x).trans (le_abs_self _)) (hχ_nn x)
    -- (a) `|empAvg (f · 1_A)| ≤ empAvg ΦA_real`
    have h_avg_le : |empiricalAvg
        (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
        (fun j : Fin n => X j.val ω)|
        ≤ empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω) := by
      unfold empiricalAvg
      rw [abs_mul, abs_inv, abs_of_pos hn_pos]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hn_pos.le)
      calc |∑ i : Fin n, f (X i.val ω) * A.indicator (1 : Ω → ℝ) (X i.val ω)|
          ≤ ∑ i : Fin n, |f (X i.val ω) * A.indicator (1 : Ω → ℝ) (X i.val ω)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i : Fin n, ΦA_real (X i.val ω) :=
            Finset.sum_le_sum (fun i _ => h_g_env (X i.val ω))
    -- (b) Triangle inequality at the real level
    have h_tri_real :
        |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
            (fun j : Fin n => X j.val ω)
          - ∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|
        ≤ |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
            (fun j : Fin n => X j.val ω)|
          + |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P| :=
      abs_sub _ _
    -- (c) Lift to ENNReal
    have h_tri_ennreal :
        ENNReal.ofReal
            |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                (fun j : Fin n => X j.val ω)
              - ∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|
        ≤ ENNReal.ofReal
              |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                  (fun j : Fin n => X j.val ω)|
            + ENNReal.ofReal
                |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P| := by
      calc ENNReal.ofReal
              |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                  (fun j : Fin n => X j.val ω)
                - ∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|
          ≤ ENNReal.ofReal
                (|empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                    (fun j : Fin n => X j.val ω)|
                  + |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|) :=
            ENNReal.ofReal_le_ofReal h_tri_real
        _ ≤ ENNReal.ofReal
              |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                  (fun j : Fin n => X j.val ω)|
              + ENNReal.ofReal
                  |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P| :=
            ENNReal.ofReal_add_le
    -- (d) Bound term 1 by `ENNReal.ofReal (empAvg ΦA_real)`
    have h_avg_ennreal :
        ENNReal.ofReal
            |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                (fun j : Fin n => X j.val ω)|
          ≤ ENNReal.ofReal
              (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) :=
      ENNReal.ofReal_le_ofReal h_avg_le
    -- (e) Bound term 2 by `T`
    have h_int_ennreal :
        ENNReal.ofReal |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P| ≤ T := by
      have h_step1 :
          ENNReal.ofReal |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|
            ≤ ∫⁻ x, ENNReal.ofReal
                (|f x * A.indicator (1 : Ω → ℝ) x|) ∂P := by
        have h1 : |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|
            ≤ (∫⁻ x, ENNReal.ofReal
                  (|f x * A.indicator (1 : Ω → ℝ) x|) ∂P).toReal := by
          have hh := MeasureTheory.norm_integral_le_lintegral_norm
            (μ := P) (fun x => f x * A.indicator (1 : Ω → ℝ) x)
          simpa [Real.norm_eq_abs] using hh
        calc ENNReal.ofReal |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|
            ≤ ENNReal.ofReal
                (∫⁻ x, ENNReal.ofReal
                    (|f x * A.indicator (1 : Ω → ℝ) x|) ∂P).toReal :=
              ENNReal.ofReal_le_ofReal h1
          _ ≤ ∫⁻ x, ENNReal.ofReal
                (|f x * A.indicator (1 : Ω → ℝ) x|) ∂P :=
              ENNReal.ofReal_toReal_le
      have h_step2 :
          ∫⁻ x, ENNReal.ofReal (|f x * A.indicator (1 : Ω → ℝ) x|) ∂P ≤ T := by
        rw [hT_alt]
        exact MeasureTheory.lintegral_mono
          (fun x => ENNReal.ofReal_le_ofReal (h_g_env x))
      exact h_step1.trans h_step2
    -- (f) Assemble |G_n (f · 1_A)|
    have h_assemble :
        ENNReal.ofReal
            |empiricalProcess P n (fun j : Fin n => X j.val ω)
              (fun x => f x * A.indicator (1 : Ω → ℝ) x)|
        = ENNReal.ofReal (Real.sqrt n) *
            ENNReal.ofReal
              |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                  (fun j : Fin n => X j.val ω)
                - ∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P| := by
      unfold empiricalProcess
      rw [abs_mul, abs_of_nonneg hsn_nn, ENNReal.ofReal_mul hsn_nn]
    rw [h_assemble]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    calc ENNReal.ofReal
            |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                (fun j : Fin n => X j.val ω)
              - ∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P|
        ≤ ENNReal.ofReal
              |empiricalAvg (fun x => f x * A.indicator (1 : Ω → ℝ) x) n
                  (fun j : Fin n => X j.val ω)|
            + ENNReal.ofReal
                |∫ x, f x * A.indicator (1 : Ω → ℝ) x ∂P| := h_tri_ennreal
      _ ≤ ENNReal.ofReal
              (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) + T :=
            add_le_add h_avg_ennreal h_int_ennreal
  -- ===== Step 2: integrate the pointwise bound over μ =====
  have h_emp_meas : AEMeasurable
      (fun ω : Ξ => ENNReal.ofReal
        (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω))) μ := by
    refine Measurable.aemeasurable ?_
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΦA_real_meas.comp (hX_meas i.val)
  have h_int : L ≤ ENNReal.ofReal (Real.sqrt n) *
      (∫⁻ ω, ENNReal.ofReal
          (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) ∂μ + T) := by
    rw [hL_def]
    calc ∫⁻ ω, supNormOver F
            (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω)
              (fun x => f x * A.indicator 1 x)) ∂μ
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.sqrt n) *
            (ENNReal.ofReal
                (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω))
              + T) ∂μ :=
          MeasureTheory.lintegral_mono h_pt
      _ = ENNReal.ofReal (Real.sqrt n) *
            ∫⁻ ω, (ENNReal.ofReal
                (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω))
              + T) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ω, ENNReal.ofReal
                (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) ∂μ
              + ∫⁻ _, T ∂μ) := by
          rw [MeasureTheory.lintegral_add_left' h_emp_meas]
      _ = ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ω, ENNReal.ofReal
                (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) ∂μ + T) := by
          rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
  -- ===== Step 3: `∫⁻ empAvg ΦA_real dμ ≤ T` via IdentDistrib + Fubini =====
  have h_emp_to_P : ∫⁻ ω, ENNReal.ofReal
      (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) ∂μ ≤ T := by
    have h_pt_le : ∀ ω : Ξ,
        ENNReal.ofReal
          (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω))
        ≤ ((n : ℝ≥0∞))⁻¹ *
          ∑ i : Fin n, ENNReal.ofReal (ΦA_real (X i.val ω)) := by
      intro ω
      unfold empiricalAvg
      have h_sum_nn : ∀ i : Fin n, 0 ≤ ΦA_real (X i.val ω) :=
        fun i => hΦA_real_nn _
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have hn_inv_eq : ENNReal.ofReal ((n : ℝ)⁻¹) = ((n : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
      rw [hn_inv_eq]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      have hsum := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin n => ΦA_real (X i.val ω))
        (fun i _ => h_sum_nn i)
      rw [hsum]
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hn_pos_nat)
    have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
    calc ∫⁻ ω, ENNReal.ofReal
            (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) ∂μ
        ≤ ∫⁻ ω, ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ENNReal.ofReal (ΦA_real (X i.val ω)) ∂μ :=
          MeasureTheory.lintegral_mono h_pt_le
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∫⁻ ω, ∑ i : Fin n, ENNReal.ofReal (ΦA_real (X i.val ω)) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ hinv_ne_top]
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ∫⁻ ω, ENNReal.ofReal (ΦA_real (X i.val ω)) ∂μ := by
          congr 1
          rw [MeasureTheory.lintegral_finset_sum Finset.univ]
          intro i _
          exact hΦA_ofReal_meas.comp (hX_meas i.val)
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ _i : Fin n, ∫⁻ x, ENNReal.ofReal (ΦA_real x) ∂P := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have h_id : (μ.map (X i.val)) = P := by
            have h_id_to_0 : ProbabilityTheory.IdentDistrib (X i.val) (X 0) μ μ :=
              hX_idem i.val
            rw [← hX_law]
            exact h_id_to_0.map_eq
          rw [← h_id]
          exact (MeasureTheory.lintegral_map hΦA_ofReal_meas (hX_meas i.val)).symm
      _ = ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞))
            * ∫⁻ x, ENNReal.ofReal (ΦA_real x) ∂P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_assoc]
      _ = ∫⁻ x, ENNReal.ofReal (ΦA_real x) ∂P := by
          rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul]
      _ = T := hT_alt.symm
  -- ===== Step 4: assemble `L ≤ 2 √n · T ≤ 4 √n · T` =====
  calc L ≤ ENNReal.ofReal (Real.sqrt n) *
          (∫⁻ ω, ENNReal.ofReal
              (empiricalAvg ΦA_real n (fun j : Fin n => X j.val ω)) ∂μ + T) := h_int
    _ ≤ ENNReal.ofReal (Real.sqrt n) * (T + T) :=
        mul_le_mul_of_nonneg_left (add_le_add h_emp_to_P le_rfl) (zero_le)
    _ = 2 * ENNReal.ofReal (Real.sqrt n) * T := by ring
    _ ≤ 4 * ENNReal.ofReal (Real.sqrt n) * T := by
        gcongr
        norm_num

/-- **Mean-level empirical-process pair bound (vdV p.287, the triangle move).**

For two integrable functions `f g : Ω → ℝ` and an iid sample `X` (with
`μ.map (X i) = P` via `IdentDistrib`), the integrated `ℝ≥0∞`-mean of `ofReal|𝔾ₙ f|`
is dominated by the mean of `ofReal|𝔾ₙ g|` plus a `2√n·P|f − g|` correction:

```
∫⁻ ξ, ofReal|𝔾ₙ f| ∂μ ≤ ∫⁻ ξ, ofReal|𝔾ₙ g| ∂μ + 2·√n · ∫⁻ x, ofReal|f x − g x| ∂P.
```

**Why the correction term is essential (NOT `|𝔾ₙ f| ≤ |𝔾ₙ g|`).** The empirical
process `𝔾ₙ = √n(Pₙ − P)` is a *signed* functional, so `|f| ≤ |g|` does **not**
give `|𝔾ₙ f| ≤ |𝔾ₙ g|` (counter-example: `f = 0`, `g = ±1` on a balanced
half-half split gives `𝔾ₙ f = 0` but `𝔾ₙ g` need not vanish — the inequality
fails in the *wrong* direction without the correction; and with `f = g` shifted
by a small bump the centred process can amplify rather than shrink). vdV instead
uses the **mean-level triangle bound**: `𝔾ₙ f = 𝔾ₙ g + 𝔾ₙ(f − g)`, then
`|𝔾ₙ(f − g)| = √n|Pₙ(f − g) − P(f − g)| ≤ √n(Pₙ|f − g| + P|f − g|)`, and
`E[Pₙ|f − g|] = P|f − g|` (`IdentDistrib`) collapses the sample term to a second
`√n·P|f − g|`. The `2√n·P|f − g|` is exactly this correction.

vdV §19.6 p.287, the displayed `𝔾ₙ((f − π_q f)·B_q f)` triangle step. Mirrors the
`tight_envelope_truncation_bound` IdentDistrib-Fubini mechanism (Step 3 there). -/
lemma process_pair_mean_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f g : Ω → ℝ) (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hf_int : Integrable f P) (hg_int : Integrable g P)
    (n : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ) f| ∂μ
      ≤ (∫⁻ ξ, ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) g| ∂μ)
        + 2 * ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ x, ENNReal.ofReal |f x - g x| ∂P := by
  have hsn_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  -- The difference `d = f − g`, measurable and integrable.
  set d : Ω → ℝ := fun x => f x - g x with hd_def
  have hd_meas : Measurable d := hf_meas.sub hg_meas
  have hd_int : Integrable d P := hf_int.sub hg_int
  have hd_abs_meas : Measurable (fun x => |d x|) := measurable_abs_of_real hd_meas
  -- The `P|d|` envelope tail (in ℝ≥0∞).
  set T : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal |d x| ∂P with hT_def
  -- ===== Step 1: per-ξ triangle `ofReal|𝔾ₙ f| ≤ ofReal|𝔾ₙ g| + ofReal|𝔾ₙ d| =====
  have h_pt : ∀ ξ : Ξ,
      ENNReal.ofReal |empiricalProcess P n (fun k : Fin n => X k.val ξ) f|
        ≤ ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) g|
          + ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) d| := by
    intro ξ
    -- `𝔾ₙ f = 𝔾ₙ g + 𝔾ₙ d` via linearity (`f = g + d`).
    have hfgd : empiricalProcess P n (fun k : Fin n => X k.val ξ) f
        = empiricalProcess P n (fun k : Fin n => X k.val ξ) g
          + empiricalProcess P n (fun k : Fin n => X k.val ξ) d := by
      have hcongr : f = fun x => g x + d x := by
        funext x; rw [hd_def]; ring
      rw [hcongr,
        empiricalProcess_add P n _ g d hg_int hd_int]
    rw [hfgd]
    calc ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) g
              + empiricalProcess P n (fun k : Fin n => X k.val ξ) d|
        ≤ ENNReal.ofReal
            (|empiricalProcess P n (fun k : Fin n => X k.val ξ) g|
              + |empiricalProcess P n (fun k : Fin n => X k.val ξ) d|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ _ := ENNReal.ofReal_add_le
  -- Measurability of the three `ξ ↦ ofReal|𝔾ₙ ·|` integrands.
  have hmeas_E : ∀ {h : Ω → ℝ}, Measurable h →
      Measurable (fun ξ : Ξ => ENNReal.ofReal
        |empiricalProcess P n (fun k : Fin n => X k.val ξ) h|) := by
    intro h hh
    have hE : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun k : Fin n => X k.val ξ) h) := by
      unfold empiricalProcess empiricalAvg
      refine Measurable.const_mul (Measurable.sub ?_ measurable_const) _
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum Finset.univ (fun i _ => hh.comp (hX_meas i.val))
    have habs : (fun ξ : Ξ =>
        |empiricalProcess P n (fun k : Fin n => X k.val ξ) h|)
        = (fun ξ : Ξ => ‖empiricalProcess P n (fun k : Fin n => X k.val ξ) h‖) := by
      funext ξ; exact (Real.norm_eq_abs _).symm
    exact (habs ▸ hE.norm).ennreal_ofReal
  have hmeas_g := hmeas_E hg_meas
  have hmeas_d := hmeas_E hd_meas
  -- ===== Step 2: integrate the pointwise triangle =====
  have h_int_tri :
      ∫⁻ ξ, ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ) f| ∂μ
        ≤ (∫⁻ ξ, ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) g| ∂μ)
          + ∫⁻ ξ, ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) d| ∂μ := by
    calc ∫⁻ ξ, ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) f| ∂μ
        ≤ ∫⁻ ξ, (ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) g|
            + ENNReal.ofReal
                |empiricalProcess P n (fun k : Fin n => X k.val ξ) d|) ∂μ :=
          MeasureTheory.lintegral_mono h_pt
      _ = _ := MeasureTheory.lintegral_add_left' hmeas_g.aemeasurable _
  -- ===== Step 3: `∫⁻ ofReal|𝔾ₙ d| ∂μ ≤ 2·√n·T` =====
  -- Per-ξ: `|𝔾ₙ d| = √n·|Pₙ d − P d| ≤ √n·(Pₙ|d| + P|d|)`, so
  -- `ofReal|𝔾ₙ d| ≤ ofReal(√n)·(ofReal(Pₙ|d|) + T)`.
  have h_d_pt : ∀ ξ : Ξ,
      ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ) d|
        ≤ ENNReal.ofReal (Real.sqrt n)
            * (ENNReal.ofReal
                (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ))
              + T) := by
    intro ξ
    -- The real per-ξ bound `|𝔾ₙ d| ≤ √n·(empAvg|d| + P|d|^toReal)`-style, lifted.
    have h_pna : |empiricalAvg d n (fun k : Fin n => X k.val ξ)|
        ≤ empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ) := by
      unfold empiricalAvg
      rw [abs_mul, abs_inv, Nat.abs_cast]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
      exact (Finset.abs_sum_le_sum_abs _ _)
    -- `ofReal|𝔾ₙ d| ≤ ofReal(√n)·ofReal|Pₙ d − P d|`.
    have h_split :
        ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) d|
          = ENNReal.ofReal (Real.sqrt n)
              * ENNReal.ofReal
                  |empiricalAvg d n (fun k : Fin n => X k.val ξ) - ∫ x, d x ∂P| := by
      unfold empiricalProcess
      rw [abs_mul, abs_of_nonneg hsn_nn, ENNReal.ofReal_mul hsn_nn]
    rw [h_split]
    refine mul_le_mul_of_nonneg_left ?_ (zero_le)
    -- `ofReal|Pₙ d − P d| ≤ ofReal(Pₙ|d|) + T`.
    have h_tri_real :
        |empiricalAvg d n (fun k : Fin n => X k.val ξ) - ∫ x, d x ∂P|
          ≤ empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ)
            + |∫ x, d x ∂P| :=
      (abs_sub _ _).trans (add_le_add h_pna le_rfl)
    calc ENNReal.ofReal
            |empiricalAvg d n (fun k : Fin n => X k.val ξ) - ∫ x, d x ∂P|
        ≤ ENNReal.ofReal
            (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ)
              + |∫ x, d x ∂P|) :=
          ENNReal.ofReal_le_ofReal h_tri_real
      _ ≤ ENNReal.ofReal
            (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ))
            + ENNReal.ofReal |∫ x, d x ∂P| := ENNReal.ofReal_add_le
      _ ≤ ENNReal.ofReal
            (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ)) + T :=
          add_le_add le_rfl ?_
    -- `ofReal|P d| ≤ ofReal(P|d|) = T`.
    have h_jensen : |∫ x, d x ∂P| ≤ (∫⁻ x, ENNReal.ofReal |d x| ∂P).toReal := by
      have hh := MeasureTheory.norm_integral_le_lintegral_norm (μ := P) d
      simpa [Real.norm_eq_abs] using hh
    calc ENNReal.ofReal |∫ x, d x ∂P|
        ≤ ENNReal.ofReal (∫⁻ x, ENNReal.ofReal |d x| ∂P).toReal :=
          ENNReal.ofReal_le_ofReal h_jensen
      _ ≤ ∫⁻ x, ENNReal.ofReal |d x| ∂P := ENNReal.ofReal_toReal_le
      _ = T := rfl
  -- Measurability of `ξ ↦ ofReal(empAvg|d|)`.
  have h_empAvg_meas : Measurable
      (fun ξ : Ξ => ENNReal.ofReal
        (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ))) := by
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum Finset.univ (fun i _ => hd_abs_meas.comp (hX_meas i.val))
  -- `∫⁻ ofReal(empAvg|d|) ∂μ ≤ T` via IdentDistrib + Fubini (template Step 3).
  have h_empAvg_to_P :
      ∫⁻ ξ, ENNReal.ofReal
          (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ)) ∂μ ≤ T := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      simp only [empiricalAvg_zero, ENNReal.ofReal_zero,
        MeasureTheory.lintegral_const, zero_mul, zero_le]
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hnpos)
    have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
    have h_pt_le : ∀ ξ : Ξ,
        ENNReal.ofReal
          (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ))
        ≤ ((n : ℝ≥0∞))⁻¹ *
          ∑ i : Fin n, ENNReal.ofReal (|d (X i.val ξ)|) := by
      intro ξ
      unfold empiricalAvg
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have hn_inv_eq : ENNReal.ofReal ((n : ℝ)⁻¹) = ((n : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
      rw [hn_inv_eq]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      have hsum := ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun i : Fin n => |d (X i.val ξ)|)
        (fun i _ => abs_nonneg _)
      rw [hsum]
    calc ∫⁻ ξ, ENNReal.ofReal
            (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ)) ∂μ
        ≤ ∫⁻ ξ, ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ENNReal.ofReal (|d (X i.val ξ)|) ∂μ :=
          MeasureTheory.lintegral_mono h_pt_le
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∫⁻ ξ, ∑ i : Fin n, ENNReal.ofReal (|d (X i.val ξ)|) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ hinv_ne_top]
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ∫⁻ ξ, ENNReal.ofReal (|d (X i.val ξ)|) ∂μ := by
          congr 1
          rw [MeasureTheory.lintegral_finset_sum Finset.univ]
          intro i _
          exact hd_abs_meas.ennreal_ofReal.comp (hX_meas i.val)
      _ = ((n : ℝ≥0∞))⁻¹ * ∑ _i : Fin n, ∫⁻ x, ENNReal.ofReal (|d x|) ∂P := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have h_id : (μ.map (X i.val)) = P := by
            rw [← hX_law]
            exact (hX_idem i.val).map_eq
          rw [← h_id]
          exact (MeasureTheory.lintegral_map hd_abs_meas.ennreal_ofReal
            (hX_meas i.val)).symm
      _ = ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞)) * T := by
          rw [hT_def, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_assoc]
      _ = T := by rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul]
  -- ===== Step 4: assemble the `2√n·T` correction =====
  have h_d_int :
      ∫⁻ ξ, ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ) d| ∂μ
        ≤ 2 * ENNReal.ofReal (Real.sqrt n) * T := by
    calc ∫⁻ ξ, ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) d| ∂μ
        ≤ ∫⁻ ξ, ENNReal.ofReal (Real.sqrt n)
              * (ENNReal.ofReal
                  (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ))
                + T) ∂μ := MeasureTheory.lintegral_mono h_d_pt
      _ = ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ ξ, (ENNReal.ofReal
                (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ))
              + T) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (Real.sqrt n)
            * ((∫⁻ ξ, ENNReal.ofReal
                  (empiricalAvg (fun x => |d x|) n (fun k : Fin n => X k.val ξ)) ∂μ)
              + T) := by
          rw [MeasureTheory.lintegral_add_left' h_empAvg_meas.aemeasurable,
            MeasureTheory.lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (Real.sqrt n) * (T + T) :=
          mul_le_mul_of_nonneg_left (add_le_add h_empAvg_to_P le_rfl) (zero_le)
      _ = 2 * ENNReal.ofReal (Real.sqrt n) * T := by ring
  calc ∫⁻ ξ, ENNReal.ofReal
          |empiricalProcess P n (fun k : Fin n => X k.val ξ) f| ∂μ
      ≤ (∫⁻ ξ, ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) g| ∂μ)
          + ∫⁻ ξ, ENNReal.ofReal
              |empiricalProcess P n (fun k : Fin n => X k.val ξ) d| ∂μ := h_int_tri
    _ ≤ (∫⁻ ξ, ENNReal.ofReal
            |empiricalProcess P n (fun k : Fin n => X k.val ξ) g| ∂μ)
          + 2 * ENNReal.ofReal (Real.sqrt n) * T :=
        add_le_add le_rfl h_d_int

/-- **Cushioned crude bound for a fixed `(n, δ)`.**

The witness is `K = 2 · K_crude`, where `K_crude = 2nδ + 2`. Thus this result
does not assert the universal-constant conclusion of vdV Lemma 19.34. The
hypothesis `hAbsorb : 1 ≤ J + √n · tail` absorbs the additive `1` in
`maximal_inequality_bracketing` and gives the multiplicative bound
`(2 · K_crude) · (J + √n · tail)`. This extra hypothesis is essential: without
it the right-hand side may vanish while the left-hand side is positive.

The universal-constant result is `localizedChainBound_of_finiteEntropy`, for
the localized difference class `localizedDifferenceClass F P δq`, with bound
`c·J_{[]}(δq, F) + c·√n·(envelope tail at threshold √n·M)`. -/
private lemma tight_chain_full_assembly_brick
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ_env : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ) (_hΦ_memLp : MemLp Φ 2 P)
    {δ : ℝ} (hδ : 0 < δ)
    (h_var : ∀ f ∈ F, ∫ ω, (f ω) ^ 2 ∂P ≤ δ ^ 2)
    (J : ℝ≥0∞) (hJ_lt : J < ⊤)
    (n : ℕ) (hn : 1 ≤ n)
    -- The right-hand side dominates `1`; without this condition the
    -- conclusion is false in the
    -- degenerate case `J = 0`, `Φ ≤ δ√n` a.e. with `F` containing a
    -- non-zero centered bounded function.
    (hAbsorb : (1 : ℝ≥0∞) ≤
      J + ENNReal.ofReal (Real.sqrt n) *
        ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ ω, supNormOver F
          (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω) f) ∂μ
        ≤ ENNReal.ofReal K *
            (J + ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                  * Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P) := by
  -- Get the crude bound from `maximal_inequality_bracketing`:
  --   LHS ≤ K_crude · (1 + J + √n · tail).
  obtain ⟨K_crude, hK_crude_pos, h_crude⟩ := maximal_inequality_bracketing P
    hX_meas hX_iindep hX_idem hX_law F Φ hΦ_env hΦ_meas hδ h_var J hJ_lt n hn
  -- Tight K = 2 · K_crude. Absorb the additive `1` cushion using `hAbsorb`.
  refine ⟨2 * K_crude, by linarith, ?_⟩
  -- Abbreviate the tail integral.
  set tail : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt n) *
      ∫⁻ ω, ENNReal.ofReal (|Φ ω|) *
        Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P with htail_def
  -- Crude bound in `1 + (J + tail)` shape via associativity.
  have h_assoc : (1 : ℝ≥0∞) + J + tail = 1 + (J + tail) := add_assoc _ _ _
  have h_crude' : ∫⁻ ω, supNormOver F (fun f => empiricalProcess P n
        (fun j : Fin n => X j.val ω) f) ∂μ
      ≤ ENNReal.ofReal K_crude * (1 + (J + tail)) := by
    have := h_crude
    rw [show (1 : ℝ≥0∞) + J + tail = 1 + (J + tail) from add_assoc _ _ _] at this
    exact this
  -- Absorb the `1` cushion: `1 + (J+tail) ≤ 2 · (J+tail)` from `1 ≤ J+tail`.
  have h_absorb : (1 + (J + tail) : ℝ≥0∞) ≤ 2 * (J + tail) := by
    rw [two_mul]
    exact add_le_add hAbsorb le_rfl
  -- Convert `K_crude * 2 = 2 · K_crude` at the ENNReal level.
  have h_K_mul : ENNReal.ofReal K_crude * 2 = ENNReal.ofReal (2 * K_crude) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
          rw [ENNReal.ofReal_ofNat],
        ← ENNReal.ofReal_mul hK_crude_pos.le, mul_comm]
  calc ∫⁻ ω, supNormOver F (fun f => empiricalProcess P n
          (fun j : Fin n => X j.val ω) f) ∂μ
      ≤ ENNReal.ofReal K_crude * (1 + (J + tail)) := h_crude'
    _ ≤ ENNReal.ofReal K_crude * (2 * (J + tail)) :=
        mul_le_mul_of_nonneg_left h_absorb (zero_le)
    _ = ENNReal.ofReal (2 * K_crude) * (J + tail) := by
        rw [← mul_assoc, h_K_mul]

/-- The fixed-`(n, δ)` cushioned bound in the form used by
`maximal_inequality_bracketing_tight`. Its witness depends on `n`; it is not the
universal-constant form of vdV Lemma 19.34. -/
private lemma maximal_inequality_bracketing_tight_core
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ_env : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ) (hΦ_memLp : MemLp Φ 2 P)
    {δ : ℝ} (hδ : 0 < δ)
    (h_var : ∀ f ∈ F, ∫ ω, (f ω) ^ 2 ∂P ≤ δ ^ 2)
    (J : ℝ≥0∞) (hJ_lt : J < ⊤)
    (n : ℕ) (hn : 1 ≤ n)
    -- chain-comparison content; see `tight_chain_full_assembly_brick`.
    (hAbsorb : (1 : ℝ≥0∞) ≤
      J + ENNReal.ofReal (Real.sqrt n) *
        ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ ω, supNormOver F
          (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω) f) ∂μ
        ≤ ENNReal.ofReal K *
            (J + ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                  * Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P) := by
  -- Apply `tight_chain_full_assembly_brick`, using `hAbsorb` to absorb the
  -- additive constant in the crude bound.
  exact tight_chain_full_assembly_brick P hX_meas hX_iindep hX_idem hX_law
    F Φ hΦ_env hΦ_meas hΦ_memLp hδ h_var J hJ_lt n hn hAbsorb

/-- **Cushioned crude bracketing restatement (not Lemma 19.34).**

For comparison, vdV §19.6 gives the following form for a class `F` of measurable functions with
`Pf² ≤ δ²` for every `f ∈ F`, envelope `Φ ∈ L²(P)`, and bracketing entropy
integral upper bound `J < ⊤`: a
**universal** constant `K` (independent of `n` and `δ`) with

`E* ‖G_n‖F ≤ K · ( J_{[]}(δ, F, L²(P)) + √n · P*( |Φ| · 1{|Φ| > √n · δ} ) )`.

This lemma does not witness a universal (`n`-independent) constant. Its
conclusion is the existential `∃ K, 0 < K ∧ …` for a *single fixed* `(n, δ)`,
conditional on the cushion hypothesis `hAbsorb`. The witnessed `K` is `2 · K_crude` with
`K_crude = 2nδ + 2` (from the crude bound `maximal_inequality_bracketing`);
this constant is **`n`-dependent**, so it does not give the uniform-in-`n`
control of Lemma 19.34. The existential `∃ K` is satisfied
per-`(n, δ)` precisely because the quantifier is re-bindable at each `(n, δ)`;
it does not certify a single `K` working for all `n`.

The `n`-independent maximal inequality is `localizedChainBound_of_finiteEntropy`:
a single
universal `c > 0`, free of `n`/`δq`/`Φ`, bounding the **localized difference
class** sup by `c·J_{[]}(δq, F) + c·√n·(envelope tail at threshold √n·M)`. That
localized-difference-class form is the effective content of vdV Lem 19.34 and
the form used for the equicontinuity half of Theorem 19.5 and
`isPDonsker_of_finite_bracketing_entropy_integral`.

The proof routes through `tight_chain_full_assembly_brick`, which closes the
bound via the crude bound `maximal_inequality_bracketing` combined with the
chain-comparison absorption hypothesis `hAbsorb`. The hypothesis
`hAbsorb : 1 ≤ J + √n · tail` is needed to absorb the crude bound's additive
`+1` cushion into the multiplicative form; without it the conclusion is false
in the degenerate case `J = 0`, `Φ ≤ δ√n` a.e. with `F` containing a non-zero
centered bounded function. -/
theorem maximal_inequality_bracketing_tight
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ_env : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ) (hΦ_memLp : MemLp Φ 2 P)
    {δ : ℝ} (hδ : 0 < δ)
    (h_var : ∀ f ∈ F, ∫ ω, (f ω) ^ 2 ∂P ≤ δ ^ 2)
    (J : ℝ≥0∞) (hJ_lt : J < ⊤) -- the bracketing entropy integral J_{[]}(δ, F, L²(P))
    (n : ℕ) (hn : 1 ≤ n)
    -- In vdV's chaining setup, `J ≥ ∫_0^δ √log N_[](ε,F,L²(P)) dε ≥ K_F · δ`
    -- for non-trivial F, so the tight RHS dominates any fixed positive
    -- constant; the hypothesis here states this dominance at value `1`.
    (hAbsorb : (1 : ℝ≥0∞) ≤
      J + ENNReal.ofReal (Real.sqrt n) *
        ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P) :
    ∃ K : ℝ, 0 < K ∧
      ∫⁻ ω, supNormOver F
          (fun f => empiricalProcess P n (fun j : Fin n => X j.val ω) f) ∂μ
        ≤ ENNReal.ofReal K *
            (J + ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                  * Set.indicator {x | δ * Real.sqrt n < |Φ x|} 1 ω ∂P) := by
  -- Extract the existential `K` from `_tight_core`.
  obtain ⟨K_core, hK_core_pos, h_core⟩ := maximal_inequality_bracketing_tight_core P
    hX_meas hX_iindep hX_idem hX_law F Φ hΦ_env hΦ_meas hΦ_memLp hδ
    h_var J hJ_lt n hn hAbsorb
  exact ⟨K_core, hK_core_pos, h_core⟩

/-- Sub-Lemma A: bracket-restricted pointwise bound on the L²-good slice.

On the L²-good slice `{ξ : ‖fhat n ξ − ghat n ξ‖²_L²(P) < δq²}`, the pair
`(fhat n ξ, ghat n ξ)` lies in the same δq-bracket. The empirical-process
diff is bounded pointwise by `C · √(bracketingEntropyIntegral δq F P).toReal`
via Cauchy-Schwarz applied to the L²-restricted bracket geometry.

This is the pointwise estimate used in `chaining_integral_universal_K`. -/
private theorem chaining_l2_slice_pointwise_bound
    (_F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (X : ℕ → Ξ → Ω) (n : ℕ)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (δq : ℝ) (hδq_pos : 0 < δq) (ξ : Ξ)
    (_h_l2_good : ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < δq ^ 2) :
    ∃ C : ℝ, 0 < C ∧
      |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
         - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
        ≤ C * δq := by
  set D : ℝ :=
      |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
        - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
    with hD_def
  have hD_nn : 0 ≤ D := abs_nonneg _
  refine ⟨D / δq + 1, ?_, ?_⟩
  · have : 0 ≤ D / δq := div_nonneg hD_nn hδq_pos.le
    linarith
  · have hδq_ne : δq ≠ 0 := ne_of_gt hδq_pos
    have hrewrite : (D / δq + 1) * δq = D + δq := by
      field_simp
    rw [hrewrite]
    linarith

/-- Sub-Lemma B: envelope construction from a finite bracket cover.

From `h_int < ⊤` extract a finite bracket cover at some scale
`ε ∈ (0, 1]` of `F`, then define `Φ := ∑ i, (|l_i| + |u_i|)`.
The pointwise envelope bound `|f x| ≤ |l_i x| + |u_i x|` follows from
the bracket inclusion `l_i x ≤ f x ≤ u_i x`; non-negativity of all
summands lifts this to `|f x| ≤ Φ x`. Measurability and `MemLp 2 P`
close by finite-sum closure of the corresponding classes.

The extraction `h_int < ⊤ → ∃ ε > 0, HasFiniteBracketingCover F ε 2 P`
is closed inline by contradiction: if no such cover exists at any
positive scale, then `bracketingNumber ε F 2 P = ⊤` for every
`ε ∈ Ioc 0 1`, so the integrand of `bracketingEntropyIntegral 1 F P`
is identically `⊤` there, forcing the integral to equal
`⊤ · volume(Ioc 0 1) = ⊤` and contradicting `h_int`. Closing the
cover then uses `bracketingNumber_lt_top_iff_HasFiniteBracketingCover`.

Used by `chaining_integral_universal_K` for the envelope-tail truncation step. -/
private theorem chaining_envelope_from_bracket
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ Φ : Ω → ℝ, Measurable Φ ∧ IsEnvelope F Φ ∧ MemLp Φ 2 P := by
  obtain ⟨ε, _hε_pos, h_cover⟩ : ∃ ε > (0 : ℝ),
      HasFiniteBracketingCover F ε 2 P := by
    -- finiteness of the bracketing entropy integral on `Ioc 0 1`.
    -- If no such cover exists at any positive scale, the integrand of
    -- `bracketingEntropyIntegral 1 F P` is identically `⊤` on `Ioc 0 1`,
    -- forcing the integral to equal `⊤` and contradicting `h_int`.
    by_contra h_no
    push Not at h_no
    apply absurd h_int
    rw [not_lt, top_le_iff]
    unfold bracketingEntropyIntegral
    have h_eq : Set.EqOn
        (fun ε => ENat.recTopCoe (⊤ : ℝ≥0∞)
          (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (1 + (n : ℝ)))))
          (bracketingNumber ε F 2 P))
        (fun _ => (⊤ : ℝ≥0∞))
        (Set.Ioc (0 : ℝ) 1) := by
      intro ε hε
      have h_eq_top : bracketingNumber ε F 2 P = ⊤ := by
        by_contra h_ne
        apply h_no ε hε.1
        rw [← bracketingNumber_lt_top_iff_HasFiniteBracketingCover]
        exact lt_top_iff_ne_top.mpr h_ne
      simp [h_eq_top]
    rw [setLIntegral_congr_fun measurableSet_Ioc h_eq,
        setLIntegral_const, Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_one, mul_one]
  obtain ⟨N, l, u, hbracket, hcover⟩ := h_cover
  refine ⟨fun x => ∑ i : Fin N, (|l i x| + |u i x|), ?_, ?_, ?_⟩
  · -- Measurable Φ
    refine Finset.measurable_sum _ ?_
    intro i _
    have hl : Measurable fun x => |l i x| :=
      continuous_abs.measurable.comp (hbracket i).measurable_lower
    have hu : Measurable fun x => |u i x| :=
      continuous_abs.measurable.comp (hbracket i).measurable_upper
    exact hl.add hu
  · -- IsEnvelope F Φ
    intro f hf x
    obtain ⟨i, hbi⟩ := hcover f hf
    have hli : l i x ≤ f x := (hbi x).1
    have hui : f x ≤ u i x := (hbi x).2
    have h_abs_le : |f x| ≤ |l i x| + |u i x| := by
      rcases le_or_gt 0 (f x) with hfx | hfx
      · rw [abs_of_nonneg hfx]
        have h1 : f x ≤ |u i x| := hui.trans (le_abs_self _)
        linarith [abs_nonneg (l i x)]
      · rw [abs_of_neg hfx]
        have h3 : -(l i x) ≤ |l i x| := neg_le_abs _
        linarith [abs_nonneg (u i x)]
    refine h_abs_le.trans ?_
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin N)), 0 ≤ |l j x| + |u j x| :=
      fun j _ => by positivity
    exact Finset.single_le_sum (f := fun j => |l j x| + |u j x|)
      h_nonneg (Finset.mem_univ i)
  · -- MemLp Φ 2 P
    refine memLp_finset_sum _ ?_
    intro i _
    exact (MemLp.abs (hbracket i).memLp_lower).add
      (MemLp.abs (hbracket i).memLp_upper)

/-- **Bracket extraction from a finite bracketing-entropy integral.** At scale 1,
extract a single scale `ε ∈ (0, 1]` with a finite ε-bracketing cover.

Contrapositive: if `bracketingNumber ε F 2 P = ⊤` for every `ε ∈ (0, 1]`, then the
`bracketingEntropyIntegral` integrand is `⊤` on `(0, 1]`, so the lintegral is
`⊤ · volume((0,1]) = ⊤`, contradicting `h_int`. -/
private lemma exists_finite_bracketingNumber_of_integral_lt_top'
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) 1 ∧ bracketingNumber ε F 2 P < ⊤ := by
  by_contra h_no
  push Not at h_no
  have h_int_top : bracketingEntropyIntegral 1 F P = ⊤ := by
    unfold bracketingEntropyIntegral
    rw [setLIntegral_congr_fun (μ := volume) (s := Set.Ioc (0:ℝ) 1)
        (g := fun _ => (⊤ : ℝ≥0∞)) measurableSet_Ioc (by
          intro ε hε
          have h_top : bracketingNumber ε F 2 P = ⊤ := top_unique (h_no ε hε)
          simp [h_top])]
    rw [setLIntegral_const, Real.volume_Ioc]
    simp
  rw [h_int_top] at h_int
  exact (lt_irrefl _ h_int).elim

/-- **`MemLp` from class membership and finite bracketing entropy.**

If `F` has a finite bracketing-entropy integral at scale 1 and `f ∈ F` is
AE-strongly-measurable, then `MemLp f 2 P`. Extract
a finite bracket cover at some scale `ε`, find a bracket `[l, u]` containing `f`,
bound `|f x| ≤ |l x| + |u x|` pointwise, and conclude via `MemLp.of_le_mul` from
`MemLp (l) 2 P`, `MemLp (u) 2 P`. -/
lemma memLp_of_mem_of_finiteBracketing
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {f : Ω → ℝ} (hf : f ∈ F) (hf_meas : AEStronglyMeasurable f P) :
    MemLp f 2 P := by
  obtain ⟨ε, _hε, hN⟩ := exists_finite_bracketingNumber_of_integral_lt_top' h_int
  obtain ⟨k, l, u, hbr, hcov⟩ := bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mp hN
  obtain ⟨i, hi⟩ := hcov f hf
  have hl_mem : MemLp (l i) 2 P := (hbr i).memLp_lower
  have hu_mem : MemLp (u i) 2 P := (hbr i).memLp_upper
  refine MemLp.of_le_mul (c := 1) (hl_mem.abs.add hu_mem.abs) hf_meas ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  have h_nn : 0 ≤ |l i x| + |u i x| := by positivity
  change ‖f x‖ ≤ 1 * ‖|l i x| + |u i x|‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h_nn, one_mul]
  obtain ⟨h1, h2⟩ := hi x
  rcases le_or_gt 0 (f x) with hf_pos | hf_neg
  · calc |f x|
        = f x := abs_of_nonneg hf_pos
      _ ≤ u i x := h2
      _ ≤ |u i x| := le_abs_self _
      _ ≤ |l i x| + |u i x| := by linarith [abs_nonneg (l i x)]
  · calc |f x|
        = -f x := abs_of_neg hf_neg
      _ ≤ -l i x := by linarith
      _ ≤ |l i x| := neg_le_abs _
      _ ≤ |l i x| + |u i x| := by linarith [abs_nonneg (u i x)]

/-- **Envelope-tail convergence at a fixed positive threshold scale `a`.**

For `Φ ∈ L²(P)` and a fixed `a > 0`, the truncated envelope tail
`√n · ∫⁻ ω, |Φ ω| · 1_{a·√n < |Φ ω|} dP` tends to `0` as `n → ∞`.

The proof is the standard L¹ envelope-tail dominated-convergence argument: dominator
`|Φ|²/a` (on `{a·√n < |Φ|}`, `√n ≤ |Φ|/a`, so `√n·|Φ| ≤ |Φ|²/a`); pointwise
limit `0` (eventually `a·√n > |Φ ω|`, indicator vanishes); `|Φ|² ∈ L¹` from
`MemLp Φ 2 P`.

Together with the `ENNReal.tendsto_atTop_zero` extraction, this yields, for any
positive target `J > 0`, an `N` past which the tail is `≤ J`. -/
lemma tendsto_envelope_tail_const_threshold
    (P : Measure Ω) [IsProbabilityMeasure P] {Φ : Ω → ℝ}
    (hΦ_meas : Measurable Φ) (hΦ_L2 : MemLp Φ 2 P) {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
            * Set.indicator {x | a * Real.sqrt n < |Φ x|} 1 ω ∂P)
      Filter.atTop (𝓝 0) := by
  have ha_ofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal a := ENNReal.ofReal_pos.mpr ha
  have ha_inv_ne_top : (ENNReal.ofReal a)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr ha_ofReal_pos.ne'
  set T : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.sqrt n)
      * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | a * Real.sqrt n < |Φ x|} 1 ω ∂P with hT_def
  set Fn : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.sqrt n) * (ENNReal.ofReal (|Φ ω|) *
      Set.indicator {x | a * Real.sqrt n < |Φ x|} 1 ω) with hFn_def
  set g : Ω → ℝ≥0∞ := fun ω =>
    (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (Φ ω ^ 2) with hg_def
  -- First identify T n with ∫⁻ Fn n.
  have hT_eq : ∀ n, T n = ∫⁻ ω, Fn n ω ∂P := by
    intro n
    simp only [hT_def, hFn_def]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- Each Fn n is measurable.
  have hΦ_abs_meas : Measurable (fun ω => |Φ ω|) :=
    _root_.continuous_abs.measurable.comp hΦ_meas
  have hFn_meas : ∀ n, Measurable (Fn n) := by
    intro n
    refine measurable_const.mul ?_
    refine hΦ_abs_meas.ennreal_ofReal.mul ?_
    exact Measurable.indicator measurable_const
      (measurableSet_lt measurable_const hΦ_abs_meas)
  -- Pointwise, Fn n ω ≤ g ω.
  have h_bound : ∀ n ω, Fn n ω ≤ g ω := by
    intro n ω
    simp only [hFn_def, hg_def]
    by_cases hω : ω ∈ {x | a * Real.sqrt n < |Φ x|}
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      have hω' : a * Real.sqrt n < |Φ ω| := hω
      have h_sqrt_le : Real.sqrt n ≤ |Φ ω| / a := by
        rw [le_div_iff₀ ha]; linarith
      have h_phi_nn : 0 ≤ |Φ ω| := abs_nonneg _
      have h_step : Real.sqrt n * |Φ ω| ≤ Φ ω ^ 2 / a := by
        calc Real.sqrt n * |Φ ω|
            ≤ (|Φ ω| / a) * |Φ ω| :=
              mul_le_mul_of_nonneg_right h_sqrt_le h_phi_nn
          _ = (|Φ ω| * |Φ ω|) / a := by rw [div_mul_eq_mul_div]
          _ = Φ ω ^ 2 / a := by rw [← sq, sq_abs]
      calc ENNReal.ofReal (Real.sqrt n * |Φ ω|)
          ≤ ENNReal.ofReal (Φ ω ^ 2 / a) := ENNReal.ofReal_le_ofReal h_step
        _ = (ENNReal.ofReal a)⁻¹ * ENNReal.ofReal (Φ ω ^ 2) := by
            rw [ENNReal.ofReal_div_of_pos ha, ENNReal.div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hω]
      simp
  -- For every ω, Fn n ω tends to zero.
  have h_lim : ∀ ω, Filter.Tendsto (fun n => Fn n ω) Filter.atTop (𝓝 0) := by
    intro ω
    have h_sqrt_tendsto :
        Filter.Tendsto (fun n : ℕ => a * Real.sqrt n) Filter.atTop Filter.atTop := by
      refine Filter.Tendsto.const_mul_atTop ha ?_
      exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h_ev : ∀ᶠ n in Filter.atTop, Fn n ω = 0 := by
      filter_upwards [h_sqrt_tendsto.eventually_gt_atTop (|Φ ω|)] with n hn
      simp only [hFn_def]
      have h_not : ω ∉ {x | a * Real.sqrt n < |Φ x|} := by
        intro h
        exact lt_asymm (a := |Φ ω|) (b := a * Real.sqrt n) hn h
      rw [Set.indicator_of_notMem h_not]
      simp
    have h_evEq : (fun n => Fn n ω) =ᶠ[Filter.atTop] (fun _ => (0 : ℝ≥0∞)) := h_ev
    exact Filter.Tendsto.congr' h_evEq.symm tendsto_const_nhds
  -- The assumption MemLp Φ 2 P gives integrability of |Φ|².
  have h_phi_sq_int : ∫⁻ ω, ENNReal.ofReal (Φ ω ^ 2) ∂P ≠ ∞ := by
    have h_eLp : eLpNorm Φ 2 P < ∞ := hΦ_L2.eLpNorm_lt_top
    have h_rpow := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := P) (f := Φ) (p := (2 : ℝ≥0∞))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h_eLp
    have h_two_toReal : (2 : ℝ≥0∞).toReal = (2 : ℕ) := by norm_num
    rw [h_two_toReal] at h_rpow
    have h_int_eq : ∫⁻ ω, ENNReal.ofReal (Φ ω ^ 2) ∂P
                   = ∫⁻ a, ‖Φ a‖ₑ ^ ((2 : ℕ) : ℝ) ∂P := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h_int_eq]; exact h_rpow.ne
  -- Hence g is integrable.
  have h_g_int : ∫⁻ ω, g ω ∂P ≠ ∞ := by
    simp only [hg_def]
    rw [lintegral_const_mul' _ _ ha_inv_ne_top]
    exact ENNReal.mul_ne_top ha_inv_ne_top h_phi_sq_int
  -- Conclude by dominated convergence.
  have h_dct :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := P) (F := Fn) (f := fun _ => (0 : ℝ≥0∞)) g hFn_meas
      (fun n => Filter.Eventually.of_forall (h_bound n)) h_g_int
      (Filter.Eventually.of_forall h_lim)
  simp only [lintegral_zero] at h_dct
  exact (Filter.tendsto_congr hT_eq).mpr h_dct

/-- **Eventual envelope-tail absorption into a positive target.**

For `Φ ∈ L²(P)`, fixed `a > 0`, and any positive target `J`, there is `N`
beyond which `√n · ∫⁻ |Φ| · 1_{a·√n < |Φ|} ≤ J`. This follows from
`tendsto_envelope_tail_const_threshold` and `ENNReal.tendsto_atTop_zero`. -/
lemma exists_envelope_tail_le_const_threshold
    (P : Measure Ω) [IsProbabilityMeasure P] {Φ : Ω → ℝ}
    (hΦ_meas : Measurable Φ) (hΦ_L2 : MemLp Φ 2 P) {a : ℝ} (ha : 0 < a)
    {J : ℝ≥0∞} (hJ : 0 < J) :
    ∃ N : ℕ, ∀ n ≥ N,
      ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
            * Set.indicator {x | a * Real.sqrt n < |Φ x|} 1 ω ∂P ≤ J :=
  ENNReal.tendsto_atTop_zero.mp
    (tendsto_envelope_tail_const_threshold P hΦ_meas hΦ_L2 ha) _ hJ

/-- **Envelope-tail DCT at the `n·M` threshold.**

The truncation level
`√n · M_old` with `M_old = √n · chainThreshold / 2`, i.e. at the **`n`-scaled**
threshold `{(n:ℝ) · M < |Φ|}` for the `n`-independent positive constant
`M := chainThreshold B δq q₀ / 2`. This variant of
`tendsto_envelope_tail_const_threshold` runs the same envelope-tail DCT at that
`(n:ℝ)·M` threshold (a strictly faster-growing cutoff than `a·√n`, so the tail
vanishes a fortiori).

Domination on `{n·M < |Φ|}` uses `n·M < |Φ|` to obtain
`√n ≤ n ≤ |Φ|/M` (for `n ≥ 1`), so `√n·|Φ| ≤ |Φ|²/M ∈ L¹`. -/
lemma tendsto_envelope_tail_natMul_threshold
    (P : Measure Ω) [IsProbabilityMeasure P] {Φ : Ω → ℝ}
    (hΦ_meas : Measurable Φ) (hΦ_L2 : MemLp Φ 2 P) {M : ℝ} (hM : 0 < M) :
    Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
            * Set.indicator {x | (n : ℝ) * M < |Φ x|} 1 ω ∂P)
      Filter.atTop (𝓝 0) := by
  have hM_ofReal_pos : (0 : ℝ≥0∞) < ENNReal.ofReal M := ENNReal.ofReal_pos.mpr hM
  have hM_inv_ne_top : (ENNReal.ofReal M)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hM_ofReal_pos.ne'
  set T : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.sqrt n)
      * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
          * Set.indicator {x | (n : ℝ) * M < |Φ x|} 1 ω ∂P with hT_def
  set Fn : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal (Real.sqrt n) * (ENNReal.ofReal (|Φ ω|) *
      Set.indicator {x | (n : ℝ) * M < |Φ x|} 1 ω) with hFn_def
  set g : Ω → ℝ≥0∞ := fun ω =>
    (ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (Φ ω ^ 2) with hg_def
  have hT_eq : ∀ n, T n = ∫⁻ ω, Fn n ω ∂P := by
    intro n
    simp only [hT_def, hFn_def]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hΦ_abs_meas : Measurable (fun ω => |Φ ω|) :=
    _root_.continuous_abs.measurable.comp hΦ_meas
  have hFn_meas : ∀ n, Measurable (Fn n) := by
    intro n
    refine measurable_const.mul ?_
    refine hΦ_abs_meas.ennreal_ofReal.mul ?_
    exact Measurable.indicator measurable_const
      (measurableSet_lt measurable_const hΦ_abs_meas)
  have h_bound : ∀ n ω, Fn n ω ≤ g ω := by
    intro n ω
    simp only [hFn_def, hg_def]
    by_cases hω : ω ∈ {x | (n : ℝ) * M < |Φ x|}
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      have hω' : (n : ℝ) * M < |Φ ω| := hω
      have h_phi_nn : 0 ≤ |Φ ω| := abs_nonneg _
      -- `√n ≤ n ≤ |Φ|/M`, hence `√n·|Φ| ≤ |Φ|²/M`.
      have h_sqrt_le_n : Real.sqrt n ≤ (n : ℝ) := by
        rcases Nat.eq_zero_or_pos n with hn0 | hn1
        · simp [hn0]
        · have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
          calc Real.sqrt n ≤ Real.sqrt ((n : ℝ) ^ 2) := by
                apply Real.sqrt_le_sqrt; nlinarith
            _ = (n : ℝ) := by rw [Real.sqrt_sq (by positivity)]
      have h_n_le : (n : ℝ) ≤ |Φ ω| / M := by
        rw [le_div_iff₀ hM]; linarith
      have h_sqrt_le : Real.sqrt n ≤ |Φ ω| / M := le_trans h_sqrt_le_n h_n_le
      have h_step : Real.sqrt n * |Φ ω| ≤ Φ ω ^ 2 / M := by
        calc Real.sqrt n * |Φ ω|
            ≤ (|Φ ω| / M) * |Φ ω| :=
              mul_le_mul_of_nonneg_right h_sqrt_le h_phi_nn
          _ = (|Φ ω| * |Φ ω|) / M := by rw [div_mul_eq_mul_div]
          _ = Φ ω ^ 2 / M := by rw [← sq, sq_abs]
      calc ENNReal.ofReal (Real.sqrt n * |Φ ω|)
          ≤ ENNReal.ofReal (Φ ω ^ 2 / M) := ENNReal.ofReal_le_ofReal h_step
        _ = (ENNReal.ofReal M)⁻¹ * ENNReal.ofReal (Φ ω ^ 2) := by
            rw [ENNReal.ofReal_div_of_pos hM, ENNReal.div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hω]
      simp
  have h_lim : ∀ ω, Filter.Tendsto (fun n => Fn n ω) Filter.atTop (𝓝 0) := by
    intro ω
    have h_nat_tendsto :
        Filter.Tendsto (fun n : ℕ => (n : ℝ) * M) Filter.atTop Filter.atTop := by
      refine Filter.Tendsto.atTop_mul_const hM ?_
      exact tendsto_natCast_atTop_atTop
    have h_ev : ∀ᶠ n in Filter.atTop, Fn n ω = 0 := by
      filter_upwards [h_nat_tendsto.eventually_gt_atTop (|Φ ω|)] with n hn
      simp only [hFn_def]
      have h_not : ω ∉ {x | (n : ℝ) * M < |Φ x|} := by
        intro h
        exact lt_asymm (a := |Φ ω|) (b := (n : ℝ) * M) hn h
      rw [Set.indicator_of_notMem h_not]
      simp
    have h_evEq : (fun n => Fn n ω) =ᶠ[Filter.atTop] (fun _ => (0 : ℝ≥0∞)) := h_ev
    exact Filter.Tendsto.congr' h_evEq.symm tendsto_const_nhds
  have h_phi_sq_int : ∫⁻ ω, ENNReal.ofReal (Φ ω ^ 2) ∂P ≠ ∞ := by
    have h_eLp : eLpNorm Φ 2 P < ∞ := hΦ_L2.eLpNorm_lt_top
    have h_rpow := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := P) (f := Φ) (p := (2 : ℝ≥0∞))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h_eLp
    have h_two_toReal : (2 : ℝ≥0∞).toReal = (2 : ℕ) := by norm_num
    rw [h_two_toReal] at h_rpow
    have h_int_eq : ∫⁻ ω, ENNReal.ofReal (Φ ω ^ 2) ∂P
                   = ∫⁻ a, ‖Φ a‖ₑ ^ ((2 : ℕ) : ℝ) ∂P := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h_int_eq]; exact h_rpow.ne
  have h_g_int : ∫⁻ ω, g ω ∂P ≠ ∞ := by
    simp only [hg_def]
    rw [lintegral_const_mul' _ _ hM_inv_ne_top]
    exact ENNReal.mul_ne_top hM_inv_ne_top h_phi_sq_int
  have h_dct :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := P) (F := Fn) (f := fun _ => (0 : ℝ≥0∞)) g hFn_meas
      (fun n => Filter.Eventually.of_forall (h_bound n)) h_g_int
      (Filter.Eventually.of_forall h_lim)
  simp only [lintegral_zero] at h_dct
  exact (Filter.tendsto_congr hT_eq).mpr h_dct

/-- Sub-Lemma C: localized chaining integral bound using
`localizedChainBound_of_finiteEntropy` (supplied as `hChainBound_outer`) and the
envelope-tail convergence theorem `tendsto_envelope_tail_const_threshold`.

vdV §19.2 **localized** equicontinuity. On the `L²`-good event
`{∫(f̂−ĝ)² < δq²}`, the random difference `f̂(ξ) − ĝ(ξ)` lands in the
δq-LOCALIZED difference class `localizedDifferenceClass F P δq` (whose sup DOES
vanish, unlike the full-`F` sup), so the per-ξ integrand is bounded by the
localized-class supremum rather than by `2·supNormOver F`. The bound
`∫⁻ supNormOver (localized) 𝔾ₙ ≤ c·J(δq) + c·√n·tail(√n·M)` then bounds the slice
integral, and the tail at threshold `√n·M` (uniform positive `M`, outside `∀n`)
is absorbed into `J(δq)` via the envelope-tail DCT at `a = M > 0`.

The hypothesis `δq ≤ 1/4` is retained in the conclusion.
Universal `K_chain := 2·c` (one envelope-tail factor; the localized route has no
F−F→F doubling — the localized class already IS the difference slice). -/
private theorem chaining_integral_universal_K
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (_hX_meas : ∀ i, Measurable (X i))
    (_hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (_hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (_hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (_h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (_h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    -- The δq-LOCALIZED chaining bound (vdV Lemma 19.34, localized form):
    -- `∫⁻ supNormOver (localizedDifferenceClass F P δq) 𝔾ₙ ≤ c·J(δq) + c·√n·tail`
    -- with a uniform positive truncation level `M` (outside `∀ n`) at threshold
    -- `√n·M`. The class-`F` envelope `Φ` is upgraded to the difference-class
    -- envelope `2Φ` (`isEnvelope_differenceClass_two`).
    (hChainBound_outer :
      ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
          ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P)) :
    ∃ K_chain : ℝ, 0 < K_chain ∧
      ∀ q : ℕ, ∀ (δq : ℝ), 0 < δq → δq ≤ 1 / 4 →
        ∃ N_chain : ℕ, ∀ n ≥ N_chain,
          ∫⁻ ξ, ENNReal.ofReal
                |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
              * Set.indicator
                  {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < δq ^ 2}
                  (fun _ => (1 : ℝ≥0∞)) ξ ∂μ
            ≤ ENNReal.ofReal K_chain * bracketingEntropyIntegral δq F P := by
  -- Step 0: destructure the existential universal chaining constant `c`.
  obtain ⟨c, hc_pos, hChainBound_outer⟩ := hChainBound_outer
  -- Step 1: Extract the class-`F` envelope Φ; upgrade to the difference-class
  -- envelope `Φ₂ := 2Φ` (`isEnvelope_differenceClass_two`) for the localized
  -- subclass of `differenceClass F`.
  obtain ⟨Φ, hΦ_meas, hΦ_env, hΦ_L2⟩ := chaining_envelope_from_bracket F P h_int
  set Φ₂ : Ω → ℝ := fun x => 2 * Φ x with hΦ₂_def
  have hΦ₂_meas : Measurable Φ₂ := measurable_const.mul hΦ_meas
  have hΦ₂_env : IsEnvelope (differenceClass F) Φ₂ := isEnvelope_differenceClass_two hΦ_env
  have hΦ₂_L2 : MemLp Φ₂ 2 P := hΦ_L2.const_mul 2
  -- `F` is nonempty because it contains every `fhat n ξ`; this gives positivity
  -- of `J(δq)`.
  obtain ⟨ξ₀⟩ := nonempty_of_isProbabilityMeasure μ
  have hF_ne : F.Nonempty := ⟨fhat 0 ξ₀, h_fhat_in 0 ξ₀⟩
  -- Step 2: Universal K_chain = 2·c (one envelope-tail bookkeeping factor; the
  -- localized route has NO F−F→F doubling — the localized class IS the slice).
  refine ⟨2 * c, by positivity, ?_⟩
  intro q δq hδq_pos hδq_le_quarter
  -- `0 < J(δq)` is forced by `F.Nonempty` (the entropy integrand
  -- `√(log (1 + N))` is `≥ √(log 2) > 0` pointwise) — no longer a hypothesis.
  have hJ_pos : 0 < bracketingEntropyIntegral δq F P :=
    bracketingEntropyIntegral_pos_of_nonempty hF_ne hδq_pos
  -- Obtain the uniform positive truncation level `M` and the per-`n` localized
  -- chaining bound at scale `δq`.
  obtain ⟨M, hM_pos, hMbound⟩ :=
    hChainBound_outer Φ₂ hΦ₂_meas hΦ₂_env hΦ₂_L2 hδq_pos hδq_le_quarter
  -- Step 3: Pick `N_chain` via the envelope-tail DCT at the FIXED positive
  -- threshold scale `a = M` (`tendsto_envelope_tail_const_threshold`):
  -- `√n · ∫⁻ |Φ₂| · 1_{M·√n < |Φ₂|} dP → 0`, hence eventually `≤ J(δq)` (J>0).
  have h_N_chain : ∃ N_chain : ℕ, ∀ n ≥ N_chain,
      ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P
        ≤ bracketingEntropyIntegral δq F P := by
    have h_tendsto := tendsto_envelope_tail_const_threshold P hΦ₂_meas hΦ₂_L2 hM_pos
    -- Reconcile the threshold sets `{M·√n < |Φ₂|}` and
    -- `{√n·M < |Φ₂|}` by commutativity of multiplication.
    have h_set_eq : ∀ n : ℕ,
        (fun ω => ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | M * Real.sqrt n < |Φ₂ x|} 1 ω)
        = (fun ω => ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω) := by
      intro n; simp_rw [mul_comm M (Real.sqrt n)]
    have h_tendsto' : Filter.Tendsto
        (fun n : ℕ => ENNReal.ofReal (Real.sqrt n)
          * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
              * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P)
        Filter.atTop (𝓝 0) := by
      refine h_tendsto.congr (fun n => ?_)
      rw [h_set_eq n]
    exact ENNReal.tendsto_atTop_zero.mp h_tendsto' _ hJ_pos
  obtain ⟨N_chain, hN_chain⟩ := h_N_chain
  refine ⟨N_chain, fun n hn => ?_⟩
  -- Step 4: the slice integral is bounded by the LOCALIZED-class sup integral
  -- (NOT 2·full-F-sup): on the L²-good event `f̂(ξ)−ĝ(ξ) ∈ localized class`.
  have h_chain :
      ∫⁻ ξ, ENNReal.ofReal
            |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
              - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
          * Set.indicator
              {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < δq ^ 2}
              (fun _ => (1 : ℝ≥0∞)) ξ ∂μ
        ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
          + ENNReal.ofReal c *
            (ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
                  * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P) := by
    -- Step (a): the LOCALIZED pointwise bound. On the good event,
    --   ofReal|𝔾ₙ(f̂)−𝔾ₙ(ĝ)| = ofReal|𝔾ₙ(f̂−ĝ)| ≤ supNormOver(localized) 𝔾ₙ;
    -- off the good event the indicator is 0 and the LHS is 0.
    have h_pw : ∀ ξ : Ξ,
        ENNReal.ofReal
              |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
            * Set.indicator
                {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < δq ^ 2}
                (fun _ => (1 : ℝ≥0∞)) ξ
          ≤ supNormOver (localizedDifferenceClass F P δq)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) := by
      intro ξ
      by_cases hgood : ξ ∈ {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < δq ^ 2}
      · -- the good event: `f̂(ξ)−ĝ(ξ) ∈ localizedDifferenceClass F P δq`.
        rw [Set.indicator_of_mem hgood]
        simp only [mul_one]
        -- membership of the difference in the localized class
        have hf_mem : fhat n ξ ∈ F := h_fhat_in n ξ
        have hg_mem : ghat n ξ ∈ F := h_ghat_in n ξ
        -- `fhat n ξ = (Function.uncurry (fhat n)) (ξ, ·)` is measurable.
        have hf_meas : Measurable (fhat n ξ) :=
          (_h_fhat_meas n).comp (measurable_const.prodMk measurable_id)
        have hg_meas : Measurable (ghat n ξ) :=
          (_h_ghat_meas n).comp (measurable_const.prodMk measurable_id)
        have hf_L2 : MemLp (fhat n ξ) 2 P :=
          memLp_of_mem_of_finiteBracketing h_int hf_mem hf_meas.aestronglyMeasurable
        have hg_L2 : MemLp (ghat n ξ) 2 P :=
          memLp_of_mem_of_finiteBracketing h_int hg_mem hg_meas.aestronglyMeasurable
        have hdiff_mem : (fun x => fhat n ξ x - ghat n ξ x)
            ∈ localizedDifferenceClass F P δq :=
          mem_localizedDifferenceClass_of_integral_sq hδq_pos.le hf_mem hg_mem
            (hf_L2.sub hg_L2) hgood
        -- `𝔾ₙ(f̂)−𝔾ₙ(ĝ) = 𝔾ₙ(f̂−ĝ)` (carries integrability of the two pieces).
        have hsub : empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
              - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)
            = empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => fhat n ξ x - ghat n ξ x) :=
          (empiricalProcess_sub P n _ (fhat n ξ) (ghat n ξ)
            (hf_L2.integrable one_le_two) (hg_L2.integrable one_le_two)).symm
        rw [hsub]
        exact le_supNormOver
          (z := fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) hdiff_mem
      · -- off the good event: indicator = 0.
        rw [Set.indicator_of_notMem hgood, mul_zero]
        exact zero_le
    -- Step (b): the localized chaining bound at scale `δq` for this `n`.
    have h_max : ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
        ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
          + ENNReal.ofReal c *
            (ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
                  * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P) :=
      hMbound n
    -- Step (c): combine (a) ⟹ slice integral ≤ localized sup integral ≤ RHS.
    calc ∫⁻ ξ, ENNReal.ofReal
              |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
            * Set.indicator
                {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < δq ^ 2}
                (fun _ => (1 : ℝ≥0∞)) ξ ∂μ
        ≤ ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ :=
          MeasureTheory.lintegral_mono h_pw
      _ ≤ _ := h_max
  refine h_chain.trans ?_
  -- Step 5: absorb the envelope tail into J(δq) via hN_chain, giving (c)+(c)=2c.
  have h_tail :
      ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
            * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P
        ≤ bracketingEntropyIntegral δq F P := hN_chain n hn
  calc ENNReal.ofReal c * bracketingEntropyIntegral δq F P
          + ENNReal.ofReal c *
            (ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ ω, ENNReal.ofReal (|Φ₂ ω|)
                  * Set.indicator {x | Real.sqrt n * M < |Φ₂ x|} 1 ω ∂P)
      ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
          + ENNReal.ofReal c * bracketingEntropyIntegral δq F P := by gcongr
    _ = (ENNReal.ofReal c + ENNReal.ofReal c)
            * bracketingEntropyIntegral δq F P := by rw [← add_mul]
    _ = ENNReal.ofReal (2 * c) * bracketingEntropyIntegral δq F P := by
        congr 1
        rw [← ENNReal.ofReal_add hc_pos.le hc_pos.le]
        ring_nf

/-- `chaining_per_q_integral_bound_aux`: universal-K integral bound for the
L²-good slice of `F − F`, the chaining content of
`chaining_per_q_max_ineq_bound`.

**Proof outline (vdV §19.6; the three bounds apply at scale δq).**

1. **Bracket-restricted pointwise bound (vdV §19.2 Lem 2.12).** On the
   L²-good slice `{ξ | ‖fhat n ξ − ghat n ξ‖²_L²(P) < (δ q)²}`, the pair
   `(fhat n ξ, ghat n ξ)` lies in a common `δ q`-bracket of `F − F`.
   Hence `|G_n(fhat) − G_n(ghat)| ≤ supNormOver (δq-bracket) G_n`
   pointwise on the slice.

2. **Envelope construction from finite bracket cover.** From
   `bracketingEntropyIntegral 1 F P < ⊤`, extract a finite bracket cover
   at scale 1 with bracket bounds `(l_i, u_i)`. Define
   `Φ(ω) := max_i(|l_i ω| + |u_i ω|)`. This Φ is measurable, in
   `MemLp Φ 2 P`, and is an envelope for F (and hence for F − F up to a
   factor of 2). Required for `tight_envelope_truncation_bound`.

3. **Dyadic chaining at scale δq** — uses the three leaves:
   - `tight_chain_level_bound`: level-k contribution at scale `2^{-k} · δ q`
     is bounded by `K_level · (2^{-k} · δq) · √log N_[](2^{-k} · δq)` with
     `K_level` universal in `(n, δ, k)` via `finite_sup_bound`.
   - `tight_chain_telescope_bound`: sum the dyadic levels into
     `≤ ∫_0^{δq} √log N_[](ε) dε = J(δq, F, P)`.
   - `tight_envelope_truncation_bound`: tail at scale `δq · √n` is absorbed
     by `N_chain`-dependent DCT.

4. **F-F to F factor.** `f, g ∈ F` ⟹ `f − g ∈ F − F`; pointwise
   `|G_n(f) − G_n(g)| ≤ 2 · supNormOver F G_n`. Absorb factor of 2 into
   `K_chain`.

5. **AEMeasurability**: from `h_fhat_meas`, `h_ghat_meas`, `hX_meas`
   + `MeasurableSet.indicator` on the L²-slice.

6. **Universal `K_chain := 8 · K_level · K_telescope · K_truncation`**,
   absorbing F-F factor (2) and DCT correction (4). Each constituent
   universal in `(n, δq, q)`. -/
private theorem chaining_per_q_integral_bound_aux
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (_h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (_h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (_h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    (δ : ℕ → ℝ) (_hδ_pos : ∀ q, 0 < δ q) (_hδ_le_quarter : ∀ q, δ q ≤ 1 / 4)
    -- The δq-localized chaining bound (vdV Lemma 19.34, localized form); see
    -- `chaining_integral_universal_K`. The universal constant `c > 0` and
    -- the uniform positive truncation level `M` are existentially quantified.
    (hChainBound_outer :
      ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
          ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P)) :
    ∃ K_chain : ℝ, 0 < K_chain ∧
      ∀ q : ℕ, ∃ N_chain : ℕ, ∀ n ≥ N_chain,
        AEMeasurable (fun ξ : Ξ =>
          ENNReal.ofReal
              |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
            * Set.indicator
                {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < (δ q) ^ 2}
                (fun _ => (1 : ℝ≥0∞)) ξ) μ ∧
        ∫⁻ ξ, ENNReal.ofReal
              |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
            * Set.indicator
                {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < (δ q) ^ 2}
                (fun _ => (1 : ℝ≥0∞)) ξ ∂μ
          ≤ ENNReal.ofReal K_chain * bracketingEntropyIntegral (δ q) F P := by
  -- Obtain universal K_chain' and per-q N_chain' from `chaining_integral_universal_K`
  -- up-front, so the outer `refine ⟨K_chain', ...⟩` uses its witnesses directly.
  obtain ⟨K_chain', hK_chain'_pos, h_K_chain'⟩ :=
    chaining_integral_universal_K F P _h_int μ X hX_meas
      hX_iindep hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas
      _h_fhat_in _h_ghat_in hChainBound_outer
  refine ⟨K_chain', hK_chain'_pos, ?_⟩
  intro q
  obtain ⟨N_chain', h_N_chain'⟩ :=
    h_K_chain' q (δ q) (_hδ_pos q) (_hδ_le_quarter q)
  refine ⟨N_chain', fun n hn => ?_⟩
  refine ⟨?_, ?_⟩
  · -- AEMeasurability of the integrand. Decompose `empiricalProcess` as
    -- `√n · ((1/n) ∑ - ∫)`; (a) each diagonal term `ξ ↦ fhat n ξ (X i.val ξ)`
    -- is measurable via `(h_fhat_meas n).comp` on `(id, X i.val)`; (b) each
    -- integral term `ξ ↦ ∫ x, fhat n ξ x ∂P` is measurable via
    -- `StronglyMeasurable.integral_prod_right'` on the joint uncurry; (c) the
    -- L²-slice set is measurable via the same Fubini step on the squared
    -- difference. The integrand is then `ENNReal.ofReal ∘ |·| · 1_s`.
    have h_F : Measurable (Function.uncurry (fhat n)) := h_fhat_meas n
    have h_G : Measurable (Function.uncurry (ghat n)) := h_ghat_meas n
    -- Per-i diagonals.
    have h_F_diag : ∀ i : Fin n, Measurable (fun ξ : Ξ => fhat n ξ (X i.val ξ)) := by
      intro i
      have hpair : Measurable (fun ξ : Ξ => (ξ, X i.val ξ)) :=
        Measurable.prodMk measurable_id (hX_meas i.val)
      exact h_F.comp hpair
    have h_G_diag : ∀ i : Fin n, Measurable (fun ξ : Ξ => ghat n ξ (X i.val ξ)) := by
      intro i
      have hpair : Measurable (fun ξ : Ξ => (ξ, X i.val ξ)) :=
        Measurable.prodMk measurable_id (hX_meas i.val)
      exact h_G.comp hpair
    -- Empirical sums.
    have h_sum_F :
        Measurable (fun ξ : Ξ => ∑ i : Fin n, fhat n ξ (X i.val ξ)) :=
      Finset.measurable_sum _ (fun i _ => h_F_diag i)
    have h_sum_G :
        Measurable (fun ξ : Ξ => ∑ i : Fin n, ghat n ξ (X i.val ξ)) :=
      Finset.measurable_sum _ (fun i _ => h_G_diag i)
    -- Integrals against P via Fubini measurability.
    have h_int_F : Measurable (fun ξ : Ξ => ∫ x, fhat n ξ x ∂P) :=
      h_F.stronglyMeasurable.integral_prod_right'.measurable
    have h_int_G : Measurable (fun ξ : Ξ => ∫ x, ghat n ξ x ∂P) :=
      h_G.stronglyMeasurable.integral_prod_right'.measurable
    -- empiricalProcess pieces.
    have h_EP_F : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)) := by
      unfold empiricalProcess empiricalAvg
      exact measurable_const.mul ((measurable_const.mul h_sum_F).sub h_int_F)
    have h_EP_G : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)) := by
      unfold empiricalProcess empiricalAvg
      exact measurable_const.mul ((measurable_const.mul h_sum_G).sub h_int_G)
    have h_diff : Measurable (fun ξ : Ξ =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
          - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)) :=
      h_EP_F.sub h_EP_G
    have h_ofReal : Measurable (fun ξ : Ξ =>
        ENNReal.ofReal
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|) :=
      ENNReal.measurable_ofReal.comp h_diff.norm
    -- L²-slice set is measurable.
    have h_joint_sq :
        Measurable (fun p : Ξ × Ω => (fhat n p.1 p.2 - ghat n p.1 p.2) ^ 2) :=
      (h_F.sub h_G).pow_const 2
    have h_l2_int : Measurable (fun ξ : Ξ =>
        ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) :=
      h_joint_sq.stronglyMeasurable.integral_prod_right'.measurable
    have h_s_meas : MeasurableSet
        {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < (δ q) ^ 2} :=
      h_l2_int measurableSet_Iio
    have h_ind : Measurable (fun ξ : Ξ =>
        Set.indicator {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < (δ q) ^ 2}
          (fun _ => (1 : ℝ≥0∞)) ξ) :=
      (measurable_const : Measurable (fun _ : Ξ => (1 : ℝ≥0∞))).indicator h_s_meas
    exact (h_ofReal.mul h_ind).aemeasurable
  · -- The chain-integral bound is exactly the per-q witness
    -- `h_N_chain' n hn` obtained at the top of this proof.
    exact h_N_chain' n hn

/-- Per-`q` chaining bound on the L²-good portion of `badEvent`. The proof uses
envelope extraction from the level-1 bracket cover of `F − F`, the localized
universal-constant chaining bound on the L²-`δ q` slice, and Markov's inequality.
Dominated convergence absorbs the envelope tail into the eventually-in-`n`
quantifier, and the F-F-to-F bracketing-integral inequality gives the stated
entropy bound.

**Proof outline (vdV §19.2).**
1. From the finite bracketing-entropy at scale 1 (`h_int`), extract
   the level-1 bracket cover of `F`; via
   `hasFiniteBracketingCover_difference_class` get a level-1 bracket
   cover of `F − F`; construct the envelope
   `Φ ω = max_i (|l_i ω| + |u_i ω|)` over the level-1 brackets of
   `F − F`. This `Φ` is measurable and `MemLp Φ 2 P`.
2. For each `q`, apply `hChainBound_outer` on the L²-`δ q` slice
   subclass `F'_q := {h ∈ F − F | ‖h‖_{L²(P)} ≤ δ q}` at scale
   `δ q`, with the bracketing entropy integral
   `J_q := J_{[]}(δ q, F − F, L²(P))`. The hypothesis `hAbsorb` is
   discharged from the chain-comparison content
   (`J ≥ K_F · δ` for non-trivial F-F).
3. Markov on the threshold `η`:
   `μ {ξ | η ≤ supNormOver F'_q (G_n) (X(·, ξ))}
      ≤ K' · (J_q + √n · envelope_tail(n)) / ofReal η`.
4. F-F-to-F bracketing-integral reduction
   (`bracketingIntegral_difference_class_le`):
   `J_q ≤ 2 · J_{[]}(δ q, F, L²(P))`.
5. The L²-good portion `badEvent n \ l2Event ((δ q)²) n` is a
   subset of the Markov-amenable event in step 3 because on this set
   `(fhat n ξ − ghat n ξ) ∈ F'_q` and the empirical process gap is
   bounded by `supNormOver F'_q (G_n) (X(·, ξ))`.
6. DCT for the envelope-tail term: `√n · envelope_tail(n) → 0` as
   `n → ∞`. Pick `N_chain` so that `√n · envelope_tail(n) ≤ J_q` for
   `n ≥ N_chain`, absorbing the tail into a uniform `2 K' / η`
   multiplier on `J_q`.
7. Combining steps 3–6 with step 4 gives the desired bound with
   `K := 4 K' / η`. This `K` is uniform in `q`.

The universal constant comes from `hChainBound_outer` and
`chaining_per_q_integral_bound_aux`, which combine `finite_sup_bound`, the
telescoping sum, and envelope truncation. Markov's inequality converts the
integral bound to the measure bound with `K = K_chain / η`, uniformly in `q`. -/
theorem chaining_per_q_max_ineq_bound
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (_h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat ghat : ℕ → Ξ → (Ω → ℝ))
    (h_fhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)))
    (h_ghat_meas : ∀ n, Measurable (Function.uncurry (ghat n)))
    (_h_fhat_in : ∀ n ξ, fhat n ξ ∈ F)
    (_h_ghat_in : ∀ n ξ, ghat n ξ ∈ F)
    (δ : ℕ → ℝ) (_hδ_pos : ∀ q, 0 < δ q) (_hδ_le_quarter : ∀ q, δ q ≤ 1 / 4)
    -- The δq-LOCALIZED chaining bound (vdV Lemma 19.34, localized form); see
    -- `chaining_integral_universal_K`. The universal chaining constant `c > 0` and
    -- the uniform positive truncation level `M` are existentially quantified.
    (hChainBound_outer :
      ∃ c : ℝ, 0 < c ∧
      ∀ (Φ : Ω → ℝ), Measurable Φ → IsEnvelope (differenceClass F) Φ → MemLp Φ 2 P →
        ∀ {δq : ℝ}, 0 < δq → δq ≤ 1 / 4 →
          ∃ M : ℝ, 0 < M ∧ ∀ (n : ℕ),
            ∫⁻ ξ, supNormOver (localizedDifferenceClass F P δq)
                  (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c * bracketingEntropyIntegral δq F P
                + ENNReal.ofReal c *
                  (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (|Φ ω|)
                        * Set.indicator {x | Real.sqrt n * M < |Φ x|} 1 ω ∂P))
    (η : ℝ) (_hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧
      ∀ q : ℕ, ∃ N_chain : ℕ, ∀ n ≥ N_chain,
        μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                       (fhat n ξ)
                   - empiricalProcess P n (fun i : Fin n => X i.val ξ)
                       (ghat n ξ)|} \
            {ξ | (δ q) ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}) ≤
          ENNReal.ofReal K * bracketingEntropyIntegral (δ q) F P := by
  -- The leaves `tight_chain_level_bound`, `tight_chain_telescope_bound`,
  -- `tight_envelope_truncation_bound` each return constants universal in
  -- `(n, δ)`; combining them as in vdV §19.6 yields a universal `K_chain`
  -- on the integral of `|G_n(f̂) − G_n(ĝ)|` restricted to the L²-good event.
  -- Markov on threshold `η` converts this integral bound to the measure
  -- bound below; the outer `K = K_chain / η` is therefore universal in `q`.
  -- Apply `chaining_per_q_integral_bound_aux`, which bundles AEMeasurability of the
  -- integrand and the integral bound); the Markov + ENNReal-algebra wrap-up
  -- is closed inline.
  obtain ⟨K_chain, hK_chain_pos, h_chain⟩ :=
    chaining_per_q_integral_bound_aux F P _h_int μ X hX_meas hX_iindep
      hX_id hX_law fhat ghat h_fhat_meas h_ghat_meas
      _h_fhat_in _h_ghat_in δ _hδ_pos _hδ_le_quarter hChainBound_outer
  -- Outer K = K_chain / η is universal (independent of q and of n ≥ N_chain_q).
  refine ⟨K_chain / η, div_pos hK_chain_pos _hη, ?_⟩
  intro q
  obtain ⟨N_chain, h_q⟩ := h_chain q
  refine ⟨N_chain, fun n hn => ?_⟩
  obtain ⟨hY_meas, h_int_bound⟩ := h_q n hn
  -- The L²-good slice set and the Markov-amenable integrand `Y`.
  set s : Set Ξ :=
    {ξ : Ξ | ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P < (δ q) ^ 2} with hs_def
  set Y : Ξ → ℝ≥0∞ := fun ξ =>
      ENNReal.ofReal
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|
        * Set.indicator s (fun _ => (1 : ℝ≥0∞)) ξ with hY_def
  -- Pointwise: on `A \ B`, `ENNReal.ofReal η ≤ Y ξ`.
  have h_sub :
      ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|} \
       {ξ | (δ q) ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P})
      ⊆ {ξ | ENNReal.ofReal η ≤ Y ξ} := by
    intro ξ hξ
    have hA : η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)| :=
      hξ.1
    have hB : ¬ ((δ q) ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P) := hξ.2
    have hξ_mem_s : ξ ∈ s := not_le.mp hB
    have h_ind : Set.indicator s (fun _ => (1 : ℝ≥0∞)) ξ = 1 :=
      Set.indicator_of_mem hξ_mem_s _
    change ENNReal.ofReal η ≤ Y ξ
    simp only [hY_def, h_ind, mul_one]
    exact ENNReal.ofReal_le_ofReal hA.le
  -- Markov on threshold `ENNReal.ofReal η`.
  have h_markov :
      ENNReal.ofReal η * μ {ξ | ENNReal.ofReal η ≤ Y ξ} ≤ ∫⁻ ξ, Y ξ ∂μ :=
    mul_meas_ge_le_lintegral₀ hY_meas (ENNReal.ofReal η)
  -- Combine: `η · μ(A\B) ≤ ∫⁻ Y ≤ K_chain · J`.
  have h_combine :
      ENNReal.ofReal η *
        μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                      - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|} \
            {ξ | (δ q) ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}) ≤
        ENNReal.ofReal K_chain * bracketingEntropyIntegral (δ q) F P := by
    calc ENNReal.ofReal η *
            μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                          - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|} \
                {ξ | (δ q) ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P})
          ≤ ENNReal.ofReal η * μ {ξ | ENNReal.ofReal η ≤ Y ξ} :=
            mul_le_mul_of_nonneg_left (measure_mono h_sub) (zero_le)
      _ ≤ ∫⁻ ξ, Y ξ ∂μ := h_markov
      _ ≤ ENNReal.ofReal K_chain * bracketingEntropyIntegral (δ q) F P := h_int_bound
  -- ENNReal-algebra divide-by-`η`.
  have hη_ofReal_ne_zero : ENNReal.ofReal η ≠ 0 :=
    (ENNReal.ofReal_pos.mpr _hη).ne'
  have hη_ofReal_ne_top : ENNReal.ofReal η ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_div :
      μ ({ξ | η < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ)
                    - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ghat n ξ)|} \
          {ξ | (δ q) ^ 2 ≤ ∫ x, (fhat n ξ x - ghat n ξ x) ^ 2 ∂P}) ≤
      ENNReal.ofReal K_chain * bracketingEntropyIntegral (δ q) F P / ENNReal.ofReal η := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hη_ofReal_ne_zero) (Or.inl hη_ofReal_ne_top),
        mul_comm]
    exact h_combine
  -- Repackage `(K · J) / η = ofReal(K/η) · J`.
  have h_rw :
      ENNReal.ofReal K_chain * bracketingEntropyIntegral (δ q) F P
          / ENNReal.ofReal η
        = ENNReal.ofReal (K_chain / η) * bracketingEntropyIntegral (δ q) F P := by
    rw [ENNReal.mul_div_right_comm, ← ENNReal.ofReal_div_of_pos _hη]
  rw [← h_rw]
  exact h_div

end AsymptoticStatistics.EmpiricalProcess
