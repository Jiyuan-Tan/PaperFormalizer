module
public import StatLean.TimeSeries.Mixing.Defs
public import StatLean.TimeSeries.Mixing.Relations
public import StatLean.TimeSeries.Process.Stationary
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

/-!
# Covariance and moment inequalities under mixing (FY §2.6.2, pp. 71–73)

The quantitative toolbox for α-mixing processes:

* **Proposition 2.5(ii) (Billingsley)**: bounded case, `|Cov(f, g)| ≤ 4 α C₁ C₂`, plus
  the complex version with constant `16` — the workhorse of Proposition 2.6;
* **Proposition 2.5(i) (Davydov)**: `1/p + 1/q < 1` ⇒
  `|Cov(f, g)| ≤ 8 α^{1 − 1/p − 1/q} ‖f‖_p ‖g‖_q` — **built here in full** (FY cites
  Doukhan §1.2.2; truncation of both factors against the bounded case);
* **Proposition 2.6 (Volkonskii–Rozanov)**: complex unit-bounded blocks with α-gaps,
  `|E ∏ ξ_l − ∏ E ξ_l| ≤ 16 (k − 1) a` — the factorization engine of both CLT proofs
  (Theorems 2.21(ii) and 2.22).  Proved for every `k ≥ 1`; **FALSE as frozen at `k = 0`**,
  where the bound reads `0 ≤ −16a` (see the declaration);
* the **fourth-moment bound** (the `q = 4` instance of FY Proposition 2.7(ii) that the
  Bernstein-block CLT consumes): bounded, zero-mean, strictly stationary,
  `α(n) ≤ K n⁻²` ⇒ `E S_n⁴ ≤ C n²`.  **Proved in full.**  Its *probabilistic* half is the
  sorted 4-tuple mixing bound `abs_integral_quad_le`, the expansion of `E S_n⁴` over
  4-tuples, and the assembly; its *counting* half `sum_four_le_of_cut_bound` — a purely
  combinatorial statement (no probability) — is proved by `Tuple.sort` symmetrisation
  (fibres of size `4!`) plus gap parametrisation, see its docstring;
* **Theorems 2.18/2.19 (Bosq exponential inequalities)** — literature DEBTS (used only
  by ch. 5 KDE uniform rates, outside the current scope). **Removed**; see below.

**Removed (2026-08-10, user directive).** The module's two sorried declarations were
deleted. Nothing consumed them, and no helper was left orphaned — every other declaration
in the file, including the whole Volkonskii–Rozanov decoupling toolbox and the `q = 4`
Doukhan–Louhichi moment bound, is untouched and remains proved.
* `bosq_exponential_debt` — Bosq 1998 Thm 1.3 / FY Theorem 2.18: for a bounded, zero-mean,
  strictly stationary process and `1 ≤ qb ≤ n/2`,
  `P(|S_n/n| > ε) ≤ 4 exp(−ε² qb/(8 b²)) + 22 (1 + 4b/ε)^{1/2} qb α([n/(2 qb)])`.
* `bosq_cramer_debt` — Bosq 1998 Thm 1.4 / FY Theorem 2.19, eq. (2.62): the same under
  Cramér's condition `E|X_t|^k ≤ C^{k−2} k! E X_t²`, with `μ(ε) = ε²/(25 E X_t² + 5Cε)`.

Both had been brick-decomposed in wave `ts/s10` — 2.18 proved in the regimes `b ≤ ε` (null
event) and "printed bound `≥ 1`", 2.19 in its vacuous regime — leaving in each case the
single residue **Bradley's coupling lemma** (1983), whose constants are exactly the printed
`22 (1+4b/ε)^{1/2}` and `11 (…) α^{2k/(2k+1)}`. The finding that this file's
Volkonskii–Rozanov decoupling **cannot** substitute for it (its error is proportional to the
*product of the sup norms* of the factors, which for `e^{λ S_i}` is exponentially large in
the block count at every `λ` reaching the printed exponent) went with the two docstrings.

Recover from `bdc8143f`.

**Scope note.** FY's Theorem 2.17 (Doukhan–Louhichi moment bounds via the
covariance-decay functional `M_{r,q}`) and the general-`q` Proposition 2.7 are *not*
stated: their only consumers in scope — Theorems 2.20(i)/2.21(i) — are themselves
cited-out literature debts carrying their own hypotheses, and the CLT proofs consume
only the `q = 4` instance stated here.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.2,
Propositions 2.5–2.7 and Theorems 2.17–2.19 (pp. 71–73). (`FY §2.6.2`.)

**Proof formalization notes.**
* Billingsley: with `η = sgn(E[f g | split])`-free classical argument: write the
  covariance against centered factors and pass to the four-event correlation via
  `f = ∫ (1_{f > t} − 1_{f < −t}) dt`-free discretization — the standard route is
  by the identity `Cov(f, g) = ∫∫ [P(f > s, g > t) − P(f > s)P(g > t)] ds dt`
  (Hoeffding), each integrand bounded by `α`; totals `4 α C₁ C₂` after splitting signs.
* Davydov: truncate at levels `C₁, C₂`, apply the bounded case to the truncations and
  Hölder/Markov to the tails; optimize the levels (`C_i = ‖·‖ · α^{-1/(...)}`) to get
  the exponent `1 − 1/p − 1/q` and constant `8`.
* Volkonskii–Rozanov: induction on `k`; each step peels the last factor with the
  complex bounded inequality (constant 16) against the cumulative-past σ-algebra.
* Fourth moment: expand `E S⁴` over index 4-tuples, split each expectation at the
  largest gap `g` (Billingsley pairs), count tuples with largest gap `g` as `O(n g²)`;
  `Σ_g n g² · g⁻² = O(n²)`, and the paired products contribute `(n Σ α)² = O(n²)`.
  As executed, the split is `abs_integral_quad_le` (proved: the two outer cuts kill the
  product term because `E X_t = 0`, the middle cut pays `E[X_aX_b]·E[X_cX_d]`), and the
  counting is isolated as `sum_four_le_of_cut_bound`.  The expensive unformalised step
  there is the symmetrisation `Σ_{(a,b,c,d)} G ≤ 24 Σ_{a≤b≤c≤d} G`, which needs an
  explicit sorting network on `ℕ⁴` or `Tuple.sort` with a fibre count.

**Bibliographic comments.** Prop 2.5(i) is Yu. A. Davydov (1968); (ii) is
P. Billingsley, *Convergence of Probability Measures* (1968), Lemma 1 of §20;
Prop 2.6 is Volkonskii & Rozanov (1959, Lemma 4.3 in Bradley's numbering). The
exponential inequalities are D. Bosq, *Nonparametric Statistics for Stochastic
Processes* (1998), Thms 1.3–1.4. Hoeffding's covariance identity is from Hoeffding
(1940); its use here follows Doukhan (1994) §1.2.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

/-! ### Proposition 2.5(ii): the bounded (Billingsley) covariance inequality

Two-σ-algebra statements follow the Mathlib `condExp` binder convention (ambient `mΩ`
as a plain implicit bound after the sub-σ-algebras, before `μ`) — see
`Mixing/Relations.lean`. -/

section TwoAlgebras

variable {Ω : Type*}

/-- Every element of the α description set is dominated by `α` itself: the description set
is bounded above by `1` on a probability space, so `le_csSup` applies. -/
private lemma le_alphaMixCoeff_of_measurableSet {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet[m₁] A)
    (hB : MeasurableSet[m₂] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ alphaMixCoeff μ m₁ m₂ := by
  refine le_csSup ⟨1, ?_⟩ ⟨A, B, hA, hB, rfl⟩
  rintro r ⟨A', B', -, -, rfl⟩
  have h1 : (μ (A' ∩ B')).toReal ≤ 1 := measureReal_le_one
  have h2 : (μ A').toReal ≤ 1 := measureReal_le_one
  have h3 : (μ B').toReal ≤ 1 := measureReal_le_one
  have h4 : (0:ℝ) ≤ (μ (A' ∩ B')).toReal := ENNReal.toReal_nonneg
  have h5 : (0:ℝ) ≤ (μ A').toReal := ENNReal.toReal_nonneg
  have h6 : (0:ℝ) ≤ (μ B').toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  refine ⟨by nlinarith, by nlinarith⟩

/-- The peeling step behind Billingsley's inequality: if the `m`-set discrepancies of `ψ`
are bounded by `K`, then `ψ` decorrelates from every `m`-measurable `φ` bounded by `C`,
with constant `2 C K`.

Proof: `∫ φ ψ = ∫ φ · E[ψ | m]` (pull-out property), so the left-hand side is
`∫ φ · W` with `W = E[ψ | m] − E ψ`; then `|∫ φ W| ≤ C ∫ |W|` and, splitting `Ω` at the
`m`-measurable sign event of `W`, `∫ |W| = ∫_A W − ∫_{Aᶜ} W ≤ 2 K` by hypothesis. -/
private lemma abs_integral_mul_sub_le_of_setIntegral_bound
    {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {φ ψ : Ω → ℝ} {C K : ℝ}
    (hφ : StronglyMeasurable[m] φ) (hφC : ∀ᵐ ω ∂μ, |φ ω| ≤ C)
    (hψ : Integrable ψ μ)
    (hK : ∀ A : Set Ω, MeasurableSet[m] A →
      |(∫ ω in A, ψ ω ∂μ) - (∫ ω, ψ ω ∂μ) * (μ A).toReal| ≤ K) :
    |(∫ ω, φ ω * ψ ω ∂μ) - (∫ ω, φ ω ∂μ) * ∫ ω, ψ ω ∂μ| ≤ 2 * C * K := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) hφC.exists.choose_spec
  have hφn : ∀ᵐ ω ∂μ, ‖φ ω‖ ≤ C := by simpa [Real.norm_eq_abs] using hφC
  have hφ' : StronglyMeasurable φ := hφ.mono hm
  have hφint : Integrable φ μ :=
    (memLp_top_of_bound hφ'.aestronglyMeasurable C hφn).integrable le_top
  set c : ℝ := ∫ ω, ψ ω ∂μ with hcdef
  set W : Ω → ℝ := fun ω => (μ[ψ|m]) ω - c with hWdef
  have hWm : StronglyMeasurable[m] W := stronglyMeasurable_condExp.sub stronglyMeasurable_const
  have hWint : Integrable W μ := integrable_condExp.sub (integrable_const c)
  have hpull : ∫ ω, φ ω * ψ ω ∂μ = ∫ ω, φ ω * (μ[ψ|m]) ω ∂μ := by
    have h1 : μ[φ * ψ|m] =ᵐ[μ] φ * μ[ψ|m] :=
      condExp_stronglyMeasurable_mul_of_bound hm hφ hψ C hφn
    calc ∫ ω, φ ω * ψ ω ∂μ = ∫ ω, (μ[φ * ψ|m]) ω ∂μ := (integral_condExp hm).symm
      _ = ∫ ω, (φ * μ[ψ|m]) ω ∂μ := integral_congr_ae h1
      _ = ∫ ω, φ ω * (μ[ψ|m]) ω ∂μ := rfl
  have hkey : (∫ ω, φ ω * ψ ω ∂μ) - (∫ ω, φ ω ∂μ) * c = ∫ ω, φ ω * W ω ∂μ := by
    rw [hpull]
    have h : ∀ ω, φ ω * W ω = φ ω * (μ[ψ|m]) ω - φ ω * c := by intro ω; ring
    simp_rw [h]
    rw [integral_sub (integrable_condExp.bdd_mul hφ'.aestronglyMeasurable hφn)
      (hφint.mul_const c), integral_mul_const]
  have hsetW : ∀ A : Set Ω, MeasurableSet[m] A →
      ∫ ω in A, W ω ∂μ = (∫ ω in A, ψ ω ∂μ) - c * (μ A).toReal := by
    intro A hA
    rw [hWdef]
    rw [integral_sub (integrable_condExp.restrict) (integrable_const c),
      setIntegral_condExp hm hψ hA, setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  set A : Set Ω := {ω | 0 ≤ W ω} with hAdef
  have hA : MeasurableSet[m] A := hWm.measurable measurableSet_Ici
  have hsplit : ∫ ω, |W ω| ∂μ = (∫ ω in A, W ω ∂μ) - ∫ ω in Aᶜ, W ω ∂μ := by
    have h1 : ∫ ω in A, |W ω| ∂μ = ∫ ω in A, W ω ∂μ :=
      setIntegral_congr_fun (hm A hA) fun x hx => abs_of_nonneg hx
    have h2 : ∫ ω in Aᶜ, |W ω| ∂μ = -∫ ω in Aᶜ, W ω ∂μ := by
      rw [← integral_neg]
      exact setIntegral_congr_fun (hm A hA).compl fun x hx => abs_of_neg (not_le.mp hx)
    rw [← integral_add_compl (hm A hA) hWint.abs, h1, h2]
    ring
  have hbd1 : |∫ ω in A, W ω ∂μ| ≤ K := by rw [hsetW A hA]; exact hK A hA
  have hbd2 : |∫ ω in Aᶜ, W ω ∂μ| ≤ K := by rw [hsetW _ hA.compl]; exact hK _ hA.compl
  have hW2K : ∫ ω, |W ω| ∂μ ≤ 2 * K := by
    rw [hsplit]
    linarith [(abs_le.mp hbd1).2, (abs_le.mp hbd2).1]
  rw [hkey]
  calc |∫ ω, φ ω * W ω ∂μ| ≤ ∫ ω, |φ ω * W ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, C * |W ω| ∂μ := by
        refine integral_mono_ae ((hWint.bdd_mul hφ'.aestronglyMeasurable hφn).abs)
          (hWint.abs.const_mul C) ?_
        filter_upwards [hφC] with ω hω
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hω (abs_nonneg _)
    _ = C * ∫ ω, |W ω| ∂μ := integral_const_mul _ _
    _ ≤ C * (2 * K) := mul_le_mul_of_nonneg_left hW2K hC
    _ = 2 * C * K := by ring

/-- **FY Proposition 2.5(ii) (Billingsley)**: `m₁`/`m₂`-measurable bounded factors have
covariance at most `4 α C₁ C₂`. -/
theorem abs_covariance_le_of_bounded {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {C₁ C₂ : ℝ}
    -- USER-INPUT: uniform bounds; FY Prop 2.5(ii)
    (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |cov[f, g; μ]| ≤ 4 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  set α := alphaMixCoeff μ m₁ m₂ with hα
  have hC₁ : 0 ≤ C₁ := le_trans (abs_nonneg _) hfC.exists.choose_spec
  have hC₂ : 0 ≤ C₂ := le_trans (abs_nonneg _) hgC.exists.choose_spec
  have hfsm : StronglyMeasurable[m₁] f := hf.stronglyMeasurable
  have hgsm : StronglyMeasurable[m₂] g := hg.stronglyMeasurable
  have hfn : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁ := by simpa [Real.norm_eq_abs] using hfC
  have hgn : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂ := by simpa [Real.norm_eq_abs] using hgC
  have hfLp : MemLp f 2 μ :=
    (memLp_top_of_bound (hfsm.mono h₁).aestronglyMeasurable C₁ hfn).mono_exponent le_top
  have hgLp : MemLp g 2 μ :=
    (memLp_top_of_bound (hgsm.mono h₂).aestronglyMeasurable C₂ hgn).mono_exponent le_top
  have hfint : Integrable f μ := hfLp.integrable one_le_two
  -- Step A: peel `f` against an arbitrary `m₂`-event; the discrepancies are the α set.
  have hstepA : ∀ B : Set Ω, MeasurableSet[m₂] B →
      |(∫ ω in B, f ω ∂μ) - (∫ ω, f ω ∂μ) * (μ B).toReal| ≤ 2 * C₁ * α := by
    intro B hB
    have hBΩ : MeasurableSet B := h₂ B hB
    have hind : Integrable (B.indicator (1 : Ω → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator hBΩ
    have h := abs_integral_mul_sub_le_of_setIntegral_bound (m := m₁) (mΩ := mΩ) h₁
      hfsm hfC hind (K := α) ?_
    · have e1 : ∫ ω, f ω * B.indicator (1 : Ω → ℝ) ω ∂μ = ∫ ω in B, f ω ∂μ := by
        rw [← integral_indicator hBΩ]
        congr 1 with ω
        by_cases hω : ω ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      have e2 : ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ B).toReal := by
        rw [integral_indicator hBΩ]
        simp [measureReal_def]
      rw [e1, e2] at h
      exact h
    · intro A hA
      have e3 : ∫ ω in A, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ (A ∩ B)).toReal := by
        rw [setIntegral_indicator hBΩ]
        simp [measureReal_def]
      have e4 : ∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ = (μ B).toReal := by
        rw [integral_indicator hBΩ]
        simp [measureReal_def]
      rw [e3, e4, mul_comm ((μ B).toReal) ((μ A).toReal)]
      exact le_alphaMixCoeff_of_measurableSet (mΩ := mΩ) (μ := μ) hA hB
  -- Step B: peel `g` against `f`, feeding Step A as the discrepancy bound.
  have hstepB := abs_integral_mul_sub_le_of_setIntegral_bound (m := m₂) (mΩ := mΩ) h₂
    hgsm hgC hfint (K := 2 * C₁ * α) hstepA
  rw [covariance_eq_sub hfLp hgLp]
  have e5 : ∫ ω, g ω * f ω ∂μ = ∫ ω, f ω * g ω ∂μ := by simp_rw [mul_comm]
  rw [e5] at hstepB
  have e6 : (∫ ω, f ω * g ω ∂μ) - (∫ ω, g ω ∂μ) * ∫ ω, f ω ∂μ
      = μ[f * g] - μ[f] * μ[g] := by
    simp only [Pi.mul_apply]
    ring
  rw [e6] at hstepB
  calc |μ[f * g] - μ[f] * μ[g]| ≤ 2 * C₂ * (2 * C₁ * α) := hstepB
    _ = 4 * α * C₁ * C₂ := by ring

/-- Billingsley's inequality in the `E[fg] − Ef·Eg` form (the shape the complex and
Volkonskii–Rozanov arguments consume). -/
private lemma abs_integral_mul_sub_mul_le_of_bounded {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g) {C₁ C₂ : ℝ}
    (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ|
      ≤ 4 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  have hfn : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁ := by simpa [Real.norm_eq_abs] using hfC
  have hgn : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂ := by simpa [Real.norm_eq_abs] using hgC
  have hfLp : MemLp f 2 μ :=
    (memLp_top_of_bound ((hf.stronglyMeasurable.mono h₁)).aestronglyMeasurable C₁ hfn).mono_exponent
      le_top
  have hgLp : MemLp g 2 μ :=
    (memLp_top_of_bound ((hg.stronglyMeasurable.mono h₂)).aestronglyMeasurable C₂ hgn).mono_exponent
      le_top
  have h := abs_covariance_le_of_bounded h₁ h₂ hf hg hfC hgC
  rwa [covariance_eq_sub hfLp hgLp] at h

private lemma abs_comb_le {x y z w K : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) (hz : |z| ≤ K)
    (hw : |w| ≤ K) : |x - y| + |z + w| ≤ 4 * K := by
  have h1 : |x - y| ≤ |x| + |y| := by
    have h := abs_add_le x (-y)
    rwa [abs_neg, ← sub_eq_add_neg] at h
  have h2 : |z + w| ≤ |z| + |w| := abs_add_le z w
  linarith

/-- **Complex Billingsley** (FY §2.6.2, constant 16): unit-modulus-bounded complex
factors. Stated with the real-bilinear covariance
`E[f·g] − E[f]·E[g]` in `ℂ`. -/
theorem norm_covariance_le_of_bounded_complex {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℂ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {C₁ C₂ : ℝ}
    -- USER-INPUT: uniform bounds; FY §2.6.2 complex remark
    (hfC : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ C₁) (hgC : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ C₂) :
    ‖(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ‖
      ≤ 16 * alphaMixCoeff μ m₁ m₂ * C₁ * C₂ := by
  have hre : Measurable (Complex.re) := Complex.continuous_re.measurable
  have him : Measurable (Complex.im) := Complex.continuous_im.measurable
  have hf₁ : Measurable[m₁] fun ω => (f ω).re := hre.comp hf
  have hf₂ : Measurable[m₁] fun ω => (f ω).im := him.comp hf
  have hg₁ : Measurable[m₂] fun ω => (g ω).re := hre.comp hg
  have hg₂ : Measurable[m₂] fun ω => (g ω).im := him.comp hg
  have hf₁C : ∀ᵐ ω ∂μ, |(f ω).re| ≤ C₁ := by
    filter_upwards [hfC] with ω hω using (Complex.abs_re_le_norm _).trans hω
  have hf₂C : ∀ᵐ ω ∂μ, |(f ω).im| ≤ C₁ := by
    filter_upwards [hfC] with ω hω using (Complex.abs_im_le_norm _).trans hω
  have hg₁C : ∀ᵐ ω ∂μ, |(g ω).re| ≤ C₂ := by
    filter_upwards [hgC] with ω hω using (Complex.abs_re_le_norm _).trans hω
  have hg₂C : ∀ᵐ ω ∂μ, |(g ω).im| ≤ C₂ := by
    filter_upwards [hgC] with ω hω using (Complex.abs_im_le_norm _).trans hω
  -- integrability
  have hfsm : StronglyMeasurable f := (hf.mono h₁ le_rfl).stronglyMeasurable
  have hf₁' : StronglyMeasurable fun ω => (f ω).re := (hf₁.mono h₁ le_rfl).stronglyMeasurable
  have hf₂' : StronglyMeasurable fun ω => (f ω).im := (hf₂.mono h₁ le_rfl).stronglyMeasurable
  have hg₁' : StronglyMeasurable fun ω => (g ω).re := (hg₁.mono h₂ le_rfl).stronglyMeasurable
  have hg₂' : StronglyMeasurable fun ω => (g ω).im := (hg₂.mono h₂ le_rfl).stronglyMeasurable
  have hgsm : StronglyMeasurable g := (hg.mono h₂ le_rfl).stronglyMeasurable
  have hfint : Integrable f μ :=
    (memLp_top_of_bound hfsm.aestronglyMeasurable C₁ hfC).integrable le_top
  have hgint : Integrable g μ :=
    (memLp_top_of_bound hgsm.aestronglyMeasurable C₂ hgC).integrable le_top
  have hfgint : Integrable (fun ω => f ω * g ω) μ :=
    hgint.bdd_mul hfsm.aestronglyMeasurable hfC
  have hcre : ∀ {F : Ω → ℂ}, Integrable F μ → (∫ ω, F ω ∂μ).re = ∫ ω, (F ω).re ∂μ := by
    intro F hF
    simpa using (integral_re hF).symm
  have hcim : ∀ {F : Ω → ℂ}, Integrable F μ → (∫ ω, F ω ∂μ).im = ∫ ω, (F ω).im ∂μ := by
    intro F hF
    simpa using (integral_im hF).symm
  have hint₁ : Integrable (fun ω => (f ω).re) μ :=
    (memLp_top_of_bound (hf₁').aestronglyMeasurable C₁
      (by simpa [Real.norm_eq_abs] using hf₁C)).integrable le_top
  have hint₂ : Integrable (fun ω => (f ω).im) μ :=
    (memLp_top_of_bound (hf₂').aestronglyMeasurable C₁
      (by simpa [Real.norm_eq_abs] using hf₂C)).integrable le_top
  have hint₃ : Integrable (fun ω => (g ω).re) μ :=
    (memLp_top_of_bound (hg₁').aestronglyMeasurable C₂
      (by simpa [Real.norm_eq_abs] using hg₁C)).integrable le_top
  have hint₄ : Integrable (fun ω => (g ω).im) μ :=
    (memLp_top_of_bound (hg₂').aestronglyMeasurable C₂
      (by simpa [Real.norm_eq_abs] using hg₂C)).integrable le_top
  have hprod : ∀ {u v : Ω → ℝ} {D : ℝ}, StronglyMeasurable u → Integrable v μ →
      (∀ᵐ ω ∂μ, |u ω| ≤ D) → Integrable (fun ω => u ω * v ω) μ := by
    intro u v D hu hv hb
    exact hv.bdd_mul hu.aestronglyMeasurable (by simpa [Real.norm_eq_abs] using hb)
  have e11 : Integrable (fun ω => (f ω).re * (g ω).re) μ := hprod hf₁' hint₃ hf₁C
  have e22 : Integrable (fun ω => (f ω).im * (g ω).im) μ := hprod hf₂' hint₄ hf₂C
  have e12 : Integrable (fun ω => (f ω).re * (g ω).im) μ := hprod hf₁' hint₄ hf₁C
  have e21 : Integrable (fun ω => (f ω).im * (g ω).re) μ := hprod hf₂' hint₃ hf₂C
  -- real and imaginary parts of the complex covariance
  have hRe : ((∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ).re
      = ((∫ ω, (f ω).re * (g ω).re ∂μ) - (∫ ω, (f ω).re ∂μ) * ∫ ω, (g ω).re ∂μ)
        - ((∫ ω, (f ω).im * (g ω).im ∂μ) - (∫ ω, (f ω).im ∂μ) * ∫ ω, (g ω).im ∂μ) := by
    rw [Complex.sub_re, Complex.mul_re, hcre hfgint, hcre hfint, hcre hgint, hcim hfint,
      hcim hgint]
    have : ∀ ω, (f ω * g ω).re = (f ω).re * (g ω).re - (f ω).im * (g ω).im := by
      intro ω; rw [Complex.mul_re]
    simp_rw [this]
    rw [integral_sub e11 e22]
    ring
  have hIm : ((∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ).im
      = ((∫ ω, (f ω).re * (g ω).im ∂μ) - (∫ ω, (f ω).re ∂μ) * ∫ ω, (g ω).im ∂μ)
        + ((∫ ω, (f ω).im * (g ω).re ∂μ) - (∫ ω, (f ω).im ∂μ) * ∫ ω, (g ω).re ∂μ) := by
    rw [Complex.sub_im, Complex.mul_im, hcim hfgint, hcre hfint, hcre hgint, hcim hfint,
      hcim hgint]
    have : ∀ ω, (f ω * g ω).im = (f ω).re * (g ω).im + (f ω).im * (g ω).re := by
      intro ω; rw [Complex.mul_im]
    simp_rw [this]
    rw [integral_add e12 e21]
    ring
  have b11 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₁ hg₁ hf₁C hg₁C
  have b22 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₂ hg₂ hf₂C hg₂C
  have b12 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₁ hg₂ hf₁C hg₂C
  have b21 := abs_integral_mul_sub_mul_le_of_bounded (mΩ := mΩ) h₁ h₂ hf₂ hg₁ hf₂C hg₁C
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hRe, hIm]
  refine (abs_comb_le b11 b22 b12 b21).trans ?_
  ring_nf
  rfl


/-! ### Proposition 2.5(i): the Davydov covariance inequality -/

/-- Tail Hölder: the `L^r`-mass of `u` on a set `S` is controlled by its `L^t`-norm times a
power of `μ S`. -/
private lemma tail_holder {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} {r t : ℝ} (hr : 0 < r) (hrt : r < t) (hu : MemLp u (ENNReal.ofReal t) μ)
    {S : Set Ω} (hS : MeasurableSet S) :
    ∫ ω, S.indicator (fun ω => |u ω| ^ r) ω ∂μ
      ≤ (∫ ω, |u ω| ^ t ∂μ) ^ (r / t) * (μ.real S) ^ (1 - r / t) := by
  have ht : 0 < t := lt_trans hr hrt
  have htr : 0 < t - r := by linarith
  set P : ℝ := t / r with hP
  set Q : ℝ := t / (t - r) with hQ
  have hconj : Real.HolderConjugate P Q := by
    refine ⟨?_, by positivity, by positivity⟩
    rw [hP, hQ]
    field_simp
    ring
  have hmem : MemLp (fun ω => |u ω| ^ r) (ENNReal.ofReal P) μ := by
    have h := hu.norm_rpow_div (ENNReal.ofReal r)
    rw [ENNReal.toReal_ofReal hr.le, ← ENNReal.ofReal_div_of_pos hr] at h
    simpa [Real.norm_eq_abs] using h
  have hind : MemLp (S.indicator (1 : Ω → ℝ)) (ENNReal.ofReal Q) μ := by
    refine (memLp_top_of_bound ((stronglyMeasurable_const.indicator hS)).aestronglyMeasurable 1
      ?_).mono_exponent le_top
    filter_upwards with ω
    exact (norm_indicator_le_norm_self (1 : Ω → ℝ) ω).trans (by simp)
  have key := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj
    (f := fun ω => |u ω| ^ r) (g := S.indicator (1 : Ω → ℝ))
    (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
    (Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    hmem hind
  have e1 : ∀ ω, S.indicator (fun ω => |u ω| ^ r) ω
      = (|u ω| ^ r) * S.indicator (1 : Ω → ℝ) ω := by
    intro ω
    by_cases hω : ω ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have e2 : ∫ ω, (S.indicator (1 : Ω → ℝ) ω) ^ Q ∂μ = μ.real S := by
    have h : ∀ ω, (S.indicator (1 : Ω → ℝ) ω) ^ Q = S.indicator (1 : Ω → ℝ) ω := by
      intro ω
      by_cases hω : ω ∈ S
      · simp [Set.indicator_of_mem, hω, Real.one_rpow]
      · simp [Set.indicator_of_notMem, hω, Real.zero_rpow hconj.symm.ne_zero]
    rw [funext h, integral_indicator_one hS]
  have e3 : ∀ ω, (|u ω| ^ r) ^ P = |u ω| ^ t := by
    intro ω
    rw [← Real.rpow_mul (abs_nonneg _), hP]
    congr 1
    field_simp
  simp_rw [e1]
  rw [e2] at key
  refine key.trans_eq ?_
  rw [show ∫ ω, (|u ω| ^ r) ^ P ∂μ = ∫ ω, |u ω| ^ t ∂μ from integral_congr_ae
    (Eventually.of_forall e3)]
  rw [show (1:ℝ) / P = r / t by rw [hP]; field_simp,
    show (1:ℝ) / Q = 1 - r / t by rw [hQ]; field_simp]


/-- Markov/Chebyshev in the form needed below. -/
private lemma markov_rpow {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {u : Ω → ℝ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (hum : Measurable u)
    (hint : Integrable (fun ω => |u ω| ^ r) μ) :
    μ.real {ω | c < |u ω|} * c ^ r ≤ ∫ ω, |u ω| ^ r ∂μ := by
  have hS : MeasurableSet {ω | c < |u ω|} := measurableSet_lt measurable_const (by fun_prop)
  have h1 : ∫ ω, ({ω | c < |u ω|}).indicator (fun _ => c ^ r) ω ∂μ ≤ ∫ ω, |u ω| ^ r ∂μ := by
    refine integral_mono ((integrable_const _).indicator hS) hint fun ω => ?_
    by_cases hω : ω ∈ {ω | c < |u ω|}
    · rw [Set.indicator_of_mem hω]
      exact Real.rpow_le_rpow hc.le (le_of_lt hω) hr.le
    · rw [Set.indicator_of_notMem hω]
      exact Real.rpow_nonneg (abs_nonneg _) _
  rwa [integral_indicator_const _ hS, smul_eq_mul] at h1

/-- Clamping to `[-c, c]` is bounded by `c`. -/
private lemma abs_clamp_le {c x : ℝ} (hc : 0 ≤ c) : |max (-c) (min c x)| ≤ c := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clamping is a contraction towards the origin. -/
private lemma abs_sub_clamp_le_of_lt {c x : ℝ} (hc : 0 ≤ c) (hx : c < |x|) :
    |x - max (-c) (min c x)| ≤ |x| := by
  rcases le_total c x with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), abs_of_nonneg (by linarith : (0:ℝ) ≤ x - c),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ x)]
    linarith
  · have h2 : x ≤ -c := by
      rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at hx <;> linarith
    rw [min_eq_right h, max_eq_left h2, abs_of_nonpos (by linarith : x - -c ≤ 0),
      abs_of_nonpos (by linarith : x ≤ 0)]
    linarith

/-- Below the level, clamping is the identity. -/
private lemma sub_clamp_eq_zero {c x : ℝ} (hx : |x| ≤ c) : x - max (-c) (min c x) = 0 := by
  rw [abs_le] at hx
  rw [min_eq_right hx.2, max_eq_right hx.1, sub_self]

private lemma covariance_eq_sub' {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) (hfg : Integrable (fun ω => f ω * g ω) μ) :
    cov[f, g; μ] = (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  have i1 : Integrable (fun ω => f ω * g ω - μ[g] * f ω) μ := hfg.sub (hf.const_mul _)
  have i2 : Integrable (fun ω => f ω * g ω - μ[g] * f ω - μ[f] * g ω) μ := i1.sub (hg.const_mul _)
  have e0 : ∫ ω, ((f ω * g ω - μ[g] * f ω - μ[f] * g ω) + μ[f] * μ[g]) ∂μ
      = (∫ ω, (f ω * g ω - μ[g] * f ω - μ[f] * g ω) ∂μ) + ∫ _ω : Ω, μ[f] * μ[g] ∂μ :=
    integral_add i2 (integrable_const _)
  have e1 : ∫ ω, (f ω * g ω - μ[g] * f ω - μ[f] * g ω) ∂μ
      = (∫ ω, (f ω * g ω - μ[g] * f ω) ∂μ) - ∫ ω, μ[f] * g ω ∂μ :=
    integral_sub i1 (hg.const_mul _)
  have e2 : ∫ ω, (f ω * g ω - μ[g] * f ω) ∂μ
      = (∫ ω, f ω * g ω ∂μ) - ∫ ω, μ[g] * f ω ∂μ :=
    integral_sub hfg (hf.const_mul _)
  have e3 : ∫ ω, μ[f] * g ω ∂μ = μ[f] * ∫ ω, g ω ∂μ := integral_const_mul _ _
  have e4 : ∫ ω, μ[g] * f ω ∂μ = μ[g] * ∫ ω, f ω ∂μ := integral_const_mul _ _
  have e5 : ∫ _ω : Ω, μ[f] * μ[g] ∂μ = μ[f] * μ[g] := by simp
  have h : ∀ ω, (f ω - μ[f]) * (g ω - μ[g])
      = (f ω * g ω - μ[g] * f ω - μ[f] * g ω) + μ[f] * μ[g] := by intro ω; ring
  rw [covariance, integral_congr_ae (Eventually.of_forall h), e0, e1, e2, e3, e4, e5]
  ring

set_option maxHeartbeats 1000000 in
-- Davydov's truncation argument is long (four Hölder applications and a limit);
-- the default heartbeat budget is not enough.
/-- **FY Proposition 2.5(i) (Davydov)**: for `p, q > 1` with `1/p + 1/q < 1`,
`|Cov(f, g)| ≤ 8 α^{1 − 1/p − 1/q} ‖f‖_p ‖g‖_q`. Built in full (truncation against the
bounded case; FY cites Doukhan §1.2.2). -/
theorem abs_covariance_le_davydov {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    {p q : ℝ}
    -- USER-INPUT: integrability exponents; FY Prop 2.5(i)
    (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q < 1)
    (hfLp : MemLp f (ENNReal.ofReal p) μ) (hgLq : MemLp g (ENNReal.ofReal q) μ) :
    |cov[f, g; μ]|
      ≤ 8 * alphaMixCoeff μ m₁ m₂ ^ (1 - 1 / p - 1 / q)
        * (eLpNorm f (ENNReal.ofReal p) μ).toReal
        * (eLpNorm g (ENNReal.ofReal q) μ).toReal := by
  -- exponent bookkeeping
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hq0 : (0:ℝ) < q := lt_trans one_pos hq
  have hip : 0 < 1 / p := by positivity
  have hiq : 0 < 1 / q := by positivity
  set p' : ℝ := p / (p - 1) with hp'def
  have hp1 : (0:ℝ) < p - 1 := by linarith
  have hp'0 : 0 < p' := by positivity
  have hinvp' : 1 / p' = 1 - 1 / p := by rw [hp'def]; field_simp
  have hp'1 : 1 < p' := by
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have h : 1 ≤ 1 / p' := by rw [le_div_iff₀ hp'0]; linarith
    rw [hinvp'] at h; linarith
  have hp'q : p' < q := by
    have h1 : 1 / q < 1 / p' := by rw [hinvp']; linarith
    by_contra hcon
    replace hcon := not_lt.mp hcon
    have := one_div_le_one_div_of_le hq0 hcon
    linarith
  set θ : ℝ := 1 - 1 / p - 1 / q with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hθp' : θ = 1 / p' - 1 / q := by rw [hθdef, hinvp']
  set α : ℝ := alphaMixCoeff μ m₁ m₂ with hαdef
  set A : ℝ := (eLpNorm f (ENNReal.ofReal p) μ).toReal with hAdef
  set B : ℝ := (eLpNorm g (ENNReal.ofReal q) μ).toReal with hBdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hα0 : 0 ≤ α := by
    have h := le_alphaMixCoeff_of_measurableSet (m₁ := m₁) (m₂ := m₂) (mΩ := mΩ) (μ := μ)
      (A := ∅) (B := ∅)
      (@MeasurableSet.empty Ω m₁) (@MeasurableSet.empty Ω m₂)
    simpa using h
  have hconjp : Real.HolderConjugate p p' := ⟨by rw [hp'def]; field_simp; ring, hp0, hp'0⟩
  -- measurability and integrability
  have hfm : Measurable f := hf.mono h₁ le_rfl
  have hgm : Measurable g := hg.mono h₂ le_rfl
  have hfint : Integrable f μ := hfLp.integrable (by simp [ENNReal.one_le_ofReal, hp.le])
  have hgint : Integrable g μ := hgLq.integrable (by simp [ENNReal.one_le_ofReal, hq.le])
  have hIf : Integrable (fun ω => |f ω| ^ p) μ := by
    have h := hfLp.integrable_norm_rpow (by simp [hp0]) (by simp)
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using h
  have hIg : Integrable (fun ω => |g ω| ^ q) μ := by
    have h := hgLq.integrable_norm_rpow (by simp [hq0]) (by simp)
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hq0.le] using h
  have hA : A = (∫ ω, |f ω| ^ p ∂μ) ^ (1 / p) := by
    rw [hAdef, toReal_eLpNorm hfLp.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by simp [hp0]) (by simp) hfLp.aestronglyMeasurable,
      ENNReal.toReal_ofReal hp0.le]
    simp [Real.norm_eq_abs, one_div]
  have hB : B = (∫ ω, |g ω| ^ q ∂μ) ^ (1 / q) := by
    rw [hBdef, toReal_eLpNorm hgLq.aestronglyMeasurable,
      lpNorm_eq_integral_norm_rpow_toReal (by simp [hq0]) (by simp) hgLq.aestronglyMeasurable,
      ENNReal.toReal_ofReal hq0.le]
    simp [Real.norm_eq_abs, one_div]
  have hAp : A ^ p = ∫ ω, |f ω| ^ p ∂μ := by
    rw [hA, ← Real.rpow_mul (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _), one_div,
      inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  have hBq : B ^ q = ∫ ω, |g ω| ^ q ∂μ := by
    rw [hB, ← Real.rpow_mul (integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _), one_div,
      inv_mul_cancel₀ hq0.ne', Real.rpow_one]
  -- `g` lies in `L^{p'}` as well
  have hgLp' : MemLp g (ENNReal.ofReal p') μ :=
    hgLq.mono_exponent (ENNReal.ofReal_le_ofReal hp'q.le)
  have hfgint : Integrable (fun ω => f ω * g ω) μ := by
    haveI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal p') 1 := by
      constructor
      simpa using hconjp.inv_add_inv_ennreal
    exact hfLp.integrable_mul hgLp'
  have hcov : cov[f, g; μ] = (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ :=
    covariance_eq_sub' hfint hgint hfgint
  -- degenerate cases
  rcases eq_or_lt_of_le hA0 with hA0' | hApos
  · have hfae : f =ᵐ[μ] 0 := by
      have hpne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
      refine (eLpNorm_eq_zero_iff hfLp.aestronglyMeasurable hpne).mp ?_
      have := hfLp.eLpNorm_ne_top
      rcases (ENNReal.toReal_eq_zero_iff _).mp hA0'.symm with h | h
      · exact h
      · exact absurd h this
    have hz : cov[f, g; μ] = 0 := by
      have h0 : μ[f] = 0 := by rw [integral_congr_ae hfae]; simp
      rw [covariance, h0]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hfae] with ω hω
      simp [hω]
    rw [hz, abs_zero, ← hA0']
    simp
  rcases eq_or_lt_of_le hB0 with hB0' | hBpos
  · have hgae : g =ᵐ[μ] 0 := by
      have hqne : ENNReal.ofReal q ≠ 0 := by simp [hq0]
      refine (eLpNorm_eq_zero_iff hgLq.aestronglyMeasurable hqne).mp ?_
      have := hgLq.eLpNorm_ne_top
      rcases (ENNReal.toReal_eq_zero_iff _).mp hB0'.symm with h | h
      · exact h
      · exact absurd h this
    have hz : cov[f, g; μ] = 0 := by
      have h0 : μ[g] = 0 := by rw [integral_congr_ae hgae]; simp
      rw [covariance, h0]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hgae] with ω hω
      simp [hω]
    rw [hz, abs_zero, ← hB0']
    simp
  -- the main estimate, at every level `β = α + ε`
  have main : ∀ ε : ℝ, 0 < ε → |cov[f, g; μ]| ≤ 8 * (α + ε) ^ θ * A * B := by
    intro ε hε
    set β : ℝ := α + ε with hβdef
    have hβ0 : 0 < β := by rw [hβdef]; linarith
    set c₁ : ℝ := A * β ^ (-(1 / p)) with hc₁def
    set c₂ : ℝ := B * β ^ (-(1 / q)) with hc₂def
    have hc₁0 : 0 < c₁ := mul_pos hApos (Real.rpow_pos_of_pos hβ0 _)
    have hc₂0 : 0 < c₂ := mul_pos hBpos (Real.rpow_pos_of_pos hβ0 _)
    set f' : Ω → ℝ := fun ω => max (-c₁) (min c₁ (f ω)) with hf'def
    set g' : Ω → ℝ := fun ω => max (-c₂) (min c₂ (g ω)) with hg'def
    set S : Set Ω := {ω | c₁ < |f ω|} with hSdef
    set T : Set Ω := {ω | c₂ < |g ω|} with hTdef
    have hSm : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
    have hTm : MeasurableSet T := measurableSet_lt measurable_const (by fun_prop)
    have hf'meas : Measurable[m₁] f' := measurable_const.max (measurable_const.min hf)
    have hg'meas : Measurable[m₂] g' := measurable_const.max (measurable_const.min hg)
    have hf'm : Measurable f' := hf'meas.mono h₁ le_rfl
    have hg'm : Measurable g' := hg'meas.mono h₂ le_rfl
    have hf'bdd : ∀ ω, |f' ω| ≤ c₁ := fun ω => abs_clamp_le hc₁0.le
    have hg'bdd : ∀ ω, |g' ω| ≤ c₂ := fun ω => abs_clamp_le hc₂0.le
    have hf''le : ∀ ω, |f ω - f' ω| ≤ S.indicator (fun ω => |f ω|) ω := by
      intro ω
      by_cases hω : ω ∈ S
      · rw [Set.indicator_of_mem hω]
        exact abs_sub_clamp_le_of_lt hc₁0.le hω
      · rw [Set.indicator_of_notMem hω, sub_clamp_eq_zero (not_lt.mp hω), abs_zero]
    have hg''le : ∀ ω, |g ω - g' ω| ≤ T.indicator (fun ω => |g ω|) ω := by
      intro ω
      by_cases hω : ω ∈ T
      · rw [Set.indicator_of_mem hω]
        exact abs_sub_clamp_le_of_lt hc₂0.le hω
      · rw [Set.indicator_of_notMem hω, sub_clamp_eq_zero (not_lt.mp hω), abs_zero]
    -- pointwise domination of the tails
    have hgg'abs : ∀ ω, |g ω - g' ω| ≤ |g ω| := by
      intro ω
      refine (hg''le ω).trans ?_
      by_cases hω : ω ∈ T
      · rw [Set.indicator_of_mem hω]
      · rw [Set.indicator_of_notMem hω]; exact abs_nonneg _
    -- Markov
    have hMS : μ.real S ≤ β := by
      have h := markov_rpow (u := f) (r := p) (c := c₁) hp0 hc₁0 hfm hIf
      have hc : c₁ ^ p * β = A ^ p := by
        rw [hc₁def, Real.mul_rpow hA0 (Real.rpow_nonneg hβ0.le _), ← Real.rpow_mul hβ0.le,
          show -(1 / p) * p = -1 by field_simp, Real.rpow_neg_one]
        field_simp
      have hcp : 0 < c₁ ^ p := Real.rpow_pos_of_pos hc₁0 p
      have h2 : μ.real S * c₁ ^ p ≤ β * c₁ ^ p := by
        rw [mul_comm β, hc, hAp]; exact h
      exact le_of_mul_le_mul_right h2 hcp
    have hMT : μ.real T ≤ β := by
      have h := markov_rpow (u := g) (r := q) (c := c₂) hq0 hc₂0 hgm hIg
      have hc : c₂ ^ q * β = B ^ q := by
        rw [hc₂def, Real.mul_rpow hB0 (Real.rpow_nonneg hβ0.le _), ← Real.rpow_mul hβ0.le,
          show -(1 / q) * q = -1 by field_simp, Real.rpow_neg_one]
        field_simp
      have hcq : 0 < c₂ ^ q := Real.rpow_pos_of_pos hc₂0 q
      have h2 : μ.real T * c₂ ^ q ≤ β * c₂ ^ q := by
        rw [mul_comm β, hc, hBq]; exact h
      exact le_of_mul_le_mul_right h2 hcq
    -- integrability of the pieces
    have hf'int : Integrable f' μ :=
      (memLp_top_of_bound hf'm.aestronglyMeasurable c₁
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hf'bdd ω)).integrable
        le_top
    have hg'int : Integrable g' μ :=
      (memLp_top_of_bound hg'm.aestronglyMeasurable c₂
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hg'bdd ω)).integrable
        le_top
    have hg'n : ∀ᵐ ω ∂μ, ‖g' ω‖ ≤ c₂ :=
      Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hg'bdd ω
    have hf''int : Integrable (fun ω => f ω - f' ω) μ := hfint.sub hf'int
    have hg''int : Integrable (fun ω => g ω - g' ω) μ := hgint.sub hg'int
    have hfg'int : Integrable (fun ω => f ω * g' ω) μ :=
      hfint.mul_bdd hg'm.aestronglyMeasurable hg'n
    have hf'g'int : Integrable (fun ω => f' ω * g' ω) μ :=
      hf'int.mul_bdd hg'm.aestronglyMeasurable hg'n
    have hf''g'int : Integrable (fun ω => (f ω - f' ω) * g' ω) μ :=
      hf''int.mul_bdd hg'm.aestronglyMeasurable hg'n
    have hfg''int : Integrable (fun ω => f ω * (g ω - g' ω)) μ := by
      have h : ∀ ω, f ω * (g ω - g' ω) = f ω * g ω - f ω * g' ω := by intro ω; ring
      simpa [h] using! hfgint.sub hfg'int
    -- the three-term decomposition
    have e1 : (∫ ω, f ω * g' ω ∂μ) + (∫ ω, f ω * (g ω - g' ω) ∂μ) = ∫ ω, f ω * g ω ∂μ := by
      rw [← integral_add hfg'int hfg''int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have e2 : (∫ ω, f' ω * g' ω ∂μ) + (∫ ω, (f ω - f' ω) * g' ω ∂μ) = ∫ ω, f ω * g' ω ∂μ := by
      rw [← integral_add hf'g'int hf''g'int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have e3 : (∫ ω, g' ω ∂μ) + (∫ ω, (g ω - g' ω) ∂μ) = ∫ ω, g ω ∂μ := by
      rw [← integral_add hg'int hg''int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have e4 : (∫ ω, f' ω ∂μ) + (∫ ω, (f ω - f' ω) ∂μ) = ∫ ω, f ω ∂μ := by
      rw [← integral_add hf'int hf''int]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    have hsplit : (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)
        = ((∫ ω, f' ω * g' ω ∂μ) - (∫ ω, f' ω ∂μ) * ∫ ω, g' ω ∂μ)
          + ((∫ ω, (f ω - f' ω) * g' ω ∂μ) - (∫ ω, (f ω - f' ω) ∂μ) * ∫ ω, g' ω ∂μ)
          + ((∫ ω, f ω * (g ω - g' ω) ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, (g ω - g' ω) ∂μ) := by
      rw [← e1, ← e2, ← e3, ← e4]
      ring
    -- tail bounds
    have hTf : ∫ ω, |f ω - f' ω| ∂μ ≤ A * β ^ (1 - 1 / p) := by
      have h1 : ∫ ω, |f ω - f' ω| ∂μ ≤ ∫ ω, S.indicator (fun ω => |f ω|) ω ∂μ :=
        integral_mono hf''int.abs (hfint.abs.indicator hSm) fun ω => hf''le ω
      have h2 := tail_holder (u := f) (r := 1) (t := p) one_pos hp hfLp hSm
      simp only [Real.rpow_one] at h2
      refine h1.trans (h2.trans ?_)
      rw [← hA]
      refine mul_le_mul_of_nonneg_left ?_ hA0
      exact Real.rpow_le_rpow measureReal_nonneg hMS (by linarith)
    have hgg'Lp' : MemLp (fun ω => g ω - g' ω) (ENNReal.ofReal p') μ :=
      hgLp'.of_le (hgint.sub hg'int).aestronglyMeasurable
        (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hgg'abs ω)
    have hIgg' : Integrable (fun ω => |g ω - g' ω| ^ p') μ := by
      have h := hgg'Lp'.integrable_norm_rpow (by simp [hp'0]) (by simp)
      simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp'0.le] using h
    have hN : (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') ≤ B * β ^ θ := by
      have hIgp' : Integrable (fun ω => |g ω| ^ p') μ := by
        have h := hgLp'.integrable_norm_rpow (by simp [hp'0]) (by simp)
        simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp'0.le] using h
      have h1 : ∫ ω, |g ω - g' ω| ^ p' ∂μ ≤ ∫ ω, T.indicator (fun ω => |g ω| ^ p') ω ∂μ := by
        refine integral_mono hIgg' (hIgp'.indicator hTm) fun ω => ?_
        · by_cases hω : ω ∈ T
          · rw [Set.indicator_of_mem hω]
            exact Real.rpow_le_rpow (abs_nonneg _) (hgg'abs ω) hp'0.le
          · rw [Set.indicator_of_notMem hω, sub_clamp_eq_zero (not_lt.mp hω), abs_zero,
              Real.zero_rpow hp'0.ne']
      have h2 := tail_holder (u := g) (r := p') (t := q) hp'0 hp'q hgLq hTm
      have h3 : ∫ ω, |g ω - g' ω| ^ p' ∂μ ≤ B ^ p' * β ^ (1 - p' / q) := by
        refine (h1.trans (h2.trans ?_))
        have hBp' : (∫ ω, |g ω| ^ q ∂μ) ^ (p' / q) = B ^ p' := by
          rw [← hBq, ← Real.rpow_mul hB0]
          congr 1
          field_simp
        rw [hBp']
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hB0 _)
        refine Real.rpow_le_rpow measureReal_nonneg hMT ?_
        rw [sub_nonneg, div_le_one hq0]
        exact hp'q.le
      calc (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p')
          ≤ (B ^ p' * β ^ (1 - p' / q)) ^ (1 / p') := by
            refine Real.rpow_le_rpow ?_ h3 (by positivity)
            exact integral_nonneg fun ω => Real.rpow_nonneg (abs_nonneg _) _
        _ = B * β ^ θ := by
            rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hβ0.le _),
              ← Real.rpow_mul hB0, ← Real.rpow_mul hβ0.le,
              mul_one_div, div_self hp'0.ne', Real.rpow_one]
            congr 1
            rw [hθp']
            field_simp
    have hTg : ∫ ω, |g ω - g' ω| ∂μ ≤ (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') := by
      have h := tail_holder (u := fun ω => g ω - g' ω) (r := 1) (t := p') one_pos hp'1 hgg'Lp'
        MeasurableSet.univ
      simpa using h
    have hIA : ∫ ω, |f ω| ∂μ ≤ A := by
      have h := tail_holder (u := f) (r := 1) (t := p) one_pos hp hfLp MeasurableSet.univ
      simp only [Real.rpow_one, Set.indicator_univ, probReal_univ, Real.one_rpow,
        mul_one] at h
      rw [hA]
      exact h
    -- the three covariance terms
    have hsub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
      have h := abs_add_le x (-y)
      rwa [abs_neg, ← sub_eq_add_neg] at h
    have hT1 : |(∫ ω, f' ω * g' ω ∂μ) - (∫ ω, f' ω ∂μ) * ∫ ω, g' ω ∂μ| ≤ 4 * α * c₁ * c₂ := by
      have h := abs_covariance_le_of_bounded (mΩ := mΩ) (μ := μ) h₁ h₂ hf'meas hg'meas
        (Eventually.of_forall hf'bdd) (Eventually.of_forall hg'bdd)
      rwa [covariance_eq_sub' hf'int hg'int hf'g'int] at h
    have hb1 : |∫ ω, (f ω - f' ω) * g' ω ∂μ| ≤ c₂ * ∫ ω, |f ω - f' ω| ∂μ := by
      calc |∫ ω, (f ω - f' ω) * g' ω ∂μ| ≤ ∫ ω, |(f ω - f' ω) * g' ω| ∂μ :=
            abs_integral_le_integral_abs
        _ ≤ ∫ ω, |f ω - f' ω| * c₂ ∂μ := by
            refine integral_mono hf''g'int.abs (hf''int.abs.mul_const c₂) fun ω => ?_
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hg'bdd ω) (abs_nonneg _)
        _ = (∫ ω, |f ω - f' ω| ∂μ) * c₂ := integral_mul_const _ _
        _ = c₂ * ∫ ω, |f ω - f' ω| ∂μ := mul_comm _ _
    have hb3 : |∫ ω, g' ω ∂μ| ≤ c₂ := by
      have h := norm_integral_le_of_norm_le_const (μ := μ) hg'n
      simpa using h
    have hT2 : |(∫ ω, (f ω - f' ω) * g' ω ∂μ) - (∫ ω, (f ω - f' ω) ∂μ) * ∫ ω, g' ω ∂μ|
        ≤ 2 * (c₂ * (A * β ^ (1 - 1 / p))) := by
      refine (hsub _ _).trans ?_
      rw [abs_mul]
      have h4 : |∫ ω, (f ω - f' ω) ∂μ| * |∫ ω, g' ω ∂μ| ≤ c₂ * ∫ ω, |f ω - f' ω| ∂μ := by
        rw [mul_comm c₂]
        exact mul_le_mul (abs_integral_le_integral_abs) hb3 (abs_nonneg _)
          (integral_nonneg fun ω => abs_nonneg _)
      have h5 : c₂ * (∫ ω, |f ω - f' ω| ∂μ) ≤ c₂ * (A * β ^ (1 - 1 / p)) :=
        mul_le_mul_of_nonneg_left hTf hc₂0.le
      linarith
    have hfabs : MemLp (fun ω => |f ω|) (ENNReal.ofReal p) μ := by
      simpa [Real.norm_eq_abs] using hfLp.norm
    have hgg'abs' : MemLp (fun ω => |g ω - g' ω|) (ENNReal.ofReal p') μ := by
      simpa [Real.norm_eq_abs] using hgg'Lp'.norm
    have hb4 : |∫ ω, f ω * (g ω - g' ω) ∂μ| ≤ A * (B * β ^ θ) := by
      calc |∫ ω, f ω * (g ω - g' ω) ∂μ| ≤ ∫ ω, |f ω * (g ω - g' ω)| ∂μ :=
            abs_integral_le_integral_abs
        _ = ∫ ω, |f ω| * |g ω - g' ω| ∂μ := by simp_rw [abs_mul]
        _ ≤ (∫ ω, |f ω| ^ p ∂μ) ^ (1 / p) * (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') :=
            integral_mul_le_Lp_mul_Lq_of_nonneg hconjp
              (Eventually.of_forall fun ω => abs_nonneg _)
              (Eventually.of_forall fun ω => abs_nonneg _) hfabs hgg'abs'
        _ = A * (∫ ω, |g ω - g' ω| ^ p' ∂μ) ^ (1 / p') := by rw [← hA]
        _ ≤ A * (B * β ^ θ) := mul_le_mul_of_nonneg_left hN hA0
    have hT3 : |(∫ ω, f ω * (g ω - g' ω) ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, (g ω - g' ω) ∂μ|
        ≤ 2 * (A * (B * β ^ θ)) := by
      refine (hsub _ _).trans ?_
      rw [abs_mul]
      have h5 : |∫ ω, f ω ∂μ| * |∫ ω, (g ω - g' ω) ∂μ| ≤ A * (B * β ^ θ) := by
        refine mul_le_mul (abs_integral_le_integral_abs.trans hIA)
          (abs_integral_le_integral_abs.trans (hTg.trans hN)) (abs_nonneg _) hA0
      linarith
    -- the exponent ledger
    have hβθ : β * (β ^ (-(1 / p)) * β ^ (-(1 / q))) = β ^ θ := by
      rw [← Real.rpow_add hβ0]
      calc β * β ^ (-(1 / p) + -(1 / q)) = β ^ (1:ℝ) * β ^ (-(1 / p) + -(1 / q)) := by
            rw [Real.rpow_one]
        _ = β ^ (1 + (-(1 / p) + -(1 / q))) := (Real.rpow_add hβ0 _ _).symm
        _ = β ^ θ := by rw [hθdef]; congr 1; ring
    have hbc : β * (c₁ * c₂) = A * B * β ^ θ := by
      rw [hc₁def, hc₂def, ← hβθ]; ring
    have hbc2 : c₂ * (A * β ^ (1 - 1 / p)) = A * B * β ^ θ := by
      have h : β ^ (-(1 / q)) * β ^ (1 - 1 / p) = β ^ θ := by
        rw [← Real.rpow_add hβ0, hθdef]
        congr 1
        ring
      rw [hc₂def]
      calc B * β ^ (-(1 / q)) * (A * β ^ (1 - 1 / p))
          = A * B * (β ^ (-(1 / q)) * β ^ (1 - 1 / p)) := by ring
        _ = A * B * β ^ θ := by rw [h]
    -- assemble
    rw [hcov, hsplit]
    have habs3 : ∀ x y z : ℝ, |x + y + z| ≤ |x| + |y| + |z| := fun x y z => by
      have h1 := abs_add_le (x + y) z
      have h2 := abs_add_le x y
      linarith
    refine (habs3 _ _ _).trans ?_
    have hα' : α ≤ β := by rw [hβdef]; linarith
    have hcc : 0 ≤ c₁ * c₂ := by positivity
    have hkey1 : 4 * α * c₁ * c₂ ≤ 4 * (A * B * β ^ θ) := by
      have h : α * (c₁ * c₂) ≤ β * (c₁ * c₂) := mul_le_mul_of_nonneg_right hα' hcc
      rw [hbc] at h
      nlinarith [h]
    have h2 := hT2
    rw [hbc2] at h2
    have h3 : 2 * (A * (B * β ^ θ)) = 2 * (A * B * β ^ θ) := by ring
    rw [h3] at hT3
    have hfinal : 4 * (A * B * β ^ θ) + 2 * (A * B * β ^ θ) + 2 * (A * B * β ^ θ)
        = 8 * β ^ θ * A * B := by ring
    linarith [hT1, hkey1, h2, hT3]
  -- pass to the limit `ε → 0`
  have hcontα : ContinuousAt (fun y : ℝ => 8 * y ^ θ * A * B) α :=
    (((Real.continuousAt_rpow_const α θ (Or.inr hθ0.le)).const_mul 8).mul continuousAt_const).mul
      continuousAt_const
  have hlim : Tendsto (fun ε : ℝ => 8 * (α + ε) ^ θ * A * B) (𝓝[>] (0:ℝ))
      (𝓝 (8 * α ^ θ * A * B)) := by
    have h1 : Tendsto (fun ε : ℝ => α + ε) (𝓝[>] (0:ℝ)) (𝓝 α) := by
      have h2 : Continuous (fun ε : ℝ => α + ε) := continuous_const.add continuous_id
      simpa using (h2.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    exact hcontα.tendsto.comp h1
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using main ε hε


/-! ### Proposition 2.6: the Volkonskii–Rozanov factorization -/

/-- **FY Proposition 2.6 (Volkonskii–Rozanov), repaired form — PROVED (axiom-clean).**
Identical to `norm_integral_prod_sub_prod_integral_le` except for the hypothesis `0 < k`,
which is exactly what that statement is missing: at `k = 0` its right-hand side
`16 · (0 − 1) · a = −16a` is negative while its left-hand side is `0` (see there).  Every
consumer has `k ≥ 1` — the number of Bernstein blocks — so this is the form to use.

Complex unit-bounded blocks measured against an increasing family with α-gaps at most `a`
factorize up to `16 (k − 1) a`.  The gap hypothesis is abstract: the α-coefficient between
the cumulative past `⨆_{j ≤ l} m j` and the next block `m (l+1)` is at most `a` —
process-level applications supply it via `IsStrictlyStationary.alphaMixCoeff_shift` and
monotonicity.

Proof: induction on the number `n` of blocks already multiplied in, the step being the
telescope `∫ P·ξ − ∏∫ = (∫ P·ξ − (∫P)(∫ξ)) + (∫P − ∏∫)·∫ξ` whose first summand is a
covariance of two unit-bounded complex variables, measurable for the cumulative past and
for the next block respectively, hence at most `16 a` by
`norm_covariance_le_of_bounded_complex`, and whose second is the induction hypothesis
times a factor of modulus `≤ 1`. -/
theorem norm_integral_prod_sub_prod_integral_le_of_pos {k : ℕ}
    {m : Fin k → MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hk : 0 < k) (hle : ∀ l, m l ≤ mΩ)
    (ξ : Fin k → Ω → ℂ) (hmeas : ∀ l, Measurable[m l] (ξ l))
    -- USER-INPUT: unit modulus bound; FY Prop 2.6
    (hbdd : ∀ l, ∀ᵐ ω ∂μ, ‖ξ l ω‖ ≤ 1)
    {a : ℝ}
    -- USER-INPUT: α-gap bound between cumulative past and next block; FY Prop 2.6
    (hgap : ∀ l : Fin k, ∀ hl : (l : ℕ) + 1 < k,
      alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ l, m j) (m ⟨(l : ℕ) + 1, hl⟩) ≤ a) :
    ‖(∫ ω, ∏ l, ξ l ω ∂μ) - ∏ l, ∫ ω, ξ l ω ∂μ‖
      ≤ 16 * ((k : ℝ) - 1) * a := by
  classical
  have hbdd' : ∀ᵐ ω ∂μ, ∀ l, ‖ξ l ω‖ ≤ 1 := ae_all_iff.mpr hbdd
  set S : ℕ → Finset (Fin k) := fun n => Finset.univ.filter (fun j : Fin k => (j : ℕ) < n)
    with hSdef
  -- the cumulative product is bounded by 1
  have hPbdd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖∏ j ∈ S n, ξ j ω‖ ≤ 1 := by
    intro n
    filter_upwards [hbdd'] with ω hω
    rw [norm_prod]
    exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hω i)
  have hint : ∀ l : Fin k, ‖∫ ω, ξ l ω ∂μ‖ ≤ 1 := by
    intro l
    have h := norm_integral_le_of_norm_le_const (μ := μ) (hbdd l)
    simpa using h
  have main : ∀ n : ℕ, 1 ≤ n → n ≤ k →
      ‖(∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ‖ ≤ 16 * ((n : ℝ) - 1) * a := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      have h1 : S 1 = ({⟨0, hk⟩} : Finset (Fin k)) := by
        ext j
        simp [hSdef, Fin.ext_iff]
      rw [h1]
      simp
    | succ n hn ih =>
      intro hnk
      have hnk' : n < k := by omega
      have ihb := ih (by omega)
      set l : Fin k := ⟨n - 1, by omega⟩ with hl
      set l' : Fin k := ⟨n, hnk'⟩ with hl'
      have hln : (l : ℕ) + 1 = n := by simp [hl]; omega
      have hMle : (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j) ≤ mΩ :=
        iSup_le fun j => iSup_le fun _ => hle j
      have hmem : ∀ j ∈ S n, m j ≤ ⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j := by
        intro j hj
        simp only [hSdef, Finset.mem_filter] at hj
        exact le_iSup₂ (f := fun (j : Fin k) (_ : (j : ℕ) ≤ (l : ℕ)) => m j) j (by omega)
      have hPmeas : Measurable[⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j]
          (fun ω => ∏ j ∈ S n, ξ j ω) :=
        Finset.measurable_prod _ fun j hj => (hmeas j).mono (hmem j hj) le_rfl
      -- the α-gap bound transported to the cumulative past and the next block
      have hα : alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j) (m l') ≤ a := by
        have h := hgap l (by omega)
        have he : (⟨(l : ℕ) + 1, by omega⟩ : Fin k) = l' := by
          apply Fin.ext; simp [hl', hln]
        rw [he] at h
        exact h
      have hcov := norm_covariance_le_of_bounded_complex
        (m₁ := ⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ (l : ℕ), m j) (m₂ := m l') (mΩ := mΩ)
        hMle (hle l') hPmeas (hmeas l') (hPbdd n) (hbdd l')
      -- the recursion
      have hnot : (l' : Fin k) ∉ S n := by simp [hSdef, hl']
      have hins : S (n + 1) = insert l' (S n) := by
        ext j
        simp [hSdef, hl', Fin.ext_iff]
        omega
      have hP1 : ∀ ω, ∏ j ∈ S (n + 1), ξ j ω = (∏ j ∈ S n, ξ j ω) * ξ l' ω := by
        intro ω
        rw [hins, Finset.prod_insert hnot, mul_comm]
      have hP2 : ∏ j ∈ S (n + 1), (∫ ω, ξ j ω ∂μ)
          = (∏ j ∈ S n, ∫ ω, ξ j ω ∂μ) * ∫ ω, ξ l' ω ∂μ := by
        rw [hins, Finset.prod_insert hnot, mul_comm]
      have hexp : (∫ ω, ∏ j ∈ S (n + 1), ξ j ω ∂μ) - ∏ j ∈ S (n + 1), ∫ ω, ξ j ω ∂μ
          = ((∫ ω, (∏ j ∈ S n, ξ j ω) * ξ l' ω ∂μ)
              - (∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) * ∫ ω, ξ l' ω ∂μ)
            + ((∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ)
              * (∫ ω, ξ l' ω ∂μ) := by
        simp_rw [hP1]
        rw [hP2]
        ring
      rw [hexp]
      refine (norm_add_le _ _).trans ?_
      have hb1 : ‖(∫ ω, (∏ j ∈ S n, ξ j ω) * ξ l' ω ∂μ)
          - (∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) * ∫ ω, ξ l' ω ∂μ‖ ≤ 16 * a := by
        refine hcov.trans ?_
        nlinarith [hα]
      have hb2 : ‖((∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ)
          * (∫ ω, ξ l' ω ∂μ)‖ ≤ 16 * ((n : ℝ) - 1) * a := by
        rw [norm_mul]
        calc ‖(∫ ω, ∏ j ∈ S n, ξ j ω ∂μ) - ∏ j ∈ S n, ∫ ω, ξ j ω ∂μ‖ * ‖∫ ω, ξ l' ω ∂μ‖
            ≤ (16 * ((n : ℝ) - 1) * a) * 1 := by
              refine mul_le_mul ihb (hint l') (norm_nonneg _) ?_
              exact le_trans (norm_nonneg _) ihb
          _ = 16 * ((n : ℝ) - 1) * a := by ring
      have : (16 : ℝ) * (((n : ℝ) + 1) - 1) * a = 16 * a + 16 * ((n : ℝ) - 1) * a := by ring
      push_cast
      rw [this]
      linarith
  have hSk : S k = Finset.univ := by
    ext j
    simp [hSdef]
  have := main k hk le_rfl
  rwa [hSk] at this

/-- **FY Proposition 2.6 (Volkonskii–Rozanov)**: complex unit-bounded blocks measured
against an increasing family with α-gaps at most `a` factorize up to `16 (k − 1) a`.
The gap hypothesis is abstract: the α-coefficient between the cumulative past
`⨆_{j ≤ l} m j` and the next block `m (l+1)` is at most `a` — process-level
applications supply it via `IsStrictlyStationary.alphaMixCoeff_shift` and
monotonicity.

**Status: PROVED — REPAIRED to `0 < k` (laptop, 2026-08-09).** The original frozen form
quantified over all `k`, and its `k = 0` corner is FALSE (verified):  At `k = 0` the index
type `Fin 0` is empty, so every hypothesis is vacuous and `a` is unconstrained; the left
side is exactly `‖1 − 1‖ = 0` (empty products, `∫ 1 = 1`) while the right side is
`16 · (0 − 1) · a = −16a`, negative for every `a > 0`.  The claim `0 ≤ −16a` is therefore
refutable.  **Repair**: add `1 ≤ k`, or replace the factor `(k − 1)` by `(k − 1 : ℕ)` cast
to `ℝ`, either of which makes the statement true.  The first of those repairs **is**
available, proved and axiom-clean, as the sibling
`norm_integral_prod_sub_prod_integral_le_of_pos` immediately above, to which the `k ≥ 1`
branch below delegates; new consumers should call that one, since no consumer needs
`k = 0`.

**Repair history.** Wave `ts/s2b` carried out this repair and reverted it because
`LimitTheorems.lean`'s private `norm_integral_prod_blocks_sub_prod_le` consumed the
unconstrained form (itself false at `k = 0` the same way). Wave `ts/s5b` then rebuilt that
consumer with its own `0 < k` hypothesis delegating to `_of_pos`, leaving THIS statement
consumer-free, so the laptop applied the repair.
-- USER-INPUT: nonempty block family; FY Prop 2.6 (the k = 0 corner is refutable) -/
theorem norm_integral_prod_sub_prod_integral_le {k : ℕ} (hk : 0 < k)
    {m : Fin k → MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hle : ∀ l, m l ≤ mΩ)
    (ξ : Fin k → Ω → ℂ) (hmeas : ∀ l, Measurable[m l] (ξ l))
    -- USER-INPUT: unit modulus bound; FY Prop 2.6
    (hbdd : ∀ l, ∀ᵐ ω ∂μ, ‖ξ l ω‖ ≤ 1)
    {a : ℝ}
    -- USER-INPUT: α-gap bound between cumulative past and next block; FY Prop 2.6
    (hgap : ∀ l : Fin k, ∀ hl : (l : ℕ) + 1 < k,
      alphaMixCoeff μ (⨆ j : Fin k, ⨆ _ : (j : ℕ) ≤ l, m j) (m ⟨(l : ℕ) + 1, hl⟩) ≤ a) :
    ‖(∫ ω, ∏ l, ξ l ω ∂μ) - ∏ l, ∫ ω, ξ l ω ∂μ‖
      ≤ 16 * ((k : ℝ) - 1) * a := by
  exact norm_integral_prod_sub_prod_integral_le_of_pos hk hle ξ hmeas hbdd hgap


end TwoAlgebras

/-! ### The fourth-moment bound (FY Proposition 2.7(ii) at `q = 4`) -/

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! The probabilistic half of FY Proposition 2.7(ii) at `q = 4`: the mixing bound on
`E[X_{t₁}X_{t₂}X_{t₃}X_{t₄}]` for a sorted 4-tuple, obtained by splitting the product at
its largest gap.  At the two outer splits the product term vanishes because the marginals
are centred; at the middle split it is `E[X_{t₁}X_{t₂}]·E[X_{t₃}X_{t₄}]`, itself a pair of
covariances of centred variables. -/

section Moment4

variable {X : ℤ → Ω → ℝ}

/-- `X s` is measurable for the past σ-algebra at any later time. -/
private lemma measurable_sigmaLE (X : ℤ → Ω → ℝ) {s t : ℤ} (hst : s ≤ t) :
    Measurable[sigmaLE X t] (X s) :=
  (Measurable.of_comap_le le_rfl).mono
    (le_iSup₂ (f := fun r (_ : r ∈ Set.Iic t) =>
      MeasurableSpace.comap (X r) inferInstance) s hst) le_rfl

/-- `X s` is measurable for the future σ-algebra at any earlier time. -/
private lemma measurable_sigmaGE (X : ℤ → Ω → ℝ) {s t : ℤ} (hst : t ≤ s) :
    Measurable[sigmaGE X t] (X s) :=
  (Measurable.of_comap_le le_rfl).mono
    (le_iSup₂ (f := fun r (_ : r ∈ Set.Ici t) =>
      MeasurableSpace.comap (X r) inferInstance) s hst) le_rfl

private lemma sigmaLE_le (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLE X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

private lemma sigmaGE_le (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaGE X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

/-- A bounded measurable function on a probability space is integrable. -/
private lemma integrable_of_bdd [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ᵐ ω ∂μ, |f ω| ≤ B) : Integrable f μ :=
  Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (by filter_upwards [hb] with ω hω; rwa [Real.norm_eq_abs])

/-- Mean zero propagates to every time by strict stationarity. -/
private lemma integral_eq_zero_of_stat [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (t : ℤ) : ∫ ω, X t ω ∂μ = 0 := by
  rw [(hstat.identDistrib hmeas t 0).integral_eq, hmean]

/-- **The cut bound**: Billingsley's inequality across a cut of the time axis, with the
mixing coefficient identified as `alphaCoeff` at the gap (this is where stationarity
enters, through `IsStrictlyStationary.alphaMixCoeff_shift`). -/
private lemma abs_integral_mul_sub_le_cut [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    {a b : ℤ} (hab : a ≤ b) {f g : Ω → ℝ}
    (hf : Measurable[sigmaLE X a] f) (hg : Measurable[sigmaGE X b] g)
    {C₁ C₂ : ℝ} (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ|
      ≤ 4 * alphaCoeff X μ (b - a).toNat * C₁ * C₂ := by
  have hbe : a + ((b - a).toNat : ℤ) = b := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hα : alphaMixCoeff μ (sigmaLE X a) (sigmaGE X b) = alphaCoeff X μ (b - a).toNat := by
    have := IsStrictlyStationary.alphaMixCoeff_shift hstat hmeas a (b - a).toNat
    rwa [hbe] at this
  have h1 : sigmaLE X a ≤ (inferInstance : MeasurableSpace Ω) := sigmaLE_le hmeas a
  have h2 : sigmaGE X b ≤ (inferInstance : MeasurableSpace Ω) := sigmaGE_le hmeas b
  have hcov := abs_covariance_le_of_bounded h1 h2 hf hg hfC hgC
  rw [hα] at hcov
  have hfm : Measurable f := hf.mono h1 le_rfl
  have hgm : Measurable g := hg.mono h2 le_rfl
  have hfi : Integrable f μ := integrable_of_bdd hfm hfC
  have hgi : Integrable g μ := integrable_of_bdd hgm hgC
  have hfgi : Integrable (fun ω => f ω * g ω) μ := by
    refine integrable_of_bdd (hfm.mul hgm) (B := C₁ * C₂) ?_
    filter_upwards [hfC, hgC] with ω e1 e2
    rw [abs_mul]
    exact mul_le_mul e1 e2 (abs_nonneg _) (le_trans (abs_nonneg _) e1)
  rwa [covariance_eq_sub' hfi hgi hfgi] at hcov

/-- The pair bound `|E X_a X_b| ≤ 4 C² α(b − a)` (the product term vanishes: `E X_a = 0`). -/
private lemma abs_integral_pair_le [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {a b : ℤ} (hab : a ≤ b) :
    |∫ ω, X a ω * X b ω ∂μ| ≤ 4 * alphaCoeff X μ (b - a).toNat * C * C := by
  have h0 : (∫ ω, X a ω ∂μ) = 0 := integral_eq_zero_of_stat hstat hmeas hmean a
  have := abs_integral_mul_sub_le_cut hstat hmeas hab
    (measurable_sigmaLE X (le_refl a)) (measurable_sigmaGE X (le_refl b)) (hbdd a) (hbdd b)
  rwa [h0, zero_mul, sub_zero] at this

/-- Nonnegativity of the process α-coefficient. -/
private lemma alphaCoeff_nonneg' [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ) (m : ℕ) :
    0 ≤ alphaCoeff X μ m := alphaMixCoeff_nonneg (mΩ := inferInstance)

private lemma abs_mul_le_of_bdd {x y B₁ B₂ : ℝ} (hx : |x| ≤ B₁) (hy : |y| ≤ B₂) :
    |x * y| ≤ B₁ * B₂ := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)

/-- **The sorted 4-tuple bound** (the probabilistic content of FY Prop 2.7(ii) at `q = 4`):
split `E[X_a X_b X_c X_d]` at its largest gap.  At the two outer splits the product term
vanishes because `E X_t = 0`; at the middle split it is `E[X_aX_b]·E[X_cX_d]`, bounded by
the pair estimate. -/
private lemma abs_integral_quad_le [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {a b c d : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (max (b - a).toNat (max (c - b).toNat (d - c).toNat))
        + 16 * C ^ 4 * (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hbdd 0).exists.choose_spec
  have hzero : ∀ t : ℤ, (∫ ω, X t ω ∂μ) = 0 :=
    integral_eq_zero_of_stat hstat hmeas hmean
  have hprod0 : (0:ℝ) ≤ alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat :=
    mul_nonneg (alphaCoeff_nonneg' X _) (alphaCoeff_nonneg' X _)
  have hC4 : (0:ℝ) ≤ C ^ 4 := by positivity
  -- (L) the left split: `X_a` against `X_b X_c X_d`
  have hL : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (b - a).toNat := by
    have hgm : Measurable[sigmaGE X b] fun ω => X b ω * X c ω * X d ω :=
      ((measurable_sigmaGE X (le_refl b)).mul (measurable_sigmaGE X hbc)).mul
        (measurable_sigmaGE X (hbc.trans hcd))
    have hgC : ∀ᵐ ω ∂μ, |X b ω * X c ω * X d ω| ≤ C * C * C := by
      filter_upwards [hbdd b, hbdd c, hbdd d] with ω e1 e2 e3
      exact abs_mul_le_of_bdd (abs_mul_le_of_bdd e1 e2) e3
    have key := abs_integral_mul_sub_le_cut hstat hmeas hab
      (measurable_sigmaLE X (le_refl a)) hgm (hbdd a) hgC
    rw [hzero a, zero_mul, sub_zero] at key
    have hre : (∫ ω, X a ω * (X b ω * X c ω * X d ω) ∂μ)
        = ∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [hre] at key
    refine key.trans (le_of_eq ?_)
    ring
  -- (R) the right split: `X_a X_b X_c` against `X_d`
  have hR : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (d - c).toNat := by
    have hfm : Measurable[sigmaLE X c] fun ω => X a ω * X b ω * X c ω :=
      ((measurable_sigmaLE X (hab.trans hbc)).mul (measurable_sigmaLE X hbc)).mul
        (measurable_sigmaLE X (le_refl c))
    have hfC : ∀ᵐ ω ∂μ, |X a ω * X b ω * X c ω| ≤ C * C * C := by
      filter_upwards [hbdd a, hbdd b, hbdd c] with ω e1 e2 e3
      exact abs_mul_le_of_bdd (abs_mul_le_of_bdd e1 e2) e3
    have key := abs_integral_mul_sub_le_cut hstat hmeas hcd hfm
      (measurable_sigmaGE X (le_refl d)) hfC (hbdd d)
    rw [hzero d, mul_zero, sub_zero] at key
    refine key.trans (le_of_eq ?_)
    ring
  -- (M) the middle split: `X_a X_b` against `X_c X_d`
  have hM : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (c - b).toNat
        + 16 * C ^ 4 * (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by
    have hfm : Measurable[sigmaLE X b] fun ω => X a ω * X b ω :=
      (measurable_sigmaLE X hab).mul (measurable_sigmaLE X (le_refl b))
    have hgm : Measurable[sigmaGE X c] fun ω => X c ω * X d ω :=
      (measurable_sigmaGE X (le_refl c)).mul (measurable_sigmaGE X hcd)
    have hfC : ∀ᵐ ω ∂μ, |X a ω * X b ω| ≤ C * C := by
      filter_upwards [hbdd a, hbdd b] with ω e1 e2
      exact abs_mul_le_of_bdd e1 e2
    have hgC : ∀ᵐ ω ∂μ, |X c ω * X d ω| ≤ C * C := by
      filter_upwards [hbdd c, hbdd d] with ω e1 e2
      exact abs_mul_le_of_bdd e1 e2
    have key := abs_integral_mul_sub_le_cut hstat hmeas hbc hfm hgm hfC hgC
    have hre : (∫ ω, (X a ω * X b ω) * (X c ω * X d ω) ∂μ)
        = ∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [hre] at key
    have hpair1 := abs_integral_pair_le hstat hmeas hbdd hmean hab
    have hpair2 := abs_integral_pair_le hstat hmeas hbdd hmean hcd
    have hsplit : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
        ≤ |(∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ)
            - (∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ|
          + |(∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ| := by
      have := abs_add_le ((∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ)
        - (∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ)
        ((∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ)
      simpa using this
    have hpp : |(∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ|
        ≤ (4 * alphaCoeff X μ (b - a).toNat * C * C)
          * (4 * alphaCoeff X μ (d - c).toNat * C * C) := by
      rw [abs_mul]
      exact mul_le_mul hpair1 hpair2 (abs_nonneg _) (le_trans (abs_nonneg _) hpair1)
    have harr : (4 * alphaCoeff X μ (b - a).toNat * C * C)
          * (4 * alphaCoeff X μ (d - c).toNat * C * C)
        = 16 * C ^ 4 * (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by
      ring
    rw [harr] at hpp
    have hkey' : |(∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ)
        - (∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ|
        ≤ 4 * C ^ 4 * alphaCoeff X μ (c - b).toNat := by
      refine key.trans (le_of_eq ?_)
      ring
    linarith
  -- pick the split at the largest gap
  have hextra : (0:ℝ) ≤ 16 * C ^ 4 *
      (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by positivity
  rcases max_choice (b - a).toNat (max (c - b).toNat (d - c).toNat) with hmx | hmx
  · rw [hmx]; linarith
  · rw [hmx]
    rcases max_choice (c - b).toNat (d - c).toNat with hmx' | hmx'
    · rw [hmx']; linarith
    · rw [hmx']; linarith

/-- The four-fold expansion of a fourth power of a finite sum. -/
private lemma sum_pow_four_expand {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ t ∈ s, f t) ^ 4
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, f a * f b * f c * f d := by
  have h2 : (∑ t ∈ s, f t) * (∑ t ∈ s, f t) = ∑ a ∈ s, ∑ b ∈ s, f a * f b := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
  have h3 : (∑ t ∈ s, f t) ^ 3 = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c := by
    have e : (∑ t ∈ s, f t) ^ 3 = (∑ a ∈ s, ∑ b ∈ s, f a * f b) * ∑ t ∈ s, f t := by
      rw [← h2]; ring
    rw [e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _
  have e : (∑ t ∈ s, f t) ^ 4
      = (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c) * ∑ t ∈ s, f t := by
    rw [← h3]; ring
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => Finset.mul_sum _ _ _

/-- Invariance of a 4-tuple functional under a permutation, from invariance under swaps. -/
private theorem tuple4_comp_perm_invariant {Gt : (Fin 4 → ℕ) → ℝ}
    (hs : ∀ (i j : Fin 4) (f : Fin 4 → ℕ), Gt (f ∘ Equiv.swap i j) = Gt f)
    (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → ℕ) : Gt (f ∘ σ) = Gt f := by
  have hmem : σ ∈ Submonoid.closure {τ : Equiv.Perm (Fin 4) | τ.IsSwap} := by
    rw [Equiv.Perm.mclosure_isSwap]; trivial
  revert f
  induction hmem using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, _, rfl⟩ := hx
      exact fun f => hs i j f
  | one => intro f; simp
  | mul x y hx hy ihx ihy =>
      intro f
      have hcomp : f ∘ (x * y) = (f ∘ x) ∘ y := by
        funext a; simp [Equiv.Perm.mul_apply]
      rw [hcomp, ihy (f ∘ x), ihx f]

private theorem tuple4_swap_invariant {G : ℕ → ℕ → ℕ → ℕ → ℝ}
    (hGs1 : ∀ a b c d, G a b c d = G b a c d)
    (hGs2 : ∀ a b c d, G a b c d = G a c b d)
    (hGs3 : ∀ a b c d, G a b c d = G a b d c)
    (i j : Fin 4) (f : Fin 4 → ℕ) :
    G ((f ∘ Equiv.swap i j) 0) ((f ∘ Equiv.swap i j) 1) ((f ∘ Equiv.swap i j) 2)
        ((f ∘ Equiv.swap i j) 3)
      = G (f 0) (f 1) (f 2) (f 3) := by
  have e02 : ∀ a b c d, G a b c d = G c b a d := fun a b c d =>
    (hGs1 a b c d).trans ((hGs2 b a c d).trans (hGs1 b c a d))
  have e13 : ∀ a b c d, G a b c d = G a d c b := fun a b c d =>
    (hGs2 a b c d).trans ((hGs3 a c b d).trans (hGs2 a c d b))
  have e03 : ∀ a b c d, G a b c d = G d b c a := fun a b c d =>
    (hGs1 a b c d).trans ((hGs3 b a c d).trans ((hGs2 b a d c).trans
      ((hGs1 b d a c).trans (hGs3 d b a c))))
  fin_cases i <;> fin_cases j <;>
    simp only [Function.comp_apply, Equiv.swap_apply_def] <;> norm_num <;>
    first
      | rfl
      | exact (hGs1 _ _ _ _).symm
      | exact (hGs2 _ _ _ _).symm
      | exact (hGs3 _ _ _ _).symm
      | exact (e02 _ _ _ _).symm
      | exact (e13 _ _ _ _).symm
      | exact (e03 _ _ _ _).symm

/-- Symmetrisation: a permutation-invariant nonnegative functional summed over a
permutation-closed family is at most `4!` times its sum over the sorted members. -/
private theorem sum_tuple4_le_sorted {Gt : (Fin 4 → ℕ) → ℝ} (hGt0 : ∀ f, 0 ≤ Gt f)
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → ℕ), Gt (f ∘ σ) = Gt f)
    (P : Finset (Fin 4 → ℕ))
    (hP : ∀ f ∈ P, ∀ σ : Equiv.Perm (Fin 4), f ∘ σ ∈ P) :
    ∑ f ∈ P, Gt f
      ≤ 24 * ∑ u ∈ P.filter (fun u => u 0 ≤ u 1 ∧ u 1 ≤ u 2 ∧ u 2 ≤ u 3), Gt u := by
  classical
  set Φ : (Fin 4 → ℕ) → (Fin 4 → ℕ) := fun f => f ∘ Tuple.sort f with hΦ
  set Pm := P.filter (fun u => u 0 ≤ u 1 ∧ u 1 ≤ u 2 ∧ u 2 ≤ u 3) with hPm
  have hmaps : ∀ f ∈ P, Φ f ∈ Pm := by
    intro f hf
    have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
    refine Finset.mem_filter.2 ⟨hP f hf _, ?_, ?_, ?_⟩
    · exact hmono (by decide : (0 : Fin 4) ≤ 1)
    · exact hmono (by decide : (1 : Fin 4) ≤ 2)
    · exact hmono (by decide : (2 : Fin 4) ≤ 3)
  have hcard : ∀ u : Fin 4 → ℕ, (P.filter (fun f => Φ f = u)).card ≤ 24 := by
    intro u
    have hsub : P.filter (fun f => Φ f = u)
        ⊆ (Finset.univ : Finset (Equiv.Perm (Fin 4))).image
            (fun σ : Equiv.Perm (Fin 4) => u ∘ (σ : Fin 4 → Fin 4)) := by
      intro f hf
      obtain ⟨-, hfu⟩ := Finset.mem_filter.1 hf
      refine Finset.mem_image.2 ⟨(Tuple.sort f)⁻¹, Finset.mem_univ _, ?_⟩
      rw [← hfu, hΦ]
      funext a
      simp
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    decide
  calc ∑ f ∈ P, Gt f
      = ∑ u ∈ Pm, ∑ f ∈ P.filter (fun f => Φ f = u), Gt f :=
        (Finset.sum_fiberwise_of_maps_to hmaps Gt).symm
    _ ≤ ∑ u ∈ Pm, 24 * Gt u := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hval : ∀ f ∈ P.filter (fun f => Φ f = u), Gt f = Gt u := by
          intro f hf
          obtain ⟨-, hfu⟩ := Finset.mem_filter.1 hf
          rw [← hfu, hΦ]
          exact (hperm (Tuple.sort f) f).symm
        rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u) (hGt0 u)
    _ = 24 * ∑ u ∈ Pm, Gt u := by rw [Finset.mul_sum]

private theorem sum_piFinset_four (s : Finset ℕ) (F : (Fin 4 → ℕ) → ℝ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin 4 => s), F f
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F ![a, b, c, d] := by
  classical
  have hprod : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F ![a, b, c, d]
      = ∑ p ∈ s ×ˢ (s ×ˢ (s ×ˢ s)), F ![p.1, p.2.1, p.2.2.1, p.2.2.2] := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product]
  rw [hprod]
  refine Finset.sum_nbij' (fun f => (f 0, f 1, f 2, f 3))
    (fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Fintype.mem_piFinset] at hf
    simp only [Finset.mem_product]
    exact ⟨hf 0, hf 1, hf 2, hf 3⟩
  · intro p hp
    simp only [Finset.mem_product] at hp
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i <;> simp [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
  · intro f _
    funext i
    fin_cases i <;> rfl
  · intro p _
    rfl
  · intro f _
    congr 1
    funext i
    fin_cases i <;> rfl

private theorem sum_inv_sq_le_two (m : ℕ) : ∑ g ∈ Finset.Ico 1 m, (1 : ℝ) / (g : ℝ) ^ 2 ≤ 2 := by
  have aux : ∀ k : ℕ, ∑ g ∈ Finset.Ico 1 (k + 2), (1 : ℝ) / (g : ℝ) ^ 2
      ≤ 2 - 1 / ((k : ℝ) + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [show k + 1 + 2 = (k + 2) + 1 from rfl,
          Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 2)]
        have hstep : (1 : ℝ) / ((k : ℝ) + 2) ^ 2
            ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
          have heq : (1 : ℝ) / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)
              = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
            field_simp
            ring
          rw [heq]
          refine one_div_le_one_div_of_le (by positivity) ?_
          nlinarith [Nat.cast_nonneg (α := ℝ) k]
        have hcast : (((k + 2 : ℕ) : ℝ)) = (k : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        push_cast
        rw [show ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 from by ring]
        linarith
  match m with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
      refine (aux k).trans ?_
      have h : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith

private theorem sum_indicator_le_succ {n m : ℕ} :
    ∑ g ∈ Finset.range n, (if g ≤ m then (1 : ℝ) else 0) ≤ (m : ℝ) + 1 := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.range n).filter (fun g => g ≤ m) ⊆ Finset.range (m + 1) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_range] at hg ⊢
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  have hc' : (((Finset.range n).filter (fun g => g ≤ m)).card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hc
  push_cast at hc'
  linarith

private theorem sum_mixing_le {A : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA1 : ∀ m, A m ≤ 1)
    (hAK : ∀ m : ℕ, 1 ≤ m → A m ≤ K / (m : ℝ) ^ 2) (n : ℕ) :
    ∑ g ∈ Finset.range n, A g ≤ 1 + 2 * K := by
  match n with
  | 0 =>
      rw [Finset.range_zero, Finset.sum_empty]
      linarith
  | (m + 1) =>
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1)]
      have h1 : ∑ g ∈ Finset.Ico 1 (m + 1), A g
          ≤ ∑ g ∈ Finset.Ico 1 (m + 1), K * (1 / (g : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun g hg => ?_
        have hg1 : 1 ≤ g := (Finset.mem_Ico.1 hg).1
        rw [mul_one_div]
        exact hAK g hg1
      have h2 : ∑ g ∈ Finset.Ico 1 (m + 1), K * (1 / (g : ℝ) ^ 2) ≤ K * 2 := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inv_sq_le_two _) hK
      have h3 := hA1 0
      linarith

private theorem sum_mixing_mul_sq_le {A : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA1 : ∀ m, A m ≤ 1)
    (hAK : ∀ m : ℕ, 1 ≤ m → A m ≤ K / (m : ℝ) ^ 2) (n : ℕ) :
    ∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2 ≤ 1 + 4 * K * (n : ℝ) := by
  match n with
  | 0 =>
      rw [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, mul_zero]
      linarith
  | (m + 1) =>
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < m + 1)]
      have h1 : ∑ g ∈ Finset.Ico 1 (m + 1), A g * ((g : ℝ) + 1) ^ 2
          ≤ ∑ _g ∈ Finset.Ico 1 (m + 1), 4 * K := by
        refine Finset.sum_le_sum fun g hg => ?_
        have hg1 : 1 ≤ g := (Finset.mem_Ico.1 hg).1
        have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
        have hb := hAK g hg1
        have hsq : ((g : ℝ) + 1) ^ 2 ≤ 4 * (g : ℝ) ^ 2 := by nlinarith
        calc A g * ((g : ℝ) + 1) ^ 2 ≤ (K / (g : ℝ) ^ 2) * ((g : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_right hb (by positivity)
          _ ≤ (K / (g : ℝ) ^ 2) * (4 * (g : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
          _ = 4 * K := by
              have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
              field_simp
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
      have hm : (((m + 1 - 1 : ℕ)) : ℝ) = (m : ℝ) := by norm_num
      rw [hm] at h1
      have h0 : A 0 * (((0 : ℕ) : ℝ) + 1) ^ 2 = A 0 := by norm_num
      rw [h0]
      have h3 := hA1 0
      have hmn : (m : ℝ) * (4 * K) ≤ 4 * K * ((m : ℝ) + 1) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      push_cast
      linarith

private theorem mixing_max_le_indicators {A : ℕ → ℝ} (hA0 : ∀ m, 0 ≤ A m) (g1 g2 g3 : ℕ) :
    A (max g1 (max g2 g3))
      ≤ (if g2 ≤ g1 then (1 : ℝ) else 0) * (if g3 ≤ g1 then (1 : ℝ) else 0) * A g1
        + (if g1 ≤ g2 then (1 : ℝ) else 0) * (if g3 ≤ g2 then (1 : ℝ) else 0) * A g2
        + (if g1 ≤ g3 then (1 : ℝ) else 0) * (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3 := by
  rcases le_total g1 g2 with h12 | h12 <;> rcases le_total g2 g3 with h23 | h23 <;>
    rcases le_total g1 g3 with h13 | h13 <;>
    simp_all [max_def] <;>
    split_ifs <;> linarith [hA0 g1, hA0 g2, hA0 g3]

private theorem sum_triple_indicator_le {A : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hA0 : ∀ m, 0 ≤ A m)
    (hA1 : ∀ m, A m ≤ 1) (hAK : ∀ m : ℕ, 1 ≤ m → A m ≤ K / (m : ℝ) ^ 2) (n : ℕ) :
    ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
        (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
      ≤ 1 + 4 * K * (n : ℝ) := by
  have hfac : ∀ x : ℕ, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
      (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
      = (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
        ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x) := by
    intro x
    have inner : ∀ y : ℕ, ∑ z ∈ Finset.range n,
        (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
        = (if y ≤ x then (1 : ℝ) else 0) *
          ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x) := by
      intro y
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => mul_assoc _ _ _
    rw [Finset.sum_congr rfl fun y _ => inner y, ← Finset.sum_mul]
  have hbound : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
        ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x)
      ≤ A x * ((x : ℝ) + 1) ^ 2 := by
    intro x _
    have hI0 : (0 : ℝ) ≤ ∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun y _ => by positivity
    have hI := sum_indicator_le_succ (n := n) (m := x)
    have hx0 : (0 : ℝ) ≤ (x : ℝ) + 1 := by positivity
    calc (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
          ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x)
        ≤ ((x : ℝ) + 1) * (((x : ℝ) + 1) * A x) := by
          refine mul_le_mul hI ?_ (mul_nonneg hI0 (hA0 x)) hx0
          exact mul_le_mul_of_nonneg_right hI (hA0 x)
      _ = A x * ((x : ℝ) + 1) ^ 2 := by ring
  calc ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
          (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
      = ∑ x ∈ Finset.range n, (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
          ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x) :=
        Finset.sum_congr rfl fun x _ => hfac x
    _ ≤ ∑ x ∈ Finset.range n, A x * ((x : ℝ) + 1) ^ 2 := Finset.sum_le_sum hbound
    _ ≤ 1 + 4 * K * (n : ℝ) := sum_mixing_mul_sq_le hK hA1 hAK n

private theorem sum_triple_max_le {A : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hA0 : ∀ m, 0 ≤ A m)
    (hA1 : ∀ m, A m ≤ 1) (hAK : ∀ m : ℕ, 1 ≤ m → A m ≤ K / (m : ℝ) ^ 2) (n : ℕ) :
    ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
        A (max g1 (max g2 g3))
      ≤ 3 * (1 + 4 * K * (n : ℝ)) := by
  have hle : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
        A (max g1 (max g2 g3))
      ≤ ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
        ((if g2 ≤ g1 then (1 : ℝ) else 0) * (if g3 ≤ g1 then (1 : ℝ) else 0) * A g1
          + (if g1 ≤ g2 then (1 : ℝ) else 0) * (if g3 ≤ g2 then (1 : ℝ) else 0) * A g2
          + (if g1 ≤ g3 then (1 : ℝ) else 0) * (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3) :=
    Finset.sum_le_sum fun g1 _ => Finset.sum_le_sum fun g2 _ =>
      Finset.sum_le_sum fun g3 _ => mixing_max_le_indicators hA0 g1 g2 g3
  refine hle.trans ?_
  rw [show (3 : ℝ) * (1 + 4 * K * (n : ℝ))
      = (1 + 4 * K * (n : ℝ)) + (1 + 4 * K * (n : ℝ)) + (1 + 4 * K * (n : ℝ)) from by ring]
  simp only [Finset.sum_add_distrib]
  have hT1 : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
      (if g2 ≤ g1 then (1 : ℝ) else 0) * (if g3 ≤ g1 then (1 : ℝ) else 0) * A g1
      ≤ 1 + 4 * K * (n : ℝ) := sum_triple_indicator_le hK hA0 hA1 hAK n
  have hT2 : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
      (if g1 ≤ g2 then (1 : ℝ) else 0) * (if g3 ≤ g2 then (1 : ℝ) else 0) * A g2
      ≤ 1 + 4 * K * (n : ℝ) := by
    rw [Finset.sum_comm]
    exact sum_triple_indicator_le hK hA0 hA1 hAK n
  have hT3 : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
      (if g1 ≤ g3 then (1 : ℝ) else 0) * (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3
      ≤ 1 + 4 * K * (n : ℝ) := by
    rw [Finset.sum_congr rfl fun g1 (_ : g1 ∈ Finset.range n) => Finset.sum_comm
      (s := Finset.range n) (t := Finset.range n)
      (f := fun g2 g3 => (if g1 ≤ g3 then (1 : ℝ) else 0) *
        (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3), Finset.sum_comm]
    exact sum_triple_indicator_le hK hA0 hA1 hAK n
  linarith

private theorem sum_triple_pair_le {A : ℕ → ℝ} {K : ℝ} (hK : 0 ≤ K) (hA0 : ∀ m, 0 ≤ A m)
    (hA1 : ∀ m, A m ≤ 1) (hAK : ∀ m : ℕ, 1 ≤ m → A m ≤ K / (m : ℝ) ^ 2) (n : ℕ) :
    ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n, A g1 * A g3
      ≤ (n : ℝ) * (1 + 2 * K) ^ 2 := by
  set S : ℝ := ∑ g ∈ Finset.range n, A g with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun g _ => hA0 g
  have hS := sum_mixing_le hK hA1 hAK n
  have heq : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n, A g1 * A g3
      = (n : ℝ) * (S * S) := by
    have h3 : ∀ g1 : ℕ, ∑ g3 ∈ Finset.range n, A g1 * A g3 = A g1 * S := by
      intro g1; rw [hSdef, Finset.mul_sum]
    have h2 : ∀ g1 : ℕ, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n, A g1 * A g3
        = (n : ℝ) * (A g1 * S) := by
      intro g1
      rw [Finset.sum_congr rfl fun g2 _ => h3 g1, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun g1 _ => h2 g1, ← Finset.mul_sum]
    rw [show (∑ g1 ∈ Finset.range n, A g1 * S) = S * S from by
      rw [← Finset.sum_mul, ← hSdef]]
  rw [heq]
  have hsq : S * S ≤ (1 + 2 * K) ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)

/-- **The counting half of FY Proposition 2.7(ii) at `q = 4` — PROVED.**

Purely combinatorial: no probability appears.  A symmetric nonnegative kernel `G` on
`ℕ⁴` whose *sorted* values obey the mixing cut bound against an antitone `A ≤ 1` with
`A m ≤ K m⁻²` has `O(n²)` four-fold sums over `range n`.  Everything probabilistic that
feeds this — the cut bound itself — is `abs_integral_quad_le` above.

PROOF, as formalised.  It follows the hand ledger, with two simplifications that remove
the two steps flagged there as expensive:
* **Symmetrisation** (`sum_tuple4_le_sorted`).  Tuples are taken as `Fin 4 → ℕ` and the
  sorting map is Mathlib's `Tuple.sort`, so no explicit sorting network is needed.  `G` is
  invariant under *every* permutation of its arguments — `tuple4_swap_invariant` turns the
  three adjacent transpositions `hGs1`–`hGs3` into all six transpositions, and
  `tuple4_comp_perm_invariant` propagates that along `Equiv.Perm.mclosure_isSwap` — so `G`
  is constant on the fibres of the sort, and each fibre injects into
  `{u ∘ σ : σ ∈ Perm (Fin 4)}`, of cardinality `4! = 24`.  Hence
  `∑_{(range n)⁴} G ≤ 24 · ∑_{sorted} G`.
* **Gap parametrisation.**  `u ↦ (u 0, u 1 − u 0, u 2 − u 1, u 3 − u 2)` is injective on
  sorted tuples (truncated subtraction is exact there) and lands in `(range n)⁴`, so the
  sorted sum is dominated by the *free* sum over `(a, g₁, g₂, g₃)`.
* **First sum** (`sum_triple_max_le`).  Instead of a fibre count over the maximum, the
  pointwise bound `A(max g₁ g₂ g₃) ≤ Σᵢ ⟦gⱼ ≤ gᵢ for all j⟧ · A(gᵢ)`
  (`mixing_max_le_indicators`) is used; each of the three resulting triple sums factorises
  as `∑_g A(g)·(#{y < n : y ≤ g})² ≤ ∑_g A(g)(g+1)² ≤ 1 + 4Kn`
  (`sum_mixing_mul_sq_le`, via `(g+1)² ≤ 4g²` for `g ≥ 1`).
* **Second sum** (`sum_triple_pair_le`).  It factorises as `n · (∑_{g<n} A g)²`, and
  `∑_{g<n} A g ≤ 1 + 2K` (`sum_mixing_le`, from `∑_{g≥1} g⁻² ≤ 2`, `sum_inv_sq_le_two`).
* `D = 24 · (12C⁴ + 48C⁴K + 16C⁴(1+2K)²)` works; the stray linear term is absorbed by
  `n ≤ n²`.

`hC` and `hAanti` are not needed by the proof and are kept only because the statement is
frozen. -/
private theorem sum_four_le_of_cut_bound {G : ℕ → ℕ → ℕ → ℕ → ℝ} {A : ℕ → ℝ} {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hA0 : ∀ m, 0 ≤ A m) (hA1 : ∀ m, A m ≤ 1) (hAanti : Antitone A)
    (hAK : ∀ m : ℕ, 1 ≤ m → A m ≤ K / (m : ℝ) ^ 2)
    (hG0 : ∀ a b c d, 0 ≤ G a b c d)
    (hGs1 : ∀ a b c d, G a b c d = G b a c d)
    (hGs2 : ∀ a b c d, G a b c d = G a c b d)
    (hGs3 : ∀ a b c d, G a b c d = G a b d c)
    (hcut : ∀ a b c d : ℕ, a ≤ b → b ≤ c → c ≤ d →
      G a b c d ≤ 4 * C ^ 4 * A (max (b - a) (max (c - b) (d - c)))
        + 16 * C ^ 4 * (A (b - a) * A (d - c))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range n,
        ∑ d ∈ Finset.range n, G a b c d ≤ D * (n : ℝ) ^ 2 := by
  classical
  have hC4 : (0 : ℝ) ≤ C ^ 4 := by positivity
  have hD0 : (0 : ℝ) ≤ 24 * (12 * C ^ 4 + 48 * C ^ 4 * K + 16 * C ^ 4 * (1 + 2 * K) ^ 2) := by
    nlinarith [sq_nonneg (1 + 2 * K)]
  refine ⟨_, hD0, fun n => ?_⟩
  obtain ⟨Gt, hGt⟩ : ∃ Gt : (Fin 4 → ℕ) → ℝ, ∀ f, Gt f = G (f 0) (f 1) (f 2) (f 3) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (Fin 4 → ℕ) → ℝ, ∀ v,
      B v = 4 * C ^ 4 * A (max (v 1) (max (v 2) (v 3))) + 16 * C ^ 4 * (A (v 1) * A (v 3)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin 4 → ℕ) → (Fin 4 → ℕ), ∀ u,
      ψ u = ![u 0, u 1 - u 0, u 2 - u 1, u 3 - u 2] := ⟨_, fun _ => rfl⟩
  set P : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => Finset.range n) with hP
  set Pm : Finset (Fin 4 → ℕ) :=
    P.filter (fun u => u 0 ≤ u 1 ∧ u 1 ≤ u 2 ∧ u 2 ≤ u 3) with hPmdef
  have hB0 : ∀ v, 0 ≤ B v := by
    intro v
    rw [hB]
    have t1 : (0 : ℝ) ≤ 4 * C ^ 4 * A (max (v 1) (max (v 2) (v 3))) :=
      mul_nonneg (by positivity) (hA0 _)
    have t2 : (0 : ℝ) ≤ 16 * C ^ 4 * (A (v 1) * A (v 3)) :=
      mul_nonneg (by positivity) (mul_nonneg (hA0 _) (hA0 _))
    linarith
  -- (a) the nested sum is a sum over the tuple family
  have hLHS : ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range n,
      ∑ d ∈ Finset.range n, G a b c d = ∑ f ∈ P, Gt f := by
    rw [hP, sum_piFinset_four]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [hGt]
    rfl
  -- (b) symmetrisation
  have hperm : ∀ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → ℕ), Gt (f ∘ σ) = Gt f := by
    refine tuple4_comp_perm_invariant ?_
    intro i j f
    rw [hGt, hGt]
    exact tuple4_swap_invariant hGs1 hGs2 hGs3 i j f
  have hPclosed : ∀ f ∈ P, ∀ σ : Equiv.Perm (Fin 4), f ∘ σ ∈ P := by
    intro f hf σ
    rw [hP, Fintype.mem_piFinset] at hf ⊢
    exact fun i => hf (σ i)
  have hsym := sum_tuple4_le_sorted (Gt := Gt) (fun f => by rw [hGt]; exact hG0 _ _ _ _)
    hperm P hPclosed
  rw [← hPmdef] at hsym
  -- (c) the cut bound, in gap coordinates
  have hcut' : ∀ u ∈ Pm, Gt u ≤ B (ψ u) := by
    intro u hu
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hu
    rw [hGt, hB, hψ]
    simpa using hcut (u 0) (u 1) (u 2) (u 3) h1 h2 h3
  -- (d) the gap map is injective on the sorted tuples and lands in the family
  have hψmem : ∀ u ∈ Pm, ψ u ∈ P := by
    intro u hu
    obtain ⟨huP, -⟩ := Finset.mem_filter.1 hu
    rw [hP, Fintype.mem_piFinset] at huP ⊢
    intro i
    rw [hψ]
    have h0 := huP 0
    have h1 := huP 1
    have h2 := huP 2
    have h3 := huP 3
    simp only [Finset.mem_range] at h0 h1 h2 h3 ⊢
    fin_cases i <;> simp <;> omega
  have hψinj : ∀ u ∈ Pm, ∀ u' ∈ Pm, ψ u = ψ u' → u = u' := by
    intro u hu u' hu' heq
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hu
    obtain ⟨-, h1', h2', h3'⟩ := Finset.mem_filter.1 hu'
    have e0 : u 0 = u' 0 := by
      have h := congrFun heq 0; rw [hψ, hψ] at h; exact h
    have e1 : u 1 - u 0 = u' 1 - u' 0 := by
      have h := congrFun heq 1; rw [hψ, hψ] at h; exact h
    have e2 : u 2 - u 1 = u' 2 - u' 1 := by
      have h := congrFun heq 2; rw [hψ, hψ] at h; exact h
    have e3 : u 3 - u 2 = u' 3 - u' 2 := by
      have h := congrFun heq 3; rw [hψ, hψ] at h; exact h
    have q0 : u 0 = u' 0 := by omega
    have q1 : u 1 = u' 1 := by omega
    have q2 : u 2 = u' 2 := by omega
    have q3 : u 3 = u' 3 := by omega
    funext i
    fin_cases i <;> assumption
  -- (e) assemble the chain
  have hstep : ∑ u ∈ Pm, Gt u ≤ ∑ v ∈ P, B v := by
    calc ∑ u ∈ Pm, Gt u ≤ ∑ u ∈ Pm, B (ψ u) := Finset.sum_le_sum hcut'
      _ = ∑ v ∈ Pm.image ψ, B v := (Finset.sum_image hψinj).symm
      _ ≤ ∑ v ∈ P, B v := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => hB0 v)
          intro v hv
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
          exact hψmem u hu
  -- (f) the gap sums
  have hBsum : ∑ v ∈ P, B v
      ≤ (n : ℝ) * (12 * C ^ 4 * (1 + 4 * K * (n : ℝ))
        + 16 * C ^ 4 * ((n : ℝ) * (1 + 2 * K) ^ 2)) := by
    rw [hP, sum_piFinset_four]
    have hin : ∀ a : ℕ, ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
        ∑ g3 ∈ Finset.range n, B ![a, g1, g2, g3]
        ≤ 12 * C ^ 4 * (1 + 4 * K * (n : ℝ))
          + 16 * C ^ 4 * ((n : ℝ) * (1 + 2 * K) ^ 2) := by
      intro a
      have hval : ∀ g1 g2 g3 : ℕ, B ![a, g1, g2, g3]
          = 4 * C ^ 4 * A (max g1 (max g2 g3)) + 16 * C ^ 4 * (A g1 * A g3) := by
        intro g1 g2 g3; rw [hB]; rfl
      calc ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
              B ![a, g1, g2, g3]
          = ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
              (4 * C ^ 4 * A (max g1 (max g2 g3)) + 16 * C ^ 4 * (A g1 * A g3)) :=
            Finset.sum_congr rfl fun g1 _ => Finset.sum_congr rfl fun g2 _ =>
              Finset.sum_congr rfl fun g3 _ => hval g1 g2 g3
        _ = 4 * C ^ 4 * (∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
                ∑ g3 ∈ Finset.range n, A (max g1 (max g2 g3)))
              + 16 * C ^ 4 * (∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
                ∑ g3 ∈ Finset.range n, A g1 * A g3) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ 12 * C ^ 4 * (1 + 4 * K * (n : ℝ))
              + 16 * C ^ 4 * ((n : ℝ) * (1 + 2 * K) ^ 2) := by
            have hm := sum_triple_max_le hK hA0 hA1 hAK n
            have hp := sum_triple_pair_le hK hA0 hA1 hAK n
            nlinarith
    calc ∑ a ∈ Finset.range n, ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
            ∑ g3 ∈ Finset.range n, B ![a, g1, g2, g3]
        ≤ ∑ _a ∈ Finset.range n, (12 * C ^ 4 * (1 + 4 * K * (n : ℝ))
            + 16 * C ^ 4 * ((n : ℝ) * (1 + 2 * K) ^ 2)) := Finset.sum_le_sum fun a _ => hin a
      _ = (n : ℝ) * (12 * C ^ 4 * (1 + 4 * K * (n : ℝ))
            + 16 * C ^ 4 * ((n : ℝ) * (1 + 2 * K) ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- (g) numerology
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : n ≤ n ^ 2 := Nat.le_self_pow (by norm_num) n
    exact_mod_cast this
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rw [hLHS]
  refine hsym.trans ?_
  have hchain := hstep.trans hBsum
  nlinarith [sq_nonneg (1 + 2 * K), hC4, hK, mul_nonneg hC4 hK]

end Moment4

/-- **FY Proposition 2.7(ii), `q = 4` instance** (the one the Bernstein-block CLT
consumes): a bounded zero-mean strictly stationary α-mixing process with
`α(n) ≤ K n⁻²` has `E S_n⁴ ≤ C n²`. -/
theorem moment4_partial_sum_le [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Prop 2.7(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY Prop 2.7
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {K : ℝ}
    -- USER-INPUT: α-decay of order n⁻²; FY Prop 2.7(ii) with q = 4
    (hα : ∀ n : ℕ, 1 ≤ n → alphaCoeff X μ n ≤ K / (n : ℝ) ^ 2) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℕ,
      ∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 4 ∂μ ≤ C' * (n : ℝ) ^ 2 := by
  classical
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hbdd 0).exists.choose_spec
  have hA0 : ∀ m, 0 ≤ alphaCoeff X μ m := alphaCoeff_nonneg' X
  have hA1 : ∀ m, alphaCoeff X μ m ≤ 1 := fun _ => alphaMixCoeff_le_one (mΩ := inferInstance)
  have hAanti : Antitone fun m : ℕ => alphaCoeff X μ m := alphaCoeff_antitone X
  have hK0 : 0 ≤ K := by
    have h1 := hα 1 le_rfl
    have h2 := hA0 1
    norm_num at h1
    linarith
  -- the kernel: the modulus of the four-fold moment
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ℕ → ℕ → ℝ, ∀ a b c d, G a b c d =
      |∫ ω, X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω * X ((c : ℤ) + 1) ω
        * X ((d : ℤ) + 1) ω ∂μ| := ⟨_, fun _ _ _ _ => rfl⟩
  have hGsymm : ∀ (a b c d a' b' c' d' : ℕ),
      (∀ ω, X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω * X ((c : ℤ) + 1) ω * X ((d : ℤ) + 1) ω
        = X ((a' : ℤ) + 1) ω * X ((b' : ℤ) + 1) ω * X ((c' : ℤ) + 1) ω * X ((d' : ℤ) + 1) ω)
      → G a b c d = G a' b' c' d' := by
    intro a b c d a' b' c' d' he
    rw [hG, hG]
    congr 1
    exact integral_congr_ae (ae_of_all _ he)
  -- the cut bound, transported from `abs_integral_quad_le`
  have hcut : ∀ a b c d : ℕ, a ≤ b → b ≤ c → c ≤ d →
      G a b c d ≤ 4 * C ^ 4 * alphaCoeff X μ (max (b - a) (max (c - b) (d - c)))
        + 16 * C ^ 4 * (alphaCoeff X μ (b - a) * alphaCoeff X μ (d - c)) := by
    intro a b c d hab hbc hcd
    have e1 : (((b : ℤ) + 1) - ((a : ℤ) + 1)).toNat = b - a := by omega
    have e2 : (((c : ℤ) + 1) - ((b : ℤ) + 1)).toNat = c - b := by omega
    have e3 : (((d : ℤ) + 1) - ((c : ℤ) + 1)).toNat = d - c := by omega
    have key := abs_integral_quad_le hstat hmeas hbdd hmean
      (a := (a : ℤ) + 1) (b := (b : ℤ) + 1) (c := (c : ℤ) + 1) (d := (d : ℤ) + 1)
      (by omega) (by omega) (by omega)
    rw [e1, e2, e3] at key
    rw [hG]
    exact key
  obtain ⟨D, hD0, hD⟩ := sum_four_le_of_cut_bound (G := G)
    (A := fun m : ℕ => alphaCoeff X μ m) (C := C) (K := K) hC0 hK0 hA0 hA1 hAanti
    (fun m hm => hα m hm) (fun a b c d => by rw [hG]; exact abs_nonneg _)
    (fun a b c d => hGsymm _ _ _ _ _ _ _ _ fun ω => by ring)
    (fun a b c d => hGsymm _ _ _ _ _ _ _ _ fun ω => by ring)
    (fun a b c d => hGsymm _ _ _ _ _ _ _ _ fun ω => by ring) hcut
  refine ⟨D, hD0, fun n => ?_⟩
  -- expand the fourth power of the partial sum and exchange with the integral
  have hint : ∀ a b c d : ℕ, Integrable (fun ω => X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω
      * X ((c : ℤ) + 1) ω * X ((d : ℤ) + 1) ω) μ := by
    intro a b c d
    refine integrable_of_bdd ((((hmeas _).mul (hmeas _)).mul (hmeas _)).mul (hmeas _))
      (B := C * C * C * C) ?_
    filter_upwards [hbdd ((a : ℤ) + 1), hbdd ((b : ℤ) + 1), hbdd ((c : ℤ) + 1),
      hbdd ((d : ℤ) + 1)] with ω f1 f2 f3 f4
    exact abs_mul_le_of_bdd (abs_mul_le_of_bdd (abs_mul_le_of_bdd f1 f2) f3) f4
  have hexp : (∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 4 ∂μ)
      = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range n,
          ∑ d ∈ Finset.range n, ∫ ω, X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω
            * X ((c : ℤ) + 1) ω * X ((d : ℤ) + 1) ω ∂μ := by
    rw [integral_congr_ae (ae_of_all _ fun ω =>
      sum_pow_four_expand (Finset.range n) fun t : ℕ => X ((t : ℤ) + 1) ω)]
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => integrable_finset_sum _ fun c _ =>
      integrable_finset_sum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact integral_finset_sum _ fun d _ => hint a b c d
  rw [hexp]
  refine le_trans ?_ (hD n)
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
  rw [hG]
  exact le_abs_self _

end Process

end StatLean.TimeSeries
