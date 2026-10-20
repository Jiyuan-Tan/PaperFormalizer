module
public import StatLean.CausalInference.Randomized.Neyman

@[expose] public section

/-!
# Regression adjustment — the difference in means as a least-squares coefficient

Two classical algebraic facts about running regressions on experimental data.

1. **The unadjusted regression is the difference in means.** The ordinary least squares
   coefficient of `Z` in the fit of `Y` on `(1, Z)` is exactly `τ̂` — regression buys
   nothing by itself, it merely repackages the estimator.
2. **Covariate adjustment stays unbiased.** For fixed coefficients `β₁, β₀`, the adjusted
   estimator
   `τ̂(β₁,β₀) = (Ȳ₁ - β₁(X̄₁ - X̄)) - (Ȳ₀ - β₀(X̄₀ - X̄))`
   is still unbiased under complete randomization, because the arm covariate means are
   themselves unbiased for the population covariate mean.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). eq. (4.3) (§4.4, p. 49: the OLS coefficient of `Z`
in `Y ~ (1, Z)` equals `τ̂`; stated in the text, no theorem number); eqs. (6.2)–(6.3)
(§6.2: the adjusted family `τ̂(β₁,β₀)`, of which Lin's estimator is the member with
estimated coefficients). (`Ding eq. (4.3); eqs. (6.2)–(6.3)`.) Compare G. W. Imbens and
D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical Sciences*, Cambridge
University Press, 2015, ch. 7. (`IR ch. 7`.)

**Scope.** Ding's Proposition 6.2 — that Lin's estimator, with coefficients *estimated* by
the fully interacted OLS fit, is the coefficient of `Z` in the regression of `Y` on
`(1, Z, X, ZX)` — is **not** formalized: it is multivariate least-squares algebra whose
causal content (unbiasedness for any fixed coefficients, which is what makes adjustment
safe under randomization) is already captured by `adjEstimator_unbiased` below. Likewise
the asymptotic efficiency comparison between `τ̂` and Lin's estimator is out of scope for
this release.

**Proof formalization notes.** The OLS identity is proved directly from the two normal
equations for a binary regressor rather than by invoking a general OLS API: with `Z` binary
the design matrix has rank at most `2`, the normal equations read
`∑(Yᵢ - a - bZᵢ) = 0` and `∑Zᵢ(Yᵢ - a - bZᵢ) = 0`, and subtracting `n₁/n` times the first
from the second gives `b = Ȳ₁ - Ȳ₀` after dividing by `n₁n₀/n`. The characterization is
stated as "any `(a, b)` satisfying the normal equations has `b = τ̂`", which avoids
committing to an existence-and-uniqueness statement about the minimizer and is the form
Ding uses. Unbiasedness of the adjusted family follows from linearity of `Design.expect`
plus `completeDesign_expect_ind`.

**Bibliographic comments.** The cautionary analysis of regression adjustment in randomized
experiments is D. A. Freedman, "On regression adjustments to experimental data," *Adv. in
Appl. Math.* **40** (2008), 180–193; the repair is W. Lin, "Agnostic notes on regression
adjustments to experimental data: reexamining Freedman's critique," *Ann. Appl. Statist.*
**7** (2013), 295–318.
-/

namespace StatLean.CausalInference

variable {n n₁ n₀ : ℕ}

/-- The **normal equations** of the least-squares fit of the observed outcome on
`(1, Z)`: the residuals are orthogonal to the constant and to the regressor. -/
def IsOLSFit (S : ScienceTable n) (z : Assignment n) (a b : ℝ) : Prop :=
  (∑ i, (S.observed z i - a - b * ind (z i)) = 0)
  ∧ (∑ i, ind (z i) * (S.observed z i - a - b * ind (z i)) = 0)

/-! ### LEAN-ONLY private helpers

Elementary bookkeeping: the binary regressor is idempotent, sums over an arm are weighted
sums over all units, and `Design.expect` is linear. None of this carries mathematical
content beyond the definitions of `ind`, `armIdx` and `Design.expect`. -/

/-- A sum over the treated arm is a `Z`-weighted sum over all units. -/
private lemma sum_ind_eq (z : Assignment n) (v : Fin n → ℝ) :
    ∑ i, v i * ind (z i) = ∑ i ∈ armIdx z true, v i := by
  rw [armIdx, Finset.sum_filter]
  exact (Finset.sum_congr rfl fun i _ => by cases z i <;> simp [ind]).symm

/-- A sum over the control arm is a `(1 - Z)`-weighted sum over all units. -/
private lemma sum_one_sub_ind_eq (z : Assignment n) (v : Fin n → ℝ) :
    ∑ i, v i * (1 - ind (z i)) = ∑ i ∈ armIdx z false, v i := by
  rw [armIdx, Finset.sum_filter]
  exact (Finset.sum_congr rfl fun i _ => by cases z i <;> simp [ind]).symm

/-- The two arms partition the units. -/
private lemma card_arm_add_card_arm (z : Assignment n) :
    (armIdx z true).card + (armIdx z false).card = n := by
  have := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => z i = true)
  simpa [armIdx, Bool.not_eq_true] using this

/-- The two arms partition any sum over the units. -/
private lemma sum_arm_add_sum_arm (z : Assignment n) (v : Fin n → ℝ) :
    ∑ i ∈ armIdx z true, v i + ∑ i ∈ armIdx z false, v i = ∑ i, v i := by
  have := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin n)) (fun i => z i = true) v
  simpa [armIdx, Bool.not_eq_true] using this

/-- The number of treated units, as a real weighted sum. -/
private lemma sum_ind_eq_card (z : Assignment n) :
    ∑ i, ind (z i) = ((armIdx z true).card : ℝ) := by
  have := sum_ind_eq z (fun _ => 1)
  simpa using this

/-- `Design.expect` respects pointwise equality on the support. -/
private lemma expect_congr {D : Design n} {f g : Assignment n → ℝ}
    (h : ∀ z ∈ D.support, f z = g z) : D.expect f = D.expect g := by
  simp only [Design.expect, Finset.sum_congr rfl h]

/-- `Design.expect` of a constant. -/
private lemma expect_const (D : Design n) (c : ℝ) : D.expect (fun _ => c) = c := by
  have hc : ((D.support.card : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr D.support_nonempty).ne'
  simp only [Design.expect, Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- `Design.expect` pulls out scalars. -/
private lemma expect_const_mul (D : Design n) (c : ℝ) (f : Assignment n → ℝ) :
    D.expect (fun z => c * f z) = c * D.expect f := by
  simp only [Design.expect, ← Finset.mul_sum]
  ring

/-- `Design.expect` is additive. -/
private lemma expect_add (D : Design n) (f g : Assignment n → ℝ) :
    D.expect (fun z => f z + g z) = D.expect f + D.expect g := by
  simp only [Design.expect, Finset.sum_add_distrib]
  ring

/-- `Design.expect` is subtractive. -/
private lemma expect_sub (D : Design n) (f g : Assignment n → ℝ) :
    D.expect (fun z => f z - g z) = D.expect f - D.expect g := by
  simp only [Design.expect, Finset.sum_sub_distrib]
  ring

/-- `Design.expect` commutes with finite sums. -/
private lemma expect_sum (D : Design n) {ι : Type*} (s : Finset ι)
    (f : ι → Assignment n → ℝ) :
    D.expect (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, D.expect (f i) := by
  simp only [Design.expect]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- **The normal equations solved.** Both statements below are read off from this single
computation: the second normal equation gives `Ȳ₁ = a + b`, and subtracting it from the
first gives `Ȳ₀ = a`. -/
private lemma ols_key (S : ScienceTable n) {z : Assignment n} {a b : ℝ}
    (hfit : IsOLSFit S z a b)
    (h1 : 0 < (armIdx z true).card) (h0 : 0 < (armIdx z false).card) :
    a = armMean S z false ∧ b = diffInMeans S z := by
  obtain ⟨e1, e2⟩ := hfit
  set T := ((armIdx z true).card : ℝ) with hT
  set C := ((armIdx z false).card : ℝ) with hC
  set ST := ∑ i ∈ armIdx z true, S.observed z i with hST
  set SC := ∑ i ∈ armIdx z false, S.observed z i with hSC
  have hTpos : 0 < T := by rw [hT]; exact_mod_cast h1
  have hCpos : 0 < C := by rw [hC]; exact_mod_cast h0
  have hn : T + C = (n : ℝ) := by rw [hT, hC]; exact_mod_cast card_arm_add_card_arm z
  -- the first normal equation
  have E1 : ST + SC - (T + C) * a - b * T = 0 := by
    rw [hn]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1
    rw [sum_ind_eq_card z] at e1
    rw [hST, hSC, sum_arm_add_sum_arm z (S.observed z)]
    linarith [e1]
  -- the second normal equation
  have E2 : ST - a * T - b * T = 0 := by
    have hterm : ∀ i : Fin n, ind (z i) * (S.observed z i - a - b * ind (z i))
        = S.observed z i * ind (z i) - a * ind (z i) - b * ind (z i) := by
      intro i; cases z i <;> simp [ind]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_ind_eq_card z,
      sum_ind_eq z (S.observed z)] at e2
    rw [hST]
    linarith [e2]
  have ha : a = C⁻¹ * SC := by
    have key : SC = C * a := by linear_combination E1 - E2
    field_simp
    linarith [key]
  refine ⟨by rw [armMean, ← hC, ← hSC]; exact ha, ?_⟩
  rw [diffInMeans, armMean, armMean, ← hT, ← hC, ← hST, ← hSC, ← ha]
  have hb : b * T = ST - a * T := by linarith [E2]
  field_simp
  linarith [hb]

/-- **The OLS coefficient of the treatment is the difference in means** (Ding eq. (4.3)):
regressing the observed outcome on an intercept and the treatment indicator reproduces
`τ̂` exactly. -/
theorem olsCoeff_eq_diffInMeans (S : ScienceTable n) {z : Assignment n} {a b : ℝ}
    -- USER-INPUT: `(a, b)` solves the least-squares normal equations; Ding §4.4
    (hfit : IsOLSFit S z a b)
    -- USER-INPUT: both arms are nonempty, else the regressor is constant and `b` is not
    -- identified; Ding §4.4
    (h1 : 0 < (armIdx z true).card) (h0 : 0 < (armIdx z false).card) :
    b = diffInMeans S z := (ols_key S hfit h1 h0).2

/-- The intercept of the same fit is the control arm mean. -/
theorem olsIntercept_eq_armMean (S : ScienceTable n) {z : Assignment n} {a b : ℝ}
    (hfit : IsOLSFit S z a b)
    (h1 : 0 < (armIdx z true).card) (h0 : 0 < (armIdx z false).card) :
    a = armMean S z false := (ols_key S hfit h1 h0).1

/-- The **arm mean of a covariate** under an assignment. -/
noncomputable def armCovMean (x : Fin n → ℝ) (z : Assignment n) (arm : Bool) : ℝ :=
  ((armIdx z arm).card : ℝ)⁻¹ * ∑ i ∈ armIdx z arm, x i

/-- The treated-arm statement, with the size hypothesis named so that it can be reused
below (the public form elaborates its own `by omega` proof term). -/
private lemma armCovMean_true_unbiased (x : Fin n → ℝ) (hsum : n₁ + n₀ = n) (h1 : 0 < n₁)
    (_h0 : 0 < n₀) (hle : n₁ ≤ n) :
    (completeDesign n n₁ hle).expect (fun z => armCovMean x z true) = popMean x := by
  have hn1 : ((n₁ : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hn : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  have hpt : ∀ z ∈ (completeDesign n n₁ hle).support,
      armCovMean x z true = (n₁ : ℝ)⁻¹ * ∑ i, x i * ind (z i) := by
    intro z hz
    have hc : (armIdx z true).card = n₁ := card_armIdx_true hle hz
    rw [armCovMean, hc, sum_ind_eq z x]
  rw [expect_congr hpt, expect_const_mul, expect_sum]
  have hterm : ∀ i : Fin n, (completeDesign n n₁ hle).expect (fun z => x i * ind (z i))
      = x i * ((n₁ : ℝ) / (n : ℝ)) := by
    intro i
    rw [expect_const_mul, completeDesign_expect_ind hle i]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, popMean]
  field_simp

/-- The control-arm mirror of `armCovMean_true_unbiased`. -/
private lemma armCovMean_false_unbiased (x : Fin n → ℝ) (hsum : n₁ + n₀ = n) (h1 : 0 < n₁)
    (h0 : 0 < n₀) (hle : n₁ ≤ n) :
    (completeDesign n n₁ hle).expect (fun z => armCovMean x z false) = popMean x := by
  have hn0 : ((n₀ : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
  have hn : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  have hcast : (n₁ : ℝ) + (n₀ : ℝ) = (n : ℝ) := by exact_mod_cast hsum
  have hpt : ∀ z ∈ (completeDesign n n₁ hle).support,
      armCovMean x z false = (n₀ : ℝ)⁻¹ * ∑ i, x i * (1 - ind (z i)) := by
    intro z hz
    have hc : (armIdx z false).card = n₀ := by
      rw [card_armIdx_false hle hz]; omega
    rw [armCovMean, hc, sum_one_sub_ind_eq z x]
  rw [expect_congr hpt, expect_const_mul, expect_sum]
  have hterm : ∀ i : Fin n, (completeDesign n n₁ hle).expect (fun z => x i * (1 - ind (z i)))
      = x i * (1 - (n₁ : ℝ) / (n : ℝ)) := by
    intro i
    rw [expect_const_mul]
    have hsub : (completeDesign n n₁ hle).expect (fun z => (1 : ℝ) - ind (z i))
        = (completeDesign n n₁ hle).expect (fun _ => (1 : ℝ))
          - (completeDesign n n₁ hle).expect (fun z => ind (z i)) :=
      expect_sub _ (fun _ => (1 : ℝ)) (fun z => ind (z i))
    rw [hsub, expect_const, completeDesign_expect_ind hle i]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_mul, popMean]
  have hfac : 1 - (n₁ : ℝ) / (n : ℝ) = (n₀ : ℝ) / (n : ℝ) := by
    field_simp; linarith [hcast]
  rw [hfac]
  field_simp

/-- **The arm covariate mean is unbiased for the population covariate mean** under complete
randomization — the fact that makes covariate adjustment harmless. -/
theorem armCovMean_unbiased (x : Fin n → ℝ) (hsum : n₁ + n₀ = n) (h1 : 0 < n₁) (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (fun z => armCovMean x z true) = popMean x :=
  armCovMean_true_unbiased x hsum h1 h0 _

/-- The **covariate-adjusted estimator with fixed coefficients** (Ding eqs. (6.2)–(6.3)). -/
noncomputable def adjEstimator (S : ScienceTable n) (x : Fin n → ℝ) (β1 β0 : ℝ)
    (z : Assignment n) : ℝ :=
  (armMean S z true - β1 * (armCovMean x z true - popMean x))
  - (armMean S z false - β0 * (armCovMean x z false - popMean x))

/-- **Unbiasedness of covariate adjustment** (Ding §6.2): for any *fixed* adjustment
coefficients, the adjusted estimator remains unbiased under complete randomization. -/
theorem adjEstimator_unbiased (S : ScienceTable n) (x : Fin n → ℝ) (β1 β0 : ℝ)
    (hsum : n₁ + n₀ = n)
    -- USER-INPUT: both arms nonempty; Ding Definition 3.1
    (h1 : 0 < n₁) (h0 : 0 < n₀) :
    (completeDesign n n₁ (by omega)).expect (adjEstimator S x β1 β0) = S.finiteATE := by
  have key : ∀ hle : n₁ ≤ n,
      (completeDesign n n₁ hle).expect (adjEstimator S x β1 β0) = S.finiteATE := by
    intro hle
    set D := completeDesign n n₁ hle with hD
    have hrw : adjEstimator S x β1 β0
        = fun z => (diffInMeans S z - β1 * (armCovMean x z true - popMean x))
            + β0 * (armCovMean x z false - popMean x) := by
      funext z; simp only [adjEstimator, diffInMeans]; ring
    rw [hrw]
    have hadd : D.expect (fun z => (diffInMeans S z - β1 * (armCovMean x z true - popMean x))
          + β0 * (armCovMean x z false - popMean x))
        = D.expect (fun z => diffInMeans S z - β1 * (armCovMean x z true - popMean x))
          + D.expect (fun z => β0 * (armCovMean x z false - popMean x)) :=
      expect_add D _ _
    have hsub : D.expect (fun z => diffInMeans S z - β1 * (armCovMean x z true - popMean x))
        = D.expect (fun z => diffInMeans S z)
          - D.expect (fun z => β1 * (armCovMean x z true - popMean x)) :=
      expect_sub D _ _
    have hA : D.expect (fun z => diffInMeans S z) = S.finiteATE :=
      differenceInMeans_unbiased S hsum h1 h0
    have hc1 : D.expect (fun z => β1 * (armCovMean x z true - popMean x)) = 0 := by
      rw [expect_const_mul D β1 (fun z => armCovMean x z true - popMean x)]
      have hd : D.expect (fun z => armCovMean x z true - popMean x)
          = D.expect (fun z => armCovMean x z true) - D.expect (fun _ => popMean x) :=
        expect_sub D _ _
      rw [hd, expect_const, hD, armCovMean_true_unbiased x hsum h1 h0 hle, sub_self, mul_zero]
    have hc0 : D.expect (fun z => β0 * (armCovMean x z false - popMean x)) = 0 := by
      rw [expect_const_mul D β0 (fun z => armCovMean x z false - popMean x)]
      have hd : D.expect (fun z => armCovMean x z false - popMean x)
          = D.expect (fun z => armCovMean x z false) - D.expect (fun _ => popMean x) :=
        expect_sub D _ _
      rw [hd, expect_const, hD, armCovMean_false_unbiased x hsum h1 h0 hle, sub_self, mul_zero]
    rw [hadd, hsub, hA, hc1, hc0, sub_zero, add_zero]
  exact key _

/-- With zero adjustment coefficients the adjusted estimator is the difference in means. -/
theorem adjEstimator_zero (S : ScienceTable n) (x : Fin n → ℝ) (z : Assignment n) :
    adjEstimator S x 0 0 z = diffInMeans S z := by
  simp only [adjEstimator, diffInMeans, zero_mul, sub_zero]

end StatLean.CausalInference
