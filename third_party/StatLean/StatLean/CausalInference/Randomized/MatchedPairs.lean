module
public import StatLean.CausalInference.Core.FiniteDefs
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The matched-pair experiment — unbiasedness, exact variance, conservativeness

In a matched-pair design the `2m` units are grouped into `m` pairs matched on covariates,
and within each pair an independent fair coin decides which unit is treated. Writing `D_j`
for the treated-minus-control observed difference in pair `j`, the estimator is
`τ̂ = m⁻¹∑_j D_j`, and

$$\mathbb E[\hat\tau]=\tau,\qquad
  \operatorname{Var}(\hat\tau)=\frac1{m^2}\sum_j\operatorname{Var}(D_j),\qquad
  \mathbb E[\hat V]-\operatorname{Var}(\hat\tau)=\frac{\sum_j(\tau_j-\tau)^2}{m(m-1)}\ \ge 0,$$

where `V̂ = {m(m-1)}⁻¹∑_j(D_j - τ̂)²`. As with Neyman's estimator, the variance estimator
is conservative, with equality exactly under a constant pair-level effect.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 7.1 with eq. (7.1) (§7.1, p. 100: the
matched-pair experiment); §7.3 (p. 103: unbiasedness, stated in the running text; the exact
variance is Problem 7.1); **Theorem 7.1** (§7.3, p. 104: `E[V̂] - Var(τ̂) =
{m(m-1)}⁻¹∑(τ_j - τ)² ≥ 0`, with equality iff the pair effects are constant), where
`V̂` is eq. (7.2). (`Ding Definition 7.1; §7.3; Theorem 7.1`.) Pairwise randomized
experiments are ch. 10 of G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics,
Social, and Biomedical Sciences*, Cambridge University Press, 2015. (`IR ch. 10`.)

**Scope and design choice.** A matched-pair assignment is *exactly* a choice, for each
pair, of which of its two members is treated — i.e. a `Bool` per pair. This file therefore
uses its own small data model (`PairedTable`, `pairExpect`) indexed by `Fin m → Bool`
rather than embedding into `Assignment (2m)`: the coin-flip structure is then manifest, the
pair differences are independent by construction, and every result is an elementary
computation. The embedding into a general `Design (2*m)` adds nothing mathematically and
is omitted.

**Proof formalization notes.** `pairExpect f = (2^m)⁻¹ ∑_{c : Fin m → Bool} f c` is the
uniform average over coin-flip patterns. The engine is `pairExpect_apply_single`: for a
function of one coordinate, the average is the two-point average
`(f true + f false)/2`, proved by summing over `Fin m → Bool` fiberwise in coordinate `j`.
Independence across pairs enters only through `pairExpect_mul_of_ne` (the average of a
product of functions of *different* coordinates factorizes), which is the same fiberwise
computation applied twice.

**Bibliographic comments.** The design and its analysis are classical; the conservativeness
of the paired variance estimator and its exactness under constant pair effects are in
D. B. Rubin, "Comment: Neyman (1923) and causal inference in experiments and observational
studies," *Statist. Sci.* **5** (1990), 472–480, and in the reference above.
-/

namespace StatLean.CausalInference

variable {m : ℕ}

/-- The **science table of a matched-pair experiment**: for each pair and each of its two
members, the two potential outcomes. The `Bool` indexes the member within the pair. -/
structure PairedTable (m : ℕ) where
  /-- Constitutive (Ding §7.1): the treated potential outcome of each member of each pair. -/
  y1 : Fin m → Bool → ℝ
  /-- Constitutive (Ding §7.1): the control potential outcome of each member of each pair. -/
  y0 : Fin m → Bool → ℝ

namespace PairedTable

/-- The individual causal effect of a member of a pair. -/
def unitEffect (P : PairedTable m) (j : Fin m) (b : Bool) : ℝ := P.y1 j b - P.y0 j b

/-- The **pair-level average causal effect** `τ_j`: the average of the two members'
individual effects (Ding §7.3). -/
noncomputable def pairEffect (P : PairedTable m) (j : Fin m) : ℝ :=
  (P.unitEffect j true + P.unitEffect j false) / 2

/-- The **average causal effect** of the matched-pair population. -/
noncomputable def ate (P : PairedTable m) : ℝ := (m : ℝ)⁻¹ * ∑ j, P.pairEffect j

/-- The **observed treated-minus-control difference in pair `j`** under the coin-flip
pattern `c`: if `c j = true` the first member is treated, otherwise the second. -/
def pairDiff (P : PairedTable m) (c : Fin m → Bool) (j : Fin m) : ℝ :=
  if c j then P.y1 j true - P.y0 j false else P.y1 j false - P.y0 j true

/-- The **matched-pair estimator** `τ̂ = m⁻¹∑_j D_j` (Ding §7.3). -/
noncomputable def pairEstimator (P : PairedTable m) (c : Fin m → Bool) : ℝ :=
  (m : ℝ)⁻¹ * ∑ j, P.pairDiff c j

/-- The **paired variance estimator** `V̂ = {m(m-1)}⁻¹∑_j(D_j - τ̂)²` (Ding eq. (7.2)). -/
noncomputable def pairVarEst (P : PairedTable m) (c : Fin m → Bool) : ℝ :=
  ((m : ℝ) * ((m : ℝ) - 1))⁻¹ * ∑ j, (P.pairDiff c j - P.pairEstimator c) ^ 2

end PairedTable

/-- The **uniform average over coin-flip patterns**: the expectation under the matched-pair
design, in which each pair is independently randomized by a fair coin
(Ding Definition 7.1). -/
noncomputable def pairExpect (f : (Fin m → Bool) → ℝ) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * ∑ c : Fin m → Bool, f c

/-- The **variance** under the matched-pair design. -/
noncomputable def pairVar (f : (Fin m → Bool) → ℝ) : ℝ :=
  pairExpect fun c => (f c - pairExpect f) ^ 2

section CoordinateSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Summing a function of the `j`-th coordinate over all `Bool`-valued patterns: split the
pattern into its `j`-th entry and the rest (`Equiv.funSplitAt`). -/
private lemma sum_coord (j : ι) (g : Bool → ℝ) :
    ∑ c : ι → Bool, g (c j)
      = (Fintype.card ({i : ι // i ≠ j} → Bool) : ℝ) * (g true + g false) := by
  have hsplit :
      (∑ c : ι → Bool, g (c j))
        = ∑ p : Bool × ({i : ι // i ≠ j} → Bool), g p.1 :=
    Equiv.sum_comp (Equiv.funSplitAt j Bool)
      (fun p : Bool × ({i : ι // i ≠ j} → Bool) => g p.1)
  rw [hsplit]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.sum_bool]
  ring

/-- The number of `Bool`-valued patterns on `ι` is twice the number on `ι` minus one point. -/
private lemma card_fun_bool_split (j : ι) :
    (Fintype.card (ι → Bool) : ℝ) = 2 * (Fintype.card ({i : ι // i ≠ j} → Bool) : ℝ) := by
  have h := sum_coord j (fun _ => (1 : ℝ))
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [h]; ring

private lemma card_sub_ne_zero (j : ι) :
    (Fintype.card ({i : ι // i ≠ j} → Bool) : ℝ) ≠ 0 := by
  have : 0 < Fintype.card ({i : ι // i ≠ j} → Bool) := Fintype.card_pos
  exact_mod_cast this.ne'

/-- The uniform average of a function of one coordinate is the two-point average. -/
private lemma avg_coord (j : ι) (g : Bool → ℝ) :
    (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ c : ι → Bool, g (c j) = (g true + g false) / 2 := by
  have hA := card_sub_ne_zero j
  rw [sum_coord j g, card_fun_bool_split j]
  field_simp

end CoordinateSplit

private lemma card_fun_bool_fin (m : ℕ) : (Fintype.card (Fin m → Bool) : ℝ) = (2 : ℝ) ^ m := by
  simp

/-- The design average of a function of a single coordinate is the two-point average — the
fair-coin property. -/
theorem pairExpect_single (j : Fin m) (g : Bool → ℝ) :
    pairExpect (fun c => g (c j)) = (g true + g false) / 2 := by
  unfold pairExpect
  rw [← card_fun_bool_fin m, avg_coord j g]

/-- The design average of a product of functions of *distinct* coordinates factorizes:
pairs are independently randomized. -/
theorem pairExpect_mul_of_ne {j k : Fin m} (hjk : j ≠ k) (g h : Bool → ℝ) :
    pairExpect (fun c => g (c j) * h (c k))
      = pairExpect (fun c => g (c j)) * pairExpect (fun c => h (c k)) := by
  have hsplit :
      (∑ c : Fin m → Bool, g (c j) * h (c k))
        = ∑ p : Bool × ({i : Fin m // i ≠ j} → Bool),
            g p.1 * h (p.2 (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j})) :=
    Equiv.sum_comp (Equiv.funSplitAt j Bool)
      (fun p : Bool × ({i : Fin m // i ≠ j} → Bool) =>
        g p.1 * h (p.2 (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j})))
  have hinner : ∀ b : Bool,
      (∑ r : ({i : Fin m // i ≠ j} → Bool), g b * h (r (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j})))
        = g b * ((Fintype.card
              ({i' : {i : Fin m // i ≠ j} // i' ≠ (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j})} → Bool)
              : ℝ) * (h true + h false)) := by
    intro b
    rw [← Finset.mul_sum, sum_coord (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j}) h]
  have hA' : (Fintype.card
      ({i' : {i : Fin m // i ≠ j} // i' ≠ (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j})} → Bool) : ℝ)
        ≠ 0 := card_sub_ne_zero _
  have h2m : (2 : ℝ) ^ m = 4 * (Fintype.card
      ({i' : {i : Fin m // i ≠ j} // i' ≠ (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j})} → Bool) : ℝ) := by
    rw [← card_fun_bool_fin m, card_fun_bool_split (ι := Fin m) j,
      card_fun_bool_split (ι := {i : Fin m // i ≠ j}) (⟨k, hjk.symm⟩ : {i : Fin m // i ≠ j})]
    ring
  conv_rhs => rw [pairExpect_single, pairExpect_single]
  unfold pairExpect
  rw [hsplit]
  simp only [Fintype.sum_prod_type, hinner, Fintype.sum_bool]
  rw [h2m]
  field_simp
  ring

/-- `pairExpect` is linear on finite sums. -/
theorem pairExpect_sum {K : Type*} [Fintype K] (F : K → (Fin m → Bool) → ℝ) :
    pairExpect (fun c => ∑ k, F k c) = ∑ k, pairExpect (F k) := by
  unfold pairExpect
  rw [Finset.sum_comm, Finset.mul_sum]

/-- `pairExpect` commutes with scalar multiples. -/
private lemma pairExpect_const_mul (a : ℝ) (f : (Fin m → Bool) → ℝ) :
    pairExpect (fun c => a * f c) = a * pairExpect f := by
  unfold pairExpect
  rw [← Finset.mul_sum]
  ring

/-- `pairExpect` is additive. -/
private lemma pairExpect_add (f g : (Fin m → Bool) → ℝ) :
    pairExpect (fun c => f c + g c) = pairExpect f + pairExpect g := by
  unfold pairExpect
  rw [Finset.sum_add_distrib]
  ring

/-- `pairExpect` is subtractive. -/
private lemma pairExpect_sub (f g : (Fin m → Bool) → ℝ) :
    pairExpect (fun c => f c - g c) = pairExpect f - pairExpect g := by
  unfold pairExpect
  rw [Finset.sum_sub_distrib]
  ring

/-- `pairExpect` of a constant. -/
private lemma pairExpect_const (a : ℝ) : pairExpect (fun _ : Fin m → Bool => a) = a := by
  unfold pairExpect
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_fun_bool_fin]
  have h2 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  field_simp

/-- **The expected pair difference is the pair effect** (Ding §7.3): each pair's observed
difference is unbiased for that pair's average causal effect. -/
theorem pairExpect_pairDiff (P : PairedTable m) (j : Fin m) :
    pairExpect (fun c => P.pairDiff c j) = P.pairEffect j := by
  have key : pairExpect (fun c => P.pairDiff c j)
      = ((P.y1 j true - P.y0 j false) + (P.y1 j false - P.y0 j true)) / 2 :=
    pairExpect_single j
      (fun b : Bool => if b then P.y1 j true - P.y0 j false else P.y1 j false - P.y0 j true)
  rw [key]
  unfold PairedTable.pairEffect PairedTable.unitEffect
  ring

/-- **Unbiasedness of the matched-pair estimator** (Ding §7.3, p. 103). -/
theorem pairEstimator_unbiased (P : PairedTable m) :
    pairExpect P.pairEstimator = P.ate := by
  have hfun : P.pairEstimator
      = fun c : Fin m → Bool => (m : ℝ)⁻¹ * ∑ j, P.pairDiff c j := rfl
  rw [hfun, pairExpect_const_mul, pairExpect_sum]
  simp only [pairExpect_pairDiff]
  rfl

/-- The centred pair difference has design mean zero. -/
private lemma pairExpect_centred (P : PairedTable m) (j : Fin m) :
    pairExpect (fun c => P.pairDiff c j - P.pairEffect j) = 0 := by
  have key : pairExpect (fun c => P.pairDiff c j - P.pairEffect j)
      = (((P.y1 j true - P.y0 j false) - P.pairEffect j)
          + ((P.y1 j false - P.y0 j true) - P.pairEffect j)) / 2 :=
    pairExpect_single j (fun b : Bool =>
      (if b then P.y1 j true - P.y0 j false else P.y1 j false - P.y0 j true) - P.pairEffect j)
  rw [key]
  unfold PairedTable.pairEffect PairedTable.unitEffect
  ring

/-- Centred pair differences from *distinct* pairs are uncorrelated. -/
private lemma pairExpect_centred_mul_eq_zero (P : PairedTable m) {j k : Fin m} (hjk : j ≠ k) :
    pairExpect (fun c => (P.pairDiff c j - P.pairEffect j) * (P.pairDiff c k - P.pairEffect k))
      = 0 := by
  have key : pairExpect
        (fun c => (P.pairDiff c j - P.pairEffect j) * (P.pairDiff c k - P.pairEffect k))
      = pairExpect (fun c => P.pairDiff c j - P.pairEffect j)
        * pairExpect (fun c => P.pairDiff c k - P.pairEffect k) :=
    pairExpect_mul_of_ne hjk
      (fun b : Bool =>
        (if b then P.y1 j true - P.y0 j false else P.y1 j false - P.y0 j true) - P.pairEffect j)
      (fun b : Bool =>
        (if b then P.y1 k true - P.y0 k false else P.y1 k false - P.y0 k true) - P.pairEffect k)
  rw [key, pairExpect_centred, zero_mul]

/-- **Exact variance of the matched-pair estimator** (Ding, Problem 7.1): the pair
differences are independent, so the variance is the average of the per-pair variances,
each of which is the squared half-difference of the two members' effects. -/
theorem pairEstimator_variance (P : PairedTable m) :
    pairVar P.pairEstimator
      = ((m : ℝ) ^ 2)⁻¹ * ∑ j, pairVar (fun c => P.pairDiff c j) := by
  have hstep : ∀ c : Fin m → Bool,
      (P.pairEstimator c - pairExpect P.pairEstimator) ^ 2
        = ((m : ℝ) ^ 2)⁻¹ * ∑ j, ∑ k,
            (P.pairDiff c j - P.pairEffect j) * (P.pairDiff c k - P.pairEffect k) := by
    intro c
    rw [pairEstimator_unbiased]
    have hd : P.pairEstimator c - P.ate
        = (m : ℝ)⁻¹ * ∑ j, (P.pairDiff c j - P.pairEffect j) := by
      unfold PairedTable.pairEstimator PairedTable.ate
      rw [Finset.sum_sub_distrib]
      ring
    rw [hd, ← Finset.sum_mul_sum]
    ring
  unfold pairVar
  simp only [hstep]
  rw [pairExpect_const_mul]
  congr 1
  rw [pairExpect_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [pairExpect_sum, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
    (fun k _ hk => pairExpect_centred_mul_eq_zero P (Ne.symm hk))]
  rw [pairExpect_pairDiff]
  congr 1
  funext c
  ring

/-- Expansion of a sum of squared deviations about an arbitrary centre. -/
private lemma sum_sq_shift (D : Fin m → ℝ) (a : ℝ) :
    ∑ j, (D j - a) ^ 2 = (∑ j, (D j) ^ 2) - 2 * a * (∑ j, D j) + (m : ℝ) * a ^ 2 := by
  have hexp : ∀ j : Fin m, (D j - a) ^ 2 = (D j) ^ 2 - 2 * a * D j + a ^ 2 := by
    intro j; ring
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hexp j), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **Theorem 7.1** (Ding §7.3, p. 104): the paired variance estimator overestimates the
true variance by exactly the dispersion of the pair effects. -/
theorem pairVarEst_bias (P : PairedTable m)
    -- USER-INPUT: at least two pairs, so that `V̂` is defined; Ding eq. (7.2)
    (hm : 2 ≤ m) :
    pairExpect P.pairVarEst - pairVar P.pairEstimator
      = ((m : ℝ) * ((m : ℝ) - 1))⁻¹ * ∑ j, (P.pairEffect j - P.ate) ^ 2 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hm1 : (m : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  -- The bias–variance regrouping of the observed sum of squares, pointwise in `c`.
  have hid : ∀ c : Fin m → Bool,
      (∑ j, (P.pairDiff c j - P.pairEstimator c) ^ 2)
        = (∑ j, (P.pairDiff c j - P.ate) ^ 2)
          - (m : ℝ) * (P.pairEstimator c - P.ate) ^ 2 := by
    intro c
    have hsum : ∑ j, P.pairDiff c j = (m : ℝ) * P.pairEstimator c := by
      unfold PairedTable.pairEstimator
      field_simp
    rw [sum_sq_shift, sum_sq_shift, hsum]
    ring
  -- `τ̂` is centred at `τ`, so its mean square deviation from `τ` is its variance.
  have hpv : pairExpect (fun c => (P.pairEstimator c - P.ate) ^ 2)
      = pairVar P.pairEstimator := by
    unfold pairVar
    rw [pairEstimator_unbiased]
  have hVE : pairExpect P.pairVarEst
      = ((m : ℝ) * ((m : ℝ) - 1))⁻¹
        * ((∑ j, pairExpect (fun c => (P.pairDiff c j - P.ate) ^ 2))
            - (m : ℝ) * pairVar P.pairEstimator) := by
    have hfun : P.pairVarEst
        = fun c : Fin m → Bool => ((m : ℝ) * ((m : ℝ) - 1))⁻¹
            * ((∑ j, (P.pairDiff c j - P.ate) ^ 2)
              - (m : ℝ) * (P.pairEstimator c - P.ate) ^ 2) := by
      funext c
      unfold PairedTable.pairVarEst
      rw [hid c]
    rw [hfun, pairExpect_const_mul, pairExpect_sub, pairExpect_sum, pairExpect_const_mul, hpv]
  -- Each pair contributes its own variance plus the squared deviation of its effect.
  have hj : ∀ j : Fin m, pairExpect (fun c => (P.pairDiff c j - P.ate) ^ 2)
      = pairVar (fun c => P.pairDiff c j) + (P.pairEffect j - P.ate) ^ 2 := by
    intro j
    have hexp : (fun c : Fin m → Bool => (P.pairDiff c j - P.ate) ^ 2)
        = fun c : Fin m → Bool =>
            ((P.pairDiff c j - P.pairEffect j) ^ 2
              + (2 * (P.pairEffect j - P.ate)) * (P.pairDiff c j - P.pairEffect j))
            + (P.pairEffect j - P.ate) ^ 2 := by
      funext c; ring
    rw [hexp, pairExpect_add, pairExpect_add, pairExpect_const, pairExpect_const_mul,
      pairExpect_centred, mul_zero, add_zero]
    congr 1
    unfold pairVar
    rw [pairExpect_pairDiff]
  rw [hVE, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hj j), Finset.sum_add_distrib,
    pairEstimator_variance]
  field_simp
  ring

/-- **Conservativeness** (Ding Theorem 7.1): the paired variance estimator is unbiased
upward. -/
theorem pairVarEst_conservative (P : PairedTable m) (hm : 2 ≤ m) :
    pairVar P.pairEstimator ≤ pairExpect P.pairVarEst := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hbias := pairVarEst_bias P hm
  have hnn : 0 ≤ ((m : ℝ) * ((m : ℝ) - 1))⁻¹ * ∑ j, (P.pairEffect j - P.ate) ^ 2 := by
    refine mul_nonneg (le_of_lt (inv_pos.mpr ?_)) (Finset.sum_nonneg fun j _ => sq_nonneg _)
    nlinarith
  linarith

/-- **Exactness under constant pair effects** (Ding Theorem 7.1): the bias vanishes exactly
when all pair-level effects agree. -/
theorem pairVarEst_unbiased_of_constant (P : PairedTable m) {τ : ℝ}
    -- USER-INPUT: constant pair-level effects; Ding Theorem 7.1
    (hconst : ∀ j, P.pairEffect j = τ) (hm : 2 ≤ m) :
    pairExpect P.pairVarEst = pairVar P.pairEstimator := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hate : P.ate = τ := by
    unfold PairedTable.ate
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hconst j), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hzero : ∑ j, (P.pairEffect j - P.ate) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hconst j, hate, sub_self]
    ring
  have hbias := pairVarEst_bias P hm
  rw [hzero, mul_zero] at hbias
  linarith

end StatLean.CausalInference
