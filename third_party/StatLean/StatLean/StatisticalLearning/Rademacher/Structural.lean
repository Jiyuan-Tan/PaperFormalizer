module
public import StatLean.StatisticalLearning.Rademacher.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-!
# Structural properties of Rademacher complexity, and Massart's lemma

Scaling/translation invariance (SSBD Lemma 26.6), the sub-Gaussian sign-MGF
bound `(e^a + e^{−a})/2 ≤ e^{a²/2}` (SSBD Lemma A.6), and **Massart's lemma**
(SSBD Lemma 26.8): for a finite `A = {a₁,…,a_N} ⊆ ℝⁿ` with mean `ā`,
`R(A) ≤ max_{a∈A} ‖a − ā‖₂ · √(2 log N)/n`, plus the center-form consumer
shape `R(A) ≤ r √(2 log |A|)/n` when every `a ∈ A` lies in the `ℓ₂`-ball of
radius `r` around a fixed center.

**Reference.** SSBD §26.1 (Lemmas 26.6, 26.8), Appendix A (Lemma A.6).
Transcriptions: `notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** Everything here is finite real analysis — the sign
average is a finite sum, so Massart's proof is the book's verbatim:
log-sum-exp + Jensen + Lemma A.6 termwise + the optimization
`λ⋆ = √(2 log N / max ‖a‖²)`, with the WLOG-centering step made explicit via
`radComplexity_translate`. The Euclidean norm on `Fin n → ℝ` is spelled
`√(∑ᵢ (aᵢ − cᵢ)²)` (the ambient `pi` norm is the sup norm — deliberately
avoided). Classes are `Finset (Fin n → ℝ)` so `N = A.card`.
-/

open scoped BigOperators

namespace StatLean.StatisticalLearning

variable {n : ℕ}

/-! ### The sign-average toolkit

`signAvg` is a finite average over the `2ⁿ` sign patterns, so all of its
algebra is `Finset.sum` bookkeeping. The one nontrivial ingredient is the
global sign flip `σ ↦ −σ`, an involution of the index set, which kills the
average of every odd function — in particular of `ε ↦ ⟨ε, a₀⟩`.
-/

/-- The global sign flip as an involutive equivalence of sign patterns. -/
private def flipSigns (n : ℕ) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ i := !σ i
  invFun σ i := !σ i
  left_inv σ := by funext i; simp
  right_inv σ := by funext i; simp

private lemma signOf_flipSigns (σ : Fin n → Bool) :
    signOf (flipSigns n σ) = -signOf σ := by
  funext i
  simp only [signOf, flipSigns, Equiv.coe_fn_mk, Pi.neg_apply]
  by_cases h : σ i = true <;> simp [h]

/-- Averaging over the sign patterns is invariant under the global flip. -/
private lemma signAvg_comp_neg (n : ℕ) (g : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => g (-ε)) = signAvg n g := by
  unfold signAvg
  congr 1
  refine Fintype.sum_equiv (flipSigns n) _ _ fun σ => ?_
  rw [signOf_flipSigns]

/-- Composition form of `signAvg_comp_neg` (avoids a `rw` on a beta-redex). -/
private lemma signAvg_comp_neg' (n : ℕ) (F G : (Fin n → ℝ) → ℝ)
    (h : ∀ ε, F ε = G (-ε)) : signAvg n F = signAvg n G := by
  rw [show F = fun ε => G (-ε) from funext h]
  exact signAvg_comp_neg n G

private lemma signAvg_add (n : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => f ε + g ε) = signAvg n f + signAvg n g := by
  unfold signAvg
  rw [Finset.sum_add_distrib]
  ring

private lemma signAvg_const_mul (n : ℕ) (c : ℝ) (g : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => c * g ε) = c * signAvg n g := by
  unfold signAvg
  rw [← Finset.mul_sum]
  ring

private lemma signAvg_mono (n : ℕ) {f g : (Fin n → ℝ) → ℝ} (h : ∀ ε, f ε ≤ g ε) :
    signAvg n f ≤ signAvg n g := by
  unfold signAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h _) (by positivity)

private lemma signAvg_sum {ι : Type*} (n : ℕ) (s : Finset ι)
    (g : ι → (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => ∑ a ∈ s, g a ε) = ∑ a ∈ s, signAvg n (g a) := by
  simp only [signAvg, ← Finset.mul_sum]
  congr 1
  exact Finset.sum_comm

/-- The sign average of an odd function vanishes. -/
private lemma signAvg_odd (n : ℕ) {g : (Fin n → ℝ) → ℝ}
    (h : ∀ ε, g (-ε) = -g ε) : signAvg n g = 0 := by
  have h1 : signAvg n (fun ε => g (-ε)) = signAvg n g := signAvg_comp_neg n g
  have h2 : signAvg n (fun ε => g (-ε)) = signAvg n (fun ε => (-1 : ℝ) * g ε) := by
    congr 1
    funext ε
    rw [h ε]
    ring
  rw [h2, signAvg_const_mul] at h1
  linarith

/-- `E_σ ⟨σ, a₀⟩ = 0` — the finite-average reading of `E σᵢ = 0`. -/
private lemma signAvg_inner_eq_zero (n : ℕ) (a₀ : Fin n → ℝ) :
    signAvg n (fun ε => ∑ i, ε i * a₀ i) = 0 := by
  refine signAvg_odd n fun ε => ?_
  simp [Finset.sum_neg_distrib]

private lemma image_inner_neg (A : Set (Fin n → ℝ)) (ε : Fin n → ℝ) :
    (fun a => ∑ i, ε i * a i) '' ((fun a => -a) '' A)
      = (fun a => ∑ i, (-ε) i * a i) '' A := by
  rw [Set.image_image]
  congr 1
  funext a
  simp

/-- The negation-invariance content, proved ahead of `radComplexity_smul_le`
(which consumes it for negative scalars). -/
private lemma radComplexity_neg_aux (A : Set (Fin n → ℝ)) :
    radComplexity ((fun a => -a) '' A) = radComplexity A := by
  unfold radComplexity
  congr 1
  refine signAvg_comp_neg' n _ _ fun ε => ?_
  rw [image_inner_neg]

/-- The sup image of a finite class is a finite set, hence bounded above. -/
private lemma bddAbove_coe_finset (B : Finset (Fin n → ℝ)) (ε : Fin n → ℝ) :
    BddAbove ((fun a => ∑ i, ε i * a i) '' (↑B : Set (Fin n → ℝ))) :=
  (B.finite_toSet.image _).bddAbove

/-- On a finite class the `sSup` of the image is the attained `Finset.sup'`. -/
private lemma sSup_coe_finset_image (B : Finset (Fin n → ℝ)) (hne : B.Nonempty)
    (f : (Fin n → ℝ) → ℝ) : sSup (f '' (↑B : Set (Fin n → ℝ))) = B.sup' hne f :=
  (Finset.sup'_eq_csSup_image B hne f).symm

/-! ### Structural lemmas -/

/-- **Translation invariance** (SSBD Lemma 26.6, translation part):
`R(A + a₀) = R(A)` — the shift is killed by `E σᵢ = 0`. -/
theorem radComplexity_translate (A : Set (Fin n → ℝ)) (a₀ : Fin n → ℝ)
    -- LEAN-ONLY: nonempty class (both sides junk-`0` otherwise)
    (hne : A.Nonempty)
    -- LEAN-ONLY: bounded sups on the untranslated class (junk-safety; a
    -- `Finset` image satisfies it)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => a + a₀) '' A) = radComplexity A := by
  unfold radComplexity
  congr 1
  have key : (fun ε : Fin n → ℝ =>
        sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => a + a₀) '' A)))
      = fun ε : Fin n → ℝ =>
        sSup ((fun a => ∑ i, ε i * a i) '' A) + ∑ i, ε i * a₀ i := by
    funext ε
    have himg : (fun a => ∑ i, ε i * a i) '' ((fun a : Fin n → ℝ => a + a₀) '' A)
        = (fun t : ℝ => t + ∑ i, ε i * a₀ i) ''
            ((fun a => ∑ i, ε i * a i) '' A) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext a
      simp [mul_add, Finset.sum_add_distrib]
    rw [himg]
    have := (OrderIso.addRight (∑ i, ε i * a₀ i)).map_csSup'
      (hne.image (fun a => ∑ i, ε i * a i)) (hbdd ε)
    simpa using this.symm
  rw [key, signAvg_add, signAvg_inner_eq_zero, add_zero]

/-- Scaling by a nonnegative factor, the auxiliary half of
`radComplexity_smul_le`. -/
private lemma radComplexity_smul_le_of_nonneg (A : Set (Fin n → ℝ)) {c : ℝ}
    (hc : 0 ≤ c) (hne : A.Nonempty)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => c • a) '' A) ≤ c * radComplexity A := by
  have hstep : ∀ ε : Fin n → ℝ,
      sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => c • a) '' A))
        ≤ c * sSup ((fun a => ∑ i, ε i * a i) '' A) := by
    intro ε
    have himg : (fun a => ∑ i, ε i * a i) '' ((fun a : Fin n → ℝ => c • a) '' A)
        = (fun t : ℝ => c * t) '' ((fun a => ∑ i, ε i * a i) '' A) := by
      rw [Set.image_image, Set.image_image]
      congr 1
      funext a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp [smul_eq_mul]; ring
    rw [himg]
    refine csSup_le ((hne.image _).image _) ?_
    rintro x ⟨t, ht, rfl⟩
    exact mul_le_mul_of_nonneg_left (le_csSup (hbdd ε) ht) hc
  unfold radComplexity
  have h1 : signAvg n
        (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => c • a) '' A)))
      ≤ c * signAvg n (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' A)) := by
    rw [← signAvg_const_mul]
    exact signAvg_mono n hstep
  calc (n : ℝ)⁻¹ * signAvg n
        (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' ((fun a => c • a) '' A)))
      ≤ (n : ℝ)⁻¹ *
          (c * signAvg n (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' A))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c * ((n : ℝ)⁻¹ *
          signAvg n (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' A))) := by ring

/-- **Scaling** (SSBD Lemma 26.6, scaling part): `R(c • A) ≤ |c| R(A)`. -/
theorem radComplexity_smul_le (A : Set (Fin n → ℝ)) (c : ℝ)
    -- LEAN-ONLY: nonempty class (both sides junk-`0` otherwise)
    (hne : A.Nonempty)
    -- LEAN-ONLY: bounded sups (junk-safety)
    (hbdd : ∀ ε : Fin n → ℝ, BddAbove ((fun a => ∑ i, ε i * a i) '' A)) :
    radComplexity ((fun a => c • a) '' A) ≤ |c| * radComplexity A := by
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    exact radComplexity_smul_le_of_nonneg A hc hne hbdd
  · have hA' : ((fun a : Fin n → ℝ => c • a) '' A)
        = (fun a : Fin n → ℝ => |c| • a) '' ((fun a => -a) '' A) := by
      rw [Set.image_image]
      congr 1
      funext a
      funext i
      simp [abs_of_neg hc]
    rw [hA']
    have hne' : ((fun a : Fin n → ℝ => -a) '' A).Nonempty := hne.image _
    have hbdd' : ∀ ε : Fin n → ℝ,
        BddAbove ((fun a => ∑ i, ε i * a i) '' ((fun a : Fin n → ℝ => -a) '' A)) := by
      intro ε
      rw [image_inner_neg]
      exact hbdd (-ε)
    calc radComplexity ((fun a : Fin n → ℝ => |c| • a) '' ((fun a => -a) '' A))
        ≤ |c| * radComplexity ((fun a : Fin n → ℝ => -a) '' A) :=
          radComplexity_smul_le_of_nonneg _ (abs_nonneg c) hne' hbdd'
      _ = |c| * radComplexity A := by rw [radComplexity_neg_aux]

/-- **Negation invariance** (SSBD §26.1, the `σ ≍ −σ` symmetry):
`R(−A) = R(A)` — negating every vector is absorbed by the sign average. Used
for the two-sided (±family) union step of SSBD §28.1. -/
theorem radComplexity_neg (A : Set (Fin n → ℝ)) :
    radComplexity ((fun a => -a) '' A) = radComplexity A :=
  radComplexity_neg_aux A

/-- **SSBD Lemma A.6**: `(e^a + e^{−a})/2 ≤ e^{a²/2}` — the MGF of a
Rademacher sign is sub-Gaussian with variance proxy `1`. -/
theorem add_exp_neg_div_two_le_exp_sq (a : ℝ) :
    (Real.exp a + Real.exp (-a)) / 2 ≤ Real.exp (a ^ 2 / 2) := by
  have h := Real.cosh_le_exp_half_sq a
  rwa [Real.cosh_eq] at h

/-! ### Massart's lemma

The proof is the book's: exponentiate, use Jensen for the sign average,
bound the sup of exponentials by their sum, factor the resulting product over
coordinates, apply Lemma A.6 termwise, and optimize in `λ`.
-/

/-- The one-vector sign MGF: `E_σ e^{λ⟨σ,b⟩} ≤ e^{λ²r²/2}` whenever
`‖b‖₂ ≤ r` (SSBD Lemma 26.8's inner step, from Lemma A.6). -/
private lemma signAvg_exp_inner_le (n : ℕ) (lam : ℝ) (b : Fin n → ℝ) {r : ℝ}
    (hsq : ∑ i, b i ^ 2 ≤ r ^ 2) :
    signAvg n (fun ε => Real.exp (lam * ∑ i, ε i * b i))
      ≤ Real.exp (lam ^ 2 * r ^ 2 / 2) := by
  set g : Fin n → Bool → ℝ :=
    fun i x => Real.exp (lam * ((if x then (1 : ℝ) else -1) * b i)) with hg
  have hprod : ∀ σ : Fin n → Bool,
      Real.exp (lam * ∑ i, signOf σ i * b i) = ∏ i, g i (σ i) := by
    intro σ
    rw [Finset.mul_sum, Real.exp_sum]
    rfl
  have hswap : ∑ σ : Fin n → Bool, ∏ i, g i (σ i)
      = ∏ i, ∑ x : Bool, g i x := by
    rw [← Finset.sum_prod_piFinset, Fintype.piFinset_univ]
  have hfac : ∀ i : Fin n, ∑ x : Bool, g i x
      ≤ 2 * Real.exp ((lam * b i) ^ 2 / 2) := by
    intro i
    have ht : g i true = Real.exp (lam * b i) := by simp [hg]
    have hf : g i false = Real.exp (-(lam * b i)) := by
      have hif : ((if (false : Bool) = true then (1 : ℝ) else -1)) = -1 := by
        norm_num
      simp only [hg, hif]
      congr 1
      ring
    have h2 : ∑ x : Bool, g i x = Real.exp (lam * b i) + Real.exp (-(lam * b i)) := by
      rw [Fintype.sum_bool, ht, hf]
    rw [h2]
    have := add_exp_neg_div_two_le_exp_sq (lam * b i)
    linarith
  have hnn : ∀ i : Fin n, (0 : ℝ) ≤ ∑ x : Bool, g i x := fun i =>
    Finset.sum_nonneg fun x _ => (Real.exp_pos _).le
  have hbound : ∏ i, ∑ x : Bool, g i x
      ≤ 2 ^ n * Real.exp (lam ^ 2 * r ^ 2 / 2) := by
    calc ∏ i, ∑ x : Bool, g i x
        ≤ ∏ i : Fin n, (2 * Real.exp ((lam * b i) ^ 2 / 2)) :=
          Finset.prod_le_prod (fun i _ => hnn i) (fun i _ => hfac i)
      _ = 2 ^ n * Real.exp (∑ i, (lam * b i) ^ 2 / 2) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum]
          simp
      _ ≤ 2 ^ n * Real.exp (lam ^ 2 * r ^ 2 / 2) := by
          have hs : ∑ i, (lam * b i) ^ 2 / 2 ≤ lam ^ 2 * r ^ 2 / 2 := by
            have hrw : ∑ i, (lam * b i) ^ 2 / 2 = lam ^ 2 / 2 * ∑ i, b i ^ 2 := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [hrw]
            have hl : (0 : ℝ) ≤ lam ^ 2 / 2 := by positivity
            nlinarith [hsq]
          have := Real.exp_le_exp.mpr hs
          have h2n : (0 : ℝ) ≤ 2 ^ n := by positivity
          nlinarith
  unfold signAvg
  have hsum : ∑ σ : Fin n → Bool, Real.exp (lam * ∑ i, signOf σ i * b i)
      ≤ 2 ^ n * Real.exp (lam ^ 2 * r ^ 2 / 2) := by
    calc ∑ σ : Fin n → Bool, Real.exp (lam * ∑ i, signOf σ i * b i)
        = ∑ σ : Fin n → Bool, ∏ i, g i (σ i) :=
          Finset.sum_congr rfl fun σ _ => hprod σ
      _ = ∏ i, ∑ x : Bool, g i x := hswap
      _ ≤ 2 ^ n * Real.exp (lam ^ 2 * r ^ 2 / 2) := hbound
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  rw [inv_mul_le_iff₀ hpos]
  linarith

/-- Massart's lemma for a class centered at the origin — the form the
optimization in `λ` is carried out in. -/
private lemma massart_core (B : Finset (Fin n → ℝ)) (hne : B.Nonempty) {r : ℝ}
    (hr : ∀ b ∈ B, Real.sqrt (∑ i, b i ^ 2) ≤ r) :
    radComplexity (↑B : Set (Fin n → ℝ)) ≤
      r * Real.sqrt (2 * Real.log B.card) / n := by
  obtain ⟨b₁, hb₁⟩ := hne
  have hr0 : 0 ≤ r := le_trans (Real.sqrt_nonneg _) (hr b₁ hb₁)
  set S : (Fin n → ℝ) → ℝ :=
    fun ε => B.sup' ⟨b₁, hb₁⟩ (fun b => ∑ i, ε i * b i) with hSdef
  have hrad : radComplexity (↑B : Set (Fin n → ℝ)) = (n : ℝ)⁻¹ * signAvg n S := by
    unfold radComplexity
    congr 1
    congr 1
    funext ε
    exact sSup_coe_finset_image B ⟨b₁, hb₁⟩ _
  have key : signAvg n S ≤ r * Real.sqrt (2 * Real.log B.card) := by
    have hcard1 : 1 ≤ B.card := Finset.card_pos.mpr ⟨b₁, hb₁⟩
    rcases eq_or_lt_of_le hcard1 with hcard | hcard
    · -- a singleton class: the sign average of a linear functional vanishes
      have hc : B.card = 1 := hcard.symm
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hc
      have hS1 : S = fun ε => ∑ i, ε i * b i := by
        funext ε
        simp [hSdef, hb]
      rw [hS1, signAvg_inner_eq_zero, hc]
      simp
    · -- `N ≥ 2`: log-sum-exp with the optimal `λ = √(2 log N)/r`
      have hN2 : 2 ≤ B.card := hcard
      have hNR : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hN2
      set L : ℝ := Real.log B.card with hL
      have hLpos : 0 < L := Real.log_pos (by linarith)
      have hrpos : 0 < r := by
        rcases hr0.lt_or_eq with h | h
        · exact h
        · exfalso
          have hzero : ∀ b ∈ B, b = 0 := by
            intro b hb
            have h1 : Real.sqrt (∑ i, b i ^ 2) ≤ 0 := by rw [h]; exact hr b hb
            have h2 : Real.sqrt (∑ i, b i ^ 2) = 0 :=
              le_antisymm h1 (Real.sqrt_nonneg _)
            have h3 : ∑ i, b i ^ 2 = 0 := by
              have hnn : (0 : ℝ) ≤ ∑ i, b i ^ 2 :=
                Finset.sum_nonneg fun i _ => sq_nonneg _
              nlinarith [Real.sq_sqrt hnn]
            funext i
            have := (Finset.sum_eq_zero_iff_of_nonneg
              (fun i (_ : i ∈ Finset.univ) => sq_nonneg (b i))).mp h3 i
              (Finset.mem_univ i)
            simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
          have hsub : B ⊆ {0} := fun b hb => by simp [hzero b hb]
          have hle := Finset.card_le_card hsub
          simp at hle
          omega
      set lam : ℝ := Real.sqrt (2 * L) / r with hlam
      have hsqrtpos : 0 < Real.sqrt (2 * L) := Real.sqrt_pos.mpr (by linarith)
      have hlampos : 0 < lam := div_pos hsqrtpos hrpos
      have hsqsq : Real.sqrt (2 * L) * Real.sqrt (2 * L) = 2 * L :=
        Real.mul_self_sqrt (by linarith)
      have hlam2 : lam ^ 2 * r ^ 2 / 2 = L := by
        rw [hlam]
        field_simp
        nlinarith [hsqsq]
      -- Jensen for the finite uniform average
      have hjensen : Real.exp (lam * signAvg n S)
          ≤ signAvg n (fun ε => Real.exp (lam * S ε)) := by
        have hw : ∑ _σ : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹ = 1 := by
          simp [Finset.sum_const, Finset.card_univ]
        have hj := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin n → Bool)))
          (w := fun _ => ((2 : ℝ) ^ n)⁻¹)
          (p := fun σ => lam * S (signOf σ))
          (fun i _ => by positivity) hw (fun i _ => Set.mem_univ _)
        simp only [smul_eq_mul] at hj
        have hleft : ∑ σ : Fin n → Bool, ((2 : ℝ) ^ n)⁻¹ * (lam * S (signOf σ))
            = lam * signAvg n S := by
          unfold signAvg
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => by ring
        have hright : ∑ σ : Fin n → Bool,
            ((2 : ℝ) ^ n)⁻¹ * Real.exp (lam * S (signOf σ))
            = signAvg n (fun ε => Real.exp (lam * S ε)) := by
          unfold signAvg
          rw [Finset.mul_sum]
        rw [hleft, hright] at hj
        exact hj
      -- the sup of exponentials is at most their sum
      have hsup : ∀ ε : Fin n → ℝ, Real.exp (lam * S ε)
          ≤ ∑ b ∈ B, Real.exp (lam * ∑ i, ε i * b i) := by
        intro ε
        obtain ⟨b₀, hb₀, hEq⟩ :=
          Finset.exists_mem_eq_sup' (⟨b₁, hb₁⟩ : B.Nonempty) (fun b => ∑ i, ε i * b i)
        have hSe : S ε = ∑ i, ε i * b₀ i := hEq
        rw [hSe]
        exact Finset.single_le_sum (f := fun b => Real.exp (lam * ∑ i, ε i * b i))
          (fun b _ => (Real.exp_pos _).le) hb₀
      have hsq : ∀ b ∈ B, ∑ i, b i ^ 2 ≤ r ^ 2 := by
        intro b hb
        have hnn : (0 : ℝ) ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        nlinarith [Real.sq_sqrt hnn, hr b hb, Real.sqrt_nonneg (∑ i, b i ^ 2)]
      have hchain : Real.exp (lam * signAvg n S)
          ≤ (B.card : ℝ) * Real.exp (lam ^ 2 * r ^ 2 / 2) := by
        calc Real.exp (lam * signAvg n S)
            ≤ signAvg n (fun ε => Real.exp (lam * S ε)) := hjensen
          _ ≤ signAvg n (fun ε => ∑ b ∈ B, Real.exp (lam * ∑ i, ε i * b i)) :=
              signAvg_mono n hsup
          _ = ∑ b ∈ B, signAvg n (fun ε => Real.exp (lam * ∑ i, ε i * b i)) :=
              signAvg_sum n B _
          _ ≤ ∑ _b ∈ B, Real.exp (lam ^ 2 * r ^ 2 / 2) :=
              Finset.sum_le_sum fun b hb => signAvg_exp_inner_le n lam b (hsq b hb)
          _ = (B.card : ℝ) * Real.exp (lam ^ 2 * r ^ 2 / 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hlog : lam * signAvg n S ≤ L + lam ^ 2 * r ^ 2 / 2 := by
        have := Real.log_le_log (Real.exp_pos _) hchain
        rwa [Real.log_exp, Real.log_mul (by positivity) (Real.exp_ne_zero _),
          Real.log_exp] at this
      rw [hlam2] at hlog
      have hfin : signAvg n S ≤ 2 * L / lam := by
        rw [le_div_iff₀ hlampos]
        nlinarith [hlog]
      have heq : 2 * L / lam = r * Real.sqrt (2 * L) := by
        rw [hlam]
        field_simp
        nlinarith [hsqsq]
      rw [heq] at hfin
      exact hfin
  rw [hrad]
  calc (n : ℝ)⁻¹ * signAvg n S
      ≤ (n : ℝ)⁻¹ * (r * Real.sqrt (2 * Real.log B.card)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = r * Real.sqrt (2 * Real.log B.card) / n := by rw [div_eq_inv_mul]

/-- **Massart's lemma, center form** (SSBD Lemma 26.8 as consumed by §28.1):
if every `a ∈ A` lies in the Euclidean ball of radius `r` around a fixed
center `c`, then `R(A) ≤ r √(2 log |A|)/n`. -/
theorem radComplexity_le_of_dist_center_le (A : Finset (Fin n → ℝ))
    (c : Fin n → ℝ) {r : ℝ}
    -- USER-INPUT: nonempty finite class; SSBD Lemma 26.8
    (hne : A.Nonempty)
    -- USER-INPUT: Euclidean radius bound around the center; SSBD Lemma 26.8
    -- (with `c = ā` this is `max_{a} ‖a − ā‖ ≤ r`)
    (hr : ∀ a ∈ A, Real.sqrt (∑ i, (a i - c i) ^ 2) ≤ r) :
    radComplexity (↑A : Set (Fin n → ℝ)) ≤
      r * Real.sqrt (2 * Real.log A.card) / n := by
  classical
  -- center the class: `B = A − c`
  set B : Finset (Fin n → ℝ) := A.image (fun a => a - c) with hB
  have hinj : Function.Injective (fun a : Fin n → ℝ => a - c) := by
    intro x y hxy
    simpa using congrArg (fun z : Fin n → ℝ => z + c) hxy
  have hcard : B.card = A.card := Finset.card_image_of_injective A hinj
  have hneB : B.Nonempty := hne.image _
  have hrB : ∀ b ∈ B, Real.sqrt (∑ i, b i ^ 2) ≤ r := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    simpa using hr a ha
  have htr : radComplexity (↑A : Set (Fin n → ℝ))
      = radComplexity (↑B : Set (Fin n → ℝ)) := by
    have himg : (fun a : Fin n → ℝ => a + c) '' (↑B : Set (Fin n → ℝ))
        = (↑A : Set (Fin n → ℝ)) := by
      rw [hB, Finset.coe_image, Set.image_image]
      simp
    rw [← himg, radComplexity_translate _ c hneB (fun ε => bddAbove_coe_finset B ε)]
  rw [htr, ← hcard]
  exact massart_core B hneB hrB

/-- **Massart's lemma** (SSBD Lemma 26.8, book form): for finite
`A = {a₁,…,a_N}` with mean `ā = N⁻¹ ∑ a`,
`R(A) ≤ max_{a∈A} ‖a − ā‖₂ · √(2 log N)/n`. -/
theorem massart (A : Finset (Fin n → ℝ))
    -- USER-INPUT: nonempty finite class; SSBD Lemma 26.8
    (hne : A.Nonempty) :
    radComplexity (↑A : Set (Fin n → ℝ)) ≤
      (A.sup' hne fun a =>
          Real.sqrt (∑ i, (a i - (A.card : ℝ)⁻¹ * ∑ b ∈ A, b i) ^ 2)) *
        Real.sqrt (2 * Real.log A.card) / n := by
  refine radComplexity_le_of_dist_center_le A
    (fun i => (A.card : ℝ)⁻¹ * ∑ b ∈ A, b i) hne ?_
  intro a ha
  exact Finset.le_sup'
    (f := fun a : Fin n → ℝ =>
      Real.sqrt (∑ i, (a i - (A.card : ℝ)⁻¹ * ∑ b ∈ A, b i) ^ 2)) ha

end StatLean.StatisticalLearning
