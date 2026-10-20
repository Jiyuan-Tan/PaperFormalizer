module
public import StatLean.StatisticalLearning.Rademacher.Defs
public import StatLean.StatisticalLearning.Rademacher.Structural

@[expose] public section

/-!
# The contraction lemma for Rademacher complexity

SSBD Lemma 26.9 (Kakade–Tewari form of Talagrand's contraction): applying a
`ρ`-Lipschitz function `φᵢ` to each coordinate does not increase the
Rademacher complexity by more than the factor `ρ`:
`R(φ ∘ A) ≤ ρ R(A)`.

**Reference.** SSBD §26.1, Lemma 26.9. Transcription:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** This is **not** the coefficient contraction already in
`ConcentrationInequalities/Symmetrization/Contraction.lean` (HDP Thm 6.6.1,
`E‖∑ aᵢεᵢxᵢ‖ ≤ E‖∑ εᵢxᵢ‖`) — the SSBD lemma contracts a *Lipschitz
composition inside a sup* and is proved coordinate-by-coordinate: condition on
the signs off coordinate `i`, write the `σᵢ`-average of sups as an average of
two sups, pair maximizers `a, a'` and use
`φᵢ(aᵢ) − φᵢ(a'ᵢ) ≤ ρ|aᵢ − a'ᵢ|`, absorbing the absolute value by the
`a ↔ a'` symmetry (SSBD Eqs. (26.12)–(26.13)). The finite-average `signAvg`
makes the conditioning a literal finite-sum split. Stated for a `Finset` class
per the sup policy (sups must be attained). The book's display has a typo
(`φ_m(y_m)` for `φ_m(a_m)`) — statement follows the corrected reading. -/

open scoped BigOperators

namespace StatLean.StatisticalLearning

variable {n : ℕ}

/-! ### Sign-average bookkeeping -/

private lemma signAvg_add' (n : ℕ) (f g : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => f ε + g ε) = signAvg n f + signAvg n g := by
  unfold signAvg
  rw [Finset.sum_add_distrib]
  ring

private lemma signAvg_mono' (n : ℕ) {f g : (Fin n → ℝ) → ℝ}
    (h : ∀ ε, f ε ≤ g ε) : signAvg n f ≤ signAvg n g := by
  unfold signAvg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h _) (by positivity)

private lemma bddAbove_coe_finset' (B : Finset (Fin n → ℝ)) (ε : Fin n → ℝ) :
    BddAbove ((fun a => ∑ i, ε i * a i) '' (↑B : Set (Fin n → ℝ))) :=
  (B.finite_toSet.image _).bddAbove

private lemma sSup_coe_finset_image' (B : Finset (Fin n → ℝ)) (hne : B.Nonempty)
    (f : (Fin n → ℝ) → ℝ) : sSup (f '' (↑B : Set (Fin n → ℝ))) = B.sup' hne f :=
  (Finset.sup'_eq_csSup_image B hne f).symm

/-! ### Flipping a single sign

Conditioning on the signs off coordinate `i₀` is implemented as the
involution `σ ↦ σ` with the `i₀`-th sign negated; the sign average is
invariant under it, so `E_σ F = E_σ (F(σ) + F(σ^{i₀}))/2` — the book's
two-term average.
-/

/-- Negate the `i₀` coordinate of a sign vector. -/
private def flipAt (i₀ : Fin n) (ε : Fin n → ℝ) : Fin n → ℝ :=
  Function.update ε i₀ (-(ε i₀))

/-- Flip the `i₀` coordinate of a Boolean sign pattern. -/
private def flipBoolAt (i₀ : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ := Function.update σ i₀ (!σ i₀)
  invFun σ := Function.update σ i₀ (!σ i₀)
  left_inv σ := by
    funext j
    rcases eq_or_ne j i₀ with rfl | h
    · simp
    · simp [Function.update_of_ne h]
  right_inv σ := by
    funext j
    rcases eq_or_ne j i₀ with rfl | h
    · simp
    · simp [Function.update_of_ne h]

private lemma signOf_flipBoolAt (i₀ : Fin n) (σ : Fin n → Bool) :
    signOf (flipBoolAt i₀ σ) = flipAt i₀ (signOf σ) := by
  funext j
  rcases eq_or_ne j i₀ with rfl | h
  · simp only [flipAt, flipBoolAt, Equiv.coe_fn_mk, signOf, Function.update_self]
    cases hh : σ j <;> simp
  · simp only [flipAt, flipBoolAt, Equiv.coe_fn_mk, signOf, Function.update_of_ne h]

private lemma signAvg_comp_flipAt (n : ℕ) (i₀ : Fin n) (G : (Fin n → ℝ) → ℝ) :
    signAvg n (fun ε => G (flipAt i₀ ε)) = signAvg n G := by
  unfold signAvg
  congr 1
  refine Fintype.sum_equiv (flipBoolAt i₀) _ _ fun σ => ?_
  rw [signOf_flipBoolAt]

/-! ### The one-coordinate contraction -/

/-- The heart of SSBD Lemma 26.9 (Eqs. (26.12)–(26.13)): applying a
`1`-Lipschitz map to a **single** coordinate does not increase the Rademacher
complexity. -/
private lemma rad_update_le (B : Finset (Fin n → ℝ)) (hne : B.Nonempty)
    (i₀ : Fin n) (ψ : ℝ → ℝ) (hψ : ∀ x y, |ψ x - ψ y| ≤ |x - y|) :
    radComplexity
        (↑(B.image fun b => Function.update b i₀ (ψ (b i₀))) : Set (Fin n → ℝ))
      ≤ radComplexity (↑B : Set (Fin n → ℝ)) := by
  classical
  set g : (Fin n → ℝ) → (Fin n → ℝ) :=
    fun b => Function.update b i₀ (ψ (b i₀)) with hgdef
  have hne' : (B.image g).Nonempty := hne.image g
  set T : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
    fun ε b => ∑ i ∈ Finset.univ.erase i₀, ε i * b i with hTdef
  have hsplit : ∀ (ε b : Fin n → ℝ), ∑ i, ε i * b i = ε i₀ * b i₀ + T ε b :=
    fun ε b =>
      (Finset.add_sum_erase _ (fun i => ε i * b i) (Finset.mem_univ i₀)).symm
  have hTg : ∀ (ε b : Fin n → ℝ), T ε (g b) = T ε b := by
    intro ε b
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne₀ : i ≠ i₀ := Finset.ne_of_mem_erase hi
    rw [hgdef]
    simp [Function.update_of_ne hne₀]
  have hsplitg : ∀ (ε b : Fin n → ℝ),
      ∑ i, ε i * (g b) i = ε i₀ * ψ (b i₀) + T ε b := by
    intro ε b
    rw [hsplit ε (g b), hTg ε b, hgdef]
    simp
  have hTflip : ∀ (ε b : Fin n → ℝ), T (flipAt i₀ ε) b = T ε b := by
    intro ε b
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne₀ : i ≠ i₀ := Finset.ne_of_mem_erase hi
    simp [flipAt, Function.update_of_ne hne₀]
  have hflip0 : ∀ ε : Fin n → ℝ, (flipAt i₀ ε) i₀ = -(ε i₀) := by
    intro ε
    simp [flipAt]
  set F : (Fin n → ℝ) → ℝ := fun ε => B.sup' hne (fun b => ∑ i, ε i * b i) with hFdef
  set F' : (Fin n → ℝ) → ℝ :=
    fun ε => B.sup' hne (fun b => ∑ i, ε i * (g b) i) with hF'def
  have hFsup : ∀ ε : Fin n → ℝ,
      sSup ((fun a => ∑ i, ε i * a i) '' (↑B : Set (Fin n → ℝ))) = F ε :=
    fun ε => sSup_coe_finset_image' B hne _
  have hF'sup : ∀ ε : Fin n → ℝ,
      sSup ((fun a => ∑ i, ε i * a i) '' (↑(B.image g) : Set (Fin n → ℝ)))
        = F' ε := by
    intro ε
    rw [sSup_coe_finset_image' (B.image g) hne' _, Finset.sup'_image]
    rfl
  -- the two-term average inequality, at every sign vector
  have hpoint : ∀ ε : Fin n → ℝ,
      F' ε + F' (flipAt i₀ ε) ≤ F ε + F (flipAt i₀ ε) := by
    intro ε
    set s : ℝ := ε i₀ with hs
    have hFe : F ε = B.sup' hne (fun b => s * b i₀ + T ε b) := by
      rw [hFdef]
      exact Finset.sup'_congr hne rfl fun b _ => hsplit ε b
    have hFf : F (flipAt i₀ ε) = B.sup' hne (fun b => -s * b i₀ + T ε b) := by
      rw [hFdef]
      refine Finset.sup'_congr hne rfl fun b _ => ?_
      rw [hsplit (flipAt i₀ ε) b, hTflip ε b, hflip0 ε]
    have hF'e : F' ε = B.sup' hne (fun b => s * ψ (b i₀) + T ε b) := by
      rw [hF'def]
      exact Finset.sup'_congr hne rfl fun b _ => hsplitg ε b
    have hF'f : F' (flipAt i₀ ε) = B.sup' hne (fun b => -s * ψ (b i₀) + T ε b) := by
      rw [hF'def]
      refine Finset.sup'_congr hne rfl fun b _ => ?_
      rw [hsplitg (flipAt i₀ ε) b, hTflip ε b, hflip0 ε]
    obtain ⟨b₁, hb₁, e₁⟩ :=
      Finset.exists_mem_eq_sup' hne (fun b => s * ψ (b i₀) + T ε b)
    obtain ⟨b₂, hb₂, e₂⟩ :=
      Finset.exists_mem_eq_sup' hne (fun b => -s * ψ (b i₀) + T ε b)
    rw [hF'e, hF'f, e₁, e₂, hFe, hFf]
    have hlip : s * (ψ (b₁ i₀) - ψ (b₂ i₀)) ≤ |s * (b₁ i₀ - b₂ i₀)| := by
      have h1 : s * (ψ (b₁ i₀) - ψ (b₂ i₀)) ≤ |s * (ψ (b₁ i₀) - ψ (b₂ i₀))| :=
        le_abs_self _
      have h2 : |s * (ψ (b₁ i₀) - ψ (b₂ i₀))| = |s| * |ψ (b₁ i₀) - ψ (b₂ i₀)| :=
        abs_mul _ _
      have h3 : |s| * |ψ (b₁ i₀) - ψ (b₂ i₀)| ≤ |s| * |b₁ i₀ - b₂ i₀| :=
        mul_le_mul_of_nonneg_left (hψ (b₁ i₀) (b₂ i₀)) (abs_nonneg s)
      have h4 : |s| * |b₁ i₀ - b₂ i₀| = |s * (b₁ i₀ - b₂ i₀)| := (abs_mul _ _).symm
      linarith
    -- the two cases of the absolute value are exchanged by `b₁ ↔ b₂`
    rcases abs_cases (s * (b₁ i₀ - b₂ i₀)) with ⟨he, _⟩ | ⟨he, _⟩
    · have h5 : s * ψ (b₁ i₀) + T ε b₁ + (-s * ψ (b₂ i₀) + T ε b₂)
          ≤ (s * b₁ i₀ + T ε b₁) + (-s * b₂ i₀ + T ε b₂) := by
        rw [he] at hlip; nlinarith [hlip]
      have h6 : s * b₁ i₀ + T ε b₁ ≤ B.sup' hne (fun b => s * b i₀ + T ε b) :=
        Finset.le_sup' (f := fun b => s * b i₀ + T ε b) hb₁
      have h7 : -s * b₂ i₀ + T ε b₂ ≤ B.sup' hne (fun b => -s * b i₀ + T ε b) :=
        Finset.le_sup' (f := fun b => -s * b i₀ + T ε b) hb₂
      linarith
    · have h5 : s * ψ (b₁ i₀) + T ε b₁ + (-s * ψ (b₂ i₀) + T ε b₂)
          ≤ (s * b₂ i₀ + T ε b₂) + (-s * b₁ i₀ + T ε b₁) := by
        rw [he] at hlip; nlinarith [hlip]
      have h6 : s * b₂ i₀ + T ε b₂ ≤ B.sup' hne (fun b => s * b i₀ + T ε b) :=
        Finset.le_sup' (f := fun b => s * b i₀ + T ε b) hb₂
      have h7 : -s * b₁ i₀ + T ε b₁ ≤ B.sup' hne (fun b => -s * b i₀ + T ε b) :=
        Finset.le_sup' (f := fun b => -s * b i₀ + T ε b) hb₁
      linarith
  have havg : signAvg n F' ≤ signAvg n F := by
    have e1 : signAvg n (fun ε => F' ε + F' (flipAt i₀ ε)) = 2 * signAvg n F' := by
      rw [signAvg_add' n F' (fun ε => F' (flipAt i₀ ε)), signAvg_comp_flipAt]
      ring
    have e2 : signAvg n (fun ε => F ε + F (flipAt i₀ ε)) = 2 * signAvg n F := by
      rw [signAvg_add' n F (fun ε => F (flipAt i₀ ε)), signAvg_comp_flipAt]
      ring
    have hmono := signAvg_mono' n hpoint
    rw [e1, e2] at hmono
    linarith
  unfold radComplexity
  have hL : (fun ε : Fin n → ℝ =>
      sSup ((fun a => ∑ i, ε i * a i) '' (↑(B.image g) : Set (Fin n → ℝ)))) = F' :=
    funext hF'sup
  have hR : (fun ε : Fin n → ℝ =>
      sSup ((fun a => ∑ i, ε i * a i) '' (↑B : Set (Fin n → ℝ)))) = F :=
    funext hFsup
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left havg (by positivity)

/-- The `1`-Lipschitz case of SSBD Lemma 26.9: process the coordinates one at
a time, each step paying nothing. -/
private lemma rad_contraction_one (A : Finset (Fin n → ℝ)) (hne : A.Nonempty)
    (ψ : Fin n → ℝ → ℝ) (hψ : ∀ i x y, |ψ i x - ψ i y| ≤ |x - y|) :
    radComplexity (↑(A.image fun a => fun i => ψ i (a i)) : Set (Fin n → ℝ))
      ≤ radComplexity (↑A : Set (Fin n → ℝ)) := by
  classical
  set G : Finset (Fin n) → (Fin n → ℝ) → (Fin n → ℝ) :=
    fun S a => fun i => if i ∈ S then ψ i (a i) else a i with hGdef
  have key : ∀ S : Finset (Fin n),
      radComplexity (↑(A.image (G S)) : Set (Fin n → ℝ))
        ≤ radComplexity (↑A : Set (Fin n → ℝ)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        have himg : A.image (G ∅) = A := by
          have hid : G ∅ = fun a => a := by
            funext a i
            simp [hGdef]
          rw [hid, Finset.image_id']
        rw [himg]
    | insert j S hj ih =>
        have hstep : A.image (G (insert j S))
            = (A.image (G S)).image (fun b => Function.update b j (ψ j (b j))) := by
          rw [Finset.image_image]
          refine Finset.image_congr ?_
          intro a _
          funext i
          rcases eq_or_ne i j with rfl | h
          · simp [hGdef, hj]
          · simp [hGdef, h]
        rw [hstep]
        exact le_trans
          (rad_update_le (A.image (G S)) (hne.image _) j (ψ j) (hψ j)) ih
  have hfin : A.image (G Finset.univ) = A.image fun a => fun i => ψ i (a i) := by
    refine Finset.image_congr ?_
    intro a _
    funext i
    simp [hGdef]
  rw [← hfin]
  exact key Finset.univ

/-- A one-point class has zero Rademacher complexity (the shift is killed by
`E σᵢ = 0`). -/
private lemma rad_singleton_eq_zero (c : Fin n → ℝ) :
    radComplexity ({c} : Set (Fin n → ℝ)) = 0 := by
  have hbdd : ∀ ε : Fin n → ℝ,
      BddAbove ((fun a => ∑ i, ε i * a i) '' ({0} : Set (Fin n → ℝ))) := by
    intro ε
    rw [Set.image_singleton]
    exact bddAbove_singleton
  have h1 : ({c} : Set (Fin n → ℝ)) = (fun a => a + c) '' ({0} : Set (Fin n → ℝ)) := by
    rw [Set.image_singleton]
    simp
  rw [h1, radComplexity_translate ({0} : Set (Fin n → ℝ)) c
    (Set.singleton_nonempty 0) hbdd]
  unfold radComplexity
  have h2 : (fun ε : Fin n → ℝ =>
      sSup ((fun a => ∑ i, ε i * a i) '' ({0} : Set (Fin n → ℝ))))
      = fun _ => (0 : ℝ) := by
    funext ε
    rw [Set.image_singleton]
    simp
  rw [h2]
  unfold signAvg
  simp

/-- **SSBD Lemma 26.9 (contraction)**: for per-coordinate `ρ`-Lipschitz maps
`φᵢ : ℝ → ℝ`, `R({(φ₁(a₁),…,φₙ(aₙ)) : a ∈ A}) ≤ ρ · R(A)` for a finite
nonempty class `A`. -/
theorem radComplexity_contraction (A : Finset (Fin n → ℝ))
    (φ : Fin n → ℝ → ℝ) {ρ : ℝ}
    -- USER-INPUT: nonempty class; SSBD Lemma 26.9 (implicit)
    (hne : A.Nonempty)
    -- USER-INPUT: `ρ ≥ 0` (Lipschitz constant); SSBD Lemma 26.9
    (hρ : 0 ≤ ρ)
    -- USER-INPUT: each `φᵢ` is `ρ`-Lipschitz; SSBD Lemma 26.9
    (hφ : ∀ i a b, |φ i a - φ i b| ≤ ρ * |a - b|) :
    radComplexity
        (↑(A.image fun a => fun i => φ i (a i)) : Set (Fin n → ℝ)) ≤
      ρ * radComplexity (↑A : Set (Fin n → ℝ)) := by
  classical
  rcases hρ.lt_or_eq with hρpos | hρ0
  · -- `ρ > 0`: normalize to the `1`-Lipschitz case and rescale
    set ψ : Fin n → ℝ → ℝ := fun i t => ρ⁻¹ * φ i t with hψdef
    have hψ : ∀ i x y, |ψ i x - ψ i y| ≤ |x - y| := by
      intro i x y
      have habs : |ψ i x - ψ i y| = ρ⁻¹ * |φ i x - φ i y| := by
        rw [hψdef]
        simp only
        rw [← mul_sub, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hρpos))]
      rw [habs]
      calc ρ⁻¹ * |φ i x - φ i y| ≤ ρ⁻¹ * (ρ * |x - y|) :=
            mul_le_mul_of_nonneg_left (hφ i x y) (le_of_lt (inv_pos.mpr hρpos))
        _ = |x - y| := by field_simp
    set Aψ : Finset (Fin n → ℝ) := A.image (fun a => fun i => ψ i (a i)) with hAψ
    have himg : (↑(A.image fun a => fun i => φ i (a i)) : Set (Fin n → ℝ))
        = (fun x : Fin n → ℝ => ρ • x) '' (↑Aψ : Set (Fin n → ℝ)) := by
      rw [hAψ, Finset.coe_image, Finset.coe_image, Set.image_image]
      congr 1
      funext a
      funext i
      change φ i (a i) = ρ * (ρ⁻¹ * φ i (a i))
      field_simp
    rw [himg]
    calc radComplexity ((fun x : Fin n → ℝ => ρ • x) '' (↑Aψ : Set (Fin n → ℝ)))
        ≤ |ρ| * radComplexity (↑Aψ : Set (Fin n → ℝ)) :=
          radComplexity_smul_le _ ρ (Finset.coe_nonempty.mpr (hne.image _))
            (fun ε => bddAbove_coe_finset' Aψ ε)
      _ = ρ * radComplexity (↑Aψ : Set (Fin n → ℝ)) := by
          rw [abs_of_nonneg hρ]
      _ ≤ ρ * radComplexity (↑A : Set (Fin n → ℝ)) :=
          mul_le_mul_of_nonneg_left (rad_contraction_one A hne ψ hψ) hρ
  · -- `ρ = 0`: every `φᵢ` is constant, so the image class is a single point
    have hconst : ∀ i x y, φ i x = φ i y := by
      intro i x y
      have h0 : |φ i x - φ i y| ≤ 0 := by
        have := hφ i x y
        rw [← hρ0] at this
        simpa using this
      have := abs_nonpos_iff.mp h0
      linarith
    obtain ⟨a₀, ha₀⟩ := hne
    have himg : A.image (fun a => fun i => φ i (a i))
        = {fun i => φ i (a₀ i)} := by
      rw [Finset.image_congr
        (g := fun _ : Fin n → ℝ => fun i => φ i (a₀ i)) ?_,
        Finset.image_const ⟨a₀, ha₀⟩]
      intro a _
      funext i
      exact hconst i (a i) (a₀ i)
    rw [himg, Finset.coe_singleton, ← hρ0, zero_mul, rad_singleton_eq_zero]

end StatLean.StatisticalLearning
