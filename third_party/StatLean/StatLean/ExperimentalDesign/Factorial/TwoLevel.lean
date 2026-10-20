module
public import Mathlib.Order.SymmDiff
public import StatLean.ExperimentalDesign.Core.Contrast

@[expose] public section

/-!
# Two-level factorial structure: the ±1 character algebra

A `2^k` factorial experiment indexes its treatment combinations by the level vectors
`x ∈ {−1,+1}^k` (encoded here as `x : ι → Bool` with sign map `true ↦ +1`,
`false ↦ −1`, over an arbitrary finite factor index `ι`).  Every factorial effect —
main effect or interaction — is carried by a **character**
$$\chi_S(x) = \prod_{j \in S} \operatorname{sign}(x_j), \qquad S \subseteq \iota,$$
and the whole `2^k` effect calculus is the orthogonality relation
$$\sum_{x} \chi_S(x)\, \chi_{S'}(x) = \begin{cases} 2^k, & S = S' \\ 0, & S \ne S'
\end{cases}$$
together with its consequences: the **factorial expansion** of any response function
`y` on the treatment combinations,
$$y(x) = \sum_{S} \widehat y(S)\, \chi_S(x), \qquad
  \widehat y(S) = 2^{-k} \sum_x y(x) \chi_S(x),$$
uniqueness of the coefficients, and the Parseval identity
`∑ₓ y(x)² = 2^k ∑_S ŷ(S)²`.  Nonempty-set characters are treatment contrasts,
linking the factorial calculus to the contrast algebra of `Core/Contrast`.

## Main results

* `levelSign`, `character` — the sign map and the characters.
* `character_mul` — multiplicativity: `χ_S χ_T = χ_{S Δ T}` (Mead's product rule for
  effect rows).
* `sum_character_eq_zero`, `sum_character_mul` — character orthogonality.
* `factorialCoeff`, `factorialExpansion`, `factorialCoeff_eq_of_expansion` — the
  expansion and its uniqueness.
* `factorialParseval` — the sum-of-squares decomposition.
* `characterContrast` — nonempty characters as treatment contrasts.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988, §13.1–§13.3: the
`±1` effect matrix `U` whose "elements are all ±1 and the rows are orthogonal", the
product rule "the elements of the PQ row are obtained by multiplying the
corresponding elements in the rows for P and Q", and the general `m`-factor effect
formula `effect = (1/2^{m−1})(p ± 1)(q ± 1)⋯`; the confounding calculus built on the
same characters is §16.2.  (`Mead §13.1`, `Mead §16.2`.)

**Scaling deviation from the book.** Mead normalises effects by `1/2^{m−1}` (and the
overall mean by `1/2^m`); our `factorialCoeff` uniformly uses `2^{−k}`, so a Mead
effect equals `2 · factorialCoeff` for nonempty `S` and the mean is
`factorialCoeff ∅`.  The uniform normalisation is what makes the expansion,
uniqueness and Parseval statements clean; the docstrings of consumers should convert.

**Proof formalization notes.**
* `character_mul` is the `∏` computation over `S ∆ T` (squares of signs cancel on
  `S ∩ T`); stated with `symmDiff` to avoid notation ambiguity.
* `sum_character_eq_zero` factors out one coordinate `j₀ ∈ S` and pairs `x` with its
  `j₀`-flip; equivalently, induct via `Fintype.sum_prod_type`-style splitting of the
  Boolean cube.  `sum_character_mul` is then `character_mul` plus the vanishing sum,
  with `symmDiff S T = ∅ ↔ S = T`.
* The expansion/uniqueness/Parseval block is finite Fourier inversion on
  `(ZMod 2)^ι` in elementary clothing; everything is a double-sum swap plus
  orthogonality.  `Fintype.card_fun` gives `|ι → Bool| = 2^k`.
-/

namespace StatLean.ExperimentalDesign

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **sign encoding** of a two-level factor: `true ↦ +1`, `false ↦ −1`
(`Mead §13.1`, the ±1 coding of upper/lower levels). -/
def levelSign (b : Bool) : ℝ := if b then 1 else -1

/-- The **character** of a set `S` of factors: `χ_S(x) = ∏_{j ∈ S} sign(x j)` — the
±1 row of the effect matrix indexed by the effect `S` (`Mead §13.1`). -/
noncomputable def character (S : Finset ι) (x : ι → Bool) : ℝ :=
  ∏ j ∈ S, levelSign (x j)

/-- The square of a level sign is one. -/
private lemma levelSign_mul_self (b : Bool) : levelSign b * levelSign b = 1 := by
  cases b <;> norm_num [levelSign]

@[simp]
theorem character_empty (x : ι → Bool) : character (∅ : Finset ι) x = 1 := by
  simp [character]

/-- Characters square to one pointwise. -/
theorem character_mul_self (S : Finset ι) (x : ι → Bool) :
    character S x * character S x = 1 := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => levelSign_mul_self (x j)

set_option maxHeartbeats 800000 in
/-- **Multiplicativity**: `χ_S · χ_T = χ_{S Δ T}` — Mead's product rule for effect
rows (`Mead §13.1`; the group law behind confounding, `Mead §16.2`). -/
theorem character_mul (S T : Finset ι) (x : ι → Bool) :
    character S x * character T x = character (symmDiff S T) x := by
  classical
  have hchi : character (symmDiff S T) x
      = (∏ j ∈ S \ T, levelSign (x j)) * ∏ j ∈ T \ S, levelSign (x j) := by
    have hdd : Disjoint (S \ T) (T \ S) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp ha).1
    unfold character
    rw [symmDiff_def, Finset.sup_eq_union, Finset.prod_union hdd]
  have hd : Disjoint (S \ T) (S ∩ T) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
  have hd' : Disjoint (T \ S) (T ∩ S) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
  have hS : (∏ j ∈ S, levelSign (x j))
      = (∏ j ∈ S \ T, levelSign (x j)) * ∏ j ∈ S ∩ T, levelSign (x j) := by
    rw [← Finset.prod_union hd, Finset.sdiff_union_inter]
  have hT : (∏ j ∈ T, levelSign (x j))
      = (∏ j ∈ T \ S, levelSign (x j)) * ∏ j ∈ S ∩ T, levelSign (x j) := by
    rw [Finset.inter_comm, ← Finset.prod_union hd', Finset.sdiff_union_inter]
  have hsq : (∏ j ∈ S ∩ T, levelSign (x j)) * ∏ j ∈ S ∩ T, levelSign (x j) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => levelSign_mul_self (x j)
  rw [hchi]
  unfold character
  rw [hS, hT]
  calc ((∏ j ∈ S \ T, levelSign (x j)) * ∏ j ∈ S ∩ T, levelSign (x j))
        * ((∏ j ∈ T \ S, levelSign (x j)) * ∏ j ∈ S ∩ T, levelSign (x j))
      = ((∏ j ∈ S \ T, levelSign (x j)) * ∏ j ∈ T \ S, levelSign (x j))
        * ((∏ j ∈ S ∩ T, levelSign (x j)) * ∏ j ∈ S ∩ T, levelSign (x j)) := by ring
    _ = (∏ j ∈ S \ T, levelSign (x j)) * ∏ j ∈ T \ S, levelSign (x j) := by
        rw [hsq, mul_one]

/-- Finite Fubini over the Boolean cube: a product-form summand factorizes. -/
private lemma sum_pi_bool_prod (G : ι → Bool → ℝ) :
    ∑ x : ι → Bool, ∏ j, G j (x j) = ∏ j, ∑ b, G j b := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- A character as a full product over the factor index. -/
private lemma character_eq_prod_univ (S : Finset ι) (x : ι → Bool) :
    character S x = ∏ j, (if j ∈ S then levelSign (x j) else 1) := by
  unfold character
  calc ∏ j ∈ S, levelSign (x j)
      = ∏ j ∈ S, (if j ∈ S then levelSign (x j) else 1) :=
        Finset.prod_congr rfl fun j hj => (if_pos hj).symm
    _ = ∏ j, (if j ∈ S then levelSign (x j) else 1) :=
        Finset.prod_subset (Finset.subset_univ S) fun j _ hj => if_neg hj

/-- A nonempty-set character sums to zero over the treatment combinations. -/
theorem sum_character_eq_zero {S : Finset ι}
    -- LEAN-ONLY: nonempty effect set; the empty character sums to `2^k`
    (hS : S.Nonempty) :
    ∑ x : ι → Bool, character S x = 0 := by
  classical
  calc ∑ x : ι → Bool, character S x
      = ∑ x : ι → Bool, ∏ j, (if j ∈ S then levelSign (x j) else 1) :=
        Finset.sum_congr rfl fun x _ => character_eq_prod_univ S x
    _ = ∏ j, ∑ b, (if j ∈ S then levelSign b else 1) :=
        sum_pi_bool_prod fun j b => if j ∈ S then levelSign b else 1
    _ = 0 := by
        obtain ⟨j₀, hj₀⟩ := hS
        refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
        simp only [if_pos hj₀]
        norm_num [Fintype.sum_bool, levelSign]

/-- **Character orthogonality** (`Mead §13.1`, orthogonality of the rows of the
effect matrix): `∑ₓ χ_S(x) χ_T(x)` is `2^k` for `S = T` and `0` otherwise. -/
theorem sum_character_mul (S T : Finset ι) :
    ∑ x : ι → Bool, character S x * character T x
      = if S = T then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  simp only [character_mul]
  by_cases hST : S = T
  · subst hST
    rw [if_pos rfl, symmDiff_self]
    calc ∑ x : ι → Bool, character (⊥ : Finset ι) x
        = ∑ _x : ι → Bool, (1 : ℝ) :=
          Finset.sum_congr rfl fun x _ => character_empty x
      _ = (Fintype.card (ι → Bool) : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      _ = (2 : ℝ) ^ Fintype.card ι := by
          rw [Fintype.card_fun, Fintype.card_bool]
          push_cast
          ring
  · rw [if_neg hST]
    refine sum_character_eq_zero ?_
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hST (symmDiff_eq_bot.mp h)

/-- The **factorial coefficient** of a response function at the effect `S`:
`ŷ(S) = 2^{−k} ∑ₓ y(x) χ_S(x)`.  Equals half the Mead effect for nonempty `S` and
the overall mean for `S = ∅` (see the module docstring for the scaling). -/
noncomputable def factorialCoeff (y : (ι → Bool) → ℝ) (S : Finset ι) : ℝ :=
  ((2 : ℝ) ^ Fintype.card ι)⁻¹ * ∑ x, y x * character S x

/-- Dual orthogonality: summing `χ_S(z) χ_S(x)` over the effects `S` detects
`z = x`. -/
private lemma sum_character_point (z x : ι → Bool) :
    ∑ S : Finset ι, character S z * character S x
      = if z = x then (2 : ℝ) ^ Fintype.card ι else 0 := by
  classical
  have h1 : (∑ S : Finset ι, character S z * character S x)
      = ∑ S : Finset ι, ∏ j ∈ S, (levelSign (z j) * levelSign (x j)) := by
    refine Finset.sum_congr rfl fun S _ => ?_
    unfold character
    rw [Finset.prod_mul_distrib]
  have key : ∑ S : Finset ι, ∏ j ∈ S, (levelSign (z j) * levelSign (x j))
      = ∏ j, (levelSign (z j) * levelSign (x j) + 1) := by
    rw [Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.prod_const_one, mul_one]
  rw [h1, key]
  by_cases hzx : z = x
  · subst hzx
    rw [if_pos rfl]
    calc ∏ j, (levelSign (z j) * levelSign (z j) + 1)
        = ∏ _j : ι, (2 : ℝ) :=
          Finset.prod_congr rfl fun j _ => by rw [levelSign_mul_self]; norm_num
      _ = (2 : ℝ) ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]
  · rw [if_neg hzx]
    obtain ⟨j₀, hj₀⟩ : ∃ j, z j ≠ x j := by
      by_contra h
      push_neg at h
      exact hzx (funext h)
    refine Finset.prod_eq_zero (Finset.mem_univ j₀) ?_
    revert hj₀
    cases z j₀ <;> cases x j₀ <;> intro hj₀ <;>
      first
        | exact absurd rfl hj₀
        | norm_num [levelSign]

/-- **The factorial expansion** (`Mead §13.1`, the effect representation `y = Ux` in
matrix form): every response function is the character sum of its factorial
coefficients. -/
theorem factorialExpansion (y : (ι → Bool) → ℝ) (x : ι → Bool) :
    y x = ∑ S : Finset ι, factorialCoeff y S * character S x := by
  classical
  have h2 : ((2 : ℝ) ^ Fintype.card ι) ≠ 0 := pow_ne_zero _ two_ne_zero
  symm
  calc ∑ S : Finset ι, factorialCoeff y S * character S x
      = ∑ S : Finset ι, ((2 : ℝ) ^ Fintype.card ι)⁻¹
          * ∑ z, y z * character S z * character S x := by
        refine Finset.sum_congr rfl fun S _ => ?_
        unfold factorialCoeff
        rw [mul_assoc]
        congr 1
        rw [Finset.sum_mul]
    _ = ((2 : ℝ) ^ Fintype.card ι)⁻¹
          * ∑ z, y z * ∑ S : Finset ι, character S z * character S x := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S _ => ?_
        ring
    _ = ((2 : ℝ) ^ Fintype.card ι)⁻¹ * (y x * (2 : ℝ) ^ Fintype.card ι) := by
        congr 1
        calc ∑ z, y z * ∑ S : Finset ι, character S z * character S x
            = ∑ z, y z * (if z = x then (2 : ℝ) ^ Fintype.card ι else 0) :=
              Finset.sum_congr rfl fun z _ => by rw [sum_character_point]
          _ = ∑ z, (if z = x then y z * (2 : ℝ) ^ Fintype.card ι else 0) :=
              Finset.sum_congr rfl fun z _ => by split <;> simp
          _ = y x * (2 : ℝ) ^ Fintype.card ι := by
              rw [Finset.sum_ite_eq' Finset.univ x
                (fun z => y z * (2 : ℝ) ^ Fintype.card ι), if_pos (Finset.mem_univ x)]
    _ = y x := by
        field_simp

/-- **Uniqueness of the factorial coefficients**: any coefficient family reproducing
`y` through the character expansion is the family of factorial coefficients. -/
theorem factorialCoeff_eq_of_expansion (y : (ι → Bool) → ℝ) (c : Finset ι → ℝ)
    -- USER-INPUT: a character representation of the response; Mead §13.1
    (h : ∀ x, y x = ∑ S : Finset ι, c S * character S x) (S : Finset ι) :
    c S = factorialCoeff y S := by
  classical
  have h2 : ((2 : ℝ) ^ Fintype.card ι) ≠ 0 := pow_ne_zero _ two_ne_zero
  have key : ∑ x, y x * character S x = c S * (2 : ℝ) ^ Fintype.card ι := by
    calc ∑ x, y x * character S x
        = ∑ x, ∑ T : Finset ι, c T * (character T x * character S x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [h x, Finset.sum_mul]
          exact Finset.sum_congr rfl fun T _ => by ring
      _ = ∑ T : Finset ι, ∑ x, c T * (character T x * character S x) :=
          Finset.sum_comm
      _ = ∑ T : Finset ι, c T * (if T = S then (2 : ℝ) ^ Fintype.card ι else 0) := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [← Finset.mul_sum, sum_character_mul]
      _ = ∑ T : Finset ι, (if T = S then c T * (2 : ℝ) ^ Fintype.card ι else 0) :=
          Finset.sum_congr rfl fun T _ => by split <;> simp
      _ = c S * (2 : ℝ) ^ Fintype.card ι := by
          rw [Finset.sum_ite_eq' Finset.univ S
            (fun T => c T * (2 : ℝ) ^ Fintype.card ι), if_pos (Finset.mem_univ S)]
  unfold factorialCoeff
  rw [key]
  field_simp

/-- **Parseval for the factorial expansion**: `∑ₓ y(x)² = 2^k ∑_S ŷ(S)²` — the exact
sum-of-squares decomposition of a `2^k` response into effect components
(`Mead §13.1`, the component SS of the effects). -/
theorem factorialParseval (y : (ι → Bool) → ℝ) :
    ∑ x, y x ^ 2
      = (2 : ℝ) ^ Fintype.card ι * ∑ S : Finset ι, factorialCoeff y S ^ 2 := by
  classical
  have h2 : ((2 : ℝ) ^ Fintype.card ι) ≠ 0 := pow_ne_zero _ two_ne_zero
  calc ∑ x, y x ^ 2
      = ∑ x, ∑ S : Finset ι, factorialCoeff y S * (y x * character S x) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [pow_two]
        nth_rewrite 1 [factorialExpansion y x]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun S _ => by ring
    _ = ∑ S : Finset ι, factorialCoeff y S * ∑ x, y x * character S x := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun S _ => by rw [Finset.mul_sum]
    _ = ∑ S : Finset ι, factorialCoeff y S
          * (factorialCoeff y S * (2 : ℝ) ^ Fintype.card ι) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        congr 1
        unfold factorialCoeff
        field_simp
    _ = (2 : ℝ) ^ Fintype.card ι * ∑ S : Finset ι, factorialCoeff y S ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun S _ => by ring

/-- A nonempty-set character, viewed as a **treatment contrast** on the treatment
combinations (`Mead §13.3`: factorial effects are contrasts). -/
noncomputable def characterContrast {S : Finset ι} (hS : S.Nonempty) :
    Contrast (ι → Bool) :=
  ⟨character S, sum_character_eq_zero hS⟩

end StatLean.ExperimentalDesign
