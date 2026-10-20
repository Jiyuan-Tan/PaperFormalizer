module
public import StatLean.ConcentrationInequalities.VC.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.Analysis.Convex.Basic

@[expose] public section

/-!
# VC dimension of half-spaces in ℝᵐ

The class of closed half-spaces
$\{x \in \mathbb{R}^m : \langle a, x\rangle \le b\}$ has VC dimension exactly
$$ \mathrm{vc}(\text{half-spaces in } \mathbb{R}^m) \;=\; m + 1, $$
and in particular half-planes in $\mathbb{R}^2$ have VC dimension $3$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.1, Example 8.3.5 (= Exercise 8.17;
half-spaces) and Example 8.3.3 (half-planes, the `m = 2` instance).

**Proof formalization notes.** Lower bound: the `(m+1)`-point set
`{0, e₀, …, e_{m−1}}` is shattered by the explicit witnesses
`a = ∑ᵢ (if eᵢ ∈ T then −1 else 1) • EuclideanSpace.single i 1` and
`b = if 0 ∈ T then 0 else −1/2` (inner products computed by
`EuclideanSpace.inner_single_left`; the design's witness was verified on
paper). Upper bound: any `(m+2)`-point set is affinely dependent
(`finrank_vectorSpan_le_iff_not_affineIndependent` + `Submodule.finrank_le`),
so `Convex.radon_partition` yields a point in the convex hulls of both cells
of a partition; a half-space realizing the corresponding labeling would put
that point in the disjoint convex sets `{⟨a,·⟩ ≤ b}` and `{b < ⟨a,·⟩}`
(`convex_halfSpace_le` / `convex_halfSpace_gt` + `convexHull_min`) —
contradiction. `Shatters.mono_right` extends "no `(m+2)`-set is shattered"
to `vcDim ≤ m + 1`. Example 8.3.3 is *derived* as the `m = 2`
instantiation, not re-proved. Constants: exact equality, no slack.
Named-sorry fallback of this work item: `not_shatters_halfSpaceClass` (the
Radon upper bound); the explicit lower-bound witness and the `vcDim`
assembly must close.

**Bibliographic comments.** The half-space computation is the classical
example of Vapnik–Chervonenkis theory (*Theory Probab. Appl.* 16 (1971),
264–280); the Radon-partition route to the upper bound follows J. Radon,
"Mengen konvexer Körper, die einen gemeinsamen Punkt enthalten," *Math.
Ann.* 83 (1921), 113–115.
-/

namespace StatLean.ConcentrationInequalities

/-- The class of closed half-spaces `{x : ⟨a, x⟩ ≤ b}` in `ℝᵐ`
(HDP §8.3.1, Example 8.3.5). Edge behavior: `a = 0` is allowed, so `∅`
(`b < 0`) and `univ` (`b ≥ 0`) are members. -/
def halfSpaceClass (m : ℕ) : Set (Set (EuclideanSpace ℝ (Fin m))) :=
  {S | ∃ (a : EuclideanSpace ℝ (Fin m)) (b : ℝ),
    S = {x : EuclideanSpace ℝ (Fin m) | inner ℝ a x ≤ b}}

open Classical in
/-- The `(m+1)`-point set `{0, e₀, …, e_{m−1}}` is shattered by half-spaces
(HDP §8.3.1, Example 8.3.5, lower bound; witness
`a i = if eᵢ ∈ T then −1 else 1`, `b = if 0 ∈ T then 0 else −1/2`). -/
theorem shatters_halfSpaceClass_simplex (m : ℕ) :
    Shatters (halfSpaceClass m)
      (insert (0 : EuclideanSpace ℝ (Fin m))
        (Finset.univ.image fun i : Fin m =>
          EuclideanSpace.single i (1 : ℝ))) := by
  classical
  intro T hsub
  -- Witness: coefficients `c i = -1` if `eᵢ ∈ T`, else `1`; threshold `b`.
  set c : Fin m → ℝ :=
    fun i => if EuclideanSpace.single i (1 : ℝ) ∈ T then (-1 : ℝ) else 1 with hc
  set a : EuclideanSpace ℝ (Fin m) :=
    ∑ i, c i • EuclideanSpace.single i (1 : ℝ) with ha
  set b : ℝ := if (0 : EuclideanSpace ℝ (Fin m)) ∈ T then (0 : ℝ) else -1 / 2 with hb
  -- Orthonormality of the basis vectors.
  have hsingle : ∀ i j : Fin m,
      (inner ℝ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) : ℝ)
        = if i = j then (1 : ℝ) else 0 := by
    intro i j
    refine (EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ)
      (EuclideanSpace.single j (1 : ℝ))).trans ?_
    simp [PiLp.single_apply, eq_comm]
  -- Inner product of `a` with a basis vector recovers the coefficient.
  have hval : ∀ j : Fin m,
      (inner ℝ a (EuclideanSpace.single j (1 : ℝ)) : ℝ) = c j := by
    intro j
    rw [ha, sum_inner]
    simp only [real_inner_smul_left, hsingle, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j c]
    simp
  -- Membership equivalence at the origin.
  have hmem0 :
      ((inner ℝ a (0 : EuclideanSpace ℝ (Fin m)) : ℝ) ≤ b)
        ↔ (0 : EuclideanSpace ℝ (Fin m)) ∈ T := by
    rw [inner_zero_right, hb]
    split_ifs with h
    · exact iff_of_true (by norm_num) h
    · exact iff_of_false (by norm_num) h
  -- Membership equivalence at a basis vector.
  have hmemj : ∀ j : Fin m,
      ((inner ℝ a (EuclideanSpace.single j (1 : ℝ)) : ℝ) ≤ b)
        ↔ EuclideanSpace.single j (1 : ℝ) ∈ T := by
    intro j
    rw [hval j]
    simp only [hc]
    by_cases hj : EuclideanSpace.single j (1 : ℝ) ∈ T
    · rw [if_pos hj]
      refine iff_of_true ?_ hj
      rw [hb]; split_ifs <;> norm_num
    · rw [if_neg hj]
      refine iff_of_false ?_ hj
      rw [hb]; split_ifs <;> norm_num
  -- Combined: for each point of `Λ`, membership in the half-space ⇔ membership in `T`.
  have hkey : ∀ x ∈ (insert (0 : EuclideanSpace ℝ (Fin m))
      (Finset.univ.image fun i : Fin m => EuclideanSpace.single i (1 : ℝ))),
      ((inner ℝ a x : ℝ) ≤ b ↔ x ∈ T) := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hx0 | hximg
    · subst hx0; exact hmem0
    · rw [Finset.mem_image] at hximg
      obtain ⟨j, -, hj⟩ := hximg
      subst hj; exact hmemj j
  refine ⟨{x | (inner ℝ a x : ℝ) ≤ b}, ⟨a, b, rfl⟩, ?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxΛ, hxS⟩
    have hxΛ' : x ∈ _ := Finset.mem_coe.mp hxΛ
    exact Finset.mem_coe.mpr ((hkey x hxΛ').mp hxS)
  · intro x hx
    have hxT : x ∈ T := Finset.mem_coe.mp hx
    have hxΛ : x ∈ _ := hsub hxT
    exact ⟨Finset.mem_coe.mpr hxΛ, (hkey x hxΛ).mpr hxT⟩

/-- No `(m+2)`-point set is shattered by half-spaces in `ℝᵐ` (HDP §8.3.1,
Example 8.3.5, upper bound via Radon's partition: `(m+2)` points are
affinely dependent, and a point common to the two convex hulls cannot be
separated from itself). -/
theorem not_shatters_halfSpaceClass {m : ℕ}
    {Λ : Finset (EuclideanSpace ℝ (Fin m))}
    -- USER-INPUT: cardinality m + 2 (one above the claimed VC dimension);
    -- HDP §8.3.1, Example 8.3.5.
    (hcard : Λ.card = m + 2) :
    ¬ Shatters (halfSpaceClass m) Λ := by
  classical
  intro hshat
  -- View the `m+2` points as a family indexed by the subtype `↥Λ`.
  set f : (↥Λ) → EuclideanSpace ℝ (Fin m) := Subtype.val with hf
  have hcardι : Fintype.card (↥Λ) = m + 2 := by rw [Fintype.card_coe]; exact hcard
  -- `m+2` points in an `m`-dimensional space are affinely dependent.
  have hfr : Module.finrank ℝ (vectorSpan ℝ (Set.range f)) ≤ m :=
    (Submodule.finrank_le _).trans finrank_euclideanSpace_fin.le
  have hnai : ¬ AffineIndependent ℝ f :=
    (finrank_vectorSpan_le_iff_not_affineIndependent ℝ f hcardι).mp hfr
  obtain ⟨I, p, hpI, hpIc⟩ := Convex.radon_partition hnai
  -- The `I`-cell lies in `Λ`, so it is realized by a labeling `T`.
  have hIΛ : f '' I ⊆ (↑Λ : Set _) := by rintro x ⟨y, -, rfl⟩; exact Finset.mem_coe.mpr y.2
  obtain ⟨T, hTsub, hTcoe⟩ := exists_finset_coe_of_subset_coe hIΛ
  obtain ⟨S, hSmem, hSeq⟩ := hshat T hTsub
  obtain ⟨a, b, hSab⟩ := hSmem
  subst hSab
  -- `↑Λ ∩ S = f '' I`.
  have hUnion : (↑Λ : Set _) ∩ {x | (inner ℝ a x : ℝ) ≤ b} = f '' I := hSeq.trans hTcoe
  -- `x ↦ ⟨a, x⟩` is linear, so both open/closed half-spaces are convex.
  have hlin : IsLinearMap ℝ (fun x : EuclideanSpace ℝ (Fin m) => (inner ℝ a x : ℝ)) :=
    { map_add := fun x y => inner_add_right a x y
      map_smul := fun r x => by rw [real_inner_smul_right, smul_eq_mul] }
  -- The `I`-cell sits in the closed half-space `{⟨a,·⟩ ≤ b}`.
  have hIS : f '' I ⊆ {x | (inner ℝ a x : ℝ) ≤ b} := by
    rw [← hUnion]; exact Set.inter_subset_right
  -- The complementary cell sits in the open half-space `{b < ⟨a,·⟩}`.
  have hIcS : f '' Iᶜ ⊆ {x | b < (inner ℝ a x : ℝ)} := by
    rintro x ⟨y, hyIc, rfl⟩
    have hyΛ : (f y) ∈ (↑Λ : Set _) := Finset.mem_coe.mpr y.2
    by_contra hxS
    simp only [Set.mem_setOf_eq, not_lt] at hxS
    have : (f y) ∈ f '' I := by rw [← hUnion]; exact ⟨hyΛ, hxS⟩
    obtain ⟨z, hzI, hz⟩ := this
    have hfinj : Function.Injective f := by rw [hf]; exact Subtype.val_injective
    exact hyIc (hfinj hz ▸ hzI)
  -- Radon's common point would lie in both disjoint half-spaces — contradiction.
  have hple : (inner ℝ a p : ℝ) ≤ b :=
    convexHull_min hIS (convex_halfSpace_le hlin b) hpI
  have hpgt : b < (inner ℝ a p : ℝ) :=
    convexHull_min hIcS (convex_halfSpace_gt hlin b) hpIc
  exact absurd hple (not_le.mpr hpgt)

/-- **Half-spaces in ℝᵐ have VC dimension m + 1** (HDP §8.3.1,
Example 8.3.5 = Exercise 8.17). -/
theorem vcDim_halfSpaceClass (m : ℕ) :
    vcDim (halfSpaceClass m) = m + 1 := by
  classical
  -- Injectivity of `i ↦ eᵢ` and `0 ∉ {eᵢ}`, hence the simplex has `m+1` points.
  have hinj : Function.Injective
      (fun i : Fin m => EuclideanSpace.single i (1 : ℝ)) := by
    intro i j hij
    by_contra hne
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin m) => v i) hij
    simp [hne] at h2
  have h0 : (0 : EuclideanSpace ℝ (Fin m)) ∉
      Finset.univ.image (fun i : Fin m => EuclideanSpace.single i (1 : ℝ)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin m) => v i) hi
    simp at h2
  have hcard_simplex :
      (insert (0 : EuclideanSpace ℝ (Fin m))
        (Finset.univ.image fun i : Fin m => EuclideanSpace.single i (1 : ℝ))).card
        = m + 1 := by
    rw [Finset.card_insert_of_notMem h0, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  apply le_antisymm
  · -- Upper bound: any shattered set has at most `m+1` points.
    rw [vcDim_le_iff]
    intro Λ hΛ
    have hnat : Λ.card ≤ m + 1 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨Λ', hsub, hc⟩ :=
        Finset.exists_subset_card_eq (show m + 2 ≤ Λ.card from hcon)
      exact not_shatters_halfSpaceClass hc (hΛ.mono_right hsub)
    calc (Λ.card : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast hnat
      _ = (m : ℕ∞) + 1 := by push_cast; ring
  · -- Lower bound: the `m+1`-point simplex is shattered.
    have h := (shatters_halfSpaceClass_simplex m).card_le_vcDim
    rw [hcard_simplex] at h
    calc (m : ℕ∞) + 1 = ((m + 1 : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ vcDim (halfSpaceClass m) := h

/-- **Half-planes in ℝ² have VC dimension 3** (HDP §8.3.1, Example 8.3.3) —
derived as the `m = 2` instance of `vcDim_halfSpaceClass`, not
re-proved. -/
theorem vcDim_halfSpaceClass_two : vcDim (halfSpaceClass 2) = 3 := by
  have h := vcDim_halfSpaceClass 2
  norm_num at h ⊢
  exact h

end StatLean.ConcentrationInequalities
