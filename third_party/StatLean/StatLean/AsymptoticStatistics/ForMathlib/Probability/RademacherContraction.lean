module
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.Rademacher
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

@[expose] public section

/-!
# Rademacher contractions

Coordinate flips preserve the finite Rademacher cube, and a deterministic
two-supremum inequality supplies the elementary contraction step.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- Flip one coordinate of a Boolean Rademacher vector. -/
def rademacherCoordinateFlip {n : ℕ}
    (k : Fin n) (ε : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = k then !(ε j) else ε j

/-- Flip every coordinate of a Boolean Rademacher vector. -/
def rademacherFlipAll {n : ℕ}
    (ε : Fin n → Bool) : Fin n → Bool := fun j => !(ε j)

@[simp] theorem rademacherSign_not (b : Bool) :
    rademacherSign (!b) = -rademacherSign b := by
  cases b <;> simp [rademacherSign]

theorem measurePreserving_bool_not_rademacher :
    MeasurePreserving Bool.not rademacherMeasure rademacherMeasure := by
  have hnot : Measurable Bool.not := measurable_of_finite _
  refine ⟨hnot, ?_⟩
  rw [rademacherMeasure]
  rw [PMF.toMeasure_map Bool.not rademacherPMF hnot]
  congr 1
  apply PMF.ext
  intro b
  cases b <;>
    simp [rademacherPMF, PMF.map_apply, PMF.uniformOfFintype_apply]

theorem measurePreserving_rademacherCoordinateFlip
    {n : ℕ} (k : Fin n) :
    MeasurePreserving (rademacherCoordinateFlip k)
      (rademacherCube n) (rademacherCube n) := by
  unfold rademacherCoordinateFlip rademacherCube
  apply measurePreserving_pi _ _
    (f := fun j b => if j = k then !b else b)
  intro j
  by_cases hj : j = k
  · simpa [hj] using measurePreserving_bool_not_rademacher
  · simpa [hj] using! MeasurePreserving.id rademacherMeasure

theorem measurePreserving_rademacherFlipAll {n : ℕ} :
    MeasurePreserving rademacherFlipAll (rademacherCube n) (rademacherCube n) := by
  unfold rademacherFlipAll rademacherCube
  exact measurePreserving_pi _ _
    (fun _ => measurePreserving_bool_not_rademacher)

set_option linter.unusedFintypeInType false in
theorem iSup_add_comp_add_iSup_sub_comp_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (c x : ι → ℝ) (ψ : ℝ → ℝ) (L : ℝ)
    (hψ : ∀ s t, |ψ s - ψ t| ≤ L * |s - t|) :
    (⨆ j, c j + ψ (x j)) + (⨆ j, c j - ψ (x j)) ≤
      (⨆ j, c j + L * x j) + (⨆ j, c j - L * x j) := by
  obtain ⟨jp, hp⟩ :=
    exists_eq_ciSup_of_finite (f := fun j => c j + ψ (x j))
  obtain ⟨jm, hm⟩ :=
    exists_eq_ciSup_of_finite (f := fun j => c j - ψ (x j))
  rw [← hp, ← hm]
  rcases le_total (x jp) (x jm) with hpm | hmp
  · calc
      c jp + ψ (x jp) + (c jm - ψ (x jm))
          ≤ (c jm + L * x jm) + (c jp - L * x jp) := by
            have hdiff : ψ (x jp) - ψ (x jm) ≤ L * (x jm - x jp) := by
              calc
                ψ (x jp) - ψ (x jm) ≤ |ψ (x jp) - ψ (x jm)| :=
                  le_abs_self _
                _ ≤ L * |x jp - x jm| := hψ _ _
                _ = L * (x jm - x jp) := by
                  rw [abs_of_nonpos (sub_nonpos.mpr hpm)]
                  ring
            linarith
      _ ≤ (⨆ j, c j + L * x j) + (⨆ j, c j - L * x j) := by
        exact add_le_add
          (le_ciSup (Set.finite_range (fun j => c j + L * x j)).bddAbove jm)
          (le_ciSup (Set.finite_range (fun j => c j - L * x j)).bddAbove jp)
  · calc
      c jp + ψ (x jp) + (c jm - ψ (x jm))
          ≤ (c jp + L * x jp) + (c jm - L * x jm) := by
            have hdiff : ψ (x jp) - ψ (x jm) ≤ L * (x jp - x jm) := by
              calc
                ψ (x jp) - ψ (x jm) ≤ |ψ (x jp) - ψ (x jm)| :=
                  le_abs_self _
                _ ≤ L * |x jp - x jm| := hψ _ _
                _ = L * (x jp - x jm) := by
                  rw [abs_of_nonneg (sub_nonneg.mpr hmp)]
            linarith
      _ ≤ (⨆ j, c j + L * x j) + (⨆ j, c j - L * x j) := by
        exact add_le_add
          (le_ciSup (Set.finite_range (fun j => c j + L * x j)).bddAbove jp)
          (le_ciSup (Set.finite_range (fun j => c j - L * x j)).bddAbove jm)

set_option linter.unusedFintypeInType false in
theorem integral_iSup_rademacherSum_update_comp_le
    {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → Fin n → ℝ) (k : Fin n)
    (x : ι → ℝ) (ψ : ℝ → ℝ) (L : ℝ)
    (hψ : ∀ s t, |ψ s - ψ t| ≤ L * |s - t|) :
    ∫ ε, ⨆ j, rademacherSum
        (Function.update (b j) k (ψ (x j))) ε ∂rademacherCube n ≤
    ∫ ε, ⨆ j, rademacherSum
        (Function.update (b j) k (L * x j)) ε ∂rademacherCube n := by
  classical
  let A : (ι → ℝ) → (Fin n → Bool) → ℝ := fun y ε =>
    ⨆ j, rademacherSum (Function.update (b j) k (y j)) ε
  have hfiniteInt (f : (Fin n → Bool) → ℝ) :
      Integrable f (rademacherCube n) := by
    have hsum_nonneg : 0 ≤ ∑ ε, ‖f ε‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine (integrable_const (μ := rademacherCube n)
      (∑ ε, ‖f ε‖)).mono (measurable_of_finite _).aestronglyMeasurable ?_
    filter_upwards with ε
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
    exact Finset.single_le_sum (fun η _ => norm_nonneg (f η))
      (Finset.mem_univ ε)
  have hA_int (y : ι → ℝ) : Integrable (A y) (rademacherCube n) :=
    hfiniteInt _
  have hflip (y : ι → ℝ) :
      ∫ ε, A y (rademacherCoordinateFlip k ε) ∂rademacherCube n =
        ∫ ε, A y ε ∂rademacherCube n := by
    let e : (Fin n → Bool) ≃ᵐ (Fin n → Bool) :=
      { toEquiv :=
          { toFun := rademacherCoordinateFlip k
            invFun := rademacherCoordinateFlip k
            left_inv := fun ε => by
              funext i
              by_cases hik : i = k <;>
                simp [rademacherCoordinateFlip, hik]
            right_inv := fun ε => by
              funext i
              by_cases hik : i = k <;>
                simp [rademacherCoordinateFlip, hik] }
        measurable_toFun := measurable_of_finite _
        measurable_invFun := measurable_of_finite _ }
    exact (measurePreserving_rademacherCoordinateFlip k).integral_comp'
      (f := e) (A y)
  have hpoint (ε : Fin n → Bool) :
      A (fun j => ψ (x j)) ε +
          A (fun j => ψ (x j)) (rademacherCoordinateFlip k ε) ≤
        A (fun j => L * x j) ε +
          A (fun j => L * x j) (rademacherCoordinateFlip k ε) := by
    let c : ι → ℝ := fun j =>
      ∑ i ∈ Finset.univ.erase k, b j i * rademacherSign (ε i)
    have hexpand (y : ι → ℝ) :
        A y ε = ⨆ j, c j + y j * rademacherSign (ε k) := by
      simp only [A]
      congr 1
      funext j
      unfold rademacherSum
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      change (∑ i ∈ Finset.univ.erase k,
        Function.update (b j) k (y j) i * rademacherSign (ε i)) +
          Function.update (b j) k (y j) k * rademacherSign (ε k) = _
      congr 1
      · unfold c
        apply Finset.sum_congr rfl
        intro i hi
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      · rw [Function.update_self]
    have hexpand_flip (y : ι → ℝ) :
        A y (rademacherCoordinateFlip k ε) =
          ⨆ j, c j - y j * rademacherSign (ε k) := by
      simp only [A]
      congr 1
      funext j
      unfold rademacherSum
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      change (∑ i ∈ Finset.univ.erase k,
        Function.update (b j) k (y j) i *
          rademacherSign (rademacherCoordinateFlip k ε i)) +
          Function.update (b j) k (y j) k *
            rademacherSign (rademacherCoordinateFlip k ε k) = _
      congr 1
      · unfold c
        apply Finset.sum_congr rfl
        intro i hi
        have hik : i ≠ k := Finset.ne_of_mem_erase hi
        rw [Function.update_of_ne hik]
        simp [rademacherCoordinateFlip, hik]
      · rw [Function.update_self]
        simp [rademacherCoordinateFlip]
    rw [hexpand, hexpand_flip, hexpand, hexpand_flip]
    cases hε : ε k
    · simpa [rademacherSign, hε, mul_comm, mul_left_comm, mul_assoc] using
        iSup_add_comp_add_iSup_sub_comp_le c x ψ L hψ
    · simp only [rademacherSign, if_true, mul_neg, mul_one]
      simp only [sub_eq_add_neg, neg_neg]
      rw [add_comm (⨆ j, c j + -ψ (x j)),
        add_comm (⨆ j, c j + -(L * x j))]
      simpa only [sub_eq_add_neg] using
        iSup_add_comp_add_iSup_sub_comp_le c x ψ L hψ
  have hsum :
      ∫ ε, (A (fun j => ψ (x j)) ε +
          A (fun j => ψ (x j)) (rademacherCoordinateFlip k ε))
          ∂rademacherCube n ≤
        ∫ ε, (A (fun j => L * x j) ε +
          A (fun j => L * x j) (rademacherCoordinateFlip k ε))
          ∂rademacherCube n :=
    integral_mono (hA_int _ |>.add (hfiniteInt _))
      (hA_int _ |>.add (hfiniteInt _)) hpoint
  rw [integral_add (hA_int _) (hfiniteInt _),
    integral_add (hA_int _) (hfiniteInt _), hflip, hflip] at hsum
  simpa [A] using (by linarith :
    ∫ ε, A (fun j => ψ (x j)) ε ∂rademacherCube n ≤
      ∫ ε, A (fun j => L * x j) ε ∂rademacherCube n)

set_option linter.unusedFintypeInType false in
theorem integral_iSup_rademacherSum_comp_le
    {n : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → Fin n → ℝ) (φ : Fin n → ℝ → ℝ) (L : ℝ)
    (hφ_lipschitz : ∀ k x y, |φ k x - φ k y| ≤ L * |x - y|) :
    ∫ ε, ⨆ j, rademacherSum (fun k => φ k (a j k)) ε
      ∂rademacherCube n ≤
      L * ∫ ε, ⨆ j, rademacherSum (a j) ε ∂rademacherCube n := by
  classical
  cases n with
  | zero => simp [rademacherSum]
  | succ n =>
    have hL : 0 ≤ L := by
      have h := hφ_lipschitz (0 : Fin (n + 1)) 0 1
      norm_num at h
      exact (abs_nonneg _).trans h
    let v : Finset (Fin (n + 1)) → ι → Fin (n + 1) → ℝ :=
      fun s j k => if k ∈ s then L * a j k else φ k (a j k)
    let I : Finset (Fin (n + 1)) → ℝ := fun s =>
      ∫ ε, ⨆ j, rademacherSum (v s j) ε ∂rademacherCube (n + 1)
    have hstep (s : Finset (Fin (n + 1))) (k : Fin (n + 1)) (hk : k ∉ s) :
        I s ≤ I (insert k s) := by
      have hleft (j : ι) :
          Function.update (v s j) k (φ k (a j k)) = v s j := by
        funext i
        by_cases hi : i = k
        · subst i; simp [v, hk]
        · simp [v, hi]
      have hright (j : ι) :
          Function.update (v s j) k (L * a j k) = v (insert k s) j := by
        funext i
        by_cases hi : i = k
        · subst i; simp [v, hk]
        · simp [v, hi]
      simpa only [I, hleft, hright] using
        integral_iSup_rademacherSum_update_comp_le (v s) k
          (fun j => a j k) (φ k) L (hφ_lipschitz k)
    have hchain : I ∅ ≤ I Finset.univ := by
      suffices ∀ s : Finset (Fin (n + 1)), I ∅ ≤ I s from this Finset.univ
      intro s
      induction s using Finset.induction_on with
      | empty => exact le_rfl
      | @insert k s hk ih => exact ih.trans (hstep s k hk)
    have hscale (ε : Fin (n + 1) → Bool) :
        (⨆ j, rademacherSum (fun k => L * a j k) ε) =
          L * (⨆ j, rademacherSum (a j) ε) := by
      have hrs (j : ι) :
          rademacherSum (fun k => L * a j k) ε =
            L * rademacherSum (a j) ε := by
        simp [rademacherSum, Finset.mul_sum, mul_assoc]
      simp_rw [hrs]
      obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite
        (f := fun j => rademacherSum (a j) ε)
      rw [← hj]
      apply le_antisymm
      · apply ciSup_le
        intro i
        have hi : rademacherSum (a i) ε ≤ rademacherSum (a j) ε := by
          rw [hj]
          exact le_ciSup (Set.finite_range (fun j => rademacherSum (a j) ε)).bddAbove i
        exact mul_le_mul_of_nonneg_left
          hi hL
      · exact le_ciSup
          (Set.finite_range (fun j => L * rademacherSum (a j) ε)).bddAbove j
    calc
      ∫ ε, ⨆ j, rademacherSum (fun k => φ k (a j k)) ε
          ∂rademacherCube (n + 1) ≤
          ∫ ε, ⨆ j, rademacherSum (fun k => L * a j k) ε
            ∂rademacherCube (n + 1) := by simpa [I, v] using hchain
      _ = ∫ ε, L * (⨆ j, rademacherSum (a j) ε)
            ∂rademacherCube (n + 1) := integral_congr_ae (Filter.Eventually.of_forall hscale)
      _ = L * ∫ ε, ⨆ j, rademacherSum (a j) ε
            ∂rademacherCube (n + 1) := integral_const_mul _ _

set_option linter.unusedFintypeInType false in
theorem integral_iSup_abs_rademacherSum_comp_le
    {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Fin n → ℝ) (φ : Fin n → ℝ → ℝ) (L : ℝ)
    (hφ_zero : ∀ k, φ k 0 = 0)
    (hφ_lipschitz : ∀ k x y, |φ k x - φ k y| ≤ L * |x - y|) :
    ∫ ε, ⨆ j, |rademacherSum (fun k => φ k (a j k)) ε|
      ∂rademacherCube n ≤
      2 * L * ∫ ε, ⨆ j, |rademacherSum (a j) ε| ∂rademacherCube n := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI : IsEmpty ι := hι
      simp
  | inr hι =>
      letI : Nonempty ι := hι
      cases n with
      | zero => simp [rademacherSum]
      | succ n =>
        have hL : 0 ≤ L := by
          have h := hφ_lipschitz (0 : Fin (n + 1)) 0 1
          norm_num at h
          exact (abs_nonneg _).trans h
        let a₀ : Option ι → Fin (n + 1) → ℝ := fun j k =>
          match j with
          | none => 0
          | some i => a i k
        let b₀ : Option ι → Fin (n + 1) → ℝ := fun j k =>
          φ k (a₀ j k)
        let A : (Option ι → Fin (n + 1) → ℝ) →
            (Fin (n + 1) → Bool) → ℝ := fun c ε =>
          ⨆ j, rademacherSum (c j) ε
        have ha₀_none (k : Fin (n + 1)) : a₀ none k = 0 := rfl
        have hb₀_none (k : Fin (n + 1)) : b₀ none k = 0 := by
          simp [b₀, ha₀_none, hφ_zero]
        have hfiniteInt (f : (Fin (n + 1) → Bool) → ℝ) :
            Integrable f (rademacherCube (n + 1)) := by
          have hsum_nonneg : 0 ≤ ∑ ε, ‖f ε‖ :=
            Finset.sum_nonneg fun _ _ => norm_nonneg _
          refine (integrable_const (μ := rademacherCube (n + 1))
            (∑ ε, ‖f ε‖)).mono (measurable_of_finite _).aestronglyMeasurable ?_
          filter_upwards with ε
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsum_nonneg]
          exact Finset.single_le_sum (fun η _ => norm_nonneg (f η))
            (Finset.mem_univ ε)
        have hflip_sum (c : Option ι → Fin (n + 1) → ℝ)
            (j : Option ι) (ε : Fin (n + 1) → Bool) :
            rademacherSum (c j) (rademacherFlipAll ε) =
              -rademacherSum (c j) ε := by
          simp [rademacherSum, rademacherFlipAll, ← Finset.sum_neg_distrib]
        have hflip_A (c : Option ι → Fin (n + 1) → ℝ) :
            ∫ ε, A c (rademacherFlipAll ε) ∂rademacherCube (n + 1) =
              ∫ ε, A c ε ∂rademacherCube (n + 1) := by
          let e : (Fin (n + 1) → Bool) ≃ᵐ (Fin (n + 1) → Bool) :=
            { toEquiv :=
                { toFun := rademacherFlipAll
                  invFun := rademacherFlipAll
                  left_inv := fun ε => by funext k; simp [rademacherFlipAll]
                  right_inv := fun ε => by funext k; simp [rademacherFlipAll] }
              measurable_toFun := measurable_of_finite _
              measurable_invFun := measurable_of_finite _ }
          exact measurePreserving_rademacherFlipAll.integral_comp' (f := e) (A c)
        have hcontract :
            ∫ ε, A b₀ ε ∂rademacherCube (n + 1) ≤
              L * ∫ ε, A a₀ ε ∂rademacherCube (n + 1) := by
          simpa [A, b₀] using integral_iSup_rademacherSum_comp_le
            a₀ φ L hφ_lipschitz
        have hleft_point (ε : Fin (n + 1) → Bool) :
            (⨆ j, |rademacherSum (fun k => φ k (a j k)) ε|) ≤
              A b₀ ε + A b₀ (rademacherFlipAll ε) := by
          apply ciSup_le
          intro j
          rw [abs_le]
          constructor
          · have hzero := le_ciSup
                (Set.finite_range (fun q => rademacherSum (b₀ q) ε)).bddAbove none
            have hj := le_ciSup
                (Set.finite_range (fun q => rademacherSum (b₀ q)
                  (rademacherFlipAll ε))).bddAbove (some j)
            rw [hflip_sum] at hj
            change -(A b₀ ε + A b₀ (rademacherFlipAll ε)) ≤
              rademacherSum (b₀ (some j)) ε
            have hnonneg : 0 ≤ A b₀ ε := by
              simpa [A, rademacherSum, hb₀_none] using hzero
            linarith
          · have hj := le_ciSup
                (Set.finite_range (fun q => rademacherSum (b₀ q) ε)).bddAbove
                (some j)
            have hzero := le_ciSup
                (Set.finite_range (fun q => rademacherSum (b₀ q)
                  (rademacherFlipAll ε))).bddAbove none
            change rademacherSum (b₀ (some j)) ε ≤
              A b₀ ε + A b₀ (rademacherFlipAll ε)
            have hnonneg : 0 ≤ A b₀ (rademacherFlipAll ε) := by
              simpa [A, rademacherSum, hb₀_none] using hzero
            linarith
        have hright_point (ε : Fin (n + 1) → Bool) :
            A a₀ ε ≤ ⨆ j, |rademacherSum (a j) ε| := by
          apply ciSup_le
          intro j
          cases j with
          | none =>
              simp only [a₀, rademacherSum, zero_mul, Finset.sum_const_zero]
              exact (abs_nonneg _).trans (le_ciSup
                (Set.finite_range (fun i => |rademacherSum (a i) ε|)).bddAbove
                (Classical.choice hι))
          | some j =>
              exact (le_abs_self _).trans (le_ciSup
                (Set.finite_range (fun i => |rademacherSum (a i) ε|)).bddAbove j)
        have hleft :
            ∫ ε, ⨆ j, |rademacherSum (fun k => φ k (a j k)) ε|
                ∂rademacherCube (n + 1) ≤
              2 * ∫ ε, A b₀ ε ∂rademacherCube (n + 1) := by
          calc
            _ ≤ ∫ ε, (A b₀ ε + A b₀ (rademacherFlipAll ε))
                ∂rademacherCube (n + 1) :=
              integral_mono (hfiniteInt _) (hfiniteInt _) hleft_point
            _ = 2 * ∫ ε, A b₀ ε ∂rademacherCube (n + 1) := by
              rw [integral_add (hfiniteInt _) (hfiniteInt _), hflip_A]
              ring
        have hright :
            ∫ ε, A a₀ ε ∂rademacherCube (n + 1) ≤
              ∫ ε, ⨆ j, |rademacherSum (a j) ε| ∂rademacherCube (n + 1) :=
          integral_mono (hfiniteInt _) (hfiniteInt _) hright_point
        calc
          _ ≤ 2 * ∫ ε, A b₀ ε ∂rademacherCube (n + 1) := hleft
          _ ≤ 2 * (L * ∫ ε, A a₀ ε ∂rademacherCube (n + 1)) := by
            gcongr
          _ ≤ 2 * (L * ∫ ε, ⨆ j, |rademacherSum (a j) ε|
                ∂rademacherCube (n + 1)) := by
            gcongr
          _ = 2 * L * ∫ ε, ⨆ j, |rademacherSum (a j) ε|
                ∂rademacherCube (n + 1) := by ring

end ProbabilityTheory
