module
public import StatLean.ConcentrationInequalities.Symmetrization.Symmetrization
public import StatLean.ConcentrationInequalities.Symmetrization.GaussianMax
public import StatLean.ConcentrationInequalities.ForMathlib.IndepTransport
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section

/-!
# Symmetrization for empirical processes (HDP Exercise 8.11)

For i.i.d. data $X_1, \dots, X_n \sim P$ and a uniformly bounded class of
functions $\{f_k\}_{k \in \iota}$ with $|f_k| \le 1$,
$$ \mathbb{E}\,\sup_{k}\Bigl|\frac1n \sum_{i=1}^n f_k(X_i)
     - \mathbb{E}_P f_k\Bigr|
   \;\le\; 2\, \mathbb{E}\,\sup_{k}\Bigl|\frac1n \sum_{i=1}^n
     \varepsilon_i f_k(X_i)\Bigr|, $$
with the book's factor `2` exactly; the signs live on the product extension
`μ.prod (signVec n)`. Finite-index core plus a `Countable`-index lift per the
batch sup policy. **The RHS is deliberately uncentered** — this is the point
of the exercise.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3, Exercise 8.11 (Symmetrization for empirical
processes).

**Proof formalization notes.** Instantiate `symmetrization_upper_pi` at
`E := ι → ℝ` with the `Fintype` Pi sup-norm (Mathlib's default norm on a
finite Pi type *is* the sup norm — no `PiLp ∞` machinery) and vectors
`Zᵢ(ω) := fun k => n⁻¹ · f_k(Xᵢ(ω))`: the centering constant cancels in
`Zᵢ − Zᵢ'`, which is exactly the book's "modify the proof of Lemma 6.3.2" and
why the RHS is uncentered. Transport by `ForMathlib/IndepTransport`; norm ↔
`iSup` bridge as in `GaussianMax.pi_norm_eq_ciSup_abs`; coordinates of the
Bochner mean via `ContinuousLinearMap.proj` + `integral_comp_comm`. The
i.i.d. hypothesis is `iIndepFun X μ` + per-index pushforward `μ.map (Xᵢ) = P`
with `P` explicit (Mathlib's `HasLaw` is absent at our pin), since
`∫ f_k dP` appears in the statement. `[NeZero n]` is genuine: the statement
is **false** at `n = 0` (LHS is the sup of population means, RHS is `0`).
We state `|f_k| ≤ 1` rather than `{0,1}`-valued — free mild generality over
the book's Boolean class. Countable lift by `exists_surjective_nat` +
monotone convergence of finite sups (`tendsto_atTop_ciSup`) + dominated
convergence with constant dominators `2` resp. `1` from the class bound.
Consumer note (VC cluster, Theorem 8.3.15): a `Finset` class is consumed as
the subtype `↥s` with `F := Subtype.val`; the RHS integral over
`μ.prod (signVec n)` is designed to be Fubini'd (`integral_prod`) and
attacked per-`ω` by `FiniteMaximal` over the sign coordinate. Named-sorry
fallback of this work item: `empirical_symmetrization_countable` (the
finite-index core — the VC cluster's actual consumption shape — fully
proven).

**Bibliographic comments.** Symmetrization of empirical processes is the
Giné–Zinn school's basic tool, going back to V. N. Vapnik and A. Ya.
Chervonenkis (1971) and formalized in E. Giné and J. Zinn, "Some limit
theorems for empirical processes," *Ann. Probab.* 12 (1984), 929–989; the
canonical treatment is van der Vaart–Wellner, *Weak Convergence and Empirical
Processes* (1996), §2.3.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Symmetrization for empirical processes, finite class** (HDP §8.3,
Exercise 8.11): `E sup_k |n⁻¹ ∑ᵢ f_k(Xᵢ) − E_P f_k| ≤ 2 E sup_k |n⁻¹ ∑ᵢ εᵢ
f_k(Xᵢ)|`, signs on the product extension `μ.prod (signVec n)`. The RHS is
deliberately uncentered. -/
theorem empirical_symmetrization {α : Type*} [MeasurableSpace α] {ι : Type*}
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ}
    [NeZero n] {X : Fin n → Ω → α} {P : Measure α} [IsProbabilityMeasure P]
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent sample; HDP Exercise 8.11
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: identically distributed with law P; HDP Exercise 8.11
    (hX_law : ∀ i, μ.map (X i) = P)
    {F : ι → α → ℝ}
    -- LEAN-ONLY: measurability of the class members
    (hF_meas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniformly bounded (Boolean) class, |f_k| ≤ 1; HDP Exercise 8.11
    (hF_bdd : ∀ k x, |F k x| ≤ 1) :
    ∫ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| ∂μ
      ≤ 2 * ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|
          ∂(μ.prod (signVec n)) := by
  classical
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- The `E := ι → ℝ`-valued data `Zᵢ(ω) = fun k => n⁻¹ · f_k(Xᵢ ω)`.
  set Z : Fin n → Ω → (ι → ℝ) := fun i ω k => (n : ℝ)⁻¹ * F k (X i ω) with hZ
  have hZ_meas : ∀ i, Measurable (Z i) := by
    intro i
    rw [measurable_pi_iff]
    intro k
    exact measurable_const.mul ((hF_meas k).comp (hX_meas i))
  have hZ_indep : iIndepFun Z μ := by
    rw [hZ]
    exact hX_indep.comp (fun (_ : Fin n) (a : α) (k : ι) => (n : ℝ)⁻¹ * F k a)
      (fun _ => by rw [measurable_pi_iff]; intro k; exact measurable_const.mul (hF_meas k))
  haveI hνp : ∀ i, IsProbabilityMeasure (μ.map (Z i)) :=
    fun i => Measure.isProbabilityMeasure_map (hZ_meas i).aemeasurable
  -- Boundedness ⇒ integrability of the class members and of `Zᵢ`.
  have hFX_int : ∀ i k, Integrable (fun ω => F k (X i ω)) μ := by
    intro i k
    refine Integrable.of_mem_Icc (-1) 1 ((hF_meas k).comp (hX_meas i)).aemeasurable ?_
    filter_upwards with ω
    exact Set.mem_Icc.mpr (abs_le.mp (hF_bdd k (X i ω)))
  have hZ_int : ∀ i, Integrable (Z i) μ := by
    intro i
    rw [integrable_pi_iff]
    intro k
    simp only [hZ]
    exact (hFX_int i k).const_mul _
  have hν_int : ∀ i, Integrable id (μ.map (Z i)) := fun i =>
    (integrable_map_measure aestronglyMeasurable_id (hZ_meas i).aemeasurable).mpr
      (by simpa using hZ_int i)
  have hev : ∀ i, ∀ j : ι, Integrable (fun z : ι → ℝ => z j) (μ.map (Z i)) := by
    intro i j
    simpa using (integrable_pi_iff.mp (hν_int i)) j
  -- The coordinate mean is `n⁻¹ ∫ f_k dP` (law transfer).
  have hc : ∀ i (k : ι), (∫ z, z ∂(μ.map (Z i))) k = (n : ℝ)⁻¹ * ∫ x, F k x ∂P := by
    intro i k
    rw [eval_integral (hev i) k,
      integral_map (hZ_meas i).aemeasurable (measurable_pi_apply k).aestronglyMeasurable]
    simp only [hZ]
    rw [integral_const_mul]
    congr 1
    rw [← hX_law i, integral_map (hX_meas i).aemeasurable (hF_meas k).aestronglyMeasurable]
  -- Pointwise: the LHS integrand is the centered-sum norm on `ι → ℝ`.
  have hpt_L : ∀ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|
      = ‖∑ i, (Z i ω - ∫ z, z ∂(μ.map (Z i)))‖ := by
    intro ω
    rw [pi_norm_eq_ciSup_abs]
    refine iSup_congr fun k => ?_
    congr 1
    have e1 : ∀ i : Fin n, (Z i ω - ∫ z, z ∂(μ.map (Z i))) k
        = (n : ℝ)⁻¹ * F k (X i ω) - (n : ℝ)⁻¹ * ∫ x, F k x ∂P := by
      intro i
      rw [Pi.sub_apply, hc i k]
    rw [Finset.sum_apply, Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_sub_distrib,
      Finset.sum_const, ← Finset.mul_sum, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  -- Pointwise: the RHS integrand is the sign-randomized sum norm.
  have hpt_R : ∀ p : Ω × (Fin n → ℝ),
      ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)| = ‖∑ i, p.2 i • Z i p.1‖ := by
    intro p
    rw [pi_norm_eq_ciSup_abs]
    refine iSup_congr fun k => ?_
    congr 1
    rw [Finset.sum_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.smul_apply, smul_eq_mul]
    simp only [hZ]
    ring
  -- Measurability of the two integrands over the canonical products.
  have hG : AEStronglyMeasurable
      (fun y : Fin n → (ι → ℝ) => ‖∑ i, (y i - ∫ z, z ∂(μ.map (Z i)))‖)
      (Measure.pi fun i => μ.map (Z i)) := by
    have hm : Measurable
        (fun y : Fin n → (ι → ℝ) => ∑ i, (y i - ∫ z, z ∂(μ.map (Z i)))) :=
      Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).sub measurable_const)
    exact hm.norm.aestronglyMeasurable
  have hH : AEStronglyMeasurable
      (fun q : (Fin n → (ι → ℝ)) × (Fin n → ℝ) => ‖∑ i, q.2 i • q.1 i‖)
      ((Measure.pi fun i => μ.map (Z i)).prod (signVec n)) := by
    have hm : Measurable
        (fun q : (Fin n → (ι → ℝ)) × (Fin n → ℝ) => ∑ i, q.2 i • q.1 i) := by
      apply Finset.measurable_sum
      intro i _
      exact ((measurable_pi_apply i).comp measurable_snd).smul
        ((measurable_pi_apply i).comp measurable_fst)
    exact hm.norm.aestronglyMeasurable
  -- Transport both sides to the canonical product laws.
  have hLHS : ∫ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| ∂μ
      = ∫ y, ‖∑ i, (y i - ∫ z, z ∂(μ.map (Z i)))‖
          ∂(Measure.pi fun i => μ.map (Z i)) := by
    rw [integral_congr_ae (ae_of_all _ hpt_L)]
    exact integral_eq_integral_pi_map (fun i => (hZ_meas i).aemeasurable) hZ_indep hG
  have hRHS : ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)| ∂(μ.prod (signVec n))
      = ∫ q, ‖∑ i, q.2 i • q.1 i‖
          ∂((Measure.pi fun i => μ.map (Z i)).prod (signVec n)) := by
    rw [integral_congr_ae (ae_of_all _ hpt_R)]
    exact integral_prod_eq_integral_pi_prod hZ_meas hZ_indep hH
  rw [hLHS, hRHS]
  exact symmetrization_upper_pi (fun i => μ.map (Z i)) hν_int

/-- Subtype-indexed `iSup` over a `Finset` equals `Finset.sup'` (no junk value,
since the index is exactly the finite carrier). Bridges the finite core's
`⨆ k : ↥s` output to the `Finset.sup'` form used by the monotone-convergence
exhaustion machinery. -/
private lemma biSup_coe_finset_eq_sup' {ι : Type*} {s : Finset ι} (hne : s.Nonempty)
    (f : ι → ℝ) :
    (⨆ (k : {x // x ∈ s}), f k.val) = s.sup' hne f := by
  haveI : Nonempty {x // x ∈ s} := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hbdd : BddAbove (Set.range fun k : {x // x ∈ s} => f k.val) := by
    refine ⟨s.sup' hne f, ?_⟩
    rintro y ⟨⟨x, hx⟩, rfl⟩
    exact Finset.le_sup' f hx
  apply le_antisymm
  · exact ciSup_le (fun k => Finset.le_sup' f k.2)
  · exact Finset.sup'_le hne f (fun x hx => le_ciSup hbdd ⟨x, hx⟩)

/-- **Symmetrization for empirical processes, countable class** (HDP §8.3,
Exercise 8.11): the `Countable ι` lift of `empirical_symmetrization` per the
batch sup policy, by exhaustion along a surjective enumeration + dominated
convergence (constant dominators from the class bound). Named-sorry debt
candidate of this work item. -/
theorem empirical_symmetrization_countable {α : Type*} [MeasurableSpace α]
    {ι : Type*} [Countable ι] [Nonempty ι] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} [NeZero n] {X : Fin n → Ω → α}
    {P : Measure α} [IsProbabilityMeasure P]
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent sample; HDP Exercise 8.11
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- USER-INPUT: identically distributed with law P; HDP Exercise 8.11
    (hX_law : ∀ i, μ.map (X i) = P)
    {F : ι → α → ℝ}
    -- LEAN-ONLY: measurability of the class members
    (hF_meas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniformly bounded (Boolean) class, |f_k| ≤ 1; HDP Exercise 8.11
    (hF_bdd : ∀ k x, |F k x| ≤ 1) :
    ∫ ω, ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| ∂μ
      ≤ 2 * ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|
          ∂(μ.prod (signVec n)) := by
  classical
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- Surjective enumeration of the countable index and its prefix Finsets.
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  set Fm : ℕ → Finset ι := fun m => (Finset.range (m + 1)).image e with hFm_def
  have hFm_ne : ∀ m, (Fm m).Nonempty := fun m =>
    ⟨e 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos m), rfl⟩⟩
  have hFm_mono : Monotone Fm := by
    intro m m' hmm
    apply Finset.image_subset_image
    intro x hx; rw [Finset.mem_range] at hx ⊢
    exact lt_of_lt_of_le hx (Nat.succ_le_succ hmm)
  -- Integrability of the class members under `P`, and `|∫ f_k dP| ≤ 1`.
  have hFk_int : ∀ k, Integrable (F k) P := fun k =>
    (integrable_const (1 : ℝ)).mono' (hF_meas k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hF_bdd k x))
  have hint_abs_le : ∀ k, |∫ x, F k x ∂P| ≤ 1 := by
    intro k
    calc |∫ x, F k x ∂P| ≤ ∫ x, |F k x| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ _x, (1 : ℝ) ∂P := integral_mono (hFk_int k).abs (integrable_const 1)
            (fun x => hF_bdd k x)
      _ = 1 := by simp
  -- The LHS integrand summands are in `[0, 2]`.
  have hLg_le2 : ∀ k ω, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| ≤ 2 := by
    intro k ω
    have hA : |(n : ℝ)⁻¹ * (∑ i, F k (X i ω))| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)⁻¹ by positivity)]
      have hsum : |∑ i, F k (X i ω)| ≤ (n : ℝ) := by
        calc |∑ i, F k (X i ω)| ≤ ∑ i, |F k (X i ω)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hF_bdd k (X i ω))
          _ = (n : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      calc (n : ℝ)⁻¹ * |∑ i, F k (X i ω)| ≤ (n : ℝ)⁻¹ * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 1 := inv_mul_cancel₀ hn
    have hB : |∫ x, F k x ∂P| ≤ 1 := hint_abs_le k
    calc |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|
        ≤ |(n : ℝ)⁻¹ * (∑ i, F k (X i ω))| + |∫ x, F k x ∂P| := by
          rw [sub_eq_add_neg]; exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
      _ ≤ 1 + 1 := add_le_add hA hB
      _ = 2 := by norm_num
  have hLg_meas : ∀ k, Measurable
      (fun ω => |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) := by
    intro k
    apply Measurable.abs
    apply Measurable.sub _ measurable_const
    apply Measurable.const_mul
    exact Finset.measurable_sum Finset.univ (fun i _ => (hF_meas k).comp (hX_meas i))
  have hbddL : ∀ ω, BddAbove
      (Set.range fun k => |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) :=
    fun ω => ⟨2, by rintro y ⟨k, rfl⟩; exact hLg_le2 k ω⟩
  have hL_int : Integrable
      (fun ω => ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) μ := by
    have haem : AEMeasurable
        (fun ω => ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) μ :=
      AEMeasurable.iSup (fun k => (hLg_meas k).aemeasurable)
    refine Integrable.mono' (integrable_const (2 : ℝ)) haem.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    have h0 : (0 : ℝ) ≤ ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P| :=
      le_ciSup_of_le (hbddL ω) (Classical.arbitrary ι) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact ciSup_le (fun k => hLg_le2 k ω)
  -- Finite prefix maxima on the LHS.
  set netL : ℕ → Ω → ℝ :=
    fun m ω => (Fm m).sup' (hFm_ne m)
      (fun k => |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) with hnetL
  have hnetL_nonneg : ∀ m ω, 0 ≤ netL m ω := by
    intro m ω; simp only [hnetL]
    obtain ⟨k, hk⟩ := hFm_ne m
    exact le_trans (abs_nonneg _) (Finset.le_sup'
      (fun k => |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) hk)
  have hnetL_le2 : ∀ m ω, netL m ω ≤ 2 := by
    intro m ω; simp only [hnetL]
    exact Finset.sup'_le (hFm_ne m) _ (fun k _ => hLg_le2 k ω)
  have hnetL_meas : ∀ m, Measurable (netL m) := by
    intro m
    have hEq : netL m = (Fm m).sup' (hFm_ne m)
        (fun k => fun ω => |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) := by
      funext ω; simp only [hnetL, Finset.sup'_apply]
    rw [hEq]
    exact Finset.measurable_sup' (hFm_ne m) (fun k _ => hLg_meas k)
  have hnetL_int : ∀ m, Integrable (netL m) μ := by
    intro m
    refine Integrable.mono' (integrable_const (2 : ℝ)) (hnetL_meas m).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnetL_nonneg m ω)]
    exact hnetL_le2 m ω
  have hnetL_mono : ∀ ω, Monotone (fun m => netL m ω) := by
    intro ω m m' hmm; simp only [hnetL]
    exact Finset.sup'_mono _ (hFm_mono hmm) (hFm_ne m)
  have hbddNetL : ∀ ω, BddAbove (Set.range fun m => netL m ω) :=
    fun ω => ⟨2, by rintro y ⟨m, rfl⟩; exact hnetL_le2 m ω⟩
  have hsupL : ∀ ω,
      (⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|) = ⨆ m, netL m ω := by
    intro ω
    apply le_antisymm
    · refine ciSup_le (fun k => ?_)
      obtain ⟨j, rfl⟩ := he k
      refine le_ciSup_of_le (hbddNetL ω) j ?_
      simp only [hnetL]
      exact Finset.le_sup' (fun k => |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|)
        (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), rfl⟩)
    · refine ciSup_le (fun m => ?_)
      simp only [hnetL]
      exact Finset.sup'_le (hFm_ne m) _ (fun k _ => le_ciSup (hbddL ω) k)
  -- The RHS: a.e. the sign coordinates are `±1`, so the integrand summands are in `[0, 1]`.
  have hRg_meas : ∀ k, Measurable
      (fun p : Ω × (Fin n → ℝ) => |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) := by
    intro k
    apply Measurable.abs
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact ((measurable_pi_apply i).comp measurable_snd).mul
      ((hF_meas k).comp ((hX_meas i).comp measurable_fst))
  have hbddR : ∀ p : Ω × (Fin n → ℝ), BddAbove
      (Set.range fun k => |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) := by
    intro p
    refine ⟨(n : ℝ)⁻¹ * ∑ i, |p.2 i|, ?_⟩
    rintro y ⟨k, rfl⟩
    dsimp only
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)⁻¹ by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc |∑ i, p.2 i * F k (X i p.1)| ≤ ∑ i, |p.2 i * F k (X i p.1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |p.2 i| := Finset.sum_le_sum (fun i _ => by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hF_bdd k (X i p.1)))
  have hae_pm := (Measure.quasiMeasurePreserving_snd
    (μ := μ) (ν := signVec n)).tendsto_ae.eventually (signVec_ae_pm n)
  have hR_bound_ae : ∀ᵐ p ∂(μ.prod (signVec n)),
      (⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) ≤ 1 := by
    filter_upwards [hae_pm] with p hp
    refine ciSup_le (fun k => ?_)
    rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)⁻¹ by positivity)]
    have hs : |∑ i, p.2 i * F k (X i p.1)| ≤ (n : ℝ) := by
      calc |∑ i, p.2 i * F k (X i p.1)| ≤ ∑ i, |p.2 i * F k (X i p.1)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [abs_mul]
            have h1 : |p.2 i| = 1 := by rcases hp i with h | h <;> rw [h] <;> norm_num
            rw [h1, one_mul]; exact hF_bdd k (X i p.1)
        _ = (n : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    calc (n : ℝ)⁻¹ * |∑ i, p.2 i * F k (X i p.1)| ≤ (n : ℝ)⁻¹ * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 1 := inv_mul_cancel₀ hn
  have hR_int : Integrable
      (fun p => ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) (μ.prod (signVec n)) := by
    have haem : AEMeasurable
        (fun p => ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) (μ.prod (signVec n)) :=
      AEMeasurable.iSup (fun k => (hRg_meas k).aemeasurable)
    refine Integrable.mono' (integrable_const (1 : ℝ)) haem.aestronglyMeasurable ?_
    filter_upwards [hR_bound_ae] with p hp
    rw [Real.norm_eq_abs,
      abs_of_nonneg (le_ciSup_of_le (hbddR p) (Classical.arbitrary ι) (abs_nonneg _))]
    exact hp
  -- Finite prefix maxima on the RHS.
  set netR : ℕ → (Ω × (Fin n → ℝ)) → ℝ :=
    fun m p => (Fm m).sup' (hFm_ne m)
      (fun k => |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) with hnetR
  have hnetR_nonneg : ∀ m p, 0 ≤ netR m p := by
    intro m p; simp only [hnetR]
    obtain ⟨k, hk⟩ := hFm_ne m
    exact le_trans (abs_nonneg _) (Finset.le_sup'
      (fun k => |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) hk)
  have hnetR_le : ∀ m p,
      netR m p ≤ ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)| := by
    intro m p; simp only [hnetR]
    exact Finset.sup'_le (hFm_ne m) _ (fun k _ => le_ciSup (hbddR p) k)
  have hnetR_meas : ∀ m, Measurable (netR m) := by
    intro m
    have hEq : netR m = (Fm m).sup' (hFm_ne m)
        (fun k => fun p => |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)|) := by
      funext p; simp only [hnetR, Finset.sup'_apply]
    rw [hEq]
    exact Finset.measurable_sup' (hFm_ne m) (fun k _ => hRg_meas k)
  have hnetR_int : ∀ m, Integrable (netR m) (μ.prod (signVec n)) := by
    intro m
    refine hR_int.mono' (hnetR_meas m).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnetR_nonneg m p)]
    exact hnetR_le m p
  have hRint_mono : ∀ m,
      ∫ p, netR m p ∂(μ.prod (signVec n))
        ≤ ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)| ∂(μ.prod (signVec n)) :=
    fun m => integral_mono (hnetR_int m) hR_int (hnetR_le m)
  -- The finite core applied to each prefix subtype.
  have hfin_step : ∀ m,
      ∫ ω, netL m ω ∂μ ≤ 2 * ∫ p, netR m p ∂(μ.prod (signVec n)) := by
    intro m
    haveI : Nonempty {x // x ∈ Fm m} := ⟨⟨(hFm_ne m).choose, (hFm_ne m).choose_spec⟩⟩
    have hcore := empirical_symmetrization (μ := μ) (P := P) (n := n) (X := X)
      (ι := {x // x ∈ Fm m}) hX_meas hX_indep hX_law
      (F := fun k : {x // x ∈ Fm m} => F k.val)
      (fun k => hF_meas k.val) (fun k x => hF_bdd k.val x)
    have eL : ∫ ω, netL m ω ∂μ
        = ∫ ω, ⨆ (k : {x // x ∈ Fm m}),
            |(n : ℝ)⁻¹ * (∑ i, F k.val (X i ω)) - ∫ x, F k.val x ∂P| ∂μ := by
      apply integral_congr_ae; filter_upwards with ω
      simp only [hnetL]
      exact (biSup_coe_finset_eq_sup' (hFm_ne m) _).symm
    have eR : ∫ p, netR m p ∂(μ.prod (signVec n))
        = ∫ p, ⨆ (k : {x // x ∈ Fm m}),
            |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k.val (X i p.1)| ∂(μ.prod (signVec n)) := by
      apply integral_congr_ae; filter_upwards with p
      simp only [hnetR]
      exact (biSup_coe_finset_eq_sup' (hFm_ne m) _).symm
    rw [eL, eR]; exact hcore
  -- Each prefix bound is dominated by the (countable) RHS target.
  have key : ∀ m, ∫ ω, netL m ω ∂μ
      ≤ 2 * ∫ p, ⨆ k, |(n : ℝ)⁻¹ * ∑ i, p.2 i * F k (X i p.1)| ∂(μ.prod (signVec n)) :=
    fun m => (hfin_step m).trans
      (mul_le_mul_of_nonneg_left (hRint_mono m) (by norm_num))
  -- Monotone convergence lifts the prefix bounds to the countable sup.
  have hlim := integral_tendsto_of_tendsto_of_monotone (μ := μ) (f := fun m ω => netL m ω)
    (F := fun ω => ⨆ k, |(n : ℝ)⁻¹ * (∑ i, F k (X i ω)) - ∫ x, F k x ∂P|)
    hnetL_int hL_int (Filter.Eventually.of_forall hnetL_mono)
    (Filter.Eventually.of_forall (fun ω => by
      rw [hsupL ω]; exact tendsto_atTop_ciSup (hnetL_mono ω) (hbddNetL ω)))
  exact le_of_tendsto hlim (Filter.Eventually.of_forall key)

end StatLean.ConcentrationInequalities
