module
public import StatLean.ConcentrationInequalities.Symmetrization.Rademacher
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# The contraction principle (HDP Theorem 6.6.1)

For fixed vectors $x_1, \dots, x_N$ in a normed space, coefficients
$a \in \mathbb{R}^N$, and independent Rademacher signs $\varepsilon_i$,
$$ \mathbb{E}\Bigl\|\sum_{i=1}^N a_i \varepsilon_i x_i\Bigr\|
   \;\le\; \|a\|_\infty\, \mathbb{E}\Bigl\|\sum_{i=1}^N \varepsilon_i x_i\Bigr\|. $$
The sharp factor $\|a\|_\infty$ is realized as the Mathlib `Fintype` Pi
sup-norm `‖a‖` on `Fin N → ℝ` — no hidden constant. Stated on the canonical
sign space `signVec N`. Forced dependency of the Gaussian symmetrization
Lemma 6.6.2.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, Theorem 6.6.1 (Contraction principle).

**Proof formalization notes.** The book's route — convexity of
$f(a) = \mathbb{E}\|\sum a_i\varepsilon_i x_i\|$ (Ex. 6.35) plus the maximum
principle on the cube (Ex. 1.4/1.5) — is replaced by elementary
single-coordinate convexification with zero uncertain Mathlib bricks: (i) the
"WLOG `‖a‖_∞ ≤ 1`" is an explicit scaling reduction (`norm_smul` +
`integral_const_mul`) with an `a = 0` case split; (ii) inside the cube, pick a
coordinate `i₀` with `a i₀ ∉ {±1}`, write `a i₀ = θ·1 + (1−θ)·(−1)`, bound
pointwise by the triangle inequality *before* integrating, and strong-induct
on the number of non-vertex coordinates; (iii) the vertex case is the change
of variables `signVec_map_mul_pm` (`(aᵢεᵢ) =ᵈ (εᵢ)` for `a ∈ {±1}^N`).
Total for all `N` (both sides `0` at `N = 0`). Named-sorry fallback of this
work item: `contraction_principle_of_abs_le_one` (the cube-normalized
induction core), with the scaling wrapper `contraction_principle` proven from
it.

**Bibliographic comments.** The contraction principle is due to J.-P. Kahane
(*Some Random Series of Functions*, 1968); the general Lipschitz-contraction
form is Ledoux–Talagrand, *Probability in Banach Spaces* (1991), Theorem 4.4.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Continuity of the coefficient-weighted sign combination `s ↦ ∑ (aᵢ sᵢ) xᵢ`. -/
private lemma continuous_sum_coeff_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : ℕ} (x : Fin N → E) (a : Fin N → ℝ) :
    Continuous (fun s : Fin N → ℝ => ∑ i, (a i * s i) • x i) :=
  continuous_finset_sum _ fun i _ =>
    (continuous_const.mul (continuous_apply i)).smul continuous_const

/-- On the `±1`-supported measure `signVec N`, the norm `‖∑ (aᵢ sᵢ) xᵢ‖` is
integrable whenever `|aᵢ| ≤ 1`: it is a.e. bounded by `∑ ‖xᵢ‖`. -/
private lemma integrable_norm_sum_coeff_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : ℕ} (x : Fin N → E) (a : Fin N → ℝ)
    (ha : ∀ i, |a i| ≤ 1) :
    Integrable (fun s : Fin N → ℝ => ‖∑ i, (a i * s i) • x i‖) (signVec N) := by
  refine Integrable.mono' (g := fun _ => ∑ i, ‖x i‖) (integrable_const _)
    (continuous_sum_coeff_smul x a).norm.aestronglyMeasurable ?_
  filter_upwards [signVec_ae_pm N] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc ‖∑ i, (a i * s i) • x i‖
      ≤ ∑ i, ‖(a i * s i) • x i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x i‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul]
        have hsi : |s i| = 1 := by rcases hs i with h | h <;> simp [h]
        calc |a i| * |s i| * ‖x i‖ ≤ 1 * 1 * ‖x i‖ := by
              gcongr
              · exact ha i
              · exact hsi.le
          _ = ‖x i‖ := by ring

/-- The vertex change of variables: for a sign pattern `a ∈ {±1}^N`,
`E‖∑ (aᵢεᵢ) xᵢ‖ = E‖∑ εᵢ xᵢ‖`, via `signVec_map_mul_pm`. -/
private lemma contraction_vertex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} (x : Fin N → E) (a : Fin N → ℝ)
    (hv : ∀ i, a i = 1 ∨ a i = -1) :
    ∫ s, ‖∑ i, (a i * s i) • x i‖ ∂(signVec N)
      = ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) := by
  have hφ : AEMeasurable (fun s : Fin N → ℝ => fun i => a i * s i) (signVec N) :=
    (measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul (a i)).aemeasurable
  have hg : AEStronglyMeasurable (fun s : Fin N → ℝ => ‖∑ i, s i • x i‖)
      ((signVec N).map (fun s i => a i * s i)) :=
    (continuous_finset_sum _ fun i _ =>
      (continuous_apply i).smul continuous_const).norm.aestronglyMeasurable
  conv_rhs => rw [← signVec_map_mul_pm hv]
  rw [integral_map hφ hg]

open Classical in
/-- Card bound for the single-coordinate vertex update: replacing `a i₀` by a
sign `v ∈ {±1}` removes `i₀` from the non-vertex set. -/
private lemma card_filter_update_le {N : ℕ} (a : Fin N → ℝ) (i₀ : Fin N) (v : ℝ)
    (hi0 : i₀ ∈ Finset.univ.filter (fun i => ¬(a i = 1 ∨ a i = -1)))
    (hv : v = 1 ∨ v = -1) :
    (Finset.univ.filter
        (fun i => ¬(Function.update a i₀ v i = 1 ∨ Function.update a i₀ v i = -1))).card
      ≤ (Finset.univ.filter (fun i => ¬(a i = 1 ∨ a i = -1))).card - 1 := by
  have hsub : Finset.univ.filter
        (fun i => ¬(Function.update a i₀ v i = 1 ∨ Function.update a i₀ v i = -1))
      ⊆ (Finset.univ.filter (fun i => ¬(a i = 1 ∨ a i = -1))).erase i₀ := by
    intro j hj
    rw [Finset.mem_filter] at hj
    have hj2 := hj.2
    have hjne : j ≠ i₀ := by
      intro hh; subst hh; rw [Function.update_self] at hj2; exact hj2 hv
    rw [Finset.mem_erase]
    refine ⟨hjne, ?_⟩
    rw [Finset.mem_filter]
    rw [Function.update_of_ne hjne] at hj2
    exact ⟨Finset.mem_univ _, hj2⟩
  calc (Finset.univ.filter
          (fun i => ¬(Function.update a i₀ v i = 1 ∨ Function.update a i₀ v i = -1))).card
      ≤ ((Finset.univ.filter (fun i => ¬(a i = 1 ∨ a i = -1))).erase i₀).card :=
        Finset.card_le_card hsub
    _ = _ := Finset.card_erase_of_mem hi0

/-- **Contraction principle, cube-normalized core** (HDP §6.6,
Theorem 6.6.1): for coefficients in the unit cube (`|aᵢ| ≤ 1`),
`E‖∑ aᵢεᵢxᵢ‖ ≤ E‖∑ εᵢxᵢ‖`. Named-sorry debt candidate of this work item. -/
theorem contraction_principle_of_abs_le_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} {x : Fin N → E} {a : Fin N → ℝ}
    -- USER-INPUT: coefficients in the unit cube (book's WLOG); HDP §6.6 Thm 6.6.1
    (ha : ∀ i, |a i| ≤ 1) :
    ∫ s, ‖∑ i, (a i * s i) • x i‖ ∂(signVec N)
      ≤ ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) := by
  classical
  set RHS := ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) with hRHS
  -- Strong induction on the number of non-vertex coordinates of the coefficient vector.
  suffices key : ∀ k (b : Fin N → ℝ), (∀ i, |b i| ≤ 1) →
      (Finset.univ.filter (fun i => ¬(b i = 1 ∨ b i = -1))).card ≤ k →
      ∫ s, ‖∑ i, (b i * s i) • x i‖ ∂(signVec N) ≤ RHS by
    exact key _ a ha le_rfl
  intro k
  induction k with
  | zero =>
    intro b hb hcard
    have hemp : Finset.univ.filter (fun i => ¬(b i = 1 ∨ b i = -1)) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    have hv : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
      by_contra h; exact Finset.filter_eq_empty_iff.mp hemp (Finset.mem_univ i) h
    rw [contraction_vertex x b hv]
  | succ k ih =>
    intro b hb hcard
    by_cases hemp : Finset.univ.filter (fun i => ¬(b i = 1 ∨ b i = -1)) = ∅
    · have hv : ∀ i, b i = 1 ∨ b i = -1 := fun i => by
        by_contra h; exact Finset.filter_eq_empty_iff.mp hemp (Finset.mem_univ i) h
      rw [contraction_vertex x b hv]
    · -- Pick a non-vertex coordinate `i₀`.
      obtain ⟨i₀, hi0mem⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hi0 := hi0mem
      rw [Finset.mem_filter] at hi0
      -- Convex-combination weight for `b i₀ = θ·1 + (1−θ)·(−1)`.
      have h1 := abs_le.mp (hb i₀)
      set θ : ℝ := (b i₀ + 1) / 2 with hθ
      have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [h1.1]
      have h1θ0 : 0 ≤ 1 - θ := by rw [hθ]; linarith [h1.2]
      -- The two vertex-updated coefficient vectors.
      have ha' : ∀ i, |Function.update b i₀ 1 i| ≤ 1 := fun i => by
        by_cases h : i = i₀
        · subst h; rw [Function.update_self]; norm_num
        · rw [Function.update_of_ne h]; exact hb i
      have ha'' : ∀ i, |Function.update b i₀ (-1) i| ≤ 1 := fun i => by
        by_cases h : i = i₀
        · subst h; rw [Function.update_self]; norm_num
        · rw [Function.update_of_ne h]; exact hb i
      -- Coefficientwise convex-combination identity.
      have hcoef : ∀ i, b i
          = θ * Function.update b i₀ 1 i + (1 - θ) * Function.update b i₀ (-1) i := by
        intro i
        by_cases h : i = i₀
        · subst h; rw [Function.update_self, Function.update_self, hθ]; ring
        · rw [Function.update_of_ne h, Function.update_of_ne h]; ring
      -- Pointwise vector decomposition.
      have hpt : ∀ s : Fin N → ℝ, ∑ i, (b i * s i) • x i
          = θ • (∑ i, (Function.update b i₀ 1 i * s i) • x i)
            + (1 - θ) • (∑ i, (Function.update b i₀ (-1) i * s i) • x i) := by
        intro s
        rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, smul_smul, ← add_smul]
        congr 1
        rw [hcoef i]; ring
      -- Pointwise triangle bound.
      have hnorm : ∀ s : Fin N → ℝ, ‖∑ i, (b i * s i) • x i‖
          ≤ θ * ‖∑ i, (Function.update b i₀ 1 i * s i) • x i‖
            + (1 - θ) * ‖∑ i, (Function.update b i₀ (-1) i * s i) • x i‖ := by
        intro s
        rw [hpt s]
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg hθ0, abs_of_nonneg h1θ0]
      -- Card decrease for the inductive hypotheses.
      have hcard1 := card_filter_update_le b i₀ 1 hi0mem (Or.inl rfl)
      have hcard2 := card_filter_update_le b i₀ (-1) hi0mem (Or.inr rfl)
      have hcard1' : (Finset.univ.filter (fun i =>
          ¬(Function.update b i₀ 1 i = 1 ∨ Function.update b i₀ 1 i = -1))).card ≤ k := by
        omega
      have hcard2' : (Finset.univ.filter (fun i =>
          ¬(Function.update b i₀ (-1) i = 1 ∨ Function.update b i₀ (-1) i = -1))).card ≤ k := by
        omega
      -- Integrability and inductive hypotheses.
      have intA := integrable_norm_sum_coeff_smul x b hb
      have intA' := integrable_norm_sum_coeff_smul x (Function.update b i₀ 1) ha'
      have intA'' := integrable_norm_sum_coeff_smul x (Function.update b i₀ (-1)) ha''
      have hA' := ih (Function.update b i₀ 1) ha' hcard1'
      have hA'' := ih (Function.update b i₀ (-1)) ha'' hcard2'
      calc ∫ s, ‖∑ i, (b i * s i) • x i‖ ∂(signVec N)
          ≤ ∫ s, (θ * ‖∑ i, (Function.update b i₀ 1 i * s i) • x i‖
              + (1 - θ) * ‖∑ i, (Function.update b i₀ (-1) i * s i) • x i‖) ∂(signVec N) :=
            integral_mono intA ((intA'.const_mul θ).add (intA''.const_mul (1 - θ))) hnorm
        _ = θ * ∫ s, ‖∑ i, (Function.update b i₀ 1 i * s i) • x i‖ ∂(signVec N)
              + (1 - θ) * ∫ s, ‖∑ i, (Function.update b i₀ (-1) i * s i) • x i‖ ∂(signVec N) := by
            rw [integral_add (intA'.const_mul θ) (intA''.const_mul (1 - θ)),
              integral_const_mul, integral_const_mul]
        _ ≤ θ * RHS + (1 - θ) * RHS := by
            have t1 := mul_le_mul_of_nonneg_left hA' hθ0
            have t2 := mul_le_mul_of_nonneg_left hA'' h1θ0
            linarith
        _ = RHS := by ring

/-- **Contraction principle** (HDP §6.6, Theorem 6.6.1):
`E‖∑ aᵢεᵢxᵢ‖ ≤ ‖a‖_∞ · E‖∑ εᵢxᵢ‖`, where `‖a‖` is the `Fintype` Pi sup-norm
on `Fin N → ℝ` (the sharp constant). Total in `x` and `a`; both sides vanish
at `N = 0`. -/
theorem contraction_principle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} (x : Fin N → E) (a : Fin N → ℝ) :
    ∫ s, ‖∑ i, (a i * s i) • x i‖ ∂(signVec N)
      ≤ ‖a‖ * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) := by
  rcases eq_or_lt_of_le (norm_nonneg a) with hM0 | hMpos
  · -- Degenerate case `‖a‖ = 0`, i.e. `a = 0`: both sides vanish.
    have ha0 : a = 0 := norm_eq_zero.mp hM0.symm
    subst ha0
    simp
  · -- Non-degenerate case: apply the core to `a / M` and pull `M` out.
    set M := ‖a‖ with hM
    have hMne : M ≠ 0 := ne_of_gt hMpos
    have hb : ∀ i, |a i / M| ≤ 1 := by
      intro i
      rw [abs_div, abs_of_pos hMpos, div_le_one hMpos]
      calc |a i| = ‖a i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖a‖ := norm_le_pi_norm a i
        _ = M := hM.symm
    have hcore : ∫ s, ‖∑ i, ((a i / M) * s i) • x i‖ ∂(signVec N)
        ≤ ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) :=
      contraction_principle_of_abs_le_one (x := x) (a := fun i => a i / M) hb
    -- Norm-homogeneity: `‖∑ ((aᵢ/M) sᵢ) xᵢ‖ = M⁻¹ · ‖∑ (aᵢ sᵢ) xᵢ‖`.
    have hpt : ∀ s : Fin N → ℝ, ‖∑ i, ((a i / M) * s i) • x i‖
        = M⁻¹ * ‖∑ i, (a i * s i) • x i‖ := by
      intro s
      have hsum : ∑ i, ((a i / M) * s i) • x i = M⁻¹ • ∑ i, (a i * s i) • x i := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul]; congr 1; rw [div_eq_inv_mul]; ring
      rw [hsum, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hMpos)]
    have hbint : ∫ s, ‖∑ i, ((a i / M) * s i) • x i‖ ∂(signVec N)
        = M⁻¹ * ∫ s, ‖∑ i, (a i * s i) • x i‖ ∂(signVec N) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    calc ∫ s, ‖∑ i, (a i * s i) • x i‖ ∂(signVec N)
        = M * ∫ s, ‖∑ i, ((a i / M) * s i) • x i‖ ∂(signVec N) := by
          rw [hbint, ← mul_assoc, mul_inv_cancel₀ hMne, one_mul]
      _ ≤ M * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) :=
          mul_le_mul_of_nonneg_left hcore (le_of_lt hMpos)

end StatLean.ConcentrationInequalities
