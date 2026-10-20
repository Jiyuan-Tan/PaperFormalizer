module
public import StatLean.CausalInference.Observational.ATT

@[expose] public section

/-!
# Overlap and trimming — bounded weights, and the estimand you actually get

Limited overlap is the practical failure mode of weighting: as `e(X)` approaches `0` or
`1` the inverse-probability weights explode. Two responses, and their consequences:

* **Strict overlap** `η ≤ e(X) ≤ 1 - η` bounds every weight by `1/η`, which is what makes
  weighting estimators stable.
* **Trimming** — discarding units outside a propensity range — restores stability but
  **changes the estimand**: what is identified afterwards is the average causal effect
  *over the retained subpopulation*, not `τ`. The overlap-weighted estimand `τ_O` is the
  smooth version of the same idea.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). §11.2.3 (pp. 160–161: the strong overlap condition
`0 < α_L ≤ e(X) ≤ α_U < 1`, stated as an unlabeled display, and the weight blow-up with
truncation/trimming as remedies); ch. 20 (*Overlap in Observational Studies*),
**Assumption 20.1** (§20.1, p. 267: strict overlap `η ≤ e(X) ≤ 1 - η`, `η ∈ (0, 1/2)`);
**Theorem 13.4** and its table (p. 188: the `h`-weighted estimands, whose overlap row is
`h(X) = e(X){1 - e(X)}`, giving
`τ_O = E[e(1-e)τ(X)]/E[e(1-e)]`, with the noted reduction to `τ` when `τ(X)` is constant).
(`Ding §11.2.3; Assumption 20.1; Theorem 13.4`.) Assessing overlap and trimming are chs. 14
and 16 of G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and
Biomedical Sciences*, Cambridge University Press, 2015. (`IR chs. 14, 16`.)

**Scope.** That "trimming changes the estimand" is **prose** in both references (Ding
§11.2.3 p. 161 and §20.1.1 p. 268 discuss it and cite Crump et al. (2009) and Yang–Ding
(2018) rather than proving an in-book theorem). What is formalized here is the precise
version of that statement: the trimmed identification formula equals the average causal
effect *conditional on the retained set* (`trimmedEstimand_eq_cate_of_trimmedSet`), which
differs from `τ` unless the conditional effect is constant. Ding's **Theorem 20.1** (the
covariate-imbalance bound under strict overlap) is not formalized: it depends on
distributional constants imported from D'Amour et al. (2021) that the book does not develop.

**Proof formalization notes.** The trimmed population is the union of the covariate cells
whose propensity lies in `[η, 1-η]`; conditioning on it is `ProbabilityTheory.cond` on that
union, so the "changed estimand" statement is an application of
`Standardization.ate_eq_sum_cate` restricted to those cells. The weight bounds are pointwise
arithmetic from `StronglyOverlapping`.

**Bibliographic comments.** The optimal trimming rule is R. K. Crump, V. J. Hotz,
G. W. Imbens and O. A. Mitnik, "Dealing with limited overlap in estimation of average
treatment effects," *Biometrika* **96** (2009), 187–199; overlap weights are F. Li,
K. L. Morgan and A. M. Zaslavsky, *J. Amer. Statist. Assoc.* **113** (2018), 390–400;
the strict-overlap critique is A. D'Amour, P. Ding, A. Feller, L. Lei and J. Sekhon,
"Overlap in observational studies with high-dimensional covariates," *J. Econometrics*
**221** (2021), 644–654.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {𝒳 : Type*} [MeasurableSpace 𝒳] [Fintype 𝒳]
  [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {Z : Ω → Bool} {y1 y0 : Ω → ℝ} {X : Ω → 𝒳}

/-- The **retained (trimmed) population**: the units whose covariate cell has propensity
score in `[η, 1 - η]` (Ding §11.2.3, Assumption 20.1). -/
def trimmedSet (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (η : ℝ) : Set Ω :=
  {ω | η ≤ propensity μ Z X (X ω) ∧ propensity μ Z X (X ω) ≤ 1 - η}

/-! ### Private infrastructure

Three bricks, all about *functions of the covariate*. A function `g : 𝒳 → ℝ` composed with
`X` is automatically measurable and bounded (`𝒳` is finite), hence integrable against any
finite measure; and inside a covariate cell of positive mass it is a.e. constant, so it
factors out of the conditional integral. The third brick is the partition statement:
`trimmedSet` is the union of the retained cells, which is what turns the trimmed integral
into a finite sum. -/

/-- A function of a finite covariate is integrable against any finite measure. -/
private lemma integrable_comp_of_finite [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ) :
    Integrable (fun ω => g (X ω)) μ := by
  refine Integrable.mono' (integrable_const (∑ x : 𝒳, |g x|))
    (((measurable_of_finite g).comp hX)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simpa using
    Finset.single_le_sum (f := fun x => |g x|) (fun i _ => abs_nonneg _) (Finset.mem_univ (X ω))

/-- Inside a covariate cell of positive mass, a function of the covariate is a.e. constant,
so its conditional mean is its value there. -/
private lemma integral_comp_cond_cell [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ)
    {x : 𝒳} (hc : μ (cell X x) ≠ 0) :
    ∫ ω, g (X ω) ∂(μ[|cell X x]) = g x := by
  haveI : IsProbabilityMeasure (μ[|cell X x]) := cond_isProbabilityMeasure hc
  have hae : ∀ᵐ ω ∂(μ[|cell X x]), g (X ω) = g x := by
    filter_upwards [ae_cond_mem (hX (measurableSet_singleton x))] with ω hω
    have hXω : X ω = x := hω
    rw [hXω]
  rw [integral_congr_ae hae, integral_const]
  simp

/-- Inside a covariate cell, a function of the covariate is a.e. constant, so it factors
out of the conditional integral. -/
private lemma integral_comp_mul_cond_cell [IsFiniteMeasure μ] (hX : Measurable X) (g : 𝒳 → ℝ)
    (f : Ω → ℝ) (x : 𝒳) :
    ∫ ω, g (X ω) * f ω ∂(μ[|cell X x]) = g x * ∫ ω, f ω ∂(μ[|cell X x]) := by
  have hae : ∀ᵐ ω ∂(μ[|cell X x]), g (X ω) * f ω = g x * f ω := by
    filter_upwards [ae_cond_mem (hX (measurableSet_singleton x))] with ω hω
    have hXω : X ω = x := hω
    rw [hXω]
  rw [integral_congr_ae hae]
  exact integral_const_mul (g x) f

/-- The covariate cells are pairwise disjoint. -/
private lemma cell_pairwiseDisjoint (X : Ω → 𝒳) (F : Finset 𝒳) :
    (F : Set 𝒳).PairwiseDisjoint (cell X) := by
  intro a _ b _ hab
  simp only [Function.onFun, Set.disjoint_left, cell, Set.mem_preimage, Set.mem_singleton_iff]
  intro ω ha hb
  exact hab (ha.symm.trans hb)

/-- The retained population is the union of the retained covariate cells. -/
private lemma trimmedSet_eq_biUnion [DecidableEq 𝒳] (μ : Measure Ω) (Z : Ω → Bool)
    (X : Ω → 𝒳) (η : ℝ) :
    trimmedSet μ Z X η
      = ⋃ x ∈ Finset.univ.filter fun x =>
            η ≤ propensity μ Z X x ∧ propensity μ Z X x ≤ 1 - η, cell X x := by
  ext ω
  simp only [trimmedSet, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, cell, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
  exact ⟨fun h => ⟨X ω, h, rfl⟩, fun ⟨_, hx, hxe⟩ => hxe ▸ hx⟩

/-- The mass of the retained population is the sum of the masses of the retained cells. -/
private lemma measureReal_trimmedSet_eq_sum [IsProbabilityMeasure μ] [DecidableEq 𝒳] {η : ℝ}
    (hX : Measurable X) :
    (μ (trimmedSet μ Z X η)).toReal
      = ∑ x ∈ Finset.univ.filter fun x =>
            η ≤ propensity μ Z X x ∧ propensity μ Z X x ≤ 1 - η, (μ (cell X x)).toReal := by
  rw [trimmedSet_eq_biUnion, measure_biUnion_finset (cell_pairwiseDisjoint X _)
    (fun x _ => hX (measurableSet_singleton x)),
    ENNReal.toReal_sum (fun x _ => measure_ne_top μ _)]

/-- **A homogeneous conditional effect is the average causal effect.** The cell weights sum
to one, and null cells contribute `0`, so no hypothesis is needed off the support. -/
private lemma ate_eq_of_constant_cate [IsProbabilityMeasure μ] {τ : ℝ} (hX : Measurable X)
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    (hconst : ∀ x : 𝒳, μ (cell X x) ≠ 0 → cate μ X y1 y0 x = τ) :
    ate μ y1 y0 = τ := by
  have hsum_one : ∑ x : 𝒳, (μ (cell X x)).toReal = 1 := by
    have hEq : ∑ x : 𝒳, μ (cell X x) = 1 := by
      have h := sum_measure_preimage_singleton (μ := μ) (f := X) Finset.univ
        (fun x _ => hX (measurableSet_singleton x))
      simpa [cell] using h
    rw [← ENNReal.toReal_sum (fun x _ => measure_ne_top μ _), hEq]
    simp
  have hterm : ∀ x ∈ (Finset.univ : Finset 𝒳),
      (μ (cell X x)).toReal * cate μ X y1 y0 x = τ * (μ (cell X x)).toReal := by
    intro x _
    rcases eq_or_ne (μ (cell X x)) 0 with hc | hc
    · rw [hc]; simp
    · rw [hconst x hc]; ring
  rw [ate_eq_sum_cate hX hint, Finset.sum_congr rfl hterm, ← Finset.mul_sum, hsum_one, mul_one]

/-- **Every `h`-weighted estimand collapses to the common conditional effect.** The weight
cancels between numerator and denominator once `τ(x)` no longer depends on `x`; this is
the general statement behind both the trimmed and the overlap-weighted reductions. -/
private lemma weightedATE_eq_of_constant_cate [IsProbabilityMeasure μ] {τ : ℝ}
    (hX : Measurable X) (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    (hconst : ∀ x : 𝒳, μ (cell X x) ≠ 0 → cate μ X y1 y0 x = τ) (g : 𝒳 → ℝ)
    (hg : ∫ ω, g (X ω) ∂μ ≠ 0) :
    weightedATE μ X y1 y0 g = τ := by
  have hbd : ∀ ω, ‖g (X ω)‖ ≤ ∑ x : 𝒳, |g x| := fun ω => by
    simpa using
      Finset.single_le_sum (f := fun x => |g x|) (fun i _ => abs_nonneg _) (Finset.mem_univ (X ω))
  have hgint : Integrable (fun ω => g (X ω)) μ := integrable_comp_of_finite hX g
  have hprod : Integrable (fun ω => g (X ω) * (y1 ω - y0 ω)) μ :=
    hint.bdd_mul ((measurable_of_finite g).comp hX).aestronglyMeasurable (ae_of_all _ hbd)
  have hnum : ∫ ω, g (X ω) * (y1 ω - y0 ω) ∂μ = τ * ∫ ω, g (X ω) ∂μ := by
    rw [integral_eq_sum_cell hX hprod, integral_eq_sum_cell hX hgint, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show (μ (cell X x)).toReal * ∫ ω, g (X ω) * (y1 ω - y0 ω) ∂(μ[|cell X x])
      = τ * ((μ (cell X x)).toReal * ∫ ω, g (X ω) ∂(μ[|cell X x]))
    rcases eq_or_ne (μ (cell X x)) 0 with hc | hc
    · rw [hc]; simp
    · rw [integral_comp_mul_cond_cell hX g _ x, integral_comp_cond_cell hX g hc,
        show ∫ ω, (y1 ω - y0 ω) ∂(μ[|cell X x]) = τ from hconst x hc]
      ring
  show (∫ ω, g (X ω) * (y1 ω - y0 ω) ∂μ) / (∫ ω, g (X ω) ∂μ) = τ
  rw [hnum, mul_div_assoc, div_self hg, mul_one]

/-- **Strict overlap bounds the treated weight** (Ding Assumption 20.1): under
`η ≤ e(X) ≤ 1 - η` every inverse-probability weight is at most `1/η`. -/
theorem inv_propensity_le_of_mem_trimmedSet {η : ℝ}
    -- LEAN-ONLY: a positive trimming threshold, so `1/η` is finite
    (hη : 0 < η) {ω : Ω} (hω : ω ∈ trimmedSet μ Z X η) :
    1 / propensity μ Z X (X ω) ≤ 1 / η :=
  one_div_le_one_div_of_le hη hω.1

/-- **Strict overlap bounds the control weight** (Ding Assumption 20.1). -/
theorem inv_one_sub_propensity_le_of_mem_trimmedSet {η : ℝ} (hη : 0 < η) {ω : Ω}
    (hω : ω ∈ trimmedSet μ Z X η) :
    1 / (1 - propensity μ Z X (X ω)) ≤ 1 / η :=
  one_div_le_one_div_of_le hη (by linarith [hω.2])

/-- Strict overlap in the sense of `StronglyOverlapping` means every unit that carries mass
is retained by trimming at the same threshold. -/
theorem stronglyOverlapping_iff_trimmedSet {η : ℝ} (hX : Measurable X) :
    StronglyOverlapping μ Z X η ↔ ∀ x : 𝒳, μ (cell X x) ≠ 0 → cell X x ⊆ trimmedSet μ Z X η := by
  constructor
  · -- Every point of the cell carries the cell's propensity value.
    intro h x hx ω hω
    have hXω : X ω = x := hω
    obtain ⟨h1, h2⟩ := h x hx
    exact ⟨by rw [hXω]; exact h1, by rw [hXω]; exact h2⟩
  · -- A cell of positive mass is nonempty, and any of its points witnesses the bounds.
    intro h x hx
    obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hx
    have hXω : X ω = x := hω
    obtain ⟨h1, h2⟩ := h x hx hω
    rw [hXω] at h1 h2
    exact ⟨h1, h2⟩

/-- The **trimmed estimand**: the average causal effect over the retained population. -/
noncomputable def trimmedATE (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳) (y1 y0 : Ω → ℝ)
    (η : ℝ) : ℝ :=
  ∫ ω, (y1 ω - y0 ω) ∂(μ[|trimmedSet μ Z X η])

/-- **Trimming changes the estimand** (Ding §11.2.3, §20.1.1 — the precise form of the
book's prose warning): what the trimmed analysis identifies is the average causal effect
*conditional on the retained set*, i.e. the cell-weighted average of the conditional
effects over retained cells only. -/
theorem trimmedATE_eq_sum_cate [IsProbabilityMeasure μ] [DecidableEq 𝒳] {η : ℝ}
    (hZ : Measurable Z) (hX : Measurable X)
    -- USER-INPUT: integrability of the individual effect
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    -- USER-INPUT: the retained population is nonnull, else the estimand is a junk value
    (hne : μ (trimmedSet μ Z X η) ≠ 0) :
    trimmedATE μ Z X y1 y0 η
      = (∑ x ∈ Finset.univ.filter fun x =>
            η ≤ propensity μ Z X x ∧ propensity μ Z X x ≤ 1 - η,
          (μ (cell X x)).toReal * cate μ X y1 y0 x)
        / (μ (trimmedSet μ Z X η)).toReal := by
  rw [trimmedATE, integral_cond_eq_setIntegral, div_eq_inv_mul]
  congr 1
  rw [trimmedSet_eq_biUnion, integral_biUnion_finset (s := cell X)
    (Finset.univ.filter fun x => η ≤ propensity μ Z X x ∧ propensity μ Z X x ≤ 1 - η)
    (fun x _ => hX (measurableSet_singleton x))
    (cell_pairwiseDisjoint X _) (fun x _ => hint.integrableOn)]
  exact Finset.sum_congr rfl fun x _ =>
    (measureReal_mul_integral_cond (measure_ne_top μ _) _).symm

/-- **Trimming is harmless exactly when the effect is homogeneous**: if the conditional
average causal effect is constant, the trimmed estimand is the average causal effect. This
is the precise sense in which trimming "does not change the estimand" only under effect
homogeneity. -/
theorem trimmedATE_eq_ate_of_constant_cate [IsProbabilityMeasure μ] [DecidableEq 𝒳] {η τ : ℝ}
    (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    (hne : μ (trimmedSet μ Z X η) ≠ 0)
    -- USER-INPUT: a homogeneous conditional effect; Ding Theorem 13.4's remark
    (hconst : ∀ x : 𝒳, μ (cell X x) ≠ 0 → cate μ X y1 y0 x = τ) :
    trimmedATE μ Z X y1 y0 η = ate μ y1 y0 := by
  have hM : (μ (trimmedSet μ Z X η)).toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, hne, measure_ne_top]
  -- The retained cells all carry the same conditional effect, so the numerator is
  -- `τ` times the retained mass. Null cells contribute `0` and need no hypothesis.
  have hnum : (∑ x ∈ Finset.univ.filter fun x =>
        η ≤ propensity μ Z X x ∧ propensity μ Z X x ≤ 1 - η,
      (μ (cell X x)).toReal * cate μ X y1 y0 x)
      = τ * (μ (trimmedSet μ Z X η)).toReal := by
    rw [measureReal_trimmedSet_eq_sum (Z := Z) hX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases eq_or_ne (μ (cell X x)) 0 with hc | hc
    · rw [hc]; simp
    · rw [hconst x hc]; ring
  rw [trimmedATE_eq_sum_cate hZ hX hint hne, hnum, mul_div_assoc, div_self hM, mul_one,
    ate_eq_of_constant_cate hX hint hconst]

/-- The **overlap-weighted estimand** `τ_O` (Ding Theorem 13.4's table, p. 188): the
smooth alternative to hard trimming, with weight `h(x) = e(x)(1 - e(x))` that downweights
extreme propensity scores. -/
noncomputable def overlapATE (μ : Measure Ω) (Z : Ω → Bool) (X : Ω → 𝒳)
    (y1 y0 : Ω → ℝ) : ℝ :=
  weightedATE μ X y1 y0 fun x => propensity μ Z X x * (1 - propensity μ Z X x)

/-- **The overlap-weighted estimand reduces to the average causal effect under a
homogeneous conditional effect** (Ding p. 188, the remark following Theorem 13.4's table).
-/
theorem overlapATE_eq_ate_of_constant_cate [IsProbabilityMeasure μ] {τ : ℝ}
    (hZ : Measurable Z) (hX : Measurable X)
    (hint : Integrable (fun ω => y1 ω - y0 ω) μ)
    -- USER-INPUT: a homogeneous conditional effect; Ding p. 188
    (hconst : ∀ x : 𝒳, μ (cell X x) ≠ 0 → cate μ X y1 y0 x = τ)
    -- USER-INPUT: the overlap weight is not degenerate (some cell has `0 < e(x) < 1`)
    (hw : ∫ ω, propensity μ Z X (X ω) * (1 - propensity μ Z X (X ω)) ∂μ ≠ 0) :
    overlapATE μ Z X y1 y0 = ate μ y1 y0 := by
  rw [overlapATE, weightedATE_eq_of_constant_cate hX hint hconst _ hw,
    ate_eq_of_constant_cate hX hint hconst]

end StatLean.CausalInference
