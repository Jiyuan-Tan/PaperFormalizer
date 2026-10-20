module
public import StatLean.ConcentrationInequalities.VC.LawOfLargeNumbersCountable
public import StatLean.ConcentrationInequalities.ForMathlib.SupRatApprox
public import Mathlib.Probability.CDF

@[expose] public section

/-!
# Glivenko–Cantelli theorem (in expectation)

For i.i.d. real data with common law $\mu$ and empirical CDF $F_n$,
$$ \mathbb{E}\, \|F_n - F\|_\infty
   \;=\; \mathbb{E} \sup_{t \in \mathbb{R}} |F_n(t) - F(t)|
   \;\le\; \frac{5400}{\sqrt{n}}. $$
The class is $\{\mathbf{1}_{(-\infty,\,t]} : t \in \mathbb{R}\}$; its VC
dimension is computed exactly ($= 1$), and the *full uncountable* supremum
over $\mathbb{R}$ is recovered deterministically from the rational
subclass by right-continuity — no countability hypothesis in the headline.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.6, Theorem 8.3.17.

**Proof formalization notes.** Deviations: (1) the book bounds
$\mathrm{vc} \le 2$ via Example 8.3.2; we compute the exact value
`vcDim iicClass = 1` (half-lines cannot realize the labeling
$g(p) = 0, g(q) = 1$ for $p < q$) — documented deviation, giving
`√d = 1`. (2) Frozen numeral `5400/√n` inherited from `vc_lln_countable`
(formula `2 × 40 × √6 × 27`, see `VC/LawOfLargeNumbers.lean`). Sup policy:
`vc_lln_countable` is applied to the countable rational subclass
`iicRatClass`; the ℝ-sup equals the ℚ-sup pointwise by right-continuity of
both the empirical CDF (`empFrac_iic_rightContinuous`, finitely many jumps)
and the population CDF (`real_iic_rightContinuous`, R6 split helper —
`StieltjesFunction` fields of `ProbabilityTheory.cdf`), through the generic
bridge `iSup_eq_iSup_rat_of_right_approx` (`ForMathlib/SupRatApprox.lean`).
Work-item single named-sorry fallback: `iSup_iic_diff_eq_iSup_rat` (the
deterministic ℝ→ℚ sup bridge); `vcDim_iicClass` and the LLN instantiation
must close.

**Bibliographic comments.** V. Glivenko and F. P. Cantelli (1933),
*Giornale dell'Istituto Italiano degli Attuari* 4; the in-expectation
$n^{-1/2}$ form follows the VC route; the sharp constant is the
DKW inequality (Dvoretzky–Kiefer–Wolfowitz 1956, Massart 1990), out of
scope here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

/-- The half-line class `{(-∞, t] : t ∈ ℝ}` (HDP Theorem 8.3.17). -/
def iicClass : Set (Set ℝ) := Set.range Set.Iic

/-- Countable rational subclass (LEAN-ONLY: sup-policy device). -/
def iicRatClass : Set (Set ℝ) := ⋃ q : ℚ, {Set.Iic (q : ℝ)}

lemma mem_iicRatClass {S : Set ℝ} :
    S ∈ iicRatClass ↔ ∃ q : ℚ, S = Set.Iic (q : ℝ) := by
  simp only [iicRatClass, Set.mem_iUnion, Set.mem_singleton_iff]

/-- No two-point set is shattered by the half-lines: for `p < q`, the label
`p ∉ S, q ∈ S` is unrealizable (`q ≤ t` forces `p ≤ t`). -/
private lemma iicClass_not_shatters_pair {p q : ℝ} (hpq : p < q) :
    ¬ Shatters iicClass ({p, q} : Finset ℝ) := by
  classical
  intro h
  obtain ⟨S, ⟨t, rfl⟩, hSt⟩ := h {q} (by
    intro w hw; rw [Finset.mem_singleton] at hw; subst hw; simp)
  -- `q ≤ t`.
  have hq : q ∈ (↑({p, q} : Finset ℝ) : Set ℝ) ∩ Set.Iic t := by
    rw [hSt]; simp
  have hqt : q ≤ t := hq.2
  -- `p` also lies in the intersection, so `p ∈ {q}`, i.e. `p = q`.
  have hp : p ∈ (↑({p, q} : Finset ℝ) : Set ℝ) ∩ Set.Iic t :=
    ⟨by simp, by rw [Set.mem_Iic]; linarith⟩
  rw [hSt] at hp
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hp
  exact absurd hp (ne_of_lt hpq)

/-- The half-line class has VC dimension exactly `1` (HDP §8.3.6; the book
uses the bound `≤ 2` via Example 8.3.2 — we compute the exact value:
one point is shattered; for `p < q` no member realizes `p ∉ S, q ∈ S`).
Documented deviation (sharper than the book). -/
theorem vcDim_iicClass : vcDim iicClass = 1 := by
  classical
  apply le_antisymm
  · rw [vcDim_le_iff]
    intro Λ hΛ
    by_contra hcon
    push_neg at hcon
    have h2 : 2 ≤ Λ.card := by
      have : (1 : ℕ) < Λ.card := by exact_mod_cast hcon
      omega
    obtain ⟨Λ', hsub, hc⟩ := Finset.exists_subset_card_eq h2
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    have hsh := hΛ.mono_right hsub
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact iicClass_not_shatters_pair hlt hsh
    · rw [Finset.pair_comm] at hsh
      exact iicClass_not_shatters_pair hgt hsh
  · -- `{0}` is shattered, giving `1 ≤ vcDim`.
    have hsh : Shatters iicClass ({0} : Finset ℝ) := by
      intro T hT
      by_cases h0 : (0 : ℝ) ∈ T
      · have hT0 : T = {0} := by
          apply Finset.Subset.antisymm hT
          intro w hw; rw [Finset.mem_singleton] at hw; subst hw; exact h0
        refine ⟨Set.Iic 0, ⟨0, rfl⟩, ?_⟩
        rw [hT0]
        ext w
        simp only [Finset.coe_singleton, Set.mem_inter_iff, Set.mem_singleton_iff,
          Set.mem_Iic]
        constructor
        · exact fun h => h.1
        · intro h; exact ⟨h, by rw [h]⟩
      · have hTe : T = ∅ := by
          rw [← Finset.subset_empty]
          intro w hw
          have := hT hw; rw [Finset.mem_singleton] at this; subst this
          exact absurd hw h0
        refine ⟨Set.Iic (-1), ⟨-1, rfl⟩, ?_⟩
        rw [hTe]
        ext w
        simp only [Finset.coe_singleton, Finset.coe_empty, Set.mem_inter_iff,
          Set.mem_singleton_iff, Set.mem_Iic, Set.mem_empty_iff_false, iff_false,
          not_and]
        intro h; rw [h]; norm_num
    have hle := hsh.card_le_vcDim
    simpa using hle

/-- The empirical CDF is right-continuous in the threshold (LEAN-ONLY:
finitely many jumps; `Set.Iic`-membership is right-stable). -/
lemma empFrac_iic_rightContinuous {n : ℕ} (x : Fin n → ℝ) :
    ∀ t : ℝ, ContinuousWithinAt (fun s => empFrac x (Set.Iic s))
      (Set.Ici t) t := by
  intro t
  -- each summand `s ↦ 𝟙[x i ≤ s]` is right-continuous (locally constant to
  -- the right of `t`).
  have hterm : ∀ i : Fin n, ContinuousWithinAt
      (fun s => (Set.Iic s).indicator (fun _ => (1 : ℝ)) (x i))
      (Set.Ici t) t := by
    intro i
    by_cases hxi : x i ≤ t
    · -- constantly `1` on `Ici t`.
      refine (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ => (1 : ℝ)) (Set.Ici t) t).congr ?_ ?_
      · intro s hs
        rw [Set.indicator_apply, if_pos]
        rw [Set.mem_Iic]; exact le_trans hxi hs
      · rw [Set.indicator_apply, if_pos]
        rw [Set.mem_Iic]; exact hxi
    · -- `t < x i`: constantly `0` on `[t, x i)`.
      have hlt : t < x i := not_le.mp hxi
      refine (continuousWithinAt_const :
        ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Ici t) t).congr_of_eventuallyEq
        ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hlt)] with s hs
        rw [Set.indicator_apply, if_neg]
        rw [Set.mem_Iic]; exact not_le.mpr hs
      · rw [Set.indicator_apply, if_neg]
        rw [Set.mem_Iic]; exact not_le.mpr hlt
  have hsum : ContinuousWithinAt
      (fun s => ∑ i, (Set.Iic s).indicator (fun _ => (1 : ℝ)) (x i))
      (Set.Ici t) t :=
    tendsto_finset_sum Finset.univ (fun i _ => hterm i)
  have heq : (fun s => empFrac x (Set.Iic s))
      = fun s => (n : ℝ)⁻¹ * ∑ i, (Set.Iic s).indicator (fun _ => (1 : ℝ)) (x i) :=
    rfl
  rw [heq]
  exact hsum.const_mul _

/-- The population CDF `t ↦ μ.real (Iic t)` is right-continuous (LEAN-ONLY,
batch reconciliation R6 split helper: `StieltjesFunction` fields of
`ProbabilityTheory.cdf` transported to `μ.real ∘ Set.Iic`). Kept separate
from `iSup_iic_diff_eq_iSup_rat` so debts stay atomic. -/
lemma real_iic_rightContinuous (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ t : ℝ, ContinuousWithinAt (fun s => μ.real (Set.Iic s))
      (Set.Ici t) t := by
  intro t
  have heq : (fun s => μ.real (Set.Iic s)) = fun s => (ProbabilityTheory.cdf μ) s := by
    funext s; rw [ProbabilityTheory.cdf_eq_real]
  rw [heq]
  exact (ProbabilityTheory.cdf μ).right_continuous t

/-- The CDF deviation is bounded by `1` (`empFrac, μ.real ∈ [0,1]`). -/
private lemma abs_empFrac_sub_le_one {n : ℕ} (x : Fin n → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (S : Set ℝ) :
    |empFrac x S - μ.real S| ≤ 1 := by
  rw [abs_le]
  have h1 := empFrac_nonneg x S
  have h2 := empFrac_le_one x S
  have h3 : (0 : ℝ) ≤ μ.real S := measureReal_nonneg
  have h4 : μ.real S ≤ 1 := measureReal_le_one
  constructor <;> linarith

/-- The countable `iicRatClass`-indexed sup collapses to a ℚ-indexed sup for a
nonnegative, `1`-bounded integrand (LEAN-ONLY reindexing over ℝ; junk
`sSup ∅ = 0` handled by nonnegativity). -/
private lemma biSup_iicRatClass_eq {g : Set ℝ → ℝ}
    (hg0 : ∀ S, 0 ≤ g S) (hg1 : ∀ S, g S ≤ 1) :
    (⨆ S ∈ iicRatClass, g S) = ⨆ q : ℚ, g (Set.Iic (q : ℝ)) := by
  classical
  set F : Set ℝ → ℝ := fun S => ⨆ (_ : S ∈ iicRatClass), g S with hF
  have hFbd : BddAbove (Set.range F) := by
    refine ⟨1, ?_⟩
    rintro y ⟨S, rfl⟩
    by_cases hS : S ∈ iicRatClass
    · rw [hF]; simp only; rw [ciSup_pos hS]; exact hg1 S
    · rw [hF]; simp only; rw [ciSup_neg hS, Real.sSup_empty]; exact zero_le_one
  have hRbd : BddAbove (Set.range (fun q : ℚ => g (Set.Iic (q : ℝ)))) :=
    ⟨1, by rintro y ⟨q, rfl⟩; exact hg1 _⟩
  have hR0 : 0 ≤ ⨆ q : ℚ, g (Set.Iic (q : ℝ)) :=
    le_ciSup_of_le hRbd 0 (hg0 _)
  apply le_antisymm
  · refine ciSup_le fun S => ?_
    simp only [hF]
    by_cases hS : S ∈ iicRatClass
    · rw [ciSup_pos hS]
      obtain ⟨q, rfl⟩ := mem_iicRatClass.mp hS
      exact le_ciSup hRbd q
    · rw [ciSup_neg hS, Real.sSup_empty]; exact hR0
  · refine ciSup_le fun q => ?_
    have hmem : Set.Iic (q : ℝ) ∈ iicRatClass := mem_iicRatClass.mpr ⟨q, rfl⟩
    have hval : g (Set.Iic (q : ℝ)) = F (Set.Iic (q : ℝ)) := by
      rw [hF]; simp only; rw [ciSup_pos hmem]
    rw [hval]
    exact le_ciSup hFbd (Set.Iic (q : ℝ))

/-- Deterministic ℝ→ℚ sup recovery for the CDF deviation (HDP §8.3.6 proof;
via `iSup_eq_iSup_rat_of_right_approx` + the two right-continuity lemmas).
This work item's single named-sorry fallback. -/
lemma iSup_iic_diff_eq_iSup_rat {n : ℕ} (x : Fin n → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (⨆ t : ℝ, |empFrac x (Set.Iic t) - μ.real (Set.Iic t)|) =
      ⨆ q : ℚ, |empFrac x (Set.Iic (q : ℝ)) - μ.real (Set.Iic (q : ℝ))| := by
  set h : ℝ → ℝ := fun t => |empFrac x (Set.Iic t) - μ.real (Set.Iic t)| with hh
  have hbd : BddAbove (Set.range h) := by
    refine ⟨1, ?_⟩
    rintro y ⟨t, rfl⟩
    exact abs_empFrac_sub_le_one x μ (Set.Iic t)
  have hcont : ∀ t : ℝ, ContinuousWithinAt h (Set.Ici t) t := by
    intro t
    exact ((empFrac_iic_rightContinuous x t).sub (real_iic_rightContinuous μ t)).abs
  exact iSup_eq_iSup_rat_of_right_approx hbd (right_approx_of_rightContinuous hcont)

/-- **Theorem 8.3.17 (Glivenko–Cantelli, in expectation)** (HDP §8.3.6;
frozen numeral `5400/√n`, formula `2 × 40 × √6 × 27` at `d = 1` — see
module notes): the expected sup-distance between the empirical and
population CDFs, with the genuine full supremum over `ℝ`. -/
theorem glivenko_cantelli {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → ℝ}
    -- LEAN-ONLY: measurability of the data stream; regularity
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent sample; HDP Thm 8.3.17
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP Thm 8.3.17 (map form)
    (hlaw : ∀ i, P.map (X i) = μ)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.6 (implicit)
    (hn : 1 ≤ n) :
    ∫ ξ, ⨆ t : ℝ, |empFrac (fun i : Fin n => X i ξ) (Set.Iic t) -
        μ.real (Set.Iic t)| ∂P ≤ 5400 / Real.sqrt n := by
  -- countable subclass data
  have hCc : iicRatClass.Countable :=
    Set.countable_iUnion (fun _ => Set.countable_singleton _)
  have hCne : iicRatClass.Nonempty :=
    ⟨Set.Iic ((0 : ℚ) : ℝ), mem_iicRatClass.mpr ⟨0, rfl⟩⟩
  have hCmeas : ∀ S ∈ iicRatClass, MeasurableSet S := by
    intro S hS
    obtain ⟨q, rfl⟩ := mem_iicRatClass.mp hS
    exact measurableSet_Iic
  have hsub : iicRatClass ⊆ iicClass := by
    intro S hS
    obtain ⟨q, rfl⟩ := mem_iicRatClass.mp hS
    exact ⟨(q : ℝ), rfl⟩
  have hd : vcDim iicRatClass ≤ (1 : ℕ∞) := by
    rw [← vcDim_iicClass]; exact vcDim_mono hsub
  -- the finite-VC countable LLN at `d = 1`
  have key := vc_lln_countable (Ξ := Ξ) (P := P) (μ := μ) (X := X)
    hXmeas hindep hlaw hCc hCne hCmeas hd (le_refl 1) hn
  -- rewrite the ℝ-sup integrand into the `iicRatClass`-sup integrand
  have hint : ∫ ξ, ⨆ t : ℝ, |empFrac (fun i : Fin n => X i ξ) (Set.Iic t) -
        μ.real (Set.Iic t)| ∂P
      = ∫ ξ, ⨆ S ∈ iicRatClass,
        |empFrac (fun i : Fin n => X i ξ) S - μ.real S| ∂P := by
    congr 1
    funext ξ
    rw [iSup_iic_diff_eq_iSup_rat (fun i : Fin n => X i ξ) μ,
      biSup_iicRatClass_eq
        (g := fun S => |empFrac (fun i : Fin n => X i ξ) S - μ.real S|)
        (fun S => abs_nonneg _) (fun S => abs_empFrac_sub_le_one _ μ S)]
  rw [hint]
  calc ∫ ξ, ⨆ S ∈ iicRatClass,
        |empFrac (fun i : Fin n => X i ξ) S - μ.real S| ∂P
      ≤ 5400 * Real.sqrt (1 : ℕ) / Real.sqrt n := key
    _ = 5400 / Real.sqrt n := by rw [Nat.cast_one, Real.sqrt_one, mul_one]

end StatLean.ConcentrationInequalities
