module
public import StatLean.HypothesisTesting.MLR.OneSided
public import StatLean.HypothesisTesting.NeymanPearson.Generalized

@[expose] public section

/-!
# Two-sided hypotheses in a one-parameter exponential family

Uniformly most powerful tests survive one step beyond the one-sided problem: for
`H : θ ≤ θ₁ or θ ≥ θ₂` against `K : θ₁ < θ < θ₂` in a one-parameter exponential family
there is a UMP test, which rejects on a *bounded* interval of the natural statistic,
$$ \varphi(x) = 1 \ \text{ if } C_1 < T(x) < C_2, \qquad \gamma_i \ \text{ if } T(x) = C_i,
\qquad 0 \ \text{ otherwise}, $$
with the four constants pinned down by the two size conditions
`E_{θ₁}φ = E_{θ₂}φ = α`. Two constraints, hence the generalized fundamental lemma with
`m = 2` rather than the plain one.

Contents:
* `twoSidedTest T C₁ C₂ γ₁ γ₂` — the test displayed above;
* `power_min_twoSided` — outside `[θ₁, θ₂]` the test *minimizes* the rejection
  probability among all tests meeting the two size conditions;
* `isUMP_twoSided` — existence of the four constants and uniform optimality;
* `power_lt_of_twoSided_right` — comparison of two such tests with a common size at `θ₁`:
  shifting the rejection interval to the right raises the power above `θ₁` and lowers it
  below;
* `twoSided_ae_unique` — the two size conditions determine the test almost everywhere.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.7 (Two-Sided Hypotheses), Theorem 3.7.1 (the UMP two-sided test `C₁ < T <
C₂` in a one-parameter exponential family) and Lemma 3.7.1 (the comparison/uniqueness step).
(`TSH4 §3.7 Thm 3.7.1, Lem 3.7.1`.)

**Proof formalization notes.**
* The rejection region is an interval of the natural statistic, so the test cannot be
  obtained from a single likelihood-ratio comparison; the two size conditions are handled
  by the two-constraint form of the generalized fundamental lemma, whose multipliers
  produce the two boundaries. Only the *sufficiency* halves of that lemma are used
  (`isMax_of_multiplier_form` for the equality-constrained competitor class of
  `power_min_twoSided`, `isMax_le_of_multiplier_form_nonneg` for the inequality-constrained
  class of the UMP clause): the multipliers are written down explicitly by
  `exists_exp_pair_sign` / `exists_exp_pair_sign_opp` rather than produced by a supporting
  hyperplane, so no inner-point hypothesis on the attainable-moment set is needed.
* The identification of the multiplier shape with an interval of the statistic is the
  two-crossing property of `A e^{b₁t} + B e^{b₂t}` against the constant `1`, and it is
  proved without calculus: at a parameter *inside* `(θ₁, θ₂)` the two exponents have
  opposite signs and both interpolation coefficients are positive, so the function is
  strictly convex outright; *outside* `[θ₁, θ₂]` the exponents have the same sign and one
  rescaling by `e^{-b_jt}` turns `1 - S` into a positive combination of two exponentials
  plus a constant, again strictly convex. A strictly convex function with two zeros has a
  forced sign pattern (`sign_of_strictConvexOn_two_zeros`).
* Two of the five statements needed a repair; each is documented on the statement itself,
  with a verified counterexample to the printed form: `power_lt_of_twoSided_right` (`hne`,
  non-degeneracy of the pair of tests) and `isUMP_twoSided` (`hatom`, no level of the
  statistic carries null probability `α` or more) are both FALSE as printed. In the second
  case the defect is the *existence* of an honest rejection interval `C₁ < C₂`: an atom of
  the null law heavier than `α` can force the solution of the two size equations to be a
  one-point randomization. Under the amendment the theorem is fully proved.
* The simultaneous solution of the two size equations is a one-dimensional sweep over the
  *level* window `(s, s+α)` of the null law of the statistic, in three bricks:
  `exists_twoSided_constants_window` (the canonical boundary weights make the size at `θ₁`
  exactly `α` for every `s`), `twoSidedVal_integral_weight_eq` (the size at `θ₂` is the
  level-space integral `∫_s^{s+α} r(Q u) du` of the likelihood ratio along the quantile
  function) and `exists_window_root` (the intermediate value theorem, with the *strict*
  rearrangement inequality `integral_lt_of_monotoneOn_of_sep` keeping the root away from the
  junk levels `0` and `1`).
* The order of branches in `twoSidedTest` puts the two boundary cases first, so the
  definition is unambiguous even for degenerate constants: at `C₁ = C₂` the value is `γ₁`,
  and for `C₂ ≤ C₁` the test rejects nowhere except possibly at the two boundary points.
  The theorems all produce or assume `C₁ < C₂`.
* The comparison lemma requires the *strict* form of the monotone likelihood ratio
  together with strictly positive densities. Both are transcribed explicitly: the strict
  ratio condition is written division-free as `p_{θ'}(x)·p_θ(y) < p_θ(x)·p_{θ'}(y)` for
  `T x < T y`, matching the frozen non-strict `HasMLR`.
* "`φ*` lies to the right of `φ`" is transcribed as the lexicographic condition on the
  left boundary: either `C₁ < C₁'`, or the boundaries agree and the randomization weight
  there is smaller, `γ₁' < γ₁`.
* Uniqueness is stated as `μ`-a.e. equality. Since the densities are strictly positive,
  this coincides with almost-sure equality under every member of the family.
* The unimodality clause of the classical statement — for `0 < α < 1` the power function
  has an interior maximum and decreases strictly away from it, unless the statistic is
  supported on two points — is not stated here.

**Bibliographic comments.** Two-sided problems and the tests solving them appear in
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Stat. Res. Mem.* **1** (1936), 1–37); the two-constraint fundamental lemma
they rest on is due to G. B. Dantzig and A. Wald ("On the fundamental lemma of Neyman and
Pearson," *Ann. Math. Statist.* **22** (1951), 87–93), and the underlying monotonicity
properties of exponential families to S. Karlin and H. Rubin ("The theory of decision
procedures for distributions with monotone likelihood ratio," *Ann. Math. Statist.* **27**
(1956), 272–299).
-/

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation

/-- The real inner product on `ℝ` is multiplication (local copy: the `MLR/OneSided`
version is `private` to that file). -/
private lemma ts_real_inner_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  have h1 : ⟪(1 : ℝ), b⟫_ℝ = b := by
    have h := real_inner_smul_right (1 : ℝ) 1 b
    simpa [real_inner_self_eq_norm_mul_norm] using h
  have h2 := real_inner_smul_left (1 : ℝ) b a
  simpa [h1] using h2

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **two-sided test** based on the statistic `T`: reject when `C₁ < T < C₂`, reject
with probability `γᵢ` when `T = Cᵢ`, accept outside. The boundary branches are tested
first, so the definition is total and unambiguous: at `C₁ = C₂` the value is `γ₁`, and for
`C₂ ≤ C₁` the test rejects only (possibly) at the two boundary points. All theorems below
produce or assume `C₁ < C₂` and `γᵢ ∈ [0,1]`. -/
noncomputable def twoSidedTest (T : 𝓧 → ℝ) (C₁ C₂ γ₁ γ₂ : ℝ) : 𝓧 → ℝ := fun x =>
  if T x = C₁ then γ₁
  else if T x = C₂ then γ₂
  else if C₁ < T x ∧ T x < C₂ then 1
  else 0

/-- The scalar value of the two-sided test as a function of the statistic level `t`,
written with nested `if`s (so `split_ifs` produces atomic order conditions). -/
private noncomputable def twoSidedVal (C₁ C₂ γ₁ γ₂ t : ℝ) : ℝ :=
  if t = C₁ then γ₁ else if t = C₂ then γ₂ else if C₁ < t then if t < C₂ then 1 else 0 else 0

/-- `twoSidedTest` factors through the statistic via `twoSidedVal`. -/
private lemma twoSidedTest_eq_val (T : 𝓧 → ℝ) (C₁ C₂ γ₁ γ₂ : ℝ) (x : 𝓧) :
    twoSidedTest T C₁ C₂ γ₁ γ₂ x = twoSidedVal C₁ C₂ γ₁ γ₂ (T x) := by
  unfold twoSidedTest twoSidedVal
  by_cases h1 : T x = C₁
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : T x = C₂
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2]
      by_cases h3 : C₁ < T x
      · rw [if_pos h3]; by_cases h4 : T x < C₂
        · rw [if_pos ⟨h3, h4⟩, if_pos h4]
        · rw [if_neg (fun h => h4 h.2), if_neg h4]
      · rw [if_neg h3, if_neg (fun h => h3 h.1)]

/-- With `γᵢ ∈ [0,1]` and `C₁ < C₂`, the scalar value lies in `[0,1]`. -/
private lemma twoSidedVal_mem_Icc {C₁ C₂ γ₁ γ₂ : ℝ}
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    twoSidedVal C₁ C₂ γ₁ γ₂ t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold twoSidedVal
  split_ifs
  · exact hγ₁
  · exact hγ₂
  · exact ⟨zero_le_one, le_refl 1⟩
  · exact ⟨le_refl 0, zero_le_one⟩
  · exact ⟨le_refl 0, zero_le_one⟩

set_option maxHeartbeats 1000000 in
/-- **Separation of the difference of two right-shifted two-sided values.** Write
`D t = twoSidedVal C₁' C₂' γ₁' γ₂' t − twoSidedVal C₁ C₂ γ₁ γ₂ t`. If the second rejection
interval lies to the right of the first (`hright`), then every level `s` at which `D s > 0`
lies strictly to the right of every level `t` at which `D t < 0`: the positive part of the
difference sits above the negative part. This is the single sign-change structure that
drives the Lehmann comparison. -/
private lemma twoSidedVal_sub_sep {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ}
    (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    (hright : C₁ < C₁' ∨ (C₁ = C₁' ∧ γ₁' < γ₁)) {s t : ℝ}
    (hs : 0 < twoSidedVal C₁' C₂' γ₁' γ₂' s - twoSidedVal C₁ C₂ γ₁ γ₂ s)
    (ht : twoSidedVal C₁' C₂' γ₁' γ₂' t - twoSidedVal C₁ C₂ γ₁ γ₂ t < 0) :
    t < s := by
  obtain ⟨hγ₁0, hγ₁1⟩ := hγ₁; obtain ⟨hγ₂0, hγ₂1⟩ := hγ₂
  obtain ⟨hγ₁'0, hγ₁'1⟩ := hγ₁'; obtain ⟨hγ₂'0, hγ₂'1⟩ := hγ₂'
  by_contra hst
  push_neg at hst
  -- `s ≤ t`; derive a contradiction with `D s > 0`, `D t < 0`.
  unfold twoSidedVal at hs ht
  rcases hright with hr | ⟨hrEq, hrγ⟩
  · split_ifs at hs ht <;>
      first
        | linarith
        | (exfalso; subst_vars; simp_all <;>
            exact absurd (le_antisymm hst (by assumption : t ≤ s)) (by assumption : ¬ s = t))
        | (exfalso; subst_vars; linarith)
        | (exfalso; have : s = t := le_antisymm hst ‹t ≤ s›; subst this; simp_all)
  · subst hrEq
    split_ifs at hs ht <;>
      first
        | linarith
        | (exfalso; subst_vars; simp_all <;>
            exact absurd (le_antisymm hst (by assumption : t ≤ s)) (by assumption : ¬ s = t))
        | (exfalso; subst_vars; linarith)
        | (exfalso; have : s = t := le_antisymm hst ‹t ≤ s›; subst this; simp_all)

/-- Widening the rejection interval on the right can only raise the test: with a common left
boundary and `C₂ < C₂'`, the value is pointwise nondecreasing. -/
private lemma twoSidedVal_le_of_lt_right {C₁ C₂ C₂' γ₁ γ₂ γ₂' : ℝ} (hC : C₁ < C₂)
    (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : 0 ≤ γ₂') (hlt : C₂ < C₂') (u : ℝ) :
    twoSidedVal C₁ C₂ γ₁ γ₂ u ≤ twoSidedVal C₁ C₂' γ₁ γ₂' u := by
  obtain ⟨hγ₂0, hγ₂1⟩ := hγ₂
  unfold twoSidedVal
  split_ifs <;> linarith

/-- Raising the right boundary weight can only raise the test. -/
private lemma twoSidedVal_le_of_le_gamma₂ {C₁ C₂ γ₁ γ₂ γ₂' : ℝ} (hle : γ₂ ≤ γ₂') (u : ℝ) :
    twoSidedVal C₁ C₂ γ₁ γ₂ u ≤ twoSidedVal C₁ C₂ γ₁ γ₂' u := by
  unfold twoSidedVal
  split_ifs <;> linarith

/-- **The equal-left-data case of the separation.** When the two rejection intervals share
their left boundary *and* its randomization weight, the difference of the two values has a
constant sign, so it can never be both positive somewhere and negative somewhere. This is
the case `twoSidedVal_sub_sep` does not cover (its `hright` requires the left data to
differ), and together the two exhaust the trichotomy on `(C₁, γ₁)`. -/
private lemma twoSidedVal_sub_sep_eqLeft {C₁ C₂ C₂' γ₁ γ₂ γ₂' : ℝ}
    (hC : C₁ < C₂) (hC' : C₁ < C₂')
    (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1) {s t : ℝ}
    (hs : 0 < twoSidedVal C₁ C₂' γ₁ γ₂' s - twoSidedVal C₁ C₂ γ₁ γ₂ s)
    (ht : twoSidedVal C₁ C₂' γ₁ γ₂' t - twoSidedVal C₁ C₂ γ₁ γ₂ t < 0) :
    False := by
  rcases lt_trichotomy C₂ C₂' with h | h | h
  · linarith [twoSidedVal_le_of_lt_right (γ₁ := γ₁) hC hγ₂ hγ₂'.1 h t]
  · subst h
    rcases le_total γ₂ γ₂' with hg | hg
    · linarith [twoSidedVal_le_of_le_gamma₂ (C₁ := C₁) (C₂ := C₂) (γ₁ := γ₁) hg t]
    · linarith [twoSidedVal_le_of_le_gamma₂ (C₁ := C₁) (C₂ := C₂) (γ₁ := γ₁) hg s]
  · linarith [twoSidedVal_le_of_lt_right (γ₁ := γ₁) hC' hγ₂' hγ₂.1 h s]

/-- **The analytic core of the two-sided uniqueness theorem.** Let `D` be a function of the
statistic `T` whose negative part lies strictly below its positive part along `T` (the
single-sign-change structure produced by `twoSidedVal_sub_sep`), and let `p₁, p₂` be
strictly positive densities whose likelihood ratio is strictly increasing along `T`. If `D`
integrates to zero against both densities, then `D` vanishes `μ`-almost everywhere.

The mechanism: the sign change gives a real `k` separating the ratio `p₂/p₁` across the sign
change, so `D·(p₂ − k·p₁) ≥ 0` pointwise while its integral is `0 − k·0 = 0`; hence
`D = 0` or `p₂ = k·p₁` a.e. Strict monotonicity of the ratio confines `{p₂ = k·p₁}` to a
single level set of `T`, on which `D` is constant, and the vanishing of `∫ D·p₁` kills that
last constant too. -/
private lemma ae_eq_zero_of_sep {μ : Measure 𝓧} {T D p₁ p₂ : 𝓧 → ℝ}
    (hp₁ : ∀ x, 0 < p₁ x) (hp₁int : Integrable p₁ μ)
    (hstrict : ∀ x y, T x < T y → p₂ x * p₁ y < p₁ x * p₂ y)
    (hsep : ∀ x y, D x < 0 → 0 < D y → T x < T y)
    (hDT : ∀ x y, T x = T y → D x = D y)
    (hint₁ : Integrable (fun x => D x * p₁ x) μ)
    (hint₂ : Integrable (fun x => D x * p₂ x) μ)
    (h₁ : ∫ x, D x * p₁ x ∂μ = 0) (h₂ : ∫ x, D x * p₂ x ∂μ = 0) :
    D =ᵐ[μ] 0 := by
  have hcancel : ∀ x, D x * p₁ x = 0 → D x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_right (ne_of_gt (hp₁ x))
  by_cases hneg : ∃ x, D x < 0
  swap
  · -- `D ≥ 0` everywhere: a nonnegative integrand with zero integral.
    push_neg at hneg
    have hnn : 0 ≤ᵐ[μ] fun x => D x * p₁ x :=
      Filter.Eventually.of_forall fun x => mul_nonneg (hneg x) (hp₁ x).le
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁).mp h₁] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    exact hcancel x hx
  by_cases hpos : ∃ y, 0 < D y
  swap
  · -- `D ≤ 0` everywhere: the same, applied to `−D·p₁`.
    push_neg at hpos
    have hnn : 0 ≤ᵐ[μ] fun x => -(D x * p₁ x) :=
      Filter.Eventually.of_forall fun x => by
        change (0 : ℝ) ≤ -(D x * p₁ x)
        nlinarith [mul_nonneg (neg_nonneg.mpr (hpos x)) (hp₁ x).le]
    have hz : ∫ x, -(D x * p₁ x) ∂μ = 0 := by rw [integral_neg, h₁, neg_zero]
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁.neg).mp hz] with x hx
    simp only [Pi.zero_apply, neg_eq_zero] at hx ⊢
    exact hcancel x hx
  obtain ⟨x₀, hx₀⟩ := hneg
  obtain ⟨y₀, hy₀⟩ := hpos
  -- The likelihood ratio is strictly larger on `{D > 0}` than on `{D < 0}`.
  have hratio : ∀ x y, D x < 0 → 0 < D y → p₂ x / p₁ x < p₂ y / p₁ y := by
    intro x y hx hy
    rw [div_lt_div_iff₀ (hp₁ x) (hp₁ y), mul_comm (p₂ y) (p₁ x)]
    exact hstrict x y (hsep x y hx hy)
  have hSne : {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}.Nonempty :=
    ⟨p₂ x₀ / p₁ x₀, x₀, hx₀, rfl⟩
  have hSub : ∀ y, 0 < D y →
      ∀ c ∈ {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}, c ≤ p₂ y / p₁ y := by
    rintro y hy c ⟨x, hx, rfl⟩
    exact (hratio x y hx hy).le
  have hbdd : BddAbove {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} :=
    ⟨p₂ y₀ / p₁ y₀, hSub y₀ hy₀⟩
  set k := sSup {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} with hkdef
  have hkle : ∀ x, D x < 0 → p₂ x / p₁ x ≤ k := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hkge : ∀ y, 0 < D y → k ≤ p₂ y / p₁ y := fun y hy => csSup_le hSne (hSub y hy)
  -- `D·(p₂ − k·p₁) ≥ 0` pointwise, with zero integral.
  have hg : ∀ x, 0 ≤ D x * p₂ x - k * (D x * p₁ x) := by
    intro x
    rcases lt_trichotomy (D x) 0 with h | h | h
    · have h2 := hkle x h
      rw [div_le_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg (neg_nonneg.mpr h.le) (sub_nonneg.mpr h2)]
    · rw [h]; simp
    · have h2 := hkge x h
      rw [le_div_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg h.le (sub_nonneg.mpr h2)]
  have hkint : Integrable (fun x => k * (D x * p₁ x)) μ := hint₁.const_mul k
  have hgint : Integrable (fun x => D x * p₂ x - k * (D x * p₁ x)) μ := hint₂.sub hkint
  have hgzero : ∫ x, (D x * p₂ x - k * (D x * p₁ x)) ∂μ = 0 := by
    rw [integral_sub hint₂ hkint, integral_const_mul, h₁, h₂]
    ring
  have hdisj : ∀ᵐ x ∂μ, D x = 0 ∨ p₂ x = k * p₁ x := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall hg) hgint).mp hgzero] with x hx
    simp only [Pi.zero_apply] at hx
    have hrw : D x * (p₂ x - k * p₁ x) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp hrw with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  by_cases hexc : ∃ x, D x ≠ 0 ∧ p₂ x = k * p₁ x
  swap
  · push_neg at hexc
    filter_upwards [hdisj] with x hx
    simp only [Pi.zero_apply]
    rcases hx with h | h
    · exact h
    · by_contra hD
      exact hexc x hD h
  obtain ⟨x₁, hx₁D, hx₁r⟩ := hexc
  -- Strict monotonicity of the ratio pins `{p₂ = k·p₁} ∩ {D ≠ 0}` to one level of `T`.
  have hlevel : ∀ x, D x ≠ 0 → p₂ x = k * p₁ x → T x = T x₁ := by
    intro x hxD hxr
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hlt := hstrict x x₁ h
      rw [hxr, hx₁r] at hlt; linarith
    · have hlt := hstrict x₁ x h
      rw [hxr, hx₁r] at hlt; linarith
  have hDzero : ∀ᵐ x ∂μ, x ∉ {y : 𝓧 | T y = T x₁} → D x = 0 := by
    filter_upwards [hdisj] with x hx hxE
    rcases hx with h | h
    · exact h
    · by_contra hD
      exact hxE (hlevel x hD h)
  -- Multiplying by the CONSTANT `D x₁` makes `D·p₁` a.e. nonnegative — a.e. either `D`
  -- vanishes or `D = D x₁` — while its integral is `0 · D x₁ = 0`. So a.e. either `D x = 0`
  -- or `D x₁ ^ 2 · p₁ x = 0`, and the latter is impossible since `p₁ > 0` and `D x₁ ≠ 0`.
  have hqnn : 0 ≤ᵐ[μ] fun x => D x * p₁ x * D x₁ := by
    filter_upwards [hDzero] with x hx
    change (0 : ℝ) ≤ D x * p₁ x * D x₁
    by_cases hxE : x ∈ {y : 𝓧 | T y = T x₁}
    · rw [hDT x x₁ hxE]
      nlinarith [mul_nonneg (mul_self_nonneg (D x₁)) (hp₁ x).le]
    · rw [hx hxE]; simp
  have hqint : Integrable (fun x => D x * p₁ x * D x₁) μ := hint₁.mul_const (D x₁)
  have hqz : ∫ x, D x * p₁ x * D x₁ ∂μ = 0 := by rw [integral_mul_const, h₁, zero_mul]
  filter_upwards [hDzero, (integral_eq_zero_iff_of_nonneg_ae hqnn hqint).mp hqz] with x hx hq
  simp only [Pi.zero_apply] at hq ⊢
  by_cases hxE : x ∈ {y : 𝓧 | T y = T x₁}
  · rw [hDT x x₁ hxE] at hq ⊢
    have h0 : D x₁ * D x₁ * p₁ x = 0 := by linear_combination hq
    exact absurd (mul_self_eq_zero.mp
      ((mul_eq_zero.mp h0).resolve_right (ne_of_gt (hp₁ x)))) hx₁D
  · exact hx hxE

/-- The two orientations of the sign change are handled at once: replacing `D` by `−D` turns
the second alternative into the first. -/
private lemma ae_eq_zero_of_sep_or {μ : Measure 𝓧} {T D p₁ p₂ : 𝓧 → ℝ}
    (hp₁ : ∀ x, 0 < p₁ x) (hp₁int : Integrable p₁ μ)
    (hstrict : ∀ x y, T x < T y → p₂ x * p₁ y < p₁ x * p₂ y)
    (hsep : (∀ x y, D x < 0 → 0 < D y → T x < T y) ∨
      (∀ x y, 0 < D x → D y < 0 → T x < T y))
    (hDT : ∀ x y, T x = T y → D x = D y)
    (hint₁ : Integrable (fun x => D x * p₁ x) μ)
    (hint₂ : Integrable (fun x => D x * p₂ x) μ)
    (h₁ : ∫ x, D x * p₁ x ∂μ = 0) (h₂ : ∫ x, D x * p₂ x ∂μ = 0) :
    D =ᵐ[μ] 0 := by
  rcases hsep with h | h
  · exact ae_eq_zero_of_sep hp₁ hp₁int hstrict h hDT hint₁ hint₂ h₁ h₂
  · have hneg : ∀ (q : 𝓧 → ℝ), Integrable (fun x => D x * q x) μ →
        Integrable (fun x => (-D x) * q x) μ := by
      intro q hq
      have h0 : Integrable (fun x => (-1 : ℝ) * (D x * q x)) μ := hq.const_mul (-1)
      refine h0.congr (Filter.Eventually.of_forall fun x => ?_)
      change (-1 : ℝ) * (D x * q x) = (-D x) * q x
      ring
    have hnegz : ∀ (q : 𝓧 → ℝ), ∫ x, D x * q x ∂μ = 0 → ∫ x, (-D x) * q x ∂μ = 0 := by
      intro q hq
      rw [show (fun x => (-D x) * q x) = fun x => -(D x * q x) from funext fun x => by ring,
        integral_neg, hq, neg_zero]
    have hres := ae_eq_zero_of_sep (D := fun x => -D x) hp₁ hp₁int hstrict
      (fun x y hx hy => by
        have hx' : -D x < 0 := hx
        have hy' : (0 : ℝ) < -D y := hy
        exact h x y (by linarith) (by linarith))
      (fun x y hxy => by simp only [hDT x y hxy])
      (hneg p₁ hint₁) (hneg p₂ hint₂) (hnegz p₁ h₁) (hnegz p₂ h₂)
    filter_upwards [hres] with x hx
    have hx' : -D x = 0 := hx
    simp only [Pi.zero_apply]
    linarith

/-- **The strict form of the analytic core.** Same single-sign-change structure as
`ae_eq_zero_of_sep`, but the second vanishing integral is replaced by the *nondegeneracy*
hypothesis `¬ D =ᵐ[μ] 0`, and the conclusion is upgraded from `≥ 0` to `> 0`: a difference
whose negative part lies strictly below its positive part along `T`, which integrates to
zero against the lower member and does not vanish almost everywhere, has a strictly positive
integral against the upper member.

The mechanism is the same separating constant `k` for the ratio `p₂/p₁`, giving
`D·(p₂ − k·p₁) ≥ 0` pointwise with integral `∫D p₂ − k·0`. Strictness is where the
nondegeneracy is consumed: were that integral zero, the set `{p₂ = k·p₁}` would have to
carry both a point with `D < 0` and a point with `D > 0`, while strict monotonicity of the
ratio confines it to a single level set of `T` — contradicting the sign change. -/
private lemma integral_pos_of_sep {μ : Measure 𝓧} {T D p₁ p₂ : 𝓧 → ℝ}
    (hp₁ : ∀ x, 0 < p₁ x)
    (hstrict : ∀ x y, T x < T y → p₂ x * p₁ y < p₁ x * p₂ y)
    (hsep : ∀ x y, D x < 0 → 0 < D y → T x < T y)
    (hint₁ : Integrable (fun x => D x * p₁ x) μ)
    (hint₂ : Integrable (fun x => D x * p₂ x) μ)
    (h₁ : ∫ x, D x * p₁ x ∂μ = 0) (hne : ¬ D =ᵐ[μ] 0) :
    0 < ∫ x, D x * p₂ x ∂μ := by
  have hcancel : ∀ x, D x * p₁ x = 0 → D x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_right (ne_of_gt (hp₁ x))
  -- Both signs occur: a one-signed `D` with `∫D p₁ = 0` and `p₁ > 0` vanishes a.e.
  have hnegex : ¬ (∀ᵐ x ∂μ, 0 ≤ D x) := by
    intro h
    refine hne ?_
    have hnn : 0 ≤ᵐ[μ] fun x => D x * p₁ x := by
      filter_upwards [h] with x hx
      exact mul_nonneg hx (hp₁ x).le
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁).mp h₁] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    exact hcancel x hx
  have hposex : ¬ (∀ᵐ x ∂μ, D x ≤ 0) := by
    intro h
    refine hne ?_
    have hnn : 0 ≤ᵐ[μ] fun x => -(D x * p₁ x) := by
      filter_upwards [h] with x hx
      change (0 : ℝ) ≤ -(D x * p₁ x)
      nlinarith [mul_nonneg (neg_nonneg.mpr hx) (hp₁ x).le]
    have hz : ∫ x, -(D x * p₁ x) ∂μ = 0 := by rw [integral_neg, h₁, neg_zero]
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint₁.neg).mp hz] with x hx
    simp only [Pi.zero_apply, neg_eq_zero] at hx ⊢
    exact hcancel x hx
  obtain ⟨x₀, hx₀⟩ : ∃ x, D x < 0 := by
    by_contra hc
    push_neg at hc
    exact hnegex (Filter.Eventually.of_forall hc)
  obtain ⟨y₀, hy₀⟩ : ∃ y, 0 < D y := by
    by_contra hc
    push_neg at hc
    exact hposex (Filter.Eventually.of_forall hc)
  -- The separating ratio constant.
  have hratio : ∀ x y, D x < 0 → 0 < D y → p₂ x / p₁ x < p₂ y / p₁ y := by
    intro x y hx hy
    rw [div_lt_div_iff₀ (hp₁ x) (hp₁ y), mul_comm (p₂ y) (p₁ x)]
    exact hstrict x y (hsep x y hx hy)
  have hSne : {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}.Nonempty :=
    ⟨p₂ x₀ / p₁ x₀, x₀, hx₀, rfl⟩
  have hSub : ∀ y, 0 < D y →
      ∀ c ∈ {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x}, c ≤ p₂ y / p₁ y := by
    rintro y hy c ⟨x, hx, rfl⟩
    exact (hratio x y hx hy).le
  have hbdd : BddAbove {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} :=
    ⟨p₂ y₀ / p₁ y₀, hSub y₀ hy₀⟩
  set k := sSup {c : ℝ | ∃ x, D x < 0 ∧ c = p₂ x / p₁ x} with hkdef
  have hkle : ∀ x, D x < 0 → p₂ x / p₁ x ≤ k := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hkge : ∀ y, 0 < D y → k ≤ p₂ y / p₁ y := fun y hy => csSup_le hSne (hSub y hy)
  have hg : ∀ x, 0 ≤ D x * p₂ x - k * (D x * p₁ x) := by
    intro x
    rcases lt_trichotomy (D x) 0 with h | h | h
    · have h2 := hkle x h
      rw [div_le_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg (neg_nonneg.mpr h.le) (sub_nonneg.mpr h2)]
    · rw [h]; simp
    · have h2 := hkge x h
      rw [le_div_iff₀ (hp₁ x)] at h2
      nlinarith [mul_nonneg h.le (sub_nonneg.mpr h2)]
  have hkint : Integrable (fun x => k * (D x * p₁ x)) μ := hint₁.const_mul k
  have hgint : Integrable (fun x => D x * p₂ x - k * (D x * p₁ x)) μ := hint₂.sub hkint
  have hgval : ∫ x, (D x * p₂ x - k * (D x * p₁ x)) ∂μ = ∫ x, D x * p₂ x ∂μ := by
    rw [integral_sub hint₂ hkint, integral_const_mul, h₁, mul_zero, sub_zero]
  have hnn : 0 ≤ ∫ x, (D x * p₂ x - k * (D x * p₁ x)) ∂μ :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hg)
  rcases eq_or_lt_of_le hnn with heq | hlt
  · exfalso
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall hg) hgint).mp heq.symm
    have hdisj : ∀ᵐ x ∂μ, D x = 0 ∨ p₂ x = k * p₁ x := by
      filter_upwards [hae] with x hx
      simp only [Pi.zero_apply] at hx
      have hrw : D x * (p₂ x - k * p₁ x) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp hrw with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    obtain ⟨x, hxD, hxr⟩ : ∃ x, D x < 0 ∧ p₂ x = k * p₁ x := by
      by_contra hc
      push_neg at hc
      refine hnegex ?_
      filter_upwards [hdisj] with x hx
      rcases hx with h | h
      · exact le_of_eq h.symm
      · by_contra hlt0
        push_neg at hlt0
        exact absurd h (hc x hlt0)
    obtain ⟨y, hyD, hyr⟩ : ∃ y, 0 < D y ∧ p₂ y = k * p₁ y := by
      by_contra hc
      push_neg at hc
      refine hposex ?_
      filter_upwards [hdisj] with x hx
      rcases hx with h | h
      · exact le_of_eq h
      · by_contra hlt0
        push_neg at hlt0
        exact absurd h (hc x hlt0)
    have hcmp := hstrict x y (hsep x y hxD hyD)
    rw [hxr, hyr] at hcmp
    have hid : k * p₁ x * p₁ y = p₁ x * (k * p₁ y) := by ring
    linarith
  · rw [hgval] at hlt
    exact hlt

/-- Expectation against a density-carrying measure equals the integral against the density
(local copy: the `MLR/OneSided` version is `private` to that file). -/
private lemma ts_integral_density_eq {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (ψ : 𝓧 → ℝ) : ∫ x, ψ x ∂P = ∫ x, ψ x * p x ∂μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq, integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hnn x)]; ring

/-- A density of a probability measure is integrable (local copy). -/
private lemma ts_density_integrable {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : Integrable p μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  have h1 : (μ.withDensity fun x => ENNReal.ofReal (p x)) Set.univ = 1 := by
    rw [← hPeq]; exact measure_univ
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  rw [h1]; exact ENNReal.one_lt_top

/-- If `ψ` is `P`-integrable and `P` has density `p`, then `ψ·p` is `μ`-integrable
(local copy). -/
private lemma ts_density_mul_integrable {μ : Measure 𝓧} {p ψ : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (hψ : Integrable ψ P) : Integrable (fun x => ψ x * p x) μ := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq] at hψ
  refine ((integrable_withDensity_iff hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hψ).congr ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hnn x)]

/-- Converse of `ts_density_mul_integrable`: if `ψ·p` is `μ`-integrable then `ψ` is
`P`-integrable. -/
private lemma ts_integrable_of_density {μ : Measure 𝓧} {p ψ : 𝓧 → ℝ} {P : Measure 𝓧}
    (h : HasDensity μ p P) (hψ : Integrable (fun x => ψ x * p x) μ) : Integrable ψ P := by
  obtain ⟨hmeas, hnn, hPeq⟩ := h
  rw [hPeq]
  refine (integrable_withDensity_iff hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mpr (hψ.congr ?_)
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hnn x)]

/-- The density integrates to `1` (local copy). -/
private lemma ts_density_integral_one {μ : Measure 𝓧} {p : 𝓧 → ℝ} {P : Measure 𝓧}
    [IsProbabilityMeasure P] (h : HasDensity μ p P) : ∫ x, p x ∂μ = 1 := by
  have h1 : ∫ x, (1 : ℝ) ∂P = ∫ x, (1 : ℝ) * p x ∂μ := ts_integral_density_eq h (fun _ => 1)
  simp only [one_mul] at h1
  rw [← h1]; simp

/-! ### Two exponentials crossing a constant twice

The multiplier shape produced by the generalized fundamental lemma is
`{p_θ > k₁p_{θ₁} + k₂p_{θ₂}}`; in canonical form this is `{S(T) < 1}` for
`S(t) = A e^{b₁t} + B e^{b₂t}`. The three lemmas below identify the shape with an interval
of the statistic when the two exponents have the same sign — the configuration that occurs
for `θ` *outside* `[θ₁, θ₂]`. No calculus is used: after multiplying by the appropriate
`e^{-b_j t}` the function `1 - S` becomes a positive combination of two exponentials plus a
constant, hence strictly convex, and a strictly convex function with two zeros has a forced
sign pattern. -/

/-- A positive combination of two exponentials of nonconstant affine arguments, plus a
constant, is strictly convex. -/
private lemma strictConvexOn_two_exp {c₁ c₂ a₁ a₂ d : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) :
    StrictConvexOn ℝ Set.univ
      fun t : ℝ => c₁ * Real.exp (a₁ * t) + c₂ * Real.exp (a₂ * t) + d := by
  refine ⟨convex_univ, fun x _ y _ hxy q r hq hr hqr => ?_⟩
  have hne₁ : a₁ * x ≠ a₁ * y := fun h => hxy (mul_left_cancel₀ ha₁ h)
  have hne₂ : a₂ * x ≠ a₂ * y := fun h => hxy (mul_left_cancel₀ ha₂ h)
  have h₁ := strictConvexOn_exp.2 (Set.mem_univ (a₁ * x)) (Set.mem_univ (a₁ * y)) hne₁ hq hr hqr
  have h₂ := strictConvexOn_exp.2 (Set.mem_univ (a₂ * x)) (Set.mem_univ (a₂ * y)) hne₂ hq hr hqr
  simp only [smul_eq_mul] at h₁ h₂ ⊢
  have e₁ : a₁ * (q * x + r * y) = q * (a₁ * x) + r * (a₁ * y) := by ring
  have e₂ : a₂ * (q * x + r * y) = q * (a₂ * x) + r * (a₂ * y) := by ring
  rw [e₁, e₂]
  have g₁ := mul_lt_mul_of_pos_left h₁ hc₁
  have g₂ := mul_lt_mul_of_pos_left h₂ hc₂
  have hd : q * d + r * d = d := by rw [← add_mul, hqr, one_mul]
  nlinarith [g₁, g₂, hd]

/-- A strictly convex function vanishing at two points is negative strictly between them
and positive strictly outside. -/
private lemma sign_of_strictConvexOn_two_zeros {g : ℝ → ℝ}
    (hg : StrictConvexOn ℝ Set.univ g) {C₁ C₂ : ℝ} (hC : C₁ < C₂)
    (h1 : g C₁ = 0) (h2 : g C₂ = 0) :
    (∀ t : ℝ, C₁ < t → t < C₂ → g t < 0) ∧ (∀ t : ℝ, t < C₁ → 0 < g t) ∧
      (∀ t : ℝ, C₂ < t → 0 < g t) := by
  have hkey : ∀ x y z : ℝ, x < y → y < z →
      g y < ((z - y) / (z - x)) * g x + ((y - x) / (z - x)) * g z := by
    intro x y z hxy hyz
    have hxz : x < z := hxy.trans hyz
    have hden : 0 < z - x := by linarith
    have ha : 0 < (z - y) / (z - x) := div_pos (by linarith) hden
    have hb : 0 < (y - x) / (z - x) := div_pos (by linarith) hden
    have hab : (z - y) / (z - x) + (y - x) / (z - x) = 1 := by field_simp; ring
    have hcomb : ((z - y) / (z - x)) * x + ((y - x) / (z - x)) * z = y := by
      field_simp; ring
    have hcx := hg.2 (Set.mem_univ x) (Set.mem_univ z) (ne_of_lt hxz) ha hb hab
    simp only [smul_eq_mul] at hcx
    rwa [hcomb] at hcx
  refine ⟨fun t ht1 ht2 => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · have := hkey C₁ t C₂ ht1 ht2
    rw [h1, h2] at this
    linarith
  · have hlt := hkey t C₁ C₂ ht hC
    rw [h1, h2] at hlt
    have ha : 0 < (C₂ - C₁) / (C₂ - t) := div_pos (by linarith) (by linarith)
    by_contra hcon
    push_neg at hcon
    nlinarith
  · have hlt := hkey C₁ C₂ t hC ht
    rw [h1, h2] at hlt
    have hb : 0 < (C₂ - C₁) / (t - C₁) := div_pos (by linarith) (by linarith)
    by_contra hcon
    push_neg at hcon
    nlinarith

/-- **Two exponentials crossing a constant twice.** For exponents `b₁ < b₂` of the same
nonzero sign and points `C₁ < C₂` there are coefficients `A, B` for which
`S(t) = A e^{b₁t} + B e^{b₂t}` equals `1` at `C₁` and `C₂`, exceeds `1` strictly between
them, and falls strictly below `1` outside. The coefficients are the solution of the `2×2`
interpolation system, and their signs (`A` of the sign of `b₂`, `B` of the opposite sign to
`b₁`) are exactly what makes the rescaled function `e^{-b_jt}(1 - S(t))` a positive
combination of exponentials. -/
private lemma exists_exp_pair_sign {b₁ b₂ C₁ C₂ : ℝ} (hb : b₁ < b₂) (hbb : 0 < b₁ * b₂)
    (hC : C₁ < C₂) :
    ∃ A B : ℝ,
      A * Real.exp (b₁ * C₁) + B * Real.exp (b₂ * C₁) = 1 ∧
      A * Real.exp (b₁ * C₂) + B * Real.exp (b₂ * C₂) = 1 ∧
      (∀ t : ℝ, C₁ < t → t < C₂ → 1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) ∧
      (∀ t : ℝ, t < C₁ → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) ∧
      (∀ t : ℝ, C₂ < t → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) := by
  have hΔ : 0 < Real.exp (b₁ * C₁) * Real.exp (b₂ * C₂)
      - Real.exp (b₁ * C₂) * Real.exp (b₂ * C₁) := by
    rw [← Real.exp_add, ← Real.exp_add, sub_pos, Real.exp_lt_exp]
    nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr hC)]
  set Δ := Real.exp (b₁ * C₁) * Real.exp (b₂ * C₂)
    - Real.exp (b₁ * C₂) * Real.exp (b₂ * C₁) with hΔdef
  set A := (Real.exp (b₂ * C₂) - Real.exp (b₂ * C₁)) / Δ with hAdef
  set B := (Real.exp (b₁ * C₁) - Real.exp (b₁ * C₂)) / Δ with hBdef
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  have hv₁ : A * Real.exp (b₁ * C₁) + B * Real.exp (b₂ * C₁) = 1 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hΔne, one_mul, hΔdef]
    ring
  have hv₂ : A * Real.exp (b₁ * C₂) + B * Real.exp (b₂ * C₂) = 1 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hΔne, one_mul, hΔdef]
    ring
  -- The sign pattern, from strict convexity of the rescaled `1 - S`.
  have hmain : (∀ t : ℝ, C₁ < t → t < C₂ →
        1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) ∧
      (∀ t : ℝ, t < C₁ → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) ∧
      (∀ t : ℝ, C₂ < t → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) := by
    -- A rescaling factor `e^{-m t}` and a strictly convex `g = e^{-m t}(1 - S)`.
    have hgen : ∀ m : ℝ, ∀ g : ℝ → ℝ, StrictConvexOn ℝ Set.univ g →
        (∀ t : ℝ, g t
          = Real.exp (-m * t) * (1 - (A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)))) →
        (∀ t : ℝ, C₁ < t → t < C₂ → 1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) ∧
          (∀ t : ℝ, t < C₁ → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) ∧
          (∀ t : ℝ, C₂ < t → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) := by
      intro m g hgc hgrel
      have hg1 : g C₁ = 0 := by rw [hgrel C₁, hv₁]; ring
      have hg2 : g C₂ = 0 := by rw [hgrel C₂, hv₂]; ring
      obtain ⟨hin, hlo, hhi⟩ := sign_of_strictConvexOn_two_zeros hgc hC hg1 hg2
      refine ⟨fun t h1 h2 => ?_, fun t h => ?_, fun t h => ?_⟩
      · have hgt := hin t h1 h2
        rw [hgrel t] at hgt
        nlinarith [Real.exp_pos (-m * t)]
      · have hgt := hlo t h
        rw [hgrel t] at hgt
        nlinarith [Real.exp_pos (-m * t)]
      · have hgt := hhi t h
        rw [hgrel t] at hgt
        nlinarith [Real.exp_pos (-m * t)]
    rcases lt_trichotomy b₁ 0 with hb₁ | hb₁ | hb₁
    · -- Both exponents negative: rescale by `e^{-b₂t}`; then `A < 0` supplies the
      -- positive coefficient.
      have hb₂ : b₂ < 0 := by nlinarith
      have hAneg : A < 0 := by
        rw [hAdef]
        apply div_neg_of_neg_of_pos _ hΔ
        rw [sub_neg]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      refine hgen b₂ (fun t => Real.exp (-b₂ * t) + (-A) * Real.exp ((b₁ - b₂) * t) + (-B))
        ?_ ?_
      · have h := strictConvexOn_two_exp (c₁ := 1) (c₂ := -A) (a₁ := -b₂) (a₂ := b₁ - b₂)
          (d := -B) one_pos (by linarith) (by intro h; nlinarith) (by intro h; nlinarith)
        refine h.congr ?_
        intro t _
        simp only [one_mul]
      · intro t
        rw [mul_sub, mul_one]
        have e₁ : Real.exp (-b₂ * t) * (A * Real.exp (b₁ * t))
            = -((-A) * Real.exp ((b₁ - b₂) * t)) := by
          rw [show (-A) * Real.exp ((b₁ - b₂) * t) = -(A * Real.exp ((b₁ - b₂) * t)) by ring]
          rw [neg_neg]
          rw [show Real.exp (-b₂ * t) * (A * Real.exp (b₁ * t))
              = A * (Real.exp (-b₂ * t) * Real.exp (b₁ * t)) by ring, ← Real.exp_add]
          congr 2
          ring
        have e₂ : Real.exp (-b₂ * t) * (B * Real.exp (b₂ * t)) = B := by
          rw [show Real.exp (-b₂ * t) * (B * Real.exp (b₂ * t))
              = B * (Real.exp (-b₂ * t) * Real.exp (b₂ * t)) by ring, ← Real.exp_add,
            show -b₂ * t + b₂ * t = 0 by ring, Real.exp_zero, mul_one]
        rw [mul_add, e₁, e₂]
        ring
    · exact absurd hbb (by rw [hb₁]; simp)
    · -- Both exponents positive: rescale by `e^{-b₁t}`; then `B < 0` supplies the
      -- positive coefficient.
      have hb₂ : 0 < b₂ := by linarith
      have hBneg : B < 0 := by
        rw [hBdef]
        apply div_neg_of_neg_of_pos _ hΔ
        rw [sub_neg]
        exact Real.exp_lt_exp.mpr (by nlinarith)
      refine hgen b₁ (fun t => Real.exp (-b₁ * t) + (-B) * Real.exp ((b₂ - b₁) * t) + (-A))
        ?_ ?_
      · have h := strictConvexOn_two_exp (c₁ := 1) (c₂ := -B) (a₁ := -b₁) (a₂ := b₂ - b₁)
          (d := -A) one_pos (by linarith) (by intro h; nlinarith) (by intro h; nlinarith)
        refine h.congr ?_
        intro t _
        simp only [one_mul]
      · intro t
        rw [mul_sub, mul_one]
        have e₁ : Real.exp (-b₁ * t) * (A * Real.exp (b₁ * t)) = A := by
          rw [show Real.exp (-b₁ * t) * (A * Real.exp (b₁ * t))
              = A * (Real.exp (-b₁ * t) * Real.exp (b₁ * t)) by ring, ← Real.exp_add,
            show -b₁ * t + b₁ * t = 0 by ring, Real.exp_zero, mul_one]
        have e₂ : Real.exp (-b₁ * t) * (B * Real.exp (b₂ * t))
            = -((-B) * Real.exp ((b₂ - b₁) * t)) := by
          rw [show (-B) * Real.exp ((b₂ - b₁) * t) = -(B * Real.exp ((b₂ - b₁) * t)) by ring]
          rw [neg_neg]
          rw [show Real.exp (-b₁ * t) * (B * Real.exp (b₂ * t))
              = B * (Real.exp (-b₁ * t) * Real.exp (b₂ * t)) by ring, ← Real.exp_add]
          congr 2
          ring
        rw [mul_add, e₁, e₂]
        ring
  exact ⟨A, B, hv₁, hv₂, hmain.1, hmain.2.1, hmain.2.2⟩

/-- **Two exponentials of opposite sign crossing a constant twice.** For `b₁ < 0 < b₂` the
same interpolation coefficients are both *positive*, so `S(t) = A e^{b₁t} + B e^{b₂t}` is
itself strictly convex: it equals `1` at `C₁` and `C₂`, is strictly below `1` between them
and strictly above outside. This is the configuration at a parameter value *inside*
`(θ₁, θ₂)`, and the positivity of `A, B` is what supplies the nonnegative multipliers. -/
private lemma exists_exp_pair_sign_opp {b₁ b₂ C₁ C₂ : ℝ} (hb₁ : b₁ < 0) (hb₂ : 0 < b₂)
    (hC : C₁ < C₂) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      A * Real.exp (b₁ * C₁) + B * Real.exp (b₂ * C₁) = 1 ∧
      A * Real.exp (b₁ * C₂) + B * Real.exp (b₂ * C₂) = 1 ∧
      (∀ t : ℝ, C₁ < t → t < C₂ → A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) < 1) ∧
      (∀ t : ℝ, t < C₁ → 1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) ∧
      (∀ t : ℝ, C₂ < t → 1 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t)) := by
  have hb : b₁ < b₂ := hb₁.trans hb₂
  have hΔ : 0 < Real.exp (b₁ * C₁) * Real.exp (b₂ * C₂)
      - Real.exp (b₁ * C₂) * Real.exp (b₂ * C₁) := by
    rw [← Real.exp_add, ← Real.exp_add, sub_pos, Real.exp_lt_exp]
    nlinarith [mul_pos (sub_pos.mpr hb) (sub_pos.mpr hC)]
  set Δ := Real.exp (b₁ * C₁) * Real.exp (b₂ * C₂)
    - Real.exp (b₁ * C₂) * Real.exp (b₂ * C₁) with hΔdef
  set A := (Real.exp (b₂ * C₂) - Real.exp (b₂ * C₁)) / Δ with hAdef
  set B := (Real.exp (b₁ * C₁) - Real.exp (b₁ * C₂)) / Δ with hBdef
  have hΔne : Δ ≠ 0 := ne_of_gt hΔ
  have hApos : 0 < A := by
    rw [hAdef]
    refine div_pos ?_ hΔ
    rw [sub_pos]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hBpos : 0 < B := by
    rw [hBdef]
    refine div_pos ?_ hΔ
    rw [sub_pos]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  have hv₁ : A * Real.exp (b₁ * C₁) + B * Real.exp (b₂ * C₁) = 1 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hΔne, one_mul, hΔdef]
    ring
  have hv₂ : A * Real.exp (b₁ * C₂) + B * Real.exp (b₂ * C₂) = 1 := by
    rw [hAdef, hBdef, div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div,
      div_eq_iff hΔne, one_mul, hΔdef]
    ring
  have hgc : StrictConvexOn ℝ Set.univ
      fun t : ℝ => A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) + (-1) :=
    strictConvexOn_two_exp hApos hBpos (ne_of_lt hb₁) (ne_of_gt hb₂)
  have hg1 : (fun t : ℝ => A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) + (-1)) C₁ = 0 := by
    change A * Real.exp (b₁ * C₁) + B * Real.exp (b₂ * C₁) + (-1) = 0
    rw [hv₁]; ring
  have hg2 : (fun t : ℝ => A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) + (-1)) C₂ = 0 := by
    change A * Real.exp (b₁ * C₂) + B * Real.exp (b₂ * C₂) + (-1) = 0
    rw [hv₂]; ring
  obtain ⟨hin, hlo, hhi⟩ := sign_of_strictConvexOn_two_zeros hgc hC hg1 hg2
  refine ⟨A, B, hApos, hBpos, hv₁, hv₂, fun t h1 h2 => ?_, fun t h => ?_, fun t h => ?_⟩
  · have h' : A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) + (-1) < 0 := hin t h1 h2
    linarith
  · have h' : 0 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) + (-1) := hlo t h
    linarith
  · have h' : 0 < A * Real.exp (b₁ * t) + B * Real.exp (b₂ * t) + (-1) := hhi t h
    linarith

/-- The two-sided test is measurable when the statistic is. -/
private lemma measurable_twoSidedTest {T : 𝓧 → ℝ} (hT : Measurable T) (C₁ C₂ γ₁ γ₂ : ℝ) :
    Measurable (twoSidedTest T C₁ C₂ γ₁ γ₂) := by
  unfold twoSidedTest
  refine Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun hT measurable_const) measurable_const
      (Measurable.ite ?_ measurable_const measurable_const))
  exact (measurableSet_lt measurable_const hT).inter (measurableSet_lt hT measurable_const)

/-- **Minimum rejection probability outside the interval.** Among all tests whose size is
exactly `α` at both `θ₁` and `θ₂`, the two-sided test minimizes the rejection probability
at every parameter value below `θ₁` or above `θ₂`. -/
theorem power_min_twoSided
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, and its canonical presentation through a strictly
    -- increasing parametrization
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap) (hrepr : IsCanonicalRepr P E ηmap)
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the two null boundaries and the level
    {θ₁ θ₂ α : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: the constants of the test under study
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC : C₁ < C₂)
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the test satisfies the two size conditions
    (hsize₁ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α)
    (hsize₂ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α) :
    ∀ ψ, IsCriticalFn ψ → power P ψ θ₁ = α → power P ψ θ₂ = α →
      ∀ θ : ℝ, θ < θ₁ ∨ θ₂ < θ →
        power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ ≤ power P ψ θ := by
  -- The competitor class is defined by two *equality* constraints, so the sufficiency half
  -- of the generalized fundamental lemma applies with multipliers of arbitrary sign
  -- (`isMax_of_multiplier_form`); no inner-point or nonnegativity hypothesis is needed.
  -- Minimizing `∫φ p_θ` is maximizing `∫(1 − φ)p_θ`, and the co-test `1 − φ` has the
  -- multiplier shape for the coefficients produced by `exists_exp_pair_sign`: outside
  -- `[θ₁, θ₂]` the two canonical exponents `bᵢ = η(θᵢ) − η(θ)` have the same sign, so the
  -- level `{k₁p_{θ₁} + k₂p_{θ₂} = p_θ}` is crossed exactly at `C₁` and `C₂`.
  intro ψ hψ hψ₁ hψ₂ θ hθout
  classical
  set p : ℝ → 𝓧 → ℝ :=
    fun ϑ x => Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ)) with hpdef
  have hp : ∀ ϑ, HasDensity E.base (p ϑ) (P ϑ) := by
    intro ϑ
    refine ⟨((E.stat_meas.const_mul (ηmap ϑ)).sub_const _).exp,
      fun x => (Real.exp_pos _).le, ?_⟩
    rw [hrepr ϑ, E.P_eq_withDensity (hnat ϑ)]
    refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpdef, ts_real_inner_mul]
  have hppos : ∀ ϑ x, 0 < p ϑ x := fun ϑ x => Real.exp_pos _
  set φ := twoSidedTest E.stat C₁ C₂ γ₁ γ₂ with hφdef
  have hφc : IsCriticalFn φ := by
    refine ⟨measurable_twoSidedTest E.stat_meas C₁ C₂ γ₁ γ₂, fun x => ?_⟩
    rw [hφdef, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁ hγ₂ (E.stat x)
  have hcrit_int : ∀ χ : 𝓧 → ℝ, IsCriticalFn χ → ∀ ϑ : ℝ, Integrable χ (P ϑ) := by
    intro χ hχ ϑ
    refine (integrable_const (1 : ℝ)).mono' hχ.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ.2 x).1]
    exact (hχ.2 x).2
  -- The co-test integral in terms of the power function.
  have hcopow : ∀ χ : 𝓧 → ℝ, IsCriticalFn χ → ∀ ϑ : ℝ,
      ∫ x, (1 - χ x) * p ϑ x ∂E.base = 1 - power P χ ϑ := by
    intro χ hχ ϑ
    have hint1 : Integrable (p ϑ) E.base := ts_density_integrable (hp ϑ)
    have hint2 : Integrable (fun x => χ x * p ϑ x) E.base :=
      ts_density_mul_integrable (hp ϑ) (hcrit_int χ hχ ϑ)
    have hsplit : ∫ x, (1 - χ x) * p ϑ x ∂E.base = ∫ x, (p ϑ x - χ x * p ϑ x) ∂E.base :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hsplit, integral_sub hint1 hint2, ts_density_integral_one (hp ϑ)]
    congr 1
    exact (ts_integral_density_eq (hp ϑ) χ).symm
  -- The canonical exponents at `θ`, of the same sign because `θ` lies outside `[θ₁, θ₂]`.
  set b₁ := ηmap θ₁ - ηmap θ with hb₁def
  set b₂ := ηmap θ₂ - ηmap θ with hb₂def
  have hb : b₁ < b₂ := by
    rw [hb₁def, hb₂def]; linarith [hη hθ]
  have hbb : 0 < b₁ * b₂ := by
    rcases hθout with hlow | hhigh
    · have h1 : 0 < b₁ := by rw [hb₁def]; linarith [hη hlow]
      have h2 : 0 < b₂ := by rw [hb₂def]; linarith [hη (hlow.trans hθ)]
      exact mul_pos h1 h2
    · have h2 : b₂ < 0 := by rw [hb₂def]; linarith [hη hhigh]
      have h1 : b₁ < 0 := by linarith
      exact mul_pos_of_neg_of_neg h1 h2
  obtain ⟨A, B, hvA, hvB, hin, hlo, hhi⟩ := exists_exp_pair_sign hb hbb hC
  -- The multipliers, and the identity `k₁p_{θ₁} + k₂p_{θ₂} = p_θ · S(T)`.
  set k₁ := A * Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap θ)) with hk₁def
  set k₂ := B * Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap θ)) with hk₂def
  have hkey : ∀ x : 𝓧, k₁ * p θ₁ x + k₂ * p θ₂ x
      = p θ x * (A * Real.exp (b₁ * E.stat x) + B * Real.exp (b₂ * E.stat x)) := by
    intro x
    have e₁ : Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap θ))
        * Real.exp (ηmap θ₁ * E.stat x - E.logPartition (ηmap θ₁))
        = Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ))
          * Real.exp (b₁ * E.stat x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hb₁def]; ring
    have e₂ : Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap θ))
        * Real.exp (ηmap θ₂ * E.stat x - E.logPartition (ηmap θ₂))
        = Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ))
          * Real.exp (b₂ * E.stat x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hb₂def]; ring
    simp only [hk₁def, hk₂def, hpdef]
    calc A * Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap θ))
          * Real.exp (ηmap θ₁ * E.stat x - E.logPartition (ηmap θ₁))
        + B * Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap θ))
          * Real.exp (ηmap θ₂ * E.stat x - E.logPartition (ηmap θ₂))
        = A * (Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap θ))
            * Real.exp (ηmap θ₁ * E.stat x - E.logPartition (ηmap θ₁)))
          + B * (Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap θ))
            * Real.exp (ηmap θ₂ * E.stat x - E.logPartition (ηmap θ₂))) := by ring
      _ = A * (Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ))
            * Real.exp (b₁ * E.stat x))
          + B * (Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ))
            * Real.exp (b₂ * E.stat x)) := by rw [e₁, e₂]
      _ = Real.exp (ηmap θ * E.stat x - E.logPartition (ηmap θ))
            * (A * Real.exp (b₁ * E.stat x) + B * Real.exp (b₂ * E.stat x)) := by ring
  -- The values of the two-sided test off and on the rejection interval.
  have hφ0 : ∀ x : 𝓧, E.stat x < C₁ ∨ C₂ < E.stat x → φ x = 0 := by
    intro x hx
    rw [hφdef]
    unfold twoSidedTest
    rcases hx with h | h
    · rw [if_neg (ne_of_lt h), if_neg (ne_of_lt (by linarith)),
        if_neg (by rintro ⟨h1, -⟩; linarith)]
    · rw [if_neg (ne_of_gt (by linarith)), if_neg (ne_of_gt h),
        if_neg (by rintro ⟨-, h2⟩; linarith)]
  have hφ1 : ∀ x : 𝓧, C₁ < E.stat x → E.stat x < C₂ → φ x = 1 := by
    intro x h1 h2
    rw [hφdef]
    unfold twoSidedTest
    rw [if_neg (ne_of_gt h1), if_neg (ne_of_lt h2), if_pos ⟨h1, h2⟩]
  -- The data of the two-constraint problem.
  set f : Fin 3 → 𝓧 → ℝ := ![p θ₁, p θ₂, p θ] with hfdef
  have hf0 : f (Fin.castSucc (0 : Fin 2)) = p θ₁ := rfl
  have hf1 : f (Fin.castSucc (1 : Fin 2)) = p θ₂ := rfl
  have hflast : f (Fin.last 2) = p θ := rfl
  have hfmeas : ∀ i, Measurable (f i) := by
    intro i
    have hm : ∀ ϑ : ℝ, Measurable (p ϑ) := fun ϑ =>
      ((E.stat_meas.const_mul (ηmap ϑ)).sub_const _).exp
    fin_cases i
    · exact hm θ₁
    · exact hm θ₂
    · exact hm θ
  have hfint : ∀ i, Integrable (f i) E.base := by
    intro i
    fin_cases i
    · exact ts_density_integrable (hp θ₁)
    · exact ts_density_integrable (hp θ₂)
    · exact ts_density_integrable (hp θ)
  have hcocrit : ∀ χ : 𝓧 → ℝ, IsCriticalFn χ → IsCriticalFn fun x => 1 - χ x := by
    intro χ hχ
    refine ⟨measurable_const.sub hχ.1, fun x => ?_⟩
    obtain ⟨h0, h1⟩ := hχ.2 x
    exact ⟨by linarith, by linarith⟩
  have hcon : ∀ i : Fin 2, ∫ x, (1 - φ x) * f i.castSucc x ∂E.base = ![1 - α, 1 - α] i := by
    intro i
    fin_cases i
    · change ∫ x, (1 - φ x) * p θ₁ x ∂E.base = 1 - α
      rw [hcopow φ hφc θ₁, hsize₁]
    · change ∫ x, (1 - φ x) * p θ₂ x ∂E.base = 1 - α
      rw [hcopow φ hφc θ₂, hsize₂]
  have hψcon : ∀ i : Fin 2, ∫ x, (1 - ψ x) * f i.castSucc x ∂E.base = ![1 - α, 1 - α] i := by
    intro i
    fin_cases i
    · change ∫ x, (1 - ψ x) * p θ₁ x ∂E.base = 1 - α
      rw [hcopow ψ hψ θ₁, hψ₁]
    · change ∫ x, (1 - ψ x) * p θ₂ x ∂E.base = 1 - α
      rw [hcopow ψ hψ θ₂, hψ₂]
  have hsum : ∀ x : 𝓧, ∑ i : Fin 2, ![k₁, k₂] i * f i.castSucc x
      = k₁ * p θ₁ x + k₂ * p θ₂ x := by
    intro x
    rw [Fin.sum_univ_two]
    rfl
  have hshape : HasMultiplierShape E.base f ![k₁, k₂] fun x => 1 - φ x := by
    constructor
    · refine Filter.Eventually.of_forall fun x hx => ?_
      rw [hsum x, hkey x, hflast] at hx
      have hS : A * Real.exp (b₁ * E.stat x) + B * Real.exp (b₂ * E.stat x) < 1 := by
        nlinarith [hppos θ x]
      have hout : E.stat x < C₁ ∨ C₂ < E.stat x := by
        rcases lt_trichotomy (E.stat x) C₁ with h | h | h
        · exact Or.inl h
        · rw [h] at hS; linarith [hvA]
        · rcases lt_trichotomy (E.stat x) C₂ with h' | h' | h'
          · exact absurd (hin (E.stat x) h h') (by linarith)
          · rw [h'] at hS; linarith [hvB]
          · exact Or.inr h'
      change (1 : ℝ) - φ x = 1
      rw [hφ0 x hout]; ring
    · refine Filter.Eventually.of_forall fun x hx => ?_
      rw [hsum x, hkey x, hflast] at hx
      have hS : 1 < A * Real.exp (b₁ * E.stat x) + B * Real.exp (b₂ * E.stat x) := by
        nlinarith [hppos θ x]
      have h1 : C₁ < E.stat x := by
        rcases lt_trichotomy (E.stat x) C₁ with h | h | h
        · exact absurd (hlo (E.stat x) h) (by linarith)
        · rw [h] at hS; linarith [hvA]
        · exact h
      have h2 : E.stat x < C₂ := by
        rcases lt_trichotomy (E.stat x) C₂ with h | h | h
        · exact h
        · rw [h] at hS; linarith [hvB]
        · exact absurd (hhi (E.stat x) h) (by linarith)
      change (1 : ℝ) - φ x = 0
      rw [hφ1 x h1 h2]; ring
  have hmax := isMax_of_multiplier_form (m := 2) E.base (f := f) hfmeas hfint
    (hcocrit φ hφc) hcon hshape (fun x => 1 - ψ x) (hcocrit ψ hψ) hψcon
  rw [hflast, hcopow ψ hψ θ, hcopow φ hφc θ] at hmax
  linarith

/-- **The two-sided test is uniformly most powerful once its two sizes are exactly `α`.**
This is the whole of `isUMP_twoSided` except for the existence of the four constants: the
level condition on `H : θ ≤ θ₁ or θ₂ ≤ θ` is `power_min_twoSided` compared against the
constant test `α`, and optimality on `K = (θ₁, θ₂)` is the *nonnegative*-multiplier form of
the generalized fundamental lemma, whose multipliers are the positive coefficients supplied
by `exists_exp_pair_sign_opp` (inside `(θ₁, θ₂)` the two canonical exponents
`bᵢ = η(θᵢ) − η(θ)` have opposite signs, which is exactly what makes both coefficients
positive and the rejection region an interval). -/
private lemma isUMP_twoSided_of_constants
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap) (hrepr : IsCanonicalRepr P E ηmap)
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    {θ₁ θ₂ α : ℝ} (hθ : θ₁ < θ₂)
    {C₁ C₂ γ₁ γ₂ : ℝ} (hC : C₁ < C₂)
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hsize₁ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α)
    (hsize₂ : power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α) :
    IsUMP P {θ : ℝ | θ ≤ θ₁ ∨ θ₂ ≤ θ} (Set.Ioo θ₁ θ₂) α
      (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) := by
  classical
  set p : ℝ → 𝓧 → ℝ :=
    fun ϑ x => Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ)) with hpdef
  have hp : ∀ ϑ, HasDensity E.base (p ϑ) (P ϑ) := by
    intro ϑ
    refine ⟨((E.stat_meas.const_mul (ηmap ϑ)).sub_const _).exp,
      fun x => (Real.exp_pos _).le, ?_⟩
    rw [hrepr ϑ, E.P_eq_withDensity (hnat ϑ)]
    refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpdef, ts_real_inner_mul]
  have hppos : ∀ ϑ x, 0 < p ϑ x := fun ϑ x => Real.exp_pos _
  set φ := twoSidedTest E.stat C₁ C₂ γ₁ γ₂ with hφdef
  have hφc : IsCriticalFn φ := by
    refine ⟨measurable_twoSidedTest E.stat_meas C₁ C₂ γ₁ γ₂, fun x => ?_⟩
    rw [hφdef, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁ hγ₂ (E.stat x)
  have hcrit_int : ∀ χ : 𝓧 → ℝ, IsCriticalFn χ → ∀ ϑ : ℝ, Integrable χ (P ϑ) := by
    intro χ hχ ϑ
    refine (integrable_const (1 : ℝ)).mono' hχ.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ.2 x).1]
    exact (hχ.2 x).2
  have hpow : ∀ (χ : 𝓧 → ℝ) (ϑ : ℝ), power P χ ϑ = ∫ x, χ x * p ϑ x ∂E.base := by
    intro χ ϑ
    unfold power
    exact ts_integral_density_eq (hp ϑ) χ
  -- The level lies in `[0,1]`, being the size of a critical function.
  have hα0 : 0 ≤ α := by
    rw [← hsize₁]
    unfold power
    exact integral_nonneg fun x => (hφc.2 x).1
  have hα1 : α ≤ 1 := by
    rw [← hsize₁]
    unfold power
    have h := integral_mono (hcrit_int φ hφc θ₁) (integrable_const (1 : ℝ))
      (fun x => (hφc.2 x).2)
    simpa using h
  have hconstcrit : IsCriticalFn fun _ : 𝓧 => α := ⟨measurable_const, fun _ => ⟨hα0, hα1⟩⟩
  have hconstpow : ∀ ϑ : ℝ, power P (fun _ : 𝓧 => α) ϑ = α := by
    intro ϑ
    unfold power
    rw [integral_const]
    simp
  refine ⟨hφc, ?_, ?_⟩
  · -- Level: outside `[θ₁, θ₂]` the constant test `α` is a legitimate competitor.
    intro ϑ hϑ
    have hmin := power_min_twoSided E P hη hrepr hnat hθ hC hγ₁ hγ₂ hsize₁ hsize₂
      (fun _ : 𝓧 => α) hconstcrit (hconstpow θ₁) (hconstpow θ₂)
    rcases hϑ with h | h
    · rcases eq_or_lt_of_le h with heq | hlt
      · rw [heq, hsize₁]
      · have := hmin ϑ (Or.inl hlt)
        rw [hconstpow ϑ] at this
        exact this
    · rcases eq_or_lt_of_le h with heq | hlt
      · rw [← heq, hsize₂]
      · have := hmin ϑ (Or.inr hlt)
        rw [hconstpow ϑ] at this
        exact this
  · -- Optimality on `(θ₁, θ₂)`.
    intro χ hχ hχlevel ϑ hϑ
    obtain ⟨hϑ1, hϑ2⟩ := Set.mem_Ioo.mp hϑ
    have hb₁ : ηmap θ₁ - ηmap ϑ < 0 := by linarith [hη hϑ1]
    have hb₂ : 0 < ηmap θ₂ - ηmap ϑ := by linarith [hη hϑ2]
    obtain ⟨A, B, hApos, hBpos, hvA, hvB, hin, hlo, hhi⟩ :=
      exists_exp_pair_sign_opp hb₁ hb₂ hC
    set k₁ := A * Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap ϑ)) with hk₁def
    set k₂ := B * Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap ϑ)) with hk₂def
    have hkey : ∀ x : 𝓧, k₁ * p θ₁ x + k₂ * p θ₂ x
        = p ϑ x * (A * Real.exp ((ηmap θ₁ - ηmap ϑ) * E.stat x)
          + B * Real.exp ((ηmap θ₂ - ηmap ϑ) * E.stat x)) := by
      intro x
      have e₁ : Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap ϑ))
          * Real.exp (ηmap θ₁ * E.stat x - E.logPartition (ηmap θ₁))
          = Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ))
            * Real.exp ((ηmap θ₁ - ηmap ϑ) * E.stat x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have e₂ : Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap ϑ))
          * Real.exp (ηmap θ₂ * E.stat x - E.logPartition (ηmap θ₂))
          = Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ))
            * Real.exp ((ηmap θ₂ - ηmap ϑ) * E.stat x) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      simp only [hk₁def, hk₂def, hpdef]
      calc A * Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap ϑ))
            * Real.exp (ηmap θ₁ * E.stat x - E.logPartition (ηmap θ₁))
          + B * Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap ϑ))
            * Real.exp (ηmap θ₂ * E.stat x - E.logPartition (ηmap θ₂))
          = A * (Real.exp (E.logPartition (ηmap θ₁) - E.logPartition (ηmap ϑ))
              * Real.exp (ηmap θ₁ * E.stat x - E.logPartition (ηmap θ₁)))
            + B * (Real.exp (E.logPartition (ηmap θ₂) - E.logPartition (ηmap ϑ))
              * Real.exp (ηmap θ₂ * E.stat x - E.logPartition (ηmap θ₂))) := by ring
        _ = A * (Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ))
              * Real.exp ((ηmap θ₁ - ηmap ϑ) * E.stat x))
            + B * (Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ))
              * Real.exp ((ηmap θ₂ - ηmap ϑ) * E.stat x)) := by rw [e₁, e₂]
        _ = Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ))
              * (A * Real.exp ((ηmap θ₁ - ηmap ϑ) * E.stat x)
                + B * Real.exp ((ηmap θ₂ - ηmap ϑ) * E.stat x)) := by ring
    have hφ0 : ∀ x : 𝓧, E.stat x < C₁ ∨ C₂ < E.stat x → φ x = 0 := by
      intro x hx
      rw [hφdef]
      unfold twoSidedTest
      rcases hx with h | h
      · rw [if_neg (ne_of_lt h), if_neg (ne_of_lt (by linarith)),
          if_neg (by rintro ⟨h1, -⟩; linarith)]
      · rw [if_neg (ne_of_gt (by linarith)), if_neg (ne_of_gt h),
          if_neg (by rintro ⟨-, h2⟩; linarith)]
    have hφ1 : ∀ x : 𝓧, C₁ < E.stat x → E.stat x < C₂ → φ x = 1 := by
      intro x h1 h2
      rw [hφdef]
      unfold twoSidedTest
      rw [if_neg (ne_of_gt h1), if_neg (ne_of_lt h2), if_pos ⟨h1, h2⟩]
    set f : Fin 3 → 𝓧 → ℝ := ![p θ₁, p θ₂, p ϑ] with hfdef
    have hflast : f (Fin.last 2) = p ϑ := rfl
    have hfmeas : ∀ i, Measurable (f i) := by
      intro i
      have hm : ∀ ζ : ℝ, Measurable (p ζ) := fun ζ =>
        ((E.stat_meas.const_mul (ηmap ζ)).sub_const _).exp
      fin_cases i
      · exact hm θ₁
      · exact hm θ₂
      · exact hm ϑ
    have hfint : ∀ i, Integrable (f i) E.base := by
      intro i
      fin_cases i
      · exact ts_density_integrable (hp θ₁)
      · exact ts_density_integrable (hp θ₂)
      · exact ts_density_integrable (hp ϑ)
    have hcon : ∀ i : Fin 2, ∫ x, φ x * f i.castSucc x ∂E.base = ![α, α] i := by
      intro i
      fin_cases i
      · change ∫ x, φ x * p θ₁ x ∂E.base = α
        rw [← hpow φ θ₁, hsize₁]
      · change ∫ x, φ x * p θ₂ x ∂E.base = α
        rw [← hpow φ θ₂, hsize₂]
    have hχcon : ∀ i : Fin 2, ∫ x, χ x * f i.castSucc x ∂E.base ≤ ![α, α] i := by
      intro i
      fin_cases i
      · change ∫ x, χ x * p θ₁ x ∂E.base ≤ α
        rw [← hpow χ θ₁]
        exact hχlevel θ₁ (Or.inl le_rfl)
      · change ∫ x, χ x * p θ₂ x ∂E.base ≤ α
        rw [← hpow χ θ₂]
        exact hχlevel θ₂ (Or.inr le_rfl)
    have hknn : ∀ i : Fin 2, 0 ≤ ![k₁, k₂] i := by
      intro i
      fin_cases i
      · exact le_of_lt (mul_pos hApos (Real.exp_pos _))
      · exact le_of_lt (mul_pos hBpos (Real.exp_pos _))
    have hsum : ∀ x : 𝓧, ∑ i : Fin 2, ![k₁, k₂] i * f i.castSucc x
        = k₁ * p θ₁ x + k₂ * p θ₂ x := by
      intro x
      rw [Fin.sum_univ_two]
      rfl
    have hshape : HasMultiplierShape E.base f ![k₁, k₂] φ := by
      constructor
      · refine Filter.Eventually.of_forall fun x hx => ?_
        rw [hsum x, hkey x, hflast] at hx
        have hS : A * Real.exp ((ηmap θ₁ - ηmap ϑ) * E.stat x)
            + B * Real.exp ((ηmap θ₂ - ηmap ϑ) * E.stat x) < 1 := by
          nlinarith [hppos ϑ x]
        have h1 : C₁ < E.stat x := by
          rcases lt_trichotomy (E.stat x) C₁ with h | h | h
          · exact absurd (hlo (E.stat x) h) (by linarith)
          · rw [h] at hS; linarith [hvA]
          · exact h
        have h2 : E.stat x < C₂ := by
          rcases lt_trichotomy (E.stat x) C₂ with h | h | h
          · exact h
          · rw [h] at hS; linarith [hvB]
          · exact absurd (hhi (E.stat x) h) (by linarith)
        exact hφ1 x h1 h2
      · refine Filter.Eventually.of_forall fun x hx => ?_
        rw [hsum x, hkey x, hflast] at hx
        have hS : 1 < A * Real.exp ((ηmap θ₁ - ηmap ϑ) * E.stat x)
            + B * Real.exp ((ηmap θ₂ - ηmap ϑ) * E.stat x) := by
          nlinarith [hppos ϑ x]
        have hout : E.stat x < C₁ ∨ C₂ < E.stat x := by
          rcases lt_trichotomy (E.stat x) C₁ with h | h | h
          · exact Or.inl h
          · rw [h] at hS; linarith [hvA]
          · rcases lt_trichotomy (E.stat x) C₂ with h' | h' | h'
            · exact absurd (hin (E.stat x) h h') (by linarith)
            · rw [h'] at hS; linarith [hvB]
            · exact Or.inr h'
        exact hφ0 x hout
    have hmax := isMax_le_of_multiplier_form_nonneg (m := 2) E.base (f := f) hfmeas hfint
      hφc hcon hknn hshape χ hχ hχcon
    rw [hflast, ← hpow χ ϑ, ← hpow φ ϑ] at hmax
    exact hmax

/-- **Monotone-rearrangement (Chebyshev-sum) inequality on `[0,1]`.** For a nondecreasing
integrable `g`, the integral over the initial segment `[0, α]` is at most `α` times the
integral over the whole interval, and the integral over the final segment `[α, 1]` is at
least `(1 − α)` times it.

This is brick (c) of the quantile-sweep roadmap recorded at `isUMP_twoSided`: with
`g = r ∘ Q` — the likelihood ratio `dν₂/dν₁` read along the quantile function of `ν₁`, which
is nondecreasing because `η₂ > η₁` — and `∫₀¹ g = 1`, it gives `h(0) ≤ α ≤ h(1 − α)` for the
sliding-window size `h(s) = ∫_s^{s+α} g`, which is what the intermediate value theorem then
consumes.

The proof is the two-sided comparison against the value at the split point: `g ≤ g α` on
`[0, α]` and `g α ≤ g` on `[α, 1]`, so `(1 − α)·∫₀^α g ≤ (1 − α)·α·g α ≤ α·∫_α^1 g`, and
adding `α·∫₀^α g` to both sides gives the first claim. -/
private lemma integral_Ioc_le_of_monotoneOn {g : ℝ → ℝ} {α : ℝ}
    (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) (hint : IntegrableOn g (Set.Icc (0 : ℝ) 1))
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..α, g u) ≤ α * ∫ u in (0 : ℝ)..1, g u ∧
      (1 - α) * (∫ u in (0 : ℝ)..1, g u) ≤ ∫ u in α..(1 : ℝ), g u := by
  obtain ⟨hα0, hα1⟩ := hα
  have hsubL : Set.uIoc (0 : ℝ) α ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le hα0]
    exact fun u hu => ⟨hu.1.le, hu.2.trans hα1⟩
  have hsubR : Set.uIoc α (1 : ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le hα1]
    exact fun u hu => ⟨hα0.trans hu.1.le, hu.2⟩
  have hsubF : Set.uIoc (0 : ℝ) (1 : ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact fun u hu => ⟨hu.1.le, hu.2⟩
  have hIL : IntervalIntegrable g MeasureTheory.volume 0 α :=
    intervalIntegrable_iff.2 (hint.mono_set hsubL)
  have hIR : IntervalIntegrable g MeasureTheory.volume α 1 :=
    intervalIntegrable_iff.2 (hint.mono_set hsubR)
  have hsplit : (∫ u in (0 : ℝ)..α, g u) + ∫ u in α..(1 : ℝ), g u = ∫ u in (0 : ℝ)..1, g u :=
    intervalIntegral.integral_add_adjacent_intervals hIL hIR
  have hαmem : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα0, hα1⟩
  -- the initial segment is below `α · g α`
  have hleft : (∫ u in (0 : ℝ)..α, g u) ≤ α * g α := by
    have h := intervalIntegral.integral_mono_on hα0 hIL
      (intervalIntegrable_const (c := g α)) (fun u hu =>
        hg ⟨hu.1, hu.2.trans hα1⟩ hαmem hu.2)
    simpa using h
  -- the final segment is above `(1 − α) · g α`
  have hright : (1 - α) * g α ≤ ∫ u in α..(1 : ℝ), g u := by
    have h := intervalIntegral.integral_mono_on hα1
      (intervalIntegrable_const (c := g α)) hIR (fun u hu =>
        hg hαmem ⟨hα0.trans hu.1, hu.2⟩ hu.1)
    simpa using h
  have hcross : (1 - α) * (∫ u in (0 : ℝ)..α, g u) ≤ α * ∫ u in α..(1 : ℝ), g u := by
    have h1 : (1 - α) * (∫ u in (0 : ℝ)..α, g u) ≤ (1 - α) * (α * g α) :=
      mul_le_mul_of_nonneg_left hleft (by linarith)
    have h2 : α * ((1 - α) * g α) ≤ α * ∫ u in α..(1 : ℝ), g u :=
      mul_le_mul_of_nonneg_left hright hα0
    nlinarith [h1, h2]
  constructor
  · rw [← hsplit]; nlinarith [hcross]
  · rw [← hsplit]; nlinarith [hcross]

section QuantileWindow

open Filter Topology ProbabilityTheory

/-- The `p`-sublevel set of a distribution function is nonempty and bounded below. -/
private lemma cdf_level_nonempty_bddBelow (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    {y : ℝ | p ≤ cdf ν y}.Nonempty ∧ BddBelow {y : ℝ | p ≤ cdf ν y} := by
  constructor
  · obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop ν).eventually_const_lt hp1).exists
    exact ⟨y, hy.le⟩
  · obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot ν).eventually_lt_const hp0)
    refine ⟨b, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy
    by_contra hcon
    exact absurd (hb y (not_le.mp hcon).le) (not_lt.mpr hy)

/-- The two defining inequalities of a quantile: the distribution function has reached `p` at
`quantile F p`, and its left limit there has not passed `p`. -/
private lemma cdf_quantile_bounds (ν : Measure ℝ) [IsProbabilityMeasure ν] {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ cdf ν (quantile (⇑(cdf ν)) p) ∧
      Function.leftLim (⇑(cdf ν)) (quantile (⇑(cdf ν)) p) ≤ p := by
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  have hrc : ∀ y : ℝ, ContinuousWithinAt (⇑(cdf ν)) (Set.Ici y) y :=
    fun y => (cdf ν).right_continuous y
  obtain ⟨hne, hbdd⟩ := cdf_level_nonempty_bddBelow ν hp0 hp1
  have hA : p ≤ cdf ν (quantile (⇑(cdf ν)) p) :=
    (quantile_le_iff hmono hrc hne hbdd).mp le_rfl
  refine ⟨hA, ?_⟩
  have hB : ∀ y, y < quantile (⇑(cdf ν)) p → cdf ν y < p := by
    intro y hy
    by_contra h
    exact absurd ((quantile_le_iff hmono hrc hne hbdd).mpr (not_lt.mp h)) (not_le.mpr hy)
  have htend : Tendsto (⇑(cdf ν)) (𝓝[<] (quantile (⇑(cdf ν)) p))
      (𝓝 (Function.leftLim (⇑(cdf ν)) (quantile (⇑(cdf ν)) p))) :=
    hmono.tendsto_leftLim _
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hB y hy).le

/-- **The quantile function is constant on the level interval of an atom.** If
`F(x⁻) < u ≤ F(x)` then `quantile F u = x`. The window `(F(x⁻), F(x)]` is the atom of `ν` at
`x` read in *level* space; this lemma says the quantile function collapses it back to `x`,
and it is what makes the two boundary terms of brick (b) below explicit. -/
private lemma quantile_eq_of_leftLim_lt (ν : Measure ℝ) [IsProbabilityMeasure ν] {x u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1)
    (hlo : Function.leftLim (⇑(cdf ν)) x < u) (hhi : u ≤ cdf ν x) :
    quantile (⇑(cdf ν)) u = x := by
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  have hrc : ∀ y : ℝ, ContinuousWithinAt (⇑(cdf ν)) (Set.Ici y) y :=
    fun y => (cdf ν).right_continuous y
  obtain ⟨hne, hbdd⟩ := cdf_level_nonempty_bddBelow ν hu0 hu1
  refine le_antisymm ((quantile_le_iff hmono hrc hne hbdd).mpr hhi) ?_
  by_contra hcon
  have hlt : quantile (⇑(cdf ν)) u < x := not_le.mp hcon
  have h1 : u ≤ cdf ν (quantile (⇑(cdf ν)) u) := (cdf_quantile_bounds ν hu0 hu1).1
  have h2 : cdf ν (quantile (⇑(cdf ν)) u) ≤ Function.leftLim (⇑(cdf ν)) x :=
    hmono.le_leftLim hlt
  linarith

/-- The levels whose quantile lies below `x`, read inside the unit interval, form the level
window `(0, F x]` up to a Lebesgue-null set — the Galois property `quantile F u ≤ x ↔ u ≤ F x`
in measure form, the null set being the single endpoint `1`. -/
private lemma quantile_preimage_Iic_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ((quantile (⇑(cdf ν)) ⁻¹' Set.Iic x) ∩ Set.Icc (0 : ℝ) 1 : Set ℝ)
      =ᵐ[MeasureTheory.volume] (Set.Ioc (0 : ℝ) (cdf ν x) : Set ℝ) := by
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  have hrc : ∀ y : ℝ, ContinuousWithinAt (⇑(cdf ν)) (Set.Ici y) y :=
    fun y => (cdf ν).right_continuous y
  have ha1 : cdf ν x ≤ 1 := cdf_le_one ν x
  have hIccIoo : Set.Icc (0 : ℝ) 1 =ᵐ[MeasureTheory.volume] Set.Ioo 0 1 := Ioo_ae_eq_Icc.symm
  have hstep : (quantile (⇑(cdf ν)) ⁻¹' Set.Iic x) ∩ Set.Ioo (0 : ℝ) 1
      = Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (cdf ν x) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨hqt, hu⟩
      obtain ⟨hne, hbdd⟩ := cdf_level_nonempty_bddBelow ν hu.1 hu.2
      exact ⟨hu, (quantile_le_iff hmono hrc hne hbdd).mp hqt⟩
    · rintro ⟨hu, hle⟩
      obtain ⟨hne, hbdd⟩ := cdf_level_nonempty_bddBelow ν hu.1 hu.2
      exact ⟨(quantile_le_iff hmono hrc hne hbdd).mpr hle, hu⟩
  have hcong : ((quantile (⇑(cdf ν)) ⁻¹' Set.Iic x) ∩ Set.Icc (0 : ℝ) 1 : Set ℝ)
      =ᵐ[MeasureTheory.volume] (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic (cdf ν x) : Set ℝ) := by
    refine (Filter.EventuallyEq.inter (ae_eq_refl _) hIccIoo).trans ?_
    rw [hstep]; exact ae_eq_refl _
  refine hcong.trans ?_
  rw [ae_eq_set]
  constructor
  · convert measure_empty (μ := MeasureTheory.volume)
    rw [Set.diff_eq_empty]
    rintro u ⟨⟨h0, -⟩, hle⟩
    exact ⟨h0, hle⟩
  · refine measure_mono_null ?_ (Real.volume_singleton (a := 1))
    rintro u ⟨⟨h0, hle⟩, hnot⟩
    rw [Set.mem_singleton_iff]
    by_contra hu1
    exact hnot ⟨⟨h0, lt_of_le_of_ne (le_trans hle ha1) hu1⟩, hle⟩

/-- **Change of variables along the quantile function, on a half-line.** For measurable `g`,
`∫_{(-∞,x]} g dν = ∫_0^{F x} g(Q u) du`.

This is the inverse-transform identity `map_quantile_uniform` localized to `Iic x`, and it is
the analytic half of brick (b): it converts the two `ν`-masses that the sliding window cuts
off into ordinary Lebesgue integrals of `g ∘ Q` over level intervals. -/
private lemma setIntegral_Iic_eq_intervalIntegral_quantile (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {g : ℝ → ℝ} (hg : Measurable g) (x : ℝ) :
    ∫ t in Set.Iic x, g t ∂ν
      = ∫ u in (0 : ℝ)..(cdf ν x), g (quantile (⇑(cdf ν)) u) := by
  classical
  have hFdef : ∀ y : ℝ, (⇑(cdf ν)) y = (ν (Set.Iic y)).toReal := fun y => by
    rw [cdf_eq_real]; rfl
  set Q : ℝ → ℝ := quantile (⇑(cdf ν)) with hQ
  set m : Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1) with hm
  have hmap : m.map Q = ν := map_quantile_uniform ν _ hFdef
  have h0 : (0 : ℝ) ≤ cdf ν x := cdf_nonneg ν x
  have h1 : cdf ν x ≤ 1 := cdf_le_one ν x
  -- the quantile function is a.e. measurable on the unit interval, being monotone there
  have haem : AEMeasurable Q m := by
    have hmonoOn : MonotoneOn Q (Set.Ioo 0 1) := by
      intro a ha b hb hab
      exact quantile_mono _ hab (cdf_level_nonempty_bddBelow ν ha.1 ha.2).2
        (cdf_level_nonempty_bddBelow ν hb.1 hb.2).1
    have hIccIoo : Set.Icc (0 : ℝ) 1 =ᵐ[MeasureTheory.volume] Set.Ioo 0 1 := Ioo_ae_eq_Icc.symm
    rw [hm, Measure.restrict_congr_set hIccIoo]
    exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hmonoOn
  have hasm : AEStronglyMeasurable (Set.indicator (Set.Iic x) g) (m.map Q) := by
    rw [hmap]
    exact (hg.indicator measurableSet_Iic).aestronglyMeasurable
  have hstep1 : ∫ t in Set.Iic x, g t ∂ν = ∫ u, Set.indicator (Set.Iic x) g (Q u) ∂m := by
    rw [← integral_indicator measurableSet_Iic, ← hmap, integral_map haem hasm]
  have hset := quantile_preimage_Iic_ae ν x
  rw [← hQ] at hset
  have hstep2 : ∫ u, Set.indicator (Set.Iic x) g (Q u) ∂m
      = ∫ u, Set.indicator (Set.Ioc (0 : ℝ) (cdf ν x)) (fun v => g (Q v)) u ∂m := by
    refine integral_congr_ae ?_
    have hmem : ∀ᵐ u ∂m, u ∈ Set.Icc (0 : ℝ) 1 := by
      rw [hm]; exact ae_restrict_mem measurableSet_Icc
    have hae : ∀ᵐ u ∂m, (u ∈ (Q ⁻¹' Set.Iic x) ∩ Set.Icc (0 : ℝ) 1)
        = (u ∈ Set.Ioc (0 : ℝ) (cdf ν x)) := by
      rw [hm]; exact ae_restrict_of_ae hset
    filter_upwards [hmem, hae] with u hu hueq
    by_cases hQx : Q u ∈ Set.Iic x
    · have huB : u ∈ Set.Ioc (0 : ℝ) (cdf ν x) := hueq ▸ (⟨hQx, hu⟩ :
        u ∈ (Q ⁻¹' Set.Iic x) ∩ Set.Icc (0 : ℝ) 1)
      rw [Set.indicator_of_mem hQx, Set.indicator_of_mem huB]
    · have huA : u ∉ (Q ⁻¹' Set.Iic x) ∩ Set.Icc (0 : ℝ) 1 := fun h => hQx h.1
      have huB : u ∉ Set.Ioc (0 : ℝ) (cdf ν x) := fun h => huA (hueq ▸ h)
      rw [Set.indicator_of_notMem hQx, Set.indicator_of_notMem huB]
  have hsub : Set.Ioc (0 : ℝ) (cdf ν x) ⊆ Set.Icc (0 : ℝ) 1 :=
    fun u hu => ⟨hu.1.le, hu.2.trans h1⟩
  rw [hstep1, hstep2, integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le h0, hm, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left hsub]

/-- Interval integrability inside the unit interval, from integrability on it. -/
private lemma intervalIntegrable_of_Icc01 {g : ℝ → ℝ}
    (hint : IntegrableOn g (Set.Icc (0 : ℝ) 1) MeasureTheory.volume) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable g MeasureTheory.volume x y := by
  refine intervalIntegrable_iff.2 (hint.mono_set fun u hu => ?_)
  rcases Set.mem_uIoc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans hx.1 h1.le, le_trans h2 hy.2⟩
  · exact ⟨le_trans hy.1 h1.le, le_trans h2 hx.2⟩

/-- **Strict monotone-rearrangement inequality.** For a nondecreasing integrable `g` on
`[0,1]` which is *not* essentially constant — it separates strictly across some level
`a ∈ (0,1)` — the initial-segment integral is *strictly* below its proportional share:
`∫₀^α g < α ∫₀¹ g` for every `α ∈ (0,1)`.

This is the strict form of brick (c) of the quantile-sweep roadmap at `isUMP_twoSided`, and
it is what places the root of the sweep in the *open* interval `(0, 1−α)`, where the
quantile pair `(Q s, Q (s+α))` is honest (the junk values `Q 0`, `Q 1` are excluded). The
separation hypothesis is supplied there by a level `a = F c` of the null law: below it the
quantile function stays at or under `c`, above it strictly beyond, so the likelihood
ratio — strictly increasing — separates. -/
private lemma integral_lt_of_monotoneOn_of_sep {g : ℝ → ℝ} {α a : ℝ}
    (hg : MonotoneOn g (Set.Ioo (0 : ℝ) 1))
    (hint : IntegrableOn g (Set.Icc (0 : ℝ) 1) MeasureTheory.volume)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hsep : ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ v ∈ Set.Ioo (0 : ℝ) 1, u ≤ a → a < v → g u < g v) :
    (∫ u in (0 : ℝ)..α, g u) < α * ∫ u in (0 : ℝ)..1, g u := by
  obtain ⟨hα0, hα1⟩ := hα
  obtain ⟨ha0, ha1⟩ := ha
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hmemα : α ∈ Set.Icc (0 : ℝ) 1 := ⟨hα0.le, hα1.le⟩
  have hmema : a ∈ Set.Icc (0 : ℝ) 1 := ⟨ha0.le, ha1.le⟩
  -- upper and lower bounds for the integral of `g` over a subinterval
  have hub : ∀ x y c : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x ≤ y →
      (∀ u ∈ Set.Ioo x y, g u ≤ c) → (∫ u in x..y, g u) ≤ (y - x) * c := by
    intro x y c hx hy hxy hle
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hxy
      (intervalIntegrable_of_Icc01 hint hx hy) intervalIntegrable_const hle
    simpa using h
  have hlb : ∀ x y c : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x ≤ y →
      (∀ u ∈ Set.Ioo x y, c ≤ g u) → (y - x) * c ≤ ∫ u in x..y, g u := by
    intro x y c hx hy hxy hle
    have h := intervalIntegral.integral_mono_on_of_le_Ioo hxy intervalIntegrable_const
      (intervalIntegrable_of_Icc01 hint hx hy) hle
    simpa using h
  have hsplitα : (∫ u in (0 : ℝ)..α, g u) + ∫ u in α..(1 : ℝ), g u = ∫ u in (0 : ℝ)..1, g u :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_Icc01 hint hmem0 hmemα)
      (intervalIntegrable_of_Icc01 hint hmemα hmem1)
  -- it suffices to prove the cleared form `(1 − α)·∫₀^α g < α·∫_α^1 g`
  suffices hkey : (1 - α) * (∫ u in (0 : ℝ)..α, g u) < α * ∫ u in α..(1 : ℝ), g u by
    nlinarith [hkey, hsplitα]
  rcases le_or_gt α a with hcase | hcase
  · -- the level `α` sits at or below the separation level: the *right* piece is too big
    set a' : ℝ := (a + 1) / 2 with ha'def
    have ha'0 : 0 < a' := by rw [ha'def]; linarith
    have ha'1 : a' < 1 := by rw [ha'def]; linarith
    have haa' : a < a' := by rw [ha'def]; linarith
    have hmema' : a' ∈ Set.Icc (0 : ℝ) 1 := ⟨ha'0.le, ha'1.le⟩
    have hgap : g α < g a' := hsep α ⟨hα0, hα1⟩ a' ⟨ha'0, ha'1⟩ hcase haa'
    have h1 : (∫ u in (0 : ℝ)..α, g u) ≤ α * g α := by
      have h := hub 0 α (g α) hmem0 hmemα hα0.le
        (fun u hu => hg ⟨hu.1, hu.2.trans hα1⟩ ⟨hα0, hα1⟩ hu.2.le)
      simpa using h
    have h3 : (a' - α) * g α ≤ ∫ u in α..a', g u :=
      hlb α a' (g α) hmemα hmema' (by linarith)
        (fun u hu => hg ⟨hα0, hα1⟩ ⟨hα0.trans hu.1, hu.2.trans ha'1⟩ hu.1.le)
    have h4 : (1 - a') * g a' ≤ ∫ u in a'..(1 : ℝ), g u :=
      hlb a' 1 (g a') hmema' hmem1 ha'1.le
        (fun u hu => hg ⟨ha'0, ha'1⟩ ⟨ha'0.trans hu.1, hu.2⟩ hu.1.le)
    have h5 : (∫ u in α..a', g u) + ∫ u in a'..(1 : ℝ), g u = ∫ u in α..(1 : ℝ), g u :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_Icc01 hint hmemα hmema')
        (intervalIntegrable_of_Icc01 hint hmema' hmem1)
    have hpos : 0 < (1 - a') * (g a' - g α) := mul_pos (by linarith) (by linarith)
    have hR : (1 - α) * g α < ∫ u in α..(1 : ℝ), g u := by linarith [h3, h4, h5, hpos]
    have hfin : (1 - α) * (∫ u in (0 : ℝ)..α, g u) ≤ (1 - α) * (α * g α) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have hmul : α * ((1 - α) * g α) < α * ∫ u in α..(1 : ℝ), g u :=
      mul_lt_mul_of_pos_left hR hα0
    linarith [hfin, hmul]
  · -- the level `α` sits strictly above it: the *left* piece is too small
    have hgap : g a < g α := hsep a ⟨ha0, ha1⟩ α ⟨hα0, hα1⟩ le_rfl hcase
    have h1 : (∫ u in (0 : ℝ)..a, g u) ≤ a * g a := by
      have h := hub 0 a (g a) hmem0 hmema ha0.le
        (fun u hu => hg ⟨hu.1, hu.2.trans ha1⟩ ⟨ha0, ha1⟩ hu.2.le)
      simpa using h
    have h2 : (∫ u in a..α, g u) ≤ (α - a) * g α :=
      hub a α (g α) hmema hmemα hcase.le
        (fun u hu => hg ⟨ha0.trans hu.1, hu.2.trans hα1⟩ ⟨hα0, hα1⟩ hu.2.le)
    have h3 : (∫ u in (0 : ℝ)..a, g u) + ∫ u in a..α, g u = ∫ u in (0 : ℝ)..α, g u :=
      intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_of_Icc01 hint hmem0 hmema)
        (intervalIntegrable_of_Icc01 hint hmema hmemα)
    have h4 : (1 - α) * g α ≤ ∫ u in α..(1 : ℝ), g u :=
      hlb α 1 (g α) hmemα hmem1 hα1.le
        (fun u hu => hg ⟨hα0, hα1⟩ ⟨hα0.trans hu.1, hu.2⟩ hu.1.le)
    have hpos : 0 < a * (g α - g a) := mul_pos ha0 (by linarith)
    have hAlt : (∫ u in (0 : ℝ)..α, g u) < α * g α := by linarith [h1, h2, h3, hpos]
    have hmul : (1 - α) * (∫ u in (0 : ℝ)..α, g u) < (1 - α) * (α * g α) :=
      mul_lt_mul_of_pos_left hAlt (by linarith : (0 : ℝ) < 1 - α)
    have hmul2 : α * ((1 - α) * g α) ≤ α * ∫ u in α..(1 : ℝ), g u :=
      mul_le_mul_of_nonneg_left h4 hα0.le
    linarith [hmul, hmul2]

/-- The mass of an atom is the jump of the distribution function there. -/
private lemma cdf_singleton_toReal (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    (ν {x}).toReal = cdf ν x - Function.leftLim (⇑(cdf ν)) x := by
  have h : (ν {x}).toReal = ((cdf ν).measure {x}).toReal := by rw [measure_cdf]
  rw [h, (cdf ν).measure_singleton x,
    ENNReal.toReal_ofReal (by simpa using (monotone_cdf (μ := ν)).leftLim_le (le_refl x))]

/-- The inverse-transform identity in the exact form the sweep uses it. -/
private lemma map_quantile_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)).map (quantile (⇑(cdf ν))) = ν :=
  map_quantile_uniform ν _ (fun y => by rw [cdf_eq_real]; rfl)

/-- The quantile function is a.e. measurable on the unit interval, being monotone there. -/
private lemma aemeasurable_quantile_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    AEMeasurable (quantile (⇑(cdf ν)))
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hmonoOn : MonotoneOn (quantile (⇑(cdf ν))) (Set.Ioo 0 1) := by
    intro a ha b hb hab
    exact quantile_mono _ hab (cdf_level_nonempty_bddBelow ν ha.1 ha.2).2
      (cdf_level_nonempty_bddBelow ν hb.1 hb.2).1
  have hIccIoo : Set.Icc (0 : ℝ) 1 =ᵐ[MeasureTheory.volume] Set.Ioo 0 1 := Ioo_ae_eq_Icc.symm
  rw [Measure.restrict_congr_set hIccIoo]
  exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hmonoOn

/-- **Brick (b): the sliding window, weighed by a density, is a level-space integral.**

With the canonical boundary weights of brick (a) — `γ₁·ν{C₁} = F(C₁) − s` and
`γ₂·ν{C₂} = s + α − F(C₂⁻)`, where `C₁ = Q(s)` and `C₂ = Q(s+α)` — the integral of the
two-sided test against any measurable weight `r` is the Lebesgue integral of `r ∘ Q` over the
*level* window `(s, s+α)`:
`∫ φ_s·r dν = ∫_s^{s+α} r(Q u) du`.

Applied with `r = dν₂/dν₁` this says the size of the window test at `θ₂` is the sliding
integral `h(s)` of the roadmap; it is the identity that turns the two-dimensional
root-finding problem of `isUMP_twoSided` into a one-dimensional sweep.

The proof splits the level window at the two atom boundaries `F(C₁) ≤ F(C₂⁻)`. On the two
outer pieces `Q` is *constant* (`quantile_eq_of_leftLim_lt`), which produces the two boundary
terms; the inner piece is evaluated by the half-line change of variables
`setIntegral_Iic_eq_intervalIntegral_quantile` at `C₁` and at `C₂`, minus the atom at `C₂`
(which the level window `(F(C₂⁻), F(C₂)]` carries and the open interval `(C₁,C₂)` does
not). -/
private lemma twoSidedVal_integral_weight_eq (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {r : ℝ → ℝ} (hr : Measurable r) (hrint : Integrable r ν)
    {α s γ₁ γ₂ : ℝ} (hα0 : 0 < α) (hs0 : 0 < s) (hs1 : s + α < 1)
    (hlt : quantile (⇑(cdf ν)) s < quantile (⇑(cdf ν)) (s + α))
    (hkey₁ : γ₁ * (ν {quantile (⇑(cdf ν)) s}).toReal
      = cdf ν (quantile (⇑(cdf ν)) s) - s)
    (hkey₂ : γ₂ * (ν {quantile (⇑(cdf ν)) (s + α)}).toReal
      = s + α - Function.leftLim (⇑(cdf ν)) (quantile (⇑(cdf ν)) (s + α))) :
    ∫ t, twoSidedVal (quantile (⇑(cdf ν)) s) (quantile (⇑(cdf ν)) (s + α)) γ₁ γ₂ t * r t ∂ν
      = ∫ u in s..(s + α), r (quantile (⇑(cdf ν)) u) := by
  classical
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  obtain ⟨hA₁, hLL₁⟩ := cdf_quantile_bounds ν hs0 (show s < 1 by linarith)
  obtain ⟨hA₂, hLL₂⟩ := cdf_quantile_bounds ν (show (0 : ℝ) < s + α by linarith) hs1
  set C₁ : ℝ := quantile (⇑(cdf ν)) s with hC₁def
  set C₂ : ℝ := quantile (⇑(cdf ν)) (s + α) with hC₂def
  -- the level geometry: `0 < s ≤ F C₁ ≤ F(C₂⁻) ≤ s + α ≤ F C₂ ≤ 1`
  have hFle : cdf ν C₁ ≤ Function.leftLim (⇑(cdf ν)) C₂ := hmono.le_leftLim hlt
  have hF₂le : cdf ν C₂ ≤ 1 := cdf_le_one ν C₂
  have hL₂nn : (0 : ℝ) ≤ Function.leftLim (⇑(cdf ν)) C₂ :=
    le_trans (cdf_nonneg ν (C₂ - 1)) (hmono.le_leftLim (by linarith))
  have hm₂ : (ν {C₂}).toReal = cdf ν C₂ - Function.leftLim (⇑(cdf ν)) C₂ :=
    cdf_singleton_toReal ν C₂
  set L₂ : ℝ := Function.leftLim (⇑(cdf ν)) C₂ with hL₂def
  set Q : ℝ → ℝ := quantile (⇑(cdf ν)) with hQdef
  set G : ℝ → ℝ := fun u => r (Q u) with hGdef
  -- integrability of `r ∘ Q` on the unit interval
  have hmap := map_quantile_cdf ν
  have haem := aemeasurable_quantile_cdf ν
  rw [← hQdef] at hmap haem
  have hGint : IntegrableOn G (Set.Icc (0 : ℝ) 1) MeasureTheory.volume := by
    have hasm : AEStronglyMeasurable r
        ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)).map Q) := by
      rw [hmap]; exact hr.aestronglyMeasurable
    have h := (MeasureTheory.integrable_map_measure hasm haem).mp (by rwa [hmap])
    exact h
  have hII : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      IntervalIntegrable G MeasureTheory.volume a b := by
    intro a b ha hb
    refine intervalIntegrable_iff.2 (hGint.mono_set fun u hu => ?_)
    rcases Set.mem_uIoc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨le_trans ha.1 h1.le, le_trans h2 hb.2⟩
    · exact ⟨le_trans hb.1 h1.le, le_trans h2 ha.2⟩
  have hmemF₁ : cdf ν C₁ ∈ Set.Icc (0 : ℝ) 1 := ⟨cdf_nonneg ν C₁, cdf_le_one ν C₁⟩
  have hmemF₂ : cdf ν C₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨cdf_nonneg ν C₂, hF₂le⟩
  have hmemL₂ : L₂ ∈ Set.Icc (0 : ℝ) 1 := ⟨hL₂nn, le_trans hLL₂ (by linarith)⟩
  have hmems : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0.le, by linarith⟩
  have hmemsα : s + α ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  -- almost every level is not the right endpoint of the unit interval
  have h1ae : ∀ᵐ u ∂(MeasureTheory.volume : Measure ℝ), u ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  -- the three constant pieces: `Q` collapses each atom level window to its atom
  have hP1 : ∫ u in s..(cdf ν C₁), G u = (cdf ν C₁ - s) * r C₁ := by
    have hcongr : ∫ u in s..(cdf ν C₁), G u = ∫ _u in s..(cdf ν C₁), r C₁ := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with u hu
      rw [Set.uIoc_of_le hA₁] at hu
      have : Q u = C₁ := quantile_eq_of_leftLim_lt ν (by linarith [hu.1])
        (by linarith [hu.2, hFle, hLL₂]) (by linarith [hu.1]) hu.2
      simp only [hGdef]
      rw [this]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  have hP2 : ∫ u in L₂..(s + α), G u = (s + α - L₂) * r C₂ := by
    have hcongr : ∫ u in L₂..(s + α), G u = ∫ _u in L₂..(s + α), r C₂ := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards with u hu
      rw [Set.uIoc_of_le hLL₂] at hu
      have : Q u = C₂ := quantile_eq_of_leftLim_lt ν (by linarith [hu.1])
        (by linarith [hu.2]) hu.1 (le_trans hu.2 hA₂)
      simp only [hGdef]
      rw [this]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  have hP4 : ∫ u in L₂..(cdf ν C₂), G u = (cdf ν C₂ - L₂) * r C₂ := by
    have hle : L₂ ≤ cdf ν C₂ := by linarith [hLL₂, hA₂]
    have hcongr : ∫ u in L₂..(cdf ν C₂), G u = ∫ _u in L₂..(cdf ν C₂), r C₂ := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [h1ae] with u hu1 hu
      rw [Set.uIoc_of_le hle] at hu
      have : Q u = C₂ := quantile_eq_of_leftLim_lt ν (by linarith [hu.1])
        (lt_of_le_of_ne (le_trans hu.2 hF₂le) hu1) hu.1 hu.2
      simp only [hGdef]
      rw [this]
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
  -- the inner piece, by the half-line change of variables at `C₁` and at `C₂`
  have hM₁ : ∫ t in Set.Iic C₁, r t ∂ν = ∫ u in (0 : ℝ)..(cdf ν C₁), G u :=
    setIntegral_Iic_eq_intervalIntegral_quantile ν hr C₁
  have hM₂ : ∫ t in Set.Iic C₂, r t ∂ν = ∫ u in (0 : ℝ)..(cdf ν C₂), G u :=
    setIntegral_Iic_eq_intervalIntegral_quantile ν hr C₂
  have hsplit0 : (∫ u in (0 : ℝ)..(cdf ν C₁), G u) + ∫ u in (cdf ν C₁)..(cdf ν C₂), G u
      = ∫ u in (0 : ℝ)..(cdf ν C₂), G u :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _ hmem0 hmemF₁)
      (hII _ _ hmemF₁ hmemF₂)
  have hsplit1 : (∫ u in s..(cdf ν C₁), G u) + ∫ u in (cdf ν C₁)..(s + α), G u
      = ∫ u in s..(s + α), G u :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _ hmems hmemF₁)
      (hII _ _ hmemF₁ hmemsα)
  have hsplit2 : (∫ u in (cdf ν C₁)..L₂, G u) + ∫ u in L₂..(s + α), G u
      = ∫ u in (cdf ν C₁)..(s + α), G u :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _ hmemF₁ hmemL₂)
      (hII _ _ hmemL₂ hmemsα)
  have hsplit3 : (∫ u in (cdf ν C₁)..L₂, G u) + ∫ u in L₂..(cdf ν C₂), G u
      = ∫ u in (cdf ν C₁)..(cdf ν C₂), G u :=
    intervalIntegral.integral_add_adjacent_intervals (hII _ _ hmemF₁ hmemL₂)
      (hII _ _ hmemL₂ hmemF₂)
  -- the left-hand side, as three indicator integrals
  have hne : C₁ ≠ C₂ := ne_of_lt hlt
  have hfun : (fun t => twoSidedVal C₁ C₂ γ₁ γ₂ t * r t)
      = fun t => γ₁ * Set.indicator {C₁} r t + γ₂ * Set.indicator {C₂} r t
        + Set.indicator (Set.Ioo C₁ C₂) r t := by
    funext t
    simp only [twoSidedVal, Set.indicator_apply, Set.mem_singleton_iff, Set.mem_Ioo]
    by_cases h1 : t = C₁
    · subst h1; simp [hne]
    · by_cases h2 : t = C₂
      · subst h2; simp [h1]
      · by_cases h3 : C₁ < t
        · by_cases h4 : t < C₂ <;> simp [h1, h2, h3, h4]
        · simp [h1, h2, h3]
  have hi₁ : Integrable (fun t : ℝ => Set.indicator {C₁} r t) ν :=
    hrint.indicator (measurableSet_singleton C₁)
  have hi₂ : Integrable (fun t : ℝ => Set.indicator {C₂} r t) ν :=
    hrint.indicator (measurableSet_singleton C₂)
  have hi₃ : Integrable (fun t : ℝ => Set.indicator (Set.Ioo C₁ C₂) r t) ν :=
    hrint.indicator measurableSet_Ioo
  have hLHS : ∫ t, twoSidedVal C₁ C₂ γ₁ γ₂ t * r t ∂ν
      = γ₁ * ((ν {C₁}).toReal * r C₁) + γ₂ * ((ν {C₂}).toReal * r C₂)
        + ∫ t in Set.Ioo C₁ C₂, r t ∂ν := by
    have hA : Integrable (fun t : ℝ => γ₁ * Set.indicator {C₁} r t
        + γ₂ * Set.indicator {C₂} r t) ν := (hi₁.const_mul γ₁).add (hi₂.const_mul γ₂)
    rw [hfun, integral_add hA hi₃,
      integral_add (hi₁.const_mul γ₁) (hi₂.const_mul γ₂), integral_const_mul, integral_const_mul,
      integral_indicator (measurableSet_singleton C₁),
      integral_indicator (measurableSet_singleton C₂), integral_indicator measurableSet_Ioo,
      integral_singleton, integral_singleton]
    simp [measureReal_def]
  -- the `(C₁, C₂)`-mass, as the difference of two half-lines minus the atom at `C₂`
  have hIoc : Set.Ioc C₁ C₂ = Set.Ioo C₁ C₂ ∪ {C₂} := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases eq_or_lt_of_le h2 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨h1, h⟩
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h1, h2.le⟩
      · exact ⟨h ▸ hlt, h.le⟩
  have hIic : ∫ t in Set.Iic C₂, r t ∂ν
      = (∫ t in Set.Iic C₁, r t ∂ν) + ∫ t in Set.Ioo C₁ C₂, r t ∂ν
        + (ν {C₂}).toReal * r C₂ := by
    have h1 : Set.Iic C₁ ∪ Set.Ioc C₁ C₂ = Set.Iic C₂ := Set.Iic_union_Ioc_eq_Iic hlt.le
    have hdisj1 : Disjoint (Set.Iic C₁) (Set.Ioc C₁ C₂) := by
      rw [Set.disjoint_left]
      rintro t ht ⟨h1, -⟩
      exact absurd ht (not_le.2 h1)
    have hdisj2 : Disjoint (Set.Ioo C₁ C₂) ({C₂} : Set ℝ) := by
      rw [Set.disjoint_left]
      rintro t ⟨-, h2⟩ ht'
      rw [Set.mem_singleton_iff] at ht'
      exact absurd h2 (by rw [ht']; exact lt_irrefl C₂)
    rw [← h1, MeasureTheory.setIntegral_union hdisj1 measurableSet_Ioc
        (hrint.integrableOn) (hrint.integrableOn), hIoc,
      MeasureTheory.setIntegral_union hdisj2 (measurableSet_singleton C₂)
        (hrint.integrableOn) (hrint.integrableOn), integral_singleton]
    simp [measureReal_def]
    ring
  rw [hLHS]
  have hgoal : (cdf ν C₁ - s) * r C₁ + (s + α - L₂) * r C₂
      + ((∫ t in Set.Iic C₂, r t ∂ν) - (∫ t in Set.Iic C₁, r t ∂ν)
        - (ν {C₂}).toReal * r C₂) = ∫ u in s..(s + α), G u := by
    rw [hM₁, hM₂, hm₂]
    linarith [hP1, hP2, hP4, hsplit0, hsplit1, hsplit2, hsplit3]
  rw [← hgoal]
  have e₁ : γ₁ * ((ν {C₁}).toReal * r C₁) = (cdf ν C₁ - s) * r C₁ := by
    rw [← hkey₁]; ring
  have e₂ : γ₂ * ((ν {C₂}).toReal * r C₂) = (s + α - L₂) * r C₂ := by
    rw [← hkey₂]; ring
  rw [e₁, e₂]
  linarith [hIic]

/-- **A law with no big atom is not a point mass.** If every atom of `ν` carries mass below
`α < 1`, then the distribution function takes some value strictly inside `(0,1)`. This is the
nondegeneracy that feeds the separation hypothesis of `integral_lt_of_monotoneOn_of_sep`. -/
private lemma exists_cdf_mem_Ioo (ν : Measure ℝ) [IsProbabilityMeasure ν] {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hatom : ∀ t : ℝ, (ν {t}).toReal < α) :
    ∃ c : ℝ, cdf ν c ∈ Set.Ioo (0 : ℝ) 1 := by
  by_contra hcon
  push_neg at hcon
  have hdich : ∀ c : ℝ, cdf ν c = 0 ∨ cdf ν c = 1 := by
    intro c
    have h := hcon c
    simp only [Set.mem_Ioo, not_and, not_lt] at h
    rcases le_or_gt (cdf ν c) 0 with h0 | h0
    · exact Or.inl (le_antisymm h0 (cdf_nonneg ν c))
    · exact Or.inr (le_antisymm (cdf_le_one ν c) (h h0))
  have hp0 : (0 : ℝ) < (1 - α) / 2 := by linarith
  have hp1 : (1 - α) / 2 < 1 := by linarith
  obtain ⟨hA, hL⟩ := cdf_quantile_bounds ν hp0 hp1
  have hF1 : cdf ν (quantile (⇑(cdf ν)) ((1 - α) / 2)) = 1 := by
    rcases hdich (quantile (⇑(cdf ν)) ((1 - α) / 2)) with h | h
    · rw [h] at hA; linarith
    · exact h
  have hmass := cdf_singleton_toReal ν (quantile (⇑(cdf ν)) ((1 - α) / 2))
  have hlt := hatom (quantile (⇑(cdf ν)) ((1 - α) / 2))
  rw [hmass, hF1] at hlt
  linarith

/-- **The sweep.** For a strictly increasing weight `r` of total `ν`-mass `1` and a level
`α ∈ (0,1)` below every atom of `ν`, there is a starting level `s ∈ (0, 1−α)` at which the
`r`-weighted mass of the level window `(s, s+α)` is exactly `α`.

Combined with brick (a) (the window has `ν`-mass exactly `α` for *every* `s`) and brick (b)
(its `r`-weighted mass is the level-space integral swept here), this is the two-equation
existence step of `isUMP_twoSided`: the second size condition is met at the root, the first
holds identically.

The three ingredients are: the sliding integral is continuous (it is a difference of two
primitives of an integrable function); its endpoint values straddle `α` *strictly*, by the
strict rearrangement inequality `integral_lt_of_monotoneOn_of_sep` — strictness is what keeps
the root away from the junk levels `0` and `1`; and the intermediate value theorem. -/
private lemma exists_window_root (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {r : ℝ → ℝ} (hr : Measurable r) (hrint : Integrable r ν) (hrsm : StrictMono r)
    (hrone : ∫ t, r t ∂ν = 1) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hatom : ∀ t : ℝ, (ν {t}).toReal < α) :
    ∃ s : ℝ, 0 < s ∧ s + α < 1 ∧
      (∫ u in s..(s + α), r (quantile (⇑(cdf ν)) u)) = α := by
  classical
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  have hrc : ∀ y : ℝ, ContinuousWithinAt (⇑(cdf ν)) (Set.Ici y) y :=
    fun y => (cdf ν).right_continuous y
  set Q : ℝ → ℝ := quantile (⇑(cdf ν)) with hQdef
  set G : ℝ → ℝ := fun u => r (Q u) with hGdef
  have hmap := map_quantile_cdf ν
  have haem := aemeasurable_quantile_cdf ν
  rw [← hQdef] at hmap haem
  have hasm : AEStronglyMeasurable r
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)).map Q) := by
    rw [hmap]; exact hr.aestronglyMeasurable
  have hGint : IntegrableOn G (Set.Icc (0 : ℝ) 1) MeasureTheory.volume :=
    (MeasureTheory.integrable_map_measure hasm haem).mp (by rwa [hmap])
  have hQmono : MonotoneOn Q (Set.Ioo (0 : ℝ) 1) := fun x hx y hy hxy =>
    quantile_mono _ hxy (cdf_level_nonempty_bddBelow ν hx.1 hx.2).2
      (cdf_level_nonempty_bddBelow ν hy.1 hy.2).1
  have hGmono : MonotoneOn G (Set.Ioo (0 : ℝ) 1) := fun x hx y hy hxy =>
    hrsm.monotone (hQmono hx hy hxy)
  have hGtot : (∫ u in (0 : ℝ)..1, G u) = 1 := by
    have h1 : ∫ t, r t ∂ν
        = ∫ u, G u ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)) := by
      conv_lhs => rw [← hmap]
      exact integral_map haem hasm
    rw [intervalIntegral.integral_of_le zero_le_one,
      ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← h1, hrone]
  -- the separation level of the sweep
  obtain ⟨c, hc⟩ := exists_cdf_mem_Ioo ν hα0 hα1 hatom
  have hsep : ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∀ v ∈ Set.Ioo (0 : ℝ) 1,
      u ≤ cdf ν c → cdf ν c < v → G u < G v := by
    intro u hu v hv hule hvlt
    have h1 : Q u ≤ c := (quantile_le_iff hmono hrc
      (cdf_level_nonempty_bddBelow ν hu.1 hu.2).1
      (cdf_level_nonempty_bddBelow ν hu.1 hu.2).2).mpr hule
    have h2 : ¬ (Q v ≤ c) := by
      intro h
      exact absurd ((quantile_le_iff hmono hrc (cdf_level_nonempty_bddBelow ν hv.1 hv.2).1
        (cdf_level_nonempty_bddBelow ν hv.1 hv.2).2).mp h) (not_le.2 hvlt)
    exact hrsm (lt_of_le_of_lt h1 (not_le.mp h2))
  -- the two strict endpoint bounds
  have hlow : (∫ u in (0 : ℝ)..α, G u) < α := by
    have h := integral_lt_of_monotoneOn_of_sep (α := α) hGmono hGint ⟨hα0, hα1⟩ hc hsep
    rw [hGtot] at h; linarith
  have hsplit : (∫ u in (0 : ℝ)..(1 - α), G u) + ∫ u in (1 - α)..(1 : ℝ), G u
      = ∫ u in (0 : ℝ)..1, G u :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_Icc01 hGint ⟨le_rfl, zero_le_one⟩ ⟨by linarith, by linarith⟩)
      (intervalIntegrable_of_Icc01 hGint ⟨by linarith, by linarith⟩ ⟨zero_le_one, le_rfl⟩)
  have hhigh : α < ∫ u in (1 - α)..(1 : ℝ), G u := by
    have h := integral_lt_of_monotoneOn_of_sep (α := 1 - α) hGmono hGint
      ⟨by linarith, by linarith⟩ hc hsep
    rw [hGtot] at h
    linarith [hsplit]
  -- the sliding integral, extended to the line and continuous there
  set Ĝ : ℝ → ℝ := Set.indicator (Set.Icc (0 : ℝ) 1) G with hĜdef
  have hĜint : Integrable Ĝ MeasureTheory.volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).2 hGint
  set H : ℝ → ℝ := fun s => (∫ u in (0 : ℝ)..(s + α), Ĝ u) - ∫ u in (0 : ℝ)..s, Ĝ u with hHdef
  have hcont : Continuous H := by
    have h1 : Continuous fun s : ℝ => ∫ u in (0 : ℝ)..(s + α), Ĝ u :=
      (hĜint.continuous_primitive 0).comp (continuous_id.add continuous_const)
    exact h1.sub (hĜint.continuous_primitive 0)
  have hval : ∀ s : ℝ, 0 ≤ s → s + α ≤ 1 → H s = ∫ u in s..(s + α), G u := by
    intro s hs0 hs1
    have hadd : (∫ u in (0 : ℝ)..s, Ĝ u) + ∫ u in s..(s + α), Ĝ u
        = ∫ u in (0 : ℝ)..(s + α), Ĝ u :=
      intervalIntegral.integral_add_adjacent_intervals
        hĜint.intervalIntegrable hĜint.intervalIntegrable
    have heq : (∫ u in s..(s + α), Ĝ u) = ∫ u in s..(s + α), G u := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [Set.uIcc_of_le (by linarith : s ≤ s + α)] at hu
      simp only [hĜdef]
      exact Set.indicator_of_mem
        (show u ∈ Set.Icc (0 : ℝ) 1 from ⟨le_trans hs0 hu.1, le_trans hu.2 hs1⟩) G
    simp only [hHdef]
    linarith [hadd, heq]
  have hH0 : H 0 = ∫ u in (0 : ℝ)..α, G u := by
    have h := hval 0 le_rfl (by linarith)
    rwa [zero_add] at h
  have hH1 : H (1 - α) = ∫ u in (1 - α)..(1 : ℝ), G u := by
    have h := hval (1 - α) (by linarith) (by linarith)
    rwa [sub_add_cancel] at h
  -- the intermediate value theorem, at a value strictly between the two endpoints
  obtain ⟨s, hs, hsval⟩ :=
    intermediate_value_Icc (by linarith : (0 : ℝ) ≤ 1 - α) hcont.continuousOn
      (show α ∈ Set.Icc (H 0) (H (1 - α)) from ⟨by rw [hH0]; linarith, by rw [hH1]; linarith⟩)
  have hs0 : 0 < s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · exact absurd (h ▸ hsval) (by rw [hH0]; linarith)
    · exact h
  have hs1 : s + α < 1 := by
    rcases eq_or_lt_of_le hs.2 with h | h
    · exact absurd (h ▸ hsval) (by rw [hH1]; linarith)
    · linarith
  exact ⟨s, hs0, hs1, by rw [← hval s hs.1 (by linarith), hsval]⟩

/-- **Brick (a): the randomized window attached to a quantile pair.**

For a law `ν` on the line, a level `α` and a starting level `s`, the two-sided test whose
boundaries are the `s`- and `(s+α)`-quantiles of `ν` has size exactly `α`, the boundary
weights being the fractions of the two boundary atoms that the level window `(s, s+α)` cuts
off. -/
private lemma exists_twoSided_constants_window (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {α s : ℝ} (hα0 : 0 < α) (hs0 : 0 < s) (hs1 : s + α < 1)
    (hlt : quantile (⇑(cdf ν)) s < quantile (⇑(cdf ν)) (s + α)) :
    ∃ γ₁ γ₂ : ℝ, γ₁ ∈ Set.Icc (0 : ℝ) 1 ∧ γ₂ ∈ Set.Icc (0 : ℝ) 1 ∧
      γ₁ * (ν {quantile (⇑(cdf ν)) s}).toReal
        = cdf ν (quantile (⇑(cdf ν)) s) - s ∧
      γ₂ * (ν {quantile (⇑(cdf ν)) (s + α)}).toReal
        = s + α - Function.leftLim (⇑(cdf ν)) (quantile (⇑(cdf ν)) (s + α)) ∧
      ∫ t, twoSidedVal (quantile (⇑(cdf ν)) s) (quantile (⇑(cdf ν)) (s + α)) γ₁ γ₂ t ∂ν = α := by
  classical
  have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
  set F : ℝ → ℝ := ⇑(cdf ν) with hF
  set C₁ : ℝ := quantile F s with hC₁
  set C₂ : ℝ := quantile F (s + α) with hC₂
  obtain ⟨hA₁, hL₁⟩ := cdf_quantile_bounds ν hs0 (by linarith)
  obtain ⟨hA₂, hL₂⟩ := cdf_quantile_bounds ν (by linarith) hs1
  set L₁ : ℝ := Function.leftLim F C₁ with hL₁def
  set L₂ : ℝ := Function.leftLim F C₂ with hL₂def
  -- the three masses
  have hm₁ : (ν {C₁}).toReal = F C₁ - L₁ := by
    rw [← measure_cdf (μ := ν), (cdf ν).measure_singleton C₁,
      ENNReal.toReal_ofReal (by simpa [hL₁def] using hmono.leftLim_le (le_refl C₁))]
  have hm₂ : (ν {C₂}).toReal = F C₂ - L₂ := by
    rw [← measure_cdf (μ := ν), (cdf ν).measure_singleton C₂,
      ENNReal.toReal_ofReal (by simpa [hL₂def] using hmono.leftLim_le (le_refl C₂))]
  have hFle : F C₁ ≤ L₂ := hmono.le_leftLim hlt
  have hmo : (ν (Set.Ioo C₁ C₂)).toReal = L₂ - F C₁ := by
    rw [← measure_cdf (μ := ν), (cdf ν).measure_Ioo,
      ENNReal.toReal_ofReal (by simpa [hL₂def] using sub_nonneg.2 hFle)]
  -- the boundary weights
  set γ₁ : ℝ := if (ν {C₁}).toReal = 0 then 0 else (F C₁ - s) / (ν {C₁}).toReal with hγ₁
  set γ₂ : ℝ := if (ν {C₂}).toReal = 0 then 0 else (s + α - L₂) / (ν {C₂}).toReal with hγ₂
  have hkey₁ : γ₁ * (ν {C₁}).toReal = F C₁ - s := by
    rw [hγ₁]
    by_cases h : (ν {C₁}).toReal = 0
    · rw [if_pos h, zero_mul]
      rw [hm₁] at h
      have : L₁ = F C₁ := by linarith
      linarith [hL₁, hA₁, this]
    · rw [if_neg h, div_mul_cancel₀ _ h]
  have hkey₂ : γ₂ * (ν {C₂}).toReal = s + α - L₂ := by
    rw [hγ₂]
    by_cases h : (ν {C₂}).toReal = 0
    · rw [if_pos h, zero_mul]
      rw [hm₂] at h
      have : L₂ = F C₂ := by linarith
      linarith [hL₂, hA₂, this]
    · rw [if_neg h, div_mul_cancel₀ _ h]
  have hγ₁mem : γ₁ ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hγ₁]
    by_cases h : (ν {C₁}).toReal = 0
    · rw [if_pos h]; exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < (ν {C₁}).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)
      rw [if_neg h]
      refine ⟨div_nonneg (by linarith) hpos.le, ?_⟩
      rw [div_le_one hpos, hm₁]
      linarith
  have hγ₂mem : γ₂ ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hγ₂]
    by_cases h : (ν {C₂}).toReal = 0
    · rw [if_pos h]; exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < (ν {C₂}).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm h)
      rw [if_neg h]
      refine ⟨div_nonneg (by linarith) hpos.le, ?_⟩
      rw [div_le_one hpos, hm₂]
      linarith
  refine ⟨γ₁, γ₂, hγ₁mem, hγ₂mem, hkey₁, hkey₂, ?_⟩
  -- the test is a sum of three indicators
  have hne : C₁ ≠ C₂ := ne_of_lt hlt
  have hfun : (fun t => twoSidedVal C₁ C₂ γ₁ γ₂ t)
      = fun t => γ₁ * Set.indicator {C₁} (1 : ℝ → ℝ) t
        + γ₂ * Set.indicator {C₂} (1 : ℝ → ℝ) t
        + Set.indicator (Set.Ioo C₁ C₂) (1 : ℝ → ℝ) t := by
    funext t
    simp only [twoSidedVal, Set.indicator_apply, Set.mem_singleton_iff, Set.mem_Ioo, Pi.one_apply]
    by_cases h1 : t = C₁
    · subst h1; simp [hne]
    · by_cases h2 : t = C₂
      · subst h2; simp [h1]
      · by_cases h3 : C₁ < t
        · by_cases h4 : t < C₂ <;> simp [h1, h2, h3, h4]
        · simp [h1, h2, h3]
  rw [hfun]
  have hi₁ : Integrable (fun t : ℝ => Set.indicator {C₁} (1 : ℝ → ℝ) t) ν :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_singleton C₁)
  have hi₂ : Integrable (fun t : ℝ => Set.indicator {C₂} (1 : ℝ → ℝ) t) ν :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_singleton C₂)
  have hi₃ : Integrable (fun t : ℝ => Set.indicator (Set.Ioo C₁ C₂) (1 : ℝ → ℝ) t) ν :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioo
  have hA : Integrable (fun t : ℝ => γ₁ * Set.indicator {C₁} (1 : ℝ → ℝ) t
      + γ₂ * Set.indicator {C₂} (1 : ℝ → ℝ) t) ν := (hi₁.const_mul γ₁).add (hi₂.const_mul γ₂)
  rw [integral_add hA hi₃,
    integral_add (hi₁.const_mul γ₁) (hi₂.const_mul γ₂), integral_const_mul, integral_const_mul,
    integral_indicator_one (measurableSet_singleton C₁),
    integral_indicator_one (measurableSet_singleton C₂),
    integral_indicator_one measurableSet_Ioo]
  simp only [measureReal_def]
  rw [hkey₁, hkey₂, hmo]
  ring

end QuantileWindow

open ProbabilityTheory in
/-- **UMP test of a two-sided hypothesis.** In a one-parameter exponential family, with the
parametrization strictly increasing, there are constants `C₁ < C₂` and boundary weights
`γ₁, γ₂ ∈ [0,1]` for which the two-sided test has size exactly `α` at both `θ₁` and `θ₂`
and is uniformly most powerful at level `α` for `H : θ ≤ θ₁ or θ₂ ≤ θ` against
`K : θ₁ < θ < θ₂`.

**Repaired statement (`hatom`).** As printed — i.e. without `hatom` — the theorem is FALSE,
and `hatom` is the minimal *checkable* repair. The conclusion demands an honest rejection
interval, `C₁ < C₂`; an atom of the null law of `T` heavier than `α` can make every honest
interval fail one of the two size equations.

*Counterexample to the printed form.* Let `𝓧 = ℝ`, `T = id`, `ηmap = id`, `θ₁ = -1`,
`θ₂ = 1`, `α = 1/20`, and let the base measure be the symmetric discrete measure
`μ = 0.94·δ₀ + ∑_{n≥1} 0.03·2⁻ⁿ·(δ_{1/n} + δ_{-1/n})`, whose support accumulates at `0` from
both sides and which is finite of bounded support, so `M(θ) = ∫e^{θt}dμ < ∞` for every `θ`
and `hnat` holds. By symmetry `M(-1) = M(1)`, so the likelihood ratio of the two boundary
members is `r(t) = dν₂/dν₁(t) = e^{2t}`, with `r(0) = 1`, and `ν₁{0} = 0.94/M(-1) > α`. Now
let `φ` be any test of the displayed form with `C₁ < C₂` and size `α` at `θ₁`. If
`0 ∈ (C₁,C₂)` then `φ(0) = 1` and the size at `θ₁` is at least `ν₁{0} > α`. If the closed
interval `[C₁,C₂]` misses `0` then `r - 1` has a constant strict sign on the support of `φ`,
so the two sizes differ. In the two remaining configurations `C₁ = 0` and `C₂ = 0` one gets
`size(θ₂) - size(θ₁) = ∫φ·(r-1)dν₁`, an integral of a function of a constant strict sign on
`(0, C₂)` resp. `(C₁, 0)` — sets of positive `ν₁`-measure, because the support accumulates at
`0` from both sides — so again the two sizes differ. Hence no honest interval attains
`α` twice, although the *degenerate* randomized test `α/ν₁{0}·1{T = 0}` does.

*Repair.* Assume every level of the statistic carries null probability strictly below `α`.
This is exactly what the counterexample violates, it is verifiable from the model alone, and
it is what makes the sliding quantile window `(Q s, Q (s+α))` nondegenerate for *every*
starting level `s` — see `exists_twoSided_constants_window` and the sweep
`exists_window_root`. It cannot simply be dropped: the degenerate corner is not reachable by
any one-parameter sweep, and the test that solves the two equations there is not of the form
demanded by the conclusion. (The alternative repair — weakening the conclusion to `C₁ ≤ C₂` —
is not adopted here, since the whole downstream optimality chain, `power_min_twoSided` and
`isUMP_twoSided_of_constants`, is stated for honest intervals.)

*Proof.* The two size equations are solved by a one-dimensional sweep over the *level*
window `(s, s+α)` of the null law `ν₁ = (P θ₁)∘T⁻¹`. Brick (a)
(`exists_twoSided_constants_window`) shows the size at `θ₁` is `α` for every `s`, with the
canonical boundary weights; brick (b) (`twoSidedVal_integral_weight_eq`) identifies the size
at `θ₂` with `∫_s^{s+α} r(Q u) du`, `r` the likelihood ratio; and the sweep
(`exists_window_root`) solves that for `α` by the intermediate value theorem, the strict
rearrangement inequality putting the root strictly inside `(0, 1−α)`. Optimality is then
`isUMP_twoSided_of_constants`. -/
theorem isUMP_twoSided
    -- USER-INPUT: the exponential family, with σ-finite reference measure
    (E : ExpFamily 𝓧 ℝ) [SigmaFinite E.base]
    -- USER-INPUT: the model, a family of probability measures on a real parameter
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the parametrization, strictly increasing (the printed hypothesis on `Q`)
    {ηmap : ℝ → ℝ} (hη : StrictMono ηmap)
    -- USER-INPUT: the model is the canonical family read through `ηmap`
    (hrepr : IsCanonicalRepr P E ηmap)
    -- USER-INPUT: every parameter value lies in the natural parameter set, so no member
    -- degenerates to the junk zero measure
    (hnat : ∀ θ, ηmap θ ∈ E.natSet)
    -- USER-INPUT: the two null boundaries, in order
    {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: nondegenerate level
    {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT (AMENDMENT): no level of the statistic carries null probability `α` or
    -- more. Without it the statement is FALSE — see the counterexample in the docstring:
    -- an atom heavier than `α` can block every honest rejection interval `C₁ < C₂`
    (hatom : ∀ t : ℝ, (P θ₁ {x | E.stat x = t}).toReal < α) :
    ∃ C₁ C₂ γ₁ γ₂ : ℝ, C₁ < C₂ ∧ γ₁ ∈ Set.Icc (0 : ℝ) 1 ∧ γ₂ ∈ Set.Icc (0 : ℝ) 1 ∧
      power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α ∧
      power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α ∧
      IsUMP P {θ : ℝ | θ ≤ θ₁ ∨ θ₂ ≤ θ} (Set.Ioo θ₁ θ₂) α
        (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) := by
  obtain ⟨C₁, C₂, γ₁, γ₂, hC, hγ₁, hγ₂, hs₁, hs₂⟩ :
      ∃ C₁ C₂ γ₁ γ₂ : ℝ, C₁ < C₂ ∧ γ₁ ∈ Set.Icc (0 : ℝ) 1 ∧ γ₂ ∈ Set.Icc (0 : ℝ) 1 ∧
        power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₁ = α ∧
        power P (twoSidedTest E.stat C₁ C₂ γ₁ γ₂) θ₂ = α := by
    classical
    -- the canonical densities and the likelihood ratio of the two boundary members
    set p : ℝ → 𝓧 → ℝ :=
      fun ϑ x => Real.exp (ηmap ϑ * E.stat x - E.logPartition (ηmap ϑ)) with hpdef
    have hp : ∀ ϑ, HasDensity E.base (p ϑ) (P ϑ) := by
      intro ϑ
      refine ⟨((E.stat_meas.const_mul (ηmap ϑ)).sub_const _).exp,
        fun x => (Real.exp_pos _).le, ?_⟩
      rw [hrepr ϑ, E.P_eq_withDensity (hnat ϑ)]
      refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hpdef, ts_real_inner_mul]
    set ν : Measure ℝ := (P θ₁).map E.stat with hνdef
    haveI hνprob : IsProbabilityMeasure ν := by
      rw [hνdef]; exact Measure.isProbabilityMeasure_map E.stat_meas.aemeasurable
    set r : ℝ → ℝ := fun t => Real.exp ((ηmap θ₂ - ηmap θ₁) * t
      - (E.logPartition (ηmap θ₂) - E.logPartition (ηmap θ₁))) with hrdef
    have hηlt : ηmap θ₁ < ηmap θ₂ := hη hθ
    have hrmeas : Measurable r := ((measurable_id.const_mul _).sub_const _).exp
    have hrsm : StrictMono r := by
      intro a b hab
      simp only [hrdef]
      exact Real.exp_lt_exp.2 (by nlinarith)
    have hratio : ∀ x : 𝓧, p θ₂ x = r (E.stat x) * p θ₁ x := by
      intro x
      simp only [hpdef, hrdef, ← Real.exp_add]
      congr 1
      ring
    -- the two powers, read on the law of the statistic
    have hpow₁ : ∀ ψ : ℝ → ℝ, Measurable ψ →
        power P (fun x => ψ (E.stat x)) θ₁ = ∫ t, ψ t ∂ν := by
      intro ψ hψ
      unfold power
      rw [hνdef, integral_map E.stat_meas.aemeasurable hψ.aestronglyMeasurable]
    have hpow₂ : ∀ ψ : ℝ → ℝ, Measurable ψ →
        power P (fun x => ψ (E.stat x)) θ₂ = ∫ t, ψ t * r t ∂ν := by
      intro ψ hψ
      unfold power
      rw [ts_integral_density_eq (hp θ₂)]
      have hcongr : ∫ x, ψ (E.stat x) * p θ₂ x ∂E.base
          = ∫ x, (fun y => ψ y * r y) (E.stat x) * p θ₁ x ∂E.base :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          simp only [hratio x]; ring)
      rw [hcongr, ← ts_integral_density_eq (hp θ₁), hνdef,
        integral_map E.stat_meas.aemeasurable (hψ.fun_mul hrmeas).aestronglyMeasurable]
    -- the ratio is a probability density on the law of the statistic
    have hrone : ∫ t, r t ∂ν = 1 := by
      have h := hpow₂ (fun _ => 1) measurable_const
      unfold power at h
      simp only [one_mul] at h
      rw [← h]
      simp
    have hrint : Integrable r ν := by
      have hbase : Integrable (fun x => r (E.stat x) * p θ₁ x) E.base :=
        (ts_density_integrable (hp θ₂)).congr
          (Filter.Eventually.of_forall fun x => hratio x)
      have h₁ : Integrable (fun x => r (E.stat x)) (P θ₁) :=
        ts_integrable_of_density (hp θ₁) hbase
      rw [hνdef]
      exact (MeasureTheory.integrable_map_measure hrmeas.aestronglyMeasurable
        E.stat_meas.aemeasurable).mpr h₁
    have hatomν : ∀ t : ℝ, (ν {t}).toReal < α := by
      intro t
      rw [hνdef, Measure.map_apply E.stat_meas (measurableSet_singleton t)]
      exact hatom t
    -- the sweep: a level window whose ratio-weighted mass is exactly `α`
    obtain ⟨s, hs0, hs1, hroot⟩ :=
      exists_window_root ν hrmeas hrint hrsm hrone hα₀ hα₁ hatomν
    have hmono : Monotone (⇑(cdf ν)) := monotone_cdf (μ := ν)
    have hrc : ∀ y : ℝ, ContinuousWithinAt (⇑(cdf ν)) (Set.Ici y) y :=
      fun y => (cdf ν).right_continuous y
    -- the window is nondegenerate: a degenerate one would be an atom of mass at least `α`
    have hlt : quantile (⇑(cdf ν)) s < quantile (⇑(cdf ν)) (s + α) := by
      have hle : quantile (⇑(cdf ν)) s ≤ quantile (⇑(cdf ν)) (s + α) :=
        quantile_mono _ (by linarith) (cdf_level_nonempty_bddBelow ν hs0 (by linarith)).2
          (cdf_level_nonempty_bddBelow ν (by linarith) hs1).1
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · exfalso
        have h1 : s + α ≤ cdf ν (quantile (⇑(cdf ν)) s) :=
          (quantile_le_iff hmono hrc (cdf_level_nonempty_bddBelow ν (by linarith) hs1).1
            (cdf_level_nonempty_bddBelow ν (by linarith) hs1).2).mp (le_of_eq h.symm)
        have h2 := (cdf_quantile_bounds ν hs0 (show s < 1 by linarith)).2
        have h3 := hatomν (quantile (⇑(cdf ν)) s)
        rw [cdf_singleton_toReal ν (quantile (⇑(cdf ν)) s)] at h3
        linarith
    -- brick (a): the canonical weights, whose size at `θ₁` is `α`
    obtain ⟨γ₁, γ₂, hγ₁, hγ₂, hkey₁, hkey₂, hsizeν⟩ :=
      exists_twoSided_constants_window ν hα₀ hs0 hs1 hlt
    have hmeasval : ∀ D₁ D₂ g₁ g₂ : ℝ, Measurable (twoSidedVal D₁ D₂ g₁ g₂) := by
      intro D₁ D₂ g₁ g₂
      have h := measurable_twoSidedTest (T := (id : ℝ → ℝ)) measurable_id D₁ D₂ g₁ g₂
      have he : twoSidedTest (id : ℝ → ℝ) D₁ D₂ g₁ g₂ = twoSidedVal D₁ D₂ g₁ g₂ :=
        funext fun t => twoSidedTest_eq_val (id : ℝ → ℝ) D₁ D₂ g₁ g₂ t
      rwa [he] at h
    have htest : twoSidedTest E.stat (quantile (⇑(cdf ν)) s) (quantile (⇑(cdf ν)) (s + α))
        γ₁ γ₂ = fun x => twoSidedVal (quantile (⇑(cdf ν)) s)
          (quantile (⇑(cdf ν)) (s + α)) γ₁ γ₂ (E.stat x) :=
      funext fun x => twoSidedTest_eq_val E.stat _ _ _ _ x
    refine ⟨quantile (⇑(cdf ν)) s, quantile (⇑(cdf ν)) (s + α), γ₁, γ₂, hlt, hγ₁, hγ₂, ?_, ?_⟩
    · rw [htest, hpow₁ _ (hmeasval _ _ _ _), hsizeν]
    · rw [htest, hpow₂ _ (hmeasval _ _ _ _),
        twoSidedVal_integral_weight_eq ν hrmeas hrint hα₀ hs0 hs1 hlt hkey₁ hkey₂, hroot]
  exact ⟨C₁, C₂, γ₁, γ₂, hC, hγ₁, hγ₂, hs₁, hs₂,
    isUMP_twoSided_of_constants E P hη hrepr hnat hθ hC hγ₁ hγ₂ hs₁ hs₂⟩


/-- **Comparison of two two-sided tests with a common size at `θ₁`.** If the rejection
interval of the second test lies to the right of that of the first — a larger left
boundary, or the same boundary with a smaller randomization weight there — then the second
test is strictly more powerful above `θ₁` and strictly less powerful below it.

**Repaired statement (`hne`).** As printed — i.e. without `hne` — the theorem is FALSE, and
`hne` is the minimal repair. The conclusion is a *strict* inequality, but nothing in the
printed hypotheses forces the two tests to differ: `hstrict` is vacuous when `T` is
constant, since it only constrains pairs with `T x < T y`.

*Counterexample to the printed form.* `𝓧 = ℝ`, `μ = volume`, `p θ x = ϕ(x − θ)` (so
`hpos : 0 < p θ x` holds), and `T = fun _ => 0`, a measurable constant, so `hstrict` holds
vacuously. Take `C₁ = -2 < C₂ = -1`, `C₁' = 1 < C₂' = 2` and all four `γ = 0`; `hright`
holds as `C₁ = -2 < 1 = C₁'`. Both tests are identically `0`: at `t = 0` neither `t = Cᵢ`
nor `Cᵢ < t < Cᵢ₊₁` holds in either configuration. So `hsize` holds (`0 = 0`) while the
conclusion demands `0 < 0` at every `θ > θ₁`. The failure is not an artefact of the constant
statistic: it occurs whenever both rejection intervals miss the essential range of `T`, and
in every such configuration the two tests coincide `μ`-a.e.

*Repair.* Assume the two tests are not `μ`-a.e. equal (`hne`). This is exactly the
negation of the conclusion of the sibling theorem `twoSided_ae_unique`, so it adds no new
notion; since the densities are strictly positive it is equivalent to the two tests
differing on a set of positive `P θ`-probability for one — equivalently every — `θ`. It
cannot be weakened away: whenever the two tests *are* a.e. equal all four powers coincide
and both strict inequalities fail.

*Proof.* The Lehmann comparison in its strict form. `twoSidedVal_sub_sep` says the positive
part of `D = φ' − φ` sits strictly above its negative part along `T`; `hsize` makes
`∫D p_{θ₁} dμ = 0`; and `integral_pos_of_sep` turns strict MLR plus `hne` into
`∫D p_θ dμ > 0` for `θ₁ < θ`. Below `θ₁` the same lemma is applied to `−D` and `−T`, whose
sign change and ratio monotonicity are both reversed. -/
theorem power_lt_of_twoSided_right
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: densities strictly positive everywhere
    (hpos : ∀ θ x, 0 < p θ x)
    -- USER-INPUT: *strict* monotone likelihood ratio, division-free: the ratio
    -- `p_{θ'}/p_θ` is strictly increasing in `T` for `θ < θ'`
    (hstrict : ∀ θ θ' : ℝ, θ < θ' → ∀ x y, T x < T y → p θ' x * p θ y < p θ x * p θ' y)
    -- USER-INPUT: the constants of the two tests, each an honest rejection interval
    {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ} (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the reference parameter value
    {θ₁ : ℝ}
    -- USER-INPUT: the two tests have the same size at `θ₁`
    (hsize : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₁ =
      power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₁)
    -- USER-INPUT: the second rejection interval lies to the right of the first
    (hright : C₁ < C₁' ∨ (C₁ = C₁' ∧ γ₁' < γ₁))
    -- REPAIR (see the docstring): the two tests are not `μ`-a.e. equal. Without it the
    -- printed statement is FALSE — a rejection interval missing the essential range of `T`
    -- makes both tests a.e. `0` and both strict inequalities fail
    (hne : ¬ twoSidedTest T C₁ C₂ γ₁ γ₂ =ᵐ[μ] twoSidedTest T C₁' C₂' γ₁' γ₂') :
    (∀ θ : ℝ, θ₁ < θ → power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ <
        power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ) ∧
      ∀ θ : ℝ, θ < θ₁ → power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ <
        power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ := by
  set φ := twoSidedTest T C₁ C₂ γ₁ γ₂ with hφdef
  set φ' := twoSidedTest T C₁' C₂' γ₁' γ₂' with hφ'def
  have hφc : IsCriticalFn φ := by
    refine ⟨measurable_twoSidedTest hT C₁ C₂ γ₁ γ₂, fun x => ?_⟩
    rw [hφdef, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁ hγ₂ (T x)
  have hφ'c : IsCriticalFn φ' := by
    refine ⟨measurable_twoSidedTest hT C₁' C₂' γ₁' γ₂', fun x => ?_⟩
    rw [hφ'def, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁' hγ₂' (T x)
  have hcrit_int : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ, Integrable ψ (P ϑ) := by
    intro ψ hψ ϑ
    refine (integrable_const (1 : ℝ)).mono' hψ.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ.2 x).1]
    exact (hψ.2 x).2
  have hmul : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ,
      Integrable (fun x => ψ x * p ϑ x) μ := fun ψ hψ ϑ =>
    ts_density_mul_integrable (hp ϑ) (hcrit_int ψ hψ ϑ)
  have hpow : ∀ (ψ : 𝓧 → ℝ) (ϑ : ℝ), power P ψ ϑ = ∫ x, ψ x * p ϑ x ∂μ := by
    intro ψ ϑ
    unfold power
    exact ts_integral_density_eq (hp ϑ) ψ
  have hDval : ∀ x, φ' x - φ x
      = twoSidedVal C₁' C₂' γ₁' γ₂' (T x) - twoSidedVal C₁ C₂ γ₁ γ₂ (T x) := by
    intro x
    rw [hφdef, hφ'def, twoSidedTest_eq_val, twoSidedTest_eq_val]
  have hDint : ∀ ϑ : ℝ, Integrable (fun x => (φ' x - φ x) * p ϑ x) μ := by
    intro ϑ
    refine ((hmul φ' hφ'c ϑ).sub (hmul φ hφc ϑ)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- The two size conditions at `θ₁` make the difference integrate to zero there.
  have h₁ : ∫ x, (φ' x - φ x) * p θ₁ x ∂μ = 0 := by
    have hcg : ∫ x, (φ' x - φ x) * p θ₁ x ∂μ
        = ∫ x, (φ' x * p θ₁ x - φ x * p θ₁ x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcg, integral_sub (hmul φ' hφ'c θ₁) (hmul φ hφc θ₁), ← hpow φ' θ₁, ← hpow φ θ₁,
      hsize, sub_self]
  -- Nondegeneracy, transported to the difference.
  have hDne : ¬ (fun x => φ' x - φ x) =ᵐ[μ] 0 := by
    intro h
    refine hne ?_
    filter_upwards [h] with x hx
    have hx' : φ' x - φ x = 0 := hx
    linarith
  -- The single sign change: the negative part of `φ' − φ` lies strictly below its
  -- positive part along `T`.
  have hsep : ∀ x y, φ' x - φ x < 0 → 0 < φ' y - φ y → T x < T y := fun x y hx hy =>
    twoSidedVal_sub_sep hC hC' hγ₁ hγ₂ hγ₁' hγ₂' hright
      (by linarith [hDval y]) (by linarith [hDval x])
  constructor
  · intro θ hθ
    have hcore := integral_pos_of_sep (T := T) (D := fun x => φ' x - φ x)
      (p₁ := p θ₁) (p₂ := p θ) (hpos θ₁) (hstrict θ₁ θ hθ) hsep (hDint θ₁) (hDint θ) h₁ hDne
    have hsplit : ∫ x, (φ' x - φ x) * p θ x ∂μ = power P φ' θ - power P φ θ := by
      rw [hpow φ' θ, hpow φ θ, ← integral_sub (hmul φ' hφ'c θ) (hmul φ hφc θ)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hsplit] at hcore
    linarith
  · intro θ hθ
    -- Below `θ₁` both the sign change and the ratio monotonicity reverse; apply the same
    -- lemma to `−D` along `−T`.
    have hstrict' : ∀ x y, -T x < -T y → p θ x * p θ₁ y < p θ₁ x * p θ y := by
      intro x y hxy
      have hTy : T y < T x := by linarith
      have hs := hstrict θ θ₁ hθ y x hTy
      linarith [hs]
    have hsep' : ∀ x y, -(φ' x - φ x) < 0 → 0 < -(φ' y - φ y) → -T x < -T y := by
      intro x y hx hy
      have h1 : 0 < φ' x - φ x := by linarith
      have h2 : φ' y - φ y < 0 := by linarith
      have h3 := hsep y x h2 h1
      linarith
    have hnegint : ∀ ϑ : ℝ, Integrable (fun x => -(φ' x - φ x) * p ϑ x) μ := by
      intro ϑ
      refine (hDint ϑ).neg.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply]
      ring
    have hnegzero : ∫ x, -(φ' x - φ x) * p θ₁ x ∂μ = 0 := by
      rw [show (fun x => -(φ' x - φ x) * p θ₁ x) = fun x => -((φ' x - φ x) * p θ₁ x) from
        funext fun x => by ring, integral_neg, h₁, neg_zero]
    have hnegne : ¬ (fun x => -(φ' x - φ x)) =ᵐ[μ] 0 := by
      intro h
      refine hDne ?_
      filter_upwards [h] with x hx
      have hx' : -(φ' x - φ x) = 0 := hx
      simp only [Pi.zero_apply]
      linarith
    have hcore := integral_pos_of_sep (T := fun x => -T x) (D := fun x => -(φ' x - φ x))
      (p₁ := p θ₁) (p₂ := p θ) (hpos θ₁) hstrict' hsep' (hnegint θ₁) (hnegint θ)
      hnegzero hnegne
    have hsplit : ∫ x, -(φ' x - φ x) * p θ x ∂μ = power P φ θ - power P φ' θ := by
      rw [hpow φ' θ, hpow φ θ, ← integral_sub (hmul φ hφc θ) (hmul φ' hφ'c θ)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hsplit] at hcore
    linarith

/-- **The size conditions determine the test.** Two two-sided tests with size exactly `α`
at both `θ₁` and `θ₂` agree almost everywhere. -/
theorem twoSided_ae_unique
    -- USER-INPUT: dominating measure, σ-finite
    (μ : Measure 𝓧) [SigmaFinite μ]
    -- USER-INPUT: the model and its densities
    (P : ℝ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)]
    (p : ℝ → 𝓧 → ℝ) (hp : ∀ θ, HasDensity μ (p θ) (P θ))
    -- USER-INPUT: the statistic
    (T : 𝓧 → ℝ) (hT : Measurable T)
    -- USER-INPUT: densities strictly positive everywhere
    (hpos : ∀ θ x, 0 < p θ x)
    -- USER-INPUT: *strict* monotone likelihood ratio, division-free
    (hstrict : ∀ θ θ' : ℝ, θ < θ' → ∀ x y, T x < T y → p θ' x * p θ y < p θ x * p θ' y)
    -- USER-INPUT: the constants of the two tests
    {C₁ C₂ C₁' C₂' γ₁ γ₂ γ₁' γ₂' : ℝ} (hC : C₁ < C₂) (hC' : C₁' < C₂')
    (hγ₁ : γ₁ ∈ Set.Icc (0 : ℝ) 1) (hγ₂ : γ₂ ∈ Set.Icc (0 : ℝ) 1)
    (hγ₁' : γ₁' ∈ Set.Icc (0 : ℝ) 1) (hγ₂' : γ₂' ∈ Set.Icc (0 : ℝ) 1)
    -- USER-INPUT: the two null boundaries, in order, and the level
    {θ₁ θ₂ α : ℝ} (hθ : θ₁ < θ₂)
    -- USER-INPUT: both tests meet both size conditions
    (hsize₁ : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₁ = α)
    (hsize₂ : power P (twoSidedTest T C₁ C₂ γ₁ γ₂) θ₂ = α)
    (hsize₁' : power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₁ = α)
    (hsize₂' : power P (twoSidedTest T C₁' C₂' γ₁' γ₂') θ₂ = α) :
    twoSidedTest T C₁ C₂ γ₁ γ₂ =ᵐ[μ] twoSidedTest T C₁' C₂' γ₁' γ₂' := by
  -- Unlike its sibling `power_lt_of_twoSided_right` (which is FALSE as stated), the
  -- degenerate constant-`T` configuration is harmless here: it forces the two tests to take
  -- the same constant value once their sizes agree. The proof is the Lehmann comparison in
  -- its equality form: the difference of the two tests changes sign at most once along `T`
  -- (`twoSidedVal_sub_sep` and `twoSidedVal_sub_sep_eqLeft`, exhausting the trichotomy on
  -- the left data), and a difference with a single sign change that integrates to zero
  -- against two members with a strict monotone likelihood ratio vanishes a.e.
  -- (`ae_eq_zero_of_sep_or`).
  set φ := twoSidedTest T C₁ C₂ γ₁ γ₂ with hφdef
  set φ' := twoSidedTest T C₁' C₂' γ₁' γ₂' with hφ'def
  have hφc : IsCriticalFn φ := by
    refine ⟨measurable_twoSidedTest hT C₁ C₂ γ₁ γ₂, fun x => ?_⟩
    rw [hφdef, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁ hγ₂ (T x)
  have hφ'c : IsCriticalFn φ' := by
    refine ⟨measurable_twoSidedTest hT C₁' C₂' γ₁' γ₂', fun x => ?_⟩
    rw [hφ'def, twoSidedTest_eq_val]
    exact twoSidedVal_mem_Icc hγ₁' hγ₂' (T x)
  have hcrit_int : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ, Integrable ψ (P ϑ) := by
    intro ψ hψ ϑ
    refine (integrable_const (1 : ℝ)).mono' hψ.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ.2 x).1]
    exact (hψ.2 x).2
  have hmul : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → ∀ ϑ : ℝ,
      Integrable (fun x => ψ x * p ϑ x) μ := fun ψ hψ ϑ =>
    ts_density_mul_integrable (hp ϑ) (hcrit_int ψ hψ ϑ)
  have hpow : ∀ (ψ : 𝓧 → ℝ) (ϑ : ℝ), power P ψ ϑ = ∫ x, ψ x * p ϑ x ∂μ := by
    intro ψ ϑ
    unfold power
    exact ts_integral_density_eq (hp ϑ) ψ
  -- The difference of the two tests is a function of the statistic.
  have hDval : ∀ x, φ' x - φ x
      = twoSidedVal C₁' C₂' γ₁' γ₂' (T x) - twoSidedVal C₁ C₂ γ₁ γ₂ (T x) := by
    intro x
    rw [hφdef, hφ'def, twoSidedTest_eq_val, twoSidedTest_eq_val]
  have hDT : ∀ x y, T x = T y → φ' x - φ x = φ' y - φ y := by
    intro x y h
    rw [hDval x, hDval y, h]
  have hDint : ∀ ϑ : ℝ, Integrable (fun x => (φ' x - φ x) * p ϑ x) μ := by
    intro ϑ
    refine ((hmul φ' hφ'c ϑ).sub (hmul φ hφc ϑ)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  -- Equal sizes at a parameter value make the difference integrate to zero there.
  have hDzero : ∀ ϑ : ℝ, power P φ ϑ = power P φ' ϑ →
      ∫ x, (φ' x - φ x) * p ϑ x ∂μ = 0 := by
    intro ϑ heq
    have hcg : ∫ x, (φ' x - φ x) * p ϑ x ∂μ = ∫ x, (φ' x * p ϑ x - φ x * p ϑ x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hcg, integral_sub (hmul φ' hφ'c ϑ) (hmul φ hφc ϑ), ← hpow φ' ϑ, ← hpow φ ϑ, heq,
      sub_self]
  have h₁ := hDzero θ₁ (hsize₁.trans hsize₁'.symm)
  have h₂ := hDzero θ₂ (hsize₂.trans hsize₂'.symm)
  -- The single sign change, in whichever of its two orientations applies.
  have hsep : (∀ x y, φ' x - φ x < 0 → 0 < φ' y - φ y → T x < T y) ∨
      (∀ x y, 0 < φ' x - φ x → φ' y - φ y < 0 → T x < T y) := by
    rcases lt_trichotomy C₁ C₁' with hc | hc | hc
    · exact Or.inl fun x y hx hy => twoSidedVal_sub_sep hC hC' hγ₁ hγ₂ hγ₁' hγ₂'
        (Or.inl hc) (by linarith [hDval y]) (by linarith [hDval x])
    · rcases lt_trichotomy γ₁' γ₁ with hg | hg | hg
      · exact Or.inl fun x y hx hy => twoSidedVal_sub_sep hC hC' hγ₁ hγ₂ hγ₁' hγ₂'
          (Or.inr ⟨hc, hg⟩) (by linarith [hDval y]) (by linarith [hDval x])
      · subst hc
        subst hg
        exact Or.inl fun x y hx hy => (twoSidedVal_sub_sep_eqLeft hC hC' hγ₂ hγ₂'
          (by linarith [hDval y]) (by linarith [hDval x])).elim
      · exact Or.inr fun x y hx hy => twoSidedVal_sub_sep hC' hC hγ₁' hγ₂' hγ₁ hγ₂
          (Or.inr ⟨hc.symm, hg⟩) (by linarith [hDval y]) (by linarith [hDval x])
    · exact Or.inr fun x y hx hy => twoSidedVal_sub_sep hC' hC hγ₁' hγ₂' hγ₁ hγ₂
        (Or.inl hc) (by linarith [hDval y]) (by linarith [hDval x])
  have hcore := ae_eq_zero_of_sep_or (D := fun x => φ' x - φ x) (hpos θ₁)
    (ts_density_integrable (hp θ₁)) (hstrict θ₁ θ₂ hθ) hsep hDT (hDint θ₁) (hDint θ₂) h₁ h₂
  filter_upwards [hcore] with x hx
  have hx' : φ' x - φ x = 0 := hx
  linarith

end StatLean.HypothesisTesting
