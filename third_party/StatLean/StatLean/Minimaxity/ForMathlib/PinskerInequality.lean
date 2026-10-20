module
public import StatLean.Minimaxity.ForMathlib.TotalVariation
public import StatLean.Minimaxity.ForMathlib.KLDivergence
public import StatLean.Minimaxity.ForMathlib.KLDataProcessing

@[expose] public section

/-!
# Pinsker–Csiszár–Kullback inequality

The total variation distance between two probability distributions is controlled by their
Kullback–Leibler divergence: for all distributions $\mathbb{P}$ and $\mathbb{Q}$,
$$\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}} \le \sqrt{\tfrac{1}{2}\, D(\mathbb{Q} \,\|\, \mathbb{P})},$$
equivalently $\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}}^2 \le \tfrac{1}{2}\, D(\mathbb{Q} \,\|\, \mathbb{P})$.
Here $\|\mathbb{P} - \mathbb{Q}\|_{\mathrm{TV}} = \sup_A (\mathbb{P}(A) - \mathbb{Q}(A))$ is the
supremum form of total variation and $D(\cdot\,\|\,\cdot)$ is the KL divergence (in nats), with the
convention $D = +\infty$ when the first argument is not absolutely continuous with respect to the
second.

The Lean statement uses the extended-nonnegative-reals square root (`rpow (1/2)` on `ℝ≥0∞`), so
the bound holds vacuously when the KL divergence is infinite; no absolute-continuity hypothesis is
needed. This matches the book statement exactly (constant $\tfrac12$, no extra assumptions).

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1, Lemma 15.2, Eq. (15.8);
the proof is developed in Exercise 15.6.

**Proof formalization notes.** We follow the route Wainwright outlines in Exercise 15.6.
The argument reduces to the two-point (Bernoulli) case by the data-processing inequality for KL
divergence applied to the binary partition `A = {q ≤ p}`, where `p = dℙ/dξ`, `q = dℚ/dξ` are
densities against the dominating measure `ξ = ℙ + ℚ`. On this optimal set the total variation
equals `ℙ(A) − ℚ(A)` (`tvDist_eq_measure_sub`). The Bernoulli crux is the elementary scalar
inequality (Exercise 15.6(a))
`2 (δ_p − δ_q)² ≤ δ_p log(δ_p/δ_q) + (1 − δ_p) log((1 − δ_p)/(1 − δ_q)) = D(Bern(δ_p) ‖ Bern(δ_q))`,
proved in `bernoulli_pinsker_scalar` by a one-variable convexity argument: the difference
`F(a) = D(Bern(a) ‖ Bern(b)) − 2(a − b)²` satisfies `F(b) = F'(b) = 0` and
`F''(a) = 1/(a(1 − a)) − 4 ≥ 0` (since `a(1 − a) ≤ 1/4`), hence `F ≥ 0`. The degenerate endpoints
`a ∈ {0, 1}` reduce to `2 c² ≤ −log(1 − c)` (`two_sq_le_neg_log_one_sub`). Pushing forward through
the indicator map `f = 𝟙_A : α → Bool` and chaining `klDiv_bool_ge` with the KL data-processing
inequality `klDiv_map_le` gives `2 ‖ℙ − ℚ‖²_TV ≤ D(ℚ ‖ ℙ)` (`klDiv_ge_two_mul_tvDist_sq`); taking
square roots in `ℝ≥0∞` yields the public theorem `pinsker_tv_le_kl`. The constant `½` is exactly the
book's; no deviation.

**Bibliographic comments.** The inequality is jointly attributed to three independent works of the
1960s, whence the triple name. M. S. Pinsker, *Information and Information Stability of Random
Variables and Processes* (translated by A. Feinstein), Holden-Day, San Francisco, 1964, first
established a bound of this form (with a non-optimal constant). The sharp constant `½` (in nats,
giving `‖P − Q‖²_TV ≤ ½ D(Q ‖ P)`) was obtained independently by I. Csiszár,
"Information-type measures of difference of probability distributions and indirect observations",
*Studia Scientiarum Mathematicarum Hungarica* 2 (1967), 299–318, and by S. Kullback,
"A lower bound for discrimination information in terms of variation", *IEEE Transactions on
Information Theory* 13 (1) (1967), 126–127 (with a correction in 13 (4) (1967), 765). The result is
now standard material; the Bernoulli-reduction proof formalized here is the one in
Wainwright's Exercise 15.6.
-/

open MeasureTheory InformationTheory Real Set
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- Derivative of `a ↦ a · log(a/c)` (a fixed nonzero `c`): `a · log(a/c) ↦ log(y/c) + 1`.
Reusable building block for the scalar Bernoulli–Pinsker convexity argument. -/
private lemma mul_log_div_hasDerivAt {c : ℝ} (hc : c ≠ 0) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun a => a * Real.log (a / c)) (Real.log (y / c) + 1) y := by
  have hgy : HasDerivAt (fun a => a / c) (1 / c) y := (hasDerivAt_id y).div_const c
  have hlog : HasDerivAt (fun a => Real.log (a / c)) y⁻¹ y := by
    have h := (Real.hasDerivAt_log (div_ne_zero hy hc)).comp y hgy
    convert! h using 1
    field_simp
  have hp := (hasDerivAt_id y).mul hlog
  convert! hp using 1
  simp only [id_eq, one_mul]
  rw [mul_inv_cancel₀ hy]

/-- **Scalar Bernoulli–Pinsker inequality** (Wainwright Exercise 15.6, pointwise step):
for `a, b ∈ (0, 1)`,
`2 (a − b)² ≤ a log(a/b) + (1 − a) log((1 − a)/(1 − b)) = D(Bern(a) ‖ Bern(b))`.

This is the elementary one-variable calculus fact underlying Pinsker's inequality:
the function `F(a) = a log(a/b) + (1 − a) log((1 − a)/(1 − b)) − 2 (a − b)²` satisfies
`F(b) = F'(b) = 0` and `F''(a) = 1/(a(1 − a)) − 4 ≥ 0` (since `a(1 − a) ≤ 1/4`), hence is
convex with minimum `0` at `a = b`. -/
private lemma bernoulli_pinsker_scalar {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  have hb0' : b ≠ 0 := hb0.ne'
  have hb1' : (1 - b) ≠ 0 := by linarith
  -- the function whose nonnegativity we want, its derivative `G`, and second derivative `H`
  set g : ℝ → ℝ := fun a =>
    a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) - 2 * (a - b) ^ 2 with hg_def
  set G : ℝ → ℝ := fun x => Real.log (x / b) - Real.log ((1 - x) / (1 - b)) - 4 * (x - b) with hG_def
  set H : ℝ → ℝ := fun x => x⁻¹ + (1 - x)⁻¹ - 4 with hH_def
  -- g'(x) = G x on (0,1)
  have hg' : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt g (G x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxne : x ≠ 0 := hx0.ne'
    have hsne : (1 - x) ≠ 0 := by linarith
    have t1 := mul_log_div_hasDerivAt hb0' hxne
    have hsub : HasDerivAt (fun a => (1:ℝ) - a) (-1) x := by
      simpa using! (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have t2base := mul_log_div_hasDerivAt hb1' hsne
    have t2 := t2base.comp x hsub
    have t3 : HasDerivAt (fun a => 2 * (a - b) ^ 2) (4 * (x - b)) x := by
      have h := ((hasDerivAt_id x).sub_const b).pow 2
      have h2 := h.const_mul (2 : ℝ)
      convert! h2 using 1
      simp only [id_eq]; ring
    have hsum := (t1.add t2).sub t3
    convert! hsum using 1
    ring
  -- G'(x) = H x on (0,1)
  have hG' : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt G (H x) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxne : x ≠ 0 := hx0.ne'
    have hsne : (1 - x) ≠ 0 := by linarith
    have hgx : HasDerivAt (fun a => a / b) (1 / b) x := (hasDerivAt_id x).div_const b
    have hl1 : HasDerivAt (fun a => Real.log (a / b)) x⁻¹ x := by
      have h := (Real.hasDerivAt_log (div_ne_zero hxne hb0')).comp x hgx
      convert! h using 1; field_simp
    have hsub : HasDerivAt (fun a => (1:ℝ) - a) (-1) x := by
      simpa using! (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have hgs : HasDerivAt (fun a => a / (1 - b)) (1 / (1 - b)) (1 - x) :=
      (hasDerivAt_id (1 - x)).div_const (1 - b)
    have hl2base : HasDerivAt (fun u => Real.log (u / (1 - b))) (1 - x)⁻¹ (1 - x) := by
      have h := (Real.hasDerivAt_log (div_ne_zero hsne hb1')).comp (1 - x) hgs
      convert! h using 1; field_simp
    have hl2 := hl2base.comp x hsub
    have t3 : HasDerivAt (fun a => 4 * (a - b)) (4 : ℝ) x := by
      have h := ((hasDerivAt_id x).sub_const b).const_mul (4 : ℝ)
      convert! h using 1; ring
    have hsum := (hl1.sub hl2).sub t3
    convert! hsum using 1
    ring
  -- H x ≥ 0 on (0,1), since 1/(x(1−x)) ≥ 4
  have hH_nonneg : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ H x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hs0 : 0 < 1 - x := by linarith
    have hid : x⁻¹ + (1 - x)⁻¹ = 1 / (x * (1 - x)) := by field_simp; ring
    have h4 : 4 ≤ x⁻¹ + (1 - x)⁻¹ := by
      rw [hid, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * x - 1)]
    simp only [hH_def]; linarith
  -- G is monotone on (0,1) (its derivative H is nonnegative)
  have hGmono : MonotoneOn G (Ioo (0:ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
    · exact fun x hx => (hG' x hx).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      exact fun x hx => (hG' x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]
      intro x hx
      rw [(hG' x hx).deriv]
      exact hH_nonneg x hx
  have hbmem : b ∈ Ioo (0:ℝ) 1 := ⟨hb0, hb1⟩
  -- G b = 0 and g b = 0 (tangent at the minimizer)
  have hGb : G b = 0 := by
    simp only [hG_def, div_self hb0', div_self hb1', Real.log_one, sub_self, mul_zero]
  have hgb : g b = 0 := by
    simp only [hg_def, div_self hb0', div_self hb1', Real.log_one, mul_zero, sub_self]
    ring
  -- conclude g a ≥ 0 by monotonicity of g on [b,a] (resp. antitonicity on [a,b])
  have hga : 0 ≤ g a := by
    rcases le_total b a with hba | hab
    · have hsub : Icc b a ⊆ Ioo (0:ℝ) 1 := fun x hx =>
        ⟨lt_of_lt_of_le hb0 hx.1, lt_of_le_of_lt hx.2 ha1⟩
      have hgmono : MonotoneOn g (Icc b a) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc b a)
        · exact fun x hx => (hg' x (hsub hx)).continuousAt.continuousWithinAt
        · intro x hx
          exact (hg' x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt
        · intro x hx
          have hxin : x ∈ Icc b a := interior_subset hx
          rw [(hg' x (hsub hxin)).deriv]
          exact hGb ▸ hGmono hbmem (hsub hxin) hxin.1
      have := hgmono (left_mem_Icc.mpr hba) (right_mem_Icc.mpr hba) hba
      rw [hgb] at this; exact this
    · have hsub : Icc a b ⊆ Ioo (0:ℝ) 1 := fun x hx =>
        ⟨lt_of_lt_of_le ha0 hx.1, lt_of_le_of_lt hx.2 hb1⟩
      have hganti : AntitoneOn g (Icc a b) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
        · exact fun x hx => (hg' x (hsub hx)).continuousAt.continuousWithinAt
        · intro x hx
          exact (hg' x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt
        · intro x hx
          have hxin : x ∈ Icc a b := interior_subset hx
          rw [(hg' x (hsub hxin)).deriv]
          exact hGb ▸ hGmono (hsub hxin) hbmem hxin.2
      have := hganti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
      rw [hgb] at this; exact this
  simp only [hg_def] at hga
  linarith

/-- Boundary case of the scalar Bernoulli–Pinsker inequality: `2 c² ≤ −log(1 − c)` on `[0, 1)`.
This is `bernoulli_pinsker_scalar` at the degenerate value `a = 0` (or, by symmetry, `a = 1`),
where one Bernoulli mass vanishes. The function `H(c) = −log(1 − c) − 2c²` satisfies `H(0) = 0`
and `H'(c) = 1/(1 − c) − 4c = (2c − 1)²/(1 − c) ≥ 0`, hence is monotone. -/
private lemma two_sq_le_neg_log_one_sub {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    2 * c ^ 2 ≤ - Real.log (1 - c) := by
  set H : ℝ → ℝ := fun x => - Real.log (1 - x) - 2 * x ^ 2 with hH
  have hderiv : ∀ x ∈ Set.Icc (0:ℝ) c, HasDerivAt H ((1 - x)⁻¹ - 4 * x) x := by
    intro x hx
    have hx1 : (1 - x) ≠ 0 := by have := hx.2; linarith
    have h1 : HasDerivAt (fun y => (1:ℝ) - y) (-1) x := by
      simpa using! (hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)
    have hlog : HasDerivAt (fun y => -Real.log (1 - y)) ((1 - x)⁻¹) x := by
      have h := (Real.hasDerivAt_log hx1).comp x h1
      have h2 := h.neg
      convert! h2 using 1; field_simp
    have hsq : HasDerivAt (fun y => 2 * y ^ 2) (4 * x) x := by
      have h := (hasDerivAt_id x).pow 2
      have h2 := h.const_mul (2 : ℝ)
      convert! h2 using 1; simp only [id_eq]; ring
    have hsum := hlog.sub hsq
    convert! hsum using 1
  have hH0 : H 0 = 0 := by simp [hH]
  have hmono : MonotoneOn H (Set.Icc 0 c) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 c)
    · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxin : x ∈ Set.Icc (0:ℝ) c := interior_subset hx
      have h1x : (0:ℝ) < 1 - x := by have := hxin.2; linarith
      rw [(hderiv x hxin).deriv]
      have : 4 * x ≤ (1 - x)⁻¹ := by
        rw [inv_eq_one_div, le_div_iff₀ h1x]; nlinarith [sq_nonneg (2 * x - 1)]
      linarith
  have hle := hmono (left_mem_Icc.mpr hc0) (right_mem_Icc.mpr hc0) hc0
  rw [hH0] at hle
  simp only [hH] at hle; linarith

/-- Scalar core after pushing forward to the two-cell partition: with masses `a = ℚ A`, `c = ℙ A`
(densities `dℚ/dξ ≤ dℙ/dξ` on `A`, so `c ∈ (0, 1)`), the binary KL divergence
`klFun(a/c)·c + klFun((1−a)/(1−c))·(1−c)` dominates `2(a − c)²`. The interior case is
`bernoulli_pinsker_scalar`; the two endpoints `a ∈ {0, 1}` use `two_sq_le_neg_log_one_sub`. -/
private lemma two_sq_le_klFun_combo {a c : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hc0 : 0 < c) (hc1 : c < 1) :
    2 * (a - c) ^ 2 ≤ klFun (a / c) * c + klFun ((1 - a) / (1 - c)) * (1 - c) := by
  have hc' : (1 - c) ≠ 0 := by linarith
  have hcne : c ≠ 0 := hc0.ne'
  rcases lt_or_eq_of_le ha0 with ha0pos | ha0eq
  · rcases lt_or_eq_of_le ha1 with ha1lt | rfl
    · -- interior: `0 < a < 1`
      have e1 : klFun (a / c) * c = a * Real.log (a / c) + c - a := by
        have h : a / c * c = a := by field_simp
        rw [klFun_apply,
          show (a / c * Real.log (a / c) + 1 - a / c) * c
              = (a / c * c) * Real.log (a / c) + c - (a / c * c) from by ring, h]
      have e2 : klFun ((1 - a) / (1 - c)) * (1 - c)
          = (1 - a) * Real.log ((1 - a) / (1 - c)) + (1 - c) - (1 - a) := by
        have h : (1 - a) / (1 - c) * (1 - c) = (1 - a) := by field_simp
        rw [klFun_apply,
          show ((1 - a) / (1 - c) * Real.log ((1 - a) / (1 - c)) + 1 - (1 - a) / (1 - c)) * (1 - c)
              = ((1 - a) / (1 - c) * (1 - c)) * Real.log ((1 - a) / (1 - c)) + (1 - c)
                - ((1 - a) / (1 - c) * (1 - c)) from by ring, h]
      rw [e1, e2]
      have := bernoulli_pinsker_scalar ha0pos ha1lt hc0 hc1
      linarith
    · -- endpoint `a = 1`
      have h : (1:ℝ) / c * c = 1 := by field_simp
      have hlog : Real.log (1 / c) = - Real.log c := by rw [one_div, Real.log_inv]
      have e1 : klFun (1 / c) * c = -Real.log c + c - 1 := by
        rw [klFun_apply,
          show (1 / c * Real.log (1 / c) + 1 - 1 / c) * c
              = (1 / c * c) * Real.log (1 / c) + c - (1 / c * c) from by ring, h, one_mul, hlog]
      have e0 : klFun ((1 - 1) / (1 - c)) * (1 - c) = (1 - c) := by simp [klFun_apply]
      rw [e1, e0]
      have hd := two_sq_le_neg_log_one_sub (c := 1 - c) (by linarith) (by linarith)
      rw [show (1:ℝ) - (1 - c) = c from by ring] at hd
      nlinarith [hd]
  · -- endpoint `a = 0`
    rw [← ha0eq]
    have e0 : klFun (0 / c) * c = c := by simp [klFun_apply]
    have h : (1 - 0:ℝ) / (1 - c) * (1 - c) = 1 := by rw [sub_zero]; field_simp
    have hlog : Real.log ((1 - 0) / (1 - c)) = - Real.log (1 - c) := by
      rw [sub_zero, one_div, Real.log_inv]
    have e2 : klFun ((1 - 0) / (1 - c)) * (1 - c) = -Real.log (1 - c) + (1 - c) - 1 := by
      rw [klFun_apply,
        show ((1 - 0) / (1 - c) * Real.log ((1 - 0) / (1 - c)) + 1 - (1 - 0) / (1 - c)) * (1 - c)
            = ((1 - 0) / (1 - c) * (1 - c)) * Real.log ((1 - 0) / (1 - c)) + (1 - c)
              - ((1 - 0) / (1 - c) * (1 - c)) from by ring, h, one_mul, hlog]
    rw [e0, e2]
    have hd := two_sq_le_neg_log_one_sub (c := c) hc0.le hc1
    nlinarith [hd]

/-- **Pinsker on the two-point space.** For probability measures `P, Q` on `Bool`,
`2 (P{true} − Q{true})² ≤ D(P ‖ Q)` (with the convention `D = ⊤` when `P ⋘̸ Q`). This is the
push-forward target of the data-processing reduction: the two atoms carry the Bernoulli masses
and the bound follows from `two_sq_le_klFun_combo`. -/
private lemma klDiv_bool_ge (P Q : Measure Bool)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ENNReal.ofReal (2 * ((P {true}).toReal - (Q {true}).toReal) ^ 2) ≤ klDiv P Q := by
  by_cases hac : P ≪ Q
  · have hPt_top : P {true} ≠ ⊤ := measure_ne_top _ _
    have hQt_top : Q {true} ≠ ⊤ := measure_ne_top _ _
    have hQf_top : Q {false} ≠ ⊤ := measure_ne_top _ _
    by_cases hQt0 : Q {true} = 0
    · have hPt0 : P {true} = 0 := hac hQt0
      have hz : ((P {true}).toReal - (Q {true}).toReal) = 0 := by rw [hPt0, hQt0]; simp
      rw [hz]; simp
    · by_cases hQf0 : Q {false} = 0
      · have hPf0 : P {false} = 0 := hac hQf0
        have hPt1 : P {true} = 1 := by
          have h := prob_compl_eq_one_sub (μ := P) (measurableSet_singleton false)
          rw [Bool.compl_singleton, Bool.not_false] at h
          rw [h, hPf0, tsub_zero]
        have hQt1 : Q {true} = 1 := by
          have h := prob_compl_eq_one_sub (μ := Q) (measurableSet_singleton false)
          rw [Bool.compl_singleton, Bool.not_false] at h
          rw [h, hQf0, tsub_zero]
        have hz : ((P {true}).toReal - (Q {true}).toReal) = 0 := by rw [hPt1, hQt1]; simp
        rw [hz]; simp
      · -- interior: both atoms of `Q` are positive
        have hQf_eq : (Q {false}).toReal = 1 - (Q {true}).toReal := by
          have h : Q {false} = 1 - Q {true} := by
            have := prob_compl_eq_one_sub (μ := Q) (measurableSet_singleton true)
            rwa [Bool.compl_singleton, Bool.not_true] at this
          rw [h, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
        have hPf_eq : (P {false}).toReal = 1 - (P {true}).toReal := by
          have h : P {false} = 1 - P {true} := by
            have := prob_compl_eq_one_sub (μ := P) (measurableSet_singleton true)
            rwa [Bool.compl_singleton, Bool.not_true] at this
          rw [h, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
        -- pointwise Radon–Nikodym identity on each atom
        have key : ∀ b : Bool, P.rnDeriv Q b * Q {b} = P {b} := by
          intro b
          have h1 := Measure.setLIntegral_rnDeriv' hac (measurableSet_singleton b)
          rwa [lintegral_singleton (P.rnDeriv Q) b] at h1
        have hrt : P.rnDeriv Q true = P {true} / Q {true} :=
          (ENNReal.eq_div_iff hQt0 hQt_top).mpr (by rw [mul_comm]; exact key true)
        have hrf : P.rnDeriv Q false = P {false} / Q {false} :=
          (ENNReal.eq_div_iff hQf0 hQf_top).mpr (by rw [mul_comm]; exact key false)
        have hrt_tr : (P.rnDeriv Q true).toReal = (P {true}).toReal / (Q {true}).toReal := by
          rw [hrt, ENNReal.toReal_div]
        have hrf_tr : (P.rnDeriv Q false).toReal
            = (1 - (P {true}).toReal) / (1 - (Q {true}).toReal) := by
          rw [hrf, ENNReal.toReal_div, hPf_eq, hQf_eq]
        have hQt_of : Q {true} = ENNReal.ofReal ((Q {true}).toReal) :=
          (ENNReal.ofReal_toReal hQt_top).symm
        have hQf_of : Q {false} = ENNReal.ofReal (1 - (Q {true}).toReal) := by
          rw [← hQf_eq]; exact (ENNReal.ofReal_toReal hQf_top).symm
        -- numeric facts about the masses
        have ha0 : (0:ℝ) ≤ (P {true}).toReal := ENNReal.toReal_nonneg
        have ha1 : (P {true}).toReal ≤ 1 := by
          rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
        have hc_pos : (0:ℝ) < (Q {true}).toReal := ENNReal.toReal_pos hQt0 hQt_top
        have hc_lt1 : (Q {true}).toReal < 1 := by
          have hpos : (0:ℝ) < (Q {false}).toReal := ENNReal.toReal_pos hQf0 hQf_top
          rw [hQf_eq] at hpos; linarith
        -- freeze the real masses so that `Q {true}` only occurs as the atom multiplier
        set a := (P {true}).toReal with ha_def
        set c := (Q {true}).toReal with hc_def
        rw [klDiv_eq_lintegral_klFun_of_ac hac, lintegral_fintype, Fintype.sum_bool,
          hrt_tr, hrf_tr, hQt_of, hQf_of]
        rw [← ENNReal.ofReal_mul (klFun_nonneg (div_nonneg ha0 hc_pos.le)),
          ← ENNReal.ofReal_mul (klFun_nonneg (div_nonneg (by linarith) (by linarith))),
          ← ENNReal.ofReal_add
              (mul_nonneg (klFun_nonneg (div_nonneg ha0 hc_pos.le)) ENNReal.toReal_nonneg)
              (mul_nonneg (klFun_nonneg (div_nonneg (by linarith) (by linarith))) (by linarith))]
        exact ENNReal.ofReal_le_ofReal (two_sq_le_klFun_combo ha0 ha1 hc_pos hc_lt1)
  · rw [klDiv_of_not_ac hac]; exact le_top

/-- The total-variation supremum is attained on the binary partition `A = {q ≤ p}`
(densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`): `‖ℙ − ℚ‖_TV = ℙ A − ℚ A`. Reproves
the optimal-set identity (the private `TotalVariation` brick is not exported), via
`Measure.setLIntegral_rnDeriv`. -/
private lemma tvDist_eq_measure_sub (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν = μ {x | ν.rnDeriv (μ + ν) x ≤ μ.rnDeriv (μ + ν) x}
                  - ν {x | ν.rnDeriv (μ + ν) x ≤ μ.rnDeriv (μ + ν) x} := by
  have hμξ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hνξ : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  have hpm : Measurable (μ.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hqm : Measurable (ν.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  set A : Set α := {x | ν.rnDeriv (μ + ν) x ≤ μ.rnDeriv (μ + ν) x} with hA
  have hAm : MeasurableSet A := measurableSet_le hqm hpm
  have hle : ν.rnDeriv (μ + ν) ≤ᵐ[(μ + ν).restrict A] μ.rnDeriv (μ + ν) :=
    ae_restrict_of_forall_mem hAm (fun x hx => hx)
  have hfin : ∫⁻ x in A, ν.rnDeriv (μ + ν) x ∂(μ + ν) ≠ ∞ := by
    rw [Measure.setLIntegral_rnDeriv hνξ A]; exact measure_ne_top ν A
  have hAsub : ∫⁻ x in A, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) = μ A - ν A := by
    rw [lintegral_sub hqm hfin hle, Measure.setLIntegral_rnDeriv hμξ A,
        Measure.setLIntegral_rnDeriv hνξ A]
  have hcompl : ∫⁻ x in Aᶜ, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) = 0 := by
    refine setLIntegral_eq_zero hAm.compl (fun x hx => ?_)
    rw [hA, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
    exact tsub_eq_zero_of_le hx.le
  have hDA : ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) = μ A - ν A := by
    rw [← lintegral_add_compl _ hAm, hcompl, add_zero, hAsub]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun s => iSup_le fun _ => ?_
    calc μ s - ν s
        = ∫⁻ x in s, μ.rnDeriv (μ + ν) x ∂(μ + ν)
            - ∫⁻ x in s, ν.rnDeriv (μ + ν) x ∂(μ + ν) := by
          rw [Measure.setLIntegral_rnDeriv hμξ s, Measure.setLIntegral_rnDeriv hνξ s]
      _ ≤ ∫⁻ x in s, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) :=
          lintegral_sub_le _ _ hqm
      _ ≤ ∫⁻ x, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) :=
          lintegral_mono' Measure.restrict_le_self le_rfl
      _ = μ A - ν A := hDA
  · exact le_iSup₂ (f := fun s (_ : MeasurableSet s) => μ s - ν s) A hAm

/-- **Data-processing core of Pinsker's inequality** (Wainwright Exercise 15.6).

The KL divergence dominates `2 · ‖ℙ − ℚ‖²_TV`. By the data-processing inequality for KL under
the binary partition `A = {q ≤ p}` (densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`),
`D(ℚ ‖ ℙ) ≥ D(Bern(ℚ A) ‖ Bern(ℙ A))`, and on the optimal set `A` the total variation equals
`ℙ A − ℚ A`. Combined with the scalar Bernoulli–Pinsker inequality
`bernoulli_pinsker_scalar` this gives the bound. -/
private lemma klDiv_ge_two_mul_tvDist_sq (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * (tvDist μ ν).toReal ^ 2) ≤ klDiv ν μ := by
  have hpm : Measurable (μ.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hqm : Measurable (ν.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  set A : Set α := {x | ν.rnDeriv (μ + ν) x ≤ μ.rnDeriv (μ + ν) x} with hA
  have hAm : MeasurableSet A := measurableSet_le hqm hpm
  have hμξ : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have hνξ : ν ≪ μ + ν := rfl.absolutelyContinuous.add_right' _
  -- on the optimal set the densities satisfy `q ≤ p`, hence `ν A ≤ μ A`
  have hνμA : ν A ≤ μ A := by
    have hle : ν.rnDeriv (μ + ν) ≤ᵐ[(μ + ν).restrict A] μ.rnDeriv (μ + ν) :=
      ae_restrict_of_forall_mem hAm (fun x hx => hx)
    calc ν A = ∫⁻ x in A, ν.rnDeriv (μ + ν) x ∂(μ + ν) :=
          (Measure.setLIntegral_rnDeriv hνξ A).symm
      _ ≤ ∫⁻ x in A, μ.rnDeriv (μ + ν) x ∂(μ + ν) := lintegral_mono_ae hle
      _ = μ A := Measure.setLIntegral_rnDeriv hμξ A
  -- the indicator of `A` as a measurable map to `Bool`
  set f : α → Bool := fun x => decide (x ∈ A) with hf_def
  have hpre : f ⁻¹' {true} = A := by ext x; simp [hf_def]
  have hfm : Measurable f := measurable_to_bool (by rw [hpre]; exact hAm)
  have hPt : (ν.map f) {true} = ν A := by
    rw [Measure.map_apply hfm (measurableSet_singleton true), hpre]
  have hQt : (μ.map f) {true} = μ A := by
    rw [Measure.map_apply hfm (measurableSet_singleton true), hpre]
  have htv_tr : (tvDist μ ν).toReal = (μ A).toReal - (ν A).toReal := by
    rw [tvDist_eq_measure_sub μ ν, ENNReal.toReal_sub_of_le hνμA (measure_ne_top μ A)]
  haveI : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hfm.aemeasurable
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hfm.aemeasurable
  calc ENNReal.ofReal (2 * (tvDist μ ν).toReal ^ 2)
      = ENNReal.ofReal (2 * (((ν.map f) {true}).toReal - ((μ.map f) {true}).toReal) ^ 2) := by
        rw [htv_tr, hPt, hQt]; congr 1; ring
    _ ≤ klDiv (ν.map f) (μ.map f) := klDiv_bool_ge (ν.map f) (μ.map f)
    _ ≤ klDiv ν μ := klDiv_map_le hfm ν μ

/-- **Bernoulli crux of Pinsker's inequality** (Wainwright Exercise 15.6).

With densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`, the half-`L¹` form of total variation
is bounded by the KL divergence through the data-processing reduction to the Bernoulli partition
`A = {p ≥ q}` and the pointwise inequality
`2 (δ_p − δ_q)² ≤ δ_p log(δ_p/δ_q) + (1 − δ_p) log((1 − δ_p)/(1 − δ_q))` followed by Jensen.
This is the genuine analytic core; the public theorem `pinsker_tv_le_kl` follows by the density
form `tvDist_eq_half_lintegral`. -/
private lemma pinsker_half_lintegral_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)
      ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  rw [← tvDist_eq_half_lintegral]
  by_cases hkl : klDiv ν μ = ⊤
  · rw [hkl, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top),
        ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact le_top
  · have htv1 : tvDist μ ν ≤ 1 := tvDist_le_one μ ν
    have htvne : tvDist μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top htv1
    set t : ℝ := (tvDist μ ν).toReal with ht
    set k : ℝ := (klDiv ν μ).toReal with hk
    have ht_nn : 0 ≤ t := ENNReal.toReal_nonneg
    have hk_nn : 0 ≤ k := ENNReal.toReal_nonneg
    have htv_eq : tvDist μ ν = ENNReal.ofReal t := (ENNReal.ofReal_toReal htvne).symm
    have hkl_eq : klDiv ν μ = ENNReal.ofReal k := (ENNReal.ofReal_toReal hkl).symm
    -- Core scalar bound `2 t² ≤ k` from the data-processing lemma.
    have hcore : 2 * t ^ 2 ≤ k := by
      have h := klDiv_ge_two_mul_tvDist_sq μ ν
      rw [← ht, hkl_eq] at h
      exact (ENNReal.ofReal_le_ofReal_iff hk_nn).mp h
    -- Assemble in `ℝ≥0∞`.
    rw [htv_eq, hkl_eq,
        show (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal k = ENNReal.ofReal (k / 2) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat,
              div_eq_mul_inv, mul_comm],
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show t = Real.sqrt (t ^ 2) from (Real.sqrt_sq ht_nn).symm]
    exact Real.sqrt_le_sqrt (by linarith)

/-- **Pinsker–Csiszár–Kullback inequality** (Wainwright Lemma 15.2, Eq. (15.8)):
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2. -/
theorem pinsker_tv_le_kl (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  rw [tvDist_eq_half_lintegral]
  exact pinsker_half_lintegral_le μ ν

end StatLean.Minimaxity
