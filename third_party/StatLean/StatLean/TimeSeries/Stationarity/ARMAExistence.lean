module
public import StatLean.TimeSeries.Process.LinearProcess
public import StatLean.TimeSeries.Models.Linear
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
# Stationary ARMA processes: existence, causality, Yule–Walker (FY §2.1.2, §2.2.1)

The transfer coefficients `ψ = a(z)/b(z)` of an ARMA(p, q) model as formal power-series
coefficients (`armaPsi`, via `PowerSeries.inv` — well-defined since `b(0) = 1`), and:

* **FY Theorem 2.1**: if `b(z) ≠ 0` on the closed unit disc, the coefficients decay
  geometrically (Cauchy estimates on the analytic function `a/b` on a disc of radius
  `> 1`), are absolutely summable, and the linear process `X = Σ ψ_j ε_{t−j}` is a
  stationary, causal solution of the ARMA equation;
* **Definition 2.3** (causality) as `IsCausalFor`;
* the **Yule–Walker recurrences** (FY eq. (2.21)): `γ(k) = Σᵢ bᵢ γ(k−1−i)` for `k > q`;
* **Proposition 2.2(i)**: exponential decay of the ACVF of a causal ARMA process;
* the Brockwell–Davis iff-facts (causality ⇔ no roots in the closed disc; uniqueness ⇔
  no roots on the circle) as statement-level DEBTS (FY cites them without proof).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.2
(Theorem 2.1, Definition 2.3, eqs. (2.3)–(2.5), pp. 30–32) and §2.2.1 (eqs. (2.20)–(2.22),
Proposition 2.2, pp. 40–41). (`FY §2.1.2 Thm 2.1, Def 2.3; §2.2.1 eq. (2.21), Prop 2.2`.)

**Proof formalization notes.**
* `armaPsi` is defined through the formal inverse in `ℝ⟦X⟧` (constant coefficient of
  `arPoly b` is `1`); the analytic content enters only through the geometric bound.
* FY proves Theorem 2.1 by the geometric expansion of `1/b`; we route the coefficient
  bound through `HasFPowerSeriesOnBall` Cauchy estimates
  (`FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`) after identifying the
  formal and analytic expansions (both are power-series solutions of `b · ψ = a`).
* The Yule–Walker derivation replaces the book's "independent" by "uncorrelated"
  (flagged in the inventory): causality kills the covariances of future innovations
  against the past through `L²`-limit continuity.
* Prop 2.2(i) avoids the book's distinct-roots partial-fraction argument entirely (the
  inventory flags the repeated-root gap): geometric decay of `ψ` gives
  `|γ(k)| ≤ σ² C² r^k/(1−r²)` directly.

**Bibliographic comments.** The MA(∞) solution of stationary ARMA equations is H. Wold
(1938); the systematic causality/invertibility theory is P. J. Brockwell and R. A. Davis,
*Time Series: Theory and Methods*, 2nd ed., Springer, 1991, §3.1 (Thm 3.1.1, Prop 3.1.2).
Yule–Walker equations: G. U. Yule (1927), G. T. Walker (1931).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **ARMA transfer coefficients** `ψ_n = [zⁿ] a(z)/b(z)` (FY eq. (2.5)'s `d_j`),
as formal power-series coefficients; well-defined because `b(0) = 1` makes `arPoly b`
invertible in `ℝ⟦X⟧`. -/
noncomputable def armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n
    (((maPoly a : Polynomial ℝ) : PowerSeries ℝ) *
      (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)

/-- `b` has **no roots in the closed unit disc** (over ℂ) — FY's standing condition
`b(z) ≠ 0` for `|z| ≤ 1`. -/
def NoRootClosedDisc {p : ℕ} (b : Fin p → ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z (arPoly b) ≠ 0

section Coeff

/-- The coefficients of the AR polynomial `b(z) = 1 - b₁z - ⋯ - b_pz^p`. -/
private lemma coeff_arPoly {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then (1 : ℝ) else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_arPoly_zero {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  rw [coeff_arPoly]; simp

/-- The coefficients of the MA polynomial `a(z) = 1 + a₁z + ⋯ + a_qz^q`. -/
private lemma coeff_maPoly {q : ℕ} (a : Fin q → ℝ) (m : ℕ) :
    (maPoly a).coeff m
      = (if m = 0 then (1 : ℝ) else 0) + ∑ j : Fin q, if m = (j : ℕ) + 1 then a j else 0 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_maPoly_zero {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  rw [coeff_maPoly]; simp

/-- The constant coefficient of `arPoly b` as a power series is `1`, hence nonzero: this is
what makes the formal inverse in `ℝ⟦X⟧` available. -/
private lemma constantCoeff_arPoly_ne_zero {p : ℕ} (b : Fin p → ℝ) :
    PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero]
  exact one_ne_zero

end Coeff

/-- `ψ_0 = 1` (both polynomials have constant coefficient `1`). -/
theorem armaPsi_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    armaPsi b a 0 = 1 := by
  rw [armaPsi, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_inv,
    Polynomial.constantCoeff_coe, Polynomial.constantCoeff_coe, coeff_arPoly_zero,
    coeff_maPoly_zero, inv_one, mul_one]

/-- The defining convolution identity `b ∗ ψ = a` (FY eq. (2.5) read coefficientwise):
`Σ_{k≤n} (arPoly b).coeff k · ψ_{n−k} = (maPoly a).coeff n`. -/
theorem arPoly_conv_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (arPoly b).coeff k * armaPsi b a (n - k)
      = (maPoly a).coeff n := by
  have key : (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
      ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
        (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) := by
    rw [← mul_assoc, mul_comm (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)),
      mul_assoc, PowerSeries.mul_inv_cancel _ (constantCoeff_arPoly_ne_zero b), mul_one]
  have hcoeff := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe] at hcoeff
  rw [← hcoeff]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]; rfl

section AnalyticCore

private lemma hasSum_poly_mul {c : ℕ → ℂ} {z S : ℂ} (P : Polynomial ℂ)
    (h : HasSum (fun n => c n * z ^ n) S) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), P.coeff k * c (n - k)) * z ^ n)
      (P.eval z * S) := by
  classical
  have hcz : ∀ k, P.natDegree < k → P.coeff k = 0 := fun k hk =>
    Polynomial.coeff_eq_zero_of_natDegree_lt hk
  have hkey : ∀ k : ℕ, HasSum (fun m => (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m)
      (P.coeff k * z ^ k * S) := by
    intro k
    have h1 : HasSum (fun n => P.coeff k * z ^ k * (c n * z ^ n)) (P.coeff k * z ^ k * S) :=
      h.mul_left _
    have hg : Function.Injective (fun n : ℕ => k + n) := add_right_injective k
    have hzero : ∀ x ∉ Set.range (fun n : ℕ => k + n),
        (if k ≤ x then P.coeff k * c (x - k) else 0) * z ^ x = 0 := by
      intro x hx
      rw [if_neg, zero_mul]
      intro hkx
      exact hx ⟨x - k, by show k + (x - k) = x; omega⟩
    refine (hg.hasSum_iff hzero).1 ?_
    have heq : ((fun m => (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m) ∘
        fun n : ℕ => k + n) = fun n => P.coeff k * z ^ k * (c n * z ^ n) := by
      funext n
      simp only [Function.comp_apply, if_pos (Nat.le_add_right k n), Nat.add_sub_cancel_left,
        pow_add]
      ring
    rw [heq]
    exact h1
  have hsum := hasSum_sum (s := Finset.range (P.natDegree + 1)) (fun k _ => hkey k)
  have hrhs : ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * z ^ k * S = P.eval z * S := by
    rw [← Finset.sum_mul, ← Polynomial.eval_eq_sum_range]
  rw [hrhs] at hsum
  have hfun : (fun m => ∑ k ∈ Finset.range (P.natDegree + 1),
        (if k ≤ m then P.coeff k * c (m - k) else 0) * z ^ m)
      = fun n => (∑ k ∈ Finset.range (n + 1), P.coeff k * c (n - k)) * z ^ n := by
    funext m
    rw [← Finset.sum_mul]
    congr 1
    obtain ⟨N, hNd, hNm⟩ : ∃ N : ℕ, P.natDegree ≤ N ∧ m ≤ N :=
      ⟨max P.natDegree m, le_max_left _ _, le_max_right _ _⟩
    have e1 : ∑ k ∈ Finset.range (P.natDegree + 1),
          (if k ≤ m then P.coeff k * c (m - k) else 0)
        = ∑ k ∈ Finset.range (N + 1), (if k ≤ m then P.coeff k * c (m - k) else 0) := by
      have hsub : Finset.range (P.natDegree + 1) ⊆ Finset.range (N + 1) := by
        intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
      refine Finset.sum_subset hsub fun k _ hk => ?_
      simp only [Finset.mem_range, not_lt] at hk
      rw [hcz k (by omega)]
      simp
    have e2 : ∑ k ∈ Finset.range (m + 1), P.coeff k * c (m - k)
        = ∑ k ∈ Finset.range (N + 1), (if k ≤ m then P.coeff k * c (m - k) else 0) := by
      have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
        intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
      rw [← Finset.sum_subset hsub (fun k _ hk => by
        simp only [Finset.mem_range, not_lt] at hk
        rw [if_neg (by omega)])]
      exact Finset.sum_congr rfl fun k hk => by
        simp only [Finset.mem_range] at hk
        rw [if_pos (by omega)]
    rw [e1, e2]
  rwa [hfun] at hsum

private lemma hasSum_poly (P : Polynomial ℂ) (z : ℂ) :
    HasSum (fun n => P.coeff n * z ^ n) (P.eval z) := by
  classical
  have h : HasSum (fun n => P.coeff n * z ^ n)
      (∑ n ∈ Finset.range (P.natDegree + 1), P.coeff n * z ^ n) :=
    hasSum_sum_of_ne_finset_zero (fun n hn => by
      simp only [Finset.mem_range, not_lt] at hn
      show P.coeff n * z ^ n = 0
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul])
  rwa [← Polynomial.eval_eq_sum_range] at h

private lemma exists_crude_bound_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    ∃ C M : ℝ, 0 ≤ C ∧ 1 ≤ M ∧ ∀ n, |armaPsi b a n| ≤ C * M ^ n := by
  classical
  have hbound : ∀ (P : Polynomial ℝ) (n : ℕ),
      |P.coeff n| ≤ ∑ j ∈ Finset.range (P.natDegree + 1), |P.coeff j| := by
    intro P n
    by_cases hn : n ≤ P.natDegree
    · exact Finset.single_le_sum (f := fun j => |P.coeff j|) (fun j _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), abs_zero]
      exact Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨Ca, hCa0, hCa⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ n, |(maPoly a).coeff n| ≤ C := by
    refine ⟨_, ?_, hbound (maPoly a)⟩
    have h := hbound (maPoly a) 0
    rwa [coeff_maPoly_zero, abs_one] at h
  obtain ⟨Cb, hCb0, hCb⟩ : ∃ C : ℝ, 1 ≤ C ∧ ∀ n, |(arPoly b).coeff n| ≤ C := by
    refine ⟨_, ?_, hbound (arPoly b)⟩
    have h := hbound (arPoly b) 0
    rwa [coeff_arPoly_zero, abs_one] at h
  refine ⟨Ca, 1 + Cb, by linarith, by linarith, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hrec := arPoly_conv_armaPsi b a n
    rw [Finset.sum_range_succ', coeff_arPoly_zero, one_mul, Nat.sub_zero] at hrec
    have hpsi : armaPsi b a n = (maPoly a).coeff n
        - ∑ i ∈ Finset.range n, (arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1)) := by
      linarith
    have htri : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
      calc |x - y| = |x + -y| := by rw [sub_eq_add_neg]
        _ ≤ |x| + |-y| := abs_add_le _ _
        _ = |x| + |y| := by rw [abs_neg]
    have h1 : |armaPsi b a n| ≤ |(maPoly a).coeff n|
        + ∑ i ∈ Finset.range n, |(arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1))| := by
      rw [hpsi]
      exact (htri _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    have h2 : ∑ i ∈ Finset.range n, |(arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1))|
        ≤ ∑ i ∈ Finset.range n, Cb * (Ca * (1 + Cb) ^ (n - 1 - i)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [abs_mul, show n - (i + 1) = n - 1 - i by omega]
      exact mul_le_mul (hCb _) (ih _ (by omega)) (abs_nonneg _) (by linarith)
    have hrefl : ∑ j ∈ Finset.range n, (1 + Cb) ^ (n - 1 - j)
        = ∑ j ∈ Finset.range n, (1 + Cb) ^ j :=
      Finset.sum_range_reflect (fun j => (1 + Cb) ^ j) n
    have h3 : ∑ i ∈ Finset.range n, Cb * (Ca * (1 + Cb) ^ (n - 1 - i))
        = Cb * Ca * ∑ j ∈ Finset.range n, (1 + Cb) ^ j := by
      rw [← hrefl, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hgeom : (∑ j ∈ Finset.range n, (1 + Cb) ^ j) * Cb = (1 + Cb) ^ n - 1 := by
      have h := geom_sum_mul (1 + Cb) n
      rwa [add_sub_cancel_left] at h
    calc |armaPsi b a n|
        ≤ |(maPoly a).coeff n|
          + ∑ i ∈ Finset.range n, |(arPoly b).coeff (i + 1) * armaPsi b a (n - (i + 1))| := h1
      _ ≤ Ca + Cb * Ca * ∑ j ∈ Finset.range n, (1 + Cb) ^ j := by
          rw [← h3]; exact add_le_add (hCa n) h2
      _ = Ca + Ca * ((1 + Cb) ^ n - 1) := by rw [← hgeom]; ring
      _ = Ca * (1 + Cb) ^ n := by ring


end AnalyticCore

/-- **Geometric decay of the transfer coefficients** (the analytic core of FY Theorem
2.1): with no roots of `b` in the closed unit disc, `|ψ_n| ≤ C rⁿ` for some `r < 1`. -/
theorem exists_geometric_bound_armaPsi {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    -- USER-INPUT: no roots of b(z) in the closed unit disc; FY §2.1.2 Thm 2.1
    (hb : NoRootClosedDisc b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n, |armaPsi b a n| ≤ C * r ^ n := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : Polynomial ℂ, A = (maPoly a).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : Polynomial ℂ, B = (arPoly b).map (algebraMap ℝ ℂ) := ⟨_, rfl⟩
  have hAc : ∀ k, A.coeff k = ((maPoly a).coeff k : ℂ) := by
    intro k; rw [hAdef, Polynomial.coeff_map]; simp
  have hBc : ∀ k, B.coeff k = ((arPoly b).coeff k : ℂ) := by
    intro k; rw [hBdef, Polynomial.coeff_map]; simp
  have hBev : ∀ z : ℂ, B.eval z = Polynomial.aeval z (arPoly b) := by
    intro z; rw [hBdef, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hBne : B ≠ 0 := by
    intro h
    have h0 := hBc 0
    rw [h, coeff_arPoly_zero] at h0
    simp at h0
  have hBdisc : ∀ z : ℂ, ‖z‖ ≤ 1 → B.eval z ≠ 0 := fun z hz => by rw [hBev]; exact hb z hz
  -- a radius `R > 1` free of roots of `B`
  obtain ⟨R, hR1, hRroot⟩ : ∃ R : ℝ, 1 < R ∧ ∀ z : ℂ, ‖z‖ ≤ R → B.eval z ≠ 0 := by
    obtain ⟨S, hS⟩ : ∃ S : Finset ℝ, S = insert (2 : ℝ) (B.roots.toFinset.image fun z => ‖z‖) :=
      ⟨_, rfl⟩
    have hSne : S.Nonempty := ⟨2, by rw [hS]; exact Finset.mem_insert_self _ _⟩
    have hSgt : ∀ x ∈ S, 1 < x := by
      intro x hx
      rw [hS, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · norm_num
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
        have hzr : B.eval z = 0 := (Polynomial.mem_roots'.1 (Multiset.mem_toFinset.1 hz)).2
        by_contra hcon
        exact hBdisc z (by linarith [not_lt.1 hcon]) hzr
    refine ⟨(1 + S.min' hSne) / 2, by linarith [hSgt _ (S.min'_mem hSne)], ?_⟩
    intro z hz hzero
    have hmem : ‖z‖ ∈ S := by
      rw [hS]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Multiset.mem_toFinset.2 (Polynomial.mem_roots'.2 ⟨hBne, hzero⟩)))
    have := S.min'_le _ hmem
    have := hSgt _ (S.min'_mem hSne)
    linarith
  obtain ⟨R', hR'1, hR'R⟩ : ∃ R' : NNReal, 1 < (R' : ℝ) ∧ ((R' : ℝ)) ≤ R := by
    refine ⟨R.toNNReal, ?_, ?_⟩ <;> rw [Real.coe_toNNReal _ (by linarith)]
    · exact hR1
  obtain ⟨g, hgdef⟩ : ∃ g : ℂ → ℂ, g = fun z => A.eval z / B.eval z := ⟨_, rfl⟩
  have hdiff : DifferentiableOn ℂ g (Metric.closedBall 0 (R' : ℝ)) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rw [hgdef]
    exact A.differentiableAt.div B.differentiableAt (hRroot z (le_trans hz hR'R))
  have hR'pos : (0 : NNReal) < R' := by
    have : (0:ℝ) < (R' : ℝ) := by linarith
    exact_mod_cast this
  have hcauchy := hdiff.hasFPowerSeriesOnBall hR'pos
  -- the formal series of the ARMA coefficients
  obtain ⟨C0, M, hC0, hM1, hcrude⟩ := exists_crude_bound_armaPsi b a
  obtain ⟨ψc, hψc⟩ : ∃ f : ℕ → ℂ, f = fun n => ((armaPsi b a n : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ P : FormalMultilinearSeries ℂ ℂ ℂ,
      P = FormalMultilinearSeries.ofScalars ℂ ψc := ⟨_, rfl⟩
  have hΨnorm : ∀ n, ‖Ψ n‖ = |armaPsi b a n| := by
    intro n
    rw [hΨ, FormalMultilinearSeries.ofScalars_norm, hψc]
    simp
  have hMpos : (0:ℝ) < M := by linarith
  have hradpos : 0 < Ψ.radius := by
    have hcoe : ((M⁻¹).toNNReal : ℝ) = M⁻¹ := Real.coe_toNNReal _ (by positivity)
    have hle : (((M⁻¹).toNNReal : NNReal) : ENNReal) ≤ Ψ.radius := by
      refine Ψ.le_radius_of_bound C0 (r := (M⁻¹).toNNReal) fun n => ?_
      rw [hΨnorm, hcoe, inv_pow]
      have hpow : (0:ℝ) < M ^ n := by positivity
      calc |armaPsi b a n| * (M ^ n)⁻¹ ≤ (C0 * M ^ n) * (M ^ n)⁻¹ := by
            exact mul_le_mul_of_nonneg_right (hcrude n) (by positivity)
        _ = C0 := by field_simp
    refine lt_of_lt_of_le ?_ hle
    have : (0:ℝ) < ((M⁻¹).toNNReal : ℝ) := by rw [hcoe]; positivity
    exact_mod_cast this
  have hΨball : HasFPowerSeriesOnBall Ψ.sum Ψ 0 Ψ.radius :=
    Ψ.hasFPowerSeriesOnBall hradpos
  obtain ⟨r1, hr1pos, hr1rad, hr1one⟩ :
      ∃ r1 : ENNReal, 0 < r1 ∧ r1 ≤ Ψ.radius ∧ r1 ≤ 1 :=
    ⟨min Ψ.radius 1, lt_min hradpos (by norm_num), min_le_left _ _, min_le_right _ _⟩
  have hΨsmall : HasFPowerSeriesOnBall Ψ.sum Ψ 0 r1 := hΨball.mono hr1pos hr1rad
  have heqon : Set.EqOn Ψ.sum g (Metric.eball (0 : ℂ) r1) := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by
      have h1 : (‖z‖₊ : ENNReal) < r1 := by
        simpa [Metric.eball, edist_eq_enorm_sub] using! hz
      have h2 : (‖z‖₊ : ENNReal) < 1 := lt_of_lt_of_le h1 hr1one
      have : ‖z‖₊ < 1 := by exact_mod_cast h2
      exact le_of_lt (by exact_mod_cast this)
    have hsum : HasSum (fun n => ψc n * z ^ n) (Ψ.sum z) := by
      have h := hΨsmall.hasSum (y := z) hz
      rw [zero_add] at h
      have h' : ∀ n : ℕ, Ψ n (fun _ => z) = ψc n * z ^ n := fun n => by
        rw [hΨ, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
      simpa only [h'] using h
    have h1 := hasSum_poly_mul B hsum
    have hcoef : ∀ n, (∑ k ∈ Finset.range (n + 1), B.coeff k * ψc (n - k)) = A.coeff n := by
      intro n
      rw [hAc, ← arPoly_conv_armaPsi b a n]
      push_cast [hBc, hψc]
      rfl
    simp only [hcoef] at h1
    have h2 := hasSum_poly A z
    have hkey := h1.unique h2
    rw [hgdef]
    rw [eq_div_iff (hBdisc z hzn)]
    simpa [mul_comm] using hkey
  have hΨg : HasFPowerSeriesOnBall g Ψ 0 r1 := hΨsmall.congr heqon
  have hfinal : HasFPowerSeriesOnBall g Ψ 0 (R' : ENNReal) := hΨg.exchange_radius hcauchy
  have h1rad : ((1 : NNReal) : ENNReal) < Ψ.radius := by
    refine lt_of_lt_of_le ?_ hfinal.r_le
    exact_mod_cast hR'1
  obtain ⟨α, hα, C, hC, hbnd⟩ := Ψ.norm_mul_pow_le_mul_pow_of_lt_radius h1rad
  refine ⟨C, le_of_lt hC, α, le_of_lt hα.1, hα.2, fun n => ?_⟩
  have h := hbnd n
  rw [hΨnorm] at h
  simpa using h


/-- Absolute summability of the transfer coefficients (FY Theorem 2.1's `Σ|d_j| < ∞`). -/
theorem summable_abs_armaPsi {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    (hb : NoRootClosedDisc b) :
    Summable fun n => |armaPsi b a n| := by
  obtain ⟨C, hC, r, hr0, hr1, hbnd⟩ := exists_geometric_bound_armaPsi a hb
  exact Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbnd
    ((summable_geometric_of_lt_one hr0 hr1).mul_left C)


section Aux

variable {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

/-- `inner ℝ` on the reals is multiplication. -/
private lemma real_inner_mul (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²` inner product of two classes is the integral of the product. -/
private lemma inner_toLp {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul, h1, h2]

/-- Cauchy–Schwarz for the `L²` pairing. -/
private lemma abs_integral_mul_le {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  rw [← inner_toLp hf hg]
  calc |(inner ℝ (hf.toLp f) (hg.toLp g) : ℝ)| ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ :=
        abs_real_inner_le_norm _ _
    _ = (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by rw [Lp.norm_toLp, Lp.norm_toLp]

/-- Distinct white-noise times have vanishing mixed moment. -/
private lemma integral_noise_mul_eq_zero [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    {s t : ℤ} (hst : s ≠ t) : ∫ ω, ε s ω * ε t ω ∂μ = 0 := by
  have h := covariance_eq_sub (hε.memLp s) (hε.memLp t)
  rw [hε.integral_eq_zero s, zero_mul, sub_zero, hε.uncorrelated s t hst] at h
  have h2 : μ[ε s * ε t] = ∫ ω, ε s ω * ε t ω ∂μ := by simp [Pi.mul_apply]
  rw [h2] at h
  exact h.symm

/-- The `L²` norm of the noise is the same at every time. -/
private lemma eLpNorm_noise_eq [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ) (t : ℤ) :
    eLpNorm (ε t) 2 μ = ENNReal.ofReal (Real.sqrt σ2) := by
  have hsq : ‖(hε.memLp t).toLp (ε t)‖ ^ 2 = σ2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have h := covariance_eq_sub (hε.memLp t) (hε.memLp t)
    rw [hε.integral_eq_zero t, zero_mul, sub_zero,
      covariance_self (hε.memLp t).aestronglyMeasurable.aemeasurable, hε.variance_eq t] at h
    have h2 : μ[ε t * ε t] = ∫ ω, ε t ω * ε t ω ∂μ := by simp [Pi.mul_apply]
    rw [h2] at h
    exact h.symm
  have hnorm : ‖(hε.memLp t).toLp (ε t)‖ = Real.sqrt σ2 := by
    have := Real.sqrt_sq (norm_nonneg ((hε.memLp t).toLp (ε t)))
    rw [hsq] at this
    exact this.symm
  rw [Lp.norm_toLp] at hnorm
  rw [← hnorm, ENNReal.ofReal_toReal (hε.memLp t).2.ne]

/-- The `L²` norm of a finite noise combination. -/
private lemma eLpNorm_noise_comb_le [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (u : ι → ℤ) :
    eLpNorm (fun ω => ∑ i ∈ s, c i * ε (u i) ω) 2 μ
      ≤ ENNReal.ofReal (∑ i ∈ s, |c i|) * ENNReal.ofReal (Real.sqrt σ2) := by
  have hfun : (fun ω => ∑ i ∈ s, c i * ε (u i) ω) = ∑ i ∈ s, fun ω => c i * ε (u i) ω := by
    funext ω; simp
  rw [hfun]
  refine (eLpNorm_sum_le (fun i _ => ((hε.measurable (u i)).const_mul (c i)).aestronglyMeasurable)
    one_le_two).trans ?_
  have hterm : ∀ i, eLpNorm (fun ω => c i * ε (u i) ω) 2 μ
      = ENNReal.ofReal |c i| * ENNReal.ofReal (Real.sqrt σ2) := by
    intro i
    have : (fun ω => c i * ε (u i) ω) = c i • (ε (u i)) := by funext ω; simp
    rw [this, eLpNorm_const_smul, eLpNorm_noise_eq hε]
    congr 1
    simp [Real.enorm_eq_ofReal_abs]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]

end Aux

private lemma cov_noise_lin_eq_zero [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (hX : IsLinearProcessOf ψ X ε μ) (hε : IsWhiteNoise ε σ2 μ) (hmX : ∀ t, MemLp (X t) 2 μ)
    {u : ℤ} (hu : 0 < u) : cov[ε u, X 0; μ] = 0 := by
  have hcov : cov[ε u, X 0; μ] = ∫ ω, ε u ω * X 0 ω ∂μ := by
    have h := covariance_eq_sub (hε.memLp u) (hmX 0)
    rw [hε.integral_eq_zero u, zero_mul, sub_zero] at h
    have h2 : μ[ε u * X 0] = ∫ ω, ε u ω * X 0 ω ∂μ := by simp [Pi.mul_apply]
    rw [h2] at h
    exact h
  rw [hcov]
  -- the partial sums pair to zero
  have hmemP : ∀ N : ℕ, MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) 2 μ :=
    fun N => memLp_finset_sum _ fun j _ => (hε.memLp _).const_mul _
  have hzero : ∀ N : ℕ,
      ∫ ω, ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ = 0 := by
    intro N
    have hexp : ∀ ω, ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω)
        = ∑ j ∈ Finset.range N, ψ j * (ε u ω * ε (0 - (j : ℕ)) ω) := by
      intro ω; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ j : ℕ, Integrable (fun ω => ψ j * (ε u ω * ε (0 - (j : ℕ)) ω)) μ := fun j =>
      ((hε.memLp u).integrable_mul (hε.memLp (0 - (j : ℕ)))).const_mul (ψ j)
    simp_rw [hexp]
    rw [integral_finset_sum _ fun j _ => hint j]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul, integral_noise_mul_eq_zero hε (by omega), mul_zero]
  -- the pairing with the defect tends to zero
  have hsplit : ∀ N : ℕ, ∫ ω, ε u ω * X 0 ω ∂μ
      = ∫ ω, ε u ω * (X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ := by
    intro N
    have hint1 : Integrable (fun ω => ε u ω * X 0 ω) μ := (hε.memLp u).integrable_mul (hmX 0)
    have hint2 : Integrable
        (fun ω => ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω)) μ :=
      (hε.memLp u).integrable_mul (hmemP N)
    have : ∫ ω, ε u ω * X 0 ω ∂μ
        - ∫ ω, ε u ω * (∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ
        = ∫ ω, ε u ω * (X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) ∂μ := by
      rw [← integral_sub hint1 hint2]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [← this, hzero N, sub_zero]
  have hbd : ∀ N : ℕ, |∫ ω, ε u ω * X 0 ω ∂μ|
      ≤ (eLpNorm (ε u) 2 μ).toReal
        * (eLpNorm (fun ω => X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) 2 μ).toReal := by
    intro N
    rw [hsplit N]
    exact abs_integral_mul_le (hε.memLp u) ((hmX 0).sub (hmemP N))
  have hlim : Tendsto (fun N : ℕ => (eLpNorm (ε u) 2 μ).toReal
      * (eLpNorm (fun ω => X 0 ω - ∑ j ∈ Finset.range N, ψ j * ε (0 - (j : ℕ)) ω) 2 μ).toReal)
      atTop (𝓝 0) := by
    have h := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hX 0)
    simpa using h.const_mul ((eLpNorm (ε u) 2 μ).toReal)
  have habs : |∫ ω, ε u ω * X 0 ω ∂μ| ≤ 0 := by
    refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbd
  exact abs_eq_zero.1 (le_antisymm habs (abs_nonneg _))

/-- Covariance only sees the a.e. class of each argument. -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIX : ∫ x, X x ∂μ = ∫ x, X' x ∂μ := integral_congr_ae hX
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  simp only [covariance, hIX, hIY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2 using by rw [h1, h2])

private lemma coeff_arPoly_succ {p : ℕ} (b : Fin p → ℝ) (i : Fin p) :
    (arPoly b).coeff ((i : ℕ) + 1) = -(b i) := by
  rw [coeff_arPoly]
  simp [Fin.val_eq_val, Finset.sum_ite_eq]

private lemma coeff_maPoly_succ {q : ℕ} (a : Fin q → ℝ) (j : Fin q) :
    (maPoly a).coeff ((j : ℕ) + 1) = a j := by
  rw [coeff_maPoly]
  simp [Fin.val_eq_val, Finset.sum_ite_eq]

private lemma coeff_maPoly_eq_zero {q : ℕ} (a : Fin q → ℝ) {m : ℕ} (hm : q < m) :
    (maPoly a).coeff m = 0 := by
  rw [coeff_maPoly, if_neg (by omega), zero_add]
  exact Finset.sum_eq_zero fun j _ => if_neg (by have := j.isLt; omega)

/-- The AR polynomial as a lag operator on an arbitrary sequence. -/
private lemma arPoly_apply {p : ℕ} (b : Fin p → ℝ) (G : ℕ → ℝ) :
    ∑ k ∈ Finset.range (p + 1), (arPoly b).coeff k * G k
      = G 0 - ∑ i : Fin p, b i * G ((i : ℕ) + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (arPoly b).coeff k * G k) (p + 1), Fin.sum_univ_succ]
  have h0 : (arPoly b).coeff ((0 : Fin (p + 1)) : ℕ) * G ((0 : Fin (p + 1)) : ℕ) = G 0 := by
    simp [coeff_arPoly_zero]
  have hs : ∀ i : Fin p, (arPoly b).coeff ((i.succ : Fin (p + 1)) : ℕ) * G ((i.succ : Fin (p+1)) : ℕ)
      = -(b i * G ((i : ℕ) + 1)) := by
    intro i
    simp only [Fin.val_succ]
    rw [coeff_arPoly_succ]
    ring
  rw [h0, Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_neg_distrib]
  ring

/-- The MA polynomial as a lag operator on an arbitrary sequence. -/
private lemma maPoly_apply {q : ℕ} (a : Fin q → ℝ) (G : ℕ → ℝ) :
    ∑ m ∈ Finset.range (q + 1), (maPoly a).coeff m * G m
      = G 0 + ∑ j : Fin q, a j * G ((j : ℕ) + 1) := by
  rw [← Fin.sum_univ_eq_sum_range (fun m => (maPoly a).coeff m * G m) (q + 1), Fin.sum_univ_succ]
  have h0 : (maPoly a).coeff ((0 : Fin (q + 1)) : ℕ) * G ((0 : Fin (q + 1)) : ℕ) = G 0 := by
    simp [coeff_maPoly_zero]
  have hs : ∀ j : Fin q, (maPoly a).coeff ((j.succ : Fin (q + 1)) : ℕ) * G ((j.succ : Fin (q+1)) : ℕ)
      = a j * G ((j : ℕ) + 1) := by
    intro j
    simp only [Fin.val_succ]
    rw [coeff_maPoly_succ]
  rw [h0, Finset.sum_congr rfl (fun j _ => hs j)]

/-- The convolution identity with the AR sum truncated at the AR order. -/
private lemma conv_range {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (p + 1),
        (if k ≤ m then (arPoly b).coeff k * armaPsi b a (m - k) else 0)
      = (maPoly a).coeff m := by
  classical
  obtain ⟨N, hNp, hNm⟩ : ∃ N : ℕ, p ≤ N ∧ m ≤ N := ⟨max p m, le_max_left _ _, le_max_right _ _⟩
  have hcz : ∀ k, p < k → (arPoly b).coeff k = 0 := by
    intro k hk
    rw [coeff_arPoly, if_neg (by omega), zero_sub, neg_eq_zero]
    exact Finset.sum_eq_zero fun i _ => if_neg (by have := i.isLt; omega)
  have e1 : ∑ k ∈ Finset.range (p + 1),
        (if k ≤ m then (arPoly b).coeff k * armaPsi b a (m - k) else 0)
      = ∑ k ∈ Finset.range (N + 1),
        (if k ≤ m then (arPoly b).coeff k * armaPsi b a (m - k) else 0) := by
    have hsub : Finset.range (p + 1) ⊆ Finset.range (N + 1) := by
      intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    refine Finset.sum_subset hsub fun k _ hk => ?_
    simp only [Finset.mem_range, not_lt] at hk
    rw [hcz k (by omega)]
    simp
  have e2 : ∑ k ∈ Finset.range (m + 1), (arPoly b).coeff k * armaPsi b a (m - k)
      = ∑ k ∈ Finset.range (N + 1),
        (if k ≤ m then (arPoly b).coeff k * armaPsi b a (m - k) else 0) := by
    have hsub : Finset.range (m + 1) ⊆ Finset.range (N + 1) := by
      intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    rw [← Finset.sum_subset hsub (fun k _ hk => by
      simp only [Finset.mem_range, not_lt] at hk
      rw [if_neg (by omega)])]
    exact Finset.sum_congr rfl fun k hk => by
      simp only [Finset.mem_range] at hk
      rw [if_pos (by omega)]
  rw [e1, ← e2, arPoly_conv_armaPsi]

/-- A range sum minus its head is the tail chunk. -/
private lemma chunk (F : ℕ → ℝ) (N k : ℕ) :
    ∑ l ∈ Finset.range N, F l - ∑ l ∈ Finset.range (N - k), F l
      = ∑ l ∈ Finset.Ico (N - k) N, F l := by
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive F (Nat.zero_le (N - k)) (Nat.sub_le N k)]
  rw [Finset.range_eq_Ico]
  ring

omit [MeasurableSpace Ω] in
/-- The AR filter applied to the partial sums differs from the truncated MA combination
only by the `p` boundary chunks. -/
private lemma UV_diff {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ)
    (ω : Ω) :
    (∑ k ∈ Finset.range (p + 1), (arPoly b).coeff k *
        ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - (k : ℕ) - (l : ℕ)) ω)
      - ∑ m ∈ Finset.range N, (maPoly a).coeff m * ε (t - (m : ℕ)) ω
      = ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.Ico (N - k) N,
          ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω := by
  classical
  have hV : ∑ m ∈ Finset.range N, (maPoly a).coeff m * ε (t - (m : ℕ)) ω
      = ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (N - k),
          ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω := by
    have step1 : ∀ m : ℕ, (maPoly a).coeff m * ε (t - (m : ℕ)) ω
        = ∑ k ∈ Finset.range (p + 1),
            (if k ≤ m then ((arPoly b).coeff k * armaPsi b a (m - k)) * ε (t - (m : ℕ)) ω
              else 0) := by
      intro m
      rw [← conv_range b a m, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by split <;> simp
    rw [Finset.sum_congr rfl (fun m _ => step1 m), Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hfil : (Finset.range N).filter (fun m => k ≤ m) = Finset.Ico k N := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [← Finset.sum_filter, hfil, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h1 : k + l - k = l := by omega
    have h2 : t - ((k + l : ℕ) : ℤ) = t - (k : ℕ) - (l : ℕ) := by push_cast; ring
    rw [h1, h2]
  rw [hV, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← chunk (fun l => (arPoly b).coeff k * armaPsi b a l
    * ε (t - (k : ℕ) - (l : ℕ)) ω) N k]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring



/-- The `L²` norm of a finite scalar combination. -/
private lemma eLpNorm_const_mul_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Ω → ℝ)
    (hf : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    eLpNorm (fun ω => ∑ i ∈ s, c i * f i ω) 2 μ
      ≤ ∑ i ∈ s, ENNReal.ofReal |c i| * eLpNorm (f i) 2 μ := by
  have hfun : (fun ω => ∑ i ∈ s, c i * f i ω) = ∑ i ∈ s, fun ω => c i * f i ω := by
    funext ω; simp
  rw [hfun]
  refine (eLpNorm_sum_le (fun i hi => ((hf i hi).const_mul (c i))) one_le_two).trans
    (Finset.sum_le_sum fun i _ => ?_)
  have hsm : (fun ω => c i * f i ω) = c i • f i := rfl
  rw [hsm, eLpNorm_const_smul]
  exact mul_le_mul_left (le_of_eq (by simp [Real.enorm_eq_ofReal_abs])) _

/-- Two `L²`-limits of the same sequence agree a.e. -/
private lemma ae_eq_of_tendsto {f g : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hFm : ∀ N, AEStronglyMeasurable (F N) μ)
    (hf : Tendsto (fun N => eLpNorm (fun ω => f ω - F N ω) 2 μ) atTop (𝓝 0))
    (hg : Tendsto (fun N => eLpNorm (fun ω => g ω - F N ω) 2 μ) atTop (𝓝 0)) :
    f =ᵐ[μ] g := by
  have hle : ∀ N, eLpNorm (fun ω => f ω - g ω) 2 μ
      ≤ eLpNorm (fun ω => f ω - F N ω) 2 μ + eLpNorm (fun ω => F N ω - g ω) 2 μ := by
    intro N
    have hfun : (fun ω => f ω - g ω)
        = (fun ω => f ω - F N ω) + (fun ω => F N ω - g ω) := by funext ω; simp
    rw [hfun]
    exact eLpNorm_add_le (hfm.sub (hFm N)) ((hFm N).sub hgm) one_le_two
  have hlim : Tendsto (fun N => eLpNorm (fun ω => f ω - F N ω) 2 μ
      + eLpNorm (fun ω => F N ω - g ω) 2 μ) atTop (𝓝 0) := by
    have hcomm : ∀ N, eLpNorm (fun ω => F N ω - g ω) 2 μ
        = eLpNorm (fun ω => g ω - F N ω) 2 μ := by
      intro N
      rw [show (fun ω => F N ω - g ω) = -(fun ω => g ω - F N ω) by funext ω; simp, eLpNorm_neg]
    simp only [hcomm]
    simpa using hf.add hg
  have hzero : eLpNorm (fun ω => f ω - g ω) 2 μ = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hle)) (zero_le)
  have hae := (eLpNorm_eq_zero_iff (hfm.sub hgm) (by norm_num)).1 hzero
  filter_upwards [hae] with ω hω
  have : f ω - g ω = 0 := hω
  linarith

/-- **Causality** (FY §2.1.2, Definition 2.3): `X` is a causal function of the noise `ε`
when it is an MA(∞) over `ε` with absolutely summable coefficients. -/
def IsCausalFor (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ ψ : ℕ → ℝ, (Summable fun n => |ψ n|) ∧ IsLinearProcessOf ψ X ε μ

/-- **FY Theorem 2.1 (existence of a stationary causal ARMA solution)**: with no roots
of `b` in the closed unit disc and white noise `ε`, the linear process with the transfer
coefficients is a stationary, causal solution of the ARMA(p, q) equation. -/
theorem exists_stationary_arma [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: no roots of b(z) in the closed unit disc; FY §2.1.2 Thm 2.1
    (hb : NoRootClosedDisc b)
    -- USER-INPUT: white-noise innovations; FY eq. (2.3)
    (hε : IsWhiteNoise ε σ2 μ) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧
      IsLinearProcessOf (armaPsi b a) X ε μ ∧ IsARMA b a σ2 X ε μ ∧
      IsStationary X μ ∧ IsCausalFor X ε μ := by
  classical
  have hψ := summable_abs_armaPsi a hb
  obtain ⟨X, hXm, hXlin⟩ := exists_isLinearProcessOf hψ hε
  have hmX : ∀ c, MemLp (X c) 2 μ := hXlin.memLp hψ hε hXm
  refine ⟨X, hXm, hXlin, ⟨hXm, hε, ?_⟩, (hXlin.isStationary hψ hε hXm).1,
    ⟨armaPsi b a, hψ, hXlin⟩⟩
  intro t
  have hmemPS : ∀ (c : ℤ) (N : ℕ),
      MemLp (fun ω => ∑ l ∈ Finset.range N, armaPsi b a l * ε (c - (l : ℕ)) ω) 2 μ :=
    fun c N => memLp_finset_sum _ fun l _ => (hε.memLp _).const_mul _
  -- the tail of the coefficient series
  obtain ⟨Tail, hTail⟩ : ∃ T : ℕ → ℝ, T = fun N => ∑ l ∈ Finset.Ico (N - p) N, |armaPsi b a l| :=
    ⟨_, rfl⟩
  have hTailnn : ∀ N, 0 ≤ Tail N := by
    intro N; rw [hTail]; exact Finset.sum_nonneg fun l _ => abs_nonneg _
  have hTail0 : Tendsto Tail atTop (𝓝 0) := by
    have hsub : Tendsto (fun N : ℕ => N - p) atTop atTop :=
      tendsto_atTop_atTop.2 fun c => ⟨c + p, fun n hn => by omega⟩
    have hbig : Tendsto (fun n : ℕ => ∑' k : ℕ, |armaPsi b a (k + n)|) atTop (𝓝 0) :=
      tendsto_sum_nat_add fun l => |armaPsi b a l|
    refine squeeze_zero hTailnn (fun N => ?_) (hbig.comp hsub)
    rw [hTail]
    simp only [Function.comp_apply]
    rw [Finset.sum_Ico_eq_sum_range]
    refine (Finset.sum_le_sum (fun i _ =>
      le_of_eq (by rw [Nat.add_comm] :
        |armaPsi b a (N - p + i)| = |armaPsi b a (i + (N - p))|))).trans ?_
    exact ((summable_nat_add_iff (N - p)).2 hψ).sum_le_tsum _ (fun i _ => abs_nonneg _)
  -- the AR coefficient mass
  obtain ⟨Cb, hCb⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.range (p + 1), |(arPoly b).coeff k| := ⟨_, rfl⟩
  -- the `L²` bound on the boundary defect
  have hdiffbd : ∀ N : ℕ,
      eLpNorm (fun ω => ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.Ico (N - k) N,
        ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω) 2 μ
      ≤ ENNReal.ofReal (Cb * Tail N) * ENNReal.ofReal (Real.sqrt σ2) := by
    intro N
    have hfun : (fun ω => ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.Ico (N - k) N,
        ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω)
        = ∑ k ∈ Finset.range (p + 1), fun ω => ∑ l ∈ Finset.Ico (N - k) N,
            ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω := by
      funext ω; simp
    rw [hfun]
    refine (eLpNorm_sum_le (fun k _ => (memLp_finset_sum _ fun l _ =>
      (hε.memLp _).const_mul _).aestronglyMeasurable) one_le_two).trans ?_
    have hk : ∀ k ∈ Finset.range (p + 1),
        eLpNorm (fun ω => ∑ l ∈ Finset.Ico (N - k) N,
          ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω) 2 μ
        ≤ ENNReal.ofReal (|(arPoly b).coeff k| * Tail N) * ENNReal.ofReal (Real.sqrt σ2) := by
      intro k hkmem
      simp only [Finset.mem_range] at hkmem
      refine (eLpNorm_noise_comb_le hε (Finset.Ico (N - k) N)
        (fun l => (arPoly b).coeff k * armaPsi b a l)
        (fun l => t - (k : ℕ) - (l : ℕ))).trans ?_
      refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
      have hs : ∑ l ∈ Finset.Ico (N - k) N, |(arPoly b).coeff k * armaPsi b a l|
          = |(arPoly b).coeff k| * ∑ l ∈ Finset.Ico (N - k) N, |armaPsi b a l| := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => abs_mul _ _
      rw [hs, hTail]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun l _ _ => abs_nonneg _)
      intro l hl
      simp only [Finset.mem_Ico] at hl ⊢
      omega
    refine (Finset.sum_le_sum hk).trans ?_
    rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
      (fun k _ => mul_nonneg (abs_nonneg _) (hTailnn N)), ← Finset.sum_mul, ← hCb]
  -- the `L²` bound on the head defect
  have hAbd : ∀ N : ℕ,
      eLpNorm (fun ω => ∑ i : Fin p, b i * (X (t - 1 - (i : ℕ)) ω
        - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω)) 2 μ
      ≤ ∑ i : Fin p, ENNReal.ofReal |b i| *
          eLpNorm (fun ω => X (t - 1 - (i : ℕ)) ω
            - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω) 2 μ :=
    fun N => eLpNorm_const_mul_sum_le Finset.univ b
      (fun i => fun ω => X (t - 1 - (i : ℕ)) ω
        - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω)
      (fun i _ => ((hmX _).sub (hmemPS (t - 1 - (i : ℕ)) N)).aestronglyMeasurable)
  -- the pointwise decomposition of the defect
  have hpt : ∀ N : ℕ, q + 1 ≤ N → ∀ ω : Ω,
      ((∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω) + ε t ω
          + ∑ j : Fin q, a j * ε (t - 1 - (j : ℕ)) ω)
        - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - (l : ℕ)) ω
      = (∑ i : Fin p, b i * (X (t - 1 - (i : ℕ)) ω
          - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω))
        - ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.Ico (N - k) N,
            ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω := by
    intro N hN ω
    have hU : ∑ k ∈ Finset.range (p + 1), (arPoly b).coeff k *
          ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - (k : ℕ) - (l : ℕ)) ω
        = (∑ l ∈ Finset.range N, armaPsi b a l * ε (t - (l : ℕ)) ω)
          - ∑ i : Fin p, b i *
              ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω := by
      rw [arPoly_apply b
        (fun k => ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - (k : ℕ) - (l : ℕ)) ω)]
      congr 1
      · exact Finset.sum_congr rfl fun l _ => by norm_num
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        congr 2
        push_cast
        ring
    have hV : ∑ m ∈ Finset.range N, (maPoly a).coeff m * ε (t - (m : ℕ)) ω
        = ε t ω + ∑ j : Fin q, a j * ε (t - 1 - (j : ℕ)) ω := by
      have h1 : ∑ m ∈ Finset.range N, (maPoly a).coeff m * ε (t - (m : ℕ)) ω
          = ∑ m ∈ Finset.range (q + 1), (maPoly a).coeff m * ε (t - (m : ℕ)) ω := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro m hm; simp only [Finset.mem_range] at hm ⊢; omega
        · intro m _ hm
          simp only [Finset.mem_range, not_lt] at hm
          rw [coeff_maPoly_eq_zero a (by omega), zero_mul]
      rw [h1, maPoly_apply a (fun m => ε (t - (m : ℕ)) ω)]
      congr 1
      · norm_num
      · refine Finset.sum_congr rfl fun j _ => ?_
        congr 2
        push_cast
        ring
    have hexp : (∑ i : Fin p, b i * (X (t - 1 - (i : ℕ)) ω
          - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω))
        = (∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω)
          - ∑ i : Fin p, b i *
              ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdiff := UV_diff b a ε t N ω
    rw [hexp]
    linarith
  -- the bounding sequence
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ≥0∞, D = fun N =>
      (∑ i : Fin p, ENNReal.ofReal |b i| *
        eLpNorm (fun ω => X (t - 1 - (i : ℕ)) ω
          - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω) 2 μ)
      + ENNReal.ofReal (Cb * Tail N) * ENNReal.ofReal (Real.sqrt σ2) := ⟨_, rfl⟩
  have hD0 : Tendsto D atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => ∑ i : Fin p, ENNReal.ofReal |b i| *
        eLpNorm (fun ω => X (t - 1 - (i : ℕ)) ω
          - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω) 2 μ)
        atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin p))
        (fun (i : Fin p) (_ : i ∈ Finset.univ) =>
          ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |b i|)
            (hXlin (t - 1 - (i : ℕ))) (Or.inr ENNReal.ofReal_ne_top))
      simpa using this
    have h2 : Tendsto (fun N => ENNReal.ofReal (Cb * Tail N) * ENNReal.ofReal (Real.sqrt σ2))
        atTop (𝓝 0) := by
      have hr : Tendsto (fun N => ENNReal.ofReal (Cb * Tail N)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (hTail0.const_mul Cb)
        simpa using this
      have := ENNReal.Tendsto.mul_const (b := ENNReal.ofReal (Real.sqrt σ2)) hr
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using this
    rw [hD]
    simpa using h1.add h2
  -- the RHS is in `L²`
  have hmemR : MemLp (fun ω => (∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω) + ε t ω
      + ∑ j : Fin q, a j * ε (t - 1 - (j : ℕ)) ω) 2 μ :=
    ((memLp_finset_sum _ fun i _ => (hmX _).const_mul _).add (hε.memLp t)).add
      (memLp_finset_sum _ fun j _ => (hε.memLp _).const_mul _)
  refine ae_eq_of_tendsto (hmX t).aestronglyMeasurable hmemR.aestronglyMeasurable
    (fun N => (hmemPS t N).aestronglyMeasurable) (hXlin t) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD0
    (Eventually.of_forall fun N => zero_le) ?_
  filter_upwards [eventually_ge_atTop (q + 1)] with N hN
  have hfeq : (fun ω => ((∑ i : Fin p, b i * X (t - 1 - (i : ℕ)) ω) + ε t ω
        + ∑ j : Fin q, a j * ε (t - 1 - (j : ℕ)) ω)
      - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - (l : ℕ)) ω)
      = (fun ω => ∑ i : Fin p, b i * (X (t - 1 - (i : ℕ)) ω
          - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω))
        - (fun ω => ∑ k ∈ Finset.range (p + 1), ∑ l ∈ Finset.Ico (N - k) N,
            ((arPoly b).coeff k * armaPsi b a l) * ε (t - (k : ℕ) - (l : ℕ)) ω) :=
    funext (hpt N hN)
  rw [hfeq, hD]
  refine (eLpNorm_sub_le ?_ ?_ one_le_two).trans (add_le_add (hAbd N) (hdiffbd N))
  · have hm : MemLp (fun ω => ∑ i : Fin p, b i * (X (t - 1 - (i : ℕ)) ω
        - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω)) 2 μ := by
      refine memLp_finset_sum _ fun i _ => ?_
      have h1 : MemLp (fun ω => X (t - 1 - (i : ℕ)) ω
          - ∑ l ∈ Finset.range N, armaPsi b a l * ε (t - 1 - (i : ℕ) - (l : ℕ)) ω) 2 μ :=
        (hmX _).sub (hmemPS (t - 1 - (i : ℕ)) N)
      exact h1.const_mul _
    exact hm.aestronglyMeasurable
  · exact (memLp_finset_sum _ fun k _ =>
      memLp_finset_sum _ fun l _ => (hε.memLp _).const_mul _).aestronglyMeasurable


/-- **Yule–Walker recurrences** (FY §2.2.1, eq. (2.21)): for a causal stationary ARMA
process and lags beyond the MA order, `γ(k) = Σᵢ bᵢ γ(k−1−i)`. -/
theorem IsARMA.acvf_yule_walker [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    -- USER-INPUT: causality (FY: eq. (2.21) is derived for the causal solution); FY §2.2.1
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hb : NoRootClosedDisc b)
    {k : ℤ}
    -- USER-INPUT: lag beyond the MA order; FY eq. (2.21)
    (hk : (q : ℤ) < k) :
    acvf X μ k = ∑ i : Fin p, b i * acvf X μ (k - 1 - (i : ℕ)) := by
  have hψ := summable_abs_armaPsi a hb
  have hmX : ∀ t, MemLp (X t) 2 μ := hcausal.memLp hψ h.whiteNoise h.measurableX
  have hmε : ∀ t, MemLp (ε t) 2 μ := h.whiteNoise.memLp
  have hcovε : ∀ u : ℤ, 0 < u → cov[ε u, X 0; μ] = 0 :=
    fun u hu => cov_noise_lin_eq_zero hcausal h.whiteNoise hmX hu
  have hmem1 : MemLp (fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω) 2 μ :=
    memLp_finset_sum _ fun i _ => (hmX _).const_mul _
  have hmem3 : MemLp (fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω) 2 μ :=
    memLp_finset_sum _ fun j _ => (hmε _).const_mul _
  have hstep : cov[X k, X 0; μ]
      = cov[fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω, X 0; μ] + cov[ε k, X 0; μ]
        + cov[fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω, X 0; μ] := by
    rw [covariance_congr_ae (h.recurrence k) (EventuallyEq.refl _ (X 0))]
    have hfun : (fun ω => (∑ i, b i * X (k - 1 - (i : ℕ)) ω) + ε k ω
        + ∑ j, a j * ε (k - 1 - (j : ℕ)) ω)
        = ((fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω) + ε k)
          + (fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω) := rfl
    rw [hfun, covariance_add_left (hmem1.add (hmε k)) hmem3 (hmX 0),
      covariance_add_left hmem1 (hmε k) (hmX 0)]
  have hz1 : cov[ε k, X 0; μ] = 0 := hcovε k (by omega)
  have hz2 : cov[fun ω => ∑ j, a j * ε (k - 1 - (j : ℕ)) ω, X 0; μ] = 0 := by
    rw [covariance_fun_sum_left (fun j => (hmε _).const_mul _) (hmX 0)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [covariance_const_mul_left, hcovε _ (by have := j.isLt; omega), mul_zero]
  have hb1 : cov[fun ω => ∑ i, b i * X (k - 1 - (i : ℕ)) ω, X 0; μ]
      = ∑ i : Fin p, b i * acvf X μ (k - 1 - (i : ℕ)) := by
    rw [covariance_fun_sum_left (fun i => (hmX _).const_mul _) (hmX 0)]
    exact Finset.sum_congr rfl fun i _ => by rw [covariance_const_mul_left]; rfl
  rw [show acvf X μ k = cov[X k, X 0; μ] from rfl, hstep, hz1, hz2, hb1]
  ring


/-- **Proposition 2.2(i)** (FY §2.2.1): the ACVF of a causal stationary ARMA process
decays exponentially. (Proved from the geometric `ψ`-bound — no distinct-roots caveat.) -/
theorem IsARMA.acvf_exponential_decay [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hb : NoRootClosedDisc b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ k : ℤ, |acvf X μ k| ≤ C * r ^ k.natAbs := by
  obtain ⟨C, hC, r, hr0, hr1, hbnd⟩ := exists_geometric_bound_armaPsi a hb
  have hψ := summable_abs_armaPsi a hb
  have hform := (hcausal.isStationary hψ h.whiteNoise h.measurableX).2
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hr2' : (0:ℝ) ≤ r ^ 2 := by positivity
  have hden : (0:ℝ) < 1 - r ^ 2 := by linarith
  refine ⟨|σ2| * C ^ 2 * (1 - r ^ 2)⁻¹, by positivity, r, hr0, hr1, fun k => ?_⟩
  set m := k.natAbs with hm
  have hle : ∀ j : ℕ, |armaPsi b a j * armaPsi b a (j + m)| ≤ C ^ 2 * r ^ m * (r ^ 2) ^ j := by
    intro j
    rw [abs_mul]
    have h1 : |armaPsi b a j| * |armaPsi b a (j + m)| ≤ (C * r ^ j) * (C * r ^ (j + m)) :=
      mul_le_mul (hbnd j) (hbnd (j + m)) (abs_nonneg _) (by positivity)
    refine h1.trans_eq ?_
    have hpow : (r ^ 2) ^ j = (r ^ j) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [pow_add, hpow]
    ring
  have hmaj : Summable fun j : ℕ => C ^ 2 * r ^ m * (r ^ 2) ^ j :=
    (summable_geometric_of_lt_one hr2' hr2).mul_left _
  have hsum : Summable fun j : ℕ => |armaPsi b a j * armaPsi b a (j + m)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hle hmaj
  have habs : |∑' j : ℕ, armaPsi b a j * armaPsi b a (j + m)|
      ≤ ∑' j : ℕ, |armaPsi b a j * armaPsi b a (j + m)| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := fun j : ℕ => armaPsi b a j * armaPsi b a (j + m))
        (by simpa only [Real.norm_eq_abs] using hsum)
  have hmajsum : ∑' j : ℕ, |armaPsi b a j * armaPsi b a (j + m)|
      ≤ C ^ 2 * r ^ m * (1 - r ^ 2)⁻¹ := by
    refine (hsum.tsum_le_tsum hle hmaj).trans_eq ?_
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr2' hr2]
  rw [hform k, abs_mul, ← hm]
  calc |σ2| * |∑' j : ℕ, armaPsi b a j * armaPsi b a (j + m)|
      ≤ |σ2| * (C ^ 2 * r ^ m * (1 - r ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (habs.trans hmajsum) (abs_nonneg _)
    _ = |σ2| * C ^ 2 * (1 - r ^ 2)⁻¹ * r ^ m := by ring


section Homogeneous

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A bounded two-sided sequence contracted along a fixed shift by a factor of norm `< 1`
vanishes identically. -/
private lemma eq_zero_of_geom (u : ℤ → V) (M : ℝ) (hbd : ∀ t, ‖u t‖ ≤ M) (β : ℂ)
    (hβ : ‖β‖ < 1) (c : ℤ) (heq : ∀ t, u t = β • u (t + c)) (t : ℤ) : u t = 0 := by
  have hpow : ∀ (n : ℕ) (s : ℤ), u s = β ^ n • u (s + (n : ℤ) * c) := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ n ih =>
        intro s
        rw [heq s, ih (s + c), smul_smul, ← pow_succ']
        congr 2
        push_cast
        ring
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbd t)
  have hle : ∀ n : ℕ, ‖u t‖ ≤ ‖β‖ ^ n * M := by
    intro n
    rw [hpow n t, norm_smul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hbd _) (by positivity)
  have hlim : Tendsto (fun n : ℕ => ‖β‖ ^ n * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg β) hβ).mul_const M
  have hz : ‖u t‖ ≤ 0 := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  exact norm_le_zero_iff.1 hz

/-- The one-step homogeneous recursion `u_t = α u_{t-1}` with `‖α‖ ≠ 1` kills every
bounded two-sided solution. -/
private lemma eq_zero_of_shift (u : ℤ → V) (M : ℝ) (hbd : ∀ t, ‖u t‖ ≤ M) (α : ℂ)
    (hα : ‖α‖ ≠ 1) (heq : ∀ t, u t = α • u (t - 1)) (t : ℤ) : u t = 0 := by
  rcases lt_or_gt_of_ne hα with hlt | hgt
  · refine eq_zero_of_geom u M hbd α hlt (-1) (fun s => ?_) t
    simpa [sub_eq_add_neg] using heq s
  · have hpos : (0 : ℝ) < ‖α‖ := lt_trans zero_lt_one hgt
    have hα0 : α ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hpos
      exact lt_irrefl _ hpos
    refine eq_zero_of_geom u M hbd α⁻¹ ?_ 1 (fun s => ?_) t
    · rw [norm_inv]
      have hmul : ‖α‖⁻¹ * ‖α‖ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
      nlinarith [inv_pos.2 hpos]
    · have hs := heq (s + 1)
      rw [add_sub_cancel_right] at hs
      rw [hs, smul_smul, inv_mul_cancel₀ hα0, one_smul]

end Homogeneous

/-- A non-constant complex polynomial with constant coefficient `1` splits off a factor
`1 - α X` with `α ≠ 0` and `α⁻¹` a root. -/
private lemma exists_linear_factor (Q : Polynomial ℂ) (h0 : Q.coeff 0 = 1)
    (hd : 0 < Q.natDegree) :
    ∃ (α : ℂ) (R : Polynomial ℂ), α ≠ 0 ∧ Q.eval α⁻¹ = 0 ∧ R.coeff 0 = 1 ∧
      R.natDegree < Q.natDegree ∧ Q = (1 - Polynomial.C α * Polynomial.X) * R := by
  classical
  obtain ⟨z, hz⟩ := Complex.exists_root (f := Q) (Polynomial.natDegree_pos_iff_degree_pos.1 hd)
  have hev : Q.eval z = 0 := hz
  have hz0 : z ≠ 0 := by
    intro hzz
    rw [hzz, ← Polynomial.coeff_zero_eq_eval_zero, h0] at hev
    exact one_ne_zero hev
  obtain ⟨S, hS⟩ := Polynomial.dvd_iff_isRoot.2 hz
  have hfac : (1 - Polynomial.C z⁻¹ * Polynomial.X) * Polynomial.C (-z)
      = Polynomial.X - Polynomial.C z := by
    have hz1 : z⁻¹ * (-z) = -1 := by field_simp
    calc (1 - Polynomial.C z⁻¹ * Polynomial.X) * Polynomial.C (-z)
        = Polynomial.C (-z) - (Polynomial.C z⁻¹ * Polynomial.C (-z)) * Polynomial.X := by ring
      _ = Polynomial.C (-z) - Polynomial.C (z⁻¹ * (-z)) * Polynomial.X := by
          rw [← Polynomial.C_mul]
      _ = Polynomial.C (-z) - Polynomial.C (-1 : ℂ) * Polynomial.X := by rw [hz1]
      _ = Polynomial.X - Polynomial.C z := by simp; ring
  have hQ : Q = (1 - Polynomial.C z⁻¹ * Polynomial.X) * (Polynomial.C (-z) * S) := by
    rw [← mul_assoc, hfac, hS]
  have hlin0 : (1 - Polynomial.C z⁻¹ * Polynomial.X).coeff 0 = 1 := by simp
  have hR0 : (Polynomial.C (-z) * S).coeff 0 = 1 := by
    have hcg := congrArg (fun P : Polynomial ℂ => P.coeff 0) hQ
    simp only [Polynomial.mul_coeff_zero, hlin0, one_mul] at hcg
    rw [Polynomial.mul_coeff_zero, ← hcg, h0]
  refine ⟨z⁻¹, Polynomial.C (-z) * S, inv_ne_zero hz0, by rw [inv_inv]; exact hev, hR0, ?_, hQ⟩
  have hRne : Polynomial.C (-z) * S ≠ 0 := by
    intro hzero
    rw [hzero] at hR0
    simp at hR0
  have hdeg1 : (1 - Polynomial.C z⁻¹ * Polynomial.X).natDegree = 1 := by
    have h1 : (Polynomial.C z⁻¹ * Polynomial.X).natDegree = 1 :=
      Polynomial.natDegree_C_mul_X _ (inv_ne_zero hz0)
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by simp [h1]), h1]
  have hlinne : (1 - Polynomial.C z⁻¹ * Polynomial.X) ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg1
    simp at hdeg1
  have := Polynomial.natDegree_mul hlinne hRne
  rw [← hQ, hdeg1] at this
  omega

/-- **The homogeneous ARMA equation has only the zero bounded solution** when the AR
polynomial has no roots on the unit circle: repeated splitting of the AR polynomial into
linear factors `1 - αX` with `‖α‖ ≠ 1`. -/
private lemma seq_eq_zero_of_poly {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] :
    ∀ (n : ℕ) (Q : Polynomial ℂ) (u : ℤ → V) (M : ℝ), Q.coeff 0 = 1 → Q.natDegree ≤ n →
      (∀ z : ℂ, Q.eval z = 0 → ‖z‖ ≠ 1) → (∀ t, ‖u t‖ ≤ M) →
      (∀ t : ℤ, ∑ k ∈ Finset.range (n + 1), Q.coeff k • u (t - (k : ℕ)) = 0) →
      ∀ t, u t = 0 := by
  intro n
  induction n with
  | zero =>
      intro Q u M h0 _ _ _ heq t
      have h := heq t
      simpa [h0] using h
  | succ n ih =>
      intro Q u M h0 hdeg hroot hbd heq t
      rcases Nat.eq_zero_or_pos Q.natDegree with hd | hd
      · have h := heq t
        rw [Finset.sum_eq_single 0] at h
        · simpa [h0] using h
        · intro k _ hk
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_smul]
        · intro hmem
          exact absurd (Finset.mem_range.2 (by omega)) hmem
      · obtain ⟨α, R, hα0, hrootα, hR0, hRdeg, hQ⟩ := exists_linear_factor Q h0 hd
        have hcoefS : ∀ k : ℕ, Q.coeff (k + 1) = R.coeff (k + 1) - α * R.coeff k := by
          intro k
          rw [hQ, sub_mul, one_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul,
            Polynomial.coeff_X_mul]
        have hcoef0 : Q.coeff 0 = R.coeff 0 := by rw [h0, hR0]
        have hRn : R.coeff (n + 1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        set Y : ℤ → V := fun s => ∑ k ∈ Finset.range (n + 1), R.coeff k • u (s - (k : ℕ))
          with hYdef
        have hstep : ∀ s : ℤ, Y s = α • Y (s - 1) := by
          intro s
          have h := heq s
          rw [Finset.sum_range_succ'] at h
          have e1 : ∀ k ∈ Finset.range (n + 1),
              Q.coeff (k + 1) • u (s - ((k + 1 : ℕ) : ℤ))
                = R.coeff (k + 1) • u (s - ((k + 1 : ℕ) : ℤ))
                  - α • (R.coeff k • u (s - 1 - (k : ℕ))) := by
            intro k _
            rw [hcoefS k, sub_smul, smul_smul]
            congr 3
            push_cast
            ring
          rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.smul_sum, hcoef0] at h
          have e2 : (∑ k ∈ Finset.range (n + 1), R.coeff (k + 1) • u (s - ((k + 1 : ℕ) : ℤ)))
              + R.coeff 0 • u (s - ((0 : ℕ) : ℤ)) = Y s := by
            rw [← Finset.sum_range_succ' (fun k => R.coeff k • u (s - (k : ℕ))) (n + 1),
              Finset.sum_range_succ, hRn, zero_smul, add_zero]
          have hzero : Y s - α • Y (s - 1) = 0 := by
            calc Y s - α • Y (s - 1)
                = ((∑ k ∈ Finset.range (n + 1), R.coeff (k + 1) • u (s - ((k + 1 : ℕ) : ℤ)))
                    - α • Y (s - 1)) + R.coeff 0 • u (s - ((0 : ℕ) : ℤ)) := by
                  rw [← e2]; abel
              _ = 0 := h
          exact sub_eq_zero.1 hzero
        have hYbd : ∀ s : ℤ, ‖Y s‖ ≤ ∑ k ∈ Finset.range (n + 1), ‖R.coeff k‖ * |M| := by
          intro s
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left ((hbd _).trans (le_abs_self M)) (norm_nonneg _)
        have hαne : ‖α‖ ≠ 1 := by
          intro hone
          refine hroot α⁻¹ hrootα ?_
          rw [norm_inv, hone, inv_one]
        have hY0 : ∀ s, Y s = 0 :=
          eq_zero_of_shift Y _ hYbd α hαne hstep
        refine ih R u M hR0 (by omega) (fun z hz => ?_) hbd (fun s => hY0 s) t
        refine hroot z ?_
        rw [hQ, Polynomial.eval_mul, hz, mul_zero]


section CausalityConverse

/-! ### The converse half of FY §2.1.2 (i): causality forces `b(z) ≠ 0` on `|z| ≤ 1`

The route is the `1/b(B)`-filter one recorded at `arma_causal_of_stationary_debt`, run in
the reverse direction: pairing the ARMA recurrence with the noise turns the *stochastic*
identity into the **deterministic** convolution `b ∗ ψ = a` on the causal transfer
coefficients (`conv_of_causal`), after which the transfer function `Ψ(z) = Σ ψ_n z^n` —
which converges on the *closed* disc because `Σ|ψ_n| < ∞` — factors `a = b · Ψ` there.  A
root of `b` in the closed disc is then a common root of `b` and `a`, which coprimality
forbids. -/

/-- The mixed second moment of white noise, both cases at once: `E[ε_u ε_v] = σ² δ_{uv}`. -/
private lemma integral_noise_mul_eq [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hε : IsWhiteNoise ε σ2 μ) (u v : ℤ) :
    ∫ ω, ε u ω * ε v ω ∂μ = if u = v then σ2 else 0 := by
  rcases eq_or_ne u v with rfl | huv
  · rw [if_pos rfl]
    have h := covariance_eq_sub (hε.memLp u) (hε.memLp u)
    rw [hε.integral_eq_zero u, zero_mul, sub_zero,
      covariance_self (hε.memLp u).aestronglyMeasurable.aemeasurable, hε.variance_eq u] at h
    have h2 : μ[ε u * ε u] = ∫ ω, ε u ω * ε u ω ∂μ := by simp [Pi.mul_apply]
    rw [h2] at h
    exact h.symm
  · rw [if_neg huv]
    exact integral_noise_mul_eq_zero hε huv

/-- **The cross moment of a causal linear process with its noise**: `E[X_t ε_s] = σ² ψ_{t−s}`
for `s ≤ t`, and `0` for `s > t` (the noise is orthogonal to the strict past of the
filter).  Both cases come from the *same* computation on the partial sums, which is why
they are bundled: only the matched index survives, and the `L²` defect is killed by
Cauchy–Schwarz. -/
private lemma integral_lin_mul_noise [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hlin : IsLinearProcessOf ψ X ε μ) (hε : IsWhiteNoise ε σ2 μ)
    (hmX : ∀ t, MemLp (X t) 2 μ) (t s : ℤ) :
    ∫ ω, X t ω * ε s ω ∂μ = if s ≤ t then σ2 * ψ (t - s).toNat else 0 := by
  classical
  set R : ℝ := if s ≤ t then σ2 * ψ (t - s).toNat else 0 with hR
  have hmemP : ∀ N : ℕ, MemLp (fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ :=
    fun N => memLp_finset_sum _ fun j _ => (hε.memLp _).const_mul _
  -- the partial sums pair to `R` exactly, as soon as the window reaches the lag
  have hpsum : ∀ N : ℕ, (t - s).toNat < N →
      ∫ ω, (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) * ε s ω ∂μ = R := by
    intro N hN
    have hexp : ∀ ω, (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) * ε s ω
        = ∑ j ∈ Finset.range N, ψ j * (ε (t - (j : ℕ)) ω * ε s ω) := by
      intro ω; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    have hint : ∀ j : ℕ, Integrable (fun ω => ψ j * (ε (t - (j : ℕ)) ω * ε s ω)) μ := fun j =>
      ((hε.memLp _).integrable_mul (hε.memLp s)).const_mul _
    simp_rw [hexp]
    rw [integral_finset_sum _ fun j _ => hint j]
    have hterm : ∀ j : ℕ, ∫ ω, ψ j * (ε (t - (j : ℕ)) ω * ε s ω) ∂μ
        = if t - (j : ℤ) = s then σ2 * ψ j else 0 := by
      intro j
      rw [integral_const_mul, integral_noise_mul_eq hε]
      by_cases hj : t - (j : ℤ) = s
      · rw [if_pos hj, if_pos hj]; ring
      · rw [if_neg hj, if_neg hj]; ring
    simp_rw [hterm]
    by_cases hst : s ≤ t
    · rw [hR, if_pos hst]
      refine Finset.sum_eq_single (t - s).toNat (fun j _ hj => if_neg (by omega))
        (fun hnot => absurd (Finset.mem_range.2 hN) hnot) |>.trans ?_
      exact if_pos (by omega)
    · rw [hR, if_neg hst]
      exact Finset.sum_eq_zero fun j _ => if_neg (by omega)
  -- the residual pairing is bounded by the `L²` defect
  have hsplit : ∀ N : ℕ, (t - s).toNat < N →
      ∫ ω, X t ω * ε s ω ∂μ - R
        = ∫ ω, (X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) * ε s ω ∂μ := by
    intro N hN
    have hint1 : Integrable (fun ω => X t ω * ε s ω) μ := (hmX t).integrable_mul (hε.memLp s)
    have hint2 : Integrable
        (fun ω => (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) * ε s ω) μ :=
      (hmemP N).integrable_mul (hε.memLp s)
    rw [← hpsum N hN, ← integral_sub hint1 hint2]
    exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have hbd : ∀ N : ℕ, (t - s).toNat < N → |∫ ω, X t ω * ε s ω ∂μ - R|
      ≤ (eLpNorm (fun ω => X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ).toReal
        * (eLpNorm (ε s) 2 μ).toReal := by
    intro N hN
    rw [hsplit N hN]
    exact abs_integral_mul_le ((hmX t).sub (hmemP N)) (hε.memLp s)
  have hlim : Tendsto (fun N : ℕ =>
      (eLpNorm (fun ω => X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ).toReal
        * (eLpNorm (ε s) 2 μ).toReal) atTop (𝓝 0) := by
    have hc := (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hlin t)
    simpa using hc.mul_const ((eLpNorm (ε s) 2 μ).toReal)
  have habs : |∫ ω, X t ω * ε s ω ∂μ - R| ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [eventually_gt_atTop (t - s).toNat] with N hN using hbd N hN
  have := abs_eq_zero.1 (le_antisymm habs (abs_nonneg _))
  linarith

/-- **The causal transfer coefficients satisfy the ARMA convolution** `b ∗ ψ = a`.

This is the deterministic shadow of the recurrence: pair `X_0 = Σ b_i X_{−1−i} + ε_0 +
Σ a_j ε_{−1−j}` with `ε_{−n}` and use `integral_lin_mul_noise` on each term.  The white
noise's orthogonality collapses every noise pairing to a Kronecker delta and every process
pairing to `σ² ψ`, and `σ² > 0` cancels. -/
private lemma conv_of_causal [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} {ψ : ℕ → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hσ : 0 < σ2) (hψ : Summable fun n => |ψ n|)
    (hlin : IsLinearProcessOf ψ X ε μ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (arPoly b).coeff k * ψ (n - k) = (maPoly a).coeff n := by
  classical
  have hmX : ∀ t, MemLp (X t) 2 μ := hlin.memLp hψ h.whiteNoise h.measurableX
  have hε := h.whiteNoise
  set s : ℤ := -(n : ℤ) with hs
  -- ## The stochastic identity, paired with `ε_{−n}`
  have hleft : ∫ ω, X 0 ω * ε s ω ∂μ = σ2 * ψ n := by
    rw [integral_lin_mul_noise hlin hε hmX 0 s, if_pos (by omega)]
    congr 2
    omega
  have hXi : ∀ i : Fin p, ∫ ω, X (0 - 1 - (i : ℕ)) ω * ε s ω ∂μ
      = if (i : ℕ) + 1 ≤ n then σ2 * ψ (n - 1 - (i : ℕ)) else 0 := by
    intro i
    rw [integral_lin_mul_noise hlin hε hmX _ s]
    by_cases hi : (i : ℕ) + 1 ≤ n
    · rw [if_pos (by omega), if_pos hi]
      congr 2
      omega
    · rw [if_neg (by omega), if_neg hi]
  have hε0 : ∫ ω, ε 0 ω * ε s ω ∂μ = if n = 0 then σ2 else 0 := by
    rw [integral_noise_mul_eq hε]
    by_cases hn : n = 0
    · rw [if_pos (by omega), if_pos hn]
    · rw [if_neg (by omega), if_neg hn]
  have hεj : ∀ j : Fin q, ∫ ω, ε (0 - 1 - (j : ℕ)) ω * ε s ω ∂μ
      = if n = (j : ℕ) + 1 then σ2 else 0 := by
    intro j
    rw [integral_noise_mul_eq hε]
    by_cases hj : n = (j : ℕ) + 1
    · rw [if_pos (by omega), if_pos hj]
    · rw [if_neg (by omega), if_neg hj]
  -- expand the recurrence under the integral sign
  have hint1 : Integrable (fun ω => X 0 ω * ε s ω) μ := (hmX 0).integrable_mul (hε.memLp s)
  have hexpand : ∫ ω, X 0 ω * ε s ω ∂μ
      = (∑ i : Fin p, b i * ∫ ω, X (0 - 1 - (i : ℕ)) ω * ε s ω ∂μ)
        + (∫ ω, ε 0 ω * ε s ω ∂μ)
        + ∑ j : Fin q, a j * ∫ ω, ε (0 - 1 - (j : ℕ)) ω * ε s ω ∂μ := by
    have hae : (fun ω => X 0 ω * ε s ω) =ᵐ[μ] fun ω =>
        (∑ i : Fin p, b i * (X (0 - 1 - (i : ℕ)) ω * ε s ω)) + (ε 0 ω * ε s ω)
          + ∑ j : Fin q, a j * (ε (0 - 1 - (j : ℕ)) ω * ε s ω) := by
      filter_upwards [h.recurrence 0] with ω hω
      rw [hω]
      simp only [add_mul, Finset.sum_mul, mul_assoc]
    rw [integral_congr_ae hae]
    have hI1 : ∀ i : Fin p, Integrable (fun ω => b i * (X (0 - 1 - (i : ℕ)) ω * ε s ω)) μ :=
      fun i => ((hmX _).integrable_mul (hε.memLp s)).const_mul _
    have hI2 : Integrable (fun ω => ε 0 ω * ε s ω) μ := (hε.memLp 0).integrable_mul (hε.memLp s)
    have hI3 : ∀ j : Fin q, Integrable (fun ω => a j * (ε (0 - 1 - (j : ℕ)) ω * ε s ω)) μ :=
      fun j => ((hε.memLp _).integrable_mul (hε.memLp s)).const_mul _
    have hS1 : Integrable (fun ω => ∑ i : Fin p, b i * (X (0 - 1 - (i : ℕ)) ω * ε s ω)) μ :=
      integrable_finset_sum _ fun i _ => hI1 i
    have hS3 : Integrable (fun ω => ∑ j : Fin q, a j * (ε (0 - 1 - (j : ℕ)) ω * ε s ω)) μ :=
      integrable_finset_sum _ fun j _ => hI3 j
    have hS12 : Integrable (fun ω =>
        (∑ i : Fin p, b i * (X (0 - 1 - (i : ℕ)) ω * ε s ω)) + ε 0 ω * ε s ω) μ := hS1.add hI2
    rw [integral_add hS12 hS3, integral_add hS1 hI2,
      integral_finset_sum _ fun i _ => hI1 i, integral_finset_sum _ fun j _ => hI3 j]
    simp_rw [integral_const_mul]
  -- ## Divide by `σ² > 0`
  rw [hleft] at hexpand
  simp_rw [hXi, hε0, hεj] at hexpand
  have hkey : ψ n = (∑ i : Fin p, if (i : ℕ) + 1 ≤ n then b i * ψ (n - 1 - (i : ℕ)) else 0)
      + (if n = 0 then (1 : ℝ) else 0) + ∑ j : Fin q, if n = (j : ℕ) + 1 then a j else 0 := by
    refine mul_left_cancel₀ (ne_of_gt hσ) ?_
    rw [hexpand]
    have e1 : ∀ i : Fin p, b i * (if (i : ℕ) + 1 ≤ n then σ2 * ψ (n - 1 - (i : ℕ)) else 0)
        = σ2 * (if (i : ℕ) + 1 ≤ n then b i * ψ (n - 1 - (i : ℕ)) else 0) := by
      intro i; split_ifs <;> ring
    have e2 : (if n = 0 then σ2 else 0) = σ2 * (if n = 0 then (1 : ℝ) else 0) := by
      split_ifs <;> ring
    have e3 : ∀ j : Fin q, a j * (if n = (j : ℕ) + 1 then σ2 else 0)
        = σ2 * (if n = (j : ℕ) + 1 then a j else 0) := by
      intro j; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_congr rfl (fun j _ => e3 j), e2,
      ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← mul_add]
  -- ## The algebraic identity relating the convolution to the coefficient shape
  have hAR : ∑ k ∈ Finset.range (n + 1), (arPoly b).coeff k * ψ (n - k)
      = ψ n - ∑ i : Fin p, if (i : ℕ) + 1 ≤ n then b i * ψ (n - 1 - (i : ℕ)) else 0 := by
    have hexp : ∀ k ∈ Finset.range (n + 1), (arPoly b).coeff k * ψ (n - k)
        = (if k = 0 then ψ (n - k) else 0)
          - ∑ i : Fin p, (if k = (i : ℕ) + 1 then b i * ψ (n - k) else 0) := by
      intro k _
      rw [coeff_arPoly, sub_mul, Finset.sum_mul]
      congr 1
      · split_ifs <;> ring
      · exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1
    · rw [Finset.sum_eq_single 0 (fun k _ hk => if_neg hk)
        (fun hnot => absurd (Finset.mem_range.2 (Nat.succ_pos n)) hnot), if_pos rfl]
      rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_ite_eq' (Finset.range (n + 1)) ((i : ℕ) + 1)
        (fun k => b i * ψ (n - k))]
      by_cases hi : (i : ℕ) + 1 ≤ n
      · rw [if_pos (Finset.mem_range.2 (by omega)), if_pos hi]
        congr 2
        omega
      · rw [if_neg (by simp only [Finset.mem_range]; omega), if_neg hi]
  have hMA : (maPoly a).coeff n
      = (if n = 0 then (1 : ℝ) else 0) + ∑ j : Fin q, if n = (j : ℕ) + 1 then a j else 0 :=
    coeff_maPoly a n
  rw [hAR, hMA, hkey]
  ring

end CausalityConverse

/-- **FY §2.1.2 cited fact (i) (Brockwell & Davis 1996, p. 83), converse half**: for an
ARMA process with a stationary causal solution and **coprime** AR/MA polynomials, `b` has
no roots in the closed unit disc.  The ⇐ half is `exists_stationary_arma`.

**Statement repair (wave `ts/f1-arma-finale`, 2026-08-09).** The frozen form — without
`hcop` — is FALSE, as recorded by wave `ts/s7`: take `p = q = 1`, `b = ![1]`, `a = ![-1]`,
i.e. `b(z) = 1 − z = a(z)`, whose common root is `z = 1`.  The recurrence
`X_t = X_{t−1} + ε_t − ε_{t−1}` is solved exactly by `X = ε`, which is stationary and
causal (`ψ = δ₀`, so `IsCausalFor X ε μ` holds) for *any* white noise, including one with
`σ² > 0`; yet `aeval 1 (arPoly ![1]) = 0` with `‖(1 : ℂ)‖ ≤ 1`, so `NoRootClosedDisc ![1]`
fails.  The repair is exactly Brockwell & Davis's standing assumption for their Thm 3.1.1,
"`φ(z)` and `θ(z)` have no common zeroes", tagged `USER-INPUT` below; with it the recorded
`1/b(B)`-filter route goes through, and it is what is proved here.

**The route, as executed.** Causality gives `ψ` with `Σ|ψ_n| < ∞` and `X_t = Σ ψ_n ε_{t−n}`
in `L²`.  Pairing the recurrence with `ε_{−n}` and using orthogonality of the innovations
(`integral_lin_mul_noise`) turns the stochastic identity into the deterministic convolution
`Σ_{k≤n} b_k ψ_{n−k} = a_n` (`conv_of_causal`) — this is where `σ² > 0` is used, to cancel
the common factor.  Absolute summability makes `Ψ(z) = Σ ψ_n z^n` converge on the *closed*
disc, and the Cauchy product (`hasSum_poly_mul`) upgrades the convolution to
`a(z) = b(z) Ψ(z)` for every `‖z‖ ≤ 1`.  A root of `b` there is therefore a root of `a`,
i.e. a common root — which `hcop` forbids by evaluating a Bézout identity.

Note `hstat` is not used: causality (with `σ² > 0`) already carries the whole argument, the
`L²` limit defining `ψ` being all that the pairing needs.  It is kept because it is the
form in which the book states the equivalence. -/
theorem arma_causal_of_stationary_debt [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    (hσ : 0 < σ2)
    -- USER-INPUT: `b(z)` and `a(z)` have no common zero (B&D's standing assumption for
    -- Thm 3.1.1); without it the statement is FALSE — see the docstring's witness
    (hcop : IsCoprime (arPoly b) (maPoly a))
    (hcausal : IsCausalFor X ε μ) :
    NoRootClosedDisc b := by
  classical
  obtain ⟨ψ, hψ, hlin⟩ := hcausal
  intro z hz hzero
  -- ## The transfer function converges on the closed disc
  have hsummable : Summable fun n : ℕ => (ψ n : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded (g := fun n => |ψ n|) hψ fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc |ψ n| * ‖z‖ ^ n ≤ |ψ n| * 1 ^ n := by gcongr
      _ = |ψ n| := by ring
  set S : ℂ := ∑' n : ℕ, (ψ n : ℂ) * z ^ n with hSdef
  have hS : HasSum (fun n : ℕ => (ψ n : ℂ) * z ^ n) S := hsummable.hasSum
  -- ## `b ∗ ψ = a`, upgraded to `a(z) = b(z) Ψ(z)` by the Cauchy product
  have hconv := conv_of_causal h hσ hψ hlin
  have hmul := hasSum_poly_mul ((arPoly b).map (algebraMap ℝ ℂ)) hS
  have hcoeffs : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1),
          ((arPoly b).map (algebraMap ℝ ℂ)).coeff k * (ψ (n - k) : ℂ))
        = ((maPoly a).map (algebraMap ℝ ℂ)).coeff n := by
    intro n
    have hpush : (∑ k ∈ Finset.range (n + 1),
        ((arPoly b).map (algebraMap ℝ ℂ)).coeff k * (ψ (n - k) : ℂ))
        = ((∑ k ∈ Finset.range (n + 1), (arPoly b).coeff k * ψ (n - k) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun k _ => by
        rw [Polynomial.coeff_map]
        norm_num
    rw [hpush, hconv n, Polynomial.coeff_map]
    norm_num
  simp_rw [hcoeffs] at hmul
  have hpoly := hasSum_poly ((maPoly a).map (algebraMap ℝ ℂ)) z
  have hmaeval : ((maPoly a).map (algebraMap ℝ ℂ)).eval z
      = ((arPoly b).map (algebraMap ℝ ℂ)).eval z * S := hpoly.unique hmul
  -- ## A root of `b` in the disc is a common root, contradicting coprimality
  have hbz : ((arPoly b).map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hzero
  have haz : Polynomial.aeval z (maPoly a) = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmaeval, hbz, zero_mul]
  obtain ⟨u, v, huv⟩ := hcop
  have := congrArg (fun P : Polynomial ℝ => Polynomial.aeval z P) huv
  simp only [map_add, map_mul, map_one] at this
  rw [hzero, haz, mul_zero, mul_zero, add_zero] at this
  exact zero_ne_one this

/-- **DEBT (Brockwell & Davis 1996, p. 82; FY §2.1.2 cited fact (ii))**: uniqueness of
the stationary solution when `b` has no roots on the unit circle: two stationary
solutions driven by the same noise agree a.e. at every time. -/
theorem arma_stationary_unique_debt [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X X' ε : ℤ → Ω → ℝ}
    -- USER-INPUT: no roots of b(z) on the unit circle; FY §2.1.2 cited fact (ii)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → Polynomial.aeval z (arPoly b) ≠ 0)
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    (h' : IsARMA b a σ2 X' ε μ) (hstat' : IsStationary X' μ) (t : ℤ) :
    X t =ᵐ[μ] X' t := by
  classical
  -- the difference process, in complex `L²`
  have hmemD : ∀ s : ℤ, MemLp (fun ω => X s ω - X' s ω) 2 μ :=
    fun s => (hstat.memLp s).sub (hstat'.memLp s)
  have hmemC : ∀ s : ℤ, MemLp (fun ω => ((X s ω - X' s ω : ℝ) : ℂ)) 2 μ :=
    fun s => (hmemD s).ofReal
  set u : ℤ → Lp ℂ 2 μ := fun s => (hmemC s).toLp _ with hudef
  -- uniform second moments from stationarity
  have hmom : ∀ (Z : ℤ → Ω → ℝ), IsStationary Z μ → ∀ s : ℤ,
      ∫ ω, Z s ω * Z s ω ∂μ = ∫ ω, Z 0 ω * Z 0 ω ∂μ := by
    intro Z hZ s
    have e1 := covariance_eq_sub (hZ.memLp s) (hZ.memLp s)
    have e2 := covariance_eq_sub (hZ.memLp 0) (hZ.memLp 0)
    have hcov : cov[Z s, Z s; μ] = cov[Z 0, Z 0; μ] := by
      have hh := hZ.cov_shift s 0
      rwa [add_zero] at hh
    have hint : ∫ ω, Z s ω ∂μ = ∫ ω, Z 0 ω ∂μ := hZ.integral_eq s 0
    have hp1 : μ[Z s * Z s] = ∫ ω, Z s ω * Z s ω ∂μ := by simp [Pi.mul_apply]
    have hp2 : μ[Z 0 * Z 0] = ∫ ω, Z 0 ω * Z 0 ω ∂μ := by simp [Pi.mul_apply]
    rw [hp1, hint] at e1
    rw [hp2] at e2
    rw [hcov, e2] at e1
    linarith
  have hnormZ : ∀ (Z : ℤ → Ω → ℝ) (hZ : IsStationary Z μ) (s : ℤ),
      ‖(hZ.memLp s).toLp (Z s)‖ = ‖(hZ.memLp 0).toLp (Z 0)‖ := by
    intro Z hZ s
    have hs : ‖(hZ.memLp s).toLp (Z s)‖ ^ 2 = ∫ ω, Z s ω * Z s ω ∂μ := by
      rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have h0 : ‖(hZ.memLp 0).toLp (Z 0)‖ ^ 2 = ∫ ω, Z 0 ω * Z 0 ω ∂μ := by
      rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have := hmom Z hZ s
    rw [← hs, ← h0] at this
    nlinarith [norm_nonneg ((hZ.memLp s).toLp (Z s)), norm_nonneg ((hZ.memLp 0).toLp (Z 0))]
  -- hence the complex difference is bounded in `L²`
  have hbd : ∀ s : ℤ, ‖u s‖
      ≤ ‖(hstat.memLp 0).toLp (X 0)‖ + ‖(hstat'.memLp 0).toLp (X' 0)‖ := by
    intro s
    have hnorm : ‖u s‖ = (eLpNorm (fun ω => X s ω - X' s ω) 2 μ).toReal := by
      rw [hudef, Lp.norm_toLp]
      congr 1
      refine eLpNorm_congr_norm_ae (Eventually.of_forall fun ω => ?_)
      rw [Complex.norm_real]
    have hsub : eLpNorm (fun ω => X s ω - X' s ω) 2 μ
        ≤ eLpNorm (X s) 2 μ + eLpNorm (X' s) 2 μ :=
      eLpNorm_sub_le (hstat.memLp s).aestronglyMeasurable
        (hstat'.memLp s).aestronglyMeasurable one_le_two
    have hfin : eLpNorm (X s) 2 μ + eLpNorm (X' s) 2 μ ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨(hstat.memLp s).2.ne, (hstat'.memLp s).2.ne⟩
    rw [hnorm]
    calc (eLpNorm (fun ω => X s ω - X' s ω) 2 μ).toReal
        ≤ (eLpNorm (X s) 2 μ + eLpNorm (X' s) 2 μ).toReal :=
          ENNReal.toReal_mono hfin hsub
      _ = (eLpNorm (X s) 2 μ).toReal + (eLpNorm (X' s) 2 μ).toReal :=
          ENNReal.toReal_add (hstat.memLp s).2.ne (hstat'.memLp s).2.ne
      _ = ‖(hstat.memLp s).toLp (X s)‖ + ‖(hstat'.memLp s).toLp (X' s)‖ := by
          rw [Lp.norm_toLp, Lp.norm_toLp]
      _ = ‖(hstat.memLp 0).toLp (X 0)‖ + ‖(hstat'.memLp 0).toLp (X' 0)‖ := by
          rw [hnormZ X hstat s, hnormZ X' hstat' s]
  -- the AR polynomial over ℂ
  set B : Polynomial ℂ := (arPoly b).map (algebraMap ℝ ℂ) with hBdef
  have hBc : ∀ k, B.coeff k = (((arPoly b).coeff k : ℝ) : ℂ) := by
    intro k; rw [hBdef, Polynomial.coeff_map]; simp
  have hcz : ∀ k, p < k → (arPoly b).coeff k = 0 := by
    intro k hk
    rw [arPoly, Polynomial.coeff_sub, Polynomial.coeff_one, if_neg (by omega),
      Polynomial.finset_sum_coeff]
    have : ∀ i : Fin p, (Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1)).coeff k = 0 := by
      intro i
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by have := i.isLt; omega),
        mul_zero]
    simp [this]
  have hB0 : B.coeff 0 = 1 := by
    rw [hBc 0]
    have : (arPoly b).coeff 0 = 1 := by
      rw [arPoly, Polynomial.coeff_sub, Polynomial.coeff_one, if_pos rfl,
        Polynomial.finset_sum_coeff]
      have : ∀ i : Fin p, (Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1)).coeff 0 = 0 := by
        intro i
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega), mul_zero]
      simp [this]
    rw [this]; norm_num
  have hBdeg : B.natDegree ≤ p := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun k hk => ?_
    rw [hBc k, hcz k (by exact_mod_cast hk)]
    norm_num
  have hBroot : ∀ z : ℂ, B.eval z = 0 → ‖z‖ ≠ 1 := by
    intro z hz hnorm
    refine hb z hnorm ?_
    rw [hBdef, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at *
    exact hz
  -- the homogeneous equation in `L²`
  have hcoeFnSum : ∀ (s : ℤ),
      ⇑(∑ k ∈ Finset.range (p + 1), B.coeff k • u (s - (k : ℕ)))
        =ᵐ[μ] fun ω => ∑ k ∈ Finset.range (p + 1), B.coeff k * (u (s - (k : ℕ)) : Ω → ℂ) ω := by
    intro s
    induction (p + 1) with
    | zero => simpa using! Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)
    | succ m ihm =>
        rw [Finset.sum_range_succ]
        filter_upwards [Lp.coeFn_add (∑ k ∈ Finset.range m, B.coeff k • u (s - (k : ℕ)))
          (B.coeff m • u (s - (m : ℕ))), ihm,
          Lp.coeFn_smul (B.coeff m) (u (s - (m : ℕ)))] with ω e1 e2 e3
        rw [e1]
        simp only [Pi.add_apply, e2, e3, Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ]
  have heq : ∀ s : ℤ, ∑ k ∈ Finset.range (p + 1), B.coeff k • u (s - (k : ℕ)) = 0 := by
    intro s
    refine Lp.ext ?_
    filter_upwards [hcoeFnSum s, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ),
      h.recurrence s, h'.recurrence s,
      ae_all_iff.2 (fun k : Fin (p + 1) => (hmemC (s - (k : ℕ))).coeFn_toLp)] with
      ω hsum hzero hrec hrec' hcoe
    rw [hsum, hzero]
    have hD : ∀ k : ℕ, k < p + 1 → (u (s - (k : ℕ)) : Ω → ℂ) ω
        = ((X (s - (k : ℕ)) ω - X' (s - (k : ℕ)) ω : ℝ) : ℂ) := by
      intro k hk
      exact hcoe ⟨k, hk⟩
    have hreal : ∑ k ∈ Finset.range (p + 1),
        (arPoly b).coeff k * (X (s - (k : ℕ)) ω - X' (s - (k : ℕ)) ω) = 0 := by
      have hG := arPoly_apply b (fun k => X (s - (k : ℕ)) ω - X' (s - (k : ℕ)) ω)
      rw [hG]
      have hshift : ∀ i : Fin p,
          X (s - ((i : ℕ) + 1 : ℕ)) ω - X' (s - ((i : ℕ) + 1 : ℕ)) ω
            = X (s - 1 - (i : ℕ)) ω - X' (s - 1 - (i : ℕ)) ω := by
        intro i
        have hidx : (s - (((i : ℕ) + 1 : ℕ) : ℤ)) = s - 1 - ((i : ℕ) : ℤ) := by
          push_cast; ring
        rw [hidx]
      simp only [Nat.cast_zero, sub_zero]
      rw [Finset.sum_congr rfl (fun i _ => by rw [hshift i] : ∀ i ∈ Finset.univ,
        b i * (X (s - ((i : ℕ) + 1 : ℕ)) ω - X' (s - ((i : ℕ) + 1 : ℕ)) ω)
          = b i * (X (s - 1 - (i : ℕ)) ω - X' (s - 1 - (i : ℕ)) ω))]
      rw [hrec, hrec']
      have hexp : ∑ i : Fin p, b i * (X (s - 1 - (i : ℕ)) ω - X' (s - 1 - (i : ℕ)) ω)
          = (∑ i : Fin p, b i * X (s - 1 - (i : ℕ)) ω)
            - ∑ i : Fin p, b i * X' (s - 1 - (i : ℕ)) ω := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hexp]
      ring
    calc ∑ k ∈ Finset.range (p + 1), B.coeff k * (u (s - (k : ℕ)) : Ω → ℂ) ω
        = ∑ k ∈ Finset.range (p + 1),
            (((arPoly b).coeff k * (X (s - (k : ℕ)) ω - X' (s - (k : ℕ)) ω) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [hBc k, hD k (Finset.mem_range.1 hk)]
          push_cast
          ring
      _ = ((∑ k ∈ Finset.range (p + 1),
            ((arPoly b).coeff k * (X (s - (k : ℕ)) ω - X' (s - (k : ℕ)) ω)) : ℝ) : ℂ) := by
          push_cast
          ring
      _ = 0 := by rw [hreal]; norm_num
  -- conclude
  have hu0 : u t = 0 := seq_eq_zero_of_poly p B u _ hB0 hBdeg hBroot hbd heq t
  have hcoe := (hmemC t).coeFn_toLp
  have hzero := Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)
  have : (fun ω => ((X t ω - X' t ω : ℝ) : ℂ)) =ᵐ[μ] 0 := by
    filter_upwards [hcoe, hzero] with ω e1 e2
    have : (u t : Ω → ℂ) ω = 0 := by rw [hu0]; exact e2
    rw [← e1]
    exact this
  filter_upwards [this] with ω hω
  have : ((X t ω - X' t ω : ℝ) : ℂ) = 0 := hω
  have hr : X t ω - X' t ω = 0 := by exact_mod_cast this
  linarith

end StatLean.TimeSeries
