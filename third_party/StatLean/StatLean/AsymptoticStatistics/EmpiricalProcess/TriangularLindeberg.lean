module
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import StatLean.AsymptoticStatistics.ForMathlib.CramerWoldEuclidean
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF

@[expose] public section

/-!
# Row-iid triangular Lindeberg central limit theorem

This file develops the scalar and finite-dimensional row-iid triangular
Lindeberg theorem used for the marginal-convergence step of van der Vaart
Theorem 19.28.  Rows are specified by raw population functions; centering,
limiting variance nonnegativity, and infinitesimality are derived internally.

The theorem admits the degenerate cases `n = 0` and `σ2 = 0` and imposes no
Feller or cross-row identical-distribution hypothesis.

Reference: van der Vaart, *Asymptotic Statistics*, Proposition 2.27 as used in
Theorem 19.28, pp.282--283.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Real Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The population-centered scalar row associated with a raw triangular row.

Constitutive (vdV Proposition 2.27 and Theorem 19.28 pp.282--283): the
finite-dimensional triangular array is centered by its rowwise population
mean.  Edge behavior: if the mean is not integrable, Lean's Bochner integral
is totalized to zero; every theorem below assumes rowwise `L²`, so that
fallback is not reached there. -/
noncomputable def centeredScalarRow
    (P : Measure Ω) (g : ℕ → Ω → ℝ) (n : ℕ) (x : Ω) : ℝ :=
  g n x - ∫ y, g n y ∂P

/-- The population-centered Euclidean row associated with a raw triangular
row.

Constitutive (vdV Proposition 2.27 and Theorem 19.28 pp.282--283): finite
coordinate vectors are centered by their rowwise population mean.  Edge
behavior: for `k = 0` this is the unique zero vector; a nonintegrable mean is
totalized by the Bochner integral. The limit theorems assume rowwise `L²`. -/
noncomputable def centeredVectorRow {k : ℕ}
    (P : Measure Ω) (g : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    (n : ℕ) (x : Ω) : EuclideanSpace ℝ (Fin k) :=
  g n x - ∫ y, g n y ∂P

/-- The centered covariance matrix of a raw Euclidean triangular row.

Constitutive (vdV Theorem 19.28 pp.282--283): its `(i,j)` entry is the
population integral of the product of the two centered coordinates.  Edge
behavior: for `k = 0` this is the unique empty matrix; nonintegrable entries
use the totalized integral. The limit theorems assume rowwise `L²`. -/
noncomputable def centeredCovMatrix {k : ℕ}
    (P : Measure Ω) (g : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    (n : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => ∫ x, centeredVectorRow P g n x i * centeredVectorRow P g n x j ∂P

private noncomputable def quadraticExpRemainder (z : ℝ) : ℂ :=
  Complex.exp ((z : ℂ) * Complex.I) -
    (1 + (z : ℂ) * Complex.I + ((z : ℂ) * Complex.I) ^ 2 / 2)

private lemma norm_quadraticExpRemainder_le_cube {z : ℝ} (hz : |z| ≤ 1) :
    ‖quadraticExpRemainder z‖ ≤ |z| ^ 3 := by
  have hz' : ‖(z : ℂ) * Complex.I‖ ≤ 1 := by simpa using hz
  have h := Complex.exp_bound (x := (z : ℂ) * Complex.I) hz'
    (n := 3) (by norm_num)
  have hsum :
      ∑ m ∈ Finset.range 3, (((z : ℂ) * Complex.I) ^ m / m.factorial) =
        1 + (z : ℂ) * Complex.I + ((z : ℂ) * Complex.I) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  rw [quadraticExpRemainder, ← hsum]
  refine h.trans ?_
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs]
  norm_num
  nlinarith [pow_nonneg (abs_nonneg z) 3]

private lemma norm_quadraticExpRemainder_le_global (z : ℝ) :
    ‖quadraticExpRemainder z‖ ≤ 2 + |z| + z ^ 2 / 2 := by
  rw [quadraticExpRemainder]
  calc
    ‖Complex.exp ((z : ℂ) * Complex.I) -
        (1 + (z : ℂ) * Complex.I + ((z : ℂ) * Complex.I) ^ 2 / 2)‖
        ≤ ‖Complex.exp ((z : ℂ) * Complex.I)‖ +
          ‖1 + (z : ℂ) * Complex.I + ((z : ℂ) * Complex.I) ^ 2 / 2‖ :=
      norm_sub_le _ _
    _ ≤ 1 + (1 + |z| + z ^ 2 / 2) := by
      gcongr
      · simp [mul_comm]
      · calc
          ‖1 + (z : ℂ) * Complex.I + ((z : ℂ) * Complex.I) ^ 2 / 2‖
              ≤ ‖(1 : ℂ)‖ + ‖(z : ℂ) * Complex.I‖ +
                  ‖((z : ℂ) * Complex.I) ^ 2 / 2‖ := by
            exact (norm_add_le _ _).trans
                  (add_le_add (norm_add_le _ _) le_rfl)
          _ = 1 + |z| + z ^ 2 / 2 := by
            rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
              Real.norm_eq_abs, norm_div, norm_pow, Complex.norm_mul,
              Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
            norm_num [sq_abs]
    _ = 2 + |z| + z ^ 2 / 2 := by ring

private lemma norm_quadraticExpRemainder_le_mul_sq_of_delta_lt_abs
    {z δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hz : δ < |z|) :
    ‖quadraticExpRemainder z‖ ≤ 4 / δ ^ 2 * z ^ 2 := by
  refine (norm_quadraticExpRemainder_le_global z).trans ?_
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  rw [div_mul_eq_mul_div, le_div_iff₀ hδsq]
  have hzsq : z ^ 2 = |z| ^ 2 := by rw [sq_abs]
  rw [hzsq]
  have hδabs : δ ≤ |z| := hz.le
  have hδsq_le : δ ^ 2 ≤ |z| ^ 2 := by nlinarith [abs_nonneg z]
  have hδsq_one : δ ^ 2 ≤ 1 := by nlinarith
  have hmix : |z| * δ ^ 2 ≤ |z| ^ 2 := by
    nlinarith [mul_nonneg (abs_nonneg z) (sub_nonneg.2 hδsq_one)]
  nlinarith [abs_nonneg z]

private lemma charFun_sub_quadratic_eq_integral_quadraticExpRemainder
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hm : Measurable Y) (hmem : MemLp Y 2 P) (hmean : ∫ x, Y x ∂P = 0)
    (u : ℝ) :
    charFun (P.map Y) u -
      (1 - (((∫ x, Y x ^ 2 ∂P) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) =
      ∫ x, quadraticExpRemainder (u * Y x) ∂P := by
  have hYint : Integrable Y P := hmem.integrable (by norm_num)
  have hYsq : Integrable (fun x => Y x ^ 2) P := hmem.integrable_sq
  have hlin : Integrable (fun x => ((u * Y x : ℝ) : ℂ) * Complex.I) P := by
    convert hYint.ofReal.const_mul (u : ℂ) |>.mul_const Complex.I using 1
    ext x
    push_cast
    rfl
  have hquad : Integrable
      (fun x => (((u * Y x : ℝ) : ℂ) * Complex.I) ^ 2 / 2) P := by
    have hb : Integrable (fun x => (((u ^ 2 / 2) * Y x ^ 2 : ℝ) : ℂ)) P :=
      (hYsq.const_mul (u ^ 2 / 2)).ofReal
    exact hb.neg.congr (Eventually.of_forall fun x => by
      change -(((u ^ 2 / 2) * Y x ^ 2 : ℝ) : ℂ) =
        (((u * Y x : ℝ) : ℂ) * Complex.I) ^ 2 / 2
      push_cast
      rw [mul_pow, Complex.I_sq]
      ring)
  have hpoly : Integrable (fun x =>
      1 + ((u * Y x : ℝ) : ℂ) * Complex.I +
        (((u * Y x : ℝ) : ℂ) * Complex.I) ^ 2 / 2) P :=
    ((integrable_const (1 : ℂ)).add hlin).add hquad
  have hexp : Integrable
      (fun x => Complex.exp (((u * Y x : ℝ) : ℂ) * Complex.I)) P := by
    refine Integrable.mono' (f := fun x =>
      Complex.exp (((u * Y x : ℝ) : ℂ) * Complex.I))
      (g := fun _ : Ω => (1 : ℝ)) (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with x
    exact (Complex.norm_exp_ofReal_mul_I (u * Y x)).le
  have hOfReal : (∫ x, (Y x : ℂ) ∂P) = ((∫ x, Y x ∂P : ℝ) : ℂ) := integral_ofReal
  have hSqOfReal : (∫ x, ((Y x ^ 2 : ℝ) : ℂ) ∂P) =
      ((∫ x, Y x ^ 2 ∂P : ℝ) : ℂ) := integral_ofReal
  have hlinInt : ∫ x, ((u * Y x : ℝ) : ℂ) * Complex.I ∂P = 0 := by
    calc
      _ = ∫ x, (u : ℂ) * (Y x : ℂ) * Complex.I ∂P := by
        apply integral_congr_ae
        filter_upwards with x
        push_cast
        rfl
      _ = (∫ x, (u : ℂ) * (Y x : ℂ) ∂P) * Complex.I :=
        integral_mul_const Complex.I (fun x => (u : ℂ) * (Y x : ℂ))
      _ = ((u : ℂ) * (∫ x, (Y x : ℂ) ∂P)) * Complex.I := by
        exact congrArg (fun z : ℂ => z * Complex.I)
          (integral_const_mul (u : ℂ) (fun x => (Y x : ℂ)) (μ := P))
      _ = ((u : ℂ) * ((∫ x, Y x ∂P : ℝ) : ℂ)) * Complex.I := by
        rw [hOfReal]
      _ = 0 := by rw [hmean]; simp
  have hquadInt :
      ∫ x, (((u * Y x : ℝ) : ℂ) * Complex.I) ^ 2 / 2 ∂P =
        -(((∫ x, Y x ^ 2 ∂P : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
    calc
      _ = ∫ x, ((u : ℂ) ^ 2 * Complex.I ^ 2 / 2) *
          ((Y x ^ 2 : ℝ) : ℂ) ∂P := by
        apply integral_congr_ae
        filter_upwards with x
        push_cast
        rw [mul_pow]
        ring
      _ = ((u : ℂ) ^ 2 * Complex.I ^ 2 / 2) *
          (∫ x, ((Y x ^ 2 : ℝ) : ℂ) ∂P) :=
        integral_const_mul ((u : ℂ) ^ 2 * Complex.I ^ 2 / 2)
          (fun x => ((Y x ^ 2 : ℝ) : ℂ))
      _ = ((u : ℂ) ^ 2 * Complex.I ^ 2 / 2) * ↑(∫ x, Y x ^ 2 ∂P) := by
        rw [hSqOfReal]
      _ = _ := by rw [Complex.I_sq]; ring
  have hpolyInt : ∫ x, (1 + ((u * Y x : ℝ) : ℂ) * Complex.I +
      (((u * Y x : ℝ) : ℂ) * Complex.I) ^ 2 / 2) ∂P =
      1 - (((∫ x, Y x ^ 2 ∂P : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
    calc
      _ = (∫ x, (1 + ((u * Y x : ℝ) : ℂ) * Complex.I) ∂P) +
          ∫ x, (((u * Y x : ℝ) : ℂ) * Complex.I) ^ 2 / 2 ∂P := by
        exact integral_add ((integrable_const (1 : ℂ)).add hlin) hquad
      _ = ((∫ x, (1 : ℂ) ∂P) +
          ∫ x, ((u * Y x : ℝ) : ℂ) * Complex.I ∂P) +
          ∫ x, (((u * Y x : ℝ) : ℂ) * Complex.I) ^ 2 / 2 ∂P := by
        rw [integral_add (integrable_const (1 : ℂ)) hlin]
      _ = _ := by rw [integral_const, hlinInt, hquadInt]; simp [probReal_univ]; ring
  calc
    charFun (P.map Y) u -
        (1 - (((∫ x, Y x ^ 2 ∂P) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) =
        (∫ x, Complex.exp (((u * Y x : ℝ) : ℂ) * Complex.I) ∂P) -
          (1 - (((∫ x, Y x ^ 2 ∂P) : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
      rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
      congr 3
      funext x
      push_cast
      rfl
    _ = ∫ x, quadraticExpRemainder (u * Y x) ∂P := by
      simp only [quadraticExpRemainder]
      rw [integral_sub hexp hpoly, hpolyInt]

private lemma tendsto_nat_mul_integral_quadraticExpRemainder
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : ℕ → Ω → ℝ} {σ2 : ℝ}
    (hYmeas : ∀ n, Measurable (Y n)) (hYmem : ∀ n, MemLp (Y n) 2 P)
    (hvar : Tendsto (fun n => ∫ x, (Y n x) ^ 2 ∂P) atTop (nhds σ2))
    (hLin : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n : ℕ => ∫⁻ x in {ω | ε * Real.sqrt n < |Y n ω|},
        ENNReal.ofReal ((Y n x) ^ 2) ∂P) atTop (nhds 0)) (t : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ‖∫ x, quadraticExpRemainder ((Real.sqrt n)⁻¹ * t * Y n x) ∂P‖)
      atTop (nhds 0) := by
  by_cases ht : t = 0
  · subst t
    simp [quadraticExpRemainder]
  have hσ2 : 0 ≤ σ2 := ge_of_tendsto' hvar fun n =>
    integral_nonneg fun x => sq_nonneg (Y n x)
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  let K : ℝ := σ2 + 1
  have hK : 0 < K := by dsimp [K]; linarith
  let δ : ℝ := min 1 (η / (4 * (t ^ 2 * K + 1)))
  have hden : 0 < 4 * (t ^ 2 * K + 1) := by positivity
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hη hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδbudget : δ * t ^ 2 * K < η / 4 := by
    have hle := min_le_right (1 : ℝ) (η / (4 * (t ^ 2 * K + 1)))
    dsimp [δ] at hle ⊢
    have htK : 0 ≤ t ^ 2 * K := mul_nonneg (sq_nonneg t) hK.le
    have hmul := mul_le_mul_of_nonneg_right hle htK
    have hratio : η * (t ^ 2 * K) / (4 * (t ^ 2 * K + 1)) < η / 4 := by
      rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
      nlinarith
    rw [div_mul_eq_mul_div] at hmul
    exact lt_of_le_of_lt (by simpa [mul_assoc] using hmul) hratio
  let ε₀ : ℝ := δ / |t|
  have ht_abs : 0 < |t| := abs_pos.2 ht
  have hε₀ : 0 < ε₀ := div_pos hδ ht_abs
  let tail : ℕ → ℝ := fun n =>
    ∫ x in {x | ε₀ * Real.sqrt n < |Y n x|}, (Y n x) ^ 2 ∂P
  have htail : Tendsto tail atTop (nhds 0) := by
    have htailE := hLin ε₀ hε₀
    have hcomp := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htailE
    rw [ENNReal.toReal_zero] at hcomp
    apply hcomp.congr'
    exact Eventually.of_forall fun n => by
      rw [Function.comp_apply, ← ofReal_integral_eq_lintegral_ofReal
        ((hYmem n).integrable_sq.integrableOn)
        (Eventually.of_forall fun x => sq_nonneg (Y n x))]
      rw [ENNReal.toReal_ofReal]
      exact integral_nonneg fun x => sq_nonneg (Y n x)
  obtain ⟨Nv, hvK⟩ := Metric.tendsto_atTop.mp hvar 1 zero_lt_one
  let a : ℝ := η * δ ^ 2 / (16 * (t ^ 2 + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨Nt, htailSmall⟩ := Metric.tendsto_atTop.mp htail a ha
  refine ⟨max (max Nv Nt) 1, fun n hn => ?_⟩
  have hnV : Nv ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hnT : Nt ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hn : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hvn' := hvK n hnV
  rw [Real.dist_eq] at hvn'
  have hvn : (∫ x, (Y n x) ^ 2 ∂P) < K := by
    dsimp [K]
    linarith [le_abs_self ((∫ x, (Y n x) ^ 2 ∂P) - σ2)]
  have htn' := htailSmall n hnT
  have htn : tail n < a := by
    have htail_nn : 0 ≤ tail n := by
      dsimp [tail]
      exact integral_nonneg fun x => sq_nonneg (Y n x)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg htail_nn] at htn'
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  let u : ℝ := (Real.sqrt n)⁻¹ * t
  let S : Set Ω := {x | ε₀ * Real.sqrt n < |Y n x|}
  have hS : MeasurableSet S := by
    exact measurableSet_lt measurable_const (hYmeas n).abs
  have hsmallInt : Integrable (fun x => δ * (u * Y n x) ^ 2) P :=
    ((hYmem n).integrable_sq.const_mul (u ^ 2)).const_mul δ |>.congr
      (Eventually.of_forall fun x => by ring)
  have hlargeInt : Integrable
      (S.indicator (fun x => 4 / δ ^ 2 * (u * Y n x) ^ 2)) P :=
    ((((hYmem n).integrable_sq.const_mul (u ^ 2)).const_mul (4 / δ ^ 2))
      |>.congr (Eventually.of_forall fun x => by ring)).indicator hS
  have hdomInt : Integrable (fun x =>
      δ * (u * Y n x) ^ 2 + S.indicator (fun x => 4 / δ ^ 2 * (u * Y n x) ^ 2) x) P := by
    exact hsmallInt.add hlargeInt
  have hpoint : ∀ x, ‖quadraticExpRemainder (u * Y n x)‖ ≤
      δ * (u * Y n x) ^ 2 + S.indicator (fun x => 4 / δ ^ 2 * (u * Y n x) ^ 2) x := by
    intro x
    by_cases hz : |u * Y n x| ≤ δ
    · have hc := norm_quadraticExpRemainder_le_cube (hz.trans hδ1)
      have hc' : |u * Y n x| ^ 3 ≤ δ * (u * Y n x) ^ 2 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (u * Y n x), sq_nonneg (u * Y n x)]
      exact hc.trans <| hc'.trans <| le_add_of_nonneg_right
        (Set.indicator_nonneg (fun _ _ => by positivity) _)
    · have hz' : δ < |u * Y n x| := lt_of_not_ge hz
      have hxS : x ∈ S := by
        dsimp [S, ε₀, u]
        rw [abs_mul, abs_mul, abs_inv, abs_of_pos hsqrt] at hz'
        rw [inv_mul_eq_div, div_mul_eq_mul_div] at hz'
        rw [div_mul_eq_mul_div, div_lt_iff₀ ht_abs, mul_comm]
        simpa [mul_comm] using (lt_div_iff₀ hsqrt).mp hz'
      rw [Set.indicator_of_mem hxS]
      exact (norm_quadraticExpRemainder_le_mul_sq_of_delta_lt_abs hδ hδ1 hz').trans
        (le_add_of_nonneg_left (by positivity))
  have hnorm := norm_integral_le_of_norm_le hdomInt
    (Eventually.of_forall hpoint)
  have hcalc : ∫ x, (δ * (u * Y n x) ^ 2 +
      S.indicator (fun x => 4 / δ ^ 2 * (u * Y n x) ^ 2) x) ∂P =
      δ * u ^ 2 * (∫ x, (Y n x) ^ 2 ∂P) +
        (4 / δ ^ 2) * u ^ 2 * tail n := by
    rw [integral_add hsmallInt hlargeInt, integral_indicator hS,
      integral_const_mul, integral_const_mul]
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_const_mul]
    dsimp [tail, S]
    congr 1 <;> ring
  rw [hcalc] at hnorm
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg n) (norm_nonneg _))]
  calc
    (n : ℝ) * ‖∫ x, quadraticExpRemainder ((Real.sqrt n)⁻¹ * t * Y n x) ∂P‖
        ≤ (n : ℝ) * (δ * u ^ 2 * (∫ x, (Y n x) ^ 2 ∂P) +
          (4 / δ ^ 2) * u ^ 2 * tail n) := by
            simpa only [u] using mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n)
    _ = δ * t ^ 2 * (∫ x, (Y n x) ^ 2 ∂P) +
          (4 / δ ^ 2) * t ^ 2 * tail n := by
            dsimp [u]
            field_simp [ne_of_gt hsqrt]
            rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    _ < η := by
      have hfirst : δ * t ^ 2 * (∫ x, (Y n x) ^ 2 ∂P) < η / 4 :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left hvn.le
          (mul_nonneg hδ.le (sq_nonneg t))) hδbudget
      have hsecond : (4 / δ ^ 2) * t ^ 2 * tail n < η / 4 := by
        calc
          (4 / δ ^ 2) * t ^ 2 * tail n < (4 / δ ^ 2) * t ^ 2 * a := by
            gcongr
          _ ≤ η / 4 := by
            dsimp [a]
            field_simp
            nlinarith [sq_nonneg t]
      linarith

/-- A limit of centered scalar second moments is nonnegative. -/
lemma nonneg_of_tendsto_centeredSecondMoment
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → ℝ} {σ2 : ℝ}
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    -- convergence of the centered row variances in vdV Proposition 2.27.
    (hvar : Tendsto
      (fun n => ∫ x, (centeredScalarRow P g n x) ^ 2 ∂P)
      atTop (𝓝 σ2)) :
    0 ≤ σ2 := by
  apply ge_of_tendsto' hvar
  intro n
  change 0 ≤ ∫ x, (g n x - ∫ y, g n y ∂P) ^ 2 ∂P
  rw [← variance_eq_integral (hg_memLp n).1.aemeasurable]
  exact variance_nonneg _ _

/-- Centered row variables divided by `√n` converge to zero in population
measure when their centered second moments converge.

This derives the infinitesimality input needed by the characteristic-function
argument; no Feller or maximum-row hypothesis is exposed. -/
lemma tendstoInMeasure_centered_invSqrt_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → ℝ} {σ2 : ℝ}
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    -- convergence of the centered row variances in vdV Proposition 2.27.
    (hvar : Tendsto
      (fun n => ∫ x, (centeredScalarRow P g n x) ^ 2 ∂P)
      atTop (𝓝 σ2)) :
    TendstoInMeasure P
      (fun (n : ℕ) x => (Real.sqrt n)⁻¹ * centeredScalarRow P g n x)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let v : ℕ → ℝ := fun n => ∫ x, (centeredScalarRow P g n x) ^ 2 ∂P
  have hv : Tendsto v atTop (nhds σ2) := hvar
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun n : ℕ => ε * Real.sqrt n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hε hsqrt
  have hinv : Tendsto (fun n : ℕ => ((ε * Real.sqrt n) ^ 2)⁻¹)
      atTop (nhds 0) := by
    have hi := (tendsto_inv_atTop_zero.comp hscale).pow 2
    change Tendsto (fun n : ℕ => (ε * Real.sqrt n)⁻¹ ^ 2)
      atTop (nhds (0 ^ 2)) at hi
    have hz : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hz] at hi
    simpa only [inv_pow] using hi
  have hquot : Tendsto (fun n => v n / (ε * Real.sqrt n) ^ 2) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hv.mul hinv
  have hquot' : Tendsto
      (fun n => ENNReal.ofReal (v n / (ε * Real.sqrt n) ^ 2))
      atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero] using!
      (ENNReal.continuous_ofReal.tendsto 0).comp hquot
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hquot'
  · exact Eventually.of_forall fun _ => zero_le
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    have hset :
        {x | ε ≤ ‖(Real.sqrt n)⁻¹ * centeredScalarRow P g n x - 0‖} =
          {x | ε * Real.sqrt n ≤ |g n x - ∫ y, g n y ∂P|} := by
      ext x
      simp only [sub_zero, Real.norm_eq_abs, abs_mul, centeredScalarRow]
      rw [abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg n))]
      simpa only [div_eq_mul_inv, mul_comm] using!
        (le_div_iff₀ hsq : ε ≤ |g n x - ∫ y, g n y ∂P| / Real.sqrt n ↔ _)
    rw [hset]
    have hcheb := meas_ge_le_variance_div_sq (hg_memLp n) (mul_pos hε hsq)
    rw [variance_eq_integral (hg_memLp n).1.aemeasurable] at hcheb
    simpa only [v, centeredScalarRow] using hcheb

/-- The centered row characteristic function has the quadratic Lindeberg
remainder required by the triangular-array power limit. -/
lemma charFun_centered_invSqrt_isLittleO_of_lindeberg
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → ℝ} {σ2 : ℝ}
    -- vdV Theorem 19.28 assumes measurable row functions.
    (hg_meas : ∀ n, Measurable (g n))
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    -- convergence of the centered row variances in vdV Proposition 2.27.
    (hvar : Tendsto
      (fun n => ∫ x, (centeredScalarRow P g n x) ^ 2 ∂P)
      atTop (𝓝 σ2))
    -- the norm-tail Lindeberg condition in vdV Proposition 2.27.
    (hLin : ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ => ∫⁻ x in
          {x | ε * Real.sqrt n < |centeredScalarRow P g n x|},
          ENNReal.ofReal ((centeredScalarRow P g n x) ^ 2) ∂P)
        atTop (𝓝 0))
    (t : ℝ) :
    (fun n : ℕ =>
      charFun (P.map (centeredScalarRow P g n)) ((Real.sqrt n)⁻¹ * t) -
        (1 + ((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ) / (n : ℂ)))
      =o[atTop] (fun n : ℕ => 1 / (n : ℂ)) := by
  let Y : ℕ → Ω → ℝ := fun n => centeredScalarRow P g n
  have hYmeas : ∀ n, Measurable (Y n) := fun n => by
    exact (hg_meas n).sub measurable_const
  have hYmem : ∀ n, MemLp (Y n) 2 P := fun n => by
    exact (hg_memLp n).sub (memLp_const _)
  have hYmean : ∀ n, ∫ x, Y n x ∂P = 0 := fun n => by
    dsimp [Y, centeredScalarRow]
    rw [integral_sub ((hg_memLp n).integrable (by norm_num))
      (integrable_const _), integral_const]
    simp [probReal_univ]
  have hremNorm := tendsto_nat_mul_integral_quadraticExpRemainder
    hYmeas hYmem hvar hLin t
  have hrem : Tendsto (fun n : ℕ => ((n : ℝ) : ℂ) *
      (∫ x, quadraticExpRemainder ((Real.sqrt n)⁻¹ * t * Y n x) ∂P))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Complex.norm_mul, Complex.norm_real, Real.norm_natCast,
      Nat.cast_nonneg, Real.norm_eq_abs, abs_of_nonneg] using hremNorm
  have hvarC : Tendsto (fun n => ((∫ x, (Y n x) ^ 2 ∂P : ℝ) : ℂ))
      atTop (nhds (σ2 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto σ2).comp hvar
  have hcorr : Tendsto (fun n =>
      -((((∫ x, (Y n x) ^ 2 ∂P : ℝ) : ℂ) - (σ2 : ℂ)) *
        (t : ℂ) ^ 2 / 2)) atTop (nhds 0) := by
    have hd := hvarC.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (σ2 : ℂ)) atTop (nhds (σ2 : ℂ)))
    convert (hd.mul_const ((t : ℂ) ^ 2 / 2)).neg using 1
    · funext n
      ring
    · ring
  have hdenom : ∀ᶠ n : ℕ in atTop, (1 / (n : ℂ)) = 0 →
      charFun (P.map (centeredScalarRow P g n)) ((Real.sqrt n)⁻¹ * t) -
        (1 + ((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ) / (n : ℂ)) = 0 := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    intro hzero
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    exact False.elim ((one_div_ne_zero hn0) hzero)
  refine (Asymptotics.isLittleO_iff_tendsto' hdenom).2 ?_
  convert (hrem.add hcorr).congr' ?_ using 1
  · norm_num
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hsqrt : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
  have hexact := charFun_sub_quadratic_eq_integral_quadraticExpRemainder
    (hYmeas n) (hYmem n) (hYmean n) ((Real.sqrt n)⁻¹ * t)
  dsimp [Y] at hexact ⊢
  have hu : ((((Real.sqrt n)⁻¹ * t : ℝ) : ℂ) ^ 2) =
      (t : ℂ) ^ 2 / (n : ℂ) := by
    have hsqC : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = (n : ℂ) := by
      norm_cast
      exact Real.sq_sqrt hnR.le
    push_cast
    field_simp [hnC, hsqrt]
    rw [hsqC]
    ring
  rw [← hexact, hu]
  field_simp [hnC]
  push_cast
  ring

/-- Scalar row-iid triangular Lindeberg central limit theorem, including the
degenerate limiting-variance case. -/
theorem tendstoInDistribution_triangular_iid_lindeberg_real
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- BOOK-ENCODING: measurable coordinates in the standard iid sample representation.
    (hX_meas : ∀ i, Measurable (X i))
    -- BOOK-ENCODING: independence in the standard iid sample representation.
    (hX_iindep : iIndepFun X μ)
    -- BOOK-ENCODING: identical distribution in the standard iid sample representation.
    (hX_idem : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    -- BOOK-ENCODING: each sample coordinate has the population law `P`.
    (hX_law : μ.map (X 0) = P)
    (g : ℕ → Ω → ℝ)
    -- vdV Theorem 19.28 assumes measurable row functions.
    (hg_meas : ∀ n, Measurable (g n))
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    {σ2 : ℝ}
    -- convergence of the centered row variances in vdV Proposition 2.27.
    (hvar : Tendsto
      (fun n => ∫ x, (centeredScalarRow P g n x) ^ 2 ∂P)
      atTop (𝓝 σ2))
    -- the norm-tail Lindeberg condition in vdV Proposition 2.27.
    (hLin : ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ => ∫⁻ x in
          {x | ε * Real.sqrt n < |centeredScalarRow P g n x|},
          ENNReal.ofReal ((centeredScalarRow P g n x) ^ 2) ∂P)
        atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ξ => (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, (g n (X i.val ξ) - ∫ x, g n x ∂P))
      atTop (id : ℝ → ℝ) (fun _ => μ) (gaussianReal 0 σ2.toNNReal) := by
  classical
  have hσ2 : 0 ≤ σ2 := nonneg_of_tendsto_centeredSecondMoment hg_memLp hvar
  have hsource : ∀ n : ℕ, AEMeasurable
      (fun ξ => (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, (g n (X i.val ξ) - ∫ x, g n x ∂P)) μ := by
    intro n
    have hsum : AEMeasurable (fun ξ =>
        ∑ i : Fin n, (g n (X i.val ξ) - ∫ x, g n x ∂P)) μ :=
      Finset.aemeasurable_fun_sum (Finset.univ : Finset (Fin n)) fun i _ =>
        (((hg_meas n).comp (hX_meas i.val)).sub measurable_const).aemeasurable
    exact hsum.const_smul ((Real.sqrt n)⁻¹ : ℝ)
  refine ⟨hsource, measurable_id.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr ?_
  intro t
  let f : ℕ → ℂ := fun n =>
    charFun (P.map (centeredScalarRow P g n)) ((Real.sqrt n)⁻¹ * t)
  have hfLittle : (fun n : ℕ =>
      f n - (1 + ((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ) / (n : ℂ)))
      =o[atTop] (fun n : ℕ => 1 / (n : ℂ)) := by
    exact charFun_centered_invSqrt_isLittleO_of_lindeberg
      hg_meas hg_memLp hvar hLin t
  have hpow : Tendsto (fun n : ℕ => f n ^ n) atTop
      (nhds (Complex.exp ((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ))) :=
    Complex.tendsto_pow_exp_of_isLittleO_sub_add_div
      (((-(σ2 * t ^ 2 / 2) : ℝ) : ℂ)) hfLittle
  have hrowCF : ∀ n : ℕ,
      charFun (μ.map (fun ξ => (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, (g n (X i.val ξ) - ∫ x, g n x ∂P))) t = f n ^ n := by
    intro n
    let Z : ℕ → Ξ → ℝ := fun i ξ => centeredScalarRow P g n (X i ξ)
    have hcmeas : Measurable (centeredScalarRow P g n) :=
      (hg_meas n).sub measurable_const
    have hZiindep : iIndepFun Z μ :=
      hX_iindep.comp (fun _ => centeredScalarRow P g n) (fun _ => hcmeas)
    have hZidem : ∀ i, IdentDistrib (Z i) (Z 0) μ μ := fun i =>
      (hX_idem i).comp hcmeas
    have hcf := ProbabilityTheory.charFun_inv_sqrt_mul_sum
      hZiindep hZidem (n := n) (t := t)
    have hmap : μ.map (Z 0) = P.map (centeredScalarRow P g n) := by
      dsimp [Z]
      change μ.map (centeredScalarRow P g n ∘ X 0) = _
      rw [← Measure.map_map hcmeas (hX_meas 0), hX_law]
    rw [hmap] at hcf
    rw [← hcf]
    congr 2
    funext ξ
    simp only [smul_eq_mul]
    rw [← Fin.sum_univ_eq_sum_range (fun k => Z k ξ) n]
    rfl
  have hsourceCF : (fun n : ℕ =>
      charFun (μ.map (fun ξ => (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, (g n (X i.val ξ) - ∫ x, g n x ∂P))) t) =
      fun n => f n ^ n := funext hrowCF
  change Tendsto (fun n : ℕ =>
      charFun (μ.map (fun ξ => (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, (g n (X i.val ξ) - ∫ x, g n x ∂P))) t)
      atTop (nhds (charFun ((gaussianReal 0 σ2.toNNReal).map id) t))
  rw [Measure.map_id, hsourceCF]
  simpa [charFun_gaussianReal, Real.coe_toNNReal σ2 hσ2] using hpow

open scoped InnerProductSpace

/-- The centered second moment of an inner-product projection is the
quadratic form of the centered covariance matrix.

This is the finite-coordinate expansion used in the Cramér–Wold reduction;
the projected raw vector is centered through `centeredScalarRow`, and the
underlying vector integral uses the orientation `⟨a, centeredVectorRow ...⟩`. -/
lemma centeredSecondMoment_inner_eq_quadratic
    {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    (n : ℕ) (a : EuclideanSpace ℝ (Fin k)) :
    ∫ x, (centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x) ^ 2 ∂P =
      a.ofLp ⬝ᵥ (centeredCovMatrix P g n).mulVec a.ofLp := by
  classical
  have hg_int : Integrable (g n) P := (hg_memLp n).integrable (by norm_num)
  have hcenter : ∀ x,
      centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x =
        ⟪a, centeredVectorRow P g n x⟫_ℝ := by
    intro x
    rw [centeredScalarRow, centeredVectorRow, integral_inner hg_int a,
      inner_sub_right]
  have hZmem : MemLp (centeredVectorRow P g n) 2 P :=
    (hg_memLp n).sub (memLp_const _)
  have hcoord : ∀ i : Fin k,
      MemLp (fun x => (centeredVectorRow P g n x).ofLp i) 2 P :=
    MeasureTheory.MemLp.eval_piLp hZmem
  have hterm : ∀ i j : Fin k, Integrable (fun x =>
      a.ofLp i * ((centeredVectorRow P g n x).ofLp i *
        (centeredVectorRow P g n x).ofLp j) * a.ofLp j) P := by
    intro i j
    exact ((hcoord i).integrable_mul (hcoord j)).const_mul (a.ofLp i)
      |>.mul_const (a.ofLp j)
  rw [integral_congr_ae (Eventually.of_forall fun x => congrArg (fun z : ℝ => z ^ 2)
    (hcenter x))]
  change (∫ x, ((centeredVectorRow P g n x).ofLp ⬝ᵥ a.ofLp) ^ 2 ∂P) = _
  have hsquare : ∀ x,
      ((centeredVectorRow P g n x).ofLp ⬝ᵥ a.ofLp) ^ 2 =
        ∑ i, ∑ j, a.ofLp i *
          ((centeredVectorRow P g n x).ofLp i *
            (centeredVectorRow P g n x).ofLp j) * a.ofLp j := by
    intro x
    rw [sq]
    change (∑ i, (centeredVectorRow P g n x).ofLp i * a.ofLp i) *
      (∑ j, (centeredVectorRow P g n x).ofLp j * a.ofLp j) = _
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [integral_congr_ae (Eventually.of_forall hsquare)]
  calc
    (∫ x, ∑ i, ∑ j, a.ofLp i *
        ((centeredVectorRow P g n x).ofLp i *
          (centeredVectorRow P g n x).ofLp j) * a.ofLp j ∂P) =
        ∑ i, ∫ x, ∑ j, a.ofLp i *
          ((centeredVectorRow P g n x).ofLp i *
            (centeredVectorRow P g n x).ofLp j) * a.ofLp j ∂P := by
      rw [integral_finset_sum _ (fun i _ =>
        integrable_finset_sum _ (fun j _ => hterm i j))]
    _ = ∑ i, ∑ j, ∫ x, a.ofLp i *
          ((centeredVectorRow P g n x).ofLp i *
            (centeredVectorRow P g n x).ofLp j) * a.ofLp j ∂P := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ (fun j _ => hterm i j)]
    _ = a.ofLp ⬝ᵥ (centeredCovMatrix P g n).mulVec a.ofLp := by
      simp only [centeredCovMatrix, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const, integral_const_mul]
      ring

/-- Entrywise convergence of centered covariance matrices implies convergence
of every centered projected second moment. -/
lemma tendsto_centeredSecondMoment_inner_of_tendsto_centeredCovMatrix
    {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    {S : Matrix (Fin k) (Fin k) ℝ}
    -- finite-coordinate covariance convergence from vdV Theorem 19.28.
    (hcov : Tendsto (centeredCovMatrix P g) atTop (𝓝 S))
    (a : EuclideanSpace ℝ (Fin k)) :
    Tendsto
      (fun n ↦ ∫ x,
        (centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x) ^ 2 ∂P)
      atTop (𝓝 (a.ofLp ⬝ᵥ S.mulVec a.ofLp)) := by
  have hquad : Tendsto
      (fun M : Matrix (Fin k) (Fin k) ℝ => a.ofLp ⬝ᵥ M.mulVec a.ofLp)
      (𝓝 S) (𝓝 (a.ofLp ⬝ᵥ S.mulVec a.ofLp)) := by
    exact (by fun_prop : Continuous
      (fun M : Matrix (Fin k) (Fin k) ℝ => a.ofLp ⬝ᵥ M.mulVec a.ofLp)).tendsto S
  convert hquad.comp hcov using 1
  funext n
  exact centeredSecondMoment_inner_eq_quadratic hg_memLp n a

/-- The vector norm-tail Lindeberg condition implies the scalar Lindeberg
condition for every inner-product projection, including the zero direction. -/
lemma lindeberg_inner_of_vector_lindeberg
    {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    -- the vector norm-tail Lindeberg condition in vdV Proposition 2.27.
    (hLin : ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ ↦ ∫⁻ x in
          {x | ε * Real.sqrt n < ‖centeredVectorRow P g n x‖},
          ENNReal.ofReal (‖centeredVectorRow P g n x‖ ^ 2) ∂P)
        atTop (𝓝 0))
    (a : EuclideanSpace ℝ (Fin k)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ ↦ ∫⁻ x in
          {x | ε * Real.sqrt n <
            |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x|},
          ENNReal.ofReal
            ((centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x) ^ 2) ∂P)
        atTop (𝓝 0) := by
  intro ε hε
  by_cases ha : a = 0
  · subst a
    simp [centeredScalarRow]
  have ha_norm : 0 < ‖a‖ := (norm_pos_iff.mpr ha)
  have htail := hLin (ε / ‖a‖) (div_pos hε ha_norm)
  have hcenter : ∀ n x,
      centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x =
        ⟪a, centeredVectorRow P g n x⟫_ℝ := by
    intro n x
    rw [centeredScalarRow, centeredVectorRow,
      integral_inner ((hg_memLp n).integrable (by norm_num)) a, inner_sub_right]
  have hupper : ∀ n : ℕ,
      (∫⁻ x in {x | ε * Real.sqrt n <
          |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x|},
        ENNReal.ofReal
          ((centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x) ^ 2) ∂P) ≤
        ENNReal.ofReal (‖a‖ ^ 2) *
          ∫⁻ x in {x | (ε / ‖a‖) * Real.sqrt n <
              ‖centeredVectorRow P g n x‖},
            ENNReal.ofReal (‖centeredVectorRow P g n x‖ ^ 2) ∂P := by
    intro n
    have habs : ∀ x,
          |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x| ≤
            ‖a‖ * ‖centeredVectorRow P g n x‖ := by
      intro x
      rw [hcenter n x]
      exact abs_real_inner_le_norm _ _
    have hsubset : {x | ε * Real.sqrt n <
        |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x|} ⊆
        {x | (ε / ‖a‖) * Real.sqrt n < ‖centeredVectorRow P g n x‖} := by
      intro x hx
      change (ε / ‖a‖) * Real.sqrt n < ‖centeredVectorRow P g n x‖
      rw [div_mul_eq_mul_div, div_lt_iff₀ ha_norm]
      exact hx.trans_le (by simpa [mul_comm] using habs x)
    have hsquare : ∀ x,
        (centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x) ^ 2 ≤
          ‖a‖ ^ 2 * ‖centeredVectorRow P g n x‖ ^ 2 := by
      intro x
      calc
        (centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x) ^ 2 =
            |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x| ^ 2 :=
          (sq_abs _).symm
        _ ≤ (‖a‖ * ‖centeredVectorRow P g n x‖) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (habs x)
        _ = _ := by ring
    calc
      (∫⁻ x in {x | ε * Real.sqrt n <
          |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x|},
        ENNReal.ofReal
          ((centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x) ^ 2) ∂P) ≤
          ∫⁻ x in {x | ε * Real.sqrt n <
              |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x|},
            ENNReal.ofReal (‖a‖ ^ 2 * ‖centeredVectorRow P g n x‖ ^ 2) ∂P :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hsquare x)
      _ = ENNReal.ofReal (‖a‖ ^ 2) *
          ∫⁻ x in {x | ε * Real.sqrt n <
              |centeredScalarRow P (fun m y ↦ ⟪a, g m y⟫_ℝ) n x|},
            ENNReal.ofReal (‖centeredVectorRow P g n x‖ ^ 2) ∂P := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg ‖a‖)]
      _ ≤ ENNReal.ofReal (‖a‖ ^ 2) *
          ∫⁻ x in {x | (ε / ‖a‖) * Real.sqrt n <
              ‖centeredVectorRow P g n x‖},
            ENNReal.ofReal (‖centeredVectorRow P g n x‖ ^ 2) ∂P :=
        mul_le_mul_right (lintegral_mono_set hsubset) _
  have hscaled := ENNReal.Tendsto.const_mul htail
    (Or.inr (ENNReal.ofReal_ne_top (r := ‖a‖ ^ 2)))
  simp only [mul_zero] at hscaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscaled
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall hupper)

/-- Every centered covariance matrix is positive semidefinite. -/
lemma centeredCovMatrix_posSemidef
    {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P) (n : ℕ) :
    (centeredCovMatrix P g n).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [centeredCovMatrix, Matrix.conjTranspose_apply, star_trivial]
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  · have hx : star x = x := by
      funext i
      exact star_trivial _
    rw [hx]
    let a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 x
    rw [← centeredSecondMoment_inner_eq_quadratic hg_memLp n a]
    exact integral_nonneg fun y => sq_nonneg _

/-- A pointwise limit of centered covariance matrices is positive
semidefinite; no strict positive-definiteness premise is needed. -/
lemma posSemidef_of_tendsto_centeredCovMatrix
    {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {g : ℕ → Ω → EuclideanSpace ℝ (Fin k)}
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    {S : Matrix (Fin k) (Fin k) ℝ}
    -- finite-coordinate covariance convergence from vdV Theorem 19.28.
    (hcov : Tendsto (centeredCovMatrix P g) atTop (𝓝 S)) :
    S.PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    have hij := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hcov j) i)
    have hji := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hcov i) j)
    apply tendsto_nhds_unique hij
    convert hji using 1
    exact funext fun n => by
      simp only [centeredCovMatrix]
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  · have hx : star x = x := by
      funext i
      exact star_trivial _
    rw [hx]
    let a : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 x
    apply ge_of_tendsto'
      (tendsto_centeredSecondMoment_inner_of_tendsto_centeredCovMatrix
        hg_memLp hcov a)
    intro n
    exact integral_nonneg fun y => sq_nonneg _

/-- Finite-dimensional row-iid triangular Lindeberg central limit theorem,
including zero-dimensional and singular-covariance cases. -/
theorem tendstoInDistribution_triangular_iid_lindeberg
    {k : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- BOOK-ENCODING: measurable coordinates in the standard iid sample representation.
    (hX_meas : ∀ i, Measurable (X i))
    -- BOOK-ENCODING: independence in the standard iid sample representation.
    (hX_iindep : iIndepFun X μ)
    -- BOOK-ENCODING: identical distribution in the standard iid sample representation.
    (hX_idem : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    -- BOOK-ENCODING: each sample coordinate has the population law `P`.
    (hX_law : μ.map (X 0) = P)
    (g : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    -- vdV Theorem 19.28 assumes measurable vector rows.
    (hg_meas : ∀ n, Measurable (g n))
    -- rowwise square-integrability in vdV Proposition 2.27.
    (hg_memLp : ∀ n, MemLp (g n) 2 P)
    {S : Matrix (Fin k) (Fin k) ℝ}
    -- finite-coordinate covariance convergence from vdV Theorem 19.28.
    (hcov : Tendsto (centeredCovMatrix P g) atTop (𝓝 S))
    -- the vector norm-tail Lindeberg condition in vdV Proposition 2.27.
    (hLin : ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n : ℕ ↦ ∫⁻ x in
          {x | ε * Real.sqrt n < ‖centeredVectorRow P g n x‖},
          ENNReal.ofReal (‖centeredVectorRow P g n x‖ ^ 2) ∂P)
        atTop (𝓝 0)) :
    TendstoInDistribution
      (fun (n : ℕ) ξ ↦ (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, centeredVectorRow P g n (X i.val ξ))
      atTop (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
      (fun _ ↦ μ) (multivariateGaussian 0 S) := by
  classical
  let W : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun n ξ =>
    (Real.sqrt n)⁻¹ • ∑ i : Fin n, centeredVectorRow P g n (X i.val ξ)
  have hW_meas : ∀ n, Measurable (W n) := by
    intro n
    have hsum : Measurable
        (fun ξ => ∑ i : Fin n, centeredVectorRow P g n (X i.val ξ)) :=
      Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
        ((hg_meas n).comp (hX_meas i.val)).sub measurable_const
    exact hsum.const_smul ((Real.sqrt n)⁻¹ : ℝ)
  have hS : S.PosSemidef :=
    posSemidef_of_tendsto_centeredCovMatrix hg_memLp hcov
  let νn : ℕ → Measure (EuclideanSpace ℝ (Fin k)) := fun n => μ.map (W n)
  haveI hνn_prob : ∀ n, IsProbabilityMeasure (νn n) := fun n =>
    Measure.isProbabilityMeasure_map (hW_meas n).aemeasurable
  have hweak : AsymptoticStatistics.WeakConverges νn
      (multivariateGaussian 0 S) := by
    apply AsymptoticStatistics.ForMathlib.cramerWold_weakConverges_euclidean
    intro a
    let ga : ℕ → Ω → ℝ := fun n x => ⟪a, g n x⟫_ℝ
    let Za : ℕ → Ξ → ℝ := fun n ξ =>
      (Real.sqrt n)⁻¹ •
        ∑ i : Fin n, centeredScalarRow P ga n (X i.val ξ)
    have hga_meas : ∀ n, Measurable (ga n) := fun n => by
      exact (continuous_const.inner continuous_id).measurable.comp (hg_meas n)
    have hga_memLp : ∀ n, MemLp (ga n) 2 P := fun n =>
      MemLp.const_inner a (hg_memLp n)
    have hvar :=
      tendsto_centeredSecondMoment_inner_of_tendsto_centeredCovMatrix
        hg_memLp hcov a
    have hLin_a := lindeberg_inner_of_vector_lindeberg hg_memLp hLin a
    have hscalar : TendstoInDistribution Za atTop (id : ℝ → ℝ)
        (fun _ => μ)
        (gaussianReal 0 (a.ofLp ⬝ᵥ S.mulVec a.ofLp).toNNReal) := by
      simpa only [Za, ga, centeredScalarRow] using
        (tendstoInDistribution_triangular_iid_lindeberg_real
          P μ X hX_meas hX_iindep hX_idem hX_law ga hga_meas hga_memLp
          hvar hLin_a)
    have hscalarWeak : AsymptoticStatistics.WeakConverges
        (fun n => μ.map (Za n))
        (gaussianReal 0 (a.ofLp ⬝ᵥ S.mulVec a.ofLp).toNNReal) := by
      intro f
      have ht :=
        (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
          hscalar.tendsto) f
      simpa only [Measure.map_id] using! ht
    have hproj : ∀ n,
        (νn n).map (fun v => ⟪a, v⟫_ℝ) = μ.map (Za n) := by
      intro n
      change (μ.map (W n)).map (fun v => ⟪a, v⟫_ℝ) = μ.map (Za n)
      rw [Measure.map_map (by fun_prop) (hW_meas n)]
      congr 1
      funext ξ
      have hcenter : ∀ i : Fin n,
          ⟪a, centeredVectorRow P g n (X i.val ξ)⟫_ℝ =
            centeredScalarRow P ga n (X i.val ξ) := by
        intro i
        change ⟪a, centeredVectorRow P g n (X i.val ξ)⟫_ℝ =
          centeredScalarRow P (fun m y => ⟪a, g m y⟫_ℝ) n (X i.val ξ)
        rw [centeredScalarRow, centeredVectorRow,
          integral_inner ((hg_memLp n).integrable (by norm_num)) a,
          inner_sub_right]
      simp only [Function.comp_apply, W, Za, real_inner_smul_right, inner_sum,
        hcenter, smul_eq_mul]
    rw [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal a hS]
    intro f
    simpa only [hproj] using hscalarWeak f
  refine ⟨fun n => (hW_meas n).aemeasurable, measurable_id.aemeasurable, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  intro f
  simpa only [W, νn, Measure.map_id] using! hweak f

end AsymptoticStatistics.EmpiricalProcess
