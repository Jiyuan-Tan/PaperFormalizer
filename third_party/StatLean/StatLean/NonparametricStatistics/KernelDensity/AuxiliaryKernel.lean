module
public import StatLean.NonparametricStatistics.KernelDensity.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Existence of bounded compactly supported kernels of arbitrary order

For every `ℓ` there is a kernel of order `ℓ` that is bounded and supported in `[−1, 1]`.

This existence result is the auxiliary device behind the uniform bound on Hölder densities
(`KernelDensity/UniformDensityBound.lean`): applying the bias inequality with bandwidth `1`
and such a kernel `K*` yields `p(x) ≤ C₂* + sup|K*|` uniformly over the density class.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.2.2 (construction of a kernel of order $\ell$;
this file replaces the Legendre-polynomial construction of Proposition 1.3 by a bounded
box-superposition construction).

**Proof formalization notes.** Instead of the classical Legendre-polynomial construction, use
a superposition of boxes: with `K₀ = ½·𝟙_{[−1,1]}` and distinct scales `a_r ∈ (0, 1]`,
`r = 0, …, ℓ`, set `K(u) = ∑ r, c_r·a_r⁻¹·K₀(u/a_r)`. Odd moments vanish by symmetry; the even
moments of `a⁻¹K₀(·/a)` are `a^{2q}/(2q+1)`, so the moment conditions become a linear system
in `c` whose matrix is (a rescaling of) a Vandermonde matrix in the distinct values `a_r²` —
invertible by `Matrix.det_vandermonde_ne_zero_iff`. Choosing `c` as the solution of the system
with right-hand side `e₀` gives `∫K = 1` and vanishing moments up to order... to cover both
parities cleanly it suffices to solve for even moments `0, 2, …, 2⌈ℓ/2⌉` (odd moments are
automatically `0`), i.e. take `⌈ℓ/2⌉ + 1` boxes. Boundedness and support are clear from the
construction.

**Bibliographic comments.** Kernels of arbitrary order are classically constructed from
orthogonal polynomial systems (cf. G. Szegő, *Orthogonal Polynomials*, 4th ed., AMS, 1975);
the box-superposition construction used here is a folklore alternative.
-/

open MeasureTheory Set
open scoped Matrix

namespace StatLean.NonparametricStatistics

/-- A rescaled box `½s⁻¹·𝟙_{[−s,s]}` written as an indicator to avoid `Decidable` friction. -/
private noncomputable def box (s u : ℝ) : ℝ :=
  Set.indicator (Set.Icc (-s) s) (fun _ => 1 / (2 * s)) u

private lemma box_pow_eq_indicator (s : ℝ) (j : ℕ) :
    (fun u => u ^ j * box s u)
      = (Set.Icc (-s) s).indicator (fun u => u ^ j / (2 * s)) := by
  funext u
  unfold box
  by_cases h : u ∈ Set.Icc (-s) s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

private lemma box_moment_eq (s : ℝ) (hs : 0 < s) (j : ℕ) :
    ∫ u, u ^ j * box s u
      = (s ^ (j + 1) - (-s) ^ (j + 1)) / (((j : ℝ) + 1) * (2 * s)) := by
  rw [box_pow_eq_indicator, integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -s ≤ s),
      intervalIntegral.integral_div, integral_pow, div_div]

private lemma box_moment_odd (s : ℝ) (_hs : 0 < s) (j : ℕ) (hj : Odd j) :
    ∫ u, u ^ j * box s u = 0 := by
  rw [box_moment_eq s _hs j, hj.add_one.neg_pow s, sub_self, zero_div]

private lemma box_moment_even (s : ℝ) (hs : 0 < s) (q : ℕ) :
    ∫ u, u ^ (2 * q) * box s u = s ^ (2 * q) / (2 * (q : ℝ) + 1) := by
  rw [box_moment_eq s hs (2 * q)]
  have hodd : Odd (2 * q + 1) := ⟨q, by ring⟩
  rw [hodd.neg_pow s]
  have h1 : (2 * (q : ℝ) + 1) ≠ 0 := by positivity
  have h2 : (2 * s) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hs)
  push_cast
  field_simp
  ring

private lemma box_integral_one (s : ℝ) (hs : 0 < s) : ∫ u, box s u = 1 := by
  have h := box_moment_even s hs 0
  simpa using h

private lemma box_integrable (s : ℝ) (_hs : 0 < s) (j : ℕ) :
    Integrable fun u => u ^ j * box s u := by
  rw [box_pow_eq_indicator]
  exact (Continuous.integrableOn_Icc (by fun_prop)).integrable_indicator measurableSet_Icc

private lemma abs_box_le (s : ℝ) (hs : 0 < s) (u : ℝ) : |box s u| ≤ 1 / (2 * s) := by
  have hpos : (0 : ℝ) < 1 / (2 * s) := one_div_pos.mpr (by linarith)
  unfold box
  by_cases h : u ∈ Set.Icc (-s) s
  · rw [Set.indicator_of_mem h, abs_of_pos hpos]
  · rw [Set.indicator_of_notMem h, abs_zero]; exact le_of_lt hpos

/-- Solvability of the (rescaled Vandermonde) moment system for the box coefficients. -/
private lemma exists_vandermonde_coeff {d : ℕ} [NeZero d] (a : Fin d → ℝ)
    (hinj : Function.Injective fun r => (a r) ^ 2) :
    ∃ c : Fin d → ℝ, ∀ q : Fin d,
      ∑ r, ((a r) ^ 2) ^ (q : ℕ) * c r = (Pi.single (0 : Fin d) 1 : Fin d → ℝ) q := by
  set e : Fin d → ℝ := Pi.single (0 : Fin d) 1 with he
  set V := Matrix.vandermonde fun r => (a r) ^ 2 with hV
  have hdet : IsUnit (Vᵀ).det := by
    rw [Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.mpr hinj).isUnit
  refine ⟨(Vᵀ)⁻¹ *ᵥ e, fun q => ?_⟩
  have hc : Vᵀ *ᵥ ((Vᵀ)⁻¹ *ᵥ e) = e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hq := congrFun hc q
  rw [← hq]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hV,
             Matrix.vandermonde_apply]

/-- **Existence of a bounded, compactly supported kernel of order `ℓ`**: there are `K` and
`Kmax` with `K` of order `ℓ`, `|K| ≤ Kmax`, and `K = 0` outside `[−1, 1]`. -/
theorem exists_bounded_kernel_of_order (ℓ : ℕ) :
    ∃ (K : ℝ → ℝ) (Kmax : ℝ), 0 < Kmax ∧ IsKernelOfOrder K ℓ ∧
      (∀ u, |K u| ≤ Kmax) ∧ ∀ u, u ∉ Set.Icc (-1 : ℝ) 1 → K u = 0 := by
  set d := ℓ / 2 + 1 with hd_def
  haveI : NeZero d := ⟨by omega⟩
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  set a : Fin d → ℝ := fun r => (((r : ℕ) : ℝ) + 1) / (d : ℝ) with ha_def
  have ha_pos : ∀ r, 0 < a r := fun r => div_pos (by positivity) hdpos
  have ha_le_one : ∀ r, a r ≤ 1 := fun r => by
    rw [ha_def]; refine (div_le_one hdpos).mpr ?_
    have := r.isLt; exact_mod_cast Nat.succ_le_of_lt this
  have hainj : Function.Injective a := by
    intro r s h
    simp only [ha_def] at h
    have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdpos
    field_simp [hd0] at h
    have : ((r : ℕ) : ℝ) = ((s : ℕ) : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast this)
  have hinj : Function.Injective fun r => (a r) ^ 2 := by
    intro r s h
    have h' : (a r) ^ 2 = (a s) ^ 2 := h
    exact hainj ((sq_eq_sq₀ (le_of_lt (ha_pos r)) (le_of_lt (ha_pos s))).mp h')
  obtain ⟨c, hc⟩ := exists_vandermonde_coeff a hinj
  have hmoment : ∀ j : ℕ, ∫ u, u ^ j * ∑ r, c r * box (a r) u
      = ∑ r, c r * ∫ u, u ^ j * box (a r) u := by
    intro j
    have hfun : (fun u => u ^ j * ∑ r, c r * box (a r) u)
        = fun u => ∑ r, c r * (u ^ j * box (a r) u) := by
      funext u; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [hfun, integral_finset_sum _ (fun r _ => (box_integrable (a r) (ha_pos r) j).const_mul _)]
    exact Finset.sum_congr rfl (fun r _ => integral_const_mul _ _)
  refine ⟨fun u => ∑ r, c r * box (a r) u, (∑ r, |c r| / (2 * a r)) + 1, ?_,
    ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · -- 0 < Kmax
    have : 0 ≤ ∑ r, |c r| / (2 * a r) := Finset.sum_nonneg
      (fun r _ => div_nonneg (abs_nonneg _) (by have := ha_pos r; linarith))
    linarith
  · -- integrable_pow
    intro j hj
    change Integrable fun u => u ^ j * ∑ r, c r * box (a r) u
    have hfun : (fun u => u ^ j * ∑ r, c r * box (a r) u)
        = fun u => ∑ r, c r * (u ^ j * box (a r) u) := by
      funext u; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun r _ => by ring)
    rw [hfun]
    exact integrable_finset_sum _ (fun r _ => (box_integrable (a r) (ha_pos r) j).const_mul _)
  · -- integral_eq_one
    show ∫ u, ∑ r, c r * box (a r) u = 1
    have h0 := hmoment 0
    simp only [pow_zero, one_mul] at h0
    rw [h0]
    have hrow0 := hc 0
    simp only [Fin.val_zero, pow_zero, one_mul, Pi.single_eq_same] at hrow0
    calc ∑ r, c r * ∫ u, box (a r) u
        = ∑ r, c r := Finset.sum_congr rfl
          (fun r _ => by rw [box_integral_one (a r) (ha_pos r), mul_one])
      _ = 1 := hrow0
  · -- moment_eq_zero
    intro j hj1 hjl
    show ∫ u, u ^ j * ∑ r, c r * box (a r) u = 0
    rcases Nat.even_or_odd j with hev | hod
    · obtain ⟨q, hq⟩ := hev
      have hj2 : j = 2 * q := by omega
      subst hj2
      rw [hmoment (2 * q)]
      have hqd : q < d := by omega
      have hq1 : 1 ≤ q := by omega
      have hstep : ∀ r : Fin d, c r * ∫ u, u ^ (2 * q) * box (a r) u
          = c r * (a r) ^ (2 * q) / (2 * (q : ℝ) + 1) := fun r => by
        rw [box_moment_even (a r) (ha_pos r) q]; ring
      rw [Finset.sum_congr rfl (fun r _ => hstep r)]
      have hqne : (⟨q, hqd⟩ : Fin d) ≠ 0 := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_zero]; omega
      have hrq := hc ⟨q, hqd⟩
      rw [Pi.single_eq_of_ne hqne] at hrq
      have hsum : ∑ r, c r * (a r) ^ (2 * q) = 0 := by
        rw [← hrq]; exact Finset.sum_congr rfl (fun r _ => by rw [pow_mul, mul_comm])
      rw [← Finset.sum_div, hsum, zero_div]
    · rw [hmoment j]
      have hzero : (∑ r, c r * ∫ u, u ^ j * box (a r) u) = ∑ _r : Fin d, (0 : ℝ) :=
        Finset.sum_congr rfl
          (fun r _ => by rw [box_moment_odd (a r) (ha_pos r) j hod, mul_zero])
      rw [hzero, Finset.sum_const_zero]
  · -- bound
    intro u
    change |∑ r, c r * box (a r) u| ≤ (∑ r, |c r| / (2 * a r)) + 1
    calc |∑ r, c r * box (a r) u|
        ≤ ∑ r, |c r * box (a r) u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r, |c r| / (2 * a r) := Finset.sum_le_sum (fun r _ => by
            rw [abs_mul]
            calc |c r| * |box (a r) u|
                ≤ |c r| * (1 / (2 * a r)) :=
                  mul_le_mul_of_nonneg_left (abs_box_le (a r) (ha_pos r) u) (abs_nonneg _)
              _ = |c r| / (2 * a r) := by rw [mul_one_div])
      _ ≤ (∑ r, |c r| / (2 * a r)) + 1 := le_add_of_nonneg_right zero_le_one
  · -- support
    intro u hu
    change (∑ r, c r * box (a r) u) = 0
    refine Finset.sum_eq_zero (fun r _ => ?_)
    have hnotmem : u ∉ Set.Icc (-(a r)) (a r) := fun hmem =>
      hu (Set.Icc_subset_Icc (by linarith [ha_le_one r]) (ha_le_one r) hmem)
    rw [show box (a r) u = 0 by
      unfold box; exact Set.indicator_of_notMem hnotmem _, mul_zero]

end StatLean.NonparametricStatistics
