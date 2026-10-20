module
public import StatLean.AsymptoticStatistics.ForMathlib.L2

@[expose] public section

/-! # L² cross terms in asymptotic expansions -/

open MeasureTheory Filter Topology Asymptotics

namespace AsymptoticStatistics.L2Utils

/-- An `L²`-small family paired with an `L²`-bounded family has an
`L¹` cross term of smaller order.  The nonnegativity clause is exactly what
allows square roots of the common scale to be recombined. -/
lemma integral_mul_isLittleO_of_sq
    {α 𝒳 : Type*} [MeasurableSpace 𝒳]
    (l : Filter α) (P : Measure 𝒳)
    (a b : α → 𝒳 → ℝ) (v : α → ℝ)
    (ha_mem : ∀ᶠ t in l, MemLp (a t) 2 P)
    (hb_mem : ∀ t, MemLp (b t) 2 P)
    (hv : ∀ᶠ t in l, 0 ≤ v t)
    (haO : (fun t => ∫ x, a t x ^ 2 ∂P) =o[l] v)
    (hbO : (fun t => ∫ x, b t x ^ 2 ∂P) =O[l] v) :
    (fun t => ∫ x, a t x * b t x ∂P) =o[l] v := by
  have haS := haO.sqrt hv
  have hbS := hbO.sqrt hv
  have hprod :
      (fun t => Real.sqrt (∫ x, a t x ^ 2 ∂P) *
        Real.sqrt (∫ x, b t x ^ 2 ∂P)) =o[l]
        (fun t => Real.sqrt (v t) * Real.sqrt (v t)) :=
    haS.mul_isBigO hbS
  have hprod' :
      (fun t => Real.sqrt (∫ x, a t x ^ 2 ∂P) *
        Real.sqrt (∫ x, b t x ^ 2 ∂P)) =o[l] v := by
    apply hprod.congr' (EventuallyEq.rfl) ?_
    filter_upwards [hv] with t ht
    exact Real.mul_self_sqrt ht
  have hbound :
      (fun t => ∫ x, a t x * b t x ∂P) =O[l]
        (fun t => Real.sqrt (∫ x, a t x ^ 2 ∂P) *
          Real.sqrt (∫ x, b t x ^ 2 ∂P)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [ha_mem] with t hat
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact abs_integral_mul_le_sqrt_integral_sq P hat (hb_mem t)
  exact hbound.trans_isLittleO hprod'

end AsymptoticStatistics.L2Utils
