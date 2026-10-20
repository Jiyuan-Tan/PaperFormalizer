module
public import StatLean.AsymptoticStatistics.Core.TangentAbstract

@[expose] public section

/-!
# Tangent cone + negation-closure ⇒ linear space

A **convex cone closed under negation is a linear subspace**. The canonical
`semiparametric_local_asymptotic_minimax_theorem` carries the three geometric
hypotheses `_hCone` + `_hConvex` + `_hNegClosed`, while the underlying
8.11-reduction `LAMSemiparametricUnbounded.lam_semiparametric_unbounded`
consumes the three linear-space closure hypotheses `_hLin_smul` / `_hLin_add` /
`_hLin_zero`. The three lemmas below discharge that equivalence, so the
canonical theorem's body can forward to the reduction.

Note on `_hLin_zero`: `TangentSpec.carrier` is a bare `Set` with no
zero-membership field and may be empty (see `Core/TangentAbstract.lean`).
`0 ∈ carrier` therefore requires `carrier.Nonempty`; the forwarding theorem
handles the empty case separately, where the LAM-LHS supremum is the empty-set
baseline `0` and the conclusion is trivial.

Reference: van der Vaart, *Asymptotic Statistics*, §25.3.
-/

open MeasureTheory

namespace AsymptoticStatistics.LowerBounds.LAMLinearFromCone

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- All-scalar scaling closure from nonneg-cone closure + negation closure. -/
theorem lin_smul_of_cone_neg (T : TangentSpec P)
    (hCone : ∀ x ∈ T.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T.carrier)
    (hNeg : ∀ x ∈ T.carrier, -x ∈ T.carrier)
    {x} (hx : x ∈ T.carrier) (t : ℝ) : t • x ∈ T.carrier := by
  rcases le_total 0 t with ht | ht
  · exact hCone x hx t ht
  · have h : t • x = (-t) • (-x) := by rw [smul_neg, neg_smul, neg_neg]
    rw [h]; exact hCone (-x) (hNeg x hx) (-t) (by linarith)

/-- Additive closure from nonneg-cone closure + convexity. -/
theorem lin_add_of_cone_convex (T : TangentSpec P)
    (hCone : ∀ x ∈ T.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T.carrier)
    (hConvex : ∀ x ∈ T.carrier, ∀ y ∈ T.carrier, ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ T.carrier)
    {x y} (hx : x ∈ T.carrier) (hy : y ∈ T.carrier) : x + y ∈ T.carrier := by
  have hmid : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ T.carrier :=
    hConvex x hx y hy (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  have h2 : (2 : ℝ) • ((1/2 : ℝ) • x + (1/2 : ℝ) • y) = x + y := by
    rw [smul_add, smul_smul, smul_smul]; norm_num
  rw [← h2]; exact hCone _ hmid 2 (by norm_num)

/-- Zero membership from nonneg-cone closure + nonempty carrier. -/
theorem lin_zero_of_cone_nonempty (T : TangentSpec P)
    (hCone : ∀ x ∈ T.carrier, ∀ t : ℝ, 0 ≤ t → t • x ∈ T.carrier)
    (hne : T.carrier.Nonempty) : (0 : ↥(L2ZeroMean P)) ∈ T.carrier := by
  obtain ⟨x, hx⟩ := hne
  have := hCone x hx 0 le_rfl
  simpa using this

end AsymptoticStatistics.LowerBounds.LAMLinearFromCone
