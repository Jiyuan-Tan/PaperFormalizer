module
public import StatLean.AsymptoticStatistics.Core.NondominatedPathwise
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperationalVec
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

@[expose] public section

/-! # Raw regularity for nondominated selected paths -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped InnerProductSpace

namespace AsymptoticStatistics.Core.NondominatedEfficiencyOperational

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedTangent
open AsymptoticStatistics.Core.EfficiencyOperationalVec
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.Core.TangentAbstract

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Raw scalar regularity along the unit local perturbation of every selected
cone path.  There is no scalar-tilt binder: nonnegative multiples are supplied
as separate carrier scores by the cone.

Edge behavior: the selected zero score derives the baseline law through the
zero-score product-equivalence theorem; that law is not bundled here. -/
def IsRegularAtND
    (C : NondominatedTangentCone P)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (ψ : Measure Ω → ℝ) (L : Measure ℝ) : Prop :=
  ∀ g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n =>
        (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
        (fun X => Real.sqrt n *
          (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))) L

/-- Baseline vector root-`n` limit distribution. -/
def HasLimitDistributionAtNDVec {d : ℕ}
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (L : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  AsymptoticStatistics.WeakConverges
    (fun n => (Measure.pi (fun _ : Fin n => P)).map
      (fun X => Real.sqrt n • (T_n n X - c))) L

/-- Raw vector regularity along unit local perturbations of selected paths. -/
def IsRegularAtNDVec {d : ℕ}
    (C : NondominatedTangentCone P)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    (L : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
    AsymptoticStatistics.WeakConverges
      (fun n => (Measure.pi (fun _ : Fin n =>
        (C.selectedPath g).curve ((Real.sqrt n)⁻¹))).map
        (fun X => Real.sqrt n •
          (T_n n X - ψ ((C.selectedPath g).curve ((Real.sqrt n)⁻¹))))) L

/-- Covariance matrix of a vector influence tuple.  `Matrix.gram` is PSD even
when singular; for `d=0` this is the empty matrix. -/
noncomputable def influenceCovarianceMatrix {d : ℕ}
    (φ : Fin d → ↥(L2ZeroMean P)) : Matrix (Fin d) (Fin d) ℝ := Matrix.gram ℝ φ

/-- A common-dominator selected-path family determines a nondominated family
when its carrier is a nonnegative cone. The construction applies
`QMDPath.toNondominatedQMDPath` pointwise. -/
noncomputable def nondominatedTangentConeOfSelectedQMDPaths
    (T : TangentSpec P) (paths : SelectedQMDPaths P T)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {g}, g ∈ T.carrier → a • g ∈ T.carrier) :
    NondominatedTangentCone P where
  carrier := T.carrier
  carrier_nonempty := ⟨0, paths.zero_mem⟩
  nonneg_smul_mem := hsmul
  selectedPath g :=
    AsymptoticStatistics.Core.NondominatedQMDPath.QMDPath.toNondominatedQMDPath
      (paths.path g)
  selectedPath_score g := by
    change (paths.path g).score = g
    exact paths.score_eq g

/-- The all-real common-dominator regularity predicate implies the unit-path
predicate for its associated cone, by specializing regularity at `a = 1`. -/
theorem isRegularAtND_of_commonDominated_allReal
    (T : TangentSpec P) (paths : SelectedQMDPaths P T)
    (hsmul : ∀ {a : ℝ}, 0 ≤ a → ∀ {g}, g ∈ T.carrier → a • g ∈ T.carrier)
    (T_n : ∀ n, (Fin n → Ω) → ℝ) (ψ : Measure Ω → ℝ) (L : Measure ℝ)
    (hreg : IsRegularAt paths T_n ψ L) :
    IsRegularAtND
      (nondominatedTangentConeOfSelectedQMDPaths T paths hsmul)
      T_n ψ L := by
  intro g
  simpa [nondominatedTangentConeOfSelectedQMDPaths,
    AsymptoticStatistics.Core.NondominatedQMDPath.QMDPath.toNondominatedQMDPath]
    using hreg g 1

end AsymptoticStatistics.Core.NondominatedEfficiencyOperational
