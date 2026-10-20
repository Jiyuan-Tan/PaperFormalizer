module
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.MetricSpace.Basic

@[expose] public section

/-!
# From a unique maximum to a well-separated maximum

The M-estimator consistency theorem needs uniform separation outside every
metric ball.  A unique maximum alone does not imply this on a noncompact space.
This file supplies the reusable upper-semicontinuity plus compact-superlevel
adapter used for maximum-likelihood consistency.
-/

open Set

namespace AsymptoticStatistics.ForMathlib

/-- A strict unique maximum of an upper-semicontinuous real function is strongly
well separated when one superlevel strictly below the maximum is compact.

At radius `epsilon`, intersect the fixed compact set `{theta | c <= M theta}`
with the closed far set `{theta | epsilon <= dist theta theta0}`.  If the
intersection is empty, the margin `M theta0 - c` works; otherwise upper
semicontinuity gives a maximizer on the intersection, whose strict gap from
`M theta0` supplies the margin. -/
theorem wellSeparated_of_uniqueMax_upperSemicontinuous_compactSuperlevel
    {Theta : Type*} [MetricSpace Theta] (M : Theta -> Real) (theta0 : Theta)
    (hunique : forall theta, theta ≠ theta0 -> M theta < M theta0)
    (husc : UpperSemicontinuous M)
    (hcompact : ∃ c : Real, c < M theta0 ∧ IsCompact {theta | c <= M theta})
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ eta, 0 < eta /\ ∀ theta,
      epsilon <= dist theta theta0 -> M theta <= M theta0 - eta := by
  obtain ⟨c, hc, hcpt⟩ := hcompact
  have hfar_closed : IsClosed {theta : Theta | epsilon <= dist theta theta0} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKcompact : IsCompact
      ({theta : Theta | epsilon <= dist theta theta0} ∩ {theta | c <= M theta}) :=
    hcpt.inter_left hfar_closed
  by_cases hK :
      ({theta : Theta | epsilon <= dist theta theta0} ∩
        {theta | c <= M theta}).Nonempty
  · obtain ⟨a, ⟨hfar_a, hlevel_a⟩, hmax⟩ :=
      UpperSemicontinuousOn.exists_isMaxOn hK hKcompact
        (husc.upperSemicontinuousOn _)
    have hca : c <= M a := hlevel_a
    have ha_ne : a ≠ theta0 :=
      dist_pos.mp (lt_of_lt_of_le hepsilon hfar_a)
    refine ⟨M theta0 - M a, sub_pos.mpr (hunique a ha_ne), ?_⟩
    intro theta hfar
    by_cases hlevel : c <= M theta
    · have hle : M theta ≤ M a := hmax ⟨hfar, hlevel⟩
      linarith
    · have hbelow : M theta < c := lt_of_not_ge hlevel
      linarith
  · refine ⟨M theta0 - c, sub_pos.mpr hc, ?_⟩
    intro theta hfar
    have hbelow : M theta < c := by
      apply lt_of_not_ge
      intro hlevel
      exact hK ⟨theta, hfar, hlevel⟩
    linarith

end AsymptoticStatistics.ForMathlib
