module
public import StatLean.AsymptoticStatistics.ForMathlib.OneSidedExpectation
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

/-!
# Local upper-semicontinuous envelopes

The shrinking-ball supremum used in Wald's consistency proof, together with
its pointwise-a.e. antitone convergence core.
-/

open MeasureTheory Filter Set Topology

namespace AsymptoticStatistics

/-- The local criterion envelope `x ↦ sup_{η ∈ ball θ r} m_η(x)` from vdV
(5.13), p.48.

Edge behavior: for `r ≤ 0` the metric ball is empty, so the dependent supremum
is `⊥`. Wald's hypotheses use only positive radii. -/
noncomputable def localCriterionSup {X Θ : Type*} [MetricSpace Θ]
    (m : Θ → X → EReal) (θ : Θ) (r : ℝ) (x : X) : EReal :=
  ⨆ η : Metric.ball θ r, m η x

/-- For the radii `1/(k+1)`, local USC envelopes decrease pointwise to the
criterion.  The exceptional set may depend on `θ`, exactly as in vdV (5.12),
p.48; the quantifiers deliberately remain `∀ θ, AE x`. -/
theorem iInf_localCriterionSup_eq
    {X Θ : Type*} [MeasurableSpace X] [MetricSpace Θ]
    (Q : Measure X) (m : Θ → X → EReal)
    -- vdV (5.12), with a θ-dependent exceptional set.
    (husc : ∀ θ, ∀ᵐ x ∂Q, UpperSemicontinuousAt (fun η => m η x) θ) :
    ∀ θ, ∀ᵐ x ∂Q,
      Antitone (fun k : ℕ => localCriterionSup m θ ((k + 1 : ℝ)⁻¹) x) ∧
      Tendsto (fun k : ℕ => localCriterionSup m θ ((k + 1 : ℝ)⁻¹) x)
        atTop (𝓝 (m θ x)) ∧
      (⨅ k : ℕ, localCriterionSup m θ ((k + 1 : ℝ)⁻¹) x) = m θ x := by
  intro θ
  filter_upwards [husc θ] with x hx
  have hanti : Antitone (fun k : ℕ =>
      localCriterionSup m θ ((k + 1 : ℝ)⁻¹) x) := by
    intro k l hkl
    unfold localCriterionSup
    refine iSup_le fun η => ?_
    refine le_iSup_of_le
      (⟨η, Metric.mem_ball.2 ((Metric.mem_ball.1 η.property).trans_le ?_)⟩ :
        Metric.ball θ ((k + 1 : ℝ)⁻¹)) le_rfl
    exact (inv_le_inv₀ (by positivity) (by positivity)).2
      (by exact_mod_cast Nat.add_le_add_right hkl 1)
  have hcenter : ∀ k : ℕ,
      m θ x ≤ localCriterionSup m θ ((k + 1 : ℝ)⁻¹) x := by
    intro k
    unfold localCriterionSup
    exact le_iSup_of_le
      (⟨θ, Metric.mem_ball_self (inv_pos.2 (by positivity))⟩ :
        Metric.ball θ ((k + 1 : ℝ)⁻¹)) le_rfl
  have hupper :
      (⨅ k : ℕ, localCriterionSup m θ ((k + 1 : ℝ)⁻¹) x) ≤ m θ x := by
    have hlimsup := hx.limsup_le
    rw [Metric.nhds_basis_ball_inv_nat_succ.limsup_eq_iInf_iSup] at hlimsup
    simpa only [localCriterionSup, one_div, iInf_true, ← iSup_subtype''] using hlimsup
  have hinf :
      (⨅ k : ℕ, localCriterionSup m θ ((k + 1 : ℝ)⁻¹) x) = m θ x :=
    hupper.antisymm (le_iInf hcenter)
  have htendsto := tendsto_atTop_iInf hanti
  rw [hinf] at htendsto
  exact ⟨hanti, htendsto, hinf⟩

end AsymptoticStatistics
