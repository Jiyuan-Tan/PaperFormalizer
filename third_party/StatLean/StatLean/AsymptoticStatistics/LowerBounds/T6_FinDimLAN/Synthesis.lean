module
public import StatLean.AsymptoticStatistics.LowerBounds.FinDimSubmodel
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.CLTinf
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.LANexpansion

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Closed-form finite-dimensional submodel LAN

This file provides `finDimSubmodel_lan_closed`, a thin forwarder over
`finDimSubmodel_lan` that internally constructs the two heavy hypotheses
`hCLT_inf` (via `cltInf_at_orthonormal_basis`) and `hLAN_expansion` (via
`lanExpansion_at_basis_and_h`), leaving them out of the public signature.

The conclusion bundle is identical to `finDimSubmodel_lan`'s: the same four
existential clauses (a)–(d), with the input list dropping the two discharged
hypotheses.

## Strategy

* Build `hCLT_inf` by invoking `cltInf_at_orthonormal_basis` with the same
  `g_P`. The brick wants orthonormality on `Lp ℝ 2 P`; the public signature
  exposes orthonormality on `↥(L2ZeroMean P)`. These are equivalent because
  the inner product on a `Submodule` is `rfl`-equal to the ambient one
  (`Submodule.coe_inner`), so we can transport via the linear isometry
  `(L2ZeroMean P).subtypeₗᵢ`.

* Build `hLAN_expansion` by invoking `lanExpansion_at_basis_and_h` with the
  same data.

* Forward to `finDimSubmodel_lan`.

Reference: vdV §25.3.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.LowerBounds.FinDimSubmodel
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Closed-form finite-dim submodel LAN.**

Thin forwarder over `finDimSubmodel_lan` that internally discharges the two
heavy hypotheses (`hCLT_inf` via `cltInf_at_orthonormal_basis`;
`hLAN_expansion` via `lanExpansion_at_basis_and_h`).

The public input list drops the discharged hypotheses; the conclusion
matches `finDimSubmodel_lan`'s four existential clauses (a)–(d) verbatim.

Reference: vdV §25.3. -/
theorem finDimSubmodel_lan_closed
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (γ : (Fin m → ℝ) → QMDPath P)
    (hγ_score : ∀ h : Fin m → ℝ,
      (γ h).score = ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)))
    (h : Fin m → ℝ) :
    ∃ (Δ : (n : ℕ) → (Fin n → Ω) → EuclideanSpace ℝ (Fin m))
      (R : (n : ℕ) → (Fin n → Ω) → ℝ),
      (∀ (n : ℕ) (X : Fin n → Ω) (i : Fin m),
        Δ n X i = (Real.sqrt n)⁻¹ *
          ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j)) ∧
      (WeakConverges
          (fun n : ℕ =>
            (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map (Δ n))
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧
      (Tendsto (fun n : ℕ =>
          Real.sqrt n * (ψ (submodelAt (γ h) n) - ψ P))
        atTop
        (𝓝 (⟪(IF_eff : ↥(L2ZeroMean P)),
              ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))) ∧
      (∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ |R n X|})
          atTop (𝓝 (0 : ℝ≥0∞))) := by
  -- Transport orthonormality from `↥(L2ZeroMean P)` to `Lp ℝ 2 P`.
  -- The inner product on a submodule is `rfl`-equal to the ambient
  -- one (`Submodule.coe_inner`), and the norm likewise. Hence the
  -- linear isometry `(L2ZeroMean P).subtypeₗᵢ` transports
  -- orthonormality definitionally.
  have h_orth_lp :
      Orthonormal ℝ (fun i : Fin m => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P)) :=
    h_orth.comp_linearIsometry (L2ZeroMean P).subtypeₗᵢ
  have hCLT_inf := cltInf_at_orthonormal_basis g_P h_orth_lp
  have hLAN_expansion :=
    lanExpansion_at_basis_and_h g_P h_orth T_set hg_in_tangent γ hγ_score h
  -- Forward to the heavy theorem.
  exact finDimSubmodel_lan T_set hψ hEIF g_P h_orth hg_in_tangent γ hγ_score h
    hCLT_inf hLAN_expansion

end AsymptoticStatistics.LowerBounds.T6_FinDimLAN
