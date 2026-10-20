module
public import StatLean.AsymptoticStatistics.Operators.CARScores
public import StatLean.AsymptoticStatistics.Operators.CAR
public import StatLean.AsymptoticStatistics.Operators.CompleteCaseIPW
public import StatLean.AsymptoticStatistics.Operators.InformationLoss
public import StatLean.AsymptoticStatistics.ForMathlib.CondExpCompProd
public import StatLean.AsymptoticStatistics.ParametricFamily.CARScore
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-!
# CAR coarsening-score identification: `(observedTangent fullQTangent)ᗮ = concrete` (vdV thm:25.40)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.3,
thm:25.40 (book p.380).

The Hilbert splitting
`H = S̄ ⊕ Sᗮ` with `coarseningScores := (observedTangent …)ᗮ`. The substantive
CAR content of thm:25.40 is the concrete
identification of that orthogonal complement: over the coarsening model
`P_full = Q ⊗ₘ r` on `𝓨 × 𝓓` with observation map `M : 𝓨 × 𝓓 → 𝓧`, the coarsening
scores are exactly the observed functions `b(x)` whose fibrewise `r`-average
vanishes,
  `Ṙ_{Q,R} = { b ∈ L²₀(P_obs) : ∀ᵐ y ∂Q, ∫ δ, b (M (y, δ)) ∂(r y) = 0 }`,
which is vdV's `E_R(b(X) | Y = y) = 0` condition.

This file uses the encoding `P_full = Q ⊗ₘ r`, `M : 𝓨 × 𝓓 → 𝓧`,
the *full* `Q`-tangent `fullQTangent` (all mean-zero functions of the first
coordinate `Y` — "`Q` completely unspecified", vdV p.380), the concrete coarsening
scores `concreteCoarseningScores`, the identification
`coarseningScores … fullQTangent = concreteCoarseningScores`, and the
CAR-carrying decomposition `car_observed_tangent_decomposition`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped InnerProductSpace ENNReal

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Operators.CoarseningScoreIdentification

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Operators.InformationLoss
open AsymptoticStatistics.Operators.CAR
open AsymptoticStatistics.Operators.CARScores
open AsymptoticStatistics.Operators.CompleteCaseIPW
open AsymptoticStatistics.ForMathlib.CondExpL2
open AsymptoticStatistics.ForMathlib.CondExpCompProd
open AsymptoticStatistics.ForMathlib.ConditionalQMD
open AsymptoticStatistics.ParametricFamily.CARScore

variable {𝓨 𝓓 𝓧 : Type*}
  [MeasurableSpace 𝓨] [MeasurableSpace 𝓓] [MeasurableSpace 𝓧]
  (Q : Measure 𝓨) [IsProbabilityMeasure Q]
  (r : Kernel 𝓨 𝓓) [IsMarkovKernel r]
  {M : 𝓨 × 𝓓 → 𝓧} (hM : Measurable M)

/-! ### The full `Q`-tangent -/

/-- *The full `Q`-tangent space* `Ṗ_Q` (vdV thm:25.40, book p.380 — "`Q` is
completely unspecified").

Constitutive (vdV §25.5.3 p.380): the tangent set of the *full-data* model when the
marginal law `Q` of `Y` ranges over **all** probability measures is the space of
all mean-zero functions of `Y` alone. Under the `P_full = Q ⊗ₘ r` encoding, `Y` is
the first coordinate `Prod.fst : 𝓨 × 𝓓 → 𝓨`, so this is the mean-zero `L²`
functions that are `comap Prod.fst`-measurable, realized as the pullback along the
`L²₀`-inclusion of Mathlib's `comap Prod.fst`-measurable submodule `lpMeas`. Removing
the "all `Q`" maximality would make this a proper subspace and break the density
half of the identification. -/
noncomputable def fullQTangent :
    Submodule ℝ ↥(L2ZeroMean (Q ⊗ₘ r)) :=
  Submodule.comap (L2ZeroMean (Q ⊗ₘ r)).subtype
    (lpMeas ℝ ℝ (MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›) 2 (Q ⊗ₘ r))

/-! ### The concrete coarsening scores -/

/-- *The concrete coarsening-score space* `Ṙ_{Q,R}` (vdV thm:25.40, book p.380),
condExp-kernel form.

Constitutive (vdV §25.5.3 p.380): the coarsening scores are the observed scores `b`
with `E_R(b(X) | Y) = 0` a.s. In `L²` terms this is the kernel of the linear map
`b ↦ E[b ∘ M | comap Prod.fst]`: pull the observed score `b` back to `𝓨 × 𝓓` along
`M` via the Doob isometry `(doobL2Equiv hM).symm`, then take the conditional
expectation under the `Y`-coordinate σ-algebra `comap Prod.fst`. Realizing it as a
`LinearMap.ker` makes it manifestly a submodule; the equivalence with vdV's verbatim
fibre condition `∫ δ, b (M (y, δ)) ∂(r y) = 0` is `mem_concreteCoarseningScores_iff`. -/
noncomputable def concreteCoarseningScores :
    Submodule ℝ ↥(L2ZeroMean ((Q ⊗ₘ r).map M)) :=
  LinearMap.ker
    (((condExpL2 ℝ ℝ (measurable_fst.comap_le)).comp
      (((lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)).subtypeL).comp
        (((doobL2Equiv hM).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (L2ZeroMean ((Q ⊗ₘ r).map M)).subtypeL))).toLinearMap)

omit [IsProbabilityMeasure Q] [IsMarkovKernel r] in
/-- The Doob pullback `↑((doobL2Equiv hM).symm b)` of an observed function `b`
agrees `Q ⊗ₘ r`-a.e. with `b ∘ M` (behavioral identity for the Doob isometry). -/
private theorem obsPullback_ae_eq
    (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
    ((((doobL2Equiv hM).symm b :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ)
      =ᵐ[Q ⊗ₘ r] fun p => (b : 𝓧 → ℝ) (M p) := by
  have h := doobL2Equiv_comp_apply hM ((doobL2Equiv hM).symm b)
  rw [(doobL2Equiv hM).apply_symm_apply] at h
  exact h.symm

/-- Membership in `concreteCoarseningScores` is exactly vanishing of the
`comap Prod.fst` conditional expectation of the Doob pullback (unfolds the
`LinearMap.ker` definition). -/
private theorem mem_concrete_iff
    (b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    b ∈ concreteCoarseningScores Q r hM ↔
      ((condExpL2 ℝ ℝ measurable_fst.comap_le
          (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
              lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
              Lp ℝ 2 (Q ⊗ₘ r)) : Lp ℝ 2 (Q ⊗ₘ r))) = 0 := by
  unfold concreteCoarseningScores
  rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero]
  rfl

/-- *Verbatim fibre characterization of the concrete coarsening scores* (vdV
thm:25.40, book p.380).

Membership in `concreteCoarseningScores` is exactly vdV's per-fibre mean-zero
condition `E_R(b(X) | Y = y) = ∫ δ, b (M (y, δ)) ∂(r y) = 0` for `Q`-a.e. `y`. -/
theorem mem_concreteCoarseningScores_iff
    (b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    b ∈ concreteCoarseningScores Q r hM ↔
      ∀ᵐ y ∂Q, ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (y, δ)) ∂(r y) = 0 := by
  rw [mem_concrete_iff Q r hM b, Lp.eq_zero_iff_ae_eq_zero]
  -- `b ∘ M` is integrable (a.e. equal to the L² Doob pullback).
  have hbM_int :
      Integrable (fun p => ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M p)) (Q ⊗ₘ r) :=
    ((Lp.memLp (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r))).integrable one_le_two).congr
      (obsPullback_ae_eq Q r hM (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)))
  -- The conditional expectation of the pullback is a.e. the fibre integral.
  have hcond_ae :
      (((condExpL2 ℝ ℝ measurable_fst.comap_le
          (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
              lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
              Lp ℝ 2 (Q ⊗ₘ r)) : Lp ℝ 2 (Q ⊗ₘ r))) : 𝓨 × 𝓓 → ℝ)
        =ᵐ[Q ⊗ₘ r]
          fun p => ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (p.1, δ)) ∂(r p.1) := by
    have h1 := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) measurable_fst.comap_le
      (Lp.memLp (((doobL2Equiv hM).symm (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r)))
    rw [Lp.toLp_coeFn] at h1
    have h2 := condExp_congr_ae (m := MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›)
      (obsPullback_ae_eq Q r hM (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)))
    have h3 := condExp_compProd_fst Q r
      (fun p => ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M p)) hbM_int
    exact (h1.trans h2).trans h3
  constructor
  · intro hh
    have hh' :
        (fun p => ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (p.1, δ)) ∂(r p.1))
          =ᵐ[Q ⊗ₘ r] 0 := hcond_ae.symm.trans hh
    have h4 := Measure.ae_ae_of_ae_compProd hh'
    filter_upwards [h4] with y hy
    obtain ⟨_, hδ₀⟩ := hy.exists
    simpa using hδ₀
  · intro hh
    refine hcond_ae.trans ?_
    have hmp : MeasurePreserving (Prod.fst : 𝓨 × 𝓓 → 𝓨) (Q ⊗ₘ r) Q :=
      ⟨measurable_fst, Measure.fst_compProd Q r⟩
    have hcomp := hmp.quasiMeasurePreserving.ae_eq_comp
      (g := fun y => ∫ δ, ((b : Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (y, δ)) ∂(r y))
      (g' := 0) hh
    filter_upwards [hcomp] with p hp
    simpa using hp

/-! ### Orthogonality: concrete scores lie in the abstract complement -/

/-- *Concrete coarsening scores lie in the abstract complement* (vdV thm:25.40,
book p.380, orthogonality half).

Every `b` with `E_R(b | Y) = 0` a.s. is orthogonal to the whole observed `Q`-score
image `observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)`. This is the tower identity
`⟪Π a, b⟫ = ⟪a, b ∘ M⟫ = E[a(Y) · E_R(b | Y)] = 0` (`Operators.CAR.inner_observedTangent_piece`
+ `condExp_compProd_fst`). -/
theorem concreteCoarseningScores_le :
    concreteCoarseningScores Q r hM
      ≤ coarseningScores hM (Q ⊗ₘ r) (fullQTangent Q r) := by
  intro b hb
  have hpull0 := (mem_concrete_iff Q r hM b).mp hb
  simp only [coarseningScores, Submodule.mem_orthogonal]
  intro u hu
  rw [mem_observedTangent_iff] at hu
  obtain ⟨a, ha, rfl⟩ := hu
  have ha_meas :
      AEStronglyMeasurable[MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›]
        ((a : Lp ℝ 2 (Q ⊗ₘ r))) (Q ⊗ₘ r) :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (Submodule.mem_comap.mp ha)
  rw [Submodule.coe_inner,
    inner_observedTangent_piece hM (Q ⊗ₘ r) a (b : Lp ℝ 2 ((Q ⊗ₘ r).map M)),
    real_inner_comm,
    ← inner_condExpL2_eq_inner_fun measurable_fst.comap_le _ _ ha_meas,
    hpull0, inner_zero_left]

/-! ### Density: the abstract complement lies in the concrete space -/

/-- *The abstract complement lies in the concrete coarsening scores* (vdV thm:25.40,
book p.380, density half).

Any observed score `b` orthogonal to the whole observed `Q`-score image satisfies
`E_R(b | Y) = 0` a.s. Set `h := E[b ∘ M | comap Prod.fst]`, a member of
`fullQTangent` (uses the FULL `Q`-tangent = "`Q` completely unspecified", vdV p.380);
orthogonality gives `⟪Π h, b⟫ = 0`, whence `‖h‖² = 0`, `h = 0`, i.e.
`E(b(X) | Y) = 0`. -/
theorem le_concreteCoarseningScores :
    coarseningScores hM (Q ⊗ₘ r) (fullQTangent Q r)
      ≤ concreteCoarseningScores Q r hM := by
  intro g hg
  refine (mem_concrete_iff Q r hM g).mpr ?_
  refine (inner_self_eq_zero (𝕜 := ℝ)).mp ?_
  set pb : Lp ℝ 2 (Q ⊗ₘ r) :=
    (((doobL2Equiv hM).symm (g : Lp ℝ 2 ((Q ⊗ₘ r).map M)) :
        lpMeas ℝ ℝ (MeasurableSpace.comap M ‹MeasurableSpace 𝓧›) 2 (Q ⊗ₘ r)) :
        Lp ℝ 2 (Q ⊗ₘ r)) with hpb_def
  set hc : Lp ℝ 2 (Q ⊗ₘ r) :=
    ((condExpL2 ℝ ℝ measurable_fst.comap_le pb : Lp ℝ 2 (Q ⊗ₘ r))) with hc_def
  -- `pb` integrates to `0` (Doob-transport of `g ∈ L²₀`).
  have hpb_int : ∫ p, (pb : 𝓨 × 𝓓 → ℝ) p ∂(Q ⊗ₘ r) = 0 := by
    rw [hpb_def, integral_congr_ae (obsPullback_ae_eq Q r hM (g : Lp ℝ 2 ((Q ⊗ₘ r).map M))),
      ← integral_map hM.aemeasurable (Lp.aestronglyMeasurable (g : Lp ℝ 2 ((Q ⊗ₘ r).map M)))]
    exact (mem_L2ZeroMean_iff _ _).mp g.2
  -- hence `hc = E[pb | comap fst]` also integrates to `0`.
  have hc_int : ∫ p, (hc : 𝓨 × 𝓓 → ℝ) p ∂(Q ⊗ₘ r) = 0 := by
    have h := integral_condExpL2_eq (𝕜 := ℝ) measurable_fst.comap_le pb
      MeasurableSet.univ (measure_ne_top (Q ⊗ₘ r) _)
    rw [setIntegral_univ, setIntegral_univ] at h
    rw [hc_def, h]; exact hpb_int
  have hc_mem : (hc : Lp ℝ 2 (Q ⊗ₘ r)) ∈ L2ZeroMean (Q ⊗ₘ r) :=
    (mem_L2ZeroMean_iff _ _).mpr hc_int
  have hc_meas :
      AEStronglyMeasurable[MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›]
        (hc : 𝓨 × 𝓓 → ℝ) (Q ⊗ₘ r) := by
    rw [hc_def]; exact aestronglyMeasurable_condExpL2 measurable_fst.comap_le pb
  have ha_full : (⟨hc, hc_mem⟩ : ↥(L2ZeroMean (Q ⊗ₘ r))) ∈ fullQTangent Q r := by
    simp only [fullQTangent, Submodule.mem_comap]
    exact Submodule.coe_mem (condExpL2 ℝ ℝ measurable_fst.comap_le pb)
  -- Orthogonality of the observed image against the coarsening score `g`.
  have h_orth' : ⟪(hc : Lp ℝ 2 (Q ⊗ₘ r)), (pb : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ = 0 := by
    have key := inner_observedTangent_coarseningScore_eq_zero hM (Q ⊗ₘ r)
      (fullQTangent Q r) (a := ⟨hc, hc_mem⟩) ha_full hg
    rw [inner_observedTangent_piece hM (Q ⊗ₘ r) ⟨hc, hc_mem⟩
      (g : Lp ℝ 2 ((Q ⊗ₘ r).map M))] at key
    exact key
  calc ⟪(hc : Lp ℝ 2 (Q ⊗ₘ r)), (hc : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ
      = ⟪(pb : Lp ℝ 2 (Q ⊗ₘ r)), (hc : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ :=
        inner_condExpL2_eq_inner_fun measurable_fst.comap_le pb hc hc_meas
    _ = ⟪(hc : Lp ℝ 2 (Q ⊗ₘ r)), (pb : Lp ℝ 2 (Q ⊗ₘ r))⟫_ℝ := real_inner_comm _ _
    _ = 0 := h_orth'

/-! ### Identification of the two coarsening-score spaces -/

/-- *Coarsening-score identification* (vdV thm:25.40, book p.380): the abstract
orthogonal complement of the observed `Q`-score image equals the concrete
`E_R(b | Y) = 0` coarsening scores. -/
theorem coarseningScores_eq_concrete :
    coarseningScores hM (Q ⊗ₘ r) (fullQTangent Q r) = concreteCoarseningScores Q r hM :=
  le_antisymm (le_concreteCoarseningScores Q r hM) (concreteCoarseningScores_le Q r hM)

/-- *Closed observed-Q tangent as the orthogonal complement of the concrete
coarsening scores* (vdV thm:25.40, book p.380).

This is the closed-tangent form of `coarseningScores_eq_concrete`: taking a
second orthogonal complement turns the abstract observed tangent into its
topological closure. It is the general operator-layer bridge consumed by
concrete coarsening examples. -/
theorem closedObservedQTangent_eq_concreteOrthogonal :
    (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)).topologicalClosure
      = (concreteCoarseningScores Q r hM)ᗮ := by
  letI hcsE : CompleteSpace ↥(L2ZeroMean ((Q ⊗ₘ r).map M)) :=
    (L2ZeroMean_isClosed ((Q ⊗ₘ r).map M)).completeSpace_coe
  rw [← coarseningScores_eq_concrete Q r hM, coarseningScores]
  exact (@Submodule.orthogonal_orthogonal_eq_closure ℝ _ _ _ _ _ hcsE).symm

/-! ### Conditional-QMD/CAR nuisance scores -/

/-- Generators of the *actual supplied* conditional-QMD/CAR nuisance-score space
at fixed dominating measure `ν` (vdV §25.5.3, book p.380).

The set quantifies over every supplied conditional-QMD path and every proof that
the path satisfies CAR, and records its observed score. Edge behavior: if no such
paths are supplied, the generator set is empty. This is not, in general, the
maximal concrete fibre-mean-zero space. -/
noncomputable def carNuisanceScoreGenerators
    (hM : Measurable M) -- the observed coarsening map is measurable.
    (ν : Measure 𝓓) [SigmaFinite ν] :
    Set ↥(L2ZeroMean ((Q ⊗ₘ r).map M)) := by
  exact {b | ∃ (γ : ConditionalQMDPath Q ν r) (hCAR : IsCARFamily M γ),
    b = conditionalQMDObservedScore M hM γ hCAR}

/-- The *actual supplied* conditional-QMD/CAR nuisance-score space at fixed `ν`
(vdV §25.5.3, book p.380): the closed linear span of
`carNuisanceScoreGenerators`.

This space records the score paths represented by `ConditionalQMDPath` and
`IsCARFamily`. It need not equal the maximal concrete fibre-mean-zero space.
Edge behavior: a constant family, or an empty generator set, yields only the
closed span of the represented scores, in particular the zero space when the
generator set is empty. -/
noncomputable def carNuisanceScores
    (hM : Measurable M) -- the observed coarsening map is measurable.
    (ν : Measure 𝓓) [SigmaFinite ν] :
    Submodule ℝ ↥(L2ZeroMean ((Q ⊗ₘ r).map M)) := by
  exact (Submodule.span ℝ (carNuisanceScoreGenerators Q r hM ν)).topologicalClosure

/-- Every observed score supplied by a conditional-QMD/CAR path belongs to the
maximal concrete fibre-mean-zero coarsening-score space (vdV thm:25.40, p.380). -/
theorem conditionalQMDObservedScore_mem_concrete
    {ν : Measure 𝓓} [SigmaFinite ν]
    (γ : ConditionalQMDPath Q ν r)
    (hCAR : IsCARFamily M γ) : -- the supplied conditional path satisfies CAR.
    conditionalQMDObservedScore M hM γ hCAR ∈
      concreteCoarseningScores Q r hM := by
  rw [mem_concreteCoarseningScores_iff]
  have hpull := Measure.ae_ae_of_ae_compProd
    (conditionalQMDObservedScore_pullback M hM γ hCAR)
  filter_upwards [hpull, conditionalScore_fibre_mean_zero γ] with y hy hy_zero
  calc
    ∫ δ,
        (((conditionalQMDObservedScore M hM γ hCAR :
            ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
            Lp ℝ 2 ((Q ⊗ₘ r).map M)) : 𝓧 → ℝ) (M (y, δ)) ∂(r y)
        = ∫ δ, γ.score y δ ∂(r y) := integral_congr_ae (by
            simpa only [Function.uncurry] using! hy)
    _ = 0 := hy_zero

/-- The actual supplied conditional-QMD/CAR nuisance span is contained in the
maximal concrete fibre-mean-zero coarsening-score space (vdV thm:25.40, p.380).
No reverse inclusion is claimed. -/
theorem carNuisanceScores_le_concreteCoarseningScores
    (ν : Measure 𝓓) [SigmaFinite ν] :
    carNuisanceScores Q r hM ν ≤ concreteCoarseningScores Q r hM := by
  unfold carNuisanceScores
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro b ⟨γ, hCAR, rfl⟩
    exact conditionalQMDObservedScore_mem_concrete Q r hM γ hCAR
  · unfold concreteCoarseningScores
    exact ContinuousLinearMap.isClosed_ker _

/-- The observed `Q`-tangent image is orthogonal to every actual supplied
conditional-QMD/CAR nuisance score (vdV thm:25.40, p.380). -/
theorem observedQTangent_orthogonal_carNuisanceScores
    (ν : Measure 𝓓) [SigmaFinite ν]
    {a : ↥(L2ZeroMean (Q ⊗ₘ r))} (ha : a ∈ fullQTangent Q r)
    {b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))}
    (hb : b ∈ carNuisanceScores Q r hM ν) :
    ⟪(informationLossOperator hM (Q ⊗ₘ r) a :
        Lp ℝ 2 ((Q ⊗ₘ r).map M)),
      (b : Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ = 0 := by
  apply CARScores.inner_observedTangent_coarseningScore_eq_zero
    hM (Q ⊗ₘ r) (fullQTangent Q r) ha
  rw [coarseningScores_eq_concrete Q r hM]
  exact carNuisanceScores_le_concreteCoarseningScores Q r hM ν hb

/-! ### CAR-carrying decomposition -/

/-- *vdV thm:25.40 — CAR observed-tangent decomposition* (book p.380).

Every mean-zero observed score `g ∈ L²₀(P_obs)` splits orthogonally as `g = p + b`,
where:
  * `p ∈ (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)).topologicalClosure` — a
    limit of conditional-expectation images `E_{Q,R}(a(Y) | X)` of full `Q`-scores
    `a` (the closure is genuine: the tangent set need not be closed), and
  * `b ∈ concreteCoarseningScores Q r hM` — a *concrete* coarsening score, i.e. an
    observed function with `E_R(b(X) | Y) = 0` a.s.,

with `p ⊥ b`. Unlike the abstract `observedTangent_orthogonal_decomposition` (whose
`b` sits in the opaque complement `(observedTangent …)ᗮ`), here `b` carries the
book's explicit `E_R(b | Y) = 0` CAR content via `coarseningScores_eq_concrete`. -/
theorem car_observed_tangent_decomposition
    (g : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    ∃ p ∈ (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)).topologicalClosure,
      ∃ b ∈ concreteCoarseningScores Q r hM,
        g = p + b ∧
        ⟪(p : Lp ℝ 2 ((Q ⊗ₘ r).map M)), (b : Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ = 0 := by
  obtain ⟨p, hp, b, hb, hgpb, hpb⟩ :=
    observedTangent_orthogonal_decomposition hM (Q ⊗ₘ r) (fullQTangent Q r) g
  refine ⟨p, hp, b, ?_, hgpb, hpb⟩
  rwa [← coarseningScores_eq_concrete Q r hM]

/-- **vdV thm:25.40 (book p.380), represented scores and maximal tangent.**

First, every conditional-QMD path that actually satisfies CAR supplies an
observed nuisance score lying in both the actual fixed-`ν` closed span and the
maximal concrete fibre-mean-zero space. Second, independently, the book-chosen
maximal concrete tangent set has the existing orthogonal decomposition/density
property. The two clauses deliberately do **not** assert that the actual supplied
span equals the maximal concrete space; constant families and empty generators
show why such an identification is unavailable in general. -/
theorem car_actual_and_maximal_tangent_2540
    -- USER-INPUT: a fixed sigma-finite conditional dominator for the supplied
    -- conditional QMD paths; vdV Lemma 25.40.
    (ν : Measure 𝓓) [SigmaFinite ν] :
    (∀ (γ : ConditionalQMDPath Q ν r) (hCAR : IsCARFamily M γ),
      conditionalQMDObservedScore M hM γ hCAR ∈
        carNuisanceScores Q r hM ν ⊓ concreteCoarseningScores Q r hM) ∧
    (∀ g : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)),
      ∃ p ∈ (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)).topologicalClosure,
        ∃ b ∈ concreteCoarseningScores Q r hM,
          g = p + b ∧
          ⟪(p : Lp ℝ 2 ((Q ⊗ₘ r).map M)),
            (b : Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ = 0) := by
  constructor
  · intro γ hCAR
    refine ⟨?_, conditionalQMDObservedScore_mem_concrete Q r hM γ hCAR⟩
    unfold carNuisanceScores
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨γ, hCAR, rfl⟩
  · exact car_observed_tangent_decomposition Q r hM

/-! ### vdV Lemma 25.41: IPW influence-function characterization -/

open AsymptoticStatistics.Core.Pathwise in
/-- *vdV lem:25.41 — IPW characterization of observed influence functions* (book
p.381-382).

With the censoring mechanism `R` known, the model `P_{Q,R}` (`Q ∈ 𝒬`, `R` fixed) has
observed tangent `observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)` — the `Π`-images
of the full `Q`-scores — since the coarsening directions are *not* tangent (`R` is
fixed). Influence functions for `χ(Q)` therefore form the affine space
`Π φ_full + (observedTangent)ᗮ`, and `(observedTangent)ᗮ = concreteCoarseningScores`
by `coarseningScores_eq_concrete`. This is vdV's statement that any influence
function is `1{δ∈C}/R(C|y)·χ_Q(Y) + b(x)`, with `b` ranging over the scores
satisfying `E_R(b | Y) = 0`, uniquely.

The statement assumes an IPW representer `φ_full` whose `Π`-image is an influence
function for `χ(Q)`. The concrete form `1{δ∈C}/R(C|y)·χ_Q(Y)` additionally requires
the `𝓨 × 𝓓` product structure, the complete-case set `C`, known `R`, and
`R(C|y)` bounded away from zero. -/
theorem ipw_influence_characterization
    -- the observed pathwise derivative `χ̇_Q`.
    (dψ_obs : (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) →L[ℝ] ℝ)
    -- the IPW-reweighted full-data representer `1{δ∈C}/R(C|y)·χ_Q(Y)`.
    (φ_full : ↥(L2ZeroMean (Q ⊗ₘ r)))
    -- `Π φ_full` is an influence function for `χ(Q)`.
    (h_ipw : letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
          Measure.isProbabilityMeasure_map hM.aemeasurable
        IsInfluenceFunction ((Q ⊗ₘ r).map M)
          (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) dψ_obs
          (informationLossOperator hM (Q ⊗ₘ r) φ_full))
    (φ_obs : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    IsInfluenceFunction ((Q ⊗ₘ r).map M)
        (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) dψ_obs φ_obs
      ↔ ∃ b ∈ concreteCoarseningScores Q r hM,
          φ_obs = informationLossOperator hM (Q ⊗ₘ r) φ_full + b := by
  haveI hpm : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  -- Membership in the concrete score space is equivalent to membership in
  -- the orthogonal complement of the observed tangent.
  have hb_orth_iff : ∀ b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)),
      b ∈ concreteCoarseningScores Q r hM ↔
        b ∈ (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r))ᗮ := by
    intro b
    rw [← coarseningScores_eq_concrete Q r hM]; rfl
  constructor
  · -- ⟹ : any influence function differs from `Π φ_full` by a coarsening score.
    intro h
    refine ⟨φ_obs - informationLossOperator hM (Q ⊗ₘ r) φ_full, ?_, by abel⟩
    rw [hb_orth_iff, Submodule.mem_orthogonal]
    intro u hu
    have e1 : ⟪(u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))), φ_obs⟫_ℝ = dψ_obs ⟨u, hu⟩ := by
      rw [real_inner_comm]; exact h ⟨u, hu⟩
    have e2 : ⟪(u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))),
        informationLossOperator hM (Q ⊗ₘ r) φ_full⟫_ℝ = dψ_obs ⟨u, hu⟩ := by
      rw [real_inner_comm]; exact h_ipw ⟨u, hu⟩
    calc
      ⟪(u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))),
          φ_obs - informationLossOperator hM (Q ⊗ₘ r) φ_full⟫_ℝ =
          ⟪(u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))), φ_obs⟫_ℝ -
            ⟪(u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))),
              informationLossOperator hM (Q ⊗ₘ r) φ_full⟫_ℝ := inner_sub_right _ _ _
      _ = dψ_obs ⟨u, hu⟩ - dψ_obs ⟨u, hu⟩ := congrArg₂ (fun x y : ℝ ↦ x - y) e1 e2
      _ = 0 := sub_self _
  · -- ⟸ : `Π φ_full + b` (with `b` a coarsening score) is an influence function.
    rintro ⟨b, hb, rfl⟩
    have hb_orth := (hb_orth_iff b).mp hb
    intro g
    calc
      ⟪informationLossOperator hM (Q ⊗ₘ r) φ_full + b,
          (g : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)))⟫_ℝ =
          ⟪informationLossOperator hM (Q ⊗ₘ r) φ_full,
            (g : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)))⟫_ℝ +
          ⟪b, (g : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)))⟫_ℝ := inner_add_left _ _ _
      _ = dψ_obs g + 0 := congrArg₂ (fun x y : ℝ ↦ x + y) (h_ipw g)
        (Submodule.inner_left_of_mem_orthogonal g.2 hb_orth)
      _ = dψ_obs g := add_zero _

/-! ### Lemma 25.41 and restricted 25.42 candidate endpoint -/

/-- Every full `Q`-tangent direction under `Q ⊗ₘ r` is the first-coordinate lift
of an `L²₀(Q)` score (vdV §25.5.3, pp.380–382). Equivalently,
`fullQTangent`, defined by `comap Prod.fst`-measurability, consists exactly of
the scores represented by `qScoreLift`. -/
theorem mem_fullQTangent_iff_eq_qScoreLift
    (a : ↥(L2ZeroMean (Q ⊗ₘ r))) :
    a ∈ fullQTangent Q r ↔
      ∃ s : ↥(L2ZeroMean Q), a = qScoreLift Q r s := by
  constructor
  · intro ha
    have ha_meas : (a : Lp ℝ 2 (Q ⊗ₘ r)) ∈
        lpMeas ℝ ℝ (MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›) 2 (Q ⊗ₘ r) :=
      Submodule.mem_comap.mp ha
    let aMeas :
        lpMeas ℝ ℝ (MeasurableSpace.comap Prod.fst ‹MeasurableSpace 𝓨›) 2 (Q ⊗ₘ r) :=
      ⟨(a : Lp ℝ 2 (Q ⊗ₘ r)), ha_meas⟩
    let sRaw : 𝓨 → ℝ :=
      ((doobL2Equiv measurable_fst aMeas : Lp ℝ 2 ((Q ⊗ₘ r).map Prod.fst)) : 𝓨 → ℝ)
    have hsRaw_mem : MemLp sRaw 2 Q := by
      rw [← Measure.fst_compProd Q r]
      exact Lp.memLp _
    have hsRaw_comp : (fun p : 𝓨 × 𝓓 ↦ sRaw p.1) =ᵐ[Q ⊗ₘ r]
        ((a : Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ) := by
      simpa only [sRaw, aMeas] using doobL2Equiv_comp_apply measurable_fst aMeas
    have hsRaw_mean : ∫ y, sRaw y ∂Q = 0 := by
      calc
        ∫ y, sRaw y ∂Q = ∫ y, sRaw y ∂((Q ⊗ₘ r).map Prod.fst) := by
          exact congrArg (fun μ : Measure 𝓨 ↦ ∫ y, sRaw y ∂μ)
            (Measure.fst_compProd Q r).symm
        _ = ∫ p, sRaw p.1 ∂(Q ⊗ₘ r) := by
          apply integral_map measurable_fst.aemeasurable
          simpa only [sRaw] using
            Lp.aestronglyMeasurable
              (doobL2Equiv measurable_fst aMeas : Lp ℝ 2 ((Q ⊗ₘ r).map Prod.fst))
        _ = ∫ p, ((a : Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ) p ∂(Q ⊗ₘ r) :=
          integral_congr_ae hsRaw_comp
        _ = 0 := (mem_L2ZeroMean_iff (Q ⊗ₘ r) (a : Lp ℝ 2 (Q ⊗ₘ r))).mp a.2
    let s : ↥(L2ZeroMean Q) :=
      AsymptoticStatistics.Core.CandidateIF.toL2ZeroMean
        { raw := sRaw, memLp2 := hsRaw_mem, mean_zero := hsRaw_mean }
    refine ⟨s, ?_⟩
    have hs_ae : (((s : Lp ℝ 2 Q) : 𝓨 → ℝ)) =ᵐ[Q] sRaw := by
      exact AsymptoticStatistics.Core.CandidateIF.coeFn_toL2ZeroMean _
    have hfst : MeasurePreserving (Prod.fst : 𝓨 × 𝓓 → 𝓨) (Q ⊗ₘ r) Q :=
      ⟨measurable_fst, Measure.fst_compProd Q r⟩
    have hs_comp := hfst.quasiMeasurePreserving.ae_eq_comp hs_ae
    have hq_ae :
        (((qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ))
          =ᵐ[Q ⊗ₘ r] qScoreLiftRaw Q s := by
      unfold qScoreLift
      exact AsymptoticStatistics.Core.CandidateIF.coeFn_toL2ZeroMean _
    apply Subtype.ext
    apply Lp.ext
    exact hsRaw_comp.symm.trans (hs_comp.symm.trans hq_ae.symm)
  · rintro ⟨s, rfl⟩
    simp only [fullQTangent, Submodule.mem_comap]
    rw [mem_lpMeas_iff_aestronglyMeasurable]
    have hraw :
        StronglyMeasurable[
          MeasurableSpace.comap (Prod.fst : 𝓨 × 𝓓 → 𝓨) ‹MeasurableSpace 𝓨›]
          (qScoreLiftRaw (𝓓 := 𝓓) Q s) := by
      exact (Lp.stronglyMeasurable (s : Lp ℝ 2 Q)).comp_measurable
        (comap_measurable (Prod.fst : 𝓨 × 𝓓 → 𝓨))
    have hq_ae :
        (((qScoreLift Q r s : Lp ℝ 2 (Q ⊗ₘ r)) : 𝓨 × 𝓓 → ℝ))
          =ᵐ[Q ⊗ₘ r] qScoreLiftRaw Q s := by
      unfold qScoreLift
      exact AsymptoticStatistics.Core.CandidateIF.coeFn_toL2ZeroMean _
    exact hraw.aestronglyMeasurable.congr hq_ae.symm

open AsymptoticStatistics.Core.Pathwise in
/-- **vdV Lemma 25.41 (book pp.381–382), explicit complete-case base
influence function.**

Starting from a full-`Q` influence representer `χ`, the explicit IPW formula
constructed in `CompleteCaseIPW` represents the observed derivative on the
fixed-`R` observed `Q`-tangent.  The additional hypothesis
`hDerivativeRestriction`: it says that the observed derivative agrees with the
full derivative on the canonical coarsened `Q`-score lift.  It does not assume
the IPW influence-function conclusion. -/
theorem completeCaseIPW_influence_2541
    (cc : CompleteCaseData M) -- complete-case observation data.
    (ε : ℝ) (hε : 0 < ε) -- vdV Lemma 25.41 positivity constant.
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y)
      -- vdV Lemma 25.41, `R(C|Y)` bounded away from zero.
    (dψQ : (⊤ : Submodule ℝ ↥(L2ZeroMean Q)) →L[ℝ] ℝ)
      -- derivative of the differentiable full-`Q` parameter.
    (χ : ↥(L2ZeroMean Q))
      -- a full-`Q` influence representer from vdV Lemma 25.41.
    (hχ : IsInfluenceFunction Q (⊤ : Submodule ℝ ↥(L2ZeroMean Q)) dψQ χ)
      -- `χ` represents the full-`Q` derivative.
    (dψObs :
      (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) →L[ℝ] ℝ)
      -- derivative of the induced observed parameter.
    (hDerivativeRestriction : ∀ s : ↥(L2ZeroMean Q),
      dψObs
          ⟨informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s),
            informationLossOperator_mem_observedTangent hM (Q ⊗ₘ r)
              (fullQTangent Q r) ((mem_fullQTangent_iff_eq_qScoreLift Q r
                (qScoreLift Q r s)).2 ⟨s, rfl⟩)⟩ =
        dψQ ⟨s, Submodule.mem_top⟩)
      -- This derivative-restriction hypothesis only
      -- identifies the two derivative encodings on canonical `Q`-score lifts.
    : letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
        Measure.isProbabilityMeasure_map hM.aemeasurable
      IsInfluenceFunction ((Q ⊗ₘ r).map M)
        (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) dψObs
        (completeCaseIPW hM Q r cc χ ε hε hπ) := by
  letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  intro g
  obtain ⟨a, ha, hga⟩ :=
    (mem_observedTangent_iff hM (Q ⊗ₘ r) (fullQTangent Q r)
      (g : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)))).mp g.2
  obtain ⟨s, has⟩ := (mem_fullQTangent_iff_eq_qScoreLift Q r a).mp ha
  subst a
  have hg : g =
      ⟨informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s),
        informationLossOperator_mem_observedTangent hM (Q ⊗ₘ r)
          (fullQTangent Q r) ((mem_fullQTangent_iff_eq_qScoreLift Q r
            (qScoreLift Q r s)).2 ⟨s, rfl⟩)⟩ := by
    apply Subtype.ext
    exact hga.symm
  subst g
  calc
    ⟪(completeCaseIPW hM Q r cc χ ε hε hπ :
          Lp ℝ 2 ((Q ⊗ₘ r).map M)),
        (informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s) :
          Lp ℝ 2 ((Q ⊗ₘ r).map M))⟫_ℝ =
        ⟪(χ : Lp ℝ 2 Q), (s : Lp ℝ 2 Q)⟫_ℝ :=
      inner_completeCaseIPW_informationLoss_qScoreLift hM Q r cc χ s ε hε hπ
    _ = dψQ ⟨s, Submodule.mem_top⟩ := by
      simpa only [Submodule.coe_inner] using hχ ⟨s, Submodule.mem_top⟩
    _ = dψObs
        ⟨informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s),
          informationLossOperator_mem_observedTangent hM (Q ⊗ₘ r)
            (fullQTangent Q r) ((mem_fullQTangent_iff_eq_qScoreLift Q r
              (qScoreLift Q r s)).2 ⟨s, rfl⟩)⟩ :=
      (hDerivativeRestriction s).symm

open AsymptoticStatistics.Core.Pathwise in
/-- **vdV Lemma 25.41 (book pp.381–382), explicit affine characterization.**

An observed influence function is exactly the explicit complete-case IPW base
plus a concrete fibre-mean-zero coarsening score.  The base influence property
is derived by `completeCaseIPW_influence_2541`. -/
theorem completeCaseIPW_characterization_2541
    -- USER-INPUT: complete-case observation interface and selection probability
    -- bounded away from zero; vdV Lemma 25.41.
    (cc : CompleteCaseData M) -- complete-case observation data.
    (ε : ℝ) (hε : 0 < ε) -- vdV Lemma 25.41 positivity constant.
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y)
      -- vdV Lemma 25.41 bounded-away-from-zero condition.
    -- USER-INPUT: full-data derivative and influence representer.
    (dψQ : (⊤ : Submodule ℝ ↥(L2ZeroMean Q)) →L[ℝ] ℝ)
      -- derivative of the differentiable full-`Q` parameter.
    (χ : ↥(L2ZeroMean Q)) -- full-`Q` influence representer.
    (hχ : IsInfluenceFunction Q (⊤ : Submodule ℝ ↥(L2ZeroMean Q)) dψQ χ)
      -- `χ` represents the full-`Q` derivative.
    -- USER-INPUT: observed derivative agrees with the full-data derivative on
    -- canonical score lifts; vdV Lemma 25.41.
    (dψObs :
      (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) →L[ℝ] ℝ)
      -- derivative of the induced observed parameter.
    (hDerivativeRestriction : ∀ s : ↥(L2ZeroMean Q),
      dψObs
          ⟨informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s),
            informationLossOperator_mem_observedTangent hM (Q ⊗ₘ r)
              (fullQTangent Q r) ((mem_fullQTangent_iff_eq_qScoreLift Q r
                (qScoreLift Q r s)).2 ⟨s, rfl⟩)⟩ =
        dψQ ⟨s, Submodule.mem_top⟩)
      -- agreement of the full and observed derivatives on canonical score lifts.
    (φobs : ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) :
    letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    IsInfluenceFunction ((Q ⊗ₘ r).map M)
        (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) dψObs φobs ↔
      ∃ b ∈ concreteCoarseningScores Q r hM,
        φobs = completeCaseIPW hM Q r cc χ ε hε hπ + b := by
  letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  have hbase := completeCaseIPW_influence_2541 Q r hM cc ε hε hπ
    dψQ χ hχ dψObs hDerivativeRestriction
  have hchar := ipw_influence_characterization Q r hM dψObs
    (completeCaseIPWFull hM Q r cc χ ε hε hπ) (by
      rw [informationLoss_completeCaseIPWFull hM Q r cc χ ε hε hπ]
      exact hbase) φobs
  rwa [informationLoss_completeCaseIPWFull hM Q r cc χ ε hε hπ] at hchar

/-- The explicit candidate in vdV Corollary 25.42 (book p.382): the complete-case
IPW influence function minus its orthogonal projection onto the actual fixed-`ν`
CAR nuisance-score span.

Edge behavior: the definition requires the standard orthogonal-projection
instance for the actual closed nuisance span; it does not replace that span by
the larger maximal concrete fibre-mean-zero space. -/
noncomputable def completeCaseIPWMinusCARProjection
    (ν : Measure 𝓓) [SigmaFinite ν]
    [hproj : (carNuisanceScores Q r hM ν).HasOrthogonalProjection]
    (cc : CompleteCaseData M) (χ : ↥(L2ZeroMean Q))
    (ε : ℝ) (hε : 0 < ε)
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y) :
    ↥(L2ZeroMean ((Q ⊗ₘ r).map M)) :=
  completeCaseIPW hM Q r cc χ ε hε hπ -
    (carNuisanceScores Q r hM ν).starProjection
      (completeCaseIPW hM Q r cc χ ε hε hπ)

open AsymptoticStatistics.Core.Pathwise in
/-- **Restricted subtract-projection statement for Corollary 25.42 (book p.382).**

The explicit Lemma 25.41 IPW candidate with `b = 0`, minus its orthogonal projection
onto the supplied actual `carNuisanceScores`, is an `IsInfluenceFunction` on the
supplied `observedQTangent ⊔ carNuisanceScores`. This does not characterize every
influence function, identify the full `R`-score tangent, establish an EIF, or prove
membership in a total tangent space. -/
theorem completeCaseIPW_subtract_projection_2542
    (ν : Measure 𝓓) [SigmaFinite ν] -- fixed conditional dominator.
    [hproj : (carNuisanceScores Q r hM ν).HasOrthogonalProjection]
      -- standard projection instance for the closed actual CAR span.
    (cc : CompleteCaseData M) -- complete-case observation data.
    (ε : ℝ) (hε : 0 < ε) -- vdV Lemma 25.41 positivity constant.
    (hπ : ∀ᵐ y ∂Q, ε ≤ selectionProbability r cc y)
      -- vdV Lemma 25.41 bounded-away-from-zero condition.
    (dψQ : (⊤ : Submodule ℝ ↥(L2ZeroMean Q)) →L[ℝ] ℝ)
      -- derivative of the differentiable full-`Q` parameter.
    (χ : ↥(L2ZeroMean Q)) -- full-`Q` influence representer.
    (hχ : IsInfluenceFunction Q (⊤ : Submodule ℝ ↥(L2ZeroMean Q)) dψQ χ)
      -- `χ` represents the full-`Q` derivative.
    (dψObs :
      (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)) →L[ℝ] ℝ)
      -- derivative on the observed `Q` tangent.
    (hDerivativeRestriction : ∀ s : ↥(L2ZeroMean Q),
      dψObs
          ⟨informationLossOperator hM (Q ⊗ₘ r) (qScoreLift Q r s),
            informationLossOperator_mem_observedTangent hM (Q ⊗ₘ r)
              (fullQTangent Q r) ((mem_fullQTangent_iff_eq_qScoreLift Q r
                (qScoreLift Q r s)).2 ⟨s, rfl⟩)⟩ =
        dψQ ⟨s, Submodule.mem_top⟩)
      -- derivative restriction between the full and observed models.
    (dψTotal :
      ((observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r) ⊔
        carNuisanceScores Q r hM ν) :
          Submodule ℝ ↥(L2ZeroMean ((Q ⊗ₘ r).map M))) →L[ℝ] ℝ)
      -- derivative on the actual combined `Q`/`R` tangent.
    (hQAgreement : ∀ (u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)))
        (hu : u ∈ observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)),
      dψTotal ⟨u, Submodule.mem_sup_left hu⟩ = dψObs ⟨u, hu⟩)
      -- the total derivative restricts to the observed `Q` derivative.
    (hRZero : ∀ (b : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)))
        (hb : b ∈ carNuisanceScores Q r hM ν),
      dψTotal ⟨b, Submodule.mem_sup_right hb⟩ = 0)
      -- χ(Q) has zero derivative along actual fixed-`Q` CAR paths.
    : letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
        Measure.isProbabilityMeasure_map hM.aemeasurable
      IsInfluenceFunction ((Q ⊗ₘ r).map M)
        (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r) ⊔
          carNuisanceScores Q r hM ν) dψTotal
        (completeCaseIPWMinusCARProjection Q r hM ν cc χ ε hε hπ) := by
  letI : IsProbabilityMeasure ((Q ⊗ₘ r).map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  have hbase := completeCaseIPW_influence_2541 Q r hM cc ε hε hπ
    dψQ χ hχ dψObs hDerivativeRestriction
  have hOrth : ∀ u ∈ observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r),
      ∀ v ∈ carNuisanceScores Q r hM ν, ⟪u, v⟫_ℝ = (0 : ℝ) := by
    intro u hu v hv
    obtain ⟨a, ha, hua⟩ :=
      (mem_observedTangent_iff hM (Q ⊗ₘ r) (fullQTangent Q r) u).mp hu
    rw [← hua]
    exact observedQTangent_orthogonal_carNuisanceScores Q r hM ν ha hv
  have hMain : ∀ (u : ↥(L2ZeroMean ((Q ⊗ₘ r).map M)))
      (hu : u ∈ observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r)),
      ⟪completeCaseIPW hM Q r cc χ ε hε hπ, u⟫_ℝ =
        dψTotal ⟨u, Submodule.mem_sup_left hu⟩ := by
    intro u hu
    calc
      ⟪completeCaseIPW hM Q r cc χ ε hε hπ, u⟫_ℝ =
          dψObs ⟨u, hu⟩ := hbase ⟨u, hu⟩
      _ = dψTotal ⟨u, Submodule.mem_sup_left hu⟩ := (hQAgreement u hu).symm
  unfold completeCaseIPWMinusCARProjection
  exact @AsymptoticStatistics.Core.EIF.influence_on_sup_of_subtract_proj_nuisance
    _ _ ((Q ⊗ₘ r).map M) _
    (observedTangent hM (Q ⊗ₘ r) (fullQTangent Q r))
    (carNuisanceScores Q r hM ν) hproj dψTotal
    (completeCaseIPW hM Q r cc χ ε hε hπ) hOrth hMain hRZero

end AsymptoticStatistics.Operators.CoarseningScoreIdentification
