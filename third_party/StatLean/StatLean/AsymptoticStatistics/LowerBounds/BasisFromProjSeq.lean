module
public import StatLean.AsymptoticStatistics.LowerBounds.ProjSeqToEif
public import StatLean.AsymptoticStatistics.ParametricFamily.SubmodelFromScores
public import StatLean.AsymptoticStatistics.Core.MassMethod

@[expose] public section

/-!
# Basis from a projection sequence

Given a `TangentSpec P` with linear-closed carrier of essentially-bounded
elements, and the `proj_seq_to_eif`-style projection sequence
`p : ℕ → ↥(L2ZeroMean P)` of an EIF onto an increasing family of
finite-dim subspaces, this file provides the 1-element basis
`g_P 0 := (1/‖p m‖) • p m` with variance exactly `‖p m‖²` at each
`m` with `‖p m‖ > 0`.

The 1-element basis avoids the cos²-mixing required by a general-σ
construction; in 1-dim tangent spaces only the proj_seq-image σ values
are ever needed.

Headline declaration: `basis_at_proj_m_pos`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics.LowerBounds.BasisFromProjSeq

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.MassMethod
open AsymptoticStatistics.ParametricFamily

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Basis from projection sequence (positive-norm case).**

Given a `TangentSpec P` with linear-closed carrier whose elements are
essentially bounded, an EIF `IF_eff` in the tangent space, the
`proj_seq_to_eif`-style projection sequence data, and an index `m` with
`0 < ‖p m‖`: produce a 1-element orthonormal basis
`g_P : Fin 1 → ↥(L2ZeroMean P)` with variance exactly `‖p m‖²`.

The basis is `g_P 0 := (1/‖p m‖) • p m`, the unit-normalized projection.

Properties verified:
* `g_P 0 ∈ T_set.carrier` (carrier is linearly closed, `p m ∈ V m ⊆ carrier`).
* `IsBoundedMixtureScores g_P` (essentially bounded only; closure under linear
  combinations from `IsEssBoundedMixtureScore.{smul, finsetSum}`).
* `Orthonormal ℝ (...)` (1-element with unit norm).
* `Submodule.span` membership for arbitrary linear combinations of `g_P`.
* `∑ j, ⟨IF_eff, g_P j⟩² = ‖p m‖²` (from the projection orthogonality
  `IF_eff - p m ⊥ V m`). -/
theorem basis_at_proj_m_pos
    (T_set : TangentSpec P)
    (h_lin_smul : ∀ x ∈ T_set.carrier, ∀ t : ℝ, t • x ∈ T_set.carrier)
    (h_lin_add : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      x + y ∈ T_set.carrier)
    (h_lin_zero : (0 : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (h_carrier_ess : ∀ g ∈ T_set.carrier, IsEssBoundedMixtureScore g)
    (IF_eff : ↥(L2ZeroMean P))
    (V : ℕ → Submodule ℝ ↥(L2ZeroMean P))
    (p : ℕ → ↥(L2ZeroMean P))
    (hV_span : ∀ m, ∃ S : Finset ↥(L2ZeroMean P),
      (↑S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
      V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P)))
    (hV_proj : ∀ m, p m ∈ V m ∧ IF_eff - p m ∈ (V m)ᗮ)
    (m : ℕ) (h_pm_pos : 0 < ‖(p m : ↥(L2ZeroMean P))‖) :
    ∃ (m_dim : ℕ) (g_P : Fin m_dim → ↥(L2ZeroMean P))
      (_hg : IsBoundedMixtureScores g_P)
      (_h_orth : Orthonormal ℝ
        (fun i => ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P))),
      (∀ j : Fin m_dim, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∀ θ : EuclideanSpace ℝ (Fin m_dim),
        (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) :
          ↥(L2ZeroMean P)) ∈ T_set.carrier) ∧
      (∑ j : Fin m_dim,
        (@inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (g_P j)) ^ 2
          = ‖(p m : ↥(L2ZeroMean P))‖ ^ 2) := by
  -- Set up the carrier as a submodule using linear-closure hypotheses.
  let carrier_sub : Submodule ℝ ↥(L2ZeroMean P) :=
    { carrier := T_set.carrier
      zero_mem' := h_lin_zero
      add_mem' := fun {x y} hx hy => h_lin_add x hx y hy
      smul_mem' := fun c {x} hx => h_lin_smul x hx c }
  -- p m ∈ V m ⊆ span S_m ⊆ carrier_sub (= carrier).
  obtain ⟨S_m, hS_m_sub, hV_eq⟩ := hV_span m
  have hpm_in_VM : (p m : ↥(L2ZeroMean P)) ∈ V m := (hV_proj m).1
  have h_VM_le_car : V m ≤ carrier_sub := by
    rw [hV_eq]
    exact Submodule.span_le.mpr hS_m_sub
  have h_p_in_car : (p m : ↥(L2ZeroMean P)) ∈ T_set.carrier :=
    h_VM_le_car hpm_in_VM
  -- p m is essentially bounded (from carrier hypothesis).
  have h_p_ess : IsEssBoundedMixtureScore (p m) :=
    h_carrier_ess (p m) h_p_in_car
  -- The unit vector u := (1/‖p m‖) • p m.
  have h_pm_norm_ne : ‖(p m : ↥(L2ZeroMean P))‖ ≠ 0 := ne_of_gt h_pm_pos
  set c : ℝ := 1 / ‖(p m : ↥(L2ZeroMean P))‖ with hc_def
  have hc_pos : 0 < c := by
    rw [hc_def]; positivity
  let u : ↥(L2ZeroMean P) := c • (p m)
  -- u ∈ carrier.
  have h_u_in_car : u ∈ T_set.carrier := h_lin_smul (p m) h_p_in_car c
  -- u IsEssBoundedMixtureScore.
  have h_u_ess : IsEssBoundedMixtureScore u := h_p_ess.smul c
  -- Define the 1-element basis.
  let g_P : Fin 1 → ↥(L2ZeroMean P) := fun _ => u
  -- Prove the existential.
  refine ⟨1, g_P, ?_hg, ?_h_orth, ?_h_basis, ?_h_linspan, ?_h_AAT⟩
  · -- IsBoundedMixtureScores g_P
    intro i
    exact h_u_ess
  · -- Orthonormal: 1-element with ‖u‖_{Lp} = 1.
    have h_u_norm_L2 : ‖u‖ = 1 := by
      change ‖(c • (p m : ↥(L2ZeroMean P)))‖ = 1
      rw [norm_smul, hc_def, Real.norm_eq_abs,
        abs_of_pos (show (0 : ℝ) < 1 / ‖(p m : ↥(L2ZeroMean P))‖ by positivity)]
      field_simp
    -- Lp coercion preserves norm: ‖(u : Lp ℝ 2 P)‖ = ‖u‖ = 1.
    refine ⟨?_, ?_⟩
    · intro i
      change ‖((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ = 1
      -- L2ZeroMean coercion to Lp preserves norm.
      have h_coe_norm :
          ‖((u : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖
            = ‖(u : ↥(L2ZeroMean P))‖ := by
        rfl
      simp [g_P, h_coe_norm, h_u_norm_L2]
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
  · -- ∀ j, g_P j ∈ T_set.carrier
    intro j
    exact h_u_in_car
  · -- ∀ θ, ∑ θ_j • g_P j ∈ T_set.carrier (sum is θ_0 • u, carrier closed under smul).
    intro θ
    have h_sum : (∑ j : Fin 1, ((WithLp.equiv 2 _) θ) j • (g_P j) :
        ↥(L2ZeroMean P))
        = ((WithLp.equiv 2 _) θ) 0 • u := by
      simp [g_P]
    rw [h_sum]
    exact h_lin_smul u h_u_in_car _
  · -- ∑ j ⟨IF_eff, g_P j⟩² = ‖p m‖².
    simp only [Fin.sum_univ_one, g_P]
    -- Compute ⟨IF_eff, u⟩ = c · ⟨IF_eff, p m⟩.
    -- Projection property: ⟨IF_eff, p m⟩ = ‖p m‖².
    -- Hence ⟨IF_eff, u⟩ = c · ‖p m‖² = (1/‖p m‖) · ‖p m‖² = ‖p m‖.
    -- Then ⟨IF_eff, u⟩² = ‖p m‖².
    have h_inner_proj :
        @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (p m)
          = ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 := by
      -- ⟨IF_eff, p m⟩ = ⟨IF_eff - p m + p m, p m⟩
      --              = ⟨IF_eff - p m, p m⟩ + ⟨p m, p m⟩
      --              = 0 + ‖p m‖²
      have h_orth : ⟪(p m : ↥(L2ZeroMean P)),
          (IF_eff : ↥(L2ZeroMean P)) - p m⟫_ℝ = 0 :=
        (Submodule.mem_orthogonal _ _).mp (hV_proj m).2 (p m) hpm_in_VM
      have h_orth_swap : ⟪(IF_eff : ↥(L2ZeroMean P)) - p m,
          (p m : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
        rw [real_inner_comm]; exact h_orth
      have h_decomp :
          @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (p m)
            = @inner ℝ _ _ ((IF_eff : ↥(L2ZeroMean P)) - p m) (p m)
              + @inner ℝ _ _ (p m : ↥(L2ZeroMean P)) (p m) := by
        rw [← inner_add_left]
        congr 1; abel
      rw [h_decomp, h_orth_swap, zero_add,
        real_inner_self_eq_norm_mul_norm, sq]
    -- ⟨IF_eff, u⟩ = c · ⟨IF_eff, p m⟩ = c · ‖p m‖²
    have h_inner_u :
        @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) u
          = c * ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 := by
      change @inner ℝ _ _ (IF_eff : ↥(L2ZeroMean P)) (c • (p m))
        = c * ‖(p m : ↥(L2ZeroMean P))‖ ^ 2
      rw [inner_smul_right, h_inner_proj]
    rw [h_inner_u]
    -- (c · ‖p m‖²)² = c² · ‖p m‖⁴ = (1/‖p m‖²) · ‖p m‖⁴ = ‖p m‖²
    have hc_pm : c * ‖(p m : ↥(L2ZeroMean P))‖ ^ 2 = ‖(p m : ↥(L2ZeroMean P))‖ := by
      rw [hc_def]
      field_simp
    rw [hc_pm]

end AsymptoticStatistics.LowerBounds.BasisFromProjSeq
