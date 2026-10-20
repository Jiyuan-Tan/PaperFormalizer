module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrow
public import StatLean.AsymptoticStatistics.ParametricFamily.UnboundedSubmodel
public import StatLean.AsymptoticStatistics.LowerBounds.UnboundedSubmodelQMDPath
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Measure-level alignment of the canonical path with the sigmoid submodel

Measure-level alignment between the `canonicalPath` realiser and the
`m`-dimensional `unboundedParamSubmodel` along an arbitrary direction `h`.

The pointwise-in-`ω` density identity does **not** hold: `gMk` of an
`L²`-sum is only `=ᵐ[P]` (not pointwise) the sum of the `gMk`s. The
alignment therefore lives at the **measure** level: both sides reduce to
`P.withDensity (ofReal ∘ ·)`, and the densities agree `P`-a.e., so the
measures coincide by `withDensity_congr_ae`.

The actual a.e. content is concentrated in the single fact that the two
sigmoid `k`-arguments (`linPerturb` of the two score families) are
`P`-a.e. equal, which in turn follows because both reduce, at the exact
`L²` level via `linPerturbScore_coe_ae`, to `t • G`, where
`G = ∑ⱼ hⱼ • g_P j` is the seed reconstructed by `canonicalPath`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998),
§25.16 (sigmoid submodel).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal BigOperators

namespace AsymptoticStatistics.LowerBounds.RegularEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## `L²`-level algebra of the linear score combination

`linPerturbScore` is `ℝ`-linear in its parameter slot; we only need the
scalar-multiplication case `θ = t • h`. -/

/-- `linPerturbScore` scales linearly in the parameter: `t • h ↦ t • (the
combination at `h`)`. Pure `L²`-algebra (no measure content). -/
lemma linPerturbScore_smul
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    linPerturbScore g_P (t • h) = t • linPerturbScore g_P h := by
  classical
  unfold linPerturbScore
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- `(t • h) i • g_P i = t • (h i • g_P i)`.
  have h_idx : (t • h) i = t * h i := rfl
  rw [h_idx, mul_smul]

/-! ## The central a.e. fact: the two `k`-arguments agree `P`-a.e.

For `g ≠ 0` with seed `G := ∑ⱼ hⱼ • g_P j` (`= linPerturbScore g_P h`),
`canonicalPath g` is the 1-dim `oneDimPath` with score family
`fun _ : Fin 1 => (1/‖G‖) • G` and direction `single 0 ‖G‖`. Both its
`k`-argument `linPerturb (fun _ => (1/‖G‖)•G) (t • single 0 ‖G‖)` and the
target `linPerturb g_P (t • h)` reduce — at the `L²` level — to
`((t • G : Lp ℝ 2 P) : Ω → ℝ)`, hence agree `P`-a.e. -/

/-- The 1-dim seed family's `k`-argument reconstructs the original
`k`-argument `P`-a.e. The seed `(1/‖G‖) • G` with direction-weight `‖G‖`
collapses to `G = linPerturbScore g_P h`, provided `‖G‖ ≠ 0` (guaranteed
by the hypothesis `hG : linPerturbScore g_P h ≠ 0`). -/
lemma seed_linPerturb_ae_eq
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h : EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hG : (linPerturbScore g_P h) ≠ 0) :
    linPerturb (fun _ : Fin 1 => (1 / ‖linPerturbScore g_P h‖) • linPerturbScore g_P h)
        (t • EuclideanSpace.single (0 : Fin 1) ‖linPerturbScore g_P h‖)
      =ᵐ[P] linPerturb g_P (t • h) := by
  classical
  set G : ↥(L2ZeroMean P) := linPerturbScore g_P h with hG_def
  set G' : Fin 1 → ↥(L2ZeroMean P) := fun _ => (1 / ‖G‖) • G with hG'_def
  have hnorm_ne : ‖G‖ ≠ 0 := norm_ne_zero_iff.mpr hG
  -- LHS reduces to `((linPerturbScore G' (t • single 0 ‖G‖) : Lp) : Ω → ℝ)`.
  have h_lhs : linPerturb G' (t • EuclideanSpace.single (0 : Fin 1) ‖G‖)
      =ᵐ[P] ((linPerturbScore G' (t • EuclideanSpace.single (0 : Fin 1) ‖G‖)
              : Lp ℝ 2 P) : Ω → ℝ) :=
    (linPerturbScore_coe_ae G' (t • EuclideanSpace.single (0 : Fin 1) ‖G‖)).symm
  -- RHS reduces to `((linPerturbScore g_P (t • h) : Lp) : Ω → ℝ)`.
  have h_rhs : linPerturb g_P (t • h)
      =ᵐ[P] ((linPerturbScore g_P (t • h) : Lp ℝ 2 P) : Ω → ℝ) :=
    (linPerturbScore_coe_ae g_P (t • h)).symm
  -- The two `L²` elements are EQUAL (exactly, no a.e.).
  have h_l2_eq :
      linPerturbScore G' (t • EuclideanSpace.single (0 : Fin 1) ‖G‖)
        = linPerturbScore g_P (t • h) := by
    -- LHS = `(t • single 0 ‖G‖) 0 • G' 0 = (t * ‖G‖) • ((1/‖G‖) • G) = t • G`.
    have h_lhs_eq :
        linPerturbScore G' (t • EuclideanSpace.single (0 : Fin 1) ‖G‖)
          = t • G := by
      unfold linPerturbScore
      rw [Fin.sum_univ_one]
      -- `(t • single 0 ‖G‖) 0 • G' 0`.
      have h_coord : (t • EuclideanSpace.single (0 : Fin 1) ‖G‖) 0 = t * ‖G‖ := by
        have h_smul : (t • EuclideanSpace.single (0 : Fin 1) ‖G‖) 0
            = t * (EuclideanSpace.single (0 : Fin 1) ‖G‖) 0 := rfl
        rw [h_smul]
        have h_single : (EuclideanSpace.single (0 : Fin 1) ‖G‖) 0 = ‖G‖ := by simp
        rw [h_single]
      rw [h_coord, hG'_def]
      -- `(t * ‖G‖) • ((1/‖G‖) • G) = t • G`.
      rw [smul_smul]
      have h_scalar : (t * ‖G‖) * (1 / ‖G‖) = t := by field_simp
      rw [h_scalar]
    -- RHS = `linPerturbScore g_P (t • h) = t • linPerturbScore g_P h = t • G`.
    rw [h_lhs_eq, linPerturbScore_smul, ← hG_def]
  -- Chain the three facts.
  refine h_lhs.trans ?_
  rw [h_l2_eq]
  exact h_rhs.symm

/-! ## Density-level a.e. equality (both branches) -/

/-- The two sigmoid densities (seed family at `(t • single 0 ‖G‖)` vs the
original family at `t • h`) agree `P`-a.e., for `g ≠ 0`. The normaliser
constants are EQUAL (by `integral_congr_ae` on a.e.-equal integrands),
and the `kSigmoid` factors agree a.e. (congruence on the a.e.-equal
`k`-arguments). -/
lemma seed_density_ae_eq
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hG : (linPerturbScore g_P h) ≠ 0)
    (h_orth' : Orthonormal ℝ (fun _i : Fin 1 =>
        (((1 / ‖linPerturbScore g_P h‖) • linPerturbScore g_P h : ↥(L2ZeroMean P))
          : Lp ℝ 2 P))) :
    (fun ω => (unboundedParamSubmodel
        (fun _ : Fin 1 => (1 / ‖linPerturbScore g_P h‖) • linPerturbScore g_P h)
        h_orth').density
          (t • EuclideanSpace.single (0 : Fin 1) ‖linPerturbScore g_P h‖) ω)
      =ᵐ[P] (fun ω => (unboundedParamSubmodel g_P h_orth).density (t • h) ω) := by
  set G' : Fin 1 → ↥(L2ZeroMean P) :=
    fun _ => (1 / ‖linPerturbScore g_P h‖) • linPerturbScore g_P h with hG'_def
  set θ' : EuclideanSpace ℝ (Fin 1) :=
    t • EuclideanSpace.single (0 : Fin 1) ‖linPerturbScore g_P h‖ with hθ'_def
  -- The core a.e. fact: the two `k`-arguments agree `P`-a.e.
  have h_lin_ae : linPerturb G' θ' =ᵐ[P] linPerturb g_P (t • h) :=
    seed_linPerturb_ae_eq g_P h t hG
  -- The two integrands `normalizer_c_integrand` agree `P`-a.e.
  have h_integrand_ae :
      normalizer_c_integrand G' θ' =ᵐ[P] normalizer_c_integrand g_P (t • h) := by
    filter_upwards [h_lin_ae] with ω hω
    unfold normalizer_c_integrand
    rw [hω]
  -- The normaliser constants are EQUAL (integral over a.e.-equal integrands).
  have h_norm_eq : normalizer_c G' θ' = normalizer_c g_P (t • h) := by
    unfold normalizer_c
    rw [integral_congr_ae h_integrand_ae]
  -- Assemble: density = `normalizer_c * normalizer_c_integrand`.
  filter_upwards [h_integrand_ae] with ω hω
  change unboundedSubmodelDensity G' θ' ω = unboundedSubmodelDensity g_P (t • h) ω
  unfold unboundedSubmodelDensity
  rw [h_norm_eq, hω]

/-! ## The main alignment theorem -/

/-- **Measure-level alignment.** The curve of `canonicalPath (∑ⱼ hⱼ • g_P j)`
at `t` equals the `unboundedParamSubmodel` measure
`P.withDensity (ofReal ∘ density (t • h))`. Both sides are `withDensity`
measures whose densities agree only `P`-a.e. (the `gMk`-of-a-sum gap), so
the equality is established via `withDensity_congr_ae`, never as a
pointwise density identity. -/
theorem canonicalPath_curve_eq_unbounded_withDensity
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    (canonicalPath (∑ j, ((WithLp.equiv 2 _) h) j • g_P j)).curve t
      = P.withDensity (fun ω => ENNReal.ofReal
          ((unboundedParamSubmodel g_P h_orth).density (t • h) ω)) := by
  classical
  -- `(WithLp.equiv 2 _) h j = h j`, so the realiser's seed is `linPerturbScore g_P h`.
  have h_seed_eq :
      (∑ j, ((WithLp.equiv 2 _) h) j • g_P j) = linPerturbScore g_P h := rfl
  rw [h_seed_eq]
  set G : ↥(L2ZeroMean P) := linPerturbScore g_P h with hG_def
  unfold canonicalPath
  by_cases hg : G = 0
  · -- `g = 0` branch: `canonicalPath 0 = boundedDensityPath 0`; curve `= P`.
    -- RHS also `= P` (`linPerturbScore g_P (t•h) =ᵐ 0`, `kSigmoid =ᵐ 1`, `c = 1`).
    simp only [hg, dif_pos]
    -- LHS: `(boundedDensityPath 0 ⟨0,_⟩).curve t`.
    -- Compute it directly: the curve is `if |t| < δ then withDensity (ofReal (1+t·0)) else P`,
    -- and both branches equal `P` because the score is `0`.
    have h_lhs : (AsymptoticStatistics.Core.MassMethod.boundedDensityPath
        (0 : ↥(L2ZeroMean P))
        (by
          refine ⟨0, ?_⟩
          have h_ae :
              (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => (0 : ℝ)) :=
            Lp.coeFn_zero _ _ _
          filter_upwards [h_ae] with ω hω
          rw [hω]; simp)).curve t = P := by
      -- The score-`0` path is constantly `P`.
      have h_zero_ae :
          (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] (fun _ => (0 : ℝ)) :=
        Lp.coeFn_zero _ _ _
      -- The curve unfolds to `if |t| < δ then withDensity (ofReal (1 + t·0)) else P`.
      -- Both `if`-branches equal `P` because the score is `0`.
      change (if |t| < (1 : ℝ) / (max 0 (Classical.choose _) + 1) then
              P.withDensity (fun ω => ENNReal.ofReal
                (1 + t * (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω))
            else P) = P
      split_ifs with ht
      · -- then branch: `withDensity (ofReal (1 + t·0)) = withDensity 1 = P`.
        have h_dens : (fun ω => ENNReal.ofReal
            (1 + t * (((0 : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω))
              =ᵐ[P] (1 : Ω → ℝ≥0∞) := by
          filter_upwards [h_zero_ae] with ω hω
          rw [hω]; simp
        rw [withDensity_congr_ae h_dens, withDensity_one]
      · -- else branch is `P` by definition.
        rfl
    rw [h_lhs]
    -- RHS `= P`: density `(t • h) =ᵐ 1`.
    symm
    have h_dens_one : (fun ω => ENNReal.ofReal
        ((unboundedParamSubmodel g_P h_orth).density (t • h) ω))
          =ᵐ[P] (1 : Ω → ℝ≥0∞) := by
      -- `density (t•h) ω = normalizer_c (t•h) * kSigmoid (linPerturb (t•h) ω)`.
      -- `linPerturbScore g_P (t•h) = t • G = t • 0 = 0` in `L²`,
      -- so `linPerturb g_P (t•h) =ᵐ 0` and `kSigmoid 0 = 1`, `normalizer_c = 1`.
      have h_linScore_zero : linPerturbScore g_P (t • h) = 0 := by
        rw [linPerturbScore_smul, ← hG_def, hg, smul_zero]
      have h_lin_ae : linPerturb g_P (t • h) =ᵐ[P] (fun _ => (0 : ℝ)) := by
        have h1 : linPerturb g_P (t • h)
            =ᵐ[P] ((linPerturbScore g_P (t • h) : Lp ℝ 2 P) : Ω → ℝ) :=
          (linPerturbScore_coe_ae g_P (t • h)).symm
        have h2 : ((linPerturbScore g_P (t • h) : Lp ℝ 2 P) : Ω → ℝ)
            =ᵐ[P] (fun _ => (0 : ℝ)) := by
          rw [h_linScore_zero]
          exact Lp.coeFn_zero _ _ _
        exact h1.trans h2
      -- `normalizer_c g_P (t•h) = 1`: integrand is a.e. `1`.
      have h_integrand_ae : normalizer_c_integrand g_P (t • h) =ᵐ[P] (fun _ => (1 : ℝ)) := by
        filter_upwards [h_lin_ae] with ω hω
        unfold normalizer_c_integrand
        rw [hω, kSigmoid_zero]
      have h_norm_one : normalizer_c g_P (t • h) = 1 := by
        unfold normalizer_c
        rw [integral_congr_ae h_integrand_ae]
        simp
      filter_upwards [h_lin_ae] with ω hω
      change ENNReal.ofReal (unboundedSubmodelDensity g_P (t • h) ω) = (1 : Ω → ℝ≥0∞) ω
      rw [Pi.one_apply]
      unfold unboundedSubmodelDensity normalizer_c_integrand
      rw [h_norm_one, hω, kSigmoid_zero, mul_one, ENNReal.ofReal_one]
    rw [withDensity_congr_ae h_dens_one, withDensity_one]
  · -- `g ≠ 0` branch: 1-dim `oneDimPath` with seed `(1/‖G‖)•G`, direction `single 0 ‖G‖`.
    simp only [hg, dif_neg, not_false_eq_true]
    -- The `oneDimPath`'s curve is `withDensity (ofReal ∘ density (t • single 0 ‖G‖))`.
    refine (unboundedParamSubmodel_oneDimPath_curve _ _ _ _).trans ?_
    -- Align via `withDensity_congr_ae` on the a.e.-equal densities.
    refine withDensity_congr_ae ?_
    -- Build the seed's orthonormality witness (the one `canonicalPath` uses).
    have hnorm_pos : 0 < ‖G‖ := norm_pos_iff.mpr hg
    have hnorm_ne : ‖G‖ ≠ 0 := hnorm_pos.ne'
    set G' : Fin 1 → ↥(L2ZeroMean P) := fun _ => (1 / ‖G‖) • G with hG'_def
    have h_orth' : Orthonormal ℝ (fun i : Fin 1 => ((G' i : ↥(L2ZeroMean P)) : Lp ℝ 2 P)) := by
      have h_norm_one : ∀ i : Fin 1, ‖((G' i : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ = 1 := by
        intro _
        have h_coe_smul :
            (((1 / ‖G‖) • G : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
              = (1 / ‖G‖) • ((G : ↥(L2ZeroMean P)) : Lp ℝ 2 P) := rfl
        rw [hG'_def]
        change ‖(((1 / ‖G‖) • G : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ = 1
        rw [h_coe_smul, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 1 / ‖G‖)]
        have h_coe_norm : ‖((G : ↥(L2ZeroMean P)) : Lp ℝ 2 P)‖ = ‖G‖ := rfl
        rw [h_coe_norm]; field_simp
      refine ⟨h_norm_one, ?_⟩
      intro i j hij
      exact absurd (Subsingleton.elim i j) hij
    -- `ENNReal.ofReal` congruence from the real-valued a.e. density equality.
    have h_dens_ae := seed_density_ae_eq g_P h_orth h t hg h_orth'
    filter_upwards [h_dens_ae] with ω hω
    rw [hω]

end AsymptoticStatistics.LowerBounds.RegularEstimator
