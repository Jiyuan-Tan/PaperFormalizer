module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.PBridgeTight
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer

@[expose] public section

/-!
# Theorem 18.14 sufficiency (⟸): finite-net discretization

The hard direction of van der Vaart, *Asymptotic Statistics* Theorem 18.14
(book p.261): marginal CLT (`IsMarginalCLT`) + asymptotic equicontinuity
(`IsAsymptoticallyEquicontinuous`) ⟹ the empirical process converges weakly in
the outer sense `⇝ₒ` to the tight `P`-Brownian bridge `G_P = gaussianPBridge` in
`ℓ∞(F)`.

The vdV proof discretizes `(↥F, ρ_P)` along a sequence of finite `2⁻ᵐ`-nets
`Sₘ` (extracted from `totallyBounded_L2`), pushes the finite-dimensional CLT
through each net, controls both empirical and limiting discretization errors,
and combines the three errors through the subadditive outer-expectation
triangle inequality.

## Main definitions

* `finiteNetProj` — the coordinate-collapsing projection of `ℓ∞(F)` onto
  the finite `2⁻ᵐ`-net `Sₘ` of `(↥F, distL2 P)`.

## Main results

* `weakConvergesOuter_findim_proj` — the `m`-projected empirical process
  converges `⇝ₒ` to the `m`-projected `G_P` marginal (finite-dim CLT).
* `empirical_proj_error_outer` — the empirical discretization error
  `‖𝔾ₙ − πₘ𝔾ₙ‖_{ℓ∞(F)}` is asymptotically negligible as `m → ∞` (outer prob).
* `limit_proj_error` — the limit discretization error
  `∫ |f(πₘ z) − f z| dG_P` → 0 as `m → ∞` (a.s. UC paths + tightness + DCT).
* `isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous_aux` — the
  ε/3 combination for a bounded-Lipschitz test function.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem
18.14 (book p.261), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology AsymptoticStatistics BoundedContinuousFunction
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

section Discretization

variable {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
variable {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
  (hF_meas : ∀ f ∈ F, Measurable f)

/-- **Finite `2⁻ᵐ`-net `Sₘ ⊆ F`.** The finite subset of `F` extracted from
`totallyBounded_L2 hF_ent` at scale `2⁻ᵐ`: every `f ∈ F` is `distL2`-within `2⁻ᵐ`
of some `g ∈ Sₘ`. This fixed finite cover makes `netRep`'s range finite
(`finite_range_netRep`).
The net is a choice of finite cover of the totally bounded space
`(↥F, distL2 P)`. -/
noncomputable def netCover {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) : Finset (Ω → ℝ) :=
  (totallyBounded_L2 hF_ent ((2 : ℝ) ^ (-(m : ℤ))) (by positivity)).choose

omit [IsProbabilityMeasure P] in
/-- `netCover` is a subset of `F`. -/
theorem netCover_subset {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) :
    (↑(netCover hF_ent m) : Set (Ω → ℝ)) ⊆ F :=
  (totallyBounded_L2 hF_ent ((2 : ℝ) ^ (-(m : ℤ))) (by positivity)).choose_spec.1

omit [IsProbabilityMeasure P] in
/-- Cover spec: every `f ∈ F` is `distL2`-within `2⁻ᵐ` of some `g ∈ netCover m`. -/
theorem netCover_spec {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) :
    ∀ f ∈ F, ∃ g ∈ netCover hF_ent m, distL2 P f g < (2 : ℝ) ^ (-(m : ℤ)) :=
  (totallyBounded_L2 hF_ent ((2 : ℝ) ^ (-(m : ℤ))) (by positivity)).choose_spec.2

/-- **Finite-net representative.** For each scale `m`, the choice of a fixed
cover point `netRep m t ∈ ↥F` lying in the finite `2⁻ᵐ`-net `Sₘ = netCover hF_ent m`
of `(↥F, distL2 P)`, with `distL2 P t (netRep m t) < 2⁻ᵐ`. The net itself is the
(finite) range of `netRep m`.

Edge: when `F = ∅` the subtype `↥F` is empty and `netRep m` is the unique empty
map; the `2⁻ᵐ`-net is empty.

The representative is a chosen cover point in `netCover hF_ent m`; its
membership and `distL2`-closeness are recorded by `netRep_mem_cover` and
`netRep_distL2_lt`. -/
noncomputable def netRep {F : Set (Ω → ℝ)} {P : Measure Ω} {G : Ω → ℝ}
    (_hG_env : IsEnvelope F G) (_hG : MemLp G 2 P)
    (_hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) (t : ↥F) : ↥F :=
  -- Pick the cover point of the fixed finite net `netCover hF_ent m` that is
  -- `2⁻ᵐ`-close to `t`. The cover spec `netCover_spec` applied to `t ∈ F`
  -- supplies such a `g ∈ netCover hF_ent m`; membership in the cover (which lies
  -- in `F` via `netCover_subset`) lifts it to `↥F`. Range finiteness follows
  -- because all values lie in the finite `netCover hF_ent m` (`finite_range_netRep`).
  let h := netCover_spec hF_ent m (t : Ω → ℝ) t.2
  ⟨h.choose, netCover_subset hF_ent m h.choose_spec.1⟩

omit [IsProbabilityMeasure P] in
/-- The `netRep m`-representative lies in the fixed finite net `netCover hF_ent m`.
This is the key fact making `netRep`'s range finite. -/
theorem netRep_mem_cover (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) (t : ↥F) :
    (netRep hG_env hG hF_meas hF_ent m t : Ω → ℝ) ∈ netCover hF_ent m :=
  (netCover_spec hF_ent m (t : Ω → ℝ) t.2).choose_spec.1

omit [IsProbabilityMeasure P] in
/-- The `netRep m`-representative is `2⁻ᵐ`-close to its argument in `distL2 P`
by `netCover_spec`. -/
theorem netRep_distL2_lt (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) (t : ↥F) :
    distL2 P (t : Ω → ℝ) (netRep hG_env hG hF_meas hF_ent m t : Ω → ℝ) < (2 : ℝ) ^ (-(m : ℤ)) :=
  (netCover_spec hF_ent m (t : Ω → ℝ) t.2).choose_spec.2

omit [IsProbabilityMeasure P] in
/-- The `netRep m`-representatives range over a finite set (the `2⁻ᵐ`-net `Sₘ`):
the image of `↥F` under `netRep m` is finite.

The values of `netRep m` all lie in the fixed finite cover `netCover hF_ent m`
(`netRep_mem_cover`). Hence the image of `Set.range (netRep m)` under the
injective `Subtype.val : ↥F → (Ω → ℝ)` is contained in the finite set
`↑(netCover hF_ent m)`, so the range itself is finite
(`Set.Finite.of_finite_image` + `Subtype.val_injective.injOn`). -/
theorem finite_range_netRep (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) :
    (Set.range (netRep hG_env hG hF_meas hF_ent m)).Finite := by
  -- The image of the range under `Subtype.val` lands in the finite cover `Sₘ`.
  apply Set.Finite.of_finite_image (f := (Subtype.val : ↥F → (Ω → ℝ)))
  · refine Set.Finite.subset (netCover hF_ent m).finite_toSet ?_
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact netRep_mem_cover hG_env hG hF_meas hF_ent m t
  · exact Subtype.val_injective.injOn

/-- **Finite-net projection `πₘ` on `ℓ∞(F)`.** Collapses each coordinate
`t : ↥F` of `z : LinfF F` to the value at its net representative:
`finiteNetProj m z t = z (netRep m t)`. Since the range of `t ↦ z (netRep m t)`
is contained in the (finite) range of `z` over the net `Sₘ`, it is `ℓ∞`-bounded
by `‖z‖`, hence a valid element of `LinfF F`.

vdV §19.2 / Theorem 18.14 (book p.261): the empirical process is approximated by
its values on a finite `2⁻ᵐ`-net; `πₘ` is the coordinate-collapse realizing this
approximation in `ℓ∞(F)`. -/
noncomputable def finiteNetProj {F : Set (Ω → ℝ)} {P : Measure Ω} {G : Ω → ℝ}
    (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) (z : LinfF F) : LinfF F :=
  -- Coordinate-collapse onto the net: `t ↦ z (netRep m t)`. The `ℓ∞`-membership
  -- holds because each coordinate `|z (netRep m t)| = ‖z (netRep m t)‖ ≤ ‖z‖`, so
  -- the range of norms is bounded above by `‖z‖`.
  ⟨fun t => z (netRep hG_env hG hF_meas hF_ent m t),
    memℓp_infty ⟨‖z‖, by
      rintro _ ⟨t, rfl⟩
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero z (netRep hG_env hG hF_meas hF_ent m t)⟩⟩

omit [IsProbabilityMeasure P] in
/-- The projection `πₘ` reads coordinate `t` off the net representative:
`finiteNetProj m z t = z (netRep m t)`. -/
theorem finiteNetProj_apply (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (m : ℕ) (z : LinfF F) (t : ↥F) :
    (finiteNetProj hG_env hG hF_meas hF_ent m z) t = z (netRep hG_env hG hF_meas hF_ent m t) :=
  rfl

omit [IsProbabilityMeasure P] in
/-- `πₘ` is measurable `LinfF F → LinfF F` (it factors through the finite-
dimensional coordinate space `ℝ^{Sₘ}`; each coordinate `z ↦ z (netRep m t)` is a
continuous evaluation). Concretely `πₘ` is a `1`-Lipschitz (norm-nonexpansive)
map: for all `z, z'`,
`‖πₘ z − πₘ z'‖ = sup_t |z (netRep m t) − z' (netRep m t)| ≤ ‖z − z'‖`,
so it is continuous, hence Borel-measurable. -/
theorem measurable_finiteNetProj (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (m : ℕ) :
    Measurable (finiteNetProj hG_env hG hF_meas hF_ent m) := by
  -- `πₘ` is `1`-Lipschitz, hence continuous, hence (Borel) measurable.
  have hlip : LipschitzWith 1 (finiteNetProj hG_env hG hF_meas hF_ent m) := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    -- Bound the sup-norm of the difference coordinatewise by `‖z − z'‖`.
    apply lp.norm_le_of_forall_le (norm_nonneg (z - z'))
    intro t
    -- coordinate `t` of `πₘ z − πₘ z'` equals `(z - z') (netRep m t)`.
    have hcoord : (finiteNetProj hG_env hG hF_meas hF_ent m z
        - finiteNetProj hG_env hG hF_meas hF_ent m z') t
        = (z - z') (netRep hG_env hG hF_meas hF_ent m t) := by
      rw [lp.coeFn_sub, lp.coeFn_sub]
      simp only [Pi.sub_apply]
      rfl
    rw [hcoord]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - z') (netRep hG_env hG hF_meas hF_ent m t)
  exact hlip.continuous.measurable

variable (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)

/-! ### Finite-dimensional convergence through the net

The projected map is `LinfF F`-valued rather than a finite tuple, while the
marginal CLT (`IsMarginalCLT.fdd`) and the Gaussian limit
(`gaussianPBridge`'s `isGaussian_fdd`) are both phrased as **finite-tuple**
(`Fin k → ℝ`) coordinate readouts, and `gaussianPBridge` is a `choose` witness
exposing only the `IsPBrownianBridge` field set. Finite-coordinate restriction,
Gaussian identification, and continuous reconstruction connect these forms. -/

/-- **Coordinate measurability of the empirical process** (for a
genuinely Borel-measurable readout `g`). For a measurable `g : Ω → ℝ`, the
coordinate evaluation `ξ ↦ empiricalProcess P n (X· ξ) g` is measurable
`Ξ → ℝ`: it is `√n` times the difference of the empirical average
`n⁻¹ ∑ᵢ g (X i ξ)` (a finite sum of the measurable maps `ξ ↦ g (X i ξ) = g ∘ X i`,
each measurable since `X i` is measurable and `g` is Borel) and the constant
`∫ g dP`.

The full carrier map
`ξ ↦ 𝔾ₙ ξ` into `ℓ∞(F)` is in general **NOT** Borel measurable for uncountable
`F` — this non-measurability is precisely why the abstract-Donsker theory uses
outer expectation `E*`. Even the *projected* map reads finitely many functions
`s ∈ Sₘ ⊆ F`, but those are only `AEStronglyMeasurable s P` (via `hF_meas`), so
`ξ ↦ s (X i ξ)` is only `μ`-a.e. measurable — Borel measurability of
`measurable_projectedEmpirical` therefore requires passing to measurable
representatives `s' =ᵐ[P] s` and using that pushforward laws are insensitive to
`μ`-a.e. modification (the same representative machinery as
`marginalCLT_fdd_of_iid` in `Donsker.lean`). This lemma is the measurable-readout
core of that argument. -/
theorem measurable_empiricalProcess_coord
    {Ξ : Type} [MeasurableSpace Ξ] (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) (g : Ω → ℝ) (hg : Measurable g) :
    Measurable (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
  -- `empiricalProcess P n X g = √n * (n⁻¹ * ∑ i, g (X i) - ∫ g dP)`.
  unfold empiricalProcess empiricalAvg
  -- `ξ ↦ g (X i.val ξ) = g ∘ (X i.val)` is measurable (Borel `g` ∘ measurable `X`).
  have hcoord : ∀ i : Fin n, Measurable (fun ξ : Ξ => g (X i.val ξ)) :=
    fun i => hg.comp (hX_meas i.val)
  -- The finite sum, the affine combination, and the constant scalar are measurable.
  have hsum : Measurable (fun ξ : Ξ => ∑ i : Fin n, g (X i.val ξ)) :=
    Finset.measurable_sum _ (fun i _ => hcoord i)
  exact (measurable_const.mul
    ((measurable_const.mul hsum).sub measurable_const))

/-! ### Shared finite-net factorization

The projected map `πₘ` factors through the finite coordinate space `Sₘ → ℝ`, where
`Sₘ = Set.range (netRep m)` is finite (`finite_range_netRep`). We package this
once: the finite index type `netIndex m`, the continuous coordinate-collapse
reconstruction `netRecon m`, and the factorization
`finiteNetProj m z = netRecon m (fun s => z s.1)`. -/

/-- The FINITE index type `Sₘ = Set.range (netRep m)` of the `2⁻ᵐ`-net, carrying a
`Fintype` instance from `finite_range_netRep`. -/
noncomputable instance netIndexFintype (m : ℕ) :
    Fintype ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) :=
  (finite_range_netRep hG_env hG hF_meas hF_ent m).fintype

omit [IsProbabilityMeasure P] in
/-- Each net representative `netRep m t` lands in the finite index set `Sₘ`. -/
theorem netRep_mem_range (m : ℕ) (t : ↥F) :
    netRep hG_env hG hF_meas hF_ent m t ∈ Set.range (netRep hG_env hG hF_meas hF_ent m) :=
  Set.mem_range_self t

omit [IsProbabilityMeasure P] in
/-- **Continuity of coordinate evaluation on `ℓ∞(F)`.** For each `i : ↥F`, the
evaluation `z ↦ z i` is `1`-Lipschitz (`lp.norm_apply_le_norm`), hence continuous. -/
theorem continuous_linfF_eval (i : ↥F) :
    Continuous (fun z : LinfF F => z i) := by
  have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
      rw [lp.coeFn_sub z w]; rfl
    rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
  exact hlip.continuous

/-- **Coordinate-collapse reconstruction `recon : (Sₘ → ℝ) → ℓ∞(F)`.** Given a
value vector `v` on the finite net `Sₘ`, reconstruct the full path by reading each
coordinate `t : ↥F` off the net representative `netRep m t ∈ Sₘ`:
`netRecon m v t = v ⟨netRep m t, _⟩`. The range of `t ↦ v ⟨netRep m t, _⟩` is
contained in the finite range of `v`, hence bounded, so this is a valid element of
`ℓ∞(F)`. The map is `1`-Lipschitz, hence continuous (`continuous_netRecon`). -/
noncomputable def netRecon (m : ℕ)
    (v : ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) → ℝ) : LinfF F :=
  ⟨fun t => v ⟨netRep hG_env hG hF_meas hF_ent m t, netRep_mem_range hG_env hG hF_meas hF_ent m t⟩,
    memℓp_infty ⟨⨆ s, ‖v s‖, by
      rintro _ ⟨t, rfl⟩
      exact le_ciSup (f := fun s => ‖v s‖) (Finite.bddAbove_range _)
        (⟨netRep hG_env hG hF_meas hF_ent m t,
          netRep_mem_range hG_env hG hF_meas hF_ent m t⟩ :
          ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))⟩⟩

omit [IsProbabilityMeasure P] in
/-- Coordinate readout of the reconstruction: `netRecon m v t = v ⟨netRep m t, _⟩`. -/
theorem netRecon_apply (m : ℕ)
    (v : ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) → ℝ) (t : ↥F) :
    (netRecon hG_env hG hF_meas hF_ent m v) t =
      v ⟨netRep hG_env hG hF_meas hF_ent m t, netRep_mem_range hG_env hG hF_meas hF_ent m t⟩ :=
  rfl

omit [IsProbabilityMeasure P] in
/-- **`netRecon` is `1`-Lipschitz, hence continuous.** Both source (`Sₘ → ℝ`, the
finite-product sup metric) and target (`ℓ∞(F)`) carry sup metrics; each output
coordinate `t` of `netRecon m v − netRecon m w` is `v(idx t) − w(idx t)`, bounded
by `dist v w = sup_s |v s − w s|` (`dist_pi_le_iff`). -/
theorem continuous_netRecon (m : ℕ) :
    Continuous (netRecon hG_env hG hF_meas hF_ent m) := by
  have hlip : LipschitzWith 1 (netRecon hG_env hG hF_meas hF_ent m) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    rw [NNReal.coe_one, one_mul, dist_eq_norm]
    apply lp.norm_le_of_forall_le dist_nonneg
    intro t
    have hmem : netRep hG_env hG hF_meas hF_ent m t
        ∈ Set.range (netRep hG_env hG hF_meas hF_ent m) :=
      netRep_mem_range hG_env hG hF_meas hF_ent m t
    have hcoord : (netRecon hG_env hG hF_meas hF_ent m v
        - netRecon hG_env hG hF_meas hF_ent m w) t
        = v ⟨_, hmem⟩ - w ⟨_, hmem⟩ := by
      rw [lp.coeFn_sub]
      simp only [Pi.sub_apply, netRecon_apply]
    rw [hcoord, Real.norm_eq_abs, ← Real.dist_eq]
    exact (dist_pi_le_iff dist_nonneg).mp (le_refl (dist v w)) _
  exact hlip.continuous

omit [IsProbabilityMeasure P] in
/-- **Finite-net factorization of `πₘ`.** The projection equals the reconstruction
applied to the finite-net coordinate restriction of `z`:
`finiteNetProj m z = netRecon m (fun s => z s.1)`. -/
theorem finiteNetProj_eq_netRecon (m : ℕ) (z : LinfF F) :
    finiteNetProj hG_env hG hF_meas hF_ent m z
      = netRecon hG_env hG hF_meas hF_ent m (fun s => z s.1) := by
  apply lp.ext
  funext t
  rw [finiteNetProj_apply, netRecon_apply]

/-- **Finite-net coordinate restriction `tuple : ℓ∞(F) → (Sₘ → ℝ)`.** Reads the
values of `z` on the finite net `Sₘ = range (netRep m)`: `netTuple m z s = z s.1`.
This is the finite-dimensional projection through which both `μ.map (πₘ ∘ 𝔾ₙ)` and
`gaussianPBridge.map πₘ` factor. -/
def netTuple (m : ℕ) (z : LinfF F)
    (s : ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))) : ℝ := z s.1

omit [IsProbabilityMeasure P] in
/-- `netTuple` is continuous: each coordinate is a continuous evaluation on `ℓ∞(F)`
(`continuous_linfF_eval`), and `Sₘ → ℝ` carries the product topology. -/
theorem continuous_netTuple (m : ℕ) :
    Continuous (netTuple hG_env hG hF_meas hF_ent m) := by
  unfold netTuple
  exact continuous_pi (fun s => continuous_linfF_eval s.1)

omit [IsProbabilityMeasure P] in
/-- `netTuple` is measurable (continuous into the finite-product Borel space). -/
theorem measurable_netTuple (m : ℕ) :
    Measurable (netTuple hG_env hG hF_meas hF_ent m) :=
  (continuous_netTuple hG_env hG hF_meas hF_ent m).measurable

omit [IsProbabilityMeasure P] in
/-- **`πₘ = netRecon ∘ netTuple`.** The projection factors as the (continuous)
reconstruction of the (continuous) finite-net restriction. -/
theorem finiteNetProj_eq_comp (m : ℕ) :
    finiteNetProj hG_env hG hF_meas hF_ent m
      = (netRecon hG_env hG hF_meas hF_ent m) ∘ (netTuple hG_env hG hF_meas hF_ent m) := by
  funext z
  rw [Function.comp_apply, finiteNetProj_eq_netRecon]
  rfl

omit [IsProbabilityMeasure P] in
/-- **Borel measurability of each net-member function `s ∈ Sₘ ⊆ F`.**

Each net coordinate `s : ↥Sₘ` is (the subtype packaging of) a member of `F`:
`s.1 : ↥F`, so `(s.1 : Ω → ℝ) ∈ F` via `s.1.2`, and the chapter hypothesis
`hF_meas : ∀ f ∈ F, Measurable f` supplies `Measurable (s.1 : Ω → ℝ)` directly.
`measurable_empiricalProcess_coord` evaluates `s` **pointwise** at the sample
points `X i ξ`, so it requires `Measurable`, rather than merely
`AEStronglyMeasurable … P`; van der Vaart likewise assumes that `F` is a class
of measurable functions. -/
theorem measurable_net_member (m : ℕ)
    (s : ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))) :
    Measurable (s.1 : Ω → ℝ) :=
  hF_meas (s.1 : Ω → ℝ) s.1.2

/-- **Measurability of the projected empirical process.** The composite
`ξ ↦ πₘ (𝔾ₙ ξ)` is Borel-measurable `Ξ → LinfF F`.

Unlike the un-projected `𝔾ₙ`, the projected map reads only the FINITE net
`Sₘ = range (netRep m)` (finite by `finite_range_netRep`): `(πₘ (𝔾ₙ ξ)) t`
equals `(𝔾ₙ ξ) (netRep m t)`, which takes values in the finite set of coordinates
`{(𝔾ₙ ξ) s : s ∈ Sₘ}`. The map therefore factors through the finite-dimensional
coordinate space `ℝ^{Sₘ}` as `(finite coordinate restriction) ∘ (ℝ^{Sₘ}-recon)`;
the restriction is measurable because each coordinate `ξ ↦ (𝔾ₙ ξ) s` is measurable
(`measurable_empiricalProcess_coord`) and the reconstruction
`ℝ^{Sₘ} → LinfF F` is continuous (so the Borel σ-algebra obstruction that defeats
the un-projected map does not arise). This is the genuine measurability content of
the discretization. -/
theorem measurable_projectedEmpirical (m : ℕ)
    {Ξ : Type} [MeasurableSpace Ξ] (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) :
    Measurable (fun ξ : Ξ => finiteNetProj hG_env hG hF_meas hF_ent m
      (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
        (memℓp_empiricalProcess
          ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
          (fun i : Fin n => X i.val ξ)))) := by
  -- Factor `πₘ ∘ 𝔾ₙ = netRecon m ∘ tuple` where
  -- `tuple ξ s = empiricalProcess P n (X·ξ) (s.1 : Ω → ℝ)`.
  have hfac : (fun ξ : Ξ => finiteNetProj hG_env hG hF_meas hF_ent m
      (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
        (memℓp_empiricalProcess
          ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
          (fun i : Fin n => X i.val ξ))))
      = (netRecon hG_env hG hF_meas hF_ent m) ∘
        (fun ξ s => empiricalProcess P n (fun i : Fin n => X i.val ξ) (s.1 : Ω → ℝ)) := by
    funext ξ
    rw [Function.comp_apply, finiteNetProj_eq_netRecon]
    rfl
  rw [hfac]
  refine (continuous_netRecon hG_env hG hF_meas hF_ent m).measurable.comp ?_
  -- Each net-coordinate `ξ ↦ empiricalProcess P n (X·ξ) (s.1 : Ω → ℝ)` is measurable
  -- by `measurable_empiricalProcess_coord`, which needs `Measurable (s.1 : Ω → ℝ)`.
  refine measurable_pi_iff.mpr (fun s => ?_)
  exact measurable_empiricalProcess_coord X hX_meas n (s.1 : Ω → ℝ)
    (measurable_net_member hG_env hG hF_meas hF_ent m s)

/-- **Measurability of the finite-net coordinate restriction of `𝔾ₙ`.** The map
`ξ ↦ netTuple m (𝔾ₙ ξ)` into `Sₘ → ℝ` is measurable: it equals
`fun ξ s => empiricalProcess P n (X·ξ) (s.1 : Ω → ℝ)`, measurable coordinatewise by
`measurable_empiricalProcess_coord` and `measurable_net_member`. -/
theorem measurable_projectedEmpirical' (m : ℕ)
    {Ξ : Type} [MeasurableSpace Ξ] (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (n : ℕ) :
    Measurable (fun ξ : Ξ => netTuple hG_env hG hF_meas hF_ent m
      (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
        (memℓp_empiricalProcess
          ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
          (fun i : Fin n => X i.val ξ)))) := by
  refine measurable_pi_iff.mpr (fun s => ?_)
  exact measurable_empiricalProcess_coord X hX_meas n (s.1 : Ω → ℝ)
    (measurable_net_member hG_env hG hF_meas hF_ent m s)

/-! ### Reindexing the finite net: `Sₘ ≃ Fin k`

The marginal CLT `IsMarginalCLT.fdd` and the multivariate Gaussian limit
both live on `EuclideanSpace ℝ (Fin k)` (a `Fin k`-indexed tuple), whereas the net
coordinate space is the finite **subtype** `↥(Set.range (netRep m))`. The
canonical enumeration `netEnum : ↥Sₘ ≃ Fin (card Sₘ)` and continuous
reindexing `netReindex : EuclideanSpace ℝ (Fin k) → (↥Sₘ → ℝ)` identify them. -/

/-- The canonical enumeration of the finite net `Sₘ = Set.range (netRep m)` as
`Fin (Fintype.card ↥Sₘ)`. -/
noncomputable def netEnum (m : ℕ) :
    ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) ≃
      Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))) :=
  Fintype.equivFin _

/-- The enumerated net tuple `φ : Fin k → (Ω → ℝ)`: `φ i` is the `Ω → ℝ` function
underlying the `i`-th net point `(netEnum m).symm i ∈ ↥Sₘ ⊆ ↥F`. Each `φ i ∈ F`
(`netPhi_mem`). -/
noncomputable def netPhi (m : ℕ)
    (i : Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))) :
    Ω → ℝ :=
  (((netEnum hG_env hG hF_meas hF_ent m).symm i).1 : Ω → ℝ)

omit [IsProbabilityMeasure P] in
/-- Each enumerated net function `netPhi m i` lies in `F`. -/
theorem netPhi_mem (m : ℕ)
    (i : Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))) :
    netPhi hG_env hG hF_meas hF_ent m i ∈ F :=
  (((netEnum hG_env hG hF_meas hF_ent m).symm i).1).2

/-- The continuous reindexing `EuclideanSpace ℝ (Fin k) → (↥Sₘ → ℝ)` sending a
tuple `v` to the net-indexed family `s ↦ v (netEnum m s)`. This transports the
`Fin k`-indexed CLT / Gaussian limit to the net coordinate space. -/
noncomputable def netReindex (m : ℕ)
    (v : EuclideanSpace ℝ (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))
    (s : ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))) : ℝ :=
  v (netEnum hG_env hG hF_meas hF_ent m s)

omit [IsProbabilityMeasure P] in
/-- `netReindex` is continuous: each output coordinate `s` is the (continuous)
evaluation of the input Euclidean vector at `netEnum m s`. -/
theorem continuous_netReindex (m : ℕ) :
    Continuous (netReindex hG_env hG hF_meas hF_ent m) :=
  continuous_pi (fun s => (continuous_apply _).comp (EuclideanSpace.equiv _ ℝ).continuous)

omit [IsProbabilityMeasure P] in
/-- `netReindex` is measurable. -/
theorem measurable_netReindex (m : ℕ) :
    Measurable (netReindex hG_env hG hF_meas hF_ent m) :=
  (continuous_netReindex hG_env hG hF_meas hF_ent m).measurable

/-- The inverse reindexing `(↥Sₘ → ℝ) → EuclideanSpace ℝ (Fin k)` sending a net-
indexed family `g` to the tuple `i ↦ g ((netEnum m).symm i)`. Two-sided inverse of
`netReindex` (`netReindex_netReindexInv` / `netReindexInv_netReindex`). -/
noncomputable def netReindexInv (m : ℕ)
    (g : ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) → ℝ) :
    EuclideanSpace ℝ (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))) :=
  WithLp.toLp 2 (fun i => g ((netEnum hG_env hG hF_meas hF_ent m).symm i))

omit [IsProbabilityMeasure P] in
/-- `netReindexInv` is continuous. -/
theorem continuous_netReindexInv (m : ℕ) :
    Continuous (netReindexInv hG_env hG hF_meas hF_ent m) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => continuous_apply _))

omit [IsProbabilityMeasure P] in
/-- `netReindexInv` is measurable. -/
theorem measurable_netReindexInv (m : ℕ) :
    Measurable (netReindexInv hG_env hG hF_meas hF_ent m) :=
  (continuous_netReindexInv hG_env hG hF_meas hF_ent m).measurable

omit [IsProbabilityMeasure P] in
/-- `netReindex ∘ netReindexInv = id` on `↥Sₘ → ℝ`. -/
theorem netReindex_netReindexInv (m : ℕ) :
    (netReindex hG_env hG hF_meas hF_ent m) ∘ (netReindexInv hG_env hG hF_meas hF_ent m)
      = id := by
  funext g
  funext s
  simp only [Function.comp_apply, netReindex, netReindexInv, id_eq,
    PiLp.toLp_apply, Equiv.symm_apply_apply]

omit [IsProbabilityMeasure P] in
/-- `netReindexInv ∘ netReindex = id` on `EuclideanSpace ℝ (Fin k)`. -/
theorem netReindexInv_netReindex (m : ℕ) :
    (netReindexInv hG_env hG hF_meas hF_ent m) ∘ (netReindex hG_env hG hF_meas hF_ent m)
      = id := by
  funext v
  simp only [Function.comp_apply, netReindexInv, netReindex, id_eq]
  rw [show (fun i => v ((netEnum hG_env hG hF_meas hF_ent m)
      ((netEnum hG_env hG hF_meas hF_ent m).symm i))) = (fun i => v i) from by
      funext i; rw [Equiv.apply_symm_apply]]

/-- **PosSemidef of the net-coordinate marginal covariance matrix.** The matrix
`marginalCovMatrix P (netPhi m)` is positive-semidefinite: its `(i,j)` entry is the
`L²(P)` inner product `⟪centredLp ψᵢ, centredLp ψⱼ⟫` of the centred net functions
(`inner_centredLp`), so the matrix is a Gram matrix (`Matrix.posSemidef_gram`). -/
theorem marginalCovMatrix_netPhi_posSemidef (m : ℕ) :
    (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)).PosSemidef := by
  classical
  set ψ : Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))) → ↥F :=
    fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1 with hψ
  -- The marginal covariance matrix is the Gram matrix of the centred net functions.
  have hgram : marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)
      = Matrix.gram ℝ (fun i => centredLp ⟨G, hG_env, hG⟩ hF_meas (ψ i)) := by
    ext i j
    rw [Matrix.gram_apply, inner_centredLp]
    rfl
  rw [hgram]
  exact Matrix.posSemidef_gram ℝ _

/-- **Gaussianity of the Euclidean bridge readout.** The Euclidean `ψ`-readout pushforward of
`G_P` is an `IsGaussian` measure: it is the CLE-transport (`WithLp.toLp 2`, i.e.
`(EuclideanSpace.equiv).symm`) of the Pi-readout law, which is Gaussian by the
`isGaussian_fdd` field (`pBridge_isGaussian_fdd`). -/
theorem gaussianPBridge_readout_isGaussian (m : ℕ) :
    ProbabilityTheory.IsGaussian
      ((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
        (fun z : LinfF F => (WithLp.toLp 2
          (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
          EuclideanSpace ℝ (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))))))) := by
  classical
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) with hk
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1 with hψ
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  -- The Pi-readout law is Gaussian (the `isGaussian_fdd` field of `G_P`).
  have hpi : ProbabilityTheory.HasGaussianLaw (fun z : LinfF F => (fun j => z (ψ j))) ν :=
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).isGaussian_fdd
      k ψ
  -- The Euclidean readout is the CLE `(EuclideanSpace.equiv).symm` applied to the Pi-readout.
  set L := (EuclideanSpace.equiv (Fin k) ℝ).symm with hL
  have hcomp : (fun z : LinfF F => (WithLp.toLp 2 (fun j => z (ψ j)) : EuclideanSpace ℝ (Fin k)))
      = L ∘ (fun z : LinfF F => (fun j => z (ψ j))) := rfl
  haveI hpi_gauss : ProbabilityTheory.IsGaussian
      (ν.map (fun z : LinfF F => (fun j => z (ψ j)))) := hpi.isGaussian_map
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable
    (L.continuous.measurable.aemeasurable) hpi.aemeasurable]
  exact ProbabilityTheory.isGaussian_map_equiv L

/-- **Mean of the Euclidean bridge readout.** The means of the two measures agree
(both `0`): RHS by `integral_id_multivariateGaussian`; LHS coordinatewise by the
mean-zero field `gaussianPBridge_mean`. -/
theorem gaussianPBridge_readout_mean (m : ℕ) :
    ∫ x, id x
        ∂((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
          (fun z : LinfF F => (WithLp.toLp 2
            (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
            EuclideanSpace ℝ (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))))
      = ∫ x, id x
        ∂(ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ
            (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))
          (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m))) := by
  classical
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) with hk
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1 with hψ
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  set R : LinfF F → EuclideanSpace ℝ (Fin k) :=
    fun z => (WithLp.toLp 2 (fun i => z (ψ i)) : EuclideanSpace ℝ (Fin k)) with hR
  -- LHS and RHS both reduce to a single Euclidean integral, then to `0`.
  -- RHS mean = `0` (`integral_id_multivariateGaussian'`, the `[id]` form).
  rw [ProbabilityTheory.integral_id_multivariateGaussian']
  -- LHS: `∫ id ∂(ν.map R) = ∫ z, R z ∂ν`; show this Euclidean integral is `0`.
  haveI hLHS_gauss : ProbabilityTheory.IsGaussian (ν.map R) :=
    gaussianPBridge_readout_isGaussian hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne m
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
        rw [lp.coeFn_sub z w]; rfl
      rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
    exact hlip.continuous
  have hR_meas : Measurable R :=
    ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi (fun i => hcont_eval (ψ i)))).measurable
  have hR_int : Integrable R ν :=
    (MeasureTheory.integrable_map_measure aestronglyMeasurable_id
      hR_meas.aemeasurable).mp ProbabilityTheory.IsGaussian.integrable_id
  rw [integral_map hR_meas.aemeasurable aestronglyMeasurable_id]
  simp only [id_eq]
  -- Coordinatewise (via `PiLp.ext`): each coordinate of the vector integral is `0`.
  refine PiLp.ext (fun i => ?_)
  -- The `i`-th coordinate is the CLM `EuclideanSpace.proj i`, which commutes with `∫`.
  have hproj : (∫ z, R z ∂ν).ofLp i = ∫ z, (R z).ofLp i ∂ν := by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) i) hR_int
    simpa only [EuclideanSpace.coe_proj] using this.symm
  -- `(R z).ofLp i = z (ψ i)`, so each coordinate integral is `0` by `gaussianPBridge_mean`.
  have hcoord : ∀ z : LinfF F, (R z).ofLp i = z (ψ i) := fun z => rfl
  rw [show (0 : EuclideanSpace ℝ (Fin k)).ofLp i = 0 from rfl, hproj]
  simp_rw [hcoord]
  exact gaussianPBridge_mean hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (ψ i)

/-- **Covariance of the Euclidean bridge readout.** The covariance bilinear forms of the two
measures agree, reducing on basis pairs (`covariance_eval_multivariateGaussian`)
to the `cov` field of `G_P` (`pBridge_cov`) matching `marginalCovEntry`. -/
theorem gaussianPBridge_readout_covarianceBilin (m : ℕ)
    (hS_psd : (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)).PosSemidef) :
    ProbabilityTheory.covarianceBilin
        ((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
          (fun z : LinfF F => (WithLp.toLp 2
            (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
            EuclideanSpace ℝ (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))))
      = ProbabilityTheory.covarianceBilin
          (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ
              (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)))))
            (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m))) := by
  classical
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) with hk
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1 with hψ
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  set S := marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m) with hS
  set R : LinfF F → EuclideanSpace ℝ (Fin k) :=
    fun z => (WithLp.toLp 2 (fun i => z (ψ i)) : EuclideanSpace ℝ (Fin k)) with hR
  haveI hν_prob : IsProbabilityMeasure ν :=
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).isProbabilityMeasure
  -- Measurability + Gaussianity + L²-membership of the readout `R`.
  have hcont_eval : ∀ i : ↥F, Continuous (fun z : LinfF F => z i) := by
    intro i
    have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
        rw [lp.coeFn_sub z w]; rfl
      rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
      exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
    exact hlip.continuous
  have hR_meas : Measurable R :=
    ((PiLp.continuous_toLp 2 _).comp
      (continuous_pi (fun i => hcont_eval (ψ i)))).measurable
  haveI hLHS_gauss : ProbabilityTheory.IsGaussian (ν.map R) :=
    gaussianPBridge_readout_isGaussian hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne m
  -- L²-membership: `id` on `ν.map R` (Gaussian) and each `R`-coordinate on `ν`.
  have hMemLp_map : MeasureTheory.MemLp id 2 (ν.map R) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  have hMemLp_R : MeasureTheory.MemLp R 2 ν :=
    (MeasureTheory.memLp_map_measure_iff aestronglyMeasurable_id
      hR_meas.aemeasurable).mp hMemLp_map
  have hMemLp_coord : ∀ i : Fin k, MeasureTheory.MemLp (fun z : LinfF F => z (ψ i)) 2 ν := by
    intro i
    have heq : (fun z : LinfF F => z (ψ i)) = (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ R := by
      funext z; rw [EuclideanSpace.coe_proj]; rfl
    rw [heq]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitz.comp_memLp (map_zero _) hMemLp_R
  -- `⟪basisFun a, u⟫ = u a` for the Euclidean basis.
  have hbasis : ∀ (a : Fin k),
      (fun u : EuclideanSpace ℝ (Fin k) =>
        (inner ℝ ((EuclideanSpace.basisFun (Fin k) ℝ).toBasis a) u : ℝ))
        = fun u => u.ofLp a := by
    intro a; funext u
    rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply]
    have hpt : ∀ x : Fin k,
        (inner ℝ ((EuclideanSpace.single a (1:ℝ)).ofLp x) (u.ofLp x) : ℝ)
          = u.ofLp x * (if x = a then (1:ℝ) else 0) := by
      intro x; rw [PiLp.single_apply]; rfl
    simp_rw [hpt]
    simp [Finset.sum_ite_eq']
  -- Reduce the bilinear-form equality to its values on the `basisFun` basis pairs.
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply]
  -- RHS first: `covarianceBilin (mvG 0 S) eᵢ eⱼ = cov[(·)ᵢ,(·)ⱼ] = S i j`.
  rw [ProbabilityTheory.covarianceBilin_apply_eq_cov
        (μ := ProbabilityTheory.multivariateGaussian 0 S)
        ProbabilityTheory.IsGaussian.memLp_two_id,
    ProbabilityTheory.covarianceBilin_apply_eq_cov (μ := ν.map R) hMemLp_map]
  rw [hbasis i, hbasis j]
  -- `u.ofLp ·` is defeq to coordinate application `u ·`; rewrite RHS to `S i j`.
  rw [ProbabilityTheory.covariance_eval_multivariateGaussian hS_psd]
  -- LHS: pull the coordinate covariance through `R` (`covariance_map`).
  have hcoord_meas : ∀ a : Fin k,
      MeasureTheory.AEStronglyMeasurable
        (fun u : EuclideanSpace ℝ (Fin k) => u.ofLp a) (ν.map R) := by
    intro a
    have h : (fun u : EuclideanSpace ℝ (Fin k) => u.ofLp a)
        = ⇑(EuclideanSpace.proj (𝕜 := ℝ) a) := by funext u; rw [EuclideanSpace.coe_proj]
    rw [h]
    exact (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.measurable.aestronglyMeasurable
  rw [ProbabilityTheory.covariance_map (hcoord_meas i) (hcoord_meas j) hR_meas.aemeasurable]
  -- The pulled-back coordinates are exactly the bridge evaluations `z ↦ z (ψ ·)`.
  have hLcoord : ((fun u : EuclideanSpace ℝ (Fin k) => u.ofLp i) ∘ R)
      = fun z : LinfF F => z (ψ i) := rfl
  have hRcoord : ((fun u : EuclideanSpace ℝ (Fin k) => u.ofLp j) ∘ R)
      = fun z : LinfF F => z (ψ j) := rfl
  rw [hLcoord, hRcoord]
  -- `cov = E[XY] − EX·EY` (mean-zero ⟹ second moment) = `pBridge_cov` = `S i j`.
  rw [ProbabilityTheory.covariance_eq_sub (hMemLp_coord i) (hMemLp_coord j)]
  -- Flatten the `Pi`-product integrand `X * Y` to a pointwise product.
  simp only [Pi.mul_apply]
  -- The means vanish (`gaussianPBridge_mean`); the mixed second moment is the `cov` field.
  have hmi := gaussianPBridge_mean hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (ψ i)
  have hmj := gaussianPBridge_mean hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (ψ j)
  have hcov := (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep
    hF_ent hF_ne).cov (ψ i) (ψ j)
  rw [hmi, hmj, hcov]
  simp only [mul_zero, sub_zero]
  -- `S i j = marginalCovEntry P (netPhi m) i j`, and `(ψ ·) = netPhi m ·` pointwise.
  simp only [hS, marginalCovMatrix, marginalCovEntry, netPhi, hψ]

/-- **Euclidean Gaussian identity.** The `ψ`-readout
pushforward of the `P`-Brownian bridge `G_P`, where `ψ i = (netEnum m).symm i ∈ ↥F`,
equals the marginal Gaussian `multivariateGaussian 0 (marginalCovMatrix P (netPhi m))`
on `EuclideanSpace ℝ (Fin k)`.

Both are centred Gaussian (mean 0): the readout law is Gaussian by
`pBridge_isGaussian_fdd`; the multivariate Gaussian by construction. Their
covariances agree entrywise: `cov[z(ψ i), z(ψ j); G_P] = P(ψi·ψj) − Pψi·Pψj`
(`pBridge_cov`, plus mean-zero) `= marginalCovEntry P (netPhi m) i j` (since
`(netPhi m) i = ψ i` as `Ω → ℝ`). Two centred Gaussians with equal covariance are
equal (`IsGaussian.ext`) on `EuclideanSpace ℝ (Fin k)`:
* **IsGaussian (LHS).** `pBridge_isGaussian_fdd m ψ` gives `IsGaussian` of the
  `Fin k → ℝ` (Pi) readout law `ν.map (fun z => fun i => z (ψ i))`; transport to
  the `EuclideanSpace` readout via `WithLp.toLp 2` (a continuous linear equiv, so
  pushforward preserves Gaussianity: `map_map` + `IsGaussian.map` of a CLE).
* **Mean 0.** `μ[id] = 0` for both, by `gaussianPBridge_mean` and
  `integral_id_multivariateGaussian'`.
* **Covariance.** `covarianceBilin` equality reduces (basis pairs) to
  `cov[xᵢ,xⱼ]` matching: `covariance_eval_multivariateGaussian` gives `S i j =
  marginalCovEntry P (netPhi m) i j`; for the bridge, `cov = second moment` (by
  mean-zero) `= pBridge_cov (ψ i) (ψ j) = marginalCovEntry`. -/
theorem gaussianPBridge_readout_eq_multivariateGaussian (m : ℕ) :
    (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
        (fun z : LinfF F => (WithLp.toLp 2
          (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
          EuclideanSpace ℝ (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))))))
      = ProbabilityTheory.multivariateGaussian 0
          (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)) := by
  classical
  -- Abbreviations: net cardinality `k`, enumerated net tuple `ψ : Fin k → ↥F`,
  -- the bridge law `ν`, the covariance matrix `S`, and the Euclidean readout `R`.
  set k := Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) with hk
  set ψ : Fin k → ↥F := fun i => ((netEnum hG_env hG hF_meas hF_ent m).symm i).1 with hψ
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  set S := marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m) with hS
  -- The Pi-readout `Rpi z = (z (ψ j))ⱼ` and the Euclidean readout `R = toLp ∘ Rpi`.
  set Rpi : LinfF F → (Fin k → ℝ) := fun z j => z (ψ j) with hRpi
  -- `S` is positive-semidefinite (covariance matrix).
  have hS_psd : S.PosSemidef :=
    marginalCovMatrix_netPhi_posSemidef hG_env hG hF_meas hF_ent m
  -- The two measures are `IsGaussian`: RHS by construction, LHS by CLE-transport.
  haveI hRHS_gauss : ProbabilityTheory.IsGaussian
      (ProbabilityTheory.multivariateGaussian 0 S) := inferInstance
  haveI hLHS_gauss : ProbabilityTheory.IsGaussian
      (ν.map (fun z : LinfF F => (WithLp.toLp 2 (Rpi z) : EuclideanSpace ℝ (Fin k)))) :=
    gaussianPBridge_readout_isGaussian hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne m
  -- `IsGaussian.ext`: equal means + equal covariance bilinear forms.
  refine ProbabilityTheory.IsGaussian.ext ?_ ?_
  · -- Means: both `0`.
    exact gaussianPBridge_readout_mean hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne m
  · -- Covariances: `covarianceBilin` agree (reduced on basis pairs to `cov = S`).
    exact gaussianPBridge_readout_covarianceBilin hG_env hG hF_meas hH_inf hH_sep
      hF_ent hF_ne m hS_psd

/-- **Standardized-form reconciliation and enumeration.** The net-coordinate
empirical readout equals the reindexed `IsMarginalCLT`-standardised vector,
pointwise in `ξ`. For every `ξ` and net point `s`,
`netTuple m (𝔾ₙ ξ) s = netReindex m (stdVec n ξ) s`, where
`stdVec n ξ = (√n)⁻¹ • (∑_{j<n} tupleVec (netPhi m) (X_j ξ) − n • E[tupleVec (netPhi m) (X_0)])`.

This is the algebraic identity reconciling `empiricalProcess`'s `√n(Pₙ − P)f`
centring with the standardised-sum form: for `s` with `netPhi m (netEnum m s) = s.1`,
the coordinate `(√n)⁻¹(∑_j s.1(X_jξ) − n∫ s.1 dP)` equals
`√n(n⁻¹∑_j s.1(X_jξ) − ∫ s.1 dP) = empiricalProcess P n (X·ξ) s.1`
(using `(√n)⁻¹·n = √n` and `E[s.1(X_0)] = ∫ s.1 dP` via `hX_law`). -/
theorem netTuple_empirical_eq_reindex_std (h_clt : IsMarginalCLT F P)
    (m : ℕ) {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (n : ℕ) (ξ : Ξ) :
    netTuple hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))
      = netReindex hG_env hG hF_meas hF_ent m
          ((Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n,
              tupleVec (netPhi hG_env hG hF_meas hF_ent m) (X i ξ)
            - n • ∫ ξ, tupleVec (netPhi hG_env hG hF_meas hF_ent m) (X 0 ξ) ∂μ)) := by
  classical
  set φ := netPhi hG_env hG hF_meas hF_ent m with hφ
  -- `P` is a probability measure (pushforward of `μ` by the measurable `X 0`).
  haveI hP_prob : IsProbabilityMeasure P := by
    rw [← hX_law]; exact Measure.isProbabilityMeasure_map (hX_meas 0).aemeasurable
  -- Each `φ i ∈ F` is `MemLp 2 P`, hence integrable, and measurable.
  have hφ_mem : ∀ i, φ i ∈ F := netPhi_mem hG_env hG hF_meas hF_ent m
  have hφ_meas : ∀ i, Measurable (φ i) := fun i => hF_meas (φ i) (hφ_mem i)
  have hφ_intP : ∀ i, Integrable (φ i) P := fun i =>
    (h_clt.1 (φ i) (hφ_mem i)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  -- `tupleVec φ` is measurable.
  have htv_meas : Measurable (tupleVec φ) := by
    have hpi : Measurable (fun ω => (fun i => φ i ω) : Ω → (Fin _ → ℝ)) :=
      measurable_pi_iff.mpr hφ_meas
    exact (EuclideanSpace.equiv _ ℝ).symm.continuous.measurable.comp hpi
  -- The vector `tupleVec φ ∘ X 0` is integrable on `μ` (each coordinate is).
  have htv_intP : Integrable (tupleVec φ) P := by
    have hmemLp : MemLp (tupleVec φ) 2 P := by
      refine memLp_piLp_iff.mpr (fun i => ?_)
      have : (fun ω => tupleVec φ ω i) = φ i := rfl
      rw [this]; exact h_clt.1 (φ i) (hφ_mem i)
    exact hmemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have htv_int : Integrable (fun ζ => tupleVec φ (X 0 ζ)) μ := by
    have : Integrable (tupleVec φ ∘ X 0) μ :=
      (integrable_map_measure htv_meas.aestronglyMeasurable (hX_meas 0).aemeasurable).mp
        (by rw [hX_law]; exact htv_intP)
    exact this
  -- Work coordinatewise on the net point `s`.
  funext s
  simp only [netReindex]
  set i := netEnum hG_env hG hF_meas hF_ent m s with hi
  -- The enumerated function `φ i` is the underlying `Ω → ℝ` of the net point `s`.
  have hφi : φ i = (s.1 : Ω → ℝ) := by
    rw [hφ, netPhi, hi, Equiv.symm_apply_apply]
  -- Coordinate readout of the Euclidean vector at `i`, via the projection CLM.
  have hproj_tv : ∀ ω, (EuclideanSpace.proj i) (tupleVec φ ω) = φ i ω := by
    intro ω; rw [EuclideanSpace.coe_proj]; rfl
  have hcoord : ((Real.sqrt n)⁻¹ • (∑ j ∈ Finset.range n, tupleVec φ (X j ξ)
        - n • ∫ ζ, tupleVec φ (X 0 ζ) ∂μ)) i
      = (Real.sqrt n)⁻¹ * ((∑ j ∈ Finset.range n, φ i (X j ξ))
          - n * ∫ ζ, φ i (X 0 ζ) ∂μ) := by
    have hint_i : (EuclideanSpace.proj i) (∫ ζ, tupleVec φ (X 0 ζ) ∂μ)
        = ∫ ζ, φ i (X 0 ζ) ∂μ := by
      rw [← ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i) htv_int]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun ζ => hproj_tv (X 0 ζ)))
    have hkey : (EuclideanSpace.proj i) ((Real.sqrt n)⁻¹ • (∑ j ∈ Finset.range n,
          tupleVec φ (X j ξ) - n • ∫ ζ, tupleVec φ (X 0 ζ) ∂μ))
        = (Real.sqrt n)⁻¹ * ((∑ j ∈ Finset.range n, φ i (X j ξ))
            - n * ∫ ζ, φ i (X 0 ζ) ∂μ) := by
      rw [map_smul, map_sub, map_sum, map_nsmul, hint_i]
      simp only [hproj_tv, smul_eq_mul, nsmul_eq_mul]
    rw [← hkey, EuclideanSpace.coe_proj]
  rw [hcoord]
  -- LHS: `netTuple (𝔾ₙ ξ) s = empiricalProcess P n (X·ξ) s.1`.
  show empiricalProcess P n (fun j : Fin n => X j.val ξ) (s.1 : Ω → ℝ)
    = (Real.sqrt n)⁻¹ * ((∑ j ∈ Finset.range n, φ i (X j ξ))
        - n * ∫ ζ, φ i (X 0 ζ) ∂μ)
  -- The integral over `μ` of `φ i ∘ X 0` equals `∫ φ i dP` (law of `X 0` is `P`).
  have hint_law : ∫ ζ, φ i (X 0 ζ) ∂μ = ∫ x, φ i x ∂P := by
    rw [← hX_law, integral_map (hX_meas 0).aemeasurable
      (hφ_meas i).aestronglyMeasurable]
  rw [hint_law, hφi]
  -- The empirical sum over `Finset.range n` ↔ over `Fin n`.
  have hsum : ∑ j ∈ Finset.range n, (s.1 : Ω → ℝ) (X j ξ)
      = ∑ j : Fin n, (s.1 : Ω → ℝ) (X j.val ξ) := by
    rw [Finset.sum_range fun j => (s.1 : Ω → ℝ) (X j ξ)]
  -- Unfold the empirical process and reconcile the `√n` prefactors.
  rw [empiricalProcess, empiricalAvg, hsum]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hsqrt_ne : Real.sqrt n ≠ 0 := hsqrt_pos.ne'
    have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    -- `√n·n⁻¹ = (√n)⁻¹` and `(√n)⁻¹·n = √n`.
    have h1 : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      field_simp; linear_combination hsq
    have h2 : (Real.sqrt n)⁻¹ * (n : ℝ) = Real.sqrt n := by
      rw [inv_mul_eq_div, eq_comm, eq_div_iff hsqrt_ne, hsq]
    -- Reconcile via the two scalar identities `h1`, `h2`.
    set A := ∑ j : Fin n, (s.1 : Ω → ℝ) (X j.val ξ) with hA
    set B := ∫ x, (s.1 : Ω → ℝ) x ∂P with hB
    linear_combination A * h1 + B * h2

/-- **Gaussian limit identification.** The `netTuple`-pushforward of
the `P`-Brownian bridge `G_P` equals the `netReindex`-pushforward of the marginal
Gaussian `multivariateGaussian 0 (marginalCovMatrix P (netPhi m))`.

Both are centred Gaussian laws on `↥Sₘ → ℝ`; they have equal covariance because the
`G_P` covariance `cov(z s, z t) = P(s·t) − Ps·Pt` (`pBridge_cov`) matches
`marginalCovEntry P (netPhi m)` (the `(netEnum s, netEnum t)` entry of
`marginalCovMatrix`). Two centred finite-dim Gaussians with equal covariance are
equal (`IsGaussian.ext` on the pushed-forward Euclidean laws, via the enumeration
isometry). `pBridge_isGaussian_fdd` supplies the Gaussianity of the `G_P` marginal. -/
theorem gaussianPBridge_map_netTuple_eq (m : ℕ) :
    (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
        (netTuple hG_env hG hF_meas hF_ent m)
      = (ProbabilityTheory.multivariateGaussian 0
            (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m))).map
          (netReindex hG_env hG hF_meas hF_ent m) := by
  -- It suffices to compare the `netReindexInv`-pushforwards (a measurable equiv with
  -- measurable left-inverse `netReindex`): both equal the marginal Gaussian on `ℝ^k`.
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  set mvg := ProbabilityTheory.multivariateGaussian 0
    (marginalCovMatrix P (netPhi hG_env hG hF_meas hF_ent m)) with hmvg
  -- Recover each side from its `netReindexInv`-pushforward via `netReindex ∘ netReindexInv = id`.
  have hrecover : ∀ ρ : Measure (↥(Set.range (netRep hG_env hG hF_meas hF_ent m)) → ℝ),
      (ρ.map (netReindexInv hG_env hG hF_meas hF_ent m)).map
        (netReindex hG_env hG hF_meas hF_ent m) = ρ := by
    intro ρ
    rw [Measure.map_map (measurable_netReindex hG_env hG hF_meas hF_ent m)
      (measurable_netReindexInv hG_env hG hF_meas hF_ent m),
      netReindex_netReindexInv, Measure.map_id]
  rw [← hrecover (ν.map (netTuple hG_env hG hF_meas hF_ent m)),
    ← hrecover (mvg.map (netReindex hG_env hG hF_meas hF_ent m))]
  congr 1
  -- `(ν.map netTuple).map netReindexInv = ν.map (netReindexInv ∘ netTuple) = readout`.
  rw [Measure.map_map (measurable_netReindexInv hG_env hG hF_meas hF_ent m)
      (measurable_netTuple hG_env hG hF_meas hF_ent m),
    Measure.map_map (measurable_netReindexInv hG_env hG hF_meas hF_ent m)
      (measurable_netReindex hG_env hG hF_meas hF_ent m),
    netReindexInv_netReindex, Measure.map_id]
  -- `netReindexInv ∘ netTuple = ψ-readout`; identify with the marginal Gaussian (core lemma).
  have hcomp : (netReindexInv hG_env hG hF_meas hF_ent m) ∘
      (netTuple hG_env hG hF_meas hF_ent m)
      = fun z : LinfF F => (WithLp.toLp 2
          (fun i => z ((netEnum hG_env hG hF_meas hF_ent m).symm i).1) :
          EuclideanSpace ℝ (Fin (Fintype.card ↥(Set.range (netRep hG_env hG hF_meas hF_ent m))))) := by
    funext z
    rfl
  rw [hcomp]
  exact gaussianPBridge_readout_eq_multivariateGaussian hG_env hG hF_meas hH_inf hH_sep
    hF_ent hF_ne m

/-- **Finite-dimensional CLT on the net coordinate space `Sₘ → ℝ`.** The
pushforward laws of the net-coordinate empirical process `μ.map (netTuple ∘ 𝔾ₙ)`
converge weakly to `gaussianPBridge.map netTuple` on `Sₘ → ℝ`.

This is the genuine finite-dimensional CLT, isolated from the `LinfF F`-valued
transport (`netRecon` continuous-mapping, done in
`weakConverges_findim_proj_of_marginalCLT`). The proof enumerates `Sₘ` as a tuple
`φ : Fin k → ↥F` (the `netIndexFintype` enumeration), applies the marginal-CLT
clause `h_clt.2` (= `IsMarginalCLT.fdd`, via `marginalCLT_fdd_of_iid`) to obtain
`TendstoInDistribution (standardised empirical vector) → multivariateGaussian 0
(marginalCovMatrix P (φ ·))`, bridges `TendstoInDistribution` to `WeakConverges`
of pushforwards (`ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`), and
identifies the limit `gaussianPBridge.map netTuple` with the same Gaussian via the
covariance match `pBridge_cov` + the Gaussian-marginal field `pBridge_isGaussian_fdd`
(two centred Gaussians with equal covariance are equal). The `empiricalProcess`
centring `√n(Pₙ − P)f` and the `IsMarginalCLT` standardisation
`(√n)⁻¹•(∑ tupleVec − n•E)` coincide coordinatewise (`empiricalProcess` /
`tupleVec` unfolding).

vdV p.261 (⟸), step 1: finite-dimensional convergence. -/
theorem weakConverges_netTuple_of_marginalCLT (h_clt : IsMarginalCLT F P)
    (m : ℕ) {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConverges
      (fun n => μ.map (fun ξ => netTuple hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))))
      ((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
        (netTuple hG_env hG hF_meas hF_ent m)) := by
  classical
  -- Abbreviations: the enumerated net tuple `φ = netPhi m` and the marginal Gaussian.
  set φ := netPhi hG_env hG hF_meas hF_ent m with hφ
  have hφ_mem : ∀ i, φ i ∈ F := netPhi_mem hG_env hG hF_meas hF_ent m
  -- The standardised CLT vector.
  set stdVec : ℕ → Ξ → EuclideanSpace ℝ (Fin _) := fun n ξ =>
    (Real.sqrt n)⁻¹ • (∑ i ∈ Finset.range n, tupleVec φ (X i ξ)
      - n • ∫ ζ, tupleVec φ (X 0 ζ) ∂μ) with hstdVec
  -- Apply the marginal CLT (`IsMarginalCLT.fdd`) to the enumerated net tuple.
  obtain ⟨Y, hY, hTID⟩ := h_clt.2 μ X hX_meas hX_indep hX_id hX_law φ hφ_mem
  -- `WeakConverges (μ.map stdVec) (multivariateGaussian 0 (marginalCovMatrix P φ))`.
  have hWC_euclid : WeakConverges (fun n => μ.map (stdVec n))
      (ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P φ)) := by
    -- The `ProbabilityMeasure`-valued limit point is `⟨mvg.map Y, _⟩ = ⟨mvg, _⟩`.
    have hlim_eq : (⟨(ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P φ)).map Y,
          Measure.isProbabilityMeasure_map hTID.aemeasurable_limit⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin _)))
        = ⟨ProbabilityTheory.multivariateGaussian 0 (marginalCovMatrix P φ),
            inferInstance⟩ :=
      Subtype.ext hY.map_eq
    intro g
    -- Bridge `TendstoInDistribution.tendsto` (in `ProbabilityMeasure`) to integrals.
    have hbridge := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hlim_eq ▸ hTID.tendsto)) g
    exact hbridge
  -- Map both sides by the continuous reindexing `netReindex` (continuous-mapping).
  have hWC_net := hWC_euclid.map (continuous_netReindex hG_env hG hF_meas hF_ent m)
    (measurable_netReindex hG_env hG hF_meas hF_ent m)
  -- Rewrite the limit via Gaussian identification.
  rw [← gaussianPBridge_map_netTuple_eq hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne m] at hWC_net
  -- Rewrite the sequence: `(μ.map stdVec).map netReindex = μ.map (netTuple ∘ 𝔾ₙ)`.
  have hseq : ∀ n : ℕ,
      (μ.map (stdVec n)).map (netReindex hG_env hG hF_meas hF_ent m)
        = μ.map (fun ξ => netTuple hG_env hG hF_meas hF_ent m
            (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
              (memℓp_empiricalProcess
                ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ)))) := by
    intro n
    rw [Measure.map_map (measurable_netReindex hG_env hG hF_meas hF_ent m)
      (by
        -- `stdVec n` is measurable: finite affine combination of `tupleVec φ ∘ X i`.
        have htv : Measurable (tupleVec φ) := by
          have hpi : Measurable (fun ω => (fun i => φ i ω) : Ω → (Fin _ → ℝ)) :=
            measurable_pi_iff.mpr (fun i => hF_meas (φ i) (hφ_mem i))
          exact (EuclideanSpace.equiv _ ℝ).symm.continuous.measurable.comp hpi
        exact Measurable.const_smul
          ((Finset.measurable_sum _ (fun i _ => htv.comp (hX_meas i))).sub measurable_const)
          ((Real.sqrt (n : ℝ))⁻¹))]
    -- Pointwise: `netReindex (stdVec n ξ) = netTuple (𝔾ₙ ξ)`.
    refine Measure.map_congr (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Function.comp_apply]
    exact (netTuple_empirical_eq_reindex_std hG_env hG hF_meas hF_ent h_clt m μ X hX_meas
      hX_id hX_law n ξ).symm
  rw [funext hseq] at hWC_net
  exact hWC_net

/-- **Finite-dimensional CLT through the net, in law form.** The pushforward
laws of the projected empirical process `μ.map (πₘ ∘ 𝔾ₙ)` converge weakly to the
`πₘ`-pushforward of `G_P = gaussianPBridge`.

The projected map `πₘ z` depends only on
the values of `z` on the finite net `Sₘ = range (netRep m)` (finite by
`finite_range_netRep`), so both `μ.map (πₘ ∘ 𝔾ₙ)` and `gaussianPBridge.map πₘ`
factor through the finite-dimensional coordinate space `ℝ^{Sₘ}`. On that space the
convergence is exactly the finite-dim CLT: enumerate `Sₘ` as a tuple
`φ : Fin k → ↥F`, apply `IsMarginalCLT.fdd` to get
`TendstoInDistribution → multivariateGaussian 0 (marginalCovMatrix P (φ ·))`, and
identify that Gaussian with the `φ`-readout of `gaussianPBridge` via the covariance
match `pBridge_cov = marginalCovEntry` + `pBridge_isGaussian_fdd` (two centred
Gaussians with equal covariance are equal). The continuous reconstruction
`ℝ^{Sₘ} → LinfF F` (a coordinate-collapse, continuous) then transports the
finite-tuple weak convergence to the `LinfF F`-valued statement via the
continuous-mapping theorem `WeakConverges.map`.

vdV p.261 (⟸), step 1 core: the finite-dimensional distributions converge. -/
theorem weakConverges_findim_proj_of_marginalCLT (h_clt : IsMarginalCLT F P)
    (m : ℕ) {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConverges
      (fun n => μ.map (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ)))))
      ((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
        (finiteNetProj hG_env hG hF_meas hF_ent m)) := by
  -- Reduce to weak convergence on the finite coordinate space `Sₘ → ℝ` via the
  -- factorization `πₘ = netRecon ∘ netTuple` and continuous-mapping (`netRecon`
  -- continuous). Both pushforwards split through `netTuple` by `Measure.map_map`.
  have hμmap : ∀ n : ℕ,
      μ.map (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ))))
        = (μ.map (fun ξ => netTuple hG_env hG hF_meas hF_ent m
            (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
              (memℓp_empiricalProcess
                ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ))))).map
          (netRecon hG_env hG hF_meas hF_ent m) := by
    intro n
    have hcomp : (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ))))
        = (netRecon hG_env hG hF_meas hF_ent m) ∘
          (fun ξ => netTuple hG_env hG hF_meas hF_ent m
            (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
              (memℓp_empiricalProcess
                ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ)))) := by
      funext ξ
      rw [Function.comp_apply, finiteNetProj_eq_comp, Function.comp_apply]
    rw [hcomp, ← Measure.map_map (continuous_netRecon hG_env hG hF_meas hF_ent m).measurable
      (measurable_projectedEmpirical' hG_env hG hF_meas hF_ent m X hX_meas n)]
  have hgmap :
      (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
        (finiteNetProj hG_env hG hF_meas hF_ent m)
        = ((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
            (netTuple hG_env hG hF_meas hF_ent m)).map
          (netRecon hG_env hG hF_meas hF_ent m) := by
    rw [Measure.map_map (continuous_netRecon hG_env hG hF_meas hF_ent m).measurable
      (measurable_netTuple hG_env hG hF_meas hF_ent m), finiteNetProj_eq_comp]
  rw [funext hμmap, hgmap]
  exact (weakConverges_netTuple_of_marginalCLT hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
    h_clt m μ X hX_meas hX_indep hX_id hX_law).map
    (continuous_netRecon hG_env hG hF_meas hF_ent m)
    (continuous_netRecon hG_env hG hF_meas hF_ent m).measurable

/-- **Finite-dimensional CLT through the net `Sₘ`.** For each fixed scale
`m`, the `πₘ`-projected empirical process converges weakly in the outer sense to
the pushforward of `G_P = gaussianPBridge` under `πₘ`.

The projected map `ξ ↦ finiteNetProj m (𝔾ₙ ξ)` factors through the finite-
dimensional coordinate space `ℝ^{Sₘ}`, hence is Borel-measurable
(`measurable_projectedEmpirical`); so `weakConvergesOuter_of_measurable`
reduces the `⇝ₒ` claim to ordinary weak convergence of pushforwards
(`weakConverges_findim_proj_of_marginalCLT`), which is exactly the
finite-dim CLT `IsMarginalCLT.fdd` evaluated on the net tuple. Covariance
identification of the limit with the `πₘ`-pushforward of the `G_P` marginal
uses `pBridge_cov` and `pBridge_isGaussian_fdd`.

vdV p.261 (⟸), step 1: the finite-dimensional distributions converge. -/
theorem weakConvergesOuter_findim_proj (h_clt : IsMarginalCLT F P) (m : ℕ)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    WeakConvergesOuter (fun _ => μ)
      (fun n ξ => finiteNetProj hG_env hG hF_meas hF_ent m
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
          (memℓp_empiricalProcess
            ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
            (fun i : Fin n => X i.val ξ))))
      ((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).map
        (finiteNetProj hG_env hG hF_meas hF_ent m)) := by
  -- Reduce the `⇝ₒ` goal to ordinary weak convergence of pushforwards via the
  -- measurable-reduction lemma.
  rw [weakConvergesOuter_of_measurable
    (fun n => measurable_projectedEmpirical hG_env hG hF_meas hF_ent m X hX_meas n)]
  -- The reduced goal is exactly the finite-dimensional CLT in law form.
  exact weakConverges_findim_proj_of_marginalCLT hG_env hG hF_meas hH_inf hH_sep
    hF_ent hF_ne h_clt m μ X hX_meas hX_indep hX_id hX_law

/-- **Empirical discretization error is asymptotically negligible.** For
every `ε > 0`, the outer probability that the `ℓ∞(F)`-distance between the
empirical process `𝔾ₙ` and its net projection `πₘ𝔾ₙ` exceeds `ε` tends to `0` as
`m → ∞`, uniformly in `n` in the `limsupₙ` sense.

The sup-norm error is majorized by `supNormOver (localized 2⁻ᵐ-class) 𝔾ₙ` via
`empiricalProcess_sub` (the coordinates of `𝔾ₙ − πₘ𝔾ₙ` are differences
`𝔾ₙ f − 𝔾ₙ (netRep m f)` of `2⁻ᵐ`-close pairs). The `m → ∞` vanishing of its
`limsupₙ` is the chaining content of `hF_ent`
(`localizedChainBound_of_finiteEntropy` / `equicontinuity_chaining_assembly_brick`
in `ChainingAssembly.lean`), followed here by passage from that real-valued
`∫⁻` bound to the **outer probability** `E*`/`P*`.

vdV p.261 (⟸), step 2: the empirical process is asymptotically uniformly close
to its finite-net discretization. -/
theorem empirical_proj_error_outer (h_eq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun m => limsup
        (fun n => outerExpectation μ
          (fun ξ => Set.indicator
            {ξ | ε < ‖empiricalProcessLinf (fun i : Fin n => X i.val ξ)
                  (memℓp_empiricalProcess
                    ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                    (fun i : Fin n => X i.val ξ))
                - finiteNetProj hG_env hG hF_meas hF_ent m
                    (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
                      (memℓp_empiricalProcess
                        ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                        (fun i : Fin n => X i.val ξ)))‖}
            (fun _ => (1 : ℝ≥0∞)) ξ))
        atTop)
      atTop (𝓝 0) := by
  -- Abbreviation for the empirical process packaged in `ℓ∞(F)`.
  set 𝔾 : ∀ (n : ℕ) (ξ : Ξ), LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ)) with h𝔾
  -- Reduce `Tendsto … (𝓝 0)` to an `∀ η>0, ∀ᶠ m, term m ≤ η` statement.
  rw [ENNReal.tendsto_nhds_zero]
  intro η₀ hη₀
  -- Pick a positive real `η` with `ENNReal.ofReal η ≤ η₀`.
  obtain ⟨a, ha0, haη⟩ := exists_between hη₀
  have ha_ne : a ≠ ⊤ := (lt_of_lt_of_le haη le_top).ne
  set η : ℝ := a.toReal with hη_def
  have hη_pos : 0 < η := ENNReal.toReal_pos ha0.ne' ha_ne
  have hofReal : ENNReal.ofReal η = a := ENNReal.ofReal_toReal ha_ne
  -- Apply the outer-sup equicontinuity modulus at oscillation `ε`, mass `η`.
  obtain ⟨δ, hδ_pos, hδ⟩ := h_eq μ X hX_meas hX_indep hX_id hX_law ε η hε hη_pos
  -- For `m` large enough that `2⁻ᵐ < δ`, the bad event is contained in the modulus event.
  -- `2⁻ᵐ = (1/2)ᵐ` is a null sequence: pick `N` with `(1/2)ᴺ < δ`.
  obtain ⟨N, hN0⟩ := exists_pow_lt_of_lt_one hδ_pos (by norm_num : (2⁻¹ : ℝ) < 1)
  have hN : ∀ m ≥ N, (2 : ℝ) ^ (-(m : ℤ)) < δ := by
    intro m hm
    have hconv : (2 : ℝ) ^ (-(m : ℤ)) = (2⁻¹ : ℝ) ^ m := by
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [hconv]
    exact lt_of_le_of_lt
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hm) hN0
  refine Filter.eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  -- The term at scale `m` equals `limsupₙ P*{ε < ‖𝔾ₙ − πₘ𝔾ₙ‖}` (indicator-1 = outer measure).
  have hterm : (fun n => outerExpectation μ
      (fun ξ => Set.indicator
        {ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}
        (fun _ => (1 : ℝ≥0∞)) ξ))
      = fun n => μ.outerMeasureStar
          {ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖} := by
    funext n
    rfl
  -- Bound each `n`-term by the modulus event's outer measure, monotone in the event.
  have hsubset : ∀ n,
      {ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}
        ⊆ {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
            ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    -- supNorm > ε ⟹ ∃ coordinate `t : ↥F` with `ε < |(𝔾ₙ − πₘ𝔾ₙ) t|`.
    -- `↥F` must be nonempty: otherwise the difference is `0` and `ε < 0` is absurd.
    have hne : Nonempty ↥F := by
      by_contra hF_empty
      rw [not_nonempty_iff] at hF_empty
      rw [lp.eq_zero' (𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)),
        norm_zero] at hξ
      exact absurd hξ (not_lt.2 hε.le)
    obtain ⟨c, ⟨t, rfl⟩, hct⟩ :=
      (lt_isLUB_iff (lp.isLUB_norm (𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)))).1 hξ
    -- The coordinate at `t` is `𝔾ₙ t − 𝔾ₙ (netRep m t)`.
    have hcoord : (𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)) t
        = empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)
          - empiricalProcess P n (fun i : Fin n => X i.val ξ)
              ((netRep hG_env hG hF_meas hF_ent m t : Ω → ℝ)) := by
      rw [lp.coeFn_sub, Pi.sub_apply, finiteNetProj_apply]
      rfl
    refine ⟨t, netRep hG_env hG hF_meas hF_ent m t, ?_, ?_⟩
    · -- `distL2 P t (netRep m t) < 2⁻ᵐ < δ`.
      exact lt_of_lt_of_le (netRep_distL2_lt hG_env hG hF_meas hF_ent m t) (le_of_lt (hN m hm))
    · -- `ε < |coordinate|` from `ε < c = ‖coordinate‖ = |coordinate|`.
      rw [← Real.norm_eq_abs, ← hcoord]
      exact hct
  -- Assemble: `term m = limsupₙ P*(bad) ≤ limsupₙ P*(modulus) ≤ ofReal η ≤ η₀`.
  rw [hterm]
  calc limsup (fun n => μ.outerMeasureStar
          {ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}) atTop
      ≤ limsup (fun n => μ.outerMeasureStar
          {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
            ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}) atTop :=
        limsup_le_limsup (Filter.Eventually.of_forall fun n =>
          outerMeasureStar_mono μ (hsubset n))
    _ ≤ ENNReal.ofReal η := hδ
    _ = a := hofReal
    _ ≤ η₀ := haη.le

omit [IsProbabilityMeasure P] in
/-- **The sequence `2⁻ᵐ` eventually undercuts every `δ > 0`.** For every `δ > 0`
there is `N` such that `(2 : ℝ) ^ (-(m : ℤ)) < δ` for all `m ≥ N`. (The net
scales `2⁻ᵐ` form a null sequence, so they eventually fall below any radius.) -/
theorem eventually_two_zpow_neg_lt {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, (2 : ℝ) ^ (-(m : ℤ)) < δ := by
  -- `2⁻ᵐ = (1/2)ᵐ` and `(1/2)ᵐ` is a null sequence: pick `N` with `(1/2)ᴺ < δ`.
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2⁻¹ : ℝ) < 1)
  refine Filter.eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  have hconv : (2 : ℝ) ^ (-(m : ℤ)) = (2⁻¹ : ℝ) ^ m := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hconv]
  calc (2⁻¹ : ℝ) ^ m
        ≤ (2⁻¹ : ℝ) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ < δ := hN

omit [IsProbabilityMeasure P] in
/-- **The net projection converges to every uniformly continuous path.** If a
path `z : LinfF F` is `distL2 P`-uniformly continuous (the `ucPaths` predicate),
then its finite-net projections converge to it in `ℓ∞(F)`:
`Tendsto (fun m => finiteNetProj m z) atTop (𝓝 z)`.

For ε > 0, the UC predicate supplies δ > 0 with `distL2-close ⟹ |z f − z g| < ε`;
since `distL2 P t (netRep m t) < 2⁻ᵐ` (`netRep_distL2_lt`) and `2⁻ᵐ < δ` for `m`
large (`eventually_two_zpow_neg_lt`), the coordinate gap
`|finiteNetProj m z t − z t| = |z (netRep m t) − z t| < ε` holds for ALL `t`
simultaneously, so `‖finiteNetProj m z − z‖ ≤ ε` (`lp.norm_le_of_forall_le`). -/
theorem tendsto_finiteNetProj_of_ucPath (z : LinfF F)
    (hz : ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ → |z f - z g| < ε) :
    Tendsto (fun m => finiteNetProj hG_env hG hF_meas hF_ent m z) atTop (𝓝 z) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Use ε/2 in the UC predicate so the sup-bound `≤ ε/2` gives strict `< ε`.
  obtain ⟨δ, hδ_pos, hδ⟩ := hz (ε / 2) (by linarith)
  -- For `m` large, `2⁻ᵐ < δ`.
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (eventually_two_zpow_neg_lt hδ_pos)
  refine ⟨N, fun m hm => ?_⟩
  rw [dist_eq_norm]
  -- Each coordinate `t` of `finiteNetProj m z − z` is bounded by `ε/2`.
  have hbound : ∀ t : ↥F,
      ‖(finiteNetProj hG_env hG hF_meas hF_ent m z - z) t‖ ≤ ε / 2 := by
    intro t
    have hcoord : (finiteNetProj hG_env hG hF_meas hF_ent m z - z) t
        = z (netRep hG_env hG hF_meas hF_ent m t) - z t := by
      rw [lp.coeFn_sub]
      simp only [Pi.sub_apply, finiteNetProj_apply]
    rw [hcoord, Real.norm_eq_abs]
    -- `distL2 P (netRep m t) t < δ` (via symmetry of `netRep_distL2_lt`).
    have hdist : distL2 P ((netRep hG_env hG hF_meas hF_ent m t : Ω → ℝ)) (t : Ω → ℝ) < δ := by
      rw [distL2_comm]
      exact lt_of_lt_of_le (netRep_distL2_lt hG_env hG hF_meas hF_ent m t)
        (le_of_lt (hN m hm))
    exact le_of_lt (hδ _ _ hdist)
  calc ‖finiteNetProj hG_env hG hF_meas hF_ent m z - z‖
        ≤ ε / 2 := lp.norm_le_of_forall_le (by linarith) hbound
      _ < ε := by linarith

/-- **Limit discretization error vanishes.** For every bounded continuous
readout `f : LinfF F →ᵇ ℝ`, the integral of `|f(πₘ z) − f z|` against
`G_P = gaussianPBridge` tends to `0` as `m → ∞`.

`G_P` concentrates on the `distL2 P`-uniformly-continuous paths
(`IsPBrownianBridge.ucPaths` of `isPBrownianBridge_gaussianPBridge`): for a.e.
path `z` the values `z (netRep m t)` converge to `z t` uniformly in `t` (the net
is `2⁻ᵐ`-fine), so `πₘ z → z` in `ℓ∞(F)` pointwise a.e., whence
`f (πₘ z) → f z` by continuity of `f`. The integrand is bounded by `2‖f‖` and
`G_P` is a probability measure (tightness gives finiteness), so DCT closes it.

vdV p.261 (⟸), step 3: the limit's net discretization converges to the limit. -/
theorem limit_proj_error (f : LinfF F →ᵇ ℝ) :
    Tendsto
      (fun m => ∫ z, |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z|
        ∂(gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne))
      atTop (𝓝 0) := by
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  -- `G_P` is a probability measure (so the constant dominator is integrable).
  have hprob : IsProbabilityMeasure ν :=
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent
      hF_ne).isProbabilityMeasure
  -- `G_P`-a.e. path is `distL2 P`-uniformly continuous.
  have hucp := (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep
    hF_ent hF_ne).ucPaths
  -- The integrand sequence, written as a function of `m`.
  set Φ : ℕ → LinfF F → ℝ :=
    fun m z => |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z| with hΦ
  -- Rewrite the target `𝓝 0` as `𝓝 (∫ z, (0 : ℝ) ∂ν)` so DCT's limit form matches.
  have hzero : (0 : ℝ) = ∫ _ : LinfF F, (0 : ℝ) ∂ν := by simp
  rw [hzero]
  -- DCT: dominator `2‖f‖`, measurable integrands, a.e. pointwise convergence to `0`.
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun _ => 2 * ‖f‖)
  · -- Each `Φ m` is `AEStronglyMeasurable`: `f ∘ πₘ` (continuous ∘ measurable) and
    -- `f` (continuous) are measurable, so their difference's absolute value is.
    intro m
    have h1 : Measurable (fun z : LinfF F => f (finiteNetProj hG_env hG hF_meas hF_ent m z)) :=
      f.continuous.measurable.comp (measurable_finiteNetProj hG_env hG hF_meas hF_ent m)
    have h2 : Measurable (fun z : LinfF F => f z) := f.continuous.measurable
    exact ((h1.sub h2).abs).aestronglyMeasurable
  · -- The constant dominator `2‖f‖` is integrable (finite measure × constant).
    exact integrable_const _
  · -- Pointwise bound `|Φ m z| ≤ 2‖f‖`: each `|f w| ≤ ‖f‖`.
    intro m
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    have hb1 : |f (finiteNetProj hG_env hG hF_meas hF_ent m z)| ≤ ‖f‖ := by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
    have hb2 : |f z| ≤ ‖f‖ := by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
    calc |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z|
          ≤ |f (finiteNetProj hG_env hG hF_meas hF_ent m z)| + |f z| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add hb1 hb2
        _ = 2 * ‖f‖ := by ring
  · -- A.e. pointwise convergence `Φ m z → 0`: for a UC path `z`,
    -- `πₘ z → z` (`tendsto_finiteNetProj_of_ucPath`), so `f (πₘ z) → f z`
    -- (continuity of `f`), so `|f (πₘ z) − f z| → 0`.
    filter_upwards [hucp] with z hz
    have htproj : Tendsto (fun m => finiteNetProj hG_env hG hF_meas hF_ent m z) atTop (𝓝 z) :=
      tendsto_finiteNetProj_of_ucPath hG_env hG hF_meas hF_ent z hz
    have hf_tendsto : Tendsto (fun m => f (finiteNetProj hG_env hG hF_meas hF_ent m z))
        atTop (𝓝 (f z)) :=
      (f.continuous.tendsto z).comp htproj
    -- `|f (πₘ z) − f z| → |f z − f z| = 0`.
    have hsub : Tendsto (fun m => f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z)
        atTop (𝓝 (0 : ℝ)) := by
      have := hf_tendsto.sub (tendsto_const_nhds (x := f z))
      simpa using this
    have := (continuous_abs.tendsto (0 : ℝ)).comp hsub
    simpa [Φ] using! this

/-! ### The ε/3 argument

The ε/3 readout split (vdV p.261) uses two generic outer-expectation lemmas,
`outerReadout_le_of_modulus` and `abs_outerReadout_diff_le`, together with the
combiner `tendsto_outerReadout_of_pieces`. -/

omit [IsProbabilityMeasure P] hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne in
/-- **One-sided readout majorant (real form).** For probability `μ`, a
bounded continuous readout `f`, two maps `X Y : Ξ → D`, a net scale `δ` and a
continuity modulus `η ≥ 0` with `f (X ξ) ≤ f (Y ξ) + η` on the *good* event
`{dist (X ξ) (Y ξ) ≤ δ}`, the shifted outer readout of `f ∘ X` is bounded by the
readout of `f ∘ Y` plus `η` plus `2‖f‖ · (outer measure of the bad event)`.

This is the real-valued `.toReal` packaging of `outerExpectation_readout_triangle`:
the error is `η + 2‖f‖ · 1_{δ < dist}`, with `Lip = 1`; finiteness of
both readouts (each `≤ 2‖f‖ · μ univ < ⊤`) lets `.toReal` distribute. -/
theorem outerReadout_le_of_modulus {Ξ D : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace D] [PseudoMetricSpace D] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (f : D →ᵇ ℝ) (X Y : Ξ → D) {δ η : ℝ} (hη : 0 ≤ η)
    (hmod : ∀ ξ, dist (X ξ) (Y ξ) ≤ δ → f (X ξ) ≤ f (Y ξ) + η) :
    (outerExpectation μ (fun ξ => ENNReal.ofReal (f (X ξ) + ‖f‖))).toReal
      ≤ (outerExpectation μ (fun ξ => ENNReal.ofReal (f (Y ξ) + ‖f‖))).toReal
        + η + 2 * ‖f‖ *
          (outerExpectation μ
            ({ξ | δ < dist (X ξ) (Y ξ)}.indicator (fun _ => (1 : ℝ≥0∞)))).toReal := by
  classical
  set badSet : Set Ξ := {ξ | δ < dist (X ξ) (Y ξ)} with hbadSet
  set ind : Ξ → ℝ≥0∞ := badSet.indicator (fun _ => (1 : ℝ≥0∞)) with hind
  set EX := outerExpectation μ (fun ξ => ENNReal.ofReal (f (X ξ) + ‖f‖)) with hEX
  set EY := outerExpectation μ (fun ξ => ENNReal.ofReal (f (Y ξ) + ‖f‖)) with hEY
  set I := outerExpectation μ ind with hI
  -- `0 ≤ ‖f‖` and the pointwise `±‖f‖` bounds on `f`.
  have hnorm : (0 : ℝ) ≤ ‖f‖ := norm_nonneg _
  -- The error term is `err = η + 2‖f‖ · 1_bad`.
  set err : Ξ → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * ind ξ with herr
  -- Pointwise majorant `hmaj`.
  have hmaj : ∀ ξ, ENNReal.ofReal (f (X ξ) + ‖f‖)
      ≤ ENNReal.ofReal (f (Y ξ) + ‖f‖) + ENNReal.ofReal 1 * err ξ := by
    intro ξ
    rw [ENNReal.ofReal_one, one_mul, herr]
    -- Reduce to a real inequality `f(Xξ)+‖f‖ ≤ (f(Yξ)+‖f‖) + (η + 2‖f‖·1_bad)`.
    have hYnn : (0 : ℝ) ≤ f (Y ξ) + ‖f‖ := by
      have := (abs_le.1 (f.norm_coe_le_norm (Y ξ))).1; linarith
    have hreal : f (X ξ) + ‖f‖
        ≤ (f (Y ξ) + ‖f‖) + (η + 2 * ‖f‖ * (ind ξ).toReal) := by
      by_cases hg : dist (X ξ) (Y ξ) ≤ δ
      · -- Good event: `ind = 0`, use the modulus bound.
        have hind0 : ind ξ = 0 := by
          rw [hind, Set.indicator_of_notMem]
          rw [hbadSet]; simp only [Set.mem_setOf_eq, not_lt]; exact hg
        rw [hind0]; simp only [ENNReal.toReal_zero, mul_zero, add_zero]
        have := hmod ξ hg; linarith
      · -- Bad event: `ind = 1`, slack `≥ 2‖f‖ ≥ f(Xξ) − f(Yξ)`.
        have hind1 : ind ξ = 1 := by
          rw [hind, Set.indicator_of_mem]
          rw [hbadSet]; simp only [Set.mem_setOf_eq]; exact lt_of_not_ge hg
        rw [hind1]; simp only [ENNReal.toReal_one, mul_one]
        have hfX := (abs_le.1 (f.norm_coe_le_norm (X ξ))).2
        have hfY := (abs_le.1 (f.norm_coe_le_norm (Y ξ))).1
        linarith
    -- Lift the real inequality through `ENNReal.ofReal`.
    calc ENNReal.ofReal (f (X ξ) + ‖f‖)
        ≤ ENNReal.ofReal ((f (Y ξ) + ‖f‖) + (η + 2 * ‖f‖ * (ind ξ).toReal)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (f (Y ξ) + ‖f‖)
            + (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * ind ξ) := by
          have hind_ne : ind ξ ≠ ⊤ := by
            rw [hind]; exact ne_top_of_le_ne_top ENNReal.one_ne_top
              (Set.indicator_le_self _ _ ξ)
          rw [ENNReal.ofReal_add hYnn (by positivity),
            ENNReal.ofReal_add hη (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_toReal hind_ne]
  -- Apply `outerExpectation_readout_triangle` at `Lip = 1`.
  have hS5 := outerExpectation_readout_triangle μ f X Y 1 err hmaj
  rw [ENNReal.ofReal_one, one_mul] at hS5
  -- `E*[err] ≤ ofReal η + ofReal(2‖f‖)·I`.
  have hEerr : outerExpectation μ err
      ≤ ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * I := by
    have hsplit : outerExpectation μ err
        ≤ outerExpectation μ (fun _ => ENNReal.ofReal η)
          + outerExpectation μ (fun ξ => ENNReal.ofReal (2 * ‖f‖) * ind ξ) := by
      have := outerExpectation_add_le (μ := μ) (fun _ => ENNReal.ofReal η)
        (fun ξ => ENNReal.ofReal (2 * ‖f‖) * ind ξ)
      simpa [herr, Pi.add_apply] using! this
    have hconst : outerExpectation μ (fun _ => ENNReal.ofReal η)
        = ENNReal.ofReal η := by rw [outerExpectation_const]; simp
    have hsmul : outerExpectation μ (fun ξ => ENNReal.ofReal (2 * ‖f‖) * ind ξ)
        = ENNReal.ofReal (2 * ‖f‖) * I := by
      have : (fun ξ => ENNReal.ofReal (2 * ‖f‖) * ind ξ)
          = (ENNReal.ofReal (2 * ‖f‖)) • ind := by
        funext ξ; simp [Pi.smul_apply, smul_eq_mul]
      rw [this, outerExpectation_const_smul _ ENNReal.ofReal_ne_top, smul_eq_mul, hI]
    rw [hconst, hsmul] at hsplit; exact hsplit
  -- Chain: `EX ≤ EY + ofReal η + ofReal(2‖f‖)·I`.
  have hchain : EX ≤ EY + (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * I) := by
    calc EX ≤ EY + outerExpectation μ err := hS5
      _ ≤ EY + (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * I) :=
          add_le_add (le_refl EY) hEerr
  -- Finiteness of all terms (each readout `≤ ofReal(2‖f‖)`, `I ≤ 1`).
  have hI_le : I ≤ 1 := by
    rw [hI]
    calc outerExpectation μ ind ≤ outerExpectation μ (fun _ => (1 : ℝ≥0∞)) :=
          outerExpectation_mono (fun ξ => Set.indicator_le_self _ _ ξ)
      _ = 1 := by rw [outerExpectation_const]; simp
  have hI_top : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hI_le
  have hEY_le : EY ≤ ENNReal.ofReal (2 * ‖f‖) := by
    rw [hEY]
    calc outerExpectation μ (fun ξ => ENNReal.ofReal (f (Y ξ) + ‖f‖))
        ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) := by
          refine outerExpectation_mono (fun ξ => ENNReal.ofReal_le_ofReal ?_)
          have := (abs_le.1 (f.norm_coe_le_norm (Y ξ))).2; linarith
      _ = ENNReal.ofReal (2 * ‖f‖) := by rw [outerExpectation_const]; simp
  have hEY_top : EY ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEY_le
  have hRHS_top : EY + (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * I) ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨hEY_top, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ?_⟩⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top
  -- Convert the ENNReal bound to `.toReal`.
  have := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hRHS_top hchain) hRHS_top).2
    hchain
  rw [ENNReal.toReal_add hEY_top (by
        exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top⟩),
    ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hη,
    ENNReal.toReal_ofReal (by positivity)] at this
  calc EX.toReal
      ≤ EY.toReal + (η + 2 * ‖f‖ * I.toReal) := this
    _ = EY.toReal + η + 2 * ‖f‖ * I.toReal := by ring

omit [IsProbabilityMeasure P] hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne in
/-- **Two-sided readout difference bound.** The absolute readout difference is
controlled by the modulus `η` plus the `2‖f‖`-scaled bad-event outer measure,
applying `outerReadout_le_of_modulus` in both directions (the bad event
`{δ < dist (X ξ) (Y ξ)}` is symmetric in `X, Y`). -/
theorem abs_outerReadout_diff_le {Ξ D : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace D] [PseudoMetricSpace D] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (f : D →ᵇ ℝ) (X Y : Ξ → D) {δ η : ℝ} (hη : 0 ≤ η)
    (hmodXY : ∀ ξ, dist (X ξ) (Y ξ) ≤ δ → f (X ξ) ≤ f (Y ξ) + η)
    (hmodYX : ∀ ξ, dist (X ξ) (Y ξ) ≤ δ → f (Y ξ) ≤ f (X ξ) + η) :
    |(outerExpectation μ (fun ξ => ENNReal.ofReal (f (X ξ) + ‖f‖))).toReal
        - (outerExpectation μ (fun ξ => ENNReal.ofReal (f (Y ξ) + ‖f‖))).toReal|
      ≤ η + 2 * ‖f‖ *
          (outerExpectation μ
            ({ξ | δ < dist (X ξ) (Y ξ)}.indicator (fun _ => (1 : ℝ≥0∞)))).toReal := by
  -- The bad event is symmetric in `X, Y` (`dist_comm`).
  have hsymm : {ξ | δ < dist (Y ξ) (X ξ)} = {ξ | δ < dist (X ξ) (Y ξ)} := by
    ext ξ; simp only [Set.mem_setOf_eq, dist_comm]
  rw [abs_sub_le_iff]
  constructor
  · -- `EX.toReal − EY.toReal ≤ η + 2‖f‖·I.toReal`.
    have := outerReadout_le_of_modulus μ f X Y hη hmodXY
    linarith
  · -- `EY.toReal − EX.toReal ≤ η + 2‖f‖·I.toReal` (swap roles; same `I` by `dist_comm`).
    have hmodYX' : ∀ ξ, dist (Y ξ) (X ξ) ≤ δ → f (Y ξ) ≤ f (X ξ) + η := by
      intro ξ hd; exact hmodYX ξ (by rw [dist_comm] at hd; exact hd)
    have := outerReadout_le_of_modulus μ f Y X hη hmodYX'
    rw [hsymm] at this
    linarith

omit [IsProbabilityMeasure P] hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne in
/-- **Unconditional readout-difference bound via the absolute-value tail.** With no
modulus hypothesis at all, the absolute `.toReal`-readout difference of `f ∘ X` and
`f ∘ Y` is controlled by the `E*`-readout of the *pointwise* gap
`|f (X ξ) − f (Y ξ)|`:

`|EX.toReal − EY.toReal| ≤ (E*[ ofReal |f∘X − f∘Y| ]).toReal`.

This is the `η = 0` / no-bad-event specialisation of `abs_outerReadout_diff_le`:
applying `outerExpectation_readout_triangle` at `Lip = 1` with
`err ξ = ofReal |f (X ξ) − f (Y ξ)|` in both directions (the pointwise majorant
`f (X ξ) + ‖f‖ ≤ (f (Y ξ) + ‖f‖) + |f (X ξ) − f (Y ξ)|` holds since
`f (X ξ) − f (Y ξ) ≤ |f (X ξ) − f (Y ξ)|`). Finiteness of all readouts
(each `≤ ofReal (2‖f‖)` since `μ` is a probability measure) lets `.toReal`
distribute. The `‖f‖ · (μ univ).toReal` shift terms cancel in the difference, so
this lemma is exactly the per-`(m,n)` `hdiff` hypothesis of the combiner. -/
theorem abs_outerReadout_diff_le_readout_abs {Ξ D : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace D] [PseudoMetricSpace D] (μ : Measure Ξ)
    [IsProbabilityMeasure μ] (f : D →ᵇ ℝ) (X Y : Ξ → D) :
    |(outerExpectation μ (fun ξ => ENNReal.ofReal (f (X ξ) + ‖f‖))).toReal
        - (outerExpectation μ (fun ξ => ENNReal.ofReal (f (Y ξ) + ‖f‖))).toReal|
      ≤ (outerExpectation μ
          (fun ξ => ENNReal.ofReal |f (X ξ) - f (Y ξ)|)).toReal := by
  classical
  set EX := outerExpectation μ (fun ξ => ENNReal.ofReal (f (X ξ) + ‖f‖)) with hEX
  set EY := outerExpectation μ (fun ξ => ENNReal.ofReal (f (Y ξ) + ‖f‖)) with hEY
  set E := outerExpectation μ (fun ξ => ENNReal.ofReal |f (X ξ) - f (Y ξ)|) with hE
  -- Finiteness of all three readouts: each integrand `≤ ofReal (2‖f‖)`, and
  -- `E*[const c] = c * μ univ = c` for a probability measure.
  have hnorm : (0 : ℝ) ≤ ‖f‖ := norm_nonneg _
  have hbound : ∀ (Z : Ξ → D), outerExpectation μ
      (fun ξ => ENNReal.ofReal (f (Z ξ) + ‖f‖)) ≤ ENNReal.ofReal (2 * ‖f‖) := by
    intro Z
    calc outerExpectation μ (fun ξ => ENNReal.ofReal (f (Z ξ) + ‖f‖))
        ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) := by
          refine outerExpectation_mono (fun ξ => ENNReal.ofReal_le_ofReal ?_)
          have := (abs_le.1 (f.norm_coe_le_norm (Z ξ))).2; linarith
      _ = ENNReal.ofReal (2 * ‖f‖) := by rw [outerExpectation_const]; simp
  have hEX_top : EX ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound X)
  have hEY_top : EY ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound Y)
  -- The two one-sided readouts at `Lip = 1`, with
  -- `err ξ = ofReal |f(Xξ) − f(Yξ)|`.
  set err : Ξ → ℝ≥0∞ := fun ξ => ENNReal.ofReal |f (X ξ) - f (Y ξ)| with herr
  -- One-sided majorant, used in both directions (`err` is symmetric in `X, Y`).
  have hmaj : ∀ (Z W : Ξ → D),
      (∀ ξ, ENNReal.ofReal (f (Z ξ) + ‖f‖)
        ≤ ENNReal.ofReal (f (W ξ) + ‖f‖) + ENNReal.ofReal 1
            * ENNReal.ofReal |f (Z ξ) - f (W ξ)|) := by
    intro Z W ξ
    rw [ENNReal.ofReal_one, one_mul]
    have hWnn : (0 : ℝ) ≤ f (W ξ) + ‖f‖ := by
      have := (abs_le.1 (f.norm_coe_le_norm (W ξ))).1; linarith
    rw [← ENNReal.ofReal_add hWnn (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (by
      have := le_abs_self (f (Z ξ) - f (W ξ)); linarith)
  -- `EX ≤ EY + E` (forward) and `EY ≤ EX + E'` with `E' = E` by `|·|`-symmetry.
  have hfwd := outerExpectation_readout_triangle μ f X Y 1 err (hmaj X Y)
  rw [ENNReal.ofReal_one, one_mul] at hfwd
  have hbwd := outerExpectation_readout_triangle μ f Y X 1
    (fun ξ => ENNReal.ofReal |f (Y ξ) - f (X ξ)|) (hmaj Y X)
  rw [ENNReal.ofReal_one, one_mul] at hbwd
  -- The two `err`s coincide via `|a − b| = |b − a|`.
  have hErr_symm : outerExpectation μ (fun ξ => ENNReal.ofReal |f (Y ξ) - f (X ξ)|)
      = E := by
    rw [hE]; congr 1; funext ξ; rw [abs_sub_comm]
  rw [hErr_symm] at hbwd
  -- Finiteness of `E` too (`|f∘X − f∘Y| ≤ 2‖f‖`).
  have hE_le : E ≤ ENNReal.ofReal (2 * ‖f‖) := by
    rw [hE]
    calc outerExpectation μ (fun ξ => ENNReal.ofReal |f (X ξ) - f (Y ξ)|)
        ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) := by
          refine outerExpectation_mono (fun ξ => ENNReal.ofReal_le_ofReal ?_)
          have hfX := abs_le.1 (f.norm_coe_le_norm (X ξ))
          have hfY := abs_le.1 (f.norm_coe_le_norm (Y ξ))
          rw [abs_le]; constructor <;> [linarith [hfX.1, hfY.2]; linarith [hfX.2, hfY.1]]
      _ = ENNReal.ofReal (2 * ‖f‖) := by rw [outerExpectation_const]; simp
  have hE_top : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE_le
  -- Convert both ENNReal bounds to `.toReal` and conclude via `abs_sub_le_iff`.
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have := (ENNReal.toReal_le_toReal hEX_top
      (ENNReal.add_ne_top.2 ⟨hEY_top, hE_top⟩)).2 hfwd
    rw [ENNReal.toReal_add hEY_top hE_top] at this; linarith
  · have := (ENNReal.toReal_le_toReal hEY_top
      (ENNReal.add_ne_top.2 ⟨hEX_top, hE_top⟩)).2 hbwd
    rw [ENNReal.toReal_add hEX_top hE_top] at this; linarith

omit [IsProbabilityMeasure P] hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne in
/-- **Per-`f` ε/3 combiner.** Given a readout sequence `R`, a limit `L`,
a projected readout `Rproj : ℕ → ℕ → ℝ` (in `m` then `n`), projected limits
`Lproj : ℕ → ℝ`, and a per-`(m,n)` discretization-tail family `Dtail : ℕ → ℕ → ℝ`,
with
* (middle) for every `m`, `Rproj m n → Lproj m` as `n→∞`;
* (limit tail) `Lproj m → L` as `m→∞`;
* (readout diff) the unconditional per-`(m,n)` bound `|R n − Rproj m n| ≤ Dtail m n`;
* (tail vanishing) `limsupₙ (Dtail m n) → 0` as `m→∞`,
the unprojected readout `R n → L` as `n→∞`. The hypothesis `hDtail` packages
the vanishing discretization tail; `empirical_readout_tail_outer` establishes it
for empirical-process readouts.

`hDbdd` ensures that `limsup (Dtail m) atTop` has its usual finite-order
behavior over `ℝ`; for empirical-process readouts the bound
`Dtail m n = (E*[…]).toReal ≤ 2‖f‖` supplies this condition. -/
theorem tendsto_outerReadout_of_pieces
    (R : ℕ → ℝ) (Rproj : ℕ → ℕ → ℝ) (Lproj : ℕ → ℝ) (L : ℝ)
    (Dtail : ℕ → ℕ → ℝ)
    (hmiddle : ∀ m, Tendsto (fun n => Rproj m n) atTop (𝓝 (Lproj m)))
    (hlimtail : Tendsto Lproj atTop (𝓝 L))
    (hdiff : ∀ m n, |R n - Rproj m n| ≤ Dtail m n)
    (hDtail : Tendsto (fun m => limsup (fun n => Dtail m n) atTop) atTop (𝓝 0))
    (hDbdd : ∀ m, IsBoundedUnder (· ≤ ·) atTop (Dtail m)) :
    Tendsto R atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Pick `m` large: tail limsup `< ε/3` AND `|Lproj m − L| < ε/3`.
  have h1 : ∀ᶠ m in atTop, limsup (fun n => Dtail m n) atTop < ε / 3 := by
    have := (Metric.tendsto_atTop.1 hDtail) (ε / 3) (by positivity)
    obtain ⟨M, hM⟩ := this
    refine Filter.eventually_atTop.2 ⟨M, fun m hm => ?_⟩
    have := hM m hm
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have h2 : ∀ᶠ m in atTop, |Lproj m - L| < ε / 3 := by
    have := (Metric.tendsto_atTop.1 hlimtail) (ε / 3) (by positivity)
    obtain ⟨M, hM⟩ := this
    refine Filter.eventually_atTop.2 ⟨M, fun m hm => ?_⟩
    rw [← Real.dist_eq]; exact hM m hm
  -- A single `m` satisfying both.
  obtain ⟨m, hm_tail, hm_lim⟩ := (h1.and h2).exists
  -- For this `m`: `Dtail m n < ε/3` eventually in `n` (`eventually_lt_of_limsup_lt`).
  have hdtail_n : ∀ᶠ n in atTop, Dtail m n < ε / 3 :=
    Filter.eventually_lt_of_limsup_lt hm_tail (hDbdd m)
  -- And the middle term `|Rproj m n − Lproj m| < ε/3` eventually in `n`.
  have hmid_n : ∀ᶠ n in atTop, |Rproj m n - Lproj m| < ε / 3 := by
    have := (Metric.tendsto_atTop.1 (hmiddle m)) (ε / 3) (by positivity)
    obtain ⟨N, hN⟩ := this
    refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    rw [← Real.dist_eq]; exact hN n hn
  -- Combine the two eventual-in-`n` facts into a single threshold `N`.
  obtain ⟨N, hN⟩ := (hdtail_n.and hmid_n).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hdtailn, hmidn⟩ := hN n hn
  -- `|R n − Rproj m n| ≤ Dtail m n < ε/3`.
  have hdiffn : |R n - Rproj m n| ≤ Dtail m n := hdiff m n
  -- Triangle: `|R n − L| ≤ |R n − Rproj m n| + |Rproj m n − Lproj m| + |Lproj m − L|`.
  rw [Real.dist_eq]
  have htri : |R n - L|
      ≤ |R n - Rproj m n| + |Rproj m n - Lproj m| + |Lproj m - L| := by
    linarith [abs_sub_le (R n) (Rproj m n) L, abs_sub_le (Rproj m n) (Lproj m) L]
  -- tail `< ε/3`, middle `< ε/3`, limtail `< ε/3` ⇒ sum `< ε`.
  linarith [htri, hdiffn, hdtailn, hmidn, hm_lim]

include hG_env hG hF_meas hF_ent in
/-- **Empirical readout-tail vanishing.** For a
*bounded-Lipschitz* `f : LinfF F →ᵇ ℝ`, the `n`-`limsup` of the pointwise-gap
`E*`-readout `E*[ |f(𝔾ₙ) − f(πₘ𝔾ₙ)| ]` tends to `0` as `m → ∞`.

This is van der Vaart's own readout-difference bound (book p.261-262), which does
*not* build an asymptotically-tight compact set for the empirical process. For a
`K`-Lipschitz `f`, split at the fixed oscillation threshold `ε`:
`|f(𝔾ₙ) − f(πₘ𝔾ₙ)| ≤ K·ε + 2‖f‖·𝟙{ε < ‖𝔾ₙ − πₘ𝔾ₙ‖}`, so the readout obeys
`Dtail m n ≤ K·ε + 2‖f‖·P*{ε < ‖𝔾ₙ − πₘ𝔾ₙ‖}`. The second factor's `limsupₙ`
vanishes as `m → ∞` by `empirical_proj_error_outer`, leaving
`limsupₘ limsupₙ Dtail ≤ K·ε`. Since `ε > 0` is arbitrary, the tail tends to `0`.

The Lipschitz hypothesis is essential: a merely bounded-*continuous* `f` on the
non-compact `ℓ∞(F)` has no global modulus, so this bound fails for it. The upgrade
to all bounded-continuous test functions happens at the headline theorem via the
inf-convolution portmanteau `weakConvergesOuter_of_lipschitz_readout`.

vdV p.261-262 (⟸): the readout-difference step for bounded-Lipschitz test
functions, controlled by empirical equicontinuity alone. -/
theorem empirical_readout_tail_outer
    (h_eq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (f : LinfF F →ᵇ ℝ)
    (hf_lip : ∃ K, LipschitzWith K f) :
    Tendsto (fun m => limsup (fun n =>
        (outerExpectation μ (fun ξ => ENNReal.ofReal
          |f (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (memℓp_empiricalProcess
                ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ)))
           - f (finiteNetProj hG_env hG hF_meas hF_ent m
                (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (memℓp_empiricalProcess
                  ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                  (fun i : Fin n => X i.val ξ))))|)).toReal) atTop)
      atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := hf_lip
  -- Abbreviate the empirical process and its `2⁻ᵐ`-net projection.
  set 𝔾 : ∀ (n : ℕ) (ξ : Ξ), LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ)) with h𝔾
  -- The per-`(m, n)` discretization-tail readout.
  set Dtail : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)).toReal
    with hDtail
  -- Goal restated in terms of `Dtail`.
  change Tendsto (fun m => limsup (fun n => Dtail m n) atTop) atTop (𝓝 0)
  -- It suffices to prove the `ε/0`-squeeze: `limsupₘ limsupₙ Dtail ≤ K·ε` for every
  -- fixed oscillation threshold `ε > 0`, with `0 ≤ Dtail`. Send `ε → 0`.
  -- We package this as: the `m`-limsup of `Dtail m ·` is dominated, for each fixed `ε`,
  -- by `K·ε + 2‖f‖·limsupₙ P*{ε < ‖𝔾ₙ − πₘ𝔾ₙ‖}`, whose `m`-limit is `K·ε`.
  -- Reduce to `Tendsto … (𝓝 0)` via the `Metric` ε-bound: prove the
  -- limsup function is eventually `< ε'` (in norm) for every `ε' > 0`.
  refine NormedAddGroup.tendsto_nhds_zero.2 (fun ε' hε' => ?_)
  -- Choose the fixed oscillation threshold `ε := (ε'/2) / (K + 1)` so that `K·ε < ε'/2`.
  set Kr : ℝ := (K : ℝ) with hKr
  have hKr_nonneg : 0 ≤ Kr := by positivity
  -- A fixed positive threshold; `ε` below.
  obtain ⟨ε, hε_pos, hKε⟩ : ∃ ε : ℝ, 0 < ε ∧ Kr * ε < ε' / 2 := by
    refine ⟨(ε' / 2) / (Kr + 1), by positivity, ?_⟩
    rw [mul_div_assoc']
    rw [div_lt_iff₀ (by positivity)]
    have : Kr * (ε' / 2) ≤ (Kr + 1) * (ε' / 2) := by nlinarith
    nlinarith [hε']
  -- Apply `empirical_proj_error_outer` at oscillation `ε`: the `n`-limsup of the
  -- outer-prob mass `P*{ε < ‖𝔾ₙ − πₘ𝔾ₙ‖}` tends to `0` in `m`.
  have hS3 := empirical_proj_error_outer (F := F) (P := P) (G := G) hG_env hG hF_meas hF_ent
    h_eq μ X hX_meas hX_indep hX_id hX_law ε hε_pos
  -- Abbreviate the outer probability as `Pstar m n : ℝ≥0∞`.
  set Pstar : ℕ → ℕ → ℝ≥0∞ := fun m n =>
    μ.outerMeasureStar
      {ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖} with hPstar
  -- The preceding convergence in `Pstar` form.
  have hS3' : Tendsto (fun m => limsup (fun n => Pstar m n) atTop) atTop (𝓝 0) := by
    refine hS3.congr (fun m => ?_)
    rfl
  -- `Pstar m n ≤ 1` (probability outer measure), so the `n`-limsup is finite.
  have hPstar_le_one : ∀ m n, Pstar m n ≤ 1 := by
    intro m n
    simp only [hPstar, Measure.outerMeasureStar]
    calc outerExpectation μ (Set.indicator _ 1)
        ≤ outerExpectation μ (fun _ => (1 : ℝ≥0∞)) := by
          refine outerExpectation_mono (fun ξ => ?_)
          rw [Set.indicator_apply]
          split_ifs <;> simp
      _ = 1 := by rw [outerExpectation_const, measure_univ, mul_one]
  -- **The per-`(m, n)` pointwise readout bound.**
  -- `|f(𝔾ₙ) − f(πₘ𝔾ₙ)| ≤ K·ε + 2‖f‖·𝟙{ε < ‖𝔾ₙ − πₘ𝔾ₙ‖}`, hence
  -- `Dtail m n ≤ K·ε + 2‖f‖·(Pstar m n).toReal`.
  have hDtail_bound : ∀ m n,
      Dtail m n ≤ Kr * ε + 2 * ‖f‖ * (Pstar m n).toReal := by
    intro m n
    -- Pointwise ℝ≥0∞ bound on the integrand.
    have hpt : ∀ ξ, ENNReal.ofReal
        |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|
        ≤ ENNReal.ofReal (Kr * ε)
          + ENNReal.ofReal (2 * ‖f‖) *
            ({ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}.indicator
              (1 : Ξ → ℝ≥0∞) ξ) := by
      intro ξ
      set a := 𝔾 n ξ with ha
      set b := finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ) with hb
      -- Lipschitz: `|f a − f b| ≤ K·‖a − b‖`, and `|f a − f b| ≤ 2‖f‖`.
      have hlip_bd : |f a - f b| ≤ Kr * ‖a - b‖ := by
        have := hK.dist_le_mul a b
        rwa [Real.dist_eq, dist_eq_norm] at this
      have h2f : |f a - f b| ≤ 2 * ‖f‖ := by
        have hfa := abs_le.1 (f.norm_coe_le_norm a)
        have hfb := abs_le.1 (f.norm_coe_le_norm b)
        rw [abs_le]; constructor <;> [linarith [hfa.1, hfb.2]; linarith [hfa.2, hfb.1]]
      by_cases hcase : ε < ‖a - b‖
      · -- On the bad event: indicator = 1, bound by the `2‖f‖` term.
        have hmem : ξ ∈ {ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖} := by
          rw [Set.mem_setOf_eq, ← ha, ← hb]; exact hcase
        rw [Set.indicator_of_mem hmem]
        calc ENNReal.ofReal |f a - f b| ≤ ENNReal.ofReal (2 * ‖f‖) :=
              ENNReal.ofReal_le_ofReal h2f
          _ ≤ ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * 1 := by
              rw [mul_one]; exact le_add_self
      · -- On the good event: `‖a − b‖ ≤ ε`, so `|f a − f b| ≤ K·ε`.
        rw [not_lt] at hcase
        have hgood : |f a - f b| ≤ Kr * ε :=
          le_trans hlip_bd (mul_le_mul_of_nonneg_left hcase hKr_nonneg)
        calc ENNReal.ofReal |f a - f b| ≤ ENNReal.ofReal (Kr * ε) :=
              ENNReal.ofReal_le_ofReal hgood
          _ ≤ ENNReal.ofReal (Kr * ε)
              + ENNReal.ofReal (2 * ‖f‖) *
                ({ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}.indicator
                  (1 : Ξ → ℝ≥0∞) ξ) := le_self_add
    -- Lift the pointwise bound through `E*` (mono + subadditivity + const + const_smul).
    have hE : outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)
        ≤ ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * Pstar m n := by
      calc outerExpectation μ (fun ξ => ENNReal.ofReal
            |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)
          ≤ outerExpectation μ (fun ξ => ENNReal.ofReal (Kr * ε)
              + ENNReal.ofReal (2 * ‖f‖) *
                ({ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}.indicator
                  (1 : Ξ → ℝ≥0∞) ξ)) := outerExpectation_mono hpt
        _ ≤ outerExpectation μ (fun _ => ENNReal.ofReal (Kr * ε))
            + outerExpectation μ (fun ξ => ENNReal.ofReal (2 * ‖f‖) *
                ({ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}.indicator
                  (1 : Ξ → ℝ≥0∞) ξ)) := outerExpectation_add_le _ _
        _ = ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * Pstar m n := by
            rw [outerExpectation_const, measure_univ, mul_one]
            congr 1
            -- `E*[c · 𝟙_A] = c · E*[𝟙_A] = c · P*(A)`, with `c = ofReal(2‖f‖)`.
            have hcs : outerExpectation μ
                (fun ξ => ENNReal.ofReal (2 * ‖f‖) *
                  ({ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}.indicator
                    (1 : Ξ → ℝ≥0∞) ξ))
                = ENNReal.ofReal (2 * ‖f‖) * outerExpectation μ
                    ({ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}.indicator
                      (1 : Ξ → ℝ≥0∞)) := by
              have := outerExpectation_const_smul (μ := μ) (ENNReal.ofReal (2 * ‖f‖))
                ENNReal.ofReal_ne_top
                ({ξ | ε < ‖𝔾 n ξ - finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)‖}.indicator
                  (1 : Ξ → ℝ≥0∞))
              simpa only [Pi.smul_apply, smul_eq_mul] using! this
            rw [hcs, hPstar]
            rfl
    -- Take `.toReal` (everything finite: `ofReal`, `Pstar ≤ 1`).
    rw [hDtail]
    have hfin : ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * Pstar m n ≠ ⊤ := by
      apply ENNReal.add_ne_top.2
      refine ⟨ENNReal.ofReal_ne_top, ?_⟩
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top (by norm_num) (hPstar_le_one m n))
    calc (outerExpectation μ (fun ξ => ENNReal.ofReal
          |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)).toReal
        ≤ (ENNReal.ofReal (Kr * ε) + ENNReal.ofReal (2 * ‖f‖) * Pstar m n).toReal :=
          ENNReal.toReal_mono hfin hE
      _ = Kr * ε + 2 * ‖f‖ * (Pstar m n).toReal := by
          rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
              (ne_top_of_le_ne_top (by norm_num) (hPstar_le_one m n))),
            ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofReal (by positivity)]
  -- The affine envelope `φ x = K·ε + 2‖f‖·x` (monotone, continuous): `Dtail m n ≤ φ (S m n)`.
  -- `Dtail` is nonnegative (`.toReal` of an `ℝ≥0∞`).
  have hDtail_nonneg : ∀ m n, 0 ≤ Dtail m n := fun m n => by
    rw [hDtail]; exact ENNReal.toReal_nonneg
  set φ : ℝ → ℝ := fun x => Kr * ε + 2 * ‖f‖ * x with hφ
  have hf_nonneg : (0 : ℝ) ≤ 2 * ‖f‖ := by positivity
  have hφ_mono : Monotone φ := by
    intro x y hxy
    simp only [hφ]
    gcongr
  have hφ_cont : Continuous φ := by
    simp only [hφ]; fun_prop
  -- The per-`n` upper bound `Pstar.toReal ≤ 1`.
  have hStoReal_le : ∀ m n, (Pstar m n).toReal ≤ 1 := fun m n =>
    ENNReal.toReal_le_of_le_ofReal (by norm_num)
      (by rw [ENNReal.ofReal_one]; exact hPstar_le_one m n)
  -- `(Pstar m ·).toReal` is bounded above (by `1`) and cobounded (nonneg).
  have hS_bdd : ∀ m, IsBoundedUnder (· ≤ ·) atTop (fun n => (Pstar m n).toReal) :=
    fun m => ⟨1, by
      rw [eventually_map]
      exact Eventually.of_forall (fun n => hStoReal_le m n)⟩
  have hS_cobdd : ∀ m, IsCoboundedUnder (· ≤ ·) atTop (fun n => (Pstar m n).toReal) :=
    fun m => Filter.isCoboundedUnder_le_of_le atTop (x := 0)
      (fun n => ENNReal.toReal_nonneg)
  -- `Dtail m ·` is bounded above (by `φ 1`) and cobounded (nonneg).
  have hDtail_bdd : ∀ m, IsBoundedUnder (· ≤ ·) atTop (fun n => Dtail m n) :=
    fun m => ⟨φ 1, by
      rw [eventually_map]
      refine Eventually.of_forall (fun n => le_trans (hDtail_bound m n) ?_)
      simp only [hφ]
      gcongr
      exact hStoReal_le m n⟩
  have hDtail_cobdd : ∀ m, IsCoboundedUnder (· ≤ ·) atTop (fun n => Dtail m n) :=
    fun m => Filter.isCoboundedUnder_le_of_le atTop (x := 0) (fun n => hDtail_nonneg m n)
  -- **Bound the `n`-limsup of `Dtail m ·` by `φ ((limsupₙ Pstar m ·).toReal)`.**
  have hlimsup_bound : ∀ m,
      limsup (fun n => Dtail m n) atTop
        ≤ φ ((limsup (fun n => Pstar m n) atTop).toReal) := by
    intro m
    -- `(limsupₙ Pstar).toReal = limsupₙ (Pstar.toReal)` (`ENNReal.limsup_toReal_eq`).
    have hPtoReal : limsup (fun n => (Pstar m n).toReal) atTop
        = (limsup (fun n => Pstar m n) atTop).toReal :=
      ENNReal.limsup_toReal_eq ENNReal.one_ne_top
        (Eventually.of_forall (fun n => hPstar_le_one m n))
    -- `φ ∘ Pstar.toReal` is bounded above (by `φ 1`).
    have hφS_bdd : IsBoundedUnder (· ≤ ·) atTop (fun n => φ ((Pstar m n).toReal)) :=
      ⟨φ 1, by
        rw [eventually_map]
        exact Eventually.of_forall (fun n => hφ_mono (hStoReal_le m n))⟩
    calc limsup (fun n => Dtail m n) atTop
        ≤ limsup (fun n => φ ((Pstar m n).toReal)) atTop :=
          limsup_le_limsup (Eventually.of_forall (fun n => hDtail_bound m n))
            (hDtail_cobdd m) hφS_bdd
      _ = φ (limsup (fun n => (Pstar m n).toReal) atTop) :=
          (hφ_mono.map_limsup_of_continuousAt (fun n => (Pstar m n).toReal)
            hφ_cont.continuousAt (hS_bdd m) (hS_cobdd m)).symm
      _ = φ ((limsup (fun n => Pstar m n) atTop).toReal) := by rw [hPtoReal]
  -- **Send `m → ∞`.** Since `limsupₙ Pstar m · → 0`,
  -- `φ(.toReal) → φ 0 = K·ε`.
  have hmtail : Tendsto (fun m => φ ((limsup (fun n => Pstar m n) atTop).toReal))
      atTop (𝓝 (Kr * ε)) := by
    have h0 : Tendsto (fun m => (limsup (fun n => Pstar m n) atTop).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).comp hS3'
      simpa using! this
    have hφ0 : φ 0 = Kr * ε := by simp only [hφ, mul_zero, add_zero]
    have := (hφ_cont.tendsto 0).comp h0
    rw [hφ0] at this
    exact this
  -- For large `m`: `limsupₙ Dtail m · ≤ φ(small) < ε'`; combine with `‖·‖`.
  have hlt : Kr * ε < ε' := lt_trans hKε (by linarith)
  have hclose : ∀ᶠ m in atTop, φ ((limsup (fun n => Pstar m n) atTop).toReal) < ε' :=
    hmtail.eventually (eventually_lt_nhds hlt)
  refine hclose.mono (fun m hm => ?_)
  -- `0 ≤ limsupₙ Dtail` (each `Dtail ≥ 0`), so `‖·‖ = limsupₙ Dtail ≤ φ(...) < ε'`.
  have hnonneg : 0 ≤ limsup (fun n => Dtail m n) atTop :=
    le_limsup_of_le (hDtail_bdd m) (fun b hb => by
      obtain ⟨n, hn⟩ := hb.exists
      exact le_trans (hDtail_nonneg m n) hn)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact lt_of_le_of_lt (hlimsup_bound m) hm

/-- **The ε/3 argument for Theorem 18.14 sufficiency (⟸).** Under the marginal
CLT and asymptotic equicontinuity, the empirical process converges `⇝ₒ` to
`G_P` in `ℓ∞(F)`.

For each `f : LinfF F →ᵇ ℝ`, split the readout error into three pieces:
the `n → ∞` finite-dimensional convergence at fixed `m`, the empirical tail
`‖𝔾ₙ − πₘ𝔾ₙ‖` lifted through the subadditive `E*` triangle inequality,
and the limit tail `∫|f(πₘ·) − f·| dG_P`. Choosing `m` large
(controls both tails) then `n` large (controls the middle) gives the ε/3 bound.

The conclusion is the `WeakConvergesOuter` readout convergence for a fixed
bounded-Lipschitz `f`; `weakConvergesOuter_of_lipschitz_readout` upgrades this to
all bounded-continuous test functions. The Lipschitz hypothesis enters only in
the empirical-tail bound.

vdV p.261 (⟸): the readout-difference + finite-dim CLT + limit-tail step, at a single
bounded-Lipschitz test function. -/
theorem isPDonsker'_of_marginalCLT_and_asymptoticallyEquicontinuous_aux
    (h_clt : IsMarginalCLT F P) (h_eq : IsAsymptoticallyEquicontinuous F P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (f : LinfF F →ᵇ ℝ)
    (hf_lip : ∃ K, LipschitzWith K f) :
    Tendsto (fun n =>
        (outerExpectation μ (fun ξ => ENNReal.ofReal
          (f (empiricalProcessLinf (fun i : Fin n => X i.val ξ)
              (memℓp_empiricalProcess
                ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
                (fun i : Fin n => X i.val ξ))) + ‖f‖))).toReal
          - ‖f‖ * (μ Set.univ).toReal) atTop
      (𝓝 (∫ y, f y ∂(gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne))) := by
  -- The empirical process and the projected process, abbreviated.
  set 𝔾 : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess
        ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ)) with h𝔾
  set GP := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hGP
  -- Abbreviations for the four readout pieces.
  set R : ℕ → ℝ := fun n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal (f (𝔾 n ξ) + ‖f‖))).toReal
      - ‖f‖ * (μ Set.univ).toReal with hR
  set Rproj : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ =>
        ENNReal.ofReal (f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))
          + ‖f‖))).toReal
      - ‖f‖ * (μ Set.univ).toReal with hRproj
  set Lproj : ℕ → ℝ := fun m =>
    ∫ z, f (finiteNetProj hG_env hG hF_meas hF_ent m z) ∂GP with hLproj
  set L : ℝ := ∫ y, f y ∂GP with hL
  -- `Dtail m n = E*[ |f(𝔾ₙ) − f(πₘ𝔾ₙ)| ]`, the pointwise-gap readout at scale `(m,n)`.
  set Dtail : ℕ → ℕ → ℝ := fun m n =>
    (outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)).toReal
    with hDtail
  change Tendsto R atTop (𝓝 L)
  -- Assemble via the abstract ε/3 combiner.
  refine tendsto_outerReadout_of_pieces R Rproj Lproj L Dtail
    ?_middle ?_limtail ?_hdiff ?_Dtail ?_hDbdd
  case _middle =>
    -- Apply `weakConvergesOuter_findim_proj` to `f`, with the
    -- limit pushforward identified via `integral_map`.
    intro m
    have hS2 := weakConvergesOuter_findim_proj hG_env hG hF_meas hH_inf hH_sep
      hF_ent hF_ne h_clt m μ X hX_meas hX_indep hX_id hX_law f
    -- `∫ f d(GP.map πₘ) = ∫ f(πₘ z) dGP = Lproj m` via `integral_map`.
    have hmap : ∫ y, f y ∂((gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent
        hF_ne).map (finiteNetProj hG_env hG hF_meas hF_ent m))
        = Lproj m := by
      rw [integral_map
        (measurable_finiteNetProj hG_env hG hF_meas hF_ent m).aemeasurable
        f.continuous.aestronglyMeasurable, hLproj, hGP]
    rw [hRproj, ← hmap]
    -- The readout is exactly `Rproj m n`; the limit is the pushforward integral.
    convert hS2 using 2
  case _limtail =>
    -- The theorem `limit_proj_error` gives `∫|f(πₘ·) − f·| → 0`, hence
    -- `Lproj m = ∫ f(πₘ·) → ∫ f· = L`.
    have hS4 := limit_proj_error hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne f
    -- `GP` is a probability measure (so `f` and `f ∘ πₘ` are integrable).
    haveI hprob : IsProbabilityMeasure GP := by
      rw [hGP]
      exact (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep
        hF_ent hF_ne).isProbabilityMeasure
    -- `|Lproj m − L| ≤ ∫ |f(πₘ·) − f·| dGP`, and the RHS → 0; squeeze.
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound : ∀ m, dist (Lproj m) L
        ≤ ∫ z, |f (finiteNetProj hG_env hG hF_meas hF_ent m z) - f z| ∂GP := by
      intro m
      -- `dist (Lproj m) L = |Lproj m − L| = |∫ (f(πₘ·) − f·)| ≤ ∫ |f(πₘ·) − f·|`.
      rw [Real.dist_eq, hLproj, hL]
      have hf_int : Integrable f GP := f.integrable _
      have hfπ_int : Integrable
          (fun z => f (finiteNetProj hG_env hG hF_meas hF_ent m z)) GP :=
        Integrable.of_bound
          (f.continuous.measurable.comp
            (measurable_finiteNetProj hG_env hG hF_meas hF_ent m)).aestronglyMeasurable
          ‖f‖ (Eventually.of_forall (fun z => f.norm_coe_le_norm _))
      rw [← integral_sub hfπ_int hf_int]
      exact abs_integral_le_integral_abs
    refine squeeze_zero (fun m => dist_nonneg) hbound ?_
    -- The right-hand side `∫ |f(πₘ·) − f·| dGP → 0`.
    simpa only [hGP] using hS4
  case _hdiff =>
    -- Readout diff (UNCONDITIONAL): the `‖f‖·(μ univ).toReal` shifts in `R` and
    -- `Rproj` cancel, so `|R n − Rproj m n|` is exactly the abs `.toReal`-readout
    -- difference of `f∘𝔾ₙ` and `f∘πₘ𝔾ₙ`, bounded by the pointwise-gap readout
    -- `Dtail m n` via `abs_outerReadout_diff_le_readout_abs`.
    intro m n
    have hbnd := abs_outerReadout_diff_le_readout_abs μ f (𝔾 n)
      (fun ξ => finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))
    -- `R n − Rproj m n = EX.toReal − EY.toReal` (the `‖f‖·(μ univ).toReal` cancel).
    have hsub : R n - Rproj m n
        = (outerExpectation μ (fun ξ => ENNReal.ofReal (f (𝔾 n ξ) + ‖f‖))).toReal
          - (outerExpectation μ (fun ξ => ENNReal.ofReal
              (f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)) + ‖f‖))).toReal := by
      rw [hR, hRproj]; ring
    rw [hsub, hDtail]
    exact hbnd
  case _Dtail =>
    -- Tail vanishing follows from `empirical_readout_tail_outer`; unfold `𝔾`
    -- to identify its integrand with `Dtail`.
    have hHP4 := empirical_readout_tail_outer hG_env hG hF_meas hF_ent
      h_eq μ X hX_meas hX_indep hX_id hX_law f hf_lip
    simpa only [hDtail, h𝔾] using hHP4
  case _hDbdd =>
    -- Boundedness: `Dtail m n = (E*[ofReal |…|]).toReal ≤ 2‖f‖`, the constant
    -- bound (`|f∘𝔾ₙ − f∘πₘ𝔾ₙ| ≤ 2‖f‖`, probability measure ⇒ `E* ≤ ofReal 2‖f‖`).
    intro m
    refine Filter.isBoundedUnder_of ⟨2 * ‖f‖, fun n => ?_⟩
    rw [hDtail]
    have hE_le : outerExpectation μ (fun ξ => ENNReal.ofReal
        |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)
        ≤ ENNReal.ofReal (2 * ‖f‖) := by
      calc outerExpectation μ (fun ξ => ENNReal.ofReal
            |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)
          ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) := by
            refine outerExpectation_mono (fun ξ => ENNReal.ofReal_le_ofReal ?_)
            have hfX := abs_le.1 (f.norm_coe_le_norm (𝔾 n ξ))
            have hfY := abs_le.1 (f.norm_coe_le_norm
              (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ)))
            rw [abs_le]
            constructor <;> [linarith [hfX.1, hfY.2]; linarith [hfX.2, hfY.1]]
        _ = ENNReal.ofReal (2 * ‖f‖) := by
            rw [outerExpectation_const, measure_univ, mul_one]
    calc (outerExpectation μ (fun ξ => ENNReal.ofReal
            |f (𝔾 n ξ) - f (finiteNetProj hG_env hG hF_meas hF_ent m (𝔾 n ξ))|)).toReal
        ≤ (ENNReal.ofReal (2 * ‖f‖)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hE_le
      _ = 2 * ‖f‖ := ENNReal.toReal_ofReal (by positivity)

end Discretization

end AsymptoticStatistics.EmpiricalProcess
