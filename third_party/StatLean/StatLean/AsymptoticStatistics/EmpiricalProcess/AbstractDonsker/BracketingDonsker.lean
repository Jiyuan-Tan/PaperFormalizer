module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.DonskerBracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Characterization
public import Mathlib

@[expose] public section

/-!
# Infinite-dimensional Gaussian-carrier form of van der Vaart Theorem 19.5

This file derives the abstract `IsPDonsker'` conclusion (`𝔾ₙ ⇝ₒ G_P` in
`ℓ∞(F)`) from the bracketing theorem when the centred Gaussian
Hilbert carrier is infinite-dimensional. The hypothesis `hH_inf` is not implied
by finite bracketing entropy, so this is the infinite-dimensional case rather
than the unconditional statement of Theorem 19.5.

The theorem `donsker'_of_finite_bracketing_entropy` applies the Theorem-18.14
characterization `isPDonsker'_iff` to
`isPDonsker_of_finite_bracketing_entropy_integral`. The remaining assumptions
follow from the single analytic input `h_int : J_{[]}(1, F, L₂(P)) < ∞`:

* the square-integrable envelope `hG_env`/`hG`
  (`exists_l2_envelope_of_entropyIntegral`);
* separability of the centred Gaussian Hilbert space `hH_sep`
  (`separableSpace_gpH_of_entropyIntegral`, via `totallyBounded_L2`);
* the finite-entropy clause `hF_ent` (which **is** `h_int`).

Only the infinite-dimensionality clause `hH_inf` remains a hypothesis. The
finite-dimensional and degenerate Gaussian-carrier cases are treated separately.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem 19.5
(book p.270), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Square-integrable envelope from a finite bracketing-entropy integral.**

If `J_{[]}(1, F, L₂(P)) < ∞`, then `F` has a measurable, `L²(P)` envelope `G`:
extract a finite `1`-bracketing cover `{[l_i, u_i]}_{i<k}`
(`hasFiniteBracketingCover_of_entropyIntegral_lt_top`) and take
`G := ∑_i (|l_i| + |u_i|)`. Each `f ∈ F` lies in some bracket `[l_i, u_i]`, so
`|f| ≤ |l_i| + |u_i| ≤ G` (the other summands are nonnegative); `G ∈ L²(P)` because
each bracket bound is in `L²(P)`. -/
lemma exists_l2_envelope_of_entropyIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤) :
    ∃ G, IsEnvelope F G ∧ MemLp G 2 P := by
  obtain ⟨k, l, u, hbr, hcov⟩ :=
    hasFiniteBracketingCover_of_entropyIntegral_lt_top h_int (by norm_num : (0:ℝ) < 1)
  refine ⟨fun x => ∑ i : Fin k, (|l i x| + |u i x|), ?_, ?_⟩
  · -- envelope: `|f x| ≤ |l i x| + |u i x| ≤ ∑ j, (|l j x| + |u j x|)`.
    intro f hf x
    obtain ⟨i, hi⟩ := hcov f hf
    have h_abs_le : |f x| ≤ |l i x| + |u i x| := by
      rcases le_or_gt 0 (f x) with hfx | hfx
      · rw [abs_of_nonneg hfx]
        have h1 : f x ≤ |u i x| := (hi x).2.trans (le_abs_self _)
        linarith [abs_nonneg (l i x)]
      · rw [abs_of_neg hfx]
        have h3 : -(l i x) ≤ |l i x| := neg_le_abs _
        linarith [(hi x).1, abs_nonneg (u i x)]
    refine h_abs_le.trans ?_
    have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin k)), 0 ≤ |l j x| + |u j x| :=
      fun j _ => by positivity
    exact Finset.single_le_sum (f := fun j => |l j x| + |u j x|)
      h_nonneg (Finset.mem_univ i)
  · -- `L²`: a finite sum of `|l i| + |u i| ∈ L²(P)`.
    refine memLp_finset_sum _ ?_
    intro i _
    exact (MemLp.abs (hbr i).memLp_lower).add (MemLp.abs (hbr i).memLp_upper)

/-- **Separability of the centred Gaussian Hilbert space from a finite
bracketing-entropy integral.**

`gpH` is the topological closure of the span of `{centredLp f : f ∈ ↥F}` in
`L²(P)`. A finite bracketing-entropy integral makes `F` totally bounded in the
`L²(P)` semimetric (`totallyBounded_L2`); the centring map `centredLp` is
`1`-Lipschitz (`norm_gpEmbed_sub_le`), so the range of `centredLp` is totally
bounded in `L²(P)`, hence separable (`TotallyBounded.isSeparable`). Separability is
preserved by `Submodule.span` (`TopologicalSpace.IsSeparable.span`) and by
topological `closure` (`TopologicalSpace.IsSeparable.closure`), so `gpH` is a
separable subspace; `TopologicalSpace.IsSeparable.separableSpace` turns that into
`SeparableSpace ↥gpH`.

Thus `hH_sep` follows from `hF_ent` through `totallyBounded_L2`. -/
lemma separableSpace_gpH_of_entropyIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    (hF_env : ∃ G, IsEnvelope F G ∧ MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    TopologicalSpace.SeparableSpace ↥(gpH hF_env hF_meas) := by
  classical
  -- The range of the centred embedding `centredLp : ↥F → L²(P)`.
  set R : Set (Lp ℝ 2 P) := Set.range (fun f : ↥F => centredLp hF_env hF_meas f) with hR
  -- STEP 1: `R` is totally bounded in `L²(P)`, by Lipschitz image of totally-bounded `↥F`.
  obtain ⟨G, hG_env, hG⟩ := id hF_env
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  have hFtb : @TotallyBounded ↥F inst.toUniformSpace Set.univ :=
    totallyBounded_F hG_env hG hF_meas h_int
  -- `centredLp` is `1`-Lipschitz: `‖centredLp s − centredLp t‖ ≤ dist s t = distL2 P s t`.
  have hLip : @LipschitzWith ↥F (Lp ℝ 2 P) inst.toPseudoEMetricSpace _ 1
      (fun f : ↥F => centredLp hF_env hF_meas f) := by
    rw [@lipschitzWith_iff_dist_le_mul ↥F (Lp ℝ 2 P) inst _ _ _]
    intro s t
    rw [NNReal.coe_one, one_mul]
    -- `dist (centredLp s) (centredLp t) = ‖centredLp s − centredLp t‖`.
    rw [dist_eq_norm]
    -- `‖centredLp s − centredLp t‖_{Lp} = ‖gpEmbed s − gpEmbed t‖_{gpH}` ≤ distL2.
    have hcoe : (centredLp hF_env hF_meas s - centredLp hF_env hF_meas t : Lp ℝ 2 P)
        = ((gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t :
            ↥(gpH hF_env hF_meas)) : Lp ℝ 2 P) := by
      rw [Submodule.coe_sub, coe_gpEmbed, coe_gpEmbed]
    rw [hcoe, ← Submodule.coe_norm]
    -- `dist s t = distL2 P s t` under the pseudometric.
    change ‖gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t‖ ≤ distL2 P (s : Ω → ℝ) (t : Ω → ℝ)
    exact norm_gpEmbed_sub_le hF_env hF_meas s t
  have hRtb : TotallyBounded R := by
    have := @TotallyBounded.image ↥F (Lp ℝ 2 P) inst.toUniformSpace _ _ _ hFtb
      hLip.uniformContinuous
    rwa [Set.image_univ] at this
  -- STEP 2: totally bounded ⟹ separable.
  have hRsep : TopologicalSpace.IsSeparable R := hRtb.isSeparable
  -- STEP 3: span + closure preserve separability; `gpH` is the closure of the span.
  have hspan : TopologicalSpace.IsSeparable
      (↑(Submodule.span ℝ R) : Set (Lp ℝ 2 P)) := hRsep.span
  have hgpH : TopologicalSpace.IsSeparable (↑(gpH hF_env hF_meas) : Set (Lp ℝ 2 P)) := by
    have : (↑(gpH hF_env hF_meas) : Set (Lp ℝ 2 P))
        = closure (↑(Submodule.span ℝ R) : Set (Lp ℝ 2 P)) := by
      rw [gpH, Submodule.topologicalClosure_coe]
    rw [this]
    exact hspan.closure
  -- STEP 4: separable set ⟹ `SeparableSpace` of the subtype.
  exact hgpH.separableSpace

/-- **Infinite-dimensional Gaussian-carrier form of Theorem 19.5.**

The theorem `isPDonsker_of_finite_bracketing_entropy_integral` implies
`ℓ∞(F)`-weak-convergence predicate `IsPDonsker'` (`𝔾ₙ ⇝ₒ G_P`) for an
infinite-dimensional centred Gaussian carrier. The additional assumption
`hH_inf` is not implied by finite bracketing entropy.

The conclusion is existential over the derived square-integrable envelope `G`
(`exists_l2_envelope_of_entropyIntegral`); the separability clause `hH_sep`
(`separableSpace_gpH_of_entropyIntegral`) and the finite-entropy clause `hF_ent`
(`= h_int`) are likewise **derived** from `h_int`. Only `hH_inf` (the
infinite-dimensionality of the centred Gaussian Hilbert space) remains an
assumption. Finite-dimensional and degenerate carriers are covered by the
corresponding finite-carrier construction.

The proof applies the Theorem-18.14 characterization `isPDonsker'_iff` to
`isPDonsker_of_finite_bracketing_entropy_integral`; the derived envelope and
separability witnesses provide its remaining assumptions.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem 19.5
(book p.270), §19.2. -/
theorem donsker'_of_finite_bracketing_entropy
    {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
    (hF_ne : F.Nonempty) (hF_meas : ∀ f ∈ F, Measurable f)
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    (hH_inf : ∀ (h : ∃ G, IsEnvelope F G ∧ MemLp G 2 P),
        ¬ FiniteDimensional ℝ ↥(gpH h hF_meas)) :
    ∃ (G : Ω → ℝ) (hG_env : IsEnvelope F G) (hG : MemLp G 2 P),
      IsPDonsker' F P hG_env hG hF_meas (hH_inf ⟨G, hG_env, hG⟩)
        (separableSpace_gpH_of_entropyIntegral h_int ⟨G, hG_env, hG⟩ hF_meas) h_int hF_ne := by
  obtain ⟨G, hG_env, hG⟩ := exists_l2_envelope_of_entropyIntegral h_int
  exact ⟨G, hG_env, hG,
    (isPDonsker'_iff hG_env hG hF_meas (hH_inf ⟨G, hG_env, hG⟩)
        (separableSpace_gpH_of_entropyIntegral h_int ⟨G, hG_env, hG⟩ hF_meas) h_int hF_ne).mpr
      (isPDonsker_of_finite_bracketing_entropy_integral F P hF_meas h_int)⟩

end AsymptoticStatistics.EmpiricalProcess
