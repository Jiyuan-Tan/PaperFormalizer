module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.PBridgeTight
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.Outer
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterTightness

@[expose] public section

/-!
# Theorem 18.14 necessity (⟹): asymptotic tightness ⟹ equicontinuity

The tightness side of the necessity direction of van der Vaart, *Asymptotic
Statistics* Theorem 18.14 (book p.261), via the outer-Prohorov asymptotic
tightness machinery (vdV §18.3 Theorem 18.12; van der Vaart–Wellner §1.5.7).

Weak convergence of the empirical process `𝔾ₙ` in `ℓ∞(F)` (the outer sense
`⇝ₒ`) to the tight `P`-Brownian-bridge law `G_P` forces, by the easy-Prohorov
direction, asymptotic tightness of `𝔾ₙ`. The uniform `distL2`-continuity of
the Brownian-bridge paths, together with closed-set outer portmanteau, gives the
oscillation-modulus control in outer probability that defines
`IsAsymptoticallyEquicontinuous`.

## Main results (all proved; vdV p.261 / 18.12)

* `outerMeasure_modulusComplement_le` — weak convergence of `𝔾ₙ` to the
  uniformly `distL2`-continuous Brownian bridge ⟹ close-pair oscillations above
  any threshold `ε` have limiting outer probability at most any prescribed `η`.
* `empiricalProcess_asymptoticallyTight` — the `⇝ₒ`-to-`G_P` hypothesis ⟹
  asymptotic tightness of `𝔾ₙ` (easy-Prohorov + `pBridge_tight`).
* `equicont_of_weakConvergesOuter_gp` — the `⇝ₒ`-to-`G_P` hypothesis ⟹
  `IsAsymptoticallyEquicontinuous F P`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Theorem
18.14 (book p.261), Theorem 18.12 (book p.260), §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology AsymptoticStatistics BoundedContinuousFunction
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

section Necessity

variable {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
variable {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
  (hF_meas : ∀ f ∈ F, Measurable f)
  (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)

/-- The **good-modulus set** at radius `δ` and level `c`: paths whose
`distL2 P`-modulus of continuity is `≤ c` at scale `δ`. This is the modulus part
of a `modulusBall` (no sup-bound constraint); its metric thickening is used in
the closed-set outer-portmanteau argument. -/
def goodModulusSet (P : Measure Ω) (F : Set (Ω → ℝ)) (δ c : ℝ) : Set (LinfF F) :=
  {z | ∀ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ → |z f - z g| ≤ c}

/-- **`goodModulusSet` is closed.** Each pair `(f, g)` within `δ` cuts out a
closed condition `{z | |z f − z g| ≤ c}` (coordinate evaluation is continuous,
`isClosed_le`); the whole set is the intersection over all such pairs. -/
theorem isClosed_goodModulusSet (P : Measure Ω) (F : Set (Ω → ℝ)) (δ c : ℝ) :
    IsClosed (goodModulusSet P F δ c) := by
  have hcont := continuous_coordEval F
  have : goodModulusSet P F δ c
      = ⋂ f : ↥F, ⋂ g : ↥F,
        {z : LinfF F | distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ → |z f - z g| ≤ c} := by
    ext z; simp only [goodModulusSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter (fun f => isClosed_iInter (fun g => ?_))
  by_cases hfg : distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ
  · have hset : {z : LinfF F | distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ → |z f - z g| ≤ c}
        = {z : LinfF F | |z f - z g| ≤ c} := by
      ext z; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hfg, fun h _ => h⟩
    rw [hset]
    exact isClosed_le (((hcont f).sub (hcont g)).abs) continuous_const
  · have hset : {z : LinfF F | distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ → |z f - z g| ≤ c}
        = Set.univ := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact fun h => absurd h hfg
    rw [hset]; exact isClosed_univ

/-- **Coordinate sup-norm bound.** For `z w : LinfF F` and `f : ↥F`,
`|z f − w f| ≤ ‖z − w‖` (each coordinate is dominated by the sup-norm). -/
theorem abs_coordEval_sub_le_norm {F : Set (Ω → ℝ)} (z w : LinfF F) (f : ↥F) :
    |z f - w f| ≤ ‖z - w‖ := by
  have hsub : z f - w f = (z - w) f := by rw [lp.coeFn_sub z w]; rfl
  rw [hsub, ← Real.norm_eq_abs]
  exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) f

/-- **`G_P`-mass of the good-modulus complement is small.** Because
`gaussianPBridge` concentrates on the `distL2 P`-uniformly-continuous paths
(`IsPBrownianBridge.ucPaths`), the good-modulus sets `goodModulusSet P F (1/(k+1)) c`
increase to a full-measure set as `k → ∞`, so for any `η > 0` there is a radius
`δ > 0` with `gaussianPBridge ((goodModulusSet P F δ c)ᶜ) ≤ ofReal η`. -/
theorem gp_goodModulusSet_compl_mass_le {c : ℝ} (hc : 0 < c)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
        (goodModulusSet P F δ c)ᶜ ≤ ENNReal.ofReal η := by
  classical
  haveI : IsProbabilityMeasure
      (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :=
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).isProbabilityMeasure
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  -- The increasing family of good-modulus sets `S k = goodModulusSet … (1/(k+1)) c`.
  set S : ℕ → Set (LinfF F) := fun k => goodModulusSet P F ((k + 1 : ℝ)⁻¹) c with hS
  have hSmono : Monotone S := by
    intro j k hjk z hz f g hfg
    refine hz f g (le_trans hfg ?_)
    have hjk' : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hjk
      linarith
    gcongr
  -- `⋃ k, S k` has full measure: a.e. path is `distL2`-uc, hence in some `S k`.
  have hcover : ∀ᵐ z ∂ν, z ∈ ⋃ k, S k := by
    have huc := (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep
      hF_ent hF_ne).ucPaths
    filter_upwards [huc] with z hz
    obtain ⟨δ', hδ'pos, hδ'⟩ := hz c hc
    obtain ⟨k, hk⟩ := exists_nat_gt (δ')⁻¹
    refine Set.mem_iUnion.2 ⟨k, fun f g hfg => ?_⟩
    -- `(k+1)⁻¹ < δ'`, so `distL2 f g ≤ (k+1)⁻¹ < δ'` ⟹ `|z f − z g| < c`.
    have hlt : (k + 1 : ℝ)⁻¹ < δ' := by
      have hkk : (δ')⁻¹ < (k : ℝ) + 1 := lt_trans hk (by linarith [Nat.cast_nonneg (α := ℝ) k])
      rw [inv_lt_comm₀ (by positivity) hδ'pos]
      exact hkk
    exact le_of_lt (hδ' f g (lt_of_le_of_lt hfg hlt))
  -- `ν (⋃ S k) = ν univ = 1`.
  have hfullmeas : ν (⋃ k, S k) = 1 := by
    have hnull : ν (⋃ k, S k)ᶜ = 0 := ae_iff.1 hcover
    have hmeas : MeasurableSet (⋃ k, S k) :=
      MeasurableSet.iUnion fun k =>
        (isClosed_goodModulusSet P F ((k + 1 : ℝ)⁻¹) c).measurableSet
    have := measure_add_measure_compl hmeas (μ := ν)
    rw [hnull, add_zero, measure_univ] at this
    exact this
  -- Continuity of measure: `ν (S k) → ν (⋃ S k) = 1`.
  have htendsto : Tendsto (fun k => ν (S k)) atTop (𝓝 (ν (⋃ k, S k))) :=
    tendsto_measure_iUnion_atTop hSmono
  rw [hfullmeas] at htendsto
  -- Pick `k` with `ν (S k) ≥ 1 − η` ⟹ `ν (S k)ᶜ ≤ η`.
  have hev : ∀ᶠ k in atTop, (1 : ℝ≥0∞) - ENNReal.ofReal η ≤ ν (S k) := by
    rcases le_or_gt 1 (ENNReal.ofReal η) with hle | hlt
    · refine Eventually.of_forall fun k => ?_
      rw [tsub_eq_zero_of_le hle]; exact zero_le
    · refine htendsto.eventually (eventually_ge_nhds ?_)
      rw [ENNReal.sub_lt_self_iff ENNReal.one_ne_top]
      exact ⟨one_pos, ENNReal.ofReal_pos.2 hη⟩
  obtain ⟨k, hk⟩ := hev.exists
  refine ⟨(k + 1 : ℝ)⁻¹, by positivity, ?_⟩
  -- `ν (S k)ᶜ = 1 − ν (S k) ≤ 1 − (1 − η) = η`.
  have hScompl : ν (S k)ᶜ = 1 - ν (S k) := by
    rw [measure_compl (isClosed_goodModulusSet P F _ c).measurableSet (measure_ne_top _ _),
      measure_univ]
  -- The goal's set is `(goodModulusSet … ((k+1)⁻¹) c)ᶜ`, which is `(S k)ᶜ` by definition.
  show ν (S k)ᶜ ≤ ENNReal.ofReal η
  rw [hScompl]
  -- `1 − ν (S k) ≤ 1 − (1 − η) = η` (since `η ≤ 1` after capping; if `η > 1` the bound is trivial).
  rcases le_or_gt 1 (ENNReal.ofReal η) with hle | hlt
  · exact le_trans tsub_le_self hle
  · calc 1 - ν (S k)
        ≤ 1 - (1 - ENNReal.ofReal η) := tsub_le_tsub_left hk 1
      _ = ENNReal.ofReal η := ENNReal.sub_sub_cancel ENNReal.one_ne_top (le_of_lt hlt)

/-- **Close-pair event lies in a thickening complement.** If a path `z` has
a close pair `(f, g)` with `distL2 f g ≤ δ` and `η < |z f − z g|`, then `z` lies
*outside* the `(η/4)`-thickening of the good-modulus set `goodModulusSet P F δ (η/2)`:
any `w` in that set has `|w f − w g| ≤ η/2`, so if `‖z − w‖ < η/4` then
`|z f − z g| ≤ |w f − w g| + 2‖z − w‖ < η/2 + η/2 = η`, a contradiction. The
thickening complement is closed, so outer portmanteau applies. -/
theorem closePair_mem_thickening_compl {F : Set (Ω → ℝ)} {P : Measure Ω}
    {δ η : ℝ} (hη : 0 < η) (z : LinfF F) (f g : ↥F)
    (hfg : distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ) (hosc : η < |z f - z g|) :
    z ∈ (Metric.thickening (η / 4) (goodModulusSet P F δ (η / 2)))ᶜ := by
  rw [Set.mem_compl_iff, Metric.mem_thickening_iff]
  push_neg
  intro w hw
  -- `w ∈ goodModulusSet` ⟹ `|w f − w g| ≤ η/2`; coordinate sup-norm bound.
  have hwmod : |w f - w g| ≤ η / 2 := hw f g hfg
  -- `|z f − z g| ≤ |w f − w g| + |z f − w f| + |z g − w g| ≤ η/2 + 2‖z − w‖`.
  have hzf : |z f - w f| ≤ ‖z - w‖ := abs_coordEval_sub_le_norm z w f
  have hzg : |z g - w g| ≤ ‖z - w‖ := abs_coordEval_sub_le_norm z w g
  have htri : |z f - z g| ≤ |w f - w g| + (|z f - w f| + |z g - w g|) := by
    have e : z f - z g = (w f - w g) + ((z f - w f) - (z g - w g)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_sub _ _
  -- if `dist z w < η/4`, i.e. `‖z − w‖ < η/4`, then `|z f − z g| < η`, contradiction.
  by_contra hlt
  push_neg at hlt
  rw [dist_eq_norm] at hlt
  have hfinal : |z f - z g| < η := by
    have h2 : ‖z - w‖ < η / 4 := hlt
    nlinarith [hwmod, hzf, hzg, htri, h2]
  exact absurd hosc (not_lt.2 (le_of_lt hfinal))

/-- **Modulus control from weak convergence to the uniformly continuous bridge.**

Suppose the empirical process `𝔾ₙ` (packaged through `empiricalProcessLinf`)
converges weakly in the outer sense to the `P`-Brownian bridge. For every
oscillation threshold `ε > 0` and probability tolerance `η > 0`, there is a
`distL2`-radius `δ > 0` such that the close-pair oscillation event

`{ξ | ∃ f g : ↥F, distL2 P f g < δ ∧ ε < |𝔾ₙ(f)(ξ) − 𝔾ₙ(g)(ξ)|}`

is, in the `limsup` along `atTop`, at most `ENNReal.ofReal η`.

The measure `gaussianPBridge` concentrates on paths that are uniformly
continuous for `distL2 P` (`IsPBrownianBridge.ucPaths`). This supplies a radius
`δ` for the oscillation threshold `ε`, with bridge-complement mass bounded by
the independent tolerance `η`; closed-set outer portmanteau transports that
bound to `𝔾ₙ`. The hypothesis `h` is the unfolded `WeakConvergesOuter`
predicate. This is the modulus implication used in vdV Theorem 18.14 (p.261),
with the weak-convergence and tightness background of Theorem 18.12 (p.260). -/
theorem outerMeasure_modulusComplement_le
    (h : ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
        [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
        (∀ i, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X μ →
        (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
        μ.map (X 0) = P →
        WeakConvergesOuter (fun _ => μ)
          (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ)))
          (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧
      limsup (fun n => μ.outerMeasureStar
          {ξ | ∃ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ ∧
            ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (g : Ω → ℝ)|})
          atTop
        ≤ ENNReal.ofReal η := by
  intro ε η hε hη
  haveI : IsProbabilityMeasure
      (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :=
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).isProbabilityMeasure
  set ν := gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hν
  -- The `⇝ₒ` instance for this iid sample.
  have hwc := h μ X hX_meas hX_indep hX_id hX_law
  -- The empirical process as `Xn` for the portmanteau bound.
  set Xn : ℕ → Ξ → LinfF F := fun n ξ =>
    empiricalProcessLinf (fun i : Fin n => X i.val ξ)
      (memℓp_empiricalProcess ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
        (fun i : Fin n => X i.val ξ)) with hXn
  -- The good-modulus radius `δ` at oscillation tolerance `ε/2` with `ν`-complement
  -- The complement has mass at most `ofReal η`; the oscillation tolerance
  -- `ε` and mass tolerance `η` are independent.
  obtain ⟨δ, hδpos, hδmass⟩ :=
    gp_goodModulusSet_compl_mass_le hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      (by linarith : (0 : ℝ) < ε / 2) hη
  refine ⟨δ, hδpos, ?_⟩
  -- The closed majorant `C = (thickening (ε/4) (goodModulusSet … δ (ε/2)))ᶜ`.
  set K := goodModulusSet P F δ (ε / 2) with hK
  set C := (Metric.thickening (ε / 4) K)ᶜ with hC
  have hCclosed : IsClosed C := Metric.isOpen_thickening.isClosed_compl
  -- `ν C ≤ ν Kᶜ ≤ ofReal η` (`K ⊆ thickening K` ⟹ complement shrinks).
  have hνC : ν C ≤ ENNReal.ofReal η := by
    refine le_trans (measure_mono ?_) hδmass
    rw [hC]
    exact Set.compl_subset_compl.2 (Metric.self_subset_thickening (by linarith) K)
  -- The close-pair event is contained in `Xn n ⁻¹' C` (L3, at oscillation `ε`).
  have hsubset : ∀ n,
      {ξ | ∃ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ ∧
        ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)
              - empiricalProcess P n (fun i : Fin n => X i.val ξ) (g : Ω → ℝ)|}
      ⊆ Xn n ⁻¹' C := by
    intro n ξ hξ
    obtain ⟨f, g, hclose, hosc⟩ := hξ
    rw [Set.mem_preimage, hC, hK]
    exact closePair_mem_thickening_compl hε (Xn n ξ) f g (le_of_lt hclose) hosc
  -- Apply portmanteau to the closed set `C`, then use `outerMeasureStar` monotonicity.
  calc limsup (fun n => μ.outerMeasureStar
          {ξ | ∃ f g : ↥F, distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ ∧
            ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (g : Ω → ℝ)|}) atTop
      ≤ limsup (fun n => μ.outerMeasureStar (Xn n ⁻¹' C)) atTop :=
        limsup_le_limsup (Eventually.of_forall fun n =>
          outerMeasureStar_mono μ (hsubset n))
    _ ≤ ν C := limsup_outerMeasureStar_preimage_isClosed_le (μ := fun _ => μ) hwc hCclosed
    _ ≤ ENNReal.ofReal η := hνC

/-- **Asymptotic tightness of `𝔾ₙ` from `⇝ₒ`-to-`G_P`.**

If the empirical process converges weakly in `ℓ∞(F)` (outer sense) to the tight
`P`-Brownian bridge `G_P`, stated in the unfolded `WeakConvergesOuter` form, then
`𝔾ₙ` is asymptotically tight.

Glue: `isAsymptoticallyTight_of_weakConvergesOuter` (easy-Prohorov direction)
applied to the per-sample `WeakConvergesOuter` instance from `h`, with the tight
Borel limit supplied by `pBridge_tight`, transported from `gpBridgeMeasure` to
`gaussianPBridge`.

vdV p.261 (⟹): `⇝ₒ` limit tight + portmanteau ⟹ sequence asymptotically tight. -/
theorem empiricalProcess_asymptoticallyTight
    (h : ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
        [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
        (∀ i, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X μ →
        (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
        μ.map (X 0) = P →
        WeakConvergesOuter (fun _ => μ)
          (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ)))
          (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    IsAsymptoticallyTight (fun _ => μ)
      (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
        (memℓp_empiricalProcess
          ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
          (fun i : Fin n => X i.val ξ))) := by
  haveI : IsProbabilityMeasure
      (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :=
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).isProbabilityMeasure
  exact AsymptoticStatistics.isAsymptoticallyTight_of_weakConvergesOuter
    (h μ X hX_meas hX_indep hX_id hX_law)
    (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).tight

/-- **`⇝ₒ`-to-`G_P` ⟹ asymptotic equicontinuity (the vdV 18.14(ii) form).**

If the empirical process converges weakly in `ℓ∞(F)` (outer sense) to the tight
`P`-Brownian bridge `G_P`, stated in the unfolded `WeakConvergesOuter` form,
then `F` is asymptotically equicontinuous.

The predicate `IsAsymptoticallyEquicontinuous` is the vdV 18.14(ii) outer-sup
modulus, and `outerMeasure_modulusComplement_le` supplies that modulus from
`⇝ₒ` at the same `(ε, η)`.

Since `IsPDonsker'` is definitionally equal to the universal form `h`, this
theorem yields the equicontinuity half of the characterization.

vdV p.261 (⟹): tightness ⟹ the modulus-of-continuity control. -/
theorem equicont_of_weakConvergesOuter_gp
    (h : ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
        [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
        (∀ i, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X μ →
        (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
        μ.map (X 0) = P →
        WeakConvergesOuter (fun _ => μ)
          (fun n ξ => empiricalProcessLinf (fun i : Fin n => X i.val ξ)
            (memℓp_empiricalProcess
              ⟨G, hG_env, hG.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)⟩
              (fun i : Fin n => X i.val ξ)))
          (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)) :
    IsAsymptoticallyEquicontinuous F P := by
  intro Ξ _inst μ _inst2 X hX_meas hX_indep hX_id hX_law ε η hε hη
  exact outerMeasure_modulusComplement_le hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
    h μ X hX_meas hX_indep hX_id hX_law ε η hε hη

end Necessity

end AsymptoticStatistics.EmpiricalProcess
