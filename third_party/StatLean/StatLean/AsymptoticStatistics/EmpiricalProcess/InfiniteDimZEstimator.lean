module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformRandomFunctions
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterProbAsymptotics

@[expose] public section

/-!
# Infinite-dimensional Z-estimator (vdV Theorem 19.26)

The `ℓ∞(H)`-indexed generalization of the scalar
goodness-of-fit Theorem 19.23 (`empiricalProcess_param_estimation`). For a
class `𝓕 = {ψ_{θ,h} : ‖θ − θ₀‖ < δcls, h ∈ H}` that is `P`-Donsker with finite
envelope, with `θ ↦ Pψ_θ` Fréchet-differentiable at a zero `θ₀` with a
bounded-below derivative `V`, and with `sup_h P(ψ_{θ,h} − ψ_{θ₀,h})² → 0` as
`θ → θ₀`: if `√n ℙₙψ_{θ̂_n} = o_P(1)` in `ℓ∞(H)` and `θ̂_n →ₚ θ₀`, then

    √n V(θ̂_n − θ₀) = −𝔾ₙψ_{θ₀} + o_P(1)   (in ℓ∞(H)).

Here `θ` belongs to a general normed space `B`, `ℓ∞(H)` is represented as
`H → ℝ`, and the conclusion uses outer probability for the supremum over
`H` (`TendstoZeroInOuterProbSup`). The `√n ℙₙψ_{θ̂_n}` rate is little-`o_P`,
as in Theorem 5.21.

Proof route: 5.21-style master identity + uniform Lemma 19.24
(`uniform_donsker_random_function_consistency`) + Fréchet remainder bound
(`frechet_remainder_sup_bound`) + rate bootstrap (`rate_bootstrap_oP`).

Principal declaration: `infinite_dim_z_estimator`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter
open scoped ENNReal Topology

/-- **Bundled hypotheses for Theorem 19.26 (infinite-dimensional Z-estimator).**

Here `θ ∈ B` for a general normed space, `H` is arbitrary, and `ℓ∞(H)` is
encoded as `H → ℝ`. The Fréchet derivative `V : B →ₗ[ℝ] (H → ℝ)` is a
linear map together with the explicit bounded-below condition `bddbelow_V`.

Only the sample-independent hypotheses are bundled here. The sample-specific
tightness assumption `h_tight` is an argument of `infinite_dim_z_estimator`
because it refers to the iid sample `μ`, `X`. -/
structure Theorem19_26Hyp
    {Ω : Type*} [MeasurableSpace Ω]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {H : Type*}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Set (Ω → ℝ)) (ψ : B → H → (Ω → ℝ)) (θ₀ : B)
    (V : B →ₗ[ℝ] (H → ℝ)) (δcls : ℝ) : Prop where
  /-- Constitutive (vdV §19.4 p.281): the Donsker class radius `δ` is positive
  (`𝓕 = {ψ_{θ,h} : ‖θ − θ₀‖ < δ}` for some `δ > 0`). -/
  hδcls : 0 < δcls
  /-- Constitutive (vdV §19.4 p.281): the class `𝓕` contains every `ψ_{θ,h}` with
  `‖θ − θ₀‖ < δcls` (definition of the Donsker class). -/
  hclass_mem : ∀ θ : B, ‖θ - θ₀‖ < δcls → ∀ h, ψ θ h ∈ 𝓕
  /-- Constitutive (vdV §19.4 p.281): each `x ↦ ψ_{θ,h}(x)` is measurable ("let
  `x ↦ ψ_{θ,h}(x)` be a measurable function"). -/
  hψ_meas : ∀ (θ : B) (h : H), Measurable (ψ θ h)
  /-- Constitutive (vdV §19.4 p.281): `𝓕` has a finite (integrable) envelope
  function ("with finite envelope function"). -/
  henv : ∃ G : Ω → ℝ, IsEnvelope 𝓕 G ∧ Integrable G P
  /-- Constitutive (vdV §19.4 p.281): `𝓕` is `P`-Donsker — equicontinuity half
  The tightness half is supplied separately as `h_tight`. -/
  h_equicont : IsAsymptoticallyEquicontinuous 𝓕 P
  /-- Constitutive (vdV §19.4 p.281): `θ₀` is a zero of `θ ↦ Pψ_θ`, i.e.
  `Pψ_{θ₀,h} = 0` for all `h` ("Fréchet-differentiable at a zero `θ₀`"). -/
  hPθ₀_zero : ∀ h, ∫ x, ψ θ₀ h x ∂P = 0
  /-- Constitutive (vdV §19.4 p.281): `V` has a continuous inverse on its range,
  encoded as bounded-below in the `ℓ∞(H)` sup: `∃ c > 0, c‖b‖ ≤ ‖V b‖_H`, in
  ENNReal-`⨆` form. -/
  bddbelow_V : ∃ c : ℝ, 0 < c ∧ ∀ b : B,
    ENNReal.ofReal (c * ‖b‖) ≤ ⨆ h, ENNReal.ofReal |V b h|
  /-- Constitutive (vdV §19.4 p.281): `θ ↦ Pψ_θ` is Fréchet-differentiable at
  `θ₀` with derivative `V`. `ε-δ` sup-over-`H` form (mirrors
  `Theorem19_23Hyp.frechet`): `sup_h |Pψ_{θ,h} − Pψ_{θ₀,h} − V(θ−θ₀)_h| ≤
  ε‖θ − θ₀‖`. -/
  frechet : ∀ ε > 0, ∃ δ > 0, ∀ θ : B, 0 < ‖θ - θ₀‖ → ‖θ - θ₀‖ < δ →
    (⨆ h, ENNReal.ofReal
        |∫ x, ψ θ h x ∂P - ∫ x, ψ θ₀ h x ∂P - V (θ - θ₀) h|)
      ≤ ENNReal.ofReal (ε * ‖θ - θ₀‖)
  /-- Constitutive (vdV §19.4 p.281): uniform `L²`-continuity of the family at
  `θ₀`, `‖P(ψ_{θ,h} − ψ_{θ₀,h})²‖_H → 0` as `θ → θ₀`. `ε-δ` sup-over-`H` form on
  `distL2` (`distL2² = P(ψ_θ − ψ_{θ₀})²`). -/
  unif_L2_cont : ∀ ε > 0, ∃ δ > 0, ∀ θ : B, ‖θ - θ₀‖ < δ →
    (⨆ h, ENNReal.ofReal (distL2 P (ψ θ h) (ψ θ₀ h))) ≤ ENNReal.ofReal ε

/-- **Master identity (pure algebra; vdV §19.4 / 5.21 rearrangement).**

For any realized parameter `b : B` (playing the role of `θ̂_n(ξ)`), sample `Xs`,
and index `h`:

    √n V(b − θ₀)_h + 𝔾ₙψ_{θ₀,h}
      = √n ℙₙψ_{b,h} − (𝔾ₙψ_{b,h} − 𝔾ₙψ_{θ₀,h}) − S_{n,h}

with remainder `S_{n,h} := √n Pψ_{b,h} − √n V(b − θ₀)_h`. Proved by unfolding
`empiricalProcess f = √n ℙₙf − √n Pf`; no hypothesis (not even `Pψ_{θ₀} = 0`) is
needed — it is a pure rearrangement. -/
theorem master_identity
    {Ω : Type*} [MeasurableSpace Ω]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {H : Type*}
    (P : Measure Ω) (ψ : B → H → (Ω → ℝ)) (θ₀ : B) (V : B →ₗ[ℝ] (H → ℝ))
    (n : ℕ) (Xs : Fin n → Ω) (b : B) (h : H) :
    Real.sqrt n * V (b - θ₀) h + empiricalProcess P n Xs (ψ θ₀ h)
      = Real.sqrt n * empiricalAvg (ψ b h) n Xs
        - (empiricalProcess P n Xs (ψ b h) - empiricalProcess P n Xs (ψ θ₀ h))
        - (Real.sqrt n * (∫ x, ψ b h x ∂P) - Real.sqrt n * V (b - θ₀) h) := by
  simp only [empiricalProcess]
  ring

/-- **Fréchet remainder is `o_P(r_n)` (step 3 + consistency).**

With `r_n(ξ) := √n‖θ̂_n(ξ) − θ₀‖` and remainder
`S_{n,ξ,h} := √n Pψ_{θ̂_n(ξ),h} − √n V(θ̂_n(ξ) − θ₀)_h`, the Fréchet `ε-δ` bound
plus `Pψ_{θ₀} = 0` give `sup_h |S| ≤ ε · r_n` on `{‖θ̂_n − θ₀‖ < δ}`, and
consistency kills the complement. Hence for every `ε > 0`,
`μ*{ξ | ∃h, ε·r_n < |S|} → 0`. This is exactly the `hS` input of
`rate_bootstrap_oP`. -/
theorem frechet_remainder_sup_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {H : Type*}
    (P : Measure Ω) (ψ : B → H → (Ω → ℝ)) (θ₀ : B) (V : B →ₗ[ℝ] (H → ℝ))
    (hPθ₀_zero : ∀ h, ∫ x, ψ θ₀ h x ∂P = 0)
    (h_frechet : ∀ ε > 0, ∃ δ > 0, ∀ θ : B, 0 < ‖θ - θ₀‖ → ‖θ - θ₀‖ < δ →
      (⨆ h, ENNReal.ofReal
          |∫ x, ψ θ h x ∂P - ∫ x, ψ θ₀ h x ∂P - V (θ - θ₀) h|)
        ≤ ENNReal.ofReal (ε * ‖θ - θ₀‖))
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (θ_hat : ∀ n, (Fin n → Ω) → B) (X : ℕ → Ξ → Ω)
    (h_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      μ.outerMeasureStar {ξ | ∃ h,
        ε * (Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) <
          |Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h x ∂P)
            - Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h|})
      atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hbd⟩ := h_frechet ε hε
  -- Squeeze between `0` and `μ {δ/2 < ‖θ̂ₙ − θ₀‖} → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h_consist (δ / 2) (half_pos hδ)) (fun n => zero_le) (fun n => ?_)
  -- `μ*(Eₙ) ≤ μ*({δ/2 < ‖·‖}) ≤ μ({δ/2 < ‖·‖})`.
  refine le_trans (outerMeasureStar_mono μ ?_) (outerMeasureStar_le_measure μ _)
  -- Inclusion `Eₙ ⊆ {δ/2 < ‖θ̂ₙ − θ₀‖}`.
  intro ξ hξ
  simp only [Set.mem_setOf_eq] at hξ ⊢
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨h, hh⟩ := hξ
  set b := θ_hat n (fun i : Fin n => X i.val ξ) with hb
  -- `|Sₙ| ≤ ε · rₙ`, contradicting `hh`.
  have hkey : |Real.sqrt n * (∫ x, ψ b h x ∂P) - Real.sqrt n * V (b - θ₀) h|
      ≤ ε * (Real.sqrt n * ‖b - θ₀‖) := by
    rcases eq_or_lt_of_le (norm_nonneg (b - θ₀)) with hzero | hpos
    · -- `b = θ₀`: both sides vanish.
      have hb0 : b - θ₀ = 0 := norm_eq_zero.1 hzero.symm
      have hbθ : b = θ₀ := by rwa [sub_eq_zero] at hb0
      simp [hbθ, hPθ₀_zero h]
    · -- `0 < ‖b − θ₀‖ < δ`: use the Fréchet ε-δ bound.
      have hδ' : ‖b - θ₀‖ < δ := lt_of_le_of_lt hcon (by linarith)
      have hsup := hbd b hpos hδ'
      have hle : ENNReal.ofReal
          |∫ x, ψ b h x ∂P - ∫ x, ψ θ₀ h x ∂P - V (b - θ₀) h|
          ≤ ENNReal.ofReal (ε * ‖b - θ₀‖) :=
        le_trans (le_iSup (fun h' : H => ENNReal.ofReal
          |∫ x, ψ b h' x ∂P - ∫ x, ψ θ₀ h' x ∂P - V (b - θ₀) h'|) h) hsup
      have hreal : |∫ x, ψ b h x ∂P - ∫ x, ψ θ₀ h x ∂P - V (b - θ₀) h|
          ≤ ε * ‖b - θ₀‖ :=
        (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε.le (norm_nonneg _))).1 hle
      rw [hPθ₀_zero h, sub_zero] at hreal
      calc |Real.sqrt n * (∫ x, ψ b h x ∂P) - Real.sqrt n * V (b - θ₀) h|
          = Real.sqrt n * |∫ x, ψ b h x ∂P - V (b - θ₀) h| := by
            rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ Real.sqrt n * (ε * ‖b - θ₀‖) :=
            mul_le_mul_of_nonneg_left hreal (Real.sqrt_nonneg _)
        _ = ε * (Real.sqrt n * ‖b - θ₀‖) := by ring
  exact absurd hkey (not_le.2 hh)

/-- **Theorem 19.26 (infinite-dimensional Z-estimator).**

Under `Theorem19_26Hyp`, an iid sample, the tightness half of the Donsker
hypothesis (`h_tight`), consistency `θ̂_n →ₚ θ₀` (`h_consist`), and the
`o_P(n^{-1/2})` estimating equation `√n ℙₙψ_{θ̂_n} →ₚ 0` in `ℓ∞(H)` (`h_est_eq`),
the centred estimator satisfies

    √n V(θ̂_n − θ₀) + 𝔾ₙψ_{θ₀} = o_P(1)   (in ℓ∞(H), outer probability),

i.e. `√n V(θ̂_n − θ₀) = −𝔾ₙψ_{θ₀} + o_P(1)`.

The identity `master_identity` rearranges the target into `√n ℙₙψ_{θ̂_n}` (the
`o_P` estimating equation `h_est_eq`) minus the uniform-19.24 remainder
`𝔾ₙψ_{θ̂_n} − 𝔾ₙψ_{θ₀}` (`o_P` via
`uniform_donsker_random_function_consistency` fed by `modifiedRandomFunction`)
minus `S_n` (`o_P` via `frechet_remainder_sup_bound` + `rate_bootstrap_oP`,
using `bddbelow_V` and `h_tight`); `oP_sup_add` combines the three `o_P` pieces. -/
theorem infinite_dim_z_estimator
    {Ω : Type*} [MeasurableSpace Ω]
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {H : Type*}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Set (Ω → ℝ)) (ψ : B → H → (Ω → ℝ)) (θ₀ : B)
    (V : B →ₗ[ℝ] (H → ℝ)) (δcls : ℝ)
    (hyp : Theorem19_26Hyp P 𝓕 ψ θ₀ V δcls)
    (θ_hat : ∀ n, (Fin n → Ω) → B)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (h_tight : IsBoundedInOuterProbSup μ (fun n ξ h =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)))
    (h_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0))
    (h_est_eq : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
        n (fun i : Fin n => X i.val ξ))) :
    TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
        + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)) := by
  obtain ⟨c, hc_pos, hc_bd⟩ := hyp.bddbelow_V
  have hθ₀_mem : ∀ h, ψ θ₀ h ∈ 𝓕 := by
    intro h
    exact hyp.hclass_mem θ₀ (by simpa using hyp.hδcls) h
  -- ============ STEP 1a: the uniform-19.24 remainder `Rhat` is o_P. ============
  have h_sup := sup_distL2_tendsto_zero_of_unif_L2_cont P ψ θ₀ hyp.unif_L2_cont μ θ_hat X h_consist
  have h_bad : Tendsto (fun n =>
      μ {ξ | δcls ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h_consist (δcls / 2) (half_pos hyp.hδcls))
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    refine measure_mono fun ξ hξ => ?_
    simp only [Set.mem_setOf_eq] at hξ ⊢
    linarith [half_lt_self hyp.hδcls]
  have h_tail := modifiedRandomFunction_tail P ψ θ₀ δcls θ_hat μ X h_sup h_bad
  have h_mem := modifiedRandomFunction_mem ψ θ₀ δcls θ_hat X 𝓕 hyp.hclass_mem hθ₀_mem
  have Rmod_oP := uniform_donsker_random_function_consistency 𝓕 P hyp.h_equicont μ X
    hX_meas hX_indep hX_id hX_law (modifiedRandomFunction ψ θ₀ δcls θ_hat X) h_mem
    (ψ θ₀) hθ₀_mem h_tail
  have Rhat_oP : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
        - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)) := by
    refine tendstoZeroInOuterProbSup_of_eq_off_vanishing Rmod_oP h_bad ?_
    intro n ξ hb hh
    simp only [Set.mem_setOf_eq, not_le] at hb
    rw [modifiedRandomFunction_eq_on_good ψ θ₀ δcls θ_hat X n ξ hh hb]
  -- ============ STEP 1b: the Fréchet remainder `Sfam` is o_P (rate bootstrap). ============
  have hS := frechet_remainder_sup_bound P ψ θ₀ V hyp.hPθ₀_zero hyp.frechet μ θ_hat X h_consist
  have hlb : ∀ (n : ℕ) (ξ : Ξ), ENNReal.ofReal
      (c * (Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖))
        ≤ ⨆ h, ENNReal.ofReal
            |Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h| := by
    intro n ξ
    have hkey := hc_bd (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    have hnorm : ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)‖
        = Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hnorm] at hkey
    have hV : ∀ h, V (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) h
        = Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h := by
      intro h; rw [map_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [hV] at hkey
    exact hkey
  have hW : ∀ (n : ℕ) (ξ : Ξ),
      (⨆ h, ENNReal.ofReal
          |Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h|)
        ≤ (⨆ h, ENNReal.ofReal
            |Real.sqrt n
                * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
                    (fun i : Fin n => X i.val ξ)
              - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
              - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)|)
          + (⨆ h, ENNReal.ofReal
            |Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h x ∂P)
              - Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h|) := by
    intro n ξ
    refine iSup_le fun h => ?_
    have hmi := master_identity P ψ θ₀ V n (fun i : Fin n => X i.val ξ)
      (θ_hat n (fun i : Fin n => X i.val ξ)) h
    have hVAS : Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
        = (Real.sqrt n
              * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
                  (fun i : Fin n => X i.val ξ)
            - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
          - (Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h x ∂P)
              - Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h) := by
      linarith [hmi]
    rw [hVAS]
    have htri : |(Real.sqrt n
              * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
                  (fun i : Fin n => X i.val ξ)
            - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
          - (Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h x ∂P)
              - Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h)|
        ≤ |Real.sqrt n
              * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
                  (fun i : Fin n => X i.val ξ)
            - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)|
          + |Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h x ∂P)
              - Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h| :=
      abs_sub _ _
    refine le_trans (ENNReal.ofReal_le_ofReal htri) ?_
    rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine add_le_add ?_ ?_
    · exact le_iSup (α := ℝ≥0∞) _ h
    · exact le_iSup (α := ℝ≥0∞) _ h
  have hA : IsBoundedInOuterProbSup μ (fun (n : ℕ) ξ h =>
      Real.sqrt n
          * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
              (fun i : Fin n => X i.val ξ)
        - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
        - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)) := by
    have hbd := OP_add_oP_sup (OP_add_oP_sup h_tight.neg h_est_eq) Rhat_oP.neg
    have heq : (fun (n : ℕ) ξ h =>
        Real.sqrt n
            * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
                (fun i : Fin n => X i.val ξ)
          - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
              - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
          - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
        = (fun (n : ℕ) (ξ : Ξ) (h : H) =>
            (-empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)
              + Real.sqrt n
                  * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
                      (fun i : Fin n => X i.val ξ))
            + -(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))) := by
      funext n ξ h; ring
    rw [heq]; exact hbd
  obtain ⟨_, Sfam_oP⟩ := rate_bootstrap_oP μ
    (fun (n : ℕ) ξ h => Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h)
    (fun (n : ℕ) ξ h =>
      Real.sqrt n
          * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
              (fun i : Fin n => X i.val ξ)
        - (empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
        - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
    (fun (n : ℕ) ξ h =>
      Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h x ∂P)
        - Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h)
    (fun (n : ℕ) ξ => Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖)
    (fun n ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    c hc_pos hlb hW hA hS
  -- ============ STEP 1c: assemble the three o_P pieces via `master_identity`. ============
  have hgoal_eq : (fun (n : ℕ) (ξ : Ξ) (h : H) =>
        Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h
          + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h))
      = (fun (n : ℕ) (ξ : Ξ) (h : H) =>
          (Real.sqrt n
                * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) n
                    (fun i : Fin n => X i.val ξ)
            + -(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)))
          + -(Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h x ∂P)
              - Real.sqrt n * V (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) h)) := by
    funext n ξ h
    rw [master_identity P ψ θ₀ V n (fun i : Fin n => X i.val ξ)
      (θ_hat n (fun i : Fin n => X i.val ξ)) h]
    ring
  rw [hgoal_eq]
  exact oP_sup_add (oP_sup_add h_est_eq Rhat_oP.neg) Sfam_oP.neg

end AsymptoticStatistics.EmpiricalProcess
