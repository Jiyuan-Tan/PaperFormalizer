module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterProbAsymptotics
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier

@[expose] public section

/-!
# Uniform Lemma 19.24 + `L²`-continuity tail inputs (vdV §19.4)

Concept layer (L1) for the infinite-dimensional Z-estimator (vdV Thm 19.26).
Provides:

* `uniform_donsker_random_function_consistency` — **THE novel core**: the
  sup-over-`H` (`ℓ∞(H)`) analog of the frozen single-pair engine
  `osc_modulus_to_random_pair` (`Donsker.lean:669`). From asymptotic
  equicontinuity of `𝓕` and an `L²(P)`-distance tail (in outer probability,
  `∃h` form), it concludes `‖𝔾ₙ(f̂_n) − 𝔾ₙ(ψ_{θ₀})‖_H →ₚ 0`, using the
  existential event formulation with `outerMeasureStar`.
* `sup_distL2_tendsto_zero_of_unif_L2_cont` — from the uniform `L²`-continuity
  clause `sup_h distL2(ψ_θ, ψ_{θ₀}) → 0` and consistency `θ̂_n →ₚ θ₀`, the
  sup-`L²`-distance of the plugged-in random function to `ψ_{θ₀}` is `o_P(1)`.
* `modifiedRandomFunction` (+ `_mem`, `_eq_on_good`, `_tail`) — the ball-cutoff
  `ψ̃ = if ‖θ̂ − θ₀‖ < δcls then ψ_{θ̂} else ψ_{θ₀}` keeping the random function
  inside `𝓕` unconditionally, needed to feed the uniform core.

Headline declarations: `uniform_donsker_random_function_consistency`,
`sup_distL2_tendsto_zero_of_unif_L2_cont`, `modifiedRandomFunction`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter
open scoped ENNReal Topology

/-- **The outer measure `P*` is dominated by the measure `μ` (all sets).**
`P*(A) ≤ μ A` for every `A` (measurable or not): for each measurable superset
`t ⊇ A`, the indicator `1_t` is a measurable majorant of `1_A`, so
`E*[1_A] ≤ ∫⁻ 1_t = μ t`; taking the infimum over measurable supersets of `A`
(`measure_eq_iInf`) gives `P*(A) ≤ μ A`. (Companion of `measure_le_outerMeasureStar`;
together they give `outerMeasureStar_eq_measure` for measurable sets, but this
direction needs no measurability of `A`.) -/
theorem outerMeasureStar_le_measure {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (A : Set Ξ) : μ.outerMeasureStar A ≤ μ A := by
  rw [measure_eq_iInf]
  refine le_iInf fun t => le_iInf fun hts => le_iInf fun ht => ?_
  rw [Measure.outerMeasureStar, outerExpectation]
  calc (⨅ U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U},
          ∫⁻ ω, (U : Ξ → ℝ≥0∞) ω ∂μ)
      ≤ ∫⁻ ω, t.indicator 1 ω ∂μ :=
        iInf_le (fun U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U} =>
          ∫⁻ ω, (U : Ξ → ℝ≥0∞) ω ∂μ) ⟨t.indicator 1, measurable_one.indicator ht, fun ω => ?_⟩
    _ = μ t := lintegral_indicator_one ht
  by_cases hω : ω ∈ A
  · simp only [Set.indicator_of_mem hω, Set.indicator_of_mem (hts hω), le_refl]
  · simp only [Set.indicator_of_notMem hω, zero_le]

/-- **Uniform Lemma 19.24 (the `ℓ∞(H)` novel core).**

Given asymptotic equicontinuity of `𝓕` (`h_equicont`), an iid sample, a random
family `fhat` valued in `𝓕`, a reference family `ψθ₀` valued in `𝓕`, and the
`L²(P)`-distance tail `distL2 P (fhat) (ψθ₀) →ₚ 0` in the sup-over-`H` outer
sense (`h_tail`), the empirical-process difference `𝔾ₙ(fhat) − 𝔾ₙ(ψθ₀)` tends to
`0` in outer probability uniformly over `H`.

For the sup-level analog of `osc_modulus_to_random_pair`, fix `ε`;
for every `η` apply equicontinuity to get `δ`; split the exceedance event as
`{∃h, ε < |D_h|} ⊆ Bₙ ∪ Tₙ` where `Bₙ` is the modulus bulk event
(`bulk_osc_mem` at each witnessing `h`) and `Tₙ := {∃h, δ ≤ distL2}` is the tail;
`outerMeasureStar_union_le` + `limsup_add_tendsto_zero_le`, tail `→ 0` from
`h_tail`. Needs only membership `fhat ∈ 𝓕`, not joint measurability. -/
theorem uniform_donsker_random_function_consistency
    {Ω : Type*} [MeasurableSpace Ω] {H : Type*}
    (𝓕 : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_equicont : IsAsymptoticallyEquicontinuous 𝓕 P)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (fhat : ℕ → Ξ → H → (Ω → ℝ))
    (h_range : ∀ n ξ h, fhat n ξ h ∈ 𝓕)
    (ψθ₀ : H → (Ω → ℝ))
    (h_ψ_range : ∀ h, ψθ₀ h ∈ 𝓕)
    (h_tail : TendstoZeroInOuterProbSup μ
      (fun n ξ h => distL2 P (fhat n ξ h) (ψθ₀ h))) :
    TendstoZeroInOuterProbSup μ (fun n ξ h =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ h)
        - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψθ₀ h)) := by
  simp only [TendstoZeroInOuterProbSup]
  intro ε hε
  set u : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar {ξ | ∃ h,
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ h)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψθ₀ h)|} with hu
  -- Reduce `Tendsto u → 0` to `∀ η > 0, limsup u ≤ ofReal η` (mirror Donsker.lean:696).
  suffices hlimsup : ∀ η : ℝ, 0 < η → limsup u atTop ≤ ENNReal.ofReal η by
    have hsup0 : limsup u atTop ≤ 0 := by
      refine ENNReal.le_of_forall_pos_le_add fun η hηpos _ => ?_
      rw [zero_add]
      have := hlimsup (η : ℝ) (by exact_mod_cast hηpos)
      rwa [ENNReal.ofReal_coe_nnreal] at this
    have hsup0' : limsup u atTop = 0 := le_antisymm hsup0 bot_le
    refine tendsto_of_le_liminf_of_limsup_le bot_le hsup0'.le ?_ ?_
    · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
    · exact isBoundedUnder_of ⟨0, fun _ => bot_le⟩
  -- Fix the mass `η`; equicontinuity at oscillation `ε`, mass `η` gives the radius `δ`.
  intro η hη
  obtain ⟨δ, hδpos, hBlimsup⟩ := h_equicont μ X hX_meas hX_indep hX_id hX_law ε η hε hη
  -- Bulk (modulus) event `Bev` and `L²`-tail event `Tev` (at radius `δ/2`).
  set Bev : ℕ → Set Ξ := fun n =>
    {ξ | ∃ s t : ↥𝓕, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|} with hBev
  set Tev : ℕ → Set Ξ := fun n =>
    {ξ | ∃ h, δ / 2 < |distL2 P (fhat n ξ h) (ψθ₀ h)|} with hTev
  clear_value Bev Tev
  -- Set-level split `{∃h, ε < |D_h|} ⊆ Bev n ∪ Tev n`.
  have hsplit : ∀ n, {ξ | ∃ h,
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (fhat n ξ h)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψθ₀ h)|} ⊆ Bev n ∪ Tev n := by
    intro n ξ hξ
    obtain ⟨h₀, hh₀⟩ := hξ
    rw [hBev, hTev]
    by_cases hcl : distL2 P (fhat n ξ h₀) (ψθ₀ h₀) < δ
    · exact Or.inl (bulk_osc_mem (h_range n ξ h₀) (h_ψ_range h₀) hcl hh₀)
    · refine Or.inr ⟨h₀, ?_⟩
      rw [not_lt] at hcl
      have hnn : (0 : ℝ) ≤ distL2 P (fhat n ξ h₀) (ψθ₀ h₀) := by
        unfold distL2; exact ENNReal.toReal_nonneg
      rw [abs_of_nonneg hnn]
      linarith [half_lt_self hδpos]
  -- Opaque envelopes `Uf = P* ∘ Bev`, `Vf = P* ∘ Tev`.
  set Uf : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar (Bev n) with hUf
  set Vf : ℕ → ℝ≥0∞ := fun n => μ.outerMeasureStar (Tev n) with hVf
  have hbound : ∀ n, u n ≤ Uf n + Vf n := by
    intro n
    rw [hUf, hVf]
    calc u n ≤ μ.outerMeasureStar (Bev n ∪ Tev n) := outerMeasureStar_mono μ (hsplit n)
      _ ≤ μ.outerMeasureStar (Bev n) + μ.outerMeasureStar (Tev n) :=
          outerMeasureStar_union_le μ _ _
  -- Tail vanishes (from `h_tail` at `δ/2`); bulk `limsup ≤ ofReal η` (equicontinuity).
  have hVf0 : Tendsto Vf atTop (𝓝 0) := by
    rw [hVf]; simp only [hTev]; exact h_tail (δ / 2) (half_pos hδpos)
  have hBlimsup' : limsup Uf atTop ≤ ENNReal.ofReal η := by
    rw [hUf]; simp only [hBev]; exact hBlimsup
  clear_value u Uf Vf
  calc limsup u atTop
      ≤ limsup (fun n => Uf n + Vf n) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound)
          isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal η := limsup_add_tendsto_zero_le Uf Vf _ hBlimsup' hVf0

/-- **Uniform `L²`-continuity of the plug-in random function.**

From the uniform `L²`-continuity clause `unif_L2_cont`
(`sup_h distL2(ψ_θ, ψ_{θ₀}) ≤ ε` for `‖θ − θ₀‖ < δ`) and consistency
`θ̂_n →ₚ θ₀` (`h_consist`), the sup-`L²`-distance of `ψ_{θ̂_n}` to `ψ_{θ₀}` is
`o_P(1)`.

Proof: fix `ε`; `unif_L2_cont` gives `δ`; the exceedance event
`{∃h, ε < distL2(ψ_{θ̂_n}, ψ_{θ₀})}` is contained in the measurable event
`{δ ≤ ‖θ̂_n − θ₀‖}` (by contraposition through `lt_iSup_iff`, D9); lift with
`measure_le_outerMeasureStar` and apply `h_consist`. -/
theorem sup_distL2_tendsto_zero_of_unif_L2_cont
    {Ω : Type*} [MeasurableSpace Ω]
    {B : Type*} [NormedAddCommGroup B] {H : Type*}
    (P : Measure Ω) (ψ : B → H → (Ω → ℝ)) (θ₀ : B)
    (unif_L2_cont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ θ : B, ‖θ - θ₀‖ < δ →
      (⨆ h, ENNReal.ofReal (distL2 P (ψ θ h) (ψ θ₀ h))) ≤ ENNReal.ofReal ε)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (θ_hat : ∀ n, (Fin n → Ω) → B) (X : ℕ → Ξ → Ω)
    (h_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0)) :
    TendstoZeroInOuterProbSup μ (fun n ξ h =>
      distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) (ψ θ₀ h)) := by
  simp only [TendstoZeroInOuterProbSup]
  intro ε hε
  -- Radius `δ` from the uniform `L²`-continuity clause.
  obtain ⟨δ, hδpos, hbd⟩ := unif_L2_cont ε hε
  -- The measurable superset event at half the radius (`h_consist` provides its mass).
  set S' : ℕ → Set Ξ := fun n =>
    {ξ | δ / 2 < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hS'
  -- Inclusion: the exceedance event lands in `S'` (contrapositive through `le_iSup`).
  have hsub : ∀ n,
      {ξ | ∃ h, ε < |distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) (ψ θ₀ h)|} ⊆ S' n := by
    intro n ξ hξ
    obtain ⟨h₀, hh₀⟩ := hξ
    simp only [hS', Set.mem_setOf_eq]
    by_contra hcon
    rw [not_lt] at hcon
    have hlt : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δ :=
      lt_of_le_of_lt hcon (half_lt_self hδpos)
    have hnn : (0 : ℝ) ≤ distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h₀) (ψ θ₀ h₀) := by
      unfold distL2; exact ENNReal.toReal_nonneg
    rw [abs_of_nonneg hnn] at hh₀
    have hle : ENNReal.ofReal
        (distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h₀) (ψ θ₀ h₀))
          ≤ ENNReal.ofReal ε :=
      le_trans (le_iSup (fun h =>
        ENNReal.ofReal (distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) (ψ θ₀ h))) h₀)
        (hbd _ hlt)
    exact absurd hh₀ (not_lt.2 ((ENNReal.ofReal_le_ofReal_iff hε.le).1 hle))
  -- Squeeze `P*(exceedance) ≤ μ(S') → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h_consist (δ / 2) (half_pos hδpos)) (Eventually.of_forall fun n => zero_le)
    (Eventually.of_forall fun n => ?_)
  calc μ.outerMeasureStar
        {ξ | ∃ h, ε < |distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) (ψ θ₀ h)|}
      ≤ μ.outerMeasureStar (S' n) := outerMeasureStar_mono μ (hsub n)
    _ ≤ μ (S' n) := outerMeasureStar_le_measure μ (S' n)

/-- **Ball-cutoff modified random function** (vdV §19.4 modified-function trick).

`modifiedRandomFunction ψ θ₀ δcls θ_hat X n ξ h` equals `ψ_{θ̂_n(ξ), h}` when the
realized estimator lies in the class ball `‖θ̂_n(ξ) − θ₀‖ < δcls`, and falls back
to `ψ_{θ₀, h}` otherwise. The cutoff guarantees the value is always in `𝓕`
(both branches), which is what the uniform core needs; on the good event
`{‖θ̂_n − θ₀‖ < δcls}` (probability `→ 1` by consistency) it agrees with the
genuine plug-in function.

Edge: on the bad event `{δcls ≤ ‖θ̂_n − θ₀‖}` the value is `ψ_{θ₀}`, so its
`distL2` to `ψ_{θ₀}` is `0`. -/
noncomputable def modifiedRandomFunction
    {Ω : Type*} {B : Type*} [NormedAddCommGroup B] {H : Type*} {Ξ : Type*}
    (ψ : B → H → (Ω → ℝ)) (θ₀ : B) (δcls : ℝ)
    (θ_hat : ∀ n, (Fin n → Ω) → B) (X : ℕ → Ξ → Ω) :
    ℕ → Ξ → H → (Ω → ℝ) :=
  fun n ξ h =>
    if ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls then
      ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h
    else ψ θ₀ h

/-- **The modified random function stays in `𝓕`.** Both branches land in `𝓕`:
the in-ball branch via `hclass_mem` (the guard `‖θ̂ − θ₀‖ < δcls` supplies the
hypothesis), the fallback branch via `hθ₀_mem`. -/
theorem modifiedRandomFunction_mem
    {Ω : Type*} {B : Type*} [NormedAddCommGroup B] {H : Type*} {Ξ : Type*}
    (ψ : B → H → (Ω → ℝ)) (θ₀ : B) (δcls : ℝ)
    (θ_hat : ∀ n, (Fin n → Ω) → B) (X : ℕ → Ξ → Ω)
    (𝓕 : Set (Ω → ℝ))
    (hclass_mem : ∀ θ : B, ‖θ - θ₀‖ < δcls → ∀ h, ψ θ h ∈ 𝓕)
    (hθ₀_mem : ∀ h, ψ θ₀ h ∈ 𝓕) :
    ∀ n ξ h, modifiedRandomFunction ψ θ₀ δcls θ_hat X n ξ h ∈ 𝓕 := by
  intro n ξ h
  unfold modifiedRandomFunction
  split_ifs with hg
  · exact hclass_mem _ hg h
  · exact hθ₀_mem h

/-- **The modified random function agrees with the plug-in on the good event.**
On `{‖θ̂_n(ξ) − θ₀‖ < δcls}` the cutoff selects the in-ball branch, so
`modifiedRandomFunction … = ψ_{θ̂_n(ξ), h}` (`if_pos`). -/
theorem modifiedRandomFunction_eq_on_good
    {Ω : Type*} {B : Type*} [NormedAddCommGroup B] {H : Type*} {Ξ : Type*}
    (ψ : B → H → (Ω → ℝ)) (θ₀ : B) (δcls : ℝ)
    (θ_hat : ∀ n, (Fin n → Ω) → B) (X : ℕ → Ξ → Ω) :
    ∀ n ξ h, ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls →
      modifiedRandomFunction ψ θ₀ δcls θ_hat X n ξ h
        = ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h := by
  intro n ξ h hgood
  unfold modifiedRandomFunction
  rw [if_pos hgood]

/-- **The modified random function has an `L²`-tail `o_P(1)`.**

Combining the plug-in `L²`-continuity `h_sup_distL2` (on the good event the
modified function equals `ψ_{θ̂_n}`, whose `distL2` to `ψ_{θ₀}` is `o_P(1)`) with
the vanishing bad-event mass `h_bad` (`μ{δcls ≤ ‖θ̂_n − θ₀‖} → 0`, from
consistency), the `distL2` of the modified function to `ψ_{θ₀}` is `o_P(1)` in
the sup-over-`H` outer sense. This is exactly the `h_tail` input of
`uniform_donsker_random_function_consistency`. -/
theorem modifiedRandomFunction_tail
    {Ω : Type*} [MeasurableSpace Ω]
    {B : Type*} [NormedAddCommGroup B] {H : Type*} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ω) (ψ : B → H → (Ω → ℝ)) (θ₀ : B) (δcls : ℝ)
    (θ_hat : ∀ n, (Fin n → Ω) → B) (μ : Measure Ξ) (X : ℕ → Ξ → Ω)
    (h_sup_distL2 : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) (ψ θ₀ h)))
    (h_bad : Tendsto (fun n =>
      μ {ξ | δcls ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0)) :
    TendstoZeroInOuterProbSup μ (fun n ξ h =>
      distL2 P (modifiedRandomFunction ψ θ₀ δcls θ_hat X n ξ h) (ψ θ₀ h)) := by
  simp only [TendstoZeroInOuterProbSup]
  intro ε hε
  -- Plug-in exceedance event `A'` and bad-event `Bbad` (cutoff missed the ball).
  set A' : ℕ → Set Ξ := fun n =>
    {ξ | ∃ h, ε < |distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) h) (ψ θ₀ h)|} with hA'
  set Bbad : ℕ → Set Ξ := fun n =>
    {ξ | δcls ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hBbad
  -- On the good event the modified function is the plug-in one; else in `Bbad`.
  have hsub : ∀ n, {ξ | ∃ h,
      ε < |distL2 P (modifiedRandomFunction ψ θ₀ δcls θ_hat X n ξ h) (ψ θ₀ h)|} ⊆
        A' n ∪ Bbad n := by
    intro n ξ hξ
    obtain ⟨h₀, hh₀⟩ := hξ
    rw [hA', hBbad]
    by_cases hg : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls
    · refine Or.inl ⟨h₀, ?_⟩
      rw [modifiedRandomFunction_eq_on_good ψ θ₀ δcls θ_hat X n ξ h₀ hg] at hh₀
      exact hh₀
    · exact Or.inr (le_of_not_gt hg)
  -- Plug-in tail `→ 0` (from `h_sup_distL2`); bad-event outer mass `→ 0` (from `h_bad`).
  have hA0 : Tendsto (fun n => μ.outerMeasureStar (A' n)) atTop (𝓝 0) := by
    simp only [hA']; exact h_sup_distL2 ε hε
  have hB0 : Tendsto (fun n => μ.outerMeasureStar (Bbad n)) atTop (𝓝 0) := by
    have hbad' : Tendsto (fun n => μ (Bbad n)) atTop (𝓝 0) := h_bad
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad'
      (Eventually.of_forall fun n => zero_le)
      (Eventually.of_forall fun n => outerMeasureStar_le_measure μ (Bbad n))
  have hsum : Tendsto (fun n => μ.outerMeasureStar (A' n) + μ.outerMeasureStar (Bbad n))
      atTop (𝓝 0) := by simpa using hA0.add hB0
  -- Final squeeze via subadditivity.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  calc μ.outerMeasureStar
        {ξ | ∃ h, ε < |distL2 P (modifiedRandomFunction ψ θ₀ δcls θ_hat X n ξ h) (ψ θ₀ h)|}
      ≤ μ.outerMeasureStar (A' n ∪ Bbad n) := outerMeasureStar_mono μ (hsub n)
    _ ≤ μ.outerMeasureStar (A' n) + μ.outerMeasureStar (Bbad n) :=
        outerMeasureStar_union_le μ _ _

/-! ### Guarded random functions and metric-space `L²` continuity

Nuisance siblings of `modifiedRandomFunction` and
`sup_distL2_tendsto_zero_of_unif_L2_cont`. The guard is an abstract predicate
`good n ξ` (in the nuisance proof: `θ̂ ∈ ball ∧ η̂ ∈ ball`), and the consistency /
`L²`-continuity are stated over a metric-space index `T` (the nuisance lives in a
metric space `H`). -/

open Classical in
/-- **Guard-cutoff random function** (vdV §5.4 nuisance modified-function trick).
Equals `fhat n ξ h` on the good event `good n ξ` and falls back to the reference
`ψθ₀ h` otherwise. Generalizes `modifiedRandomFunction` from the ball-membership
guard `‖θ̂ − θ₀‖ < δcls` to an arbitrary predicate `good : ℕ → Ξ → Prop` (needed
because the nuisance good event is a conjunction `θ̂ ∈ ball ∧ η̂ ∈ ball`).
`noncomputable` via `Classical.propDecidable` on the guard.

Edge: off the good event the value is `ψθ₀ h`, so its `distL2` to `ψθ₀` is `0`. -/
noncomputable def guardedRandomFunction
    {Ω : Type*} {H : Type*} {Ξ : Type*}
    (good : ℕ → Ξ → Prop) (fhat : ℕ → Ξ → H → (Ω → ℝ)) (ψθ₀ : H → (Ω → ℝ)) :
    ℕ → Ξ → H → (Ω → ℝ) :=
  fun n ξ h => if good n ξ then fhat n ξ h else ψθ₀ h

/-- **The guarded random function stays in `𝓕`.** On the good event it is `fhat`
(`hfhat_mem` supplies membership there); off it, `ψθ₀ ∈ 𝓕` (`hθ₀_mem`). Mirror of
`modifiedRandomFunction_mem`. -/
theorem guardedRandomFunction_mem
    {Ω : Type*} {H : Type*} {Ξ : Type*}
    (good : ℕ → Ξ → Prop) (fhat : ℕ → Ξ → H → (Ω → ℝ)) (ψθ₀ : H → (Ω → ℝ))
    (𝓕 : Set (Ω → ℝ))
    (hfhat_mem : ∀ n ξ, good n ξ → ∀ h, fhat n ξ h ∈ 𝓕)
    (hθ₀_mem : ∀ h, ψθ₀ h ∈ 𝓕) :
    ∀ n ξ h, guardedRandomFunction good fhat ψθ₀ n ξ h ∈ 𝓕 := by
  intro n ξ h
  simp only [guardedRandomFunction]
  split_ifs with hg
  · exact hfhat_mem n ξ hg h
  · exact hθ₀_mem h

/-- **The guarded random function agrees with `fhat` on the good event.**
`if_pos` on the guard `good n ξ`. Mirror of `modifiedRandomFunction_eq_on_good`. -/
theorem guardedRandomFunction_eq_on_good
    {Ω : Type*} {H : Type*} {Ξ : Type*}
    (good : ℕ → Ξ → Prop) (fhat : ℕ → Ξ → H → (Ω → ℝ)) (ψθ₀ : H → (Ω → ℝ)) :
    ∀ n ξ h, good n ξ →
      guardedRandomFunction good fhat ψθ₀ n ξ h = fhat n ξ h := by
  intro n ξ h hg
  simp only [guardedRandomFunction, if_pos hg]

/-- **The guarded random function has an `L²`-tail `o_P(1)`.** On the good event
it equals `fhat` (whose `distL2` to `ψθ₀` is `o_P(1)`, `h_sup_distL2`); the bad
event `{ξ | ¬ good n ξ}` has vanishing mass (`h_bad`). Mirror of
`modifiedRandomFunction_tail`; this is the `h_tail` input of
`uniform_donsker_random_function_consistency` in the nuisance core. -/
theorem guardedRandomFunction_tail
    {Ω : Type*} [MeasurableSpace Ω] {H : Type*} {Ξ : Type*} [MeasurableSpace Ξ]
    (P : Measure Ω) (good : ℕ → Ξ → Prop) (fhat : ℕ → Ξ → H → (Ω → ℝ))
    (ψθ₀ : H → (Ω → ℝ)) (μ : Measure Ξ)
    (h_sup_distL2 : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      distL2 P (fhat n ξ h) (ψθ₀ h)))
    (h_bad : Tendsto (fun n => μ {ξ | ¬ good n ξ}) atTop (𝓝 0)) :
    TendstoZeroInOuterProbSup μ (fun n ξ h =>
      distL2 P (guardedRandomFunction good fhat ψθ₀ n ξ h) (ψθ₀ h)) := by
  simp only [TendstoZeroInOuterProbSup]
  intro ε hε
  -- Plug-in exceedance event `A'` and bad-event `Bbad` (guard missed).
  set A' : ℕ → Set Ξ := fun n =>
    {ξ | ∃ h, ε < |distL2 P (fhat n ξ h) (ψθ₀ h)|} with hA'
  set Bbad : ℕ → Set Ξ := fun n => {ξ | ¬ good n ξ} with hBbad
  -- On the good event the guarded function is `fhat`; else in `Bbad`.
  have hsub : ∀ n, {ξ | ∃ h,
      ε < |distL2 P (guardedRandomFunction good fhat ψθ₀ n ξ h) (ψθ₀ h)|} ⊆
        A' n ∪ Bbad n := by
    intro n ξ hξ
    obtain ⟨h₀, hh₀⟩ := hξ
    rw [hA', hBbad]
    by_cases hg : good n ξ
    · refine Or.inl ⟨h₀, ?_⟩
      rw [guardedRandomFunction_eq_on_good good fhat ψθ₀ n ξ h₀ hg] at hh₀
      exact hh₀
    · exact Or.inr hg
  -- Plug-in tail `→ 0` (from `h_sup_distL2`); bad-event outer mass `→ 0` (from `h_bad`).
  have hA0 : Tendsto (fun n => μ.outerMeasureStar (A' n)) atTop (𝓝 0) := by
    simp only [hA']; exact h_sup_distL2 ε hε
  have hB0 : Tendsto (fun n => μ.outerMeasureStar (Bbad n)) atTop (𝓝 0) := by
    have hbad' : Tendsto (fun n => μ (Bbad n)) atTop (𝓝 0) := h_bad
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad'
      (Eventually.of_forall fun n => zero_le)
      (Eventually.of_forall fun n => outerMeasureStar_le_measure μ (Bbad n))
  have hsum : Tendsto (fun n => μ.outerMeasureStar (A' n) + μ.outerMeasureStar (Bbad n))
      atTop (𝓝 0) := by simpa using hA0.add hB0
  -- Final squeeze via subadditivity.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  calc μ.outerMeasureStar
        {ξ | ∃ h, ε < |distL2 P (guardedRandomFunction good fhat ψθ₀ n ξ h) (ψθ₀ h)|}
      ≤ μ.outerMeasureStar (A' n ∪ Bbad n) := outerMeasureStar_mono μ (hsub n)
    _ ≤ μ.outerMeasureStar (A' n) + μ.outerMeasureStar (Bbad n) :=
        outerMeasureStar_union_le μ _ _

/-- **Uniform `L²`-continuity of the plug-in random function (metric index).**
Metric-space generalization of `sup_distL2_tendsto_zero_of_unif_L2_cont`: the
parameter index `T` carries a `MetricSpace` (the nuisance space), the
`L²`-continuity clause uses `dist t t₀ < δ`, and consistency `t̂_n →ₚ t₀` is in
`dist`. Feeds the `h_tail` input for the nuisance direction of the N8 core. -/
theorem sup_distL2_tendsto_zero_of_unif_L2_cont_metric
    {Ω : Type*} [MeasurableSpace Ω]
    {T : Type*} [MetricSpace T] {H : Type*}
    (P : Measure Ω) (ψ : T → H → (Ω → ℝ)) (t₀ : T)
    (unif_L2_cont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : T, dist t t₀ < δ →
      (⨆ h, ENNReal.ofReal (distL2 P (ψ t h) (ψ t₀ h))) ≤ ENNReal.ofReal ε)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (t_hat : ∀ n, (Fin n → Ω) → T) (X : ℕ → Ξ → Ω)
    (h_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < dist (t_hat n (fun i : Fin n => X i.val ξ)) t₀}) atTop (𝓝 0)) :
    TendstoZeroInOuterProbSup μ (fun n ξ h =>
      distL2 P (ψ (t_hat n (fun i : Fin n => X i.val ξ)) h) (ψ t₀ h)) := by
  simp only [TendstoZeroInOuterProbSup]
  intro ε hε
  -- Radius `δ` from the uniform `L²`-continuity clause.
  obtain ⟨δ, hδpos, hbd⟩ := unif_L2_cont ε hε
  -- The measurable superset event at half the radius (`h_consist` provides its mass).
  set S' : ℕ → Set Ξ := fun n =>
    {ξ | δ / 2 < dist (t_hat n (fun i : Fin n => X i.val ξ)) t₀} with hS'
  -- Inclusion: the exceedance event lands in `S'` (contrapositive through `le_iSup`).
  have hsub : ∀ n,
      {ξ | ∃ h, ε < |distL2 P (ψ (t_hat n (fun i : Fin n => X i.val ξ)) h) (ψ t₀ h)|} ⊆ S' n := by
    intro n ξ hξ
    obtain ⟨h₀, hh₀⟩ := hξ
    simp only [hS', Set.mem_setOf_eq]
    by_contra hcon
    rw [not_lt] at hcon
    have hlt : dist (t_hat n (fun i : Fin n => X i.val ξ)) t₀ < δ :=
      lt_of_le_of_lt hcon (half_lt_self hδpos)
    have hnn : (0 : ℝ) ≤ distL2 P (ψ (t_hat n (fun i : Fin n => X i.val ξ)) h₀) (ψ t₀ h₀) := by
      unfold distL2; exact ENNReal.toReal_nonneg
    rw [abs_of_nonneg hnn] at hh₀
    have hle : ENNReal.ofReal
        (distL2 P (ψ (t_hat n (fun i : Fin n => X i.val ξ)) h₀) (ψ t₀ h₀))
          ≤ ENNReal.ofReal ε :=
      le_trans (le_iSup (fun h =>
        ENNReal.ofReal (distL2 P (ψ (t_hat n (fun i : Fin n => X i.val ξ)) h) (ψ t₀ h))) h₀)
        (hbd _ hlt)
    exact absurd hh₀ (not_lt.2 ((ENNReal.ofReal_le_ofReal_iff hε.le).1 hle))
  -- Squeeze `P*(exceedance) ≤ μ(S') → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h_consist (δ / 2) (half_pos hδpos)) (Eventually.of_forall fun n => zero_le)
    (Eventually.of_forall fun n => ?_)
  calc μ.outerMeasureStar
        {ξ | ∃ h, ε < |distL2 P (ψ (t_hat n (fun i : Fin n => X i.val ξ)) h) (ψ t₀ h)|}
      ≤ μ.outerMeasureStar (S' n) := outerMeasureStar_mono μ (hsub n)
    _ ≤ μ (S' n) := outerMeasureStar_le_measure μ (S' n)

end AsymptoticStatistics.EmpiricalProcess
