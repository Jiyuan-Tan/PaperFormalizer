module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker

@[expose] public section

/-!
# Outer-probability `o_P` / `O_P` for sup-over-`H` random families

This file provides outer-probability asymptotic predicates for the
infinite-dimensional Z-estimator, vdV §19.4
Theorem 19.26 (`infinite_dim_z_estimator`). The conclusion of 19.26 is a
statement about convergence in the sup norm `‖·‖_H = sup over H` of an
`ℓ∞(H)`-valued sequence, "in outer probability". We encode `ℓ∞(H)` as a plain
family `g : ℕ → Ξ → H → ℝ` and model the two
outer-probability modes:

* `‖g_n‖_H →ₚ 0` (little-`o_P`), via `TendstoZeroInOuterProbSup`;
* `‖g_n‖_H = O_P(1)` (bounded in probability), via `IsBoundedInOuterProbSup`.

Both are stated with the **existential** event `{ξ | ∃ h, ε < |g n ξ h|}` rather
than `{ξ | ε < sSup_h |g n ξ h|}`: the `∃h` form needs no `BddAbove` /
`ciSup` side condition and matches the shape of the
`IsAsymptoticallyEquicontinuous` predicate. Mass is measured with the outer
measure `Measure.outerMeasureStar` (the sup / ∃ over uncountable `H` is generally
not `μ`-measurable).

The algebra proofs use the outer-measure lemmas `outerMeasureStar_mono` and
`outerMeasureStar_union_le` from `Donsker.lean`.

Principal declarations: `TendstoZeroInOuterProbSup`, `IsBoundedInOuterProbSup`,
`oP_sup_add`, `oP_sup_mono`, `OP_add_oP_sup`, `rate_bootstrap_oP`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter
open scoped ENNReal Topology

/-- **Little-`o_P` in the `ℓ∞(H)` sup norm (outer probability).**
`‖g_n‖_H = sup_h |g_n(·,h)| →ₚ 0`: for every threshold `ε > 0` the outer measure
of the existential exceedance event `{ξ | ∃ h, ε < |g n ξ h|}` tends to `0`.

Edge: if `H` is empty the event is empty for all `ε`, so the predicate holds
vacuously (its `outerMeasureStar` is `0`). vdV §19.4 (conclusion of Thm 19.26,
`+ o_P(1)` in `ℓ∞(H)`). -/
def TendstoZeroInOuterProbSup {Ξ H : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (g : ℕ → Ξ → H → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ.outerMeasureStar {ξ | ∃ h, ε < |g n ξ h|}) atTop (𝓝 0)

/-- **Bounded in outer probability in the `ℓ∞(H)` sup norm (`O_P(1)`).**
`‖g_n‖_H = O_P(1)`: for every `η > 0` there is a level `M` such that the `limsup`
of the outer measure of `{ξ | ∃ h, M < |g n ξ h|}` is at most `η`.

Edge: if `H` is empty every exceedance event is empty, so any `M` works.
vdV §19.4 (marginal asymptotic tightness of the empirical process over the class,
used in the rate bootstrap, step 5 of the 5.21-style proof). -/
def IsBoundedInOuterProbSup {Ξ H : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (g : ℕ → Ξ → H → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ,
    limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, M < |g n ξ h|}) atTop
      ≤ ENNReal.ofReal η

/-- **Scalar little-`o_P` (outer probability).** The `H`-free specialization of
`TendstoZeroInOuterProbSup` for a scalar random sequence `g : ℕ → Ξ → ℝ`
(the estimation rate `r_n := √n‖θ̂_n − θ₀‖` lives here). Since the event
`{ξ | ε < |g n ξ|}` carries no `∃h`, it is `μ`-measurable when `g n` is
measurable; the outer measure is used uniformly with the sup version. -/
def TendstoZeroInOuterProbScalar {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (g : ℕ → Ξ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ.outerMeasureStar {ξ | ε < |g n ξ|}) atTop (𝓝 0)

/-- **Scalar bounded in outer probability (`O_P(1)`).** The `H`-free
specialization of `IsBoundedInOuterProbSup`. The conclusion `r_n = O_P(1)` of the
rate bootstrap (step 5) is stated with this predicate on the scalar rate
`r_n := √n‖θ̂_n − θ₀‖`. -/
def IsBoundedInOuterProbScalar {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (g : ℕ → Ξ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ,
    limsup (fun n => μ.outerMeasureStar {ξ | M < |g n ξ|}) atTop
      ≤ ENNReal.ofReal η

/-- **Squeeze from `limsup`-bounds to `Tendsto`.** A nonnegative `ℝ≥0∞` sequence
whose `limsup` is `≤ ENNReal.ofReal ε` for *every* `ε > 0` tends to `0`. Mirror of
the closing idiom of `osc_modulus_to_random_pair` (`Donsker.lean`). -/
private theorem tendsto_zero_of_limsup_le_ofReal (u : ℕ → ℝ≥0∞)
    (h : ∀ ε : ℝ, 0 < ε → limsup u atTop ≤ ENNReal.ofReal ε) :
    Tendsto u atTop (𝓝 0) := by
  have hsup0 : limsup u atTop ≤ 0 := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hεpos _ => ?_
    rw [zero_add]
    have := h (ε : ℝ) (by exact_mod_cast hεpos)
    rwa [ENNReal.ofReal_coe_nnreal] at this
  have hsup0' : limsup u atTop = 0 := le_antisymm hsup0 bot_le
  refine tendsto_of_le_liminf_of_limsup_le bot_le hsup0'.le ?_ ?_
  · exact isBoundedUnder_of ⟨⊤, fun _ => le_top⟩
  · exact isBoundedUnder_of ⟨0, fun _ => bot_le⟩

/-- **`o_P` is closed under addition (sup form).** If `g₁ →ₚ 0` and `g₂ →ₚ 0`
in the `ℓ∞(H)` sup norm, so does their pointwise sum.

Outline: `{ξ | ∃h, ε < |g₁+g₂|} ⊆ {ξ | ∃h, ε/2 < |g₁|} ∪ {ξ | ∃h, ε/2 < |g₂|}`
(triangle inequality); close via `outerMeasureStar_mono` +
`outerMeasureStar_union_le`; the sum of two `→ 0` sequences `→ 0`. -/
theorem oP_sup_add {Ξ H : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    {g₁ g₂ : ℕ → Ξ → H → ℝ}
    (h₁ : TendstoZeroInOuterProbSup μ g₁) (h₂ : TendstoZeroInOuterProbSup μ g₂) :
    TendstoZeroInOuterProbSup μ (fun n ξ h => g₁ n ξ h + g₂ n ξ h) := by
  intro ε hε
  have hsub : ∀ n, {ξ | ∃ h, ε < |g₁ n ξ h + g₂ n ξ h|}
      ⊆ {ξ | ∃ h, ε / 2 < |g₁ n ξ h|} ∪ {ξ | ∃ h, ε / 2 < |g₂ n ξ h|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    have htri : ε < |g₁ n ξ h| + |g₂ n ξ h| := lt_of_lt_of_le hh (abs_add_le _ _)
    by_cases h1 : ε / 2 < |g₁ n ξ h|
    · exact Or.inl ⟨h, h1⟩
    · push_neg at h1
      exact Or.inr ⟨h, by linarith⟩
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, ε < |g₁ n ξ h + g₂ n ξ h|}
      ≤ μ.outerMeasureStar {ξ | ∃ h, ε / 2 < |g₁ n ξ h|}
        + μ.outerMeasureStar {ξ | ∃ h, ε / 2 < |g₂ n ξ h|} :=
    fun n => le_trans (outerMeasureStar_mono μ (hsub n)) (outerMeasureStar_union_le μ _ _)
  have hsum : Tendsto (fun n => μ.outerMeasureStar {ξ | ∃ h, ε / 2 < |g₁ n ξ h|}
      + μ.outerMeasureStar {ξ | ∃ h, ε / 2 < |g₂ n ξ h|}) atTop (𝓝 0) := by
    have := (h₁ (ε / 2) (by linarith)).add (h₂ (ε / 2) (by linarith))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall hb)

/-- **`o_P` monotonicity (sup form).** A pointwise-dominated family inherits the
`→ₚ 0` of its dominator: if `|g| ≤ |g'|` everywhere and `g' →ₚ 0`, then `g →ₚ 0`.

Outline: `{ξ | ∃h, ε < |g|} ⊆ {ξ | ∃h, ε < |g'|}` (the same `h` witnesses via
`|g n ξ h| ≤ |g' n ξ h|`); close via `outerMeasureStar_mono` + squeeze. -/
theorem oP_sup_mono {Ξ H : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    {g g' : ℕ → Ξ → H → ℝ}
    (hle : ∀ n ξ h, |g n ξ h| ≤ |g' n ξ h|)
    (h' : TendstoZeroInOuterProbSup μ g') :
    TendstoZeroInOuterProbSup μ g := by
  intro ε hε
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, ε < |g n ξ h|}
      ≤ μ.outerMeasureStar {ξ | ∃ h, ε < |g' n ξ h|} := by
    intro n
    refine outerMeasureStar_mono μ ?_
    intro ξ hξ
    obtain ⟨h, hh⟩ := hξ
    exact ⟨h, lt_of_lt_of_le hh (hle n ξ h)⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h' ε hε)
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall hb)

/-- **`O_P(1) + o_P(1) = O_P(1)` (sup form).** A bounded-in-probability family
plus an `o_P(1)` family stays bounded in probability.

Outline: given `η`, take `M` for `a` at mass `η`; then
`{ξ | ∃h, M+ε < |a+s|} ⊆ {ξ | ∃h, M < |a|} ∪ {ξ | ∃h, ε < |s|}`; `limsup ≤ η + 0`
via `outerMeasureStar_union_le` + `limsup_add_tendsto_zero_le`. -/
theorem OP_add_oP_sup {Ξ H : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    {a s : ℕ → Ξ → H → ℝ}
    (ha : IsBoundedInOuterProbSup μ a) (hs : TendstoZeroInOuterProbSup μ s) :
    IsBoundedInOuterProbSup μ (fun n ξ h => a n ξ h + s n ξ h) := by
  intro η hη
  obtain ⟨M, hM⟩ := ha η hη
  refine ⟨M + 1, ?_⟩
  have hsub : ∀ n, {ξ | ∃ h, M + 1 < |a n ξ h + s n ξ h|}
      ⊆ {ξ | ∃ h, M < |a n ξ h|} ∪ {ξ | ∃ h, (1 : ℝ) < |s n ξ h|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    have htri : M + 1 < |a n ξ h| + |s n ξ h| := lt_of_lt_of_le hh (abs_add_le _ _)
    by_cases h1 : M < |a n ξ h|
    · exact Or.inl ⟨h, h1⟩
    · push_neg at h1
      exact Or.inr ⟨h, by linarith⟩
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, M + 1 < |a n ξ h + s n ξ h|}
      ≤ μ.outerMeasureStar {ξ | ∃ h, M < |a n ξ h|}
        + μ.outerMeasureStar {ξ | ∃ h, (1 : ℝ) < |s n ξ h|} :=
    fun n => le_trans (outerMeasureStar_mono μ (hsub n)) (outerMeasureStar_union_le μ _ _)
  calc limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, M + 1 < |a n ξ h + s n ξ h|}) atTop
      ≤ limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, M < |a n ξ h|}
          + μ.outerMeasureStar {ξ | ∃ h, (1 : ℝ) < |s n ξ h|}) atTop :=
        limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal η := limsup_add_tendsto_zero_le _ _ _ hM (hs 1 one_pos)

/-- **Rate bootstrap (step 5 of the vdV 5.21-style proof of Thm 19.26).**

Let `r_n ≥ 0` be a scalar rate. Suppose a family `Vfam` is bounded
below by `c · r_n` in the `ℓ∞(H)` sup (`hlb`), decomposes as `Vfam ≤ Afam + Sfam`
in the sup (`hW`) with `Afam = O_P(1)` (`hA`) and `Sfam` controlled by `ε · r_n`
in outer probability for every `ε > 0` (`hS`). Then the rate is bounded in
probability (`r_n = O_P(1)`) **and** `Sfam →ₚ 0` in the sup norm.

The argument is self-referential in `r_n`: from `c·r_n ≤ ‖Afam‖ + ‖Sfam‖ ≤
O_P(1) + ε·r_n` one gets `(c − ε)·r_n ≤ O_P(1)`, hence `r_n = O_P(1)`; then
`‖Sfam‖ ≤ ε·r_n = ε·O_P(1)` for arbitrary `ε`, giving `Sfam →ₚ 0`.

The deterministic sups `⨆ h, ENNReal.ofReal |·|` are bridged to the `∃h`-events
of `hA` / the conclusion via `lt_iSup_iff`. All event comparisons use
`outerMeasureStar`, so no measurability premise on `r_n` is required.

The self-referential argument is carried out directly with `ℝ≥0∞` `limsup`
and outer-measure event comparisons. -/
theorem rate_bootstrap_oP {Ξ H : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (Vfam Afam Sfam : ℕ → Ξ → H → ℝ) (r : ℕ → Ξ → ℝ)
    (hr_nonneg : ∀ n ξ, 0 ≤ r n ξ)
    (c : ℝ) (hc : 0 < c)
    (hlb : ∀ n ξ,
      ENNReal.ofReal (c * r n ξ) ≤ ⨆ h, ENNReal.ofReal |Vfam n ξ h|)
    (hW : ∀ n ξ, (⨆ h, ENNReal.ofReal |Vfam n ξ h|) ≤
      (⨆ h, ENNReal.ofReal |Afam n ξ h|) + (⨆ h, ENNReal.ofReal |Sfam n ξ h|))
    (hA : IsBoundedInOuterProbSup μ Afam)
    (hS : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | ∃ h, ε * r n ξ < |Sfam n ξ h|}) atTop (𝓝 0)) :
    IsBoundedInOuterProbScalar μ r ∧ TendstoZeroInOuterProbSup μ Sfam := by
  -- **Part (a): `r = O_P(1)`.**  From `c·r ≤ ‖Vfam‖ ≤ ‖Afam‖ + ‖Sfam‖` and the
  -- controls `‖Afam‖ = O_P(1)`, `‖Sfam‖ ≤ (c/2)·r` (off a vanishing tail) one gets
  -- `(c/2)·r ≤ M` on the bulk, i.e. `r ≤ (2/c)·M`.
  have h_rate : IsBoundedInOuterProbScalar μ r := by
    intro η hη
    obtain ⟨M, hM⟩ := hA η hη
    set M₀ : ℝ := max M 0 with hM₀def
    have hM₀0 : 0 ≤ M₀ := le_max_right _ _
    have hMM₀ : M ≤ M₀ := le_max_left _ _
    have hM₀_limsup : limsup (fun n =>
        μ.outerMeasureStar {ξ | ∃ h, M₀ < |Afam n ξ h|}) atTop ≤ ENNReal.ofReal η := by
      refine le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
        outerMeasureStar_mono μ ?_) isCobounded_le_of_bot
        (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hM
      intro ξ hξ
      obtain ⟨h, hh⟩ := hξ
      exact ⟨h, lt_of_le_of_lt hMM₀ hh⟩
    refine ⟨2 * M₀ / c, ?_⟩
    have hsub : ∀ n, {ξ | 2 * M₀ / c < |r n ξ|}
        ⊆ {ξ | ∃ h, M₀ < |Afam n ξ h|} ∪ {ξ | ∃ h, c / 2 * r n ξ < |Sfam n ξ h|} := by
      intro n ξ hξ
      simp only [Set.mem_setOf_eq] at hξ
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      obtain ⟨hA', hS'⟩ := hcon
      simp only [Set.mem_setOf_eq, not_exists, not_lt] at hA' hS'
      have hAsup : (⨆ h, ENNReal.ofReal |Afam n ξ h|) ≤ ENNReal.ofReal M₀ :=
        iSup_le fun h => ENNReal.ofReal_le_ofReal (hA' h)
      have hSsup : (⨆ h, ENNReal.ofReal |Sfam n ξ h|) ≤ ENNReal.ofReal (c / 2 * r n ξ) :=
        iSup_le fun h => ENNReal.ofReal_le_ofReal (hS' h)
      have hcr_nonneg : (0 : ℝ) ≤ c / 2 * r n ξ :=
        mul_nonneg (div_nonneg hc.le (by norm_num)) (hr_nonneg n ξ)
      have hchain : ENNReal.ofReal (c * r n ξ)
          ≤ ENNReal.ofReal M₀ + ENNReal.ofReal (c / 2 * r n ξ) :=
        le_trans (hlb n ξ) (le_trans (hW n ξ) (add_le_add hAsup hSsup))
      rw [← ENNReal.ofReal_add hM₀0 hcr_nonneg,
          ENNReal.ofReal_le_ofReal_iff (add_nonneg hM₀0 hcr_nonneg)] at hchain
      rw [abs_of_nonneg (hr_nonneg n ξ), div_lt_iff₀ hc] at hξ
      have e1 : c / 2 * r n ξ = c * r n ξ / 2 := by ring
      rw [e1] at hchain
      rw [mul_comm (r n ξ) c] at hξ
      linarith
    have hb : ∀ n, μ.outerMeasureStar {ξ | 2 * M₀ / c < |r n ξ|}
        ≤ μ.outerMeasureStar {ξ | ∃ h, M₀ < |Afam n ξ h|}
          + μ.outerMeasureStar {ξ | ∃ h, c / 2 * r n ξ < |Sfam n ξ h|} :=
      fun n => le_trans (outerMeasureStar_mono μ (hsub n)) (outerMeasureStar_union_le μ _ _)
    calc limsup (fun n => μ.outerMeasureStar {ξ | 2 * M₀ / c < |r n ξ|}) atTop
        ≤ limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, M₀ < |Afam n ξ h|}
            + μ.outerMeasureStar {ξ | ∃ h, c / 2 * r n ξ < |Sfam n ξ h|}) atTop :=
          limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
            (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ ≤ ENNReal.ofReal η := limsup_add_tendsto_zero_le _ _ _ hM₀_limsup (hS (c / 2) (half_pos hc))
  refine ⟨h_rate, ?_⟩
  -- **Part (b): `Sfam →ₚ 0`.**  Fix ε; for each η pick `M₀ ≥ 0` bounding `r`
  -- (part (a)); on `{r ≤ M₀}` we have `(ε/(M₀+1))·r < ε`, so
  -- `{∃h, ε < |Sfam|} ⊆ {M₀ < r} ∪ {∃h, (ε/(M₀+1))·r < |Sfam|}`; the second → 0 by `hS`.
  intro ε hε
  refine tendsto_zero_of_limsup_le_ofReal _ ?_
  intro η hη
  obtain ⟨M, hMr⟩ := h_rate η hη
  set M₀ : ℝ := max M 0 with hM₀def
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hMM₀ : M ≤ M₀ := le_max_left _ _
  have hMr₀ : limsup (fun n => μ.outerMeasureStar {ξ | M₀ < |r n ξ|}) atTop
      ≤ ENNReal.ofReal η := by
    refine le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
      outerMeasureStar_mono μ ?_) isCobounded_le_of_bot
      (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hMr
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    exact lt_of_le_of_lt hMM₀ hξ
  have hM₀1 : (0 : ℝ) < M₀ + 1 := by linarith
  set ε' : ℝ := ε / (M₀ + 1) with hε'def
  have hε'0 : 0 < ε' := div_pos hε hM₀1
  have hsub : ∀ n, {ξ | ∃ h, ε < |Sfam n ξ h|}
      ⊆ {ξ | M₀ < |r n ξ|} ∪ {ξ | ∃ h, ε' * r n ξ < |Sfam n ξ h|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    by_cases hr : M₀ < r n ξ
    · left
      simp only [Set.mem_setOf_eq, abs_of_nonneg (hr_nonneg n ξ)]
      exact hr
    · right
      push_neg at hr
      refine ⟨h, ?_⟩
      have h1 : ε' * r n ξ ≤ ε' * M₀ := mul_le_mul_of_nonneg_left hr hε'0.le
      have h2 : ε' * M₀ < ε := by
        rw [hε'def, div_mul_eq_mul_div, div_lt_iff₀ hM₀1]
        exact mul_lt_mul_of_pos_left (by linarith) hε
      exact lt_trans (lt_of_le_of_lt h1 h2) hh
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, ε < |Sfam n ξ h|}
      ≤ μ.outerMeasureStar {ξ | M₀ < |r n ξ|}
        + μ.outerMeasureStar {ξ | ∃ h, ε' * r n ξ < |Sfam n ξ h|} :=
    fun n => le_trans (outerMeasureStar_mono μ (hsub n)) (outerMeasureStar_union_le μ _ _)
  calc limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, ε < |Sfam n ξ h|}) atTop
      ≤ limsup (fun n => μ.outerMeasureStar {ξ | M₀ < |r n ξ|}
          + μ.outerMeasureStar {ξ | ∃ h, ε' * r n ξ < |Sfam n ξ h|}) atTop :=
        limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal η := limsup_add_tendsto_zero_le _ _ _ hMr₀ (hS ε' hε'0)

/-- `P*(A) ≤ μ A` for every set `A`. The public
copy `outerMeasureStar_le_measure` lives one layer up in
`UniformRandomFunctions.lean`, which imports this file, so it is not in scope
here; the four sign / modification helpers below need it, so we re-prove it
privately. Every measurable superset `t ⊇ A` gives `E*[1_A] ≤ ∫⁻ 1_t = μ t`;
the infimum over such `t` (`measure_eq_iInf`) is `μ A`. -/
private theorem outerMeasureStar_le_measure_aux {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (A : Set Ξ) : μ.outerMeasureStar A ≤ μ A := by
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

/-- `o_P` in the `ℓ∞(H)` sup norm is closed under pointwise
negation (`|−g| = |g|`, so the exceedance events coincide). -/
theorem TendstoZeroInOuterProbSup.neg {Ξ H : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {g : ℕ → Ξ → H → ℝ} (h : TendstoZeroInOuterProbSup μ g) :
    TendstoZeroInOuterProbSup μ (fun n ξ hh => -g n ξ hh) := by
  intro ε hε
  simp only [abs_neg]
  exact h ε hε

/-- `o_P(1) ⟹ O_P(1)` in the `ℓ∞(H)` sup norm: a family that
tends to `0` in outer probability is bounded in outer probability (witness
`M = 1`; the `limsup` of a sequence tending to `0` is `0 ≤ ENNReal.ofReal η`). -/
theorem isBoundedInOuterProbSup_of_tendstoZero {Ξ H : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {g : ℕ → Ξ → H → ℝ} (h : TendstoZeroInOuterProbSup μ g) :
    IsBoundedInOuterProbSup μ g := by
  intro η hη
  refine ⟨1, ?_⟩
  have hlim : limsup (fun n => μ.outerMeasureStar {ξ | ∃ hh, (1 : ℝ) < |g n ξ hh|}) atTop = 0 :=
    (h 1 one_pos).limsup_eq
  rw [hlim]
  exact zero_le

/-- `O_P(1)` in the `ℓ∞(H)` sup norm is closed under pointwise
negation. -/
theorem IsBoundedInOuterProbSup.neg {Ξ H : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {g : ℕ → Ξ → H → ℝ} (h : IsBoundedInOuterProbSup μ g) :
    IsBoundedInOuterProbSup μ (fun n ξ hh => -g n ξ hh) := by
  intro η hη
  obtain ⟨M, hM⟩ := h η hη
  refine ⟨M, ?_⟩
  simp only [abs_neg]
  exact hM

/-- `o_P` in the `ℓ∞(H)` sup norm is insensitive to a
modification off a vanishing-mass event: if `g'` is `o_P` and `g = g'` off a
`bad` event of `μ`-mass `→ 0`, then `g` is `o_P` as well.

Outline: `{ξ | ∃h, ε < |g|} ⊆ {ξ | ∃h, ε < |g'|} ∪ bad n` (on `ξ ∉ bad n`,
`g = g'`); `outerMeasureStar_mono` + `outerMeasureStar_union_le`, then
`μ*(bad) ≤ μ(bad) → 0` (via `outerMeasureStar_le_measure_aux`) and squeeze. -/
theorem tendstoZeroInOuterProbSup_of_eq_off_vanishing {Ξ H : Type*}
    [MeasurableSpace Ξ] {μ : Measure Ξ} {g g' : ℕ → Ξ → H → ℝ} {bad : ℕ → Set Ξ}
    (hg' : TendstoZeroInOuterProbSup μ g')
    (hbad : Tendsto (fun n => μ (bad n)) atTop (𝓝 0))
    (heq : ∀ n ξ, ξ ∉ bad n → ∀ hh, g n ξ hh = g' n ξ hh) :
    TendstoZeroInOuterProbSup μ g := by
  intro ε hε
  have hsub : ∀ n, {ξ | ∃ h, ε < |g n ξ h|}
      ⊆ {ξ | ∃ h, ε < |g' n ξ h|} ∪ bad n := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    by_cases hb : ξ ∈ bad n
    · exact Or.inr hb
    · exact Or.inl ⟨h, by rwa [heq n ξ hb h] at hh⟩
  have hbadstar : Tendsto (fun n => μ.outerMeasureStar (bad n)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
      (Eventually.of_forall fun n => zero_le)
      (Eventually.of_forall fun n => outerMeasureStar_le_measure_aux μ (bad n))
  have hsum : Tendsto (fun n => μ.outerMeasureStar {ξ | ∃ h, ε < |g' n ξ h|}
      + μ.outerMeasureStar (bad n)) atTop (𝓝 0) := by
    simpa using (hg' ε hε).add hbadstar
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  calc μ.outerMeasureStar {ξ | ∃ h, ε < |g n ξ h|}
      ≤ μ.outerMeasureStar ({ξ | ∃ h, ε < |g' n ξ h|} ∪ bad n) :=
        outerMeasureStar_mono μ (hsub n)
    _ ≤ μ.outerMeasureStar {ξ | ∃ h, ε < |g' n ξ h|} + μ.outerMeasureStar (bad n) :=
        outerMeasureStar_union_le μ _ _

/-! ### Weighted `o_P` and `O_P` relative to a random rate (vdV Theorem 5.31)

The nuisance Z-estimator (`ZEstimatorNuisance.lean`, vdV Thm 5.31) states its
error as `o_P(1 + √n‖P ψ_{θ₀,η̂ₙ}‖)`, i.e. relative to a *random weight* `w n ξ`.
This block is the weighted sibling of the constant-rate layer above: each
exceedance event carries the weight, `{ξ | ∃ h, ε · w n ξ < |g n ξ h|}`. Each is
proved by mirroring its constant-rate sibling with the weight threaded through the
exceedance thresholds. -/

/-- **Weighted little-`o_P` in the `ℓ∞(H)` sup norm.** `g_n = o_P(w_n)` uniformly
over `H`: for every `ε > 0` the outer measure of the weighted exceedance event
`{ξ | ∃ h, ε · w n ξ < |g n ξ h|}` tends to `0`. Reduces to
`TendstoZeroInOuterProbSup` when `w ≡ 1`. vdV §5.4 (`o_P(1 + √n‖·‖)` conclusion of
Thm 5.31). -/
def TendstoZeroInOuterProbSupWt {Ξ H : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (w : ℕ → Ξ → ℝ) (g : ℕ → Ξ → H → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ.outerMeasureStar {ξ | ∃ h, ε * w n ξ < |g n ξ h|}) atTop (𝓝 0)

/-- **Weighted `O_P` in the `ℓ∞(H)` sup norm.** `g_n = O_P(w_n)` uniformly over
`H`: for every `η > 0` there is a level `M` with `limsup` of the outer measure of
`{ξ | ∃ h, M · w n ξ < |g n ξ h|}` at most `η`. -/
def IsBoundedInOuterProbSupWt {Ξ H : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (w : ℕ → Ξ → ℝ) (g : ℕ → Ξ → H → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ,
    limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, M * w n ξ < |g n ξ h|}) atTop
      ≤ ENNReal.ofReal η

/-- **Weighted scalar `O_P` (rate bounded by the weight).** The `H`-free weighted
sibling of `IsBoundedInOuterProbScalar`: `r_n = O_P(w_n)`. The rate
`r_n := √n‖θ̂_n − θ₀‖` of the nuisance bootstrap is bounded relative to the drift
weight `w_n = 1 + √n‖P ψ_{θ₀,η̂ₙ}‖`. -/
def IsBoundedInOuterProbScalarWt {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) (w : ℕ → Ξ → ℝ) (r : ℕ → Ξ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ M : ℝ,
    limsup (fun n => μ.outerMeasureStar {ξ | M * w n ξ < |r n ξ|}) atTop
      ≤ ENNReal.ofReal η

/-- **Weighted `o_P` is closed under addition (sup form).** Weighted sibling of
`oP_sup_add`; the `ε/2`-split uses `w ≥ 1 > 0`. -/
theorem oP_supWt_add {Ξ H : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    {w : ℕ → Ξ → ℝ} (hw : ∀ n ξ, 1 ≤ w n ξ)
    {g₁ g₂ : ℕ → Ξ → H → ℝ}
    (h₁ : TendstoZeroInOuterProbSupWt μ w g₁) (h₂ : TendstoZeroInOuterProbSupWt μ w g₂) :
    TendstoZeroInOuterProbSupWt μ w (fun n ξ h => g₁ n ξ h + g₂ n ξ h) := by
  intro ε hε
  have hsub : ∀ n, {ξ | ∃ h, ε * w n ξ < |g₁ n ξ h + g₂ n ξ h|}
      ⊆ {ξ | ∃ h, ε / 2 * w n ξ < |g₁ n ξ h|} ∪ {ξ | ∃ h, ε / 2 * w n ξ < |g₂ n ξ h|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    have htri : ε * w n ξ < |g₁ n ξ h| + |g₂ n ξ h| := lt_of_lt_of_le hh (abs_add_le _ _)
    have hww : ε * w n ξ = ε / 2 * w n ξ + ε / 2 * w n ξ := by ring
    by_cases h1 : ε / 2 * w n ξ < |g₁ n ξ h|
    · exact Or.inl ⟨h, h1⟩
    · push_neg at h1
      exact Or.inr ⟨h, by linarith⟩
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, ε * w n ξ < |g₁ n ξ h + g₂ n ξ h|}
      ≤ μ.outerMeasureStar {ξ | ∃ h, ε / 2 * w n ξ < |g₁ n ξ h|}
        + μ.outerMeasureStar {ξ | ∃ h, ε / 2 * w n ξ < |g₂ n ξ h|} :=
    fun n => le_trans (outerMeasureStar_mono μ (hsub n)) (outerMeasureStar_union_le μ _ _)
  have hsum : Tendsto (fun n => μ.outerMeasureStar {ξ | ∃ h, ε / 2 * w n ξ < |g₁ n ξ h|}
      + μ.outerMeasureStar {ξ | ∃ h, ε / 2 * w n ξ < |g₂ n ξ h|}) atTop (𝓝 0) := by
    have := (h₁ (ε / 2) (by linarith)).add (h₂ (ε / 2) (by linarith))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall hb)

/-- **A family dominated by the weight is `O_P(w)`.** If `|g n ξ h| ≤ w n ξ` for
all `n ξ h`, then `g = O_P(w)` uniformly over `H` (the `M = 1` weighted exceedance
event is empty, since `w < |g| ≤ w` is impossible). Used to absorb the drift term
`√n·driftVec` in the nuisance-estimator remainder. -/
theorem isBoundedInOuterProbSupWt_of_le_wt {Ξ H : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {w : ℕ → Ξ → ℝ} {g : ℕ → Ξ → H → ℝ}
    (h_dom : ∀ n ξ h, |g n ξ h| ≤ w n ξ) :
    IsBoundedInOuterProbSupWt μ w g := by
  intro η hη
  refine ⟨1, ?_⟩
  have hz : ∀ n, μ.outerMeasureStar {ξ | ∃ h, (1 : ℝ) * w n ξ < |g n ξ h|} = 0 := by
    intro n
    have hempty : {ξ | ∃ h, (1 : ℝ) * w n ξ < |g n ξ h|} = (∅ : Set Ξ) := by
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      intro h
      rw [one_mul]
      exact not_lt.mpr (h_dom n ξ h)
    rw [hempty]
    exact le_antisymm (le_trans (outerMeasureStar_le_measure_aux μ ∅) (by simp)) (zero_le)
  simp only [hz]
  rw [limsup_const]
  exact zero_le

/-- **Weighted `o_P` from coefficient × rate domination.** If `coeff_n →ₚ 0`
(scalar), the rate `r_n = O_P(w_n)`, and `|g n ξ h| ≤ coeff n ξ · r n ξ` for all
`n ξ h`, then `g = o_P(w)` uniformly over `H`. This turns a `coeff →ₚ 0` factor
(the V-swap modulus / the Fréchet modulus) times the `O_P(w)` rate into a weighted
`o_P`. -/
theorem oPWt_of_coeff_mul_rate {Ξ H : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ}
    {w : ℕ → Ξ → ℝ} (hw : ∀ n ξ, 1 ≤ w n ξ)
    {g : ℕ → Ξ → H → ℝ} {coeff r : ℕ → Ξ → ℝ}
    (hcoeff_nonneg : ∀ n ξ, 0 ≤ coeff n ξ) (hr_nonneg : ∀ n ξ, 0 ≤ r n ξ)
    (h_coeff : TendstoZeroInOuterProbScalar μ coeff)
    (h_rate : IsBoundedInOuterProbScalarWt μ w r)
    (h_dom : ∀ n ξ h, |g n ξ h| ≤ coeff n ξ * r n ξ) :
    TendstoZeroInOuterProbSupWt μ w g := by
  intro ε hε
  refine tendsto_zero_of_limsup_le_ofReal _ ?_
  intro η hη
  obtain ⟨M, hM⟩ := h_rate η hη
  set M₀ : ℝ := max M 1 with hM₀def
  have hM₀1 : (1 : ℝ) ≤ M₀ := le_max_right _ _
  have hM₀0 : (0 : ℝ) < M₀ := lt_of_lt_of_le one_pos hM₀1
  have hMM₀ : M ≤ M₀ := le_max_left _ _
  have hM₀ne : M₀ ≠ 0 := ne_of_gt hM₀0
  have hM₀_limsup : limsup (fun n =>
      μ.outerMeasureStar {ξ | M₀ * w n ξ < |r n ξ|}) atTop ≤ ENNReal.ofReal η := by
    refine le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
      outerMeasureStar_mono μ ?_) isCobounded_le_of_bot
      (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hM
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    have hwpos : 0 ≤ w n ξ := le_trans zero_le_one (hw n ξ)
    have hle : M * w n ξ ≤ M₀ * w n ξ := mul_le_mul_of_nonneg_right hMM₀ hwpos
    linarith
  have hεM₀ : 0 < ε / M₀ := div_pos hε hM₀0
  have hsub : ∀ n, {ξ | ∃ h, ε * w n ξ < |g n ξ h|}
      ⊆ {ξ | M₀ * w n ξ < |r n ξ|} ∪ {ξ | ε / M₀ < |coeff n ξ|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hr', hc'⟩ := hcon
    simp only [Set.mem_setOf_eq, not_lt] at hr' hc'
    rw [abs_of_nonneg (hr_nonneg n ξ)] at hr'
    rw [abs_of_nonneg (hcoeff_nonneg n ξ)] at hc'
    have step1 : coeff n ξ * r n ξ ≤ (ε / M₀) * r n ξ :=
      mul_le_mul_of_nonneg_right hc' (hr_nonneg n ξ)
    have step2 : (ε / M₀) * r n ξ ≤ (ε / M₀) * (M₀ * w n ξ) :=
      mul_le_mul_of_nonneg_left hr' hεM₀.le
    have step3 : (ε / M₀) * (M₀ * w n ξ) = ε * w n ξ := by
      rw [← mul_assoc, div_mul_cancel₀ ε hM₀ne]
    have hfinal : |g n ξ h| ≤ ε * w n ξ := by
      calc |g n ξ h| ≤ coeff n ξ * r n ξ := h_dom n ξ h
        _ ≤ (ε / M₀) * r n ξ := step1
        _ ≤ (ε / M₀) * (M₀ * w n ξ) := step2
        _ = ε * w n ξ := step3
    linarith
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, ε * w n ξ < |g n ξ h|}
      ≤ μ.outerMeasureStar {ξ | M₀ * w n ξ < |r n ξ|}
        + μ.outerMeasureStar {ξ | ε / M₀ < |coeff n ξ|} :=
    fun n => le_trans (outerMeasureStar_mono μ (hsub n)) (outerMeasureStar_union_le μ _ _)
  calc limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, ε * w n ξ < |g n ξ h|}) atTop
      ≤ limsup (fun n => μ.outerMeasureStar {ξ | M₀ * w n ξ < |r n ξ|}
          + μ.outerMeasureStar {ξ | ε / M₀ < |coeff n ξ|}) atTop :=
        limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal η :=
        limsup_add_tendsto_zero_le _ _ _ hM₀_limsup (h_coeff (ε / M₀) hεM₀)

/-- **Weighted rate bootstrap (step 5 of the vdV 5.21-style proof, Thm 5.31).**

The weighted sibling of `rate_bootstrap_oP`. The lower bound `hlb` on `‖Vfam‖`
may fail on a guard event `bad` of vanishing outer mass (`hbad`), reflecting that
the neighborhood nonsingularity of `V η` only holds once `η̂` is close to `η₀`.
Under the decomposition `hW` with `Afam = O_P(w)` (`hA`) and `Sfam`
controlled by `ε · r` (`hS`), the rate `r` is `O_P(w)` and `Sfam →ₚ 0` relative to
`w`.

The proof combines the self-referential `ℝ≥0∞` `limsup` argument with the
vanishing guard event. -/
theorem rate_bootstrap_oP_wt {Ξ H : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (Vfam Afam Sfam : ℕ → Ξ → H → ℝ) (r w : ℕ → Ξ → ℝ)
    (hr_nonneg : ∀ n ξ, 0 ≤ r n ξ)
    (hw : ∀ n ξ, 1 ≤ w n ξ)
    (bad : ℕ → Set Ξ)
    (hbad : Tendsto (fun n => μ.outerMeasureStar (bad n)) atTop (𝓝 0))
    (c : ℝ) (hc : 0 < c)
    (hlb : ∀ n ξ, ξ ∉ bad n →
      ENNReal.ofReal (c * r n ξ) ≤ ⨆ h, ENNReal.ofReal |Vfam n ξ h|)
    (hW : ∀ n ξ, (⨆ h, ENNReal.ofReal |Vfam n ξ h|) ≤
      (⨆ h, ENNReal.ofReal |Afam n ξ h|) + (⨆ h, ENNReal.ofReal |Sfam n ξ h|))
    (hA : IsBoundedInOuterProbSupWt μ w Afam)
    (hS : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | ∃ h, ε * r n ξ < |Sfam n ξ h|}) atTop (𝓝 0)) :
    IsBoundedInOuterProbScalarWt μ w r ∧ TendstoZeroInOuterProbSupWt μ w Sfam := by
  have hcne : c ≠ 0 := ne_of_gt hc
  -- **Part (a): `r = O_P(w)`.**
  have h_rate : IsBoundedInOuterProbScalarWt μ w r := by
    intro η hη
    obtain ⟨M, hM⟩ := hA η hη
    set M₀ : ℝ := max M 0 with hM₀def
    have hM₀0 : 0 ≤ M₀ := le_max_right _ _
    have hMM₀ : M ≤ M₀ := le_max_left _ _
    have hM₀_limsup : limsup (fun n =>
        μ.outerMeasureStar {ξ | ∃ h, M₀ * w n ξ < |Afam n ξ h|}) atTop
        ≤ ENNReal.ofReal η := by
      refine le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
        outerMeasureStar_mono μ ?_) isCobounded_le_of_bot
        (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hM
      intro ξ hξ
      obtain ⟨h, hh⟩ := hξ
      refine ⟨h, ?_⟩
      have hwpos : 0 ≤ w n ξ := le_trans zero_le_one (hw n ξ)
      have hle : M * w n ξ ≤ M₀ * w n ξ := mul_le_mul_of_nonneg_right hMM₀ hwpos
      linarith
    refine ⟨2 * M₀ / c, ?_⟩
    have hsub : ∀ n, {ξ | 2 * M₀ / c * w n ξ < |r n ξ|}
        ⊆ {ξ | ∃ h, M₀ * w n ξ < |Afam n ξ h|}
          ∪ (bad n ∪ {ξ | ∃ h, c / 2 * r n ξ < |Sfam n ξ h|}) := by
      intro n ξ hξ
      simp only [Set.mem_setOf_eq] at hξ
      by_contra hcon
      rw [Set.mem_union, not_or, Set.mem_union, not_or] at hcon
      obtain ⟨hA', hbad', hS'⟩ := hcon
      simp only [Set.mem_setOf_eq, not_exists, not_lt] at hA' hS'
      have hAsup : (⨆ h, ENNReal.ofReal |Afam n ξ h|) ≤ ENNReal.ofReal (M₀ * w n ξ) :=
        iSup_le fun h => ENNReal.ofReal_le_ofReal (hA' h)
      have hSsup : (⨆ h, ENNReal.ofReal |Sfam n ξ h|) ≤ ENNReal.ofReal (c / 2 * r n ξ) :=
        iSup_le fun h => ENNReal.ofReal_le_ofReal (hS' h)
      have hwpos : 0 ≤ w n ξ := le_trans zero_le_one (hw n ξ)
      have hM₀w_nonneg : (0 : ℝ) ≤ M₀ * w n ξ := mul_nonneg hM₀0 hwpos
      have hcr_nonneg : (0 : ℝ) ≤ c / 2 * r n ξ :=
        mul_nonneg (div_nonneg hc.le (by norm_num)) (hr_nonneg n ξ)
      have hchain : ENNReal.ofReal (c * r n ξ)
          ≤ ENNReal.ofReal (M₀ * w n ξ) + ENNReal.ofReal (c / 2 * r n ξ) :=
        le_trans (hlb n ξ hbad') (le_trans (hW n ξ) (add_le_add hAsup hSsup))
      rw [← ENNReal.ofReal_add hM₀w_nonneg hcr_nonneg,
          ENNReal.ofReal_le_ofReal_iff (add_nonneg hM₀w_nonneg hcr_nonneg)] at hchain
      rw [abs_of_nonneg (hr_nonneg n ξ)] at hξ
      have hcK : c * (2 * M₀ / c) = 2 * M₀ := by field_simp
      have hξ' : c * (2 * M₀ / c * w n ξ) < c * r n ξ := mul_lt_mul_of_pos_left hξ hc
      have hlhs : c * (2 * M₀ / c * w n ξ) = 2 * (M₀ * w n ξ) := by
        rw [← mul_assoc, hcK]; ring
      rw [hlhs] at hξ'
      have e1 : c / 2 * r n ξ = c * r n ξ / 2 := by ring
      rw [e1] at hchain
      linarith
    have hb : ∀ n, μ.outerMeasureStar {ξ | 2 * M₀ / c * w n ξ < |r n ξ|}
        ≤ μ.outerMeasureStar {ξ | ∃ h, M₀ * w n ξ < |Afam n ξ h|}
          + (μ.outerMeasureStar (bad n)
            + μ.outerMeasureStar {ξ | ∃ h, c / 2 * r n ξ < |Sfam n ξ h|}) := by
      intro n
      refine le_trans (outerMeasureStar_mono μ (hsub n)) ?_
      refine le_trans (outerMeasureStar_union_le μ _ _) ?_
      exact add_le_add le_rfl (outerMeasureStar_union_le μ _ _)
    calc limsup (fun n => μ.outerMeasureStar {ξ | 2 * M₀ / c * w n ξ < |r n ξ|}) atTop
        ≤ limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, M₀ * w n ξ < |Afam n ξ h|}
            + (μ.outerMeasureStar (bad n)
              + μ.outerMeasureStar {ξ | ∃ h, c / 2 * r n ξ < |Sfam n ξ h|})) atTop :=
          limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
            (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
      _ ≤ ENNReal.ofReal η :=
          limsup_add_tendsto_zero_le _ _ _ hM₀_limsup
            (by simpa using hbad.add (hS (c / 2) (half_pos hc)))
  refine ⟨h_rate, ?_⟩
  -- **Part (b): `Sfam →ₚ 0` relative to `w`.**
  intro ε hε
  refine tendsto_zero_of_limsup_le_ofReal _ ?_
  intro η hη
  obtain ⟨M, hMr⟩ := h_rate η hη
  set M₀ : ℝ := max M 0 with hM₀def
  have hM₀0 : 0 ≤ M₀ := le_max_right _ _
  have hMM₀ : M ≤ M₀ := le_max_left _ _
  have hMr₀ : limsup (fun n => μ.outerMeasureStar {ξ | M₀ * w n ξ < |r n ξ|}) atTop
      ≤ ENNReal.ofReal η := by
    refine le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
      outerMeasureStar_mono μ ?_) isCobounded_le_of_bot
      (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hMr
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    have hwpos : 0 ≤ w n ξ := le_trans zero_le_one (hw n ξ)
    have hle : M * w n ξ ≤ M₀ * w n ξ := mul_le_mul_of_nonneg_right hMM₀ hwpos
    linarith
  have hM₀1 : (0 : ℝ) < M₀ + 1 := by linarith
  set ε' : ℝ := ε / (M₀ + 1) with hε'def
  have hε'0 : 0 < ε' := div_pos hε hM₀1
  have hsub : ∀ n, {ξ | ∃ h, ε * w n ξ < |Sfam n ξ h|}
      ⊆ {ξ | M₀ * w n ξ < |r n ξ|} ∪ {ξ | ∃ h, ε' * r n ξ < |Sfam n ξ h|} := by
    intro n ξ hξ
    obtain ⟨h, hh⟩ := hξ
    by_cases hr : M₀ * w n ξ < r n ξ
    · left
      simp only [Set.mem_setOf_eq, abs_of_nonneg (hr_nonneg n ξ)]
      exact hr
    · right
      push_neg at hr
      refine ⟨h, ?_⟩
      have hwpos : 0 < w n ξ := lt_of_lt_of_le one_pos (hw n ξ)
      have h1 : ε' * r n ξ ≤ ε' * (M₀ * w n ξ) := mul_le_mul_of_nonneg_left hr hε'0.le
      have h2 : ε' * (M₀ * w n ξ) < ε * w n ξ := by
        have hεM : ε' * M₀ < ε := by
          rw [hε'def, div_mul_eq_mul_div, div_lt_iff₀ hM₀1]
          exact mul_lt_mul_of_pos_left (by linarith) hε
        calc ε' * (M₀ * w n ξ) = (ε' * M₀) * w n ξ := by ring
          _ < ε * w n ξ := mul_lt_mul_of_pos_right hεM hwpos
      exact lt_trans (lt_of_le_of_lt h1 h2) hh
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, ε * w n ξ < |Sfam n ξ h|}
      ≤ μ.outerMeasureStar {ξ | M₀ * w n ξ < |r n ξ|}
        + μ.outerMeasureStar {ξ | ∃ h, ε' * r n ξ < |Sfam n ξ h|} :=
    fun n => le_trans (outerMeasureStar_mono μ (hsub n)) (outerMeasureStar_union_le μ _ _)
  calc limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, ε * w n ξ < |Sfam n ξ h|}) atTop
      ≤ limsup (fun n => μ.outerMeasureStar {ξ | M₀ * w n ξ < |r n ξ|}
          + μ.outerMeasureStar {ξ | ∃ h, ε' * r n ξ < |Sfam n ξ h|}) atTop :=
        limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ ≤ ENNReal.ofReal η := limsup_add_tendsto_zero_le _ _ _ hMr₀ (hS ε' hε'0)

end AsymptoticStatistics.EmpiricalProcess
