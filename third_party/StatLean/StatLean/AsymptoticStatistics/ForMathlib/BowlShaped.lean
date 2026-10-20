module
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-!
# Bowl-shaped loss functions

A loss function `L : E → ℝ≥0∞` is **bowl-shaped** if it is measurable, symmetric
about the origin, and has convex sublevel sets `{x | L x ≤ c}` (equivalently, the
sublevel sets are convex symmetric subsets of `E`). This is van der Vaart's standing
assumption on the loss in the Local Asymptotic Minimax theorem (vdV §8.7 Theorem 8.11);
the definition is given in vdV §8.4. Note vdV distinguishes **bowl-shaped** (convex
symmetric sublevel sets) from **subconvex** (bowl-shaped *and* closed sublevel sets,
i.e. additionally lower semicontinuous); the `BowlShaped` structure here is bowl-shaped
only. Typical examples: norm powers `‖·‖^p` for `p ≥ 1`, indicators of convex symmetric
set complements, finite maxima and truncations of these.

Headline declaration: the `BowlShaped` structure, with the basic properties
`le_at_zero`, `truncate`, `norm_pow`, `le_smul_of_one_le`, and the lsc-envelope API
(`lscEnvelope`, `lowerSemicontinuous_lscEnvelope`).

Design notes: measurability is kept as an explicit field (rather than derived) so the
structure works for `E` more general than `ℝ^d`, where convex sublevel sets would already
force Borel measurability. The codomain `ℝ≥0∞` matches Mathlib's `bayesRisk` / `avgRisk`
/ `minimaxRisk` framework; vdV uses `[0, ∞)`, and the generalisation to `[0, ∞]` is a
no-op for finite-valued losses while letting us state results without an integrability
hypothesis.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal

namespace AsymptoticStatistics

variable {E : Type*}

/-- A **bowl-shaped** loss function `L : E → ℝ≥0∞`: measurable, symmetric, with
convex sublevel sets (vdV §8.4).

This is **not** "subconvex": vdV reserves that term for bowl-shaped *with closed*
sublevel sets (equivalently `L` lower semicontinuous). This structure has no
closed-sublevel / lsc field, so consumers needing lsc carry it separately.

See the file header for the role in the LAM theorem (vdV §8.4/§8.7) and for design
notes on the codomain and the explicit measurability field. -/
structure BowlShaped [AddCommGroup E] [Module ℝ E] [MeasurableSpace E]
    (L : E → ℝ≥0∞) : Prop where
  /-- `L` is measurable. This is implicit in vdV, where any integral on the LHS of
  the LAM bound is silently assumed defined. -/
  measurable : Measurable L
  /-- vdV §8.5: `L` is symmetric about the origin. -/
  symm : ∀ x, L (-x) = L x
  /-- vdV §8.5: every sublevel set `{x | L x ≤ c}` is convex.
  Combined with `symm`, this gives "convex symmetric sublevel sets" — the
  literal definition of bowl-shaped. -/
  convex_sublevel : ∀ c : ℝ≥0∞, Convex ℝ {x | L x ≤ c}

namespace BowlShaped

variable [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] {L : E → ℝ≥0∞}

/-- A bowl-shaped loss attains its minimum at the origin: `L 0 ≤ L x`.

Proof: `x` and `-x` are both in `{y | L y ≤ L x}` (by `symm` + reflexivity);
their convex combination at weights `(1/2, 1/2)` is `0`; sublevel set is
convex by `convex_sublevel`. -/
lemma le_at_zero (h : BowlShaped L) (x : E) : L 0 ≤ L x := by
  have hx_mem : x ∈ {y | L y ≤ L x} := show L x ≤ L x from le_refl _
  have hnx_mem : (-x : E) ∈ {y | L y ≤ L x} := show L (-x) ≤ L x from (h.symm x).le
  have h_combo : ((1/2 : ℝ) • x + (1/2 : ℝ) • (-x)) ∈ {y | L y ≤ L x} :=
    h.convex_sublevel (L x) hx_mem hnx_mem (by norm_num) (by norm_num) (by norm_num)
  have hzero : (1/2 : ℝ) • x + (1/2 : ℝ) • (-x) = (0 : E) := by
    rw [smul_neg, add_neg_cancel]
  rwa [hzero] at h_combo

/-- **Truncation**: `min L M` is bowl-shaped for any constant `M : ℝ≥0∞`.

The sublevel set `{x | (L x ⊓ M) ≤ c}` equals either `{x | L x ≤ c}` (when
`¬ M ≤ c`) or the whole space (when `M ≤ c`); both are convex.

Used in `Ch8/LocalAsymptoticMinimax.lean` Step E to extend the LAM bound from bounded
bowl-shaped `L` to general bowl-shaped `L` via monotone convergence on
`L = ⨆ M, L ⊓ M`. -/
lemma truncate (h : BowlShaped L) (M : ℝ≥0∞) :
    BowlShaped (fun x => L x ⊓ M) where
  measurable := Measurable.min h.measurable measurable_const
  symm := fun x => by simp only [h.symm]
  convex_sublevel := fun c => by
    by_cases hMc : M ≤ c
    · have hsub : {x | L x ⊓ M ≤ c} = Set.univ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, inf_le_iff]
        exact Or.inr hMc
      rw [hsub]
      exact convex_univ
    · have hsub : {x | L x ⊓ M ≤ c} = {x | L x ≤ c} := by
        ext x
        simp only [Set.mem_setOf_eq, inf_le_iff]
        exact ⟨fun h' => h'.resolve_right hMc, Or.inl⟩
      rw [hsub]
      exact h.convex_sublevel c

/-- For convex symmetric `C ⊂ E`, the indicator-of-complement
`L = ∞ · 1_{Cᶜ}` is bowl-shaped. The prototypical example: this loss
function declares "you left the convex body" with the worst possible value.

Encoded via `Set.indicator` (no `Decidable (x ∈ C)` requirement); the value at
`x` is `∞` if `x ∈ Cᶜ` (i.e. `x ∉ C`) and `0` otherwise. -/
lemma indicator_compl_of_convexSymm
    {C : Set E} (hC_meas : MeasurableSet C)
    (hC_conv : Convex ℝ C) (hC_symm : ∀ x ∈ C, -x ∈ C) :
    BowlShaped (Cᶜ.indicator (fun _ : E => (∞ : ℝ≥0∞))) where
  measurable := Measurable.indicator measurable_const hC_meas.compl
  symm := fun x => by
    -- C symmetric ⇔ Cᶜ symmetric ⇒ indicator agrees on x and -x.
    have h_iff : -x ∈ C ↔ x ∈ C :=
      ⟨fun h => by simpa using hC_symm (-x) h, hC_symm x⟩
    by_cases hx : x ∈ C
    · have hxC : x ∉ Cᶜ := fun h => h hx
      have hnxC : -x ∉ Cᶜ := fun h => h (h_iff.mpr hx)
      rw [Set.indicator_of_notMem hxC, Set.indicator_of_notMem hnxC]
    · have hxC : x ∈ Cᶜ := hx
      have hnxC : -x ∈ Cᶜ := fun h => hx (h_iff.mp h)
      rw [Set.indicator_of_mem hxC, Set.indicator_of_mem hnxC]
  convex_sublevel := fun c => by
    by_cases hc : c = ∞
    · -- All x satisfy `_ ≤ ∞`; the sublevel set is everything.
      have hsub : {x | Cᶜ.indicator (fun _ : E => (∞ : ℝ≥0∞)) x ≤ c} = Set.univ := by
        ext x; simp [hc]
      rw [hsub]; exact convex_univ
    · -- For finite `c`, indicator ≤ c forces `x ∈ C` (else value is ∞ > c).
      have hsub : {x | Cᶜ.indicator (fun _ : E => (∞ : ℝ≥0∞)) x ≤ c} = C := by
        ext x
        refine ⟨fun hx_le => ?_, fun hxC => ?_⟩
        · by_contra hxC
          have hxCc : x ∈ Cᶜ := hxC
          rw [Set.mem_setOf_eq, Set.indicator_of_mem hxCc] at hx_le
          exact hc (top_unique hx_le)
        · have hxCc : x ∉ Cᶜ := fun h => h hxC
          change Cᶜ.indicator (fun _ : E => (∞ : ℝ≥0∞)) x ≤ c
          rw [Set.indicator_of_notMem hxCc]; exact zero_le
      rw [hsub]; exact hC_conv

/-- The norm-`p` loss `L x = ENNReal.ofReal (‖x‖^p)` is bowl-shaped for `p ≥ 1`.

The sublevel set `{x | ‖x‖^p ≤ c}` is the closed ball of radius `c^(1/p)`
(universe when `c = ⊤`), which is convex (norms are seminorms) and symmetric. -/
lemma norm_pow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {p : ℝ} (hp : 1 ≤ p) :
    BowlShaped (fun x : E => ENNReal.ofReal (‖x‖ ^ p)) where
  measurable := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact (continuous_norm.rpow_const fun _ => Or.inr (le_trans zero_le_one hp)).measurable
  symm := fun x => by simp [norm_neg]
  convex_sublevel := fun c => by
    by_cases hc : c = ∞
    · -- {x | _ ≤ ∞} = univ.
      have hsub : {x : E | ENNReal.ofReal (‖x‖ ^ p) ≤ c} = Set.univ := by
        ext x; simp [hc]
      rw [hsub]; exact convex_univ
    · -- Sublevel = closed ball of radius `c.toReal ^ p⁻¹`.
      have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
      have hpinv_pos : 0 < p⁻¹ := inv_pos.mpr hp_pos
      have hctR_nn : 0 ≤ c.toReal := ENNReal.toReal_nonneg
      set r : ℝ := c.toReal ^ p⁻¹ with hr_def
      -- Key bridge: for `a ≥ 0`, `a^p ≤ c.toReal ↔ a ≤ r`.
      have h_iff : ∀ a, 0 ≤ a → (a ^ p ≤ c.toReal ↔ a ≤ r) := by
        intro a ha
        have hap_nn : 0 ≤ a ^ p := Real.rpow_nonneg ha p
        have h_eq : (a ^ p) ^ p⁻¹ = a := by
          rw [← Real.rpow_mul ha, mul_inv_cancel₀ (ne_of_gt hp_pos), Real.rpow_one]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [← h_eq]
          exact Real.rpow_le_rpow hap_nn h (le_of_lt hpinv_pos)
        · have h' : a ^ p ≤ r ^ p := Real.rpow_le_rpow ha h (le_trans zero_le_one hp)
          rwa [hr_def, ← Real.rpow_mul hctR_nn, inv_mul_cancel₀ (ne_of_gt hp_pos),
               Real.rpow_one] at h'
      have hsub : {x : E | ENNReal.ofReal (‖x‖ ^ p) ≤ c} = Metric.closedBall (0 : E) r := by
        ext x
        simp only [Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right,
                   ENNReal.ofReal_le_iff_le_toReal hc]
        exact h_iff (‖x‖) (norm_nonneg _)
      rw [hsub]; exact convex_closedBall _ _

/-- A bowl-shaped loss is non-decreasing along rays from the origin: for
`1 ≤ c`, `L x ≤ L (c • x)`.

Since `0 < c`, `x = c⁻¹ • (c • x) + (1 − c⁻¹) • 0`, a convex combination
with weights in `[0,1]` summing to `1`. Both `c • x` (trivially) and `0`
(by `BowlShaped.le_at_zero`) lie in the sublevel set
`{y | L y ≤ L (c • x)}`, which is convex by `convex_sublevel`. -/
lemma le_smul_of_one_le {L : E → ℝ≥0∞} (hL : BowlShaped L)
    {c : ℝ} (hc : 1 ≤ c) (x : E) : L x ≤ L (c • x) := by
  have hc_pos : (0 : ℝ) < c := zero_lt_one.trans_le hc
  have hc_inv_pos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc_pos
  have hc_inv_le_one : c⁻¹ ≤ 1 := by
    rw [← one_div, div_le_one hc_pos]; exact hc
  have h_x_combo : c⁻¹ • (c • x) + (1 - c⁻¹) • (0 : E) = x := by
    rw [smul_zero, add_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt hc_pos), one_smul]
  have h_cx_mem : c • x ∈ {y | L y ≤ L (c • x)} :=
    show L (c • x) ≤ L (c • x) from le_refl _
  have h_zero_mem : (0 : E) ∈ {y | L y ≤ L (c • x)} := hL.le_at_zero (c • x)
  have h_combo_mem :
      c⁻¹ • (c • x) + (1 - c⁻¹) • (0 : E) ∈ {y | L y ≤ L (c • x)} :=
    hL.convex_sublevel (L (c • x)) h_cx_mem h_zero_mem
      hc_inv_pos.le (by linarith) (by ring)
  rw [h_x_combo] at h_combo_mem
  exact h_combo_mem

omit [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] in
/-- If a function `L : E → ℝ≥0∞` has all sublevel sets closed, it is lower
semicontinuous. The `BowlShaped` premise is not needed (kept in this namespace
purely because all of 8.11's downstream consumers feed in a bowl-shaped `L`).

Thin wrapper over Mathlib's `lowerSemicontinuous_iff_isClosed_preimage`,
exposing the more readable "closed sublevel" framing.

Used in `Ch8/LocalAsymptoticMinimax.lean` Step B/D, where Portmanteau under weak
convergence requires an lsc integrand. -/
lemma lowerSemicontinuous_of_isClosed_sublevel
    [TopologicalSpace E]
    (h_closed : ∀ c : ℝ≥0∞, IsClosed {x | L x ≤ c}) :
    LowerSemicontinuous L := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  exact h_closed

/-- **Lsc envelope** of `L`: `lscEnvelope L x := liminf_{y → x} L y`.

This is the largest lsc minorant of `L` (when `L` is `ℝ≥0∞`-valued and the
domain is a topological space).

Used in `Ch8/LocalAsymptoticMinimax.lean` Steps B+D: `BowlShaped L` does not imply `L`
lsc, but `lscEnvelope L` is lsc bowl-shaped, and the LAM bound passes through
the envelope without loss (since `lscEnvelope L ≤ L` and the inequality is
preserved by the bound). -/
noncomputable def lscEnvelope [TopologicalSpace E] (L : E → ℝ≥0∞) : E → ℝ≥0∞ :=
  fun x => Filter.liminf L (𝓝 x)

omit [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] in
/-- `lscEnvelope L ≤ L` pointwise (`L` is its own upper bound; lsc envelope
is the largest lsc minorant).

Proof: any `b` such that `b ≤ L y` eventually around `x` satisfies `b ≤ L x`
in particular (since `x ∈ U` for any `U ∈ 𝓝 x`). Then `liminf L (𝓝 x) ≤ L x`
by `Filter.liminf_le_of_le`. -/
lemma lscEnvelope_le [TopologicalSpace E] (L : E → ℝ≥0∞) (x : E) :
    lscEnvelope L x ≤ L x := by
  unfold lscEnvelope
  refine Filter.liminf_le_of_le (h := ?_)
  intro b hb
  exact hb.self_of_nhds

omit [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] in
/-- `lscEnvelope L` is lower semicontinuous — the standard result that the
liminf-at-point map is lsc.

Used in `Ch8/LocalAsymptoticMinimax.lean` Steps B/D where Portmanteau is applied to the
lsc envelope of the bowl-shaped loss. **Crucially**, we do *not* claim the
envelope is itself bowl-shaped: that would require additional topological
assumptions on `E` (`[ContinuousNeg E]`, `[ContinuousSMul ℝ E]`) that the
Step B/D consumer does not need — only lsc of the envelope is needed for
Portmanteau, plus `lscEnvelope_le` for the inequality chain.

Proof: standard double-liminf argument. For each `c ≤ liminf L (𝓝 x)`,
take open `V ⊆ U` with `x ∈ V` and `∀ z ∈ U, c ≤ L z`; then for every
`y ∈ V`, `V ∈ 𝓝 y`, giving `c ≤ liminf L (𝓝 y)`. Hence `c` is below the
liminf of `lscEnvelope L` at `x`. -/
lemma lowerSemicontinuous_lscEnvelope [TopologicalSpace E] (L : E → ℝ≥0∞) :
    LowerSemicontinuous (lscEnvelope L) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  change Filter.liminf L (𝓝 x) ≤ Filter.liminf (lscEnvelope L) (𝓝 x)
  rw [Filter.liminf_eq, Filter.liminf_eq]
  refine sSup_le_sSup ?_
  intro c hc
  -- hc : ∀ᶠ z in 𝓝 x, c ≤ L z
  -- want: ∀ᶠ y in 𝓝 x, c ≤ lscEnvelope L y = liminf L (𝓝 y)
  obtain ⟨U, hU_mem, hU_le⟩ := Filter.eventually_iff_exists_mem.mp hc
  rw [mem_nhds_iff] at hU_mem
  obtain ⟨V, hVU, hV_open, hxV⟩ := hU_mem
  rw [Set.mem_setOf_eq, Filter.eventually_iff_exists_mem]
  refine ⟨V, hV_open.mem_nhds hxV, fun y hyV => ?_⟩
  change c ≤ lscEnvelope L y
  unfold lscEnvelope
  rw [Filter.liminf_eq]
  exact le_sSup (s := {a | ∀ᶠ z in 𝓝 y, a ≤ L z})
    (Filter.eventually_iff_exists_mem.mpr
      ⟨V, hV_open.mem_nhds hyV, fun z hzV => hU_le z (hVU hzV)⟩)

omit [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] in
/-- For real-domain bowl-shaped `L : ℝ → ℝ≥0∞`, `0 ≤ x ≤ y` implies `L x ≤ L y`.

Proof: `-y` and `y` are both in the sublevel set `{u | L u ≤ L y}` (by symmetry
of `L`), and `x = t · y + (1 - t) · (-y)` with `t := (x + y)/(2y) ∈ [1/2, 1]`
when `y > 0`, giving `x` as a convex combination of the two. By
`convex_sublevel`, `L x ≤ L y`. The `y = 0` case forces `x = 0`. -/
lemma mono_on_Ici_zero {L : ℝ → ℝ≥0∞}
    (hL : BowlShaped (E := ℝ) L) :
    ∀ ⦃x y : ℝ⦄, 0 ≤ x → x ≤ y → L x ≤ L y := by
  intro x y hx hxy
  have hy : 0 ≤ y := le_trans hx hxy
  rcases eq_or_lt_of_le hy with hy0 | hy_pos
  · have hy_eq : y = 0 := hy0.symm
    have hx_eq : x = 0 := le_antisymm (by rw [hy_eq] at hxy; exact hxy) hx
    rw [hx_eq, hy_eq]
  · have h2y_pos : (0 : ℝ) < 2 * y := by linarith
    set t : ℝ := (x + y) / (2 * y) with ht_def
    have ht0 : 0 ≤ t := by
      have hnum : (0 : ℝ) ≤ x + y := by linarith
      exact div_nonneg hnum (le_of_lt h2y_pos)
    have ht1 : t ≤ 1 := by
      rw [ht_def, div_le_one h2y_pos]
      linarith
    have hcombo : t * y + (1 - t) * (-y) = x := by
      rw [ht_def]
      have hy_ne : (2 * y) ≠ 0 := ne_of_gt h2y_pos
      field_simp
      ring
    have hy_mem : y ∈ {u : ℝ | L u ≤ L y} := show L y ≤ L y from le_refl _
    have hny_mem : (-y) ∈ {u : ℝ | L u ≤ L y} := show L (-y) ≤ L y from (hL.symm y).le
    have h_in : t • y + (1 - t) • (-y) ∈ {u : ℝ | L u ≤ L y} :=
      hL.convex_sublevel (L y) hy_mem hny_mem ht0
        (by linarith) (by ring)
    have h_smul1 : (t : ℝ) • y = t * y := rfl
    have h_smul2 : ((1 - t) : ℝ) • (-y) = (1 - t) * (-y) := rfl
    rw [h_smul1, h_smul2, hcombo] at h_in
    exact h_in

omit [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] in
/-- For real-domain bowl-shaped `L : ℝ → ℝ≥0∞`, `|x| ≤ |y|` implies `L x ≤ L y`. -/
lemma le_of_abs_le {L : ℝ → ℝ≥0∞}
    (hL : BowlShaped (E := ℝ) L) {x y : ℝ} (h_abs : |x| ≤ |y|) :
    L x ≤ L y := by
  have hLx : L x = L (|x|) := by
    rcases abs_choice x with hx | hx
    · rw [hx]
    · rw [hx, hL.symm]
  have hLy : L y = L (|y|) := by
    rcases abs_choice y with hy | hy
    · rw [hy]
    · rw [hy, hL.symm]
  rw [hLx, hLy]
  exact hL.mono_on_Ici_zero (abs_nonneg x) h_abs

omit [AddCommGroup E] [Module ℝ E] [MeasurableSpace E] in
/-- **Real-line uniform continuity from bowl-shape + continuity + finite bound.**

For `L : ℝ → ℝ≥0∞` that is bowl-shaped, continuous, and uniformly bounded
above by some `M_bound ≠ ⊤`, the real-valued companion `fun x => (L x).toReal`
is uniformly continuous on `ℝ`. -/
lemma uniformContinuous_toReal_of_bdd_cont {L : ℝ → ℝ≥0∞}
    (hL : BowlShaped (E := ℝ) L) (hL_cont : Continuous L)
    {M_bound : ℝ≥0∞} (hM : M_bound ≠ ⊤) (hL_le : ∀ x, L x ≤ M_bound) :
    UniformContinuous (fun x => (L x).toReal) := by
  set f : ℝ → ℝ := fun x => (L x).toReal with hf_def
  have hL_ne_top : ∀ x, L x ≠ ⊤ := fun x => ne_top_of_le_ne_top hM (hL_le x)
  have hf_cont : Continuous f := by
    refine continuous_iff_continuousAt.mpr (fun x => ?_)
    have h_inner : ContinuousAt L x := hL_cont.continuousAt
    have h_outer : ContinuousAt ENNReal.toReal (L x) :=
      ENNReal.continuousAt_toReal (hL_ne_top x)
    exact h_outer.comp h_inner
  have hf_abs_mono : ∀ x y : ℝ, |x| ≤ |y| → f x ≤ f y := fun x y h =>
    ENNReal.toReal_mono (hL_ne_top y) (hL.le_of_abs_le h)
  have hf_bdd : ∀ x, f x ≤ M_bound.toReal :=
    fun x => ENNReal.toReal_mono hM (hL_le x)
  have hf_mono_Ici : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → f a ≤ f b := fun a b ha hab => by
    refine hf_abs_mono a b ?_
    rw [abs_of_nonneg ha, abs_of_nonneg (le_trans ha hab)]; exact hab
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  set Linf : ℝ := ⨆ n : ℕ, f n with hLinf_def
  have h_bddAbove : BddAbove (Set.range fun n : ℕ => f n) :=
    ⟨M_bound.toReal, fun _ ⟨n, hn⟩ => hn ▸ hf_bdd _⟩
  have h_seq_mono : Monotone (fun n : ℕ => f n) := fun a b hab =>
    hf_mono_Ici (Nat.cast_nonneg a) (by exact_mod_cast hab)
  have h_seq_tendsto : Tendsto (fun n : ℕ => f n) atTop (𝓝 Linf) :=
    tendsto_atTop_ciSup h_seq_mono h_bddAbove
  have hf_le_Linf : ∀ x, f x ≤ Linf := by
    intro x
    have h1 : f x ≤ f ((⌈|x|⌉₊ : ℕ) : ℝ) := by
      refine hf_abs_mono x _ ?_
      have h_nn : (0 : ℝ) ≤ ((⌈|x|⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [abs_of_nonneg h_nn]
      exact Nat.le_ceil _
    have h2 : f ((⌈|x|⌉₊ : ℕ) : ℝ) ≤ Linf := le_ciSup h_bddAbove ⌈|x|⌉₊
    exact h1.trans h2
  obtain ⟨N, hN_dist⟩ : ∃ N : ℕ, |f N - Linf| < ε / 4 := by
    have h_metric := (Metric.tendsto_atTop.mp h_seq_tendsto) (ε / 4) hε4
    obtain ⟨N₀, hN₀⟩ := h_metric
    refine ⟨N₀, ?_⟩
    rw [← Real.dist_eq]; exact hN₀ N₀ le_rfl
  have hN : Linf - ε / 4 < f N := by
    have h_abs := abs_lt.mp hN_dist
    linarith [h_abs.1]
  set K : ℝ := (N : ℝ) with hK_def
  have hK_nn : 0 ≤ K := Nat.cast_nonneg N
  have h_far : ∀ x, K ≤ |x| → Linf - ε / 4 ≤ f x ∧ f x ≤ Linf := by
    intro x hxK
    refine ⟨?_, hf_le_Linf x⟩
    have h1 : f K ≤ f x := by
      refine hf_abs_mono K x ?_
      rw [abs_of_nonneg hK_nn]; exact hxK
    linarith
  set K' : ℝ := K + 2 with hK'_def
  have h_compact : IsCompact (Set.Icc (-K') K') := isCompact_Icc
  have h_uc_compact :
      UniformContinuousOn f (Set.Icc (-K') K') :=
    h_compact.uniformContinuousOn_of_continuous hf_cont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at h_uc_compact
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := h_uc_compact (ε / 2) (by linarith)
  refine ⟨min δ₀ 1, lt_min hδ₀_pos one_pos, ?_⟩
  intro x y hxy
  have hxy_min : dist x y < δ₀ := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy_one : dist x y < 1 := lt_of_lt_of_le hxy (min_le_right _ _)
  by_cases hx_in : |x| ≤ K + 1
  · by_cases hy_in : |y| ≤ K + 1
    · have hx_in' : x ∈ Set.Icc (-K') K' := by
        rw [Set.mem_Icc]; refine ⟨?_, ?_⟩ <;>
          [linarith [abs_le.mp hx_in |>.1]; linarith [abs_le.mp hx_in |>.2]]
      have hy_in' : y ∈ Set.Icc (-K') K' := by
        rw [Set.mem_Icc]; refine ⟨?_, ?_⟩ <;>
          [linarith [abs_le.mp hy_in |>.1]; linarith [abs_le.mp hy_in |>.2]]
      have := hδ₀ x hx_in' y hy_in' hxy_min
      rw [Real.dist_eq] at this ⊢
      linarith
    · push Not at hy_in
      have hy_far : K ≤ |y| := by linarith
      have hx_far : K ≤ |x| := by
        have h_abs_diff : |(|x| - |y|)| ≤ |x - y| := abs_abs_sub_abs_le_abs_sub x y
        have h_left : |y| - |x| ≤ |x - y| := by
          have := neg_le_of_abs_le h_abs_diff
          linarith
        have h_xy_lt : |x - y| < 1 := by
          rw [Real.dist_eq] at hxy_one; exact hxy_one
        linarith
      have ⟨h_x_lo, h_x_hi⟩ := h_far x hx_far
      have ⟨h_y_lo, h_y_hi⟩ := h_far y hy_far
      rw [Real.dist_eq]
      have : |f x - f y| ≤ ε / 2 := by
        rw [abs_le]
        refine ⟨?_, ?_⟩ <;> linarith
      linarith
  · push Not at hx_in
    have hx_far : K ≤ |x| := by linarith
    have hy_far : K ≤ |y| := by
      have h_abs_diff : |(|x| - |y|)| ≤ |x - y| := abs_abs_sub_abs_le_abs_sub x y
      have h_left : |x| - |y| ≤ |x - y| := by
        have := le_abs_self (|x| - |y|)
        linarith [h_abs_diff]
      have h_xy_lt : |x - y| < 1 := by
        rw [Real.dist_eq] at hxy_one; exact hxy_one
      linarith
    have ⟨h_x_lo, h_x_hi⟩ := h_far x hx_far
    have ⟨h_y_lo, h_y_hi⟩ := h_far y hy_far
    rw [Real.dist_eq]
    have : |f x - f y| ≤ ε / 2 := by
      rw [abs_le]
      refine ⟨?_, ?_⟩ <;> linarith
    linarith

end BowlShaped

end AsymptoticStatistics
