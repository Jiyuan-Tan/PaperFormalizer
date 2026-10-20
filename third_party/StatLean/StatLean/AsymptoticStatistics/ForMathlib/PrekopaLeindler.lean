module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
Asymptotic Statistics — Prékopa-Leindler inequality.

The functional generalisation of Brunn-Minkowski. Foundational tool for
log-concave measure theory; the route by which we prove Anderson's lemma
(`ForMathlib/Anderson.lean`) for multivariate Gaussian shifts.

Mathlib has neither Prékopa-Leindler nor Brunn-Minkowski directly. We build
the 1D form first, then n-dim by induction over Fubini (each marginal is
log-concave by 1D PL applied fibre-wise).

The proof of `prekopaLeindler_1d` is organized through named lemmas for the
level-set inclusion, the one-dimensional Brunn-Minkowski inequality, the
resulting level-measure bound, and the layer-cake integral assembly.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise Topology

namespace AsymptoticStatistics

/-! ## 1D Prékopa-Leindler — sub-helpers

The 1D PL proof factors as four named steps:

1. **Level-set inclusion** (`prekopaLeindler_1d_levelInclusion`): for `α > 0`,
   `t • {f > α} + (1-t) • {g > α} ⊆ {h > α}`, via the pointwise hypothesis
   on `h` and the trivial identity `α^t · α^(1-t) = α`.

2. **1D Brunn-Minkowski** (`oneDim_brunn_minkowski_le`): for
   nonempty measurable `A, B ⊆ ℝ` with `A + B ⊆ C` measurable,
   `volume A + volume B ≤ volume C`. The proof first treats compact sets and
   then passes to measurable sets by inner regularity, separately handling
   zero and infinite measure.

3. **Level-measure bound** (`prekopaLeindler_1d_levelMeasureBound`):
   combines (1) + (2) + smul-set scaling
   (`Measure.addHaar_smul_of_nonneg` with `finrank ℝ ℝ = 1`) to give
   `t · m({f>α}) + (1-t) · m({g>α}) ≤ m({h>α})` for `α > 0`.

4. **Integral assembly**: layer-cake on ENNReal-valued functions
   (`lintegral_eq_lintegral_meas_lt_ennreal`, reducible from Mathlib's
   ℝ-valued form via truncation + MCT) plus weighted AM-GM lifted to ENNReal
   (`ennreal_geom_mean_le_arith_mean2_weighted`, lifted from
   `Real.geom_mean_le_arith_mean2_weighted`).
-/

/-- **Level-set inclusion (1D PL).**

For `t ∈ (0, 1)` and finite `α > 0`, if `f, g, h : ℝ → ℝ≥0∞` satisfy the PL
pointwise hypothesis, then for `x ∈ {f > α}` and `y ∈ {g > α}`:
  `h(t x + (1-t) y) ≥ f(x)^t · g(y)^(1-t) > α^t · α^(1-t) = α`.

Equivalently:
  `t • {x | α < f x} + (1-t) • {y | α < g y} ⊆ {z | α < h z}`. -/
private theorem prekopaLeindler_1d_levelInclusion
    {f g h : ℝ → ℝ≥0∞}
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤) :
    t • {x | α < f x} + (1 - t) • {y | α < g y} ⊆ {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  rintro z hz
  rw [Set.mem_add] at hz
  obtain ⟨_, hu, _, hv, rfl⟩ := hz
  rw [Set.mem_smul_set] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  -- `hx : α < f x`, `hy : α < g y`. Goal: `α < h (t * x + (1 - t) * y)`.
  simp only [smul_eq_mul, Set.mem_setOf_eq] at hx hy ⊢
  -- Step 1: `α = α ^ t * α ^ (1 - t)` (using `α ∈ (0, ∞)`).
  have h_alpha_split : α = α ^ t * α ^ (1 - t) := by
    rw [← ENNReal.rpow_add t (1 - t) hα_pos.ne' hα_top]
    have ht_one : t + (1 - t) = (1 : ℝ) := by ring
    rw [ht_one, ENNReal.rpow_one]
  -- Step 2: `α ^ t < f(x) ^ t` and `α ^ (1-t) < g(y) ^ (1-t)`.
  have h1 : α ^ t < f x ^ t := ENNReal.rpow_lt_rpow hx ht_pos
  have h2 : α ^ (1 - t) < g y ^ (1 - t) := ENNReal.rpow_lt_rpow hy h1t_pos
  -- Step 3: multiply.
  have h3 : α ^ t * α ^ (1 - t) < f x ^ t * g y ^ (1 - t) := ENNReal.mul_lt_mul h1 h2
  -- Step 4: chain with the PL hypothesis at (x, y).
  calc α = α ^ t * α ^ (1 - t) := h_alpha_split
    _ < f x ^ t * g y ^ (1 - t) := h3
    _ ≤ h (t * x + (1 - t) * y) := h_le x y

/-- **1D Brunn-Minkowski (compact case).**

For nonempty compact `K_A, K_B ⊆ ℝ`:
$$\text{vol}(K_A) + \text{vol}(K_B) \le \text{vol}(K_A + K_B).$$

**Proof**: let `a := sSup K_A` and `b := sInf K_B` (attained on compact). Then
`K_A ⊆ Iic a` and `K_B ⊆ Ici b`. Define translates `U := K_A + {b}` and
`V := {a} + K_B`. Both `U, V ⊆ K_A + K_B` (using `b ∈ K_B`, `a ∈ K_A`). Then:
- `U ⊆ Iic (a + b)`, `V ⊆ Ici (a + b)`, so `U ∩ V ⊆ {a + b}`, hence
  `vol(U ∩ V) = 0` (Lebesgue is non-atomic).
- `vol U = vol K_A`, `vol V = vol K_B` by translation invariance.
- `vol(U ∪ V) + vol(U ∩ V) = vol U + vol V`, so `vol(U ∪ V) = vol U + vol V`.
- `U ∪ V ⊆ K_A + K_B`, hence `vol(K_A + K_B) ≥ vol(U ∪ V) = vol K_A + vol K_B`.
-/
private lemma oneDim_brunn_minkowski_compact_le
    {K_A K_B : Set ℝ}
    (hA_compact : IsCompact K_A) (hB_compact : IsCompact K_B)
    (hA_ne : K_A.Nonempty) (hB_ne : K_B.Nonempty) :
    volume K_A + volume K_B ≤ volume (K_A + K_B) := by
  -- `a := sup K_A`, `b := inf K_B`, both attained on compact.
  set a := sSup K_A with ha_def
  set b := sInf K_B with hb_def
  have ha_mem : a ∈ K_A := hA_compact.sSup_mem hA_ne
  have hb_mem : b ∈ K_B := hB_compact.sInf_mem hB_ne
  have hA_le_a : ∀ x ∈ K_A, x ≤ a :=
    fun x hx => le_csSup hA_compact.bddAbove hx
  have hB_ge_b : ∀ y ∈ K_B, b ≤ y :=
    fun y hy => csInf_le hB_compact.bddBelow hy
  -- Translates: `U := K_A + {b}`, `V := {a} + K_B`.
  set U : Set ℝ := K_A + {b} with hU_def
  set V : Set ℝ := {a} + K_B with hV_def
  -- Both `U, V ⊆ K_A + K_B`.
  have hU_sub_AB : U ⊆ K_A + K_B := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    exact ⟨x, hx, b, hb_mem, rfl⟩
  have hV_sub_AB : V ⊆ K_A + K_B := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    exact ⟨a, ha_mem, y, hy, rfl⟩
  -- `vol U = vol K_A` via translation invariance.
  have hU_vol : volume U = volume K_A := by
    rw [hU_def, Set.add_singleton, Set.image_add_right]
    exact MeasureTheory.measure_preimage_add_right volume (-b) K_A
  -- `vol V = vol K_B`.
  have hV_vol : volume V = volume K_B := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact MeasureTheory.measure_preimage_add volume (-a) K_B
  -- `U ⊆ Iic (a + b)`.
  have hU_sub_Iic : U ⊆ Set.Iic (a + b) := by
    rintro _ ⟨x, hx, _, rfl, rfl⟩
    have := hA_le_a x hx
    simp only [Set.mem_Iic]
    linarith
  -- `V ⊆ Ici (a + b)`.
  have hV_sub_Ici : V ⊆ Set.Ici (a + b) := by
    rintro _ ⟨_, rfl, y, hy, rfl⟩
    have := hB_ge_b y hy
    simp only [Set.mem_Ici]
    linarith
  -- `U ∩ V ⊆ {a + b}`.
  have h_inter_sub : U ∩ V ⊆ {a + b} := by
    rintro z ⟨hzU, hzV⟩
    have h1 := hU_sub_Iic hzU
    have h2 := hV_sub_Ici hzV
    simp only [Set.mem_Iic] at h1
    simp only [Set.mem_Ici] at h2
    simp only [Set.mem_singleton_iff]
    linarith
  -- `vol(U ∩ V) ≤ vol{a+b} = 0`.
  have h_inter_zero : volume (U ∩ V) = 0 := by
    apply le_antisymm _ (zero_le)
    calc volume (U ∩ V)
        ≤ volume ({a + b} : Set ℝ) := MeasureTheory.measure_mono h_inter_sub
      _ = 0 := MeasureTheory.measure_singleton (a + b)
  -- `vol(U ∪ V) + vol(U ∩ V) = vol U + vol V` (inclusion-exclusion).
  -- Need `MeasurableSet V`. `V = {a} + K_B`, where `K_B` compact (so closed,
  -- measurable) and `{a}` measurable, but the Minkowski sum need not be.
  -- Workaround: `V = (· + a) '' K_B` (after rewriting via singleton + comm),
  -- which is the image of compact `K_B` under continuous `(· + a)`, hence
  -- compact, hence closed, hence measurable.
  have hV_meas : MeasurableSet V := by
    rw [hV_def, Set.singleton_add, Set.image_add_left]
    exact (hB_compact.measurableSet).preimage (measurable_const_add (-a))
  have h_inc_excl : volume (U ∪ V) + volume (U ∩ V) = volume U + volume V :=
    MeasureTheory.measure_union_add_inter U hV_meas
  -- `vol(U ∪ V) ≤ vol(K_A + K_B)` via monotonicity.
  have h_union_sub : U ∪ V ⊆ K_A + K_B := Set.union_subset hU_sub_AB hV_sub_AB
  have h_union_le : volume (U ∪ V) ≤ volume (K_A + K_B) :=
    MeasureTheory.measure_mono h_union_sub
  -- Assemble: `vol K_A + vol K_B = vol U + vol V = vol(U∪V) + vol(U∩V)
  --            = vol(U∪V) + 0 ≤ vol(K_A + K_B)`.
  calc volume K_A + volume K_B
      = volume U + volume V := by rw [hU_vol, hV_vol]
    _ = volume (U ∪ V) + volume (U ∩ V) := h_inc_excl.symm
    _ = volume (U ∪ V) + 0 := by rw [h_inter_zero]
    _ = volume (U ∪ V) := add_zero _
    _ ≤ volume (K_A + K_B) := h_union_le

/-- **1D Brunn-Minkowski (outer-measure form, sufficient for PL).**

For nonempty Lebesgue-measurable `A, B ⊆ ℝ` and any measurable `C ⊇ A + B`:
$$\text{vol}(A) + \text{vol}(B) \le \text{vol}(C).$$

**Proof**: reduce to compact via inner regularity. For any `ε > 0`, find
compact `K_A ⊆ A, K_B ⊆ B` with `vol A < vol K_A + ε / 2,
vol B < vol K_B + ε / 2`. Then `K_A + K_B ⊆ A + B ⊆ C`, and by the compact
case, `vol K_A + vol K_B ≤ vol(K_A + K_B) ≤ vol C`. Hence
`vol A + vol B ≤ vol K_A + ε/2 + vol K_B + ε/2 ≤ vol C + ε`. Take `ε → 0`.

The `vol A = ⊤` case is handled separately (then `vol K_A → ⊤`, so
`vol C = ⊤`). -/
private theorem oneDim_brunn_minkowski_le
    {A B C : Set ℝ}
    (hA_meas : MeasurableSet A) (hB_meas : MeasurableSet B)
    (_hC_meas : MeasurableSet C)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty)
    (hAB_sub : A + B ⊆ C) :
    volume A + volume B ≤ volume C := by
  -- Pre-step: trivial case `vol A = 0`.
  -- Then `{a₀} + B ⊆ A + B ⊆ C` gives `vol B ≤ vol C`, hence the bound.
  by_cases hA_zero : volume A = 0
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    rw [hA_zero, zero_add]
    calc volume B = volume (({a₀} : Set ℝ) + B) := h_aB_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_aB_sub_C
  -- Pre-step: trivial case `vol B = 0`. Symmetric.
  by_cases hB_zero : volume B = 0
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    rw [hB_zero, add_zero]
    calc volume A = volume (A + ({b₀} : Set ℝ)) := h_Ab_eq.symm
      _ ≤ volume C := MeasureTheory.measure_mono h_Ab_sub_C
  -- Edge case `vol A = ⊤`: show `vol C = ⊤` via inner regularity.
  -- For each compact `K_A ⊆ A`, `K_A + {b₀} ⊆ A + B ⊆ C` with same volume,
  -- so `vol C ≥ ⨆ K compact ⊆ A, vol K = vol A = ⊤`.
  by_cases hA_top : volume A = ⊤
  · obtain ⟨b₀, hb₀⟩ := hB_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hA_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume A = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hA_meas
    calc (⊤ : ℝ≥0∞)
        = volume A := hA_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_A => iSup_le fun hK_A_sub => iSup_le fun _ => ?_
          have h_KA_b0_sub : K_A + ({b₀} : Set ℝ) ⊆ C :=
            fun z ⟨x, hx, _, rfl, hxz⟩ => hAB_sub ⟨x, hK_A_sub hx, b₀, hb₀, hxz⟩
          have h_KA_b0_eq : volume (K_A + ({b₀} : Set ℝ)) = volume K_A := by
            rw [Set.add_singleton, Set.image_add_right]
            exact MeasureTheory.measure_preimage_add_right volume (-b₀) K_A
          calc volume K_A
              = volume (K_A + ({b₀} : Set ℝ)) := h_KA_b0_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_KA_b0_sub
  -- Symmetric to vol A = ⊤ case.
  by_cases hB_top : volume B = ⊤
  · obtain ⟨a₀, ha₀⟩ := hA_ne
    suffices h_C_top : volume C = ⊤ by
      rw [hB_top, h_C_top]; exact le_top
    apply top_le_iff.mp
    have h_inner :
        volume B = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K :=
      MeasureTheory.Measure.InnerRegularWRT.measure_eq_iSup
        MeasureTheory.Measure.InnerRegular.innerRegular hB_meas
    calc (⊤ : ℝ≥0∞)
        = volume B := hB_top.symm
      _ = ⨆ (K : Set ℝ), ⨆ (_ : K ⊆ B), ⨆ (_ : IsCompact K), volume K := h_inner
      _ ≤ volume C := by
          refine iSup_le fun K_B => iSup_le fun hK_B_sub => iSup_le fun _ => ?_
          have h_a0_KB_sub : ({a₀} : Set ℝ) + K_B ⊆ C :=
            fun z ⟨_, rfl, y, hy, hyz⟩ => hAB_sub ⟨a₀, ha₀, y, hK_B_sub hy, hyz⟩
          have h_a0_KB_eq : volume (({a₀} : Set ℝ) + K_B) = volume K_B := by
            rw [Set.singleton_add, Set.image_add_left]
            exact MeasureTheory.measure_preimage_add volume (-a₀) K_B
          calc volume K_B
              = volume (({a₀} : Set ℝ) + K_B) := h_a0_KB_eq.symm
            _ ≤ volume C := MeasureTheory.measure_mono h_a0_KB_sub
  -- Both finite, both nonzero. Use ε-approximation.
  -- Key: with vol A > 0 and vol A < ⊤, can pick K_A nonempty (vol K_A > 0).
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _hC_top
  -- Pick δ small enough that `vol K_A + δ < vol A` is impossible (so K_A
  -- nonempty automatic). Concretely: δ := min(ε/2, vol A / 2, vol B / 2).
  -- Simpler: just take δ := ε/2 and handle empty K_A by direct bound.
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2 with hδ_def
  have hδ_pos : (0 : ℝ≥0∞) < δ := by
    rw [hδ_def]
    refine ENNReal.div_pos ?_ (by norm_num)
    exact_mod_cast hε.ne'
  have hδ_ne : δ ≠ 0 := hδ_pos.ne'
  have hδ_le : δ ≤ ε := by
    rw [hδ_def]; exact ENNReal.half_le_self
  -- Inner regularity for A and B.
  obtain ⟨K_A, hK_A_sub, hK_A_compact, hK_A_lt⟩ :=
    hA_meas.exists_isCompact_lt_add hA_top hδ_ne
  obtain ⟨K_B, hK_B_sub, hK_B_compact, hK_B_lt⟩ :=
    hB_meas.exists_isCompact_lt_add hB_top hδ_ne
  -- Empty K_A case: handle via vol A < δ ≤ ε bound.
  rcases K_A.eq_empty_or_nonempty with hKA_empty | hKA_ne
  · -- `vol K_A = 0`, so `vol A < δ`. Combined with `vol B ≤ vol C` gives the bound.
    rw [hKA_empty, MeasureTheory.measure_empty, zero_add] at hK_A_lt
    -- vol A < δ ≤ ε
    have hA_le_ε : volume A ≤ (ε : ℝ≥0∞) := le_trans hK_A_lt.le hδ_le
    -- vol B ≤ vol C: pick a₀ ∈ A, {a₀} + B ⊆ C, measure-preserving.
    obtain ⟨a₀, ha₀⟩ := hA_ne
    have h_aB_sub_C : ({a₀} : Set ℝ) + B ⊆ C := fun z ⟨_, rfl, y, hy, hyz⟩ =>
      hAB_sub ⟨a₀, ha₀, y, hy, hyz⟩
    have h_aB_eq : volume (({a₀} : Set ℝ) + B) = volume B := by
      rw [Set.singleton_add, Set.image_add_left]
      exact MeasureTheory.measure_preimage_add volume (-a₀) B
    have hB_le_C : volume B ≤ volume C := by
      rw [← h_aB_eq]; exact MeasureTheory.measure_mono h_aB_sub_C
    calc volume A + volume B ≤ (ε : ℝ≥0∞) + volume C := add_le_add hA_le_ε hB_le_C
      _ = volume C + (ε : ℝ≥0∞) := add_comm _ _
  rcases K_B.eq_empty_or_nonempty with hKB_empty | hKB_ne
  · -- Symmetric to the empty K_A case.
    rw [hKB_empty, MeasureTheory.measure_empty, zero_add] at hK_B_lt
    have hB_le_ε : volume B ≤ (ε : ℝ≥0∞) := le_trans hK_B_lt.le hδ_le
    obtain ⟨b₀, hb₀⟩ := hB_ne
    have h_Ab_sub_C : A + ({b₀} : Set ℝ) ⊆ C := fun z ⟨x, hx, _, rfl, hxz⟩ =>
      hAB_sub ⟨x, hx, b₀, hb₀, hxz⟩
    have h_Ab_eq : volume (A + ({b₀} : Set ℝ)) = volume A := by
      rw [Set.add_singleton, Set.image_add_right]
      exact MeasureTheory.measure_preimage_add_right volume (-b₀) A
    have hA_le_C : volume A ≤ volume C := by
      rw [← h_Ab_eq]; exact MeasureTheory.measure_mono h_Ab_sub_C
    exact add_le_add hA_le_C hB_le_ε
  · -- Generic case: both K_A, K_B nonempty.
    have hKAB_sub : K_A + K_B ⊆ C :=
      fun z ⟨x, hx, y, hy, hxyz⟩ =>
        hAB_sub ⟨x, hK_A_sub hx, y, hK_B_sub hy, hxyz⟩
    have h_compact_bm := oneDim_brunn_minkowski_compact_le
      hK_A_compact hK_B_compact hKA_ne hKB_ne
    have h_KAKB_le_C : volume (K_A + K_B) ≤ volume C :=
      MeasureTheory.measure_mono hKAB_sub
    -- `vol A + vol B ≤ (vol K_A + δ) + (vol K_B + δ) ≤ vol C + 2δ ≤ vol C + ε`.
    have h_2δ_le_ε : (2 : ℝ≥0∞) * δ ≤ (ε : ℝ≥0∞) := by
      rw [hδ_def]; exact ENNReal.mul_div_le
    calc volume A + volume B
        ≤ (volume K_A + δ) + (volume K_B + δ) := by gcongr
      _ = (volume K_A + volume K_B) + (δ + δ) := by ring
      _ = (volume K_A + volume K_B) + 2 * δ := by ring
      _ ≤ volume C + 2 * δ := by
          gcongr
          exact le_trans h_compact_bm h_KAKB_le_C
      _ ≤ volume C + (ε : ℝ≥0∞) := by gcongr

/-- **Level-measure bound (1D PL, both level sets nonempty).**

For `α ∈ (0, ∞)` with both `A_α := {x | α < f x}` and `B_α := {y | α < g y}`
nonempty:
$$t \cdot \text{vol}(A_\alpha) + (1-t) \cdot \text{vol}(B_\alpha)
  \;\le\; \text{vol}(\{z \mid \alpha < h(z)\}).$$

Combines `prekopaLeindler_1d_levelInclusion` (set inclusion) +
`oneDim_brunn_minkowski_le` (BM measure inequality) +
`Measure.addHaar_smul_of_nonneg` (smul scaling: `vol(c • s) = ofReal(c) * vol(s)`
for `c ≥ 0` since `finrank ℝ ℝ = 1`).

Note: this lemma assumes both level sets are nonempty. In the ess-sup-aligned
assembly, for `α` below the common essential supremum both level sets have
positive measure and hence are nonempty, so this lemma applies. At or above the
common essential supremum, both level-set measures are zero (although the sets
need not be empty), so their contribution to the pointwise bound vanishes. -/
private theorem prekopaLeindler_1d_levelMeasureBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    {α : ℝ≥0∞} (hα_pos : 0 < α) (hα_top : α ≠ ⊤)
    (hA_ne : ({x | α < f x} : Set ℝ).Nonempty)
    (hB_ne : ({y | α < g y} : Set ℝ).Nonempty) :
    ENNReal.ofReal t * volume {x | α < f x}
      + ENNReal.ofReal (1 - t) * volume {y | α < g y}
      ≤ volume {z | α < h z} := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set A : Set ℝ := {x | α < f x} with hA_def
  set B : Set ℝ := {y | α < g y} with hB_def
  set C : Set ℝ := {z | α < h z} with hC_def
  -- Level sets are measurable via `f, g, h` measurable + `Ioi α` measurable.
  have hA_meas : MeasurableSet A := hf_meas measurableSet_Ioi
  have hB_meas : MeasurableSet B := hg_meas measurableSet_Ioi
  have hC_meas : MeasurableSet C := hh_meas measurableSet_Ioi
  -- Inclusion: `t • A + (1 - t) • B ⊆ C` from level-set inclusion helper.
  have h_incl : t • A + (1 - t) • B ⊆ C :=
    prekopaLeindler_1d_levelInclusion ht_pos ht_lt h_le hα_pos hα_top
  -- Smul-set measurability (uses `t ≠ 0`).
  have htA_meas : MeasurableSet (t • A) :=
    hA_meas.const_smul_of_ne_zero ht_pos.ne'
  have h1tB_meas : MeasurableSet ((1 - t) • B) :=
    hB_meas.const_smul_of_ne_zero h1t_pos.ne'
  -- Smul-set nonempty.
  have htA_ne : (t • A).Nonempty := Set.smul_set_nonempty.mpr hA_ne
  have h1tB_ne : ((1 - t) • B).Nonempty := Set.smul_set_nonempty.mpr hB_ne
  -- 1D BM applied to `t • A`, `(1-t) • B`, `C`.
  have h_bm : volume (t • A) + volume ((1 - t) • B) ≤ volume C :=
    oneDim_brunn_minkowski_le htA_meas h1tB_meas hC_meas htA_ne h1tB_ne h_incl
  -- Smul-set measure scaling: `vol(c • S) = ofReal c * vol(S)` for `c ≥ 0`,
  -- since `finrank ℝ ℝ = 1`.
  have h_finrank : Module.finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ
  have h_smul_t : volume (t • A) = ENNReal.ofReal t * volume A := by
    rw [Measure.addHaar_smul_of_nonneg volume ht_pos.le A, h_finrank, pow_one]
  have h_smul_1t : volume ((1 - t) • B) = ENNReal.ofReal (1 - t) * volume B := by
    rw [Measure.addHaar_smul_of_nonneg volume h1t_pos.le B, h_finrank, pow_one]
  rw [← h_smul_t, ← h_smul_1t]
  exact h_bm

/-- **Layer-cake for ENNReal-valued lintegral.**

For measurable `f : ℝ → ℝ≥0∞`,
$$\int^- f \, d\lambda
  \;=\; \int^-_{\alpha \in (0, \infty)} \lambda(\{x \mid \alpha < f(x)\})
  \, d\alpha.$$

Mathlib has this for `f : α → ℝ` (`MeasureTheory.lintegral_eq_lintegral_meas_lt`)
but not directly for ENNReal-valued `f`. Derived here via truncation
`f_n := f ⊓ n` + monotone convergence on both sides + Mathlib's ℝ-valued
form applied to `f_n.toReal` per `n`. -/
private theorem lintegral_eq_lintegral_meas_lt_ennreal
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x} := by
  -- Truncation: `fN n x := f x ⊓ n` is bounded, monotone in `n`, sup = `f`.
  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  have hfN_meas : ∀ n, Measurable (fN n) :=
    fun n => hf.inf measurable_const
  have hfN_lt_top : ∀ n x, fN n x ≠ ⊤ :=
    fun n x => ne_top_of_le_ne_top ENNReal.coe_ne_top inf_le_right
  have hfN_mono : Monotone fN := by
    intro m n hmn x
    exact inf_le_inf_left _ (by exact_mod_cast hmn)
  have hfN_iSup_eq : ∀ x, ⨆ n, fN n x = f x := fun x => by
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  -- LHS via MCT.
  have hLHS : ∫⁻ x, f x = ⨆ n, ∫⁻ x, fN n x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas hfN_mono]
    exact MeasureTheory.lintegral_congr fun x => (hfN_iSup_eq x).symm
  -- For each `n`, layer cake on `fN n` via Mathlib's ℝ-version + transfer
  -- `ENNReal.ofReal ((fN n x).toReal) = fN n x` (using `fN n x ≠ ⊤`).
  have h_per_n : ∀ n, ∫⁻ x, fN n x =
      ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    have h_eq : ∫⁻ x, fN n x = ∫⁻ x, ENNReal.ofReal ((fN n x).toReal) :=
      MeasureTheory.lintegral_congr fun x => (ENNReal.ofReal_toReal (hfN_lt_top n x)).symm
    rw [h_eq, MeasureTheory.lintegral_eq_lintegral_meas_lt volume
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        ((hfN_meas n).ennreal_toReal.aemeasurable)]
    -- Goal: `∫⁻ α in Ioi 0, vol {x | α < (fN n x).toReal}
    --      = ∫⁻ α in Ioi 0, vol {x | ENNReal.ofReal α < fN n x}`.
    apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
    intro α hα
    have hα_nn : (0 : ℝ) ≤ α := le_of_lt hα
    change volume {x | α < (fN n x).toReal}
        = volume {x | ENNReal.ofReal α < fN n x}
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mpr h
      rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)] at this
    · have h' : ENNReal.ofReal α < ENNReal.ofReal ((fN n x).toReal) := by
        rwa [ENNReal.ofReal_toReal (hfN_lt_top n x)]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα_nn).mp h'
  -- RHS: rewrite `vol{ofReal α < f x}` as `⨆ n vol{ofReal α < fN n x}` via
  -- `Monotone.measure_iUnion` + `⋃ n {ofReal α < fN n x} = {ofReal α < f x}`,
  -- then swap iSup with `∫⁻ α` via MCT.
  have h_set_mono : ∀ α : ℝ,
      Monotone fun n : ℕ => {x | ENNReal.ofReal α < fN n x} := by
    intro α m n hmn x hx
    exact lt_of_lt_of_le hx (hfN_mono hmn x)
  have h_set_iUnion : ∀ α : ℝ,
      ⋃ n : ℕ, {x | ENNReal.ofReal α < fN n x}
        = {x | ENNReal.ofReal α < f x} := by
    intro α
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨fun ⟨n, hn⟩ => lt_of_lt_of_le hn (le_trans inf_le_left le_rfl), ?_⟩
    intro hx
    rw [← hfN_iSup_eq x] at hx
    exact lt_iSup_iff.mp hx
  -- Measurability of `α ↦ vol {ofReal α < fN n x}`: use Tonelli's
  -- measurability lemma `measurable_measure_prodMk_left`.
  have h_meas_vol : ∀ n,
      Measurable fun α : ℝ => volume {x | ENNReal.ofReal α < fN n x} := by
    intro n
    -- The set `{(α, x) | ofReal α < fN n x}` is measurable in `ℝ × ℝ`.
    have h_set_meas : MeasurableSet
        {p : ℝ × ℝ | ENNReal.ofReal p.1 < fN n p.2} :=
      measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        ((hfN_meas n).comp measurable_snd)
    -- Apply `measurable_measure_prodMk_left` to volume on `ℝ` (sfinite).
    exact measurable_measure_prodMk_left h_set_meas
  have hRHS : ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < f x}
        = ⨆ n, ∫⁻ α in Ioi (0 : ℝ), volume {x | ENNReal.ofReal α < fN n x} := by
    rw [show (fun α => volume {x | ENNReal.ofReal α < f x})
          = fun α => ⨆ n, volume {x | ENNReal.ofReal α < fN n x} from
        funext fun α => by rw [← h_set_iUnion α,
          (h_set_mono α).measure_iUnion]]
    exact MeasureTheory.lintegral_iSup (fun n => h_meas_vol n)
      (fun m n hmn α => MeasureTheory.measure_mono (h_set_mono α hmn))
  rw [hLHS, hRHS]
  exact iSup_congr h_per_n

/-- **ENNReal weighted AM-GM (2-form).**

For `t ∈ (0, 1)` and `a, b : ℝ≥0∞`:
$$a^t \cdot b^{1-t} \;\le\; t \cdot a + (1-t) \cdot b.$$

Lifted from `Real.geom_mean_le_arith_mean2_weighted` via `toReal`/`ofReal`,
with `⊤` edge cases handled by absorbing into RHS. -/
private theorem ennreal_geom_mean_le_arith_mean2_weighted
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (a b : ℝ≥0∞) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  by_cases ha : a = ⊤
  · subst ha
    have h_rhs : ENNReal.ofReal t * ⊤ + ENNReal.ofReal (1 - t) * b = ⊤ := by
      have : ENNReal.ofReal t ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  by_cases hb : b = ⊤
  · subst hb
    have h_rhs : ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * ⊤ = ⊤ := by
      have : ENNReal.ofReal (1 - t) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero]; linarith
      simp [ENNReal.mul_top this]
    rw [h_rhs]; exact le_top
  -- Both finite; lift to Real.
  set A : ℝ := a.toReal with hA_def
  set B : ℝ := b.toReal with hB_def
  have hA_nn : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB_nn : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hofa : ENNReal.ofReal A = a := ENNReal.ofReal_toReal ha
  have hofb : ENNReal.ofReal B = b := ENNReal.ofReal_toReal hb
  have h_real : A ^ t * B ^ (1 - t) ≤ t * A + (1 - t) * B :=
    Real.geom_mean_le_arith_mean2_weighted ht_pos.le h1t_pos.le hA_nn hB_nn
      (by linarith)
  have hAt_nn : (0 : ℝ) ≤ A ^ t := Real.rpow_nonneg hA_nn t
  have hBt_nn : (0 : ℝ) ≤ B ^ (1 - t) := Real.rpow_nonneg hB_nn (1 - t)
  calc a ^ t * b ^ (1 - t)
      = ENNReal.ofReal A ^ t * ENNReal.ofReal B ^ (1 - t) := by rw [hofa, hofb]
    _ = ENNReal.ofReal (A ^ t) * ENNReal.ofReal (B ^ (1 - t)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA_nn ht_pos.le,
            ENNReal.ofReal_rpow_of_nonneg hB_nn h1t_pos.le]
    _ = ENNReal.ofReal (A ^ t * B ^ (1 - t)) := by
        rw [← ENNReal.ofReal_mul hAt_nn]
    _ ≤ ENNReal.ofReal (t * A + (1 - t) * B) := ENNReal.ofReal_le_ofReal h_real
    _ = ENNReal.ofReal (t * A) + ENNReal.ofReal ((1 - t) * B) :=
        ENNReal.ofReal_add (mul_nonneg ht_pos.le hA_nn)
          (mul_nonneg h1t_pos.le hB_nn)
    _ = ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
        rw [ENNReal.ofReal_mul ht_pos.le, ENNReal.ofReal_mul h1t_pos.le,
            hofa, hofb]

/-- **Arithmetic-bound assembly (1D PL, ess-sup-aligned form).**

Under the PL pointwise hypothesis AND `essSup f = essSup g`:
$$t \cdot \int f \;+\; (1-t) \cdot \int g \;\le\; \int h.$$

The `essSup` alignment hypothesis is necessary for the pointwise level-measure
bound to apply at every `α`: for `α < essSup f = essSup g`, both level sets
have positive measure (hence non-empty); for `α ≥ essSup f = essSup g`, both
have null measure, so the LHS pointwise contribution is 0.

The unconditional `prekopaLeindler_1d` reduces to this conditional form by
rescaling `f → c•f, h → c^t•h` (with `c := essSup g / essSup f`) which
preserves both PL hypothesis and conclusion while equalizing ess-sups. -/
private theorem prekopaLeindler_1d_arithBound
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (h_ess_eq : essSup f volume = essSup g volume) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ y, g y)
      ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set M : ℝ≥0∞ := essSup f volume with hM_def
  -- Helper: for `β < M`, the level set `{φ > β}` has positive measure when
  -- `essSup φ = M`. Standard via `essSup_le_of_ae_le` contrapositive.
  have h_pos_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, β < M → 0 < volume {x | β < φ x} := by
    intro φ hφ_ess β hβ
    by_contra h_neg
    rw [not_lt, nonpos_iff_eq_zero] at h_neg
    have h_ae : φ ≤ᵐ[volume] fun _ => β := by
      rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
      simpa using h_neg
    have : essSup φ volume ≤ β := essSup_le_of_ae_le β h_ae
    rw [hφ_ess] at this
    exact absurd this (not_le.mpr hβ)
  -- Helper: for `β ≥ M`, the level set `{φ > β}` has null measure.
  have h_null_meas : ∀ {φ : ℝ → ℝ≥0∞}, essSup φ volume = M →
      ∀ {β : ℝ≥0∞}, M ≤ β → volume {x | β < φ x} = 0 := by
    intro φ hφ_ess β hβ
    have h_essSup_le : essSup φ volume ≤ β := hφ_ess.trans_le hβ
    -- {φ > β} ⊆ {φ > essSup φ}, latter null by `meas_essSup_lt`.
    have h_sub : {x | β < φ x} ⊆ {x | essSup φ volume < φ x} :=
      fun x hx => lt_of_le_of_lt h_essSup_le hx
    refine le_antisymm ?_ (zero_le)
    calc volume {x | β < φ x}
        ≤ volume {x | essSup φ volume < φ x} := MeasureTheory.measure_mono h_sub
      _ = 0 := meas_essSup_lt
  -- Named integrand functions (with explicit measurability):
  let volF : ℝ → ℝ≥0∞ := fun α => volume {x | ENNReal.ofReal α < f x}
  let volG : ℝ → ℝ≥0∞ := fun α => volume {y | ENNReal.ofReal α < g y}
  let volH : ℝ → ℝ≥0∞ := fun α => volume {z | ENNReal.ofReal α < h z}
  have hvolF_meas : Measurable volF :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hf_meas.comp measurable_snd))
  have hvolG_meas : Measurable volG :=
    measurable_measure_prodMk_left
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst)
        (hg_meas.comp measurable_snd))
  -- Pointwise bound on `volF, volG, volH`.
  have h_pointwise : ∀ α : ℝ, 0 < α →
      ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α := by
    intro α hα
    have hα_pos_e : (0 : ℝ≥0∞) < ENNReal.ofReal α :=
      ENNReal.ofReal_pos.mpr hα
    have hα_top : ENNReal.ofReal α ≠ ⊤ := ENNReal.ofReal_ne_top
    by_cases hαM : ENNReal.ofReal α < M
    · -- `α < M`: both level sets positive-measure ⇒ non-empty.
      have hA_pos : 0 < volume {x | ENNReal.ofReal α < f x} :=
        h_pos_meas hM_def.symm hαM
      have hB_pos : 0 < volume {y | ENNReal.ofReal α < g y} :=
        h_pos_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      have hA_ne : ({x | ENNReal.ofReal α < f x} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hA_pos.ne'
      have hB_ne : ({y | ENNReal.ofReal α < g y} : Set ℝ).Nonempty :=
        MeasureTheory.nonempty_of_measure_ne_zero hB_pos.ne'
      exact prekopaLeindler_1d_levelMeasureBound hf_meas hg_meas hh_meas
        ht_pos ht_lt h_le hα_pos_e hα_top hA_ne hB_ne
    · -- `α ≥ M`: both level sets null, LHS = 0.
      rw [not_lt] at hαM
      have hf_null : volF α = 0 := h_null_meas hM_def.symm hαM
      have hg_null : volG α = 0 := h_null_meas (h_ess_eq.symm.trans hM_def.symm) hαM
      change ENNReal.ofReal t * volF α + ENNReal.ofReal (1 - t) * volG α ≤ volH α
      rw [hf_null, hg_null, mul_zero, mul_zero, zero_add]
      exact zero_le
  -- Layer cake.
  rw [lintegral_eq_lintegral_meas_lt_ennreal hf_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hg_meas,
      lintegral_eq_lintegral_meas_lt_ennreal hh_meas]
  -- Reshape to use volF/volG/volH names.
  change ENNReal.ofReal t * (∫⁻ α in Ioi (0:ℝ), volF α)
       + ENNReal.ofReal (1 - t) * (∫⁻ α in Ioi (0:ℝ), volG α)
       ≤ ∫⁻ α in Ioi (0:ℝ), volH α
  -- Pull constants inside.
  rw [← MeasureTheory.lintegral_const_mul _ hvolF_meas,
      ← MeasureTheory.lintegral_const_mul _ hvolG_meas]
  -- Combine sums.
  rw [← MeasureTheory.lintegral_add_left (hvolF_meas.const_mul _)]
  -- Apply pointwise bound.
  exact MeasureTheory.setLIntegral_mono'
    measurableSet_Ioi (fun α hα => h_pointwise α hα)

/-- **Prékopa-Leindler 1D — bounded-ess-sup helper.**

Same statement as `prekopaLeindler_1d` but with `essSup f, essSup g ≠ ⊤`.
Body: trivial 0-cases + main rescaling case. The unconditional
`prekopaLeindler_1d` reduces to this via truncation + monotone convergence. -/
private theorem prekopaLeindler_1d_essBdd
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y))
    (hMf_top : essSup f volume ≠ ⊤) (hMg_top : essSup g volume ≠ ⊤) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  set Mf := essSup f volume with hMf_def
  set Mg := essSup g volume with hMg_def
  -- Trivial case `essSup f = 0` ⇒ `f = 0 a.e.` ⇒ `∫f = 0` ⇒ LHS = 0.
  by_cases hMf_zero : Mf = 0
  · have hf_int_zero : ∫⁻ x, f x = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hf_meas]
      filter_upwards [ENNReal.ae_le_essSup f] with x hx
      rw [← hMf_def, hMf_zero] at hx
      exact le_antisymm hx (zero_le)
    rw [hf_int_zero, ENNReal.zero_rpow_of_pos ht_pos, zero_mul]
    exact zero_le
  -- Symmetric: `essSup g = 0`.
  by_cases hMg_zero : Mg = 0
  · have hg_int_zero : ∫⁻ y, g y = 0 := by
      rw [MeasureTheory.lintegral_eq_zero_iff hg_meas]
      filter_upwards [ENNReal.ae_le_essSup g] with y hy
      rw [← hMg_def, hMg_zero] at hy
      exact le_antisymm hy (zero_le)
    rw [hg_int_zero, ENNReal.zero_rpow_of_pos h1t_pos, mul_zero]
    exact zero_le
  -- Main case: `Mf, Mg ∈ (0, ⊤)`. Rescale `f → c•f, h → c^t•h` with
  -- `c := Mg / Mf` (so `essSup (c•f) = c · Mf = Mg`).
  set c : ℝ≥0∞ := Mg / Mf with hc_def
  have hc_pos : (0 : ℝ≥0∞) < c := ENNReal.div_pos hMg_zero hMf_top
  have hc_top : c ≠ ⊤ := by
    rw [hc_def]
    exact (ENNReal.div_lt_top hMg_top hMf_zero).ne
  have hcMf_eq_Mg : c * Mf = Mg := by
    rw [hc_def, ENNReal.div_mul_cancel hMf_zero hMf_top]
  -- Define rescaled `f', h'`.
  set f' : ℝ → ℝ≥0∞ := fun x => c * f x with hf'_def
  set h' : ℝ → ℝ≥0∞ := fun z => c ^ t * h z with hh'_def
  have hf'_meas : Measurable f' := hf_meas.const_mul c
  have hh'_meas : Measurable h' := hh_meas.const_mul (c ^ t)
  -- `essSup f' = c * Mf = Mg = essSup g`.
  have hf'_essSup : essSup f' volume = Mg := by
    change essSup (fun x => c * f x) volume = Mg
    rw [ENNReal.essSup_const_mul, hcMf_eq_Mg]
  -- PL hypothesis for `(f', g, h')`.
  have h_le' : ∀ x y : ℝ,
      f' x ^ t * g y ^ (1 - t) ≤ h' (t * x + (1 - t) * y) := by
    intro x y
    change (c * f x) ^ t * g y ^ (1 - t) ≤ c ^ t * h (t * x + (1 - t) * y)
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc]
    gcongr
    exact h_le x y
  -- Apply `arithBound` + AM-GM to `(f', g, h')`.
  have h_amgm := ennreal_geom_mean_le_arith_mean2_weighted ht_pos ht_lt
    (∫⁻ x, f' x) (∫⁻ y, g y)
  have h_arith := prekopaLeindler_1d_arithBound hf'_meas hg_meas hh'_meas
    ht_pos ht_lt h_le' (hf'_essSup.trans hMg_def.symm)
  have h_pl_rescaled :
      (∫⁻ x, f' x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h' z :=
    le_trans h_amgm h_arith
  -- Translate: `∫f' = c · ∫f`, `∫h' = c^t · ∫h`. Cancel `c^t`.
  rw [show ∫⁻ x, f' x = c * ∫⁻ x, f x from
        MeasureTheory.lintegral_const_mul c hf_meas,
      show ∫⁻ z, h' z = c ^ t * ∫⁻ z, h z from
        MeasureTheory.lintegral_const_mul (c ^ t) hh_meas,
      ENNReal.mul_rpow_of_nonneg _ _ ht_pos.le, mul_assoc] at h_pl_rescaled
  -- Now `h_pl_rescaled : c^t * ((∫f)^t * (∫g)^(1-t)) ≤ c^t * ∫h`.
  have hct_ne_zero : c ^ t ≠ 0 := (ENNReal.rpow_pos hc_pos hc_top).ne'
  have hct_ne_top : c ^ t ≠ ⊤ :=
    (ENNReal.rpow_lt_top_of_nonneg ht_pos.le hc_top).ne
  -- `mul_le_mul_iff_left` gives the form `a * c ≤ b * c ↔ a ≤ b`. Convert via mul_comm.
  rw [mul_comm (c ^ t) _, mul_comm (c ^ t) _] at h_pl_rescaled
  exact (ENNReal.mul_le_mul_iff_left hct_ne_zero hct_ne_top).mp h_pl_rescaled

theorem prekopaLeindler_1d
    {f g h : ℝ → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  have h1t_pos : 0 < 1 - t := sub_pos.mpr ht_lt
  -- Truncate `f, g`: `f_n := f ⊓ n, g_n := g ⊓ n`. Both `essSup ≤ n < ⊤`.
  set fN : ℕ → ℝ → ℝ≥0∞ := fun n x => f x ⊓ (n : ℝ≥0∞) with hfN_def
  set gN : ℕ → ℝ → ℝ≥0∞ := fun n y => g y ⊓ (n : ℝ≥0∞) with hgN_def
  have hfN_meas : ∀ n, Measurable (fN n) := fun n => hf_meas.inf measurable_const
  have hgN_meas : ∀ n, Measurable (gN n) := fun n => hg_meas.inf measurable_const
  have hfN_essSup_top : ∀ n, essSup (fN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (fN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  have hgN_essSup_top : ∀ n, essSup (gN n) volume ≠ ⊤ := fun n => by
    have h_le_n : essSup (gN n) volume ≤ (n : ℝ≥0∞) :=
      essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun _ => inf_le_right)
    exact ne_of_lt (lt_of_le_of_lt h_le_n ENNReal.coe_lt_top)
  -- PL hypothesis for `(fN n, gN m, h)` (any n, m): truncation only weakens.
  have h_le_N : ∀ n m, ∀ x y : ℝ,
      fN n x ^ t * gN m y ^ (1 - t) ≤ h (t * x + (1 - t) * y) := by
    intro n m x y
    calc fN n x ^ t * gN m y ^ (1 - t)
        ≤ f x ^ t * g y ^ (1 - t) := by
          gcongr <;> exact inf_le_left
      _ ≤ h (t * x + (1 - t) * y) := h_le x y
  -- Per-(n, m): apply bdd helper.
  have h_per_nm : ∀ n m,
      (∫⁻ x, fN n x) ^ t * (∫⁻ y, gN m y) ^ (1 - t) ≤ ∫⁻ z, h z := fun n m =>
    prekopaLeindler_1d_essBdd (hfN_meas n) (hgN_meas m) hh_meas ht_pos ht_lt
      (h_le_N n m) (hfN_essSup_top n) (hgN_essSup_top m)
  -- Monotone in n: `∫fN n ↑ ∫f` (MCT). Similarly gN.
  have hfN_mono : Monotone fun n => ∫⁻ x, fN n x := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro x; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hgN_mono : Monotone fun m => ∫⁻ y, gN m y := by
    intro n m hnm
    apply MeasureTheory.lintegral_mono
    intro y; exact inf_le_inf_left _ (by exact_mod_cast hnm)
  have hfN_iSup : ⨆ n, ∫⁻ x, fN n x = ∫⁻ x, f x := by
    rw [← MeasureTheory.lintegral_iSup hfN_meas (fun n m hnm x =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro x
    simp only [fN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hgN_iSup : ⨆ m, ∫⁻ y, gN m y = ∫⁻ y, g y := by
    rw [← MeasureTheory.lintegral_iSup hgN_meas (fun n m hnm y =>
      inf_le_inf_left _ (by exact_mod_cast hnm))]
    apply MeasureTheory.lintegral_congr
    intro y
    simp only [gN]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  -- Conclude: `(∫f)^t * (∫g)^(1-t) ≤ ∫h` via iSup commute with rpow + mul.
  -- `(∫f)^t = (⨆ n, ∫fN n)^t = ⨆ n, (∫fN n)^t` (rpow continuous + monotone).
  -- Similarly for g.
  -- `(⨆ n, A_n) * (⨆ m, B_m) = ⨆ n, ⨆ m, A_n * B_m ≤ ⨆ k, A_k * B_k ≤ ∫h`.
  -- Helper: `(⨆ a_n)^p = ⨆ a_n^p` for monotone `a_n` and `p ≥ 0`.
  -- Via `tendsto_atTop_iSup` + `continuous_rpow_const` + `tendsto_nhds_unique`.
  have h_rpow_iSup : ∀ (a : ℕ → ℝ≥0∞) (p : ℝ), 0 ≤ p → Monotone a →
      (⨆ n, a n) ^ p = ⨆ n, a n ^ p := by
    intro a p hp ha_mono
    have h_tendsto : Filter.Tendsto a Filter.atTop (𝓝 (⨆ n, a n)) :=
      tendsto_atTop_iSup ha_mono
    have h_tendsto_pow : Filter.Tendsto (fun n => a n ^ p) Filter.atTop
        (𝓝 ((⨆ n, a n) ^ p)) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h_tendsto
    have ha_pow_mono : Monotone (fun n => a n ^ p) := fun n m hnm =>
      ENNReal.rpow_le_rpow (ha_mono hnm) hp
    exact tendsto_nhds_unique h_tendsto_pow (tendsto_atTop_iSup ha_pow_mono)
  rw [← hfN_iSup, ← hgN_iSup]
  -- Push rpow inside iSup.
  rw [h_rpow_iSup _ t ht_pos.le hfN_mono,
      h_rpow_iSup _ (1 - t) h1t_pos.le hgN_mono]
  -- `(⨆ n, A_n) * (⨆ m, B_m) = ⨆ n, ⨆ m, A_n * B_m`.
  rw [ENNReal.iSup_mul]
  refine iSup_le fun n => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  -- Goal: `(∫fN n)^t * (∫gN m)^(1-t) ≤ ∫h`. Use `h_per_nm n m`.
  exact h_per_nm n m

/-- **Prékopa-Leindler inequality (finite-dimensional form).**

For nonneg measurable `f, g, h : (ι → ℝ) → ℝ≥0∞` (with `ι` finite) and
`t ∈ (0, 1)` such that
$h(t \cdot x + (1-t) \cdot y) \ge f(x)^t \cdot g(y)^{1-t}$
for all `x, y : ι → ℝ`, we have
$$\int h \;\ge\; \left(\int f\right)^t \cdot \left(\int g\right)^{1-t}$$
where all integrals are with respect to the Pi product Lebesgue measure on
`ι → ℝ` (available as `volume` via `MeasureTheory.MeasureSpace.pi`).

The statement uses `ι → ℝ` rather than `EuclideanSpace ℝ ι` because only the
former has a default `MeasureSpace` instance (by Mathlib design — `PiLp` is a
type synonym chosen *not* to inherit the Pi measure to avoid ambiguity with
Haar measure). For the `anderson_lemma_set` application, transfer via
`PiLp.volume_preserving_toLp` / `EuclideanSpace.equiv`.

**Proof.** Use `Fintype.induction_empty_option`, transporting the inequality and
product volume along equivalences of finite index types. For the empty type,
product volume is a Dirac measure at the unique function, so the conclusion is
the pointwise hypothesis at that function. In the `Option α` step,
`MeasurableEquiv.piOptionEquivProd` splits a function into its `α` coordinates
and its `none` coordinate. Fubini expresses each integral as an outer integral
over `ℝ` of an inner integral over `α → ℝ`; the induction hypothesis applied to
the inner fibres gives the Prékopa-Leindler hypothesis for these three marginal
functions on `ℝ`, and `prekopaLeindler_1d` completes the step.

This is the form directly consumed by `anderson_lemma_set` in
`ForMathlib/Anderson.lean`: apply with `f(x) := ρ(x) · 𝟙_{C-y}(x)`,
`g(x) := ρ(x) · 𝟙_{C+y}(x)`, `h(x) := ρ(x) · 𝟙_C(x)` (where `ρ` is the
Gaussian density, in `(ι → ℝ)`-coordinates) and `t = 1/2`; the pointwise
hypothesis follows from log-concavity of `ρ` and midpoint-convexity of `C`. -/
theorem prekopaLeindler.{u}
    {ι : Type u} [Fintype ι]
    {f g h : (ι → ℝ) → ℝ≥0∞}
    (hf_meas : Measurable f) (hg_meas : Measurable g) (hh_meas : Measurable h)
    {t : ℝ} (ht_pos : 0 < t) (ht_lt : t < 1)
    (h_le : ∀ x y : ι → ℝ,
      f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ y, g y) ^ (1 - t) ≤ ∫⁻ z, h z := by
  -- Generalise over the index type κ and over `(f, g, h, s)` so we can run
  -- `Fintype.induction_empty_option` (the predicate must be `(κ : Type u) →
  -- [Fintype κ] → Prop`, sharing the universe of `ι`).
  suffices H : ∀ (κ : Type u) [Fintype κ] (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z by
    exact H ι f g h hf_meas hg_meas hh_meas ht_pos ht_lt h_le
  intro κ _Fκ
  refine Fintype.induction_empty_option
    (P := fun κ [Fintype κ] => ∀ (f g h : (κ → ℝ) → ℝ≥0∞),
      Measurable f → Measurable g → Measurable h →
      ∀ {s : ℝ}, 0 < s → s < 1 →
      (∀ x y : κ → ℝ, f x ^ s * g y ^ (1 - s) ≤ h (s • x + (1 - s) • y)) →
      (∫⁻ x, f x) ^ s * (∫⁻ y, g y) ^ (1 - s) ≤ ∫⁻ z, h z) ?_ ?_ ?_ κ
  · -- `of_equiv`: transport along an `Equiv α ≃ β`. Pull `(f, g, h)` back
    -- through `(piCongrLeft (fun _ : α => ℝ) e.symm).symm : (α → ℝ) ≃ᵐ (β → ℝ)`,
    -- whose value `ψ.symm x b = x (e.symm b)` is `rfl`-apply.
    intro α β _Fβ e IH f g h hf hg hh s hs hs1 hle
    letI : Fintype α := Fintype.ofEquiv β e.symm
    set ψ : (β → ℝ) ≃ᵐ (α → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : α => ℝ) e.symm with hψ_def
    -- `ψ.symm` preserves affine combinations (componentwise).
    have hψ_smul : ∀ x y : α → ℝ,
        ψ.symm (s • x + (1 - s) • y) = s • ψ.symm x + (1 - s) • ψ.symm y := fun _ _ => rfl
    -- Volume transfer: `(volume_α).map ψ.symm = volume_β`.
    have h_vol_fwd : (volume : Measure (β → ℝ)).map ψ = (volume : Measure (α → ℝ)) := by
      conv_lhs => rw [MeasureTheory.volume_pi]
      conv_rhs => rw [MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piCongrLeft e.symm (fun _ : α => volume)
    have h_vol : (volume : Measure (α → ℝ)).map ψ.symm = (volume : Measure (β → ℝ)) := by
      rw [← h_vol_fwd, MeasurableEquiv.map_symm_map]
    -- Pull `(f, g, h)` back to `(α → ℝ)`.
    have hf' : Measurable (f ∘ ψ.symm) := hf.comp ψ.symm.measurable
    have hg' : Measurable (g ∘ ψ.symm) := hg.comp ψ.symm.measurable
    have hh' : Measurable (h ∘ ψ.symm) := hh.comp ψ.symm.measurable
    have hle' : ∀ x y : α → ℝ,
        (f ∘ ψ.symm) x ^ s * (g ∘ ψ.symm) y ^ (1 - s)
        ≤ (h ∘ ψ.symm) (s • x + (1 - s) • y) := by
      intro x y
      change f (ψ.symm x) ^ s * g (ψ.symm y) ^ (1 - s) ≤ h (ψ.symm (s • x + (1 - s) • y))
      rw [hψ_smul x y]
      exact hle (ψ.symm x) (ψ.symm y)
    -- Translate β-side integrals back to α-side via `lintegral_map`.
    have hf_int : ∫⁻ y, f y = ∫⁻ x, f (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hf ψ.symm.measurable
    have hg_int : ∫⁻ y, g y = ∫⁻ x, g (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hg ψ.symm.measurable
    have hh_int : ∫⁻ y, h y = ∫⁻ x, h (ψ.symm x) := by
      conv_lhs => rw [show (volume : Measure (β → ℝ))
          = (volume : Measure (α → ℝ)).map ψ.symm from h_vol.symm]
      exact MeasureTheory.lintegral_map hh ψ.symm.measurable
    rw [hf_int, hg_int, hh_int]
    exact IH (f ∘ ψ.symm) (g ∘ ψ.symm) (h ∘ ψ.symm) hf' hg' hh' hs hs1 hle'
  · -- `h_empty`: `PEmpty → ℝ` is a singleton. Volume is Dirac at the unique
    -- point; all integrals reduce to evaluation, the conclusion is the PL
    -- hypothesis at that point.
    intro f g h hf_meas hg_meas hh_meas s hs_pos hs_lt h_le
    have h_volume : (volume : Measure (PEmpty → ℝ))
        = Measure.dirac (fun a : PEmpty => isEmptyElim a) :=
      Measure.volume_pi_eq_dirac _
    rw [h_volume, lintegral_dirac' _ hf_meas, lintegral_dirac' _ hg_meas,
        lintegral_dirac' _ hh_meas]
    have h_pl := h_le (fun a => isEmptyElim a) (fun a => isEmptyElim a)
    have h_smul : s • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                  + (1 - s) • (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ)
                = (fun a : PEmpty => isEmptyElim a : PEmpty → ℝ) := by
      funext a; exact isEmptyElim a
    rwa [h_smul] at h_pl
  · -- `h_option`: `P α ⇒ P (Option α)`. Split the index off the `none`-coord
    -- via `MeasurableEquiv.piOptionEquivProd`, push integrals through Fubini
    -- to land outer-on-ℝ + inner-on-(α → ℝ); apply IH fibrewise to obtain the
    -- 1D PL hypothesis on the marginalised integrals; close with
    -- `prekopaLeindler_1d`.
    intro α _Fα IH f g h hf hg hh s hs hs1 hle
    let E : ((i : Option α) → ℝ) ≃ᵐ ((i : α) → ℝ) × ℝ :=
      MeasurableEquiv.piOptionEquivProd (fun _ : Option α => ℝ)
    -- `E.symm` is `rfl`-apply at `none` (gives `u`) and `some a` (gives `x' a`).
    have hE_none : ∀ (x' : α → ℝ) (u : ℝ),
        E.symm (x', u) none = u := fun _ _ => rfl
    have hE_some : ∀ (x' : α → ℝ) (u : ℝ) (a : α),
        E.symm (x', u) (some a) = x' a := fun _ _ _ => rfl
    -- `E.symm` preserves affine combinations (verified at each `Option` case).
    have hE_smul : ∀ (x' y' : α → ℝ) (u v : ℝ),
        s • E.symm (x', u) + (1 - s) • E.symm (y', v)
        = E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v) := by
      intro x' y' u v
      funext i
      cases i with
      | none =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * u + (1 - s) * v = s * u + (1 - s) * v
        rfl
      | some a =>
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        change s * x' a + (1 - s) * y' a = s * x' a + (1 - s) * y' a
        rfl
    -- Volume transfer: `(volume_α.prod volume_ℝ).map E.symm = volume_OptionAlpha`.
    have h_vol : ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        = (volume : Measure (Option α → ℝ)) := by
      conv_rhs => rw [MeasureTheory.volume_pi]
      conv_lhs => rw [show (volume : Measure (α → ℝ))
          = MeasureTheory.Measure.pi (fun _ : α => volume) from MeasureTheory.volume_pi]
      exact MeasureTheory.Measure.pi_map_piOptionEquivProd
        (fun _ : Option α => volume)
    -- Marginalised functions on ℝ.
    set F : ℝ → ℝ≥0∞ := fun u => ∫⁻ x' : α → ℝ, f (E.symm (x', u)) with hF_def
    set G : ℝ → ℝ≥0∞ := fun v => ∫⁻ y' : α → ℝ, g (E.symm (y', v)) with hG_def
    set H_marg : ℝ → ℝ≥0∞ := fun w => ∫⁻ z' : α → ℝ, h (E.symm (z', w)) with hH_def
    -- Measurability of `f ∘ E.symm`, `g ∘ E.symm`, `h ∘ E.symm`.
    have hf_comp : Measurable (fun p : (α → ℝ) × ℝ => f (E.symm p)) :=
      hf.comp E.symm.measurable
    have hg_comp : Measurable (fun p : (α → ℝ) × ℝ => g (E.symm p)) :=
      hg.comp E.symm.measurable
    have hh_comp : Measurable (fun p : (α → ℝ) × ℝ => h (E.symm p)) :=
      hh.comp E.symm.measurable
    have hF_meas : Measurable F := Measurable.lintegral_prod_left' hf_comp
    have hG_meas : Measurable G := Measurable.lintegral_prod_left' hg_comp
    have hH_marg_meas : Measurable H_marg := Measurable.lintegral_prod_left' hh_comp
    -- 1D PL hypothesis on `(F, G, H_marg)` via IH at each `(u, v) ∈ ℝ × ℝ`.
    have h_FGH_le : ∀ u v : ℝ,
        F u ^ s * G v ^ (1 - s) ≤ H_marg (s * u + (1 - s) * v) := by
      intro u v
      have hf_slice : Measurable (fun x' : α → ℝ => f (E.symm (x', u))) :=
        hf.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hg_slice : Measurable (fun y' : α → ℝ => g (E.symm (y', v))) :=
        hg.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have hh_slice : Measurable (fun z' : α → ℝ =>
          h (E.symm (z', s * u + (1 - s) * v))) :=
        hh.comp (E.symm.measurable.comp (measurable_id.prodMk measurable_const))
      have h_slice_le : ∀ x' y' : α → ℝ,
          f (E.symm (x', u)) ^ s * g (E.symm (y', v)) ^ (1 - s)
          ≤ h (E.symm (s • x' + (1 - s) • y', s * u + (1 - s) * v)) := by
        intro x' y'
        have h_pl := hle (E.symm (x', u)) (E.symm (y', v))
        rw [hE_smul] at h_pl
        exact h_pl
      exact IH _ _ _ hf_slice hg_slice hh_slice hs hs1 h_slice_le
    -- Apply 1D PL.
    have h_1d := prekopaLeindler_1d hF_meas hG_meas hH_marg_meas hs hs1 h_FGH_le
    -- Translate full Option-α integrals back via `h_vol` + Fubini.
    have h_int_split : ∀ (k : (Option α → ℝ) → ℝ≥0∞), Measurable k →
        ∫⁻ z, k z = ∫⁻ u : ℝ, ∫⁻ x' : α → ℝ, k (E.symm (x', u)) := by
      intro k hk
      conv_lhs => rw [show (volume : Measure (Option α → ℝ))
          = ((volume : Measure (α → ℝ)).prod (volume : Measure ℝ)).map E.symm
        from h_vol.symm]
      rw [MeasureTheory.lintegral_map hk E.symm.measurable]
      exact MeasureTheory.lintegral_prod_symm' _ (hk.comp E.symm.measurable)
    rw [h_int_split f hf, h_int_split g hg, h_int_split h hh]
    exact h_1d

end AsymptoticStatistics
