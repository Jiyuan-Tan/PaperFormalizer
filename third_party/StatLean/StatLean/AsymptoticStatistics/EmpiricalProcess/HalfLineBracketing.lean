module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.HalfLineQuantile
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

/-!
# Finite bracketing of the half-line indicator class

The atom-safe grid gives finite `L¹(P)` and `L²(P)` bracketing covers. Open
gaps are bracketed separately from quantile singletons, so the construction
works for Dirac measures and arbitrary atomic laws. The resulting polynomial
`O(δ⁻²)` count makes the bracketing entropy integral finite.

This file does not claim that finite bracketing makes the Gaussian carrier
finite-dimensional; that implication is false for continuous distributions.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal

private lemma indicatorWidth_isEpsBracket
    (P : Measure ℝ) [IsProbabilityMeasure P] {p : ℝ≥0∞} {eps mesh : ℝ}
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    {l u : ℝ → ℝ} {s : Set ℝ}
    (hl : Measurable l) (hu : Measurable u) (hlp : MemLp l p P)
    (hup : MemLp u p P) (hlu : ∀ x, l x ≤ u x) (hs : MeasurableSet s)
    (hdiff : (fun x ↦ u x - l x) = s.indicator (fun _ ↦ (1 : ℝ)))
    (hPs : P s ≤ ENNReal.ofReal mesh)
    (hstrict : (ENNReal.ofReal mesh) ^ (1 / p.toReal) < ENNReal.ofReal eps) :
    IsEpsBracket eps l u p P := by
  refine ⟨hlu, hl, hu, hlp, hup, ?_⟩
  rw [hdiff, eLpNorm_indicator_const hs hp0 hpTop]
  simpa using (ENNReal.rpow_le_rpow hPs (by positivity)).trans_lt hstrict

private theorem halfLine_gridCover
    (P : Measure ℝ) [IsProbabilityMeasure P] (n : ℕ) (p : ℝ≥0∞) (eps : ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) {mesh : ℝ}
    (hgridmesh : 1 / (n + 2 : ℝ) ≤ mesh)
    (hstrict : (ENNReal.ofReal mesh) ^ (1 / p.toReal) < ENNReal.ofReal eps) :
    ∃ l u : Fin (2 * n + 3) → ℝ → ℝ,
      (∀ i, IsEpsBracket eps (l i) (u i) p P) ∧
      (∀ f ∈ halfLineIndicatorClass, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x) := by
  classical
  obtain ⟨q, hq, hleft, hgap, hright⟩ := exists_halfLine_atomSafeGrid P n
  have heps : 0 < eps := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hstrict)
  let I := Fin (n + 1) ⊕ (Fin n ⊕ Fin 2)
  have hcard : Fintype.card I = 2 * n + 3 := by simp [I]; omega
  let e : Fin (2 * n + 3) ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  let lo : I → ℝ → ℝ
    | Sum.inl i => halfLineIndicator (q i)
    | Sum.inr (Sum.inl j) => halfLineIndicator (q j.castSucc)
    | Sum.inr (Sum.inr z) => if z = 0 then 0 else halfLineIndicator (q (Fin.last n))
  let hi : I → ℝ → ℝ
    | Sum.inl i => halfLineIndicator (q i)
    | Sum.inr (Sum.inl j) =>
        if q j.castSucc < q j.succ then openHalfLineIndicator (q j.succ)
        else halfLineIndicator (q j.castSucc)
    | Sum.inr (Sum.inr z) => if z = 0 then openHalfLineIndicator (q 0) else 1
  refine ⟨fun i ↦ lo (e i), fun i ↦ hi (e i), ?_, ?_⟩
  · intro i
    change IsEpsBracket eps (lo (e i)) (hi (e i)) p P
    rcases hidx : e i with j | j | z
    · dsimp [lo, hi]
      refine ⟨fun x ↦ le_rfl, measurable_halfLineIndicator _,
        measurable_halfLineIndicator _, halfLineIndicator_memLp P _ _,
        halfLineIndicator_memLp P _ _, ?_⟩
      simp [heps]
    · dsimp [lo, hi]
      by_cases hjump : q j.castSucc < q j.succ
      · simp only [if_pos hjump]
        apply indicatorWidth_isEpsBracket (p := p) (eps := eps) (mesh := mesh)
          (s := Set.Ioo (q j.castSucc) (q j.succ)) P hp0 hpTop
          (measurable_halfLineIndicator _) (measurable_openHalfLineIndicator _)
          (halfLineIndicator_memLp P _ _) (openHalfLineIndicator_memLp P _ _)
        · intro x
          by_cases hxj : x ≤ q j.castSucc
          · have hxjs : x < q j.succ := hxj.trans_lt hjump
            simp [halfLineIndicator, openHalfLineIndicator, hxj, hxjs]
          · by_cases hxjs : x < q j.succ <;>
              simp [halfLineIndicator, openHalfLineIndicator, hxj, hxjs]
        · exact measurableSet_Ioo
        · funext x
          by_cases hxj : x ≤ q j.castSucc
          · have hxjs : x < q j.succ := hxj.trans_lt hjump
            simp [halfLineIndicator, openHalfLineIndicator, Set.mem_Ioo, hxj, hxjs]
          · by_cases hxjs : x < q j.succ
            · have hlow : q j.castSucc < x := lt_of_not_ge hxj
              simp [halfLineIndicator, openHalfLineIndicator, Set.mem_Ioo, hxj, hxjs, hlow]
            · simp [halfLineIndicator, openHalfLineIndicator, Set.mem_Ioo, hxj, hxjs]
        · exact (hgap j).trans (ENNReal.ofReal_le_ofReal hgridmesh)
        · exact hstrict
      · simp only [if_neg hjump]
        refine ⟨fun x ↦ le_rfl, measurable_halfLineIndicator _,
          measurable_halfLineIndicator _, halfLineIndicator_memLp P _ _,
          halfLineIndicator_memLp P _ _, ?_⟩
        simp [heps]
    · fin_cases z
      · change IsEpsBracket eps (fun _ ↦ 0) (openHalfLineIndicator (q 0)) p P
        apply indicatorWidth_isEpsBracket (p := p) (eps := eps) (mesh := mesh)
          (s := Set.Iio (q 0)) P hp0 hpTop
          measurable_const (measurable_openHalfLineIndicator _) (memLp_const 0)
          (openHalfLineIndicator_memLp P _ _)
        · intro x
          by_cases hx : x < q 0 <;> simp [openHalfLineIndicator, hx]
        · exact measurableSet_Iio
        · funext x
          by_cases hx : x < q 0 <;> simp [openHalfLineIndicator, hx]
        · exact hleft.trans (ENNReal.ofReal_le_ofReal hgridmesh)
        · exact hstrict
      · change IsEpsBracket eps (halfLineIndicator (q (Fin.last n))) (fun _ ↦ 1) p P
        apply indicatorWidth_isEpsBracket (p := p) (eps := eps) (mesh := mesh)
          (s := Set.Ioi (q (Fin.last n))) P hp0 hpTop
          (measurable_halfLineIndicator _) measurable_const
          (halfLineIndicator_memLp P _ _) (memLp_const 1)
        · intro x
          by_cases hx : x ≤ q (Fin.last n) <;> simp [halfLineIndicator, hx]
        · exact measurableSet_Ioi
        · funext x
          by_cases hx : x ≤ q (Fin.last n)
          · simp [halfLineIndicator, hx]
          · have hgt : q (Fin.last n) < x := lt_of_not_ge hx
            simp [halfLineIndicator, hx, hgt]
        · exact hright.trans (ENNReal.ofReal_le_ofReal hgridmesh)
        · exact hstrict
  · rintro f ⟨t, rfl⟩
    by_cases htq : ∃ i, t = q i
    · obtain ⟨i, rfl⟩ := htq
      refine ⟨e.symm (Sum.inl i), fun x ↦ ?_⟩
      simp [lo, hi]
    · by_cases ht0 : t < q 0
      · refine ⟨e.symm (Sum.inr (Sum.inr 0)), fun x ↦ ?_⟩
        simp only [Equiv.apply_symm_apply]
        constructor
        · by_cases hxt : x ≤ t <;> simp [lo, halfLineIndicator, hxt]
        · by_cases hxt : x ≤ t
          · simp [hi, halfLineIndicator, openHalfLineIndicator, hxt, hxt.trans_lt ht0]
          · by_cases hx0 : x < q 0 <;>
              simp [hi, openHalfLineIndicator, halfLineIndicator, hxt, hx0]
      · by_cases htl : q (Fin.last n) < t
        · refine ⟨e.symm (Sum.inr (Sum.inr 1)), fun x ↦ ?_⟩
          simp only [Equiv.apply_symm_apply]
          constructor
          · by_cases hx : x ≤ q (Fin.last n)
            · simp [lo, halfLineIndicator, hx, hx.trans htl.le]
            · by_cases hxt : x ≤ t <;> simp [lo, halfLineIndicator, hx, hxt]
          · by_cases hxt : x ≤ t <;> simp [hi, halfLineIndicator, hxt]
        · let R : ℕ → Prop := fun m ↦ ∃ hm : m < n + 1, t < q ⟨m, hm⟩
          have hex : ∃ m : ℕ, R m := by
            refine ⟨n, ⟨by omega, ?_⟩⟩
            simpa using! lt_of_le_of_ne (le_of_not_gt htl)
              (fun h ↦ htq ⟨Fin.last n, h⟩)
          let m := Nat.find hex
          obtain ⟨hmn, hmqt⟩ := Nat.find_spec hex
          change m < n + 1 at hmn
          change t < q ⟨m, hmn⟩ at hmqt
          have hm0 : 0 < m := by
            by_contra h
            have hmzero : m = 0 := Nat.eq_zero_of_not_pos h
            have hfin : (⟨m, hmn⟩ : Fin (n + 1)) = 0 := Fin.ext hmzero
            have hmqt0 : t < q 0 := by
              simpa only [hfin] using hmqt
            exact (not_lt_of_ge (le_of_not_gt ht0)) hmqt0
          let j : Fin n := ⟨m - 1, by omega⟩
          have hjcast : j.castSucc = ⟨m - 1, by omega⟩ := rfl
          have hjsucc : j.succ = ⟨m, hmn⟩ := by ext; simp [j]; omega
          have hlow : q j.castSucc < t := by
            have hnotR : ¬ R (m - 1) := by
              intro hR
              have hle := Nat.find_min' hex hR
              change m ≤ m - 1 at hle
              omega
            have hnot : ¬ t < q ⟨m - 1, by omega⟩ := fun h ↦ hnotR ⟨by omega, h⟩
            exact lt_of_le_of_ne (le_of_not_gt hnot)
              (fun h ↦ htq ⟨⟨m - 1, by omega⟩, h.symm⟩)
          refine ⟨e.symm (Sum.inr (Sum.inl j)), fun x ↦ ?_⟩
          simp only [Equiv.apply_symm_apply]
          constructor
          · by_cases hx : x ≤ q j.castSucc
            · simp [lo, halfLineIndicator, hx, hx.trans hlow.le]
            · by_cases hxt : x ≤ t <;> simp [lo, halfLineIndicator, hx, hxt]
          · have hupp : t < q j.succ := by simpa only [hjsucc] using hmqt
            have hjump : q j.castSucc < q j.succ := hlow.trans hupp
            by_cases hx : x ≤ t
            · simp [hi, hjump, halfLineIndicator, openHalfLineIndicator, hx, hx.trans_lt hupp]
            · by_cases hxu : x < q j.succ <;>
                simp [hi, hjump, openHalfLineIndicator, halfLineIndicator, hx, hxu]

/-- Finite `L¹(P)` bracketing at every positive scale, with strict bracket
width `< ε` as required by `IsEpsBracket`. -/
theorem halfLine_hasFiniteBracketingCover_L1
    (P : Measure ℝ) [IsProbabilityMeasure P] {ε : ℝ} (hε : 0 < ε) :
    HasFiniteBracketingCover halfLineIndicatorClass ε 1 P := by
  let n : ℕ := ⌈2 / ε⌉₊
  have hn : 2 / ε ≤ (n : ℝ) := Nat.le_ceil _
  have htwo : 2 ≤ ε * n := by
    rw [div_le_iff₀ hε] at hn
    simpa [mul_comm] using hn
  have hgrid : 1 / (n + 2 : ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)]
    nlinarith
  have hstrict : (ENNReal.ofReal (ε / 2)) ^ (1 / (1 : ℝ≥0∞).toReal) <
      ENNReal.ofReal ε := by
    norm_num
    exact ENNReal.ofReal_lt_ofReal_iff hε |>.2 (half_lt_self hε)
  obtain ⟨l, u, hbr, hcov⟩ := halfLine_gridCover P n 1 ε (by norm_num) (by norm_num)
    hgrid hstrict
  exact ⟨2 * n + 3, l, u, hbr, hcov⟩

/-- Finite `L²(P)` bracketing at every positive scale. The grid mesh is
chosen strictly below `δ²`, not merely at most `δ²`. -/
theorem halfLine_hasFiniteBracketingCover_L2
    (P : Measure ℝ) [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    HasFiniteBracketingCover halfLineIndicatorClass δ 2 P := by
  let n : ℕ := ⌈2 / δ ^ 2⌉₊
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hn : 2 / δ ^ 2 ≤ (n : ℝ) := Nat.le_ceil _
  have htwo : 2 ≤ δ ^ 2 * n := by
    rw [div_le_iff₀ hδsq] at hn
    simpa [mul_comm] using hn
  have hgrid : 1 / (n + 2 : ℝ) ≤ δ ^ 2 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)]
    nlinarith
  have hstrict : (ENNReal.ofReal (δ ^ 2 / 2)) ^ (1 / (2 : ℝ≥0∞).toReal) <
      ENNReal.ofReal δ := by
    rw [show 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) by norm_num,
      ENNReal.ofReal_rpow_of_pos (by positivity), ← Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_lt_ofReal_iff hδ |>.2 <| (Real.sqrt_lt' hδ).2 (by nlinarith)
  obtain ⟨l, u, hbr, hcov⟩ := halfLine_gridCover P n 2 δ (by norm_num) (by norm_num)
    hgrid hstrict
  exact ⟨2 * n + 3, l, u, hbr, hcov⟩

/-- Coarse polynomial bracketing count for `0 < δ ≤ 1`. The constant `8`
absorbs the open-gap brackets, singleton jump brackets, and strict-scale
inflation. -/
theorem halfLine_bracketingNumber_L2_le
    (P : Measure ℝ) [IsProbabilityMeasure P] {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    bracketingNumber δ halfLineIndicatorClass 2 P ≤
      (((⌈8 / δ ^ 2⌉₊ : ℕ) : ℕ∞)) := by
  let n : ℕ := ⌈2 / δ ^ 2⌉₊
  have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
  have hn : 2 / δ ^ 2 ≤ (n : ℝ) := Nat.le_ceil _
  have htwo : 2 ≤ δ ^ 2 * n := by
    rw [div_le_iff₀ hδsq] at hn
    simpa [mul_comm] using hn
  have hgrid : 1 / (n + 2 : ℝ) ≤ δ ^ 2 / 2 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < n + 2)]
    nlinarith
  have hstrict : (ENNReal.ofReal (δ ^ 2 / 2)) ^ (1 / (2 : ℝ≥0∞).toReal) <
      ENNReal.ofReal δ := by
    rw [show 1 / (2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) by norm_num,
      ENNReal.ofReal_rpow_of_pos (by positivity), ← Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_lt_ofReal_iff hδ |>.2 <| (Real.sqrt_lt' hδ).2 (by nlinarith)
  obtain ⟨l, u, hbr, hcov⟩ := halfLine_gridCover P n 2 δ (by norm_num) (by norm_num)
    hgrid hstrict
  have hδsq_one : δ ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]
  have ha2 : 2 ≤ 2 / δ ^ 2 := by
    rw [le_div_iff₀ hδsq]
    nlinarith
  have hnlt : (n : ℝ) < 2 / δ ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hreal : (2 * n + 3 : ℕ) < 8 / δ ^ 2 + 1 := by
    norm_cast
    rw [Nat.cast_add, Nat.cast_mul]
    norm_num
    rw [show 8 / δ ^ 2 = 4 * (2 / δ ^ 2) by ring]
    nlinarith
  have hNat : 2 * n + 3 ≤ ⌈8 / δ ^ 2⌉₊ := by
    by_contra h
    have hsucc : ⌈8 / δ ^ 2⌉₊ + 1 ≤ 2 * n + 3 := Nat.lt_of_not_ge h
    have hceil : 8 / δ ^ 2 ≤ (⌈8 / δ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have hsucc' : (⌈8 / δ ^ 2⌉₊ : ℝ) + 1 ≤ (2 * n + 3 : ℕ) := by exact_mod_cast hsucc
    linarith
  unfold bracketingNumber
  refine (iInf_le_of_le (2 * n + 3) (iInf_le_of_le ⟨l, u, hbr, hcov⟩ le_rfl)).trans ?_
  exact_mod_cast hNat

private lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [show a + b = Real.sqrt a ^ 2 + Real.sqrt b ^ 2 by
    rw [Real.sq_sqrt ha, Real.sq_sqrt hb]]
  calc
    Real.sqrt (Real.sqrt a ^ 2 + Real.sqrt b ^ 2)
        ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- The half-line class has finite `L²(P)` bracketing entropy integral.
This is the structural input to the carrier-agnostic Donsker theorem. -/
theorem halfLine_bracketingEntropyIntegral_lt_top
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    bracketingEntropyIntegral 1 halfLineIndicatorClass P < ⊤ := by
  set A : ℝ := Real.log 10 with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact Real.log_nonneg (by norm_num)
  set B : ℝ := Real.sqrt A + Real.sqrt 2 with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hdom : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      entropyIntegrand s halfLineIndicatorClass P ≤
        ENNReal.ofReal (B * s ^ (-(1 / 2) : ℝ)) := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hN := halfLine_bracketingNumber_L2_le P hs0 hs1
    have hweight := entropyWeight_mono hN
    rw [entropyWeight_coe] at hweight
    refine hweight.trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hs2pos : 0 < s ^ 2 := sq_pos_of_pos hs0
    have hs2le : s ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hs1)]
    have hinv : 1 ≤ 1 / s ^ 2 := by
      rw [le_div_iff₀ hs2pos]
      simpa using hs2le
    have hceil : ((⌈8 / s ^ 2⌉₊ : ℕ) : ℝ) < 8 / s ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have harg : 1 + ((⌈8 / s ^ 2⌉₊ : ℕ) : ℝ) ≤ 10 / s ^ 2 := by
      have hrewrite : 10 / s ^ 2 = 2 + 8 / s ^ 2 + 2 * (1 / s ^ 2 - 1) := by ring
      rw [hrewrite]
      nlinarith
    have hypos : 0 < 1 / s := by positivity
    have hlog : Real.log (1 + ((⌈8 / s ^ 2⌉₊ : ℕ) : ℝ)) ≤
        A + 2 * (1 / s) := by
      calc
        Real.log (1 + ((⌈8 / s ^ 2⌉₊ : ℕ) : ℝ))
            ≤ Real.log (10 / s ^ 2) := Real.log_le_log (by positivity) harg
        _ = Real.log 10 + 2 * Real.log (1 / s) := by
          rw [show 10 / s ^ 2 = 10 * (1 / s) ^ 2 by ring,
            Real.log_mul (by norm_num) (pow_pos hypos 2).ne', Real.log_pow]
          norm_num
        _ ≤ A + 2 * (1 / s) := by
          rw [hA]
          have hy := Real.log_le_sub_one_of_pos hypos
          nlinarith
    have hsqrt_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
    have hsqrt_le : Real.sqrt s ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hs1
    have hspow : s ^ (-(1 / 2) : ℝ) = (Real.sqrt s)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs0.le]
    calc
      Real.sqrt (Real.log (1 + ((⌈8 / s ^ 2⌉₊ : ℕ) : ℝ)))
          ≤ Real.sqrt (A + 2 * (1 / s)) := Real.sqrt_le_sqrt hlog
      _ ≤ Real.sqrt A + Real.sqrt (2 * (1 / s)) :=
        sqrt_add_le A (2 * (1 / s)) hA0 (by positivity)
      _ = Real.sqrt A + Real.sqrt 2 / Real.sqrt s := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2), one_div, Real.sqrt_inv]
        ring
      _ ≤ Real.sqrt A / Real.sqrt s + Real.sqrt 2 / Real.sqrt s := by
        have hle : Real.sqrt A ≤ Real.sqrt A / Real.sqrt s := by
          rw [le_div_iff₀ hsqrt_pos]
          nlinarith [Real.sqrt_nonneg A]
        linarith
      _ = B * s ^ (-(1 / 2) : ℝ) := by rw [hB, hspow]; ring
  have hInt : ∫⁻ s in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (s ^ (-(1 / 2) : ℝ)) ∂volume < ⊤ := by
    have hi : IntegrableOn (fun s : ℝ ↦ s ^ (-(1 / 2) : ℝ))
        (Set.Ioc (0 : ℝ) 1) volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun s : ℝ ↦ s ^ (-(1 / 2) : ℝ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact Real.rpow_nonneg hs.1.le _
    exact (hasFiniteIntegral_iff_ofReal hnn).mp hi.2
  rw [bracketingEntropyIntegral_eq_setLIntegral]
  apply lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc hdom)
  have hsplit : (∫⁻ s in Set.Ioc (0 : ℝ) 1,
      ENNReal.ofReal (B * s ^ (-(1 / 2) : ℝ)) ∂volume) =
      ENNReal.ofReal B * ∫⁻ s in Set.Ioc (0 : ℝ) 1,
        ENNReal.ofReal (s ^ (-(1 / 2) : ℝ)) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s _ ↦ ?_)
    rw [← ENNReal.ofReal_mul hB0]
  rw [hsplit]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInt

end AsymptoticStatistics.EmpiricalProcess
