module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.VCSharpCoveringTransfer
public import StatLean.AsymptoticStatistics.EmpiricalProcess.VCUniformEntropy
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyMaximal

@[expose] public section

/-!
# VC uniform covering and entropy bounds

This module proves the corrected two-radius form of van der Vaart Lemma
19.15, its original-radius corollary, and the resulting entropy integral.  The
printed original-radius RHS is not asserted because it misses radius rescaling.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter
open scoped ENNReal

universe u

open UniformEntropyStructural

/-- Corrected source form of vdV Lemma 19.15: the strict-cover bound controls radius `2 * ε` with
the printed RHS.  The factor `2` belongs in the radius; this does not assert
the false printed original-radius statement. -/
theorem vcSubgraph_uniformLpCoveringNumber_twoRadius_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω)
        (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : ℕ) (r ε : ℝ),
        @IsVCSubgraphClass Ω mΩ F V →
        @UniformEntropyStructural.IsEnvelope Ω F G →
        1 ≤ r → 0 < ε → ε < 1 →
        ∃ N : ℕ,
          @uniformLpCoveringNumber Ω mΩ F G r (2 * ε) ≤ (N : ℕ∞) ∧
          (N : ℝ) ≤ K * V * (16 * Real.exp 1) ^ V *
            (1 / ε) ^ (r * (V - 1 : ℕ)) := by
  obtain ⟨K, hK, hcover⟩ := exists_universalVCAdmissibleStrictTwoRadiusCoverConstant
  refine ⟨K, hK, ?_⟩
  intro Ω mΩ F G V r ε hVC hG hr hε₀ hε₁
  letI : MeasurableSpace Ω := mΩ
  let B : ℝ := K * V * (16 * Real.exp 1) ^ V *
    (1 / ε) ^ (r * (V - 1 : ℕ))
  let N : ℕ := ⌊B⌋₊
  have hB₀ : 0 ≤ B := by
    dsimp only [B]
    positivity
  refine ⟨N, ?_, ?_⟩
  · unfold uniformLpCoveringNumber
    refine iSup_le fun Q => iSup_le fun hQ => ?_
    obtain ⟨C, hCcover, hCcard⟩ :=
      hcover Ω mΩ F G V Q r ε hVC hG hQ hr hε₀ hε₁
    have hCN : C.card ≤ N := by
      apply Nat.le_floor
      simpa only [B] using hCcard
    calc
      finiteLpCoveringNumber F G Q r (2 * ε) ≤ (C.card : ℕ∞) :=
        finiteLpCoveringNumber_le_of_cover hCcover
      _ ≤ (N : ℕ∞) := by exact_mod_cast hCN
  · simpa only [N] using Nat.floor_le hB₀

/-- Corrected original-radius corollary, obtained at `ε / 2`.  Its RHS contains
`(2 / ε)^(r(V-1))`; it is deliberately not vdV's false printed RHS. -/
theorem vcSubgraph_uniformLpCoveringNumber_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω)
        (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : ℕ) (r ε : ℝ),
        @IsVCSubgraphClass Ω mΩ F V →
        @UniformEntropyStructural.IsEnvelope Ω F G →
        1 ≤ r → 0 < ε → ε < 1 →
        ∃ N : ℕ,
          @uniformLpCoveringNumber Ω mΩ F G r ε ≤ (N : ℕ∞) ∧
          (N : ℝ) ≤ K * V * (16 * Real.exp 1) ^ V *
            (2 / ε) ^ (r * (V - 1 : ℕ)) := by
  obtain ⟨K, hK, htwo⟩ := vcSubgraph_uniformLpCoveringNumber_twoRadius_le
  refine ⟨K, hK, ?_⟩
  intro Ω mΩ F G V r ε hVC hG hr hε₀ hε₁
  obtain ⟨N, hNcover, hNcard⟩ :=
    htwo Ω mΩ F G V r (ε / 2) hVC hG hr (by positivity) (by linarith)
  refine ⟨N, ?_, ?_⟩
  · simpa only [show (2 : ℝ) * (ε / 2) = ε by ring] using hNcover
  · have hrecip : (1 : ℝ) / (ε / 2) = 2 / ε := by
      field_simp [hε₀.ne']
    simpa only [hrecip] using hNcard

/-- A VC-subgraph class with an envelope has finite uniform `L²` entropy
integral via the corrected covering theorem, without measurability, moment,
or finite-support assumptions. -/
theorem vcSubgraph_uniformEntropyIntegral_lt_top
    [MeasurableSpace Ω] {F : Set (Ω → ℝ)} {G : Ω → ℝ} {V : ℕ}
    (hVC : IsVCSubgraphClass F V)
    (hG : UniformEntropyStructural.IsEnvelope F G) :
    uniformEntropyIntegral 1 F G 2 < ⊤ := by
  obtain ⟨K, hK, htwo⟩ := vcSubgraph_uniformLpCoveringNumber_twoRadius_le
  let A : ℝ := K * V * (16 * Real.exp 1) ^ V
  have hA₀ : 0 ≤ A := by dsimp only [A]; positivity
  by_cases hV : V ≤ 1
  · let M : ℕ := ⌊A⌋₊
    have hdom : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        entropyWeight (uniformLpCoveringNumber F G 2 ε) ≤
          entropyWeight (M : ℕ∞) := by
      intro ε hε
      obtain ⟨N, hNcover, hNcard⟩ :=
        htwo Ω ‹MeasurableSpace Ω› F G V 2 (ε / 2) hVC hG
          (by norm_num) (by linarith [hε.1]) (by linarith [hε.2])
      have hcover : uniformLpCoveringNumber F G 2 ε ≤ (N : ℕ∞) := by
        simpa only [show (2 : ℝ) * (ε / 2) = ε by ring] using hNcover
      have hNM : N ≤ M := by
        apply Nat.le_floor
        calc
          (N : ℝ) ≤ K * V * (16 * Real.exp 1) ^ V *
              (1 / (ε / 2)) ^ ((2 : ℝ) * (V - 1 : ℕ)) := hNcard
          _ = A := by
            rw [Nat.sub_eq_zero_of_le hV]
            simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one, A]
      exact (entropyWeight_mono hcover).trans
        (entropyWeight_mono (by exact_mod_cast hNM))
    unfold uniformEntropyIntegral
    calc
      (∫⁻ ε in Set.Ioc (0 : ℝ) 1,
          entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume)
          ≤ ∫⁻ _ε in Set.Ioc (0 : ℝ) 1, entropyWeight (M : ℕ∞) ∂volume :=
        setLIntegral_mono_ae' measurableSet_Ioc (Eventually.of_forall hdom)
      _ = entropyWeight (M : ℕ∞) := by
        rw [setLIntegral_const, Real.volume_Ioc]
        norm_num
      _ < ⊤ := by
        rw [entropyWeight_coe]
        exact ENNReal.ofReal_lt_top
  · have hV₂ : 2 ≤ V := by omega
    let q : ℕ := 2 * (V - 1)
    let D : ℝ := max 1 A
    let C : ℝ := 2 * D
    have hD₁ : 1 ≤ D := by
      exact le_max_left 1 A
    have hC₀ : 0 < C := by dsimp only [C]; positivity
    have hq₁ : 1 ≤ q := by
      dsimp only [q]
      omega
    obtain ⟨Cp, hCp₀, hInt⟩ :=
      sqrt_log_pow_ratio_lintegral_le C hC₀ q
    have hdom : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        entropyWeight (uniformLpCoveringNumber F G 2 ε) ≤
          ENNReal.ofReal
            (Real.sqrt (Real.log (1 + (C * 1 / ε) ^ q))) := by
      intro ε hε
      obtain ⟨N, hNcover, hNcard⟩ :=
        htwo Ω ‹MeasurableSpace Ω› F G V 2 (ε / 2) hVC hG
          (by norm_num) (by linarith [hε.1]) (by linarith [hε.2])
      have hcover : uniformLpCoveringNumber F G 2 ε ≤ (N : ℕ∞) := by
        simpa only [show (2 : ℝ) * (ε / 2) = ε by ring] using hNcover
      have hrecip : (1 : ℝ) / (ε / 2) = 2 / ε := by
        field_simp [hε.1.ne']
      have hexp : (2 : ℝ) * (V - 1 : ℕ) = (q : ℝ) := by
        dsimp only [q]
        push_cast
        rfl
      have hNpoly : (N : ℝ) ≤ (C * 1 / ε) ^ q := by
        calc
          (N : ℝ) ≤ K * V * (16 * Real.exp 1) ^ V *
              (1 / (ε / 2)) ^ ((2 : ℝ) * (V - 1 : ℕ)) := hNcard
          _ = A * (2 / ε) ^ q := by
            rw [hrecip, hexp, Real.rpow_natCast]
          _ ≤ D * (2 / ε) ^ q := by
            exact mul_le_mul_of_nonneg_right (le_max_right 1 A)
              (pow_nonneg (div_nonneg (by norm_num) hε.1.le) q)
          _ ≤ D ^ q * (2 / ε) ^ q := by
            exact mul_le_mul_of_nonneg_right (le_self_pow₀ hD₁ (by omega))
              (pow_nonneg (div_nonneg (by norm_num) hε.1.le) q)
          _ = (C * 1 / ε) ^ q := by
            rw [← mul_pow]
            congr 1
            dsimp only [C]
            ring
      calc
        entropyWeight (uniformLpCoveringNumber F G 2 ε)
            ≤ entropyWeight (N : ℕ∞) := entropyWeight_mono hcover
        _ = ENNReal.ofReal (Real.sqrt (Real.log (1 + (N : ℝ)))) :=
          entropyWeight_coe N
        _ ≤ ENNReal.ofReal
              (Real.sqrt (Real.log (1 + (C * 1 / ε) ^ q))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.sqrt_le_sqrt
          apply Real.log_le_log (by positivity)
          linarith
    unfold uniformEntropyIntegral
    calc
      (∫⁻ ε in Set.Ioc (0 : ℝ) 1,
          entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume)
          ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) 1,
              ENNReal.ofReal
                (Real.sqrt (Real.log (1 + (C * 1 / ε) ^ q))) ∂volume :=
        setLIntegral_mono_ae' measurableSet_Ioc (Eventually.of_forall hdom)
      _ ≤ ENNReal.ofReal (Cp * 1) := hInt 1 one_pos
      _ < ⊤ := ENNReal.ofReal_lt_top

end AsymptoticStatistics.EmpiricalProcess
