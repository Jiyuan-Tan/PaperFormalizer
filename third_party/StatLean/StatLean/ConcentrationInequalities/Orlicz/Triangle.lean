module
public import StatLean.ConcentrationInequalities.Orlicz.Basic
public import StatLean.ConcentrationInequalities.Orlicz.Generators
public import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public section

/-!
# Orlicz norm — triangle inequality

The triangle inequality for the general Luxemburg norm,
$$ \|X + Y\|_\psi \le \|X\|_\psi + \|Y\|_\psi, $$
via convexity: if `a` is a gauge for `X` and `b` a gauge for `Y`, then
`a + b` is a gauge for `X + Y` since
$$ \psi\Bigl(\frac{u + v}{a+b}\Bigr)
   \le \frac{a}{a+b}\,\psi\Bigl(\frac{u}{a}\Bigr)
     + \frac{b}{a+b}\,\psi\Bigl(\frac{v}{b}\Bigr). $$
Instances for the ψ₂/ψ₁ generators (first half of the B4 bridge; homogeneity
is `Orlicz/Basic.lean`) and the finite-sum corollary.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Exercise 2.42 (‖·‖_{ψ₂} is a norm) and the display
after Eq. (2.18) in §2.6.1; Exercise 2.43 for the general Orlicz norm.

**Proof formalization notes.** The `ENNReal` inf-addition step
("`⨅ + ⨅ = ⨅` of sums") has no packaged Mathlib lemma on this index; it is
hand-rolled through the ε-free witness pattern
`exists_mem_orliczSet_lt_of_orliczNorm_lt` with explicit case splits on empty
gauge sets (`norm = ⊤` makes the bound trivial). Measurability of ψ and
a.e.-measurability of X, Y are LEAN-ONLY hypotheses: the plain `lintegral` is
not subadditive without measurability of the integrands. Constants: exact
(the triangle inequality carries no constant). Named-sorry fallback of this
work item: `orliczNorm_add_le` itself, with the ψ₂/ψ₁ instances and the
finset-sum corollary derived from it.

**Bibliographic comments.** That the Luxemburg gauge is a norm is Luxemburg's
thesis (Delft, 1955). See also Rao–Ren, *Theory of Orlicz Spaces*, Dekker
1991, §III.3.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Core gauge-addition step** (the Luxemburg convexity argument): if `a` is a
gauge for `X` and `b` a gauge for `Y`, then `a + b` is a gauge for `X + Y`.
Pointwise `ψ(|X+Y|/(a+b)) ≤ (a/(a+b))·ψ(|X|/a) + (b/(a+b))·ψ(|Y|/b)` by the
triangle inequality, monotonicity and convexity of `ψ`; integrating and using
the two gauge conditions gives `∫⁻ ψ(|X+Y|/(a+b)) ≤ a/(a+b) + b/(a+b) = 1`. -/
private lemma orliczSet_add_mem {ψ : ℝ → ℝ}
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    (hψ_conv : ConvexOn ℝ (Set.Ici 0) ψ)
    (hψ_meas : Measurable ψ)
    {X Y : Ω → ℝ} {μ : Measure Ω}
    -- `hY` (Y's a.e.-measurability) is unused: the additive `lintegral` split only
    -- needs the first summand measurable; kept for a symmetric interface.
    (hX : AEMeasurable X μ) (_hY : AEMeasurable Y μ)
    {a b : ℝ≥0} (ha : a ∈ orliczSet ψ X μ) (hb : b ∈ orliczSet ψ Y μ) :
    (a + b) ∈ orliczSet ψ (fun ω => X ω + Y ω) μ := by
  obtain ⟨ha0, haInt⟩ := ha
  obtain ⟨hb0, hbInt⟩ := hb
  have ha0' : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha0
  have hb0' : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb0
  have hab0 : (0:ℝ) < (a:ℝ) + (b:ℝ) := by linarith
  have hwa : (0:ℝ) ≤ (a:ℝ) / ((a:ℝ) + (b:ℝ)) := by positivity
  have hwb : (0:ℝ) ≤ (b:ℝ) / ((a:ℝ) + (b:ℝ)) := by positivity
  have hsum' : (a:ℝ) / ((a:ℝ) + (b:ℝ)) + (b:ℝ) / ((a:ℝ) + (b:ℝ)) = 1 := by
    rw [← add_div, div_self hab0.ne']
  -- a.e.-measurability of the two ψ-integrands (needed for the additive split)
  have hg₁ : AEMeasurable (fun ω => ENNReal.ofReal (ψ (|X ω| / (a:ℝ)))) μ :=
    (hψ_meas.comp_aemeasurable (hX.abs.div_const _)).ennreal_ofReal
  -- pointwise convexity bound
  have hpt : ∀ ω, ENNReal.ofReal (ψ (|X ω + Y ω| / ((a:ℝ) + (b:ℝ))))
      ≤ ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ))) * ENNReal.ofReal (ψ (|X ω| / (a:ℝ)))
        + ENNReal.ofReal ((b:ℝ) / ((a:ℝ) + (b:ℝ))) * ENNReal.ofReal (ψ (|Y ω| / (b:ℝ))) := by
    intro ω
    have hu0 : (0:ℝ) ≤ |X ω| := abs_nonneg _
    have hv0 : (0:ℝ) ≤ |Y ω| := abs_nonneg _
    have hxa : |X ω| / (a:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (by positivity)
    have hyb : |Y ω| / (b:ℝ) ∈ Set.Ici (0:ℝ) := Set.mem_Ici.mpr (by positivity)
    have hconv := hψ_conv.2 hxa hyb hwa hwb hsum'
    simp only [smul_eq_mul] at hconv
    -- the convex combination equals the scaled sum
    have hid : (a:ℝ) / ((a:ℝ) + (b:ℝ)) * (|X ω| / (a:ℝ))
          + (b:ℝ) / ((a:ℝ) + (b:ℝ)) * (|Y ω| / (b:ℝ))
        = (|X ω| + |Y ω|) / ((a:ℝ) + (b:ℝ)) := by
      field_simp
    rw [hid] at hconv
    -- monotonicity shrinks the numerator |X+Y| ≤ |X| + |Y|
    have hmarg : |X ω + Y ω| / ((a:ℝ) + (b:ℝ)) ≤ (|X ω| + |Y ω|) / ((a:ℝ) + (b:ℝ)) :=
      (div_le_div_iff_of_pos_right hab0).mpr (abs_add_le _ _)
    have hm1 : |X ω + Y ω| / ((a:ℝ) + (b:ℝ)) ∈ Set.Ici (0:ℝ) :=
      Set.mem_Ici.mpr (by positivity)
    have hm2 : (|X ω| + |Y ω|) / ((a:ℝ) + (b:ℝ)) ∈ Set.Ici (0:ℝ) :=
      Set.mem_Ici.mpr (by positivity)
    have hreal : ψ (|X ω + Y ω| / ((a:ℝ) + (b:ℝ)))
        ≤ (a:ℝ) / ((a:ℝ) + (b:ℝ)) * ψ (|X ω| / (a:ℝ))
          + (b:ℝ) / ((a:ℝ) + (b:ℝ)) * ψ (|Y ω| / (b:ℝ)) :=
      (hψ_mono hm1 hm2 hmarg).trans hconv
    calc ENNReal.ofReal (ψ (|X ω + Y ω| / ((a:ℝ) + (b:ℝ))))
        ≤ ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ)) * ψ (|X ω| / (a:ℝ))
            + (b:ℝ) / ((a:ℝ) + (b:ℝ)) * ψ (|Y ω| / (b:ℝ))) :=
          ENNReal.ofReal_le_ofReal hreal
      _ ≤ ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ)) * ψ (|X ω| / (a:ℝ)))
            + ENNReal.ofReal ((b:ℝ) / ((a:ℝ) + (b:ℝ)) * ψ (|Y ω| / (b:ℝ))) :=
          ENNReal.ofReal_add_le
      _ = ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ))) * ENNReal.ofReal (ψ (|X ω| / (a:ℝ)))
            + ENNReal.ofReal ((b:ℝ) / ((a:ℝ) + (b:ℝ))) * ENNReal.ofReal (ψ (|Y ω| / (b:ℝ))) := by
          rw [ENNReal.ofReal_mul hwa, ENNReal.ofReal_mul hwb]
  refine ⟨add_pos ha0 hb0, ?_⟩
  simp only [NNReal.coe_add]
  calc ∫⁻ ω, ENNReal.ofReal (ψ (|X ω + Y ω| / ((a:ℝ) + (b:ℝ)))) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ)))
            * ENNReal.ofReal (ψ (|X ω| / (a:ℝ)))
          + ENNReal.ofReal ((b:ℝ) / ((a:ℝ) + (b:ℝ)))
            * ENNReal.ofReal (ψ (|Y ω| / (b:ℝ)))) ∂μ := lintegral_mono hpt
    _ = ∫⁻ ω, ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ)))
            * ENNReal.ofReal (ψ (|X ω| / (a:ℝ))) ∂μ
          + ∫⁻ ω, ENNReal.ofReal ((b:ℝ) / ((a:ℝ) + (b:ℝ)))
            * ENNReal.ofReal (ψ (|Y ω| / (b:ℝ))) ∂μ :=
        lintegral_add_left' (hg₁.const_mul _) _
    _ = ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ)))
            * ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (a:ℝ))) ∂μ
          + ENNReal.ofReal ((b:ℝ) / ((a:ℝ) + (b:ℝ)))
            * ∫⁻ ω, ENNReal.ofReal (ψ (|Y ω| / (b:ℝ))) ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((a:ℝ) / ((a:ℝ) + (b:ℝ))) * 1
          + ENNReal.ofReal ((b:ℝ) / ((a:ℝ) + (b:ℝ))) * 1 := by
        gcongr
    _ = 1 := by
        rw [mul_one, mul_one, ← ENNReal.ofReal_add hwa hwb, hsum', ENNReal.ofReal_one]

/-- **Triangle inequality** for the Orlicz norm (HDP Exercise 2.42; B4 part 1):
gauges add along the convexity splitting of ψ. -/
theorem orliczNorm_add_le {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- USER-INPUT: ψ convex on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_conv : ConvexOn ℝ (Set.Ici 0) ψ)
    -- LEAN-ONLY: measurability of ψ; plain lintegral is not subadditive without
    -- measurable integrands, satisfied by both generators, no book scope change
    (hψ_meas : Measurable ψ)
    {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; lintegral-additivity regularity
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; lintegral-additivity regularity
    (hY : AEMeasurable Y μ) :
    orliczNorm ψ (fun ω => X ω + Y ω) μ ≤ orliczNorm ψ X μ + orliczNorm ψ Y μ := by
  -- `⊤` case: an infinite bound is trivially an upper bound.
  rcases eq_or_ne (orliczNorm ψ X μ + orliczNorm ψ Y μ) ⊤ with hT | hT
  · rw [hT]; exact le_top
  -- Otherwise both norms are finite; beat every `c` above the sum by a gauge.
  obtain ⟨hBfin, hCfin⟩ := ENNReal.add_ne_top.mp hT
  refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
  -- room `r > 0` with `‖X‖ + ‖Y‖ + r < c`; split it in two.
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hc
  have hr2 : ((r : ℝ≥0∞) / 2) ≠ 0 := by
    simp [ENNReal.div_eq_zero_iff, (by exact_mod_cast hr0.ne' : (r : ℝ≥0∞) ≠ 0)]
  -- extract a gauge for `X` below `‖X‖ + r/2` and one for `Y` below `‖Y‖ + r/2`
  obtain ⟨a, haMem, haLt⟩ := exists_mem_orliczSet_lt_of_orliczNorm_lt
    (lt_of_lt_of_le (ENNReal.lt_add_right hBfin hr2) le_rfl)
  obtain ⟨b, hbMem, hbLt⟩ := exists_mem_orliczSet_lt_of_orliczNorm_lt
    (lt_of_lt_of_le (ENNReal.lt_add_right hCfin hr2) le_rfl)
  -- `a + b` is a gauge for `X + Y`, and `↑a + ↑b < c`
  have hmem := orliczSet_add_mem hψ_mono hψ_conv hψ_meas hX hY haMem hbMem
  refine le_of_lt ?_
  calc orliczNorm ψ (fun ω => X ω + Y ω) μ
      ≤ ((a + b : ℝ≥0) : ℝ≥0∞) := orliczNorm_le_of_mem hmem
    _ = (a : ℝ≥0∞) + (b : ℝ≥0∞) := by push_cast; rfl
    _ < (orliczNorm ψ X μ + (r : ℝ≥0∞) / 2) + (orliczNorm ψ Y μ + (r : ℝ≥0∞) / 2) :=
        ENNReal.add_lt_add haLt hbLt
    _ = orliczNorm ψ X μ + orliczNorm ψ Y μ + (r : ℝ≥0∞) := by
        rw [add_add_add_comm, ENNReal.add_halves]
    _ < c := hr

/-- Triangle inequality for the sub-Gaussian norm (B4; HDP Exercise 2.42 /
display after Eq. (2.18) in §2.6.1). -/
theorem subGaussianNorm_add_le {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; inherited from orliczNorm_add_le
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; inherited from orliczNorm_add_le
    (hY : AEMeasurable Y μ) :
    subGaussianNorm (fun ω => X ω + Y ω) μ
      ≤ subGaussianNorm X μ + subGaussianNorm Y μ :=
  orliczNorm_add_le psiTwo_monotoneOn psiTwo_convexOn psiTwo_measurable hX hY

/-- Triangle inequality for the sub-exponential norm (B4, ψ₁ instance). -/
theorem subExponentialNorm_add_le {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; inherited from orliczNorm_add_le
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; inherited from orliczNorm_add_le
    (hY : AEMeasurable Y μ) :
    subExponentialNorm (fun ω => X ω + Y ω) μ
      ≤ subExponentialNorm X μ + subExponentialNorm Y μ :=
  orliczNorm_add_le (psiOne_monotone.monotoneOn _) psiOne_convexOn psiOne_measurable hX hY

/-- Finite-sum triangle inequality (induction corollary; finiteness
ingredient for `IsSubGaussianVec`). -/
theorem orliczNorm_finset_sum_le {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- USER-INPUT: ψ convex on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_conv : ConvexOn ℝ (Set.Ici 0) ψ)
    -- USER-INPUT: ψ(0) ≤ 0 (book: ψ(0) = 0); HDP Exercise 2.42 — REQUIRED for
    -- the empty-sum base case (statement fix at the wave-2 gate: without it,
    -- ψ ≡ 1 is admissible and `orliczNorm ψ 0 μ = ⊤` for `μ univ > 1`, making
    -- the empty-sum inequality false; caught honestly by the closure session)
    (hψ0 : ψ 0 ≤ 0)
    -- LEAN-ONLY: measurability of ψ; inherited from orliczNorm_add_le
    (hψ_meas : Measurable ψ)
    {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of each summand; inherited from orliczNorm_add_le
    (hX : ∀ i ∈ s, AEMeasurable (X i) μ) :
    orliczNorm ψ (fun ω => ∑ i ∈ s, X i ω) μ ≤ ∑ i ∈ s, orliczNorm ψ (X i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      -- With `ψ 0 ≤ 0` the zero function has Orlicz norm 0 (`orliczNorm_zero`).
      exact le_of_eq (orliczNorm_zero hψ0 μ)
  | insert a s ha ih =>
      have hXa : AEMeasurable (X a) μ := hX a (Finset.mem_insert_self a s)
      have hXs : ∀ i ∈ s, AEMeasurable (X i) μ := fun i hi =>
        hX i (Finset.mem_insert_of_mem hi)
      have hsum_meas : AEMeasurable (fun ω => ∑ i ∈ s, X i ω) μ :=
        Finset.aemeasurable_fun_sum s hXs
      calc orliczNorm ψ (fun ω => ∑ i ∈ insert a s, X i ω) μ
          = orliczNorm ψ (fun ω => X a ω + ∑ i ∈ s, X i ω) μ := by
            simp only [Finset.sum_insert ha]
        _ ≤ orliczNorm ψ (X a) μ + orliczNorm ψ (fun ω => ∑ i ∈ s, X i ω) μ :=
            orliczNorm_add_le hψ_mono hψ_conv hψ_meas hXa hsum_meas
        _ ≤ orliczNorm ψ (X a) μ + ∑ i ∈ s, orliczNorm ψ (X i) μ := by
            gcongr
            exact ih hXs
        _ = ∑ i ∈ insert a s, orliczNorm ψ (X i) μ := by
            rw [Finset.sum_insert ha]

end StatLean.ConcentrationInequalities
