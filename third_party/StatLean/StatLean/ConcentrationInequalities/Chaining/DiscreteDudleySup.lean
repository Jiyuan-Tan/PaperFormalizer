module
public import StatLean.ConcentrationInequalities.Chaining.DiscreteDudley
public import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
public import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

@[expose] public section

/-!
# Discrete Dudley inequality with a genuine supremum

Honest `sup_{t ∈ T}` forms of the discrete Dudley inequality
(HDP Theorem 8.1.4, Eq. (8.2), and its absolute Remark 8.1.5 twin) over an
arbitrary — possibly uncountable — index set, against the dyadic entropy
series `dudleyLSum T`: the per-finite-subset anchored form, countable-subset
cores, countable displays, and separable-supremum forms. Companion of
`Chaining/DudleySup.lean` (integral RHS) at the series RHS; constants `6√3`
(anchored/mean-zero) and `20` (absolute) frozen as in `discrete_dudley` /
`discrete_dudley_abs`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.4, Eq. (8.2), Remark 8.1.5;
uncountable forms per the p. 227 footnote through separable versions
(`Chaining/SeparableProcess.lean`).

**Proof formalization notes.** Same engine recipe as `DudleySup.lean` with
`discrete_dudley` / `discrete_dudley_abs` as the per-finite-subset inputs
and `dudleyLSum T` as the `ℝ≥0∞` carrier (divergent series = honest `⊤`).
The anchored family contains `0` (anchor in the subset / `t₀ ∈ T`), so the
`ENNReal.ofReal` carrier is junk-free; a bare mean-zero `⨆ t ∈ T, X t ω`
statement would be FALSE at `|T| = 1`. Named-sorry fallback of this work
item: `discrete_dudley_anchored` (the sup'-shift algebra).

**Bibliographic comments.** R. M. Dudley, *J. Funct. Anal.* 1 (1967),
290–330; the dyadic-series form is HDP's Theorem 8.1.4 route to the
entropy integral.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Discrete Dudley inequality, anchored mean-zero form, per finite
subset** (HDP §8.1, Theorem 8.1.4, Eq. (8.2)): for a finite `F ⊆ T`
containing the anchor,
`E max_{t∈F} (X_t − X_{t₀}) ≤ 6√3 · K · dudleyLSum T` in `ℝ≥0∞`. Under
`hmean` the anchor's mean cancels, so this equals `E max_{t∈F} X_t`.
Constant `6√3` as in `discrete_dudley`. -/
theorem discrete_dudley_anchored {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- USER-INPUT: the anchor point, inside the subset; HDP §8.1
    {t₀ : E} (ht₀F : t₀ ∈ F) :
    ENNReal.ofReal (∫ ω, F.sup' ⟨t₀, ht₀F⟩ (fun t => X t ω - X t₀ ω) ∂μ)
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  classical
  have hFne : F.Nonempty := ⟨t₀, ht₀F⟩
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hF (Finset.mem_coe.mpr ht)
  have ht₀T : t₀ ∈ T := hmemT t₀ ht₀F
  -- Pointwise `sup'`-shift: subtracting the anchor commutes with the finite max.
  have hpt : ∀ ω, F.sup' hFne (fun t => X t ω - X t₀ ω)
      = (F.sup' hFne fun t => X t ω) - X t₀ ω := by
    intro ω
    have := Finset.comp_sup'_eq_sup'_comp (s := F) hFne (f := fun t => X t ω)
      (fun x : ℝ => x - X t₀ ω) (fun x y => (max_sub_sub_right x y (X t₀ ω)).symm)
    exact this.symm
  -- Integrability of the finite maximum (per-coordinate `hint`).
  have hIntSup : MeasureTheory.Integrable (fun ω => F.sup' hFne fun t => X t ω) μ :=
    integrable_sup'_finset hFne (fun i hi => hint i (hmemT i hi))
  -- The anchor's mean cancels under `hmean`.
  have hsplit : (∫ ω, F.sup' hFne (fun t => X t ω - X t₀ ω) ∂μ)
      = (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ) - ∫ ω, X t₀ ω ∂μ := by
    rw [show (fun ω => F.sup' hFne fun t => X t ω - X t₀ ω)
          = (fun ω => (F.sup' hFne fun t => X t ω) - X t₀ ω) from funext hpt]
    exact integral_sub hIntSup (hint t₀ ht₀T)
  rw [hsplit, hmean t₀ ht₀T, sub_zero]
  exact discrete_dudley hcov hne hmeas hint hmean hinc hF hFne

/-- **Discrete Dudley inequality, absolute form, countable-subset supremum
core** (HDP §8.1, Remark 8.1.5 discrete):
`∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 20·K·dudleyLSum T` for any countable
`C ⊆ T`, entropy of the FULL `T`. -/
theorem discrete_dudley_abs_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T := by
  classical
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  -- Uniform ψ₂ scale of the anchored increments over the (bounded) carrier.
  set L : ℝ≥0 := K * Real.toNNReal (Metric.diam T) with hL
  have hSG : ∀ t ∈ T, subGaussianNorm (fun ω => X t ω - X t₀ ω) μ ≤ (L : ℝ≥0∞) := by
    intro t ht
    refine (hinc t₀ ht₀ t ht).trans ?_
    have hde : edist t₀ t ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd ht₀ ht)
    calc (K : ℝ≥0∞) * edist t₀ t
        ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
      _ = (L : ℝ≥0∞) := by rw [hL]; push_cast; ring
  -- Monotone-convergence lift from the per-finite-subset absolute form.
  refine lintegral_biSup_le_of_forall_finset
    (g := fun t ω => ENNReal.ofReal |X t ω - X t₀ ω|) hCcnt
    (fun t ht => (((hmeas t (hC ht)).sub (hmeas t₀ ht₀)).abs).ennreal_ofReal) ?_
  intro F hFC hFne
  have hFT : ↑F ⊆ T := hFC.trans hC
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hFT (Finset.mem_coe.mpr ht)
  have h0 : ∀ ω, 0 ≤ F.sup' hFne fun t => |X t ω - X t₀ ω| := by
    intro ω
    obtain ⟨t₁, ht₁⟩ := hFne
    exact (abs_nonneg _).trans (Finset.le_sup' (fun t => |X t ω - X t₀ ω|) ht₁)
  have hInt : MeasureTheory.Integrable
      (fun ω => F.sup' hFne fun t => |X t ω - X t₀ ω|) μ := by
    have hbi := integrable_biSup_abs (s := F) hFne (Y := fun t ω => X t ω - X t₀ ω)
      (L := L) (fun i hi => (hmeas i (hmemT i hi)).sub (hmeas t₀ ht₀))
      (fun i hi => hSG i (hmemT i hi))
    have hEq : (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|)
        = fun ω => F.sup' hFne fun t => |X t ω - X t₀ ω| :=
      funext fun ω => biSup_finset_eq_sup' hFne _ (fun _ _ => abs_nonneg _)
    rwa [hEq] at hbi
  calc ∫⁻ ω, ⨆ t ∈ F, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      = ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ) :=
        lintegral_biSup_finset_ofReal_eq hFne h0 hInt
    _ ≤ ENNReal.ofReal 20 * K * dudleyLSum T :=
        discrete_dudley_abs hcov hne hmeas hinc ht₀ hFT hFne

/-- **Discrete Dudley inequality, anchored mean-zero form, countable-subset
supremum core** (HDP §8.1, Theorem 8.1.4):
`∫⁻ sup_{t∈C} (X_t − X_{t₀})⁺ ≤ 6√3·K·dudleyLSum T` for countable `C ⊆ T`;
the anchor is required in `T`, not in `C`. -/
theorem discrete_dudley_anchored_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  classical
  -- Monotone-convergence lift; each finite window is enlarged by the anchor so
  -- that the `ENNReal.ofReal` carrier is junk-free (a `0`-valued member).
  refine lintegral_biSup_le_of_forall_finset
    (g := fun t ω => ENNReal.ofReal (X t ω - X t₀ ω)) hCcnt
    (fun t ht => ((hmeas t (hC ht)).sub (hmeas t₀ ht₀)).ennreal_ofReal) ?_
  intro F hFC hFne
  have ht₀F' : t₀ ∈ insert t₀ F := Finset.mem_insert_self t₀ F
  have hF'ne : (insert t₀ F).Nonempty := ⟨t₀, ht₀F'⟩
  have hF'T : ↑(insert t₀ F) ⊆ T := by
    intro x hx
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with rfl | hxF
    · exact ht₀
    · exact hC (hFC (Finset.mem_coe.mpr hxF))
  have hmemT' : ∀ t, t ∈ insert t₀ F → t ∈ T :=
    fun t ht => hF'T (Finset.mem_coe.mpr ht)
  have h0 : ∀ ω, 0 ≤ (insert t₀ F).sup' hF'ne fun t => X t ω - X t₀ ω := by
    intro ω
    have := Finset.le_sup' (f := fun t => X t ω - X t₀ ω) (s := insert t₀ F) ht₀F'
    rwa [sub_self] at this
  have hInt : MeasureTheory.Integrable
      (fun ω => (insert t₀ F).sup' hF'ne fun t => X t ω - X t₀ ω) μ :=
    integrable_sup'_finset hF'ne
      (fun i hi => (hint i (hmemT' i hi)).sub (hint t₀ ht₀))
  have hmono : ∀ ω, (⨆ t ∈ F, ENNReal.ofReal (X t ω - X t₀ ω))
      ≤ ⨆ t ∈ insert t₀ F, ENNReal.ofReal (X t ω - X t₀ ω) := by
    intro ω
    exact iSup₂_le fun t ht =>
      le_iSup₂ (f := fun t (_ : t ∈ insert t₀ F) => ENNReal.ofReal (X t ω - X t₀ ω))
        t (Finset.mem_insert_of_mem ht)
  calc ∫⁻ ω, ⨆ t ∈ F, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ∫⁻ ω, ⨆ t ∈ insert t₀ F, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ :=
        lintegral_mono hmono
    _ = ENNReal.ofReal
          (∫ ω, (insert t₀ F).sup' hF'ne (fun t => X t ω - X t₀ ω) ∂μ) :=
        lintegral_biSup_finset_ofReal_eq hF'ne h0 hInt
    _ ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T :=
        discrete_dudley_anchored hcov hne hmeas hint hmean hinc hF'T ht₀F'

/-- **Discrete Dudley inequality, absolute form, separable supremum**
(HDP §8.1, Remark 8.1.5 discrete, general `T`):
`∫⁻ sup_{t∈T} |X_t − X_{t₀}| ≤ 20·K·dudleyLSum T` in `ℝ≥0∞` for a
separable version of the process. -/
theorem discrete_dudley_abs_separable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T := by
  classical
  -- The separability witness, enlarged by the anchor so it carries `t₀`.
  obtain ⟨T₀, hT₀T, hT₀cnt, hae⟩ := hsep
  have hCT : insert t₀ T₀ ⊆ T := Set.insert_subset ht₀ hT₀T
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  -- Value-closure transport of the (lower-semicontinuous) integrand shape.
  have hcongr : ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      = ∫⁻ ω, ⨆ t ∈ insert t₀ T₀, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have hx : ∀ t ∈ T, X t ω ∈ closure ((fun s => X s ω) '' (insert t₀ T₀)) :=
      fun t ht => closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t ht)
    exact biSup_ennreal_comp_eq_of_forall_mem_closure (x := fun t => X t ω) hCT hx
      (φ := fun v => ENNReal.ofReal |v - X t₀ ω|)
      (Continuous.lowerSemicontinuous
        (ENNReal.continuous_ofReal.comp ((continuous_id.sub continuous_const).abs)))
  rw [hcongr]
  exact discrete_dudley_abs_countable_subset hcov hne hmeas hinc ht₀ hCT hCcnt

/-- **Discrete Dudley inequality (Theorem 8.1.4), separable supremum**
(HDP §8.1, Eq. (8.2), general `T`): for a separable version of a mean-zero
process, `∫⁻ sup_{t∈T} (X_t − X_{t₀})⁺ ≤ 6√3·K·dudleyLSum T` in `ℝ≥0∞` —
the junk-free rendering of `E sup_{t∈T} X_t ≤ CK Σ_k 2^{−k}√log 𝒩`. -/
theorem discrete_dudley_anchored_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  classical
  -- The separability witness, enlarged by the anchor so it carries `t₀`.
  obtain ⟨T₀, hT₀T, hT₀cnt, hae⟩ := hsep
  have hCT : insert t₀ T₀ ⊆ T := Set.insert_subset ht₀ hT₀T
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  -- Value-closure transport of the (lower-semicontinuous) integrand shape.
  have hcongr : ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      = ∫⁻ ω, ⨆ t ∈ insert t₀ T₀, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have hx : ∀ t ∈ T, X t ω ∈ closure ((fun s => X s ω) '' (insert t₀ T₀)) :=
      fun t ht => closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t ht)
    exact biSup_ennreal_comp_eq_of_forall_mem_closure (x := fun t => X t ω) hCT hx
      (φ := fun v => ENNReal.ofReal (v - X t₀ ω))
      (Continuous.lowerSemicontinuous
        (ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const)))
  rw [hcongr]
  exact discrete_dudley_anchored_countable_subset hcov hne hmeas hint hmean hinc
    ht₀ hCT hCcnt

/-- **Discrete Dudley inequality, absolute form, countable supremum**
(HDP §8.1, Remark 8.1.5 discrete): the `C := T` display of the
countable-subset core. -/
theorem discrete_dudley_abs_countable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T :=
  discrete_dudley_abs_countable_subset hcov hne hmeas hinc ht₀ subset_rfl hcnt

/-- **Discrete Dudley inequality (Theorem 8.1.4), countable supremum**
(HDP §8.1, Eq. (8.2)): the `C := T` display of the anchored
countable-subset core. -/
theorem discrete_dudley_anchored_countable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T :=
  discrete_dudley_anchored_countable_subset hcov hne hmeas hint hmean hinc ht₀
    subset_rfl hcnt

end StatLean.ConcentrationInequalities
