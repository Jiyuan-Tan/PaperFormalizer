module
public import StatLean.ConcentrationInequalities.Chaining.Dudley
public import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
public import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

@[expose] public section

/-!
# Dudley's inequality with a genuine supremum over the index set

Honest `sup_{t ∈ T}` forms of Dudley's integral inequality
(Theorem 8.1.3 / Eqs. (8.13), (8.14), (8.16)) over an arbitrary — possibly
uncountable — metric-space index set `T`, in three grades:

* `*_countable_subset` — the cores: supremum over a countable `C ⊆ T`,
  entropy of the FULL `T` (so no subset-covering constant loss), via the
  `CountableSupLift` engines fed by the per-finite-subset theorems;
* `*_countable` — `C := T` displays for countable `T`;
* `*_separable` — supremum over `T` itself under
  `hsep : IsSeparableProcess X T μ`, via the value-closure transports.

Carriers: mean-zero content is stated in the **anchored** form
`ENNReal.ofReal (X t ω − X t₀ ω)` with `t₀ ∈ T` (the family contains `0`,
so neither the `Real.sSup` junk nor the positive-part inflation can fire;
a bare `⨆ t ∈ T, X t ω` mean-zero statement is FALSE already at `|T| = 1`);
under `hmean`, `E sup_{t∈T} X_t = E sup_{t∈T} (X_t − X_{t₀})`, so the
anchored form IS Theorem 8.1.3. Absolute forms use
`ENNReal.ofReal |X t ω − X t₀ ω|` (Eq. (8.13)) and the pair double-sup
(Eq. (8.14)). Real Bochner displays carry the `≠ ⊤` junk-guard `hDL`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.3, Eqs. (8.13), (8.14),
(8.16); the uncountable forms realize the p. 227 footnote ("the general
case typically follows by approximation") through separable versions
(`Chaining/SeparableProcess.lean`).

**Proof formalization notes.** Frozen constants unchanged from the
per-finite-subset family: `12√3` (anchored/mean-zero), `40` (absolute),
`80 = 2 × 40` (pair, triangle through the anchor). The cores measure the
entropy of `T` directly (`F ⊆ C ⊆ T` composes into `dudley_inequality*`),
so the historical `ε/2` subset-covering loss does not reappear. The anchor
`t₀` is required in `T`, NOT in `C` — separable assemblies instantiate
`C := insert t₀ T₀` against the witness `T₀` of `hsep`, and all transports
run pointwise under `filter_upwards` (the shape `φ` captures `X t₀ ω`).
The published `dudley_inequality_countable` (pairwise-distance cap, fused
`ENNReal.ofReal (40 * K)` constant) is unchanged; the forms here
standardize on `Metric.diam T ≤ D` and the per-`F` constant shape
`ENNReal.ofReal 40 * ↑K`. Named-sorry fallback of this work item:
`dudley_inequality_abs_pair_separable` (the pair transport composition).

**Bibliographic comments.** R. M. Dudley, *J. Funct. Anal.* 1 (1967),
290–330; separable versions per J. L. Doob, *Stochastic Processes*, Wiley
1953, Ch. II, and R. van Handel, *Probability in High Dimension*, §5.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Integrability of the anchored absolute finite maximum over a finite
`F ⊆ T`, with the anchor `t₀` required only in `T` (not in `F`): the ψ₂
bounds come from `hinc` against the diameter of `T`, which is finite by
`isBounded_of_coveringNumber_ne_top`. Replay of the leg block of
`dudley_inequality_abs_pair` (`Chaining/Dudley.lean`). -/
private lemma integrable_sup'_abs_sub_of_coveringNumber {X : E → Ω → ℝ}
    {K : ℝ≥0} {T : Set E} [IsProbabilityMeasure μ]
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    {F : Finset E} (hF : ↑F ⊆ T) (hFne : F.Nonempty) :
    MeasureTheory.Integrable (fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|)) μ := by
  classical
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  set L : ℝ≥0 := K * Real.toNNReal (Metric.diam T) with hLdef
  have hB : MeasureTheory.Integrable (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|) μ := by
    refine integrable_biSup_abs hFne (L := L) (fun t ht => ?_) (fun t ht => ?_)
    · exact (hmeas t (hF (Finset.mem_coe.mpr ht))).sub (hmeas t₀ ht₀)
    · have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
      refine (hinc t₀ ht₀ t htT).trans ?_
      have hde : edist t₀ t ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd ht₀ htT)
      calc (K : ℝ≥0∞) * edist t₀ t
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = (L : ℝ≥0∞) := by rw [hLdef]; push_cast; ring
  have heq : (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|)
      = fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|) :=
    funext fun ω => biSup_finset_eq_sup' hFne (fun t => |X t ω - X t₀ ω|)
      (fun _ _ => abs_nonneg _)
  rwa [heq] at hB

/-- **Dudley's inequality, anchored mean-zero form, per finite subset**
(HDP §8.1, Theorem 8.1.3 + Eq. (8.16)): for a finite `F ⊆ T` containing the
anchor, `E max_{t∈F} (X_t − X_{t₀}) ≤ 12√3 · K · ∫₀^D √(log 𝒩(T,d,ε)) dε`
in `ℝ≥0∞`. Under `hmean` the anchor's mean cancels, so this equals
`E max_{t∈F} X_t` — the Remark 7.2.1 finite stage of the anchored supremum
forms below. Constant `12√3` as in `dudley_inequality`. -/
theorem dudley_inequality_anchored {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- USER-INPUT: the anchor point, inside the subset; HDP §8.1
    {t₀ : E} (ht₀F : t₀ ∈ F) :
    ENNReal.ofReal (∫ ω, F.sup' ⟨t₀, ht₀F⟩ (fun t => X t ω - X t₀ ω) ∂μ)
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  classical
  have hFne : F.Nonempty := ⟨t₀, ht₀F⟩
  have ht₀T : t₀ ∈ T := hF (Finset.mem_coe.mpr ht₀F)
  have hIntSup : MeasureTheory.Integrable (fun ω => F.sup' hFne (fun t => X t ω)) μ :=
    integrable_sup'_finset hFne (fun i hi => hint i (hF (Finset.mem_coe.mpr hi)))
  -- Shift the anchor out of the finite maximum (`φ := (· − X t₀ ω)` is a
  -- lattice map on `ℝ`).
  have hpt : ∀ ω, F.sup' hFne (fun t => X t ω - X t₀ ω)
      = F.sup' hFne (fun t => X t ω) - X t₀ ω := fun ω =>
    (Finset.comp_sup'_eq_sup'_comp hFne (f := fun t => X t ω) (fun v => v - X t₀ ω)
      (fun x y => (max_sub_sub_right x y (X t₀ ω)).symm)).symm
  have hInt : ∫ ω, F.sup' hFne (fun t => X t ω - X t₀ ω) ∂μ
      = ∫ ω, F.sup' hFne (fun t => X t ω) ∂μ := by
    simp only [hpt]
    rw [integral_sub hIntSup (hint t₀ ht₀T), hmean t₀ ht₀T, sub_zero]
  rw [show (⟨t₀, ht₀F⟩ : F.Nonempty) = hFne from rfl, hInt]
  exact dudley_inequality hcov hne hmeas hint hmean hinc hD hD0 hF hFne

/-- **Dudley's inequality, absolute form, countable-subset supremum core**
(HDP §8.1, Eq. (8.13)): `∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 40·K·∫₀^D √log 𝒩(T)`
for any countable `C ⊆ T`, entropy of the FULL `T`. The engine stage of the
countable and separable displays. -/
theorem dudley_inequality_abs_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D := by
  classical
  refine lintegral_biSup_le_of_forall_finset
    (g := fun t ω => ENNReal.ofReal |X t ω - X t₀ ω|) hCcnt
    (fun t ht => ((hmeas t (hC ht)).sub (hmeas t₀ ht₀)).abs.ennreal_ofReal) ?_
  intro F hFC hFne
  have hFT : ↑F ⊆ T := hFC.trans hC
  have h0 : ∀ ω, 0 ≤ F.sup' hFne (fun t => |X t ω - X t₀ ω|) := by
    intro ω
    obtain ⟨a, ha⟩ := hFne
    exact (abs_nonneg _).trans (Finset.le_sup' (fun t => |X t ω - X t₀ ω|) ha)
  rw [lintegral_biSup_finset_ofReal_eq hFne h0
    (integrable_sup'_abs_sub_of_coveringNumber hcov hmeas hinc ht₀ hFT hFne)]
  exact dudley_inequality_abs hcov hne hmeas hinc ht₀ hD hD0 hFT hFne

/-- **Dudley's inequality, anchored mean-zero form, countable-subset
supremum core** (HDP §8.1, Theorem 8.1.3 + Eq. (8.16)):
`∫⁻ sup_{t∈C} (X_t − X_{t₀})⁺ ≤ 12√3·K·∫₀^D √log 𝒩(T)` for countable
`C ⊆ T`. The anchor is required in `T`, not in `C`. -/
theorem dudley_inequality_anchored_countable_subset {X : E → Ω → ℝ}
    {K : ℝ≥0} {T : Set E}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  classical
  refine lintegral_biSup_le_of_forall_finset
    (g := fun t ω => ENNReal.ofReal (X t ω - X t₀ ω)) hCcnt
    (fun t ht => ((hmeas t (hC ht)).sub (hmeas t₀ ht₀)).ennreal_ofReal) ?_
  intro F hFC hFne
  -- Enlarge the window by the anchor so the anchored family contains `0`.
  have ht₀F' : t₀ ∈ insert t₀ F := Finset.mem_insert_self _ _
  have hF'ne : (insert t₀ F).Nonempty := ⟨t₀, ht₀F'⟩
  have hF'T : ↑(insert t₀ F) ⊆ T := by
    intro x hx
    rw [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact ht₀
    · exact hC (hFC hx)
  have hmono : ∀ ω, (⨆ t ∈ F, ENNReal.ofReal (X t ω - X t₀ ω))
      ≤ ⨆ t ∈ insert t₀ F, ENNReal.ofReal (X t ω - X t₀ ω) := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    exact le_biSup (fun t => ENNReal.ofReal (X t ω - X t₀ ω))
      (Finset.mem_insert_of_mem ht)
  have h0 : ∀ ω, 0 ≤ (insert t₀ F).sup' hF'ne (fun t => X t ω - X t₀ ω) := by
    -- The anchor's own member value is `0`, so the anchored family is
    -- nonnegative at the `sup'` level (the sharp `ofReal` junk guard).
    intro ω
    exact le_trans (le_of_eq (sub_self (X t₀ ω)).symm)
      (Finset.le_sup' (fun t => X t ω - X t₀ ω) ht₀F')
  have hInt : MeasureTheory.Integrable
      (fun ω => (insert t₀ F).sup' hF'ne (fun t => X t ω - X t₀ ω)) μ :=
    integrable_sup'_finset hF'ne
      (fun i hi => (hint i (hF'T (Finset.mem_coe.mpr hi))).sub (hint t₀ ht₀))
  calc ∫⁻ ω, ⨆ t ∈ F, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ∫⁻ ω, ⨆ t ∈ insert t₀ F, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ :=
        lintegral_mono hmono
    _ = ENNReal.ofReal
          (∫ ω, (insert t₀ F).sup' hF'ne (fun t => X t ω - X t₀ ω) ∂μ) :=
        lintegral_biSup_finset_ofReal_eq hF'ne h0 hInt
    _ ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D :=
        dudley_inequality_anchored hcov hne hmeas hint hmean hinc hD hD0 hF'T ht₀F'

/-- **Dudley's inequality, absolute form, separable supremum** (HDP §8.1,
Eq. (8.13), general `T`): for a separable version of the process,
`∫⁻ sup_{t∈T} |X_t − X_{t₀}| ≤ 40·K·∫₀^D √(log 𝒩(T,d,ε)) dε` in `ℝ≥0∞`,
NO mean-zero. `T` may be uncountable; `hsep` is the version-selection input
this requires (see `IsSeparableProcess`). Constant `40` as in
`dudley_inequality_abs`; cf. the published countable form
`dudley_inequality_countable` (pairwise cap, fused constant shape). -/
theorem dudley_inequality_abs_separable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D := by
  classical
  obtain ⟨T₀, hT₀T, hT₀cnt, hae⟩ := hsep
  -- The anchor is required in the carrier of the countable core.
  have hCT : insert t₀ T₀ ⊆ T := Set.insert_subset_iff.mpr ⟨ht₀, hT₀T⟩
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  have hcong : ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      = ∫⁻ ω, ⨆ t ∈ insert t₀ T₀, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    -- The shape `φ` captures `X t₀ ω`, so the transport runs pointwise in `ω`.
    exact biSup_ennreal_comp_eq_of_forall_mem_closure (x := fun t => X t ω)
      (φ := fun v => ENNReal.ofReal |v - X t₀ ω|) hCT
      (fun t ht => closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t ht))
      ((ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_id.sub continuous_const))).lowerSemicontinuous)
  rw [hcong]
  exact dudley_inequality_abs_countable_subset hcov hne hmeas hinc ht₀ hD hD0 hCT hCcnt

/-- **Dudley's integral inequality, separable supremum** (HDP §8.1,
Theorem 8.1.3 + Eq. (8.16), general `T`): for a separable version of a
mean-zero process,
`∫⁻ sup_{t∈T} (X_t − X_{t₀})⁺ ≤ 12√3·K·∫₀^D √(log 𝒩(T,d,ε)) dε` in
`ℝ≥0∞`. Under `hmean`, `E sup_{t∈T} X_t = E sup_{t∈T} (X_t − X_{t₀})` and
the anchored family contains `0`, so this is the junk-free rendering of
Theorem 8.1.3 (the bare `⨆ t ∈ T, X t ω` form is FALSE at `|T| = 1`).
Constant `12√3` as in `dudley_inequality`. -/
theorem dudley_inequality_anchored_separable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  classical
  obtain ⟨T₀, hT₀T, hT₀cnt, hae⟩ := hsep
  have hCT : insert t₀ T₀ ⊆ T := Set.insert_subset_iff.mpr ⟨ht₀, hT₀T⟩
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  have hcong : ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      = ∫⁻ ω, ⨆ t ∈ insert t₀ T₀, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    exact biSup_ennreal_comp_eq_of_forall_mem_closure (x := fun t => X t ω)
      (φ := fun v => ENNReal.ofReal (v - X t₀ ω)) hCT
      (fun t ht => closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t ht))
      ((ENNReal.continuous_ofReal.comp
        (continuous_id.sub continuous_const)).lowerSemicontinuous)
  rw [hcong]
  exact dudley_inequality_anchored_countable_subset hcov hne hmeas hint hmean hinc
    ht₀ hD hD0 hCT hCcnt

/-- **Dudley's inequality, absolute form, countable supremum**
(HDP §8.1, Eq. (8.13)): the `C := T` display of the countable-subset core,
with the diameter-shaped cap (cf. `dudley_inequality_countable`, the
published pairwise-cap twin). -/
theorem dudley_inequality_abs_countable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D :=
  dudley_inequality_abs_countable_subset hcov hne hmeas hinc ht₀ hD hD0
    (Set.Subset.refl T) hcnt

/-- **Dudley's integral inequality, anchored mean-zero form, countable
supremum** (HDP §8.1, Theorem 8.1.3 + Eq. (8.16)): the `C := T` display of
the anchored countable-subset core. -/
theorem dudley_inequality_anchored_countable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D :=
  dudley_inequality_anchored_countable_subset hcov hne hmeas hint hmean hinc ht₀
    hD hD0 (Set.Subset.refl T) hcnt

/-- **Dudley's inequality, absolute form, separable supremum, real display**
(HDP §8.1, Eq. (8.13)): under the finite-entropy junk-guard,
`∫ sup_{t∈T} |X_t − X_{t₀}| ≤ 40·K·(∫₀^D √log 𝒩)` as real numbers. The
supremum is a.e. finite and a.e. measurable under `hsep`, so the Bochner
integral is honest. -/
theorem dudley_inequality_abs_separable_real {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite entropy integral (real-display junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * (dudleyLIntegral T D).toReal := by
  classical
  obtain ⟨T₀, hT₀T, hT₀cnt, hae⟩ := hsep
  have hCT : insert t₀ T₀ ⊆ T := Set.insert_subset_iff.mpr ⟨ht₀, hT₀T⟩
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  have hBtop : ENNReal.ofReal 40 * (K : ℝ≥0∞) * dudleyLIntegral T D ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) hDL
  -- Transport the REAL supremum to the countable carrier (pointwise in `ω`).
  have hcong : ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      = ∫ ω, ⨆ t ∈ insert t₀ T₀, |X t ω - X t₀ ω| ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    exact biSup_real_comp_eq_of_forall_mem_closure (x := fun t => X t ω)
      (φ := fun v => |v - X t₀ ω|) hCT
      (fun t ht => closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t ht))
      (continuous_abs.comp (continuous_id.sub continuous_const))
      (fun _ => abs_nonneg _)
  have hreal : ∫ ω, ⨆ t ∈ insert t₀ T₀, |X t ω - X t₀ ω| ∂μ
      ≤ (ENNReal.ofReal 40 * (K : ℝ≥0∞) * dudleyLIntegral T D).toReal :=
    integral_biSup_le_of_lintegral_biSup_le hCcnt
      (fun t ht => ((hmeas t (hCT ht)).sub (hmeas t₀ ht₀)).abs)
      (fun _ _ _ => abs_nonneg _)
      (dudley_inequality_abs_countable_subset hcov hne hmeas hinc ht₀ hD hD0
        hCT hCcnt) hBtop
  rw [hcong]
  refine hreal.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 40), ENNReal.coe_toReal]

/-- **Dudley's inequality, absolute form, countable supremum, real display**
(HDP §8.1, Eq. (8.13)): the countable-`T` real display under the
finite-entropy junk-guard. -/
theorem dudley_inequality_abs_countable_real {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite entropy integral (real-display junk-guard)
    {D : ℝ} (hDL : dudleyLIntegral T D ≠ ⊤)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * (dudleyLIntegral T D).toReal := by
  classical
  have hBtop : ENNReal.ofReal 40 * (K : ℝ≥0∞) * dudleyLIntegral T D ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top) hDL
  have hreal : ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ (ENNReal.ofReal 40 * (K : ℝ≥0∞) * dudleyLIntegral T D).toReal :=
    integral_biSup_le_of_lintegral_biSup_le hcnt
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
      (fun _ _ _ => abs_nonneg _)
      (dudley_inequality_abs_countable hcnt hcov hne hmeas hinc ht₀ hD hD0) hBtop
  refine hreal.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 40), ENNReal.coe_toReal]

/-- **Theorem 8.1.3, `∫₀^∞` display, separable supremum** (HDP §8.1): the
uncapped entropy integral form of the anchored mean-zero separable
supremum. The cap `D := diam T + 1` is instantiated internally (a divergent
integral makes the RHS an honest `⊤`). -/
theorem dudley_inequality_anchored_separable_Ioi {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K
          * ∫⁻ ε in Set.Ioi (0 : ℝ), ENNReal.ofReal (sqrtLogCov T ε) := by
  have hDpos : (0 : ℝ) < Metric.diam T + 1 := by
    have := Metric.diam_nonneg (s := T); linarith
  have hDle : Metric.diam T ≤ Metric.diam T + 1 := by linarith
  rw [dudleyLIntegral_Ioi_eq hcov hne hDle hDpos]
  exact dudley_inequality_anchored_separable hcov hne hmeas hint hmean hinc hsep
    ht₀ hDle hDpos

/-- **Dudley's inequality, pair form, countable-subset supremum core**
(HDP §8.1, Eq. (8.14)): the two-sided oscillation over a countable `C ⊆ T`,
`∫⁻ sup_{t,s∈C} |X_t − X_s| ≤ 80·K·∫₀^D √log 𝒩(T)`. Constant `80 = 2 × 40`
by the triangle inequality through an anchor. -/
theorem dudley_inequality_abs_pair_countable_subset {X : E → Ω → ℝ}
    {K : ℝ≥0} {T : Set E}
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
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ⨆ s ∈ C, ENNReal.ofReal |X t ω - X s ω| ∂μ
      ≤ ENNReal.ofReal 80 * K * dudleyLIntegral T D := by
  classical
  -- Route the oscillation through an anchor by the triangle inequality.
  have ht₀ : hne.some ∈ T := hne.some_mem
  set t₀ := hne.some with ht₀def
  have hpt : ∀ ω, (⨆ t ∈ C, ⨆ s ∈ C, ENNReal.ofReal |X t ω - X s ω|)
      ≤ (⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω|)
        + ⨆ s ∈ C, ENNReal.ofReal |X s ω - X t₀ ω| := by
    intro ω
    refine iSup₂_le fun t ht => iSup₂_le fun s hs => ?_
    have htri : |X t ω - X s ω| ≤ |X t ω - X t₀ ω| + |X s ω - X t₀ ω| := by
      have h := abs_sub_le (X t ω) (X t₀ ω) (X s ω)
      rwa [abs_sub_comm (X t₀ ω) (X s ω)] at h
    calc ENNReal.ofReal |X t ω - X s ω|
        ≤ ENNReal.ofReal (|X t ω - X t₀ ω| + |X s ω - X t₀ ω|) :=
          ENNReal.ofReal_le_ofReal htri
      _ ≤ ENNReal.ofReal |X t ω - X t₀ ω| + ENNReal.ofReal |X s ω - X t₀ ω| :=
          ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add
          (le_biSup (fun t => ENNReal.ofReal |X t ω - X t₀ ω|) ht)
          (le_biSup (fun s => ENNReal.ofReal |X s ω - X t₀ ω|) hs)
  have hlegmeas : AEMeasurable
      (fun ω => ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω|) μ :=
    AEMeasurable.biSup C hCcnt
      fun t ht => ((hmeas t (hC ht)).sub (hmeas t₀ ht₀)).abs.ennreal_ofReal
  have hleg : ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D :=
    dudley_inequality_abs_countable_subset hcov hne hmeas hinc ht₀ hD hD0 hC hCcnt
  calc ∫⁻ ω, ⨆ t ∈ C, ⨆ s ∈ C, ENNReal.ofReal |X t ω - X s ω| ∂μ
      ≤ ∫⁻ ω, ((⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω|)
          + ⨆ s ∈ C, ENNReal.ofReal |X s ω - X t₀ ω|) ∂μ := lintegral_mono hpt
    _ = (∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ)
          + ∫⁻ ω, ⨆ s ∈ C, ENNReal.ofReal |X s ω - X t₀ ω| ∂μ :=
        lintegral_add_left' hlegmeas _
    _ ≤ (ENNReal.ofReal 40 * K * dudleyLIntegral T D)
          + ENNReal.ofReal 40 * K * dudleyLIntegral T D := add_le_add hleg hleg
    _ = ENNReal.ofReal 80 * K * dudleyLIntegral T D := by
        rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]; ring

/-- **Dudley's inequality, pair form, separable supremum** (HDP §8.1,
Eq. (8.14), general `T`): `∫⁻ sup_{t,s∈T} |X_t − X_s| ≤ 80·K·∫₀^D √log 𝒩`
in `ℝ≥0∞` for a separable version of the process. Constant `80` as in
`dudley_inequality_abs_pair`. -/
theorem dudley_inequality_abs_pair_separable {X : E → Ω → ℝ} {K : ℝ≥0}
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
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ⨆ s ∈ T, ENNReal.ofReal |X t ω - X s ω| ∂μ
      ≤ ENNReal.ofReal 80 * K * dudleyLIntegral T D := by
  classical
  obtain ⟨T₀, hT₀T, hT₀cnt, hae⟩ := hsep
  -- No anchor in the statement: the countable witness itself is the carrier.
  have hcong : ∫⁻ ω, ⨆ t ∈ T, ⨆ s ∈ T, ENNReal.ofReal |X t ω - X s ω| ∂μ
      = ∫⁻ ω, ⨆ t ∈ T₀, ⨆ s ∈ T₀, ENNReal.ofReal |X t ω - X s ω| ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    exact biSup_pair_ennreal_comp_eq_of_forall_mem_closure (x := fun t => X t ω)
      (φ := fun v w => ENNReal.ofReal |v - w|) hT₀T hω
      (fun w => (ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_id.sub continuous_const))).lowerSemicontinuous)
      (fun v => (ENNReal.continuous_ofReal.comp
        (continuous_abs.comp (continuous_const.sub continuous_id))).lowerSemicontinuous)
  rw [hcong]
  exact dudley_inequality_abs_pair_countable_subset hcov hne hmeas hinc hD hD0
    hT₀T hT₀cnt

end StatLean.ConcentrationInequalities
