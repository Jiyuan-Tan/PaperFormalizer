module
public import StatLean.ConcentrationInequalities.Chaining.GenericChaining
public import StatLean.ConcentrationInequalities.Chaining.CountableSupLift
public import StatLean.ConcentrationInequalities.Chaining.SeparableProcess

@[expose] public section

/-!
# Generic chaining with a genuine supremum over the index set

Honest `sup_{t ∈ T}` forms of the generic chaining bound (HDP Theorem 8.5.2
via the Remark 8.5.3 anchoring) over an arbitrary — possibly uncountable —
metric-space index set: countable-subset cores against `gammaFunctional A`
and `gammaTwo T`, tail forms on the junk-free existential event and the
formal supremum, separable-supremum expectation forms (absolute and
anchored), and the real display under the `γ₂ ≠ ⊤` junk-guard. As in the
per-finite-subset family, NO covering package appears anywhere: admissible
sequences carry all the geometry and `gammaTwo` is an honest `ℝ≥0∞`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.2, Theorem 8.5.2, Remark 8.5.3, Eq. (8.50);
the uncountable forms realize the p. 227 / p. 249 footnotes ("assuming T is
finite to avoid measurability issues; the general case typically follows by
approximation") through separable versions.

**Proof formalization notes.** Frozen constants unchanged: `20` for the
expectation forms, `(12 + 4u)` for the tail. The anchored separable form
`generic_chaining_separable` carries NO mean-zero/integrability hypotheses
(Lean-side strengthening: the anchored carrier is dominated by the absolute
one at the same constant; under `hmean` its LHS dominates every
Remark-7.2.1 finite maximum of `X` itself — see `generic_chaining`). The
countable-subset integrability plumbing has no covering package to bound
increments with; it branches on `K = 0` and `gammaFunctional A = ⊤` and
otherwise bounds `dist t t₀` through the level-0 singleton
(`ofReal_infDist_zero_le_gammaFunctional`). Named-sorry fallback of this
work item: `generic_chaining_of_admissible_countable_subset` (that
integrability plumbing).

**Bibliographic comments.** M. Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, Springer 2014, §2.2–2.3 (the majorizing-measure
γ₂ theory); separable versions per van Handel, *Probability in High
Dimension*, §5.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Generic chaining along an admissible sequence, countable-subset
supremum core** (HDP §8.5.2): `∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 20·K·γ(A)` in
`ℝ≥0∞` for any countable `C ⊆ T`; the `γ(A) = ⊤` branch is trivial. -/
theorem generic_chaining_of_admissible_countable_subset {X : E → Ω → ℝ}
    {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaFunctional A := by
  classical
  by_cases hK0 : K = 0
  · -- `K = 0`: every increment vanishes a.e., hence so does the countable sup.
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ C, X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff hCcnt]
      intro t ht
      have htT := hC ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t htT
        rw [hK0] at h
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero
        ((hmeas t htT).sub (hmeas t₀ ht₀)) hnorm
    have hae : (fun ω => ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω|)
        =ᵐ[μ] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [hz] with ω hω
      refine le_antisymm (iSup₂_le fun t ht => ?_) (zero_le)
      rw [hω t ht, abs_zero, ENNReal.ofReal_zero]
    calc ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
        = ∫⁻ _, (0 : ℝ≥0∞) ∂μ := lintegral_congr_ae hae
      _ = 0 := lintegral_zero
      _ ≤ 20 * K * gammaFunctional A := zero_le
  · by_cases hγ : gammaFunctional A = ⊤
    · rw [hγ,
        ENNReal.mul_top (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr hK0))]
      exact le_top
    · -- Main case: a uniform ψ₂ bound on the anchored increments, obtained from
      -- the level-0 singleton, feeds the finite-maximum integrability.
      obtain ⟨L, hLbound⟩ : ∃ L : ℝ≥0, ∀ t ∈ T,
          subGaussianNorm (fun ω => X t ω - X t₀ ω) μ ≤ (L : ℝ≥0∞) := by
        obtain ⟨a₀, ha₀⟩ := Finset.card_eq_one.mp A.card_zero
        have hptR : ∀ x ∈ T, dist x a₀ ≤ (gammaFunctional A).toReal := by
          intro x hx
          have h := ofReal_infDist_zero_le_gammaFunctional A hx
          rw [ha₀, Finset.coe_singleton, Metric.infDist_singleton] at h
          have h' := ENNReal.toReal_mono hγ h
          rwa [ENNReal.toReal_ofReal dist_nonneg] at h'
        refine ⟨K * Real.toNNReal (2 * (gammaFunctional A).toReal), fun t ht => ?_⟩
        refine (hinc t₀ ht₀ t ht).trans ?_
        have hd : dist t₀ t ≤ 2 * (gammaFunctional A).toReal := by
          calc dist t₀ t ≤ dist t₀ a₀ + dist a₀ t := dist_triangle _ _ _
            _ = dist t₀ a₀ + dist t a₀ := by rw [dist_comm a₀ t]
            _ ≤ (gammaFunctional A).toReal + (gammaFunctional A).toReal :=
                add_le_add (hptR t₀ ht₀) (hptR t ht)
            _ = 2 * (gammaFunctional A).toReal := by ring
        have hle : edist t₀ t
            ≤ ENNReal.ofReal (2 * (gammaFunctional A).toReal) := by
          rw [edist_dist]; exact ENNReal.ofReal_le_ofReal hd
        calc (K : ℝ≥0∞) * edist t₀ t
            ≤ (K : ℝ≥0∞) * ENNReal.ofReal (2 * (gammaFunctional A).toReal) :=
              by gcongr
          _ = ((K * Real.toNNReal (2 * (gammaFunctional A).toReal) : ℝ≥0) : ℝ≥0∞) := by
              rw [ENNReal.coe_mul]; rfl
      refine lintegral_biSup_le_of_forall_finset
        (g := fun t ω => ENNReal.ofReal |X t ω - X t₀ ω|) hCcnt
        (fun t ht => (((hmeas t (hC ht)).sub (hmeas t₀ ht₀)).abs).ennreal_ofReal) ?_
      intro F hF hFne
      have hFT : (↑F : Set E) ⊆ T := hF.trans hC
      have h0 : ∀ ω, 0 ≤ F.sup' hFne fun t => |X t ω - X t₀ ω| := by
        intro ω
        obtain ⟨a, ha⟩ := hFne
        exact (abs_nonneg _).trans (Finset.le_sup' (fun t => |X t ω - X t₀ ω|) ha)
      have hIntB : MeasureTheory.Integrable
          (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|) μ :=
        integrable_biSup_abs hFne (Y := fun t ω => X t ω - X t₀ ω)
          (fun t ht => (hmeas t (hFT (Finset.mem_coe.mpr ht))).sub (hmeas t₀ ht₀))
          (fun t ht => hLbound t (hFT (Finset.mem_coe.mpr ht)))
      have hInt : MeasureTheory.Integrable
          (fun ω => F.sup' hFne fun t => |X t ω - X t₀ ω|) μ := by
        refine hIntB.congr (Filter.Eventually.of_forall fun ω => ?_)
        exact biSup_finset_eq_sup' hFne (fun t => |X t ω - X t₀ ω|)
          (fun t _ => abs_nonneg _)
      rw [lintegral_biSup_finset_ofReal_eq hFne h0 hInt]
      exact generic_chaining_of_admissible hne hmeas hinc ht₀ A hFT hFne

/-- **Generic chaining, absolute form, countable-subset supremum core**
(HDP §8.5.2, Theorem 8.5.2 via Remark 8.5.3):
`∫⁻ sup_{t∈C} |X_t − X_{t₀}| ≤ 20·K·γ₂(T,d)` in `ℝ≥0∞`, by the infimum
over admissible sequences. -/
theorem generic_chaining_abs_countable_subset {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    ∫⁻ ω, ⨆ t ∈ C, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaTwo T := by
  haveI : Nonempty (AdmissibleSequence T) := nonempty_admissibleSequence hne
  have ha_top : (20 : ℝ≥0∞) * ↑K ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have hpush : (20 : ℝ≥0∞) * ↑K * gammaTwo T
      = ⨅ A : AdmissibleSequence T, 20 * ↑K * gammaFunctional A := by
    rw [show gammaTwo T = ⨅ A : AdmissibleSequence T, gammaFunctional A from rfl]
    exact ENNReal.mul_iInf (fun h => absurd h ha_top)
  rw [hpush]
  exact le_iInf fun A =>
    generic_chaining_of_admissible_countable_subset hne hmeas hinc ht₀ A hC hCcnt

/-- **Generic chaining, tail form, existential countable-subset core**
(HDP §8.5.2, Eq. (8.50)): with probability at least `1 − 2e^{−u²}`, no
member of the countable subfamily `C ⊆ T` has anchored increment exceeding
`(12 + 4u)·K·γ(A)`. The junk-free engine stage of the formal-supremum
displays. -/
theorem generic_chaining_tail_exists {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index so the anchor exists
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment max; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u)
    {C : Set E}
    -- LEAN-ONLY: the countable approximating subfamily (sup policy)
    (hC : C ⊆ T)
    -- LEAN-ONLY: countability of the subfamily (sup policy)
    (hCcnt : C.Countable) :
    μ {ω | ∃ t ∈ C, (12 + 4 * u) * K * (gammaFunctional A).toReal
        < |X t ω - X t₀ ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  refine measure_exists_lt_le_of_forall_finset
    (f := fun t ω => |X t ω - X t₀ ω|) hCcnt ?_
  intro F hFne hF
  exact generic_chaining_tail hne hmeas hinc ht₀ A hA hu (hF.trans hC) hFne

/-- **Generic chaining, tail form, separable supremum** (HDP §8.5.2,
Eq. (8.50), general `T`): for a separable version, the anchored increment
supremum over `T` exceeds `(12 + 4u)·K·γ(A)` with probability at most
`2e^{−u²}`. -/
theorem generic_chaining_tail_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index so the anchor exists
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment max; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal
        < ⨆ t ∈ T, |X t ω - X t₀ ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  obtain ⟨T₀, hT₀sub, hT₀cnt, hclos⟩ := hsep
  have hCsub : insert t₀ T₀ ⊆ T := Set.insert_subset ht₀ hT₀sub
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  have hthr0 : 0 ≤ (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal :=
    mul_nonneg (mul_nonneg (by linarith) K.coe_nonneg) ENNReal.toReal_nonneg
  refine le_trans (measure_mono_ae ?_)
    (generic_chaining_tail_exists hne hmeas hinc ht₀ A hA hu hCsub hCcnt)
  filter_upwards [hclos] with ω hω hmem
  obtain ⟨t, htT, ht⟩ := exists_lt_of_lt_biSup_real hthr0 hmem
  have hcl : X t ω ∈ closure ((fun s => X s ω) '' insert t₀ T₀) :=
    closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t htT)
  obtain ⟨a, haA, hlt'⟩ := exists_lt_comp_of_mem_closure hcl
    (φ := fun v => |v - X t₀ ω|) ((continuous_id.sub continuous_const).abs) ht
  obtain ⟨t', ht'C, rfl⟩ := haA
  exact ⟨t', ht'C, hlt'⟩

/-- **Generic chaining, absolute form, separable supremum** (HDP §8.5.2 via
Remark 8.5.3, general `T`): `∫⁻ sup_{t∈T} |X_t − X_{t₀}| ≤ 20·K·γ₂(T,d)`
in `ℝ≥0∞` for a separable version, NO mean-zero. -/
theorem generic_chaining_abs_separable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaTwo T := by
  obtain ⟨T₀, hT₀sub, hT₀cnt, hclos⟩ := hsep
  have hCsub : insert t₀ T₀ ⊆ T := Set.insert_subset ht₀ hT₀sub
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  have hcong : ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      = ∫⁻ ω, ⨆ t ∈ insert t₀ T₀, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hclos] with ω hω
    exact biSup_ennreal_comp_eq_of_forall_mem_closure hCsub
      (x := fun s => X s ω)
      (fun t ht => closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t ht))
      (φ := fun v => ENNReal.ofReal |v - X t₀ ω|)
      ((ENNReal.continuous_ofReal.comp
        ((continuous_id.sub continuous_const).abs)).lowerSemicontinuous)
  rw [hcong]
  exact generic_chaining_abs_countable_subset hne hmeas hinc ht₀ hCsub hCcnt

/-- **Theorem 8.5.2 (generic chaining bound), separable supremum**
(HDP §8.5.2, general `T`): `∫⁻ sup_{t∈T} (X_t − X_{t₀})⁺ ≤ 20·K·γ₂(T,d)`
in `ℝ≥0∞` for a separable version. Lean-side strengthening: NO
mean-zero/integrability hypotheses — the anchored carrier is dominated by
`generic_chaining_abs_separable` at the SAME frozen constant `20`; under
mean-zero the LHS dominates every Remark-7.2.1 finite maximum of `X` itself
(see `generic_chaining`), so this is the honest sup-form of the book's
`E sup_{t∈T} X_t ≤ C·K·γ₂(T,d)`. -/
theorem generic_chaining_separable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point (Remark 8.5.3 device)
    (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal (X t ω - X t₀ ω) ∂μ
      ≤ 20 * K * gammaTwo T := by
  refine le_trans (lintegral_mono fun ω => ?_)
    (generic_chaining_abs_separable hne hmeas hinc hsep ht₀)
  exact iSup₂_mono fun t _ => ENNReal.ofReal_le_ofReal (le_abs_self _)

/-- **Generic chaining, absolute form, separable supremum, real display**
(HDP §8.5.2): under the `γ₂ ≠ ⊤` junk-guard,
`∫ sup_{t∈T} |X_t − X_{t₀}| ≤ 20·K·(γ₂(T,d)).toReal` as real numbers. -/
theorem generic_chaining_abs_separable_real {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: separable version of the process; HDP p.227 footnote
    -- (van Handel APM §5.3)
    (hsep : IsSeparableProcess X T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite γ₂ so the real RHS is honest (junk-guard)
    (hγ : gammaTwo T ≠ ⊤) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ ≤ 20 * K * (gammaTwo T).toReal := by
  obtain ⟨T₀, hT₀sub, hT₀cnt, hclos⟩ := hsep
  have hCsub : insert t₀ T₀ ⊆ T := Set.insert_subset ht₀ hT₀sub
  have hCcnt : (insert t₀ T₀).Countable := hT₀cnt.insert t₀
  have hB : ∫⁻ ω, ⨆ t ∈ insert t₀ T₀, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaTwo T :=
    generic_chaining_abs_countable_subset hne hmeas hinc ht₀ hCsub hCcnt
  have hBtop : (20 : ℝ≥0∞) * ↑K * gammaTwo T ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hγ
  have hreal : ∫ ω, ⨆ t ∈ insert t₀ T₀, |X t ω - X t₀ ω| ∂μ
      ≤ ((20 : ℝ≥0∞) * ↑K * gammaTwo T).toReal :=
    integral_biSup_le_of_lintegral_biSup_le hCcnt
      (fun t ht => ((hmeas t (hCsub ht)).sub (hmeas t₀ ht₀)).abs)
      (fun _ _ _ => abs_nonneg _) hB hBtop
  have htrans : ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      = ∫ ω, ⨆ t ∈ insert t₀ T₀, |X t ω - X t₀ ω| ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hclos] with ω hω
    exact biSup_real_comp_eq_of_forall_mem_closure hCsub
      (x := fun s => X s ω)
      (fun t ht => closure_mono (Set.image_mono (Set.subset_insert t₀ T₀)) (hω t ht))
      (φ := fun v => |v - X t₀ ω|) ((continuous_id.sub continuous_const).abs)
      (fun _ => abs_nonneg _)
  rw [htrans]
  refine hreal.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal]

/-- **Generic chaining, absolute form, countable supremum** (HDP §8.5.2):
the `C := T` display of the countable-subset core. -/
theorem generic_chaining_abs_countable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * gammaTwo T :=
  generic_chaining_abs_countable_subset hne hmeas hinc ht₀ (Set.Subset.refl T) hcnt

/-- **Generic chaining, tail form, countable supremum** (HDP §8.5.2,
Eq. (8.50)): the `C := T` display of the tail core, on the formal
supremum. -/
theorem generic_chaining_tail_countable {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonempty index so the anchor exists
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment max; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal
        < ⨆ t ∈ T, |X t ω - X t₀ ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  have hthr0 : 0 ≤ (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal :=
    mul_nonneg (mul_nonneg (by linarith) K.coe_nonneg) ENNReal.toReal_nonneg
  refine le_trans (measure_mono ?_)
    (generic_chaining_tail_exists hne hmeas hinc ht₀ A hA hu
      (Set.Subset.refl T) hcnt)
  intro ω hω
  exact exists_lt_of_lt_biSup_real hthr0 hω

/-- **Generic chaining, absolute form, countable supremum, real display**
(HDP §8.5.2): the countable-`T` real display under the `γ₂ ≠ ⊤`
junk-guard. -/
theorem generic_chaining_abs_countable_real {X : E → Ω → ℝ} {K : ℝ≥0}
    {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    -- LEAN-ONLY: finite γ₂ so the real RHS is honest (junk-guard)
    (hγ : gammaTwo T ≠ ⊤) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ ≤ 20 * K * (gammaTwo T).toReal := by
  have hB := generic_chaining_abs_countable hcnt hne hmeas hinc ht₀
  have hBtop : (20 : ℝ≥0∞) * ↑K * gammaTwo T ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hγ
  have hreal : ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ ((20 : ℝ≥0∞) * ↑K * gammaTwo T).toReal :=
    integral_biSup_le_of_lintegral_biSup_le hcnt
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
      (fun _ _ _ => abs_nonneg _) hB hBtop
  refine hreal.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal]

end StatLean.ConcentrationInequalities
