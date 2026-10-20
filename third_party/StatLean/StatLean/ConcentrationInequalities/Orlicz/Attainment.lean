module
public import StatLean.ConcentrationInequalities.Orlicz.Basic
public import StatLean.ConcentrationInequalities.Orlicz.Generators

@[expose] public section

/-!
# Orlicz norm — attainment, definiteness, and the book-form conversions

Limiting behavior of the Luxemburg infimum. The **attainment lemma** is the
book's silent WLOG "if $\|X\|_{\psi_2} \le K$ then $\mathbb{E}\exp(X^2/K^2)
\le 2$": the defining condition holds *at* any upper bound of the norm, not
just strictly above it. **Definiteness** is
$$ \|X\|_\psi = 0 \iff X = 0 \text{ a.e.} $$
The four ψ₂/ψ₁ conversion lemmas translate `subGaussianNorm X μ ≤ K` into the
book-form threshold-2 conditions $\mathbb{E}\exp(X^2/K^2) \le 2$ (resp.
$\mathbb{E}\exp(|X|/K) \le 2$) and back; every bridge (B1–B3 and the ψ₁
analogues) consumes them.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press: Definition 2.6.4 / Eq. (2.18) and Definition
2.8.4 / Eq. (2.25) (the norms), Exercise 2.42 (definiteness), and the silent
normalization step in the proofs of Propositions 2.6.6, 2.8.1 and Lemmas
2.8.5–2.8.6.

**Proof formalization notes.** Mathlib has no packaged Luxemburg-attainment
lemma. The attainment proof runs monotone convergence
(`MeasureTheory.lintegral_iSup_directed`) along `Kₙ = K·(1 + 1/(n+1)) ↓ K`,
each `Kₙ` in the gauge set by upward closure; it needs `MonotoneOn ψ (Ici 0)`
**and** `Continuous ψ` together (a merely left-continuous ψ would break the
sup-identification silently). The ±1 shift between the threshold-1 Luxemburg
condition on `ψ = exp − 1` and the threshold-2 book condition on `exp` is done
*additively* (`ofReal (e^u − 1) + 1 = ofReal (e^u)` pointwise, then
`lintegral_add_right'`) to avoid `ENNReal` truncated subtraction; the
conversions therefore need `[IsProbabilityMeasure μ]` (`∫⁻ 1 ∂μ = μ univ`).
Named-sorry fallback of this work item: `orliczNorm_eq_zero_iff` (the
least-consumed declaration; the attainment lemma and the four conversions
must close since every bridge consumes them).

**Bibliographic comments.** Attainment of the Luxemburg gauge under
continuity is classical Orlicz-space theory (Luxemburg 1955; see also
Rao–Ren, *Theory of Orlicz Spaces*, Dekker 1991, §III); the threshold-2
formulation is Vershynin's.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Attainment** (the book's silent WLOG `‖X‖_{ψ₂} ≤ K ⇒ E exp(X²/K²) ≤ 2`):
the Luxemburg condition holds at any upper bound `K` of the norm. Monotone
convergence along `Kₙ ↓ K` via `lintegral_iSup_directed`. -/
theorem lintegral_le_one_of_orliczNorm_le {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- LEAN-ONLY: continuity of ψ; needed for the sup-identification along Kₙ ↓ K,
    -- satisfied by both generators (Generators.lean), no book scope change
    (hψ_cont : Continuous ψ)
    {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; Mathlib-side regularity for lintegral limits
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP §2.6.1 (the norm bound is at a scale K > 0)
    (hK : 0 < K)
    -- USER-INPUT: norm bound ‖X‖_ψ ≤ K; HDP Prop 2.6.6 / 2.8.1 proofs (WLOG step)
    (h : orliczNorm ψ X μ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K : ℝ))) ∂μ ≤ 1 := by
  set kr : ℝ := (K : ℝ) with hkr
  have hkr0 : 0 < kr := by rw [hkr]; exact NNReal.coe_pos.mpr hK
  have hkrne : kr ≠ 0 := ne_of_gt hkr0
  -- For each `n`, extract a gauge member `s n` with `K ≤ s n ≤ K·(1 + 1/(n+1))`.
  have hex : ∀ n : ℕ, ∃ s : ℝ≥0, s ∈ orliczSet ψ X μ ∧ kr ≤ (s : ℝ) ∧
      (s : ℝ) ≤ kr * (1 + ((n : ℝ) + 1)⁻¹) := by
    intro n
    set cₙ : ℝ≥0 := K * (1 + ((n : ℕ) + 1 : ℝ≥0)⁻¹) with hcₙ
    have hcoe : (cₙ : ℝ) = kr * (1 + ((n : ℝ) + 1)⁻¹) := by
      rw [hcₙ, hkr]; push_cast; ring
    have hd : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    have hKlt : K < cₙ := by
      rw [← NNReal.coe_lt_coe, hcoe, ← hkr]
      have := mul_pos hkr0 hd
      nlinarith
    have hlt : orliczNorm ψ X μ < (cₙ : ℝ≥0∞) :=
      lt_of_le_of_lt h (by exact_mod_cast hKlt)
    obtain ⟨s, hs_mem, hs_lt⟩ := exists_mem_orliczSet_lt_of_orliczNorm_lt hlt
    have hs_ltc : s < cₙ := by exact_mod_cast hs_lt
    refine ⟨max s K, orliczSet_upward hψ_mono (le_max_left s K) hs_mem, ?_, ?_⟩
    · rw [hkr]; exact_mod_cast le_max_right s K
    · have hmax : max s K ≤ cₙ := max_le (le_of_lt hs_ltc) (le_of_lt hKlt)
      calc ((max s K : ℝ≥0) : ℝ) ≤ (cₙ : ℝ) := by exact_mod_cast hmax
        _ = kr * (1 + ((n : ℝ) + 1)⁻¹) := hcoe
  choose s hs_mem hs_lb hs_ub using hex
  -- The scales `s n` converge to `K` from above.
  have hU : Tendsto (fun n : ℕ => kr * (1 + ((n : ℝ) + 1)⁻¹)) atTop (𝓝 kr) := by
    have h0 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h1 : Tendsto (fun n : ℕ => 1 + ((n : ℝ) + 1)⁻¹) atTop (𝓝 1) := by
      simpa using h0.const_add (1 : ℝ)
    simpa using h1.const_mul kr
  have hs_tend : Tendsto (fun n : ℕ => (s n : ℝ)) atTop (𝓝 kr) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU hs_lb hs_ub
  -- Pointwise convergence of the integrands, by continuity of `ψ`.
  have hf_tend : ∀ ω, Tendsto (fun n : ℕ => ENNReal.ofReal (ψ (|X ω| / (s n : ℝ)))) atTop
      (𝓝 (ENNReal.ofReal (ψ (|X ω| / kr)))) := by
    intro ω
    have hdiv : Tendsto (fun n : ℕ => |X ω| / (s n : ℝ)) atTop (𝓝 (|X ω| / kr)) :=
      (tendsto_const_nhds).div hs_tend hkrne
    exact (ENNReal.continuous_ofReal.tendsto _).comp ((hψ_cont.tendsto _).comp hdiv)
  -- Measurability of each integrand.
  have hf_meas : ∀ n : ℕ, AEMeasurable
      (fun ω => ENNReal.ofReal (ψ (|X ω| / (s n : ℝ)))) μ := by
    intro n
    have haX : AEMeasurable (fun ω => |X ω|) μ := continuous_abs.measurable.comp_aemeasurable hX
    exact (hψ_cont.measurable.comp_aemeasurable (haX.div_const _)).ennreal_ofReal
  -- Each integral is `≤ 1` by gauge membership.
  have hf_le : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (s n : ℝ))) ∂μ ≤ 1 :=
    fun n => (hs_mem n).2
  -- Fatou.
  calc ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / kr)) ∂μ
      = ∫⁻ ω, liminf (fun n : ℕ => ENNReal.ofReal (ψ (|X ω| / (s n : ℝ)))) atTop ∂μ := by
        refine lintegral_congr (fun ω => ?_)
        exact ((hf_tend ω).liminf_eq).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (s n : ℝ))) ∂μ) atTop :=
        lintegral_liminf_le' hf_meas
    _ ≤ liminf (fun _ : ℕ => (1 : ℝ≥0∞)) atTop :=
        liminf_le_liminf (Eventually.of_forall hf_le)
    _ = 1 := liminf_const 1

/-- **Definiteness** (HDP Exercise 2.42): the Orlicz norm vanishes iff
`X = 0` a.e.; forward direction via Markov at each ε and `K ↓ 0`. -/
theorem orliczNorm_eq_zero_iff {ψ : ℝ → ℝ}
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ_mono : MonotoneOn ψ (Set.Ici 0))
    -- USER-INPUT: ψ(0) ≤ 0 (book: ψ(0) = 0); HDP Exercise 2.42 (Orlicz function)
    (hψ0 : ψ 0 ≤ 0)
    -- USER-INPUT: ψ → ∞ at ∞; HDP Exercise 2.42 (Orlicz function, definiteness)
    (hψ_top : Filter.Tendsto ψ Filter.atTop Filter.atTop)
    {X : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; Markov-argument regularity, no book scope
    (hX : AEMeasurable X μ) :
    orliczNorm ψ X μ = 0 ↔ X =ᵐ[μ] 0 := by
  -- Monotone extension of `ψ` to all of `ℝ` (equal to `ψ` on `[0,∞)`), used only
  -- to get measurability of the integrand from `MonotoneOn`.
  set ψ' : ℝ → ℝ := fun x => ψ (max x 0) with hψ'
  have hψ'_mono : Monotone ψ' := by
    intro a b hab
    exact hψ_mono (le_max_right a 0) (le_max_right b 0) (max_le_max hab le_rfl)
  have hψ'_meas : Measurable ψ' := hψ'_mono.measurable
  have haX : AEMeasurable (fun ω => |X ω|) μ := continuous_abs.measurable.comp_aemeasurable hX
  constructor
  · intro h0
    -- Every level set `{t ≤ |X|}` is null.
    have hAt : ∀ t : ℝ, 0 < t → μ {ω | t ≤ |X ω|} = 0 := by
      intro t ht
      by_contra hm
      have hbound : ∀ N : ℕ, (N : ℝ≥0∞) * μ {ω | t ≤ |X ω|} ≤ 1 := by
        intro N
        obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (hψ_top.eventually_ge_atTop (N : ℝ))
        have hmaxT : T ≤ max T 1 := le_max_left _ _
        have hmaxpos : (0 : ℝ) < max T 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
        have hδpos : (0 : ℝ) < t / max T 1 := by positivity
        have hlt0 : orliczNorm ψ X μ < ENNReal.ofReal (t / max T 1) := by
          rw [h0]; exact ENNReal.ofReal_pos.mpr hδpos
        obtain ⟨K, hK_mem, hK_lt⟩ := exists_mem_orliczSet_lt_of_orliczNorm_lt hlt0
        have hKpos' : (0 : ℝ) < (K : ℝ) := NNReal.coe_pos.mpr hK_mem.1
        have hKδ : (K : ℝ) < t / max T 1 := by
          rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff hδpos] at hK_lt
          exact hK_lt
        have hKM : (K : ℝ) * max T 1 < t := by
          have := mul_lt_mul_of_pos_right hKδ hmaxpos
          rwa [div_mul_cancel₀ t (ne_of_gt hmaxpos)] at this
        have hxT : T ≤ t / (K : ℝ) := by
          rw [le_div_iff₀ hKpos']
          nlinarith [mul_le_mul_of_nonneg_right hmaxT (le_of_lt hKpos')]
        have hψx : (N : ℝ) ≤ ψ (t / (K : ℝ)) := hT _ hxT
        -- Markov's inequality for the integrand at scale `K`.
        set ε : ℝ≥0∞ := ENNReal.ofReal (ψ (t / (K : ℝ))) with hε
        have heq : ∀ ω, ψ' (|X ω| / (K : ℝ)) = ψ (|X ω| / (K : ℝ)) := by
          intro ω
          change ψ (max (|X ω| / (K : ℝ)) 0) = ψ (|X ω| / (K : ℝ))
          rw [max_eq_left (by positivity)]
        have hf_meas : AEMeasurable (fun ω => ENNReal.ofReal (ψ (|X ω| / (K : ℝ)))) μ := by
          have hfun : (fun ω => ENNReal.ofReal (ψ (|X ω| / (K : ℝ))))
              = fun ω => ENNReal.ofReal (ψ' (|X ω| / (K : ℝ))) := by
            funext ω; rw [heq ω]
          rw [hfun]
          exact (hψ'_meas.comp_aemeasurable (haX.div_const _)).ennreal_ofReal
        have hsub : {ω | t ≤ |X ω|} ⊆ {ω | ε ≤ ENNReal.ofReal (ψ (|X ω| / (K : ℝ)))} := by
          intro ω hω
          have hle : t / (K : ℝ) ≤ |X ω| / (K : ℝ) :=
            (div_le_div_iff_of_pos_right hKpos').mpr hω
          have : ψ (t / (K : ℝ)) ≤ ψ (|X ω| / (K : ℝ)) :=
            hψ_mono (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by positivity)) hle
          exact ENNReal.ofReal_le_ofReal this
        have hNε : (N : ℝ≥0∞) ≤ ε := by
          rw [hε, ← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal hψx
        calc (N : ℝ≥0∞) * μ {ω | t ≤ |X ω|}
            ≤ ε * μ {ω | t ≤ |X ω|} := by gcongr
          _ ≤ ε * μ {ω | ε ≤ ENNReal.ofReal (ψ (|X ω| / (K : ℝ)))} := by
              gcongr
          _ ≤ ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K : ℝ))) ∂μ :=
              mul_meas_ge_le_lintegral₀ hf_meas ε
          _ ≤ 1 := hK_mem.2
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hm ENNReal.one_ne_top
      exact absurd (hbound N) (not_le.mpr hN)
    -- Cover `{X ≠ 0}` by the level sets `{1/(m+1) ≤ |X|}`.
    have hsubset : {ω | X ω ≠ 0} ⊆ ⋃ m : ℕ, {ω | (1 : ℝ) / (m + 1) ≤ |X ω|} := by
      intro ω hω
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hω)
      exact Set.mem_iUnion.mpr ⟨m, le_of_lt hm⟩
    have hnull : μ (⋃ m : ℕ, {ω | (1 : ℝ) / (m + 1) ≤ |X ω|}) = 0 := by
      rw [measure_iUnion_null_iff]
      exact fun m => hAt _ (by positivity)
    rw [Filter.EventuallyEq, ae_iff]
    simp only [Pi.zero_apply]
    exact measure_mono_null hsubset hnull
  · intro h
    rw [orliczNorm_congr_ae h]
    exact orliczNorm_zero hψ0 μ

/-- `‖X‖_{ψ₂} ≤ K` unfolded to the book form `E exp(X²/K²) ≤ 2`
(HDP Definition 2.6.4). -/
theorem lintegral_exp_sq_le_two_of_subGaussianNorm_le
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; attainment-lemma regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.6.4
    (hK : 0 < K)
    -- USER-INPUT: sub-Gaussian norm bound ‖X‖_{ψ₂} ≤ K; HDP Definition 2.6.4
    (h : subGaussianNorm X μ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2 := by
  have key := lintegral_le_one_of_orliczNorm_le psiTwo_monotoneOn psiTwo_continuous hX hK
    (by rwa [subGaussianNorm_def] at h)
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2))
      = ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) + 1 := by
    intro ω
    have hsq : (|X ω| / (K : ℝ)) ^ 2 = (X ω / (K : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
    have he : (0 : ℝ) ≤ Real.exp ((X ω / (K : ℝ)) ^ 2) - 1 := by
      have := Real.add_one_le_exp ((X ω / (K : ℝ)) ^ 2)
      nlinarith [sq_nonneg (X ω / (K : ℝ))]
    rw [psiTwo_apply, hsq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add he zero_le_one]
    congr 1; ring
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ
      = ∫⁻ ω, (ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) + 1) ∂μ := lintegral_congr hpt
    _ = (∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) ∂μ) + 1 := by
        rw [lintegral_add_right _ measurable_const, lintegral_one, measure_univ]
    _ ≤ 1 + 1 := add_le_add key le_rfl
    _ = 2 := by norm_num

/-- Reverse conversion: the book form `E exp(X²/K²) ≤ 2` bounds the norm by
`K` (HDP Definition 2.6.4; additive −1 shift, no `ENNReal` tsub). -/
theorem subGaussianNorm_le_of_lintegral_exp_sq_le_two
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.6.4
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(X²/K²) ≤ 2; HDP Definition 2.6.4
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ ≤ 2) :
    subGaussianNorm X μ ≤ (K : ℝ≥0∞) := by
  rw [subGaussianNorm_def]
  apply orliczNorm_le_of_lintegral_le hK
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2))
      = ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) + 1 := by
    intro ω
    have hsq : (|X ω| / (K : ℝ)) ^ 2 = (X ω / (K : ℝ)) ^ 2 := by
      rw [div_pow, div_pow, sq_abs]
    have he : (0 : ℝ) ≤ Real.exp ((X ω / (K : ℝ)) ^ 2) - 1 := by
      have := Real.add_one_le_exp ((X ω / (K : ℝ)) ^ 2)
      nlinarith [sq_nonneg (X ω / (K : ℝ))]
    rw [psiTwo_apply, hsq, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add he zero_le_one]
    congr 1; ring
  have hsum : ∫⁻ ω, ENNReal.ofReal (Real.exp ((X ω / (K : ℝ)) ^ 2)) ∂μ
      = (∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / (K : ℝ))) ∂μ) + 1 := by
    rw [lintegral_congr hpt, lintegral_add_right _ measurable_const, lintegral_one, measure_univ]
  rw [hsum, show (2 : ℝ≥0∞) = 1 + 1 by norm_num] at h
  exact (ENNReal.add_le_add_iff_right (by norm_num)).mp h

/-- `‖X‖_{ψ₁} ≤ K` unfolded to the book form `E exp(|X|/K) ≤ 2`
(HDP Definition 2.8.4). -/
theorem lintegral_exp_abs_le_two_of_subExponentialNorm_le
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability of X; attainment-lemma regularity
    (hX : AEMeasurable X μ)
    {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.8.4
    (hK : 0 < K)
    -- USER-INPUT: sub-exponential norm bound ‖X‖_{ψ₁} ≤ K; HDP Definition 2.8.4
    (h : subExponentialNorm X μ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2 := by
  have key := lintegral_le_one_of_orliczNorm_le (psiOne_monotone.monotoneOn _)
    psiOne_continuous hX hK (by rwa [subExponentialNorm_def] at h)
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ)))
      = ENNReal.ofReal (psiOne (|X ω| / (K : ℝ))) + 1 := by
    intro ω
    have hx0 : (0 : ℝ) ≤ |X ω| / (K : ℝ) := by positivity
    have he : (0 : ℝ) ≤ Real.exp (|X ω| / (K : ℝ)) - 1 := by
      have := Real.add_one_le_exp (|X ω| / (K : ℝ)); linarith
    rw [psiOne_apply, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add he zero_le_one]
    congr 1; ring
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ
      = ∫⁻ ω, (ENNReal.ofReal (psiOne (|X ω| / (K : ℝ))) + 1) ∂μ := lintegral_congr hpt
    _ = (∫⁻ ω, ENNReal.ofReal (psiOne (|X ω| / (K : ℝ))) ∂μ) + 1 := by
        rw [lintegral_add_right _ measurable_const, lintegral_one, measure_univ]
    _ ≤ 1 + 1 := add_le_add key le_rfl
    _ = 2 := by norm_num

/-- Reverse conversion: the book form `E exp(|X|/K) ≤ 2` bounds the norm by
`K` (HDP Definition 2.8.4). -/
theorem subExponentialNorm_le_of_lintegral_exp_abs_le_two
    -- LEAN-ONLY: probability measure; the ±1 shift costs one ∫⁻ 1 ∂μ = μ(univ)
    [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {K : ℝ≥0}
    -- USER-INPUT: positive scale; HDP Definition 2.8.4
    (hK : 0 < K)
    -- USER-INPUT: book-form condition E exp(|X|/K) ≤ 2; HDP Definition 2.8.4
    (h : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ ≤ 2) :
    subExponentialNorm X μ ≤ (K : ℝ≥0∞) := by
  rw [subExponentialNorm_def]
  apply orliczNorm_le_of_lintegral_le hK
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ)))
      = ENNReal.ofReal (psiOne (|X ω| / (K : ℝ))) + 1 := by
    intro ω
    have hx0 : (0 : ℝ) ≤ |X ω| / (K : ℝ) := by positivity
    have he : (0 : ℝ) ≤ Real.exp (|X ω| / (K : ℝ)) - 1 := by
      have := Real.add_one_le_exp (|X ω| / (K : ℝ)); linarith
    rw [psiOne_apply, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add he zero_le_one]
    congr 1; ring
  have hsum : ∫⁻ ω, ENNReal.ofReal (Real.exp (|X ω| / (K : ℝ))) ∂μ
      = (∫⁻ ω, ENNReal.ofReal (psiOne (|X ω| / (K : ℝ))) ∂μ) + 1 := by
    rw [lintegral_congr hpt, lintegral_add_right _ measurable_const, lintegral_one, measure_univ]
  rw [hsum, show (2 : ℝ≥0∞) = 1 + 1 by norm_num] at h
  exact (ENNReal.add_le_add_iff_right (by norm_num)).mp h

end StatLean.ConcentrationInequalities
