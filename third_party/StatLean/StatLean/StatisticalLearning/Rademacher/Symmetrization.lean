module
public import StatLean.StatisticalLearning.Rademacher.Defs
public import StatLean.StatisticalLearning.Core.SampleLaw
public import StatLean.ConcentrationInequalities.Symmetrization.Empirical

@[expose] public section

/-!
# Symmetrization: representativeness ≤ 2 × expected Rademacher complexity

SSBD Lemma 26.2: `E_{S∼Dⁿ}[Rep_D(𝓕,S)] ≤ 2 E_{S∼Dⁿ}[R(𝓕∘S)]`, where
`Rep_D(𝓕,S) = sup_{f∈𝓕}(L_D(f) − L_S(f))` — the one-sided, non-absolute
ghost-sample symmetrization that powers all of Ch. 26's generalization bounds.

**Reference.** SSBD §26.1, Lemma 26.2 (Eqs. (26.6)–(26.9)). Transcription:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** The project's
`ConcentrationInequalities/Symmetrization/Empirical.lean` proves the
*absolute-value* form; SSBD's constants in Theorem 26.5 need this one-sided
non-absolute form, so it is proved here afresh by the book's argument: ghost
sample `S' ∼ Dⁿ` + Jensen (sup of expectation ≤ expectation of sup), per-
coordinate swap invariance introducing the signs, and the `σ ≍ −σ` split
giving the factor 2. The per-coordinate swap is the project's
`Symmetrization/SignFlip.lean` brick `measurePreserving_condSwap`, applied on
`(sampleLaw D n).prod (sampleLaw D n)` with `ν i = D`. The sign average is
bridged to the `signVec` product measure by `signAvg_eq_integral_signVec`,
proved at the *measure* level: `signVec N = ∑_σ 2⁻ᴺ δ_{signOf σ}`
(`Measure.pi_eq` tested on boxes, the two-atom `radLaw` masses expanding by
`Fintype.prod_sum`), so `integral_dirac` disposes of every measurability side
condition and the identity holds for an arbitrary `g`. Index sets are countable
and sups are `sSup`-of-image with a uniform bound `c`, per the batch sup policy.
-/

open MeasureTheory ProbabilityTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z ι : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {n : ℕ}

/-! ### LEAN-ONLY: the finitely-atomic description of `signVec` -/

/-- Product-of-indicators reading of the indicator of a measurable box
(LEAN-ONLY bookkeeping for `signVec_eq_sum_dirac`). -/
private theorem indicator_univ_pi {N : ℕ} (t : Fin N → Set ℝ) (x : Fin N → ℝ) :
    (Set.univ.pi t).indicator (1 : (Fin N → ℝ) → ℝ≥0∞) x
      = ∏ i, (t i).indicator (1 : ℝ → ℝ≥0∞) (x i) := by
  classical
  simp only [Set.indicator_apply, Pi.one_apply, Set.mem_univ_pi]
  rw [Finset.prod_boole]
  simp

/-- `radLaw` of a set, expanded as a two-term `Bool`-sum (LEAN-ONLY). -/
private theorem radLaw_apply_eq_sum_bool (t : Set ℝ) :
    radLaw t = ∑ b : Bool, (2 : ℝ≥0∞)⁻¹ * t.indicator 1 (if b then (1 : ℝ) else -1) := by
  rw [Fintype.sum_bool, radLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply, Measure.dirac_apply, smul_eq_mul, smul_eq_mul]
  simp

/-- **The sign vector is the uniform law on the `2ⁿ` sign atoms** (LEAN-ONLY):
`signVec N = ∑_σ 2⁻ᴺ δ_{signOf σ}`. Proved by testing on measurable boxes
(`Measure.pi_eq`): the product of the two-atom `radLaw` masses expands into the
sum over sign patterns (`Fintype.prod_sum`). -/
private theorem signVec_eq_sum_dirac (N : ℕ) :
    signVec N = Measure.sum
      (fun σ : Fin N → Bool => (2 ^ N : ℝ≥0∞)⁻¹ • Measure.dirac (signOf σ)) := by
  classical
  rw [Measure.sum_fintype]
  refine Measure.pi_eq ?_
  intro t _
  rw [Measure.finset_sum_apply]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => radLaw_apply_eq_sum_bool (t i)),
    Fintype.prod_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, indicator_univ_pi,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.inv_pow]
  rfl

/-- Bridge between the finite sign average and the `signVec` product law
(LEAN-ONLY): `signAvg n g = ∫ ε, g ε ∂(signVec n)` for every `g` — the law
`signVec n` is supported on the `2ⁿ` sign atoms with equal mass, so every
function is a.e.-strongly measurable and the integral is the finite average. -/
theorem signAvg_eq_integral_signVec (g : (Fin n → ℝ) → ℝ) :
    signAvg n g = ∫ ε, g ε ∂(signVec n) := by
  classical
  rw [signVec_eq_sum_dirac,
    integral_sum_measure (integrable_sum_dirac (fun _ => by simp) Summable.of_finite),
    tsum_fintype]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [signAvg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  simp [ENNReal.toReal_inv]

/-! ### LEAN-ONLY toolkit: countable `sSup`-of-image, sign sums, bounded integrands -/

/-- The `sSup`-of-image spelling as an `iSup` over the subtype — the bridge to
Mathlib's countable-`iSup` measurability lemma. -/
private lemma sSup_image_eq_iSup (f : ι → ℝ) (K : Set ι) :
    sSup (f '' K) = ⨆ k : K, f k := by
  rw [Set.image_eq_range]
  rfl

/-- A uniform upper bound on the family bounds the image above. -/
private lemma bddAbove_image {f : ι → ℝ} {K : Set ι} {M : ℝ} (h : ∀ k ∈ K, f k ≤ M) :
    BddAbove (f '' K) := ⟨M, by rintro y ⟨k, hk, rfl⟩; exact h k hk⟩

/-- `csSup_le` in `sSup`-of-image form. -/
private lemma sSup_image_le {f : ι → ℝ} {K : Set ι} {M : ℝ} (hne : K.Nonempty)
    (h : ∀ k ∈ K, f k ≤ M) : sSup (f '' K) ≤ M :=
  csSup_le (hne.image f) (by rintro y ⟨k, hk, rfl⟩; exact h k hk)

/-- `le_csSup` in `sSup`-of-image form, boundedness supplied by a uniform bound. -/
private lemma le_sSup_image {f : ι → ℝ} {K : Set ι} {M : ℝ} {k : ι} (hk : k ∈ K)
    (hb : ∀ j ∈ K, f j ≤ M) : f k ≤ sSup (f '' K) :=
  le_csSup (bddAbove_image hb) ⟨k, hk, rfl⟩

/-- A uniform two-sided bound on the family transfers to the sup (one witness in
`K` supplies the lower bound). -/
private lemma abs_sSup_image_le {f : ι → ℝ} {K : Set ι} {M : ℝ} {k₀ : ι} (hk₀ : k₀ ∈ K)
    (h : ∀ k ∈ K, |f k| ≤ M) : |sSup (f '' K)| ≤ M := by
  have hub : ∀ k ∈ K, f k ≤ M := fun k hk => (abs_le.1 (h k hk)).2
  refine abs_le.2 ⟨?_, sSup_image_le ⟨k₀, hk₀⟩ hub⟩
  exact ((abs_le.1 (h k₀ hk₀)).1).trans (le_sSup_image hk₀ hub)

/-- Rademacher signs have modulus one. -/
private lemma abs_signOf {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : |signOf σ i| = 1 := by
  rcases h : σ i <;> simp [signOf, h]

/-- A sign-weighted sum of `n` terms of modulus `≤ M` has modulus `≤ n M`. -/
private lemma abs_sum_signOf_le {n : ℕ} (σ : Fin n → Bool) (g : Fin n → ℝ) {M : ℝ}
    (h : ∀ i, |g i| ≤ M) : |∑ i, signOf σ i * g i| ≤ n * M := by
  calc |∑ i, signOf σ i * g i| ≤ ∑ i, |signOf σ i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_signOf, one_mul]; exact h i
    _ = n * M := by simp [mul_comm]

/-- Reindexing a sign-pattern sum by the global flip `σ ↦ ¬σ` (an involution). -/
private lemma sum_bool_flip {n : ℕ} (g : (Fin n → Bool) → ℝ) :
    ∑ σ : Fin n → Bool, g (fun i => !(σ i)) = ∑ σ : Fin n → Bool, g σ :=
  Fintype.sum_bijective (fun σ i => !(σ i))
    (Function.Involutive.bijective fun σ => funext fun i => Bool.not_not (σ i)) _ _ fun _ => rfl

/-- A countable `sSup`-of-image of measurable functions is measurable. -/
private lemma measurable_sSup_image {X : Type*} [MeasurableSpace X] {K : Set ι}
    (hKc : K.Countable) {g : ι → X → ℝ} (hg : ∀ k, Measurable (g k)) :
    Measurable fun x => sSup ((fun k => g k x) '' K) := by
  haveI := hKc.to_subtype
  have h : (fun x => sSup ((fun k => g k x) '' K)) = fun x => ⨆ k : K, g k x := by
    funext x; exact sSup_image_eq_iSup _ _
  rw [h]
  exact Measurable.iSup fun k => hg k

/-- A bounded measurable function is integrable against a finite measure. -/
private lemma integrable_of_abs_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] {f : X → ℝ} (hm : Measurable f) {M : ℝ} (h : ∀ x, |f x| ≤ M) :
    Integrable f ν :=
  (integrable_const M).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using h x)

/-- **SSBD Lemma 26.2** (one-sided symmetrization, countable family): for a
countable index type and a uniformly bounded measurable family `F`,
`E_{S∼Dⁿ} sup_{k∈K} (L_D(F k) − L_S(F k)) ≤ 2 E_{S∼Dⁿ} R(F ∘ S)`. -/
theorem integral_sup_risk_sub_empRisk_le_two_mul_integral_empRad
    (F : ι → Z → ℝ) (K : Set ι) {c : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    -- USER-INPUT: nonempty family; SSBD §26.1 (implicit)
    (hK : K.Nonempty)
    -- USER-INPUT: measurability of the family; SSBD Remark 3.1
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniform bound `|f| ≤ c` on the family; SSBD Thm 26.5
    -- setting (supplies integrability of the sups)
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: at least one example; SSBD §26.1 (implicit)
    (hn : 1 ≤ n) :
    ∫ s, sSup ((fun k => risk D F k - empRisk F s k) '' K)
        ∂(sampleLaw D n) ≤
      2 * ∫ s, empRad F K s ∂(sampleLaw D n) := by
  classical
  obtain ⟨k₀, hk₀⟩ := hK
  -- `Z` is nonempty because `D` is a probability measure.
  have hZ : Nonempty Z := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 : D Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨z₀⟩ := hZ
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hbdd k₀ hk₀ z₀)
  have hnpos : 0 < n := hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  -- basic bounds
  have hIcc : ∀ k ∈ K, ∀ z, F k z ∈ Set.Icc (-c) c := fun k hk z => abs_le.1 (hbdd k hk z)
  have hFint : ∀ k ∈ K, Integrable (F k) D := fun k hk =>
    integrable_of_abs_le (hmeas k) (hbdd k hk)
  have hempmeas : ∀ k, Measurable fun s : Sample Z n => empRisk F s k := fun k =>
    measurable_empRisk (hmeas k)
  have hemp : ∀ k ∈ K, ∀ s : Sample Z n, |empRisk F s k| ≤ c := fun k hk s =>
    abs_le.2 (Set.mem_Icc.1 (empRisk_mem_Icc (hIcc k hk) hn s))
  have hrisk : ∀ k ∈ K, |risk D F k| ≤ c := fun k hk =>
    abs_le.2 (Set.mem_Icc.1 (risk_mem_Icc (hIcc k hk) (hmeas k)))
  set μ : Measure (Sample Z n) := sampleLaw D n with hμdef
  -- ### the three integrands
  -- `G s = sup_k (L_D k - L_s k)`
  have hGmeas : Measurable fun s : Sample Z n =>
      sSup ((fun k => risk D F k - empRisk F s k) '' K) :=
    measurable_sSup_image hKc fun k => measurable_const.sub (hempmeas k)
  have hGbdd : ∀ s : Sample Z n,
      |sSup ((fun k => risk D F k - empRisk F s k) '' K)| ≤ 2 * c := by
    intro s
    have hub : ∀ k ∈ K, risk D F k - empRisk F s k ≤ 2 * c := by
      intro k hk
      have h1 := abs_le.1 (hrisk k hk)
      have h2 := abs_le.1 (hemp k hk s)
      linarith [h1.2, h2.1]
    refine abs_le.2 ⟨?_, sSup_image_le ⟨k₀, hk₀⟩ hub⟩
    have h1 := abs_le.1 (hrisk k₀ hk₀)
    have h2 := abs_le.1 (hemp k₀ hk₀ s)
    have : -(2 * c) ≤ risk D F k₀ - empRisk F s k₀ := by linarith [h1.1, h2.2]
    exact this.trans (le_sSup_image hk₀ hub)
  have hGint : Integrable (fun s : Sample Z n =>
      sSup ((fun k => risk D F k - empRisk F s k) '' K)) μ :=
    integrable_of_abs_le hGmeas hGbdd
  -- `H w = sup_k (L_{w.2} k - L_{w.1} k)`
  have hHmeas : Measurable fun w : Sample Z n × Sample Z n =>
      sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K) :=
    measurable_sSup_image hKc fun k =>
      ((hempmeas k).comp measurable_snd).sub ((hempmeas k).comp measurable_fst)
  have hHbdd : ∀ w : Sample Z n × Sample Z n,
      |sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K)| ≤ 2 * c := by
    intro w
    have hub : ∀ k ∈ K, empRisk F w.2 k - empRisk F w.1 k ≤ 2 * c := by
      intro k hk
      have h1 := abs_le.1 (hemp k hk w.2)
      have h2 := abs_le.1 (hemp k hk w.1)
      linarith [h1.2, h2.1]
    refine abs_le.2 ⟨?_, sSup_image_le ⟨k₀, hk₀⟩ hub⟩
    have h1 := abs_le.1 (hemp k₀ hk₀ w.2)
    have h2 := abs_le.1 (hemp k₀ hk₀ w.1)
    have : -(2 * c) ≤ empRisk F w.2 k₀ - empRisk F w.1 k₀ := by linarith [h1.1, h2.2]
    exact this.trans (le_sSup_image hk₀ hub)
  have hHint : Integrable (fun w : Sample Z n × Sample Z n =>
      sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K)) (μ.prod μ) :=
    integrable_of_abs_le hHmeas hHbdd
  -- ### Step A: Jensen / sup of expectation ≤ expectation of sup
  have hstepA : ∀ s : Sample Z n,
      sSup ((fun k => risk D F k - empRisk F s k) '' K) ≤
        ∫ s', sSup ((fun k => empRisk F s' k - empRisk F s k) '' K) ∂μ := by
    intro s
    refine csSup_le (Set.Nonempty.image _ ⟨k₀, hk₀⟩) ?_
    rintro y ⟨k, hk, rfl⟩
    have hub : ∀ (s' : Sample Z n), ∀ j ∈ K, empRisk F s' j - empRisk F s j ≤ 2 * c := by
      intro s' j hj
      have h1 := abs_le.1 (hemp j hj s')
      have h2 := abs_le.1 (hemp j hj s)
      linarith [h1.2, h2.1]
    have hint1 : Integrable (fun s' : Sample Z n => empRisk F s' k - empRisk F s k) μ :=
      integrable_of_abs_le (M := 2 * c) ((hempmeas k).sub measurable_const) (fun s' => by
        have h1 := abs_le.1 (hemp k hk s')
        have h2 := abs_le.1 (hemp k hk s)
        exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩)
    have hint2 : Integrable (fun s' : Sample Z n =>
        sSup ((fun j => empRisk F s' j - empRisk F s j) '' K)) μ :=
      integrable_of_abs_le
        (measurable_sSup_image hKc fun j => (hempmeas j).sub measurable_const)
        (fun s' => hHbdd (s, s'))
    have heq : risk D F k - empRisk F s k
        = ∫ s', (empRisk F s' k - empRisk F s k) ∂μ := by
      rw [integral_sub (integrable_of_abs_le (hempmeas k) (hemp k hk)) (integrable_const _),
        hμdef, integral_empRisk (hFint k hk) hn, integral_const]
      simp
    change risk D F k - empRisk F s k ≤
      ∫ s', sSup ((fun j => empRisk F s' j - empRisk F s j) '' K) ∂μ
    rw [heq]
    refine integral_mono hint1 hint2 fun s' => ?_
    exact le_sSup_image hk (hub s')
  -- ### Step B: to the product measure
  have hstepB : ∫ s, sSup ((fun k => risk D F k - empRisk F s k) '' K) ∂μ ≤
      ∫ w, sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K) ∂(μ.prod μ) := by
    rw [integral_prod _ hHint]
    exact integral_mono hGint hHint.integral_prod_left hstepA
  -- ### Step C: the conditional swap turns the ghost gap into a signed gap
  have hstepC : ∀ σ : Fin n → Bool,
      ∫ w, sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K) ∂(μ.prod μ)
        = ∫ w, sSup ((fun k => (n : ℝ)⁻¹ *
              ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K) ∂(μ.prod μ) := by
    intro σ
    have hT : MeasurePreserving
        (fun w : Sample Z n × Sample Z n =>
          ((fun i => if σ i then w.1 i else w.2 i : Sample Z n),
           (fun i => if σ i then w.2 i else w.1 i : Sample Z n)))
        (μ.prod μ) (μ.prod μ) := measurePreserving_condSwap (fun _ => D) σ
    have hmap : ∫ w, sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K) ∂(μ.prod μ)
        = ∫ w, sSup ((fun k => empRisk F (fun i => if σ i then w.2 i else w.1 i) k
              - empRisk F (fun i => if σ i then w.1 i else w.2 i) k) '' K) ∂(μ.prod μ) := by
      conv_lhs => rw [← hT.map_eq]
      exact integral_map hT.measurable.aemeasurable
        (hT.map_eq.symm ▸ hHmeas.aestronglyMeasurable)
    rw [hmap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    refine congrArg sSup (Set.image_congr' fun k => ?_)
    rw [empRisk, empRisk, ← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rcases hσi : σ i with _ | _ <;> simp [signOf, hσi]
  -- ### the signed sup, and `empRad` in sign-average form
  have hAmeas : ∀ σ : Fin n → Bool, Measurable fun s : Sample Z n =>
      sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K) := fun σ =>
    measurable_sSup_image hKc fun k =>
      Finset.measurable_sum _ fun i _ => ((hmeas k).comp (measurable_pi_apply i)).const_mul _
  have hAbdd : ∀ (σ : Fin n → Bool) (s : Sample Z n),
      |sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)| ≤ n * c := fun σ s =>
    abs_sSup_image_le hk₀ fun k hk => abs_sum_signOf_le σ _ fun i => hbdd k hk (s i)
  have hempRad_eq : ∀ s : Sample Z n, empRad F K s
      = (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)) := by
    intro s
    simp only [empRad, radComplexity, signAvg, evalFamily, Set.image_image]
  have hRadmeas : Measurable fun s : Sample Z n => empRad F K s := by
    have h : (fun s : Sample Z n => empRad F K s)
        = fun s : Sample Z n => (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
            sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)) := funext hempRad_eq
    rw [h]
    exact measurable_const.mul
      (measurable_const.mul (Finset.measurable_sum _ fun σ _ => hAmeas σ))
  have hRadbdd : ∀ s : Sample Z n, |empRad F K s| ≤ c := by
    intro s
    rw [hempRad_eq s, abs_mul, abs_mul]
    have hsum : |∑ σ : Fin n → Bool, sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)|
        ≤ (2 ^ n : ℝ) * (n * c) := by
      calc |∑ σ : Fin n → Bool, sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)|
          ≤ ∑ σ : Fin n → Bool, |sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _σ : Fin n → Bool, (n : ℝ) * c :=
            Finset.sum_le_sum fun σ _ => hAbdd σ s
        _ = (2 ^ n : ℝ) * (n * c) := by simp [Finset.sum_const, mul_comm]
    have h2 : |(2 ^ n : ℝ)⁻¹| = (2 ^ n : ℝ)⁻¹ := abs_of_nonneg (by positivity)
    have h1 : |(n : ℝ)⁻¹| = (n : ℝ)⁻¹ := abs_of_nonneg (by positivity)
    rw [h1, h2]
    have hstep : (2 ^ n : ℝ)⁻¹ *
        |∑ σ : Fin n → Bool, sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)|
          ≤ (2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * (n * c)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    calc (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ *
          |∑ σ : Fin n → Bool, sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)|)
        ≤ (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * (n * c))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = c := by field_simp
  -- ### Step D: average the swap identity over all sign patterns
  have hKσbdd : ∀ (σ : Fin n → Bool) (w : Sample Z n × Sample Z n),
      |sSup ((fun k => (n : ℝ)⁻¹ *
          ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K)| ≤ 2 * c := by
    intro σ w
    refine abs_sSup_image_le hk₀ fun k hk => ?_
    have hb : |∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))| ≤ (n : ℝ) * (2 * c) :=
      abs_sum_signOf_le σ _ fun i => by
        have h1 := abs_le.1 (hbdd k hk (w.2 i))
        have h2 := abs_le.1 (hbdd k hk (w.1 i))
        exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ)⁻¹)]
    calc (n : ℝ)⁻¹ * |∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))|
        ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (2 * c)) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 * c := by field_simp
  have hKσmeas : ∀ σ : Fin n → Bool, Measurable fun w : Sample Z n × Sample Z n =>
      sSup ((fun k => (n : ℝ)⁻¹ *
        ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K) := fun σ =>
    measurable_sSup_image hKc fun k =>
      (Finset.measurable_sum _ fun i _ =>
        ((((hmeas k).comp (measurable_pi_apply i)).comp measurable_snd).sub
          (((hmeas k).comp (measurable_pi_apply i)).comp measurable_fst)).const_mul _).const_mul _
  have hKσint : ∀ σ : Fin n → Bool, Integrable (fun w : Sample Z n × Sample Z n =>
      sSup ((fun k => (n : ℝ)⁻¹ *
        ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K)) (μ.prod μ) := fun σ =>
    integrable_of_abs_le (hKσmeas σ) (hKσbdd σ)
  have hHavg : ∫ w, sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K) ∂(μ.prod μ)
      = ∫ w, ((2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          sSup ((fun k => (n : ℝ)⁻¹ *
            ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K)) ∂(μ.prod μ) := by
    rw [integral_const_mul, integral_finset_sum _ fun σ _ => hKσint σ,
      Finset.sum_congr rfl fun σ (_ : σ ∈ Finset.univ) => (hstepC σ).symm,
      Finset.sum_const, Finset.card_univ]
    have hcard : (Fintype.card (Fin n → Bool) : ℝ) = 2 ^ n := by simp
    rw [nsmul_eq_mul, hcard]
    field_simp
  -- ### Step E: split the signed sup and identify the two Rademacher averages
  have hstepE : ∀ w : Sample Z n × Sample Z n,
      (2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          sSup ((fun k => (n : ℝ)⁻¹ *
            ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K)
        ≤ empRad F K w.2 + empRad F K w.1 := by
    intro w
    have hper : ∀ σ : Fin n → Bool,
        sSup ((fun k => (n : ℝ)⁻¹ *
            ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K)
          ≤ (n : ℝ)⁻¹ * sSup ((fun k => ∑ i, signOf σ i * F k (w.2 i)) '' K)
            + (n : ℝ)⁻¹ *
                sSup ((fun k => ∑ i, signOf (fun j => !(σ j)) i * F k (w.1 i)) '' K) := by
      intro σ
      refine csSup_le (Set.Nonempty.image _ ⟨k₀, hk₀⟩) ?_
      rintro y ⟨k, hk, rfl⟩
      have hsplit : ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))
          = (∑ i, signOf σ i * F k (w.2 i))
            + ∑ i, signOf (fun j => !(σ j)) i * F k (w.1 i) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases hσi : σ i with _ | _ <;> simp [signOf, hσi] <;> ring
      have hb2 : ∑ i, signOf σ i * F k (w.2 i)
          ≤ sSup ((fun k => ∑ i, signOf σ i * F k (w.2 i)) '' K) :=
        le_sSup_image hk fun j hj =>
          (abs_le.1 (abs_sum_signOf_le σ _ fun i => hbdd j hj (w.2 i))).2
      have hb1 : ∑ i, signOf (fun j => !(σ j)) i * F k (w.1 i)
          ≤ sSup ((fun k => ∑ i, signOf (fun j => !(σ j)) i * F k (w.1 i)) '' K) :=
        le_sSup_image hk fun j hj =>
          (abs_le.1 (abs_sum_signOf_le _ _ fun i => hbdd j hj (w.1 i))).2
      change (n : ℝ)⁻¹ * ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))
          ≤ (n : ℝ)⁻¹ * sSup ((fun k => ∑ i, signOf σ i * F k (w.2 i)) '' K)
            + (n : ℝ)⁻¹ *
                sSup ((fun k => ∑ i, signOf (fun j => !(σ j)) i * F k (w.1 i)) '' K)
      rw [hsplit, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_left hb2 (by positivity))
        (mul_le_mul_of_nonneg_left hb1 (by positivity))
    have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hper σ
    have hmono := mul_le_mul_of_nonneg_left hsum
      (by positivity : (0:ℝ) ≤ (2 ^ n : ℝ)⁻¹)
    refine hmono.trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib]
    have hflip : ∑ σ : Fin n → Bool, (n : ℝ)⁻¹ *
          sSup ((fun k => ∑ i, signOf (fun j => !(σ j)) i * F k (w.1 i)) '' K)
        = ∑ σ : Fin n → Bool, (n : ℝ)⁻¹ *
            sSup ((fun k => ∑ i, signOf σ i * F k (w.1 i)) '' K) :=
      sum_bool_flip (fun σ => (n : ℝ)⁻¹ *
        sSup ((fun k => ∑ i, signOf σ i * F k (w.1 i)) '' K))
    rw [hflip, hempRad_eq w.2, hempRad_eq w.1, mul_add, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  -- ### Step F: marginalize
  have hRadint2 : Integrable (fun w : Sample Z n × Sample Z n =>
      empRad F K w.2 + empRad F K w.1) (μ.prod μ) :=
    integrable_of_abs_le (M := 2 * c)
      ((hRadmeas.comp measurable_snd).add (hRadmeas.comp measurable_fst)) fun w => by
        have h1 := abs_le.1 (hRadbdd w.2)
        have h2 := abs_le.1 (hRadbdd w.1)
        exact abs_le.2 ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
  have hRadint1 : Integrable (fun s : Sample Z n => empRad F K s) μ :=
    integrable_of_abs_le hRadmeas hRadbdd
  have hHavgint : Integrable (fun w : Sample Z n × Sample Z n =>
      (2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
        sSup ((fun k => (n : ℝ)⁻¹ *
          ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K)) (μ.prod μ) :=
    (integrable_finset_sum _ fun σ _ => hKσint σ).const_mul _
  have hmarg : ∫ w : Sample Z n × Sample Z n,
      (empRad F K w.2 + empRad F K w.1) ∂(μ.prod μ) = 2 * ∫ s, empRad F K s ∂μ := by
    rw [integral_prod _ hRadint2]
    have hinner : ∀ s : Sample Z n, ∫ s', (empRad F K s' + empRad F K s) ∂μ
        = (∫ s', empRad F K s' ∂μ) + empRad F K s := by
      intro s
      rw [integral_add hRadint1 (integrable_const _), integral_const]
      simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hinner),
      integral_add (integrable_const _) hRadint1, integral_const]
    simp
    ring
  calc ∫ s, sSup ((fun k => risk D F k - empRisk F s k) '' K) ∂μ
      ≤ ∫ w, sSup ((fun k => empRisk F w.2 k - empRisk F w.1 k) '' K) ∂(μ.prod μ) := hstepB
    _ = ∫ w, ((2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          sSup ((fun k => (n : ℝ)⁻¹ *
            ∑ i, signOf σ i * (F k (w.2 i) - F k (w.1 i))) '' K)) ∂(μ.prod μ) := hHavg
    _ ≤ ∫ w, (empRad F K w.2 + empRad F K w.1) ∂(μ.prod μ) :=
        integral_mono hHavgint hRadint2 hstepE
    _ = 2 * ∫ s, empRad F K s ∂μ := hmarg


end StatLean.StatisticalLearning
