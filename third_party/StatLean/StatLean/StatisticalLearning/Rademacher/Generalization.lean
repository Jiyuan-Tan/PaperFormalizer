module
public import StatLean.StatisticalLearning.Rademacher.Symmetrization
public import StatLean.ConcentrationInequalities.McDiarmid.McDiarmid

@[expose] public section

/-!
# Rademacher generalization bounds

The ERM bounds in expectation and via Markov (SSBD Theorem 26.3) and the
high-probability generalization bounds (SSBD Theorem 26.5, parts 1–3, exact
constants): for a family uniformly bounded by `c`, with probability `≥ 1 − δ`,
* (1) `∀f: L_D(f) − L_S(f) ≤ 2 E_{S'} R(𝓕∘S') + c√(2 ln(2/δ)/n)`;
* (2) `∀f: L_D(f) − L_S(f) ≤ 2 R(𝓕∘S) + 4c√(2 ln(4/δ)/n)`;
* (3) ERM vs any fixed `f⋆`: `≤ 2 R(𝓕∘S) + 5c√(2 ln(8/δ)/n)`.

**Reference.** SSBD §26.1, Theorems 26.3 and 26.5, Lemma 26.4 (McDiarmid).
Transcription: `notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.** McDiarmid comes from
`ConcentrationInequalities/McDiarmid/McDiarmid.lean` (bounded differences
`2c/n` for both `sup_k(L_D − L_S)` and `R(𝓕∘S)` as functions of the sample;
this forces the LEAN-ONLY `StandardBorelSpace Z`/`Nonempty Z` instances that
the repo's McDiarmid carries). Part 3's deviation of the fixed competitor
(SSBD Eq. (26.11)) is taken from the *same* McDiarmid brick applied to
`s ↦ L_S(k⋆)` — which has the same `2c/n` bounded differences and mean
`L_D(k⋆)` (`integral_empRisk`) — rather than from a separate Hoeffding bound;
the three deviations are combined by a union bound at `δ/8` each, which lands
inside the book's frozen `5c√(2 log(8/δ)/n)`. The three high-probability
statements degenerate at `c = 0` (every loss vanishes, both sides are `0`), a
case split the McDiarmid tail calibration `exp(−n t²/(2c²)) = δ/a` needs.
Countable index + `sSup`-image sups + uniform bound per the batch sup policy.
-/

open MeasureTheory ProbabilityTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {Z ι : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z]
  {D : Measure Z} [IsProbabilityMeasure D] {n : ℕ}
  {F : ι → Z → ℝ} {K : Set ι} {c : ℝ}

/-! ### LEAN-ONLY toolkit: countable `sSup`-of-image, bounded integrands, coordinate
perturbations, and the McDiarmid/Markov wrappers used by all six theorems.

These mirror the private helpers of `Rademacher/Symmetrization.lean` (private
declarations are file-scoped, so the shared ones are restated here). -/

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

/-- Uniformly `d`-close families have `d`-close sups — the sup stability behind the
bounded-differences estimates. -/
private lemma abs_sSup_image_sub_le {f g : ι → ℝ} {K : Set ι} {d M : ℝ} (hne : K.Nonempty)
    (hf : ∀ k ∈ K, f k ≤ M) (hg : ∀ k ∈ K, g k ≤ M) (h : ∀ k ∈ K, |f k - g k| ≤ d) :
    |sSup (f '' K) - sSup (g '' K)| ≤ d := by
  have h1 : sSup (f '' K) ≤ sSup (g '' K) + d :=
    sSup_image_le hne fun k hk => by
      have h2 := (abs_le.1 (h k hk)).2
      have h3 : g k ≤ sSup (g '' K) := le_sSup_image hk hg
      linarith
  have h4 : sSup (g '' K) ≤ sSup (f '' K) + d :=
    sSup_image_le hne fun k hk => by
      have h2 := (abs_le.1 (h k hk)).1
      have h3 : f k ≤ sSup (f '' K) := le_sSup_image hk hf
      linarith
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- Rademacher signs have modulus one. -/
private lemma abs_signOf (σ : Fin n → Bool) (i : Fin n) : |signOf σ i| = 1 := by
  rcases h : σ i <;> simp [signOf, h]

/-- A sign-weighted sum of `n` terms of modulus `≤ M` has modulus `≤ n M`. -/
private lemma abs_sum_signOf_le (σ : Fin n → Bool) (g : Fin n → ℝ) {M : ℝ}
    (h : ∀ i, |g i| ≤ M) : |∑ i, signOf σ i * g i| ≤ n * M := by
  calc |∑ i, signOf σ i * g i| ≤ ∑ i, |signOf σ i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_signOf, one_mul]; exact h i
    _ = n * M := by simp [mul_comm]

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

/-! ### coordinate perturbation -/

omit [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] in
/-- Updating one coordinate changes a coordinatewise sum only through that
coordinate. -/
private lemma sum_sub_sum_update (h : Fin n → Z → ℝ) (x : Sample Z n) (j : Fin n) (y : Z) :
    (∑ i, h i (x i)) - (∑ i, h i (Function.update x j y i)) = h j (x j) - h j y := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [Function.update_of_ne hij]
    ring
  · simp

/-! ### `empRad` as a sign average -/

omit [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] in
/-- `empRad` written out as the explicit `2ⁿ`-term sign average of sups — the form
used for measurability, boundedness and bounded differences. -/
private lemma empRad_eq_signAvg (F : ι → Z → ℝ) (K : Set ι) (s : Sample Z n) :
    empRad F K s = (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
      sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)) := by
  simp only [empRad, radComplexity, signAvg, evalFamily, Set.image_image]

omit [StandardBorelSpace Z] [Nonempty Z] in
/-- The empirical Rademacher complexity is measurable in the sample (finite sum of
countable sups of measurable functions). -/
private lemma measurable_empRad (hKc : K.Countable) (hmeas : ∀ k, Measurable (F k)) :
    Measurable fun s : Sample Z n => empRad F K s := by
  have h : (fun s : Sample Z n => empRad F K s)
      = fun s : Sample Z n => (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
          sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)) :=
    funext (empRad_eq_signAvg F K)
  rw [h]
  exact measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun σ _ =>
    measurable_sSup_image hKc fun k =>
      Finset.measurable_sum _ fun i _ => ((hmeas k).comp (measurable_pi_apply i)).const_mul _))

omit [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] in
/-- The empirical Rademacher complexity of a family bounded by `c` is bounded by
`c`. -/
private lemma abs_empRad_le (hK : K.Nonempty) (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n)
    (s : Sample Z n) : |empRad F K s| ≤ c := by
  obtain ⟨k₀, hk₀⟩ := hK
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hA : ∀ σ : Fin n → Bool,
      |sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)| ≤ n * c := fun σ =>
    abs_sSup_image_le hk₀ fun k hk => abs_sum_signOf_le σ _ fun i => hbdd k hk (s i)
  rw [empRad_eq_signAvg F K s, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ)⁻¹),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 ^ n : ℝ)⁻¹)]
  have hsum : |∑ σ : Fin n → Bool, sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)|
      ≤ (2 ^ n : ℝ) * ((n : ℝ) * c) := by
    calc |∑ σ : Fin n → Bool, sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)|
        ≤ ∑ σ : Fin n → Bool, |sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Fin n → Bool, (n : ℝ) * c := Finset.sum_le_sum fun σ _ => hA σ
      _ = (2 ^ n : ℝ) * ((n : ℝ) * c) := by simp [mul_comm]
  calc (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ *
        |∑ σ : Fin n → Bool, sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K)|)
      ≤ (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * ((n : ℝ) * c))) := by
        gcongr
    _ = c := by field_simp

/-! ### risk / empirical-risk bounds -/

omit [StandardBorelSpace Z] [Nonempty Z] in
/-- Empirical risks of a family bounded by `c` are bounded by `c`. -/
private lemma abs_empRisk_le (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n) {k : ι}
    (hk : k ∈ K) (s : Sample Z n) : |empRisk F s k| ≤ c :=
  abs_le.2 (Set.mem_Icc.1 (empRisk_mem_Icc (fun z => abs_le.1 (hbdd k hk z)) hn s))

omit [StandardBorelSpace Z] [Nonempty Z] in
/-- True risks of a family bounded by `c` are bounded by `c`. -/
private lemma abs_risk_le (hmeas : ∀ k, Measurable (F k)) (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    {k : ι} (hk : k ∈ K) : |risk D F k| ≤ c :=
  abs_le.2 (Set.mem_Icc.1 (risk_mem_Icc (fun z => abs_le.1 (hbdd k hk z)) (hmeas k)))

omit [StandardBorelSpace Z] [Nonempty Z] in
/-- The representativeness gap of a single hypothesis is bounded by `2c`. -/
private lemma abs_risk_sub_empRisk_le (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n) {k : ι} (hk : k ∈ K) (s : Sample Z n) :
    |risk D F k - empRisk F s k| ≤ 2 * c := by
  have h1 := abs_le.1 (abs_risk_le (D := D) hmeas hbdd hk)
  have h2 := abs_le.1 (abs_empRisk_le hbdd hn hk s)
  exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

omit [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure D] in
/-- The representativeness functional `s ↦ sup_k (L_D(k) − L_s(k))` is measurable. -/
private lemma measurable_gap (hKc : K.Countable) (hmeas : ∀ k, Measurable (F k)) :
    Measurable fun s : Sample Z n => sSup ((fun k => risk D F k - empRisk F s k) '' K) :=
  measurable_sSup_image hKc fun k => measurable_const.sub (measurable_empRisk (hmeas k))

omit [StandardBorelSpace Z] [Nonempty Z] in
/-- The representativeness functional is bounded by `2c`. -/
private lemma abs_gap_le (hK : K.Nonempty) (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n) (s : Sample Z n) :
    |sSup ((fun k => risk D F k - empRisk F s k) '' K)| ≤ 2 * c := by
  obtain ⟨k₀, hk₀⟩ := hK
  exact abs_sSup_image_le hk₀ fun k hk => abs_risk_sub_empRisk_le hmeas hbdd hn hk s

omit [StandardBorelSpace Z] [Nonempty Z] in
/-- The representativeness functional is integrable (bounded and measurable). -/
private lemma integrable_gap (hKc : K.Countable) (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k)) (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n) :
    Integrable (fun s : Sample Z n =>
      sSup ((fun k => risk D F k - empRisk F s k) '' K)) (sampleLaw D n) :=
  integrable_of_abs_le (measurable_gap hKc hmeas) (abs_gap_le hK hmeas hbdd hn)

/-! ### bounded differences -/

omit [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] in
/-- **Bounded differences for the empirical risk**: changing one example moves
`L_S(k)` by at most `2c/n`. -/
private lemma abs_empRisk_sub_update_le (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n)
    {k : ι} (hk : k ∈ K) (j : Fin n) (x : Sample Z n) (y : Z) :
    |empRisk F x k - empRisk F (Function.update x j y) k| ≤ 2 * c / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hd : |F k (x j) - F k y| ≤ 2 * c := by
    have h1 := abs_le.1 (hbdd k hk (x j))
    have h2 := abs_le.1 (hbdd k hk y)
    exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  rw [empRisk, empRisk, ← mul_sub, sum_sub_sum_update (fun _ z => F k z) x j y, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ)⁻¹)]
  calc (n : ℝ)⁻¹ * |F k (x j) - F k y| ≤ (n : ℝ)⁻¹ * (2 * c) := by gcongr
    _ = 2 * c / n := by field_simp

omit [StandardBorelSpace Z] [Nonempty Z] in
/-- **Bounded differences for the representativeness functional** (SSBD Thm 26.5,
the `2c/n` of Lemma 26.4's application): changing one example moves every
element of the sup's image by `≤ 2c/n`, hence the sup itself. -/
private lemma abs_gap_sub_update_le (hK : K.Nonempty) (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n) (j : Fin n) (x : Sample Z n) (y : Z) :
    |sSup ((fun k => risk D F k - empRisk F x k) '' K)
        - sSup ((fun k => risk D F k - empRisk F (Function.update x j y) k) '' K)|
      ≤ 2 * c / n := by
  refine abs_sSup_image_sub_le (M := 2 * c) hK
    (fun k hk => (abs_le.1 (abs_risk_sub_empRisk_le hmeas hbdd hn hk x)).2)
    (fun k hk => (abs_le.1 (abs_risk_sub_empRisk_le hmeas hbdd hn hk _)).2) fun k hk => ?_
  have he : (risk D F k - empRisk F x k)
      - (risk D F k - empRisk F (Function.update x j y) k)
      = -(empRisk F x k - empRisk F (Function.update x j y) k) := by ring
  rw [he, abs_neg]
  exact abs_empRisk_sub_update_le hbdd hn hk j x y

omit [MeasurableSpace Z] [StandardBorelSpace Z] [Nonempty Z] in
/-- **Bounded differences for the empirical Rademacher complexity**: changing one
example moves `R(F∘S)` by at most `2c/n` (each `ε`-sup moves by `≤ 2c`, and the
average carries the `n⁻¹`). -/
private lemma abs_empRad_sub_update_le (hK : K.Nonempty)
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c) (hn : 1 ≤ n) (j : Fin n) (x : Sample Z n) (y : Z) :
    |empRad F K x - empRad F K (Function.update x j y)| ≤ 2 * c / n := by
  obtain ⟨k₀, hk₀⟩ := hK
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hbdd k₀ hk₀ (x j))
  have hper : ∀ σ : Fin n → Bool,
      |sSup ((fun k => ∑ i, signOf σ i * F k (x i)) '' K)
        - sSup ((fun k => ∑ i, signOf σ i * F k (Function.update x j y i)) '' K)|
        ≤ 2 * c := by
    intro σ
    refine abs_sSup_image_sub_le (M := (n : ℝ) * c) ⟨k₀, hk₀⟩
      (fun k hk => (abs_le.1 (abs_sum_signOf_le σ _ fun i => hbdd k hk (x i))).2)
      (fun k hk => (abs_le.1 (abs_sum_signOf_le σ _ fun i => hbdd k hk _)).2) fun k hk => ?_
    rw [sum_sub_sum_update (fun i z => signOf σ i * F k z) x j y]
    have he : signOf σ j * F k (x j) - signOf σ j * F k y
        = signOf σ j * (F k (x j) - F k y) := by ring
    rw [he, abs_mul, abs_signOf, one_mul]
    have h1 := abs_le.1 (hbdd k hk (x j))
    have h2 := abs_le.1 (hbdd k hk y)
    exact abs_le.2 ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  rw [empRad_eq_signAvg F K x, empRad_eq_signAvg F K (Function.update x j y), ← mul_sub,
    ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ)⁻¹),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 ^ n : ℝ)⁻¹)]
  have hsum : |∑ σ : Fin n → Bool, (sSup ((fun k => ∑ i, signOf σ i * F k (x i)) '' K)
        - sSup ((fun k => ∑ i, signOf σ i * F k (Function.update x j y i)) '' K))|
      ≤ (2 ^ n : ℝ) * (2 * c) := by
    calc |∑ σ : Fin n → Bool, (sSup ((fun k => ∑ i, signOf σ i * F k (x i)) '' K)
            - sSup ((fun k => ∑ i, signOf σ i * F k (Function.update x j y i)) '' K))|
        ≤ ∑ σ : Fin n → Bool, |sSup ((fun k => ∑ i, signOf σ i * F k (x i)) '' K)
            - sSup ((fun k => ∑ i, signOf σ i * F k (Function.update x j y i)) '' K)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Fin n → Bool, 2 * c := Finset.sum_le_sum fun σ _ => hper σ
      _ = (2 ^ n : ℝ) * (2 * c) := by simp [mul_comm]
  calc (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * |∑ σ : Fin n → Bool,
        (sSup ((fun k => ∑ i, signOf σ i * F k (x i)) '' K)
          - sSup ((fun k => ∑ i, signOf σ i * F k (Function.update x j y i)) '' K))|)
      ≤ (n : ℝ)⁻¹ * ((2 ^ n : ℝ)⁻¹ * ((2 ^ n : ℝ) * (2 * c))) := by gcongr
    _ = 2 * c / n := by field_simp

/-! ### McDiarmid on the sample law, and the tail arithmetic -/

/-- McDiarmid (`ConcentrationInequalities.McDiarmid`) specialized to the i.i.d.
sample law with the uniform bounded-differences constant `2c/n`; the exponent
`−2t²/∑ₖcₖ²` becomes the book's `−n t²/(2c²)`. -/
private lemma mcdiarmid_sampleLaw {f : Sample Z n → ℝ} (hf : Measurable f)
    (hint : Integrable f (sampleLaw D n))
    (hbd : ∀ (j : Fin n) (x : Sample Z n) (y : Z),
      |f x - f (Function.update x j y)| ≤ 2 * c / n)
    (hc : 0 ≤ c) (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    sampleLaw D n {s | t < f s - ∫ s', f s' ∂(sampleLaw D n)}
      ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * t ^ 2 / (2 * c ^ 2))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hmc := McDiarmid (μ := sampleLaw D n) (β := fun _ : Fin n => Z)
    (fun (i : Fin n) (s : Sample Z n) => s i) (fun i => measurable_pi_apply i) f hf
    (fun _ => 2 * c / n) (fun _ => div_nonneg (by linarith) hnR.le) hbd
    iIndepFun_eval_sampleLaw hint ht
  have hexp : Real.exp (-2 * t ^ 2 / (∑ _k : Fin n, (2 * c / n) ^ 2))
      = Real.exp (-(n : ℝ) * t ^ 2 / (2 * c ^ 2)) := by
    congr 1
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
      field_simp
  rw [hexp] at hmc
  exact hmc

/-- The book's threshold calibration: at `t = c √(2 log(a/δ)/n)` the McDiarmid tail
`exp(−n t²/(2c²))` equals `δ/a` (SSBD Thm 26.5's choice of constants). -/
private lemma exp_tail_eq {a δ t : ℝ} (hc : 0 < c) (hn : 1 ≤ n) (ha : 0 < a) (hδ : 0 < δ)
    (hL : 0 ≤ Real.log (a / δ)) (ht : t = c * Real.sqrt (2 * Real.log (a / δ) / n)) :
    Real.exp (-(n : ℝ) * t ^ 2 / (2 * c ^ 2)) = δ / a := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hnn : (0 : ℝ) ≤ 2 * Real.log (a / δ) / n := div_nonneg (by linarith) hnR.le
  have hsq : t ^ 2 = c ^ 2 * (2 * Real.log (a / δ) / n) := by
    rw [ht, mul_pow, Real.sq_sqrt hnn]
  have hkey : -(n : ℝ) * t ^ 2 / (2 * c ^ 2) = -Real.log (a / δ) := by
    rw [hsq]
    field_simp
  rw [hkey, Real.exp_neg, Real.exp_log (by positivity), inv_div]

/-- A small complement gives a `1 − δ` lower bound on the (possibly non-measurable,
outer-measure) event, by subadditivity. -/
private lemma prob_ge_of_compl_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {E : Set X} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ν Eᶜ ≤ ENNReal.ofReal δ) : ENNReal.ofReal (1 - δ) ≤ ν E := by
  have h1 : (1 : ℝ≥0∞) ≤ ν E + ν Eᶜ := by
    have h2 := measure_union_le (μ := ν) E Eᶜ
    rwa [Set.union_compl_self, measure_univ] at h2
  have h3 : (1 : ℝ≥0∞) ≤ ν E + ENNReal.ofReal δ := h1.trans (add_le_add le_rfl h)
  rw [ENNReal.ofReal_sub _ hδ, ENNReal.ofReal_one]
  exact tsub_le_iff_right.2 h3

/-- **Markov's inequality** in the `1 − δ` form used by SSBD Thm 26.3: a nonnegative
integrable `f` with `E f ≤ R` satisfies `f ≤ R/δ` with probability `≥ 1 − δ`.
The degenerate `R = 0` case is handled by `f =ᵐ 0`. -/
private lemma markov_prob {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    {f : X → ℝ} {R δ : ℝ} (hf : Integrable f ν) (hnn : ∀ x, 0 ≤ f x)
    (hR : ∫ x, f x ∂ν ≤ R) (hδ : 0 < δ) :
    ENNReal.ofReal (1 - δ) ≤ ν {x | f x ≤ R / δ} := by
  refine prob_ge_of_compl_le hδ.le ?_
  have hI : 0 ≤ ∫ x, f x ∂ν := integral_nonneg hnn
  have hR0 : 0 ≤ R := hI.trans hR
  rcases eq_or_lt_of_le hR0 with hR' | hRpos
  · have hI0 : ∫ x, f x ∂ν = 0 := le_antisymm (hR.trans hR'.symm.le) hI
    have hae := (integral_eq_zero_iff_of_nonneg hnn hf).1 hI0
    have hnull : ν {x | ¬ (f x = 0)} = 0 := ae_iff.1 hae
    have hsub : {x | f x ≤ R / δ}ᶜ ⊆ {x | ¬ (f x = 0)} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      have hx' : R / δ < f x := hx
      rw [← hR', zero_div] at hx'
      exact fun h => absurd h (ne_of_gt hx')
    calc ν {x | f x ≤ R / δ}ᶜ ≤ ν {x | ¬ (f x = 0)} := measure_mono hsub
      _ = 0 := hnull
      _ ≤ ENNReal.ofReal δ := zero_le
  · have hsub : {x | f x ≤ R / δ}ᶜ ⊆ {x | R / δ ≤ f x} := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
      exact hx.le
    have hpos : 0 < R / δ := div_pos hRpos hδ
    have hmark := mul_meas_ge_le_integral_of_nonneg (μ := ν)
      (Filter.Eventually.of_forall hnn) hf (R / δ)
    have h2 : (R / δ) * ν.real {x | R / δ ≤ f x} ≤ (R / δ) * δ := by
      rw [div_mul_cancel₀ R hδ.ne']
      exact hmark.trans hR
    have hreal : ν.real {x | R / δ ≤ f x} ≤ δ := le_of_mul_le_mul_left h2 hpos
    calc ν {x | f x ≤ R / δ}ᶜ ≤ ν {x | R / δ ≤ f x} := measure_mono hsub
      _ = ENNReal.ofReal (ν.real {x | R / δ ≤ f x}) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hreal

/-- The good event of SSBD Thm 26.5: `f` exceeds its mean by more than
`c √(2 log(a/δ)/n)` with probability at most `δ/a`. -/
private lemma mcdiarmid_event {f : Sample Z n → ℝ} (hf : Measurable f)
    (hint : Integrable f (sampleLaw D n))
    (hbd : ∀ (j : Fin n) (x : Sample Z n) (y : Z),
      |f x - f (Function.update x j y)| ≤ 2 * c / n)
    (hc : 0 < c) (hn : 1 ≤ n) {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hle : δ ≤ a) :
    sampleLaw D n {s | f s ≤ (∫ s', f s' ∂(sampleLaw D n))
        + c * Real.sqrt (2 * Real.log (a / δ) / n)}ᶜ ≤ ENNReal.ofReal (δ / a) := by
  have hL : 0 ≤ Real.log (a / δ) := Real.log_nonneg ((one_le_div hδ).2 hle)
  have ht : 0 ≤ c * Real.sqrt (2 * Real.log (a / δ) / n) :=
    mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hsub : {s : Sample Z n | f s ≤ (∫ s', f s' ∂(sampleLaw D n))
        + c * Real.sqrt (2 * Real.log (a / δ) / n)}ᶜ
      ⊆ {s | c * Real.sqrt (2 * Real.log (a / δ) / n)
            < f s - ∫ s', f s' ∂(sampleLaw D n)} := by
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hs
    simp only [Set.mem_setOf_eq]
    linarith
  calc sampleLaw D n {s | f s ≤ (∫ s', f s' ∂(sampleLaw D n))
          + c * Real.sqrt (2 * Real.log (a / δ) / n)}ᶜ
      ≤ sampleLaw D n {s | c * Real.sqrt (2 * Real.log (a / δ) / n)
          < f s - ∫ s', f s' ∂(sampleLaw D n)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) *
          (c * Real.sqrt (2 * Real.log (a / δ) / n)) ^ 2 / (2 * c ^ 2))) :=
        mcdiarmid_sampleLaw hf hint hbd hc.le hn ht
    _ = ENNReal.ofReal (δ / a) := by rw [exp_tail_eq hc hn ha hδ hL rfl]

/-- **SSBD Theorem 26.3 (first display)**: an ERM-style selector's expected
overfitting gap is at most twice the expected Rademacher complexity:
`E_S[L_D(A(S)) − L_S(A(S))] ≤ 2 E_S R(F∘S)` whenever `A` selects in `K`. -/
theorem integral_risk_sub_empRisk_le_two_mul_integral_empRad
    {A : Sample Z n → ι}
    -- USER-INPUT: nonempty family; SSBD §26.1 (implicit)
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    -- USER-INPUT: measurability of the family; SSBD Remark 3.1
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniform bound `|f| ≤ c`; SSBD Thm 26.5 setting
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: the selector stays in the family; SSBD §26.1 (ERM ∈ 𝓗)
    (hA : ∀ s, A s ∈ K)
    -- LEAN-ONLY: a.e.-strong measurability of the selected risk/empirical
    -- gap in the sample (the book's `E[…]` presupposes it)
    (hAmeas : AEStronglyMeasurable
      (fun s => risk D F (A s) - empRisk F s (A s)) (sampleLaw D n))
    -- USER-INPUT: at least one example; SSBD §26.1 (implicit)
    (hn : 1 ≤ n) :
    ∫ s, (risk D F (A s) - empRisk F s (A s)) ∂(sampleLaw D n) ≤
      2 * ∫ s, empRad F K s ∂(sampleLaw D n) := by
  have hAint : Integrable (fun s => risk D F (A s) - empRisk F s (A s)) (sampleLaw D n) :=
    (integrable_const (2 * c)).mono' hAmeas (Filter.Eventually.of_forall fun s => by
      simpa [Real.norm_eq_abs] using abs_risk_sub_empRisk_le hmeas hbdd hn (hA s) s)
  calc ∫ s, (risk D F (A s) - empRisk F s (A s)) ∂(sampleLaw D n)
      ≤ ∫ s, sSup ((fun k => risk D F k - empRisk F s k) '' K) ∂(sampleLaw D n) :=
        integral_mono hAint (integrable_gap hKc hK hmeas hbdd hn) fun s =>
          le_sSup_image (hA s) fun k hk =>
            (abs_le.1 (abs_risk_sub_empRisk_le hmeas hbdd hn hk s)).2
    _ ≤ 2 * ∫ s, empRad F K s ∂(sampleLaw D n) :=
        integral_sup_risk_sub_empRisk_le_two_mul_integral_empRad F K hKc hK hmeas hbdd hn


/-- **SSBD Theorem 26.3 (second display)**: for an ERM selector `A` and any
competitor `kStar ∈ K`,
`E_S[L_D(A(S))] − L_D(kStar) ≤ 2 E_S R(F∘S)`. -/
theorem integral_risk_erm_sub_risk_le_two_mul_integral_empRad
    {A : Sample Z n → ι} {kStar : ι}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: `A` is an ERM selector over `K`; SSBD Thm 26.3
    (hA : ∀ s, A s ∈ K ∧ ∀ k ∈ K, empRisk F s (A s) ≤ empRisk F s k)
    -- USER-INPUT: the competitor lies in the family; SSBD Thm 26.3
    (hkStar : kStar ∈ K)
    -- LEAN-ONLY: a.e.-strong measurability of the selected risk
    (hAmeas : AEStronglyMeasurable
      (fun s => risk D F (A s)) (sampleLaw D n))
    (hn : 1 ≤ n) :
    ∫ s, risk D F (A s) ∂(sampleLaw D n) - risk D F kStar ≤
      2 * ∫ s, empRad F K s ∂(sampleLaw D n) := by
  have hAint : Integrable (fun s => risk D F (A s)) (sampleLaw D n) :=
    (integrable_const c).mono' hAmeas (Filter.Eventually.of_forall fun s => by
      simpa [Real.norm_eq_abs] using abs_risk_le (D := D) hmeas hbdd (hA s).1)
  have hkint : Integrable (fun s : Sample Z n => empRisk F s kStar) (sampleLaw D n) :=
    integrable_of_abs_le (measurable_empRisk (hmeas kStar)) (abs_empRisk_le hbdd hn hkStar)
  have hgapint := integrable_gap (D := D) hKc hK hmeas hbdd hn
  have hptw : ∀ s : Sample Z n, risk D F (A s) ≤
      sSup ((fun k => risk D F k - empRisk F s k) '' K) + empRisk F s kStar := by
    intro s
    have h1 : risk D F (A s) - empRisk F s (A s)
        ≤ sSup ((fun k => risk D F k - empRisk F s k) '' K) :=
      le_sSup_image (hA s).1 fun k hk =>
        (abs_le.1 (abs_risk_sub_empRisk_le hmeas hbdd hn hk s)).2
    have h2 : empRisk F s (A s) ≤ empRisk F s kStar := (hA s).2 kStar hkStar
    linarith
  have hstep : ∫ s, risk D F (A s) ∂(sampleLaw D n)
      ≤ (∫ s, sSup ((fun k => risk D F k - empRisk F s k) '' K) ∂(sampleLaw D n))
        + risk D F kStar := by
    calc ∫ s, risk D F (A s) ∂(sampleLaw D n)
        ≤ ∫ s, (sSup ((fun k => risk D F k - empRisk F s k) '' K) + empRisk F s kStar)
            ∂(sampleLaw D n) := integral_mono hAint (hgapint.add hkint) hptw
      _ = (∫ s, sSup ((fun k => risk D F k - empRisk F s k) '' K) ∂(sampleLaw D n))
            + risk D F kStar := by
          rw [integral_add hgapint hkint,
            integral_empRisk (integrable_of_abs_le (hmeas kStar) (hbdd kStar hkStar)) hn]
  have h262 := integral_sup_risk_sub_empRisk_le_two_mul_integral_empRad (D := D) F K hKc hK
    hmeas hbdd hn
  linarith


/-- **SSBD Theorem 26.3 (third display, Markov)**: with probability `≥ 1 − δ`,
the ERM excess risk over the best competitor is at most
`2 E_{S'} R(F∘S')/δ`. -/
theorem measure_erm_excess_le_two_mul_integral_empRad_div
    {A : Sample Z n → ι} {kStar : ι} {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    (hA : ∀ s, A s ∈ K ∧ ∀ k ∈ K, empRisk F s (A s) ≤ empRisk F s k)
    -- USER-INPUT: `kStar` is a risk minimizer of the family (so the excess is
    -- nonnegative and Markov applies); SSBD Thm 26.3
    (hkStar : kStar ∈ K) (hmin : ∀ k ∈ K, risk D F kStar ≤ risk D F k)
    (hAmeas : AEStronglyMeasurable
      (fun s => risk D F (A s)) (sampleLaw D n))
    (hn : 1 ≤ n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Thm 26.3
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | risk D F (A s) - risk D F kStar ≤
        2 * (∫ s', empRad F K s' ∂(sampleLaw D n)) / δ} := by
  have hAint : Integrable (fun s => risk D F (A s)) (sampleLaw D n) :=
    (integrable_const c).mono' hAmeas (Filter.Eventually.of_forall fun s => by
      simpa [Real.norm_eq_abs] using abs_risk_le (D := D) hmeas hbdd (hA s).1)
  have hXint : Integrable (fun s => risk D F (A s) - risk D F kStar) (sampleLaw D n) :=
    hAint.sub (integrable_const _)
  have hXnn : ∀ s : Sample Z n, 0 ≤ risk D F (A s) - risk D F kStar := fun s =>
    sub_nonneg.2 (hmin _ (hA s).1)
  have hXR : ∫ s, (risk D F (A s) - risk D F kStar) ∂(sampleLaw D n)
      ≤ 2 * ∫ s', empRad F K s' ∂(sampleLaw D n) := by
    rw [integral_sub hAint (integrable_const _), integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    exact integral_risk_erm_sub_risk_le_two_mul_integral_empRad hKc hK hmeas hbdd hA
      hkStar hAmeas hn
  exact markov_prob hXint hXnn hXR hδ


/-- **SSBD Theorem 26.5, part 1**: with probability `≥ 1 − δ`, simultaneously
for every `k ∈ K`,
`L_D(F k) − L_S(F k) ≤ 2 E_{S'∼Dⁿ} R(F∘S') + c √(2 ln(2/δ)/n)`. -/
theorem rademacher_generalization_expected {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    -- USER-INPUT: uniform bound `|ℓ(h,z)| ≤ c`; SSBD Thm 26.5
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    (hn : 1 ≤ n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD Thm 26.5
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ k ∈ K,
        risk D F k - empRisk F s k ≤
          2 * (∫ s', empRad F K s' ∂(sampleLaw D n)) +
            c * Real.sqrt (2 * Real.log (2 / δ) / n)} := by
  obtain ⟨k₀, hk₀⟩ := hK
  have hK' : K.Nonempty := ⟨k₀, hk₀⟩
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hbdd k₀ hk₀ (Classical.arbitrary Z))
  rcases eq_or_lt_of_le hc0 with hc | hcpos
  · have hF0 : ∀ k ∈ K, ∀ z, F k z = 0 := by
      intro k hk z
      have h := hbdd k hk z
      rw [← hc] at h
      exact abs_eq_zero.1 (le_antisymm h (abs_nonneg _))
    have hrisk0 : ∀ k ∈ K, risk D F k = 0 := fun k hk => by simp [risk, hF0 k hk]
    have hemp0 : ∀ (s : Sample Z n) (k : ι), k ∈ K → empRisk F s k = 0 := fun s k hk => by
      simp [empRisk, hF0 k hk]
    have hrad0 : ∀ s : Sample Z n, empRad F K s = 0 := by
      intro s
      rw [empRad_eq_signAvg]
      have hz : ∀ σ : Fin n → Bool,
          sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K) = 0 := by
        intro σ
        have himg : (fun k => ∑ i, signOf σ i * F k (s i)) '' K = (fun _ : ι => (0 : ℝ)) '' K :=
          Set.image_congr fun k hk => by simp [hF0 k hk]
        rw [himg, Set.Nonempty.image_const hK', csSup_singleton]
      simp [hz]
    have hset : {s : Sample Z n | ∀ k ∈ K, risk D F k - empRisk F s k ≤
        2 * (∫ s', empRad F K s' ∂(sampleLaw D n)) +
          c * Real.sqrt (2 * Real.log (2 / δ) / n)} = Set.univ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro k hk
      rw [hrisk0 k hk, hemp0 s k hk, ← hc]
      simp [hrad0]
    rw [hset, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  · have hev := mcdiarmid_event (D := D)
      (f := fun s : Sample Z n => sSup ((fun k => risk D F k - empRisk F s k) '' K))
      (measurable_gap hKc hmeas) (integrable_gap (D := D) hKc hK' hmeas hbdd hn)
      (fun j x y => abs_gap_sub_update_le hK' hmeas hbdd hn j x y) hcpos hn
      (a := 2) two_pos hδ (by linarith)
    have h262 := integral_sup_risk_sub_empRisk_le_two_mul_integral_empRad (D := D) F K hKc hK'
      hmeas hbdd hn
    have hgood : ENNReal.ofReal (1 - δ) ≤ sampleLaw D n
        {s : Sample Z n | sSup ((fun k => risk D F k - empRisk F s k) '' K)
          ≤ (∫ s', sSup ((fun k => risk D F k - empRisk F s' k) '' K) ∂(sampleLaw D n))
            + c * Real.sqrt (2 * Real.log (2 / δ) / n)} :=
      prob_ge_of_compl_le hδ.le (hev.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    refine hgood.trans (measure_mono fun s hs k hk => ?_)
    have h1 : risk D F k - empRisk F s k
        ≤ sSup ((fun k => risk D F k - empRisk F s k) '' K) :=
      le_sSup_image hk fun j hj => (abs_le.1 (abs_risk_sub_empRisk_le hmeas hbdd hn hj s)).2
    have h2 : sSup ((fun k => risk D F k - empRisk F s k) '' K)
        ≤ (∫ s', sSup ((fun k => risk D F k - empRisk F s' k) '' K) ∂(sampleLaw D n))
          + c * Real.sqrt (2 * Real.log (2 / δ) / n) := hs
    linarith


/-- **SSBD Theorem 26.5, part 2** (data-dependent bound): with probability
`≥ 1 − δ`, simultaneously for every `k ∈ K`,
`L_D(F k) − L_S(F k) ≤ 2 R(F∘S) + 4c √(2 ln(4/δ)/n)`. -/
theorem rademacher_generalization_empirical {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    (hn : 1 ≤ n)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ k ∈ K,
        risk D F k - empRisk F s k ≤
          2 * empRad F K s + 4 * c * Real.sqrt (2 * Real.log (4 / δ) / n)} := by
  obtain ⟨k₀, hk₀⟩ := hK
  have hK' : K.Nonempty := ⟨k₀, hk₀⟩
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hbdd k₀ hk₀ (Classical.arbitrary Z))
  rcases eq_or_lt_of_le hc0 with hc | hcpos
  · have hF0 : ∀ k ∈ K, ∀ z, F k z = 0 := by
      intro k hk z
      have h := hbdd k hk z
      rw [← hc] at h
      exact abs_eq_zero.1 (le_antisymm h (abs_nonneg _))
    have hrisk0 : ∀ k ∈ K, risk D F k = 0 := fun k hk => by simp [risk, hF0 k hk]
    have hemp0 : ∀ (s : Sample Z n) (k : ι), k ∈ K → empRisk F s k = 0 := fun s k hk => by
      simp [empRisk, hF0 k hk]
    have hrad0 : ∀ s : Sample Z n, empRad F K s = 0 := by
      intro s
      rw [empRad_eq_signAvg]
      have hz : ∀ σ : Fin n → Bool,
          sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K) = 0 := by
        intro σ
        have himg : (fun k => ∑ i, signOf σ i * F k (s i)) '' K = (fun _ : ι => (0 : ℝ)) '' K :=
          Set.image_congr fun k hk => by simp [hF0 k hk]
        rw [himg, Set.Nonempty.image_const hK', csSup_singleton]
      simp [hz]
    have hset : {s : Sample Z n | ∀ k ∈ K, risk D F k - empRisk F s k ≤
        2 * empRad F K s + 4 * c * Real.sqrt (2 * Real.log (4 / δ) / n)} = Set.univ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro k hk
      rw [hrisk0 k hk, hemp0 s k hk, ← hc]
      simp [hrad0]
    rw [hset, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  · have hu : 0 ≤ c * Real.sqrt (2 * Real.log (4 / δ) / n) :=
      mul_nonneg hcpos.le (Real.sqrt_nonneg _)
    have hRmeas : Measurable fun s : Sample Z n => empRad F K s := measurable_empRad hKc hmeas
    have hRint : Integrable (fun s : Sample Z n => empRad F K s) (sampleLaw D n) :=
      integrable_of_abs_le hRmeas (abs_empRad_le hK' hbdd hn)
    have hev1 := mcdiarmid_event (D := D)
      (f := fun s : Sample Z n => sSup ((fun k => risk D F k - empRisk F s k) '' K))
      (measurable_gap hKc hmeas) (integrable_gap (D := D) hKc hK' hmeas hbdd hn)
      (fun j x y => abs_gap_sub_update_le hK' hmeas hbdd hn j x y) hcpos hn
      (a := 4) (by norm_num) hδ (by linarith)
    have hev2 := mcdiarmid_event (D := D) (f := fun s : Sample Z n => -empRad F K s)
      hRmeas.neg hRint.neg
      (fun j x y => by
        have h : -empRad F K x - -empRad F K (Function.update x j y)
            = -(empRad F K x - empRad F K (Function.update x j y)) := by ring
        rw [h, abs_neg]
        exact abs_empRad_sub_update_le hK' hbdd hn j x y) hcpos hn
      (a := 4) (by norm_num) hδ (by linarith)
    have h262 := integral_sup_risk_sub_empRisk_le_two_mul_integral_empRad (D := D) F K hKc hK'
      hmeas hbdd hn
    have hbound : sampleLaw D n
        ({s : Sample Z n | sSup ((fun k => risk D F k - empRisk F s k) '' K)
            ≤ (∫ s', sSup ((fun k => risk D F k - empRisk F s' k) '' K) ∂(sampleLaw D n))
              + c * Real.sqrt (2 * Real.log (4 / δ) / n)}
          ∩ {s : Sample Z n | -empRad F K s
            ≤ (∫ s', -empRad F K s' ∂(sampleLaw D n))
              + c * Real.sqrt (2 * Real.log (4 / δ) / n)})ᶜ ≤ ENNReal.ofReal δ := by
      rw [Set.compl_inter]
      refine (measure_union_le _ _).trans ?_
      refine (add_le_add hev1 hev2).trans ?_
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine (prob_ge_of_compl_le hδ.le hbound).trans (measure_mono fun s hs k hk => ?_)
    have h1 : risk D F k - empRisk F s k
        ≤ sSup ((fun k => risk D F k - empRisk F s k) '' K) :=
      le_sSup_image hk fun j hj => (abs_le.1 (abs_risk_sub_empRisk_le hmeas hbdd hn hj s)).2
    have h2 : sSup ((fun k => risk D F k - empRisk F s k) '' K)
        ≤ (∫ s', sSup ((fun k => risk D F k - empRisk F s' k) '' K) ∂(sampleLaw D n))
          + c * Real.sqrt (2 * Real.log (4 / δ) / n) := hs.1
    have h3 : -empRad F K s ≤ (∫ s', -empRad F K s' ∂(sampleLaw D n))
          + c * Real.sqrt (2 * Real.log (4 / δ) / n) := hs.2
    rw [integral_neg] at h3
    linarith


/-- **SSBD Theorem 26.5, part 3** (ERM excess risk, data-dependent): for an
ERM selector `A` and any fixed `kStar ∈ K`, with probability `≥ 1 − δ`,
`L_D(A(S)) − L_D(kStar) ≤ 2 R(F∘S) + 5c √(2 ln(8/δ)/n)`. -/
theorem rademacher_erm_excess {A : Sample Z n → ι} {kStar : ι} {δ : ℝ}
    -- LEAN-ONLY: countable family per the batch sup policy
    (hKc : K.Countable)
    (hK : K.Nonempty)
    (hmeas : ∀ k, Measurable (F k))
    (hbdd : ∀ k ∈ K, ∀ z, |F k z| ≤ c)
    -- USER-INPUT: `A` is an ERM selector over `K`; SSBD Thm 26.5(3)
    (hA : ∀ s, A s ∈ K ∧ ∀ k ∈ K, empRisk F s (A s) ≤ empRisk F s k)
    -- USER-INPUT: fixed competitor; SSBD Thm 26.5(3) ("for any h⋆")
    (hkStar : kStar ∈ K)
    (hn : 1 ≤ n)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s |
        risk D F (A s) - risk D F kStar ≤
          2 * empRad F K s + 5 * c * Real.sqrt (2 * Real.log (8 / δ) / n)} := by
  obtain ⟨k₀, hk₀⟩ := hK
  have hK' : K.Nonempty := ⟨k₀, hk₀⟩
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hbdd k₀ hk₀ (Classical.arbitrary Z))
  rcases eq_or_lt_of_le hc0 with hc | hcpos
  · have hF0 : ∀ k ∈ K, ∀ z, F k z = 0 := by
      intro k hk z
      have h := hbdd k hk z
      rw [← hc] at h
      exact abs_eq_zero.1 (le_antisymm h (abs_nonneg _))
    have hrisk0 : ∀ k ∈ K, risk D F k = 0 := fun k hk => by simp [risk, hF0 k hk]
    have hrad0 : ∀ s : Sample Z n, empRad F K s = 0 := by
      intro s
      rw [empRad_eq_signAvg]
      have hz : ∀ σ : Fin n → Bool,
          sSup ((fun k => ∑ i, signOf σ i * F k (s i)) '' K) = 0 := by
        intro σ
        have himg : (fun k => ∑ i, signOf σ i * F k (s i)) '' K = (fun _ : ι => (0 : ℝ)) '' K :=
          Set.image_congr fun k hk => by simp [hF0 k hk]
        rw [himg, Set.Nonempty.image_const hK', csSup_singleton]
      simp [hz]
    have hset : {s : Sample Z n | risk D F (A s) - risk D F kStar ≤
        2 * empRad F K s + 5 * c * Real.sqrt (2 * Real.log (8 / δ) / n)} = Set.univ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      rw [hrisk0 _ (hA s).1, hrisk0 _ hkStar, ← hc]
      simp [hrad0]
    rw [hset, measure_univ]
    exact ENNReal.ofReal_le_one.2 (by linarith)
  · have hv : 0 ≤ c * Real.sqrt (2 * Real.log (8 / δ) / n) :=
      mul_nonneg hcpos.le (Real.sqrt_nonneg _)
    have hRmeas : Measurable fun s : Sample Z n => empRad F K s := measurable_empRad hKc hmeas
    have hRint : Integrable (fun s : Sample Z n => empRad F K s) (sampleLaw D n) :=
      integrable_of_abs_le hRmeas (abs_empRad_le hK' hbdd hn)
    have hev1 := mcdiarmid_event (D := D)
      (f := fun s : Sample Z n => sSup ((fun k => risk D F k - empRisk F s k) '' K))
      (measurable_gap hKc hmeas) (integrable_gap (D := D) hKc hK' hmeas hbdd hn)
      (fun j x y => abs_gap_sub_update_le hK' hmeas hbdd hn j x y) hcpos hn
      (a := 8) (by norm_num) hδ (by linarith)
    have hev2 := mcdiarmid_event (D := D) (f := fun s : Sample Z n => -empRad F K s)
      hRmeas.neg hRint.neg
      (fun j x y => by
        have h : -empRad F K x - -empRad F K (Function.update x j y)
            = -(empRad F K x - empRad F K (Function.update x j y)) := by ring
        rw [h, abs_neg]
        exact abs_empRad_sub_update_le hK' hbdd hn j x y) hcpos hn
      (a := 8) (by norm_num) hδ (by linarith)
    have hev3 := mcdiarmid_event (D := D) (f := fun s : Sample Z n => empRisk F s kStar)
      (measurable_empRisk (hmeas kStar))
      (integrable_of_abs_le (measurable_empRisk (hmeas kStar)) (abs_empRisk_le hbdd hn hkStar))
      (fun j x y => abs_empRisk_sub_update_le hbdd hn hkStar j x y) hcpos hn
      (a := 8) (by norm_num) hδ (by linarith)
    have h262 := integral_sup_risk_sub_empRisk_le_two_mul_integral_empRad (D := D) F K hKc hK'
      hmeas hbdd hn
    have hbound : sampleLaw D n
        ({s : Sample Z n | sSup ((fun k => risk D F k - empRisk F s k) '' K)
            ≤ (∫ s', sSup ((fun k => risk D F k - empRisk F s' k) '' K) ∂(sampleLaw D n))
              + c * Real.sqrt (2 * Real.log (8 / δ) / n)}
          ∩ ({s : Sample Z n | -empRad F K s
            ≤ (∫ s', -empRad F K s' ∂(sampleLaw D n))
              + c * Real.sqrt (2 * Real.log (8 / δ) / n)}
          ∩ {s : Sample Z n | empRisk F s kStar
            ≤ (∫ s', empRisk F s' kStar ∂(sampleLaw D n))
              + c * Real.sqrt (2 * Real.log (8 / δ) / n)}))ᶜ ≤ ENNReal.ofReal δ := by
      rw [Set.compl_inter, Set.compl_inter]
      refine (measure_union_le _ _).trans ?_
      refine (add_le_add hev1 ((measure_union_le _ _).trans (add_le_add hev2 hev3))).trans ?_
      rw [← ENNReal.ofReal_add (by linarith) (by linarith),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    refine (prob_ge_of_compl_le hδ.le hbound).trans (measure_mono fun s hs => ?_)
    have h1 : risk D F (A s) - empRisk F s (A s)
        ≤ sSup ((fun k => risk D F k - empRisk F s k) '' K) :=
      le_sSup_image (hA s).1 fun j hj =>
        (abs_le.1 (abs_risk_sub_empRisk_le hmeas hbdd hn hj s)).2
    have h2 : sSup ((fun k => risk D F k - empRisk F s k) '' K)
        ≤ (∫ s', sSup ((fun k => risk D F k - empRisk F s' k) '' K) ∂(sampleLaw D n))
          + c * Real.sqrt (2 * Real.log (8 / δ) / n) := hs.1
    have h3 : -empRad F K s ≤ (∫ s', -empRad F K s' ∂(sampleLaw D n))
          + c * Real.sqrt (2 * Real.log (8 / δ) / n) := hs.2.1
    rw [integral_neg] at h3
    have h4 : empRisk F s kStar ≤ (∫ s', empRisk F s' kStar ∂(sampleLaw D n))
          + c * Real.sqrt (2 * Real.log (8 / δ) / n) := hs.2.2
    rw [integral_empRisk (integrable_of_abs_le (hmeas kStar) (hbdd kStar hkStar)) hn] at h4
    have h5 : empRisk F s (A s) ≤ empRisk F s kStar := (hA s).2 kStar hkStar
    simp only [Set.mem_setOf_eq]
    linarith


end StatLean.StatisticalLearning
