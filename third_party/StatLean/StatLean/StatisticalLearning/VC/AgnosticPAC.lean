module
public import StatLean.StatisticalLearning.VC.Bridge
public import StatLean.StatisticalLearning.Rademacher.Structural
public import StatLean.StatisticalLearning.Rademacher.Generalization
public import StatLean.StatisticalLearning.Core.ERM
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Finite VC dimension ⇒ agnostic PAC learnability (upper bound)

The agnostic upper bound of the Fundamental Theorem of learning theory
(SSBD Theorem 6.7 direction 6→1→2→3; Theorem 6.8 items 1–2 up to the book's
own `log(d/ε)` looseness), by the Massart route of SSBD §28.1:

* Sauer–Shelah bounds the loss-pattern count by `(en/d)^d` (`VC/Bridge`);
* Massart's lemma turns that into `R(𝓕∘S) ≤ √(2d log(en/d)/n)` pointwise;
* Theorem 26.5(1) on the loss family and its negation plus a union bound give,
  w.p. `≥ 1 − δ`: `∀h ∈ 𝓗, |L_D(h) − L_S(h)| ≤ √(8d log(en/d)/n) +
  √(2 log(4/δ)/n)` (SSBD §28.1 step 4);
* the log-inversion Lemma A.2 yields the explicit sufficient sample size
  `m ≥ (128d/ε²)·log(64d/ε²) + (8/ε²)(8d log(e/d) + 2 log(4/δ))`
  (SSBD p. 341, exact constants frozen).

**Reference.** SSBD §28.1; Lemma A.2. Transcriptions:
`notes/statistical_learning/book_statements/ch6-28.md`.

**Formalization notes.** `Countable 𝓗` is LEAN-ONLY per the batch sup policy
(the book quantifies over arbitrary classes); the `StandardBorelSpace X`
instance is inherited from the McDiarmid engine behind Theorem 26.5. The VC
hypothesis is `vcDim (setClassOf 𝓗) ≤ d` (set-class dictionary). This is the
`log(d/ε)`-loose form the book actually proves — the tight `d/ε²` of
Theorem 6.8 requires chaining and is out of scope (SSBD's own remark). -/

open MeasureTheory StatLean.ConcentrationInequalities
open scoped ENNReal BigOperators

namespace StatLean.StatisticalLearning

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X]
  {n : ℕ} {d : ℕ}

/-- **SSBD Lemma A.2** (log inversion): for `a ≥ 1`, `b > 0`, every
`x ≥ 4a log(2a) + 2b` satisfies `x ≥ a log x + b`. -/
theorem ge_log_bound_of_ge (a b x : ℝ)
    -- USER-INPUT: `a ≥ 1`; SSBD Lemma A.2
    (ha : 1 ≤ a)
    -- USER-INPUT: `b > 0`; SSBD Lemma A.2
    (hb : 0 < b)
    (hx : 4 * a * Real.log (2 * a) + 2 * b ≤ x) :
    a * Real.log x + b ≤ x := by
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
  have h2a : (1 : ℝ) ≤ 2 * a := by linarith
  have hlog2a : 0 ≤ Real.log (2 * a) := Real.log_nonneg h2a
  have hmul : 0 ≤ a * Real.log (2 * a) := mul_nonneg ha0.le hlog2a
  have hxpos : 0 < x := by nlinarith
  -- concavity of `log` at `2a`: `log x ≤ log (2a) + x/(2a) − 1`
  have hkey : Real.log (x / (2 * a)) ≤ x / (2 * a) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hsplit : Real.log (x / (2 * a)) = Real.log x - Real.log (2 * a) :=
    Real.log_div (ne_of_gt hxpos) (by positivity)
  have h1 : Real.log x ≤ Real.log (2 * a) + x / (2 * a) - 1 := by
    rw [hsplit] at hkey; linarith
  have hxa : a * (x / (2 * a)) = x / 2 := by field_simp
  have h2 : a * Real.log x ≤ a * Real.log (2 * a) + x / 2 - a := by
    have := mul_le_mul_of_nonneg_left h1 ha0.le
    nlinarith [this]
  linarith

/-- **Pointwise VC bound on the empirical Rademacher complexity**
(SSBD §28.1 step 2): if `vcDim (setClassOf 𝓗) ≤ d`, `1 ≤ d`, `d + 1 < n`,
then for every sample, `R(ℓ₀₁∘𝓗∘S) ≤ √(2 d log(en/d)/n)`. -/
theorem vc_empRad_le (𝓗 : Set (X → Bool)) (s : Sample (X × Bool) n)
    -- USER-INPUT: nonempty class; SSBD §28.1 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: VC dimension bound; SSBD Thm 6.8 / §28.1
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 side condition
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `d + 1 < n`; SSBD Lemma 6.10 (`m > d + 1`)
    (hn : d + 1 < n) :
    empRad zeroOneLoss 𝓗 s ≤
      Real.sqrt (2 * d * Real.log (Real.exp 1 * n / d) / n) := by
  classical
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hfin := finite_evalFamily_zeroOneLoss 𝓗 s
  have hAcoe : (↑hfin.toFinset : Set (Fin n → ℝ)) = evalFamily zeroOneLoss 𝓗 s :=
    hfin.coe_toFinset
  have hEne : (evalFamily zeroOneLoss 𝓗 s).Nonempty := h𝓗.image _
  have hAne : hfin.toFinset.Nonempty := (Set.Finite.toFinset_nonempty hfin).mpr hEne
  -- every loss vector lies in the Euclidean ball of radius `√n` around `0`
  have hr : ∀ a ∈ hfin.toFinset,
      Real.sqrt (∑ i, (a i - (0 : Fin n → ℝ) i) ^ 2) ≤ Real.sqrt n := by
    intro a ha
    have ha' : a ∈ evalFamily zeroOneLoss 𝓗 s := by
      rw [← hAcoe]; exact ha
    obtain ⟨h, -, rfl⟩ := ha'
    refine Real.sqrt_le_sqrt ?_
    have hone : ∀ i : Fin n,
        ((fun i => zeroOneLoss h (s i)) i - (0 : Fin n → ℝ) i) ^ 2 ≤ (1 : ℝ) := by
      intro i
      by_cases hp : h (s i).1 = (s i).2 <;> simp [zeroOneLoss, hp]
    calc ∑ i, ((fun i => zeroOneLoss h (s i)) i - (0 : Fin n → ℝ) i) ^ 2
        ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hone i
      _ = (n : ℝ) := by simp
  have hmassart := radComplexity_le_of_dist_center_le hfin.toFinset 0 hAne hr
  rw [hAcoe] at hmassart
  -- Sauer–Shelah bounds the loss-pattern count
  have hNcard : (evalFamily zeroOneLoss 𝓗 s).ncard = hfin.toFinset.card := by
    rw [← Set.ncard_coe_finset hfin.toFinset, hAcoe]
  have hN1 : 1 ≤ hfin.toFinset.card := Finset.card_pos.mpr hAne
  have hN1R : (1 : ℝ) ≤ (hfin.toFinset.card : ℝ) := by exact_mod_cast hN1
  have hpow : ((hfin.toFinset.card : ℕ) : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
    have := ncard_evalFamily_zeroOneLoss_le_pow 𝓗 s hd hd1 hn
    rwa [hNcard] at this
  have hlogN : Real.log (hfin.toFinset.card) ≤ d * Real.log (Real.exp 1 * n / d) := by
    calc Real.log (hfin.toFinset.card)
        ≤ Real.log ((Real.exp 1 * n / d) ^ d) :=
          Real.log_le_log (by linarith) hpow
      _ = d * Real.log (Real.exp 1 * n / d) := by rw [Real.log_pow]
  have hlogNnn : 0 ≤ Real.log (hfin.toFinset.card) := Real.log_nonneg hN1R
  -- the sqrt bookkeeping `√n · √(2 log N)/n = √(2 log N / n)`
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hnn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have halg : Real.sqrt n * Real.sqrt (2 * Real.log (hfin.toFinset.card)) / n
      = Real.sqrt (2 * Real.log (hfin.toFinset.card) / n) := by
    rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * Real.log (hfin.toFinset.card)) ((n : ℝ)),
      div_eq_div_iff (ne_of_gt hnR) (ne_of_gt hsqrtn)]
    calc Real.sqrt n * Real.sqrt (2 * Real.log (hfin.toFinset.card)) * Real.sqrt n
        = Real.sqrt (2 * Real.log (hfin.toFinset.card)) * (Real.sqrt n * Real.sqrt n) := by
          ring
      _ = Real.sqrt (2 * Real.log (hfin.toFinset.card)) * (n : ℝ) := by rw [hnn]
  rw [empRad]
  refine hmassart.trans ?_
  rw [halg]
  refine Real.sqrt_le_sqrt ?_
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hLnn : 0 ≤ Real.log (Real.exp 1 * n / d) := by
    have : Real.log (hfin.toFinset.card) ≤ (d : ℝ) * Real.log (Real.exp 1 * n / d) := hlogN
    nlinarith
  refine (div_le_div_iff_of_pos_right hnR).mpr ?_
  nlinarith

omit [StandardBorelSpace X] [Nonempty X] in
/-- The 0–1 loss is the indicator of the error set, hence measurable
(LEAN-ONLY regularity, via the `VC/Bridge` dictionary). -/
private theorem measurable_zeroOneLoss {h : X → Bool}
    (hmeas : MeasurableSet (errSet h)) : Measurable (zeroOneLoss h) := by
  have hfun : (zeroOneLoss h : X × Bool → ℝ) = (errSet h).indicator 1 := by
    funext p
    by_cases hp : h p.1 = p.2
    · have : p ∉ errSet h := by simpa [errSet] using hp
      simp [zeroOneLoss, hp, this]
    · have : p ∈ errSet h := by simpa [errSet] using hp
      simp [zeroOneLoss, hp, this]
  rw [hfun]
  exact measurable_const.indicator hmeas

omit [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] in
private theorem zeroOneLoss_nonneg (h : X → Bool) (p : X × Bool) :
    0 ≤ zeroOneLoss h p := by
  simp only [zeroOneLoss]; split <;> norm_num

omit [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] in
private theorem zeroOneLoss_le_one (h : X → Bool) (p : X × Bool) :
    zeroOneLoss h p ≤ 1 := by
  simp only [zeroOneLoss]; split <;> norm_num

omit [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] in
private theorem abs_zeroOneLoss_le_one (h : X → Bool) (p : X × Bool) :
    |zeroOneLoss h p| ≤ 1 :=
  abs_le.mpr ⟨by linarith [zeroOneLoss_nonneg h p], zeroOneLoss_le_one h p⟩

/-- A pointwise bound survives the Bochner junk value when the bound is
nonnegative (LEAN-ONLY: no integrability hypothesis is available for
`s ↦ R(𝓕∘S)`). -/
private theorem integral_le_of_forall_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ x, f x ≤ M) : ∫ x, f x ∂μ ≤ M := by
  by_cases hint : Integrable f μ
  · calc ∫ x, f x ∂μ ≤ ∫ _x, M ∂μ := integral_mono hint (integrable_const M) hf
      _ = M := by simp
  · rw [integral_undef hint]; exact hM

omit [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] in
/-- Re-indexing the evaluated family by the subtype of the class (LEAN-ONLY:
Theorem 26.5 asks for measurability of `F k` at *every* index, so the class is
consumed as `↥𝓗` with `K = univ`). -/
private theorem evalFamily_subtype (𝓗 : Set (X → Bool)) (s : Sample (X × Bool) n) :
    evalFamily (fun k : ↥𝓗 => zeroOneLoss (k : X → Bool)) Set.univ s
      = evalFamily zeroOneLoss 𝓗 s := by
  ext v
  constructor
  · rintro ⟨k, -, rfl⟩; exact ⟨(k : X → Bool), k.2, rfl⟩
  · rintro ⟨h, hh, rfl⟩; exact ⟨⟨h, hh⟩, Set.mem_univ _, rfl⟩

omit [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] in
/-- The evaluated family of the negated loss is the negation of the evaluated
family (LEAN-ONLY: feeds `radComplexity_neg` for the second, mirrored
application of Theorem 26.5). -/
private theorem evalFamily_neg_subtype (𝓗 : Set (X → Bool))
    (s : Sample (X × Bool) n) :
    evalFamily (fun (k : ↥𝓗) p => -zeroOneLoss (k : X → Bool) p) Set.univ s
      = (fun a => -a) '' evalFamily zeroOneLoss 𝓗 s := by
  ext v
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨fun i => zeroOneLoss (k : X → Bool) (s i), ⟨(k : X → Bool), k.2, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨⟨h, hh⟩, Set.mem_univ _, rfl⟩

/-- **VC uniform deviation, high probability** (SSBD §28.1 step 4): for a
countable class of VC dimension `≤ d`, with probability `≥ 1 − δ`,
simultaneously for every `h ∈ 𝓗`,
`|L_D(h) − L_S(h)| ≤ √(8 d log(en/d)/n) + √(2 log(4/δ)/n)`. -/
theorem vc_uniformDeviation_hp (𝓗 : Set (X → Bool))
    (D : Measure (X × Bool)) [IsProbabilityMeasure D] {δ : ℝ}
    -- LEAN-ONLY: countable class per the batch sup policy
    (hc : 𝓗.Countable)
    -- USER-INPUT: nonempty class; SSBD §28.1 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: measurable error sets; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, MeasurableSet (errSet h))
    -- USER-INPUT: VC dimension bound; SSBD Thm 6.8 / §28.1
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 side condition
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `d + 1 < n`; SSBD Lemma 6.10 (`m > d + 1`)
    (hn : d + 1 < n)
    -- USER-INPUT: `δ ∈ (0,1)`; SSBD §28.1
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw D n {s | ∀ h ∈ 𝓗,
        |empRisk zeroOneLoss s h - risk D zeroOneLoss h| ≤
          Real.sqrt (8 * d * Real.log (Real.exp 1 * n / d) / n) +
            Real.sqrt (2 * Real.log (4 / δ) / n)} := by
  classical
  haveI : Countable ↥𝓗 := hc.to_subtype
  haveI : Nonempty ↥𝓗 := h𝓗.to_subtype
  have hn1 : 1 ≤ n := by omega
  have hδ2 : 0 < δ / 2 := by linarith
  have hδ2' : δ / 2 < 1 := by linarith
  set M : ℝ := Real.sqrt (2 * d * Real.log (Real.exp 1 * n / d) / n) with hMdef
  set B : ℝ := Real.sqrt (8 * d * Real.log (Real.exp 1 * n / d) / n) +
      Real.sqrt (2 * Real.log (4 / δ) / n) with hBdef
  have hMnn : 0 ≤ M := Real.sqrt_nonneg _
  have hsqrt4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have h2M : 2 * M = Real.sqrt (8 * d * Real.log (Real.exp 1 * n / d) / n) := by
    rw [hMdef, show (8 : ℝ) * d * Real.log (Real.exp 1 * n / d) / n
        = 4 * (2 * d * Real.log (Real.exp 1 * n / d) / n) by ring,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), hsqrt4]
  have hδlog : (2 : ℝ) / (δ / 2) = 4 / δ := by
    rw [div_div_eq_mul_div]; norm_num
  -- the two one-sided events
  have hmeasSet : ∀ (c : ℝ) (g : (X → Bool) → ℝ)
      (G : (X → Bool) → Sample (X × Bool) n → ℝ),
      (∀ h ∈ 𝓗, Measurable (G h)) →
      MeasurableSet {s : Sample (X × Bool) n | ∀ h ∈ 𝓗, g h - G h s ≤ c} := by
    intro c g G hG
    have hEq : {s : Sample (X × Bool) n | ∀ h ∈ 𝓗, g h - G h s ≤ c}
        = ⋂ h ∈ 𝓗, {s : Sample (X × Bool) n | g h - G h s ≤ c} := by
      ext s; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hEq]
    exact MeasurableSet.biInter hc fun h hh =>
      measurableSet_le (measurable_const.sub (hG h hh)) measurable_const
  have hGmeas : ∀ h ∈ 𝓗,
      Measurable fun s : Sample (X × Bool) n => empRisk zeroOneLoss s h :=
    fun h hh => measurable_empRisk (measurable_zeroOneLoss (hmeas h hh))
  have hE1meas : MeasurableSet {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
      risk D zeroOneLoss h - empRisk zeroOneLoss s h ≤ B} :=
    hmeasSet B (fun h => risk D zeroOneLoss h)
      (fun h s => empRisk zeroOneLoss s h) hGmeas
  have hE2meas : MeasurableSet {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
      -risk D zeroOneLoss h - -empRisk zeroOneLoss s h ≤ B} :=
    hmeasSet B (fun h => -risk D zeroOneLoss h)
      (fun h s => -empRisk zeroOneLoss s h)
      (fun h hh => (hGmeas h hh).neg)
  -- the empirical Rademacher complexity is bounded by `M` on every sample
  have hradF : ∀ s' : Sample (X × Bool) n,
      empRad (fun k : ↥𝓗 => zeroOneLoss (k : X → Bool)) Set.univ s' ≤ M := by
    intro s'
    rw [empRad, evalFamily_subtype, ← empRad]
    exact vc_empRad_le 𝓗 s' h𝓗 hd hd1 hn
  have hradG : ∀ s' : Sample (X × Bool) n,
      empRad (fun (k : ↥𝓗) p => -zeroOneLoss (k : X → Bool) p) Set.univ s' ≤ M := by
    intro s'
    rw [empRad, evalFamily_neg_subtype, radComplexity_neg, ← empRad]
    exact vc_empRad_le 𝓗 s' h𝓗 hd hd1 hn
  have hintF : ∫ s', empRad (fun k : ↥𝓗 => zeroOneLoss (k : X → Bool)) Set.univ s'
      ∂(sampleLaw D n) ≤ M := integral_le_of_forall_le _ hMnn hradF
  have hintG : ∫ s', empRad (fun (k : ↥𝓗) p => -zeroOneLoss (k : X → Bool) p)
      Set.univ s' ∂(sampleLaw D n) ≤ M := integral_le_of_forall_le _ hMnn hradG
  -- Theorem 26.5(1) on the loss family
  have hE1 : ENNReal.ofReal (1 - δ / 2) ≤
      sampleLaw D n {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
        risk D zeroOneLoss h - empRisk zeroOneLoss s h ≤ B} := by
    refine le_trans (rademacher_generalization_expected
      (D := D) (n := n) (K := (Set.univ : Set ↥𝓗)) (c := 1)
      (F := fun k : ↥𝓗 => zeroOneLoss (k : X → Bool))
      Set.countable_univ Set.univ_nonempty
      (fun k => measurable_zeroOneLoss (hmeas _ k.2))
      (fun k _ z => abs_zeroOneLoss_le_one _ z) hn1 hδ2 hδ2') (measure_mono ?_)
    intro s hs h hh
    have hk := hs ⟨h, hh⟩ (Set.mem_univ _)
    have hbnd : 2 * (∫ s', empRad (fun k : ↥𝓗 => zeroOneLoss (k : X → Bool))
          Set.univ s' ∂(sampleLaw D n)) +
        1 * Real.sqrt (2 * Real.log (2 / (δ / 2)) / n) ≤ B := by
      rw [hδlog, hBdef, ← h2M]
      have : (0:ℝ) ≤ Real.sqrt (2 * Real.log (4 / δ) / n) := Real.sqrt_nonneg _
      linarith
    exact le_trans hk hbnd
  -- Theorem 26.5(1) on the negated loss family
  have hE2 : ENNReal.ofReal (1 - δ / 2) ≤
      sampleLaw D n {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
        -risk D zeroOneLoss h - -empRisk zeroOneLoss s h ≤ B} := by
    refine le_trans (rademacher_generalization_expected
      (D := D) (n := n) (K := (Set.univ : Set ↥𝓗)) (c := 1)
      (F := fun (k : ↥𝓗) p => -zeroOneLoss (k : X → Bool) p)
      Set.countable_univ Set.univ_nonempty
      (fun k => (measurable_zeroOneLoss (hmeas _ k.2)).neg)
      (fun k _ z => by
        rw [abs_neg]; exact abs_zeroOneLoss_le_one _ z) hn1 hδ2 hδ2') (measure_mono ?_)
    intro s hs h hh
    have hk := hs ⟨h, hh⟩ (Set.mem_univ _)
    have hrisk : risk D (fun (k : ↥𝓗) p => -zeroOneLoss (k : X → Bool) p) ⟨h, hh⟩
        = -risk D zeroOneLoss h := by
      simp [risk, integral_neg]
    have hemp : empRisk (fun (k : ↥𝓗) p => -zeroOneLoss (k : X → Bool) p) s ⟨h, hh⟩
        = -empRisk zeroOneLoss s h := by
      simp [empRisk, Finset.sum_neg_distrib]
    rw [hrisk, hemp] at hk
    refine le_trans hk ?_
    rw [hδlog, hBdef, ← h2M]
    have : (0:ℝ) ≤ Real.sqrt (2 * Real.log (4 / δ) / n) := Real.sqrt_nonneg _
    linarith
  -- union bound on the complements
  have hcomplbnd : ∀ (E : Set (Sample (X × Bool) n)), MeasurableSet E →
      ENNReal.ofReal (1 - δ / 2) ≤ sampleLaw D n E →
      sampleLaw D n Eᶜ ≤ ENNReal.ofReal (δ / 2) := by
    intro E hEm hE
    rw [prob_compl_eq_one_sub hEm]
    calc (1 : ℝ≥0∞) - sampleLaw D n E ≤ 1 - ENNReal.ofReal (1 - δ / 2) :=
        tsub_le_tsub_left hE 1
      _ = ENNReal.ofReal (δ / 2) := by
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_sub _ (by linarith : (0:ℝ) ≤ 1 - δ / 2)]
        norm_num
  have hc1 := hcomplbnd _ hE1meas hE1
  have hc2 := hcomplbnd _ hE2meas hE2
  have hcompl : sampleLaw D n
      ({s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
          risk D zeroOneLoss h - empRisk zeroOneLoss s h ≤ B} ∩
        {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
          -risk D zeroOneLoss h - -empRisk zeroOneLoss s h ≤ B})ᶜ
      ≤ ENNReal.ofReal δ := by
    rw [Set.compl_inter]
    refine (measure_union_le _ _).trans ?_
    calc sampleLaw D n {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
            risk D zeroOneLoss h - empRisk zeroOneLoss s h ≤ B}ᶜ +
          sampleLaw D n {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
            -risk D zeroOneLoss h - -empRisk zeroOneLoss s h ≤ B}ᶜ
        ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hc1 hc2
      _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  have hinter : ENNReal.ofReal (1 - δ) ≤ sampleLaw D n
      ({s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
          risk D zeroOneLoss h - empRisk zeroOneLoss s h ≤ B} ∩
        {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
          -risk D zeroOneLoss h - -empRisk zeroOneLoss s h ≤ B}) := by
    rw [prob_compl_eq_one_sub (hE1meas.inter hE2meas)] at hcompl
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ + sampleLaw D n
        ({s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
            risk D zeroOneLoss h - empRisk zeroOneLoss s h ≤ B} ∩
          {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
            -risk D zeroOneLoss h - -empRisk zeroOneLoss s h ≤ B}) :=
      tsub_le_iff_right.mp hcompl
    calc ENNReal.ofReal (1 - δ) = 1 - ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hδ.le]
      _ ≤ (ENNReal.ofReal δ + sampleLaw D n
            ({s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
                risk D zeroOneLoss h - empRisk zeroOneLoss s h ≤ B} ∩
              {s : Sample (X × Bool) n | ∀ h ∈ 𝓗,
                -risk D zeroOneLoss h - -empRisk zeroOneLoss s h ≤ B})) -
            ENNReal.ofReal δ := tsub_le_tsub_right h1 _
      _ = _ := by rw [ENNReal.add_sub_cancel_left ENNReal.ofReal_ne_top]
  refine hinter.trans (measure_mono ?_)
  rintro s ⟨hs1, hs2⟩ h hh
  have h1 := hs1 h hh
  have h2 := hs2 h hh
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The sample-size arithmetic behind SSBD §28.1 step 5, in abstract form:
with `a = 64d/ε²`, `e1 = log(e/d)`, `W = (8/ε²) log(4/δ)` and `x = m`, the
book's `m ≥ 2a log a + a·e1 + 2W` forces `(√P + √W)² ≤ m` for the *halved*
target `P = (a/2)·log(em/d)` — i.e. the `ε/2`-representativeness that
Lemma 4.2 consumes, not merely `ε`-representativeness. The two regimes
`m ≤ a²` (where `2P ≤ 2a log a + a·e1`) and `m > a²` (where `m` itself pays
for the logarithm) are separated because no single Cauchy–Schwarz split
covers both. -/
private theorem sqrt_add_sq_le_of_ge {a e1 W x : ℝ}
    (ha : 64 ≤ a) (he1 : e1 ≤ 1) (hW : 0 ≤ W) (hx0 : 0 < x)
    (hL : 0 ≤ e1 + Real.log x)
    (hnn : 0 ≤ 2 * a * Real.log a + a * e1)
    (hx : 2 * a * Real.log a + a * e1 + 2 * W ≤ x) :
    (Real.sqrt ((a / 2) * (e1 + Real.log x)) + Real.sqrt W) ^ 2 ≤ x := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hPnn : 0 ≤ (a / 2) * (e1 + Real.log x) := by positivity
  have hsqP : Real.sqrt ((a / 2) * (e1 + Real.log x)) ^ 2
      = (a / 2) * (e1 + Real.log x) := Real.sq_sqrt hPnn
  have hsqW : Real.sqrt W ^ 2 = W := Real.sq_sqrt hW
  have hexp : (Real.sqrt ((a / 2) * (e1 + Real.log x)) + Real.sqrt W) ^ 2
      = (a / 2) * (e1 + Real.log x) +
        2 * (Real.sqrt ((a / 2) * (e1 + Real.log x)) * Real.sqrt W) + W := by
    have hring : (Real.sqrt ((a / 2) * (e1 + Real.log x)) + Real.sqrt W) ^ 2
        = Real.sqrt ((a / 2) * (e1 + Real.log x)) ^ 2 +
          2 * (Real.sqrt ((a / 2) * (e1 + Real.log x)) * Real.sqrt W) +
          Real.sqrt W ^ 2 := by ring
    rw [hring, hsqP, hsqW]
  rw [hexp]
  rcases le_or_gt x (a ^ 2) with hcase | hcase
  · -- low regime: the `κ = 1` split, `2P ≤ 2a log a + a·e1`
    have hlogx : Real.log x ≤ 2 * Real.log a := by
      have h1 : Real.log x ≤ Real.log (a ^ 2) := Real.log_le_log hx0 hcase
      have h2 : Real.log (a ^ 2) = 2 * Real.log a := by
        rw [Real.log_pow]; norm_num
      rw [h2] at h1; exact h1
    have hmul := mul_le_mul_of_nonneg_left hlogx ha0.le
    have h2P : 2 * ((a / 2) * (e1 + Real.log x)) ≤ 2 * a * Real.log a + a * e1 := by
      nlinarith [hmul]
    have hAM : 2 * (Real.sqrt ((a / 2) * (e1 + Real.log x)) * Real.sqrt W)
        ≤ (a / 2) * (e1 + Real.log x) + W := by
      nlinarith [sq_nonneg (Real.sqrt ((a / 2) * (e1 + Real.log x)) - Real.sqrt W),
        hsqP, hsqW]
    linarith
  · -- high regime: `x > a²`, the `κ = 1/3` split
    have hAM : 2 * (Real.sqrt ((a / 2) * (e1 + Real.log x)) * Real.sqrt W)
        ≤ 3 * ((a / 2) * (e1 + Real.log x)) + W / 3 := by
      nlinarith [sq_nonneg (3 * Real.sqrt ((a / 2) * (e1 + Real.log x)) - Real.sqrt W),
        hsqP, hsqW]
    -- `12 log a ≤ (29/32) a` for `a ≥ 64`
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hlog64 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; norm_num
    have hloga : Real.log a ≤ a / 64 + Real.log 64 - 1 := by
      have h1 : Real.log (a / 64) ≤ a / 64 - 1 :=
        Real.log_le_sub_one_of_pos (by linarith)
      rw [Real.log_div (ne_of_gt ha0) (by norm_num : (64 : ℝ) ≠ 0)] at h1
      linarith
    have h12 : 12 * Real.log a ≤ (29 / 32) * a := by linarith
    -- `4P ≤ x/3`
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    have hlogdiv : Real.log (x / a ^ 2) ≤ x / a ^ 2 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplitx : Real.log (x / a ^ 2) = Real.log x - 2 * Real.log a := by
      rw [Real.log_div (ne_of_gt hx0) (ne_of_gt ha2), Real.log_pow]; norm_num
    have hlogx : Real.log x ≤ x / a ^ 2 - 1 + 2 * Real.log a := by
      rw [hsplitx] at hlogdiv; linarith
    have hstep : 4 * ((a / 2) * (e1 + Real.log x))
        ≤ 2 * x / a + 4 * a * Real.log a := by
      have hmul := mul_le_mul_of_nonneg_left
        (show e1 + Real.log x ≤ x / a ^ 2 + 2 * Real.log a by linarith)
        (by linarith : (0 : ℝ) ≤ 2 * a)
      calc 4 * ((a / 2) * (e1 + Real.log x)) = 2 * a * (e1 + Real.log x) := by ring
        _ ≤ 2 * a * (x / a ^ 2 + 2 * Real.log a) := hmul
        _ = 2 * x / a + 4 * a * Real.log a := by field_simp; ring
    have hxa : 2 * x / a ≤ x / 32 := by
      have hstep2 : 2 * x / a ≤ 2 * x / 64 := by gcongr
      linarith
    have he2 : 4 * a * Real.log a ≤ (29 / 96) * a ^ 2 := by nlinarith [h12]
    have he3 : (29 / 96) * a ^ 2 ≤ (29 / 96) * x := by nlinarith
    have h4P : 4 * ((a / 2) * (e1 + Real.log x)) ≤ x / 3 := by linarith
    linarith

/-- **Finite VC dimension ⇒ agnostic PAC learnability by ERM**
(SSBD Theorem 6.7, 6→3; §28.1 headline with the explicit sample size of
p. 341): any ERM selector agnostically PAC-learns a countable class of VC
dimension `≤ d` with sample complexity
`m(ε,δ) = ⌈(128d/ε²) log(64d/ε²) + (8/ε²)(8d log(e/d) + 2 log(4/δ))⌉ + d + 2`
(the `+ d + 2` enforces Sauer's `m > d + 1` side condition; book constants
otherwise frozen). -/
theorem vc_isAgnosticPACLearnerWith (𝓗 : Set (X → Bool))
    {A : ∀ m : ℕ, Sample (X × Bool) m → (X → Bool)}
    -- LEAN-ONLY: countable class per the batch sup policy
    (hc : 𝓗.Countable)
    -- USER-INPUT: nonempty class; SSBD §28.1 (implicit)
    (h𝓗 : 𝓗.Nonempty)
    -- USER-INPUT: measurable error sets; SSBD Remark 3.1
    (hmeas : ∀ h ∈ 𝓗, MeasurableSet (errSet h))
    -- USER-INPUT: VC dimension bound; SSBD Thm 6.8
    (hd : vcDim (setClassOf 𝓗) ≤ (d : ℕ∞))
    -- USER-INPUT: `1 ≤ d`; SSBD Lemma 6.10 side condition
    (hd1 : 1 ≤ d)
    -- USER-INPUT: `A` is an ERM selector; SSBD §28.1 ("applying the ERM rule")
    (hA : ∀ (m : ℕ) (s : Sample (X × Bool) m),
      IsERM 𝓗 zeroOneLoss s (A m s)) :
    IsAgnosticPACLearnerWith 𝓗 zeroOneLoss A
      (fun ε δ =>
        ⌈128 * d / ε ^ 2 * Real.log (64 * d / ε ^ 2) +
            8 / ε ^ 2 * (8 * d * Real.log (Real.exp 1 / d) +
              2 * Real.log (4 / δ))⌉₊ + d + 2) := by
  intro D hD ε δ hε hδ hδ1 m hm
  dsimp only at hm
  haveI : IsProbabilityMeasure D := hD
  have hbddset : BddBelow (risk D zeroOneLoss '' 𝓗) := by
    refine ⟨0, ?_⟩
    rintro r ⟨h, -, rfl⟩
    exact risk_nonneg fun z => zeroOneLoss_nonneg h z
  rcases le_or_gt ε 1 with hε1 | hε1
  · -- the substantive regime `ε ≤ 1`
    have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hdm : d + 1 < m := by omega
    have hm0 : 0 < m := by omega
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    have hdmR : (d : ℝ) < (m : ℝ) := by exact_mod_cast (show d < m by omega)
    have hε2 : (0 : ℝ) < ε ^ 2 := by positivity
    have hε2le : ε ^ 2 ≤ 1 := by nlinarith
    have hmK : 128 * (d : ℝ) / ε ^ 2 * Real.log (64 * (d : ℝ) / ε ^ 2) +
        8 / ε ^ 2 * (8 * (d : ℝ) * Real.log (Real.exp 1 / (d : ℝ)) +
          2 * Real.log (4 / δ)) ≤ (m : ℝ) := by
      refine le_trans (Nat.le_ceil _) ?_
      have h1 : ⌈128 * (d : ℝ) / ε ^ 2 * Real.log (64 * (d : ℝ) / ε ^ 2) +
          8 / ε ^ 2 * (8 * (d : ℝ) * Real.log (Real.exp 1 / (d : ℝ)) +
            2 * Real.log (4 / δ))⌉₊ ≤ m := by omega
      exact_mod_cast h1
    set a : ℝ := 64 * d / ε ^ 2 with hadef
    set e1 : ℝ := Real.log (Real.exp 1 / d) with he1def
    set W : ℝ := 8 / ε ^ 2 * Real.log (4 / δ) with hWdef
    have ha : 64 ≤ a := by
      rw [hadef, le_div_iff₀ hε2]
      nlinarith
    have ha0 : (0 : ℝ) < a := by linarith
    have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1R
    have he1eq : e1 = 1 - Real.log d := by
      rw [he1def, Real.log_div (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
    have he1 : e1 ≤ 1 := by rw [he1eq]; linarith
    have hlog4δ : 0 < Real.log (4 / δ) :=
      Real.log_pos (by rw [lt_div_iff₀ hδ]; linarith)
    have hW : 0 ≤ W := by
      rw [hWdef]; exact mul_nonneg (by positivity) hlog4δ.le
    have hlogdm : Real.log d ≤ Real.log m := Real.log_le_log (by linarith) hdmR.le
    have hL : 0 ≤ e1 + Real.log m := by rw [he1eq]; linarith
    have hda : (d : ℝ) ≤ a := by
      rw [hadef, le_div_iff₀ hε2]; nlinarith
    have hlogda : Real.log d ≤ Real.log a := Real.log_le_log (by linarith) hda
    have hnn : 0 ≤ 2 * a * Real.log a + a * e1 := by
      rw [he1eq]; nlinarith
    -- the frozen sample size is exactly `2a log a + a·log(e/d) + 2W`
    have hKeq : 2 * a * Real.log a + a * e1 + 2 * W =
        128 * (d : ℝ) / ε ^ 2 * Real.log a +
          8 / ε ^ 2 * (8 * (d : ℝ) * e1 + 2 * Real.log (4 / δ)) := by
      rw [hadef, hWdef]; ring
    have hx : 2 * a * Real.log a + a * e1 + 2 * W ≤ (m : ℝ) := by
      rw [hKeq]; exact hmK
    have hkey := sqrt_add_sq_le_of_ge (a := a) (e1 := e1) (W := W) (x := (m : ℝ))
      ha he1 hW hmR hL hnn hx
    have hPnn : 0 ≤ (a / 2) * (e1 + Real.log m) := by positivity
    have hPW : Real.sqrt ((a / 2) * (e1 + Real.log m)) + Real.sqrt W
        ≤ Real.sqrt m := by
      calc Real.sqrt ((a / 2) * (e1 + Real.log m)) + Real.sqrt W
          = Real.sqrt ((Real.sqrt ((a / 2) * (e1 + Real.log m)) + Real.sqrt W) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt m := Real.sqrt_le_sqrt hkey
    have hsqrtm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
    have hLm : Real.log (Real.exp 1 * m / d) = e1 + Real.log m := by
      rw [he1def, show Real.exp 1 * (m : ℝ) / d = (Real.exp 1 / d) * m by ring,
        Real.log_mul (by positivity) (ne_of_gt hmR)]
    have hu : 8 * (d : ℝ) * Real.log (Real.exp 1 * m / d) / m
        = (ε / 2) ^ 2 * (((a / 2) * (e1 + Real.log m)) / m) := by
      rw [hLm, hadef]; field_simp; ring
    have hv : 2 * Real.log (4 / δ) / (m : ℝ) = (ε / 2) ^ 2 * (W / m) := by
      rw [hWdef]; field_simp; ring
    have hfinal : Real.sqrt (8 * (d : ℝ) * Real.log (Real.exp 1 * m / d) / m)
        + Real.sqrt (2 * Real.log (4 / δ) / m) ≤ ε / 2 := by
      rw [hu, hv, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (ε / 2) ^ 2),
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ (ε / 2) ^ 2),
        Real.sqrt_sq (by linarith : (0:ℝ) ≤ ε / 2),
        Real.sqrt_div hPnn ((m : ℝ)), Real.sqrt_div hW ((m : ℝ))]
      have hratio : (Real.sqrt ((a / 2) * (e1 + Real.log m)) + Real.sqrt W)
          / Real.sqrt m ≤ 1 := (div_le_one hsqrtm).mpr hPW
      have hsplit : ε / 2 * (Real.sqrt ((a / 2) * (e1 + Real.log m)) / Real.sqrt m)
            + ε / 2 * (Real.sqrt W / Real.sqrt m)
          = ε / 2 * ((Real.sqrt ((a / 2) * (e1 + Real.log m)) + Real.sqrt W)
            / Real.sqrt m) := by ring
      rw [hsplit]
      nlinarith [hratio, hε]
    have hdev := vc_uniformDeviation_hp (n := m) 𝓗 D hc h𝓗 hmeas hd hd1 hdm hδ hδ1
    refine hdev.trans (measure_mono ?_)
    intro s hs
    have hrep : UniformDeviationLE D 𝓗 zeroOneLoss s (ε / 2) := fun h hh =>
      (hs h hh).trans hfinal
    exact risk_le_bestRisk_add_of_isERM_of_uniformDeviation hrep (hA m s) hbddset
  · -- `ε > 1`: the 0–1 risk never exceeds `1 ≤ bestRisk + ε`
    have hbestnn : 0 ≤ bestRisk D 𝓗 zeroOneLoss := by
      obtain ⟨h0, hh0⟩ := h𝓗
      refine le_csInf ⟨risk D zeroOneLoss h0, ⟨h0, hh0, rfl⟩⟩ ?_
      rintro r ⟨h, -, rfl⟩
      exact risk_nonneg fun z => zeroOneLoss_nonneg h z
    have hall : {s : Sample (X × Bool) m |
        risk D zeroOneLoss (A m s) ≤ bestRisk D 𝓗 zeroOneLoss + ε} = Set.univ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hmem := (hA m s).1
      have h1 : risk D zeroOneLoss (A m s) ≤ 1 :=
        (risk_mem_Icc (fun z => ⟨zeroOneLoss_nonneg _ z, zeroOneLoss_le_one _ z⟩)
          (measurable_zeroOneLoss (hmeas _ hmem))).2
      linarith
    rw [hall, measure_univ]
    exact ENNReal.ofReal_le_one.mpr (by linarith)

end StatLean.StatisticalLearning
