module
public import StatLean.ConcentrationInequalities.VC.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.SubGaussian.Bounded
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Dimension reduction: ε-separation survives empirical projection

Let $S_1, \dots, S_N$ ($N = |\mathcal{F}| \ge 2$) be measurable sets that are
$\varepsilon$-separated in $L^2(\mu)$ in the squared sense
$\mu(S \bigtriangleup T) > \varepsilon^2$ for all pairs $S \ne T$, and let
$X_1, X_2, \dots$ be i.i.d. with law $\mu$. If
$n \ge 100\,\varepsilon^{-4}\log|\mathcal{F}|$, then with probability at
least $0.99$ the family stays $\varepsilon/2$-separated in $L^2(\mu_n)$:
$$ \mathbb{P}\Bigl\{\exists\, S \ne T \in \mathcal{F} :
   \mu_n(S \bigtriangleup T) \le \varepsilon^2/4 \Bigr\} \;\le\; 1/100. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.5, Lemma 8.3.14 (stated in squared-distance
form: net radius `ε` ⟺ measure ≤ `ε²`, separation ⟺ `> ε²`).

**Proof formalization notes.** Per-pair concentration reuses the existing
`hoeffding` (ℕ-indexed, `Finset.range n`, `μ.real` conclusion) applied
one-sided to the *negated* indicators
`Y i ξ := −(S ∆ T).indicator 1 (X i ξ)`: each `Y i` takes values in
`[−1, 0]`, hence is `IsSubGaussian` with proxy `(1/2)²` via
`isSubGaussian_of_mem_Icc`, giving
`P{empFrac ≤ μ.real(S∆T) − t} ≤ exp(−2·n·t²)`. Applying it at the deviation
`t = (3/4)ε²` (from separation `> ε²` down to threshold `ε²/4`) gives
`exp(−(9/8)·n·ε⁴)` per ordered pair; the union bound over at most `|F|²`
ordered pairs plus the numeric fact `100·log 2 ≥ 2·log|F|/log|F| …` slack
(`log 100 ≤ 5`, one-sided Hoeffding needs only `≈ 8·ε⁻⁴·log|F|` samples, so
the book's sample-size constant `C = 100` is provable with large slack)
closes the bound `≤ 1/100`. Union-bound measurability: only the per-pair
Hoeffding event needs to be measurable, which it is since `S, T` are.
Identical distribution is encoded as the map equality `P.map (X i) = μ`
(the pin's `ProbabilityTheory.HasLaw` is not used, per the batch's frozen
interface). Constants: failure probability `1/100` and sample-size constant
`100` are the book's. Named-sorry fallback of this work item:
`dimension_reduction` (keep `empFrac_symmDiff_concentration_pair` — the
Hoeffding reuse — real; sorry only the union-bound + numeric assembly).

**Bibliographic comments.** The dimension-reduction step is the modern
streamlining (due to R. Vershynin) of the random-projection idea in
the covering-number bound of R. M. Dudley, "Central limit theorems for
empirical measures," *Ann. Probab.* 6 (1978), 899–929.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Numeric helper: `log 100 ≤ 5` (LEAN-ONLY: `exp 5 ≥ 100` via
`Real.exp_one_gt_d9`). -/
private lemma log_hundred_le_five : Real.log 100 ≤ 5 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have hmono : (2.7182818283 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 5
  have he : (Real.exp 1) ^ 5 = Real.exp 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  nlinarith [hmono, he]

/-- Per-pair one-sided concentration of the empirical measure of a symmetric
difference (HDP §8.3.5, Lemma 8.3.14 proof step): the empirical fraction of
`S ∆ T` undershoots its mean by `t` with probability at most
`exp(−2·n·t²)` — the existing `hoeffding` applied to the negated indicators,
sub-Gaussian with proxy `(1/2)²` via `isSubGaussian_of_mem_Icc`. -/
lemma empFrac_symmDiff_concentration_pair {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; needed to lift
    -- independence through the indicator composition, no scope change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.5,
    -- Lemma 8.3.14 ("i.i.d.").
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.5, Lemma 8.3.14 (stated as a
    -- map equality; `ProbabilityTheory.HasLaw` not used per batch interface).
    (hlaw : ∀ i, P.map (X i) = μ)
    {S T : Set Ω}
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hS : MeasurableSet S) (hT : MeasurableSet T)
    {t : ℝ}
    -- USER-INPUT: positive deviation level; HDP §8.3.5, Lemma 8.3.14 proof.
    (ht : 0 < t)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.3.5 (implicit).
    (hn : 1 ≤ n) :
    P {ξ | empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ μ.real (S ∆ T) - t}
      ≤ ENNReal.ofReal (Real.exp (-2 * n * t ^ 2)) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hWmeas : MeasurableSet (S ∆ T) := hS.symmDiff hT
  -- The negated indicator `g` and the data-composed family `Y`.
  set g : Ω → ℝ := fun z => -((S ∆ T).indicator (fun _ => (1 : ℝ)) z) with hgdef
  have hgmeas : Measurable g := (measurable_const.indicator hWmeas).neg
  set Y : ℕ → Ξ → ℝ := fun i ξ => g (X i ξ) with hYdef
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hgmeas.comp (hXmeas i)
  -- Independence of `Y` from independence of `X`.
  have hY_indep : iIndepFun Y P := by
    have := hindep.comp (fun _ : ℕ => g) (fun _ => hgmeas)
    exact this
  -- Each `Y i` lives in `[-1, 0]`, hence is sub-Gaussian with proxy `(1/2)²`.
  set c2 : ℝ≥0 := (‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 with hc2def
  have hc2 : ((c2 : ℝ≥0) : ℝ) = 1 / 4 := by
    rw [hc2def]; push_cast; rw [Real.norm_eq_abs]; norm_num
  have hY_subG : ∀ i, i < n → IsSubGaussian (Y i) c2 P := by
    intro i _
    apply isSubGaussian_of_mem_Icc (a := (-1 : ℝ)) (b := (0 : ℝ)) (hYmeas i).aemeasurable
    filter_upwards with ξ
    rw [Set.mem_Icc]
    have hind0 : 0 ≤ (S ∆ T).indicator (fun _ => (1 : ℝ)) (X i ξ) :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    have hind1 : (S ∆ T).indicator (fun _ => (1 : ℝ)) (X i ξ) ≤ 1 := by
      rw [Set.indicator_apply]; split_ifs <;> norm_num
    simp only [hYdef, hgdef]
    constructor <;> linarith
  -- Mean of each `Y i` is `-μ.real (S ∆ T)`.
  have hEint : ∀ i, ∫ ξ, Y i ξ ∂P = -(μ.real (S ∆ T)) := by
    intro i
    have hmap : ∫ z, g z ∂(P.map (X i)) = ∫ ξ, g (X i ξ) ∂P :=
      integral_map (hXmeas i).aemeasurable hgmeas.aestronglyMeasurable
    rw [hlaw i] at hmap
    have hgint : ∫ z, g z ∂μ = -(μ.real (S ∆ T)) := by
      simp only [hgdef]
      rw [integral_neg, integral_indicator_const (1 : ℝ) hWmeas, smul_eq_mul, mul_one]
    simp only [hYdef]
    rw [← hmap, hgint]
  -- Rewrite the Hoeffding sum into `n·μ.real − (empirical count)`.
  have hstep : ∀ ξ, (∑ i ∈ Finset.range n, (Y i ξ - ∫ y, Y i y ∂P))
      = (n : ℝ) * μ.real (S ∆ T)
        - ∑ i ∈ Finset.range n, (S ∆ T).indicator (fun _ => (1 : ℝ)) (X i ξ) := by
    intro ξ
    have hterm : ∀ i, Y i ξ - ∫ y, Y i y ∂P
        = μ.real (S ∆ T) - (S ∆ T).indicator (fun _ => (1 : ℝ)) (X i ξ) := by
      intro i
      rw [hEint i]
      simp only [hYdef, hgdef]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- The two events coincide.
  have hset : {ξ | empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ μ.real (S ∆ T) - t}
      = {ξ | (n : ℝ) * t ≤ ∑ i ∈ Finset.range n, (Y i ξ - ∫ y, Y i y ∂P)} := by
    ext ξ
    simp only [Set.mem_setOf_eq, empFrac]
    rw [hstep ξ,
      Fin.sum_univ_eq_sum_range
        (fun i => (S ∆ T).indicator (fun _ => (1 : ℝ)) (X i ξ)) n,
      inv_mul_eq_div, div_le_iff₀ hn0]
    constructor <;> intro h <;> nlinarith
  -- Apply Hoeffding and reconcile the exponent, then push to `ℝ≥0∞`.
  have hmain := hoeffding (μ := P) hYmeas hY_indep hY_subG hn ht
  rw [← hset] at hmain
  have hexp : -(n : ℝ) * t ^ 2 / (2 * (c2 : ℝ)) = -2 * (n : ℝ) * t ^ 2 := by
    rw [hc2]; ring
  rw [hexp] at hmain
  have hfin : P {ξ | empFrac (fun i : Fin n => X i ξ) (S ∆ T)
      ≤ μ.real (S ∆ T) - t} ≠ ⊤ := measure_ne_top P _
  calc P {ξ | empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ μ.real (S ∆ T) - t}
      = ENNReal.ofReal (P {ξ | empFrac (fun i : Fin n => X i ξ) (S ∆ T)
          ≤ μ.real (S ∆ T) - t}).toReal := (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (Real.exp (-2 * (n : ℝ) * t ^ 2)) :=
        ENNReal.ofReal_le_ofReal hmain

/-- **Dimension reduction** (HDP §8.3.5, Lemma 8.3.14, squared-distance
form): an `ε`-separated finite family (`μ(S ∆ T) > ε²` for `S ≠ T`) stays
`ε/2`-separated in `L²(μ_n)` (`μ_n(S ∆ T) > ε²/4`) with probability at least
`0.99`, once `n ≥ 100·ε⁻⁴·log|F|`. -/
theorem dimension_reduction {Ξ : Type*} [MeasurableSpace Ξ]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity, no scope
    -- change.
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: the sample is jointly independent; HDP §8.3.5,
    -- Lemma 8.3.14.
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP §8.3.5, Lemma 8.3.14 (map form).
    (hlaw : ∀ i, P.map (X i) = μ)
    (F : Finset (Set Ω))
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hFmeas : ∀ S ∈ F, MeasurableSet S)
    -- USER-INPUT: at least two sets, so there is a pair to separate;
    -- HDP §8.3.5, Lemma 8.3.14 (implicit in "ε-separated").
    (hF2 : 2 ≤ F.card)
    {ε : ℝ}
    -- USER-INPUT: positive separation radius; HDP §8.3.5, Lemma 8.3.14.
    (hε : 0 < ε)
    -- USER-INPUT: ε-separation in L²(μ), squared form; HDP §8.3.5,
    -- Lemma 8.3.14.
    (hsep : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → ε ^ 2 < μ.real (S ∆ T))
    {n : ℕ}
    -- USER-INPUT: sample-size condition n ≥ 100·ε⁻⁴·log|F|; HDP §8.3.5,
    -- Lemma 8.3.14 (book's unnamed constant committed as C = 100).
    (hn : 100 * ε⁻¹ ^ 4 * Real.log F.card ≤ n) :
    P {ξ | ∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧
        empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ ε ^ 2 / 4}
      ≤ ENNReal.ofReal (1 / 100) := by
  classical
  -- Positivity facts.
  have hMle : (2 : ℝ) ≤ F.card := by exact_mod_cast hF2
  have hMpos : (0 : ℝ) < F.card := by linarith
  have hlogpos : 0 < Real.log F.card :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < F.card))
  have hε4 : 0 < ε ^ 4 := by positivity
  have hRHSpos : 0 < 100 * ε⁻¹ ^ 4 * Real.log F.card :=
    mul_pos (mul_pos (by norm_num) (by positivity)) hlogpos
  have hnRpos : (0 : ℝ) < n := lt_of_lt_of_le hRHSpos hn
  have hn1 : 1 ≤ n := by exact_mod_cast hnRpos
  set L := Real.log F.card with hLdef
  -- `n·ε⁴ ≥ 100·L`.
  have hnε : 100 * L ≤ (n : ℝ) * ε ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hn (le_of_lt hε4)
    have hsimp : (100 * ε⁻¹ ^ 4 * L) * ε ^ 4 = 100 * L := by
      field_simp
    rwa [hsimp] at h
  -- Per (ordered) pair, the one-sided undershoot has probability `≤ exp(−(9/8)nε⁴)`.
  have hpair : ∀ p ∈ F.offDiag,
      P {ξ | empFrac (fun i : Fin n => X i ξ) (p.1 ∆ p.2) ≤ ε ^ 2 / 4}
        ≤ ENNReal.ofReal (Real.exp (-(9 / 8) * n * ε ^ 4)) := by
    intro p hp
    obtain ⟨haF, hbF, hab⟩ := Finset.mem_offDiag.mp hp
    have hμ : ε ^ 2 < μ.real (p.1 ∆ p.2) := hsep p.1 haF p.2 hbF hab
    set t : ℝ := μ.real (p.1 ∆ p.2) - ε ^ 2 / 4 with htdef
    have hεsq : 0 < ε ^ 2 := by positivity
    have htpos : 0 < t := by rw [htdef]; nlinarith [hμ]
    have hthr : (3 / 4) * ε ^ 2 < t := by rw [htdef]; nlinarith [hμ]
    have hbnd : μ.real (p.1 ∆ p.2) - t = ε ^ 2 / 4 := by rw [htdef]; ring
    rw [← hbnd]
    refine (empFrac_symmDiff_concentration_pair hXmeas hindep hlaw
      (hFmeas p.1 haF) (hFmeas p.2 hbF) htpos hn1).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h2t : (9 / 8) * ε ^ 4 ≤ 2 * t ^ 2 := by nlinarith [hthr, htpos]
    nlinarith [mul_le_mul_of_nonneg_left h2t hnn]
  -- Rewrite the bad event as a finite union over off-diagonal pairs.
  have hE : {ξ | ∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧
        empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ ε ^ 2 / 4}
      = ⋃ p ∈ F.offDiag,
          {ξ | empFrac (fun i : Fin n => X i ξ) (p.1 ∆ p.2) ≤ ε ^ 2 / 4} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_offDiag, Prod.exists,
      exists_prop]
    constructor
    · rintro ⟨S, hS, T, hT, hne, hle⟩; exact ⟨S, T, ⟨hS, hT, hne⟩, hle⟩
    · rintro ⟨S, T, ⟨hS, hT, hne⟩, hle⟩; exact ⟨S, hS, T, hT, hne, hle⟩
  rw [hE]
  refine (measure_biUnion_finset_le _ _).trans ?_
  refine (Finset.sum_le_sum hpair).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  -- Reduce the ℝ≥0∞ bound to a real inequality.
  have hcardle : (F.offDiag.card : ℝ) ≤ (F.card : ℝ) ^ 2 := by
    have h : F.offDiag.card ≤ F.card ^ 2 := by
      rw [Finset.offDiag_card, sq]; exact Nat.sub_le _ _
    calc (F.offDiag.card : ℝ) ≤ ((F.card ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
      _ = (F.card : ℝ) ^ 2 := by push_cast; ring
  have hexp5 : (100 : ℝ) ≤ Real.exp 5 :=
    (Real.log_le_iff_le_exp (by norm_num)).mp log_hundred_le_five
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLlb : Real.log 2 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) hMle
  have hL5 : (5 : ℝ) ≤ 110.5 * L := by nlinarith [hLlb, hlog2]
  have hM2 : (F.card : ℝ) ^ 2 = Real.exp (2 * L) := by
    have hexpL : Real.exp L = F.card := by rw [hLdef]; exact Real.exp_log hMpos
    rw [← hexpL, ← Real.exp_nat_mul]; norm_num
  have hexpchain : (F.card : ℝ) ^ 2 * Real.exp (-(9 / 8) * n * ε ^ 4) ≤ 1 / 100 := by
    calc (F.card : ℝ) ^ 2 * Real.exp (-(9 / 8) * n * ε ^ 4)
        = Real.exp (2 * L) * Real.exp (-(9 / 8) * n * ε ^ 4) := by rw [hM2]
      _ = Real.exp (2 * L + -(9 / 8) * n * ε ^ 4) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-5) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hnε, hL5]
      _ ≤ 1 / 100 := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hexp5
  have hreal : (F.offDiag.card : ℝ) * Real.exp (-(9 / 8) * n * ε ^ 4) ≤ 1 / 100 :=
    le_trans (mul_le_mul_of_nonneg_right hcardle (Real.exp_nonneg _)) hexpchain
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hreal

end StatLean.ConcentrationInequalities
