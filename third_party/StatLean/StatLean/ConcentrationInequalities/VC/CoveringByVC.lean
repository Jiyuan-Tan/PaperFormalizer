module
public import StatLean.ConcentrationInequalities.VC.SauerShelah
public import StatLean.ConcentrationInequalities.VC.DimensionReduction
public import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Covering numbers via VC dimension (Theorem 8.3.13)

For a class $\mathcal{C}$ of measurable sets with
$\mathrm{vc}(\mathcal{C}) \le d$ ($d \ge 1$), *every* probability measure
$\mu$, and every $0 < \varepsilon < 1$:
$$ \mathcal{N}\bigl(\mathcal{C}, L^2(\mu), \varepsilon\bigr)
   \;\le\; \Bigl(\frac{2}{\varepsilon}\Bigr)^{21 d}, $$
in the squared-distance encoding
$\|\mathbf{1}_S - \mathbf{1}_T\|_{L^2(\mu)}^2 = \mu(S \bigtriangleup T)$
(net radius $\varepsilon \iff$ measure $\le \varepsilon^2$, separation
$\iff > \varepsilon^2$). Packing form: any $\varepsilon$-separated
subfamily has at most $(2/\varepsilon)^{21d}$ members. Euclidean form: the
$(\sqrt n)^{-1}$-scaled empirical projection of $\mathcal{C}$ has covering
number at most $\lfloor(2/\varepsilon)^{21d}\rfloor$ — valid for the random
empirical measure precisely because the theorem holds for *every* $\mu$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.5, Theorem 8.3.13 (including footnote 4)
and the empirical-projection reading of §8.3.6.

**Proof formalization notes.** No `PseudoMetricSpace` instance is put on the
class for general `μ` (a Bochner integral of a non-`L²` difference is junk
`0`, breaking the triangle inequality), so the general-`μ` statements use
explicit `μ.real (S ∆ T)` nets/separation; the instance-based
`coveringNumber` appears only for the Euclidean `empProj`. Spine of the
packing bound: instantiate the CANONICAL i.i.d. witness
`Ξ := ℕ → Ω`, `P := Measure.infinitePi (fun _ => μ)`, `X i := Function.eval
i` (via `iIndepFun_infinitePi` / `infinitePi_map_eval`), apply
`dimension_reduction` (a good sample exists since `P(bad) ≤ 1/100 < 1`),
extract ≥ `N` distinct traces on the good sample, and count them by
Sauer–Shelah (`card_traceFamily_le_pow`). The by-contradiction algebra of
footnote 4 is isolated as the pure-real `card_le_pow_of_entropy_bound` with
a quantified-over-`n` hypothesis; assuming `N > (2/ε)^{21d}` also yields
`n > 1400·d ≥ d`, discharging the `d ≤ n` side condition — the book's
unstated regime assumption. The `21`: `N ≤ (400e·ε⁻⁴)^{2d}` (from
`n ≤ 2·100·ε⁻⁴·log N` and `log N ≤ 2d·N^{1/(2d)}`) plus `(400e)² ≤ 2^21`
and `ε < 1`; closable by `nlinarith` with `Real.exp_one_lt_d9`. The
class-level net form is a maximal-cardinality separated family (bounded by
the packing bound, so a maximum exists; maximality makes it a net by
insert-contradiction) — no Zorn, no `Metric.packingNumber`. The two
`private` lemmas duplicate ~15 lines of `AsymptoticStatistics` empirical-
measure content (deliberate: importing another area's concept layer is
forbidden); documented for future promotion to a shared `ForMathlib`.
Named-sorry fallback of this work item: `card_le_pow_of_entropy_bound`
(the footnote-4 algebra); the probabilistic/combinatorial spine
`sepFamily_card_le_of_vcDim_le` must close against it.

**Bibliographic comments.** Covering numbers of VC classes are due to
R. M. Dudley, "Central limit theorems for empirical measures," *Ann.
Probab.* 6 (1978), 899–929, with the sharp exponent later obtained by
D. Haussler, "Sphere packing numbers for subsets of the Boolean n-cube with
bounded Vapnik–Chervonenkis dimension," *J. Combin. Theory Ser. A* 69
(1995), 217–232; the (non-sharp) exponent-`Cd` version is the one
formalized here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal symmDiff

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Footnote-4 algebra of Theorem 8.3.13 (HDP §8.3.5), isolated as pure real
analysis: if every `n ≥ 100·ε⁻⁴·log N` forces `N ≤ (e·n/d)^d`, then
`N ≤ (2/ε)^{21d}`. The `21` absorbs `(400e)² ≤ 2^21` and `ε < 1`. -/
lemma card_le_pow_of_entropy_bound {N d : ℕ} {ε : ℝ}
    -- USER-INPUT: 1 ≤ d (nondegenerate VC dimension); HDP §8.3.5,
    -- Theorem 8.3.13.
    (hd1 : 1 ≤ d)
    -- USER-INPUT: 0 < ε < 1 (the theorem's radius regime); HDP §8.3.5,
    -- Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1)
    -- LEAN-ONLY: the quantified-over-n Sauer–Shelah input, exactly what the
    -- probabilistic spine produces; isolates the footnote-4 algebra from
    -- probability and combinatorics.
    (hN : ∀ n : ℕ, 100 * ε⁻¹ ^ 4 * Real.log N ≤ n →
      (N : ℝ) ≤ (Real.exp 1 * n / d) ^ d) :
    (N : ℝ) ≤ (2 / ε) ^ (21 * d) := by
  -- Real preliminaries reused throughout.
  have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hεinv : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1.le
  have hε4 : (1 : ℝ) ≤ ε⁻¹ ^ 4 := one_le_pow₀ hεinv
  have hbase_ge2 : (2 : ℝ) ≤ 2 / ε := by rw [le_div_iff₀ hε]; nlinarith [hε1, hε]
  have hbase_ge1 : (1 : ℝ) ≤ 2 / ε := le_trans (by norm_num) hbase_ge2
  have hbasepow_ge1 : (1 : ℝ) ≤ (2 / ε) ^ (21 * d) := one_le_pow₀ hbase_ge1
  -- Reduce to `N ≥ 2`; for `N ≤ 1` the bound is immediate.
  rcases le_or_gt N 1 with hNsmall | hN2
  · calc (N : ℝ) ≤ 1 := by exact_mod_cast hNsmall
      _ ≤ (2 / ε) ^ (21 * d) := hbasepow_ge1
  -- `N ≥ 2`.
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_gt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogN2 : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hN2R
  have hxpos : (0 : ℝ) < Real.log (N : ℝ) := lt_of_lt_of_le hlog2_pos hlogN2
  have hxne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hxpos
  -- Instantiate the entropy hypothesis at `n₀ = ⌈100 ε⁻⁴ log N⌉`.
  set n₀ : ℕ := ⌈100 * ε⁻¹ ^ 4 * Real.log (N : ℝ)⌉₊ with hn₀
  have hr0 : (0 : ℝ) ≤ 100 * ε⁻¹ ^ 4 * Real.log (N : ℝ) := by positivity
  have hle : 100 * ε⁻¹ ^ 4 * Real.log (N : ℝ) ≤ (n₀ : ℝ) := Nat.le_ceil _
  have hlt : (n₀ : ℝ) < 100 * ε⁻¹ ^ 4 * Real.log (N : ℝ) + 1 := Nat.ceil_lt_add_one hr0
  have h100 : (1 : ℝ) ≤ 100 * ε⁻¹ ^ 4 * Real.log (N : ℝ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hε4) hxpos.le, hlogN2, hlog2_gt, hε4]
  have hn₀pos : 1 ≤ n₀ := by
    have : (1 : ℝ) ≤ (n₀ : ℝ) := le_trans h100 hle
    exact_mod_cast this
  have hn₀ne : (n₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hbound := hN n₀ hle
  -- Take logs.
  have hlogmain : Real.log (N : ℝ) ≤ (d : ℝ) * Real.log (Real.exp 1 * (n₀ : ℝ) / (d : ℝ)) := by
    have h := Real.log_le_log hNpos hbound
    rwa [Real.log_pow] at h
  -- Expand `log(e·n₀/d) = 1 + log n₀ − log d`.
  have hid : Real.log (Real.exp 1 * (n₀ : ℝ) / (d : ℝ))
      = 1 + Real.log (n₀ : ℝ) - Real.log (d : ℝ) := by
    rw [Real.log_div (mul_ne_zero (Real.exp_ne_zero 1) hn₀ne) hd0,
      Real.log_mul (Real.exp_ne_zero 1) hn₀ne, Real.log_exp]
  -- Bound `log n₀ ≤ log 200 − 4 log ε + log(log N)`.
  have hn₀bound : (n₀ : ℝ) ≤ 200 * ε⁻¹ ^ 4 * Real.log (N : ℝ) := by nlinarith [hlt, h100]
  have hC : Real.log (n₀ : ℝ)
      ≤ Real.log 200 - 4 * Real.log ε + Real.log (Real.log (N : ℝ)) := by
    have hpos200 : (0 : ℝ) < 200 * ε⁻¹ ^ 4 * Real.log (N : ℝ) := by positivity
    have h := Real.log_le_log (by exact_mod_cast hn₀pos : (0:ℝ) < (n₀:ℝ)) hn₀bound
    rw [Real.log_mul (by positivity) hxne, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_inv] at h
    push_cast at h
    linarith [h]
  -- Bound `log(log N) ≤ log 2 + log d + (log N)/(2d) − 1`.
  have h2dne : (2 : ℝ) * (d : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hd0
  have hD : Real.log (Real.log (N : ℝ))
      ≤ Real.log 2 + Real.log (d : ℝ) + Real.log (N : ℝ) / (2 * (d : ℝ)) - 1 := by
    have hdiv : Real.log (Real.log (N : ℝ) / (2 * (d : ℝ)))
        = Real.log (Real.log (N : ℝ)) - Real.log (2 * (d : ℝ)) := Real.log_div hxne h2dne
    have hsub : Real.log (Real.log (N : ℝ) / (2 * (d : ℝ)))
        ≤ Real.log (N : ℝ) / (2 * (d : ℝ)) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlog2d : Real.log (2 * (d : ℝ)) = Real.log 2 + Real.log (d : ℝ) :=
      Real.log_mul (by norm_num) hd0
    linarith [hdiv, hsub, hlog2d]
  -- Assemble the `B`-bound and multiply by `d`.
  have hB : Real.log (Real.exp 1 * (n₀ : ℝ) / (d : ℝ))
      ≤ Real.log 200 - 4 * Real.log ε + Real.log 2 + Real.log (N : ℝ) / (2 * (d : ℝ)) := by
    rw [hid]; linarith [hC, hD]
  have hxdB : Real.log (N : ℝ)
      ≤ (d : ℝ) * (Real.log 200 - 4 * Real.log ε + Real.log 2
          + Real.log (N : ℝ) / (2 * (d : ℝ))) :=
    le_trans hlogmain (mul_le_mul_of_nonneg_left hB hd_nonneg)
  have hcancel : (d : ℝ) * (Real.log (N : ℝ) / (2 * (d : ℝ))) = Real.log (N : ℝ) / 2 := by
    field_simp
  have heq2 : (d : ℝ) * (Real.log 200 - 4 * Real.log ε + Real.log 2
        + Real.log (N : ℝ) / (2 * (d : ℝ)))
      = (d : ℝ) * (Real.log 200 - 4 * Real.log ε + Real.log 2) + Real.log (N : ℝ) / 2 := by
    rw [mul_add, hcancel]
  rw [heq2] at hxdB
  -- Numeric facts for the final combination.
  have hnum : 2 * Real.log 200 ≤ 19 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 200 ^ 2) (by norm_num : (200:ℝ) ^ 2 ≤ 2 ^ 19)
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h; linarith [h]
  have hlogε_nonpos : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1.le
  -- Close in log form, then exponentiate.
  have hpospow : (0 : ℝ) < (2 / ε) ^ (21 * d) := by positivity
  have hgoal : Real.log (N : ℝ) ≤ Real.log ((2 / ε) ^ (21 * d)) := by
    rw [Real.log_pow, Real.log_div (by norm_num) (ne_of_gt hε)]
    push_cast
    nlinarith [hxdB, mul_nonneg hd_nonneg (sub_nonneg.mpr hnum),
      mul_nonneg hd_nonneg (neg_nonneg.mpr hlogε_nonpos)]
  have hexp := Real.exp_le_exp.mpr hgoal
  rwa [Real.exp_log hNpos, Real.exp_log hpospow] at hexp

/-- **Covering numbers via VC dimension, packing form** (HDP §8.3.5,
Theorem 8.3.13, the core): any `ε`-separated subfamily (squared form
`μ(S ∆ T) > ε²`) of a class with `vc ≤ d` has at most `(2/ε)^{21d}`
members, for every probability measure `μ`. -/
theorem sepFamily_card_le_of_vcDim_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {C : Set (Set Ω)}
    -- LEAN-ONLY: measurability of the class members (implicit in the book's
    -- Boolean functions on a probability space).
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.5, Theorem 8.3.13.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.5 (regime of Exercise 0.6 / Lemma 8.3.9).
    (hd1 : 1 ≤ d)
    {ε : ℝ}
    -- USER-INPUT: radius regime 0 < ε < 1; HDP §8.3.5, Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1)
    {F : Finset (Set Ω)}
    -- USER-INPUT: the separated subfamily lies in the class; HDP §8.3.5.
    (hFC : ↑F ⊆ C)
    -- USER-INPUT: ε-separation in L²(μ), squared form; HDP §8.3.5,
    -- Theorem 8.3.13.
    (hsep : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → ε ^ 2 < μ.real (S ∆ T)) :
    (F.card : ℝ) ≤ (2 / ε) ^ (21 * d) := by
  classical
  -- If `F` is already small the bound is immediate; otherwise the entropy
  -- algebra applies and its `∀ n` hypothesis is what the spine produces.
  by_cases hcard : (F.card : ℝ) ≤ (2 / ε) ^ (21 * d)
  · exact hcard
  push_neg at hcard
  -- Real preliminaries.
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hεinv : (1 : ℝ) ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1.le
  have h4 : (1 : ℝ) ≤ ε⁻¹ ^ 4 := one_le_pow₀ hεinv
  have h2e : (2 : ℝ) ≤ 2 / ε := by rw [le_div_iff₀ hε]; nlinarith [hε1, hε]
  have hbase_pos : (0 : ℝ) < 2 / ε := by positivity
  have hone_le_base : (1 : ℝ) ≤ 2 / ε := le_trans (by norm_num) h2e
  have hlogdiv : Real.log 2 ≤ Real.log (2 / ε) := Real.log_le_log (by norm_num) h2e
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- `F.card ≥ 2`.
  have hposbase : (0 : ℝ) < (2 / ε) ^ (21 * d) := by positivity
  have hone_le_pow : (1 : ℝ) ≤ (2 / ε) ^ (21 * d) := one_le_pow₀ hone_le_base
  have hF2 : 2 ≤ F.card := by
    have : (1 : ℝ) < (F.card : ℝ) := lt_of_le_of_lt hone_le_pow hcard
    have : 1 < F.card := by exact_mod_cast this
    omega
  -- Apply the footnote-4 algebra; supply the quantified Sauer–Shelah input.
  apply card_le_pow_of_entropy_bound hd1 hε hε1
  intro n hn
  -- From `F.card > (2/ε)^{21d}` and `n ≥ 100 ε⁻⁴ log F.card`, deduce `d ≤ n`.
  have hlogFcard : ((21 * d : ℕ) : ℝ) * Real.log (2 / ε) < Real.log F.card := by
    have h := Real.log_lt_log hposbase hcard
    rwa [Real.log_pow] at h
  have h21d : ((21 * d : ℕ) : ℝ) = 21 * (d : ℝ) := by push_cast; ring
  rw [h21d] at hlogFcard
  have hlogpos : (0 : ℝ) < Real.log F.card := by
    have h1 : (0 : ℝ) < 21 * (d : ℝ) * Real.log (2 / ε) := by
      apply mul_pos
      · positivity
      · linarith [hlogdiv, hlog2]
    linarith [hlogFcard, h1]
  have hstep1 : (100 : ℝ) * Real.log F.card ≤ (n : ℝ) := by
    have hmul : (100 : ℝ) * Real.log F.card ≤ 100 * ε⁻¹ ^ 4 * Real.log F.card := by
      nlinarith [h4, hlogpos]
    linarith [hn, hmul]
  have hdn_real : (d : ℝ) ≤ (n : ℝ) := by
    have hbig : (d : ℝ) ≤ 100 * Real.log F.card := by
      nlinarith [hlogFcard,
        mul_nonneg (by positivity : (0 : ℝ) ≤ 21 * (d : ℝ))
          (by linarith [hlogdiv] : (0 : ℝ) ≤ Real.log (2 / ε) - Real.log 2),
        mul_nonneg (by positivity : (0 : ℝ) ≤ 21 * (d : ℝ))
          (by linarith [hlog2] : (0 : ℝ) ≤ Real.log 2 - 0.6931471803),
        hdR]
    linarith [hstep1, hbig]
  have hdn : d ≤ n := by exact_mod_cast hdn_real
  haveI : NeZero n := ⟨by omega⟩
  -- Canonical i.i.d. witness on `ℕ → Ω` (product measure is a probability
  -- measure automatically).
  set X : ℕ → (ℕ → Ω) → Ω := fun i ω => ω i with hXdef
  have hXmeas : ∀ i, Measurable (X i) := fun i => measurable_pi_apply i
  have hindep : iIndepFun X (Measure.infinitePi (fun _ : ℕ => μ)) := by
    have h := iIndepFun_infinitePi (𝓧 := fun _ : ℕ => Ω) (P := fun _ : ℕ => μ)
      (X := fun _ => (id : Ω → Ω)) (fun _ => measurable_id)
    simpa [X] using h
  have hlaw : ∀ i, (Measure.infinitePi (fun _ : ℕ => μ)).map (X i) = μ :=
    fun i => Measure.infinitePi_map_eval (fun _ : ℕ => μ) i
  have hFmeas : ∀ S ∈ F, MeasurableSet S :=
    fun S hS => hCmeas S (hFC (Finset.mem_coe.mpr hS))
  have hdr := dimension_reduction hXmeas hindep hlaw F hFmeas hF2 hε hsep hn
  -- The good event is nonempty: its complement (the bad event) is not all of Ξ.
  have hbad : ∃ ξ, ξ ∉ {ξ | ∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧
      empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ ε ^ 2 / 4} := by
    by_contra hcon
    push_neg at hcon
    have huniv : {ξ | ∃ S ∈ F, ∃ T ∈ F, S ≠ T ∧
        empFrac (fun i : Fin n => X i ξ) (S ∆ T) ≤ ε ^ 2 / 4} = Set.univ :=
      Set.eq_univ_of_forall hcon
    rw [huniv, measure_univ] at hdr
    exact absurd hdr (not_le.mpr (ENNReal.ofReal_lt_one.mpr (by norm_num)))
  obtain ⟨ξ, hξ⟩ := hbad
  simp only [Set.mem_setOf_eq, not_exists, not_and, not_le] at hξ
  -- The sample.
  set x : Fin n → Ω := fun i => X i ξ with hxdef
  set Λ : Finset Ω := Finset.image x Finset.univ with hΛdef
  -- The `F`-members have pairwise-distinct traces on the sample.
  have htrmem : ∀ S ∈ F, Λ.filter (· ∈ S) ∈ traceFamily C Λ := by
    intro S hS
    rw [mem_traceFamily]
    refine ⟨Finset.filter_subset _ _, S, hFC (Finset.mem_coe.mpr hS), ?_⟩
    rw [Finset.coe_filter]
    ext y
    simp [Set.mem_inter_iff]
  have hinj : Set.InjOn (fun S => Λ.filter (· ∈ S)) (↑F : Set (Set Ω)) := by
    intro S hS T hT hfeq
    by_contra hne
    have hgood := hξ S (Finset.mem_coe.mp hS) T (Finset.mem_coe.mp hT) hne
    have hpos : 0 < empFrac x (S ∆ T) := by
      have hq : (0 : ℝ) < ε ^ 2 / 4 := by positivity
      simp only [x] at hgood ⊢
      linarith [hgood]
    obtain ⟨i, hi⟩ := empFrac_pos_iff.mp hpos
    have hiΛ : x i ∈ Λ := Finset.mem_image_of_mem x (Finset.mem_univ i)
    have hmem : (x i ∈ S) ↔ (x i ∈ T) := by
      have hf : Λ.filter (· ∈ S) = Λ.filter (· ∈ T) := hfeq
      have h : (x i ∈ Λ.filter (· ∈ S)) ↔ (x i ∈ Λ.filter (· ∈ T)) := by rw [hf]
      simpa [Finset.mem_filter, hiΛ] using h
    rw [Set.mem_symmDiff] at hi
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hmem.mp h1)
    · exact h2 (hmem.mpr h1)
  have hcardle : F.card ≤ (traceFamily C Λ).card :=
    Finset.card_le_card_of_injOn (fun S => Λ.filter (· ∈ S))
      (fun S hS => htrmem S (Finset.mem_coe.mp hS)) hinj
  have hΛcard : Λ.card ≤ n := by
    calc Λ.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have htrpow : ((traceFamily C Λ).card : ℝ) ≤ (Real.exp 1 * n / d) ^ d :=
    card_traceFamily_le_pow hd hd1 hΛcard hdn
  calc (F.card : ℝ) ≤ ((traceFamily C Λ).card : ℝ) := by exact_mod_cast hcardle
    _ ≤ (Real.exp 1 * n / d) ^ d := htrpow

/-- **Covering numbers via VC dimension, net form** (HDP §8.3.5,
Theorem 8.3.13): `𝒩(C, L²(μ), ε) ≤ (2/ε)^{21d}` — an internal `ε`-net
(squared form `μ(S ∆ T) ≤ ε²`) of the stated cardinality exists. Proof: a
maximal-cardinality `ε`-separated subfamily (which exists since
cardinalities are bounded by the packing form) is a net by
insert-contradiction. -/
theorem exists_L2_net_of_vcDim_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] {C : Set (Set Ω)}
    -- LEAN-ONLY: measurability of the class members; as in the packing form.
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.5, Theorem 8.3.13.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.5.
    (hd1 : 1 ≤ d)
    {ε : ℝ}
    -- USER-INPUT: radius regime 0 < ε < 1; HDP §8.3.5, Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ N : Finset (Set Ω), ↑N ⊆ C ∧ (N.card : ℝ) ≤ (2 / ε) ^ (21 * d) ∧
      ∀ S ∈ C, ∃ T ∈ N, μ.real (S ∆ T) ≤ ε ^ 2 := by
  classical
  set K : ℕ := ⌊(2 / ε) ^ (21 * d)⌋₊ with hK
  -- Cardinalities of `ε`-separated subfamilies of `C`.
  set s : Set ℕ := {m | ∃ G : Finset (Set Ω), ↑G ⊆ C ∧
    (∀ S ∈ G, ∀ T ∈ G, S ≠ T → ε ^ 2 < μ.real (S ∆ T)) ∧ G.card = m} with hs
  have hs0 : (0 : ℕ) ∈ s := ⟨∅, by simp, by simp, by simp⟩
  have hbdd : ∀ m ∈ s, m ≤ K := by
    rintro m ⟨G, hGC, hGsep, rfl⟩
    exact Nat.le_floor
      (sepFamily_card_le_of_vcDim_le hCmeas hd hd1 hε hε1 hGC hGsep)
  have hsfin : s.Finite := Set.Finite.subset (Set.finite_Iic K) hbdd
  have hsne : s.Nonempty := ⟨0, hs0⟩
  obtain ⟨G, hGC, hGsep, hGcard⟩ := hsne.csSup_mem hsfin
  refine ⟨G, hGC, sepFamily_card_le_of_vcDim_le hCmeas hd hd1 hε hε1 hGC hGsep, ?_⟩
  -- Maximality makes `G` a net.
  intro S hS
  by_contra hcon
  push_neg at hcon
  have hSnotin : S ∉ G := by
    intro hSin
    have h := hcon S hSin
    rw [symmDiff_self, Set.bot_eq_empty, measureReal_empty] at h
    nlinarith [sq_nonneg ε]
  have hG'sep : ∀ A ∈ insert S G, ∀ B ∈ insert S G, A ≠ B →
      ε ^ 2 < μ.real (A ∆ B) := by
    intro A hA B hB hAB
    simp only [Finset.mem_insert] at hA hB
    rcases hA with rfl | hA <;> rcases hB with rfl | hB
    · exact absurd rfl hAB
    · exact hcon B hB
    · rw [symmDiff_comm]; exact hcon A hA
    · exact hGsep A hA B hB hAB
  have hG'C : ↑(insert S G) ⊆ C := by
    rw [Finset.coe_insert]; exact Set.insert_subset hS hGC
  have hmem : G.card + 1 ∈ s :=
    ⟨insert S G, hG'C, hG'sep, Finset.card_insert_of_notMem hSnotin⟩
  have hle : G.card + 1 ≤ sSup s := le_csSup hsfin.bddAbove hmem
  rw [hGcard] at hle
  omega

/-- **Empirical projection** (LEAN-ONLY carrier for the empirical `L²(μ_n)`
geometry of HDP §8.3.6): `v_S = (√n)⁻¹ · (𝟙_S(x_i))_{i < n} ∈ ℝⁿ`, built as
a sum of `EuclideanSpace.single`s (defeq-safe at the pin). Then
`dist(v_S, v_T)² = empFrac x (S ∆ T) = ‖𝟙_S − 𝟙_T‖²_{L²(μ_n)}` exactly.
Edge behavior: `n = 0` gives the empty vector; the `(√0)⁻¹ = 0` junk is
multiplied into an empty sum. -/
noncomputable def empProj {n : ℕ} (x : Fin n → Ω) (S : Set Ω) :
    EuclideanSpace ℝ (Fin n) :=
  ∑ i, EuclideanSpace.single i
    ((Real.sqrt n)⁻¹ * S.indicator (fun _ => (1 : ℝ)) (x i))

/-- Coordinates of the empirical projection (LEAN-ONLY:
`EuclideanSpace.single_apply` bookkeeping). -/
@[simp] lemma empProj_apply {n : ℕ} (x : Fin n → Ω) (S : Set Ω) (i : Fin n) :
    empProj x S i = (Real.sqrt n)⁻¹ * S.indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  have h : empProj x S = WithLp.toLp 2
      (fun j : Fin n => (Real.sqrt n)⁻¹ * S.indicator (fun _ => (1 : ℝ)) (x j)) := by
    rw [empProj]
    simp only [EuclideanSpace.single, ← PiLp.toLp_single, ← WithLp.toLp_sum]
    rw [Finset.univ_sum_single]
  rw [h, PiLp.toLp_apply]

/-- The empirical projection is an exact (squared) isometry onto the
empirical `L²` geometry (LEAN-ONLY: `EuclideanSpace.dist_eq` + indicator
algebra `(𝟙_S − 𝟙_T)² = 𝟙_{S ∆ T}`). -/
lemma dist_empProj_sq {n : ℕ} [NeZero n] (x : Fin n → Ω) (S T : Set Ω) :
    dist (empProj x S) (empProj x T) ^ 2 = empFrac x (S ∆ T) := by
  classical
  rw [EuclideanSpace.dist_sq_eq]
  have hsqrt : ((Real.sqrt n)⁻¹) ^ 2 = (n : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have key : ∀ i : Fin n,
      dist (empProj x S i) (empProj x T i) ^ 2
        = (n : ℝ)⁻¹ * (S ∆ T).indicator (fun _ => (1 : ℝ)) (x i) := by
    intro i
    rw [empProj_apply, empProj_apply, Real.dist_eq, sq_abs, ← mul_sub, mul_pow, hsqrt]
    congr 1
    by_cases hS : x i ∈ S <;> by_cases hT : x i ∈ T <;>
      simp [Set.mem_symmDiff, hS, hT]
  rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, empFrac]

/-- The `(n : ℝ≥0∞)⁻¹ • ∑ dirac` empirical measure is a probability measure
(LEAN-ONLY: local duplicate of `AsymptoticStatistics` content — deliberate
non-import of another area's concept layer; candidate for promotion to a
shared `ForMathlib`). -/
private lemma isProbabilityMeasure_avg_dirac {n : ℕ} [NeZero n]
    (x : Fin n → Ω) :
    IsProbabilityMeasure
      ((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)) := by
  constructor
  rw [Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n)
    (ENNReal.natCast_ne_top n)

/-- On measurable sets, the averaged-dirac empirical measure evaluates to
`empFrac` (LEAN-ONLY bridge; see `isProbabilityMeasure_avg_dirac`). -/
private lemma avg_dirac_real_eq_empFrac {n : ℕ} [NeZero n] (x : Fin n → Ω)
    {S : Set Ω}
    -- LEAN-ONLY: measurability so `Measure.dirac` evaluates by membership.
    (hS : MeasurableSet S) :
    ((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)).real S
      = empFrac x S := by
  classical
  rw [measureReal_ennreal_smul_apply, measureReal_def, Measure.finset_sum_apply]
  simp_rw [Measure.dirac_apply' _ hS]
  rw [ENNReal.toReal_sum (fun i _ => by
      rw [Set.indicator_apply]; split_ifs <;> simp), empFrac]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : x i ∈ S <;> simp [h]

/-- **Covering number of the empirical projection** (HDP §8.3.5–8.3.6:
Theorem 8.3.13 applied to the empirical measure `μ_n` — the KEY SUBTLETY is
that the theorem holds for *every* probability measure, hence for the random
`μ_n(ω)` with a sample-independent right-hand side):
`𝒩(empProj x '' C, ε) ≤ ⌊(2/ε)^{21d}⌋` in `EuclideanSpace ℝ (Fin n)`.
Transported from `exists_L2_net_of_vcDim_le` at `μ := μ_n` via
`dist_empProj_sq` and `Metric.IsCover.coveringNumber_le_encard`. -/
theorem coveringNumber_empProj_le {n : ℕ} [NeZero n] (x : Fin n → Ω)
    {C : Set (Set Ω)}
    -- LEAN-ONLY: measurability of the class members; needed for the dirac
    -- `.real` evaluation, no scope change.
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.5, Theorem 8.3.13.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.3.5.
    (hd1 : 1 ≤ d)
    {ε : ℝ}
    -- USER-INPUT: radius regime 0 < ε < 1; HDP §8.3.5, Theorem 8.3.13.
    (hε : 0 < ε) (hε1 : ε < 1) :
    coveringNumber (empProj x '' C) ε ≤ (⌊(2 / ε) ^ (21 * d)⌋₊ : ℕ∞) := by
  classical
  haveI : IsProbabilityMeasure ((n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)) :=
    isProbabilityMeasure_avg_dirac x
  obtain ⟨N, hNC, hNcard, hNnet⟩ :=
    exists_L2_net_of_vcDim_le hCmeas hd hd1 hε hε1
      (μ := (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i))
  -- The image of the net covers the image of the class.
  have hcover : Metric.IsCover (Real.toNNReal ε) (empProj x '' C) (empProj x '' ↑N) := by
    apply IsEpsilonNet.isCover hε.le
    refine ⟨Set.image_mono hNC, ?_⟩
    rintro v ⟨S, hSC, rfl⟩
    obtain ⟨T, hTN, hTle⟩ := hNnet S hSC
    refine ⟨empProj x T, Set.mem_image_of_mem _ hTN, ?_⟩
    have hST : MeasurableSet (S ∆ T) :=
      (hCmeas S hSC).symmDiff (hCmeas T (hNC (Finset.mem_coe.mpr hTN)))
    have hsq : dist (empProj x S) (empProj x T) ^ 2 ≤ ε ^ 2 := by
      rw [dist_empProj_sq, ← avg_dirac_real_eq_empFrac x hST]; exact hTle
    have hnn := dist_nonneg (x := empProj x S) (y := empProj x T)
    nlinarith [hsq, hnn, hε]
  -- Bound the covering number by the net-image cardinality.
  have hle := hcover.coveringNumber_le_encard (Set.image_mono hNC)
  have hbound : (empProj x '' ↑N).encard ≤ (⌊(2 / ε) ^ (21 * d)⌋₊ : ℕ∞) := by
    calc (empProj x '' ↑N).encard ≤ (↑N : Set (Set Ω)).encard := Set.encard_image_le _ _
      _ = (N.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard N
      _ ≤ (⌊(2 / ε) ^ (21 * d)⌋₊ : ℕ∞) := by exact_mod_cast Nat.le_floor hNcard
  exact le_trans hle hbound

end StatLean.ConcentrationInequalities
