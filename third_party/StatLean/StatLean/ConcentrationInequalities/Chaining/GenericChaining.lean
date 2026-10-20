module
public import StatLean.ConcentrationInequalities.Chaining.GammaTwo
public import StatLean.ConcentrationInequalities.Chaining.SubsetChaining
public import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
public import StatLean.ConcentrationInequalities.Chaining.TailToExpectation
public import StatLean.ConcentrationInequalities.Chaining.DyadicNets
public import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Generic chaining (Talagrand's γ₂ bound)

For a mean-zero process $(X_t)_{t \in T}$ with sub-Gaussian increments
(Eq. 8.1) on a finite metric space $(T, d)$,
$$ \mathbb{E} \max_{t \in T} X_t \;\le\; 20\, K \,\gamma_2(T, d), $$
where $\gamma_2$ is the Talagrand functional over admissible sequences
(Definition 8.5.1, `Chaining/GammaTwo.lean`) and $20$ freezes the book's
unnamed absolute constant $C$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.5.2, Theorem 8.5.2 (proof Steps 1–3,
Eqs. (8.48)–(8.50)); Remark 8.5.3 for the mean-zero-free $|X_t - X_{t_0}|$
form.

**Proof formalization notes.** Finite-`T` core per the batch sup policy
(book WLOG, p. 247 Step 1). The high-probability form
(`generic_chaining_tail_of_finite`) carries per-level thresholds
$2^{k/2}(\sqrt{2\log 2} + 1) + u$ over the admissible-sequence levels and a
union bound over $|T_k|\cdot|T_{k-1}| \le 2^{2^{k+1}}$ chain pairs; the
expectation forms integrate it via
`Chaining/TailToExpectation.lean`. **Frozen constants** (formula + numeral):
tail threshold factor `(12 + 4u)` — the sharp canonical-anchor factor
`(6 + 2u)` doubled through the arbitrary-anchor triangle; expectation
constant `20` (book's unnamed absolute `C`, from integrating the
`(12 + 4u)` tail). Per batch reconciliation R4, the mean-zero assemblies
carry the LEAN-ONLY hypothesis `hint : ∀ t ∈ T, Integrable (X t) μ` ruling
out Bochner-junk means (the per-pair increment means are then genuine).

**Bibliographic comments.** Generic chaining and the majorizing-measure
theory are due to X. Fernique ("Régularité des trajectoires des fonctions
aléatoires gaussiennes," in *École d'Été de Probabilités de Saint-Flour
IV–1974*, Lecture Notes in Mathematics 480, Springer, 1975, 1–96) and
M. Talagrand ("Regularity of Gaussian processes," *Acta Math.* 159 (1987),
99–149; *Upper and Lower Bounds for Stochastic Processes*, Springer, 2014).
The admissible-sequence formulation of $\gamma_2$ is Talagrand's; the
matching lower bound (the majorizing measure theorem) is not formalized
here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- A.e.-measurability of a finite (hence countable) `biSup` of
a.e.-measurable functions. -/
private lemma aemeasurable_biSup_of_finite {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {E : Type*} {T : Set E} (hfin : T.Finite) {g : E → Ω → ℝ}
    (hg : ∀ t ∈ T, AEMeasurable (g t) μ) :
    AEMeasurable (fun ω => ⨆ t ∈ T, g t ω) μ :=
  AEMeasurable.biSup T hfin.countable hg

/-- A.e.-measurability of a pointwise `Finset.sup'` of a.e.-measurable
functions (junk-free twin of `aemeasurable_biSup_of_finite`). -/
private lemma aemeasurable_sup'_finset {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {g : ι → Ω → ℝ}
    (hg : ∀ i ∈ s, AEMeasurable (g i) μ) :
    AEMeasurable (fun ω => s.sup' hs (fun i => g i ω)) μ := by
  classical
  revert hg
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => intro hg; exact hg a (by simp)
  | cons a t ha ht ih =>
      intro hg
      simp only [Finset.sup'_cons ht]
      exact (hg a (by simp)).sup (ih (fun i hi => hg i (by simp [hi])))

/-- A single value is dominated by the finite `biSup`, unconditionally (the
`ℝ`-junk branches only push the biSup up). -/
private lemma le_biSup_of_finite {E : Type*} {T : Set E} (hfin : T.Finite)
    (g : E → ℝ) {t : E} (ht : t ∈ T) : g t ≤ ⨆ s ∈ T, g s := by
  have setToF : (⨆ s ∈ hfin.toFinset, g s) = ⨆ s ∈ T, g s :=
    iSup_congr fun s => by rw [hfin.mem_toFinset]
  rw [← setToF]
  exact le_biSup_finset g (hfin.mem_toFinset.mpr ht)

/-- A uniform **nonnegative** bound on the values dominates the finite
`biSup`. The nonnegativity `hc` is REQUIRED (junk-value guard, statement fix
at the debt gate): for `E ⊋ T` the real biSup carries the junk branch value
`0`, so `⨆ s ∈ T, g s = max (max_T g) 0 ≤ c` genuinely needs `0 ≤ c`
(e.g. `g ≡ -1 ≤ c := -1` on a proper subset, but the biSup is `0`). Every
use in this file has an `|·|`-valued or otherwise nonnegative bound. -/
private lemma biSup_le_of_finite {E : Type*} {T : Set E} (hfin : T.Finite)
    (hne : T.Nonempty) (g : E → ℝ) {c : ℝ} (h : ∀ s ∈ T, g s ≤ c)
    (hc : 0 ≤ c) : ⨆ s ∈ T, g s ≤ c := by
  refine Real.iSup_le (fun s => ?_) hc
  by_cases hs : s ∈ T
  · rw [ciSup_pos hs]; exact h s hs
  · haveI : IsEmpty (s ∈ T) := ⟨hs⟩
    rw [Real.iSup_of_isEmpty]; exact hc

/-- Exponential geometric tail `∑_{k<n} exp(-(k+1)) ≤ 1`, via `exp(-1) ≤ 1/2`. -/
private lemma sum_exp_neg_succ_le_one (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.exp (-((k : ℝ) + 1)) ≤ 1 := by
  have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h2
  have hsum : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
    have hrw : ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ (k + 1)
        = (1 / 2) * ∑ k ∈ Finset.range n, (1 / 2 : ℝ) ^ k := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by rw [pow_succ]; ring
    rw [hrw]; linarith [sum_geometric_two_le n]
  have hterm : ∀ k ∈ Finset.range n, Real.exp (-((k : ℝ) + 1)) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k _
    have hei : Real.exp (-((k : ℝ) + 1)) = Real.exp (-1) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hei]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) he1 (k + 1)
  exact le_trans (Finset.sum_le_sum hterm) hsum

/-- **Generic chaining, high-probability form** (HDP §8.5.2, Theorem 8.5.2
proof Steps 2–3, Eqs. (8.48)–(8.50)): for any admissible sequence `A`, the
sup of increments exceeds `(12 + 4u)·K·γ(A)` with probability at most
`2 exp(−u²)`. This work item's single named-sorry fallback. -/
theorem generic_chaining_tail_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure; bridge-B1 tail machinery requires it
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG p.247 Step 1; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index so the sup is genuine
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the process; regularity
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point of the increment sup; Remark 8.5.3 device
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T)
    -- LEAN-ONLY: finite functional (⊤ makes the event's threshold junk 0)
    (hA : gammaFunctional A ≠ ⊤)
    {u : ℝ}
    -- USER-INPUT: deviation parameter u ≥ 0; HDP Eq (8.50)
    (hu : 0 ≤ u) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal <
        ⨆ t ∈ T, |X t ω - X t₀ ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  classical
  set G : ℝ := (gammaFunctional A).toReal with hGdef
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  -- Finite carrier as a `Finset`, with `⨆ over F = ⨆ over T`.
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hfin.mem_toFinset.mp ht
  have setToF : ∀ f : E → ℝ, (⨆ t ∈ F, f t) = ⨆ t ∈ T, f t :=
    fun f => iSup_congr fun t => by rw [hfin.mem_toFinset]
  -- Canonical anchor `a₀` = the seq-0 singleton point.
  obtain ⟨a₀, ha₀seq⟩ := Finset.card_eq_one.mp A.card_zero
  have ha₀mem : a₀ ∈ A.seq 0 := by rw [ha₀seq]; exact Finset.mem_singleton_self a₀
  have ha₀T : a₀ ∈ T := A.subset_carrier 0 (Finset.mem_coe.mpr ha₀mem)
  have hπ0 : ∀ t : E, netProj (A.seq 0) t = a₀ := by
    intro t; rw [ha₀seq]
    have hmem := netProj_mem (Finset.singleton_nonempty a₀) t
    rwa [Finset.mem_singleton] at hmem
  -- √2 bricks.
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2sq, hs2nn]
  have hw2 : ∀ k : ℕ, (Real.sqrt 2 ^ k) ^ 2 = 2 ^ k := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hK0 : K = 0
  · -- K = 0: all increments vanish a.e., so the anchored sup is a.e. 0.
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff hfin.countable]
      intro t ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t ht
        rw [hK0] at h
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas t₀ ht₀)) hnorm
    have hallz : ∀ᵐ ω ∂μ, (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ 0 := by
      filter_upwards [hz] with ω hω
      exact biSup_le_of_finite hfin hne _ (fun s hs => by rw [hω s hs, abs_zero]) le_rfl
    have hthr0 : (12 + 4 * u) * (K : ℝ) * G = 0 := by rw [hK0]; simp
    rw [hthr0]
    have hnull : μ {ω | (0 : ℝ) < ⨆ t ∈ T, |X t ω - X t₀ ω|} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp hallz)
      simp only [Set.mem_setOf_eq, not_le]; exact hω
    rw [hnull]; exact zero_le
  · -- Main case: K > 0.
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (0 : ℝ≥0) < K := lt_of_le_of_ne (zero_le (a := K)) (Ne.symm hK0)
      exact_mod_cast this
    set thr : ℝ := (12 + 4 * u) * (K : ℝ) * G with hthr
    -- Number of chaining levels: past `n` every point has a net point at distance 0.
    obtain ⟨n, hn⟩ := A.exists_eventually_dist_zero hfin hA
    -- Projections onto the admissible levels.
    have hprojmem : ∀ k : ℕ, ∀ t : E, netProj (A.seq k) t ∈ A.seq k :=
      fun k t => netProj_mem (A.nonempty k) t
    have hprojT : ∀ k : ℕ, ∀ t : E, netProj (A.seq k) t ∈ T :=
      fun k t => A.subset_carrier k (Finset.mem_coe.mpr (hprojmem k t))
    have hprojdist : ∀ k : ℕ, ∀ t : E,
        dist t (netProj (A.seq k) t) ≤ Metric.infDist t ↑(A.seq k) := by
      intro k t
      have hcpt : IsCompact (↑(A.seq k) : Set E) := (A.seq k).finite_toSet.isCompact
      have hnek : (↑(A.seq k) : Set E).Nonempty := Finset.coe_nonempty.mpr (A.nonempty k)
      obtain ⟨b, hb_mem, hb_eq⟩ := hcpt.exists_infDist_eq_dist hnek t
      exact dist_netProj_le ⟨b, Finset.mem_coe.mp hb_mem, le_of_eq hb_eq.symm⟩
    -- Chain end: `X (π_n t) = X t` a.e.
    have hfine0 : ∀ t ∈ T, dist t (netProj (A.seq n) t) = 0 := by
      intro t ht
      obtain ⟨a, ha_mem, ha0⟩ := hn n le_rfl t ht
      have hinf0 : Metric.infDist t ↑(A.seq n) = 0 :=
        le_antisymm
          (le_trans (Metric.infDist_le_dist_of_mem (Finset.mem_coe.mpr ha_mem)) ha0.le)
          Metric.infDist_nonneg
      exact le_antisymm (le_trans (hprojdist n t) hinf0.le) dist_nonneg
    have hclean : ∀ᵐ ω ∂μ, ∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω := by
      rw [hfin.eventually_all]
      intro t ht
      have hsub := hinc.sub_ae_eq_zero (hmeas t ht) (hmeas (netProj (A.seq n) t) (hprojT n t))
        ht (hprojT n t) (hfine0 t ht)
      filter_upwards [hsub] with ω hω
      have : X (netProj (A.seq n) t) ω - X t ω = 0 := hω
      linarith
    -- Per-level threshold sequence and pair sets.
    set L₆ : ℝ := Real.sqrt (6 * Real.log 2) with hL6
    have hL6nn : 0 ≤ L₆ := Real.sqrt_nonneg _
    set s : ℕ → ℝ := fun k => Real.sqrt 2 ^ k * L₆ + Real.sqrt ((k : ℝ) + 1) + u with hsdef
    have hs_nn : ∀ k, 0 ≤ s k := fun k =>
      add_nonneg (add_nonneg (mul_nonneg (pow_nonneg hs2nn k) hL6nn) (Real.sqrt_nonneg _)) hu
    set PS : ℕ → Finset (E × E) := fun k => A.seq (k + 1) ×ˢ A.seq k with hPSdef
    -- The γ-functional dominates every finite partial series.
    have hPle : ∀ t ∈ T, ∀ m : ℕ,
        ∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) ≤ G := by
      intro t ht m
      rw [hGdef]
      have h1 : ∑ k ∈ Finset.range m,
            ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
          ≤ gammaFunctional A := by
        refine le_trans (ENNReal.sum_le_tsum (Finset.range m)) ?_
        exact le_iSup₂ (f := fun t (_ : t ∈ T) =>
          ∑' k, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) t ht
      have h2 := ENNReal.toReal_mono hA h1
      rw [ENNReal.toReal_sum (fun k _ => ENNReal.ofReal_ne_top)] at h2
      rw [Finset.sum_congr rfl (fun k _ => ENNReal.toReal_ofReal
        (mul_nonneg (pow_nonneg hs2nn k) Metric.infDist_nonneg))] at h2
      exact h2
    -- Per-pair sub-gaussian tail: `μ {K d(a,b) s_k < |X_a − X_b|} ≤ 2 exp(−s_k²)`.
    have hpair : ∀ k, ∀ p ∈ PS k,
        μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) := by
      intro k p hp
      rw [hPSdef, Finset.mem_product] at hp
      have hp1T : p.1 ∈ T := A.subset_carrier (k + 1) (Finset.mem_coe.mpr hp.1)
      have hp2T : p.2 ∈ T := A.subset_carrier k (Finset.mem_coe.mpr hp.2)
      rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist p.1 p.2) with hd0 | hdpos
      · -- degenerate `dist = 0`: increment vanishes a.e.
        have haez : (fun ω => X p.1 ω - X p.2 ω) =ᵐ[μ] 0 :=
          hinc.sub_ae_eq_zero (hmeas p.2 hp2T) (hmeas p.1 hp1T) hp2T hp1T
            (by rw [dist_comm]; exact hd0.symm)
        have haene : ∀ᵐ ω ∂μ, X p.1 ω - X p.2 ω = 0 := by
          filter_upwards [haez] with ω hω; exact hω
        have hnull : μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} = 0 := by
          refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp haene)
          simp only [Set.mem_setOf_eq] at hω ⊢
          intro h0
          rw [h0, abs_zero] at hω
          have : (0 : ℝ) ≤ (K : ℝ) * dist p.1 p.2 * s k :=
            mul_nonneg (mul_nonneg hKpos.le dist_nonneg) (hs_nn k)
          linarith
        rw [hnull]; exact zero_le
      · -- non-degenerate: B1 tail with an exact exponent.
        have hdpos' : 0 < dist p.2 p.1 := by rw [dist_comm]; exact hdpos
        have hKd : 0 < (K : ℝ) * dist p.2 p.1 := mul_pos hKpos hdpos'
        have hτ0 : 0 ≤ (K : ℝ) * dist p.1 p.2 * s k :=
          mul_nonneg (mul_nonneg hKpos.le dist_nonneg) (hs_nn k)
        have htail := hinc.measure_abs_sub_ge_le (hmeas p.2 hp2T) (hmeas p.1 hp1T)
          hp2T hp1T hKd hτ0
        have hsub01 : {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}
            ⊆ {ω | (K : ℝ) * dist p.1 p.2 * s k ≤ |X p.1 ω - X p.2 ω|} := by
          intro ω h; simp only [Set.mem_setOf_eq] at h ⊢; exact le_of_lt h
        refine le_trans (measure_mono hsub01) (le_trans htail ?_)
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        refine le_of_eq (congrArg Real.exp ?_)
        rw [dist_comm p.1 p.2]
        have hAnz : ((K : ℝ) * dist p.2 p.1) ≠ 0 := hKd.ne'
        field_simp
        try ring
    -- Per-level union bound.
    have hlevel : ∀ k, μ (⋃ p ∈ PS k,
          {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
        ≤ ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
      intro k
      have hreal : ((PS k).card : ℝ) * (2 * Real.exp (-(s k) ^ 2))
          ≤ 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
        set Q : ℝ := 2 ^ (3 * 2 ^ k) with hQ
        have hQpos : 0 < Q := by rw [hQ]; positivity
        have hQ1 : (1 : ℝ) ≤ Q := by rw [hQ]; exact one_le_pow₀ (by norm_num)
        have hMle : ((PS k).card : ℝ) ≤ Q := by
          rw [hPSdef, hQ, Finset.card_product]
          have hc1 : ((A.seq (k + 1)).card : ℝ) ≤ 2 ^ 2 ^ (k + 1) := by
            exact_mod_cast A.card_le (k + 1)
          have hc2 : ((A.seq k).card : ℝ) ≤ 2 ^ 2 ^ k := by exact_mod_cast A.card_le k
          calc (((A.seq (k + 1)).card * (A.seq k).card : ℕ) : ℝ)
              = ((A.seq (k + 1)).card : ℝ) * ((A.seq k).card : ℝ) := by push_cast; ring
            _ ≤ (2 ^ 2 ^ (k + 1) : ℝ) * (2 ^ 2 ^ k : ℝ) :=
                mul_le_mul hc1 hc2 (by positivity) (by positivity)
            _ = (2 : ℝ) ^ (3 * 2 ^ k) := by
                rw [← pow_add]; congr 1; rw [pow_succ]; ring
        have hssq : 6 * 2 ^ k * Real.log 2 + ((k : ℝ) + 1) + u ^ 2 ≤ (s k) ^ 2 := by
          have ha : (0 : ℝ) ≤ Real.sqrt 2 ^ k * L₆ := mul_nonneg (pow_nonneg hs2nn k) hL6nn
          have hb : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
          have hL6sq : L₆ ^ 2 = 6 * Real.log 2 := by rw [hL6, Real.sq_sqrt (by positivity)]
          have hsq1 : (Real.sqrt 2 ^ k * L₆) ^ 2 = 6 * 2 ^ k * Real.log 2 := by
            rw [mul_pow, hw2, hL6sq]; ring
          have hsq2 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
          simp only [hsdef]
          nlinarith [ha, hb, hu, hsq1, hsq2, mul_nonneg ha hb, mul_nonneg ha hu, mul_nonneg hb hu]
        have hQlog : Real.log (Q ^ 2) = 6 * 2 ^ k * Real.log 2 := by
          rw [hQ, ← pow_mul, Real.log_pow]; push_cast; ring
        have hexpQ : Real.exp (-(6 * 2 ^ k * Real.log 2)) = (Q ^ 2)⁻¹ := by
          rw [← hQlog, Real.exp_neg, Real.exp_log (by positivity)]
        have hchain : Real.exp (-(s k) ^ 2)
            ≤ (Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
          calc Real.exp (-(s k) ^ 2)
              ≤ Real.exp (-(6 * 2 ^ k * Real.log 2 + ((k : ℝ) + 1) + u ^ 2)) :=
                Real.exp_le_exp.mpr (by linarith [hssq])
            _ = Real.exp (-(6 * 2 ^ k * Real.log 2)) * Real.exp (-((k : ℝ) + 1))
                  * Real.exp (-u ^ 2) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
            _ = (Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by rw [hexpQ]
        calc ((PS k).card : ℝ) * (2 * Real.exp (-(s k) ^ 2))
            ≤ Q * (2 * ((Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2))) := by
              apply mul_le_mul hMle _ (by positivity) hQpos.le
              exact mul_le_mul_of_nonneg_left hchain (by norm_num)
          _ ≤ 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
              rw [show Q * (2 * ((Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)))
                    = (Q * (Q ^ 2)⁻¹) * (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) from
                    by ring]
              apply mul_le_of_le_one_left (by positivity)
              rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hQpos.ne', one_mul]
              exact (inv_le_one₀ hQpos).mpr hQ1
      calc μ (⋃ p ∈ PS k, {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
          ≤ ∑ p ∈ PS k, μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ _p ∈ PS k, ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) :=
            Finset.sum_le_sum (fun p hp => hpair k p hp)
        _ = (PS k).card • ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) := by rw [Finset.sum_const]
        _ ≤ ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast ((PS k).card),
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hreal
    -- Deterministic threshold sum: `∑ (ρ_{k+1}+ρ_k) s_k ≤ (6+2u) G`.
    have hsumG : ∀ t ∈ T, ∑ k ∈ Finset.range n,
        (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
          ≤ (6 + 2 * u) * G := by
      intro t ht
      have hinfnn : ∀ k : ℕ, (0 : ℝ) ≤ Metric.infDist t ↑(A.seq k) := fun k => Metric.infDist_nonneg
      have hS0 : ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) ≤ G :=
        hPle t ht n
      have hS1 : Real.sqrt 2
          * ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)) ≤ G := by
        have heq : Real.sqrt 2
              * ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
            = ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
        rw [heq]
        calc ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1))
            ≤ ∑ k ∈ Finset.range (n + 1), Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) := by
              rw [Finset.sum_range_succ' (fun k => Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)) n]
              have h0 : (0 : ℝ) ≤ Real.sqrt 2 ^ 0 * Metric.infDist t ↑(A.seq 0) :=
                mul_nonneg (by positivity) (hinfnn 0)
              linarith
          _ ≤ G := hPle t ht (n + 1)
      have hR0 : ∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq k) ≤ G := by
        refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) hS0
        have h1 : (1 : ℝ) ≤ Real.sqrt 2 ^ k := one_le_pow₀ hs2ge1
        nlinarith [hinfnn k, h1]
      have hR1 : ∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1)) ≤ G := by
        have hstep : ∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1))
            ≤ ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1)) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have h1 : (1 : ℝ) ≤ Real.sqrt 2 ^ (k + 1) := one_le_pow₀ hs2ge1
          nlinarith [hinfnn (k + 1), h1]
        have heq : ∑ k ∈ Finset.range n, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1))
            = Real.sqrt 2
              * ∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
        rw [heq] at hstep; linarith [hstep, hS1]
      -- key numeric slack.
      have key0 : (L₆ + 1) * (Real.sqrt 2 + 1) ≤ 6 * Real.sqrt 2 := by
        have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have hL6sq : L₆ ^ 2 = 6 * Real.log 2 := by rw [hL6, Real.sq_sqrt (by positivity)]
        have hL6bd : L₆ ≤ 2.04 := by nlinarith [hL6sq, hL6nn, hlog]
        have hs2lb : 1.414 ≤ Real.sqrt 2 := by nlinarith [hs2sq, hs2nn]
        have hs2ub : Real.sqrt 2 ≤ 1.4143 := by nlinarith [hs2sq, hs2nn]
        nlinarith [hL6bd, hL6nn, hs2lb, hs2ub, mul_nonneg hL6nn hs2nn]
      -- per-term bound `(ρ_{k+1}+ρ_k) s_k ≤ (L₆+1)(√2^k ρ_{k+1} + √2^k ρ_k) + u(ρ_{k+1}+ρ_k)`.
      have hterm_le : ∀ k ∈ Finset.range n,
          (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
            ≤ (L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
              + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) := by
        intro k _
        have hsqrtk : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt 2 ^ k := by
          have hk2 : (k : ℝ) + 1 ≤ 2 ^ k := by
            exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self)
          have hle2 : Real.sqrt ((k : ℝ) + 1) ^ 2 ≤ (Real.sqrt 2 ^ k) ^ 2 := by
            rw [Real.sq_sqrt (by positivity), hw2]; exact hk2
          exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (pow_nonneg hs2nn k) two_ne_zero).mp hle2
        have hsk : s k ≤ Real.sqrt 2 ^ k * (L₆ + 1) + u := by
          simp only [hsdef]; nlinarith [hsqrtk, pow_nonneg hs2nn k, hL6nn]
        have hnn : (0 : ℝ) ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) :=
          add_nonneg (hinfnn (k + 1)) (hinfnn k)
        calc (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
            ≤ (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k))
                * (Real.sqrt 2 ^ k * (L₆ + 1) + u) := mul_le_mul_of_nonneg_left hsk hnn
          _ = (L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
              + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) := by ring
      calc ∑ k ∈ Finset.range n,
            (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
          ≤ ∑ k ∈ Finset.range n,
              ((L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                  + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
                + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k))) :=
            Finset.sum_le_sum hterm_le
        _ = (L₆ + 1) * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
              + u * ((∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1)))
                + (∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq k))) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ (6 + 2 * u) * G := by
            have hL1nn : (0 : ℝ) ≤ L₆ + 1 := by linarith [hL6nn]
            have hs2pos : (0 : ℝ) < Real.sqrt 2 := by linarith [hs2ge1]
            have hLpart : (L₆ + 1)
                * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                  + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
                ≤ 6 * G := by
              have hb : Real.sqrt 2
                    * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                  + Real.sqrt 2
                    * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
                  ≤ G + Real.sqrt 2 * G := by
                have := mul_le_mul_of_nonneg_left hS0 hs2pos.le
                linarith [hS1, this]
              have hkey : Real.sqrt 2 * ((L₆ + 1)
                    * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))))
                  ≤ Real.sqrt 2 * (6 * G) := by
                have hstep : Real.sqrt 2 * ((L₆ + 1)
                      * ((∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                        + (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))))
                    = (L₆ + 1) * (Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) := by
                  ring
                rw [hstep]
                calc (L₆ + 1) * (Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + Real.sqrt 2
                        * (∑ k ∈ Finset.range n, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
                    ≤ (L₆ + 1) * (G + Real.sqrt 2 * G) := mul_le_mul_of_nonneg_left hb hL1nn
                  _ = (L₆ + 1) * (Real.sqrt 2 + 1) * G := by ring
                  _ ≤ 6 * Real.sqrt 2 * G := by nlinarith [key0, hG0]
                  _ = Real.sqrt 2 * (6 * G) := by ring
              exact le_of_mul_le_mul_left hkey hs2pos
            have hupart : u * ((∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq (k + 1)))
                  + (∑ k ∈ Finset.range n, Metric.infDist t ↑(A.seq k))) ≤ 2 * u * G := by
              nlinarith [mul_nonneg hu (sub_nonneg.mpr hR1), mul_nonneg hu (sub_nonneg.mpr hR0)]
            nlinarith [hLpart, hupart]
    -- On the good event the anchored sup is ≤ (6+2u) K G.
    have hgood : ∀ ω, (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω) →
        (∀ k ∈ Finset.range n, ∀ p ∈ PS k,
          ¬ ((K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|)) →
        (⨆ t ∈ T, |X t ω - X a₀ ω|) ≤ (6 + 2 * u) * (K : ℝ) * G := by
      intro ω hω hnb
      rw [← setToF (fun t => |X t ω - X a₀ ω|),
        biSup_finset_eq_sup' hFne _ (fun _ _ => abs_nonneg _)]
      refine Finset.sup'_le hFne _ (fun t htF => ?_)
      have htT := hmemT t htF
      have htel : X t ω - X a₀ ω = ∑ k ∈ Finset.range n,
          (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω) := by
        have h0 : X (netProj (A.seq 0) t) ω = X a₀ ω := by rw [hπ0 t]
        have hnn : X (netProj (A.seq n) t) ω = X t ω := hω t htT
        rw [← hnn, ← h0]
        exact chain_telescope (fun i => X (netProj (A.seq i) t) ω)
      have hpb : ∀ k ∈ Finset.range n,
          |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k := by
        intro k hk
        have hpair_mem : (netProj (A.seq (k + 1)) t, netProj (A.seq k) t) ∈ PS k := by
          rw [hPSdef, Finset.mem_product]; exact ⟨hprojmem (k + 1) t, hprojmem k t⟩
        have hnot := hnb k hk _ hpair_mem
        push_neg at hnot
        have hdle : dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t)
            ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) := by
          calc dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t)
              ≤ dist (netProj (A.seq (k + 1)) t) t + dist t (netProj (A.seq k) t) :=
                dist_triangle _ _ _
            _ = dist t (netProj (A.seq (k + 1)) t) + dist t (netProj (A.seq k) t) := by
                rw [dist_comm (netProj (A.seq (k + 1)) t) t]
            _ ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) :=
                add_le_add (hprojdist (k + 1) t) (hprojdist k t)
        calc |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ (K : ℝ) * dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t) * s k := hnot
          _ ≤ (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k := by
              apply mul_le_mul_of_nonneg_right _ (hs_nn k)
              exact mul_le_mul_of_nonneg_left hdle hKpos.le
      calc |X t ω - X a₀ ω|
          = |∑ k ∈ Finset.range n,
              (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω)| := by rw [htel]
        _ ≤ ∑ k ∈ Finset.range n,
              |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n,
              (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k :=
            Finset.sum_le_sum hpb
        _ = (K : ℝ) * ∑ k ∈ Finset.range n,
              (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
        _ ≤ (K : ℝ) * ((6 + 2 * u) * G) :=
            mul_le_mul_of_nonneg_left (hsumG t htT) hKpos.le
        _ = (6 + 2 * u) * (K : ℝ) * G := by ring
    -- Arbitrary anchor is at most twice the canonical one.
    have hreduce : ∀ ω, (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ 2 * ⨆ t ∈ T, |X t ω - X a₀ ω| := by
      intro ω
      have hHnn : (0 : ℝ) ≤ ⨆ t ∈ T, |X t ω - X a₀ ω| := by
        rw [← setToF (fun t => |X t ω - X a₀ ω|)]
        exact le_trans (abs_nonneg _)
          (le_biSup_finset (fun t => |X t ω - X a₀ ω|) (hfin.mem_toFinset.mpr ha₀T))
      refine biSup_le_of_finite hfin hne _ (fun t htT => ?_)
        (mul_nonneg (by norm_num) hHnn)
      have hta : |X t ω - X a₀ ω| ≤ ⨆ t' ∈ T, |X t' ω - X a₀ ω| :=
        le_biSup_of_finite hfin (fun t' => |X t' ω - X a₀ ω|) htT
      have ht0a : |X t₀ ω - X a₀ ω| ≤ ⨆ t' ∈ T, |X t' ω - X a₀ ω| :=
        le_biSup_of_finite hfin (fun t' => |X t' ω - X a₀ ω|) ht₀
      have htri := abs_sub_le (X t ω) (X a₀ ω) (X t₀ ω)
      have hcomm : |X a₀ ω - X t₀ ω| = |X t₀ ω - X a₀ ω| := abs_sub_comm _ _
      rw [hcomm] at htri
      linarith [hta, ht0a, htri]
    -- The bad set collects all per-level pair-events.
    set BAD : Set Ω := ⋃ k ∈ Finset.range n, ⋃ p ∈ PS k,
      {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} with hBAD
    have hBADmeas : μ BAD ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
      rw [hBAD]
      calc μ (⋃ k ∈ Finset.range n, ⋃ p ∈ PS k,
              {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
          ≤ ∑ k ∈ Finset.range n, μ (⋃ p ∈ PS k,
              {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}) :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ k ∈ Finset.range n,
              ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) :=
            Finset.sum_le_sum (fun k _ => hlevel k)
        _ = ENNReal.ofReal
              (∑ k ∈ Finset.range n, 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
        _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [show (∑ k ∈ Finset.range n, 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2))
                  = (2 * Real.exp (-u ^ 2)) * ∑ k ∈ Finset.range n, Real.exp (-((k : ℝ) + 1)) from
                by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)]
            have hle := mul_le_mul_of_nonneg_left (sum_exp_neg_succ_le_one n)
              (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-u ^ 2))
            linarith [hle]
    -- The target event is contained in `BAD` plus the null clean-complement.
    have hincl : {ω | thr < ⨆ t ∈ T, |X t ω - X t₀ ω|}
        ⊆ BAD ∪ {ω | ¬ (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      by_contra hcon
      rw [Set.mem_union, not_or] at hcon
      obtain ⟨hnBAD, hnclean⟩ := hcon
      simp only [Set.mem_setOf_eq, not_not] at hnclean
      have hnb : ∀ k ∈ Finset.range n, ∀ p ∈ PS k,
          ¬ ((K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|) := by
        intro k hk p hp hlt
        exact hnBAD (by rw [hBAD]; exact Set.mem_biUnion hk (Set.mem_biUnion hp hlt))
      have hb := hgood ω hnclean hnb
      have hle : (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ thr := by
        rw [hthr]
        calc ⨆ t ∈ T, |X t ω - X t₀ ω| ≤ 2 * ⨆ t ∈ T, |X t ω - X a₀ ω| := hreduce ω
          _ ≤ 2 * ((6 + 2 * u) * (K : ℝ) * G) := by linarith [hb]
          _ = (12 + 4 * u) * (K : ℝ) * G := by ring
      linarith [hω, hle]
    calc μ {ω | thr < ⨆ t ∈ T, |X t ω - X t₀ ω|}
        ≤ μ (BAD ∪ {ω | ¬ (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω)}) := measure_mono hincl
      _ ≤ μ BAD + μ {ω | ¬ (∀ t ∈ T, X (netProj (A.seq n) t) ω = X t ω)} := measure_union_le _ _
      _ = μ BAD := by rw [ae_iff.mp hclean, add_zero]
      _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := hBADmeas

/-- Generic chaining, expectation form at a fixed admissible sequence (HDP
§8.5.2 + Remark 8.5.3 — no mean-zero for the `|X_t − X_{t₀}|` form).
Frozen constant `20` (formula `6 + 2√π ≤ 10`), integrating
`generic_chaining_tail_of_finite` via `TailToExpectation`. -/
theorem generic_chaining_of_admissible_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {t₀ : E}
    -- LEAN-ONLY: anchor point
    (ht₀ : t₀ ∈ T)
    (A : AdmissibleSequence T) :
    ENNReal.ofReal (∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ) ≤
      20 * K * gammaFunctional A := by
  -- Measurability and nonnegativity of the increment sup.
  have hZm : AEMeasurable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => |X t ω - X t₀ ω|)
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
  have hZ0 : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω| := by
    filter_upwards with ω
    exact Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
  by_cases hK0 : K = 0
  · -- K = 0: all increments vanish a.e., so the sup is a.e. 0.
    subst hK0
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff hfin.countable]
      intro t ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t ht
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas t₀ ht₀)) hnorm
    have hZae : (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      have hup : (⨆ t ∈ T, |X t ω - X t₀ ω|) ≤ 0 :=
        biSup_le_of_finite hfin hne _ (fun s hs => by rw [hω s hs]; simp) le_rfl
      have hlo : (0 : ℝ) ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _))
      simp only [Pi.zero_apply]
      linarith
    rw [integral_congr_ae hZae]
    simp
  · by_cases hγ : gammaFunctional A = ⊤
    · rw [hγ, ENNReal.mul_top (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr hK0))]
      exact le_top
    · -- Main case: integrate the tail bound via `TailToExpectation`.
      have ha0 : (0 : ℝ) ≤ 12 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have hb0 : (0 : ℝ) ≤ 4 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have htail : ∀ u : ℝ, 0 ≤ u →
          μ {ω | 12 * (K : ℝ) * (gammaFunctional A).toReal
                + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
              < ⨆ t ∈ T, |X t ω - X t₀ ω|}
            ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
        intro u hu
        have hval := generic_chaining_tail_of_finite hfin hne hmeas hinc ht₀ A hγ hu
        have hthr : 12 * (K : ℝ) * (gammaFunctional A).toReal
              + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
            = (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal := by ring
        have hset : {ω | 12 * (K : ℝ) * (gammaFunctional A).toReal
                + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
              < ⨆ t ∈ T, |X t ω - X t₀ ω|}
            = {ω | (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal
              < ⨆ t ∈ T, |X t ω - X t₀ ω|} := by
          ext ω; simp only [Set.mem_setOf_eq, hthr]
        rw [hset]; exact hval
      have hInt : ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
          ≤ 12 * (K : ℝ) * (gammaFunctional A).toReal
            + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal) :=
        integral_le_of_tail_le hZm hZ0 ha0 hb0 htail
      have hc : (0 : ℝ) ≤ (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg K.coe_nonneg ENNReal.toReal_nonneg
      have hsqrt : Real.sqrt Real.pi ≤ 2 := by
        nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_lt_d2]
      have hmid : 12 * (K : ℝ) * (gammaFunctional A).toReal
          + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal)
          ≤ 20 * (K : ℝ) * (gammaFunctional A).toReal := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hc, hc, hsqrt]
      have hfinal : ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal)
          = 20 * ↑K * gammaFunctional A := by
        rw [show (20 : ℝ) * (K : ℝ) * (gammaFunctional A).toReal
              = 20 * ((K : ℝ) * (gammaFunctional A).toReal) from by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20),
            ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_toReal hγ, ENNReal.ofReal_ofNat]
        ring
      calc ENNReal.ofReal (∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ)
          ≤ ENNReal.ofReal (12 * (K : ℝ) * (gammaFunctional A).toReal
              + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal)) :=
            ENNReal.ofReal_le_ofReal hInt
        _ ≤ ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal) :=
            ENNReal.ofReal_le_ofReal hmid
        _ = 20 * ↑K * gammaFunctional A := hfinal

/-- **Theorem 8.5.2 (generic chaining bound)** (HDP §8.5.2; book's absolute
constant frozen `C = 20`, from the renegotiated tail `(12 + 4u)`): mean-zero
process with sub-Gaussian increments has `E max_{t ∈ T} X_t ≤ 20·K·γ₂(T,d)`,
in `ofReal` form.

Carrier note (statement fix at the debt gate): the finite maximum is stated
with the junk-free `Finset.sup'` carrier — the previous set-bounded
`⨆ t ∈ T, X t ω` form was **false** at `|T| = 1` (left side `∫ (X_{t₀})⁺ > 0`
against `γ₂ = 0`); see `discrete_dudley_of_finite` for the same renegotiation. -/
theorem generic_chaining_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index (book WLOG; sup policy core)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability of the process, ruling out Bochner-junk
    -- means (batch reconciliation R4; the book's E X_t = 0 presupposes it)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ENNReal.ofReal
        (∫ ω, hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hne) (fun t => X t ω) ∂μ)
      ≤ 20 * K * gammaTwo T := by
  -- Anchor at a point of `T` (Remark 8.5.3 device).
  set t₀ := hne.some with ht₀def
  have ht₀ : t₀ ∈ T := hne.some_mem
  have hFne : hfin.toFinset.Nonempty := hfin.toFinset_nonempty.mpr hne
  -- Measurability of the anchored abs increment sup.
  have hWm : AEMeasurable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ :=
    aemeasurable_biSup_of_finite hfin (g := fun t ω => |X t ω - X t₀ ω|)
      (fun t ht => ((hmeas t ht).sub (hmeas t₀ ht₀)).abs)
  -- Integrability of the increment sup via domination by a finite sum.
  have hSumInt : Integrable (fun ω => ∑ t ∈ hfin.toFinset, |X t ω - X t₀ ω|) μ :=
    integrable_finset_sum _
      (fun t ht => ((hint t (hfin.mem_toFinset.mp ht)).sub (hint t₀ ht₀)).abs)
  have hWint : Integrable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ := by
    refine Integrable.mono' hSumInt hWm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.iSup_nonneg (fun t => Real.iSup_nonneg (fun _ => abs_nonneg _)))]
    exact biSup_le_of_finite hfin ⟨t₀, ht₀⟩ _
      (fun s hs => Finset.single_le_sum (f := fun t => |X t ω - X t₀ ω|)
        (fun i _ => abs_nonneg _) (hfin.mem_toFinset.mpr hs))
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  -- Integrability of the (junk-free) process max.
  have hSXint : Integrable
      (fun ω => hfin.toFinset.sup' hFne (fun t => X t ω)) μ :=
    integrable_sup'_finset hFne (fun t ht => hint t (hfin.mem_toFinset.mp ht))
  -- E max X ≤ E sup |X − X t₀| (mean-zero anchor cancels).
  have hred : ∫ ω, hfin.toFinset.sup' hFne (fun t => X t ω) ∂μ
      ≤ ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ := by
    have hbound : ∫ ω, hfin.toFinset.sup' hFne (fun t => X t ω) ∂μ
        ≤ ∫ ω, (X t₀ ω + ⨆ t ∈ T, |X t ω - X t₀ ω|) ∂μ := by
      refine integral_mono hSXint ((hint t₀ ht₀).add hWint) (fun ω => ?_)
      refine Finset.sup'_le hFne _ (fun s hs => ?_)
      have h1 : |X s ω - X t₀ ω| ≤ ⨆ t ∈ T, |X t ω - X t₀ ω| :=
        le_biSup_of_finite hfin (fun r => |X r ω - X t₀ ω|) (hfin.mem_toFinset.mp hs)
      have h2 := le_abs_self (X s ω - X t₀ ω)
      linarith
    rwa [integral_add (hint t₀ ht₀) hWint, hmean t₀ ht₀, zero_add] at hbound
  refine le_trans (ENNReal.ofReal_le_ofReal hred) ?_
  haveI : Nonempty (AdmissibleSequence T) := nonempty_admissibleSequence hne
  have ha_top : (20 : ℝ≥0∞) * ↑K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have hpush : (20 : ℝ≥0∞) * ↑K * gammaTwo T
      = ⨅ A : AdmissibleSequence T, 20 * ↑K * gammaFunctional A := by
    rw [show gammaTwo T = ⨅ A : AdmissibleSequence T, gammaFunctional A from rfl]
    exact ENNReal.mul_iInf (fun h => absurd h ha_top)
  rw [hpush]
  exact le_iInf (fun A => generic_chaining_of_admissible_of_finite hfin hne hmeas hinc ht₀ A)

/-- Theorem 8.5.2, real display (LEAN-ONLY: via `gammaTwo_lt_top_of_finite`
the `ℝ≥0∞` bound descends to `ℝ`; `Finset.sup'` carrier as in
`generic_chaining_of_finite`). -/
theorem generic_chaining_real_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: finite index
    (hfin : T.Finite)
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability (R4, as above)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hne) (fun t => X t ω) ∂μ
      ≤ 20 * K * (gammaTwo T).toReal := by
  have h3 := generic_chaining_of_finite hfin hne hmeas hint hmean hinc
  have htop : (20 : ℝ≥0∞) * ↑K * gammaTwo T ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top)
      (gammaTwo_lt_top_of_finite hfin hne).ne
  rw [ENNReal.ofReal_le_iff_le_toReal htop, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal] at h3
  exact h3

/-! ### Faithful general forms (arbitrary `T`; HDP Remark 7.2.1)

Theorem 8.5.2 is stated in HDP for a mean-zero process on a general metric
space `(T, d)` (its proof's WLOG-to-finite, p. 247 Step 1, cites Remark
7.2.1). Unlike the Dudley family, no covering package is needed: admissible
sequences carry all the geometry, `gammaTwo` is already an honest `ℝ≥0∞`
(`⊤` at divergence, no junk), and the `γ₂ = ⊤` case is trivial. The chain
for a finite subset `F ⊆ T` walks the sequence's levels inside `T` and is
truncated; the residual is controlled by
`sqrt_two_pow_mul_infDist_le_toReal_gammaFunctional` (each `d(t, T_k)` is
`≤ toReal·(√2)^{−k} → 0`, uniformly on `F`), replacing the finite-`T`
chain-end device `exists_eventually_dist_zero`. -/

/-- **Generic chaining, tail form** (HDP §8.5.2, Eq. (8.50); faithful
general-`T` form): for every finite subset `F ⊆ T`, the anchored maximum
exceeds `(12 + 4u)·K·(γ₂-series)` with probability at most `2e^{−u²}`. -/
theorem generic_chaining_tail {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
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
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    μ {ω | (12 + 4 * u) * K * (gammaFunctional A).toReal <
        F.sup' hFne (fun t => |X t ω - X t₀ ω|)} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
  classical
  set G : ℝ := (gammaFunctional A).toReal with hGdef
  have hG0 : 0 ≤ G := ENNReal.toReal_nonneg
  have hmemT : ∀ t ∈ F, t ∈ T := fun t ht => hF (Finset.mem_coe.mpr ht)
  -- Canonical anchor `a₀` = the seq-0 singleton point.
  obtain ⟨a₀, ha₀seq⟩ := Finset.card_eq_one.mp A.card_zero
  have ha₀mem : a₀ ∈ A.seq 0 := by rw [ha₀seq]; exact Finset.mem_singleton_self a₀
  have ha₀T : a₀ ∈ T := A.subset_carrier 0 (Finset.mem_coe.mpr ha₀mem)
  have hπ0 : ∀ t : E, netProj (A.seq 0) t = a₀ := by
    intro t; rw [ha₀seq]
    have hmem := netProj_mem (Finset.singleton_nonempty a₀) t
    rwa [Finset.mem_singleton] at hmem
  -- √2 bricks.
  have hs2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2ge1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith [hs2sq, hs2nn]
  have hs2pos : (0 : ℝ) < Real.sqrt 2 := by linarith [hs2ge1]
  have hs2gt1 : (1 : ℝ) < Real.sqrt 2 := by nlinarith [hs2sq, hs2nn]
  have hw2 : ∀ k : ℕ, (Real.sqrt 2 ^ k) ^ 2 = 2 ^ k := by
    intro k
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hK0 : K = 0
  · -- K = 0: all increments vanish a.e., so the anchored sup is a.e. 0.
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ (↑F : Set E), X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff F.countable_toSet]
      intro t ht
      have htT := hF ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t htT
        rw [hK0] at h
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t htT).sub (hmeas t₀ ht₀)) hnorm
    have hallz : ∀ᵐ ω ∂μ, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ≤ 0 := by
      filter_upwards [hz] with ω hω
      refine Finset.sup'_le hFne _ (fun s hs => ?_)
      rw [hω s (Finset.mem_coe.mpr hs), abs_zero]
    have hthr0 : (12 + 4 * u) * (K : ℝ) * G = 0 := by rw [hK0]; simp
    rw [hthr0]
    have hnull : μ {ω | (0 : ℝ) < F.sup' hFne (fun t => |X t ω - X t₀ ω|)} = 0 := by
      refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp hallz)
      simp only [Set.mem_setOf_eq, not_le]; exact hω
    rw [hnull]; exact zero_le
  · -- Main case: K > 0.
    have hKnn : (0 : ℝ≥0) < K := lt_of_le_of_ne (zero_le (a := K)) (Ne.symm hK0)
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKnn
    set thr : ℝ := (12 + 4 * u) * (K : ℝ) * G with hthr
    -- Projections onto the admissible levels.
    have hprojmem : ∀ k : ℕ, ∀ t : E, netProj (A.seq k) t ∈ A.seq k :=
      fun k t => netProj_mem (A.nonempty k) t
    have hprojT : ∀ k : ℕ, ∀ t : E, netProj (A.seq k) t ∈ T :=
      fun k t => A.subset_carrier k (Finset.mem_coe.mpr (hprojmem k t))
    have hprojdist : ∀ k : ℕ, ∀ t : E,
        dist t (netProj (A.seq k) t) ≤ Metric.infDist t ↑(A.seq k) := by
      intro k t
      have hcpt : IsCompact (↑(A.seq k) : Set E) := (A.seq k).finite_toSet.isCompact
      have hnek : (↑(A.seq k) : Set E).Nonempty := Finset.coe_nonempty.mpr (A.nonempty k)
      obtain ⟨b, hb_mem, hb_eq⟩ := hcpt.exists_infDist_eq_dist hnek t
      exact dist_netProj_le ⟨b, Finset.mem_coe.mp hb_mem, le_of_eq hb_eq.symm⟩
    -- infDist decays like `G·(√2)^{−m}`.
    have hinfle : ∀ t ∈ T, ∀ m : ℕ,
        Metric.infDist t ↑(A.seq m) ≤ G / Real.sqrt 2 ^ m := by
      intro t ht m
      have h := sqrt_two_pow_mul_infDist_le_toReal_gammaFunctional A hA ht m
      rw [mul_comm] at h
      exact (le_div_iff₀ (pow_pos hs2pos m)).mpr h
    -- Per-level threshold sequence and pair sets.
    set L₆ : ℝ := Real.sqrt (6 * Real.log 2) with hL6
    have hL6nn : 0 ≤ L₆ := Real.sqrt_nonneg _
    set s : ℕ → ℝ := fun k => Real.sqrt 2 ^ k * L₆ + Real.sqrt ((k : ℝ) + 1) + u with hsdef
    have hs_nn : ∀ k, 0 ≤ s k := fun k =>
      add_nonneg (add_nonneg (mul_nonneg (pow_nonneg hs2nn k) hL6nn) (Real.sqrt_nonneg _)) hu
    set PS : ℕ → Finset (E × E) := fun k => A.seq (k + 1) ×ˢ A.seq k with hPSdef
    -- The γ-functional dominates every finite partial series.
    have hPle : ∀ t ∈ T, ∀ m : ℕ,
        ∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) ≤ G := by
      intro t ht m
      rw [hGdef]
      have h1 : ∑ k ∈ Finset.range m,
            ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
          ≤ gammaFunctional A := by
        refine le_trans (ENNReal.sum_le_tsum (Finset.range m)) ?_
        exact le_iSup₂ (f := fun t (_ : t ∈ T) =>
          ∑' k, ENNReal.ofReal (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) t ht
      have h2 := ENNReal.toReal_mono hA h1
      rw [ENNReal.toReal_sum (fun k _ => ENNReal.ofReal_ne_top)] at h2
      rw [Finset.sum_congr rfl (fun k _ => ENNReal.toReal_ofReal
        (mul_nonneg (pow_nonneg hs2nn k) Metric.infDist_nonneg))] at h2
      exact h2
    -- Per-pair sub-gaussian tail.
    have hpair : ∀ k, ∀ p ∈ PS k,
        μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}
          ≤ ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) := by
      intro k p hp
      rw [hPSdef, Finset.mem_product] at hp
      have hp1T : p.1 ∈ T := A.subset_carrier (k + 1) (Finset.mem_coe.mpr hp.1)
      have hp2T : p.2 ∈ T := A.subset_carrier k (Finset.mem_coe.mpr hp.2)
      rcases eq_or_lt_of_le (dist_nonneg : (0 : ℝ) ≤ dist p.1 p.2) with hd0 | hdpos
      · have haez : (fun ω => X p.1 ω - X p.2 ω) =ᵐ[μ] 0 :=
          hinc.sub_ae_eq_zero (hmeas p.2 hp2T) (hmeas p.1 hp1T) hp2T hp1T
            (by rw [dist_comm]; exact hd0.symm)
        have haene : ∀ᵐ ω ∂μ, X p.1 ω - X p.2 ω = 0 := by
          filter_upwards [haez] with ω hω; exact hω
        have hnull : μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} = 0 := by
          refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp haene)
          simp only [Set.mem_setOf_eq] at hω ⊢
          intro h0
          rw [h0, abs_zero] at hω
          have : (0 : ℝ) ≤ (K : ℝ) * dist p.1 p.2 * s k :=
            mul_nonneg (mul_nonneg hKpos.le dist_nonneg) (hs_nn k)
          linarith
        rw [hnull]; exact zero_le
      · have hdpos' : 0 < dist p.2 p.1 := by rw [dist_comm]; exact hdpos
        have hKd : 0 < (K : ℝ) * dist p.2 p.1 := mul_pos hKpos hdpos'
        have hτ0 : 0 ≤ (K : ℝ) * dist p.1 p.2 * s k :=
          mul_nonneg (mul_nonneg hKpos.le dist_nonneg) (hs_nn k)
        have htail := hinc.measure_abs_sub_ge_le (hmeas p.2 hp2T) (hmeas p.1 hp1T)
          hp2T hp1T hKd hτ0
        have hsub01 : {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}
            ⊆ {ω | (K : ℝ) * dist p.1 p.2 * s k ≤ |X p.1 ω - X p.2 ω|} := by
          intro ω h; simp only [Set.mem_setOf_eq] at h ⊢; exact le_of_lt h
        refine le_trans (measure_mono hsub01) (le_trans htail ?_)
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        refine le_of_eq (congrArg Real.exp ?_)
        rw [dist_comm p.1 p.2]
        have hAnz : ((K : ℝ) * dist p.2 p.1) ≠ 0 := hKd.ne'
        field_simp
        try ring
    -- Per-level union bound.
    have hlevel : ∀ k, μ (⋃ p ∈ PS k,
          {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
        ≤ ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
      intro k
      have hreal : ((PS k).card : ℝ) * (2 * Real.exp (-(s k) ^ 2))
          ≤ 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
        set Q : ℝ := 2 ^ (3 * 2 ^ k) with hQ
        have hQpos : 0 < Q := by rw [hQ]; positivity
        have hQ1 : (1 : ℝ) ≤ Q := by rw [hQ]; exact one_le_pow₀ (by norm_num)
        have hMle : ((PS k).card : ℝ) ≤ Q := by
          rw [hPSdef, hQ, Finset.card_product]
          have hc1 : ((A.seq (k + 1)).card : ℝ) ≤ 2 ^ 2 ^ (k + 1) := by
            exact_mod_cast A.card_le (k + 1)
          have hc2 : ((A.seq k).card : ℝ) ≤ 2 ^ 2 ^ k := by exact_mod_cast A.card_le k
          calc (((A.seq (k + 1)).card * (A.seq k).card : ℕ) : ℝ)
              = ((A.seq (k + 1)).card : ℝ) * ((A.seq k).card : ℝ) := by push_cast; ring
            _ ≤ (2 ^ 2 ^ (k + 1) : ℝ) * (2 ^ 2 ^ k : ℝ) :=
                mul_le_mul hc1 hc2 (by positivity) (by positivity)
            _ = (2 : ℝ) ^ (3 * 2 ^ k) := by
                rw [← pow_add]; congr 1; rw [pow_succ]; ring
        have hssq : 6 * 2 ^ k * Real.log 2 + ((k : ℝ) + 1) + u ^ 2 ≤ (s k) ^ 2 := by
          have ha : (0 : ℝ) ≤ Real.sqrt 2 ^ k * L₆ := mul_nonneg (pow_nonneg hs2nn k) hL6nn
          have hb : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := Real.sqrt_nonneg _
          have hL6sq : L₆ ^ 2 = 6 * Real.log 2 := by rw [hL6, Real.sq_sqrt (by positivity)]
          have hsq1 : (Real.sqrt 2 ^ k * L₆) ^ 2 = 6 * 2 ^ k * Real.log 2 := by
            rw [mul_pow, hw2, hL6sq]; ring
          have hsq2 : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
          simp only [hsdef]
          nlinarith [ha, hb, hu, hsq1, hsq2, mul_nonneg ha hb, mul_nonneg ha hu, mul_nonneg hb hu]
        have hQlog : Real.log (Q ^ 2) = 6 * 2 ^ k * Real.log 2 := by
          rw [hQ, ← pow_mul, Real.log_pow]; push_cast; ring
        have hexpQ : Real.exp (-(6 * 2 ^ k * Real.log 2)) = (Q ^ 2)⁻¹ := by
          rw [← hQlog, Real.exp_neg, Real.exp_log (by positivity)]
        have hchain : Real.exp (-(s k) ^ 2)
            ≤ (Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
          calc Real.exp (-(s k) ^ 2)
              ≤ Real.exp (-(6 * 2 ^ k * Real.log 2 + ((k : ℝ) + 1) + u ^ 2)) :=
                Real.exp_le_exp.mpr (by linarith [hssq])
            _ = Real.exp (-(6 * 2 ^ k * Real.log 2)) * Real.exp (-((k : ℝ) + 1))
                  * Real.exp (-u ^ 2) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
            _ = (Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by rw [hexpQ]
        calc ((PS k).card : ℝ) * (2 * Real.exp (-(s k) ^ 2))
            ≤ Q * (2 * ((Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2))) := by
              apply mul_le_mul hMle _ (by positivity) hQpos.le
              exact mul_le_mul_of_nonneg_left hchain (by norm_num)
          _ ≤ 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2) := by
              rw [show Q * (2 * ((Q ^ 2)⁻¹ * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)))
                    = (Q * (Q ^ 2)⁻¹) * (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) from
                    by ring]
              apply mul_le_of_le_one_left (by positivity)
              rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ hQpos.ne', one_mul]
              exact (inv_le_one₀ hQpos).mpr hQ1
      calc μ (⋃ p ∈ PS k, {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
          ≤ ∑ p ∈ PS k, μ {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ _p ∈ PS k, ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) :=
            Finset.sum_le_sum (fun p hp => hpair k p hp)
        _ = (PS k).card • ENNReal.ofReal (2 * Real.exp (-(s k) ^ 2)) := by rw [Finset.sum_const]
        _ ≤ ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast ((PS k).card),
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hreal
    -- Deterministic threshold sum for arbitrary truncation level `m`.
    have hsumG : ∀ t ∈ T, ∀ m : ℕ, ∑ k ∈ Finset.range m,
        (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
          ≤ (6 + 2 * u) * G := by
      intro t ht m
      have hinfnn : ∀ k : ℕ, (0 : ℝ) ≤ Metric.infDist t ↑(A.seq k) := fun k => Metric.infDist_nonneg
      have hS0 : ∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) ≤ G :=
        hPle t ht m
      have hS1 : Real.sqrt 2
          * ∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)) ≤ G := by
        have heq : Real.sqrt 2
              * ∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
            = ∑ k ∈ Finset.range m, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
        rw [heq]
        calc ∑ k ∈ Finset.range m, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1))
            ≤ ∑ k ∈ Finset.range (m + 1), Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k) := by
              rw [Finset.sum_range_succ' (fun k => Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)) m]
              have h0 : (0 : ℝ) ≤ Real.sqrt 2 ^ 0 * Metric.infDist t ↑(A.seq 0) :=
                mul_nonneg (by positivity) (hinfnn 0)
              linarith
          _ ≤ G := hPle t ht (m + 1)
      have hR0 : ∑ k ∈ Finset.range m, Metric.infDist t ↑(A.seq k) ≤ G := by
        refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) hS0
        have h1 : (1 : ℝ) ≤ Real.sqrt 2 ^ k := one_le_pow₀ hs2ge1
        nlinarith [hinfnn k, h1]
      have hR1 : ∑ k ∈ Finset.range m, Metric.infDist t ↑(A.seq (k + 1)) ≤ G := by
        have hstep : ∑ k ∈ Finset.range m, Metric.infDist t ↑(A.seq (k + 1))
            ≤ ∑ k ∈ Finset.range m, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1)) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have h1 : (1 : ℝ) ≤ Real.sqrt 2 ^ (k + 1) := one_le_pow₀ hs2ge1
          nlinarith [hinfnn (k + 1), h1]
        have heq : ∑ k ∈ Finset.range m, Real.sqrt 2 ^ (k + 1) * Metric.infDist t ↑(A.seq (k + 1))
            = Real.sqrt 2
              * ∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by rw [pow_succ]; ring)
        rw [heq] at hstep; linarith [hstep, hS1]
      have key0 : (L₆ + 1) * (Real.sqrt 2 + 1) ≤ 6 * Real.sqrt 2 := by
        have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
        have hL6sq : L₆ ^ 2 = 6 * Real.log 2 := by rw [hL6, Real.sq_sqrt (by positivity)]
        have hL6bd : L₆ ≤ 2.04 := by nlinarith [hL6sq, hL6nn, hlog]
        have hs2lb : 1.414 ≤ Real.sqrt 2 := by nlinarith [hs2sq, hs2nn]
        have hs2ub : Real.sqrt 2 ≤ 1.4143 := by nlinarith [hs2sq, hs2nn]
        nlinarith [hL6bd, hL6nn, hs2lb, hs2ub, mul_nonneg hL6nn hs2nn]
      have hterm_le : ∀ k ∈ Finset.range m,
          (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
            ≤ (L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
              + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) := by
        intro k _
        have hsqrtk : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt 2 ^ k := by
          have hk2 : (k : ℝ) + 1 ≤ 2 ^ k := by
            exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self)
          have hle2 : Real.sqrt ((k : ℝ) + 1) ^ 2 ≤ (Real.sqrt 2 ^ k) ^ 2 := by
            rw [Real.sq_sqrt (by positivity), hw2]; exact hk2
          exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (pow_nonneg hs2nn k) two_ne_zero).mp hle2
        have hsk : s k ≤ Real.sqrt 2 ^ k * (L₆ + 1) + u := by
          simp only [hsdef]; nlinarith [hsqrtk, pow_nonneg hs2nn k, hL6nn]
        have hnn : (0 : ℝ) ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) :=
          add_nonneg (hinfnn (k + 1)) (hinfnn k)
        calc (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
            ≤ (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k))
                * (Real.sqrt 2 ^ k * (L₆ + 1) + u) := mul_le_mul_of_nonneg_left hsk hnn
          _ = (L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
              + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) := by ring
      calc ∑ k ∈ Finset.range m,
            (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k
          ≤ ∑ k ∈ Finset.range m,
              ((L₆ + 1) * (Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1))
                  + Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
                + u * (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k))) :=
            Finset.sum_le_sum hterm_le
        _ = (L₆ + 1) * ((∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                + (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
              + u * ((∑ k ∈ Finset.range m, Metric.infDist t ↑(A.seq (k + 1)))
                + (∑ k ∈ Finset.range m, Metric.infDist t ↑(A.seq k))) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ ≤ (6 + 2 * u) * G := by
            have hL1nn : (0 : ℝ) ≤ L₆ + 1 := by linarith [hL6nn]
            have hLpart : (L₆ + 1)
                * ((∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                  + (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
                ≤ 6 * G := by
              have hb : Real.sqrt 2
                    * (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                  + Real.sqrt 2
                    * (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))
                  ≤ G + Real.sqrt 2 * G := by
                have := mul_le_mul_of_nonneg_left hS0 hs2pos.le
                linarith [hS1, this]
              have hkey : Real.sqrt 2 * ((L₆ + 1)
                    * ((∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))))
                  ≤ Real.sqrt 2 * (6 * G) := by
                have hstep : Real.sqrt 2 * ((L₆ + 1)
                      * ((∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                        + (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))))
                    = (L₆ + 1) * (Real.sqrt 2
                        * (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + Real.sqrt 2
                        * (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k))) := by
                  ring
                rw [hstep]
                calc (L₆ + 1) * (Real.sqrt 2
                        * (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq (k + 1)))
                      + Real.sqrt 2
                        * (∑ k ∈ Finset.range m, Real.sqrt 2 ^ k * Metric.infDist t ↑(A.seq k)))
                    ≤ (L₆ + 1) * (G + Real.sqrt 2 * G) := mul_le_mul_of_nonneg_left hb hL1nn
                  _ = (L₆ + 1) * (Real.sqrt 2 + 1) * G := by ring
                  _ ≤ 6 * Real.sqrt 2 * G := by nlinarith [key0, hG0]
                  _ = Real.sqrt 2 * (6 * G) := by ring
              exact le_of_mul_le_mul_left hkey hs2pos
            have hupart : u * ((∑ k ∈ Finset.range m, Metric.infDist t ↑(A.seq (k + 1)))
                  + (∑ k ∈ Finset.range m, Metric.infDist t ↑(A.seq k))) ≤ 2 * u * G := by
              nlinarith [mul_nonneg hu (sub_nonneg.mpr hR1), mul_nonneg hu (sub_nonneg.mpr hR0)]
            nlinarith [hLpart, hupart]
    -- On the good event, the anchored increment splits as chain + residual.
    have hgood : ∀ m : ℕ, ∀ ω,
        (∀ k ∈ Finset.range m, ∀ p ∈ PS k,
          ¬ ((K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|)) →
        ∀ t ∈ T, |X t ω - X a₀ ω|
          ≤ (6 + 2 * u) * (K : ℝ) * G + |X t ω - X (netProj (A.seq m) t) ω| := by
      intro m ω hnb t htT
      have htel : X t ω - X a₀ ω
          = (X t ω - X (netProj (A.seq m) t) ω)
            + ∑ k ∈ Finset.range m,
                (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω) := by
        have hchain : X (netProj (A.seq m) t) ω - X a₀ ω
            = ∑ k ∈ Finset.range m,
                (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω) := by
          have := chain_telescope (fun i => X (netProj (A.seq i) t) ω) (n := m)
          simp only [hπ0] at this
          exact this
        rw [← hchain]; ring
      have hpb : ∀ k ∈ Finset.range m,
          |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1))
                + Metric.infDist t ↑(A.seq k)) * s k := by
        intro k hk
        have hpair_mem : (netProj (A.seq (k + 1)) t, netProj (A.seq k) t) ∈ PS k := by
          rw [hPSdef, Finset.mem_product]; exact ⟨hprojmem (k + 1) t, hprojmem k t⟩
        have hnot := hnb k hk _ hpair_mem
        push_neg at hnot
        have hdle : dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t)
            ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) := by
          calc dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t)
              ≤ dist (netProj (A.seq (k + 1)) t) t + dist t (netProj (A.seq k) t) :=
                dist_triangle _ _ _
            _ = dist t (netProj (A.seq (k + 1)) t) + dist t (netProj (A.seq k) t) := by
                rw [dist_comm (netProj (A.seq (k + 1)) t) t]
            _ ≤ Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k) :=
                add_le_add (hprojdist (k + 1) t) (hprojdist k t)
        calc |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ (K : ℝ) * dist (netProj (A.seq (k + 1)) t) (netProj (A.seq k) t) * s k := hnot
          _ ≤ (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1))
                + Metric.infDist t ↑(A.seq k)) * s k := by
              apply mul_le_mul_of_nonneg_right _ (hs_nn k)
              exact mul_le_mul_of_nonneg_left hdle hKpos.le
      have hsum : ∑ k ∈ Finset.range m,
          |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ (6 + 2 * u) * (K : ℝ) * G := by
        calc ∑ k ∈ Finset.range m,
              |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω|
            ≤ ∑ k ∈ Finset.range m,
                (K : ℝ) * (Metric.infDist t ↑(A.seq (k + 1))
                  + Metric.infDist t ↑(A.seq k)) * s k := Finset.sum_le_sum hpb
          _ = (K : ℝ) * ∑ k ∈ Finset.range m,
                (Metric.infDist t ↑(A.seq (k + 1)) + Metric.infDist t ↑(A.seq k)) * s k := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)
          _ ≤ (K : ℝ) * ((6 + 2 * u) * G) :=
              mul_le_mul_of_nonneg_left (hsumG t htT m) hKpos.le
          _ = (6 + 2 * u) * (K : ℝ) * G := by ring
      calc |X t ω - X a₀ ω|
          = |(X t ω - X (netProj (A.seq m) t) ω)
              + ∑ k ∈ Finset.range m,
                  (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω)| := by rw [htel]
        _ ≤ |X t ω - X (netProj (A.seq m) t) ω|
              + |∑ k ∈ Finset.range m,
                  (X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω)| := abs_add_le _ _
        _ ≤ |X t ω - X (netProj (A.seq m) t) ω|
              + ∑ k ∈ Finset.range m,
                  |X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω| := by
              have := Finset.abs_sum_le_sum_abs
                (fun k => X (netProj (A.seq (k + 1)) t) ω - X (netProj (A.seq k) t) ω)
                (Finset.range m)
              linarith
        _ ≤ |X t ω - X (netProj (A.seq m) t) ω| + (6 + 2 * u) * (K : ℝ) * G := by linarith [hsum]
        _ = (6 + 2 * u) * (K : ℝ) * G + |X t ω - X (netProj (A.seq m) t) ω| := by ring
    -- Enlarged subset containing the anchor, for the residual sup.
    set F' : Finset E := insert t₀ F with hF'def
    have hF'ne : F'.Nonempty := ⟨t₀, Finset.mem_insert_self t₀ F⟩
    have hF'sub : ↑F' ⊆ T := by
      rw [hF'def, Finset.coe_insert]
      exact Set.insert_subset ht₀ hF
    have ht₀F' : t₀ ∈ F' := Finset.mem_insert_self t₀ F
    have hFsubF' : ∀ t ∈ F, t ∈ F' := fun t ht => Finset.mem_insert_of_mem ht
    -- Net radii and residual thresholds.
    set r : ℝ := (Real.sqrt 2)⁻¹ with hrdef
    have hr0 : 0 < r := by rw [hrdef]; positivity
    have hr1 : r < 1 := by rw [hrdef]; rw [inv_lt_one₀ hs2pos]; linarith [hs2ge1]
    have hrinv : r⁻¹ = Real.sqrt 2 := by rw [hrdef, inv_inv]
    set ε : ℕ → ℝ := fun m => (G + 1) * r ^ m with hεdef
    have hεpos : ∀ m, 0 < ε m := fun m => by
      rw [hεdef]; exact mul_pos (by linarith [hG0]) (pow_pos hr0 m)
    have hεm : ∀ m, ε m = (G + 1) * (Real.sqrt 2 ^ m)⁻¹ := fun m => by
      simp only [hεdef, hrdef, inv_pow]
    have hεle : ∀ m, G / Real.sqrt 2 ^ m ≤ ε m := by
      intro m
      rw [hεm m, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    set δ : ℕ → ℝ := fun m => Real.sqrt (ε m) with hδdef
    have hδpos : ∀ m, 0 < δ m := fun m => Real.sqrt_pos.mpr (hεpos m)
    have hδnn : ∀ m, 0 ≤ δ m := fun m => (hδpos m).le
    have hεanti : Antitone ε := by
      intro a b hab
      show (G + 1) * r ^ b ≤ (G + 1) * r ^ a
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr0.le hr1.le hab)
        (by linarith [hG0])
    have hδanti : Antitone δ := fun a b hab => Real.sqrt_le_sqrt (hεanti hab)
    -- `ε m → 0`.
    have hε0 : Filter.Tendsto ε Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun m => (G + 1) * r ^ m) Filter.atTop (nhds ((G + 1) * 0)) :=
        Filter.Tendsto.const_mul _ (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
      rw [mul_zero] at this; exact this
    have hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hε0
      rw [Real.sqrt_zero] at h; exact h
    -- The residual-tail probability tends to `0`.
    have hxeq : ∀ m, -(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2 = -(1 / ((K : ℝ) ^ 2 * ε m)) := by
      intro m
      have hδsq : (δ m) ^ 2 = ε m := by
        show Real.sqrt (ε m) ^ 2 = ε m
        exact Real.sq_sqrt (hεpos m).le
      have hpos : (δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2 = 1 / ((K : ℝ) ^ 2 * ε m) := by
        rw [hδsq, mul_pow]
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring
      rw [neg_div, hpos]
    have hxtop : Filter.Tendsto (fun m => 1 / ((K : ℝ) ^ 2 * ε m)) Filter.atTop Filter.atTop := by
      have hform : ∀ m, 1 / ((K : ℝ) ^ 2 * ε m)
          = (1 / ((K : ℝ) ^ 2 * (G + 1))) * Real.sqrt 2 ^ m := by
        intro m
        have hsm : (Real.sqrt 2 ^ m) ≠ 0 := (pow_pos hs2pos m).ne'
        have hG1 : (0 : ℝ) < G + 1 := by linarith [hG0]
        rw [hεm m]
        field_simp
      rw [Filter.tendsto_congr hform]
      exact Filter.Tendsto.const_mul_atTop (by positivity)
        (tendsto_pow_atTop_atTop_of_one_lt hs2gt1)
    have hexp0 : Filter.Tendsto
        (fun m => Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2)) Filter.atTop (nhds 0) := by
      have hcongr : (fun m => Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2))
          = (fun m => Real.exp (-(1 / ((K : ℝ) ^ 2 * ε m)))) := by
        funext m; rw [hxeq m]
      rw [hcongr]
      exact Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atBot_iff.mpr hxtop)
    -- Assemble the per-level bound and the residual bound at each `m`.
    have hBADmeas : ∀ m : ℕ, μ (⋃ k ∈ Finset.range m, ⋃ p ∈ PS k,
          {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
        ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
      intro m
      calc μ (⋃ k ∈ Finset.range m, ⋃ p ∈ PS k,
              {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|})
          ≤ ∑ k ∈ Finset.range m, μ (⋃ p ∈ PS k,
              {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|}) :=
            measure_biUnion_finset_le _ _
        _ ≤ ∑ k ∈ Finset.range m,
              ENNReal.ofReal (2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) :=
            Finset.sum_le_sum (fun k _ => hlevel k)
        _ = ENNReal.ofReal
              (∑ k ∈ Finset.range m, 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2)) := by
            rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
        _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
            apply ENNReal.ofReal_le_ofReal
            rw [show (∑ k ∈ Finset.range m, 2 * Real.exp (-((k : ℝ) + 1)) * Real.exp (-u ^ 2))
                  = (2 * Real.exp (-u ^ 2)) * ∑ k ∈ Finset.range m, Real.exp (-((k : ℝ) + 1)) from
                by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by ring)]
            have hle := mul_le_mul_of_nonneg_left (sum_exp_neg_succ_le_one m)
              (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-u ^ 2))
            linarith [hle]
    -- The per-`m` containment and measure bound.
    have hSm : ∀ m : ℕ, μ {ω | thr + 2 * δ m < F.sup' hFne (fun t => |X t ω - X t₀ ω|)}
        ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2))
          + ENNReal.ofReal (2 * (F'.card : ℝ)
              * Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2)) := by
      intro m
      set BAD : Set Ω := ⋃ k ∈ Finset.range m, ⋃ p ∈ PS k,
        {ω | (K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|} with hBADdef
      set RES : Set Ω := {ω | δ m < F'.sup' hF'ne
        (fun t => |X t ω - X (netProj (A.seq m) t) ω|)} with hRESdef
      have hincl : {ω | thr + 2 * δ m < F.sup' hFne (fun t => |X t ω - X t₀ ω|)}
          ⊆ BAD ∪ RES := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        by_contra hcon
        rw [Set.mem_union, not_or] at hcon
        obtain ⟨hnBAD, hnRES⟩ := hcon
        have hnb : ∀ k ∈ Finset.range m, ∀ p ∈ PS k,
            ¬ ((K : ℝ) * dist p.1 p.2 * s k < |X p.1 ω - X p.2 ω|) := by
          intro k hk p hp hlt
          exact hnBAD (by rw [hBADdef]; exact Set.mem_biUnion hk (Set.mem_biUnion hp hlt))
        have hRle : F'.sup' hF'ne (fun t => |X t ω - X (netProj (A.seq m) t) ω|) ≤ δ m := by
          rw [hRESdef, Set.mem_setOf_eq, not_lt] at hnRES; exact hnRES
        have hresF' : ∀ t ∈ F', |X t ω - X (netProj (A.seq m) t) ω| ≤ δ m := fun t ht =>
          le_trans (Finset.le_sup' (fun t => |X t ω - X (netProj (A.seq m) t) ω|) ht) hRle
        have hle : F.sup' hFne (fun t => |X t ω - X t₀ ω|) ≤ thr + 2 * δ m := by
          refine Finset.sup'_le hFne _ (fun t ht => ?_)
          have htT := hmemT t ht
          have hga := hgood m ω hnb t htT
          have hgt₀ := hgood m ω hnb t₀ ht₀
          have hrt := hresF' t (hFsubF' t ht)
          have hrt₀ := hresF' t₀ ht₀F'
          have htri : |X t ω - X t₀ ω|
              ≤ |X t ω - X a₀ ω| + |X t₀ ω - X a₀ ω| := by
            have h := abs_sub_le (X t ω) (X a₀ ω) (X t₀ ω)
            rwa [abs_sub_comm (X a₀ ω) (X t₀ ω)] at h
          rw [hthr]
          have hexpand : (12 + 4 * u) * (K : ℝ) * G
              = (6 + 2 * u) * (K : ℝ) * G + (6 + 2 * u) * (K : ℝ) * G := by ring
          rw [hexpand]
          linarith [hga, hgt₀, hrt, hrt₀, htri]
        exact absurd hω (not_lt.mpr hle)
      -- residual measure via `residual_tail_le`.
      have hres_bd : μ RES ≤ ENNReal.ofReal
          (2 * (F'.card : ℝ) * Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2)) := by
        rw [hRESdef]
        exact residual_tail_le hmeas hinc (A.subset_carrier m) (A.nonempty m)
          (hεpos m) hKnn
          (fun t ht => ⟨netProj (A.seq m) t, hprojmem m t,
            le_trans (hprojdist m t) (le_trans (hinfle t ht m) (hεle m))⟩)
          hF'sub hF'ne (hδnn m)
      calc μ {ω | thr + 2 * δ m < F.sup' hFne (fun t => |X t ω - X t₀ ω|)}
          ≤ μ (BAD ∪ RES) := measure_mono hincl
        _ ≤ μ BAD + μ RES := measure_union_le _ _
        _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2))
              + ENNReal.ofReal (2 * (F'.card : ℝ)
                  * Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2)) :=
            add_le_add (hBADmeas m) hres_bd
    -- Limit: the truncated sets increase to the target and the residual vanishes.
    set S : ℕ → Set Ω := fun m => {ω | thr + 2 * δ m < F.sup' hFne (fun t => |X t ω - X t₀ ω|)}
      with hSdef
    have hSmono : Monotone S := by
      intro a b hab ω hω
      rw [hSdef] at hω ⊢
      simp only [Set.mem_setOf_eq] at hω ⊢
      have : thr + 2 * δ b ≤ thr + 2 * δ a := by linarith [hδanti hab]
      linarith [hω]
    have hUnion : (⋃ m, S m) = {ω | thr < F.sup' hFne (fun t => |X t ω - X t₀ ω|)} := by
      ext ω
      simp only [Set.mem_iUnion, hSdef, Set.mem_setOf_eq]
      constructor
      · rintro ⟨m, hm⟩; linarith [hδpos m]
      · intro hlt
        have h2δ0 : Filter.Tendsto (fun m => thr + 2 * δ m) Filter.atTop (nhds thr) := by
          have := (hδ0.const_mul (2 : ℝ)).const_add thr
          rwa [mul_zero, add_zero] at this
        have hev := h2δ0.eventually_lt_const hlt
        obtain ⟨m, hm⟩ := hev.exists
        exact ⟨m, hm⟩
    have hStendsto : Filter.Tendsto (fun m => μ (S m)) Filter.atTop
        (nhds (μ (⋃ m, S m))) := tendsto_measure_iUnion_atTop hSmono
    have hRHStendsto : Filter.Tendsto
        (fun m => ENNReal.ofReal (2 * Real.exp (-u ^ 2))
          + ENNReal.ofReal (2 * (F'.card : ℝ)
              * Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2))) Filter.atTop
        (nhds (ENNReal.ofReal (2 * Real.exp (-u ^ 2)))) := by
      have hgreal : Filter.Tendsto (fun m => 2 * (F'.card : ℝ)
          * Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2)) Filter.atTop (nhds 0) := by
        have := hexp0.const_mul (2 * (F'.card : ℝ))
        rwa [mul_zero] at this
      have hg0 : Filter.Tendsto (fun m => ENNReal.ofReal (2 * (F'.card : ℝ)
          * Real.exp (-(δ m) ^ 2 / ((K : ℝ) * ε m) ^ 2))) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_ofReal.tendsto 0).comp hgreal
        rwa [ENNReal.ofReal_zero] at this
      have := hg0.const_add (ENNReal.ofReal (2 * Real.exp (-u ^ 2)))
      rwa [add_zero] at this
    have hfinal : μ (⋃ m, S m) ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) :=
      le_of_tendsto_of_tendsto' hStendsto hRHStendsto (fun m => hSm m)
    rwa [hUnion] at hfinal

/-- **Generic chaining along an admissible sequence** (HDP §8.5.2; faithful
general-`T` form): `E max_{t∈F} |X_t − X_{t₀}| ≤ 20·K·(γ₂-series of A)` in
`ℝ≥0∞`, for every finite subset `F ⊆ T`; the `⊤` branch is trivial. -/
theorem generic_chaining_of_admissible {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
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
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ) ≤
      20 * K * gammaFunctional A := by
  have hmemT : ∀ t ∈ F, t ∈ T := fun t ht => hF (Finset.mem_coe.mpr ht)
  -- Measurability and nonnegativity of the increment sup.
  have hZm : AEMeasurable (fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|)) μ :=
    aemeasurable_sup'_finset hFne
      (fun t ht => ((hmeas t (hmemT t ht)).sub (hmeas t₀ ht₀)).abs)
  have hZ0 : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|) := by
    filter_upwards with ω
    obtain ⟨a, ha⟩ := hFne
    exact (abs_nonneg _).trans (Finset.le_sup' (fun t => |X t ω - X t₀ ω|) ha)
  by_cases hK0 : K = 0
  · -- K = 0: all increments vanish a.e., so the sup is a.e. 0.
    subst hK0
    have hz : ∀ᵐ ω ∂μ, ∀ t ∈ (↑F : Set E), X t ω - X t₀ ω = 0 := by
      rw [ae_ball_iff F.countable_toSet]
      intro t ht
      have htT := hmemT t ht
      have hnorm : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ = 0 := by
        have h := hinc t₀ ht₀ t htT
        simp only [ENNReal.coe_zero, zero_mul, nonpos_iff_eq_zero] at h
        exact h
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t htT).sub (hmeas t₀ ht₀)) hnorm
    have hZae : (fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|)) =ᵐ[μ] 0 := by
      filter_upwards [hz] with ω hω
      simp only [Pi.zero_apply]
      refine le_antisymm (Finset.sup'_le hFne _ (fun s hs => ?_))
        ((abs_nonneg _).trans
          (Finset.le_sup' (fun t => |X t ω - X t₀ ω|) hFne.choose_spec))
      rw [hω s (Finset.mem_coe.mpr hs), abs_zero]
    rw [integral_congr_ae hZae]
    simp
  · by_cases hγ : gammaFunctional A = ⊤
    · rw [hγ, ENNReal.mul_top (mul_ne_zero (by norm_num) (ENNReal.coe_ne_zero.mpr hK0))]
      exact le_top
    · -- Main case: integrate the tail bound via `TailToExpectation`.
      have ha0 : (0 : ℝ) ≤ 12 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have hb0 : (0 : ℝ) ≤ 4 * (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg (mul_nonneg (by norm_num) K.coe_nonneg) ENNReal.toReal_nonneg
      have htail : ∀ u : ℝ, 0 ≤ u →
          μ {ω | 12 * (K : ℝ) * (gammaFunctional A).toReal
                + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
              < F.sup' hFne (fun t => |X t ω - X t₀ ω|)}
            ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2)) := by
        intro u hu
        have hval := generic_chaining_tail hne hmeas hinc ht₀ A hγ hu hF hFne
        have hthr : 12 * (K : ℝ) * (gammaFunctional A).toReal
              + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
            = (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal := by ring
        have hset : {ω | 12 * (K : ℝ) * (gammaFunctional A).toReal
                + 4 * (K : ℝ) * (gammaFunctional A).toReal * u
              < F.sup' hFne (fun t => |X t ω - X t₀ ω|)}
            = {ω | (12 + 4 * u) * (K : ℝ) * (gammaFunctional A).toReal
              < F.sup' hFne (fun t => |X t ω - X t₀ ω|)} := by
          ext ω; simp only [Set.mem_setOf_eq, hthr]
        rw [hset]; exact hval
      have hInt : ∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ
          ≤ 12 * (K : ℝ) * (gammaFunctional A).toReal
            + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal) :=
        integral_le_of_tail_le hZm hZ0 ha0 hb0 htail
      have hc : (0 : ℝ) ≤ (K : ℝ) * (gammaFunctional A).toReal :=
        mul_nonneg K.coe_nonneg ENNReal.toReal_nonneg
      have hsqrt : Real.sqrt Real.pi ≤ 2 := by
        nlinarith [Real.sq_sqrt Real.pi_pos.le, Real.sqrt_nonneg Real.pi, Real.pi_lt_d2]
      have hmid : 12 * (K : ℝ) * (gammaFunctional A).toReal
          + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal)
          ≤ 20 * (K : ℝ) * (gammaFunctional A).toReal := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt) hc, hc, hsqrt]
      have hfinal : ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal)
          = 20 * ↑K * gammaFunctional A := by
        rw [show (20 : ℝ) * (K : ℝ) * (gammaFunctional A).toReal
              = 20 * ((K : ℝ) * (gammaFunctional A).toReal) from by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20),
            ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal,
            ENNReal.ofReal_toReal hγ, ENNReal.ofReal_ofNat]
        ring
      calc ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
          ≤ ENNReal.ofReal (12 * (K : ℝ) * (gammaFunctional A).toReal
              + Real.sqrt Real.pi * (4 * (K : ℝ) * (gammaFunctional A).toReal)) :=
            ENNReal.ofReal_le_ofReal hInt
        _ ≤ ENNReal.ofReal (20 * (K : ℝ) * (gammaFunctional A).toReal) :=
            ENNReal.ofReal_le_ofReal hmid
        _ = 20 * ↑K * gammaFunctional A := hfinal

/-- **Theorem 8.5.2 (generic chaining bound)** (HDP §8.5.2; faithful
general-`T` form, book's absolute constant frozen `C = 20`): mean-zero
process with sub-Gaussian increments on an arbitrary metric space satisfies,
for every finite subset `F ⊆ T` (the Remark 7.2.1 reading of E sup),
`E max_{t∈F} X_t ≤ 20·K·γ₂(T,d)` in `ℝ≥0∞`. -/
theorem generic_chaining {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability of the process, ruling out Bochner-junk
    -- means (reconciliation R4; the book's E X_t = 0 presupposes it)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ) ≤
      20 * K * gammaTwo T := by
  have hmemT : ∀ t ∈ F, t ∈ T := fun t ht => hF (Finset.mem_coe.mpr ht)
  -- Anchor at a point of `T` (Remark 8.5.3 device).
  set t₀ := hne.some with ht₀def
  have ht₀ : t₀ ∈ T := hne.some_mem
  -- Integrability of the two finite maxima.
  have hSXint : Integrable (fun ω => F.sup' hFne (fun t => X t ω)) μ :=
    integrable_sup'_finset hFne (fun t ht => hint t (hmemT t ht))
  have hWint : Integrable (fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|)) μ :=
    integrable_sup'_finset hFne
      (fun t ht => ((hint t (hmemT t ht)).sub (hint t₀ ht₀)).abs)
  -- E max X ≤ E sup |X − X t₀| (mean-zero anchor cancels).
  have hred : ∫ ω, F.sup' hFne (fun t => X t ω) ∂μ
      ≤ ∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ := by
    have hbound : ∫ ω, F.sup' hFne (fun t => X t ω) ∂μ
        ≤ ∫ ω, (X t₀ ω + F.sup' hFne (fun t => |X t ω - X t₀ ω|)) ∂μ := by
      refine integral_mono hSXint ((hint t₀ ht₀).add hWint) (fun ω => ?_)
      refine Finset.sup'_le hFne _ (fun s hs => ?_)
      have h1 : |X s ω - X t₀ ω| ≤ F.sup' hFne (fun t => |X t ω - X t₀ ω|) :=
        Finset.le_sup' (fun t => |X t ω - X t₀ ω|) hs
      have h2 := le_abs_self (X s ω - X t₀ ω)
      linarith
    rwa [integral_add (hint t₀ ht₀) hWint, hmean t₀ ht₀, zero_add] at hbound
  refine le_trans (ENNReal.ofReal_le_ofReal hred) ?_
  haveI : Nonempty (AdmissibleSequence T) := nonempty_admissibleSequence hne
  have ha_top : (20 : ℝ≥0∞) * ↑K ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  have hpush : (20 : ℝ≥0∞) * ↑K * gammaTwo T
      = ⨅ A : AdmissibleSequence T, 20 * ↑K * gammaFunctional A := by
    rw [show gammaTwo T = ⨅ A : AdmissibleSequence T, gammaFunctional A from rfl]
    exact ENNReal.mul_iInf (fun h => absurd h ha_top)
  rw [hpush]
  exact le_iInf (fun A => generic_chaining_of_admissible hne hmeas hinc ht₀ A hF hFne)

/-- Theorem 8.5.2, real display (faithful general-`T` form): under a finite
γ₂ (LEAN-ONLY junk-guard replacing the former finiteness of `T`),
`E max_{t∈F} X_t ≤ 20·K·γ₂(T,d)` as real numbers. -/
theorem generic_chaining_real {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: probability measure
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: nonempty index
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: integrability (R4, as above)
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero process; HDP Thm 8.5.2
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-Gaussian increments Eq (8.1); HDP Thm 8.5.2
    (hinc : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: finite γ₂ so the real RHS is honest (junk-guard)
    (hγ : gammaTwo T ≠ ⊤)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ∫ ω, F.sup' hFne (fun t => X t ω) ∂μ ≤ 20 * K * (gammaTwo T).toReal := by
  have h3 := generic_chaining hne hmeas hint hmean hinc hF hFne
  have htop : (20 : ℝ≥0∞) * ↑K * gammaTwo T ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) hγ
  rw [ENNReal.ofReal_le_iff_le_toReal htop, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.coe_toReal] at h3
  exact h3

end StatLean.ConcentrationInequalities
