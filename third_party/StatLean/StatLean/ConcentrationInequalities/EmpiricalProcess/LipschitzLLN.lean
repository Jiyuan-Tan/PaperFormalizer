module
public import StatLean.ConcentrationInequalities.EmpiricalProcess.Defs
public import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzCovering
public import StatLean.ConcentrationInequalities.EmpiricalProcess.SubGaussianIncrements
public import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzDense
public import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
public import StatLean.ConcentrationInequalities.Chaining.DudleyConsumers
public import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal

@[expose] public section

/-!
# The Lipschitz law of large numbers — Theorem 8.2.3, assembly

For i.i.d. $X_1, \dots, X_n$ with values in $[0,1]$ and common law $P$, the
empirical process is uniformly small over the **genuine full** $L$-Lipschitz
class:
$$ \mathbb{E} \sup_{\|f\|_{\mathrm{Lip}} \le L}
   \Bigl| \frac{1}{n} \sum_{i=1}^{n} f(X_i) - \mathbb{E}_P f \Bigr|
   \;\le\; \frac{C L}{\sqrt{n}}, \qquad C = 960. $$
No countability hypothesis appears: the supremum inside the expectation is
over the uncountable subtype $\{f : [0,1] \to \mathbb{R} \,\|\,
\|f\|_{\mathrm{Lip}} \le L\}$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, Theorem 8.2.3 (book constant $C$ unnamed)
and Eq. (8.25).

**Proof formalization notes.** **Frozen constant `lipschitzLLNConst = 960`**,
coherent along both derivations: (i) the design formula
$\bigl(\int_0^1 \sqrt{24/\varepsilon}\, d\varepsilon\bigr) \cdot
C_{\mathrm{Dudley}} \cdot C_{\mathrm{B3}} = 4\sqrt{6} \cdot 40 \cdot \sqrt{6}
= 960$ (entropy integral $2\sqrt{24} = 4\sqrt 6$; `dudley_inequality_abs`
constant $40$; Orlicz-B3 carrier $\sqrt 6$), and (ii) the committed proof
route, the chaining cluster's packaged plug `dudley_abs_of_cov_le_exp_div`
at $80\,K\sqrt{C D}$ with increment constant $K = \sqrt{6}/\sqrt{n}$
(× $L$ after R1), entropy exponent $C = 24$, diameter cap $D = 1$:
$80 \cdot \sqrt 6 \cdot \sqrt{24} = 80 \cdot 12 = 960$. Assembly: per-`m`
finite Dudley bound on `T = lipschitzNetUnion m` with base point
`0 ∈ T` (`zero_mem_lipschitzNet`) and the `24/ε` majorant
(`log_toNat_coveringNumber_subset_le`); monotone-convergence E-sup lift
(`integral_tendsto_of_tendsto_of_monotone` + `tendsto_atTop_ciSup` +
`aestronglyMeasurable_of_tendsto_ae`, uniform-in-`m` bound `2` for the
integrand); then the pointwise R3/R2/R1 rewrites of `LipschitzDense.lean`
under the integral. The chaining theorems' integrability hypothesis
(`hint`, LEAN-ONLY Bochner-junk guard) and the increment mean-zero
hypotheses are **derived in the proof** (bounded process + probability
measures + `integral_empiricalProcess`), never exported — no hypothesis
laundering; the headline hypotheses are exactly the book's: independence,
common law on `[0,1]` (codomain type), `n ≥ 1` (`[NeZero n]`), plus
LEAN-ONLY per-index measurability. Edge behavior: `L = 0` holds via the
degenerate lemma `iSup_abs_empiricalProcess_lipZero_eq` (both sides `0` and
`0 ≤ 0`). Named-sorry fallback of the work item `hdp-emp-lln`:
`expectation_sup'_netUnion_le` (the single point of contact with the
chaining Dudley interface).

**Bibliographic comments.** Theorem 8.2.3 is a quantitative mean
Glivenko–Cantelli / Wasserstein-1 law of large numbers; the $n^{-1/2}$ rate
for the Lipschitz class on $[0,1]$ traces to R. M. Dudley, "The speed of
mean Glivenko–Cantelli convergence," *Ann. Math. Statist.* 40 (1969), 40–50;
the uniform-LLN framework is Vapnik–Chervonenkis (1971) and the chaining
route is Dudley (1967).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {P : Measure unitInterval} {n : ℕ} {X : Fin n → Ω → unitInterval}

/-- The zero function belongs to every exhaustion stage (base point `0 ∈ T`
of the Dudley plug; HDP §8.2, Eq. (8.25)). -/
private theorem zero_mem_lipschitzNetUnion (m : ℕ) :
    (0 : C(unitInterval, ℝ)) ∈ lipschitzNetUnion m := by
  classical
  rw [lipschitzNetUnion, Finset.mem_biUnion]
  exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos m), zero_mem_lipschitzNet (0 + 1)⟩

/-- Conversion between the set-bounded supremum over a Finset's coercion and
`Finset.sup'` (both equal the honest finite maximum when the family is
nonnegative — the junk-value guard `h0` is required, see
`biSup_finset_eq_sup'`; every use here is `|·|`-valued). -/
private lemma biSup_coe_finset_eq_sup' {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (g : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ g i) :
    (⨆ t ∈ (↑s : Set ι), g t) = s.sup' hs g := by
  rw [← biSup_finset_eq_sup' hs g h0]
  simp only [Finset.mem_coe]

/-- Pointwise bound `|X_g| ≤ 2` for class members (values in `[0,1]`). -/
private theorem abs_ep_le_two_of_mem [IsProbabilityMeasure P]
    {g : C(unitInterval, ℝ)} (hg : g ∈ lipschitzUnitClass) (ω : Ω) :
    |empiricalProcess P n X ⇑g ω| ≤ 2 := by
  have hbound : ∀ x, |(⇑g : unitInterval → ℝ) x| ≤ 1 := by
    intro x
    have hx := hg.2 x
    rw [abs_le]; exact ⟨by linarith [hx.1], hx.2⟩
  simpa using abs_empiricalProcess_le (f := ⇑g) hbound ω

/-- `ω ↦ |X_g(ω)|` is integrable for class members (bounded by `2`). -/
private theorem integrable_abs_ep_of_mem [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] {g : C(unitInterval, ℝ)}
    (hg : g ∈ lipschitzUnitClass) (hX : ∀ i, Measurable (X i)) :
    Integrable (fun ω => |empiricalProcess P n X ⇑g ω|) μ := by
  refine Integrable.mono' (integrable_const (2 : ℝ))
    (measurable_empiricalProcess g.continuous.measurable hX).abs.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_abs]
  exact abs_ep_le_two_of_mem hg ω

open Classical in
/-- The finite maximum of `|X_g|` over the exhaustion stage `N_m`. -/
private noncomputable def netMaxAbs (P : Measure unitInterval) (n : ℕ)
    (X : Fin n → Ω → unitInterval) (m : ℕ) (ω : Ω) : ℝ :=
  (lipschitzNetUnion m).sup' (lipschitzNetUnion_nonempty m)
    (fun g => |empiricalProcess P n X ⇑g ω|)

/-- **The Theorem 8.2.3 constant** (HDP §8.2; the book's `C` is unnamed).
Frozen numeral `960`; formula `4√6 · 40 · √6` (entropy integral
`∫₀¹ √(24/ε) dε = 4√6` × `dudley_inequality_abs` constant `40` × Orlicz-B3
carrier `√6`), equivalently `80 · √6 · √24` via the packaged plug
`dudley_abs_of_cov_le_exp_div` (`80·K·√(C·D)` at `K = √6/√n`, `C = 24`,
`D = 1`). -/
noncomputable def lipschitzLLNConst : ℝ := 960

/-- **Per-`m` finite Dudley bound** (HDP §8.2, Eq. (8.25)): the expected
maximum of `|X_g|` over the exhaustion stage `lipschitzNetUnion m` is at most
`960/√n`, uniformly in `m` — the chaining plug `dudley_abs_of_cov_le_exp_div`
at base point `0 ∈ T`, entropy majorant `24/ε`, diameter cap `1`, increment
constant `√6/√n`. Single point of contact with the chaining Dudley interface;
named-sorry fallback of `hdp-emp-lln`. -/
theorem expectation_sup'_netUnion_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n]
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) (m : ℕ) :
    ∫ ω, (lipschitzNetUnion m).sup' (lipschitzNetUnion_nonempty m)
        (fun g => |empiricalProcess P n X ⇑g ω|) ∂μ
      ≤ lipschitzLLNConst / Real.sqrt n := by
  -- The finite index set and its basic properties.
  have hsub : (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)) ⊆ lipschitzUnitClass :=
    lipschitzNetUnion_subset m
  have hne : (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)).Nonempty :=
    Finset.coe_nonempty.mpr (lipschitzNetUnion_nonempty m)
  have hfin : (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)).Finite :=
    (lipschitzNetUnion m).finite_toSet
  -- The empirical process is `0` at the base point `0 ∈ T`.
  have hzero_ep : ∀ ω, empiricalProcess P n X ⇑(0 : C(unitInterval, ℝ)) ω = 0 := by
    intro ω
    have hcz : (⇑(0 : C(unitInterval, ℝ)) : unitInterval → ℝ) = (fun _ => (0 : ℝ)) := by
      funext x; rfl
    rw [hcz, empiricalProcess_zero_fun]
  -- Sub-gaussian increments restricted to the net.
  have hinc : SubGaussianIncrements (fun (f : C(unitInterval, ℝ)) => empiricalProcess P n X ⇑f)
      (Real.toNNReal (Real.sqrt 6 / Real.sqrt n)) (↑(lipschitzNetUnion m)) μ :=
    (subGaussianIncrements_empiricalProcess hX hindep hlaw).mono_set (Set.subset_univ _)
  -- Measurability of the coordinates.
  have hmeas : ∀ t ∈ (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)),
      AEMeasurable (fun ω => empiricalProcess P n X ⇑t ω) μ :=
    fun t _ => (measurable_empiricalProcess t.continuous.measurable hX).aemeasurable
  -- Diameter cap `D = 1`.
  have hdiam : Metric.diam (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)) ≤ 1 :=
    Metric.diam_le_of_forall_dist_le (by norm_num)
      (fun x hx y hy => dist_le_one_of_mem_lipschitzUnitClass (hsub hx) (hsub hy))
  -- Entropy majorant `24/ε` on `(0, 1]`.
  have hcov : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      coveringNumber (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)) ε ≠ ⊤ ∧
      ((coveringNumber (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)) ε).toNat : ℝ)
        ≤ Real.exp (24 / ε) := by
    intro ε hε
    refine ⟨coveringNumber_subset_lipschitzUnitClass_ne_top hsub hε.1, ?_⟩
    rcases eq_or_lt_of_le hε.2 with h1 | h1
    · subst h1
      rw [coveringNumber_subset_eq_one_of_one_le hsub hne le_rfl]
      simp only [ENat.toNat_one, Nat.cast_one, div_one]
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)
    · exact coveringNumber_subset_toNat_le_exp hsub hε.1 h1
  -- The packaged Dudley plug.
  have hplug := dudley_abs_of_cov_le_exp_div (μ := μ)
    (X := fun (f : C(unitInterval, ℝ)) => empiricalProcess P n X ⇑f)
    hfin hne hmeas hinc (zero_mem_lipschitzNetUnion m) (by norm_num : (0 : ℝ) ≤ 24)
    (by norm_num : (0 : ℝ) < 1) hdiam hcov
  -- Rewrite the goal's integrand to the plug's anchored supremum.
  simp only [lipschitzLLNConst]
  have hrw : ∀ ω, (lipschitzNetUnion m).sup' (lipschitzNetUnion_nonempty m)
        (fun g => |empiricalProcess P n X ⇑g ω|)
      = ⨆ t ∈ (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)),
          |empiricalProcess P n X ⇑t ω - empiricalProcess P n X ⇑(0 : C(unitInterval, ℝ)) ω| := by
    intro ω
    rw [biSup_coe_finset_eq_sup' (lipschitzNetUnion_nonempty m) _
      (fun _ _ => abs_nonneg _)]
    refine Finset.sup'_congr (lipschitzNetUnion_nonempty m) rfl (fun g _ => ?_)
    rw [hzero_ep ω, sub_zero]
  simp_rw [hrw]
  have hn : (0 : ℝ) < Real.sqrt n :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n))
  calc ∫ ω, ⨆ t ∈ (↑(lipschitzNetUnion m) : Set C(unitInterval, ℝ)),
        |empiricalProcess P n X ⇑t ω - empiricalProcess P n X ⇑(0 : C(unitInterval, ℝ)) ω| ∂μ
      ≤ 80 * ((Real.toNNReal (Real.sqrt 6 / Real.sqrt n) : ℝ≥0) : ℝ)
          * Real.sqrt (24 * 1) := hplug
    _ = 960 / Real.sqrt n := by
        rw [Real.coe_toNNReal _ (by positivity), mul_one]
        have h6 : Real.sqrt 6 * Real.sqrt 24 = 12 := by
          rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6),
            show (6 : ℝ) * 24 = 12 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12)]
        field_simp
        linear_combination 80 * h6

/-- **E-sup over the class (8.24)** (HDP §8.2): monotone-convergence lift of
the per-`m` bound along the R3 identity — the genuine uncountable supremum
enters the Bochner integral (integrand measurable as a monotone limit,
bounded by `2`). -/
theorem expectation_sup_lipschitzUnitClass_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n]
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    ∫ ω, (⨆ f : lipschitzUnitClass,
        |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω|) ∂μ
      ≤ lipschitzLLNConst / Real.sqrt n := by
  -- Integrability of each finite maximum `netMaxAbs m`.
  have hS_int : ∀ m, Integrable (fun ω => netMaxAbs P n X m ω) μ := by
    intro m
    have hb : Integrable (fun ω => ⨆ g ∈ lipschitzNetUnion m,
        |empiricalProcess P n X ⇑g ω|) μ :=
      integrable_biSup_finset (lipschitzNetUnion_nonempty m)
      (X := fun (g : C(unitInterval, ℝ)) (ω : Ω) => |empiricalProcess P n X ⇑g ω|)
      (fun g hg => integrable_abs_ep_of_mem
        (lipschitzNetUnion_subset m (Finset.mem_coe.mpr hg)) hX)
    refine hb.congr ?_
    filter_upwards with ω
    simp only [netMaxAbs]
    exact biSup_finset_eq_sup' (lipschitzNetUnion_nonempty m) _
      (fun _ _ => abs_nonneg _)
  -- Uniform bounds `0 ≤ netMaxAbs P n X m ω ≤ 2`.
  have hSle2 : ∀ m ω, netMaxAbs P n X m ω ≤ 2 := by
    intro m ω
    simp only [netMaxAbs]
    exact Finset.sup'_le (lipschitzNetUnion_nonempty m) _
      (fun g hg => abs_ep_le_two_of_mem
        (lipschitzNetUnion_subset m (Finset.mem_coe.mpr hg)) ω)
  have hS0 : ∀ m ω, 0 ≤ netMaxAbs P n X m ω := by
    intro m ω
    simp only [netMaxAbs]
    exact le_trans (abs_nonneg _)
      (Finset.le_sup' (f := fun (g : C(unitInterval, ℝ)) => |empiricalProcess P n X ⇑g ω|)
        (zero_mem_lipschitzNetUnion m))
  have hbddF : ∀ ω, BddAbove (Set.range (fun m => netMaxAbs P n X m ω)) := by
    intro ω
    refine ⟨2, ?_⟩
    rintro y ⟨m, rfl⟩
    exact hSle2 m ω
  -- Monotonicity in `m` (growing exhaustion).
  have hS_mono : ∀ ω, Monotone (fun m => netMaxAbs P n X m ω) := by
    intro ω m m' hmm
    simp only [netMaxAbs]
    exact Finset.sup'_mono _ (lipschitzNetUnion_mono hmm) (lipschitzNetUnion_nonempty m)
  -- The class supremum `F ω = ⨆ m, netMaxAbs P n X m ω` is measurable and integrable.
  have hF_aem : AEMeasurable (fun ω => ⨆ m, netMaxAbs P n X m ω) μ :=
    AEMeasurable.iSup (fun m => (hS_int m).aestronglyMeasurable.aemeasurable)
  have hF_int : Integrable (fun ω => ⨆ m, netMaxAbs P n X m ω) μ := by
    refine Integrable.mono' (integrable_const (2 : ℝ)) hF_aem.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (le_ciSup_of_le (hbddF ω) 0 (hS0 0 ω))]
    exact ciSup_le (fun m => hSle2 m ω)
  -- Pointwise convergence `netMaxAbs P n X m ω → F ω`.
  have hS_tendsto : ∀ ω, Tendsto (fun m => netMaxAbs P n X m ω) atTop
      (𝓝 (⨆ m, netMaxAbs P n X m ω)) :=
    fun ω => tendsto_atTop_ciSup (hS_mono ω) (hbddF ω)
  -- Monotone convergence of the Bochner integrals.
  have hint_tendsto : Tendsto (fun m => ∫ ω, netMaxAbs P n X m ω ∂μ) atTop
      (𝓝 (∫ ω, (⨆ m, netMaxAbs P n X m ω) ∂μ)) :=
    integral_tendsto_of_tendsto_of_monotone hS_int hF_int
      (Filter.Eventually.of_forall hS_mono) (Filter.Eventually.of_forall hS_tendsto)
  -- The limit inherits the per-`m` bound.
  have hle : ∫ ω, (⨆ m, netMaxAbs P n X m ω) ∂μ ≤ lipschitzLLNConst / Real.sqrt n :=
    le_of_tendsto hint_tendsto
      (Filter.Eventually.of_forall (fun m => expectation_sup'_netUnion_le hX hindep hlaw m))
  -- Rewrite the class supremum via the R3 dense-net identity.
  simp_rw [iSup_abs_empiricalProcess_eq_iSup_netUnion]
  exact hle

/-- **Theorem 8.2.3 (Lipschitz law of large numbers), HEADLINE** (HDP §8.2):
for i.i.d. `X₁, …, Xₙ` with values in `[0,1]` and common law `P`,
`E sup_{‖f‖_Lip ≤ L} |n⁻¹ ∑ f(Xᵢ) − E_P f| ≤ 960·L/√n` — over the genuine
full `L`-Lipschitz class, no countability hypothesis. Book constant unnamed;
ours frozen at `lipschitzLLNConst = 960`. `L = 0` is included (degenerate
case). -/
theorem lipschitz_lln {L : ℝ≥0} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n]
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1] (codomain type); HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    ∫ ω, (⨆ f : {f : unitInterval → ℝ // LipschitzWith L f},
        |empiricalProcess P n X (↑f) ω|) ∂μ
      ≤ lipschitzLLNConst * (L : ℝ) / Real.sqrt n := by
  rcases eq_or_ne L 0 with hL | hL
  · -- Degenerate case `L = 0`: the empirical process vanishes on constants.
    subst hL
    simp_rw [iSup_abs_empiricalProcess_lipZero_eq]
    simp
  · -- `L ≠ 0`: reduce to the unit class via the R1 scaling and R2 shift.
    simp_rw [iSup_abs_empiricalProcess_lip_smul hL, iSup_abs_empiricalProcess_lipOne_eq]
    rw [integral_const_mul]
    calc (L : ℝ) * ∫ ω, (⨆ f : lipschitzUnitClass,
            |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω|) ∂μ
        ≤ (L : ℝ) * (lipschitzLLNConst / Real.sqrt n) :=
          mul_le_mul_of_nonneg_left
            (expectation_sup_lipschitzUnitClass_le hX hindep hlaw) (by positivity)
      _ = lipschitzLLNConst * (L : ℝ) / Real.sqrt n := by ring

end StatLean.ConcentrationInequalities
