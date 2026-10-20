module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib

@[expose] public section

/-!
# Glivenko–Cantelli classes via finite $L_1$-bracketing (Theorem 19.4)

A class $\mathcal F$ of measurable functions is **$P$-Glivenko–Cantelli** if, for
any i.i.d. sample $X_1, X_2, \dots$ drawn from $P$, the empirical-process
supremum deviation
$$\|\mathbb P_n - P\|_{\mathcal F} \;=\; \sup_{f \in \mathcal F}
  \Bigl| \tfrac1n \sum_{i=1}^n f(X_i) - \int f \, dP \Bigr|$$
converges to $0$ almost surely as $n \to \infty$.

The headline result is: *every class $\mathcal F$ of measurable functions whose
$L_1(P)$ bracketing numbers are finite — that is, $N_{[\,]}(\varepsilon,
\mathcal F, L_1(P)) < \infty$ for every $\varepsilon > 0$ — is
$P$-Glivenko–Cantelli.* Here a finite $\varepsilon$-bracketing cover means a
finite collection of brackets $[l_i, u_i]$ with $\int (u_i - l_i)\, dP <
\varepsilon$ that together contain every $f \in \mathcal F$ (each $f$ satisfies
$l_i \le f \le u_i$ pointwise for some $i$).

**Added/changed hypotheses (Lean vs. book).** The Lean statement carries the
integrability side-condition $f \in L_1(P)$ for every $f \in \mathcal F$
(`h_F_int`); this is the only $\mathcal F$-side requirement, since
measurability of each $f$ follows from integrability, and the only places
$\mathcal F$-side data enters the proof are the pointwise sandwich and the
comparison of integrals. The Glivenko–Cantelli predicate is stated
construction-agnostically: it is universally quantified over the sample
probability space and the i.i.d. sequence rather than committed to a single
canonical construction of the sample.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 19 (Empirical Processes), §19.2 (Glivenko–Cantelli Theorems),
Theorem 19.4.

**Proof formalization notes.** The proof generalises van der Vaart's §19.1
argument for the classical Theorem 19.1; van der Vaart omits the proof of
Theorem 19.4, calling it a "straightforward generalization" of Theorem 19.1.
A per-$\varepsilon$ step (`gc_eventual_bound_per_eps`) applies the strong law of
large numbers to each bracket endpoint $l_i, u_i$ and uses the bracket sandwich
$l_i \le f \le u_i$ to bound the supremum deviation by $2\varepsilon$ eventually,
almost surely. The full result then follows by a double-limit chase: take the
countable intersection of the full-measure sets obtained for
$\varepsilon = 1/(k+1)$, $k \in \mathbb N$, and let $k \to \infty$.

**Bibliographic comments.** The classical Glivenko–Cantelli theorem — uniform
a.s. convergence of the empirical distribution function to the true
distribution function — originates in two companion 1933 papers in the same
journal volume: V. Glivenko, "Sulla determinazione empirica delle leggi di
probabilità," *Giornale dell'Istituto Italiano degli Attuari* 4 (1933), 92–99
(the continuous case), and F. P. Cantelli, "Sulla determinazione empirica delle
leggi di probabilità," *Giornale dell'Istituto Italiano degli Attuari* 4 (1933),
421–424 (the general case). The abstract bracketing-entropy formulation
generalised here (van der Vaart's Theorem 19.4) is part of the modern theory of
empirical processes and is not attributable to a single seminal paper; it is
folklore in that literature, presented systematically in A. W. van der Vaart and
J. A. Wellner, *Weak Convergence and Empirical Processes*, Springer, 1996.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `F` is **P-Glivenko–Cantelli** iff, for every iid sample `X_i ~ P`
on any probability space `(Ξ, μ)`, the empirical-deviation supremum
`sup_{f ∈ F} |P_n f − P f|` converges to `0` almost surely.

This adopts vdV's intuitive statement (§19.2) without committing to a
specific construction of the iid sample: the statement is universally
quantified over the sample probability space and the iid sequence.

vdV §19.2: the abstract Glivenko–Cantelli predicate. -/
def IsPGlivenkoCantelli (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∀ {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω},
    (∀ i, Measurable (X i)) →
    Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) →
    (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
    μ.map (X 0) = P →
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      supNormOver F
        (fun f => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (X i ω) - ∫ x, f x ∂P))
      atTop (𝓝 (0 : ℝ≥0∞))

/-! ### Helper lemmas for Theorem 19.4. -/

/-- Strong law of large numbers for a single integrable, measurable function
applied along an iid sample sequence. Internal helper for the proof of
Theorem 19.4. -/
private lemma slln_ae_via_iid_real {P : Measure Ω}
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg_int : Integrable g P) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, g (X j ω))
      atTop (𝓝 (∫ x, g x ∂P)) := by
  set Y : ℕ → Ξ → ℝ := fun j ω => g (X j ω) with hY_def
  have hY_indep : Pairwise (fun i j => ProbabilityTheory.IndepFun (Y i) (Y j) μ) := by
    intro i j hij
    exact (hX_indep hij).comp hg_meas hg_meas
  have hY_idem : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ :=
    fun i => (hX_idem i).comp hg_meas
  have h_int_map : Integrable g (μ.map (X 0)) := by rw [hX_law]; exact hg_int
  have h_aestrong : AEStronglyMeasurable g (μ.map (X 0)) := h_int_map.aestronglyMeasurable
  have hY_int : Integrable (Y 0) μ :=
    (integrable_map_measure h_aestrong (hX_meas 0).aemeasurable).mp h_int_map
  have h_int_eq : ∫ x, g x ∂P = ∫ ω, Y 0 ω ∂μ := by
    have h1 : ∫ x, g x ∂(μ.map (X 0)) = ∫ ω, g (X 0 ω) ∂μ :=
      integral_map (hX_meas 0).aemeasurable h_aestrong
    rw [← hX_law]
    exact h1
  have h_law := ProbabilityTheory.strong_law_ae_real Y hY_int hY_indep hY_idem
  filter_upwards [h_law] with ω hω
  rw [h_int_eq]
  -- strong_law_ae_real returns `(∑ Y i ω) / n → μ[Y 0]`. Convert.
  have h_eq : ∀ n : ℕ,
      (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, g (X j ω)
        = (∑ i ∈ Finset.range n, Y i ω) / n := by
    intro n
    change (n : ℝ)⁻¹ * (∑ j ∈ Finset.range n, g (X j ω)) =
        (∑ i ∈ Finset.range n, g (X i ω)) / (n : ℝ)
    rw [div_eq_mul_inv, mul_comm]
  simp_rw [h_eq]
  exact hω

/-- The `L_1(P)`-size of a bracket, expressed as a real-valued integral.

If `(l, u)` is an ε-bracket in `L_1(P)`, then `∫ (u − l) dP < ε`. -/
private lemma bracket_size_integral_lt {ε : ℝ} (hε : 0 < ε)
    {l u : Ω → ℝ} {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsEpsBracket ε l u 1 P) :
    ∫ x, u x - l x ∂P < ε := by
  have h_nn : ∀ x, 0 ≤ u x - l x := fun x => sub_nonneg.mpr (h.isBracket x)
  have h_int : Integrable (fun x => u x - l x) P :=
    (h.memLp_upper.integrable le_rfl).sub (h.memLp_lower.integrable le_rfl)
  have h_eLpNorm_eq : eLpNorm (fun x => u x - l x) 1 P
      = ENNReal.ofReal (∫ x, u x - l x ∂P) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    have : (fun x => ‖u x - l x‖ₑ) = (fun x => ENNReal.ofReal (u x - l x)) :=
      funext fun x => Real.enorm_eq_ofReal (h_nn x)
    rw [this]
    exact (ofReal_integral_eq_lintegral_ofReal h_int (Filter.Eventually.of_forall h_nn)).symm
  have h_size : ENNReal.ofReal (∫ x, u x - l x ∂P) < ENNReal.ofReal ε := by
    rw [← h_eLpNorm_eq]; exact h.size_lt
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp h_size

/-- Per-`ε` Glivenko–Cantelli step.

For a fixed `ε > 0`, if `F` admits a finite ε-bracketing cover in `L_1(P)`
and the iid sample `X_i ~ P` is in place, then on a `μ`-a.s. set there is
some `N` such that for all `n ≥ N`, the supremum deviation
`supNormOver F (fun f => (1/n) Σ f(X_j ω) − ∫ f dP)` is at most
`ENNReal.ofReal (2 ε)`. -/
private lemma gc_eventual_bound_per_eps {P : Measure Ω} [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    {F : Set (Ω → ℝ)}
    (h_F_int : ∀ f ∈ F, Integrable f P)
    {ε : ℝ} (hε : 0 < ε)
    (h_bracket : HasFiniteBracketingCover F ε 1 P) :
    ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      supNormOver F (fun f => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω) - ∫ x, f x ∂P)
        ≤ ENNReal.ofReal (2 * ε) := by
  obtain ⟨m, l, u, hbr, hcov⟩ := h_bracket
  have hl_slln : ∀ i, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω))
        atTop (𝓝 (∫ x, l i x ∂P)) := fun i =>
    slln_ae_via_iid_real hX_meas hX_indep hX_idem hX_law
      (hbr i).measurable_lower ((hbr i).memLp_lower.integrable le_rfl)
  have hu_slln : ∀ i, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω))
        atTop (𝓝 (∫ x, u i x ∂P)) := fun i =>
    slln_ae_via_iid_real hX_meas hX_indep hX_idem hX_law
      (hbr i).measurable_upper ((hbr i).memLp_upper.integrable le_rfl)
  have h_combined : ∀ᵐ ω ∂μ, ∀ i,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω))
        atTop (𝓝 (∫ x, l i x ∂P)) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω))
        atTop (𝓝 (∫ x, u i x ∂P)) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [hl_slln i, hu_slln i] with ω hl hu
    exact ⟨hl, hu⟩
  filter_upwards [h_combined] with ω hcomb
  -- Per-i eventual bounds on |empirical-average − integral|.
  have h_eventual_l : ∀ i, ∀ᶠ n : ℕ in atTop,
      |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, l i x ∂P| < ε := by
    intro i
    have h := (hcomb i).1
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [Real.dist_eq] at this
  have h_eventual_u : ∀ i, ∀ᶠ n : ℕ in atTop,
      |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, u i x ∂P| < ε := by
    intro i
    have h := (hcomb i).2
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    have := hN n hn
    rwa [Real.dist_eq] at this
  -- Combine all 2m eventual conditions.
  have h_eventual : ∀ᶠ n : ℕ in atTop, ∀ i,
      |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, l i x ∂P| < ε ∧
      |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, u i x ∂P| < ε := by
    rw [eventually_all]
    intro i
    exact (h_eventual_l i).and (h_eventual_u i)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h_eventual
  refine ⟨N, fun n hn => ?_⟩
  -- Goal: supNormOver F (fun f => (n)⁻¹ Σ f(X j ω) − ∫ f) ≤ ENNReal.ofReal (2ε).
  refine iSup₂_le fun f hf => ?_
  obtain ⟨i, hf_i⟩ := hcov f hf
  have h_lf : ∀ x, l i x ≤ f x := fun x => (hf_i x).1
  have h_fu : ∀ x, f x ≤ u i x := fun x => (hf_i x).2
  -- Unpack the per-i bracketing data.
  have hl_int : Integrable (l i) P := (hbr i).memLp_lower.integrable le_rfl
  have hu_int : Integrable (u i) P := (hbr i).memLp_upper.integrable le_rfl
  have hf_int : Integrable f P := h_F_int f hf
  have h_size : ∫ x, u i x - l i x ∂P < ε := bracket_size_integral_lt hε (hbr i)
  have hN_i := hN n hn i
  have hl_err :
      |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, l i x ∂P| < ε := hN_i.1
  have hu_err :
      |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, u i x ∂P| < ε := hN_i.2
  -- Sums sandwich.
  have hsum_lf : ∑ j ∈ Finset.range n, l i (X j ω) ≤ ∑ j ∈ Finset.range n, f (X j ω) :=
    Finset.sum_le_sum fun j _ => h_lf (X j ω)
  have hsum_fu : ∑ j ∈ Finset.range n, f (X j ω) ≤ ∑ j ∈ Finset.range n, u i (X j ω) :=
    Finset.sum_le_sum fun j _ => h_fu (X j ω)
  -- Integrals sandwich.
  have h_int_lf : ∫ x, l i x ∂P ≤ ∫ x, f x ∂P :=
    integral_mono hl_int hf_int (fun x => h_lf x)
  have h_int_fu : ∫ x, f x ∂P ≤ ∫ x, u i x ∂P :=
    integral_mono hf_int hu_int (fun x => h_fu x)
  -- Now bound the per-f deviation.
  have h_bound : |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω) - ∫ x, f x ∂P| ≤ 2 * ε := by
    have hn_pos : 0 ≤ (n : ℝ)⁻¹ := by positivity
    have hsum_lower : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω)
                  ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω) :=
      mul_le_mul_of_nonneg_left hsum_lf hn_pos
    have hsum_upper : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω)
                  ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) :=
      mul_le_mul_of_nonneg_left hsum_fu hn_pos
    have h_diff_eq : ∫ x, u i x - l i x ∂P = ∫ x, u i x ∂P - ∫ x, l i x ∂P :=
      integral_sub hu_int hl_int
    have hsize' : ∫ x, u i x ∂P - ∫ x, l i x ∂P < ε := by rw [← h_diff_eq]; exact h_size
    have h_abs_l : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, l i x ∂P
                 ∈ Set.Ioo (-ε) ε := abs_lt.mp hl_err
    have h_abs_u : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, u i x ∂P
                 ∈ Set.Ioo (-ε) ε := abs_lt.mp hu_err
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- -(2ε) ≤ (1/n) Σ f - ∫ f
      have h_step :
          (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, u i x ∂P
            ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω) - ∫ x, f x ∂P := by linarith
      have h_lower_bound :
          -(2 * ε) ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, u i x ∂P := by
        have h1 : -ε ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, l i x ∂P :=
          h_abs_l.1.le
        have h2 : -ε ≤ -(∫ x, u i x ∂P - ∫ x, l i x ∂P) := by linarith
        have : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, u i x ∂P
             = ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, l i (X j ω) - ∫ x, l i x ∂P)
               + (- (∫ x, u i x ∂P - ∫ x, l i x ∂P)) := by ring
        linarith
      linarith
    · -- (1/n) Σ f - ∫ f ≤ 2ε
      have h_step :
          (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω) - ∫ x, f x ∂P
            ≤ (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, l i x ∂P := by linarith
      have h_upper_bound :
          (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, l i x ∂P ≤ 2 * ε := by
        have h1 : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, u i x ∂P ≤ ε :=
          h_abs_u.2.le
        have h2 : ∫ x, u i x ∂P - ∫ x, l i x ∂P ≤ ε := hsize'.le
        have : (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, l i x ∂P
             = ((n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, u i (X j ω) - ∫ x, u i x ∂P)
               + (∫ x, u i x ∂P - ∫ x, l i x ∂P) := by ring
        linarith
      linarith
  calc ENNReal.ofReal |(n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω) - ∫ x, f x ∂P|
      ≤ ENNReal.ofReal (2 * ε) := ENNReal.ofReal_le_ofReal h_bound

/-- **Theorem 19.4 (Glivenko–Cantelli via finite L¹-bracketing)**.

Every class `F` of measurable functions admitting a finite ε-bracketing
cover in `L_1(P)` for every `ε > 0` is `P`-Glivenko–Cantelli.

vdV §19.2 Theorem 19.4: "Every class `F` of measurable functions such
that `N_{[]}(ε, F, L_1(P)) < ∞` for every `ε > 0` is `P`-Glivenko–Cantelli."

vdV omits the proof, calling it a "straightforward generalization" of
the classical Theorem 19.1.

`h_F_int` (integrability of every `f ∈ F`) is the only F-side condition
needed: measurability of `f` is implied via
`Integrable.aestronglyMeasurable`, and pointwise sandwich + integral
comparison are the only places where F-side data enters the proof. -/
theorem isPGlivenkoCantelli_of_finite_bracketing_L1
    (F : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (h_F_int : ∀ f ∈ F, Integrable f P)
    (h_bracket : ∀ ε > 0, HasFiniteBracketingCover F ε 1 P) :
    IsPGlivenkoCantelli F P := by
  intro Ξ _ μ _ X hX_meas hX_indep hX_idem hX_law
  -- Per-`k` a.s. bound: eventually `supNormOver ≤ 2/(k+1)` on a full-measure set.
  have key : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∃ N : ℕ, ∀ n ≥ N,
      supNormOver F (fun f => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, f (X j ω) - ∫ x, f x ∂P)
        ≤ ENNReal.ofReal (2 * (1 / (k + 1 : ℝ))) := by
    intro k
    have hεk : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    exact gc_eventual_bound_per_eps hX_meas hX_indep hX_idem hX_law h_F_int hεk
      (h_bracket _ hεk)
  -- Countable intersection of full-measure sets is full-measure.
  rw [show (fun ω => Tendsto (fun n : ℕ =>
      supNormOver F (fun f => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (X i ω) - ∫ x, f x ∂P))
      atTop (𝓝 (0 : ℝ≥0∞))) = _ from rfl]
  rw [← ae_all_iff] at key
  filter_upwards [key] with ω hω
  rw [ENNReal.tendsto_atTop_zero]
  intro b hb
  -- Find k such that ENNReal.ofReal (2 / (k + 1 : ℝ)) ≤ b.
  by_cases hb_top : b = ⊤
  · refine ⟨0, fun n _ => ?_⟩
    rw [hb_top]; exact le_top
  have hb_pos : (0 : ℝ) < b.toReal := ENNReal.toReal_pos hb.ne' hb_top
  -- Choose k large enough so that 2/(k+1) ≤ b.toReal.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, 2 / (k + 1 : ℝ) ≤ b.toReal := by
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / b.toReal)
    refine ⟨k, ?_⟩
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h_bound : 2 / b.toReal < (k : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hb_pos] at h_bound
    -- h_bound : 2 < ((k : ℝ) + 1) * b.toReal
    rw [div_le_iff₀ hk1_pos]
    -- goal: 2 ≤ b.toReal * ((k : ℝ) + 1)
    nlinarith
  obtain ⟨N, hN⟩ := hω k
  refine ⟨N, fun n hn => ?_⟩
  calc supNormOver F _
      ≤ ENNReal.ofReal (2 * (1 / (k + 1 : ℝ))) := hN n hn
    _ = ENNReal.ofReal (2 / (k + 1 : ℝ)) := by rw [mul_one_div]
    _ ≤ ENNReal.ofReal b.toReal := ENNReal.ofReal_le_ofReal hk
    _ = b := ENNReal.ofReal_toReal hb_top

end AsymptoticStatistics.EmpiricalProcess
