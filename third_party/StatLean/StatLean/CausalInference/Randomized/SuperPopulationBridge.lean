module
public import StatLean.CausalInference.Core.PopulationDefs
public import Mathlib.Probability.StrongLaw

@[expose] public section

/-!
# From the finite population to the superpopulation

The two frameworks are reconciled by treating the `n` units as an i.i.d. sample from a
superpopulation: the finite-population average causal effect of the sampled units is then
itself a random variable, unbiased for the superpopulation effect and converging to it,

$$\mathbb E\Bigl[\frac1n\sum_{i<n}\{Y_i(1)-Y_i(0)\}\Bigr]=\tau,
\qquad
\frac1n\sum_{i<n}\{Y_i(1)-Y_i(0)\}\ \xrightarrow{\ \text{a.s.}\ }\ \tau .$$

So a design-based analysis of a sampled finite population is automatically an analysis of
the superpopulation estimand.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). ch. 9, Definition 9.3 (§9.1, p. 130: the CRE under
the superpopulation framework, with `{Zᵢ, Yᵢ(1), Yᵢ(0), Xᵢ}` i.i.d. and
`Z ⫫ {Y(1),Y(0),X}`) and eq. (9.1) (`τ = E(Y|Z=1) - E(Y|Z=0)`); §9.1–9.2 (p. 131:
the conditional moments given the assignment vector, stated as unnumbered displays).
(`Ding ch. 9; Definition 9.3; eq. (9.1)`.) The corresponding discussion is in
G. W. Imbens and D. B. Rubin, *Causal Inference for Statistics, Social, and Biomedical
Sciences*, Cambridge University Press, 2015, ch. 6. (`IR ch. 6`.)

**Scope.** The two-level (sampling × assignment) variance decomposition is **not**
formalized: it is not a numbered result in Ding's ch. 9 (he works directly in the i.i.d.
superpopulation), and stating it faithfully would require a joint model of the sampling
mechanism and the design that neither reference text sets up. What is formalized is the
part Ding does state: unbiasedness and convergence of the sampled finite-population
effect, plus the identification identity eq. (9.1) — the latter is
`SelectionBias.primaFacie_eq_ate_of_indep`, proved there in exactly Definition 9.3's
independence form.

**Proof formalization notes.** Unbiasedness is linearity of the integral plus
`IdentDistrib.integral_eq`; convergence is Mathlib's `ProbabilityTheory.strong_law_ae_real`
applied to the individual-effect sequence `Wᵢ = Yᵢ(1) - Yᵢ(0)`, whose pairwise
independence and identical distribution are inherited from the sampled units. The
hypotheses are stated on `W` directly rather than on the pair `(Y(1), Y(0))` so that the
Mathlib lemma applies verbatim; deriving them from independence of the *pairs* is a
routine `IndepFun.comp` step recorded as `indepFun_unitEffect`.

**Bibliographic comments.** The finite-population/superpopulation bridge for causal
inference is developed in P. Ding, X. Li and L. W. Miratrix, "Bridging finite and super
population causal inference," *J. Causal Inference* **5** (2017), 20160027.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **individual causal effects of the sampled units**: `Wᵢ = Yᵢ(1) - Yᵢ(0)`. -/
def sampledEffect (Y1 Y0 : ℕ → Ω → ℝ) (i : ℕ) : Ω → ℝ := fun ω => Y1 i ω - Y0 i ω

/-- The **finite-population average causal effect of the first `n` sampled units**, as a
random variable on the sampling space. -/
noncomputable def sampledFiniteATE (Y1 Y0 : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, sampledEffect Y1 Y0 i ω

/-- Pairwise independence of the individual effects, inherited from independence of the
sampled potential-outcome pairs. -/
theorem indepFun_sampledEffect {Y1 Y0 : ℕ → Ω → ℝ}
    -- USER-INPUT: the sampled units are independent; Ding Definition 9.3
    (hindep : Pairwise fun i j =>
      IndepFun (fun ω => (Y1 i ω, Y0 i ω)) (fun ω => (Y1 j ω, Y0 j ω)) μ) :
    Pairwise fun i j => IndepFun (sampledEffect Y1 Y0 i) (sampledEffect Y1 Y0 j) μ := by
  intro i j hij
  exact (hindep hij).comp (φ := fun p : ℝ × ℝ => p.1 - p.2) (ψ := fun p : ℝ × ℝ => p.1 - p.2)
    (measurable_fst.sub measurable_snd) (measurable_fst.sub measurable_snd)

/-- **Unbiasedness of the sampled finite-population effect** (Ding ch. 9): its expectation
over the sampling of units is the superpopulation average causal effect. -/
theorem integral_sampledFiniteATE [IsProbabilityMeasure μ] {Y1 Y0 : ℕ → Ω → ℝ} {n : ℕ}
    -- USER-INPUT: the sampled units are identically distributed; Ding Definition 9.3
    (hident : ∀ i, IdentDistrib (sampledEffect Y1 Y0 i) (sampledEffect Y1 Y0 0) μ μ)
    -- USER-INPUT: integrable individual effect; Ding assumes finite means
    (hint : Integrable (sampledEffect Y1 Y0 0) μ)
    -- LEAN-ONLY: a nonempty sample, else `n⁻¹` is a junk value
    (hn : 0 < n) :
    ∫ ω, sampledFiniteATE Y1 Y0 n ω ∂μ = ate μ (Y1 0) (Y0 0) := by
  have hintI : ∀ i, Integrable (sampledEffect Y1 Y0 i) μ :=
    fun i => (hident i).integrable_iff.mpr hint
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hstep : ∫ ω, sampledFiniteATE Y1 Y0 n ω ∂μ
      = (n : ℝ)⁻¹ * ∫ ω, (∑ i ∈ Finset.range n, sampledEffect Y1 Y0 i ω) ∂μ := by
    simp only [sampledFiniteATE]
    exact integral_const_mul _ _
  rw [hstep, integral_finset_sum _ fun i _ => hintI i]
  have hterm : ∀ i ∈ Finset.range n,
      ∫ ω, sampledEffect Y1 Y0 i ω ∂μ = ∫ ω, sampledEffect Y1 Y0 0 ω ∂μ :=
    fun i _ => (hident i).integral_eq
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hn0, one_mul]
  rfl

/-- **Convergence of the sampled finite-population effect** (Ding ch. 9): as the sample
grows, the finite-population effect of the sampled units converges almost surely to the
superpopulation effect. -/
theorem tendsto_sampledFiniteATE [IsProbabilityMeasure μ] {Y1 Y0 : ℕ → Ω → ℝ}
    -- USER-INPUT: the sampled units are independent; Ding Definition 9.3
    (hindep : Pairwise fun i j =>
      IndepFun (fun ω => (Y1 i ω, Y0 i ω)) (fun ω => (Y1 j ω, Y0 j ω)) μ)
    -- USER-INPUT: identically distributed sampled units; Ding Definition 9.3
    (hident : ∀ i, IdentDistrib (sampledEffect Y1 Y0 i) (sampledEffect Y1 Y0 0) μ μ)
    -- USER-INPUT: integrable individual effect; needed for the strong law
    (hint : Integrable (sampledEffect Y1 Y0 0) μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => sampledFiniteATE Y1 Y0 n ω) atTop
      (𝓝 (ate μ (Y1 0) (Y0 0))) := by
  have hlaw := strong_law_ae_real (μ := μ) (sampledEffect Y1 Y0) hint
    (indepFun_sampledEffect hindep) hident
  have hate : ate μ (Y1 0) (Y0 0) = ∫ ω, sampledEffect Y1 Y0 0 ω ∂μ := rfl
  rw [hate]
  filter_upwards [hlaw] with ω hω
  refine hω.congr fun m => ?_
  simp only [sampledFiniteATE]
  rw [div_eq_inv_mul]

end StatLean.CausalInference
