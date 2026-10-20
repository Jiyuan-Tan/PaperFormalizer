module
public import StatLean.Bayesian.BernsteinVonMises.ScoreTest
public import StatLean.Bayesian.BernsteinVonMises.TestBoost

@[expose] public section

/-!
# Exponentially powerful tests

Assembly of the exponential-tests lemma: under the conditions of the Bernstein–von Mises theorem
(DQM at `θ₀`, nonsingular
Fisher information, the uniform-tests condition), for every `Mₙ → ∞` there are tests `φₙ` and a
constant `c > 0` with
`P^n_{θ₀} φₙ → 0` and `P^n_θ(1 − φₙ) ≤ exp(−c n (‖θ−θ₀‖² ∧ 1))` for every
`‖θ − θ₀‖ ≥ Mₙ/√n` and every sufficiently large `n`.

The test is the pointwise maximum of the moderate-range truncated-score test
(`ScoreTest.exists_moderate_tests`, covering `Mₙ/√n ≤ ‖θ−θ₀‖ ≤ ε`) and the boosted
far-range test (`TestBoost.exists_boosted_tests`, covering `‖θ−θ₀‖ ≥ ε`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2,
Lemma 10.3, p. 143 (statement) and pp. 143–144 (proof).

**Proof formalization notes.** The two ranges are glued with a single rate constant
`c := min(c_moderate, c_far)`; on the far range `‖θ−θ₀‖ ≥ ε` one has
`min(‖θ−θ₀‖², 1) ≤ 1`, so `exp(−c_far n)` dominates `exp(−c n (‖θ−θ₀‖² ∧ 1))` after
shrinking `c` by the factor `min(ε², 1)`. The size at `θ₀` of the maximum test is bounded by
the sum of the two sizes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure
  productMeasure_isProbabilityMeasure)

namespace StatLean.Bayesian

/-- A measurable `[0,1]`-valued statistic is integrable with respect to the (probability)
product experiment `P^n_θ`. -/
private lemma integrable_of_test {k : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧}
    {θ : EuclideanSpace ℝ (Fin k)} {n : ℕ}
    [IsProbabilityMeasure (productMeasure M μ θ n)]
    {f : (Fin n → 𝓧) → ℝ} (hf : Measurable f)
    (hf01 : ∀ ω, f ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable f (productMeasure M μ θ n) := by
  refine (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf01 ω).1]
  exact (hf01 ω).2

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}

/-- **Exponentially powerful tests**. Under the conditions of the Bernstein–von Mises theorem,
for every `Mₙ → ∞` there exist tests `φₙ` and `c > 0` with vanishing size at `θ₀` and
type-II error `≤ exp(−c n (‖θ−θ₀‖² ∧ 1))` uniformly over `‖θ − θ₀‖ ≥ Mₙ/√n`, for `n`
large. -/
theorem exponential_tests
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV §10.2
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV §10.2
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.2 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop) :
    ∃ (φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ) (c : ℝ), 0 < c ∧
      IsExpConsistentTestSeq M μ θ₀ Mseq c φ := by
  haveI hProb : ∀ (θ : EuclideanSpace ℝ (Fin k)) (n : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ n) :=
    fun θ n => productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- The moderate-range tests, valid on `Mₙ/√n ≤ ‖θ−θ₀‖ ≤ ε`.
  obtain ⟨φmod, ε, cmod, hε, hcmod, hmodM, hmod01, hmodI, N₁, hmodII⟩ :=
    exists_moderate_tests hPDF hsc hDQM hJ_pd hJ hM
  -- Shrink the separation radius below `1`, so that `min (‖θ−θ₀‖², 1) = ‖θ−θ₀‖²` below it.
  obtain ⟨ε₁, hε₁pos, hε₁le1, hε₁leε⟩ : ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ ε :=
    ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, min_le_left _ _⟩
  -- The boosted far-range tests, valid on `‖θ−θ₀‖ ≥ ε₁`.
  obtain ⟨φfar, cfar, hcfar, hfarM, hfar01, hfarI, N₂, hfarII⟩ :=
    exists_boosted_tests hPDF hTests hε₁pos
  obtain ⟨c, hcpos, hcmod', hcfar'⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ cmod ∧ c ≤ cfar :=
    ⟨min cmod cfar, lt_min hcmod hcfar, min_le_left _ _, min_le_right _ _⟩
  -- Basic facts about the glued test `φ n ω = max (φmod n ω) (φfar n ω)`.
  have hφM : ∀ n : ℕ, Measurable fun ω : Fin n → 𝓧 => max (φmod n ω) (φfar n ω) :=
    fun n => (hmodM n).max (hfarM n)
  have hφ01 : ∀ (n : ℕ) (ω : Fin n → 𝓧),
      max (φmod n ω) (φfar n ω) ∈ Set.Icc (0 : ℝ) 1 := fun n ω =>
    ⟨le_trans (hmod01 n ω).1 (le_max_left _ _), max_le (hmod01 n ω).2 (hfar01 n ω).2⟩
  -- `1 − ·` of a test is again a test.
  have hsubM : ∀ {n : ℕ} {f : (Fin n → 𝓧) → ℝ}, Measurable f →
      Measurable fun ω => 1 - f ω := fun hf => measurable_const.sub hf
  have hsub01 : ∀ {n : ℕ} {f : (Fin n → 𝓧) → ℝ}, (∀ ω, f ω ∈ Set.Icc (0 : ℝ) 1) →
      ∀ ω : Fin n → 𝓧, (1 - f ω) ∈ Set.Icc (0 : ℝ) 1 := by
    intro n f hf ω
    exact ⟨by linarith [(hf ω).2], by linarith [(hf ω).1]⟩
  refine ⟨fun n ω => max (φmod n ω) (φfar n ω), c, hcpos, ?_, ?_, ?_, ?_⟩
  · exact hφM
  · exact hφ01
  · -- Size at `θ₀`: `∫ max ≤ ∫ φmod + ∫ φfar → 0`.
    have hnn : ∀ n : ℕ,
        0 ≤ ∫ ω, max (φmod n ω) (φfar n ω) ∂(productMeasure M μ θ₀ n) :=
      fun n => integral_nonneg fun ω => (hφ01 n ω).1
    have hle : ∀ n : ℕ, ∫ ω, max (φmod n ω) (φfar n ω) ∂(productMeasure M μ θ₀ n)
        ≤ (∫ ω, φmod n ω ∂(productMeasure M μ θ₀ n))
          + ∫ ω, φfar n ω ∂(productMeasure M μ θ₀ n) := by
      intro n
      rw [← integral_add (integrable_of_test (hmodM n) (hmod01 n))
        (integrable_of_test (hfarM n) (hfar01 n))]
      refine integral_mono (integrable_of_test (hφM n) (hφ01 n))
        (((integrable_of_test (hmodM n) (hmod01 n)).add
          (integrable_of_test (hfarM n) (hfar01 n)))) fun ω => ?_
      exact max_le (by linarith [(hfar01 n ω).1]) (by linarith [(hmod01 n ω).1])
    refine squeeze_zero hnn hle ?_
    simpa using hmodI.add hfarI
  · -- Exponential type-II bound.
    refine ⟨max N₁ N₂, fun n hn θ hθ => ?_⟩
    have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
    have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmin_nonneg : (0 : ℝ) ≤ min (‖θ - θ₀‖ ^ 2) 1 :=
      le_min (sq_nonneg _) zero_le_one
    have hmin_le_one : min (‖θ - θ₀‖ ^ 2) 1 ≤ 1 := min_le_right _ _
    rcases le_total ‖θ - θ₀‖ ε₁ with hcase | hcase
    · -- Moderate range: use `φmod`.
      have hstep : ∫ ω, (1 - max (φmod n ω) (φfar n ω)) ∂(productMeasure M μ θ n)
          ≤ ∫ ω, (1 - φmod n ω) ∂(productMeasure M μ θ n) := by
        refine integral_mono (integrable_of_test (hsubM (hφM n)) (hsub01 (hφ01 n)))
          (integrable_of_test (hsubM (hmodM n)) (hsub01 (hmod01 n))) fun ω => ?_
        have : φmod n ω ≤ max (φmod n ω) (φfar n ω) := le_max_left _ _
        linarith
      refine hstep.trans ((hmodII n hn₁ θ hθ (hcase.trans hε₁leε)).trans ?_)
      refine Real.exp_le_exp.2 ?_
      have hsq : ‖θ - θ₀‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (θ - θ₀)]
      rw [min_eq_left hsq]
      have hnx : (0 : ℝ) ≤ (n : ℝ) * ‖θ - θ₀‖ ^ 2 := mul_nonneg hnnn (sq_nonneg _)
      linarith [mul_nonneg (sub_nonneg.2 hcmod') hnx]
    · -- Far range: use `φfar`.
      have hstep : ∫ ω, (1 - max (φmod n ω) (φfar n ω)) ∂(productMeasure M μ θ n)
          ≤ ∫ ω, (1 - φfar n ω) ∂(productMeasure M μ θ n) := by
        refine integral_mono (integrable_of_test (hsubM (hφM n)) (hsub01 (hφ01 n)))
          (integrable_of_test (hsubM (hfarM n)) (hsub01 (hfar01 n))) fun ω => ?_
        have : φfar n ω ≤ max (φmod n ω) (φfar n ω) := le_max_right _ _
        linarith
      refine hstep.trans ((hfarII n hn₂ θ hcase).trans ?_)
      refine Real.exp_le_exp.2 ?_
      linarith [mul_nonneg (mul_nonneg hcpos.le hnnn) (sub_nonneg.2 hmin_le_one),
        mul_nonneg (sub_nonneg.2 hcfar') hnnn]

end StatLean.Bayesian

