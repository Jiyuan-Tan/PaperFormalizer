module
public import StatLean.HypothesisTesting.Tests.Defs
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import StatLean.PointEstimation.ExponentialFamily.Smoothness

@[expose] public section

/-!
# Continuous power functions: boundary optimality ⇒ unbiased optimality

When every test has a **continuous** power function, unbiasedness of a test forces its power
to equal `α` on the *common boundary*
$$ \omega_B \;=\; \overline{\Theta_0} \cap \overline{\Theta_1} $$
of the null set `Θ₀` and the alternative set `Θ₁` (the set of points that are points or
limit points of both). Consequently the class of tests that are **similar on `ω_B`** contains
the class of unbiased level-`α` tests, and a test that is optimal in the larger (similar)
class and has level `α` is automatically UMP unbiased. This is the standard device that
converts the two-sided optimality problems into constrained Neyman–Pearson problems.

Main results:

* `isSimilar_boundary_of_isUnbiasedTest` — unbiased + continuous power ⇒ similar on `ω_B`;
* `isUMPU_of_isUMP_on_boundary` — optimal among boundary-similar tests + level `α` ⇒ UMPU;
* `continuous_power_expFamily` — power functions of exponential families are continuous on
  the interior of the natural parameter set (statement only here);
* `continuous_power_of_isCanonicalRepr` — the same for any continuous reparametrization.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.1 (Unbiasedness for Hypothesis Testing), Lemma 4.1.1 (a test with
continuous power that is UMP on the boundary is UMP unbiased). (`TSH4 §4.1 Lem 4.1.1`.)

**Proof formalization notes.**
* The boundary set is supplied as data together with the defining equation
  `ωB = closure Θ₀ ∩ closure Θ₁`, rather than as a definition, so that callers may
  instantiate it with the concrete finite boundary sets (`{θ₀}`, `{θ₁, θ₂}`) that the
  one-parameter applications use, discharging the equation once.
* Continuity of the power function is quantified over *all* critical functions: this is what
  the source development assumes, and it is exactly what the exponential-family smoothness
  theorem delivers.
* The constant test `φ ≡ α` is the comparison test used to derive unbiasedness of the
  optimal test; it is a critical function precisely when `0 ≤ α ≤ 1`, whence the two
  side conditions on `α`.
* `continuous_power_expFamily` is stated as `ContinuousOn` over `interior E.natSet`: at
  boundary points of the natural parameter set the interchange of limit and integral can
  fail, and the source theorem is likewise restricted to the interior.

**Bibliographic comments.** Unbiasedness for testing problems, and the boundary-similarity
device recorded here, are due to J. Neyman and E. S. Pearson ("Contributions to the theory
of testing statistical hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37),
building on their earlier optimality theory ("On the problem of the most efficient tests of
statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933), 289–337). The analyticity
of integrals against exponential-family densities, which supplies the continuity hypothesis,
goes back to the work systematized in O. Barndorff-Nielsen (*Information and Exponential
Families in Statistical Theory*, Wiley, 1978) and L. D. Brown (*Fundamentals of Statistical
Exponential Families*, IMS Lecture Notes 9, 1986).
-/

open MeasureTheory
open StatLean.PointEstimation
open scoped InnerProductSpace

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Unbiased ⇒ similar on the boundary.**

If every power function is continuous, then a test that is unbiased at level `α` for
`Θ₀` against `Θ₁` has power exactly `α` on the common boundary
`ωB = closure Θ₀ ∩ closure Θ₁`: on `closure Θ₀` continuity propagates `power ≤ α`, on
`closure Θ₁` it propagates `α ≤ power`. -/
theorem isSimilar_boundary_of_isUnbiasedTest [TopologicalSpace Θ]
    {P : Θ → Measure 𝓧} {Θ₀ Θ₁ ωB : Set Θ} {α : ℝ} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the boundary set is the set of points that are points or limit points of
    -- both the null and the alternative set; classical boundary of a testing problem
    (hωB : ωB = closure Θ₀ ∩ closure Θ₁)
    -- USER-INPUT: every test has a continuous power function; the regularity hypothesis of
    -- the boundary device
    (hcont : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → Continuous (power P ψ))
    -- USER-INPUT: the test under consideration is a randomized test
    (hφ : IsCriticalFn φ)
    -- USER-INPUT: the test is unbiased at level `α`
    (hunb : IsUnbiasedTest P Θ₀ Θ₁ α φ) :
    IsSimilar P ωB α φ := by
  have hcont_f : Continuous (power P φ) := hcont φ hφ
  -- on `closure Θ₀` continuity propagates `power ≤ α`
  have hle : closure Θ₀ ⊆ {θ | power P φ θ ≤ α} :=
    closure_minimal (fun θ hθ => hunb.1 θ hθ) (isClosed_le hcont_f continuous_const)
  -- on `closure Θ₁` continuity propagates `α ≤ power`
  have hge : closure Θ₁ ⊆ {θ | α ≤ power P φ θ} :=
    closure_minimal (fun θ hθ => hunb.2 θ hθ) (isClosed_le continuous_const hcont_f)
  intro θ hθ
  rw [hωB] at hθ
  exact le_antisymm (hle hθ.1) (hge hθ.2)

/-- **Boundary optimality ⇒ UMP unbiasedness.**

Assume every power function is continuous, and let `φ₀` be a level-`α` test that is similar
on the common boundary `ωB` and uniformly at least as powerful, on `Θ₁`, as every test that
is similar on `ωB`. Then `φ₀` is UMP unbiased at level `α`.

Two steps: the boundary-similar class contains the unbiased class
(`isSimilar_boundary_of_isUnbiasedTest`), so `φ₀` beats every unbiased competitor; and `φ₀`
is itself unbiased because the constant test `φ ≡ α` is boundary-similar.

The hypothesis `hsim` records that `φ₀` belongs to the class it is optimal in, as the source
formulation ("uniformly most powerful *among* the tests satisfying the boundary condition")
does; it is not consumed by the argument sketched above and may be dropped if a later
refactor prefers the minimal hypothesis set. -/
theorem isUMPU_of_isUMP_on_boundary [TopologicalSpace Θ]
    {P : Θ → Measure 𝓧} {Θ₀ Θ₁ ωB : Set Θ} {α : ℝ} {φ₀ : 𝓧 → ℝ}
    -- LEAN-ONLY: the family members are probability measures; needed so that the constant
    -- test `φ ≡ α` has power `α`, no scope change (every statistical model is such)
    [∀ θ, IsProbabilityMeasure (P θ)]
    -- USER-INPUT: the boundary set is the common boundary of null and alternative
    (hωB : ωB = closure Θ₀ ∩ closure Θ₁)
    -- USER-INPUT: every test has a continuous power function
    (hcont : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → Continuous (power P ψ))
    -- LEAN-ONLY: the level lies in `[0,1]`; needed for `φ ≡ α` to be a critical function
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    -- USER-INPUT: the candidate is a randomized test
    (hφ₀ : IsCriticalFn φ₀)
    -- USER-INPUT: the candidate has level `α` on the null set
    (hlevel : IsLevel P Θ₀ φ₀ α)
    -- USER-INPUT: the candidate is similar on the boundary
    (hsim : IsSimilar P ωB α φ₀)
    -- USER-INPUT: the candidate is uniformly most powerful among boundary-similar tests
    (hbest : ∀ ψ : 𝓧 → ℝ, IsCriticalFn ψ → IsSimilar P ωB α ψ →
      ∀ θ ∈ Θ₁, power P ψ θ ≤ power P φ₀ θ) :
    IsUMPU P Θ₀ Θ₁ α φ₀ := by
  -- the constant test `φ ≡ α` is a critical function and boundary-similar
  have hconst_crit : IsCriticalFn (fun _ : 𝓧 => α) :=
    ⟨measurable_const, fun _ => ⟨hα₀, hα₁⟩⟩
  have hconst_power : ∀ θ' : Θ, power P (fun _ : 𝓧 => α) θ' = α := fun θ' => by
    rw [power, integral_const, probReal_univ, one_smul]
  have hconst_sim : IsSimilar P ωB α (fun _ : 𝓧 => α) := fun θ' _ => hconst_power θ'
  refine ⟨hφ₀, ⟨hlevel, ?_⟩, ?_⟩
  · -- unbiasedness: `φ₀` beats the boundary-similar constant test on the alternative
    intro θ hθ
    have h := hbest (fun _ : 𝓧 => α) hconst_crit hconst_sim θ hθ
    rwa [hconst_power] at h
  · -- optimality among unbiased tests: they are boundary-similar, so `hbest` applies
    intro ψ hψ_crit hψ_unb θ hθ
    have hψ_sim : IsSimilar P ωB α ψ :=
      isSimilar_boundary_of_isUnbiasedTest hωB hcont hψ_crit hψ_unb
    exact hbest ψ hψ_crit hψ_sim θ hθ

/-- **Power functions of an exponential family are continuous on the interior of the natural
parameter set.**

For a bounded measurable `φ`, `η ↦ ∫ φ dP_η` is continuous on `interior E.natSet`. Writing
`P_η = ν.tilted ⟪η, T ·⟫`, the power is the ratio
`(∫ φ e^{⟪η,T⟫} dν) / (∫ e^{⟪η,T⟫} dν)`; both integrals are differentiable — hence continuous
— on the interior of the corresponding weighted natural parameter sets by
`ExpFamily.continuousOn_integral_exp_inner`, and `|φ| ≤ 1` places `E.natSet` inside the
`φ`-weighted natural set, so both are continuous on `interior E.natSet`. The denominator is
positive there whenever `ν ≠ 0`, and for `ν = 0` every `P_η` vanishes and the power is
constantly `0`.

**FLAGGED SIGNATURE AMENDMENT.** The two instance hypotheses `[BorelSpace V]` and
`[FiniteDimensional ℝ V]` were *added* to the frozen statement: without a finite-dimension
assumption the theorem is **false**. Counterexample. Let `V` be the incomplete inner-product
space `c₀₀ ⊆ ℓ²` of finitely supported real sequences, `𝓧 = ℕ` with the discrete σ-algebra,
`ν{0} = 1` and `ν{n} = e^{-n²}` for `n ≥ 1`, and `T 0 = 0`, `T n = n³ eₙ`. For finitely
supported `η` all but finitely many terms of `∫ e^{⟪η,T⟫} dν = 1 + ∑_{n≥1} e^{-n² + n³ηₙ}`
equal `e^{-n²}`, so `E.natSet = V` and `interior E.natSet = V ∋ 0`. Take `φ = 1_{\{0\}}`
(a critical function). The numerator `∫ φ e^{⟪η,T⟫} dν = 1` is constant, while at
`η_k = k⁻¹ e_k → 0` the denominator is `2 + S − e^{-k²}` versus `1 + S` at `η = 0`
(`S = ∑_{n≥1} e^{-n²}`), because the `n = k` term becomes `e^{-k² + k³/k} = 1`. So the power
tends to `1/(2+S) ≠ 1/(1+S)`. The failure is genuine: in infinite dimensions membership of
`η` in the *interior* of the natural parameter set does not bound `∫ e^{⟪·,T⟫} dν` on a
neighbourhood of `η`, which is exactly what the `2^{dim V}` sign-vector envelope of
`ExpFamily.integrable_abs_exp_inner_add_norm` supplies in finite dimensions. `[BorelSpace V]`
is likewise needed because the frozen signature leaves `MeasurableSpace V` unrelated to the
topology; every intended instantiation is `V = EuclideanSpace ℝ (Fin k)`, where both hold. -/
theorem continuous_power_expFamily {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V]
    -- LEAN-ONLY (AMENDMENT): the Borel structure ties the given `MeasurableSpace V` to the
    -- topology, and finite dimension supplies the sign-vector envelope dominating
    -- `e^{⟪η,T⟫}` on a ball; see the counterexample above — the statement is false without it
    [BorelSpace V] [FiniteDimensional ℝ V]
    (E : ExpFamily 𝓧 V) {φ : 𝓧 → ℝ}
    -- USER-INPUT: the integrand is a randomized test (bounded, measurable)
    (hφ : IsCriticalFn φ) :
    ContinuousOn (fun η => powerAgainst (E.P η) φ) (interior E.natSet) := by
  -- the two exponential integrals appearing in the tilted representation of the power
  set num : V → ℝ := fun η => ∫ x, φ x * Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base with hnum_def
  set den : V → ℝ := fun η => ∫ x, Real.exp ⟪η, E.stat x⟫_ℝ ∂E.base with hden_def
  -- `|φ| ≤ 1` puts the natural parameter set inside the `φ`-weighted one
  have hsub : E.natSet ⊆ E.weightedNatSet φ := by
    intro η hη
    refine (hη : Integrable _ _).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hφ.1.abs.aestronglyMeasurable).mul
        ((((innerSL ℝ η).continuous.measurable.comp E.stat_meas)).exp.aestronglyMeasurable)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc |φ x| * Real.exp ⟪η, E.stat x⟫_ℝ ≤ 1 * Real.exp ⟪η, E.stat x⟫_ℝ := by
            gcongr
            rw [abs_of_nonneg (hφ.2 x).1]; exact (hφ.2 x).2
        _ = Real.exp ⟪η, E.stat x⟫_ℝ := one_mul _
  -- continuity of the numerator, transported from the `φ`-weighted natural set
  have hnum : ContinuousOn num (interior E.natSet) :=
    (E.continuousOn_integral_exp_inner hφ.1).mono (interior_mono hsub)
  -- continuity of the denominator: the weight `1` has `weightedNatSet = natSet`
  have hwone : E.weightedNatSet (fun _ : 𝓧 => (1 : ℝ)) = E.natSet := by
    ext η; simp [ExpFamily.weightedNatSet, ExpFamily.natSet]
  have hden : ContinuousOn den (interior E.natSet) := by
    have h := E.continuousOn_integral_exp_inner
      (f := fun _ : 𝓧 => (1 : ℝ)) measurable_const
    rw [hwone] at h
    simpa only [one_mul, hden_def] using h
  -- the tilted representation `powerAgainst (E.P η) φ = num η / den η`
  have hrepr : ∀ η : V, powerAgainst (E.P η) φ = num η / den η := by
    intro η
    rw [powerAgainst, ExpFamily.P, integral_tilted]
    simp only [smul_eq_mul, hnum_def, hden_def]
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  simp only [hrepr]
  -- degenerate case: a zero reference measure makes every member measure zero
  rcases eq_zero_or_neZero E.base with hzero | _
  · refine ContinuousOn.congr (continuousOn_const (c := (0 : ℝ))) (fun η _ => ?_)
    simp only [hnum_def, hden_def, hzero]
    simp
  -- generic case: the denominator is a positive integral of a positive integrand
  refine hnum.div hden (fun η hη => ne_of_gt ?_)
  have hmem : η ∈ E.natSet := interior_subset hη
  have hmem' : Integrable (fun x => Real.exp ⟪η, E.stat x⟫_ℝ) E.base := hmem
  simpa only [hden_def] using integral_exp_pos hmem'

/-- **Continuity of the power function through a reparametrization.**

If `P'` is the canonical exponential family read through a continuous parameter map `ηmap`
taking values in the interior of the natural parameter set, then every power function of
`P'` is continuous — the hypothesis consumed by `isUMPU_of_isUMP_on_boundary`. -/
theorem continuous_power_of_isCanonicalRepr {Θ' V : Type*} [TopologicalSpace Θ']
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
    -- LEAN-ONLY (AMENDMENT): inherited from `continuous_power_expFamily`, where the
    -- unamended statement is false; see the counterexample recorded there
    [BorelSpace V] [FiniteDimensional ℝ V]
    {P' : Θ' → Measure 𝓧} {E : ExpFamily 𝓧 V} {ηmap : Θ' → V} {φ : 𝓧 → ℝ}
    -- USER-INPUT: the model is a reparametrized canonical exponential family
    (hrepr : IsCanonicalRepr P' E ηmap)
    -- USER-INPUT: the parametrization is continuous; classical smooth-parametrization input
    (hcont : Continuous ηmap)
    -- USER-INPUT: the parametrization stays in the interior of the natural parameter set
    (hmem : ∀ θ, ηmap θ ∈ interior E.natSet)
    -- USER-INPUT: the integrand is a randomized test
    (hφ : IsCriticalFn φ) :
    Continuous (power P' φ) := by
  have hpow : power P' φ = (fun η => powerAgainst (E.P η) φ) ∘ ηmap := by
    funext θ; rw [power, hrepr θ]; rfl
  rw [hpow]
  exact (continuous_power_expFamily E hφ).comp_continuous hcont hmem

end StatLean.HypothesisTesting
