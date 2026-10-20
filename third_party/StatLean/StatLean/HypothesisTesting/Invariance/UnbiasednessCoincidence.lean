module
public import StatLean.HypothesisTesting.Invariance.AlmostInvariance

@[expose] public section

/-!
# Unbiasedness and invariance coincide when the unbiased solution is unique

Unbiasedness and invariance are logically independent optimality restrictions: each
succeeds on problems where the other does not. Where both deliver a uniformly most
powerful member, however, the two answers agree — and this is not accidental.

The reason is a symmetry of the unbiased class itself. If the testing problem is invariant
under `G`, then a critical function is unbiased of level `α` exactly when its translate
`x ↦ φ(g·x)` is, because translation permutes the null and alternative classes through the
induced action. Hence if `φ*` is UMP unbiased, so is every translate of it, and all of them
have the same power function. If the UMP unbiased test is **unique up to null sets**, all
these translates collapse onto `φ*`, which therefore is almost invariant. A UMP almost
invariant test `φ` is then at least as powerful as `φ*`; conversely `φ` is itself unbiased
(compare it with the invariant constant test `x ↦ α`), so it is dominated by `φ*`. The two
power functions agree, and uniqueness of `φ*` forces `φ = φ*` almost everywhere — which in
passing also makes the UMP almost invariant test unique.

**Main result.** `umpu_eq_umpAlmostInvariant_ae` — with an explicit a.e.-uniqueness
hypothesis on the UMP unbiased test, a UMP unbiased test and a UMP almost invariant test
coincide almost everywhere, and the latter is itself a.e. unique.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.6
(Unbiasedness and Invariance), Theorem 6.6.1 (a unique UMP unbiased test and a UMP
almost-invariant test coincide). (`TSH4 §6.6 Thm 6.6.1`.)

**Proof formalization notes.**
* The uniqueness of the unbiased solution is an **explicit hypothesis** (`huniq`), exactly
  as in the source, which assumes "there exists a UMP unbiased test `φ*` which is unique
  up to sets of measure zero". It is stated as: every UMP unbiased level-`α` test agrees
  with `φ*` off a `μ`-null set.
* `μ` is a σ-finite measure equivalent to the family, the standard carrier of "a.e." for
  a dominated model; the equivalence is what lets power equality be converted into a.e.
  equality of tests and back.
* `0 ≤ α ≤ 1` is required because the argument compares the candidate against the constant
  test `x ↦ α`, which must itself be a critical function.
* Stability of the null and alternative classes under the induced action is what makes the
  unbiased class translation-stable; it is stated separately from model invariance.
* **Signature amendment (documented deviation).** The argument forms the translate
  `x ↦ φ*(g·x)` and needs it to be a critical function, i.e. `Measurable (g • ·)`. A bare
  `[MulAction G 𝓧]` does not supply this, and with a non-measurable action the translate is
  not a test at all, so the hypothesis `hsmul : ∀ g, Measurable (g • ·)` — the content of
  `[MeasurableSMul G 𝓧]`, stated as a plain hypothesis so no `MeasurableSpace G` structure
  has to be imposed — is added. This is the same amendment as in
  `Invariance/SufficiencyReduction.lean`.
* The proof turns out not to use `hequiv` (the "family-null ⟹ `μ`-null" half of the
  equivalence of `μ` with the family): only `hdom` is needed, to push the `μ`-a.e. almost
  invariance of `φ*` down to each member. `hequiv` is retained in the signature because it
  is part of the source's standing assumption that `μ` is equivalent to the family.

**Bibliographic comments.** Unbiasedness for tests was introduced by J. Neyman and
E. S. Pearson ("Contributions to the theory of testing statistical hypotheses," *Stat.
Res. Mem.* **1** (1936), 1–37). The consistency of the unbiasedness and (almost)
invariance principles, in the form proved here, belongs to E. L. Lehmann's development of
invariance in the 1950s, resting on the Hunt–Stein circle of ideas (G. A. Hunt and
C. Stein, "Most stringent tests of statistical hypotheses," unpublished manuscript, 1946;
C. Stein, "Some problems in multivariate analysis, Part I," Technical Report 6, Department
of Statistics, Stanford University, 1956). Uniqueness of the unbiased solution, in the
exponential-family setting where it is typically verified, comes from the completeness
theory of E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased
estimation," *Sankhyā* **10** (1950), 305–340).
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (IsInvariantModel)

variable {G Θ 𝓧 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] [MulAction G Θ]

/-- **A UMP unbiased test and a UMP almost invariant test coincide a.e.** Given an
invariant testing problem, a σ-finite measure equivalent to the family, and an explicit
a.e.-uniqueness hypothesis on the UMP unbiased test, the UMP almost invariant test equals
the UMP unbiased test off a null set — and is itself unique up to null sets. -/
theorem umpu_eq_umpAlmostInvariant_ae {P : Θ → Measure 𝓧} [∀ θ, IsProbabilityMeasure (P θ)]
    {μ : Measure 𝓧} [SigmaFinite μ] {Θ₀ Θ₁ : Set Θ} {α : ℝ} {φstar φ : 𝓧 → ℝ}
    -- USER-INPUT: the model intertwines the sample- and parameter-space actions
    (hP : IsInvariantModel (G := G) P)
    -- USER-INPUT (amendment, see the module note): `G` acts on the sample space by
    -- measurable maps
    (hsmul : ∀ g : G, Measurable fun x : 𝓧 => g • x)
    -- USER-INPUT: the null and alternative classes are preserved by the induced action
    (hΘ₀ : ∀ (g : G) (θ : Θ), θ ∈ Θ₀ → g • θ ∈ Θ₀)
    (hΘ₁ : ∀ (g : G) (θ : Θ), θ ∈ Θ₁ → g • θ ∈ Θ₁)
    -- USER-INPUT: `μ` is equivalent to the family: every member is `μ`-absolutely
    -- continuous, and a set null under every member is `μ`-null
    (hdom : ∀ θ, P θ ≪ μ)
    (hequiv : ∀ A : Set 𝓧, MeasurableSet A → (∀ θ, P θ A = 0) → μ A = 0)
    -- USER-INPUT: the prescribed level is a probability, so the constant test `x ↦ α`
    -- is an admissible (invariant) competitor
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    -- USER-INPUT: `φstar` is UMP unbiased at level `α`
    (hstar : IsUMPU P Θ₀ Θ₁ α φstar)
    -- USER-INPUT: the UMP unbiased test is unique up to sets of measure zero
    (huniq : ∀ ψ : 𝓧 → ℝ, IsUMPU P Θ₀ Θ₁ α ψ → ψ =ᵐ[μ] φstar)
    -- USER-INPUT: `φ` is UMP among almost invariant level-`α` tests
    (hφ : IsUMPAlmostInvariant G P Θ₀ Θ₁ α φ) :
    φ =ᵐ[μ] φstar ∧ ∀ ψ : 𝓧 → ℝ, IsUMPAlmostInvariant G P Θ₀ Θ₁ α ψ → ψ =ᵐ[μ] φ := by
  -- Translating a test along `g` shifts its power function along the induced action.
  have hshiftpow : ∀ (χ : 𝓧 → ℝ), Measurable χ → ∀ (g : G) (θ : Θ),
      power P (fun x => χ (g • x)) θ = power P χ (g • θ) := by
    intro χ hχ g θ
    simp only [power]
    rw [← hP g θ, integral_map (hsmul g).aemeasurable hχ.aestronglyMeasurable]
  -- Translating a critical function keeps it critical.
  have hshiftcrit : ∀ (χ : 𝓧 → ℝ), IsCriticalFn χ → ∀ g : G,
      IsCriticalFn (fun x => χ (g • x)) := fun χ hχ g =>
    ⟨hχ.1.comp (hsmul g), fun x => hχ.2 _⟩
  -- Translating an unbiased test keeps it unbiased: the induced action permutes the classes.
  have hshiftunb : ∀ (χ : 𝓧 → ℝ), Measurable χ → IsUnbiasedTest P Θ₀ Θ₁ α χ → ∀ g : G,
      IsUnbiasedTest P Θ₀ Θ₁ α (fun x => χ (g • x)) := by
    intro χ hχ hunb g
    refine ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩
    · rw [hshiftpow χ hχ g θ]; exact hunb.1 _ (hΘ₀ g θ hθ)
    · rw [hshiftpow χ hχ g θ]; exact hunb.2 _ (hΘ₁ g θ hθ)
  -- (1) Every translate of `φstar` is again UMP unbiased.
  have hstarshift : ∀ g : G, IsUMPU P Θ₀ Θ₁ α (fun x => φstar (g • x)) := by
    intro g
    refine ⟨hshiftcrit φstar hstar.1 g, hshiftunb φstar hstar.1.1 hstar.2.1 g, ?_⟩
    intro χ hχcrit hχunb θ hθ
    -- compare `χ` with its translate by `g⁻¹`, which is again unbiased
    have hkey := hstar.2.2 (fun x => χ (g⁻¹ • x)) (hshiftcrit χ hχcrit g⁻¹)
      (hshiftunb χ hχcrit.1 hχunb g⁻¹) (g • θ) (hΘ₁ g θ hθ)
    rw [hshiftpow χ hχcrit.1 g⁻¹ (g • θ), inv_smul_smul] at hkey
    rw [hshiftpow φstar hstar.1.1 g θ]
    exact hkey
  -- ... hence, by uniqueness, `φstar` is almost invariant with respect to `μ`.
  have hstarai : IsAlmostInvariant G μ φstar := fun g => huniq _ (hstarshift g)
  have hstaraiP : ∀ θ : Θ, IsAlmostInvariant G (P θ) φstar := fun θ g =>
    (hstarai g).filter_mono (hdom θ).ae_le
  -- The main run: any UMP almost invariant test agrees a.e. with `φstar`.
  have hmain : ∀ χ : 𝓧 → ℝ, IsUMPAlmostInvariant G P Θ₀ Θ₁ α χ → χ =ᵐ[μ] φstar := by
    intro χ hχ
    -- (2) `φstar` is an almost-invariant level-`α` competitor, so `χ` beats it on `Θ₁`.
    have hge : ∀ θ ∈ Θ₁, power P φstar θ ≤ power P χ θ :=
      hχ.2.2.2 φstar hstar.1 hstaraiP hstar.2.1.1
    -- (3) comparing `χ` with the constant test `x ↦ α` shows `χ` is unbiased.
    have hconstpow : ∀ θ : Θ, power P (fun _ : 𝓧 => α) θ = α := by
      intro θ; simp [power]
    have hχunb : IsUnbiasedTest P Θ₀ Θ₁ α χ := by
      refine ⟨hχ.2.2.1, fun θ hθ => ?_⟩
      have h := hχ.2.2.2 (fun _ => α) ⟨measurable_const, fun _ => ⟨hα0, hα1⟩⟩
        (fun θ' _ => ae_of_all _ fun _ => rfl)
        (fun θ' _ => by rw [hconstpow θ']) θ hθ
      rwa [hconstpow θ] at h
    -- (4) so `hstar` dominates `χ`; the two powers agree on `Θ₁` and `χ` is itself UMPU.
    have hle : ∀ θ ∈ Θ₁, power P χ θ ≤ power P φstar θ := hstar.2.2 χ hχ.1 hχunb
    exact huniq χ ⟨hχ.1, hχunb, fun ξ hξcrit hξunb θ hθ =>
      (hstar.2.2 ξ hξcrit hξunb θ hθ).trans (hge θ hθ)⟩
  exact ⟨hmain φ hφ, fun ψ hψ => (hmain ψ hψ).trans (hmain φ hφ).symm⟩

end StatLean.HypothesisTesting
