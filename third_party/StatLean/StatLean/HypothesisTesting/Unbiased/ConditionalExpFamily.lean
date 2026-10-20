module
public import StatLean.HypothesisTesting.Tests.Defs
public import StatLean.HypothesisTesting.ForMathlib.CondDistribTilt
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The conditional exponential family engine

A multiparameter exponential family in which one coordinate `θ` is of interest and the
remaining coordinates `ϑ` are nuisance parameters may be reduced to its sufficient statistic
`(U, T)`, whose joint law is again exponential:
$$ dP^{U,T}_{\theta,\vartheta}(u,t) \;=\; C(\theta,\vartheta)\,
   \exp\bigl(\theta u + \langle \vartheta, t\rangle\bigr)\, d\nu(u,t). $$
This is `IsCanonicalUT`. The engine of the multiparameter theory is the observation that
**conditionally on `T = t`** this collapses to a *one-parameter* exponential family in `θ`,
$$ dP^{U\mid t}_{\theta}(u) \;=\; C_t(\theta)\, e^{\theta u}\, d\nu_t(u), $$
whose base measure `ν_t` depends only on `t` and whose normalizer `C_t(θ)` depends only on
`(t, θ)`: **the nuisance parameter `ϑ` has disappeared**. Every conditional test built on this
family therefore has a `ϑ`-free conditional size, and the one-parameter optimality theory
applies surface by surface.

Contents:

* `IsCanonicalUT` — the canonical joint form of the sufficient statistic;
* `condDistrib_expFamily_of_isCanonicalUT` — the conditional law of `U` given `T = t` is a
  one-parameter exponential family with `(θ,ϑ)`-free base and `ϑ`-free normalizer;
* `condDistrib_eq_of_fst_eq` — the conditional law depends on `(θ, ϑ)` only through `θ`;
* `integral_eq_integral_condDistrib` — the overall power of a test is the average of its
  conditional powers over the law of `T`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 4 (Unbiasedness: Theory
and First Applications), §4.4 (UMP Unbiased Tests for Multiparameter Exponential Families),
Lemma 4.4.1 (the canonical `(U,T)` form and the conditional exponential family obtained by
conditioning on `T`). (`TSH4 §4.4 Lem 4.4.1`.)

**Proof formalization notes.**
* The conditional law is Mathlib's `condDistrib U T (P p)`, a Markov kernel `Ξ ⇝ ℝ`
  determined up to `((P p).map T)`-null sets; every conclusion below is therefore stated
  almost everywhere with respect to the law of `T`. Since all members of an exponential
  family with a common base measure are mutually absolutely continuous, the null sets do
  not depend on the parameter, so "a.e. `t`" is unambiguous across the family.
* The tilting computation behind `condDistrib_expFamily_of_isCanonicalUT` — the conditional
  distribution of a `withDensity`-tilted joint law on a standard Borel space is the tilt of
  the conditional distribution — is the sibling-drafted brick
  `StatLean/HypothesisTesting/ForMathlib/CondDistribTilt.lean`; the existential produced
  here (`νt`, `Ct`) is meant to be read off from that brick applied to the joint density
  `exp(θu + ⟪ϑ,t⟫)`, in which the `ϑ`-dependent factor `exp⟪ϑ,t⟫` is `u`-free and hence
  cancels between numerator and normalizer.
* **Signature amendment.** `condDistrib_expFamily_of_isCanonicalUT` and
  `condDistrib_eq_of_fst_eq` carry an added instance `[OpensMeasurableSpace Ξ]`: without it
  the σ-algebra of `Ξ` is unrelated to its topology, the canonical density need not be
  measurable, and neither `withDensity_mul` nor the tilt engine applies. It is documented at
  each theorem; `[SecondCountableTopology Ξ]` is *not* needed.
* `IsCanonicalUT` is a predicate on a supplied family rather than a bundled structure, so
  that a model may be presented in any parametrization and identified with the canonical
  form only on the parameter set `Ω` actually used. Off `Ω` it says nothing.
* No positivity or σ-finiteness is imposed on the base measures in the statement: they are
  consequences of the canonical form on standard Borel spaces and belong in the proof, not
  the signature.

**Bibliographic comments.** Conditioning on a sufficient statistic to eliminate nuisance
parameters is due to J. Neyman ("Outline of a theory of statistical estimation based on the
classical theory of probability," *Phil. Trans. R. Soc. A* **236** (1937), 333–380) and
J. Neyman and E. S. Pearson ("Contributions to the theory of testing statistical
hypotheses," *Statistical Research Memoirs* **1** (1936), 1–37); the completeness theory
that makes the reduction lossless is due to E. L. Lehmann and H. Scheffé ("Completeness,
similar regions, and unbiased estimation," *Sankhyā* **10** (1950), 305–340; **15** (1955),
219–236).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.HypothesisTesting

variable {𝓧 Ξ : Type*} [MeasurableSpace 𝓧]
  [NormedAddCommGroup Ξ] [InnerProductSpace ℝ Ξ] [MeasurableSpace Ξ]

/-- **Canonical `(U, T)` exponential family.**

The joint law of the sufficient statistic `(U, T)` under the parameter `(θ, ϑ) ∈ Ω` has
density `C(θ,ϑ)·exp(θ·u + ⟪ϑ, t⟫)` with respect to a fixed parameter-free measure `ν` on
the range of `(U, T)`. Here `U` carries the parameter of interest `θ` and `T` carries the
nuisance parameters `ϑ`.

Edge behaviour: the condition is imposed only for parameters in `Ω`; members of `P` outside
`Ω` are unconstrained. -/
def IsCanonicalUT (P : ℝ × Ξ → Measure 𝓧) (Ω : Set (ℝ × Ξ)) (U : 𝓧 → ℝ) (T : 𝓧 → Ξ)
    (ν : Measure (ℝ × Ξ)) (C : ℝ × Ξ → ℝ) : Prop :=
  ∀ p ∈ Ω, (P p).map (fun x => (U x, T x))
    = ν.withDensity fun z => ENNReal.ofReal (C p * Real.exp (p.1 * z.1 + ⟪p.2, z.2⟫_ℝ))

/-- Measurability of the canonical exponential density `z ↦ C·exp(θ z.1 + ⟪ϑ, z.2⟫)` on the
product `ℝ × Ξ`. This is the one place where the Borel-compatibility of the σ-algebra of the
nuisance space is used: `[OpensMeasurableSpace Ξ]` makes the continuous linear functional
`t ↦ ⟪ϑ, t⟫` measurable. -/
private lemma measurable_canonicalDensity [OpensMeasurableSpace Ξ] (c θ : ℝ) (ϑ : Ξ) :
    Measurable fun z : ℝ × Ξ => ENNReal.ofReal (c * Real.exp (θ * z.1 + ⟪ϑ, z.2⟫_ℝ)) := by
  have h : Measurable fun z : ℝ × Ξ => ⟪ϑ, z.2⟫_ℝ :=
    ((innerSL ℝ ϑ).continuous.measurable).comp measurable_snd
  exact (((measurable_const.mul measurable_fst).add h).exp.const_mul c).ennreal_ofReal

/-- **The conditional law of `U` given `T = t` is a one-parameter exponential family.**

For a canonical `(U, T)` family there are a base measure `ν_t` on the line depending only on
`t` and normalizers `C_t(θ)` depending only on `(t, θ)` — in particular **not** on the
nuisance parameter `ϑ` — such that, for every parameter in `Ω` and almost every `t`,
`dP^{U|t}_θ(u) = C_t(θ)·e^{θu}·dν_t(u)`.

This is the reduction that makes the whole multiparameter theory one-parameter: the
conditional problem given `T = t` is a one-parameter exponential family in `θ` with natural
statistic `u`.

**FLAGGED SIGNATURE AMENDMENT.** The instance `[OpensMeasurableSpace Ξ]` was *added* to the
frozen statement. It is the exact hypothesis making the nuisance factor `t ↦ ⟪ϑ, t⟫` — hence
the canonical density `z ↦ C(p)·exp(θ z.1 + ⟪ϑ, z.2⟫)` itself — measurable, which every step
of the proof consumes: `withDensity_mul` (to rewrite the joint law of `(U,T)` at `p` as a
product-form tilt of the joint law at a reference parameter `p₀`) and
`condDistrib_fst_withDensity_tilt` (to cancel the nuisance factor from the conditional law)
both require measurable factors. Without it the frozen `[MeasurableSpace Ξ]` is unrelated to
the topology of `Ξ` and the density appearing in `IsCanonicalUT` need not be measurable, so
`Measure.withDensity` silently replaces it by its largest measurable minorant. That does not
make the conclusion false — it tends to make the *hypothesis* degenerate instead: e.g. for
`Ξ = ℝ` with the trivial σ-algebra the largest measurable minorant of
`exp(θu + ϑt)` over each atom `ℝ × ℝ` is `0` whenever `ϑ ≠ 0`, so `IsCanonicalUT` forces
`ϑ = 0` for every `p ∈ Ω` and the family is measurable after all — but no route is known that
proves the statement without a measurable density. Every intended instantiation
(`Ξ = EuclideanSpace ℝ (Fin k)`) satisfies the instance. `[SecondCountableTopology Ξ]` is
*not* needed: the argument never compares `borel (ℝ × Ξ)` with the product σ-algebra. -/
theorem condDistrib_expFamily_of_isCanonicalUT
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ}
    -- LEAN-ONLY: the family members are probability measures; needed for `condDistrib`
    [∀ p, IsProbabilityMeasure (P p)]
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of the nuisance space contains the open sets, so
    -- that the linear functionals `t ↦ ⟪ϑ, t⟫` are measurable; see the docstring
    [OpensMeasurableSpace Ξ]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C) :
    ∃ (νt : Ξ → Measure ℝ) (Ct : Ξ → ℝ → ℝ),
      ∀ p ∈ Ω, ∀ᵐ t ∂((P p).map T),
        condDistrib U T (P p) t
          = (νt t).withDensity fun u => ENNReal.ofReal (Ct t p.1 * Real.exp (p.1 * u)) := by
  classical
  rcases Set.eq_empty_or_nonempty Ω with hΩ | ⟨p₀, hp₀⟩
  · exact ⟨fun _ => 0, fun _ _ => 0, fun p hp => absurd (hΩ ▸ hp) (Set.notMem_empty p)⟩
  have hUTm : Measurable fun x => (U x, T x) := hU.prodMk hT
  haveI hQprob : ∀ q, IsProbabilityMeasure ((P q).map fun x => (U x, T x)) := fun _ =>
    Measure.isProbabilityMeasure_map hUTm.aemeasurable
  -- the normalizing constants are strictly positive on `Ω`: a nonpositive one would make the
  -- density vanish identically and the joint law the zero measure
  have hCpos : ∀ q ∈ Ω, 0 < C q := by
    intro q hq
    by_cases hpos : 0 < C q
    · exact hpos
    exfalso
    have hle : C q ≤ 0 := not_lt.mp hpos
    have hzero : ((P q).map fun x => (U x, T x)) = 0 := by
      rw [hUT q hq]
      have hd0 : (fun z : ℝ × Ξ =>
          ENNReal.ofReal (C q * Real.exp (q.1 * z.1 + ⟪q.2, z.2⟫_ℝ))) = 0 := by
        funext z
        have hpos := Real.exp_pos (q.1 * z.1 + ⟪q.2, z.2⟫_ℝ)
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
        nlinarith
      rw [hd0, withDensity_zero]
    have h1 := (hQprob q).measure_univ
    rw [hzero] at h1
    simp at h1
  have hC₀ : (0 : ℝ) < C p₀ := hCpos p₀ hp₀
  -- the conditional law of the interest statistic under the reference parameter
  set Q₀ : Measure (ℝ × Ξ) := (P p₀).map fun x => (U x, T x) with hQ₀
  haveI : IsProbabilityMeasure Q₀ := hQprob p₀
  set κ₀ : Kernel Ξ ℝ := condDistrib Prod.fst Prod.snd Q₀ with hκ₀
  -- the conditional law computed from the joint law of `(U, T)` is the conditional law of `U`
  have hck : ∀ (ρ₁ ρ₂ : Measure (Ξ × ℝ)) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂],
      ρ₁ = ρ₂ → ρ₁.condKernel = ρ₂.condKernel := by
    rintro ρ₁ ρ₂ _ _ rfl; rfl
  have hcd : ∀ q : ℝ × Ξ, condDistrib Prod.fst Prod.snd ((P q).map fun x => (U x, T x))
      = condDistrib U T (P q) := by
    intro q
    have hmap : (((P q).map fun x => (U x, T x)).map fun z : ℝ × Ξ => (z.2, z.1))
        = (P q).map fun a => (T a, U a) :=
      Measure.map_map (measurable_snd.prodMk measurable_fst) hUTm
    rw [condDistrib, condDistrib]
    exact hck _ _ hmap
  refine ⟨fun t => (κ₀ t).withDensity fun u => ENNReal.ofReal (Real.exp (-(p₀.1 * u))),
    fun t θ => (∫⁻ u, ENNReal.ofReal (Real.exp ((θ - p₀.1) * u)) ∂(κ₀ t)).toReal⁻¹, ?_⟩
  intro p hp
  -- the product-form tilt taking the reference joint law to the joint law at `p`
  set g : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp ((p.1 - p₀.1) * u)) with hg_def
  set k : Ξ → ℝ≥0∞ := fun t => ENNReal.ofReal (C p / C p₀ * Real.exp ⟪p.2 - p₀.2, t⟫_ℝ)
    with hk_def
  have hg : Measurable g := ((measurable_id.const_mul (p.1 - p₀.1)).exp).ennreal_ofReal
  have hk : Measurable k :=
    ((((innerSL ℝ (p.2 - p₀.2)).continuous.measurable).exp).const_mul (C p / C p₀)).ennreal_ofReal
  have hreal : ∀ (u : ℝ) (t : Ξ),
      C p * Real.exp (p.1 * u + ⟪p.2, t⟫_ℝ)
        = C p₀ * Real.exp (p₀.1 * u + ⟪p₀.2, t⟫_ℝ) *
            (Real.exp ((p.1 - p₀.1) * u) * (C p / C p₀ * Real.exp ⟪p.2 - p₀.2, t⟫_ℝ)) := by
    intro u t
    have h1 : Real.exp (p₀.1 * u) ≠ 0 := (Real.exp_pos _).ne'
    have h2 : Real.exp ⟪p₀.2, t⟫_ℝ ≠ 0 := (Real.exp_pos _).ne'
    rw [inner_sub_left, sub_mul, Real.exp_add, Real.exp_add, Real.exp_sub, Real.exp_sub]
    field_simp
  have hprodm : Measurable fun z : ℝ × Ξ => g z.1 * k z.2 :=
    (hg.comp measurable_fst).mul (hk.comp measurable_snd)
  have hfac : ((P p).map fun x => (U x, T x)) = Q₀.withDensity fun z => g z.1 * k z.2 := by
    rw [hUT p hp, hQ₀, hUT p₀ hp₀,
      ← withDensity_mul _ (measurable_canonicalDensity _ _ _) hprodm]
    congr 1
    funext z
    simp only [Pi.mul_apply, hg_def, hk_def]
    rw [hreal z.1 z.2, ENNReal.ofReal_mul (mul_nonneg hC₀.le (Real.exp_pos _).le),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  -- the tilt engine: the nuisance factor `k` cancels from the conditional law
  have htilt := condDistrib_fst_withDensity_tilt Q₀ ((P p).map fun x => (U x, T x)) hg hk hfac
  have hposC := condTiltNormalizer_pos_lt_top_ae Q₀ ((P p).map fun x => (U x, T x)) hg hk hfac
  have hsnd : (((P p).map fun x => (U x, T x)).map Prod.snd) = (P p).map T := by
    rw [Measure.map_map measurable_snd hUTm]
    rfl
  rw [← hsnd]
  filter_upwards [htilt, hposC] with t ht hpos
  rw [← hcd p, ht]
  -- identify the normalised tilt of the reference conditional law with the asserted
  -- one-parameter exponential form
  set Cn := condTiltNormalizer Q₀ g t with hCn_def
  have hCnReal : (0 : ℝ) < Cn.toReal := ENNReal.toReal_pos hpos.1.ne' hpos.2.ne
  have hofCn : ENNReal.ofReal Cn.toReal⁻¹ = Cn⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hCnReal, ENNReal.ofReal_toReal hpos.2.ne]
  have hCtval : (∫⁻ u, ENNReal.ofReal (Real.exp ((p.1 - p₀.1) * u)) ∂(κ₀ t)) = Cn := by
    rw [hCn_def, condTiltNormalizer, hg_def, hκ₀]
  have he₀ : Measurable fun u : ℝ => ENNReal.ofReal (Real.exp (-(p₀.1 * u))) :=
    (((measurable_id.const_mul p₀.1).neg).exp).ennreal_ofReal
  have hD : Measurable fun u : ℝ => ENNReal.ofReal (Cn.toReal⁻¹ * Real.exp (p.1 * u)) :=
    (((measurable_id.const_mul p.1).exp).const_mul _).ennreal_ofReal
  have hdens : (fun u : ℝ => ENNReal.ofReal (Real.exp (-(p₀.1 * u)))) *
      (fun u : ℝ => ENNReal.ofReal (Cn.toReal⁻¹ * Real.exp (p.1 * u))) = Cn⁻¹ • g := by
    funext u
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, hg_def]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← hofCn,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [sub_mul, Real.exp_sub, Real.exp_neg, div_eq_mul_inv]
    ring
  simp only [hCtval]
  rw [← withDensity_mul _ he₀ hD, hdens, withDensity_smul _ hg]

/-- **The conditional law does not depend on the nuisance parameter.**

Two parameters of `Ω` sharing the same coordinate of interest `θ` induce the same
conditional distribution of `U` given `T = t`, for almost every `t`. Immediate from
`condDistrib_expFamily_of_isCanonicalUT`, since the right-hand side there mentions the
parameter only through `p.1`.

The proof does not go through that theorem but through the same engine specialised to a
*pure nuisance* tilt: when `p.1 = q.1` the joint law at `p` is the joint law at `q`
reweighted by the `u`-free factor `k(t) = (C p / C q)·exp⟪ϑp − ϑq, t⟫`, i.e. the case
`g ≡ 1` of `condDistrib_fst_withDensity_tilt`, whose conditional normaliser is `1`. This
keeps the conclusion on the `p`-marginal of `T`, which is the filter asked for, and avoids
transporting an almost-everywhere statement across the two marginals.

**FLAGGED SIGNATURE AMENDMENT.** `[OpensMeasurableSpace Ξ]` was added, for the same reason
as in `condDistrib_expFamily_of_isCanonicalUT`; see that docstring. -/
theorem condDistrib_eq_of_fst_eq
    {P : ℝ × Ξ → Measure 𝓧} {Ω : Set (ℝ × Ξ)} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ}
    {ν : Measure (ℝ × Ξ)} {C : ℝ × Ξ → ℝ} {p q : ℝ × Ξ}
    -- LEAN-ONLY: the family members are probability measures; needed for `condDistrib`
    [∀ p, IsProbabilityMeasure (P p)]
    -- LEAN-ONLY (AMENDMENT): the σ-algebra of the nuisance space contains the open sets, so
    -- that the nuisance factor `t ↦ exp⟪ϑp − ϑq, t⟫` is measurable; see the docstring
    [OpensMeasurableSpace Ξ]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- USER-INPUT: the joint law of `(U, T)` is in canonical exponential form on `Ω`
    (hUT : IsCanonicalUT P Ω U T ν C)
    -- USER-INPUT: both parameters belong to the parameter set
    (hp : p ∈ Ω) (hq : q ∈ Ω)
    -- USER-INPUT: the two parameters agree in the coordinate of interest
    (hfst : p.1 = q.1) :
    ∀ᵐ t ∂((P p).map T), condDistrib U T (P p) t = condDistrib U T (P q) t := by
  classical
  have hUTm : Measurable fun x => (U x, T x) := hU.prodMk hT
  haveI hQprob : ∀ r, IsProbabilityMeasure ((P r).map fun x => (U x, T x)) := fun _ =>
    Measure.isProbabilityMeasure_map hUTm.aemeasurable
  have hCpos : ∀ r ∈ Ω, 0 < C r := by
    intro r hr
    by_cases hpos : 0 < C r
    · exact hpos
    exfalso
    have hle : C r ≤ 0 := not_lt.mp hpos
    have hzero : ((P r).map fun x => (U x, T x)) = 0 := by
      rw [hUT r hr]
      have hd0 : (fun z : ℝ × Ξ =>
          ENNReal.ofReal (C r * Real.exp (r.1 * z.1 + ⟪r.2, z.2⟫_ℝ))) = 0 := by
        funext z
        have hexp := Real.exp_pos (r.1 * z.1 + ⟪r.2, z.2⟫_ℝ)
        simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero]
        nlinarith
      rw [hd0, withDensity_zero]
    have h1 := (hQprob r).measure_univ
    rw [hzero] at h1
    simp at h1
  have hCq : (0 : ℝ) < C q := hCpos q hq
  haveI : IsProbabilityMeasure ((P q).map fun x => (U x, T x)) := hQprob q
  have hck : ∀ (ρ₁ ρ₂ : Measure (Ξ × ℝ)) [IsFiniteMeasure ρ₁] [IsFiniteMeasure ρ₂],
      ρ₁ = ρ₂ → ρ₁.condKernel = ρ₂.condKernel := by
    rintro ρ₁ ρ₂ _ _ rfl; rfl
  have hcd : ∀ r : ℝ × Ξ, condDistrib Prod.fst Prod.snd ((P r).map fun x => (U x, T x))
      = condDistrib U T (P r) := by
    intro r
    have hmap : (((P r).map fun x => (U x, T x)).map fun z : ℝ × Ξ => (z.2, z.1))
        = (P r).map fun a => (T a, U a) :=
      Measure.map_map (measurable_snd.prodMk measurable_fst) hUTm
    rw [condDistrib, condDistrib]
    exact hck _ _ hmap
  -- the pure nuisance factor
  have hk : Measurable fun t : Ξ =>
      ENNReal.ofReal (C p / C q * Real.exp ⟪p.2 - q.2, t⟫_ℝ) :=
    ((((innerSL ℝ (p.2 - q.2)).continuous.measurable).exp).const_mul (C p / C q)).ennreal_ofReal
  have hreal : ∀ (u : ℝ) (t : Ξ),
      C p * Real.exp (p.1 * u + ⟪p.2, t⟫_ℝ)
        = C q * Real.exp (q.1 * u + ⟪q.2, t⟫_ℝ) *
            (C p / C q * Real.exp ⟪p.2 - q.2, t⟫_ℝ) := by
    intro u t
    have h2 : Real.exp ⟪q.2, t⟫_ℝ ≠ 0 := (Real.exp_pos _).ne'
    rw [hfst, inner_sub_left, Real.exp_add, Real.exp_add, Real.exp_sub]
    field_simp
  have hprodm : Measurable fun z : ℝ × Ξ =>
      (1 : ℝ → ℝ≥0∞) z.1 * ENNReal.ofReal (C p / C q * Real.exp ⟪p.2 - q.2, z.2⟫_ℝ) := by
    simp only [Pi.one_apply, one_mul]
    exact hk.comp measurable_snd
  have hfac : ((P p).map fun x => (U x, T x))
      = ((P q).map fun x => (U x, T x)).withDensity fun z =>
          (1 : ℝ → ℝ≥0∞) z.1 * ENNReal.ofReal (C p / C q * Real.exp ⟪p.2 - q.2, z.2⟫_ℝ) := by
    rw [hUT p hp, hUT q hq,
      ← withDensity_mul _ (measurable_canonicalDensity _ _ _) hprodm]
    congr 1
    funext z
    simp only [Pi.mul_apply, Pi.one_apply, one_mul]
    rw [hreal z.1 z.2, ENNReal.ofReal_mul (mul_nonneg hCq.le (Real.exp_pos _).le)]
  have htilt := condDistrib_fst_withDensity_tilt ((P q).map fun x => (U x, T x))
    ((P p).map fun x => (U x, T x)) measurable_one hk hfac
  have hsnd : (((P p).map fun x => (U x, T x)).map Prod.snd) = (P p).map T := by
    rw [Measure.map_map measurable_snd hUTm]
    rfl
  rw [← hsnd]
  filter_upwards [htilt] with t ht
  have hnorm : condTiltNormalizer ((P q).map fun x => (U x, T x)) (1 : ℝ → ℝ≥0∞) t = 1 := by
    rw [condTiltNormalizer]
    simp only [Pi.one_apply, lintegral_one]
    exact measure_univ
  rw [← hcd p, ← hcd q, ht, hnorm, withDensity_one, inv_one, one_smul]

/-- **Overall power is the average of conditional powers.**

For a test `φ` of the sufficient statistic, the power against `P_{θ,ϑ}` is obtained by
averaging the conditional power on each surface `T = t` over the law of `T`:
`E_{θ,ϑ}[φ(U,T)] = ∫ (∫ φ(u,t) dP^{U|t}_θ(u)) dP^T_{θ,ϑ}(t)`.

This is the identity by which maximizing the conditional power surface by surface maximizes
the unconditional power; it is a disintegration statement and needs no exponential-family
structure. -/
theorem integral_eq_integral_condDistrib
    {P : ℝ × Ξ → Measure 𝓧} {U : 𝓧 → ℝ} {T : 𝓧 → Ξ} {p : ℝ × Ξ} {φ : ℝ × Ξ → ℝ}
    -- LEAN-ONLY: the family members are probability measures; needed for `condDistrib`
    [∀ p, IsProbabilityMeasure (P p)]
    -- USER-INPUT: the two components of the sufficient statistic are measurable
    (hU : Measurable U) (hT : Measurable T)
    -- LEAN-ONLY: measurability of the integrand; standard regularity
    (hφ : Measurable φ)
    -- LEAN-ONLY: integrability of the integrand; automatic for critical functions under a
    -- probability measure, but stated in the general form used by the disintegration
    (hint : Integrable (fun x => φ (U x, T x)) (P p)) :
    ∫ x, φ (U x, T x) ∂(P p)
      = ∫ t, (∫ u, φ (u, t) ∂(condDistrib U T (P p) t)) ∂((P p).map T) := by
  have hfm : Measurable (fun x => (T x, U x)) := hT.prodMk hU
  have hgm : Measurable (fun z : Ξ × ℝ => φ (z.2, z.1)) :=
    hφ.comp (measurable_snd.prodMk measurable_fst)
  -- disintegrate the joint law of `(T, U)` along `T`
  have hmap : (P p).map (fun x => (T x, U x)) = (P p).map T ⊗ₘ condDistrib U T (P p) :=
    (compProd_map_condDistrib hU.aemeasurable).symm
  have hint' : Integrable (fun z : Ξ × ℝ => φ (z.2, z.1))
      ((P p).map (fun x => (T x, U x))) := by
    rw [integrable_map_measure hgm.aestronglyMeasurable hfm.aemeasurable]; exact hint
  calc ∫ x, φ (U x, T x) ∂(P p)
      = ∫ z, φ (z.2, z.1) ∂((P p).map (fun x => (T x, U x))) :=
        (integral_map hfm.aemeasurable hgm.aestronglyMeasurable).symm
    _ = ∫ z, φ (z.2, z.1) ∂((P p).map T ⊗ₘ condDistrib U T (P p)) := by rw [hmap]
    _ = ∫ t, (∫ u, φ (u, t) ∂(condDistrib U T (P p) t)) ∂((P p).map T) :=
        Measure.integral_compProd (hmap ▸ hint')

end StatLean.HypothesisTesting
