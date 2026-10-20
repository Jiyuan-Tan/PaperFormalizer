module
public import StatLean.HypothesisTesting.ForMathlib.BerryEsseen

@[expose] public section

/-!
# The damped Edgeworth expansion in an inner product space

`ForMathlib/BerryEsseen.lean` proves the one-dimensional damped one-term Edgeworth expansion
`norm_charFun_pow_sub_edgeworth_le`: for a centred law `μ` on the line with second moment `v`,
third moment `m₃` and a finite fourth moment, and for `s` in the window `v s² ≤ 2`,
`ρ|s| ≤ 3v/2`,

`‖φ_μ(s)ⁿ − e^{−n v s²/2}(1 − n i m₃ s³/6)‖ ≤ e^{−(n−2) v s²/4}(…)`.

The studentized Edgeworth expansion of `Bootstrap/Edgeworth.lean` needs the same estimate for a
law on `ℝ²` — the joint law of `(X − μ, (X − μ)² − σ²)`, whose sample mean carries both the
numerator and the denominator of the studentized root. This file supplies it, and the point of
the file is that **no genuinely two-dimensional argument is required**: the characteristic
function of a measure on an inner product space, evaluated along a ray `s • t`, is the
characteristic function of the *one-dimensional projection* `⟪·, t⟫` evaluated at `s`
(`charFun_smul_eq_charFun_map_inner`). Every hypothesis and every conclusion of the
one-dimensional theorem therefore transfers verbatim, with the moments of `μ` replaced by the
moments of the projected law.

## Main definitions

* `vecRootLaw F Z n` — the law of `n^{-1/2} ∑_{i<n} Z(yᵢ)` under `n` independent draws from `F`,
  a measure on the inner product space `E`. For `E = ℝ` and `Z = id − E_F X` this is
  `Bootstrap/Edgeworth.lean`'s `meanRootLaw`.

## Main statements

* `charFun_smul_eq_charFun_map_inner` — the projection identity
  `φ_μ(s • t) = φ_{μ ∘ ⟪·,t⟫⁻¹}(s)`.
* `norm_charFun_smul_le_exp_neg_sq` — the Gaussian majorant on a window, in `E`.
* `norm_charFun_smul_pow_sub_edgeworth_le` — the damped one-term Edgeworth expansion in `E`.
* `charFun_vecRootLaw` — `φ_{vecRootLaw F Z n}(t) = φ_{F ∘ Z⁻¹}(n^{-1/2} • t)ⁿ`, the
  factorisation that lets the previous item be applied to a sample mean.
* `mixCharFun` — the **mixed** characteristic function `∫ ⟪w,b⟫ e^{i⟪w,t⟫} ∂μ`, together with
  its exact factorisation on a vector root (`mixCharFun_vecRootLaw`), the first-order Taylor
  bound on a single factor (`norm_mixCharFun_sub_mul_I_le`) and the resulting one-term expansion
  `‖mix_{ρ_n}(b,a) − iκ φ(n^{-1/2}a)^{n−1}‖ ≤ 3M/(2√n)`
  (`norm_mixCharFun_vecRootLaw_sub_le`). Up to a factor `i` this is the directional derivative
  of `charFun`; it is estimated directly because the studentized expansion needs an *inequality*
  for it and inequalities cannot be differentiated.
* `multiCharFun` — the **multilinear** extension `∫ (∏_{l<k} ⟪w, b l⟫) e^{i⟪w,t⟫} ∂μ`, with its
  exact factorisation on a vector root (`multiCharFun_vecRootLaw`):
  `multi_{ρ_n}(b,a) = n^{-k/2} ∑_{σ : Fin k → Fin n} ∏_{i<n} slot_{σ⁻¹(i)}(n^{-1/2} • a)`,
  a sum over the `nᵏ` assignments of weight slots to coordinates. `mixCharFun` is the case
  `k = 1` (where all `n` summands coincide and `n · n^{-1/2} = √n`) and `charFun` is `k = 0`.
  The third-order delta-method surrogate of the studentized route is a degree-four polynomial
  in the coordinates of the root, so its characteristic function is a finite combination of
  `multiCharFun`s with `k ≤ 4`, and is *not* reachable from the one-slot theory.
* `multiCharFun_vecRootLaw_two` — the `k = 2` assignment sum **in closed form**:
  `multi_{ρ_N}(b,a) = N^{-1}(N·slot_{{0,1}}(c)φ^{N−1} + N(N−1)·slot_{{0}}(c)slot_{{1}}(c)φ^{N−2})`.
  The point of stating it is that the off-diagonal block is **not** negligible: each single-slot
  factor is `O(N^{-1/2})` for a centred `Z`, so the block is `N^{-1}·N²·O(N⁻¹) = O(1)`, exactly
  the order of the diagonal. The `k = 1` intuition — where there is no off-diagonal at all — is
  therefore misleading, and the `k ≥ 2` estimate is a genuine analytic item rather than wiring.
* `norm_multiCharFun_vecRootLaw_two_sub_le` — the `k = 2` **estimate** itself, the analytic half
  the closed form leaves open:
  `‖multi_{ρ_N}(b,a) − (κ₀₁φ(c)^{N−1} − κ₀κ₁φ(c)^{N−2})‖ ≤ N^{-1/2}·multiTwoRemConst`,
  for a law centred in both slot directions, with `κ₀₁ = ∫⟪x,b₀⟫⟪x,b₁⟫` and
  `κ_j = ∫⟪x,b_j⟫⟪x,a⟫`. Its ingredients are `norm_integral_ofReal_mul_cexp_sub_le` for the
  diagonal slot (**no** centring: the diagonal has its `O(1)` limit already at zeroth order) and
  `norm_mixCharFun_sub_mul_I_le` for the two single slots (centring **essential**: without it
  the off-diagonal block, whose multiplicity is `N − 1`, diverges). The off-diagonal limit is
  `−κ₀κ₁`, of the same order as the diagonal and of opposite sign.
* `ae_norm_vecRootLaw_le` — a **bounded** summand gives a root with bounded support: `‖Z‖ ≤ K`
  pointwise implies `‖root‖ ≤ √n·K` pointwise, so every polynomial in the root's coordinates is
  integrable with no moment hypothesis on `F` at all. This is what truncation buys, and it is
  the moment half of the studentized route's truncated-law replacement.

## Proof formalization notes

* The projection identity is `charFun_apply` on both sides plus `real_inner_smul_right`; it is
  the whole content of "the multivariate expansion is the univariate one". Note that it is an
  identity between the value at `s • t` and a *one-dimensional* characteristic function, not a
  statement about `charFun μ` as a function on `E`: what is expanded is the restriction of
  `φ_μ` to each ray through the origin, uniformly in the direction.
* Consequently the moments appearing in the expansion are the **directional** moments
  `∫ ⟪x, t⟫^k ∂μ`. In the classical formulation these are the contractions of the cumulant
  tensors with `t`: `∫⟪x,t⟫² = ⟪Σ t, t⟫` is the covariance form and `∫⟪x,t⟫³` is the third
  cumulant tensor evaluated at `(t,t,t)`. Nothing is lost by carrying them as scalars.
* The window conditions `v s² ≤ 2`, `ρ|s| ≤ 3v/2` are direction-dependent through
  `v = v(t) = ⟪Σt,t⟫`. Turning them into a window *uniform in the direction* is where
  nondegeneracy of `Σ` enters: `v(t) ≥ λ_min ‖t‖²` is what converts a bound on `‖t‖` into the
  window conditions for every direction. That step is a hypothesis of the consumer, not of this
  file.
* `charFun_vecRootLaw` is proved exactly as `charFun_meanRootLaw` is in
  `Bootstrap/Edgeworth.lean`: the root map is a scalar multiple of a sum of one-variable
  functions of the coordinates, `Complex.exp_sum` turns the exponential of the sum into a
  product, and `MeasureTheory.integral_fintype_prod_eq_pow` is Fubini for such a product on
  `Measure.pi`. No transfer through the canonical i.i.d. construction is needed.

**Reference.** P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer, 1992, Chapter 2
(the "smooth function model": the statistic is a smooth function of a vector sample mean, and
the expansion is obtained from the multivariate expansion of that mean).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace

namespace StatLean.HypothesisTesting

/-! ## The projection identity

The characteristic function of a measure on an inner product space, restricted to the ray
`s ↦ s • t`, is the characteristic function of the pushforward under `x ↦ ⟪x, t⟫`. -/

section Projection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- The linear form `x ↦ ⟪x, t⟫` is measurable. -/
lemma measurable_inner_right (t : E) : Measurable fun x : E => ⟪x, t⟫ :=
  (continuous_id.inner continuous_const).measurable

/-- The **projected law** in the direction `t`: the pushforward of `μ` under `x ↦ ⟪x, t⟫`. -/
noncomputable def projLaw (μ : Measure E) (t : E) : Measure ℝ :=
  μ.map fun x : E => ⟪x, t⟫

instance isProbabilityMeasure_projLaw (μ : Measure E) [IsProbabilityMeasure μ] (t : E) :
    IsProbabilityMeasure (projLaw μ t) := by
  rw [projLaw]
  exact Measure.isProbabilityMeasure_map (measurable_inner_right t).aemeasurable

/-- Integrals against the projected law are directional integrals against `μ`. -/
lemma integral_projLaw (μ : Measure E) (t : E) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (projLaw μ t)) :
    ∫ y, f y ∂(projLaw μ t) = ∫ x, f ⟪x, t⟫ ∂μ :=
  integral_map (measurable_inner_right t).aemeasurable hf

/-- Integrability against the projected law is directional integrability against `μ`. -/
lemma integrable_projLaw_iff (μ : Measure E) (t : E) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (projLaw μ t)) :
    Integrable f (projLaw μ t) ↔ Integrable (fun x : E => f ⟪x, t⟫) μ :=
  integrable_map_measure hf (measurable_inner_right t).aemeasurable

/-- **The projection identity.** `φ_μ(s • t) = φ_{projLaw μ t}(s)`: along every ray through the
origin, the characteristic function of a measure on an inner product space is the
characteristic function of a measure on the line. -/
theorem charFun_smul_eq_charFun_map_inner (μ : Measure E) (t : E) (s : ℝ) :
    charFun μ (s • t) = charFun (projLaw μ t) s := by
  rw [charFun_apply_real, projLaw,
    integral_map (measurable_inner_right t).aemeasurable (by fun_prop), charFun_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [real_inner_smul_right]
  push_cast
  ring_nf

end Projection

/-! ## The expansion, transferred

Both estimates of `ForMathlib/BerryEsseen.lean` that the Edgeworth remainder consumes — the
Gaussian majorant on a window and the damped one-term expansion of the `n`-th power — hold in
an inner product space along every ray, with the moments replaced by the directional moments
`∫ ⟪x, t⟫^k ∂μ`. Both are corollaries of the projection identity. -/

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

/-- **Gaussian majorant for a characteristic function on a window, in an inner product space.**
On the window `v s² ≤ 2`, `ρ|s| ≤ 3v/2` built from the directional moments
`v = ∫⟪x,t⟫²`, `ρ = ∫|⟪x,t⟫|³` of a directionally centred law,
`‖φ_μ(s • t)‖ ≤ exp(−v s²/4)`.

This is the two-dimensional analogue of `norm_charFun_le_exp_neg_sq` that
`Bootstrap/Edgeworth.lean` records as missing; it needs no two-dimensional argument. -/
theorem norm_charFun_smul_le_exp_neg_sq (μ : Measure E) [IsProbabilityMeasure μ]
    {t : E} {v : ℝ}
    (hint1 : Integrable (fun x : E => ⟪x, t⟫) μ)
    (hint2 : Integrable (fun x : E => ⟪x, t⟫ ^ 2) μ)
    (hint3 : Integrable (fun x : E => |⟪x, t⟫| ^ 3) μ)
    (hmean : ∫ x, ⟪x, t⟫ ∂μ = 0) (hvar : ∫ x, ⟪x, t⟫ ^ 2 ∂μ = v)
    {s : ℝ} (hs2 : v * s ^ 2 ≤ 2)
    (hs3 : (∫ x, |⟪x, t⟫| ^ 3 ∂μ) * |s| ≤ 3 * v / 2) :
    ‖charFun μ (s • t)‖ ≤ Real.exp (-(v * s ^ 2 / 4)) := by
  have e1 : ∫ y : ℝ, y ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ∂μ := integral_projLaw μ t (by fun_prop)
  have e2 : ∫ y : ℝ, y ^ 2 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 2 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e3 : ∫ y : ℝ, |y| ^ 3 ∂(projLaw μ t) = ∫ x, |⟪x, t⟫| ^ 3 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  rw [charFun_smul_eq_charFun_map_inner]
  exact norm_charFun_le_exp_neg_sq _ ((integrable_projLaw_iff μ t (by fun_prop)).2 hint1)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint2)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint3) (by rw [e1, hmean]) (by rw [e2, hvar])
    hs2 (by rw [e3]; exact hs3)

/-- **Damped one-term Edgeworth expansion in an inner product space.**

For a law `μ` on `E` which is centred in the direction `t`, with directional second moment `v`,
directional third moment `m₃` and a finite directional fourth moment, and for `s` in the window
`v s² ≤ 2`, `ρ|s| ≤ 3v/2`,

`‖φ_μ(s • t)ⁿ − e^{−n v s²/2}(1 − n i m₃ s³/6)‖ ≤ e^{−(n−2) v s²/4}(…)`,

with the same right-hand side as `norm_charFun_pow_sub_edgeworth_le`, written with `n = m + 2`.

**This is step 1 of the studentized route of `Bootstrap/Edgeworth.lean`.** For the pair
`Z = (X − μ, (X − μ)² − σ²)` it is the bivariate expansion recorded there as missing, and the
directional moments are the contractions of the cumulant tensors of `Z` with `t`. -/
theorem norm_charFun_smul_pow_sub_edgeworth_le (μ : Measure E) [IsProbabilityMeasure μ]
    {t : E} {v m₃ : ℝ}
    (hint1 : Integrable (fun x : E => ⟪x, t⟫) μ)
    (hint2 : Integrable (fun x : E => ⟪x, t⟫ ^ 2) μ)
    (hint3 : Integrable (fun x : E => |⟪x, t⟫| ^ 3) μ)
    (hint4 : Integrable (fun x : E => ⟪x, t⟫ ^ 4) μ)
    (hmean : ∫ x, ⟪x, t⟫ ∂μ = 0) (hvar : ∫ x, ⟪x, t⟫ ^ 2 ∂μ = v)
    (hthird : ∫ x, ⟪x, t⟫ ^ 3 ∂μ = m₃)
    {s : ℝ} (hs2 : v * s ^ 2 ≤ 2)
    (hs3 : (∫ x, |⟪x, t⟫| ^ 3 ∂μ) * |s| ≤ 3 * v / 2) (m : ℕ) :
    ‖charFun μ (s • t) ^ (m + 2)
        - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
            * (1 - ((m : ℂ) + 2) * Complex.I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6)‖
      ≤ Real.exp (-(v * s ^ 2 / 4)) ^ m *
          (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2
              * ((∫ x, |⟪x, t⟫| ^ 3 ∂μ) * |s| ^ 3 / 6 + (v * s ^ 2 / 2) ^ 2 / 2) ^ 2
            + ((m : ℝ) + 2) * ((v * s ^ 2 / 2) * (|m₃| * |s| ^ 3 / 6)
              + ((∫ x, ⟪x, t⟫ ^ 4 ∂μ) * |s| ^ 4 / 24 + (v * s ^ 2 / 2) ^ 2 / 2))) := by
  have e1 : ∫ y : ℝ, y ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ∂μ := integral_projLaw μ t (by fun_prop)
  have e2 : ∫ y : ℝ, y ^ 2 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 2 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e3 : ∫ y : ℝ, |y| ^ 3 ∂(projLaw μ t) = ∫ x, |⟪x, t⟫| ^ 3 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e3' : ∫ y : ℝ, y ^ 3 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 3 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  have e4 : ∫ y : ℝ, y ^ 4 ∂(projLaw μ t) = ∫ x, ⟪x, t⟫ ^ 4 ∂μ :=
    integral_projLaw μ t (by fun_prop)
  rw [charFun_smul_eq_charFun_map_inner, ← e3, ← e4]
  exact norm_charFun_pow_sub_edgeworth_le _ ((integrable_projLaw_iff μ t (by fun_prop)).2 hint1)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint2)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint3)
    ((integrable_projLaw_iff μ t (by fun_prop)).2 hint4) (by rw [e1, hmean]) (by rw [e2, hvar])
    (by rw [e3', hthird]) hs2 (by rw [e3]; exact hs3) m

end Expansion

/-! ## The law of a vector root

The expansion above estimates an `n`-th power of a characteristic function; what a statistic
supplies is the law of a normalised sum. `vecRootLaw` is that law, and `charFun_vecRootLaw` is
the factorisation, proved directly on `Measure.pi` exactly as `charFun_meanRootLaw` is. -/

section VecRoot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The root map `y ↦ n^{-1/2} ∑ᵢ Z(yᵢ)` is measurable. -/
lemma measurable_vecRoot {Z : ℝ → E} (hZ : Measurable Z) (n : ℕ) :
    Measurable fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ • ∑ i, Z (y i) :=
  (continuous_const_smul ((Real.sqrt n)⁻¹ : ℝ)).measurable.comp
    (Finset.measurable_sum _ fun i _ => hZ.comp (measurable_pi_apply i))

/-- The **law of the vector root** `n^{-1/2} ∑_{i<n} Z(yᵢ)` under `n` independent draws from
`F`. For `E = ℝ` and `Z = (· − E_F X)` this is `Bootstrap/Edgeworth.lean`'s `meanRootLaw`. -/
noncomputable def vecRootLaw (F : Measure ℝ) (Z : ℝ → E) (n : ℕ) : Measure E :=
  (Measure.pi fun _ : Fin n => F).map fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ • ∑ i, Z (y i)

theorem isProbabilityMeasure_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) (n : ℕ) : IsProbabilityMeasure (vecRootLaw F Z n) := by
  rw [vecRootLaw]
  exact Measure.isProbabilityMeasure_map (measurable_vecRoot hZ n).aemeasurable

/-- **The characteristic function of a vector root, as an `n`-th power.**
`φ_{vecRootLaw F Z n}(t) = φ_{F ∘ Z⁻¹}(n^{-1/2} • t)ⁿ`.

Together with `norm_charFun_smul_pow_sub_edgeworth_le` — whose left-hand side is an `n`-th
power of `φ` *along a ray* — this is the whole characteristic-function half of a multivariate
one-term Edgeworth expansion. -/
theorem charFun_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) (n : ℕ) (t : E) :
    charFun (vecRootLaw F Z n) t = charFun (F.map Z) ((Real.sqrt n)⁻¹ • t) ^ n := by
  set c : E := (Real.sqrt n)⁻¹ • t with hc
  have hmeasg : Measurable fun y : Fin n → ℝ => (Real.sqrt n)⁻¹ • ∑ i, Z (y i) :=
    measurable_vecRoot hZ n
  have hstep1 : charFun (vecRootLaw F Z n) t
      = ∫ y : Fin n → ℝ, ∏ i : Fin n, Complex.exp ((⟪Z (y i), c⟫ : ℝ) * Complex.I)
        ∂(Measure.pi fun _ : Fin n => F) := by
    rw [charFun_apply, vecRootLaw, integral_map hmeasg.aemeasurable (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have harg : (⟪(Real.sqrt n)⁻¹ • ∑ i, Z (y i), t⟫ : ℝ) = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) :=
      calc (⟪(Real.sqrt n)⁻¹ • ∑ i, Z (y i), t⟫ : ℝ)
          = (Real.sqrt n)⁻¹ * ⟪∑ i, Z (y i), t⟫ := real_inner_smul_left _ _ _
        _ = (Real.sqrt n)⁻¹ * ∑ i : Fin n, (⟪Z (y i), t⟫ : ℝ) := by rw [sum_inner]
        _ = ∑ i : Fin n, (Real.sqrt n)⁻¹ * (⟪Z (y i), t⟫ : ℝ) := Finset.mul_sum _ _ _
        _ = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) := by
            simp only [hc, real_inner_smul_right]
    simp only [harg]
    rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  have hstep2 : (∫ y : Fin n → ℝ, ∏ i : Fin n, Complex.exp ((⟪Z (y i), c⟫ : ℝ) * Complex.I)
        ∂(Measure.pi fun _ : Fin n => F))
      = (∫ x : ℝ, Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) ∂F) ^ n := by
    have h := MeasureTheory.integral_fintype_prod_eq_pow (ι := Fin n) (μ := F)
      (fun x : ℝ => Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I))
    simpa using h
  have hstep3 : (∫ x : ℝ, Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) ∂F)
      = charFun (F.map Z) c := by
    rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
  rw [hstep1, hstep2, hstep3]

/-- **The one-term Edgeworth expansion of a vector root, at the level of characteristic
functions.** For a directionally centred `Z` with directional second moment `v`, third moment
`m₃` and finite fourth moment, and for `t` in the direction-dependent window,

`‖φ_{vecRootLaw F Z n}(t) − e^{−v/2}(1 − i m₃ n^{-1/2}/6)‖ ≤ (the damped remainder)`,

written with `n = m + 2`. The Gaussian factor and the `n^{-1/2}` correction are exactly the
Fourier transform of the multivariate Edgeworth signed density in the direction `t`.

**This is the bivariate expansion that `Bootstrap/Edgeworth.lean` records as the sole missing
ingredient of the studentized expansion**, specialised to `E = ℝ²` and
`Z = studentPair F = (X − μ, (X − μ)² − σ²)`. It is the composition of `charFun_vecRootLaw`
with `norm_charFun_smul_pow_sub_edgeworth_le`; the scaling `n s² = 1` at `s = n^{-1/2}` turns
`e^{−n v s²/2}` into `e^{−v/2}` and `n s³` into `s`. -/
theorem norm_charFun_vecRootLaw_sub_edgeworth_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {t : E} {v m₃ : ℝ} (m : ℕ)
    (hint1 : Integrable (fun x : E => ⟪x, t⟫) (F.map Z))
    (hint2 : Integrable (fun x : E => ⟪x, t⟫ ^ 2) (F.map Z))
    (hint3 : Integrable (fun x : E => |⟪x, t⟫| ^ 3) (F.map Z))
    (hint4 : Integrable (fun x : E => ⟪x, t⟫ ^ 4) (F.map Z))
    (hmean : ∫ x, ⟪x, t⟫ ∂(F.map Z) = 0) (hvar : ∫ x, ⟪x, t⟫ ^ 2 ∂(F.map Z) = v)
    (hthird : ∫ x, ⟪x, t⟫ ^ 3 ∂(F.map Z) = m₃)
    (hs2 : v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 ≤ 2)
    (hs3 : (∫ x, |⟪x, t⟫| ^ 3 ∂(F.map Z)) * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹|
      ≤ 3 * v / 2) :
    ‖charFun (vecRootLaw F Z (m + 2)) t
        - ((Real.exp (-(v / 2)) : ℝ) : ℂ)
            * (1 - Complex.I * (m₃ : ℂ) * (((Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) / 6)‖
      ≤ Real.exp (-(v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 4)) ^ m *
          (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2
              * ((∫ x, |⟪x, t⟫| ^ 3 ∂(F.map Z))
                  * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹| ^ 3 / 6
                + (v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 2) ^ 2 / 2) ^ 2
            + ((m : ℝ) + 2)
              * ((v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 2)
                  * (|m₃| * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹| ^ 3 / 6)
                + ((∫ x, ⟪x, t⟫ ^ 4 ∂(F.map Z))
                    * |(Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹| ^ 4 / 24
                  + (v * (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ ^ 2 / 2) ^ 2 / 2))) := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  set s : ℝ := (Real.sqrt ((m + 2 : ℕ) : ℝ))⁻¹ with hs
  have hne : ((m : ℝ) + 2) ≠ 0 := by positivity
  have hN : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by push_cast; positivity
  have hsq : s ^ 2 = (((m + 2 : ℕ) : ℝ))⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hN.le]
  have h2 : ((m : ℝ) + 2) * s ^ 2 = 1 := by
    rw [hsq]; push_cast; field_simp
  have hgauss : ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
      = ((Real.exp (-(v / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul, Complex.ofReal_inj]
    congr 1
    push_cast
    linear_combination (-(v / 2)) * h2
  have hreal : ((m : ℝ) + 2) * s ^ 3 = s := by
    calc ((m : ℝ) + 2) * s ^ 3 = (((m : ℝ) + 2) * s ^ 2) * s := by ring
      _ = s := by rw [h2, one_mul]
  have hcorr : ((m : ℂ) + 2) * Complex.I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6
      = Complex.I * (m₃ : ℂ) * (s : ℂ) / 6 := by
    have hc : ((m : ℂ) + 2) * (s : ℂ) ^ 3 = (s : ℂ) := by exact_mod_cast hreal
    calc ((m : ℂ) + 2) * Complex.I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6
        = Complex.I * (m₃ : ℂ) * (((m : ℂ) + 2) * (s : ℂ) ^ 3) / 6 := by ring
      _ = Complex.I * (m₃ : ℂ) * (s : ℂ) / 6 := by rw [hc]
  rw [charFun_vecRootLaw F hZ, ← hs, ← hgauss, ← hcorr]
  exact norm_charFun_smul_pow_sub_edgeworth_le (F.map Z) hint1 hint2 hint3 hint4 hmean hvar
    hthird hs2 hs3 m

end VecRoot

/-! ## The mixed characteristic function

The studentized route of `Bootstrap/Edgeworth.lean` needs, besides the expansion of
`ψ_n(θ, s) = φ_{ρ_n}(θ e₁/σ + s e₂/σ²)` supplied by
`norm_charFun_vecRootLaw_sub_edgeworth_le`, an expansion of the *`s`-derivative* of `ψ_n` at
`s = 0`. Differentiating an inequality is not legitimate, so that estimate cannot be read off
from the expansion; it is proved here from scratch, for the quantity the derivative is:

`mixCharFun μ b t = ∫ ⟪w, b⟫ e^{i⟪w,t⟫} ∂μ`,

the character in the direction `t` weighted by the coordinate in the direction `b`.

The point of this section is that the mixed quantity is *easier* than the expansion, not
harder. Its value on a vector root factorises **exactly** — one distinguished coordinate
carrying the weight `⟪·, b⟫`, the remaining `n − 1` carrying only the character
(`mixCharFun_vecRootLaw`) — and a first-order Taylor bound on the single distinguished factor
(`norm_mixCharFun_sub_mul_I_le`) then gives the whole estimate, with the covariance
`κ = ∫ ⟪x, b⟫⟪x, a⟫` as the limit and an `O(n^{-1/2})` remainder
(`norm_mixCharFun_vecRootLaw_sub_le`). No smoothing, no window and no Cramér condition enter:
the factorisation is an identity and the Taylor bound is pointwise. -/

section Mixed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The **mixed characteristic function** `∫ ⟪w, b⟫ e^{i⟪w,t⟫} ∂μ`.

Up to the factor `i` this is the derivative of `charFun μ` at `t` in the direction `b`
(Mathlib's `iteratedFDeriv_charFun` at `n = 1` computes exactly this integral), but it is
defined and estimated directly: what the studentized expansion needs is an *inequality* for it,
uniform in `t`, and inequalities cannot be differentiated. -/
noncomputable def mixCharFun (μ : Measure E) (b t : E) : ℂ :=
  ∫ w, ((⟪w, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) ∂μ

/-- The mixed characteristic function of a pushforward is a directional integral. -/
lemma mixCharFun_map (F : Measure ℝ) {Z : ℝ → E} (hZ : Measurable Z) (b t : E) :
    mixCharFun (F.map Z) b t
      = ∫ x, ((⟪Z x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪Z x, t⟫ : ℝ) * Complex.I) ∂F := by
  rw [mixCharFun, integral_map hZ.aemeasurable (by fun_prop)]

/-- **The mixed characteristic function of a vector root factorises exactly.**

`∫ ⟪w, b⟫ e^{i⟪w,a⟫} ∂(vecRootLaw F Z n) = √n · (∫ ⟪Z x, b⟫ e^{i⟪Z x, c⟫} ∂F) · φ(c)^{n−1}`,
with `c = n^{-1/2} • a`.

This is the analogue of `charFun_vecRootLaw` for the weighted character, and it is the reason
(M1)(b) is tractable: the weight `⟪·, b⟫` of the root is `n^{-1/2} ∑ᵢ ⟪Z(yᵢ), b⟫`, a *sum*, so
the integrand splits into `n` products over the coordinates, each with exactly one
distinguished factor. Fubini on `Measure.pi` (`integral_fintype_prod_eq_prod`) evaluates each,
and the `n` summands are equal; the surviving `n · n^{-1/2} = √n` is the whole reason the
mixed quantity is of size `n^{-1/2}` larger than a plain characteristic function before the
centring of `⟪·, b⟫` is used. -/
theorem mixCharFun_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {b : E} (hb : Integrable (fun x : ℝ => (⟪Z x, b⟫ : ℝ)) F)
    (m : ℕ) (a : E) :
    mixCharFun (vecRootLaw F Z (m + 1)) b a
      = (Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ)
          * mixCharFun (F.map Z) b ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a)
          * charFun (F.map Z) ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a) ^ m := by
  classical
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hNpos
  set r : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  have hZb : Measurable fun x : ℝ => (⟪Z x, b⟫ : ℝ) := (measurable_inner_right b).comp hZ
  have hZc : Measurable fun x : ℝ => (⟪Z x, c⟫ : ℝ) := (measurable_inner_right c).comp hZ
  set g : ℝ → ℂ := fun x => Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) with hgdef
  set f : ℝ → ℂ := fun x => ((⟪Z x, b⟫ : ℝ) : ℂ) * g x with hfdef
  have hgnorm : ∀ x, ‖g x‖ = 1 := by
    intro x
    rw [hgdef]
    simp [Complex.norm_exp]
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hfm : Measurable f := by rw [hfdef]; fun_prop
  -- the `i`-th summand of the weight, written as a product over the coordinates
  set h : Fin (m + 1) → Fin (m + 1) → ℝ → ℂ :=
    fun i j x => if j = i then f x else g x with hhdef
  have hprod : ∀ (i : Fin (m + 1)) (y : Fin (m + 1) → ℝ),
      ∏ j, h i j (y j) = ((⟪Z (y i), b⟫ : ℝ) : ℂ) * ∏ j, g (y j) := by
    intro i y
    have hfac : ∀ j : Fin (m + 1),
        h i j (y j) = (if j = i then ((⟪Z (y j), b⟫ : ℝ) : ℂ) else 1) * g (y j) := by
      intro j
      by_cases hji : j = i
      · simp [hhdef, hfdef, hji]
      · simp [hhdef, hji]
    simp_rw [hfac]
    rw [Finset.prod_mul_distrib,
      Finset.prod_ite_eq' Finset.univ i (fun j => ((⟪Z (y j), b⟫ : ℝ) : ℂ))]
    simp
  -- each summand is integrable on the product measure: its modulus is `|⟪Z(yᵢ), b⟫|`
  have hint : ∀ i : Fin (m + 1),
      Integrable (fun y : Fin (m + 1) → ℝ => ∏ j, h i j (y j))
        (Measure.pi fun _ : Fin (m + 1) => F) := by
    intro i
    have hdom : Integrable (fun y : Fin (m + 1) → ℝ => |(⟪Z (y i), b⟫ : ℝ)|)
        (Measure.pi fun _ : Fin (m + 1) => F) := by
      have := (measurePreserving_eval (μ := fun _ : Fin (m + 1) => F)
        i).integrable_comp_of_integrable hb.abs
      simpa [Function.comp] using! this
    have hmeas : ∀ j : Fin (m + 1),
        Measurable fun y : Fin (m + 1) → ℝ => h i j (y j) := by
      intro j
      rcases eq_or_ne j i with rfl | hji
      · simpa [hhdef] using! hfm.comp (measurable_pi_apply j)
      · simpa [hhdef, hji] using! hgm.comp (measurable_pi_apply j)
    refine Integrable.mono' hdom
      ((Finset.measurable_prod _ fun j _ => hmeas j).aestronglyMeasurable) ?_
    filter_upwards with y
    rw [hprod i y, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hone : ‖∏ j, g (y j)‖ = 1 := by
      rw [norm_prod]
      simp [hgnorm]
    rw [hone, mul_one]
  -- step 1: rewrite the mixed integral over the root law as an integral over the product
  have hstep1 : mixCharFun (vecRootLaw F Z (m + 1)) b a
      = ∫ y : Fin (m + 1) → ℝ, ((r : ℂ) * ∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F) := by
    rw [mixCharFun, vecRootLaw,
      integral_map (measurable_vecRoot hZ (m + 1)).aemeasurable (by fun_prop)]
    simp only [← hrdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hbi : (⟪r • ∑ i, Z (y i), b⟫ : ℝ) = r * ∑ i : Fin (m + 1), (⟪Z (y i), b⟫ : ℝ) := by
      rw [real_inner_smul_left, sum_inner]
    have hai : (⟪r • ∑ i, Z (y i), a⟫ : ℝ) = ∑ i : Fin (m + 1), (⟪Z (y i), c⟫ : ℝ) := by
      calc (⟪r • ∑ i, Z (y i), a⟫ : ℝ)
          = r * ⟪∑ i, Z (y i), a⟫ := real_inner_smul_left _ _ _
        _ = r * ∑ i : Fin (m + 1), (⟪Z (y i), a⟫ : ℝ) := by rw [sum_inner]
        _ = ∑ i : Fin (m + 1), r * (⟪Z (y i), a⟫ : ℝ) := Finset.mul_sum _ _ _
        _ = ∑ i : Fin (m + 1), (⟪Z (y i), c⟫ : ℝ) := by
            simp only [hcdef, real_inner_smul_right]
    simp only []
    rw [hbi, hai]
    have hexp : Complex.exp (((∑ i : Fin (m + 1), (⟪Z (y i), c⟫ : ℝ)) : ℝ) * Complex.I)
        = ∏ j, g (y j) := by
      rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    rw [hexp]
    simp_rw [hprod]
    rw [← Finset.sum_mul]
    push_cast
    ring
  rw [hstep1]
  -- step 2: pull out the constant and swap the (finite) sum with the integral
  have hstep2 : ∫ y : Fin (m + 1) → ℝ, ((r : ℂ) * ∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F)
      = (r : ℂ) * ∫ y : Fin (m + 1) → ℝ, (∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F) := integral_const_mul _ _
  have hstep3 : ∫ y : Fin (m + 1) → ℝ, (∑ i, ∏ j, h i j (y j))
        ∂(Measure.pi fun _ : Fin (m + 1) => F)
      = ∑ i, ∫ y : Fin (m + 1) → ℝ, ∏ j, h i j (y j)
        ∂(Measure.pi fun _ : Fin (m + 1) => F) :=
    integral_finset_sum _ fun i _ => hint i
  -- step 3: Fubini on each summand, and the `n − 1` undistinguished factors give a power
  have hA : ∫ x, f x ∂F = mixCharFun (F.map Z) b c := by
    rw [mixCharFun_map F hZ]
  have hB : ∫ x, g x ∂F = charFun (F.map Z) c := by
    rw [charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
  have hterm : ∀ i : Fin (m + 1),
      ∫ y : Fin (m + 1) → ℝ, ∏ j, h i j (y j) ∂(Measure.pi fun _ : Fin (m + 1) => F)
        = mixCharFun (F.map Z) b c * charFun (F.map Z) c ^ m := by
    intro i
    have hfub : ∫ y : Fin (m + 1) → ℝ, ∏ j, h i j (y j)
          ∂(Measure.pi fun _ : Fin (m + 1) => F)
        = ∏ j, ∫ x, h i j x ∂F :=
      MeasureTheory.integral_fintype_prod_eq_prod (fun j : Fin (m + 1) => h i j)
    rw [hfub]
    have hval : ∀ j : Fin (m + 1),
        (∫ x, h i j x ∂F) = if j = i then mixCharFun (F.map Z) b c else charFun (F.map Z) c := by
      intro j
      by_cases hji : j = i
      · simp only [hhdef, hji, if_pos rfl]
        exact hA
      · simp only [hhdef, if_neg hji]
        exact hB
    simp_rw [hval]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    rw [Finset.prod_congr rfl (fun j hj => if_neg (Finset.ne_of_mem_erase hj)),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [hstep2, hstep3]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hrm : (r : ℝ) * ((m + 1 : ℕ) : ℝ) = Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    rw [hrdef, inv_mul_eq_div]
    exact Real.div_sqrt
  have hrmC : (r : ℂ) * ((m + 1 : ℕ) : ℂ) = ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) hrm
  calc (r : ℂ) * (((m + 1 : ℕ) : ℂ) * (mixCharFun (F.map Z) b c * charFun (F.map Z) c ^ m))
      = ((r : ℂ) * ((m + 1 : ℕ) : ℂ))
          * (mixCharFun (F.map Z) b c * charFun (F.map Z) c ^ m) := by ring
    _ = (Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ) * mixCharFun (F.map Z) b c
          * charFun (F.map Z) c ^ m := by rw [hrmC]; ring

/-- **First-order Taylor bound for the mixed characteristic function.**

For a law `μ` that is centred in the direction `b`,

`‖∫ ⟪x,b⟫ e^{i⟪x,t⟫} ∂μ − i ∫ ⟪x,b⟫⟪x,t⟫ ∂μ‖ ≤ (3/2) ∫ |⟪x,b⟫| ⟪x,t⟫² ∂μ`.

The centring kills the constant term of `e^{i⟪x,t⟫} = 1 + i⟪x,t⟫ + O(⟪x,t⟫²)` and what survives
at first order is the *covariance* of the two directions. The remainder costs one moment more
than the plain characteristic function would (`|⟪x,b⟫|⟪x,t⟫²` rather than `⟪x,t⟫²`) — this is
the "one extra moment of the summands under the integral" that the studentized route pays. -/
theorem norm_mixCharFun_sub_mul_I_le (μ : Measure E) [IsProbabilityMeasure μ] {b t : E}
    (hb : Integrable (fun x : E => (⟪x, b⟫ : ℝ)) μ)
    (hbt : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ)) μ)
    (hbt2 : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2) μ)
    (hmean : ∫ x, (⟪x, b⟫ : ℝ) ∂μ = 0) :
    ‖mixCharFun μ b t - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ)‖
      ≤ 3 / 2 * ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2 ∂μ := by
  have hbm : Measurable fun x : E => (⟪x, b⟫ : ℝ) := measurable_inner_right b
  have htm : Measurable fun x : E => (⟪x, t⟫ : ℝ) := measurable_inner_right t
  -- the three integrable pieces of the expansion of the integrand
  have hA : Integrable
      (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ := by
    refine Integrable.mono' hb.norm (by fun_prop) ?_
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp
  have hB : Integrable (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ)) μ := hb.ofReal
  have hCeq : (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)))
      = fun x : E => Complex.I * (((⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) : ℝ) : ℂ) := by
    funext x
    push_cast
    ring
  have hC : Integrable
      (fun x : E => ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))) μ := by
    rw [hCeq]
    exact hbt.ofReal.const_mul Complex.I
  -- the exact identity: the difference is the integral of the second-order remainder
  have hkey : ∫ x, ((⟪x, b⟫ : ℝ) : ℂ)
        * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
      = mixCharFun μ b t - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ) := by
    have hexp : ∀ x : E, ((⟪x, b⟫ : ℝ) : ℂ)
          * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))
        = ((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)
          - ((⟪x, b⟫ : ℝ) : ℂ)
          - ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) := fun x => by ring
    have hIB : ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) ∂μ = 0 := by
      rw [integral_complex_ofReal, hmean, Complex.ofReal_zero]
    have hIC : ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
        = Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ) := by
      have h1 : ∫ x, Complex.I * (((⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) : ℝ) : ℂ) ∂μ
          = Complex.I * ∫ x, (((⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) : ℝ) : ℂ) ∂μ :=
        integral_const_mul _ _
      rw [hCeq, h1, integral_complex_ofReal]
    calc ∫ x, ((⟪x, b⟫ : ℝ) : ℂ)
            * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
              - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
        = ∫ x, (((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)
              - ((⟪x, b⟫ : ℝ) : ℂ)
              - ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hexp)
      _ = (∫ x, (((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)
              - ((⟪x, b⟫ : ℝ) : ℂ)) ∂μ)
            - ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ :=
          integral_sub (hA.sub hB) hC
      _ = ((∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ)
            - ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) ∂μ)
            - ∫ x, ((⟪x, b⟫ : ℝ) : ℂ) * (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ := by
          rw [integral_sub hA hB]
      _ = mixCharFun μ b t - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, t⟫ : ℝ) ∂μ : ℝ) : ℂ) := by
          rw [hIB, hIC, mixCharFun, sub_zero]
  rw [← hkey]
  have hdom : Integrable (fun x : E => 3 / 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2)) μ :=
    hbt2.const_mul (3 / 2)
  have hpt : ∀ x : E, ‖((⟪x, b⟫ : ℝ) : ℂ)
        * (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ))‖
      ≤ 3 / 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2) := by
    intro x
    have hcomm : Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)
        = Complex.exp (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) - 1
          - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) := by
      rw [mul_comm ((⟪x, t⟫ : ℝ) : ℂ) Complex.I]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hcomm]
    calc |(⟪x, b⟫ : ℝ)| * ‖Complex.exp (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) - 1
            - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)‖
        ≤ |(⟪x, b⟫ : ℝ)| * (3 * (⟪x, t⟫ : ℝ) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (norm_cexp_sub_one_sub_mul_I_le _) (abs_nonneg _)
      _ = 3 / 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, t⟫ : ℝ) ^ 2) := by ring
  refine (norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpt)).trans ?_
  exact le_of_eq (integral_const_mul _ _)

/-- **(M1)(b), assembled: the one-term expansion of the mixed characteristic function of a
vector root.**

`‖∫ ⟪w,b⟫ e^{i⟪w,a⟫} ∂ρ_n − i κ φ(n^{-1/2} a)^{n−1}‖ ≤ 3 M /(2√n)`, with
`κ = ∫ ⟪x,b⟫⟪x,a⟫` the covariance of the two directions and
`M = ∫ |⟪x,b⟫|⟪x,a⟫²` the mixed third moment, for a law centred in the direction `b`.

This is the estimate the studentized route of `Bootstrap/Edgeworth.lean` records as (M1)(b) —
the expansion of `∂_s ψ_n(θ, s)|_{s=0}`, equivalently of `E[V e^{iθU}]`, which cannot be
obtained by differentiating the inequality of `norm_charFun_vecRootLaw_sub_edgeworth_le`.

Two features are worth recording. First, the leading term is *not* damped by the extra `n^{-1/2}`
that the naive count suggests: the `√n` produced by the factorisation cancels exactly against
the `n^{-1/2}` of the covariance in the rescaled direction, so the mixed quantity has a
nonvanishing limit `i κ e^{−v/2}`, which is precisely the source of the studentized
`n^{-1/2}` coefficient `(1/6)γ(2t² + 1)` and of its difference from the centred one. Second,
what remains between this statement and the Gaussian limit is only the replacement of
`φ(n^{-1/2} a)^{n−1}` by `e^{−v/2}`, i.e. a Berry–Esseen-level estimate for an `(n−1)`-st power
at the argument `n^{-1/2}` — a mismatch of one factor with
`norm_charFun_smul_pow_sub_edgeworth_le`, not a new analytic difficulty. -/
theorem norm_mixCharFun_vecRootLaw_sub_le (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {a b : E} (m : ℕ)
    (hb : Integrable (fun x : E => (⟪x, b⟫ : ℝ)) (F.map Z))
    (hba : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hba2 : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hmean : ∫ x, (⟪x, b⟫ : ℝ) ∂(F.map Z) = 0) :
    ‖mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) : ℝ) : ℂ)
            * charFun (F.map Z) ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a) ^ m‖
      ≤ 3 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))
          * ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsq : (0 : ℝ) < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 hNpos
  set r : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  set κ : ℝ := ∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκdef
  set M : ℝ := ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) with hMdef
  have hc1 : ∀ x : E, (⟪x, c⟫ : ℝ) = r * (⟪x, a⟫ : ℝ) := fun x => by
    rw [hcdef, real_inner_smul_right]
  -- the two directional moments in the rescaled direction `c`
  have hκc : ∫ x, (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ) ∂(F.map Z) = r * κ := by
    have h1 : ∀ x : E, (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ)
        = r * ((⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := fun x => by rw [hc1 x]; ring
    simp_rw [h1]
    rw [hκdef]
    exact integral_const_mul _ _
  have hMc : ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2 ∂(F.map Z) = r ^ 2 * M := by
    have h1 : ∀ x : E, |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2
        = r ^ 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := fun x => by rw [hc1 x]; ring
    simp_rw [h1]
    rw [hMdef]
    exact integral_const_mul _ _
  have hbtc : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ)) (F.map Z) := by
    have h1 : (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, c⟫ : ℝ))
        = fun x : E => r * ((⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := by
      funext x; rw [hc1 x]; ring
    rw [h1]
    exact hba.const_mul r
  have hbt2c : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2) (F.map Z) := by
    have h1 : (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2)
        = fun x : E => r ^ 2 * (|(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := by
      funext x; rw [hc1 x]; ring
    rw [h1]
    exact hba2.const_mul (r ^ 2)
  -- the single-factor estimate, in the rescaled direction
  have hone : ‖mixCharFun (F.map Z) b c - Complex.I * ((r * κ : ℝ) : ℂ)‖
      ≤ 3 / 2 * (r ^ 2 * M) := by
    have h := norm_mixCharFun_sub_mul_I_le (F.map Z) hb hbtc hbt2c hmean
    rwa [hκc, hMc] at h
  -- the factorisation, and the cancellation `√n · n^{-1/2} = 1`
  have hbZ : Integrable (fun x : ℝ => (⟪Z x, b⟫ : ℝ)) F :=
    (integrable_map_measure hb.aestronglyMeasurable hZ.aemeasurable).1 hb
  have hfac := mixCharFun_vecRootLaw F hZ hbZ m a
  rw [← hrdef, ← hcdef] at hfac
  have hsr : (Real.sqrt ((m + 1 : ℕ) : ℝ)) * r = 1 := by
    rw [hrdef]; field_simp
  have hsrC : ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ) = 1 := by
    exact_mod_cast congrArg (fun z : ℝ => (z : ℂ)) hsr
  have halg : mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * (κ : ℂ) * charFun (F.map Z) c ^ m
      = ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)
          * (mixCharFun (F.map Z) b c - Complex.I * ((r * κ : ℝ) : ℂ))
          * charFun (F.map Z) c ^ m := by
    rw [hfac]
    have hexp : ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * (Complex.I * ((r * κ : ℝ) : ℂ))
        = Complex.I * (κ : ℂ) := by
      rw [Complex.ofReal_mul]
      calc ((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)
            * (Complex.I * (((r : ℝ) : ℂ) * ((κ : ℝ) : ℂ)))
          = (((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) * ((r : ℝ) : ℂ))
              * (Complex.I * ((κ : ℝ) : ℂ)) := by ring
        _ = Complex.I * (κ : ℂ) := by rw [hsrC, one_mul]
    rw [mul_sub, hexp]
    ring
  rw [halg, norm_mul, norm_mul]
  have hBle : ‖charFun (F.map Z) c ^ m‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one c)
  have hM0 : (0 : ℝ) ≤ M := integral_nonneg fun x => by positivity
  have hnormsq : ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖ = Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsq.le]
  calc ‖((Real.sqrt ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ)‖
        * ‖mixCharFun (F.map Z) b c - Complex.I * ((r * κ : ℝ) : ℂ)‖
        * ‖charFun (F.map Z) c ^ m‖
      ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * (3 / 2 * (r ^ 2 * M)) * 1 := by
        rw [hnormsq]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hone hsq.le) hBle (norm_nonneg _)
          (mul_nonneg hsq.le (by positivity))
    _ = 3 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ)) * M := by
        have hne : Real.sqrt ((m + 1 : ℕ) : ℝ) ≠ 0 := hsq.ne'
        rw [hrdef]
        field_simp

/-! ### The multilinear extension

`mixCharFun` carries a **linear** weight `⟪·, b⟫`, and that is exactly one slot. The third-order
delta-method surrogate of the studentized route,
`Hₙ = u − uvr/2 + u³r²/2 + 3uv²r²/8` with `r = n^{-1/2}`, is a polynomial of degree four in the
two coordinates, so expanding `E[e^{iθHₙ}]` in powers of `r` produces the weights `uv`, `u³`,
`uv²` and `(uv)²` — bilinear, trilinear and quartic. None of them is a `mixCharFun`, and this
is what makes the surrogate's characteristic function unavailable from the one-slot theory
alone. (It affects the *second*-order surrogate equally: its leading correction already needs
`E[uv e^{iθu}]`.)

The extension is not a wall, and it is carried out here. The exact factorisation of
`mixCharFun_vecRootLaw` rests only on the weight `⟪root, b⟫` being a *sum over the coordinates*;
a product of `k` such sums expands (`Finset.prod_univ_sum`) into a sum over the `nᵏ`
**assignments** `σ : Fin k → Fin n` of weight slots to coordinates. Regrouping an assignment
fiberwise (`Finset.prod_fiberwise`) turns its summand into a genuine product over the
coordinates — coordinate `i` carrying the weights in the fiber `σ⁻¹(i)` — and Fubini on
`Measure.pi` evaluates it as a product of one-dimensional integrals. The result is

`multi_{ρ_n}(b, a) = n^{-k/2} ∑_{σ : Fin k → Fin n} ∏_{i<n} slot_{σ⁻¹(i)}(n^{-1/2} • a)`,

a purely combinatorial identity: no moment assumption enters it beyond what is needed to make
each summand integrable. The one-slot statement is the case `k = 1`, where every `σ` has a
single distinguished coordinate, all `n` summands are equal, and the surviving
`n · n^{-1/2} = √n` is the `√n` of `mixCharFun_vecRootLaw`.

The **diagonal/off-diagonal bookkeeping** the applications need is now visible in the identity
rather than hidden: assignments `σ` that are injective contribute `k` distinct factors each
carrying one slot (these give the "leading" terms), while assignments with collisions
concentrate several slots on one coordinate and are suppressed by the extra powers of
`n^{-1/2}` relative to the number of free coordinates. -/

/-- The **multilinearly weighted characteristic function**
`∫ (∏_{l<k} ⟪w, b l⟫) e^{i⟪w,t⟫} ∂μ`.

For `k = 1` this is `mixCharFun` (`multiCharFun_one`) and for `k = 0` it is `charFun`
(`multiCharFun_zero`). The studentized surrogate needs `k` up to `4`, with repetitions among
the `b l` — the slots are an indexed family, not a set. -/
noncomputable def multiCharFun (μ : Measure E) {k : ℕ} (b : Fin k → E) (t : E) : ℂ :=
  ∫ w, (∏ l : Fin k, ((⟪w, b l⟫ : ℝ) : ℂ)) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) ∂μ

/-- The **single-coordinate factor** of the factorisation: the character in the direction `c`
of one summand, weighted by the inner products in the slots of `T`. `T = ∅` gives `charFun`
and `T = {l}` gives `mixCharFun`, both of the pushforward `F.map Z`. -/
noncomputable def slotCharFun (F : Measure ℝ) (Z : ℝ → E) {k : ℕ} (b : Fin k → E)
    (T : Finset (Fin k)) (c : E) : ℂ :=
  ∫ x, (∏ l ∈ T, ((⟪Z x, b l⟫ : ℝ) : ℂ)) * Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) ∂F

omit [BorelSpace E] [SecondCountableTopology E] in
@[simp] lemma multiCharFun_zero (μ : Measure E) (b : Fin 0 → E) (t : E) :
    multiCharFun μ b t = charFun μ t := by
  simp [multiCharFun, charFun_apply]

omit [BorelSpace E] [SecondCountableTopology E] in
@[simp] lemma multiCharFun_one (μ : Measure E) (b : E) (t : E) :
    multiCharFun μ (fun _ : Fin 1 => b) t = mixCharFun μ b t := by
  simp [multiCharFun, mixCharFun]

lemma slotCharFun_empty (F : Measure ℝ) {Z : ℝ → E} (hZ : Measurable Z) {k : ℕ}
    (b : Fin k → E) (c : E) :
    slotCharFun F Z b ∅ c = charFun (F.map Z) c := by
  rw [slotCharFun, charFun_apply, integral_map hZ.aemeasurable (by fun_prop)]
  simp

lemma slotCharFun_singleton (F : Measure ℝ) {Z : ℝ → E} (hZ : Measurable Z) {k : ℕ}
    (b : Fin k → E) (l : Fin k) (c : E) :
    slotCharFun F Z b {l} c = mixCharFun (F.map Z) (b l) c := by
  rw [slotCharFun, mixCharFun_map F hZ]
  simp

/-- **The multilinearly weighted characteristic function of a vector root factorises exactly.**

`∫ (∏_{l<k} ⟪w, b l⟫) e^{i⟪w,a⟫} ∂(vecRootLaw F Z n)
   = n^{-k/2} ∑_{σ : Fin k → Fin n} ∏_{i<n} slot_{σ⁻¹(i)}(n^{-1/2} • a)`.

This is the `k`-slot generalisation of `mixCharFun_vecRootLaw`, and it is what the third-order
delta-method surrogate's characteristic function needs: the surrogate is a degree-four
polynomial in the coordinates of the root, so its transform is a finite combination of
`multiCharFun`s with `k ≤ 4`.

The only hypothesis is that every *sub-product* of the weights be `F`-integrable, which is what
makes each of the `nᵏ` assignment summands integrable on `Measure.pi`; for `Z = studentPair F`
and `b` drawn from the two coordinate directions it is a moment condition on `F` of order at
most `2k`. -/
theorem multiCharFun_vecRootLaw (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {k n : ℕ} (b : Fin k → E)
    (hint : ∀ T : Finset (Fin k),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (a : E) :
    multiCharFun (vecRootLaw F Z n) b a
      = (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) ^ k *
          ∑ σ : Fin k → Fin n, ∏ i : Fin n,
            slotCharFun F Z b (Finset.univ.filter fun l => σ l = i)
              ((Real.sqrt (n : ℝ))⁻¹ • a) := by
  classical
  set r : ℝ := (Real.sqrt (n : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  set g : ℝ → ℂ := fun x => Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I) with hgdef
  have hgnorm : ∀ x, ‖g x‖ = 1 := by
    intro x; rw [hgdef]; simp [Complex.norm_exp]
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hbm : ∀ l : Fin k, Measurable fun x : ℝ => (⟪Z x, b l⟫ : ℝ) :=
    fun l => (measurable_inner_right (b l)).comp hZ
  -- the single-coordinate factor attached to a set `T` of slots
  set u : Finset (Fin k) → ℝ → ℂ :=
    fun T x => (∏ l ∈ T, ((⟪Z x, b l⟫ : ℝ) : ℂ)) * g x with hudef
  have hum : ∀ T, Measurable (u T) := by
    intro T
    refine Measurable.mul ?_ hgm
    exact Finset.measurable_prod _ fun l _ => (Complex.measurable_ofReal.comp (hbm l))
  have hunorm : ∀ (T : Finset (Fin k)) (x : ℝ), ‖u T x‖ = ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)| := by
    intro T x
    rw [hudef, norm_mul, hgnorm, mul_one, norm_prod]
    exact Finset.prod_congr rfl fun l _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
  have huint : ∀ T, Integrable (u T) F := by
    intro T
    refine Integrable.mono' (hint T) (hum T).aestronglyMeasurable ?_
    filter_upwards with x
    exact le_of_eq (hunorm T x)
  -- the fibre of an assignment over a coordinate
  set fib : (Fin k → Fin n) → Fin n → Finset (Fin k) :=
    fun σ i => Finset.univ.filter fun l => σ l = i with hfibdef
  -- step 1: the integrand over `Measure.pi`
  have hstep1 : multiCharFun (vecRootLaw F Z n) b a
      = ∫ y : Fin n → ℝ, ((r : ℂ) ^ k * ∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F) := by
    rw [multiCharFun, vecRootLaw,
      integral_map (measurable_vecRoot hZ n).aemeasurable (by fun_prop)]
    simp only [← hrdef]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only []
    -- the character factorises over the coordinates
    have hai : (⟪r • ∑ i, Z (y i), a⟫ : ℝ) = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) := by
      calc (⟪r • ∑ i, Z (y i), a⟫ : ℝ)
          = r * ⟪∑ i, Z (y i), a⟫ := real_inner_smul_left _ _ _
        _ = r * ∑ i : Fin n, (⟪Z (y i), a⟫ : ℝ) := by rw [sum_inner]
        _ = ∑ i : Fin n, r * (⟪Z (y i), a⟫ : ℝ) := Finset.mul_sum _ _ _
        _ = ∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ) := by
            simp only [hcdef, real_inner_smul_right]
    have hexp : Complex.exp (((∑ i : Fin n, (⟪Z (y i), c⟫ : ℝ)) : ℝ) * Complex.I)
        = ∏ i, g (y i) := by
      rw [Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
    -- the weight expands into assignments
    have hwt : (∏ l : Fin k, ((⟪r • ∑ i, Z (y i), b l⟫ : ℝ) : ℂ))
        = (r : ℂ) ^ k * ∑ σ : Fin k → Fin n, ∏ l : Fin k,
            ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ) := by
      have hbl : ∀ l : Fin k, ((⟪r • ∑ i, Z (y i), b l⟫ : ℝ) : ℂ)
          = (r : ℂ) * ∑ i : Fin n, ((⟪Z (y i), b l⟫ : ℝ) : ℂ) := by
        intro l
        have : (⟪r • ∑ i, Z (y i), b l⟫ : ℝ) = r * ∑ i : Fin n, (⟪Z (y i), b l⟫ : ℝ) := by
          rw [real_inner_smul_left, sum_inner]
        rw [this]
        push_cast
        ring
      simp_rw [hbl]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin n)))
        (fun (l : Fin k) (i : Fin n) => ((⟪Z (y i), b l⟫ : ℝ) : ℂ))
      rw [this, Fintype.piFinset_univ]
    rw [hai, hexp, hwt]
    -- each assignment summand is the product over coordinates of the slot factors
    have hassign : ∀ σ : Fin k → Fin n,
        (∏ l : Fin k, ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ)) * ∏ i, g (y i)
          = ∏ i, u (fib σ i) (y i) := by
      intro σ
      have hsplit : (∏ i, u (fib σ i) (y i))
          = (∏ i : Fin n, ∏ l ∈ fib σ i, ((⟪Z (y i), b l⟫ : ℝ) : ℂ)) * ∏ i, g (y i) := by
        rw [hudef, ← Finset.prod_mul_distrib]
      have hfibre : (∏ i : Fin n, ∏ l ∈ fib σ i, ((⟪Z (y i), b l⟫ : ℝ) : ℂ))
          = ∏ l : Fin k, ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ) := by
        have hcongr : ∀ i : Fin n, (∏ l ∈ fib σ i, ((⟪Z (y i), b l⟫ : ℝ) : ℂ))
            = ∏ l ∈ fib σ i, ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ) := by
          intro i
          refine Finset.prod_congr rfl fun l hl => ?_
          have : σ l = i := (Finset.mem_filter.1 hl).2
          rw [this]
        simp_rw [hcongr]
        exact Finset.prod_fiberwise Finset.univ σ fun l => ((⟪Z (y (σ l)), b l⟫ : ℝ) : ℂ)
      rw [hsplit, hfibre]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun σ _ => hassign σ
  -- step 2: pull out the constant, exchange the finite sum with the integral
  have hint2 : ∀ σ : Fin k → Fin n,
      Integrable (fun y : Fin n → ℝ => ∏ i, u (fib σ i) (y i))
        (Measure.pi fun _ : Fin n => F) :=
    fun σ => Integrable.fintype_prod fun i => huint (fib σ i)
  have hstep2 : (∫ y : Fin n → ℝ, ((r : ℂ) ^ k * ∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F))
      = (r : ℂ) ^ k * ∫ y : Fin n → ℝ, (∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F) := integral_const_mul _ _
  have hstep3 : (∫ y : Fin n → ℝ, (∑ σ : Fin k → Fin n, ∏ i, u (fib σ i) (y i))
        ∂(Measure.pi fun _ : Fin n => F))
      = ∑ σ : Fin k → Fin n, ∫ y : Fin n → ℝ, ∏ i, u (fib σ i) (y i)
        ∂(Measure.pi fun _ : Fin n => F) :=
    integral_finset_sum _ fun σ _ => hint2 σ
  -- step 3: Fubini on each assignment summand
  have hstep4 : ∀ σ : Fin k → Fin n,
      (∫ y : Fin n → ℝ, ∏ i, u (fib σ i) (y i) ∂(Measure.pi fun _ : Fin n => F))
        = ∏ i, slotCharFun F Z b (fib σ i) c :=
    fun σ => MeasureTheory.integral_fintype_prod_eq_prod fun i : Fin n => u (fib σ i)
  rw [hstep1, hstep2, hstep3]
  simp_rw [hstep4]
  rfl

end Mixed

/-! ### The `k = 2` diagonal/off-diagonal split, and why it is not bookkeeping

`multiCharFun_vecRootLaw` is an **identity**, not an estimate: it expresses the multilinearly
weighted characteristic function of a vector root as a sum over the `nᵏ` assignments of weight
slots to coordinates. Turning it into an estimate is what the studentized surrogate's transform
needs, and `norm_mixCharFun_vecRootLaw_sub_le` does it only for `k = 1`.

The `k = 1` case is deceptively simple because there is nothing to split: all `n` assignments
coincide, and the whole content is the surviving `n · n^{-1/2} = √n`. For `k = 2` the sum
genuinely splits, and **both halves contribute at the same order**:

* the `n` *diagonal* assignments give `n^{-1} · n · slot_{\{0,1\}}(c) · φ(c)^{n−1}`, of order `1`;
* the `n(n − 1)` *off-diagonal* ones give
  `n^{-1} · n(n − 1) · slot_{\{0\}}(c) · slot_{\{1\}}(c) · φ(c)^{n−2}`, and each single-slot factor
  is `O(n^{-1/2})` when `Z` is centred — so this block is `n^{-1} · n² · O(n⁻¹) = O(1)` as well.

Discarding the off-diagonal block, as the `k = 1` picture invites, would therefore change the
*limit* and not merely the remainder. That is why `Bootstrap/Edgeworth.lean`'s wave-23 note
records the `k ≥ 2` estimate as a genuine analytic residue rather than as wiring.

`multiCharFun_vecRootLaw_two` is the exact combinatorial half of that estimate: it evaluates the
assignment sum in closed form, leaving only a one-factor Taylor bound on `slot_{\{0\}}`,
`slot_{\{1\}}` and `slot_{\{0,1\}}` — the same kind of estimate
`norm_mixCharFun_vecRootLaw_sub_le` already performs at `k = 1`. The identity holds for every
`N`, including the degenerate `N = 0` and `N = 1` where the coefficient `N(N − 1)` vanishes on
its own. -/

section MultiTwo

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private lemma prod_fiber_diag {N : ℕ} (g : Finset (Fin 2) → ℂ) (j : Fin N) :
    (∏ i : Fin N, g (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i))
      = g Finset.univ * g ∅ ^ (N - 1) := by
  classical
  set h : Fin N → ℂ :=
    fun i => g (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i) with hh
  have hj : h j = g Finset.univ := by
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = j)
        = Finset.univ := by
      ext l
      fin_cases l <;> simp
    rw [hh]
    simp only [hset]
  have hother : ∀ i : Fin N, i ≠ j → h i = g ∅ := by
    intro i hi
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i)
        = ∅ := by
      ext l
      fin_cases l <;> simp [Ne.symm hi]
    rw [hh]
    simp only [hset]
  rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ j), hj]
  congr 1
  have hcard : (Finset.univ.erase j).card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  calc (∏ x ∈ Finset.univ.erase j, h x) = ∏ _x ∈ Finset.univ.erase j, g ∅ :=
        Finset.prod_congr rfl fun x hx => hother x (Finset.mem_erase.1 hx).1
    _ = g ∅ ^ (N - 1) := by rw [Finset.prod_const, hcard]

private lemma prod_fiber_offdiag {N : ℕ} (g : Finset (Fin 2) → ℂ) {j k : Fin N} (hjk : j ≠ k) :
    (∏ i : Fin N, g (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i))
      = g {0} * (g {1} * g ∅ ^ (N - 2)) := by
  classical
  set h : Fin N → ℂ :=
    fun i => g (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i) with hh
  have hj : h j = g {0} := by
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = j)
        = {0} := by
      ext l
      fin_cases l <;> simp [Ne.symm hjk]
    rw [hh]
    simp only [hset]
  have hk : h k = g {1} := by
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = k)
        = {1} := by
      ext l
      fin_cases l <;> simp [hjk]
    rw [hh]
    simp only [hset]
  have hother : ∀ i : Fin N, i ≠ j → i ≠ k → h i = g ∅ := by
    intro i hij hik
    have hset : (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i)
        = ∅ := by
      ext l
      fin_cases l <;> simp [Ne.symm hij, Ne.symm hik]
    rw [hh]
    simp only [hset]
  have hkmem : k ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨Ne.symm hjk, Finset.mem_univ k⟩
  rw [← Finset.mul_prod_erase Finset.univ h (Finset.mem_univ j), hj,
    ← Finset.mul_prod_erase (Finset.univ.erase j) h hkmem, hk]
  congr 2
  have hcard : ((Finset.univ.erase j).erase k).card = N - 2 := by
    rw [Finset.card_erase_of_mem hkmem, Finset.card_erase_of_mem (Finset.mem_univ j),
      Finset.card_univ, Fintype.card_fin]
    omega
  calc (∏ x ∈ (Finset.univ.erase j).erase k, h x)
      = ∏ _x ∈ (Finset.univ.erase j).erase k, g ∅ :=
        Finset.prod_congr rfl fun x hx =>
          hother x (Finset.mem_erase.1 (Finset.mem_erase.1 hx).2).1 (Finset.mem_erase.1 hx).1
    _ = g ∅ ^ (N - 2) := by rw [Finset.prod_const, hcard]

private lemma sum_pi_fin_two {N : ℕ} {M : Type*} [AddCommMonoid M] (G : (Fin 2 → Fin N) → M) :
    (∑ σ : Fin 2 → Fin N, G σ) = ∑ j : Fin N, ∑ k : Fin N, G ![j, k] := by
  have hfun : ∀ σ : Fin 2 → Fin N, (![σ 0, σ 1] : Fin 2 → Fin N) = σ := by
    intro σ
    funext l
    fin_cases l <;> rfl
  have h1 : (∑ σ : Fin 2 → Fin N, G σ) = ∑ p : Fin N × Fin N, G ![p.1, p.2] :=
    Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin N) _ _ fun σ => by
      simp only [piFinTwoEquiv_apply]
      exact (congrArg G (hfun σ)).symm
  rw [h1, Fintype.sum_prod_type]

variable (F : Measure ℝ) (Z : ℝ → E) (b : Fin 2 → E) (c : E)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The diagonal fibre computation, in the shape `multiCharFun_vecRootLaw` produces. -/
private lemma prod_fiber_diag' {N : ℕ} (j : Fin N) :
    (∏ i : Fin N, slotCharFun F Z b
        (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i) c)
      = slotCharFun F Z b Finset.univ c * slotCharFun F Z b ∅ c ^ (N - 1) :=
  prod_fiber_diag (fun T => slotCharFun F Z b T c) j

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- The off-diagonal fibre computation, in the shape `multiCharFun_vecRootLaw` produces. -/
private lemma prod_fiber_offdiag' {N : ℕ} {j k : Fin N} (hjk : j ≠ k) :
    (∏ i : Fin N, slotCharFun F Z b
        (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i) c)
      = slotCharFun F Z b {0} c *
          (slotCharFun F Z b {1} c * slotCharFun F Z b ∅ c ^ (N - 2)) :=
  prod_fiber_offdiag (fun T => slotCharFun F Z b T c) hjk

set_option maxHeartbeats 800000 in
-- The `Finset` rewrites below run over a nested sum whose summand is a product over `Fin N`
-- of `slotCharFun`s; the default heartbeat budget is not enough.
/-- **The `k = 2` assignment sum, in closed form.**

`multi_{ρ_N}(b, a) = N^{-1}(N · slot_{{0,1}}(c) φ(c)^{N−1} + N(N−1) · slot_{{0}}(c) slot_{{1}}(c)
φ(c)^{N−2})` with `c = N^{-1/2} • a`.

This is the exact combinatorial half of the `k = 2` estimate the studentized surrogate's
transform consumes; see the note above for why the second summand cannot be dropped. -/
theorem multiCharFun_vecRootLaw_two (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {N : ℕ} (b : Fin 2 → E)
    (hint : ∀ T : Finset (Fin 2),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (a : E) :
    multiCharFun (vecRootLaw F Z N) b a
      = (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ 2 *
        ((N : ℂ) * (slotCharFun F Z b Finset.univ ((Real.sqrt (N : ℝ))⁻¹ • a)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1))
          + (N : ℂ) * ((N : ℂ) - 1)
              * (slotCharFun F Z b {0} ((Real.sqrt (N : ℝ))⁻¹ • a)
                  * (slotCharFun F Z b {1} ((Real.sqrt (N : ℝ))⁻¹ • a)
                      * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2)))) := by
  classical
  rw [multiCharFun_vecRootLaw F hZ b hint a]
  congr 1
  rw [sum_pi_fin_two]
  have hempty := slotCharFun_empty F hZ b ((Real.sqrt (N : ℝ))⁻¹ • a)
  have hdiag : ∀ j : Fin N,
      (∏ i : Fin N, slotCharFun F Z b
          (Finset.univ.filter fun l : Fin 2 => (![j, j] : Fin 2 → Fin N) l = i)
          ((Real.sqrt (N : ℝ))⁻¹ • a))
        = slotCharFun F Z b Finset.univ ((Real.sqrt (N : ℝ))⁻¹ • a)
            * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1) := by
    intro j
    rw [prod_fiber_diag' F Z b ((Real.sqrt (N : ℝ))⁻¹ • a) j, hempty]
  have hoff : ∀ j k : Fin N, j ≠ k →
      (∏ i : Fin N, slotCharFun F Z b
          (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i)
          ((Real.sqrt (N : ℝ))⁻¹ • a))
        = slotCharFun F Z b {0} ((Real.sqrt (N : ℝ))⁻¹ • a)
            * (slotCharFun F Z b {1} ((Real.sqrt (N : ℝ))⁻¹ • a)
                * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2)) := by
    intro j k hjk
    rw [prod_fiber_offdiag' F Z b ((Real.sqrt (N : ℝ))⁻¹ • a) hjk, hempty]
  have hinner : ∀ j : Fin N,
      (∑ k : Fin N, ∏ i : Fin N, slotCharFun F Z b
          (Finset.univ.filter fun l : Fin 2 => (![j, k] : Fin 2 → Fin N) l = i)
          ((Real.sqrt (N : ℝ))⁻¹ • a))
        = slotCharFun F Z b Finset.univ ((Real.sqrt (N : ℝ))⁻¹ • a)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1)
          + ((N : ℂ) - 1) * (slotCharFun F Z b {0} ((Real.sqrt (N : ℝ))⁻¹ • a)
              * (slotCharFun F Z b {1} ((Real.sqrt (N : ℝ))⁻¹ • a)
                  * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2))) := by
    intro j
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
    have hcard : (Finset.univ.erase j).card = N - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    have hcast : (((N - 1 : ℕ) : ℂ)) = (N : ℂ) - 1 := by
      have := Nat.cast_sub (R := ℂ) hN
      simpa using this
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j), hdiag j,
      Finset.sum_congr rfl (fun k hk => hoff j k (Ne.symm (Finset.mem_erase.1 hk).1)),
      Finset.sum_const, hcard, nsmul_eq_mul, hcast]
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hinner j), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end MultiTwo

/-! ### The `k = 2` estimate: the analytic half

`multiCharFun_vecRootLaw_two` closes the *combinatorial* half of the `k = 2` estimate. What is
left is the analytic half, and it is the same one-factor Taylor bound that
`norm_mixCharFun_vecRootLaw_sub_le` performs at `k = 1`, now applied to the three surviving
slots of the closed form:

* `slot_{{0,1}}(c) = ∫⟪x,b₀⟫⟪x,b₁⟫e^{i⟪x,c⟫}` is within `‖e^{iy} − 1‖ ≤ |y|` of the plain
  covariance `κ₀₁ = ∫⟪x,b₀⟫⟪x,b₁⟫`, at cost `N^{-1/2}∫|⟪x,b₀⟫⟪x,b₁⟫||⟪x,a⟫|`. **No centring is
  used here**: the diagonal block already has its `O(1)` limit at zeroth order;
* `slot_{{j}}(c) = mix_μ(b_j, c)` is within `(3/2)N⁻¹∫|⟪x,b_j⟫|⟪x,a⟫²` of `i N^{-1/2} κ_j` with
  `κ_j = ∫⟪x,b_j⟫⟪x,a⟫`, by `norm_mixCharFun_sub_mul_I_le`. **Here the centring is what
  matters**: without `∫⟪x,b_j⟫ = 0` the slot is `O(1)` rather than `O(N^{-1/2})`, and the
  off-diagonal block — which carries the factor `N(N−1)N^{-1} = N − 1` — would diverge.

The two combine to `multi_{ρ_N}(b,a) = κ₀₁φ^{N−1} − κ₀κ₁φ^{N−2} + O(N^{-1/2})`, the accuracy the
studentized surrogate's coefficient `c₂ = θr/2σ³` requires. Three points are worth recording.

*The off-diagonal limit is `−κ₀κ₁`, not `0`.* The product of the two purely imaginary leading
terms is `(i N^{-1/2}κ₀)(i N^{-1/2}κ₁) = −κ₀κ₁/N`, and the block's multiplicity `N − 1` cancels
the `N⁻¹` exactly. This is the quantitative form of the wave-23 warning: the block is of the
same order as the diagonal, and its sign is opposite.

*The error of the multiplicity is `O(N⁻¹)`, not `O(1)`.* `(N − 1)/N = 1 − N⁻¹`, so replacing
`N − 1` by `N` costs only `N⁻¹|κ₀κ₁|` — which is why the closed form can be used with the exact
coefficient `N(N−1)` and no loss.

*The two powers `φ^{N−1}` and `φ^{N−2}` are kept apart.* Collapsing them costs `‖φ(c) − 1‖`,
which is `O(N⁻¹)` only after a centring in the direction `a` (`norm_charFun_sub_one_le`); since
the consumer compares both powers with the same Gaussian anyway, nothing is gained by doing it
here, and one hypothesis is saved. -/

section MultiTwoEstimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- `slotCharFun` read on the pushforward law: the slot factor is a weighted character of
`F.map Z`, not of `F`. -/
lemma slotCharFun_eq_integral_map (F : Measure ℝ) {Z : ℝ → E} (hZ : Measurable Z) {k : ℕ}
    (b : Fin k → E) (T : Finset (Fin k)) (c : E) :
    slotCharFun F Z b T c
      = ∫ w, (∏ l ∈ T, ((⟪w, b l⟫ : ℝ) : ℂ))
          * Complex.exp ((⟪w, c⟫ : ℝ) * Complex.I) ∂(F.map Z) := by
  rw [slotCharFun, integral_map hZ.aemeasurable (by fun_prop)]

omit [SecondCountableTopology E] in
/-- **A weighted character is within one moment of the weight's own integral.**
`‖∫ g e^{i⟪·,t⟫} − ∫ g‖ ≤ ∫ |g| |⟪·,t⟫|`, from `‖e^{iy} − 1‖ ≤ |y|`.

This is the zeroth-order companion of `norm_mixCharFun_sub_mul_I_le`: no centring is needed
because the leading term is the weight's integral itself rather than `0`. It is what the
*diagonal* slot of the `k = 2` estimate consumes. -/
lemma norm_integral_ofReal_mul_cexp_sub_le (μ : Measure E) {g : E → ℝ} {t : E}
    (hgmeas : Measurable g) (hg : Integrable g μ)
    (hgt : Integrable (fun x : E => |g x| * |(⟪x, t⟫ : ℝ)|) μ) :
    ‖(∫ w, ((g w : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) ∂μ)
        - ((∫ w, g w ∂μ : ℝ) : ℂ)‖
      ≤ ∫ w, |g w| * |(⟪w, t⟫ : ℝ)| ∂μ := by
  have htm : Measurable fun w : E => (⟪w, t⟫ : ℝ) := measurable_inner_right t
  have hem : Measurable fun w : E => Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) := by fun_prop
  have hA : Integrable
      (fun w : E => ((g w : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I)) μ := by
    refine Integrable.mono' hg.norm
      (((Complex.measurable_ofReal.comp hgmeas).mul hem).aestronglyMeasurable) ?_
    filter_upwards with w
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    simp
  have hB : Integrable (fun w : E => ((g w : ℝ) : ℂ)) μ := hg.ofReal
  have hkey : (∫ w, ((g w : ℝ) : ℂ)
        * (Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) - 1) ∂μ)
      = (∫ w, ((g w : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) ∂μ)
        - ((∫ w, g w ∂μ : ℝ) : ℂ) := by
    have hpt : ∀ w : E, ((g w : ℝ) : ℂ) * (Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) - 1)
        = ((g w : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I)
          - ((g w : ℝ) : ℂ) := fun w => by ring
    have hsp : (∫ w, (((g w : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I)
          - ((g w : ℝ) : ℂ)) ∂μ)
        = (∫ w, ((g w : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) ∂μ)
          - ∫ w, ((g w : ℝ) : ℂ) ∂μ := integral_sub hA hB
    calc (∫ w, ((g w : ℝ) : ℂ) * (Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I) - 1) ∂μ)
        = ∫ w, (((g w : ℝ) : ℂ) * Complex.exp ((⟪w, t⟫ : ℝ) * Complex.I)
            - ((g w : ℝ) : ℂ)) ∂μ := integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = _ := by rw [hsp, integral_complex_ofReal]
  rw [← hkey]
  refine norm_integral_le_of_norm_le hgt (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (⟪w, t⟫ : ℝ))
  rw [Real.norm_eq_abs] at h
  rwa [mul_comm ((⟪w, t⟫ : ℝ) : ℂ) Complex.I]

/-- The remainder constant of the `k = 2` estimate: the mixed third moments of the two slot
directions against `a`, the two covariances, and their products. Every summand is a moment of
the *sampling* law, not of the root, so it does not grow with `N`. -/
noncomputable def multiTwoRemConst (μ : Measure E) (b : Fin 2 → E) (a : E) : ℝ :=
  (∫ x, |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)| ∂μ)
    + |∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂μ| * |∫ x, (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂μ|
    + 3 / 2 * (|∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂μ|
          * ∫ x, |(⟪x, b 1⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂μ
        + (∫ x, |(⟪x, b 0⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂μ)
          * |∫ x, (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂μ|)
    + 9 / 4 * (∫ x, |(⟪x, b 0⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂μ)
        * ∫ x, |(⟪x, b 1⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂μ

set_option maxHeartbeats 1000000 in
-- The proof carries six named moments and three slot estimates through a long chain of
-- norm inequalities; the default heartbeat budget is not enough for the final elaboration.
/-- **The `k = 2` estimate for the multilinearly weighted characteristic function of a vector
root.**

`‖multi_{ρ_N}(b, a) − (κ₀₁ φ(c)^{N−1} − κ₀κ₁ φ(c)^{N−2})‖ ≤ N^{-1/2} · multiTwoRemConst`,

with `c = N^{-1/2} • a`, `κ₀₁ = ∫⟪x,b₀⟫⟪x,b₁⟫`, `κ_j = ∫⟪x,b_j⟫⟪x,a⟫`, for a law centred in
both slot directions.

This is the analytic half of the item the wave-23 note of `Bootstrap/Edgeworth.lean` records as
residue (i) at `k = 2`, and its accuracy `O(N^{-1/2})` is what the studentized surrogate's
coefficient `c₂ = θr/2σ³` needs. The off-diagonal contribution `−κ₀κ₁ φ^{N−2}` is *not* a
remainder: it is of the same order as the diagonal and of opposite sign, so the `k = 1` picture
— where no off-diagonal exists — would give the wrong limit. -/
theorem norm_multiCharFun_vecRootLaw_two_sub_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {N : ℕ} (hN : 1 ≤ N) (b : Fin 2 → E) (a : E)
    (hint : ∀ T : Finset (Fin 2),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (hb0 : Integrable (fun x : E => (⟪x, b 0⟫ : ℝ)) (F.map Z))
    (hb1 : Integrable (fun x : E => (⟪x, b 1⟫ : ℝ)) (F.map Z))
    (hm0 : ∫ x, (⟪x, b 0⟫ : ℝ) ∂(F.map Z) = 0)
    (hm1 : ∫ x, (⟪x, b 1⟫ : ℝ) ∂(F.map Z) = 0)
    (hb0a : Integrable (fun x : E => (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hb1a : Integrable (fun x : E => (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hb0a2 : Integrable (fun x : E => |(⟪x, b 0⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hb1a2 : Integrable (fun x : E => |(⟪x, b 1⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hprod : Integrable (fun x : E => (⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)) (F.map Z))
    (hproda : Integrable
      (fun x : E => |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) (F.map Z)) :
    ‖multiCharFun (vecRootLaw F Z N) b a
        - (((∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ) ∂(F.map Z) : ℝ) : ℂ)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1)
            - (((∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z))
                  * (∫ x, (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z)) : ℝ) : ℂ)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2))‖
      ≤ (Real.sqrt (N : ℝ))⁻¹ * multiTwoRemConst (F.map Z) b a := by
  classical
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hsq : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hN1
  set r : ℝ := (Real.sqrt (N : ℝ))⁻¹ with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]; exact inv_pos.2 (lt_of_lt_of_le zero_lt_one hsq)
  have hr1 : r ≤ 1 := by
    rw [hrdef]; exact inv_le_one_of_one_le₀ hsq
  have hr2 : r ^ 2 = ((N : ℝ))⁻¹ := by
    rw [hrdef, inv_pow, Real.sq_sqrt hNpos.le]
  have hNr : (N : ℝ) * r ^ 2 = 1 := by rw [hr2]; field_simp
  have hr2le : r ^ 2 ≤ r := by nlinarith [hrpos, hr1]
  set c : E := r • a with hcdef
  set φ : ℂ := charFun (F.map Z) c with hφdef
  have hφ1 : ‖φ‖ ≤ 1 := by rw [hφdef]; exact norm_charFun_le_one c
  have hφp : ∀ m : ℕ, ‖φ ^ m‖ ≤ 1 := fun m => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hφ1
  have hca : ∀ w : E, (⟪w, c⟫ : ℝ) = r * (⟪w, a⟫ : ℝ) := fun w => by
    rw [hcdef, real_inner_smul_right]
  -- the moments
  set κ01 : ℝ := ∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ) ∂(F.map Z) with hκ01
  set κ0 : ℝ := ∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκ0
  set κ1 : ℝ := ∫ x, (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκ1
  set M0 : ℝ := ∫ x, |(⟪x, b 0⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) with hM0
  set M1 : ℝ := ∫ x, |(⟪x, b 1⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) with hM1
  set M01 : ℝ := ∫ x, |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)| ∂(F.map Z) with hM01
  have hM0nn : 0 ≤ M0 := by rw [hM0]; exact integral_nonneg fun x => by positivity
  have hM1nn : 0 ≤ M1 := by rw [hM1]; exact integral_nonneg fun x => by positivity
  have hM01nn : 0 ≤ M01 := by rw [hM01]; exact integral_nonneg fun x => by positivity
  -- the diagonal slot
  have hdiag : ‖slotCharFun F Z b Finset.univ c - (κ01 : ℂ)‖ ≤ r * M01 := by
    have hgm : Measurable fun w : E => (⟪w, b 0⟫ : ℝ) * (⟪w, b 1⟫ : ℝ) :=
      (measurable_inner_right (b 0)).mul (measurable_inner_right (b 1))
    have hgt : Integrable
        (fun x : E => |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|) (F.map Z) := by
      have hEq : (fun x : E => |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|)
          = fun x : E => r * (|(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := by
        funext x
        rw [hca x, abs_mul r ((⟪x, a⟫ : ℝ)), abs_of_pos hrpos]
        ring
      rw [hEq]
      exact hproda.const_mul r
    have hmom : (∫ x, |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)| ∂(F.map Z))
        = r * M01 := by
      have hEq : ∀ x : E, |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|
          = r * (|(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := fun x => by
        rw [hca x, abs_mul r ((⟪x, a⟫ : ℝ)), abs_of_pos hrpos]; ring
      simp_rw [hEq]
      rw [hM01]
      exact integral_const_mul _ _
    have hslot : slotCharFun F Z b Finset.univ c
        = ∫ w, (((⟪w, b 0⟫ : ℝ) * (⟪w, b 1⟫ : ℝ) : ℝ) : ℂ)
            * Complex.exp ((⟪w, c⟫ : ℝ) * Complex.I) ∂(F.map Z) := by
      rw [slotCharFun_eq_integral_map F hZ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [Fin.prod_univ_two, Complex.ofReal_mul]
    rw [hslot, hκ01, ← hmom]
    exact norm_integral_ofReal_mul_cexp_sub_le (F.map Z) hgm hprod hgt
  -- the two single slots
  have hslotone : ∀ j : Fin 2, ∀ κ M : ℝ,
      Integrable (fun x : E => (⟪x, b j⟫ : ℝ)) (F.map Z) →
      (∫ x, (⟪x, b j⟫ : ℝ) ∂(F.map Z)) = 0 →
      Integrable (fun x : E => (⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z) →
      Integrable (fun x : E => |(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z) →
      (∫ x, (⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z)) = κ →
      (∫ x, |(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) = M →
      ‖slotCharFun F Z b {j} c - Complex.I * ((r * κ : ℝ) : ℂ)‖ ≤ 3 / 2 * (r ^ 2 * M) := by
    intro j κ M hbj hmj hbja hbja2 hκj hMj
    have hbtc : Integrable (fun x : E => (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ)) (F.map Z) := by
      have hEq : (fun x : E => (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ))
          = fun x : E => r * ((⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := by
        funext x; rw [hca x]; ring
      rw [hEq]; exact hbja.const_mul r
    have hbt2c : Integrable (fun x : E => |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2) (F.map Z) := by
      have hEq : (fun x : E => |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2)
          = fun x : E => r ^ 2 * (|(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := by
        funext x; rw [hca x]; ring
      rw [hEq]; exact hbja2.const_mul (r ^ 2)
    have hκc : (∫ x, (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ) ∂(F.map Z)) = r * κ := by
      have hEq : ∀ x : E, (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ)
          = r * ((⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := fun x => by rw [hca x]; ring
      simp_rw [hEq]
      rw [integral_const_mul, hκj]
    have hMc : (∫ x, |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2 ∂(F.map Z)) = r ^ 2 * M := by
      have hEq : ∀ x : E, |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2
          = r ^ 2 * (|(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := fun x => by rw [hca x]; ring
      simp_rw [hEq]
      rw [integral_const_mul, hMj]
    have h := norm_mixCharFun_sub_mul_I_le (F.map Z) hbj hbtc hbt2c hmj
    rw [hκc, hMc] at h
    rwa [slotCharFun_singleton F hZ b j c]
  have e0 : ‖slotCharFun F Z b {0} c - Complex.I * ((r * κ0 : ℝ) : ℂ)‖
      ≤ 3 / 2 * (r ^ 2 * M0) := hslotone 0 κ0 M0 hb0 hm0 hb0a hb0a2 hκ0.symm hM0.symm
  have e1 : ‖slotCharFun F Z b {1} c - Complex.I * ((r * κ1 : ℝ) : ℂ)‖
      ≤ 3 / 2 * (r ^ 2 * M1) := hslotone 1 κ1 M1 hb1 hm1 hb1a hb1a2 hκ1.symm hM1.symm
  -- the closed form of the assignment sum, with `r² N = 1` used to clear the prefactor
  have hw : ((r : ℝ) : ℂ) ^ 2 * (N : ℂ) = 1 := by
    have : ((r ^ 2 * (N : ℝ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [show r ^ 2 * (N : ℝ) = 1 by linarith [hNr]]
    push_cast at this
    linear_combination this
  have hid : multiCharFun (vecRootLaw F Z N) b a
      = slotCharFun F Z b Finset.univ c * φ ^ (N - 1)
        + ((N : ℂ) - 1) * (slotCharFun F Z b {0} c
            * (slotCharFun F Z b {1} c * φ ^ (N - 2))) := by
    rw [multiCharFun_vecRootLaw_two F hZ b hint a, ← hrdef, ← hcdef, ← hφdef]
    have hexpand : (((r : ℝ) : ℂ)) ^ 2 * ((N : ℂ) * (slotCharFun F Z b Finset.univ c * φ ^ (N - 1))
          + (N : ℂ) * ((N : ℂ) - 1) * (slotCharFun F Z b {0} c
              * (slotCharFun F Z b {1} c * φ ^ (N - 2))))
        = (((r : ℝ) : ℂ) ^ 2 * (N : ℂ)) * (slotCharFun F Z b Finset.univ c * φ ^ (N - 1))
          + (((r : ℝ) : ℂ) ^ 2 * (N : ℂ)) * (((N : ℂ) - 1) * (slotCharFun F Z b {0} c
              * (slotCharFun F Z b {1} c * φ ^ (N - 2)))) := by ring
    rw [hexpand, hw, one_mul, one_mul]
  -- the algebraic decomposition of the difference
  set s01 : ℂ := slotCharFun F Z b Finset.univ c with hs01
  set s0 : ℂ := slotCharFun F Z b {0} c with hs0
  set s1 : ℂ := slotCharFun F Z b {1} c with hs1
  set p0 : ℂ := Complex.I * ((r * κ0 : ℝ) : ℂ) with hp0
  set p1 : ℂ := Complex.I * ((r * κ1 : ℝ) : ℂ) with hp1
  have hp0n : ‖p0‖ = r * |κ0| := by
    rw [hp0, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hrpos]
  have hp1n : ‖p1‖ = r * |κ1| := by
    rw [hp1, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hrpos]
  have hs0n : ‖s0‖ ≤ r * |κ0| + 3 / 2 * (r ^ 2 * M0) := by
    have hsplit : s0 = p0 + (s0 - p0) := by ring
    calc ‖s0‖ = ‖p0 + (s0 - p0)‖ := by rw [← hsplit]
      _ ≤ ‖p0‖ + ‖s0 - p0‖ := norm_add_le _ _
      _ ≤ r * |κ0| + 3 / 2 * (r ^ 2 * M0) := by rw [hp0n]; linarith [e0]
  have hp0p1 : p0 * p1 = -(((r ^ 2 * (κ0 * κ1) : ℝ)) : ℂ) := by
    rw [hp0, hp1]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hoffprod : ‖s0 * s1 - p0 * p1‖
      ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) := by
    have heq : s0 * s1 - p0 * p1 = s0 * (s1 - p1) + (s0 - p0) * p1 := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hp1n]
    have h1 : ‖s0‖ * ‖s1 - p1‖ ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1)) :=
      mul_le_mul hs0n e1 (norm_nonneg _) (by positivity)
    have h2 : ‖s0 - p0‖ * (r * |κ1|) ≤ 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) :=
      mul_le_mul_of_nonneg_right e0 (by positivity)
    linarith
  -- the multiplicity `N − 1` and the exact cancellation of the leading off-diagonal term
  have hmult : ((N : ℂ) - 1) * (p0 * p1) + ((κ0 * κ1 : ℝ) : ℂ)
      = ((r ^ 2 * (κ0 * κ1) : ℝ) : ℂ) := by
    have hcast : ((N : ℂ) - 1) = ((((N : ℝ) - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hp0p1, hcast, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      Complex.ofReal_inj]
    have hfin : ((N : ℝ) - 1) * (r ^ 2 * (κ0 * κ1)) = (κ0 * κ1) - r ^ 2 * (κ0 * κ1) := by
      linear_combination (κ0 * κ1) * hNr
    linarith [hfin]
  have hNm1 : ‖((N : ℂ) - 1)‖ = (N : ℝ) - 1 := by
    have hcast : ((N : ℂ) - 1) = ((((N : ℝ) - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ) - 1)]
  have hT2 : ‖((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)‖
      ≤ ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1| := by
    have heq : ((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)
        = ((N : ℂ) - 1) * (s0 * s1 - p0 * p1)
          + (((N : ℂ) - 1) * (p0 * p1) + ((κ0 * κ1 : ℝ) : ℂ)) := by ring
    rw [heq, hmult]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hNm1, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2)]
    have := mul_le_mul_of_nonneg_left hoffprod (by linarith : (0:ℝ) ≤ (N:ℝ) - 1)
    linarith
  -- assembly
  have hsplit : multiCharFun (vecRootLaw F Z N) b a
      - ((κ01 : ℂ) * φ ^ (N - 1) - ((κ0 * κ1 : ℝ) : ℂ) * φ ^ (N - 2))
      = (s01 - (κ01 : ℂ)) * φ ^ (N - 1)
        + (((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)) * φ ^ (N - 2) := by
    rw [hid]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hb1' : ‖(s01 - (κ01 : ℂ))‖ * ‖φ ^ (N - 1)‖ ≤ r * M01 :=
    calc ‖(s01 - (κ01 : ℂ))‖ * ‖φ ^ (N - 1)‖ ≤ (r * M01) * 1 :=
          mul_le_mul hdiag (hφp _) (norm_nonneg _) (by positivity)
      _ = r * M01 := mul_one _
  have hnn2 : (0 : ℝ) ≤ ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0))
        * (3 / 2 * (r ^ 2 * M1)) + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1| := by
    have hA : (0 : ℝ) ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) := by positivity
    have hB : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
    have hC : (0 : ℝ) ≤ r ^ 2 * |κ0 * κ1| := by positivity
    nlinarith [mul_nonneg hB hA]
  have hb2' : ‖((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)‖ * ‖φ ^ (N - 2)‖
      ≤ ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1| :=
    calc ‖((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)‖ * ‖φ ^ (N - 2)‖
        ≤ (((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
            + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1|) * 1 :=
          mul_le_mul hT2 (hφp _) (norm_nonneg _) hnn2
      _ = _ := mul_one _
  -- the arithmetic: `N − 1 ≤ N` and `N r² = 1` turn `N r³` into `r` and `N r⁴` into `r²`
  have hmid : ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|))
      ≤ 3 / 2 * r * |κ0| * M1 + 9 / 4 * r ^ 2 * M0 * M1 + 3 / 2 * r * M0 * |κ1| := by
    have hpos : (0 : ℝ) ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) := by positivity
    have hle : ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|))
        ≤ (N : ℝ) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos
    have heq : (N : ℝ) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|))
        = 3 / 2 * r * |κ0| * M1 + 9 / 4 * r ^ 2 * M0 * M1 + 3 / 2 * r * M0 * |κ1| := by
      linear_combination (3 / 2 * r * |κ0| * M1 + 9 / 4 * r ^ 2 * M0 * M1
        + 3 / 2 * r * M0 * |κ1|) * hNr
    linarith [hle, heq.le, heq.ge]
  rw [multiTwoRemConst, ← hκ0, ← hκ1, ← hM0, ← hM1, ← hM01]
  have habs : |κ0 * κ1| = |κ0| * |κ1| := abs_mul _ _
  have h1 : r ^ 2 * |κ0 * κ1| ≤ r * (|κ0| * |κ1|) := by
    rw [habs]
    exact mul_le_mul_of_nonneg_right hr2le (by positivity)
  have h2 : 9 / 4 * r ^ 2 * M0 * M1 ≤ 9 / 4 * (r * (M0 * M1)) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hr2le) (mul_nonneg hM0nn hM1nn)]
  linarith [hb1', hb2', hmid, h1, h2]

set_option maxHeartbeats 1000000 in
-- Same shape as `norm_multiCharFun_vecRootLaw_two_sub_le`: six named moments and three slot
-- estimates carried through a long chain of norm inequalities.
/-- **The `k = 2` estimate, with its Gaussian damping kept.**

`‖multi_{ρ_N}(b, a) − (κ₀₁φ(c)^{N−1} − κ₀κ₁φ(c)^{N−2})‖ ≤ N^{-1/2}·multiTwoRemConst·‖φ(c)‖^{N−2}`

under exactly the hypotheses of `norm_multiCharFun_vecRootLaw_two_sub_le`, of which this is a
strict sharpening. Both error terms of the decomposition multiply `φ(c)^{N−1}` or `φ(c)^{N−2}`
— the assignment sum has nothing else in it — so the only change is that those two powers are
kept instead of being rounded up to `1`.

The companion of `norm_multiCharFun_vecRootLaw_damped_le` at `k = 2`, and needed for the same
reason: the studentized window of `Bootstrap/Edgeworth.lean` evaluates this at `a = (θ/σ)•e₀`
with `|θ|` growing like `√N`, where `multiTwoRemConst` is a polynomial in `|θ|` of degree four
and the undamped bound has nothing to control it. See the wave-42 note there. -/
theorem norm_multiCharFun_vecRootLaw_two_sub_damped_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {N : ℕ} (hN : 1 ≤ N) (b : Fin 2 → E) (a : E)
    (hint : ∀ T : Finset (Fin 2),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (hb0 : Integrable (fun x : E => (⟪x, b 0⟫ : ℝ)) (F.map Z))
    (hb1 : Integrable (fun x : E => (⟪x, b 1⟫ : ℝ)) (F.map Z))
    (hm0 : ∫ x, (⟪x, b 0⟫ : ℝ) ∂(F.map Z) = 0)
    (hm1 : ∫ x, (⟪x, b 1⟫ : ℝ) ∂(F.map Z) = 0)
    (hb0a : Integrable (fun x : E => (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hb1a : Integrable (fun x : E => (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hb0a2 : Integrable (fun x : E => |(⟪x, b 0⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hb1a2 : Integrable (fun x : E => |(⟪x, b 1⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hprod : Integrable (fun x : E => (⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)) (F.map Z))
    (hproda : Integrable
      (fun x : E => |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) (F.map Z)) :
    ‖multiCharFun (vecRootLaw F Z N) b a
        - (((∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ) ∂(F.map Z) : ℝ) : ℂ)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 1)
            - (((∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z))
                  * (∫ x, (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z)) : ℝ) : ℂ)
              * charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a) ^ (N - 2))‖
      ≤ (Real.sqrt (N : ℝ))⁻¹ * multiTwoRemConst (F.map Z) b a
        * ‖charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a)‖ ^ (N - 2) := by
  classical
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  have hsq : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hN1
  set r : ℝ := (Real.sqrt (N : ℝ))⁻¹ with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]; exact inv_pos.2 (lt_of_lt_of_le zero_lt_one hsq)
  have hr1 : r ≤ 1 := by
    rw [hrdef]; exact inv_le_one_of_one_le₀ hsq
  have hr2 : r ^ 2 = ((N : ℝ))⁻¹ := by
    rw [hrdef, inv_pow, Real.sq_sqrt hNpos.le]
  have hNr : (N : ℝ) * r ^ 2 = 1 := by rw [hr2]; field_simp
  have hr2le : r ^ 2 ≤ r := by nlinarith [hrpos, hr1]
  set c : E := r • a with hcdef
  set φ : ℂ := charFun (F.map Z) c with hφdef
  have hφ1 : ‖φ‖ ≤ 1 := by rw [hφdef]; exact norm_charFun_le_one c
  have hφp : ∀ m : ℕ, N - 2 ≤ m → ‖φ ^ m‖ ≤ ‖φ‖ ^ (N - 2) := fun m hm => by
    rw [norm_pow]; exact pow_le_pow_of_le_one (norm_nonneg _) hφ1 hm
  have hφP : (0 : ℝ) ≤ ‖φ‖ ^ (N - 2) := by positivity
  have hca : ∀ w : E, (⟪w, c⟫ : ℝ) = r * (⟪w, a⟫ : ℝ) := fun w => by
    rw [hcdef, real_inner_smul_right]
  -- the moments
  set κ01 : ℝ := ∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ) ∂(F.map Z) with hκ01
  set κ0 : ℝ := ∫ x, (⟪x, b 0⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκ0
  set κ1 : ℝ := ∫ x, (⟪x, b 1⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκ1
  set M0 : ℝ := ∫ x, |(⟪x, b 0⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) with hM0
  set M1 : ℝ := ∫ x, |(⟪x, b 1⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) with hM1
  set M01 : ℝ := ∫ x, |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)| ∂(F.map Z) with hM01
  have hM0nn : 0 ≤ M0 := by rw [hM0]; exact integral_nonneg fun x => by positivity
  have hM1nn : 0 ≤ M1 := by rw [hM1]; exact integral_nonneg fun x => by positivity
  have hM01nn : 0 ≤ M01 := by rw [hM01]; exact integral_nonneg fun x => by positivity
  -- the diagonal slot
  have hdiag : ‖slotCharFun F Z b Finset.univ c - (κ01 : ℂ)‖ ≤ r * M01 := by
    have hgm : Measurable fun w : E => (⟪w, b 0⟫ : ℝ) * (⟪w, b 1⟫ : ℝ) :=
      (measurable_inner_right (b 0)).mul (measurable_inner_right (b 1))
    have hgt : Integrable
        (fun x : E => |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|) (F.map Z) := by
      have hEq : (fun x : E => |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|)
          = fun x : E => r * (|(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := by
        funext x
        rw [hca x, abs_mul r ((⟪x, a⟫ : ℝ)), abs_of_pos hrpos]
        ring
      rw [hEq]
      exact hproda.const_mul r
    have hmom : (∫ x, |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)| ∂(F.map Z))
        = r * M01 := by
      have hEq : ∀ x : E, |(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|
          = r * (|(⟪x, b 0⟫ : ℝ) * (⟪x, b 1⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := fun x => by
        rw [hca x, abs_mul r ((⟪x, a⟫ : ℝ)), abs_of_pos hrpos]; ring
      simp_rw [hEq]
      rw [hM01]
      exact integral_const_mul _ _
    have hslot : slotCharFun F Z b Finset.univ c
        = ∫ w, (((⟪w, b 0⟫ : ℝ) * (⟪w, b 1⟫ : ℝ) : ℝ) : ℂ)
            * Complex.exp ((⟪w, c⟫ : ℝ) * Complex.I) ∂(F.map Z) := by
      rw [slotCharFun_eq_integral_map F hZ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
      simp only [Fin.prod_univ_two, Complex.ofReal_mul]
    rw [hslot, hκ01, ← hmom]
    exact norm_integral_ofReal_mul_cexp_sub_le (F.map Z) hgm hprod hgt
  -- the two single slots
  have hslotone : ∀ j : Fin 2, ∀ κ M : ℝ,
      Integrable (fun x : E => (⟪x, b j⟫ : ℝ)) (F.map Z) →
      (∫ x, (⟪x, b j⟫ : ℝ) ∂(F.map Z)) = 0 →
      Integrable (fun x : E => (⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z) →
      Integrable (fun x : E => |(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z) →
      (∫ x, (⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z)) = κ →
      (∫ x, |(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) = M →
      ‖slotCharFun F Z b {j} c - Complex.I * ((r * κ : ℝ) : ℂ)‖ ≤ 3 / 2 * (r ^ 2 * M) := by
    intro j κ M hbj hmj hbja hbja2 hκj hMj
    have hbtc : Integrable (fun x : E => (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ)) (F.map Z) := by
      have hEq : (fun x : E => (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ))
          = fun x : E => r * ((⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := by
        funext x; rw [hca x]; ring
      rw [hEq]; exact hbja.const_mul r
    have hbt2c : Integrable (fun x : E => |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2) (F.map Z) := by
      have hEq : (fun x : E => |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2)
          = fun x : E => r ^ 2 * (|(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := by
        funext x; rw [hca x]; ring
      rw [hEq]; exact hbja2.const_mul (r ^ 2)
    have hκc : (∫ x, (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ) ∂(F.map Z)) = r * κ := by
      have hEq : ∀ x : E, (⟪x, b j⟫ : ℝ) * (⟪x, c⟫ : ℝ)
          = r * ((⟪x, b j⟫ : ℝ) * (⟪x, a⟫ : ℝ)) := fun x => by rw [hca x]; ring
      simp_rw [hEq]
      rw [integral_const_mul, hκj]
    have hMc : (∫ x, |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2 ∂(F.map Z)) = r ^ 2 * M := by
      have hEq : ∀ x : E, |(⟪x, b j⟫ : ℝ)| * (⟪x, c⟫ : ℝ) ^ 2
          = r ^ 2 * (|(⟪x, b j⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) := fun x => by rw [hca x]; ring
      simp_rw [hEq]
      rw [integral_const_mul, hMj]
    have h := norm_mixCharFun_sub_mul_I_le (F.map Z) hbj hbtc hbt2c hmj
    rw [hκc, hMc] at h
    rwa [slotCharFun_singleton F hZ b j c]
  have e0 : ‖slotCharFun F Z b {0} c - Complex.I * ((r * κ0 : ℝ) : ℂ)‖
      ≤ 3 / 2 * (r ^ 2 * M0) := hslotone 0 κ0 M0 hb0 hm0 hb0a hb0a2 hκ0.symm hM0.symm
  have e1 : ‖slotCharFun F Z b {1} c - Complex.I * ((r * κ1 : ℝ) : ℂ)‖
      ≤ 3 / 2 * (r ^ 2 * M1) := hslotone 1 κ1 M1 hb1 hm1 hb1a hb1a2 hκ1.symm hM1.symm
  -- the closed form of the assignment sum, with `r² N = 1` used to clear the prefactor
  have hw : ((r : ℝ) : ℂ) ^ 2 * (N : ℂ) = 1 := by
    have : ((r ^ 2 * (N : ℝ) : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [show r ^ 2 * (N : ℝ) = 1 by linarith [hNr]]
    push_cast at this
    linear_combination this
  have hid : multiCharFun (vecRootLaw F Z N) b a
      = slotCharFun F Z b Finset.univ c * φ ^ (N - 1)
        + ((N : ℂ) - 1) * (slotCharFun F Z b {0} c
            * (slotCharFun F Z b {1} c * φ ^ (N - 2))) := by
    rw [multiCharFun_vecRootLaw_two F hZ b hint a, ← hrdef, ← hcdef, ← hφdef]
    have hexpand : (((r : ℝ) : ℂ)) ^ 2 * ((N : ℂ) * (slotCharFun F Z b Finset.univ c * φ ^ (N - 1))
          + (N : ℂ) * ((N : ℂ) - 1) * (slotCharFun F Z b {0} c
              * (slotCharFun F Z b {1} c * φ ^ (N - 2))))
        = (((r : ℝ) : ℂ) ^ 2 * (N : ℂ)) * (slotCharFun F Z b Finset.univ c * φ ^ (N - 1))
          + (((r : ℝ) : ℂ) ^ 2 * (N : ℂ)) * (((N : ℂ) - 1) * (slotCharFun F Z b {0} c
              * (slotCharFun F Z b {1} c * φ ^ (N - 2)))) := by ring
    rw [hexpand, hw, one_mul, one_mul]
  -- the algebraic decomposition of the difference
  set s01 : ℂ := slotCharFun F Z b Finset.univ c with hs01
  set s0 : ℂ := slotCharFun F Z b {0} c with hs0
  set s1 : ℂ := slotCharFun F Z b {1} c with hs1
  set p0 : ℂ := Complex.I * ((r * κ0 : ℝ) : ℂ) with hp0
  set p1 : ℂ := Complex.I * ((r * κ1 : ℝ) : ℂ) with hp1
  have hp0n : ‖p0‖ = r * |κ0| := by
    rw [hp0, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hrpos]
  have hp1n : ‖p1‖ = r * |κ1| := by
    rw [hp1, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos hrpos]
  have hs0n : ‖s0‖ ≤ r * |κ0| + 3 / 2 * (r ^ 2 * M0) := by
    have hsplit : s0 = p0 + (s0 - p0) := by ring
    calc ‖s0‖ = ‖p0 + (s0 - p0)‖ := by rw [← hsplit]
      _ ≤ ‖p0‖ + ‖s0 - p0‖ := norm_add_le _ _
      _ ≤ r * |κ0| + 3 / 2 * (r ^ 2 * M0) := by rw [hp0n]; linarith [e0]
  have hp0p1 : p0 * p1 = -(((r ^ 2 * (κ0 * κ1) : ℝ)) : ℂ) := by
    rw [hp0, hp1]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hoffprod : ‖s0 * s1 - p0 * p1‖
      ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) := by
    have heq : s0 * s1 - p0 * p1 = s0 * (s1 - p1) + (s0 - p0) * p1 := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hp1n]
    have h1 : ‖s0‖ * ‖s1 - p1‖ ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1)) :=
      mul_le_mul hs0n e1 (norm_nonneg _) (by positivity)
    have h2 : ‖s0 - p0‖ * (r * |κ1|) ≤ 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) :=
      mul_le_mul_of_nonneg_right e0 (by positivity)
    linarith
  -- the multiplicity `N − 1` and the exact cancellation of the leading off-diagonal term
  have hmult : ((N : ℂ) - 1) * (p0 * p1) + ((κ0 * κ1 : ℝ) : ℂ)
      = ((r ^ 2 * (κ0 * κ1) : ℝ) : ℂ) := by
    have hcast : ((N : ℂ) - 1) = ((((N : ℝ) - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hp0p1, hcast, ← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_add,
      Complex.ofReal_inj]
    have hfin : ((N : ℝ) - 1) * (r ^ 2 * (κ0 * κ1)) = (κ0 * κ1) - r ^ 2 * (κ0 * κ1) := by
      linear_combination (κ0 * κ1) * hNr
    linarith [hfin]
  have hNm1 : ‖((N : ℂ) - 1)‖ = (N : ℝ) - 1 := by
    have hcast : ((N : ℂ) - 1) = ((((N : ℝ) - 1 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ) - 1)]
  have hT2 : ‖((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)‖
      ≤ ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1| := by
    have heq : ((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)
        = ((N : ℂ) - 1) * (s0 * s1 - p0 * p1)
          + (((N : ℂ) - 1) * (p0 * p1) + ((κ0 * κ1 : ℝ) : ℂ)) := by ring
    rw [heq, hmult]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hNm1, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ r ^ 2)]
    have := mul_le_mul_of_nonneg_left hoffprod (by linarith : (0:ℝ) ≤ (N:ℝ) - 1)
    linarith
  -- assembly
  have hsplit : multiCharFun (vecRootLaw F Z N) b a
      - ((κ01 : ℂ) * φ ^ (N - 1) - ((κ0 * κ1 : ℝ) : ℂ) * φ ^ (N - 2))
      = (s01 - (κ01 : ℂ)) * φ ^ (N - 1)
        + (((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)) * φ ^ (N - 2) := by
    rw [hid]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have hb1' : ‖(s01 - (κ01 : ℂ))‖ * ‖φ ^ (N - 1)‖ ≤ (r * M01) * ‖φ‖ ^ (N - 2) :=
    mul_le_mul hdiag (hφp _ (by omega)) (norm_nonneg _) (by positivity)
  have hnn2 : (0 : ℝ) ≤ ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0))
        * (3 / 2 * (r ^ 2 * M1)) + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1| := by
    have hA : (0 : ℝ) ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) := by positivity
    have hB : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
    have hC : (0 : ℝ) ≤ r ^ 2 * |κ0 * κ1| := by positivity
    nlinarith [mul_nonneg hB hA]
  have hb2' : ‖((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)‖ * ‖φ ^ (N - 2)‖
      ≤ (((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1|) * ‖φ‖ ^ (N - 2) :=
    mul_le_mul hT2 (hφp _ le_rfl) (norm_nonneg _) hnn2
  -- the arithmetic: `N − 1 ≤ N` and `N r² = 1` turn `N r³` into `r` and `N r⁴` into `r²`
  have hmid : ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|))
      ≤ 3 / 2 * r * |κ0| * M1 + 9 / 4 * r ^ 2 * M0 * M1 + 3 / 2 * r * M0 * |κ1| := by
    have hpos : (0 : ℝ) ≤ (r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
        + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|) := by positivity
    have hle : ((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|))
        ≤ (N : ℝ) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) :=
      mul_le_mul_of_nonneg_right (by linarith) hpos
    have heq : (N : ℝ) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|))
        = 3 / 2 * r * |κ0| * M1 + 9 / 4 * r ^ 2 * M0 * M1 + 3 / 2 * r * M0 * |κ1| := by
      linear_combination (3 / 2 * r * |κ0| * M1 + 9 / 4 * r ^ 2 * M0 * M1
        + 3 / 2 * r * M0 * |κ1|) * hNr
    linarith [hle, heq.le, heq.ge]
  have hplain : (r * M01)
      + (((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
          + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1|)
      ≤ r * multiTwoRemConst (F.map Z) b a := by
    rw [multiTwoRemConst, ← hκ0, ← hκ1, ← hM0, ← hM1, ← hM01]
    have habs : |κ0 * κ1| = |κ0| * |κ1| := abs_mul _ _
    have h1 : r ^ 2 * |κ0 * κ1| ≤ r * (|κ0| * |κ1|) := by
      rw [habs]
      exact mul_le_mul_of_nonneg_right hr2le (by positivity)
    have h2 : 9 / 4 * r ^ 2 * M0 * M1 ≤ 9 / 4 * (r * (M0 * M1)) := by
      nlinarith [mul_nonneg (sub_nonneg.2 hr2le) (mul_nonneg hM0nn hM1nn)]
    linarith [hmid, h1, h2]
  have hsum : ‖(s01 - (κ01 : ℂ))‖ * ‖φ ^ (N - 1)‖
      + ‖((N : ℂ) - 1) * (s0 * s1) + ((κ0 * κ1 : ℝ) : ℂ)‖ * ‖φ ^ (N - 2)‖
      ≤ ((r * M01)
          + (((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
              + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1|)) * ‖φ‖ ^ (N - 2) := by
    have hexp : ((r * M01)
        + (((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
            + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1|)) * ‖φ‖ ^ (N - 2)
        = (r * M01) * ‖φ‖ ^ (N - 2)
          + (((N : ℝ) - 1) * ((r * |κ0| + 3 / 2 * (r ^ 2 * M0)) * (3 / 2 * (r ^ 2 * M1))
              + 3 / 2 * (r ^ 2 * M0) * (r * |κ1|)) + r ^ 2 * |κ0 * κ1|) * ‖φ‖ ^ (N - 2) := by
      ring
    rw [hexp]
    linarith [hb1', hb2']
  refine hsum.trans ?_
  exact mul_le_mul_of_nonneg_right hplain hφP

end MultiTwoEstimate


/-! ## One-factor bookkeeping: from `φ^{n−1}` to `φ^n`

`norm_mixCharFun_vecRootLaw_sub_le` compares the mixed characteristic function of a vector
root with `iκ φ(n^{-1/2}a)^{n−1}` — an `(n−1)`-st power, while `charFun_vecRootLaw` and the
damped expansion `norm_charFun_smul_pow_sub_edgeworth_le` both speak about the `n`-th power
`φ(n^{-1/2}a)^n = φ_{ρ_n}(a)`. This section supplies the missing factor.

The estimate is elementary and costs `O(n^{-1})`, i.e. it is invisible at the accuracy of a
one-term expansion. Indeed `z^{n−1} − z^n = z^{n−1}(1 − z)`, and `‖z‖ ≤ 1` for a characteristic
function, so the whole difference is bounded by `‖1 − φ(c)‖` at the *rescaled* argument
`c = n^{-1/2} • a`; for a law centred in the direction `a` this is
`‖∫ (e^{i⟪x,c⟫} − 1 − i⟪x,c⟫)‖ ≤ (3/2)∫⟪x,c⟫² = (3/2) v(a)/n`.

The centring is what makes this `O(n^{-1})` rather than `O(n^{-1/2})`: without it the linear
term survives and the bound is only `‖∫⟪x,c⟫‖ = O(n^{-1/2})`, which would swamp the
`n^{-1/2}` coefficient the studentized expansion is trying to produce. -/

section OneFactor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **A characteristic function is quadratically close to `1` in a centred direction.**
`‖φ_μ(t) − 1‖ ≤ (3/2)∫⟪x,t⟫²` whenever `∫⟪x,t⟫ = 0`.

This is `norm_cexp_sub_one_sub_mul_I_le` integrated against `μ`, with the centring used to
delete the linear term of the expansion of `e^{i⟪x,t⟫}`. -/
theorem norm_charFun_sub_one_le (μ : Measure E) [IsProbabilityMeasure μ] {t : E}
    (hint1 : Integrable (fun x : E => (⟪x, t⟫ : ℝ)) μ)
    (hint2 : Integrable (fun x : E => (⟪x, t⟫ : ℝ) ^ 2) μ)
    (hmean : ∫ x, (⟪x, t⟫ : ℝ) ∂μ = 0) :
    ‖charFun μ t - 1‖ ≤ 3 / 2 * ∫ x, (⟪x, t⟫ : ℝ) ^ 2 ∂μ := by
  have htm : Measurable fun x : E => (⟪x, t⟫ : ℝ) := measurable_inner_right t
  have hA : Integrable (fun x : E => Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I)) μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  have hC : Integrable (fun x : E => Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) μ :=
    hint1.ofReal.const_mul Complex.I
  have hcf : ∫ x, Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ = charFun μ t := by
    rw [charFun_apply]
  have hIC : ∫ x, Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) ∂μ = 0 := by
    have h1 : ∫ x, Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) ∂μ
        = Complex.I * ∫ x, ((⟪x, t⟫ : ℝ) : ℂ) ∂μ := integral_const_mul _ _
    rw [h1, integral_complex_ofReal, hmean, Complex.ofReal_zero, mul_zero]
  have hkey : ∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
        - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ = charFun μ t - 1 := by
    have hs1 : ∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
          - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) ∂μ
        = (∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1) ∂μ)
          - ∫ x, Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) ∂μ :=
      integral_sub (hA.sub (integrable_const 1)) hC
    have hs2 : ∫ x, (Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1) ∂μ
        = (∫ x, Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) ∂μ) - ∫ _x : E, (1 : ℂ) ∂μ :=
      integral_sub hA (integrable_const 1)
    rw [hs1, hs2, hIC, hcf]
    simp
  rw [← hkey]
  have hdom : Integrable (fun x : E => 3 / 2 * (⟪x, t⟫ : ℝ) ^ 2) μ := hint2.const_mul (3 / 2)
  have hpt : ∀ x : E, ‖Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1
      - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)‖ ≤ 3 / 2 * (⟪x, t⟫ : ℝ) ^ 2 := by
    intro x
    have hcomm : Complex.exp ((⟪x, t⟫ : ℝ) * Complex.I) - 1 - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)
        = Complex.exp (Complex.I * ((⟪x, t⟫ : ℝ) : ℂ)) - 1
          - Complex.I * ((⟪x, t⟫ : ℝ) : ℂ) := by
      rw [mul_comm ((⟪x, t⟫ : ℝ) : ℂ) Complex.I]
    rw [hcomm]
    have h := norm_cexp_sub_one_sub_mul_I_le (⟪x, t⟫ : ℝ)
    linarith
  refine (norm_integral_le_of_norm_le hdom (Filter.Eventually.of_forall hpt)).trans ?_
  exact le_of_eq (integral_const_mul _ _)

/-- Dropping one factor from a power of a number of modulus at most `1` costs `‖1 − z‖`. -/
lemma norm_pow_sub_pow_succ_le {z : ℂ} (hz : ‖z‖ ≤ 1) (m : ℕ) :
    ‖z ^ m - z ^ (m + 1)‖ ≤ ‖1 - z‖ := by
  have he : z ^ m - z ^ (m + 1) = z ^ m * (1 - z) := by ring
  rw [he, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) hz

/-- **The one-factor comparison for the characteristic function of a vector root.**

`‖φ_{F∘Z⁻¹}(n^{-1/2}a)^{n−1} − φ_{ρ_n}(a)‖ ≤ (3/2) v/n`, with `v = ∫⟪x,a⟫²` the directional
variance, for a law centred in the direction `a`.

This is the bookkeeping that lets the `(n−1)`-st power produced by the mixed expansion
(M1)(b) be replaced by the characteristic function of the vector root itself, to which the
damped expansion `norm_charFun_vecRootLaw_sub_edgeworth_le` applies verbatim. -/
theorem norm_charFun_pow_sub_charFun_vecRootLaw_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {a : E} (m : ℕ)
    (ha : Integrable (fun x : E => (⟪x, a⟫ : ℝ)) (F.map Z))
    (ha2 : Integrable (fun x : E => (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hmean : ∫ x, (⟪x, a⟫ : ℝ) ∂(F.map Z) = 0) :
    ‖charFun (F.map Z) ((Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a) ^ m
        - charFun (vecRootLaw F Z (m + 1)) a‖
      ≤ 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1)) := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hNpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  set r : ℝ := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  have hc1 : ∀ x : E, (⟪x, c⟫ : ℝ) = r * (⟪x, a⟫ : ℝ) := fun x => by
    rw [hcdef, real_inner_smul_right]
  have hrsq : r ^ 2 = (((m : ℝ) + 1))⁻¹ := by
    rw [hrdef, inv_pow, Real.sq_sqrt hNpos.le]
    push_cast
    ring
  -- the directional data in the rescaled direction
  have hac : Integrable (fun x : E => (⟪x, c⟫ : ℝ)) (F.map Z) := by
    have h1 : (fun x : E => (⟪x, c⟫ : ℝ)) = fun x : E => r * (⟪x, a⟫ : ℝ) := by
      funext x; exact hc1 x
    rw [h1]
    exact ha.const_mul r
  have hac2 : Integrable (fun x : E => (⟪x, c⟫ : ℝ) ^ 2) (F.map Z) := by
    have h1 : (fun x : E => (⟪x, c⟫ : ℝ) ^ 2) = fun x : E => r ^ 2 * (⟪x, a⟫ : ℝ) ^ 2 := by
      funext x; rw [hc1 x]; ring
    rw [h1]
    exact ha2.const_mul (r ^ 2)
  have hmeanc : ∫ x, (⟪x, c⟫ : ℝ) ∂(F.map Z) = 0 := by
    have h1 : ∀ x : E, (⟪x, c⟫ : ℝ) = r * (⟪x, a⟫ : ℝ) := hc1
    simp_rw [h1]
    rw [integral_const_mul, hmean, mul_zero]
  have hvarc : ∫ x, (⟪x, c⟫ : ℝ) ^ 2 ∂(F.map Z)
      = r ^ 2 * ∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z) := by
    have h1 : ∀ x : E, (⟪x, c⟫ : ℝ) ^ 2 = r ^ 2 * (⟪x, a⟫ : ℝ) ^ 2 := fun x => by
      rw [hc1 x]; ring
    simp_rw [h1]
    exact integral_const_mul _ _
  -- the two estimates
  have hone : ‖charFun (F.map Z) c - 1‖
      ≤ 3 / 2 * (r ^ 2 * ∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) := by
    have h := norm_charFun_sub_one_le (F.map Z) hac hac2 hmeanc
    rwa [hvarc] at h
  have hpow := norm_pow_sub_pow_succ_le (norm_charFun_le_one (μ := F.map Z) c) m
  have hroot : charFun (vecRootLaw F Z (m + 1)) a = charFun (F.map Z) c ^ (m + 1) := by
    rw [charFun_vecRootLaw F hZ, ← hrdef, ← hcdef]
  rw [hroot]
  calc ‖charFun (F.map Z) c ^ m - charFun (F.map Z) c ^ (m + 1)‖
      ≤ ‖1 - charFun (F.map Z) c‖ := hpow
    _ = ‖charFun (F.map Z) c - 1‖ := norm_sub_rev _ _
    _ ≤ 3 / 2 * (r ^ 2 * ∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) := hone
    _ = 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1)) := by
        rw [hrsq]; ring

/-- **(M1)(b), with the one-factor bookkeeping done: the mixed characteristic function of a
vector root against the characteristic function of that same root.**

`‖mix_{ρ_n}(b,a) − i κ φ_{ρ_n}(a)‖ ≤ 3M/(2√n) + (3/2)|κ| v/n`, with `κ = ∫⟪x,b⟫⟪x,a⟫`,
`M = ∫|⟪x,b⟫|⟪x,a⟫²` and `v = ∫⟪x,a⟫²`, for a law centred in the directions `a` and `b`.

This is the form the studentized route consumes: the right-hand factor is now
`φ_{ρ_n}(a) = charFun (vecRootLaw F Z n) a` itself, so the damped expansion
`norm_charFun_vecRootLaw_sub_edgeworth_le` — which estimates exactly that quantity — applies to
it verbatim, and the two expansions can be added. The extra cost `(3/2)|κ|v/n` is `O(n^{-1})`,
invisible at the accuracy of a one-term expansion. -/
theorem norm_mixCharFun_vecRootLaw_sub_charFun_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {a b : E} (m : ℕ)
    (hb : Integrable (fun x : E => (⟪x, b⟫ : ℝ)) (F.map Z))
    (ha : Integrable (fun x : E => (⟪x, a⟫ : ℝ)) (F.map Z))
    (ha2 : Integrable (fun x : E => (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hba : Integrable (fun x : E => (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ)) (F.map Z))
    (hba2 : Integrable (fun x : E => |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2) (F.map Z))
    (hmeanb : ∫ x, (⟪x, b⟫ : ℝ) ∂(F.map Z) = 0)
    (hmeana : ∫ x, (⟪x, a⟫ : ℝ) ∂(F.map Z) = 0) :
    ‖mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * ((∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) : ℝ) : ℂ)
            * charFun (vecRootLaw F Z (m + 1)) a‖
      ≤ 3 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))
            * ∫ x, |(⟪x, b⟫ : ℝ)| * (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)
          + 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1))
              * |∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z)| := by
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  set κ : ℝ := ∫ x, (⟪x, b⟫ : ℝ) * (⟪x, a⟫ : ℝ) ∂(F.map Z) with hκdef
  set c : E := (Real.sqrt ((m + 1 : ℕ) : ℝ))⁻¹ • a with hcdef
  have h1 := norm_mixCharFun_vecRootLaw_sub_le F hZ m hb hba hba2 hmeanb
  rw [← hκdef, ← hcdef] at h1
  have h2 := norm_charFun_pow_sub_charFun_vecRootLaw_le F hZ m ha ha2 hmeana
  rw [← hcdef] at h2
  have hsplit : mixCharFun (vecRootLaw F Z (m + 1)) b a
        - Complex.I * (κ : ℂ) * charFun (vecRootLaw F Z (m + 1)) a
      = (mixCharFun (vecRootLaw F Z (m + 1)) b a
          - Complex.I * (κ : ℂ) * charFun (F.map Z) c ^ m)
        + Complex.I * (κ : ℂ)
            * (charFun (F.map Z) c ^ m - charFun (vecRootLaw F Z (m + 1)) a) := by
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hsecond : ‖Complex.I * (κ : ℂ)
      * (charFun (F.map Z) c ^ m - charFun (vecRootLaw F Z (m + 1)) a)‖
      ≤ 3 / 2 * ((∫ x, (⟪x, a⟫ : ℝ) ^ 2 ∂(F.map Z)) / ((m : ℝ) + 1)) * |κ| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  linarith

/-- **The Cramér tail transfers to a vector root for free.**

If `‖φ_{F∘Z⁻¹}(t)‖ ≤ c` on the whole region `ε ≤ ‖t‖`, then `‖φ_{ρ_n}(t)‖ ≤ cⁿ` on the region
`ε√n ≤ ‖t‖`. This is `charFun_vecRootLaw` and nothing else: the law of the vector root *is* a
normalised sum, so its characteristic function *is* an `n`-th power, and the rescaling by
`n^{-1/2}` converts the region `ε ≤ ‖·‖` into `ε√n ≤ ‖·‖`.

It is the exact analogue, for the bivariate law, of what `edgeworthGap_tail_le` does for the
centred root, and it shows that **no conditioning device is needed at the level of `ρ_n`**: the
transfer that wave 13 attributed to Hall's trick of conditioning on `n − k` of the coordinates
is free here. Conditioning would be needed only for the law of a *nonlinear* functional of the
root, which the (M1)(b) route never forms. -/
theorem norm_charFun_vecRootLaw_le_pow (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {c ε : ℝ} (hε : 0 < ε)
    (hc : ∀ t : E, ε ≤ ‖t‖ → ‖charFun (F.map Z) t‖ ≤ c)
    {n : ℕ} (hn : 0 < n) {t : E} (ht : ε * Real.sqrt (n : ℝ) ≤ ‖t‖) :
    ‖charFun (vecRootLaw F Z n) t‖ ≤ c ^ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hscale : ‖((Real.sqrt (n : ℝ))⁻¹ : ℝ) • t‖ = ‖t‖ / Real.sqrt (n : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hsn, inv_mul_eq_div]
  have hge : ε ≤ ‖((Real.sqrt (n : ℝ))⁻¹ : ℝ) • t‖ := by
    rw [hscale, le_div_iff₀ hsn]
    linarith
  rw [charFun_vecRootLaw F hZ, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hc _ hge) n

end OneFactor

/-! ## Bounded summands: the root has bounded support, so every moment of it is finite

The multilinear weights of the studentized surrogate's transform are moments of the *root*, and
under a finite fourth moment of the sampling law two of them are **infinite** — see the wave-25
note on `edgeworth_studentized_uniform` in `Bootstrap/Edgeworth.lean`. The classical repair is
to truncate the summands before expanding. What truncation buys, at the level of this file, is
completely elementary and is recorded here: if `‖Z‖ ≤ K` pointwise then the root
`n^{-1/2}∑Z(yᵢ)` is bounded by `√n·K` pointwise, so its law is carried by a ball and *every*
polynomial in its coordinates is integrable — no moment hypothesis on `F` survives at all.

The price of the truncation is a change of law, and that is paid on the other side, by the
union bound `measure_pi_exists_coord_mem_le` of `Bootstrap/Edgeworth.lean`. The two are
complementary and neither is `measure_pi_truncated_sum_le_exp`, which bounds the tail of a
truncated *sum*. -/

section BoundedRoot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- A bounded measurable function is integrable against a finite measure. This is the only
integrability statement the truncated route needs: after truncation every weight is bounded on
the support of the root's law. -/
lemma integrable_of_ae_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (h : ∀ᵐ x ∂μ, |f x| ≤ C) : Integrable f μ := by
  refine Integrable.mono' (integrable_const C) hf ?_
  filter_upwards [h] with x hx
  rwa [Real.norm_eq_abs]

/-- **A bounded summand gives a root with bounded support.** If `‖Z x‖ ≤ K` for every `x`, the
law of the root `n^{-1/2}∑_{i<n} Z(yᵢ)` is carried by the closed ball of radius `√n·K`.

The bound is pointwise on the product space and is transported by `ae_map_iff`; no independence
and no moment of `F` is used. -/
theorem ae_norm_vecRootLaw_le (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {K : ℝ} (hK : ∀ x, ‖Z x‖ ≤ K) (n : ℕ) :
    ∀ᵐ w ∂(vecRootLaw F Z n), ‖w‖ ≤ Real.sqrt (n : ℝ) * K := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (norm_nonneg _) (hK 0)
  have hmeas : MeasurableSet {w : E | ‖w‖ ≤ Real.sqrt (n : ℝ) * K} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [vecRootLaw, ae_map_iff (measurable_vecRoot hZ n).aemeasurable hmeas]
  refine Filter.Eventually.of_forall fun y => ?_
  have hsum : ‖∑ i, Z (y i)‖ ≤ (n : ℝ) * K := by
    calc ‖∑ i, Z (y i)‖ ≤ ∑ _i : Fin n, K :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hK (y i))
      _ = (n : ℝ) * K := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsn : (0 : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
  have hkey : (Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) * K) ≤ Real.sqrt (n : ℝ) * K := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hsq : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
      have hid : (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
        have h2 : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) :=
          Real.mul_self_sqrt hn0.le
        field_simp
        linarith [h2]
      have heq : (Real.sqrt (n : ℝ))⁻¹ * ((n : ℝ) * K) = Real.sqrt (n : ℝ) * K := by
        linear_combination K * hid
      exact heq.le
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsn]
  exact le_trans (mul_le_mul_of_nonneg_left hsum hsn) hkey

end BoundedRoot

/-! ## The `k ≥ 3` estimate at `O(1)`: the image count, not the partition lattice

The `k = 2` estimate `norm_multiCharFun_vecRootLaw_two_sub_le` identifies the *limit* of
`multi_{ρ_N}(b,a)` to accuracy `O(N^{-1/2})`, and for that the exact split of the assignment sum
into its diagonal and off-diagonal blocks is unavoidable: the two blocks are of the same order
and of opposite sign. The wave-25 note of `Bootstrap/Edgeworth.lean` records the `k = 3, 4`
residue as "the same thing with the partition lattice of `Fin k` in place of a single diagonal,
and the counting is the only new work".

**That is more than is needed, and the re-derivation below replaces it.** At `k = 3, 4` the
consumer (`norm_integral_cexp_deltaSurrogate_sub_graded_le`, whose coefficients `c₃`, `c₄`, `c₅`
are `O(n⁻¹)`) asks only for an `O(1)` *bound*, not for a limit. A bound needs no cancellation
*between* partitions — only the cancellation *inside* a singleton slot, which is the centring. So
the assignment sum can be estimated term by term, and the partition lattice never appears:

* each fibre `T = σ⁻¹(i)` contributes a factor `slot_T(c)` carrying `r^{|T|}` of the prefactor
  `r^k = ∏_i r^{|σ⁻¹(i)|}`, and **each such factor is at most `Q/N`, whatever `|T|` is**:
  `|T| = 0` gives `‖φ(c)‖ ≤ 1`; `|T| = 1` gives `r·(rQ) = Q/N` *by the centring*; `|T| = j ≥ 2`
  gives `r^j·Q(√N)^{j-2} = Q/N`, since a slot of `j` weights is allowed to grow like
  `N^{(j-2)/2}` — exactly what the truncated law delivers (`E[ξ̃²η̃²] ≍ N` at `τ = √n`, and
  `r⁴·N·N = 1`);
* hence the `σ`-summand is at most `(Q/N)^{m(σ)}` with `m(σ) = |image σ|`, and the whole estimate
  reduces to the elementary count `∑_{σ : Fin k → Fin N} (Q/N)^{|image σ|} ≤ (k+1)k^kQ^k`
  (`sum_div_pow_card_image_le`), whose proof is one containment: a `σ` with `|image σ| = m` is
  determined by a subset of size `m` (at most `N^m` of them, `Nat.choose_le_pow`) and a map into
  it (at most `m^k`).

The graded hypothesis `hQ2` is the whole content: a single uniform bound `Q` on every slot moment
would give `Q^k` with `Q ≍ N` and is useless, whereas the *graded* allowance
`Q·(√N)^{|T|-2}` is exactly what makes every fibre factor `Q/N`. This is the same phenomenon as
the grading of the envelope in `r` (wave 25, `surrogateRemGraded`), one level up.

The estimate applies verbatim at `k = 2` (with a worse constant than
`norm_multiCharFun_vecRootLaw_two_sub_le`, and without the limit), at `k = 1` and at `k = 0`. -/

section MultiBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **The assignment count.** `∑_{σ : Fin k → Fin N} y^{|image σ|} ≤ (k+1)k^kQ^k` for `y = Q/N`
and `1 ≤ Q`, uniformly in `N`.

This is the entire combinatorial content of the `O(1)` multilinear estimate. Grouping the `N^k`
assignments by the cardinality `m` of their image, a `σ` with `|image σ| = m` lies in the set of
maps into some fixed `m`-element subset of `Fin N`; there are at most `N^m` such subsets
(`Nat.choose_le_pow`) and `m^k` such maps, and the weight `(Q/N)^m` cancels the `N^m` exactly. -/
lemma sum_div_pow_card_image_le {k N : ℕ} (hN : 1 ≤ N) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ σ : Fin k → Fin N, (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card
      ≤ ((k : ℝ) + 1) * (k : ℝ) ^ k * Q ^ k := by
  classical
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (Fin k → Fin N)),
      (Finset.image σ Finset.univ).card ∈ Finset.range (k + 1) := by
    intro σ _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc (Finset.image σ Finset.univ).card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_image_le
      _ = k := by simp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      (∑ σ ∈ Finset.univ.filter
          (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m),
        (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card)
        ≤ (k : ℝ) ^ k * Q ^ k := by
    intro m hm
    have hmk : m ≤ k := by
      rw [Finset.mem_range, Nat.lt_succ_iff] at hm; exact hm
    -- the summand is constant on the fibre
    have hconst : (∑ σ ∈ Finset.univ.filter
        (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m),
        (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card)
        = ((Finset.univ.filter
            (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m)).card : ℝ)
          * (Q / (N : ℝ)) ^ m := by
      rw [Finset.sum_congr rfl (fun σ hσ => by
        rw [(Finset.mem_filter.1 hσ).2]), Finset.sum_const, nsmul_eq_mul]
    -- the fibre is contained in a union of `N.choose m` boxes, each of size `m ^ k`
    have hcard : (Finset.univ.filter
        (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m)).card
        ≤ N ^ m * m ^ k := by
      have hsub : (Finset.univ.filter
          (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m))
          ⊆ ((Finset.univ : Finset (Fin N)).powersetCard m).biUnion
              (fun S : Finset (Fin N) => Fintype.piFinset (fun _ : Fin k => S)) := by
        intro σ hσ
        rw [Finset.mem_filter] at hσ
        refine Finset.mem_biUnion.2 ⟨Finset.image σ Finset.univ, ?_, ?_⟩
        · exact Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hσ.2⟩
        · exact Fintype.mem_piFinset.2 fun l => Finset.mem_image_of_mem σ (Finset.mem_univ l)
      have hbox : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
          (Fintype.piFinset (fun _ : Fin k => S)).card = m ^ k := by
        intro S hS
        rw [Fintype.card_piFinset_const, (Finset.mem_powersetCard.1 hS).2]
      calc (Finset.univ.filter
              (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m)).card
          ≤ (((Finset.univ : Finset (Fin N)).powersetCard m).biUnion
              (fun S : Finset (Fin N) => Fintype.piFinset (fun _ : Fin k => S))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard m,
              (Fintype.piFinset (fun _ : Fin k => S)).card := Finset.card_biUnion_le
        _ = ∑ _S ∈ (Finset.univ : Finset (Fin N)).powersetCard m, m ^ k :=
            Finset.sum_congr rfl hbox
        _ = ((Finset.univ : Finset (Fin N)).powersetCard m).card * m ^ k := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ N ^ m * m ^ k := by
            have : ((Finset.univ : Finset (Fin N)).powersetCard m).card = N.choose m := by
              rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
            rw [this]
            exact Nat.mul_le_mul_right _ (Nat.choose_le_pow N m)
    have hcardR : ((Finset.univ.filter
        (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m)).card : ℝ)
        ≤ (N : ℝ) ^ m * (m : ℝ) ^ k := by
      exact_mod_cast hcard
    have hpow : ((N : ℝ) ^ m * (m : ℝ) ^ k) * (Q / (N : ℝ)) ^ m = (m : ℝ) ^ k * Q ^ m := by
      rw [div_pow]
      field_simp
    calc (∑ σ ∈ Finset.univ.filter
            (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m),
            (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card)
        = ((Finset.univ.filter
            (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m)).card : ℝ)
          * (Q / (N : ℝ)) ^ m := hconst
      _ ≤ ((N : ℝ) ^ m * (m : ℝ) ^ k) * (Q / (N : ℝ)) ^ m := by
          gcongr
      _ = (m : ℝ) ^ k * Q ^ m := hpow
      _ ≤ (k : ℝ) ^ k * Q ^ k := by
          gcongr
  calc (∑ m ∈ Finset.range (k + 1), ∑ σ ∈ Finset.univ.filter
          (fun σ : Fin k → Fin N => (Finset.image σ Finset.univ).card = m),
          (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card)
      ≤ ∑ _m ∈ Finset.range (k + 1), (k : ℝ) ^ k * Q ^ k := Finset.sum_le_sum hterm
    _ = ((k : ℝ) + 1) * (k : ℝ) ^ k * Q ^ k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

set_option maxHeartbeats 800000 in
-- The assembly carries a per-fibre trichotomy through a product over `Fin N` and a sum over the
-- `N^k` assignments; the default heartbeat budget is not enough.
/-- **The `O(1)` estimate for the multilinearly weighted characteristic function of a vector
root, at every `k`.**

`‖multi_{ρ_N}(b, a)‖ ≤ (k+1)k^k Q^k` for a law centred in every slot direction, under the
**graded** moment allowance

* `∫|⟪x,b_l⟫||⟪x,a⟫| ≤ Q` for each single slot (used together with the centring), and
* `∫∏_{l∈T}|⟪x,b_l⟫| ≤ Q·(√N)^{|T|-2}` for every `T` with `|T| ≥ 2`.

This is residue (i) of the wave-25 note of `Bootstrap/Edgeworth.lean` at `k = 3, 4` — and it is
uniform in `N`, in `a` and in `k`. The `k = 2` case is subsumed, though
`norm_multiCharFun_vecRootLaw_two_sub_le` is sharper there (it identifies the limit to
`O(N^{-1/2})`, which the surrogate's coefficient `c₂` needs; `c₃`, `c₄`, `c₅` are `O(n⁻¹)` and
need only this).

The grading of `hQ2` in `|T|` is the whole content, and it is forced: for the studentized pair
truncated at `τ = √n` the top slot moment `E[ξ̃²η̃²]` is of order `N`, so a *uniform* allowance `Q`
would have to be taken of order `N` and `Q^k` would be useless, whereas the graded allowance
makes every fibre factor `r^{|T|}·‖slot_T‖` equal to `Q/N` regardless of `|T|`. -/
theorem norm_multiCharFun_vecRootLaw_le (F : Measure ℝ) [IsProbabilityMeasure F] {Z : ℝ → E}
    (hZ : Measurable Z) {k N : ℕ} (hN : 1 ≤ N) (b : Fin k → E) (a : E) {Q : ℝ} (hQ : 1 ≤ Q)
    (hint : ∀ T : Finset (Fin k),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (hbl : ∀ l : Fin k, Integrable (fun x : E => (⟪x, b l⟫ : ℝ)) (F.map Z))
    (hcent : ∀ l : Fin k, (∫ x, (⟪x, b l⟫ : ℝ) ∂(F.map Z)) = 0)
    (hbla : ∀ l : Fin k,
      Integrable (fun x : E => |(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) (F.map Z))
    (hQ1 : ∀ l : Fin k, (∫ x, |(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)| ∂(F.map Z)) ≤ Q)
    (hQ2 : ∀ T : Finset (Fin k), 2 ≤ T.card →
      (∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z))
        ≤ Q * Real.sqrt (N : ℝ) ^ (T.card - 2)) :
    ‖multiCharFun (vecRootLaw F Z N) b a‖ ≤ ((k : ℝ) + 1) * (k : ℝ) ^ k * Q ^ k := by
  classical
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsq : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN0
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  rw [multiCharFun_vecRootLaw F hZ b hint a]
  set r : ℝ := (Real.sqrt (N : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  have hrpos : 0 < r := by rw [hrdef]; exact inv_pos.2 hsq
  have hrsq : r * Real.sqrt (N : ℝ) = 1 := by
    rw [hrdef]; field_simp
  have hr2 : r ^ 2 = ((N : ℝ))⁻¹ := by rw [hrdef, inv_pow, Real.sq_sqrt hN0.le]
  have hca : ∀ w : E, (⟪w, c⟫ : ℝ) = r * (⟪w, a⟫ : ℝ) := fun w => by
    rw [hcdef, real_inner_smul_right]
  -- the per-fibre bound: **every** fibre factor is at most `Q/N`
  have hslot : ∀ T : Finset (Fin k),
      r ^ T.card * ‖slotCharFun F Z b T c‖ ≤ (if T = ∅ then 1 else Q / (N : ℝ)) := by
    intro T
    rcases eq_or_ne T ∅ with rfl | hTne
    · rw [if_pos rfl, Finset.card_empty, pow_zero, one_mul, slotCharFun_empty F hZ b c]
      exact norm_charFun_le_one c
    rw [if_neg hTne]
    have hpos : 1 ≤ T.card := Finset.card_pos.2 (Finset.nonempty_of_ne_empty hTne)
    rcases eq_or_lt_of_le hpos with h1 | h2
    · -- a single slot: the centring gives `‖slot‖ ≤ rQ`, and `r·rQ = Q/N`
      obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h1.symm
      have hgm : Measurable fun w : E => (⟪w, b l⟫ : ℝ) := measurable_inner_right (b l)
      have habs : ∀ x : E, |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|
          = r * (|(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := fun x => by
        rw [hca x, abs_mul r ((⟪x, a⟫ : ℝ)), abs_of_pos hrpos]; ring
      have hgt : Integrable (fun x : E => |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|) (F.map Z) := by
        have hEq : (fun x : E => |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|)
            = fun x : E => r * (|(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := funext habs
        rw [hEq]; exact (hbla l).const_mul r
      have hmom : (∫ x, |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)| ∂(F.map Z))
          = r * ∫ x, |(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)| ∂(F.map Z) := by
        simp_rw [habs]
        exact integral_const_mul _ _
      have hbound := norm_integral_ofReal_mul_cexp_sub_le (F.map Z) hgm (hbl l) hgt
      rw [hcent l] at hbound
      simp only [Complex.ofReal_zero, sub_zero] at hbound
      rw [hmom] at hbound
      have hslot1 : ‖slotCharFun F Z b {l} c‖ ≤ r * Q := by
        rw [slotCharFun_singleton F hZ b l c, mixCharFun]
        exact hbound.trans (mul_le_mul_of_nonneg_left (hQ1 l) hrpos.le)
      rw [Finset.card_singleton, pow_one]
      calc r * ‖slotCharFun F Z b {l} c‖ ≤ r * (r * Q) :=
            mul_le_mul_of_nonneg_left hslot1 hrpos.le
        _ = Q / (N : ℝ) := by
            rw [show r * (r * Q) = r ^ 2 * Q by ring, hr2]
            field_simp
    · -- a fibre of size `j ≥ 2`: the graded allowance gives `r^j·Q(√N)^{j-2} = Q/N`
      have hnorm : ‖slotCharFun F Z b T c‖
          ≤ ∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z) := by
        have hmap : (∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z))
            = ∫ x, ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)| ∂F := by
          rw [integral_map hZ.aemeasurable]
          exact (Finset.measurable_prod _ fun l _ =>
            (measurable_inner_right (b l)).abs).aestronglyMeasurable
        rw [hmap, slotCharFun]
        refine norm_integral_le_of_norm_le (hint T) (Filter.Eventually.of_forall fun x => ?_)
        have hx : ‖(∏ l ∈ T, ((⟪Z x, b l⟫ : ℝ) : ℂ))
            * Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I)‖
            = ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)| := by
          rw [norm_mul, norm_prod]
          simp [Complex.norm_exp]
        exact hx.le
      obtain ⟨d, hd⟩ : ∃ d, T.card = d + 2 := ⟨T.card - 2, by omega⟩
      have harith : r ^ (d + 2) * (Q * Real.sqrt (N : ℝ) ^ d) = Q / (N : ℝ) := by
        have hstep : r ^ (d + 2) * Real.sqrt (N : ℝ) ^ d = ((N : ℝ))⁻¹ := by
          calc r ^ (d + 2) * Real.sqrt (N : ℝ) ^ d
              = (r * Real.sqrt (N : ℝ)) ^ d * r ^ 2 := by rw [mul_pow]; ring
            _ = r ^ 2 := by rw [hrsq, one_pow, one_mul]
            _ = ((N : ℝ))⁻¹ := hr2
        calc r ^ (d + 2) * (Q * Real.sqrt (N : ℝ) ^ d)
            = (r ^ (d + 2) * Real.sqrt (N : ℝ) ^ d) * Q := by ring
          _ = ((N : ℝ))⁻¹ * Q := by rw [hstep]
          _ = Q / (N : ℝ) := by field_simp
      have hQ2' : (∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z))
          ≤ Q * Real.sqrt (N : ℝ) ^ d := by
        have := hQ2 T h2
        rwa [hd, Nat.add_sub_cancel] at this
      rw [hd]
      calc r ^ (d + 2) * ‖slotCharFun F Z b T c‖
          ≤ r ^ (d + 2) * (Q * Real.sqrt (N : ℝ) ^ d) := by
            refine mul_le_mul_of_nonneg_left (hnorm.trans hQ2') (pow_nonneg hrpos.le _)
        _ = Q / (N : ℝ) := harith
  -- the per-assignment bound: the product over the fibres is `(Q/N)^{|image σ|}`
  have hperm : ∀ σ : Fin k → Fin N,
      r ^ k * ∏ i : Fin N, ‖slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖
        ≤ (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card := by
    intro σ
    have hsum : ∑ i : Fin N, (Finset.univ.filter fun l : Fin k => σ l = i).card = k := by
      have hfw := Finset.card_eq_sum_card_fiberwise
        (f := σ) (s := (Finset.univ : Finset (Fin k))) (t := (Finset.univ : Finset (Fin N)))
        (fun x _ => Finset.mem_univ _)
      simpa using hfw.symm
    have hrk : r ^ k
        = ∏ i : Fin N, r ^ (Finset.univ.filter fun l : Fin k => σ l = i).card := by
      rw [Finset.prod_pow_eq_pow_sum, hsum]
    rw [hrk, ← Finset.prod_mul_distrib]
    refine (Finset.prod_le_prod (fun i _ => mul_nonneg (pow_nonneg hrpos.le _) (norm_nonneg _))
      (fun i _ => hslot _)).trans (le_of_eq ?_)
    have hif : ∀ i : Fin N,
        (if (Finset.univ.filter fun l : Fin k => σ l = i) = ∅ then (1 : ℝ) else Q / (N : ℝ))
          = (if i ∈ Finset.image σ Finset.univ then Q / (N : ℝ) else 1) := by
      intro i
      by_cases hi : i ∈ Finset.image σ Finset.univ
      · rw [if_pos hi, if_neg]
        rw [Finset.mem_image] at hi
        obtain ⟨l, _, hl⟩ := hi
        exact Finset.nonempty_iff_ne_empty.1
          ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩⟩
      · rw [if_neg hi, if_pos]
        rw [Finset.filter_eq_empty_iff]
        intro l _
        exact fun hl => hi (Finset.mem_image.2 ⟨l, Finset.mem_univ _, hl⟩)
    simp_rw [hif]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  calc ‖((r : ℝ) : ℂ) ^ k * ∑ σ : Fin k → Fin N, ∏ i : Fin N,
        slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖
      = r ^ k * ‖∑ σ : Fin k → Fin N, ∏ i : Fin N,
          slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖ := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    _ ≤ r ^ k * ∑ σ : Fin k → Fin N, ∏ i : Fin N,
          ‖slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hrpos.le k)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => le_of_eq (norm_prod _ _))
    _ = ∑ σ : Fin k → Fin N, r ^ k * ∏ i : Fin N,
          ‖slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖ :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ σ : Fin k → Fin N, (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card :=
        Finset.sum_le_sum fun σ _ => hperm σ
    _ ≤ ((k : ℝ) + 1) * (k : ℝ) ^ k * Q ^ k := sum_div_pow_card_image_le hN hQ

set_option maxHeartbeats 800000 in
-- Same shape as `norm_multiCharFun_vecRootLaw_le`: a per-fibre trichotomy carried through a
-- product over `Fin N` and a sum over the `N^k` assignments; the default budget is not enough.
/-- **The `O(1)` multilinear estimate, with its Gaussian damping kept.**

`‖multi_{ρ_N}(b, a)‖ ≤ (k+1)k^k Q^k · ‖φ_{F∘Z⁻¹}(N^{-1/2} • a)‖^{N−k}`

under exactly the hypotheses of `norm_multiCharFun_vecRootLaw_le`, of which this is a strict
sharpening (`‖φ‖ ≤ 1`, so the damping factor is at most `1`).

**Why the damping has to be kept, and why it is free.** Every assignment `σ : Fin k → Fin N`
leaves `N − |image σ| ≥ N − k` coordinates *unweighted*, and each of them contributes the plain
factor `slot_∅(c) = φ_{F∘Z⁻¹}(c)`. `norm_multiCharFun_vecRootLaw_le` throws those factors away
one at a time (`‖φ(c)‖ ≤ 1`), which is harmless when `a` is fixed and fatal when `a` grows with
`N`: the studentized window of `Bootstrap/Edgeworth.lean` evaluates this at `a = (θ/σ)•e₀` with
`|θ|` up to `c√N`, where the `O(1)` bound has *polynomial growth in `θ`* and cannot be dominated
by any envelope that the Esseen split can integrate. The damping factor is what restores
`e^{−θ²/2}`, and the only change in the proof is that the empty fibres keep `‖φ(c)‖` instead of
being rounded up to `1`. See the wave-42 note in `Bootstrap/Edgeworth.lean` on the shape of
(U4). -/
theorem norm_multiCharFun_vecRootLaw_damped_le (F : Measure ℝ) [IsProbabilityMeasure F]
    {Z : ℝ → E} (hZ : Measurable Z) {k N : ℕ} (hN : 1 ≤ N) (b : Fin k → E) (a : E)
    {Q : ℝ} (hQ : 1 ≤ Q)
    (hint : ∀ T : Finset (Fin k),
      Integrable (fun x : ℝ => ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)|) F)
    (hbl : ∀ l : Fin k, Integrable (fun x : E => (⟪x, b l⟫ : ℝ)) (F.map Z))
    (hcent : ∀ l : Fin k, (∫ x, (⟪x, b l⟫ : ℝ) ∂(F.map Z)) = 0)
    (hbla : ∀ l : Fin k,
      Integrable (fun x : E => |(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) (F.map Z))
    (hQ1 : ∀ l : Fin k, (∫ x, |(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)| ∂(F.map Z)) ≤ Q)
    (hQ2 : ∀ T : Finset (Fin k), 2 ≤ T.card →
      (∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z))
        ≤ Q * Real.sqrt (N : ℝ) ^ (T.card - 2)) :
    ‖multiCharFun (vecRootLaw F Z N) b a‖
      ≤ ((k : ℝ) + 1) * (k : ℝ) ^ k * Q ^ k
        * ‖charFun (F.map Z) ((Real.sqrt (N : ℝ))⁻¹ • a)‖ ^ (N - k) := by
  classical
  haveI : IsProbabilityMeasure (F.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsq : (0 : ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hN0
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  rw [multiCharFun_vecRootLaw F hZ b hint a]
  set r : ℝ := (Real.sqrt (N : ℝ))⁻¹ with hrdef
  set c : E := r • a with hcdef
  set D : ℝ := ‖charFun (F.map Z) c‖ with hDdef
  have hD0 : 0 ≤ D := norm_nonneg _
  have hD1 : D ≤ 1 := norm_charFun_le_one c
  have hrpos : 0 < r := by rw [hrdef]; exact inv_pos.2 hsq
  have hrsq : r * Real.sqrt (N : ℝ) = 1 := by rw [hrdef]; field_simp
  have hr2 : r ^ 2 = ((N : ℝ))⁻¹ := by rw [hrdef, inv_pow, Real.sq_sqrt hN0.le]
  have hca : ∀ w : E, (⟪w, c⟫ : ℝ) = r * (⟪w, a⟫ : ℝ) := fun w => by
    rw [hcdef, real_inner_smul_right]
  -- the per-fibre bound: the empty fibres now keep the damping factor `D`
  have hslot : ∀ T : Finset (Fin k),
      r ^ T.card * ‖slotCharFun F Z b T c‖ ≤ (if T = ∅ then D else Q / (N : ℝ)) := by
    intro T
    rcases eq_or_ne T ∅ with rfl | hTne
    · rw [if_pos rfl, Finset.card_empty, pow_zero, one_mul, slotCharFun_empty F hZ b c]
    rw [if_neg hTne]
    have hpos : 1 ≤ T.card := Finset.card_pos.2 (Finset.nonempty_of_ne_empty hTne)
    rcases eq_or_lt_of_le hpos with h1 | h2
    · obtain ⟨l, rfl⟩ := Finset.card_eq_one.1 h1.symm
      have hgm : Measurable fun w : E => (⟪w, b l⟫ : ℝ) := measurable_inner_right (b l)
      have habs : ∀ x : E, |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|
          = r * (|(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := fun x => by
        rw [hca x, abs_mul r ((⟪x, a⟫ : ℝ)), abs_of_pos hrpos]; ring
      have hgt : Integrable (fun x : E => |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|) (F.map Z) := by
        have hEq : (fun x : E => |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)|)
            = fun x : E => r * (|(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)|) := funext habs
        rw [hEq]; exact (hbla l).const_mul r
      have hmom : (∫ x, |(⟪x, b l⟫ : ℝ)| * |(⟪x, c⟫ : ℝ)| ∂(F.map Z))
          = r * ∫ x, |(⟪x, b l⟫ : ℝ)| * |(⟪x, a⟫ : ℝ)| ∂(F.map Z) := by
        simp_rw [habs]
        exact integral_const_mul _ _
      have hbound := norm_integral_ofReal_mul_cexp_sub_le (F.map Z) hgm (hbl l) hgt
      rw [hcent l] at hbound
      simp only [Complex.ofReal_zero, sub_zero] at hbound
      rw [hmom] at hbound
      have hslot1 : ‖slotCharFun F Z b {l} c‖ ≤ r * Q := by
        rw [slotCharFun_singleton F hZ b l c, mixCharFun]
        exact hbound.trans (mul_le_mul_of_nonneg_left (hQ1 l) hrpos.le)
      rw [Finset.card_singleton, pow_one]
      calc r * ‖slotCharFun F Z b {l} c‖ ≤ r * (r * Q) :=
            mul_le_mul_of_nonneg_left hslot1 hrpos.le
        _ = Q / (N : ℝ) := by
            rw [show r * (r * Q) = r ^ 2 * Q by ring, hr2]
            field_simp
    · have hnorm : ‖slotCharFun F Z b T c‖
          ≤ ∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z) := by
        have hmap : (∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z))
            = ∫ x, ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)| ∂F := by
          rw [integral_map hZ.aemeasurable]
          exact (Finset.measurable_prod _ fun l _ =>
            (measurable_inner_right (b l)).abs).aestronglyMeasurable
        rw [hmap, slotCharFun]
        refine norm_integral_le_of_norm_le (hint T) (Filter.Eventually.of_forall fun x => ?_)
        have hx : ‖(∏ l ∈ T, ((⟪Z x, b l⟫ : ℝ) : ℂ))
            * Complex.exp ((⟪Z x, c⟫ : ℝ) * Complex.I)‖
            = ∏ l ∈ T, |(⟪Z x, b l⟫ : ℝ)| := by
          rw [norm_mul, norm_prod]
          simp [Complex.norm_exp]
        exact hx.le
      obtain ⟨d, hd⟩ : ∃ d, T.card = d + 2 := ⟨T.card - 2, by omega⟩
      have harith : r ^ (d + 2) * (Q * Real.sqrt (N : ℝ) ^ d) = Q / (N : ℝ) := by
        have hstep : r ^ (d + 2) * Real.sqrt (N : ℝ) ^ d = ((N : ℝ))⁻¹ := by
          calc r ^ (d + 2) * Real.sqrt (N : ℝ) ^ d
              = (r * Real.sqrt (N : ℝ)) ^ d * r ^ 2 := by rw [mul_pow]; ring
            _ = r ^ 2 := by rw [hrsq, one_pow, one_mul]
            _ = ((N : ℝ))⁻¹ := hr2
        calc r ^ (d + 2) * (Q * Real.sqrt (N : ℝ) ^ d)
            = (r ^ (d + 2) * Real.sqrt (N : ℝ) ^ d) * Q := by ring
          _ = ((N : ℝ))⁻¹ * Q := by rw [hstep]
          _ = Q / (N : ℝ) := by field_simp
      have hQ2' : (∫ x, ∏ l ∈ T, |(⟪x, b l⟫ : ℝ)| ∂(F.map Z))
          ≤ Q * Real.sqrt (N : ℝ) ^ d := by
        have := hQ2 T h2
        rwa [hd, Nat.add_sub_cancel] at this
      rw [hd]
      calc r ^ (d + 2) * ‖slotCharFun F Z b T c‖
          ≤ r ^ (d + 2) * (Q * Real.sqrt (N : ℝ) ^ d) := by
            refine mul_le_mul_of_nonneg_left (hnorm.trans hQ2') (pow_nonneg hrpos.le _)
        _ = Q / (N : ℝ) := harith
  -- the per-assignment bound, now carrying `D^{N−k}`
  have hperm : ∀ σ : Fin k → Fin N,
      r ^ k * ∏ i : Fin N, ‖slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖
        ≤ D ^ (N - k) * (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card := by
    intro σ
    have himk : (Finset.image σ Finset.univ).card ≤ k := by
      calc (Finset.image σ Finset.univ).card ≤ (Finset.univ : Finset (Fin k)).card :=
            Finset.card_image_le
        _ = k := by simp
    have hsum : ∑ i : Fin N, (Finset.univ.filter fun l : Fin k => σ l = i).card = k := by
      have hfw := Finset.card_eq_sum_card_fiberwise
        (f := σ) (s := (Finset.univ : Finset (Fin k))) (t := (Finset.univ : Finset (Fin N)))
        (fun x _ => Finset.mem_univ _)
      simpa using hfw.symm
    have hrk : r ^ k
        = ∏ i : Fin N, r ^ (Finset.univ.filter fun l : Fin k => σ l = i).card := by
      rw [Finset.prod_pow_eq_pow_sum, hsum]
    rw [hrk, ← Finset.prod_mul_distrib]
    refine (Finset.prod_le_prod (fun i _ => mul_nonneg (pow_nonneg hrpos.le _) (norm_nonneg _))
      (fun i _ => hslot _)).trans ?_
    have hif : ∀ i : Fin N,
        (if (Finset.univ.filter fun l : Fin k => σ l = i) = ∅ then D else Q / (N : ℝ))
          = (if i ∈ Finset.image σ Finset.univ then Q / (N : ℝ) else D) := by
      intro i
      by_cases hi : i ∈ Finset.image σ Finset.univ
      · rw [if_pos hi, if_neg]
        rw [Finset.mem_image] at hi
        obtain ⟨l, _, hl⟩ := hi
        exact Finset.nonempty_iff_ne_empty.1
          ⟨l, Finset.mem_filter.2 ⟨Finset.mem_univ _, hl⟩⟩
      · rw [if_neg hi, if_pos]
        rw [Finset.filter_eq_empty_iff]
        intro l _
        exact fun hl => hi (Finset.mem_image.2 ⟨l, Finset.mem_univ _, hl⟩)
    simp_rw [hif]
    rw [Finset.prod_ite]
    have hc1 : (Finset.univ.filter
        (fun i : Fin N => i ∈ Finset.image σ Finset.univ)).card
        = (Finset.image σ Finset.univ).card := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have hc2 : (Finset.univ.filter
        (fun i : Fin N => ¬ i ∈ Finset.image σ Finset.univ)).card
        = N - (Finset.image σ Finset.univ).card := by
      rw [Finset.filter_not, Finset.card_sdiff, Finset.inter_univ, hc1,
        Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_const, Finset.prod_const, hc1, hc2]
    have hpowD : D ^ (N - (Finset.image σ Finset.univ).card) ≤ D ^ (N - k) :=
      pow_le_pow_of_le_one hD0 hD1 (by omega)
    calc (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card
            * D ^ (N - (Finset.image σ Finset.univ).card)
        ≤ (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card * D ^ (N - k) := by
          refine mul_le_mul_of_nonneg_left hpowD (by positivity)
      _ = D ^ (N - k) * (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card := by ring
  calc ‖((r : ℝ) : ℂ) ^ k * ∑ σ : Fin k → Fin N, ∏ i : Fin N,
        slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖
      = r ^ k * ‖∑ σ : Fin k → Fin N, ∏ i : Fin N,
          slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖ := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
    _ ≤ r ^ k * ∑ σ : Fin k → Fin N, ∏ i : Fin N,
          ‖slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hrpos.le k)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => le_of_eq (norm_prod _ _))
    _ = ∑ σ : Fin k → Fin N, r ^ k * ∏ i : Fin N,
          ‖slotCharFun F Z b (Finset.univ.filter fun l => σ l = i) c‖ :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ σ : Fin k → Fin N,
          D ^ (N - k) * (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card :=
        Finset.sum_le_sum fun σ _ => hperm σ
    _ = D ^ (N - k)
          * ∑ σ : Fin k → Fin N, (Q / (N : ℝ)) ^ (Finset.image σ Finset.univ).card := by
        rw [← Finset.mul_sum]
    _ ≤ D ^ (N - k) * (((k : ℝ) + 1) * (k : ℝ) ^ k * Q ^ k) := by
        exact mul_le_mul_of_nonneg_left (sum_div_pow_card_image_le hN hQ) (by positivity)
    _ = ((k : ℝ) + 1) * (k : ℝ) ^ k * Q ^ k * D ^ (N - k) := by ring

end MultiBound

end StatLean.HypothesisTesting
