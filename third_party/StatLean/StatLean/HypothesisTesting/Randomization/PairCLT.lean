module
public import StatLean.HypothesisTesting.Randomization.Asymptotics
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

@[expose] public section

/-!
# The bivariate sign-change randomization central limit theorem

This file supplies the one analytic engine that all the *joint* randomization limits of the
area consume: the law of a linear statistic recomputed at **two independent uniform sign
patterns** converges to a product of two identical centred Gaussians.

Everything is done at the level of characteristic functions, which is what makes the
"two independent group elements" structure trivial: averaging `exp(i(sa+s'b))` over the four
sign pairs `(s,s') ∈ {\pm 1\}^2` factorizes as `cos a · cos b`, so the two coordinates
decouple *exactly* at every finite `n`, and the limit is automatically a product measure.

## Main results

* `weakConverges_of_tendsto_charFun` — Lévy continuity in the `WeakConverges` packaging;
* `weakConverges_prod_of_tendsto_charFun` — its product-space form: pointwise convergence of
  the characteristic function of `μ n` (transported to `WithLp 2 (E × E)`) to a *product* of
  two characteristic functions gives weak convergence to the product measure;
* `charFun_randPairLaw_signSum` — the exact finite-`n` identity
  `charFun = (4⁻¹ ∑_{s,s'} charFun (Q.map W_{s,s'}) n^{-1/2})^n`;
* `weakConverges_randPairLaw_signSum` — the resulting bivariate CLT, for data in an arbitrary
  finite-dimensional real inner-product space.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.2–§17.4 (the joint hypothesis of Theorem 17.2.3, verified for the
sign-change group in Theorem 17.2.4 and Lemmas 17.4.1–17.4.3). (`TSH4 §17.2 Thm 17.2.4`.)

**Proof formalization notes.**
* *No mean-zero hypothesis.* Averaging over the sign group symmetrizes the summands, so the
  first-order term of the expansion cancels identically: only the **second moment**
  `∫ ⟪x,t⟫² dQ` enters. This is why the vector building block of
  `Randomization/MultivariateQuadratic` holds verbatim with `S` read as the second-moment
  matrix, as its file notes predict.
* *No independent CLT brick is used.* The finite-`n` characteristic function is computed in
  closed form (`charFun_randPairLaw_signSum`) — a product over the `n` coordinates, obtained
  from `Finset.prod_univ_sum` (sum over sign patterns of a product = product of sums) and
  `integral_fintype_prod_eq_pow` (Fubini for product measures). The limit is then the
  classical `(1 + t/n + o(1/n))ⁿ → eᵗ` of `Complex.tendsto_pow_exp_of_isLittleO_sub_add_div`,
  fed by the second-order Taylor expansion of a one-dimensional characteristic function
  (`taylorWithinEval_charFun_two_zero`).
* *Why `WithLp 2 (E × E)`.* Lévy's continuity theorem needs an inner-product space, and the
  plain product `E × E` carries the sup norm. `WithLp 2 (E × E)` is the same measurable space
  and the same topology (`WithLp.prod_continuous_toLp` / `prod_continuous_ofLp`), so weak
  convergence transports back and forth; `charFun_prod` identifies the characteristic function
  of a product measure there.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### Lévy continuity, in the `WeakConverges` packaging -/

/-- **Lévy's continuity theorem, `WeakConverges` form.** Pointwise convergence of
characteristic functions to that of a probability measure gives weak convergence. -/
lemma weakConverges_of_tendsto_charFun {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {μ : ℕ → Measure H} [∀ n, IsProbabilityMeasure (μ n)] {ν : Measure H}
    [IsProbabilityMeasure ν]
    (h : ∀ t : H, Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (charFun ν t))) :
    WeakConverges μ ν := by
  set pn : ℕ → ProbabilityMeasure H := fun n => ⟨μ n, inferInstance⟩ with hpn
  set pν : ProbabilityMeasure H := ⟨ν, inferInstance⟩ with hpν
  have htend : Tendsto pn atTop (𝓝 pν) :=
    ProbabilityMeasure.tendsto_of_tendsto_charFun (by simpa [pn, pν] using h)
  intro f
  simpa [pn, pν] using
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp htend) f

/-- **Lévy continuity onto a product limit.** If the characteristic function of `μ n`,
transported to the Hilbert-space model `WithLp 2 (E × E)` of the product, converges pointwise
to the product `charFun ν₁ t₁ · charFun ν₂ t₂`, then `μ n` converges weakly to `ν₁ ⊗ ν₂`. -/
lemma weakConverges_prod_of_tendsto_charFun {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure (E × E)} [∀ n, IsProbabilityMeasure (μ n)]
    {ν₁ ν₂ : Measure E} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ t : WithLp 2 (E × E),
      Tendsto (fun n => charFun ((μ n).map (WithLp.toLp 2)) t) atTop
        (𝓝 (charFun ν₁ (WithLp.ofLp t).1 * charFun ν₂ (WithLp.ofLp t).2))) :
    WeakConverges μ (ν₁.prod ν₂) := by
  haveI : ∀ n, IsProbabilityMeasure ((μ n).map (WithLp.toLp (V := E × E) 2)) := fun n =>
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
  haveI : IsProbabilityMeasure ((ν₁.prod ν₂).map (WithLp.toLp (V := E × E) 2)) :=
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
  have hlim : WeakConverges (fun n => (μ n).map (WithLp.toLp 2))
      ((ν₁.prod ν₂).map (WithLp.toLp 2)) := by
    refine weakConverges_of_tendsto_charFun (fun t => ?_)
    rw [charFun_prod]
    exact h t
  have hmap := hlim.map (f := WithLp.ofLp) (WithLp.prod_continuous_ofLp 2 E E)
    (WithLp.measurable_ofLp 2 (E × E))
  have hcollapse : ∀ ρ : Measure (E × E),
      (ρ.map (WithLp.toLp (V := E × E) 2)).map WithLp.ofLp = ρ := by
    intro ρ
    have hid : (WithLp.ofLp : WithLp 2 (E × E) → E × E) ∘ (WithLp.toLp (V := E × E) 2) = id := rfl
    rw [Measure.map_map (WithLp.measurable_ofLp 2 (E × E)) (WithLp.measurable_toLp 2 (E × E)),
      hid, Measure.map_id]
  simpa only [hcollapse] using hmap

/-- Transporting a measure on `E × E` to the Hilbert model and back is the identity. -/
private lemma map_toLp_map_ofLp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (ρ : Measure (E × E)) :
    (ρ.map (WithLp.toLp (V := E × E) 2)).map WithLp.ofLp = ρ := by
  have hid : (WithLp.ofLp : WithLp 2 (E × E) → E × E) ∘ (WithLp.toLp (V := E × E) 2) = id := rfl
  rw [Measure.map_map (WithLp.measurable_ofLp 2 (E × E)) (WithLp.measurable_toLp 2 (E × E)),
    hid, Measure.map_id]

/-- Weak convergence on `E × E` is weak convergence on the Hilbert model `WithLp 2 (E × E)`:
the two carry the same topology. -/
private lemma weakConverges_map_toLp_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {μ : ℕ → Measure (E × E)} {ν : Measure (E × E)} :
    WeakConverges μ ν ↔
      WeakConverges (fun n => (μ n).map (WithLp.toLp 2)) (ν.map (WithLp.toLp 2)) := by
  constructor
  · intro h
    exact h.map (WithLp.prod_continuous_toLp 2 E E) (WithLp.measurable_toLp 2 (E × E))
  · intro h
    have hmap := h.map (WithLp.prod_continuous_ofLp 2 E E) (WithLp.measurable_ofLp 2 (E × E))
    simpa only [map_toLp_map_ofLp] using hmap

/-- The forward half of Lévy continuity in the `WeakConverges` packaging. -/
private lemma tendsto_charFun_of_weakConverges {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
    {μ : ℕ → Measure H} [∀ n, IsProbabilityMeasure (μ n)] {ν : Measure H}
    [IsProbabilityMeasure ν] (h : WeakConverges μ ν) (t : H) :
    Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (charFun ν t)) := by
  set pn : ℕ → ProbabilityMeasure H := fun n => ⟨μ n, inferInstance⟩ with hpn
  set pν : ProbabilityMeasure H := ⟨ν, inferInstance⟩ with hpν
  have htend : Tendsto pn atTop (𝓝 pν) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr (by simpa [pn, pν] using! h)
  simpa [pn, pν] using (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp htend) t

/-! ### Integrating a bounded test function against `randPairLaw` -/

/-- **`randPairLaw` unfolded inside an integral.** For a bounded measurable `F`, the integral
against the doubly randomized law is the group average of the integrals of `F` composed with
the two randomized statistics. -/
lemma integral_randPairLaw {𝓧 Z : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Z]
    {G : Type*} [Group G] [Fintype G] [MulAction G 𝓧] (P : Measure 𝓧) [IsProbabilityMeasure P]
    (T : 𝓧 → Z) (hT : ∀ g : G, Measurable fun x : 𝓧 => T (g • x))
    (F : Z × Z → ℂ) (hF : Measurable F) (hFb : ∀ z, ‖F z‖ ≤ 1) :
    ∫ z, F z ∂(randPairLaw G T P)
      = ((Fintype.card G : ℂ) ^ 2)⁻¹ *
        ∑ g : G, ∑ g' : G, ∫ x, F (T (g • x), T (g' • x)) ∂P := by
  classical
  have hint : ∀ (ρ : Measure (Z × Z)), IsFiniteMeasure ρ → Integrable F ρ := by
    intro ρ _
    exact Integrable.mono' (integrable_const (1 : ℝ)) hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hFb)
  have hpair : ∀ g g' : G, Measurable fun x : 𝓧 => (T (g • x), T (g' • x)) :=
    fun g g' => (hT g).prodMk (hT g')
  haveI hprob : ∀ g g' : G,
      IsProbabilityMeasure (P.map fun x : 𝓧 => (T (g • x), T (g' • x))) :=
    fun g g' => Measure.isProbabilityMeasure_map (hpair g g').aemeasurable
  rw [randPairLaw, integral_smul_measure,
    integral_finset_sum_measure (fun g _ => integrable_finset_sum_measure.2
      (fun g' _ => hint _ inferInstance))]
  have hstep : ∀ g : G, ∫ z, F z ∂(∑ g' : G, P.map fun x : 𝓧 => (T (g • x), T (g' • x)))
      = ∑ g' : G, ∫ x, F (T (g • x), T (g' • x)) ∂P := by
    intro g
    rw [integral_finset_sum_measure (fun g' _ => hint _ inferInstance)]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [integral_map (hpair g g').aemeasurable hF.aestronglyMeasurable]
  simp_rw [hstep]
  have hcoef : ((((Fintype.card G : ℝ≥0∞)) ^ 2)⁻¹).toReal = ((Fintype.card G : ℝ) ^ 2)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  have hc : ((((Fintype.card G : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) = ((Fintype.card G : ℂ) ^ 2)⁻¹ := by
    push_cast
    ring
  rw [hcoef, ← hc]
  exact RCLike.real_smul_eq_coe_mul _ _

/-- **Equivariant reduction of `randPairLaw`.** If `Φ` intertwines the group actions, the
doubly randomized law of `T ∘ Φ` under `P` is the doubly randomized law of `T` under the
pushforward `P.map Φ`. -/
lemma randPairLaw_comp {𝓧 𝓨 Z : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    [MeasurableSpace Z] {G : Type*} [Group G] [Fintype G] [MulAction G 𝓧] [MulAction G 𝓨]
    (P : Measure 𝓧) {Φ : 𝓧 → 𝓨} (hΦ : Measurable Φ)
    (hequiv : ∀ (g : G) (x : 𝓧), Φ (g • x) = g • Φ x)
    {T : 𝓨 → Z} (hT : Measurable T) (hsmul : ∀ g : G, Measurable fun y : 𝓨 => g • y) :
    randPairLaw G (fun x => T (Φ x)) P = randPairLaw G T (P.map Φ) := by
  unfold randPairLaw
  congr 1
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun g' _ => ?_
  have h := Measure.map_map (μ := P) (g := fun y : 𝓨 => (T (g • y), T (g' • y))) (f := Φ)
    ((hT.comp (hsmul g)).prodMk (hT.comp (hsmul g'))) hΦ
  rw [h]
  congr 1
  funext x
  simp only [Function.comp_apply, hequiv]

/-! ### The sign-change group acting on vector-valued data -/

/-- The sign-change action on vector data, written out: `(ε • x) i = εᵢ • xᵢ`, with the
integer unit read as a real scalar. -/
lemma signChange_smul_apply_vec {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (ε : Fin n → ℤˣ) (x : Fin n → V) (i : Fin n) :
    (ε • x) i = ((ε i : ℤ) : ℝ) • x i := by
  change ((ε i : ℤ)) • x i = _
  rw [← Int.cast_smul_eq_zsmul ℝ]

/-- The sign-change group on `n` coordinates has `2ⁿ` elements. -/
private lemma card_signPattern (n : ℕ) : Fintype.card (Fin n → ℤˣ) = 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_units_int]

/-- A double sum over the two-element group `ℤˣ`, written out. -/
private lemma sum_units_int {M : Type*} [AddCommMonoid M] (f : ℤˣ → ℤˣ → M) :
    (∑ s : ℤˣ, ∑ s' : ℤˣ, f s s') = f 1 1 + f 1 (-1) + (f (-1) 1 + f (-1) (-1)) := by
  classical
  rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from UnitsInt.univ,
    Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
    Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
    Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]

section SignSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- The real linear form `y ↦ s⟪y,t₁⟫ + s'⟪y,t₂⟫` obtained by pairing the data with the two
test directions through a sign pair. Averaging over the four sign pairs is what makes the two
components of `randPairLaw` decouple. -/
private noncomputable def signDir (t : WithLp 2 (E × E)) (s s' : ℤˣ) (y : E) : ℝ :=
  ((s : ℤ) : ℝ) * ⟪y, (WithLp.ofLp t).1⟫ + ((s' : ℤ) : ℝ) * ⟪y, (WithLp.ofLp t).2⟫

private lemma continuous_signDir (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    Continuous (signDir t s s') := by
  have h1 : Continuous fun y : E => ⟪y, (WithLp.ofLp t).1⟫ :=
    (continuous_id (X := E)).inner continuous_const
  have h2 : Continuous fun y : E => ⟪y, (WithLp.ofLp t).2⟫ :=
    (continuous_id (X := E)).inner continuous_const
  exact (h1.const_mul _).add (h2.const_mul _)

private lemma measurable_signDir (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    Measurable (signDir t s s') := (continuous_signDir t s s').measurable

/-- Pairing the sign-flipped normalized sum with a test direction. -/
private lemma inner_signSum (n : ℕ) (ε : Fin n → ℤˣ) (x : Fin n → E) (t : E) :
    ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i, t⟫
      = ∑ i, (Real.sqrt (n : ℝ))⁻¹ * (((ε i : ℤ) : ℝ) * ⟪x i, t⟫) := by
  rw [real_inner_smul_left, sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [signChange_smul_apply_vec, real_inner_smul_left]

/-- The joint exponential factorizes across coordinates. -/
private lemma exp_inner_pair_eq_prod (n : ℕ) (t : WithLp 2 (E × E)) (ε ε' : Fin n → ℤˣ)
    (x : Fin n → E) :
    Complex.exp (((⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i, (WithLp.ofLp t).1⟫
        + ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε' • x) i, (WithLp.ofLp t).2⟫ : ℝ) : ℂ) * Complex.I)
      = ∏ i, Complex.exp
          ((((Real.sqrt (n : ℝ))⁻¹ * signDir t (ε i) (ε' i) (x i) : ℝ) : ℂ) * Complex.I) := by
  have hexp : (⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i, (WithLp.ofLp t).1⟫
      + ⟪(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε' • x) i, (WithLp.ofLp t).2⟫ : ℝ)
      = ∑ i, (Real.sqrt (n : ℝ))⁻¹ * signDir t (ε i) (ε' i) (x i) := by
    rw [inner_signSum, inner_signSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold signDir
    ring
  rw [hexp, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]

/-- The single-coordinate factor of the randomized characteristic function. -/
private noncomputable def signFactor (n : ℕ) (t : WithLp 2 (E × E)) (s s' : ℤˣ) (y : E) : ℂ :=
  Complex.exp ((((Real.sqrt (n : ℝ))⁻¹ * signDir t s s' y : ℝ) : ℂ) * Complex.I)

private lemma measurable_signFactor (n : ℕ) (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    Measurable (signFactor n t s s') := by
  unfold signFactor
  exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    ((continuous_signDir t s s').const_mul _)).mul continuous_const)).measurable

private lemma norm_signFactor (n : ℕ) (t : WithLp 2 (E × E)) (s s' : ℤˣ) (y : E) :
    ‖signFactor n t s s' y‖ = 1 := by
  unfold signFactor
  exact Complex.norm_exp_ofReal_mul_I _

/-- Sum over sign patterns of a product = product of the coordinatewise sums, applied to the
two independent sign vectors. -/
private lemma prod_sum_signFactor (n : ℕ) (t : WithLp 2 (E × E)) (x : Fin n → E) :
    ∏ i, (∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' (x i))
      = ∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
          ∏ i, signFactor n t (ε i) (ε' i) (x i) := by
  classical
  rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ℤˣ))
    (fun i s => ∑ s' : ℤˣ, signFactor n t s s' (x i)), Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ℤˣ))
    (fun i s' => signFactor n t (ε i) s' (x i)), Fintype.piFinset_univ]

/-- **The exact characteristic function of the sign-change randomized pair.**
At every finite `n` the joint characteristic function of the pair
`(n^{-1/2}∑ᵢεᵢXᵢ, n^{-1/2}∑ᵢε'ᵢXᵢ)` is the `n`-th power of the four-term sign average of
one-dimensional characteristic functions. -/
private lemma charFun_randPairLaw_signSum (Q : Measure E) [IsProbabilityMeasure Q]
    (n : ℕ) (t : WithLp 2 (E × E)) :
    charFun ((randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
        (Measure.pi fun _ : Fin n => Q)).map (WithLp.toLp 2)) t
      = ((4 : ℂ)⁻¹ * ∑ s : ℤˣ, ∑ s' : ℤˣ,
          charFun (Q.map (signDir t s s')) (Real.sqrt (n : ℝ))⁻¹) ^ n := by
  classical
  set u : ℝ := (Real.sqrt (n : ℝ))⁻¹ with hudef
  set T : (Fin n → E) → E := fun x => u • ∑ i, x i with hTdef
  set πQ : Measure (Fin n → E) := Measure.pi fun _ : Fin n => Q with hπQ
  -- The bounded test function on the product.
  set F : E × E → ℂ := fun z =>
    Complex.exp (((⟪z.1, (WithLp.ofLp t).1⟫ + ⟪z.2, (WithLp.ofLp t).2⟫ : ℝ) : ℂ) * Complex.I)
    with hFdef
  have hFcont : Continuous F := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp
      ((continuous_fst.inner continuous_const).add (continuous_snd.inner continuous_const))
  have hFb : ∀ z, ‖F z‖ ≤ 1 := fun z => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  -- Measurability of the action and of the statistic.
  have hsmul : ∀ ε : Fin n → ℤˣ, Measurable fun x : Fin n → E => ε • x := by
    intro ε
    refine measurable_pi_lambda _ fun i => ?_
    simp only [signChange_smul_apply_vec]
    exact (measurable_pi_apply i).const_smul _
  have hTmeas : Measurable T :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul u
  have hTg : ∀ ε : Fin n → ℤˣ, Measurable fun x : Fin n → E => T (ε • x) :=
    fun ε => hTmeas.comp (hsmul ε)
  -- Step 1: the characteristic function as an integral against `randPairLaw`.
  have hcontExp : Continuous fun y : WithLp 2 (E × E) =>
      Complex.exp (((⟪y, t⟫ : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      ((continuous_id (X := WithLp 2 (E × E))).inner continuous_const)).mul continuous_const)
  have hstep1 : charFun ((randPairLaw (Fin n → ℤˣ) T πQ).map (WithLp.toLp 2)) t
      = ∫ z, F z ∂(randPairLaw (Fin n → ℤˣ) T πQ) := by
    rw [charFun_apply, integral_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
      hcontExp.aestronglyMeasurable]
    rfl
  -- Step 2: unfold the group average.
  have hstep2 := integral_randPairLaw (G := Fin n → ℤˣ) πQ T hTg F hFcont.measurable hFb
  -- Step 3: the per-pattern integrand factorizes across coordinates.
  have hstep3 : ∀ (ε ε' : Fin n → ℤˣ) (x : Fin n → E),
      F (T (ε • x), T (ε' • x)) = ∏ i, signFactor n t (ε i) (ε' i) (x i) := by
    intro ε ε' x
    exact exp_inner_pair_eq_prod n t ε ε' x
  -- Integrability bookkeeping.
  have hprodmeas : ∀ ε ε' : Fin n → ℤˣ,
      Measurable fun x : Fin n → E => ∏ i, signFactor n t (ε i) (ε' i) (x i) := by
    intro ε ε'
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_signFactor n t (ε i) (ε' i)).comp (measurable_pi_apply i)
  have hprodb : ∀ (ε ε' : Fin n → ℤˣ) (x : Fin n → E),
      ‖∏ i, signFactor n t (ε i) (ε' i) (x i)‖ ≤ 1 := by
    intro ε ε' x
    rw [norm_prod]
    simp [norm_signFactor]
  have hprodint : ∀ ε ε' : Fin n → ℤˣ,
      Integrable (fun x : Fin n → E => ∏ i, signFactor n t (ε i) (ε' i) (x i)) πQ := by
    intro ε ε'
    exact Integrable.mono' (integrable_const (1 : ℝ)) (hprodmeas ε ε').aestronglyMeasurable
      (Filter.Eventually.of_forall (hprodb ε ε'))
  have hkint : ∀ s s' : ℤˣ, Integrable (signFactor n t s s') Q :=
    fun s s' => Integrable.mono' (integrable_const (1 : ℝ))
      (measurable_signFactor n t s s').aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => le_of_eq (norm_signFactor n t s s' y))
  -- Step 4: swap the finite sums with the integral and use Fubini for the product measure.
  have hstep4 : (∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
        ∫ x, F (T (ε • x), T (ε' • x)) ∂πQ)
      = (∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, signFactor n t s s' y ∂Q) ^ n := by
    have h1 : (∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ, ∫ x, F (T (ε • x), T (ε' • x)) ∂πQ)
        = ∫ x, ∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
            ∏ i, signFactor n t (ε i) (ε' i) (x i) ∂πQ := by
      rw [integral_finset_sum _ (fun ε _ => integrable_finset_sum _ fun ε' _ => hprodint ε ε')]
      refine Finset.sum_congr rfl fun ε _ => ?_
      rw [integral_finset_sum _ (fun ε' _ => hprodint ε ε')]
      refine Finset.sum_congr rfl fun ε' _ => ?_
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hstep3 ε ε' x)
    rw [h1]
    have h2 : (fun x : Fin n → E => ∑ ε : Fin n → ℤˣ, ∑ ε' : Fin n → ℤˣ,
          ∏ i, signFactor n t (ε i) (ε' i) (x i))
        = fun x : Fin n → E => ∏ i, (∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' (x i)) := by
      funext x
      exact (prod_sum_signFactor n t x).symm
    have h3 := integral_fintype_prod_eq_pow (ι := Fin n)
      (f := fun y : E => ∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' y) (μ := Q)
    rw [h2, hπQ]
    refine h3.trans ?_
    rw [Fintype.card_fin]
    congr 1
    have hsw1 : ∫ y : E, (∑ s : ℤˣ, ∑ s' : ℤˣ, signFactor n t s s' y) ∂Q
        = ∑ s : ℤˣ, ∫ y : E, (∑ s' : ℤˣ, signFactor n t s s' y) ∂Q :=
      integral_finset_sum (f := fun s : ℤˣ => fun y : E => ∑ s' : ℤˣ, signFactor n t s s' y)
        Finset.univ (fun s _ => integrable_finset_sum Finset.univ fun s' _ => hkint s s')
    have hsw2 : ∀ s : ℤˣ, ∫ y : E, (∑ s' : ℤˣ, signFactor n t s s' y) ∂Q
        = ∑ s' : ℤˣ, ∫ y : E, signFactor n t s s' y ∂Q := fun s =>
      integral_finset_sum (f := fun s' : ℤˣ => fun y : E => signFactor n t s s' y)
        Finset.univ (fun s' _ => hkint s s')
    exact hsw1.trans (Finset.sum_congr rfl fun s _ => hsw2 s)
  -- Step 5: identify the coordinate integrals as one-dimensional characteristic functions.
  have hstep5 : ∀ s s' : ℤˣ,
      ∫ y, signFactor n t s s' y ∂Q = charFun (Q.map (signDir t s s')) u := by
    intro s s'
    have haes : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I)) (Q.map (signDir t s s')) :=
      (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
    rw [charFun_apply_real, integral_map (measurable_signDir t s s').aemeasurable haes]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    unfold signFactor
    rw [Complex.ofReal_mul]
  -- Assemble.
  rw [hstep1, hstep2, hstep4]
  simp_rw [hstep5]
  have hcard : ((Fintype.card (Fin n → ℤˣ) : ℂ) ^ 2)⁻¹ = ((4 : ℂ)⁻¹) ^ n := by
    rw [card_signPattern]
    push_cast
    rw [← pow_mul, mul_comm n 2, pow_mul, ← inv_pow]
    norm_num
  rw [hcard, ← mul_pow]

/-! ### The limit -/

/-- **Second-order Taylor expansion of a one-dimensional characteristic function**, without
the mean-zero / unit-variance normalization of Mathlib's `taylor_charFun_two`. The
sign-averaged expansion below needs the unnormalized form, because the four sign directions
have different (nonzero) means and second moments. -/
private lemma isLittleO_charFun_taylor {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : Ω → ℝ} (hW : AEMeasurable W P)
    (hint : MemLp id 2 (P.map W)) :
    (fun v : ℝ => charFun (P.map W) v
        - (1 + (P[W] : ℝ) * v * Complex.I - (P[W ^ 2] : ℝ) * v ^ 2 / 2))
      =o[𝓝 0] fun v : ℝ => v ^ 2 := by
  have h := taylor_isLittleO_univ (x₀ := (0 : ℝ)) (contDiff_charFun hint)
  simp only [sub_zero] at h
  refine h.congr' (Filter.Eventually.of_forall fun v => ?_) Filter.EventuallyEq.rfl
  simp only []
  rw [taylorWithinEval_charFun_two_zero hW hint v]

/-- Pairing with a fixed direction is square-integrable when the data is. -/
lemma memLp_inner_right (Q : Measure E) (hQ2 : MemLp id 2 Q) (v : E) :
    MemLp (fun y : E => ⟪y, v⟫) 2 Q := by
  have hmeas : AEStronglyMeasurable (fun y : E => ⟪y, v⟫) Q :=
    ((continuous_id (X := E)).inner continuous_const).aestronglyMeasurable
  have hdom : MemLp (fun y : E => ‖v‖ * ‖y‖) 2 Q := by
    simpa using hQ2.norm.const_mul ‖v‖
  refine hdom.mono hmeas (Filter.Eventually.of_forall fun y => ?_)
  have hineq : |⟪y, v⟫| ≤ ‖y‖ * ‖v‖ := abs_real_inner_le_norm y v
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [mul_comm ‖v‖ ‖y‖]
  exact hineq

private lemma memLp_signDir (Q : Measure E) (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E))
    (s s' : ℤˣ) : MemLp (signDir t s s') 2 Q := by
  unfold signDir
  exact ((memLp_inner_right Q hQ2 _).const_mul _).add ((memLp_inner_right Q hQ2 _).const_mul _)

private lemma memLp_id_map_signDir (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E)) (s s' : ℤˣ) :
    MemLp id 2 (Q.map (signDir t s s')) := by
  rw [memLp_map_measure_iff aestronglyMeasurable_id (measurable_signDir t s s').aemeasurable]
  exact memLp_signDir Q hQ2 t s s'

/-- The four sign directions have vanishing total first moment. -/
private lemma sum_integral_signDir (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E)) :
    ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, signDir t s s' y ∂Q = 0 := by
  classical
  have hint : ∀ s s' : ℤˣ, Integrable (signDir t s s') Q := fun s s' =>
    (memLp_signDir Q hQ2 t s s').integrable (by norm_num)
  have h1 : ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, signDir t s s' y ∂Q
      = ∫ y, (∑ s : ℤˣ, ∑ s' : ℤˣ, signDir t s s' y) ∂Q := by
    rw [integral_finset_sum (f := fun s : ℤˣ => fun y : E => ∑ s' : ℤˣ, signDir t s s' y)
      Finset.univ (fun s _ => integrable_finset_sum Finset.univ fun s' _ => hint s s')]
    exact (Finset.sum_congr rfl fun s _ =>
      integral_finset_sum (f := fun s' : ℤˣ => fun y : E => signDir t s s' y)
        Finset.univ (fun s' _ => hint s s')).symm
  rw [h1]
  have hzero : ∀ y : E, (∑ s : ℤˣ, ∑ s' : ℤˣ, signDir t s s' y) = 0 := by
    intro y
    rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from UnitsInt.univ]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
      Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    unfold signDir
    push_cast
    ring
  have hz : ∫ y, (∑ s : ℤˣ, ∑ s' : ℤˣ, signDir t s s' y) ∂Q = ∫ _y : E, (0 : ℝ) ∂Q :=
    integral_congr_ae (Filter.Eventually.of_forall hzero)
  rw [hz, integral_zero]

/-- The four sign directions have total second moment `4(A+B)`. -/
private lemma sum_integral_signDir_sq (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ2 : MemLp id 2 Q) (t : WithLp 2 (E × E)) :
    ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, (signDir t s s' y) ^ 2 ∂Q
      = 4 * ((∫ y, ⟪y, (WithLp.ofLp t).1⟫ ^ 2 ∂Q) + ∫ y, ⟪y, (WithLp.ofLp t).2⟫ ^ 2 ∂Q) := by
  classical
  have hint : ∀ s s' : ℤˣ, Integrable (fun y => (signDir t s s' y) ^ 2) Q := fun s s' => by
    have := (memLp_signDir Q hQ2 t s s').integrable_sq
    simpa using this
  have hint1 : Integrable (fun y : E => ⟪y, (WithLp.ofLp t).1⟫ ^ 2) Q := by
    simpa using (memLp_inner_right Q hQ2 (WithLp.ofLp t).1).integrable_sq
  have hint2 : Integrable (fun y : E => ⟪y, (WithLp.ofLp t).2⟫ ^ 2) Q := by
    simpa using (memLp_inner_right Q hQ2 (WithLp.ofLp t).2).integrable_sq
  have h1 : ∑ s : ℤˣ, ∑ s' : ℤˣ, ∫ y, (signDir t s s' y) ^ 2 ∂Q
      = ∫ y, (∑ s : ℤˣ, ∑ s' : ℤˣ, (signDir t s s' y) ^ 2) ∂Q := by
    rw [integral_finset_sum
      (f := fun s : ℤˣ => fun y : E => ∑ s' : ℤˣ, (signDir t s s' y) ^ 2)
      Finset.univ (fun s _ => integrable_finset_sum Finset.univ fun s' _ => hint s s')]
    exact (Finset.sum_congr rfl fun s _ =>
      integral_finset_sum (f := fun s' : ℤˣ => fun y : E => (signDir t s s' y) ^ 2)
        Finset.univ (fun s' _ => hint s s')).symm
  rw [h1]
  have hpt : ∀ y : E, (∑ s : ℤˣ, ∑ s' : ℤˣ, (signDir t s s' y) ^ 2)
      = 4 * (⟪y, (WithLp.ofLp t).1⟫ ^ 2 + ⟪y, (WithLp.ofLp t).2⟫ ^ 2) := by
    intro y
    rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from UnitsInt.univ]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    rw [Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1),
      Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    unfold signDir
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_add hint1 hint2]

/-! ### The bivariate sign-change central limit theorem -/

/-- **The bivariate sign-change randomization central limit theorem.** For i.i.d. data `Q`
with finite second moments in a finite-dimensional real inner-product space, the normalized
sums recomputed at **two independent uniform sign patterns** converge jointly in law to a
*product* `ν ⊗ ν`, where `ν` is the centred Gaussian whose characteristic function is
`exp(−∫⟪y,v⟫²dQ / 2)`.

No mean-zero assumption is needed: averaging over the sign group symmetrizes each summand,
so the first-order term of the expansion cancels identically and only the second moment
survives. The asymptotic independence of the two components is exact at every finite `n` —
it is the factorization of the four-term sign average, not a limiting phenomenon. -/
theorem weakConverges_randPairLaw_signSum [FiniteDimensional ℝ E]
    (Q : Measure E) [IsProbabilityMeasure Q]
    -- USER-INPUT: finite second moments of the observation
    (hQ2 : MemLp id 2 Q) (ν : Measure E) [IsProbabilityMeasure ν]
    -- USER-INPUT: `ν` is the centred Gaussian with the second-moment form of `Q`
    (hν : ∀ v : E, charFun ν v = Complex.exp (-((∫ y, ⟪y, v⟫ ^ 2 ∂Q : ℝ) : ℂ) / 2)) :
    WeakConverges (fun n => randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
        (Measure.pi fun _ : Fin n => Q)) (ν.prod ν) := by
  classical
  -- Measurability of the action and of the statistic, so that `randPairLaw` is a probability.
  have hsmul : ∀ (n : ℕ) (ε : Fin n → ℤˣ), Measurable fun x : Fin n → E => ε • x := by
    intro n ε
    refine measurable_pi_lambda _ fun i => ?_
    simp only [signChange_smul_apply_vec]
    exact (measurable_pi_apply i).const_smul _
  have hTmeas : ∀ n : ℕ,
      Measurable fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i := fun n =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul _
  haveI hprob : ∀ n : ℕ, IsProbabilityMeasure (randPairLaw (Fin n → ℤˣ)
      (fun x : Fin n → E => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
      (Measure.pi fun _ : Fin n => Q)) := fun n =>
    isProbabilityMeasure_randPairLaw _ _ _ (hTmeas n) (hsmul n)
  refine weakConverges_prod_of_tendsto_charFun (fun t => ?_)
  simp_rw [charFun_randPairLaw_signSum Q]
  -- Notation for the two second moments and the four sign directions.
  set A : ℝ := ∫ y, ⟪y, (WithLp.ofLp t).1⟫ ^ 2 ∂Q with hA
  set B : ℝ := ∫ y, ⟪y, (WithLp.ofLp t).2⟫ ^ 2 ∂Q with hB
  set RR : ℤˣ → ℤˣ → ℝ → ℂ := fun s s' v => charFun (Q.map (signDir t s s')) v
    - (1 + (Q[signDir t s s'] : ℝ) * v * Complex.I
      - (Q[(signDir t s s') ^ 2] : ℝ) * v ^ 2 / 2) with hRR
  -- Identify the limit.
  have hlim : charFun ν (WithLp.ofLp t).1 * charFun ν (WithLp.ofLp t).2
      = Complex.exp (-(((A + B : ℝ)) : ℂ) / 2) := by
    rw [hν, hν, ← Complex.exp_add, ← hA, ← hB]
    push_cast
    ring_nf
  rw [hlim]
  refine Complex.tendsto_pow_exp_of_isLittleO_sub_add_div _ ?_
  -- Each of the four directions has a second-order expansion; compose with `n^{-1/2} → 0`.
  have hu0 : Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hRo : ∀ s s' : ℤˣ, (fun n : ℕ => RR s s' ((Real.sqrt (n : ℝ))⁻¹)) =o[atTop]
      fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹) ^ 2 := by
    intro s s'
    exact (isLittleO_charFun_taylor (measurable_signDir t s s').aemeasurable
      (memLp_id_map_signDir Q hQ2 t s s')).comp_tendsto hu0
  have hsum : (fun n : ℕ => (4 : ℂ)⁻¹ * (RR 1 1 ((Real.sqrt (n : ℝ))⁻¹)
        + RR 1 (-1) ((Real.sqrt (n : ℝ))⁻¹)
        + (RR (-1) 1 ((Real.sqrt (n : ℝ))⁻¹) + RR (-1) (-1) ((Real.sqrt (n : ℝ))⁻¹))))
      =o[atTop] fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹) ^ 2 :=
    (((hRo 1 1).add (hRo 1 (-1))).add ((hRo (-1) 1).add (hRo (-1) (-1)))).const_mul_left _
  -- The moment identities, written out over the four sign pairs.
  have hv2 : ∀ n : ℕ, ((Real.sqrt (n : ℝ))⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
    intro n
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hMeq : ∀ s s' : ℤˣ, Q[(signDir t s s') ^ 2] = ∫ y, (signDir t s s' y) ^ 2 ∂Q :=
    fun s s' => rfl
  have hm4 : Q[signDir t 1 1] + Q[signDir t 1 (-1)]
      + (Q[signDir t (-1) 1] + Q[signDir t (-1) (-1)]) = 0 := by
    rw [← sum_units_int (fun s s' => ∫ y, signDir t s s' y ∂Q)]
    exact sum_integral_signDir Q hQ2 t
  have hM4 : Q[(signDir t 1 1) ^ 2] + Q[(signDir t 1 (-1)) ^ 2]
      + (Q[(signDir t (-1) 1) ^ 2] + Q[(signDir t (-1) (-1)) ^ 2]) = 4 * (A + B) := by
    simp_rw [hMeq]
    rw [← sum_units_int (fun s s' => ∫ y, (signDir t s s' y) ^ 2 ∂Q)]
    exact sum_integral_signDir_sq Q hQ2 t
  -- The algebraic identity: the four remainders reassemble the required difference.
  have key : ∀ n : ℕ,
      (4 : ℂ)⁻¹ * (∑ s : ℤˣ, ∑ s' : ℤˣ, charFun (Q.map (signDir t s s')) ((Real.sqrt (n : ℝ))⁻¹))
          - (1 + -(((A + B : ℝ)) : ℂ) / 2 / (n : ℂ))
        = (4 : ℂ)⁻¹ * (RR 1 1 ((Real.sqrt (n : ℝ))⁻¹) + RR 1 (-1) ((Real.sqrt (n : ℝ))⁻¹)
          + (RR (-1) 1 ((Real.sqrt (n : ℝ))⁻¹) + RR (-1) (-1) ((Real.sqrt (n : ℝ))⁻¹))) := by
    intro n
    have hvsq : (((Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) ^ 2 = 1 / (n : ℂ) := by
      rw [← Complex.ofReal_pow, hv2 n]
      push_cast
      rw [one_div]
    have hm4' : ((Q[signDir t 1 1] : ℝ) : ℂ) + ((Q[signDir t 1 (-1)] : ℝ) : ℂ)
        + (((Q[signDir t (-1) 1] : ℝ) : ℂ) + ((Q[signDir t (-1) (-1)] : ℝ) : ℂ)) = 0 := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add, hm4]
      simp
    have hM4' : ((Q[(signDir t 1 1) ^ 2] : ℝ) : ℂ) + ((Q[(signDir t 1 (-1)) ^ 2] : ℝ) : ℂ)
        + (((Q[(signDir t (-1) 1) ^ 2] : ℝ) : ℂ)
          + ((Q[(signDir t (-1) (-1)) ^ 2] : ℝ) : ℂ)) = 4 * (((A + B : ℝ)) : ℂ) := by
      rw [← Complex.ofReal_add, ← Complex.ofReal_add, ← Complex.ofReal_add, hM4]
      push_cast
      ring
    rw [sum_units_int (fun s s' => charFun (Q.map (signDir t s s')) ((Real.sqrt (n : ℝ))⁻¹))]
    simp only [hRR]
    rw [hvsq]
    linear_combination ((4 : ℂ)⁻¹ * ((Real.sqrt (n : ℝ))⁻¹ : ℝ) * Complex.I) * hm4'
      - ((4 : ℂ)⁻¹ * (1 / (n : ℂ)) / 2) * hM4'
  -- Transfer the little-o statement along the identity and the comparison function.
  rw [← Asymptotics.isLittleO_norm_right]
  have hnorm : (fun n : ℕ => ‖(1 : ℂ) / (n : ℂ)‖) = fun n : ℕ => ((Real.sqrt (n : ℝ))⁻¹) ^ 2 := by
    funext n
    rw [hv2 n, norm_div, Complex.norm_natCast, norm_one, one_div]
  rw [hnorm]
  exact hsum.congr' (Filter.Eventually.of_forall fun n => (key n).symm) Filter.EventuallyEq.rfl

end SignSum

/-! ### A Slutsky principle for doubly randomized laws -/

section Slutsky

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]

/-- `‖e^{iα} − e^{iβ}‖ ≤ min 2 (2|α − β|)`: the two crude bounds a randomization Slutsky
argument needs — uniform boundedness, and Lipschitz control by the phase difference. -/
private lemma norm_exp_sub_exp_le (α β : ℝ) :
    ‖Complex.exp ((α : ℂ) * Complex.I) - Complex.exp ((β : ℂ) * Complex.I)‖
      ≤ min 2 (2 * |α - β|) := by
  have hnα : ‖Complex.exp ((α : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hnβ : ‖Complex.exp ((β : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖Complex.exp ((α : ℂ) * Complex.I) - Complex.exp ((β : ℂ) * Complex.I)‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [hnα, hnβ]
    norm_num
  refine le_min h2 ?_
  have hnormcast : ‖((α - β : ℝ) : ℂ) * Complex.I‖ = |α - β| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rcases le_or_gt |α - β| 1 with hle | hgt
  · have hfac : Complex.exp ((α : ℂ) * Complex.I) - Complex.exp ((β : ℂ) * Complex.I)
        = Complex.exp ((β : ℂ) * Complex.I)
          * (Complex.exp (((α - β : ℝ) : ℂ) * Complex.I) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add,
        show ((β : ℂ) * Complex.I + ((α - β : ℝ) : ℂ) * Complex.I) = (α : ℂ) * Complex.I from by
          push_cast; ring]
    rw [hfac, norm_mul, hnβ, one_mul]
    have := Complex.norm_exp_sub_one_le (x := ((α - β : ℝ) : ℂ) * Complex.I)
      (by rw [hnormcast]; exact hle)
    rwa [hnormcast] at this
  · refine le_trans h2 ?_
    nlinarith

/-- If a nonnegative statistic vanishes in probability, so does the expectation of its
truncated multiple `min 2 (c·D)`. -/
private lemma tendsto_integral_min_of_tendstoInProb {𝓨 : ℕ → Type*}
    [∀ n, MeasurableSpace (𝓨 n)] (P : ∀ n, Measure (𝓨 n)) [∀ n, IsProbabilityMeasure (P n)]
    (D : ∀ n, 𝓨 n → ℝ) (hD : ∀ n, Measurable (D n)) (hnn : ∀ n x, 0 ≤ D n x)
    (hrem : ∀ δ > (0 : ℝ), Tendsto (fun n => (P n).real {x | δ ≤ D n x}) atTop (𝓝 0))
    {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n => ∫ x, min 2 (c * D n x) ∂(P n)) atTop (𝓝 0) := by
  have hmeas : ∀ n, Measurable fun x : 𝓨 n => min 2 (c * D n x) := fun n =>
    measurable_const.min ((hD n).const_mul c)
  have hbdd : ∀ (n : ℕ) (x : 𝓨 n), ‖min 2 (c * D n x)‖ ≤ 2 := by
    intro n x
    have h0 : 0 ≤ min 2 (c * D n x) := le_min (by norm_num) (mul_nonneg hc (hnn n x))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact min_le_left _ _
  have hint : ∀ n, Integrable (fun x : 𝓨 n => min 2 (c * D n x)) (P n) := fun n =>
    Integrable.mono' (integrable_const (2 : ℝ)) (hmeas n).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbdd n))
  have hnn' : ∀ n, 0 ≤ ∫ x, min 2 (c * D n x) ∂(P n) := fun n =>
    integral_nonneg fun x => le_min (by norm_num) (mul_nonneg hc (hnn n x))
  -- The key inequality, for every truncation level `δ`.
  have hkey : ∀ (δ : ℝ), 0 < δ → ∀ n,
      ∫ x, min 2 (c * D n x) ∂(P n) ≤ c * δ + 2 * (P n).real {x | δ ≤ D n x} := by
    intro δ hδ n
    have hset : MeasurableSet {x : 𝓨 n | δ ≤ D n x} :=
      measurableSet_le measurable_const (hD n)
    have hone : Integrable (1 : 𝓨 n → ℝ) (P n) := integrable_const 1
    have hptwise : ∀ x : 𝓨 n, min 2 (c * D n x)
        ≤ c * δ + 2 * Set.indicator {x : 𝓨 n | δ ≤ D n x} (1 : 𝓨 n → ℝ) x := by
      intro x
      by_cases hx : δ ≤ D n x
      · have hval : Set.indicator {x : 𝓨 n | δ ≤ D n x} (1 : 𝓨 n → ℝ) x = 1 :=
          Set.indicator_of_mem (s := {x : 𝓨 n | δ ≤ D n x}) hx (1 : 𝓨 n → ℝ)
        rw [hval]
        have h2' : min 2 (c * D n x) ≤ 2 := min_le_left _ _
        nlinarith [mul_nonneg hc hδ.le]
      · push_neg at hx
        have hind : (0 : ℝ) ≤ Set.indicator {x : 𝓨 n | δ ≤ D n x} (1 : 𝓨 n → ℝ) x :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) x
        have h2' : min 2 (c * D n x) ≤ c * D n x := min_le_right _ _
        nlinarith
    have hind_int : Integrable
        (fun x : 𝓨 n => c * δ + 2 * Set.indicator {x : 𝓨 n | δ ≤ D n x} (1 : 𝓨 n → ℝ) x)
        (P n) :=
      (integrable_const _).add ((hone.indicator hset).const_mul 2)
    calc ∫ x, min 2 (c * D n x) ∂(P n)
        ≤ ∫ x, (c * δ + 2 * Set.indicator {x : 𝓨 n | δ ≤ D n x} (1 : 𝓨 n → ℝ) x)
            ∂(P n) :=
          integral_mono (hint n) hind_int hptwise
      _ = c * δ + 2 * (P n).real {x | δ ≤ D n x} := by
          rw [integral_add (integrable_const _) ((hone.indicator hset).const_mul 2),
            integral_const, integral_const_mul, integral_indicator_one hset]
          simp
  -- Conclude by making `δ` small.
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  set δ : ℝ := ε / (2 * (c + 1)) with hδdef
  have hcpos : (0 : ℝ) < c + 1 := by linarith
  have hδpos : 0 < δ := by positivity
  have hcδ : c * δ < ε / 2 := by
    have hfac : c * δ = (c / (c + 1)) * (ε / 2) := by
      rw [hδdef]; field_simp
    have hlt : c / (c + 1) < 1 := by rw [div_lt_one hcpos]; linarith
    calc c * δ = (c / (c + 1)) * (ε / 2) := hfac
      _ < 1 * (ε / 2) := mul_lt_mul_of_pos_right hlt (by positivity)
      _ = ε / 2 := one_mul _
  have hev := (hrem δ hδpos).eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 4 by positivity))
  filter_upwards [hev] with n hn
  have hb := hkey δ hδpos n
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn' n)]
  linarith

/-- The one-step truncation estimate behind the previous lemma, isolated so that the
group-averaged variant can reuse it: `∫ min 2 (c·D) ≤ cδ + 2·P{D ≥ δ}`. -/
private lemma integral_min_le {𝓨 : Type*} [MeasurableSpace 𝓨] (P : Measure 𝓨)
    [IsProbabilityMeasure P] (D : 𝓨 → ℝ) (hD : Measurable D) (hnn : ∀ x, 0 ≤ D x)
    {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∫ x, min 2 (c * D x) ∂P ≤ c * δ + 2 * P.real {x | δ ≤ D x} := by
  have hmeas : Measurable fun x : 𝓨 => min 2 (c * D x) := measurable_const.min (hD.const_mul c)
  have hbdd : ∀ x : 𝓨, ‖min 2 (c * D x)‖ ≤ 2 := by
    intro x
    have h0 : 0 ≤ min 2 (c * D x) := le_min (by norm_num) (mul_nonneg hc (hnn x))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact min_le_left _ _
  have hint : Integrable (fun x : 𝓨 => min 2 (c * D x)) P :=
    Integrable.mono' (integrable_const (2 : ℝ)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have hset : MeasurableSet {x : 𝓨 | δ ≤ D x} := measurableSet_le measurable_const hD
  have hone : Integrable (1 : 𝓨 → ℝ) P := integrable_const 1
  have hptwise : ∀ x : 𝓨, min 2 (c * D x)
      ≤ c * δ + 2 * Set.indicator {x : 𝓨 | δ ≤ D x} (1 : 𝓨 → ℝ) x := by
    intro x
    by_cases hx : δ ≤ D x
    · have hval : Set.indicator {x : 𝓨 | δ ≤ D x} (1 : 𝓨 → ℝ) x = 1 :=
        Set.indicator_of_mem (s := {x : 𝓨 | δ ≤ D x}) hx (1 : 𝓨 → ℝ)
      rw [hval]
      have h2' : min 2 (c * D x) ≤ 2 := min_le_left _ _
      nlinarith [mul_nonneg hc hδ.le]
    · have hx' : D x < δ := not_le.mp hx
      have hind : (0 : ℝ) ≤ Set.indicator {x : 𝓨 | δ ≤ D x} (1 : 𝓨 → ℝ) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) x
      have h2' : min 2 (c * D x) ≤ c * D x := min_le_right _ _
      nlinarith [mul_nonneg hc (sub_nonneg.mpr hx'.le)]
  have hind_int : Integrable
      (fun x : 𝓨 => c * δ + 2 * Set.indicator {x : 𝓨 | δ ≤ D x} (1 : 𝓨 → ℝ) x) P :=
    (integrable_const _).add ((hone.indicator hset).const_mul 2)
  calc ∫ x, min 2 (c * D x) ∂P
      ≤ ∫ x, (c * δ + 2 * Set.indicator {x : 𝓨 | δ ≤ D x} (1 : 𝓨 → ℝ) x) ∂P :=
        integral_mono hint hind_int hptwise
    _ = c * δ + 2 * P.real {x | δ ≤ D x} := by
        rw [integral_add (integrable_const _) ((hone.indicator hset).const_mul 2),
          integral_const, integral_const_mul, integral_indicator_one hset]
        simp

/-- **Group-averaged form of `tendsto_integral_min_of_tendstoInProb`.** If the *mixture over
the group* of the remainder probabilities vanishes, so does the mixture of the truncated
expectations. This is what replaces the invariance step when the data law is not assumed
group invariant. -/
private lemma tendsto_avg_integral_min_of_tendstoInProb {𝓨 : ℕ → Type*}
    [∀ n, MeasurableSpace (𝓨 n)] {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, Fintype (G n)]
    (P : ∀ n, Measure (𝓨 n)) [∀ n, IsProbabilityMeasure (P n)]
    (D : ∀ n, G n → 𝓨 n → ℝ) (hD : ∀ (n : ℕ) (g : G n), Measurable (D n g))
    (hnn : ∀ (n : ℕ) (g : G n) (x : 𝓨 n), 0 ≤ D n g x)
    (hrem : ∀ δ > (0 : ℝ), Tendsto (fun n => (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, (P n).real {x | δ ≤ D n g x}) atTop (𝓝 0))
    {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun n => (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, ∫ x, min 2 (c * D n g x) ∂(P n)) atTop (𝓝 0) := by
  have hcardpos : ∀ n : ℕ, (0 : ℝ) < (Fintype.card (G n) : ℝ) := fun n => by
    exact_mod_cast Fintype.card_pos
  have hnn' : ∀ n : ℕ, 0 ≤ (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, ∫ x, min 2 (c * D n g x) ∂(P n) := by
    intro n
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => ?_)
    exact integral_nonneg fun x => le_min (by norm_num) (mul_nonneg hc (hnn n g x))
  have hkey : ∀ (δ : ℝ), 0 < δ → ∀ n : ℕ,
      (Fintype.card (G n) : ℝ)⁻¹ * ∑ g : G n, ∫ x, min 2 (c * D n g x) ∂(P n)
        ≤ c * δ + 2 * ((Fintype.card (G n) : ℝ)⁻¹ *
            ∑ g : G n, (P n).real {x | δ ≤ D n g x}) := by
    intro δ hδ n
    have hsum : ∑ g : G n, ∫ x, min 2 (c * D n g x) ∂(P n)
        ≤ ∑ g : G n, (c * δ + 2 * (P n).real {x | δ ≤ D n g x}) :=
      Finset.sum_le_sum fun g _ => integral_min_le (P n) (D n g) (hD n g) (hnn n g) hc hδ
    have hsplit : ∑ g : G n, (c * δ + 2 * (P n).real {x | δ ≤ D n g x})
        = (Fintype.card (G n) : ℝ) * (c * δ)
          + 2 * ∑ g : G n, (P n).real {x | δ ≤ D n g x} := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.mul_sum]
    have hmul := mul_le_mul_of_nonneg_left (hsum.trans hsplit.le)
      (le_of_lt (inv_pos.mpr (hcardpos n)))
    refine hmul.trans (le_of_eq ?_)
    field_simp
  rw [NormedAddCommGroup.tendsto_nhds_zero]
  intro ε hε
  set δ : ℝ := ε / (2 * (c + 1)) with hδdef
  have hcpos : (0 : ℝ) < c + 1 := by linarith
  have hδpos : 0 < δ := by positivity
  have hcδ : c * δ < ε / 2 := by
    have hfac : c * δ = (c / (c + 1)) * (ε / 2) := by rw [hδdef]; field_simp
    have hlt : c / (c + 1) < 1 := by rw [div_lt_one hcpos]; linarith
    calc c * δ = (c / (c + 1)) * (ε / 2) := hfac
      _ < 1 * (ε / 2) := mul_lt_mul_of_pos_right hlt (by positivity)
      _ = ε / 2 := one_mul _
  have hev := (hrem δ hδpos).eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 4 by positivity))
  filter_upwards [hev] with n hn
  have hb := hkey δ hδpos n
  rw [Real.norm_eq_abs, abs_of_nonneg (hnn' n)]
  linarith

/-- Subadditivity of the truncation `min 2 ·` on nonnegative arguments. -/
private lemma min_two_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 2 (a + b) ≤ min 2 a + min 2 b := by
  rcases le_or_gt a 2 with h1 | h1
  · rcases le_or_gt b 2 with h2 | h2
    · rw [min_eq_right h1, min_eq_right h2]
      exact min_le_right _ _
    · rw [min_eq_left h2.le]
      have := min_le_left (2 : ℝ) (a + b)
      have h0 : 0 ≤ min 2 a := le_min (by norm_num) ha
      linarith
  · rw [min_eq_left h1.le]
    have := min_le_left (2 : ℝ) (a + b)
    have h0 : 0 ≤ min 2 b := le_min (by norm_num) hb
    linarith

/-- **Slutsky for doubly randomized laws, mixture form.** If the statistic `Tₙ` differs from
a reference statistic `Lₙ` by a remainder that vanishes in probability *at randomized data*
— i.e. the group mixture `|Gₙ|⁻¹ ∑_g Pₙ{‖Tₙ(g·x) − Lₙ(g·x)‖ ≥ δ}` tends to `0` — then the
two doubly randomized laws have the same weak limits.

This is the transfer that turns an *asymptotically linear* statistic into its linear part
inside a randomization limit; it is proved at the level of characteristic functions
(`‖e^{iα} − e^{iβ}‖ ≤ min 2 (2|α−β|)`), which is what makes the group average collapse.

No group invariance of the data law is assumed. That matters: the applications in
`Randomization/SlutskyRandomization` and `Randomization/Studentized` studentize by a scale
which is *not* group invariant, and their hypotheses are stated as exactly this mixture.
The invariant special case is `weakConverges_randPairLaw_of_tendstoInProb` below. -/
theorem weakConverges_randPairLaw_of_tendstoInProb_avg
    {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓧 n)]
    (P : ∀ n, Measure (𝓧 n)) [∀ n, IsProbabilityMeasure (P n)]
    (T L : ∀ n, 𝓧 n → E) {ν : Measure (E × E)} [IsProbabilityMeasure ν]
    -- USER-INPUT: both statistics are measurable (data regularity)
    (hT : ∀ n, Measurable (T n)) (hL : ∀ n, Measurable (L n))
    -- USER-INPUT: the group acts measurably
    (hsmul : ∀ (n : ℕ) (g : G n), Measurable fun x : 𝓧 n => g • x)
    -- USER-INPUT: the remainder vanishes in probability at randomized data
    (hrem : ∀ δ > (0 : ℝ), Tendsto (fun n => (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, (P n).real {x | δ ≤ ‖T n (g • x) - L n (g • x)‖}) atTop (𝓝 0))
    -- USER-INPUT: the reference statistic already has the randomized limit `ν`
    (hconv : WeakConverges (fun n => randPairLaw (G n) (L n) (P n)) ν) :
    WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) ν := by
  classical
  haveI hpT : ∀ n, IsProbabilityMeasure (randPairLaw (G n) (T n) (P n)) := fun n =>
    isProbabilityMeasure_randPairLaw _ _ _ (hT n) (hsmul n)
  haveI hpL : ∀ n, IsProbabilityMeasure (randPairLaw (G n) (L n) (P n)) := fun n =>
    isProbabilityMeasure_randPairLaw _ _ _ (hL n) (hsmul n)
  rw [weakConverges_map_toLp_iff] at hconv ⊢
  haveI hmT : ∀ n, IsProbabilityMeasure
      ((randPairLaw (G n) (T n) (P n)).map (WithLp.toLp (V := E × E) 2)) := fun n =>
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
  haveI hmL : ∀ n, IsProbabilityMeasure
      ((randPairLaw (G n) (L n) (P n)).map (WithLp.toLp (V := E × E) 2)) := fun n =>
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
  haveI hmν : IsProbabilityMeasure (ν.map (WithLp.toLp (V := E × E) 2)) :=
    Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
  refine weakConverges_of_tendsto_charFun (fun t => ?_)
  have hlim := tendsto_charFun_of_weakConverges hconv t
  -- The bounded test function on the product.
  set F : E × E → ℂ := fun z =>
    Complex.exp (((⟪z.1, (WithLp.ofLp t).1⟫ + ⟪z.2, (WithLp.ofLp t).2⟫ : ℝ) : ℂ) * Complex.I)
    with hFdef
  have hFcont : Continuous F := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp
      ((continuous_fst.inner continuous_const).add (continuous_snd.inner continuous_const))
  have hFb : ∀ z, ‖F z‖ ≤ 1 := fun z => le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hcontExp : Continuous fun y : WithLp 2 (E × E) =>
      Complex.exp (((⟪y, t⟫ : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      ((continuous_id (X := WithLp 2 (E × E))).inner continuous_const)).mul continuous_const)
  have hchar : ∀ (S : ∀ n, 𝓧 n → E), (∀ n, Measurable (S n)) → ∀ n : ℕ,
      charFun ((randPairLaw (G n) (S n) (P n)).map (WithLp.toLp 2)) t
        = ((Fintype.card (G n) : ℂ) ^ 2)⁻¹ *
          ∑ g : G n, ∑ g' : G n, ∫ x, F (S n (g • x), S n (g' • x)) ∂(P n) := by
    intro S hS n
    rw [charFun_apply, integral_map (WithLp.measurable_toLp 2 (E × E)).aemeasurable
      hcontExp.aestronglyMeasurable]
    exact integral_randPairLaw (P n) (S n) (fun g => (hS n).comp (hsmul n g)) F
      hFcont.measurable hFb
  -- The comparison function.
  set c₁ : ℝ := 2 * ‖(WithLp.ofLp t).1‖ with hc₁
  set c₂ : ℝ := 2 * ‖(WithLp.ofLp t).2‖ with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set B : ℕ → ℝ := fun n => (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, ∫ x, min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖) ∂(P n)
    + (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, ∫ x, min 2 (c₂ * ‖T n (g • x) - L n (g • x)‖) ∂(P n) with hBdef
  have hDmeas : ∀ n, Measurable fun x : 𝓧 n => ‖T n x - L n x‖ :=
    fun n => ((hT n).sub (hL n)).norm
  have hDsmul : ∀ (n : ℕ) (g : G n),
      Measurable fun x : 𝓧 n => ‖T n (g • x) - L n (g • x)‖ :=
    fun n g => (hDmeas n).comp (hsmul n g)
  have hBlim : Tendsto B atTop (𝓝 0) := by
    have h1 := tendsto_avg_integral_min_of_tendstoInProb P
      (fun n g x => ‖T n (g • x) - L n (g • x)‖) hDsmul (fun n g x => norm_nonneg _) hrem hc₁0
    have h2 := tendsto_avg_integral_min_of_tendstoInProb P
      (fun n g x => ‖T n (g • x) - L n (g • x)‖) hDsmul (fun n g x => norm_nonneg _) hrem hc₂0
    simpa only [hBdef, add_zero] using h1.add h2
  -- Integrability bookkeeping for the pointwise bound.
  have hFint : ∀ (S : ∀ n, 𝓧 n → E), (∀ n, Measurable (S n)) → ∀ (n : ℕ) (g g' : G n),
      Integrable (fun x : 𝓧 n => F (S n (g • x), S n (g' • x))) (P n) := by
    intro S hS n g g'
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (Filter.Eventually.of_forall
      fun x => hFb _)
    exact (hFcont.measurable.comp (((hS n).comp (hsmul n g)).prodMk
      ((hS n).comp (hsmul n g')))).aestronglyMeasurable
  have hminmeas : ∀ (n : ℕ) (c : ℝ) (g : G n),
      Measurable fun x : 𝓧 n => min 2 (c * ‖T n (g • x) - L n (g • x)‖) :=
    fun n c g => measurable_const.min (((hDmeas n).comp (hsmul n g)).const_mul c)
  have hminint : ∀ (n : ℕ) (c : ℝ) (g : G n), 0 ≤ c →
      Integrable (fun x : 𝓧 n => min 2 (c * ‖T n (g • x) - L n (g • x)‖)) (P n) := by
    intro n c g hc
    refine Integrable.mono' (integrable_const (2 : ℝ)) (hminmeas n c g).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ min 2 (c * ‖T n (g • x) - L n (g • x)‖) :=
      le_min (by norm_num) (mul_nonneg hc (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact min_le_left _ _
  -- The per-`n` estimate.
  have hstep : ∀ n : ℕ,
      ‖charFun ((randPairLaw (G n) (T n) (P n)).map (WithLp.toLp 2)) t
        - charFun ((randPairLaw (G n) (L n) (P n)).map (WithLp.toLp 2)) t‖ ≤ B n := by
    intro n
    have hcard : (0 : ℝ) < (Fintype.card (G n) : ℝ) := by exact_mod_cast Fintype.card_pos
    have hcardne : (Fintype.card (G n) : ℝ) ≠ 0 := ne_of_gt hcard
    have hterm : ∀ g g' : G n,
        ‖∫ x, (F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))) ∂(P n)‖
          ≤ (∫ x, min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖) ∂(P n))
            + ∫ x, min 2 (c₂ * ‖T n (g' • x) - L n (g' • x)‖) ∂(P n) := by
      intro g g'
      have hptw : ∀ x : 𝓧 n,
          ‖F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))‖
            ≤ min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖)
              + min 2 (c₂ * ‖T n (g' • x) - L n (g' • x)‖) := by
        intro x
        refine le_trans (norm_exp_sub_exp_le _ _) ?_
        refine le_trans (min_le_min_left _ ?_)
          (min_two_add_le (by positivity) (by positivity))
        have hexp : (⟪T n (g • x), (WithLp.ofLp t).1⟫ + ⟪T n (g' • x), (WithLp.ofLp t).2⟫)
            - (⟪L n (g • x), (WithLp.ofLp t).1⟫ + ⟪L n (g' • x), (WithLp.ofLp t).2⟫)
            = ⟪T n (g • x) - L n (g • x), (WithLp.ofLp t).1⟫
              + ⟪T n (g' • x) - L n (g' • x), (WithLp.ofLp t).2⟫ := by
          rw [inner_sub_left, inner_sub_left]; ring
        rw [hexp]
        have hb1 : |⟪T n (g • x) - L n (g • x), (WithLp.ofLp t).1⟫|
            ≤ ‖T n (g • x) - L n (g • x)‖ * ‖(WithLp.ofLp t).1‖ := abs_real_inner_le_norm _ _
        have hb2 : |⟪T n (g' • x) - L n (g' • x), (WithLp.ofLp t).2⟫|
            ≤ ‖T n (g' • x) - L n (g' • x)‖ * ‖(WithLp.ofLp t).2‖ := abs_real_inner_le_norm _ _
        have habs := abs_add_le (⟪T n (g • x) - L n (g • x), (WithLp.ofLp t).1⟫)
          (⟪T n (g' • x) - L n (g' • x), (WithLp.ofLp t).2⟫)
        rw [hc₁, hc₂]
        nlinarith [abs_nonneg (⟪T n (g • x) - L n (g • x), (WithLp.ofLp t).1⟫),
          abs_nonneg (⟪T n (g' • x) - L n (g' • x), (WithLp.ofLp t).2⟫)]
      have hdiffint : Integrable
          (fun x : 𝓧 n => F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x)))
          (P n) := (hFint T hT n g g').sub (hFint L hL n g g')
      calc ‖∫ x, (F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))) ∂(P n)‖
          ≤ ∫ x, ‖F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))‖ ∂(P n) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ x, (min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖)
              + min 2 (c₂ * ‖T n (g' • x) - L n (g' • x)‖)) ∂(P n) :=
            integral_mono hdiffint.norm
              ((hminint n c₁ g hc₁0).add (hminint n c₂ g' hc₂0)) hptw
        _ = _ := integral_add (hminint n c₁ g hc₁0) (hminint n c₂ g' hc₂0)
    have hsum : (∑ g : G n, ∑ g' : G n, ∫ x, F (T n (g • x), T n (g' • x)) ∂(P n))
        - ∑ g : G n, ∑ g' : G n, ∫ x, F (L n (g • x), L n (g' • x)) ∂(P n)
        = ∑ g : G n, ∑ g' : G n,
            ∫ x, (F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))) ∂(P n) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun g' _ =>
        (integral_sub (hFint T hT n g g') (hFint L hL n g g')).symm
    rw [hchar T hT n, hchar L hL n, ← mul_sub, hsum, norm_mul]
    have hc : ‖((Fintype.card (G n) : ℂ) ^ 2)⁻¹‖ = ((Fintype.card (G n) : ℝ) ^ 2)⁻¹ := by
      rw [norm_inv, norm_pow, Complex.norm_natCast]
    rw [hc]
    have hBmul : (Fintype.card (G n) : ℝ) ^ 2 * B n
        = (Fintype.card (G n) : ℝ) *
            ∑ g : G n, ∫ x, min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖) ∂(P n)
          + (Fintype.card (G n) : ℝ) *
            ∑ g : G n, ∫ x, min 2 (c₂ * ‖T n (g • x) - L n (g • x)‖) ∂(P n) := by
      simp only [hBdef]
      field_simp
    have hnorm : ‖∑ g : G n, ∑ g' : G n,
        ∫ x, (F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))) ∂(P n)‖
        ≤ (Fintype.card (G n) : ℝ) ^ 2 * B n := by
      refine le_trans (norm_sum_le _ _) ?_
      have hinner : ∀ g : G n, ‖∑ g' : G n,
          ∫ x, (F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))) ∂(P n)‖
          ≤ (Fintype.card (G n) : ℝ) *
              ∫ x, min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖) ∂(P n)
            + ∑ g' : G n, ∫ x, min 2 (c₂ * ‖T n (g' • x) - L n (g' • x)‖) ∂(P n) := by
        intro g
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ g' : G n, ‖∫ x, (F (T n (g • x), T n (g' • x))
              - F (L n (g • x), L n (g' • x))) ∂(P n)‖
            ≤ ∑ g' : G n, ((∫ x, min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖) ∂(P n))
                + ∫ x, min 2 (c₂ * ‖T n (g' • x) - L n (g' • x)‖) ∂(P n)) :=
              Finset.sum_le_sum fun g' _ => hterm g g'
          _ = _ := by
              rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc ∑ g : G n, ‖∑ g' : G n,
            ∫ x, (F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))) ∂(P n)‖
          ≤ ∑ g : G n, ((Fintype.card (G n) : ℝ) *
                ∫ x, min 2 (c₁ * ‖T n (g • x) - L n (g • x)‖) ∂(P n)
              + ∑ g' : G n, ∫ x, min 2 (c₂ * ‖T n (g' • x) - L n (g' • x)‖) ∂(P n)) :=
            Finset.sum_le_sum fun g _ => hinner g
        _ = (Fintype.card (G n) : ℝ) ^ 2 * B n := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
              nsmul_eq_mul, hBmul]
    calc ((Fintype.card (G n) : ℝ) ^ 2)⁻¹ * ‖∑ g : G n, ∑ g' : G n,
          ∫ x, (F (T n (g • x), T n (g' • x)) - F (L n (g • x), L n (g' • x))) ∂(P n)‖
        ≤ ((Fintype.card (G n) : ℝ) ^ 2)⁻¹ * ((Fintype.card (G n) : ℝ) ^ 2 * B n) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = B n := by
          rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hdiff : Tendsto (fun n =>
      charFun ((randPairLaw (G n) (T n) (P n)).map (WithLp.toLp 2)) t
        - charFun ((randPairLaw (G n) (L n) (P n)).map (WithLp.toLp 2)) t) atTop (𝓝 0) :=
    squeeze_zero_norm hstep hBlim
  have := hdiff.add hlim
  simpa using this

/-- **Slutsky for doubly randomized laws, invariant case.** The special case of
`weakConverges_randPairLaw_of_tendstoInProb_avg` in which the data law *is* group invariant:
then the remainder probabilities at randomized data all coincide with the remainder
probability at the data itself, so the plain convergence-in-probability hypothesis
suffices. -/
theorem weakConverges_randPairLaw_of_tendstoInProb
    {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
    {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓧 n)]
    (P : ∀ n, Measure (𝓧 n)) [∀ n, IsProbabilityMeasure (P n)]
    (T L : ∀ n, 𝓧 n → E) {ν : Measure (E × E)} [IsProbabilityMeasure ν]
    -- USER-INPUT: both statistics are measurable (data regularity)
    (hT : ∀ n, Measurable (T n)) (hL : ∀ n, Measurable (L n))
    -- USER-INPUT: the group acts measurably
    (hsmul : ∀ (n : ℕ) (g : G n), Measurable fun x : 𝓧 n => g • x)
    -- USER-INPUT: the data law is invariant under the group (the randomization hypothesis)
    (hinv : ∀ (n : ℕ) (g : G n), (P n).map (fun x : 𝓧 n => g • x) = P n)
    -- USER-INPUT: the remainder vanishes in probability
    (hrem : ∀ δ > (0 : ℝ),
      Tendsto (fun n => (P n).real {x | δ ≤ ‖T n x - L n x‖}) atTop (𝓝 0))
    -- USER-INPUT: the reference statistic already has the randomized limit `ν`
    (hconv : WeakConverges (fun n => randPairLaw (G n) (L n) (P n)) ν) :
    WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) ν := by
  refine weakConverges_randPairLaw_of_tendstoInProb_avg P T L hT hL hsmul ?_ hconv
  intro δ hδ
  have hEq : ∀ n : ℕ, (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, (P n).real {x | δ ≤ ‖T n (g • x) - L n (g • x)‖}
        = (P n).real {x | δ ≤ ‖T n x - L n x‖} := by
    intro n
    have hcard : (0 : ℝ) < (Fintype.card (G n) : ℝ) := by exact_mod_cast Fintype.card_pos
    have hset : MeasurableSet {x : 𝓧 n | δ ≤ ‖T n x - L n x‖} :=
      measurableSet_le measurable_const (((hT n).sub (hL n)).norm)
    have hg : ∀ g : G n, (P n).real {x | δ ≤ ‖T n (g • x) - L n (g • x)‖}
        = (P n).real {x | δ ≤ ‖T n x - L n x‖} := by
      intro g
      have hpre : {x : 𝓧 n | δ ≤ ‖T n (g • x) - L n (g • x)‖}
          = (fun x : 𝓧 n => g • x) ⁻¹' {x : 𝓧 n | δ ≤ ‖T n x - L n x‖} := rfl
      rw [hpre, Measure.real, Measure.real, ← Measure.map_apply (hsmul n g) hset, hinv n g]
    simp_rw [hg]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hcard), one_mul]
  exact (hrem δ hδ).congr fun n => (hEq n).symm

end Slutsky

/-! ### Tightness from a weak limit on `ℝ` -/

/-- **A weakly convergent sequence of laws on `ℝ` is uniformly tight.** For every `ε > 0`
there is a threshold `M` beyond which all but finitely many of the laws put mass at most
`ε`.

This is the ingredient that upgrades "the random scaling converges in probability" to "the
*rescaled statistic* converges in probability": the statistic itself is `O_P(1)`, and that
is read off its weak limit rather than assumed. -/
lemma exists_tight_bound_of_weakConverges {μ : ℕ → Measure ℝ}
    [∀ n, IsProbabilityMeasure (μ n)] {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (h : WeakConverges μ ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, (μ n).real {y : ℝ | M ≤ |y|} ≤ ε := by
  classical
  have hmeasA : ∀ c : ℝ, MeasurableSet {y : ℝ | c ≤ |y|} := fun c =>
    measurableSet_le measurable_const continuous_abs.measurable
  -- The tails shrink to the empty set, so some integer threshold already works for `ν`.
  have hanti : Antitone fun k : ℕ => {y : ℝ | (k : ℝ) ≤ |y|} := by
    intro i j hij y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    exact le_trans (by exact_mod_cast hij) hy
  have hinter : (⋂ k : ℕ, {y : ℝ | (k : ℝ) ≤ |y|}) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨k, hk⟩ := exists_nat_gt |y|
    exact ⟨k, hk⟩
  have htend := tendsto_measure_iInter_atTop (μ := ν)
    (fun k : ℕ => (hmeasA (k : ℝ)).nullMeasurableSet) hanti ⟨0, measure_ne_top ν _⟩
  rw [hinter, measure_empty] at htend
  have htendR : Tendsto (fun k : ℕ => ν.real {y : ℝ | (k : ℝ) ≤ |y|}) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (by simp)).comp htend
    simpa [Measure.real, Function.comp] using! this
  obtain ⟨k, hk⟩ :=
    (htendR.eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))).exists
  -- A bounded continuous ramp squeezed between the two tail indicators.
  set φ : ℝ → ℝ := fun y => max 0 (min 1 (|y| - (k : ℝ))) with hφdef
  have hφcont : Continuous φ :=
    continuous_const.max (continuous_const.min (continuous_abs.sub continuous_const))
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => le_max_left _ _
  have hφ1 : ∀ y, φ y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  set f : BoundedContinuousFunction ℝ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨φ, hφcont⟩ 1 (by
    intro x y
    rw [Real.dist_eq, abs_le]
    exact ⟨by simpa using by linarith [hφ0 x, hφ1 y], by simpa using by linarith [hφ1 x, hφ0 y]⟩)
    with hfdef
  have hfval : ∀ y, f y = φ y := fun _ => rfl
  have hfint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], Integrable (fun y => f y) ρ :=
    fun ρ _ => f.integrable ρ
  -- Lower bound: the ramp dominates the indicator of the `k+1` tail.
  have hlow : ∀ (ρ : Measure ℝ) [IsProbabilityMeasure ρ],
      ρ.real {y : ℝ | (k : ℝ) + 1 ≤ |y|} ≤ ∫ y, f y ∂ρ := by
    intro ρ _
    rw [← integral_indicator_one (hmeasA ((k : ℝ) + 1))]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator (hmeasA ((k : ℝ) + 1)))
      (hfint ρ) fun y => ?_
    by_cases hy : (k : ℝ) + 1 ≤ |y|
    · rw [Set.indicator_of_mem (s := {y : ℝ | (k : ℝ) + 1 ≤ |y|}) hy, Pi.one_apply, hfval]
      have h1 : (1 : ℝ) ≤ |y| - (k : ℝ) := by linarith
      change (1 : ℝ) ≤ max 0 (min 1 (|y| - (k : ℝ)))
      rw [min_eq_left h1, max_eq_right zero_le_one]
    · rw [Set.indicator_of_notMem (s := {y : ℝ | (k : ℝ) + 1 ≤ |y|}) hy]
      exact hφ0 y
  -- Upper bound: the ramp is dominated by the indicator of the `k` tail.
  have hhigh : ∫ y, f y ∂ν ≤ ν.real {y : ℝ | (k : ℝ) ≤ |y|} := by
    rw [← integral_indicator_one (hmeasA (k : ℝ))]
    refine integral_mono (hfint ν)
      ((integrable_const (1 : ℝ)).indicator (hmeasA (k : ℝ))) fun y => ?_
    by_cases hy : (k : ℝ) ≤ |y|
    · rw [Set.indicator_of_mem (s := {y : ℝ | (k : ℝ) ≤ |y|}) hy, Pi.one_apply]
      exact hφ1 y
    · rw [Set.indicator_of_notMem (s := {y : ℝ | (k : ℝ) ≤ |y|}) hy, hfval]
      have hneg : |y| - (k : ℝ) ≤ 0 := by linarith [not_le.mp hy]
      change max 0 (min 1 (|y| - (k : ℝ))) ≤ (0 : ℝ)
      exact max_le le_rfl ((min_le_right _ _).trans hneg)
  refine ⟨(k : ℝ) + 1, by positivity, ?_⟩
  have hlt : ∫ y, f y ∂ν < ε := by linarith
  filter_upwards [(h f).eventually (eventually_lt_nhds hlt)] with n hn
  exact le_of_lt (lt_of_le_of_lt (hlow (μ n)) hn)

end StatLean.HypothesisTesting
