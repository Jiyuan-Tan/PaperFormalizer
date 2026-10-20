module
public import StatLean.RobustStatistics.Core.InfluenceFunction
public import StatLean.RobustStatistics.MEstimation.MLocationFunctional
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# The influence function of location M-functionals — the flagship formula

For a location M-functional defined by `E_P ψ(x - T(P)) = 0`, the influence function at
contamination point `x₀` is (`MMY §3.1`, eq. (3.7); proof in §3.8.1)

$$\operatorname{IF}(x_0; T, P) = \frac{\psi(x_0 - \theta_0)}{A}, \qquad
  A = \int \psi'(x - \theta_0)\,dP(x),$$

so a *bounded score forces a bounded influence function* — the theorem chain
`ψ bounded ⟹ IF bounded` that separates Huber estimation from the mean.

The book's derivation (`MMY §3.8.1`, eq. (3.58)–(3.59)) differentiates the contaminated
estimating identity along the mixture path and notes "it is taken for granted that
`∂θ_ε/∂ε` exists and `θ_ε → θ_0`"; the rigorous proof is delegated to Huber–Ronchetti.
The Lean statements mirror that structure honestly: the *root path* `θ` and its one-sided
differentiability at `0` are explicit inputs, and the theorem computes the derivative's
unique possible value. The Lipschitz version `mLocationRoot_influence_of_lipschitz`
requires `ψ` differentiable only `P`-almost everywhere along the shifted data, which is
exactly what the kinked Huber score satisfies when `P` has no atoms at `θ₀ ± c`.

* `mLocationRoot_influence_of_lipschitz` — the IF formula for Lipschitz scores with a.e.
  derivatives (engine).
* `mLocationRoot_influence` — the smooth-score corollary (`ψ'` everywhere).
* `mLocationFunctional_hasInfluenceAt` — packaged as `HasInfluenceAt` for a functional.
* `mLocation_influence_bounded` — `|ψ| ≤ c ⟹ |IF| ≤ c/|A|` (`MMY` (3.30)–(3.31) context).
* `huberLocation_influence`, `huberLocation_influence_bounded` — the Huber instance:
  `IF = ψ_c(x₀ - θ₀)/P(|x - θ₀| < c)`, bounded by `c / P(|x - θ₀| < c)`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.1 (eq. (3.7)),
§3.3 (eq. (3.29)–(3.31)), §3.8.1 (eq. (3.58)–(3.59)).

**Bibliographic comments.** The influence function of an M-estimator — `ψ(x−θ)/A`, bounded
score ⟹ bounded influence — is F. R. Hampel, "The influence curve and its role in robust
estimation," *J. Amer. Statist. Assoc.* **69** (1974), 383–393, developed at book length in
Hampel, Ronchetti, Rousseeuw and Stahel, *Robust Statistics: The Approach Based on Influence
Functions*, Wiley, 1986, §2.3; the von Mises derivative framework is von Mises (1947).
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace StatLean.RobustStatistics

/-! ### Private analytic bricks -/

/-- A Lipschitz score integrable at one shift is integrable at every shift: the difference
of two shifted scores is bounded by `L * |θ₀ - θ'|`, integrable against a finite measure. -/
private theorem integrable_shift_of_lipschitz {P : Measure ℝ} [IsFiniteMeasure P]
    {ψ : ℝ → ℝ} {L : ℝ≥0} (hψlip : LipschitzWith L ψ) {θ₀ : ℝ}
    (hint : Integrable (fun x => ψ (x - θ₀)) P) (θ' : ℝ) :
    Integrable (fun x => ψ (x - θ')) P := by
  have hcont : Continuous fun x : ℝ => ψ (x - θ') :=
    hψlip.continuous.comp (continuous_id.sub continuous_const)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ψ (x - θ')) P := hcont.aestronglyMeasurable
  have hdiff : Integrable (fun x : ℝ => ψ (x - θ') - ψ (x - θ₀)) P := by
    refine Integrable.mono' (g := fun _ : ℝ => (L : ℝ) * |θ₀ - θ'|) (integrable_const _)
      (hmeas.sub hint.aestronglyMeasurable) ?_
    filter_upwards with x
    have h := hψlip.dist_le_mul (x - θ') (x - θ₀)
    rw [Real.dist_eq, Real.dist_eq] at h
    have he : x - θ' - (x - θ₀) = θ₀ - θ' := by ring
    rw [he] at h
    simpa [Real.norm_eq_abs] using h
  refine (hdiff.add hint).congr ?_
  filter_upwards with x
  simp

/-- The one-sided product rule at `0` for a factor that is merely *continuous*: if `q` is
continuous within `s` at `0` then `t ↦ t * q t` has right derivative `q 0` there. This is
the honest form of the `t·ψ(x₀ - θ_t)` term of the contaminated M-equation, whose second
factor need not be differentiable. -/
private theorem hasDerivWithinAt_id_mul {q : ℝ → ℝ} {s : Set ℝ}
    (hq : ContinuousWithinAt q s 0) :
    HasDerivWithinAt (fun t : ℝ => t * q t) (q 0) s 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine Filter.Tendsto.congr' ?_ (hq.mono_left (nhdsWithin_mono _ Set.diff_subset))
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht.2
  rw [slope_def_field, sub_zero, zero_mul, sub_zero, mul_comm, mul_div_assoc, div_self ht0,
    mul_one]

/-- **The influence-function formula for M-functionals, Lipschitz engine**
(`MMY §3.8.1`): if `θ t` solves the `δ_{x₀}`-contaminated M-equation for small `t ≥ 0`
and is right-differentiable at `0` with derivative `d`, then
`d = ψ(x₀ - θ₀) / A` with `A = ∫ ψd dP` the mean a.e. derivative of the score along the
shifted data. -/
theorem mLocationRoot_influence_of_lipschitz {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ ψd : ℝ → ℝ} {L : ℝ≥0} {θ : ℝ → ℝ} {θ₀ x₀ d A : ℝ}
    -- USER-INPUT: Lipschitz score; MMY §3.8.1 (regularity for the interchange)
    (hψlip : LipschitzWith L ψ)
    -- USER-INPUT: the score is integrable at the uncontaminated root — automatic for the
    -- bounded ψ-functions of MMY Def 2.2, a genuine moment condition beyond them
    (hint : Integrable (fun x => ψ (x - θ₀)) P)
    -- USER-INPUT: ψ differentiable P-a.e. along the θ₀-shifted data, with derivative ψd;
    -- MMY §3.8.1 ("assume ψ' exists"), weakened to the a.e. form the Huber score satisfies
    (hae : ∀ᵐ x ∂P, HasDerivAt ψ (ψd x) (x - θ₀))
    -- LEAN-ONLY: measurability of the chosen a.e. derivative, for the parametric-integral
    -- theorem; no scope change (any version works)
    (hψd_meas : AEStronglyMeasurable ψd P)
    -- USER-INPUT: θ t solves the contaminated M-equation for small t ≥ 0; MMY (3.58)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    -- USER-INPUT: the contaminated root path is right-differentiable at 0; MMY §3.8.1
    -- ("it is taken for granted that ∂θ_ε/∂ε exists")
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    (hA : A = ∫ x, ψd x ∂P)
    -- USER-INPUT: nondegenerate denominator; MMY Thm 10.7 (B ≠ 0)
    (hA0 : A ≠ 0) :
    d = ψ (x₀ - θ₀) / A := by
  -- Every shift of the score is integrable, so the mixture split below is honest.
  have hshift : ∀ θ' : ℝ, Integrable (fun x => ψ (x - θ')) P := fun θ' =>
    integrable_shift_of_lipschitz hψlip hint θ'
  -- Step 1: the population score `θ' ↦ ∫ ψ(x - θ') dP` has derivative `-A` at `θ₀`.
  have hGderiv : HasDerivAt (fun θ' : ℝ => ∫ x, ψ (x - θ') ∂P) (-A) θ₀ := by
    have hlip : ∀ᵐ x ∂P, LipschitzOnWith (Real.nnabs ((L : ℝ)))
        (fun θ' : ℝ => ψ (x - θ')) Set.univ := by
      filter_upwards with x
      rw [Real.nnabs_coe]
      refine LipschitzWith.lipschitzOnWith ?_
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      have h := hψlip.dist_le_mul (x - a) (x - b)
      rw [Real.dist_eq, Real.dist_eq] at h ⊢
      have he : x - a - (x - b) = b - a := by ring
      rw [he, abs_sub_comm b a] at h
      exact h
    have hdiff : ∀ᵐ x ∂P, HasDerivAt (fun θ' : ℝ => ψ (x - θ')) (-(ψd x)) θ₀ := by
      filter_upwards [hae] with x hx
      simpa [Function.comp_def] using hx.comp θ₀ ((hasDerivAt_id θ₀).const_sub x)
    have key := hasDerivAt_integral_of_dominated_loc_of_lip (𝕜 := ℝ)
      (F := fun (θ' : ℝ) (x : ℝ) => ψ (x - θ')) (x₀ := θ₀) (bound := fun _ : ℝ => (L : ℝ))
      (F' := fun x => -(ψd x)) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall fun θ' => (hshift θ').aestronglyMeasurable)
      hint hψd_meas.neg hlip (integrable_const _) hdiff
    have hneg : (∫ x, -(ψd x) ∂P) = -A := by rw [integral_neg, hA]
    rw [hneg] at key
    exact key.2
  -- Step 2: the contaminated M-equation, split by the point-mass mixture formula.
  have hIco : Set.Ico (0 : ℝ) 1 ∈ 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t h1 h2
    exact ⟨h1, h2⟩
  have hΦ0 : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
      (∫ x, ψ (x - θ t) ∂P) + t * (ψ (x₀ - θ t) - ∫ x, ψ (x - θ t) ∂P) = 0 := by
    filter_upwards [hroot, hIco] with t ht htI
    have hti : ∫ x, ψ (x - θ t) ∂(contaminate P (Measure.dirac x₀) t) = 0 := ht
    rw [integral_contaminate_dirac htI.1 htI.2.le (hshift (θ t)) x₀] at hti
    have hring : (∫ x, ψ (x - θ t) ∂P) + t * (ψ (x₀ - θ t) - ∫ x, ψ (x - θ t) ∂P)
        = (1 - t) * (∫ x, ψ (x - θ t) ∂P) + t * ψ (x₀ - θ t) := by ring
    rw [hring]
    exact hti
  -- `t = 0` belongs to every `𝓝[Ici 0] 0`-set: the uncontaminated equation.
  have hzero : (∫ x, ψ (x - θ₀) ∂P) = 0 := by
    have h00 := mem_of_mem_nhdsWithin (Set.self_mem_Ici (a := (0 : ℝ))) hΦ0
    simp only [Set.mem_setOf_eq, zero_mul, add_zero, hθ0] at h00
    exact h00
  -- Step 3: differentiate the two pieces within `Ici 0` at `0`.
  have hcomp : HasDerivWithinAt (fun t : ℝ => ∫ x, ψ (x - θ t) ∂P) (-A * d)
      (Set.Ici 0) 0 := by
    simpa [Function.comp_def] using
      HasDerivAt.comp_hasDerivWithinAt_of_eq (x := (0 : ℝ)) hGderiv hθd hθ0.symm
  have hqcont : ContinuousWithinAt
      (fun t : ℝ => ψ (x₀ - θ t) - ∫ x, ψ (x - θ t) ∂P) (Set.Ici (0 : ℝ)) 0 := by
    have hψc : ContinuousWithinAt (fun t : ℝ => ψ (x₀ - θ t)) (Set.Ici (0 : ℝ)) 0 := by
      have hat : ContinuousAt (fun u : ℝ => ψ (x₀ - u)) (θ 0) :=
        (hψlip.continuous.comp (continuous_const.sub continuous_id)).continuousAt
      simpa [Function.comp_def] using hat.comp_continuousWithinAt hθd.continuousWithinAt
    exact hψc.sub hcomp.continuousWithinAt
  have h2 : HasDerivWithinAt (fun t : ℝ => t * (ψ (x₀ - θ t) - ∫ x, ψ (x - θ t) ∂P))
      (ψ (x₀ - θ₀) - 0) (Set.Ici (0 : ℝ)) 0 := by
    have := hasDerivWithinAt_id_mul hqcont
    rwa [hθ0, hzero] at this
  have hΦderiv : HasDerivWithinAt
      (fun t : ℝ => (∫ x, ψ (x - θ t) ∂P) + t * (ψ (x₀ - θ t) - ∫ x, ψ (x - θ t) ∂P))
      (-A * d + (ψ (x₀ - θ₀) - 0)) (Set.Ici (0 : ℝ)) 0 := hcomp.fun_add h2
  -- Step 4: the same function is eventually `0`, so its within-derivative is `0`.
  have hΦconst : HasDerivWithinAt
      (fun t : ℝ => (∫ x, ψ (x - θ t) ∂P) + t * (ψ (x₀ - θ t) - ∫ x, ψ (x - θ t) ∂P))
      0 (Set.Ici (0 : ℝ)) 0 := by
    refine HasDerivWithinAt.congr_of_eventuallyEq
      (f := fun _ : ℝ => (0 : ℝ)) (hasDerivWithinAt_const (c := (0 : ℝ))
        (x := (0 : ℝ)) (s := Set.Ici (0 : ℝ))) ?_ ?_
    · filter_upwards [hΦ0] with t ht using ht
    · simp [hθ0, hzero]
  have huniq : -A * d + (ψ (x₀ - θ₀) - 0) = 0 :=
    (hΦderiv.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hΦconst.derivWithin (uniqueDiffWithinAt_Ici 0))
  rw [eq_div_iff hA0]
  linarith

/-- **The influence-function formula for M-functionals, smooth scores**
(`MMY §3.1`, eq. (3.7)): the specialization of the Lipschitz engine to scores with an
everywhere derivative `ψ'` bounded by a constant. -/
theorem mLocationRoot_influence {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ ψ' : ℝ → ℝ} {C : ℝ} {θ : ℝ → ℝ} {θ₀ x₀ d A : ℝ}
    -- USER-INPUT: differentiable score with derivative ψ'; MMY §3.8.1
    (hψ : ∀ u, HasDerivAt ψ (ψ' u) u)
    -- USER-INPUT: bounded score derivative (dominates the interchange); MMY (10.8)
    (hψ'b : ∀ u, |ψ' u| ≤ C)
    -- USER-INPUT: the score is integrable at the uncontaminated root; MMY §3.8.1 context
    (hint : Integrable (fun x => ψ (x - θ₀)) P)
    -- LEAN-ONLY: measurability of ψ'; automatic for continuous derivatives
    (hψ'_meas : Measurable ψ')
    -- USER-INPUT: θ t solves the contaminated M-equation for small t ≥ 0; MMY (3.58)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    -- USER-INPUT: the contaminated root path is right-differentiable at 0; MMY §3.8.1
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    (hA : A = ∫ x, ψ' (x - θ₀) ∂P)
    -- USER-INPUT: nondegenerate denominator; MMY Thm 10.7 (B ≠ 0)
    (hA0 : A ≠ 0) :
    d = ψ (x₀ - θ₀) / A := by
  -- The bound `C` is automatically nonnegative: it dominates `|ψ' 0|`.
  have hC : 0 ≤ C := (abs_nonneg _).trans (hψ'b 0)
  -- A globally differentiable score with derivative bounded by `C` is `C`-Lipschitz (MVT).
  have hlip : LipschitzWith C.toNNReal ψ := by
    refine lipschitzWith_of_nnnorm_deriv_le (fun u => (hψ u).differentiableAt) fun u => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C hC, (hψ u).deriv,
      Real.norm_eq_abs]
    exact hψ'b u
  exact mLocationRoot_influence_of_lipschitz hlip hint
    (Filter.Eventually.of_forall fun x => hψ (x - θ₀))
    (hψ'_meas.comp (measurable_id.sub_const θ₀)).aestronglyMeasurable hroot hθ0 hθd hA hA0

/-- **The influence function of an M-location functional** (`MMY` eq. (3.7)), packaged
for a functional `T : Measure ℝ → ℝ` whose values solve the contaminated M-equation along
the point-mass path: `HasInfluenceAt T P x₀ (ψ(x₀ - T P)/A)`. -/
theorem mLocationFunctional_hasInfluenceAt {P : Measure ℝ} [IsProbabilityMeasure P]
    {T : Measure ℝ → ℝ} {ψ ψd : ℝ → ℝ} {L : ℝ≥0} {x₀ A : ℝ}
    (hψlip : LipschitzWith L ψ)
    -- USER-INPUT: the score is integrable at the uncontaminated value; MMY §3.8.1 context
    (hint : Integrable (fun x => ψ (x - T P)) P)
    (hae : ∀ᵐ x ∂P, HasDerivAt ψ (ψd x) (x - T P))
    (hψd_meas : AEStronglyMeasurable ψd P)
    -- USER-INPUT: T tracks roots of the contaminated M-equation near 0; MMY §3.7 (3.51)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t)
        (T (contaminate P (Measure.dirac x₀) t)))
    -- USER-INPUT: the contamination curve of T is right-differentiable at 0; MMY §3.8.1
    (hTd : ∃ d, HasDerivWithinAt (fun t : ℝ => T (contaminate P (Measure.dirac x₀) t)) d
      (Set.Ici 0) 0)
    (hA : A = ∫ x, ψd x ∂P) (hA0 : A ≠ 0) :
    HasInfluenceAt T P x₀ (ψ (x₀ - T P) / A) := by
  obtain ⟨d, hd⟩ := hTd
  -- The contamination curve of `T` is a root path starting at the uncontaminated value.
  have hθ0 : (fun t : ℝ => T (contaminate P (Measure.dirac x₀) t)) 0 = T P := by simp
  -- The engine pins down its one-sided derivative.
  have key : d = ψ (x₀ - T P) / A :=
    mLocationRoot_influence_of_lipschitz
      (θ := fun t : ℝ => T (contaminate P (Measure.dirac x₀) t))
      hψlip hint hae hψd_meas hroot hθ0 hd hA hA0
  rw [hasInfluenceAt_iff_hasDerivWithinAt, ← key]
  exact hd

/-- **Bounded score ⟹ bounded influence** (`MMY §3.3`, eq. (3.30)–(3.31) context): if
`|ψ| ≤ c` then any influence value produced by the M-functional formula is bounded by
`c/|A|`, uniformly in the contamination point. -/
theorem mLocation_influence_bounded {ψ : ℝ → ℝ} {c A u : ℝ}
    -- USER-INPUT: bounded score; MMY §2.3.2 / Def 2.2
    (hψb : ∀ v, |ψ v| ≤ c) (hA0 : A ≠ 0) :
    |ψ u / A| ≤ c / |A| := by
  have hApos : 0 < |A| := abs_pos.mpr hA0
  rw [abs_div]
  gcongr
  exact hψb u

/-! ### The Huber instance (`MMY §2.3.2` + §3.1) -/

/-- **The influence function of the Huber location functional** (`MMY` eq. (3.7) with eq.
(2.29)): `IF(x₀) = ψ_c(x₀ - θ₀) / P(|x - θ₀| < c)`. The denominator is the mass of the
central region, the a.e. derivative of the clipped score. -/
theorem huberLocation_influence {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ}
    (hc : 0 < c) {θ : ℝ → ℝ} {θ₀ x₀ d : ℝ}
    -- USER-INPUT: no atoms at the clipping knots (a.e. differentiability of ψ_c along the
    -- shifted data); MMY §10.3 (F continuous at the relevant points)
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0)
    -- USER-INPUT: θ t solves the contaminated Huber equation for small t ≥ 0; MMY (3.58)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot (huberPsi c) (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    -- USER-INPUT: right-differentiable root path; MMY §3.8.1
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    -- USER-INPUT: the central region has positive mass (B ≠ 0); MMY Thm 10.7
    (hmass : 0 < P.real {x | |x - θ₀| < c}) :
    d = huberPsi c (x₀ - θ₀) / P.real {x | |x - θ₀| < c} := by
  classical
  -- The central region, and the a.e. derivative of the clipped score along shifted data.
  have hSmeas : MeasurableSet {x : ℝ | |x - θ₀| < c} :=
    measurableSet_lt ((continuous_id.sub continuous_const).abs).measurable measurable_const
  -- `|ψ_c| ≤ c`, so the score is integrable against the probability measure `P`.
  have hint : Integrable (fun x => huberPsi c (x - θ₀)) P := by
    refine Integrable.mono' (integrable_const c)
      ((huberPsi_continuous c).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    simpa [Real.norm_eq_abs] using abs_huberPsi_le hc.le (x - θ₀)
  -- Off the two knots `θ₀ ± c` the Huber score is locally the identity or locally constant.
  have hae : ∀ᵐ x ∂P, HasDerivAt (huberPsi c)
      (Set.indicator {x : ℝ | |x - θ₀| < c} 1 x) (x - θ₀) := by
    have hnull : P ({θ₀ + c} ∪ {θ₀ - c}) = 0 := measure_union_null h_atom_add h_atom_sub
    filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
    have habs : |x - θ₀| ≠ c := by
      intro h
      rcases (abs_eq hc.le).mp h with h1 | h1
      · exact hx (Or.inl (by simp only [Set.mem_singleton_iff]; linarith))
      · exact hx (Or.inr (by simp only [Set.mem_singleton_iff]; linarith))
    rcases lt_or_gt_of_ne habs with hlt | hgt
    · -- Interior of the linear branch: `ψ_c` agrees with the identity near `x - θ₀`.
      have hmem : x ∈ {x : ℝ | |x - θ₀| < c} := hlt
      rw [Set.indicator_of_mem hmem, Pi.one_apply]
      refine (hasDerivAt_id (x - θ₀)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hlt] with u hu
      exact huberPsi_of_abs_le hc.le (le_of_lt hu)
    · -- Clipped branch: `ψ_c` is locally the constant `±c`.
      have hnmem : x ∉ {x : ℝ | |x - θ₀| < c} := not_lt.mpr hgt.le
      rw [Set.indicator_of_notMem hnmem]
      rcases lt_abs.mp hgt with h1 | h1
      · refine (hasDerivAt_const (x - θ₀) c).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds h1] with u hu
        have hu' : c < u := hu
        rw [huberPsi, min_eq_left hu'.le, max_eq_right (by linarith : -c ≤ c)]
      · refine (hasDerivAt_const (x - θ₀) (-c)).congr_of_eventuallyEq ?_
        filter_upwards [Iio_mem_nhds (by linarith : x - θ₀ < -c)] with u hu
        have hu' : u < -c := hu
        rw [huberPsi, min_eq_right (by linarith : u ≤ c), max_eq_left (by linarith : u ≤ -c)]
  -- The denominator is the mass of the central region.
  have hA : P.real {x : ℝ | |x - θ₀| < c}
      = ∫ x, Set.indicator {x : ℝ | |x - θ₀| < c} 1 x ∂P :=
    (integral_indicator_one hSmeas).symm
  exact mLocationRoot_influence_of_lipschitz (huberPsi_lipschitz c) hint hae
    (measurable_one.indicator hSmeas).aestronglyMeasurable hroot hθ0 hθd hA hmass.ne'

/-- **The Huber location functional has bounded influence** (`MMY §3.3`): the influence
value at any contamination point is bounded by `c / P(|x - θ₀| < c)`. Contrast with the
unbounded influence of the mean (`LocationScale/Mean.lean`). -/
theorem huberLocation_influence_bounded {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ}
    (hc : 0 < c) {θ : ℝ → ℝ} {θ₀ x₀ d : ℝ}
    (h_atom_add : P {θ₀ + c} = 0) (h_atom_sub : P {θ₀ - c} = 0)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot (huberPsi c) (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    (hmass : 0 < P.real {x | |x - θ₀| < c}) :
    |d| ≤ c / P.real {x | |x - θ₀| < c} := by
  rw [huberLocation_influence hc h_atom_add h_atom_sub hroot hθ0 hθd hmass]
  have hbd := mLocation_influence_bounded (ψ := huberPsi c) (c := c)
    (A := P.real {x | |x - θ₀| < c}) (u := x₀ - θ₀) (abs_huberPsi_le hc.le) hmass.ne'
  rwa [abs_of_pos hmass] at hbd

end StatLean.RobustStatistics
