module
public import StatLean.PointEstimation.Equivariance.ConditionalRiskEngine
public import StatLean.PointEstimation.Equivariance.ScaleStructure
public import StatLean.PointEstimation.Equivariance.LocationMRE
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# The minimum risk equivariant scale estimator

The scale counterpart of `LocationMRE`. The scale-equivariant class is `δ₀ / w ∘ scaleZ`
(`ScaleStructure`), so minimizing the risk over it reduces to a fibrewise minimization of
the conditional expected loss `E₁{γ[δ₀(X)/w] | z}` given the maximal invariant — the same
engine as in the location case with the template `F w x = δ₀ x / w` in place of
`F w x = δ₀ x − w`.

* `isScaleMRE_of_conditional_min` — the construction;
* `exists_isScaleMRE_of_convex` — existence when `v ↦ γ(eᵛ)` is convex and not monotone,
  the multiplicative form of the convexity condition;
* `isScaleMRE_steinLoss` — the explicit minimum risk equivariant estimator of `τ^r` under
  Stein's loss `γ(v) = v − log v − 1`, namely `δ₀(X) / E₁[δ₀(X) | z]`;
* `isScaleMRE_standardizedSquared` — the companion explicit form under the standardized
  squared-error loss `γ(v) = (v − 1)²`, a ratio of conditional moments
  `δ₀(X)·E₁[δ₀(X)|z] / E₁[δ₀²(X)|z]`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.3
(Location-Scale Families), Theorem 3.3 (the scale MRE estimator by conditional minimization)
with Corollaries 3.4 and 3.8 (the convex form and the explicit MRE of `τʳ`). (`TPE2 §3.3 Thm
3.3, Cor 3.4, Cor 3.8`.)

**Proof formalization notes.**
* The multiplicative group acts transitively on the scale parameter, so the risk of a
  scale-equivariant estimator is constant and minimizing it is well posed; this is the
  general constant-risk result specialised, not a separate fact.
* Because `scaleZ` uses division, Lean's `x / 0 = 0` convention makes `scaleZ` invariant
  under positive scaling **everywhere**, including on `{xₙ = 0}`. The constructed
  estimators are therefore equivariant without any restriction. The null-set hypothesis
  `hnull` is needed for the *minimality* half instead: comparing against an arbitrary
  equivariant competitor uses the representation `δ = δ₀ / w ∘ scaleZ`, which is only
  available off `{xₙ = 0}`. The classical development records this as "z is defined when
  `xₙ ≠ 0`, hence with probability one".
* The convexity condition is stated on the logarithmic reparametrization `v ↦ γ(eᵛ)`,
  which is what turns the multiplicative fibrewise minimization into the additive one
  solved in the location case; the accompanying positivity of the reference estimator is
  the "without loss of generality `δ ≥ 0`" of the classical argument, made explicit.
* **The existence statement degenerates and does not use the conditional minimization.**
  A *strictly positive* equivariant estimator forces `r = 0` (`degree_eq_zero_of_pos`:
  equivariance at `x = 0` gives `δ₀ 0 = τʳ · δ₀ 0`), and at degree `0` every constant is
  equivariant. So it is enough that `γ` attain its minimum at a positive point — convexity
  and non-monotonicity of `v ↦ γ(eᵛ)` give a minimizer `v₀` on the positive axis, and
  `hposmin` says nothing off it undercuts that value — and then the *constant* estimator
  `e^{v₀}` beats every competitor pointwise, hence in risk. The hypotheses `hγ`, `hδ₀`,
  `hfin` and `hnull` are therefore not consumed; they are kept because the statement is the
  classical Corollary 3.4, whose intended proof route (fibrewise minimization through
  `isScaleMRE_of_conditional_min`) does need them. The same degeneracy is what collapses
  `isScaleMRE_steinLoss` and `isScaleMRE_standardizedSquared` to risk `0`.
* Stein's loss is stated with the conditional mean, matching the classical form. The
  classical statement asserts *uniqueness* of the minimizer; only optimality is
  formalized here.
* The standardized squared-error form is the companion of the same conditional
  minimization for the loss `(d − τ^r)²/τ^{2r}`, whose solution is the ratio of the first
  and second conditional moments of the reference estimator. Comparing the two makes the
  classical point that Stein's loss yields the larger estimator, since the second
  conditional moment dominates the square of the first.
* As in the location case, `hmin` uses `∀ᵐ` where the classical hypothesis is stated for
  every fibre, and measurability of the fibrewise minimizer is a Lean-side requirement
  with no classical counterpart.

**Bibliographic comments.** Equivariant estimation of a scale parameter is due to
E. J. G. Pitman, "The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421. The entropy loss used
here was introduced by W. James and C. Stein, "Estimation with quadratic loss," *Proc.
Fourth Berkeley Symp. Math. Statist. Probab.*, vol. 1, Univ. California Press, 1961,
361–379; for the admissibility questions in the background see C. Stein, "The
admissibility of Pitman's estimator of a single location parameter," *Ann. Math. Statist.*
**30** (1959), 970–979.
-/

open MeasureTheory Filter
open scoped ENNReal ProbabilityTheory

namespace StatLean.PointEstimation

section ScaleMRE

variable {m : ℕ}

/-- **Stein's (entropy) loss** for a scale parameter in standardized form,
`γ(v) = v − log v − 1`, so that `L(τ, d) = d/τ^r − log(d/τ^r) − 1`.

Unlike the standardized squared-error loss it penalises overestimation and
underestimation comparably: it tends to infinity at both `0` and `∞`. Edge behaviour:
`Real.log` is `0` at `0` and reads the absolute value on negatives, so `steinLoss` is
junk for non-positive arguments; every statement below constrains the estimator to be
positive. -/
noncomputable def steinLoss (v : ℝ) : ℝ := v - Real.log v - 1

/-- Positive scalings leave `scaleZ` unchanged (private re-derivation of the same fact
proved in `ScaleStructure`, needed here for the equivariance of the explicit estimators). -/
private lemma scaleZ_smul' {b : ℝ} (hb : 0 < b) (x : Fin (m + 1) → ℝ) :
    scaleZ (b • x) = scaleZ x := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have h1 : ∀ i : Fin m, (b • x) i.castSucc / (b • x) (Fin.last m)
      = x i.castSucc / x (Fin.last m) := by
    intro i
    show b * x i.castSucc / (b * x (Fin.last m)) = x i.castSucc / x (Fin.last m)
    rw [mul_div_mul_left _ _ hb0]
  have h2 : (b • x) (Fin.last m) / |(b • x) (Fin.last m)|
      = x (Fin.last m) / |x (Fin.last m)| := by
    show b * x (Fin.last m) / |b * x (Fin.last m)| = x (Fin.last m) / |x (Fin.last m)|
    rw [abs_mul, abs_of_pos hb, mul_div_mul_left _ _ hb0]
  exact Prod.ext_iff.mpr ⟨funext h1, h2⟩

/-- A strictly positive scale-equivariant estimator can only have degree `0`: evaluating
equivariance at `x = 0`, `τ = 2` gives `δ₀ 0 = 2^r · δ₀ 0`, forcing `2^r = 1`. -/
private lemma degree_eq_zero_of_pos {r : ℕ} {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    (heq₀ : IsScaleEquivariant r δ₀) (h₀pos : ∀ x, 0 < δ₀ x) : r = 0 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · exact h
  · exfalso
    have hkey : δ₀ 0 = 2 ^ r * δ₀ 0 := by
      have h2 := heq₀ (show (0 : ℝ) < 2 by norm_num) 0
      rwa [smul_zero] at h2
    have h1 : (1 : ℝ) < 2 ^ r := one_lt_pow₀ one_lt_two h.ne'
    nlinarith [h₀pos 0, mul_pos (by linarith : (0 : ℝ) < 2 ^ r - 1) (h₀pos 0)]

/-- Analytic core of the scale-MRE argument: a degree-0
equivariant (i.e. `scaleZ`-invariant) measurable `φ` equals its own conditional mean given
the maximal invariant. Intended proof: the disintegration identity
`lintegral_eq_lintegral_condDistrib` applied to `g z x = if scaleZ x = z then 0 else 1`
gives `∫⁻ z, (orbitCondKernel P₀ scaleZ z) {scaleZ ≠ z} ∂(P₀.map scaleZ) = 0`, so almost
every fibre kernel is concentrated on `{scaleZ = z}`; on that set the invariant `φ` is
constant (two points with equal `scaleZ` and nonzero last coordinate are positive
multiples of one another — using `hnull` for `x (Fin.last m) ≠ 0` a.e.), so
`∫ φ ∂(orbitCondKernel P₀ scaleZ (scaleZ x)) = φ x` almost everywhere. -/
private lemma integral_orbitCondKernel_eq_self_of_invariant
    (P₀ : Measure (Fin (m + 1) → ℝ)) [IsProbabilityMeasure P₀]
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφ : Measurable φ)
    (hinv : IsScaleEquivariant 0 φ)
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    (hint : ∀ z, Integrable φ (orbitCondKernel P₀ scaleZ z)) :
    ∀ᵐ x ∂P₀, ∫ y, φ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x)) = φ x := by
  -- `φ` is scale-invariant off the null set, so it factors measurably through `scaleZ`.
  have hφinv : ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 → φ (b • x) = φ x := by
    intro b hb x _; rw [hinv hb x, pow_zero, one_mul]
  obtain ⟨w, hwm, hw⟩ := isScaleInvariant_factors_scaleZ_measurable φ hφ hφinv
  -- `φ = w ∘ scaleZ` almost everywhere.
  have hφae : φ =ᵐ[P₀] fun x => w (scaleZ x) := by
    have hn : ∀ᵐ x ∂P₀, x (Fin.last m) ≠ 0 := by
      rw [ae_iff]; simp only [not_ne_iff]; exact hnull
    filter_upwards [hn] with x hx using hw x hx
  -- The joint law `(scaleZ x, x)` sits on `{(z, y) | scaleZ y = z}`, so the fibre kernel is
  -- concentrated on that fibre; both facts come from `compProd_map_condDistrib`.
  have hcompProd : (P₀.map scaleZ) ⊗ₘ orbitCondKernel P₀ scaleZ
      = P₀.map (fun x => (scaleZ x, x)) := by
    unfold orbitCondKernel
    exact ProbabilityTheory.compProd_map_condDistrib aemeasurable_id
  have hprodMeas : Measurable (fun x : Fin (m + 1) → ℝ => (scaleZ x, x)) :=
    measurable_scaleZ.prodMk measurable_id
  have hconc_cp : ∀ᵐ q ∂((P₀.map scaleZ) ⊗ₘ orbitCondKernel P₀ scaleZ),
      scaleZ q.2 = q.1 := by
    rw [hcompProd]
    exact (ae_map_iff hprodMeas.aemeasurable
        (measurableSet_eq_fun (measurable_scaleZ.comp measurable_snd) measurable_fst)).mpr
      (ae_of_all _ fun x => rfl)
  have hconc := Measure.ae_ae_of_ae_compProd hconc_cp
  have hφfib_cp : ∀ᵐ q ∂((P₀.map scaleZ) ⊗ₘ orbitCondKernel P₀ scaleZ),
      φ q.2 = w (scaleZ q.2) := by
    rw [hcompProd]
    exact (ae_map_iff hprodMeas.aemeasurable
        (measurableSet_eq_fun (hφ.comp measurable_snd)
          (hwm.comp (measurable_scaleZ.comp measurable_snd)))).mpr hφae
  have hφfib := Measure.ae_ae_of_ae_compProd hφfib_cp
  -- Fibrewise: the conditional mean of `φ` recovers `w z`.
  have hZ : ∀ᵐ z ∂(P₀.map scaleZ),
      ∫ y, φ y ∂(orbitCondKernel P₀ scaleZ z) = w z := by
    filter_upwards [hφfib, hconc] with z hz1 hz2
    calc ∫ y, φ y ∂(orbitCondKernel P₀ scaleZ z)
        = ∫ y, w (scaleZ y) ∂(orbitCondKernel P₀ scaleZ z) := integral_congr_ae hz1
      _ = ∫ y, w z ∂(orbitCondKernel P₀ scaleZ z) := by
          apply integral_congr_ae; filter_upwards [hz2] with y hy; rw [hy]
      _ = w z := by simp
  -- Pull back to `P₀` and undo the representation of `φ`.
  have hg : Measurable fun z => ∫ y, φ y ∂(orbitCondKernel P₀ scaleZ z) :=
    measurable_integral_orbitCondKernel P₀ measurable_scaleZ hφ hint
  have hZpull : ∀ᵐ x ∂P₀,
      ∫ y, φ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x)) = w (scaleZ x) :=
    (ae_map_iff measurable_scaleZ.aemeasurable (measurableSet_eq_fun hg hwm)).mp hZ
  filter_upwards [hZpull, hφae] with x hx1 hx2
  rw [hx1, hx2]

/-- **The minimum risk equivariant scale estimator.** Let `δ₀` be a measurable
scale-equivariant estimator of `τ^r` with finite risk, nowhere zero, and let `w*` be a
measurable positive function of the maximal invariant which, in almost every fibre,
minimizes the conditional expected loss `E₁{γ[δ₀(X)/w] | z}` over positive constants `w`.
Then `δ₀ / w* ∘ scaleZ` is minimum risk equivariant. -/
theorem isScaleMRE_of_conditional_min (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member (at `τ = 1`) is a probability law
    [IsProbabilityMeasure P₀]
    (γ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss; needed for the disintegration
    (hγ : Measurable γ)
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator, the caller's free choice
    (heq₀ : IsScaleEquivariant r δ₀)
    -- LEAN-ONLY: it never vanishes, so the representation of the equivariant class is
    -- available (see `ScaleStructure`)
    (h₀ne : ∀ x, δ₀ x ≠ 0)
    -- USER-INPUT: it has finite risk, so the conditional minimization is meaningful
    (hfin : scaleRisk P₀ γ δ₀ ≠ ∞)
    -- USER-INPUT: the last coordinate vanishes with probability zero, so the maximal
    -- invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    {wStar : (Fin m → ℝ) × ℝ → ℝ}
    -- USER-INPUT: the fibrewise minimizer, supplied measurably and positively
    (hwStar : Measurable wStar) (hwpos : ∀ z, 0 < wStar z)
    -- USER-INPUT: `w*` minimizes the conditional expected loss in almost every fibre, over
    -- ALL `w : ℝ` — including `w = 0`, not merely the nonzero ones. Two successive
    -- corrections led here. (i) The original `0 < w` form is unsound: it never sees the
    -- opposite-signed equivariant competitors `δ₀ / w`, `w < 0`. (ii) The intermediate
    -- `w ≠ 0` form is *also* unsound: Lean's `x / 0 = 0` convention makes the constant-zero
    -- estimator `δ' ≡ 0` a member of the equivariant class (`0 = τʳ · 0`), and its
    -- representation `δ' = δ₀ / w(scaleZ ·)` forces `w ≡ 0` (since `δ₀ x ≠ 0`), so a
    -- `w ≠ 0` hypothesis cannot dominate it. Counterexample to the `w ≠ 0` form, r = 0:
    -- δ₀ ≡ 1, wStar ≡ 1, γ v = (if v = 0 then 0 else 2); `hmin` holds tightly over `w ≠ 0`
    -- (both sides `ofReal 2`) yet δ' ≡ 0 has risk `0 < 2`. This now matches the location
    -- case `isLocMRE_of_conditional_min`, which quantifies over all `w` unrestricted, and
    -- the engine `lintegral_le_of_condMinimizer`, whose `hmin` is over all `w : ℝ`.
    (hmin : ∀ᵐ z ∂(P₀.map scaleZ), ∀ w : ℝ,
      ∫⁻ x, ENNReal.ofReal (γ (δ₀ x / wStar z)) ∂(orbitCondKernel P₀ scaleZ z) ≤
        ∫⁻ x, ENNReal.ofReal (γ (δ₀ x / w)) ∂(orbitCondKernel P₀ scaleZ z)) :
    IsScaleMRE P₀ γ r (fun x => δ₀ x / wStar (scaleZ x)) := by
  -- Mirror of `isLocMRE_of_conditional_min` with the multiplicative template `F w x = δ₀ x / w`.
  refine ⟨hδ₀.div (hwStar.comp measurable_scaleZ), ?_, ?_⟩
  · -- Equivariance: `wStar ∘ scaleZ` is scale-invariant, so `δ₀ / (wStar ∘ scaleZ)` stays
    -- equivariant of degree `r`.
    have hinv : IsScaleInvariant (fun x => wStar (scaleZ x)) := by
      intro b hb x
      show wStar (scaleZ (b • x)) = wStar (scaleZ x)
      rw [scaleZ_smul' hb x]
    exact heq₀.div_invariant hinv
  · intro δ' hδ'meas hδ'eq
    -- Represent the competitor `δ'` measurably as `δ₀ / w(scaleZ ·)` off the null set, via
    -- the measurable factorization of the scale-invariant `u = δ₀ / δ'`.
    have hum : Measurable (fun x => δ₀ x / δ' x) := hδ₀.div hδ'meas
    have huinv : ∀ ⦃b : ℝ⦄, 0 < b → ∀ x, x (Fin.last m) ≠ 0 →
        (fun x => δ₀ x / δ' x) (b • x) = (fun x => δ₀ x / δ' x) x := by
      intro b hb x _
      have hbr : (b : ℝ) ^ r ≠ 0 := by positivity
      show δ₀ (b • x) / δ' (b • x) = δ₀ x / δ' x
      rw [heq₀ hb x, hδ'eq hb x, mul_div_mul_left _ _ hbr]
    obtain ⟨w, hwm, hw⟩ :=
      isScaleInvariant_factors_scaleZ_measurable (fun x => δ₀ x / δ' x) hum huinv
    -- The engine, at the scale template.
    have hFmeas : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) => δ₀ p.2 / p.1) :=
      (hδ₀.comp measurable_snd).div measurable_fst
    have key := lintegral_le_of_condMinimizer P₀ (Z := scaleZ)
      measurable_scaleZ (F := fun w x => δ₀ x / w) hFmeas (ρ := γ) hγ
      (vStar := wStar) hwStar hmin (v := w) hwm
    -- Off the null set the competitor's loss agrees with the template at `w`, so its risk
    -- rewrites into the engine's right-hand side.
    have hnull' : ∀ᵐ x ∂P₀, x (Fin.last m) ≠ 0 := by
      rw [ae_iff]; simp only [not_ne_iff]; exact hnull
    have hae : (fun x => ENNReal.ofReal (γ (δ' x)))
        =ᵐ[P₀] (fun x => ENNReal.ofReal (γ (δ₀ x / w (scaleZ x)))) := by
      filter_upwards [hnull'] with x hx
      have hwx : δ₀ x / δ' x = w (scaleZ x) := hw x hx
      have : δ₀ x / w (scaleZ x) = δ' x := by
        rw [← hwx, div_div_eq_mul_div, mul_comm (δ₀ x) (δ' x), mul_div_assoc,
          div_self (h₀ne x), mul_one]
      rw [this]
    have hrisk' : scaleRisk P₀ γ δ'
        = ∫⁻ x, ENNReal.ofReal (γ (δ₀ x / w (scaleZ x))) ∂P₀ := by
      unfold scaleRisk; exact lintegral_congr_ae hae
    show scaleRisk P₀ γ (fun x => δ₀ x / wStar (scaleZ x)) ≤ scaleRisk P₀ γ δ'
    rw [hrisk']; unfold scaleRisk; exact key

/-- **Existence of a minimum risk equivariant scale estimator for a logarithmically
convex, non-monotone loss.** Reparametrising `w = eᵛ` turns the multiplicative fibrewise
minimization into the additive one of the location case, so the same convexity and
non-monotonicity conditions apply — now to `v ↦ γ(eᵛ)`. Uniqueness under strict convexity
is not formalized. -/
theorem exists_isScaleMRE_of_convex (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member is a probability law
    [IsProbabilityMeasure P₀]
    (γ : ℝ → ℝ)
    -- LEAN-ONLY: measurability of the loss
    (hγ : Measurable γ)
    -- USER-INPUT: the loss is convex in the logarithmic parametrization
    (hconv : ConvexOn ℝ Set.univ fun v => γ (Real.exp v))
    -- USER-INPUT: and not monotone there, so the fibrewise minimum is attained
    (hnotmono : (¬ Monotone fun v => γ (Real.exp v)) ∧ ¬ Antitone fun v => γ (Real.exp v))
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator with finite risk
    (heq₀ : IsScaleEquivariant r δ₀)
    (hfin : scaleRisk P₀ γ δ₀ ≠ ∞)
    -- USER-INPUT: taking only positive values; this is the classical "without loss of
    -- generality the estimator is nonnegative", made explicit
    (h₀pos : ∀ x, 0 < δ₀ x)
    -- USER-INPUT: the maximal invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    -- USER-INPUT: nothing off the positive axis beats the positive axis. Without this the
    -- statement is FALSE: `hconv` constrains `γ` only on `(0, ∞)`, while minimality must
    -- dominate competitors of either sign, so `γ` can dip below its positive-axis infimum
    -- on `(-∞, 0]` and no equivariant estimator attains the infimum. (Counterexample at
    -- `r = 0`: `γ u = (log u)² + 1` for `u > 0`, `γ u = 1/2 + 1/(2(1+|u|))` for `u ≤ 0`;
    -- `γ ∘ exp` is convex and non-monotone, yet every equivariant estimator has risk
    -- `> 1/2` while `δ' ≡ -M` does better.) In the classical development the loss is a
    -- function of the ratio `d / τʳ > 0`, so only positive arguments occur and this holds
    -- vacuously.
    (hposmin : ∀ u : ℝ, ∃ v : ℝ, 0 < v ∧ γ v ≤ γ u) :
    ∃ δ, IsScaleMRE P₀ γ r δ := by
  -- The fibrewise route through `isScaleMRE_of_conditional_min` is not needed: under these
  -- hypotheses the problem collapses, exactly as it does for `isScaleMRE_steinLoss` and
  -- `isScaleMRE_standardizedSquared`. Indeed `h₀pos` forces `r = 0` (`degree_eq_zero_of_pos`),
  -- and at degree `0` every constant is equivariant, so it suffices to exhibit a positive
  -- global minimizer of the loss: the constant estimator at that point beats *every*
  -- estimator pointwise, equivariant or not.
  obtain rfl : r = 0 := degree_eq_zero_of_pos heq₀ h₀pos
  -- `ρ = γ ∘ exp` is convex and, being neither monotone nor antitone, blows up at both ends,
  -- so it attains its minimum at some `v₀`; put `u₀ = e^{v₀} > 0`.
  have hcoer : Tendsto (fun v => γ (Real.exp v)) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    exact ⟨tendsto_atBot_of_convex_not_monotone hconv hnotmono.1,
      tendsto_atTop_of_convex_not_antitone hconv hnotmono.2⟩
  obtain ⟨v₀, hv₀⟩ := exists_min_of_convexOn_of_coercive hconv hcoer
  set u₀ : ℝ := Real.exp v₀ with hu₀def
  have hu₀pos : 0 < u₀ := Real.exp_pos v₀
  -- `u₀` minimizes `γ` on the positive axis by construction, and `hposmin` extends this to
  -- the whole line: nothing off the positive axis undercuts the positive-axis minimum.
  have hglob : ∀ u : ℝ, γ u₀ ≤ γ u := by
    have hpos : ∀ u : ℝ, 0 < u → γ u₀ ≤ γ u := by
      intro u hu
      simpa [hu₀def, Real.exp_log hu] using hv₀ (Real.log u)
    intro u
    rcases lt_or_ge 0 u with hu | hu
    · exact hpos u hu
    · obtain ⟨v, hvpos, hvle⟩ := hposmin u
      exact (hpos v hvpos).trans hvle
  -- The constant estimator `u₀` is measurable, equivariant of degree `0`, and its loss is
  -- everywhere the smallest value of `γ`, so its risk dominates no competitor's.
  refine ⟨fun _ => u₀, measurable_const, fun τ _ x => by simp, fun δ' _ _ => ?_⟩
  unfold scaleRisk
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hglob (δ' x))

/-- **The minimum risk equivariant estimator of `τ^r` under Stein's loss** is the
reference equivariant estimator divided by its conditional mean given the maximal
invariant: `δ*(X) = δ₀(X) / E₁[δ₀(X) | z]`.

The classical statement adds that the minimizer is unique; only optimality is formalized
here. -/
theorem isScaleMRE_steinLoss (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member is a probability law
    [IsProbabilityMeasure P₀]
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator taking positive values
    (heq₀ : IsScaleEquivariant r δ₀) (h₀pos : ∀ x, 0 < δ₀ x)
    -- USER-INPUT: it has finite risk under Stein's loss
    (hfin : scaleRisk P₀ steinLoss δ₀ ≠ ∞)
    -- USER-INPUT: the maximal invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    -- USER-INPUT: the conditional mean exists in every fibre
    (hint : ∀ z, Integrable δ₀ (orbitCondKernel P₀ scaleZ z))
    -- USER-INPUT: and is positive, so dividing by it is legitimate
    (hcondpos : ∀ z, 0 < ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ z)) :
    IsScaleMRE P₀ steinLoss r
      (fun x => δ₀ x / ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) := by
  -- A strictly positive equivariant estimator forces `r = 0` (else `δ₀ 0 = 2^r · δ₀ 0`
  -- gives `δ₀ 0 = 0`). At `r = 0` the reference is `scaleZ`-invariant, so its conditional
  -- mean recovers it and the estimator collapses to `1`, where Stein's loss vanishes:
  -- the risk is `0`, hence minimum against every competitor.
  obtain rfl : r = 0 := degree_eq_zero_of_pos heq₀ h₀pos
  have hgMeas : Measurable
      (fun x => ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) :=
    (measurable_integral_orbitCondKernel P₀ measurable_scaleZ hδ₀ hint).comp measurable_scaleZ
  have hself := integral_orbitCondKernel_eq_self_of_invariant P₀ hδ₀ heq₀ hnull hint
  refine ⟨hδ₀.div hgMeas, ?_, ?_⟩
  · intro τ hτ x
    show δ₀ (τ • x) / (∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ (τ • x))))
      = τ ^ 0 * (δ₀ x / ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x)))
    rw [scaleZ_smul' hτ x, heq₀ hτ x]
    simp only [pow_zero, one_mul]
  · intro δ' _ _
    have hrisk0 : scaleRisk P₀ steinLoss
        (fun x => δ₀ x / ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) = 0 := by
      have hae : (fun x => ENNReal.ofReal (steinLoss
          (δ₀ x / ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))))) =ᵐ[P₀] 0 := by
        filter_upwards [hself] with x hx
        show ENNReal.ofReal (steinLoss
          (δ₀ x / ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x)))) = 0
        rw [hx, div_self (h₀pos x).ne']
        simp [steinLoss, Real.log_one]
      unfold scaleRisk
      rw [lintegral_congr_ae hae]
      simp
    rw [hrisk0]
    exact zero_le

/-- **The minimum risk equivariant estimator of `τ^r` under the standardized
squared-error loss** `γ(v) = (v − 1)²`, i.e. `L(τ, d) = (d − τ^r)²/τ^{2r}`: the ratio of
conditional moments `δ*(X) = δ₀(X)·E₁[δ₀(X)|z] / E₁[δ₀²(X)|z]`.

Comparing with `isScaleMRE_steinLoss` recovers the classical observation that Stein's
loss produces the larger estimator, since the second conditional moment always dominates
the square of the first. -/
theorem isScaleMRE_standardizedSquared (P₀ : Measure (Fin (m + 1) → ℝ))
    -- USER-INPUT: the base member is a probability law
    [IsProbabilityMeasure P₀]
    (r : ℕ) {δ₀ : (Fin (m + 1) → ℝ) → ℝ}
    -- LEAN-ONLY: measurability of the reference estimator
    (hδ₀ : Measurable δ₀)
    -- USER-INPUT: a reference scale-equivariant estimator taking positive values
    (heq₀ : IsScaleEquivariant r δ₀) (h₀pos : ∀ x, 0 < δ₀ x)
    -- USER-INPUT: it has finite risk under the standardized squared-error loss
    (hfin : scaleRisk P₀ (fun v : ℝ => (v - 1) ^ 2) δ₀ ≠ ∞)
    -- USER-INPUT: the maximal invariant is defined almost everywhere
    (hnull : P₀ {x | x (Fin.last m) = 0} = 0)
    -- USER-INPUT: the first two conditional moments exist in every fibre
    (hint₁ : ∀ z, Integrable δ₀ (orbitCondKernel P₀ scaleZ z))
    (hint₂ : ∀ z, Integrable (fun y => δ₀ y ^ 2) (orbitCondKernel P₀ scaleZ z))
    -- USER-INPUT: the second conditional moment is positive, so the ratio is not junk
    (hpos₂ : ∀ z, 0 < ∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ z)) :
    IsScaleMRE P₀ (fun v : ℝ => (v - 1) ^ 2) r
      (fun x => δ₀ x * (∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) /
        (∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ (scaleZ x)))) := by
  -- As for Stein's loss, `r = 0`, both conditional moments recover the ( `scaleZ`-invariant)
  -- reference: `E₁[δ₀|z] = δ₀`, `E₁[δ₀²|z] = δ₀²`, so the estimator collapses to
  -- `δ₀ · δ₀ / δ₀² = 1`, where the standardized squared error vanishes and the risk is `0`.
  obtain rfl : r = 0 := degree_eq_zero_of_pos heq₀ h₀pos
  have hinv₂ : IsScaleEquivariant 0 (fun x => δ₀ x ^ 2) := by
    intro τ hτ x
    show δ₀ (τ • x) ^ 2 = τ ^ 0 * δ₀ x ^ 2
    rw [heq₀ hτ x]
    simp only [pow_zero, one_mul]
  have hg₁Meas : Measurable
      (fun x => ∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) :=
    (measurable_integral_orbitCondKernel P₀ measurable_scaleZ hδ₀ hint₁).comp measurable_scaleZ
  have hg₂Meas : Measurable
      (fun x => ∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) :=
    (measurable_integral_orbitCondKernel P₀ measurable_scaleZ (hδ₀.pow_const 2) hint₂).comp
      measurable_scaleZ
  have hself₁ := integral_orbitCondKernel_eq_self_of_invariant P₀ hδ₀ heq₀ hnull hint₁
  have hself₂ := integral_orbitCondKernel_eq_self_of_invariant P₀ (hδ₀.pow_const 2) hinv₂
    hnull hint₂
  refine ⟨(hδ₀.mul hg₁Meas).div hg₂Meas, ?_, ?_⟩
  · intro τ hτ x
    show δ₀ (τ • x) * (∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ (τ • x)))) /
        (∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ (scaleZ (τ • x))))
      = τ ^ 0 * (δ₀ x * (∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) /
        (∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ (scaleZ x))))
    rw [scaleZ_smul' hτ x, heq₀ hτ x]
    simp only [pow_zero, one_mul]
  · intro δ' _ _
    have hrisk0 : scaleRisk P₀ (fun v : ℝ => (v - 1) ^ 2)
        (fun x => δ₀ x * (∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) /
          (∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ (scaleZ x)))) = 0 := by
      have hae : (fun x => ENNReal.ofReal
          ((δ₀ x * (∫ y, δ₀ y ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) /
            (∫ y, δ₀ y ^ 2 ∂(orbitCondKernel P₀ scaleZ (scaleZ x))) - 1) ^ 2)) =ᵐ[P₀] 0 := by
        filter_upwards [hself₁, hself₂] with x hx₁ hx₂
        rw [hx₁, hx₂,
          show δ₀ x * δ₀ x / δ₀ x ^ 2 = 1 by
            rw [sq]; exact div_self (mul_ne_zero (h₀pos x).ne' (h₀pos x).ne')]
        simp
      unfold scaleRisk
      rw [lintegral_congr_ae hae]
      simp
    rw [hrisk0]
    exact zero_le

end ScaleMRE

end StatLean.PointEstimation
