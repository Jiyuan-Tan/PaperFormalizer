module
public import StatLean.PointEstimation.LinearModel.Canonical
public import StatLean.PointEstimation.LinearModel.LeastSquares
public import StatLean.MultipleTesting.ForMathlib.ChiSquared
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section

/-!
# Equivariant optimality in the normal linear model

The estimators that are optimal among unbiased estimators are also optimal among
equivariant ones, for the natural groups acting on the normal linear model:

* translations of the signal block, `Y ↦ Y + (a, 0)`, under which `η ↦ η + a` and a linear
  functional `∑ λᵢ ηᵢ` of the mean shifts by `∑ λᵢ aᵢ` — the group for which `∑ λᵢ Yᵢ` is
  minimum risk equivariant under any convex even loss `ρ(d − ∑ λᵢ ηᵢ)`;
* the same translations together with the scale changes `Y ↦ cY`, under which
  `σ² ↦ c²σ²` — the group for which a fixed multiple of the residual sum of squares is
  minimum risk equivariant for `σ²` under the loss `(d − σ²)²/σ⁴`; the multiplier is a
  ratio of chi-square moments, and equals `1/(n − s + 2)`;
* translations by the mean subspace in the original coordinates, `X ↦ X + b` with `b ∈ W`,
  for which the least-squares functional is minimum risk equivariant.

Contents: `IsCanonicalEquivariant`, `canonicalRisk`, `IsCanonicalMRE`;
`IsCanonicalScaleEquivariant`, `canonicalScaleRisk`, `IsCanonicalScaleMRE`,
`residualScaleConst`; `IsSubspaceEquivariant`, `linearBaseRisk`, `IsSubspaceMRE`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.4 (Normal
Linear Models), Corollary 4.5 (the equivariance of the canonical estimators). (`TPE2 §3.4 Cor
4.5`.)

**Proof formalization notes.**
* *Lightweight group formalization.* Equivariance is expressed by explicit functional
  equations on the competing estimators (`IsCanonicalEquivariant`,
  `IsCanonicalScaleEquivariant`, `IsSubspaceEquivariant`) rather than through the general
  `[Group G] [MulAction G _]` framework. The acting groups here are concrete (`ℝˢ` acting
  by translation of a coordinate block, and its semidirect product with the positive
  reals), the induced action on the decision space is a shift or a power, and routing
  through the general framework would force an instance-heavy encoding for no gain. The
  general-framework bridge lemmas can be added later without changing these statements.
* *Constant risk.* Under each group the risk of an equivariant estimator is constant in the
  parameter, so minimum risk equivariance is stated as minimality of the risk at a single
  base parameter — `(η, σ²) = (0, σ²)` for the translation group and `(0, 1)` for the
  location-scale group. Losses enter `∫⁻` through `ENNReal.ofReal` (junk-value discipline).
* *The scale clause.* The optimal multiplier of the residual sum of squares is only pinned
  down once the acting group contains the scale changes: under translations alone the risk
  still depends on `σ²`. The statement below therefore uses the location-scale group, which
  is also the route by which the classical proof obtains the constant.
* *The constant.* `residualScaleConst m r` is the ratio of chi-square moments
  `E[V^r]/E[V^{2r}]`, `V ∼ χ²_m`; for `r = 1` the moments `E[V] = m` and
  `E[V²] = m(m + 2)` (`StatLean.MultipleTesting.integral_id_chiSquared` and
  `StatLean.MultipleTesting.variance_chiSquared`) give the classical
  `1/(m + 2) = 1/(n − s + 2)` — a larger denominator than the unbiased `1/(n − s)`.

**Bibliographic comments.** Equivariant estimation of location and scale parameters is due
to E. J. G. Pitman ("The estimation of the location and scale parameters of a continuous
population of any given form," *Biometrika* **30** (1939), 391–421); its use in the linear
model follows H. Scheffé (*The Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear
Statistical Inference and Its Applications*, 2nd ed., Wiley, 1973), with the
coordinate-free viewpoint of W. Kruskal ("When are Gauss–Markov and least squares
estimators identical?" in *Essays in Probability and Statistics*, 1965). The underlying
least-squares theory is that of C. F. Gauss (*Theoria combinationis observationum
erroribus minimis obnoxiae*, 1821/1823) and A. A. Markov (*Wahrscheinlichkeitsrechnung*,
Teubner, 1912). The distribution of the residual sum of squares goes back to F. R. Helmert
(*Z. Math. Phys.* **21** (1876), 192–218).
-/

open MeasureTheory ProbabilityTheory
open StatLean.MultipleTesting (chiSquared)
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {s m n : ℕ}

/-! ## Translations of the signal block -/

/-- **Equivariance under translations of the signal block**: shifting the first `s`
coordinates by `a` shifts the estimator of `∑ λᵢ ηᵢ` by `∑ λᵢ aᵢ`. -/
def IsCanonicalEquivariant (lam : Fin s → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))),
    δ (y + canonicalMean a) = δ y + ∑ i, lam i * a i

/-- Risk of `δ` at the base parameter `(η, σ²) = (0, σ²)` for a loss
`ρ(d − ∑ λᵢ ηᵢ)`; for equivariant estimators the risk equals this constant. -/
noncomputable def canonicalRisk (σ2 : PosVar) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ (δ y))
    ∂(canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2))

/-- **Minimum risk equivariant** estimator of `∑ λᵢ ηᵢ` under translations of the signal
block: measurable, equivariant, and of minimal (constant) risk among all such. -/
def IsCanonicalMRE (σ2 : PosVar) (lam : Fin s → ℝ) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  Measurable δ ∧ IsCanonicalEquivariant lam δ ∧
    ∀ δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ,
      Measurable δ' → IsCanonicalEquivariant lam δ' →
        canonicalRisk σ2 ρ δ ≤ canonicalRisk σ2 ρ δ'

/-! ### Convex-symmetric core (private scaffolding)

The reflection of the signal block, `Y ↦ (-Y_head, Y_res)`, is a symmetry of the base law
`canonicalModel (0, σ²)` (each coordinate is centred Gaussian), it negates `∑ λᵢ Yᵢ`, and it
is a signal-block translation, so it fixes `δ' − δ₀` for every equivariant `δ'`. Combined
with the pointwise midpoint convexity `ρ(δ₀) ≤ ½ρ(δ₀+h) + ½ρ(δ₀−h)` this gives the
minimality without any explicit head/residual independence decomposition. -/

/-- The reflection of the signal block: negates the first `s` coordinates, fixes the rest. -/
private noncomputable def canonicalReflect (y : EuclideanSpace ℝ (Fin (s + m))) :
    EuclideanSpace ℝ (Fin (s + m)) :=
  (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
    (fun k => if (k : ℕ) < s then -(y k) else y k)

private lemma measurable_canonicalReflect :
    Measurable (canonicalReflect (s := s) (m := m)) := by
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_lambda _ (fun k => ?_))
  by_cases h : (k : ℕ) < s
  · simp only [h, if_true]
    exact ((measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 _)).neg
  · simp only [h, if_false]
    exact (measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 _)

/-- The reflection is a translation of the signal block by `-2 Y_head`. -/
private lemma canonicalReflect_eq (y : EuclideanSpace ℝ (Fin (s + m))) :
    canonicalReflect y = y + canonicalMean (fun i => -2 * canonicalHead y i) := by
  ext k
  refine Fin.addCases (fun a => ?_) (fun b => ?_) k
  · show (if ((Fin.castAdd m a : Fin (s + m)) : ℕ) < s then -(y (Fin.castAdd m a))
          else y (Fin.castAdd m a))
        = y (Fin.castAdd m a) + (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.castAdd m a)
    rw [if_pos (by simpa using a.isLt)]
    rw [show (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.castAdd m a)
          = Fin.append (fun i => -2 * canonicalHead y i) (0 : Fin m → ℝ) (Fin.castAdd m a) from rfl,
        Fin.append_left]
    show -(y (Fin.castAdd m a)) = y (Fin.castAdd m a) + -2 * y (Fin.castAdd m a)
    ring
  · show (if ((Fin.natAdd s b : Fin (s + m)) : ℕ) < s then -(y (Fin.natAdd s b))
          else y (Fin.natAdd s b))
        = y (Fin.natAdd s b) + (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.natAdd s b)
    rw [if_neg (by simp)]
    rw [show (canonicalMean (fun i => -2 * canonicalHead y i)) (Fin.natAdd s b)
          = Fin.append (fun i => -2 * canonicalHead y i) (0 : Fin m → ℝ) (Fin.natAdd s b) from rfl,
        Fin.append_right, Pi.zero_apply, add_zero]

/-- The reflection preserves the base law `canonicalModel (0, σ²)`. -/
private lemma canonicalModel_zero_map_reflect (σ2 : PosVar) :
    (canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2)).map canonicalReflect
      = canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2) := by
  have hmeas_toLp :
      Measurable (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m))) :=
    WithLp.measurable_toLp 2 _
  set f : Fin (s + m) → ℝ → ℝ := fun k t => if (k : ℕ) < s then -t else t with hf
  have hmeas_f : ∀ k, Measurable (f k) := by
    intro k; by_cases h : (k : ℕ) < s <;> simp only [hf, h, if_true, if_false] <;> fun_prop
  have hcoord : ∀ k, (gaussianReal (0 : ℝ) σ2.1).map (f k) = gaussianReal 0 σ2.1 := by
    intro k
    by_cases h : (k : ℕ) < s
    · have hfk : f k = (fun t => -t) := by funext t; simp only [hf, h, if_true]
      rw [hfk, gaussianReal_map_neg, neg_zero]
    · have hfk : f k = fun t => t := by funext t; simp only [hf, h, if_false]
      rw [hfk, Measure.map_id']
  haveI hsf : ∀ k, SigmaFinite ((gaussianReal (0 : ℝ) σ2.1).map (f k)) := by
    intro k; rw [hcoord k]; infer_instance
  have hfam : (fun i : Fin (s + m) => gaussianReal ((canonicalMean (0 : Fin s → ℝ)) i) σ2.1)
      = (fun _ => gaussianReal (0 : ℝ) σ2.1) := by
    funext i
    congr 1
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · show (Fin.append (0 : Fin s → ℝ) (0 : Fin m → ℝ)) (Fin.castAdd m a) = 0
      rw [Fin.append_left]; rfl
    · show (Fin.append (0 : Fin s → ℝ) (0 : Fin m → ℝ)) (Fin.natAdd s b) = 0
      rw [Fin.append_right]; rfl
  have hbase : canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2)
      = (Measure.pi (fun _ : Fin (s + m) => gaussianReal (0 : ℝ) σ2.1)).map (WithLp.toLp 2) := by
    rw [canonicalModel]
    show (Measure.pi
          (fun i => gaussianReal ((canonicalMean (0 : Fin s → ℝ)) i) σ2.1)).map (WithLp.toLp 2)
        = (Measure.pi (fun _ => gaussianReal (0 : ℝ) σ2.1)).map (WithLp.toLp 2)
    rw [hfam]
  rw [hbase, Measure.map_map measurable_canonicalReflect hmeas_toLp]
  have hcomp :
      canonicalReflect ∘ (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
        = (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
            ∘ (fun x k => f k (x k)) := by
    funext x
    show canonicalReflect (WithLp.toLp 2 x) = WithLp.toLp 2 (fun k => f k (x k))
    rfl
  have hprod : Measurable (fun x : Fin (s + m) → ℝ => fun k => f k (x k)) :=
    measurable_pi_lambda _ (fun k => (hmeas_f k).comp (measurable_pi_apply k))
  rw [hcomp, ← Measure.map_map hmeas_toLp hprod,
    Measure.pi_map_pi (f := f) (fun k => (hmeas_f k).aemeasurable)]
  simp only [hcoord]

/-- The unbiased optimal estimator `∑ λᵢ Yᵢ` of `∑ λᵢ ηᵢ` is also minimum risk equivariant
under translations of the signal block, for every convex even loss. -/
theorem isCanonicalMRE_linear_combination
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional
    (lam : Fin s → ℝ) (σ2 : PosVar) {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss in the estimation error
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: even loss in the estimation error
    (heven : ∀ t : ℝ, ρ (-t) = ρ t) :
    IsCanonicalMRE (m := m) σ2 lam ρ (fun y => ∑ i, lam i * canonicalHead y i) := by
  set δ₀ : EuclideanSpace ℝ (Fin (s + m)) → ℝ := fun y => ∑ i, lam i * canonicalHead y i with hδ₀
  set M := canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), σ2) with hM
  -- `δ₀` is measurable and equivariant.
  have hδ₀meas : Measurable δ₀ := by
    rw [hδ₀]
    refine Finset.measurable_sum _ (fun i _ => measurable_const.mul ?_)
    exact (measurable_pi_apply (Fin.castAdd m i)).comp (WithLp.measurable_ofLp 2 _)
  have hHD : ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))) (i : Fin s),
      canonicalHead (y + canonicalMean a) i = canonicalHead y i + a i := by
    intro a y i
    have hsum : canonicalHead (y + canonicalMean a) i
        = canonicalHead y i + canonicalHead (canonicalMean (m := m) a) i := rfl
    have hcm : canonicalHead (canonicalMean (m := m) a) i = a i := by
      have hval : canonicalHead (canonicalMean (m := m) a) i
          = Fin.append a (0 : Fin m → ℝ) (Fin.castAdd m i) := rfl
      rw [hval, Fin.append_left]
    rw [hsum, hcm]
  have hδ₀equiv : IsCanonicalEquivariant lam δ₀ := by
    intro a y
    show ∑ i, lam i * canonicalHead (y + canonicalMean a) i
        = (∑ i, lam i * canonicalHead y i) + ∑ i, lam i * a i
    simp_rw [hHD, mul_add]
    rw [Finset.sum_add_distrib]
  refine ⟨hδ₀meas, hδ₀equiv, fun δ' hδ'meas hδ'equiv => ?_⟩
  -- `ρ` is continuous, hence measurable.
  have hρmeas : Measurable ρ :=
    (continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)).measurable
  -- `h := δ' − δ₀`; the reflection sends `δ'` to `δ₀ − (δ' − δ₀)` up to the even loss.
  set h : EuclideanSpace ℝ (Fin (s + m)) → ℝ := fun y => δ' y - δ₀ y with hh
  have hδ'eq : ∀ y, δ' y = δ₀ y + h y := fun y => by rw [hh]; ring
  -- reflection identity via equivariance of `δ'`
  have hsa : ∀ y, ∑ i, lam i * (-2 * canonicalHead y i) = -2 * δ₀ y := by
    intro y; rw [hδ₀, Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
  have hδ'R : ∀ y, δ' (canonicalReflect y) = -δ₀ y + h y := by
    intro y
    rw [canonicalReflect_eq y, hδ'equiv (fun i => -2 * canonicalHead y i) y, hsa y, hδ'eq y]
    ring
  -- pointwise midpoint convexity: `2 ρ(δ₀) ≤ ρ(δ₀+h) + ρ(δ₀−h)`
  have hpt : ∀ y, 2 * ρ (δ₀ y) ≤ ρ (δ₀ y + h y) + ρ (δ₀ y - h y) := by
    intro y
    have hc := hconv.2 (Set.mem_univ (δ₀ y + h y)) (Set.mem_univ (δ₀ y - h y))
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul] at hc
    rw [show (1 / 2 : ℝ) * (δ₀ y + h y) + (1 / 2 : ℝ) * (δ₀ y - h y) = δ₀ y by ring] at hc
    linarith
  -- measurability of the ENNReal integrands
  have hmeas0 : Measurable (fun y => ENNReal.ofReal (ρ (δ₀ y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp hδ₀meas)
  have hhmeas : Measurable h := hδ'meas.sub hδ₀meas
  have hmeasP : Measurable (fun y => ENNReal.ofReal (ρ (δ₀ y + h y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp (hδ₀meas.add hhmeas))
  have hmeasM : Measurable (fun y => ENNReal.ofReal (ρ (δ₀ y - h y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp (hδ₀meas.sub hhmeas))
  have hmeas' : Measurable (fun y => ENNReal.ofReal (ρ (δ' y))) :=
    ENNReal.measurable_ofReal.comp (hρmeas.comp hδ'meas)
  -- write the risk of `δ'` two ways using the reflection symmetry of the base law
  have hJp : canonicalRisk σ2 ρ δ' = ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y + h y)) ∂M := by
    show ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂M = _
    refine lintegral_congr (fun y => ?_)
    rw [hδ'eq y]
  have hJm : canonicalRisk σ2 ρ δ' = ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y - h y)) ∂M := by
    show ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂M = _
    calc ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂M
        = ∫⁻ y, ENNReal.ofReal (ρ (δ' y)) ∂(M.map canonicalReflect) := by
          rw [hM, canonicalModel_zero_map_reflect]
      _ = ∫⁻ y, ENNReal.ofReal (ρ (δ' (canonicalReflect y))) ∂M :=
          lintegral_map hmeas' measurable_canonicalReflect
      _ = ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y - h y)) ∂M := by
          refine lintegral_congr (fun y => ?_)
          rw [hδ'R y, show -δ₀ y + h y = -(δ₀ y - h y) by ring, heven]
  -- assemble: `2 · risk δ₀ ≤ 2 · risk δ'`
  have hfinal : 2 * canonicalRisk σ2 ρ δ₀ ≤ 2 * canonicalRisk σ2 ρ δ' := by
    calc 2 * canonicalRisk σ2 ρ δ₀
        = ∫⁻ y, 2 * ENNReal.ofReal (ρ (δ₀ y)) ∂M := by
          show 2 * ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y)) ∂M = _
          rw [← lintegral_const_mul 2 hmeas0]
      _ ≤ ∫⁻ y, (ENNReal.ofReal (ρ (δ₀ y + h y)) + ENNReal.ofReal (ρ (δ₀ y - h y))) ∂M := by
          refine lintegral_mono (fun y => ?_)
          calc 2 * ENNReal.ofReal (ρ (δ₀ y))
              = ENNReal.ofReal (2 * ρ (δ₀ y)) := by
                rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
            _ ≤ ENNReal.ofReal (ρ (δ₀ y + h y) + ρ (δ₀ y - h y)) := ENNReal.ofReal_le_ofReal (hpt y)
            _ ≤ ENNReal.ofReal (ρ (δ₀ y + h y)) + ENNReal.ofReal (ρ (δ₀ y - h y)) :=
                ENNReal.ofReal_add_le
      _ = (∫⁻ y, ENNReal.ofReal (ρ (δ₀ y + h y)) ∂M)
            + ∫⁻ y, ENNReal.ofReal (ρ (δ₀ y - h y)) ∂M :=
          lintegral_add_left hmeasP _
      _ = canonicalRisk σ2 ρ δ' + canonicalRisk σ2 ρ δ' := by rw [← hJp, ← hJm]
      _ = 2 * canonicalRisk σ2 ρ δ' := (two_mul _).symm
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hfinal

/-! ## Translations of the signal block together with scale changes -/

/-- **Equivariance of degree `2r` under the location-scale group**: the transformation
`y ↦ c(y + (a, 0))` multiplies an estimator of `σ^{2r} = (σ²)^r` by `c^{2r}`. -/
def IsCanonicalScaleEquivariant (r : ℕ) (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → ∀ (a : Fin s → ℝ) (y : EuclideanSpace ℝ (Fin (s + m))),
    δ (c • (y + canonicalMean a)) = c ^ (2 * r) * δ y

/-- Risk of `δ` at the base parameter `(η, σ²) = (0, 1)` for the loss
`(d − (σ²)^r)²/(σ²)^{2r}`; for equivariant estimators the risk equals this constant. -/
noncomputable def canonicalScaleRisk (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((δ y - 1) ^ 2)
    ∂(canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), ⟨1, zero_lt_one⟩))

/-- **Minimum risk equivariant** estimator of `(σ²)^r` under the location-scale group. -/
def IsCanonicalScaleMRE (r : ℕ) (δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ) : Prop :=
  Measurable δ ∧ IsCanonicalScaleEquivariant r δ ∧
    ∀ δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ,
      Measurable δ' → IsCanonicalScaleEquivariant r δ' →
        canonicalScaleRisk δ ≤ canonicalScaleRisk δ'

/-- The optimal multiplier of `(S²)^r`: the ratio `E[V^r]/E[V^{2r}]` of chi-square moments
with `k` degrees of freedom — the constant minimizing `E(c·V^r − 1)²`. -/
noncomputable def residualScaleConst (k r : ℕ) : ℝ :=
  (∫ v, v ^ r ∂(chiSquared k)) / (∫ v, v ^ (2 * r) ∂(chiSquared k))

open Set in
/-- Integrability of `x ↦ xᵏ` under `χ²ₘ` (`m ≥ 1`): mirrors the Gamma-moment brick. -/
private lemma integrable_pow_chiSquared {m : ℕ} (hm : 0 < m) (k : ℕ) :
    Integrable (fun x => x ^ k) (chiSquared m) := by
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set a : ℝ := (m : ℝ) / 2 with ha_def
  have ha : (0 : ℝ) < a := by rw [ha_def]; linarith
  have hr : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  rw [show chiSquared m = gammaMeasure a (1 / 2) from rfl]
  rw [gammaMeasure, integrable_withDensity_iff
        (show Measurable (gammaPDF a (1 / 2)) from
          (measurable_gammaPDFReal a (1 / 2)).ennreal_ofReal)
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hcongr : (fun x => x ^ k * (gammaPDF a (1 / 2) x).toReal)
      = fun x => x ^ k * gammaPDFReal a (1 / 2) x := by
    funext x
    rw [show gammaPDF a (1 / 2) x = ENNReal.ofReal (gammaPDFReal a (1 / 2) x) from rfl,
        ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
  rw [hcongr]
  have hmodel : IntegrableOn (fun x => x ^ (a + (k : ℝ) - 1) * Real.exp (-((1 / 2) * x)))
      (Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a + (k : ℝ) - 1) (b := 1 / 2)
      (by have := Nat.cast_nonneg (α := ℝ) k; linarith) one_pos hr
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hx
    beta_reduce; rw [Real.rpow_one, neg_mul]
  have hIoi : IntegrableOn (fun x => x ^ k * gammaPDFReal a (1 / 2) x) (Ioi (0 : ℝ)) volume := by
    refine IntegrableOn.congr_fun (hmodel.const_mul ((1 / 2) ^ a / Real.Gamma a))
      (fun x hx => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hx
    rw [gammaPDFReal, if_pos hx.le, ← Real.rpow_natCast x k,
        show a + (k : ℝ) - 1 = (a - 1) + (k : ℝ) by ring, Real.rpow_add hx (a - 1) (k : ℝ)]
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, hIoi⟩
  refine integrableOn_zero.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [mem_setOf_eq, Classical.not_imp, mem_Iic] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_eq_of_le hx1 with h | h
  · exact absurd (show x ^ k * gammaPDFReal a (1 / 2) x = 0 by
      rw [gammaPDFReal, if_neg (not_le.mpr h), mul_zero]).symm hx2
  · exact h

/-- The multiplier at `r = 1`: `E[V] = m` and `E[V²] = m(m + 2)` give
`residualScaleConst m 1 = 1/(m + 2)`, the classical `1/(n − s + 2)`. -/
theorem residualScaleConst_one
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    residualScaleConst m 1 = 1 / ((m : ℝ) + 2) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hI1 : ∫ v, v ^ 1 ∂(chiSquared m) = (m : ℝ) := by
    simp only [pow_one]; exact StatLean.MultipleTesting.integral_id_chiSquared hm
  have hI2 : ∫ v, v ^ (2 * 1) ∂(chiSquared m) = (m : ℝ) * ((m : ℝ) + 2) := by
    have e21 : (2 * 1 : ℕ) = 2 := rfl
    rw [e21]
    have hint1 : Integrable (fun x : ℝ => x) (chiSquared m) := by
      simpa using integrable_pow_chiSquared hm 1
    have hint2 : Integrable (fun x : ℝ => x ^ 2) (chiSquared m) := integrable_pow_chiSquared hm 2
    have hvar := StatLean.MultipleTesting.variance_chiSquared hm
    have hmean := StatLean.MultipleTesting.integral_id_chiSquared hm
    have hexp : ∀ x : ℝ, (x - (m : ℝ)) ^ 2 = x ^ 2 - 2 * (m : ℝ) * x + (m : ℝ) ^ 2 :=
      fun x => by ring
    have hf : Integrable (fun x : ℝ => x ^ 2 - 2 * (m : ℝ) * x) (chiSquared m) :=
      hint2.sub (hint1.const_mul (2 * (m : ℝ)))
    rw [show (∫ x, (x - (m : ℝ)) ^ 2 ∂(chiSquared m))
          = (∫ x, x ^ 2 ∂(chiSquared m)) - 2 * (m : ℝ) * (∫ x, x ∂(chiSquared m)) + (m : ℝ) ^ 2
        from by
        simp_rw [hexp]
        rw [integral_add hf (integrable_const _),
            integral_sub hint2 (hint1.const_mul (2 * (m : ℝ))), integral_const_mul,
            integral_const, probReal_univ, smul_eq_mul, one_mul]] at hvar
    rw [hmean] at hvar
    linarith [hvar]
  rw [residualScaleConst, hI1, hI2]
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Measurability of the residual sum of squares. -/
private lemma measurable_canonicalRSS :
    Measurable (canonicalRSS (s := s) (m := m)) :=
  Finset.measurable_sum _ (fun j _ =>
    (((measurable_pi_apply (Fin.natAdd s j)).comp (WithLp.measurable_ofLp 2 _))).pow_const 2)

/-- The residual sum of squares scales by `c²` under the location-scale group action
`y ↦ c(y + (a, 0))`: the signal shift `a` leaves every residual coordinate untouched and the
scaling multiplies each by `c`. -/
private lemma canonicalRSS_smul_add_canonicalMean (c : ℝ) (a : Fin s → ℝ)
    (y : EuclideanSpace ℝ (Fin (s + m))) :
    canonicalRSS (c • (y + canonicalMean a)) = c ^ 2 * canonicalRSS y := by
  simp only [canonicalRSS, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hmean : (canonicalMean a) (Fin.natAdd s j) = 0 := by
    show (Fin.append a (0 : Fin m → ℝ)) (Fin.natAdd s j) = 0
    rw [Fin.append_right]; rfl
  rw [PiLp.smul_apply, PiLp.add_apply, hmean, add_zero, smul_eq_mul, mul_pow]

/-! ### Gaussian scaling bricks (private scaffolding)

The location-scale optimality below rests on one analytic fact about the isotropic Gaussian:
a function invariant under positive scalings is *uncorrelated with the radius*. It is derived
here from the exact Gaussian tilt identity — tilting the standard product Gaussian by
`exp(-((λ−1)/2)‖x‖²)` is the same as changing the variance from `1` to `1/λ`, which a
scale-invariant integrand cannot see. -/

/-- Product of `N` centred Gaussians of variance `v` on `Fin N → ℝ`. -/
private noncomputable def piGauss (N : ℕ) (v : ℝ≥0) : Measure (Fin N → ℝ) :=
  Measure.pi fun _ : Fin N => gaussianReal 0 v

private instance instIsProbPiGauss (N : ℕ) (v : ℝ≥0) :
    IsProbabilityMeasure (piGauss N v) := by
  unfold piGauss; infer_instance

private lemma piGauss_withDensity (N : ℕ) {v : ℝ≥0} (hv : v ≠ 0) :
    piGauss N v
      = (volume : Measure (Fin N → ℝ)).withDensity
          (fun x => ∏ i, gaussianPDF 0 v (x i)) := by
  have h_each : (fun _ : Fin N => gaussianReal (0 : ℝ) v)
      = fun _ : Fin N => (volume : Measure ℝ).withDensity (gaussianPDF 0 v) := by
    funext _; exact gaussianReal_of_var_ne_zero 0 hv
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF (0 : ℝ) v)) := by
    rw [← gaussianReal_of_var_ne_zero (0 : ℝ) hv]; infer_instance
  rw [piGauss, h_each, ← pi_withDensity_prod (fun _ : Fin N => measurable_gaussianPDF (0 : ℝ) v),
    ← volume_pi]

private lemma piGauss_map_smul (N : ℕ) (c : ℝ) :
    (piGauss N 1).map (fun x => c • x) = piGauss N ⟨c ^ 2, sq_nonneg c⟩ := by
  have hf : ∀ _ : Fin N, AEMeasurable (fun t : ℝ => c * t) (gaussianReal 0 1) :=
    fun _ => (measurable_const_mul c).aemeasurable
  have hmap : ∀ _ : Fin N, (gaussianReal (0 : ℝ) 1).map (fun t : ℝ => c * t)
      = gaussianReal 0 (NNReal.mk (c ^ 2) (sq_nonneg c)) := by
    intro _
    rw [gaussianReal_map_const_mul (c := c), mul_zero, mul_one]
  haveI : ∀ _ : Fin N, SigmaFinite ((gaussianReal (0 : ℝ) 1).map (fun t : ℝ => c * t)) := by
    intro i; rw [hmap i]; infer_instance
  have hcast : (fun x : Fin N → ℝ => c • x) = fun (x : Fin N → ℝ) (i : Fin N) => c * x i := rfl
  unfold piGauss; rw [hcast, Measure.pi_map_pi hf]
  exact congrArg Measure.pi (funext hmap)

/-- The product of `N` centred Gaussian densities of variance `w`, in closed form. -/
private lemma prod_gaussianPDFReal (N : ℕ) (w : ℝ≥0) (x : Fin N → ℝ) :
    ∏ i, gaussianPDFReal 0 w (x i)
      = (Real.sqrt (2 * Real.pi * w))⁻¹ ^ N
          * Real.exp (-(∑ i, x i ^ 2) / (2 * (w : ℝ))) := by
  simp only [gaussianPDFReal, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  rw [neg_div, ← Finset.sum_div, Finset.sum_neg_distrib, neg_div]

/-- **Gaussian tilt identity.** For a measurable function `u` that is invariant under positive
scalings, tilting the standard product Gaussian by `exp(-((λ−1)/2)‖x‖²)` only multiplies the
integral of `u` by the constant `λ^{−N/2}` — the tilt is exactly a change of variance, and `u`
does not see it. -/
private lemma lintegral_hom_exp_tilt {N : ℕ} {u : (Fin N → ℝ) → ℝ≥0∞}
    (hu : Measurable u) (hhom : ∀ c : ℝ, 0 < c → ∀ x, u (c • x) = u x)
    {lam : ℝ} (hlam : 0 < lam) :
    ∫⁻ x, u x * ENNReal.ofReal (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2)) ∂(piGauss N 1)
      = ENNReal.ofReal ((Real.sqrt lam)⁻¹ ^ N) * ∫⁻ x, u x ∂(piGauss N 1) := by
  have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  set c : ℝ := (Real.sqrt lam)⁻¹ with hc_def
  have hcpos : 0 < c := by rw [hc_def]; positivity
  set v : ℝ≥0 := ⟨c ^ 2, sq_nonneg c⟩ with hv_def
  have hvcoe : (v : ℝ) = lam⁻¹ := by
    rw [hv_def]
    change c ^ 2 = lam⁻¹
    rw [hc_def, inv_pow, Real.sq_sqrt hlam.le]
  have hvne : v ≠ 0 := by
    intro h
    have : (v : ℝ) = 0 := by rw [h]; simp
    rw [hvcoe] at this
    exact absurd this (by positivity)
  -- the pointwise density identity
  have hdens : ∀ x : Fin N → ℝ,
      (∏ i, gaussianPDF 0 1 (x i)) * ENNReal.ofReal
          (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2))
        = ENNReal.ofReal ((Real.sqrt lam)⁻¹ ^ N) * ∏ i, gaussianPDF 0 v (x i) := by
    intro x
    have hprod : ∀ w : ℝ≥0, ∏ i, gaussianPDF 0 w (x i)
        = ENNReal.ofReal (∏ i, gaussianPDFReal 0 w (x i)) := by
      intro w
      simp only [gaussianPDF_def]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)]
    rw [hprod, hprod, ← ENNReal.ofReal_mul (Finset.prod_nonneg
        (fun i _ => gaussianPDFReal_nonneg _ _ _)),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [prod_gaussianPDFReal, prod_gaussianPDFReal, hvcoe, NNReal.coe_one, mul_one]
    have hlne : lam ≠ 0 := hlam.ne'
    have hconst : (Real.sqrt lam)⁻¹ ^ N * (Real.sqrt (2 * Real.pi * lam⁻¹))⁻¹ ^ N
        = (Real.sqrt (2 * Real.pi))⁻¹ ^ N := by
      have hcancel : lam * (2 * Real.pi * lam⁻¹) = 2 * Real.pi := by field_simp
      rw [← mul_pow, ← mul_inv, ← Real.sqrt_mul hlam.le, hcancel]
    have hexp : (-(∑ i, x i ^ 2)) / (2 * 1) + -((lam - 1) / 2) * ∑ i, x i ^ 2
        = (-(∑ i, x i ^ 2)) / (2 * lam⁻¹) := by
      field_simp
      ring
    rw [mul_assoc, ← Real.exp_add, ← mul_assoc, hconst, hexp]
  -- rewrite both sides as Lebesgue integrals against the explicit densities
  have hmeasD : ∀ w : ℝ≥0, Measurable (fun x : Fin N → ℝ => ∏ i, gaussianPDF 0 w (x i)) :=
    fun w => Finset.measurable_prod _
      (fun i _ => (measurable_gaussianPDF 0 w).comp (measurable_pi_apply i))
  have hmeasE : Measurable (fun x : Fin N → ℝ =>
      ENNReal.ofReal (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2))) := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact measurable_const.mul (Finset.measurable_sum _
      (fun i _ => (measurable_pi_apply i).pow_const 2))
  have hstep1 : ∫⁻ x, u x * ENNReal.ofReal
        (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2)) ∂(piGauss N 1)
      = ENNReal.ofReal ((Real.sqrt lam)⁻¹ ^ N) * ∫⁻ x, u x ∂(piGauss N v) := by
    rw [piGauss_withDensity N (one_ne_zero), piGauss_withDensity N hvne,
      lintegral_withDensity_eq_lintegral_mul _ (hmeasD 1) (hu.fun_mul hmeasE),
      lintegral_withDensity_eq_lintegral_mul _ (hmeasD v) hu]
    simp only [Pi.mul_apply]
    rw [← lintegral_const_mul _ ((hmeasD v).fun_mul hu)]
    refine lintegral_congr (fun x => ?_)
    rw [show (∏ i, gaussianPDF 0 1 (x i)) * (u x * ENNReal.ofReal
          (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2)))
        = ((∏ i, gaussianPDF 0 1 (x i)) * ENNReal.ofReal
          (Real.exp (-((lam - 1) / 2) * ∑ i, x i ^ 2))) * u x from by ring,
      hdens x, mul_assoc]
  rw [hstep1]
  congr 1
  rw [show v = ⟨c ^ 2, sq_nonneg c⟩ from rfl, ← piGauss_map_smul N c,
    lintegral_map hu (measurable_const_smul c)]
  exact lintegral_congr (fun x => hhom c hcpos x)


/-- The squared radius on the pi space. -/
private def sqSum {N : ℕ} (x : Fin N → ℝ) : ℝ := ∑ i, x i ^ 2

private lemma measurable_sqSum {N : ℕ} : Measurable (sqSum (N := N)) :=
  Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).pow_const 2)

/-- **Radius independence, bounded form.** A bounded, positively-scale-invariant `u` is
uncorrelated with every measurable function of the squared radius under the standard
product Gaussian. -/
private lemma lintegral_hom_mul_bounded {N : ℕ} {u : (Fin N → ℝ) → ℝ≥0∞}
    (hu : Measurable u) (hhom : ∀ c : ℝ, 0 < c → ∀ x, u (c • x) = u x)
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hbdd : ∀ x, u x ≤ K)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, u x * φ (sqSum x) ∂(piGauss N 1)
      = (∫⁻ x, u x ∂(piGauss N 1)) * ∫⁻ x, φ (sqSum x) ∂(piGauss N 1) := by
  set μ : Measure (Fin N → ℝ) := piGauss N 1 with hμ
  set C : ℝ≥0∞ := ∫⁻ x, u x ∂μ with hC
  have hCfin : C ≠ ⊤ := by
    have h1 : C ≤ K := by
      calc C ≤ ∫⁻ _, K ∂μ := lintegral_mono hbdd
        _ = K := by rw [lintegral_const, measure_univ, mul_one]
    exact ne_top_of_le_ne_top hK h1
  set ν₁ : Measure ℝ := (μ.withDensity u).map sqSum with hν₁
  set ν₂ : Measure ℝ := C • (μ.map sqSum) with hν₂
  have hval₁ : ∀ ψ : ℝ → ℝ≥0∞, Measurable ψ →
      ∫⁻ y, ψ y ∂ν₁ = ∫⁻ x, u x * ψ (sqSum x) ∂μ := by
    intro ψ hψ
    have hcomp : Measurable (fun x : Fin N → ℝ => ψ (sqSum x)) := hψ.comp measurable_sqSum
    rw [hν₁, lintegral_map hψ measurable_sqSum,
      lintegral_withDensity_eq_lintegral_mul _ hu hcomp]
    rfl
  have hval₂ : ∀ ψ : ℝ → ℝ≥0∞, Measurable ψ →
      ∫⁻ y, ψ y ∂ν₂ = C * ∫⁻ x, ψ (sqSum x) ∂μ := by
    intro ψ hψ
    rw [hν₂, lintegral_smul_measure, lintegral_map hψ measurable_sqSum, smul_eq_mul]
  haveI hfin₁ : IsFiniteMeasure ν₁ := by
    constructor
    rw [hν₁, Measure.map_apply measurable_sqSum MeasurableSet.univ, Set.preimage_univ,
      withDensity_apply u MeasurableSet.univ, setLIntegral_univ]
    exact hCfin.lt_top
  haveI hfin₂ : IsFiniteMeasure ν₂ := by
    constructor
    rw [hν₂, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply measurable_sqSum MeasurableSet.univ, Set.preimage_univ,
      measure_univ, mul_one]
    exact hCfin.lt_top
  -- the two Laplace transforms agree on `(-∞, 1/2)`
  have hexpmeas : ∀ t : ℝ, Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (t * y))) :=
    fun t => ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul t))
  have hlap : ∀ t : ℝ, t < 1 / 2 →
      (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₁
          = ENNReal.ofReal ((Real.sqrt (1 - 2 * t))⁻¹ ^ N) * C
        ∧ ∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₂
          = ENNReal.ofReal ((Real.sqrt (1 - 2 * t))⁻¹ ^ N) * C) := by
    intro t ht
    have hlam : (0 : ℝ) < 1 - 2 * t := by linarith
    have hcoef : -((1 - 2 * t - 1) / 2) = t := by ring
    constructor
    · rw [hval₁ _ (hexpmeas t)]
      have := lintegral_hom_exp_tilt (N := N) hu hhom hlam
      rw [hcoef] at this
      rw [show (fun x : Fin N → ℝ => u x * ENNReal.ofReal (Real.exp (t * sqSum x)))
            = fun x => u x * ENNReal.ofReal (Real.exp (t * ∑ i, x i ^ 2)) from rfl]
      exact this
    · rw [hval₂ _ (hexpmeas t)]
      have := lintegral_hom_exp_tilt (N := N) (u := fun _ => 1) measurable_const
        (fun c _ x => rfl) hlam
      rw [hcoef] at this
      simp only [one_mul, lintegral_const, measure_univ, mul_one] at this
      rw [show (fun x : Fin N → ℝ => ENNReal.ofReal (Real.exp (t * sqSum x)))
            = fun x => ENNReal.ofReal (Real.exp (t * ∑ i, x i ^ 2)) from rfl, this,
        mul_comm]
  have hfinlap : ∀ t : ℝ, t < 1 / 2 →
      ∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₁ ≠ ⊤ := by
    intro t ht
    rw [(hlap t ht).1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCfin
  have hint : ∀ (ν : Measure ℝ) (t : ℝ),
      (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν ≠ ⊤) →
      Integrable (fun y => Real.exp (t * y)) ν := by
    intro ν t htop
    refine ⟨(Real.measurable_exp.comp (measurable_const_mul t)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => (Real.exp_pos _).le))]
    exact lt_top_iff_ne_top.mpr htop
  have hbochner : ∀ (ν : Measure ℝ) (t : ℝ),
      ∫ y, Real.exp (t * y) ∂ν = (∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν).toReal := by
    intro ν t
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun y => (Real.exp_pos _).le))
      (Real.measurable_exp.comp (measurable_const_mul t)).aestronglyMeasurable
  have hfinlap₂ : ∀ t : ℝ, t < 1 / 2 →
      ∫⁻ y, ENNReal.ofReal (Real.exp (t * y)) ∂ν₂ ≠ ⊤ := by
    intro t ht
    rw [(hlap t ht).2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCfin
  have hkey : ν₁ = ν₂ := by
    refine ext_of_integral_exp_eqOn (S := Set.Iio (1 / 2 : ℝ))
      (by rw [interior_Iio]; exact ⟨0, by norm_num⟩)
      (fun t ht => hint _ t (hfinlap t ht))
      (fun t ht => hint _ t (hfinlap₂ t ht))
      (fun t ht => ?_)
    rw [hbochner, hbochner, (hlap t ht).1, (hlap t ht).2]
  rw [← hval₁ φ hφ, hkey, hval₂ φ hφ]

/-- **Radius independence.** A positively-scale-invariant `u` is uncorrelated with every
measurable function of the squared radius under the standard product Gaussian. -/
private lemma lintegral_hom_mul {N : ℕ} {u : (Fin N → ℝ) → ℝ≥0∞}
    (hu : Measurable u) (hhom : ∀ c : ℝ, 0 < c → ∀ x, u (c • x) = u x)
    {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, u x * φ (sqSum x) ∂(piGauss N 1)
      = (∫⁻ x, u x ∂(piGauss N 1)) * ∫⁻ x, φ (sqSum x) ∂(piGauss N 1) := by
  set μ : Measure (Fin N → ℝ) := piGauss N 1 with hμ
  set w : ℕ → (Fin N → ℝ) → ℝ≥0∞ := fun n x => min (u x) (n : ℝ≥0∞) with hw
  have hwmeas : ∀ n, Measurable (w n) := fun n => hu.min measurable_const
  have hwhom : ∀ n, ∀ c : ℝ, 0 < c → ∀ x, w n (c • x) = w n x := by
    intro n c hc x; rw [hw]; simp only [hhom c hc x]
  have hwmono : Monotone w := by
    intro a b hab x
    exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hab)
  have hwsup : ∀ x, ⨆ n, w n x = u x := by
    intro x
    refine le_antisymm (iSup_le (fun n => min_le_left _ _)) ?_
    exact le_of_forall_lt (fun b hb => by
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hb)
      exact lt_of_lt_of_le (lt_min hb hn) (le_iSup (fun n => w n x) n))
  have hstep : ∀ n, ∫⁻ x, w n x * φ (sqSum x) ∂μ
      = (∫⁻ x, w n x ∂μ) * ∫⁻ x, φ (sqSum x) ∂μ :=
    fun n => lintegral_hom_mul_bounded (hwmeas n) (hwhom n)
      (ENNReal.natCast_ne_top n) (fun x => min_le_right _ _) hφ
  have hφc : Measurable (fun x : Fin N → ℝ => φ (sqSum x)) := hφ.comp measurable_sqSum
  have hL : ∫⁻ x, u x * φ (sqSum x) ∂μ = ⨆ n, ∫⁻ x, w n x * φ (sqSum x) ∂μ := by
    rw [← lintegral_iSup (fun n => (hwmeas n).fun_mul hφc)
      (fun a b hab x => mul_le_mul' (hwmono hab x) le_rfl)]
    refine lintegral_congr (fun x => ?_)
    rw [← hwsup x, ENNReal.iSup_mul]
  have hR : ∫⁻ x, u x ∂μ = ⨆ n, ∫⁻ x, w n x ∂μ := by
    rw [← lintegral_iSup hwmeas (fun a b hab x => hwmono hab x)]
    exact lintegral_congr (fun x => (hwsup x).symm)
  rw [hL, hR, ENNReal.iSup_mul]
  exact iSup_congr hstep


private lemma sqSum_nonneg {N : ℕ} (x : Fin N → ℝ) : 0 ≤ sqSum x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private lemma sqSum_smul {N : ℕ} (c : ℝ) (x : Fin N → ℝ) :
    sqSum (c • x) = c ^ 2 * sqSum x := by
  simp only [sqSum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by
    rw [Pi.smul_apply, smul_eq_mul, mul_pow])

/-- The last `m` coordinates of a standard product Gaussian are again a standard product
Gaussian. -/
private lemma piGauss_map_tail (s m : ℕ) :
    (piGauss (s + m) 1).map (fun (x : Fin (s + m) → ℝ) (j : Fin m) => x (Fin.natAdd s j))
      = piGauss m 1 := by
  classical
  have hmeas : Measurable (fun (x : Fin (s + m) → ℝ) (j : Fin m) => x (Fin.natAdd s j)) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  change (Measure.pi fun _ : Fin (s + m) => gaussianReal (0 : ℝ) 1).map _
      = Measure.pi fun _ : Fin m => gaussianReal (0 : ℝ) 1
  refine (Measure.pi_eq (μ := fun _ : Fin m => gaussianReal (0 : ℝ) 1) (fun t ht => ?_)).symm
  set t' : Fin (s + m) → Set ℝ := Fin.addCases (fun _ => Set.univ) t with ht'
  have hleft : ∀ i : Fin s, t' (Fin.castAdd m i) = Set.univ := fun i => by
    rw [ht']; exact Fin.addCases_left i
  have hright : ∀ j : Fin m, t' (Fin.natAdd s j) = t j := fun j => by
    rw [ht']; exact Fin.addCases_right j
  have hpre : (fun (x : Fin (s + m) → ℝ) (j : Fin m) => x (Fin.natAdd s j)) ⁻¹'
      (Set.univ.pi t) = Set.univ.pi t' := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro h k
      refine Fin.addCases (fun i => ?_) (fun j => ?_) k
      · rw [hleft i]; exact Set.mem_univ _
      · rw [hright j]; exact h j
    · intro h j
      have hk := h (Fin.natAdd s j)
      rwa [hright j] at hk
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi ht), hpre, Measure.pi_pi,
    Fin.prod_univ_add]
  have hone : ∀ i : Fin s, (gaussianReal (0 : ℝ) 1) (t' (Fin.castAdd m i)) = 1 := by
    intro i; rw [hleft i]; exact measure_univ
  rw [Finset.prod_congr rfl (fun i _ => hone i), Finset.prod_const_one, one_mul]
  exact Finset.prod_congr rfl (fun j _ => by rw [hright j])

/-- The squared radius of a standard product Gaussian is `χ²ₘ`. -/
private lemma piGauss_map_sqSum {m : ℕ} (hm : 0 < m) :
    (piGauss m 1).map sqSum = chiSquared m := by
  have hlaw : ∀ i : Fin m,
      Measure.map (fun x : Fin m → ℝ => x i) (piGauss m 1) = gaussianReal 0 1 := fun i =>
    (measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) i).map_eq
  have hindep : iIndepFun (fun (i : Fin m) (x : Fin m → ℝ) => x i) (piGauss m 1) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  exact StatLean.MultipleTesting.map_sum_sq_eq_chiSquared hm (piGauss m 1)
    (fun i x => x i) (fun i => measurable_pi_apply i) hlaw hindep

/-- Integrability of the powers of the squared radius. -/
private lemma integrable_sqSum_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    Integrable (fun w : Fin m → ℝ => sqSum w ^ k) (piGauss m 1) := by
  have hasm : AEStronglyMeasurable (fun v : ℝ => v ^ k) ((piGauss m 1).map sqSum) :=
    (continuous_pow k).measurable.aestronglyMeasurable
  have h := integrable_pow_chiSquared hm k
  rw [← piGauss_map_sqSum hm] at h
  exact (integrable_map_measure hasm measurable_sqSum.aemeasurable).mp h

/-- The moments of the squared radius are the `χ²ₘ` moments. -/
private lemma integral_sqSum_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∫ w : Fin m → ℝ, sqSum w ^ k ∂(piGauss m 1) = ∫ v, v ^ k ∂(chiSquared m) := by
  have hasm : AEStronglyMeasurable (fun v : ℝ => v ^ k) ((piGauss m 1).map sqSum) :=
    (continuous_pow k).measurable.aestronglyMeasurable
  rw [← piGauss_map_sqSum hm, integral_map measurable_sqSum.aemeasurable hasm]

/-- The `ℝ≥0∞` form of the moments of the squared radius. -/
private lemma lintegral_sqSum_pow {m : ℕ} (hm : 0 < m) (k : ℕ) :
    ∫⁻ w : Fin m → ℝ, ENNReal.ofReal (sqSum w ^ k) ∂(piGauss m 1)
      = ENNReal.ofReal (∫ v, v ^ k ∂(chiSquared m)) := by
  rw [← integral_sqSum_pow hm k,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_sqSum_pow hm k)
      (ae_of_all _ (fun w => pow_nonneg (sqSum_nonneg w) k))]

/-- Positivity of the `χ²ₘ` moments (`m ≥ 1`). -/
private lemma chiSquared_moment_pos {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : 0 < k) :
    0 < ∫ v, v ^ k ∂(chiSquared m) := by
  classical
  rw [← integral_sqSum_pow hm k]
  rw [integral_pos_iff_support_of_nonneg (fun w => pow_nonneg (sqSum_nonneg w) k)
    (integrable_sqSum_pow hm k)]
  obtain ⟨j₀⟩ : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  have hZ : MeasurableSet {w : Fin m → ℝ | sqSum w = 0} :=
    measurableSet_eq_fun measurable_sqSum measurable_const
  have hnull : (piGauss m 1) {w : Fin m → ℝ | sqSum w = 0} = 0 := by
    have hsub : {w : Fin m → ℝ | sqSum w = 0} ⊆ {w : Fin m → ℝ | w j₀ = 0} := by
      intro w hw
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).mp hw
      have h0 := this j₀ (Finset.mem_univ j₀)
      exact sq_eq_zero_iff.mp h0
    refine measure_mono_null hsub ?_
    have hev : {w : Fin m → ℝ | w j₀ = 0} = (fun x : Fin m → ℝ => x j₀) ⁻¹' {(0 : ℝ)} := rfl
    haveI : NullSingletonClass (gaussianReal (0 : ℝ) 1) := nullSingletonClass_gaussianReal one_ne_zero
    have hmapev : Measure.map (fun x : Fin m → ℝ => x j₀) (piGauss m 1) = gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : Fin m => gaussianReal (0 : ℝ) 1) j₀).map_eq
    rw [hev, ← Measure.map_apply (measurable_pi_apply j₀) (measurableSet_singleton _), hmapev]
    exact measure_singleton 0
  have hsupp : (Function.support fun w : Fin m → ℝ => sqSum w ^ k)
      = {w : Fin m → ℝ | sqSum w = 0}ᶜ := by
    ext w
    simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_setOf_eq]
    exact ⟨fun h hc => h (by rw [hc, zero_pow hk.ne']), fun h hc =>
      h ((pow_eq_zero_iff hk.ne').mp hc)⟩
  rw [hsupp, prob_compl_eq_one_sub hZ, hnull, tsub_zero]
  exact zero_lt_one


/-- **Radius independence, `ℝ≥0∞` one-sided form.** -/
private lemma lintegral_ofReal_hom_mul_pow {m : ℕ} (hm : 0 < m) {g : (Fin m → ℝ) → ℝ}
    (hg : Measurable g) (hghom : ∀ c : ℝ, 0 < c → ∀ w, g (c • w) = g w) (k : ℕ) :
    ∫⁻ w, ENNReal.ofReal (g w * sqSum w ^ k) ∂(piGauss m 1)
      = ENNReal.ofReal (∫ v, v ^ k ∂(chiSquared m))
          * ∫⁻ w, ENNReal.ofReal (g w) ∂(piGauss m 1) := by
  have hSnn : ∀ w : Fin m → ℝ, (0 : ℝ) ≤ sqSum w ^ k := fun w => pow_nonneg (sqSum_nonneg w) k
  have hφ : Measurable (fun v : ℝ => ENNReal.ofReal (v ^ k)) :=
    ENNReal.measurable_ofReal.comp ((continuous_pow k).measurable)
  have hu : Measurable (fun w => ENNReal.ofReal (g w)) := ENNReal.measurable_ofReal.comp hg
  have huhom : ∀ c : ℝ, 0 < c → ∀ w, ENNReal.ofReal (g (c • w)) = ENNReal.ofReal (g w) :=
    fun c hc w => by rw [hghom c hc w]
  have hmain := lintegral_hom_mul (N := m) hu huhom hφ
  calc ∫⁻ w, ENNReal.ofReal (g w * sqSum w ^ k) ∂(piGauss m 1)
      = ∫⁻ w, ENNReal.ofReal (g w) * ENNReal.ofReal (sqSum w ^ k) ∂(piGauss m 1) :=
        lintegral_congr (fun w => ENNReal.ofReal_mul' (hSnn w))
    _ = (∫⁻ w, ENNReal.ofReal (g w) ∂(piGauss m 1))
          * ∫⁻ w, ENNReal.ofReal (sqSum w ^ k) ∂(piGauss m 1) := hmain
    _ = ENNReal.ofReal (∫ v, v ^ k ∂(chiSquared m))
          * ∫⁻ w, ENNReal.ofReal (g w) ∂(piGauss m 1) := by
        rw [lintegral_sqSum_pow hm k, mul_comm]

/-- **Signed radius independence.** For a `0`-homogeneous `h`, the `k`-th radial moment
factorizes: `∫ h ‖w‖^{2k} dγ = E[V^k] ∫ h dγ`. -/
private lemma integral_hom_mul_pow {m : ℕ} (hm : 0 < m) {h : (Fin m → ℝ) → ℝ}
    (hmeas : Measurable h) (hhom : ∀ c : ℝ, 0 < c → ∀ w, h (c • w) = h w) (k : ℕ)
    (hint : Integrable h (piGauss m 1))
    (hintS : Integrable (fun w => h w * sqSum w ^ k) (piGauss m 1)) :
    ∫ w, h w * sqSum w ^ k ∂(piGauss m 1)
      = (∫ v, v ^ k ∂(chiSquared m)) * ∫ w, h w ∂(piGauss m 1) := by
  set μ : Measure (Fin m → ℝ) := piGauss m 1 with hμ
  set Ak : ℝ := ∫ v, v ^ k ∂(chiSquared m) with hAk
  have hAknn : 0 ≤ Ak := by
    rw [hAk, ← integral_sqSum_pow hm k]
    exact integral_nonneg (fun w => pow_nonneg (sqSum_nonneg w) k)
  have hpos := lintegral_ofReal_hom_mul_pow hm hmeas hhom k
  have hneg := lintegral_ofReal_hom_mul_pow hm hmeas.fun_neg
    (fun c hc w => by simp only [hhom c hc w]) k
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hintS,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint]
  have hrw2 : ∫⁻ w, ENNReal.ofReal (-(h w * sqSum w ^ k)) ∂μ
      = ENNReal.ofReal Ak * ∫⁻ w, ENNReal.ofReal (-h w) ∂μ := by
    rw [← hneg]
    exact lintegral_congr (fun w => by rw [neg_mul])
  rw [hpos, hrw2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hAknn]
  ring

/-- **The location-scale `L²` minimization on the residual block.** Among the functions of
the residual vector that are positively homogeneous of degree `2r`, the multiple
`t⋆ ‖w‖^{2r}` of the radial power with `t⋆ = E[V^r]/E[V^{2r}]` minimizes `∫ (f − 1)² dγₘ`. -/
private lemma lintegral_scale_risk_le {m : ℕ} (hm : 0 < m) {r : ℕ} (hr : 0 < r)
    {f : (Fin m → ℝ) → ℝ} (hf : Measurable f)
    (hhom : ∀ c : ℝ, 0 < c → ∀ w, f (c • w) = c ^ (2 * r) * f w) :
    ∫⁻ w, ENNReal.ofReal ((residualScaleConst m r * sqSum w ^ r - 1) ^ 2) ∂(piGauss m 1)
      ≤ ∫⁻ w, ENNReal.ofReal ((f w - 1) ^ 2) ∂(piGauss m 1) := by
  set μ : Measure (Fin m → ℝ) := piGauss m 1 with hμ
  set Ar : ℝ := ∫ v, v ^ r ∂(chiSquared m) with hAr
  set A2r : ℝ := ∫ v, v ^ (2 * r) ∂(chiSquared m) with hA2r
  have hArpos : 0 < Ar := chiSquared_moment_pos hm hr
  have hA2rpos : 0 < A2r := chiSquared_moment_pos hm (by omega)
  have htdef : residualScaleConst m r = Ar / A2r := rfl
  have hsq : ∀ w : Fin m → ℝ, (sqSum w ^ r) ^ 2 = sqSum w ^ (2 * r) := fun w => by
    rw [← pow_mul, mul_comm]
  have habs : ∀ t : ℝ, |t| ≤ 1 + t ^ 2 := by
    intro t
    rcases le_or_gt |t| 1 with h | h
    · nlinarith [sq_nonneg t]
    · nlinarith [sq_abs t]
  -- the reference risk, computed exactly
  have hrefexp : ∀ w : Fin m → ℝ, (residualScaleConst m r * sqSum w ^ r - 1) ^ 2
      = residualScaleConst m r ^ 2 * sqSum w ^ (2 * r)
          - 2 * residualScaleConst m r * sqSum w ^ r + 1 := by
    intro w; rw [← hsq w]; ring
  have hrefint : Integrable (fun w => (residualScaleConst m r * sqSum w ^ r - 1) ^ 2) μ := by
    refine Integrable.congr ?_ (ae_of_all _ (fun w => (hrefexp w).symm))
    exact (((integrable_sqSum_pow hm (2 * r)).const_mul _).sub
      ((integrable_sqSum_pow hm r).const_mul _)).add (integrable_const 1)
  have href : ∫ w, (residualScaleConst m r * sqSum w ^ r - 1) ^ 2 ∂μ = 1 - Ar ^ 2 / A2r := by
    have hPa : Integrable
        (fun w : Fin m → ℝ => residualScaleConst m r ^ 2 * sqSum w ^ (2 * r)) μ :=
      (integrable_sqSum_pow hm (2 * r)).const_mul _
    have hPb : Integrable
        (fun w : Fin m → ℝ => 2 * residualScaleConst m r * sqSum w ^ r) μ :=
      (integrable_sqSum_pow hm r).const_mul _
    have hPab : Integrable (fun w : Fin m → ℝ => residualScaleConst m r ^ 2 * sqSum w ^ (2 * r)
        - 2 * residualScaleConst m r * sqSum w ^ r) μ := hPa.sub hPb
    rw [integral_congr_ae (ae_of_all _ hrefexp),
      integral_add hPab (integrable_const 1), integral_sub hPa hPb,
      integral_const_mul, integral_const_mul, integral_sqSum_pow hm, integral_sqSum_pow hm,
      integral_const, probReal_univ, smul_eq_mul, one_mul, htdef]
    field_simp
    ring
  by_cases htop : ∫⁻ w, ENNReal.ofReal ((f w - 1) ^ 2) ∂μ = ⊤
  · rw [htop]; exact le_top
  -- integrability of the competitor
  have hI1 : Integrable (fun w => (f w - 1) ^ 2) μ := by
    refine ⟨((hf.sub measurable_const).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun w => sq_nonneg (f w - 1)))]
    exact lt_top_iff_ne_top.mpr htop
  have hI2 : Integrable f μ := by
    refine Integrable.mono' ((integrable_const (2 : ℝ)).add hI1) hf.aestronglyMeasurable
      (ae_of_all _ (fun w => ?_))
    have h2 := habs (f w - 1)
    have h3 : f w - 1 ≤ |f w - 1| := le_abs_self _
    have h4 : -(f w - 1) ≤ |f w - 1| := neg_le_abs _
    have h5 : |f w| ≤ 2 + (f w - 1) ^ 2 := by
      rcases abs_cases (f w) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
    calc ‖f w‖ = |f w| := rfl
      _ ≤ 2 + (f w - 1) ^ 2 := h5
  have hI3 : Integrable (fun w => f w ^ 2) μ := by
    have hsum : Integrable (fun w : Fin m → ℝ => (f w - 1) ^ 2 + (2 * f w - 1)) μ :=
      hI1.add ((hI2.const_mul 2).sub (integrable_const 1))
    exact hsum.congr (ae_of_all _ (fun w => by ring))
  -- the scale-invariant factor `u = f / ‖w‖^{2r}`
  set u : (Fin m → ℝ) → ℝ := fun w => f w / sqSum w ^ r with hudef
  have humeas : Measurable u := hf.div (measurable_sqSum.pow_const r)
  have hf0 : f 0 = 0 := by
    have h2 := hhom 2 (by norm_num) 0
    rw [smul_zero] at h2
    have hgt : (1 : ℝ) < 2 ^ (2 * r) := by
      calc (1 : ℝ) < 2 := by norm_num
        _ = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (2 * r) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith [h2, hgt]
  have hsq0 : sqSum (0 : Fin m → ℝ) = 0 := by simp [sqSum]
  have hfu : ∀ w, f w = u w * sqSum w ^ r := by
    intro w
    by_cases hw : sqSum w = 0
    · have hw0 : w = 0 := by
        funext i
        have hi := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => sq_nonneg (w i))).mp hw i (Finset.mem_univ i)
        simpa using sq_eq_zero_iff.mp hi
      rw [hw0, hf0, hsq0, zero_pow hr.ne', mul_zero]
    · simp only [hudef]
      exact (div_mul_cancel₀ _ (pow_ne_zero r hw)).symm
  have huhom : ∀ c : ℝ, 0 < c → ∀ w, u (c • w) = u w := by
    intro c hc w
    have hcne : (c : ℝ) ^ (2 * r) ≠ 0 := by positivity
    simp only [hudef]
    rw [hhom c hc w, sqSum_smul, mul_pow, ← pow_mul, mul_div_mul_left _ _ hcne]
  have hu2hom : ∀ c : ℝ, 0 < c → ∀ w, u (c • w) ^ 2 = u w ^ 2 :=
    fun c hc w => by rw [huhom c hc w]
  have hfsq : ∀ w, f w ^ 2 = u w ^ 2 * sqSum w ^ (2 * r) := by
    intro w; rw [hfu w, mul_pow, hsq w]
  have hu2S : Integrable (fun w => u w ^ 2 * sqSum w ^ (2 * r)) μ :=
    hI3.congr (ae_of_all _ hfsq)
  -- `u ∈ L²`, from finiteness of the tilted integral
  have hlin := lintegral_ofReal_hom_mul_pow hm (humeas.pow_const 2) hu2hom (2 * r)
  have hLfin : ∫⁻ w, ENNReal.ofReal (u w ^ 2 * sqSum w ^ (2 * r)) ∂μ ≠ ⊤ :=
    ne_of_lt ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun w =>
      mul_nonneg (sq_nonneg (u w)) (pow_nonneg (sqSum_nonneg w) _)))).mp hu2S.2)
  have hu2fin : ∫⁻ w, ENNReal.ofReal (u w ^ 2) ∂μ ≠ ⊤ := by
    intro hc
    have hne : ENNReal.ofReal A2r ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hA2rpos
    rw [hlin, hc, ENNReal.mul_top hne] at hLfin
    exact hLfin rfl
  have hu2 : Integrable (fun w => u w ^ 2) μ :=
    ⟨(humeas.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun w => sq_nonneg (u w)))).mpr
        (lt_top_iff_ne_top.mpr hu2fin)⟩
  have huint : Integrable u μ := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add hu2) humeas.aestronglyMeasurable
      (ae_of_all _ (fun w => ?_))
    calc ‖u w‖ = |u w| := rfl
      _ ≤ 1 + u w ^ 2 := habs (u w)
  have hIu : Integrable (fun w => u w * sqSum w ^ r) μ := hI2.congr (ae_of_all _ hfu)
  -- the two moment identities
  have hmom1 : ∫ w, f w ∂μ = Ar * ∫ w, u w ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hfu)]
    exact integral_hom_mul_pow hm humeas huhom r huint hIu
  have hmom2 : ∫ w, f w ^ 2 ∂μ = A2r * ∫ w, u w ^ 2 ∂μ := by
    rw [integral_congr_ae (ae_of_all _ hfsq)]
    exact integral_hom_mul_pow hm (humeas.pow_const 2) hu2hom (2 * r) hu2 hu2S
  set a : ℝ := ∫ w, u w ∂μ with hadef
  set B : ℝ := ∫ w, u w ^ 2 ∂μ with hBdef
  have hCS : a ^ 2 ≤ B := by
    have hnn : 0 ≤ ∫ w, (u w - a) ^ 2 ∂μ := integral_nonneg (fun w => sq_nonneg _)
    have hCa : Integrable (fun w : Fin m → ℝ => u w ^ 2) μ := hu2
    have hCb : Integrable (fun w : Fin m → ℝ => 2 * a * u w) μ := huint.const_mul (2 * a)
    have hCab : Integrable (fun w : Fin m → ℝ => u w ^ 2 - 2 * a * u w) μ := hCa.sub hCb
    rw [integral_congr_ae (ae_of_all _ (fun w => show (u w - a) ^ 2
        = u w ^ 2 - 2 * a * u w + a ^ 2 from by ring)),
      integral_add hCab (integrable_const _),
      integral_sub hCa hCb, integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul] at hnn
    linarith
  have hfexp : ∫ w, (f w - 1) ^ 2 ∂μ = A2r * B - 2 * (Ar * a) + 1 := by
    have hFa : Integrable (fun w : Fin m → ℝ => f w ^ 2) μ := hI3
    have hFb : Integrable (fun w : Fin m → ℝ => 2 * f w) μ := hI2.const_mul 2
    have hFab : Integrable (fun w : Fin m → ℝ => f w ^ 2 - 2 * f w) μ := hFa.sub hFb
    rw [integral_congr_ae (ae_of_all _ (fun w => show (f w - 1) ^ 2
        = f w ^ 2 - 2 * f w + 1 from by ring)),
      integral_add hFab (integrable_const _),
      integral_sub hFa hFb, integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul, hmom1, hmom2]
  have hfinal : 1 - Ar ^ 2 / A2r ≤ ∫ w, (f w - 1) ^ 2 ∂μ := by
    rw [hfexp]
    have key : 2 * (Ar * a) - A2r * B ≤ Ar ^ 2 / A2r := by
      rw [le_div_iff₀ hA2rpos]
      nlinarith [sq_nonneg (A2r * a - Ar), mul_le_mul_of_nonneg_left hCS hA2rpos.le,
        hA2rpos, sq_nonneg A2r]
    linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hrefint (ae_of_all _ (fun w => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hI1 (ae_of_all _ (fun w => sq_nonneg _)), href]
  exact ENNReal.ofReal_le_ofReal hfinal


/-- **Analytic core of the location-scale MRE clause.** Minimality of the χ²-calibrated
multiple `residualScaleConst m r · (S²)^r` of the residual sum of squares, against every
measurable degree-`2r` location-scale-equivariant competitor.

Route (every step is a lemma proved above):

* *Reduction.* Head-translation equivariance (the `c = 1` case) makes an equivariant `δ'`
  invariant under `y ↦ y + (a, 0)`, so `δ'(y) = f(y_res)` with `f w := δ'(0, w)`, and the
  scaling clause makes `f` positively homogeneous of degree `2r`. Under the base parameter
  `(0, 1)` the residual block is a standard Gaussian `γₘ` (`piGauss_map_tail`), so the risk
  is `∫ (f − 1)² dγₘ`; the reference estimator is `f₀(w) = t⋆‖w‖^{2r}` with
  `t⋆ = residualScaleConst m r = E[V^r]/E[V^{2r}]` and `V = ‖w‖² ∼ χ²ₘ`
  (`piGauss_map_sqSum`).

* *Factorization.* Writing `f = u · ‖w‖^{2r}` with `u` invariant under positive scalings,
  the two moment identities `∫ f dγₘ = E[V^r] ∫ u dγₘ` and `∫ f² dγₘ = E[V^{2r}] ∫ u² dγₘ`
  hold (`integral_hom_mul_pow`): a scale-invariant function is *uncorrelated with the
  radius*. Cauchy–Schwarz `∫ u² ≥ (∫ u)²` and completing the square in `a = ∫ u dγₘ` give
  `∫ (f − 1)² ≥ 1 − E[V^r]²/E[V^{2r}] = ∫ (f₀ − 1)²` (`lintegral_scale_risk_le`).

* *Radius independence* (`lintegral_hom_mul`) is the single analytic input, and it is
  obtained **without** differentiating under the integral sign — the obstruction recorded in
  earlier versions of this file. The exact Gaussian tilt identity
  `∫ u · e^{−((λ−1)/2)‖x‖²} dγ = λ^{−N/2} ∫ u dγ` (`lintegral_hom_exp_tilt`; immediate from
  `gaussianReal_map_const_mul` and the product-density formula, because the tilt *is* a
  change of variance, which a scale-invariant `u` cannot see) says that the Laplace
  transforms of the two finite measures `(u·γ) ∘ ‖·‖²` and `(∫ u dγ) · χ²ₘ` agree on
  `(−∞, 1/2)`. Laplace-transform uniqueness (`ext_of_integral_exp_eqOn`) identifies the two
  measures, and monotone convergence removes the boundedness assumption on `u`. -/
private lemma canonicalScaleRisk_residualScaleConst_le
    (hm : 0 < m) {r : ℕ} (hr : 0 < r)
    (δ' : EuclideanSpace ℝ (Fin (s + m)) → ℝ) (hδ'meas : Measurable δ')
    (hδ'equiv : IsCanonicalScaleEquivariant r δ') :
    canonicalScaleRisk (s := s) (m := m) (fun y => residualScaleConst m r * canonicalRSS y ^ r)
      ≤ canonicalScaleRisk δ' := by
  classical
  have hcm0 : canonicalMean (m := m) (0 : Fin s → ℝ)
      = (0 : EuclideanSpace ℝ (Fin (s + m))) := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · change (Fin.append (0 : Fin s → ℝ) (0 : Fin m → ℝ)) (Fin.castAdd m a)
        = (0 : EuclideanSpace ℝ (Fin (s + m))) (Fin.castAdd m a)
      rw [Fin.append_left]; rfl
    · change (Fin.append (0 : Fin s → ℝ) (0 : Fin m → ℝ)) (Fin.natAdd s b)
        = (0 : EuclideanSpace ℝ (Fin (s + m))) (Fin.natAdd s b)
      rw [Fin.append_right]; rfl
  have hmodel : canonicalModel (s := s) (m := m) ((0 : Fin s → ℝ), ⟨1, zero_lt_one⟩)
      = (piGauss (s + m) 1).map (WithLp.toLp 2) := by
    rw [canonicalModel, hcm0, gaussianVector, canonicalNormal, piGauss]
    exact congrArg (fun ν => Measure.map (WithLp.toLp 2) ν)
      (congrArg Measure.pi (funext (fun i => rfl)))
  have hrisk : ∀ δ : EuclideanSpace ℝ (Fin (s + m)) → ℝ, Measurable δ →
      canonicalScaleRisk (s := s) (m := m) δ
        = ∫⁻ x, ENNReal.ofReal ((δ (WithLp.toLp 2 x) - 1) ^ 2) ∂(piGauss (s + m) 1) := by
    intro δ hδ
    have hmeasφ : Measurable (fun y : EuclideanSpace ℝ (Fin (s + m)) =>
        ENNReal.ofReal ((δ y - 1) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((hδ.sub measurable_const).pow_const 2)
    rw [canonicalScaleRisk, hmodel, lintegral_map hmeasφ (WithLp.measurable_toLp 2 _)]
  set tl : (Fin (s + m) → ℝ) → (Fin m → ℝ) := fun x j => x (Fin.natAdd s j) with htl
  have htlmeas : Measurable tl := measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  have htail : ∀ F : (Fin m → ℝ) → ℝ≥0∞, Measurable F →
      ∫⁻ x, F (tl x) ∂(piGauss (s + m) 1) = ∫⁻ w, F w ∂(piGauss m 1) := by
    intro F hF
    rw [← piGauss_map_tail s m, lintegral_map hF htlmeas]
  set f : (Fin m → ℝ) → ℝ :=
    fun w => δ' (WithLp.toLp 2 (Fin.append (0 : Fin s → ℝ) w)) with hfdef
  have hap : Measurable
      (fun w : Fin m → ℝ => (Fin.append (0 : Fin s → ℝ) w : Fin (s + m) → ℝ)) := by
    refine measurable_pi_lambda _ (fun k => ?_)
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · simp only [Fin.append_left]; exact measurable_const
    · simp only [Fin.append_right]; exact measurable_pi_apply b
  have hfmeas : Measurable f := hδ'meas.comp ((WithLp.measurable_toLp 2 _).comp hap)
  have hdecomp : ∀ x : Fin (s + m) → ℝ,
      (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (s + m)))
        = WithLp.toLp 2 (Fin.append (0 : Fin s → ℝ) (tl x))
            + canonicalMean (fun i => x (Fin.castAdd m i)) := by
    intro x
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · change x (Fin.castAdd m a)
        = Fin.append (0 : Fin s → ℝ) (tl x) (Fin.castAdd m a)
          + Fin.append (fun i => x (Fin.castAdd m i)) (0 : Fin m → ℝ) (Fin.castAdd m a)
      rw [Fin.append_left, Fin.append_left]
      change x (Fin.castAdd m a) = 0 + x (Fin.castAdd m a)
      rw [zero_add]
    · change x (Fin.natAdd s b)
        = Fin.append (0 : Fin s → ℝ) (tl x) (Fin.natAdd s b)
          + Fin.append (fun i => x (Fin.castAdd m i)) (0 : Fin m → ℝ) (Fin.natAdd s b)
      rw [Fin.append_right, Fin.append_right]
      change x (Fin.natAdd s b) = x (Fin.natAdd s b) + 0
      rw [add_zero]
  have hδ'f : ∀ x : Fin (s + m) → ℝ, δ' (WithLp.toLp 2 x) = f (tl x) := by
    intro x
    rw [hdecomp x]
    have h1 := hδ'equiv (c := 1) zero_lt_one (fun i => x (Fin.castAdd m i))
      (WithLp.toLp 2 (Fin.append (0 : Fin s → ℝ) (tl x)))
    rw [one_smul, one_pow, one_mul] at h1
    rw [h1]
  have hfhom : ∀ c : ℝ, 0 < c → ∀ w, f (c • w) = c ^ (2 * r) * f w := by
    intro c hc w
    have happ : (Fin.append (0 : Fin s → ℝ) (c • w) : Fin (s + m) → ℝ)
        = c • Fin.append (0 : Fin s → ℝ) w := by
      funext k
      refine Fin.addCases (fun a => ?_) (fun b => ?_) k
      · rw [Fin.append_left]
        change (0 : ℝ) = c * Fin.append (0 : Fin s → ℝ) w (Fin.castAdd m a)
        rw [Fin.append_left]
        change (0 : ℝ) = c * (0 : ℝ)
        rw [mul_zero]
      · rw [Fin.append_right]
        change c * w b = c * Fin.append (0 : Fin s → ℝ) w (Fin.natAdd s b)
        rw [Fin.append_right]
    simp only [hfdef]
    rw [happ]
    have h1 := hδ'equiv hc (0 : Fin s → ℝ)
      (WithLp.toLp 2 (Fin.append (0 : Fin s → ℝ) w))
    rw [hcm0, add_zero] at h1
    exact h1
  rw [hrisk _ (measurable_const.fun_mul (measurable_canonicalRSS.pow_const r)), hrisk _ hδ'meas]
  have hL : ∀ x : Fin (s + m) → ℝ,
      residualScaleConst m r * canonicalRSS (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin (s + m))) ^ r
        = residualScaleConst m r * sqSum (tl x) ^ r := fun x => rfl
  simp only [hL, hδ'f]
  have hF1 : Measurable (fun w : Fin m → ℝ =>
      ENNReal.ofReal ((residualScaleConst m r * sqSum w ^ r - 1) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_const.mul (measurable_sqSum.pow_const r)).sub measurable_const).pow_const 2)
  have hF2 : Measurable (fun w : Fin m → ℝ => ENNReal.ofReal ((f w - 1) ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hfmeas.sub measurable_const).pow_const 2)
  rw [htail _ hF1, htail _ hF2]
  exact lintegral_scale_risk_le hm hr hfmeas hfhom

/-- A fixed multiple of `(S²)^r` is minimum risk equivariant for `(σ²)^r` under the
location-scale group, the multiplier being the chi-square moment ratio. -/
theorem isCanonicalScaleMRE_residual_pow
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the degree of the estimated power of the variance
    {r : ℕ} (hr : 0 < r) :
    IsCanonicalScaleMRE (s := s) (m := m) r
      (fun y => residualScaleConst m r * canonicalRSS y ^ r) := by
  refine ⟨measurable_const.mul (measurable_canonicalRSS.pow_const r), ?_, ?_⟩
  · -- equivariance: `S²` scales by `c²`, so `(S²)^r` scales by `c^{2r}`
    intro c _ a y
    show residualScaleConst m r * canonicalRSS (c • (y + canonicalMean a)) ^ r
        = c ^ (2 * r) * (residualScaleConst m r * canonicalRSS y ^ r)
    rw [canonicalRSS_smul_add_canonicalMean, mul_pow, ← pow_mul]
    ring
  · -- minimality: the analytic core, factored out as a named `private` lemma
    exact fun δ' hδ'meas hδ'equiv =>
      canonicalScaleRisk_residualScaleConst_le hm hr δ' hδ'meas hδ'equiv

/-- The classical variance clause: under the loss `(d − σ²)²/σ⁴`, the minimum risk
equivariant estimator of `σ²` is `S²/(m + 2)`, that is `S²/(n − s + 2)`. -/
theorem isCanonicalScaleMRE_residual_variance
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    IsCanonicalScaleMRE (s := s) (m := m) 1 (fun y => canonicalRSS y / ((m : ℝ) + 2)) := by
  -- The variance clause is the `r = 1` case of `isCanonicalScaleMRE_residual_pow`, with the
  -- chi-square moment ratio evaluated by `residualScaleConst_one`.
  have h := isCanonicalScaleMRE_residual_pow (s := s) (m := m) hm (r := 1) one_pos
  have heq : (fun y : EuclideanSpace ℝ (Fin (s + m)) => residualScaleConst m 1 * canonicalRSS y ^ 1)
      = fun y => canonicalRSS y / ((m : ℝ) + 2) := by
    funext y; rw [residualScaleConst_one hm, pow_one]; ring
  rw [heq] at h
  exact h

/-! ## Translations by the mean subspace, in the original coordinates -/

/-- **Equivariance under translations by the mean subspace**: shifting the observation by
`b ∈ W` shifts an estimator of `⟪γ, ξ⟫` by `⟪γ, b⟫`. -/
def IsSubspaceEquivariant (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (γ : EuclideanSpace ℝ (Fin n)) (δ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ b ∈ W, ∀ y : EuclideanSpace ℝ (Fin n), δ (y + b) = δ y + ⟪γ, b⟫_ℝ

/-- Risk of `δ` at the base parameter `ξ = 0` for a loss `ρ(d − ⟪γ, ξ⟫)`; for equivariant
estimators the risk equals this constant. -/
noncomputable def linearBaseRisk (σ2 : PosVar) (ρ : ℝ → ℝ)
    (δ : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ (δ y)) ∂(gaussianVector (0 : EuclideanSpace ℝ (Fin n)) σ2.1)

/-- **Minimum risk equivariant** estimator of `⟪γ, ξ⟫` under translations by the mean
subspace. -/
def IsSubspaceMRE (W : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (σ2 : PosVar)
    (γ : EuclideanSpace ℝ (Fin n)) (ρ : ℝ → ℝ) (δ : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  Measurable δ ∧ IsSubspaceEquivariant W γ δ ∧
    ∀ δ', Measurable δ' → IsSubspaceEquivariant W γ δ' →
      linearBaseRisk σ2 ρ δ ≤ linearBaseRisk σ2 ρ δ'

/-- The least-squares functional is minimum risk equivariant for `⟪γ, ξ⟫` under
translations by the mean subspace, for every convex even loss. -/
theorem isSubspaceMRE_lse_functional (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model
    (hW : Module.finrank ℝ W < n) (σ2 : PosVar)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional, taken
    -- inside the mean subspace (a general one is replaced by its projection)
    {γ : EuclideanSpace ℝ (Fin n)} (hγ : γ ∈ W) {ρ : ℝ → ℝ}
    -- USER-INPUT: convex loss in the estimation error
    (hconv : ConvexOn ℝ Set.univ ρ)
    -- USER-INPUT: even loss in the estimation error
    (heven : ∀ t : ℝ, ρ (-t) = ρ t) :
    IsSubspaceMRE W σ2 γ ρ (fun y => ⟪γ, lse W y⟫_ℝ) := by
  classical
  obtain ⟨m, hm, hsm, L, hmean, hsurj, hRSS, hlse⟩ := exists_headSubspace_isometry W hW
  set δ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => ⟪γ, lse W y⟫_ℝ with hδdef
  set lam : Fin (Module.finrank ℝ W) → ℝ := canonicalHead (L γ) with hlam
  have hρmeas : Measurable ρ :=
    (continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)).measurable
  have hLmeas : Measurable L := L.continuous.measurable
  have hLsymm : Measurable (L.symm : _ → EuclideanSpace ℝ (Fin n)) := L.symm.continuous.measurable
  -- the base law transports to the canonical base law
  have hcm0 : canonicalMean (0 : Fin (Module.finrank ℝ W) → ℝ)
      = (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + m))) := by
    ext k
    refine Fin.addCases (fun a => ?_) (fun b => ?_) k
    · show (Fin.append (0 : Fin (Module.finrank ℝ W) → ℝ) (0 : Fin m → ℝ)) (Fin.castAdd m a)
          = (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + m))) (Fin.castAdd m a)
      rw [Fin.append_left]; rfl
    · show (Fin.append (0 : Fin (Module.finrank ℝ W) → ℝ) (0 : Fin m → ℝ)) (Fin.natAdd _ b)
          = (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ W + m))) (Fin.natAdd _ b)
      rw [Fin.append_right]; rfl
  have hbaseL : (gaussianVector (0 : EuclideanSpace ℝ (Fin n)) σ2.1).map L
      = canonicalModel (s := Module.finrank ℝ W) (m := m)
          ((0 : Fin (Module.finrank ℝ W) → ℝ), σ2) := by
    rw [gaussianVector_map_linearIsometryEquiv L 0 σ2.1, map_zero, canonicalModel, hcm0]
  -- risk change of variables `linearBaseRisk f = canonicalRisk (f ∘ L⁻¹)`
  have hbridge : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, Measurable f →
      linearBaseRisk σ2 ρ f = canonicalRisk σ2 ρ (fun z => f (L.symm z)) := by
    intro f hf
    have hφ : Measurable (fun z => ENNReal.ofReal (ρ (f (L.symm z)))) :=
      ENNReal.measurable_ofReal.comp (hρmeas.comp (hf.comp hLsymm))
    show ∫⁻ y, ENNReal.ofReal (ρ (f y)) ∂(gaussianVector (0 : EuclideanSpace ℝ (Fin n)) σ2.1)
        = ∫⁻ z, ENNReal.ofReal (ρ (f (L.symm z)))
            ∂(canonicalModel (s := Module.finrank ℝ W) (m := m) (_, σ2))
    rw [← hbaseL, lintegral_map hφ hLmeas]
    refine lintegral_congr (fun y => ?_)
    rw [L.symm_apply_apply]
  -- the estimator, transported, is exactly `δ₀` of the canonical core
  have hδL : (fun z => δ (L.symm z)) = fun z => ∑ i, lam i * canonicalHead z i := by
    funext z
    rw [hδdef]
    show ⟪γ, lse W (L.symm z)⟫_ℝ = ∑ i, lam i * canonicalHead z i
    rw [hlse γ hγ (L.symm z), L.apply_symm_apply]
  have hδmeas : Measurable δ := by
    rw [hδdef]
    exact (continuous_const.inner W.starProjection.continuous).measurable
  refine ⟨hδmeas, ?_, fun δ' hδ'meas hδ'equiv => ?_⟩
  · -- subspace-equivariance of `δ`
    intro b hb y
    rw [hδdef]
    show ⟪γ, lse W (y + b)⟫_ℝ = ⟪γ, lse W y⟫_ℝ + ⟪γ, b⟫_ℝ
    rw [show lse W (y + b) = W.starProjection (y + b) from rfl,
      show lse W y = W.starProjection y from rfl, map_add,
      Submodule.starProjection_eq_self_iff.mpr hb, inner_add_right]
  · -- minimality via the canonical convex-symmetric core
    obtain ⟨_, _, hmin⟩ :=
      isCanonicalMRE_linear_combination (s := Module.finrank ℝ W) (m := m) hm lam σ2 hconv heven
    rw [hbridge δ hδmeas, hbridge δ' hδ'meas, hδL]
    refine hmin (fun z => δ' (L.symm z)) (hδ'meas.comp hLsymm) ?_
    -- `δ' ∘ L⁻¹` is canonically equivariant with coefficient vector `lam`
    intro a z
    show δ' (L.symm (z + canonicalMean a)) = δ' (L.symm z) + ∑ i, lam i * a i
    obtain ⟨x, hx⟩ := hsurj a
    change canonicalHead (L (x : EuclideanSpace ℝ (Fin n))) = a at hx
    have hLx : L (x : EuclideanSpace ℝ (Fin n)) = canonicalMean a := by
      rw [hmean (x : EuclideanSpace ℝ (Fin n)) x.2, hx]
    have hsymm : L.symm (canonicalMean a) = (x : EuclideanSpace ℝ (Fin n)) := by
      rw [← hLx, L.symm_apply_apply]
    rw [map_add, hsymm, hδ'equiv (x : EuclideanSpace ℝ (Fin n)) x.2 (L.symm z)]
    congr 1
    have hxproj : lse W (x : EuclideanSpace ℝ (Fin n)) = (x : EuclideanSpace ℝ (Fin n)) :=
      Submodule.starProjection_eq_self_iff.mpr x.2
    have hxval := hlse γ hγ (x : EuclideanSpace ℝ (Fin n))
    rw [hxproj] at hxval
    rw [hxval]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hlam, hx]

end StatLean.PointEstimation
