module
public import StatLean.PointEstimation.InformationInequality.Basic
public import StatLean.PointEstimation.ExponentialFamily.Defs
public import StatLean.PointEstimation.ExponentialFamily.MGF
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.MGFAnalytic

@[expose] public section

/-!
# The Fisher information of an exponential family

In canonical form the log-density of an exponential family is `⟨η, T(x)⟩ − A(η)`, so its
score in the natural parameter is `T(x) − ∇A(η)`: the natural statistic, centered. The
information is therefore the *curvature of the log-partition function*, equivalently the
covariance of the natural statistic:
$$ I(\eta) = A''(\eta) \quad (\text{one-dimensional}), \qquad
   I(\eta)_{ij} = \frac{\partial^2 A}{\partial\eta_i\,\partial\eta_j}(\eta)
               = \operatorname{cov}_\eta\bigl(T_i, T_j\bigr) \quad (s\text{-dimensional}). $$

Contents:
* `ExpFamily.toParametricFamily` — the canonical family read as a family of densities
  `exp(⟨η, T(x)⟩ − A(η))` with respect to the reference measure, so that the score and the
  information of this area apply to it;
* `fisherInfo_expFamily` — the one-dimensional identity `I(η) = A''(η)`;
* `infoMatrix_expFamily` — the information matrix is the covariance matrix of the natural
  statistic.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), Theorem 5.4 (the Fisher information of an exponential family is
`A″`). (`TPE2 §2.5 Thm 5.4`.)

**Proof formalization notes.**
* Both statements are given in the *natural* parametrization, where the score is
  `T − ∇A` and the identities are clean. The mean-value parametrization `τ = ∇A(η)` — in
  which the information is the *inverse* of the covariance matrix of `T`, and in dimension
  one `I(τ) = 1 / var_θ(T)` — follows by the reparametrization rule for the information
  (`fisherInfo_reparam` and its matrix analogue), since the Jacobian of `η ↦ τ(η)` is that
  same covariance matrix. This is a deliberate change of presentation, not of content.
* Smoothness of `A` is not assumed: it is forced by membership of `η` in the *interior* of
  the natural parameter set, where the log-partition function is analytic. That single
  membership hypothesis is therefore the only regularity input, and differentiability
  statements about `A` are consequences (proved in the exponential-family smoothness file),
  not hypotheses here.
* The density presentation `exp(⟨η, T x⟩ − A(η))` relative to `base` agrees with the
  member measure built by exponential tilting; where the reference measure is the zero
  measure both sides of the identities degenerate to `0` and the statements remain true.
* The `s`-dimensional statement is phrased entrywise, with the covariance of the coordinate
  statistics under the member measure, which is the form consumed by the multiparameter
  information inequality.

**Bibliographic comments.** The identification of the information of an exponential family
with the curvature of its cumulant function goes back to R. A. Fisher ("Theory of
statistical estimation," *Proc. Camb. Phil. Soc.* **22** (1925), 700–725) and to the
characterizations of exponential families by G. Darmois ("Sur les lois de probabilité à
estimation exhaustive," *C. R. Acad. Sci. Paris* **200** (1935), 1265–1266), B. O. Koopman
("On distributions admitting a sufficient statistic," *Trans. Amer. Math. Soc.* **39**
(1936), 399–409) and E. J. G. Pitman ("Sufficient statistics and intrinsic accuracy,"
*Proc. Camb. Phil. Soc.* **32** (1936), 567–579). The matrix form of the information, and
its role in the multiparameter bound, are due to C. R. Rao ("Information and the accuracy
attainable in the estimation of statistical parameters," *Bull. Calcutta Math. Soc.* **37**
(1945), 81–91); the convex-analytic treatment of the log-partition function is that of
L. D. Brown (*Fundamentals of Statistical Exponential Families*, IMS Lecture Notes 9, 1986).
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [OpensMeasurableSpace V]

/-- The canonical exponential family **read as a family of densities**
`p_η(x) = exp(⟨η, T(x)⟩ − A(η))` relative to its reference measure, so that the score and
the Fisher information of this area apply to it directly. The densities are positive
everywhere, so the family trivially has a common support. -/
noncomputable def ExpFamily.toParametricFamily (E : ExpFamily 𝓧 V) : ParametricFamily 𝓧 V where
  density η x := Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η)
  density_meas η := by
    have h : Continuous fun v : V => ⟪η, v⟫_ℝ := continuous_const.inner continuous_id
    exact ((h.measurable.comp E.stat_meas).sub measurable_const).exp
  density_nonneg _ _ := Real.exp_nonneg _

/-- **The information of a one-dimensional canonical exponential family is the curvature of
its log-partition function**: `I(η) = A''(η)`.

The score is the centered natural statistic `T − A'(η)`, so the information is the variance
of `T` under the member measure, which is the second derivative of `A`. In the mean-value
parametrization this becomes the reciprocal of that variance, by the reparametrization rule
for the information. -/
theorem fisherInfo_expFamily (E : ExpFamily 𝓧 ℝ) (η : ℝ)
    -- USER-INPUT: the natural parameter lies in the interior of the natural parameter set;
    -- the classical condition under which the log-partition function is smooth (and hence
    -- the only regularity input of the statement)
    (hη : η ∈ interior E.natSet) :
    fisherInfo E.toParametricFamily E.base η = deriv (deriv E.logPartition) η := by
  have hηnat : η ∈ E.natSet := interior_subset hη
  have hmem : η ∈ interior (integrableExpSet E.stat E.base) := by
    rw [← E.natSet_eq_integrableExpSet]; exact hη
  -- inner product on ℝ is multiplication
  have hinner : ∀ a b : ℝ, ⟪a, b⟫_ℝ = a * b := fun a b => by rw [← real_inner_comm]; rfl
  -- the log-partition function is differentiable at `η`
  have hA : HasDerivAt E.logPartition (deriv E.logPartition η) η := by
    rw [E.logPartition_eq_cgf]
    exact (analyticAt_cgf hmem).differentiableAt.hasDerivAt
  -- derivative of the density in the parameter
  have hden_deriv : ∀ x, HasDerivAt (fun t => E.toParametricFamily.density t x)
      (E.toParametricFamily.density η x * (E.stat x - deriv E.logPartition η)) η := by
    intro x
    have hfun : (fun t : ℝ => ⟪t, E.stat x⟫_ℝ) = fun t => t * E.stat x :=
      funext fun t => hinner t (E.stat x)
    have h1 : HasDerivAt (fun t : ℝ => ⟪t, E.stat x⟫_ℝ) (E.stat x) η := by
      rw [hfun]; simpa using (hasDerivAt_id η).mul_const (E.stat x)
    have hlin : HasDerivAt (fun t : ℝ => ⟪t, E.stat x⟫_ℝ - E.logPartition t)
        (E.stat x - deriv E.logPartition η) η := h1.sub hA
    exact hlin.exp
  -- the score equals the centered natural statistic `T − A'(η)`
  have hscore_id : ∀ x, score E.toParametricFamily η x = E.stat x - deriv E.logPartition η := by
    intro x
    have hpos : (0 : ℝ) < E.toParametricFamily.density η x := Real.exp_pos _
    rw [score, (hden_deriv x).deriv, mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]
  have hPeq : E.toParametricFamily.toMeasure E.base η = E.P η := by
    rw [E.P_eq_withDensity hηnat]; rfl
  rw [fisherInfo]
  calc ∫ x, score E.toParametricFamily η x ^ 2 * E.toParametricFamily.density η x ∂E.base
      = ∫ x, (E.stat x - deriv E.logPartition η) ^ 2 * E.toParametricFamily.density η x ∂E.base
        := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hscore_id]
    _ = ∫ x, (E.stat x - deriv E.logPartition η) ^ 2 ∂(E.toParametricFamily.toMeasure E.base η) :=
        (integral_toMeasure_eq E.toParametricFamily E.base η
          (fun x => (E.stat x - deriv E.logPartition η) ^ 2)).symm
    _ = ∫ x, (E.stat x - deriv E.logPartition η) ^ 2 ∂(E.P η) := by rw [hPeq]
    _ = variance E.stat (E.P η) := by
        rw [variance_eq_integral E.stat_meas.aemeasurable, E.integral_stat_P hη]
    _ = iteratedDeriv 2 E.logPartition η := E.variance_stat_P hη
    _ = deriv (deriv E.logPartition) η := by rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- The inner product of the `i`-th coordinate unit vector with `v` is the `i`-th coordinate. -/
private lemma inner_single_coord {s : ℕ} (i : Fin s) (v : EuclideanSpace ℝ (Fin s)) :
    ⟪EuclideanSpace.single i (1 : ℝ), v⟫_ℝ = v i := by
  have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) v
  simp only [map_one, one_mul] at h
  exact h

/-- Measurability of the (extended-real) density in the exact `exp`-form produced by
`P_eq_withDensity`, so that `withDensity` rewrites match syntactically. -/
private lemma measurable_density_exp {s : ℕ}
    (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) (η : EuclideanSpace ℝ (Fin s)) :
    Measurable (fun x => ENNReal.ofReal (Real.exp (⟪η, E.stat x⟫_ℝ - E.logPartition η))) :=
  (E.toParametricFamily.density_meas η).ennreal_ofReal

/-- Bridge `∫ g dP_η = ∫ g · p_η dν` for the multiparameter member, mirroring
`integral_toMeasure_eq` (which is phrased only for real parameters). -/
private lemma integral_P_eq {s : ℕ} (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    {η : EuclideanSpace ℝ (Fin s)} (hη : η ∈ E.natSet) (g : 𝓧 → ℝ) :
    ∫ x, g x ∂(E.P η) = ∫ x, g x * E.toParametricFamily.density η x ∂E.base := by
  rw [E.P_eq_withDensity hη,
    integral_withDensity_eq_integral_toReal_smul (measurable_density_exp E η)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only [ExpFamily.toParametricFamily]
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm]

/-- **Directional derivative of the log-partition function is the coordinate mean.** Along the
line `η + t·eᵢ` the log-partition function is `A(η) + cgf Tᵢ(P η)` on a neighborhood of `0`, so
its derivative at `0` is the mean `E_η[Tᵢ]` of the `i`-th coordinate statistic. -/
private lemma hasDerivAt_logPartition_dir {s : ℕ}
    (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) {η : EuclideanSpace ℝ (Fin s)}
    (hb : E.base ≠ 0) (hη : η ∈ interior E.natSet) (i : Fin s) :
    HasDerivAt (fun t : ℝ => E.logPartition (η + t • EuclideanSpace.single i 1))
      (∫ x, E.stat x i ∂(E.P η)) 0 := by
  haveI hPprob : IsProbabilityMeasure (E.P η) :=
    E.isProbabilityMeasure_P hb (interior_subset hη)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior η hη
  -- membership of the line in the natural parameter set, for small increments
  have hmemb : ∀ t : ℝ, t ∈ Set.Ioo (-r) r →
      η + t • EuclideanSpace.single i 1 ∈ E.natSet := by
    intro t ht
    apply interior_subset; apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hns : ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp
    rw [hns, mul_one, Real.norm_eq_abs]; exact abs_lt.mpr ⟨ht.1, ht.2⟩
  -- the coordinate statistic is integrable-exp near `0`, so `0` is an interior point
  have hint_line : ∀ t : ℝ, t ∈ Set.Ioo (-r) r →
      Integrable (fun x => Real.exp (t * E.stat x i)) (E.P η) := by
    intro t ht
    rw [E.P_eq_withDensity (interior_subset hη),
      integrable_withDensity_iff (measurable_density_exp E η)
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hb_int : Integrable
        (fun x => Real.exp ⟪η + t • EuclideanSpace.single i 1, E.stat x⟫_ℝ) E.base := hmemb t ht
    refine (hb_int.const_mul (Real.exp (- E.logPartition η))).congr
      (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [inner_add_left, real_inner_smul_left, inner_single_coord]
    ring
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x => E.stat x i) (E.P η)) := by
    have hIoo : Set.Ioo (-r) r ⊆ integrableExpSet (fun x => E.stat x i) (E.P η) :=
      fun t ht => hint_line t ht
    exact (isOpen_Ioo.subset_interior_iff.mpr hIoo) ⟨by linarith, hr⟩
  -- derivative of the cumulant generating function at `0` is the mean
  have hderiv_val : deriv (cgf (fun x => E.stat x i) (E.P η)) 0
      = ∫ x, E.stat x i ∂(E.P η) := by
    rw [deriv_cgf_zero h0, probReal_univ, div_one]
  have hcgf_HDA : HasDerivAt (cgf (fun x => E.stat x i) (E.P η))
      (∫ x, E.stat x i ∂(E.P η)) 0 := by
    rw [← hderiv_val]; exact (analyticAt_cgf h0).differentiableAt.hasDerivAt
  -- the log-partition line agrees with `cgf + A(η)` near `0`
  have hcgf_eq : (fun t : ℝ => E.logPartition (η + t • EuclideanSpace.single i 1))
      =ᶠ[nhds (0 : ℝ)] (fun t => cgf (fun x => E.stat x i) (E.P η) t + E.logPartition η) := by
    filter_upwards [Ioo_mem_nhds (show (-r : ℝ) < 0 by linarith) hr] with t ht
    have hmgf : mgf (fun x => E.stat x i) (E.P η) t
        = Real.exp (E.logPartition (η + t • EuclideanSpace.single i 1) - E.logPartition η) := by
      rw [mgf, ← E.integral_exp_inner_P hb (interior_subset hη) (hmemb t ht)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [real_inner_smul_left, inner_single_coord]
    have hcgf_t : cgf (fun x => E.stat x i) (E.P η) t
        = E.logPartition (η + t • EuclideanSpace.single i 1) - E.logPartition η := by
      rw [cgf, hmgf, Real.log_exp]
    rw [hcgf_t]; ring
  exact (hcgf_HDA.add_const (E.logPartition η)).congr_of_eventuallyEq hcgf_eq

/-- **The coordinate score of the canonical family is the centered natural statistic**:
`scoreVecᵢ(x) = Tᵢ(x) − ∂ᵢA(η)`, where `∂ᵢA(η)` is the derivative supplied as `m`. -/
private lemma scoreVec_expFamily_coord {s : ℕ}
    (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s))) (η : EuclideanSpace ℝ (Fin s))
    (i : Fin s) (m : ℝ)
    (hd : HasDerivAt (fun t : ℝ => E.logPartition (η + t • EuclideanSpace.single i 1)) m 0)
    (x : 𝓧) :
    scoreVec E.toParametricFamily η x i = E.stat x i - m := by
  have hinner : HasDerivAt
      (fun t : ℝ => ⟪η + t • EuclideanSpace.single i 1, E.stat x⟫_ℝ) (E.stat x i) 0 := by
    have hfun : (fun t : ℝ => ⟪η + t • EuclideanSpace.single i 1, E.stat x⟫_ℝ)
        = fun t => ⟪η, E.stat x⟫_ℝ + E.stat x i * t := by
      funext t
      rw [inner_add_left, real_inner_smul_left, inner_single_coord]
      ring
    rw [hfun]
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (E.stat x i)).const_add ⟪η, E.stat x⟫_ℝ)
  have hexpo : HasDerivAt
      (fun t : ℝ => ⟪η + t • EuclideanSpace.single i 1, E.stat x⟫_ℝ
          - E.logPartition (η + t • EuclideanSpace.single i 1)) (E.stat x i - m) 0 :=
    hinner.sub hd
  have hdens : HasDerivAt
      (fun t : ℝ => E.toParametricFamily.density (η + t • EuclideanSpace.single i 1) x)
      (E.toParametricFamily.density η x * (E.stat x i - m)) 0 := by
    have h := hexpo.exp
    simp only [zero_smul, add_zero] at h
    exact h
  have hpos : (0 : ℝ) < E.toParametricFamily.density η x := Real.exp_pos _
  change deriv (fun t : ℝ => E.toParametricFamily.density (η + t • EuclideanSpace.single i 1) x) 0
      / E.toParametricFamily.density η x = E.stat x i - m
  rw [hdens.deriv, mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]

/-- **The information matrix of a canonical exponential family is the covariance matrix of
its natural statistic**: `I(η)_{ij} = cov_η(T_i, T_j)`, equivalently the Hessian of the
log-partition function.

In the mean-value parametrization the information matrix is the *inverse* of this
covariance matrix, by the matrix reparametrization rule. -/
theorem infoMatrix_expFamily {s : ℕ} (E : ExpFamily 𝓧 (EuclideanSpace ℝ (Fin s)))
    (η : EuclideanSpace ℝ (Fin s))
    -- USER-INPUT: the natural parameter lies in the interior of the natural parameter set
    (hη : η ∈ interior E.natSet) (i j : Fin s) :
    infoMatrix E.toParametricFamily E.base η i j
      = covariance (fun x => E.stat x i) (fun x => E.stat x j) (E.P η) := by
  rcases eq_or_ne E.base 0 with hb | hb
  · -- degenerate reference measure: both sides vanish
    have hP0 : E.P η = 0 := by
      rw [show E.P η = E.base.tilted (fun x => ⟪η, E.stat x⟫_ℝ) from rfl, hb, tilted_zero_measure]
    simp only [infoMatrix, hb, integral_zero_measure, hP0, covariance_zero_measure]
  · -- coordinate scores are centered statistics; the entry is their covariance
    have hscore_i := scoreVec_expFamily_coord E η i _ (hasDerivAt_logPartition_dir E hb hη i)
    have hscore_j := scoreVec_expFamily_coord E η j _ (hasDerivAt_logPartition_dir E hb hη j)
    simp only [infoMatrix]
    have hcong : (fun x => scoreVec E.toParametricFamily η x i
          * scoreVec E.toParametricFamily η x j * E.toParametricFamily.density η x)
        = fun x => ((E.stat x i - ∫ y, E.stat y i ∂(E.P η))
            * (E.stat x j - ∫ y, E.stat y j ∂(E.P η))) * E.toParametricFamily.density η x := by
      funext x; rw [hscore_i x, hscore_j x]
    rw [hcong, ← integral_P_eq E (interior_subset hη)
      (fun x => (E.stat x i - ∫ y, E.stat y i ∂(E.P η))
        * (E.stat x j - ∫ y, E.stat y j ∂(E.P η)))]
    simp only [covariance]

end StatLean.PointEstimation
