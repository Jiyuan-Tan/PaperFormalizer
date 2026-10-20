module
public import StatLean.PointEstimation.LinearModel.Defs
public import StatLean.PointEstimation.UMVU.Defs
public import StatLean.PointEstimation.UMVU.CovarianceCriterion
public import StatLean.PointEstimation.UMVU.RaoBlackwell
public import StatLean.PointEstimation.Completeness.Defs
public import StatLean.PointEstimation.Completeness.ExpFamily
public import StatLean.PointEstimation.ExponentialFamily.Basic
public import StatLean.PointEstimation.Sufficiency.Defs
public import StatLean.PointEstimation.Sufficiency.Factorization
public import StatLean.PointEstimation.Sufficiency.RegularConditional
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

@[expose] public section

/-!
# The canonical normal linear model

An orthogonal change of basis carries the normal linear model with an `s`-dimensional mean
subspace to its **canonical form**: the first `s` coordinates are independent `N(ηᵢ, σ²)`
with `η` ranging freely over `ℝˢ`, and the remaining `m` coordinates are independent
`N(0, σ²)`. All optimality statements for the model are proved in this coordinate system
and transported back afterwards.

* `PosVar` — the strictly positive variances (the nuisance-parameter range);
* `CanonicalParam s` — the parameter `(η, σ²)` of the canonical model;
* `canonicalMean η` — the mean vector `(η₁, …, η_s, 0, …, 0)`;
* `canonicalModel p` — the canonical family on `EuclideanSpace ℝ (Fin (s + m))`;
* `canonicalHead y` — the first `s` coordinates `(Y₁, …, Y_s)`;
* `canonicalRSS y` — the residual sum of squares `S² = ∑_{j} Y_{s+j}²`;
* `canonicalStat y = (canonicalHead y, canonicalRSS y)` — the complete sufficient statistic;
* `canonicalStat_hasSufficientKernel`, `canonicalStat_isCompleteStat`,
  `canonical_complete_sufficient`;
* `isUMVU_coord`, `isUMVU_linear_combination`, `isUMVU_residual_variance` — the unbiased
  optimality statements: `Yᵢ` for `ηᵢ`, `∑ λᵢ Yᵢ` for `∑ λᵢ ηᵢ`, and `S²/m` for `σ²`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.4 (Normal
Linear Models), Theorem 4.3 (in the canonical model each `Yᵢ` is UMVU and MRE for `ηᵢ`, and
`c·Sʳ` for `σʳ`) and Theorem 4.4 (the UMVU estimators of `Σγᵢηᵢ` and `σ²`). (`TPE2 §3.4 Thm
4.3, Thm 4.4`.)

**Proof formalization notes.**
* *Parameter packaging.* The mean is indexed by a free `η : Fin s → ℝ` together with a
  positive variance, and embedded into the observation space by `canonicalMean`; the
  alternative — a subtype `{x : Fin n → ℝ // ∀ j ≥ s, x j = 0}` — was rejected because
  every statement would then carry subtype coercions, and because the completeness proof
  needs the parameter to range over a set with nonempty interior in `ℝˢ⁺¹`, which the free
  product `(Fin s → ℝ) × PosVar` exhibits directly.
* *Dimension packaging.* The observation dimension is written `n = s + m` rather than
  `s ≤ n`, so that "the first `s` coordinates" and "the last `m` coordinates" are
  `Fin.castAdd`/`Fin.natAdd` with no arithmetic side conditions. The standing assumption
  `s < n` of the model becomes `0 < m`, carried explicitly by every theorem below.
* *Variance range.* `σ² = 0` is excluded (`PosVar`): the degenerate member falls outside
  the classical statements and would break completeness bookkeeping.
* Completeness is intended to go through the full-rank exponential-family theorem, with
  natural statistic `canonicalStat` and natural parameter `(η/σ², −1/(2σ²))`, whose range
  has nonempty interior in `ℝˢ × ℝ`; the sufficiency kernel is the Gaussian conditional
  law of the observation given the statistic.

**Bibliographic comments.** The reduction of the normal linear model to canonical form by
an orthogonal transformation, and the resulting optimality of least squares, go back to
C. F. Gauss (*Theoria combinationis observationum erroribus minimis obnoxiae*, 1821/1823)
and A. A. Markov (*Wahrscheinlichkeitsrechnung*, Teubner, 1912); the modern
coordinate-free treatment is that of W. Kruskal ("When are Gauss–Markov and least squares
estimators identical?" in *Essays in Probability and Statistics*, 1965), H. Scheffé (*The
Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear Statistical Inference and Its
Applications*, 2nd ed., Wiley, 1973). Completeness of the canonical statistic and the
resulting minimum-variance property are due to E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950),
305–340).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

/-- The strictly positive variances: the range of the nuisance parameter `σ²` in every
normal linear model considered here (a vanishing variance degenerates the observation and
is excluded from the classical statements). -/
abbrev PosVar : Type := {v : ℝ≥0 // 0 < v}

/-- The parameter of the canonical model: `s` unrestricted mean coordinates together with
the unknown positive common variance. -/
abbrev CanonicalParam (s : ℕ) : Type := (Fin s → ℝ) × PosVar

variable {s m : ℕ}

/-! ## The model -/

/-- The **canonical mean vector** `(η₁, …, η_s, 0, …, 0)`: the free means occupy the first
`s` coordinates and the remaining `m` coordinates are centred. -/
noncomputable def canonicalMean (η : Fin s → ℝ) : EuclideanSpace ℝ (Fin (s + m)) :=
  (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
    (Fin.append η (0 : Fin m → ℝ))

/-- The **canonical normal linear model**: independent coordinates, the first `s` with free
means `η` and the last `m` centred, all with common variance `σ²`. -/
noncomputable def canonicalModel (p : CanonicalParam s) :
    Measure (EuclideanSpace ℝ (Fin (s + m))) :=
  gaussianVector (canonicalMean (m := m) p.1) p.2.1

/-! ## The canonical statistic -/

/-- The **signal block** `(Y₁, …, Y_s)`: the first `s` coordinates of the observation. -/
def canonicalHead (y : EuclideanSpace ℝ (Fin (s + m))) : Fin s → ℝ :=
  fun i => y (Fin.castAdd m i)

/-- The **residual sum of squares** `S² = ∑_{j=1}^{m} Y_{s+j}²` of the canonical model. -/
def canonicalRSS (y : EuclideanSpace ℝ (Fin (s + m))) : ℝ :=
  ∑ j : Fin m, y (Fin.natAdd s j) ^ 2

/-- The **canonical statistic** `(Y₁, …, Y_s, S²)`, jointly complete and sufficient for
`(η, σ²)`. -/
def canonicalStat (y : EuclideanSpace ℝ (Fin (s + m))) : (Fin s → ℝ) × ℝ :=
  (canonicalHead y, canonicalRSS y)

/-- Measurability of the canonical statistic (needed by every consumer that pushes the
model forward along it). -/
theorem measurable_canonicalStat :
    Measurable (canonicalStat (s := s) (m := m)) := by
  have hcoord : ∀ k : Fin (s + m),
      Measurable (fun y : EuclideanSpace ℝ (Fin (s + m)) => y k) :=
    fun k => (measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 (Fin (s + m) → ℝ))
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ (fun i => hcoord (Fin.castAdd m i))
  · exact Finset.measurable_sum _ (fun j _ => (hcoord (Fin.natAdd s j)).pow_const 2)

/-- **Product-Gaussian density.** The canonical normal law is the Lebesgue measure on
`Fin n → ℝ` weighted by the product of the per-coordinate Gaussian densities. -/
private lemma canonicalNormal_eq_withDensity {n : ℕ} (η : Fin n → ℝ) {σ2 : ℝ≥0}
    (hσ : σ2 ≠ 0) :
    canonicalNormal η σ2
      = (volume : Measure (Fin n → ℝ)).withDensity
          (fun x => ∏ i, gaussianPDF (η i) σ2 (x i)) := by
  have h_each : (fun i => gaussianReal (η i) σ2)
      = fun i => (volume : Measure ℝ).withDensity (gaussianPDF (η i) σ2) := by
    funext i; exact gaussianReal_of_var_ne_zero (η i) hσ
  haveI : ∀ i : Fin n, SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF (η i) σ2)) := by
    intro i; rw [← gaussianReal_of_var_ne_zero (η i) hσ]; infer_instance
  rw [canonicalNormal, h_each, ← pi_withDensity_prod (fun i => measurable_gaussianPDF (η i) σ2),
    ← volume_pi]

/-! ## Exponential-family scaffolding (private)

The completeness proof recognizes the canonical model as a full-rank exponential family with
**total** sum of squares as the last natural coordinate (the residual form is *not* an
exponential family: a `−(1/2σ²)∑_{i<s} yᵢ²` term survives), and transports completeness of
that statistic to the frozen `canonicalStat = (head, RSS)` along the measurable shear
`(a, total) ↦ (a, total − ∑ aᵢ²)`. -/

/-- The exponential family underlying the canonical model, on the pi observation space
`Fin (s+m) → ℝ` with reference measure `volume`. Its natural statistic is
`ỹ ↦ (y₀,…,y_{s−1}, ∑ₖ yₖ²)` (head coordinates and the **total** sum of squares). -/
private noncomputable def canonicalExpFamily (s m : ℕ) :
    ExpFamily (Fin (s + m) → ℝ) (EuclideanSpace ℝ (Fin (s + 1))) where
  base := volume
  stat := fun y =>
    (WithLp.toLp 2 : (Fin (s + 1) → ℝ) → EuclideanSpace ℝ (Fin (s + 1)))
      (Fin.snoc (fun i : Fin s => y (Fin.castAdd m i)) (∑ k, y k ^ 2))
  stat_meas := by
    apply (WithLp.measurable_toLp 2 (Fin (s + 1) → ℝ)).comp
    refine measurable_pi_iff.2 fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]
      exact Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).pow_const 2
    · simp only [Fin.snoc_castSucc]
      exact measurable_pi_apply _

private lemma canonicalExpFamily_stat (y : Fin (s + m) → ℝ) :
    (canonicalExpFamily s m).stat y
      = (WithLp.toLp 2 : (Fin (s + 1) → ℝ) → EuclideanSpace ℝ (Fin (s + 1)))
          (Fin.snoc (fun i : Fin s => y (Fin.castAdd m i)) (∑ k, y k ^ 2)) := rfl

private lemma canonicalExpFamily_base : (canonicalExpFamily s m).base = volume := rfl

/-- The natural parameter attached to `(η, σ²)`: `(η₁/σ², …, η_s/σ², −1/(2σ²))`. -/
private noncomputable def canonicalEta (p : CanonicalParam s) :
    EuclideanSpace ℝ (Fin (s + 1)) :=
  (WithLp.toLp 2 : (Fin (s + 1) → ℝ) → EuclideanSpace ℝ (Fin (s + 1)))
    (Fin.snoc (fun i : Fin s => p.1 i / (p.2.1 : ℝ)) (-(1 / (2 * (p.2.1 : ℝ)))))

/-- The normalizing constant of the tilted density (positive). -/
private noncomputable def canonicalC (p : CanonicalParam s) : ℝ :=
  (Real.sqrt (2 * Real.pi * (p.2.1 : ℝ)))⁻¹ ^ (s + m)
    * Real.exp (-(∑ i, p.1 i ^ 2) / (2 * (p.2.1 : ℝ)))

private lemma canonicalC_pos (p : CanonicalParam s) : 0 < canonicalC (m := m) p := by
  have hv : (0 : ℝ) < (p.2.1 : ℝ) := by exact_mod_cast p.2.2
  have h2πv : (0 : ℝ) < 2 * Real.pi * (p.2.1 : ℝ) :=
    mul_pos (mul_pos two_pos Real.pi_pos) hv
  exact mul_pos (pow_pos (inv_pos.2 (Real.sqrt_pos.2 h2πv)) _) (Real.exp_pos _)

/-- The real inner product of two scalars is their product. -/
private lemma real_inner_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  have h1 : ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_mul_norm]; simp
  calc ⟪a, b⟫_ℝ = ⟪a • (1 : ℝ), b • (1 : ℝ)⟫_ℝ := by
        rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one]
    _ = a * (b * ⟪(1 : ℝ), (1 : ℝ)⟫_ℝ) := by rw [real_inner_smul_left, real_inner_smul_right]
    _ = a * b := by rw [h1, mul_one]

/-- The inner product `⟪canonicalEta p, T̃ y⟫` in explicit coordinate form. -/
private lemma canonicalEta_inner (p : CanonicalParam s) (y : Fin (s + m) → ℝ) :
    ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ
      = (∑ i, p.1 i / (p.2.1 : ℝ) * y (Fin.castAdd m i))
        + -(1 / (2 * (p.2.1 : ℝ))) * (∑ k, y k ^ 2) := by
  rw [canonicalEta, canonicalExpFamily_stat, PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp only [real_inner_mul, Fin.snoc_castSucc, Fin.snoc_last]

/-- **Core density identity.** The product of per-coordinate Gaussian densities of the
canonical model equals `C·exp⟪η, T̃⟫` — the exponential-family form. -/
private lemma canonical_pdf_prod_eq (p : CanonicalParam s) (y : Fin (s + m) → ℝ) :
    (∏ k, gaussianPDFReal ((Fin.append p.1 (0 : Fin m → ℝ)) k) p.2.1 (y k))
      = canonicalC (m := m) p
          * Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ := by
  have hv : (0 : ℝ) < (p.2.1 : ℝ) := by exact_mod_cast p.2.2
  have hvne : (p.2.1 : ℝ) ≠ 0 := ne_of_gt hv
  set mean : Fin (s + m) → ℝ := Fin.append p.1 (0 : Fin m → ℝ) with hmean
  -- Expand the product into constant × exp of a sum.
  have hprod :
      (∏ k, gaussianPDFReal (mean k) p.2.1 (y k))
        = (Real.sqrt (2 * Real.pi * (p.2.1 : ℝ)))⁻¹ ^ (s + m)
            * Real.exp (∑ k, -(y k - mean k) ^ 2 / (2 * (p.2.1 : ℝ))) := by
    simp only [gaussianPDFReal_def]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum]
  rw [hprod, canonicalC,
    mul_assoc ((Real.sqrt (2 * Real.pi * (p.2.1 : ℝ)))⁻¹ ^ (s + m)), ← Real.exp_add]
  congr 1
  congr 1
  -- The exponent identity `∑ -(yₖ-meanₖ)²/(2v) = -(∑ηᵢ²)/(2v) + ⟪η, T̃⟫`.
  rw [canonicalEta_inner]
  have hmul : ∑ k, y k * mean k = ∑ i, y (Fin.castAdd m i) * p.1 i := by
    rw [Fin.sum_univ_add]
    simp only [hmean, Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
  have hsq : ∑ k, mean k ^ 2 = ∑ i, p.1 i ^ 2 := by
    rw [Fin.sum_univ_add]
    simp only [hmean, Fin.append_left, Fin.append_right, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, add_zero]
  have hnum : ∑ k, -(y k - mean k) ^ 2 / (2 * (p.2.1 : ℝ))
      = (-(∑ k, y k ^ 2) + 2 * (∑ k, y k * mean k) - (∑ k, mean k ^ 2)) / (2 * (p.2.1 : ℝ)) := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_congr rfl (fun k _ => show -(y k - mean k) ^ 2
          = -(y k ^ 2) + 2 * (y k * mean k) - mean k ^ 2 from by ring),
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hR : (∑ i, p.1 i / (p.2.1 : ℝ) * y (Fin.castAdd m i))
      = (∑ i, y (Fin.castAdd m i) * p.1 i) / (p.2.1 : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hnum, hmul, hsq, hR]
  field_simp
  ring

/-- Measurability of the exponential integrand `y ↦ exp⟪η, T̃ y⟫`. -/
private lemma measurable_expInner (p : CanonicalParam s) :
    Measurable
      (fun y : Fin (s + m) → ℝ => Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ) :=
  (((continuous_const.inner continuous_id).measurable).comp
    (canonicalExpFamily s m).stat_meas).exp

/-- The ENNReal density of the canonical model in exponential-family form. -/
private lemma canonical_density_eq (p : CanonicalParam s) (y : Fin (s + m) → ℝ) :
    (∏ i, gaussianPDF ((Fin.append p.1 (0 : Fin m → ℝ)) i) p.2.1 (y i))
      = ENNReal.ofReal (canonicalC (m := m) p)
          * ENNReal.ofReal (Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
    canonical_pdf_prod_eq, ENNReal.ofReal_mul (canonicalC_pos p).le]

/-- **The exponential-family bridge.** The canonical product-Gaussian law with mean
`(η, 0)` equals the exponential-family member `P (canonicalEta p)`. -/
private lemma canonicalNormal_eq_P (p : CanonicalParam s) :
    canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1
      = (canonicalExpFamily s m).P (canonicalEta p) := by
  set φ : (Fin (s + m) → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ) with hφ
  set A : ℝ := (canonicalExpFamily s m).logPartition (canonicalEta p) with hA
  have hφmeas : Measurable φ := (measurable_expInner p).ennreal_ofReal
  have hσ : p.2.1 ≠ 0 := ne_of_gt p.2.2
  -- The canonical law as a weighted volume.
  have hcanon : canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1
      = volume.withDensity (fun y => ENNReal.ofReal (canonicalC (m := m) p) * φ y) := by
    rw [canonicalNormal_eq_withDensity _ hσ]
    exact withDensity_congr_ae (Filter.Eventually.of_forall fun y => canonical_density_eq p y)
  haveI : IsProbabilityMeasure (canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1) := by
    unfold canonicalNormal; infer_instance
  have hbne : (volume : Measure (Fin (s + m) → ℝ)) ≠ 0 := by
    intro h
    have h0 : canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1 = 0 := by
      rw [hcanon, h, withDensity_zero_left]
    have := measure_univ (μ := canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1)
    rw [h0] at this; simp at this
  set Z : ℝ≥0∞ := ∫⁻ y, φ y ∂(volume : Measure (Fin (s + m) → ℝ)) with hZ
  -- Total mass of the canonical law gives `ofReal C · Z = 1`.
  have hmassC : ENNReal.ofReal (canonicalC (m := m) p) * Z = 1 := by
    have := measure_univ (μ := canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1)
    rw [hcanon, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_const_mul _ hφmeas] at this
    exact this
  have hZne : Z ≠ 0 := by
    rintro h; rw [h, mul_zero] at hmassC; exact one_ne_zero hmassC.symm
  have hZlt : Z ≠ ∞ := by
    rintro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (canonicalC_pos (m := m) p)).ne'] at hmassC
    exact ENNReal.top_ne_one hmassC
  -- Hence `canonicalEta p` is a natural parameter (Gaussian integrability).
  have hmem : canonicalEta p ∈ (canonicalExpFamily s m).natSet := by
    show Integrable
      (fun y => Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ)
      (canonicalExpFamily s m).base
    rw [canonicalExpFamily_base]
    refine ⟨(measurable_expInner p).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
    exact lt_of_le_of_ne le_top hZlt
  haveI : IsProbabilityMeasure ((canonicalExpFamily s m).P (canonicalEta p)) :=
    ExpFamily.isProbabilityMeasure_P _ (by rw [canonicalExpFamily_base]; exact hbne) hmem
  -- The member in density form.
  have hP : (canonicalExpFamily s m).P (canonicalEta p)
      = volume.withDensity (fun y => ENNReal.ofReal (Real.exp (-A)) * φ y) := by
    rw [ExpFamily.P_eq_withDensity _ hmem, canonicalExpFamily_base]
    refine withDensity_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hφ, ← hA]
    rw [show ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ - A
          = -A + ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ from by ring,
      Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hmassP : ENNReal.ofReal (Real.exp (-A)) * Z = 1 := by
    have := measure_univ (μ := (canonicalExpFamily s m).P (canonicalEta p))
    rw [hP, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_const_mul _ hφmeas] at this
    exact this
  have hconst : ENNReal.ofReal (canonicalC (m := m) p) = ENNReal.ofReal (Real.exp (-A)) :=
    (ENNReal.mul_left_inj hZne hZlt).1 (hmassC.trans hmassP.symm)
  rw [hcanon, hP, hconst]

/-- `canonicalEta p` is a natural parameter of the exponential family (Gaussian
integrability). -/
private lemma canonicalEta_mem_natSet (p : CanonicalParam s) :
    canonicalEta p ∈ (canonicalExpFamily s m).natSet := by
  set φ : (Fin (s + m) → ℝ) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ) with hφ
  have hφmeas : Measurable φ := (measurable_expInner p).ennreal_ofReal
  have hσ : p.2.1 ≠ 0 := ne_of_gt p.2.2
  have hcanon : canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1
      = volume.withDensity (fun y => ENNReal.ofReal (canonicalC (m := m) p) * φ y) := by
    rw [canonicalNormal_eq_withDensity _ hσ]
    exact withDensity_congr_ae (Filter.Eventually.of_forall fun y => canonical_density_eq p y)
  haveI : IsProbabilityMeasure (canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1) := by
    unfold canonicalNormal; infer_instance
  have hmassC : ENNReal.ofReal (canonicalC (m := m) p)
      * ∫⁻ y, φ y ∂(volume : Measure (Fin (s + m) → ℝ)) = 1 := by
    have := measure_univ (μ := canonicalNormal (Fin.append p.1 (0 : Fin m → ℝ)) p.2.1)
    rw [hcanon, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      lintegral_const_mul _ hφmeas] at this
    exact this
  have hZlt : (∫⁻ y, φ y ∂(volume : Measure (Fin (s + m) → ℝ))) ≠ ∞ := by
    rintro h
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (canonicalC_pos (m := m) p)).ne'] at hmassC
    exact ENNReal.top_ne_one hmassC
  show Integrable
    (fun y => Real.exp ⟪canonicalEta p, (canonicalExpFamily s m).stat y⟫_ℝ)
    (canonicalExpFamily s m).base
  rw [canonicalExpFamily_base]
  refine ⟨(measurable_expInner p).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le)]
  exact lt_of_le_of_ne le_top hZlt

/-- The **measurable shear** carrying the total-sum-of-squares statistic `(a, total)` to the
frozen residual statistic `(a, total − ∑ aᵢ²)`. -/
private def canonicalShear (v : EuclideanSpace ℝ (Fin (s + 1))) : (Fin s → ℝ) × ℝ :=
  (fun i => v (Fin.castSucc i), v (Fin.last s) - ∑ i, v (Fin.castSucc i) ^ 2)

private lemma measurable_canonicalShear : Measurable (canonicalShear (s := s)) := by
  have hcoord : ∀ k : Fin (s + 1),
      Measurable (fun v : EuclideanSpace ℝ (Fin (s + 1)) => v k) :=
    fun k => (measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 (Fin (s + 1) → ℝ))
  refine Measurable.prodMk (measurable_pi_lambda _ fun i => hcoord (Fin.castSucc i)) ?_
  exact (hcoord (Fin.last s)).sub
    (Finset.measurable_sum _ fun i _ => (hcoord (Fin.castSucc i)).pow_const 2)

/-- `canonicalStat ∘ toLp = canonicalShear ∘ T̃`: the frozen statistic is the shear of the
exponential-family statistic. -/
private lemma canonicalStat_toLp_eq_shear (y : Fin (s + m) → ℝ) :
    canonicalStat ((WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m))) y)
      = canonicalShear ((canonicalExpFamily s m).stat y) := by
  refine Prod.ext ?_ ?_
  · funext i
    simp only [canonicalStat, canonicalHead, canonicalShear, canonicalExpFamily_stat,
      PiLp.toLp_apply, Fin.snoc_castSucc]
  · simp only [canonicalStat, canonicalRSS, canonicalShear, canonicalExpFamily_stat,
      PiLp.toLp_apply, Fin.snoc_castSucc, Fin.snoc_last]
    rw [Fin.sum_univ_add]; ring

/-- **Completeness transfers** along a measurable reparametrization of the sample and a
surjective reindexing of the parameter. -/
private lemma isCompleteFamily_map_comp {α β : Type*} {V' W' : Type*}
    [MeasurableSpace V'] [MeasurableSpace W']
    {Q : α → Measure V'} (hQ : IsCompleteFamily Q)
    {ρ : β → α} (hρ : Function.Surjective ρ)
    {ψ : V' → W'} (hψ : Measurable ψ) :
    IsCompleteFamily (fun b => (Q (ρ b)).map ψ) := by
  intro f hf hint hmean
  have hInt : ∀ a, Integrable (fun v => f (ψ v)) (Q a) := by
    intro a; obtain ⟨b, rfl⟩ := hρ a
    exact (integrable_map_measure hf.aestronglyMeasurable hψ.aemeasurable).1 (hint b)
  have hMean : ∀ a, ∫ v, f (ψ v) ∂(Q a) = 0 := by
    intro a; obtain ⟨b, rfl⟩ := hρ a
    rw [← integral_map hψ.aemeasurable hf.aestronglyMeasurable]; exact hmean b
  have hkey := hQ (fun v => f (ψ v)) (hf.comp hψ) hInt hMean
  intro b
  exact (ae_map_iff (μ := Q (ρ b)) hψ.aemeasurable
    (p := fun w => f w = (0 : W' → ℝ) w) (hf (measurableSet_singleton 0))).2 (hkey (ρ b))

/-- The range of `canonicalEta` (the open half-space `{w : w_last < 0}`) has nonempty
interior. -/
private lemma interior_range_canonicalEta_nonempty :
    (interior (Set.range (canonicalEta (s := s)))).Nonempty := by
  set S : Set (EuclideanSpace ℝ (Fin (s + 1))) := {w | w (Fin.last s) < 0} with hSdef
  have hcont : Continuous (fun w : EuclideanSpace ℝ (Fin (s + 1)) => w (Fin.last s)) :=
    (continuous_apply (Fin.last s)).comp (PiLp.continuous_ofLp 2 (fun _ : Fin (s + 1) => ℝ))
  have hSopen : IsOpen S := isOpen_lt hcont continuous_const
  have hSsub : S ⊆ Set.range (canonicalEta (s := s)) := by
    intro w hw
    have hw0 : w (Fin.last s) < 0 := hw
    have hwne : w (Fin.last s) ≠ 0 := ne_of_lt hw0
    set vr : ℝ := -1 / (2 * w (Fin.last s)) with hvrdef
    have h2w : 2 * w (Fin.last s) < 0 := by linarith
    have hvr : 0 < vr := div_pos_of_neg_of_neg (by norm_num) h2w
    have hcoe : (Real.toNNReal vr : ℝ) = vr := Real.coe_toNNReal vr hvr.le
    have hlast : -(1 / (2 * vr)) = w (Fin.last s) := by rw [hvrdef]; field_simp
    refine ⟨(fun i => w (Fin.castSucc i) * vr, ⟨vr.toNNReal, Real.toNNReal_pos.2 hvr⟩), ?_⟩
    rw [canonicalEta]
    simp only [hcoe]
    have hfun : (fun i => w (Fin.castSucc i) * vr / vr) = fun i => w (Fin.castSucc i) := by
      funext i; rw [mul_div_assoc, div_self (ne_of_gt hvr), mul_one]
    rw [hfun, hlast]
    have hsnoc : Fin.snoc (fun i => w (Fin.castSucc i)) (w (Fin.last s)) = WithLp.ofLp w :=
      Fin.snoc_init_self (WithLp.ofLp w)
    rw [hsnoc, WithLp.toLp_ofLp]
  have hSne : S.Nonempty :=
    ⟨canonicalEta (s := s) (fun _ => 0, ⟨1, one_pos⟩), by
      show canonicalEta (fun _ => 0, ⟨1, one_pos⟩) (Fin.last s) < 0
      rw [canonicalEta]
      simp only [PiLp.toLp_apply, Fin.snoc_last, NNReal.coe_one]
      norm_num⟩
  have hsub : S ⊆ interior (Set.range (canonicalEta (s := s))) := by
    rw [← hSopen.interior_eq]; exact interior_mono hSsub
  exact hSne.mono hsub

/-! ## Sufficiency-kernel scaffolding (private)

The canonical model is dominated by `volume` on the observation space, with the
product-Gaussian density `canonicalDensity`, which factors through `canonicalStat` as
`canonicalFactor (canonicalStat y) · 1` — the Fisher–Neyman form. -/

/-- The product-Gaussian density of the canonical model on the observation space
`EuclideanSpace ℝ (Fin (s + m))` (with respect to `volume`). -/
private noncomputable def canonicalDensity (θ : CanonicalParam s) :
    EuclideanSpace ℝ (Fin (s + m)) → ℝ≥0∞ :=
  fun Y => ∏ i, gaussianPDF ((Fin.append θ.1 (0 : Fin m → ℝ)) i) θ.2.1 (Y i)

/-- The `T`-side Fisher–Neyman factor: `canonicalDensity θ y = canonicalFactor θ (canonicalStat y)`. -/
private noncomputable def canonicalFactor (θ : CanonicalParam s) :
    (Fin s → ℝ) × ℝ → ℝ≥0∞ :=
  fun t => ENNReal.ofReal (canonicalC (m := m) θ) *
    ENNReal.ofReal (Real.exp ((∑ i, θ.1 i / (θ.2.1 : ℝ) * t.1 i)
      + -(1 / (2 * (θ.2.1 : ℝ))) * (t.2 + ∑ i, t.1 i ^ 2)))

private lemma measurable_canonicalDensity (θ : CanonicalParam s) :
    Measurable (canonicalDensity (m := m) θ) := by
  unfold canonicalDensity
  refine Finset.measurable_prod _ fun i _ => ?_
  exact (measurable_gaussianPDF _ _).comp
    ((measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin (s + m) → ℝ)))

private lemma measurable_canonicalFactor (θ : CanonicalParam s) :
    Measurable (canonicalFactor (m := m) θ) := by
  unfold canonicalFactor
  refine measurable_const.mul (Measurable.ennreal_ofReal (Real.measurable_exp.comp ?_))
  refine (Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
    (measurable_const.mul (measurable_snd.add
      (Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_fst).pow_const 2)))

/-- The canonical model is a probability measure. -/
private instance isProbabilityMeasure_canonicalModel (θ : CanonicalParam s) :
    IsProbabilityMeasure (canonicalModel (m := m) θ) := by
  have hmap : canonicalModel (m := m) θ
      = (canonicalNormal (Fin.append θ.1 (0 : Fin m → ℝ)) θ.2.1).map
          (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m))) := by
    rw [canonicalModel, gaussianVector,
      show (fun i => (canonicalMean θ.1) i) = Fin.append θ.1 (0 : Fin m → ℝ) from rfl]
  rw [hmap]
  haveI : IsProbabilityMeasure (canonicalNormal (Fin.append θ.1 (0 : Fin m → ℝ)) θ.2.1) := by
    unfold canonicalNormal; infer_instance
  exact Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 _).aemeasurable

/-- **Domination density.** The canonical model is `volume` on the observation space weighted
by `canonicalDensity`. -/
private lemma canonicalModel_eq_withDensity (θ : CanonicalParam s) :
    canonicalModel (m := m) θ = (volume).withDensity (canonicalDensity (m := m) θ) := by
  have hσ : θ.2.1 ≠ 0 := ne_of_gt θ.2.2
  have hcomp : (canonicalDensity (m := m) θ) ∘
      (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m)))
      = fun x => ∏ i, gaussianPDF ((Fin.append θ.1 (0 : Fin m → ℝ)) i) θ.2.1 (x i) := by
    funext x; simp only [canonicalDensity, Function.comp, PiLp.toLp_apply]
  rw [canonicalModel, gaussianVector,
      show (fun i => (canonicalMean θ.1) i) = Fin.append θ.1 (0 : Fin m → ℝ) from rfl,
      canonicalNormal_eq_withDensity _ hσ, ← hcomp,
      ← AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity volume _
        (WithLp.measurable_toLp 2 (Fin (s + m) → ℝ)) _ (measurable_canonicalDensity θ),
      (PiLp.volume_preserving_toLp (Fin (s + m))).map_eq]

/-! ## Completeness and sufficiency -/

/-- **Sufficiency of the canonical statistic**: the conditional law of the observation
given `(Y₁, …, Y_s, S²)` does not depend on `(η, σ²)`. -/
theorem canonicalStat_hasSufficientKernel
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    HasSufficientKernel (canonicalModel (s := s) (m := m)) canonicalStat := by
  have hP : ∀ θ : CanonicalParam s,
      canonicalModel (m := m) θ = (volume).withDensity (canonicalDensity (m := m) θ) :=
    canonicalModel_eq_withDensity
  have hfac : IsFactorizedDensity (canonicalDensity (s := s) (m := m)) volume canonicalStat
      (canonicalFactor (s := s) (m := m)) (fun _ => 1) := by
    intro θ
    refine Filter.Eventually.of_forall fun Y => ?_
    show canonicalDensity θ Y = canonicalFactor θ (canonicalStat Y) * 1
    rw [mul_one]
    have hd : canonicalDensity θ Y
        = ENNReal.ofReal (canonicalC (m := m) θ) *
          ENNReal.ofReal (Real.exp
            ⟪canonicalEta θ, (canonicalExpFamily s m).stat (fun k => Y k)⟫_ℝ) := by
      simpa only [canonicalDensity] using canonical_density_eq θ (fun k => Y k)
    have hexp : ⟪canonicalEta θ, (canonicalExpFamily s m).stat (fun k => Y k)⟫_ℝ
        = (∑ i, θ.1 i / (θ.2.1 : ℝ) * (canonicalStat Y).1 i)
          + -(1 / (2 * (θ.2.1 : ℝ))) *
              ((canonicalStat Y).2 + ∑ i, (canonicalStat Y).1 i ^ 2) := by
      rw [canonicalEta_inner]
      simp only [canonicalStat, canonicalHead, canonicalRSS]
      rw [Fin.sum_univ_add]
      ring
    rw [hd, canonicalFactor, hexp]
  have hdom : ∀ θ : CanonicalParam s, canonicalModel (m := m) θ ≪ volume := by
    intro θ; rw [hP θ]; exact withDensity_absolutelyContinuous _ _
  have hsuf : IsSufficient (canonicalModel (s := s) (m := m)) canonicalStat :=
    isSufficient_of_isFactorizedDensity (canonicalModel (s := s) (m := m)) volume
      (canonicalDensity (s := s) (m := m)) measurable_canonicalDensity hP measurable_canonicalStat
      measurable_canonicalFactor measurable_const hfac
  exact hasSufficientKernel_of_isSufficient_dominated (canonicalModel (s := s) (m := m))
    measurable_canonicalStat volume hdom hsuf

/-- **Completeness of the canonical statistic**: an integrable function of
`(Y₁, …, Y_s, S²)` with identically vanishing mean vanishes almost everywhere. -/
theorem canonicalStat_isCompleteStat
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    IsCompleteStat (canonicalModel (s := s) (m := m)) canonicalStat := by
  -- Completeness of `T̃` from the full-rank exponential-family theorem.
  have hcomplete := isCompleteStat_of_interior_nonempty
    (canonicalExpFamily s m) (Set.range (canonicalEta (s := s)))
    (by rintro _ ⟨p, rfl⟩; exact canonicalEta_mem_natSet p)
    interior_range_canonicalEta_nonempty
  -- Reindex by the (surjective) natural-parameter map and shear onto `canonicalStat`.
  have hρ : Function.Surjective
      (fun p : CanonicalParam s =>
        (⟨canonicalEta p, Set.mem_range_self p⟩ : ↥(Set.range (canonicalEta (s := s))))) := by
    rintro ⟨w, p, rfl⟩; exact ⟨p, rfl⟩
  have htrans := isCompleteFamily_map_comp hcomplete hρ (measurable_canonicalShear (s := s))
  -- Identify the transported family with the model pushed forward by `canonicalStat`.
  show IsCompleteFamily (fun p => (canonicalModel p).map canonicalStat)
  have hfun : (fun p : CanonicalParam s => (canonicalModel (m := m) p).map (canonicalStat (m := m)))
      = fun p => (((canonicalExpFamily s m).P (canonicalEta p)).map
          (canonicalExpFamily s m).stat).map canonicalShear := by
    funext p
    have hL : (canonicalModel (m := m) p).map (canonicalStat (m := m))
        = ((canonicalExpFamily s m).P (canonicalEta p)).map
            (fun y => canonicalStat
              ((WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m))) y)) := by
      rw [canonicalModel, gaussianVector,
        Measure.map_map measurable_canonicalStat (WithLp.measurable_toLp 2 (Fin (s + m) → ℝ)),
        show (fun i => (canonicalMean p.1) i) = Fin.append p.1 (0 : Fin m → ℝ) from rfl,
        canonicalNormal_eq_P]
      rfl
    rw [hL, Measure.map_map measurable_canonicalShear (canonicalExpFamily s m).stat_meas]
    congr 1
    funext y
    exact canonicalStat_toLp_eq_shear y
  rw [hfun]; exact htrans

/-- `(Y₁, …, Y_s, S²)` is a **complete sufficient statistic** for `(η, σ²)`. -/
theorem canonical_complete_sufficient
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    HasSufficientKernel (canonicalModel (s := s) (m := m)) canonicalStat ∧
      IsCompleteStat (canonicalModel (s := s) (m := m)) canonicalStat :=
  ⟨canonicalStat_hasSufficientKernel (s := s) hm, canonicalStat_isCompleteStat (s := s) hm⟩

/-! ## UMVU scaffolding (private)

Every candidate below is a function of the complete sufficient statistic `canonicalStat`.
For such an estimator the covariance criterion is met: the covariance with any unbiased
estimator of zero vanishes, because its Rao–Blackwellization is an unbiased function of the
complete statistic, hence a.e. zero. The one subtlety — the competitor `U` carries only a
per-parameter `L²` representative — is resolved by the **mutual absolute continuity** of the
canonical members (strictly positive Gaussian densities), which upgrades a `P p₀`-a.e.
representative to a global one. -/

/-- The canonical density is strictly positive (a product of positive Gaussian pdfs). -/
private lemma canonicalDensity_pos (θ : CanonicalParam s)
    (Y : EuclideanSpace ℝ (Fin (s + m))) : 0 < canonicalDensity (m := m) θ Y := by
  unfold canonicalDensity
  rw [pos_iff_ne_zero, ne_eq, Finset.prod_eq_zero_iff]
  push_neg
  intro i _
  rw [gaussianPDF]
  exact (ENNReal.ofReal_pos.2 (gaussianPDFReal_pos _ _ _ (ne_of_gt θ.2.2))).ne'

/-- `volume` is absolutely continuous with respect to every canonical member. -/
private lemma volume_absolutelyContinuous_canonicalModel (θ : CanonicalParam s) :
    (volume : Measure (EuclideanSpace ℝ (Fin (s + m)))) ≪ canonicalModel (m := m) θ := by
  rw [canonicalModel_eq_withDensity]
  exact withDensity_absolutelyContinuous' (measurable_canonicalDensity θ).aemeasurable
    (Filter.Eventually.of_forall fun Y => (canonicalDensity_pos θ Y).ne')

/-- **Mutual absolute continuity** of the canonical members. -/
private lemma canonicalModel_absolutelyContinuous (θ θ' : CanonicalParam s) :
    canonicalModel (m := m) θ ≪ canonicalModel (m := m) θ' := by
  have h1 : canonicalModel (m := m) θ ≪ volume := by
    rw [canonicalModel_eq_withDensity]; exact withDensity_absolutelyContinuous _ _
  exact h1.trans (volume_absolutelyContinuous_canonicalModel θ')

/-- **Global measurable representative.** A per-parameter `L²` competitor has a single
measurable representative valid `P θ`-a.e. for every `θ` — the payoff of mutual absolute
continuity. -/
private lemma exists_measurableRep {U : EuclideanSpace ℝ (Fin (s + m)) → ℝ}
    (hU : MemEstL2 (canonicalModel (s := s) (m := m)) U) :
    ∃ Û : EuclideanSpace ℝ (Fin (s + m)) → ℝ, Measurable Û ∧
      ∀ θ, U =ᵐ[canonicalModel (m := m) θ] Û := by
  set θ₀ : CanonicalParam s := (fun _ => 0, ⟨1, one_pos⟩) with hθ₀
  refine ⟨(hU θ₀).aestronglyMeasurable.mk U,
    (hU θ₀).aestronglyMeasurable.stronglyMeasurable_mk.measurable, fun θ => ?_⟩
  exact (canonicalModel_absolutelyContinuous θ θ₀).ae_eq
    (hU θ₀).aestronglyMeasurable.ae_eq_mk

/-- **The covariance criterion is met by any function of the complete sufficient statistic.**
This is the reusable engine behind the three UMVU statements. -/
private theorem isUMVU_canonical_of_stat (hm : 0 < m)
    {g : CanonicalParam s → ℝ} {φ : (Fin s → ℝ) × ℝ → ℝ} (hφ : Measurable φ)
    (hunb : IsUnbiased (canonicalModel (s := s) (m := m)) g (fun y => φ (canonicalStat y)))
    (hL2 : MemEstL2 (canonicalModel (s := s) (m := m)) (fun y => φ (canonicalStat y))) :
    IsUMVU (canonicalModel (s := s) (m := m)) g (fun y => φ (canonicalStat y)) := by
  obtain ⟨Q, hQm, hgraph⟩ := canonicalStat_hasSufficientKernel (s := s) hm
  have hcomplete : IsCompleteStat (canonicalModel (s := s) (m := m)) canonicalStat :=
    canonicalStat_isCompleteStat (s := s) hm
  haveI hstatprob : ∀ θ' : CanonicalParam s,
      IsProbabilityMeasure (statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ') :=
    fun θ' => Measure.isProbabilityMeasure_map
      (μ := canonicalModel θ') measurable_canonicalStat.aemeasurable
  rw [isUMVU_iff_uncorrelated_unbiasedZero _ g hunb hL2]
  intro U hUz hUL2 θ
  obtain ⟨Û, hÛm, hÛae⟩ := exists_measurableRep hUL2
  -- covariance reduces to `∫ φ(T x) · U x`, since `E[U] = 0`
  have hEU : ∫ x, U x ∂(canonicalModel θ) = 0 := hUz θ
  rw [covariance_eq_sub (hL2 θ) (hUL2 θ), hEU, mul_zero, sub_zero]
  show ∫ x, φ (canonicalStat x) * U x ∂(canonicalModel θ) = 0
  -- replace `U` by its global representative `Û`
  have hprodeq : ∫ x, φ (canonicalStat x) * U x ∂(canonicalModel θ)
      = ∫ x, φ (canonicalStat x) * Û x ∂(canonicalModel θ) := by
    refine integral_congr_ae ?_
    filter_upwards [hÛae θ] with x hx
    rw [hx]
  rw [hprodeq]
  -- disintegrate the cross-integral through the sufficiency kernel
  have hÛL2 : ∀ θ', MemLp Û 2 (canonicalModel (m := m) θ') :=
    fun θ' => (hUL2 θ').ae_eq (hÛae θ')
  have hÛint : ∀ θ', Integrable Û (canonicalModel (m := m) θ') :=
    fun θ' => (hÛL2 θ').integrable one_le_two
  have hgm : Measurable (fun x : EuclideanSpace ℝ (Fin (s + m)) => (canonicalStat x, x)) :=
    measurable_canonicalStat.prodMk measurable_id
  have hf2 : Measurable (fun z : ((Fin s → ℝ) × ℝ) × EuclideanSpace ℝ (Fin (s + m)) =>
      φ z.1 * Û z.2) := (hφ.comp measurable_fst).mul (hÛm.comp measurable_snd)
  haveI : IsMarkovKernel Q := hQm
  -- rbEstimator of `Û` is an unbiased function of the complete statistic, hence a.e. zero
  have hrbUnb : IsUnbiased (canonicalModel (s := s) (m := m)) (fun _ => 0)
      (fun x => rbEstimator Q Û (canonicalStat x)) :=
    isUnbiased_rbEstimator (canonicalModel (s := s) (m := m)) (fun _ => 0)
      measurable_canonicalStat hgraph hÛm hÛint
      (fun θ' => by rw [← integral_congr_ae (hÛae θ')]; exact hUz θ')
  have hrbmeas : Measurable (rbEstimator Q Û) :=
    (hÛm.stronglyMeasurable.integral_kernel (κ := Q)).measurable
  have hrbint : ∀ θ', Integrable (rbEstimator Q Û)
      (statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ') := by
    intro θ'
    have hÛsnd : Integrable (fun z : ((Fin s → ℝ) × ℝ) × EuclideanSpace ℝ (Fin (s + m)) => Û z.2)
        (statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ' ⊗ₘ Q) := by
      rw [← hgraph θ']
      exact (integrable_map_measure (hÛm.comp measurable_snd).aestronglyMeasurable
        hgm.aemeasurable).mpr (hÛint θ')
    have hnorm := ((Measure.integrable_compProd_iff hÛsnd.aestronglyMeasurable).mp hÛsnd).2
    refine Integrable.mono' hnorm hrbmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    exact (norm_integral_le_integral_norm _).trans_eq rfl
  have hrbmean : ∀ θ', ∫ t, rbEstimator Q Û t
      ∂(statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ') = 0 := by
    intro θ'
    rw [statLaw, integral_map measurable_canonicalStat.aemeasurable
      hrbmeas.aestronglyMeasurable]
    exact hrbUnb θ'
  have hrbzero : rbEstimator Q Û
      =ᵐ[statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ] 0 :=
    hcomplete (rbEstimator Q Û) hrbmeas hrbint hrbmean θ
  -- the cross-integral equals `∫ φ · rbEstimator = 0`
  have hInt : Integrable (fun z => φ z.1 * Û z.2)
      (statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ ⊗ₘ Q) := by
    rw [← hgraph θ, integrable_map_measure hf2.aestronglyMeasurable hgm.aemeasurable]
    exact (hL2 θ).integrable_mul (hÛL2 θ)
  calc ∫ x, φ (canonicalStat x) * Û x ∂(canonicalModel θ)
      = ∫ z, φ z.1 * Û z.2
          ∂((canonicalModel θ).map (fun x => (canonicalStat x, x))) :=
        (integral_map hgm.aemeasurable hf2.aestronglyMeasurable).symm
    _ = ∫ z, φ z.1 * Û z.2
          ∂(statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ ⊗ₘ Q) := by rw [hgraph θ]
    _ = ∫ t, ∫ x, φ t * Û x ∂(Q t)
          ∂(statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ) :=
        Measure.integral_compProd hInt
    _ = ∫ t, φ t * rbEstimator Q Û t
          ∂(statLaw (canonicalModel (s := s) (m := m)) canonicalStat θ) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        exact integral_const_mul (φ t) Û
    _ = 0 := by
        refine integral_eq_zero_of_ae ?_
        filter_upwards [hrbzero] with t ht
        simp [ht]

/-! ## Coordinate moment reductions (private)

Every coordinate `y ↦ y k` of the canonical model is a single Gaussian marginal
`N(meanₖ, σ²)`. Integration and `L²`-membership of a function of one coordinate reduce to
the corresponding statement for `gaussianReal`. -/

/-- The canonical model as a pushforward of the coordinate product of Gaussians. -/
private lemma canonicalModel_eq_map_pi (p : CanonicalParam s) :
    canonicalModel (m := m) p
      = (Measure.pi (fun i => gaussianReal ((Fin.append p.1 (0 : Fin m → ℝ)) i) p.2.1)).map
          (WithLp.toLp 2 : (Fin (s + m) → ℝ) → EuclideanSpace ℝ (Fin (s + m))) := by
  rw [canonicalModel, gaussianVector]; rfl

/-- Reduction of a coordinate integral to a one-dimensional Gaussian integral. -/
private lemma canonicalModel_integral_coord (p : CanonicalParam s) (k : Fin (s + m))
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ y, f (y k) ∂(canonicalModel (m := m) p)
      = ∫ x, f x ∂(gaussianReal ((Fin.append p.1 (0 : Fin m → ℝ)) k) p.2.1) := by
  have hgmeas : Measurable (fun y : EuclideanSpace ℝ (Fin (s + m)) => f (y k)) :=
    hf.comp ((measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 _))
  rw [canonicalModel_eq_map_pi,
      integral_map (WithLp.measurable_toLp 2 _).aemeasurable hgmeas.aestronglyMeasurable]
  simp only [PiLp.toLp_apply]
  exact integral_comp_eval hf.aestronglyMeasurable

/-- Reduction of coordinate `L²`-membership to a one-dimensional Gaussian statement. -/
private lemma canonicalModel_memLp_coord (p : CanonicalParam s) (k : Fin (s + m))
    {f : ℝ → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 (gaussianReal ((Fin.append p.1 (0 : Fin m → ℝ)) k) p.2.1)) :
    MemLp (fun y => f (y k)) 2 (canonicalModel (m := m) p) := by
  have hgmeas : Measurable (fun y : EuclideanSpace ℝ (Fin (s + m)) => f (y k)) :=
    hfm.comp ((measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 _))
  rw [canonicalModel_eq_map_pi]
  refine (memLp_map_measure_iff hgmeas.aestronglyMeasurable
    (WithLp.measurable_toLp 2 _).aemeasurable).mpr ?_
  exact hf.comp_measurePreserving (MeasureTheory.measurePreserving_eval
    (μ := fun i => gaussianReal ((Fin.append p.1 (0 : Fin m → ℝ)) i) p.2.1) k)

/-! ## Unbiased optimality in the canonical model -/

/-- Each coordinate `Yᵢ` of the signal block is UMVU for the corresponding mean `ηᵢ`. -/
theorem isUMVU_coord
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) (i : Fin s) :
    IsUMVU (canonicalModel (s := s) (m := m)) (fun p => p.1 i)
      (fun y => canonicalHead y i) := by
  have hφ : Measurable (fun t : (Fin s → ℝ) × ℝ => t.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  refine isUMVU_canonical_of_stat hm hφ ?_ ?_
  · intro p
    show ∫ y, y (Fin.castAdd m i) ∂(canonicalModel p) = p.1 i
    have hc := canonicalModel_integral_coord (m := m) p (Fin.castAdd m i) (f := id) measurable_id
    simp only [id_eq] at hc
    rw [hc, integral_id_gaussianReal, Fin.append_left]
  · intro p
    show MemLp (fun y => y (Fin.castAdd m i)) 2 (canonicalModel p)
    exact canonicalModel_memLp_coord (m := m) p (Fin.castAdd m i)
      (f := id) measurable_id (memLp_id_gaussianReal 2)

/-- Every linear combination `∑ λᵢ Yᵢ` of the signal block is UMVU for `∑ λᵢ ηᵢ`. -/
theorem isUMVU_linear_combination
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional
    (lam : Fin s → ℝ) :
    IsUMVU (canonicalModel (s := s) (m := m)) (fun p => ∑ i, lam i * p.1 i)
      (fun y => ∑ i, lam i * canonicalHead y i) := by
  have hφ : Measurable (fun t : (Fin s → ℝ) × ℝ => ∑ i, lam i * t.1 i) :=
    Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)
  have hcoordMemLp : ∀ (p : CanonicalParam s) (i : Fin s),
      MemLp (fun y : EuclideanSpace ℝ (Fin (s + m)) => y (Fin.castAdd m i)) 2
        (canonicalModel p) := fun p i =>
    canonicalModel_memLp_coord (m := m) p (Fin.castAdd m i) (f := id) measurable_id
      (memLp_id_gaussianReal 2)
  have hcoordmean : ∀ (p : CanonicalParam s) (i : Fin s),
      ∫ y, y (Fin.castAdd m i) ∂(canonicalModel p) = p.1 i := by
    intro p i
    have hc := canonicalModel_integral_coord (m := m) p (Fin.castAdd m i) (f := id) measurable_id
    simp only [id_eq] at hc
    rw [hc, integral_id_gaussianReal, Fin.append_left]
  refine isUMVU_canonical_of_stat hm hφ ?_ ?_
  · intro p
    show ∫ y, ∑ i, lam i * y (Fin.castAdd m i) ∂(canonicalModel p) = ∑ i, lam i * p.1 i
    rw [integral_finset_sum _
      (fun i _ => ((hcoordMemLp p i).integrable one_le_two).const_mul (lam i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, hcoordmean p i]
  · intro p
    show MemLp (fun y => ∑ i, lam i * y (Fin.castAdd m i)) 2 (canonicalModel p)
    exact memLp_finset_sum _ fun i _ => (hcoordMemLp p i).const_mul (lam i)

/-- The rescaled residual sum of squares `S²/m` (that is, `S²/(n − s)`) is UMVU for the
variance `σ²`. -/
theorem isUMVU_residual_variance
    -- USER-INPUT: at least one residual coordinate (`s < n`); standing dimension condition
    (hm : 0 < m) :
    IsUMVU (canonicalModel (s := s) (m := m)) (fun p => (p.2.1 : ℝ))
      (fun y => canonicalRSS y / (m : ℝ)) := by
  have hφ : Measurable (fun t : (Fin s → ℝ) × ℝ => t.2 / (m : ℝ)) :=
    measurable_snd.div_const _
  -- one-dimensional second moment of a centred Gaussian
  have hsq2 : ∀ v : ℝ≥0, ∫ x, x ^ 2 ∂(gaussianReal (0 : ℝ) v) = (v : ℝ) := by
    intro v
    have h := variance_eq_sub (μ := gaussianReal (0 : ℝ) v) (X := id) (memLp_id_gaussianReal 2)
    rw [variance_id_gaussianReal] at h
    simp only [integral_id_gaussianReal, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, Pi.pow_apply, id_eq] at h
    linarith [h]
  -- `x ↦ x²` is square-integrable under any one-dimensional Gaussian (fourth moment finite)
  have hsqMemLp : ∀ (μ : ℝ) (v : ℝ≥0), MemLp (fun x => x ^ 2) 2 (gaussianReal μ v) := by
    intro μ v
    haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := ⟨by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by norm_num) (by norm_num)]
      rw [← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
    have h4 : MemLp (id : ℝ → ℝ) 4 (gaussianReal μ v) := memLp_id_gaussianReal' 4 (by simp)
    refine (h4.mul h4).ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, id_eq]; ring
  -- per-residual-coordinate second moment and integrability
  have hcoordsqmean : ∀ (p : CanonicalParam s) (j : Fin m),
      ∫ y : EuclideanSpace ℝ (Fin (s + m)), (y (Fin.natAdd s j)) ^ 2 ∂(canonicalModel p)
        = (p.2.1 : ℝ) := by
    intro p j
    have hc := canonicalModel_integral_coord (m := m) p (Fin.natAdd s j)
      (f := fun x => x ^ 2) (measurable_id.pow_const 2)
    rw [hc, Fin.append_right]
    simpa using hsq2 p.2.1
  have hcoordsqint : ∀ (p : CanonicalParam s) (j : Fin m),
      Integrable (fun y : EuclideanSpace ℝ (Fin (s + m)) => (y (Fin.natAdd s j)) ^ 2)
        (canonicalModel p) := fun p j =>
    (canonicalModel_memLp_coord (m := m) p (Fin.natAdd s j) (f := fun x => x ^ 2)
      (measurable_id.pow_const 2) (hsqMemLp _ _)).integrable one_le_two
  refine isUMVU_canonical_of_stat hm hφ ?_ ?_
  · intro p
    show ∫ y : EuclideanSpace ℝ (Fin (s + m)), canonicalRSS y / (m : ℝ) ∂(canonicalModel p)
      = (p.2.1 : ℝ)
    have hRSS : ∫ y : EuclideanSpace ℝ (Fin (s + m)), canonicalRSS y ∂(canonicalModel p)
        = (m : ℝ) * p.2.1 := by
      show ∫ y : EuclideanSpace ℝ (Fin (s + m)), ∑ j, (y (Fin.natAdd s j)) ^ 2 ∂(canonicalModel p)
        = (m : ℝ) * p.2.1
      rw [integral_finset_sum _ (fun j _ => hcoordsqint p j),
        Finset.sum_congr rfl (fun j _ => hcoordsqmean p j), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [integral_div, hRSS, mul_comm, mul_div_assoc,
      div_self (by exact_mod_cast hm.ne'), mul_one]
  · intro p
    show MemLp (fun y => canonicalRSS y / (m : ℝ)) 2 (canonicalModel p)
    have hRSSmemLp : MemLp (fun y : EuclideanSpace ℝ (Fin (s + m)) => canonicalRSS y) 2
        (canonicalModel p) := by
      show MemLp (fun y : EuclideanSpace ℝ (Fin (s + m)) => ∑ j, (y (Fin.natAdd s j)) ^ 2) 2
        (canonicalModel p)
      exact memLp_finset_sum _ fun j _ => canonicalModel_memLp_coord (m := m) p (Fin.natAdd s j)
        (f := fun x => x ^ 2) (measurable_id.pow_const 2) (hsqMemLp _ _)
    simpa [div_eq_mul_inv] using hRSSmemLp.mul_const (m : ℝ)⁻¹

end StatLean.PointEstimation
