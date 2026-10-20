module
public import StatLean.PointEstimation.InformationInequality.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-!
# Additivity of the Fisher information over independent observations

The information carried by two independent observations is the sum of the informations
they carry separately: for `X ~ p_θ` on `𝓧` and `Y ~ q_θ` on `𝓨`, independent, the joint
density is `p_θ(x) q_θ(y)` and
$$ I_{(X,Y)}(\theta) \;=\; I_X(\theta) + I_Y(\theta), \qquad\text{hence}\qquad
   I_{X_1,\dots,X_n}(\theta) \;=\; n\,I(\theta) $$
for an independent identically distributed sample. The joint score is the sum of the two
scores and the cross term vanishes because each score has mean zero.

Contents:
* `prodFamily` — the product family `θ ↦ p_θ ⊗ q_θ` on `𝓧 × 𝓨`;
* `fisherInfo_prod` — additivity of the information over an independent pair;
* `piFamily` — the `n`-fold product family on `Fin n → 𝓧`;
* `fisherInfo_pi` — the information in an independent identically distributed sample of
  size `n` is `n` times the information in one observation.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.5 (The
Information Inequality), Theorem 5.8 (additivity of the Fisher information over independent
observations). (`TPE2 §2.5 Thm 5.8`.)

**Proof formalization notes.**
* The product family is built at the level of *densities*, `p_θ(x) q_θ(y)`, so that the
  dominating measure of the pair is the product `μ ⊗ ν` and the score of the pair is
  literally the sum `ℓ̇_θ(x) + ℓ̇_θ(y)` on the common support (product rule for the
  parameter derivative, then division by the product density).
* The cross term `2 ∫∫ ℓ̇_θ(x) ℓ̇_θ(y) p_θ(x) q_θ(y)` factorizes by Fubini into a product of
  two mean-zero integrals; this is the only place the mean-zero hypotheses are used, and it
  is why they appear as hypotheses rather than being absorbed into the definitions.
* The `n`-fold statement is not obtained by iterating the pair statement (the carrier
  `Fin n → 𝓧` is not a nested binary product); it is proved directly, the score of the
  product density being the sum of the coordinate scores and the cross terms vanishing
  pairwise.
* The σ-finiteness instances are Lean-side requirements of the product-measure theory
  (Fubini), not conditions of the classical statement.

**Bibliographic comments.** Additivity of the information over independent observations
is due to R. A. Fisher ("Theory of statistical estimation," *Proc. Camb. Phil. Soc.* **22**
(1925), 700–725, where the information in a sample is computed as `n` times the information
in a single observation); it underlies the `1/n` scale of the information bound in
C. R. Rao ("Information and the accuracy attainable in the estimation of statistical
parameters," *Bull. Calcutta Math. Soc.* **37** (1945), 81–91) and H. Cramér
(*Mathematical Methods of Statistics*, Princeton University Press, 1946, §32.3).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

open AsymptoticStatistics (ParametricFamily IsPDFOf)

variable {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-! ## Two independent observations -/

/-- The **product family** of two dominated families: the density of the pair is the
product of the densities, `(θ, (x, y)) ↦ p_θ(x) q_θ(y)`, relative to the product of the
dominating measures. Measurability and non-negativity are inherited coordinatewise. -/
noncomputable def prodFamily (M : ParametricFamily 𝓧 ℝ) (N : ParametricFamily 𝓨 ℝ) :
    ParametricFamily (𝓧 × 𝓨) ℝ where
  density θ z := M.density θ z.1 * N.density θ z.2
  density_meas θ :=
    ((M.density_meas θ).comp measurable_fst).mul ((N.density_meas θ).comp measurable_snd)
  density_nonneg θ z := mul_nonneg (M.density_nonneg θ z.1) (N.density_nonneg θ z.2)

/-- **Additivity of the information over an independent pair**: the information carried by
`(X, Y)` with independent components is `I_X(θ) + I_Y(θ)`.

The joint score splits as `ℓ̇_θ(x) + ℓ̇_θ(y)`; squaring and integrating, the cross term is
the product of the two (vanishing) mean scores. -/
theorem fisherInfo_prod (M : ParametricFamily 𝓧 ℝ) (N : ParametricFamily 𝓨 ℝ)
    (μ : Measure 𝓧) (ν : Measure 𝓨)
    -- LEAN-ONLY: σ-finiteness of the dominating measures, required by Fubini for the
    -- product measure; no restriction of the classical statement
    [SigmaFinite μ] [SigmaFinite ν]
    -- USER-INPUT: both families are probability-density families
    (hM : IsPDFOf M μ) (hN : IsPDFOf N ν)
    -- USER-INPUT: both families have a common support; classical regularity condition
    (hMsupp : HasCommonSupport M) (hNsupp : HasCommonSupport N)
    (θ : ℝ)
    -- USER-INPUT: on their supports, both densities are differentiable in the parameter;
    -- classical smoothness condition, needed for the product rule (off the support the
    -- parameter map is constant `0` by the common-support condition)
    (hMdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    (hNdiff : ∀ y, 0 < N.density θ y → DifferentiableAt ℝ (fun t => N.density t y) θ)
    -- USER-INPUT: both scores have mean zero; classical regularity condition, and exactly
    -- what kills the cross term
    (hM0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    (hN0 : ∫ y, score N θ y * N.density θ y ∂ν = 0)
    -- LEAN-ONLY: finiteness of both informations as Bochner integrals
    (hMint : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    (hNint : Integrable (fun y => score N θ y ^ 2 * N.density θ y) ν)
    -- LEAN-ONLY: integrability of the two mean scores, needed to factorize the cross term
    (hMint1 : Integrable (fun x => score M θ x * M.density θ x) μ)
    (hNint1 : Integrable (fun y => score N θ y * N.density θ y) ν) :
    fisherInfo (prodFamily M N) (μ.prod ν) θ = fisherInfo M μ θ + fisherInfo N ν θ := by
  -- pointwise: the joint integrand splits into three product terms
  have key : ∀ z : 𝓧 × 𝓨, score (prodFamily M N) θ z ^ 2 * (prodFamily M N).density θ z
      = score M θ z.1 ^ 2 * M.density θ z.1 * N.density θ z.2
        + 2 * (score M θ z.1 * M.density θ z.1 * (score N θ z.2 * N.density θ z.2))
        + M.density θ z.1 * (score N θ z.2 ^ 2 * N.density θ z.2) := by
    intro z
    simp only [score, prodFamily]
    rcases eq_or_lt_of_le (M.density_nonneg θ z.1) with hp | hp
    · rw [← hp]; ring
    · rcases eq_or_lt_of_le (N.density_nonneg θ z.2) with hq | hq
      · rw [← hq]; ring
      · have hprodderiv : deriv (fun t => M.density t z.1 * N.density t z.2) θ
            = deriv (fun t => M.density t z.1) θ * N.density θ z.2
              + M.density θ z.1 * deriv (fun t => N.density t z.2) θ :=
          (((hMdiff z.1 hp).hasDerivAt).mul ((hNdiff z.2 hq).hasDerivAt)).deriv
        rw [hprodderiv]
        have hpne := hp.ne'
        have hqne := hq.ne'
        field_simp
        ring
  simp only [fisherInfo]
  have hcongr : (∫ z, score (prodFamily M N) θ z ^ 2 * (prodFamily M N).density θ z ∂(μ.prod ν))
      = ∫ z, (score M θ z.1 ^ 2 * M.density θ z.1 * N.density θ z.2
        + 2 * (score M θ z.1 * M.density θ z.1 * (score N θ z.2 * N.density θ z.2))
        + M.density θ z.1 * (score N θ z.2 ^ 2 * N.density θ z.2)) ∂(μ.prod ν) :=
    integral_congr_ae (Filter.Eventually.of_forall key)
  rw [hcongr]
  have iF1 : Integrable (fun z : 𝓧 × 𝓨 =>
      score M θ z.1 ^ 2 * M.density θ z.1 * N.density θ z.2) (μ.prod ν) :=
    Integrable.mul_prod hMint (hN.density_integrable θ)
  have iF2 : Integrable (fun z : 𝓧 × 𝓨 =>
      score M θ z.1 * M.density θ z.1 * (score N θ z.2 * N.density θ z.2)) (μ.prod ν) :=
    Integrable.mul_prod hMint1 hNint1
  have iF3 : Integrable (fun z : 𝓧 × 𝓨 =>
      M.density θ z.1 * (score N θ z.2 ^ 2 * N.density θ z.2)) (μ.prod ν) :=
    Integrable.mul_prod (hM.density_integrable θ) hNint
  have iF2c : Integrable (fun z : 𝓧 × 𝓨 =>
      2 * (score M θ z.1 * M.density θ z.1 * (score N θ z.2 * N.density θ z.2))) (μ.prod ν) :=
    iF2.const_mul 2
  have iF12 : Integrable (fun z : 𝓧 × 𝓨 =>
      score M θ z.1 ^ 2 * M.density θ z.1 * N.density θ z.2
        + 2 * (score M θ z.1 * M.density θ z.1 * (score N θ z.2 * N.density θ z.2)))
      (μ.prod ν) := iF1.add iF2c
  rw [integral_add iF12 iF3, integral_add iF1 iF2c, integral_const_mul]
  have eF1 : (∫ z, score M θ z.1 ^ 2 * M.density θ z.1 * N.density θ z.2 ∂(μ.prod ν))
      = (∫ x, score M θ x ^ 2 * M.density θ x ∂μ) * (∫ y, N.density θ y ∂ν) :=
    integral_prod_mul (fun x => score M θ x ^ 2 * M.density θ x) (fun y => N.density θ y)
  have eF2 : (∫ z, score M θ z.1 * M.density θ z.1 * (score N θ z.2 * N.density θ z.2) ∂(μ.prod ν))
      = (∫ x, score M θ x * M.density θ x ∂μ) * (∫ y, score N θ y * N.density θ y ∂ν) :=
    integral_prod_mul (fun x => score M θ x * M.density θ x)
      (fun y => score N θ y * N.density θ y)
  have eF3 : (∫ z, M.density θ z.1 * (score N θ z.2 ^ 2 * N.density θ z.2) ∂(μ.prod ν))
      = (∫ x, M.density θ x ∂μ) * (∫ y, score N θ y ^ 2 * N.density θ y ∂ν) :=
    integral_prod_mul (fun x => M.density θ x) (fun y => score N θ y ^ 2 * N.density θ y)
  rw [eF1, eF2, eF3, hM0, hN0, hM.density_integral_eq_one θ, hN.density_integral_eq_one θ]
  ring

/-! ## An independent identically distributed sample -/

/-- The **`n`-fold product family**: the density of an independent identically distributed
sample of size `n` is the product `∏ i, p_θ(x i)`, relative to the `n`-fold product of the
dominating measure. For `n = 0` the density is the empty product `1`, which is the correct
degenerate value (the model on the one-point sample space carries no information). -/
noncomputable def piFamily (M : ParametricFamily 𝓧 ℝ) (n : ℕ) :
    ParametricFamily (Fin n → 𝓧) ℝ where
  density θ x := ∏ i, M.density θ (x i)
  density_meas θ :=
    Finset.measurable_prod _ fun i _ => (M.density_meas θ).comp (measurable_pi_apply i)
  density_nonneg θ x := Finset.prod_nonneg fun i _ => M.density_nonneg θ (x i)

/-- **The information in an independent identically distributed sample**: a sample of size
`n` carries `n` times the information carried by one observation. -/
theorem fisherInfo_pi (M : ParametricFamily 𝓧 ℝ) (μ : Measure 𝓧)
    -- LEAN-ONLY: σ-finiteness of the dominating measure, required by the product-measure
    -- theory
    [SigmaFinite μ]
    (n : ℕ) (θ : ℝ)
    -- USER-INPUT: the family is a probability-density family
    (hM : IsPDFOf M μ)
    -- USER-INPUT: the family has a common support; classical regularity condition
    (hsupp : HasCommonSupport M)
    -- USER-INPUT: on the support, the density is differentiable in the parameter
    (hdiff : ∀ x, 0 < M.density θ x → DifferentiableAt ℝ (fun t => M.density t x) θ)
    -- USER-INPUT: the score has mean zero; classical regularity condition
    (hmean0 : ∫ x, score M θ x * M.density θ x ∂μ = 0)
    -- LEAN-ONLY: finiteness of the information as a Bochner integral
    (hint : Integrable (fun x => score M θ x ^ 2 * M.density θ x) μ)
    -- LEAN-ONLY: integrability of the mean score, needed to factorize the cross terms
    (hint1 : Integrable (fun x => score M θ x * M.density θ x) μ) :
    fisherInfo (piFamily M n) (Measure.pi fun _ : Fin n => μ) θ = (n : ℝ) * fisherInfo M μ θ := by
  -- product-rule reduction of the joint score on the support
  have hderiv_pi : ∀ x : Fin n → 𝓧, (∀ i, 0 < M.density θ (x i)) →
      deriv (fun t => ∏ i, M.density t (x i)) θ
        = (∑ i, score M θ (x i)) * ∏ i, M.density θ (x i) := by
    intro x hx
    rw [deriv_fun_finset_prod (fun i _ => hdiff (x i) (hx i)), Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hne := (hx i).ne'
    rw [smul_eq_mul, score,
      ← Finset.mul_prod_erase Finset.univ (fun k => M.density θ (x k)) (Finset.mem_univ i)]
    field_simp
  -- pointwise: joint integrand = (∑ scoreᵢ)² · ∏ pⱼ
  have key_pi : ∀ x : Fin n → 𝓧, score (piFamily M n) θ x ^ 2 * (piFamily M n).density θ x
      = (∑ i, score M θ (x i)) ^ 2 * ∏ i, M.density θ (x i) := by
    intro x
    rcases eq_or_ne (∏ i, M.density θ (x i)) 0 with h0 | h0
    · have hpi : (piFamily M n).density θ x = 0 := by simp only [piFamily]; exact h0
      rw [hpi, h0]; ring
    · have hx : ∀ i, 0 < M.density θ (x i) := fun i =>
        lt_of_le_of_ne (M.density_nonneg θ (x i))
          (Ne.symm fun hi => h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi))
      have hscore_eq : score (piFamily M n) θ x = ∑ i, score M θ (x i) := by
        rw [score]
        simp only [piFamily]
        rw [hderiv_pi x hx, mul_div_assoc, div_self h0, mul_one]
      rw [hscore_eq]
      simp only [piFamily]
  -- expand the square into a double sum
  have hexpand : ∀ x : Fin n → 𝓧, (∑ i, score M θ (x i)) ^ 2 * ∏ k, M.density θ (x k)
      = ∑ i, ∑ j, score M θ (x i) * score M θ (x j) * ∏ k, M.density θ (x k) := by
    intro x
    rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
  -- per-coordinate integrability of the guarded product factors
  have hf_int : ∀ i j k : Fin n, Integrable (fun a => (if k = i then score M θ a else 1)
      * (if k = j then score M θ a else 1) * M.density θ a) μ := by
    intro i j k
    by_cases hki : k = i
    · by_cases hkj : k = j
      · simp only [if_pos hki, if_pos hkj]
        exact hint.congr (Filter.Eventually.of_forall fun a => by ring)
      · simp only [if_pos hki, if_neg hkj, mul_one]
        exact hint1
    · by_cases hkj : k = j
      · simp only [if_neg hki, if_pos hkj, one_mul]
        exact hint1
      · simp only [if_neg hki, if_neg hkj, one_mul, mul_one]
        exact hM.density_integrable θ
  -- factorisation of the (i,j)-term integrand into a coordinatewise product
  have hpt : ∀ (i j : Fin n) (x : Fin n → 𝓧),
      score M θ (x i) * score M θ (x j) * ∏ k, M.density θ (x k)
        = ∏ k, (if k = i then score M θ (x k) else 1) * (if k = j then score M θ (x k) else 1)
            * M.density θ (x k) := by
    intro i j x
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq',
      if_pos (Finset.mem_univ i), if_pos (Finset.mem_univ j)]
  -- integrability of each base term over the product measure
  have hbase_int : ∀ i j : Fin n, Integrable
      (fun x => score M θ (x i) * score M θ (x j) * ∏ k, M.density θ (x k))
      (Measure.pi fun _ : Fin n => μ) := by
    intro i j
    refine (Integrable.fintype_prod (f := fun k a => (if k = i then score M θ a else 1)
      * (if k = j then score M θ a else 1) * M.density θ a) (fun k => hf_int i j k)).congr ?_
    exact Filter.Eventually.of_forall fun x => (hpt i j x).symm
  -- the (i,j)-term evaluates to `I` on the diagonal and `0` off it
  have hterm : ∀ i j : Fin n,
      (∫ x, score M θ (x i) * score M θ (x j) * ∏ k, M.density θ (x k)
        ∂(Measure.pi fun _ : Fin n => μ)) = if i = j then fisherInfo M μ θ else 0 := by
    intro i j
    rw [integral_congr_ae (Filter.Eventually.of_forall (hpt i j)),
      integral_fintype_prod_eq_prod (fun k a => (if k = i then score M θ a else 1)
        * (if k = j then score M θ a else 1) * M.density θ a)]
    by_cases hij : i = j
    · subst hij
      have hoff : ∀ k ∈ (Finset.univ : Finset (Fin n)), k ≠ i →
          (∫ a, (if k = i then score M θ a else 1) * (if k = i then score M θ a else 1)
            * M.density θ a ∂μ) = 1 := by
        intro k _ hk
        simp only [if_neg hk, one_mul]
        exact hM.density_integral_eq_one θ
      rw [if_pos rfl, Finset.prod_eq_single i hoff (fun h => absurd (Finset.mem_univ i) h)]
      simp only [↓reduceIte]
      rw [fisherInfo]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      ring
    · rw [if_neg hij]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp only [if_pos rfl, if_neg hij, mul_one]
      exact hmean0
  -- integrability of the inner sum
  have hsum_int : ∀ i : Fin n, Integrable
      (fun x => ∑ j, score M θ (x i) * score M θ (x j) * ∏ k, M.density θ (x k))
      (Measure.pi fun _ : Fin n => μ) :=
    fun i => integrable_finset_sum Finset.univ (fun j _ => hbase_int i j)
  -- assemble
  rw [fisherInfo, integral_congr_ae (Filter.Eventually.of_forall key_pi),
    integral_congr_ae (Filter.Eventually.of_forall hexpand),
    integral_finset_sum Finset.univ (fun i _ => hsum_int i)]
  have hinner : ∀ i : Fin n, (∫ x, ∑ j, score M θ (x i) * score M θ (x j) * ∏ k, M.density θ (x k)
      ∂(Measure.pi fun _ : Fin n => μ)) = ∑ j, if i = j then fisherInfo M μ θ else 0 := by
    intro i
    rw [integral_finset_sum Finset.univ (fun j _ => hbase_int i j)]
    exact Finset.sum_congr rfl (fun j _ => hterm i j)
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end StatLean.PointEstimation
