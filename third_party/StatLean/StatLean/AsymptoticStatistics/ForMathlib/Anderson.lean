module
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianConv
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
public import StatLean.AsymptoticStatistics.ForMathlib.PiGaussian
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import StatLean.AsymptoticStatistics.ForMathlib.PrekopaLeindler
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Topology.Algebra.Module.Equiv

@[expose] public section

/-!
# Anderson's lemma for centered multivariate Gaussians

Anderson (1955): for centered Gaussian $\nu = N(0, \Sigma)$ on $\mathbb R^d$ and
convex symmetric $C \subset \mathbb R^d$, $\nu(C - y) \le \nu(C)$ for any
$y \in \mathbb R^d$. Equivalently $\int L \, d\nu \le \int L(\cdot + y) \, d\nu$
for any bowl-shaped $L$.

Anderson is built via the Prékopa-Leindler route (`ForMathlib/PrekopaLeindler.lean`):
the multivariate Gaussian density is log-concave, so PL gives Anderson. The set
form `anderson_lemma_set` is the technical core; the loss / independent /
PSD-monotone forms (`anderson_lemma_loss`, `anderson_lemma_independent`,
`gaussian_lintegral_mono_of_psd_le`) are corollaries.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder Topology

namespace AsymptoticStatistics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Stochastic dominance via superlevel-set inequality** (ℝ≥0∞-valued).

For two probability measures `μ, ν` on a measurable space `E` and a measurable
`L : E → ℝ≥0∞`, if `μ {L > c} ≤ ν {L > c}` for every level `c : ℝ≥0∞`, then
`∫⁻ L ∂μ ≤ ∫⁻ L ∂ν`.

**Proof**: truncate `L` to `L_n := L ⊓ (n : ℝ≥0∞)` — bounded by `n`, monotone
in `n`, with `⨆ n, L_n = L`. MCT (`lintegral_iSup`) reduces the goal to the
per-`n` inequality `∫⁻ L_n ∂μ ≤ ∫⁻ L_n ∂ν`. On each truncation, `L_n` is
`∞`-free, so `L_n = ENNReal.ofReal (L_n·).toReal`; apply Mathlib's real-valued
layer cake `lintegral_eq_lintegral_meas_lt` on both sides and compare the
inner level sets. For real `t ∈ Ioi 0` below `n`, `{t < (L_n·).toReal}` unfolds
to `{ENNReal.ofReal t < L}` (the `⊓ n` side is automatic), and `h_level`
applies verbatim; for `t ≥ n` the set is empty. -/
lemma lintegral_mono_of_meas_lt_le
    {E : Type*} [MeasurableSpace E] {L : E → ℝ≥0∞} (hL : Measurable L)
    {μ ν : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h_level : ∀ c : ℝ≥0∞, μ {x | c < L x} ≤ ν {x | c < L x}) :
    ∫⁻ x, L x ∂μ ≤ ∫⁻ x, L x ∂ν := by
  -- Truncation family `F n x := L x ⊓ (n : ℝ≥0∞)`.
  have hF_meas : ∀ n : ℕ, Measurable (fun x => L x ⊓ (n : ℝ≥0∞)) :=
    fun n => hL.min measurable_const
  have hF_mono : Monotone (fun (n : ℕ) (x : E) => L x ⊓ (n : ℝ≥0∞)) :=
    fun m n hmn x => inf_le_inf_left _ (by exact_mod_cast hmn)
  have hF_bdd : ∀ (n : ℕ) (x : E), L x ⊓ (n : ℝ≥0∞) ≤ (n : ℝ≥0∞) :=
    fun _ _ => inf_le_right
  have hF_fin : ∀ (n : ℕ) (x : E), L x ⊓ (n : ℝ≥0∞) ≠ ⊤ := fun n x h => by
    have : (⊤ : ℝ≥0∞) ≤ (n : ℝ≥0∞) := h ▸ hF_bdd n x
    exact ENNReal.natCast_ne_top n (top_le_iff.mp this)
  -- Pointwise `⨆ n, L x ⊓ n = L x`.
  have hF_sup : ∀ x, ⨆ n : ℕ, L x ⊓ (n : ℝ≥0∞) = L x := by
    intro x
    refine le_antisymm (iSup_le fun _ => inf_le_left) ?_
    by_cases hL_top : L x = ⊤
    · rw [hL_top]
      simp only [top_inf_eq]
      exact ENNReal.iSup_natCast.ge
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hL_top
      exact le_iSup_of_le n (le_inf le_rfl hn.le)
  -- Swap `L` for its truncation sup; then MCT on both measures.
  have hL_eq : L = fun x => ⨆ n : ℕ, L x ⊓ (n : ℝ≥0∞) :=
    funext fun x => (hF_sup x).symm
  calc ∫⁻ x, L x ∂μ
      = ⨆ n : ℕ, ∫⁻ x, L x ⊓ (n : ℝ≥0∞) ∂μ := by
        conv_lhs => rw [hL_eq]
        exact lintegral_iSup hF_meas hF_mono
    _ ≤ ⨆ n : ℕ, ∫⁻ x, L x ⊓ (n : ℝ≥0∞) ∂ν := by
        -- Per-`n` inequality via real-valued layer cake.
        refine iSup_mono (fun n => ?_)
        have hFn_toReal_meas : Measurable (fun x => (L x ⊓ (n : ℝ≥0∞)).toReal) :=
          (hF_meas n).ennreal_toReal
        have hFn_eq : (fun x => L x ⊓ (n : ℝ≥0∞))
            = fun x => ENNReal.ofReal ((L x ⊓ (n : ℝ≥0∞)).toReal) :=
          funext fun x => (ENNReal.ofReal_toReal (hF_fin n x)).symm
        have h_μ_lc : ∫⁻ x, L x ⊓ (n : ℝ≥0∞) ∂μ
            = ∫⁻ t in Set.Ioi (0 : ℝ), μ {x | t < (L x ⊓ (n : ℝ≥0∞)).toReal} := by
          rw [hFn_eq]
          exact lintegral_eq_lintegral_meas_lt μ
            (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
            hFn_toReal_meas.aemeasurable
        have h_ν_lc : ∫⁻ x, L x ⊓ (n : ℝ≥0∞) ∂ν
            = ∫⁻ t in Set.Ioi (0 : ℝ), ν {x | t < (L x ⊓ (n : ℝ≥0∞)).toReal} := by
          rw [hFn_eq]
          exact lintegral_eq_lintegral_meas_lt ν
            (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
            hFn_toReal_meas.aemeasurable
        rw [h_μ_lc, h_ν_lc]
        refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
        have ht_pos : (0 : ℝ) < t := ht
        by_cases htn : t < (n : ℝ)
        · -- For `t < n`: level set equals `{ENNReal.ofReal t < L}`.
          have h_set_eq : {x : E | t < (L x ⊓ (n : ℝ≥0∞)).toReal}
              = {x | ENNReal.ofReal t < L x} := by
            ext x
            simp only [Set.mem_setOf_eq]
            rw [← ENNReal.ofReal_lt_iff_lt_toReal ht_pos.le (hF_fin n x)]
            refine ⟨fun h => lt_of_lt_of_le h inf_le_left, fun h => lt_inf_iff.mpr ⟨h, ?_⟩⟩
            rw [show ((n : ℕ) : ℝ≥0∞) = ENNReal.ofReal n from
                (ENNReal.ofReal_natCast n).symm]
            exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht_pos.le).mpr htn
          rw [h_set_eq]
          exact h_level _
        · -- For `t ≥ n`: level set is empty.
          have htn' : (n : ℝ) ≤ t := not_lt.mp htn
          have h_empty : {x : E | t < (L x ⊓ (n : ℝ≥0∞)).toReal} = ∅ := by
            ext x
            simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
            calc (L x ⊓ (n : ℝ≥0∞)).toReal
                ≤ ((n : ℝ≥0∞)).toReal :=
                  ENNReal.toReal_mono (ENNReal.natCast_ne_top n) (hF_bdd n x)
              _ = (n : ℝ) := ENNReal.toReal_natCast n
              _ ≤ t := htn'
          rw [h_empty, measure_empty]
          exact zero_le
    _ = ∫⁻ x, L x ∂ν := by
        conv_rhs => rw [hL_eq]
        exact (lintegral_iSup hF_meas hF_mono).symm

omit [DecidableEq ι] in
/-- **1D Gaussian density log-concavity at midpoint** (squared form).

For all `t₁, t₂ : ℝ`,
`gaussianPDFReal 0 1 t₁ · gaussianPDFReal 0 1 t₂ ≤ (gaussianPDFReal 0 1 ((t₁+t₂)/2))²`.

This is the geometric-mean-≤-midpoint-value form of log-concavity for the
standard 1D Gaussian density. The squared version sidesteps `Real.sqrt` for a
cleaner proof; downstream `gaussianPDF_pi_geom_mean_le` (ENNReal-valued, with
`^(1/2)`) is derived from this. -/
lemma gaussianPDFReal_one_log_concave (t₁ t₂ : ℝ) :
    gaussianPDFReal 0 1 t₁ * gaussianPDFReal 0 1 t₂
      ≤ (gaussianPDFReal 0 1 ((t₁ + t₂) / 2)) ^ 2 := by
  -- Unfold both sides; let `c := (√(2π·1))⁻¹` be the normalising constant.
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
  set c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hc_def
  -- Reorganise both sides as `c² · (exp ...)`.
  have h_lhs : c * Real.exp (-t₁ ^ 2 / 2) * (c * Real.exp (-t₂ ^ 2 / 2))
      = c ^ 2 * Real.exp (-(t₁ ^ 2 + t₂ ^ 2) / 2) := by
    rw [show c * Real.exp (-t₁ ^ 2 / 2) * (c * Real.exp (-t₂ ^ 2 / 2))
        = c ^ 2 * (Real.exp (-t₁ ^ 2 / 2) * Real.exp (-t₂ ^ 2 / 2)) by ring,
        ← Real.exp_add]
    congr 1; ring
  have h_rhs : (c * Real.exp (-((t₁ + t₂) / 2) ^ 2 / 2)) ^ 2
      = c ^ 2 * Real.exp (-(t₁ + t₂) ^ 2 / 4) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 1; ring
  rw [h_lhs, h_rhs]
  -- Reduce to: `c² · exp(-(t₁²+t₂²)/2) ≤ c² · exp(-(t₁+t₂)²/4)`
  -- via `(t₁+t₂)² ≤ 2(t₁²+t₂²)` (parallelogram inequality `add_sq_le`).
  have h_c_sq_nn : 0 ≤ c ^ 2 := sq_nonneg _
  refine mul_le_mul_of_nonneg_left ?_ h_c_sq_nn
  refine Real.exp_le_exp_of_le ?_
  -- Goal: -(t₁² + t₂²)/2 ≤ -(t₁+t₂)²/4
  have h_par : (t₁ + t₂) ^ 2 ≤ 2 * (t₁ ^ 2 + t₂ ^ 2) := add_sq_le
  linarith

omit [DecidableEq ι] in
/-- **Pi standard Gaussian density log-concavity** (real-valued, squared form).

The product form of `gaussianPDFReal_one_log_concave`, lifted from each
coordinate via `Finset.prod_le_prod`. -/
lemma gaussianPDFReal_pi_log_concave (u v : ι → ℝ) :
    (∏ i, gaussianPDFReal 0 1 (u i)) * (∏ i, gaussianPDFReal 0 1 (v i))
      ≤ (∏ i, gaussianPDFReal 0 1 ((u i + v i) / 2)) ^ 2 := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  exact Finset.prod_le_prod
    (fun i _ => mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))
    (fun i _ => gaussianPDFReal_one_log_concave (u i) (v i))

omit [DecidableEq ι] in
/-- **Pi standard Gaussian density log-concavity** (ENNReal-valued, squared form).

ENNReal lift of `gaussianPDFReal_pi_log_concave` via `ENNReal.ofReal` monotonicity. -/
lemma gaussianPDF_pi_log_concave (u v : ι → ℝ) :
    (∏ i, gaussianPDF 0 1 (u i)) * (∏ i, gaussianPDF 0 1 (v i))
      ≤ (∏ i, gaussianPDF 0 1 ((u i + v i) / 2)) ^ 2 := by
  -- Express each `gaussianPDF` as `ENNReal.ofReal (gaussianPDFReal …)`.
  simp_rw [gaussianPDF_def]
  -- Pull `ofReal` through the products via `ENNReal.ofReal_prod_of_nonneg`.
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _),
      ← ENNReal.ofReal_pow (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _)]
  exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_pi_log_concave u v)

omit [DecidableEq ι] in
/-- **Pi standard Gaussian density log-concavity** (half-power form for PL).

The form directly used by PL at `t = 1/2`:
`(∏ᵢ pdf(uᵢ))^{1/2} · (∏ᵢ pdf(vᵢ))^{1/2} ≤ ∏ᵢ pdf((uᵢ+vᵢ)/2)`.

Derived from the squared form `gaussianPDF_pi_log_concave` by taking square root
in ENNReal. -/
lemma gaussianPDF_pi_geom_mean_le (u v : ι → ℝ) :
    (∏ i, gaussianPDF 0 1 (u i)) ^ ((1 : ℝ) / 2)
        * (∏ i, gaussianPDF 0 1 (v i)) ^ ((1 : ℝ) / 2)
      ≤ ∏ i, gaussianPDF 0 1 ((u i + v i) / 2) := by
  have h_sq := gaussianPDF_pi_log_concave u v
  have h_half_nn : (0 : ℝ) ≤ 1 / 2 := by norm_num
  -- LHS = (∏ pdf u_i)^{1/2} · (∏ pdf v_i)^{1/2} = ((∏ pdf u_i) · (∏ pdf v_i))^{1/2}
  rw [← ENNReal.mul_rpow_of_nonneg _ _ h_half_nn]
  -- Take ^{1/2} of both sides of the squared inequality.
  have h_taken : ((∏ i, gaussianPDF 0 1 (u i)) * ∏ i, gaussianPDF 0 1 (v i))
        ^ ((1 : ℝ) / 2)
      ≤ ((∏ i, gaussianPDF 0 1 ((u i + v i) / 2)) ^ 2) ^ ((1 : ℝ) / 2) :=
    ENNReal.rpow_le_rpow h_sq h_half_nn
  -- Simplify the RHS: (c^(2:ℕ))^(1/2:ℝ) = c.
  have h_simp : ((∏ i, gaussianPDF 0 1 ((u i + v i) / 2)) ^ 2) ^ ((1 : ℝ) / 2)
      = ∏ i, gaussianPDF 0 1 ((u i + v i) / 2) := by
    rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul,
        show ((2 : ℕ) : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  rw [h_simp] at h_taken
  exact h_taken

omit [DecidableEq ι] in
/-- **Generalised PL-Anderson on `Measure.pi (gaussianReal 0 1)`** (private).

For any measurable `A_+, A_- ⊂ (ι → ℝ)` and convex symmetric measurable
`K ⊂ (ι → ℝ)` such that the Minkowski mean is contained in `K`
(`(1/2)•u + (1/2)•v ∈ K` for `u ∈ A_+`, `v ∈ A_-`) plus measure symmetry
`ν A_- = ν A_+`, conclude `ν A_+ ≤ ν K`.

Proof shape mirrors `anderson_lemma_set_pi`'s PL argument with `A_+ := C - y`,
`A_- := C + y`, `K := C`, but takes generic `A_+, A_-, K` — needed for the
singular-PSD branch of `anderson_lemma_set` where the relevant sets are
`Φ⁻¹'(C ± y)` and `Φ⁻¹' C` for a non-invertible linear `Φ` and translation
into `K` is no longer a literal shift. -/
private lemma _pl_anderson_pi_general
    {A_plus A_minus K : Set (ι → ℝ)}
    (hA_plus_meas : MeasurableSet A_plus) (hA_minus_meas : MeasurableSet A_minus)
    (hK_meas : MeasurableSet K)
    (h_mean : ∀ u ∈ A_plus, ∀ v ∈ A_minus, ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) ∈ K)
    (h_symm : (Measure.pi (fun _ : ι => gaussianReal 0 1)) A_minus =
              (Measure.pi (fun _ : ι => gaussianReal 0 1)) A_plus) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) A_plus ≤
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) K := by
  set ν := Measure.pi (fun _ : ι => gaussianReal 0 1) with hν_def
  let ρ : (ι → ℝ) → ℝ≥0∞ := fun x => ∏ i, gaussianPDF 0 1 (x i)
  have hρ_meas : Measurable ρ :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have h_ν_eq : ν = (volume : Measure (ι → ℝ)).withDensity ρ :=
    pi_gaussianReal_eq_withDensity
  have h_ν_set : ∀ A : Set (ι → ℝ), MeasurableSet A →
      ν A = ∫⁻ x, A.indicator ρ x ∂volume := fun A hA => by
    rw [h_ν_eq, withDensity_apply ρ hA, ← lintegral_indicator hA]
  have h_PL : (∫⁻ x, A_plus.indicator ρ x ∂volume) ^ ((1 : ℝ) / 2)
        * (∫⁻ x, A_minus.indicator ρ x ∂volume) ^ (1 - (1 : ℝ) / 2)
      ≤ ∫⁻ z, K.indicator ρ z ∂volume := by
    refine prekopaLeindler
      (hρ_meas.indicator hA_plus_meas)
      (hρ_meas.indicator hA_minus_meas)
      (hρ_meas.indicator hK_meas)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) ?_
    intro u v
    simp only [show (1 : ℝ) - 1/2 = 1/2 from by norm_num]
    by_cases hu : u ∈ A_plus
    · by_cases hv : v ∈ A_minus
      · have h_mid : (1/2 : ℝ) • u + (1/2 : ℝ) • v ∈ K := h_mean u hu v hv
        rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv,
            Set.indicator_of_mem h_mid]
        change (∏ i, gaussianPDF 0 1 (u i)) ^ ((1:ℝ)/2)
             * (∏ i, gaussianPDF 0 1 (v i)) ^ ((1:ℝ)/2)
             ≤ ∏ i, gaussianPDF 0 1 (((1/2 : ℝ) • u + (1/2 : ℝ) • v) i)
        have h_per_i : ∀ i : ι, ((1/2:ℝ) • u + (1/2:ℝ) • v) i = (u i + v i) / 2 := by
          intro i; simp [Pi.smul_apply, Pi.add_apply]; ring
        simp only [h_per_i]
        exact gaussianPDF_pi_geom_mean_le u v
      · rw [Set.indicator_of_notMem hv,
            ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2), mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hu,
          ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2), zero_mul]
      exact zero_le
  simp only [show (1 : ℝ) - 1/2 = 1/2 from by norm_num] at h_PL
  rw [← h_ν_set A_plus hA_plus_meas, ← h_ν_set A_minus hA_minus_meas,
      ← h_ν_set K hK_meas] at h_PL
  rw [h_symm] at h_PL
  have h_sq : ν A_plus ^ ((1:ℝ)/2) * ν A_plus ^ ((1:ℝ)/2) = ν A_plus := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2),
        show ((1:ℝ)/2 + 1/2) = 1 from by norm_num, ENNReal.rpow_one]
  rw [h_sq] at h_PL
  exact h_PL

omit [DecidableEq ι] in
/-- **Anderson's lemma — Pi standard Gaussian form** (PL-ready intermediate).

For the product of independent standard 1D Gaussians on `ι → ℝ`
(`Measure.pi (fun _ => gaussianReal 0 1)`), and any convex symmetric measurable
set `C ⊂ ι → ℝ`, the shifted measure satisfies
$$\nu_0(C - y) \le \nu_0(C), \qquad \nu_0 = \bigotimes_i N(0,1).$$

This is the "raw" form to which the Prékopa-Leindler inequality directly
applies: `Measure.pi (gaussianReal 0 1) = volume.withDensity ρ` where
`ρ(x) = (2π)^{-d/2} exp(-‖x‖² / 2)` is the standard Gaussian density on
`ι → ℝ`, and `ρ` is log-concave (its log is `-‖x‖²/2 - const`, concave on a
real inner product space).

**Proof sketch**: let `f := ρ · 𝟙_{C-y}`, `g := ρ · 𝟙_{C+y}`,
`h := ρ · 𝟙_C`. Apply n-dim PL (`prekopaLeindler`) at `t = 1/2`:
the pointwise hypothesis `f(u)^{1/2} g(v)^{1/2} ≤ h((u+v)/2)` follows from
log-concavity of `ρ` and midpoint convexity of `C` (using `C` symmetric:
`u ∈ C-y` and `v ∈ C+y` ⇒ `u+y ∈ C, v-y ∈ C` ⇒ `(u+v)/2 = ((u+y) + (v-y))/2 ∈ C`).
Hence `√(ν_0(C-y) · ν_0(C+y)) ≤ ν_0(C)`, i.e. `ν_0(C-y)·ν_0(C+y) ≤ ν_0(C)²`.
Symmetry of the standard Gaussian (`pi (gaussianReal 0 1)` is invariant under
`x ↦ -x`) plus `C` symmetric gives `ν_0(C+y) = ν_0(C-y)`. Conclude.

Used by `anderson_lemma_set` (the multivariate form) via transport through
`stdGaussian.map S^{1/2}` after bridging `Measure.pi` ↔ `stdGaussian` via
`map_pi_eq_stdGaussian`. -/
theorem anderson_lemma_set_pi
    {C : Set (ι → ℝ)} (hC_meas : MeasurableSet C)
    (hC_conv : Convex ℝ C) (hC_symm : ∀ x ∈ C, -x ∈ C)
    (y : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) {x | x + y ∈ C}
      ≤ (Measure.pi (fun _ : ι => gaussianReal 0 1)) C := by
  set ν := Measure.pi (fun _ : ι => gaussianReal 0 1) with hν_def
  let ρ : (ι → ℝ) → ℝ≥0∞ := fun x => ∏ i, gaussianPDF 0 1 (x i)
  have hρ_meas : Measurable ρ :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  -- Density: ν = volume.withDensity ρ.
  have h_ν_eq : ν = (volume : Measure (ι → ℝ)).withDensity ρ :=
    pi_gaussianReal_eq_withDensity
  -- The two shifted sets and `C` itself; all measurable.
  let A_plus : Set (ι → ℝ) := {x | x + y ∈ C}
  let A_minus : Set (ι → ℝ) := {x | x - y ∈ C}
  have hA_plus_meas : MeasurableSet A_plus := (measurable_id.add_const y) hC_meas
  have hA_minus_meas : MeasurableSet A_minus := (measurable_id.sub_const y) hC_meas
  -- Generic: `ν A = ∫⁻ A.indicator ρ` via `withDensity_apply`.
  have h_ν_set : ∀ A : Set (ι → ℝ), MeasurableSet A →
      ν A = ∫⁻ x, A.indicator ρ x ∂volume := fun A hA => by
    rw [h_ν_eq, withDensity_apply ρ hA, ← lintegral_indicator hA]
  -- PL functions: f, g, h := ρ * 𝟙_{A±, C}.
  -- We'll work with the equivalent `A.indicator ρ` form.
  -- Apply PL at `t = 1/2`.
  have h_PL : (∫⁻ x, A_plus.indicator ρ x ∂volume) ^ ((1 : ℝ) / 2)
        * (∫⁻ x, A_minus.indicator ρ x ∂volume) ^ (1 - (1 : ℝ) / 2)
      ≤ ∫⁻ z, C.indicator ρ z ∂volume := by
    refine prekopaLeindler
      (hρ_meas.indicator hA_plus_meas)
      (hρ_meas.indicator hA_minus_meas)
      (hρ_meas.indicator hC_meas)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) ?_
    intro u v
    -- Normalise `1 - 1/2 = 1/2` so downstream rewrites match.
    have h_one_minus_half : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    simp only [h_one_minus_half]
    -- Pointwise: A_plus.indicator ρ u ^ {1/2} * A_minus.indicator ρ v ^ {1/2}
    --             ≤ C.indicator ρ ((1/2)•u + (1/2)•v)
    -- Case split on whether u ∈ A_plus and v ∈ A_minus.
    by_cases hu : u ∈ A_plus
    · by_cases hv : v ∈ A_minus
      · -- Both: midpoint in C by convexity (using C symmetric to handle ±y).
        -- (u+y) ∈ C, (v-y) ∈ C; (1/2)(u+y) + (1/2)(v-y) = (1/2)u + (1/2)v ∈ C.
        have hu' : u + y ∈ C := hu
        have hv' : v - y ∈ C := hv
        have h_mid_in_C : (1/2 : ℝ) • u + (1/2 : ℝ) • v ∈ C := by
          have h_combine : (1/2 : ℝ) • u + (1/2 : ℝ) • v
              = (1/2 : ℝ) • (u + y) + (1/2 : ℝ) • (v - y) := by
            rw [smul_add, smul_sub]; abel
          rw [h_combine]
          exact hC_conv hu' hv' (by norm_num) (by norm_num) (by norm_num)
        rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv,
            Set.indicator_of_mem h_mid_in_C]
        -- Reduce to Pi log-concave at half power.
        change (∏ i, gaussianPDF 0 1 (u i)) ^ ((1:ℝ)/2)
             * (∏ i, gaussianPDF 0 1 (v i)) ^ ((1:ℝ)/2)
             ≤ ∏ i, gaussianPDF 0 1 (((1/2 : ℝ) • u + (1/2 : ℝ) • v) i)
        -- Convert the midpoint per-coord to `(u i + v i) / 2`.
        have h_per_i : ∀ i : ι, ((1/2:ℝ) • u + (1/2:ℝ) • v) i = (u i + v i) / 2 := by
          intro i; simp [Pi.smul_apply, Pi.add_apply]; ring
        simp only [h_per_i]
        exact gaussianPDF_pi_geom_mean_le u v
      · rw [Set.indicator_of_notMem hv, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2),
            mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hu, ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2),
          zero_mul]
      exact zero_le
  -- Normalise `1 - 1/2 = 1/2` in `h_PL`.
  simp only [show (1 : ℝ) - 1/2 = 1/2 from by norm_num] at h_PL
  -- Convert integrals back to measures.
  rw [← h_ν_set A_plus hA_plus_meas, ← h_ν_set A_minus hA_minus_meas,
      ← h_ν_set C hC_meas] at h_PL
  -- Symmetry: ν A_minus = ν A_plus.
  have h_symm : ν A_minus = ν A_plus := by
    -- Use `pi_gaussianReal_neg_invariant`: for measurable A, ν A = ν (-A).
    -- A_minus = -A_plus (using C symmetric).
    have h_neg : Measure.map (fun x : ι → ℝ => -x) ν = ν :=
      pi_gaussianReal_neg_invariant
    have h_neg_apply : ν A_minus = ν ((fun x : ι → ℝ => -x) ⁻¹' A_minus) := by
      conv_lhs => rw [← h_neg]
      rw [Measure.map_apply measurable_neg hA_minus_meas]
    rw [h_neg_apply]
    -- (fun x => -x) ⁻¹' A_minus = {x | -x ∈ A_minus} = {x | -x - y ∈ C}
    --   = {x | -(x + y) ∈ C} = {x | x + y ∈ C} = A_plus  (using C symmetric)
    congr 1
    ext x
    constructor
    · intro hx
      have : -x - y ∈ C := hx
      have h_neg_in : -(x + y) ∈ C := by rw [neg_add]; exact this
      have : x + y ∈ C := by
        have := hC_symm _ h_neg_in
        rwa [neg_neg] at this
      exact this
    · intro hx
      have hxy : x + y ∈ C := hx
      have h_neg_in : -(x + y) ∈ C := hC_symm _ hxy
      change -x - y ∈ C
      rw [show (-x - y : ι → ℝ) = -(x + y) from by abel]
      exact h_neg_in
  rw [h_symm] at h_PL
  -- ν(A_plus)^{1/2} * ν(A_plus)^{1/2} = ν(A_plus).
  have h_sq : ν A_plus ^ ((1:ℝ)/2) * ν A_plus ^ ((1:ℝ)/2) = ν A_plus := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2),
        show ((1:ℝ)/2 + 1/2) = 1 from by norm_num, ENNReal.rpow_one]
  rw [h_sq] at h_PL
  exact h_PL

omit [DecidableEq ι] in
/-- **Anderson's lemma — continuous-linear-image form.**

For a continuous linear map `L : (ι → ℝ) →L[ℝ] V`, the pushforward of the Pi
standard Gaussian by `u ↦ L u` is `-`-invariant for any symmetric convex `C`:
the shifted measure satisfies `ν{u | L u + y ∈ C} ≤ ν{u | L u ∈ C}`.

This is a Lean-internal generalisation of `anderson_lemma_set_pi` to a
linear image (`T_S` need not be invertible). Same proof shape — PL at the
midpoint plus the symmetry `ν₀(A_minus) = ν₀(A_plus)` via linearity of `L`
and `pi_gaussianReal_neg_invariant`. -/
theorem anderson_lemma_image_pi
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (L : (ι → ℝ) →L[ℝ] V)
    {C : Set V}
    (hC_meas : MeasurableSet C)
    (hC_conv : Convex ℝ C)
    (hC_symm : ∀ x ∈ C, -x ∈ C)
    (y : V) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) {u | L u + y ∈ C} ≤
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) {u | L u ∈ C} := by
  set ν := Measure.pi (fun _ : ι => gaussianReal 0 1) with hν_def
  let ρ : (ι → ℝ) → ℝ≥0∞ := fun x => ∏ i, gaussianPDF 0 1 (x i)
  have hρ_meas : Measurable ρ :=
    Finset.measurable_prod _ fun i _ =>
      (measurable_gaussianPDF 0 1).comp (measurable_pi_apply i)
  have h_ν_eq : ν = (volume : Measure (ι → ℝ)).withDensity ρ :=
    pi_gaussianReal_eq_withDensity
  let A_plus : Set (ι → ℝ) := {u | L u + y ∈ C}
  let A_minus : Set (ι → ℝ) := {u | L u - y ∈ C}
  let A_target : Set (ι → ℝ) := {u | L u ∈ C}
  have hL_meas : Measurable L := L.continuous.measurable
  have hA_plus_meas : MeasurableSet A_plus := (hL_meas.add_const y) hC_meas
  have hA_minus_meas : MeasurableSet A_minus := (hL_meas.sub_const y) hC_meas
  have hA_target_meas : MeasurableSet A_target := hL_meas hC_meas
  have h_ν_set : ∀ A : Set (ι → ℝ), MeasurableSet A →
      ν A = ∫⁻ x, A.indicator ρ x ∂volume := fun A hA => by
    rw [h_ν_eq, withDensity_apply ρ hA, ← lintegral_indicator hA]
  have h_PL : (∫⁻ x, A_plus.indicator ρ x ∂volume) ^ ((1 : ℝ) / 2)
        * (∫⁻ x, A_minus.indicator ρ x ∂volume) ^ (1 - (1 : ℝ) / 2)
      ≤ ∫⁻ z, A_target.indicator ρ z ∂volume := by
    refine prekopaLeindler
      (hρ_meas.indicator hA_plus_meas)
      (hρ_meas.indicator hA_minus_meas)
      (hρ_meas.indicator hA_target_meas)
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1) ?_
    intro u v
    have h_one_minus_half : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    simp only [h_one_minus_half]
    by_cases hu : u ∈ A_plus
    · by_cases hv : v ∈ A_minus
      · have hu' : L u + y ∈ C := hu
        have hv' : L v - y ∈ C := hv
        have h_mid_in_A_target : (1/2 : ℝ) • u + (1/2 : ℝ) • v ∈ A_target := by
          change L ((1/2 : ℝ) • u + (1/2 : ℝ) • v) ∈ C
          rw [map_add, L.map_smul, L.map_smul]
          have h_combine : (1/2 : ℝ) • L u + (1/2 : ℝ) • L v
              = (1/2 : ℝ) • (L u + y) + (1/2 : ℝ) • (L v - y) := by
            rw [smul_add, smul_sub]; abel
          rw [h_combine]
          exact hC_conv hu' hv' (by norm_num) (by norm_num) (by norm_num)
        rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv,
            Set.indicator_of_mem h_mid_in_A_target]
        change (∏ i, gaussianPDF 0 1 (u i)) ^ ((1:ℝ)/2)
             * (∏ i, gaussianPDF 0 1 (v i)) ^ ((1:ℝ)/2)
             ≤ ∏ i, gaussianPDF 0 1 (((1/2 : ℝ) • u + (1/2 : ℝ) • v) i)
        have h_per_i : ∀ i : ι, ((1/2:ℝ) • u + (1/2:ℝ) • v) i = (u i + v i) / 2 := by
          intro i; simp [Pi.smul_apply, Pi.add_apply]; ring
        simp only [h_per_i]
        exact gaussianPDF_pi_geom_mean_le u v
      · rw [Set.indicator_of_notMem hv,
            ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2),
            mul_zero]
        exact zero_le
    · rw [Set.indicator_of_notMem hu,
          ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1/2),
          zero_mul]
      exact zero_le
  simp only [show (1 : ℝ) - 1/2 = 1/2 from by norm_num] at h_PL
  rw [← h_ν_set A_plus hA_plus_meas, ← h_ν_set A_minus hA_minus_meas,
      ← h_ν_set A_target hA_target_meas] at h_PL
  have h_symm : ν A_minus = ν A_plus := by
    have h_neg : Measure.map (fun u : ι → ℝ => -u) ν = ν :=
      pi_gaussianReal_neg_invariant
    have h_neg_apply : ν A_minus = ν ((fun u : ι → ℝ => -u) ⁻¹' A_minus) := by
      conv_lhs => rw [← h_neg]
      rw [Measure.map_apply measurable_neg hA_minus_meas]
    rw [h_neg_apply]
    congr 1
    ext u
    constructor
    · intro hu
      have h0 : L (-u) - y ∈ C := hu
      have h_neg_in : -(L u + y) ∈ C := by
        rw [show -(L u + y) = L (-u) - y from by rw [map_neg]; abel]
        exact h0
      have h_pos : L u + y ∈ C := by
        have := hC_symm _ h_neg_in
        rwa [neg_neg] at this
      exact h_pos
    · intro hu
      have huy : L u + y ∈ C := hu
      have h_neg_in : -(L u + y) ∈ C := hC_symm _ huy
      change L (-u) - y ∈ C
      rw [show L (-u) - y = -(L u + y) from by rw [map_neg]; abel]
      exact h_neg_in
  rw [h_symm] at h_PL
  have h_sq : ν A_plus ^ ((1:ℝ)/2) * ν A_plus ^ ((1:ℝ)/2) = ν A_plus := by
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (0:ℝ) ≤ 1/2),
        show ((1:ℝ)/2 + 1/2) = 1 from by norm_num, ENNReal.rpow_one]
  rw [h_sq] at h_PL
  exact h_PL

omit [DecidableEq ι] in
/-- **Anderson's lemma — `stdGaussian` form on `EuclideanSpace`.**

For the standard Gaussian measure `stdGaussian (EuclideanSpace ℝ ι)` and any
convex symmetric measurable set `C ⊂ EuclideanSpace ℝ ι`, the shifted measure
satisfies `ν(C - y) ≤ ν(C)`.

This bridges `anderson_lemma_set_pi` (on `ι → ℝ` with the Pi product Gaussian)
to the `EuclideanSpace ℝ ι` setting, via `map_pi_eq_stdGaussian`. Used by
`anderson_lemma_set` (the multivariate form) as the second transport stage. -/
theorem anderson_lemma_set_stdGaussian
    {C : Set (EuclideanSpace ℝ ι)} (hC_meas : MeasurableSet C)
    (hC_conv : Convex ℝ C) (hC_symm : ∀ x ∈ C, -x ∈ C)
    (y : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)) {x | x + y ∈ C} ≤
      (stdGaussian (EuclideanSpace ℝ ι)) C := by
  -- `stdGaussian E = (Measure.pi (gaussianReal 0 1)).map (toLp 2)` via Mathlib.
  -- Pull both sides back to Pi, apply `anderson_lemma_set_pi` to the preimaged
  -- set and shift.
  rw [← map_pi_eq_stdGaussian]
  set e : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  -- Cast `(toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)` is the underlying function of `e`.
  have h_toLp_eq : (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) = e := rfl
  rw [h_toLp_eq]
  have h_e_meas : Measurable e := e.toLinearMap.continuous_of_finiteDimensional.measurable
  -- Compute preimages.
  have h_super_meas : MeasurableSet {x : EuclideanSpace ℝ ι | x + y ∈ C} :=
    (measurable_id.add_const y) hC_meas
  rw [Measure.map_apply h_e_meas h_super_meas, Measure.map_apply h_e_meas hC_meas]
  -- `e ⁻¹' {x | x + y ∈ C} = {u | u + e.symm y ∈ e ⁻¹' C}` via linear bijection.
  have h_pre_eq : (e : (ι → ℝ) → EuclideanSpace ℝ ι) ⁻¹' {x | x + y ∈ C}
      = {u | u + e.symm y ∈ e ⁻¹' C} := by
    ext u
    change e u + y ∈ C ↔ e (u + e.symm y) ∈ C
    rw [map_add, e.apply_symm_apply]
  rw [h_pre_eq]
  -- Apply `anderson_lemma_set_pi` to the preimaged set.
  refine anderson_lemma_set_pi ?_ ?_ ?_ _
  · exact h_e_meas hC_meas
  · exact hC_conv.linear_preimage e.toLinearMap
  · intro u hu
    -- u ∈ e ⁻¹' C means e u ∈ C; want -u ∈ e ⁻¹' C, i.e., e (-u) ∈ C.
    -- e (-u) = -(e u) by linearity; -(e u) ∈ C by hC_symm.
    rw [Set.mem_preimage, map_neg]
    exact hC_symm _ hu

/-- **Anderson's lemma — set form for PosDef covariance.**

This is the technique-driven sub-form: the proof goes through PL + matrix square
root invertibility, which strictly needs `S.PosDef`. The vdV-canonical
`anderson_lemma_set` (allowing `S.PosSemidef`) is derived from this.

For centered multivariate Gaussian `multivariateGaussian 0 S`
(`S` **positive definite**) and any convex symmetric measurable set `C`,
the measure of the shifted set `C - y` (= `{x | x + y ∈ C}`) is at most
the measure of `C` itself:

$$\nu(C - y) \le \nu(C), \qquad \nu = N(0, S).$$

**Proof sketch**: reduce to `anderson_lemma_set_pi` via two transports.

* `multivariateGaussian 0 S = stdGaussian (EuclideanSpace ℝ ι) .map S^{1/2}`
  (by definition of `multivariateGaussian` as a pushforward through the
  matrix square root). When `S.PosDef`, `S^{1/2}` (= `toEuclideanCLM (CFC.sqrt S)`)
  is invertible; the preimage of a convex symmetric set under the (linear)
  `S^{1/2}` is again convex symmetric, so set-form Anderson on `stdGaussian`
  at the preimaged set + preimaged shift gives the inequality.
* `stdGaussian (EuclideanSpace ℝ ι) = (Measure.pi (gaussianReal 0 1)).map (toLp 2)`
  by `map_pi_eq_stdGaussian`. Bridge to `anderson_lemma_set_pi`.

**Why `PosDef` not `PosSemidef`**: the proof technique (PL via density)
strictly needs an invertible square root for the change of variables. The
classical statement holds for PSD too (Anderson's inequality is about
centered symmetric log-concave measures); `anderson_lemma_set` recovers the
full PSD statement from this PosDef form. -/
theorem anderson_lemma_set_posDef
    {S : Matrix ι ι ℝ} (hS : S.PosDef)
    {C : Set (EuclideanSpace ℝ ι)} (hC_meas : MeasurableSet C)
    (hC_conv : Convex ℝ C) (hC_symm : ∀ x ∈ C, -x ∈ C)
    (y : EuclideanSpace ℝ ι) :
    (multivariateGaussian 0 S) {x | x + y ∈ C} ≤ (multivariateGaussian 0 S) C := by
  -- From `S.PosDef`, the matrix square root `CFC.sqrt S` is also positive
  -- definite (`Matrix.PosDef.posDef_sqrt`), hence invertible.
  have h_sqrt_unit : IsUnit (CFC.sqrt S) := hS.isStrictlyPositive.sqrt.isUnit
  -- Lift to the corresponding CLM: `toEuclideanCLM` is a star algebra equiv
  -- (in particular a `MulEquivClass`), so it transfers `IsUnit`.
  have h_T_unit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) :=
    (MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι))).mpr h_sqrt_unit
  -- From `IsUnit T`, build the `ContinuousLinearEquiv` so we can invert.
  let T_cle : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι :=
    ContinuousLinearEquiv.ofUnit h_T_unit.unit
  have h_T_meas : Measurable (T_cle : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :=
    T_cle.toContinuousLinearMap.continuous.measurable
  -- `multivariateGaussian 0 S = stdGaussian.map T_cle` by definition.
  have h_mvg : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map T_cle := by
    rw [multivariateGaussian]
    congr 1
    funext x
    rw [zero_add]
    rfl
  rw [h_mvg]
  -- Pull both measures back to stdGaussian via `Measure.map_apply`.
  have h_super_meas : MeasurableSet {x : EuclideanSpace ℝ ι | x + y ∈ C} :=
    (measurable_id.add_const y) hC_meas
  rw [Measure.map_apply h_T_meas h_super_meas]
  rw [Measure.map_apply h_T_meas hC_meas]
  -- `T_cle ⁻¹' {x | x + y ∈ C} = {u | u + T_cle.symm y ∈ T_cle ⁻¹' C}` (linear bijection).
  have h_pre_eq : (T_cle : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) ⁻¹' {x | x + y ∈ C}
      = {u | u + T_cle.symm y ∈ (T_cle : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) ⁻¹' C} := by
    ext u
    change T_cle u + y ∈ C ↔ T_cle (u + T_cle.symm y) ∈ C
    rw [map_add, T_cle.apply_symm_apply]
  rw [h_pre_eq]
  -- Apply `anderson_lemma_set_stdGaussian` to the preimaged set + shift.
  refine anderson_lemma_set_stdGaussian ?_ ?_ ?_ _
  · exact h_T_meas hC_meas
  · exact hC_conv.linear_preimage T_cle.toLinearMap
  · intro u hu
    rw [Set.mem_preimage, map_neg]
    exact hC_symm _ hu

/-- **Anderson's lemma — set form** (vdV-canonical, `S.PosSemidef`).

For centered multivariate Gaussian `multivariateGaussian 0 S` (`S` positive
**semi**definite — the original vdV statement) and any convex symmetric measurable
set `C`, the measure of the shifted set `C - y` is at most the measure of `C`:

$$\nu(C - y) \le \nu(C), \qquad \nu = N(0, S).$$

**Proof** (by cases on `S`):

* Case `S = 0`: `multivariateGaussian 0 0 = Dirac 0`
  (`multivariateGaussian_zero_cov`). For convex symmetric nonempty `C`, the
  midpoint `0 = midpoint y (-y)` belongs to `C` (`Convex.midpoint_mem` +
  `midpoint_self_neg`), so `Dirac 0 C = 1` and the LHS is bounded by 1
  (probability measure). Empty `C` is trivial.

* Case `S.PosDef`: direct application of `anderson_lemma_set_posDef`.

* Case `S.PosSemidef` non-PosDef and `S ≠ 0`: via `_pl_anderson_pi_general`.
  The PL argument only requires the pullback
  `Φ := T_clm ∘ toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι` to be **linear**
  (Minkowski-mean preservation), not invertible, so the same template as
  `anderson_lemma_set_posDef` works modulo replacing the invertible CLE with a
  non-injective CLM `T_clm := toEuclideanCLM (sqrt S)`. -/
theorem anderson_lemma_set
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {C : Set (EuclideanSpace ℝ ι)} (hC_meas : MeasurableSet C)
    (hC_conv : Convex ℝ C) (hC_symm : ∀ x ∈ C, -x ∈ C)
    (y : EuclideanSpace ℝ ι) :
    (multivariateGaussian 0 S) {x | x + y ∈ C} ≤ (multivariateGaussian 0 S) C := by
  by_cases hS_zero : S = 0
  · -- **Case `S = 0`**: `mvg 0 0 = Dirac 0`. If `C` empty both sides 0;
    -- if `C` nonempty, `0 ∈ C` (midpoint), so RHS `= 1` and LHS `≤ 1` (probability).
    subst hS_zero
    rw [multivariateGaussian_zero_cov]
    rcases C.eq_empty_or_nonempty with h_empty | ⟨z, hz⟩
    · simp [h_empty]
    · -- `0 = midpoint z (-z) ∈ C` since `z, -z ∈ C` and `C` convex.
      have h_neg : -z ∈ C := hC_symm z hz
      have h_zero : (0 : EuclideanSpace ℝ ι) ∈ C := by
        have := hC_conv.midpoint_mem hz h_neg
        rwa [midpoint_self_neg] at this
      rw [MeasureTheory.Measure.dirac_apply_of_mem h_zero]
      exact MeasureTheory.prob_le_one
  · by_cases h_posDef : S.PosDef
    · -- **Case `S.PosDef`**: direct application of the unconditional PosDef form.
      exact anderson_lemma_set_posDef h_posDef hC_meas hC_conv hC_symm y
    · -- **Case `S ≠ 0` singular PSD**: PL on `Pi gaussianReal` via the linear
      -- pullback `Φ := T_clm ∘ toLp 2`, where `T_clm = toEuclideanCLM (sqrt S)`.
      -- `T_clm` is **not** invertible here, but the PL argument only requires
      -- linearity (preserves Minkowski mean), so `Φ` works the same way as in
      -- the PosDef case modulo the lack of a CLE.
      set T_clm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
        Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hT_clm_def
      let Φ : (ι → ℝ) → EuclideanSpace ℝ ι :=
        fun u => T_clm (WithLp.toLp 2 u)
      have h_toLp_meas : Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) :=
        (PiLp.continuous_toLp 2 _).measurable
      have hΦ_meas : Measurable Φ := T_clm.continuous.measurable.comp h_toLp_meas
      have hΦ_smul : ∀ (s : ℝ) (u : ι → ℝ), Φ (s • u) = s • Φ u := fun s u => by
        change T_clm (WithLp.toLp 2 (s • u)) = s • T_clm (WithLp.toLp 2 u)
        rw [show (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) (s • u)
              = s • (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) u from rfl,
            T_clm.map_smul]
      have hΦ_add : ∀ (u v : ι → ℝ), Φ (u + v) = Φ u + Φ v := fun u v => by
        change T_clm (WithLp.toLp 2 (u + v))
            = T_clm (WithLp.toLp 2 u) + T_clm (WithLp.toLp 2 v)
        rw [show (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) (u + v)
              = (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) u
                + (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) v from rfl,
            T_clm.map_add]
      -- `mvg 0 S = (Pi gaussianReal 0 1).map Φ`.
      have h_mvg_eq : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
          = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map Φ := by
        rw [multivariateGaussian]
        rw [show (fun x : EuclideanSpace ℝ ι => (0 : EuclideanSpace ℝ ι) + T_clm x)
            = (T_clm : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) from
          funext fun x => zero_add (T_clm x)]
        rw [← map_pi_eq_stdGaussian,
            Measure.map_map T_clm.continuous.measurable h_toLp_meas]
        rfl
      rw [h_mvg_eq]
      have h_super_meas : MeasurableSet {x : EuclideanSpace ℝ ι | x + y ∈ C} :=
        (measurable_id.add_const y) hC_meas
      rw [Measure.map_apply hΦ_meas h_super_meas, Measure.map_apply hΦ_meas hC_meas]
      -- Set up `A_+`, `A_-`, `K` for `_pl_anderson_pi_general`.
      set A_plus : Set (ι → ℝ) := Φ ⁻¹' {x | x + y ∈ C} with hA_plus_def
      set A_minus : Set (ι → ℝ) := Φ ⁻¹' {x | x - y ∈ C} with hA_minus_def
      set K : Set (ι → ℝ) := Φ ⁻¹' C with hK_def
      have hA_plus_meas : MeasurableSet A_plus := hΦ_meas h_super_meas
      have hA_minus_meas : MeasurableSet A_minus :=
        hΦ_meas ((measurable_id.sub_const y) hC_meas)
      have hK_meas : MeasurableSet K := hΦ_meas hC_meas
      -- Mean condition: `Φ((1/2)u + (1/2)v) = (1/2)Φu + (1/2)Φv ∈ C` by convexity
      -- of `C` (using `Φu + y, Φv - y ∈ C`).
      have h_mean : ∀ u ∈ A_plus, ∀ v ∈ A_minus,
          ((1/2:ℝ) • u + (1/2:ℝ) • v) ∈ K := by
        intro u hu v hv
        have hu' : Φ u + y ∈ C := hu
        have hv' : Φ v - y ∈ C := hv
        change Φ ((1/2:ℝ) • u + (1/2:ℝ) • v) ∈ C
        rw [hΦ_add, hΦ_smul, hΦ_smul]
        have h_combine : (1/2 : ℝ) • Φ u + (1/2 : ℝ) • Φ v
            = (1/2 : ℝ) • (Φ u + y) + (1/2 : ℝ) • (Φ v - y) := by
          rw [smul_add, smul_sub]; abel
        rw [h_combine]
        exact hC_conv hu' hv' (by norm_num) (by norm_num) (by norm_num)
      -- Symmetry: `A_- = -A_+` (via `Φ` linear + `C` symmetric), then
      -- `pi gaussianReal` symmetric.
      have h_symm : (Measure.pi (fun _ : ι => gaussianReal 0 1)) A_minus =
                    (Measure.pi (fun _ : ι => gaussianReal 0 1)) A_plus := by
        have h_neg_inv : Measure.map (fun u : ι → ℝ => -u)
            (Measure.pi (fun _ : ι => gaussianReal 0 1)) =
            Measure.pi (fun _ : ι => gaussianReal 0 1) :=
          pi_gaussianReal_neg_invariant
        have h_apply_neg : (Measure.pi (fun _ : ι => gaussianReal 0 1)) A_minus =
            (Measure.pi (fun _ : ι => gaussianReal 0 1))
              ((fun u : ι → ℝ => -u) ⁻¹' A_minus) := by
          conv_lhs => rw [← h_neg_inv]
          exact Measure.map_apply measurable_neg hA_minus_meas
        rw [h_apply_neg]
        congr 1
        ext u
        have hΦ_neg : Φ (-u) = -Φ u := by
          rw [show (-u : ι → ℝ) = (-1:ℝ) • u from by simp]
          rw [hΦ_smul]; simp
        constructor
        · intro hu
          have h1 : Φ (-u) - y ∈ C := hu
          rw [hΦ_neg] at h1
          have h2 : -(Φ u + y) ∈ C := by rw [neg_add]; exact h1
          have h3 : Φ u + y ∈ C := by
            have := hC_symm _ h2
            rwa [neg_neg] at this
          exact h3
        · intro hu
          have h1 : Φ u + y ∈ C := hu
          change Φ (-u) - y ∈ C
          rw [hΦ_neg]
          have h2 : -(Φ u + y) ∈ C := hC_symm _ h1
          rw [show -Φ u - y = -(Φ u + y) from by abel]
          exact h2
      exact _pl_anderson_pi_general hA_plus_meas hA_minus_meas hK_meas h_mean h_symm

/-- **Anderson's lemma — loss form.**

For bowl-shaped `L` and centered Gaussian, integrating against the shifted
loss $L(\cdot + y)$ is no smaller than integrating against $L$ itself:

$$\int L \, d\nu \le \int L(x + y) \, d\nu(x), \qquad \nu = N(0, S).$$

**Proof**: convert the RHS to an integral against the pushforward
`ν.map (·+y)` via `MeasureTheory.lintegral_map`. Then apply
`lintegral_mono_of_meas_lt_le`: the required level-set inequality
`ν{c < L} ≤ (ν.map (·+y)){c < L}` follows from `anderson_lemma_set` applied
to the convex symmetric sublevel `{L ≤ c}` and complementing
(both measures are probability, so `μ Aᶜ = 1 - μ A`). -/
theorem anderson_lemma_loss
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {L : EuclideanSpace ℝ ι → ℝ≥0∞} (hL : BowlShaped L)
    (y : EuclideanSpace ℝ ι) :
    ∫⁻ x, L x ∂(multivariateGaussian 0 S) ≤
      ∫⁻ x, L (x + y) ∂(multivariateGaussian 0 S) := by
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) S with hν_def
  -- Convert RHS to an integral against the pushforward `ν.map (·+y)`.
  have h_add_meas : Measurable (fun x : EuclideanSpace ℝ ι => x + y) :=
    measurable_id.add_const y
  rw [show ∫⁻ x, L (x + y) ∂ν = ∫⁻ z, L z ∂(ν.map (fun x => x + y)) from
      (MeasureTheory.lintegral_map hL.measurable h_add_meas).symm]
  -- Apply level-set stochastic dominance with `ν` vs `ν.map (·+y)`.
  refine lintegral_mono_of_meas_lt_le hL.measurable (fun c => ?_)
  -- Goal: ν {c < L} ≤ (ν.map (·+y)) {c < L}.
  have h_super_meas : MeasurableSet {x : EuclideanSpace ℝ ι | c < L x} :=
    hL.measurable measurableSet_Ioi
  rw [Measure.map_apply h_add_meas h_super_meas]
  -- Convert {c < L} = {L ≤ c}ᶜ on both sides, then apply `anderson_lemma_set`.
  have h_compl : {x : EuclideanSpace ℝ ι | c < L x} = {x | L x ≤ c}ᶜ := by
    ext x; simp [not_le]
  rw [h_compl, Set.preimage_compl]
  -- Sublevel `{L ≤ c}` is convex symmetric by `BowlShaped`.
  have hC_meas : MeasurableSet {x : EuclideanSpace ℝ ι | L x ≤ c} :=
    hL.measurable measurableSet_Iic
  have hC_conv : Convex ℝ {x | L x ≤ c} := hL.convex_sublevel c
  have hC_symm : ∀ x ∈ {x : EuclideanSpace ℝ ι | L x ≤ c}, -x ∈ {x | L x ≤ c} := by
    intro x hx
    simp only [Set.mem_setOf_eq, hL.symm] at hx ⊢
    exact hx
  -- Pass to complements: `ν Aᶜ = 1 - ν A`, then apply monotonicity.
  -- `(·+y) ⁻¹' {L ≤ c} = {x | x+y ∈ {L ≤ c}}` by `rfl`; phrase `h_and` in
  -- preimage shape to match the goal after `prob_compl_eq_one_sub`.
  have h_and : ν ((fun x : EuclideanSpace ℝ ι => x + y) ⁻¹' {x | L x ≤ c})
      ≤ ν {x | L x ≤ c} :=
    anderson_lemma_set hS hC_meas hC_conv hC_symm y
  rw [prob_compl_eq_one_sub hC_meas, prob_compl_eq_one_sub (h_add_meas hC_meas)]
  exact tsub_le_tsub_left h_and 1

/-- **Anderson's lemma — translation form** (specialized variant of `anderson_lemma_loss`).

For bowl-shaped `L` and centered Gaussian `N(0, S)`, the integral of `L` against
the centered Gaussian is no larger than the integral of `c ↦ L(c - z)` for any
fixed `c`:

$$\int L(z) \, d N(0, S)(z) \le \int L(c - z) \, d N(0, S)(z).$$

This is the "shift-by-`c`" form consumed by
`avgRisk_gaussianShift_ge_bayesRiskAtTau`: for the posterior-residual integrand
`L(c - ψDotMat g)` with `c := y - ψDotMat (Σ_τ J x)`, this gives
`bayesRiskAtTau ≤ ∫ L(c - z) ∂N(0, ψDotMat·Σ_τ·ψDotMatᵀ)`.

**Proof**: bowl-symmetry `L(c - z) = L(z - c)` (since `L(-w) = L(w)`), then
`L(z - c) = L(z + (-c))`, then `anderson_lemma_loss` with shift `-c`. -/
theorem lintegral_loss_translated_ge
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {L : EuclideanSpace ℝ ι → ℝ≥0∞} (hL : BowlShaped L)
    (c : EuclideanSpace ℝ ι) :
    ∫⁻ z, L z ∂(multivariateGaussian 0 S) ≤
      ∫⁻ z, L (c - z) ∂(multivariateGaussian 0 S) := by
  -- Bowl-symmetry: `L(c - z) = L(-(z - c)) = L(z - c)`. Then `L(z - c) = L(z + (-c))`.
  have h_rewrite : ∫⁻ z, L (c - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S)
      = ∫⁻ z, L (z + (-c)) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) := by
    refine lintegral_congr fun z => ?_
    have h_neg : c - z = -(z - c) := by abel
    rw [h_neg, hL.symm, sub_eq_add_neg]
  rw [h_rewrite]
  exact anderson_lemma_loss hS hL (-c)

/-- **Anderson's lemma — independent shift form.**

For bowl-shaped `L`, centered Gaussian `G ~ N(0, S)`, and any independent
random variable `Y` (encoded as a probability measure on the same space),

$$\mathbb E\, L(G + Y) \;\ge\; \mathbb E\, L(G).$$

Proof: unfold convolution via `Measure.lintegral_conv` to get
`∫⁻ z, L z ∂(N ∗ Y) = ∫⁻ x, ∫⁻ y, L (x + y) ∂Y ∂N`, then `lintegral_lintegral_swap`
to put `Y` outside. For each fixed `y`, `anderson_lemma_loss` gives the
fibre-wise inequality `∫⁻ x, L x ∂N ≤ ∫⁻ x, L (x + y) ∂N`; integrate over
`Y` and use that `Y` is a probability measure. -/
theorem anderson_lemma_independent
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    {L : EuclideanSpace ℝ ι → ℝ≥0∞} (hL : BowlShaped L)
    (Y : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure Y] :
    ∫⁻ x, L x ∂(multivariateGaussian 0 S) ≤
      ∫⁻ z, L z ∂((multivariateGaussian 0 S) ∗ Y) := by
  set μ := multivariateGaussian (0 : EuclideanSpace ℝ ι) S with hμ
  -- Convolution-as-Fubini: ∫⁻ z L z ∂(μ ∗ Y) = ∫⁻ x ∫⁻ y, L (x+y) ∂Y ∂μ
  rw [Measure.lintegral_conv hL.measurable]
  -- Swap to put Y outside, μ inside (so we can apply anderson_lemma_loss).
  rw [lintegral_lintegral_swap]
  · -- ∫⁻ x L x ∂μ ≤ ∫⁻ y ∫⁻ x, L (x+y) ∂μ ∂Y
    calc ∫⁻ x, L x ∂μ
        = ∫⁻ _ : EuclideanSpace ℝ ι, ∫⁻ x, L x ∂μ ∂Y := by
            rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ y, ∫⁻ x, L (x + y) ∂μ ∂Y := by
            exact lintegral_mono (fun y => anderson_lemma_loss hS hL y)
  · -- Joint measurability of `(x, y) ↦ L (x + y)`.
    exact (hL.measurable.comp measurable_add).aemeasurable

/-- **PSD-monotone Anderson.**

For PSD `S₁ ≼ S₂` (i.e. `S₂ - S₁` is PSD) and bowl-shaped `L`,

$$\int L \, dN(0, S_1) \;\le\; \int L \, dN(0, S_2).$$

Proof: by `multivariateGaussian_conv_multivariateGaussian`,
$N(0, S_2) = N(0, S_1) \ast N(0, S_2 - S_1)$. Apply `anderson_lemma_independent`
with $Y = N(0, S_2 - S_1)$.

This is the Anderson form used in the flat-prior limit of the Gaussian-shift
Bayes risk. -/
theorem gaussian_lintegral_mono_of_psd_le
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosSemidef) (_hS₂ : S₂.PosSemidef)
    (h_le : (S₂ - S₁).PosSemidef)
    {L : EuclideanSpace ℝ ι → ℝ≥0∞} (hL : BowlShaped L) :
    ∫⁻ x, L x ∂(multivariateGaussian 0 S₁) ≤
      ∫⁻ x, L x ∂(multivariateGaussian 0 S₂) := by
  -- Rewrite the larger Gaussian as the convolution of the smaller with the
  -- difference, then cite anderson_lemma_independent.
  have h_conv : multivariateGaussian (0 : EuclideanSpace ℝ ι) S₂
      = multivariateGaussian 0 S₁ ∗ multivariateGaussian 0 (S₂ - S₁) := by
    rw [multivariateGaussian_conv_multivariateGaussian _ _ hS₁ h_le]
    congr 1
    · simp
    · abel
  rw [h_conv]
  exact anderson_lemma_independent hS₁ hL _

end AsymptoticStatistics
