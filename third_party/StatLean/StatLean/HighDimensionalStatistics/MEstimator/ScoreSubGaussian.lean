module
public import StatLean.HighDimensionalStatistics.MEstimator.GLMDefs
public import StatLean.HighDimensionalStatistics.ForMathlib.PsiTaylor
public import StatLean.ConcentrationInequalities.SubGaussian.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.IntegrableExpMul

@[expose] public section

/-!
# Sub-Gaussianity of the GLM score

The probabilistic core underlying the high-dimensional GLM corollaries. Consider a generalized
linear model in canonical (exponential-family) form with cumulant function $\psi$, design matrix
$X$, and true parameter $\theta^\star$, writing $\eta_i = \langle x_i, \theta^\star\rangle$ for the
$i$-th linear predictor. Under
  - (G1) **column normalization**: $\tfrac1n\sum_{i=1}^n x_{ij}^2 \le C^2$ for every column $j$, and
  - (G2) the **bounded-curvature exponential family**: $0 \le \psi'' \le B^2$,

each coordinate of the score (negative log-likelihood gradient) evaluated at the truth,
$$ \bigl(\nabla L_n(\theta^\star)\bigr)_j \;=\; \frac1n\sum_{i=1}^n \bigl(\psi'(\eta_i) - y_i\bigr)\,x_{ij}, $$
is a centered sub-Gaussian random variable with variance proxy $\le B^2 C^2 / n$.

This is the deviation bound for the empirical score that drives the choice of regularization
parameter $\lambda_n \asymp B C\sqrt{(\log d)/n}$ in the GLM Lasso/M-estimator rate. The mean-zero
property uses $\mathbb{E}[y_i] = \psi'(\eta_i)$, the standard exponential-family mean identity.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019, Chapter 9 (Decomposability and restricted strong convexity),
within the proof of Corollary 9.26 (p. 288). Conditions (G1)/(G2) and the per-term score
$V_{ij} = (\psi'(\eta_i) - y_i)\,x_{ij}$ follow the book's GLM setup. The variance proxy stated here,
$B^2 C^2/n$, is the form provable from these hypotheses; the book quotes the corresponding
sub-Gaussian tail with the same $B^2 C^2$ scale.

**Proof formalization notes.** The per-term variable $V_{ij} = (\psi'(\eta_i) - y_i)\,x_{ij}$ has MGF
$\exp\bigl(\psi(\eta_i + s) - \psi(\eta_i) - s\,\psi'(\eta_i)\bigr)$ with $s = -t\,x_{ij}$, obtained from
the constitutive `hmgf` identity of the exponential family. `psi_taylor_upper` (Taylor remainder with
$\psi'' \le B^2$) bounds this by $\exp(B^2 x_{ij}^2 t^2 / 2)$, so $V_{ij}$ is centered sub-Gaussian
with proxy $B^2 x_{ij}^2$. Summing over the independent observations $i$ and rescaling by $1/n$
(reusing the `Lasso/RandomNoise.lean` `colInner_isSubGaussian` pattern) and applying (G1) gives the
final proxy $B^2 C^2 / n$. Mean-zero of each term comes from $\mathbb{E}[y_i] = \psi'(\eta_i)$, derived
here as the derivative of the MGF at $0$.

**Bibliographic comments.** High-dimensional analysis of the GLM Lasso originates with
S. A. van de Geer, "High-dimensional generalized linear models and the lasso," *The Annals of
Statistics* **36**(2), 614–645 (2008), which established prediction/estimation oracle inequalities
for $\ell_1$-penalized GLMs. The unified treatment via decomposable regularizers and restricted
strong convexity — the framework Wainwright's Chapter 9 follows — is due to S. Negahban,
P. Ravikumar, M. J. Wainwright, and B. Yu, "A unified framework for high-dimensional analysis of
$M$-estimators with decomposable regularizers," *Statistical Science* **27**(4), 538–557 (2012).
The sub-Gaussian score deviation bound formalized here is a standard ingredient of these analyses
(the empirical-process / concentration step controlling $\nabla L_n(\theta^\star)$); it is not a
separately named theorem but the concentration sub-step of the GLM corollary.
-/

namespace StatLean.HighDimensionalStatistics.MEstimator

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open StatLean.ConcentrationInequalities

variable {n d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Integrability of `exp(s·yᵢ)` for every `s`, derived from the constitutive MGF identity:
if `exp(s·yᵢ)` were not integrable, the MGF would be the junk value `0` (`mgf_undef`), contradicting
`M.hmgf i s = exp(…) > 0`. -/
private lemma y_exp_integrable (M : GLMExpFamily n d μ) (i : Fin n) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * M.y i ω)) μ := by
  by_contra hni
  have h0 := mgf_undef hni
  rw [M.hmgf i s] at h0
  exact (Real.exp_pos _).ne' h0

/-- The set of exponents at which `exp(t·yᵢ)` is integrable is all of `ℝ` (from `y_exp_integrable`),
so `0` lies in its interior — the hypothesis needed for `deriv_mgf_zero` / integrability of `yᵢ`. -/
private lemma y_integrableExpSet_univ (M : GLMExpFamily n d μ) (i : Fin n) :
    integrableExpSet (M.y i) μ = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact y_exp_integrable M i t

/-- The mean function identity `E[yᵢ] = ψ'(ηᵢ)`. The mean is the derivative of the MGF at `0`
(`deriv_mgf_zero`); the constitutive `hmgf` gives `mgf yᵢ = exp(ψ(ηᵢ+·) − ψ(ηᵢ))`, whose derivative
at `0` is `ψ'(ηᵢ)`. -/
private lemma y_mean (M : GLMExpFamily n d μ) (i : Fin n) :
    ∫ ω, M.y i ω ∂μ = M.ψ' (linPred M.X M.θstar i) := by
  set η := linPred M.X M.θstar i with hη
  have hmem : (0 : ℝ) ∈ interior (integrableExpSet (M.y i) μ) := by
    rw [y_integrableExpSet_univ M i, interior_univ]; exact Set.mem_univ 0
  rw [← deriv_mgf_zero hmem]
  have hmgf_eq : mgf (M.y i) μ = fun s => Real.exp (M.ψ (η + s) - M.ψ η) := by
    funext s; rw [M.hmgf i s, hη]
  rw [hmgf_eq]
  have hinner : HasDerivAt (fun s => M.ψ (η + s) - M.ψ η) (M.ψ' η) 0 := by
    have h1 : HasDerivAt (fun s => M.ψ (η + s)) (M.ψ' η) 0 := by
      have := (M.hψ' (η + 0)).comp 0 ((hasDerivAt_id 0).const_add η)
      simpa using! this
    simpa using h1.sub_const (M.ψ η)
  have hderiv : HasDerivAt (fun s => Real.exp (M.ψ (η + s) - M.ψ η)) (M.ψ' η) 0 := by
    simpa using hinner.exp
  exact hderiv.deriv

/-- The per-term score variable `Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is centered sub-Gaussian with proxy
`B²·xᵢⱼ²`. Derived from the constitutive MGF identity (`M.hmgf`) and `psi_taylor_upper`:
`mgf Vᵢⱼ μ t = exp(ψ(ηᵢ + (−t·xᵢⱼ)) − ψ(ηᵢ) − (−t·xᵢⱼ)·ψ'(ηᵢ)) ≤ exp(B²·xᵢⱼ²·t²/2)`. -/
theorem score_term_hasSubgaussianMGF (M : GLMExpFamily n d μ) (i : Fin n) (j : Fin d) :
    HasSubgaussianMGF (fun ω => (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j)
      ⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ μ := by
  set η := linPred M.X M.θstar i with hη
  set a := M.X i j with ha
  refine ⟨?_, ?_⟩
  · -- integrable_exp_mul
    intro t
    have heq : (fun ω => Real.exp (t * ((M.ψ' η - M.y i ω) * a)))
        = (fun ω => Real.exp (t * (a * M.ψ' η)) * Real.exp ((-a * t) * M.y i ω)) := by
      funext ω; rw [← Real.exp_add]; congr 1; ring
    rw [heq]
    exact (y_exp_integrable M i (-a * t)).const_mul _
  · -- mgf_le
    intro t
    have hmgfeq : mgf (fun ω => (M.ψ' η - M.y i ω) * a) μ t
        = Real.exp (M.ψ (η + (-a * t)) - M.ψ η - (-a * t) * M.ψ' η) := by
      have hfun : (fun ω => (M.ψ' η - M.y i ω) * a)
          = (fun ω => a * M.ψ' η + (-a) * M.y i ω) := by
        funext ω; ring
      rw [hfun, mgf_const_add, mgf_const_mul, M.hmgf i, ← hη, ← Real.exp_add]
      congr 1; ring
    rw [hmgfeq]
    change _ ≤ Real.exp (M.B ^ 2 * a ^ 2 * t ^ 2 / 2)
    apply Real.exp_le_exp.mpr
    calc M.ψ (η + (-a * t)) - M.ψ η - (-a * t) * M.ψ' η
        ≤ M.B ^ 2 / 2 * (-a * t) ^ 2 :=
          psi_taylor_upper M.ψ M.ψ' M.ψ'' M.B M.hψ' M.hψ'' M.hψ''_le η (-a * t)
      _ = M.B ^ 2 * a ^ 2 * t ^ 2 / 2 := by ring

/-- **GLM score coordinate sub-Gaussianity.** Under column normalization (G1, `IsColumnNormalized X C`)
and the GLM exp-family with `0 ≤ ψ'' ≤ B²` (G2, in `M`), the score coordinate
`scoreCoord M j = (1/n)∑ᵢ (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is sub-Gaussian with variance proxy `B²C²/n`. -/
theorem score_coord_isSubGaussian (M : GLMExpFamily n d μ) [IsProbabilityMeasure μ]
    (C : ℝ) (hC : IsColumnNormalized M.X C) (hn : 0 < n) (j : Fin d) :
    IsSubGaussian (scoreCoord M j) ⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ μ := by
  set V : Fin n → Ω → ℝ :=
    fun i ω => (M.ψ' (linPred M.X M.θstar i) - M.y i ω) * M.X i j with hV
  -- Independence of the per-term family from `M.hindep`.
  have hV_indep : iIndepFun V μ :=
    M.hindep.comp (fun i x => (M.ψ' (linPred M.X M.θstar i) - x) * M.X i j)
      (fun i => (measurable_const.sub measurable_id).mul measurable_const)
  -- Each per-term variable is sub-Gaussian with proxy `B²xᵢⱼ²`.
  have hV_sg : ∀ i, HasSubgaussianMGF (V i) ⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ μ :=
    fun i => score_term_hasSubgaussianMGF M i j
  -- Sum over the independent terms.
  have hsum : HasSubgaussianMGF (fun ω => ∑ i, V i ω)
      (∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0)) μ :=
    HasSubgaussianMGF.sum_of_iIndepFun hV_indep (fun i _ => hV_sg i)
  -- Rescale by `1/n`.
  have hscaled := hsum.const_mul (1 / (n : ℝ))
  -- Mean-zero of each term (`E[yᵢ] = ψ'(ηᵢ)`) hence of the coordinate.
  have hVi : ∀ i, ∫ ω, V i ω ∂μ = 0 := by
    intro i
    have hyi : Integrable (M.y i) μ :=
      integrable_of_mem_interior_integrableExpSet (by
        rw [y_integrableExpSet_univ M i, interior_univ]; exact Set.mem_univ 0)
    have hrw : (fun ω => V i ω)
        = fun ω => M.ψ' (linPred M.X M.θstar i) * M.X i j - M.X i j * M.y i ω := by
      funext ω; simp only [hV]; ring
    rw [show (∫ ω, V i ω ∂μ)
          = ∫ ω, (M.ψ' (linPred M.X M.θstar i) * M.X i j - M.X i j * M.y i ω) ∂μ from by
        rw [hrw]]
    rw [integral_sub (integrable_const _) (hyi.const_mul _), integral_const,
        integral_const_mul, y_mean M i, probReal_univ, one_smul]
    ring
  have hmean : ∫ ω, scoreCoord M j ω ∂μ = 0 := by
    have hsc_eq : scoreCoord M j = fun ω => (1 / (n : ℝ)) * ∑ i, V i ω := by
      funext ω; simp only [scoreCoord, hV]
    simp only [hsc_eq]
    rw [integral_const_mul,
        integral_finset_sum Finset.univ (fun i _ => (hV_sg i).integrable),
        Finset.sum_congr rfl (fun i _ => hVi i), Finset.sum_const_zero, mul_zero]
  -- Proxy monotonicity: the rescaled proxy `(1/n²)∑ᵢ B²xᵢⱼ²` is `≤ B²C²/n` by (G1).
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hB2 : (0 : ℝ) ≤ M.B ^ 2 := sq_nonneg _
  -- Proxy bound in `ℝ≥0` (cast to `ℝ` and clear denominators).
  have hproxy : (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩
        * ∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0))
      ≤ (⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ : ℝ≥0) := by
    -- Bound the sum by `B²·(n·C²)` entirely within `ℝ≥0` (cast termwise via the sum coercion).
    have hreal : ∑ i, M.B ^ 2 * M.X i j ^ 2 ≤ M.B ^ 2 * ((n : ℝ) * C ^ 2) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hC j) hB2
    have hsum_le : (∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0))
        ≤ (⟨M.B ^ 2 * ((n : ℝ) * C ^ 2), by positivity⟩ : ℝ≥0) := by
      apply NNReal.coe_le_coe.mp
      change _ ≤ M.B ^ 2 * ((n : ℝ) * C ^ 2)
      refine le_trans (le_of_eq ?_) hreal
      exact (NNReal.coe_sum _ _).trans rfl
    calc (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩ : ℝ≥0)
            * ∑ i, (⟨M.B ^ 2 * M.X i j ^ 2, by positivity⟩ : ℝ≥0)
          ≤ (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩ : ℝ≥0)
            * ⟨M.B ^ 2 * ((n : ℝ) * C ^ 2), by positivity⟩ :=
            mul_le_mul_of_nonneg_left hsum_le (zero_le)
      _ = ⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ := by
            rw [show (⟨(1 / (n : ℝ)) ^ 2, by positivity⟩ : ℝ≥0)
                  * ⟨M.B ^ 2 * ((n : ℝ) * C ^ 2), by positivity⟩
                = ⟨(1 / (n : ℝ)) ^ 2 * (M.B ^ 2 * ((n : ℝ) * C ^ 2)), by positivity⟩ from rfl]
            apply NNReal.coe_injective
            change (1 / (n : ℝ)) ^ 2 * (M.B ^ 2 * ((n : ℝ) * C ^ 2)) = M.B ^ 2 * C ^ 2 / n
            field_simp
  have hup : HasSubgaussianMGF (fun ω => (1 / (n : ℝ)) * ∑ i, V i ω)
      (⟨M.B ^ 2 * C ^ 2 / n, by positivity⟩ : ℝ≥0) μ :=
    ⟨hscaled.integrable_exp_mul, fun t => (hscaled.mgf_le t).trans
      (Real.exp_le_exp.mpr (by gcongr; exact_mod_cast hproxy))⟩
  -- Assemble: centered (mean zero) sub-Gaussian.
  refine isSubGaussian_iff.mpr ?_
  rw [hmean]
  simp only [sub_zero]
  exact hup

end StatLean.HighDimensionalStatistics.MEstimator
