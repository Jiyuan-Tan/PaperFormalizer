module
public import StatLean.Minimaxity.Fano.LocalPacking
public import StatLean.Minimaxity.ForMathlib.Packing.HammingPacking

@[expose] public section

/-!
# Minimax risk for density estimation in Hellinger distance

Estimating a twice-smooth density $f \in \mathcal{F}_2$ in the squared Hellinger metric, from $n$
i.i.d. samples, has minimax risk of order $n^{-4/5}$. Concretely, this file states the Fano
local-packing route: from a Hamming-separated subfamily of perturbed densities with separation
$\delta_n \asymp n^{-2/5}$ and a controlled pairwise Kullback–Leibler divergence, the Fano local
packing bound (`minimax_local_packing`) delivers a minimax risk lower bound of order
$\delta_n^2 \asymp n^{-4/5}$. The squared-Hellinger loss is encoded through the squaring map
$\Phi(x) = x^2$ applied to the Hellinger (extended) distance, and the bound obtained is
$\tfrac{1}{2}\, n^{-4/5}$.

This is the standard rate $n^{-2\beta/(2\beta+1)}$ for estimating a $\beta$-smooth density,
specialised to smoothness $\beta = 2$ (twice-smooth), which gives the exponent $4/5$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3, Examples 15.15 and
15.22, with the local KL/cardinality conditions corresponding to Eqs (15.35a)–(15.35b).

**Proof formalization notes.** We state the local-packing route of Example 15.15 rather than the
global metric-entropy route of Example 15.22: the perturbed-density / Hamming construction supplies
(i) a separation `IsSeparatedFamily` with $\delta_n = n^{-2/5}$, (ii) the pairwise KL bound (15.35a)
$\mathrm{KL}(P_{\theta_j}\,\Vert\,P_{\theta_k}) \le c^2\, n\, \delta_n^2$, and (iii) the packing
cardinality bound (15.35b) $2\,(c^2 n \delta_n^2 + \log 2) \le \log M$. Feeding these to
`minimax_local_packing` with the monotone squaring map $\Phi(x) = x^2$ yields the conclusion.
The separation, KL control, and cardinality conditions enter as `USER-INPUT` hypotheses
(`hsep`, `h35a`, `h35b`), since they are the externally supplied data of the construction; the
remaining work is the arithmetic identity converting `ENNReal.ofReal (2⁻¹ · δₙ²)` into
`2⁻¹ · (ENNReal.ofReal δₙ)²`.

**Bibliographic comments.** The $n^{-2\beta/(2\beta+1)}$ minimax rate for nonparametric density
estimation under smoothness $\beta$ is classical, going back to I. A. Ibragimov and R. Z.
Khasminskii and to C. J. Stone, *Optimal global rates of convergence for nonparametric regression*
and related density-estimation work (Ann. Statist., 1980s). The systematic information-theoretic
(Fano / metric-entropy) determination of such rates — the approach Wainwright's Examples 15.15 and
15.22 follow — is due to Y. Yang and A. Barron, *Information-theoretic determination of minimax
rates of convergence*, Annals of Statistics, 27(5):1564–1599, 1999. The Fano local-packing lower
bound used here is the local version of their general scheme; the $\beta = 2$, Hellinger-loss
instance is the worked example, not a result with a single distinct seminal origin.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Minimax risk for density estimation in Hellinger distance** (Wainwright Example 15.15): for a
local packing of the twice-smooth density class with separation `δₙ = n^{-2/5}` and pairwise KL
control (the perturbed-density / Hamming construction), `minimax_local_packing` gives a minimax
risk (squared Hellinger, encoded as `edist²`) of at least `½ · n^{-4/5}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3, Example 15.15. -/
theorem density_estimation_hellinger_rate {ι 𝓧 Ω : Type*} [MeasurableSpace ι] [MeasurableSpace 𝓧]
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (n : ℕ) (hn : 1 ≤ n)
    (g : ι → Ω) (P : Kernel ι 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → ι) (hθ : Measurable θfam) (c : ℝ) (hM : 2 ≤ M)
    -- USER-INPUT: a Hamming-separated subfamily with separation `δₙ = n^{-2/5}`; Wainwright §15.3, Ex 15.15.
    (hsep : IsSeparatedFamily g θfam (ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ) / 5))))
    -- USER-INPUT: pairwise KL control (15.35a) for the perturbed-density construction; Wainwright §15.3.
    (h35a : ∀ j k, j ≠ k → klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
      ≤ ENNReal.ofReal (c ^ 2 * n * ((n : ℝ) ^ (-(2 : ℝ) / 5)) ^ 2))
    -- USER-INPUT: packing cardinality (15.35b); Wainwright §15.3.
    (h35b : 2 * (c ^ 2 * n * ((n : ℝ) ^ (-(2 : ℝ) / 5)) ^ 2 + Real.log 2) ≤ Real.log (M : ℝ)) :
    ENNReal.ofReal (2⁻¹ * ((n : ℝ) ^ (-(2 : ℝ) / 5)) ^ 2) ≤ minimaxRiskDist (· ^ 2) g P := by
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(2 : ℝ) / 5) := by positivity
  have hδtoReal : (ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ) / 5))).toReal = (n : ℝ) ^ (-(2 : ℝ) / 5) :=
    ENNReal.toReal_ofReal hx0
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have h35a' : ∀ j k, j ≠ k →
      klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * (n : ℝ) *
            (ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ) / 5))).toReal ^ 2) := by
    intro j k hjk; rw [hδtoReal]; exact h35a j k hjk
  have h35b' : 2 * (c ^ 2 * (n : ℝ) *
      (ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ) / 5))).toReal ^ 2 + Real.log 2) ≤ Real.log (M : ℝ) := by
    rw [hδtoReal]; exact h35b
  have key := minimax_local_packing (fun x : ℝ≥0∞ => x ^ 2) g P θfam hθ
    (ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ) / 5))) c (n : ℝ) hΦ hsep (by positivity) h35a' h35b'
  have harith : ENNReal.ofReal (2⁻¹ * ((n : ℝ) ^ (-(2 : ℝ) / 5)) ^ 2)
      = 2⁻¹ * (ENNReal.ofReal ((n : ℝ) ^ (-(2 : ℝ) / 5))) ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), ENNReal.ofReal_pow hx0,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [harith]
  exact key

end StatLean.Minimaxity
