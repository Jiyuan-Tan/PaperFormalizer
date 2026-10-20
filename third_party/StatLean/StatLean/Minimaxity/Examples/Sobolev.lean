module
public import StatLean.Minimaxity.Fano.LocalPacking
public import StatLean.Minimaxity.Fano.YangBarron
public import StatLean.Minimaxity.ForMathlib.Packing.SobolevEntropy

@[expose] public section

/-!
# Minimax risk for smoothness-α Sobolev regression (Yang–Barron method)

Consider nonparametric regression over a smoothness-$\alpha$ Sobolev ellipsoid
$\mathcal{F}_\alpha$, with i.i.d. Gaussian noise of variance $\sigma^2$ and sample size $n$.
The Yang–Barron method combines the metric entropy of $\mathcal{F}_\alpha$ — which scales like
$\log N(\delta;\mathcal{F}_\alpha) \asymp \delta^{-1/\alpha}$ — with Fano's lemma to give a minimax
lower bound on the estimation error measured in squared $L^2$-norm:
$$
\inf_{\widehat{f}} \sup_{f \in \mathcal{F}_\alpha}\, \mathbb{E}\,\|\widehat{f} - f\|_2^2
\;\gtrsim\; \left(\frac{\sigma^2}{n}\right)^{\frac{2\alpha}{2\alpha+1}}.
$$

We formalize the local-packing form of this bound. Given a $\delta_n$-separated family of $M$
candidate parameters, with separation
$$
\delta_n = \left(\frac{\sigma^2}{n}\right)^{\frac{\alpha}{2\alpha+1}},
$$
satisfying the pairwise Kullback–Leibler bound (15.35a)
$\mathrm{KL}(P_{\theta_j}\,\|\,P_{\theta_k}) \le c^2\, n\, \delta_n^2$ and the packing-cardinality
condition (15.35b) $\,2\,(c^2 n\,\delta_n^2 + \log 2) \le \log M$, the abstract local-packing bound
`minimax_local_packing` yields a minimax risk in squared $L^2$-distance of at least
$$
\tfrac{1}{2}\,\delta_n^2
= \tfrac{1}{2}\left(\frac{\sigma^2}{n}\right)^{\frac{2\alpha}{2\alpha+1}}.
$$
We require $\alpha > \tfrac{1}{2}$, $\sigma > 0$, $n \ge 1$, and $M \ge 2$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Example 15.23
(Sobolev ellipsoids), using the Yang–Barron method (Lemma 15.21) and the Sobolev metric-entropy
estimate (Example 5.12), with packing conditions Eq. (15.35a)–(15.35b).

**Proof formalization notes.** Rather than re-deriving the entropy/KL balance from the analytic
definition of $\mathcal{F}_\alpha$, the formalization takes the separation $\delta_n$, the pairwise
KL control (15.35a), and the packing cardinality (15.35b) as the Sobolev-specific inputs and feeds
them to the abstract `minimax_local_packing` (Fano / local-packing) machinery. The squared-distance
loss is encoded as the monotone map `x ↦ x²` on `ℝ≥0∞`, and the bound is stated with the
`ENNReal.ofReal` packaging of $\tfrac12 \delta_n^2$; the arithmetic `harith` step reconciles
`ofReal (2⁻¹ · δ²)` with `2⁻¹ · (ofReal δ)²`. The leading constant $\tfrac12$ is the constant
delivered by `minimax_local_packing`, matching the order of Example 15.23 up to the universal factor.

**Bibliographic comments.** The entropy-to-minimax-rate methodology formalized here originates with
Y. Yang and A. Barron, "Information-theoretic determination of minimax rates of convergence,"
*Annals of Statistics*, Vol. 27, No. 5 (1999), pp. 1564–1599. That paper establishes (notably its
Theorems 1–6) that minimax rates of convergence in density estimation and regression are governed by
the metric entropy of the parameter class, via mutual-information / Fano arguments; the
$(\sigma^2/n)^{2\alpha/(2\alpha+1)}$ rate for smoothness-$\alpha$ classes is the canonical instance.
Wainwright §15.3.5 presents this as the "Yang–Barron method" (Lemma 15.21), and Example 15.23
specializes it to Sobolev ellipsoids.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Minimax risk for Sobolev regression** (Wainwright Example 15.23): from a packing of the
smoothness-`α` Sobolev family with separation `δₙ = (σ²/n)^{α/(2α+1)}` and pairwise KL control,
`minimax_local_packing` gives a minimax risk (squared `L²`, encoded as `edist²`) of at least
`½ · (σ²/n)^{2α/(2α+1)}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Example 15.23. -/
theorem sobolev_regression_rate {ι 𝓧 Ω : Type*} [MeasurableSpace ι] [MeasurableSpace 𝓧]
    [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] (n : ℕ) (hn : 1 ≤ n) (α σ : ℝ)
    (hα : 1 / 2 < α) (hσ : 0 < σ)
    (g : ι → Ω) (P : Kernel ι 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → ι) (hθ : Measurable θfam) (c : ℝ) (hM : 2 ≤ M)
    -- USER-INPUT: separation `δₙ = (σ²/n)^{α/(2α+1)}`; Wainwright §15.3.5, Example 15.23.
    (hsep : IsSeparatedFamily g θfam (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))))
    -- USER-INPUT: pairwise KL control (15.35a) for the Sobolev construction; Wainwright §15.3.5.
    (h35a : ∀ j k, j ≠ k → klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
      ≤ ENNReal.ofReal (c ^ 2 * n * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2))
    -- USER-INPUT: packing cardinality (15.35b); Wainwright §15.3.5.
    (h35b : 2 * (c ^ 2 * n * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2 + Real.log 2) ≤ Real.log (M : ℝ)) :
    ENNReal.ofReal (2⁻¹ * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2) ≤ minimaxRiskDist (· ^ 2) g P := by
  have hx0 : (0 : ℝ) ≤ (σ ^ 2 / n) ^ (α / (2 * α + 1)) := by positivity
  have hδtoReal : (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))).toReal
      = (σ ^ 2 / n) ^ (α / (2 * α + 1)) := ENNReal.toReal_ofReal hx0
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have h35a' : ∀ j k, j ≠ k →
      klDiv ((P.comap θfam hθ) j) ((P.comap θfam hθ) k)
        ≤ ENNReal.ofReal (c ^ 2 * (n : ℝ) *
            (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))).toReal ^ 2) := by
    intro j k hjk; rw [hδtoReal]; exact h35a j k hjk
  have h35b' : 2 * (c ^ 2 * (n : ℝ) *
      (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))).toReal ^ 2 + Real.log 2)
      ≤ Real.log (M : ℝ) := by rw [hδtoReal]; exact h35b
  have key := minimax_local_packing (fun x : ℝ≥0∞ => x ^ 2) g P θfam hθ
    (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))) c (n : ℝ) hΦ hsep (by positivity) h35a' h35b'
  have harith : ENNReal.ofReal (2⁻¹ * ((σ ^ 2 / n) ^ (α / (2 * α + 1))) ^ 2)
      = 2⁻¹ * (ENNReal.ofReal ((σ ^ 2 / n) ^ (α / (2 * α + 1)))) ^ 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹), ENNReal.ofReal_pow hx0,
        ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [harith]
  exact key

end StatLean.Minimaxity
