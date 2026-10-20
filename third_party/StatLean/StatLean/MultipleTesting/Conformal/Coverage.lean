module
public import StatLean.MultipleTesting.ForMathlib.RankUniform

@[expose] public section

/-!
# Split-conformal prediction coverage guarantee

**Split-conformal prediction.** Consider $n+1$ nonconformity scores $S_0, \dots, S_{n-1}$
(from the calibration sample) together with a test score $S_n$, for a total of $m = n+1$ scores
that are **exchangeable** and almost surely pairwise distinct. The split-conformal prediction set
$\hat C$ is formed from the $k$-th smallest calibration score, where $k = \lceil (n+1)(1-\alpha)\rceil$.
Then the prediction set covers the test point with probability at least $1 - \alpha$:
$$
\mathbb{P}\bigl(Y_{n+1} \in \hat C\bigr) \;\ge\; 1 - \alpha .
$$
The covering event $\{Y_{n+1} \in \hat C\}$ is exactly the event that the test score is among the
$k$ smallest of the $m = n+1$ scores, i.e. $\{S_n \le S_{(k)}\}$, which equals
$\{\operatorname{rank}(S_n) \le k\}$.

**Main result** (`conformal_coverage`): with $k = \lceil (n+1)(1-\alpha)\rceil$,
$$
1 - \alpha \;\le\; \mathbb{P}\bigl(\operatorname{rank}(S_n) \le k\bigr).
$$

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 19 (Multiple Hypotheses), §19.1 (Conformal Inference).
Also E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes,
Stanford University, 2023, Lecture 9, §9.6, Theorem 2.

**Proof formalization notes.** By rank uniformity (`measure_rankOf_le`), the rank of the test score
is uniform on $\{1, \dots, n+1\}$, so $\mathbb{P}(\operatorname{rank}(S_n) \le k) = k/(n+1)$; and
$k = \lceil (n+1)(1-\alpha)\rceil \ge (n+1)(1-\alpha)$ gives $k/(n+1) \ge 1 - \alpha$. The Lean
proof proceeds in three steps: (1) $k \le n+1$, since $(n+1)(1-\alpha) \le n+1$ as $1 - \alpha \le 1$;
(2) apply `measure_rankOf_le` to rewrite the probability as $k/(n+1)$; (3) bridge through
`ENNReal.ofReal` and discharge $k/(n+1) \ge 1 - \alpha$ via the ceiling lower bound `Nat.le_ceil`.
The exchangeability, measurability, and a.s.-distinctness hypotheses are genuine external inputs
on the score family (Candès L9 §9.6).

**Bibliographic comments.** Split (a.k.a. inductive) conformal prediction originates with
H. Papadopoulos, K. Proedrou, V. Vovk & A. Gammerman, "Inductive Confidence Machines for
Regression", *ECML 2002*, LNCS 2430, pp. 345–356, and is developed systematically in V. Vovk,
A. Gammerman & G. Shafer, *Algorithmic Learning in a Random World*, Springer, 2005. The finite-sample
marginal coverage guarantee for split conformal in the regression setting, in the form proved here,
is Theorem 2.2 (with the companion full-conformal statement Theorem 2.1) of J. Lei, M. G'Sell,
A. Rinaldo, R. J. Tibshirani & L. Wasserman, "Distribution-Free Predictive Inference for Regression",
*Journal of the American Statistical Association* 113(523):1094–1111, 2018. The mechanism is the
exchangeability of the augmented score sample, which makes the rank of the test score uniform; the
$1-\alpha$ guarantee then follows from the ceiling choice of order statistic.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Conformal coverage** (Lu, *Big Data Analysis* (Springer, 2025), Ch 19, §19.1 Conformal
Inference; also Candès, Lecture 9, §9.6, Theorem 2, STAT 300C). For `n+1` exchangeable,
a.s. distinct scores, the split-conformal prediction set built from the `⌈(n+1)(1−α)⌉`-th smallest
score covers the test point (the `rankOf S (last) ≤ k` event) with probability at least `1 − α`. -/
theorem conformal_coverage {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (S : Fin (n + 1) → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    -- USER-INPUT: each score is measurable; Candès L9 §9.6
    (hmeas : ∀ i, Measurable (S i))
    -- USER-INPUT: the scores are exchangeable (calibration + test exchangeable); Candès L9 §9.6
    (hExch : Exchangeable S μ)
    -- USER-INPUT: the scores are a.s. pairwise distinct; Candès L9 §9.6
    (hdistinct : ∀ᵐ ω ∂μ, Function.Injective (fun i => S i ω)) :
    (ENNReal.ofReal (1 - α)) ≤
      μ {ω | rankOf S (Fin.last n) ω ≤ ⌈((n : ℝ) + 1) * (1 - α)⌉₊} := by
  set k : ℕ := ⌈((n : ℝ) + 1) * (1 - α)⌉₊ with hkdef
  -- Step 1: `k ≤ n+1`, since `(n+1)(1−α) ≤ n+1` as `1−α ≤ 1`.
  have hk : k ≤ n + 1 := by
    rw [hkdef]
    refine Nat.ceil_le.mpr ?_
    push_cast
    nlinarith [hα0]
  -- Step 2: rank uniformity gives `μ{rankOf ≤ k} = k/(n+1)`.
  rw [measure_rankOf_le S μ hmeas hExch hdistinct (Fin.last n) hk]
  -- Step 3: bridge `k/(n+1) = ofReal (k/(n+1)) ≥ ofReal (1−α)`.
  have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [← ENNReal.ofReal_natCast k, ← ENNReal.ofReal_natCast (n + 1),
    ← ENNReal.ofReal_div_of_pos hnpos]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hnpos]
  have hceil : ((n : ℝ) + 1) * (1 - α) ≤ (k : ℝ) := by
    rw [hkdef]; exact Nat.le_ceil _
  push_cast at hceil ⊢
  nlinarith [hceil]

end StatLean.MultipleTesting
