module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Shannon entropy, conditional entropy, mutual information and their basic inequalities

This file develops the information-theoretic background of the Minimaxity appendix used in the
proof of Fano's inequality. For a probability distribution one defines the **Shannon entropy**
$H(\mathbb{Q}) = -\int q \log q \, d\mu$, written via the density $q = d\mathbb{Q}/d\mu$ as
$-\int \log(d\mathbb{Q}/d\mu)\, d\mathbb{Q}$, and in the discrete case
$H(p) = -\sum_x p(x) \log p(x)$ for a probability mass function $p$ on a finite set. For a joint
pmf on $\mathcal{X} \times \mathcal{Y}$ one defines the **conditional entropy**
$H(X \mid Y) = H(X,Y) - H(Y)$ and the **mutual information**
$I(X;Y) = H(X) + H(Y) - H(X,Y)$, where $H(X)$ and $H(Y)$ are the entropies of the marginals.

The elementary properties proved here are:

* nonnegativity $H(p) \ge 0$ for any pmf;
* the maximal-entropy bound $H(p) \le \log |\mathcal{X}|$, with equality at the uniform distribution;
* "conditioning reduces entropy", $H(X \mid Y) \le H(X)$, equivalent to nonnegativity of the
  mutual information, $I(X;Y) \ge 0$ (equivalently subadditivity $H(X,Y) \le H(X) + H(Y)$).

In Lean terms: `shannonEntropy Q μ` is the measure-theoretic entropy; `discreteEntropy p`,
`discreteCondEntropy p`, `discreteMutualInfo p` are the discrete versions on `ι`, `ι × κ`; and the
three inequalities are `discreteEntropy_nonneg`, `discreteEntropy_le_log_card`,
`discreteCondEntropy_le_entropy`. The nonnegativity lemma carries the extra normalization
hypotheses (`0 ≤ p i`, `p i ≤ 1`) that pin down $p$ as a pmf; the bound and conditioning lemmas
take the total-mass-one hypothesis `∑ p = 1` rather than leaving it implicit, matching the book's
standing "p is a probability distribution" assumption.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4 (information-theoretic
appendix): Definition 15.24 (Shannon entropy, Eq. (15.57)), Eq. (15.58) (discrete entropy),
Definition 15.25 and Eq. (15.60b) (conditional entropy), Eq. (15.60d) (mutual information),
Eq. (15.60a) (conditioning reduces entropy), Exercise 15.2 (nonnegativity and the $\log|\mathcal{X}|$
bound).

**Proof formalization notes.** The discrete entropy is expressed through Mathlib's
`Real.negMulLog`, so $H(p) = \sum_i \mathrm{negMulLog}(p_i)$. Nonnegativity is termwise from
`Real.negMulLog_nonneg`. The maximal-entropy bound $H(p) \le \log|\mathcal{X}|$ is obtained from
Jensen's inequality for the concave function `negMulLog` (`Real.concaveOn_negMulLog.le_map_sum`)
with uniform weights $1/n$; the per-term and per-sum identities are bookkept explicitly so the
$1/n$ factor cancels. Conditioning-reduces-entropy is reduced to subadditivity
$H(X,Y) \le H(X) + H(Y)$, which in turn follows from the per-term Gibbs bound
`negMulLog_term_bound`: for $0 \le p \le a$, $p \le b$ one has
$p\log a + p\log b - p\log p \le ab - p$ (proved from $\log t \le t - 1$ applied to $t = ab/p$).
Summing this over the joint pmf, the slack $\sum (a_{x_1} b_{x_2} - p_x)$ telescopes to $0$ because
the marginals are normalized.

**Bibliographic comments.** The entropy functional and all of these properties originate with
C. E. Shannon, "A Mathematical Theory of Communication", *Bell System Technical Journal* **27**
(1948), 379–423 and 623–656. Shannon introduces $H = -\sum p_i \log p_i$ in §6 ("Choice,
Uncertainty and Entropy"); the maximal-entropy property ($H \le \log n$ with equality iff uniform)
and the subadditivity / conditioning inequalities ($H(x,y) \le H(x) + H(y)$, $H_x(y) \le H(y)$,
with equality iff independence) are listed there among his enumerated properties of $H$. The
inequality $\log t \le t - 1$ underlying the Gibbs/subadditivity step is the elementary form of the
nonnegativity of relative entropy (Kullback–Leibler divergence); see S. Kullback and R. A. Leibler,
"On Information and Sufficiency", *Annals of Mathematical Statistics* **22** (1951), 79–86. The
specific numbering (Definitions 15.24/15.25, Eqs. (15.57)–(15.60), Exercise 15.2) is Wainwright's
textbook synthesis of this classical material.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.Minimaxity

/-- **Shannon entropy** (Wainwright Definition 15.24, Eq. (15.57)): `H(ℚ) = −∫ q log q dμ`, written
via the density `q = dℚ/dμ` as `−∫ log(dℚ/dμ) dℚ`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Definition 15.24. -/
noncomputable def shannonEntropy {α : Type*} [MeasurableSpace α] (Q μ : Measure α) : ℝ :=
  -∫ x, Real.log ((Q.rnDeriv μ x).toReal) ∂Q

/-- **Discrete Shannon entropy** (Wainwright Eq. (15.58)): `H(p) = −Σ p(x) log p(x) = Σ negMulLog(p x)`
for a probability mass function `p` on a finite set.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Eq. (15.58). -/
noncomputable def discreteEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- **Conditional entropy** (Wainwright Definition 15.25, Eq. (15.60b)): `H(X | Y) = H(X,Y) − H(Y)`,
for a joint pmf `p` on `ι × κ` with `Y`-marginal `Σᵢ p(i, ·)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Definition 15.25. -/
noncomputable def discreteCondEntropy {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ) : ℝ :=
  discreteEntropy p - discreteEntropy (fun k : κ => ∑ i, p (i, k))

/-- **Mutual information** (Wainwright Eq. (15.60d)): `I(X;Y) = H(X) + H(Y) − H(X,Y)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Eq. (15.60d). -/
noncomputable def discreteMutualInfo {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ) : ℝ :=
  discreteEntropy (fun i : ι => ∑ k, p (i, k)) + discreteEntropy (fun k : κ => ∑ i, p (i, k))
    - discreteEntropy p

/-- **Discrete entropy is nonnegative** for a probability mass function (Wainwright Exercise 15.2a).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.2. -/
theorem discreteEntropy_nonneg {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) : 0 ≤ discreteEntropy p := by
  rw [discreteEntropy]
  exact Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (h0 i) (h1 i)

/-- **Discrete entropy is bounded by `log|𝒳|`** (Wainwright Exercise 15.2b), with equality at the
uniform distribution.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.2. -/
theorem discreteEntropy_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι] (p : ι → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    discreteEntropy p ≤ Real.log (Fintype.card ι) := by
  have hncard : 0 < Fintype.card ι := Fintype.card_pos
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hncard
  have hne : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hnpos
  -- Jensen for the concave function `negMulLog`, with uniform weights `1/n`.
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset ι)) (w := fun _ => 1 / (Fintype.card ι : ℝ)) (p := p)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp)
    (fun i _ => h0 i)
  have hLHS : (∑ i, (1 / (Fintype.card ι : ℝ)) • Real.negMulLog (p i))
      = (1 / (Fintype.card ι : ℝ)) * discreteEntropy p := by
    rw [discreteEntropy, Finset.mul_sum]
    simp [smul_eq_mul]
  have hRHS : (∑ i, (1 / (Fintype.card ι : ℝ)) • p i) = 1 / (Fintype.card ι : ℝ) := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
  rw [hLHS, hRHS] at hjensen
  have hlog : Real.negMulLog (1 / (Fintype.card ι : ℝ))
      = (1 / (Fintype.card ι : ℝ)) * Real.log (Fintype.card ι) := by
    simp only [Real.negMulLog_def, one_div, Real.log_inv]; ring
  rw [hlog] at hjensen
  exact le_of_mul_le_mul_left hjensen (div_pos one_pos hnpos)

/-- Per-term Gibbs bound underlying subadditivity of entropy: for nonnegative `p ≤ a` and `p ≤ b`,
`p log a + p log b − p log p ≤ a·b − p`. Summed over a joint pmf (with `a`, `b` the marginal
masses) this gives `H(X,Y) ≤ H(X) + H(Y)`, i.e. `I(X;Y) ≥ 0`. -/
private lemma negMulLog_term_bound {p a b : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hpa : p ≤ a) (hpb : p ≤ b) :
    p * Real.log a + p * Real.log b - p * Real.log p ≤ a * b - p := by
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · subst hp0; simpa using mul_nonneg ha hb
  · have hapos : 0 < a := lt_of_lt_of_le hp0 hpa
    have hbpos : 0 < b := lt_of_lt_of_le hp0 hpb
    have habpos : 0 < a * b := mul_pos hapos hbpos
    have hlog : Real.log (a * b / p) ≤ a * b / p - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hmul : p * Real.log (a * b / p) ≤ p * (a * b / p - 1) :=
      mul_le_mul_of_nonneg_left hlog (le_of_lt hp0)
    rw [Real.log_div (ne_of_gt habpos) (ne_of_gt hp0),
        Real.log_mul (ne_of_gt hapos) (ne_of_gt hbpos)] at hmul
    have hrhs : p * (a * b / p - 1) = a * b - p := by field_simp
    rw [hrhs, mul_sub, mul_add] at hmul
    linarith [hmul]

/-- **Conditioning reduces entropy** (Wainwright Eq. (15.60a)): `H(X | Y) ≤ H(X)`, equivalently the
mutual information is nonnegative (`I(X;Y) ≥ 0`).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.4, Eq. (15.60a). -/
theorem discreteCondEntropy_le_entropy {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι × κ → ℝ)
    (h0 : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    discreteCondEntropy p ≤ discreteEntropy (fun i : ι => ∑ k, p (i, k)) := by
  -- Reduce to subadditivity `H(X,Y) ≤ H(X) + H(Y)`, then abbreviate the two marginals.
  rw [discreteCondEntropy, sub_le_iff_le_add]
  set a : ι → ℝ := fun i => ∑ k, p (i, k) with ha_def
  set b : κ → ℝ := fun k => ∑ i, p (i, k) with hb_def
  -- Nonnegativity of marginals, and the `p ≤ marginal` domination facts.
  have ha0 : ∀ i, 0 ≤ a i := fun i => Finset.sum_nonneg fun k _ => h0 (i, k)
  have hb0 : ∀ k, 0 ≤ b k := fun k => Finset.sum_nonneg fun i _ => h0 (i, k)
  have hpa : ∀ x : ι × κ, p x ≤ a x.1 := fun x =>
    Finset.single_le_sum (f := fun k => p (x.1, k)) (fun k _ => h0 (x.1, k)) (Finset.mem_univ x.2)
  have hpb : ∀ x : ι × κ, p x ≤ b x.2 := fun x =>
    Finset.single_le_sum (f := fun i => p (i, x.2)) (fun i _ => h0 (i, x.2)) (Finset.mem_univ x.1)
  -- Rewrite each entropy as a single sum over `ι × κ`.
  have hEp : discreteEntropy p = ∑ x : ι × κ, (- p x * Real.log (p x)) := by
    rw [discreteEntropy]; simp_rw [Real.negMulLog_def]
  have hEa : discreteEntropy a = ∑ x : ι × κ, (- p x * Real.log (a x.1)) := by
    rw [discreteEntropy, Fintype.sum_prod_type]
    dsimp only
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Real.negMulLog_def]
    rw [← Finset.sum_mul]
    congr 1
    exact (Finset.sum_neg_distrib _).symm
  have hEb : discreteEntropy b = ∑ x : ι × κ, (- p x * Real.log (b x.2)) := by
    rw [discreteEntropy, Fintype.sum_prod_type_right]
    dsimp only
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [Real.negMulLog_def]
    rw [← Finset.sum_mul]
    congr 1
    exact (Finset.sum_neg_distrib _).symm
  -- The marginal masses are total mass `1`.
  have hA : (∑ i, a i) = 1 := by rw [ha_def, ← Fintype.sum_prod_type]; exact hsum
  have hB : (∑ k, b k) = 1 := by rw [hb_def, ← Fintype.sum_prod_type_right]; exact hsum
  have hab : (∑ x : ι × κ, a x.1 * b x.2) = 1 := by
    rw [Fintype.sum_prod_type]
    dsimp only
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hA, hB, mul_one]
  rw [hEp, hEa, hEb, ← Finset.sum_add_distrib]
  -- Termwise the joint term is below the marginal term plus slack `a·b − p`, which sums to `0`.
  refine le_trans (Finset.sum_le_sum (g := fun x : ι × κ =>
      (- p x * Real.log (a x.1) + - p x * Real.log (b x.2)) + (a x.1 * b x.2 - p x))
    (fun x _ => ?_)) ?_
  · have hterm := negMulLog_term_bound (h0 x) (ha0 x.1) (hb0 x.2) (hpa x) (hpb x)
    nlinarith [hterm]
  · rw [Finset.sum_add_distrib]
    have hzero : (∑ x : ι × κ, (a x.1 * b x.2 - p x)) = 0 := by
      rw [Finset.sum_sub_distrib, hab, hsum]; norm_num
    rw [hzero, add_zero]

end StatLean.Minimaxity
