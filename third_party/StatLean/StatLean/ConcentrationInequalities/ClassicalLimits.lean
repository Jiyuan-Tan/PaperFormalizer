module
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
# Classical limit theorems: Law of Large Numbers and Central Limit Theorem

The two classical limit theorems for an i.i.d. sequence $X_0, X_1, \dots$ of real-valued
random variables on a probability space $(\Omega, P)$.

* **Law of Large Numbers (in probability).** If $X_0$ is integrable ($\mathbb{E}|X_0| < \infty$),
  then the sample mean converges in probability to the common mean $\mu := \mathbb{E}[X_0]$:
  $$ \frac{1}{n}\sum_{i<n} X_i \;\xrightarrow{\;P\;}\; \mu . $$

* **Central Limit Theorem.** If $X_0$ has a finite variance $\sigma^2 := \operatorname{Var}(X_0)$,
  then the centered and scaled partial sums converge in distribution to a centered
  Gaussian with that variance:
  $$ \frac{1}{\sqrt{n}}\Bigl(\sum_{k<n} X_k - n\,\mu\Bigr) \;\xrightarrow{\;d\;}\; N(0, \sigma^2). $$
  This is the standard Lindeberg–Lévy "sum-form" normalization; the more familiar
  $\sqrt{n}\,(\bar X_n - \mu)/\sigma \to N(0,1)$ form follows by dividing through by
  $\sigma > 0$ (composing with the affine map $y \mapsto y/\sigma$, which sends
  $N(0,\sigma^2)$ to $N(0,1)$).

Each is proved by a thin delegation to Mathlib: the LLN to `ProbabilityTheory.strong_law_ae`
(a.e. convergence, which implies convergence in measure on a probability space) and the CLT
to `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 4 (Concentration Inequalities), §4.1
(Asymptotic versus Non-Asymptotic).

**Proof formalization notes.**

The book states the LLN under "i.i.d., finite mean" and the CLT under "i.i.d., finite mean
and variance". Mathlib requires:

* Strong-law form (`strong_law_ae`): `Integrable (X 0)`, pairwise independence,
  identical distribution. We take the (book-equivalent, slightly stronger) mutual
  independence `iIndepFun X P` and derive pairwise independence via `iIndepFun.indepFun`.
  On a probability (hence finite) measure, a.e. convergence implies convergence in measure
  via `MeasureTheory.tendstoInMeasure_of_tendsto_ae`, yielding the in-probability conclusion.

* CLT form (`tendstoInDistribution_inv_sqrt_mul_sum_sub`): `MemLp (X 0) 2 P`
  (the textbook's "finite variance" — equivalent on a probability space to
  `Integrable` + finite second moment), `iIndepFun X P`, identical distribution,
  and a witness `Y` on a (possibly different) probability space `(Ω', P')`
  carrying the target Gaussian law `N(0, σ²)`. We mirror these hypotheses
  verbatim; the `MemLp 2` strengthening over the book's bare "finite variance"
  is harmless on a probability space.

**Bibliographic comments.** Both results are classical folklore with no single seminal
source.

* *Law of large numbers.* The earliest form is the weak law for Bernoulli trials in
  J. Bernoulli, *Ars Conjectandi* (Basel, 1713, posthumous). The general weak LLN for
  i.i.d. variables with a finite mean is due to A. Khinchin, "Sur la loi des grands
  nombres," *Comptes Rendus Acad. Sci. Paris* **189** (1929), 477–479. The almost-sure
  (strong) law actually invoked here — A. N. Kolmogorov, "Über die Summen durch den Zufall
  bestimmter unabhängiger Größen," *Math. Ann.* **99** (1928), 309–319, with the i.i.d.
  finite-mean criterion in his *Grundbegriffe der Wahrscheinlichkeitsrechnung*
  (Springer, 1933) — is strictly stronger and implies the in-probability statement.

* *Central limit theorem.* The de Moivre–Laplace theorem (A. de Moivre, 1733; P.-S. Laplace,
  *Théorie analytique des probabilités*, 1812) is the binomial special case. The modern
  i.i.d. theorem under a finite second moment is the Lindeberg–Lévy CLT: J. W. Lindeberg,
  "Eine neue Herleitung des Exponentialgesetzes in der Wahrscheinlichkeitsrechnung,"
  *Math. Z.* **15** (1922), 211–225, and P. Lévy, *Calcul des probabilités*
  (Gauthier-Villars, Paris, 1925).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace StatLean.ConcentrationInequalities

/-- **Law of Large Numbers, in probability** (Lu BDA §4.1).

For an i.i.d. sequence `X 0, X 1, …` of real-valued random variables on a
probability space `(Ω, P)` with `E |X 0| < ∞`, the sample mean
`n⁻¹ · ∑_{i<n} X i` converges *in probability* to `μ := E[X 0]`.

Proof: Mathlib's `strong_law_ae` gives a.e. convergence; on a probability
(hence finite) measure, a.e. convergence implies convergence in measure
via `MeasureTheory.tendstoInMeasure_of_tendsto_ae`.

The book's "i.i.d." is encoded here as mutual independence (`iIndepFun`) plus
identical distribution — the standard formalization. Pairwise independence
(what `strong_law_ae` consumes) is derived internally. -/
theorem law_of_large_numbers_in_probability
    {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    -- USER-INPUT: integrability of X 0 (book: "finite mean"); Lu-BDA §4.1
    (hint : Integrable (X 0) P)
    -- USER-INPUT: mutual independence of the sequence (book: "i.i.d."); Lu-BDA §4.1
    (hindep : iIndepFun X P)
    -- USER-INPUT: identical distributions (book: "i.i.d."); Lu-BDA §4.1
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) atTop
      (fun _ => ∫ x, X 0 x ∂P) := by
  have hpair : Pairwise (Function.onFun (fun x y => IndepFun x y P) X) :=
    fun _ _ hij => hindep.indepFun hij
  have hae := ProbabilityTheory.strong_law_ae X hint hpair hident
  have hX_ae : ∀ i, AEStronglyMeasurable (X i) P :=
    fun i => (hident i).aestronglyMeasurable_fst
  have hf_ae : ∀ (n : ℕ), AEStronglyMeasurable
      (fun ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω) P := fun (n : ℕ) =>
    ((Finset.aestronglyMeasurable_sum (Finset.range n) (fun i _ => hX_ae i)).congr
        (Filter.Eventually.of_forall fun ω => Finset.sum_apply ω _ X)).const_smul' _
  exact MeasureTheory.tendstoInMeasure_of_tendsto_ae hf_ae hae

/-- **Central Limit Theorem** (Lu BDA §4.1).

For an i.i.d. sequence `X 0, X 1, …` of real-valued random variables on a
probability space `(Ω, P)` with `X 0 ∈ L²(P)`, the centered-and-scaled partial
sums
  `(√n)⁻¹ · (∑_{k<n} X k − n · E[X 0])`
converge *in distribution* (under `P`) to a real Gaussian random variable
`Y` with mean `0` and variance `σ² = Var(X 0)`, defined on an auxiliary
probability space `(Ω', P')`.

This is the book's CLT in the standard "sum-form" Lindeberg–Lévy normalization;
the more familiar `√n · ((X̄ₙ − μ)/σ) → N(0,1)` form is obtained by dividing
through by `σ > 0` (i.e. by composing with the affine `y ↦ y/σ`, which sends
`N(0, σ²)` to `N(0,1)`).

Proof: direct delegation to `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub`. -/
theorem central_limit_theorem
    {Ω Ω' : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace Ω'}
    {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    -- USER-INPUT: target Gaussian witness on (Ω', P') with variance σ² = Var(X 0); Lu-BDA §4.1
    (hY : HasLaw Y (gaussianReal 0 (variance (X 0) P).toNNReal) P')
    -- USER-INPUT: finite second moment of X 0 (book: "finite variance"); Lu-BDA §4.1
    -- LEAN-ONLY strengthening: Mathlib's CLT statement is phrased with `MemLp _ 2`,
    -- which on a probability space is equivalent to the book's "finite variance".
    (hX : MemLp (X 0) 2 P)
    -- USER-INPUT: mutual independence of the sequence (book: "i.i.d."); Lu-BDA §4.1
    (hindep : iIndepFun X P)
    -- USER-INPUT: identical distributions (book: "i.i.d."); Lu-BDA §4.1
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ *
        (∑ k ∈ Finset.range n, X k ω - (n : ℝ) * ∫ x, X 0 x ∂P))
      atTop Y (fun _ => P) P' :=
  ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum_sub hY hX hindep hident

end StatLean.ConcentrationInequalities
