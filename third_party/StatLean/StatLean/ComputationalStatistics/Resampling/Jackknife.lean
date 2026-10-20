module
public import StatLean.ComputationalStatistics.Core.Defs
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The jackknife: pseudovalues and the basic algebra

Quenouille–Tukey delete-one jackknife over a sample of size `n + 1` (ECS §3.3,
with the book's group size `k = 1`, so `r = n + 1` groups):

* `jackknifeDelete i x = x ∘ Fin.succAbove i` — the sample with observation `i`
  removed;
* `jackknifeMean` — the delete-one average `T₍•₎` (eq. (3.5));
* `jackknifePseudoValue` — `T*ᵢ = (n+1)·T − n·T₍₋ᵢ₎` (eq. (3.6));
* `jackknifed` — the jackknifed statistic `J(T)`, the mean of the pseudovalues
  (eq. (3.7)), with the closed forms of eq. (3.8) and eq. (3.12);
* `jackknifeBiasEstimate` — `B_J = n·(T₍•₎ − T)` (eq. (3.11));
* `jackknifeVarianceEstimate` — Tukey's variance estimator (eq. (3.9));
* the **linear-functional case** (ECS §3.3, p. 75): for plug-in averages
  `T = mcEstimate g`, the pseudovalues are the observations `g(xᵢ)`, `J(T) = T`,
  and the jackknife variance estimator is the classical `s²/n` for the sample
  mean (`jackknifeVariance_mcEstimate`).

The statistic is passed as a *pair* `(T, T')` — its full-sample and
reduced-sample versions — because a "statistic defined for every sample size"
is not a single Lean function; the bias-reduction theorem in
`Resampling/JackknifeBias.lean` constrains the pair through its moment
hypotheses.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §3.3 (jackknife methods, eqs. (3.5)–(3.12)).
(`ECS §3.3`.)

**Proof formalization notes.**

* Everything in this file is finite algebra over `Fin (n+1)`-indexed sums —
  no measure theory; the probabilistic statements live in
  `Resampling/JackknifeBias.lean`.
* Deletion is `Fin.succAbove`, avoiding `n − 1` arithmetic; the key sum
  identity is `Fin.sum_univ_succAbove`.
* Edge behaviour: at `n = 0` the reduced sample is empty and `T'` is evaluated
  on the empty sample; all identities remain true as stated (the `n = 0`
  variance estimator is the empty sum `0`).

**Bibliographic comments.** M. Quenouille, "Approximate tests of correlation in
time-series," *J. Roy. Statist. Soc. B* **11** (1949), 68–84, and "Notes on bias
in estimation," *Biometrika* **43** (1956), 353–360 (bias correction); J. Tukey,
"Bias and confidence in not-quite large samples (abstract)," *Ann. Math.
Statist.* **29** (1958), 614 (pseudovalues and the variance estimator).
-/

open scoped BigOperators

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} {n : ℕ}

/-- **Delete-one sample** (ECS §3.3): the sample `x` with observation `i`
removed, reindexed over `Fin n` by `Fin.succAbove`. -/
def jackknifeDelete (i : Fin (n + 1)) (x : Fin (n + 1) → 𝓧) : Fin n → 𝓧 :=
  x ∘ i.succAbove

/-- **The delete-one average** `T₍•₎` (ECS §3.3, eq. (3.5)): the average of the
reduced-sample statistic over the `n + 1` deletions. -/
noncomputable def jackknifeMean (T' : (Fin n → 𝓧) → ℝ) (x : Fin (n + 1) → 𝓧) :
    ℝ :=
  ((n : ℝ) + 1)⁻¹ * ∑ i, T' (jackknifeDelete i x)

/-- **Jackknife pseudovalue** (ECS §3.3, eq. (3.6)):
`T*ᵢ = (n+1)·T(x) − n·T'(x₍₋ᵢ₎)`. -/
noncomputable def jackknifePseudoValue (T : (Fin (n + 1) → 𝓧) → ℝ)
    (T' : (Fin n → 𝓧) → ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → 𝓧) : ℝ :=
  ((n : ℝ) + 1) * T x - n * T' (jackknifeDelete i x)

/-- **The jackknifed statistic** `J(T)` (ECS §3.3, eq. (3.7)): the mean of the
pseudovalues. -/
noncomputable def jackknifed (T : (Fin (n + 1) → 𝓧) → ℝ)
    (T' : (Fin n → 𝓧) → ℝ) (x : Fin (n + 1) → 𝓧) : ℝ :=
  ((n : ℝ) + 1)⁻¹ * ∑ i, jackknifePseudoValue T T' i x

/-- **The jackknife bias estimator** (ECS §3.3, eq. (3.11)):
`B_J = n·(T₍•₎ − T)`. -/
noncomputable def jackknifeBiasEstimate (T : (Fin (n + 1) → 𝓧) → ℝ)
    (T' : (Fin n → 𝓧) → ℝ) (x : Fin (n + 1) → 𝓧) : ℝ :=
  n * (jackknifeMean T' x - T x)

/-- **Tukey's jackknife variance estimator** (ECS §3.3, eq. (3.9)):
`V_J = Σᵢ (T*ᵢ − J(T))² / (r(r−1))` with `r = n + 1` groups. -/
noncomputable def jackknifeVarianceEstimate (T : (Fin (n + 1) → 𝓧) → ℝ)
    (T' : (Fin n → 𝓧) → ℝ) (x : Fin (n + 1) → 𝓧) : ℝ :=
  (((n : ℝ) + 1) * n)⁻¹ * ∑ i, (jackknifePseudoValue T T' i x - jackknifed T T' x) ^ 2

/-- **Closed form of the jackknifed statistic** (ECS §3.3, eq. (3.8)):
`J(T) = (n+1)·T − n·T₍•₎`. -/
theorem jackknifed_eq (T : (Fin (n + 1) → 𝓧) → ℝ) (T' : (Fin n → 𝓧) → ℝ)
    (x : Fin (n + 1) → 𝓧) :
    jackknifed T T' x = ((n : ℝ) + 1) * T x - n * jackknifeMean T' x := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hsum : ∑ i : Fin (n + 1), jackknifePseudoValue T T' i x
      = ((n : ℝ) + 1) * (((n : ℝ) + 1) * T x)
        - n * ∑ i : Fin (n + 1), T' (jackknifeDelete i x) := by
    simp only [jackknifePseudoValue, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    push_cast
    ring
  unfold jackknifed jackknifeMean
  rw [hsum]
  field_simp

/-- **The jackknifed statistic is the bias-corrected statistic** (ECS §3.3,
eq. (3.12)): `J(T) = T − B_J`. -/
theorem jackknifed_eq_sub_biasEstimate (T : (Fin (n + 1) → 𝓧) → ℝ)
    (T' : (Fin n → 𝓧) → ℝ) (x : Fin (n + 1) → 𝓧) :
    jackknifed T T' x = T x - jackknifeBiasEstimate T T' x := by
  rw [jackknifed_eq]
  unfold jackknifeBiasEstimate
  ring

/-- **Pseudovalues of a plug-in average are the observations** (ECS §3.3,
p. 75: "if `T` is a linear functional of the ECDF, then `T*ⱼ = T(xⱼ)`"). -/
theorem jackknifePseudoValue_mcEstimate (g : 𝓧 → ℝ) (i : Fin (n + 1))
    (x : Fin (n + 1) → 𝓧) :
    jackknifePseudoValue (mcEstimate g) (mcEstimate g) i x = g (x i) := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hsum : ∑ j : Fin (n + 1), g (x j)
      = g (x i) + ∑ j : Fin n, g (x (i.succAbove j)) :=
    Fin.sum_univ_succAbove (fun j => g (x j)) i
  unfold jackknifePseudoValue mcEstimate jackknifeDelete
  push_cast
  rw [mul_inv_cancel_left₀ hn, hsum]
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    simp
  · have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0.ne'
    rw [mul_inv_cancel_left₀ hn']
    simp

/-- **The jackknife does not move a plug-in average** (ECS §3.3, p. 75):
`J(T) = T` for `T = mcEstimate g`. -/
theorem jackknifed_mcEstimate (g : 𝓧 → ℝ) (x : Fin (n + 1) → 𝓧) :
    jackknifed (mcEstimate g) (mcEstimate g) x = mcEstimate g x := by
  unfold jackknifed
  simp only [jackknifePseudoValue_mcEstimate]
  unfold mcEstimate
  push_cast
  ring

/-- **The jackknife variance estimate of the sample mean is `s²/n`**
(ECS §3.3, remark after eq. (3.9)): for the plug-in average of `g` over the
`n + 1` observations,
`V_J = ((n+1)·n)⁻¹·Σᵢ (g(xᵢ) − ḡ)² = s²_{g}/(n+1)`, with `s²` the
Bessel-corrected sample variance of the `g`-values. -/
theorem jackknifeVariance_mcEstimate (g : 𝓧 → ℝ) (x : Fin (n + 1) → 𝓧) :
    jackknifeVarianceEstimate (mcEstimate g) (mcEstimate g) x
      = (((n : ℝ) + 1) * n)⁻¹ * ∑ i, (g (x i) - mcEstimate g x) ^ 2 := by
  unfold jackknifeVarianceEstimate
  simp only [jackknifePseudoValue_mcEstimate, jackknifed_mcEstimate]

end StatLean.ComputationalStatistics

