module
public import StatLean.Minimaxity.EstimationToTesting
public import StatLean.Minimaxity.Fano.MutualInformation
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# Fano's method for minimax lower bounds

**Fano's inequality.** Consider an $M$-ary hypothesis-testing problem in which an index
$J$ is drawn uniformly from $\{1, \dots, M\}$ and an observation $Z$ is generated from the
$J$-th distribution. For any test $\psi$ that guesses $J$ from $Z$, the error probability is
lower bounded by the mutual information $I(Z; J)$ between the observation and the index:
$$
\inf_{\psi} \mathbb{P}\bigl[\psi(Z) \neq J\bigr]
  \;\ge\; 1 - \frac{I(Z; J) + \log 2}{\log M}.
$$
Here $\log$ denotes the natural logarithm, and the bound is nontrivial when $M \ge 2$
(so that $\log M > 0$).

**Fano minimax lower bound.** Combining Fano's inequality with the estimation-to-testing
reduction (the same Proposition 15.1 reduction used elsewhere in this module) gives a lower
bound on the minimax risk. For an increasing distortion function $\Phi$ and a family of
parameters $\theta_1, \dots, \theta_M$ that is $2\delta$-separated under the (pseudo)metric on
the target space, the minimax risk for the distortion loss $\Phi \circ \rho$ satisfies
$$
\mathfrak{M}\bigl(\theta(\mathcal{P}); \Phi \circ \rho\bigr)
  \;\ge\; \Phi(\delta)\left(1 - \frac{I(Z; J) + \log 2}{\log M}\right),
$$
where $I(Z; J)$ is the mutual information of the sub-model induced by restricting to the
$M$ candidate parameters.

This file formalizes both statements: `fano_inequality` (the $M$-ary error bound) and
`minimax_fano_lower_bound` (the minimax consequence). Notation alignment with the Lean
statements: the error probability $\inf_\psi \mathbb{P}[\psi(Z) \neq J]$ is the M-ary Bayes
risk of the 0–1 loss under the uniform prior, written `multiwayTestingError Q`; the mutual
information $I(Z; J)$ is `mutualInformation Q`; and the natural-log constants enter through
`ENNReal.ofReal (Real.log ·)` to keep the inequality in the extended nonnegative reals.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2,
Eq. (15.31) (Fano's inequality), Proposition 15.12 with Eq. (15.32) (Fano minimax lower
bound), via the Shannon-entropy form Eq. (15.61).

**Proof formalization notes.** The proof of Fano's inequality (Eq. (15.31)) goes through the
Shannon-entropy form (Eq. (15.61)) supported by the entropy appendix `ForMathlib/Entropy.lean`.
The chain is assembled in stages: the mutual-information identity
$I(Z; J) = \log M - H(J \mid Z)$ under the uniform prior (`mutualInformation_toReal_eq`, a pure
Radon–Nikodym computation) and the conditional-entropy bound
$H(J \mid Z) \le \log 2 + q\,\log M$ with $q$ the testing error (`condEntropy_le_fano`, the
information-theoretic crux, built from the pointwise discrete Fano inequality
`discrete_fano_pointwise`, the sub-probability entropy bound `negMulLog_sum_le_card`, and the
MAP/Bayes-risk identity `mapError_integral_le`) combine in `fano_real` to the real-valued chain
$\log M \le I + \log 2 + q\,\log M$. The wrapper `fano_entropy_continuous` discharges the
`ℝ≥0∞` bookkeeping (the `⊤` cases and the `ENNReal.ofReal` push-through), and `fano_inequality`
performs the division rearrangement into $1 - (I + \log 2)/\log M \le q$. The minimax bound
multiplies through by $\Phi(\delta)$ and applies the estimation-to-testing reduction
(`minimax_ge_testing_error`).

**Bibliographic comments.** Fano's inequality is classical information theory, originating with
R. M. Fano, *Transmission of Information: A Statistical Theory of Communications*, MIT Press and
Wiley, 1961 (and standard in T. M. Cover and J. A. Thomas, *Elements of Information Theory*,
Wiley). Its use as a device for statistical minimax lower bounds traces to R. Z. Has'minskii,
"A lower bound on the risks of nonparametric estimates of densities in the uniform metric,"
*Theory of Probability and Its Applications* 23 (1978), 794–798, and to the systematic
development by L. Birgé, "Approximation dans les espaces métriques et théorie de l'estimation,"
*Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete* 65 (1983), 181–237. The
synthesis of the Fano, Assouad, and Le Cam methods presented in Wainwright's §15.3 follows the
influential survey of B. Yu, "Assouad, Fano, and Le Cam," in *Festschrift for Lucien Le Cam:
Research Papers in Probability and Statistics* (D. Pollard, E. Torgersen, G. L. Yang, eds.),
Springer, New York, 1997, pp. 423–435, which is the standard reference for the testing-reduction
formulation of Eq. (15.31)–(15.32) formalized here.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- Pointwise expansion of `negMulLog` under the uniform-prior rescaling `x ↦ M⁻¹ · x` (with
`x = (dQⱼ/dμ)(z) ≥ 0` the component density against the mixture). The identity
`negMulLog (M⁻¹ x) = M⁻¹ (log M) x − M⁻¹ (x log x)` is the per-`j`, per-`z` algebra that turns the
posterior entropy `∑ⱼ negMulLog (M⁻¹ rⱼ)` into `log M − M⁻¹ ∑ⱼ rⱼ log rⱼ` (after using
`∑ⱼ rⱼ = M`). The `x = 0` boundary is consistent because `negMulLog 0 = 0 = 0·log 0`. -/
private lemma negMulLog_inv_mul {M : ℕ} (hM : (M : ℝ) ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog ((M : ℝ)⁻¹ * x)
      = (M : ℝ)⁻¹ * Real.log (M : ℝ) * x - (M : ℝ)⁻¹ * (x * Real.log x) := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0]; simp
  · simp only [Real.negMulLog_def]
    rw [Real.log_mul (inv_ne_zero hM) hx0.ne', Real.log_inv]
    ring

/-- Radon–Nikodym derivative of a finite sum of finite measures splits over the sum, a.e. against a
common dominating measure. (Local copy of the same fact used in `Fano/MutualInformation.lean`;
proved by induction from the two-term `rnDeriv_add'`.) -/
private lemma rnDeriv_finset_sum_ae {α : Type*} [MeasurableSpace α] {ι : Type*} (s : Finset ι)
    (P : ι → Measure α) (ξ : Measure α) [SigmaFinite ξ] [∀ i, IsFiniteMeasure (P i)] :
    (∑ i ∈ s, P i).rnDeriv ξ =ᵐ[ξ] ∑ i ∈ s, (P i).rnDeriv ξ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Measure.rnDeriv_add' (P i) (∑ k ∈ s, P k) ξ, ih] with x h1 h2
      rw [Finset.sum_insert hi, Pi.add_apply, h1, Pi.add_apply, h2]

/-- **Conditional Shannon entropy `H(J | Z)`** of the M-ary testing problem, built concretely from
the component densities `rⱼ(z) = d(Q j)/d(mixture Q)(z)`. With the uniform prior the posterior mass
is `ℙ(J = j | Z = z) = M⁻¹ rⱼ(z)`, so
`H(J | Z) = ∫ z, ∑ⱼ negMulLog (M⁻¹ rⱼ(z)) ∂(mixture Q)`. This is `H(J|Z)` of Wainwright's
appendix (Def. 15.25 specialised to the testing posterior), phrased without the `posterior` kernel
so that the mutual-information identity below is a pure Radon–Nikodym computation. -/
private noncomputable def condEntropy {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) : ℝ :=
  ∫ z, (∑ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)) ∂(mixture Q)

/-- **Mutual-information identity** `I(Z; J) = H(J) − H(J | Z) = log M − H(J | Z)` (Wainwright
Eq. (15.60d) with the uniform prior, so `H(J) = log M`). The genuinely-mechanical half of the
entropy form of Fano's inequality: it is a Radon–Nikodym computation, needing only that the mutual
information is finite (so every `klDiv (Q j) (mixture Q)` is finite, i.e. each component is
absolutely continuous with integrable log-likelihood ratio against the mixture).

The proof expands `(mutualInformation Q).toReal = M⁻¹ ∑ⱼ (klDiv (Q j) (mixture Q)).toReal`, writes
each `(klDiv (Q j) (mixture Q)).toReal = ∫ rⱼ log rⱼ ∂(mixture Q)` via
`toReal_klDiv_of_measure_eq` and the change of variables `integral_rnDeriv_smul`, and matches it
against `condEntropy` after the pointwise `negMulLog_inv_mul` expansion and the a.e. identity
`∑ⱼ rⱼ = M`. -/
private lemma mutualInformation_toReal_eq {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧)
    [IsMarkovKernel Q] (hI : mutualInformation Q ≠ ⊤) :
    (mutualInformation Q).toReal = Real.log (M : ℝ) - condEntropy Q := by
  classical
  haveI hμprob : IsProbabilityMeasure (mixture Q) := by unfold mixture; infer_instance
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMne : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  have hMinv_ne : (M : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMtop
  -- each component is absolutely continuous w.r.t. the mixture
  have hac : ∀ j, Q j ≪ mixture Q := fun j => by
    rw [mixture_eq_inv_smul_sum]
    exact (Measure.absolutelyContinuous_of_le
      (Finset.single_le_sum (f := fun k => Q k) (fun i _ => Measure.zero_le _)
        (Finset.mem_univ j))).smul_right hMinv_ne
  -- finiteness of the mutual information forces every KL term finite
  have hsum_ne : (∑ j, klDiv (Q j) (mixture Q)) ≠ ⊤ := by
    intro hcon; exact hI (by rw [mutualInformation, hcon, ENNReal.mul_top hMinv_ne])
  have hfin : ∀ j, klDiv (Q j) (mixture Q) ≠ ⊤ := fun j hcon =>
    hsum_ne (top_le_iff.mp (hcon ▸ Finset.single_le_sum
      (f := fun k => klDiv (Q k) (mixture Q)) (fun i _ => zero_le) (Finset.mem_univ j)))
  have hint : ∀ j, Integrable (llr (Q j) (mixture Q)) (Q j) := fun j =>
    (klDiv_ne_top_iff.mp (hfin j)).2
  -- per-component integrability of `rⱼ log rⱼ` against the mixture
  have hintμ : ∀ j, Integrable (fun z => ((Q j).rnDeriv (mixture Q) z).toReal *
      Real.log ((Q j).rnDeriv (mixture Q) z).toReal) (mixture Q) := fun j =>
    (integrable_rnDeriv_mul_log_iff (hac j)).mpr (hint j)
  -- each KL term, in real form, is `∫ rⱼ log rⱼ` against the mixture
  have hklj : ∀ j, (klDiv (Q j) (mixture Q)).toReal = ∫ z, ((Q j).rnDeriv (mixture Q) z).toReal *
      Real.log ((Q j).rnDeriv (mixture Q) z).toReal ∂(mixture Q) := by
    intro j
    haveI : IsProbabilityMeasure (Q j) := inferInstance
    rw [toReal_klDiv_of_measure_eq (hac j) (by rw [measure_univ, measure_univ]),
      ← integral_rnDeriv_smul (hac j)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    simp only [llr_def, smul_eq_mul]
  -- the real form of the mutual information
  have hMItoReal : (mutualInformation Q).toReal
      = (M : ℝ)⁻¹ * ∑ j, (klDiv (Q j) (mixture Q)).toReal := by
    rw [mutualInformation, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_sum (fun j _ => hfin j)]
  -- the component densities sum to `M`, a.e. against the mixture (ℝ≥0∞ form)
  have hsum_ennreal : (fun z => ∑ k, (Q k).rnDeriv (mixture Q) z)
      =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
    have hS : (M : ℝ≥0∞) • mixture Q = ∑ k, Q k := by
      rw [mixture_eq_inv_smul_sum, smul_smul, ENNReal.mul_inv_cancel hMne hMtop, one_smul]
    have h1 := rnDeriv_finset_sum_ae (Finset.univ : Finset (Fin M)) (fun k => Q k) (mixture Q)
    have h2 : (∑ k, Q k).rnDeriv (mixture Q) =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
      rw [← hS]
      filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (mixture Q) (mixture Q) hMtop,
        Measure.rnDeriv_self (mixture Q)] with x hx hx2
      simp [hx, Pi.smul_apply, hx2]
    filter_upwards [h1, h2] with z e1 e2
    rw [← Finset.sum_apply, ← e1, e2]
  have htop : ∀ᵐ z ∂(mixture Q), ∀ k, (Q k).rnDeriv (mixture Q) z ≠ ∞ := by
    rw [ae_all_iff]; intro k; exact Measure.rnDeriv_ne_top (Q k) (mixture Q)
  -- the real (toReal) form of the sum identity
  have hsumR : (fun z => ∑ j, ((Q j).rnDeriv (mixture Q) z).toReal) =ᵐ[mixture Q]
      fun _ => (M : ℝ) := by
    filter_upwards [hsum_ennreal, htop] with z hz hzt
    rw [← ENNReal.toReal_sum (fun k _ => hzt k), hz, ENNReal.toReal_natCast]
  -- pointwise: the posterior entropy integrand equals `log M − M⁻¹ ∑ⱼ rⱼ log rⱼ`
  have hpt : (fun z => ∑ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal))
      =ᵐ[mixture Q] fun z => Real.log (M : ℝ) - (M : ℝ)⁻¹ * ∑ j,
        (((Q j).rnDeriv (mixture Q) z).toReal * Real.log ((Q j).rnDeriv (mixture Q) z).toReal) := by
    filter_upwards [hsumR] with z hz
    have key : ∀ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)
        = (M : ℝ)⁻¹ * Real.log (M : ℝ) * ((Q j).rnDeriv (mixture Q) z).toReal
          - (M : ℝ)⁻¹ * (((Q j).rnDeriv (mixture Q) z).toReal
            * Real.log ((Q j).rnDeriv (mixture Q) z).toReal) :=
      fun j => negMulLog_inv_mul hMr ENNReal.toReal_nonneg
    rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hz,
      show (M : ℝ)⁻¹ * Real.log (M : ℝ) * (M : ℝ) = Real.log (M : ℝ) from by
        rw [mul_comm ((M : ℝ)⁻¹) (Real.log (M : ℝ)), mul_assoc, inv_mul_cancel₀ hMr, mul_one]]
  -- assemble: integrate the pointwise identity and recognise the KL terms
  have hcond : condEntropy Q
      = Real.log (M : ℝ) - (M : ℝ)⁻¹ * ∑ j, (klDiv (Q j) (mixture Q)).toReal := by
    have hg_int : Integrable (fun z => (M : ℝ)⁻¹ * ∑ j,
        (((Q j).rnDeriv (mixture Q) z).toReal * Real.log ((Q j).rnDeriv (mixture Q) z).toReal))
        (mixture Q) :=
      (integrable_finset_sum Finset.univ (fun j _ => hintμ j)).const_mul _
    have hconst : ∫ _z, Real.log (M : ℝ) ∂(mixture Q) = Real.log (M : ℝ) := by
      simp
    rw [condEntropy, integral_congr_ae hpt, integral_sub (integrable_const _) hg_int, hconst,
      integral_const_mul, integral_finset_sum _ (fun j _ => hintμ j),
      Finset.sum_congr rfl (fun j _ => (hklj j).symm)]
  rw [hMItoReal, hcond]; ring

/-- **Sub-probability entropy bound.** For nonnegative weights `p` on a nonempty finite set `s` with
total mass `S = ∑ᵢ pᵢ`, the unnormalised entropy is bounded by `negMulLog S + S·log|s|`. This is the
`log|𝒳|` entropy bound (Wainwright Exercise 15.2b) in sub-probability form: dividing by `S` to make
`p/S` a pmf on `s` and using Jensen for `negMulLog` (concave on `[0,∞)`) with uniform weights
`1/|s|`. Used to control the conditional entropy on the `M−1` non-maximal outcomes in the pointwise
discrete Fano inequality. -/
private lemma negMulLog_sum_le_card {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hs : s.Nonempty) :
    ∑ i ∈ s, Real.negMulLog (p i)
      ≤ Real.negMulLog (∑ i ∈ s, p i) + (∑ i ∈ s, p i) * Real.log (s.card) := by
  classical
  have hNpos : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hNne : (s.card : ℝ) ≠ 0 := ne_of_gt hNpos
  set S := ∑ i ∈ s, p i with hS
  -- Jensen for `negMulLog` with uniform weights `1/|s|`.
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := s) (w := fun _ => 1 / (s.card : ℝ)) (p := p)
    (fun i _ => by positivity)
    (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => hp i hi)
  have hsum_w : ∑ i ∈ s, (1 / (s.card : ℝ)) • p i = (1 / (s.card : ℝ)) * S := by
    simp only [smul_eq_mul, ← Finset.mul_sum, ← hS]
  have hsum_L : ∑ i ∈ s, (1 / (s.card : ℝ)) • Real.negMulLog (p i)
      = (1 / (s.card : ℝ)) * ∑ i ∈ s, Real.negMulLog (p i) := by
    simp only [smul_eq_mul, ← Finset.mul_sum]
  rw [hsum_w, hsum_L] at hjensen
  -- Multiply through by `|s|`.
  have key : ∑ i ∈ s, Real.negMulLog (p i)
      ≤ (s.card : ℝ) * Real.negMulLog ((1 / (s.card : ℝ)) * S) := by
    have h2 := mul_le_mul_of_nonneg_left hjensen hNpos.le
    rwa [← mul_assoc, mul_one_div, div_self hNne, one_mul] at h2
  refine le_trans key (le_of_eq ?_)
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun i hi => hp i hi) : (0 : ℝ) ≤ S) with hS0 | hS0
  · rw [show S = 0 from hS0.symm]; simp [Real.negMulLog_def]
  · have hNne' : (1 : ℝ) / (s.card : ℝ) ≠ 0 := by positivity
    simp only [Real.negMulLog_def]
    rw [Real.log_mul hNne' (ne_of_gt hS0), one_div, Real.log_inv]
    field_simp
    ring

/-- **Pointwise discrete Fano inequality.** For a probability mass function `p` on `Fin M`
(`M ≥ 2`), the Shannon entropy is bounded by `log 2 + (1 − maxⱼ pⱼ)·log M`. This is the crude form
of Wainwright's Fano chain `H(p) ≤ h(e) + e·log(M−1)` with `e = 1 − maxⱼ pⱼ`: split off the maximal
outcome `j*` (giving the binary entropy `binEntropy e = negMulLog (p j*) + negMulLog e`), bound the
conditional entropy of the remaining `M−1` outcomes by `e·log(M−1)` via `negMulLog_sum_le_card`, and
relax `binEntropy e ≤ log 2` (`Real.binEntropy_le_log_two`) and `log(M−1) ≤ log M`. -/
private lemma discrete_fano_pointwise {M : ℕ} (hM : 2 ≤ M) (p : Fin M → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1) :
    ∑ j, Real.negMulLog (p j) ≤ Real.log 2 + (1 - ⨆ j, p j) * Real.log (M : ℝ) := by
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  obtain ⟨js, hjs⟩ := Finite.exists_max p
  have hbdd : BddAbove (Set.range p) := Set.Finite.bddAbove (Set.finite_range p)
  have hsup : (⨆ j, p j) = p js := le_antisymm (ciSup_le hjs) (le_ciSup hbdd js)
  rw [hsup]
  set m := p js with hm
  have hm1 : m ≤ 1 := by
    rw [hm, ← hp1]; exact Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ js)
  have he0 : (0 : ℝ) ≤ 1 - m := by linarith
  have hsplit : ∑ j, Real.negMulLog (p j)
      = Real.negMulLog m + ∑ j ∈ Finset.univ.erase js, Real.negMulLog (p j) := by
    rw [hm]
    exact (Finset.add_sum_erase Finset.univ (fun j => Real.negMulLog (p j))
      (Finset.mem_univ js)).symm
  have hSe : ∑ j ∈ Finset.univ.erase js, p j = 1 - m := by
    have h := Finset.add_sum_erase Finset.univ p (Finset.mem_univ js)
    rw [hp1] at h; rw [hm]; linarith [h]
  have hcard : (Finset.univ.erase js).card = M - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ js), Finset.card_univ, Fintype.card_fin]
  have hne : (Finset.univ.erase js).Nonempty := by
    rw [← Finset.card_pos, hcard]; omega
  have hsub := negMulLog_sum_le_card (Finset.univ.erase js) p (fun i _ => hp0 i) hne
  rw [hSe, hcard] at hsub
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hcast] at hsub
  have hbin : Real.negMulLog m + Real.negMulLog (1 - m) = Real.binEntropy (1 - m) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub (1 - m),
      show (1 : ℝ) - (1 - m) = m from by ring]
    ring
  have hb2 : Real.binEntropy (1 - m) ≤ Real.log 2 := Real.binEntropy_le_log_two
  have hMge : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogle : Real.log ((M : ℝ) - 1) ≤ Real.log (M : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hprod : (1 - m) * Real.log ((M : ℝ) - 1) ≤ (1 - m) * Real.log (M : ℝ) :=
    mul_le_mul_of_nonneg_left hlogle he0
  rw [hsplit]
  calc Real.negMulLog m + ∑ j ∈ Finset.univ.erase js, Real.negMulLog (p j)
      ≤ Real.negMulLog m + (Real.negMulLog (1 - m) + (1 - m) * Real.log ((M : ℝ) - 1)) := by
        linarith [hsub]
    _ = Real.binEntropy (1 - m) + (1 - m) * Real.log ((M : ℝ) - 1) := by rw [← hbin]; ring
    _ ≤ Real.log 2 + (1 - m) * Real.log (M : ℝ) := by linarith [hb2, hprod]

/-- **Pointwise MAP/Bayes-error bound.** For a posterior pmf `p` on `Fin M` (`∑ⱼ pⱼ = 1`, each
`pⱼ < ∞`) and any sub-probability decision weights `b` with `∑ⱼ bⱼ = 1`, `bⱼ ≤ 1` (the test mass
`bⱼ = κ(z){j}`), the pointwise MAP error `1 − maxⱼ pⱼ` is at most the posterior-weighted `0–1` loss
`∑ⱼ pⱼ(1 − bⱼ)`. This is the per-`z` core of `mapError_integral_le`: the MAP test (which always
guesses `argmaxⱼ pⱼ`) attains the smallest possible posterior error, so any test's error dominates
it. The bound is `∑ⱼ pⱼ bⱼ ≤ (maxⱼ pⱼ)·∑ⱼ bⱼ = maxⱼ pⱼ`. -/
private lemma map_error_pointwise {M : ℕ} (hM : 0 < M)
    (p b : Fin M → ℝ≥0∞) (hp_top : ∀ j, p j ≠ ⊤) (hp_sum : ∑ j, p j = 1)
    (hb_le : ∀ j, b j ≤ 1) (hb_sum : ∑ j, b j = 1) :
    ENNReal.ofReal (1 - ⨆ j, (p j).toReal) ≤ ∑ j, p j * (1 - b j) := by
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  obtain ⟨js, hjs⟩ := Finite.exists_max (fun j => (p j).toReal)
  have hbdd : BddAbove (Set.range fun j => (p j).toReal) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hsup : (⨆ j, (p j).toReal) = (p js).toReal :=
    le_antisymm (ciSup_le hjs) (le_ciSup hbdd js)
  have hpjs1 : p js ≤ 1 :=
    (Finset.single_le_sum (f := p) (fun i _ => zero_le) (Finset.mem_univ js)).trans hp_sum.le
  have hpj_le : ∀ j, p j ≤ p js := fun j =>
    (ENNReal.toReal_le_toReal (hp_top j) (hp_top js)).mp (hjs j)
  have hLHS : ENNReal.ofReal (1 - ⨆ j, (p j).toReal) = 1 - p js := by
    rw [hsup]
    have h1 : ((1 : ℝ≥0∞) - p js).toReal = 1 - (p js).toReal := by
      rw [ENNReal.toReal_sub_of_le hpjs1 ENNReal.one_ne_top, ENNReal.toReal_one]
    rw [← h1, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
  rw [hLHS, tsub_le_iff_right]
  have expand : ∀ j, p j * (1 - b j) + p j * b j = p j := fun j => by
    rw [← mul_add, tsub_add_cancel_of_le (hb_le j), mul_one]
  calc (1 : ℝ≥0∞) = ∑ j, p j := hp_sum.symm
    _ = ∑ j, (p j * (1 - b j) + p j * b j) := Finset.sum_congr rfl (fun j _ => (expand j).symm)
    _ = ∑ j, p j * (1 - b j) + ∑ j, p j * b j := Finset.sum_add_distrib
    _ ≤ ∑ j, p j * (1 - b j) + p js := by
        gcongr
        calc ∑ j, p j * b j ≤ ∑ j, p js * b j :=
              Finset.sum_le_sum (fun j _ => by gcongr; exact hpj_le j)
          _ = p js * ∑ j, b j := (Finset.mul_sum _ _ _).symm
          _ = p js := by rw [hb_sum, mul_one]

/-- **MAP / Bayes-risk identity** (the genuinely information-theoretic crux of the
conditional-entropy Fano bound). The integral over the mixture of the pointwise Bayes/MAP error
`e(z) = 1 − maxⱼ ℙ(J = j | Z = z) = 1 − maxⱼ M⁻¹ rⱼ(z)` is at most the M-ary testing error, i.e. the
Bayes risk of the `0–1` loss under the uniform prior. (Equality holds — the MAP test attains the
Bayes risk — but only the `≤` direction is needed for the entropy bound.)

Proof. Reduce `bayesRisk` to its `iInf` form: for any Markov `κ : 𝓧 → Fin M`, the posterior-weighted
`0–1` loss `avgRisk (zeroOneLoss M) Q κ (uniformPrior M) = ∫⁻ z, ∑ⱼ M⁻¹rⱼ(z)·κ(z){j}ᶜ ∂(mixture Q)`
dominates `∫⁻ ENNReal.ofReal e` pointwise (`map_error_pointwise`), hence `∫ e ≤ ⨅κ avgRisk =
multiwayTestingError Q`. The `0–1` Bayes risk is `≤ 1 ≠ ⊤`, supplying the `toReal` conversion. -/
private lemma mapError_integral_le {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (hM : 2 ≤ M) :
    ∫ z, (1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) ∂(mixture Q)
      ≤ (multiwayTestingError Q).toReal := by
  classical
  haveI hμprob : IsProbabilityMeasure (mixture Q) := by unfold mixture; infer_instance
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMne : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  have hMinv_ne : (M : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMtop
  haveI : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  -- each component is absolutely continuous w.r.t. the mixture
  have hac : ∀ j, Q j ≪ mixture Q := fun j => by
    rw [mixture_eq_inv_smul_sum]
    exact (Measure.absolutelyContinuous_of_le
      (Finset.single_le_sum (f := fun k => Q k) (fun i _ => Measure.zero_le _)
        (Finset.mem_univ j))).smul_right hMinv_ne
  -- the component densities sum to `M` a.e. against the mixture (ℝ≥0∞ form), and are finite a.e.
  have hsum_ennreal : (fun z => ∑ k, (Q k).rnDeriv (mixture Q) z)
      =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
    have hS : (M : ℝ≥0∞) • mixture Q = ∑ k, Q k := by
      rw [mixture_eq_inv_smul_sum, smul_smul, ENNReal.mul_inv_cancel hMne hMtop, one_smul]
    have h1 := rnDeriv_finset_sum_ae (Finset.univ : Finset (Fin M)) (fun k => Q k) (mixture Q)
    have h2 : (∑ k, Q k).rnDeriv (mixture Q) =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
      rw [← hS]
      filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (mixture Q) (mixture Q) hMtop,
        Measure.rnDeriv_self (mixture Q)] with x hx hx2
      simp [hx, Pi.smul_apply, hx2]
    filter_upwards [h1, h2] with z e1 e2
    rw [← Finset.sum_apply, ← e1, e2]
  have htop : ∀ᵐ z ∂(mixture Q), ∀ k, (Q k).rnDeriv (mixture Q) z ≠ ∞ := by
    rw [ae_all_iff]; intro k; exact Measure.rnDeriv_ne_top (Q k) (mixture Q)
  have hsumR : (fun z => ∑ j, ((Q j).rnDeriv (mixture Q) z).toReal) =ᵐ[mixture Q]
      fun _ => (M : ℝ) := by
    filter_upwards [hsum_ennreal, htop] with z hz hzt
    rw [← ENNReal.toReal_sum (fun k _ => hzt k), hz, ENNReal.toReal_natCast]
  -- a.e. the maximal posterior mass lies in `[0, 1]`, so the MAP error `e(z)` is in `[0, 1]`
  have hp_ae : ∀ᵐ z ∂(mixture Q),
      ∑ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal = 1 := by
    filter_upwards [hsumR] with z hz
    rw [← Finset.mul_sum, hz, inv_mul_cancel₀ hMr]
  have hsup_ae : ∀ᵐ z ∂(mixture Q),
      (0 ≤ ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)
        ∧ (⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) ≤ 1 := by
    filter_upwards [hp_ae] with z hz
    have hp0 : ∀ j, 0 ≤ (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal := fun j => by positivity
    have hbdd : BddAbove (Set.range fun j => (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) :=
      Set.Finite.bddAbove (Set.finite_range _)
    refine ⟨le_trans (hp0 ⟨0, by omega⟩) (le_ciSup hbdd ⟨0, by omega⟩), ?_⟩
    refine ciSup_le fun j => ?_
    calc (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal
        ≤ ∑ k, (M : ℝ)⁻¹ * ((Q k).rnDeriv (mixture Q) z).toReal :=
          Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ j)
      _ = 1 := hz
  -- measurability and integrability of the MAP error `e(z) = 1 − maxⱼ M⁻¹rⱼ(z)`
  have h_meas_sup : Measurable fun z =>
      ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal :=
    Measurable.iSup fun j =>
      ((Measure.measurable_rnDeriv (Q j) (mixture Q)).ennreal_toReal).const_mul _
  have h_sup_int : Integrable
      (fun z => ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) (mixture Q) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) h_meas_sup.aestronglyMeasurable ?_
    filter_upwards [hsup_ae] with z hz
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.1, hz.2], hz.2⟩
  have h_ebar_int : Integrable
      (fun z => 1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) (mixture Q) :=
    (integrable_const (1 : ℝ)).sub h_sup_int
  have h_ebar_nonneg : (0 : 𝓧 → ℝ) ≤ᵐ[mixture Q]
      fun z => 1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal := by
    filter_upwards [hsup_ae] with z hz
    simp only [Pi.zero_apply]
    linarith [hz.2]
  -- the per-index uniform-prior mass is `M⁻¹`
  have hpt : ∀ k : Fin M, (uniformPrior M) {k} = (M : ℝ≥0∞)⁻¹ := by
    intro k
    rw [uniformPrior, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
  -- the `0–1` Bayes risk is `≤ 1`, hence finite
  have hq1 : multiwayTestingError Q ≤ 1 := by
    rw [multiwayTestingError]
    refine (bayesRisk_le_avgRisk (zeroOneLoss M) Q
      (Kernel.const 𝓧 (Measure.dirac (Classical.arbitrary (Fin M)))) (uniformPrior M)).trans ?_
    set κ0 := Kernel.const 𝓧 (Measure.dirac (Classical.arbitrary (Fin M))) with hκ0
    haveI : IsMarkovKernel (κ0 ∘ₖ Q) := by infer_instance
    rw [avgRisk]
    calc ∫⁻ j, ∫⁻ y, zeroOneLoss M j y ∂((κ0 ∘ₖ Q) j) ∂(uniformPrior M)
        ≤ ∫⁻ _j, 1 ∂(uniformPrior M) := by
          refine lintegral_mono fun j => ?_
          calc ∫⁻ y, zeroOneLoss M j y ∂((κ0 ∘ₖ Q) j)
              ≤ ∫⁻ _y, 1 ∂((κ0 ∘ₖ Q) j) := by
                refine lintegral_mono fun y => ?_
                unfold zeroOneLoss; split <;> simp
            _ = 1 := by rw [lintegral_one, measure_univ]
      _ = 1 := by rw [lintegral_one, measure_univ]
  have hqne : multiwayTestingError Q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq1
  -- avgRisk of any Markov test, in mixture-integral form
  have havg : ∀ (κ : Kernel 𝓧 (Fin M)), IsMarkovKernel κ →
      avgRisk (zeroOneLoss M) Q κ (uniformPrior M)
        = ∫⁻ z, ∑ j, ((Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ) * (M : ℝ≥0∞)⁻¹
            ∂(mixture Q) := by
    intro κ hκ
    haveI := hκ
    have hmeas : ∀ j, Measurable fun z => (Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ :=
      fun j => (Measure.measurable_rnDeriv (Q j) (mixture Q)).mul
        (Kernel.measurable_coe κ (measurableSet_singleton j).compl)
    have hinner : ∀ j : Fin M, ∫⁻ y, zeroOneLoss M j y ∂((κ ∘ₖ Q) j)
        = ∫⁻ z, (Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ ∂(mixture Q) := by
      intro j
      have hmc : Measurable fun z => (κ z) ({j}ᶜ) :=
        Kernel.measurable_coe κ (measurableSet_singleton j).compl
      have e1 : ∀ z, ∫⁻ y, zeroOneLoss M j y ∂(κ z) = (κ z) {j}ᶜ := by
        intro z
        have hind : (fun y => zeroOneLoss M j y) = Set.indicator {j}ᶜ (1 : Fin M → ℝ≥0∞) := by
          funext y
          by_cases h : j = y
          · subst h
            simp [zeroOneLoss, Set.mem_compl_iff, Set.mem_singleton_iff]
          · simp [zeroOneLoss, Set.mem_compl_iff, Set.mem_singleton_iff, h, Ne.symm h]
        rw [hind, lintegral_indicator_one (measurableSet_singleton j).compl]
      rw [Kernel.comp_apply,
        Measure.lintegral_bind κ.aemeasurable (measurable_of_countable _).aemeasurable]
      simp_rw [e1]
      exact (lintegral_rnDeriv_mul (hac j) hmc.aemeasurable).symm
    have step : ∀ j, (∫⁻ z, (Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ ∂(mixture Q)) * (M : ℝ≥0∞)⁻¹
        = ∫⁻ z, ((Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ) * (M : ℝ≥0∞)⁻¹ ∂(mixture Q) :=
      fun j => (lintegral_mul_const _ (hmeas j)).symm
    unfold avgRisk
    calc ∫⁻ j, ∫⁻ y, zeroOneLoss M j y ∂((κ ∘ₖ Q) j) ∂(uniformPrior M)
        = ∫⁻ j, (∫⁻ z, (Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ ∂(mixture Q))
            ∂(uniformPrior M) := lintegral_congr hinner
      _ = ∑ j, (∫⁻ z, (Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ ∂(mixture Q))
            * (uniformPrior M) {j} := lintegral_fintype _
      _ = ∑ j, (∫⁻ z, (Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ ∂(mixture Q)) * (M : ℝ≥0∞)⁻¹ := by
          simp_rw [hpt]
      _ = ∑ j, ∫⁻ z, ((Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ) * (M : ℝ≥0∞)⁻¹ ∂(mixture Q) := by
          simp_rw [step]
      _ = ∫⁻ z, ∑ j, ((Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ) * (M : ℝ≥0∞)⁻¹ ∂(mixture Q) :=
          (lintegral_finset_sum _ (fun j _ => (hmeas j).mul_const _)).symm
  -- `ENNReal.ofReal (∫ e) ≤ ⨅κ avgRisk = multiwayTestingError Q`
  have hkey : ENNReal.ofReal
      (∫ z, (1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) ∂(mixture Q))
        ≤ multiwayTestingError Q := by
    rw [ofReal_integral_eq_lintegral_ofReal h_ebar_int h_ebar_nonneg, multiwayTestingError,
      bayesRisk]
    refine le_iInf₂ (fun κ hκ => ?_)
    haveI := hκ
    rw [havg κ hκ]
    refine lintegral_mono_ae ?_
    filter_upwards [hsum_ennreal, htop] with z hz hzt
    haveI : IsProbabilityMeasure (κ z) := inferInstance
    have hp_top : ∀ j, (M : ℝ≥0∞)⁻¹ * (Q j).rnDeriv (mixture Q) z ≠ ⊤ :=
      fun j => ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hMne) (hzt j)
    have hp_sum : ∑ j, (M : ℝ≥0∞)⁻¹ * (Q j).rnDeriv (mixture Q) z = 1 := by
      rw [← Finset.mul_sum, hz, ENNReal.inv_mul_cancel hMne hMtop]
    have hb_le : ∀ j, (κ z) {j} ≤ 1 := fun _ => prob_le_one
    have hb_sum : ∑ j, (κ z) {j} = 1 := by
      rw [sum_measure_singleton, Finset.coe_univ, measure_univ]
    have hpconv : ∀ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal
        = ((M : ℝ≥0∞)⁻¹ * (Q j).rnDeriv (mixture Q) z).toReal := by
      intro j; rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    have hRHSconv : ∀ j, ((Q j).rnDeriv (mixture Q) z * (κ z) {j}ᶜ) * (M : ℝ≥0∞)⁻¹
        = ((M : ℝ≥0∞)⁻¹ * (Q j).rnDeriv (mixture Q) z) * (1 - (κ z) {j}) := by
      intro j; rw [prob_compl_eq_one_sub (measurableSet_singleton j)]; ring
    simp_rw [hpconv, hRHSconv]
    exact map_error_pointwise (by omega)
      (fun j => (M : ℝ≥0∞)⁻¹ * (Q j).rnDeriv (mixture Q) z)
      (fun j => (κ z) {j}) hp_top hp_sum hb_le hb_sum
  exact (ENNReal.ofReal_le_iff_le_toReal hqne).mp hkey

/-- **Conditional-entropy Fano inequality** (Wainwright Eq. (15.61), the genuinely-deep
information-theoretic half): the posterior entropy `H(J | Z)` is controlled by the testing error,
```
H(J | Z) ≤ log 2 + q · log M,        q = multiwayTestingError Q.
```
This is the single named residual of the Fano lower bound. (The other half — the mutual-information
identity `I = log M − H(J | Z)` — is fully proved in `mutualInformation_toReal_eq`, and the
surrounding `ℝ≥0∞` bookkeeping in `fano_entropy_continuous` / the division rearrangement in
`fano_inequality`.) The hypothesis `q ≠ ⊤` is genuine: for `q = ⊤` the bound (with `q.toReal = 0`)
would read `H(J|Z) ≤ log 2`, false for large `M`; it is supplied by the finite branch of
`fano_entropy_continuous` (and in fact always holds, the Bayes risk of the `0–1` loss being `≤ 1`).

TODO(mmx, named debt — strictly smaller than the former whole-crux `fano_real`): prove the sharp
Fano chain `H(J | Z) ≤ h(e) + e·log(M−1) ≤ log 2 + q·log M`, where `e(z) = 1 − maxⱼ ℙ(J=j|Z=z)` is
the pointwise MAP error. The route: (i) a pointwise discrete Fano `∑ⱼ negMulLog pⱼ ≤ binEntropy (1 −
maxⱼ pⱼ) + (1 − maxⱼ pⱼ)·log (M−1)` for a pmf `p` on `Fin M`; (ii) integrate over `mixture Q`,
using concavity of `Real.binEntropy` (Jensen) to pull `∫ binEntropy (e z) ≤ binEntropy (∫ e z)`;
(iii) identify `∫ e z ∂(mixture Q) = multiwayTestingError Q` (the MAP test attains the Bayes risk of
the `0–1` loss); (iv) close with `Real.binEntropy_le_log_two` and `log (M−1) ≤ log M`. -/
private lemma condEntropy_le_fano {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (hM : 2 ≤ M) (hq : multiwayTestingError Q ≠ ⊤) :
    condEntropy Q ≤ Real.log 2 + (multiwayTestingError Q).toReal * Real.log (M : ℝ) := by
  classical
  haveI hμprob : IsProbabilityMeasure (mixture Q) := by unfold mixture; infer_instance
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMne : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hMtop : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top M
  have hMinv_ne : (M : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hMtop
  -- each component is absolutely continuous w.r.t. the mixture (so the densities sum to `M` a.e.)
  have hac : ∀ j, Q j ≪ mixture Q := fun j => by
    rw [mixture_eq_inv_smul_sum]
    exact (Measure.absolutelyContinuous_of_le
      (Finset.single_le_sum (f := fun k => Q k) (fun i _ => Measure.zero_le _)
        (Finset.mem_univ j))).smul_right hMinv_ne
  have hsum_ennreal : (fun z => ∑ k, (Q k).rnDeriv (mixture Q) z)
      =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
    have hS : (M : ℝ≥0∞) • mixture Q = ∑ k, Q k := by
      rw [mixture_eq_inv_smul_sum, smul_smul, ENNReal.mul_inv_cancel hMne hMtop, one_smul]
    have h1 := rnDeriv_finset_sum_ae (Finset.univ : Finset (Fin M)) (fun k => Q k) (mixture Q)
    have h2 : (∑ k, Q k).rnDeriv (mixture Q) =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
      rw [← hS]
      filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (mixture Q) (mixture Q) hMtop,
        Measure.rnDeriv_self (mixture Q)] with x hx hx2
      simp [hx, Pi.smul_apply, hx2]
    filter_upwards [h1, h2] with z e1 e2
    rw [← Finset.sum_apply, ← e1, e2]
  have htop : ∀ᵐ z ∂(mixture Q), ∀ k, (Q k).rnDeriv (mixture Q) z ≠ ∞ := by
    rw [ae_all_iff]; intro k; exact Measure.rnDeriv_ne_top (Q k) (mixture Q)
  have hsumR : (fun z => ∑ j, ((Q j).rnDeriv (mixture Q) z).toReal) =ᵐ[mixture Q]
      fun _ => (M : ℝ) := by
    filter_upwards [hsum_ennreal, htop] with z hz hzt
    rw [← ENNReal.toReal_sum (fun k _ => hzt k), hz, ENNReal.toReal_natCast]
  -- pointwise: the posterior masses `M⁻¹ rⱼ(z)` form a pmf a.e.
  have hp_ae : ∀ᵐ z ∂(mixture Q),
      ∑ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal = 1 := by
    filter_upwards [hsumR] with z hz
    rw [← Finset.mul_sum, hz, inv_mul_cancel₀ hMr]
  -- a.e. the maximal posterior mass lies in `[0, 1]`
  have hsup_ae : ∀ᵐ z ∂(mixture Q),
      (0 ≤ ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)
        ∧ (⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) ≤ 1 := by
    filter_upwards [hp_ae] with z hz
    have hp0 : ∀ j, 0 ≤ (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal := fun j => by positivity
    have hbdd : BddAbove (Set.range fun j => (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) :=
      Set.Finite.bddAbove (Set.finite_range _)
    have j0 : Fin M := ⟨0, by omega⟩
    refine ⟨le_trans (hp0 j0) (le_ciSup hbdd j0), ?_⟩
    refine ciSup_le fun j => ?_
    calc (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal
        ≤ ∑ k, (M : ℝ)⁻¹ * ((Q k).rnDeriv (mixture Q) z).toReal :=
          Finset.single_le_sum (fun k _ => hp0 k) (Finset.mem_univ j)
      _ = 1 := hz
  -- measurability and integrability of the maximal posterior mass
  have h_meas_sup : Measurable fun z =>
      ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal :=
    Measurable.iSup fun j =>
      ((Measure.measurable_rnDeriv (Q j) (mixture Q)).ennreal_toReal).const_mul _
  have h_sup_int : Integrable
      (fun z => ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) (mixture Q) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) h_meas_sup.aestronglyMeasurable ?_
    filter_upwards [hsup_ae] with z hz
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hz.1, hz.2], hz.2⟩
  have h_ebar_int : Integrable
      (fun z => 1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) (mixture Q) :=
    (integrable_const (1 : ℝ)).sub h_sup_int
  have hlogM_nonneg : (0 : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hRHS_nonneg : 0 ≤ Real.log 2 + (multiwayTestingError Q).toReal * Real.log (M : ℝ) :=
    add_nonneg (Real.log_nonneg (by norm_num)) (mul_nonneg ENNReal.toReal_nonneg hlogM_nonneg)
  rw [condEntropy]
  by_cases hF : Integrable
      (fun z => ∑ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)) (mixture Q)
  · have hFG : (fun z => ∑ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal))
        ≤ᵐ[mixture Q]
        fun z => Real.log 2 + (1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)
          * Real.log (M : ℝ) := by
      filter_upwards [hp_ae] with z hz
      exact discrete_fano_pointwise hM
        (fun j => (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal) (fun j => by positivity) hz
    calc ∫ z, (∑ j, Real.negMulLog ((M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)) ∂(mixture Q)
        ≤ ∫ z, (Real.log 2 + (1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)
            * Real.log (M : ℝ)) ∂(mixture Q) :=
          integral_mono_ae hF ((integrable_const _).add (h_ebar_int.mul_const _)) hFG
      _ = Real.log 2 + (∫ z, (1 - ⨆ j, (M : ℝ)⁻¹ * ((Q j).rnDeriv (mixture Q) z).toReal)
            ∂(mixture Q)) * Real.log (M : ℝ) := by
          rw [integral_add (integrable_const _) (h_ebar_int.mul_const _), integral_mul_const,
            integral_const, probReal_univ, one_smul]
      _ ≤ Real.log 2 + (multiwayTestingError Q).toReal * Real.log (M : ℝ) := by
          gcongr
          exact mapError_integral_le Q hM
  · rw [integral_undef hF]; exact hRHS_nonneg

/-- **Real-valued entropy form of Fano's inequality** (Wainwright Eq. (15.61)). Writing
`I = (I(Z;J)).toReal`, `q = (multiwayTestingError Q).toReal`, the mutual-information identity
`I = log M − H(J|Z)` (`mutualInformation_toReal_eq`) and the conditional-entropy Fano bound
`H(J|Z) ≤ log 2 + q·log M` (`condEntropy_le_fano`) combine to
```
log M ≤ I + log 2 + q · log M.
```
It is stated over `ℝ`; the `ℝ≥0∞` bookkeeping is discharged in `fano_entropy_continuous`, which
supplies the finiteness hypotheses `mutualInformation Q ≠ ⊤`, `multiwayTestingError Q ≠ ⊤` from its
`⊤`-case split. -/
private lemma fano_real {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    -- LEAN-ONLY: finiteness of the mutual information; supplied by `fano_entropy_continuous`'s
    -- `⊤`-branch split, no scope change (the `I = ⊤` case is handled there separately).
    (hI : mutualInformation Q ≠ ⊤)
    -- LEAN-ONLY: finiteness of the testing error; supplied by `fano_entropy_continuous`, no scope
    -- change (always holds, Bayes risk of the bounded `0–1` loss being `≤ 1`).
    (hq : multiwayTestingError Q ≠ ⊤)
    (hM : 2 ≤ M) :
    Real.log (M : ℝ)
      ≤ (mutualInformation Q).toReal + Real.log 2
          + (multiwayTestingError Q).toReal * Real.log (M : ℝ) := by
  have hid := mutualInformation_toReal_eq Q hI
  have hfano := condEntropy_le_fano Q hM hq
  linarith

/-- **Entropy form of Fano's inequality** (Wainwright Eq. (15.61)), packaged in the kernel-KL /
Bayes-risk encodings used by this module. Writing `L = log M`, `I = I(Z; J)`,
`q = multiwayTestingError Q` and `c = log 2`, the standard Fano chain
`H(J|Z) ≤ h(q) + q·log(M−1) ≤ log 2 + q·log M` together with `I = H(J) − H(J|Z) = log M − H(J|Z)`
rearranges to
```
log M ≤ I(Z; J) + log 2 + q · log M.
```
The genuinely-hard real-analytic content is isolated in `fano_real`; this wrapper discharges only
the `ℝ≥0∞` bookkeeping (the `⊤` cases and the `ENNReal.ofReal` push-through). The surrounding
`ℝ≥0∞` rearrangement into `1 − (I+c)/L ≤ q` (division and truncated subtraction) is discharged in
`fano_inequality` below. -/
private lemma fano_entropy_continuous {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (hM : 2 ≤ M) :
    ENNReal.ofReal (Real.log (M : ℝ))
      ≤ mutualInformation Q + ENNReal.ofReal (Real.log 2)
          + multiwayTestingError Q * ENNReal.ofReal (Real.log (M : ℝ)) := by
  -- `ℝ≥0∞` wrapper around the real-valued Fano bound `fano_real`: handle the `⊤` cases and then
  -- push everything through `ENNReal.ofReal`.
  have hlogM_pos : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogM_nonneg : (0 : ℝ) ≤ Real.log (M : ℝ) := hlogM_pos.le
  have hlog2_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  -- If the mutual information is infinite the RHS is `⊤`.
  by_cases hItop : mutualInformation Q = ⊤
  · rw [hItop]; simp
  -- If the testing error is infinite, then `q · log M = ⊤` (since `log M > 0`) and the RHS is `⊤`.
  by_cases hqtop : multiwayTestingError Q = ⊤
  · have hne : ENNReal.ofReal (Real.log (M : ℝ)) ≠ 0 := (ENNReal.ofReal_pos.mpr hlogM_pos).ne'
    rw [hqtop, ENNReal.top_mul hne]; simp
  -- Both quantities finite: rewrite the RHS as a single `ENNReal.ofReal` and apply `fano_real`.
  have hReal := fano_real Q hItop hqtop hM
  have hsum_eq : mutualInformation Q + ENNReal.ofReal (Real.log 2)
        + multiwayTestingError Q * ENNReal.ofReal (Real.log (M : ℝ))
      = ENNReal.ofReal ((mutualInformation Q).toReal + Real.log 2
          + (multiwayTestingError Q).toReal * Real.log (M : ℝ)) := by
    rw [ENNReal.ofReal_add (add_nonneg ENNReal.toReal_nonneg hlog2_nonneg)
          (mul_nonneg ENNReal.toReal_nonneg hlogM_nonneg),
        ENNReal.ofReal_add ENNReal.toReal_nonneg hlog2_nonneg,
        ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal hItop, ENNReal.ofReal_toReal hqtop]
  rw [hsum_eq]
  exact ENNReal.ofReal_le_ofReal hReal

/-- **Fano's inequality** (Wainwright Eq. (15.31)): the error probability of the M-ary test is
lower bounded by `1 − (I(Z; J) + log 2)/log M`, where `I(Z; J)` is the mutual information.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2, Eq. (15.31). -/
theorem fano_inequality {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    -- USER-INPUT: at least two hypotheses, so `log M > 0`; Wainwright §15.3.2.
    (hM : 2 ≤ M) :
    1 - (mutualInformation Q + ENNReal.ofReal (Real.log 2)) / ENNReal.ofReal (Real.log (M : ℝ))
      ≤ multiwayTestingError Q := by
  -- `ℝ≥0∞` rearrangement of the entropy-form bound `L ≤ I + c + q·L` into `1 − (I+c)/L ≤ q`,
  -- using `0 < L < ∞` (since `log M > 0` for `M ≥ 2`).
  have hbound := fano_entropy_continuous Q hM
  have hMr : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hLpos : 0 < ENNReal.ofReal (Real.log (M : ℝ)) :=
    ENNReal.ofReal_pos.mpr (Real.log_pos hMr)
  have hLtop : ENNReal.ofReal (Real.log (M : ℝ)) ≠ ⊤ := ENNReal.ofReal_ne_top
  set L := ENNReal.ofReal (Real.log (M : ℝ)) with hL
  set I := mutualInformation Q with hI
  set c := ENNReal.ofReal (Real.log 2) with hc
  set q := multiwayTestingError Q with hq
  -- goal: `1 - (I + c) / L ≤ q`
  rw [tsub_le_iff_right]
  -- goal: `1 ≤ q + (I + c) / L`
  calc (1 : ℝ≥0∞)
      = L / L := (ENNReal.div_self hLpos.ne' hLtop).symm
    _ ≤ (I + c + q * L) / L := by gcongr
    _ = (I + c) / L + q * L / L := by rw [ENNReal.add_div]
    _ = (I + c) / L + q := by rw [mul_div_assoc, ENNReal.div_self hLpos.ne' hLtop, mul_one]
    _ = q + (I + c) / L := add_comm _ _

/-- **Fano minimax lower bound** (Wainwright Proposition 15.12, Eq. (15.32)): for an increasing
distortion `Φ` and a `2δ`-separated family `θfam : Fin M → Θ`,
`M(θ(𝒫); Φ∘ρ) ≥ Φ(δ)(1 − (I(Z; J) + log 2)/log M)`, where `I(Z; J)` is the mutual information of the
induced sub-model.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.2, Proposition 15.12. -/
theorem minimax_fano_lower_bound [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {M : ℕ} [NeZero M] (θfam : Fin M → Θ) (hθ : Measurable θfam) (δ : ℝ≥0∞)
    -- USER-INPUT: at least two hypotheses; Wainwright §15.3.2, Prop 15.12.
    (hM : 2 ≤ M)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.3.2, Prop 15.12.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `{θfam j}` is a `2δ`-separated set; Wainwright §15.3.2, Prop 15.12.
    (hsep : IsSeparatedFamily g θfam δ) :
    Φ δ * (1 - (mutualInformation (P.comap θfam hθ) + ENNReal.ofReal (Real.log 2))
                / ENNReal.ofReal (Real.log (M : ℝ)))
      ≤ minimaxRiskDist Φ g P :=
  -- `Φ δ · (Fano bound) ≤ Φ δ · (testing error) ≤ minimax risk`: Fano's inequality (15.31) bounds
  -- the bracket by the M-ary testing error, and the estimation-to-testing reduction (Prop 15.1)
  -- turns that into the minimax risk.
  calc Φ δ * (1 - (mutualInformation (P.comap θfam hθ) + ENNReal.ofReal (Real.log 2))
                  / ENNReal.ofReal (Real.log (M : ℝ)))
      ≤ Φ δ * multiwayTestingError (P.comap θfam hθ) :=
        mul_le_mul_right (fano_inequality (P.comap θfam hθ) hM) _
    _ ≤ minimaxRiskDist Φ g P := minimax_ge_testing_error Φ g P θfam hθ δ hΦ hsep

end StatLean.Minimaxity
