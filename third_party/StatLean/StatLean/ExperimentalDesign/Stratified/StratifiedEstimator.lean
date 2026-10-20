module
public import StatLean.ExperimentalDesign.Stratified.ProductDesign
public import StatLean.ExperimentalDesign.Core.Stratification
public import StatLean.ExperimentalDesign.SurveySampling.SimpleRandomSampling

@[expose] public section

/-!
# Stratified estimators: weighted combination across independent strata

The generic estimator of blocked/stratified design-based inference is the weighted
combination `∑_b w_b · f_b(ω_b)` of per-stratum statistics under a product design.
This file proves the two abstract identities
$$\mathbb E\Bigl[\sum_b w_b f_b\Bigr] = \sum_b w_b\, \mathbb E_{D_b}[f_b], \qquad
  \operatorname{Var}\Bigl(\sum_b w_b f_b\Bigr)
    = \sum_b w_b^2 \operatorname{Var}_{D_b}(f_b),$$
and instantiates them at **stratified simple random sampling** with the
size-proportional weights `w_b = N_b/N`: the stratified sample mean is unbiased for
the population mean, with exact variance
$$\operatorname{Var} = \sum_b \Bigl(\frac{N_b}{N}\Bigr)^2
    \Bigl(1 - \frac{n_b}{N_b}\Bigr) \frac{S_b^2}{n_b}.$$
Blocked randomized experiments reuse the same two abstract identities through
`Randomization/Blocked`.

## Main results

* `stratified_expect`, `stratified_var` — the abstract weighted-combination moments.
* `stratifiedSRS` — independent within-stratum SRSWOR.
* `stratifiedMeanEstimator` — the `N_b/N`-weighted stratified sample mean.
* `stratifiedSRS_mean_unbiased`, `stratifiedSRS_mean_variance` — its exact moments.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988, §9.4 (blockwise
randomisation moments; independence between blocks) and §7.1–7.2 (block structure);
the stratified-sampling formulas are survey-sampling classics (W.G. Cochran,
*Sampling Techniques*, 3rd ed., Wiley, 1977, ch. 5).  (`Mead §9.4`, `Mead §7.2`.)

**Proof formalization notes.**
* The abstract identities are `pmfExpect_sum`/`pmfVar_productDesign_sum` composed
  with `pmfExpect_smul`/`pmfVar_smul` and the marginal lemmas.
* The stratified-SRS instantiation runs over the stratum subtypes
  `Stratum st b = {i // st i = b}`; the deterministic half is
  `populationMean_stratified`.
* The hypothesis `∀ b, n b ≠ 0` forces every stratum to be sampled and (through
  `n b ≤ N_b`) every stratum to be nonempty — the textbook stratified frame.  Empty
  strata would require dropping their weight-zero terms; deferred to a later round.
-/

namespace StatLean.ExperimentalDesign

section Abstract

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {Ω : B → Type*} [∀ b, Fintype (Ω b)] [∀ b, DecidableEq (Ω b)]

/-- **Expectation of a weighted stratum combination** under independent per-stratum
designs (`Mead §9.4`). -/
theorem stratified_expect (D : ∀ b, PMF (Ω b)) (w : B → ℝ) (f : ∀ b, Ω b → ℝ) :
    pmfExpect (productDesign D) (fun ω => ∑ b, w b * f b (ω b))
      = ∑ b, w b * pmfExpect (D b) (f b) := by
  classical
  refine (pmfExpect_sum (productDesign D) Finset.univ fun b ω => w b * f b (ω b)).trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  refine (pmfExpect_smul (productDesign D) (w b) fun ω => f b (ω b)).trans ?_
  rw [pmfExpect_productDesign_comp]

/-- **Variance of a weighted stratum combination** under independent per-stratum
designs: no cross-stratum terms (`Mead §9.4`). -/
theorem stratified_var (D : ∀ b, PMF (Ω b)) (w : B → ℝ) (f : ∀ b, Ω b → ℝ) :
    pmfVar (productDesign D) (fun ω => ∑ b, w b * f b (ω b))
      = ∑ b, w b ^ 2 * pmfVar (D b) (f b) := by
  classical
  refine (pmfVar_productDesign_sum D fun b x => w b * f b x).trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  exact pmfVar_smul (D b) (w b) (f b)

end Abstract

section StratifiedSRS

variable {U B : Type*} [Fintype U] [DecidableEq U] [Fintype B] [DecidableEq B]

/-- **Stratified simple random sampling**: independent SRSWOR of size `n b` within
each stratum of the stratification `st` (Cochran ch. 5; `Mead §9.6` blockwise
randomisation). -/
noncomputable def stratifiedSRS (st : U → B) (n : B → ℕ)
    (hn : ∀ b, n b ≤ Fintype.card (Stratum st b)) :
    PMF (∀ b, Finset (Stratum st b)) :=
  productDesign fun b => simpleRandomSampling (n b) (hn b)

/-- The **stratified sample mean**: the `N_b/N`-weighted combination of the
within-stratum sample means.  Edge behaviour: an empty stratum contributes `0`
through its vanishing weight. -/
noncomputable def stratifiedMeanEstimator (st : U → B) (y : U → ℝ)
    (ω : ∀ b, Finset (Stratum st b)) : ℝ :=
  ∑ b, (Fintype.card (Stratum st b) : ℝ) / (Fintype.card U : ℝ)
      * sampleMean (fun i : Stratum st b => y i) (ω b)

/-- **Unbiasedness of the stratified sample mean**: with positive within-stratum
sample sizes, the design expectation is the population mean (Cochran ch. 5,
Theorem 5.1; the blockwise-unbiasedness pattern of `Mead §9.4`). -/
theorem stratifiedSRS_mean_unbiased
    -- LEAN-ONLY: nonempty population, so the global size `N` is invertible
    [Nonempty U] (st : U → B) (n : B → ℕ)
    (hn : ∀ b, n b ≤ Fintype.card (Stratum st b))
    -- USER-INPUT: every stratum is sampled (positive within-stratum sizes); Cochran ch. 5
    (hpos : ∀ b, n b ≠ 0) (y : U → ℝ) :
    pmfExpect (stratifiedSRS st n hn) (stratifiedMeanEstimator st y)
      = populationMean y := by
  classical
  refine (stratified_expect (fun b => simpleRandomSampling (n b) (hn b))
      (fun b => (Fintype.card (Stratum st b) : ℝ) / (Fintype.card U : ℝ))
      (fun b => sampleMean fun i : Stratum st b => y i)).trans ?_
  have h2 : ∀ b, pmfExpect (simpleRandomSampling (n b) (hn b))
      (sampleMean fun i : Stratum st b => y i)
      = populationMean fun i : Stratum st b => y i := fun b =>
    srs_sampleMean_unbiased (n b) (hn b) (hpos b) _
  refine Eq.trans ?_ (populationMean_stratified st y).symm
  exact Finset.sum_congr rfl fun b _ => by rw [h2 b]

/-- **Exact variance of the stratified sample mean**:
`∑_b (N_b/N)² (1 − n_b/N_b) S_b²/n_b` (Cochran ch. 5, Theorem 5.3; no cross-stratum
terms by `Mead §9.4`). -/
theorem stratifiedSRS_mean_variance (st : U → B) (n : B → ℕ)
    (hn : ∀ b, n b ≤ Fintype.card (Stratum st b))
    -- USER-INPUT: every stratum is sampled (positive within-stratum sizes); Cochran ch. 5
    (hpos : ∀ b, n b ≠ 0) (y : U → ℝ) :
    pmfVar (stratifiedSRS st n hn) (stratifiedMeanEstimator st y)
      = ∑ b, ((Fintype.card (Stratum st b) : ℝ) / (Fintype.card U : ℝ)) ^ 2
          * ((1 - (n b : ℝ) / (Fintype.card (Stratum st b) : ℝ))
              * populationVariance (fun i : Stratum st b => y i) / (n b : ℝ)) := by
  classical
  refine (stratified_var (fun b => simpleRandomSampling (n b) (hn b))
      (fun b => (Fintype.card (Stratum st b) : ℝ) / (Fintype.card U : ℝ))
      (fun b => sampleMean fun i : Stratum st b => y i)).trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [srs_sampleMean_variance (n b) (hn b) (hpos b)]

end StratifiedSRS

end StatLean.ExperimentalDesign
