module
public import StatLean.HypothesisTesting.Randomization.SignChange
public import StatLean.HypothesisTesting.Randomization.PairCLT
public import StatLean.HypothesisTesting.Randomization.TwoSamplePermutation
public import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
public import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
public import StatLean.MultipleTesting.ForMathlib.ChiSquared
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# Randomization tests for a multivariate mean: quadratic-form limits

Testing $\mu(P) = 0$ for i.i.d. random vectors in $\mathbb{R}^p$ is classically done with
Hotelling's $T^2$ statistic, whose exact critical values require multivariate normality. A
randomization test using the **sign-change group** — replacing $X_i$ by $-X_i$ for an
arbitrary subset of indices — is exact for *every* law with $X_i$ and $-X_i$ identically
distributed, and this file establishes that it is asymptotically level $\alpha$ far beyond
that class, under second moments alone.

All three results below use the **sign-change group**, not the permutation group: the
permutation group belongs to the two-sample problem, whereas the one-sample multivariate
mean is invariant under sign changes. Writing $\varepsilon, \varepsilon'$ for two
independent uniform sign patterns:

* the **vector** building block — $n^{-1/2}\bigl(\sum_i \varepsilon_i X_i,
  \sum_i \varepsilon_i' X_i\bigr) \xrightarrow{d} (Z_1, Z_2)$ with $Z_1, Z_2$ i.i.d.
  $N(0, \Sigma)$;
* the **modified** $T^2$ statistic $\tilde T_n = n \bar X_n^\top \tilde\Sigma_n^{-1}
  \bar X_n$, built from the uncentred second-moment matrix
  $\tilde\Sigma_n = n^{-1}\sum_i X_iX_i^\top$ — which is itself *invariant* under sign
  changes — has randomized pair converging to
  $(Z_1^\top\Sigma^{-1}Z_1, Z_2^\top\Sigma^{-1}Z_2)$, a product of two independent
  $\chi^2_p$ laws;
* Hotelling's $T^2$ statistic $T_n = n\bar X_n^\top \hat\Sigma_n^{-1}\bar X_n$, built from
  the centred sample covariance with divisor $n - 1$, has the same limit.

Since the unconditional limit of $T_n$ is also $\chi^2_p$, the randomization test based on
either statistic has rejection probability tending to the nominal level under any $P$ with
mean $0$ and finite second moments — and retains *exact* level whenever $X_i$ and $-X_i$
are identically distributed.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.4 (Further Examples), Lemmas 17.4.1–17.4.3 (the quadratic-form
building block, joint convergence under two independent assignments, and the independent
chi-squared pair limit). (`TSH4 §17.4 Lem 17.4.1–17.4.3`.)

**Proof formalization notes.**
* *Group.* The acting group is `Fin n → ℤˣ` (i.e. `{±1}ⁿ`) acting componentwise on
  `Fin n → EuclideanSpace ℝ (Fin p)`, the same Mathlib-supplied action as in
  `Randomization/SignChange`, now with vector-valued coordinates.
* *Vector-valued randomized pairs.* `randPairLaw` is used at the target
  `EuclideanSpace ℝ (Fin p)` for the first result and at `ℝ` for the two quadratic-form
  results; that is the reason it is stated for a general measurable target.
* *Matrices and `EuclideanSpace`.* Data vectors live in `EuclideanSpace ℝ (Fin p)` (needed
  by `multivariateGaussian`), while sample covariance matrices are plain
  `Matrix (Fin p) (Fin p) ℝ`; the bridge is `.ofLp` together with `⬝ᵥ` and `Matrix.mulVec`,
  the convention already used elsewhere in the library. Matrix inversion is Mathlib's
  total `Matrix.inv`, which returns `0` on singular input — so all statistics here are
  total, with junk values exactly on the null set where the sample covariance degenerates.
* *Why the modified statistic is separated out.* $\tilde\Sigma_n$ is unchanged when any
  $X_i$ is replaced by $-X_i$, so recomputing $\tilde T_n$ over the group only moves
  $\bar X_n$; that is what makes its randomization analysis immediate from the vector
  building block plus the continuous mapping theorem. Hotelling's $\hat\Sigma_n$ is not
  invariant, and its treatment goes through the consistency
  $\hat\Sigma_n(\varepsilon_1X_1, \dots, \varepsilon_nX_n) \to \Sigma$ in probability,
  which is where mean-zero is used a second time.
* *Mean-zero and the second-moment variant.* The results are stated with $\mu(P) = 0$, as
  in the classical formulation, and `S` is then simultaneously the covariance and the
  second-moment matrix. The vector limit in fact holds verbatim without mean-zero provided
  `S` is read as the second-moment matrix $E[X_jX_k]$ — which is how the covariance
  hypothesis is phrased here, so that generalization needs no restatement.
* *Nondegeneracy.* Positive definiteness of `S` is genuine input: it is what makes
  `S⁻¹` meaningful and the quadratic form a $\chi^2_p$ rather than a degenerate law.
  `[NeZero p]` records that there is at least one degree of freedom.
* The identification of the limiting quadratic form with `chiSquared p` is isolated as
  `map_quadraticForm_multivariateGaussian_eq_chiSquared`, the one genuinely
  distributional step; the rest is the Cramér–Wold device plus the central limit theorem
  of the sibling brick `StatLean.HypothesisTesting.ForMathlib.LindebergCLT`, applied to the
  i.i.d. vectors `(εᵢXᵢ, ε'ᵢXᵢ)`, whose cross-covariance vanishes because
  `E[εᵢ]E[ε'ᵢ] = 0`.

**Bibliographic comments.** Sign-change randomization tests originate with R. A. Fisher
(*The Design of Experiments*, Oliver & Boyd, Edinburgh, 1935) and E. J. G. Pitman
("Significance tests which may be applied to samples from any populations," *J. R.
Statist. Soc. Suppl.* **4** (1937), 119–130); their exactness under a group hypothesis is
E. L. Lehmann and C. Stein ("On the theory of some non-parametric hypotheses," *Ann. Math.
Statist.* **20** (1949), 28–45), and the sampled-group variant M. Dwass ("Modified
randomization tests for nonparametric hypotheses," *Ann. Math. Statist.* **28** (1957),
181–187). Large-sample theory for permutation and randomization statistics is
W. Hoeffding ("The large-sample power of tests based on permutations of observations,"
*Ann. Math. Statist.* **23** (1952), 169–192); the asymptotic robustness of such tests
when the group hypothesis fails is J. P. Romano ("Bootstrap and randomization tests of some
nonparametric hypotheses," *Ann. Statist.* **17** (1989), 141–159; "On the behavior of
randomization tests without a group invariance assumption," *J. Amer. Statist. Assoc.*
**85** (1990), 686–692), with the studentization principle behind the modified statistic
due to A. Janssen ("Studentized permutation tests for non-i.i.d. hypotheses and the
generalized Behrens–Fisher problem," *Statist. Probab. Lett.* **36** (1997), 9–21) and the
general framework to E. Chung and J. P. Romano ("Exact and asymptotically robust
permutation tests," *Ann. Statist.* **41** (2013), 484–507).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace Matrix

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

variable {p : ℕ}

/-! ### Sample functionals -/

/-- Sample mean of a vector-valued sample. -/
noncomputable def sampleMeanVec {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  (n : ℝ)⁻¹ • ∑ i, x i

/-- The **uncentred second-moment matrix** `Σ̃ₙ = n⁻¹ ∑ᵢ XᵢXᵢᵀ`. Unchanged when any `Xᵢ`
is replaced by `−Xᵢ`, hence invariant under the sign-change group. -/
noncomputable def modifiedCovMatrix {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k => (n : ℝ)⁻¹ * ∑ i, (x i).ofLp j * (x i).ofLp k

/-- The **sample covariance matrix** `Σ̂ₙ = (n−1)⁻¹ ∑ᵢ (Xᵢ − X̄ₙ)(Xᵢ − X̄ₙ)ᵀ`. Not
invariant under sign changes. -/
noncomputable def sampleCovMatrix {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun j k => ((n : ℝ) - 1)⁻¹ *
    ∑ i, ((x i).ofLp j - (sampleMeanVec x).ofLp j) *
      ((x i).ofLp k - (sampleMeanVec x).ofLp k)

/-- **Hotelling's `T²` statistic** `Tₙ = n X̄ₙᵀ Σ̂ₙ⁻¹ X̄ₙ`. Total: a singular sample
covariance gives Mathlib's junk inverse `0`, hence the value `0`. -/
noncomputable def hotellingTSq {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ :=
  (n : ℝ) *
    ((sampleMeanVec x).ofLp ⬝ᵥ (sampleCovMatrix x)⁻¹.mulVec (sampleMeanVec x).ofLp)

/-- The **modified `T²` statistic** `T̃ₙ = n X̄ₙᵀ Σ̃ₙ⁻¹ X̄ₙ`, built from the uncentred
second-moment matrix (divisor `n` rather than `n − 1`). -/
noncomputable def modifiedTSq {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin p)) : ℝ :=
  (n : ℝ) *
    ((sampleMeanVec x).ofLp ⬝ᵥ (modifiedCovMatrix x)⁻¹.mulVec (sampleMeanVec x).ofLp)

/-! ### The distributional bridge -/

/-- **The quadratic form of a nondegenerate centred Gaussian is chi-squared**:
if `Z ∼ N(0, S)` with `S` positive definite, then `ZᵀS⁻¹Z ∼ χ²_p`. -/
theorem map_quadraticForm_multivariateGaussian_eq_chiSquared [NeZero p]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance, so `S⁻¹` is a genuine inverse
    (hpd : S.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map
        (fun z => z.ofLp ⬝ᵥ S⁻¹.mulVec z.ofLp) = chiSquared p := by
  -- The quadratic-form spelling `z.ofLp ⬝ᵥ S⁻¹ *ᵥ z.ofLp` is `Matrix.inner_toEuclideanCLM`
  -- of the inner-product spelling `⟪z, toEuclideanCLM S⁻¹ z⟫`, whose pushforward is the
  -- whitening bridge `multivariateGaussian_map_inner_inv_eq_chiSquared`.
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hfun : (fun z : EuclideanSpace ℝ (Fin p) => z.ofLp ⬝ᵥ S⁻¹.mulVec z.ofLp)
      = fun z => ⟪z, Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹ z⟫ := by
    funext z
    exact (Matrix.inner_toEuclideanCLM S⁻¹ z z).symm
  rw [hfun]
  exact multivariateGaussian_map_inner_inv_eq_chiSquared hp hpd

/-! ### The vector building block -/

/-- **Sign-change randomization: the vector limit.** For i.i.d. vectors with mean `0` and
second-moment matrix `S`, the normalized sign-flipped sums at two independent uniform sign
patterns converge jointly in law to a pair of **independent, identically distributed**
centred Gaussians with covariance `S`:
$$ n^{-1/2}\Bigl(\sum_i \varepsilon_i X_i,\; \sum_i \varepsilon_i' X_i\Bigr)
   \;\xrightarrow{d}\; (Z_1, Z_2), \qquad Z_1, Z_2 \text{ i.i.d. } N(0, S). $$
Asymptotic independence comes from `E[εᵢ]E[ε'ᵢ] = 0`.

*The mean-zero hypothesis `hmean` is not used in the proof*, confirming the remark in the
file notes: the sign average symmetrizes each summand, so the first-order term of the
characteristic-function expansion cancels identically and only the second-moment matrix `S`
(as supplied by `hsecond`) enters. It is retained in the signature because it is the
classical formulation and because the two quadratic-form corollaries below do use it. -/
theorem weakConverges_randPairLaw_signChange_sum
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance
    (hpd : S.PosDef)
    -- USER-INPUT: finite second moments of the observation vector
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: the population mean vanishes; the null hypothesis under test
    (hmean : ∫ x, x ∂P = 0)
    -- USER-INPUT: `S` is the second-moment matrix (= the covariance, since the mean
    -- vanishes); stating it this way is what makes the result hold verbatim for a
    -- nonzero mean with `S` read as the second-moment matrix
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
        (Measure.pi fun _ : Fin n => P))
      ((multivariateGaussian 0 S).prod (multivariateGaussian 0 S)) := by
  -- The general bivariate sign-change CLT of `Randomization/PairCLT` applies verbatim with
  -- `E = EuclideanSpace ℝ (Fin p)`: all that is left is to identify the limiting Gaussian
  -- through its characteristic function, i.e. to check that the second-moment matrix `S`
  -- represents the quadratic form `v ↦ ∫ ⟪y,v⟫² dP`. (Mean-zero is *not* used: the sign
  -- average symmetrizes each summand, so the first-order term cancels identically.)
  classical
  have hcoord : ∀ j : Fin p,
      MemLp (fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j) 2 P := by
    intro j
    have h := memLp_inner_right P hL2 (EuclideanSpace.single j (1 : ℝ))
    have heq : (fun y : EuclideanSpace ℝ (Fin p) => ⟪y, EuclideanSpace.single j (1 : ℝ)⟫)
        = fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j := by
      funext y
      simp [EuclideanSpace.inner_single_right]
    rwa [heq] at h
  have hinner_expand : ∀ y v : EuclideanSpace ℝ (Fin p),
      ⟪y, v⟫ = ∑ j, y.ofLp j * v.ofLp j := by
    intro y v
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun j _ => by
      simp [real_inner_eq_re_inner ℝ, RCLike.inner_apply, mul_comm]
  have hmoment : ∀ v : EuclideanSpace ℝ (Fin p),
      ∫ y, ⟪y, v⟫ ^ 2 ∂P = v.ofLp ⬝ᵥ S *ᵥ v.ofLp := by
    intro v
    have hpt : ∀ y : EuclideanSpace ℝ (Fin p), ⟪y, v⟫ ^ 2
        = ∑ j, ∑ k, (v.ofLp j * v.ofLp k) * (y.ofLp j * y.ofLp k) := by
      intro y
      rw [hinner_expand y v, sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    have hint : ∀ j k : Fin p,
        Integrable (fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j * y.ofLp k) P := by
      intro j k
      simpa using! (hcoord j).integrable_mul (hcoord k)
    have h1 : ∫ y, ⟪y, v⟫ ^ 2 ∂P
        = ∫ y, (∑ j, ∑ k, (v.ofLp j * v.ofLp k) * (y.ofLp j * y.ofLp k)) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall hpt)
    rw [h1, integral_finset_sum (f := fun j : Fin p => fun y : EuclideanSpace ℝ (Fin p) =>
        ∑ k, (v.ofLp j * v.ofLp k) * (y.ofLp j * y.ofLp k)) Finset.univ
      (fun j _ => integrable_finset_sum Finset.univ fun k _ => (hint j k).const_mul _)]
    have h2 : ∀ j : Fin p, ∫ y, (∑ k, (v.ofLp j * v.ofLp k) * (y.ofLp j * y.ofLp k)) ∂P
        = ∑ k, (v.ofLp j * v.ofLp k) * S j k := by
      intro j
      rw [integral_finset_sum (f := fun k : Fin p => fun y : EuclideanSpace ℝ (Fin p) =>
          (v.ofLp j * v.ofLp k) * (y.ofLp j * y.ofLp k)) Finset.univ
        (fun k _ => (hint j k).const_mul _)]
      exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul, hsecond j k]
    rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h2 j)]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hchar : ∀ v : EuclideanSpace ℝ (Fin p),
      charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) v
        = Complex.exp (-((∫ y, ⟪y, v⟫ ^ 2 ∂P : ℝ) : ℂ) / 2) := by
    intro v
    rw [charFun_multivariateGaussian hpd.posSemidef, hmoment v]
    simp [neg_div]
  exact weakConverges_randPairLaw_signSum P hL2 (multivariateGaussian 0 S) hchar

/-! ### From the vector limit to the quadratic-form limit -/

/-- Measurability of the sign-change action on vector-valued data. -/
private lemma measurable_signChange_smul_vec {n : ℕ} (ε : Fin n → ℤˣ) :
    Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin p) => ε • x) := by
  refine measurable_pi_lambda (fun x : Fin n → EuclideanSpace ℝ (Fin p) => ε • x) fun i => ?_
  have heq : (fun x : Fin n → EuclideanSpace ℝ (Fin p) => (ε • x) i)
      = fun x => ((ε i : ℤ) : ℝ) • x i :=
    funext fun x => signChange_smul_apply_vec ε x i
  rw [heq]
  have hcoord : Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin p) => x i) :=
    measurable_pi_apply i
  exact hcoord.const_smul (((ε i : ℤ) : ℝ))

/-- The normalized sum, the vector statistic of the building block, is measurable. -/
private lemma measurable_signSum {n : ℕ} :
    Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
      (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i) := by
  have hsum : Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin p) => ∑ i, x i) :=
    Finset.measurable_sum Finset.univ fun i _ =>
      (measurable_pi_apply i : Measurable (fun x : Fin n → EuclideanSpace ℝ (Fin p) => x i))
  exact hsum.const_smul ((Real.sqrt (n : ℝ))⁻¹)

/-- The quadratic form written out in coordinates. -/
private lemma quadFormInv_eq (S : Matrix (Fin p) (Fin p) ℝ)
    (v : EuclideanSpace ℝ (Fin p)) :
    v.ofLp ⬝ᵥ S⁻¹.mulVec v.ofLp = ∑ j, ∑ k, S⁻¹ j k * (v.ofLp j * v.ofLp k) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- Coordinate evaluation on `EuclideanSpace` is continuous. -/
private lemma continuous_ofLp_coord (j : Fin p) :
    Continuous (fun v : EuclideanSpace ℝ (Fin p) => v.ofLp j) := by
  fun_prop

/-- The quadratic form `v ↦ vᵀ S⁻¹ v` is continuous. -/
private lemma continuous_quadFormInv (S : Matrix (Fin p) (Fin p) ℝ) :
    Continuous (fun v : EuclideanSpace ℝ (Fin p) => v.ofLp ⬝ᵥ S⁻¹.mulVec v.ofLp) := by
  simp only [quadFormInv_eq]
  exact continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun k _ =>
    continuous_const.mul ((continuous_ofLp_coord j).mul (continuous_ofLp_coord k))

/-- The quadratic form `v ↦ vᵀ S⁻¹ v` is measurable. -/
private lemma measurable_quadFormInv (S : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (fun v : EuclideanSpace ℝ (Fin p) => v.ofLp ⬝ᵥ S⁻¹.mulVec v.ofLp) :=
  (continuous_quadFormInv S).measurable

/-- **The reference quadratic-form limit.** Composing the vector building block with the
*population* quadratic form `v ↦ vᵀS⁻¹v` gives a doubly randomized law converging to a
product of two independent `χ²_p` laws. This is the limit that the sample-based statistics
`modifiedTSq` and `hotellingTSq` are compared against. -/
private lemma weakConverges_randPairLaw_quadFormInv [NeZero p]
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ} (hpd : S.PosDef) (hL2 : MemLp id 2 P)
    (hmean : ∫ x, x ∂P = 0)
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          (fun v : EuclideanSpace ℝ (Fin p) => v.ofLp ⬝ᵥ S⁻¹.mulVec v.ofLp)
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i))
        (Measure.pi fun _ : Fin n => P))
      ((chiSquared p).prod (chiSquared p)) := by
  classical
  set q : EuclideanSpace ℝ (Fin p) → ℝ := fun v => v.ofLp ⬝ᵥ S⁻¹.mulVec v.ofLp with hqdef
  have hqm : Measurable q := measurable_quadFormInv S
  have hbase := weakConverges_randPairLaw_signChange_sum P hpd hL2 hmean hsecond
  have hmapped := hbase.map (f := Prod.map q q)
    ((continuous_quadFormInv S).prodMap (continuous_quadFormInv S)) (hqm.prodMap hqm)
  have hlim : ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).prod
      (multivariateGaussian 0 S)).map (Prod.map q q) = (chiSquared p).prod (chiSquared p) := by
    rw [← Measure.map_prod_map _ _ hqm hqm,
      map_quadraticForm_multivariateGaussian_eq_chiSquared hpd]
  rw [hlim] at hmapped
  have hEq : (fun n => randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) => q ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i))
        (Measure.pi fun _ : Fin n => P))
      = fun n => (randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
        (Measure.pi fun _ : Fin n => P)).map (Prod.map q q) := by
    funext n
    exact randPairLaw_map (G := Fin n → ℤˣ) _ _ measurable_signSum
      (fun ε => measurable_signChange_smul_vec ε) hqm
  rw [hEq]
  exact hmapped

/-- **The uncentred second-moment matrix is sign-invariant.** Replacing `Xᵢ` by `−Xᵢ`
leaves `Σ̃ₙ` unchanged, since each summand is a product of two coordinates of the *same*
observation. -/
private lemma modifiedCovMatrix_signChange {n : ℕ} (ε : Fin n → ℤˣ)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    modifiedCovMatrix (ε • x) = modifiedCovMatrix x := by
  ext j k
  simp only [modifiedCovMatrix, Matrix.of_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (ε • x) i = ((ε i : ℤ) : ℝ) • x i := signChange_smul_apply_vec ε x i
  have hsq : (((ε i : ℤ) : ℝ)) * (((ε i : ℤ) : ℝ)) = 1 := by
    rcases Int.units_eq_one_or (ε i) with h1 | h1 <;> rw [h1] <;> norm_num
  rw [h]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  linear_combination (x i).ofLp j * (x i).ofLp k * hsq

/-- Scaling inside the quadratic form. -/
private lemma quadFormInv_smul (M : Matrix (Fin p) (Fin p) ℝ) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin p)) :
    ((c • v : EuclideanSpace ℝ (Fin p)).ofLp) ⬝ᵥ
        M⁻¹.mulVec ((c • v : EuclideanSpace ℝ (Fin p)).ofLp)
      = c ^ 2 * (v.ofLp ⬝ᵥ M⁻¹.mulVec v.ofLp) := by
  have hof : ((c • v : EuclideanSpace ℝ (Fin p)).ofLp) = c • v.ofLp := rfl
  rw [hof, Matrix.mulVec_smul]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The modified statistic recomputed at a sign pattern.** Since `Σ̃ₙ` is sign-invariant,
only the normalized sum `Vₙ = n^{-1/2} ∑ᵢ εᵢXᵢ` moves along the group, and
`T̃ₙ(ε · x) = Vₙ(ε · x)ᵀ Σ̃ₙ(x)⁻¹ Vₙ(ε · x)`. This is the algebraic reduction that lets the
vector building block carry the whole randomization analysis. -/
private lemma modifiedTSq_signChange {n : ℕ} (hn : 0 < n) (ε : Fin n → ℤˣ)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) :
    modifiedTSq (ε • x)
      = ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i : EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ
          (modifiedCovMatrix x)⁻¹.mulVec
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i : EuclideanSpace ℝ (Fin p)).ofLp := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne : (n : ℝ) ≠ 0 := hnR.ne'
  have hsq : (Real.sqrt (n : ℝ))⁻¹ ^ 2 = ((n : ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
  have hmean : (sampleMeanVec (ε • x) : EuclideanSpace ℝ (Fin p))
      = ((n : ℝ))⁻¹ • ∑ i, (ε • x) i := rfl
  rw [modifiedTSq, modifiedCovMatrix_signChange ε x, hmean,
    quadFormInv_smul _ ((n : ℝ))⁻¹, quadFormInv_smul _ ((Real.sqrt (n : ℝ))⁻¹), hsq]
  field_simp

/-! ### Perturbing the matrix inside the quadratic form

The reduction of `modifiedTSq` onto the vector building block replaces the *population*
matrix `S⁻¹` by the *sample* matrix `Σ̃ₙ⁻¹`. Everything needed to control that replacement is
elementary and collected here: a coordinate bound on `EuclideanSpace`, the resulting
entrywise estimate for the quadratic form, and the fact that matrix inversion is continuous
at a nonsingular matrix in the explicit "entrywise tolerance" form that a
convergence-in-probability argument consumes. -/

/-- A coordinate of a vector is dominated by its norm. -/
private lemma abs_ofLp_le_norm (v : EuclideanSpace ℝ (Fin p)) (j : Fin p) :
    |v.ofLp j| ≤ ‖v‖ := by
  have heq : v.ofLp j = ⟪v, EuclideanSpace.single j (1 : ℝ)⟫ := by
    simp [EuclideanSpace.inner_single_right]
  rw [heq]
  simpa [PiLp.norm_single] using
    abs_real_inner_le_norm v (EuclideanSpace.single j (1 : ℝ))

/-- The quadratic form written out in coordinates, for an arbitrary matrix. -/
private lemma quadForm_eq (M : Matrix (Fin p) (Fin p) ℝ) (v : EuclideanSpace ℝ (Fin p)) :
    v.ofLp ⬝ᵥ M.mulVec v.ofLp = ∑ j, ∑ k, M j k * (v.ofLp j * v.ofLp k) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- **Entrywise perturbation bound for a quadratic form.** If two matrices agree entrywise
to within `η`, their quadratic forms at `v` differ by at most `p²η‖v‖²`. This is the estimate
that splits the randomization remainder into a "matrix is close" event and a "vector is
bounded" event. -/
private lemma abs_quadForm_sub_le {M N : Matrix (Fin p) (Fin p) ℝ}
    (v : EuclideanSpace ℝ (Fin p)) {η : ℝ}
    (h : ∀ j k, |M j k - N j k| ≤ η) :
    |v.ofLp ⬝ᵥ M.mulVec v.ofLp - v.ofLp ⬝ᵥ N.mulVec v.ofLp| ≤ (p : ℝ) ^ 2 * η * ‖v‖ ^ 2 := by
  have hdiff : v.ofLp ⬝ᵥ M.mulVec v.ofLp - v.ofLp ⬝ᵥ N.mulVec v.ofLp
      = ∑ j, ∑ k, (M j k - N j k) * (v.ofLp j * v.ofLp k) := by
    rw [quadForm_eq, quadForm_eq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hdiff]
  have hterm : ∀ j k : Fin p,
      |(M j k - N j k) * (v.ofLp j * v.ofLp k)| ≤ η * ‖v‖ ^ 2 := by
    intro j k
    rw [abs_mul, abs_mul, sq]
    exact mul_le_mul (h j k)
      (mul_le_mul (abs_ofLp_le_norm v j) (abs_ofLp_le_norm v k) (abs_nonneg _) (norm_nonneg v))
      (by positivity) ((abs_nonneg _).trans (h j k))
  calc |∑ j, ∑ k, (M j k - N j k) * (v.ofLp j * v.ofLp k)|
      ≤ ∑ j : Fin p, |∑ k, (M j k - N j k) * (v.ofLp j * v.ofLp k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin p, ∑ _k : Fin p, η * ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun j _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm j k)
    _ = (p : ℝ) ^ 2 * η * ‖v‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

section MatrixInvContinuity

attribute [local instance] Matrix.normedAddCommGroup

/-- **Continuity of matrix inversion at a positive-definite matrix, entrywise form.** For
every tolerance `η` there is a tolerance `ρ` such that matrices within `ρ` of `S` entrywise
have inverses within `η` of `S⁻¹` entrywise.

The `ε`-`δ` phrasing (rather than `ContinuousAt`) is what a convergence-in-probability
argument can use: the law of large numbers controls the *entries* of the sample matrix, and
this lemma converts that control into control of the entries of its inverse. -/
private lemma exists_entrywise_tol_matrix_inv {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegeneracy, so that `S` is a point of continuity of inversion
    (hpd : S.PosDef) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > (0 : ℝ), ∀ M : Matrix (Fin p) (Fin p) ℝ,
      (∀ j k, |M j k - S j k| < ρ) → ∀ j k, |M⁻¹ j k - S⁻¹ j k| < η := by
  have hdet : S.det ≠ 0 := hpd.det_pos.ne'
  have hCA : ContinuousAt (Inv.inv : Matrix (Fin p) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ) S := by
    refine continuousAt_matrix_inv S ?_
    simp only [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.continuousAt_iff.mp hCA η hη
  refine ⟨ρ, hρpos, fun M hM j k => ?_⟩
  have hdist : dist M S < ρ := by
    rw [dist_eq_norm, Matrix.norm_lt_iff hρpos]
    intro j' k'
    simpa [Matrix.sub_apply, Real.norm_eq_abs] using hM j' k'
  have hlt := hρ hdist
  rw [dist_eq_norm] at hlt
  have hentry := Matrix.norm_entry_le_entrywise_sup_norm (M⁻¹ - S⁻¹) (i := j) (j := k)
  simp only [Matrix.sub_apply, Real.norm_eq_abs] at hentry
  linarith

end MatrixInvContinuity

/-! ### Measurability of the sample statistics

`Matrix (Fin p) (Fin p) ℝ` carries no `MeasurableSpace` instance, so measurability of the
matrix-valued sample functionals is established entrywise, through the Leibniz formula for
the determinant and the cofactor formula for the adjugate. -/

/-- Determinants of a measurable family of matrices are measurable. -/
private lemma measurable_det_of_entries {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin p) (Fin p) ℝ} (hF : ∀ j k, Measurable fun a => F a j k) :
    Measurable fun a => (F a).det := by
  simp only [Matrix.det_apply']
  exact Finset.measurable_sum _ fun σ _ =>
    (Finset.measurable_prod _ fun i _ => hF (σ i) i).const_mul _

/-- Adjugates of a measurable family of matrices are measurable, entrywise. -/
private lemma measurable_adjugate_of_entries {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin p) (Fin p) ℝ} (hF : ∀ j k, Measurable fun a => F a j k) (j k : Fin p) :
    Measurable fun a => (F a).adjugate j k := by
  classical
  simp only [Matrix.adjugate_apply]
  refine measurable_det_of_entries (F := fun a => (F a).updateRow k (Pi.single j 1)) ?_
  intro j' k'
  by_cases h : j' = k
  · subst h
    simp only [Matrix.updateRow_self]
    exact measurable_const
  · simpa only [Matrix.updateRow_ne h] using hF j' k'

/-- Inverses of a measurable family of matrices are measurable, entrywise. Mathlib's
`Matrix.inv` is total (`0` on singular input), and so is this statement. -/
private lemma measurable_inv_of_entries {α : Type*} [MeasurableSpace α]
    {F : α → Matrix (Fin p) (Fin p) ℝ} (hF : ∀ j k, Measurable fun a => F a j k) (j k : Fin p) :
    Measurable fun a => (F a)⁻¹ j k := by
  have hpt : ∀ a, (F a)⁻¹ j k = ((F a).det)⁻¹ * (F a).adjugate j k := by
    intro a
    rw [Matrix.inv_def]
    simp [Ring.inverse_eq_inv]
  simp only [hpt]
  exact ((measurable_det_of_entries hF).inv).mul (measurable_adjugate_of_entries hF j k)

/-- A coordinate of a data vector is measurable. -/
private lemma measurable_coord {n : ℕ} (i : Fin n) (j : Fin p) :
    Measurable fun x : Fin n → EuclideanSpace ℝ (Fin p) => (x i).ofLp j :=
  (continuous_ofLp_coord j).measurable.comp (measurable_pi_apply i)

/-- The entries of the uncentred second-moment matrix are measurable. -/
private lemma measurable_modifiedCovMatrix_entry {n : ℕ} (j k : Fin p) :
    Measurable fun x : Fin n → EuclideanSpace ℝ (Fin p) => modifiedCovMatrix x j k := by
  simp only [modifiedCovMatrix, Matrix.of_apply]
  exact (Finset.measurable_sum _ fun i _ =>
    (measurable_coord i j).mul (measurable_coord i k)).const_mul _

/-- A coordinate of the sample mean is measurable. -/
private lemma measurable_sampleMeanVec_coord {n : ℕ} (j : Fin p) :
    Measurable fun x : Fin n → EuclideanSpace ℝ (Fin p) => (sampleMeanVec x).ofLp j := by
  have hpt : ∀ x : Fin n → EuclideanSpace ℝ (Fin p),
      (sampleMeanVec x).ofLp j = (n : ℝ)⁻¹ * ∑ i, (x i).ofLp j := by
    intro x
    simp [sampleMeanVec, Finset.sum_apply]
  simp only [hpt]
  exact (Finset.measurable_sum _ fun i _ => measurable_coord i j).const_mul _

/-- **Products of two coordinates are integrable** under a square-integrable law — the
entries of the uncentred second-moment matrix are `L¹`, and no better: the observation has
two moments, so its coordinate products have one. -/
private lemma integrable_ofLp_mul (P : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure P] (hL2 : MemLp id 2 P) (j k : Fin p) :
    Integrable (fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j * y.ofLp k) P := by
  have hcoord : ∀ j : Fin p, MemLp (fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j) 2 P := by
    intro j
    have h := memLp_inner_right P hL2 (EuclideanSpace.single j (1 : ℝ))
    have heq : (fun y : EuclideanSpace ℝ (Fin p) => ⟪y, EuclideanSpace.single j (1 : ℝ)⟫)
        = fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j := by
      funext y
      simp [EuclideanSpace.inner_single_right]
    rwa [heq] at h
  simpa using! (hcoord j).integrable_mul (hcoord k)

/-- The modified `T²` statistic is measurable. -/
private lemma measurable_modifiedTSq {n : ℕ} :
    Measurable (modifiedTSq (p := p) (n := n)) := by
  have hfun : (modifiedTSq (p := p) (n := n))
      = fun x => (n : ℝ) * ∑ j, ∑ k, (modifiedCovMatrix x)⁻¹ j k *
          ((sampleMeanVec x).ofLp j * (sampleMeanVec x).ofLp k) := by
    funext x
    rw [modifiedTSq, quadForm_eq]
  rw [hfun]
  refine Measurable.const_mul (Finset.measurable_sum _ fun j _ =>
    Finset.measurable_sum _ fun k _ => ?_) _
  exact (measurable_inv_of_entries (fun j' k' => measurable_modifiedCovMatrix_entry j' k') j
      k).mul ((measurable_sampleMeanVec_coord j).mul (measurable_sampleMeanVec_coord k))

/-- **The tightness input.** Composing the vector building block with the squared norm gives
a randomized limit for `‖Vₙ‖²`, whose first marginal is therefore uniformly tight. This is
what controls the size of the randomized vector statistic when the *sample* matrix is
substituted for the population one inside the quadratic form; it replaces an assumption of
`O_P(1)` by a consequence of the building block. -/
private lemma weakConverges_randPairLaw_normSq
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ} (hpd : S.PosDef) (hL2 : MemLp id 2 P)
    (hmean : ∫ x, x ∂P = 0)
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n : ℕ => (randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i‖ ^ 2)
        (Measure.pi fun _ : Fin n => P)).map Prod.fst)
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map
        (fun v : EuclideanSpace ℝ (Fin p) => ‖v‖ ^ 2)) := by
  classical
  set w : EuclideanSpace ℝ (Fin p) → ℝ := fun v => ‖v‖ ^ 2 with hwdef
  have hwc : Continuous w := by fun_prop
  have hwm : Measurable w := hwc.measurable
  have hbase := weakConverges_randPairLaw_signChange_sum P hpd hL2 hmean hsecond
  have hmapped := hbase.map (f := Prod.map w w) (hwc.prodMap hwc) (hwm.prodMap hwm)
  rw [← Measure.map_prod_map _ _ hwm hwm] at hmapped
  have heq : ∀ n : ℕ, randPairLaw (Fin n → ℤˣ)
      (fun x : Fin n → EuclideanSpace ℝ (Fin p) => w ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i))
      (Measure.pi fun _ : Fin n => P)
      = (randPairLaw (Fin n → ℤˣ)
          (fun x : Fin n → EuclideanSpace ℝ (Fin p) => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i)
          (Measure.pi fun _ : Fin n => P)).map (Prod.map w w) := fun n =>
    randPairLaw_map (G := Fin n → ℤˣ) _ _ measurable_signSum
      (fun ε => measurable_signChange_smul_vec ε) hwm
  rw [← funext heq] at hmapped
  haveI : ∀ n : ℕ, IsProbabilityMeasure
      (randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) => w ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i))
        (Measure.pi fun _ : Fin n => P)) := fun n =>
    isProbabilityMeasure_randPairLaw (G := Fin n → ℤˣ) _ _ (hwm.comp measurable_signSum)
      (fun ε => measurable_signChange_smul_vec ε)
  haveI : IsProbabilityMeasure
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map w) :=
    Measure.isProbabilityMeasure_map hwm.aemeasurable
  simpa using hmapped.map continuous_fst measurable_fst

/-! ### Quadratic-form limits -/

set_option maxHeartbeats 1000000 in
-- The assembly elaborates a dozen `randPairLaw`-shaped statements over a varying group and
-- a varying data space; unification of those is what costs the extra heartbeats.
/-- **Sign-change randomization for the modified `T²` statistic.** The randomized pair
converges in law to `(Z₁ᵀS⁻¹Z₁, Z₂ᵀS⁻¹Z₂)`, i.e. to a product of two **independent**
chi-squared laws with `p` degrees of freedom. The second-moment matrix used here is
invariant under sign changes, so only the sample mean moves along the group. -/
theorem weakConverges_randPairLaw_signChange_modifiedTSq [NeZero p]
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance
    (hpd : S.PosDef)
    -- USER-INPUT: finite second moments of the observation vector
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: the population mean vanishes; the null hypothesis under test
    (hmean : ∫ x, x ∂P = 0)
    -- USER-INPUT: `S` is the second-moment matrix (= the covariance here)
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ) (modifiedTSq (p := p) (n := n))
        (Measure.pi fun _ : Fin n => P))
      ((chiSquared p).prod (chiSquared p)) := by
  classical
  -- The reference statistic is the *population* quadratic form of the vector building block,
  -- whose randomized limit is the reference limit `χ²_p ⊗ χ²_p`.
  have hconv := weakConverges_randPairLaw_quadFormInv P hpd hL2 hmean hsecond
  have hbase := weakConverges_randPairLaw_signChange_sum P hpd hL2 hmean hsecond
  have hwm : Measurable fun v : EuclideanSpace ℝ (Fin p) => ‖v‖ ^ 2 :=
    (by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin p) => ‖v‖ ^ 2).measurable
  haveI hprobW : ∀ n : ℕ, IsProbabilityMeasure
      (randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i‖ ^ 2)
        (Measure.pi fun _ : Fin n => P)) := fun n =>
    isProbabilityMeasure_randPairLaw (G := Fin n → ℤˣ) _ _ (hwm.comp measurable_signSum)
      (fun ε => measurable_signChange_smul_vec ε)
  haveI : ∀ n : ℕ, IsProbabilityMeasure
      ((randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i‖ ^ 2)
        (Measure.pi fun _ : Fin n => P)).map Prod.fst) := fun n =>
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map
        (fun v : EuclideanSpace ℝ (Fin p) => ‖v‖ ^ 2)) :=
    Measure.isProbabilityMeasure_map hwm.aemeasurable
  have hmarg := weakConverges_randPairLaw_normSq P hpd hL2 hmean hsecond
  -- (a) The `L¹` law of large numbers: the uncentred second-moment matrix is consistent,
  -- entrywise. Its entries are products of two coordinates, hence only `L¹`.
  have hlln : ∀ (j k : Fin p) (ρ : ℝ), 0 < ρ → Tendsto (fun n : ℕ =>
      (Measure.pi fun _ : Fin n => P).real
        {x : Fin n → EuclideanSpace ℝ (Fin p) | ρ ≤ |modifiedCovMatrix x j k - S j k|})
      atTop (𝓝 0) := by
    intro j k ρ hρ
    have h := tendsto_pi_real_lln (P := P)
      (fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j * y.ofLp k)
      (integrable_ofLp_mul P hL2 j k) hρ
    refine h.congr fun n => ?_
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, modifiedCovMatrix, Matrix.of_apply, hsecond j k]
  have hllnsum : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun n : ℕ => ∑ j : Fin p, ∑ k : Fin p,
      (Measure.pi fun _ : Fin n => P).real
        {x : Fin n → EuclideanSpace ℝ (Fin p) | ρ ≤ |modifiedCovMatrix x j k - S j k|})
      atTop (𝓝 0) := by
    intro ρ hρ
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin p))
      (fun j (_ : j ∈ Finset.univ) => tendsto_finset_sum (Finset.univ : Finset (Fin p))
        fun k (_ : k ∈ Finset.univ) => hlln j k ρ hρ)
    simpa using h
  refine weakConverges_randPairLaw_of_tendstoInProb_avg
    (fun n : ℕ => Measure.pi fun _ : Fin n => P)
    (fun n : ℕ => modifiedTSq (p := p) (n := n))
    (fun (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin p)) =>
      (fun v : EuclideanSpace ℝ (Fin p) => v.ofLp ⬝ᵥ S⁻¹.mulVec v.ofLp)
        ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i))
    (fun _ => measurable_modifiedTSq)
    (fun _ => (measurable_quadFormInv S).comp measurable_signSum)
    (fun _ ε => measurable_signChange_smul_vec ε) ?_ hconv
  -- The remainder. Only the vector statistic moves along the group, so the difference is
  -- the quadratic form of the *matrix* error `Σ̃ₙ⁻¹ − S⁻¹` at the randomized vector.
  intro δ hδ
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hMpos, hMev⟩ :=
    exists_tight_bound_of_weakConverges hmarg (show (0 : ℝ) < ε / 2 by positivity)
  have hden : (0 : ℝ) < (p : ℝ) ^ 2 * M + 1 := by positivity
  set η : ℝ := δ / ((p : ℝ) ^ 2 * M + 1) with hηdef
  have hηpos : 0 < η := div_pos hδ hden
  obtain ⟨ρ, hρpos, hρ⟩ := exists_entrywise_tol_matrix_inv hpd hηpos
  have hkey : (p : ℝ) ^ 2 * η * M < δ := by
    have hrw : (p : ℝ) ^ 2 * η * M = δ * ((p : ℝ) ^ 2 * M) / ((p : ℝ) ^ 2 * M + 1) := by
      rw [hηdef]; field_simp
    rw [hrw, div_lt_iff₀ hden]
    nlinarith
  have hllnev :=
    (hllnsum ρ hρpos).eventually (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [hMev, hllnev, eventually_gt_atTop 0] with n hn0 hn1 hnpos
  have hmeasM : MeasurableSet {y : ℝ | M ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  -- The two-way inclusion at each sign pattern.
  have hincl : ∀ g : Fin n → ℤˣ,
      {x : Fin n → EuclideanSpace ℝ (Fin p) | δ ≤ ‖modifiedTSq (g • x) -
          ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i :
              EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ S⁻¹.mulVec
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)).ofLp‖}
        ⊆ (⋃ jk : Fin p × Fin p,
              {x : Fin n → EuclideanSpace ℝ (Fin p) |
                ρ ≤ |modifiedCovMatrix x jk.1 jk.2 - S jk.1 jk.2|})
          ∪ {x : Fin n → EuclideanSpace ℝ (Fin p) |
              M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|} := by
    intro g x hx
    simp only [Set.mem_setOf_eq, modifiedTSq_signChange hnpos g x, Real.norm_eq_abs] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_le, Prod.forall] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hentry : ∀ j k, |(modifiedCovMatrix x)⁻¹ j k - S⁻¹ j k| ≤ η := fun j k =>
      (hρ (modifiedCovMatrix x) (fun j' k' => hc1 j' k') j k).le
    have hbound := abs_quadForm_sub_le
      (M := (modifiedCovMatrix x)⁻¹) (N := S⁻¹)
      ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)) hentry
    have hnv : ‖((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p))‖ ^ 2 < M := by
      rwa [abs_of_nonneg (by positivity)] at hc2
    have hmul : (p : ℝ) ^ 2 * η *
        ‖((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p))‖ ^ 2
          ≤ (p : ℝ) ^ 2 * η * M :=
      mul_le_mul_of_nonneg_left hnv.le (by positivity)
    linarith
  -- Turn the inclusion into a bound on the group mixture.
  have hstep : ∀ g : Fin n → ℤˣ,
      (Measure.pi fun _ : Fin n => P).real
          {x : Fin n → EuclideanSpace ℝ (Fin p) | δ ≤ ‖modifiedTSq (g • x) -
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i :
                EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ S⁻¹.mulVec
              ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)).ofLp‖}
        ≤ (∑ j : Fin p, ∑ k : Fin p, (Measure.pi fun _ : Fin n => P).real
              {x : Fin n → EuclideanSpace ℝ (Fin p) |
                ρ ≤ |modifiedCovMatrix x j k - S j k|})
          + (Measure.pi fun _ : Fin n => P).real
              {x : Fin n → EuclideanSpace ℝ (Fin p) |
                M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|} := by
    intro g
    have hmono := measureReal_mono (μ := Measure.pi fun _ : Fin n => P) (hincl g)
      (measure_ne_top _ _)
    have hunion := measureReal_union_le (μ := Measure.pi fun _ : Fin n => P)
      (⋃ jk : Fin p × Fin p,
        {x : Fin n → EuclideanSpace ℝ (Fin p) | ρ ≤ |modifiedCovMatrix x jk.1 jk.2 - S jk.1 jk.2|})
      {x : Fin n → EuclideanSpace ℝ (Fin p) |
        M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|}
    have hiUnion : (Measure.pi fun _ : Fin n => P).real
        (⋃ jk : Fin p × Fin p,
          {x : Fin n → EuclideanSpace ℝ (Fin p) |
            ρ ≤ |modifiedCovMatrix x jk.1 jk.2 - S jk.1 jk.2|})
        ≤ ∑ j : Fin p, ∑ k : Fin p, (Measure.pi fun _ : Fin n => P).real
            {x : Fin n → EuclideanSpace ℝ (Fin p) |
              ρ ≤ |modifiedCovMatrix x j k - S j k|} :=
      (measureReal_iUnion_fintype_le _).trans_eq (by rw [Fintype.sum_prod_type])
    linarith
  -- The tail term, averaged over the group, is the first marginal of the randomized pair.
  have hmargval : ((randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i‖ ^ 2)
        (Measure.pi fun _ : Fin n => P)).map Prod.fst).real {y : ℝ | M ≤ |y|}
      = (Fintype.card (Fin n → ℤˣ) : ℝ)⁻¹ * ∑ g : Fin n → ℤˣ,
          (Measure.pi fun _ : Fin n => P).real
            {x : Fin n → EuclideanSpace ℝ (Fin p) |
              M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|} := by
    have hset : (Prod.fst ⁻¹' {y : ℝ | M ≤ |y|} : Set (ℝ × ℝ))
        = {y : ℝ | M ≤ |y|} ×ˢ (Set.univ : Set ℝ) := by ext z; simp [Set.mem_prod]
    rw [Measure.real, Measure.map_apply measurable_fst hmeasM, hset]
    exact real_randPairLaw_prod_univ (G := Fin n → ℤˣ) _ _ (hwm.comp measurable_signSum)
      (fun ε => measurable_signChange_smul_vec ε) hmeasM
  rw [hmargval] at hn0
  have hcard : (0 : ℝ) < (Fintype.card (Fin n → ℤˣ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum := Finset.sum_le_sum fun g (_ : g ∈ (Finset.univ : Finset (Fin n → ℤˣ))) => hstep g
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hnonneg : (0 : ℝ) ≤ (Fintype.card (Fin n → ℤˣ) : ℝ)⁻¹ *
      ∑ g : Fin n → ℤˣ, (Measure.pi fun _ : Fin n => P).real
        {x : Fin n → EuclideanSpace ℝ (Fin p) | δ ≤ ‖modifiedTSq (g • x) -
          ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i :
              EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ S⁻¹.mulVec
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)).ofLp‖} :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => measureReal_nonneg)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hfinal := mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.2 hcard))
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul] at hfinal
  linarith

/-! ### Hotelling's statistic: the same reduction with a moving matrix

Hotelling's `Σ̂ₙ` is *not* sign-invariant, so both the vector statistic and the matrix move
along the group. The three lemmas below show that the motion of the matrix is `O(1/n)`
uniformly on the tightness event, so the reduction of the previous section survives verbatim
with one extra estimate. -/

/-- A coordinate of the sample mean, written out. -/
private lemma sampleMeanVec_ofLp {n : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin p)) (j : Fin p) :
    (sampleMeanVec y).ofLp j = (n : ℝ)⁻¹ * ∑ i, (y i).ofLp j := by
  simp [sampleMeanVec, Finset.sum_apply]

/-- A coordinate of the normalized sum, written out. -/
private lemma signSum_ofLp {n : ℕ} (y : Fin n → EuclideanSpace ℝ (Fin p)) (j : Fin p) :
    ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i : EuclideanSpace ℝ (Fin p)).ofLp j
      = (Real.sqrt (n : ℝ))⁻¹ * ∑ i, (y i).ofLp j := by
  simp [Finset.sum_apply]

/-- **Recentring identity.** The centred cross-moment equals the uncentred one minus `n`
times the product of the two means. -/
private lemma sum_centred_mul_eq {n : ℕ} (hn : 0 < n) (y : Fin n → EuclideanSpace ℝ (Fin p))
    (j k : Fin p) :
    ∑ i, ((y i).ofLp j - (sampleMeanVec y).ofLp j) * ((y i).ofLp k - (sampleMeanVec y).ofLp k)
      = (∑ i, (y i).ofLp j * (y i).ofLp k)
        - (n : ℝ) * ((sampleMeanVec y).ofLp j * (sampleMeanVec y).ofLp k) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsumj : ∑ i, (y i).ofLp j = (n : ℝ) * (sampleMeanVec y).ofLp j := by
    rw [sampleMeanVec_ofLp, ← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul]
  have hsumk : ∑ i, (y i).ofLp k = (n : ℝ) * (sampleMeanVec y).ofLp k := by
    rw [sampleMeanVec_ofLp, ← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul]
  have hexp : ∀ i, ((y i).ofLp j - (sampleMeanVec y).ofLp j) *
      ((y i).ofLp k - (sampleMeanVec y).ofLp k)
      = (y i).ofLp j * (y i).ofLp k
        - (sampleMeanVec y).ofLp k * (y i).ofLp j
        - (sampleMeanVec y).ofLp j * (y i).ofLp k
        + (sampleMeanVec y).ofLp j * (sampleMeanVec y).ofLp k := fun i => by ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hsumj, hsumk]
  ring

/-- **The sample covariance recomputed at a sign pattern, entrywise.** Sign changes leave the
uncentred sum alone, so only the rank-one mean correction moves:
`Σ̂ₙ(ε·x) = (n−1)⁻¹(n Σ̃ₙ(x) − Vₙ(ε·x)Vₙ(ε·x)ᵀ)`. -/
private lemma sampleCovMatrix_signChange_entry {n : ℕ} (hn : 0 < n) (ε : Fin n → ℤˣ)
    (x : Fin n → EuclideanSpace ℝ (Fin p)) (j k : Fin p) :
    sampleCovMatrix (ε • x) j k
      = ((n : ℝ) - 1)⁻¹ * ((n : ℝ) * modifiedCovMatrix x j k
          - ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i : EuclideanSpace ℝ (Fin p)).ofLp j
            * ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i : EuclideanSpace ℝ (Fin p)).ofLp k) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  have hsq : (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ = ((n : ℝ))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hnR.le]
  -- the uncentred cross-moment is sign-invariant
  have hunc : ∑ i, ((ε • x) i).ofLp j * ((ε • x) i).ofLp k
      = (n : ℝ) * modifiedCovMatrix x j k := by
    have hEq : ∀ i, ((ε • x) i).ofLp j * ((ε • x) i).ofLp k
        = (x i).ofLp j * (x i).ofLp k := by
      intro i
      have h : (ε • x) i = ((ε i : ℤ) : ℝ) • x i := signChange_smul_apply_vec ε x i
      have hs : (((ε i : ℤ) : ℝ)) * (((ε i : ℤ) : ℝ)) = 1 := by
        rcases Int.units_eq_one_or (ε i) with h1 | h1 <;> rw [h1] <;> norm_num
      rw [h]
      simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      linear_combination (x i).ofLp j * (x i).ofLp k * hs
    simp only [hEq, modifiedCovMatrix, Matrix.of_apply, ← mul_assoc,
      mul_inv_cancel₀ hnR.ne', one_mul]
  -- the mean correction is the rank-one term in `Vₙ`
  have hmean : (n : ℝ) * ((sampleMeanVec (ε • x)).ofLp j * (sampleMeanVec (ε • x)).ofLp k)
      = ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i : EuclideanSpace ℝ (Fin p)).ofLp j
        * ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i : EuclideanSpace ℝ (Fin p)).ofLp k := by
    rw [sampleMeanVec_ofLp, sampleMeanVec_ofLp, signSum_ofLp, signSum_ofLp]
    have hrhs : ((Real.sqrt (n : ℝ))⁻¹ * ∑ i, ((ε • x) i).ofLp j)
        * ((Real.sqrt (n : ℝ))⁻¹ * ∑ i, ((ε • x) i).ofLp k)
        = ((Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹)
          * ((∑ i, ((ε • x) i).ofLp j) * (∑ i, ((ε • x) i).ofLp k)) := by ring
    rw [hrhs, hsq]
    field_simp
  rw [sampleCovMatrix, Matrix.of_apply, sum_centred_mul_eq hn, hunc, hmean]

/-- **Hotelling's statistic in terms of the normalized sum.** Dividing the sample mean by its
own normalization, `Tₙ(y) = Vₙ(y)ᵀ Σ̂ₙ(y)⁻¹ Vₙ(y)`; no invariance is used. -/
private lemma hotellingTSq_eq {n : ℕ} (hn : 0 < n) (y : Fin n → EuclideanSpace ℝ (Fin p)) :
    hotellingTSq y
      = ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i : EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ
          (sampleCovMatrix y)⁻¹.mulVec
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i : EuclideanSpace ℝ (Fin p)).ofLp := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : (Real.sqrt (n : ℝ))⁻¹ ^ 2 = ((n : ℝ))⁻¹ := by
    rw [← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
  have hmean : (sampleMeanVec y : EuclideanSpace ℝ (Fin p)) = ((n : ℝ))⁻¹ • ∑ i, y i := rfl
  rw [hotellingTSq, hmean, quadFormInv_smul _ ((n : ℝ))⁻¹,
    quadFormInv_smul _ ((Real.sqrt (n : ℝ))⁻¹), hsq]
  field_simp

/-- **The matrix motion is `O(1/n)`.** Hotelling's matrix differs from the sign-invariant
uncentred one by the rank-one mean correction, controlled by the size of the vector
statistic. -/
private lemma abs_sampleCov_sub_le {n : ℕ} (hn : 0 < n) {S : Matrix (Fin p) (Fin p) ℝ}
    (ε : Fin n → ℤˣ) (x : Fin n → EuclideanSpace ℝ (Fin p)) (j k : Fin p)
    (hn1 : (0 : ℝ) ≤ ((n : ℝ) - 1)⁻¹) (hne : (n : ℝ) - 1 ≠ 0) :
    |sampleCovMatrix (ε • x) j k - S j k|
      ≤ |modifiedCovMatrix x j k - S j k|
        + ((n : ℝ) - 1)⁻¹ * (|modifiedCovMatrix x j k|
            + ‖((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i : EuclideanSpace ℝ (Fin p))‖ ^ 2) := by
  set v : EuclideanSpace ℝ (Fin p) :=
    (Real.sqrt (n : ℝ))⁻¹ • ∑ i, (ε • x) i with hvdef
  have hstep : sampleCovMatrix (ε • x) j k - modifiedCovMatrix x j k
      = ((n : ℝ) - 1)⁻¹ * (modifiedCovMatrix x j k - v.ofLp j * v.ofLp k) := by
    rw [sampleCovMatrix_signChange_entry hn ε x j k, ← hvdef]
    field_simp
    ring
  have hprod : |v.ofLp j * v.ofLp k| ≤ ‖v‖ ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul (abs_ofLp_le_norm v j) (abs_ofLp_le_norm v k) (abs_nonneg _) (norm_nonneg v)
  have hfirst : |sampleCovMatrix (ε • x) j k - modifiedCovMatrix x j k|
      ≤ ((n : ℝ) - 1)⁻¹ * (|modifiedCovMatrix x j k| + ‖v‖ ^ 2) := by
    rw [hstep, abs_mul, abs_of_nonneg hn1]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hn1
    exact add_le_add_right hprod _
  calc |sampleCovMatrix (ε • x) j k - S j k|
      ≤ |sampleCovMatrix (ε • x) j k - modifiedCovMatrix x j k|
          + |modifiedCovMatrix x j k - S j k| := by
        have := abs_add_le (sampleCovMatrix (ε • x) j k - modifiedCovMatrix x j k)
          (modifiedCovMatrix x j k - S j k)
        simpa using this
    _ ≤ |modifiedCovMatrix x j k - S j k|
          + ((n : ℝ) - 1)⁻¹ * (|modifiedCovMatrix x j k| + ‖v‖ ^ 2) := by linarith

/-- The entries of the sample covariance matrix are measurable. -/
private lemma measurable_sampleCovMatrix_entry {n : ℕ} (j k : Fin p) :
    Measurable fun x : Fin n → EuclideanSpace ℝ (Fin p) => sampleCovMatrix x j k := by
  simp only [sampleCovMatrix, Matrix.of_apply]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  exact ((measurable_coord i j).sub (measurable_sampleMeanVec_coord j)).mul
    ((measurable_coord i k).sub (measurable_sampleMeanVec_coord k))

/-- Hotelling's `T²` statistic is measurable. -/
private lemma measurable_hotellingTSq {n : ℕ} :
    Measurable (hotellingTSq (p := p) (n := n)) := by
  have hfun : (hotellingTSq (p := p) (n := n))
      = fun x => (n : ℝ) * ∑ j, ∑ k, (sampleCovMatrix x)⁻¹ j k *
          ((sampleMeanVec x).ofLp j * (sampleMeanVec x).ofLp k) := by
    funext x
    rw [hotellingTSq, quadForm_eq]
  rw [hfun]
  refine Measurable.const_mul (Finset.measurable_sum _ fun j _ =>
    Finset.measurable_sum _ fun k _ => ?_) _
  exact (measurable_inv_of_entries (fun j' k' => measurable_sampleCovMatrix_entry j' k') j
      k).mul ((measurable_sampleMeanVec_coord j).mul (measurable_sampleMeanVec_coord k))

set_option maxHeartbeats 1000000 in
-- Same unification cost as the sibling assembly for the modified statistic.
/-- **Sign-change randomization for Hotelling's `T²` statistic.** Same limit as for the
modified statistic — a product of two independent `χ²_p` laws — obtained by showing that
the centred sample covariance recomputed at a random sign pattern is still consistent for
`S`. Since the unconditional limit of the statistic is also `χ²_p`, the randomization test
based on `Tₙ` has rejection probability tending to the nominal level under any law with
mean `0` and finite second moments, while remaining exact whenever `Xᵢ` and `−Xᵢ` are
identically distributed. -/
theorem weakConverges_randPairLaw_signChange_hotellingTSq [NeZero p]
    (P : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure P]
    {S : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: nondegenerate covariance
    (hpd : S.PosDef)
    -- USER-INPUT: finite second moments of the observation vector
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: the population mean vanishes; the null hypothesis under test
    (hmean : ∫ x, x ∂P = 0)
    -- USER-INPUT: `S` is the second-moment matrix (= the covariance here)
    (hsecond : ∀ j k, ∫ x, x.ofLp j * x.ofLp k ∂P = S j k) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ) (hotellingTSq (p := p) (n := n))
        (Measure.pi fun _ : Fin n => P))
      ((chiSquared p).prod (chiSquared p)) := by
  classical
  -- Same reference statistic, same reference limit, same three ingredients as for the
  -- modified statistic; the only new step is that the matrix now moves along the group, by
  -- an amount that is `O(1/n)` on the tightness event.
  have hconv := weakConverges_randPairLaw_quadFormInv P hpd hL2 hmean hsecond
  have hwm : Measurable fun v : EuclideanSpace ℝ (Fin p) => ‖v‖ ^ 2 :=
    (by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin p) => ‖v‖ ^ 2).measurable
  haveI hprobW : ∀ n : ℕ, IsProbabilityMeasure
      (randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i‖ ^ 2)
        (Measure.pi fun _ : Fin n => P)) := fun n =>
    isProbabilityMeasure_randPairLaw (G := Fin n → ℤˣ) _ _ (hwm.comp measurable_signSum)
      (fun ε => measurable_signChange_smul_vec ε)
  haveI : ∀ n : ℕ, IsProbabilityMeasure
      ((randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i‖ ^ 2)
        (Measure.pi fun _ : Fin n => P)).map Prod.fst) := fun n =>
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map
        (fun v : EuclideanSpace ℝ (Fin p) => ‖v‖ ^ 2)) :=
    Measure.isProbabilityMeasure_map hwm.aemeasurable
  have hmarg := weakConverges_randPairLaw_normSq P hpd hL2 hmean hsecond
  have hlln : ∀ (j k : Fin p) (ρ : ℝ), 0 < ρ → Tendsto (fun n : ℕ =>
      (Measure.pi fun _ : Fin n => P).real
        {x : Fin n → EuclideanSpace ℝ (Fin p) | ρ ≤ |modifiedCovMatrix x j k - S j k|})
      atTop (𝓝 0) := by
    intro j k ρ hρ
    have h := tendsto_pi_real_lln (P := P)
      (fun y : EuclideanSpace ℝ (Fin p) => y.ofLp j * y.ofLp k)
      (integrable_ofLp_mul P hL2 j k) hρ
    refine h.congr fun n => ?_
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, modifiedCovMatrix, Matrix.of_apply, hsecond j k]
  have hllnsum : ∀ ρ : ℝ, 0 < ρ → Tendsto (fun n : ℕ => ∑ j : Fin p, ∑ k : Fin p,
      (Measure.pi fun _ : Fin n => P).real
        {x : Fin n → EuclideanSpace ℝ (Fin p) | ρ ≤ |modifiedCovMatrix x j k - S j k|})
      atTop (𝓝 0) := by
    intro ρ hρ
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin p))
      (fun j (_ : j ∈ Finset.univ) => tendsto_finset_sum (Finset.univ : Finset (Fin p))
        fun k (_ : k ∈ Finset.univ) => hlln j k ρ hρ)
    simpa using h
  refine weakConverges_randPairLaw_of_tendstoInProb_avg
    (fun n : ℕ => Measure.pi fun _ : Fin n => P)
    (fun n : ℕ => hotellingTSq (p := p) (n := n))
    (fun (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin p)) =>
      (fun v : EuclideanSpace ℝ (Fin p) => v.ofLp ⬝ᵥ S⁻¹.mulVec v.ofLp)
        ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i))
    (fun _ => measurable_hotellingTSq)
    (fun _ => (measurable_quadFormInv S).comp measurable_signSum)
    (fun _ ε => measurable_signChange_smul_vec ε) ?_ hconv
  intro δ hδ
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨M, hMpos, hMev⟩ :=
    exists_tight_bound_of_weakConverges hmarg (show (0 : ℝ) < ε / 2 by positivity)
  have hden : (0 : ℝ) < (p : ℝ) ^ 2 * M + 1 := by positivity
  set η : ℝ := δ / ((p : ℝ) ^ 2 * M + 1) with hηdef
  have hηpos : 0 < η := div_pos hδ hden
  obtain ⟨ρ, hρpos, hρ⟩ := exists_entrywise_tol_matrix_inv hpd hηpos
  have hkey : (p : ℝ) ^ 2 * η * M < δ := by
    have hrw : (p : ℝ) ^ 2 * η * M = δ * ((p : ℝ) ^ 2 * M) / ((p : ℝ) ^ 2 * M + 1) := by
      rw [hηdef]; field_simp
    rw [hrw, div_lt_iff₀ hden]
    nlinarith
  -- A uniform bound on the entries of the sample matrix on the "matrix is close" event.
  set C : ℝ := (∑ j : Fin p, ∑ k : Fin p, |S j k|) + ρ with hCdef
  have hSle : ∀ j k : Fin p, |S j k| ≤ ∑ j : Fin p, ∑ k : Fin p, |S j k| := by
    intro j k
    refine le_trans (Finset.single_le_sum (f := fun k' => |S j k'|)
      (fun k' _ => abs_nonneg _) (Finset.mem_univ k)) ?_
    exact Finset.single_le_sum (f := fun j' => ∑ k' : Fin p, |S j' k'|)
      (fun j' _ => Finset.sum_nonneg fun k' _ => abs_nonneg _) (Finset.mem_univ j)
  have hCpos : (0 : ℝ) < C + M := by
    have : (0 : ℝ) ≤ ∑ j : Fin p, ∑ k : Fin p, |S j k| :=
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
    rw [hCdef]; linarith
  -- The matrix motion is `O(1/n)`, hence eventually negligible.
  have htend : Tendsto (fun n : ℕ => ((n : ℝ) - 1)⁻¹ * (C + M)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop
    simpa using (tendsto_inv_atTop_zero.comp h1).mul_const (C + M)
  have hsmallev :=
    htend.eventually (eventually_lt_nhds (show (0 : ℝ) < ρ / 2 by positivity))
  have hllnev :=
    (hllnsum (ρ / 2) (by positivity)).eventually
      (eventually_lt_nhds (show (0 : ℝ) < ε / 2 by positivity))
  filter_upwards [hMev, hllnev, hsmallev, eventually_gt_atTop 1] with n hn0 hn1 hn2 hnpos
  have hnpos0 : 0 < n := lt_trans Nat.zero_lt_one hnpos
  have hnR1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn1nonneg : (0 : ℝ) ≤ ((n : ℝ) - 1)⁻¹ := inv_nonneg.2 (by linarith)
  have hmeasM : MeasurableSet {y : ℝ | M ≤ |y|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hincl : ∀ g : Fin n → ℤˣ,
      {x : Fin n → EuclideanSpace ℝ (Fin p) | δ ≤ ‖hotellingTSq (g • x) -
          ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i :
              EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ S⁻¹.mulVec
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)).ofLp‖}
        ⊆ (⋃ jk : Fin p × Fin p,
              {x : Fin n → EuclideanSpace ℝ (Fin p) |
                ρ / 2 ≤ |modifiedCovMatrix x jk.1 jk.2 - S jk.1 jk.2|})
          ∪ {x : Fin n → EuclideanSpace ℝ (Fin p) |
              M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|} := by
    intro g x hx
    simp only [Set.mem_setOf_eq, hotellingTSq_eq hnpos0 (g • x), Real.norm_eq_abs] at hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or, not_exists,
      not_le, Prod.forall] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hnv : ‖((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p))‖ ^ 2 < M := by
      rwa [abs_of_nonneg (by positivity)] at hc2
    -- Hotelling's matrix is close to `S` too: it differs from the sign-invariant one by a
    -- rank-one term of size `O(1/n)`.
    have hclose : ∀ j k, |sampleCovMatrix (g • x) j k - S j k| < ρ := by
      intro j k
      have hbase := abs_sampleCov_sub_le (S := S) hnpos0 g x j k hn1nonneg hne
      have hsmall : |modifiedCovMatrix x j k| ≤ C := by
        have h1 : |modifiedCovMatrix x j k| ≤ |modifiedCovMatrix x j k - S j k| + |S j k| := by
          have := abs_add_le (modifiedCovMatrix x j k - S j k) (S j k)
          simpa using this
        have := hSle j k
        rw [hCdef]
        linarith [hc1 j k]
      have hmono : ((n : ℝ) - 1)⁻¹ * (|modifiedCovMatrix x j k|
            + ‖((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p))‖ ^ 2)
          ≤ ((n : ℝ) - 1)⁻¹ * (C + M) :=
        mul_le_mul_of_nonneg_left (by linarith) hn1nonneg
      linarith [hc1 j k]
    have hentry : ∀ j k, |(sampleCovMatrix (g • x))⁻¹ j k - S⁻¹ j k| ≤ η := fun j k =>
      (hρ (sampleCovMatrix (g • x)) (fun j' k' => hclose j' k') j k).le
    have hbound := abs_quadForm_sub_le
      (M := (sampleCovMatrix (g • x))⁻¹) (N := S⁻¹)
      ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)) hentry
    have hmul : (p : ℝ) ^ 2 * η *
        ‖((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p))‖ ^ 2
          ≤ (p : ℝ) ^ 2 * η * M :=
      mul_le_mul_of_nonneg_left hnv.le (by positivity)
    linarith
  have hstep : ∀ g : Fin n → ℤˣ,
      (Measure.pi fun _ : Fin n => P).real
          {x : Fin n → EuclideanSpace ℝ (Fin p) | δ ≤ ‖hotellingTSq (g • x) -
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i :
                EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ S⁻¹.mulVec
              ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)).ofLp‖}
        ≤ (∑ j : Fin p, ∑ k : Fin p, (Measure.pi fun _ : Fin n => P).real
              {x : Fin n → EuclideanSpace ℝ (Fin p) |
                ρ / 2 ≤ |modifiedCovMatrix x j k - S j k|})
          + (Measure.pi fun _ : Fin n => P).real
              {x : Fin n → EuclideanSpace ℝ (Fin p) |
                M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|} := by
    intro g
    have hmono := measureReal_mono (μ := Measure.pi fun _ : Fin n => P) (hincl g)
      (measure_ne_top _ _)
    have hunion := measureReal_union_le (μ := Measure.pi fun _ : Fin n => P)
      (⋃ jk : Fin p × Fin p,
        {x : Fin n → EuclideanSpace ℝ (Fin p) |
          ρ / 2 ≤ |modifiedCovMatrix x jk.1 jk.2 - S jk.1 jk.2|})
      {x : Fin n → EuclideanSpace ℝ (Fin p) |
        M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|}
    have hiUnion : (Measure.pi fun _ : Fin n => P).real
        (⋃ jk : Fin p × Fin p,
          {x : Fin n → EuclideanSpace ℝ (Fin p) |
            ρ / 2 ≤ |modifiedCovMatrix x jk.1 jk.2 - S jk.1 jk.2|})
        ≤ ∑ j : Fin p, ∑ k : Fin p, (Measure.pi fun _ : Fin n => P).real
            {x : Fin n → EuclideanSpace ℝ (Fin p) |
              ρ / 2 ≤ |modifiedCovMatrix x j k - S j k|} :=
      (measureReal_iUnion_fintype_le _).trans_eq (by rw [Fintype.sum_prod_type])
    linarith
  have hmargval : ((randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → EuclideanSpace ℝ (Fin p) =>
          ‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, x i‖ ^ 2)
        (Measure.pi fun _ : Fin n => P)).map Prod.fst).real {y : ℝ | M ≤ |y|}
      = (Fintype.card (Fin n → ℤˣ) : ℝ)⁻¹ * ∑ g : Fin n → ℤˣ,
          (Measure.pi fun _ : Fin n => P).real
            {x : Fin n → EuclideanSpace ℝ (Fin p) |
              M ≤ |‖(Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i‖ ^ 2|} := by
    have hset : (Prod.fst ⁻¹' {y : ℝ | M ≤ |y|} : Set (ℝ × ℝ))
        = {y : ℝ | M ≤ |y|} ×ˢ (Set.univ : Set ℝ) := by ext z; simp [Set.mem_prod]
    rw [Measure.real, Measure.map_apply measurable_fst hmeasM, hset]
    exact real_randPairLaw_prod_univ (G := Fin n → ℤˣ) _ _ (hwm.comp measurable_signSum)
      (fun ε => measurable_signChange_smul_vec ε) hmeasM
  rw [hmargval] at hn0
  have hcard : (0 : ℝ) < (Fintype.card (Fin n → ℤˣ) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum := Finset.sum_le_sum fun g (_ : g ∈ (Finset.univ : Finset (Fin n → ℤˣ))) => hstep g
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hnonneg : (0 : ℝ) ≤ (Fintype.card (Fin n → ℤˣ) : ℝ)⁻¹ *
      ∑ g : Fin n → ℤˣ, (Measure.pi fun _ : Fin n => P).real
        {x : Fin n → EuclideanSpace ℝ (Fin p) | δ ≤ ‖hotellingTSq (g • x) -
          ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i :
              EuclideanSpace ℝ (Fin p)).ofLp ⬝ᵥ S⁻¹.mulVec
            ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, (g • x) i : EuclideanSpace ℝ (Fin p)).ofLp‖} :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun g _ => measureReal_nonneg)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hfinal := mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.2 hcard))
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul] at hfinal
  linarith

end StatLean.HypothesisTesting
