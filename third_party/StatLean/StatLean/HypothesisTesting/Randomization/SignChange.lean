module
public import StatLean.HypothesisTesting.Randomization.Asymptotics
public import StatLean.HypothesisTesting.Randomization.PairCLT
public import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# The sign-change randomization test is asymptotically normal

For i.i.d. real observations $X_1, \dots, X_n$ the natural randomization group is the
group of **sign changes**: $\varepsilon = (\varepsilon_1, \dots, \varepsilon_n)$ with
$\varepsilon_i \in \{\pm 1\}$ acting by
$(\varepsilon \cdot x)_i = \varepsilon_i x_i$, a group of order $2^n$. If the common law
is symmetric about $0$ the randomization hypothesis holds, and the resulting test is exact
at every sample size. The point of this file is what happens *asymptotically*, in
particular when symmetry fails.

Assume the statistic is **asymptotically linear**,
$$ T_n = n^{-1/2}\sum_{i=1}^n \psi(X_i) + o_P(1), \qquad
   \tau^2 = \operatorname{Var}[\psi(X_1)] < \infty , $$
with $\psi$ an **odd** function. Then:

* if the common law is symmetric about $0$, the randomization distribution satisfies
  $\hat R_n(t) \xrightarrow{P} \Phi(t/\tau)$;
* if it is not, let $\tilde P$ be its **symmetrization**, the law with c.d.f.
  $\tilde F(t) = \tfrac12\bigl[F(t) + 1 - F(-t)\bigr]$, and assume asymptotic linearity
  under $\tilde P$; then, still under the original law,
  $\hat R_n(t) \xrightarrow{P} \Phi(t/\tau(\tilde P))$ and
  $\hat r_n(1-\alpha) \xrightarrow{P} \tau(\tilde P)\, z_{1-\alpha}$.

The second part is the reason the sign-change test is usable without symmetry: the
randomization distribution still stabilizes, at the symmetrized model's scale.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.2 (Permutation and Randomization Tests), Theorem 17.2.4 (the
sign-change randomization distribution is asymptotically normal). (`TSH4 §17.2 Thm 17.2.4`.)

**Proof formalization notes.**
* *The sign-change group.* It is `Fin n → ℤˣ`: the units of `ℤ` are exactly `±1`, so this
  is `{±1}ⁿ` on the nose, a finite abelian group of order `2ⁿ` (`card_signChangeGroup`).
  Its action on `Fin n → ℝ` is Mathlib's componentwise action, obtained by composing
  `Pi.mulAction'` (a product of monoids acting componentwise), `Units.instMulAction`
  (`u • a = (u : M) • a`) and the `ℤ`-module structure of `ℝ`; no new instance is declared
  here, and `signChange_smul_apply` pins the resulting formula
  `(ε • x) i = εᵢ · xᵢ` so that downstream proofs never have to unfold that chain.
* *Symmetrization.* `symmetrize P` is the equal mixture of `P` and its reflection, i.e.
  the law of `X` multiplied by an independent random sign. Its c.d.f. agrees with the
  book's $\tilde F(t) = \tfrac12[F(t) + 1 - F(-t)]$ at every continuity point of $F$; at an
  atom of $P$ located at $-t$ the two differ by half that atom's mass, because
  $1 - F(-t)$ is the *open* upper tail while the reflected measure contributes the closed
  one. The mixture form is the standard object and is what the argument uses (the
  randomization distribution depends on the data only through $|X_1|, \dots, |X_n|$, whose
  law is the same under `P` and `symmetrize P`).
* *Mean-zero is not a hypothesis.* Oddness of `ψ` together with symmetry of the law and
  square-integrability already force $E[\psi(X_1)] = 0$; carrying it as an assumption
  would be laundering a derivable fact through the signature. It is therefore omitted, and
  `τ²` is stated as the **second moment** $\int \psi^2$, which equals the variance exactly
  because the mean vanishes.
* *Nondegeneracy.* `0 < τ` is required so that `Φ(t/τ)` is a c.d.f.; the degenerate case
  `τ = 0` has no limiting distribution of this form.
* *Asymptotic linearity* is stated with the triangular-array convergence in probability of
  `Randomization/Asymptotics`, applied to the remainder
  `T n x − n^{-1/2} ∑ᵢ ψ(xᵢ)`; that is exactly the `o_P(1)` of the display.
* The limit is reached through the bivariate sign-change central limit theorem of the sibling
  file `Randomization/PairCLT` (`weakConverges_randPairLaw_signSum`). That engine works at the
  level of characteristic functions: averaging over the four sign pairs `(s,s') ∈ {±1}²`
  factorizes the joint characteristic function across coordinates *exactly at every finite `n`*,
  so asymptotic independence of the two randomized copies is not a limiting phenomenon but an
  identity, and no mean-zero hypothesis is needed. The passage from the statistic to its linear
  part is `PairCLT.weakConverges_randPairLaw_of_tendstoInProb`, a Slutsky transfer that consumes
  exactly the `o_P(1)` of `hlin` together with sign-invariance of `⊗ⁿP` (which is `hsymm`).
* Oddness of `ψ` enters through the equivariance `ψ(εᵢxᵢ) = εᵢψ(xᵢ)`, which lets the
  coordinatewise map `x ↦ (ψ(xᵢ))ᵢ` intertwine the two sign actions; `randPairLaw_comp` then
  transports the whole randomized pair to the pushforward law `P.map ψ`.

**Bibliographic comments.** Sign-change (randomization) tests for a symmetric location
model go back to R. A. Fisher (*The Design of Experiments*, Oliver & Boyd, Edinburgh,
1935) and E. J. G. Pitman ("Significance tests which may be applied to samples from any
populations," *J. R. Statist. Soc. Suppl.* **4** (1937), 119–130), with the group-theoretic
exactness in E. L. Lehmann and C. Stein ("On the theory of some non-parametric
hypotheses," *Ann. Math. Statist.* **20** (1949), 28–45). The large-sample analysis is due
to W. Hoeffding ("The large-sample power of tests based on permutations of observations,"
*Ann. Math. Statist.* **23** (1952), 169–192); the behaviour without the group invariance
assumption, i.e. the asymmetric case handled here through symmetrization, is
J. P. Romano ("On the behavior of randomization tests without a group invariance
assumption," *J. Amer. Statist. Assoc.* **85** (1990), 686–692), sharpened by E. Chung and
J. P. Romano ("Exact and asymptotically robust permutation tests," *Ann. Statist.* **41**
(2013), 484–507).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-! ### The sign-change group -/

/-- The sign-change action, written out: `(ε • x) i = εᵢ · xᵢ`. The action itself is
Mathlib's componentwise `Pi` action of `Fin n → ℤˣ` on `Fin n → ℝ`; this lemma is the
interface downstream proofs use. -/
lemma signChange_smul_apply {n : ℕ} (ε : Fin n → ℤˣ) (x : Fin n → ℝ) (i : Fin n) :
    (ε • x) i = ((ε i : ℤ) : ℝ) * x i := by
  change ((ε i : ℤ)) • x i = ((ε i : ℤ) : ℝ) * x i
  exact zsmul_eq_mul _ _

/-- The sign-change group has `2ⁿ` elements. -/
lemma card_signChangeGroup (n : ℕ) : Fintype.card (Fin n → ℤˣ) = 2 ^ n := by
  simp [Fintype.card_fun, Fintype.card_units_int]

/-- The sign-change action of a fixed group element is measurable: componentwise it is
multiplication by the constant `±1`. (Unlike the abstract action of `Randomization/Asymptotics`,
here the action is concrete and its measurability is available, so only `Measurable (T n)` is left
implicit in the frozen signatures below.) -/
lemma measurable_signChange_smul {n : ℕ} (ε : Fin n → ℤˣ) :
    Measurable (fun x : Fin n → ℝ => ε • x) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  simp only [signChange_smul_apply]
  exact (measurable_pi_apply i).const_mul _

/-- **Symmetrization** of a law on the line: the equal mixture of `P` and its reflection,
i.e. the law of the data multiplied by an independent random sign. Its c.d.f. is
`t ↦ ½(F(t) + 1 − F(−t))` at every continuity point of `F` (see the file notes for the
atom convention). -/
noncomputable def symmetrize (P : Measure ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (P + P.map (fun t => -t))

/-! ### Gaussian c.d.f. helpers -/

/-- The c.d.f. of an atomless probability measure on `ℝ` is continuous. Right-continuity is
built into the Stieltjes packaging; left-continuity is the vanishing of the atom at `t`. -/
private lemma continuousAt_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NullSingletonClass μ] (t : ℝ) : ContinuousAt (cdf μ) t := by
  have hmono : Monotone (cdf μ) := monotone_cdf μ
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim]
  have hright : Function.rightLim (cdf μ) t = cdf μ t :=
    (hmono.continuousWithinAt_Ioi_iff_rightLim_eq).1
      (((cdf μ).right_continuous t).mono Set.Ioi_subset_Ici_self)
  have hle : Function.leftLim (cdf μ) t ≤ cdf μ t := hmono.leftLim_le le_rfl
  have hge : cdf μ t ≤ Function.leftLim (cdf μ) t := by
    have h0 := (cdf μ).measure_singleton t
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero, sub_nonpos] at h0
    exact h0
  rw [le_antisymm hle hge, hright]

/-- Gaussian scaling of the c.d.f.: `cdf (N(0,τ²)) t = cdf (N(0,1)) (t/τ)` for `τ > 0`. -/
private lemma cdf_gaussianReal_scale {τ : ℝ} (hτ : 0 < τ) (t : ℝ) :
    cdf (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))) t = cdf (gaussianReal 0 1) (t / τ) := by
  have hmap : gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))
      = (gaussianReal 0 1).map (fun x => τ * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · rw [mul_zero]
    · rw [mul_one]
  have hset : (fun x : ℝ => τ * x) ⁻¹' Set.Iic t = Set.Iic (t / τ) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ hτ, mul_comm τ x]
  rw [cdf_eq_real, cdf_eq_real, hmap, measureReal_def, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Iic, hset]

/-! ### Symmetric case -/

/-- **The sign-change randomization distribution is asymptotically Gaussian (symmetric
case).** For i.i.d. data symmetric about `0` and an asymptotically linear statistic with
odd influence function `ψ` and scale `τ`, the doubly randomized statistic converges jointly
to a product of centred Gaussians with variance `τ²` — i.e. the hypothesis of the general
asymptotic randomization theorem holds with `R = N(0, τ²)`. -/
theorem weakConverges_randPairLaw_signChange (P : Measure ℝ) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ : ℝ}
    -- USER-INPUT: the common law is symmetric about `0`; the randomization hypothesis
    -- for the sign-change group
    (hsymm : P.map (fun t => -t) = P)
    -- USER-INPUT: the influence function is odd; needed for `ψ(εᵢXᵢ) = εᵢψ(Xᵢ)`
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable; user-supplied function
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment of the influence function
    (hψL2 : MemLp ψ 2 P)
    -- LEAN-ONLY: nondegenerate scale, so that `Φ(·/τ)` is a c.d.f.; the degenerate case
    -- `τ = 0` has no limit law of this form and is excluded rather than formalized
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of the influence function (equal to its second
    -- moment, since oddness and symmetry force the mean to vanish)
    (hτ : ∫ t, (ψ t) ^ 2 ∂P = τ ^ 2)
    -- USER-INPUT: the statistic is measurable (data regularity). NOT derivable from the
    -- other hypotheses and genuinely needed: for a non-measurable statistic every
    -- `randPairLaw` degenerates to the zero measure (Bernstein-set construction), so the
    -- conclusion is false without it. Mirrors `Randomization/Asymptotics.lean`.
    (hT : ∀ n, Measurable (T n))
    -- USER-INPUT: the statistic is asymptotically linear with influence function `ψ`
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0) :
    WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ) (T n) (Measure.pi fun _ : Fin n => P))
      ((gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))).prod
        (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))) := by
  classical
  -- The linear part of the statistic, and the law of the influence function.
  set Q : Measure ℝ := P.map ψ with hQdef
  haveI hQprob : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hψmeas.aemeasurable
  have hQ2 : MemLp id 2 Q := by
    rw [hQdef, memLp_map_measure_iff aestronglyMeasurable_id hψmeas.aemeasurable]
    simpa using hψL2
  have hτQ : ∫ y, y ^ 2 ∂Q = τ ^ 2 := by
    rw [hQdef, integral_map hψmeas.aemeasurable (by fun_prop)]
    exact hτ
  -- The product law is invariant under every sign change (symmetry of `P`).
  have hinv : ∀ (n : ℕ) (ε : Fin n → ℤˣ),
      (Measure.pi fun _ : Fin n => P).map (fun x => ε • x) = Measure.pi fun _ : Fin n => P := by
    intro n ε
    refine (Measure.pi_eq (fun s hs => ?_)).symm
    rw [Measure.map_apply (measurable_signChange_smul ε) (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → ℝ => ε • x) ⁻¹' Set.pi Set.univ s
        = Set.pi Set.univ (fun i => (fun xi : ℝ => ((ε i : ℤ) : ℝ) * xi) ⁻¹' s i) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, signChange_smul_apply]
    rw [hpre, Measure.pi_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases Int.units_eq_one_or (ε i) with h | h
    · rw [h]
      congr 1
      ext xi
      simp
    · rw [h]
      have hset : (fun xi : ℝ => (((-1 : ℤˣ) : ℤ) : ℝ) * xi) ⁻¹' s i
          = (fun t : ℝ => -t) ⁻¹' s i := by
        ext xi
        simp
      rw [hset, ← Measure.map_apply measurable_neg (hs i), hsymm]
  -- Coordinatewise application of `ψ` pushes the product law to the product of `Q`.
  have hΨmeas : ∀ n : ℕ, Measurable (fun x : Fin n → ℝ => fun i => ψ (x i)) := fun n =>
    measurable_pi_lambda _ fun i => hψmeas.comp (measurable_pi_apply i)
  have hpush : ∀ n : ℕ, (Measure.pi fun _ : Fin n => P).map (fun x : Fin n → ℝ => fun i => ψ (x i))
      = Measure.pi fun _ : Fin n => Q := by
    intro n
    refine (Measure.pi_eq (fun s hs => ?_)).symm
    rw [Measure.map_apply (hΨmeas n) (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → ℝ => fun i => ψ (x i)) ⁻¹' Set.pi Set.univ s
        = Set.pi Set.univ (fun i => ψ ⁻¹' s i) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    rw [hpre, Measure.pi_pi]
    exact Finset.prod_congr rfl fun i _ => by rw [hQdef, Measure.map_apply hψmeas (hs i)]
  -- Oddness makes the coordinatewise `ψ` equivariant for the sign-change action.
  have hequiv : ∀ (n : ℕ) (ε : Fin n → ℤˣ) (x : Fin n → ℝ),
      (fun i => ψ ((ε • x) i)) = ε • fun i => ψ (x i) := by
    intro n ε x
    funext i
    rw [signChange_smul_apply, signChange_smul_apply]
    rcases Int.units_eq_one_or (ε i) with h | h
    · rw [h]; simp
    · rw [h]
      simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
      exact hodd _
  -- The randomized pair of the linear part is that of the plain sign-flipped sum under `Q`.
  have hsumsmul : ∀ (n : ℕ) (ε : Fin n → ℤˣ),
      Measurable fun y : Fin n → ℝ => ε • y := fun n ε => measurable_signChange_smul ε
  have hsumT : ∀ n : ℕ,
      Measurable fun y : Fin n → ℝ => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i := fun n =>
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_mul
      ((Real.sqrt (n : ℝ))⁻¹)
  have hid : ∀ n : ℕ,
      randPairLaw (Fin n → ℤˣ) (fun x : Fin n → ℝ => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, ψ (x i))
          (Measure.pi fun _ : Fin n => P)
        = randPairLaw (Fin n → ℤˣ)
            (fun y : Fin n → ℝ => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, y i)
            (Measure.pi fun _ : Fin n => Q) := by
    intro n
    have hcomp := randPairLaw_comp (G := Fin n → ℤˣ) (Measure.pi fun _ : Fin n => P)
      (hΨmeas n) (fun ε x => hequiv n ε x) (hsumT n) (hsumsmul n)
    rw [hpush n] at hcomp
    exact hcomp
  -- The bivariate sign-change CLT for the plain sum, with the Gaussian identified.
  have hchar : ∀ v : ℝ, charFun (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))) v
      = Complex.exp (-((∫ y, ⟪y, v⟫ ^ 2 ∂Q : ℝ) : ℂ) / 2) := by
    intro v
    have hmom : ∫ y, ⟪y, v⟫ ^ 2 ∂Q = v ^ 2 * τ ^ 2 := by
      have hpt : ∀ y : ℝ, ⟪y, v⟫ ^ 2 = v ^ 2 * y ^ 2 := by
        intro y
        have : ⟪y, v⟫ = v * y := by
          simp [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
        rw [this]; ring
      calc ∫ y, ⟪y, v⟫ ^ 2 ∂Q = ∫ y, v ^ 2 * y ^ 2 ∂Q :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = v ^ 2 * τ ^ 2 := by rw [integral_const_mul, hτQ]
    rw [charFun_gaussianReal, hmom]
    congr 1
    push_cast
    ring
  have hCLT := weakConverges_randPairLaw_signSum Q hQ2
    (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))) hchar
  have hCLT' : WeakConverges
      (fun n => randPairLaw (Fin n → ℤˣ)
        (fun x : Fin n → ℝ => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, ψ (x i))
        (Measure.pi fun _ : Fin n => P))
      ((gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))).prod (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))) := by
    simpa only [hid] using hCLT
  -- Slutsky: replace the linear part by the statistic itself.
  refine weakConverges_randPairLaw_of_tendstoInProb (G := fun n => Fin n → ℤˣ)
    (fun n => Measure.pi fun _ : Fin n => P) T
    (fun n x => (Real.sqrt (n : ℝ))⁻¹ * ∑ i, ψ (x i)) hT
    (fun n => ((Finset.measurable_sum _ fun i _ =>
      hψmeas.comp (measurable_pi_apply i))).const_mul _)
    (fun n ε => measurable_signChange_smul ε) (fun n ε => hinv n ε) ?_ hCLT'
  intro δ hδ
  simpa only [Real.norm_eq_abs, sub_zero] using hlin δ hδ


/-- **Consequence: the randomization distribution converges to `Φ(·/τ)`.** Under the
hypotheses above, `R̂ₙ(t) →P Φ(t/τ)` for every `t`. -/
theorem randDist_signChange_tendstoInProb (P : Measure ℝ) [IsProbabilityMeasure P]
    (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ : ℝ}
    -- USER-INPUT: the common law is symmetric about `0`
    (hsymm : P.map (fun t => -t) = P)
    -- USER-INPUT: the influence function is odd
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment of the influence function
    (hψL2 : MemLp ψ 2 P)
    -- LEAN-ONLY: nondegenerate scale (see above)
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of the influence function
    (hτ : ∫ t, (ψ t) ^ 2 ∂P = τ ^ 2)
    -- USER-INPUT: the statistic is measurable (data regularity). NOT derivable from the
    -- other hypotheses and genuinely needed: for a non-measurable statistic every
    -- `randPairLaw` degenerates to the zero measure (Bernstein-set construction), so the
    -- conclusion is false without it. Mirrors `Randomization/Asymptotics.lean`.
    (hT : ∀ n, Measurable (T n))
    -- USER-INPUT: the statistic is asymptotically linear with influence function `ψ`
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0)
    (t : ℝ) :
    TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => randDist (Fin n → ℤˣ) (T n) x t)
      (cdf (gaussianReal 0 1) (t / τ)) := by
  -- Feed the bivariate CLT (`weakConverges_randPairLaw_signChange`) into the forward engine
  -- `randDist_tendstoInProb_cdf`, discharging measurability of the action with
  -- `measurable_signChange_smul` and continuity of the Gaussian c.d.f. with
  -- `continuousAt_cdf_of_noAtoms`, then rewrite the limit via `cdf_gaussianReal_scale`.
  have hjoint := weakConverges_randPairLaw_signChange P ψ T hsymm hodd hψmeas hψL2 hτpos hτ hT hlin
  have hvne : (NNReal.mk (τ ^ 2) (sq_nonneg τ)) ≠ 0 :=
    NNReal.coe_ne_zero.mp (by rw [NNReal.coe_mk]; positivity)
  haveI : NullSingletonClass (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ))) := nullSingletonClass_gaussianReal hvne
  have hcont : ContinuousAt (cdf (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))) t :=
    continuousAt_cdf_of_noAtoms _ t
  have hmain := randDist_tendstoInProb_cdf (G := fun n => Fin n → ℤˣ)
    (fun n => Measure.pi fun _ : Fin n => P) T (gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)))
    hT (fun n => measurable_signChange_smul) hjoint hcont
  rwa [cdf_gaussianReal_scale hτpos t] at hmain

/-! ### Symmetrization: transfer of the randomization law -/

/-- The randomization distribution is constant on orbits: `R̂(σ • x, t) = R̂(x, t)`. This is
pure group reindexing (`g ↦ g σ` is a bijection of `G`), and is what makes `R̂` a function of
`|x₁|, …, |xₙ|` only. -/
private lemma randDist_smul_invariant {G 𝓧 : Type*} [Group G] [Fintype G]
    [MeasurableSpace 𝓧] [MulAction G 𝓧] (T : 𝓧 → ℝ) (σ : G) (x : 𝓧) (t : ℝ) :
    randDist G T (σ • x) t = randDist G T x t := by
  unfold randDist
  congr 1
  rw [← Equiv.sum_comp (Equiv.mulRight σ)
    (fun g : G => if T (g • x) ≤ t then (1 : ℝ) else 0)]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  rw [Equiv.coe_mulRight, mul_smul]

/-- The randomization distribution is a measurable function of the data. -/
private lemma measurable_randDist {G 𝓧 : Type*} [Group G] [Fintype G]
    [MeasurableSpace 𝓧] [MulAction G 𝓧] {T : 𝓧 → ℝ} (hT : Measurable T)
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) (t : ℝ) :
    Measurable (fun x => randDist G T x t) := by
  unfold randDist
  refine Measurable.const_mul (Finset.measurable_sum _ (fun g _ => ?_)) _
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (hT.comp (hsmul g)) measurableSet_Iic

/-- `symmetrize P` is a probability measure. -/
instance isProbabilityMeasure_symmetrize (P : Measure ℝ) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (symmetrize P) := by
  constructor
  rw [symmetrize, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply measurable_neg MeasurableSet.univ, Set.preimage_univ, measure_univ,
    smul_eq_mul, one_add_one_eq_two,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

/-- `symmetrize P` is invariant under reflection. -/
private lemma symmetrize_map_neg (P : Measure ℝ) :
    (symmetrize P).map (fun t => -t) = symmetrize P := by
  have hneg : Measurable (fun t : ℝ => -t) := measurable_neg
  rw [symmetrize, Measure.map_smul, Measure.map_add _ _ hneg, Measure.map_map hneg hneg]
  have hid : (fun t : ℝ => -t) ∘ (fun t : ℝ => -t) = id := by ext t; simp
  rw [hid, Measure.map_id, add_comm]

/-- **The product of the symmetrized law is the sign-change average of the product law.**
`⊗ⁿ (symmetrize P) = 2⁻ⁿ ∑_{σ ∈ {±1}ⁿ} (⊗ⁿ P).map (σ • ·)`. Proved by matching both sides on
measurable rectangles (`Measure.pi_eq`): the box mass factorizes and the product of the
two-term mixtures expands into the sum over sign vectors. -/
private lemma pi_symmetrize_eq (P : Measure ℝ) [IsProbabilityMeasure P] (n : ℕ) :
    Measure.pi (fun _ : Fin n => symmetrize P)
      = ((2 : ℝ≥0∞) ^ n)⁻¹ •
        ∑ σ : Fin n → ℤˣ, (Measure.pi (fun _ : Fin n => P)).map (fun x => σ • x) := by
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply]
  have hterm : ∀ σ : Fin n → ℤˣ,
      ((Measure.pi (fun _ : Fin n => P)).map (fun x => σ • x)) (Set.pi Set.univ s)
        = ∏ i, P ((fun xi : ℝ => ((σ i : ℤ) : ℝ) * xi) ⁻¹' s i) := by
    intro σ
    rw [Measure.map_apply (measurable_signChange_smul σ) (MeasurableSet.univ_pi hs)]
    rw [show (fun x : Fin n → ℝ => σ • x) ⁻¹' Set.pi Set.univ s
          = Set.pi Set.univ (fun i => (fun xi : ℝ => ((σ i : ℤ) : ℝ) * xi) ⁻¹' s i) from ?_]
    · exact Measure.pi_pi _ _
    · ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, signChange_smul_apply]
  simp_rw [hterm]
  have hsum : (∑ σ : Fin n → ℤˣ, ∏ i, P ((fun xi : ℝ => ((σ i : ℤ) : ℝ) * xi) ⁻¹' s i))
      = ∏ i : Fin n, ∑ u : ℤˣ, P ((fun xi : ℝ => ((u : ℤ) : ℝ) * xi) ⁻¹' s i) := by
    rw [Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ℤˣ))
      (fun i u => P ((fun xi : ℝ => ((u : ℤ) : ℝ) * xi) ⁻¹' s i)), Fintype.piFinset_univ]
  rw [hsum]
  have hcol : ∀ i, (∑ u : ℤˣ, P ((fun xi : ℝ => ((u : ℤ) : ℝ) * xi) ⁻¹' s i))
      = P (s i) + (P.map (fun t => -t)) (s i) := by
    intro i
    rw [show (Finset.univ : Finset ℤˣ) = {1, -1} from UnitsInt.univ,
      Finset.sum_pair (by decide : (1 : ℤˣ) ≠ -1)]
    congr 1
    · congr 1; ext xi; simp
    · rw [Measure.map_apply measurable_neg (hs i)]
      congr 1; ext xi; simp [Units.val_neg]
  simp_rw [hcol]
  have hRHS : ∀ i, symmetrize P (s i)
      = (2 : ℝ≥0∞)⁻¹ * (P (s i) + (P.map (fun t => -t)) (s i)) := by
    intro i; rw [symmetrize, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  simp_rw [hRHS]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow]

/-- **Transfer on sign-invariant sets.** For a measurable set `S` fixed by every sign change,
`⊗ⁿ(symmetrize P)` and `⊗ⁿ P` assign it the same mass — the averaging identity collapses since
each pushforward returns `S`. -/
private lemma pi_symmetrize_apply_invariant (P : Measure ℝ) [IsProbabilityMeasure P] (n : ℕ)
    (S : Set (Fin n → ℝ)) (hS : MeasurableSet S)
    (hinv : ∀ σ : Fin n → ℤˣ, (fun x : Fin n → ℝ => σ • x) ⁻¹' S = S) :
    Measure.pi (fun _ : Fin n => symmetrize P) S = Measure.pi (fun _ : Fin n => P) S := by
  rw [pi_symmetrize_eq P n, Measure.smul_apply, smul_eq_mul, Measure.finset_sum_apply]
  have hmap : ∀ σ : Fin n → ℤˣ,
      ((Measure.pi (fun _ : Fin n => P)).map (fun x => σ • x)) S
        = Measure.pi (fun _ : Fin n => P) S := by
    intro σ; rw [Measure.map_apply (measurable_signChange_smul σ) hS, hinv σ]
  simp_rw [hmap]
  rw [Finset.sum_const, Finset.card_univ, card_signChangeGroup, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, ← mul_assoc,
    ENNReal.inv_mul_cancel (pow_ne_zero n (by norm_num)) (ENNReal.pow_ne_top (by norm_num)),
    one_mul]

/-! ### Asymmetric case, via the symmetrized model -/

/-- **The randomization distribution stabilizes even without symmetry.** If the common law
is *not* symmetric about `0`, asymptotic linearity is assumed under the symmetrized law
`symmetrize P`, with odd influence function `ψ` and scale `τ`. Then, under the original
law, `R̂ₙ(t) →P Φ(t/τ)` — the randomization distribution converges to the symmetrized
model's Gaussian, not to the true sampling distribution. -/
theorem randDist_signChange_tendstoInProb_symmetrized (P : Measure ℝ)
    [IsProbabilityMeasure P] (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ : ℝ}
    -- USER-INPUT: the influence function is odd
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment under the **symmetrized** law
    (hψL2 : MemLp ψ 2 (symmetrize P))
    -- LEAN-ONLY: nondegenerate scale (see above)
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of `ψ` under the **symmetrized** law
    (hτ : ∫ t, (ψ t) ^ 2 ∂(symmetrize P) = τ ^ 2)
    -- USER-INPUT: the statistic is measurable (data regularity). NOT derivable from the
    -- other hypotheses and genuinely needed: for a non-measurable statistic every
    -- `randPairLaw` degenerates to the zero measure (Bernstein-set construction), so the
    -- conclusion is false without it. Mirrors `Randomization/Asymptotics.lean`.
    (hT : ∀ n, Measurable (T n))
    -- USER-INPUT: the statistic is asymptotically linear **under the symmetrized law**
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => symmetrize P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0)
    (t : ℝ) :
    TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => randDist (Fin n → ℤˣ) (T n) x t)
      (cdf (gaussianReal 0 1) (t / τ)) := by
  -- Apply the symmetric-case result under `symmetrize P` (where `hsymm` holds by
  -- `symmetrize_map_neg`), then transfer the level-set masses from `Measure.pi (symmetrize P)`
  -- back to `Measure.pi P`: the randomization distribution is sign-invariant
  -- (`randDist_smul_invariant`), so its level sets are fixed by the sign-change group, and the
  -- two product measures agree there (`pi_symmetrize_apply_invariant`).
  intro ε hε
  have hconv := randDist_signChange_tendstoInProb (symmetrize P) ψ T (symmetrize_map_neg P)
    hodd hψmeas hψL2 hτpos hτ hT hlin t ε hε
  refine hconv.congr (fun n => ?_)
  set c := cdf (gaussianReal 0 1) (t / τ) with hc
  set S : Set (Fin n → ℝ) := {x | ε ≤ |randDist (Fin n → ℤˣ) (T n) x t - c|} with hS
  have hg : Measurable (fun x : Fin n → ℝ => randDist (Fin n → ℤˣ) (T n) x t) :=
    measurable_randDist (hT n) (fun g => measurable_signChange_smul g) t
  have hSmeas : MeasurableSet S :=
    measurableSet_le measurable_const ((hg.sub measurable_const).abs)
  have hinv : ∀ σ : Fin n → ℤˣ, (fun x : Fin n → ℝ => σ • x) ⁻¹' S = S := by
    intro σ; ext x
    simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, randDist_smul_invariant]
  rw [measureReal_def, measureReal_def, pi_symmetrize_apply_invariant P n S hSmeas hinv]

/-- The c.d.f. of a nondegenerate centred Gaussian is strictly increasing (its density is
strictly positive, so every interval carries strictly positive mass). -/
private lemma strictMono_cdf_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) :
    StrictMono (cdf (gaussianReal 0 v)) := by
  intro y z hyz
  rw [cdf_eq_real, cdf_eq_real]
  have hpos : 0 < gaussianReal 0 v (Set.Ioc y z) := by
    rw [pos_iff_ne_zero]; intro h0
    have hvol := (gaussianReal_absolutelyContinuous' 0 hv) h0
    rw [Real.volume_Ioc] at hvol
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne' hvol
  have hdisj : gaussianReal 0 v (Set.Iic z)
      = gaussianReal 0 v (Set.Iic y) + gaussianReal 0 v (Set.Ioc y z) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hyz.le]
  rw [measureReal_def, measureReal_def, hdisj,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  have hp2 : 0 < (gaussianReal 0 v (Set.Ioc y z)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

/-- Every level `p ∈ (0,1)` is attained by a continuous c.d.f. of an atomless probability
measure (intermediate value theorem, using the `0`/`1` limits at `∓∞`). -/
private lemma exists_cdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : ∃ q, cdf μ q = p := by
  have hcont : Continuous (cdf μ) :=
    continuous_iff_continuousAt.mpr (fun x => continuousAt_cdf_of_noAtoms μ x)
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hp0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hp1)).exists
  have hab : min a b ≤ max a b := min_le_max
  have hca' : cdf μ (min a b) < p := lt_of_le_of_lt (monotone_cdf (μ := μ) (min_le_left a b)) ha
  have hcb' : p < cdf μ (max a b) := lt_of_lt_of_le hb (monotone_cdf (μ := μ) (le_max_right a b))
  obtain ⟨q, _, hq⟩ := intermediate_value_Icc hab hcont.continuousOn ⟨hca'.le, hcb'.le⟩
  exact ⟨q, hq⟩

/-- The randomization quantile is constant on orbits (its sublevel set of `randDist` is). -/
private lemma randQuantile_smul_invariant {G 𝓧 : Type*} [Group G] [Fintype G]
    [MeasurableSpace 𝓧] [MulAction G 𝓧] (T : 𝓧 → ℝ) {p : ℝ} (σ : G) (x : 𝓧) :
    randQuantile G T p (σ • x) = randQuantile G T p x := by
  unfold randQuantile
  congr 1; ext t
  simp only [Set.mem_setOf_eq, randDist_smul_invariant]

/-- The randomization quantile is a measurable function of the data: its strict sublevel set
is a countable union (over rational thresholds) of `randDist` sublevel sets. -/
private lemma measurable_randQuantile {G 𝓧 : Type*} [Group G] [Fintype G]
    [MeasurableSpace 𝓧] [MulAction G 𝓧] {T : 𝓧 → ℝ} (hT : Measurable T)
    (hsmul : ∀ g : G, Measurable (fun x : 𝓧 => g • x)) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    Measurable (fun x => randQuantile G T p x) := by
  haveI : Nonempty G := ⟨1⟩
  have hne : ∀ x : 𝓧, ({t : ℝ | p ≤ randDist G T x t}).Nonempty := by
    intro x
    refine ⟨Finset.univ.sup' Finset.univ_nonempty (fun g : G => T (g • x)), ?_⟩
    have hone : randDist G T x
        (Finset.univ.sup' Finset.univ_nonempty (fun g : G => T (g • x))) = 1 := by
      unfold randDist
      rw [Finset.sum_congr rfl (fun g _ => if_pos
        (Finset.le_sup' (fun g : G => T (g • x)) (Finset.mem_univ g))),
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]
    rw [Set.mem_setOf_eq, hone]; exact hp1
  apply measurable_of_Iio
  intro r
  have hset : (fun x => randQuantile G T p x) ⁻¹' Set.Iio r
      = ⋃ s : {s : ℚ // (s : ℝ) < r}, {x | p ≤ randDist G T x (s : ℝ)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq, Subtype.exists]
    constructor
    · intro hlt
      obtain ⟨t, ht_mem, ht_lt⟩ :=
        (csInf_lt_iff (bddBelow_randDist_sublevel G T x hp0) (hne x)).mp hlt
      obtain ⟨s, hts, hsr⟩ := exists_rat_btwn ht_lt
      exact ⟨s, hsr, le_trans ht_mem (randDist_mono G T x hts.le)⟩
    · rintro ⟨s, hsr, hs⟩
      exact lt_of_le_of_lt (csInf_le (bddBelow_randDist_sublevel G T x hp0) hs) hsr
  rw [hset]
  exact MeasurableSet.iUnion (fun s =>
    measurableSet_le measurable_const (measurable_randDist hT hsmul (s : ℝ)))

/-- **The randomization critical value converges to `τ z_{1−α}`.** Companion of the
previous statement: the data-dependent critical value of the sign-change test converges in
probability to the symmetrized model's Gaussian quantile. -/
theorem randQuantile_signChange_tendstoInProb_symmetrized (P : Measure ℝ)
    [IsProbabilityMeasure P] (ψ : ℝ → ℝ) (T : ∀ n, (Fin n → ℝ) → ℝ) {τ α : ℝ}
    -- USER-INPUT: the influence function is odd
    (hodd : ∀ t, ψ (-t) = -ψ t)
    -- USER-INPUT: the influence function is measurable
    (hψmeas : Measurable ψ)
    -- USER-INPUT: finite second moment under the **symmetrized** law
    (hψL2 : MemLp ψ 2 (symmetrize P))
    -- LEAN-ONLY: nondegenerate scale (see above)
    (hτpos : 0 < τ)
    -- USER-INPUT: `τ²` is the variance of `ψ` under the **symmetrized** law
    (hτ : ∫ t, (ψ t) ^ 2 ∂(symmetrize P) = τ ^ 2)
    -- USER-INPUT: nominal level strictly between `0` and `1`; the calibration range
    (hα₀ : 0 < α) (hα₁ : α < 1)
    -- USER-INPUT: the statistic is measurable (data regularity). NOT derivable from the
    -- other hypotheses and genuinely needed: for a non-measurable statistic every
    -- `randPairLaw` degenerates to the zero measure (Bernstein-set construction), so the
    -- conclusion is false without it. Mirrors `Randomization/Asymptotics.lean`.
    (hT : ∀ n, Measurable (T n))
    -- USER-INPUT: the statistic is asymptotically linear **under the symmetrized law**
    (hlin : TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => symmetrize P)
      (fun n x => T n x - (Real.sqrt n)⁻¹ * ∑ i, ψ (x i)) 0) :
    TendstoInProbTriangular (fun n => Measure.pi fun _ : Fin n => P)
      (fun n x => randQuantile (Fin n → ℤˣ) (T n) (1 - α) x)
      (τ * cdfQuantile (gaussianReal 0 1) (1 - α)) := by
  -- Feed the joint law from `weakConverges_randPairLaw_signChange` (under `symmetrize P`) into
  -- `randQuantile_tendstoInProb`, with the limit `R = N(0,τ²)`: continuity from
  -- `nullSingletonClass_gaussianReal`, the two-sided bracketing from `strictMono_cdf_gaussianReal` at the
  -- level `1-α` (attained by `exists_cdf_eq`). Then rewrite the limiting quantile via the
  -- Gaussian scaling (`cdf_gaussianReal_scale` + `quantile_eq_of_strictMono`) and transfer the
  -- level-set masses back to `Measure.pi P` (sign invariance of `randQuantile`).
  set R := gaussianReal 0 (NNReal.mk (τ ^ 2) (sq_nonneg τ)) with hRdef
  have hvne : (NNReal.mk (τ ^ 2) (sq_nonneg τ)) ≠ 0 :=
    NNReal.coe_ne_zero.mp (by rw [NNReal.coe_mk]; positivity)
  haveI : NullSingletonClass R := nullSingletonClass_gaussianReal hvne
  have hp0 : (0 : ℝ) < 1 - α := by linarith
  have hp1 : (1 : ℝ) - α < 1 := by linarith
  have hSM : StrictMono (cdf R) := strictMono_cdf_gaussianReal hvne
  obtain ⟨q, hq⟩ := exists_cdf_eq R hp0 hp1
  have hqquant : cdfQuantile R (1 - α) = q := quantile_eq_of_strictMono hSM hq
  have hcont : ContinuousAt (cdf R) (cdfQuantile R (1 - α)) :=
    continuousAt_cdf_of_noAtoms R _
  have hstrict : ∀ ε > (0 : ℝ), cdf R (cdfQuantile R (1 - α) - ε) < 1 - α ∧
      1 - α < cdf R (cdfQuantile R (1 - α) + ε) := by
    intro ε hε
    rw [hqquant]
    refine ⟨?_, ?_⟩
    · rw [← hq]; exact hSM (by linarith)
    · rw [← hq]; exact hSM (by linarith)
  -- Gaussian scaling of the limiting quantile.
  have hSM1 : StrictMono (cdf (gaussianReal 0 1)) := strictMono_cdf_gaussianReal one_ne_zero
  have hscale : cdf (gaussianReal 0 1) (q / τ) = 1 - α := by
    rw [← cdf_gaussianReal_scale hτpos q]; exact hq
  have hq0 : cdfQuantile (gaussianReal 0 1) (1 - α) = q / τ :=
    quantile_eq_of_strictMono hSM1 hscale
  have hτ0 : τ ≠ 0 := ne_of_gt hτpos
  have hlimit : cdfQuantile R (1 - α) = τ * cdfQuantile (gaussianReal 0 1) (1 - α) := by
    rw [hqquant, hq0]; field_simp
  -- The joint law under the symmetrized model, then the quantile engine.
  have hjoint := weakConverges_randPairLaw_signChange (symmetrize P) ψ T (symmetrize_map_neg P)
    hodd hψmeas hψL2 hτpos hτ hT hlin
  rw [← hRdef] at hjoint
  have hmain := randQuantile_tendstoInProb (G := fun n => Fin n → ℤˣ)
    (fun n => Measure.pi fun _ : Fin n => symmetrize P) T R hT
    (fun n => measurable_signChange_smul) hjoint hα₀ hα₁ hcont hstrict
  rw [hlimit] at hmain
  -- Transfer the level-set masses from `Measure.pi (symmetrize P)` to `Measure.pi P`.
  intro ε hε
  refine (hmain ε hε).congr (fun n => ?_)
  set c := τ * cdfQuantile (gaussianReal 0 1) (1 - α) with hc
  set S : Set (Fin n → ℝ) :=
    {x | ε ≤ |randQuantile (Fin n → ℤˣ) (T n) (1 - α) x - c|} with hS
  have hgq : Measurable (fun x : Fin n → ℝ => randQuantile (Fin n → ℤˣ) (T n) (1 - α) x) :=
    measurable_randQuantile (hT n) (fun g => measurable_signChange_smul g) hp0 (le_of_lt hp1)
  have hSmeas : MeasurableSet S :=
    measurableSet_le measurable_const ((hgq.sub measurable_const).abs)
  have hinv : ∀ σ : Fin n → ℤˣ, (fun x : Fin n → ℝ => σ • x) ⁻¹' S = S := by
    intro σ; ext x
    simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, randQuantile_smul_invariant]
  rw [measureReal_def, measureReal_def, pi_symmetrize_apply_invariant P n S hSmeas hinv]

end StatLean.HypothesisTesting
