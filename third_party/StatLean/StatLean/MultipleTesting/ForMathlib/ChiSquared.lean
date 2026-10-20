module
public import StatLean.MultipleTesting.ForMathlib.GammaMoments
public import StatLean.MultipleTesting.ForMathlib.GaussianSquareMGF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-!
# The chi-squared distribution and the sum-of-squares law

This file defines the chi-squared distribution through Mathlib's Gamma family and proves the
**exact distributional law**: if $Z_1, \dots, Z_n$ are independent standard Gaussian random
variables, $Z_i \sim N(0,1)$, then their sum of squares follows a chi-squared distribution with
$n$ degrees of freedom,
$$ \sum_{i=1}^{n} Z_i^2 \;\sim\; \chi^2_n . $$
Here $\chi^2_n$ is defined as the Gamma distribution with shape $n/2$ and rate $1/2$, i.e.
$\chi^2_n := \mathrm{Gamma}(n/2,\, 1/2)$, which is a probability measure for $n \ge 1$. Alongside
the law we record the basic functionals of $\chi^2_n$:

* the moment generating function $\;\mathbb{E}\!\left[e^{tX}\right] = \left(\tfrac{1/2}{1/2 - t}\right)^{n/2} = (1 - 2t)^{-n/2}\;$ for $t < 1/2$ (`mgf_chiSquared`);
* the mean $\;\mathbb{E}[X] = n\;$ (`integral_id_chiSquared`) and variance $\;\mathrm{Var}(X) = 2n\;$ (`variance_chiSquared`), obtained from the Gamma mean $a/r$ and variance $a/r^2$ evaluated at $a = n/2$, $r = 1/2$.

These moments feed the chi-squared test's null-hypothesis moments $\mathbb{E}[T_n] = n$,
$\mathrm{Var}[T_n] = 2n$ (used in `ChiSquaredTest/Distribution.lean`). The result is
theorem-agnostic and is placed in the `ForMathlib` layer.

Note on hypotheses: the Lean statement requires $n \ge 1$ (so that $\chi^2_n$ is a genuine
probability measure), and takes the three standard inputs of the i.i.d. setup explicitly —
measurability of each $Z_i$, the marginal law $Z_i \sim N(0,1)$, and joint independence of the
family. The book states the result for an i.i.d. standard Gaussian sample; these are exactly
that hypothesis made precise.

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford
University, 2023. Lecture 2, §2.3 (the chi-squared distribution and its connection to the squared
norm of a Gaussian vector).

**Proof formalization notes.** The proof is by matching moment generating functions and then
appealing to the fact that equal MGFs on a neighbourhood of $0$ (equivalently, equal
characteristic functions) determine the law.

* By independence, the MGF of $\sum_i Z_i^2$ factors as the product of the per-coordinate MGFs of
  $Z_i^2$. For $t < 1/2$ each squared-standard-Gaussian MGF equals $(1 - 2t)^{-1/2} = (\sqrt{1-2t})^{-1}$ (`mgf_exp_sq_stdGaussian`), so the product is $(\sqrt{1-2t})^{-n}$; the `rpow` bridge
  `chiSq_mgf_rpow_bridge` reconciles this with the Gamma MGF $\left(\tfrac{1/2}{1/2-t}\right)^{n/2}$.
* For $t \ge 1/2$ both MGFs vanish: the integrand $e^{t x^2}$ (resp. $e^{t x}$) is non-integrable
  under $N(0,1)$ (resp. $\chi^2_n$), via the dedicated half-line integrability bricks
  `integrable_exp_mul_gammaMeasure` / `not_integrable_exp_mul_gammaMeasure` and their $\chi^2$
  specializations. This gives MGF equality on all of $\mathbb{R}$.
* From MGF equality, $0$ lies in the interior of the integrable-exponent set of the statistic, the
  complex MGFs agree on the imaginary axis, and `Measure.ext_of_charFun` concludes equality of the
  two laws. The Gamma MGF and moment lemmas are imported from `GammaMoments.lean` and the
  squared-Gaussian MGF from `GaussianSquareMGF.lean`.

**Bibliographic comments.** This is a folklore result with no single seminal paper. The
distribution of a sum of squared independent normal variates was derived by F. R. Helmert,
"Über die Berechnung des wahrscheinlichen Fehlers aus einer endlichen Anzahl wahrer
Beobachtungsfehler" (*Zeitschrift für Mathematik und Physik* 20, 1875, pp. 300–404), in the
course of studying the distribution of the sample variance. The distribution and its central role
in goodness-of-fit testing were independently popularized by K. Pearson, "On the criterion that a
given system of deviations from the probable in the case of a correlated system of variables is
such that it can be reasonably supposed to have arisen from random sampling" (*Philosophical
Magazine*, Series 5, 50(302), 1900, pp. 157–175). The identity $\sum_i Z_i^2 \sim \chi^2_n$ is now
standard material and is not attributed to a single original theorem.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The **chi-squared distribution** with `k` degrees of freedom, `χ²ₖ := Gamma(k/2, 1/2)`
(Candès L2 §2.3). A probability measure for `k ≥ 1`. -/
noncomputable def chiSquared (k : ℕ) : Measure ℝ := gammaMeasure ((k : ℝ) / 2) (1 / 2)

/-- `χ²ₖ` is a probability measure for `k ≥ 1`. -/
instance isProbabilityMeasure_chiSquared (k : ℕ) [NeZero k] :
    IsProbabilityMeasure (chiSquared k) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne k)
  unfold chiSquared
  exact isProbabilityMeasure_gammaMeasure (by linarith) (by norm_num)

/-- **MGF of `χ²ₖ`**: `E[e^{tX}] = ((1/2)/((1/2)−t))^{k/2}` for `t < 1/2` (`k ≥ 1`) — the
χ² moment generating function `(1−2t)^{−k/2}`. From `mgf_gammaMeasure`. -/
theorem mgf_chiSquared {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, Real.exp (t * x) ∂(chiSquared k) = ((1 / 2) / ((1 / 2) - t)) ^ ((k : ℝ) / 2) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold chiSquared
  exact mgf_gammaMeasure (by linarith) (by norm_num) ht

/-- **Mean of `χ²ₖ`**: `E[X] = k` (`k ≥ 1`). From the Gamma mean `a/r` at `a=k/2`, `r=1/2`. -/
theorem integral_id_chiSquared {k : ℕ} (hk : 0 < k) :
    ∫ x, x ∂(chiSquared k) = (k : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  unfold chiSquared
  rw [integral_id_gammaMeasure (by linarith) (by norm_num)]
  ring

/-- **Variance of `χ²ₖ`**: `E[(X−k)²] = 2k` (`k ≥ 1`). From the Gamma variance `a/r²`. -/
theorem variance_chiSquared {k : ℕ} (hk : 0 < k) :
    ∫ x, (x - (k : ℝ)) ^ 2 ∂(chiSquared k) = 2 * (k : ℝ) := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : (0 : ℝ) < (k : ℝ) / 2 := by linarith
  have hr : (0 : ℝ) < (1 : ℝ) / 2 := by norm_num
  have hcenter : ((k : ℝ) / 2) / (1 / 2) = (k : ℝ) := by ring
  have hvar := variance_gammaMeasure ha hr
  rw [hcenter] at hvar
  unfold chiSquared
  rw [hvar]
  ring

/-! ## MGF-domain integrability bricks for `Gamma(a,r)` -/

/-- **Integrability of `x ↦ exp(l·x)` under `Gamma(a,r)` for `l < r`** (the MGF convergence
half-line). Mirrors `integrable_pow_gammaMeasure`: reduce to `∫_{Ioi 0} C·x^{a−1}·e^{−(r−l)x}`. -/
private lemma integrable_exp_mul_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    {l : ℝ} (hl : l < r) :
    Integrable (fun x => Real.exp (l * x)) (gammaMeasure a r) := by
  have hmeasG : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hmeasG
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rw [show (fun x => Real.exp (l * x) * (gammaPDF a r x).toReal)
        = (fun x => Real.exp (l * x) * gammaPDFReal a r x) from by
      funext x
      rw [show gammaPDF a r x = ENNReal.ofReal (gammaPDFReal a r x) from rfl,
        ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]]
  have hmodel : IntegrableOn (fun x => x ^ (a - 1) * Real.exp (-((r - l) * x)))
      (Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r - l)
      (by linarith) one_pos (by linarith)
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    beta_reduce; rw [Real.rpow_one, neg_mul]
  have hIoi : IntegrableOn (fun x => Real.exp (l * x) * gammaPDFReal a r x) (Ioi 0) volume := by
    refine IntegrableOn.congr_fun (hmodel.const_mul (r ^ a / Real.Gamma a))
      (fun x hx => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hx
    rw [gammaPDFReal, if_pos hx.le,
      show -((r - l) * x) = l * x + -(r * x) from by ring, Real.exp_add]
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, hIoi⟩
  refine integrableOn_zero.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [mem_setOf_eq, Classical.not_imp, mem_Iic] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_eq_of_le hx1 with h | h
  · exact absurd (show Real.exp (l * x) * gammaPDFReal a r x = 0 by
      rw [gammaPDFReal, if_neg (not_le.mpr h), mul_zero]).symm hx2
  · exact h

/-- **Non-integrability of `x ↦ exp(l·x)` under `Gamma(a,r)` for `r ≤ l`**: on `Ioi 1` the
density-weighted integrand `C·x^{a−1}·e^{(l−r)x} ≥ C·x^{a−1}`, and `x^{a−1}` is non-integrable on
`Ioi 1` (since `a − 1 ≥ −1`). Pins the Gamma MGF to `0` past its convergence half-line. -/
private lemma not_integrable_exp_mul_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    {l : ℝ} (hl : r ≤ l) :
    ¬ Integrable (fun x => Real.exp (l * x)) (gammaMeasure a r) := by
  have hmeasG : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integrable_withDensity_iff hmeasG
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  rw [show (fun x => Real.exp (l * x) * (gammaPDF a r x).toReal)
        = (fun x => Real.exp (l * x) * gammaPDFReal a r x) from by
      funext x
      rw [show gammaPDF a r x = ENNReal.ofReal (gammaPDFReal a r x) from rfl,
        ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]]
  intro hInt
  set C : ℝ := r ^ a / Real.Gamma a with hC
  have hCpos : 0 < C := div_pos (Real.rpow_pos_of_pos hr a) (Real.Gamma_pos_of_pos ha)
  have hmodel_ni : ¬ IntegrableOn (fun x => x ^ (a - 1)) (Ioi (1 : ℝ)) volume := by
    rw [integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)]
    intro hlt; linarith
  apply hmodel_ni
  have hI1 : IntegrableOn (fun x => Real.exp (l * x) * gammaPDFReal a r x) (Ioi (1 : ℝ)) volume :=
    hInt.integrableOn
  have hcmp : IntegrableOn (fun x => C * x ^ (a - 1)) (Ioi (1 : ℝ)) volume := by
    refine Integrable.mono hI1 (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    have hxa : (0 : ℝ) ≤ x ^ (a - 1) := Real.rpow_nonneg hx0.le _
    have hexpge : (1 : ℝ) ≤ Real.exp ((l - r) * x) :=
      Real.one_le_exp (mul_nonneg (by linarith) hx0.le)
    rw [gammaPDFReal, if_pos hx0.le, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ C * x ^ (a - 1)),
      abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ Real.exp (l * x) * (C * x ^ (a - 1) * Real.exp (-(r * x)))),
      show Real.exp (l * x) * (C * x ^ (a - 1) * Real.exp (-(r * x)))
          = C * x ^ (a - 1) * Real.exp ((l - r) * x) from by
        rw [show (l - r) * x = l * x + -(r * x) from by ring, Real.exp_add]; ring]
    nlinarith [hexpge, mul_nonneg hCpos.le hxa]
  have hscaled := hcmp.const_mul (C⁻¹)
  refine IntegrableOn.congr_fun hscaled (fun x _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, inv_mul_cancel₀ hCpos.ne', one_mul]

/-- `x ↦ exp(l·x)` is integrable under `χ²ₙ` exactly on the MGF half-line `l < 1/2`. -/
private lemma integrable_exp_mul_chiSquared {n : ℕ} (hn : 0 < n) {l : ℝ} (hl : l < 1 / 2) :
    Integrable (fun x => Real.exp (l * x)) (chiSquared n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold chiSquared
  exact integrable_exp_mul_gammaMeasure (by linarith) (by norm_num) hl

/-- `x ↦ exp(l·x)` is non-integrable under `χ²ₙ` for `1/2 ≤ l`. -/
private lemma not_integrable_exp_mul_chiSquared {n : ℕ} (hn : 0 < n) {l : ℝ} (hl : 1 / 2 ≤ l) :
    ¬ Integrable (fun x => Real.exp (l * x)) (chiSquared n) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold chiSquared
  exact not_integrable_exp_mul_gammaMeasure (by linarith) (by norm_num) hl

/-- **rpow bridge**: `((√(1−2l))⁻¹)ⁿ = ((1/2)/((1/2)−l))^{n/2}` for `l < 1/2` — both equal
`(1−2l)^{−n/2}`. Reconciles the squared-Gaussian MGF power with the χ²ₙ Gamma MGF. -/
private lemma chiSq_mgf_rpow_bridge (n : ℕ) {l : ℝ} (hl : l < 1 / 2) :
    (Real.sqrt (1 - 2 * l))⁻¹ ^ n = ((1 / 2) / ((1 / 2) - l)) ^ ((n : ℝ) / 2) := by
  have hb : (0 : ℝ) < 1 - 2 * l := by linarith
  have hRHSbase : (1 / 2 : ℝ) / ((1 / 2) - l) = (1 - 2 * l)⁻¹ := by
    rw [show (1 / 2 : ℝ) - l = (1 - 2 * l) / 2 from by ring]; field_simp
  have hL : (Real.sqrt (1 - 2 * l))⁻¹ ^ n = (1 - 2 * l) ^ (-(n : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hb.le, ← Real.rpow_natCast _ n, ← Real.rpow_mul hb.le]
    congr 1; ring
  have hR : ((1 / 2 : ℝ) / ((1 / 2) - l)) ^ ((n : ℝ) / 2) = (1 - 2 * l) ^ (-(n : ℝ) / 2) := by
    rw [hRHSbase, show (1 - 2 * l)⁻¹ = (1 - 2 * l) ^ (-1 : ℝ) from by
        rw [Real.rpow_neg hb.le, Real.rpow_one], ← Real.rpow_mul hb.le]
    congr 1; ring
  rw [hL, hR]

/-- **Sum-of-squares law** (Candès L2 §2.3): for i.i.d. `Zᵢ ∼ N(0,1)`, `∑ᵢ Zᵢ² ∼ χ²ₙ`.
The exact distributional identity behind the chi-squared test statistic `Tₙ = ‖Y‖²` under `H₀`. -/
theorem map_sum_sq_eq_chiSquared {n : ℕ} (hn : 0 < n) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Fin n → Ω → ℝ)
    -- USER-INPUT: each Zᵢ is measurable; Candès L2 §2.3
    (hmeas : ∀ i, Measurable (Z i))
    -- USER-INPUT: each Zᵢ ∼ N(0,1); Candès L2 §2.3
    (hlaw : ∀ i, Measure.map (Z i) μ = gaussianReal 0 1)
    -- USER-INPUT: the Zᵢ are jointly independent; Candès L2 §2.3
    (hindep : iIndepFun Z μ) :
    Measure.map (fun ω => ∑ i, (Z i ω) ^ 2) μ = chiSquared n := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  -- the statistic and the per-coordinate squared family
  set S : Ω → ℝ := fun ω => ∑ i, (Z i ω) ^ 2 with hS
  set W : Fin n → Ω → ℝ := fun i ω => (Z i ω) ^ 2 with hW
  have hWmeas : ∀ i, Measurable (W i) := fun i => (hmeas i).pow_const 2
  have hWindep : iIndepFun W μ := by
    have := hindep.comp (fun _ => fun x : ℝ => x ^ 2) (fun _ => by fun_prop)
    simpa [Function.comp, hW] using! this
  have hSsum : S = ∑ i, W i := by
    funext ω; simp only [hS, hW, Finset.sum_apply]
  have hSmeas : Measurable S := by
    rw [hS]; exact Finset.measurable_sum _ (fun i _ => (hmeas i).pow_const 2)
  -- per-coordinate squared-Gaussian MGF: `mgf (W i) μ l = ∫ exp(l y²) dN(0,1)`
  have hWval : ∀ (i : Fin n) (l : ℝ),
      mgf (W i) μ l = ∫ y, Real.exp (l * y ^ 2) ∂(gaussianReal 0 1) := by
    intro i l
    have hg_asm : AEStronglyMeasurable (fun y => Real.exp (l * y ^ 2)) (Measure.map (Z i) μ) :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_pow 2))).aestronglyMeasurable
    simp only [mgf]
    rw [show (fun ω => Real.exp (l * W i ω))
          = (fun ω => (fun y => Real.exp (l * y ^ 2)) (Z i ω)) from by funext ω; simp [hW]]
    rw [← integral_map (hmeas i).aemeasurable hg_asm, hlaw i]
  -- `mgf id (chiSquared n) l = ∫ exp(l x) dχ²ₙ`
  have hidval : ∀ l : ℝ, mgf id (chiSquared n) l = ∫ x, Real.exp (l * x) ∂(chiSquared n) := by
    intro l; simp only [mgf, id_eq]
  -- OBLIGATION A: the two real MGFs agree on all of ℝ
  have hA : mgf S μ = mgf id (chiSquared n) := by
    funext l
    rw [show mgf S μ l = ∏ i, mgf (W i) μ l from by
      rw [hSsum]; exact hWindep.mgf_sum hWmeas Finset.univ]
    rcases lt_or_ge l (1 / 2) with hl | hl
    · -- l < 1/2 : product of squared-Gaussian MGFs vs the Gamma MGF
      have hWi : ∀ i, mgf (W i) μ l = (Real.sqrt (1 - 2 * l))⁻¹ := fun i => by
        rw [hWval i l, mgf_exp_sq_stdGaussian hl]
      rw [Finset.prod_congr rfl (fun i _ => hWi i), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, hidval l, mgf_chiSquared hn hl]
      exact chiSq_mgf_rpow_bridge n hl
    · -- l ≥ 1/2 : both MGFs vanish (non-integrability)
      have hWi0 : ∀ i, mgf (W i) μ l = 0 := fun i => by
        rw [hWval i l, integral_undef (not_integrable_exp_sq_stdGaussian hl)]
      obtain ⟨i0, _⟩ := (Finset.univ_nonempty (α := Fin n))
      rw [Finset.prod_eq_zero (Finset.mem_univ i0) (hWi0 i0), hidval l,
        integral_undef (not_integrable_exp_mul_chiSquared hn hl)]
  -- OBLIGATION B: `0 ∈ interior (integrableExpSet S μ)` via the transferred Gamma half-line
  have hB : (0 : ℝ) ∈ interior (integrableExpSet S μ) := by
    rw [integrableExpSet_eq_of_mgf hA, mem_interior]
    refine ⟨Iio (1 / 2), fun l hl => ?_, isOpen_Iio, mem_Iio.mpr (by norm_num)⟩
    rw [mem_Iio] at hl
    change Integrable (fun x => Real.exp (l * id x)) (chiSquared n)
    simpa only [id_eq] using integrable_exp_mul_chiSquared hn hl
  -- ASSEMBLE: equal char. functions ⇒ equal laws (imaginary axis lies in the MGF strip)
  haveI : IsProbabilityMeasure (Measure.map S μ) :=
    Measure.isProbabilityMeasure_map hSmeas.aemeasurable
  refine MeasureTheory.Measure.ext_of_charFun (funext fun t => ?_)
  rw [← complexMGF_mul_I hSmeas.aemeasurable t, ← complexMGF_id_mul_I t]
  refine eqOn_complexMGF_of_mgf hA ?_
  rw [Set.mem_setOf_eq, show ((t : ℂ) * Complex.I).re = 0 from by simp]
  exact hB

end StatLean.MultipleTesting
