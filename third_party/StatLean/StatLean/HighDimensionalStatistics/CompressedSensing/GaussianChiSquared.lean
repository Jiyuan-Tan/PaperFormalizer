module
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.ConcentrationInequalities.SubExponential.Defs
public import StatLean.ConcentrationInequalities.SubExponential.SampleMean
public import StatLean.HighDimensionalStatistics.LinearModel.Defs
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# χ²₁ sub-exponentiality and the fixed-`β` Gaussian quadratic-form tail

The probabilistic core of the random-RIP theorem. Two results, stated in standard
mathematical notation:

* **Centered χ²₁ is sub-exponential.** If $g \sim N(0,1)$, then the centered square
  $g^2 - 1$ is sub-exponential with parameter $\alpha = 4$: its centered moment generating
  function satisfies $\mathbb{E}\,e^{t(g^2-1)} \le e^{t^2\alpha^2/2}$ for $|t| \le 1/\alpha$.
  (`chiSq1_centered_isSubExponential`.)

* **Fixed-vector quadratic-form tail.** Let $X \in \mathbb{R}^{n\times d}$ have i.i.d.
  $N(0, 1/n)$ entries and fix a nonzero vector $\beta \in \mathbb{R}^d$. Then the normalised
  quadratic form $\|X\beta\|^2/\|\beta\|^2$ concentrates around $1$:
  $$\mathbb{P}\!\left(\left|\frac{\|X\beta\|^2}{\|\beta\|^2} - 1\right| > \delta\right)
      \le 2\,e^{-n\delta^2/32}, \qquad 0 < \delta \le 1.$$
  (`gaussian_quadratic_form_tail`.) This is exactly the fixed-$\beta$ step of the $3s$-RIP
  construction theorem, where the ratio is recognised as a normalised $\chi^2_n$ variable:
  $\|X\beta\|^2/\|\beta\|^2 = \tfrac1n\sum_{i=1}^n g_i^2$ with $g_i \sim N(0,1)$ i.i.d.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 9 (Restricted Isometry Property),
§9.1 (Restricted Isometry Property), Theorem 9.2 and its fixed-$\beta$ tail Eq. (9.1).
The book states the fixed-$\beta$ bound as $\mathbb{P}(|\,\|X\beta\|^2/\|\beta\|^2 - 1| >
\delta) \le 2\,e^{-n\delta^2/8}$.

**Proof formalization notes.**

* `chiSq1_centered_isSubExponential`: via the closed-form χ²₁ MGF
  $\mathbb{E}\,e^{l g^2} = (1-2l)^{-1/2}$ for $l < 1/2$ (from the Gaussian integral
  $\int e^{l x^2}\,dN(0,1) = (1-2l)^{-1/2}$, `integral_gaussian`), giving the centered MGF
  $e^{-l}(1-2l)^{-1/2}$, which is bounded by $e^{8 l^2}$ on $|l| \le 1/4$ (`exp_chiSq_mgf_bound`).
* `gaussian_quadratic_form_tail`: write $\|X\beta\|^2/\|\beta\|^2 = \tfrac1n\sum_i g_i^2$
  where each row contributes $g_i \sim N(0,1)$ i.i.d. — the rows are Gaussian by the
  sum-of-independent-Gaussians lemma (`map_sum_gaussianReal`) plus a block-independence
  argument over the matrix index $(i,j)$ (`iIndepFun_rows`). Then apply
  `chiSq1_centered_isSubExponential` to $g_i^2 - 1$ and the sub-exponential sample-mean tail
  (`measure_sampleMean_lt_le_quadratic`), once for $\sum (g_i^2 - 1)$ and once for its
  negation, and union the two one-sided events.

* **Deviation from book (constant).** The book exponent $n\delta^2/8$ corresponds to the
  sharp sub-exponential parameter $\alpha = 2$ for $g^2 - 1$. The constant we actually
  *prove* for the χ²₁ MGF bound is $\alpha = 4$ (the bound $e^{-l}(1-2l)^{-1/2} \le e^{8 l^2}$
  on $|l| \le 1/4$), so the sample-mean tail yields $2\,e^{-n\delta^2/(2\alpha^2)} =
  2\,e^{-n\delta^2/32}$. We therefore state the **provable** exponent $n\delta^2/32$ in
  `gaussian_quadratic_form_tail`. Downstream consumers (`RandomRIP.lean`) must use $32$.

**Bibliographic comments.** The χ²₁ moment generating function $(1-2t)^{-1/2}$ and the
resulting sub-exponential / Bernstein-type tail for chi-square variables are classical
folklore with no single seminal origin; the book itself attributes the fixed-$\beta$ bound
to a standard $\chi^2_n$ concentration exercise. The use of this fixed-vector concentration
inequality as the central lemma in a self-contained proof of the Restricted Isometry
Property for Gaussian (and more general sub-Gaussian) random matrices is due to
R. Baraniuk, M. Davenport, R. DeVore, and M. Wakin, "A Simple Proof of the Restricted
Isometry Property for Random Matrices," *Constructive Approximation* 28(3):253–263, 2008
(their Lemma 5.1 / concentration inequality $\mathbb{P}(|\,\|\Phi x\|^2 - \|x\|^2\,| \ge
\epsilon\|x\|^2) \le 2 e^{-M c_0(\epsilon)}$), building on the Johnson–Lindenstrauss
concentration tradition and the random-matrix RIP analysis of E. Candès and T. Tao,
"Decoding by Linear Programming," *IEEE Trans. Inform. Theory* 51(12):4203–4215, 2005.

Concept-layer for the compressed-sensing sub-area; consumed by `RandomRIP.lean`.
-/

open MeasureTheory ProbabilityTheory Matrix Real
open scoped ENNReal NNReal
open StatLean.ConcentrationInequalities

namespace StatLean.HighDimensionalStatistics

/-! ## Gaussian-square moment generating function bricks -/

/-- Pointwise identity collapsing the standard-Gaussian density times `exp(l x²)` into a
single Gaussian kernel `(√(2π))⁻¹ · exp(−(1/2 − l) x²)`. -/
private lemma gaussianPDF_mul_exp_sq (l x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (l * x ^ 2)
      = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
  have hpdf : gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [hpdf, mul_assoc, ← Real.exp_add,
    show -x ^ 2 / 2 + l * x ^ 2 = -(1 / 2 - l) * x ^ 2 from by ring]

/-- **Closed-form χ²₁-type integral**: for `l < 1/2`,
`∫ exp(l x²) dN(0,1)(x) = (1 − 2l)^{-1/2}`. -/
private lemma integral_exp_mul_sq_stdGaussian {l : ℝ} (hl : l < 1 / 2) :
    ∫ x, Real.exp (l * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * l))⁻¹ := by
  have hb : (0 : ℝ) < 1 / 2 - l := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (l * x ^ 2)
      = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
    intro x; rw [smul_eq_mul]; exact gaussianPDF_mul_exp_sq l x
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian (1 / 2 - l)]
  -- (√(2π))⁻¹ · √(π/(1/2 − l)) = (√(1 − 2l))⁻¹
  have hπ : (0 : ℝ) ≤ (2 * π)⁻¹ := by positivity
  rw [← Real.sqrt_inv, ← Real.sqrt_mul hπ,
    show (2 * π)⁻¹ * (π / (1 / 2 - l)) = (1 - 2 * l)⁻¹ from by
      have hpine : π ≠ 0 := Real.pi_ne_zero
      have hbne : (1 / 2 - l) ≠ 0 := hb.ne'
      field_simp,
    Real.sqrt_inv]

/-- Integrability of `x ↦ exp(l x²)` under the standard Gaussian for `l < 1/2`. -/
private lemma integrable_exp_mul_sq_stdGaussian {l : ℝ} (hl : l < 1 / 2) :
    Integrable (fun x => Real.exp (l * x ^ 2)) (gaussianReal 0 1) := by
  have hb : (0 : ℝ) < 1 / 2 - l := by linarith
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]
  have hpt : (fun x => gaussianPDFReal 0 1 x * Real.exp (l * x ^ 2))
      = fun x => (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
    funext x; exact gaussianPDF_mul_exp_sq l x
  rw [hpt]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

/-- **Analytic χ²₁ MGF bound**: `e^{−l} (1 − 2l)^{-1/2} ≤ e^{8l²}` for `|l| ≤ 1/4`. -/
private lemma exp_chiSq_mgf_bound {l : ℝ} (hl : |l| ≤ 1 / 4) :
    Real.exp (-l) * (Real.sqrt (1 - 2 * l))⁻¹ ≤ Real.exp (8 * l ^ 2) := by
  have hlu : l ≤ 1 / 4 := (le_abs_self l).trans hl
  have hll : -(1 / 4) ≤ l := (abs_le.mp hl).1
  have hb : (0 : ℝ) < 1 - 2 * l := by linarith
  -- core inequality: exp(−2l − 16l²) ≤ 1 − 2l
  have hcore : Real.exp (-2 * l - 16 * l ^ 2) ≤ 1 - 2 * l := by
    have hpos : (0 : ℝ) < 1 + 2 * l + 16 * l ^ 2 := by nlinarith [sq_nonneg (4 * l + 1 / 4)]
    have h1 : 1 + 2 * l + 16 * l ^ 2 ≤ Real.exp (2 * l + 16 * l ^ 2) := by
      have := Real.add_one_le_exp (2 * l + 16 * l ^ 2); linarith
    calc Real.exp (-2 * l - 16 * l ^ 2)
        = (Real.exp (2 * l + 16 * l ^ 2))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
      _ ≤ (1 + 2 * l + 16 * l ^ 2)⁻¹ := inv_anti₀ hpos h1
      _ ≤ 1 - 2 * l := by
            rw [inv_eq_one_div, div_le_iff₀ hpos]
            nlinarith [mul_nonneg (sq_nonneg l) (show (0 : ℝ) ≤ 3 - 8 * l from by linarith)]
  -- from the core inequality: exp(−l − 8l²) ≤ √(1 − 2l)
  have hsqrt : Real.exp (-l - 8 * l ^ 2) ≤ Real.sqrt (1 - 2 * l) := by
    have he : Real.sqrt (Real.exp (-2 * l - 16 * l ^ 2)) = Real.exp (-l - 8 * l ^ 2) := by
      rw [← Real.exp_half]; congr 1; ring
    calc Real.exp (-l - 8 * l ^ 2) = Real.sqrt (Real.exp (-2 * l - 16 * l ^ 2)) := he.symm
      _ ≤ Real.sqrt (1 - 2 * l) := Real.sqrt_le_sqrt hcore
  -- assemble
  have hfin : Real.exp (-l) ≤ Real.exp (8 * l ^ 2) * Real.sqrt (1 - 2 * l) := by
    calc Real.exp (-l) = Real.exp (8 * l ^ 2) * Real.exp (-l - 8 * l ^ 2) := by
            rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (8 * l ^ 2) * Real.sqrt (1 - 2 * l) :=
            mul_le_mul_of_nonneg_left hsqrt (Real.exp_pos _).le
  rw [← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.mpr hb)]
  exact hfin

/-! ## Mean of `g² − 1` and the χ²₁ sub-exponential theorem -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- For `g ∼ N(0,1)`, `E[g² − 1] = 0`. -/
private lemma integral_sq_sub_one_eq_zero {μ : Measure Ω} [IsProbabilityMeasure μ]
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Measure.map g μ = gaussianReal 0 1) :
    ∫ x, (g x ^ 2 - 1) ∂μ = 0 := by
  have hInt2 : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
    have := (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) 2).integrable_sq
    simpa using this
  have hEsq : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
    rw [variance_eq_integral (by fun_prop)] at hv
    simpa using hv
  calc ∫ x, (g x ^ 2 - 1) ∂μ
      = ∫ y, (y ^ 2 - 1) ∂(Measure.map g μ) := by
        rw [integral_map hg_meas.aemeasurable (by fun_prop)]
    _ = ∫ y, (y ^ 2 - 1) ∂(gaussianReal 0 1) := by rw [hg]
    _ = (∫ y, y ^ 2 ∂(gaussianReal 0 1)) - ∫ _y, (1 : ℝ) ∂(gaussianReal 0 1) := by
        rw [integral_sub hInt2 (integrable_const 1)]
    _ = 0 := by rw [hEsq, integral_const]; simp

/-- **Centered χ²₁ is sub-exponential** (Lu §9.1, used for the fixed-`β` tail Eq. (9.1)).
For `g ∼ N(0,1)`, `g² − 1` is sub-exponential with parameter `α = 4`. -/
theorem chiSq1_centered_isSubExponential
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Ω → ℝ)
    -- USER-INPUT: g is measurable; Lu-BDA §9.1, Theorem 9.2
    (hg_meas : Measurable g)
    -- USER-INPUT: g ∼ N(0,1); Lu-BDA §9.1, Theorem 9.2
    (hg : Measure.map g μ = gaussianReal 0 1) :
    IsSubExponential (fun ω => g ω ^ 2 - 1) 4 μ := by
  have hmean := integral_sq_sub_one_eq_zero hg_meas hg
  -- MGF closed form for `l < 1/2`
  have hmgf : ∀ {l : ℝ}, l < 1 / 2 →
      mgf (fun ω => g ω ^ 2 - 1) μ l = Real.exp (-l) * (Real.sqrt (1 - 2 * l))⁻¹ := by
    intro l hl2
    simp only [mgf]
    have hpt : ∀ ω, Real.exp (l * (g ω ^ 2 - 1))
        = Real.exp (-l) * Real.exp (l * g ω ^ 2) := by
      intro ω; rw [← Real.exp_add]; congr 1; ring
    simp_rw [hpt]
    rw [integral_const_mul]
    congr 1
    have hmap : ∫ ω, Real.exp (l * g ω ^ 2) ∂μ
        = ∫ y, Real.exp (l * y ^ 2) ∂(Measure.map g μ) := by
      rw [integral_map hg_meas.aemeasurable (by fun_prop)]
    rw [hmap, hg, integral_exp_mul_sq_stdGaussian hl2]
  constructor
  · -- mgf_le field
    intro l hl
    have hl2 : l < 1 / 2 := lt_of_le_of_lt ((le_abs_self l).trans hl) (by norm_num)
    have hcenter : (fun ω => g ω ^ 2 - 1 - ∫ x, (g x ^ 2 - 1) ∂μ) = fun ω => g ω ^ 2 - 1 := by
      rw [hmean]; funext ω; ring
    rw [hcenter, hmgf hl2,
      show l ^ 2 * ((4 : ℝ≥0) : ℝ) ^ 2 / 2 = 8 * l ^ 2 from by push_cast; ring]
    exact exp_chiSq_mgf_bound hl
  · -- integrable_exp_mul field
    intro l hl
    have hl2 : l < 1 / 2 := lt_of_le_of_lt ((le_abs_self l).trans hl) (by norm_num)
    have hcenter : (fun ω => Real.exp (l * (g ω ^ 2 - 1 - ∫ x, (g x ^ 2 - 1) ∂μ)))
        = fun ω => Real.exp (-l) * Real.exp (l * g ω ^ 2) := by
      rw [hmean]; funext ω; rw [← Real.exp_add]; congr 1; ring
    rw [hcenter]
    apply Integrable.const_mul
    have hφ : Integrable (fun y => Real.exp (l * y ^ 2)) (Measure.map g μ) := by
      rw [hg]; exact integrable_exp_mul_sq_stdGaussian hl2
    exact (integrable_map_measure hφ.aestronglyMeasurable hg_meas.aemeasurable).mp hφ

/-! ## Negation of a sub-exponential variable -/

/-- If `Z` is sub-exponential with parameter `α`, so is `−Z`. -/
private lemma isSubExponential_neg {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {α : ℝ≥0} (h : IsSubExponential Z α μ) :
    IsSubExponential (fun ω => -Z ω) α μ := by
  have hmean : ∫ x, (-Z x) ∂μ = -∫ x, Z x ∂μ := integral_neg _
  constructor
  · intro l hl
    have hcc : (fun ω => -Z ω - ∫ x, (-Z x) ∂μ) = -(fun ω => Z ω - ∫ x, Z x ∂μ) := by
      funext ω; rw [hmean]; simp only [Pi.neg_apply]; ring
    rw [hcc, mgf_neg]
    have hbound := h.mgf_le (-l) (by rwa [abs_neg])
    rwa [show (-l) ^ 2 * (α : ℝ) ^ 2 / 2 = l ^ 2 * (α : ℝ) ^ 2 / 2 from by ring] at hbound
  · intro l hl
    have hint := h.integrable_exp_mul (-l) (by rwa [abs_neg])
    have hcc : (fun ω => Real.exp (l * (-Z ω - ∫ x, (-Z x) ∂μ)))
        = fun ω => Real.exp (-l * (Z ω - ∫ x, Z x ∂μ)) := by
      funext ω; rw [hmean]; congr 1; ring
    rw [hcc]; exact hint

/-! ## Sum of independent real Gaussians -/

/-- The pushforward of a finite sum of **independent** real Gaussians is again Gaussian:
`map (∑ᵢ Yᵢ) μ = N(∑ mᵢ, ∑ vᵢ)`. -/
private lemma map_sum_gaussianReal {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} {Y : ι → Ω → ℝ} {m : ι → ℝ} {v : ι → ℝ≥0}
    (hmeas : ∀ i, Measurable (Y i)) (hindep : iIndepFun Y μ)
    (hlaw : ∀ i, Measure.map (Y i) μ = gaussianReal (m i) (v i)) (s : Finset ι) :
    Measure.map (fun ω => ∑ i ∈ s, Y i ω) μ
      = gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    simp [Measure.map_const, measure_univ, gaussianReal_zero_var]
  | insert a s ha ih =>
    have hindepF : IndepFun (Y a) (∑ i ∈ s, Y i) μ :=
      (hindep.indepFun_finset_sum_of_notMem hmeas ha).symm
    have ih' : Measure.map (∑ i ∈ s, Y i) μ
        = gaussianReal (∑ i ∈ s, m i) (∑ i ∈ s, v i) := by
      rw [show (∑ i ∈ s, Y i) = (fun ω => ∑ i ∈ s, Y i ω) from
        funext fun ω => Finset.sum_apply ω s Y]
      exact ih
    have key := gaussianReal_add_gaussianReal_of_indepFun hindepF (hlaw a) ih'
    simp only [Finset.sum_insert ha]
    rw [show (fun ω => Y a ω + ∑ i ∈ s, Y i ω) = (Y a + ∑ i ∈ s, Y i) from
      funext fun ω => by rw [Pi.add_apply, Finset.sum_apply]]
    exact key

/-! ## Grouping independence over a product index -/

section Curry

variable {α β γ : Type*} [Fintype α] [Fintype β] [MeasurableSpace γ]

/-- Uncurrying the product of products of probability measures over the index `α × β`
recovers the product measure over `α × β`. -/
private lemma map_uncurry_pi_pi (ν : α → β → Measure γ) [∀ a b, IsProbabilityMeasure (ν a b)] :
    (Measure.pi (fun a => Measure.pi (fun b => ν a b))).map
        (fun (g : α → β → γ) (p : α × β) => g p.1 p.2)
      = Measure.pi (fun p : α × β => ν p.1 p.2) := by
  classical
  have hmu : Measurable (fun (g : α → β → γ) (p : α × β) => g p.1 p.2) := by
    apply measurable_pi_lambda; intro p
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hmu (MeasurableSet.univ_pi hs)]
  have hpre : (fun (g : α → β → γ) (p : α × β) => g p.1 p.2) ⁻¹' (Set.univ.pi s)
      = Set.univ.pi (fun a => Set.univ.pi (fun b => s (a, b))) := by
    ext g
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h a b; exact h (a, b)
    · intro h p; exact h p.1 p.2
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_prod_type' (fun a b => ν a b (s (a, b)))]

/-- Currying direction of `map_uncurry_pi_pi`. -/
private lemma map_curry_pi_pi (ν : α → β → Measure γ) [∀ a b, IsProbabilityMeasure (ν a b)] :
    (Measure.pi (fun p : α × β => ν p.1 p.2)).map (fun (h : α × β → γ) a b => h (a, b))
      = Measure.pi (fun a => Measure.pi (fun b => ν a b)) := by
  classical
  have hmu : Measurable (fun (g : α → β → γ) (p : α × β) => g p.1 p.2) := by
    apply measurable_pi_lambda; intro p
    exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hmc : Measurable (fun (h : α × β → γ) (a : α) (b : β) => h (a, b)) := by
    apply measurable_pi_lambda; intro a; apply measurable_pi_lambda; intro b
    exact measurable_pi_apply (a, b)
  rw [← map_uncurry_pi_pi ν, Measure.map_map hmc hmu,
    show ((fun (h : α × β → γ) a b => h (a, b)) ∘ (fun (g : α → β → γ) (p : α × β) => g p.1 p.2))
        = id from funext fun g => rfl,
    Measure.map_id]

set_option linter.unusedFintypeInType false in
/-- **Block independence**: if the family `(Yₐᵦ)` indexed by pairs `(a,b)` is independent,
then the "row" family `a ↦ (b ↦ Yₐᵦ)` (valued in `β → γ`) is independent.

The `Fintype α`/`Fintype β` instances are required for `Measure.pi` in the proof even
though they do not appear in the statement. -/
private lemma iIndepFun_rows {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : α → β → Ω → γ) (hY : ∀ a b, AEMeasurable (Y a b) μ)
    (hindep : iIndepFun (fun (p : α × β) ω => Y p.1 p.2 ω) μ) :
    iIndepFun (fun (a : α) ω => (fun b => Y a b ω)) μ := by
  classical
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun a => aemeasurable_pi_lambda _ (fun b => hY a b))]
  -- per-row independence
  have hrow : ∀ a, μ.map (fun ω => fun b => Y a b ω)
      = Measure.pi (fun b => μ.map (Y a b)) := by
    intro a
    have hsub : iIndepFun (fun b ω => Y a b ω) μ := by
      have := hindep.precomp (g := fun b : β => (a, b))
        (fun x y h => by simpa using h)
      simpa using this
    rw [← iIndepFun_iff_map_fun_eq_pi_map (fun b => hY a b)]
    exact hsub
  -- entries independence as a product
  have hent : μ.map (fun ω => fun p : α × β => Y p.1 p.2 ω)
      = Measure.pi (fun p : α × β => μ.map (Y p.1 p.2)) := by
    rw [← iIndepFun_iff_map_fun_eq_pi_map (fun p : α × β => hY p.1 p.2)]
    exact hindep
  have hentAE : AEMeasurable (fun ω => fun p : α × β => Y p.1 p.2 ω) μ :=
    aemeasurable_pi_lambda _ (fun p : α × β => hY p.1 p.2)
  have hmc : Measurable (fun (h : α × β → γ) (a : α) (b : β) => h (a, b)) := by
    apply measurable_pi_lambda; intro a; apply measurable_pi_lambda; intro b
    exact measurable_pi_apply (a, b)
  rw [show (fun ω => fun a b => Y a b ω)
        = (fun (h : α × β → γ) a b => h (a, b)) ∘ (fun ω => fun p : α × β => Y p.1 p.2 ω)
      from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hmc.aemeasurable hentAE, hent,
    show (Measure.pi (fun a => μ.map (fun ω => fun b => Y a b ω)))
        = Measure.pi (fun a => Measure.pi (fun b => μ.map (Y a b)))
      from by congr 1; funext a; exact hrow a]
  haveI : ∀ a b, IsProbabilityMeasure (μ.map (Y a b)) :=
    fun a b => Measure.isProbabilityMeasure_map (hY a b)
  exact map_curry_pi_pi (fun a b => μ.map (Y a b))

end Curry

/-! ## The fixed-`β` quadratic-form tail -/

variable {n d : ℕ}

/-- **Fixed-`β` quadratic-form tail** (Lu §9.1, Eq. (9.1)). If `X` has i.i.d. `N(0,1/n)`
entries then for any fixed `β ≠ 0`,
`P(|‖Xβ‖²/‖β‖² − 1| > δ) ≤ 2·exp(−n δ²/32)`.

**Constant deviation from the book** (which states `8`): the provable χ²₁ sub-exponential
parameter is `α = 4`, giving the sample-mean exponent `2α² = 32`. See the module docstring. -/
theorem gaussian_quadratic_form_tail
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    -- USER-INPUT: the entries Xᵢⱼ are jointly independent; Lu-BDA §9.1, Theorem 9.2
    (hindep : iIndepFun (fun (p : Fin n × Fin d) ω => X ω p.1 p.2) μ)
    -- USER-INPUT: each entry Xᵢⱼ ∼ N(0,1/n); Lu-BDA §9.1, Theorem 9.2
    (hlaw : ∀ i j, Measure.map (fun ω => X ω i j) μ
              = gaussianReal 0 (⟨1 / (n : ℝ), div_nonneg zero_le_one (Nat.cast_nonneg n)⟩ : ℝ≥0))
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | δ < |‖designMap (X ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 32)) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- n = 0 : the bound is ≥ 1 ≥ μ(any set)
    subst hn0
    have h2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 2 := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from by simp]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    calc μ {ω | δ < |‖designMap (X ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|}
        ≤ 1 := prob_le_one
      _ ≤ ENNReal.ofReal 2 := h2
      _ = ENNReal.ofReal (2 * Real.exp (-((0 : ℕ) : ℝ) * δ ^ 2 / 32)) := by
          congr 1
          rw [show (-((0 : ℕ) : ℝ) * δ ^ 2 / 32) = 0 from by push_cast; ring,
            Real.exp_zero, mul_one]
  · -- n > 0
    set vn : ℝ≥0 := ⟨1 / (n : ℝ), div_nonneg zero_le_one (Nat.cast_nonneg n)⟩ with hvn
    have hβ' : ‖β‖ ≠ 0 := norm_ne_zero_iff.mpr hβ
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    -- aemeasurable entries, then a measurable representative
    have hXae : ∀ i j, AEMeasurable (fun ω => X ω i j) μ := by
      intro i j
      apply AEMeasurable.of_map_ne_zero
      rw [hlaw i j]; exact IsProbabilityMeasure.ne_zero _
    set X' : Ω → Matrix (Fin n) (Fin d) ℝ :=
      fun ω => Matrix.of (fun i j => (hXae i j).mk (fun ω' => X ω' i j) ω) with hX'def
    have hX'meas : ∀ i j, Measurable (fun ω => X' ω i j) :=
      fun i j => (hXae i j).measurable_mk
    have hXeq : ∀ i j, (fun ω => X' ω i j) =ᵐ[μ] (fun ω => X ω i j) :=
      fun i j => (hXae i j).ae_eq_mk.symm
    have hX'law : ∀ i j, Measure.map (fun ω => X' ω i j) μ = gaussianReal 0 vn := by
      intro i j; rw [Measure.map_congr (hXeq i j)]; exact hlaw i j
    have hX'indep : iIndepFun (fun (p : Fin n × Fin d) ω => X' ω p.1 p.2) μ :=
      (iIndepFun_congr (fun p : Fin n × Fin d => hXeq p.1 p.2)).mpr hindep
    -- matrices agree a.e.
    have hae_mat : ∀ᵐ ω ∂μ, X' ω = X ω := by
      have hall : ∀ᵐ ω ∂μ, ∀ i j, X' ω i j = X ω i j := by
        rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j; exact hXeq i j
      filter_upwards [hall] with ω hω; ext i j; exact hω i j
    have hevent : μ {ω | δ < |‖designMap (X ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|}
        = μ {ω | δ < |‖designMap (X' ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|} := by
      apply measure_congr
      filter_upwards [hae_mat] with ω hω
      have hdm : designMap (X' ω) β = designMap (X ω) β := by rw [hω]
      change (δ < |‖designMap (X ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|)
           = (δ < |‖designMap (X' ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|)
      rw [hdm]
    rw [hevent]
    -- coefficient vector and rescaled rows
    set c : Fin d → ℝ := fun j => (Real.sqrt (n : ℝ) / ‖β‖) * β.ofLp j with hc
    set g : Fin n → Ω → ℝ := fun i ω => ∑ j, c j * X' ω i j with hg
    have hgmeas : ∀ i, Measurable (g i) := by
      intro i; simp only [hg]
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (hX'meas i j))
    -- per-row entry independence
    have hrowindep : ∀ i, iIndepFun (fun j ω => X' ω i j) μ := by
      intro i
      have := hX'indep.precomp (g := fun j : Fin d => (i, j)) (fun x y h => by simpa using h)
      simpa using this
    -- per-entry scaled law
    have hYlaw : ∀ i j, Measure.map (fun ω => c j * X' ω i j) μ
        = gaussianReal 0 (NNReal.mk ((c j) ^ 2) (sq_nonneg _) * vn) := by
      intro i j
      rw [show (fun ω => c j * X' ω i j) = (fun x => c j * x) ∘ (fun ω => X' ω i j) from rfl,
        ← Measure.map_map (by fun_prop) (hX'meas i j), hX'law i j,
        gaussianReal_map_const_mul]
      simp
    -- the variances of one row sum to 1
    have hvar : (∑ j, (NNReal.mk ((c j) ^ 2) (sq_nonneg _) * vn : ℝ≥0)) = (1 : ℝ≥0) := by
      rw [← NNReal.coe_inj]
      push_cast [NNReal.coe_sum]
      have hsum : ∑ j, (β.ofLp j) ^ 2 = ‖β‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq β).symm
      have hterm : ∀ j, ((c j) ^ 2 : ℝ) * (vn : ℝ) = (β.ofLp j) ^ 2 / ‖β‖ ^ 2 := by
        intro j
        have hvn' : (vn : ℝ) = 1 / (n : ℝ) := rfl
        simp only [hc, hvn', mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        field_simp
      calc ∑ j, ((c j) ^ 2 : ℝ) * (vn : ℝ)
          = ∑ j, (β.ofLp j) ^ 2 / ‖β‖ ^ 2 := Finset.sum_congr rfl (fun j _ => hterm j)
        _ = (∑ j, (β.ofLp j) ^ 2) / ‖β‖ ^ 2 := by rw [Finset.sum_div]
        _ = 1 := by rw [hsum, div_self (pow_ne_zero 2 hβ')]
    -- law of g i
    have hgi_law : ∀ i, Measure.map (g i) μ = gaussianReal 0 1 := by
      intro i
      have hYmeas : ∀ j, Measurable (fun ω => c j * X' ω i j) :=
        fun j => measurable_const.mul (hX'meas i j)
      have hYindep : iIndepFun (fun j ω => c j * X' ω i j) μ := by
        have := (hrowindep i).comp (fun j => fun x : ℝ => c j * x)
          (fun j => measurable_const.mul measurable_id)
        simpa [Function.comp] using! this
      have hsum := map_sum_gaussianReal hYmeas hYindep (hYlaw i) (Finset.univ : Finset (Fin d))
      rw [show (fun ω => ∑ j ∈ (Finset.univ : Finset (Fin d)), c j * X' ω i j) = g i from rfl]
        at hsum
      rw [hsum, Finset.sum_const_zero, hvar]
    -- independence of the rescaled rows, hence of g
    have hgindep : iIndepFun g μ := by
      have hrows := iIndepFun_rows (fun i j ω => X' ω i j)
        (fun i j => (hX'meas i j).aemeasurable) hX'indep
      have := hrows.comp (fun _ => fun r : Fin d → ℝ => ∑ j, c j * r j)
        (fun _ => by fun_prop)
      simpa [Function.comp, hg] using! this
    -- the sub-exponential variables `Z i = (g i)² − 1`
    set Z : Fin n → Ω → ℝ := fun i ω => (g i ω) ^ 2 - 1 with hZ
    have hZmeas : ∀ i, Measurable (Z i) := fun i => ((hgmeas i).pow_const 2).sub_const 1
    have hZsubexp : ∀ i, IsSubExponential (Z i) 4 μ :=
      fun i => chiSq1_centered_isSubExponential μ (g i) (hgmeas i) (hgi_law i)
    have hZmean : ∀ i, ∫ ω, Z i ω ∂μ = 0 :=
      fun i => integral_sq_sub_one_eq_zero (hgmeas i) (hgi_law i)
    have hZindep : iIndepFun Z μ := by
      have := hgindep.comp (fun _ => fun x : ℝ => x ^ 2 - 1) (fun _ => by fun_prop)
      simpa [Function.comp, hZ] using! this
    -- `‖Xβ‖²/‖β‖² − 1 = (1/n) ∑ᵢ Zᵢ`
    have hQS : ∀ ω, ‖designMap (X' ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1
        = (1 / (n : ℝ)) * ∑ i, Z i ω := by
      intro ω
      have hcoord : ∀ i, (designMap (X' ω) β).ofLp i = ∑ j, X' ω i j * β.ofLp j := by
        intro i
        have hrw : (designMap (X' ω) β).ofLp = X' ω *ᵥ β.ofLp := rfl
        rw [hrw]; simp [Matrix.mulVec, dotProduct]
      have hgcoord : ∀ i, g i ω = (Real.sqrt (n : ℝ) / ‖β‖) * (designMap (X' ω) β).ofLp i := by
        intro i
        rw [hcoord i]
        simp only [hg, hc, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      have hnorm : ‖designMap (X' ω) β‖ ^ 2 / ‖β‖ ^ 2 = (1 / (n : ℝ)) * ∑ i, (g i ω) ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_div, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hap : (designMap (X' ω) β) i = (designMap (X' ω) β).ofLp i := rfl
        rw [hap, hgcoord i, mul_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        field_simp
      rw [hnorm]
      simp only [hZ]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_sub, mul_one]
      field_simp
    -- two-sided sub-exponential tail
    have hα : (0 : ℝ) < ((4 : ℝ≥0) : ℝ) := by norm_num
    have hδα : δ ≤ ((4 : ℝ≥0) : ℝ) := le_trans hδ1 (by norm_num)
    have htail1 := measure_sampleMean_lt_le_quadratic hn hZsubexp hZmean hZindep hα hZmeas
      hδ.le hδα
    -- negated variables
    have hnegZsubexp : ∀ i, IsSubExponential (fun ω => -(Z i ω)) 4 μ :=
      fun i => isSubExponential_neg (hZsubexp i)
    have hnegZmean : ∀ i, ∫ ω, -(Z i ω) ∂μ = 0 := fun i => by rw [integral_neg, hZmean i]; simp
    have hnegZindep : iIndepFun (fun i ω => -(Z i ω)) μ := by
      have := hZindep.comp (fun _ => fun x : ℝ => -x) (fun _ => measurable_neg)
      simpa [Function.comp] using! this
    have hnegZmeas : ∀ i, Measurable (fun ω => -(Z i ω)) := fun i => (hZmeas i).neg
    have htail2 := measure_sampleMean_lt_le_quadratic hn hnegZsubexp hnegZmean hnegZindep hα
      hnegZmeas hδ.le hδα
    -- normalise the exponent denominator `2·4² = 32`
    have h32 : (2 * ((4 : ℝ≥0) : ℝ) ^ 2) = 32 := by norm_num
    rw [h32] at htail1 htail2
    -- assemble
    have hgoal_set : {ω | δ < |‖designMap (X' ω) β‖ ^ 2 / ‖β‖ ^ 2 - 1|}
        = {ω | δ < |(1 / (n : ℝ)) * ∑ i, Z i ω|} := by
      ext ω; simp only [Set.mem_setOf_eq, hQS ω]
    rw [hgoal_set]
    have hsubset : {ω | δ < |(1 / (n : ℝ)) * ∑ i, Z i ω|}
        ⊆ {ω | δ < (1 / (n : ℝ)) * ∑ i, Z i ω - 0}
          ∪ {ω | δ < (1 / (n : ℝ)) * ∑ i, -(Z i ω) - 0} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, sub_zero, Set.mem_union] at hω ⊢
      rcases le_or_gt 0 ((1 / (n : ℝ)) * ∑ i, Z i ω) with hpos | hneg
      · left; rwa [abs_of_nonneg hpos] at hω
      · right
        rw [abs_of_neg hneg] at hω
        have heq : (1 / (n : ℝ)) * ∑ i, -(Z i ω) = -((1 / (n : ℝ)) * ∑ i, Z i ω) := by
          rw [Finset.sum_neg_distrib, mul_neg]
        rw [heq]; exact hω
    calc μ {ω | δ < |(1 / (n : ℝ)) * ∑ i, Z i ω|}
        ≤ μ ({ω | δ < (1 / (n : ℝ)) * ∑ i, Z i ω - 0}
              ∪ {ω | δ < (1 / (n : ℝ)) * ∑ i, -(Z i ω) - 0}) := measure_mono hsubset
      _ ≤ μ {ω | δ < (1 / (n : ℝ)) * ∑ i, Z i ω - 0}
            + μ {ω | δ < (1 / (n : ℝ)) * ∑ i, -(Z i ω) - 0} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * δ ^ 2 / 32))
            + ENNReal.ofReal (Real.exp (-(n : ℝ) * δ ^ 2 / 32)) := add_le_add htail1 htail2
      _ = ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * δ ^ 2 / 32)) := by
          rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]; congr 1; ring

end StatLean.HighDimensionalStatistics
