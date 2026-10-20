module
public import StatLean.ConcentrationInequalities.Symmetrization.Symmetrization
public import StatLean.ConcentrationInequalities.Symmetrization.Contraction
public import StatLean.ConcentrationInequalities.Symmetrization.SymmetricLaw
public import StatLean.ConcentrationInequalities.Symmetrization.GaussianVector
public import StatLean.ConcentrationInequalities.Symmetrization.GaussianMax
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Symmetrization with Gaussians (HDP Lemma 6.6.2)

For independent mean-zero random vectors $X_1, \dots, X_N$ in a Banach space
and independent standard Gaussian multipliers $g_1, \dots, g_N$,
$$ \mathbb{E}\Bigl\|\sum_i X_i\Bigr\|
   \;\le\; \sqrt{2\pi}\; \mathbb{E}\Bigl\|\sum_i g_i X_i\Bigr\|
   \qquad\text{and}\qquad
   \mathbb{E}\Bigl\|\sum_i g_i X_i\Bigr\|
   \;\le\; 2\sqrt{2\log(2N)}\; \mathbb{E}\Bigl\|\sum_i X_i\Bigr\|. $$
The Gaussian multipliers live on the product extension `μ.prod (gaussVec N)`.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, Lemma 6.6.2 (Symmetrization with
Gaussians), pp. 185–186; the unavoidability of the $\sqrt{\log N}$ factor is
Remark 6.6.3.

**Proof formalization notes.** **Constants.** Upper: we prove the *sharp*
constant $\sqrt{2\pi} = 2\sqrt{\pi/2} \approx 2.5066$, from the exact
$\mathbb{E}|g| = \sqrt{2/\pi}$ (`ForMathlib/GaussianAbsMoment`); the book's
display constant `3` is provided as the headline via `√(2π) ≤ 3`
(`2π ≤ 8 < 9` from `Real.pi_le_four`). Lower: the book's unnamed
`(c/√(log N)) E‖∑gX‖ ≤ E‖∑X‖` is committed to the explicit all-`N ≥ 1` form
with factor `2·√(2 log(2N))` (`2` from Lemma 6.3.2-lower, `√(2 log(2N))` from
`GaussianMax`; the `2N` vs `N` in the log is the documented two-sided
union-bound cost), plus the `N ≥ 2` corollary with factor `4√(log N)` — the
book's `c = 1/4` — via `log(2N) ≤ 2 log N`. **Proof route** (book
pp. 185–186). Upper: Lemma 6.3.2-upper, insert `E|g| = √(2/π)`, Jensen
pointwise (`norm_integral_le_integral_norm` + `integral_smul_const`), then
`(εᵢ|gᵢ|) =ᵈ (gᵢ)` (`SymmetricLaw`). Lower: `(εᵢgᵢ) =ᵈ (gᵢ)`, pointwise
contraction with `a := g` conditionally on `(ω, s)`, factorize with
`integral_prod_mul`, Lemma 6.3.2-lower, and `E max|gᵢ|` (`GaussianMax`).
Triple products `μ ⊗ signVec ⊗ gaussVec` are handled in iterated-integral
style (`integral_prod` twice) — no `Measure.prod` associativity plumbing.
`N = 0` in the all-`N` lower bound is a case split (both sides `0`; `Real.log`
junk makes the constant harmless). Named-sorry fallback of this work item:
`gaussian_symmetrization_lower` (the upper chain with the `√(2π)`/`3`
constants fully proven; the `N ≥ 2` corollary inherits the debt).

**Bibliographic comments.** Gaussian–Rademacher comparison is classical
Banach-space theory: the upper direction and the `√(log N)` loss trace to
unconditionality arguments in Ledoux–Talagrand, *Probability in Banach
Spaces* (1991), §4.2 (where the loss is shown necessary at `ℓ∞^N`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}

/-- Each coordinate of the sign vector is integrable (`id` is integrable
against `radLaw`, transported along the measure-preserving evaluation). -/
private lemma integrable_eval_signVec (i : Fin N) :
    Integrable (fun s => s i) (signVec N) := by
  have hid : Integrable (id : ℝ → ℝ) radLaw := by
    simp only [radLaw]
    refine integrable_add_measure.mpr ⟨?_, ?_⟩
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
    · exact (integrable_dirac (by simp)).smul_measure (by simp)
  simpa using (measurePreserving_eval_signVec N i).integrable_comp_of_integrable hid

/-- The `E`-valued family `p ↦ ‖∑ᵢ p.2ᵢ • Xᵢ(p.1)‖` is integrable on
`μ.prod ρ` whenever each coordinate of `ρ` and each `Xᵢ` is integrable. -/
private lemma integrable_normX (μ : Measure Ω) [IsProbabilityMeasure μ]
    {ρ : Measure (Fin N → ℝ)} [IsProbabilityMeasure ρ] {X : Fin N → Ω → E}
    (hcoef : ∀ i, Integrable (fun v => v i) ρ)
    (hX_int : ∀ i, Integrable (X i) μ) :
    Integrable (fun p : Ω × (Fin N → ℝ) => ‖∑ i, p.2 i • X i p.1‖) (μ.prod ρ) := by
  have hsum : Integrable (fun p : Ω × (Fin N → ℝ) => ∑ i, p.2 i • X i p.1) (μ.prod ρ) := by
    refine integrable_finset_sum _ (fun i _ => ?_)
    exact (hX_int i).op_fst_snd (op := fun (a : E) (r : ℝ) => r • a)
      (continuous_snd.smul continuous_fst)
      ⟨1, fun a r => le_of_eq (by show ‖r • a‖ = 1 * ‖a‖ * ‖r‖; rw [norm_smul]; ring)⟩
      (hcoef i)
  exact hsum.norm

/-- Pointwise Jensen step (book p. 185): for fixed vectors `vᵢ` and a fixed
sign pattern `s`, `‖∑ sᵢ vᵢ‖ ≤ √(π/2) · E‖∑ (sᵢ|gᵢ|) vᵢ‖`, since
`E|gᵢ| = √(2/π)` and `√(π/2)·√(2/π) = 1`. -/
private lemma jensen_pointwise (v : Fin N → E) (s : Fin N → ℝ) :
    ‖∑ i, s i • v i‖
      ≤ Real.sqrt (Real.pi / 2) * ∫ g, ‖∑ i, (s i * |g i|) • v i‖ ∂(gaussVec N) := by
  have hdnn : (0 : ℝ) ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hcnn : (0 : ℝ) ≤ Real.sqrt (Real.pi / 2) := Real.sqrt_nonneg _
  have hint : ∀ i, Integrable (fun g => (s i * |g i|) • v i) (gaussVec N) := fun i =>
    (((integrable_eval_gaussVec N i).abs).const_mul (s i)).smul_const (v i)
  -- ∫ g, ∑ᵢ (sᵢ|gᵢ|)•vᵢ  =  √(2/π) • ∑ᵢ sᵢ•vᵢ
  have hA : ∫ g, (∑ i, (s i * |g i|) • v i) ∂(gaussVec N)
      = Real.sqrt (2 / Real.pi) • (∑ i, s i • v i) := by
    rw [integral_finset_sum _ (fun i _ => hint i)]
    have hterm : ∀ i, ∫ g, (s i * |g i|) • v i ∂(gaussVec N)
        = (s i * Real.sqrt (2 / Real.pi)) • v i := by
      intro i
      rw [integral_smul_const, integral_const_mul, integral_abs_eval_gaussVec]
    simp_rw [hterm]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [mul_comm (s i), mul_smul])
  -- Jensen: √(2/π) · ‖∑ sᵢ vᵢ‖ ≤ ∫ ‖∑ (sᵢ|gᵢ|) vᵢ‖
  have hnorm : Real.sqrt (2 / Real.pi) * ‖∑ i, s i • v i‖
      ≤ ∫ g, ‖∑ i, (s i * |g i|) • v i‖ ∂(gaussVec N) := by
    calc Real.sqrt (2 / Real.pi) * ‖∑ i, s i • v i‖
        = ‖Real.sqrt (2 / Real.pi) • (∑ i, s i • v i)‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hdnn]
      _ = ‖∫ g, (∑ i, (s i * |g i|) • v i) ∂(gaussVec N)‖ := by rw [hA]
      _ ≤ ∫ g, ‖∑ i, (s i * |g i|) • v i‖ ∂(gaussVec N) := norm_integral_le_integral_norm _
  -- √(π/2)·√(2/π) = 1
  have hcd : Real.sqrt (Real.pi / 2) * Real.sqrt (2 / Real.pi) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show Real.pi / 2 * (2 / Real.pi) = 1 by
          rw [div_mul_div_comm, mul_comm (Real.pi) 2]
          exact div_self (by positivity : (0 : ℝ) < 2 * Real.pi).ne']
    exact Real.sqrt_one
  calc ‖∑ i, s i • v i‖
      = Real.sqrt (Real.pi / 2) * (Real.sqrt (2 / Real.pi) * ‖∑ i, s i • v i‖) := by
          rw [← mul_assoc, hcd, one_mul]
    _ ≤ Real.sqrt (Real.pi / 2) * ∫ g, ‖∑ i, (s i * |g i|) • v i‖ ∂(gaussVec N) :=
          mul_le_mul_of_nonneg_left hnorm hcnn

/-- The joint `(s, g)`-family `‖∑ᵢ (sᵢ|gᵢ|) xᵢ‖` is integrable on
`signVec ⊗ gaussVec`. -/
private lemma integrable_abs_prod (x : Fin N → E) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ‖∑ i, (p.1 i * |p.2 i|) • x i‖)
      ((signVec N).prod (gaussVec N)) := by
  have hsum : Integrable
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => ∑ i, (p.1 i * |p.2 i|) • x i)
      ((signVec N).prod (gaussVec N)) := by
    refine integrable_finset_sum _ (fun i _ => ?_)
    exact ((integrable_eval_signVec i).mul_prod
      ((integrable_eval_gaussVec N i).abs)).smul_const (x i)
  exact hsum.norm

/-- Change of variables `(εᵢ|gᵢ|)ᵢ =ᵈ (gᵢ)ᵢ` (book p. 186): the Gaussian
average of `‖∑ᵢ hᵢ xᵢ‖` equals the `signVec ⊗ gaussVec` average of
`‖∑ᵢ (sᵢ|gᵢ|) xᵢ‖`. -/
private lemma cov_gaussVec (x : Fin N → E) :
    ∫ h, ‖∑ i, h i • x i‖ ∂(gaussVec N)
      = ∫ p, ‖∑ i, (p.1 i * |p.2 i|) • x i‖ ∂((signVec N).prod (gaussVec N)) := by
  have hmap : ((signVec N).prod (gaussVec N)).map (fun p i => p.1 i * |p.2 i|) = gaussVec N := by
    simp only [gaussVec]
    exact map_signVec_mul_abs_pi (fun _ => isSymmetricLaw_gaussianReal 1)
  have hΦmeas : AEMeasurable
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => fun i => p.1 i * |p.2 i|)
      ((signVec N).prod (gaussVec N)) := by
    refine Measurable.aemeasurable ?_
    refine measurable_pi_lambda _ (fun i => ?_)
    exact ((measurable_pi_apply i).comp measurable_fst).mul
      (((measurable_pi_apply i).comp measurable_snd).abs)
  have hψ : AEStronglyMeasurable (fun h : Fin N → ℝ => ‖∑ i, h i • x i‖)
      (((signVec N).prod (gaussVec N)).map (fun p i => p.1 i * |p.2 i|)) := by
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_norm.comp (continuous_finset_sum _ (fun i _ =>
      (continuous_apply i).smul continuous_const))
  have himeq := integral_map hΦmeas hψ
  rw [hmap] at himeq
  exact himeq

/-- Upper inner inequality (per outcome): `E‖∑ᵢ sᵢ xᵢ‖ ≤ √(π/2) · E‖∑ᵢ gᵢ xᵢ‖`
for fixed vectors `xᵢ` — Jensen, then the sign-mixing change of variables. -/
private lemma upper_inner (x : Fin N → E) :
    ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N)
      ≤ Real.sqrt (Real.pi / 2) * ∫ h, ‖∑ i, h i • x i‖ ∂(gaussVec N) := by
  have hFp := integrable_abs_prod x
  calc ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N)
      ≤ ∫ s, Real.sqrt (Real.pi / 2)
            * (∫ g, ‖∑ i, (s i * |g i|) • x i‖ ∂(gaussVec N)) ∂(signVec N) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun s => norm_nonneg _))
          ((hFp.integral_prod_left).const_mul _)
          (Filter.Eventually.of_forall (fun s => jensen_pointwise x s))
    _ = Real.sqrt (Real.pi / 2)
          * ∫ s, (∫ g, ‖∑ i, (s i * |g i|) • x i‖ ∂(gaussVec N)) ∂(signVec N) :=
        integral_const_mul _ _
    _ = Real.sqrt (Real.pi / 2)
          * ∫ p, ‖∑ i, (p.1 i * |p.2 i|) • x i‖ ∂((signVec N).prod (gaussVec N)) := by
        rw [integral_prod _ hFp]
    _ = Real.sqrt (Real.pi / 2) * ∫ h, ‖∑ i, h i • x i‖ ∂(gaussVec N) := by
        rw [← cov_gaussVec x]

/-- The Pi sup-norm is invariant under coordinatewise absolute value. -/
private lemma norm_abs_pi [NeZero N] (g : Fin N → ℝ) : ‖(fun i => |g i|)‖ = ‖g‖ := by
  haveI : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
  rw [pi_norm_eq_ciSup_abs, pi_norm_eq_ciSup_abs]
  simp [abs_abs]

/-- The sup-norm of the Gaussian vector is integrable. -/
private lemma integrable_norm_gaussVec :
    Integrable (fun g : Fin N → ℝ => ‖g‖) (gaussVec N) := by
  have hsum : Integrable (fun g : Fin N → ℝ => ∑ i, |g i|) (gaussVec N) :=
    integrable_finset_sum _ (fun i _ => (integrable_eval_gaussVec N i).abs)
  refine hsum.mono' continuous_norm.aestronglyMeasurable (Filter.Eventually.of_forall (fun g => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |g j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- Lower inner inequality (per outcome): `E‖∑ᵢ gᵢ xᵢ‖ ≤ √(2 log 2N) · E‖∑ᵢ sᵢ xᵢ‖`
for fixed `xᵢ` — sign-mixing change of variables, the contraction principle at
coefficients `|gᵢ|`, then `E‖g‖_∞ ≤ √(2 log 2N)`. -/
private lemma lower_inner [NeZero N] (x : Fin N → E) :
    ∫ g, ‖∑ i, g i • x i‖ ∂(gaussVec N)
      ≤ Real.sqrt (2 * Real.log (2 * N)) * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) := by
  have hFp := integrable_abs_prod x
  have hKnn : 0 ≤ ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) :=
    integral_nonneg (fun s => norm_nonneg _)
  have hstep : ∀ g' : Fin N → ℝ,
      ∫ s, ‖∑ i, (s i * |g' i|) • x i‖ ∂(signVec N)
        ≤ ‖g'‖ * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) := by
    intro g'
    calc ∫ s, ‖∑ i, (s i * |g' i|) • x i‖ ∂(signVec N)
        = ∫ s, ‖∑ i, (|g' i| * s i) • x i‖ ∂(signVec N) := by simp_rw [mul_comm]
      _ ≤ ‖(fun i => |g' i|)‖ * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) :=
            contraction_principle x (fun i => |g' i|)
      _ = ‖g'‖ * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) := by rw [norm_abs_pi]
  rw [cov_gaussVec x, integral_prod_symm _ hFp]
  calc ∫ g', ∫ s, ‖∑ i, (s i * |g' i|) • x i‖ ∂(signVec N) ∂(gaussVec N)
      ≤ ∫ g', ‖g'‖ * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) ∂(gaussVec N) := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun g' => integral_nonneg (fun s => norm_nonneg _)))
          (integrable_norm_gaussVec.mul_const _) (Filter.Eventually.of_forall hstep)
    _ = (∫ g', ‖g'‖ ∂(gaussVec N)) * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) := by
        rw [integral_mul_const]
    _ ≤ Real.sqrt (2 * Real.log (2 * N)) * ∫ s, ‖∑ i, s i • x i‖ ∂(signVec N) :=
        mul_le_mul_of_nonneg_right (integral_pi_norm_gaussVec_le N) hKnn

end Helpers

/-- **Gaussian symmetrization, upper bound, sharp constant** (HDP §6.6,
Lemma 6.6.2): `E‖∑ Xᵢ‖ ≤ √(2π) · E‖∑ gᵢXᵢ‖` — the sharp form of the book's
constant `3`, from the exact `E|g| = √(2/π)`. -/
theorem gaussian_symmetrization_upper_sqrt {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ} {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability (book's E‖Xᵢ‖ < ∞); HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ ω, ‖∑ i, X i ω‖ ∂μ
      ≤ Real.sqrt (2 * Real.pi)
          * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N)) := by
  have hIS := integrable_normX (X := X) μ
    (ρ := signVec N) (fun i => integrable_eval_signVec i) hX_int
  have hIG := integrable_normX (X := X) μ
    (ρ := gaussVec N) (fun i => integrable_eval_gaussVec N i) hX_int
  have core : ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N))
      ≤ Real.sqrt (Real.pi / 2)
          * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N)) := by
    rw [integral_prod _ hIS, integral_prod _ hIG,
      ← integral_const_mul (Real.sqrt (Real.pi / 2))
        (fun ω => ∫ h, ‖∑ i, h i • X i ω‖ ∂(gaussVec N))]
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun ω => integral_nonneg (fun s => norm_nonneg _)))
      ((hIG.integral_prod_left).const_mul _)
      (Filter.Eventually.of_forall (fun ω => upper_inner (fun i => X i ω)))
  calc ∫ ω, ‖∑ i, X i ω‖ ∂μ
      ≤ 2 * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) :=
        symmetrization_upper hX_meas hX_int hX_mean hX_indep
    _ ≤ 2 * (Real.sqrt (Real.pi / 2)
          * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N))) :=
        mul_le_mul_of_nonneg_left core (by norm_num)
    _ = Real.sqrt (2 * Real.pi)
          * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N)) := by
        have hconst : (2 : ℝ) * Real.sqrt (Real.pi / 2) = Real.sqrt (2 * Real.pi) := by
          rw [show (2 : ℝ) * Real.pi = 4 * (Real.pi / 2) by ring,
            Real.sqrt_mul (by norm_num) (Real.pi / 2),
            show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [← mul_assoc, hconst]

/-- **Gaussian symmetrization, upper bound, book constant** (HDP §6.6,
Lemma 6.6.2): `E‖∑ Xᵢ‖ ≤ 3 · E‖∑ gᵢXᵢ‖`; headline via `√(2π) ≤ 3`
(`Real.pi_le_four`). -/
theorem gaussian_symmetrization_upper {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ ω, ‖∑ i, X i ω‖ ∂μ
      ≤ 3 * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N)) := by
  refine (gaussian_symmetrization_upper_sqrt hX_meas hX_int hX_mean hX_indep).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg (fun p => norm_nonneg _))
  rw [show (3 : ℝ) = Real.sqrt 9 by
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])

/-- **Gaussian symmetrization, lower bound, explicit constant** (HDP §6.6,
Lemma 6.6.2): `E‖∑ gᵢXᵢ‖ ≤ 2√(2 log(2N)) · E‖∑ Xᵢ‖` for all `N` (both sides
`0` at `N = 0`). Documented deviation: `√(log 2N)` vs the book's `√(log N)`
(two-sided union-bound cost). Named-sorry debt candidate of this work item. -/
theorem gaussian_symmetrization_lower {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {N : ℕ}
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N))
      ≤ 2 * Real.sqrt (2 * Real.log (2 * N)) * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  rcases eq_or_ne N 0 with hN0 | hN0
  · subst hN0
    simp
  haveI : NeZero N := ⟨hN0⟩
  have hIS := integrable_normX (X := X) μ
    (ρ := signVec N) (fun i => integrable_eval_signVec i) hX_int
  have hIG := integrable_normX (X := X) μ
    (ρ := gaussVec N) (fun i => integrable_eval_gaussVec N i) hX_int
  have core : ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N))
      ≤ Real.sqrt (2 * Real.log (2 * N))
          * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) := by
    rw [integral_prod _ hIG, integral_prod _ hIS,
      ← integral_const_mul (Real.sqrt (2 * Real.log (2 * N)))
        (fun ω => ∫ s, ‖∑ i, s i • X i ω‖ ∂(signVec N))]
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun ω => integral_nonneg (fun h => norm_nonneg _)))
      ((hIS.integral_prod_left).const_mul _)
      (Filter.Eventually.of_forall (fun ω => lower_inner (fun i => X i ω)))
  calc ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N))
      ≤ Real.sqrt (2 * Real.log (2 * N))
          * ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (signVec N)) := core
    _ ≤ Real.sqrt (2 * Real.log (2 * N)) * (2 * ∫ ω, ‖∑ i, X i ω‖ ∂μ) :=
        mul_le_mul_of_nonneg_left
          (symmetrization_lower hX_meas hX_int hX_mean hX_indep) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (2 * Real.log (2 * N)) * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by ring

/-- **Gaussian symmetrization, lower bound, book form** (HDP §6.6,
Lemma 6.6.2): for `N ≥ 2`, `E‖∑ gᵢXᵢ‖ ≤ 4√(log N) · E‖∑ Xᵢ‖` — the book's
`(c/√(log N)) E‖∑gX‖ ≤ E‖∑X‖` with explicit `c = 1/4`, via
`log(2N) ≤ 2 log N`. -/
theorem gaussian_symmetrization_lower_log {μ : Measure Ω}
    [IsProbabilityMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {N : ℕ}
    -- USER-INPUT: 2 ≤ N (the book's c/√(log N) form is vacuous at N = 1); HDP §6.6
    (hN : 2 ≤ N)
    {X : Fin N → Ω → E}
    -- LEAN-ONLY: measurability of the data
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: integrability; HDP §6.6 Lemma 6.6.2
    (hX_int : ∀ i, Integrable (X i) μ)
    -- USER-INPUT: mean zero; HDP §6.6 Lemma 6.6.2
    (hX_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    -- USER-INPUT: independent family; HDP §6.6 Lemma 6.6.2
    (hX_indep : iIndepFun X μ) :
    ∫ p, ‖∑ i, p.2 i • X i p.1‖ ∂(μ.prod (gaussVec N))
      ≤ 4 * Real.sqrt (Real.log N) * ∫ ω, ‖∑ i, X i ω‖ ∂μ := by
  refine (gaussian_symmetrization_lower hX_meas hX_int hX_mean hX_indep).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg (fun ω => norm_nonneg _))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hlog : Real.log (2 * (N : ℝ)) = Real.log 2 + Real.log N :=
    Real.log_mul (by norm_num) hNne
  have hle : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hsqrt : Real.sqrt (2 * Real.log (2 * N)) ≤ 2 * Real.sqrt (Real.log N) := by
    have e : (2 : ℝ) * Real.sqrt (Real.log N) = Real.sqrt (4 * Real.log N) := by
      rw [show (4 : ℝ) * Real.log N = 2 ^ 2 * Real.log N by ring,
        Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by norm_num), Real.sqrt_sq (by norm_num)]
    rw [e]
    exact Real.sqrt_le_sqrt (by rw [hlog]; nlinarith)
  linarith [hsqrt, Real.sqrt_nonneg (Real.log N)]

end StatLean.ConcentrationInequalities
