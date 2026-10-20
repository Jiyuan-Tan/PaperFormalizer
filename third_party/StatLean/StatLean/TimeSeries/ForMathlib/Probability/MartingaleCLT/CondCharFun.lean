module
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-!
# Conditional characteristic-function calculus for MDS arrays

The analytic bricks of the Brown/Hall–Heyde martingale CLT
(`MartingaleCLT/BrownCLT.lean` assembles them):

* the **conditional Taylor estimate**: a.e.,
  `‖E[e^{iuX} | 𝓖] − (1 − u²/2 · E[X² | 𝓖])‖` is controlled by the conditional
  Lindeberg mass at any level `ε` plus `|u|³ ε · E[X² | 𝓖]`;
* the **nesting-free tower telescope**
  (`norm_integral_exp_rowSum_mul_invProd_sub_one_le`): reweighting `e^{iuS_n}` by the
  *inverse* Taylor product `∏_i ψ_i⁻¹`, `ψ_i = 1 − u²/2 · E[X_i²|𝓕_i]`, makes
  `E[e^{iuS_n}∏_i ψ_i⁻¹]` a genuine martingale telescope whose distance to `1` is at
  most the summed conditional Taylor errors;
* the **product comparison**: on the event where the conditional variance process is
  close to `σ²` and the summands are uniformly small,
  `∏_i (1 − u²/2 · E[X_i²|𝓕_i])` is close to `e^{−u²σ²/2}` — in `L¹`
  (`tendsto_integral_abs_prod_one_sub_condVar_sub`), hence in mean;
* the **assembled comparison** (`norm_integral_exp_rowSum_sub_gaussian_le`), which
  combines the two into the bound on `‖E e^{iuS_n} − e^{−u²σ²/2}‖` that `mds_clt`
  consumes.

**Retired statement.**  An earlier plan routed the argument through an *unweighted*
telescope `‖E e^{iuS_n} − E ∏_i ψ_i‖ ≤ Σ_i (conditional Taylor errors)`
(`norm_integral_exp_rowSum_sub_prod_le`, deleted 2026-08-08).  That statement is
**false** as frozen.  Writing `φ_i = e^{iuX_i}` (modulus `1`, `𝓕_{i+1}`-measurable),
any telescoping of `∏φ − ∏ψ` has summands `Φ_j(φ_j − ψ_j)Λ_j` with `Φ_j = ∏_{i<j}φ_i`,
`Λ_j = ∏_{i>j}ψ_i`, and `φ_j − ψ_j = T_j + iuX_j + (u²/2)(v_j − X_j²)` with
`‖T_j‖ ≤ min(|uX_j|³/6, u²X_j²)`.  The frozen right-hand side is exactly `Σ_j E‖T_j‖`;
the other two summands are killed only if `Λ_j` is `𝓕_{n,j}`-measurable, i.e. only if
the *future* conditional variances are already known at time `j`.  They are
`𝓕_{n,i}`-measurable, never `𝓕_{n,j}`-measurable, so peeling from the right, from the
left, and the nested and bounded-multiplier variants all break at the same place; with
`v_i` a slowly-varying function of the past sum, `Σ_j E[Φ_j(iuX_j)Λ_j]` adds coherently
and grows like `√(k n)` relative to the frozen bound.  This is a missing hypothesis
(Brown's `V_n →p σ²` constant, or Hall–Heyde's nesting `𝓕_{n,i} ⊆ 𝓕_{n+1,i}`), not a
proof-search failure.  The nesting-free telescope above avoids it entirely: keeping the
ψ-factors in the *past* product makes the multiplier `𝓕_{n,i}`-measurable at every step.

**Reference.** Hall & Heyde (1980), §3.2 (proof of Thm 3.2), after Brown (1971) §3.
(`Hall–Heyde §3.2` in tags.)

**Proof formalization notes.**
* Conditional expectations of complex-valued integrands are taken componentwise
  (`Complex.re/im` through Mathlib's real `condExp`); the statements below pre-split
  them so the closure sessions never need a ℂ-valued `condExp` API.
* All statements are a.e. inequalities between real quantities — no conditional
  independence is ever invoked (that is the point of the martingale method).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

section CondTaylor

variable {Ω : Type*}

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`** — the pointwise input to the
conditional Taylor estimate: `‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both halves are elementary: the cubic one by integrating the exponential's remainder
three times, the quadratic one from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle
inequality (Mathlib only provides the non-uniform `taylor_charFun_two`). -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0:ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  have hA2z : ∀ z : ℝ, (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0:ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0:ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · have hz : (0:ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz

/-- **Conditional Taylor estimate** (Hall–Heyde Lemma 3.1-adjacent): for a
square-integrable `X` with `E[X | 𝓖] = 0` and any `ε > 0`, a.e.
`‖(E[cos uX | 𝓖] + i E[sin uX | 𝓖]) − (1 − u²/2 E[X²|𝓖])‖
  ≤ u² E[X² 1_{|X| ≥ ε} | 𝓖] + |u|³ ε E[X² | 𝓖]`.

Binder convention: ambient `mΩ` is a plain implicit bound after `m` and before `μ`
(see `Mixing/Relations.lean`). -/
theorem norm_condexp_exp_sub_one_sub_le {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {X : Ω → ℝ} (hX : Measurable X) (hL2 : MemLp X 2 μ)
    (hcond : μ[X | m] =ᵐ[μ] 0) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ,
      ‖(⟨μ[fun ω' => Real.cos (u * X ω') | m] ω,
          μ[fun ω' => Real.sin (u * X ω') | m] ω⟩ : ℂ)
          - (1 - u ^ 2 / 2 * μ[fun ω' => X ω' ^ 2 | m] ω)‖
        ≤ u ^ 2 * μ[fun ω' => X ω' ^ 2 * Set.indicator {x : Ω | ε ≤ |X x|}
              (fun _ => (1 : ℝ)) ω' | m] ω
          + |u| ^ 3 * ε * μ[fun ω' => X ω' ^ 2 | m] ω := by
  classical
  have hXint : Integrable X μ := hL2.integrable one_le_two
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := hL2.integrable_sq
  have hXabs : Measurable fun x => |X x| := continuous_abs.measurable.comp hX
  set S : Set Ω := {x : Ω | ε ≤ |X x|} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const hXabs
  have hindeq : (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
      = S.indicator (fun ω => X ω ^ 2) := by
    funext ω
    by_cases h : ω ∈ S <;> simp [h]
  have hind : Integrable (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω) μ := by
    rw [hindeq]; exact hX2.indicator hSm
  have hofX : Measurable fun ω => ((u * X ω : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_const.mul hX)
  -- the exponential, its Taylor polynomial, and the error
  set Z : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((u * X ω : ℝ) : ℂ)) with hZdef
  set P : Ω → ℂ := fun ω => 1 + Complex.I * ((u * X ω : ℝ) : ℂ)
      - ((u * X ω : ℝ) : ℂ) ^ 2 / 2 with hPdef
  set W : Ω → ℂ := fun ω => Z ω - P ω with hWdef
  set g : Ω → ℝ := fun ω => u ^ 2 * (X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
      + |u| ^ 3 * ε * X ω ^ 2 with hgdef
  have hgint : Integrable g μ := (hind.const_mul _).add (hX2.const_mul _)
  -- (i) the pointwise Taylor estimate, split at the level `ε`
  have hWbound : ∀ ω, ‖W ω‖ ≤ g ω := by
    intro ω
    have h : ‖W ω‖ ≤ min (|u * X ω| ^ 3 / 6) ((u * X ω) ^ 2) :=
      norm_cexp_sub_taylor_le (u * X ω)
    by_cases hcase : ω ∈ S
    · have hi : S.indicator (fun _ => (1 : ℝ)) ω = 1 := Set.indicator_of_mem hcase 1
      have h2 : ‖W ω‖ ≤ (u * X ω) ^ 2 := h.trans (min_le_right _ _)
      have hnn : 0 ≤ |u| ^ 3 * ε * X ω ^ 2 := by positivity
      simp only [hgdef, hi, mul_one]
      nlinarith [h2]
    · have hi : S.indicator (fun _ => (1 : ℝ)) ω = 0 := Set.indicator_of_notMem hcase _
      have hlt : |X ω| < ε := by
        simpa [hSdef, Set.mem_setOf_eq, not_le] using hcase
      have h2 : ‖W ω‖ ≤ |u * X ω| ^ 3 / 6 := h.trans (min_le_left _ _)
      have habs : |u * X ω| ^ 3 = |u| ^ 3 * (|X ω| * X ω ^ 2) := by
        rw [abs_mul, mul_pow, show |X ω| ^ 3 = |X ω| * |X ω| ^ 2 by ring, sq_abs]
      have hu3 : (0 : ℝ) ≤ |u| ^ 3 := by positivity
      have hcube : |X ω| * X ω ^ 2 ≤ ε * X ω ^ 2 :=
        mul_le_mul_of_nonneg_right hlt.le (sq_nonneg _)
      have step1 : |u| ^ 3 * (|X ω| * X ω ^ 2) ≤ |u| ^ 3 * (ε * X ω ^ 2) :=
        mul_le_mul_of_nonneg_left hcube hu3
      have step2 : (0 : ℝ) ≤ |u| ^ 3 * (ε * X ω ^ 2) := by positivity
      have step3 : |u| ^ 3 * ε * X ω ^ 2 = |u| ^ 3 * (ε * X ω ^ 2) := by ring
      simp only [hgdef, hi, mul_zero, zero_add]
      rw [habs] at h2
      linarith
  -- (ii) integrability
  have hZint : Integrable Z μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact ((Complex.measurable_exp.comp (measurable_const.mul hofX))).aestronglyMeasurable
    · simp [hZdef, Complex.norm_exp]
  have hofXint : Integrable (fun ω => ((X ω : ℝ) : ℂ)) μ := by
    simpa using Complex.ofRealCLM.integrable_comp hXint
  have hofX2int : Integrable (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) μ := by
    simpa using Complex.ofRealCLM.integrable_comp hX2
  have hPeq : P = (fun _ => (1 : ℂ)) + (Complex.I * (u : ℂ)) • (fun ω => ((X ω : ℝ) : ℂ))
      - ((u : ℂ) ^ 2 / 2) • (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) := by
    funext ω
    simp only [hPdef, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hPint : Integrable P μ := by
    rw [hPeq]
    exact ((integrable_const _).add (hofXint.smul _)).sub (hofX2int.smul _)
  have hWint : Integrable W μ := hZint.sub hPint
  -- (iii) conditional Jensen for the modulus + conditional monotonicity
  have hJensen : ∀ᵐ ω ∂μ, ‖μ[W | m] ω‖ ≤ μ[g | m] ω := by
    have h1 := _root_.norm_condExp_le (m := m) (μ := μ) W
    have h2 := condExp_mono (m := m) hWint.norm hgint (ae_of_all _ hWbound)
    filter_upwards [h1, h2] with ω hh1 hh2 using hh1.trans hh2
  -- (iv) the conditional expectation of the majorant
  have hgcond : μ[g | m] =ᵐ[μ] fun ω =>
      u ^ 2 * μ[fun ω' => X ω' ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω' | m] ω
        + |u| ^ 3 * ε * μ[fun ω' => X ω' ^ 2 | m] ω := by
    have hgeq : g = (u ^ 2) • (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
        + (|u| ^ 3 * ε) • (fun ω => X ω ^ 2) := by
      funext ω; simp [hgdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hgeq]
    have h1 := condExp_add (μ := μ) (m := m) (hind.smul (u ^ 2)) (hX2.smul (|u| ^ 3 * ε))
    have h2 := condExp_smul (μ := μ) (m := m) (u ^ 2)
      (fun ω => X ω ^ 2 * S.indicator (fun _ => (1 : ℝ)) ω)
    have h3 := condExp_smul (μ := μ) (m := m) (|u| ^ 3 * ε) (fun ω => X ω ^ 2)
    filter_upwards [h1, h2, h3] with ω e1 e2 e3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 ⊢
    rw [e1, e2, e3]
  -- (v) the conditional expectation of `Z` is the pair of the real conditional expectations
  have hcosint : Integrable (fun ω => Real.cos (u * X ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact (Real.measurable_cos.comp (measurable_const.mul hX)).aestronglyMeasurable
    · simpa using Real.abs_cos_le_one _
  have hsinint : Integrable (fun ω => Real.sin (u * X ω)) μ := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
    · exact (Real.measurable_sin.comp (measurable_const.mul hX)).aestronglyMeasurable
    · simpa using Real.abs_sin_le_one _
  have hZre : (fun ω => (μ[Z | m] ω).re) =ᵐ[μ] μ[fun ω => Real.cos (u * X ω) | m] := by
    have h := Complex.reCLM.comp_condExp_comm (m := m) hZint
    have hcomp : (⇑Complex.reCLM ∘ Z) = fun ω => Real.cos (u * X ω) := by
      funext ω
      simp only [hZdef, Function.comp_apply, Complex.reCLM_apply]
      rw [mul_comm, Complex.exp_ofReal_mul_I_re]
    rw [hcomp] at h
    exact h
  have hZim : (fun ω => (μ[Z | m] ω).im) =ᵐ[μ] μ[fun ω => Real.sin (u * X ω) | m] := by
    have h := Complex.imCLM.comp_condExp_comm (m := m) hZint
    have hcomp : (⇑Complex.imCLM ∘ Z) = fun ω => Real.sin (u * X ω) := by
      funext ω
      simp only [hZdef, Function.comp_apply, Complex.imCLM_apply]
      rw [mul_comm, Complex.exp_ofReal_mul_I_im]
    rw [hcomp] at h
    exact h
  -- (vi) the conditional expectation of the Taylor polynomial
  have hofRe : ∀ f : Ω → ℝ, Integrable f μ →
      μ[fun ω => ((f ω : ℝ) : ℂ) | m] =ᵐ[μ] fun ω => ((μ[f | m] ω : ℝ) : ℂ) := by
    intro f hf
    have h := Complex.ofRealCLM.comp_condExp_comm (m := m) hf
    have hcomp : (⇑Complex.ofRealCLM ∘ f) = fun ω => ((f ω : ℝ) : ℂ) := rfl
    rw [hcomp] at h
    exact h.symm
  have hcondP : μ[P | m] =ᵐ[μ] fun ω =>
      (1 : ℂ) - (u : ℂ) ^ 2 / 2 * ((μ[fun ω' => X ω' ^ 2 | m] ω : ℝ) : ℂ) := by
    rw [hPeq]
    have h1 := condExp_add (μ := μ) (m := m) (integrable_const (1 : ℂ))
      (hofXint.smul (Complex.I * (u : ℂ)))
    have h2 := condExp_sub (μ := μ) (m := m)
      ((integrable_const (1 : ℂ)).add (hofXint.smul (Complex.I * (u : ℂ))))
      (hofX2int.smul ((u : ℂ) ^ 2 / 2))
    have h3 := condExp_smul (μ := μ) (m := m) (Complex.I * (u : ℂ))
      (fun ω => ((X ω : ℝ) : ℂ))
    have h4 := condExp_smul (μ := μ) (m := m) ((u : ℂ) ^ 2 / 2)
      (fun ω => ((X ω ^ 2 : ℝ) : ℂ))
    have h5 := hofRe X hXint
    have h6 := hofRe (fun ω => X ω ^ 2) hX2
    have h7 : μ[fun _ : Ω => (1 : ℂ) | m] = fun _ => (1 : ℂ) := condExp_const hm _
    filter_upwards [h1, h2, h3, h4, h5, h6, hcond] with ω e1 e2 e3 e4 e5 e6 e7
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 e3 e4 ⊢
    rw [e2, e1, e3, e4, e5, e6, h7]
    simp only [e7, Pi.zero_apply, Complex.ofReal_zero, mul_zero, add_zero]
  -- (vii) assembly
  have hcondW : μ[W | m] =ᵐ[μ] μ[Z | m] - μ[P | m] := condExp_sub hZint hPint m
  filter_upwards [hJensen, hgcond, hZre, hZim, hcondP, hcondW] with ω h1 h2 h3 h4 h5 h6
  have hEq : (⟨μ[fun ω' => Real.cos (u * X ω') | m] ω,
      μ[fun ω' => Real.sin (u * X ω') | m] ω⟩ : ℂ)
      - (1 - u ^ 2 / 2 * μ[fun ω' => X ω' ^ 2 | m] ω) = μ[W | m] ω := by
    rw [h6]
    simp only [Pi.sub_apply, h5]
    apply Complex.ext
    · simp [← h3]
    · simp [← h4]
  rw [hEq, ← h2]
  exact h1

open Complex in
/-- The `ℂ`-valued conditional characteristic function is the pair of the two real
conditional expectations that `norm_condexp_exp_sub_one_sub_le` is stated with. -/
private lemma condExp_cexp_eq_pair {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y) (u : ℝ) :
    ∀ᵐ ω ∂μ, μ[fun ω' => Complex.exp (I * ((u * Y ω' : ℝ) : ℂ)) | m] ω
      = (⟨μ[fun ω' => Real.cos (u * Y ω') | m] ω,
          μ[fun ω' => Real.sin (u * Y ω') | m] ω⟩ : ℂ) := by
  have hmeas : Measurable fun ω => Complex.exp (I * ((u * Y ω : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hY)).const_mul I)
  have hZint : Integrable (fun ω => Complex.exp (I * ((u * Y ω : ℝ) : ℂ))) μ := by
    refine (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp [Complex.norm_exp]
  have hre := Complex.reCLM.comp_condExp_comm (m := m) hZint
  have him := Complex.imCLM.comp_condExp_comm (m := m) hZint
  have hcompre : (⇑Complex.reCLM ∘ fun ω => Complex.exp (I * ((u * Y ω : ℝ) : ℂ)))
      = fun ω => Real.cos (u * Y ω) := by
    funext ω
    simp only [Function.comp_apply, Complex.reCLM_apply]
    rw [mul_comm, Complex.exp_ofReal_mul_I_re]
  have hcompim : (⇑Complex.imCLM ∘ fun ω => Complex.exp (I * ((u * Y ω : ℝ) : ℂ)))
      = fun ω => Real.sin (u * Y ω) := by
    funext ω
    simp only [Function.comp_apply, Complex.imCLM_apply]
    rw [mul_comm, Complex.exp_ofReal_mul_I_im]
  rw [hcompre] at hre
  rw [hcompim] at him
  filter_upwards [hre, him] with ω h1 h2
  exact Complex.ext (by simpa using h1) (by simpa using h2)

open Complex in
/-- **Conditional Taylor estimate, `ℂ`-valued form.** Same content as
`norm_condexp_exp_sub_one_sub_le`, phrased with the conditional expectation of the complex
exponential itself — the form the tower peel consumes. -/
theorem norm_condexp_cexp_sub_taylor_le {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {Y : Ω → ℝ} (hY : Measurable Y) (hL2 : MemLp Y 2 μ)
    (hcond : μ[Y | m] =ᵐ[μ] 0) (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ‖μ[fun ω' => Complex.exp (I * ((u * Y ω' : ℝ) : ℂ)) | m] ω
        - (1 - u ^ 2 / 2 * μ[fun ω' => Y ω' ^ 2 | m] ω)‖
      ≤ u ^ 2 * μ[fun ω' => Y ω' ^ 2 * Set.indicator {x : Ω | ε ≤ |Y x|}
            (fun _ => (1 : ℝ)) ω' | m] ω
        + |u| ^ 3 * ε * μ[fun ω' => Y ω' ^ 2 | m] ω := by
  filter_upwards [condExp_cexp_eq_pair (m := m) (μ := μ) hY u,
    norm_condexp_exp_sub_one_sub_le hm hY hL2 hcond u hε] with ω h1 h2
  rw [h1]
  exact h2

end CondTaylor

section ProductEstimates

/-! ### Elementary product estimates

The deterministic inputs to the product comparison: the Taylor product `∏ (1 − u²vᵢ/2)`
is compared with `∏ e^{−u²vᵢ/2} = e^{−u²V/2}` factorwise, and the latter with the
Gaussian factor by the (one-)Lipschitz property of `e^{−·}` on `[0, ∞)`. -/

/-- `|∏ f − ∏ g| ≤ Σ |f − g|` for two families in the real unit ball. -/
private lemma abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i, |f i| ≤ 1) (hg : ∀ i, |g i| ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hfs : |∏ i ∈ s, f i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun i _ => abs_nonneg _) fun i _ => hf i
    have hkey : f a * (∏ i ∈ s, f i) - g a * ∏ i ∈ s, g i
        = (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
    rw [hkey]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |f a - g a| * |∏ i ∈ s, f i| ≤ |f a - g a| * 1 :=
      mul_le_mul_of_nonneg_left hfs (abs_nonneg _)
    have h2 : |g a| * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ 1 * ∑ i ∈ s, |f i - g i| :=
      mul_le_mul (hg a) ih (abs_nonneg _) zero_le_one
    linarith

/-- `|(1 − a) − e^{−a}| ≤ a²` for `a ≥ 0` (both halves from `1 + x ≤ eˣ`). -/
private lemma abs_one_sub_sub_exp_neg_le {a : ℝ} (ha : 0 ≤ a) :
    |(1 - a) - Real.exp (-a)| ≤ a ^ 2 := by
  have hA : 1 - a ≤ Real.exp (-a) := by have := Real.add_one_le_exp (-a); linarith
  have hp : 0 < Real.exp (-a) := Real.exp_pos _
  have hB : Real.exp (-a) * (1 + a) ≤ 1 := by
    have h := Real.add_one_le_exp a
    have he : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  rw [abs_le]
  constructor <;> nlinarith

/-- `e^{−·}` is `1`-Lipschitz on `[0, ∞)`. -/
private lemma abs_exp_neg_sub_le {S L : ℝ} (hS : 0 ≤ S) (hL : 0 ≤ L) :
    |Real.exp (-S) - Real.exp (-L)| ≤ |S - L| := by
  have key : ∀ x y : ℝ, 0 ≤ x → x ≤ y → Real.exp (-x) - Real.exp (-y) ≤ y - x := by
    intro x y hx hxy
    have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : 1 - (y - x) ≤ Real.exp (-(y - x)) := by
      have := Real.add_one_le_exp (-(y - x)); linarith
    have h3 : Real.exp (-x) * Real.exp (-(y - x)) = Real.exp (-y) := by
      rw [← Real.exp_add]; congr 1; ring
    have hp : 0 < Real.exp (-x) := Real.exp_pos _
    nlinarith
  rcases le_total S L with hle | hle
  · have h1 := key S L hS hle
    have h2 : Real.exp (-L) ≤ Real.exp (-S) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (by linarith : S - L ≤ 0), abs_of_nonneg (by linarith)]
    linarith
  · have h1 := key L S hL hle
    have h2 : Real.exp (-S) ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ S - L), abs_of_nonpos (by linarith)]
    linarith

/-- The Taylor product is uniformly bounded by `e^{u²c/2}` as soon as the conditional
variance **process** is bounded by `c` — this is what makes the product comparison
dominated-convergence-friendly (a bound on `E V` alone does not, see the witness on
`tendsto_integral_prod_one_sub_condVar`). -/
private lemma abs_prod_one_sub_le_exp {m : ℕ} {v : Fin m → ℝ} {u c : ℝ}
    (hv0 : ∀ i, 0 ≤ v i) (hsum : (∑ i, v i) ≤ c) :
    |∏ i, (1 - u ^ 2 / 2 * v i)| ≤ Real.exp (u ^ 2 * c / 2) := by
  rw [Finset.abs_prod]
  have hstep : ∀ i ∈ Finset.univ, |1 - u ^ 2 / 2 * v i| ≤ Real.exp (u ^ 2 / 2 * v i) := by
    intro i _
    have ha : 0 ≤ u ^ 2 / 2 * v i := mul_nonneg (by positivity) (hv0 i)
    have h1 : |1 - u ^ 2 / 2 * v i| ≤ 1 + u ^ 2 / 2 * v i := by
      rw [abs_le]; constructor <;> linarith
    have h2 := Real.add_one_le_exp (u ^ 2 / 2 * v i)
    linarith
  calc ∏ i, |1 - u ^ 2 / 2 * v i| ≤ ∏ i, Real.exp (u ^ 2 / 2 * v i) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) hstep
    _ = Real.exp (∑ i, u ^ 2 / 2 * v i) := (Real.exp_sum _ _).symm
    _ = Real.exp (u ^ 2 / 2 * ∑ i, v i) := by rw [Finset.mul_sum]
    _ ≤ Real.exp (u ^ 2 * c / 2) := by
        refine Real.exp_le_exp.2 ?_
        have : (0:ℝ) ≤ u ^ 2 / 2 := by positivity
        nlinarith

/-- **The pointwise product comparison**: on the event where every conditional variance is
at most `β` and the variance process is within `β` of `σ²`, the Taylor product is within
`(u²β/2)·(u²(σ² + β)/2) + u²β/2` of the Gaussian factor `e^{−u²σ²/2}`. -/
private lemma abs_prod_one_sub_sub_exp_le {m : ℕ} {v : Fin m → ℝ} {u σ2 β : ℝ}
    (hv0 : ∀ i, 0 ≤ v i) (hvb : ∀ i, v i ≤ β) (hβ : 0 ≤ β)
    (hsmall : u ^ 2 * β ≤ 1) (hσ : 0 ≤ σ2)
    (hsum : |(∑ i, v i) - σ2| ≤ β) :
    |(∏ i, (1 - u ^ 2 / 2 * v i)) - Real.exp (-(u ^ 2 * σ2 / 2))|
      ≤ u ^ 2 * β / 2 * (u ^ 2 * (σ2 + β) / 2) + u ^ 2 * β / 2 := by
  have hu : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
  have ha0 : ∀ i, 0 ≤ u ^ 2 / 2 * v i := fun i => mul_nonneg (by positivity) (hv0 i)
  have hab : ∀ i, u ^ 2 / 2 * v i ≤ u ^ 2 * β / 2 := by
    intro i
    have := mul_le_mul_of_nonneg_left (hvb i) (by positivity : (0:ℝ) ≤ u ^ 2 / 2)
    linarith
  have hahalf : ∀ i, u ^ 2 / 2 * v i ≤ 1 / 2 := fun i => (hab i).trans (by linarith)
  -- (i) replace each factor by its exponential
  have hstep1 : |(∏ i, (1 - u ^ 2 / 2 * v i)) - ∏ i, Real.exp (-(u ^ 2 / 2 * v i))|
      ≤ ∑ i, (u ^ 2 / 2 * v i) ^ 2 := by
    refine le_trans (abs_prod_sub_prod_le Finset.univ
      (f := fun i => 1 - u ^ 2 / 2 * v i) (g := fun i => Real.exp (-(u ^ 2 / 2 * v i)))
      (fun i => by rw [abs_le]; constructor <;> linarith [ha0 i, hahalf i])
      (fun i => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.2 (by linarith [ha0 i]))) ?_
    exact Finset.sum_le_sum fun i _ => abs_one_sub_sub_exp_neg_le (ha0 i)
  -- (ii) the exponential product is the exponential of the variance process
  have hstep2 : (∏ i, Real.exp (-(u ^ 2 / 2 * v i))) = Real.exp (-(u ^ 2 / 2 * ∑ i, v i)) := by
    rw [← Real.exp_sum]
    congr 1
    simp [Finset.mul_sum]
  -- (iii) the quadratic remainder
  have hsq : ∑ i, (u ^ 2 / 2 * v i) ^ 2 ≤ u ^ 2 * β / 2 * (u ^ 2 / 2 * ∑ i, v i) := by
    have hrw : u ^ 2 * β / 2 * (u ^ 2 / 2 * ∑ i, v i)
        = ∑ i, u ^ 2 * β / 2 * (u ^ 2 / 2 * v i) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hrw]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := ha0 i
    have h2 := hab i
    nlinarith
  have hSle : u ^ 2 / 2 * ∑ i, v i ≤ u ^ 2 * (σ2 + β) / 2 := by
    have h1 : (∑ i, v i) ≤ σ2 + β := by
      have := (abs_le.1 hsum).2; linarith
    nlinarith
  have hS0 : 0 ≤ u ^ 2 / 2 * ∑ i, v i :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hv0 i)
  -- (iv) the Gaussian factor
  have hstep3 : |Real.exp (-(u ^ 2 / 2 * ∑ i, v i)) - Real.exp (-(u ^ 2 * σ2 / 2))|
      ≤ u ^ 2 * β / 2 := by
    refine le_trans (abs_exp_neg_sub_le hS0 (by positivity)) ?_
    have he : u ^ 2 / 2 * (∑ i, v i) - u ^ 2 * σ2 / 2 = u ^ 2 / 2 * ((∑ i, v i) - σ2) := by ring
    rw [he, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ u ^ 2 / 2)]
    have := mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ u ^ 2 / 2)
    linarith
  have hquad : ∑ i, (u ^ 2 / 2 * v i) ^ 2 ≤ u ^ 2 * β / 2 * (u ^ 2 * (σ2 + β) / 2) := by
    refine hsq.trans ?_
    have h0 : (0:ℝ) ≤ u ^ 2 * β / 2 := by positivity
    exact mul_le_mul_of_nonneg_left hSle h0
  calc |(∏ i, (1 - u ^ 2 / 2 * v i)) - Real.exp (-(u ^ 2 * σ2 / 2))|
      ≤ |(∏ i, (1 - u ^ 2 / 2 * v i)) - ∏ i, Real.exp (-(u ^ 2 / 2 * v i))|
        + |(∏ i, Real.exp (-(u ^ 2 / 2 * v i))) - Real.exp (-(u ^ 2 * σ2 / 2))| :=
        abs_sub_le _ _ _
    _ ≤ u ^ 2 * β / 2 * (u ^ 2 * (σ2 + β) / 2) + u ^ 2 * β / 2 := by
        rw [hstep2] at hstep1 ⊢
        linarith [hstep1.trans hquad, hstep3]

/-- `(1 − a)⁻¹ ≤ e^{2a}` for `a ∈ [0, 1/2]`. -/
private lemma inv_one_sub_le_exp_two_mul {a : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 1 / 2) :
    (1 - a)⁻¹ ≤ Real.exp (2 * a) := by
  have hpos : (0:ℝ) < 1 - a := by linarith
  have hE : 1 + 2 * a ≤ Real.exp (2 * a) := by
    have := Real.add_one_le_exp (2 * a); linarith
  have h1 : 1 ≤ Real.exp (2 * a) * (1 - a) := by nlinarith
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  exact h1

/-- The **inverse** Taylor product is bounded by `e^{u²c}` on any index subset, as soon as
each `u²vᵢ/2 ≤ 1/2` and the variance process is bounded by `c`.  This is the domination that
makes the nesting-free (multiplicative) telescope work. -/
private lemma prod_inv_one_sub_le_exp {m : ℕ} {v : Fin m → ℝ} {u c : ℝ}
    (hv0 : ∀ i, 0 ≤ v i) (hvd : ∀ i, u ^ 2 / 2 * v i ≤ 1 / 2) (hsum : (∑ i, v i) ≤ c)
    (s : Finset (Fin m)) :
    ∏ i ∈ s, (1 - u ^ 2 / 2 * v i)⁻¹ ≤ Real.exp (u ^ 2 * c) := by
  have ha0 : ∀ i, 0 ≤ u ^ 2 / 2 * v i := fun i => mul_nonneg (by positivity) (hv0 i)
  have hu : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
  calc ∏ i ∈ s, (1 - u ^ 2 / 2 * v i)⁻¹
      ≤ ∏ i ∈ s, Real.exp (2 * (u ^ 2 / 2 * v i)) :=
        Finset.prod_le_prod (fun i _ => inv_nonneg.2 (by linarith [ha0 i, hvd i]))
          (fun i _ => inv_one_sub_le_exp_two_mul (ha0 i) (hvd i))
    _ = Real.exp (∑ i ∈ s, 2 * (u ^ 2 / 2 * v i)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (u ^ 2 * c) := by
        refine Real.exp_le_exp.2 ?_
        have hsub : (∑ i ∈ s, v i) ≤ ∑ i, v i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hv0 j
        have hrw : (∑ i ∈ s, 2 * (u ^ 2 / 2 * v i)) = u ^ 2 * ∑ i ∈ s, v i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hrw]
        nlinarith

end ProductEstimates

section Arrays

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

open Complex in
/-- **One tower peel** — the reusable core of every telescope in this file.

If the multiplier `Y` is `𝓕_{n,i}`-measurable (i.e. *known at time `i`*) and bounded by
`B`, then replacing `e^{iuX_{n,i}}` by its conditional Taylor polynomial
`1 − u²/2·E[X_{n,i}²|𝓕_{n,i}]` under the integral costs at most `B` times the `i`-th
conditional Taylor error.  Only the tower property and the pull-out property are used.

The hypothesis `hYm` is the crux of the whole method: the multiplier must be measurable
**at time `i`**, never later.  It is exactly what the frozen
`norm_integral_exp_rowSum_sub_prod_le` cannot arrange for the future ψ-factors, and what
`norm_integral_exp_rowSum_mul_invProd_sub_one_le` arranges by keeping the ψ-factors in the
*past* product. -/
theorem norm_integral_mul_cexp_sub_taylor_le [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) (n : ℕ) (i : Fin (k n)) (u : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Y : Ω → ℂ} (hYm : StronglyMeasurable[F n i.castSucc] Y) {B : ℝ}
    (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ B) :
    ‖∫ ω, Y ω * (Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
        - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) ∂μ‖
      ≤ B * (u ^ 2 * ∫ ω, X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
              (fun _ => (1 : ℝ)) ω ∂μ + |u| ^ 3 * ε * ∫ ω, X n i ω ^ 2 ∂μ) := by
  classical
  have hm : F n i.castSucc ≤ ‹MeasurableSpace Ω› := h.le_ambient n i.castSucc
  have hXm : Measurable (X n i) := (h.adapted n i).mono (h.le_ambient n _) le_rfl
  have hXsq : Integrable (fun ω => X n i ω ^ 2) μ := (h.memLp n i).integrable_sq
  have hSm : MeasurableSet {x : Ω | ε ≤ |X n i x|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp hXm)
  have hindint : Integrable (fun ω => X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
      (fun _ => (1 : ℝ)) ω) μ := by
    have heq : (fun ω => X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
        (fun _ => (1 : ℝ)) ω)
        = Set.indicator {x : Ω | ε ≤ |X n i x|} (fun ω => X n i ω ^ 2) := by
      funext ω; by_cases hω : ω ∈ {x : Ω | ε ≤ |X n i x|} <;> simp [hω]
    rw [heq]; exact hXsq.indicator hSm
  -- the exponential, its conditional expectation, and the Taylor polynomial
  have hZm : Measurable fun ω => Complex.exp (I * ((u * X n i ω : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hXm)).const_mul I)
  have hZ1 : ∀ ω, ‖Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))‖ = 1 := fun ω => by
    rw [Complex.norm_exp]; simp
  have hZint : Integrable (fun ω => Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))) μ :=
    (integrable_const (1 : ℝ)).mono' hZm.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [hZ1 ω])
  have hYmeas : Measurable Y := hYm.measurable.mono hm le_rfl
  have hYas : AEStronglyMeasurable Y μ := hYmeas.aestronglyMeasurable
  have hvint : Integrable (μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc]) μ := integrable_condExp
  have hΨint : Integrable (fun ω =>
      (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)) μ := by
    have h1 : Integrable
        (fun ω => ((μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℝ) : ℂ)) μ := by
      simpa using Complex.ofRealCLM.integrable_comp hvint
    simpa using! (integrable_const (1 : ℂ)).sub (h1.const_mul ((u : ℂ) ^ 2 / 2))
  have hCEint : Integrable (μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ))
      | F n i.castSucc]) μ := integrable_condExp
  -- the tower step
  have hYZint : Integrable (fun ω => Y ω * Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))) μ :=
    hZint.bdd_mul hYas hYb
  have hYΨint : Integrable (fun ω => Y ω * (1 - u ^ 2 / 2 *
      μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)) μ := hΨint.bdd_mul hYas hYb
  have hYCEint : Integrable (fun ω => Y ω *
      μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ)) | F n i.castSucc] ω) μ :=
    hCEint.bdd_mul hYas hYb
  have hpull : μ[fun ω => Y ω * Complex.exp (I * ((u * X n i ω : ℝ) : ℂ)) | F n i.castSucc]
      =ᵐ[μ] fun ω => Y ω * μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ))
        | F n i.castSucc] ω := by
    have := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
      (m := F n i.castSucc) (μ := μ) hYm (by simpa using hYZint) hZint
    simpa using this
  have hkey : (∫ ω, Y ω * Complex.exp (I * ((u * X n i ω : ℝ) : ℂ)) ∂μ)
      = ∫ ω, Y ω * μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ))
        | F n i.castSucc] ω ∂μ := by
    calc (∫ ω, Y ω * Complex.exp (I * ((u * X n i ω : ℝ) : ℂ)) ∂μ)
        = ∫ ω, μ[fun ω => Y ω * Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
            | F n i.castSucc] ω ∂μ := (integral_condExp hm).symm
      _ = _ := integral_congr_ae hpull
  have hrewrite : (∫ ω, Y ω * (Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
      - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) ∂μ)
      = ∫ ω, Y ω * (μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ))
          | F n i.castSucc] ω
        - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) ∂μ := by
    have hL : (∫ ω, Y ω * (Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
        - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) ∂μ)
        = (∫ ω, Y ω * Complex.exp (I * ((u * X n i ω : ℝ) : ℂ)) ∂μ)
          - ∫ ω, Y ω * (1 - u ^ 2 / 2 *
            μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ) ∂μ := by
      have hfun : (fun ω => Y ω * (Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
          - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)))
          = fun ω => Y ω * Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
            - Y ω * (1 - u ^ 2 / 2 *
              μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ) := by
        funext ω; ring
      rw [hfun]
      exact integral_sub hYZint hYΨint
    have hR : (∫ ω, Y ω * (μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ))
          | F n i.castSucc] ω
        - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) ∂μ)
        = (∫ ω, Y ω * μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ))
            | F n i.castSucc] ω ∂μ)
          - ∫ ω, Y ω * (1 - u ^ 2 / 2 *
            μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ) ∂μ := by
      have hfun : (fun ω => Y ω *
          (μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ)) | F n i.castSucc] ω
            - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)))
          = fun ω => Y ω *
              μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ)) | F n i.castSucc] ω
            - Y ω * (1 - u ^ 2 / 2 *
              μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ) := by
        funext ω; ring
      rw [hfun]
      exact integral_sub hYCEint hYΨint
    rw [hL, hR, hkey]
  rw [hrewrite]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hCE := norm_condexp_cexp_sub_taylor_le hm hXm (h.memLp n i) (h.condexp_zero n i) u hε
  have hdiffint : Integrable (fun ω => Y ω *
      (μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ)) | F n i.castSucc] ω
        - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω))) μ := by
    have hfun : (fun ω => Y ω *
        (μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ)) | F n i.castSucc] ω
          - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)))
        = fun ω => Y ω *
            μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ)) | F n i.castSucc] ω
          - Y ω * (1 - u ^ 2 / 2 *
            μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ) := by
      funext ω; ring
    rw [hfun]
    exact hYCEint.sub hYΨint
  have hmajint : Integrable (fun ω => B * (u ^ 2 *
      μ[fun ω' => X n i ω' ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
        (fun _ => (1 : ℝ)) ω' | F n i.castSucc] ω
      + |u| ^ 3 * ε * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) μ :=
    ((integrable_condExp.const_mul _).add (integrable_condExp.const_mul _)).const_mul _
  have hbound : ∀ᵐ ω ∂μ, ‖Y ω *
      (μ[fun ω' => Complex.exp (I * ((u * X n i ω' : ℝ) : ℂ)) | F n i.castSucc] ω
        - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω))‖
      ≤ B * (u ^ 2 * μ[fun ω' => X n i ω' ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
          (fun _ => (1 : ℝ)) ω' | F n i.castSucc] ω
        + |u| ^ 3 * ε * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) := by
    filter_upwards [hYb, hCE] with ω h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  refine le_trans (integral_mono_ae hdiffint.norm hmajint hbound) (le_of_eq ?_)
  rw [integral_const_mul, integral_add (integrable_condExp.const_mul _)
    (integrable_condExp.const_mul _), integral_const_mul, integral_const_mul,
    integral_condExp hm, integral_condExp hm]

open Complex in
/-- **Nesting-free tower telescope** (the route `mds_clt` actually uses).

Reweighting `e^{iuS_n}` by the *inverse* Taylor product `∏ᵢ ψᵢ⁻¹`,
`ψᵢ = 1 − u²/2·E[X_{n,i}²|𝓕_{n,i}]`, turns Brown's comparison into a genuine martingale
telescope: peeling the factor at index `i` leaves the multiplier
`(∏_{j<i} e^{iuX_j}ψⱼ⁻¹)·ψᵢ⁻¹`, which is `𝓕_{n,i}`-measurable — the *past* product.  No
nesting or predictability of the conditional variances is needed, unlike for the
unweighted comparison `E e^{iuS_n}` vs `E ∏ᵢψᵢ` (see the obstruction on
`norm_integral_exp_rowSum_sub_prod_le`).

The price is the two clamps: `hd` (each conditional variance `≤ d` with `u²d ≤ 1`, so
`ψᵢ ∈ [1/2, 1]` and the inverses exist) and `hc` (the variance process `≤ c`, so the
inverse product is bounded by `e^{u²c}`).  Both are supplied by the doubly truncated
Hall–Heyde array in `MartingaleCLT/BrownCLT.lean`. -/
theorem norm_integral_exp_rowSum_mul_invProd_sub_one_le [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) (n : ℕ) (u : ℝ) {ε : ℝ} (hε : 0 < ε) {c d : ℝ}
    -- LEAN-ONLY: per-index clamp making every Taylor factor lie in `[1/2, 1]`
    (hd : ∀ i, ∀ᵐ ω ∂μ, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω ≤ d)
    (hdu : u ^ 2 * d ≤ 1)
    -- LEAN-ONLY: clamp on the conditional variance process
    (hc : ∀ᵐ ω ∂μ, mdsCondVariance k X F μ n ω ≤ c) :
    ‖(∫ ω, Complex.exp (I * ((u * mdsRowSum k X n ω : ℝ) : ℂ))
        * ∏ i, (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹ ∂μ) - 1‖
      ≤ 2 * Real.exp (u ^ 2 * c)
        * (∑ i, (u ^ 2 * ∫ ω, X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
              (fun _ => (1 : ℝ)) ω ∂μ) + ∑ i, (|u| ^ 3 * ε * ∫ ω, X n i ω ^ 2 ∂μ)) := by
  classical
  have hu2 : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
  -- (0) pointwise control of the Taylor factors
  have hae : ∀ᵐ ω ∂μ, (∀ i : Fin (k n),
        0 ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω
          ∧ u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω ≤ 1 / 2)
      ∧ mdsCondVariance k X F μ n ω ≤ c := by
    have h1 : ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
        0 ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω :=
      ae_all_iff.2 fun i => condExp_nonneg (ae_of_all _ fun _ => sq_nonneg _)
    have h2 : ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
        μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω ≤ d := ae_all_iff.2 hd
    filter_upwards [h1, h2, hc] with ω e1 e2 e3
    refine ⟨fun i => ⟨e1 i, ?_⟩, e3⟩
    have := mul_le_mul_of_nonneg_left (e2 i) (by positivity : (0:ℝ) ≤ u ^ 2 / 2)
    nlinarith [e1 i]
  -- (1) the cumulative index sets
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Finset (Fin (k n)),
      ∀ m, S m = Finset.univ.filter (fun i : Fin (k n) => (i : ℕ) < m) := ⟨_, fun _ => rfl⟩
  have hS0 : S 0 = ∅ := by rw [hS]; ext j; simp
  have hSfull : S (k n) = Finset.univ := by rw [hS]; ext j; simpa using j.isLt
  have hSins : ∀ (m : ℕ) (hm : m < k n),
      S (m + 1) = insert (⟨m, hm⟩ : Fin (k n)) (S m) := by
    intro m hm
    rw [hS, hS]
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | hj'
      · exact Or.inr hj'
      · exact Or.inl (Fin.ext hj')
    · rintro (rfl | hj)
      · simp
      · omega
  have hSnotmem : ∀ (m : ℕ) (hm : m < k n), (⟨m, hm⟩ : Fin (k n)) ∉ S m := by
    intro m hm
    rw [hS]; simp
  -- (2) the cumulative reweighted product
  obtain ⟨P, hP⟩ : ∃ P : ℕ → Ω → ℂ, ∀ m ω, P m ω =
      ∏ j ∈ S m, (Complex.exp (I * ((u * X n j ω : ℝ) : ℂ))
        * (1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω : ℂ)⁻¹) :=
    ⟨_, fun _ _ => rfl⟩
  have hψcast : ∀ (j : Fin (k n)) (ω : Ω),
      (1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω : ℂ)
        = ((1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω : ℝ) : ℂ) := by
    intro j ω; push_cast; ring
  have hnormP : ∀ᵐ ω ∂μ, ∀ m : ℕ, ‖P m ω‖ ≤ Real.exp (u ^ 2 * c) := by
    filter_upwards [hae] with ω hω m
    obtain ⟨hfac, hsum⟩ := hω
    rw [hP m ω, norm_prod]
    have hstep : ∀ j ∈ S m, ‖Complex.exp (I * ((u * X n j ω : ℝ) : ℂ))
        * (1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω : ℂ)⁻¹‖
        = (1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω : ℝ)⁻¹ := by
      intro j _
      rw [norm_mul, Complex.norm_exp]
      have h1 : (I * ((u * X n j ω : ℝ) : ℂ)).re = 0 := by simp
      rw [h1, Real.exp_zero, one_mul, hψcast j ω, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith [(hfac j).2] : (0:ℝ) <
          1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω)]
    rw [Finset.prod_congr rfl hstep]
    exact prod_inv_one_sub_le_exp (fun j => (hfac j).1) (fun j => (hfac j).2) hsum (S m)
  have hPmeas : ∀ (m : ℕ) (hm : m < k n),
      Measurable[F n (⟨m, hm⟩ : Fin (k n)).castSucc] (P m) := by
    intro m hm
    have he : P m = fun ω => ∏ j ∈ S m, (Complex.exp (I * ((u * X n j ω : ℝ) : ℂ))
        * (1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω : ℂ)⁻¹) := funext (hP m)
    rw [he]
    refine Finset.measurable_prod _ fun j hj => ?_
    have hjm : (j : ℕ) < m := by rw [hS] at hj; simpa using hj
    have hle1 : F n j.succ ≤ F n (⟨m, hm⟩ : Fin (k n)).castSucc :=
      h.mono n (by rw [Fin.le_def]; simp [Fin.val_succ]; omega)
    have hle2 : F n j.castSucc ≤ F n (⟨m, hm⟩ : Fin (k n)).castSucc :=
      h.mono n (by rw [Fin.le_def]; simp; omega)
    have hXj : Measurable[F n (⟨m, hm⟩ : Fin (k n)).castSucc] (X n j) :=
      (h.adapted n j).mono hle1 le_rfl
    have hvj : Measurable[F n (⟨m, hm⟩ : Fin (k n)).castSucc]
        (μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc]) :=
      (stronglyMeasurable_condExp.measurable).mono hle2 le_rfl
    exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hXj)).const_mul I)).mul
      ((measurable_const.sub ((Complex.measurable_ofReal.comp hvj).const_mul _)).inv)
  -- (3) integrability of the cumulative products
  have hPint : ∀ m : ℕ, Integrable (P m) μ := by
    intro m
    have hmeas : Measurable (P m) := by
      have he : P m = fun ω => ∏ j ∈ S m, (Complex.exp (I * ((u * X n j ω : ℝ) : ℂ))
          * (1 - u ^ 2 / 2 * μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc] ω : ℂ)⁻¹) := funext (hP m)
      rw [he]
      refine Finset.measurable_prod _ fun j _ => ?_
      have hXj : Measurable (X n j) := (h.adapted n j).mono (h.le_ambient n _) le_rfl
      have hvj : Measurable (μ[fun ω' => X n j ω' ^ 2 | F n j.castSucc]) :=
        (stronglyMeasurable_condExp.measurable).mono (h.le_ambient n _) le_rfl
      exact (Complex.measurable_exp.comp
        ((Complex.measurable_ofReal.comp (measurable_const.mul hXj)).const_mul I)).mul
        ((measurable_const.sub ((Complex.measurable_ofReal.comp hvj).const_mul _)).inv)
    refine Integrable.mono' (integrable_const (Real.exp (u ^ 2 * c)))
      hmeas.aestronglyMeasurable ?_
    filter_upwards [hnormP] with ω hω
    exact hω m
  -- (4) one telescope step
  have hstep : ∀ (m : ℕ) (hm : m < k n),
      ‖(∫ ω, P (m + 1) ω ∂μ) - ∫ ω, P m ω ∂μ‖
        ≤ 2 * Real.exp (u ^ 2 * c)
          * (u ^ 2 * ∫ ω, X n (⟨m, hm⟩ : Fin (k n)) ω ^ 2 *
              Set.indicator {x : Ω | ε ≤ |X n (⟨m, hm⟩ : Fin (k n)) x|}
                (fun _ => (1 : ℝ)) ω ∂μ
            + |u| ^ 3 * ε * ∫ ω, X n (⟨m, hm⟩ : Fin (k n)) ω ^ 2 ∂μ) := by
    intro m hm
    set i : Fin (k n) := ⟨m, hm⟩ with hidef
    obtain ⟨Y, hY⟩ : ∃ Y : Ω → ℂ, ∀ ω, Y ω = P m ω *
        (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹ := ⟨_, fun _ => rfl⟩
    have hYm : StronglyMeasurable[F n i.castSucc] Y := by
      have he : Y = fun ω => P m ω *
          (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹ := funext hY
      rw [he]
      refine Measurable.stronglyMeasurable ?_
      exact (hPmeas m hm).mul
        ((measurable_const.sub ((Complex.measurable_ofReal.comp
          (stronglyMeasurable_condExp.measurable)).const_mul _)).inv)
    have hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ 2 * Real.exp (u ^ 2 * c) := by
      filter_upwards [hae, hnormP] with ω hω hnp
      obtain ⟨hfac, -⟩ := hω
      rw [hY ω, norm_mul, hψcast i ω, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [(hfac i).2] : (0:ℝ) <
          1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)]
      have hinv : (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℝ)⁻¹ ≤ 2 := by
        rw [inv_eq_one_div, div_le_iff₀ (by linarith [(hfac i).2])]
        linarith [(hfac i).1, (hfac i).2, mul_nonneg (by positivity : (0:ℝ) ≤ u ^ 2 / 2)
          (hfac i).1]
      have h0 : (0:ℝ) ≤ Real.exp (u ^ 2 * c) := (Real.exp_pos _).le
      have hPn := hnp m
      nlinarith [norm_nonneg (P m ω), inv_nonneg.2 (le_of_lt (by linarith [(hfac i).2] :
        (0:ℝ) < 1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω))]
    have hdiff : ∀ᵐ ω ∂μ, P (m + 1) ω - P m ω
        = Y ω * (Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
          - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) := by
      filter_upwards [hae] with ω hω
      obtain ⟨hfac, -⟩ := hω
      have hne : (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ) ≠ 0 := by
        rw [hψcast i ω, Ne, Complex.ofReal_eq_zero]
        linarith [(hfac i).2]
      rw [hP (m + 1) ω, hSins m hm, Finset.prod_insert (hSnotmem m hm), ← hP m ω, hY ω]
      -- with `A = P m ω`, `E = e^{iuX_i}`, `B = ψ_i`: `E·B⁻¹·A − A = A·B⁻¹·(E − B)`
      have key : ∀ A E B : ℂ, B ≠ 0 → E * B⁻¹ * A - A = A * B⁻¹ * (E - B) := by
        intro A E B hB
        field_simp
      exact key _ _ _ hne
    have hint : (∫ ω, P (m + 1) ω ∂μ) - ∫ ω, P m ω ∂μ
        = ∫ ω, Y ω * (Complex.exp (I * ((u * X n i ω : ℝ) : ℂ))
          - (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) ∂μ := by
      rw [← integral_sub (hPint (m + 1)) (hPint m)]
      exact integral_congr_ae hdiff
    rw [hint]
    exact norm_integral_mul_cexp_sub_taylor_le h n i u hε hYm hYb
  -- (5) telescope
  have htel : ∀ m : ℕ, m ≤ k n →
      ‖(∫ ω, P m ω ∂μ) - 1‖ ≤ ∑ j ∈ Finset.range m, (if hj : j < k n then
        2 * Real.exp (u ^ 2 * c)
          * (u ^ 2 * ∫ ω, X n (⟨j, hj⟩ : Fin (k n)) ω ^ 2 *
              Set.indicator {x : Ω | ε ≤ |X n (⟨j, hj⟩ : Fin (k n)) x|}
                (fun _ => (1 : ℝ)) ω ∂μ
            + |u| ^ 3 * ε * ∫ ω, X n (⟨j, hj⟩ : Fin (k n)) ω ^ 2 ∂μ) else 0) := by
    intro m
    induction m with
    | zero =>
      intro _
      have h0 : (∫ ω, P 0 ω ∂μ) = 1 := by
        have he : ∀ ω, P 0 ω = 1 := fun ω => by rw [hP 0 ω, hS0, Finset.prod_empty]
        rw [integral_congr_ae (ae_of_all _ he)]
        simp
      simp [h0]
    | succ m ih =>
      intro hm
      have hm' : m < k n := hm
      have hmle : m ≤ k n := le_of_lt hm'
      have h1 := ih hmle
      have h2 := hstep m hm'
      rw [Finset.sum_range_succ]
      have hsplit : (∫ ω, P (m + 1) ω ∂μ) - 1
          = ((∫ ω, P (m + 1) ω ∂μ) - ∫ ω, P m ω ∂μ) + ((∫ ω, P m ω ∂μ) - 1) := by ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [dif_pos hm']
      linarith
  -- (6) identify the endpoint
  have hend : ∀ ω, P (k n) ω = Complex.exp (I * ((u * mdsRowSum k X n ω : ℝ) : ℂ))
      * ∏ i, (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹ := by
    intro ω
    rw [hP (k n) ω, hSfull, Finset.prod_mul_distrib]
    congr 1
    rw [← Complex.exp_sum]
    congr 1
    rw [mdsRowSum]
    push_cast
    rw [Finset.mul_sum]
    exact (Finset.mul_sum _ _ _).symm
  have hfinal := htel (k n) le_rfl
  rw [integral_congr_ae (ae_of_all _ hend)] at hfinal
  refine hfinal.trans (le_of_eq ?_)
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun j => (if hj : j < k n then
    2 * Real.exp (u ^ 2 * c)
      * (u ^ 2 * ∫ ω, X n (⟨j, hj⟩ : Fin (k n)) ω ^ 2 *
          Set.indicator {x : Ω | ε ≤ |X n (⟨j, hj⟩ : Fin (k n)) x|}
            (fun _ => (1 : ℝ)) ω ∂μ
        + |u| ^ 3 * ε * ∫ ω, X n (⟨j, hj⟩ : Fin (k n)) ω ^ 2 ∂μ) else 0)) (k n)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos i.isLt]
  simp only [Fin.eta]
  ring

/-- **`L¹` product comparison**: if the conditional variance process converges to `σ²` in
probability and the individual conditional variances are uniformly asymptotically
negligible, the Taylor product converges to the Gaussian factor **in `L¹`**.

The `L¹` form (rather than the convergence-in-mean form
`tendsto_integral_prod_one_sub_condVar` below, which it implies) is what the
nesting-free telescope needs: the telescope controls `E[e^{iuS_n}∏ᵢψᵢ⁻¹] − 1`, and
converting that into `E e^{iuS_n} − e^{−u²σ²/2}` costs one pointwise multiplication by
the *random* weight `∏ᵢψᵢ` — see `norm_integral_exp_rowSum_sub_gaussian_le`. -/
theorem tendsto_integral_abs_prod_one_sub_condVar_sub [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: conditional variance → σ² in probability; Brown's condition
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: uniform asymptotic negligibility of the conditional variances
    (hunif : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | ∃ i, δ ≤ μ[fun ω' => X n i ω' ^ 2
          | F n i.castSucc] ω}).toReal) atTop (𝓝 0))
    -- LEAN-ONLY (repair, 2026-08-05): pointwise clamp on the conditional variance
    -- PROCESS (supplied by the Hall–Heyde truncated array, whose variance process is
    -- bounded by the truncation level); an `L¹` bound on `V_n` does NOT suffice and what
    -- makes the Taylor product uniformly bounded — see the witness recorded below.
    {c : ℝ} (hclamp : ∀ n, ∀ᵐ ω ∂μ, mdsCondVariance k X F μ n ω ≤ c)
    (u : ℝ) :
    Tendsto (fun n => ∫ ω, |(∏ i, (1 - u ^ 2 / 2 *
          μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω))
        - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ) atTop (𝓝 0) := by
  -- DEBT (wave 2): FALSE as frozen, with an explicit witness — REPAIRED 2026-08-05 by
  -- the `hclamp` hypothesis (a pointwise bound on the conditional variance PROCESS).
  -- `hbdd` (an L¹ bound on `V_n`) does not rule out mass escape, because the factors
  -- `1 - u²v/2` are NOT bounded by 1: a single index with `v ≈ 1/p` on an event of
  -- probability `p` contributes `p · u²/(2p) = u²/2` to the integral while carrying
  -- `L¹`-mass 1 and vanishing in probability.
  --
  -- WITNESS.  `Ω = [0,1) × {-1,1}`, `μ = volume × uniform`, `ξ ω = ω.2`,
  -- `p_n = 1/(n+2)`, `A_n = [0,p_n) × {-1,1}`; `k n = 2`,
  -- `F n 0 = ⊥`, `F n 1 = σ(A_n)`, `F n 2 = ⊤`, and
  --   `X n 0 = (1 - p_n)·1_{A_n} - p_n·1_{A_nᶜ}`,  `X n 1 = p_n^{-1/2}·ξ·1_{A_n}`.
  -- This is an `IsMDSArray` (`E[X n 0] = 0`; `E[X n 1|F n 1] = 0` since `ξ ⟂ A_n`), with
  --   `v_{n,0} = p_n(1-p_n)`,  `v_{n,1} = p_n^{-1}·1_{A_n}`,  `V_n = p_n(1-p_n) + p_n^{-1}1_{A_n}`.
  -- Then `∫V_n = p_n(1-p_n) + 1 ≤ 2` (`hbdd`, B = 2); `V_n →p 0` (`hvar`, σ² = 0, since
  -- `μ(A_n) = p_n → 0`); `μ{∃i, δ ≤ v_{n,i}} ≤ p_n + [p_n(1-p_n) ≥ δ] → 0` (`hunif`).
  -- But
  --   `∫ ∏_i (1 - u²v_{n,i}/2) = (1 - u²p_n(1-p_n)/2)·(1 - (u²/(2p_n))·μ(A_n))`
  --                            = `(1 - u²p_n(1-p_n)/2)(1 - u²/2) → 1 - u²/2`,
  -- whereas the claimed limit is `exp(-u²·0/2) = 1`.  These differ for every `u ≠ 0`.
  -- (Note `V_n = p_n^{-1}` on `A_n`, so this witness violates `hclamp` for every `c`.)
  --
  -- REPAIR APPLIED: `hclamp` gives `‖∏ᵢ(1 - u²vᵢ/2)‖ ≤ e^{u²c/2}` pointwise
  -- (`abs_prod_one_sub_le_exp`), which is exactly the domination the witness destroys.
  -- The proof is then a plain `ε`-argument: on the event where every `vᵢ ≤ β` and
  -- `|V_n - σ²| ≤ β` the product is within `βM` of `e^{-u²σ²/2}`
  -- (`abs_prod_one_sub_sub_exp_le`), and the complementary event has vanishing measure
  -- by `hvar` and `hunif`.  Note the argument does not use `hbdd`, which `hclamp`
  -- subsumes; `hbdd` is kept so that the frozen call sites are unaffected.
  classical
  obtain ⟨p, hp⟩ : ∃ p : ℕ → Ω → ℝ, ∀ (n : ℕ) (ω : Ω), p n ω =
      ∏ i, (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) :=
    ⟨_, fun _ _ => rfl⟩
  have hvmeas : ∀ (n : ℕ) (i : Fin (k n)),
      Measurable (μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc]) := fun n i =>
    (stronglyMeasurable_condExp.measurable).mono (h.le_ambient n i.castSucc) le_rfl
  have hv0 : ∀ n : ℕ, ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
      0 ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω :=
    fun n => ae_all_iff.2 fun i => condExp_nonneg (ae_of_all _ fun _ => sq_nonneg _)
  have hVsum : ∀ (n : ℕ) (ω : Ω),
      (∑ i, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) = mdsCondVariance k X F μ n ω :=
    fun _ _ => rfl
  have hVmeas : ∀ n, Measurable (mdsCondVariance k X F μ n) := fun n =>
    Finset.measurable_sum _ fun i _ => hvmeas n i
  have hpmeas : ∀ n, Measurable (p n) := by
    intro n
    have he : p n = fun ω => ∏ i, (1 - u ^ 2 / 2 *
        μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) := funext (hp n)
    rw [he]
    exact Finset.measurable_prod _ fun i _ => measurable_const.sub ((hvmeas n i).const_mul _)
  have hpbdd : ∀ n, ∀ᵐ ω ∂μ, |p n ω| ≤ Real.exp (u ^ 2 * c / 2) := by
    intro n
    filter_upwards [hv0 n, hclamp n] with ω h1 h2
    rw [hp n ω]
    exact abs_prod_one_sub_le_exp h1 (by rw [hVsum]; exact h2)
  have hpint : ∀ n, Integrable (p n) μ := by
    intro n
    refine Integrable.mono' (integrable_const (Real.exp (u ^ 2 * c / 2)))
      (hpmeas n).aestronglyMeasurable ?_
    filter_upwards [hpbdd n] with ω hω
    rwa [Real.norm_eq_abs]
  -- the `L¹` limit, stated through the opaque abbreviation `p`
  have main : Tendsto (fun n => ∫ ω, |p n ω - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ)
      atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨M, hM0, hMdef⟩ : ∃ M : ℝ, 0 ≤ M ∧ M = u ^ 2 * u ^ 2 * (σ2 + 1) / 4 + u ^ 2 / 2 := by
      refine ⟨_, ?_, rfl⟩
      have h1 : (0:ℝ) ≤ u ^ 2 * u ^ 2 * (σ2 + 1) :=
        mul_nonneg (mul_nonneg (sq_nonneg u) (sq_nonneg u)) (by linarith)
      have h2 : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
      linarith
    obtain ⟨T, hT0, hTdef⟩ : ∃ T : ℝ, 0 < T ∧ T = Real.exp (u ^ 2 * c / 2) + 1 :=
      ⟨_, by positivity, rfl⟩
    obtain ⟨β, hβpos, hβ1, hβu, hβM⟩ : ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ u ^ 2 * β ≤ 1
        ∧ M * β ≤ η / 4 := by
      refine ⟨min 1 (min (1 / (u ^ 2 + 1)) ((η / 4) / (M + 1))), ?_, min_le_left _ _, ?_, ?_⟩
      · have h1 : (0:ℝ) < 1 / (u ^ 2 + 1) := by positivity
        have h2 : (0:ℝ) < (η / 4) / (M + 1) := by
          have : (0:ℝ) < M + 1 := by linarith
          positivity
        exact lt_min one_pos (lt_min h1 h2)
      · have hle : min 1 (min (1 / (u ^ 2 + 1)) ((η / 4) / (M + 1))) ≤ 1 / (u ^ 2 + 1) :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        have hu2 : (0:ℝ) < u ^ 2 + 1 := by positivity
        have := mul_le_mul_of_nonneg_left hle (sq_nonneg u)
        rw [mul_one_div] at this
        have hdiv : u ^ 2 / (u ^ 2 + 1) ≤ 1 := by
          rw [div_le_one hu2]; linarith
        linarith
      · have hle : min 1 (min (1 / (u ^ 2 + 1)) ((η / 4) / (M + 1))) ≤ (η / 4) / (M + 1) :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        have hM1 : (0:ℝ) < M + 1 := by linarith
        have := mul_le_mul_of_nonneg_left hle hM0
        refine this.trans ?_
        rw [mul_div_assoc'] at *
        rw [div_le_iff₀ hM1]
        nlinarith [hη.le]
    -- the exceptional event
    obtain ⟨θ, hθpos, hθdef⟩ : ∃ θ : ℝ, 0 < θ ∧ θ = η / (8 * T) := ⟨_, by positivity, rfl⟩
    have e1 := (hvar β hβpos).eventually (gt_mem_nhds hθpos)
    have e2 := (hunif β hβpos).eventually (gt_mem_nhds hθpos)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (e1.and e2)
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨hn1, hn2⟩ := hN n hn
    obtain ⟨A, hAdef⟩ : ∃ A : Set Ω, A = {ω | β ≤ |mdsCondVariance k X F μ n ω - σ2|}
        ∪ {ω | ∃ i, β ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω} := ⟨_, rfl⟩
    have hA : MeasurableSet A := by
      rw [hAdef]
      refine MeasurableSet.union
        (measurableSet_le measurable_const
          (continuous_abs.measurable.comp ((hVmeas n).sub measurable_const))) ?_
      have hEq : {ω | ∃ i, β ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω}
          = ⋃ i, {ω | β ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω} := by
        ext ω; simp
      rw [hEq]
      exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (hvmeas n i)
    have hmajor : ∀ᵐ ω ∂μ, |p n ω - Real.exp (-(u ^ 2 * σ2 / 2))|
        ≤ M * β + T * Set.indicator A (fun _ => (1:ℝ)) ω := by
      filter_upwards [hv0 n, hpbdd n] with ω hnn hbd
      by_cases hωA : ω ∈ A
      · rw [Set.indicator_of_mem hωA]
        have h1 : |p n ω - Real.exp (-(u ^ 2 * σ2 / 2))|
            ≤ |p n ω| + |Real.exp (-(u ^ 2 * σ2 / 2))| := abs_sub _ _
        have h2 : |Real.exp (-(u ^ 2 * σ2 / 2))| ≤ 1 := by
          rw [abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])
        have h3 : (0:ℝ) ≤ M * β := mul_nonneg hM0 hβpos.le
        rw [hTdef]
        linarith
      · have hnotA : ω ∉ {ω | β ≤ |mdsCondVariance k X F μ n ω - σ2|}
            ∧ ω ∉ {ω | ∃ i, β ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω} := by
          rw [hAdef] at hωA
          exact ⟨fun hc => hωA (Or.inl hc), fun hc => hωA (Or.inr hc)⟩
        have hvb : ∀ i, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω ≤ β := by
          intro i
          by_contra hc
          exact hnotA.2 ⟨i, le_of_lt (lt_of_not_ge hc)⟩
        have hsum : |(∑ i, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) - σ2| ≤ β := by
          rw [hVsum]
          exact le_of_lt (lt_of_not_ge hnotA.1)
        rw [Set.indicator_of_notMem hωA, hp n ω]
        have hkey := abs_prod_one_sub_sub_exp_le hnn hvb hβpos.le hβu hσ hsum
        have hσβ : σ2 + β ≤ σ2 + 1 := by linarith
        have hu2 : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
        have hbb : u ^ 2 * β / 2 * (u ^ 2 * (σ2 + β) / 2) + u ^ 2 * β / 2 ≤ M * β := by
          rw [hMdef]
          nlinarith [mul_nonneg hu2 hβpos.le, mul_nonneg (mul_nonneg hu2 hu2) hβpos.le]
        have hT1 : (0:ℝ) ≤ T := hT0.le
        linarith
    -- integrate the majorant
    have hint1 : Integrable (fun ω => |p n ω - Real.exp (-(u ^ 2 * σ2 / 2))|) μ :=
      ((hpint n).sub (integrable_const _)).abs
    have hint2 : Integrable
        (fun ω => M * β + T * Set.indicator A (fun _ => (1:ℝ)) ω) μ :=
      (integrable_const _).add (((integrable_const (1:ℝ)).indicator hA).const_mul _)
    have hstep : ∫ ω, |p n ω - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ ≤ M * β + T * μ.real A := by
      refine le_trans (integral_mono_ae hint1 hint2 hmajor) (le_of_eq ?_)
      rw [integral_add (integrable_const _) (((integrable_const (1:ℝ)).indicator hA).const_mul _),
        integral_const, integral_const_mul, integral_indicator_const _ hA]
      simp
    have hAmeas : μ.real A ≤ (μ {ω | β ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal
        + (μ {ω | ∃ i, β ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω}).toReal := by
      rw [hAdef, measureReal_def]
      refine le_trans (ENNReal.toReal_mono ?_ (measure_union_le _ _)) (le_of_eq ?_)
      · exact ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩
      · exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
    have hnn : (0:ℝ) ≤ ∫ ω, |p n ω - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ :=
      integral_nonneg fun ω => abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
    have hfin : T * μ.real A ≤ T * (2 * θ) := by
      have : μ.real A ≤ 2 * θ := by
        have := hAmeas
        rw [measureReal_def] at this ⊢
        linarith
      exact mul_le_mul_of_nonneg_left this hT0.le
    have hθval : T * (2 * θ) = η / 4 := by
      rw [hθdef]; field_simp; ring
    have hMβ : M * β ≤ η / 4 := hβM
    linarith [hstep]
  -- unfold the opaque abbreviation
  exact main.congr fun n => integral_congr_ae (ae_of_all _ fun ω => by rw [hp n ω])

/-- **Product comparison**: if the conditional variance process converges to `σ²` in
probability and the individual conditional variances are uniformly asymptotically
negligible, the Taylor product converges to the Gaussian factor.  This is the
convergence-in-mean shadow of `tendsto_integral_abs_prod_one_sub_condVar_sub`. -/
theorem tendsto_integral_prod_one_sub_condVar [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) {σ2 : ℝ} (hσ : 0 ≤ σ2)
    -- USER-INPUT: conditional variance → σ² in probability; Brown's condition
    (hvar : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | δ ≤ |mdsCondVariance k X F μ n ω - σ2|}).toReal)
        atTop (𝓝 0))
    -- USER-INPUT: uniform asymptotic negligibility of the conditional variances
    (hunif : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun n => (μ {ω | ∃ i, δ ≤ μ[fun ω' => X n i ω' ^ 2
          | F n i.castSucc] ω}).toReal) atTop (𝓝 0))
    -- LEAN-ONLY: a uniform L¹ bound on the variance process.  Unused (the pointwise
    -- clamp `hclamp` subsumes it); retained so that the frozen call sites are unaffected.
    (_hbdd : ∃ B : ℝ, ∀ n, ∫ ω, mdsCondVariance k X F μ n ω ∂μ ≤ B)
    -- LEAN-ONLY (repair, 2026-08-05): pointwise clamp on the conditional variance PROCESS
    {c : ℝ} (hclamp : ∀ n, ∀ᵐ ω ∂μ, mdsCondVariance k X F μ n ω ≤ c)
    (u : ℝ) :
    Tendsto (fun n => ∫ ω, ∏ i, (1 - (u ^ 2 / 2 : ℂ) *
        (μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℝ)) ∂μ) atTop
      (𝓝 (Complex.exp (-(u ^ 2 * σ2 / 2 : ℝ)))) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p : ℕ → Ω → ℝ, ∀ (n : ℕ) (ω : Ω), p n ω =
      ∏ i, (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) :=
    ⟨_, fun _ _ => rfl⟩
  have hvmeas : ∀ (n : ℕ) (i : Fin (k n)),
      Measurable (μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc]) := fun n i =>
    (stronglyMeasurable_condExp.measurable).mono (h.le_ambient n i.castSucc) le_rfl
  have hv0 : ∀ n : ℕ, ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
      0 ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω :=
    fun n => ae_all_iff.2 fun i => condExp_nonneg (ae_of_all _ fun _ => sq_nonneg _)
  have hVsum : ∀ (n : ℕ) (ω : Ω),
      (∑ i, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) = mdsCondVariance k X F μ n ω :=
    fun _ _ => rfl
  have hpmeas : ∀ n, Measurable (p n) := by
    intro n
    have he : p n = fun ω => ∏ i, (1 - u ^ 2 / 2 *
        μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) := funext (hp n)
    rw [he]
    exact Finset.measurable_prod _ fun i _ => measurable_const.sub ((hvmeas n i).const_mul _)
  have hpbdd : ∀ n, ∀ᵐ ω ∂μ, |p n ω| ≤ Real.exp (u ^ 2 * c / 2) := by
    intro n
    filter_upwards [hv0 n, hclamp n] with ω h1 h2
    rw [hp n ω]
    exact abs_prod_one_sub_le_exp h1 (by rw [hVsum]; exact h2)
  have hpint : ∀ n, Integrable (p n) μ := by
    intro n
    refine Integrable.mono' (integrable_const (Real.exp (u ^ 2 * c / 2)))
      (hpmeas n).aestronglyMeasurable ?_
    filter_upwards [hpbdd n] with ω hω
    rwa [Real.norm_eq_abs]
  have hL1 := tendsto_integral_abs_prod_one_sub_condVar_sub h hσ hvar hunif hclamp u
  have main : Tendsto (fun n => ∫ ω, p n ω ∂μ) atTop
      (𝓝 (Real.exp (-(u ^ 2 * σ2 / 2)))) := by
    rw [Metric.tendsto_atTop] at hL1 ⊢
    intro η hη
    obtain ⟨N, hN⟩ := hL1 η hη
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have heq : (∫ ω, |(∏ i, (1 - u ^ 2 / 2 *
          μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω))
          - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ)
        = ∫ ω, |p n ω - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by simp only [hp n ω])
    rw [Real.dist_eq, sub_zero, heq,
      abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)] at h1
    rw [Real.dist_eq]
    refine lt_of_le_of_lt ?_ h1
    have hsub : (∫ ω, p n ω ∂μ) - Real.exp (-(u ^ 2 * σ2 / 2))
        = ∫ ω, (p n ω - Real.exp (-(u ^ 2 * σ2 / 2))) ∂μ := by
      rw [integral_sub (hpint n) (integrable_const _), integral_const]
      simp
    rw [hsub]
    have := norm_integral_le_integral_norm
      (μ := μ) (f := fun ω => p n ω - Real.exp (-(u ^ 2 * σ2 / 2)))
    simpa only [Real.norm_eq_abs] using this
  -- transfer to the complex statement
  have hcast : ∀ n : ℕ, (∫ ω, ∏ i, (1 - (u ^ 2 / 2 : ℂ) * (μ[fun ω' => X n i ω' ^ 2
      | F n i.castSucc] ω : ℝ)) ∂μ) = ((∫ ω, p n ω ∂μ : ℝ) : ℂ) := by
    intro n
    have hpt : ∀ ω, (∏ i, (1 - (u ^ 2 / 2 : ℂ) * (μ[fun ω' => X n i ω' ^ 2
        | F n i.castSucc] ω : ℝ))) = ((p n ω : ℝ) : ℂ) := by
      intro ω
      rw [hp n ω, Complex.ofReal_prod]
      exact Finset.prod_congr rfl fun i _ => by push_cast; ring
    simp_rw [hpt]
    exact integral_complex_ofReal
  have hgauss : Complex.exp (-(u ^ 2 * σ2 / 2 : ℝ))
      = ((Real.exp (-(u ^ 2 * σ2 / 2)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hgauss]
  refine Tendsto.congr (fun n => (hcast n).symm) ?_
  exact (Complex.continuous_ofReal.tendsto _).comp main

open Complex in
/-- **The comparison `mds_clt` consumes.**  Combining the nesting-free telescope
`norm_integral_exp_rowSum_mul_invProd_sub_one_le` with the `L¹` distance of the Taylor
product `Π = ∏ᵢ(1 − u²vᵢ/2)` from the Gaussian factor `γ = e^{−u²σ²/2}` bounds
`‖E e^{iuS_n} − γ‖` directly.

The algebra is the exact identity
`e^{iuS} − γ = e^{iuS}·(1 − γΠ⁻¹) + γ·(e^{iuS}Π⁻¹ − 1)`.
The second summand is the telescope (times `γ ≤ 1`).  The first is pointwise
`‖1 − γΠ⁻¹‖ = |Π − γ|·‖Π⁻¹‖ ≤ e^{u²c}|Π − γ|`, using `Π·Π⁻¹ = 1`, which is where the
clamps `hd`/`hdu` are needed: they put every factor in `[1/2, 1]`, so `Π` never
vanishes and `Π⁻¹` is dominated by `e^{u²c}` (`prod_inv_one_sub_le_exp`). -/
theorem norm_integral_exp_rowSum_sub_gaussian_le [IsProbabilityMeasure μ]
    {k : ℕ → ℕ} {X : (n : ℕ) → Fin (k n) → Ω → ℝ}
    {F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω}
    (h : IsMDSArray k X F μ) (n : ℕ) (u : ℝ) {ε : ℝ} (hε : 0 < ε) {c d σ2 : ℝ}
    (hσ : 0 ≤ σ2)
    -- LEAN-ONLY: per-index clamp making every Taylor factor lie in `[1/2, 1]`
    (hd : ∀ i, ∀ᵐ ω ∂μ, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω ≤ d)
    (hdu : u ^ 2 * d ≤ 1)
    -- LEAN-ONLY: clamp on the conditional variance process
    (hc : ∀ᵐ ω ∂μ, mdsCondVariance k X F μ n ω ≤ c) :
    ‖(∫ ω, Complex.exp (I * ((u * mdsRowSum k X n ω : ℝ) : ℂ)) ∂μ)
        - ((Real.exp (-(u ^ 2 * σ2 / 2)) : ℝ) : ℂ)‖
      ≤ Real.exp (u ^ 2 * c) * ∫ ω, |(∏ i, (1 - u ^ 2 / 2 *
            μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω))
          - Real.exp (-(u ^ 2 * σ2 / 2))| ∂μ
        + 2 * Real.exp (u ^ 2 * c)
            * (∑ i, (u ^ 2 * ∫ ω, X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
                  (fun _ => (1 : ℝ)) ω ∂μ) + ∑ i, (|u| ^ 3 * ε * ∫ ω, X n i ω ^ 2 ∂μ)) := by
  classical
  have hu2 : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
  set γ : ℝ := Real.exp (-(u ^ 2 * σ2 / 2)) with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; exact Real.exp_pos _
  have hγ1 : γ ≤ 1 := by
    rw [hγdef]
    exact Real.exp_le_one_iff.2 (by nlinarith)
  -- (0) pointwise control of the Taylor factors (as in the telescope)
  have hae : ∀ᵐ ω ∂μ, (∀ i : Fin (k n),
        0 ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω
          ∧ u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω ≤ 1 / 2)
      ∧ mdsCondVariance k X F μ n ω ≤ c := by
    have h1 : ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
        0 ≤ μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω :=
      ae_all_iff.2 fun i => condExp_nonneg (ae_of_all _ fun _ => sq_nonneg _)
    have h2 : ∀ᵐ ω ∂μ, ∀ i : Fin (k n),
        μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω ≤ d := ae_all_iff.2 hd
    filter_upwards [h1, h2, hc] with ω e1 e2 e3
    refine ⟨fun i => ⟨e1 i, ?_⟩, e3⟩
    have := mul_le_mul_of_nonneg_left (e2 i) (by positivity : (0:ℝ) ≤ u ^ 2 / 2)
    nlinarith [e1 i]
  have hψcast : ∀ (i : Fin (k n)) (ω : Ω),
      (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)
        = ((1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℝ) : ℂ) := by
    intro i ω; push_cast; ring
  -- (1) the three players
  obtain ⟨E, hE⟩ : ∃ E : Ω → ℂ, ∀ ω,
      E ω = Complex.exp (I * ((u * mdsRowSum k X n ω : ℝ) : ℂ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Ω → ℝ, ∀ ω, Ψ ω =
      ∏ i, (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Ω → ℂ, ∀ ω, Q ω =
      ∏ i, (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hvmeas : ∀ i : Fin (k n),
      Measurable (μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc]) := fun i =>
    (stronglyMeasurable_condExp.measurable).mono (h.le_ambient n i.castSucc) le_rfl
  have hEmeas : Measurable E := by
    have he : E = fun ω => Complex.exp (I * ((u * mdsRowSum k X n ω : ℝ) : ℂ)) := funext hE
    rw [he]
    have hS : Measurable (mdsRowSum k X n) :=
      Finset.measurable_sum _ fun i _ => (h.adapted n i).mono (h.le_ambient n _) le_rfl
    exact Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (measurable_const.mul hS)).const_mul I)
  have hΨmeas : Measurable Ψ := by
    have he : Ψ = fun ω => ∏ i, (1 - u ^ 2 / 2 *
        μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω) := funext hΨ
    rw [he]
    exact Finset.measurable_prod _ fun i _ => measurable_const.sub ((hvmeas i).const_mul _)
  have hQmeas : Measurable Q := by
    have he : Q = fun ω => ∏ i, (1 - u ^ 2 / 2 *
        μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹ := funext hQ
    rw [he]
    exact Finset.measurable_prod _ fun i _ =>
      (measurable_const.sub ((Complex.measurable_ofReal.comp (hvmeas i)).const_mul _)).inv
  have hE1 : ∀ ω, ‖E ω‖ = 1 := fun ω => by rw [hE ω, Complex.norm_exp]; simp
  -- (2) the inverse product is dominated, and inverts `Ψ`
  have hQb : ∀ᵐ ω ∂μ, ‖Q ω‖ ≤ Real.exp (u ^ 2 * c) := by
    filter_upwards [hae] with ω hω
    obtain ⟨hfac, hsum⟩ := hω
    rw [hQ ω, norm_prod]
    have hstep : ∀ i ∈ (Finset.univ : Finset (Fin (k n))),
        ‖(1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹‖
        = (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℝ)⁻¹ := by
      intro i _
      rw [hψcast i ω, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith [(hfac i).2] : (0:ℝ) <
          1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)]
    rw [Finset.prod_congr rfl hstep]
    exact prod_inv_one_sub_le_exp (fun i => (hfac i).1) (fun i => (hfac i).2) hsum Finset.univ
  have hΨQ : ∀ᵐ ω ∂μ, ((Ψ ω : ℝ) : ℂ) * Q ω = 1 := by
    filter_upwards [hae] with ω hω
    obtain ⟨hfac, -⟩ := hω
    rw [hΨ ω, hQ ω, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    have hne : (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ) ≠ 0 := by
      rw [hψcast i ω, Ne, Complex.ofReal_eq_zero]
      linarith [(hfac i).2]
    rw [← hψcast i ω]
    exact mul_inv_cancel₀ hne
  have hΨ1 : ∀ᵐ ω ∂μ, |Ψ ω| ≤ 1 := by
    filter_upwards [hae] with ω hω
    obtain ⟨hfac, -⟩ := hω
    rw [hΨ ω, Finset.abs_prod]
    refine Finset.prod_le_one (fun i _ => abs_nonneg _) fun i _ => ?_
    rw [abs_of_pos (by linarith [(hfac i).2] : (0:ℝ) <
      1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)]
    have := mul_nonneg (by positivity : (0:ℝ) ≤ u ^ 2 / 2) (hfac i).1
    linarith
  -- (3) integrability
  have hEint : Integrable E μ :=
    Integrable.mono' (integrable_const (1:ℝ)) hEmeas.aestronglyMeasurable
      (ae_of_all _ fun ω => le_of_eq (hE1 ω))
  have hEQint : Integrable (fun ω => E ω * Q ω) μ := by
    refine Integrable.mono' (integrable_const (Real.exp (u ^ 2 * c)))
      (hEmeas.mul hQmeas).aestronglyMeasurable ?_
    filter_upwards [hQb] with ω hω
    rw [norm_mul, hE1 ω, one_mul]
    exact hω
  have hΨγint : Integrable (fun ω => |Ψ ω - γ|) μ := by
    have hsubm : Measurable fun ω => Ψ ω - γ := hΨmeas.sub measurable_const
    have hmeas2 : Measurable fun ω => |Ψ ω - γ| := continuous_abs.measurable.comp hsubm
    refine Integrable.mono' (integrable_const (2:ℝ)) hmeas2.aestronglyMeasurable ?_
    filter_upwards [hΨ1] with ω hω
    rw [Real.norm_eq_abs, abs_abs]
    have h1 : |Ψ ω - γ| ≤ |Ψ ω| + |γ| := abs_sub _ _
    rw [abs_of_pos hγ0] at h1
    linarith
  have hmixint : Integrable (fun ω => E ω * (1 - (γ : ℂ) * Q ω)) μ := by
    have hfun : (fun ω => E ω * (1 - (γ : ℂ) * Q ω))
        = fun ω => E ω - (γ : ℂ) * (E ω * Q ω) := by funext ω; ring
    rw [hfun]
    exact hEint.sub (hEQint.const_mul _)
  -- (4) the identity
  have hsplit : (∫ ω, E ω ∂μ) - (γ : ℂ)
      = (∫ ω, E ω * (1 - (γ : ℂ) * Q ω) ∂μ) + (γ : ℂ) * ((∫ ω, E ω * Q ω ∂μ) - 1) := by
    have h1 : (∫ ω, E ω * (1 - (γ : ℂ) * Q ω) ∂μ)
        = (∫ ω, E ω ∂μ) - (γ : ℂ) * ∫ ω, E ω * Q ω ∂μ := by
      have hfun : (fun ω => E ω * (1 - (γ : ℂ) * Q ω))
          = fun ω => E ω - (γ : ℂ) * (E ω * Q ω) := by funext ω; ring
      rw [hfun, integral_sub hEint (hEQint.const_mul _)]
      congr 1
      exact integral_const_mul _ _
    rw [h1]; ring
  -- (5) fold the goal onto the abbreviations
  have hEgoal : (∫ ω, Complex.exp (I * ((u * mdsRowSum k X n ω : ℝ) : ℂ)) ∂μ)
      = ∫ ω, E ω ∂μ := integral_congr_ae (ae_of_all _ fun ω => (hE ω).symm)
  have hΨgoal : (∫ ω, |(∏ i, (1 - u ^ 2 / 2 *
        μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω)) - γ| ∂μ)
      = ∫ ω, |Ψ ω - γ| ∂μ :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only [hΨ ω])
  have hEQgoal : (∫ ω, Complex.exp (I * ((u * mdsRowSum k X n ω : ℝ) : ℂ))
        * ∏ i, (1 - u ^ 2 / 2 * μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω : ℂ)⁻¹ ∂μ)
      = ∫ ω, E ω * Q ω ∂μ :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only [hE ω, hQ ω])
  have htel := norm_integral_exp_rowSum_mul_invProd_sub_one_le h n u hε hd hdu hc
  rw [hEQgoal] at htel
  rw [hEgoal, hΨgoal, hsplit]
  refine (norm_add_le _ _).trans ?_
  -- (6) the two summands
  have hb1 : ‖∫ ω, E ω * (1 - (γ : ℂ) * Q ω) ∂μ‖
      ≤ Real.exp (u ^ 2 * c) * ∫ ω, |Ψ ω - γ| ∂μ := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ᵐ ω ∂μ, ‖E ω * (1 - (γ : ℂ) * Q ω)‖
        ≤ Real.exp (u ^ 2 * c) * |Ψ ω - γ| := by
      filter_upwards [hΨQ, hQb] with ω h1 h2
      have hid : (1 : ℂ) - (γ : ℂ) * Q ω = ((Ψ ω - γ : ℝ) : ℂ) * Q ω := by
        push_cast
        rw [sub_mul, h1]
      rw [norm_mul, hE1 ω, one_mul, hid, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |Ψ ω - γ| * ‖Q ω‖ ≤ |Ψ ω - γ| * Real.exp (u ^ 2 * c) :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ = Real.exp (u ^ 2 * c) * |Ψ ω - γ| := mul_comm _ _
    refine (integral_mono_ae hmixint.norm (hΨγint.const_mul _) hpt).trans (le_of_eq ?_)
    exact integral_const_mul _ _
  have hb2 : ‖(γ : ℂ) * ((∫ ω, E ω * Q ω ∂μ) - 1)‖
      ≤ 2 * Real.exp (u ^ 2 * c)
          * (∑ i, (u ^ 2 * ∫ ω, X n i ω ^ 2 * Set.indicator {x : Ω | ε ≤ |X n i x|}
                (fun _ => (1 : ℝ)) ω ∂μ) + ∑ i, (|u| ^ 3 * ε * ∫ ω, X n i ω ^ 2 ∂μ)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ0]
    calc γ * ‖(∫ ω, E ω * Q ω ∂μ) - 1‖ ≤ 1 * ‖(∫ ω, E ω * Q ω ∂μ) - 1‖ :=
          mul_le_mul_of_nonneg_right hγ1 (norm_nonneg _)
      _ = ‖(∫ ω, E ω * Q ω ∂μ) - 1‖ := one_mul _
      _ ≤ _ := htel
  linarith

end Arrays

end StatLean.TimeSeries
