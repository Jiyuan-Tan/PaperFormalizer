module
public import StatLean.CausalInference.IV.LATE
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-!
# Linear instrumental variables — the moment condition and the covariance ratio

The econometric face of the same identification result. In the linear model
`Y = α + βD + ε` with an instrument satisfying `Cov(Z, ε) = 0`, the structural coefficient
is the ratio of covariances

$$\beta=\frac{\operatorname{Cov}(Z,Y)}{\operatorname{Cov}(Z,D)},$$

and when `Z` is binary this ratio *is* the Wald ratio of `IV.LATE` — the "indirect least
squares" identity. So the potential-outcome and the linear-model routes to IV agree.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). Definition 23.1 (§23.2, p. 318: endogeneity /
exogeneity); Definition 23.2 (§23.3, p. 319: the linear IV model with moment condition
eq. (23.3) `E[εZ] = 0`); §23.4 (p. 320: the just-identified solution
`β = E(ZDᵀ)⁻¹E(ZY)`); **Example 23.7** (pp. 320–321: the scalar case
`β = cov(Z,Y)/cov(Z,D)`, which Ding notes is "identical to the identification formula in
Theorem 21.1" for a binary instrument); §23.6.2 (pp. 323–324: reduced form eq. (23.11),
indirect least squares `β₁ = Γ₁/γ₁`). (`Ding Definition 23.2; Example 23.7; §23.4;
§23.6.2`.) Model-based IV analysis in G. W. Imbens and D. B. Rubin, *Causal Inference for
Statistics, Social, and Biomedical Sciences*, Cambridge University Press, 2015, ch. 25.
(`IR ch. 25`.)

**Scope.** The **population** scalar case: a single endogenous regressor and a single
instrument, in covariance form. The matrix two-stage least squares algebra of
Definition 23.3 / Theorem 23.1 is sample-level OLS bookkeeping and is out of scope for
this release; the statistical content — that the instrument identifies `β` through the
ratio of the reduced form to the first stage — is fully captured here.

**Proof formalization notes.** Everything is bilinearity of `cov` (`ProbabilityTheory.cov`,
notation `cov[X, Y; μ]`), which Mathlib provides with `MemLp _ 2 _` side conditions;
following the convention of `StatLean/StatisticalModels/Coarsening/Attenuation.lean`, those
integrability hypotheses are `USER-INPUT` because Mathlib's `cov` junk-values to `0`
without them, which would make the statements vacuous rather than false. The binary-`Z`
bridge rests on `cov_binary_eq`: for a `Bool`-valued instrument,
`Cov(Z, W) = P(Z=1)P(Z=0)·(E[W|Z=1] - E[W|Z=0])`, so the `P(Z=1)P(Z=0)` factors cancel in
the ratio and the covariance ratio collapses to the Wald ratio.

**Bibliographic comments.** The instrumental-variable estimator goes back to
P. G. Wright, *The Tariff on Animal and Vegetable Oils*, Macmillan, 1928 (Appendix B), and
O. Reiersøl, "Confluence analysis by means of instrumental sets of variables," *Ark. Mat.
Astr. Fys.* **32A** (1945). The modern potential-outcome reading is Angrist–Imbens–Rubin
(1996), cited in `IV.Defs`.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.CausalInference

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The linear IV model** (Ding Definition 23.2): the structural equation
`Y = α + βD + ε` together with the exogeneity moment conditions `E[ε] = 0` and
`Cov(Z, ε) = 0`. -/
structure LinearIVModel (μ : Measure Ω) (Zr D Y : Ω → ℝ) (α β : ℝ) : Prop where
  /-- Constitutive (Ding Definition 23.2): the structural equation, with `ε = Y - α - βD`. -/
  structural : ∀ ω, Y ω = α + β * D ω + (Y ω - α - β * D ω)
  /-- Constitutive (Ding Definition 23.2): the error has mean zero. -/
  mean_zero : ∫ ω, (Y ω - α - β * D ω) ∂μ = 0
  /-- Constitutive (Ding eq. (23.3)): the instrument is uncorrelated with the error — the
  exclusion restriction in linear-model form. -/
  exogenous : cov[Zr, fun ω => Y ω - α - β * D ω; μ] = 0

/-- Bilinearity of the covariance along the structural equation, proved here so that it is
available to `LinearIVModel.beta_eq_cov_div_cov` below; it is restated as
`cov_structural_decomp`. -/
private lemma cov_structural_decomp_aux {Zr D Y : Ω → ℝ} {α β : ℝ} [IsProbabilityMeasure μ]
    (hZ : MemLp Zr 2 μ) (hD : MemLp D 2 μ) (hY : MemLp Y 2 μ) :
    cov[Zr, Y; μ] = β * cov[Zr, D; μ] + cov[Zr, fun ω => Y ω - α - β * D ω; μ] := by
  have hYc : MemLp (fun ω => Y ω - α) 2 μ := hY.sub (memLp_const α)
  have hDc : MemLp (fun ω => β * D ω) 2 μ := hD.const_mul β
  rw [covariance_fun_sub_right hZ hYc hDc,
    covariance_sub_const_right (hY.integrable (by norm_num)) α,
    covariance_const_mul_right]
  ring

/-- **The just-identified IV solution** (Ding Example 23.7): under the linear IV model with
a relevant instrument, the structural coefficient is the ratio of covariances. -/
theorem LinearIVModel.beta_eq_cov_div_cov {Zr D Y : Ω → ℝ} {α β : ℝ} [IsProbabilityMeasure μ]
    (hmodel : LinearIVModel μ Zr D Y α β)
    -- USER-INPUT: square-integrability, so that Mathlib's `cov` is the genuine covariance
    -- rather than its junk value; cf. `Coarsening/Attenuation.lean`
    (hZ : MemLp Zr 2 μ) (hD : MemLp D 2 μ) (hY : MemLp Y 2 μ)
    -- USER-INPUT: instrument relevance `Cov(Z, D) ≠ 0`; Ding §23.4
    (hrel : cov[Zr, D; μ] ≠ 0) :
    β = cov[Zr, Y; μ] / cov[Zr, D; μ] := by
  rw [eq_div_iff hrel, cov_structural_decomp_aux (α := α) (β := β) hZ hD hY, hmodel.exogenous,
    add_zero, mul_comm]

/-- Bilinearity consequence used above, recorded on its own: the covariance of the
instrument with the outcome decomposes along the structural equation. -/
theorem cov_structural_decomp {Zr D Y : Ω → ℝ} {α β : ℝ} [IsProbabilityMeasure μ]
    (hZ : MemLp Zr 2 μ) (hD : MemLp D 2 μ) (hY : MemLp Y 2 μ) :
    cov[Zr, Y; μ] = β * cov[Zr, D; μ] + cov[Zr, fun ω => Y ω - α - β * D ω; μ] := by
  exact cov_structural_decomp_aux hZ hD hY

/-- **Covariance with a binary instrument** is the arm contrast scaled by the arm
probabilities: `Cov(Z, W) = P(Z=1)P(Z=0)(E[W|Z=1] - E[W|Z=0])`. -/
theorem cov_bool_eq_prob_mul_ittContrast {Z : Ω → Bool} {W : Ω → ℝ} [IsProbabilityMeasure μ]
    -- USER-INPUT: measurability of the instrument; user-supplied data
    (hZ : Measurable Z)
    -- USER-INPUT: square-integrability of the response
    (hW : MemLp W 2 μ)
    -- USER-INPUT: both instrument arms have positive probability
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0) :
    cov[fun ω => ind (Z ω), W; μ]
      = (μ {ω | Z ω = true}).toReal * (μ {ω | Z ω = false}).toReal
          * ittContrast μ Z W := by
  have hT : MeasurableSet {ω | Z ω = true} := hZ (measurableSet_singleton true)
  have hcompl : {ω | Z ω = true}ᶜ = {ω | Z ω = false} := by ext ω; simp
  have hiW : Integrable W μ := hW.integrable (by norm_num)
  have hindm : Measurable fun ω => ind (Z ω) := (measurable_of_countable ind).comp hZ
  have hindb : ∀ ω, ‖ind (Z ω)‖ ≤ 1 := by
    intro ω; cases h : Z ω <;> simp [ind]
  have hindL : MemLp (fun ω => ind (Z ω)) 2 μ :=
    MemLp.of_bound hindm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hindb)
  have hpq : (μ {ω | Z ω = true}).toReal + (μ {ω | Z ω = false}).toReal = 1 := by
    rw [← hcompl, ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      measure_add_measure_compl hT]
    simp
  have hmul : ∫ ω, (fun ω => ind (Z ω)) ω * W ω ∂μ = ∫ ω in {ω | Z ω = true}, W ω ∂μ := by
    rw [← integral_indicator hT]
    congr 1
    funext ω
    by_cases h : Z ω = true <;> simp [ind, h]
  have hone : ∫ ω, ind (Z ω) ∂μ = (μ {ω | Z ω = true}).toReal := by
    have hfe : (fun ω => ind (Z ω)) = Set.indicator {ω | Z ω = true} 1 := by
      funext ω
      by_cases h : Z ω = true <;> simp [ind, h]
    rw [hfe, integral_indicator_one hT, measureReal_def]
  have hsplit : ∫ ω, W ω ∂μ
      = (μ {ω | Z ω = true}).toReal * ∫ ω, W ω ∂(μ[|{ω | Z ω = true}])
        + (μ {ω | Z ω = false}).toReal * ∫ ω, W ω ∂(μ[|{ω | Z ω = false}]) := by
    rw [measureReal_mul_integral_cond (measure_ne_top μ _),
      measureReal_mul_integral_cond (measure_ne_top μ _), ← hcompl,
      integral_add_compl hT hiW]
  rw [covariance_eq_sub hindL hW]
  simp only [Pi.mul_apply]
  rw [hmul, hone, hsplit, ← measureReal_mul_integral_cond (measure_ne_top μ _) W,
    ittContrast, primaFacie, treatedEvent]
  have hq : (μ {ω | Z ω = false}).toReal = 1 - (μ {ω | Z ω = true}).toReal := by linarith
  rw [hq]
  ring

/-- **Indirect least squares = the Wald ratio** (Ding Example 23.7, §23.6.2): for a binary
instrument the covariance ratio equals the ratio of the two intention-to-treat contrasts —
the reduced form over the first stage. -/
theorem cov_ratio_eq_ittContrast_ratio {Z : Ω → Bool} {D Y : Ω → ℝ} [IsProbabilityMeasure μ]
    (hZ : Measurable Z) (hD : MemLp D 2 μ) (hY : MemLp Y 2 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    -- USER-INPUT: instrument relevance; Ding §23.4
    (hrel : ittContrast μ Z D ≠ 0) :
    cov[fun ω => ind (Z ω), Y; μ] / cov[fun ω => ind (Z ω), D; μ]
      = ittContrast μ Z Y / ittContrast μ Z D := by
  have hp : (μ {ω | Z ω = true}).toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, hZ1, measure_ne_top μ _]
  have hq : (μ {ω | Z ω = false}).toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, hZ0, measure_ne_top μ _]
  rw [cov_bool_eq_prob_mul_ittContrast hZ hY hZ1 hZ0,
    cov_bool_eq_prob_mul_ittContrast hZ hD hZ1 hZ0]
  exact mul_div_mul_left _ _ (mul_ne_zero hp hq)

/-- **The two routes to IV agree** (Ding Example 23.7 vs Theorem 21.1): with a binary
instrument and a binary treatment satisfying the potential-outcome IV assumptions, the
linear-IV coefficient is the complier average causal effect. -/
theorem beta_eq_cace {Z d1 d0 : Ω → Bool} {y1 y0 : Ω → ℝ} {α β : ℝ} [IsProbabilityMeasure μ]
    -- USER-INPUT: the linear IV model for the observed data; Ding Definition 23.2
    (hmodel : LinearIVModel μ (fun ω => ind (Z ω)) (fun ω => ind (obsTreat Z d1 d0 ω))
      (obs Z y1 y0) α β)
    -- USER-INPUT: the three potential-outcome IV assumptions; Ding Assumptions 21.1–21.3
    (hrand : IVRandomized μ Z d1 d0 y1 y0) (hmono : NoDefiers d1 d0)
    (hexcl : ExclusionRestriction d1 d0 y1 y0)
    (hZm : Measurable Z) (hd1 : Measurable d1) (hd0 : Measurable d0)
    (hy1 : Measurable y1) (hy0 : Measurable y0)
    -- USER-INPUT: square-integrability for the covariance form
    (hD : MemLp (fun ω => ind (obsTreat Z d1 d0 ω)) 2 μ) (hY : MemLp (obs Z y1 y0) 2 μ)
    (hi1 : Integrable y1 μ) (hi0 : Integrable y0 μ)
    (hZ1 : μ {ω | Z ω = true} ≠ 0) (hZ0 : μ {ω | Z ω = false} ≠ 0)
    -- USER-INPUT: instrument relevance; Ding Theorem 21.1
    (hrel : ittContrast μ Z (fun ω => ind (obsTreat Z d1 d0 ω)) ≠ 0)
    (hrelcov : cov[fun ω => ind (Z ω), fun ω => ind (obsTreat Z d1 d0 ω); μ] ≠ 0) :
    β = cace μ d1 d0 y1 y0 := by
  have hindm : Measurable fun ω => ind (Z ω) := (measurable_of_countable ind).comp hZm
  have hindL : MemLp (fun ω => ind (Z ω)) 2 μ :=
    MemLp.of_bound hindm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by cases h : Z ω <;> simp [ind])
  rw [LinearIVModel.beta_eq_cov_div_cov hmodel hindL hD hY hrelcov,
    cov_ratio_eq_ittContrast_ratio hZm hD hY hZ1 hZ0 hrel,
    ← cace_eq_ittContrast_div hrand hmono hexcl hZm hd1 hd0 hy1 hy0 hi1 hi0 hZ1 hZ0 hrel]

end StatLean.CausalInference
