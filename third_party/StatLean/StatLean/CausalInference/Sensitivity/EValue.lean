module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The E-value — how strong must unmeasured confounding be?

Cornfield's inequality bounds the *observed* risk ratio by a function of the two
confounding risk ratios: if an unmeasured binary confounder `U` fully explains an observed
association, then

$$\mathrm{RR}^{\mathrm{obs}}\ \le\
  \frac{\mathrm{RR}_{ZU}\,\mathrm{RR}_{UY}}{\mathrm{RR}_{ZU}+\mathrm{RR}_{UY}-1}
  \;=\;\beta(\mathrm{RR}_{ZU},\mathrm{RR}_{UY}).$$

Inverting this bound gives the **E-value**
`E = RR + √(RR(RR-1))`: to explain away an observed risk ratio `RR`, the *larger* of the two
confounding associations must be at least `E`. It is a one-number summary of how fragile a
causal claim is.

**Reference.** P. Ding, *A First Course in Causal Inference*, arXiv:2305.18793v2, 2023
(published by Chapman & Hall/CRC, 2024). ch. 17 (*E-Value: Evidence for Causation in
Observational Studies with Unmeasured Confounding*): **Theorem 17.1** (§17.1, p. 233, with
the exact identity eq. (17.2) on p. 234) under latent ignorability `Z ⫫ Y | (X, U)` and the
positivity conditions (17.1); **Lemma 17.1** (p. 235: the properties of
`β(w₁,w₂) = w₁w₂/(w₁+w₂-1)`, including `β ≤ w²/(2w-1)` for `w = max(w₁,w₂)`);
**Definition 17.1** (§17.2, p. 236: the E-value); the "explaining away" displays of §17.2
(pp. 235–236, unnumbered). (`Ding ch. 17; Theorem 17.1; Lemma 17.1; Definition 17.1`.)
Sensitivity analysis and bounds are ch. 22 of G. W. Imbens and D. B. Rubin, *Causal
Inference for Statistics, Social, and Biomedical Sciences*, Cambridge University Press,
2015. (`IR ch. 22`.)

**Scope.** This file formalizes the **algebra** of the bound: the properties of `β`, the
sharp threshold, and the E-value's defining inversion property. The probabilistic
derivation of Theorem 17.1 from a latent-ignorability model (Ding's eq. (17.2)) is *not*
formalized in this release: it needs the confounded-observational-model layer that the
`Rosenbaum` and `Observational` files build for other purposes, and its content is the
inequality that we take as the starting point here. What *is* proved is exactly the part a
practitioner uses — that `E` is the least value of `max(RR_ZU, RR_UY)` compatible with a
given observed risk ratio.

**Proof formalization notes.** All statements are about real numbers under
`1 ≤ w₁, w₂` and `1 ≤ RR`, so they are `nlinarith`/`field_simp`-shaped once the right
auxiliary square is supplied. The key identity behind the E-value is that
`β(E, E) = E²/(2E-1) = RR` exactly when `E = RR + √(RR(RR-1))`, i.e. `E` is the root of
`E² - 2·RR·E + RR = 0` that is `≥ 1`; the discriminant is `4RR(RR-1) ≥ 0` precisely
because `RR ≥ 1`.

**Bibliographic comments.** J. Cornfield et al., "Smoking and lung cancer: recent evidence
and a discussion of some questions," *J. Natl. Cancer Inst.* **22** (1959), 173–203;
T. J. VanderWeele and P. Ding, "Sensitivity analysis in observational research:
introducing the E-value," *Ann. Intern. Med.* **167** (2017), 268–274; the sharpness of the
bound is P. Ding and T. J. VanderWeele, "Sensitivity analysis without assumptions,"
*Epidemiology* **27** (2016), 368–377.
-/

namespace StatLean.CausalInference

/-- Cornfield's **bounding factor** `β(w₁,w₂) = w₁w₂/(w₁+w₂-1)` (Ding Theorem 17.1,
Lemma 17.1): the largest observed risk ratio that confounding associations `w₁, w₂` can
produce. -/
noncomputable def boundingFactor (w₁ w₂ : ℝ) : ℝ := w₁ * w₂ / (w₁ + w₂ - 1)

/-- The **E-value** of an observed risk ratio (Ding Definition 17.1):
`E = RR + √(RR(RR-1))`. -/
noncomputable def eValue (rr : ℝ) : ℝ := rr + Real.sqrt (rr * (rr - 1))

/-- The bounding factor is at least `1` when both confounding associations are
(Ding Lemma 17.1). -/
theorem one_le_boundingFactor {w₁ w₂ : ℝ} (h₁ : 1 ≤ w₁) (h₂ : 1 ≤ w₂) :
    1 ≤ boundingFactor w₁ w₂ := by
  have hpos : (0:ℝ) < w₁ + w₂ - 1 := by linarith
  rw [boundingFactor, le_div_iff₀ hpos]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂)]

/-- The bounding factor is monotone in each argument (Ding Lemma 17.1). -/
theorem boundingFactor_le_of_le {w₁ w₂ w₁' : ℝ} (h₁ : 1 ≤ w₁) (h₂ : 1 ≤ w₂) (h : w₁ ≤ w₁') :
    boundingFactor w₁ w₂ ≤ boundingFactor w₁' w₂ := by
  have h₁' : (1:ℝ) ≤ w₁' := h₁.trans h
  have hp : (0:ℝ) < w₁ + w₂ - 1 := by linarith
  have hp' : (0:ℝ) < w₁' + w₂ - 1 := by linarith
  rw [boundingFactor, boundingFactor, div_le_div_iff₀ hp hp']
  nlinarith [mul_nonneg (mul_nonneg (zero_le_one.trans h₂) (sub_nonneg.2 h)) (sub_nonneg.2 h₂)]

/-- **Lemma 17.1** (Ding p. 235): the bounding factor is controlled by the *larger* of the
two confounding associations, `β(w₁,w₂) ≤ w²/(2w-1)` with `w = max(w₁,w₂)`. This is what
reduces a two-parameter sensitivity analysis to one number. -/
theorem boundingFactor_le_sq_div {w₁ w₂ : ℝ} (h₁ : 1 ≤ w₁) (h₂ : 1 ≤ w₂) :
    boundingFactor w₁ w₂ ≤ max w₁ w₂ ^ 2 / (2 * max w₁ w₂ - 1) := by
  have hcomm : ∀ a b : ℝ, boundingFactor a b = boundingFactor b a := by
    intro a b; unfold boundingFactor; ring_nf
  have hw₁ : w₁ ≤ max w₁ w₂ := le_max_left _ _
  have hw₂ : w₂ ≤ max w₁ w₂ := le_max_right _ _
  have hw1 : (1:ℝ) ≤ max w₁ w₂ := h₁.trans hw₁
  have hself : boundingFactor (max w₁ w₂) (max w₁ w₂)
      = max w₁ w₂ ^ 2 / (2 * max w₁ w₂ - 1) := by
    unfold boundingFactor; ring_nf
  rw [← hself]
  calc boundingFactor w₁ w₂ ≤ boundingFactor (max w₁ w₂) w₂ :=
        boundingFactor_le_of_le h₁ h₂ hw₁
    _ = boundingFactor w₂ (max w₁ w₂) := hcomm _ _
    _ ≤ boundingFactor (max w₁ w₂) (max w₁ w₂) := boundingFactor_le_of_le h₂ hw1 hw₂

/-- The E-value is at least one, and at least the observed risk ratio. -/
theorem le_eValue {rr : ℝ} (h : 1 ≤ rr) : rr ≤ eValue rr := by
  unfold eValue
  linarith [Real.sqrt_nonneg (rr * (rr - 1))]

/-- The E-value is at least `1`. -/
theorem one_le_eValue {rr : ℝ} (h : 1 ≤ rr) : 1 ≤ eValue rr :=
  h.trans (le_eValue h)

/-- The square of the E-value's radical, restated for `nlinarith`/`linear_combination`. -/
private lemma sq_sqrt_rr {rr : ℝ} (h : 1 ≤ rr) :
    Real.sqrt (rr * (rr - 1)) ^ 2 = rr * (rr - 1) :=
  Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))

/-- The smaller root `rr - √(rr(rr-1))` of `x² - 2·rr·x + rr` never exceeds `1`. -/
private lemma sub_one_le_sqrt_rr {rr : ℝ} (h : 1 ≤ rr) :
    rr - 1 ≤ Real.sqrt (rr * (rr - 1)) := by
  have h1 : Real.sqrt ((rr - 1) ^ 2) ≤ Real.sqrt (rr * (rr - 1)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ rr - 1)] at h1

/-- **The defining identity of the E-value** (Ding §17.2): at `w₁ = w₂ = E` the bounding
factor is exactly the observed risk ratio — `E` is the point at which confounding could
just barely explain the association away. -/
theorem boundingFactor_eValue_self {rr : ℝ} (h : 1 ≤ rr) :
    boundingFactor (eValue rr) (eValue rr) = rr := by
  have hE : (1:ℝ) ≤ eValue rr := one_le_eValue h
  have hden : (0:ℝ) < eValue rr + eValue rr - 1 := by linarith
  have hkey : eValue rr * eValue rr = rr * (eValue rr + eValue rr - 1) := by
    simp only [eValue]
    linear_combination sq_sqrt_rr h
  unfold boundingFactor
  rw [div_eq_iff (ne_of_gt hden)]
  exact hkey

/-- **The E-value is a valid threshold** (Ding §17.2): if both confounding associations are
below the E-value, they cannot produce the observed risk ratio — so explaining the
association away requires at least one association of size `E`. -/
theorem lt_of_boundingFactor_ge {rr w₁ w₂ : ℝ} (hrr : 1 ≤ rr) (h₁ : 1 ≤ w₁) (h₂ : 1 ≤ w₂)
    -- USER-INPUT: confounding is strong enough to explain the observed association away;
    -- Ding Theorem 17.1
    (hexplain : rr ≤ boundingFactor w₁ w₂) :
    eValue rr ≤ max w₁ w₂ := by
  have hw1 : (1:ℝ) ≤ max w₁ w₂ := h₁.trans (le_max_left _ _)
  have hden : (0:ℝ) < 2 * max w₁ w₂ - 1 := by linarith
  -- The one-parameter form of Cornfield's bound, cleared of its denominator.
  have hq : rr * (2 * max w₁ w₂ - 1) ≤ max w₁ w₂ ^ 2 := by
    rw [← le_div_iff₀ hden]
    exact hexplain.trans (boundingFactor_le_sq_div h₁ h₂)
  have hs2 := sq_sqrt_rr hrr
  have hlow := sub_one_le_sqrt_rr hrr
  unfold eValue
  rcases lt_or_ge (rr - Real.sqrt (rr * (rr - 1))) (max w₁ w₂) with hcase | hcase
  · -- `max w₁ w₂` lies strictly above the smaller root, so it must lie above the larger one:
    -- otherwise `(w - (rr - s))·(w - (rr + s)) = w² - 2·rr·w + rr` would be negative.
    nlinarith [hq, hs2, hcase]
  · -- Degenerate branch: `1 ≤ max w₁ w₂ ≤ rr - s ≤ 1` forces `rr = 1` and `s = 0`.
    have hs : Real.sqrt (rr * (rr - 1)) = rr - 1 := le_antisymm (by linarith) hlow
    have hrr1 : rr = 1 := by rw [hs] at hs2; nlinarith [hs2]
    rw [hrr1] at hs ⊢
    linarith [hw1, hs]

/-- **The E-value is the *least* such threshold** (Ding §17.2): it is attained, so no
smaller number has the previous property. Together with `lt_of_boundingFactor_ge` this
characterizes the E-value. -/
theorem exists_boundingFactor_eq {rr : ℝ} (h : 1 ≤ rr) :
    ∃ w₁ w₂ : ℝ, 1 ≤ w₁ ∧ 1 ≤ w₂ ∧ max w₁ w₂ = eValue rr ∧ boundingFactor w₁ w₂ = rr :=
  ⟨eValue rr, eValue rr, one_le_eValue h, one_le_eValue h, max_self _,
    boundingFactor_eValue_self h⟩

/-- The E-value of a null association is `1`: no confounding is needed to explain away an
association that is not there (Ding §17.2). -/
theorem eValue_one : eValue 1 = 1 := by
  norm_num [eValue]

/-- The E-value is monotone in the observed risk ratio: stronger observed associations are
harder to explain away (Ding §17.2). -/
theorem eValue_mono {rr rr' : ℝ} (h : 1 ≤ rr) (hle : rr ≤ rr') : eValue rr ≤ eValue rr' := by
  unfold eValue
  have hmono : rr * (rr - 1) ≤ rr' * (rr' - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hle) (by linarith : (0:ℝ) ≤ rr' + rr - 1)]
  exact add_le_add hle (Real.sqrt_le_sqrt hmono)

end StatLean.CausalInference
