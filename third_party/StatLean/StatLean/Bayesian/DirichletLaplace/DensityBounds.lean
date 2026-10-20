module
public import StatLean.Bayesian.DirichletLaplace.MarginalDensity
public import StatLean.Bayesian.ForMathlib.GammaBounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Dirichlet–Laplace density and tail bounds (C3)

Quantitative two-sided control of the DL marginal density `dlDensity a` (from `MarginalDensity`, C2)
and of the marginal tail `ℙ_{DL,a}(|θ| > δ)`. These are BPPD **Lemma 3.2** (density bounds (13)/(14))
and **Lemma 3.3** (tail bound), the analytic core consumed by the product-density estimates
(`PriorDensityBounds`, C4), the support-count Chernoff bound (`PriorSmallBall`, C5), and Lemma 6.1
(`PriorMassRatio`, C14).

Results:
* **P3** `dlDensity_le` — upper bound `f_{DL,a}(x) ≤ 17·a·δ^{a-1}` for `δ ≤ |x|` (BPPD eq. (13)).
* **P4** `dlDensity_ge_of_one_le` / `dlDensity_ge` — lower bounds `f_{DL,a}(x) ≥ (a/64)·|x|^{-1/2}
  e^{-3√|x|}` (`|x| ≥ 1`) and the uniform log-linear form `≥ (a/64) e^{-3-(7/2)√|x|}` (BPPD eq. (14)).
* **P5** `dlMarginal_abs_gt_le` (+ `dlMarginal_abs_gt_le'`, `dlMarginal_abs_le_ge`) — the tail bound
  `ℙ_{DL,a}(|θ| > δ) ≤ (8 + 2 log(1/δ))/Γ(a)`, its `ζ`-form `≤ e·a·(8 + 2 log(1/δ))`, and the
  complementary box-mass lower bound (BPPD Lemma 3.3).

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, JASA 110 (2015), 1479–1490 (arXiv:1401.5398). Lemma 3.2 (eq. (13)/(14)),
Lemma 3.3.

**Proof formalization notes.**
* **P3** (`dlDensity_le`): on the real integral form (C2, `dlDensity_eq_ofReal_integral`), substitute
  `u = |x|/ψ` and bound `∫ u^{-a} e^{-u} du` on `(0, |x|/… )`; combine with `dlNormConst_le` (C2).
  Deviation **D8**: the upper bound genuinely needs `a ≤ 1/2` — the small-`ψ` tail of the mixture
  produces a `Γ(1-a)` factor that blows up as `a → 1⁻`, so the paper's `a ≤ 1` is insufficient for a
  clean constant. `17` is a roomy explicit numeral, not the paper's unspecified constant.
* **P4** (`dlDensity_ge_of_one_le`, `dlDensity_ge`): restrict the mixture integral to
  `ψ ∈ [√(2|x|), 2√(2|x|)]` and bound both densities below there; combine with `dlNormConst_ge` (C2).
  Deviation **D5**: this restriction yields the exponent `-(3/√2)√|x|`, rounded up to `-3√|x|` (the
  paper sketches `-2√|x|`, which the restriction cannot deliver). The uniform log-linear form
  absorbs the algebraic factor via `|x|^{-1/2} e^{-3√|x|} ≥ e^{-3-(7/2)√|x|}` and is extended to
  `|x| < 1` by monotonicity (P2). Lower bounds need only `a ≤ 1` (contrast D8). `a/64` is roomy.
* **P5** (`dlMarginal_abs_gt_le`): from `dlMarginal_abs_gt_eq_mixture` (C2), split the `Gamma`-mixture
  tail `∫ e^{-δ/ψ} dGamma_{a,1/2}` at `ψ = 4δ`. Deviation **D6**: proved *without* Alzer's
  inequality — the small part (`ψ ≤ 4δ`) is `≤ 4` via `e^{-u} ≤ u^{-(1-a)}`, the large part
  (`ψ > 4δ`) is `≤ C + 2 log(1/δ)` via `ψ^{a-1} ≤ max(ψ^{-1}, 1)`; holds for all `δ ∈ (0,1)` (no
  "`δ` small"). `Γ` numerics go through `Γ(1+a) ∈ [e^{-1}, 2]` (F2), *not* the paper's "`Γ(x) ≥ 1/x`"
  (false as stated). The `ζ`-form uses `1/Γ(a) ≤ e·a` (`inv_e_mul_le_Gamma`, F2); the complement is
  `1 − (tail)` via `IsProbabilityMeasure`.

**Bibliographic comments.** Sharp tail and density estimates of this kind are the technical engine of
Bayesian posterior-contraction theory in the framework of Ghosal–Ghosh–van der Vaart (*Ann.
Statist.* 28 (2000), 500–531) and Castillo–van der Vaart (*Ann. Statist.* 40 (2012), 2069–2101);
here they quantify how the Dirichlet–Laplace marginal simultaneously concentrates near the origin
(box-mass lower bound) and retains heavy enough tails (`ℙ(|θ| > δ)` upper bound) to recover sparse
signals.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

variable {a δ : ℝ}

/-! ### Reusable analytic bricks for the tail estimate (P5) -/

/-- `e^{-u} ≤ u^{-b}` for `u > 0`, `0 ≤ b ≤ 1` (via `u^b ≤ max(1,u) ≤ e^u`). Feeds the small-`ψ`
part of the Lemma 3.3 mixture-tail split. -/
private lemma exp_neg_le_rpow_neg {u b : ℝ} (hu : 0 < u) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp (-u) ≤ u ^ (-b) := by
  have hub : u ^ b ≤ Real.exp u := by
    rcases le_or_gt u 1 with h | h
    · exact le_trans (Real.rpow_le_one hu.le h hb0)
        (by have := Real.add_one_le_exp u; linarith [hu.le])
    · calc u ^ b ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le hb1
        _ = u := Real.rpow_one u
        _ ≤ Real.exp u := by have := Real.add_one_le_exp u; linarith
  rw [Real.rpow_neg hu.le, Real.exp_neg]
  exact inv_anti₀ (Real.rpow_pos_of_pos hu b) hub

/-- Pointwise `ℝ≥0∞` product identity for the Gamma×tail integrand (`ψ > 0`):
`g_{a,1/2}(ψ)·e^{-δ/ψ} = ofReal((1/2)^a/Γ(a)·ψ^{a-1}·e^{-ψ/2}·e^{-δ/ψ})`. -/
private lemma gammaExp_ennreal {a δ ψ : ℝ} (ha : 0 < a) (hψ : 0 < ψ) :
    gammaPDF a 2⁻¹ ψ * ENNReal.ofReal (Real.exp (-δ / ψ))
      = ENNReal.ofReal ((2⁻¹ : ℝ) ^ a / Real.Gamma a
          * (ψ ^ (a - 1) * Real.exp (-ψ / 2) * Real.exp (-δ / ψ))) := by
  rw [gammaPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha (by norm_num) ψ),
    gammaPDFReal, if_pos hψ.le]
  congr 1
  rw [show -(2⁻¹ * ψ) = -ψ / 2 by ring]; ring

/-- Pointwise integrand identity for the substitution `u = δ/ψ` (`p = -1` in `integral_comp_rpow_Ioi`):
`(|-1|·ψ^{-2})·((ψ^{-1})^{-a}·e^{-δψ^{-1}}) = ψ^{a-2}·e^{-δ/ψ}` on `ψ > 0`. -/
private lemma covIntegrand_eq {a δ ψ : ℝ} (hψ : 0 < ψ) :
    (|(-1 : ℝ)| * ψ ^ ((-1 : ℝ) - 1))
        • ((ψ ^ (-1 : ℝ)) ^ (1 - a - 1) * Real.exp (-(δ * ψ ^ (-1 : ℝ))))
      = ψ ^ (a - 2) * Real.exp (-δ / ψ) := by
  rw [smul_eq_mul, show |(-1 : ℝ)| = 1 by norm_num, one_mul,
    show ((-1 : ℝ) - 1) = -2 by norm_num, show (1 - a - 1 : ℝ) = -a by ring,
    ← Real.rpow_mul hψ.le, show (-1 : ℝ) * -a = a by ring, Real.rpow_neg_one ψ,
    show δ * ψ⁻¹ = δ / ψ by rw [div_eq_mul_inv], ← mul_assoc, ← Real.rpow_add hψ,
    show (-2 : ℝ) + a = a - 2 by ring, neg_div]

/-- The reciprocal-exponent integral `∫_{ψ>0} ψ^{a-2} e^{-δ/ψ} dψ = (1/δ)^{1-a} Γ(1-a)`
(substitution `u = δ/ψ`, then the Gamma integral). Feeds the density upper bound P3. -/
private lemma integral_rpow_exp_neg_div {a δ : ℝ} (ha1 : a < 1) (hδ : 0 < δ) :
    ∫ ψ in Set.Ioi 0, ψ ^ (a - 2) * Real.exp (-δ / ψ)
      = (1 / δ) ^ (1 - a) * Real.Gamma (1 - a) := by
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi (show (0 : ℝ) < 1 - a by linarith) hδ,
    ← integral_comp_rpow_Ioi (fun y => y ^ (1 - a - 1) * Real.exp (-(δ * y)))
      (show (-1 : ℝ) ≠ 0 by norm_num)]
  exact setIntegral_congr_fun measurableSet_Ioi (fun ψ hψ => (covIntegrand_eq hψ).symm)

/-! ### P3 — density upper bound (BPPD Lemma 3.2, eq. (13)) -/

/-- **P3 / Lemma 3.2 upper bound (BPPD eq. (13)).** For a threshold `0 < δ ≤ 1` and any point with
`δ ≤ |x|`, the DL marginal density satisfies `f_{DL,a}(x) ≤ 17 · a · δ^{a-1}`.

Deviation **D8**: the bound needs `a ≤ 1/2` (the `Γ(1-a)` factor from the small-`ψ` tail blows up as
`a → 1⁻`; the paper's `a ≤ 1` is not enough). Lower bounds P4 need only `a ≤ 1`. The prefactor `17`
is a roomy explicit numeral. -/
lemma dlDensity_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.2)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1/2 (D8: Γ(1-a) control in the density upper bound); BPPD §3.1 (Lemma 3.2)
    (ha1 : a ≤ 1 / 2)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.2)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold ≤ 1; BPPD §3.1 (Lemma 3.2)
    (hδ1 : δ ≤ 1)
    -- USER-INPUT: point outside the δ-window; BPPD §3.1 (Lemma 3.2)
    {x : ℝ} (hx : δ ≤ |x|) :
    dlDensity a x ≤ ENNReal.ofReal (17 * a * δ ^ (a - 1)) := by
  have hδx : dlDensity a x ≤ dlDensity a δ :=
    dlDensity_anti (by rw [abs_of_pos hδ]; exact hx)
  refine le_trans hδx ?_
  rw [dlDensity_eq_ofReal_integral ha hδ.ne']
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [abs_of_pos hδ]
  -- integrability of the two comparison integrands
  have hJint : IntegrableOn (fun ψ => ψ ^ (a - 2) * Real.exp (-ψ / 2 - δ / ψ))
      (Set.Ioi 0) := by
    have h := integrable_dlDensity_integrand ha hδ.ne'
    simp only [abs_of_pos hδ] at h
    simp_rw [mul_assoc] at h
    exact (integrable_const_mul_iff
      (isUnit_iff_ne_zero.mpr (dlNormConst_pos ha).ne') _).mp h
  have hg : IntegrableOn (fun y => y ^ (1 - a - 1) * Real.exp (-(δ * y))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1 - a - 1) (p := 1) (b := δ)
      (by linarith) one_pos hδ
    simp only [Real.rpow_one, neg_mul] at h
    exact h
  have hJbigint : IntegrableOn (fun ψ => ψ ^ (a - 2) * Real.exp (-δ / ψ)) (Set.Ioi 0) := by
    have hc := (integrableOn_Ioi_comp_rpow_iff
      (fun y => y ^ (1 - a - 1) * Real.exp (-(δ * y))) (show (-1 : ℝ) ≠ 0 by norm_num)).mpr hg
    exact hc.congr_fun (fun ψ hψ => covIntegrand_eq hψ) measurableSet_Ioi
  -- pull the constant, compare, and evaluate
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  have hJle : ∫ ψ in Set.Ioi 0, ψ ^ (a - 2) * Real.exp (-ψ / 2 - δ / ψ)
      ≤ ∫ ψ in Set.Ioi 0, ψ ^ (a - 2) * Real.exp (-δ / ψ) := by
    refine setIntegral_mono_on hJint hJbigint measurableSet_Ioi (fun ψ hψ => ?_)
    have hψ0 : 0 < ψ := hψ
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hψ0.le _)
    exact Real.exp_le_exp.mpr (by rw [neg_div, neg_div]; linarith [hψ0.le])
  have hpow : (1 / δ) ^ (1 - a) = δ ^ (a - 1) := by
    rw [one_div, Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le, show -(1 - a) = a - 1 by ring]
  have hΓ4 : Real.Gamma (1 - a) ≤ 4 := Gamma_one_sub_le_four ha.le ha1
  have hnorm : dlNormConst a ≤ Real.exp 1 / 2 * a := dlNormConst_le ha (by linarith)
  have hdlpos : (0 : ℝ) ≤ dlNormConst a := (dlNormConst_pos ha).le
  have hδpow : (0 : ℝ) ≤ δ ^ (a - 1) := Real.rpow_nonneg hδ.le _
  calc dlNormConst a * ∫ ψ in Set.Ioi 0, ψ ^ (a - 2) * Real.exp (-ψ / 2 - δ / ψ)
      ≤ dlNormConst a * ∫ ψ in Set.Ioi 0, ψ ^ (a - 2) * Real.exp (-δ / ψ) :=
        mul_le_mul_of_nonneg_left hJle hdlpos
    _ = dlNormConst a * ((1 / δ) ^ (1 - a) * Real.Gamma (1 - a)) := by
        rw [integral_rpow_exp_neg_div (by linarith) hδ]
    _ = dlNormConst a * δ ^ (a - 1) * Real.Gamma (1 - a) := by rw [hpow]; ring
    _ ≤ Real.exp 1 / 2 * a * δ ^ (a - 1) * 4 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hnorm hδpow) hΓ4
          (Real.Gamma_pos_of_pos (by linarith)).le (by positivity)
    _ ≤ 17 * (a * δ ^ (a - 1)) := by
        nlinarith [Real.exp_one_lt_three, mul_nonneg ha.le hδpow]

/-! ### P4 — density lower bounds (BPPD Lemma 3.2, eq. (14); deviation D5) -/

/-- **P4 / Lemma 3.2 lower bound (BPPD eq. (14)), large-`|x|` form.** For `1 ≤ |x|`,
`f_{DL,a}(x) ≥ (a/64) · |x|^{-1/2} · e^{-3√|x|}`.

Deviation **D5**: restricting the mixture to `ψ ∈ [√(2|x|), 2√(2|x|)]` produces the exponent
`-(3/√2)√|x|`, rounded up to `-3√|x|` (the paper sketches `-2√|x|`, unattainable by this
restriction). `a/64` is a roomy explicit constant; lower bounds need only `a ≤ 1` (contrast D8). -/
lemma dlDensity_ge_of_one_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.2)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1 (lower-bound regime; cf. D8); BPPD §3.1 (Lemma 3.2)
    (ha1 : a ≤ 1)
    -- USER-INPUT: point with |x| ≥ 1; BPPD §3.1 (Lemma 3.2)
    {x : ℝ} (hx : 1 ≤ |x|) :
    ENNReal.ofReal ((a / 64) * |x| ^ (-(1 / 2) : ℝ) * Real.exp (-3 * Real.sqrt |x|))
      ≤ dlDensity a x := by
  set r := |x| with hr_def
  have hr1 : (1 : ℝ) ≤ r := hx
  have hr0 : (0 : ℝ) < r := by linarith
  have h2r : (0 : ℝ) < 2 * r := by linarith
  set s := Real.sqrt (2 * r) with hs_def
  have hs0 : (0 : ℝ) < s := Real.sqrt_pos.mpr h2r
  have h2s : (0 : ℝ) < 2 * s := by positivity
  have hs2 : s ^ 2 = 2 * r := Real.sq_sqrt h2r.le
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hs_def, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have h1_2s : (1 : ℝ) ≤ 2 * s := by linarith
  have hqr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hq0 : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hq1 : (1 : ℝ) ≤ Real.sqrt r := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hr1
  have hsqrt2_ge : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt2_le : Real.sqrt 2 ≤ 3 / 2 := by
    have h := Real.sqrt_le_sqrt (show (2 : ℝ) ≤ (3 / 2) ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have hs_eq : s = Real.sqrt 2 * Real.sqrt r := by
    rw [hs_def, Real.sqrt_mul (by norm_num) r]
  -- the constant lower bound `L` on the mixture integrand over `Icc s (2s)`
  set L : ℝ := (a / 8) * (2 * s) ^ (a - 2) * Real.exp (-3 * Real.sqrt r) with hL_def
  have hL_nonneg : 0 ≤ L :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg h2s.le _)) (Real.exp_pos _).le
  -- lintegral lower bound
  have hstep : ENNReal.ofReal (L * s) ≤ dlDensity a x := by
    rw [dlDensity]
    calc ENNReal.ofReal (L * s)
        = ∫⁻ _ψ in Set.Icc s (2 * s), ENNReal.ofReal L ∂volume := by
          rw [setLIntegral_const, Real.volume_Icc, show 2 * s - s = s by ring,
            ← ENNReal.ofReal_mul hL_nonneg]
      _ ≤ ∫⁻ ψ in Set.Icc s (2 * s), gammaPDF a 2⁻¹ ψ * laplacePDF ψ x ∂volume := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
            (ae_of_all _ fun ψ (hmem : ψ ∈ Set.Icc s (2 * s)) => ?_))
          obtain ⟨hψl, hψu⟩ := hmem
          have hψ0 : 0 < ψ := lt_of_lt_of_le hs0 hψl
          rw [gammaLaplace_ennreal ha hψ0]
          refine ENNReal.ofReal_le_ofReal ?_
          -- `L ≤ dlNormConst a * ψ^(a-2) * exp(-ψ/2 - r/ψ)`
          have hA : a / 8 ≤ dlNormConst a := dlNormConst_ge ha ha1
          have hB : (2 * s) ^ (a - 2) ≤ ψ ^ (a - 2) :=
            Real.rpow_le_rpow_of_nonpos hψ0 hψu (by linarith)
          have hC : Real.exp (-3 * Real.sqrt r) ≤ Real.exp (-ψ / 2 - r / ψ) := by
            refine Real.exp_le_exp.mpr ?_
            -- `-3√r ≤ -ψ/2 - r/ψ`, i.e. `ψ/2 + r/ψ ≤ 3√r`
            have hψq : Real.sqrt r ≤ ψ := by
              refine le_trans ?_ hψl; rw [hs_eq]; nlinarith [hsqrt2_ge, hq0]
            have hψ3q : ψ ≤ 3 * Real.sqrt r := by
              refine le_trans hψu ?_; rw [hs_eq]; nlinarith [hsqrt2_le, hq0]
            have hrψ : r / ψ ≤ Real.sqrt r := by
              rw [div_le_iff₀ hψ0]; nlinarith [hqr, hψq, hq0]
            have : -ψ / 2 = -(ψ / 2) := by ring
            rw [this]
            linarith [hψ3q, hrψ, hq0]
          have hposB : (0 : ℝ) ≤ (2 * s) ^ (a - 2) := Real.rpow_nonneg h2s.le _
          have hposdl : (0 : ℝ) ≤ dlNormConst a := (dlNormConst_pos ha).le
          calc L = a / 8 * (2 * s) ^ (a - 2) * Real.exp (-3 * Real.sqrt r) := hL_def
            _ ≤ dlNormConst a * ψ ^ (a - 2) * Real.exp (-ψ / 2 - r / ψ) :=
                mul_le_mul (mul_le_mul hA hB hposB hposdl) hC (Real.exp_pos _).le
                  (mul_nonneg hposdl (Real.rpow_nonneg hψ0.le _))
      _ ≤ ∫⁻ ψ, gammaPDF a 2⁻¹ ψ * laplacePDF ψ x ∂volume :=
          setLIntegral_le_lintegral _ _
  -- assemble
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hstep
  -- `target ≤ L * s`
  have hval : (2 * s) ^ (2 : ℝ) = 8 * r := by
    rw [Real.rpow_two, show (2 * s) ^ 2 = 4 * s ^ 2 by ring, hs2]; ring
  have he2 : (2 * s) ^ (-2 : ℝ) = 1 / (8 * r) := by
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg h2s.le, hval, one_div]
  have he1 : (2 * s) ^ (-2 : ℝ) ≤ (2 * s) ^ (a - 2) :=
    Real.rpow_le_rpow_of_exponent_le h1_2s (by linarith)
  have hstep2 : a / 8 * (2 * s) ^ (-2 : ℝ) * s ≤ a / 8 * (2 * s) ^ (a - 2) * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he1 (by positivity)) hs0.le
  have hrp : r ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt r := by
    rw [Real.rpow_neg hr0.le, ← Real.sqrt_eq_rpow, one_div]
  have hfinal : a / 64 * r ^ (-(1 / 2) : ℝ) ≤ a / 8 * (2 * s) ^ (-2 : ℝ) * s := by
    rw [he2, hs_eq, hrp,
      show a / 64 * (1 / Real.sqrt r) = a / (64 * Real.sqrt r) by ring,
      show a / 8 * (1 / (8 * r)) * (Real.sqrt 2 * Real.sqrt r)
        = a * Real.sqrt 2 * Real.sqrt r / (64 * r) by ring,
      div_le_div_iff₀ (by positivity) (by positivity),
      show a * Real.sqrt 2 * Real.sqrt r * (64 * Real.sqrt r)
        = 64 * a * Real.sqrt 2 * (Real.sqrt r * Real.sqrt r) by ring,
      Real.mul_self_sqrt hr0.le]
    nlinarith [mul_nonneg (sub_nonneg.mpr hsqrt2_ge) (show (0:ℝ) ≤ 64 * a * r by positivity)]
  calc a / 64 * r ^ (-(1 / 2) : ℝ) * Real.exp (-3 * Real.sqrt r)
      ≤ a / 8 * (2 * s) ^ (a - 2) * s * Real.exp (-3 * Real.sqrt r) :=
        mul_le_mul_of_nonneg_right (hfinal.trans hstep2) (Real.exp_pos _).le
    _ = L * s := by rw [hL_def]; ring

/-- **P4 / Lemma 3.2 lower bound, uniform log-linear form (deviation D5).** Absorbing `|x|^{-1/2}`
into the exponential (`|x|^{-1/2} e^{-3√|x|} ≥ e^{-3-(7/2)√|x|}`) gives a bound with a purely
`√|x|`-linear exponent, valid for **every** `x` (the `|x| < 1` range via monotonicity P2):
`f_{DL,a}(x) ≥ (a/64) · e^{-3 - (7/2)√|x|}`. This is the form consumed by the prior small-ball and
Lemma 6.1 mass estimates (C5, C14). -/
lemma dlDensity_ge
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.2)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1 (lower-bound regime); BPPD §3.1 (Lemma 3.2)
    (ha1 : a ≤ 1) (x : ℝ) :
    ENNReal.ofReal ((a / 64) * Real.exp (-3 - (7 / 2) * Real.sqrt |x|)) ≤ dlDensity a x := by
  rcases le_or_gt 1 |x| with hx | hx
  · -- `|x| ≥ 1`: absorb `|x|^{-1/2}` into the exponential
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) (dlDensity_ge_of_one_le ha ha1 hx)
    set t := Real.sqrt |x| with ht
    have ht1 : (1 : ℝ) ≤ t := by
      rw [ht, show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx
    have ht0 : (0 : ℝ) < t := by linarith
    have hxt : |x| ^ (-(1 / 2) : ℝ) = 1 / t := by
      rw [ht, Real.rpow_neg (abs_nonneg x), ← Real.sqrt_eq_rpow, one_div]
    -- `t ≤ e^{3 + t/2}`
    have hfin : t ≤ Real.exp (3 + t / 2) := by
      have hle2 : t / 2 ≤ Real.exp (t / 2) := by
        have := Real.add_one_le_exp (t / 2); linarith
      have h2e3 : (2 : ℝ) ≤ Real.exp 3 := by have := Real.add_one_le_exp (3 : ℝ); linarith
      rw [Real.exp_add]
      calc t ≤ 2 * Real.exp (t / 2) := by linarith
        _ ≤ Real.exp 3 * Real.exp (t / 2) := mul_le_mul_of_nonneg_right h2e3 (Real.exp_pos _).le
    have key : Real.exp (-3 - 7 / 2 * t) ≤ 1 / t * Real.exp (-3 * t) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ ht0,
        show -3 * t = (-3 - 7 / 2 * t) + (3 + t / 2) by ring, Real.exp_add]
      exact mul_le_mul_of_nonneg_left hfin (Real.exp_pos _).le
    rw [hxt, mul_assoc]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  · -- `|x| < 1`: monotonicity (P2) reduces to the value at `|x| = 1`
    have hmono : dlDensity a 1 ≤ dlDensity a x :=
      dlDensity_anti (by rw [abs_one]; exact le_of_lt hx)
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_)
      (dlDensity_ge_of_one_le ha ha1 (by rw [abs_one]))) hmono
    rw [abs_one, Real.one_rpow, Real.sqrt_one, mul_one, mul_one]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg |x|])

/-! ### P5 — marginal tail bound (BPPD Lemma 3.3; deviation D6) -/

/-- **P5 / Lemma 3.3 (BPPD tail bound).** The DL marginal tail obeys
`ℙ_{DL,a}(|θ| > δ) ≤ (8 + 2 log(1/δ)) / Γ(a)` for every `0 < a ≤ 1`, `0 < δ < 1`.

Deviation **D6**: proved *without* Alzer's inequality. Split the `Gamma`-mixture tail
`∫ e^{-δ/ψ} dGamma_{a,1/2}` at `ψ = 4δ`: the small part is `≤ 4` via `e^{-u} ≤ u^{-(1-a)}`, the large
part is `≤ C + 2 log(1/δ)` via `ψ^{a-1} ≤ max(ψ^{-1}, 1)`. Holds for all `δ ∈ (0,1)` (no "`δ`
small"). `Γ` numerics use `Γ(1+a) ∈ [e^{-1}, 2]` (F2), not the paper's false "`Γ(x) ≥ 1/x`". -/
lemma dlMarginal_abs_gt_le
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.3)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1 (Lemma 3.3)
    (ha1 : a ≤ 1)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold < 1; BPPD §3.1 (Lemma 3.3)
    (hδ1 : δ < 1) :
    dlMarginal a {x | δ < |x|}
      ≤ ENNReal.ofReal ((8 + 2 * Real.log (1 / δ)) / Real.Gamma a) := by
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have h4δ : (0 : ℝ) < 4 * δ := by linarith
  have hlogpos : (0 : ℝ) ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hcoeff : (0 : ℝ) ≤ (2⁻¹ : ℝ) ^ a / Real.Gamma a := by positivity
  -- abbreviation for the (coefficient-free) real integrand
  set G : ℝ → ℝ := fun ψ => ψ ^ (a - 1) * Real.exp (-ψ / 2) * Real.exp (-δ / ψ) with hG
  -- the core `∫⁻ over Ioi 0 of ofReal G` is `≤ ofReal (4δ^a + log(1/δ) + 2)`
  have hbound : ∫⁻ ψ in Set.Ioi 0, ENNReal.ofReal (G ψ) ∂volume
      ≤ ENNReal.ofReal (4 * δ ^ a + Real.log (1 / δ) + 2) := by
    -- split `Ioi 0 = Ioc 0 (4δ) ∪ Ioi (4δ)`
    rw [← Set.Ioc_union_Ioi_eq_Ioi h4δ.le,
      lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
    -- small part: `≤ ofReal (4 δ^a)`
    have hsmall : ∫⁻ ψ in Set.Ioc 0 (4 * δ), ENNReal.ofReal (G ψ) ∂volume
        ≤ ENNReal.ofReal (4 * δ ^ a) := by
      calc ∫⁻ ψ in Set.Ioc 0 (4 * δ), ENNReal.ofReal (G ψ) ∂volume
          ≤ ∫⁻ _ψ in Set.Ioc 0 (4 * δ), ENNReal.ofReal (δ ^ (a - 1)) ∂volume := by
            refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
              (ae_of_all _ fun ψ (hmem : ψ ∈ Set.Ioc 0 (4 * δ)) => ?_))
            have hψ : 0 < ψ := hmem.1
            refine ENNReal.ofReal_le_ofReal ?_
            have he2 : Real.exp (-δ / ψ) ≤ (δ / ψ) ^ (a - 1) := by
              have h := exp_neg_le_rpow_neg (u := δ / ψ) (b := 1 - a) (div_pos hδ hψ)
                (by linarith) (by linarith)
              rwa [show -(1 - a) = a - 1 by ring, show -(δ / ψ) = -δ / ψ by ring] at h
            have hkey : ψ ^ (a - 1) * (δ / ψ) ^ (a - 1) = δ ^ (a - 1) := by
              rw [← Real.mul_rpow hψ.le (div_pos hδ hψ).le,
                show ψ * (δ / ψ) = δ by field_simp]
            calc G ψ = ψ ^ (a - 1) * Real.exp (-ψ / 2) * Real.exp (-δ / ψ) := rfl
              _ ≤ ψ ^ (a - 1) * 1 * (δ / ψ) ^ (a - 1) :=
                  mul_le_mul (mul_le_mul le_rfl (Real.exp_le_one_iff.mpr (by linarith))
                    (Real.exp_pos _).le (Real.rpow_nonneg hψ.le _)) he2
                    (Real.exp_pos _).le (by positivity)
              _ = δ ^ (a - 1) := by rw [mul_one, hkey]
        _ = ENNReal.ofReal (δ ^ (a - 1)) * ENNReal.ofReal (4 * δ) := by
            rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
        _ = ENNReal.ofReal (4 * δ ^ a) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show a - 1 = a + (-1) by ring, Real.rpow_add hδ, Real.rpow_neg_one]
            field_simp
    -- middle part `Ioc (4δ) 1`: `≤ ofReal (log (1/δ))`
    have hmid : ∫⁻ ψ in Set.Ioc (4 * δ) 1, ENNReal.ofReal (G ψ) ∂volume
        ≤ ENNReal.ofReal (Real.log (1 / δ)) := by
      have hstep : ∫⁻ ψ in Set.Ioc (4 * δ) 1, ENNReal.ofReal (G ψ) ∂volume
          ≤ ∫⁻ ψ in Set.Ioc (4 * δ) 1, ENNReal.ofReal ψ⁻¹ ∂volume := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
          (ae_of_all _ fun ψ (hmem : ψ ∈ Set.Ioc (4 * δ) 1) => ?_))
        obtain ⟨hψl, hψu⟩ := hmem
        have hψ0 : 0 < ψ := lt_trans h4δ hψl
        refine ENNReal.ofReal_le_ofReal ?_
        have hnn : (0 : ℝ) ≤ ψ ^ (a - 1) := Real.rpow_nonneg hψ0.le _
        have he1 : Real.exp (-ψ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have he2 : Real.exp (-δ / ψ) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by rw [neg_div]; exact neg_nonpos.mpr (div_pos hδ hψ0).le)
        have e3 : ψ ^ (a - 1) ≤ ψ ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hψ0 hψu (by linarith)
        calc G ψ = ψ ^ (a - 1) * Real.exp (-ψ / 2) * Real.exp (-δ / ψ) := rfl
          _ ≤ ψ ^ (a - 1) * 1 * 1 :=
              mul_le_mul (mul_le_mul le_rfl he1 (Real.exp_pos _).le hnn) he2
                (Real.exp_pos _).le (by positivity)
          _ = ψ ^ (a - 1) := by ring
          _ ≤ ψ ^ (-1 : ℝ) := e3
          _ = ψ⁻¹ := Real.rpow_neg_one ψ
      refine hstep.trans ?_
      rcases le_or_gt (4 * δ) 1 with h41 | h41
      · have hcont : ContinuousOn (fun ψ : ℝ => ψ⁻¹) (Set.Icc (4 * δ) 1) :=
          ContinuousOn.inv₀ continuousOn_id (fun ψ hψ => by
            have : 0 < ψ := lt_of_lt_of_le h4δ hψ.1; exact this.ne')
        have hint : IntegrableOn (fun ψ : ℝ => ψ⁻¹) (Set.Ioc (4 * δ) 1) :=
          (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun ψ hψ =>
            by have : 0 < ψ := lt_trans h4δ hψ.1; positivity))]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← intervalIntegral.integral_of_le h41, integral_inv_of_pos h4δ (by norm_num)]
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff₀ h4δ hδ]; linarith
      · rw [Set.Ioc_eq_empty (by linarith), Measure.restrict_empty, lintegral_zero_measure]
        exact zero_le
    -- far part `Ioi 1`: `≤ ofReal 2`
    have hfar : ∫⁻ ψ in Set.Ioi 1, ENNReal.ofReal (G ψ) ∂volume ≤ ENNReal.ofReal 2 := by
      have hint_exp : IntegrableOn (fun ψ => Real.exp (-ψ / 2)) (Set.Ioi (1 : ℝ)) := by
        have h := integrableOn_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 1
        refine h.congr_fun (fun ψ _ => ?_) measurableSet_Ioi
        beta_reduce; rw [show -1 / 2 * ψ = -ψ / 2 by ring]
      have hval : ∫ ψ in Set.Ioi (1 : ℝ), Real.exp (-ψ / 2) = 2 * Real.exp (-1 / 2) := by
        rw [show (fun ψ : ℝ => Real.exp (-ψ / 2)) = (fun ψ => Real.exp (-1 / 2 * ψ)) by
          funext ψ; rw [show -ψ / 2 = -1 / 2 * ψ by ring]]
        rw [integral_exp_mul_Ioi (show (-1 / 2 : ℝ) < 0 by norm_num) 1,
          show (-1 / 2 : ℝ) * 1 = -1 / 2 by ring]; ring
      calc ∫⁻ ψ in Set.Ioi 1, ENNReal.ofReal (G ψ) ∂volume
          ≤ ∫⁻ ψ in Set.Ioi 1, ENNReal.ofReal (Real.exp (-ψ / 2)) ∂volume := by
            refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
              (ae_of_all _ fun ψ (hψ : (1 : ℝ) < ψ) => ?_))
            have hψ0 : 0 < ψ := by linarith
            refine ENNReal.ofReal_le_ofReal ?_
            have hr1 : ψ ^ (a - 1) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
            have he2 : Real.exp (-δ / ψ) ≤ 1 :=
              Real.exp_le_one_iff.mpr (by rw [neg_div]; exact neg_nonpos.mpr (div_pos hδ hψ0).le)
            calc G ψ = ψ ^ (a - 1) * Real.exp (-ψ / 2) * Real.exp (-δ / ψ) := rfl
              _ ≤ 1 * Real.exp (-ψ / 2) * 1 :=
                  mul_le_mul (mul_le_mul hr1 le_rfl (Real.exp_pos _).le (by norm_num)) he2
                    (Real.exp_pos _).le (by positivity)
              _ = Real.exp (-ψ / 2) := by ring
        _ = ENNReal.ofReal (∫ ψ in Set.Ioi 1, Real.exp (-ψ / 2)) :=
            (ofReal_integral_eq_lintegral_ofReal hint_exp
              (ae_of_all _ fun ψ => (Real.exp_pos _).le)).symm
        _ ≤ ENNReal.ofReal 2 := by
            rw [hval]; refine ENNReal.ofReal_le_ofReal ?_
            nlinarith [Real.exp_le_one_iff.mpr (show (-1 / 2 : ℝ) ≤ 0 by norm_num),
              Real.exp_pos (-1 / 2 : ℝ)]
    -- combine middle + far over `Ioi 4δ`
    have hlarge : ∫⁻ ψ in Set.Ioi (4 * δ), ENNReal.ofReal (G ψ) ∂volume
        ≤ ENNReal.ofReal (Real.log (1 / δ)) + ENNReal.ofReal 2 := by
      refine le_trans (lintegral_mono_set
        (Set.Ioi_subset_Ioc_union_Ioi (a := 4 * δ) (b := 1))) ?_
      exact (lintegral_union_le _ _ _).trans (add_le_add hmid hfar)
    calc _ ≤ ENNReal.ofReal (4 * δ ^ a) + (ENNReal.ofReal (Real.log (1 / δ)) + ENNReal.ofReal 2) :=
          add_le_add hsmall hlarge
      _ = ENNReal.ofReal (4 * δ ^ a + Real.log (1 / δ) + 2) := by
          rw [ENNReal.ofReal_add (add_nonneg (by positivity) hlogpos) (by norm_num : (0:ℝ) ≤ 2),
            ENNReal.ofReal_add (by positivity) hlogpos, add_assoc]
  -- assemble: reduce the tail to `ofReal coeff * hbound`
  rw [dlMarginal_abs_gt_eq_mixture ha hδ.le, gammaMeasure]
  have hgpdf : Measurable (gammaPDF a 2⁻¹) :=
    (ProbabilityTheory.measurable_gammaPDFReal a 2⁻¹).ennreal_ofReal
  have hexpm : Measurable (fun ψ => ENNReal.ofReal (Real.exp (-δ / ψ))) := by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hgpdf hexpm]
  -- restrict to `Ioi 0`
  have h0 : ∫⁻ ψ in Set.Iic 0,
      (gammaPDF a 2⁻¹ * fun ψ => ENNReal.ofReal (Real.exp (-δ / ψ))) ψ ∂volume = 0 := by
    rw [setLIntegral_congr (Iio_ae_eq_Iic (a := (0 : ℝ))).symm,
      setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0)
        (fun ψ (hψ : ψ < 0) => by simp [gammaPDF_of_neg hψ]), lintegral_zero]
  rw [← lintegral_add_compl
      (fun ψ => (gammaPDF a 2⁻¹ * fun ψ => ENNReal.ofReal (Real.exp (-δ / ψ))) ψ)
      measurableSet_Iic,
    h0, zero_add, Set.compl_Iic]
  simp only [Pi.mul_apply]
  rw [setLIntegral_congr_fun measurableSet_Ioi
      (fun ψ (hψ : 0 < ψ) => gammaExp_ennreal ha hψ)]
  simp_rw [ENNReal.ofReal_mul hcoeff]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal ((2⁻¹ : ℝ) ^ a / Real.Gamma a)
        * ∫⁻ ψ in Set.Ioi 0, ENNReal.ofReal (G ψ) ∂volume
      ≤ ENNReal.ofReal ((2⁻¹ : ℝ) ^ a / Real.Gamma a)
        * ENNReal.ofReal (4 * δ ^ a + Real.log (1 / δ) + 2) := by
        exact mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal ((2⁻¹ : ℝ) ^ a / Real.Gamma a * (4 * δ ^ a + Real.log (1 / δ) + 2)) := by
        rw [← ENNReal.ofReal_mul hcoeff]
    _ ≤ ENNReal.ofReal ((8 + 2 * Real.log (1 / δ)) / Real.Gamma a) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show (2⁻¹ : ℝ) ^ a / Real.Gamma a * (4 * δ ^ a + Real.log (1 / δ) + 2)
              = ((2⁻¹ : ℝ) ^ a * (4 * δ ^ a + Real.log (1 / δ) + 2)) / Real.Gamma a by ring,
          div_le_div_iff_of_pos_right hΓ]
        -- `(1/2)^a * (4δ^a + log(1/δ) + 2) ≤ 8 + 2 log(1/δ)`
        have h12 : (2⁻¹ : ℝ) ^ a ≤ 1 :=
          Real.rpow_le_one (by norm_num) (by norm_num) ha.le
        have hδa : δ ^ a ≤ 1 := Real.rpow_le_one hδ.le hδ1.le ha.le
        have hmul : (2⁻¹ : ℝ) ^ a * δ ^ a ≤ 1 := by
          calc (2⁻¹ : ℝ) ^ a * δ ^ a ≤ 1 * 1 :=
                mul_le_mul h12 hδa (Real.rpow_nonneg hδ.le a) (by norm_num)
            _ = 1 := by ring
        nlinarith [hmul, hlogpos, mul_le_of_le_one_left hlogpos h12,
          mul_le_of_le_one_left (show (0 : ℝ) ≤ 2 by norm_num) h12]

/-- **P5 / Lemma 3.3, `ζ`-form.** Bounding `1/Γ(a) ≤ e·a` (`inv_e_mul_le_Gamma`, F2) turns the tail
bound into `ζ(δ) := ℙ_{DL,a}(|θ| > δ) ≤ e·a·(8 + 2 log(1/δ))` — the estimate consumed by the
support-count Chernoff bound (C5) and the reduction of Theorem 3.4 (C15). -/
lemma dlMarginal_abs_gt_le'
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.3)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1 (Lemma 3.3)
    (ha1 : a ≤ 1)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold < 1; BPPD §3.1 (Lemma 3.3)
    (hδ1 : δ < 1) :
    dlMarginal a {x | δ < |x|}
      ≤ ENNReal.ofReal (Real.exp 1 * a * (8 + 2 * Real.log (1 / δ))) := by
  refine le_trans (dlMarginal_abs_gt_le ha ha1 hδ hδ1) (ENNReal.ofReal_le_ofReal ?_)
  have hlog : (0 : ℝ) ≤ 8 + 2 * Real.log (1 / δ) := by
    have : (0 : ℝ) ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    linarith
  have hinv : 1 / Real.Gamma a ≤ Real.exp 1 * a := by
    rw [← one_div_one_div (Real.exp 1 * a)]
    exact one_div_le_one_div_of_le (by positivity) (inv_e_mul_le_Gamma ha ha1)
  calc (8 + 2 * Real.log (1 / δ)) / Real.Gamma a
      = (8 + 2 * Real.log (1 / δ)) * (1 / Real.Gamma a) := by rw [mul_one_div]
    _ ≤ (8 + 2 * Real.log (1 / δ)) * (Real.exp 1 * a) := mul_le_mul_of_nonneg_left hinv hlog
    _ = Real.exp 1 * a * (8 + 2 * Real.log (1 / δ)) := by ring

/-- **P5 / Lemma 3.3, complement (box-mass lower bound).** The DL marginal puts most of its mass in
`[-δ, δ]`: `ℙ_{DL,a}(|θ| ≤ δ) ≥ 1 - e·a·(8 + 2 log(1/δ))`. Complement of `dlMarginal_abs_gt_le'` via
`IsProbabilityMeasure`; feeds the `ℙ(|θ₁| < δ)^{q-|S|}` box correction of Lemma 6.1 (C14). -/
lemma dlMarginal_abs_le_ge
    -- USER-INPUT: nondegenerate DL shape parameter; BPPD §3.1 (Lemma 3.3)
    (ha : 0 < a)
    -- USER-INPUT: shape ≤ 1; BPPD §3.1 (Lemma 3.3)
    (ha1 : a ≤ 1)
    -- USER-INPUT: positive threshold; BPPD §3.1 (Lemma 3.3)
    (hδ : 0 < δ)
    -- USER-INPUT: threshold < 1; BPPD §3.1 (Lemma 3.3)
    (hδ1 : δ < 1) :
    1 - ENNReal.ofReal (Real.exp 1 * a * (8 + 2 * Real.log (1 / δ)))
      ≤ dlMarginal a {x | |x| ≤ δ} := by
  have hmeas : MeasurableSet {x : ℝ | δ < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hcompl : {x : ℝ | |x| ≤ δ} = {x : ℝ | δ < |x|}ᶜ := by
    ext x; simp [not_lt]
  rw [hcompl, prob_compl_eq_one_sub hmeas]
  exact tsub_le_tsub_left (dlMarginal_abs_gt_le' ha ha1 hδ hδ1) 1

end StatLean.Bayesian
