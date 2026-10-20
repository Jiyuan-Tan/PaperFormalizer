module
public import StatLean.NonparametricStatistics.ForMathlib.GaussianExpSq

@[expose] public section

/-!
# Maximal inequalities via exponential-square moments

* `lintegral_iSup_sq_le_log` — if `E[exp(α₀·ηⱼ²)] ≤ C₀` for `j = 1, …, M`, then
  `E[max_j ηⱼ²] ≤ log(C₀·M)/α₀`. No independence is required.
* `lintegral_iSup_normSq_gaussian_le` — for `M` random vectors in `ℝ^d` whose coordinates are
  centered Gaussians with variances `≤ vmax`:
  `E[max_j ‖ηⱼ‖²] ≤ 4·d·vmax·log(√2·M·d)`.

These are the grid-maximum bounds behind sup-norm risk rates of linear smoothers with Gaussian
noise (the `log n` price of the sup-norm).

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.2, Lemma 1.6 (expected maximum of squares
under exponential-square moments) and Corollary 1.3 (Gaussian vectors).

**Proof formalization notes.** The first bound is Jensen + a union bound inside the logarithm:
`E max ηⱼ² = α₀⁻¹·E log max exp(α₀ηⱼ²) ≤ α₀⁻¹·log E ∑ⱼ exp(α₀ηⱼ²) ≤ α₀⁻¹·log(M·C₀)`.
Note `C₀ ≥ 1` is *derived* (each `E exp(α₀η²) ≥ 1` by Jensen since `E[α₀η²] ≥ 0`), not
assumed. The vector corollary takes `α₀ = 1/(4·vmax)`, applies the Gaussian
exponential-square bound `≤ √2` coordinatewise (`M·d` scalar variables), and uses
`max_j ∑_k η_{jk}² ≤ d·max_{j,k} η_{jk}²`.

**Bibliographic comments.** The `log M` maximal bound from uniform exponential moments is a
classical device in Gaussian process theory and nonparametric sup-norm analysis; see e.g.
W. Härdle, *Applied Nonparametric Regression* (Cambridge, 1990) and standard references on
maxima of Gaussian vectors.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- **Maximal bound from exponential-square moments**: if `E[exp(α₀·ηⱼ²)] ≤ C₀` for each of
the `M ≥ 1` (arbitrarily dependent) variables `ηⱼ`, then
`E[max_j ηⱼ²] ≤ log(C₀·M)/α₀`. -/
theorem lintegral_iSup_sq_le_log {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {M : ℕ}
    -- LEAN-ONLY: at least one variable, so the maximum is over a nonempty family
    (hM : 1 ≤ M)
    {η : Fin M → Ω → ℝ} {α₀ C₀ : ℝ}
    -- USER-INPUT: positive exponent scale; classical input of the maximal bound
    (hα : 0 < α₀)
    -- LEAN-ONLY: measurability of the variables; standard regularity
    (hmeas : ∀ j, Measurable (η j))
    -- USER-INPUT: uniform exponential-square moment bound; classical input
    (hexp : ∀ j, ∫⁻ ω, ENNReal.ofReal (Real.exp (α₀ * (η j ω) ^ 2)) ∂P
      ≤ ENNReal.ofReal C₀) :
    ∫⁻ ω, ENNReal.ofReal (⨆ j, (η j ω) ^ 2) ∂P
      ≤ ENNReal.ofReal (Real.log (C₀ * M) / α₀) := by
  classical
  haveI : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM
  have hα' : 0 ≤ α₀⁻¹ := (inv_pos.mpr hα).le
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM
  -- `C₀ ≥ 1` is derived: each `E[exp(α₀ η²)] ≥ E[1] = 1`.
  have hC₀ : 1 ≤ C₀ := by
    have h1 : (1 : ℝ≥0∞)
        ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (α₀ * (η ⟨0, hM⟩ ω) ^ 2)) ∂P := by
      calc (1 : ℝ≥0∞) = ∫⁻ _, 1 ∂P := by rw [lintegral_const, measure_univ, mul_one]
        _ ≤ _ := lintegral_mono (fun ω => ENNReal.one_le_ofReal.mpr
            (Real.one_le_exp (by positivity)))
    exact ENNReal.one_le_ofReal.mp (h1.trans (hexp ⟨0, hM⟩))
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hcM : (0 : ℝ) < C₀ * M := mul_pos hC₀pos hMpos
  -- The partition function `Z ω = ∑ⱼ exp(α₀ ηⱼ²)`.
  set Z : Ω → ℝ := fun ω => ∑ j, Real.exp (α₀ * (η j ω) ^ 2) with hZ
  have hZmeas : Measurable Z := by fun_prop
  have hZpos : ∀ ω, 0 < Z ω := fun ω =>
    Finset.sum_pos (fun j _ => Real.exp_pos _) Finset.univ_nonempty
  have hg_int : ∀ j, Integrable (fun ω => Real.exp (α₀ * (η j ω) ^ 2)) P := by
    intro j
    rw [← lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le))]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hexp j)
  have hZ_int : Integrable Z P := integrable_finset_sum _ (fun j _ => hg_int j)
  -- `∫ Z ≤ C₀·M` (union bound).
  have hZ_int_le : ∫ ω, Z ω ∂P ≤ C₀ * M := by
    have hlint : ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal (C₀ * M) := by
      calc ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P
          = ∑ j, ∫⁻ ω, ENNReal.ofReal (Real.exp (α₀ * (η j ω) ^ 2)) ∂P := by
            rw [← lintegral_finset_sum _ (fun j _ => by fun_prop)]
            exact lintegral_congr (fun ω =>
              ENNReal.ofReal_sum_of_nonneg (fun j _ => (Real.exp_pos _).le))
        _ ≤ ∑ _j : Fin M, ENNReal.ofReal C₀ := Finset.sum_le_sum (fun j _ => hexp j)
        _ = ENNReal.ofReal (C₀ * M) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_comm]
    have hbridge := (ofReal_integral_eq_lintegral_ofReal hZ_int
      (Filter.Eventually.of_forall (fun ω => (hZpos ω).le))) ▸ hlint
    exact (ENNReal.ofReal_le_ofReal_iff hcM.le).mp hbridge
  -- Pointwise: `⨆ⱼ ηⱼ² ≤ α₀⁻¹·log Z ≤ α₀⁻¹·(log(C₀M) + Z/(C₀M) − 1)`.
  have hSU : ∀ ω, (⨆ j, (η j ω) ^ 2)
      ≤ α₀⁻¹ * (Real.log (C₀ * M) + Z ω / (C₀ * M) - 1) := by
    intro ω
    have hsup_le : (⨆ j, (η j ω) ^ 2) ≤ α₀⁻¹ * Real.log (Z ω) := by
      apply ciSup_le
      intro j
      have hterm : Real.exp (α₀ * (η j ω) ^ 2) ≤ Z ω :=
        Finset.single_le_sum (f := fun k => Real.exp (α₀ * (η k ω) ^ 2))
          (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j)
      have hlog : α₀ * (η j ω) ^ 2 ≤ Real.log (Z ω) := by
        rw [← Real.log_exp (α₀ * (η j ω) ^ 2)]
        exact Real.log_le_log (Real.exp_pos _) hterm
      exact (le_inv_mul_iff₀ hα).mpr hlog
    have htangent : Real.log (Z ω) ≤ Real.log (C₀ * M) + Z ω / (C₀ * M) - 1 := by
      have h := Real.log_le_sub_one_of_pos (div_pos (hZpos ω) hcM)
      rw [Real.log_div (ne_of_gt (hZpos ω)) (ne_of_gt hcM)] at h
      linarith
    exact hsup_le.trans (mul_le_mul_of_nonneg_left htangent hα')
  -- Integrability of the majorant and of the sup.
  have hU_int : Integrable (fun ω => α₀⁻¹ * (Real.log (C₀ * M) + Z ω / (C₀ * M) - 1)) P :=
    ((((integrable_const (Real.log (C₀ * M))).add (hZ_int.div_const (C₀ * M))).sub
      (integrable_const 1))).const_mul α₀⁻¹
  have hSmeas : Measurable (fun ω => ⨆ j, (η j ω) ^ 2) :=
    Measurable.iSup (fun j => (hmeas j).pow_const 2)
  have hSnn : ∀ ω, 0 ≤ ⨆ j, (η j ω) ^ 2 := fun ω =>
    le_ciSup_of_le ((Set.finite_range _).bddAbove) (Classical.arbitrary (Fin M)) (sq_nonneg _)
  have hS_int : Integrable (fun ω => ⨆ j, (η j ω) ^ 2) P :=
    hU_int.mono' hSmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hSnn ω)]; exact hSU ω))
  -- Assemble: `∫ ⨆ ≤ α₀⁻¹·log(C₀M)`.
  have hUeq : ∫ ω, α₀⁻¹ * (Real.log (C₀ * M) + Z ω / (C₀ * M) - 1) ∂P
      = α₀⁻¹ * (Real.log (C₀ * M) + (∫ ω, Z ω ∂P) / (C₀ * M) - 1) := by
    rw [integral_const_mul]
    congr 1
    rw [show (fun ω => Real.log (C₀ * M) + Z ω / (C₀ * M) - 1)
        = (fun ω => (C₀ * M)⁻¹ * Z ω + (Real.log (C₀ * M) - 1)) from by funext ω; ring,
      integral_add (hZ_int.const_mul (C₀ * M)⁻¹) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
    ring
  have hint_S_le : ∫ ω, (⨆ j, (η j ω) ^ 2) ∂P ≤ Real.log (C₀ * M) / α₀ := by
    calc ∫ ω, (⨆ j, (η j ω) ^ 2) ∂P
        ≤ ∫ ω, α₀⁻¹ * (Real.log (C₀ * M) + Z ω / (C₀ * M) - 1) ∂P :=
          integral_mono hS_int hU_int hSU
      _ = α₀⁻¹ * (Real.log (C₀ * M) + (∫ ω, Z ω ∂P) / (C₀ * M) - 1) := hUeq
      _ ≤ α₀⁻¹ * Real.log (C₀ * M) := by
          refine mul_le_mul_of_nonneg_left ?_ hα'
          have : (∫ ω, Z ω ∂P) / (C₀ * M) ≤ 1 := (div_le_one hcM).mpr hZ_int_le
          linarith
      _ = Real.log (C₀ * M) / α₀ := by rw [inv_mul_eq_div]
  rw [← ofReal_integral_eq_lintegral_ofReal hS_int (Filter.Eventually.of_forall hSnn)]
  exact ENNReal.ofReal_le_ofReal hint_S_le

/-- **Expected maximum of squared norms of Gaussian-coordinate vectors**: if each coordinate
`η j · k` of the `M ≥ 1` random vectors in `ℝ^d` (`d ≥ 1`) is a centered Gaussian with
variance at most `vmax`, then `E[max_j ‖ηⱼ‖²] ≤ 4·d·vmax·log(√2·M·d)`.
No independence (within or across vectors) is required. -/
theorem lintegral_iSup_normSq_gaussian_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {M d : ℕ}
    -- LEAN-ONLY: nonempty family and nonzero dimension
    (hM : 1 ≤ M) (hd : 1 ≤ d)
    {η : Fin M → Ω → Fin d → ℝ} {vmax : ℝ≥0}
    -- LEAN-ONLY: measurability of the coordinates; standard regularity
    (hmeas : ∀ j k, Measurable fun ω => η j ω k)
    -- USER-INPUT: each coordinate is a centered Gaussian with variance at most `vmax`;
    -- classical Gaussian-vector input
    (hgauss : ∀ j k, ∃ v : ℝ≥0, v ≤ vmax ∧ HasLaw (fun ω => η j ω k) (gaussianReal 0 v) P) :
    ∫⁻ ω, ENNReal.ofReal (⨆ j, ∑ k, (η j ω k) ^ 2) ∂P
      ≤ ENNReal.ofReal (4 * d * (vmax : ℝ) * Real.log (Real.sqrt 2 * M * d)) := by
  classical
  haveI : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM
  rcases (zero_le (a := vmax)).eq_or_lt with hvmax | hvmax
  · -- `vmax = 0`: every coordinate is a.e. `0`, so both sides vanish.
    have hvz : vmax = 0 := hvmax.symm
    subst hvz
    have hzero : ∀ j k, ∫⁻ ω, ENNReal.ofReal ((η j ω k) ^ 2) ∂P = 0 := by
      intro j k
      obtain ⟨v, hv, hlaw⟩ := hgauss j k
      have hv0 : v = 0 := le_antisymm hv (zero_le (a := v))
      have h := hlaw.lintegral_comp (f := fun x => ENNReal.ofReal (x ^ 2)) (by fun_prop)
      rw [h, hv0, gaussianReal_zero_var, lintegral_dirac]
      simp
    have hsup_le_sum : ∀ ω, (⨆ j, ∑ k, (η j ω k) ^ 2) ≤ ∑ j, ∑ k, (η j ω k) ^ 2 := by
      intro ω
      exact ciSup_le fun j => Finset.single_le_sum (f := fun j => ∑ k, (η j ω k) ^ 2)
        (fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hsum_ofReal : ∀ ω, ∑ j, ∑ k, ENNReal.ofReal ((η j ω k) ^ 2)
        = ENNReal.ofReal (∑ j, ∑ k, (η j ω k) ^ 2) := by
      intro ω
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _)]
      exact Finset.sum_congr rfl fun j _ =>
        (ENNReal.ofReal_sum_of_nonneg fun k _ => sq_nonneg _).symm
    have key : ∫⁻ ω, ENNReal.ofReal (⨆ j, ∑ k, (η j ω k) ^ 2) ∂P = 0 := by
      refine le_antisymm ?_ (zero_le)
      calc ∫⁻ ω, ENNReal.ofReal (⨆ j, ∑ k, (η j ω k) ^ 2) ∂P
          ≤ ∫⁻ ω, ∑ j, ∑ k, ENNReal.ofReal ((η j ω k) ^ 2) ∂P := by
            refine lintegral_mono (fun ω => ?_)
            rw [hsum_ofReal ω]
            exact ENNReal.ofReal_le_ofReal (hsup_le_sum ω)
        _ = ∑ j, ∑ k, ∫⁻ ω, ENNReal.ofReal ((η j ω k) ^ 2) ∂P := by
            rw [lintegral_finset_sum _ (fun j _ => by fun_prop)]
            exact Finset.sum_congr rfl fun j _ =>
              lintegral_finset_sum _ (fun k _ => by fun_prop)
        _ = 0 := by simp [hzero]
    rw [key, show (4 * (d : ℝ) * ((0 : ℝ≥0) : ℝ) * Real.log (Real.sqrt 2 * M * d)) = 0 by simp,
      ENNReal.ofReal_zero]
  · -- `0 < vmax`: reindex `M·d` coordinates and apply `lintegral_iSup_sq_le_log`.
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hd
    have hvpos : (0 : ℝ) < (vmax : ℝ) := by exact_mod_cast hvmax
    have hvne : (vmax : ℝ) ≠ 0 := ne_of_gt hvpos
    set e : Fin M × Fin d ≃ Fin (M * d) := finProdFinEquiv with he
    set η' : Fin (M * d) → Ω → ℝ := fun p ω => η (e.symm p).1 ω (e.symm p).2 with hη'
    set α₀ : ℝ := 1 / (4 * (vmax : ℝ)) with hα₀
    have hα₀pos : 0 < α₀ := by rw [hα₀]; positivity
    have hMd : 1 ≤ M * d := Nat.mul_pos (by omega) (by omega)
    have hη'meas : ∀ p, Measurable (η' p) := fun p => hmeas _ _
    have hSmeas' : Measurable (fun ω => ⨆ p, (η' p ω) ^ 2) :=
      Measurable.iSup (fun p => (hη'meas p).pow_const 2)
    have hη'exp : ∀ p, ∫⁻ ω, ENNReal.ofReal (Real.exp (α₀ * (η' p ω) ^ 2)) ∂P
        ≤ ENNReal.ofReal (Real.sqrt 2) := by
      intro p
      obtain ⟨v, hv, hlaw⟩ := hgauss (e.symm p).1 (e.symm p).2
      have hlaw' : HasLaw (η' p) (gaussianReal 0 v) P := hlaw
      rw [hlaw'.lintegral_comp (f := fun x => ENNReal.ofReal (Real.exp (α₀ * x ^ 2)))
        (by fun_prop)]
      refine lintegral_exp_mul_sq_gaussianReal_le v ?_
      rw [hα₀]
      have hvle : (v : ℝ) ≤ vmax := by exact_mod_cast hv
      calc (1 : ℝ) / (4 * (vmax : ℝ)) * (4 * (v : ℝ))
          ≤ 1 / (4 * (vmax : ℝ)) * (4 * (vmax : ℝ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 1 := by field_simp
    have h3 := lintegral_iSup_sq_le_log (M := M * d) (η := η') hMd hα₀pos hη'meas hη'exp
    have hbdd : ∀ ω, BddAbove (Set.range (fun p => (η' p ω) ^ 2)) :=
      fun ω => (Set.finite_range _).bddAbove
    have hpt : ∀ ω, (⨆ j, ∑ k, (η j ω k) ^ 2) ≤ (d : ℝ) * ⨆ p, (η' p ω) ^ 2 := by
      intro ω
      refine ciSup_le fun j => ?_
      calc ∑ k, (η j ω k) ^ 2 ≤ ∑ _k : Fin d, ⨆ p, (η' p ω) ^ 2 := by
            refine Finset.sum_le_sum (fun k _ => ?_)
            have hcoord : η' (e (j, k)) ω = η j ω k := by
              simp only [hη', Equiv.symm_apply_apply]
            rw [← hcoord]
            exact le_ciSup (hbdd ω) (e (j, k))
        _ = (d : ℝ) * ⨆ p, (η' p ω) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hlogeq : Real.log (Real.sqrt 2 * ((M * d : ℕ) : ℝ))
        = Real.log (Real.sqrt 2 * M * d) := by rw [Nat.cast_mul, ← mul_assoc]
    calc ∫⁻ ω, ENNReal.ofReal (⨆ j, ∑ k, (η j ω k) ^ 2) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal ((d : ℝ) * ⨆ p, (η' p ω) ^ 2) ∂P :=
          lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hpt ω))
      _ = ENNReal.ofReal (d : ℝ) * ∫⁻ ω, ENNReal.ofReal (⨆ p, (η' p ω) ^ 2) ∂P := by
          rw [← lintegral_const_mul (ENNReal.ofReal d) hSmeas'.ennreal_ofReal]
          exact lintegral_congr (fun ω => ENNReal.ofReal_mul (by positivity))
      _ ≤ ENNReal.ofReal (d : ℝ) * ENNReal.ofReal (Real.log (Real.sqrt 2 * ((M * d : ℕ) : ℝ)) / α₀)
          := by gcongr
      _ = ENNReal.ofReal (4 * d * (vmax : ℝ) * Real.log (Real.sqrt 2 * M * d)) := by
          rw [← ENNReal.ofReal_mul (by positivity), hlogeq, hα₀]
          congr 1
          field_simp

end StatLean.NonparametricStatistics
