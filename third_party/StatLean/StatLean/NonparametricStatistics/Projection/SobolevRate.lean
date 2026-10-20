module
public import StatLean.NonparametricStatistics.Projection.MISEDecomposition
public import StatLean.NonparametricStatistics.Projection.Aliasing

@[expose] public section

/-!
# MISE rate of the projection estimator over Sobolev classes

Over the Sobolev-ellipsoid class `{f = seriesFun θ : θ ∈ Θ(β, L²/π^{2β})}` (`β ≥ 1`), with
independent centered noise of common second moment `σ_ξ²` at the regular design, the
projection estimator of order `N = ⌈α·n^{1/(2β+1)}⌉` attains
$$ \sup_{f}\ \mathbb E\,\|\hat f_{nN} - f\|_{L^2[0,1]}^2 \;\le\; C\,n^{-\frac{2\beta}{2\beta+1}},
   \qquad C = C(\beta, L, \alpha, \sigma_\xi^2), $$
the same rate as for Hölder pointwise estimation — MISE-optimal over the class.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.2, Theorem 1.9 (MISE rate
$n^{-2\beta/(2\beta+1)}$ of the projection estimator over the Sobolev ellipsoid).

**Proof formalization notes.** Combine the exact decomposition (`proj_mise_decomposition`)
with the three term bounds: the stochastic term `σ_ξ²N/n ≤ σ_ξ²(α+1)·n^{−2β/(2β+1)}` (ceiling
bound `N ≤ αn^{1/(2β+1)} + 1`); the aliasing term
`∑_{j≤N} αⱼ² ≤ N·(residualConst β Q)²·n^{1−2β} = O(n^{1/(2β+1)+1−2β}) = O(n^{−2β/(2β+1)})`
for `β ≥ 1` (`riemannResidual_abs_le`); the tail `ρ_N ≤ Q/a_{N+1}² ≤ Q·N^{−2β}
≤ Q·α^{−2β}·n^{−2β/(2β+1)}` by the ellipsoid and monotonicity of the weights
(`a_{N+1} ≥ N^β`). Absolute summability of `θ` — the input of the decomposition — is derived
on the ellipsoid via `MemEllipsoid.summable_abs` (with `β ≥ 1 > 1/2`), never assumed. The
constant is existential with the stated dependence (binder position); side conditions
`3 ≤ n` and `N ≤ n − 1` hold for all large `n` and are explicit hypotheses of the finite-`n`
statement.

**Bibliographic comments.** Orthogonal-series rates over smoothness classes originate with
N. N. Čencov, *Soviet Math. Dokl.* **3** (1962), 1559–1562; the regular-design regression
form follows J. Rice, *Ann. Statist.* **12** (1984), 1215–1230, and R. Shibata, *Biometrika*
**68** (1981), 45–54; the ellipsoid viewpoint is standard since M. S. Pinsker, *Probl. Inf.
Transm.* **16** (1980), 120–133.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-- **MISE rate of the projection estimator over the Sobolev-ellipsoid class**: with
`N = ⌈α·n^{1/(2β+1)}⌉` there is `C = C(β, L, α, σ_ξ²)` such that for all admissible `n`,
every `θ ∈ Θ(β, L²/π^{2β})`, and every independent centered noise with second moment `σ_ξ²`,
`E‖f̂_{nN} − seriesFun θ‖₂² ≤ C·n^{−2β/(2β+1)}`. -/
theorem proj_sobolev_rate {β L α σξ2 : ℝ}
    -- USER-INPUT: smoothness at least one, positive radius and tuning, nonnegative noise
    -- level; classical parameters
    (hβ : 1 ≤ β) (hL : 0 < L) (hα : 0 < α) (hσ : 0 ≤ σξ2) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n N : ℕ},
        -- LEAN-ONLY: side conditions valid for all large `n`; the finite-`n` form of the
        -- classical asymptotic statement
        3 ≤ n → N = ⌈α * (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1))⌉₊ → N ≤ n - 1 →
      ∀ {θ : ℕ → ℝ},
        MemEllipsoid β (ellipsoidRadius β L) θ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : Fin n → Ω → ℝ),
        (∀ i, Measurable (ξ i)) → iIndepFun ξ P →
        (∀ i, ∫ ω, ξ i ω ∂P = 0) →
        (∀ i, ∫⁻ ω, ENNReal.ofReal ((ξ i ω) ^ 2) ∂P = ENNReal.ofReal σξ2) →
        ∫⁻ ω, (∫⁻ x in Set.Icc (0 : ℝ) 1, ENNReal.ofReal
            ((projEstimator (fun i => seriesFun θ (regularDesign n i) + ξ i ω) N x
              - seriesFun θ x) ^ 2)) ∂P
          ≤ ENNReal.ofReal (C * (n : ℝ) ^ (-(2 * β / (2 * β + 1)))) := by
  have hβ0 : 0 < β := by linarith
  have hβh : (1 : ℝ) / 2 < β := by linarith
  have h2b1 : (0 : ℝ) < 2 * β + 1 := by linarith
  set Q : ℝ := ellipsoidRadius β L with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]; unfold ellipsoidRadius
    exact div_pos (pow_pos hL 2) (Real.rpow_pos_of_pos Real.pi_pos _)
  -- key exponent inequality for the aliasing term (uses `β ≥ 1`)
  have hexpB : (1 : ℝ) / (2 * β + 1) + (1 - 2 * β) ≤ -(2 * β / (2 * β + 1)) := by
    have key : (1 : ℝ) / (2 * β + 1) + 2 * β / (2 * β + 1) = 1 := by
      field_simp; ring
    linarith
  refine ⟨σξ2 * (α + 1) + (residualConst β Q) ^ 2 * (α + 1)
      + Q * α ^ (-(2 * β)) + 1, ?_, ?_⟩
  · have hA0 : 0 ≤ σξ2 * (α + 1) := mul_nonneg hσ (by linarith)
    have hB0 : 0 ≤ (residualConst β Q) ^ 2 * (α + 1) := mul_nonneg (sq_nonneg _) (by linarith)
    have hD0 : 0 ≤ Q * α ^ (-(2 * β)) := mul_nonneg hQpos.le (Real.rpow_nonneg hα.le _)
    linarith
  · intro n N hn hNdef hNn θ hθ Ω instΩ P instP ξ hξm hξi hξ0 hξ2
    have hnpos : 0 < (n : ℝ) := by
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hN1 : 1 ≤ N := by
      rw [hNdef]
      exact Nat.one_le_ceil_iff.mpr (mul_pos hα (Real.rpow_pos_of_pos hnpos _))
    have hθ1 : Summable fun j => |θ j| := hθ.summable_abs hβh hQpos.le
    have hdecomp := proj_mise_decomposition hN1 hNn hσ hθ1 hξm hξi hξ0 hξ2
    rw [hdecomp]
    apply ENNReal.ofReal_le_ofReal
    set ρ : ℝ := -(2 * β / (2 * β + 1)) with hρdef
    have hρpos : 0 < (n : ℝ) ^ ρ := Real.rpow_pos_of_pos hnpos _
    set t : ℝ := (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) with ht
    have htpos : 0 < t := Real.rpow_pos_of_pos hnpos _
    have ht1 : 1 ≤ t := Real.one_le_rpow hn1 (by positivity)
    have hNle : (N : ℝ) ≤ α * t + 1 := by
      rw [hNdef]; exact le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have hNge : α * t ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
    have hexpA : t / (n : ℝ) = (n : ℝ) ^ ρ := by
      rw [ht, div_eq_mul_inv, ← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hnpos, hρdef]
      congr 1; field_simp; ring
    have hinv_le : (n : ℝ)⁻¹ ≤ (n : ℝ) ^ ρ := by
      rw [← Real.rpow_neg_one (n : ℝ)]
      apply Real.rpow_le_rpow_of_exponent_le hn1
      rw [hρdef]
      have : 2 * β / (2 * β + 1) ≤ 1 := by rw [div_le_one h2b1]; linarith
      linarith
    -- Term A: stochastic
    have hA : σξ2 * (N : ℝ) / (n : ℝ) ≤ σξ2 * (α + 1) * (n : ℝ) ^ ρ := by
      have hNdiv : (N : ℝ) * (n : ℝ)⁻¹ ≤ (α + 1) * (n : ℝ) ^ ρ := by
        calc (N : ℝ) * (n : ℝ)⁻¹ ≤ (α * t + 1) * (n : ℝ)⁻¹ :=
              mul_le_mul_of_nonneg_right hNle (inv_nonneg.mpr hnpos.le)
          _ = α * (t * (n : ℝ)⁻¹) + (n : ℝ)⁻¹ := by ring
          _ = α * (n : ℝ) ^ ρ + (n : ℝ)⁻¹ := by rw [← div_eq_mul_inv, hexpA]
          _ ≤ α * (n : ℝ) ^ ρ + (n : ℝ) ^ ρ := by linarith [hinv_le]
          _ = (α + 1) * (n : ℝ) ^ ρ := by ring
      rw [mul_div_assoc, div_eq_mul_inv]
      calc σξ2 * ((N : ℝ) * (n : ℝ)⁻¹) ≤ σξ2 * ((α + 1) * (n : ℝ) ^ ρ) :=
            mul_le_mul_of_nonneg_left hNdiv hσ
        _ = σξ2 * (α + 1) * (n : ℝ) ^ ρ := by ring
    -- Term B: aliasing
    have hB : (∑ j ∈ Finset.Icc 1 N, (riemannResidual θ n j) ^ 2)
        ≤ (residualConst β Q) ^ 2 * (α + 1) * (n : ℝ) ^ ρ := by
      have hterm : ∀ j ∈ Finset.Icc 1 N,
          (riemannResidual θ n j) ^ 2 ≤ (residualConst β Q) ^ 2 * (n : ℝ) ^ (1 - 2 * β) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        have hjle : j ≤ n - 1 := le_trans hj.2 hNn
        have hres := riemannResidual_abs_le hβh hQpos.le hn hj.1 hjle hθ
        have hsq : (riemannResidual θ n j) ^ 2
            ≤ (residualConst β Q * (n : ℝ) ^ ((1 : ℝ) / 2 - β)) ^ 2 := by
          rw [← sq_abs (riemannResidual θ n j)]
          exact pow_le_pow_left₀ (abs_nonneg _) hres 2
        calc (riemannResidual θ n j) ^ 2
            ≤ (residualConst β Q * (n : ℝ) ^ ((1 : ℝ) / 2 - β)) ^ 2 := hsq
          _ = (residualConst β Q) ^ 2 * (n : ℝ) ^ (1 - 2 * β) := by
              rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 2 - β)) 2,
                ← Real.rpow_mul hnpos.le,
                show ((1 : ℝ) / 2 - β) * ((2 : ℕ) : ℝ) = 1 - 2 * β from by push_cast; ring]
      have hcard : (∑ j ∈ Finset.Icc 1 N, (riemannResidual θ n j) ^ 2)
          ≤ (Finset.Icc 1 N).card • ((residualConst β Q) ^ 2 * (n : ℝ) ^ (1 - 2 * β)) :=
        Finset.sum_le_card_nsmul _ _ _ hterm
      rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hcard
      have hNt : (N : ℝ) ≤ (α + 1) * t := by nlinarith [hNle, ht1, hα]
      have htpow : t * (n : ℝ) ^ (1 - 2 * β) ≤ (n : ℝ) ^ ρ := by
        rw [ht, ← Real.rpow_add hnpos]
        apply Real.rpow_le_rpow_of_exponent_le hn1
        rw [hρdef]; exact hexpB
      calc (∑ j ∈ Finset.Icc 1 N, (riemannResidual θ n j) ^ 2)
          ≤ (N : ℝ) * ((residualConst β Q) ^ 2 * (n : ℝ) ^ (1 - 2 * β)) := hcard
        _ ≤ ((α + 1) * t) * ((residualConst β Q) ^ 2 * (n : ℝ) ^ (1 - 2 * β)) :=
            mul_le_mul_of_nonneg_right hNt (by positivity)
        _ = (residualConst β Q) ^ 2 * (α + 1) * (t * (n : ℝ) ^ (1 - 2 * β)) := by ring
        _ ≤ (residualConst β Q) ^ 2 * (α + 1) * (n : ℝ) ^ ρ :=
            mul_le_mul_of_nonneg_left htpow (mul_nonneg (sq_nonneg _) (by linarith))
    -- Term C: bias tail
    have hC : tailEnergy θ N ≤ Q * α ^ (-(2 * β)) * (n : ℝ) ^ ρ := by
      have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN1
      have hwtail : Summable fun m => (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2 :=
        hθ.summable.comp_injective (add_right_injective (N + 1))
      have hcompC : ∀ m, θ (N + 1 + m) ^ 2
          ≤ (N : ℝ) ^ (-(2 * β)) * (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2 := by
        intro m
        have hw'pos : 0 < sobolevWeight β (N + 1 + m) := sobolevWeight_pos hβ0 (by omega)
        have hNw : (N : ℝ) ^ β ≤ sobolevWeight β (N + 1 + m) :=
          sobolevWeight_ge_of_ge hβ0 (by omega) hN1
        have hidentity : (sobolevWeight β (N + 1 + m))⁻¹ ^ 2
            * (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2 = θ (N + 1 + m) ^ 2 := by
          rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hw'pos.ne', one_pow, one_mul]
        calc θ (N + 1 + m) ^ 2 = (sobolevWeight β (N + 1 + m))⁻¹ ^ 2
              * (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2 := hidentity.symm
          _ ≤ (N : ℝ) ^ (-(2 * β)) * (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2 :=
              mul_le_mul_of_nonneg_right (inv_sq_weight_le hNpos hNw) (sq_nonneg _)
      have htailsumm : Summable fun m => θ (N + 1 + m) ^ 2 :=
        Summable.of_nonneg_of_le (fun m => sq_nonneg _) hcompC (hwtail.mul_left _)
      have hstep1 : tailEnergy θ N
          ≤ (N : ℝ) ^ (-(2 * β)) * ∑' m, (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2 := by
        unfold tailEnergy
        rw [← tsum_mul_left]
        exact Summable.tsum_le_tsum hcompC htailsumm (hwtail.mul_left _)
      have hstep2 : (∑' m, (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2) ≤ Q := by
        refine le_trans ?_ hθ.tsum_le
        exact Summable.tsum_le_tsum_of_inj (fun m => N + 1 + m) (add_right_injective (N + 1))
          (fun c _ => sq_nonneg _) (fun m => le_refl _) hwtail hθ.summable
      have hNexp : (N : ℝ) ^ (-(2 * β)) ≤ α ^ (-(2 * β)) * (n : ℝ) ^ ρ := by
        have hαt : 0 < α * t := mul_pos hα htpos
        have h1 : (N : ℝ) ^ (-(2 * β)) ≤ (α * t) ^ (-(2 * β)) :=
          Real.rpow_le_rpow_of_nonpos hαt hNge (by linarith)
        have h2 : (α * t) ^ (-(2 * β)) = α ^ (-(2 * β)) * (n : ℝ) ^ ρ := by
          rw [Real.mul_rpow hα.le htpos.le, ht, ← Real.rpow_mul hnpos.le, hρdef,
            show (1 : ℝ) / (2 * β + 1) * (-(2 * β)) = -(2 * β / (2 * β + 1)) from by ring]
        rw [h2] at h1; exact h1
      calc tailEnergy θ N
          ≤ (N : ℝ) ^ (-(2 * β)) * ∑' m, (sobolevWeight β (N + 1 + m) * θ (N + 1 + m)) ^ 2 :=
            hstep1
        _ ≤ (N : ℝ) ^ (-(2 * β)) * Q :=
            mul_le_mul_of_nonneg_left hstep2 (Real.rpow_nonneg hNpos.le _)
        _ ≤ (α ^ (-(2 * β)) * (n : ℝ) ^ ρ) * Q :=
            mul_le_mul_of_nonneg_right hNexp hQpos.le
        _ = Q * α ^ (-(2 * β)) * (n : ℝ) ^ ρ := by ring
    -- combine
    have hdist : (σξ2 * (α + 1) + (residualConst β Q) ^ 2 * (α + 1)
          + Q * α ^ (-(2 * β)) + 1) * (n : ℝ) ^ ρ
        = σξ2 * (α + 1) * (n : ℝ) ^ ρ + (residualConst β Q) ^ 2 * (α + 1) * (n : ℝ) ^ ρ
          + Q * α ^ (-(2 * β)) * (n : ℝ) ^ ρ + (n : ℝ) ^ ρ := by ring
    rw [hdist]
    linarith [hA, hB, hC, hρpos]

end StatLean.NonparametricStatistics

