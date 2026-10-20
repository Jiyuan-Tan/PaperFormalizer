module
public import StatLean.NonparametricStatistics.LocalPolynomial.SupNorm.StochasticTerm
public import StatLean.NonparametricStatistics.LocalPolynomial.SupNorm.Increments
public import StatLean.NonparametricStatistics.LocalPolynomial.PointwiseRisk

@[expose] public section

/-!
# Sup-norm rate of the local polynomial estimator

Over the Hölder class `Σ(β, L)` on `[0,1]`, with i.i.d. centered Gaussian noise, a Lipschitz
boxed kernel, and the sup-norm bandwidth `h = α·(log n/n)^{1/(2β+1)}`:
$$ \mathbb E\bigl[\ \|\hat f_n - f\|_\infty^2\ \bigr]
   \;\le\; C\,\Bigl(\frac{\log n}{n}\Bigr)^{\frac{2\beta}{2\beta+1}}, $$
uniformly over the class — the pointwise rate deteriorates by exactly a `log n` factor, the
classical price of the supremum (and this rate is optimal for sup-norm loss).

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.6.2, Theorem 1.8 (sup-norm rate $(\log n /
n)^{\beta/(2\beta+1)}$ of the local polynomial estimator).

**Proof formalization notes.** Split
`‖f̂ − f‖∞² ≤ 2·(sup_t |∑ᵢ ξᵢW*ᵢ(t)|)² + 2·(sup_t |bias(t)|)²`: the bias sup is
`q₁·h^β` pointwise-uniformly (`lp_bias_deterministic`), the stochastic sup is
`C·σ_ξ²·log n/(nh)` (`lp_supnorm_stochastic_le`, whose proof uses
`lp_weight_lipschitz_sum`); substituting the bandwidth balances
`h^{2β} = (log n/n)^{2β/(2β+1)}` against `log n/(nh) = α^{-(2β+1)}·…·(log n/n)^{2β/(2β+1)}`.
The supremum is a genuine `⨆` over `[0,1]`; no measurability is needed since the risk is a
lower Lebesgue integral. The constant is existential with dependence
`(β, L, α, K, λ₀, a₀, σ_ξ)` fixed by binder position.

**Bibliographic comments.** Sup-norm rates with the `(log n/n)^{β/(2β+1)}` phenomenon go back
to I. A. Ibragimov and R. Z. Has'minskii, *Statistical Estimation: Asymptotic Theory*
(Springer, 1981), and C. J. Stone, *Ann. Statist.* **10** (1982), 1040–1053.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.NonparametricStatistics

/-- **Sup-norm rate of LP(`ℓ`) over `Σ(β, L)`** with Gaussian noise and bandwidth
`h = α·(log n/n)^{1/(2β+1)}`: there is `C` (depending only on the displayed fixed parameters)
with `E‖f̂ − f‖∞² ≤ C·(log n/n)^{2β/(2β+1)}` for all admissible `n`, designs, noise, and
`f ∈ Σ(β, L)`. -/
theorem lp_supnorm_rate {β L α : ℝ} {K : ℝ → ℝ} {Kmax lam0 a₀ LK : ℝ} {v : ℝ≥0}
    -- USER-INPUT: class, tuning, and design parameters; classical inputs
    (hβ : 0 < β) (hL : 0 ≤ L) (hα : 0 < α) (hlam : 0 < lam0) (ha₀ : 0 ≤ a₀)
    -- USER-INPUT: kernel bounded and supported in `[−1,1]`; standing kernel assumption
    (hbox : KernelBoxed K Kmax)
    -- USER-INPUT: Lipschitz kernel; the sup-norm analysis input
    (hKlip : ∀ u u' : ℝ, |K u - K u'| ≤ LK * |u - u'|) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ}, 2 ≤ n →
      ∀ {h : ℝ},
        -- LEAN-ONLY: the sup-norm-optimal bandwidth, packaged as an equation
        h = α * (Real.log n / n) ^ ((1 : ℝ) / (2 * β + 1)) →
        -- LEAN-ONLY: side conditions, satisfied for all large `n`
        1 / (2 * (n : ℝ)) ≤ h → h ≤ 1 →
      ∀ {xdat : Fin n → ℝ}, (∀ i, xdat i ∈ Set.Icc (0 : ℝ) 1) →
        DesignEigenvalueLB xdat K h (holderIndex β) lam0 →
        DesignDensityBound xdat a₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ξ : Fin n → Ω → ℝ),
        (∀ i, Measurable (ξ i)) → iIndepFun ξ P →
        (∀ i, HasLaw (ξ i) (gaussianReal 0 v) P) →
      ∀ {f : ℝ → ℝ}, MemHolderOn β L f (Set.Icc 0 1) →
        ∫⁻ ω, ENNReal.ofReal
            ((⨆ t : Set.Icc (0 : ℝ) 1,
              |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ)
                - f (t : ℝ)|) ^ 2) ∂P
          ≤ ENNReal.ofReal (C * (Real.log n / n) ^ (2 * β / (2 * β + 1))) := by
  obtain ⟨Cs, hCspos, hCs⟩ := lp_supnorm_stochastic_le (ℓ := holderIndex β) hlam ha₀ hbox hKlip
  set q₁ : ℝ := lpBiasConst β L Kmax lam0 a₀ with hq₁def
  refine ⟨2 * Cs * (v : ℝ) / α + 2 * q₁ ^ 2 * α ^ (2 * β) + 1, by positivity, ?_⟩
  intro n hn h hform hhl hh1 xdat hx heig hdens Ω _ P _ ξ hξm hξind hξlaw f hf
  have hn0 : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn0
  have hh : 0 < h := lt_of_lt_of_le (div_pos one_pos (mul_pos (by norm_num) hnpos)) hhl
  have hnh : (0 : ℝ) < (n : ℝ) * h := mul_pos hnpos hh
  set r : ℝ := Real.log n / n with hrdef
  have hlognpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hβ1 : (0 : ℝ) < 2 * β + 1 := by linarith
  have hKmax : 0 ≤ Kmax := le_trans (abs_nonneg (K 0)) (hbox.1 0)
  have hCstnn : (0 : ℝ) ≤ lpWeightConst Kmax lam0 a₀ := by
    unfold lpWeightConst
    exact le_trans (div_nonneg (mul_nonneg (by norm_num) hKmax) hlam.le) (le_max_left _ _)
  -- bound of the stochastic term at each `t`, uniformly bounded (for `BddAbove`)
  have hZbdd : ∀ ω, BddAbove (Set.range fun t : Set.Icc (0 : ℝ) 1 =>
      |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) := by
    intro ω
    refine ⟨(∑ i, |ξ i ω|) * lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h), ?_⟩
    rintro _ ⟨t, rfl⟩
    calc |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|
        ≤ ∑ i, |ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, |ξ i ω| * |lpWeight xdat K h (holderIndex β) (t : ℝ) i| := by simp_rw [abs_mul]
      _ ≤ ∑ i, |ξ i ω| * (lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h)) := by
          refine Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
          exact lp_weight_abs_le hn0 hh hlam ha₀ heig hbox t.2 i
      _ = (∑ i, |ξ i ω|) * lpWeightConst Kmax lam0 a₀ / ((n : ℝ) * h) := by
          rw [← Finset.sum_mul]; ring
  -- pointwise bias/stochastic split
  have hpt : ∀ ω (t : Set.Icc (0 : ℝ) 1),
      |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ) - f (t : ℝ)|
        ≤ q₁ * h ^ β + |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i| := by
    intro ω t
    have hsplit :
        lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ) - f (t : ℝ)
        = (∑ i, f (xdat i) * lpWeight xdat K h (holderIndex β) (t : ℝ) i - f (t : ℝ))
          + ∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i := by
      simp only [lpEstimator]
      rw [show (∑ i, (f (xdat i) + ξ i ω) * lpWeight xdat K h (holderIndex β) (t : ℝ) i)
          = (∑ i, f (xdat i) * lpWeight xdat K h (holderIndex β) (t : ℝ) i)
            + ∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i from by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => by ring)]
      ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    gcongr
    exact lp_bias_deterministic hβ hL hn0 hhl hlam ha₀ hx heig hbox hdens hf t.2
  -- squared pointwise bound
  have hptsq : ∀ ω, (⨆ t : Set.Icc (0 : ℝ) 1,
        |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ) - f (t : ℝ)|) ^ 2
      ≤ 2 * (⨆ t : Set.Icc (0 : ℝ) 1,
          |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) ^ 2
        + 2 * (q₁ * h ^ β) ^ 2 := by
    intro ω
    have hbnd : (⨆ t : Set.Icc (0 : ℝ) 1,
          |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ) - f (t : ℝ)|)
        ≤ q₁ * h ^ β + ⨆ t : Set.Icc (0 : ℝ) 1,
            |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i| := by
      apply ciSup_le; intro t
      refine le_trans (hpt ω t) ?_
      gcongr
      exact le_ciSup (hZbdd ω) t
    have hfbdd : BddAbove (Set.range fun t : Set.Icc (0 : ℝ) 1 =>
        |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ) - f (t : ℝ)|) := by
      obtain ⟨B, hB⟩ := hZbdd ω
      refine ⟨q₁ * h ^ β + B, ?_⟩
      rintro _ ⟨t, rfl⟩
      refine le_trans (hpt ω t) ?_
      gcongr
      exact hB ⟨t, rfl⟩
    have hff_nn : 0 ≤ ⨆ t : Set.Icc (0 : ℝ) 1,
        |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ) - f (t : ℝ)| :=
      le_trans (abs_nonneg _)
        (le_ciSup hfbdd (⟨0, Set.mem_Icc.mpr ⟨le_refl 0, zero_le_one⟩⟩ : Set.Icc (0 : ℝ) 1))
    calc (⨆ t : Set.Icc (0 : ℝ) 1, |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h
            (holderIndex β) (t : ℝ) - f (t : ℝ)|) ^ 2
        ≤ (q₁ * h ^ β + ⨆ t : Set.Icc (0 : ℝ) 1,
            |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) ^ 2 :=
          pow_le_pow_left₀ hff_nn hbnd 2
      _ ≤ 2 * (⨆ t : Set.Icc (0 : ℝ) 1,
            |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) ^ 2
          + 2 * (q₁ * h ^ β) ^ 2 := by
          nlinarith [sq_nonneg (q₁ * h ^ β - ⨆ t : Set.Icc (0 : ℝ) 1,
            |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|)]
  -- rpow substitution
  have hqh : 2 * (q₁ * h ^ β) ^ 2 = 2 * q₁ ^ 2 * h ^ (2 * β) := by
    rw [mul_pow, pow_two (h ^ β), ← Real.rpow_add hh, show β + β = 2 * β by ring]; ring
  have hh2b : h ^ (2 * β) = α ^ (2 * β) * r ^ (2 * β / (2 * β + 1)) := by
    rw [hform, Real.mul_rpow hα.le (Real.rpow_nonneg hrpos.le _),
      ← Real.rpow_mul hrpos.le, show 1 / (2 * β + 1) * (2 * β) = 2 * β / (2 * β + 1) by ring]
  have hstep : Real.log n / ((n : ℝ) * h) = r / h := by rw [hrdef]; field_simp
  have hexpE : (1 : ℝ) - 1 / (2 * β + 1) = 2 * β / (2 * β + 1) := by
    rw [eq_div_iff hβ1.ne', sub_mul, one_mul, div_mul_cancel₀ _ hβ1.ne']; ring
  have h2 : 2 * Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h)
      = 2 * Cs * (v : ℝ) / α * r ^ (2 * β / (2 * β + 1)) := by
    rw [show 2 * Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h)
        = 2 * Cs * (v : ℝ) * (Real.log n / ((n : ℝ) * h)) by ring, hstep, hform,
      show r / (α * r ^ (1 / (2 * β + 1))) = α⁻¹ * (r ^ (1 : ℝ) / r ^ (1 / (2 * β + 1))) by
        rw [Real.rpow_one]; ring, ← Real.rpow_sub hrpos, hexpE]
    ring
  -- assemble
  have hCsapp := hCs hn hhl hh1 hx heig hdens P ξ v hξm hξind hξlaw
  have hdbl : (2 : ℝ≥0∞) * ENNReal.ofReal (Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h))
      = ENNReal.ofReal (2 * Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h)) := by
    rw [show 2 * Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h)
        = 2 * (Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h)) by ring,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  calc ∫⁻ ω, ENNReal.ofReal ((⨆ t : Set.Icc (0 : ℝ) 1,
        |lpEstimator xdat (fun i => f (xdat i) + ξ i ω) K h (holderIndex β) (t : ℝ)
          - f (t : ℝ)|) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (2 * (⨆ t : Set.Icc (0 : ℝ) 1,
          |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) ^ 2
        + 2 * (q₁ * h ^ β) ^ 2) ∂P :=
        lintegral_mono (fun ω => ENNReal.ofReal_le_ofReal (hptsq ω))
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (2 * (⨆ t : Set.Icc (0 : ℝ) 1,
          |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) ^ 2)
        + ENNReal.ofReal (2 * (q₁ * h ^ β) ^ 2)) ∂P :=
        lintegral_mono (fun ω => ENNReal.ofReal_add_le)
    _ = ∫⁻ ω, ENNReal.ofReal (2 * (⨆ t : Set.Icc (0 : ℝ) 1,
          |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) ^ 2) ∂P
        + ∫⁻ _ω, ENNReal.ofReal (2 * (q₁ * h ^ β) ^ 2) ∂P :=
        lintegral_add_right _ measurable_const
    _ = 2 * ∫⁻ ω, ENNReal.ofReal ((⨆ t : Set.Icc (0 : ℝ) 1,
          |∑ i, ξ i ω * lpWeight xdat K h (holderIndex β) (t : ℝ) i|) ^ 2) ∂P
        + ENNReal.ofReal (2 * (q₁ * h ^ β) ^ 2) := by
        congr 1
        · rw [lintegral_congr (fun ω => by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]),
            lintegral_const_mul' 2 _ (by simp)]
        · rw [lintegral_const, measure_univ, mul_one]
    _ ≤ 2 * ENNReal.ofReal (Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h))
        + ENNReal.ofReal (2 * (q₁ * h ^ β) ^ 2) :=
        add_le_add (mul_le_mul_right hCsapp 2) (le_refl _)
    _ = ENNReal.ofReal (2 * Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h))
        + ENNReal.ofReal (2 * (q₁ * h ^ β) ^ 2) := by rw [hdbl]
    _ = ENNReal.ofReal (2 * Cs * (v : ℝ) * Real.log n / ((n : ℝ) * h)
        + 2 * (q₁ * h ^ β) ^ 2) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((2 * Cs * (v : ℝ) / α + 2 * q₁ ^ 2 * α ^ (2 * β) + 1)
        * r ^ (2 * β / (2 * β + 1))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hqh, h2, hh2b]
        have hrE : 0 ≤ r ^ (2 * β / (2 * β + 1)) := Real.rpow_nonneg hrpos.le _
        nlinarith [hrE]

end StatLean.NonparametricStatistics
