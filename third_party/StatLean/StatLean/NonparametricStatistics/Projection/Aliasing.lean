module
public import StatLean.NonparametricStatistics.Projection.DiscreteOrthogonality
public import StatLean.NonparametricStatistics.Projection.TrigOrthogonality
public import StatLean.NonparametricStatistics.ForMathlib.TailSumRpow

@[expose] public section

/-!
# Aliasing bounds for Riemann-sum residuals over Sobolev ellipsoids

The Riemann-sum residual `αⱼ` of the coefficient estimate is pure *aliasing*: at the regular
design, the frequencies `1 ≤ m ≤ n − 1` reproduce exactly, so only the coefficient tail
`m ≥ n` leaks:
$$ \max_{1\le j\le n-1} |\alpha_j| \;\le\; 2\!\!\sum_{m \ge n}\!|\theta_m|
   \;\le\; C_{\beta,Q}\, n^{\frac12-\beta} \quad \text{over } \Theta(\beta, Q),\ \beta > 1/2. $$
Also here: membership in an ellipsoid with `β > 1/2` forces absolute summability of the
coefficients — so the summability assumption of the risk decomposition is *derived* on the
ellipsoid, never assumed there.

**Reference.** A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer Series in
Statistics, Springer, New York, 2009. Chapter 1, §1.7.2, Lemma 1.8 (bounds on the aliasing
residuals $\alpha_j$ over the ellipsoid $\Theta(\beta, Q)$).

**Proof formalization notes.** Substituting the (uniformly convergent) series into the design
sum and using discrete orthonormality for `m ≤ n − 1` leaves
`αⱼ = ∑_{m≥n} θ_m·(n⁻¹∑ₛφ_m(s/n)φⱼ(s/n))`, and each averaged product is bounded by `2`
(`|φ| ≤ √2`). Cauchy–Schwarz against the ellipsoid weights plus the p-series tail bound
(`tsum_nat_add_rpow_neg_le`, with `a_m ≥ (m−1)^β`, i.e. `s = 2β`) gives the rate; the
explicit constant is
`residualConst β Q = 2·√Q·√(2β/(2β−1))·3^{β−1/2}` (the `3^{β−1/2}` absorbs the shift
`(n−2) ≥ n/3`, valid for `n ≥ 3`). The ellipsoid-to-`ℓ¹` lemma is Cauchy–Schwarz with the
convergent weight series `∑ a_m^{-2}`.

**Bibliographic comments.** J. Rice, *Ann. Statist.* **12** (1984), 1215–1230; the extension
of discrete orthogonality beyond `n − 1` frequencies is studied in B. T. Polyak and
A. B. Tsybakov, *Theory Probab. Appl.* **35** (1990), 293–306.
-/

open scoped ENNReal

namespace StatLean.NonparametricStatistics

/-! ### Elementary bounds on the Sobolev weight sequence -/

private lemma sobolevWeight_nonneg (β : ℝ) (j : ℕ) : 0 ≤ sobolevWeight β j := by
  unfold sobolevWeight
  split_ifs with h
  · exact Real.rpow_nonneg (Nat.cast_nonneg j) β
  · have hj : 1 ≤ j := by omega
    have : (0 : ℝ) ≤ (j : ℝ) - 1 := by
      have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    exact Real.rpow_nonneg this β

private lemma sobolevWeight_ge (hβ : 0 < β) {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) - 1) ^ β ≤ sobolevWeight β m := by
  have hm1 : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  unfold sobolevWeight
  split_ifs with h
  · exact Real.rpow_le_rpow hm1 (by linarith) hβ.le
  · exact le_refl _

lemma sobolevWeight_pos (hβ : 0 < β) {m : ℕ} (hm : 2 ≤ m) : 0 < sobolevWeight β m := by
  have h := sobolevWeight_ge hβ hm
  have hpos : (0 : ℝ) < ((m : ℝ) - 1) ^ β := by
    apply Real.rpow_pos_of_pos
    have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  linarith

lemma sobolevWeight_ge_of_ge (hβ : 0 < β) {N m : ℕ} (hm : N + 1 ≤ m) (hN : 1 ≤ N) :
    (N : ℝ) ^ β ≤ sobolevWeight β m := by
  have hm2 : 2 ≤ m := by omega
  have h1 := sobolevWeight_ge hβ hm2
  have hle : (N : ℝ) ≤ (m : ℝ) - 1 := by
    have : (N + 1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  exact (Real.rpow_le_rpow (Nat.cast_nonneg N) hle hβ.le).trans h1

/-- The explicit aliasing constant `C_{β,Q} = 2·√Q·√(2β/(2β−1))·3^{β−1/2}` of the residual
bound over the ellipsoid `Θ(β, Q)`. -/
noncomputable def residualConst (β Q : ℝ) : ℝ :=
  2 * Real.sqrt Q * Real.sqrt (2 * β / (2 * β - 1)) * 3 ^ (β - 1 / 2)

/-- **Ellipsoid membership implies absolutely summable coefficients** (for `β > 1/2`):
the summability input of the risk decomposition is derived on the ellipsoid. -/
theorem MemEllipsoid.summable_abs {β Q : ℝ} {θ : ℕ → ℝ}
    -- USER-INPUT: smoothness above one half and nonnegative radius; classical range in
    -- which the ellipsoid embeds into `ℓ¹`
    (hβ : 1 / 2 < β) (hQ : 0 ≤ Q)
    (hθ : MemEllipsoid β Q θ) :
    Summable fun j => |θ j| := by
  have hβ0 : 0 < β := by linarith
  -- summability from `j = 2` onward suffices
  refine (summable_nat_add_iff 2).mp ?_
  -- the two comparison series
  have hB : Summable fun m : ℕ => (sobolevWeight β (m + 2) * θ (m + 2)) ^ 2 :=
    (summable_nat_add_iff 2).mpr hθ.summable
  have hpser : Summable fun m : ℕ => ((1 + m : ℕ) : ℝ) ^ (-(2 * β)) :=
    summable_nat_add_rpow_neg (by linarith : (1 : ℝ) < 2 * β) 1
  -- the inverse-square weight series is dominated by the p-series
  have hwbound : ∀ m : ℕ,
      (sobolevWeight β (m + 2))⁻¹ ^ 2 ≤ ((1 + m : ℕ) : ℝ) ^ (-(2 * β)) := by
    intro m
    set c : ℝ := ((1 + m : ℕ) : ℝ) with hc
    have hcpos : 0 < c := by
      rw [hc]; exact_mod_cast (by omega : 0 < 1 + m)
    have hcw : c ^ β ≤ sobolevWeight β (m + 2) :=
      sobolevWeight_ge_of_ge hβ0 (m := m + 2) (N := 1 + m) (by omega) (by omega)
    have hcbpos : 0 < c ^ β := Real.rpow_pos_of_pos hcpos β
    have hle : (sobolevWeight β (m + 2))⁻¹ ≤ (c ^ β)⁻¹ := inv_anti₀ hcbpos hcw
    have hinv0 : 0 ≤ (sobolevWeight β (m + 2))⁻¹ := inv_nonneg.mpr (sobolevWeight_nonneg β _)
    calc (sobolevWeight β (m + 2))⁻¹ ^ 2 ≤ ((c ^ β)⁻¹) ^ 2 :=
          pow_le_pow_left₀ hinv0 hle 2
      _ = c ^ (-(2 * β)) := by
          rw [(Real.rpow_neg hcpos.le β).symm]
          rw [show ((c ^ (-β)) ^ 2) = c ^ (-β) * c ^ (-β) from by ring,
            ← Real.rpow_add hcpos, show -β + -β = -(2 * β) from by ring]
  have hA : Summable fun m : ℕ => (sobolevWeight β (m + 2))⁻¹ ^ 2 :=
    Summable.of_nonneg_of_le (fun m => by positivity) hwbound hpser
  -- AM–GM comparison for `|θ (m + 2)|`
  have hbound : ∀ m : ℕ, |θ (m + 2)|
      ≤ ((sobolevWeight β (m + 2))⁻¹ ^ 2 + (sobolevWeight β (m + 2) * θ (m + 2)) ^ 2) / 2 := by
    intro m
    have hw0 : 0 < sobolevWeight β (m + 2) := sobolevWeight_pos hβ0 (by omega)
    have hxy : (sobolevWeight β (m + 2))⁻¹ * (sobolevWeight β (m + 2) * |θ (m + 2)|)
        = |θ (m + 2)| := by
      rw [← mul_assoc, inv_mul_cancel₀ hw0.ne', one_mul]
    have hy2 : (sobolevWeight β (m + 2) * |θ (m + 2)|) ^ 2
        = (sobolevWeight β (m + 2) * θ (m + 2)) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    have h := two_mul_le_add_sq (sobolevWeight β (m + 2))⁻¹
      (sobolevWeight β (m + 2) * |θ (m + 2)|)
    rw [mul_assoc, hxy, hy2] at h
    linarith
  refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) hbound ?_
  exact (hA.add hB).div_const 2

/-- The averaged product `n⁻¹ ∑ᵢ φ_k(xᵢ)·φ_j(xᵢ)` of two basis functions at the regular
design — the aliasing coefficient of frequency `k` into frequency `j`. -/
private noncomputable def aliasKernel (n j k : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i)

private lemma aliasKernel_abs_le {n : ℕ} (hn0 : (n : ℝ) ≠ 0) (hnpos : 0 < (n : ℝ))
    (j k : ℕ) : |aliasKernel n j k| ≤ 2 := by
  unfold aliasKernel
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
  have hsum_le : |∑ i : Fin n, trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i)|
      ≤ (n : ℝ) * 2 := by
    calc |∑ i : Fin n, trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i)|
        ≤ ∑ i : Fin n, |trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (2 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul]
          calc |trigBasis k (regularDesign n i)| * |trigBasis j (regularDesign n i)|
              ≤ Real.sqrt 2 * Real.sqrt 2 := by
                gcongr
                · exact trigBasis_abs_le _ _
                · exact trigBasis_abs_le _ _
            _ = 2 := Real.mul_self_sqrt (by norm_num)
      _ = (n : ℝ) * 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc (n : ℝ)⁻¹ * |∑ i : Fin n, trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i)|
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * 2) := by gcongr
    _ = 2 := by rw [← mul_assoc, inv_mul_cancel₀ hn0, one_mul]

/-- **Aliasing bound via the coefficient tail**: for `1 ≤ j ≤ n − 1` and absolutely summable
coefficients, `|αⱼ| ≤ 2·∑_{m≥n}|θ_m|` (re-indexed as a `tsum` over `m ↦ n + m`). -/
theorem riemannResidual_abs_le_tail {θ : ℕ → ℝ} {n j : ℕ}
    (hj : 1 ≤ j) (hj' : j ≤ n - 1)
    -- USER-INPUT: absolutely summable coefficients; the classical summability assumption
    (hθ1 : Summable fun j => |θ j|) :
    |riemannResidual θ n j| ≤ 2 * ∑' m : ℕ, |θ (n + m)| := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnpos : 0 < (n : ℝ) := by positivity
  -- summability of the coefficient series (times `φ j`) at each design point
  have hbk : ∀ (i : Fin n) (k : ℕ),
      |θ k * trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i)| ≤ 2 * |θ k| := by
    intro i k
    rw [abs_mul, abs_mul]
    calc |θ k| * |trigBasis k (regularDesign n i)| * |trigBasis j (regularDesign n i)|
        ≤ |θ k| * Real.sqrt 2 * Real.sqrt 2 := by
          gcongr
          · exact trigBasis_abs_le _ _
          · exact trigBasis_abs_le _ _
      _ = 2 * |θ k| := by rw [mul_assoc, Real.mul_self_sqrt (by norm_num)]; ring
  have hsumfi : ∀ i : Fin n, Summable fun k =>
      θ k * trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i) := by
    intro i
    exact summable_abs_iff.mp
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (hbk i) (hθ1.mul_left 2))
  -- the coefficient product expands as a `tsum` at each design point
  have hexp : ∀ i : Fin n,
      seriesFun θ (regularDesign n i) * trigBasis j (regularDesign n i)
        = ∑' k, θ k * trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i) := by
    intro i; unfold seriesFun; exact (tsum_mul_right).symm
  -- the design average of the coefficient estimate equals `∑' k, θ k · aliasKernel`
  have claimA : (n : ℝ)⁻¹ * ∑ i : Fin n,
      seriesFun θ (regularDesign n i) * trigBasis j (regularDesign n i)
        = ∑' k, θ k * aliasKernel n j k := by
    calc (n : ℝ)⁻¹ * ∑ i : Fin n,
          seriesFun θ (regularDesign n i) * trigBasis j (regularDesign n i)
        = (n : ℝ)⁻¹ * ∑ i : Fin n,
            ∑' k, θ k * trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i) := by
          rw [Finset.sum_congr rfl (fun i _ => hexp i)]
      _ = (n : ℝ)⁻¹ * ∑' k, ∑ i : Fin n,
            θ k * trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i) := by
          rw [← Summable.tsum_finsetSum (fun i _ => hsumfi i)]
      _ = ∑' k, (n : ℝ)⁻¹ * ∑ i : Fin n,
            θ k * trigBasis k (regularDesign n i) * trigBasis j (regularDesign n i) := by
          rw [tsum_mul_left]
      _ = ∑' k, θ k * aliasKernel n j k := by
          refine tsum_congr (fun k => ?_)
          unfold aliasKernel
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
  -- orthonormality collapses the head of the series
  have hortho : ∀ k, 1 ≤ k → k ≤ n - 1 → aliasKernel n j k = if k = j then 1 else 0 :=
    fun k hk hk' => trigBasis_discrete_orthonormal hk hk' hj hj'
  have hK0 : aliasKernel n j 0 = 0 := by
    unfold aliasKernel
    have hz : ∀ i : Fin n,
        trigBasis 0 (regularDesign n i) * trigBasis j (regularDesign n i) = 0 := by
      intro i; simp [trigBasis]
    rw [Finset.sum_congr rfl (fun i _ => hz i), Finset.sum_const, smul_zero, mul_zero]
  -- summability of `k ↦ θ k · aliasKernel`
  have hsummθc : Summable fun k => θ k * aliasKernel n j k := by
    refine summable_abs_iff.mp
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) (hθ1.mul_left 2))
    rw [abs_mul]
    calc |θ k| * |aliasKernel n j k| ≤ |θ k| * 2 :=
          mul_le_mul_of_nonneg_left (aliasKernel_abs_le hn0 hnpos j k) (abs_nonneg _)
      _ = 2 * |θ k| := by ring
  -- the head collapses to `θ j`
  have h0 : ∀ k ∈ Finset.range n, k ≠ j → θ k * aliasKernel n j k = 0 := by
    intro k hk hkj
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [hK0, mul_zero]
    · have hkle : k ≤ n - 1 := by have := Finset.mem_range.mp hk; omega
      rw [hortho k hkpos hkle, if_neg hkj, mul_zero]
  have h1 : j ∉ Finset.range n → θ j * aliasKernel n j j = 0 :=
    fun hjn => absurd (Finset.mem_range.mpr (by omega)) hjn
  have hhead : ∑ k ∈ Finset.range n, θ k * aliasKernel n j k = θ j := by
    rw [Finset.sum_eq_single j h0 h1, hortho j hj hj', if_pos rfl, mul_one]
  -- split the series at `n`
  have hsplit := hsummθc.sum_add_tsum_nat_add n
  rw [hhead] at hsplit
  -- `riemannResidual = ∑' m, θ (m + n) · aliasKernel`
  have hres : riemannResidual θ n j = ∑' m, θ (m + n) * aliasKernel n j (m + n) := by
    unfold riemannResidual
    rw [claimA]
    linarith [hsplit]
  rw [hres]
  -- summability of the tail and of `|θ (m + n)|`
  have hsummtail : Summable fun m => θ (m + n) * aliasKernel n j (m + n) :=
    (summable_nat_add_iff n).mpr hsummθc
  have hθ1shift : Summable fun m => |θ (m + n)| := (summable_nat_add_iff n).mpr hθ1
  have hnormtail : Summable fun m => |θ (m + n) * aliasKernel n j (m + n)| :=
    summable_abs_iff.mpr hsummtail
  calc |∑' m, θ (m + n) * aliasKernel n j (m + n)|
      ≤ ∑' m, |θ (m + n) * aliasKernel n j (m + n)| := by
        have := norm_tsum_le_tsum_norm (f := fun m => θ (m + n) * aliasKernel n j (m + n))
          (by simpa [Real.norm_eq_abs] using hnormtail)
        simpa [Real.norm_eq_abs] using this
    _ ≤ ∑' m, 2 * |θ (m + n)| := by
        refine Summable.tsum_le_tsum (fun m => ?_) hnormtail (hθ1shift.mul_left 2)
        rw [abs_mul]
        calc |θ (m + n)| * |aliasKernel n j (m + n)| ≤ |θ (m + n)| * 2 :=
              mul_le_mul_of_nonneg_left (aliasKernel_abs_le hn0 hnpos j (m + n)) (abs_nonneg _)
          _ = 2 * |θ (m + n)| := by ring
    _ = 2 * ∑' m, |θ (m + n)| := tsum_mul_left
    _ = 2 * ∑' m, |θ (n + m)| := by rw [tsum_congr (fun m => by rw [Nat.add_comm])]

/-- Inverse-square weight bound: `w⁻² ≤ c^{−2β}` whenever `c^β ≤ w` for `c > 0`. -/
lemma inv_sq_weight_le {c w β : ℝ} (hc : 0 < c) (hcw : c ^ β ≤ w) :
    w⁻¹ ^ 2 ≤ c ^ (-(2 * β)) := by
  have hcbpos : 0 < c ^ β := Real.rpow_pos_of_pos hc β
  have hw0 : 0 ≤ w⁻¹ := inv_nonneg.mpr (le_of_lt (lt_of_lt_of_le hcbpos hcw))
  have hle : w⁻¹ ≤ (c ^ β)⁻¹ := inv_anti₀ hcbpos hcw
  calc w⁻¹ ^ 2 ≤ ((c ^ β)⁻¹) ^ 2 := pow_le_pow_left₀ hw0 hle 2
    _ = c ^ (-(2 * β)) := by
        rw [(Real.rpow_neg hc.le β).symm,
          show ((c ^ (-β)) ^ 2) = c ^ (-β) * c ^ (-β) from by ring,
          ← Real.rpow_add hc, show -β + -β = -(2 * β) from by ring]

/-- **Aliasing rate over the Sobolev ellipsoid**: for `θ ∈ Θ(β, Q)` with `β > 1/2`, `n ≥ 3`,
and `1 ≤ j ≤ n − 1`, `|αⱼ| ≤ residualConst β Q · n^{1/2−β}`. -/
theorem riemannResidual_abs_le {β Q : ℝ} {θ : ℕ → ℝ} {n j : ℕ}
    -- USER-INPUT: smoothness above one half and nonnegative radius; classical parameters
    (hβ : 1 / 2 < β) (hQ : 0 ≤ Q)
    -- LEAN-ONLY: `n ≥ 3` so the tail estimate's shifted power is controlled
    (hn : 3 ≤ n)
    (hj : 1 ≤ j) (hj' : j ≤ n - 1)
    (hθ : MemEllipsoid β Q θ) :
    |riemannResidual θ n j| ≤ residualConst β Q * (n : ℝ) ^ ((1 : ℝ) / 2 - β) := by
  have hβ0 : 0 < β := by linarith
  have hs : (1 : ℝ) < 2 * β := by linarith
  have hden : (0 : ℝ) < 2 * β - 1 := by linarith
  have hθ1 : Summable fun j => |θ j| := hθ.summable_abs hβ hQ
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2pos : (0 : ℝ) < (n : ℝ) - 2 := by linarith
  -- weight positivity on the tail
  have hwpos : ∀ m : ℕ, 0 < sobolevWeight β (n + m) := fun m => sobolevWeight_pos hβ0 (by omega)
  -- shorthand sequences
  set u : ℕ → ℝ := fun m => (sobolevWeight β (n + m))⁻¹ with hu
  set v : ℕ → ℝ := fun m => sobolevWeight β (n + m) * |θ (n + m)| with hv
  set a : ℕ → ℝ := fun m => |θ (n + m)| with ha
  have hunn : ∀ m, 0 ≤ u m := fun m => inv_nonneg.mpr (sobolevWeight_nonneg β _)
  have hvnn : ∀ m, 0 ≤ v m := fun m => mul_nonneg (sobolevWeight_nonneg β _) (abs_nonneg _)
  have hauv : ∀ m, a m = u m * v m := by
    intro m; rw [ha, hu, hv, ← mul_assoc, inv_mul_cancel₀ (hwpos m).ne', one_mul]
  -- `∑ u²` : summability and p-series bound
  have hpser : Summable fun m : ℕ => ((n - 1 + m : ℕ) : ℝ) ^ (-(2 * β)) :=
    summable_nat_add_rpow_neg hs (n - 1)
  have hucomp : ∀ m, (u m) ^ 2 ≤ ((n - 1 + m : ℕ) : ℝ) ^ (-(2 * β)) := by
    intro m
    set c : ℝ := ((n - 1 + m : ℕ) : ℝ) with hc
    have hcval : ((n - 1 + m : ℕ) : ℝ) = (n : ℝ) + (m : ℝ) - 1 := by
      rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
    have hcpos : 0 < c := by rw [hc, hcval]; linarith [Nat.cast_nonneg (α := ℝ) m]
    have hcw : c ^ β ≤ sobolevWeight β (n + m) := by
      have hge := sobolevWeight_ge hβ0 (show 2 ≤ n + m by omega)
      have : ((↑(n + m) : ℝ) - 1) = c := by rw [hc, hcval]; push_cast; ring
      rwa [this] at hge
    rw [hu]; exact inv_sq_weight_le hcpos hcw
  have husumm : Summable fun m => (u m) ^ 2 :=
    Summable.of_nonneg_of_le (fun m => sq_nonneg _) hucomp hpser
  have hBu_le : (∑' m, (u m) ^ 2) ≤ 2 * β / (2 * β - 1) * ((n : ℝ) - 2) ^ (1 - 2 * β) := by
    have h1 : (∑' m, (u m) ^ 2) ≤ ∑' m, ((n - 1 + m : ℕ) : ℝ) ^ (-(2 * β)) :=
      Summable.tsum_le_tsum hucomp husumm hpser
    have h2 := tsum_nat_add_rpow_neg_le hs (show 2 ≤ n - 1 by omega)
    have hcast : (((n - 1 : ℕ) : ℝ) - 1) = (n : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
    rw [hcast] at h2
    exact h1.trans h2
  -- `∑ v²` : summability and ellipsoid bound
  have hveq : ∀ m, (v m) ^ 2 = (sobolevWeight β (n + m) * θ (n + m)) ^ 2 := by
    intro m; rw [hv, mul_pow, mul_pow, sq_abs]
  have hvsumm : Summable fun m => (v m) ^ 2 := by
    refine (hθ.summable.comp_injective (add_right_injective n)).congr (fun m => ?_)
    rw [hveq]; rfl
  have hBv_le : (∑' m, (v m) ^ 2) ≤ Q := by
    have hbridge : (∑' m, (v m) ^ 2) = ∑' m, (sobolevWeight β (n + m) * θ (n + m)) ^ 2 :=
      tsum_congr hveq
    rw [hbridge]
    refine le_trans ?_ hθ.tsum_le
    exact Summable.tsum_le_tsum_of_inj (fun m => n + m) (add_right_injective n)
      (fun c _ => sq_nonneg _) (fun m => le_refl _)
      (hθ.summable.comp_injective (add_right_injective n)) hθ.summable
  have hBunn : 0 ≤ ∑' m, (u m) ^ 2 := tsum_nonneg (fun m => sq_nonneg _)
  have hBvnn : 0 ≤ ∑' m, (v m) ^ 2 := tsum_nonneg (fun m => sq_nonneg _)
  -- Cauchy–Schwarz on the tail: `∑ a ≤ √(∑u²)·√(∑v²)`
  have hcs : (∑' m, a m) ≤ Real.sqrt ((∑' m, (u m) ^ 2) * (∑' m, (v m) ^ 2)) := by
    refine Real.tsum_le_of_sum_range_le (fun m => by rw [ha]; exact abs_nonneg _) (fun M => ?_)
    have hnn : 0 ≤ ∑ m ∈ Finset.range M, u m * v m :=
      Finset.sum_nonneg (fun m _ => mul_nonneg (hunn m) (hvnn m))
    rw [Finset.sum_congr rfl (fun m _ => hauv m), Real.le_sqrt hnn (by positivity)]
    calc (∑ m ∈ Finset.range M, u m * v m) ^ 2
        ≤ (∑ m ∈ Finset.range M, (u m) ^ 2) * (∑ m ∈ Finset.range M, (v m) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (∑' m, (u m) ^ 2) * (∑' m, (v m) ^ 2) := by
          apply mul_le_mul
          · exact Summable.sum_le_tsum _ (fun m _ => sq_nonneg _) husumm
          · exact Summable.sum_le_tsum _ (fun m _ => sq_nonneg _) hvsumm
          · exact Finset.sum_nonneg (fun m _ => sq_nonneg _)
          · exact hBunn
  -- numeric assembly
  have hsqrtpow : Real.sqrt (((n : ℝ) - 2) ^ (1 - 2 * β)) = ((n : ℝ) - 2) ^ ((1 : ℝ) / 2 - β) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn2pos.le,
      show (1 - 2 * β) * (1 / 2) = (1 : ℝ) / 2 - β from by ring]
  have hpow_le : ((n : ℝ) - 2) ^ ((1 : ℝ) / 2 - β)
      ≤ 3 ^ (β - 1 / 2) * (n : ℝ) ^ ((1 : ℝ) / 2 - β) := by
    have he : (1 : ℝ) / 2 - β ≤ 0 := by linarith
    have hxy : (n : ℝ) / 3 ≤ (n : ℝ) - 2 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]; linarith
    have h1 : ((n : ℝ) - 2) ^ ((1 : ℝ) / 2 - β) ≤ ((n : ℝ) / 3) ^ ((1 : ℝ) / 2 - β) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hxy he
    have h2 : ((n : ℝ) / 3) ^ ((1 : ℝ) / 2 - β)
        = 3 ^ (β - 1 / 2) * (n : ℝ) ^ ((1 : ℝ) / 2 - β) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
        show -((1 : ℝ) / 2 - β) = β - 1 / 2 from by ring]
      ring
    exact h1.trans (le_of_eq h2)
  -- combine
  have htail := riemannResidual_abs_le_tail hj hj' hθ1
  have hRHSunn : 0 ≤ 2 * β / (2 * β - 1) * ((n : ℝ) - 2) ^ (1 - 2 * β) :=
    mul_nonneg (div_nonneg (by linarith) hden.le) (Real.rpow_nonneg hn2pos.le _)
  have hmono : (∑' m, (u m) ^ 2) * (∑' m, (v m) ^ 2)
      ≤ (2 * β / (2 * β - 1) * ((n : ℝ) - 2) ^ (1 - 2 * β)) * Q :=
    mul_le_mul hBu_le hBv_le hBvnn hRHSunn
  have hsqrt_le : Real.sqrt ((∑' m, (u m) ^ 2) * (∑' m, (v m) ^ 2))
      ≤ Real.sqrt Q * Real.sqrt (2 * β / (2 * β - 1)) * ((n : ℝ) - 2) ^ ((1 : ℝ) / 2 - β) := by
    refine (Real.sqrt_le_sqrt hmono).trans ?_
    rw [show (2 * β / (2 * β - 1) * ((n : ℝ) - 2) ^ (1 - 2 * β)) * Q
          = (Q * (2 * β / (2 * β - 1))) * ((n : ℝ) - 2) ^ (1 - 2 * β) from by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul hQ, hsqrtpow]
  -- final numeric bound
  refine htail.trans ?_
  have ha_eq : (∑' m, a m) = ∑' m, |θ (n + m)| := by rw [ha]
  rw [ha_eq] at hcs ⊢
  have hcoef : 0 ≤ 2 * Real.sqrt Q * Real.sqrt (2 * β / (2 * β - 1)) := by positivity
  calc 2 * ∑' m, |θ (n + m)|
      ≤ 2 * Real.sqrt ((∑' m, (u m) ^ 2) * (∑' m, (v m) ^ 2)) := by linarith [hcs]
    _ ≤ 2 * (Real.sqrt Q * Real.sqrt (2 * β / (2 * β - 1))
          * ((n : ℝ) - 2) ^ ((1 : ℝ) / 2 - β)) := by
        linarith [hsqrt_le]
    _ = (2 * Real.sqrt Q * Real.sqrt (2 * β / (2 * β - 1)))
          * ((n : ℝ) - 2) ^ ((1 : ℝ) / 2 - β) := by
        ring
    _ ≤ (2 * Real.sqrt Q * Real.sqrt (2 * β / (2 * β - 1)))
          * (3 ^ (β - 1 / 2) * (n : ℝ) ^ ((1 : ℝ) / 2 - β)) :=
        mul_le_mul_of_nonneg_left hpow_le hcoef
    _ = residualConst β Q * (n : ℝ) ^ ((1 : ℝ) / 2 - β) := by rw [residualConst]; ring

end StatLean.NonparametricStatistics
