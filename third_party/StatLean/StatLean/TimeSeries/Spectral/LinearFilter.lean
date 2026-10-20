module
public import StatLean.TimeSeries.Spectral.SpectralDensity

@[expose] public section

/-!
# Linear filters and the input–output spectral relation (FY §2.3.3, Theorem 2.12)

**Definition 2.7** (two-sided linear filter with `ℓ¹` coefficients, as an `L²`-limit —
the convergence mode FY leaves implicit), the **transfer function**
`Γ(λ) = Σ_{k ∈ ℤ} φ_k e^{−ikλ}`, and **FY Theorem 2.12** with the inventory's
hypothesis-discipline upgrades: for a stationary input with summable ACVF and an `ℓ¹`
filter, the output is stationary (derived, not assumed), its ACVF is the double
convolution `γ_X(k) = Σ_{j,l} φ_j φ_l γ_Y(k + j − l)` and is summable (derived — FY
assumes it), and the spectral densities satisfy `g_X = |Γ|² g_Y` pointwise.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.3,
Definition 2.7 (eqs. (2.41)–(2.42)), Theorem 2.12 with in-text proof (pp. 55–56).
(`FY §2.3.3 Def 2.7, Thm 2.12`.)

**Proof formalization notes.** Well-definedness (existence of the `L²`-limits) mirrors
the one-sided `Process/LinearProcess.lean` development with two-sided symmetric partial
sums `Σ_{|k| ≤ N}`; the ACVF convolution passes `L²`-continuity of covariance through
the double series (Fubini for absolutely convergent double sums,
`Summable.tsum_comm`-family); the density identity is the triple-series rearrangement of
FY's proof, executed on the series side of `spectralDensityOf`.

**Bibliographic comments.** Linear filtering of stationary processes is classical
Wiener–Kolmogorov theory; FY follow Brockwell & Davis (1991), Thm 4.4.1.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Two-sided linear filter** (FY Definition 2.7, eq. (2.41)): `X_t = Σ_{k ∈ ℤ} φ_k
Y_{t−k}` as an `L²`-limit of the symmetric partial sums. -/
def IsFilteredBy (X Y : ℤ → Ω → ℝ) (φ : ℤ → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N : ℕ => eLpNorm
      (fun ω => X t ω - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ k * Y (t - k) ω) 2 μ)
    atTop (nhds 0)

/-- The **transfer function** `Γ(λ) = Σ_{k ∈ ℤ} φ_k e^{−ikλ}` (FY §2.3.3; junk when
`φ ∉ ℓ¹` by the `tsum` convention). -/
noncomputable def transferFun (φ : ℤ → ℝ) (l : AddCircle (2 * π)) : ℂ :=
  ∑' k : ℤ, (φ k : ℂ) * fourier (-k) l

section Aux

variable {Y : ℤ → Ω → ℝ} {φ : ℤ → ℝ}

/-- `inner ℝ` on the reals is multiplication. -/
private lemma real_inner_mul (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²` inner product of two classes is the integral of the product. -/
private lemma inner_toLp {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul, h1, h2]

/-- The symmetric partial sum `Σ_{|k| ≤ N} φ_k Y_{t−k}` of the filter. -/
private noncomputable def fpsum (φ : ℤ → ℝ) (Y : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ k * Y (t - k) ω

private lemma memLp_fpsum (hY : IsStationary Y μ) (t : ℤ) (N : ℕ) :
    MemLp (fpsum φ Y t N) 2 μ :=
  memLp_finset_sum _ fun k _ => (hY.memLp (t - k)).const_mul (φ k)

private noncomputable def fpsumLp (hY : IsStationary Y μ) (φ : ℤ → ℝ) (t : ℤ) (N : ℕ) :
    Lp ℝ 2 μ := (memLp_fpsum (φ := φ) hY t N).toLp _

private lemma coeFn_fpsumLp (hY : IsStationary Y μ) (φ : ℤ → ℝ) (t : ℤ) (N : ℕ) :
    ⇑(fpsumLp hY φ t N) =ᵐ[μ] fpsum φ Y t N :=
  (memLp_fpsum (φ := φ) hY t N).coeFn_toLp

/-- The second moment of the input does not depend on time. -/
private lemma integral_sq_stationary [IsProbabilityMeasure μ] (hY : IsStationary Y μ) (s : ℤ) :
    ∫ ω, Y s ω * Y s ω ∂μ = acvf Y μ 0 + (∫ ω, Y 0 ω ∂μ) ^ 2 := by
  have h := covariance_eq_sub (hY.memLp s) (hY.memLp s)
  have hcov : cov[Y s, Y s; μ] = acvf Y μ 0 := by
    have h1 := hY.cov_eq_acvf s s
    rwa [sub_self] at h1
  have hmul : μ[Y s * Y s] = ∫ ω, Y s ω * Y s ω ∂μ := by simp [Pi.mul_apply]
  rw [hcov, hmul, hY.integral_eq s 0] at h
  have hsq : (∫ ω, Y 0 ω ∂μ) ^ 2 = (∫ ω, Y 0 ω ∂μ) * (∫ ω, Y 0 ω ∂μ) := sq _
  linarith

/-- The common `L²` norm of the input marginals. -/
private noncomputable def inputNorm (Y : ℤ → Ω → ℝ) (μ : Measure Ω) : ℝ :=
  Real.sqrt (acvf Y μ 0 + (∫ ω, Y 0 ω ∂μ) ^ 2)

private lemma norm_YLp [IsProbabilityMeasure μ] (hY : IsStationary Y μ) (s : ℤ) :
    ‖(hY.memLp s).toLp (Y s)‖ = inputNorm Y μ := by
  have h : ‖(hY.memLp s).toLp (Y s)‖ ^ 2 = acvf Y μ 0 + (∫ ω, Y 0 ω ∂μ) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp, integral_sq_stationary hY s]
  have h2 := Real.sqrt_sq (norm_nonneg ((hY.memLp s).toLp (Y s)))
  rw [h] at h2
  exact h2.symm

private lemma Icc_int_succ (N : ℕ) :
    Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)
      = insert (-((N : ℤ) + 1)) (insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ))) := by
  ext m
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- Passing from `N` to `N + 1` adds the two extreme terms. -/
private lemma fpsum_succ (φ : ℤ → ℝ) (Y : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) (ω : Ω) :
    fpsum φ Y t (N + 1) ω
      = φ (-((N : ℤ) + 1)) * Y (t + ((N : ℤ) + 1)) ω
        + (φ ((N : ℤ) + 1) * Y (t - ((N : ℤ) + 1)) ω + fpsum φ Y t N ω) := by
  simp only [fpsum]
  rw [show ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 by push_cast; ring, Icc_int_succ N,
    Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  rw [show t - -((N : ℤ) + 1) = t + ((N : ℤ) + 1) by ring]

private lemma fpsumLp_succ (hY : IsStationary Y μ) (φ : ℤ → ℝ) (t : ℤ) (N : ℕ) :
    fpsumLp hY φ t (N + 1)
      = φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
        + (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))
          + fpsumLp hY φ t N) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_fpsumLp hY φ t (N + 1), coeFn_fpsumLp hY φ t N,
    Lp.coeFn_add (φ (-((N : ℤ) + 1)) •
        (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1))))
      (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))
        + fpsumLp hY φ t N),
    Lp.coeFn_add (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1))))
      (fpsumLp hY φ t N),
    Lp.coeFn_smul (φ (-((N : ℤ) + 1)))
      ((hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))),
    Lp.coeFn_smul (φ ((N : ℤ) + 1))
      ((hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))),
    (hY.memLp (t + ((N : ℤ) + 1))).coeFn_toLp, (hY.memLp (t - ((N : ℤ) + 1))).coeFn_toLp]
    with ω h1 h2 h3 h4 h5 h6 h7 h8
  simp only [h1, h3, h4, h5, h6, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h7, h8, h2]
  exact fpsum_succ φ Y t N ω

private lemma dist_fpsumLp_succ [IsProbabilityMeasure μ] (hY : IsStationary Y μ) (φ : ℤ → ℝ)
    (t : ℤ) (N : ℕ) :
    dist (fpsumLp hY φ t N) (fpsumLp hY φ t (N + 1))
      ≤ (|φ (-((N : ℤ) + 1))| + |φ ((N : ℤ) + 1)|) * inputNorm Y μ := by
  rw [dist_comm, dist_eq_norm, fpsumLp_succ]
  have hcancel : (φ (-((N : ℤ) + 1)) •
        (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
      + (φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))
        + fpsumLp hY φ t N)) - fpsumLp hY φ t N
      = φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
        + φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1))) := by
    abel
  rw [hcancel]
  calc ‖φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))
          + φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))‖
      ≤ ‖φ (-((N : ℤ) + 1)) • (hY.memLp (t + ((N : ℤ) + 1))).toLp (Y (t + ((N : ℤ) + 1)))‖
        + ‖φ ((N : ℤ) + 1) • (hY.memLp (t - ((N : ℤ) + 1))).toLp (Y (t - ((N : ℤ) + 1)))‖ :=
        norm_add_le _ _
    _ = (|φ (-((N : ℤ) + 1))| + |φ ((N : ℤ) + 1)|) * inputNorm Y μ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_YLp hY,
          norm_YLp hY]
        ring

private lemma summable_shift_pos (hφ : Summable fun k : ℤ => |φ k|) :
    Summable fun N : ℕ => |φ ((N : ℤ) + 1)| :=
  hφ.comp_injective (fun a b hab => by omega)

private lemma summable_shift_neg (hφ : Summable fun k : ℤ => |φ k|) :
    Summable fun N : ℕ => |φ (-((N : ℤ) + 1))| :=
  hφ.comp_injective (fun a b hab => by omega)

end Aux

/-- **Existence of the filtered process** (the well-definedness FY glosses): an `ℓ¹`
filter applied to a weakly stationary input admits an `L²` output. -/
theorem exists_isFilteredBy [IsProbabilityMeasure μ] {Y : ℤ → Ω → ℝ} {φ : ℤ → ℝ}
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hmeas : ∀ t, Measurable (Y t)) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧ IsFilteredBy X Y φ μ := by
  have main : ∀ t : ℤ, ∃ f : Ω → ℝ, Measurable f ∧
      Tendsto (fun N => eLpNorm (fun ω => f ω - fpsum φ Y t N ω) 2 μ) atTop (nhds 0) := by
    intro t
    have hsum : Summable fun N : ℕ => dist (fpsumLp hY φ t N) (fpsumLp hY φ t N.succ) := by
      refine Summable.of_nonneg_of_le (fun N => dist_nonneg)
        (fun N => dist_fpsumLp_succ hY φ t N) ?_
      exact ((summable_shift_neg hφ).add (summable_shift_pos hφ)).mul_right _
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
    refine ⟨(Lp.aestronglyMeasurable L).mk _,
      (Lp.aestronglyMeasurable L).stronglyMeasurable_mk.measurable, ?_⟩
    have heq : ∀ N : ℕ,
        eLpNorm (fun ω => ((Lp.aestronglyMeasurable L).mk _) ω - fpsum φ Y t N ω) 2 μ
          = edist (fpsumLp hY φ t N) L := by
      intro N
      rw [edist_comm, Lp.edist_def]
      refine eLpNorm_congr_ae ?_
      filter_upwards [(Lp.aestronglyMeasurable L).ae_eq_mk, coeFn_fpsumLp hY φ t N]
        with ω h1 h2
      simp only [Pi.sub_apply, ← h1, h2]
    simp_rw [heq, edist_dist]
    simpa using ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.mp hL)
  choose X hXm hXlim using main
  exact ⟨X, hXm, hXlim⟩

section Aux2

variable {Y : ℤ → Ω → ℝ} {φ : ℤ → ℝ}

/-- The finite-window covariance of two partial sums is the finite double convolution. -/
private lemma covariance_fpsum [IsProbabilityMeasure μ] (hY : IsStationary Y μ)
    (φ : ℤ → ℝ) (s t : ℤ) (N : ℕ) :
    cov[fpsum φ Y s N, fpsum φ Y t N; μ]
      = ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ l ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          φ j * φ l * acvf Y μ (s - t + j - l) := by
  have hfun : ∀ u : ℤ, fpsum φ Y u N
      = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), (fun ω => φ k * Y (u - k) ω) := by
    intro u
    funext ω
    simp [fpsum, Finset.sum_apply]
  rw [hfun s, hfun t, covariance_sum_sum'
    (fun k _ => (hY.memLp (s - k)).const_mul (φ k))
    (fun k _ => (hY.memLp (t - k)).const_mul (φ k))]
  have hterm : ∀ j l : ℤ, cov[fun ω => φ j * Y (s - j) ω, fun ω => φ l * Y (t - l) ω; μ]
      = φ j * φ l * acvf Y μ (s - j - (t - l)) := by
    intro j l
    rw [covariance_const_mul_left, covariance_const_mul_right, hY.cov_eq_acvf, ← mul_assoc]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => hterm j l]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  rw [show s - x - (t - y) = s - t + y - x by ring]
  ring

/-- The double-convolution family is absolutely summable on `ℤ × ℤ`. -/
private lemma summable_convProd [IsProbabilityMeasure μ] (hY : IsStationary Y μ)
    (hφ : Summable fun k => |φ k|) (k : ℤ) :
    Summable fun p : ℤ × ℤ => φ p.1 * φ p.2 * acvf Y μ (k + p.1 - p.2) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun p => norm_nonneg _)
    (fun p => ?_)
    ((hφ.mul_of_nonneg hφ (fun i => abs_nonneg (φ i)) (fun i => abs_nonneg (φ i))).mul_right
      (acvf Y μ 0)))
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hY.abs_acvf_le _) (by positivity)

/-- The symmetric square windows exhaust `ℤ × ℤ`. -/
private lemma tendsto_IccProd :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ))
      atTop atTop := by
  refine tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun p => ?_)
  · have hab' : (a : ℤ) ≤ (b : ℤ) := by exact_mod_cast hab
    refine Finset.subset_iff.mpr fun q hq => ?_
    simp only [Finset.mem_product, Finset.mem_Icc] at hq ⊢
    omega
  · refine ⟨max p.1.natAbs p.2.natAbs, ?_⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    omega

end Aux2

/-- **FY Theorem 2.12, stationarity + ACVF convolution** (output stationarity and the
double-convolution formula, both *derived* — FY assumes the former and glosses the
latter): `γ_X(k) = Σ'_j Σ'_l φ_j φ_l γ_Y(k + j − l)`. -/
theorem IsFilteredBy.isStationary [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t)) :
    IsStationary X μ ∧
      ∀ k : ℤ, acvf X μ k = ∑' j : ℤ, ∑' l : ℤ, φ j * φ l * acvf Y μ (k + j - l) := by
  -- the output marginals are square integrable
  have hmem : ∀ t, MemLp (X t) 2 μ := by
    intro t
    obtain ⟨N, hN⟩ := ((h t).eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
    have hdiff : MemLp (fun ω => X t ω - fpsum φ Y t N ω) 2 μ :=
      ⟨(hmeasX t).aestronglyMeasurable.sub (memLp_fpsum hY t N).aestronglyMeasurable,
        lt_of_lt_of_le hN (by norm_num)⟩
    have hsum2 := hdiff.add (memLp_fpsum (φ := φ) hY t N)
    have hfun : ((fun ω => X t ω - fpsum φ Y t N ω) + fpsum φ Y t N) = X t := by
      funext ω; simp
    rwa [hfun] at hsum2
  -- the partial sums converge to the output in the Hilbert space `L²`
  have hconv : ∀ t : ℤ,
      Tendsto (fun N => fpsumLp hY φ t N) atTop (nhds ((hmem t).toLp (X t))) := by
    intro t
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : ∀ N, dist (fpsumLp hY φ t N) ((hmem t).toLp (X t))
        = (eLpNorm (fun ω => X t ω - fpsum φ Y t N ω) 2 μ).toReal := by
      intro N
      rw [Lp.dist_def, eLpNorm_sub_comm]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [coeFn_fpsumLp hY φ t N, (hmem t).coeFn_toLp] with ω h1 h2
      simp only [Pi.sub_apply, h1, h2]
    simp_rw [hd]
    simpa using! (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (h t)
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const 1
  have hI : ∀ {f : Ω → ℝ} (hf : MemLp f 2 μ),
      (inner ℝ (hf.toLp f) (hone.toLp (fun _ => (1 : ℝ))) : ℝ) = ∫ ω, f ω ∂μ := by
    intro f hf
    rw [inner_toLp]
    simp
  have hform : ∀ (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      cov[f, g; μ] = (inner ℝ (hf.toLp f) (hg.toLp g) : ℝ)
        - (inner ℝ (hf.toLp f) (hone.toLp (fun _ => (1 : ℝ))) : ℝ)
          * (inner ℝ (hg.toLp g) (hone.toLp (fun _ => (1 : ℝ))) : ℝ) := by
    intro f g hf hg
    rw [covariance_eq_sub hf hg, inner_toLp, hI hf, hI hg]
    congr 1
  -- covariances pass to the `L²` limits
  have hcovlim : ∀ s t : ℤ, Tendsto (fun N => cov[fpsum φ Y s N, fpsum φ Y t N; μ]) atTop
      (nhds cov[X s, X t; μ]) := by
    intro s t
    have h1 : Tendsto (fun N => (inner ℝ (fpsumLp hY φ s N) (fpsumLp hY φ t N) : ℝ)) atTop
        (nhds (inner ℝ ((hmem s).toLp (X s)) ((hmem t).toLp (X t)) : ℝ)) :=
      (hconv s).inner (hconv t)
    have h2 : ∀ u : ℤ, Tendsto
        (fun N => (inner ℝ (fpsumLp hY φ u N) (hone.toLp (fun _ => (1 : ℝ))) : ℝ)) atTop
        (nhds (inner ℝ ((hmem u).toLp (X u)) (hone.toLp (fun _ => (1 : ℝ))) : ℝ)) :=
      fun u => (hconv u).inner tendsto_const_nhds
    have hlim := h1.sub ((h2 s).mul (h2 t))
    rw [← hform (X s) (X t) (hmem s) (hmem t)] at hlim
    exact hlim.congr fun N =>
      (hform (fpsum φ Y s N) (fpsum φ Y t N) (memLp_fpsum hY s N) (memLp_fpsum hY t N)).symm
  -- ... and the finite windows converge to the double series
  have hcov : ∀ s t : ℤ, cov[X s, X t; μ]
      = ∑' j : ℤ, ∑' l : ℤ, φ j * φ l * acvf Y μ (s - t + j - l) := by
    intro s t
    refine tendsto_nhds_unique (hcovlim s t) ?_
    have hstep : ∀ N : ℕ, cov[fpsum φ Y s N, fpsum φ Y t N; μ]
        = ∑ p ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ),
            φ p.1 * φ p.2 * acvf Y μ (s - t + p.1 - p.2) := by
      intro N
      rw [covariance_fpsum hY φ s t N, ← Finset.sum_product']
    simp only [hstep]
    have hlim := (summable_convProd hY hφ (s - t)).hasSum.comp tendsto_IccProd
    rw [(summable_convProd hY hφ (s - t)).tsum_prod] at hlim
    exact hlim
  -- the means are constant in time
  have hmeanlim : ∀ t : ℤ, Tendsto (fun N => ∫ ω, fpsum φ Y t N ω ∂μ) atTop
      (nhds (∫ ω, X t ω ∂μ)) := by
    intro t
    have hlim : Tendsto
        (fun N => (inner ℝ (fpsumLp hY φ t N) (hone.toLp (fun _ => (1 : ℝ))) : ℝ)) atTop
        (nhds (inner ℝ ((hmem t).toLp (X t)) (hone.toLp (fun _ => (1 : ℝ))) : ℝ)) :=
      (hconv t).inner tendsto_const_nhds
    rw [hI (hmem t)] at hlim
    exact hlim.congr fun N => hI (memLp_fpsum hY t N)
  have hmeanval : ∀ (t : ℤ) (N : ℕ), ∫ ω, fpsum φ Y t N ω ∂μ
      = (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), φ k) * ∫ ω, Y 0 ω ∂μ := by
    intro t N
    simp only [fpsum]
    rw [integral_finset_sum _ (fun k _ =>
      ((hY.memLp (t - k)).const_mul (φ k)).integrable (by norm_num)), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    calc ∫ ω, φ k * Y (t - k) ω ∂μ = φ k * ∫ ω, Y (t - k) ω ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ = φ k * ∫ ω, Y 0 ω ∂μ := by rw [hY.integral_eq (t - k) 0]
  refine ⟨⟨hmem, fun s t => ?_, fun t k => ?_⟩, fun k => ?_⟩
  · refine tendsto_nhds_unique (hmeanlim s) ((hmeanlim t).congr fun N => ?_)
    rw [hmeanval t N, hmeanval s N]
  · rw [hcov (t + k) t, hcov k 0, show t + k - t = k by ring, sub_zero]
  · change cov[X k, X 0; μ] = _
    rw [hcov k 0, sub_zero]

/-- The shear `(k, j, l) ↦ (k − j + l, j, l)` of `ℤ³`, which turns the convolution
weight `|γ(k + j − l)|` into the free weight `|γ(k)|`. -/
private def shearEquiv : ℤ × ℤ × ℤ ≃ ℤ × ℤ × ℤ where
  toFun q := (q.1 - q.2.1 + q.2.2, q.2.1, q.2.2)
  invFun q := (q.1 + q.2.1 - q.2.2, q.2.1, q.2.2)
  left_inv q := by
    show (q.1 - q.2.1 + q.2.2 + q.2.1 - q.2.2, q.2.1, q.2.2) = q
    rw [show q.1 - q.2.1 + q.2.2 + q.2.1 - q.2.2 = q.1 by ring]
  right_inv q := by
    show (q.1 + q.2.1 - q.2.2 - q.2.1 + q.2.2, q.2.1, q.2.2) = q
    rw [show q.1 + q.2.1 - q.2.2 - q.2.1 + q.2.2 = q.1 by ring]

/-- The `ℓ¹ ∗ ℓ¹ ∗ ℓ¹` majorant of the output ACVF, summable on `ℤ × (ℤ × ℤ)`. -/
private lemma summable_convMajorant {Y : ℤ → Ω → ℝ} {φ : ℤ → ℝ}
    (hφ : Summable fun k => |φ k|) (hYsum : HasSummableACVF Y μ) :
    Summable fun q : ℤ × ℤ × ℤ =>
      |φ q.2.1| * |φ q.2.2| * |acvf Y μ (q.1 + q.2.1 - q.2.2)| := by
  have hφ2 : Summable fun p : ℤ × ℤ => |φ p.1| * |φ p.2| :=
    hφ.mul_of_nonneg hφ (fun i => abs_nonneg (φ i)) (fun i => abs_nonneg (φ i))
  have hbase : Summable fun q : ℤ × ℤ × ℤ => |φ q.2.1| * |φ q.2.2| * |acvf Y μ q.1| := by
    have h1 : Summable fun q : ℤ × ℤ × ℤ => |acvf Y μ q.1| * (|φ q.2.1| * |φ q.2.2|) :=
      hYsum.mul_of_nonneg hφ2 (fun i => abs_nonneg _) (fun p => by positivity)
    exact h1.congr fun q => mul_comm _ _
  refine (Equiv.summable_iff shearEquiv).mp (hbase.congr fun q => ?_)
  show |φ q.2.1| * |φ q.2.2| * |acvf Y μ q.1|
      = |φ q.2.1| * |φ q.2.2| * |acvf Y μ (q.1 - q.2.1 + q.2.2 + q.2.1 - q.2.2)|
  rw [show q.1 - q.2.1 + q.2.2 + q.2.1 - q.2.2 = q.1 by ring]

/-- Summability of the output ACVF (derived; FY assumes it): `ℓ¹ ∗ ℓ¹ ∗ ℓ¹`. -/
theorem IsFilteredBy.hasSummableACVF [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hYsum : HasSummableACVF Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t)) :
    HasSummableACVF X μ := by
  have hgnn : (0 : ℤ × ℤ × ℤ → ℝ)
      ≤ fun q => |φ q.2.1| * |φ q.2.2| * |acvf Y μ (q.1 + q.2.1 - q.2.2)| :=
    fun q => by positivity
  obtain ⟨hslice, hout⟩ :=
    (summable_prod_of_nonneg hgnn).mp (summable_convMajorant hφ hYsum)
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hout
  have hform := (h.isStationary hφ hY hmeasY hmeasX).2 k
  rw [← (summable_convProd hY hφ k).tsum_prod] at hform
  rw [hform]
  have hnormsum : Summable fun p : ℤ × ℤ =>
      ‖φ p.1 * φ p.2 * acvf Y μ (k + p.1 - p.2)‖ := by
    refine (hslice k).congr fun p => ?_
    simp only [Real.norm_eq_abs, abs_mul]
  calc |∑' p : ℤ × ℤ, φ p.1 * φ p.2 * acvf Y μ (k + p.1 - p.2)|
      ≤ ∑' p : ℤ × ℤ, ‖φ p.1 * φ p.2 * acvf Y μ (k + p.1 - p.2)‖ := by
        rw [← Real.norm_eq_abs]
        exact norm_tsum_le_tsum_norm hnormsum
    _ = ∑' p : ℤ × ℤ, |φ p.1| * |φ p.2| * |acvf Y μ (k + p.1 - p.2)| :=
        tsum_congr fun p => by simp only [Real.norm_eq_abs, abs_mul]

section Aux3

private lemma norm_fourier_one (k : ℤ) (l : AddCircle (2 * π)) :
    ‖fourier (T := 2 * π) k l‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- Character series with `ℓ¹` real weights are absolutely convergent. -/
private lemma summable_fourier_mul {γ : ℤ → ℝ} (hsum : Summable fun k => |γ k|)
    (l : AddCircle (2 * π)) (n : ℤ → ℤ) :
    Summable fun j : ℤ => (γ j : ℂ) * fourier (T := 2 * π) (n j) l := by
  have hn : ∀ j : ℤ, ‖(γ j : ℂ) * fourier (T := 2 * π) (n j) l‖ = |γ j| := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_fourier_one, mul_one]
  exact Summable.of_norm (by simpa only [hn] using hsum)

private lemma tsum_mul_im_zero {γ : ℤ → ℝ} (heven : ∀ k, γ (-k) = γ k)
    (l : AddCircle (2 * π)) :
    ∑' j : ℤ, γ j * (fourier (T := 2 * π) j l).im = 0 := by
  have hodd : ∀ j : ℤ, γ (-j) * (fourier (T := 2 * π) (-j) l).im
      = -(γ j * (fourier (T := 2 * π) j l).im) := by
    intro j
    rw [heven, fourier_neg, Complex.conj_im]
    ring
  have h1 : ∑' j : ℤ, γ (-j) * (fourier (T := 2 * π) (-j) l).im
      = ∑' j : ℤ, γ j * (fourier (T := 2 * π) j l).im :=
    (Equiv.neg ℤ).tsum_eq fun j => γ j * (fourier (T := 2 * π) j l).im
  rw [tsum_congr hodd, tsum_neg] at h1
  linarith

private lemma tsum_fourier_ofReal' {γ : ℤ → ℝ} (heven : ∀ k, γ (-k) = γ k)
    (hsum : Summable fun k => |γ k|) (l : AddCircle (2 * π)) :
    ∑' j : ℤ, (γ j : ℂ) * fourier (T := 2 * π) j l
      = (((∑' j : ℤ, γ j * (fourier (T := 2 * π) j l).re : ℝ)) : ℂ) := by
  have hFsum := summable_fourier_mul hsum l (fun j => j)
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, Complex.re_tsum hFsum]
    exact tsum_congr fun j => Complex.re_ofReal_mul _ _
  · rw [Complex.ofReal_im, Complex.im_tsum hFsum,
      tsum_congr fun j => Complex.im_ofReal_mul (γ j) (fourier (T := 2 * π) j l)]
    exact tsum_mul_im_zero heven l

/-- The spectral density in complex (character-series) form. -/
private lemma ofReal_spectralDensityOf [IsProbabilityMeasure μ] {Z : ℤ → Ω → ℝ}
    (hstat : IsStationary Z μ) (hsum : HasSummableACVF Z μ) (l : AddCircle (2 * π)) :
    ((spectralDensityOf Z μ l : ℝ) : ℂ)
      = (((2 * π)⁻¹ : ℝ) : ℂ) * ∑' k : ℤ, (acvf Z μ k : ℂ) * fourier k l := by
  rw [spectralDensityOf, Complex.ofReal_mul, tsum_fourier_ofReal' hstat.acvf_even hsum l]

/-- The reindexing `(k, j, l) ↦ ((j, l), k + j − l)` matching the output ACVF series
against the triple product `Γ · conj Γ · g_Y`. -/
private def convEquiv : ℤ × ℤ × ℤ ≃ (ℤ × ℤ) × ℤ where
  toFun r := ((r.2.1, r.2.2), r.1 + r.2.1 - r.2.2)
  invFun q := (q.2 - q.1.1 + q.1.2, q.1.1, q.1.2)
  left_inv r := by
    show (r.1 + r.2.1 - r.2.2 - r.2.1 + r.2.2, r.2.1, r.2.2) = r
    rw [show r.1 + r.2.1 - r.2.2 - r.2.1 + r.2.2 = r.1 by ring]
  right_inv q := by
    show ((q.1.1, q.1.2), q.2 - q.1.1 + q.1.2 + q.1.1 - q.1.2) = q
    rw [show q.2 - q.1.1 + q.1.2 + q.1.1 - q.1.2 = q.2 by ring]

end Aux3

/-- **FY Theorem 2.12 (spectral form)**: `g_X(λ) = |Γ(λ)|² · g_Y(λ)`. -/
theorem IsFilteredBy.spectralDensityOf_eq [IsProbabilityMeasure μ] {X Y : ℤ → Ω → ℝ}
    {φ : ℤ → ℝ} (h : IsFilteredBy X Y φ μ)
    (hφ : Summable fun k => |φ k|) (hY : IsStationary Y μ)
    (hYsum : HasSummableACVF Y μ)
    (hmeasY : ∀ t, Measurable (Y t)) (hmeasX : ∀ t, Measurable (X t))
    (l : AddCircle (2 * π)) :
    spectralDensityOf X μ l = ‖transferFun φ l‖ ^ 2 * spectralDensityOf Y μ l := by
  obtain ⟨hXstat, hXacvf⟩ := h.isStationary hφ hY hmeasY hmeasX
  have hXsum : HasSummableACVF X μ := h.hasSummableACVF hφ hY hYsum hmeasY hmeasX
  have hφ2 : Summable fun p : ℤ × ℤ => |φ p.1| * |φ p.2| :=
    hφ.mul_of_nonneg hφ (fun i => abs_nonneg (φ i)) (fun i => abs_nonneg (φ i))
  have hf1 : Summable fun j : ℤ => (φ j : ℂ) * fourier (T := 2 * π) (-j) l :=
    summable_fourier_mul hφ l (fun j => -j)
  have hf2 : Summable fun j : ℤ => (φ j : ℂ) * fourier (T := 2 * π) j l :=
    summable_fourier_mul hφ l (fun j => j)
  have hgY : Summable fun m : ℤ => (acvf Y μ m : ℂ) * fourier (T := 2 * π) m l :=
    summable_fourier_mul hYsum l (fun m => m)
  -- the conjugate transfer function is the positively-indexed character series
  have hconjΓ : (starRingEnd ℂ) (transferFun φ l)
      = ∑' j : ℤ, (φ j : ℂ) * fourier (T := 2 * π) j l := by
    have hmap : HasSum
        (fun j : ℤ => (starRingEnd ℂ) ((φ j : ℂ) * fourier (T := 2 * π) (-j) l))
        ((starRingEnd ℂ) (transferFun φ l)) :=
      hf1.hasSum.map ((starRingEnd ℂ).toAddMonoidHom) Complex.continuous_conj
    rw [← hmap.tsum_eq]
    exact tsum_congr fun j => by
      rw [map_mul, Complex.conj_ofReal, fourier_neg, Complex.conj_conj]
  -- `Γ · conj Γ` is the double character series
  have hprod2 : Summable fun p : ℤ × ℤ =>
      ((φ p.1 : ℂ) * fourier (T := 2 * π) (-p.1) l) *
        ((φ p.2 : ℂ) * fourier (T := 2 * π) p.2 l) := by
    have hn : ∀ p : ℤ × ℤ, ‖((φ p.1 : ℂ) * fourier (T := 2 * π) (-p.1) l) *
        ((φ p.2 : ℂ) * fourier (T := 2 * π) p.2 l)‖ = |φ p.1| * |φ p.2| := by
      intro p
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, norm_fourier_one, norm_fourier_one,
        mul_one, mul_one]
    exact Summable.of_norm (by simpa only [hn] using hφ2)
  have hprod3 : Summable fun q : (ℤ × ℤ) × ℤ =>
      (((φ q.1.1 : ℂ) * fourier (T := 2 * π) (-q.1.1) l) *
          ((φ q.1.2 : ℂ) * fourier (T := 2 * π) q.1.2 l)) *
        ((acvf Y μ q.2 : ℂ) * fourier (T := 2 * π) q.2 l) := by
    have hn : ∀ q : (ℤ × ℤ) × ℤ,
        ‖(((φ q.1.1 : ℂ) * fourier (T := 2 * π) (-q.1.1) l) *
            ((φ q.1.2 : ℂ) * fourier (T := 2 * π) q.1.2 l)) *
          ((acvf Y μ q.2 : ℂ) * fourier (T := 2 * π) q.2 l)‖
        = (|φ q.1.1| * |φ q.1.2|) * |acvf Y μ q.2| := by
      intro q
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        Real.norm_eq_abs, norm_fourier_one, norm_fourier_one, norm_fourier_one,
        mul_one, mul_one, mul_one]
    refine Summable.of_norm (by
      simpa only [hn] using
        hφ2.mul_of_nonneg hYsum (fun p => by positivity) (fun m => abs_nonneg _))
  have hCB : (transferFun φ l * (starRingEnd ℂ) (transferFun φ l))
        * (∑' m : ℤ, (acvf Y μ m : ℂ) * fourier (T := 2 * π) m l)
      = ∑' q : (ℤ × ℤ) × ℤ,
          (((φ q.1.1 : ℂ) * fourier (T := 2 * π) (-q.1.1) l) *
              ((φ q.1.2 : ℂ) * fourier (T := 2 * π) q.1.2 l)) *
            ((acvf Y μ q.2 : ℂ) * fourier (T := 2 * π) q.2 l) := by
    rw [hconjΓ, transferFun, hf1.tsum_mul_tsum hf2 hprod2]
    exact hprod2.tsum_mul_tsum hgY hprod3
  -- the reindexed summand identity
  have hFG : ∀ r : ℤ × ℤ × ℤ,
      (((φ r.2.1 * φ r.2.2 * acvf Y μ (r.1 + r.2.1 - r.2.2) : ℝ)) : ℂ)
          * fourier (T := 2 * π) r.1 l
        = (((φ r.2.1 : ℂ) * fourier (T := 2 * π) (-r.2.1) l) *
              ((φ r.2.2 : ℂ) * fourier (T := 2 * π) r.2.2 l)) *
            ((acvf Y μ (r.1 + r.2.1 - r.2.2) : ℂ) *
              fourier (T := 2 * π) (r.1 + r.2.1 - r.2.2) l) := by
    intro r
    have he : fourier (T := 2 * π) (-r.2.1) l * fourier (T := 2 * π) r.2.2 l
        * fourier (T := 2 * π) (r.1 + r.2.1 - r.2.2) l = fourier (T := 2 * π) r.1 l := by
      rw [← fourier_add, ← fourier_add,
        show -r.2.1 + r.2.2 + (r.1 + r.2.1 - r.2.2) = r.1 by ring]
    push_cast
    rw [← he]
    ring
  have hFsum : Summable fun r : ℤ × ℤ × ℤ =>
      (((φ r.2.1 * φ r.2.2 * acvf Y μ (r.1 + r.2.1 - r.2.2) : ℝ)) : ℂ)
        * fourier (T := 2 * π) r.1 l :=
    ((Equiv.summable_iff convEquiv).mpr hprod3).congr fun r => (hFG r).symm
  -- the output density series is the same triple sum
  have hslice : ∀ k : ℤ, (∑' p : ℤ × ℤ,
        (((φ p.1 * φ p.2 * acvf Y μ (k + p.1 - p.2) : ℝ)) : ℂ) * fourier (T := 2 * π) k l)
      = (acvf X μ k : ℂ) * fourier (T := 2 * π) k l := by
    intro k
    rw [tsum_mul_right, ← Complex.ofReal_tsum, hXacvf k,
      ← (summable_convProd hY hφ k).tsum_prod]
  have hA : (∑' k : ℤ, (acvf X μ k : ℂ) * fourier (T := 2 * π) k l)
      = ∑' q : (ℤ × ℤ) × ℤ,
          (((φ q.1.1 : ℂ) * fourier (T := 2 * π) (-q.1.1) l) *
              ((φ q.1.2 : ℂ) * fourier (T := 2 * π) q.1.2 l)) *
            ((acvf Y μ q.2 : ℂ) * fourier (T := 2 * π) q.2 l) := by
    rw [← tsum_congr hslice, ← hFsum.tsum_prod, tsum_congr hFG]
    exact convEquiv.tsum_eq (fun q : (ℤ × ℤ) × ℤ =>
      (((φ q.1.1 : ℂ) * fourier (T := 2 * π) (-q.1.1) l) *
          ((φ q.1.2 : ℂ) * fourier (T := 2 * π) q.1.2 l)) *
        ((acvf Y μ q.2 : ℂ) * fourier (T := 2 * π) q.2 l))
  -- assemble over ℂ
  refine Complex.ofReal_inj.mp ?_
  rw [ofReal_spectralDensityOf hXstat hXsum l, hA, ← hCB, Complex.ofReal_mul,
    ofReal_spectralDensityOf hY hYsum l, Complex.ofReal_pow, ← Complex.mul_conj']
  ring

end StatLean.TimeSeries
