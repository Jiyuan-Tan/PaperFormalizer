module
public import StatLean.TimeSeries.Models.WhiteNoise
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Linear (MA(∞)) processes (FY §2.1.2, eq. (2.1))

The one-sided linear process `X_t = Σ_{j≥0} ψ_j ε_{t−j}` with absolutely summable
coefficients over white noise: well-definedness (`L²` convergence of the partial sums),
existence, stationarity with the autocovariance formula
`γ(k) = σ² Σ_{j≥0} ψ_j ψ_{j+|k|}` (FY eq. (2.2)), strict stationarity under i.i.d.
innovations, and almost-sure convergence of the defining series under i.i.d.
innovations (FY cites Chow & Teicher 1997, Cor. 3 p. 117).

`IsLinearProcessOf ψ X ε μ` says the partial sums converge to `X t` in `L²`
(`eLpNorm … 2 μ → 0`) at every time — the convergence mode FY works with. (The
*two-sided* linear process of FY Theorem 2.8/2.14 will generalize this in batch B/C.)

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.2,
eqs. (2.1)–(2.2) (pp. 30–31). (`FY §2.1.2 eq. (2.1)–(2.2)`.)

**Proof formalization notes.** Existence: the partial sums are Cauchy in `L²` by
`ℓ¹ ⊆ ℓ²` of the coefficients and WN orthogonality; completeness of `L²` provides a
limit, chosen measurably per `t`. The ACVF formula interchanges `cov` with the `L²`
limits (continuity of the inner product) and collapses the double series by
uncorrelatedness. Strict stationarity under i.i.d. innovations transports the
finite-dimensional laws of the partial sums (each a fixed measurable function of a
shift of the i.i.d. family) to the a.e./in-measure limit. The a.e. convergence uses
absolute (Tonelli) summability, which the `ℓ¹` coefficient hypothesis supplies.

**Bibliographic comments.** Infinite moving averages originate with E. Slutsky (1927)
and H. Wold (1938); the `L²` theory is the Wiener–Kolmogorov era's; the almost-sure
convergence of independent series is Kolmogorov's three-series/maximal-inequality circle
(FY cite Y. S. Chow and H. Teicher, *Probability Theory*, 3rd ed., Springer, 1997).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `X` is the **linear process** with coefficients `ψ` over the noise `ε` (FY eq.
(2.1)): at every time the `L²` distance from the partial sums vanishes,
`‖X_t − Σ_{j<N} ψ_j ε_{t−j}‖_{L²(μ)} → 0`. -/
def IsLinearProcessOf (ψ : ℕ → ℝ) (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N => eLpNorm
      (fun ω => X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) 2 μ)
    atTop (𝓝 0)

section Aux

variable {ψ : ℕ → ℝ} {σ2 : ℝ} {ε : ℤ → Ω → ℝ}

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

/-- The `N`-term partial sum `Σ_{j<N} ψ_j ε_{t−j}` of the linear process. -/
private noncomputable def psum (ψ : ℕ → ℝ) (ε : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω

private lemma memLp_psum (hε : IsWhiteNoise ε σ2 μ) (t : ℤ) (N : ℕ) :
    MemLp (psum ψ ε t N) 2 μ :=
  memLp_finset_sum _ fun j _ => (hε.memLp (t - (j : ℕ))).const_mul (ψ j)

/-- Second moments of white noise: `E[ε_a ε_b] = σ² δ_{ab}` (the means vanish, so the
mixed moment is the covariance). -/
private lemma integral_noise_mul [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (a b : ℤ) : ∫ ω, ε a ω * ε b ω ∂μ = if a = b then σ2 else 0 := by
  have h := covariance_eq_sub (hε.memLp a) (hε.memLp b)
  rw [hε.integral_eq_zero a, zero_mul, sub_zero] at h
  have h2 : μ[ε a * ε b] = ∫ ω, ε a ω * ε b ω ∂μ := by
    simp [Pi.mul_apply]
  rw [h2] at h
  rw [← h]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, covariance_self (hε.memLp a).aestronglyMeasurable.aemeasurable,
      hε.variance_eq a]
  · rw [if_neg hab, hε.uncorrelated a b hab]

/-- The `L²` norm of the noise is `√σ²` at every time. -/
private lemma norm_toLp_noise [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ) (a : ℤ) :
    ‖(hε.memLp a).toLp (ε a)‖ = Real.sqrt σ2 := by
  have h : ‖(hε.memLp a).toLp (ε a)‖ ^ 2 = σ2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp, integral_noise_mul hε a a, if_pos rfl]
  have h2 := Real.sqrt_sq (norm_nonneg ((hε.memLp a).toLp (ε a)))
  rw [h] at h2
  exact h2.symm

/-- The `L²` class of the `N`-term partial sum. -/
private noncomputable def psumLp [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (t : ℤ) (N : ℕ) : Lp ℝ 2 μ :=
  (memLp_psum (ψ := ψ) hε t N).toLp _

private lemma coeFn_psumLp [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (t : ℤ) (N : ℕ) : ⇑(psumLp hε ψ t N) =ᵐ[μ] psum ψ ε t N :=
  (memLp_psum (ψ := ψ) hε t N).coeFn_toLp

/-- Successive partial sums differ by the single term `ψ_N ε_{t−N}`, of `L²` norm
`|ψ_N| √σ²`. -/
private lemma dist_psumLp_succ [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    dist (psumLp hε ψ t N) (psumLp hε ψ t (N + 1)) = |ψ N| * Real.sqrt σ2 := by
  rw [dist_comm, Lp.dist_def]
  have hae : (⇑(psumLp hε ψ t (N + 1)) - ⇑(psumLp hε ψ t N))
      =ᵐ[μ] (ψ N • ε (t - (N : ℕ))) := by
    filter_upwards [coeFn_psumLp hε ψ t (N + 1), coeFn_psumLp hε ψ t N] with ω h1 h2
    simp only [Pi.sub_apply, h1, h2, psum, Finset.sum_range_succ, Pi.smul_apply, smul_eq_mul]
    ring
  rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, ENNReal.toReal_mul]
  have h : ((eLpNorm (ε (t - (N : ℕ))) 2 μ)).toReal = Real.sqrt σ2 := by
    rw [← Lp.norm_toLp _ (hε.memLp (t - (N : ℕ))), norm_toLp_noise hε]
  rw [h]
  simp

/-- The mixed second moment of two partial sums at lag `s − t = m ≥ 0`: by
uncorrelatedness only the matched noise indices `s − i = t − j` survive, and they
contribute `σ² ψ_{m+l} ψ_l`. -/
private lemma integral_psum_mul [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) {s t : ℤ} {m : ℕ} (hd : s - t = (m : ℤ)) (N : ℕ) :
    ∫ ω, psum ψ ε s N ω * psum ψ ε t N ω ∂μ
      = σ2 * ∑ l ∈ Finset.range (N - m), ψ (m + l) * ψ l := by
  have hint : ∀ (a b : ℤ) (c d : ℝ),
      Integrable (fun ω => (c * ε a ω) * (d * ε b ω)) μ :=
    fun a b c d => ((hε.memLp a).const_mul c).integrable_mul ((hε.memLp b).const_mul d)
  have hterm : ∀ i j : ℕ, ∫ ω, (ψ i * ε (s - (i : ℕ)) ω) * (ψ j * ε (t - (j : ℕ)) ω) ∂μ
      = ψ i * ψ j * (if s - (i : ℤ) = t - (j : ℤ) then σ2 else 0) := by
    intro i j
    have hre : ∀ ω, (ψ i * ε (s - (i : ℕ)) ω) * (ψ j * ε (t - (j : ℕ)) ω)
        = (ψ i * ψ j) * (ε (s - (i : ℕ)) ω * ε (t - (j : ℕ)) ω) := fun ω => by ring
    simp_rw [hre]
    rw [integral_const_mul, integral_noise_mul hε]
  have hexp : ∀ ω, psum ψ ε s N ω * psum ψ ε t N ω
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (ψ i * ε (s - (i : ℕ)) ω) * (ψ j * ε (t - (j : ℕ)) ω) := by
    intro ω
    simp only [psum]
    rw [Finset.sum_mul_sum]
  simp_rw [hexp]
  rw [integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint _ _ _ _]
  have hstep : ∀ i ∈ Finset.range N,
      ∫ ω, ∑ j ∈ Finset.range N, (ψ i * ε (s - (i : ℕ)) ω) * (ψ j * ε (t - (j : ℕ)) ω) ∂μ
        = if m ≤ i then ψ i * ψ (i - m) * σ2 else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [integral_finset_sum _ fun j _ => hint _ _ _ _]
    simp_rw [hterm]
    by_cases him : m ≤ i
    · rw [if_pos him]
      rw [Finset.sum_eq_single (i - m) (fun j _ hjne => ?_) (fun hnot => ?_)]
      · rw [if_pos (by omega)]
      · rw [if_neg (fun h => hjne (by omega)), mul_zero]
      · exact absurd (Finset.mem_range.2 (by omega)) hnot
    · rw [if_neg him]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg (fun h => him (by omega)), mul_zero]
  rw [Finset.sum_congr rfl hstep]
  have hsub : ∑ i ∈ Finset.Ico m N, (if m ≤ i then ψ i * ψ (i - m) * σ2 else 0)
      = ∑ i ∈ Finset.range N, (if m ≤ i then ψ i * ψ (i - m) * σ2 else 0) :=
    Finset.sum_subset (fun x hx => Finset.mem_range.2 (Finset.mem_Ico.1 hx).2)
      (fun x hx hxn => by
        rw [Finset.mem_range] at hx
        rw [Finset.mem_Ico] at hxn
        rw [if_neg (by omega)])
  rw [← hsub, Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_Ico.1 hi).1),
    Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [Nat.add_sub_cancel_left]; ring

private lemma inner_psumLp [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (s t : ℤ) (N M : ℕ) :
    inner ℝ (psumLp hε ψ s N) (psumLp hε ψ t M)
      = ∫ ω, psum ψ ε s N ω * psum ψ ε t M ω ∂μ :=
  inner_toLp _ _

/-- Partial sums have mean zero. -/
private lemma integral_psum [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    (ψ : ℕ → ℝ) (t : ℤ) (N : ℕ) : ∫ ω, psum ψ ε t N ω ∂μ = 0 := by
  simp only [psum]
  rw [integral_finset_sum _ fun j _ => ((hε.memLp (t - (j : ℕ))).const_mul (ψ j)).integrable
    (by norm_num)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, hε.integral_eq_zero, mul_zero]

/-- `|ψ|` is bounded by its own sum. -/
private lemma abs_psi_le (hψ : Summable fun j => |ψ j|) (j : ℕ) :
    |ψ j| ≤ ∑' i : ℕ, |ψ i| :=
  hψ.le_tsum j fun _ _ => abs_nonneg _

/-- The lag-`m` coefficient series is summable. -/
private lemma summable_shift (hψ : Summable fun j => |ψ j|) (m : ℕ) :
    Summable fun l : ℕ => ψ (m + l) * ψ l := by
  refine Summable.of_abs ?_
  refine Summable.of_nonneg_of_le (fun l => abs_nonneg _)
    (fun l => ?_) (hψ.mul_left (∑' i : ℕ, |ψ i|))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_psi_le hψ (m + l)) (abs_nonneg _)

/-- **Shift invariance of finite i.i.d. blocks**: for any finite family of times `u` and
any shift `k`, the joint law of `(ε_{u a + k})_a` is that of `(ε_{u a})_a`. Repetitions in
`u` are allowed: the block factors through the (injective) enumeration of the range, on
which the product-law characterization of independence applies. -/
private lemma map_noise_block [IsProbabilityMeasure μ] {A : Type*} [Finite A]
    (hε : IsIIDNoise ε σ2 μ) (u : A → ℤ) (k : ℤ) :
    μ.map (fun ω a => ε (u a + k) ω) = μ.map (fun ω a => ε (u a) ω) := by
  classical
  have : Fintype A := Fintype.ofFinite A
  set S : Finset ℤ := Finset.image u Finset.univ with hS
  set ρ : A → {x // x ∈ S} :=
    fun a => ⟨u a, Finset.mem_image_of_mem u (Finset.mem_univ a)⟩ with hρ
  -- the block indexed by the (distinct) times in the range of `u`
  have hlaw : ∀ c : ℤ, μ.map (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω)
      = Measure.pi (fun _ : {x // x ∈ S} => μ.map (ε 0)) := by
    intro c
    have hinj : Function.Injective (fun b : {x // x ∈ S} => (b : ℤ) + c) := by
      intro b1 b2 h
      exact Subtype.ext (by simpa using h)
    have hindep : iIndepFun (fun b : {x // x ∈ S} => ε ((b : ℤ) + c)) μ :=
      hε.iIndep.precomp hinj
    rw [(iIndepFun_iff_map_fun_eq_pi_map fun b => (hε.measurable _).aemeasurable).1 hindep]
    exact congrArg Measure.pi (funext fun b => (hε.identDistrib _ 0).map_eq)
  -- the general block is the range block precomposed with `ρ`
  have hmb : ∀ c : ℤ, Measurable (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => measurable_pi_lambda _ fun b => hε.measurable _
  have hcomp : Measurable (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) :=
    measurable_pi_lambda _ fun a => measurable_pi_apply (ρ a)
  have hfac : ∀ c : ℤ, (fun ω a => ε (u a + c) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) ∘ (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + c) ω) :=
    fun c => rfl
  have hzero : (fun ω a => ε (u a) ω)
      = (fun v : {x // x ∈ S} → ℝ => v ∘ ρ) ∘ (fun ω (b : {x // x ∈ S}) => ε ((b : ℤ) + 0) ω) := by
    funext ω a
    simp only [Function.comp_apply, add_zero, hρ]
  rw [hfac k, hzero, ← Measure.map_map hcomp (hmb k), ← Measure.map_map hcomp (hmb 0),
    hlaw k, hlaw 0]

/-- Windows of partial sums are shift-invariant in law: each is one fixed measurable
function of the corresponding i.i.d. noise block. -/
private lemma map_psum_vec [IsProbabilityMeasure μ] (hε : IsIIDNoise ε σ2 μ)
    (ψ : ℕ → ℝ) {n : ℕ} (t : Fin n → ℤ) (N : ℕ) (k : ℤ) :
    μ.map (fun ω (i : Fin n) => psum ψ ε (t i + k) N ω)
      = μ.map (fun ω (i : Fin n) => psum ψ ε (t i) N ω) := by
  classical
  set u : Fin n × Fin N → ℤ := fun p => t p.1 - (p.2 : ℕ) with hu
  set G : (Fin n × Fin N → ℝ) → (Fin n → ℝ) :=
    fun v i => ∑ j : Fin N, ψ j * v (i, j) with hG
  have hGm : Measurable G :=
    measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ => by fun_prop
  have hbm : ∀ c : ℤ, Measurable (fun ω (a : Fin n × Fin N) => ε (u a + c) ω) :=
    fun c => measurable_pi_lambda _ fun a => hε.measurable _
  have hbm0 : Measurable (fun ω (a : Fin n × Fin N) => ε (u a) ω) :=
    measurable_pi_lambda _ fun a => hε.measurable _
  have hfac : (fun ω (i : Fin n) => psum ψ ε (t i + k) N ω)
      = G ∘ (fun ω (a : Fin n × Fin N) => ε (u a + k) ω) := by
    funext ω i
    simp only [Function.comp_apply, hG, psum, hu]
    rw [← Fin.sum_univ_eq_sum_range (fun j => ψ j * ε (t i + k - (j : ℕ)) ω) N]
    exact Finset.sum_congr rfl fun j _ => by congr 2; ring
  have h0 : (fun ω (i : Fin n) => psum ψ ε (t i) N ω)
      = G ∘ (fun ω (a : Fin n × Fin N) => ε (u a) ω) := by
    funext ω i
    simp only [Function.comp_apply, hG, psum, hu]
    rw [← Fin.sum_univ_eq_sum_range (fun j => ψ j * ε (t i - (j : ℕ)) ω) N]
  rw [hfac, h0, ← Measure.map_map hGm (hbm k), ← Measure.map_map hGm hbm0,
    map_noise_block hε u k]

private lemma measurable_psum (hmε : ∀ s, Measurable (ε s)) (ψ : ℕ → ℝ) (s : ℤ) (N : ℕ) :
    Measurable (psum ψ ε s N) :=
  Finset.measurable_sum _ fun _ _ => (hmε _).const_mul _

/-- The total defect of a `k`-shifted and an unshifted window of partial sums at stage
`N`: one scalar sequence dominating every coordinate of both. -/
private noncomputable def windowDefect (ψ : ℕ → ℝ) (X ε : ℤ → Ω → ℝ) {n : ℕ}
    (t : Fin n → ℤ) (k : ℤ) (N : ℕ) : Ω → ℝ := fun ω =>
  (∑ i : Fin n, ‖X (t i + k) ω - psum ψ ε (t i + k) N ω‖)
    + ∑ i : Fin n, ‖X (t i + 0) ω - psum ψ ε (t i + 0) N ω‖

private lemma measurable_windowDefect {X : ℤ → Ω → ℝ} {n : ℕ} (hmε : ∀ s, Measurable (ε s))
    (hmX : ∀ s, Measurable (X s)) (ψ : ℕ → ℝ) (t : Fin n → ℤ) (k : ℤ) (N : ℕ) :
    Measurable (windowDefect ψ X ε t k N) :=
  (Finset.measurable_sum _ fun _ _ => ((hmX _).sub (measurable_psum hmε ψ _ _)).norm).add
    (Finset.measurable_sum _ fun _ _ => ((hmX _).sub (measurable_psum hmε ψ _ _)).norm)

/-- The total defect vanishes in `L²`. -/
private lemma tendsto_windowDefect [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ} {n : ℕ}
    (hX : IsLinearProcessOf ψ X ε μ) (hmε : ∀ s, Measurable (ε s))
    (hmX : ∀ s, Measurable (X s)) (t : Fin n → ℤ) (k : ℤ) :
    Tendsto (fun N => eLpNorm (windowDefect ψ X ε t k N) 2 μ) atTop (𝓝 0) := by
  have hsplit : ∀ (c : ℤ) (N : ℕ),
      eLpNorm (fun ω => ∑ i : Fin n, ‖X (t i + c) ω - psum ψ ε (t i + c) N ω‖) 2 μ
        ≤ ∑ i : Fin n, eLpNorm (fun ω => X (t i + c) ω - psum ψ ε (t i + c) N ω) 2 μ := by
    intro c N
    have hfun : (fun ω => ∑ i : Fin n, ‖X (t i + c) ω - psum ψ ε (t i + c) N ω‖)
        = ∑ i : Fin n, fun ω => ‖X (t i + c) ω - psum ψ ε (t i + c) N ω‖ := by
      funext ω; simp
    rw [hfun]
    refine (eLpNorm_sum_le (fun i _ => ?_) one_le_two).trans_eq ?_
    · exact (((hmX _).sub (measurable_psum hmε ψ _ _)).norm).aestronglyMeasurable
    · exact Finset.sum_congr rfl fun i _ => eLpNorm_norm _
  have hbound : ∀ N : ℕ, eLpNorm (windowDefect ψ X ε t k N) 2 μ
      ≤ (∑ i : Fin n, eLpNorm (fun ω => X (t i + k) ω - psum ψ ε (t i + k) N ω) 2 μ)
        + ∑ i : Fin n, eLpNorm (fun ω => X (t i + 0) ω - psum ψ ε (t i + 0) N ω) 2 μ := by
    intro N
    refine le_trans (eLpNorm_add_le ?_ ?_ one_le_two) (add_le_add (hsplit k N) (hsplit 0 N))
    · exact (Finset.measurable_sum _ fun i _ =>
        ((hmX _).sub (measurable_psum hmε ψ _ _)).norm).aestronglyMeasurable
    · exact (Finset.measurable_sum _ fun i _ =>
        ((hmX _).sub (measurable_psum hmε ψ _ _)).norm).aestronglyMeasurable
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun N => zero_le) hbound
  have hsum : ∀ c : ℤ, Tendsto (fun N =>
      ∑ i : Fin n, eLpNorm (fun ω => X (t i + c) ω - psum ψ ε (t i + c) N ω) 2 μ)
      atTop (𝓝 0) := by
    intro c
    simpa using! tendsto_finset_sum (Finset.univ : Finset (Fin n)) fun i _ => hX (t i + c)
  simpa using (hsum k).add (hsum 0)

/-- Along a subsequence, both windows of partial sums converge a.e. to the corresponding
windows of the process. -/
private lemma exists_subseq_window [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ} {n : ℕ}
    (hX : IsLinearProcessOf ψ X ε μ) (hmε : ∀ s, Measurable (ε s))
    (hmX : ∀ s, Measurable (X s)) (t : Fin n → ℤ) (k : ℤ) :
    ∃ ns : ℕ → ℕ, ∀ c : ℤ, (c = k ∨ c = 0) → ∀ᵐ ω ∂μ,
      Tendsto (fun j => (fun i => psum ψ ε (t i + c) (ns j) ω : Fin n → ℝ)) atTop
        (𝓝 fun i => X (t i + c) ω) := by
  obtain ⟨ns, -, hns⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun N => (measurable_windowDefect hmε hmX ψ t k N).aestronglyMeasurable)
      aestronglyMeasurable_zero
      (by simpa using tendsto_windowDefect hX hmε hmX t k)).exists_seq_tendsto_ae
  refine ⟨ns, fun c hc => ?_⟩
  filter_upwards [hns] with ω hω
  rw [tendsto_pi_nhds]
  intro i
  have hmem : ∀ (c' : ℤ) (j : ℕ), ‖X (t i + c') ω - psum ψ ε (t i + c') (ns j) ω‖
      ≤ ∑ i' : Fin n, ‖X (t i' + c') ω - psum ψ ε (t i' + c') (ns j) ω‖ := fun c' j =>
    Finset.single_le_sum (f := fun i' : Fin n =>
      ‖X (t i' + c') ω - psum ψ ε (t i' + c') (ns j) ω‖)
      (fun i' _ => norm_nonneg _) (Finset.mem_univ i)
  have hbound : ∀ j : ℕ, ‖X (t i + c) ω - psum ψ ε (t i + c) (ns j) ω‖
      ≤ windowDefect ψ X ε t k (ns j) ω := by
    intro j
    rcases hc with rfl | rfl
    · exact le_add_of_le_of_nonneg (hmem _ j) (Finset.sum_nonneg fun i' _ => norm_nonneg _)
    · exact le_add_of_nonneg_of_le (Finset.sum_nonneg fun i' _ => norm_nonneg _) (hmem _ j)
  have hzero : Tendsto (fun j => ‖X (t i + c) ω - psum ψ ε (t i + c) (ns j) ω‖) atTop (𝓝 0) :=
    squeeze_zero (fun j => norm_nonneg _) hbound (by simpa using hω)
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [dist_eq_norm, norm_sub_rev] using hzero

/-- The `L²` convergence of the partial sums, in `psum` form. -/
private lemma tendsto_eLpNorm_psum {X : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ) (t : ℤ) :
    Tendsto (fun N => eLpNorm (psum ψ ε t N - X t) 2 μ) atTop (𝓝 0) := by
  refine (hX t).congr fun N => ?_
  have h1 : (fun ω => X t ω - ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω)
      = (X t - psum ψ ε t N) := rfl
  rw [h1, eLpNorm_sub_comm]

/-- A real series with `ℓ¹` `ℝ≥0∞`-norms is summable. -/
private lemma summable_of_tsum_enorm_ne_top {f : ℕ → ℝ} (h : (∑' j : ℕ, ‖f j‖ₑ) ≠ ∞) :
    Summable f :=
  Summable.of_nnnorm (ENNReal.tsum_coe_ne_top_iff_summable.1
    (by simpa only [enorm_eq_nnnorm] using h))

/-- Absolute summability gives finiteness of the `ℝ≥0∞`-norm series. -/
private lemma tsum_enorm_ne_top_of_summable {f : ℕ → ℝ} (h : Summable fun j => |f j|) :
    (∑' j : ℕ, ‖f j‖ₑ) ≠ ∞ := by
  have h1 : Summable fun j => ‖f j‖₊ :=
    NNReal.summable_coe.1 (by simpa only [coe_nnnorm, Real.norm_eq_abs] using h)
  simpa only [enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.2 h1

end Aux

/-- **Existence** (FY §2.1.2): over white noise, absolutely summable coefficients define
a linear process (`L²`-limits of the partial sums, chosen measurably). -/
theorem exists_isLinearProcessOf [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: absolutely summable coefficients; FY eq. (2.1)
    (hψ : Summable fun j => |ψ j|)
    -- USER-INPUT: white-noise innovations; FY eq. (2.1)
    (hε : IsWhiteNoise ε σ2 μ) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧ IsLinearProcessOf ψ X ε μ := by
  have main : ∀ t : ℤ, ∃ f : Ω → ℝ, Measurable f ∧
      Tendsto (fun N => eLpNorm (fun ω => f ω - psum ψ ε t N ω) 2 μ) atTop (𝓝 0) := by
    intro t
    have hsum : Summable fun N : ℕ => dist (psumLp hε ψ t N) (psumLp hε ψ t N.succ) :=
      (hψ.mul_right (Real.sqrt σ2)).congr fun N => (dist_psumLp_succ hε ψ t N).symm
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
    refine ⟨(Lp.aestronglyMeasurable L).mk _,
      (Lp.aestronglyMeasurable L).stronglyMeasurable_mk.measurable, ?_⟩
    have heq : ∀ N : ℕ,
        eLpNorm (fun ω => ((Lp.aestronglyMeasurable L).mk _) ω - psum ψ ε t N ω) 2 μ
          = edist (psumLp hε ψ t N) L := by
      intro N
      rw [edist_comm, Lp.edist_def]
      refine eLpNorm_congr_ae ?_
      filter_upwards [(Lp.aestronglyMeasurable L).ae_eq_mk, coeFn_psumLp hε ψ t N] with ω h1 h2
      simp only [Pi.sub_apply, ← h1, h2]
    simp_rw [heq, edist_dist]
    simpa using ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.mp hL)
  choose X hXm hXlim using main
  exact ⟨X, hXm, hXlim⟩

/-- Marginals of a linear process are in `L²`. -/
theorem IsLinearProcessOf.memLp [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    -- LEAN-ONLY: measurability of the limits; supplied by `exists_isLinearProcessOf`
    (hmeas : ∀ t, Measurable (X t)) (t : ℤ) : MemLp (X t) 2 μ := by
  obtain ⟨N, hN⟩ := ((hX t).eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
  have hdiff : MemLp (fun ω => X t ω - psum ψ ε t N ω) 2 μ :=
    ⟨(hmeas t).aestronglyMeasurable.sub (memLp_psum hε t N).aestronglyMeasurable,
      lt_of_lt_of_le hN (by norm_num)⟩
  have hsum := hdiff.add (memLp_psum (ψ := ψ) hε t N)
  have hfun : ((fun ω => X t ω - psum ψ ε t N ω) + psum ψ ε t N) = X t := by
    funext ω; simp
  rwa [hfun] at hsum

/-- **Stationarity + the ACVF formula** (FY §2.1.2, eq. (2.2)): a linear process over
white noise is weakly stationary with `γ(k) = σ² Σ_{j≥0} ψ_j ψ_{j+|k|}`. -/
theorem IsLinearProcessOf.isStationary [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsWhiteNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) :
    IsStationary X μ ∧
      ∀ k : ℤ, acvf X μ k = σ2 * ∑' j : ℕ, ψ j * ψ (j + k.natAbs) := by
  have hmem : ∀ t, MemLp (X t) 2 μ := hX.memLp hψ hε hmeas
  -- the partial sums converge to `X t` in the Hilbert space `L²`
  have hconv : ∀ t : ℤ,
      Tendsto (fun N => psumLp hε ψ t N) atTop (𝓝 ((hmem t).toLp (X t))) := by
    intro t
    rw [tendsto_iff_dist_tendsto_zero]
    have hd : ∀ N, dist (psumLp hε ψ t N) ((hmem t).toLp (X t))
        = (eLpNorm (fun ω => X t ω - psum ψ ε t N ω) 2 μ).toReal := by
      intro N
      rw [Lp.dist_def, eLpNorm_sub_comm]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [coeFn_psumLp hε ψ t N, (hmem t).coeFn_toLp] with ω h1 h2
      simp only [Pi.sub_apply, h1, h2]
    simp_rw [hd]
    simpa using! (ENNReal.continuousAt_toReal (by simp)).tendsto.comp (hX t)
  -- the mean is zero at every time, being the limit of the (zero) means of the partial sums
  have hone : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const 1
  have hmean : ∀ t : ℤ, ∫ ω, X t ω ∂μ = 0 := by
    intro t
    have hlim : Tendsto (fun N => (inner ℝ (psumLp hε ψ t N) (hone.toLp _) : ℝ)) atTop
        (𝓝 (inner ℝ ((hmem t).toLp (X t)) (hone.toLp (fun _ => (1 : ℝ))))) :=
      (hconv t).inner tendsto_const_nhds
    have hzero : ∀ N, (inner ℝ (psumLp hε ψ t N) (hone.toLp (fun _ => (1 : ℝ))) : ℝ) = 0 := by
      intro N
      rw [show psumLp hε ψ t N = (memLp_psum (ψ := ψ) hε t N).toLp (psum ψ ε t N) from rfl,
        inner_toLp]
      simpa using integral_psum hε ψ t N
    have hval : (inner ℝ ((hmem t).toLp (X t)) (hone.toLp (fun _ => (1 : ℝ))) : ℝ)
        = ∫ ω, X t ω ∂μ := by
      rw [inner_toLp]; simp
    rw [← hval]
    exact tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
  -- with vanishing means the covariance is the `L²` inner product
  have hcovXL : ∀ s t : ℤ, cov[X s, X t; μ]
      = (inner ℝ ((hmem s).toLp (X s)) ((hmem t).toLp (X t)) : ℝ) := by
    intro s t
    rw [covariance_eq_sub (hmem s) (hmem t), hmean s, hmean t, inner_toLp]
    simp [Pi.mul_apply]
  -- the covariance at a nonnegative lag `m`
  have hkey : ∀ (s t : ℤ) (m : ℕ), s - t = (m : ℤ) →
      cov[X s, X t; μ] = σ2 * ∑' l : ℕ, ψ (m + l) * ψ l := by
    intro s t m hd
    rw [hcovXL]
    refine tendsto_nhds_unique ((hconv s).inner (hconv t)) ?_
    have heq : ∀ N : ℕ, (inner ℝ (psumLp hε ψ s N) (psumLp hε ψ t N) : ℝ)
        = σ2 * ∑ l ∈ Finset.range (N - m), ψ (m + l) * ψ l := fun N => by
      rw [inner_psumLp, integral_psum_mul hε ψ hd]
    simp only [heq]
    refine Filter.Tendsto.const_mul _ ?_
    exact ((summable_shift hψ m).hasSum.tendsto_sum_nat).comp
      (Filter.tendsto_atTop_atTop.2 fun b => ⟨b + m, fun a ha => by omega⟩)
  -- ... hence at every lag, by symmetry
  have hcov : ∀ s t : ℤ, cov[X s, X t; μ] = σ2 * ∑' j : ℕ, ψ j * ψ (j + (s - t).natAbs) := by
    have hconvert : ∀ m : ℕ, (∑' l : ℕ, ψ (m + l) * ψ l) = ∑' j : ℕ, ψ j * ψ (j + m) :=
      fun m => tsum_congr fun l => by rw [mul_comm, add_comm m l]
    intro s t
    by_cases h : t ≤ s
    · rw [hkey s t (s - t).natAbs (Int.natAbs_of_nonneg (by omega)).symm, hconvert]
    · rw [covariance_comm, hkey t s (s - t).natAbs (by omega), hconvert]
  refine ⟨⟨hmem, fun s t => by rw [hmean s, hmean t], fun t k => ?_⟩, fun k => ?_⟩
  · have h1 : t + k - t = k := by ring
    rw [hcov (t + k) t, hcov k 0, sub_zero, h1]
  · change cov[X k, X 0; μ] = _
    rw [hcov k 0, sub_zero]

/-- **Strict stationarity under i.i.d. innovations** (FY §2.1.2, asserted): a linear
process over i.i.d. noise is strictly stationary. -/
theorem IsLinearProcessOf.isStrictlyStationary [IsProbabilityMeasure μ] {ψ : ℕ → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsIIDNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) :
    IsStrictlyStationary X μ := by
  intro n t k
  have hvm : ∀ (c : ℤ) (N : ℕ), Measurable fun ω (i : Fin n) => psum ψ ε (t i + c) N ω :=
    fun c N => measurable_pi_lambda _ fun i => measurable_psum hε.measurable ψ _ _
  have hXm : ∀ c : ℤ, Measurable fun ω (i : Fin n) => X (t i + c) ω :=
    fun c => measurable_pi_lambda _ fun i => hmeas _
  obtain ⟨ns, hns⟩ := exists_subseq_window hX hε.measurable hmeas t k
  haveI : IsProbabilityMeasure (μ.map fun ω (i : Fin n) => X (t i + k) ω) :=
    Measure.isProbabilityMeasure_map (hXm k).aemeasurable
  haveI : IsProbabilityMeasure (μ.map fun ω (i : Fin n) => X (t i + 0) ω) :=
    Measure.isProbabilityMeasure_map (hXm 0).aemeasurable
  have hgoal : (μ.map fun ω (i : Fin n) => X (t i + k) ω)
      = μ.map fun ω (i : Fin n) => X (t i + 0) ω := by
    refine MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    -- dominated convergence along the subsequence
    have hlim : ∀ c : ℤ, (c = k ∨ c = 0) →
        Tendsto (fun j => ∫ ω, f (fun i => psum ψ ε (t i + c) (ns j) ω) ∂μ) atTop
          (𝓝 (∫ ω, f (fun i => X (t i + c) ω) ∂μ)) := by
      intro c hc
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun j => (f.continuous.measurable.comp (hvm c (ns j))).aestronglyMeasurable)
        (integrable_const _) (fun j => Eventually.of_forall fun ω => f.norm_coe_le_norm _) ?_
      filter_upwards [hns c hc] with ω hω using (f.continuous.tendsto _).comp hω
    -- at every stage the two windows of partial sums have the same law
    have hstep : ∀ N : ℕ, ∫ ω, f (fun i => psum ψ ε (t i + k) N ω) ∂μ
        = ∫ ω, f (fun i => psum ψ ε (t i + 0) N ω) ∂μ := by
      intro N
      have h1 : ∀ c : ℤ, ∫ ω, f (fun i => psum ψ ε (t i + c) N ω) ∂μ
          = ∫ y, f y ∂(μ.map fun ω (i : Fin n) => psum ψ ε (t i + c) N ω) := fun c =>
        (integral_map (hvm c N).aemeasurable f.continuous.aestronglyMeasurable).symm
      rw [h1 k, h1 0]
      congr 1
      have h2 : (μ.map fun ω (i : Fin n) => psum ψ ε (t i + 0) N ω)
          = μ.map fun ω (i : Fin n) => psum ψ ε (t i) N ω := by simp
      rw [h2, map_psum_vec hε ψ t N k]
    rw [integral_map (hXm k).aemeasurable f.continuous.aestronglyMeasurable,
      integral_map (hXm 0).aemeasurable f.continuous.aestronglyMeasurable]
    refine tendsto_nhds_unique (hlim k (Or.inl rfl)) ?_
    simpa only [hstep] using hlim 0 (Or.inr rfl)
  simpa using hgoal

/-- **Almost-sure convergence under independence** (FY cites Chow & Teicher 1997, Cor. 3
p. 117). With `ℓ¹` coefficients the general Kolmogorov series theorem is not needed: the
series converges *absolutely* a.e., because `E Σ_j |ψ_j ε_{t−j}| = (Σ_j |ψ_j|) E|ε_0|`
is finite; an `L²`-convergent subsequence identifies the a.e. limit with `X_t`. -/
theorem IsLinearProcessOf.ae_tendsto [IsProbabilityMeasure μ] {ψ : ℕ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hX : IsLinearProcessOf ψ X ε μ)
    (hψ : Summable fun j => |ψ j|) (hε : IsIIDNoise ε σ2 μ)
    (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun N => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) atTop (𝓝 (X t ω)) := by
  -- the noise has one common finite first absolute moment
  have hC : eLpNorm (ε 0) 1 μ ≠ ∞ := (hε.memLp.mono_exponent one_le_two).2.ne
  have hnorm : ∀ s : ℤ, ∫⁻ ω, ‖ε s ω‖ₑ ∂μ = eLpNorm (ε 0) 1 μ := by
    intro s
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact (hε.identDistrib s 0).eLpNorm_eq 1
  -- the coefficients are `ℓ¹`, so the series converges absolutely in `L¹`
  have hcoef : (∑' j : ℕ, ‖ψ j‖ₑ) ≠ ∞ := tsum_enorm_ne_top_of_summable hψ
  have hlint : ∫⁻ ω, ∑' j : ℕ, ‖ψ j * ε (t - (j : ℕ)) ω‖ₑ ∂μ
      = (∑' j : ℕ, ‖ψ j‖ₑ) * eLpNorm (ε 0) 1 μ := by
    rw [lintegral_tsum fun j => ((hε.measurable (t - (j : ℕ))).const_mul (ψ j)).enorm.aemeasurable,
      ← ENNReal.tsum_mul_right]
    refine tsum_congr fun j => ?_
    simp_rw [enorm_mul]
    rw [lintegral_const_mul _ (hε.measurable (t - (j : ℕ))).enorm, hnorm]
  -- hence it converges absolutely almost everywhere
  have hfin : ∀ᵐ ω ∂μ, (∑' j : ℕ, ‖ψ j * ε (t - (j : ℕ)) ω‖ₑ) ≠ ∞ := by
    refine (ae_lt_top' ?_ ?_).mono fun ω hω => hω.ne
    · exact AEMeasurable.ennreal_tsum fun j =>
        ((hε.measurable (t - (j : ℕ))).const_mul (ψ j)).enorm.aemeasurable
    · rw [hlint]
      exact ENNReal.mul_ne_top hcoef hC
  -- an `L²`-convergent subsequence pins the a.e. limit down to `X t`
  obtain ⟨ns, hmono, hns⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun N => (measurable_psum hε.measurable ψ t N).aestronglyMeasurable)
      (hmeas t).aestronglyMeasurable
      (tendsto_eLpNorm_psum hX t)).exists_seq_tendsto_ae
  filter_upwards [hfin, hns] with ω hω hωns
  have hsummable : Summable fun j : ℕ => ψ j * ε (t - (j : ℕ)) ω :=
    summable_of_tsum_enorm_ne_top hω
  have hfull : Tendsto (fun N => ∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω) atTop
      (𝓝 (∑' j : ℕ, ψ j * ε (t - (j : ℕ)) ω)) := hsummable.hasSum.tendsto_sum_nat
  have hlimeq : (∑' j : ℕ, ψ j * ε (t - (j : ℕ)) ω) = X t ω :=
    tendsto_nhds_unique (hfull.comp hmono.tendsto_atTop) hωns
  rwa [hlimeq] at hfull

end StatLean.TimeSeries
