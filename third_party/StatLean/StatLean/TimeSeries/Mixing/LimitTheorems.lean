module
public import StatLean.TimeSeries.Mixing.Inequalities
public import StatLean.TimeSeries.Mixing.Relations
public import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
public import StatLean.TimeSeries.ForMathlib.Ergodic.Birkhoff

@[expose] public section

/-!
# Limit theorems for α-mixing processes (FY §2.6.3, pp. 74–76)

* **Theorem 2.20(ii)** (in-text proof): bounded zero-mean strictly stationary with
  `Σ α(j) < ∞` ⇒ the ACVF is absolutely summable and
  `n⁻¹ Var(S_n) → γ(0) + 2 Σ_{j≥1} γ(j)` (eq. (2.63)). **Erratum**: the book's display
  bounds `|γ(j)| ≤ 4α(j){E|X_1|}²`; the correct Billingsley bound is `4α(j)C²` — we
  state and use the corrected form.
* **Theorem 2.21(ii)** (in-text proof, pp. 75–76): additionally `σ² > 0` ⇒
  `S_n/√n →d N(0, σ²)`, `σ² = γ(0) + 2Σγ(j)` — the Bernstein-block scheme: big blocks
  of length `l_n ≈ n^{3/4}`, small blocks `s_n ≈ n^{1/4}`, block count `k_n ≈ n^{1/4}`;
  small-block negligibility in `L²`; characteristic-function factorization via
  Volkonskii–Rozanov (`16(k_n − 1)α(s_n) → 0`, using `m·α(m) → 0` from monotone +
  summable). **Note.** Strict stationarity makes the big blocks *identically
  distributed*, so the factorized characteristic function is the single power
  `(φ_n)^{k_n}` — no independent-copy triangular array (and hence no appeal to the
  Lindeberg double-array CLT) is needed.
  **STATUS: PROVED, axiom-clean** (wave `ts/s5b`), by the **cubic/adaptive-block** route,
  not by a Lindeberg split. (a) small-block negligibility, (b) the Volkonskii–Rozanov
  factorization and (c) the closing scalar limit `(φ_n)^{k_n} → e^{−σ²u²/2}` are all
  proved. (c) runs through the block expansion `E e^{i v B} − 1 = −(v²/2) E B² + R`
  (`charFun_block_expand`) and the **global cubic** bound on `R`
  (`norm_integral_remainder_cubic_le`: `‖R‖ ≤ 4|v|³√(E B² · E B⁴)`), which needs *no*
  truncation level and hence no uniform-integrability input. The fourth moment is supplied
  by `m4_tendsto_moment4_div_cube` (`E S_l⁴ = o(l³)` **from `Σ α(j) < ∞` alone**, via the
  sorted-4-tuple largest-gap split plus a Cesàro count), and the block lengths by
  `exists_block_scheme_adaptive` (an `α`-dependent `l_n ≍ √n a_n`, `s_n ≍ k_n ≍ √n/a_n`,
  with `a_n → ∞` slowly enough that `E S_{l_n}⁴ = o(l_n n)`).
  The former named debt `lindeberg_blocks_debt` is **no longer used by anything**, and is
  itself now **PROVED** (wave `ts/s10`): being *equivalent* to 2.21(ii) (see its docstring),
  it cannot be closed by the cubic route, but it *is* a corollary of the finished CLT —
  `S_l/√l →d N(0,σ²)` plus `E S_l²/l → σ²` makes `S_l²/l` uniformly integrable. That
  derivation (`tail_le_sub_min`, `exists_tail_threshold`) goes through Lévy continuity,
  which is why this file now imports `MeasureTheory.Measure.LevyConvergence`.
* **Theorem 2.20(i)** (Bosq 1998 §1.5) — the `δ`-moment variance rate: **PROVED**, and
  axiom-clean. The Billingsley bound `|γ(n)| ≤ 4α(n)C²` is replaced by **Davydov**
  (`Mixing/Inequalities.abs_covariance_le_davydov` at `p = q = δ`), whose side condition
  `1/p + 1/q < 1` is exactly `δ > 2`: `|γ(n)| ≤ 8 α(n)^{1−2/δ} ‖X_0‖_δ²`. The limit itself
  is the shared Fejér/Tannery core `tendsto_var_rate_of_summable`, which 2.20(ii) also uses.
* **Theorem 2.21(i)** (Peligrad; the `δ`-moment CLT) — **PROVED** by **truncation onto
  2.21(ii)**. Clamp and re-centre, `Y^M_t = clamp_M(X_t) − E clamp_M(X_0)`,
  `Z^M_t = X_t − Y^M_t`; both are common measurable transforms of `X`, hence strictly
  stationary with `α_{Y^M}, α_{Z^M} ≤ α_X` (`isStrictlyStationary_comp`,
  `alphaCoeff_comp_le`), and `Σ α^{1−2/δ} < ∞` forces `Σ α < ∞` because `α ≤ 1`. The two
  limits in `M` both come from 2.20(i): `σ_Z(M)² = Σ_k γ_{Z^M}(k) → 0` by dominated
  convergence over the lags (dominant: Davydov on `Z^M` with the `M`-uniform envelope
  `|Z^M_0| ≤ |X_0| + E|X_0|`; per-lag limit: the AM–GM bound `|γ_{Z^M}(k)| ≤ E(Z^M_0)²`),
  and `σ_Y(M)² → σ²` by Minkowski at every `n`. **Now axiom-clean**, since 2.21(ii) is.
* **Proposition 2.8 (SLLN)** — α-mixing + `E|X| < ∞` ⇒ `S_n/n → EX` a.s.: **PROVED**
  (wave `ts/s10b`) and axiom-clean, by the cited route, which wave `ts/s10` had shown to be
  the *only* one the frozen hypotheses support (`E|X_0| < ∞` and `α(n) → 0` with no rate
  give no second moment for Chebyshev, and the file's fourth-moment brick needs `|X| ≤ C`
  **and** `Σ α < ∞`). The four steps — shift invariance of the path law on `ℤ → ℝ`,
  `α(n) → 0 ⇒` ergodicity of the shift, Birkhoff, transport back to `Ω` — are executed in
  the `BirkhoffSLLN` section below; the pointwise ergodic theorem itself is the new
  `ForMathlib/Ergodic/Birkhoff.lean` (Garsia's maximal inequality ⇒ a.e. convergence to the
  conditional expectation on the invariant σ-algebra ⇒ the ergodic corollary).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.3,
Prop 2.8, Thms 2.20–2.21, eq. (2.63) (pp. 74–76). (`FY §2.6.3`.)

**Proof formalization notes.**
* Summability statements are spelled inline (`Summable fun k : ℤ => |acvf X μ k|`)
  rather than through `Spectral/SpectralDensity.HasSummableACVF` — this concept-layer
  file must not import the spectral assembly.
* `σ²` is packaged as `acvf X μ 0 + 2 * Σ'_{j : ℕ} acvf X μ (j + 1)`.
* The α-coefficient of the blocks is controlled through
  `IsStrictlyStationary.alphaMixCoeff_shift` (Relations) + `alphaMixCoeff_mono`.

**Bibliographic comments.** The Bernstein small-block/large-block method is
S. N. Bernstein (1927); Theorem 2.21's proof follows Ibragimov–Linnik (1971) Thm 18.4.1
as streamlined by FY. The δ-moment CLT (i) is M. Peligrad (*Invariance principles for
mixing sequences*, Ann. Probab. 1982-adjacent); Thm 2.20(i) is Bosq (1998) §1.5. The
SLLN via ergodicity is Doob (1953) ch. X / Ibragimov–Linnik (1971) ch. 17.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal symmDiff

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Private toolbox for the bounded α-mixing limit theorems

Shared bricks for Theorems 2.20(ii) and 2.21(ii): the Billingsley bound on the ACVF,
absolute summability of the ACVF, the `Λ·|D|` bound on the second moment of a partial sum
over an arbitrary index set, and the exact "triangular-weight" expansion of a double sum
`∑_{s,t<n} f(s−t)`. -/

section Toolbox

variable {X : ℤ → Ω → ℝ} {C : ℝ}

/-- Boundedness on a probability space forces `0 ≤ C`. -/
private lemma bound_nonneg [IsProbabilityMeasure μ]
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) : 0 ≤ C := by
  obtain ⟨ω, hω⟩ := (hbdd 0).exists
  exact le_trans (abs_nonneg _) hω

/-- A bounded measurable coordinate lies in every `L^p`. -/
private lemma memLp_of_bdd [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (t : ℤ) (p : ℝ≥0∞) : MemLp (X t) p μ := by
  refine MemLp.mono_exponent ?_ le_top
  refine memLp_top_of_bound (hmeas t).aestronglyMeasurable C ?_
  filter_upwards [hbdd t] with ω hω
  simpa [Real.norm_eq_abs] using hω

private lemma sigmaLE_le (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaLE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

private lemma sigmaGE_le (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaGE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

omit [MeasurableSpace Ω] in
private lemma measurable_comap_self (X : ℤ → Ω → ℝ) (s : ℤ) :
    Measurable[MeasurableSpace.comap (X s) inferInstance] (X s) :=
  fun _ hs => ⟨_, hs, rfl⟩

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLE (X : ℤ → Ω → ℝ) {s n : ℤ} (h : s ≤ n) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaLE X n :=
  le_iSup₂ (f := fun (s : ℤ) (_ : s ∈ Set.Iic n) =>
    MeasurableSpace.comap (X s) inferInstance) s h

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaGE (X : ℤ → Ω → ℝ) {s n : ℤ} (h : n ≤ s) :
    MeasurableSpace.comap (X s) inferInstance ≤ sigmaGE X n :=
  le_iSup₂ (f := fun (s : ℤ) (_ : s ∈ Set.Ici n) =>
    MeasurableSpace.comap (X s) inferInstance) s h

/-- **Billingsley bound on the ACVF** (FY Thm 2.20(ii), corrected constant `4α(n)C²`):
`γ(n) = Cov(X_n, X_0)` pairs the anchored past `σ{X_s : s ≤ 0}` (holding `X_0`) with the
future `σ{X_s : s ≥ n}` (holding `X_n`). -/
private lemma abs_acvf_le_alphaCoeff [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (n : ℕ) :
    |acvf X μ (n : ℤ)| ≤ 4 * alphaCoeff X μ n * C ^ 2 := by
  have h1 : sigmaLE X 0 ≤ (inferInstance : MeasurableSpace Ω) := sigmaLE_le hmeas 0
  have h2 : sigmaGE X (n : ℤ) ≤ (inferInstance : MeasurableSpace Ω) := sigmaGE_le hmeas _
  have hf : Measurable[sigmaLE X 0] (X 0) :=
    (measurable_comap_self X 0).mono (comap_le_sigmaLE X le_rfl) le_rfl
  have hg : Measurable[sigmaGE X (n : ℤ)] (X (n : ℤ)) :=
    (measurable_comap_self X _).mono (comap_le_sigmaGE X le_rfl) le_rfl
  have key := abs_covariance_le_of_bounded h1 h2 hf hg (hbdd 0) (hbdd (n : ℤ))
  rw [acvf, covariance_comm]
  calc |cov[X 0, X (n : ℤ); μ]|
      ≤ 4 * alphaMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ)) * C * C := key
    _ = 4 * alphaCoeff X μ n * C ^ 2 := by rw [alphaCoeff]; ring

/-- The ACVF of a (weakly) stationary process is even. -/
private lemma acvf_neg (hws : IsStationary X μ) (k : ℤ) : acvf X μ (-k) = acvf X μ k := by
  have h1 := hws.cov_shift k (-k)
  rw [add_neg_cancel] at h1
  rw [acvf, acvf, ← h1, covariance_comm]

/-- Absolute summability of the ACVF (first half of FY Thm 2.20(ii)). -/
private lemma summable_abs_acvf' [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ) (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    Summable fun k : ℤ => |acvf X μ k| := by
  have hws : IsStationary X μ := hstat.isStationary hmeas (memLp_of_bdd hmeas hbdd 0 2)
  have hpos : Summable fun n : ℕ => |acvf X μ (n : ℤ)| := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
      ((((summable_nat_add_iff 1).mpr hα).mul_left 4).mul_right (C ^ 2))
    exact_mod_cast abs_acvf_le_alphaCoeff hmeas hbdd (n + 1)
  refine Summable.of_nat_of_neg hpos ?_
  simpa only [acvf_neg hws] using hpos

/-- The lag-`(s − t)` covariance of the shifted coordinates. -/
private lemma cov_shift_pair (hws : IsStationary X μ) (s t : ℕ) :
    cov[X ((s : ℤ) + 1), X ((t : ℤ) + 1); μ] = acvf X μ ((s : ℤ) - (t : ℤ)) := by
  have h := hws.cov_shift ((t : ℤ) + 1) ((s : ℤ) - (t : ℤ))
  have e : ((t : ℤ) + 1) + ((s : ℤ) - (t : ℤ)) = (s : ℤ) + 1 := by ring
  rw [e] at h
  exact h

/-- The double sum of the ACVF over an arbitrary index set is at most `Λ · |D|`: for each
fixed `s` the map `t ↦ s − t` is injective, so the inner sum is dominated by the full
`ℤ`-series `Λ = Σ_k |γ(k)|`. -/
private lemma sum_sum_acvf_le (hsum : Summable fun k : ℤ => |acvf X μ k|) (D : Finset ℕ) :
    ∑ s ∈ D, ∑ t ∈ D, acvf X μ ((s : ℤ) - (t : ℤ))
      ≤ (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := by
  calc ∑ s ∈ D, ∑ t ∈ D, acvf X μ ((s : ℤ) - (t : ℤ))
      ≤ ∑ s ∈ D, ∑ t ∈ D, |acvf X μ ((s : ℤ) - (t : ℤ))| := by
        gcongr with s _ t _
        exact le_abs_self _
    _ ≤ ∑ _s ∈ D, ∑' k : ℤ, |acvf X μ k| := by
        refine Finset.sum_le_sum fun s _ => ?_
        have hinj : ∀ x ∈ D, ∀ y ∈ D, (s : ℤ) - (x : ℤ) = (s : ℤ) - (y : ℤ) → x = y := by
          intro x _ y _ h; omega
        have himg : ∑ k ∈ D.image (fun t : ℕ => (s : ℤ) - (t : ℤ)), |acvf X μ k|
            = ∑ t ∈ D, |acvf X μ ((s : ℤ) - (t : ℤ))| := Finset.sum_image hinj
        rw [← himg]
        exact hsum.sum_le_tsum _ (fun i _ => abs_nonneg _)
    _ = (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The partial sum over an arbitrary index set has mean zero. -/
private lemma integral_partialSum_eq_zero [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0) (D : Finset ℕ) :
    ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ∂μ = 0 := by
  have hsplit : ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ∂μ
      = ∑ t ∈ D, ∫ ω, X ((t : ℤ) + 1) ω ∂μ :=
    integral_finset_sum (f := fun (t : ℕ) ω => X ((t : ℤ) + 1) ω) D
      (fun t _ => (memLp_of_bdd hmeas hbdd ((t : ℤ) + 1) 1).integrable le_rfl)
  rw [hsplit]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [(hstat.identDistrib hmeas ((t : ℤ) + 1) 0).integral_eq, hmean]

/-- **The `Λ·|D|` second-moment bound.** For a bounded, zero-mean, strictly stationary
process with summable ACVF, the partial sum over an arbitrary finite index set `D` has
`E S_D² ≤ Λ |D|`, `Λ = Σ_{k ∈ ℤ} |γ(k)|`. This is the workhorse of both the variance rate
and the negligibility of the Bernstein small blocks. -/
private lemma integral_sq_partialSum_le [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hsum : Summable fun k : ℤ => |acvf X μ k|) (D : Finset ℕ) :
    ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ ≤ (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := by
  have hws : IsStationary X μ := hstat.isStationary hmeas (memLp_of_bdd hmeas hbdd 0 2)
  have hmemD : ∀ t ∈ D, MemLp (X ((t : ℤ) + 1)) 2 μ := fun t _ =>
    memLp_of_bdd hmeas hbdd _ 2
  have hfun : (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) = ∑ t ∈ D, X ((t : ℤ) + 1) := by
    funext ω; simp [Finset.sum_apply]
  have hmemS : MemLp (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) 2 μ := by
    rw [hfun]; exact memLp_finset_sum' (μ := μ) D hmemD
  have hvar : variance (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) μ
      = ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
    rw [variance_of_integral_eq_zero hmemS.aestronglyMeasurable.aemeasurable
      (integral_partialSum_eq_zero hmeas hstat hbdd hmean D)]
  rw [← hvar, variance_fun_sum' hmemD]
  calc ∑ s ∈ D, ∑ t ∈ D, cov[X ((s : ℤ) + 1), X ((t : ℤ) + 1); μ]
      = ∑ s ∈ D, ∑ t ∈ D, acvf X μ ((s : ℤ) - (t : ℤ)) := by
        exact Finset.sum_congr rfl fun s _ =>
          Finset.sum_congr rfl fun t _ => cov_shift_pair hws s t
    _ ≤ (∑' k : ℤ, |acvf X μ k|) * (D.card : ℝ) := sum_sum_acvf_le hsum D

end Toolbox

/-! ### The triangular-weight expansion of `∑_{s,t<n} f(s−t)` -/

section Triangular

/-- `{s − n : s < n} = [−n, 0)`. -/
private lemma sum_range_sub_last (f : ℤ → ℝ) (n : ℕ) :
    ∑ s ∈ Finset.range n, f ((s : ℤ) - (n : ℤ)) = ∑ k ∈ Finset.Ico (-(n : ℤ)) 0, f k := by
  have hinj : Function.Injective fun s : ℕ => (s : ℤ) - (n : ℤ) := by
    intro a b h; dsimp only at h; omega
  have hmap : (Finset.range n).map ⟨fun s : ℕ => (s : ℤ) - (n : ℤ), hinj⟩
      = Finset.Ico (-(n : ℤ)) 0 := by
    ext k
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro hk; exact ⟨(k + n).toNat, by omega, by omega⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- `{n − t : t ≤ n} = [0, n]`. -/
private lemma sum_range_last_sub (f : ℤ → ℝ) (n : ℕ) :
    ∑ t ∈ Finset.range (n + 1), f ((n : ℤ) - (t : ℤ)) = ∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), f k := by
  have hinj : Function.Injective fun t : ℕ => (n : ℤ) - (t : ℤ) := by
    intro a b h; dsimp only at h; omega
  have hmap : (Finset.range (n + 1)).map ⟨fun t : ℕ => (n : ℤ) - (t : ℤ), hinj⟩
      = Finset.Icc (0 : ℤ) (n : ℤ) := by
    ext k
    simp only [Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk, Finset.mem_Icc]
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro hk; exact ⟨((n : ℤ) - k).toNat, by omega, by omega⟩
  rw [← hmap, Finset.sum_map]
  rfl

/-- **Triangular-weight identity**: `∑_{s,t<n} f(s−t) = ∑_{|k|<n} (n − |k|) f(k)`. -/
private lemma sum_sub_double_eq (f : ℤ → ℝ) : ∀ n : ℕ,
    ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ))
      = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hIoo : Finset.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1) = Finset.Icc (-(n : ℤ)) (n : ℤ) := by
      ext k; simp only [Finset.mem_Ioo, Finset.mem_Icc]; omega
    have hsplit : Finset.Icc (-(n : ℤ)) (n : ℤ)
        = Finset.Ico (-(n : ℤ)) 0 ∪ Finset.Icc (0 : ℤ) (n : ℤ) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.Ico (-(n : ℤ)) 0) (Finset.Icc (0 : ℤ) (n : ℤ)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_Icc] at hk'
      omega
    -- left-hand side: peel the last row and the last column
    have hL : ∑ s ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1), f ((s : ℤ) - (t : ℤ))
        = (∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ)))
          + ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k := by
      rw [Finset.sum_range_succ]
      have hrow : ∀ s ∈ Finset.range n, ∑ t ∈ Finset.range (n + 1), f ((s : ℤ) - (t : ℤ))
          = (∑ t ∈ Finset.range n, f ((s : ℤ) - (t : ℤ))) + f ((s : ℤ) - (n : ℤ)) := by
        intro s _
        rw [Finset.sum_range_succ]
      rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, sum_range_sub_last,
        sum_range_last_sub, hsplit, Finset.sum_union hdisj]
      ring
    -- right-hand side: the two extreme lags carry weight `1`
    have hR : ∑ k ∈ Finset.Ioo (-((n : ℤ) + 1)) ((n : ℤ) + 1), (((n : ℝ) + 1) - |(k : ℝ)|) * f k
        = (∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k)
          + ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), f k := by
      rw [hIoo]
      have hshrink : ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k
          = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * f k := by
        refine (Finset.sum_subset ?_ ?_).symm
        · intro k hk
          simp only [Finset.mem_Ioo] at hk
          simp only [Finset.mem_Icc]
          omega
        · intro k hk hk'
          simp only [Finset.mem_Icc] at hk
          simp only [Finset.mem_Ioo, not_and_or, not_lt] at hk'
          have : |(k : ℝ)| = (n : ℝ) := by
            rcases hk' with h | h
            · have : k = -(n : ℤ) := by omega
              subst this; push_cast; simp
            · have : k = (n : ℤ) := by omega
              subst this; push_cast; simp
          rw [this]; ring
      rw [← hshrink, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hL, ih]
    push_cast
    push_cast at hR
    rw [hR]

end Triangular

/-- The two-sided ACVF series is the book's `σ² = γ(0) + 2 Σ_{j ≥ 1} γ(j)` (evenness of the
ACVF folds the negative lags onto the positive ones). -/
private lemma tsum_acvf_eq [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hws : IsStationary X μ) (hsum : Summable fun k : ℤ => |acvf X μ k|) :
    (∑' k : ℤ, acvf X μ k) = acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) := by
  have hsumZ : Summable fun k : ℤ => acvf X μ k := hsum.of_abs
  have hsumN : Summable fun n : ℕ => acvf X μ (n : ℤ) := hsumZ.comp_injective Nat.cast_injective
  have hsumN1 : Summable fun n : ℕ => acvf X μ ((n : ℤ) + 1) := by
    have h := (summable_nat_add_iff 1).mpr hsumN
    refine h.congr fun n => ?_
    have e : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    rw [e]
  have hneg : Summable fun n : ℕ => acvf X μ (-((n : ℤ) + 1)) := by
    simpa only [acvf_neg hws] using hsumN1
  have hnegeq : (∑' n : ℕ, acvf X μ (-((n : ℤ) + 1))) = ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) :=
    tsum_congr fun n => acvf_neg hws _
  have hshift : (∑' n : ℕ, acvf X μ ((n + 1 : ℕ) : ℤ))
      = ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) :=
    tsum_congr fun n => by
      rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
  have hpos : (∑' n : ℕ, acvf X μ (n : ℤ))
      = acvf X μ 0 + ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) := by
    rw [hsumN.tsum_eq_zero_add, hshift]
    norm_num
  rw [tsum_of_nat_of_neg_add_one hsumN hneg, hnegeq, hpos]
  ring

/-- **The variance rate from summability alone.** For a weakly stationary process whose
ACVF is absolutely summable, `n⁻¹ Var(S_n) → Σ_{k ∈ ℤ} γ(k) = γ(0) + 2 Σ_{j ≥ 1} γ(j)`:
the exact triangular-weight expansion turns `n⁻¹ Var(S_n)` into the Fejér-weighted series
`Σ_k (1 − |k|/n) γ(k)`, and Tannery's theorem (dominated convergence for series, dominant
`|γ|`) passes to the limit.

This is the analytic core shared by FY Theorem 2.20(ii) (bounded, `Σ α < ∞`) and its
`δ`-moment counterpart 2.20(i) (`L^δ`, `Σ α^{1−2/δ} < ∞`) — the two differ only in how
absolute summability of the ACVF is obtained (Billingsley vs. Davydov). -/
private lemma tendsto_var_rate_of_summable [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hws : IsStationary X μ) (hsum : Summable fun k : ℤ => |acvf X μ k|) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
        variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ) atTop
      (𝓝 (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))) := by
  classical
  -- (a) the `ℤ`-series of the ACVF is the book's `σ² = γ(0) + 2 Σ_{j≥1} γ(j)`
  have hσeq : (∑' k : ℤ, acvf X μ k)
      = acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) := tsum_acvf_eq hws hsum
  -- (b) the exact triangular-weight expansion of `Var S_n`
  have hvar : ∀ n : ℕ, variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ
      = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), ((n : ℝ) - |(k : ℝ)|) * acvf X μ k := by
    intro n
    have h1 : ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n,
          cov[X ((s : ℤ) + 1), X ((t : ℤ) + 1); μ]
        = ∑ s ∈ Finset.range n, ∑ t ∈ Finset.range n, acvf X μ ((s : ℤ) - (t : ℤ)) :=
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => cov_shift_pair hws s t
    have h0 := variance_fun_sum' (μ := μ) (X := fun t : ℕ => X ((t : ℤ) + 1))
      (s := Finset.range n) (fun t _ => hws.memLp _)
    rw [h0, h1, sum_sub_double_eq]
  -- (c) the Fejér-weighted family, extended by zero to all of `ℤ`
  set g : ℕ → ℤ → ℝ := fun n k =>
    if k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ) then (1 - |(k : ℝ)| / (n : ℝ)) * acvf X μ k else 0
    with hgdef
  have hns : ∀ n : ℕ, (n : ℝ)⁻¹ * variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ
      = ∑' k : ℤ, g n k := by
    intro n
    have hz : ∑' k : ℤ, g n k = ∑ k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ), g n k :=
      tsum_eq_sum fun k hk => by simp only [hgdef, if_neg hk]
    rw [hvar n, hz]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      simp only [hgdef, if_pos hk]
      field_simp
  -- (d) Tannery / dominated convergence for series: the Fejér weights tend to `1`
  have hdom : Tendsto (fun n : ℕ => ∑' k : ℤ, g n k) atTop (𝓝 (∑' k : ℤ, acvf X μ k)) := by
    refine tendsto_tsum_of_dominated_convergence hsum (fun k => ?_) (Eventually.of_forall ?_)
    · have hk : ∀ᶠ n : ℕ in atTop, g n k = (1 - |(k : ℝ)| / (n : ℝ)) * acvf X μ k := by
        filter_upwards [eventually_ge_atTop (k.natAbs + 1)] with n hn
        have hmem : k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ) := by
          simp only [Finset.mem_Ioo]
          have : (k.natAbs : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
          omega
        simp only [hgdef, if_pos hmem]
      refine Tendsto.congr' (hk.mono fun n h => h.symm) ?_
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - |(k : ℝ)| / (n : ℝ)) atTop (𝓝 1) := by
        simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat |(k : ℝ)|)
      simpa using h1.mul_const (acvf X μ k)
    · intro n k
      by_cases hk : k ∈ Finset.Ioo (-(n : ℤ)) (n : ℤ)
      · simp only [hgdef, if_pos hk, Real.norm_eq_abs, abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        simp only [Finset.mem_Ioo] at hk
        have hklt : |(k : ℝ)| < (n : ℝ) := by
          rw [abs_lt]
          exact ⟨by exact_mod_cast hk.1, by exact_mod_cast hk.2⟩
        have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg _) hklt
        have hd0 : 0 ≤ |(k : ℝ)| / (n : ℝ) := div_nonneg (abs_nonneg _) hnpos.le
        have hd1 : |(k : ℝ)| / (n : ℝ) < 1 := (div_lt_one hnpos).mpr hklt
        rw [abs_le]
        constructor <;> linarith
      · simp only [hgdef, if_neg hk, norm_zero]
        exact abs_nonneg _
  rw [← hσeq]
  exact (Tendsto.congr (fun n => (hns n).symm) hdom)

/-- **FY Theorem 2.20(ii)** (in-text; erratum `4α(j)C²` applied): bounded zero-mean
strictly stationary + summable α ⇒ summable ACVF and the variance-rate identity
(2.63). -/
theorem summable_acvf_and_var_rate_of_bounded [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.20(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.20(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    (Summable fun k : ℤ => |acvf X μ k|) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ) atTop
        (𝓝 (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))) := by
  classical
  have hws : IsStationary X μ := hstat.isStationary hmeas (memLp_of_bdd hmeas hbdd 0 2)
  have hsum : Summable fun k : ℤ => |acvf X μ k| := summable_abs_acvf' hmeas hstat hbdd hα
  exact ⟨hsum, tendsto_var_rate_of_summable hws hsum⟩

/-! ### Analytic bricks for the Bernstein-block CLT -/

section Bernstein

/-- Third-order Taylor control of `e^{ix}` in the two forms the block expansion consumes:
a **global cubic** bound (for the bulk, where the phase is small) and a **global
quadratic** bound (for the Lindeberg tail, where the phase is not small). Both follow from
`Complex.exp_bound` at `n = 3` on `|x| ≤ 1` and from the triangle inequality
(`‖e^{ix}‖ = 1`) on `|x| > 1`. -/
private lemma norm_expI_taylor (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖
        ≤ 4 * |x| ^ 3 ∧
      ‖Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖
        ≤ 4 * x ^ 2 := by
  have hzn : ‖(x : ℂ) * Complex.I‖ = |x| := by
    simp
  have hI2 : ((x : ℂ) * Complex.I) ^ 2 = -(x : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  have hsum : ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ m / (Nat.factorial m : ℂ)
      = 1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, hI2]
    push_cast
    ring
  have habs : 0 ≤ |x| := abs_nonneg x
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  by_cases hx : |x| ≤ 1
  · have hb := Complex.exp_bound (x := (x : ℂ) * Complex.I) (by rw [hzn]; exact hx)
      (n := 3) (by norm_num)
    rw [hsum, hzn] at hb
    have hb' : ‖Complex.exp ((x : ℂ) * Complex.I)
        - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ |x| ^ 3 := by
      refine hb.trans ?_
      have : ((3 : ℕ).succ : ℝ) * (((Nat.factorial 3 : ℝ)) * (3 : ℝ))⁻¹ ≤ 1 := by
        norm_num [Nat.factorial]
      nlinarith [pow_nonneg habs 3]
    refine ⟨hb'.trans (by nlinarith [pow_nonneg habs 3]), hb'.trans ?_⟩
    have : |x| ^ 3 = |x| * x ^ 2 := by rw [← hsq]; ring
    nlinarith [sq_nonneg x]
  · rw [not_le] at hx
    have hE : ‖Complex.exp ((x : ℂ) * Complex.I)
        - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 1 + (1 + |x| + x ^ 2 / 2) := by
      refine (norm_sub_le _ _).trans ?_
      gcongr
      · exact le_of_eq (Complex.norm_exp_ofReal_mul_I x)
      · refine (norm_sub_le _ _).trans ?_
        gcongr
        · refine (norm_add_le _ _).trans ?_
          rw [hzn, norm_one]
        · rw [norm_div, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
            Complex.norm_ofNat, abs_of_nonneg (sq_nonneg x)]
    have h1 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
    have h2 : |x| ≤ x ^ 2 := by nlinarith
    have hq : ‖Complex.exp ((x : ℂ) * Complex.I)
        - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 4 * x ^ 2 := by
      refine hE.trans ?_; linarith
    refine ⟨hq.trans ?_, hq⟩
    have : x ^ 2 ≤ |x| ^ 3 := by
      rw [← hsq]; nlinarith [pow_nonneg habs 2]
    linarith

/-- Telescoping bound for powers of unit-modulus complex numbers. -/
private lemma norm_pow_sub_pow_le_of_norm_le_one {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ∀ k : ℕ, ‖a ^ k - b ^ k‖ ≤ (k : ℝ) * ‖a - b‖ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by ring
    rw [hstep]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow]
    have h1 : ‖a‖ * ‖a ^ k - b ^ k‖ ≤ 1 * ((k : ℝ) * ‖a - b‖) :=
      mul_le_mul ha ih (norm_nonneg _) zero_le_one
    have h2 : ‖a - b‖ * ‖b‖ ^ k ≤ ‖a - b‖ * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hb) (norm_nonneg _)
    push_cast
    linarith

/-- **`m · α(m) → 0`** for a monotone summable mixing sequence: the tail block
`Σ_{m/2 ≤ j < m} α(j)` dominates `(m/2)·α(m)` and vanishes by the Cauchy criterion. -/
private lemma tendsto_mul_alphaCoeff [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    Tendsto (fun m : ℕ => (m : ℝ) * alphaCoeff X μ m) atTop (𝓝 0) := by
  have hanti : Antitone fun n : ℕ => alphaCoeff X μ n := alphaCoeff_antitone X
  have hnn : ∀ n : ℕ, 0 ≤ alphaCoeff X μ n := fun _ => alphaMixCoeff_nonneg
  have hT : Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, alphaCoeff X μ j) atTop
      (𝓝 (∑' j : ℕ, alphaCoeff X μ j)) := hα.hasSum.tendsto_sum_nat
  have hhalf : Tendsto (fun m : ℕ => m / 2) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨2 * b + 1, fun a ha => by omega⟩
  have hdiff : Tendsto (fun m : ℕ => (∑ j ∈ Finset.range m, alphaCoeff X μ j)
      - ∑ j ∈ Finset.range (m / 2), alphaCoeff X μ j) atTop (𝓝 0) := by
    simpa using hT.sub (hT.comp hhalf)
  refine squeeze_zero (fun m => mul_nonneg (Nat.cast_nonneg _) (hnn m)) (fun m => ?_)
    (by simpa using hdiff.const_mul 2)
  have hle : m / 2 ≤ m := Nat.div_le_self _ _
  have hIco : ∑ j ∈ Finset.Ico (m / 2) m, alphaCoeff X μ j
      = (∑ j ∈ Finset.range m, alphaCoeff X μ j)
        - ∑ j ∈ Finset.range (m / 2), alphaCoeff X μ j := by
    rw [Finset.sum_Ico_eq_sub _ hle]
  have hcard : ((Finset.Ico (m / 2) m).card : ℝ) * alphaCoeff X μ m
      ≤ ∑ j ∈ Finset.Ico (m / 2) m, alphaCoeff X μ j := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun j hj => ?_
    exact hanti (le_of_lt (Finset.mem_Ico.mp hj).2)
  rw [← hIco]
  have hc : ((Finset.Ico (m / 2) m).card : ℝ) = ((m - m / 2 : ℕ) : ℝ) := by
    rw [Nat.card_Ico]
  have hge : (m : ℝ) ≤ 2 * ((m - m / 2 : ℕ) : ℝ) := by
    have : m ≤ 2 * (m - m / 2) := by omega
    exact_mod_cast this
  nlinarith [hnn m, hcard, hc ▸ hcard]

/-! #### The block scheme -/

private lemma tendsto_natSqrt : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b * b, fun a ha => by
    calc b = Nat.sqrt (b * b) := (Nat.sqrt_eq b).symm
      _ ≤ Nat.sqrt a := Nat.sqrt_le_sqrt ha⟩

private lemma tendsto_natSqrt_div : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / (n : ℝ))
    atTop (𝓝 0) := by
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.sqrt n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp tendsto_natSqrt
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hone
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hs : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
  have hsq : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le n
  have hs0 : (0 : ℝ) < (Nat.sqrt n : ℝ) := by exact_mod_cast hs
  rw [div_le_div_iff₀ (by positivity) hs0]
  nlinarith

/-- **The Bernstein block scheme.** Small blocks `s_n ≈ n^{1/4}`, big blocks
`l_n = ⌊n/s_n⌋ + 1 ≈ n^{3/4}`, block count `k_n = ⌊n/(l_n + s_n)⌋ ≈ n^{1/4}`. The choice
`l_n s_n > n` forces `k_n ≤ s_n`, which is exactly what turns `m α(m) → 0` into the
Volkonskii–Rozanov budget `k_n α(s_n) → 0`.

**Superseded** (wave `ts/s5b`) by `exists_block_scheme_adaptive`, which the CLT now uses:
the fixed exponent `3/4` cannot meet the cubic budget `E S_{l_n}⁴ = o(l_n n)` under
summability alone (that needs `√n · η_{n^{3/4}} → 0`, i.e. a *rate* for `η`). Kept as the
`s_n = ⌊n^{1/4}⌋ + 1` instance of `exists_block_scheme_of_small`, which is what the
adaptive scheme is built from. -/
private lemma exists_block_scheme [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    ∃ l s k : ℕ → ℕ,
      (∀ n, 1 ≤ s n) ∧ (∀ n, 1 ≤ l n) ∧ (∀ n, k n * (l n + s n) ≤ n) ∧
      Tendsto (fun n : ℕ => (l n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
  classical
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℕ, ∀ n, s n = Nat.sqrt (Nat.sqrt n) + 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l : ℕ → ℕ, ∀ n, l n = n / s n + 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ → ℕ, ∀ n, k n = n / (l n + s n) := ⟨_, fun _ => rfl⟩
  have hs1 : ∀ n, 1 ≤ s n := fun n => by rw [hsdef]; omega
  have hl1 : ∀ n, 1 ≤ l n := fun n => by rw [hldef]; exact Nat.le_add_left 1 _
  have hfit : ∀ n, k n * (l n + s n) ≤ n := fun n => by rw [hkdef]; exact Nat.div_mul_le_self _ _
  -- `s_n l_n > n`: the big blocks overshoot, which is what caps the block count
  have hsl : ∀ n, n < s n * l n := by
    intro n
    have h1 := Nat.div_add_mod n (s n)
    have h2 : n % s n < s n := Nat.mod_lt _ (hs1 n)
    have h3 : s n * l n = s n * (n / s n) + s n := by rw [hldef]; ring
    omega
  have hks : ∀ n, k n ≤ s n := by
    intro n
    by_contra hcon
    rw [not_le] at hcon
    have h1 : k n * l n ≤ n :=
      le_trans (Nat.mul_le_mul_left (k n) (Nat.le_add_right (l n) (s n))) (hfit n)
    have h2 : (s n + 1) * l n ≤ k n * l n := Nat.mul_le_mul_right _ hcon
    have h3 : (s n + 1) * l n = s n * l n + l n := by ring
    have h4 := hsl n
    have h5 := hl1 n
    omega
  -- the small blocks grow
  have hstopN : Tendsto s atTop atTop :=
    tendsto_atTop_mono (fun n => by simp only [Function.comp_apply, hsdef]; omega)
      (tendsto_natSqrt.comp tendsto_natSqrt)
  have hinvs : Tendsto (fun n : ℕ => (1 : ℝ) / (s n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hstopN
  have hinvn : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  -- `s_n² / n → 0`
  have hs2 : ∀ n, s n ^ 2 ≤ 3 * Nat.sqrt n + 1 := by
    intro n
    have hq : Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n :=
      Nat.sqrt_le (Nat.sqrt n)
    have hq' : Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n := Nat.sqrt_le_self _
    have : s n ^ 2 = Nat.sqrt (Nat.sqrt n) * Nat.sqrt (Nat.sqrt n)
        + 2 * Nat.sqrt (Nat.sqrt n) + 1 := by rw [hsdef]; ring
    omega
  have hsqn : Tendsto (fun n : ℕ => (s n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 3 * ((Nat.sqrt n : ℝ) / (n : ℝ)) + 1 / (n : ℝ))
        atTop (𝓝 0) := by
      simpa using (tendsto_natSqrt_div.const_mul 3).add hinvn
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb : (s n : ℝ) ^ 2 ≤ 3 * (Nat.sqrt n : ℝ) + 1 := by exact_mod_cast hs2 n
    have hrw : 3 * ((Nat.sqrt n : ℝ) / (n : ℝ)) + 1 / (n : ℝ)
        = (3 * (Nat.sqrt n : ℝ) + 1) / (n : ℝ) := by ring
    rw [hrw, div_le_div_iff_of_pos_right hn0]
    exact hb
  -- `l_n / n → 0`
  have hln0 : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
      (by simpa only [add_zero] using hinvs.add hinvn)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hs1 n
    have hdiv : ((n / s n : ℕ) : ℝ) ≤ (n : ℝ) / (s n : ℝ) := Nat.cast_div_le
    have hlc : (l n : ℝ) ≤ (n : ℝ) / (s n : ℝ) + 1 := by
      rw [hldef]; push_cast; linarith
    calc (l n : ℝ) / (n : ℝ) ≤ ((n : ℝ) / (s n : ℝ) + 1) / (n : ℝ) := by gcongr
      _ = 1 / (s n : ℝ) + 1 / (n : ℝ) := by field_simp
  -- `l_n → ∞`
  have hltop : Tendsto (fun n : ℕ => (l n : ℝ)) atTop atTop := by
    have hhalf : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / 2) atTop atTop :=
      Tendsto.atTop_div_const (by norm_num)
        (tendsto_natCast_atTop_atTop.comp tendsto_natSqrt)
    refine tendsto_atTop_mono' _ ?_ hhalf
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hr1 : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
    have hsr : s n ≤ 2 * Nat.sqrt n := by
      have := Nat.sqrt_le_self (Nat.sqrt n)
      rw [hsdef]; omega
    have hrr : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le n
    have hs0 : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hs1 n
    have hnl : (n : ℝ) < (s n : ℝ) * (l n : ℝ) := by exact_mod_cast hsl n
    have hsr' : (s n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by exact_mod_cast hsr
    have hr0 : (0 : ℝ) < (Nat.sqrt n : ℝ) := by exact_mod_cast hr1
    nlinarith [hnl, hrr, hsr', hr0]
  -- `k_n l_n / n → 1`
  have hkl : Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have hsn0 : Tendsto (fun n : ℕ => (s n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hsqn
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hs1' : (1 : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hs1 n
      gcongr
      nlinarith
    have hlow : Tendsto (fun n : ℕ => 1 - (s n : ℝ) ^ 2 / (n : ℝ) - (l n : ℝ) / (n : ℝ)
        - (s n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds.sub hsqn).sub hln0).sub hsn0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hkq : (l n + s n) * k n + n % (l n + s n) = n := by
        rw [hkdef]; exact Nat.div_add_mod n (l n + s n)
      have hmlt : n % (l n + s n) < l n + s n := Nat.mod_lt _ (by have := hl1 n; omega)
      have hexp : (l n + s n) * k n = k n * l n + k n * s n := by ring
      have hks' : k n * s n ≤ s n * s n := Nat.mul_le_mul_right _ (hks n)
      have hnat : n ≤ k n * l n + s n * s n + l n + s n := by omega
      have hcast : (n : ℝ) ≤ ((k n * l n : ℕ) : ℝ) + (s n : ℝ) ^ 2 + (l n : ℝ) + (s n : ℝ) := by
        have h2 : ((n : ℕ) : ℝ) ≤ ((k n * l n + s n * s n + l n + s n : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at h2 ⊢
        nlinarith [h2]
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      calc 1 - (s n : ℝ) ^ 2 / (n : ℝ) - (l n : ℝ) / (n : ℝ) - (s n : ℝ) / (n : ℝ)
          = ((n : ℝ) - (s n : ℝ) ^ 2 - (l n : ℝ) - (s n : ℝ)) / (n : ℝ) := by field_simp
        _ ≤ ((k n * l n : ℕ) : ℝ) / (n : ℝ) := by gcongr; linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 : k n * l n ≤ n :=
        le_trans (Nat.mul_le_mul_left (k n) (Nat.le_add_right (l n) (s n))) (hfit n)
      rw [div_le_one hn0]
      exact_mod_cast h1
  -- `k_n α(s_n) → 0`
  have hkα : Tendsto (fun n : ℕ => (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
    have hnn : ∀ m : ℕ, 0 ≤ alphaCoeff X μ m := fun _ => alphaMixCoeff_nonneg
    refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg _) (hnn _)) (fun n => ?_)
      ((tendsto_mul_alphaCoeff hα).comp hstopN)
    have : (k n : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hks n
    exact mul_le_mul_of_nonneg_right this (hnn _)
  exact ⟨l, s, k, hs1, hl1, hfit, hltop, hln0, hkl, hkα⟩

/-- **The Bernstein block scheme, parametrised by the small block.**  Given any small-block
length `s_n ≥ 1` with `s_n → ∞` and `s_n²/n → 0`, the big blocks `l_n = ⌊n/s_n⌋ + 1` and the
count `k_n = ⌊n/(l_n + s_n)⌋` satisfy every constraint the Bernstein argument uses.  The
choice `l_n s_n > n` forces `k_n ≤ s_n`, which is what turns `m α(m) → 0` into the
Volkonskii–Rozanov budget `k_n α(s_n) → 0`. -/
private lemma exists_block_scheme_of_small [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hα : Summable fun n : ℕ => alphaCoeff X μ n)
    (s : ℕ → ℕ) (hs1 : ∀ n, 1 ≤ s n) (hstopN : Tendsto s atTop atTop)
    (hsqn : Tendsto (fun n : ℕ => (s n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0)) :
    ∃ l k : ℕ → ℕ,
      (∀ n, l n = n / s n + 1) ∧ (∀ n, k n = n / (l n + s n)) ∧
      (∀ n, 1 ≤ l n) ∧ (∀ n, k n * (l n + s n) ≤ n) ∧
      Tendsto (fun n : ℕ => (l n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
  classical
  obtain ⟨l, hldef⟩ : ∃ l : ℕ → ℕ, ∀ n, l n = n / s n + 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ → ℕ, ∀ n, k n = n / (l n + s n) := ⟨_, fun _ => rfl⟩
  have hl1 : ∀ n, 1 ≤ l n := fun n => by rw [hldef]; exact Nat.le_add_left 1 _
  have hfit : ∀ n, k n * (l n + s n) ≤ n := fun n => by rw [hkdef]; exact Nat.div_mul_le_self _ _
  have hsl : ∀ n, n < s n * l n := by
    intro n
    have h1 := Nat.div_add_mod n (s n)
    have h2 : n % s n < s n := Nat.mod_lt _ (hs1 n)
    have h3 : s n * l n = s n * (n / s n) + s n := by rw [hldef]; ring
    omega
  have hks : ∀ n, k n ≤ s n := by
    intro n
    by_contra hcon
    rw [not_le] at hcon
    have h1 : k n * l n ≤ n :=
      le_trans (Nat.mul_le_mul_left (k n) (Nat.le_add_right (l n) (s n))) (hfit n)
    have h2 : (s n + 1) * l n ≤ k n * l n := Nat.mul_le_mul_right _ hcon
    have h3 : (s n + 1) * l n = s n * l n + l n := by ring
    have h4 := hsl n
    have h5 := hl1 n
    omega
  have hinvs : Tendsto (fun n : ℕ => (1 : ℝ) / (s n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hstopN
  have hinvn : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  -- `l_n / n → 0`
  have hln0 : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_
      (by simpa only [add_zero] using hinvs.add hinvn)
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hs1 n
    have hdiv : ((n / s n : ℕ) : ℝ) ≤ (n : ℝ) / (s n : ℝ) := Nat.cast_div_le
    have hlc : (l n : ℝ) ≤ (n : ℝ) / (s n : ℝ) + 1 := by
      rw [hldef]; push_cast; linarith
    calc (l n : ℝ) / (n : ℝ) ≤ ((n : ℝ) / (s n : ℝ) + 1) / (n : ℝ) := by gcongr
      _ = 1 / (s n : ℝ) + 1 / (n : ℝ) := by field_simp
  -- `n / s_n² → ∞`, hence `l_n → ∞`
  have hnsq : Tendsto (fun n : ℕ => (n : ℝ) / (s n : ℝ) ^ 2) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    by_cases hb : 0 < b
    swap
    · rw [not_lt] at hb
      filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) ≤ (n : ℝ) / (s n : ℝ) ^ 2 := by positivity
      linarith
    · filter_upwards [hsqn.eventually_le_const (show (0 : ℝ) < 1 / b by positivity),
        eventually_ge_atTop 1] with n hle hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hs0 : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hs1 n
      have hs2 : (0 : ℝ) < (s n : ℝ) ^ 2 := by positivity
      rw [le_div_iff₀ hs2]
      rw [div_le_div_iff₀ hn0 hb] at hle
      linarith
  have hltop : Tendsto (fun n : ℕ => (l n : ℝ)) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ hnsq
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < (s n : ℝ) := by exact_mod_cast hs1 n
    have hs1' : (1 : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hs1 n
    have hnl : (n : ℝ) < (s n : ℝ) * (l n : ℝ) := by exact_mod_cast hsl n
    have hstep : (n : ℝ) / (s n : ℝ) ^ 2 ≤ (n : ℝ) / (s n : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hs0]
      nlinarith [mul_nonneg (mul_nonneg hn0.le hs0.le) (sub_nonneg.2 hs1')]
    refine hstep.trans ?_
    rw [div_le_iff₀ hs0]
    nlinarith
  -- `s_n / n → 0`
  have hsn0 : Tendsto (fun n : ℕ => (s n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hsqn
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs1' : (1 : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hs1 n
    gcongr
    nlinarith
  -- `k_n l_n / n → 1`
  have hkl : Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => 1 - (s n : ℝ) ^ 2 / (n : ℝ) - (l n : ℝ) / (n : ℝ)
        - (s n : ℝ) / (n : ℝ)) atTop (𝓝 1) := by
      simpa using ((tendsto_const_nhds.sub hsqn).sub hln0).sub hsn0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hkq : (l n + s n) * k n + n % (l n + s n) = n := by
        rw [hkdef]; exact Nat.div_add_mod n (l n + s n)
      have hmlt : n % (l n + s n) < l n + s n := Nat.mod_lt _ (by have := hl1 n; omega)
      have hexp : (l n + s n) * k n = k n * l n + k n * s n := by ring
      have hks' : k n * s n ≤ s n * s n := Nat.mul_le_mul_right _ (hks n)
      have hnat : n ≤ k n * l n + s n * s n + l n + s n := by omega
      have hcast : (n : ℝ) ≤ ((k n * l n : ℕ) : ℝ) + (s n : ℝ) ^ 2 + (l n : ℝ) + (s n : ℝ) := by
        have h2 : ((n : ℕ) : ℝ) ≤ ((k n * l n + s n * s n + l n + s n : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at h2 ⊢
        nlinarith [h2]
      have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
      calc 1 - (s n : ℝ) ^ 2 / (n : ℝ) - (l n : ℝ) / (n : ℝ) - (s n : ℝ) / (n : ℝ)
          = ((n : ℝ) - (s n : ℝ) ^ 2 - (l n : ℝ) - (s n : ℝ)) / (n : ℝ) := by field_simp
        _ ≤ ((k n * l n : ℕ) : ℝ) / (n : ℝ) := by gcongr; linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have h1 : k n * l n ≤ n :=
        le_trans (Nat.mul_le_mul_left (k n) (Nat.le_add_right (l n) (s n))) (hfit n)
      rw [div_le_one hn0]
      exact_mod_cast h1
  -- `k_n α(s_n) → 0`
  have hkα : Tendsto (fun n : ℕ => (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
    have hnn : ∀ m : ℕ, 0 ≤ alphaCoeff X μ m := fun _ => alphaMixCoeff_nonneg
    refine squeeze_zero (fun n => mul_nonneg (Nat.cast_nonneg _) (hnn _)) (fun n => ?_)
      ((tendsto_mul_alphaCoeff hα).comp hstopN)
    have : (k n : ℝ) ≤ (s n : ℝ) := by exact_mod_cast hks n
    exact mul_le_mul_of_nonneg_right this (hnn _)
  exact ⟨l, k, hldef, hkdef, hl1, hfit, hltop, hln0, hkl, hkα⟩

/-- **The adaptive small block.**  Given a nonnegative bounded `η_l → 0`, there is a
small-block length `s_n` admissible for the Bernstein scheme
(`s_n ≥ 1`, `s_n → ∞`, `s_n²/n → 0`) whose companion big block `l_n = ⌊n/s_n⌋ + 1`
satisfies `l_n² η(l_n) = o(n)`. -/
private lemma exists_adaptive_small {η : ℕ → ℝ} (hη0 : ∀ l, 0 ≤ η l) {B0 : ℝ}
    (hηB : ∀ l, η l ≤ B0) (hηlim : Tendsto η atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, (∀ n, 1 ≤ s n) ∧ Tendsto s atTop atTop ∧
      Tendsto (fun n : ℕ => (s n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((n / s n + 1 : ℕ) : ℝ) ^ 2 * η (n / s n + 1) / (n : ℝ))
        atTop (𝓝 0) := by
  classical
  have hB0 : 0 ≤ B0 := le_trans (hη0 0) (hηB 0)
  -- the antitone envelope of `η`
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℕ → ℝ, ∀ m, θ m = sSup (Set.range fun j : ℕ => η (j + m)) :=
    ⟨_, fun _ => rfl⟩
  have hbddA : ∀ m, BddAbove (Set.range fun j : ℕ => η (j + m)) := by
    intro m
    exact ⟨B0, by rintro x ⟨j, rfl⟩; exact hηB _⟩
  have hne : ∀ m, (Set.range fun j : ℕ => η (j + m)).Nonempty := fun m => ⟨η m, ⟨0, by simp⟩⟩
  have hθge : ∀ m l : ℕ, m ≤ l → η l ≤ θ m := by
    intro m l hml
    rw [hθdef]
    refine le_csSup (hbddA m) ⟨l - m, ?_⟩
    show η (l - m + m) = η l
    rw [Nat.sub_add_cancel hml]
  have hθ0 : ∀ m, 0 ≤ θ m := fun m => le_trans (hη0 m) (hθge m m le_rfl)
  have hθlim : Tendsto θ atTop (𝓝 0) := by
    refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hηlim.eventually_le_const (half_pos hε))
    filter_upwards [eventually_ge_atTop N] with m hm
    rw [Real.norm_eq_abs, abs_of_nonneg (hθ0 m)]
    have hle : θ m ≤ ε / 2 := by
      rw [hθdef]
      refine csSup_le (hne m) ?_
      rintro x ⟨j, rfl⟩
      exact hN _ (by omega)
    linarith
  -- the envelope evaluated at `⌊√n⌋/3`
  obtain ⟨d, hddef⟩ : ∃ d : ℕ → ℝ, ∀ n, d n = θ (Nat.sqrt n / 3) := ⟨_, fun _ => rfl⟩
  have hd0 : ∀ n, 0 ≤ d n := fun n => by rw [hddef]; exact hθ0 _
  have hsqrt3top : Tendsto (fun n : ℕ => Nat.sqrt n / 3) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨(3 * b + 3) * (3 * b + 3), fun a ha => ?_⟩
    have h1 : 3 * b + 3 ≤ Nat.sqrt a := by
      calc 3 * b + 3 = Nat.sqrt ((3 * b + 3) * (3 * b + 3)) := (Nat.sqrt_eq _).symm
        _ ≤ Nat.sqrt a := Nat.sqrt_le_sqrt ha
    omega
  have hdlim : Tendsto d atTop (𝓝 0) := by
    have := hθlim.comp hsqrt3top
    refine this.congr fun n => ?_
    rw [hddef]
    rfl
  -- a strictly positive perturbation, its reciprocal, and the fourth root
  obtain ⟨e, hedef⟩ : ∃ e : ℕ → ℝ, ∀ n, e n = d n + 1 / ((n : ℝ) + 1) := ⟨_, fun _ => rfl⟩
  have he0 : ∀ n, 0 < e n := by
    intro n
    rw [hedef]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hd0 n]
  have helim : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := hdlim.add h1
    rw [add_zero] at this
    exact this.congr fun n => (hedef n).symm
  have hinv : Tendsto (fun n : ℕ => 1 / e n) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    by_cases hb : 0 < b
    swap
    · rw [not_lt] at hb
      filter_upwards with n
      have : (0 : ℝ) < 1 / e n := one_div_pos.2 (he0 n)
      linarith
    · filter_upwards [helim.eventually_le_const (show (0 : ℝ) < 1 / b by positivity)] with n hle
      rw [le_div_iff₀ (he0 n)]
      rw [le_div_iff₀ hb] at hle
      linarith
  obtain ⟨q, hqdef⟩ : ∃ q : ℕ → ℕ, ∀ n, q n = ⌊1 / e n⌋₊ := ⟨_, fun _ => rfl⟩
  have hqtop : Tendsto q atTop atTop := by
    have := tendsto_nat_floor_atTop (α := ℝ) |>.comp hinv
    exact this.congr fun n => (hqdef n).symm
  have hqd : ∀ n, (q n : ℝ) * d n ≤ 1 := by
    intro n
    have h1 : (q n : ℝ) ≤ 1 / e n := by
      rw [hqdef]; exact Nat.floor_le (one_div_pos.2 (he0 n)).le
    have h2 : d n ≤ e n := by rw [hedef]; nlinarith [(show (0:ℝ) < 1/((n:ℝ)+1) by positivity)]
    calc (q n : ℝ) * d n ≤ (1 / e n) * d n := mul_le_mul_of_nonneg_right h1 (hd0 n)
      _ ≤ (1 / e n) * e n := mul_le_mul_of_nonneg_left h2 (one_div_pos.2 (he0 n)).le
      _ = 1 := one_div_mul_cancel (ne_of_gt (he0 n))
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ → ℕ, ∀ n, c n = Nat.sqrt (Nat.sqrt (q n)) := ⟨_, fun _ => rfl⟩
  have hc4 : ∀ n, c n ^ 4 ≤ q n := by
    intro n
    have h1 : c n * c n ≤ Nat.sqrt (q n) := by rw [hcdef]; exact Nat.sqrt_le _
    have h2 : Nat.sqrt (q n) * Nat.sqrt (q n) ≤ q n := Nat.sqrt_le _
    calc c n ^ 4 = (c n * c n) * (c n * c n) := by ring
      _ ≤ Nat.sqrt (q n) * Nat.sqrt (q n) := Nat.mul_le_mul h1 h1
      _ ≤ q n := h2
  have hctop : Tendsto c atTop atTop := by
    have : Tendsto (fun m : ℕ => Nat.sqrt (Nat.sqrt m)) atTop atTop := by
      have hs : Tendsto Nat.sqrt atTop atTop :=
        tendsto_atTop_atTop.2 fun b => ⟨b * b, fun a ha => by
          calc b = Nat.sqrt (b * b) := (Nat.sqrt_eq b).symm
            _ ≤ Nat.sqrt a := Nat.sqrt_le_sqrt ha⟩
      exact hs.comp hs
    exact (this.comp hqtop).congr fun n => (hcdef n).symm
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → ℕ, ∀ n, a n = c n + 1 := ⟨_, fun _ => rfl⟩
  have ha1 : ∀ n, 1 ≤ a n := fun n => by rw [hadef]; omega
  have hatop : Tendsto (fun n : ℕ => (a n : ℝ)) atTop atTop := by
    refine tendsto_natCast_atTop_atTop.comp ?_
    exact tendsto_atTop_mono (fun n => by rw [hadef]; omega) hctop
  -- the key budget `a_n² d_n → 0`
  have hbudget : Tendsto (fun n : ℕ => (a n : ℝ) ^ 2 * d n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 4 / (c n : ℝ) ^ 2) atTop (𝓝 0) := by
      have hcR : Tendsto (fun n : ℕ => (c n : ℝ) ^ 2) atTop atTop :=
        (tendsto_pow_atTop (n := 2) (by norm_num)).comp
          (tendsto_natCast_atTop_atTop.comp hctop)
      exact hcR.const_div_atTop 4
    refine squeeze_zero' (Eventually.of_forall fun n =>
      mul_nonneg (by positivity) (hd0 n)) ?_ hlim
    filter_upwards [hctop.eventually_ge_atTop 1] with n hcn
    have hc0 : (0 : ℝ) < (c n : ℝ) := by exact_mod_cast hcn
    have hcd : (c n : ℝ) ^ 4 * d n ≤ 1 := by
      have h1 : ((c n ^ 4 : ℕ) : ℝ) ≤ ((q n : ℕ) : ℝ) := by exact_mod_cast hc4 n
      push_cast at h1
      calc (c n : ℝ) ^ 4 * d n ≤ (q n : ℝ) * d n := mul_le_mul_of_nonneg_right h1 (hd0 n)
        _ ≤ 1 := hqd n
    have haR : (a n : ℝ) = (c n : ℝ) + 1 := by rw [hadef]; push_cast; ring
    have hc1 : (1 : ℝ) ≤ (c n : ℝ) := by exact_mod_cast hcn
    have hle : (a n : ℝ) ^ 2 ≤ 4 * (c n : ℝ) ^ 2 := by
      rw [haR]; nlinarith [hc1]
    calc (a n : ℝ) ^ 2 * d n ≤ (4 * (c n : ℝ) ^ 2) * d n :=
          mul_le_mul_of_nonneg_right hle (hd0 n)
      _ ≤ 4 / (c n : ℝ) ^ 2 := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < (c n : ℝ) ^ 2)]
          nlinarith [hcd]
  -- the small block
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℕ, ∀ n,
      s n = Nat.sqrt n / a n + Nat.sqrt (Nat.sqrt (Nat.sqrt n)) + 1 := ⟨_, fun _ => rfl⟩
  have hs1 : ∀ n, 1 ≤ s n := fun n => by rw [hsdef]; exact Nat.le_add_left 1 _
  have hsqrttop : Tendsto Nat.sqrt atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * b, fun a ha => by
      calc b = Nat.sqrt (b * b) := (Nat.sqrt_eq b).symm
        _ ≤ Nat.sqrt a := Nat.sqrt_le_sqrt ha⟩
  have hsqrtdiv : Tendsto (fun n : ℕ => (Nat.sqrt n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (Nat.sqrt n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp hsqrttop
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hone
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
    have hsq : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le n
    have hs0 : (0 : ℝ) < (Nat.sqrt n : ℝ) := by exact_mod_cast hs
    rw [div_le_div_iff₀ (by positivity) hs0]
    nlinarith
  have hstop : Tendsto s atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) ((hsqrttop.comp hsqrttop).comp hsqrttop)
    simp only [Function.comp_apply]
    rw [hsdef]
    exact Nat.le_succ_of_le (Nat.le_add_left _ _)
  -- `s_n² / n → 0`
  have hsq : Tendsto (fun n : ℕ => (s n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 3 / (a n : ℝ) ^ 2
        + 3 * ((Nat.sqrt n : ℝ) / (n : ℝ)) + 3 * (1 / (n : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 3 / (a n : ℝ) ^ 2) atTop (𝓝 0) :=
        ((tendsto_pow_atTop (n := 2) (by norm_num)).comp hatop).const_div_atTop 3
      have h2 := hsqrtdiv.const_mul (3 : ℝ)
      have h3 := tendsto_one_div_atTop_nhds_zero_nat.const_mul (3 : ℝ)
      simpa using (h1.add h2).add h3
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have ha0 : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast ha1 n
    have hr1 : (Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le n
    have hr3 : (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ) * (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ)
        ≤ (Nat.sqrt n : ℝ) := by
      have h1 : Nat.sqrt (Nat.sqrt (Nat.sqrt n)) * Nat.sqrt (Nat.sqrt (Nat.sqrt n))
          ≤ Nat.sqrt (Nat.sqrt n) := Nat.sqrt_le _
      have h2 : Nat.sqrt (Nat.sqrt n) ≤ Nat.sqrt n := Nat.sqrt_le_self _
      have : Nat.sqrt (Nat.sqrt (Nat.sqrt n)) * Nat.sqrt (Nat.sqrt (Nat.sqrt n)) ≤ Nat.sqrt n :=
        le_trans h1 h2
      exact_mod_cast this
    have hdvd : ((Nat.sqrt n / a n : ℕ) : ℝ) ≤ (Nat.sqrt n : ℝ) / (a n : ℝ) := Nat.cast_div_le
    have hsc : (s n : ℝ) = ((Nat.sqrt n / a n : ℕ) : ℝ)
        + (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ) + 1 := by
      rw [hsdef]; push_cast; ring
    have hx0 : (0 : ℝ) ≤ ((Nat.sqrt n / a n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hy0 : (0 : ℝ) ≤ (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ) := Nat.cast_nonneg _
    have hxsq : ((Nat.sqrt n / a n : ℕ) : ℝ) ^ 2 * (a n : ℝ) ^ 2 ≤ (n : ℝ) := by
      have h1 : ((Nat.sqrt n / a n : ℕ) : ℝ) * (a n : ℝ) ≤ (Nat.sqrt n : ℝ) :=
        (le_div_iff₀ ha0).1 hdvd
      have h2 := mul_self_le_mul_self (mul_nonneg hx0 ha0.le) h1
      nlinarith [h2, hr1]
    rw [div_le_iff₀ hn0, hsc]
    have hexp : (3 / (a n : ℝ) ^ 2 + 3 * ((Nat.sqrt n : ℝ) / (n : ℝ)) + 3 * (1 / (n : ℝ)))
        * (n : ℝ) = 3 * (n : ℝ) / (a n : ℝ) ^ 2 + 3 * (Nat.sqrt n : ℝ) + 3 := by
      field_simp
    rw [hexp]
    have hxb : ((Nat.sqrt n / a n : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) / (a n : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      exact hxsq
    have hY2 : (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ) ^ 2 ≤ (Nat.sqrt n : ℝ) := by
      nlinarith [hr3]
    have hcomb : (((Nat.sqrt n / a n : ℕ) : ℝ) + (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ) + 1) ^ 2
        ≤ 3 * ((Nat.sqrt n / a n : ℕ) : ℝ) ^ 2
          + 3 * (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ) ^ 2 + 3 := by
      nlinarith [sq_nonneg (((Nat.sqrt n / a n : ℕ) : ℝ)
          - (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ)),
        sq_nonneg (((Nat.sqrt n / a n : ℕ) : ℝ) - 1),
        sq_nonneg ((Nat.sqrt (Nat.sqrt (Nat.sqrt n)) : ℝ) - 1)]
    have hd1 : 3 * ((Nat.sqrt n / a n : ℕ) : ℝ) ^ 2 ≤ 3 * ((n : ℝ) / (a n : ℝ) ^ 2) := by
      linarith
    have hd2 : 3 * ((n : ℝ) / (a n : ℝ) ^ 2) = 3 * (n : ℝ) / (a n : ℝ) ^ 2 := by ring
    linarith
  -- the cubic budget for the companion big block
  refine ⟨s, hs1, hstop, hsq, ?_⟩
  have hlim : Tendsto (fun n : ℕ => 8 * (a n : ℝ) ^ 2 * d n + 2 * (d n * (1 / (n : ℝ))))
      atTop (𝓝 0) := by
    have h1 := hbudget.const_mul (8 : ℝ)
    have h2 := (hdlim.mul tendsto_one_div_atTop_nhds_zero_nat).const_mul (2 : ℝ)
    have := h1.add h2
    simpa [mul_assoc] using this
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hlim
  · exact div_nonneg (mul_nonneg (by positivity) (hη0 _)) (Nat.cast_nonneg _)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr1n : 1 ≤ Nat.sqrt n := Nat.sqrt_pos.mpr hn
  -- (F1) `s_n ≤ 3 ⌊√n⌋`
  have hF1 : s n ≤ 3 * Nat.sqrt n := by
    have h1 : Nat.sqrt n / a n ≤ Nat.sqrt n := Nat.div_le_self _ _
    have h2 : Nat.sqrt (Nat.sqrt (Nat.sqrt n)) ≤ Nat.sqrt n :=
      le_trans (Nat.sqrt_le_self _) (Nat.sqrt_le_self _)
    rw [hsdef]
    omega
  -- (F2) `⌊√n⌋/3 ≤ l_n`
  have hF2 : Nat.sqrt n / 3 ≤ n / s n + 1 := by
    have h0 : 0 < 3 * Nat.sqrt n := by omega
    have h1 : n / (3 * Nat.sqrt n) ≤ n / s n := Nat.div_le_div_left hF1 (hs1 n)
    have h2 : Nat.sqrt n / 3 ≤ n / (3 * Nat.sqrt n) := by
      rw [Nat.le_div_iff_mul_le h0]
      have h3 : Nat.sqrt n / 3 * 3 ≤ Nat.sqrt n := Nat.div_mul_le_self _ _
      have h4 : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
      calc Nat.sqrt n / 3 * (3 * Nat.sqrt n) = (Nat.sqrt n / 3 * 3) * Nat.sqrt n := by ring
        _ ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_right _ h3
        _ ≤ n := h4
    omega
  -- (F3) `(n/s_n) ⌊√n⌋ ≤ n a_n`
  have hF3 : (n / s n) * Nat.sqrt n ≤ n * a n := by
    have hsa : Nat.sqrt n < s n * a n := by
      have h1 := Nat.div_add_mod (Nat.sqrt n) (a n)
      have h2 : Nat.sqrt n % a n < a n := Nat.mod_lt _ (ha1 n)
      have h3 : s n * a n = (Nat.sqrt n / a n) * a n
          + (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) + 1) * a n := by rw [hsdef]; ring
      have h4 : a n ≤ (Nat.sqrt (Nat.sqrt (Nat.sqrt n)) + 1) * a n := Nat.le_mul_of_pos_left _ (by omega)
      nlinarith [h1, h2, h3, h4]
    calc (n / s n) * Nat.sqrt n ≤ (n / s n) * (s n * a n) :=
          Nat.mul_le_mul_left _ (le_of_lt hsa)
      _ = ((n / s n) * s n) * a n := by ring
      _ ≤ n * a n := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
  -- (F4) `n ≤ 4 ⌊√n⌋²`
  have hF4 : n ≤ 4 * (Nat.sqrt n * Nat.sqrt n) := by
    have h1 : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
    nlinarith [hr1n]
  -- assemble
  have hR0 : (0 : ℝ) < (Nat.sqrt n : ℝ) := by exact_mod_cast hr1n
  have hA1 : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
  have hηd : η (n / s n + 1) ≤ d n := by
    rw [hddef]
    exact hθge _ _ hF2
  have hL : ((n / s n + 1 : ℕ) : ℝ) ≤ (n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ) + 1 := by
    have h3 : ((n / s n : ℕ) : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) * (a n : ℝ) := by
      exact_mod_cast hF3
    have : ((n / s n : ℕ) : ℝ) ≤ (n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ) := by
      rw [le_div_iff₀ hR0]; exact h3
    push_cast
    linarith
  have hL0 : (0 : ℝ) ≤ ((n / s n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNR : (n : ℝ) ≤ 4 * ((Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ)) := by exact_mod_cast hF4
  have hLsq : ((n / s n + 1 : ℕ) : ℝ) ^ 2
      ≤ 2 * ((n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ)) ^ 2 + 2 := by
    have hb0 : (0 : ℝ) ≤ (n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ) := by positivity
    nlinarith [hL, hL0, hb0, sq_nonneg ((n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ) - 1)]
  rw [div_le_iff₀ hn0]
  have hstep : ((n / s n + 1 : ℕ) : ℝ) ^ 2 * η (n / s n + 1)
      ≤ (2 * ((n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ)) ^ 2 + 2) * d n := by
    have h1 : ((n / s n + 1 : ℕ) : ℝ) ^ 2 * η (n / s n + 1)
        ≤ ((n / s n + 1 : ℕ) : ℝ) ^ 2 * d n :=
      mul_le_mul_of_nonneg_left hηd (by positivity)
    have h2 : ((n / s n + 1 : ℕ) : ℝ) ^ 2 * d n
        ≤ (2 * ((n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ)) ^ 2 + 2) * d n :=
      mul_le_mul_of_nonneg_right hLsq (hd0 n)
    linarith
  refine hstep.trans ?_
  have hsqr : ((n : ℝ) * (a n : ℝ) / (Nat.sqrt n : ℝ)) ^ 2
      = (n : ℝ) ^ 2 * (a n : ℝ) ^ 2 / ((Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ)) := by
    field_simp
  rw [hsqr]
  have hkey : (n : ℝ) ^ 2 * (a n : ℝ) ^ 2 / ((Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ))
      ≤ 4 * ((n : ℝ) * (a n : ℝ) ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hNR, sq_nonneg ((a n : ℝ)), hn0.le, mul_nonneg hn0.le (sq_nonneg ((a n : ℝ)))]
  have hd0n := hd0 n
  have hfin : (2 * ((n : ℝ) ^ 2 * (a n : ℝ) ^ 2
        / ((Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ))) + 2) * d n
      ≤ (8 * (a n : ℝ) ^ 2 * d n + 2 * (d n * (1 / (n : ℝ)))) * (n : ℝ) := by
    have h1 : 2 * ((n : ℝ) ^ 2 * (a n : ℝ) ^ 2 / ((Nat.sqrt n : ℝ) * (Nat.sqrt n : ℝ)))
        ≤ 8 * ((n : ℝ) * (a n : ℝ) ^ 2) := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hd0n
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have h3 : (8 * (a n : ℝ) ^ 2 * d n + 2 * (d n * (1 / (n : ℝ)))) * (n : ℝ)
        = 8 * ((n : ℝ) * (a n : ℝ) ^ 2) * d n + 2 * d n := by
      field_simp
    rw [h3]
    linarith
  exact hfin

/-! #### Window laws, phase increments, and the Lindeberg input -/

/-- `‖e^{ix} − 1‖ ≤ |x| + 5x²` — the crude phase-increment bound, read off the
third-order Taylor brick (no trigonometric identities needed). -/
private lemma norm_expI_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| + 5 * x ^ 2 := by
  have hT := (norm_expI_taylor x).2
  have hx : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  have hx2 : ‖(x : ℂ) ^ 2 / 2‖ = x ^ 2 / 2 := by
    rw [norm_div, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, abs_of_nonneg (sq_nonneg x)]
  have hsplit : Complex.exp ((x : ℂ) * Complex.I) - 1
      = (Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2))
        + ((x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖(x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2‖ ≤ |x| + x ^ 2 / 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [hx, hx2]
  nlinarith [hT, h2, sq_nonneg x]

/-- The phase `e^{i v B}` is integrable (unit modulus). -/
private lemma integrable_expI_block [IsProbabilityMeasure μ] {B : Ω → ℝ}
    (hB : Measurable B) (v : ℝ) :
    Integrable (fun ω => Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)) μ := by
  have hmf : Measurable fun ω => Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (measurable_const.mul hB)).mul measurable_const)
  refine MemLp.integrable (q := ⊤) le_top (memLp_top_of_bound hmf.aestronglyMeasurable 1 ?_)
  filter_upwards with ω
  rw [Complex.norm_exp_ofReal_mul_I]

/-- Integrability of the third-order Taylor remainder of `e^{i v B}`. -/
private lemma integrable_expI_remainder [IsProbabilityMeasure μ] {B : Ω → ℝ}
    (hB : Measurable B) (hBmem : MemLp B 2 μ) (v : ℝ) :
    Integrable (fun ω => Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
      - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) μ := by
  have hBi : Integrable B μ := hBmem.integrable one_le_two
  have hB2 : Integrable (fun ω => B ω ^ 2) μ := hBmem.integrable_sq
  have ha : Integrable (fun _ : Ω => (1 : ℂ)) μ := integrable_const _
  have hb : Integrable (fun ω => ((v * B ω : ℝ) : ℂ) * Complex.I) μ :=
    ((hBi.const_mul v).ofReal).mul_const _
  have hc : Integrable (fun ω => ((v * B ω : ℝ) : ℂ) ^ 2 / 2) μ := by
    have h0 : Integrable (fun ω => (((v ^ 2 * B ω ^ 2 : ℝ)) : ℂ)) μ :=
      ((hB2.const_mul (v ^ 2)).ofReal)
    refine (h0.div_const 2).congr (Eventually.of_forall fun ω => ?_)
    push_cast
    ring
  exact (integrable_expI_block hB v).sub ((ha.add hb).sub hc)

/-- **Block expansion.** For a zero-mean square-integrable `B`,
`E e^{i v B} − 1 = −(v²/2) E B² + R` with `R` the integrated Taylor remainder. -/
private lemma charFun_block_expand [IsProbabilityMeasure μ] {B : Ω → ℝ}
    (hB : Measurable B) (hBmem : MemLp B 2 μ) (hB1 : ∫ ω, B ω ∂μ = 0) (v : ℝ) :
    (∫ ω, Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I) ∂μ) - 1
      = -((v ^ 2 / 2 * ∫ ω, B ω ^ 2 ∂μ : ℝ) : ℂ)
        + ∫ ω, (Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
            - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) ∂μ := by
  have hBi : Integrable B μ := hBmem.integrable one_le_two
  have hB2 : Integrable (fun ω => B ω ^ 2) μ := hBmem.integrable_sq
  have ha : Integrable (fun _ : Ω => (1 : ℂ)) μ := integrable_const _
  have hb : Integrable (fun ω => ((v * B ω : ℝ) : ℂ) * Complex.I) μ :=
    ((hBi.const_mul v).ofReal).mul_const _
  have hc : Integrable (fun ω => ((v * B ω : ℝ) : ℂ) ^ 2 / 2) μ := by
    have h0 : Integrable (fun ω => (((v ^ 2 * B ω ^ 2 : ℝ)) : ℂ)) μ :=
      ((hB2.const_mul (v ^ 2)).ofReal)
    refine (h0.div_const 2).congr (Eventually.of_forall fun ω => ?_)
    push_cast
    ring
  have hab : Integrable (fun ω => (1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I) μ := ha.add hb
  have habc : Integrable (fun ω => (1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I
      - ((v * B ω : ℝ) : ℂ) ^ 2 / 2) μ := hab.sub hc
  have hpoly : ∫ ω, ((1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I
      - ((v * B ω : ℝ) : ℂ) ^ 2 / 2) ∂μ = 1 - ((v ^ 2 / 2 * ∫ ω, B ω ^ 2 ∂μ : ℝ) : ℂ) := by
    have s1 : ∫ ω, ((1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I
        - ((v * B ω : ℝ) : ℂ) ^ 2 / 2) ∂μ
        = (∫ ω, ((1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I) ∂μ)
          - ∫ ω, ((v * B ω : ℝ) : ℂ) ^ 2 / 2 ∂μ := integral_sub hab hc
    have s2 : ∫ ω, ((1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I) ∂μ
        = (∫ _ : Ω, (1 : ℂ) ∂μ) + ∫ ω, ((v * B ω : ℝ) : ℂ) * Complex.I ∂μ := integral_add ha hb
    have e1 : ∫ _ : Ω, (1 : ℂ) ∂μ = 1 := by simp
    have e2 : ∫ ω, ((v * B ω : ℝ) : ℂ) * Complex.I ∂μ = 0 := by
      have h1 : ∫ ω, ((v * B ω : ℝ) : ℂ) * Complex.I ∂μ
          = (∫ ω, ((v * B ω : ℝ) : ℂ) ∂μ) * Complex.I :=
        integral_mul_const Complex.I (fun ω => ((v * B ω : ℝ) : ℂ))
      have h2 : ∫ ω, ((v * B ω : ℝ) : ℂ) ∂μ = ((∫ ω, v * B ω ∂μ : ℝ) : ℂ) :=
        integral_complex_ofReal
      have h3 : ∫ ω, v * B ω ∂μ = v * ∫ ω, B ω ∂μ := integral_const_mul v B
      rw [h1, h2, h3, hB1]
      simp
    have e3 : ∫ ω, ((v * B ω : ℝ) : ℂ) ^ 2 / 2 ∂μ = ((v ^ 2 / 2 * ∫ ω, B ω ^ 2 ∂μ : ℝ) : ℂ) := by
      have hcg : ∀ ω : Ω, ((v * B ω : ℝ) : ℂ) ^ 2 / 2 = (((v ^ 2 / 2 * B ω ^ 2 : ℝ)) : ℂ) := by
        intro ω; push_cast; ring
      simp_rw [hcg]
      rw [integral_complex_ofReal, integral_const_mul]
    rw [s1, s2, e1, e2, e3]
    ring
  have s0 : ∫ ω, (Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
      - ((1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) ∂μ
      = (∫ ω, Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I) ∂μ)
        - ∫ ω, ((1 : ℂ) + ((v * B ω : ℝ) : ℂ) * Complex.I
            - ((v * B ω : ℝ) : ℂ) ^ 2 / 2) ∂μ :=
    integral_sub (integrable_expI_block hB v) habc
  rw [s0, hpoly]
  ring

/-- **Lindeberg split of the remainder.** -/
private lemma norm_integral_remainder_le [IsProbabilityMeasure μ] {B : Ω → ℝ}
    (hB : Measurable B) (hBmem : MemLp B 2 μ) (v : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ ω, (Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
        - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) ∂μ‖
      ≤ 4 * |v| ^ 3 * T * (∫ ω, B ω ^ 2 ∂μ)
        + 4 * v ^ 2 * ∫ ω in {ω | T ≤ |B ω|}, B ω ^ 2 ∂μ := by
  classical
  set g : Ω → ℝ := fun ω => ‖Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
      - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)‖ with hgdef
  have hrem : Integrable (fun ω => Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
      - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) μ :=
    integrable_expI_remainder hB hBmem v
  have hg : Integrable g μ := hrem.norm
  have hB2 : Integrable (fun ω => B ω ^ 2) μ := hBmem.integrable_sq
  set S : Set Ω := {ω | T ≤ |B ω|} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const hB.abs
  have hsplit : ∫ ω, g ω ∂μ = (∫ ω in S, g ω ∂μ) + ∫ ω in Sᶜ, g ω ∂μ :=
    (integral_add_compl hSm hg).symm
  -- on `S`: quadratic bound
  have hS1 : ∫ ω in S, g ω ∂μ ≤ 4 * v ^ 2 * ∫ ω in S, B ω ^ 2 ∂μ := by
    have hmono : ∫ ω in S, g ω ∂μ ≤ ∫ ω in S, (4 * v ^ 2) * B ω ^ 2 ∂μ := by
      refine setIntegral_mono_on hg.integrableOn ((hB2.const_mul _).integrableOn) hSm ?_
      intro ω _
      have := (norm_expI_taylor (v * B ω)).2
      calc g ω ≤ 4 * (v * B ω) ^ 2 := this
        _ = 4 * v ^ 2 * B ω ^ 2 := by ring
    rw [integral_const_mul] at hmono
    exact hmono
  -- on `Sᶜ`: cubic bound
  have hS2 : ∫ ω in Sᶜ, g ω ∂μ ≤ 4 * |v| ^ 3 * T * ∫ ω, B ω ^ 2 ∂μ := by
    have hmono : ∫ ω in Sᶜ, g ω ∂μ ≤ ∫ ω in Sᶜ, (4 * |v| ^ 3 * T) * B ω ^ 2 ∂μ := by
      refine setIntegral_mono_on hg.integrableOn ((hB2.const_mul _).integrableOn) hSm.compl ?_
      intro ω hω
      have hlt : |B ω| < T := by
        simp only [hSdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
        exact hω
      have h1 := (norm_expI_taylor (v * B ω)).1
      have habs : |v * B ω| ^ 3 = |v| ^ 3 * |B ω| ^ 3 := by
        rw [abs_mul, mul_pow]
      have h3 : |B ω| ^ 3 ≤ T * B ω ^ 2 := by
        have : |B ω| ^ 3 = |B ω| * B ω ^ 2 := by
          rw [← sq_abs (B ω)]; ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hlt.le (sq_nonneg _)
      calc g ω ≤ 4 * |v * B ω| ^ 3 := h1
        _ = 4 * |v| ^ 3 * |B ω| ^ 3 := by rw [habs]; ring
        _ ≤ 4 * |v| ^ 3 * (T * B ω ^ 2) := by
            have : (0:ℝ) ≤ 4 * |v| ^ 3 := by positivity
            exact mul_le_mul_of_nonneg_left h3 this
        _ = 4 * |v| ^ 3 * T * B ω ^ 2 := by ring
    rw [integral_const_mul] at hmono
    refine hmono.trans ?_
    have hle : ∫ ω in Sᶜ, B ω ^ 2 ∂μ ≤ ∫ ω, B ω ^ 2 ∂μ :=
      setIntegral_le_integral hB2 (Eventually.of_forall fun ω => sq_nonneg _)
    have hcnn : (0:ℝ) ≤ 4 * |v| ^ 3 * T := by positivity
    exact mul_le_mul_of_nonneg_left hle hcnn
  calc ‖∫ ω, (Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
        - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) ∂μ‖
      ≤ ∫ ω, g ω ∂μ := norm_integral_le_integral_norm _
    _ = (∫ ω in S, g ω ∂μ) + ∫ ω in Sᶜ, g ω ∂μ := hsplit
    _ ≤ 4 * |v| ^ 3 * T * (∫ ω, B ω ^ 2 ∂μ) + 4 * v ^ 2 * ∫ ω in S, B ω ^ 2 ∂μ := by
        linarith

/-- Cauchy–Schwarz for the Bochner integral, discriminant form. -/
private lemma sq_integral_mul_le [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, f ω * g ω ∂μ) ^ 2 ≤ (∫ ω, f ω ^ 2 ∂μ) * ∫ ω, g ω ^ 2 ∂μ := by
  have hf2 : Integrable (fun ω => f ω ^ 2) μ := hf.integrable_sq
  have hg2 : Integrable (fun ω => g ω ^ 2) μ := hg.integrable_sq
  have hfg : Integrable (fun ω => f ω * g ω) μ := by
    have := MemLp.integrable_mul (p := 2) (q := 2) hf hg
    simpa using! this
  set A : ℝ := ∫ ω, f ω ^ 2 ∂μ with hA
  set Bq : ℝ := ∫ ω, g ω ^ 2 ∂μ with hBq
  set Cc : ℝ := ∫ ω, f ω * g ω ∂μ with hCc
  have hA0 : 0 ≤ A := integral_nonneg fun ω => sq_nonneg _
  have hB0 : 0 ≤ Bq := integral_nonneg fun ω => sq_nonneg _
  have hkey : ∀ t : ℝ, 0 ≤ A - 2 * t * Cc + t ^ 2 * Bq := by
    intro t
    have hi1 : Integrable (fun ω => f ω ^ 2 - 2 * t * (f ω * g ω)) μ :=
      hf2.sub (hfg.const_mul (2 * t))
    have hi2 : Integrable (fun ω => t ^ 2 * g ω ^ 2) μ := hg2.const_mul (t ^ 2)
    have hnn : 0 ≤ ∫ ω, (f ω - t * g ω) ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
    have e1 : (∫ ω, (f ω ^ 2 - 2 * t * (f ω * g ω) + t ^ 2 * g ω ^ 2) ∂μ)
        = (∫ ω, (f ω ^ 2 - 2 * t * (f ω * g ω)) ∂μ) + ∫ ω, t ^ 2 * g ω ^ 2 ∂μ :=
      integral_add hi1 hi2
    have e2 : (∫ ω, (f ω ^ 2 - 2 * t * (f ω * g ω)) ∂μ)
        = (∫ ω, f ω ^ 2 ∂μ) - ∫ ω, 2 * t * (f ω * g ω) ∂μ :=
      integral_sub hf2 (hfg.const_mul (2 * t))
    have e3 : (∫ ω, 2 * t * (f ω * g ω) ∂μ) = 2 * t * Cc := integral_const_mul _ _
    have e4 : (∫ ω, t ^ 2 * g ω ^ 2 ∂μ) = t ^ 2 * Bq := integral_const_mul _ _
    have heq : ∫ ω, (f ω - t * g ω) ^ 2 ∂μ = A - 2 * t * Cc + t ^ 2 * Bq := by
      rw [integral_congr_ae (Eventually.of_forall
        (fun ω => by ring : ∀ ω, (f ω - t * g ω) ^ 2
          = f ω ^ 2 - 2 * t * (f ω * g ω) + t ^ 2 * g ω ^ 2)), e1, e2, e3, e4, ← hA]
    rwa [heq] at hnn
  rcases eq_or_lt_of_le hB0 with hB | hB
  · have hgz : (fun ω => g ω ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (g ω)) hg2).1 hB.symm
    have hC0 : Cc = 0 := by
      rw [hCc]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hgz] with ω hω
      have : g ω = 0 := by
        have h2 : g ω ^ 2 = 0 := hω
        nlinarith [sq_nonneg (g ω), h2]
      simp [this]
    rw [hC0, ← hB]
    simp
  · have h := hkey (Cc / Bq)
    have hBne : Bq ≠ 0 := ne_of_gt hB
    have hrw : A - 2 * (Cc / Bq) * Cc + (Cc / Bq) ^ 2 * Bq = A - Cc ^ 2 / Bq := by
      field_simp
      ring
    rw [hrw, sub_nonneg, div_le_iff₀ hB] at h
    linarith

/-- Boundedness gives membership in every `L^q`. -/
private lemma memLp_of_abs_bdd [IsProbabilityMeasure μ] {h : Ω → ℝ} (hh : Measurable h)
    {M : ℝ} (hbd : ∀ᵐ ω ∂μ, |h ω| ≤ M) (q : ℝ≥0∞) : MemLp h q μ := by
  refine MemLp.mono_exponent ?_ le_top
  refine memLp_top_of_bound hh.aestronglyMeasurable M ?_
  filter_upwards [hbd] with ω hω
  simpa [Real.norm_eq_abs] using hω

/-- **The cubic (Lindeberg-free) remainder bound.**  The global cubic half of
`norm_expI_taylor` bounds the third-order Taylor remainder of `E e^{i v B}` by
`4 |v|³ E|B|³`, and Cauchy–Schwarz turns `E|B|³ = E(|B| · B²)` into
`√(E B² · E B⁴)`.  This is the estimate that replaces the Lindeberg split
`norm_integral_remainder_le` in the cubic/adaptive route: no truncation level appears,
so no uniform-integrability input is needed. -/
private lemma norm_integral_remainder_cubic_le [IsProbabilityMeasure μ] {B : Ω → ℝ}
    (hB : Measurable B) {K : ℝ} (hbd : ∀ᵐ ω ∂μ, |B ω| ≤ K) (v : ℝ) :
    ‖∫ ω, (Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
        - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) ∂μ‖
      ≤ 4 * |v| ^ 3 * Real.sqrt ((∫ ω, B ω ^ 2 ∂μ) * ∫ ω, B ω ^ 4 ∂μ) := by
  classical
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) hbd.exists.choose_spec
  have hBmem : ∀ q : ℝ≥0∞, MemLp B q μ := memLp_of_abs_bdd hB hbd
  have hBi : Integrable B μ := (hBmem 1).integrable le_rfl
  have hB2 : Integrable (fun ω => B ω ^ 2) μ := (hBmem 2).integrable_sq
  -- integrability of the Taylor remainder
  have hexpi : Integrable (fun ω => Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)) μ := by
    have hmf : Measurable fun ω => Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul hB)).mul measurable_const)
    refine MemLp.integrable (q := ⊤) le_top (memLp_top_of_bound hmf.aestronglyMeasurable 1 ?_)
    filter_upwards with ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have ha : Integrable (fun _ : Ω => (1 : ℂ)) μ := integrable_const _
  have hb : Integrable (fun ω => ((v * B ω : ℝ) : ℂ) * Complex.I) μ :=
    ((hBi.const_mul v).ofReal).mul_const _
  have hc : Integrable (fun ω => ((v * B ω : ℝ) : ℂ) ^ 2 / 2) μ := by
    have h0 : Integrable (fun ω => (((v ^ 2 * B ω ^ 2 : ℝ)) : ℂ)) μ :=
      ((hB2.const_mul (v ^ 2)).ofReal)
    refine (h0.div_const 2).congr (Eventually.of_forall fun ω => ?_)
    push_cast
    ring
  have hrem : Integrable (fun ω => Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
      - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) μ :=
    hexpi.sub ((ha.add hb).sub hc)
  -- the cubic pointwise bound
  have hcube : Integrable (fun ω => 4 * |v| ^ 3 * |B ω| ^ 3) μ := by
    refine Integrable.mono' (integrable_const (4 * |v| ^ 3 * K ^ 3))
      (((hB.abs.pow_const 3).const_mul _).aestronglyMeasurable) ?_
    filter_upwards [hbd] with ω hω
    have h1 : |B ω| ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hω 3
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (0 : ℝ) ≤ 4 * |v| ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_left h1 this
  have hpt : ∀ ω, ‖Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
      - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)‖
      ≤ 4 * |v| ^ 3 * |B ω| ^ 3 := by
    intro ω
    have h1 := (norm_expI_taylor (v * B ω)).1
    have habs : |v * B ω| ^ 3 = |v| ^ 3 * |B ω| ^ 3 := by rw [abs_mul, mul_pow]
    calc ‖Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
          - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)‖
        ≤ 4 * |v * B ω| ^ 3 := h1
      _ = 4 * |v| ^ 3 * |B ω| ^ 3 := by rw [habs]; ring
  -- Cauchy–Schwarz on `|B| · B²`
  have hcs : (∫ ω, |B ω| ^ 3 ∂μ) ≤ Real.sqrt ((∫ ω, B ω ^ 2 ∂μ) * ∫ ω, B ω ^ 4 ∂μ) := by
    have habs2 : MemLp (fun ω => |B ω|) 2 μ :=
      memLp_of_abs_bdd hB.abs (by filter_upwards [hbd] with ω hω; simpa using hω) 2
    have hsq2 : MemLp (fun ω => B ω ^ 2) 2 μ := by
      refine memLp_of_abs_bdd (hB.pow_const 2) (M := K ^ 2) ?_ 2
      filter_upwards [hbd] with ω hω
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_abs (B ω), abs_nonneg (B ω), hω]
    have h := sq_integral_mul_le habs2 hsq2
    have e1 : ∫ ω, |B ω| * B ω ^ 2 ∂μ = ∫ ω, |B ω| ^ 3 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by
        show |B ω| * B ω ^ 2 = |B ω| ^ 3
        rw [← sq_abs (B ω)]; ring)
    have e2 : ∫ ω, |B ω| ^ 2 ∂μ = ∫ ω, B ω ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by
        show |B ω| ^ 2 = B ω ^ 2
        rw [sq_abs])
    have e3 : ∫ ω, (B ω ^ 2) ^ 2 ∂μ = ∫ ω, B ω ^ 4 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by
        show (B ω ^ 2) ^ 2 = B ω ^ 4
        ring)
    rw [e1, e2, e3] at h
    have hnn : (0 : ℝ) ≤ ∫ ω, |B ω| ^ 3 ∂μ :=
      integral_nonneg fun ω => by positivity
    calc (∫ ω, |B ω| ^ 3 ∂μ) = Real.sqrt ((∫ ω, |B ω| ^ 3 ∂μ) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∫ ω, B ω ^ 2 ∂μ) * ∫ ω, B ω ^ 4 ∂μ) := Real.sqrt_le_sqrt h
  calc ‖∫ ω, (Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
        - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (((v * B ω : ℝ) : ℂ) * Complex.I)
          - (1 + ((v * B ω : ℝ) : ℂ) * Complex.I - ((v * B ω : ℝ) : ℂ) ^ 2 / 2)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, 4 * |v| ^ 3 * |B ω| ^ 3 ∂μ := integral_mono hrem.norm hcube hpt
    _ = 4 * |v| ^ 3 * ∫ ω, |B ω| ^ 3 ∂μ := integral_const_mul _ _
    _ ≤ 4 * |v| ^ 3 * Real.sqrt ((∫ ω, B ω ^ 2 ∂μ) * ∫ ω, B ω ^ 4 ∂μ) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)

/-- **Product-to-exponential comparison.** If `a_n = 1 + z_n` has modulus at most one,
`Re z_n ≤ 0`, `z_n → 0`, `k_n z_n → w` and `k_n ‖z_n‖² → 0`, then `a_n^{k_n} → e^w`. This
is the scalar limit that replaces the independent-copy array in the Bernstein scheme:
stationarity makes all big blocks identically distributed, so the factorized
characteristic function is a single power. -/
private lemma tendsto_pow_of_tendsto_mul {k : ℕ → ℕ} {z : ℕ → ℂ} {w : ℂ}
    (hz1 : ∀ n, ‖1 + z n‖ ≤ 1) (hzre : ∀ n, (z n).re ≤ 0)
    (hz0 : Tendsto z atTop (𝓝 0))
    (hkz : Tendsto (fun n => (k n : ℂ) * z n) atTop (𝓝 w))
    (hkb : Tendsto (fun n => (k n : ℝ) * ‖z n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => (1 + z n) ^ k n) atTop (𝓝 (Complex.exp w)) := by
  have hexpre : ∀ n, ‖Complex.exp (z n)‖ ≤ 1 := by
    intro n
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (hzre n)
  have hgap : Tendsto (fun n => (1 + z n) ^ k n - Complex.exp ((k n : ℂ) * z n))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hkb
    have hz0' : ∀ᶠ n in atTop, ‖z n‖ ≤ 1 := by
      have := hz0.norm
      simp only [norm_zero] at this
      filter_upwards [this.eventually_le_const (by norm_num : (0:ℝ) < 1)] with n hn using hn
    filter_upwards [hz0'] with n hn
    have hpow : Complex.exp ((k n : ℂ) * z n) = Complex.exp (z n) ^ k n := by
      rw [Complex.exp_nat_mul]
    rw [hpow]
    refine (norm_pow_sub_pow_le_of_norm_le_one (hz1 n) (hexpre n) (k n)).trans ?_
    have hstep : ‖(1 + z n) - Complex.exp (z n)‖ ≤ ‖z n‖ ^ 2 := by
      have h := Complex.norm_exp_sub_one_sub_id_le (x := z n) hn
      rw [← norm_neg]
      have he : -((1 + z n) - Complex.exp (z n)) = Complex.exp (z n) - 1 - z n := by ring
      rw [he]
      exact h
    exact mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg _)
  have hexp : Tendsto (fun n => Complex.exp ((k n : ℂ) * z n)) atTop (𝓝 (Complex.exp w)) :=
    (Complex.continuous_exp.tendsto w).comp hkz
  have := hgap.add hexp
  simpa using this

/-- Strict stationarity transports the law of a length-`m` window: any measurable
functional of a shifted block sum has the anchored expectation. -/
private lemma integral_comp_window_eq [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {F : ℝ → ℂ} (hF : Measurable F) (m : ℕ) (c : ℤ) :
    ∫ ω, F (∑ t ∈ Finset.range m, X ((t : ℤ) + 1 + c) ω) ∂μ
      = ∫ ω, F (∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) ∂μ := by
  have hG : Measurable fun q : Fin m → ℝ => F (∑ i, q i) :=
    hF.comp (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
  have hm1 : Measurable fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1 + c) ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have hm2 : Measurable fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1) ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have key := hstat m (fun i : Fin m => ((i : ℕ) : ℤ) + 1) c
  have e1 := integral_map (μ := μ) (φ := fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1 + c) ω)
    (f := fun q : Fin m → ℝ => F (∑ i, q i)) hm1.aemeasurable hG.aestronglyMeasurable
  have e2 := integral_map (μ := μ) (φ := fun ω (i : Fin m) => X (((i : ℕ) : ℤ) + 1) ω)
    (f := fun q : Fin m → ℝ => F (∑ i, q i)) hm2.aemeasurable hG.aestronglyMeasurable
  rw [key] at e1
  have h := e1.symm.trans e2
  have conv1 : ∀ ω : Ω, ∑ t ∈ Finset.range m, X ((t : ℤ) + 1 + c) ω
      = ∑ i : Fin m, X (((i : ℕ) : ℤ) + 1 + c) ω :=
    fun ω => (Fin.sum_univ_eq_sum_range (fun j : ℕ => X ((j : ℤ) + 1 + c) ω) m).symm
  have conv2 : ∀ ω : Ω, ∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω
      = ∑ i : Fin m, X (((i : ℕ) : ℤ) + 1) ω :=
    fun ω => (Fin.sum_univ_eq_sum_range (fun j : ℕ => X ((j : ℤ) + 1) ω) m).symm
  simp only [conv1, conv2]
  exact h

/-- Cauchy–Schwarz on a probability space in the only form used: `(E|f|)² ≤ E f²`
(the variance of `|f|` is nonnegative). -/
private lemma sq_integral_abs_le [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, |f ω| ∂μ) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂μ := by
  have habs : MemLp (fun ω => |f ω|) 2 μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have h := variance_nonneg (fun ω => |f ω|) μ
  rw [variance_eq_sub habs] at h
  simp only [Pi.pow_apply, sq_abs] at h
  linarith

omit [MeasurableSpace Ω] in
private lemma sigmaLE_mono (X : ℤ → Ω → ℝ) {a b : ℤ} (h : a ≤ b) :
    sigmaLE X a ≤ sigmaLE X b :=
  iSup₂_le fun _ hs => comap_le_sigmaLE X (le_trans hs h)

omit [MeasurableSpace Ω] in
private lemma sigmaGE_mono (X : ℤ → Ω → ℝ) {a b : ℤ} (h : a ≤ b) :
    sigmaGE X b ≤ sigmaGE X a :=
  iSup₂_le fun _ hs => comap_le_sigmaGE X (le_trans h hs)

/-- **Volkonskii–Rozanov for the Bernstein big blocks.** The `j`-th big block occupies
the time window `[j(l+s)+1, j(l+s)+l]`, so its σ-algebra sits inside
`σ{X_t : t ≤ j(l+s)+l} ⊓ σ{X_t : t ≥ j(l+s)+1}`; consecutive cumulative pasts and blocks
are separated by the small block of length `s`, and the shift lemma identifies the gap
coefficient as `α(s+1) ≤ α(s)`. -/
private lemma norm_integral_prod_blocks_sub_prod_le [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (l s : ℕ) {k : ℕ} (hk : 0 < k) (v : ℝ) :
    ‖(∫ ω, ∏ j : Fin k, Complex.exp (((v * ∑ i ∈ Finset.range l,
            X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        - ∏ j : Fin k, ∫ ω, Complex.exp (((v * ∑ i ∈ Finset.range l,
            X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I) ∂μ‖
      ≤ 16 * ((k : ℝ) - 1) * alphaCoeff X μ s := by
  classical
  set m : Fin k → MeasurableSpace Ω := fun j =>
    sigmaLE X (((j : ℕ) * (l + s) : ℕ) + l) ⊓ sigmaGE X (((j : ℕ) * (l + s) : ℕ) + 1) with hm
  have hle : ∀ j, m j ≤ (inferInstance : MeasurableSpace Ω) := fun j =>
    le_trans inf_le_left (sigmaLE_le hmeas _)
  -- each block variable is measurable for the block σ-algebra
  have hcomap : ∀ (j : Fin k) (i : ℕ), i < l →
      MeasurableSpace.comap (X ((i : ℤ) + 1 + (((j : ℕ) * (l + s) : ℕ) : ℤ))) inferInstance
        ≤ m j := by
    intro j i hi
    refine le_inf (comap_le_sigmaLE X ?_) (comap_le_sigmaGE X ?_)
    · have : (i : ℤ) + 1 ≤ (l : ℤ) := by exact_mod_cast hi
      push_cast
      omega
    · push_cast
      omega
  have hmeasξ : ∀ j : Fin k, Measurable[m j] fun ω =>
      Complex.exp (((v * ∑ i ∈ Finset.range l,
        X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I) := by
    intro j
    have hsum : Measurable[m j] fun ω => ∑ i ∈ Finset.range l,
        X ((i : ℤ) + 1 + (((j : ℕ) * (l + s) : ℕ) : ℤ)) ω :=
      Finset.measurable_sum _ fun i hi =>
        (measurable_comap_self X _).mono (hcomap j i (Finset.mem_range.mp hi)) le_rfl
    exact (Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp (measurable_const.mul hsum))).mul measurable_const))
  have hbddξ : ∀ j : Fin k, ∀ᵐ ω ∂μ, ‖Complex.exp (((v * ∑ i ∈ Finset.range l,
      X ((i : ℤ) + 1 + ((j : ℕ) * (l + s) : ℕ)) ω : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro j
    filter_upwards with ω
    rw [Complex.norm_exp_ofReal_mul_I]
  refine norm_integral_prod_sub_prod_integral_le_of_pos hk hle _ hmeasξ hbddξ ?_
  intro j hj
  -- cumulative past ≤ `σ{X_t : t ≤ j(l+s)+l}`, next block ≤ `σ{X_t : t ≥ j(l+s)+l+s+1}`
  have hpast : (⨆ j' : Fin k, ⨆ _ : (j' : ℕ) ≤ (j : ℕ), m j')
      ≤ sigmaLE X (((j : ℕ) * (l + s) : ℕ) + l) := by
    refine iSup₂_le fun j' hj' => le_trans inf_le_left (sigmaLE_mono X ?_)
    have : ((j' : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hj'
    have hmul : ((j' : ℕ) * (l + s) : ℕ) ≤ ((j : ℕ) * (l + s) : ℕ) :=
      Nat.mul_le_mul_right _ hj'
    have : (((j' : ℕ) * (l + s) : ℕ) : ℤ) ≤ (((j : ℕ) * (l + s) : ℕ) : ℤ) := by
      exact_mod_cast hmul
    omega
  have hfut : m ⟨(j : ℕ) + 1, hj⟩
      ≤ sigmaGE X ((((j : ℕ) * (l + s) : ℕ) + l : ℤ) + ((s : ℤ) + 1)) := by
    refine le_trans inf_le_right (sigmaGE_mono X ?_)
    have hmul : (((j : ℕ) + 1) * (l + s) : ℕ) = ((j : ℕ) * (l + s) : ℕ) + (l + s) := by ring
    push_cast [hmul]
    omega
  calc alphaMixCoeff μ (⨆ j' : Fin k, ⨆ _ : (j' : ℕ) ≤ (j : ℕ), m j') (m ⟨(j : ℕ) + 1, hj⟩)
      ≤ alphaMixCoeff μ (sigmaLE X (((j : ℕ) * (l + s) : ℕ) + l))
          (sigmaGE X ((((j : ℕ) * (l + s) : ℕ) + l : ℤ) + ((s : ℤ) + 1))) :=
        alphaMixCoeff_mono hpast hfut
    _ = alphaCoeff X μ (s + 1) := by
        have := hstat.alphaMixCoeff_shift hmeas ((((j : ℕ) * (l + s) : ℕ) + l : ℤ)) (s + 1)
        simpa using this
    _ ≤ alphaCoeff X μ s := alphaCoeff_antitone X (Nat.le_succ s)

/-! #### The fourth moment of a block under summability alone

The bricks below re-derive, **from `Σ α < ∞` only**, the sorted-4-tuple largest-gap split
and the counting that turns it into `E S_l⁴ = o(l³)`.  `Mixing/Inequalities` proves the
same split, but its counting half (`sum_four_le_of_cut_bound`) is stated against the decay
*rate* `α(m) ≤ K m⁻²` (Yokoyama's `O(l²)`), which summability does not supply; only
`m α(m) → 0` is available (`tendsto_mul_alphaCoeff`), and it delivers `o(l³)` by Cesàro.
Those bricks are `private` to `Inequalities`, so they are reproduced here. -/

section Moment4Summable

variable {X : ℤ → Ω → ℝ}

omit [MeasurableSpace Ω] in
private lemma m4_measurable_sigmaLE (X : ℤ → Ω → ℝ) {s t : ℤ} (hst : s ≤ t) :
    Measurable[sigmaLE X t] (X s) :=
  (Measurable.of_comap_le le_rfl).mono
    (le_iSup₂ (f := fun r (_ : r ∈ Set.Iic t) =>
      MeasurableSpace.comap (X r) inferInstance) s hst) le_rfl

omit [MeasurableSpace Ω] in
private lemma m4_measurable_sigmaGE (X : ℤ → Ω → ℝ) {s t : ℤ} (hst : t ≤ s) :
    Measurable[sigmaGE X t] (X s) :=
  (Measurable.of_comap_le le_rfl).mono
    (le_iSup₂ (f := fun r (_ : r ∈ Set.Ici t) =>
      MeasurableSpace.comap (X r) inferInstance) s hst) le_rfl

private lemma m4_sigmaLE_le (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaLE X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

private lemma m4_sigmaGE_le (hmeas : ∀ t, Measurable (X t)) (t : ℤ) :
    sigmaGE X t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

private lemma m4_integrable_of_bdd [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ᵐ ω ∂μ, |f ω| ≤ B) : Integrable f μ :=
  Integrable.mono' (integrable_const B) hf.aestronglyMeasurable
    (by filter_upwards [hb] with ω hω; rwa [Real.norm_eq_abs])

private lemma m4_memLp_of_bdd [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ᵐ ω ∂μ, |f ω| ≤ B) : MemLp f 2 μ := by
  refine MemLp.mono_exponent ?_ le_top
  refine memLp_top_of_bound hf.aestronglyMeasurable B ?_
  filter_upwards [hb] with ω hω
  simpa [Real.norm_eq_abs] using hω

private lemma m4_covariance_eq_sub [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    cov[f, g; μ] = (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  rw [covariance_eq_sub hf hg]
  simp only [Pi.mul_apply]

private lemma m4_integral_eq_zero_of_stat [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (t : ℤ) : ∫ ω, X t ω ∂μ = 0 := by
  rw [(hstat.identDistrib hmeas t 0).integral_eq, hmean]

/-- Billingsley's inequality across a cut of the time axis. -/
private lemma m4_cut_bound [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    {a b : ℤ} (hab : a ≤ b) {f g : Ω → ℝ}
    (hf : Measurable[sigmaLE X a] f) (hg : Measurable[sigmaGE X b] g)
    {C₁ C₂ : ℝ} (hfC : ∀ᵐ ω ∂μ, |f ω| ≤ C₁) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C₂) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ|
      ≤ 4 * alphaCoeff X μ (b - a).toNat * C₁ * C₂ := by
  have hbe : a + ((b - a).toNat : ℤ) = b := by
    rw [Int.toNat_of_nonneg (by omega)]; ring
  have hα : alphaMixCoeff μ (sigmaLE X a) (sigmaGE X b) = alphaCoeff X μ (b - a).toNat := by
    have := IsStrictlyStationary.alphaMixCoeff_shift hstat hmeas a (b - a).toNat
    rwa [hbe] at this
  have h1 : sigmaLE X a ≤ (inferInstance : MeasurableSpace Ω) := m4_sigmaLE_le hmeas a
  have h2 : sigmaGE X b ≤ (inferInstance : MeasurableSpace Ω) := m4_sigmaGE_le hmeas b
  have hcov := abs_covariance_le_of_bounded h1 h2 hf hg hfC hgC
  rw [hα] at hcov
  have hfm : Measurable f := hf.mono h1 le_rfl
  have hgm : Measurable g := hg.mono h2 le_rfl
  rwa [m4_covariance_eq_sub (m4_memLp_of_bdd hfm hfC) (m4_memLp_of_bdd hgm hgC)] at hcov

private lemma m4_abs_mul_le_of_bdd {x y B₁ B₂ : ℝ} (hx : |x| ≤ B₁) (hy : |y| ≤ B₂) :
    |x * y| ≤ B₁ * B₂ := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg _) (le_trans (abs_nonneg _) hx)

private lemma m4_pair_le [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {a b : ℤ} (hab : a ≤ b) :
    |∫ ω, X a ω * X b ω ∂μ| ≤ 4 * alphaCoeff X μ (b - a).toNat * C * C := by
  have h0 : (∫ ω, X a ω ∂μ) = 0 := m4_integral_eq_zero_of_stat hstat hmeas hmean a
  have := m4_cut_bound hstat hmeas hab
    (m4_measurable_sigmaLE X (le_refl a)) (m4_measurable_sigmaGE X (le_refl b)) (hbdd a) (hbdd b)
  rwa [h0, zero_mul, sub_zero] at this

private lemma m4_alphaCoeff_nonneg [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ) (m : ℕ) :
    0 ≤ alphaCoeff X μ m := alphaMixCoeff_nonneg (mΩ := inferInstance)

/-- **The sorted 4-tuple bound**: split `E[X_a X_b X_c X_d]` at its largest gap. -/
private lemma m4_quad_le [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t))
    {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {a b c d : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (max (b - a).toNat (max (c - b).toNat (d - c).toNat))
        + 16 * C ^ 4 * (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by
  have hzero : ∀ t : ℤ, (∫ ω, X t ω ∂μ) = 0 :=
    m4_integral_eq_zero_of_stat hstat hmeas hmean
  have hC4 : (0:ℝ) ≤ C ^ 4 := by positivity
  have hL : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (b - a).toNat := by
    have hgm : Measurable[sigmaGE X b] fun ω => X b ω * X c ω * X d ω :=
      ((m4_measurable_sigmaGE X (le_refl b)).mul (m4_measurable_sigmaGE X hbc)).mul
        (m4_measurable_sigmaGE X (hbc.trans hcd))
    have hgC : ∀ᵐ ω ∂μ, |X b ω * X c ω * X d ω| ≤ C * C * C := by
      filter_upwards [hbdd b, hbdd c, hbdd d] with ω e1 e2 e3
      exact m4_abs_mul_le_of_bdd (m4_abs_mul_le_of_bdd e1 e2) e3
    have key := m4_cut_bound hstat hmeas hab
      (m4_measurable_sigmaLE X (le_refl a)) hgm (hbdd a) hgC
    rw [hzero a, zero_mul, sub_zero] at key
    have hre : (∫ ω, X a ω * (X b ω * X c ω * X d ω) ∂μ)
        = ∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [hre] at key
    refine key.trans (le_of_eq ?_)
    ring
  have hR : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (d - c).toNat := by
    have hfm : Measurable[sigmaLE X c] fun ω => X a ω * X b ω * X c ω :=
      ((m4_measurable_sigmaLE X (hab.trans hbc)).mul (m4_measurable_sigmaLE X hbc)).mul
        (m4_measurable_sigmaLE X (le_refl c))
    have hfC : ∀ᵐ ω ∂μ, |X a ω * X b ω * X c ω| ≤ C * C * C := by
      filter_upwards [hbdd a, hbdd b, hbdd c] with ω e1 e2 e3
      exact m4_abs_mul_le_of_bdd (m4_abs_mul_le_of_bdd e1 e2) e3
    have key := m4_cut_bound hstat hmeas hcd hfm
      (m4_measurable_sigmaGE X (le_refl d)) hfC (hbdd d)
    rw [hzero d, mul_zero, sub_zero] at key
    refine key.trans (le_of_eq ?_)
    ring
  have hM : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
      ≤ 4 * C ^ 4 * alphaCoeff X μ (c - b).toNat
        + 16 * C ^ 4 * (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by
    have hfm : Measurable[sigmaLE X b] fun ω => X a ω * X b ω :=
      (m4_measurable_sigmaLE X hab).mul (m4_measurable_sigmaLE X (le_refl b))
    have hgm : Measurable[sigmaGE X c] fun ω => X c ω * X d ω :=
      (m4_measurable_sigmaGE X (le_refl c)).mul (m4_measurable_sigmaGE X hcd)
    have hfC : ∀ᵐ ω ∂μ, |X a ω * X b ω| ≤ C * C := by
      filter_upwards [hbdd a, hbdd b] with ω e1 e2
      exact m4_abs_mul_le_of_bdd e1 e2
    have hgC : ∀ᵐ ω ∂μ, |X c ω * X d ω| ≤ C * C := by
      filter_upwards [hbdd c, hbdd d] with ω e1 e2
      exact m4_abs_mul_le_of_bdd e1 e2
    have key := m4_cut_bound hstat hmeas hbc hfm hgm hfC hgC
    have hre : (∫ ω, (X a ω * X b ω) * (X c ω * X d ω) ∂μ)
        = ∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [hre] at key
    have hpair1 := m4_pair_le hstat hmeas hbdd hmean hab
    have hpair2 := m4_pair_le hstat hmeas hbdd hmean hcd
    have hsplit : |∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ|
        ≤ |(∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ)
            - (∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ|
          + |(∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ| := by
      have := abs_add_le ((∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ)
        - (∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ)
        ((∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ)
      simpa using this
    have hpp : |(∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ|
        ≤ (4 * alphaCoeff X μ (b - a).toNat * C * C)
          * (4 * alphaCoeff X μ (d - c).toNat * C * C) := by
      rw [abs_mul]
      exact mul_le_mul hpair1 hpair2 (abs_nonneg _) (le_trans (abs_nonneg _) hpair1)
    have harr : (4 * alphaCoeff X μ (b - a).toNat * C * C)
          * (4 * alphaCoeff X μ (d - c).toNat * C * C)
        = 16 * C ^ 4 * (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by
      ring
    rw [harr] at hpp
    have hkey' : |(∫ ω, X a ω * X b ω * X c ω * X d ω ∂μ)
        - (∫ ω, X a ω * X b ω ∂μ) * ∫ ω, X c ω * X d ω ∂μ|
        ≤ 4 * C ^ 4 * alphaCoeff X μ (c - b).toNat := by
      refine key.trans (le_of_eq ?_)
      ring
    linarith
  have hextra : (0:ℝ) ≤ 16 * C ^ 4 *
      (alphaCoeff X μ (b - a).toNat * alphaCoeff X μ (d - c).toNat) := by
    have := m4_alphaCoeff_nonneg (μ := μ) X (b - a).toNat
    have := m4_alphaCoeff_nonneg (μ := μ) X (d - c).toNat
    positivity
  rcases max_choice (b - a).toNat (max (c - b).toNat (d - c).toNat) with hmx | hmx
  · rw [hmx]; linarith
  · rw [hmx]
    rcases max_choice (c - b).toNat (d - c).toNat with hmx' | hmx'
    · rw [hmx']; linarith
    · rw [hmx']; linarith

/-! ### The combinatorial layer -/

/-- The four-fold expansion of a fourth power of a finite sum. -/
private lemma m4_sum_pow_four_expand {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ t ∈ s, f t) ^ 4
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, f a * f b * f c * f d := by
  have h2 : (∑ t ∈ s, f t) * (∑ t ∈ s, f t) = ∑ a ∈ s, ∑ b ∈ s, f a * f b := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
  have h3 : (∑ t ∈ s, f t) ^ 3 = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c := by
    have e : (∑ t ∈ s, f t) ^ 3 = (∑ a ∈ s, ∑ b ∈ s, f a * f b) * ∑ t ∈ s, f t := by
      rw [← h2]; ring
    rw [e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _
  have e : (∑ t ∈ s, f t) ^ 4
      = (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, f a * f b * f c) * ∑ t ∈ s, f t := by
    rw [← h3]; ring
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => Finset.mul_sum _ _ _

/-- Invariance of a 4-tuple functional under a permutation, from invariance under swaps. -/
private theorem m4_tuple4_comp_perm_invariant {Gt : (Fin 4 → ℕ) → ℝ}
    (hs : ∀ (i j : Fin 4) (f : Fin 4 → ℕ), Gt (f ∘ Equiv.swap i j) = Gt f)
    (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → ℕ) : Gt (f ∘ σ) = Gt f := by
  have hmem : σ ∈ Submonoid.closure {τ : Equiv.Perm (Fin 4) | τ.IsSwap} := by
    rw [Equiv.Perm.mclosure_isSwap]; trivial
  revert f
  induction hmem using Submonoid.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, _, rfl⟩ := hx
      exact fun f => hs i j f
  | one => intro f; simp
  | mul x y hx hy ihx ihy =>
      intro f
      have hcomp : f ∘ (x * y) = (f ∘ x) ∘ y := by
        funext a; simp [Equiv.Perm.mul_apply]
      rw [hcomp, ihy (f ∘ x), ihx f]

private theorem m4_tuple4_swap_invariant {G : ℕ → ℕ → ℕ → ℕ → ℝ}
    (hGs1 : ∀ a b c d, G a b c d = G b a c d)
    (hGs2 : ∀ a b c d, G a b c d = G a c b d)
    (hGs3 : ∀ a b c d, G a b c d = G a b d c)
    (i j : Fin 4) (f : Fin 4 → ℕ) :
    G ((f ∘ Equiv.swap i j) 0) ((f ∘ Equiv.swap i j) 1) ((f ∘ Equiv.swap i j) 2)
        ((f ∘ Equiv.swap i j) 3)
      = G (f 0) (f 1) (f 2) (f 3) := by
  have e02 : ∀ a b c d, G a b c d = G c b a d := fun a b c d =>
    (hGs1 a b c d).trans ((hGs2 b a c d).trans (hGs1 b c a d))
  have e13 : ∀ a b c d, G a b c d = G a d c b := fun a b c d =>
    (hGs2 a b c d).trans ((hGs3 a c b d).trans (hGs2 a c d b))
  have e03 : ∀ a b c d, G a b c d = G d b c a := fun a b c d =>
    (hGs1 a b c d).trans ((hGs3 b a c d).trans ((hGs2 b a d c).trans
      ((hGs1 b d a c).trans (hGs3 d b a c))))
  fin_cases i <;> fin_cases j <;>
    simp only [Function.comp_apply, Equiv.swap_apply_def] <;> norm_num <;>
    first
      | rfl
      | exact (hGs1 _ _ _ _).symm
      | exact (hGs2 _ _ _ _).symm
      | exact (hGs3 _ _ _ _).symm
      | exact (e02 _ _ _ _).symm
      | exact (e13 _ _ _ _).symm
      | exact (e03 _ _ _ _).symm

/-- Symmetrisation: a permutation-invariant nonnegative functional summed over a
permutation-closed family is at most `4!` times its sum over the sorted members. -/
private theorem m4_sum_tuple4_le_sorted {Gt : (Fin 4 → ℕ) → ℝ} (hGt0 : ∀ f, 0 ≤ Gt f)
    (hperm : ∀ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → ℕ), Gt (f ∘ σ) = Gt f)
    (P : Finset (Fin 4 → ℕ))
    (hP : ∀ f ∈ P, ∀ σ : Equiv.Perm (Fin 4), f ∘ σ ∈ P) :
    ∑ f ∈ P, Gt f
      ≤ 24 * ∑ u ∈ P.filter (fun u => u 0 ≤ u 1 ∧ u 1 ≤ u 2 ∧ u 2 ≤ u 3), Gt u := by
  classical
  set Φ : (Fin 4 → ℕ) → (Fin 4 → ℕ) := fun f => f ∘ Tuple.sort f with hΦ
  set Pm := P.filter (fun u => u 0 ≤ u 1 ∧ u 1 ≤ u 2 ∧ u 2 ≤ u 3) with hPm
  have hmaps : ∀ f ∈ P, Φ f ∈ Pm := by
    intro f hf
    have hmono : Monotone (f ∘ Tuple.sort f) := Tuple.monotone_sort f
    refine Finset.mem_filter.2 ⟨hP f hf _, ?_, ?_, ?_⟩
    · exact hmono (by decide : (0 : Fin 4) ≤ 1)
    · exact hmono (by decide : (1 : Fin 4) ≤ 2)
    · exact hmono (by decide : (2 : Fin 4) ≤ 3)
  have hcard : ∀ u : Fin 4 → ℕ, (P.filter (fun f => Φ f = u)).card ≤ 24 := by
    intro u
    have hsub : P.filter (fun f => Φ f = u)
        ⊆ (Finset.univ : Finset (Equiv.Perm (Fin 4))).image
            (fun σ : Equiv.Perm (Fin 4) => u ∘ (σ : Fin 4 → Fin 4)) := by
      intro f hf
      obtain ⟨-, hfu⟩ := Finset.mem_filter.1 hf
      refine Finset.mem_image.2 ⟨(Tuple.sort f)⁻¹, Finset.mem_univ _, ?_⟩
      rw [← hfu, hΦ]
      funext a
      simp
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    decide
  calc ∑ f ∈ P, Gt f
      = ∑ u ∈ Pm, ∑ f ∈ P.filter (fun f => Φ f = u), Gt f :=
        (Finset.sum_fiberwise_of_maps_to hmaps Gt).symm
    _ ≤ ∑ u ∈ Pm, 24 * Gt u := by
        refine Finset.sum_le_sum fun u _ => ?_
        have hval : ∀ f ∈ P.filter (fun f => Φ f = u), Gt f = Gt u := by
          intro f hf
          obtain ⟨-, hfu⟩ := Finset.mem_filter.1 hf
          rw [← hfu, hΦ]
          exact (hperm (Tuple.sort f) f).symm
        rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u) (hGt0 u)
    _ = 24 * ∑ u ∈ Pm, Gt u := by rw [Finset.mul_sum]

private theorem m4_sum_piFinset_four (s : Finset ℕ) (F : (Fin 4 → ℕ) → ℝ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin 4 => s), F f
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F ![a, b, c, d] := by
  classical
  have hprod : ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, F ![a, b, c, d]
      = ∑ p ∈ s ×ˢ (s ×ˢ (s ×ˢ s)), F ![p.1, p.2.1, p.2.2.1, p.2.2.2] := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product]
  rw [hprod]
  refine Finset.sum_nbij' (fun f => (f 0, f 1, f 2, f 3))
    (fun p => ![p.1, p.2.1, p.2.2.1, p.2.2.2]) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    rw [Fintype.mem_piFinset] at hf
    simp only [Finset.mem_product]
    exact ⟨hf 0, hf 1, hf 2, hf 3⟩
  · intro p hp
    simp only [Finset.mem_product] at hp
    rw [Fintype.mem_piFinset]
    intro i
    fin_cases i <;> simp [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
  · intro f _
    funext i
    fin_cases i <;> rfl
  · intro p _
    rfl
  · intro f _
    congr 1
    funext i
    fin_cases i <;> rfl

private theorem m4_max_le_indicators {A : ℕ → ℝ} (hA0 : ∀ m, 0 ≤ A m) (g1 g2 g3 : ℕ) :
    A (max g1 (max g2 g3))
      ≤ (if g2 ≤ g1 then (1 : ℝ) else 0) * (if g3 ≤ g1 then (1 : ℝ) else 0) * A g1
        + (if g1 ≤ g2 then (1 : ℝ) else 0) * (if g3 ≤ g2 then (1 : ℝ) else 0) * A g2
        + (if g1 ≤ g3 then (1 : ℝ) else 0) * (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3 := by
  rcases le_total g1 g2 with h12 | h12 <;> rcases le_total g2 g3 with h23 | h23 <;>
    rcases le_total g1 g3 with h13 | h13 <;>
    simp_all [max_def] <;>
    split_ifs <;> linarith [hA0 g1, hA0 g2, hA0 g3]

private theorem m4_sum_indicator_le_succ {n m : ℕ} :
    ∑ g ∈ Finset.range n, (if g ≤ m then (1 : ℝ) else 0) ≤ (m : ℝ) + 1 := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.range n).filter (fun g => g ≤ m) ⊆ Finset.range (m + 1) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_range] at hg ⊢
    omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  have hc' : (((Finset.range n).filter (fun g => g ≤ m)).card : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast hc
  push_cast at hc'
  linarith

private theorem m4_sum_triple_indicator_le {A : ℕ → ℝ} (hA0 : ∀ m, 0 ≤ A m) (n : ℕ) :
    ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
        (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
      ≤ ∑ x ∈ Finset.range n, A x * ((x : ℝ) + 1) ^ 2 := by
  have hfac : ∀ x : ℕ, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
      (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
      = (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
        ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x) := by
    intro x
    have inner : ∀ y : ℕ, ∑ z ∈ Finset.range n,
        (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
        = (if y ≤ x then (1 : ℝ) else 0) *
          ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x) := by
      intro y
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => mul_assoc _ _ _
    rw [Finset.sum_congr rfl fun y _ => inner y, ← Finset.sum_mul]
  have hbound : ∀ x ∈ Finset.range n,
      (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
        ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x)
      ≤ A x * ((x : ℝ) + 1) ^ 2 := by
    intro x _
    have hI0 : (0 : ℝ) ≤ ∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0) :=
      Finset.sum_nonneg fun y _ => by positivity
    have hI := m4_sum_indicator_le_succ (n := n) (m := x)
    have hx0 : (0 : ℝ) ≤ (x : ℝ) + 1 := by positivity
    calc (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
          ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x)
        ≤ ((x : ℝ) + 1) * (((x : ℝ) + 1) * A x) := by
          refine mul_le_mul hI ?_ (mul_nonneg hI0 (hA0 x)) hx0
          exact mul_le_mul_of_nonneg_right hI (hA0 x)
      _ = A x * ((x : ℝ) + 1) ^ 2 := by ring
  calc ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, ∑ z ∈ Finset.range n,
          (if y ≤ x then (1 : ℝ) else 0) * (if z ≤ x then (1 : ℝ) else 0) * A x
      = ∑ x ∈ Finset.range n, (∑ y ∈ Finset.range n, (if y ≤ x then (1 : ℝ) else 0)) *
          ((∑ z ∈ Finset.range n, (if z ≤ x then (1 : ℝ) else 0)) * A x) :=
        Finset.sum_congr rfl fun x _ => hfac x
    _ ≤ ∑ x ∈ Finset.range n, A x * ((x : ℝ) + 1) ^ 2 := Finset.sum_le_sum hbound

/-- The triple sum of `A` at the largest gap, under **summability only**: it is at most
three copies of the quadratically weighted partial sum `W n = ∑_{g<n} A(g)(g+1)²`. -/
private theorem m4_sum_triple_max_le {A : ℕ → ℝ} (hA0 : ∀ m, 0 ≤ A m) (n : ℕ) :
    ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
        A (max g1 (max g2 g3))
      ≤ 3 * ∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2 := by
  have hle : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
        A (max g1 (max g2 g3))
      ≤ ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
        ((if g2 ≤ g1 then (1 : ℝ) else 0) * (if g3 ≤ g1 then (1 : ℝ) else 0) * A g1
          + (if g1 ≤ g2 then (1 : ℝ) else 0) * (if g3 ≤ g2 then (1 : ℝ) else 0) * A g2
          + (if g1 ≤ g3 then (1 : ℝ) else 0) * (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3) :=
    Finset.sum_le_sum fun g1 _ => Finset.sum_le_sum fun g2 _ =>
      Finset.sum_le_sum fun g3 _ => m4_max_le_indicators hA0 g1 g2 g3
  refine hle.trans ?_
  set W : ℝ := ∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2 with hW
  rw [show (3 : ℝ) * W = W + W + W from by ring]
  simp only [Finset.sum_add_distrib]
  have hT1 : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
      (if g2 ≤ g1 then (1 : ℝ) else 0) * (if g3 ≤ g1 then (1 : ℝ) else 0) * A g1
      ≤ W := m4_sum_triple_indicator_le hA0 n
  have hT2 : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
      (if g1 ≤ g2 then (1 : ℝ) else 0) * (if g3 ≤ g2 then (1 : ℝ) else 0) * A g2
      ≤ W := by
    rw [Finset.sum_comm]
    exact m4_sum_triple_indicator_le hA0 n
  have hT3 : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
      (if g1 ≤ g3 then (1 : ℝ) else 0) * (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3
      ≤ W := by
    rw [Finset.sum_congr rfl fun g1 (_ : g1 ∈ Finset.range n) => Finset.sum_comm
      (s := Finset.range n) (t := Finset.range n)
      (f := fun g2 g3 => (if g1 ≤ g3 then (1 : ℝ) else 0) *
        (if g2 ≤ g3 then (1 : ℝ) else 0) * A g3), Finset.sum_comm]
    exact m4_sum_triple_indicator_le hA0 n
  linarith

private theorem m4_sum_triple_pair_le {A : ℕ → ℝ} {M : ℝ} (hA0 : ∀ m, 0 ≤ M → 0 ≤ A m)
    (hM0 : 0 ≤ M) (hAM : ∀ k : ℕ, ∑ g ∈ Finset.range k, A g ≤ M) (n : ℕ) :
    ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n, A g1 * A g3
      ≤ (n : ℝ) * M ^ 2 := by
  set S : ℝ := ∑ g ∈ Finset.range n, A g with hSdef
  have hS0 : (0 : ℝ) ≤ S := Finset.sum_nonneg fun g _ => hA0 g hM0
  have hS := hAM n
  have heq : ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n, A g1 * A g3
      = (n : ℝ) * (S * S) := by
    have h3 : ∀ g1 : ℕ, ∑ g3 ∈ Finset.range n, A g1 * A g3 = A g1 * S := by
      intro g1; rw [hSdef, Finset.mul_sum]
    have h2 : ∀ g1 : ℕ, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n, A g1 * A g3
        = (n : ℝ) * (A g1 * S) := by
      intro g1
      rw [Finset.sum_congr rfl fun g2 _ => h3 g1, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun g1 _ => h2 g1, ← Finset.mul_sum]
    rw [show (∑ g1 ∈ Finset.range n, A g1 * S) = S * S from by
      rw [← Finset.sum_mul, ← hSdef]]
  rw [heq]
  have hsq : S * S ≤ M ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)

/-- **The counting half under summability alone.**  A symmetric nonnegative kernel `G` on
`ℕ⁴` whose *sorted* values obey the mixing cut bound against a nonnegative `A` with
uniformly bounded partial sums has

`∑_{(range n)⁴} G ≤ 24 n (12 C⁴ W n + 16 C⁴ n M²)`,  `W n = ∑_{g<n} A(g)(g+1)²`.

Unlike `Mixing/Inequalities.sum_four_le_of_cut_bound` this needs **no decay rate** on `A`;
the price is that the first term is expressed through `W n` rather than being `O(n)`. -/
private theorem m4_sum_four_le {G : ℕ → ℕ → ℕ → ℕ → ℝ} {A : ℕ → ℝ} {C M : ℝ}
    (hA0 : ∀ m, 0 ≤ A m) (hM0 : 0 ≤ M) (hAM : ∀ k : ℕ, ∑ g ∈ Finset.range k, A g ≤ M)
    (hG0 : ∀ a b c d, 0 ≤ G a b c d)
    (hGs1 : ∀ a b c d, G a b c d = G b a c d)
    (hGs2 : ∀ a b c d, G a b c d = G a c b d)
    (hGs3 : ∀ a b c d, G a b c d = G a b d c)
    (hcut : ∀ a b c d : ℕ, a ≤ b → b ≤ c → c ≤ d →
      G a b c d ≤ 4 * C ^ 4 * A (max (b - a) (max (c - b) (d - c)))
        + 16 * C ^ 4 * (A (b - a) * A (d - c)))
    (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range n,
        ∑ d ∈ Finset.range n, G a b c d
      ≤ 24 * ((n : ℝ) * (12 * C ^ 4 * (∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2)
          + 16 * C ^ 4 * ((n : ℝ) * M ^ 2))) := by
  classical
  have hC4 : (0 : ℝ) ≤ C ^ 4 := by positivity
  obtain ⟨Gt, hGt⟩ : ∃ Gt : (Fin 4 → ℕ) → ℝ, ∀ f, Gt f = G (f 0) (f 1) (f 2) (f 3) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : (Fin 4 → ℕ) → ℝ, ∀ v,
      B v = 4 * C ^ 4 * A (max (v 1) (max (v 2) (v 3))) + 16 * C ^ 4 * (A (v 1) * A (v 3)) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin 4 → ℕ) → (Fin 4 → ℕ), ∀ u,
      ψ u = ![u 0, u 1 - u 0, u 2 - u 1, u 3 - u 2] := ⟨_, fun _ => rfl⟩
  set P : Finset (Fin 4 → ℕ) := Fintype.piFinset (fun _ : Fin 4 => Finset.range n) with hP
  set Pm : Finset (Fin 4 → ℕ) :=
    P.filter (fun u => u 0 ≤ u 1 ∧ u 1 ≤ u 2 ∧ u 2 ≤ u 3) with hPmdef
  have hB0 : ∀ v, 0 ≤ B v := by
    intro v
    rw [hB]
    have t1 : (0 : ℝ) ≤ 4 * C ^ 4 * A (max (v 1) (max (v 2) (v 3))) :=
      mul_nonneg (by positivity) (hA0 _)
    have t2 : (0 : ℝ) ≤ 16 * C ^ 4 * (A (v 1) * A (v 3)) :=
      mul_nonneg (by positivity) (mul_nonneg (hA0 _) (hA0 _))
    linarith
  have hLHS : ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range n,
      ∑ d ∈ Finset.range n, G a b c d = ∑ f ∈ P, Gt f := by
    rw [hP, m4_sum_piFinset_four]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    rw [hGt]
    rfl
  have hperm : ∀ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → ℕ), Gt (f ∘ σ) = Gt f := by
    refine m4_tuple4_comp_perm_invariant ?_
    intro i j f
    rw [hGt, hGt]
    exact m4_tuple4_swap_invariant hGs1 hGs2 hGs3 i j f
  have hPclosed : ∀ f ∈ P, ∀ σ : Equiv.Perm (Fin 4), f ∘ σ ∈ P := by
    intro f hf σ
    rw [hP, Fintype.mem_piFinset] at hf ⊢
    exact fun i => hf (σ i)
  have hsym := m4_sum_tuple4_le_sorted (Gt := Gt) (fun f => by rw [hGt]; exact hG0 _ _ _ _)
    hperm P hPclosed
  rw [← hPmdef] at hsym
  have hcut' : ∀ u ∈ Pm, Gt u ≤ B (ψ u) := by
    intro u hu
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hu
    rw [hGt, hB, hψ]
    simpa using hcut (u 0) (u 1) (u 2) (u 3) h1 h2 h3
  have hψmem : ∀ u ∈ Pm, ψ u ∈ P := by
    intro u hu
    obtain ⟨huP, -⟩ := Finset.mem_filter.1 hu
    rw [hP, Fintype.mem_piFinset] at huP ⊢
    intro i
    rw [hψ]
    have h0 := huP 0
    have h1 := huP 1
    have h2 := huP 2
    have h3 := huP 3
    simp only [Finset.mem_range] at h0 h1 h2 h3 ⊢
    fin_cases i <;> simp <;> omega
  have hψinj : ∀ u ∈ Pm, ∀ u' ∈ Pm, ψ u = ψ u' → u = u' := by
    intro u hu u' hu' heq
    obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.1 hu
    obtain ⟨-, h1', h2', h3'⟩ := Finset.mem_filter.1 hu'
    have e0 : u 0 = u' 0 := by
      have h := congrFun heq 0; rw [hψ, hψ] at h; exact h
    have e1 : u 1 - u 0 = u' 1 - u' 0 := by
      have h := congrFun heq 1; rw [hψ, hψ] at h; exact h
    have e2 : u 2 - u 1 = u' 2 - u' 1 := by
      have h := congrFun heq 2; rw [hψ, hψ] at h; exact h
    have e3 : u 3 - u 2 = u' 3 - u' 2 := by
      have h := congrFun heq 3; rw [hψ, hψ] at h; exact h
    have q0 : u 0 = u' 0 := by omega
    have q1 : u 1 = u' 1 := by omega
    have q2 : u 2 = u' 2 := by omega
    have q3 : u 3 = u' 3 := by omega
    funext i
    fin_cases i <;> assumption
  have hstep : ∑ u ∈ Pm, Gt u ≤ ∑ v ∈ P, B v := by
    calc ∑ u ∈ Pm, Gt u ≤ ∑ u ∈ Pm, B (ψ u) := Finset.sum_le_sum hcut'
      _ = ∑ v ∈ Pm.image ψ, B v := (Finset.sum_image hψinj).symm
      _ ≤ ∑ v ∈ P, B v := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun v _ _ => hB0 v)
          intro v hv
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hv
          exact hψmem u hu
  have hBsum : ∑ v ∈ P, B v
      ≤ (n : ℝ) * (12 * C ^ 4 * (∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2)
        + 16 * C ^ 4 * ((n : ℝ) * M ^ 2)) := by
    rw [hP, m4_sum_piFinset_four]
    have hin : ∀ a : ℕ, ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
        ∑ g3 ∈ Finset.range n, B ![a, g1, g2, g3]
        ≤ 12 * C ^ 4 * (∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2)
          + 16 * C ^ 4 * ((n : ℝ) * M ^ 2) := by
      intro a
      have hval : ∀ g1 g2 g3 : ℕ, B ![a, g1, g2, g3]
          = 4 * C ^ 4 * A (max g1 (max g2 g3)) + 16 * C ^ 4 * (A g1 * A g3) := by
        intro g1 g2 g3; rw [hB]; rfl
      calc ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
              B ![a, g1, g2, g3]
          = ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n, ∑ g3 ∈ Finset.range n,
              (4 * C ^ 4 * A (max g1 (max g2 g3)) + 16 * C ^ 4 * (A g1 * A g3)) :=
            Finset.sum_congr rfl fun g1 _ => Finset.sum_congr rfl fun g2 _ =>
              Finset.sum_congr rfl fun g3 _ => hval g1 g2 g3
        _ = 4 * C ^ 4 * (∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
                ∑ g3 ∈ Finset.range n, A (max g1 (max g2 g3)))
              + 16 * C ^ 4 * (∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
                ∑ g3 ∈ Finset.range n, A g1 * A g3) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ 12 * C ^ 4 * (∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2)
              + 16 * C ^ 4 * ((n : ℝ) * M ^ 2) := by
            have hm := m4_sum_triple_max_le hA0 n
            have hp := m4_sum_triple_pair_le (A := A) (M := M) (fun m _ => hA0 m) hM0 hAM n
            nlinarith
    calc ∑ a ∈ Finset.range n, ∑ g1 ∈ Finset.range n, ∑ g2 ∈ Finset.range n,
            ∑ g3 ∈ Finset.range n, B ![a, g1, g2, g3]
        ≤ ∑ _a ∈ Finset.range n, (12 * C ^ 4 * (∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2)
            + 16 * C ^ 4 * ((n : ℝ) * M ^ 2)) := Finset.sum_le_sum fun a _ => hin a
      _ = (n : ℝ) * (12 * C ^ 4 * (∑ g ∈ Finset.range n, A g * ((g : ℝ) + 1) ^ 2)
            + 16 * C ^ 4 * ((n : ℝ) * M ^ 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hLHS]
  refine hsym.trans ?_
  have hchain := hstep.trans hBsum
  linarith

/-! ### The fourth-moment bound and its `o(l³)` rate -/

/-- **`E S_l⁴ ≤ 24 l (12 C⁴ W_l + 16 C⁴ l Λ_α²)`** for a bounded, zero-mean, strictly
stationary process with **summable** mixing coefficients, where
`W_l = ∑_{g<l} α(g)(g+1)²` and `Λ_α = ∑' α`. -/
private theorem m4_moment4_le [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) (n : ℕ) :
    ∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 4 ∂μ
      ≤ 24 * ((n : ℝ) * (12 * C ^ 4 *
          (∑ g ∈ Finset.range n, alphaCoeff X μ g * ((g : ℝ) + 1) ^ 2)
        + 16 * C ^ 4 * ((n : ℝ) * (∑' g : ℕ, alphaCoeff X μ g) ^ 2))) := by
  classical
  have hA0 : ∀ m, 0 ≤ alphaCoeff X μ m := m4_alphaCoeff_nonneg X
  have hM0 : (0 : ℝ) ≤ ∑' g : ℕ, alphaCoeff X μ g := tsum_nonneg hA0
  have hAM : ∀ k : ℕ, ∑ g ∈ Finset.range k, alphaCoeff X μ g ≤ ∑' g : ℕ, alphaCoeff X μ g :=
    fun k => hα.sum_le_tsum _ (fun i _ => hA0 i)
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ℕ → ℕ → ℝ, ∀ a b c d, G a b c d =
      |∫ ω, X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω * X ((c : ℤ) + 1) ω
        * X ((d : ℤ) + 1) ω ∂μ| := ⟨_, fun _ _ _ _ => rfl⟩
  have hGsymm : ∀ (a b c d a' b' c' d' : ℕ),
      (∀ ω, X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω * X ((c : ℤ) + 1) ω * X ((d : ℤ) + 1) ω
        = X ((a' : ℤ) + 1) ω * X ((b' : ℤ) + 1) ω * X ((c' : ℤ) + 1) ω * X ((d' : ℤ) + 1) ω)
      → G a b c d = G a' b' c' d' := by
    intro a b c d a' b' c' d' he
    rw [hG, hG]
    congr 1
    exact integral_congr_ae (ae_of_all _ he)
  have hcut : ∀ a b c d : ℕ, a ≤ b → b ≤ c → c ≤ d →
      G a b c d ≤ 4 * C ^ 4 * alphaCoeff X μ (max (b - a) (max (c - b) (d - c)))
        + 16 * C ^ 4 * (alphaCoeff X μ (b - a) * alphaCoeff X μ (d - c)) := by
    intro a b c d hab hbc hcd
    have e1 : (((b : ℤ) + 1) - ((a : ℤ) + 1)).toNat = b - a := by omega
    have e2 : (((c : ℤ) + 1) - ((b : ℤ) + 1)).toNat = c - b := by omega
    have e3 : (((d : ℤ) + 1) - ((c : ℤ) + 1)).toNat = d - c := by omega
    have key := m4_quad_le hstat hmeas hbdd hmean
      (a := (a : ℤ) + 1) (b := (b : ℤ) + 1) (c := (c : ℤ) + 1) (d := (d : ℤ) + 1)
      (by omega) (by omega) (by omega)
    rw [e1, e2, e3] at key
    rw [hG]
    exact key
  have hD := m4_sum_four_le (G := G) (A := fun m : ℕ => alphaCoeff X μ m) (C := C)
    (M := ∑' g : ℕ, alphaCoeff X μ g) hA0 hM0 hAM
    (fun a b c d => by rw [hG]; exact abs_nonneg _)
    (fun a b c d => hGsymm _ _ _ _ _ _ _ _ fun ω => by ring)
    (fun a b c d => hGsymm _ _ _ _ _ _ _ _ fun ω => by ring)
    (fun a b c d => hGsymm _ _ _ _ _ _ _ _ fun ω => by ring) hcut n
  have hint : ∀ a b c d : ℕ, Integrable (fun ω => X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω
      * X ((c : ℤ) + 1) ω * X ((d : ℤ) + 1) ω) μ := by
    intro a b c d
    refine m4_integrable_of_bdd ((((hmeas _).mul (hmeas _)).mul (hmeas _)).mul (hmeas _))
      (B := C * C * C * C) ?_
    filter_upwards [hbdd ((a : ℤ) + 1), hbdd ((b : ℤ) + 1), hbdd ((c : ℤ) + 1),
      hbdd ((d : ℤ) + 1)] with ω f1 f2 f3 f4
    exact m4_abs_mul_le_of_bdd (m4_abs_mul_le_of_bdd (m4_abs_mul_le_of_bdd f1 f2) f3) f4
  have hexp : (∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 4 ∂μ)
      = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, ∑ c ∈ Finset.range n,
          ∑ d ∈ Finset.range n, ∫ ω, X ((a : ℤ) + 1) ω * X ((b : ℤ) + 1) ω
            * X ((c : ℤ) + 1) ω * X ((d : ℤ) + 1) ω ∂μ := by
    rw [integral_congr_ae (ae_of_all _ fun ω =>
      m4_sum_pow_four_expand (Finset.range n) fun t : ℕ => X ((t : ℤ) + 1) ω)]
    rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ =>
      integrable_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ fun b _ => integrable_finset_sum _ fun c _ =>
      integrable_finset_sum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finset_sum _ fun c _ => integrable_finset_sum _ fun d _ => hint a b c d]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact integral_finset_sum _ fun d _ => hint a b c d
  rw [hexp]
  refine le_trans ?_ hD
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => ?_
  rw [hG]
  exact le_abs_self _

/-- **Cesàro**: if `c_g → 0` then `∑_{g<l} (g+1) c_g = o(l²)`. -/
private lemma m4_tendsto_weighted_div_sq {c : ℕ → ℝ} (hc0 : ∀ m, 0 ≤ c m)
    (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun l : ℕ => (∑ g ∈ Finset.range l, ((g : ℝ) + 1) * c g) / (l : ℝ) ^ 2)
      atTop (𝓝 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hc.eventually_le_const (half_pos hε))
  set Kn : ℝ := ∑ g ∈ Finset.range N, ((g : ℝ) + 1) * c g with hKn
  have hKn0 : 0 ≤ Kn := Finset.sum_nonneg fun g _ => mul_nonneg (by positivity) (hc0 g)
  have hsq : Tendsto (fun l : ℕ => (l : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (n := 2) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hKlim : Tendsto (fun l : ℕ => Kn / (l : ℝ) ^ 2) atTop (𝓝 0) := hsq.const_div_atTop Kn
  filter_upwards [hKlim.eventually_lt_const (half_pos hε), eventually_ge_atTop (max N 1)]
    with l hlt hlge
  have hlN : N ≤ l := le_trans (le_max_left _ _) hlge
  have hl1 : 1 ≤ l := le_trans (le_max_right _ _) hlge
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl1
  have hsum0 : (0 : ℝ) ≤ ∑ g ∈ Finset.range l, ((g : ℝ) + 1) * c g :=
    Finset.sum_nonneg fun g _ => mul_nonneg (by positivity) (hc0 g)
  have hsplit : ∑ g ∈ Finset.range l, ((g : ℝ) + 1) * c g
      = Kn + ∑ g ∈ Finset.Ico N l, ((g : ℝ) + 1) * c g := by
    rw [hKn, Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le N) hlN).symm
  have htail : ∑ g ∈ Finset.Ico N l, ((g : ℝ) + 1) * c g ≤ (l : ℝ) ^ 2 * (ε / 2) := by
    have hterm : ∀ g ∈ Finset.Ico N l, ((g : ℝ) + 1) * c g ≤ (l : ℝ) * (ε / 2) := by
      intro g hg
      obtain ⟨hgN, hgl⟩ := Finset.mem_Ico.1 hg
      have h1 : ((g : ℝ) + 1) ≤ (l : ℝ) := by
        have : g + 1 ≤ l := hgl
        exact_mod_cast this
      have h2 : c g ≤ ε / 2 := hN g hgN
      have h3 : (0 : ℝ) ≤ (g : ℝ) + 1 := by positivity
      nlinarith [hc0 g]
    calc ∑ g ∈ Finset.Ico N l, ((g : ℝ) + 1) * c g
        ≤ ∑ _g ∈ Finset.Ico N l, (l : ℝ) * (ε / 2) := Finset.sum_le_sum hterm
      _ = ((l - N : ℕ) : ℝ) * ((l : ℝ) * (ε / 2)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (l : ℝ) ^ 2 * (ε / 2) := by
          have hc1 : ((l - N : ℕ) : ℝ) ≤ (l : ℝ) := by
            have : l - N ≤ l := Nat.sub_le _ _
            exact_mod_cast this
          have : (0 : ℝ) ≤ (l : ℝ) * (ε / 2) := by positivity
          nlinarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum0 (by positivity))]
  rw [hsplit, add_div]
  have h2 : (∑ g ∈ Finset.Ico N l, ((g : ℝ) + 1) * c g) / (l : ℝ) ^ 2 ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [htail]
  linarith

/-- **`E S_l⁴ = o(l³)` from `Σ α < ∞` alone.** -/
private theorem m4_tendsto_moment4_div_cube [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    {C : ℝ} (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) :
    Tendsto (fun l : ℕ =>
        (∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 4 ∂μ) / (l : ℝ) ^ 3)
      atTop (𝓝 0) := by
  classical
  have hA0 : ∀ m, 0 ≤ alphaCoeff X μ m := m4_alphaCoeff_nonneg X
  set M : ℝ := ∑' g : ℕ, alphaCoeff X μ g with hMdef
  have hM0 : (0 : ℝ) ≤ M := tsum_nonneg hA0
  have hC4 : (0 : ℝ) ≤ C ^ 4 := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ g : ℕ, c g = ((g : ℝ) + 1) * alphaCoeff X μ g :=
    ⟨_, fun _ => rfl⟩
  have hc0 : ∀ g, 0 ≤ c g := fun g => by rw [hc]; exact mul_nonneg (by positivity) (hA0 g)
  have hclim : Tendsto c atTop (𝓝 0) := by
    have h1 := tendsto_mul_alphaCoeff (X := X) (μ := μ) hα
    have h2 : Tendsto (fun m : ℕ => alphaCoeff X μ m) atTop (𝓝 0) := hα.tendsto_atTop_zero
    have := h1.add h2
    rw [add_zero] at this
    refine this.congr fun m => ?_
    rw [hc]; ring
  have hWeq : ∀ l : ℕ, ∑ g ∈ Finset.range l, alphaCoeff X μ g * ((g : ℝ) + 1) ^ 2
      = ∑ g ∈ Finset.range l, ((g : ℝ) + 1) * c g :=
    fun l => Finset.sum_congr rfl fun g _ => by rw [hc]; ring
  have hces := m4_tendsto_weighted_div_sq hc0 hclim
  have hlim : Tendsto (fun l : ℕ =>
      288 * C ^ 4 * ((∑ g ∈ Finset.range l, ((g : ℝ) + 1) * c g) / (l : ℝ) ^ 2)
        + 384 * C ^ 4 * M ^ 2 * (1 / (l : ℝ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun l : ℕ => (1 : ℝ) / (l : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have := (hces.const_mul (288 * C ^ 4)).add (h2.const_mul (384 * C ^ 4 * M ^ 2))
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun l => ?_) ?_ hlim
  · exact div_nonneg (integral_nonneg fun ω => by positivity) (by positivity)
  filter_upwards [eventually_ge_atTop 1] with l hl
  have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hD := m4_moment4_le hmeas hstat hbdd hmean hα l
  rw [hWeq l] at hD
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (l : ℝ) ^ 3)]
  refine hD.trans (le_of_eq ?_)
  field_simp
  ring

end Moment4Summable


/-- **The adaptive Bernstein block scheme.**  Same seven constraints as
`exists_block_scheme`, plus the **cubic budget** `E S_{l_n}⁴ = o(l_n n)` that the
Lindeberg-free remainder estimate `norm_integral_remainder_cubic_le` consumes.

The big block is `α`-dependent: `l_n = ⌊n/s_n⌋ + 1` with the *small* block
`s_n = ⌊√n⌋/a_n + ⌊√⌊√⌊√n⌋⌋⌋ + 1` and `a_n → ∞` chosen (in `exists_adaptive_small`) so
slowly that `a_n² · sup_{m ≥ ⌊√n⌋/3} η_m → 0`, where `E S_l⁴ = l³ η_l`.  Since
`η_l → 0` by `m4_tendsto_moment4_div_cube`, such an `a_n` exists; and `l_n ≍ √n a_n`,
`s_n ≍ k_n ≍ √n / a_n` keeps every Bernstein constraint. -/
private lemma exists_block_scheme_adaptive [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ) {C : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n)
    (hsumacvf : Summable fun k : ℤ => |acvf X μ k|) :
    ∃ l s k : ℕ → ℕ,
      (∀ n, 1 ≤ s n) ∧ (∀ n, 1 ≤ l n) ∧ (∀ n, k n * (l n + s n) ≤ n) ∧
      Tendsto (fun n : ℕ => (l n : ℝ)) atTop atTop ∧
      Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun n : ℕ => (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => (∫ ω, (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 4 ∂μ)
        / ((l n : ℝ) * (n : ℝ))) atTop (𝓝 0) := by
  classical
  have hC0 : 0 ≤ C := bound_nonneg hbdd
  set Λ : ℝ := ∑' j : ℤ, |acvf X μ j| with hΛdef
  have hΛ0 : 0 ≤ Λ := tsum_nonneg fun _ => abs_nonneg _
  have hSmeas : ∀ D : Finset ℕ, Measurable fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω :=
    fun D => Finset.measurable_sum _ fun t _ => hmeas _
  -- a.e. bound on a partial sum
  have hcoord : ∀ᵐ ω ∂μ, ∀ t : ℕ, |X ((t : ℤ) + 1) ω| ≤ C := by
    rw [ae_all_iff]
    intro t
    exact hbdd _
  have hSbdd : ∀ l : ℕ, ∀ᵐ ω ∂μ, |∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω| ≤ C * (l : ℝ) := by
    intro l
    filter_upwards [hcoord] with ω hω
    calc |∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω|
        ≤ ∑ t ∈ Finset.range l, |X ((t : ℤ) + 1) ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range l, C := Finset.sum_le_sum fun t _ => hω t
      _ = C * (l : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  -- the normalised fourth moment
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, ∀ l : ℕ, η l =
      (∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 4 ∂μ) / (l : ℝ) ^ 3 :=
    ⟨_, fun _ => rfl⟩
  have hη0 : ∀ l, 0 ≤ η l := fun l => by
    rw [hηdef]
    exact div_nonneg (integral_nonneg fun ω => by positivity) (by positivity)
  have hηB : ∀ l, η l ≤ C ^ 2 * Λ := by
    intro l
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      rw [hηdef]
      simp only [Nat.cast_zero]
      rw [show (0 : ℝ) ^ 3 = 0 by ring, div_zero]
      positivity
    · have hl0 : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
      have hint4 : Integrable (fun ω => (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 4) μ := by
        refine m4_integrable_of_bdd ((hSmeas _).pow_const 4) (B := (C * (l : ℝ)) ^ 4) ?_
        filter_upwards [hSbdd l] with ω hω
        have h1 : |(∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 4|
            = |∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω| ^ 4 := by
          rw [abs_pow]
        rw [h1]
        exact pow_le_pow_left₀ (abs_nonneg _) hω 4
      have hint2 : Integrable
          (fun ω => (C * (l : ℝ)) ^ 2 * (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 2) μ := by
        refine m4_integrable_of_bdd (((hSmeas _).pow_const 2).const_mul _)
          (B := (C * (l : ℝ)) ^ 2 * (C * (l : ℝ)) ^ 2) ?_
        filter_upwards [hSbdd l] with ω hω
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C * (l : ℝ)) ^ 2)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω), abs_nonneg
          (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω), hω]
      have h4 : (∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 4 ∂μ)
          ≤ (C * (l : ℝ)) ^ 2 * ∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
        have hmono : (∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 4 ∂μ)
            ≤ ∫ ω, (C * (l : ℝ)) ^ 2 * (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
          refine integral_mono_ae hint4 hint2 ?_
          filter_upwards [hSbdd l] with ω hω
          have hsq : (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 2 ≤ (C * (l : ℝ)) ^ 2 := by
            nlinarith [sq_abs (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω), abs_nonneg
              (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω), hω]
          nlinarith [sq_nonneg (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω)]
        rwa [integral_const_mul] at hmono
      have h2 : (∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) ≤ Λ * (l : ℝ) := by
        have h := integral_sq_partialSum_le hmeas hstat hbdd hmean hsumacvf (Finset.range l)
        rwa [Finset.card_range] at h
      have h20 : (0 : ℝ) ≤ ∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 2 ∂μ :=
        integral_nonneg fun ω => sq_nonneg _
      have hchain : (∫ ω, (∑ t ∈ Finset.range l, X ((t : ℤ) + 1) ω) ^ 4 ∂μ)
          ≤ C ^ 2 * Λ * (l : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (C * (l : ℝ)) ^ 2)
        nlinarith [h4, this]
      rw [hηdef, div_le_iff₀ (by positivity : (0 : ℝ) < (l : ℝ) ^ 3)]
      exact hchain
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h := m4_tendsto_moment4_div_cube hmeas hstat hbdd hmean hα
    exact h.congr fun l => (hηdef l).symm
  obtain ⟨s, hs1, hstop, hsq, hbud⟩ := exists_adaptive_small hη0 hηB hηlim
  obtain ⟨l, k, hldef, hkdef, hl1, hfit, hltop, hln0, hkl, hkα⟩ :=
    exists_block_scheme_of_small hα s hs1 hstop hsq
  refine ⟨l, s, k, hs1, hl1, hfit, hltop, hln0, hkl, hkα, ?_⟩
  refine hbud.congr fun n => ?_
  have hln : n / s n + 1 = l n := (hldef n).symm
  rw [hln, hηdef]
  have hl0 : (0 : ℝ) < (l n : ℝ) := by exact_mod_cast hl1 n
  field_simp

end Bernstein

/-- **FY Theorem 2.21(ii)** (full in-text proof, Bernstein blocks): bounded zero-mean
strictly stationary, summable α, positive long-run variance ⇒ `S_n/√n →d N(0, σ²)`
(charFun form). -/
theorem clt_of_bounded_alphaMixing [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.21(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.21(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n)
    -- USER-INPUT: positive long-run variance; FY Thm 2.21
    (hσ : 0 < acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0
        (Real.toNNReal (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1)))) u)) := by
  classical
  set σ2 : ℝ := acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) with hσ2def
  have hSmeas : ∀ D : Finset ℕ, Measurable fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω :=
    fun D => Finset.measurable_sum _ fun t _ => hmeas _
  -- ### 0. Both sides as explicit integrals
  have hRHS : charFun (gaussianReal 0 (Real.toNNReal σ2)) u
      = Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2)) := by
    rw [charFun_gaussianReal, Real.coe_toNNReal _ hσ.le]
    congr 1
    push_cast
    ring
  have hcf : ∀ n : ℕ, charFun (μ.map fun ω =>
      (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u
      = ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ := by
    intro n
    have hae : AEMeasurable (fun ω => (Real.sqrt n)⁻¹ *
        ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ :=
      (measurable_const.mul (hSmeas _)).aemeasurable
    have hsm : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I))
        (μ.map fun ω => (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    rw [charFun_apply_real, integral_map hae hsm]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    push_cast
    ring
  rw [hRHS]
  simp only [hcf]
  -- ### 1. Block scheme and moment bookkeeping
  obtain ⟨hsumacvf, hrate⟩ := summable_acvf_and_var_rate_of_bounded hmeas hstat hbdd hmean hα
  obtain ⟨l, s, k, hs1, hl1, hfit, hltop, hln0, hkl, hkα, hcub⟩ :=
    exists_block_scheme_adaptive hmeas hstat hbdd hmean hα hsumacvf
  have hkpos : ∀ᶠ n : ℕ in atTop, 0 < k n := by
    filter_upwards [hkl.eventually_const_lt (show (0 : ℝ) < 1 by norm_num)] with n hn
    by_contra hcon
    have hk0 : k n = 0 := by omega
    rw [hk0] at hn
    simp at hn
  set Λ : ℝ := ∑' j : ℤ, |acvf X μ j| with hΛdef
  have hΛ0 : 0 ≤ Λ := tsum_nonneg fun _ => abs_nonneg _
  have hSmem : ∀ (D : Finset ℕ) (q : ℝ≥0∞),
      MemLp (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) q μ := by
    intro D q
    have hfun : (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) = ∑ t ∈ D, X ((t : ℤ) + 1) := by
      funext ω; simp [Finset.sum_apply]
    rw [hfun]
    exact memLp_finset_sum' (μ := μ) D fun t _ => memLp_of_bdd hmeas hbdd _ q
  have hSint : ∀ D : Finset ℕ, Integrable (fun ω => ∑ t ∈ D, X ((t : ℤ) + 1) ω) μ :=
    fun D => (hSmem D 1).integrable le_rfl
  have hSsq : ∀ D : Finset ℕ, Integrable (fun ω => (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) μ :=
    fun D => (hSmem D 2).integrable_sq
  have hS1 : ∀ D : Finset ℕ, ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ∂μ = 0 :=
    integral_partialSum_eq_zero hmeas hstat hbdd hmean
  have hS2 : ∀ D : Finset ℕ, ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ ≤ Λ * (D.card : ℝ) :=
    integral_sq_partialSum_le hmeas hstat hbdd hmean hsumacvf
  have hS2nn : ∀ D : Finset ℕ, 0 ≤ ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ :=
    fun _ => integral_nonneg fun _ => sq_nonneg _
  -- the big-block variance rate
  have hltopN : Tendsto l atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hltop.eventually_ge_atTop (b : ℝ))
    exact ⟨N, fun a ha => by exact_mod_cast hN a ha⟩
  have hblock : Tendsto (fun n : ℕ => ((l n : ℝ))⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2 ∂μ) atTop (𝓝 σ2) := by
    have hv : ∀ m : ℕ, variance (fun ω => ∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) μ
        = ∫ ω, (∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := fun m =>
      variance_of_integral_eq_zero (hSmem _ 2).aestronglyMeasurable.aemeasurable (hS1 _)
    have h := hrate.comp hltopN
    simpa only [Function.comp_def, hv] using h
  -- ### 2. Geometry of the block partition
  have hd : ∀ (n j j' : ℕ), j < j' →
      Disjoint (Finset.Ico (j * (l n + s n)) (j * (l n + s n) + l n))
        (Finset.Ico (j' * (l n + s n)) (j' * (l n + s n) + l n)) := by
    intro n j j' h
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [Finset.mem_Ico] at ha ha'
    have h1 : (j + 1) * (l n + s n) ≤ j' * (l n + s n) := Nat.mul_le_mul_right _ h
    have h2 : (j + 1) * (l n + s n) = j * (l n + s n) + (l n + s n) := by ring
    omega
  have hdisj : ∀ (n : ℕ), ∀ j ∈ Finset.range (k n), ∀ j' ∈ Finset.range (k n), j ≠ j' →
      Disjoint (Finset.Ico (j * (l n + s n)) (j * (l n + s n) + l n))
        (Finset.Ico (j' * (l n + s n)) (j' * (l n + s n) + l n)) := by
    intro n j _ j' _ hne
    rcases Nat.lt_or_ge j j' with h | h
    · exact hd n j j' h
    · exact (hd n j' j (by omega)).symm
  set G : ℕ → Finset ℕ := fun n =>
    (Finset.range (k n)).biUnion fun j =>
      Finset.Ico (j * (l n + s n)) (j * (l n + s n) + l n) with hGdef
  have hGsub : ∀ n, G n ⊆ Finset.range n := by
    intro n a ha
    simp only [hGdef, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico] at ha
    obtain ⟨j, hj, haj⟩ := ha
    have h1 : (j + 1) * (l n + s n) ≤ k n * (l n + s n) := Nat.mul_le_mul_right _ hj
    have h2 : (j + 1) * (l n + s n) = j * (l n + s n) + (l n + s n) := by ring
    have h4 := hfit n
    simp only [Finset.mem_range]
    omega
  have hGcard : ∀ n, (G n).card = k n * l n := by
    intro n
    simp only [hGdef]
    rw [Finset.card_biUnion (hdisj n)]
    simp [Nat.card_Ico, mul_comm]
  have hDcard : ∀ n, ((Finset.range n \ G n).card : ℝ) = (n : ℝ) - ((k n * l n : ℕ) : ℝ) := by
    intro n
    have hc : (Finset.range n \ G n).card + k n * l n = n := by
      have h := Finset.card_sdiff_add_card_eq_card (hGsub n)
      rwa [hGcard, Finset.card_range] at h
    have hcast : ((Finset.range n \ G n).card : ℝ) + ((k n * l n : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) hc
    linarith
  have hsplit : ∀ (n : ℕ) (ω : Ω), ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω
      = (∑ t ∈ G n, X ((t : ℤ) + 1) ω) + ∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω := by
    intro n ω
    rw [add_comm]
    exact (Finset.sum_sdiff (hGsub n)).symm
  have hblocksum : ∀ (n : ℕ) (ω : Ω), ∑ t ∈ G n, X ((t : ℤ) + 1) ω
      = ∑ j ∈ Finset.range (k n), ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + ((j * (l n + s n) : ℕ) : ℤ)) ω := by
    intro n ω
    simp only [hGdef]
    rw [Finset.sum_biUnion (fun j hj j' hj' hne => hdisj n j hj j' hj' hne)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    push_cast
    ring
  -- ### 3. The three characteristic functions
  set Φ : ℕ → ℂ := fun n => ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
      ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ with hΦdef
  set Φ' : ℕ → ℂ := fun n => ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
      ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ with hΦ'def
  set φ : ℕ → ℂ := fun n => ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
      ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ with hφdef
  have hexpint : ∀ (D : Finset ℕ) (v : ℝ), Integrable (fun ω =>
      Complex.exp (((v * ∑ t ∈ D, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)) μ := by
    intro D v
    have hmf : Measurable fun ω =>
        Complex.exp (((v * ∑ t ∈ D, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul (hSmeas D))).mul measurable_const)
    refine MemLp.integrable (q := ⊤) le_top (memLp_top_of_bound hmf.aestronglyMeasurable 1 ?_)
    filter_upwards with ω
    rw [Complex.norm_exp_ofReal_mul_I]
  -- ### 4. Gap A: small blocks + remainder are `L²`-negligible
  have hW : Tendsto (fun n : ℕ =>
      (∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => Λ * (1 - ((k n * l n : ℕ) : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
      have h := (hkl.const_sub 1).const_mul Λ
      simpa using h
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hS2nn _) (Nat.cast_nonneg _))
      ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h1 := hS2 (Finset.range n \ G n)
    rw [hDcard n] at h1
    rw [div_le_iff₀ hn0]
    have he : Λ * (1 - ((k n * l n : ℕ) : ℝ) / (n : ℝ)) * (n : ℝ)
        = Λ * ((n : ℝ) - ((k n * l n : ℕ) : ℝ)) := by field_simp
    rw [he]
    exact h1
  have hA : Tendsto (fun n : ℕ => Φ n - Φ' n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => |u| * Real.sqrt
        ((∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ))
        + 5 * u ^ 2 * ((∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
          / (n : ℝ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.sqrt
          ((∫ ω, (∑ t ∈ Finset.range n \ G n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ)))
          atTop (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp hW
        simpa [Function.comp_def] using h
      have := (h1.const_mul |u|).add (hW.const_mul (5 * u ^ 2))
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsq : Real.sqrt (n : ℝ) > 0 := Real.sqrt_pos.mpr hn0
    set D : Finset ℕ := Finset.range n \ G n with hDdef
    set w : ℝ := u * (Real.sqrt n)⁻¹ with hwdef
    -- pointwise phase-increment bound
    have hpt : ∀ ω : Ω, ‖Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)‖
        ≤ |w * ∑ t ∈ D, X ((t : ℤ) + 1) ω| + 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 := by
      intro ω
      have hreal : u * (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω
          = (u * (Real.sqrt n)⁻¹ * ∑ t ∈ G n, X ((t : ℤ) + 1) ω)
            + w * ∑ t ∈ D, X ((t : ℤ) + 1) ω := by
        rw [hsplit n ω, hwdef]; ring
      have hfac : Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
          - Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
          = Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
            * (Complex.exp (((w * ∑ t ∈ D, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) - 1) := by
        rw [hreal, Complex.ofReal_add, add_mul, Complex.exp_add]
        ring
      rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact norm_expI_sub_one_le _
    have hint : Integrable (fun ω => |w * ∑ t ∈ D, X ((t : ℤ) + 1) ω|
        + 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) μ := by
      refine Integrable.add ((hSint D).const_mul w).abs ?_
      have : Integrable (fun ω => (5 * w ^ 2) * (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) μ :=
        (hSsq D).const_mul _
      refine this.congr (Eventually.of_forall fun ω => ?_)
      ring
    calc ‖Φ n - Φ' n‖
        = ‖∫ ω, (Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)) ∂μ‖ := by
          rw [integral_sub (hexpint _ _) (hexpint _ _)]
      _ ≤ ∫ ω, ‖Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ G n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (|w * ∑ t ∈ D, X ((t : ℤ) + 1) ω|
            + 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2) ∂μ :=
          integral_mono (((hexpint (Finset.range n) _).sub (hexpint (G n) _)).norm) hint hpt
      _ ≤ |u| * Real.sqrt ((∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ))
            + 5 * u ^ 2 * ((∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ)) := by
          have hE2 : 0 ≤ ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := hS2nn D
          have hA1 : ∫ ω, |w * ∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ
              = |w| * ∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ := by
            simp_rw [abs_mul]
            rw [integral_const_mul]
          have hA2 : ∫ ω, 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ
              = 5 * w ^ 2 * ∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ := by
            have hpw : ∀ ω : Ω, 5 * (w * ∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2
                = (5 * w ^ 2) * (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 := fun ω => by ring
            simp_rw [hpw]
            rw [integral_const_mul]
          rw [integral_add ((hSint D).const_mul w).abs
            (((hSsq D).const_mul (5 * w ^ 2)).congr (Eventually.of_forall fun ω => by ring)),
            hA1, hA2]
          have hcs : (∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ)
              ≤ Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) := by
            have h := sq_integral_abs_le (hSmem D 2)
            have hnn : 0 ≤ ∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ :=
              integral_nonneg fun _ => abs_nonneg _
            calc (∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ)
                = Real.sqrt ((∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ) ^ 2) :=
                  (Real.sqrt_sq hnn).symm
              _ ≤ Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) := Real.sqrt_le_sqrt h
          have hw1 : |w| = |u| / Real.sqrt (n : ℝ) := by
            rw [hwdef, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
            ring
          have hw2 : w ^ 2 = u ^ 2 / (n : ℝ) := by
            rw [hwdef, mul_pow, inv_pow, Real.sq_sqrt hn0.le]
            ring
          rw [hw1, hw2, Real.sqrt_div hE2]
          have h1 : |u| / Real.sqrt (n : ℝ) * (∫ ω, |∑ t ∈ D, X ((t : ℤ) + 1) ω| ∂μ)
              ≤ |u| / Real.sqrt (n : ℝ)
                * Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) :=
            mul_le_mul_of_nonneg_left hcs (by positivity)
          have heq1 : |u| / Real.sqrt (n : ℝ)
              * Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
              = |u| * (Real.sqrt (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
                / Real.sqrt (n : ℝ)) := by ring
          have heq2 : 5 * (u ^ 2 / (n : ℝ)) * (∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
              = 5 * u ^ 2 * ((∫ ω, (∑ t ∈ D, X ((t : ℤ) + 1) ω) ^ 2 ∂μ) / (n : ℝ)) := by ring
          linarith
  -- ### 5. Gap B: Volkonskii–Rozanov factorization; identical block laws give a power
  have hB : Tendsto (fun n : ℕ => Φ' n - (φ n) ^ (k n)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 16 * (k n : ℝ) * alphaCoeff X μ (s n)) atTop (𝓝 0) := by
      have h := hkα.const_mul (16 : ℝ)
      simpa [mul_assoc] using h
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hkpos] with n hkn
    have hprod : Φ' n = ∫ ω, ∏ j : Fin (k n), Complex.exp (((u * (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ) : ℂ) * Complex.I) ∂μ := by
      simp only [hΦ'def]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      dsimp only
      rw [hblocksum n ω]
      have hexpo : (((u * (Real.sqrt n)⁻¹ * ∑ j ∈ Finset.range (k n), ∑ i ∈ Finset.range (l n),
            X ((i : ℤ) + 1 + ((j * (l n + s n) : ℕ) : ℤ)) ω : ℝ)) : ℂ) * Complex.I
          = ∑ j : Fin (k n), ((((u * (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range (l n),
            X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ)) : ℂ) * Complex.I) := by
        rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((((u * (Real.sqrt n)⁻¹ *
          ∑ i ∈ Finset.range (l n),
            X ((i : ℤ) + 1 + ((j * (l n + s n) : ℕ) : ℤ)) ω : ℝ)) : ℂ) * Complex.I))]
        push_cast
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [hexpo, Complex.exp_sum]
    have hFmeas : Measurable fun x : ℝ =>
        Complex.exp (((u * (Real.sqrt n)⁻¹ * x : ℝ) : ℂ) * Complex.I) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        (measurable_const.mul measurable_id)).mul measurable_const)
    have hone : ∀ j : Fin (k n), (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        = φ n := fun j =>
      integral_comp_window_eq hmeas hstat hFmeas (l n) (((j : ℕ) * (l n + s n) : ℕ) : ℤ)
    have hfac : ∏ j : Fin (k n), (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
        ∑ i ∈ Finset.range (l n),
          X ((i : ℤ) + 1 + (((j : ℕ) * (l n + s n) : ℕ) : ℤ)) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        = (φ n) ^ (k n) := by
      rw [Finset.prod_congr rfl (fun j _ => hone j), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    rw [hprod, ← hfac]
    refine le_trans (norm_integral_prod_blocks_sub_prod_le hmeas hstat (l n) (s n) hkn
      (u * (Real.sqrt n)⁻¹)) ?_
    have hnn : 0 ≤ alphaCoeff X μ (s n) := alphaMixCoeff_nonneg
    nlinarith [hnn]
  -- ### 6. Gap C: the scalar limit `(φ n)^{k_n} → exp(−σ²u²/2)`, then the three-term squeeze
  --
  -- `φ n = E e^{i v_n B_n}` with `v_n = u n^{-1/2}` and `B_n` one big block; mean zero
  -- kills the linear Taylor term, so `φ n − 1 = −(v_n²/2) E B_n² + R n`. The remainder
  -- is split at the Lindeberg level `ε √n` (cubic bound below, quadratic bound above).
  have hBmeas : ∀ n : ℕ, Measurable fun ω => ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω :=
    fun n => hSmeas _
  have hφn : ∀ n : ℕ, φ n = ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
      ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ := by
    intro n; simp only [hφdef]
  obtain ⟨m2, hm2def⟩ : ∃ m2 : ℕ → ℝ, ∀ n : ℕ, m2 n
      = ∫ ω, (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2 ∂μ := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℕ → ℂ, ∀ n : ℕ, R n = ∫ ω,
      (Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
        - (1 + ((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I
          - ((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω : ℝ) : ℂ) ^ 2 / 2)) ∂μ :=
    ⟨_, fun _ => rfl⟩
  have hm2nn : ∀ n, 0 ≤ m2 n := fun n => by rw [hm2def]; exact hS2nn _
  have hm2le : ∀ n, m2 n ≤ Λ * (l n : ℝ) := fun n => by
    rw [hm2def]
    have h := hS2 (Finset.range (l n))
    rwa [Finset.card_range] at h
  -- (a) the block expansion
  have hexp : ∀ n : ℕ, φ n - 1
      = -((((u * (Real.sqrt n)⁻¹) ^ 2 / 2 * m2 n : ℝ)) : ℂ) + R n := fun n => by
    rw [hφn n, hm2def n, hRdef n]
    exact charFun_block_expand (hBmeas n) (hSmem _ 2) (hS1 _) (u * (Real.sqrt n)⁻¹)
  -- (b) the crude remainder bound (Lindeberg level `0`)
  have hRbd0 : ∀ n : ℕ, ‖R n‖ ≤ 4 * (u * (Real.sqrt n)⁻¹) ^ 2 * m2 n := fun n => by
    rw [hRdef n, hm2def n]
    have h := norm_integral_remainder_le (B := fun ω => ∑ t ∈ Finset.range (l n),
      X ((t : ℤ) + 1) ω) (hBmeas n) (hSmem _ 2) (u * (Real.sqrt n)⁻¹) (T := 0) le_rfl
    have hset : {ω : Ω | (0 : ℝ) ≤ |∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω|} = Set.univ := by
      ext ω; simp [abs_nonneg]
    rw [hset, setIntegral_univ] at h
    simpa using h
  -- (c) `‖φ n − 1‖ ≤ 5 u² Λ (l_n / n)`
  have hzbd : ∀ n : ℕ, 1 ≤ n → ‖φ n - 1‖ ≤ 5 * u ^ 2 * Λ * ((l n : ℝ) / (n : ℝ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hv2 : (u * (Real.sqrt n)⁻¹) ^ 2 = u ^ 2 / (n : ℝ) := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hn0.le]
      ring
    have h4 : (0 : ℝ) ≤ u ^ 2 / (n : ℝ) := by positivity
    have hnorm1 : ‖(-((((u * (Real.sqrt n)⁻¹) ^ 2 / 2 * m2 n : ℝ)) : ℂ))‖
        = u ^ 2 / (n : ℝ) / 2 * m2 n := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, hv2,
        abs_of_nonneg (mul_nonneg (by positivity) (hm2nn n))]
    have h1 : ‖R n‖ ≤ 4 * (u ^ 2 / (n : ℝ)) * m2 n := by
      have h := hRbd0 n; rwa [hv2] at h
    have h2 : ‖φ n - 1‖ ≤ u ^ 2 / (n : ℝ) / 2 * m2 n + 4 * (u ^ 2 / (n : ℝ)) * m2 n := by
      rw [hexp n]
      refine (norm_add_le _ _).trans ?_
      rw [hnorm1]
      linarith
    have h3 : m2 n ≤ Λ * (l n : ℝ) := hm2le n
    have hprod : (0 : ℝ) ≤ u ^ 2 * Λ * ((l n : ℝ) / (n : ℝ)) := by
      refine mul_nonneg (mul_nonneg (sq_nonneg u) hΛ0) ?_
      positivity
    calc ‖φ n - 1‖ ≤ u ^ 2 / (n : ℝ) / 2 * m2 n + 4 * (u ^ 2 / (n : ℝ)) * m2 n := h2
      _ = (9 / 2 * (u ^ 2 / (n : ℝ))) * m2 n := by ring
      _ ≤ (9 / 2 * (u ^ 2 / (n : ℝ))) * (Λ * (l n : ℝ)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 9 / 2 * (u ^ 2 * Λ * ((l n : ℝ) / (n : ℝ))) := by
          field_simp
      _ ≤ 5 * u ^ 2 * Λ * ((l n : ℝ) / (n : ℝ)) := by linarith
  -- (d) `φ n − 1 → 0`
  have hz0 : Tendsto (fun n : ℕ => φ n - 1) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 5 * u ^ 2 * Λ * ((l n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
      simpa using hln0.const_mul (5 * u ^ 2 * Λ)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn using hzbd n hn
  -- (e) `k_n ‖φ n − 1‖² → 0`
  have hkb : Tendsto (fun n : ℕ => (k n : ℝ) * ‖φ n - 1‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => (5 * u ^ 2 * Λ) ^ 2 * (((k n * l n : ℕ) : ℝ) / (n : ℝ))
        * ((l n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
      simpa using (hkl.const_mul ((5 * u ^ 2 * Λ) ^ 2)).mul hln0
    refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have hsq : ‖φ n - 1‖ ^ 2 ≤ (5 * u ^ 2 * Λ * ((l n : ℝ) / (n : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hzbd n hn) 2
    calc (k n : ℝ) * ‖φ n - 1‖ ^ 2
        ≤ (k n : ℝ) * (5 * u ^ 2 * Λ * ((l n : ℝ) / (n : ℝ))) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)
      _ = (5 * u ^ 2 * Λ) ^ 2 * (((k n * l n : ℕ) : ℝ) / (n : ℝ)) * ((l n : ℝ) / (n : ℝ)) := by
          push_cast
          field_simp
  -- (f) `k_n E B_n² / n → σ²`
  have hkm2 : Tendsto (fun n : ℕ => (k n : ℝ) * m2 n / (n : ℝ)) atTop (𝓝 σ2) := by
    have hblock' : Tendsto (fun n : ℕ => ((l n : ℝ))⁻¹ * m2 n) atTop (𝓝 σ2) := by
      simpa only [hm2def] using hblock
    have hprod : Tendsto (fun n : ℕ => ((k n * l n : ℕ) : ℝ) / (n : ℝ)
        * (((l n : ℝ))⁻¹ * m2 n)) atTop (𝓝 (1 * σ2)) := hkl.mul hblock'
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hl0 : (0 : ℝ) < (l n : ℝ) := by exact_mod_cast hl1 n
    have hlne : (l n : ℝ) ≠ 0 := ne_of_gt hl0
    push_cast
    field_simp
  -- (g) the **cubic** remainder limit `k_n ‖R n‖ → 0` (no Lindeberg split, no uniform
  -- integrability): the global cubic Taylor bound gives
  -- `‖R n‖ ≤ 4 |v_n|³ √(E B_n² · E B_n⁴)`, and the adaptive scheme's budget
  -- `E B_n⁴ = o(l_n n)` turns `k_n ≤ n/l_n`, `E B_n² ≤ Λ l_n` into
  -- `k_n ‖R n‖ ≤ 4 |u|³ √(Λ · E B_n⁴/(l_n n)) → 0`.
  have hSbdd : ∀ m : ℕ, ∀ᵐ ω ∂μ, |∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω| ≤ C * (m : ℝ) := by
    have hcoord : ∀ᵐ ω ∂μ, ∀ t : ℕ, |X ((t : ℤ) + 1) ω| ≤ C := by
      rw [ae_all_iff]
      intro t
      exact hbdd _
    intro m
    filter_upwards [hcoord] with ω hω
    calc |∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω|
        ≤ ∑ t ∈ Finset.range m, |X ((t : ℤ) + 1) ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range m, C := Finset.sum_le_sum fun t _ => hω t
      _ = C * (m : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  obtain ⟨m4, hm4def⟩ : ∃ m4 : ℕ → ℝ, ∀ n : ℕ, m4 n
      = ∫ ω, (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 4 ∂μ := ⟨_, fun _ => rfl⟩
  have hm4nn : ∀ n, 0 ≤ m4 n := fun n => by
    rw [hm4def]
    exact integral_nonneg fun ω => by positivity
  have hkR : Tendsto (fun n : ℕ => (k n : ℝ) * ‖R n‖) atTop (𝓝 0) := by
    have hQ : Tendsto (fun n : ℕ => m4 n / ((l n : ℝ) * (n : ℝ))) atTop (𝓝 0) := by
      simpa only [hm4def] using hcub
    have hlim : Tendsto (fun n : ℕ =>
        4 * |u| ^ 3 * Real.sqrt (Λ * (m4 n / ((l n : ℝ) * (n : ℝ))))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Λ * (m4 n / ((l n : ℝ) * (n : ℝ)))) atTop (𝓝 0) := by
        simpa using hQ.const_mul Λ
      have h2 : Tendsto (fun n : ℕ =>
          Real.sqrt (Λ * (m4 n / ((l n : ℝ) * (n : ℝ))))) atTop (𝓝 0) := by
        have h3 := (Real.continuous_sqrt.tendsto 0).comp h1
        simpa [Function.comp_def] using h3
      simpa using h2.const_mul (4 * |u| ^ 3)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hl0 : (0 : ℝ) < (l n : ℝ) := by exact_mod_cast hl1 n
    have hk0 : (0 : ℝ) ≤ (k n : ℝ) := Nat.cast_nonneg _
    have hcube := norm_integral_remainder_cubic_le
      (B := fun ω => ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω)
      (hBmeas n) (hSbdd (l n)) (u * (Real.sqrt n)⁻¹)
    rw [← hRdef n, ← hm2def n, ← hm4def n] at hcube
    have habs : |u * (Real.sqrt (n : ℝ))⁻¹| ^ 3
        = |u| ^ 3 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
      have h3 : (Real.sqrt (n : ℝ)) ^ 3 = (n : ℝ) * Real.sqrt (n : ℝ) := by
        rw [pow_succ, Real.sq_sqrt hn0.le]
      rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, h3]
      field_simp
    rw [habs] at hcube
    have hsq1 : Real.sqrt (m2 n * m4 n) ≤ Real.sqrt (Λ * (l n : ℝ) * m4 n) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hm2le n) (hm4nn n))
    have hkle : (k n : ℝ) ≤ (n : ℝ) / (l n : ℝ) := by
      rw [le_div_iff₀ hl0]
      have h1 : k n * l n ≤ n :=
        le_trans (Nat.mul_le_mul_left (k n) (Nat.le_add_right (l n) (s n))) (hfit n)
      exact_mod_cast h1
    have hsq2 : Real.sqrt (Λ * (l n : ℝ) * m4 n)
        = Real.sqrt (Λ * (m4 n / ((l n : ℝ) * (n : ℝ)))) * (Real.sqrt (n : ℝ) * (l n : ℝ)) := by
      have he : Λ * (l n : ℝ) * m4 n
          = (Λ * (m4 n / ((l n : ℝ) * (n : ℝ)))) * ((n : ℝ) * (l n : ℝ) ^ 2) := by
        field_simp
      have hnn : (0 : ℝ) ≤ Λ * (m4 n / ((l n : ℝ) * (n : ℝ))) := by
        refine mul_nonneg hΛ0 (div_nonneg (hm4nn n) (by positivity))
      rw [he, Real.sqrt_mul hnn, Real.sqrt_mul hn0.le, Real.sqrt_sq hl0.le]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk0 (norm_nonneg _))]
    calc (k n : ℝ) * ‖R n‖
        ≤ ((n : ℝ) / (l n : ℝ))
            * (4 * (|u| ^ 3 / ((n : ℝ) * Real.sqrt (n : ℝ)))
              * Real.sqrt (Λ * (l n : ℝ) * m4 n)) := by
          refine mul_le_mul hkle (hcube.trans ?_) (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hsq1 (by positivity)
      _ = 4 * |u| ^ 3 * Real.sqrt (Λ * (m4 n / ((l n : ℝ) * (n : ℝ)))) := by
          rw [hsq2]
          field_simp
  -- (h) `k_n (φ n − 1) → −σ²u²/2`
  have hkz : Tendsto (fun n : ℕ => (k n : ℂ) * (φ n - 1)) atTop
      (𝓝 (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2))) := by
    have hmain : Tendsto (fun n : ℕ => (-(((u ^ 2 / 2) * ((k n : ℝ) * m2 n / (n : ℝ)) : ℝ) : ℂ)))
        atTop (𝓝 (-(((u ^ 2 / 2) * σ2 : ℝ) : ℂ))) :=
      (((Complex.continuous_ofReal.tendsto _).comp (hkm2.const_mul (u ^ 2 / 2)))).neg
    have hrem : Tendsto (fun n : ℕ => (k n : ℂ) * R n) atTop (𝓝 0) := by
      refine squeeze_zero_norm ?_ hkR
      intro n
      rw [norm_mul, Complex.norm_natCast]
    have hsum := hmain.add hrem
    rw [add_zero] at hsum
    have heqlim : (-(((u ^ 2 / 2) * σ2 : ℝ) : ℂ)) = -((σ2 : ℂ) * (u : ℂ) ^ 2 / 2) := by
      push_cast
      ring
    rw [heqlim] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hv2 : (u * (Real.sqrt (n : ℝ))⁻¹) ^ 2 = u ^ 2 / (n : ℝ) := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hn0.le]
      ring
    have hne : (n : ℝ) ≠ 0 := ne_of_gt hn0
    rw [hexp n, hv2]
    push_cast
    field_simp
  -- (i) the power
  have hpow : Tendsto (fun n : ℕ => (φ n) ^ (k n)) atTop
      (𝓝 (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2)))) := by
    have hz1 : ∀ n : ℕ, ‖1 + (φ n - 1)‖ ≤ 1 := by
      intro n
      have hfold : (1 : ℂ) + (φ n - 1) = φ n := by ring
      rw [hfold, hφn n]
      refine (norm_integral_le_integral_norm _).trans ?_
      have hpt : ∀ ω : Ω, ‖Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)‖ = 1 :=
        fun ω => Complex.norm_exp_ofReal_mul_I _
      simp only [hpt]
      simp
    have hzre : ∀ n : ℕ, (φ n - 1).re ≤ 0 := by
      intro n
      have h := hz1 n
      have hfold : (1 : ℂ) + (φ n - 1) = φ n := by ring
      rw [hfold] at h
      have h2 : (φ n).re ≤ ‖φ n‖ := Complex.re_le_norm _
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    refine (tendsto_pow_of_tendsto_mul hz1 hzre hz0 hkz hkb).congr fun n => ?_
    congr 1
    ring
  -- (j) the three-term squeeze
  have hfin := (hA.add hB).add hpow
  rw [zero_add, zero_add] at hfin
  refine hfin.congr fun n => ?_
  ring

/-! ### The Lindeberg-level debt, closed as a corollary of Theorem 2.21(ii)

The statement `lindeberg_blocks_debt` below is *asymptotic uniform integrability of the
normalised block squares* `Y_l = S_l²/l` — see its docstring for why that is **equivalent
to** Theorem 2.21(ii) and hence unreachable from the local moment toolbox. Now that
2.21(ii) is proved (the cubic/adaptive route), the equivalence can be run in the other
direction, and that is what the two bricks here do: `tail_le_sub_min` is the elementary
inequality `∫_{Y ≥ 2c} Y ≤ 2 (E Y − E (Y ∧ c))` for `Y ≥ 0`, and `exists_tail_threshold`
feeds it the two limits the CLT and the variance rate supply (`E Y_l → σ²` and, by Lévy
continuity, `E (Y_l ∧ c) → E (σ²Z² ∧ c)`) to produce a threshold that works
**uniformly in `l`**. -/

/-- **A tail integral bounded by a truncation defect.** For `Y ≥ 0` integrable and `c > 0`,
`∫_{2c ≤ Y} Y ≤ 2 (E Y − E (Y ∧ c))`: on `{Y ≥ 2c}` one has `Y ≤ 2 (Y − c) = 2(Y − Y ∧ c)`,
and the integrand `2 (Y − Y ∧ c)` is nonnegative everywhere, so the set integral is at most
the full one. -/
private lemma tail_le_sub_min [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hYm : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hYi : Integrable Y μ) {c : ℝ} (hc : 0 < c) :
    ∫ ω in {ω | 2 * c ≤ Y ω}, Y ω ∂μ ≤ 2 * ((∫ ω, Y ω ∂μ) - ∫ ω, min (Y ω) c ∂μ) := by
  have hmini : Integrable (fun ω => min (Y ω) c) μ := by
    refine hYi.mono ((hYm.min measurable_const).aestronglyMeasurable) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_min (hY0 ω) hc.le),
      abs_of_nonneg (hY0 ω)]
    exact min_le_left _ _
  have hA : MeasurableSet {ω | 2 * c ≤ Y ω} := measurableSet_le measurable_const hYm
  have hg0 : (0 : Ω → ℝ) ≤ᵐ[μ] fun ω => 2 * (Y ω - min (Y ω) c) := by
    filter_upwards with ω
    have h := min_le_left (Y ω) c
    simp only [Pi.zero_apply]
    linarith
  have hgi : Integrable (fun ω => 2 * (Y ω - min (Y ω) c)) μ := (hYi.sub hmini).const_mul 2
  have h1 : ∫ ω in {ω | 2 * c ≤ Y ω}, Y ω ∂μ
      ≤ ∫ ω in {ω | 2 * c ≤ Y ω}, 2 * (Y ω - min (Y ω) c) ∂μ := by
    refine setIntegral_mono_on hYi.integrableOn hgi.integrableOn hA ?_
    intro ω hω
    have hω' : 2 * c ≤ Y ω := hω
    have hmin : min (Y ω) c = c := min_eq_right (by linarith)
    rw [hmin]
    linarith
  have h2 : ∫ ω in {ω | 2 * c ≤ Y ω}, 2 * (Y ω - min (Y ω) c) ∂μ
      ≤ ∫ ω, 2 * (Y ω - min (Y ω) c) ∂μ := setIntegral_le_integral hgi hg0
  have h3 : ∫ ω, 2 * (Y ω - min (Y ω) c) ∂μ
      = 2 * ((∫ ω, Y ω ∂μ) - ∫ ω, min (Y ω) c ∂μ) := by
    have e1 : ∫ ω, 2 * (Y ω - min (Y ω) c) ∂μ = 2 * ∫ ω, (Y ω - min (Y ω) c) ∂μ :=
      integral_const_mul _ _
    rw [e1, integral_sub hYi hmini]
  linarith

/-- **Uniform integrability of the normalised block squares `S_m²/m`.** For every `δ > 0`
there is a level `K` such that, at **every** block length `m ≥ 1` and every threshold
`T ≥ K m`, `∫_{S_m² ≥ T} S_m² ≤ δ m`.

Route. Write `Y_m = S_m²/m`. Theorem 2.20(ii) gives `E Y_m → σ²`. If `σ² = 0` the bound is
immediate from `∫_{A} Y_m ≤ E Y_m`. If `σ² > 0`, Theorem 2.21(ii) gives `S_m/√m →d N(0,σ²)`
in characteristic-function form, hence — by Lévy continuity
(`ProbabilityMeasure.tendsto_of_tendsto_charFun`) — weakly, so
`E (Y_m ∧ c) = E h_c(S_m/√m) → ∫ (x² ∧ c) dN(0,σ²)` for the bounded continuous
`h_c(x) = x² ∧ c`; and `∫ (x² ∧ c) dN(0,σ²) ↑ σ²` by dominated convergence. Feeding
`tail_le_sub_min` a `c` with `σ² − ∫(x² ∧ c) < δ/4` gives the bound for all large `m`.
The finitely many small `m` are absorbed by raising `K` above `C² M₀`, since `|S_m| ≤ C m`
makes the event `{S_m² ≥ K m}` null there. -/
private lemma exists_tail_threshold [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ) {C : ℝ}
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C) (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m → ∀ T : ℝ, K * m ≤ T →
      ∫ ω in {ω | T ≤ (∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) ^ 2},
        (∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) ^ 2 ∂μ ≤ δ * m := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Ω → ℝ,
      ∀ m : ℕ, S m = fun ω => ∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω := ⟨_, fun _ => rfl⟩
  have hSapp : ∀ (m : ℕ) (ω : Ω), S m ω = ∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω := by
    intro m ω; rw [hS]
  simp only [← hSapp]
  have hC0 : 0 ≤ C := bound_nonneg hbdd
  have hSmeas : ∀ m, Measurable (S m) := by
    intro m; rw [hS]; exact Finset.measurable_sum _ fun t _ => hmeas _
  have hcoord : ∀ᵐ ω ∂μ, ∀ t : ℕ, |X ((t : ℤ) + 1) ω| ≤ C := by
    rw [ae_all_iff]; intro t; exact hbdd _
  have hSbdd : ∀ m : ℕ, ∀ᵐ ω ∂μ, |S m ω| ≤ C * (m : ℝ) := by
    intro m
    filter_upwards [hcoord] with ω hω
    rw [hSapp]
    calc |∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω|
        ≤ ∑ t ∈ Finset.range m, |X ((t : ℤ) + 1) ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range m, C := Finset.sum_le_sum fun t _ => hω t
      _ = C * (m : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hSmem : ∀ m : ℕ, MemLp (S m) 2 μ := by
    intro m
    refine MemLp.mono_exponent
      (memLp_top_of_bound (hSmeas m).aestronglyMeasurable (C * (m : ℝ)) ?_) le_top
    filter_upwards [hSbdd m] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hSsq : ∀ m, Integrable (fun ω => (S m ω) ^ 2) μ := fun m => (hSmem m).integrable_sq
  have hSsq0 : ∀ m, 0 ≤ ∫ ω, (S m ω) ^ 2 ∂μ := fun m =>
    integral_nonneg fun ω => sq_nonneg _
  have hSint0 : ∀ m : ℕ, ∫ ω, S m ω ∂μ = 0 := by
    intro m
    simp only [hSapp]
    exact integral_partialSum_eq_zero hmeas hstat hbdd hmean (Finset.range m)
  obtain ⟨σ2, hσ2def⟩ : ∃ s : ℝ, s = acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) :=
    ⟨_, rfl⟩
  have hvr := summable_acvf_and_var_rate_of_bounded hmeas hstat hbdd hmean hα
  have hvareq : ∀ m : ℕ, variance (fun ω => ∑ t ∈ Finset.range m, X ((t : ℤ) + 1) ω) μ
      = ∫ ω, (S m ω) ^ 2 ∂μ := by
    intro m
    rw [← hS m, variance_of_integral_eq_zero (hSmeas m).aemeasurable (hSint0 m)]
  have hEY : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * ∫ ω, (S m ω) ^ 2 ∂μ) atTop (𝓝 σ2) := by
    rw [hσ2def]
    exact hvr.2.congr fun m => by rw [hvareq m]
  have hσ0 : 0 ≤ σ2 :=
    ge_of_tendsto' hEY fun m => mul_nonneg (by positivity) (hSsq0 m)
  -- the uniform statement for large `m`
  have hmain : ∃ (K0 : ℝ) (M0 : ℕ), 0 < K0 ∧ 1 ≤ M0 ∧ ∀ m : ℕ, M0 ≤ m →
      ∫ ω in {ω | K0 * (m : ℝ) ≤ (S m ω) ^ 2}, (S m ω) ^ 2 ∂μ ≤ δ * m := by
    rcases eq_or_lt_of_le hσ0 with hz | hpos
    · -- degenerate long-run variance: the whole second moment is eventually small
      have hlim : Tendsto (fun m : ℕ => (m : ℝ)⁻¹ * ∫ ω, (S m ω) ^ 2 ∂μ) atTop (𝓝 0) := by
        rw [← hz] at hEY; exact hEY
      obtain ⟨M0, hM0⟩ := eventually_atTop.1
        ((hlim.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop 1))
      refine ⟨1, max M0 1, one_pos, le_max_right _ _, fun m hm => ?_⟩
      obtain ⟨hm1, hm2⟩ := hM0 m (le_trans (le_max_left _ _) hm)
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm2
      calc ∫ ω in {ω | (1 : ℝ) * (m : ℝ) ≤ (S m ω) ^ 2}, (S m ω) ^ 2 ∂μ
          ≤ ∫ ω, (S m ω) ^ 2 ∂μ :=
            setIntegral_le_integral (hSsq m) (Eventually.of_forall fun ω => sq_nonneg _)
        _ ≤ δ * m := by
            have h := (mul_lt_mul_of_pos_right hm1 hmpos).le
            have h3 : ((m : ℝ)⁻¹ * ∫ ω, (S m ω) ^ 2 ∂μ) * (m : ℝ)
                = ∫ ω, (S m ω) ^ 2 ∂μ := by field_simp
            linarith [h, h3]
    · -- the non-degenerate case: Lévy + the truncated Gaussian second moment
      have hpos' : 0 < acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) := by
        rw [← hσ2def]; exact hpos
      have hclt := clt_of_bounded_alphaMixing hmeas hstat hbdd hmean hα hpos'
      have hmapmeas : ∀ m : ℕ, AEMeasurable (fun ω => (Real.sqrt m)⁻¹ * S m ω) μ :=
        fun m => (measurable_const.mul (hSmeas m)).aemeasurable
      obtain ⟨P, hP⟩ : ∃ P : ℕ → ProbabilityMeasure ℝ, ∀ m : ℕ,
          (P m : Measure ℝ) = μ.map (fun ω => (Real.sqrt m)⁻¹ * S m ω) :=
        ⟨fun m => ⟨μ.map (fun ω => (Real.sqrt m)⁻¹ * S m ω),
          Measure.isProbabilityMeasure_map (hmapmeas m)⟩, fun _ => rfl⟩
      obtain ⟨P0, hP0⟩ : ∃ P0 : ProbabilityMeasure ℝ,
          (P0 : Measure ℝ) = gaussianReal 0 (Real.toNNReal σ2) :=
        ⟨⟨gaussianReal 0 (Real.toNNReal σ2), inferInstance⟩, rfl⟩
      have hweak : Tendsto P atTop (𝓝 P0) := by
        refine ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
        intro u
        simp only [hP, hP0]
        have := hclt u
        rw [hσ2def]
        simpa only [hS] using this
      -- convergence of the truncated normalised squares
      have hmin_conv : ∀ c : ℝ, 0 ≤ c →
          Tendsto (fun m : ℕ => ∫ ω, min ((m : ℝ)⁻¹ * (S m ω) ^ 2) c ∂μ) atTop
            (𝓝 (∫ x : ℝ, min (x ^ 2) c ∂(gaussianReal 0 (Real.toNNReal σ2)))) := by
        intro c hc0
        have hcont : Continuous fun x : ℝ => min (x ^ 2) c :=
          (continuous_pow 2).min continuous_const
        obtain ⟨f, hf⟩ : ∃ f : BoundedContinuousFunction ℝ ℝ, ∀ x, f x = min (x ^ 2) c :=
          ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ℝ => min (x ^ 2) c) hcont c
            (fun x => by
              rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg x) hc0)]
              exact min_le_right _ _), fun _ => rfl⟩
        have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hweak) f
        simp only [hP, hP0] at h
        have hR : ∫ x : ℝ, f x ∂(gaussianReal 0 (Real.toNNReal σ2))
            = ∫ x : ℝ, min (x ^ 2) c ∂(gaussianReal 0 (Real.toNNReal σ2)) := by
          exact integral_congr_ae (Eventually.of_forall fun x => hf x)
        rw [hR] at h
        refine h.congr fun m => ?_
        rw [integral_map (hmapmeas m) f.continuous.aestronglyMeasurable]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [hf]
        congr 1
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
        rw [mul_pow, inv_pow, Real.sq_sqrt hm0]
      -- the truncated Gaussian second moment increases to `σ²`
      have hgauss : Tendsto (fun j : ℕ =>
          ∫ x : ℝ, min (x ^ 2) (j : ℝ) ∂(gaussianReal 0 (Real.toNNReal σ2))) atTop (𝓝 σ2) := by
        have hintb : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (Real.toNNReal σ2)) := by
          simpa using (memLp_id_gaussianReal' (μ := 0) (v := Real.toNNReal σ2) 2
            (by simp)).integrable_sq
        have hI : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (Real.toNNReal σ2)) = σ2 := by
          have h1 : Var[fun x : ℝ => x; gaussianReal 0 (Real.toNNReal σ2)]
              = (Real.toNNReal σ2 : ℝ) := variance_fun_id_gaussianReal
          rw [variance_of_integral_eq_zero (X := fun x : ℝ => x) measurable_id.aemeasurable
            (integral_id_gaussianReal (μ := 0) (v := Real.toNNReal σ2))] at h1
          rw [h1, Real.coe_toNNReal _ hσ0]
        have hdom : Tendsto (fun j : ℕ =>
            ∫ x : ℝ, min (x ^ 2) (j : ℝ) ∂(gaussianReal 0 (Real.toNNReal σ2))) atTop
            (𝓝 (∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 (Real.toNNReal σ2)))) := by
          refine tendsto_integral_of_dominated_convergence (fun x : ℝ => x ^ 2)
            (fun j => ((continuous_pow 2).min continuous_const).aestronglyMeasurable) hintb
            (fun j => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
          · rw [Real.norm_eq_abs, abs_of_nonneg (le_min (sq_nonneg x) (by positivity))]
            exact min_le_left _ _
          · have hev : (fun j : ℕ => min (x ^ 2) (j : ℝ)) =ᶠ[atTop] fun _ : ℕ => x ^ 2 := by
              filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (x ^ 2)] with j hj
              exact min_eq_left hj
            exact tendsto_const_nhds.congr' hev.symm
        rw [hI] at hdom
        exact hdom
      -- choose the truncation level
      obtain ⟨j, hj1, hjδ⟩ : ∃ j : ℕ, 1 ≤ j ∧
          σ2 - δ / 4 < ∫ x : ℝ, min (x ^ 2) (j : ℝ) ∂(gaussianReal 0 (Real.toNNReal σ2)) := by
        obtain ⟨j, hj⟩ := ((hgauss.eventually (lt_mem_nhds (show σ2 - δ / 4 < σ2 by linarith))).and
          (eventually_ge_atTop 1)).exists
        exact ⟨j, hj.2, hj.1⟩
      have hcpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
      have hdiff : Tendsto (fun m : ℕ => 2 * (((m : ℝ)⁻¹ * ∫ ω, (S m ω) ^ 2 ∂μ)
            - ∫ ω, min ((m : ℝ)⁻¹ * (S m ω) ^ 2) (j : ℝ) ∂μ)) atTop
          (𝓝 (2 * (σ2 - ∫ x : ℝ, min (x ^ 2) (j : ℝ)
            ∂(gaussianReal 0 (Real.toNNReal σ2))))) :=
        ((hEY.sub (hmin_conv (j : ℝ) hcpos.le)).const_mul 2)
      have hlt : 2 * (σ2 - ∫ x : ℝ, min (x ^ 2) (j : ℝ)
          ∂(gaussianReal 0 (Real.toNNReal σ2))) < δ := by linarith
      obtain ⟨M0, hM0⟩ := eventually_atTop.1
        ((hdiff.eventually (gt_mem_nhds hlt)).and (eventually_ge_atTop 1))
      refine ⟨2 * (j : ℝ), max M0 1, by positivity, le_max_right _ _, fun m hm => ?_⟩
      obtain ⟨hm1, hm2⟩ := hM0 m (le_trans (le_max_left _ _) hm)
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm2
      have hmne : ((m : ℝ)) ≠ 0 := ne_of_gt hmpos
      have hY := tail_le_sub_min (μ := μ) (Y := fun ω => (m : ℝ)⁻¹ * (S m ω) ^ 2)
        (measurable_const.mul ((hSmeas m).pow_const 2)) (fun ω => by positivity)
        ((hSsq m).const_mul _) hcpos
      have hset : {ω | 2 * (j : ℝ) ≤ (m : ℝ)⁻¹ * (S m ω) ^ 2}
          = {ω | 2 * (j : ℝ) * (m : ℝ) ≤ (S m ω) ^ 2} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h
          have h2 := mul_le_mul_of_nonneg_right h hmpos.le
          have h3 : (m : ℝ)⁻¹ * (S m ω) ^ 2 * (m : ℝ) = (S m ω) ^ 2 := by field_simp
          linarith [h2, h3]
        · intro h
          have h2 := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hmpos.le)
          have h3 : (m : ℝ)⁻¹ * (2 * (j : ℝ) * (m : ℝ)) = 2 * (j : ℝ) := by field_simp
          linarith [h2, h3]
      rw [hset] at hY
      have hsplit : ∫ ω in {ω | 2 * (j : ℝ) * (m : ℝ) ≤ (S m ω) ^ 2},
            (m : ℝ)⁻¹ * (S m ω) ^ 2 ∂μ
          = (m : ℝ)⁻¹ * ∫ ω in {ω | 2 * (j : ℝ) * (m : ℝ) ≤ (S m ω) ^ 2}, (S m ω) ^ 2 ∂μ :=
        integral_const_mul _ _
      rw [hsplit] at hY
      have hEfun : ∫ ω, (m : ℝ)⁻¹ * (S m ω) ^ 2 ∂μ = (m : ℝ)⁻¹ * ∫ ω, (S m ω) ^ 2 ∂μ :=
        integral_const_mul _ _
      rw [hEfun] at hY
      have hfinal : (m : ℝ)⁻¹ * ∫ ω in {ω | 2 * (j : ℝ) * (m : ℝ) ≤ (S m ω) ^ 2},
          (S m ω) ^ 2 ∂μ ≤ δ := le_trans hY hm1.le
      have h4 := mul_le_mul_of_nonneg_right hfinal hmpos.le
      have h5 : ((m : ℝ)⁻¹ * ∫ ω in {ω | 2 * (j : ℝ) * (m : ℝ) ≤ (S m ω) ^ 2},
            (S m ω) ^ 2 ∂μ) * (m : ℝ)
          = ∫ ω in {ω | 2 * (j : ℝ) * (m : ℝ) ≤ (S m ω) ^ 2}, (S m ω) ^ 2 ∂μ := by
        field_simp
      linarith [h4, h5]
  -- assemble: raise the threshold above the trivial bound for the small `m`
  obtain ⟨K0, M0, hK0, hM01, hbig⟩ := hmain
  refine ⟨max K0 (C ^ 2 * M0 + 1), lt_of_lt_of_le hK0 (le_max_left _ _), fun m hm1 T hT => ?_⟩
  have hm1' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  by_cases hm : M0 ≤ m
  · have hsub : {ω | T ≤ (S m ω) ^ 2} ⊆ {ω | K0 * (m : ℝ) ≤ (S m ω) ^ 2} := by
      intro ω hω
      have h1 : K0 * (m : ℝ) ≤ max K0 (C ^ 2 * M0 + 1) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hmpos.le
      exact le_trans (le_trans h1 hT) hω
    calc ∫ ω in {ω | T ≤ (S m ω) ^ 2}, (S m ω) ^ 2 ∂μ
        ≤ ∫ ω in {ω | K0 * (m : ℝ) ≤ (S m ω) ^ 2}, (S m ω) ^ 2 ∂μ :=
          setIntegral_mono_set ((hSsq m).integrableOn)
            (Eventually.of_forall fun ω => sq_nonneg _) (Eventually.of_forall hsub)
      _ ≤ δ * m := hbig m hm
  · -- `m < M0`: the level `T` is above the a.s. bound on `S_m²`
    rw [not_le] at hm
    have hae : ∀ᵐ ω ∂μ, (S m ω) ^ 2 < T := by
      filter_upwards [hSbdd m] with ω hω
      have hsq : (S m ω) ^ 2 ≤ (C * (m : ℝ)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hω 2
      have hmM : (m : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hm.le
      have h1 : (C * (m : ℝ)) ^ 2 ≤ C ^ 2 * (M0 : ℝ) * (m : ℝ) := by nlinarith [sq_nonneg C]
      have h2 : C ^ 2 * (M0 : ℝ) * (m : ℝ) < (C ^ 2 * M0 + 1) * (m : ℝ) := by nlinarith
      have h3 : (C ^ 2 * M0 + 1) * (m : ℝ) ≤ max K0 (C ^ 2 * M0 + 1) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hmpos.le
      linarith
    have hnull : μ {ω | T ≤ (S m ω) ^ 2} = 0 := by
      have h := ae_iff.1 hae
      simpa only [not_lt] using h
    rw [setIntegral_measure_zero _ hnull]
    positivity

/-- **FORMER NAMED PRIVATE DEBT — now PROVED** (Ibragimov–Linnik, *Independent and
Stationary Sequences of Random Variables*, 1971, Theorem 18.5.3; the technical lemma
behind FY Theorem 2.21(ii)).

Under `|X| ≤ C`, strict stationarity, zero mean and `Σ α(j) < ∞`, the normalised block
sums `S_l²/l` are **uniformly integrable**, so the Lindeberg mass at a level `ε√n` with
`l_n/n → 0` vanishes.

**STATUS (wave `ts/s10`): PROVED, as a corollary of Theorem 2.21(ii).** Nothing depends on
it — `clt_of_bounded_alphaMixing` (2.21(ii)) and `clt_of_alphaMixing_debt` (2.21(i)) were
closed in wave `ts/s5b` by the cubic/adaptive-block route, which bypasses the Lindeberg
split entirely. The analysis below (retained) explains why that route does **not** deliver
this statement, and why the only way to close it is to run the equivalence backwards, from
the finished CLT. That is what `exists_tail_threshold` above does.

**The statement is exactly asymptotic uniform integrability of `S_l²/l`** — *not* something
weaker. In the variable `Y_l = S_l²/l` the Lindeberg level `ε√n` is the threshold
`K_n = ε² n / l_n`, and `l_n/n → 0` says precisely `K_n → ∞`; conversely every sequence
`K_n → ∞` is realised by the admissible choice `l_n = ⌈ε² n / K_n⌉`. So quantifying over all
`l` with `l_n/n → 0` is quantifying over all thresholds, i.e.
`lim_{K→∞} sup_l ∫_{S_l²/l ≥ K} S_l²/l = 0`. (Note `sup_l`, not `limsup_l`: the frozen
statement allows a *bounded* `l_n` — e.g. `l ≡ 1` — so the uniformity must be over **all**
`l ≥ 1`, which is why `exists_tail_threshold` absorbs the small block lengths separately
through the a.s. bound `|S_m| ≤ C m`.)

**Consequently the debt is *equivalent* to the theorem it serves, not a weaker ingredient
— which is exactly why the cubic/adaptive route cannot close it.** That route proves the
CLT; it does not produce this uniform-integrability statement as a by-product. Concretely,
the best the fourth moment gives here is
`l_n⁻¹ ∫_{|S_{l_n}| ≥ ε√n} S_{l_n}² ≤ E S_{l_n}⁴/(ε² l_n n) = l_n² η_{l_n}/(ε² n)`, and
`l_n/n → 0` alone does **not** force `l_n² η_{l_n} = o(n)`: take `l_n = n/log n` and an `η`
tending to `0` slowly (`η_l ≍ 1/log² l` is realised by `α(g) ≍ (g log² g)⁻¹`), and the
right-hand side diverges. The *adaptive* `l_n` is admissible for the CLT precisely because
the CLT gets to choose `l_n`; this lemma quantifies over **every** admissible `l_n`.

**What closes it** (executed here): `S_l/√l →d N(0, σ²)` (Theorem 2.21(ii)) together with
`E S_l²/l → σ²` (Theorem 2.20(ii)) makes `Y_l = S_l²/l` a nonnegative sequence converging
in distribution with converging means, hence uniformly integrable — via
`∫_{Y ≥ 2c} Y ≤ 2 (E Y − E[Y ∧ c])` (`tail_le_sub_min`) and `E[σ²Z² ∧ c] ↑ σ²`. The
distributional step needs Lévy continuity
(`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun`), since 2.21(ii) is stated
in characteristic-function form; that is the one import this file gained in wave `ts/s10`.
The degenerate case `σ² = 0` never reaches the CLT (which requires `σ² > 0`): there
`E Y_l → 0` bounds the tail integral directly.

**Why the second-moment toolbox cannot close it.** The two facts this file supplies about
one big block are `E S_l² ≤ Λ l` (`integral_sq_partialSum_le`) and `|S_l| ≤ C l` a.s.
Every interpolation they support has the shape
`∫_{|S_l| ≥ T} S_l² ≤ (C l)^γ · E S_l² / T^γ`, i.e. after dividing by `l` and taking
`T = ε√n`, the bound `Λ · (C l_n / (ε √n))^γ` — which vanishes only when `l_n = o(√n)`.
But the Bernstein constraints *force* `l_n ≫ √n` at **every** admissible scheme: the
Volkonskii–Rozanov budget needs `k_n ≤ s_n` (all `Σ α < ∞` gives is `m α(m) → 0`, see
`tendsto_mul_alphaCoeff`), the small blocks must be negligible so `s_n = o(l_n)`, and
`k_n ≍ n / l_n`; together `n / l_n ≲ s_n = o(l_n)`, i.e. `l_n² ≫ n`. So no choice of
block lengths makes the Lindeberg event empty or Chebyshev-negligible — and this is *not*
what the proof below does: it never chooses block lengths at all.

**The route that closes the theorem** (wave `ts/s5b`, recorded here for context). Do *not*
split the remainder at a Lindeberg level — use the global cubic half of `norm_expI_taylor`.
With `v_n = u n^{-1/2}` and `k_n ≍ n / l_n`,
`k_n ‖R n‖ ≤ 4 |u|³ · E|S_{l_n}|³ / (l_n √n)`, so it suffices that `E|S_l|³ = o(l √n)`;
Cauchy–Schwarz turns this into `E S_l⁴ = o(l n)`. And `E S_l⁴ = o(l³)` **is** available
from `Σ α < ∞` alone: splitting a sorted 4-tuple at its largest gap `G` gives
`E S_l⁴ ≤ 24 l (12 C⁴ W_l + 16 C⁴ l Λ_α²)` with `W_l = Σ_{g<l} α(g)(g+1)²` and
`Λ_α = Σ' α`, and `W_l = o(l²)` by Cesàro from `tendsto_mul_alphaCoeff`. Writing
`E S_l⁴ = l³ η_l` with `η_l → 0`, the requirement `E S_l⁴ = o(l n)` reads
`l_n² η_{l_n} = o(n)`, which holds for an **adaptively** chosen `l_n = ⌈√n · a_n⌉` with
`a_n → ∞` slowly enough (`exists_adaptive_small`, `exists_block_scheme_adaptive`). -/
private theorem lindeberg_blocks_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ) {C : ℝ}
    -- USER-INPUT: uniform bound; FY Thm 2.21(ii)
    (hbdd : ∀ t, ∀ᵐ ω ∂μ, |X t ω| ≤ C)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: summable mixing coefficients; FY Thm 2.21(ii)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n)
    (l : ℕ → ℕ) (hl1 : ∀ n, 1 ≤ l n)
    (hln : Tendsto (fun n : ℕ => (l n : ℝ) / (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((l n : ℝ))⁻¹ *
        ∫ ω in {ω | ε * Real.sqrt n ≤ |∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω|},
          (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨K, hK0, hK⟩ := exists_tail_threshold hmeas hstat hbdd hmean hα (half_pos hδ)
  have hev : ∀ᶠ n : ℕ in atTop, K * (l n : ℝ) ≤ ε ^ 2 * (n : ℝ) := by
    have h1 : Tendsto (fun n : ℕ => K * ((l n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
      simpa using hln.const_mul K
    have h2 : ∀ᶠ n : ℕ in atTop, K * ((l n : ℝ) / (n : ℝ)) < ε ^ 2 :=
      h1.eventually (gt_mem_nhds (by positivity))
    filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h3 := (mul_lt_mul_of_pos_right hn hn0).le
    have h4 : K * ((l n : ℝ) / (n : ℝ)) * (n : ℝ) = K * (l n : ℝ) := by field_simp
    linarith [h3, h4]
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hn => ?_⟩
  have hnn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hSmn : Measurable fun ω => (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2 :=
    (Finset.measurable_sum _ fun t _ => hmeas _).pow_const 2
  have hsetEq : {ω | ε * Real.sqrt n ≤ |∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω|}
      = {ω | ε ^ 2 * (n : ℝ) ≤ (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have h1 : (ε * Real.sqrt n) ^ 2
          ≤ |∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h 2
      rw [sq_abs, mul_pow, Real.sq_sqrt hnn] at h1
      exact h1
    · intro h
      by_contra hcon
      rw [not_le] at hcon
      have h1 : |∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω| ^ 2 < (ε * Real.sqrt n) ^ 2 :=
        pow_lt_pow_left₀ hcon (abs_nonneg _) two_ne_zero
      rw [sq_abs, mul_pow, Real.sq_sqrt hnn] at h1
      linarith
  rw [hsetEq]
  have hbound := hK (l n) (hl1 n) (ε ^ 2 * (n : ℝ)) (hN n hn)
  have hl0 : (0 : ℝ) < (l n : ℝ) := by exact_mod_cast hl1 n
  have hnonneg : 0 ≤ ((l n : ℝ))⁻¹ *
      ∫ ω in {ω | ε ^ 2 * (n : ℝ) ≤ (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2},
        (∑ t ∈ Finset.range (l n), X ((t : ℤ) + 1) ω) ^ 2 ∂μ :=
    mul_nonneg (by positivity)
      (setIntegral_nonneg (measurableSet_le measurable_const hSmn) fun ω _ => sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have h5 := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.2 hl0))
  have h6 : ((l n : ℝ))⁻¹ * (δ / 2 * (l n : ℝ)) = δ / 2 := by field_simp
  linarith [h5, h6]


/-! ### The `δ`-moment versions (FY Theorems 2.20(i)/2.21(i))

The `L^δ` route replaces the Billingsley bound `|γ(n)| ≤ 4α(n)C²` by the **Davydov** bound
`|γ(n)| ≤ 8 α(n)^{1−2/δ} ‖X_0‖_δ²` (`Mixing/Inequalities.abs_covariance_le_davydov` at
`p = q = δ`); absolute summability of the ACVF then follows from `Σ α^{1−2/δ} < ∞`, and the
variance rate is the shared analytic core `tendsto_var_rate_of_summable`. -/

section Delta

variable {X : ℤ → Ω → ℝ} {δ : ℝ}

/-- `2 ≤ ENNReal.ofReal δ` for `2 < δ`. -/
private lemma two_le_ofReal (hδ : 2 < δ) : (2 : ℝ≥0∞) ≤ ENNReal.ofReal δ := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact ENNReal.ofReal_le_ofReal hδ.le

/-- **Davydov bound on the ACVF** (FY Thm 2.20(i)), taken at `p = q = δ`: the lag-`n`
covariance pairs the anchored past `σ{X_s : s ≤ 0}` (holding `X_0`) with the future
`σ{X_s : s ≥ n}` (holding `X_n`), and strict stationarity makes the two `L^δ` norms equal.
The `1/p + 1/q < 1` side condition of Davydov's inequality is exactly `δ > 2`. -/
private lemma abs_acvf_le_alphaCoeff_davydov [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ) (n : ℕ) :
    |acvf X μ (n : ℤ)| ≤ 8 * alphaCoeff X μ n ^ (1 - 2 / δ)
      * (eLpNorm (X 0) (ENNReal.ofReal δ) μ).toReal ^ 2 := by
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hδ1 : (1 : ℝ) < δ := by linarith
  have hpq : 1 / δ + 1 / δ < 1 := by
    have h2 : 1 / δ + 1 / δ = 2 / δ := by ring
    rw [h2, div_lt_one hδ0]; linarith
  have h1 : sigmaLE X 0 ≤ (inferInstance : MeasurableSpace Ω) := sigmaLE_le hmeas 0
  have h2 : sigmaGE X (n : ℤ) ≤ (inferInstance : MeasurableSpace Ω) := sigmaGE_le hmeas _
  have hf : Measurable[sigmaLE X 0] (X 0) :=
    (measurable_comap_self X 0).mono (comap_le_sigmaLE X le_rfl) le_rfl
  have hg : Measurable[sigmaGE X (n : ℤ)] (X (n : ℤ)) :=
    (measurable_comap_self X _).mono (comap_le_sigmaGE X le_rfl) le_rfl
  have hid : IdentDistrib (X 0) (X (n : ℤ)) μ μ := hstat.identDistrib hmeas 0 (n : ℤ)
  have hLδn : MemLp (X (n : ℤ)) (ENNReal.ofReal δ) μ := hid.memLp_snd hLδ
  have hnorm : eLpNorm (X (n : ℤ)) (ENNReal.ofReal δ) μ
      = eLpNorm (X 0) (ENNReal.ofReal δ) μ := (hid.eLpNorm_eq (ENNReal.ofReal δ)).symm
  have key := abs_covariance_le_davydov h1 h2 hf hg hδ1 hδ1 hpq hLδ hLδn
  rw [acvf, covariance_comm]
  refine key.trans (le_of_eq ?_)
  rw [hnorm, alphaCoeff]
  have he : (1 : ℝ) - 1 / δ - 1 / δ = 1 - 2 / δ := by ring
  rw [he]
  ring

/-- Absolute summability of the ACVF under the `δ`-moment hypotheses (first half of FY
Theorem 2.20(i)): Davydov per lag, `Σ α^{1−2/δ} < ∞` over lags, and evenness of the ACVF
to fold the negative lags in. -/
private lemma summable_abs_acvf_davydov [IsProbabilityMeasure μ]
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ) (hws : IsStationary X μ)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ (1 - 2 / δ)) :
    Summable fun k : ℤ => |acvf X μ k| := by
  have hpos : Summable fun n : ℕ => |acvf X μ (n : ℤ)| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => abs_acvf_le_alphaCoeff_davydov hmeas hstat hδ hLδ n)
      ((hα.mul_left 8).mul_right _)
  refine Summable.of_nat_of_neg hpos ?_
  simpa only [acvf_neg hws] using hpos

/-! #### Transfer bricks for the truncation argument

`clt_of_alphaMixing_debt` is reduced to `clt_of_bounded_alphaMixing` by truncating the
coordinates. Every structural hypothesis has to be transported along a *common measurable
transform* `X_t ↦ g(X_t)`: strict stationarity (the finite-dimensional laws compose), the
past/future σ-algebras (they shrink) and hence the α-coefficients. -/

/-- Strict stationarity is preserved by a common measurable transform of the coordinates:
the finite-dimensional law of `(g ∘ X_{t_i + k})_i` is the pushforward of that of
`(X_{t_i + k})_i` along the fixed map `v ↦ g ∘ v`. -/
private lemma isStrictlyStationary_comp (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ) {g : ℝ → ℝ} (hg : Measurable g) :
    IsStrictlyStationary (fun t ω => g (X t ω)) μ := by
  intro n t k
  have hG : Measurable fun (v : Fin n → ℝ) (i : Fin n) => g (v i) :=
    measurable_pi_lambda _ fun i => hg.comp (measurable_pi_apply i)
  have hXk : Measurable fun ω (i : Fin n) => X (t i + k) ω :=
    measurable_pi_lambda _ fun i => hmeas _
  have hX0 : Measurable fun ω (i : Fin n) => X (t i) ω :=
    measurable_pi_lambda _ fun i => hmeas _
  show (μ.map fun ω (i : Fin n) => g (X (t i + k) ω))
      = μ.map fun ω (i : Fin n) => g (X (t i) ω)
  have e1 : (fun ω (i : Fin n) => g (X (t i + k) ω))
      = (fun (v : Fin n → ℝ) (i : Fin n) => g (v i)) ∘ fun ω (i : Fin n) => X (t i + k) ω := rfl
  have e2 : (fun ω (i : Fin n) => g (X (t i) ω))
      = (fun (v : Fin n → ℝ) (i : Fin n) => g (v i)) ∘ fun ω (i : Fin n) => X (t i) ω := rfl
  rw [e1, e2, ← Measure.map_map hG hXk, ← Measure.map_map hG hX0, hstat n t k]

/-- The past σ-algebra of a transformed process is contained in that of the original. -/
private lemma sigmaLE_comp_le (hmeas : ∀ t, Measurable (X t)) {g : ℝ → ℝ} (hg : Measurable g)
    (n : ℤ) : sigmaLE (fun t ω => g (X t ω)) n ≤ sigmaLE X n := by
  refine iSup₂_le fun s hs => ?_
  have hm : Measurable[sigmaLE X n] fun ω => g (X s ω) :=
    hg.comp ((measurable_comap_self X s).mono (comap_le_sigmaLE X hs) le_rfl)
  exact hm.comap_le

/-- The future σ-algebra of a transformed process is contained in that of the original. -/
private lemma sigmaGE_comp_le (hmeas : ∀ t, Measurable (X t)) {g : ℝ → ℝ} (hg : Measurable g)
    (n : ℤ) : sigmaGE (fun t ω => g (X t ω)) n ≤ sigmaGE X n := by
  refine iSup₂_le fun s hs => ?_
  have hm : Measurable[sigmaGE X n] fun ω => g (X s ω) :=
    hg.comp ((measurable_comap_self X s).mono (comap_le_sigmaGE X hs) le_rfl)
  exact hm.comap_le

/-- Transformed coordinates are *at most* as dependent: `α_{g∘X}(n) ≤ α_X(n)`. -/
private lemma alphaCoeff_comp_le [IsProbabilityMeasure μ] (hmeas : ∀ t, Measurable (X t))
    {g : ℝ → ℝ} (hg : Measurable g) (n : ℕ) :
    alphaCoeff (fun t ω => g (X t ω)) μ n ≤ alphaCoeff X μ n :=
  alphaMixCoeff_mono (sigmaLE_comp_le hmeas hg 0) (sigmaGE_comp_le hmeas hg (n : ℤ))

/-- `Σ α^θ < ∞` with `0 < θ ≤ 1` forces `Σ α < ∞`: the coefficients lie in `[0, 1]`, where
raising to a smaller exponent can only increase them. -/
private lemma summable_alphaCoeff_of_rpow [IsProbabilityMeasure μ] {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ θ) :
    Summable fun n : ℕ => alphaCoeff X μ n := by
  refine hα.of_nonneg_of_le (fun n => alphaMixCoeff_nonneg) (fun n => ?_)
  have h0 : 0 ≤ alphaCoeff X μ n := alphaMixCoeff_nonneg
  have h1 : alphaCoeff X μ n ≤ 1 := alphaMixCoeff_le_one (mΩ := inferInstance)
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, Real.zero_rpow hθ0.ne']
  · calc alphaCoeff X μ n = alphaCoeff X μ n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ alphaCoeff X μ n ^ θ := Real.rpow_le_rpow_of_exponent_ge h h1 hθ1

/-! #### `L²` bricks: the `√∫f²` form of the `L²` norm and Minkowski's inequality -/

/-- `‖f‖_{L²}` in the `√∫f²` form. -/
private lemma eLpNorm_two_eq_sqrt [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ ω, f ω ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have hint : (∫ ω, ‖f ω‖ ^ ((2 : ℝ≥0∞).toReal) ∂μ) = ∫ ω, f ω ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show ‖f ω‖ ^ ((2 : ℝ≥0∞).toReal) = f ω ^ 2
    have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2, Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  rw [hint]
  congr 1
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- **Minkowski** in the only form the truncation argument consumes. -/
private lemma sqrt_integral_sq_add_le [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ ω, (f ω + g ω) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hfg : MemLp (fun ω => f ω + g ω) 2 μ := hf.add hg
  have hmink : eLpNorm (fun ω => f ω + g ω) 2 μ ≤ eLpNorm f 2 μ + eLpNorm g 2 μ := by
    have h := eLpNorm_add_le (μ := μ) (p := 2) hf.aestronglyMeasurable hg.aestronglyMeasurable
      one_le_two
    exact h
  rw [eLpNorm_two_eq_sqrt hfg, eLpNorm_two_eq_sqrt hf, eLpNorm_two_eq_sqrt hg,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)] at hmink
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmink

/-- **Minkowski**, difference form. -/
private lemma sqrt_integral_sq_sub_le [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Real.sqrt (∫ ω, (f ω - g ω) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hgn : MemLp (fun ω => -g ω) 2 μ := hg.neg
  have h : Real.sqrt (∫ ω, (f ω + -g ω) ^ 2 ∂μ)
      ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) + Real.sqrt (∫ ω, (-g ω) ^ 2 ∂μ) :=
    sqrt_integral_sq_add_le hf hgn
  have e1 : (∫ ω, (f ω + -g ω) ^ 2 ∂μ) = ∫ ω, (f ω - g ω) ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by ring)
  have e2 : (∫ ω, (-g ω) ^ 2 ∂μ) = ∫ ω, g ω ^ 2 ∂μ :=
    integral_congr_ae (Eventually.of_forall fun ω => by ring)
  rw [e1, e2] at h
  exact h

/-! #### Clamping arithmetic -/

/-- The clamp `x ↦ max (−M) (min M x)` is measurable. -/
private lemma measurable_clamp (M : ℝ) : Measurable fun x : ℝ => max (-M) (min M x) :=
  measurable_const.max (measurable_const.min measurable_id)

/-- Clamping to `[−M, M]` is bounded by `M`. -/
private lemma abs_clamp_le'' {M x : ℝ} (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ M := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- Clamping only moves a point towards the origin, so the discarded part is no larger than
the point itself. -/
private lemma abs_sub_clamp_le'' {M x : ℝ} (hM : 0 ≤ M) :
    |x - max (-M) (min M x)| ≤ |x| := by
  rcases le_total x (-M) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]
    rw [abs_of_nonpos (by linarith : x ≤ 0), abs_of_nonpos (by linarith : x - -M ≤ 0)]
    linarith
  · rcases le_total x M with h2 | h2
    · rw [min_eq_right h2, max_eq_right h]
      simp
    · rw [min_eq_left h2, max_eq_right (by linarith)]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x), abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - M)]
      linarith

/-- Below the clamping level nothing is discarded. -/
private lemma sub_clamp_eq_zero'' {M x : ℝ} (h : |x| ≤ M) : x - max (-M) (min M x) = 0 := by
  rw [abs_le] at h
  rw [min_eq_right h.2, max_eq_right h.1, sub_self]

/-! #### Davydov over `ℤ`-lags, and transfer of the mixing hypothesis -/

/-- The Davydov ACVF bound at an arbitrary (signed) lag. -/
private lemma abs_acvf_int_le_davydov [IsProbabilityMeasure μ] {W : ℤ → Ω → ℝ}
    (hmW : ∀ t, Measurable (W t)) (hstatW : IsStrictlyStationary W μ)
    (hwsW : IsStationary W μ) (hδ : 2 < δ) (hLδW : MemLp (W 0) (ENNReal.ofReal δ) μ) (k : ℤ) :
    |acvf W μ k| ≤ 8 * alphaCoeff W μ k.natAbs ^ (1 - 2 / δ)
      * (eLpNorm (W 0) (ENNReal.ofReal δ) μ).toReal ^ 2 := by
  set m : ℕ := k.natAbs with hm
  rcases le_or_gt 0 k with h | h
  · have hk : k = (m : ℤ) := by omega
    rw [hk]
    exact abs_acvf_le_alphaCoeff_davydov hmW hstatW hδ hLδW m
  · have hk : k = -((m : ℤ)) := by omega
    rw [hk, acvf_neg hwsW]
    exact abs_acvf_le_alphaCoeff_davydov hmW hstatW hδ hLδW m

/-- `Σ α_X^θ < ∞` transfers to any process whose coefficients are dominated by `α_X`. -/
private lemma summable_rpow_of_le [IsProbabilityMeasure μ] {W : ℤ → Ω → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hle : ∀ n : ℕ, alphaCoeff W μ n ≤ alphaCoeff X μ n)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ θ) :
    Summable fun n : ℕ => alphaCoeff W μ n ^ θ :=
  hα.of_nonneg_of_le (fun _ => Real.rpow_nonneg alphaMixCoeff_nonneg θ)
    (fun n => Real.rpow_le_rpow alphaMixCoeff_nonneg (hle n) hθ)

/-! #### Partial-sum bookkeeping for a general stationary `L²` process -/

/-- Every coordinate has the law of `W 0`, hence the same `L^p` membership. -/
private lemma memLp_coord [IsProbabilityMeasure μ] {W : ℤ → Ω → ℝ}
    (hmW : ∀ t, Measurable (W t)) (hstatW : IsStrictlyStationary W μ) {p : ℝ≥0∞}
    (hL : MemLp (W 0) p μ) (t : ℤ) : MemLp (W t) p μ :=
  (hstatW.identDistrib hmW 0 t).memLp_snd hL

/-- Partial sums inherit `L^p` membership. -/
private lemma memLp_partialSum [IsProbabilityMeasure μ] {W : ℤ → Ω → ℝ}
    (hmW : ∀ t, Measurable (W t)) (hstatW : IsStrictlyStationary W μ) {p : ℝ≥0∞}
    (hL : MemLp (W 0) p μ) (D : Finset ℕ) :
    MemLp (fun ω => ∑ t ∈ D, W ((t : ℤ) + 1) ω) p μ := by
  have hfun : (fun ω => ∑ t ∈ D, W ((t : ℤ) + 1) ω) = ∑ t ∈ D, W ((t : ℤ) + 1) := by
    funext ω; simp [Finset.sum_apply]
  rw [hfun]
  exact memLp_finset_sum' (μ := μ) D fun t _ => memLp_coord hmW hstatW hL _

/-- Partial sums of a zero-mean stationary process have mean zero. -/
private lemma integral_partialSum_eq_zero' [IsProbabilityMeasure μ] {W : ℤ → Ω → ℝ}
    (hmW : ∀ t, Measurable (W t)) (hstatW : IsStrictlyStationary W μ)
    (hL1 : MemLp (W 0) 1 μ) (hmeanW : ∫ ω, W 0 ω ∂μ = 0) (D : Finset ℕ) :
    ∫ ω, (∑ t ∈ D, W ((t : ℤ) + 1) ω) ∂μ = 0 := by
  have hsplit : ∫ ω, (∑ t ∈ D, W ((t : ℤ) + 1) ω) ∂μ
      = ∑ t ∈ D, ∫ ω, W ((t : ℤ) + 1) ω ∂μ :=
    integral_finset_sum (f := fun (t : ℕ) ω => W ((t : ℤ) + 1) ω) D
      (fun t _ => (memLp_coord hmW hstatW hL1 _).integrable le_rfl)
  rw [hsplit]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [(hstatW.identDistrib hmW ((t : ℤ) + 1) 0).integral_eq, hmeanW]

/-- For a zero-mean stationary `L²` process the variance of a partial sum is its second
moment. -/
private lemma variance_partialSum_eq [IsProbabilityMeasure μ] {W : ℤ → Ω → ℝ}
    (hmW : ∀ t, Measurable (W t)) (hstatW : IsStrictlyStationary W μ)
    (hL2 : MemLp (W 0) 2 μ) (hmeanW : ∫ ω, W 0 ω ∂μ = 0) (D : Finset ℕ) :
    variance (fun ω => ∑ t ∈ D, W ((t : ℤ) + 1) ω) μ
      = ∫ ω, (∑ t ∈ D, W ((t : ℤ) + 1) ω) ^ 2 ∂μ :=
  variance_of_integral_eq_zero
    (memLp_partialSum hmW hstatW hL2 D).aestronglyMeasurable.aemeasurable
    (integral_partialSum_eq_zero' hmW hstatW (hL2.mono_exponent one_le_two) hmeanW D)

/-- The crude bound `|γ_W(k)| ≤ E W_0²` (AM–GM on the product, stationarity on the second
moment). It is what makes the *discarded* part of the truncation negligible lag by lag. -/
private lemma abs_acvf_le_integral_sq [IsProbabilityMeasure μ] {W : ℤ → Ω → ℝ}
    (hmW : ∀ t, Measurable (W t)) (hstatW : IsStrictlyStationary W μ)
    (hL2 : MemLp (W 0) 2 μ) (hmeanW : ∫ ω, W 0 ω ∂μ = 0) (k : ℤ) :
    |acvf W μ k| ≤ ∫ ω, (W 0 ω) ^ 2 ∂μ := by
  have hk2 : MemLp (W k) 2 μ := memLp_coord hmW hstatW hL2 k
  have hmk : ∫ ω, W k ω ∂μ = 0 := by
    rw [(hstatW.identDistrib hmW k 0).integral_eq, hmeanW]
  have hsqk : ∫ ω, (W k ω) ^ 2 ∂μ = ∫ ω, (W 0 ω) ^ 2 ∂μ := by
    have := ((hstatW.identDistrib hmW k 0).comp (measurable_id.pow_const 2)).integral_eq
    simpa using this
  have hprod : Integrable (fun ω => W k ω * W 0 ω) μ := by
    have h := MemLp.integrable_mul hk2 hL2
    exact h
  have hcov : acvf W μ k = ∫ ω, W k ω * W 0 ω ∂μ := by
    rw [acvf, covariance_eq_sub hk2 hL2, hmk, hmeanW]
    simp [Pi.mul_apply]
  rw [hcov]
  have h1 : |∫ ω, W k ω * W 0 ω ∂μ| ≤ ∫ ω, |W k ω * W 0 ω| ∂μ :=
    abs_integral_le_integral_abs
  have h2 : ∫ ω, |W k ω * W 0 ω| ∂μ
      ≤ ∫ ω, ((W k ω) ^ 2 + (W 0 ω) ^ 2) / 2 ∂μ := by
    refine integral_mono hprod.abs ((hk2.integrable_sq.add hL2.integrable_sq).div_const 2)
      fun ω => ?_
    rw [abs_mul]
    nlinarith [sq_nonneg (|W k ω| - |W 0 ω|), abs_nonneg (W k ω), abs_nonneg (W 0 ω),
      sq_abs (W k ω), sq_abs (W 0 ω)]
  have h3 : ∫ ω, ((W k ω) ^ 2 + (W 0 ω) ^ 2) / 2 ∂μ = ∫ ω, (W 0 ω) ^ 2 ∂μ := by
    rw [integral_div, integral_add hk2.integrable_sq hL2.integrable_sq, hsqk]
    ring
  linarith

/-- Clamping never increases the modulus. -/
private lemma abs_clamp_le_abs {M x : ℝ} (hM : 0 ≤ M) : |max (-M) (min M x)| ≤ |x| := by
  rcases le_total x (-M) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]
    rw [abs_of_nonpos (by linarith : (-M : ℝ) ≤ 0), abs_of_nonpos (by linarith : x ≤ 0)]
    linarith
  · rcases le_total x M with h2 | h2
    · rw [min_eq_right h2, max_eq_right h]
    · rw [min_eq_left h2, max_eq_right (by linarith)]
      rw [abs_of_nonneg hM, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      linarith

/-- Below the clamping level the clamp is the identity. -/
private lemma clamp_eq_self'' {M x : ℝ} (h : |x| ≤ M) : max (-M) (min M x) = x := by
  have := sub_clamp_eq_zero'' h
  linarith

/-- The characteristic function of the law of a scaled statistic, as an integral over `Ω`. -/
private lemma charFun_map_scaled [IsProbabilityMeasure μ] {S : Ω → ℝ} (hS : Measurable S)
    (a u : ℝ) :
    charFun (μ.map fun ω => a * S ω) u
      = ∫ ω, Complex.exp (((u * a * S ω : ℝ) : ℂ) * Complex.I) ∂μ := by
  have hae : AEMeasurable (fun ω => a * S ω) μ := (measurable_const.mul hS).aemeasurable
  have hsm : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ) * Complex.I))
      (μ.map fun ω => a * S ω) :=
    (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  rw [charFun_apply_real, integral_map hae hsm]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  push_cast
  ring

/-- The `ℤ`-indexed Davydov dominant is summable. -/
private lemma summable_int_dominant [IsProbabilityMeasure μ] {θ c : ℝ}
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ θ) :
    Summable fun k : ℤ => 8 * alphaCoeff X μ k.natAbs ^ θ * c := by
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using (hα.mul_left 8).mul_right c
  · simpa using (hα.mul_left 8).mul_right c

end Delta

/-- **FY Theorem 2.20(i)** (Bosq 1998 §1.5) — the `δ`-moment version of the variance rate:
`E|X|^δ < ∞` (`δ > 2`) and `Σ_j α(j)^{1−2/δ} < ∞` give an absolutely summable ACVF and
`n⁻¹ Var(S_n) → γ(0) + 2 Σ_{j ≥ 1} γ(j)`. Davydov's covariance inequality supplies the
per-lag bound; the limit itself is the shared Fejér/Tannery core
`tendsto_var_rate_of_summable`. -/
theorem summable_acvf_and_var_rate_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {δ : ℝ}
    -- USER-INPUT: δ-moment; FY Thm 2.20(i)
    (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ)
    -- USER-INPUT: zero mean; FY §2.6.3 setup
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    -- USER-INPUT: Σ α^{1−2/δ} < ∞; FY Thm 2.20(i)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ (1 - 2 / δ)) :
    (Summable fun k : ℤ => |acvf X μ k|) ∧
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
          variance (fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) μ) atTop
        (𝓝 (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))) := by
  have hws : IsStationary X μ :=
    hstat.isStationary hmeas (hLδ.mono_exponent (two_le_ofReal hδ))
  have hsum : Summable fun k : ℤ => |acvf X μ k| :=
    summable_abs_acvf_davydov hmeas hstat hδ hLδ hws hα
  exact ⟨hsum, tendsto_var_rate_of_summable hws hsum⟩

/-- **DEBT (Peligrad; FY Theorem 2.21(i))**: the `δ`-moment CLT under the Thm 2.20(i)
hypotheses and positive long-run variance. -/
theorem clt_of_alphaMixing_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {δ : ℝ} (hδ : 2 < δ) (hLδ : MemLp (X 0) (ENNReal.ofReal δ) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hα : Summable fun n : ℕ => alphaCoeff X μ n ^ (1 - 2 / δ))
    (hσ : 0 < acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1))
    (u : ℝ) :
    Tendsto (fun n : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0
        (Real.toNNReal (acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1)))) u)) := by
  classical
  -- ### 0. Exponent bookkeeping and the `X`-side variance rate
  have hδ0 : (0 : ℝ) < δ := by linarith
  have hθ0 : (0 : ℝ) < 1 - 2 / δ := by
    have h : 2 / δ < 1 := (div_lt_one hδ0).mpr (by linarith)
    linarith
  have hθ1 : (1 : ℝ) - 2 / δ ≤ 1 := by
    have h : (0 : ℝ) < 2 / δ := by positivity
    linarith
  have hmem2 : MemLp (X 0) 2 μ := hLδ.mono_exponent (two_le_ofReal hδ)
  have hXint : Integrable (X 0) μ := hmem2.integrable one_le_two
  obtain ⟨hsumX, hrateX⟩ := summable_acvf_and_var_rate_debt hmeas hstat hδ hLδ hmean hα
  set σ2 : ℝ := acvf X μ 0 + 2 * ∑' j : ℕ, acvf X μ ((j : ℤ) + 1) with hσ2def
  -- ### 1. The truncated (`gY`) and discarded (`gZ`) coordinate maps
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ M : ℕ,
      c M = ∫ ω, max (-(M : ℝ)) (min (M : ℝ) (X 0 ω)) ∂μ := ⟨_, fun _ => rfl⟩
  obtain ⟨gY, hgY⟩ : ∃ gY : ℕ → ℝ → ℝ, ∀ M : ℕ,
      gY M = fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x) - c M := ⟨_, fun _ => rfl⟩
  obtain ⟨gZ, hgZ⟩ : ∃ gZ : ℕ → ℝ → ℝ, ∀ M : ℕ,
      gZ M = fun x : ℝ => x - gY M x := ⟨_, fun _ => rfl⟩
  have hgYm : ∀ M : ℕ, Measurable (gY M) := fun M => by
    rw [hgY M]; exact (measurable_clamp _).sub_const _
  have hgZm : ∀ M : ℕ, Measurable (gZ M) := fun M => by
    rw [hgZ M]; exact measurable_id.sub (hgYm M)
  have hsplitYZ : ∀ (M : ℕ) (x : ℝ), gY M x + gZ M x = x := by
    intro M x; simp only [hgZ M]; ring
  have hclampInt : ∀ M : ℕ, Integrable (fun ω => max (-(M : ℝ)) (min (M : ℝ) (X 0 ω))) μ := by
    intro M
    refine MemLp.integrable (q := ⊤) le_top (memLp_top_of_bound
      ((measurable_clamp _).comp (hmeas 0)).aestronglyMeasurable (M : ℝ) ?_)
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using abs_clamp_le'' (M := (M : ℝ)) (Nat.cast_nonneg M)
  set b : ℝ := ∫ ω, |X 0 ω| ∂μ with hbdef
  have hb0 : (0 : ℝ) ≤ b := integral_nonneg fun _ => abs_nonneg _
  have hcb : ∀ M : ℕ, |c M| ≤ b := by
    intro M
    have hz : c M = ∫ ω, (max (-(M : ℝ)) (min (M : ℝ) (X 0 ω)) - X 0 ω) ∂μ := by
      rw [hc M, integral_sub (hclampInt M) hXint, hmean, sub_zero]
    rw [hz]
    refine abs_integral_le_integral_abs.trans ?_
    refine integral_mono ((hclampInt M).sub hXint).abs hXint.abs fun ω => ?_
    rw [abs_sub_comm]
    exact abs_sub_clamp_le'' (M := (M : ℝ)) (Nat.cast_nonneg M)
  -- pointwise size of the two parts
  have hYbound : ∀ (M : ℕ) (x : ℝ), |gY M x| ≤ (M : ℝ) + b := by
    intro M x
    have h1 := abs_clamp_le'' (M := (M : ℝ)) (x := x) (Nat.cast_nonneg M)
    have h2 := hcb M
    rw [hgY M]
    rw [abs_le] at h1 h2 ⊢
    constructor <;> [linarith; linarith]
  have hZbound : ∀ (M : ℕ) (x : ℝ), |gZ M x| ≤ |x| + b := by
    intro M x
    have h1 := abs_sub_clamp_le'' (M := (M : ℝ)) (x := x) (Nat.cast_nonneg M)
    have h2 := hcb M
    have hx : gZ M x = (x - max (-(M : ℝ)) (min (M : ℝ) x)) + c M := by
      simp only [hgZ M, hgY M]; ring
    rw [hx]
    rw [abs_le] at h1 h2 ⊢
    constructor <;> [linarith; linarith]
  -- ### 2. Structural facts for the two derived processes
  have hmY : ∀ (M : ℕ) (t : ℤ), Measurable fun ω => gY M (X t ω) :=
    fun M t => (hgYm M).comp (hmeas t)
  have hmZ : ∀ (M : ℕ) (t : ℤ), Measurable fun ω => gZ M (X t ω) :=
    fun M t => (hgZm M).comp (hmeas t)
  have hstatY : ∀ M : ℕ, IsStrictlyStationary (fun t ω => gY M (X t ω)) μ :=
    fun M => isStrictlyStationary_comp hmeas hstat (hgYm M)
  have hstatZ : ∀ M : ℕ, IsStrictlyStationary (fun t ω => gZ M (X t ω)) μ :=
    fun M => isStrictlyStationary_comp hmeas hstat (hgZm M)
  have hαYle : ∀ (M n : ℕ), alphaCoeff (fun t ω => gY M (X t ω)) μ n ≤ alphaCoeff X μ n :=
    fun M n => alphaCoeff_comp_le hmeas (hgYm M) n
  have hαZle : ∀ (M n : ℕ), alphaCoeff (fun t ω => gZ M (X t ω)) μ n ≤ alphaCoeff X μ n :=
    fun M n => alphaCoeff_comp_le hmeas (hgZm M) n
  have hbddY : ∀ (M : ℕ) (t : ℤ), ∀ᵐ ω ∂μ, |gY M (X t ω)| ≤ (M : ℝ) + b := by
    intro M t; filter_upwards with ω; exact hYbound M _
  have hYtop : ∀ M : ℕ, MemLp (fun ω => gY M (X 0 ω)) ⊤ μ := by
    intro M
    refine memLp_top_of_bound (hmY M 0).aestronglyMeasurable ((M : ℝ) + b) ?_
    filter_upwards with ω
    simpa [Real.norm_eq_abs] using hYbound M (X 0 ω)
  have hδY : ∀ M : ℕ, MemLp (fun ω => gY M (X 0 ω)) (ENNReal.ofReal δ) μ :=
    fun M => (hYtop M).mono_exponent le_top
  have hY2 : ∀ M : ℕ, MemLp (fun ω => gY M (X 0 ω)) 2 μ :=
    fun M => (hYtop M).mono_exponent le_top
  have hYint : ∀ M : ℕ, Integrable (fun ω => gY M (X 0 ω)) μ :=
    fun M => (hY2 M).integrable one_le_two
  have hmeanY : ∀ M : ℕ, ∫ ω, gY M (X 0 ω) ∂μ = 0 := by
    intro M
    have heq : (fun ω => gY M (X 0 ω))
        = fun ω => max (-(M : ℝ)) (min (M : ℝ) (X 0 ω)) - c M := by
      funext ω; rw [hgY M]
    rw [heq, integral_sub (hclampInt M) (integrable_const _), integral_const, ← hc M]
    simp
  have hmeanZ : ∀ M : ℕ, ∫ ω, gZ M (X 0 ω) ∂μ = 0 := by
    intro M
    have heq : (fun ω => gZ M (X 0 ω)) = fun ω => X 0 ω - gY M (X 0 ω) := by
      funext ω; simp only [hgZ M]
    rw [heq, integral_sub hXint (hYint M), hmean, hmeanY M, sub_zero]
  -- the dominating envelope of the discarded coordinate
  have hEnvδ : MemLp (fun ω => |X 0 ω| + b) (ENNReal.ofReal δ) μ := by
    have h1 : MemLp (fun ω => |X 0 ω|) (ENNReal.ofReal δ) μ := by
      simpa only [Real.norm_eq_abs] using hLδ.norm
    exact h1.add (memLp_const b)
  have hEnv2 : MemLp (fun ω => |X 0 ω| + b) 2 μ := by
    have h1 : MemLp (fun ω => |X 0 ω|) 2 μ := by
      simpa only [Real.norm_eq_abs] using hmem2.norm
    exact h1.add (memLp_const b)
  have hδZ : ∀ M : ℕ, MemLp (fun ω => gZ M (X 0 ω)) (ENNReal.ofReal δ) μ := by
    intro M
    refine hEnvδ.mono (hmZ M 0).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg (X 0 ω)) hb0)]
    exact hZbound M (X 0 ω)
  have hZ2 : ∀ M : ℕ, MemLp (fun ω => gZ M (X 0 ω)) 2 μ := by
    intro M
    refine hEnv2.mono (hmZ M 0).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg (X 0 ω)) hb0)]
    exact hZbound M (X 0 ω)
  have hαYsum : ∀ M : ℕ,
      Summable fun n : ℕ => alphaCoeff (fun t ω => gY M (X t ω)) μ n ^ (1 - 2 / δ) :=
    fun M => summable_rpow_of_le hθ0.le (hαYle M) hα
  have hαZsum : ∀ M : ℕ,
      Summable fun n : ℕ => alphaCoeff (fun t ω => gZ M (X t ω)) μ n ^ (1 - 2 / δ) :=
    fun M => summable_rpow_of_le hθ0.le (hαZle M) hα
  -- ### 3. Variance rates for the two derived processes
  obtain ⟨sY, hsY⟩ : ∃ sY : ℕ → ℝ, ∀ M : ℕ, sY M = acvf (fun t ω => gY M (X t ω)) μ 0
      + 2 * ∑' j : ℕ, acvf (fun t ω => gY M (X t ω)) μ ((j : ℤ) + 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨sZ, hsZ⟩ : ∃ sZ : ℕ → ℝ, ∀ M : ℕ, sZ M = acvf (fun t ω => gZ M (X t ω)) μ 0
      + 2 * ∑' j : ℕ, acvf (fun t ω => gZ M (X t ω)) μ ((j : ℤ) + 1) := ⟨_, fun _ => rfl⟩
  have hYpack := fun M : ℕ =>
    summable_acvf_and_var_rate_debt (hmY M) (hstatY M) hδ (hδY M) (hmeanY M) (hαYsum M)
  have hZpack := fun M : ℕ =>
    summable_acvf_and_var_rate_debt (hmZ M) (hstatZ M) hδ (hδZ M) (hmeanZ M) (hαZsum M)
  have hrateY : ∀ M : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      variance (fun ω => ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) μ) atTop
      (𝓝 (sY M)) := by
    intro M; rw [hsY M]; exact (hYpack M).2
  have hrateZ : ∀ M : ℕ, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ *
      variance (fun ω => ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) μ) atTop
      (𝓝 (sZ M)) := by
    intro M; rw [hsZ M]; exact (hZpack M).2
  -- ### 4. The discarded part vanishes: `σ_Z(M)² → 0`
  have hcM0 : Tendsto c atTop (𝓝 0) := by
    have hconv : ∀ᵐ ω ∂μ, Tendsto (fun M : ℕ => max (-(M : ℝ)) (min (M : ℝ) (X 0 ω)))
        atTop (𝓝 (X 0 ω)) := by
      filter_upwards with ω
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop (Nat.ceil |X 0 ω|)] with M hM
      have hle : |X 0 ω| ≤ (M : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hM)
      exact (clamp_eq_self'' hle).symm
    have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (M : ℕ) ω => max (-(M : ℝ)) (min (M : ℝ) (X 0 ω))) (f := fun ω => X 0 ω)
      (bound := fun ω => |X 0 ω|)
      (fun M => ((measurable_clamp _).comp (hmeas 0)).aestronglyMeasurable)
      hXint.abs
      (fun M => Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using abs_clamp_le_abs (M := (M : ℝ)) (Nat.cast_nonneg M))
      hconv
    rw [hmean] at hdct
    exact hdct.congr fun M => (hc M).symm
  have heZ : Tendsto (fun M : ℕ => ∫ ω, (gZ M (X 0 ω)) ^ 2 ∂μ) atTop (𝓝 0) := by
    have hconv : ∀ᵐ ω ∂μ, Tendsto (fun M : ℕ => (gZ M (X 0 ω)) ^ 2) atTop (𝓝 0) := by
      filter_upwards with ω
      have hEq : ∀ᶠ M : ℕ in atTop, c M = gZ M (X 0 ω) := by
        filter_upwards [eventually_ge_atTop (Nat.ceil |X 0 ω|)] with M hM
        have hle : |X 0 ω| ≤ (M : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hM)
        have := sub_clamp_eq_zero'' hle
        simp only [hgZ M, hgY M]
        linarith
      have h1 : Tendsto (fun M : ℕ => gZ M (X 0 ω)) atTop (𝓝 0) := Tendsto.congr' hEq hcM0
      simpa using h1.pow 2
    have hdomint : Integrable (fun ω => (|X 0 ω| + b) ^ 2) μ := hEnv2.integrable_sq
    have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (M : ℕ) ω => (gZ M (X 0 ω)) ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun ω => (|X 0 ω| + b) ^ 2)
      (fun M => ((hmZ M 0).pow_const 2).aestronglyMeasurable)
      hdomint
      (fun M => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hb := hZbound M (X 0 ω)
        have h0 : (0 : ℝ) ≤ |gZ M (X 0 ω)| := abs_nonneg _
        nlinarith [sq_abs (gZ M (X 0 ω)), abs_nonneg (X 0 ω)])
      hconv
    simpa using hdct
  have hptZ : ∀ k : ℤ,
      Tendsto (fun M : ℕ => acvf (fun t ω => gZ M (X t ω)) μ k) atTop (𝓝 0) := by
    intro k
    refine squeeze_zero_norm (fun M => ?_) heZ
    rw [Real.norm_eq_abs]
    exact abs_acvf_le_integral_sq (hmZ M) (hstatZ M) (hZ2 M) (hmeanZ M) k
  set A2 : ℝ := (eLpNorm (fun ω => |X 0 ω| + b) (ENNReal.ofReal δ) μ).toReal with hA2def
  have hA20 : (0 : ℝ) ≤ A2 := ENNReal.toReal_nonneg
  have hZδle : ∀ M : ℕ,
      (eLpNorm (fun ω => gZ M (X 0 ω)) (ENNReal.ofReal δ) μ).toReal ≤ A2 := by
    intro M
    refine ENNReal.toReal_mono hEnvδ.eLpNorm_ne_top (eLpNorm_mono_ae ?_)
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (abs_nonneg (X 0 ω)) hb0)]
    exact hZbound M (X 0 ω)
  have hdomk : ∀ (M : ℕ) (k : ℤ), |acvf (fun t ω => gZ M (X t ω)) μ k|
      ≤ 8 * alphaCoeff X μ k.natAbs ^ (1 - 2 / δ) * A2 ^ 2 := by
    intro M k
    have hwsZ : IsStationary (fun t ω => gZ M (X t ω)) μ :=
      (hstatZ M).isStationary (hmZ M) (hZ2 M)
    refine (abs_acvf_int_le_davydov (hmZ M) (hstatZ M) hwsZ hδ (hδZ M) k).trans ?_
    have h1 : alphaCoeff (fun t ω => gZ M (X t ω)) μ k.natAbs ^ (1 - 2 / δ)
        ≤ alphaCoeff X μ k.natAbs ^ (1 - 2 / δ) :=
      Real.rpow_le_rpow alphaMixCoeff_nonneg (hαZle M _) hθ0.le
    have h0 : (0 : ℝ) ≤ alphaCoeff (fun t ω => gZ M (X t ω)) μ k.natAbs ^ (1 - 2 / δ) :=
      Real.rpow_nonneg alphaMixCoeff_nonneg _
    have h2 : (eLpNorm (fun ω => gZ M (X 0 ω)) (ENNReal.ofReal δ) μ).toReal ^ 2 ≤ A2 ^ 2 := by
      have h := hZδle M
      nlinarith [ENNReal.toReal_nonneg
        (a := eLpNorm (fun ω => gZ M (X 0 ω)) (ENNReal.ofReal δ) μ)]
    have h3 : (0 : ℝ) ≤ (eLpNorm (fun ω => gZ M (X 0 ω)) (ENNReal.ofReal δ) μ).toReal ^ 2 :=
      sq_nonneg _
    nlinarith [Real.rpow_nonneg (alphaMixCoeff_nonneg (μ := μ)
      (m₁ := sigmaLE X 0) (m₂ := sigmaGE X (k.natAbs : ℤ))) (1 - 2 / δ)]
  have hK1 : Tendsto sZ atTop (𝓝 0) := by
    have htsum : ∀ M : ℕ, sZ M = ∑' k : ℤ, acvf (fun t ω => gZ M (X t ω)) μ k := by
      intro M
      rw [hsZ M]
      exact (tsum_acvf_eq ((hstatZ M).isStationary (hmZ M) (hZ2 M)) (hZpack M).1).symm
    have hdc := tendsto_tsum_of_dominated_convergence
      (f := fun (M : ℕ) (k : ℤ) => acvf (fun t ω => gZ M (X t ω)) μ k)
      (g := fun _ : ℤ => (0 : ℝ))
      (summable_int_dominant (X := X) (c := A2 ^ 2) hα) hptZ
      (Eventually.of_forall fun M k => by rw [Real.norm_eq_abs]; exact hdomk M k)
    rw [tsum_zero] at hdc
    exact hdc.congr fun M => (htsum M).symm
  -- ### 5. The truncated variance converges: `σ_Y(M)² → σ²`
  have hsqX : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ)⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)) atTop (𝓝 (Real.sqrt σ2)) := by
    refine (Real.continuous_sqrt.tendsto _).comp (hrateX.congr fun n => ?_)
    rw [variance_partialSum_eq hmeas hstat hmem2 hmean (Finset.range n)]
  have hsqY : ∀ M : ℕ, Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ)⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ)) atTop
      (𝓝 (Real.sqrt (sY M))) := by
    intro M
    refine (Real.continuous_sqrt.tendsto _).comp ((hrateY M).congr fun n => ?_)
    rw [variance_partialSum_eq (hmY M) (hstatY M) (hY2 M) (hmeanY M) (Finset.range n)]
  have hsqZ : ∀ M : ℕ, Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ)⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ)) atTop
      (𝓝 (Real.sqrt (sZ M))) := by
    intro M
    refine (Real.continuous_sqrt.tendsto _).comp ((hrateZ M).congr fun n => ?_)
    rw [variance_partialSum_eq (hmZ M) (hstatZ M) (hZ2 M) (hmeanZ M) (Finset.range n)]
  have hsumsplit : ∀ (M n : ℕ) (ω : Ω), (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω)
      = (∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω))
        + ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω) := by
    intro M n ω
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => (hsplitYZ M (X ((t : ℤ) + 1) ω)).symm
  have hmink : ∀ M n : ℕ, Real.sqrt ((n : ℝ)⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
      ≤ Real.sqrt ((n : ℝ)⁻¹ *
          ∫ ω, (∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ)
        + Real.sqrt ((n : ℝ)⁻¹ *
          ∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) := by
    intro M n
    have hX : (∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
        = ∫ ω, ((∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω))
            + ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by
        show (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 2
            = ((∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω))
              + ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2
        rw [hsumsplit M n ω])
    have hmk := sqrt_integral_sq_add_le
      (memLp_partialSum (hmY M) (hstatY M) (hY2 M) (Finset.range n))
      (memLp_partialSum (hmZ M) (hstatZ M) (hZ2 M) (Finset.range n))
    have hc0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    rw [hX, Real.sqrt_mul hc0, Real.sqrt_mul hc0, Real.sqrt_mul hc0]
    have := mul_le_mul_of_nonneg_left hmk (Real.sqrt_nonneg ((n : ℝ)⁻¹))
    linarith [this]
  have hmink' : ∀ M n : ℕ, Real.sqrt ((n : ℝ)⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ)
      ≤ Real.sqrt ((n : ℝ)⁻¹ * ∫ ω, (∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) ^ 2 ∂μ)
        + Real.sqrt ((n : ℝ)⁻¹ *
          ∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) := by
    intro M n
    have hY : (∫ ω, (∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ)
        = ∫ ω, ((∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω)
            - ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by
        show (∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) ^ 2
            = ((∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω)
              - ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2
        rw [hsumsplit M n ω]; ring)
    have hmk := sqrt_integral_sq_sub_le
      (memLp_partialSum hmeas hstat hmem2 (Finset.range n))
      (memLp_partialSum (hmZ M) (hstatZ M) (hZ2 M) (Finset.range n))
    have hc0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    rw [hY, Real.sqrt_mul hc0, Real.sqrt_mul hc0, Real.sqrt_mul hc0]
    have := mul_le_mul_of_nonneg_left hmk (Real.sqrt_nonneg ((n : ℝ)⁻¹))
    linarith [this]
  have hsqrtZ0 : Tendsto (fun M : ℕ => Real.sqrt (sZ M)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hK1
    simpa using! this
  have hcmp1 : ∀ M : ℕ, Real.sqrt σ2 ≤ Real.sqrt (sY M) + Real.sqrt (sZ M) := fun M =>
    le_of_tendsto_of_tendsto' hsqX ((hsqY M).add (hsqZ M)) (fun n => hmink M n)
  have hcmp2 : ∀ M : ℕ, Real.sqrt (sY M) ≤ Real.sqrt σ2 + Real.sqrt (sZ M) := fun M =>
    le_of_tendsto_of_tendsto' (hsqY M) (hsqX.add (hsqZ M)) (fun n => hmink' M n)
  have hsY0 : ∀ M : ℕ, 0 ≤ sY M := by
    intro M
    refine ge_of_tendsto' (hrateY M) fun n => ?_
    have : (0 : ℝ) ≤ variance (fun ω => ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) μ :=
      variance_nonneg _ _
    positivity
  have hsqrtY : Tendsto (fun M : ℕ => Real.sqrt (sY M)) atTop (𝓝 (Real.sqrt σ2)) := by
    have hd : Tendsto (fun M : ℕ => Real.sqrt (sY M) - Real.sqrt σ2) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun M => ?_) hsqrtZ0
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [hcmp1 M], by linarith [hcmp2 M]⟩
    have := hd.add_const (Real.sqrt σ2)
    simpa using this
  have hK2 : Tendsto sY atTop (𝓝 σ2) := by
    have h := hsqrtY.pow 2
    rw [Real.sq_sqrt hσ.le] at h
    exact h.congr fun M => Real.sq_sqrt (hsY0 M)
  -- ### 6. Assembly: three-term `ε`-argument
  have hRHS : charFun (gaussianReal 0 (Real.toNNReal σ2)) u
      = Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2)) := by
    rw [charFun_gaussianReal, Real.coe_toNNReal _ hσ.le]
    congr 1
    push_cast
    ring
  have hSmeasX : ∀ n : ℕ, Measurable fun ω => ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω :=
    fun n => Finset.measurable_sum _ fun t _ => hmeas _
  have hSmeasY : ∀ M n : ℕ,
      Measurable fun ω => ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) :=
    fun M n => Finset.measurable_sum _ fun t _ => hmY M _
  have hSmeasZ : ∀ M n : ℕ,
      Measurable fun ω => ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω) :=
    fun M n => Finset.measurable_sum _ fun t _ => hmZ M _
  have hcfX : ∀ n : ℕ, charFun (μ.map fun ω =>
      (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) u
      = ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ :=
    fun n => charFun_map_scaled (hSmeasX n) _ u
  have hcfY : ∀ M n : ℕ, charFun (μ.map fun ω =>
      (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)) u
      = ∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ) * Complex.I) ∂μ :=
    fun M n => charFun_map_scaled (hSmeasY M n) _ u
  simp only [hcfX, hRHS]
  -- the truncated central limit theorem, in integral form
  have hCLTY : ∀ M : ℕ, 0 < sY M → Tendsto (fun n : ℕ => ∫ ω, Complex.exp
      (((u * (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ)
        * Complex.I) ∂μ) atTop (𝓝 (Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2)))) := by
    intro M hpos
    have hpos' : 0 < acvf (fun t ω => gY M (X t ω)) μ 0
        + 2 * ∑' j : ℕ, acvf (fun t ω => gY M (X t ω)) μ ((j : ℤ) + 1) := by
      rw [← hsY M]; exact hpos
    have h := clt_of_bounded_alphaMixing (hmY M) (hstatY M) (hbddY M) (hmeanY M)
      (summable_alphaCoeff_of_rpow hθ0 hθ1 (hαYsum M)) hpos' u
    have hR : charFun (gaussianReal 0 (Real.toNNReal (acvf (fun t ω => gY M (X t ω)) μ 0
        + 2 * ∑' j : ℕ, acvf (fun t ω => gY M (X t ω)) μ ((j : ℤ) + 1)))) u
        = Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2)) := by
      rw [charFun_gaussianReal, Real.coe_toNNReal _ hpos'.le, ← hsY M]
      congr 1
      push_cast
      ring
    rw [hR] at h
    simpa only [hcfY] using h
  -- the truncation error, uniformly in `n`
  have hdiff : ∀ (M n : ℕ), 1 ≤ n →
      dist (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ) * Complex.I) ∂μ)
      ≤ |u| * Real.sqrt ((n : ℝ)⁻¹ *
          ∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) := by
    intro M n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs0 : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    have hiX := integrable_expI_block (μ := μ) (hSmeasX n) (u * (Real.sqrt n)⁻¹)
    have hiY := integrable_expI_block (μ := μ) (hSmeasY M n) (u * (Real.sqrt n)⁻¹)
    rw [dist_eq_norm, ← integral_sub hiX hiY]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hptw : ∀ ω : Ω, ‖Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I)
        - Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ) * Complex.I)‖
        ≤ |u| * (Real.sqrt (n : ℝ))⁻¹ *
          |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| := by
      intro ω
      set aX : ℝ := u * (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω with haX
      set aY : ℝ := u * (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω)
        with haY
      have harg : (aX : ℂ) * Complex.I
          = (aY : ℂ) * Complex.I + Complex.I * ((aX - aY : ℝ) : ℂ) := by
        push_cast; ring
      have hfac : Complex.exp ((aX : ℂ) * Complex.I) - Complex.exp ((aY : ℂ) * Complex.I)
          = Complex.exp ((aY : ℂ) * Complex.I) *
            (Complex.exp (Complex.I * ((aX - aY : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, mul_one, ← Complex.exp_add, ← harg]
      rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
      have hd : aX - aY
          = u * (Real.sqrt (n : ℝ))⁻¹ * ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω) := by
        rw [haX, haY, ← mul_sub, hsumsplit M n ω]
        ring
      have habs : |u * (Real.sqrt (n : ℝ))⁻¹ *
            ∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)|
          = |u| * (Real.sqrt (n : ℝ))⁻¹ *
            |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹)]
      rw [Real.norm_eq_abs, hd, habs]
    refine (integral_mono ((hiX.sub hiY).norm) ?_ hptw).trans ?_
    · exact (((memLp_partialSum (hmZ M) (hstatZ M) (hZ2 M) (Finset.range n)).integrable
        one_le_two).abs.const_mul _)
    · have hIC : ∫ ω, |u| * (Real.sqrt (n : ℝ))⁻¹ *
            |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| ∂μ
          = |u| * (Real.sqrt (n : ℝ))⁻¹ *
            ∫ ω, |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| ∂μ := integral_const_mul _ _
      rw [hIC]
      have hcs : ∫ ω, |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| ∂μ
          ≤ Real.sqrt (∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) := by
        have h0 : (0 : ℝ) ≤ ∫ ω, |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| ∂μ :=
          integral_nonneg fun _ => abs_nonneg _
        calc ∫ ω, |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| ∂μ
            = Real.sqrt ((∫ ω, |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| ∂μ) ^ 2) :=
              (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt (∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) :=
              Real.sqrt_le_sqrt (sq_integral_abs_le
                (memLp_partialSum (hmZ M) (hstatZ M) (hZ2 M) (Finset.range n)))
      have hsq : Real.sqrt ((n : ℝ)⁻¹ *
          ∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ)
          = (Real.sqrt (n : ℝ))⁻¹ *
            Real.sqrt (∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_inv]
      rw [hsq]
      have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg _
      have hinv0 : (0 : ℝ) ≤ (Real.sqrt (n : ℝ))⁻¹ := by positivity
      calc |u| * (Real.sqrt (n : ℝ))⁻¹ *
            ∫ ω, |∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)| ∂μ
          ≤ |u| * (Real.sqrt (n : ℝ))⁻¹ *
            Real.sqrt (∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) := by
            have : (0 : ℝ) ≤ |u| * (Real.sqrt (n : ℝ))⁻¹ := by positivity
            exact mul_le_mul_of_nonneg_left hcs this
        _ = |u| * ((Real.sqrt (n : ℝ))⁻¹ *
            Real.sqrt (∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ)) := by
            ring
  -- choose the truncation level
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by linarith
  have hExp : Tendsto (fun M : ℕ => Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2))) atTop
      (𝓝 (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2)))) := by
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have h1 : Tendsto (fun M : ℕ => ((sY M : ℝ) : ℂ)) atTop (𝓝 ((σ2 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hK2
    exact ((h1.mul tendsto_const_nhds).div_const 2).neg
  have hf1 : ∀ᶠ M : ℕ in atTop, |u| * Real.sqrt (sZ M) < ε / 4 := by
    have h0 : Tendsto (fun M : ℕ => |u| * Real.sqrt (sZ M)) atTop (𝓝 0) := by
      simpa using hsqrtZ0.const_mul |u|
    exact h0.eventually (gt_mem_nhds hε4)
  have hf2 : ∀ᶠ M : ℕ in atTop, 0 < sY M := hK2.eventually (lt_mem_nhds hσ)
  have hf3 : ∀ᶠ M : ℕ in atTop,
      dist (Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2)))
        (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2))) < ε / 4 := by
    have h := hExp.eventually (Metric.ball_mem_nhds
      (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2))) hε4)
    simpa only [Metric.mem_ball] using h
  obtain ⟨M, h1, h2, h3⟩ := (hf1.and (hf2.and hf3)).exists
  -- with `M` fixed, both remaining terms are eventually small
  have he1 : ∀ᶠ n : ℕ in atTop, |u| * Real.sqrt ((n : ℝ)⁻¹ *
      ∫ ω, (∑ t ∈ Finset.range n, gZ M (X ((t : ℤ) + 1) ω)) ^ 2 ∂μ) < ε / 4 :=
    ((hsqZ M).const_mul |u|).eventually (gt_mem_nhds h1)
  have he2 : ∀ᶠ n : ℕ in atTop, dist (∫ ω, Complex.exp
      (((u * (Real.sqrt n)⁻¹ * ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ)
        * Complex.I) ∂μ) (Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2))) < ε / 4 := by
    have h := (hCLTY M h2).eventually (Metric.ball_mem_nhds
      (Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2))) hε4)
    simpa only [Metric.mem_ball] using h
  obtain ⟨N, hN⟩ := eventually_atTop.1 (he1.and (he2.and (eventually_ge_atTop 1)))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hn1, hn2, hn3⟩ := hN n hn
  have hstep := hdiff M n hn3
  calc dist (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
          ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ)
        (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2)))
      ≤ dist (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω : ℝ) : ℂ) * Complex.I) ∂μ)
          (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ) * Complex.I) ∂μ)
        + dist (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
            ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ) * Complex.I) ∂μ)
          (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2))) := dist_triangle _ _ _
    _ < ε := by
        have h4 : dist (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ) * Complex.I) ∂μ)
            (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2)))
            ≤ dist (∫ ω, Complex.exp (((u * (Real.sqrt n)⁻¹ *
              ∑ t ∈ Finset.range n, gY M (X ((t : ℤ) + 1) ω) : ℝ) : ℂ) * Complex.I) ∂μ)
              (Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2)))
              + dist (Complex.exp (-((sY M : ℂ) * (u : ℂ) ^ 2 / 2)))
                (Complex.exp (-((σ2 : ℂ) * (u : ℂ) ^ 2 / 2))) := dist_triangle _ _ _
        linarith

/-! ### α-mixing ⇒ ergodicity of the shift, and the SLLN (FY Proposition 2.8)

The route the book cites: the path law `ν = μ ∘ (ω ↦ (X_t ω)_t)⁻¹` on `ℤ → ℝ` is shift
invariant by strict stationarity, `α(n) → 0` makes the shift ergodic for `ν`, and Birkhoff's
pointwise ergodic theorem (`ForMathlib/Ergodic/Birkhoff.lean`) applied to the coordinate
observable gives the strong law. The bricks below rebuild, privately, the path-space
machinery of `Mixing/Relations.lean` (which is `private` there) and add the ergodicity step.
-/

section BirkhoffSLLN

omit [MeasurableSpace Ω] in
private lemma comap_path_cyl (X : ℤ → Ω → ℝ) (k : ℤ) (S : Set ℤ) :
    MeasurableSpace.comap (fun ω (t : ℤ) => X (t + k) ω) (cylinderEvents S)
      = ⨆ s ∈ S, MeasurableSpace.comap (X (s + k)) inferInstance := by
  unfold cylinderEvents
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun s => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun _ => ?_
  rw [MeasurableSpace.comap_comp]
  rfl

omit [MeasurableSpace Ω] in
private lemma iSup_Iic_sh (X : ℤ → Ω → ℝ) (c k : ℤ) :
    (⨆ s ∈ Set.Iic c, MeasurableSpace.comap (X (s + k)) inferInstance) = sigmaLE X (c + k) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (iSup₂_le fun u hu => ?_)
  · exact le_iSup₂_of_le (s + k) (Set.mem_Iic.mpr (by have : s ≤ c := hs; omega)) le_rfl
  · refine le_iSup₂_of_le (u - k) (Set.mem_Iic.mpr (by have : u ≤ c + k := hu; omega)) ?_
    exact le_of_eq (by rw [sub_add_cancel])

omit [MeasurableSpace Ω] in
private lemma iSup_Ici_sh (X : ℤ → Ω → ℝ) (c k : ℤ) :
    (⨆ s ∈ Set.Ici c, MeasurableSpace.comap (X (s + k)) inferInstance) = sigmaGE X (c + k) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (iSup₂_le fun u hu => ?_)
  · exact le_iSup₂_of_le (s + k) (Set.mem_Ici.mpr (by have : c ≤ s := hs; omega)) le_rfl
  · refine le_iSup₂_of_le (u - k) (Set.mem_Ici.mpr (by have : c + k ≤ u := hu; omega)) ?_
    exact le_of_eq (by rw [sub_add_cancel])

private lemma alphaMix_comap {V : Ω → (ℤ → ℝ)} (hV : Measurable V)
    {ν : Measure (ℤ → ℝ)} (hν : μ.map V = ν)
    (m₁ m₂ : MeasurableSpace (ℤ → ℝ)) (h₁ : m₁ ≤ MeasurableSpace.pi)
    (h₂ : m₂ ≤ MeasurableSpace.pi) :
    alphaMixCoeff μ (m₁.comap V) (m₂.comap V)
      = @alphaMixCoeff (ℤ → ℝ) MeasurableSpace.pi ν m₁ m₂ := by
  have hval : ∀ {S : Set (ℤ → ℝ)},
      @MeasurableSet (ℤ → ℝ) MeasurableSpace.pi S → ν S = μ (V ⁻¹' S) := by
    intro S hS
    rw [← hν]
    exact Measure.map_apply hV hS
  unfold alphaMixCoeff
  refine congrArg sSup (Set.ext fun r => ?_)
  constructor
  · rintro ⟨A, B, ⟨A', hA', rfl⟩, ⟨B', hB', rfl⟩, rfl⟩
    refine ⟨A', B', hA', hB', ?_⟩
    have e3 : ν (A' ∩ B') = μ (V ⁻¹' A' ∩ V ⁻¹' B') := by
      rw [hval (@MeasurableSet.inter (ℤ → ℝ) MeasurableSpace.pi _ _ (h₁ _ hA') (h₂ _ hB')),
        Set.preimage_inter]
    rw [hval (h₁ _ hA'), hval (h₂ _ hB'), e3]
  · rintro ⟨A', B', hA', hB', rfl⟩
    refine ⟨V ⁻¹' A', V ⁻¹' B', ⟨A', hA', rfl⟩, ⟨B', hB', rfl⟩, ?_⟩
    have e3 : ν (A' ∩ B') = μ (V ⁻¹' A' ∩ V ⁻¹' B') := by
      rw [hval (@MeasurableSet.inter (ℤ → ℝ) MeasurableSpace.pi _ _ (h₁ _ hA') (h₂ _ hB')),
        Set.preimage_inter]
    rw [hval (h₁ _ hA'), hval (h₂ _ hB'), e3]

private lemma map_fintuple_sh {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℤ) (s : Finset ℤ) :
    (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω)
      = μ.map fun ω (i : s) => X (i : ℤ) ω := by
  classical
  set e : s ≃ Fin s.card := s.equivFin with he
  set t : Fin s.card → ℤ := fun j => ((e.symm j : s) : ℤ) with ht
  set Φ : (Fin s.card → ℝ) → (∀ _ : s, ℝ) := fun p i => p (e i) with hΦdef
  have hΦ : Measurable Φ := measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  have hte : ∀ i : s, t (e i) = (i : ℤ) := by
    intro i; simp [ht]
  have hcomp : ∀ c : ℤ, Measurable fun ω (j : Fin s.card) => X (t j + c) ω :=
    fun c => measurable_pi_lambda _ fun j => hmeas _
  have hpush : ∀ c : ℤ,
      (μ.map fun ω (j : Fin s.card) => X (t j + c) ω).map Φ
        = μ.map fun ω (i : s) => X ((i : ℤ) + c) ω := by
    intro c
    rw [Measure.map_map hΦ (hcomp c)]
    congr 1
    funext ω i
    simp [hΦdef, hte i]
  have h0 : (μ.map fun ω (j : Fin s.card) => X (t j + 0) ω)
      = μ.map fun ω (j : Fin s.card) => X (t j) ω := by simp
  calc (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω)
      = (μ.map fun ω (j : Fin s.card) => X (t j + k) ω).map Φ := (hpush k).symm
    _ = (μ.map fun ω (j : Fin s.card) => X (t j) ω).map Φ := by rw [hstat s.card t k]
    _ = (μ.map fun ω (j : Fin s.card) => X (t j + 0) ω).map Φ := by rw [h0]
    _ = μ.map fun ω (i : s) => X ((i : ℤ) + 0) ω := hpush 0
    _ = μ.map fun ω (i : s) => X (i : ℤ) ω := by simp

private lemma map_path_sh {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t)) (k : ℤ) :
    (μ.map fun ω (u : ℤ) => X (u + k) ω) = μ.map fun ω (u : ℤ) => X u ω := by
  have hTm : Measurable fun ω (u : ℤ) => X (u + k) ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  refine ext_of_generate_finite (measurableCylinders fun _ : ℤ => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders C).mp hC
    have hcyl : MeasurableSet (cylinder s S) := MeasurableSet.cylinder (α := fun _ : ℤ => ℝ) s hSm
    have hT : Measurable fun ω (i : s) => X ((i : ℤ) + k) ω :=
      measurable_pi_lambda _ fun _ => hmeas _
    have hU : Measurable fun ω (i : s) => X (i : ℤ) ω :=
      measurable_pi_lambda _ fun _ => hmeas _
    have eT : (μ.map fun ω (u : ℤ) => X (u + k) ω) (cylinder s S)
        = (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω) S := by
      rw [Measure.map_apply hTm hcyl, Measure.map_apply hT hSm]
      rfl
    have eU : (μ.map fun ω (u : ℤ) => X u ω) (cylinder s S)
        = (μ.map fun ω (i : s) => X (i : ℤ) ω) S := by
      rw [Measure.map_apply hUm hcyl, Measure.map_apply hU hSm]
      rfl
    rw [eT, eU, map_fintuple_sh hstat hmeas k s]
  · rw [Measure.map_apply hTm MeasurableSet.univ, Measure.map_apply hUm MeasurableSet.univ]
    simp


/-! ### Path law and shift -/

private noncomputable def pathLaw (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Measure (ℤ → ℝ) :=
  μ.map fun ω (u : ℤ) => X u ω

private def shiftPath : (ℤ → ℝ) → (ℤ → ℝ) := fun y u => y (u + 1)

private lemma measurable_shiftPath : Measurable shiftPath :=
  measurable_pi_lambda _ fun u => measurable_pi_apply (u + 1)

private lemma shiftPath_iterate : ∀ (n : ℕ) (y : ℤ → ℝ) (u : ℤ),
    shiftPath^[n] y u = y (u + n) := by
  intro n
  induction n with
  | zero => intro y u; simp
  | succ n ih =>
      intro y u
      rw [Function.iterate_succ_apply, ih (shiftPath y) u]
      change y (u + n + 1) = y (u + ((n : ℤ) + 1))
      congr 1
      ring

private lemma measurePreserving_shiftPath [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ) :
    MeasurePreserving shiftPath (pathLaw X μ) (pathLaw X μ) := by
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  refine ⟨measurable_shiftPath, ?_⟩
  simp only [pathLaw]
  rw [Measure.map_map measurable_shiftPath hUm]
  exact map_path_sh hstat hmeas 1

private lemma symmDiff_inter_subset {γ : Type*} (P Q P' Q' : Set γ) :
    (P ∩ Q) ∆ (P' ∩ Q') ⊆ (P ∆ P') ∪ (Q ∆ Q') := by
  intro x hx
  simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union] at *
  tauto

private lemma preimage_symmDiff' {γ δ : Type*} (f : γ → δ) (s t : Set δ) :
    f ⁻¹' (s ∆ t) = (f ⁻¹' s) ∆ (f ⁻¹' t) := by
  ext x; simp only [Set.mem_preimage, Set.mem_symmDiff]

private lemma measurableSet_cylinder_Iic (s : Finset ℤ) (S : Set (∀ _ : s, ℝ))
    (hS : MeasurableSet S) (p : ℤ) (hp : ∀ i ∈ s, i ≤ p) :
    MeasurableSet[cylinderEvents (Set.Iic p)]
      (cylinder (α := fun _ : ℤ => ℝ) s S) := by
  letI : MeasurableSpace (ℤ → ℝ) := cylinderEvents (Set.Iic p)
  have hmap : Measurable fun (y : ℤ → ℝ) (i : s) => y (i : ℤ) :=
    measurable_pi_iff.2 fun i => measurable_cylinderEvent_apply (Set.mem_Iic.2 (hp i i.2))
  exact hmap hS

private lemma measurableSet_shift_cylinder_Ici (s : Finset ℤ) (S : Set (∀ _ : s, ℝ))
    (hS : MeasurableSet S) (c : ℤ) (k : ℕ) (hc : ∀ i ∈ s, c ≤ (i : ℤ) + k) :
    MeasurableSet[cylinderEvents (Set.Ici c)]
      (shiftPath^[k] ⁻¹' cylinder (α := fun _ : ℤ => ℝ) s S) := by
  have heq : shiftPath^[k] ⁻¹' cylinder (α := fun _ : ℤ => ℝ) s S
      = (fun (y : ℤ → ℝ) (i : s) => y ((i : ℤ) + k)) ⁻¹' S := by
    ext y
    have hfun : s.restrict (shiftPath^[k] y) = fun i : s => y ((i : ℤ) + k) := by
      funext i; exact shiftPath_iterate k y _
    simp only [Set.mem_preimage, mem_cylinder, hfun]
  rw [heq]
  letI : MeasurableSpace (ℤ → ℝ) := cylinderEvents (Set.Ici c)
  have hmap : Measurable fun (y : ℤ → ℝ) (i : s) => y ((i : ℤ) + k) :=
    measurable_pi_iff.2 fun i => measurable_cylinderEvent_apply (Set.mem_Ici.2 (hc i i.2))
  exact hmap hS

private lemma preErgodic_shiftPath [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (hstat : IsStrictlyStationary X μ)
    (hmix : IsAlphaMixing X μ) :
    PreErgodic shiftPath (pathLaw X μ) := by
  classical
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  have hνeq : (μ.map fun ω (u : ℤ) => X u ω) = pathLaw X μ := rfl
  haveI hνP : IsProbabilityMeasure (pathLaw X μ) := by
    rw [← hνeq]; exact Measure.isProbabilityMeasure_map hUm.aemeasurable
  have hMP : MeasurePreserving shiftPath (pathLaw X μ) (pathLaw X μ) :=
    measurePreserving_shiftPath hmeas hstat
  -- the α-coefficient of the path law between two cylinder σ-algebras is the process one
  have hcoef : ∀ (p : ℤ) (m : ℕ),
      @alphaMixCoeff (ℤ → ℝ) MeasurableSpace.pi (pathLaw X μ) (cylinderEvents (Set.Iic p))
          (cylinderEvents (Set.Ici (p + (m : ℤ)))) = alphaCoeff X μ m := by
    intro p m
    have hL : MeasurableSpace.comap (fun ω (u : ℤ) => X u ω) (cylinderEvents (Set.Iic p))
        = sigmaLE X p := by
      have h := comap_path_cyl X 0 (Set.Iic p)
      simp only [add_zero] at h
      exact h
    have hG : MeasurableSpace.comap (fun ω (u : ℤ) => X u ω)
        (cylinderEvents (Set.Ici (p + (m : ℤ)))) = sigmaGE X (p + (m : ℤ)) := by
      have h := comap_path_cyl X 0 (Set.Ici (p + (m : ℤ)))
      simp only [add_zero] at h
      exact h
    rw [← alphaMix_comap hUm hνeq (cylinderEvents (Set.Iic p))
      (cylinderEvents (Set.Ici (p + (m : ℤ)))) cylinderEvents_le_pi cylinderEvents_le_pi,
      hL, hG]
    exact hstat.alphaMixCoeff_shift hmeas p m
  refine ⟨fun A hA hinv => ?_⟩
  set a : ℝ := (pathLaw X μ).real A with hadef
  have ha0 : 0 ≤ a := measureReal_nonneg
  have ha1 : a ≤ 1 := by
    rw [hadef]
    simpa using measureReal_mono (μ := pathLaw X μ) (Set.subset_univ A)
  have hAn : ∀ n : ℕ, shiftPath^[n] ⁻¹' A = A := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ, Set.preimage_comp, ih, hinv]
  -- the approximation-plus-mixing estimate
  have key : ∀ δ : ℝ, 0 < δ → ∀ m : ℕ, |a - a * a| ≤ 4 * δ + alphaCoeff X μ m := by
    intro δ hδ m
    obtain ⟨B, hBc, hBA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := pathLaw X μ) isSetRing_measurableCylinders
      ⟨{Set.univ}, Set.countable_singleton _,
        by simpa using univ_mem_measurableCylinders fun _ : ℤ => ℝ, by simp⟩
      generateFrom_measurableCylinders.symm hA (ENNReal.ofReal_pos.2 hδ)
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders B).mp hBc
    set p : ℤ := if h : s.Nonempty then s.max' h else 0 with hp
    set q : ℤ := if h : s.Nonempty then s.min' h else 0 with hq
    have hple : ∀ i ∈ s, i ≤ p := by
      intro i hi
      have hne : s.Nonempty := ⟨i, hi⟩
      rw [hp, dif_pos hne]
      exact Finset.le_max' s i hi
    have hqle : ∀ i ∈ s, q ≤ i := by
      intro i hi
      have hne : s.Nonempty := ⟨i, hi⟩
      rw [hq, dif_pos hne]
      exact Finset.min'_le s i hi
    have hqp : q ≤ p := by
      by_cases hne : s.Nonempty
      · obtain ⟨i, hi⟩ := hne
        exact le_trans (hqle i hi) (hple i hi)
      · rw [hp, hq, dif_neg hne, dif_neg hne]
    set n : ℕ := (p - q + (m : ℤ)).toNat with hndef
    have hn : (n : ℤ) = p - q + (m : ℤ) := Int.toNat_of_nonneg (by omega)
    have hci : ∀ i ∈ s, p + (m : ℤ) ≤ (i : ℤ) + (n : ℤ) := by
      intro i hi
      have := hqle i hi
      omega
    have hB1 : MeasurableSet[cylinderEvents (Set.Iic p)]
        (cylinder (α := fun _ : ℤ => ℝ) s S) :=
      measurableSet_cylinder_Iic s S hSm p hple
    have hB2 : MeasurableSet[cylinderEvents (Set.Ici (p + (m : ℤ)))]
        (shiftPath^[n] ⁻¹' cylinder (α := fun _ : ℤ => ℝ) s S) :=
      measurableSet_shift_cylinder_Ici s S hSm (p + (m : ℤ)) n hci
    set Cy : Set (ℤ → ℝ) := cylinder (α := fun _ : ℤ => ℝ) s S with hCy
    set Cn : Set (ℤ → ℝ) := shiftPath^[n] ⁻¹' Cy with hCn
    have hCyM : MeasurableSet Cy := MeasurableSet.cylinder (α := fun _ : ℤ => ℝ) s hSm
    have hCnM : MeasurableSet Cn := ((hMP.iterate n).measurable) hCyM
    set b : ℝ := (pathLaw X μ).real Cy with hbdef
    have hb0 : 0 ≤ b := measureReal_nonneg
    have hb1 : b ≤ 1 := by
      rw [hbdef]; simpa using measureReal_mono (μ := pathLaw X μ) (Set.subset_univ Cy)
    have hCnval : (pathLaw X μ) Cn = (pathLaw X μ) Cy :=
      (hMP.iterate n).measure_preimage hCyM.nullMeasurableSet
    have hCnreal : (pathLaw X μ).real Cn = b := by rw [hbdef, measureReal_def, measureReal_def,
      hCnval]
    -- the approximation bound
    have hdelta : (pathLaw X μ).real (Cy ∆ A) ≤ δ := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hδ.le hBA.le
    have hba : |b - a| ≤ δ :=
      le_trans (abs_measureReal_sub_le_measureReal_symmDiff hCyM.nullMeasurableSet
        hA.nullMeasurableSet) hdelta
    -- the intersection bound
    have hsymm2 : (pathLaw X μ).real ((Cy ∩ Cn) ∆ (A ∩ A)) ≤ 2 * δ := by
      have hsub : (Cy ∩ Cn) ∆ (A ∩ A) ⊆ (Cy ∆ A) ∪ (Cn ∆ (shiftPath^[n] ⁻¹' A)) := by
        rw [hAn n]
        exact symmDiff_inter_subset _ _ _ _
      have hpre : Cn ∆ (shiftPath^[n] ⁻¹' A) = shiftPath^[n] ⁻¹' (Cy ∆ A) := by
        rw [hCn, preimage_symmDiff']
      have hmm : (pathLaw X μ).real (shiftPath^[n] ⁻¹' (Cy ∆ A))
          = (pathLaw X μ).real (Cy ∆ A) := by
        rw [measureReal_def, measureReal_def,
          (hMP.iterate n).measure_preimage (hCyM.symmDiff hA).nullMeasurableSet]
      calc (pathLaw X μ).real ((Cy ∩ Cn) ∆ (A ∩ A))
          ≤ (pathLaw X μ).real ((Cy ∆ A) ∪ (Cn ∆ (shiftPath^[n] ⁻¹' A))) :=
            measureReal_mono hsub
        _ ≤ (pathLaw X μ).real (Cy ∆ A)
              + (pathLaw X μ).real (Cn ∆ (shiftPath^[n] ⁻¹' A)) := measureReal_union_le _ _
        _ = 2 * (pathLaw X μ).real (Cy ∆ A) := by rw [hpre, hmm]; ring
        _ ≤ 2 * δ := by linarith
    have hAA : A ∩ A = A := Set.inter_self A
    have b1 : |a - (pathLaw X μ).real (Cy ∩ Cn)| ≤ 2 * δ := by
      rw [hAA] at hsymm2
      rw [abs_sub_comm, hadef]
      exact le_trans (abs_measureReal_sub_le_measureReal_symmDiff
        (hCyM.inter hCnM).nullMeasurableSet hA.nullMeasurableSet) hsymm2
    have b2 : |(pathLaw X μ).real (Cy ∩ Cn) - b * b| ≤ alphaCoeff X μ m := by
      have hle : |((pathLaw X μ) (Cy ∩ Cn)).toReal
            - ((pathLaw X μ) Cy).toReal * ((pathLaw X μ) Cn).toReal|
          ≤ @alphaMixCoeff (ℤ → ℝ) MeasurableSpace.pi (pathLaw X μ)
              (cylinderEvents (Set.Iic p)) (cylinderEvents (Set.Ici (p + (m : ℤ)))) :=
        le_csSup alphaMixCoeff_set_bddAbove ⟨Cy, Cn, hB1, hB2, rfl⟩
      rw [hcoef p m] at hle
      have e1 : ((pathLaw X μ) Cy).toReal * ((pathLaw X μ) Cn).toReal = b * b := by
        rw [hCnval, hbdef, measureReal_def]
      rw [measureReal_def, ← e1]
      exact hle
    have b3 : |b * b - a * a| ≤ 2 * δ := by
      have hfac : b * b - a * a = (b - a) * (b + a) := by ring
      rw [hfac, abs_mul]
      have h1 : |b + a| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
      have h2 : (0 : ℝ) ≤ |b - a| := abs_nonneg _
      nlinarith [abs_nonneg (b + a)]
    have t1 : |a - a * a| ≤ |a - (pathLaw X μ).real (Cy ∩ Cn)|
        + |(pathLaw X μ).real (Cy ∩ Cn) - a * a| := abs_sub_le _ _ _
    have t2 : |(pathLaw X μ).real (Cy ∩ Cn) - a * a|
        ≤ |(pathLaw X μ).real (Cy ∩ Cn) - b * b| + |b * b - a * a| := abs_sub_le _ _ _
    linarith
  -- let δ → 0 and m → ∞
  have hzero : a - a * a = 0 := by
    by_contra hne
    have hpos : 0 < |a - a * a| := abs_pos.2 hne
    obtain ⟨m, hm⟩ : ∃ m : ℕ, alphaCoeff X μ m < |a - a * a| / 2 :=
      (hmix.eventually (gt_mem_nhds (by linarith))).exists
    have := key (|a - a * a| / 8) (by linarith) m
    linarith
  have hcases : a = 0 ∨ a = 1 := by
    rcases mul_eq_zero.1 (show a * (1 - a) = 0 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hAval : (pathLaw X μ) A = ENNReal.ofReal a := by
    rw [hadef, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [eventuallyConst_set']
  rcases hcases with h | h
  · exact Or.inl (ae_eq_empty.2 (by rw [hAval, h]; simp))
  · refine Or.inr (ae_eq_univ.2 ?_)
    rw [prob_compl_eq_one_sub hA, hAval, h]
    simp

end BirkhoffSLLN

/-- **DEBT (Doob 1953 / Ibragimov–Linnik 1971; FY Proposition 2.8)**: the strong law
for α-mixing strictly stationary sequences with a first moment. The cited route is
"α-mixing ⇒ ergodicity" + the Birkhoff pointwise ergodic theorem, which the Mathlib
pin does not provide.

**STATUS (wave `ts/s10b`): PROVED, axiom-clean**, by exactly the cited route. The wave-`ts/s10`
four-item build list below is executed in full; the moment-route analysis that follows it is
still the reason this is the *only* available route, and is kept.

**No moment/Borel–Cantelli route exists under the frozen hypotheses.** They are exactly
`E|X_0| < ∞` (`hL1`) and `α(n) → 0` (`hmix`, i.e. `IsAlphaMixing`, which is *convergence to
zero with no rate*). In particular:
* there is **no second moment**, so Chebyshev is unavailable and the subsequence
  (`n = m²`) + Borel–Cantelli argument cannot even be started. The fourth-moment brick of
  this file (`m4_moment4_le`, `m4_tendsto_moment4_div_cube`) needs `|X| ≤ C` *and*
  `Σ α(j) < ∞`; **neither** is assumed here;
* adding a second moment would not help: with `α(n) → 0` and no rate, Davydov
  (`Mixing/Inequalities.abs_covariance_le_davydov`) gives `|γ(n)| ≤ 8 α(n)^{1−2/δ} ‖X_0‖_δ²`
  only under a `δ > 2` moment, and even then `Σ|γ(n)|` need not converge — the ACVF of an
  `α`-mixing stationary sequence can fail to be summable, so `n⁻¹ Var S_n` need not even
  be bounded;
* truncating at level `n` restores all moments but the resulting variance bound is
  `Σ_{|k|<n} |γ_n(k)|`, which again needs a mixing **rate** to be `o(n)`.
So the cited ergodic route is not one convenient proof among several: it is the only one
the hypotheses support, and it is what the statement is *equivalent* to (Birkhoff for an
ergodic shift is exactly this statement for the coordinate process).

**The former named residue — the Birkhoff pointwise ergodic theorem — is now supplied by
`StatLean/TimeSeries/ForMathlib/Ergodic/Birkhoff.lean`** (`maximal_ergodic`,
`birkhoffAverage_ae_tendsto_condexp`, `birkhoffAverage_ae_tendsto_integral`; that file is
`0`-sorry and axiom-clean). The pin's own `Mathlib/Dynamics/BirkhoffSum/*` still carry only
the algebraic bookkeeping for `birkhoffSum`/`birkhoffAverage`, and
`Mathlib/Analysis/InnerProductSpace/MeanErgodic.lean` is von Neumann's **mean** (`L²`)
ergodic theorem, which does not give the a.e. statement.

**How the four items were executed.**
(i) The path law `ν = μ.map (fun ω t => X t ω)` on `ℤ → ℝ` is shift invariant: `map_path_sh`
    above (`ext_of_generate_finite` over `measurableCylinders`, reducing to the
    finite-dimensional invariance of `IsStrictlyStationary` through `s ≃ Fin s.card`).
(ii) `α(n) → 0 ⇒ the shift is ergodic for ν`: `preErgodic_shiftPath`. For measurable
    shift-invariant `A` and any `δ > 0`, a cylinder `B = cylinder s S` with
    `ν (B Δ A) < δ` exists — **the approximation step *is* in the pin**, contrary to what
    wave `ts/s10` recorded: `MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetRing`
    (`Mathlib/MeasureTheory/Measure/MeasuredSets.lean`) applied to the set ring
    `MeasureTheory.isSetRing_measurableCylinders`
    (`Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean`) with
    `generateFrom_measurableCylinders`. With `p = max s`, `q = min s` and `n` chosen so that
    `q + n = p + m`, the cylinder is `cylinderEvents (Iic p)`-measurable and `σ^{-n}B` is
    `cylinderEvents (Ici (p+m))`-measurable, so the α-bound `le_csSup` gives
    `|ν(B ∩ σ^{-n}B) − ν(B) ν(σ^{-n}B)| ≤ α(m)`, using the transfer of the coefficient to the
    path law (`alphaMix_comap`) and the **re-anchoring lemma**
    `IsStrictlyStationary.alphaMixCoeff_shift` of `Mixing/Relations.lean` — a cylinder sits in
    an arbitrary finite window, not in `(−∞, 0]`, so re-anchoring is genuinely needed.
    Together with `|ν(A) − ν(A)²| ≤ 4δ + α(m)` this forces `ν(A) ∈ {0,1}`.
(iii) `maximal_ergodic` (Garsia) and `birkhoffAverage_ae_tendsto_integral` in the new file.
(iv) Transport back to `Ω` along the path map, free via `MeasureTheory.ae_of_ae_map`.
**Indexing note.** The statement sums `X_1, …, X_n`, while `birkhoffSum shiftPath (· 0) n`
sums `y_0, …, y_{n−1}`; the two are matched by evaluating the a.e. statement at `σ y` rather
than by changing the observable, which is free because `σ` is measure preserving.

**Duplication note.** `Mixing/Relations.lean` proves items of the path-space machinery
(`comap_path_cylinderEvents`, `iSup_Iic_shift`, `iSup_Ici_shift`, `alphaMixCoeff_comap`,
`map_finsetTuple_shift`, `map_path_shift`) but keeps them `private`, i.e. file-scoped, so
they are re-proved verbatim above as `comap_path_cyl`, `iSup_Iic_sh`, `iSup_Ici_sh`,
`alphaMix_comap`, `map_fintuple_sh`, `map_path_sh`. Un-privatizing them in `Relations.lean`
would let this file drop ~130 lines. -/
theorem slln_of_alphaMixing_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    (hL1 : Integrable (X 0) μ)
    -- USER-INPUT: α-mixing; FY Prop 2.8
    (hmix : IsAlphaMixing X μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, X ((t : ℤ) + 1) ω) atTop
      (𝓝 (∫ ω', X 0 ω' ∂μ)) := by
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  have hνeq : (μ.map fun ω (u : ℤ) => X u ω) = pathLaw X μ := rfl
  haveI hνP : IsProbabilityMeasure (pathLaw X μ) := by
    rw [← hνeq]; exact Measure.isProbabilityMeasure_map hUm.aemeasurable
  have herg : Ergodic shiftPath (pathLaw X μ) :=
    ⟨measurePreserving_shiftPath hmeas hstat, preErgodic_shiftPath hmeas hstat hmix⟩
  have hgm : Measurable fun y : ℤ → ℝ => y 0 := measurable_pi_apply 0
  have hgint : Integrable (fun y : ℤ → ℝ => y 0) (pathLaw X μ) := by
    rw [← hνeq, integrable_map_measure hgm.aestronglyMeasurable hUm.aemeasurable]
    exact hL1
  have hgintegral : ∫ y, (fun y : ℤ → ℝ => y 0) y ∂(pathLaw X μ) = ∫ ω, X 0 ω ∂μ := by
    rw [← hνeq, integral_map hUm.aemeasurable hgm.aestronglyMeasurable]
  have hbirk := birkhoffAverage_ae_tendsto_integral herg measurable_shiftPath hgint
  rw [hgintegral] at hbirk
  have hshifted : ∀ᵐ y ∂(pathLaw X μ), Tendsto
      (fun n => birkhoffAverage ℝ shiftPath (fun y : ℤ → ℝ => y 0) n (shiftPath y)) atTop
      (𝓝 (∫ ω, X 0 ω ∂μ)) :=
    (measurePreserving_shiftPath hmeas hstat).quasiMeasurePreserving.ae hbirk
  have hform : ∀ (y : ℤ → ℝ) (n : ℕ),
      birkhoffAverage ℝ shiftPath (fun y : ℤ → ℝ => y 0) n (shiftPath y)
        = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, y ((t : ℤ) + 1) := by
    intro y n
    simp only [birkhoffAverage, birkhoffSum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : shiftPath^[k] (shiftPath y) = shiftPath^[k + 1] y :=
      (Function.iterate_succ_apply shiftPath k y).symm
    rw [h1]
    have h2 := shiftPath_iterate (k + 1) y 0
    rw [h2]
    congr 1
    push_cast
    ring
  refine ae_of_ae_map (p := fun y : ℤ → ℝ => Tendsto (fun n : ℕ =>
      (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, y ((t : ℤ) + 1)) atTop (𝓝 (∫ ω', X 0 ω' ∂μ)))
    hUm.aemeasurable ?_
  rw [hνeq]
  filter_upwards [hshifted] with y hy
  simpa only [hform y] using hy

end StatLean.TimeSeries
