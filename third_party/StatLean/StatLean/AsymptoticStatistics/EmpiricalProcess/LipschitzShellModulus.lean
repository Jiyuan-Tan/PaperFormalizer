module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChainingAssembly
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ParametricClassDonsker
public import StatLean.AsymptoticStatistics.ForMathlib.SqrtLogIntegral

@[expose] public section

/-!
# Lipschitz shell modulus bound — the clean bracketing route

Target (identical to `MEstimator.Rate.modulus_maximal_bound`'s conclusion):

    ∃ C > 0, ∃ ρ > 0, ∀ 0 < δ < ρ, ∀ n,
      ∫⁻ ξ, ‖𝔾ₙ‖_{M̄_δ} ∂μ ≤ ofReal (C · δ)

over the **fixed-center shell**
`M̄_δ = { ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ < δ }`.

## Why this route (bracketing, not covering)

The covering route (`centeredLipschitz_localizedModulus_bound`) requires
Rademacher **symmetrization**. The **bracketing**
localized maximal inequality `localizedChainBound_of_finiteEntropy`
(`ChainingAssembly.lean`, vdV Lemma 19.34) needs **no symmetrization**. This file
reuses that inequality.

## Route

1. `M̄_δ = paramClass (shellPsi m θ₀) (ball θ₀ δ)` (`shellSet_eq_paramClass`, `d ≥ 1`).
2. Finite entropy for the engine: `parametricClass_bracketingEntropyIntegral_lt_top`.
3. `M̄_δ ⊆ localizedDifferenceClass F P δq` with `δq := δ·(‖menv‖₂+1)`
   (`shellSet_subset_localized`): each `m_θ − m_{θ₀} = f − g` with `f = m_θ ∈ F`,
   `g = m_{θ₀} = 0 ∈ F`, and `eLpNorm (m_θ − m_{θ₀}) ≤ δ‖menv‖₂ ≤ δq`.
4. Apply the (M-lower-bounded) engine `localizedChainBound_shell_MLower`:
   `∫⁻ ‖𝔾ₙ‖_{localized} ≤ c·J_{[]}(δq, F) + c·(√n · envelope tail)`.
5. Relative bracketing entropy `J_{[]}(δq, F) ≤ Cent·δ`
   (`paramClass_shell_bracketingEntropyIntegral_le`): `N_{[]}` is *relative*.
6. Envelope tail `√n · ∫⁻ |Φ|·1{√n·M < |Φ|} ≤ Ctail·δ` (`shellTail_fold`):
   `Φ = 2δ|menv|`, `M ≥ cM·δq` ⟹ δ cancels (Chebyshev).

## Quantitative ingredients

Two estimates reduce to the **relative bracketing number** of the shell, where
`N_{[]}(s, F)` scales like the ratio `δ/s`, not like `1/s`:

* `paramClass_shell_bracketingEntropyIntegral_le` bounds the entropy integral.
* `localizedChainBound_shell_MLower` supplies the clamp-level lower bound. The
  base inequality `localizedChainBound_of_finiteEntropy` returns `∃ M > 0` without
  a lower bound, while the quantitative `≤ C·δ` conclusion needs `M ≥ cM·δq`. The
  engine's internal `M = min(θ/2, θ')` with `θ, θ' ≥ δq/(1+√log(1+N))` from
  `localized_{chain,global}Threshold_lower_bound`, and `N` (the localized-difference
  bracketing numbers at scales `δq`, `δq/2`) is a δ-free constant because `δq ∝ δ`
  makes the ratio `δ/δq` constant.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology NNReal

/-- Reindexing of the fixed-center difference `θ ↦ (ω ↦ m_θ ω − m_{θ₀} ω)` into the
`paramClass` shape: `Fin d` fibers all carry the same function (constant in `j`), so
`paramClass (shellPsi m θ₀) Θ = { m_θ − m_{θ₀} : θ ∈ Θ }` whenever `d ≥ 1`. -/
noncomputable def shellPsi {d : ℕ} {Ω : Type*}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) → Fin d → (Ω → ℝ) :=
  fun θ _ => fun ω => m θ ω - m θ₀ ω

/-- The **fixed-center shell** `M̄_δ = { ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ < δ }`. -/
def shellSet {d : ℕ} {Ω : Type*}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    Set (Ω → ℝ) :=
  {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
    g = fun ω => m θ ω - m θ₀ ω}

/-! ### The shell set as a `paramClass` -/

/-- For `d ≥ 1` the fixed-center shell equals the reindexed `paramClass`
over the Euclidean ball. The `Fin d` fiber is nonempty (`d ≥ 1`) and `shellPsi` is
constant in `j`, so the `∃ j` collapses. `θ ∈ ball θ₀ δ ↔ ‖θ − θ₀‖ < δ`
(`Metric.mem_ball`, `dist_eq_norm`). -/
theorem shellSet_eq_paramClass {d : ℕ} (hd : 1 ≤ d) {Ω : Type*}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d)) (δ : ℝ) :
    shellSet m θ₀ δ = paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ) := by
  ext g
  simp only [shellSet, paramClass, Set.mem_setOf_eq]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact ⟨θ, by rw [Metric.mem_ball, dist_eq_norm]; exact hθ, ⟨0, hd⟩, rfl⟩
  · rintro ⟨θ, hθ, _j, rfl⟩
    exact ⟨θ, by rw [← dist_eq_norm, ← Metric.mem_ball]; exact hθ, rfl⟩

/-! ### Regularity of the shell class -/

/-- The shell members are in `L²(P)`: `m_θ − m_{θ₀}` is dominated by `‖θ − θ₀‖·|menv|`
which is in `L²` because `menv ∈ L²`. -/
theorem shellPsi_memLp {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (θ : EuclideanSpace ℝ (Fin d)) (hθρ : θ ∈ Metric.closedBall θ₀ ρ) (j : Fin d) :
    MemLp (shellPsi m θ₀ θ j) 2 P := by
  refine MemLp.mono' (hmenv.norm.const_mul' ‖θ - θ₀‖)
    (((hm_meas θ).sub (hm_meas θ₀)).aestronglyMeasurable) ?_
  filter_upwards with x
  simp only [shellPsi]
  calc ‖m θ x - m θ₀ x‖ = |m θ x - m θ₀ x| := Real.norm_eq_abs _
    _ ≤ menv x * ‖θ - θ₀‖ := hLip θ hθρ θ₀ (Metric.mem_closedBall_self hρ.le) x
    _ ≤ ‖menv x‖ * ‖θ - θ₀‖ :=
        mul_le_mul_of_nonneg_right (Real.le_norm_self (menv x)) (norm_nonneg _)
    _ = ‖θ - θ₀‖ * ‖menv x‖ := mul_comm _ _

/-- The engine's `hLip` on `shellPsi`: `|shellPsi θ₁ j x − shellPsi θ₂ j x|
= |m_θ₁ x − m_θ₂ x| ≤ menv x · ‖θ₁ − θ₂‖`. -/
theorem shellPsi_lipschitz {d : ℕ} {Ω : Type*}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (θ₁ : EuclideanSpace ℝ (Fin d)) (hθ₁ρ : θ₁ ∈ Metric.closedBall θ₀ ρ)
    (θ₂ : EuclideanSpace ℝ (Fin d)) (hθ₂ρ : θ₂ ∈ Metric.closedBall θ₀ ρ)
    (j : Fin d) (x : Ω) :
    |shellPsi m θ₀ θ₁ j x - shellPsi m θ₀ θ₂ j x| ≤ menv x * ‖θ₁ - θ₂‖ := by
  simp only [shellPsi]
  have : m θ₁ x - m θ₀ x - (m θ₂ x - m θ₀ x) = m θ₁ x - m θ₂ x := by ring
  rw [this]
  exact hLip θ₁ hθ₁ρ θ₂ hθ₂ρ x

/-! ### The shell `L²` radius and localized inclusion -/

/-- `eLpNorm (m_θ − m_{θ₀}) ≤ δ · ‖menv‖₂` for `‖θ − θ₀‖ < δ`: pointwise
`|m_θ − m_{θ₀}| ≤ ‖θ − θ₀‖·|menv| ≤ δ·|menv|`, then `eLpNorm_mono` and
`eLpNorm_const_smul`. -/
theorem shellSet_radius_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) {θ : EuclideanSpace ℝ (Fin d)} (hθ : ‖θ - θ₀‖ < δ) :
    eLpNorm (fun ω => m θ ω - m θ₀ ω) 2 P
      ≤ ENNReal.ofReal δ * eLpNorm menv 2 P := by
  have hθρ : θ ∈ Metric.closedBall θ₀ ρ :=
    Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact (lt_of_lt_of_le hθ hδρ).le)
  have hpt : eLpNorm (fun ω => m θ ω - m θ₀ ω) 2 P
      ≤ eLpNorm (fun ω => δ * menv ω) 2 P := by
    apply eLpNorm_mono
    intro x
    simp only [Real.norm_eq_abs, abs_mul]
    calc |m θ x - m θ₀ x| ≤ menv x * ‖θ - θ₀‖ :=
          hLip θ hθρ θ₀ (Metric.mem_closedBall_self hρ.le) x
      _ ≤ |menv x| * ‖θ - θ₀‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |menv x| * δ := mul_le_mul_of_nonneg_left hθ.le (abs_nonneg _)
      _ = |δ| * |menv x| := by rw [abs_of_pos hδ]; ring
  refine le_trans hpt ?_
  have : (fun ω => δ * menv ω) = δ • menv := by funext ω; simp [Pi.smul_apply, smul_eq_mul]
  rw [this, eLpNorm_const_smul]
  gcongr
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos hδ]

/-- With `δq := δ·(‖menv‖₂ + 1)`, the fixed-center shell embeds into the
localized difference class of `F = paramClass (shellPsi m θ₀) (ball θ₀ δ)`: each
`m_θ − m_{θ₀}` is `f − g` with `f = m_θ ∈ F`, `g = m_{θ₀} = 0 ∈ F` (`θ₀ ∈ ball θ₀ δ`),
and radius `≤ δ‖menv‖₂ ≤ δq`. -/
theorem shellSet_subset_localized {d : ℕ} (hd : 1 ≤ d) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {δ : ℝ} (hδ : 0 < δ) (hδρ : δ ≤ ρ) :
    shellSet m θ₀ δ
      ⊆ localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
          (δ * ((eLpNorm menv 2 P).toReal + 1)) := by
  rintro g ⟨θ, hθ, rfl⟩
  -- `f = m_θ = shellPsi θ 0`, `g' = m_{θ₀} = shellPsi θ₀ 0`.
  have hθmem : θ ∈ Metric.ball θ₀ δ := by rw [Metric.mem_ball, dist_eq_norm]; exact hθ
  have hθ₀mem : θ₀ ∈ Metric.ball θ₀ δ := by rw [Metric.mem_ball]; simpa using hδ
  have hf : shellPsi m θ₀ θ ⟨0, hd⟩ ∈ paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ) :=
    ⟨θ, hθmem, ⟨0, hd⟩, rfl⟩
  have hg : shellPsi m θ₀ θ₀ ⟨0, hd⟩ ∈ paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ) :=
    ⟨θ₀, hθ₀mem, ⟨0, hd⟩, rfl⟩
  -- The radius bound `≤ δ·(‖menv‖₂ + 1)`.
  have hrad : eLpNorm (fun ω => m θ ω - m θ₀ ω) 2 P
      ≤ ENNReal.ofReal (δ * ((eLpNorm menv 2 P).toReal + 1)) := by
    refine le_trans (shellSet_radius_le m θ₀ menv ρ hρ hLip hδ hδρ hθ) ?_
    have hmenv_ne : eLpNorm menv 2 P ≠ ⊤ := hmenv.eLpNorm_lt_top.ne
    have hnn : 0 ≤ (eLpNorm menv 2 P).toReal := ENNReal.toReal_nonneg
    calc ENNReal.ofReal δ * eLpNorm menv 2 P
        = ENNReal.ofReal δ * ENNReal.ofReal (eLpNorm menv 2 P).toReal := by
          rw [ENNReal.ofReal_toReal hmenv_ne]
      _ = ENNReal.ofReal (δ * (eLpNorm menv 2 P).toReal) := (ENNReal.ofReal_mul hδ.le).symm
      _ ≤ ENNReal.ofReal (δ * ((eLpNorm menv 2 P).toReal + 1)) := by
          apply ENNReal.ofReal_le_ofReal; nlinarith [hnn, hδ.le]
  -- Assemble: `m_θ − m_{θ₀} = shellPsi θ 0 − shellPsi θ₀ 0`.
  have heq : (fun ω => m θ ω - m θ₀ ω)
      = fun ω => shellPsi m θ₀ θ ⟨0, hd⟩ ω - shellPsi m θ₀ θ₀ ⟨0, hd⟩ ω := by
    funext ω; simp only [shellPsi]; ring
  rw [heq]
  refine mem_localizedDifferenceClass hf hg ?_
  rw [← heq]; exact hrad

/-! ### Relative bracketing entropy of the shell -/

/-- **Relative bracketing number of the closed shell.**

Euclidean-net analogue of `l2CoveringNumber_shell_le`, packaged for
`bracketingNumber_le_of_lipschitz`. For the closed shell
`paramClass (shellPsi m θ₀) (closedBall θ₀ δ)` the bracketing number at scale `t`
is bounded by the *relative* ratio `δ/t`:

    N_{[]}(t, F_δ, L²(P)) ≤ d · (C·δ/t)^d   for `0 < t ≤ 2δ(‖menv‖₂+1)`,

with `C := 2·Ce·(‖menv‖₂+1)` δ-free (`Ce` the unit-ball covering constant). The
`δ`-dilation `c ↦ θ₀ + δ•(c−θ₀)` of an `η`-net of `closedBall θ₀ 1`
(`η = t/(2δ(‖menv‖₂+1))`, so the dilated net has Euclidean radius
`δη = t/(2(‖menv‖₂+1))`) is such a net of `closedBall θ₀ δ`, and
`2·(δη)·‖menv‖₂ = t·‖menv‖₂/(‖menv‖₂+1) < t` clears the
`bracketingNumber_le_of_lipschitz` scale gate. The `menv`-Lipschitz/`L²` data are
supplied by `shellPsi_lipschitz` / `shellPsi_memLp`. -/
private theorem shellClosedBall_bracketingNumber_le {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ρ → ∀ t : ℝ, 0 < t →
        t ≤ 2 * δ * ((eLpNorm menv 2 P).toReal + 1) →
      ∃ N : ℕ, bracketingNumber t
          (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) 2 P ≤ (N : ℕ∞) ∧
        (N : ℝ) ≤ (d : ℝ) * (C * δ / t) ^ d := by
  classical
  set M : ℝ := (eLpNorm menv 2 P).toReal with hMdef
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  have hMp1_pos : (0 : ℝ) < M + 1 := by positivity
  obtain ⟨Ce, hCe_pos, hcover⟩ :=
    coveringNumber_le_of_bounded_euclidean (Metric.closedBall θ₀ 1) Metric.isBounded_closedBall
  refine ⟨2 * Ce * (M + 1), by positivity, fun δ hδ hδρ t ht htle => ?_⟩
  -- Net scale `η = t/(2(M+1)δ) ∈ (0, 1]`; dilated Euclidean radius `ρ = δη`.
  set η : ℝ := t / (2 * (M + 1) * δ) with hηdef
  have hden_pos : (0 : ℝ) < 2 * (M + 1) * δ := by positivity
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  have hη_le : η ≤ 1 := by
    rw [hηdef, div_le_one hden_pos]; nlinarith [htle]
  obtain ⟨S, hSΘ, hΘcover, hScard⟩ := hcover η hη_pos hη_le
  set rad : ℝ := δ * η with hrad_def
  have hrad_pos : 0 < rad := by rw [hrad_def]; positivity
  -- The δ-dilated net of `closedBall θ₀ δ`.
  set Simg : Finset (EuclideanSpace ℝ (Fin d)) :=
    S.image (fun c => θ₀ + δ • (c - θ₀)) with hSimg
  have hSimg_sub : ↑Simg ⊆ Metric.closedBall θ₀ δ := by
    intro c' hc'
    rw [hSimg, Finset.coe_image, Set.mem_image] at hc'
    obtain ⟨c, hcS, rfl⟩ := hc'
    have hc_norm : ‖c - θ₀‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact Metric.mem_closedBall.mp (hSΘ (Finset.mem_coe.mpr hcS))
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hδ]
    calc δ * ‖c - θ₀‖ ≤ δ * 1 := mul_le_mul_of_nonneg_left hc_norm hδ.le
      _ = δ := mul_one δ
  have hSimg_net : Metric.closedBall θ₀ δ ⊆ ⋃ c ∈ Simg, Metric.ball c rad := by
    intro x hx
    have hx_norm : ‖x - θ₀‖ ≤ δ := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hx
    set u : EuclideanSpace ℝ (Fin d) := θ₀ + δ⁻¹ • (x - θ₀) with hudef
    have hu_norm : ‖u - θ₀‖ ≤ 1 := by
      have huθ : u - θ₀ = δ⁻¹ • (x - θ₀) := by rw [hudef, add_sub_cancel_left]
      rw [huθ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
      calc δ⁻¹ * ‖x - θ₀‖ ≤ δ⁻¹ * δ :=
            mul_le_mul_of_nonneg_left hx_norm (inv_pos.mpr hδ).le
        _ = 1 := inv_mul_cancel₀ hδ.ne'
    have huΘ : u ∈ Metric.closedBall θ₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]; exact hu_norm
    obtain ⟨c, hcS, hcu⟩ := Set.mem_iUnion₂.mp (hΘcover huΘ)
    have hcu_lt : ‖u - c‖ < η := by
      rw [← dist_eq_norm]; exact Metric.mem_ball.mp hcu
    refine Set.mem_iUnion₂.mpr ⟨θ₀ + δ • (c - θ₀), ?_, ?_⟩
    · rw [hSimg]; exact Finset.mem_image_of_mem _ hcS
    · rw [Metric.mem_ball, dist_eq_norm]
      have hvec : x - (θ₀ + δ • (c - θ₀)) = δ • (u - c) := by
        simp only [hudef, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
        abel
      rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hδ, hrad_def]
      exact mul_lt_mul_of_pos_left hcu_lt hδ
  -- Scale gate `2·ρ·M < t` for `bracketingNumber_le_of_lipschitz`.
  have hscale : 2 * rad * M < t := by
    rw [hrad_def]
    have hrw : 2 * (δ * η) * M = t * M / (M + 1) := by
      rw [hηdef]; field_simp
    rw [hrw, div_lt_iff₀ hMp1_pos]; nlinarith [ht, hM_nn]
  have hψmeas : ∀ θ ∈ Metric.closedBall θ₀ δ, ∀ j : Fin d,
      Measurable (shellPsi m θ₀ θ j) := by
    intro θ _ j; exact (hm_meas θ).sub (hm_meas θ₀)
  have hBN := bracketingNumber_le_of_lipschitz P (shellPsi m θ₀) (Metric.closedBall θ₀ δ)
    menv hmenv hmenv_meas hψmeas
    (fun θ hθδ j =>
      shellPsi_memLp m θ₀ hm_meas menv hmenv ρ hρ hLip θ
        (Metric.closedBall_subset_closedBall hδρ hθδ) j)
    (fun θ₁ hθ₁δ θ₂ hθ₂δ j x =>
      shellPsi_lipschitz m θ₀ menv ρ hρ hLip θ₁
        (Metric.closedBall_subset_closedBall hδρ hθ₁δ) θ₂
        (Metric.closedBall_subset_closedBall hδρ hθ₂δ) j x)
    hrad_pos hSimg_sub hSimg_net hscale
  refine ⟨d * Simg.card, hBN, ?_⟩
  -- Cardinality: `(d·|Simg|:ℝ) ≤ d·(Ce/η)^d = d·(C·δ/t)^d`.
  have hcard_le : (Simg.card : ℝ) ≤ (S.card : ℝ) := by
    rw [hSimg]; exact_mod_cast Finset.card_image_le
  have hCeη : Ce / η = 2 * Ce * (M + 1) * δ / t := by
    rw [hηdef, div_div_eq_mul_div]; ring
  rw [Nat.cast_mul]
  calc (d : ℝ) * (Simg.card : ℝ)
      ≤ (d : ℝ) * (Ce / η) ^ d :=
        mul_le_mul_of_nonneg_left (le_trans hcard_le hScard) (Nat.cast_nonneg d)
    _ = (d : ℝ) * (2 * Ce * (M + 1) * δ / t) ^ d := by rw [hCeη]

/-- **Relative-bracketing scale-invariance of the shell's localized difference class.**

The `δ`-uniform bracketing bound the quantitative modulus needs: there is a *single* `N*`
(free of `δ`) bounding both localized-difference bracketing numbers at scales `δq`, `δq/2`
(`δq = δ·(‖menv‖₂+1)`) that the chaining engine's clamp-lower-bound reads.

Route (all monotone, no symmetrization): with `G_δ = localizedDifferenceClass F_δ P δq`,
`F_δ = paramClass (shellPsi m θ₀) (ball θ₀ δ)`, for any bracket scale `t ∈ [δq/2, δq]`:

    N_{[]}(t, G_δ)
      ≤ N_{[]}(t, F_δ − F_δ)             (localized ⊆ difference class)
      ≤ N_{[]}(t/2, F_δ)²                (`bracketingNumber_differenceClass_le_sq`)
      ≤ N_{[]}(t/2, F_δ^{closed})²       (`ball ⊆ closedBall`)
      ≤ N_a²  with  (N_a : ℝ) ≤ d·(C·δ/(t/2))^d ≤ d·(4C/s)^d = K'   (relative dilated net).

`K'` is `δ`-free because `t/2 ≥ δq/4 = δ·s/4`, so `Cδ/(t/2) ≤ 4C/s`. Take `N* = ⌊K'⌋₊²`. -/
theorem shell_localizedDiff_bracketingNumber_le {d : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ N : ℕ, ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      bracketingNumber (δ * ((eLpNorm menv 2 P).toReal + 1))
          (localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
            (δ * ((eLpNorm menv 2 P).toReal + 1))) 2 P ≤ (N : ℕ∞) ∧
      bracketingNumber (δ * ((eLpNorm menv 2 P).toReal + 1) / 2)
          (localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
            (δ * ((eLpNorm menv 2 P).toReal + 1))) 2 P ≤ (N : ℕ∞) := by
  classical
  obtain ⟨C, hC_pos, hBN⟩ :=
    shellClosedBall_bracketingNumber_le P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
  set M : ℝ := (eLpNorm menv 2 P).toReal with hMdef
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  set s : ℝ := M + 1 with hs_def
  have hs_pos : 0 < s := by rw [hs_def]; positivity
  set K' : ℝ := (d : ℝ) * (4 * C / s) ^ d with hK'_def
  set Kf : ℕ := ⌊K'⌋₊ with hKf_def
  refine ⟨Kf ^ 2, fun δ hδ hδρ => ?_⟩
  set δq : ℝ := δ * s with hδq_def
  have hδq_pos : 0 < δq := by rw [hδq_def]; positivity
  set F : Set (Ω → ℝ) := paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ) with hF_def
  set Fc : Set (Ω → ℝ) := paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ) with hFc_def
  have hFsub : F ⊆ Fc := by
    rw [hF_def, hFc_def]; rintro g ⟨θ, hθ, j, rfl⟩
    exact ⟨θ, Metric.ball_subset_closedBall hθ, j, rfl⟩
  -- Core: for `δq/2 ≤ t ≤ δq`, `N_{[]}(t, localizedDiff F δq) ≤ (Kf : ℕ∞)²`.
  have hbn : ∀ t : ℝ, δq / 2 ≤ t → t ≤ δq →
      bracketingNumber t (localizedDifferenceClass F P δq) 2 P ≤ (Kf : ℕ∞) ^ 2 := by
    intro t ht_lo ht_hi
    have ht_pos : 0 < t := lt_of_lt_of_le (by positivity) ht_lo
    have ht2_pos : (0 : ℝ) < t / 2 := by positivity
    have ht2_le : t / 2 ≤ 2 * δ * s := by
      have h1 : t / 2 ≤ δq := by linarith [ht_hi]
      rw [hδq_def] at h1; nlinarith [h1, mul_nonneg hδ.le hs_pos.le]
    obtain ⟨Na, hNa_le, hNa_bd⟩ := hBN δ hδ hδρ (t / 2) ht2_pos ht2_le
    -- `(Na : ℝ) ≤ K'`.
    have hNa_K' : (Na : ℝ) ≤ K' := by
      refine le_trans hNa_bd ?_
      rw [hK'_def]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
      apply pow_le_pow_left₀ (by positivity) _ d
      -- `C*δ/(t/2) ≤ 4*C/s`, since `t/2 ≥ δq/4 = δ*s/4`.
      have ht2_ge : δ * s / 4 ≤ t / 2 := by rw [hδq_def] at ht_lo; linarith [ht_lo]
      calc C * δ / (t / 2)
          ≤ C * δ / (δ * s / 4) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) ht2_ge
        _ = 4 * C / s := by field_simp
    have hNa_Kf : Na ≤ Kf := by rw [hKf_def]; exact Nat.le_floor hNa_K'
    -- finite bracketing cover of `F` at `t/2`.
    have hcov : HasFiniteBracketingCover F (t / 2) 2 P := by
      apply bracketingNumber_lt_top_iff_HasFiniteBracketingCover.mp
      calc bracketingNumber (t / 2) F 2 P
          ≤ bracketingNumber (t / 2) Fc 2 P := bracketingNumber_mono_class hFsub
        _ ≤ (Na : ℕ∞) := hNa_le
        _ < ⊤ := ENat.coe_lt_top Na
    calc bracketingNumber t (localizedDifferenceClass F P δq) 2 P
        ≤ bracketingNumber t (differenceClass F) 2 P :=
          bracketingNumber_mono_class localizedDifferenceClass_subset
      _ ≤ (bracketingNumber (t / 2) F 2 P) ^ 2 :=
          bracketingNumber_differenceClass_le_sq ht_pos hcov
      _ ≤ (bracketingNumber (t / 2) Fc 2 P) ^ 2 :=
          pow_le_pow_left' (bracketingNumber_mono_class hFsub) 2
      _ ≤ (Na : ℕ∞) ^ 2 := pow_le_pow_left' hNa_le 2
      _ ≤ (Kf : ℕ∞) ^ 2 := pow_le_pow_left' (by exact_mod_cast hNa_Kf) 2
  have hcast : (Kf : ℕ∞) ^ 2 = ((Kf ^ 2 : ℕ) : ℕ∞) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · have h := hbn δq (by linarith [hδq_pos]) le_rfl
    rwa [hcast] at h
  · have h := hbn (δq / 2) le_rfl (by linarith [hδq_pos])
    rwa [hcast] at h

/-- **Relative bracketing entropy integral of the shell.**

`J_{[]}(δq, F) ≤ Cent · δ` for `F = paramClass (shellPsi m θ₀) (ball θ₀ δ)` and
`δq = δ·(‖menv‖₂ + 1)`. The bracketing number `N_{[]}(s, F)` is **relative**
(`∝ (δ/s)`): a *rescaled* ε-net of `ball θ₀ δ` (the unit-ball net of
`coveringNumber_le_of_bounded_euclidean` dilated by `c ↦ θ₀ + δ·(c − θ₀)`) puts `δ`
in the numerator, so `N_{[]}(s, F) ≤ d·(C·δ/s)^d`. Feeding this into the scale-free
analytic integral `sqrt_log_pow_ratio_lintegral_le` (at power `d`) gives the clean
`Cent·δ` (the spurious `√log(1/δ)` cancels because the covering scale is relative).

Proof: reduce to the CLOSED shell by class monotonicity
(`bracketingEntropyIntegral_mono_class`, `ball ⊆ closedBall`), then dominate the
entropy integrand pointwise via `shellClosedBall_bracketingNumber_le`
(`N_{[]}(ε, F_δ) ≤ d·(C·δ/ε)^d`, relative dilated net) and integrate with the
scale-free `sqrt_log_pow_ratio_lintegral_le` at power `d`. The factor `d` is absorbed
into the ratio power by `d ≤ 2^d` (`Nat.lt_two_pow_self`), and `δ ≤ δq` folds the `δ`
numerator into the `δq` numerator the integral lemma expects. Mirror of the proven
covering-route `l2CoveringEntropyIntegral_shell_le` transplanted to the *bracketing*
integral. -/
theorem paramClass_shell_bracketingEntropyIntegral_le {d : ℕ} (hd : 1 ≤ d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ Cent : ℝ, 0 < Cent ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      bracketingEntropyIntegral (δ * ((eLpNorm menv 2 P).toReal + 1))
          (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
        ≤ ENNReal.ofReal (Cent * δ) := by
  classical
  obtain ⟨C, hC_pos, hBN⟩ :=
    shellClosedBall_bracketingNumber_le P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
  obtain ⟨Cp, hCp_pos, hInt⟩ :=
    AsymptoticStatistics.ForMathlib.sqrt_log_pow_ratio_lintegral_le (2 * C) (by positivity) d
  set M : ℝ := (eLpNorm menv 2 P).toReal with hMdef
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  have hMp1_pos : (0 : ℝ) < M + 1 := by positivity
  refine ⟨Cp * (M + 1), by positivity, fun δ hδ hδρ => ?_⟩
  set δq : ℝ := δ * (M + 1) with hδqdef
  have hδq_pos : 0 < δq := by rw [hδqdef]; positivity
  have hδ_le_δq : δ ≤ δq := by rw [hδqdef]; nlinarith [hM_nn, hδ.le]
  -- Class-monotonicity reduction to the CLOSED shell.
  have hmono_class :
      bracketingEntropyIntegral δq (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
        ≤ bracketingEntropyIntegral δq
            (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) P := by
    apply bracketingEntropyIntegral_mono_class
    rintro g ⟨θ, hθ, j, rfl⟩
    exact ⟨θ, Metric.ball_subset_closedBall hθ, j, rfl⟩
  -- Pointwise domination of the closed-shell entropy integrand on `Ioc 0 δq`.
  have hdom : ∀ ε ∈ Set.Ioc (0 : ℝ) δq,
      entropyIntegrand ε (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) P
        ≤ ENNReal.ofReal (Real.sqrt (Real.log (1 + (2 * C * δq / ε) ^ d))) := by
    intro ε hε
    obtain ⟨hε0, hεδq⟩ := hε
    have htle : ε ≤ 2 * δ * (M + 1) := by
      have h0 : (0 : ℝ) ≤ δ * (M + 1) := mul_nonneg hδ.le hMp1_pos.le
      have hδqeq : δq = δ * (M + 1) := hδqdef
      nlinarith [hεδq, h0, hδqeq]
    obtain ⟨N, hN_le, hN_bd⟩ := hBN δ hδ hδρ ε hε0 htle
    calc entropyIntegrand ε (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) P
        = entropyWeight (bracketingNumber ε
            (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) 2 P) := rfl
      _ ≤ entropyWeight (N : ℕ∞) := entropyWeight_mono hN_le
      _ = ENNReal.ofReal (Real.sqrt (Real.log (1 + (N : ℝ)))) := entropyWeight_coe N
      _ ≤ ENNReal.ofReal (Real.sqrt (Real.log (1 + (2 * C * δq / ε) ^ d))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.sqrt_le_sqrt
          apply Real.log_le_log (by positivity)
          have hNle : (N : ℝ) ≤ (2 * C * δq / ε) ^ d := by
            calc (N : ℝ)
                ≤ (d : ℝ) * (C * δ / ε) ^ d := hN_bd
              _ ≤ (2 : ℝ) ^ d * (C * δ / ε) ^ d := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact_mod_cast (Nat.lt_two_pow_self (n := d)).le
              _ = (2 * (C * δ / ε)) ^ d := by rw [mul_pow]
              _ ≤ (2 * C * δq / ε) ^ d := by
                  apply pow_le_pow_left₀ (by positivity)
                  rw [show 2 * (C * δ / ε) = 2 * C * δ / ε by ring]
                  gcongr
          linarith [hNle]
  calc bracketingEntropyIntegral δq (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
      ≤ bracketingEntropyIntegral δq
          (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) P := hmono_class
    _ = ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
          entropyIntegrand ε (paramClass (shellPsi m θ₀) (Metric.closedBall θ₀ δ)) P ∂volume :=
        bracketingEntropyIntegral_eq_setLIntegral δq _ P
    _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (2 * C * δq / ε) ^ d))) ∂volume :=
        setLIntegral_mono_ae' measurableSet_Ioc (Eventually.of_forall hdom)
    _ ≤ ENNReal.ofReal (Cp * δq) := hInt δq hδq_pos
    _ = ENNReal.ofReal (Cp * (M + 1) * δ) := by rw [hδqdef]; congr 1; ring

/-! ### Localized chaining with a lower bound on the clamp level -/

/-- The shell **difference-class envelope** `Φ_δ = 2δ·|menv|`. Since each shell
difference `(m_θ − m_{θ₀}) − (m_{θ'} − m_{θ₀}) = m_θ − m_{θ'}` obeys
`|m_θ − m_{θ'}| ≤ menv·‖θ − θ'‖ ≤ 2δ·|menv|` (both `θ, θ' ∈ ball θ₀ δ`). -/
noncomputable def shellDiffEnvelope {Ω : Type*} (menv : Ω → ℝ) (δ : ℝ) : Ω → ℝ :=
  fun ω => 2 * δ * ‖menv ω‖

/-- **Localized chaining bound with `M` bounded below.**

`localizedChainBound_of_finiteEntropy` (vdV Lemma 19.34, with **no
symmetrization**) specialized to the shell `F = paramClass (shellPsi m θ₀) (ball θ₀ δ)`
with the difference-class envelope `Φ_δ = 2δ·|menv|` and `δq = δ·(‖menv‖₂ + 1)`,
**additionally exposing** the δq-proportional lower bound `cM·δq ≤ M` on the engine's
clamp level.

The underlying inequality returns `∃ M > 0` with no lower bound. Internally
`M = min(θ/2, θ')` with
`θ ≥ δq/(1+√log(1+NB₀·NB₁))`, `θ' ≥ δq/(1+√log(1+NB₀))`
(`localized_{chain,global}Threshold_lower_bound`), where `NB₀`, `NB₁` are the
localized-difference bracketing numbers at scales `δq`, `δq/2`; those are δ-free
constants (relative bracketing, `δq ∝ δ`), so `M ≥ cM·δq` with `cM` δ-free. -/
theorem localizedChainBound_shell_MLower {d : ℕ} (hd : 1 ≤ d) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧ ∃ cM : ℝ, 0 < cM ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
        (δ * ((eLpNorm menv 2 P).toReal + 1) ≤ 1 / 4) →
        ∃ M : ℝ, cM * (δ * ((eLpNorm menv 2 P).toReal + 1)) ≤ M ∧ 0 < M ∧
          ∀ n : ℕ,
            ∫⁻ ξ, supNormOver
                (localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
                  (δ * ((eLpNorm menv 2 P).toReal + 1)))
                (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
              ≤ ENNReal.ofReal c
                  * bracketingEntropyIntegral (δ * ((eLpNorm menv 2 P).toReal + 1))
                      (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
                + ENNReal.ofReal c
                    * (ENNReal.ofReal (Real.sqrt n)
                      * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv δ ω|)
                          * Set.indicator {x | Real.sqrt n * M < |shellDiffEnvelope menv δ x|}
                              1 ω ∂P) := by
  classical
  -- The constant `c₀` from `localized_core_construction` is independent of `F`,
  -- so `c := c₀·(4√2)+4c₀` is uniform over the varying shell `F_δ`.
  obtain ⟨c₀, hc₀_one, hengine⟩ :=
    chain_supnorm_dyadic_bound_uniform (P := P) (μ := μ) hX_meas hX_indep hX_id hX_law
  have hc₀_pos : 0 < c₀ := lt_of_lt_of_le one_pos hc₀_one
  -- **δ-free** relative bracketing bound `N*` on the shell's localized difference class.
  obtain ⟨Nstar, hNstar⟩ :=
    shell_localizedDiff_bracketingNumber_le P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
  refine ⟨c₀ * (4 * Real.sqrt 2) + 4 * c₀, by positivity,
    min (1 / (2 * (1 + Real.sqrt (Real.log (1 + ((Nstar * Nstar : ℕ) : ℝ))))))
        (1 / (1 + Real.sqrt (Real.log (1 + (Nstar : ℝ))))), by positivity,
    fun δ hδ hδρ hδq4 => ?_⟩
  -- The shell class and its regularity at a fixed `δ`.
  set F : Set (Ω → ℝ) := paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ) with hF_def
  have hθ₀_mem : θ₀ ∈ Metric.ball θ₀ δ := by rw [Metric.mem_ball]; simpa using hδ
  have hΘ_bdd : Bornology.IsBounded (Metric.ball θ₀ δ) := Metric.isBounded_ball
  have hψ_meas : ∀ θ ∈ Metric.ball θ₀ δ, ∀ j : Fin d, Measurable (shellPsi m θ₀ θ j) :=
    fun θ _ j => (hm_meas θ).sub (hm_meas θ₀)
  have hψ_L2 : ∀ θ ∈ Metric.ball θ₀ δ, ∀ j : Fin d, MemLp (shellPsi m θ₀ θ j) 2 P :=
    fun θ hθδ j => shellPsi_memLp m θ₀ hm_meas menv hmenv ρ hρ hLip θ
      (Metric.closedBall_subset_closedBall hδρ (Metric.ball_subset_closedBall hθδ)) j
  have hψLip : ∀ θ₁ ∈ Metric.ball θ₀ δ, ∀ θ₂ ∈ Metric.ball θ₀ δ, ∀ (j : Fin d) (x : Ω),
      |shellPsi m θ₀ θ₁ j x - shellPsi m θ₀ θ₂ j x| ≤ menv x * ‖θ₁ - θ₂‖ :=
    fun θ₁ hθ₁δ θ₂ hθ₂δ j x => shellPsi_lipschitz m θ₀ menv ρ hρ hLip θ₁
      (Metric.closedBall_subset_closedBall hδρ (Metric.ball_subset_closedBall hθ₁δ)) θ₂
      (Metric.closedBall_subset_closedBall hδρ (Metric.ball_subset_closedBall hθ₂δ)) j x
  have hF_int : bracketingEntropyIntegral 1 F P < ⊤ :=
    parametricClass_bracketingEntropyIntegral_lt_top P (shellPsi m θ₀) (Metric.ball θ₀ δ) hΘ_bdd
      menv hmenv hmenv_meas hψ_meas hψ_L2 hψLip
  have hF_ne : F.Nonempty := ⟨shellPsi m θ₀ θ₀ ⟨0, hd⟩, ⟨θ₀, hθ₀_mem, ⟨0, hd⟩, rfl⟩⟩
  have hF_meas : ∀ f ∈ F, Measurable f := by
    rintro _ ⟨θ, _, j, rfl⟩; exact (hm_meas θ).sub (hm_meas θ₀)
  -- envelope `Φ_δ = shellDiffEnvelope menv δ = 2δ|menv|` of the difference class.
  have hΦ_meas : Measurable (shellDiffEnvelope menv δ) := by
    unfold shellDiffEnvelope; exact hmenv_meas.norm.const_mul _
  have hΦ_L2 : MemLp (shellDiffEnvelope menv δ) 2 P := by
    have hEq : shellDiffEnvelope menv δ = fun ω => (2 * δ) * ‖menv ω‖ := rfl
    rw [hEq]; exact hmenv.norm.const_mul' (2 * δ)
  have hΦ_env : IsEnvelope (differenceClass F) (shellDiffEnvelope menv δ) := by
    rintro _ ⟨f, g, ⟨θ, hθ, j, rfl⟩, ⟨θ', hθ', j', rfl⟩, rfl⟩ x
    simp only [shellPsi, shellDiffEnvelope]
    have heq : m θ x - m θ₀ x - (m θ' x - m θ₀ x) = m θ x - m θ' x := by ring
    rw [heq]
    have h2 : ‖θ - θ'‖ ≤ 2 * δ := by
      have hθn : ‖θ - θ₀‖ < δ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hθ
      have hθ'n : ‖θ' - θ₀‖ < δ := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hθ'
      calc ‖θ - θ'‖ = ‖(θ - θ₀) - (θ' - θ₀)‖ := by rw [sub_sub_sub_cancel_right]
        _ ≤ ‖θ - θ₀‖ + ‖θ' - θ₀‖ := norm_sub_le _ _
        _ ≤ 2 * δ := by linarith
    calc |m θ x - m θ' x| ≤ menv x * ‖θ - θ'‖ :=
          hLip θ (Metric.closedBall_subset_closedBall hδρ (Metric.ball_subset_closedBall hθ)) θ'
            (Metric.closedBall_subset_closedBall hδρ (Metric.ball_subset_closedBall hθ')) x
      _ ≤ |menv x| * (2 * δ) :=
          mul_le_mul (le_abs_self _) h2 (norm_nonneg _) (abs_nonneg _)
      _ = 2 * δ * ‖menv x‖ := by rw [Real.norm_eq_abs]; ring
  -- Use the uniform-constant construction at scale `δq = δ·(‖menv‖₂+1)`.
  have hδq_pos : 0 < δ * ((eLpNorm menv 2 P).toReal + 1) := by
    have : 0 ≤ (eLpNorm menv 2 P).toReal := ENNReal.toReal_nonneg
    positivity
  obtain ⟨M, hM_pos, _, hM_Nbd, hbound⟩ :=
    localized_core_construction (F := F) hF_ne hF_meas hF_int
      μ X hX_meas hX_indep hX_id hX_law c₀ hc₀_one hengine
      (shellDiffEnvelope menv δ) hΦ_meas hΦ_env hΦ_L2 hδq_pos hδq4
  -- feed the δ-free `N*` into the bracketing-explicit clamp lower bound ⇒ δ-free `cM·δq ≤ M`.
  have hM_lb := hM_Nbd Nstar (hNstar δ hδ hδρ).1 (hNstar δ hδ hδρ).2
  refine ⟨M, hM_lb, hM_pos, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · -- `n = 0`: the empirical process ≡ 0 ⟹ LHS integral = 0.
    subst hn0
    have h_lhs : ∫⁻ ξ, supNormOver (localizedDifferenceClass F P (δ * ((eLpNorm menv 2 P).toReal + 1)))
          (fun h => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) h) ∂μ = 0 := by
      have h_sup0 : ∀ ξ : Ξ, supNormOver
          (localizedDifferenceClass F P (δ * ((eLpNorm menv 2 P).toReal + 1)))
          (fun h => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) h) = 0 := by
        intro ξ
        simp only [supNormOver, empiricalProcess_zero, abs_zero, ENNReal.ofReal_zero]
        exact le_antisymm (by simp) (by positivity)
      simp only [h_sup0, lintegral_zero]
    rw [h_lhs]; exact zero_le
  · exact hbound n hn_pos

/-! ### The envelope tail bound -/

/-- **Envelope tail fold by Chebyshev's inequality.**

For `Φ_δ = 2δ|menv|` and clamp level `M ≥ cM·δq` with `δq = δ·(‖menv‖₂ + 1)`, the
`√n`-scaled envelope tail is `≤ Ctail·δ`, uniformly in `n`:

    √n · ∫⁻ |Φ_δ| · 1{√n·M < |Φ_δ|} ∂P
      ≤ (1/M) ∫⁻ Φ_δ² = 4δ²‖menv‖₂²/M ≤ 4δ²‖menv‖₂²/(cM·δq) ≤ Ctail·δ.

On `{√n·M < |Φ_δ|}`, `√n < |Φ_δ|/M`, so `√n·|Φ_δ| ≤ |Φ_δ|²/M` (Chebyshev-Markov);
`|Φ_δ|² = 4δ²menv²`; and `M ≥ cM·δ·(‖menv‖₂+1) ≥ cM·δ·‖menv‖₂` cancels one `δ`. -/
theorem shellTail_fold {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    {cM : ℝ} (hcM : 0 < cM) :
    ∃ Ctail : ℝ, 0 < Ctail ∧ ∀ δ : ℝ, 0 < δ → ∀ M : ℝ,
      cM * (δ * ((eLpNorm menv 2 P).toReal + 1)) ≤ M →
      ∀ n : ℕ,
        ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv δ ω|)
                * Set.indicator {x | Real.sqrt n * M < |shellDiffEnvelope menv δ x|} 1 ω ∂P
          ≤ ENNReal.ofReal (Ctail * δ) := by
  -- `T := ∫⁻ menv² < ⊤`.
  have hT_ne : ∫⁻ ω, ENNReal.ofReal (menv ω ^ 2) ∂P ≠ ∞ := by
    have h_eLp : eLpNorm menv 2 P < ∞ := hmenv.eLpNorm_lt_top
    have h_rpow := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (μ := P) (f := menv) (p := (2 : ℝ≥0∞))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) h_eLp
    have h_two : (2 : ℝ≥0∞).toReal = (2 : ℕ) := by norm_num
    rw [h_two] at h_rpow
    have h_int_eq : ∫⁻ ω, ENNReal.ofReal (menv ω ^ 2) ∂P
        = ∫⁻ a, ‖menv a‖ₑ ^ ((2 : ℕ) : ℝ) ∂P := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    rw [h_int_eq]; exact h_rpow.ne
  set T : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (menv ω ^ 2) ∂P with hT_def
  have hTnn : (0 : ℝ) ≤ T.toReal := ENNReal.toReal_nonneg
  refine ⟨4 * T.toReal / cM + 1, by positivity, fun δ hδ M hM n => ?_⟩
  have hMpos : 0 < M :=
    lt_of_lt_of_le (by positivity) hM
  -- Pointwise Chebyshev: `√n·ofReal|Φ_δ|·1_A ≤ ofReal(4δ²/M) · ofReal(menv²)`.
  have hpt : ∀ ω : Ω,
      ENNReal.ofReal (Real.sqrt n) * (ENNReal.ofReal (|shellDiffEnvelope menv δ ω|)
          * Set.indicator {x | Real.sqrt n * M < |shellDiffEnvelope menv δ x|} 1 ω)
        ≤ ENNReal.ofReal (4 * δ ^ 2 / M) * ENNReal.ofReal (menv ω ^ 2) := by
    intro ω
    by_cases hω : ω ∈ {x | Real.sqrt n * M < |shellDiffEnvelope menv δ x|}
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have hΦabs : |shellDiffEnvelope menv δ ω| = 2 * δ * |menv ω| := by
        simp only [shellDiffEnvelope, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * δ * |menv ω|)]
      have hω' : Real.sqrt n * M < 2 * δ * |menv ω| := by
        rw [← hΦabs]; exact hω
      rw [hΦabs]
      -- `√n·(2δ|menv|) ≤ (2δ|menv|)²/M = 4δ²menv²/M`.
      have hsn_le : Real.sqrt n ≤ (2 * δ * |menv ω|) / M := by
        rw [le_div_iff₀ hMpos]; linarith [hω']
      have h1 : Real.sqrt n * (2 * δ * |menv ω|) ≤ 4 * δ ^ 2 / M * menv ω ^ 2 := by
        calc Real.sqrt n * (2 * δ * |menv ω|)
            ≤ ((2 * δ * |menv ω|) / M) * (2 * δ * |menv ω|) :=
              mul_le_mul_of_nonneg_right hsn_le (by positivity)
          _ = (2 * δ * |menv ω|) * (2 * δ * |menv ω|) / M := by ring
          _ = 4 * δ ^ 2 / M * menv ω ^ 2 := by
              rw [← sq_abs (menv ω)]; ring
      calc ENNReal.ofReal (Real.sqrt n) * ENNReal.ofReal (2 * δ * |menv ω|)
          = ENNReal.ofReal (Real.sqrt n * (2 * δ * |menv ω|)) :=
            (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
        _ ≤ ENNReal.ofReal (4 * δ ^ 2 / M * menv ω ^ 2) := ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal (4 * δ ^ 2 / M) * ENNReal.ofReal (menv ω ^ 2) :=
            ENNReal.ofReal_mul (by positivity)
    · rw [Set.indicator_of_notMem hω]
      simp
  -- Integrate the pointwise bound.
  calc ENNReal.ofReal (Real.sqrt n)
        * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv δ ω|)
            * Set.indicator {x | Real.sqrt n * M < |shellDiffEnvelope menv δ x|} 1 ω ∂P
      = ∫⁻ ω, ENNReal.ofReal (Real.sqrt n)
            * (ENNReal.ofReal (|shellDiffEnvelope menv δ ω|)
              * Set.indicator {x | Real.sqrt n * M < |shellDiffEnvelope menv δ x|} 1 ω) ∂P := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (4 * δ ^ 2 / M) * ENNReal.ofReal (menv ω ^ 2) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (4 * δ ^ 2 / M) * T := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((4 * T.toReal / cM + 1) * δ) := by
        -- `4δ²/M · T ≤ (4T/cM + 1)·δ` because `M ≥ cM·δ·(‖menv‖₂+1) ≥ cM·δ`.
        have hMlb : cM * δ ≤ M := by
          refine le_trans ?_ hM
          have hA1 : (1 : ℝ) ≤ (eLpNorm menv 2 P).toReal + 1 := by
            have := ENNReal.toReal_nonneg (a := eLpNorm menv 2 P); linarith
          calc cM * δ = cM * (δ * 1) := by ring
            _ ≤ cM * (δ * ((eLpNorm menv 2 P).toReal + 1)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA1 hδ.le) hcM.le
        -- Abstract `T.toReal` as `tr` so the `T`-rewrite only hits the standalone factor.
        set tr : ℝ := T.toReal with htr
        have hTeq : T = ENNReal.ofReal tr := by rw [htr, ENNReal.ofReal_toReal hT_ne]
        rw [hTeq, ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        -- `4δ²/M·tr ≤ 4δ·tr/cM ≤ (4tr/cM + 1)·δ`.
        have h1 : 4 * δ ^ 2 / M * tr ≤ 4 * δ * tr / cM := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hMpos hcM]
          nlinarith [mul_nonneg (by linarith [hMlb] : (0:ℝ) ≤ M - cM * δ)
            (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hδ.le) hTnn), hTnn, hδ.le]
        have h2 : 4 * δ * tr / cM ≤ (4 * tr / cM + 1) * δ := by
          have hEq : (4 * tr / cM + 1) * δ = 4 * δ * tr / cM + δ := by ring
          rw [hEq]; linarith [hδ.le]
        linarith [h1, h2]

/-! ### Fixed-center shell modulus -/

/-- **Fixed-center shell modulus bound (bracketing route).**

Exactly the conclusion of `MEstimator.Rate.modulus_maximal_bound`:

    ∃ C > 0, ∃ ρ > 0, ∀ 0 < δ < ρ, ∀ n,
      ∫⁻ ξ, ‖𝔾ₙ‖_{M̄_δ} ∂μ ≤ ofReal (C · δ).

The proof combines the shell-set identification, its localized inclusion, the
relative bracketing entropy bound, the localized chaining estimate, and the
Chebyshev envelope-tail bound. -/
theorem lipschitzShellModulus_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ δ : ℝ, 0 < δ → δ < ρ → ∀ n : ℕ,
      ∫⁻ ξ, supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal (C * δ) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · -- `d = 0`: the parameter space is a single point, so the shell forces `θ = θ₀`
    -- and every member of the class is the zero function ⟹ `𝔾ₙ = 0` ⟹ LHS `= 0`.
    refine ⟨1, one_pos, 1, one_pos, fun δ hδ _ n => ?_⟩
    subst hd0
    have hsup0 : ∀ ξ : Ξ, supNormOver
        {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin 0), ‖θ - θ₀‖ < δ ∧
          g = fun ω => m θ ω - m θ₀ ω}
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) = 0 := by
      intro ξ
      apply le_antisymm _ (zero_le)
      refine iSup₂_le (fun g hg => ?_)
      obtain ⟨θ, _, rfl⟩ := hg
      have hθ : θ = θ₀ := Subsingleton.elim _ _
      have h0 : (fun ω => m θ ω - m θ₀ ω) = (fun _ => (0 : ℝ)) := by
        funext ω; simp [hθ]
      rw [h0]
      simp [empiricalProcess, empiricalAvg]
    rw [lintegral_congr hsup0, lintegral_zero]
    exact zero_le
  · -- `d ≥ 1`: the genuine bracketing-route assembly.
    -- Localized chaining with a lower bound on `M`.
    obtain ⟨c, hc_pos, cM, hcM_pos, hEng⟩ :=
      localizedChainBound_shell_MLower hd P m θ₀ hm_meas menv hmenv hmenv_meas ρ hρ hLip
        μ X hX_meas hX_indep hX_id hX_law
    -- Relative bracketing entropy.
    obtain ⟨Cent, hCent_pos, hEnt⟩ :=
      paramClass_shell_bracketingEntropyIntegral_le hd P m θ₀ hm_meas menv hmenv hmenv_meas
        ρ hρ hLip
    -- Envelope-tail bound.
    obtain ⟨Ctail, hCtail_pos, hTail⟩ := shellTail_fold menv hmenv hcM_pos
    -- Abbreviate `s := ‖menv‖₂ + 1` (folds `(eLpNorm menv 2 P).toReal + 1` in all three).
    set s : ℝ := (eLpNorm menv 2 P).toReal + 1 with hs_def
    have hs_pos : 0 < s := by
      have : (0 : ℝ) ≤ (eLpNorm menv 2 P).toReal := ENNReal.toReal_nonneg
      rw [hs_def]; linarith
    -- The final constant and radius.
    refine ⟨c * Cent + c * Ctail, by positivity, min (1 / (4 * s)) ρ,
      lt_min (by positivity) hρ, fun δ hδ hδlt n => ?_⟩
    -- Split `δ < min (1/(4s)) ρ` into the `δq ≤ 1/4` bound and the `δ ≤ ρ` link.
    have hδ4s : δ < 1 / (4 * s) := lt_of_lt_of_le hδlt (min_le_left _ _)
    have hδρ : δ ≤ ρ := (lt_of_lt_of_le hδlt (min_le_right _ _)).le
    -- `δq ≤ 1/4`.
    have hδq_le : δ * s ≤ 1 / 4 := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < 4 * s)] at hδ4s
      nlinarith [hδ4s, hs_pos, hδ.le]
    -- Localized chaining at scale `δ`.
    obtain ⟨M, hM_lb, hM_pos, hbound⟩ := hEng δ hδ hδρ hδq_le
    -- Reduce `M̄_δ ⊆ localized`.
    have hsub := shellSet_subset_localized hd m θ₀ menv hmenv ρ hρ hLip hδ hδρ
    -- Bound the integrand pointwise then integrate.
    have hmono : ∀ ξ : Ξ,
        supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f)
        ≤ supNormOver
            (localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P (δ * s))
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) := by
      intro ξ
      exact supNormOver_mono hsub _
    calc ∫⁻ ξ, supNormOver
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ∫⁻ ξ, supNormOver
            (localizedDifferenceClass (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P (δ * s))
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ :=
          lintegral_mono hmono
      _ ≤ ENNReal.ofReal c
            * bracketingEntropyIntegral (δ * s)
                (paramClass (shellPsi m θ₀) (Metric.ball θ₀ δ)) P
          + ENNReal.ofReal c
              * (ENNReal.ofReal (Real.sqrt n)
                * ∫⁻ ω, ENNReal.ofReal (|shellDiffEnvelope menv δ ω|)
                    * Set.indicator {x | Real.sqrt n * M < |shellDiffEnvelope menv δ x|}
                        1 ω ∂P) := hbound n
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Cent * δ)
          + ENNReal.ofReal c * ENNReal.ofReal (Ctail * δ) := by
          gcongr
          · exact hEnt δ hδ hδρ
          · exact hTail δ hδ M hM_lb n
      _ = ENNReal.ofReal ((c * Cent + c * Ctail) * δ) := by
          rw [← ENNReal.ofReal_mul hc_pos.le, ← ENNReal.ofReal_mul hc_pos.le,
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring

end AsymptoticStatistics.EmpiricalProcess
