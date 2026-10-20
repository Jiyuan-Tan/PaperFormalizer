module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ParametricClassDonsker
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringOuterMaximal
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Uniform-entropy (covering) localized maximal inequality (vdV Thm 2.14.1 / Cor 19.35)

Finite-dimensional, envelope-relative **covering-number** maximal inequality for the
centered Lipschitz class

    F_full = {ω ↦ m_θ ω − m_{θ₀} ω : θ ∈ ℝ^d, ‖θ − θ₀‖ ≤ 1},  envelope `menv ∈ L²(P)`, Lipschitz.

For M-estimator normality, the localized empirical
modulus over the `δq`-slice `(F_full − F_full)_{δq}` is bounded **linearly** in the slice
radius, **uniformly in `n`** and with a **clean constant** (no spurious `√log(1/δq)`):

    ∫⁻ ξ, ‖𝔾ₙ‖_{(F_full − F_full)_{δq}} ∂μ ≤ C · δq   ∀ δq > 0, ∀ n.

**Why bracketing fails, why covering wins.** The absolute-scale bracketing entropy integral
`J_{[]}(δq, F) ≈ δq·√(k log(1/δq))` carries a spurious `√log(1/δq)`. Instead use the
**radius-relative covering scale**: the `δq`-slice has `L²`-radius `δq`, so its covering number
`N_{L²}(ε, slice_{δq}) ≤ (C·δq/ε)^{2d}` has the *ratio* `δq/ε` in it — a scaled copy — whence

    ∫₀^{δq} √log N_{L²}(ε, slice_{δq}) dε = δq · C_d   (scale-free constant),

removing the `√log` and giving `E*‖𝔾ₙ‖ ≲ C_d·δq`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Thm 2.14.1, Cor 19.35.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Definitions: `L²(P)` covering number and covering-entropy integral -/

/-- The **`L²(P)` covering number** `N_{L²}(s, F)` — the minimum cardinality of an
`s`-net of `F` by points of `F` in the intrinsic `L²(P)` semimetric `distL2 P`,
valued in `ℕ∞`.

An `s`-net is a finite `S ⊆ F` with every `f ∈ F` within `distL2 P`-distance `< s` of
some `g ∈ S`. The infimum ranges over such nets (`⊤` if none exists), mirroring
`bracketingNumber`.

vdV §19.2 / §2.1: the covering number in the intrinsic `L²(P)` metric that drives the
uniform-entropy (Dudley) chaining bound. -/
noncomputable def l2CoveringNumber (P : Measure Ω) (F : Set (Ω → ℝ)) (s : ℝ) : ℕ∞ :=
  ⨅ (S : Finset (Ω → ℝ)) (_ : ↑S ⊆ F ∧ ∀ f ∈ F, ∃ g ∈ S, distL2 P f g < s), (S.card : ℕ∞)

/-- The **`L²(P)` covering entropy integral** `∫₀^δ √log(1 + N_{L²}(ε, F)) dε`, the
covering analogue of `bracketingEntropyIntegral`. Reuses the `entropyWeight`
`N ↦ √(log (1 + N))` (with the `⊤` convention) from `Bracketing.lean`. -/
noncomputable def l2CoveringEntropyIntegral
    (δ : ℝ) (F : Set (Ω → ℝ)) (P : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 δ, entropyWeight (l2CoveringNumber P F ε) ∂volume

/-- `l2CoveringNumber ≤ |S|` for any `s`-net `S ⊆ F`: the infimum is at most the size of
any admissible net. -/
lemma l2CoveringNumber_le_of_net {P : Measure Ω} {F : Set (Ω → ℝ)} {s : ℝ}
    {S : Finset (Ω → ℝ)} (hSF : ↑S ⊆ F)
    (hnet : ∀ f ∈ F, ∃ g ∈ S, distL2 P f g < s) :
    l2CoveringNumber P F s ≤ (S.card : ℕ∞) := by
  refine iInf_le_of_le S (iInf_le_of_le ⟨hSF, hnet⟩ le_rfl)

/-! ## Lipschitz-to-`L²`-net bridge

An `η`-Euclidean-net of the parameter ball `‖θ − θ₀‖ ≤ 1` induces an
`(η·‖menv‖₂)`-`L²`-net of `F_full`, because `‖m_θ − m_{θ'}‖₂ ≤ ‖menv‖₂·‖θ − θ'‖`. Combined
with the finite-dim Euclidean covering bound `coveringNumber_le_of_bounded_euclidean`
(`|S| ≤ (C/η)^d`) this yields `N_{L²}(s, F_full) ≤ (C'/s)^d`. -/

/-- **`L²` Lipschitz contraction**: `‖m_θ − m_{θ'}‖₂ ≤ ‖menv‖₂ · ‖θ − θ'‖`.

Pointwise `|m_θ ω − m_{θ'} ω| ≤ menv ω · ‖θ − θ'‖ ≤ |menv ω| · ‖θ − θ'‖`
(`hLip`) lifts through `eLpNorm_mono` + `eLpNorm_const_smul` to the `L²` bound, then to
`distL2` via `.toReal` (both norms finite since `menv ∈ L²`). -/
lemma distL2_centeredDiff_le
    {d : ℕ} {P : Measure Ω}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (θ θ' : EuclideanSpace ℝ (Fin d)) :
    distL2 P (fun ω => m θ ω) (fun ω => m θ' ω)
      ≤ (eLpNorm menv 2 P).toReal * ‖θ - θ'‖ := by
  -- `eLpNorm (m θ − m θ') ≤ eLpNorm (‖θ − θ'‖ • menv) = ofReal ‖θ − θ'‖ · eLpNorm menv`.
  have hptwise : ∀ ω, ‖(fun ω => m θ ω) ω - (fun ω => m θ' ω) ω‖
      ≤ ‖(‖θ - θ'‖ • menv) ω‖ := by
    intro ω
    simp only [Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul]
    calc |m θ ω - m θ' ω| ≤ menv ω * ‖θ - θ'‖ := hLip θ θ' ω
      _ ≤ |menv ω| * ‖θ - θ'‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ = |‖θ - θ'‖| * |menv ω| := by rw [abs_of_nonneg (norm_nonneg _)]; ring
  have hmono : eLpNorm (fun ω => m θ ω - m θ' ω) 2 P
      ≤ eLpNorm (‖θ - θ'‖ • menv) 2 P := eLpNorm_mono hptwise
  rw [eLpNorm_const_smul] at hmono
  -- Transfer to `.toReal`.
  unfold distL2
  have hmenv_ne : eLpNorm menv 2 P ≠ ⊤ := hmenv.eLpNorm_ne_top
  have hsub_eq : (fun ω => m θ ω) - (fun ω => m θ' ω) = fun ω => m θ ω - m θ' ω := rfl
  rw [hsub_eq]
  have henorm : ‖‖θ - θ'‖‖ₑ * eLpNorm menv 2 P
      = ENNReal.ofReal (‖θ - θ'‖ * (eLpNorm menv 2 P).toReal) := by
    rw [Real.enorm_eq_ofReal (norm_nonneg _), ← ENNReal.ofReal_toReal hmenv_ne,
      ← ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_toReal hmenv_ne]
  rw [henorm] at hmono
  calc (eLpNorm (fun ω => m θ ω - m θ' ω) 2 P).toReal
      ≤ (ENNReal.ofReal (‖θ - θ'‖ * (eLpNorm menv 2 P).toReal)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono
    _ = ‖θ - θ'‖ * (eLpNorm menv 2 P).toReal := by
        rw [ENNReal.toReal_ofReal (by positivity)]
    _ = (eLpNorm menv 2 P).toReal * ‖θ - θ'‖ := by ring

/-- **Finite-dimensional `L²`-covering bound for the centered Lipschitz class.**

For `F_full = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ ≤ 1}` with a common `L²(P)` Lipschitz
envelope `menv`, the `L²(P)` covering number is polynomial in `1/s`:

    N_{L²}(s, F_full) ≤ (C/s)^d   for `0 < s ≤ ‖menv‖₂ + 1`,

with `C` depending only on `θ₀` (via the ball radius) and `‖menv‖₂`. Route: an
`η`-Euclidean-net of the ball `‖θ − θ₀‖ ≤ 1` (with `η = s/(‖menv‖₂+1)`) becomes an
`s`-`L²`-net of `F_full` by `distL2_centeredDiff_le`; the finite-dim Euclidean cover
`coveringNumber_le_of_bounded_euclidean` supplies `|S| ≤ (C_e/η)^d`.

This is the covering-number input to vdV Theorem 2.14.1 and Corollary 19.35. -/
theorem l2CoveringNumber_centeredLipschitz_le
    {d : ℕ} {P : Measure Ω}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 < s → s ≤ (eLpNorm menv 2 P).toReal + 1 →
      ∃ N : ℕ, l2CoveringNumber P
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ 1 ∧
            g = fun ω => m θ ω - m θ₀ ω} s ≤ (N : ℕ∞) ∧
        (N : ℝ) ≤ (C / s) ^ d := by
  classical
  set M : ℝ := (eLpNorm menv 2 P).toReal with hMdef
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  -- Euclidean covering bound for the parameter ball `Θ = closedBall θ₀ 1`.
  obtain ⟨Ce, hCe_pos, hcover⟩ :=
    coveringNumber_le_of_bounded_euclidean (Metric.closedBall θ₀ 1) Metric.isBounded_closedBall
  refine ⟨Ce * (M + 1), by positivity, fun s hs hs_le => ?_⟩
  -- Net scale `η = s/(M+1) ∈ (0, 1]`.
  set η : ℝ := s / (M + 1) with hηdef
  have hMp1_pos : (0 : ℝ) < M + 1 := by positivity
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  have hη_le : η ≤ 1 := by rw [hηdef, div_le_one hMp1_pos]; linarith
  obtain ⟨S, hSΘ, hΘcover, hScard⟩ := hcover η hη_pos hη_le
  -- The `L²`-net: images of the θ-net under `θ ↦ (ω ↦ m θ ω − m θ₀ ω)`.
  set F_full : Set (Ω → ℝ) :=
    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ 1 ∧
      g = fun ω => m θ ω - m θ₀ ω} with hFdef
  set Simg : Finset (Ω → ℝ) := S.image (fun c => fun ω => m c ω - m θ₀ ω) with hSimg
  refine ⟨Simg.card, ?_, ?_⟩
  · -- `l2CoveringNumber P F_full s ≤ |Simg|`.
    refine l2CoveringNumber_le_of_net ?_ ?_
    · -- `Simg ⊆ F_full`.
      intro g hg
      rw [hSimg, Finset.coe_image, Set.mem_image] at hg
      obtain ⟨c, hcS, rfl⟩ := hg
      have hc_ball : c ∈ Metric.closedBall θ₀ 1 := hSΘ (Finset.mem_coe.mpr hcS)
      rw [hFdef]
      exact ⟨c, by rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hc_ball, rfl⟩
    · -- Every `g ∈ F_full` is within `distL2 < s` of some net point.
      intro g hg
      rw [hFdef, Set.mem_setOf_eq] at hg
      obtain ⟨θ, hθ, rfl⟩ := hg
      have hθΘ : θ ∈ Metric.closedBall θ₀ 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact hθ
      obtain ⟨c, hcS, hθc⟩ := Set.mem_iUnion₂.mp (hΘcover hθΘ)
      refine ⟨fun ω => m c ω - m θ₀ ω, ?_, ?_⟩
      · rw [hSimg]; exact Finset.mem_image_of_mem _ hcS
      · -- `distL2 (m_θ − m_{θ₀}) (m_c − m_{θ₀}) = distL2 (m_θ) (m_c) ≤ M‖θ−c‖ < s`.
        have hdist_eq : distL2 P (fun ω => m θ ω - m θ₀ ω) (fun ω => m c ω - m θ₀ ω)
            = distL2 P (fun ω => m θ ω) (fun ω => m c ω) := by
          unfold distL2
          congr 1
          apply eLpNorm_congr_ae
          filter_upwards with ω
          simp only [Pi.sub_apply]; ring
        rw [hdist_eq]
        have hle := distL2_centeredDiff_le m menv hmenv hLip θ c
        have hθc_lt : ‖θ - c‖ < η := by
          rw [← dist_eq_norm]; exact Metric.mem_ball.mp hθc
        calc distL2 P (fun ω => m θ ω) (fun ω => m c ω)
            ≤ M * ‖θ - c‖ := hle
          _ ≤ M * η := by
              rcases eq_or_lt_of_le hM_nn with hM0 | hMpos
              · rw [← hM0]; simp
              · exact mul_le_mul_of_nonneg_left hθc_lt.le hM_nn
          _ < s := by
              have hrw : M * η = M * s / (M + 1) := by rw [hηdef]; ring
              rw [hrw, div_lt_iff₀ hMp1_pos]
              nlinarith [hs]
  · -- Cardinality: `|Simg| ≤ |S| ≤ (Ce/η)^d = (Ce(M+1)/s)^d`.
    have hcard_le : (Simg.card : ℝ) ≤ (S.card : ℝ) := by
      rw [hSimg]; exact_mod_cast Finset.card_image_le
    calc (Simg.card : ℝ) ≤ (S.card : ℝ) := hcard_le
      _ ≤ (Ce / η) ^ d := hScard
      _ = (Ce * (M + 1) / s) ^ d := by
          rw [hηdef, div_div_eq_mul_div]

/-! ## Fixed-center shell-covering geometric bound

**The soundness correction (vdV Lemma 19.38 note, book p.289).** The uniform-entropy counterpart
of the *localized small-`L²`-ball* maximal inequality "appears to be untrue" (vdV): the
pairwise-difference slice `(F − F)_{δq}` has pointwise envelope `2·menv` (base-point degeneracy —
`m_θ − m_{θ'}` depends on both `θ` and the base `θ'`), so its covering number `~(‖menv‖₂/ε)^d`
has **no `δ` in the numerator** and the spurious `√log(1/δ)` does not cancel. The clean `C·δ`
bound holds ONLY over the **fixed-center shell**

    M_δ = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ ≤ δ},   envelope `δ·menv`,

whose covering number IS a scale-free `(δ/s)` ratio (`N(s, M_δ) ≤ (C·δ/s)^d`). This is
vdV Cor 19.35 / Thm 2.14.1. The results below are therefore stated over `M_δ`. -/

/-- **Shell-covering bound** — vdV Corollary 19.35 / Lemma 19.38.

For the **fixed-center shell** `M_δ = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ ≤ δ}` (envelope `δ·menv`),
the `L²(P)` covering number at scale `s ≤ δ` is bounded by the *ratio* `δ/s`:

    N_{L²}(s, M_δ) ≤ (C · δ / s)^d   for `0 < s ≤ δ`,

with `C` depending only on `θ₀` (via the unit-ball covering constant) and `‖menv‖₂`. This IS the
scale-free covering bound the uniform-entropy chaining needs: the scale is relative to the shell
radius `δ`, so `δ/s ≥ 1` and the entropy integral `∫₀^δ √log N(ε,M_δ)dε` comes out linear in `δ`
with a `δ`-free constant (`sqrt_log_pow_ratio_lintegral_le`). The `d` (not `2d`) power reflects
that `M_δ` is a single-parameter shell, not a pairwise-difference slice.

The proof rescales `l2CoveringNumber_centeredLipschitz_le` to the shell: an
`η`-Euclidean-net `S` of the UNIT ball `closedBall θ₀ 1` (`coveringNumber_le_of_bounded_euclidean`,
`|S| ≤ (Ce/η)^d`) is mapped by the **δ-dilation** `c ↦ θ₀ + δ•(c − θ₀)` to a net of the shell
`closedBall θ₀ δ`; the `L²` Lipschitz width `distL2_centeredDiff_le` (`≤ ‖menv‖₂·δ·‖u−c‖`) turns
it into an `s`-`L²`-net of `M_δ` at `η = s/((‖menv‖₂+1)·δ)` (the `+1` slack forces strict `< s`).

The theorem is stated over the closed shell `‖θ−θ₀‖ ≤ δ`, so the
δ-dilation maps net points into the shell. The open-shell modulus theorem
`centeredLipschitz_localizedModulus_bound` follows by `supNormOver_mono`.

This is the geometric core of vdV Theorem 2.14.1 and Corollary 19.35. -/
theorem l2CoveringNumber_shell_le
    {d : ℕ} {P : Measure Ω}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ s : ℝ, 0 < s → s ≤ δ →
      ∃ N : ℕ, l2CoveringNumber P
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω} s ≤ (N : ℕ∞) ∧
        (N : ℝ) ≤ (C * δ / s) ^ d := by
  classical
  set M : ℝ := (eLpNorm menv 2 P).toReal with hMdef
  have hM_nn : 0 ≤ M := ENNReal.toReal_nonneg
  have hMp1_pos : (0 : ℝ) < M + 1 := by positivity
  obtain ⟨Ce, hCe_pos, hcover⟩ :=
    coveringNumber_le_of_bounded_euclidean (Metric.closedBall θ₀ 1) Metric.isBounded_closedBall
  refine ⟨Ce * (M + 1), by positivity, fun δ hδ s hs hsδ => ?_⟩
  -- Net scale `η = s/((M+1)·δ) ∈ (0, 1]`.
  set η : ℝ := s / ((M + 1) * δ) with hηdef
  have hden_pos : (0 : ℝ) < (M + 1) * δ := by positivity
  have hη_pos : 0 < η := by rw [hηdef]; positivity
  have hη_le : η ≤ 1 := by
    rw [hηdef, div_le_one hden_pos]
    nlinarith [hsδ, mul_nonneg hM_nn hδ.le]
  obtain ⟨S, hSΘ, hΘcover, hScard⟩ := hcover η hη_pos hη_le
  set Mδ : Set (Ω → ℝ) :=
    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
      g = fun ω => m θ ω - m θ₀ ω} with hMδdef
  -- δ-dilation of the θ-net: `c ↦ (ω ↦ m (θ₀ + δ•(c−θ₀)) ω − m θ₀ ω)`.
  set Simg : Finset (Ω → ℝ) :=
    S.image (fun c => fun ω => m (θ₀ + δ • (c - θ₀)) ω - m θ₀ ω) with hSimg
  refine ⟨Simg.card, ?_, ?_⟩
  · refine l2CoveringNumber_le_of_net ?_ ?_
    · -- `Simg ⊆ Mδ`.
      intro g hg
      rw [hSimg, Finset.coe_image, Set.mem_image] at hg
      obtain ⟨c, hcS, rfl⟩ := hg
      have hc_ball : c ∈ Metric.closedBall θ₀ 1 := hSΘ (Finset.mem_coe.mpr hcS)
      have hc_norm : ‖c - θ₀‖ ≤ 1 := by
        rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp hc_ball
      rw [hMδdef]
      refine ⟨θ₀ + δ • (c - θ₀), ?_, rfl⟩
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      calc δ * ‖c - θ₀‖ ≤ δ * 1 := mul_le_mul_of_nonneg_left hc_norm hδ.le
        _ = δ := mul_one δ
    · -- Coverage: every `g ∈ Mδ` is within `distL2 < s` of a dilated net point.
      intro g hg
      rw [hMδdef, Set.mem_setOf_eq] at hg
      obtain ⟨θ, hθ, rfl⟩ := hg
      set u : EuclideanSpace ℝ (Fin d) := θ₀ + δ⁻¹ • (θ - θ₀) with hudef
      have hu_norm : ‖u - θ₀‖ ≤ 1 := by
        have huθ : u - θ₀ = δ⁻¹ • (θ - θ₀) := by rw [hudef, add_sub_cancel_left]
        rw [huθ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
        calc δ⁻¹ * ‖θ - θ₀‖ ≤ δ⁻¹ * δ :=
              mul_le_mul_of_nonneg_left hθ (inv_pos.mpr hδ).le
          _ = 1 := inv_mul_cancel₀ hδ.ne'
      have huΘ : u ∈ Metric.closedBall θ₀ 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]; exact hu_norm
      obtain ⟨c, hcS, hcu⟩ := Set.mem_iUnion₂.mp (hΘcover huΘ)
      have hc_norm : ‖c - θ₀‖ ≤ 1 := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp (hSΘ (Finset.mem_coe.mpr hcS))
      have hcu_lt : ‖u - c‖ < η := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hcu
      refine ⟨fun ω => m (θ₀ + δ • (c - θ₀)) ω - m θ₀ ω, ?_, ?_⟩
      · rw [hSimg]; exact Finset.mem_image_of_mem _ hcS
      · -- `distL2 (m_θ − m_θ₀) (m_{θ_c} − m_θ₀) = distL2 m_θ m_{θ_c} ≤ M‖θ−θ_c‖ < s`.
        have hdist_eq : distL2 P (fun ω => m θ ω - m θ₀ ω)
              (fun ω => m (θ₀ + δ • (c - θ₀)) ω - m θ₀ ω)
            = distL2 P (fun ω => m θ ω) (fun ω => m (θ₀ + δ • (c - θ₀)) ω) := by
          unfold distL2
          congr 1
          apply eLpNorm_congr_ae
          filter_upwards with ω
          simp only [Pi.sub_apply]; ring
        rw [hdist_eq]
        have hle := distL2_centeredDiff_le m menv hmenv hLip θ (θ₀ + δ • (c - θ₀))
        -- `θ − (θ₀ + δ•(c−θ₀)) = δ•(u − c)`.
        have hvec : θ - (θ₀ + δ • (c - θ₀)) = δ • (u - c) := by
          simp only [hudef, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hδ.ne', one_smul]
          abel
        calc distL2 P (fun ω => m θ ω) (fun ω => m (θ₀ + δ • (c - θ₀)) ω)
            ≤ M * ‖θ - (θ₀ + δ • (c - θ₀))‖ := hle
          _ = M * (δ * ‖u - c‖) := by
              rw [hvec, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
          _ ≤ M * (δ * η) := by
              apply mul_le_mul_of_nonneg_left _ hM_nn
              exact mul_le_mul_of_nonneg_left hcu_lt.le hδ.le
          _ < s := by
              have hrw : M * (δ * η) = M * s / (M + 1) := by
                rw [hηdef]; field_simp
              rw [hrw, div_lt_iff₀ hMp1_pos]
              nlinarith [hs, hM_nn]
  · -- Cardinality: `|Simg| ≤ |S| ≤ (Ce/η)^d = (Ce(M+1)δ/s)^d`.
    have hcard_le : (Simg.card : ℝ) ≤ (S.card : ℝ) := by
      rw [hSimg]; exact_mod_cast Finset.card_image_le
    calc (Simg.card : ℝ) ≤ (S.card : ℝ) := hcard_le
      _ ≤ (Ce / η) ^ d := hScard
      _ = (Ce * (M + 1) * δ / s) ^ d := by
          congr 1
          rw [hηdef, div_div_eq_mul_div]
          ring

/-- `∫₀^{δq} √(δq/ε) dε = 2·δq`, the scale-free `ε^{-1/2}` integral.
Via `√(δq/ε) = √δq · ε^{-1/2}`, `ofReal_integral_eq_lintegral_ofReal`, and `integral_rpow`. -/
private lemma lintegral_sqrt_ratio {δq : ℝ} (hδq : 0 < δq) :
    ∫⁻ ε in Set.Ioc (0 : ℝ) δq, ENNReal.ofReal (Real.sqrt (δq / ε)) ∂volume
      = ENNReal.ofReal (2 * δq) := by
  -- `√(δq/ε) = √δq · ε^{-1/2}` on `(0, δq]`.
  have hfun : Set.EqOn (fun ε : ℝ => Real.sqrt (δq / ε))
      (fun ε => Real.sqrt δq * ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 δq) := by
    intro ε hε
    have hε0 : 0 < ε := hε.1
    change Real.sqrt (δq / ε) = Real.sqrt δq * ε ^ (-(1 / 2) : ℝ)
    rw [Real.rpow_neg hε0.le, ← Real.sqrt_eq_rpow, Real.sqrt_div hδq.le, div_eq_mul_inv]
  have hint_pow : IntegrableOn (fun ε : ℝ => ε ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 δq) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).1
  have hbase : IntegrableOn (fun ε : ℝ => Real.sqrt δq * ε ^ (-(1 / 2) : ℝ))
      (Set.Ioc 0 δq) volume := hint_pow.const_mul (Real.sqrt δq)
  have hint : IntegrableOn (fun ε : ℝ => Real.sqrt (δq / ε)) (Set.Ioc 0 δq) volume :=
    hbase.congr_fun hfun.symm measurableSet_Ioc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 δq)] (fun ε => Real.sqrt (δq / ε)) :=
    Eventually.of_forall (fun ε => Real.sqrt_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioc hfun, integral_const_mul,
    ← intervalIntegral.integral_of_le hδq.le, integral_rpow (Or.inl (by norm_num))]
  have h0 : (0 : ℝ) ^ (-(1 / 2) + 1 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have hd : δq ^ (-(1 / 2) + 1 : ℝ) = Real.sqrt δq := by
    rw [show (-(1 / 2) + 1 : ℝ) = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  rw [h0, hd, sub_zero, show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num,
    show Real.sqrt δq * (Real.sqrt δq / (1 / 2)) = 2 * (Real.sqrt δq * Real.sqrt δq) from by ring,
    Real.mul_self_sqrt hδq.le]

/-- **Scale-free finite-dimensional entropy integral.**

For `C > 0`, `p : ℕ`,

    ∫₀^{δq} √log(1 + (C·δq/ε)^p) dε ≤ Cp · δq   for every `δq > 0`,

with `Cp` **independent of `δq`** (the scale-free constant): the covering scale is relative to
the slice radius, so `y := δq/ε ≥ 1` and `√log(1 + (C·y)^p) ≤ B·√y` with
`B = √(log 2 + p|log C| + p)`, whence `∫₀^{δq} √log(…) ≤ B·∫₀^{δq} √(δq/ε) dε = B·2δq`
(`lintegral_sqrt_ratio`). This is the clean removal of the spurious `√log(1/δq)`. -/
theorem sqrt_log_pow_ratio_lintegral_le (C : ℝ) (hC : 0 < C) (p : ℕ) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ δq : ℝ, 0 < δq →
      ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δq / ε) ^ p))) ∂volume
        ≤ ENNReal.ofReal (Cp * δq) := by
  set A : ℝ := Real.log 2 + p * |Real.log C| + p with hAdef
  have hA_pos : 0 < A := by
    have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ (p : ℝ) * |Real.log C| := by positivity
    rw [hAdef]; positivity
  set B : ℝ := Real.sqrt A with hBdef
  have hB_pos : 0 < B := Real.sqrt_pos.mpr hA_pos
  have hB_nn : 0 ≤ B := hB_pos.le
  refine ⟨2 * B, by positivity, fun δq hδq => ?_⟩
  -- Pointwise: `√log(1 + (Cδq/ε)^p) ≤ B·√(δq/ε)` on `(0, δq]`.
  have hpoint : ∀ ε ∈ Set.Ioc (0 : ℝ) δq,
      Real.sqrt (Real.log (1 + (C * δq / ε) ^ p)) ≤ B * Real.sqrt (δq / ε) := by
    intro ε hε
    obtain ⟨hε0, hεδ⟩ := hε
    set y : ℝ := δq / ε with hy
    have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hε0]; linarith
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    have hCδε : C * δq / ε = C * y := by rw [hy]; ring
    rw [hCδε]
    have hlogy_nn : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hlogy_le : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    have hlog_le : Real.log (1 + (C * y) ^ p) ≤ A * y := by
      have hl2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hl2 : Real.log 2 ≤ Real.log 2 * y := by nlinarith [hl2_pos, hy1]
      by_cases hge : 1 ≤ (C * y) ^ p
      · have hCyp_pos : 0 < (C * y) ^ p := by positivity
        have ha : (0 : ℝ) ≤ (p : ℝ) * |Real.log C| :=
          mul_nonneg (Nat.cast_nonneg p) (abs_nonneg _)
        have hpc : (p : ℝ) * |Real.log C| ≤ (p : ℝ) * |Real.log C| * y := by nlinarith [ha, hy1]
        have hply : (p : ℝ) * Real.log y ≤ (p : ℝ) * y :=
          mul_le_mul_of_nonneg_left hlogy_le (Nat.cast_nonneg p)
        calc Real.log (1 + (C * y) ^ p)
            ≤ Real.log (2 * (C * y) ^ p) := Real.log_le_log (by positivity) (by linarith)
          _ = Real.log 2 + p * Real.log (C * y) := by
              rw [Real.log_mul two_ne_zero hCyp_pos.ne', Real.log_pow]
          _ = Real.log 2 + p * (Real.log C + Real.log y) := by rw [Real.log_mul hC.ne' hy0.ne']
          _ ≤ Real.log 2 + p * (|Real.log C| + Real.log y) := by
              gcongr; exact le_abs_self _
          _ = Real.log 2 + p * |Real.log C| + p * Real.log y := by ring
          _ ≤ Real.log 2 * y + p * |Real.log C| * y + p * y := by linarith
          _ = A * y := by rw [hAdef]; ring
      · have hlt : (C * y) ^ p < 1 := not_le.mp hge
        have hCyp_nn : (0 : ℝ) ≤ (C * y) ^ p := by positivity
        calc Real.log (1 + (C * y) ^ p)
            ≤ Real.log 2 := Real.log_le_log (by positivity) (by linarith)
          _ ≤ Real.log 2 * y := hl2
          _ ≤ A * y := by
              rw [hAdef]
              nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) * |Real.log C|) hy0.le,
                mul_nonneg (Nat.cast_nonneg p) hy0.le]
    calc Real.sqrt (Real.log (1 + (C * y) ^ p))
        ≤ Real.sqrt (A * y) := Real.sqrt_le_sqrt hlog_le
      _ = Real.sqrt A * Real.sqrt y := Real.sqrt_mul hA_pos.le y
      _ = B * Real.sqrt y := by rw [hBdef]
  -- Integrate the pointwise bound.
  calc ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
        ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δq / ε) ^ p))) ∂volume
      ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) δq, ENNReal.ofReal (B * Real.sqrt (δq / ε)) ∂volume :=
        setLIntegral_mono_ae' measurableSet_Ioc
          (Eventually.of_forall fun ε hε => ENNReal.ofReal_le_ofReal (hpoint ε hε))
    _ = ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
          ENNReal.ofReal B * ENNReal.ofReal (Real.sqrt (δq / ε)) ∂volume :=
        lintegral_congr fun ε => ENNReal.ofReal_mul hB_nn
    _ = ENNReal.ofReal B * ∫⁻ ε in Set.Ioc (0 : ℝ) δq,
          ENNReal.ofReal (Real.sqrt (δq / ε)) ∂volume :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal B * ENNReal.ofReal (2 * δq) := by rw [lintegral_sqrt_ratio hδq]
    _ = ENNReal.ofReal (2 * B * δq) := by
        rw [← ENNReal.ofReal_mul hB_nn]; congr 1; ring

/-! ## Scale-free finite-dimensional covering entropy -/

/-- **Scale-free fixed-center shell covering entropy integral** (vdV Corollary 19.35).

For the fixed-center shell `M_δ = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ ≤ δ}` the covering entropy
integral is linear in `δ` with a `δ`-free constant:

    ∫₀^δ √log(1 + N_{L²}(ε, M_δ)) dε ≤ C_d · δ   for all `δ > 0`.

Assembled from the shell-covering bound (`l2CoveringNumber_shell_le`, the scale-free `δ/ε` ratio)
and the scale-free integral (`sqrt_log_pow_ratio_lintegral_le` at power `d`): dominate the entropy
integrand pointwise via `entropyWeight_mono`, then integrate. This is the clean replacement for the
bracketing `J_{[]}(δ) ≈ δ√log(1/δ)` (the spurious `√log` cancels because the covering scale is
*relative* to the shell radius).

This is the entropy-integral bound in vdV Theorem 2.14.1 and Corollary 19.35. -/
theorem l2CoveringEntropyIntegral_shell_le
    {d : ℕ} {P : Measure Ω}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ δ : ℝ, 0 < δ →
      l2CoveringEntropyIntegral δ
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω} P
        ≤ ENNReal.ofReal (Cd * δ) := by
  classical
  obtain ⟨C, hC_pos, hshell⟩ := l2CoveringNumber_shell_le m θ₀ menv hmenv hLip
  obtain ⟨Cp, hCp_pos, hInt⟩ := sqrt_log_pow_ratio_lintegral_le C hC_pos d
  refine ⟨Cp, hCp_pos, fun δ hδ => ?_⟩
  set Mδ : Set (Ω → ℝ) :=
    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
      g = fun ω => m θ ω - m θ₀ ω} with hMδdef
  -- Pointwise domination of the entropy integrand on `Ioc 0 δ`.
  have hdom : ∀ ε ∈ Set.Ioc (0 : ℝ) δ,
      entropyWeight (l2CoveringNumber P Mδ ε)
        ≤ ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δ / ε) ^ d))) := by
    intro ε hε
    obtain ⟨hε0, hεδ⟩ := hε
    obtain ⟨N, hN_le, hN_bd⟩ := hshell δ hδ ε hε0 hεδ
    calc entropyWeight (l2CoveringNumber P Mδ ε)
        ≤ entropyWeight (N : ℕ∞) := entropyWeight_mono hN_le
      _ = ENNReal.ofReal (Real.sqrt (Real.log (1 + (N : ℝ)))) := entropyWeight_coe N
      _ ≤ ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δ / ε) ^ d))) := by
          apply ENNReal.ofReal_le_ofReal
          apply Real.sqrt_le_sqrt
          apply Real.log_le_log (by positivity)
          linarith [hN_bd]
  -- Integrate the pointwise bound.
  calc l2CoveringEntropyIntegral δ Mδ P
      = ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
          entropyWeight (l2CoveringNumber P Mδ ε) ∂volume := rfl
    _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * δ / ε) ^ d))) ∂volume := by
        exact setLIntegral_mono_ae' measurableSet_Ioc (Eventually.of_forall hdom)
    _ ≤ ENNReal.ofReal (Cp * δ) := hInt δ hδ

/-! ## Covering-chaining maximal inequality -/

/-- **Envelope-tail Chebyshev bound for the shell envelope `δ·menv`.**

For the shell envelope `Φ_δ = δ·menv ∈ L²(P)`, the `√n`-scaled envelope tail at the
`δ`-proportional truncation threshold `√n·κ·δ` (which, since `Φ_δ = δ·menv`, cancels the `δ` into
the `δ`-free level set `{√n·κ < |menv|}`) is bounded **linearly in `δ`, uniformly in `n`**:

    √n · ∫⁻ |δ·menv| · 1_{√n·κ < |menv|} dP ≤ C · δ.

This is the clean `β = 1` envelope-tail estimate (no `√log`, no `n`-dependence): the truncation
threshold is proportional to the envelope radius `δ`, so `δ` cancels in the level set and the
factor `√n · ∫⁻ |menv| 1_{√n·κ < |menv|}` is bounded by the `n`- and `δ`-free constant `‖menv‖₂²/κ`
via the elementary estimate `|menv|·1_{|menv|>a} ≤ menv²/a` at `a = √n·κ` (`√n ≤ |menv|/κ` on the
level set). This bounds the envelope-tail term in
`centeredLipschitz_shellModulus_bound_closed`. -/
private lemma shellEnvelope_tail_le
    {P : Measure Ω} (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ,
      ENNReal.ofReal (Real.sqrt n)
          * ∫⁻ ω, ENNReal.ofReal (δ * |menv ω|)
              * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω ∂P
        ≤ ENNReal.ofReal (C * δ) := by
  -- `T := ∫⁻ menv² < ⊤` from `menv ∈ L²`.
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
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (1 / κ) * T with hK₀_def
  have hK₀_ne : K₀ ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hT_ne)).ne
  refine ⟨K₀.toReal + 1, by positivity, fun δ hδ n => ?_⟩
  -- Pointwise: `√n·ofReal(δ|menv|)·1_A ≤ ofReal δ · ofReal(menv²/κ)`.
  have hpt : ∀ ω : Ω,
      ENNReal.ofReal (Real.sqrt n) * (ENNReal.ofReal (δ * |menv ω|)
          * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω)
        ≤ ENNReal.ofReal δ * ENNReal.ofReal (menv ω ^ 2 / κ) := by
    intro ω
    by_cases hω : ω ∈ {x | Real.sqrt n * κ < |menv x|}
    · rw [Set.indicator_of_mem hω, Pi.one_apply, mul_one]
      have hω' : Real.sqrt n * κ < |menv ω| := hω
      have hsn_le : Real.sqrt n ≤ |menv ω| / κ := by
        rw [le_div_iff₀ hκ]; linarith [hω']
      have h1 : Real.sqrt n * |menv ω| ≤ menv ω ^ 2 / κ := by
        calc Real.sqrt n * |menv ω|
            ≤ (|menv ω| / κ) * |menv ω| :=
              mul_le_mul_of_nonneg_right hsn_le (abs_nonneg _)
          _ = (|menv ω| * |menv ω|) / κ := by ring
          _ = menv ω ^ 2 / κ := by rw [← sq, sq_abs]
      have hstep : Real.sqrt n * (δ * |menv ω|) ≤ δ * (menv ω ^ 2 / κ) := by
        rw [show Real.sqrt n * (δ * |menv ω|) = δ * (Real.sqrt n * |menv ω|) by ring]
        exact mul_le_mul_of_nonneg_left h1 hδ.le
      calc ENNReal.ofReal (Real.sqrt n) * ENNReal.ofReal (δ * |menv ω|)
          = ENNReal.ofReal (Real.sqrt n * (δ * |menv ω|)) :=
            (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
        _ ≤ ENNReal.ofReal (δ * (menv ω ^ 2 / κ)) := ENNReal.ofReal_le_ofReal hstep
        _ = ENNReal.ofReal δ * ENNReal.ofReal (menv ω ^ 2 / κ) :=
            ENNReal.ofReal_mul hδ.le
    · rw [Set.indicator_of_notMem hω]; simp
  calc ENNReal.ofReal (Real.sqrt n)
          * ∫⁻ ω, ENNReal.ofReal (δ * |menv ω|)
              * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω ∂P
      = ∫⁻ ω, ENNReal.ofReal (Real.sqrt n) * (ENNReal.ofReal (δ * |menv ω|)
              * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω) ∂P :=
        (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal δ * ENNReal.ofReal (menv ω ^ 2 / κ) ∂P :=
        lintegral_mono hpt
    _ = ENNReal.ofReal δ * ∫⁻ ω, ENNReal.ofReal (menv ω ^ 2 / κ) ∂P :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal δ * K₀ := by
        congr 1
        rw [hK₀_def, hT_def,
          ← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (1 / κ)) _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun ω => ?_
        rw [← ENNReal.ofReal_mul (div_nonneg zero_le_one hκ.le)]
        congr 1; ring
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (K₀.toReal + 1) := by
        gcongr
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one,
          ENNReal.ofReal_toReal hK₀_ne, ENNReal.ofReal_one]
        exact le_add_right le_rfl
    _ = ENNReal.ofReal ((K₀.toReal + 1) * δ) := by
        rw [← ENNReal.ofReal_mul hδ.le]; congr 1; ring

/-- **Generic clamp-lift split** (covering counterpart of `localized_supNorm_lift`,
`ChainingAssembly.lean`, stated over an arbitrary enveloped class `G` rather than the bracketing
`localizedDifferenceClass`). Bounds the integrated empirical-process modulus over `G` by the
modulus over the clamped class `truncateClass G Mc` plus the `√n`-truncation excess at level `Mc`:

    ∫⁻ ‖𝔾ₙ‖_G ≤ ∫⁻ ‖𝔾ₙ‖_{truncate G Mc} + 4√n·∫⁻ |Φ|·1{Mc<|Φ|}.

Per `ξ`: `𝔾ₙ h = 𝔾ₙ(clampFn Mc h) + 𝔾ₙ(h − clampFn Mc h)` (`empiricalProcess_add`, both pieces
integrable since `|·| ≤ Φ ∈ L¹`); `supNormOver` is subadditive; the clamped sup reindexes to
`truncateClass G Mc`; the excess class `{h − clampFn Mc h}` is pointwise dominated by
`Ψ = |Φ|·1{Mc<|Φ|}`, so its integrated sup is closed by the measurable envelope process
`Bproc ξ = √n·(empAvg Ψ ξ + ∫⁻Ψ)` (`supNormProcess_dominated_pointwise_bound`) via
`lintegral_add_right'`. Faithful port; only the class `G` is generalised. -/
private lemma supNorm_clamp_lift
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (G : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ)
    (hΦ_env : IsEnvelope G Φ) (hG_meas : ∀ h ∈ G, Measurable h)
    (hΦ_int : Integrable Φ P)
    (Mc : ℝ) (hMc : 0 ≤ Mc) (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ξ, supNormOver G
          (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
      ≤ (∫⁻ ξ, supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
        + 4 * ENNReal.ofReal (Real.sqrt n)
            * ∫⁻ x, ENNReal.ofReal (|Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x) ∂P := by
  classical
  have hΦ_envG : IsEnvelope G Φ := hΦ_env
  set Ψ : Ω → ℝ := fun x => |Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x with hΨ_def
  set 𝒢 : Set (Ω → ℝ) := {g | ∃ h ∈ G, g = fun x => h x - clampFn Mc h x} with h𝒢_def
  have hΦ_abs_meas : Measurable (fun x => |Φ x|) := hΦ_meas.norm
  have hset_meas : MeasurableSet {y | Mc < |Φ y|} := hΦ_abs_meas measurableSet_Ioi
  have hΨ_meas : Measurable Ψ := by
    refine hΦ_meas.norm.mul ?_
    exact measurable_const.indicator hset_meas
  have hΨ_nn : ∀ x, 0 ≤ Ψ x := by
    intro x
    refine mul_nonneg (abs_nonneg _) ?_
    by_cases hx : x ∈ {y | Mc < |Φ y|} <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hdom : ∀ g ∈ 𝒢, ∀ x, |g x| ≤ Ψ x := by
    rintro g ⟨h, hhG, rfl⟩ x
    have hhΦ : |h x| ≤ Φ x := hΦ_envG h hhG x
    change |h x - clampFn Mc h x| ≤ |Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x
    by_cases hx : x ∈ {y | Mc < |Φ y|}
    · rw [Set.indicator_of_mem hx]
      simp only [Pi.one_apply, mul_one]
      have h1 : |h x - clampFn Mc h x| ≤ |h x| := by
        unfold clampFn clampReal
        rcases le_total (h x) Mc with hle | hle <;>
          rcases le_total (-Mc) (h x) with hle2 | hle2 <;>
          rw [max_def, min_def] <;> split_ifs <;>
          rcases abs_cases (h x) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
          rw [e2] <;>
          rw [abs_sub_le_iff] <;> constructor <;> linarith
      exact le_trans h1 (le_trans hhΦ (le_abs_self _))
    · rw [Set.indicator_of_notMem hx]
      simp only [mul_zero]
      have hΦle : |Φ x| ≤ Mc := not_lt.mp (by simpa using hx)
      have hhle : |h x| ≤ Mc := le_trans (le_trans hhΦ (le_abs_self _)) hΦle
      have hcl : clampFn Mc h x = h x := by unfold clampFn; exact clampReal_of_mem hhle
      rw [hcl]; simp
  have hint_of_dom : ∀ {g : Ω → ℝ}, Measurable g → (∀ x, |g x| ≤ Φ x) → Integrable g P := by
    intro g hg_meas hg_dom
    refine Integrable.mono' hΦ_int hg_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hg_dom x)
  have h_pt : ∀ ξ : Ξ,
      supNormOver G (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
        ≤ supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
          + supNormOver 𝒢
              (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
    intro ξ
    refine iSup₂_le fun h hhG => ?_
    have hh_meas : Measurable h := hG_meas h hhG
    have hh_dom : ∀ x, |h x| ≤ Φ x := hΦ_envG h hhG
    have hclamp_meas : Measurable (clampFn Mc h) := clampFn_measurable hh_meas
    have hclamp_dom : ∀ x, |clampFn Mc h x| ≤ Φ x :=
      fun x => le_trans (abs_clampReal_le Mc hMc (h x)) (hh_dom x)
    have hh_int : Integrable h P := hint_of_dom hh_meas hh_dom
    have hclamp_int : Integrable (clampFn Mc h) P := hint_of_dom hclamp_meas hclamp_dom
    have hsplit : empiricalProcess P n (fun i : Fin n => X i.val ξ) h
        = empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)
          + empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (fun x => h x - clampFn Mc h x) := by
      rw [← empiricalProcess_add P n _ (clampFn Mc h) (fun x => h x - clampFn Mc h x)
        hclamp_int (hh_int.sub hclamp_int)]
      congr 1; funext x; ring
    simp only []
    rw [hsplit]
    calc ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)
            + empiricalProcess P n (fun i : Fin n => X i.val ξ) (fun x => h x - clampFn Mc h x)|
        ≤ ENNReal.ofReal
              (|empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)|
                + |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (fun x => h x - clampFn Mc h x)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ ≤ ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) (clampFn Mc h)|
            + ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ)
                (fun x => h x - clampFn Mc h x)| := ENNReal.ofReal_add_le
      _ ≤ supNormOver (truncateClass G Mc)
              (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
            + supNormOver 𝒢
                (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) := by
        refine add_le_add ?_ ?_
        · exact le_supNormOver (z := fun h => empiricalProcess P n
            (fun i : Fin n => X i.val ξ) h) ⟨h, hhG, rfl⟩
        · exact le_supNormOver (z := fun g => empiricalProcess P n
            (fun i : Fin n => X i.val ξ) g) ⟨h, hhG, rfl⟩
  set T : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P with hT_def
  set Bproc : Ξ → ℝ≥0∞ := fun ξ => ENNReal.ofReal (Real.sqrt n) *
      (ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) + T) with hBproc_def
  have hBproc_meas : Measurable Bproc := by
    refine Measurable.const_mul ?_ _
    refine Measurable.fun_add ?_ measurable_const
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΨ_meas.comp (hX_meas i.val)
  have h_excess_le : ∀ ξ : Ξ, supNormOver 𝒢
        (fun g => empiricalProcess P n (fun i : Fin n => X i.val ξ) g) ≤ Bproc ξ := by
    intro ξ
    exact supNormProcess_dominated_pointwise_bound (P := P) 𝒢 Ψ hdom n hn ξ
  have hΨ_ofReal_meas : Measurable (fun x => ENNReal.ofReal (Ψ x)) := hΨ_meas.ennreal_ofReal
  have hΨ_meas_avg : AEMeasurable
      (fun ξ : Ξ => ENNReal.ofReal
        (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))) μ := by
    refine Measurable.aemeasurable ?_
    refine Measurable.ennreal_ofReal ?_
    unfold empiricalAvg
    refine Measurable.const_mul ?_ _
    refine Finset.measurable_sum Finset.univ ?_
    intro i _
    exact hΨ_meas.comp (hX_meas i.val)
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have h_emp_to_P : ∫⁻ ξ, ENNReal.ofReal
      (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ ≤ T := by
    have h_pt_le : ∀ ξ : Ξ,
        ENNReal.ofReal (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ))
        ≤ ((n : ℝ≥0∞))⁻¹ * ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) := by
      intro ξ
      unfold empiricalAvg
      rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
      have hn_inv_eq : ENNReal.ofReal ((n : ℝ)⁻¹) = ((n : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hn_pos, ENNReal.ofReal_natCast]
      rw [hn_inv_eq]
      refine mul_le_mul_of_nonneg_left ?_ (zero_le)
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hΨ_nn _)]
    have hn_ne_top : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
    have hn_ne_zero : (n : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hn_pos_nat)
    have hinv_ne_top : ((n : ℝ≥0∞))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hn_ne_zero
    calc ∫⁻ ξ, ENNReal.ofReal
            (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ
        ≤ ∫⁻ ξ, ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ :=
          MeasureTheory.lintegral_mono h_pt_le
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∫⁻ ξ, ∑ i : Fin n, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ := by
          rw [MeasureTheory.lintegral_const_mul' _ _ hinv_ne_top]
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ i : Fin n, ∫⁻ ξ, ENNReal.ofReal (Ψ (X i.val ξ)) ∂μ := by
          congr 1
          rw [MeasureTheory.lintegral_finset_sum Finset.univ]
          intro i _
          exact hΨ_ofReal_meas.comp (hX_meas i.val)
      _ = ((n : ℝ≥0∞))⁻¹ *
            ∑ _i : Fin n, ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          have h_id : (μ.map (X i.val)) = P := by
            rw [← hX_law]; exact (hX_idem i.val).map_eq
          rw [← h_id]
          exact (MeasureTheory.lintegral_map hΨ_ofReal_meas (hX_meas i.val)).symm
      _ = ((n : ℝ≥0∞))⁻¹ * ((n : ℝ≥0∞)) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      _ = T := by rw [ENNReal.inv_mul_cancel hn_ne_zero hn_ne_top, one_mul, hT_def]
  have hBproc_int_le : ∫⁻ ξ, Bproc ξ ∂μ
      ≤ 4 * ENNReal.ofReal (Real.sqrt n) * T := by
    rw [hBproc_def]
    rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      MeasureTheory.lintegral_add_left' hΨ_meas_avg,
      MeasureTheory.lintegral_const, measure_univ, mul_one]
    calc ENNReal.ofReal (Real.sqrt n) *
            (∫⁻ ξ, ENNReal.ofReal
                (empiricalAvg Ψ n (fun j : Fin n => X j.val ξ)) ∂μ + T)
        ≤ ENNReal.ofReal (Real.sqrt n) * (T + T) :=
          mul_le_mul_of_nonneg_left (add_le_add h_emp_to_P le_rfl) (zero_le)
      _ = 2 * ENNReal.ofReal (Real.sqrt n) * T := by ring
      _ ≤ 4 * ENNReal.ofReal (Real.sqrt n) * T := by gcongr; norm_num
  calc ∫⁻ ξ, supNormOver G
          (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ
      ≤ ∫⁻ ξ, (supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h)
          + Bproc ξ) ∂μ := by
        refine MeasureTheory.lintegral_mono (fun ξ => ?_)
        exact le_trans (h_pt ξ) (add_le_add le_rfl (h_excess_le ξ))
    _ = (∫⁻ ξ, supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
        + ∫⁻ ξ, Bproc ξ ∂μ :=
        MeasureTheory.lintegral_add_right' _ hBproc_meas.aemeasurable
    _ ≤ (∫⁻ ξ, supNormOver (truncateClass G Mc)
            (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) h) ∂μ)
        + 4 * ENNReal.ofReal (Real.sqrt n) * ∫⁻ x, ENNReal.ofReal (Ψ x) ∂P := by
        have := hBproc_int_le
        rw [hT_def] at this
        gcongr

/-! ## Covering telescope comparison (dyadic sum ≤ covering entropy integral)

The **pure real-analysis** half of the covering Dudley chain: the geometric dyadic series
`Σ_q (1/2)^q·δ · √log(1 + N_{L²}((1/2)^q·δ, F))` is bounded by *twice* the covering entropy
integral `l2CoveringEntropyIntegral δ F P` (no empirical process involved). This is the covering
analogue of `dyadic_sum_le_bracketingEntropyIntegral` (`Bracketing.lean`). It
uses antitonicity of `l2CoveringNumber` in the scale: an `s₁`-net is an
`s₂`-net whenever `s₁ ≤ s₂`. -/

/-- `l2CoveringNumber` is antitone in the scale `s`: every `s₁`-net is an `s₂`-net for
`s₁ ≤ s₂`, so the infimum defining `l2CoveringNumber P F s₂` ranges over a superset. -/
private lemma l2CoveringNumber_antitone_eps {P : Measure Ω} {F : Set (Ω → ℝ)}
    {s₁ s₂ : ℝ} (hs : s₁ ≤ s₂) :
    l2CoveringNumber P F s₂ ≤ l2CoveringNumber P F s₁ := by
  unfold l2CoveringNumber
  refine iInf_mono fun S => ?_
  refine iInf_mono' fun hS => ⟨⟨hS.1, fun f hf => ?_⟩, le_rfl⟩
  obtain ⟨g, hgS, hg⟩ := hS.2 f hf
  exact ⟨g, hgS, lt_of_lt_of_le hg hs⟩

/-- The covering entropy integrand `ε ↦ entropyWeight (l2CoveringNumber P F ε)` is antitone in
`ε` (covering analogue of `entropyIntegrand_antitone_eps`). -/
private lemma covering_entropyWeight_antitone_eps {P : Measure Ω} {F : Set (Ω → ℝ)}
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    entropyWeight (l2CoveringNumber P F ε₂) ≤ entropyWeight (l2CoveringNumber P F ε₁) :=
  entropyWeight_mono (l2CoveringNumber_antitone_eps hε)

/-- The dyadic scales `(1/2)^q·δ` partition `Ioc 0 δ` into the intervals
`Ioc ((1/2)^{q+1}·δ) ((1/2)^q·δ)`. -/
private lemma covering_iUnion_dyadic_Ioc_eq {δ : ℝ} (hδ : 0 < δ) :
    ⋃ q : ℕ, Set.Ioc ((1/2 : ℝ)^(q+1) * δ) ((1/2 : ℝ)^q * δ) = Set.Ioc 0 δ := by
  have hhalf_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have hapos : ∀ q : ℕ, 0 < (1/2 : ℝ)^q * δ := fun q => by positivity
  apply Set.eq_of_subset_of_subset
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ioc] at hx
    obtain ⟨q, hlo, hhi⟩ := hx
    refine ⟨lt_trans (hapos (q+1)) hlo, ?_⟩
    refine le_trans hhi ?_
    calc (1/2 : ℝ)^q * δ ≤ 1 * δ := by
            apply mul_le_mul_of_nonneg_right _ hδ.le
            exact pow_le_one₀ hhalf_pos.le (by norm_num)
      _ = δ := one_mul δ
  · intro x hx
    simp only [Set.mem_Ioc] at hx
    obtain ⟨hx0, hxδ⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    have hexists : ∃ q : ℕ, (1/2 : ℝ)^q * δ < x := by
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < x / δ)
        (by norm_num : (1/2 : ℝ) < 1)
      exact ⟨N, (lt_div_iff₀ hδ).mp hN⟩
    classical
    let q₀ := Nat.find hexists
    have hq₀ : (1/2 : ℝ)^q₀ * δ < x := Nat.find_spec hexists
    have hq₀_pos : 1 ≤ q₀ := by
      rcases Nat.eq_zero_or_pos q₀ with h0 | h; swap; · exact h
      exfalso
      rw [show q₀ = 0 from h0] at hq₀; simp only [pow_zero, one_mul] at hq₀
      exact absurd hq₀ (not_lt.mpr hxδ)
    obtain ⟨p, hp⟩ : ∃ p, q₀ = p + 1 := ⟨q₀ - 1, by omega⟩
    have hprev : ¬ (1/2 : ℝ)^p * δ < x :=
      Nat.find_min hexists (by omega : p < q₀)
    refine ⟨p, ?_, not_lt.mp hprev⟩
    rw [hp] at hq₀
    exact hq₀

/-- Per-dyadic-interval lower bound for the covering integrand (covering copy of
`dyadic_term_le_two_setLIntegral`): on `Ioc ((1/2)^{q+1}·δ) ((1/2)^q·δ)` the integrand is `≥`
its right-endpoint value (antitonicity), and the interval has length exactly half the dyadic
weight, so `ofReal((1/2)^q·δ) · entropyWeight(N((1/2)^q·δ)) ≤ 2·∫⁻ over the interval`. -/
private lemma covering_dyadic_term_le_two_setLIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ENNReal.ofReal ((1/2 : ℝ)^q * δ)
        * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^q * δ))
      ≤ 2 * ∫⁻ ε in Set.Ioc ((1/2 : ℝ)^(q+1) * δ) ((1/2 : ℝ)^q * δ),
            entropyWeight (l2CoveringNumber P F ε) ∂volume := by
  set aq : ℝ := (1/2 : ℝ)^q * δ with haq
  set aq1 : ℝ := (1/2 : ℝ)^(q+1) * δ with haq1
  have haq_pos : 0 < aq := by rw [haq]; positivity
  have haq1_eq : aq1 = (1/2 : ℝ) * aq := by rw [haq1, haq]; ring
  have hconst_le : ∫⁻ _ε in Set.Ioc aq1 aq, entropyWeight (l2CoveringNumber P F aq) ∂volume
      ≤ ∫⁻ ε in Set.Ioc aq1 aq, entropyWeight (l2CoveringNumber P F ε) ∂volume := by
    refine setLIntegral_mono' measurableSet_Ioc (fun ε hε => ?_)
    exact covering_entropyWeight_antitone_eps hε.2
  rw [setLIntegral_const, Real.volume_Ioc] at hconst_le
  have hlen : aq - aq1 = (1/2 : ℝ) * aq := by rw [haq1_eq]; ring
  rw [hlen] at hconst_le
  have hsplit : ENNReal.ofReal aq = 2 * ENNReal.ofReal ((1/2 : ℝ) * aq) := by
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  calc ENNReal.ofReal aq * entropyWeight (l2CoveringNumber P F aq)
      = 2 * (entropyWeight (l2CoveringNumber P F aq) * ENNReal.ofReal ((1/2 : ℝ) * aq)) := by
        rw [hsplit]; ring
    _ ≤ 2 * ∫⁻ ε in Set.Ioc aq1 aq, entropyWeight (l2CoveringNumber P F ε) ∂volume := by
        gcongr

/-- **Covering telescope comparison.** The dyadic covering entropy
series is bounded by twice the covering entropy integral — the covering analogue of
`dyadic_sum_le_bracketingEntropyIntegral`. Factor `2` is exact: on each dyadic interval the
integrand dominates its right-endpoint value and the length is half the dyadic weight; the
disjoint intervals reassemble `Ioc 0 δ`. -/
private theorem covering_dyadic_sum_le_l2CoveringEntropyIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hδ : 0 < δ) :
    ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
        * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^q * δ))
      ≤ 2 * l2CoveringEntropyIntegral δ F P := by
  set I : ℕ → Set ℝ := fun q => Set.Ioc ((1/2 : ℝ)^(q+1) * δ) ((1/2 : ℝ)^q * δ) with hI
  have hI_meas : ∀ q, MeasurableSet (I q) := fun q => measurableSet_Ioc
  have hscale_anti : ∀ {m n : ℕ}, m ≤ n → (1/2 : ℝ)^n * δ ≤ (1/2 : ℝ)^m * δ := by
    intro m n hmn
    apply mul_le_mul_of_nonneg_right _ hδ.le
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hI_disj : Pairwise (Function.onFun Disjoint I) := by
    intro m n hmn
    wlog hlt : m < n generalizing m n
    · exact (this hmn.symm (by omega)).symm
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    simp only [hI, Set.mem_Ioc] at hxm hxn
    have : x ≤ (1/2 : ℝ)^(m+1) * δ := le_trans hxn.2 (hscale_anti (by omega))
    exact absurd hxm.1 (not_lt.mpr this)
  calc ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^q * δ))
      ≤ ∑' q : ℕ, 2 * ∫⁻ ε in I q, entropyWeight (l2CoveringNumber P F ε) ∂volume :=
        ENNReal.tsum_le_tsum (fun q => covering_dyadic_term_le_two_setLIntegral hδ q)
    _ = 2 * ∑' q : ℕ, ∫⁻ ε in I q, entropyWeight (l2CoveringNumber P F ε) ∂volume := by
        rw [ENNReal.tsum_mul_left]
    _ = 2 * ∫⁻ ε in ⋃ q, I q, entropyWeight (l2CoveringNumber P F ε) ∂volume := by
        rw [lintegral_iUnion hI_meas hI_disj]
    _ = 2 * l2CoveringEntropyIntegral δ F P := by
        unfold l2CoveringEntropyIntegral
        rw [hI, covering_iUnion_dyadic_Ioc_eq hδ]

/-! ## Population-covering series

The empirical-process estimate below uses the book-faithful uniform finite-discrete covering
chain, whose nets live in the realized sample metric. The population-covering series records
nets that certify that the shell is nonempty and hence that the regularized series has a
positive head term. -/

/-- **Minimal `L²`-net extraction (the `iInf` defining `l2CoveringNumber` is attained).**

When the `L²(P)` covering number of `F` at scale `s` is finite (bounded by some `N : ℕ`), the
infimum defining `l2CoveringNumber P F s` is *attained*: there is an actual finite `s`-net
`S ⊆ F` in the `distL2 P` semimetric whose cardinality **equals** `l2CoveringNumber P F s`
(in particular `≤ N`).

The shell-covering bound `l2CoveringNumber_shell_le` returns a cardinality bound,
while the population-series formulation also records an attaining net.

Proof: the admissible-net cardinalities `A = {|S| : S an s-net ⊆ F}` form a nonempty set of
naturals (nonempty because `l2CoveringNumber < ⊤`), whose least element `Nat.sInf A` is attained
by some net (`Nat.sInf_mem`); a two-sided `iInf`/`sInf` comparison identifies
`l2CoveringNumber P F s = (Nat.sInf A : ℕ∞)`. -/
private lemma l2CoveringNumber_exists_min_net {P : Measure Ω} {F : Set (Ω → ℝ)} {s : ℝ}
    {N : ℕ} (hle : l2CoveringNumber P F s ≤ (N : ℕ∞)) :
    ∃ S : Finset (Ω → ℝ), (↑S ⊆ F) ∧ (∀ f ∈ F, ∃ g ∈ S, distL2 P f g < s) ∧
      (S.card : ℕ∞) = l2CoveringNumber P F s := by
  classical
  -- Admissible nets exist, else the `iInf` would be `⊤ > N`.
  have hne : ∃ S : Finset (Ω → ℝ),
      (↑S ⊆ F) ∧ ∀ f ∈ F, ∃ g ∈ S, distL2 P f g < s := by
    by_contra hcon
    have htop : l2CoveringNumber P F s = ⊤ := by
      unfold l2CoveringNumber
      refine le_antisymm le_top (le_iInf fun S => le_iInf fun hS => ?_)
      exact absurd ⟨S, hS⟩ hcon
    rw [htop] at hle
    exact absurd (top_le_iff.mp hle) (ENat.coe_ne_top N)
  -- The set of admissible-net cardinalities.
  set A : Set ℕ := {k | ∃ S : Finset (Ω → ℝ),
      (↑S ⊆ F ∧ ∀ f ∈ F, ∃ g ∈ S, distL2 P f g < s) ∧ S.card = k} with hA
  have hA_ne : A.Nonempty := by
    obtain ⟨S, hSF, hSnet⟩ := hne
    exact ⟨S.card, S, ⟨hSF, hSnet⟩, rfl⟩
  obtain ⟨S₀, hS₀_adm, hS₀_card⟩ := Nat.sInf_mem hA_ne
  -- `l2CoveringNumber P F s = (Nat.sInf A : ℕ∞)`.
  have hval : ((sInf A : ℕ) : ℕ∞) = l2CoveringNumber P F s := by
    unfold l2CoveringNumber
    apply le_antisymm
    · -- `sInf A ≤` every admissible card.
      refine le_iInf fun S => le_iInf fun hS => ?_
      exact_mod_cast Nat.sInf_le (⟨S, hS, rfl⟩ : S.card ∈ A)
    · -- The `iInf` is `≤ |S₀| = sInf A`.
      calc (⨅ (S : Finset (Ω → ℝ)) (_ : ↑S ⊆ F ∧ ∀ f ∈ F, ∃ g ∈ S, distL2 P f g < s),
              (S.card : ℕ∞))
          ≤ (S₀.card : ℕ∞) := iInf_le_of_le S₀ (iInf_le _ hS₀_adm)
        _ = ((sInf A : ℕ) : ℕ∞) := by rw [hS₀_card]
  exact ⟨S₀, hS₀_adm.1, hS₀_adm.2, by rw [← hval, hS₀_card]⟩

/-- **Dyadic shift-reindex of the covering-chain series.**

The per-level covering-chain bound is naturally indexed by the *finer* (link) scale
`ε_{q+1} = (1/2)^{q+1}·δ` — the smaller of the two nets bridged at chain level `q` — so the
process telescope produces the **shifted** covering series
`∑_q ε_q·entropyWeight(N(ε_{q+1}))`. Because the dyadic scales satisfy `ε_q = 2·ε_{q+1}`, this
shifted series is at most **twice** the on-diagonal series used below:

    ∑_q ofReal(ε_q)·entropyWeight(N(ε_{q+1})) ≤ 2·∑_q ofReal(ε_q)·entropyWeight(N(ε_q)).

Pure `ℝ≥0∞`-series algebra: `ofReal(ε_q) = ofReal(2·ε_{q+1}) = 2·ofReal(ε_{q+1})`, so the LHS is
`2·∑_q term(q+1)` with `term q := ofReal(ε_q)·entropyWeight(N(ε_q))`; the tail sum
`∑_q term(q+1) ≤ ∑_q term(q)` drops the `q = 0` head (`ENNReal.tsum_comp_le_tsum_of_injective`
along `Nat.succ`). This is the covering analogue of the `ε_q = 2ε_{q+1}` index
shift in the bracketing chaining bound. -/
private lemma covering_shifted_dyadic_series_le
    {P : Measure Ω} {F : Set (Ω → ℝ)} {δ : ℝ} :
    ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
        * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^(q+1) * δ))
      ≤ 2 * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^q * δ)) := by
  -- Per-term: `ofReal(ε_q)·w(N(ε_{q+1})) = 2·(ofReal(ε_{q+1})·w(N(ε_{q+1})))`.
  have hstep : ∀ q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
        * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^(q+1) * δ))
      = 2 * (ENNReal.ofReal ((1/2 : ℝ)^(q+1) * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^(q+1) * δ))) := by
    intro q
    have hval : (1/2 : ℝ)^q * δ = 2 * ((1/2 : ℝ)^(q+1) * δ) := by ring
    rw [hval, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    ring
  -- Tail sum ≤ full sum (drop the `q = 0` head, all terms nonneg).
  have htail : (∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^(q+1) * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^(q+1) * δ)))
      ≤ ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^q * δ)) :=
    ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
      (fun q => ENNReal.ofReal ((1/2 : ℝ)^q * δ)
        * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^q * δ)))
  calc ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^(q+1) * δ))
      = ∑' q : ℕ, 2 * (ENNReal.ofReal ((1/2 : ℝ)^(q+1) * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^(q+1) * δ))) := tsum_congr hstep
    _ = 2 * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^(q+1) * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^(q+1) * δ)) := by
        rw [ENNReal.tsum_mul_left]
    _ ≤ 2 * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
          * entropyWeight (l2CoveringNumber P F ((1/2 : ℝ)^q * δ)) :=
        mul_le_mul_of_nonneg_left htail (zero_le (a := 2))

/-- The centered Lipschitz shell is pointwise dense.  This is the
measurability/admissibility input for the uniform-covering symmetrization
theorem. -/
private lemma centeredLipschitz_shell_empProcPointwiseDense
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (δ : ℝ) :
    EmpProcPointwiseDense
      {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
        g = fun ω => m θ ω - m θ₀ ω} P := by
  let Θ : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall θ₀ δ
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense (↥Θ)
  let D : Set (EuclideanSpace ℝ (Fin d)) := Subtype.val '' D₀
  let F' : Set (Ω → ℝ) :=
    (fun θ => fun ω => m θ ω - m θ₀ ω) '' D
  have hD_sub : D ⊆ Θ := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hD_count : D.Countable := hD₀c.image _
  have hΘ_clD : Θ ⊆ closure D := by
    intro θ hθ
    have hθ' : (⟨θ, hθ⟩ : ↥Θ) ∈ closure D₀ := hD₀d ⟨θ, hθ⟩
    have him := image_closure_subset_closure_image continuous_subtype_val
      (Set.mem_image_of_mem Subtype.val hθ')
    exact him
  refine ⟨F', ?_, hD_count.image _, ?_, ?_⟩
  · rintro _ ⟨θ, hθD, rfl⟩
    have hθΘ := hD_sub hθD
    exact ⟨θ, by simpa [Θ, Metric.mem_closedBall, dist_eq_norm] using hθΘ, rfl⟩
  · rintro f ⟨θ, hθ, rfl⟩
    have hθΘ : θ ∈ Θ := by
      simpa [Θ, Metric.mem_closedBall, dist_eq_norm] using hθ
    obtain ⟨θseq, hθseq_mem, hθseq_lim⟩ := mem_closure_iff_seq_limit.mp (hΘ_clD hθΘ)
    refine ⟨fun n => fun ω => m (θseq n) ω - m θ₀ ω,
      fun n => ⟨θseq n, hθseq_mem n, rfl⟩, fun x => ?_⟩
    have hnorm : Tendsto (fun n => ‖θseq n - θ‖) atTop (𝓝 0) := by
      have hsub : Tendsto (fun n => θseq n - θ) atTop (𝓝 0) := by
        simpa using hθseq_lim.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => θ) atTop (𝓝 θ))
      simpa using! (continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin d))).comp hsub
    have hzero : Tendsto (fun n => ‖menv x‖ * ‖θseq n - θ‖) atTop (𝓝 0) := by
      simpa using hnorm.const_mul ‖menv x‖
    apply tendsto_sub_nhds_zero_iff.mp
    refine squeeze_zero_norm (fun n => ?_) hzero
    calc
      ‖(m (θseq n) x - m θ₀ x) - (m θ x - m θ₀ x)‖
          = |m (θseq n) x - m θ x| := by rw [Real.norm_eq_abs]; congr 1; ring
      _ ≤ menv x * ‖θseq n - θ‖ := hLip (θseq n) θ x
      _ ≤ ‖menv x‖ * ‖θseq n - θ‖ :=
        mul_le_mul_of_nonneg_right (Real.le_norm_self _) (norm_nonneg _)
  · refine ⟨fun x => δ * |menv x|, ?_, ?_⟩
    · exact ((hmenv.integrable (by norm_num)).abs).const_mul δ
    · rintro _ ⟨θ, hθ, rfl⟩ x
      calc
        |m θ x - m θ₀ x| ≤ menv x * ‖θ - θ₀‖ := hLip θ θ₀ x
        _ ≤ |menv x| * ‖θ - θ₀‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ ≤ |menv x| * δ := mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
        _ = δ * |menv x| := by ring

omit [MeasurableSpace Ω] in
/-- Euclidean parameter nets give normalized finite-discrete `L²` covers of
the clamped shell, uniformly over the realized finite-discrete law. -/
private lemma uniformL2CoveringNumber_truncate_shell_le
    {d : ℕ}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ M : ℝ, ∀ ε : ℝ,
      0 < ε → ε ≤ 1 →
      ∃ N : ℕ,
        uniformL2CoveringNumber
            (truncateClass
              {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                g = fun ω => m θ ω - m θ₀ ω} M)
            (fun ω => δ * |menv ω|) ε ≤ (N : ℕ∞) ∧
          (N : ℝ) ≤ (C / ε) ^ d := by
  classical
  obtain ⟨C, hC, hcover⟩ :=
    coveringNumber_le_of_bounded_euclidean
      (Metric.closedBall θ₀ 1) Metric.isBounded_closedBall
  refine ⟨C, hC, fun δ hδ M ε hε hε1 => ?_⟩
  obtain ⟨S, _hSball, hballCover, hScard⟩ := hcover ε hε hε1
  let θmap : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun c => θ₀ + δ • (c - θ₀)
  let fmap : EuclideanSpace ℝ (Fin d) → Ω → ℝ :=
    fun c => clampFn M (fun ω => m (θmap c) ω - m θ₀ ω)
  let Simg : Finset (Ω → ℝ) := S.image fmap
  have hS_nonempty : S.Nonempty := by
    have hθ₀ball : θ₀ ∈ Metric.closedBall θ₀ 1 := by simp
    obtain ⟨c, hcS, -⟩ := Set.mem_iUnion₂.mp (hballCover hθ₀ball)
    exact ⟨c, hcS⟩
  have hSimg_nonempty : Simg.Nonempty := hS_nonempty.image fmap
  refine ⟨Simg.card, ?_, ?_⟩
  · unfold uniformL2CoveringNumber
    refine iSup_le fun Q => ?_
    have habsNorm : Q.l2Seminorm (fun x => |menv x|) = Q.l2Seminorm menv := by
      unfold FiniteDiscreteProbability.l2Seminorm
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      simp only [abs_abs]
    have hΦNorm : Q.l2Seminorm (fun x => δ * |menv x|) =
        δ * Q.l2Seminorm menv := by
      rw [FiniteDiscreteProbability.l2Seminorm_mul, abs_of_pos hδ, habsNorm]
    by_cases hΦzero : Q.l2Seminorm (fun x => δ * |menv x|) = 0
    · rw [normalizedL2CoveringNumber_of_l2Seminorm_eq_zero Q _ _ ε hΦzero]
      exact_mod_cast Finset.one_le_card.mpr hSimg_nonempty
    · simp only [normalizedL2CoveringNumber, if_neg hΦzero]
      refine iInf_le_of_le Simg (iInf_le_of_le ?_ le_rfl)
      rintro f ⟨g, ⟨θ, hθ, rfl⟩, rfl⟩
      let u : EuclideanSpace ℝ (Fin d) := θ₀ + δ⁻¹ • (θ - θ₀)
      have huNorm : ‖u - θ₀‖ ≤ 1 := by
        have huθ : u - θ₀ = δ⁻¹ • (θ - θ₀) := by
          simp only [u, add_sub_cancel_left]
        rw [huθ, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
        calc
          δ⁻¹ * ‖θ - θ₀‖ ≤ δ⁻¹ * δ :=
            mul_le_mul_of_nonneg_left hθ (inv_pos.mpr hδ).le
          _ = 1 := inv_mul_cancel₀ hδ.ne'
      have huBall : u ∈ Metric.closedBall θ₀ 1 := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        exact huNorm
      obtain ⟨c, hcS, huc⟩ := Set.mem_iUnion₂.mp (hballCover huBall)
      refine ⟨fmap c, Finset.mem_image_of_mem fmap hcS, ?_⟩
      have hucNorm : ‖u - c‖ < ε := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp huc
      have hθvec : θ - θmap c = δ • (u - c) := by
        simp only [θmap, u, smul_sub, smul_add, smul_smul,
          mul_inv_cancel₀ hδ.ne', one_smul]
        abel
      have hθNorm : ‖θ - θmap c‖ < δ * ε := by
        rw [hθvec, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
        exact mul_lt_mul_of_pos_left hucNorm hδ
      have hmPos : 0 < Q.l2Seminorm menv := by
        refine lt_of_le_of_ne (Q.l2Seminorm_nonneg menv) ?_
        intro hmZero
        apply hΦzero
        rw [hΦNorm, ← hmZero, mul_zero]
      have hdist : Q.distL2
          (clampFn M (fun ω => m θ ω - m θ₀ ω))
          (fmap c) ≤ ‖θ - θmap c‖ * Q.l2Seminorm menv := by
        unfold FiniteDiscreteProbability.distL2
        calc
          Q.l2Seminorm
                (clampFn M (fun ω => m θ ω - m θ₀ ω) - fmap c)
              ≤ Q.l2Seminorm (fun x => ‖θ - θmap c‖ * menv x) := by
                apply Q.l2Seminorm_mono_abs
                intro x
                simp only [Pi.sub_apply, fmap]
                calc
                  |clampReal M (m θ x - m θ₀ x) -
                      clampReal M (m (θmap c) x - m θ₀ x)|
                      ≤ |(m θ x - m θ₀ x) -
                          (m (θmap c) x - m θ₀ x)| :=
                        abs_clampReal_sub_clampReal_le _ _ _
                  _ = |m θ x - m (θmap c) x| := by congr 1; ring
                  _ ≤ menv x * ‖θ - θmap c‖ := hLip θ (θmap c) x
                  _ ≤ |menv x| * ‖θ - θmap c‖ :=
                    mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
                  _ = |‖θ - θmap c‖ * menv x| := by
                    rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
                    ring
          _ = ‖θ - θmap c‖ * Q.l2Seminorm menv := by
            rw [Q.l2Seminorm_mul, abs_of_nonneg (norm_nonneg _)]
      calc
        Q.distL2 (clampFn M (fun ω => m θ ω - m θ₀ ω)) (fmap c)
            ≤ ‖θ - θmap c‖ * Q.l2Seminorm menv := hdist
        _ < (δ * ε) * Q.l2Seminorm menv :=
          mul_lt_mul_of_pos_right hθNorm hmPos
        _ = ε * Q.l2Seminorm (fun x => δ * |menv x|) := by
          rw [hΦNorm]
          ring
  · calc
      (Simg.card : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_image_le
      _ ≤ (C / ε) ^ d := hScard

omit [MeasurableSpace Ω] in
/-- The unit-endpoint uniform finite-discrete entropy integral of every
clamped centered shell is bounded by a dimension-dependent constant. -/
private lemma uniformCoveringEntropyIntegral_truncate_shell_le
    {d : ℕ}
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (menv : Ω → ℝ)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ δ : ℝ, 0 < δ → ∀ M : ℝ,
      uniformCoveringEntropyIntegral 1
          (truncateClass
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω} M)
          (fun ω => δ * |menv ω|) ≤ ENNReal.ofReal Cd := by
  classical
  obtain ⟨C, hC, hcover⟩ :=
    uniformL2CoveringNumber_truncate_shell_le m θ₀ menv hLip
  obtain ⟨Cd, hCd, hInt⟩ := sqrt_log_pow_ratio_lintegral_le C hC d
  refine ⟨Cd, hCd, fun δ hδ M => ?_⟩
  let G : Set (Ω → ℝ) :=
    truncateClass
      {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
        g = fun ω => m θ ω - m θ₀ ω} M
  let Φ : Ω → ℝ := fun ω => δ * |menv ω|
  have hdom : ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      entropyWeight (uniformL2CoveringNumber G Φ ε) ≤
        ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * 1 / ε) ^ d))) := by
    intro ε hε
    obtain ⟨N, hN, hNcard⟩ := hcover δ hδ M ε hε.1 hε.2
    calc
      entropyWeight (uniformL2CoveringNumber G Φ ε)
          ≤ entropyWeight (N : ℕ∞) := entropyWeight_mono hN
      _ = ENNReal.ofReal (Real.sqrt (Real.log (1 + (N : ℝ)))) := entropyWeight_coe N
      _ ≤ ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * 1 / ε) ^ d))) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.sqrt_le_sqrt
        apply Real.log_le_log (by positivity)
        rw [show C * 1 / ε = C / ε by ring]
        linarith
  calc
    uniformCoveringEntropyIntegral 1 G Φ
        = ∫⁻ ε in Set.Ioc (0 : ℝ) 1,
            entropyWeight (uniformL2CoveringNumber G Φ ε) ∂volume := rfl
    _ ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (Real.log (1 + (C * 1 / ε) ^ d))) ∂volume :=
      setLIntegral_mono_ae' measurableSet_Ioc (Eventually.of_forall hdom)
    _ ≤ ENNReal.ofReal (Cd * 1) := hInt 1 one_pos
    _ = ENNReal.ofReal Cd := by rw [mul_one]

/-- **Uniform-covering bound with a population covering series.**

The stochastic estimate follows vdV's covering route: finite Euclidean parameter nets give
normalized covers uniformly over finite-discrete laws; after conditioning on the sample, the
Rademacher chain uses `L²(Pₙ)` projections, finite links, and a terminal residual that
vanishes in the sample metric.  Symmetrization and expected sample-`L²` envelope control then
give `C·δ`, uniformly in `n`.

The conclusion is expressed using a shifted population-`L²(P)` series. Population nets
do **not** control the sample residual. Here `hnets` establishes that the shell contains zero,
so its `q = 1` net is nonempty and the regularized `q = 0` series head is at least
`δ·entropyWeight(1)`. This positive head absorbs the book bound `C·δ`. -/
private theorem covering_process_chain_shifted_core
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hnets : ∀ δ : ℝ, 0 < δ → ∀ q : ℕ,
      ∃ S : Finset (Ω → ℝ),
        (↑S ⊆ {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω}) ∧
        (∀ f ∈ {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω}, ∃ g ∈ S, distL2 P f g < (1/2 : ℝ)^q * δ) ∧
        (S.card : ℕ∞) = l2CoveringNumber P
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^q * δ)) :
    ∃ K : ℝ, 0 < K ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ξ, supNormOver
          (truncateClass
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (Real.sqrt n * κ * δ))
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal K
            * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * entropyWeight (l2CoveringNumber P
                    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                      g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^(q+1) * δ)) := by
  classical
  obtain ⟨Cd, hCd, hEntropy⟩ :=
    uniformCoveringEntropyIntegral_truncate_shell_le m θ₀ menv hLip
  let M₂ : ℝ := (eLpNorm menv 2 P).toReal
  have hM₂ : 0 ≤ M₂ := ENNReal.toReal_nonneg
  let C₀ : ℝ := 52 * Cd * M₂ + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  let w : ℝ := Real.sqrt (Real.log 2)
  have hw : 0 < w := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨C₀ / w, div_pos hC₀ hw, 1, one_pos, fun δ hδ n hn => ?_⟩
  let Mδ : Set (Ω → ℝ) :=
    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
      g = fun ω => m θ ω - m θ₀ ω}
  let Mc : ℝ := Real.sqrt n * 1 * δ
  let G : Set (Ω → ℝ) := truncateClass Mδ Mc
  let Φ : Ω → ℝ := fun ω => δ * |menv ω|
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hMc_pos : 0 < Mc := by dsimp [Mc]; positivity
  have hMc : 0 ≤ Mc := hMc_pos.le
  have hDenseMδ : EmpProcPointwiseDense Mδ P := by
    simpa only [Mδ] using
      centeredLipschitz_shell_empProcPointwiseDense P m θ₀ menv hmenv hLip δ
  have hDenseG : EmpProcPointwiseDense G P :=
    EmpProcPointwiseDense_truncateClass hMc hDenseMδ
  have hG_meas : ∀ g ∈ G, Measurable g := by
    rintro g ⟨f, ⟨θ, _, rfl⟩, rfl⟩
    exact clampFn_measurable ((hm_meas θ).sub (hm_meas θ₀))
  have hΦ_meas : Measurable Φ := by
    exact (hmenv_meas.abs).const_mul δ
  have hΦ_env : IsEnvelope G Φ := by
    rintro g ⟨f, ⟨θ, hθ, rfl⟩, rfl⟩ x
    calc
      |clampFn Mc (fun ω => m θ ω - m θ₀ ω) x|
          ≤ |m θ x - m θ₀ x| := abs_clampReal_le Mc hMc _
      _ ≤ menv x * ‖θ - θ₀‖ := hLip θ θ₀ x
      _ ≤ |menv x| * ‖θ - θ₀‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |menv x| * δ := mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
      _ = Φ x := by dsimp [Φ]; ring
  have hΦ_norm : eLpNorm Φ 2 P = ENNReal.ofReal δ * eLpNorm menv 2 P := by
    have habs : eLpNorm (fun x => |menv x|) 2 P = eLpNorm menv 2 P := by
      simpa [Real.norm_eq_abs] using (eLpNorm_norm (μ := P) (p := (2 : ℝ≥0∞)) menv)
    have hfun : Φ = δ • (fun x => |menv x|) := by
      funext x
      simp only [Φ, Pi.smul_apply, smul_eq_mul]
    rw [hfun, eLpNorm_const_smul, habs, Real.enorm_eq_ofReal_abs, abs_of_pos hδ]
  have hSup_meas : Measurable (fun ξ : Ξ =>
      supNormOver G
        (empiricalProcess P n (fun i : Fin n => X i.val ξ))) :=
    measurable_empiricalProcessSup_dense P G hDenseG X hX_meas hG_meas n
  have hOuter := outer_empiricalProcessSup_le_uniformCoveringEntropyIntegral
    P μ X hX_meas hX_indep hX_id hX_law G hDenseG hG_meas Φ hΦ_env hΦ_meas n
  have hmenv_eq : eLpNorm menv 2 P = ENNReal.ofReal M₂ :=
    (ENNReal.ofReal_toReal hmenv.eLpNorm_ne_top).symm
  have hcoeff : 52 * ENNReal.ofReal Cd * eLpNorm menv 2 P ≤ ENNReal.ofReal C₀ := by
    rw [hmenv_eq, show (52 : ℝ≥0∞) = ENNReal.ofReal 52 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 52),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hCd.le)]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C₀]
    linarith
  have hlinear : (∫⁻ ξ, supNormOver G
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ)
      ≤ ENNReal.ofReal (C₀ * δ) := by
    calc
      (∫⁻ ξ, supNormOver G
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ)
          = MeasureTheory.outerExpectation μ (fun ξ => supNormOver G
              (empiricalProcess P n (fun i : Fin n => X i.val ξ))) :=
            (MeasureTheory.outerExpectation_eq_lintegral hSup_meas).symm
      _ ≤ 52 * uniformCoveringEntropyIntegral 1 G Φ * eLpNorm Φ 2 P := hOuter
      _ ≤ 52 * ENNReal.ofReal Cd * eLpNorm Φ 2 P := by
        gcongr
        simpa only [G, Φ, Mδ] using hEntropy δ hδ Mc
      _ = ENNReal.ofReal δ *
            (52 * ENNReal.ofReal Cd * eLpNorm menv 2 P) := by
        rw [hΦ_norm]
        ring
      _ ≤ ENNReal.ofReal δ * ENNReal.ofReal C₀ :=
        by simpa [mul_comm] using mul_le_mul_right hcoeff (ENNReal.ofReal δ)
      _ = ENNReal.ofReal (C₀ * δ) := by
        rw [← ENNReal.ofReal_mul hδ.le]
        congr 1
        ring
  obtain ⟨S, _hSsub, hSnet, hScard⟩ := hnets δ hδ 1
  have hzero : (fun _ : Ω => 0) ∈ Mδ := by
    refine ⟨θ₀, by simpa using hδ.le, ?_⟩
    funext x
    ring
  obtain ⟨g, hgS, -⟩ := hSnet (fun _ : Ω => 0) hzero
  have hcard : (1 : ℕ∞) ≤ l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ 1 * δ) := by
    rw [← hScard]
    exact_mod_cast Finset.one_le_card.mpr ⟨g, hgS⟩
  have hweight : ENNReal.ofReal w ≤
      entropyWeight (l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ 1 * δ)) := by
    calc
      ENNReal.ofReal w = entropyWeight (1 : ℕ∞) := by
        change ENNReal.ofReal w = entropyWeight ((1 : ℕ) : ℕ∞)
        rw [entropyWeight_coe]
        dsimp [w]
        norm_num
      _ ≤ entropyWeight (l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ 1 * δ)) :=
        entropyWeight_mono hcard
  have hhead : ENNReal.ofReal δ *
        entropyWeight (l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ 1 * δ)) ≤
      ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
        entropyWeight (l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ (q + 1) * δ)) := by
    simpa using (ENNReal.le_tsum 0 (f := fun q : ℕ =>
      ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
        entropyWeight (l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ (q + 1) * δ))))
  have hseries : ENNReal.ofReal δ * ENNReal.ofReal w ≤
      ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
        entropyWeight (l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ (q + 1) * δ)) := by
    have hweight_mul : ENNReal.ofReal δ * ENNReal.ofReal w ≤
        ENNReal.ofReal δ *
          entropyWeight (l2CoveringNumber P Mδ ((1 / 2 : ℝ) ^ 1 * δ)) := by
      simpa [mul_comm] using mul_le_mul_right hweight (ENNReal.ofReal δ)
    exact hweight_mul.trans hhead
  calc
    (∫⁻ ξ, supNormOver G
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ)
        ≤ ENNReal.ofReal (C₀ * δ) := hlinear
    _ = ENNReal.ofReal (C₀ / w) *
          (ENNReal.ofReal δ * ENNReal.ofReal w) := by
      rw [← ENNReal.ofReal_mul hδ.le,
        ← ENNReal.ofReal_mul (div_nonneg hC₀.le hw.le)]
      congr 1
      field_simp [hw.ne']
    _ ≤ ENNReal.ofReal (C₀ / w) *
          ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
            entropyWeight (l2CoveringNumber P Mδ
              ((1 / 2 : ℝ) ^ (q + 1) * δ)) := by
      simpa [mul_comm] using
        mul_le_mul_right hseries (ENNReal.ofReal (C₀ / w))

/-- Reindex the shifted population-covering series onto its diagonal form.
The stochastic estimate is supplied by the uniform finite-discrete/sample-`L²`
bound; this lemma is `ℝ≥0∞` series algebra. -/
private theorem covering_chain_tree_core
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hnets : ∀ δ : ℝ, 0 < δ → ∀ q : ℕ,
      ∃ S : Finset (Ω → ℝ),
        (↑S ⊆ {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω}) ∧
        (∀ f ∈ {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω}, ∃ g ∈ S, distL2 P f g < (1/2 : ℝ)^q * δ) ∧
        (S.card : ℕ∞) = l2CoveringNumber P
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^q * δ)) :
    ∃ K : ℝ, 0 < K ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ξ, supNormOver
          (truncateClass
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (Real.sqrt n * κ * δ))
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal K
            * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * entropyWeight (l2CoveringNumber P
                    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                      g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^q * δ)) := by
  obtain ⟨K, hK, κ, hκ, hcore⟩ :=
    covering_process_chain_shifted_core P m θ₀ hm_meas menv hmenv hmenv_meas hLip
      μ X hX_meas hX_indep hX_id hX_law hnets
  refine ⟨2 * K, by positivity, κ, hκ, fun δ hδ n hn => ?_⟩
  calc ∫⁻ ξ, supNormOver
          (truncateClass
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (Real.sqrt n * κ * δ))
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ ENNReal.ofReal K
          * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyWeight (l2CoveringNumber P
                  {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                    g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^(q+1) * δ)) :=
        hcore δ hδ n hn
    _ ≤ ENNReal.ofReal K
          * (2 * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyWeight (l2CoveringNumber P
                  {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                    g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^q * δ))) := by
        gcongr
        exact covering_shifted_dyadic_series_le
    _ = ENNReal.ofReal (2 * K)
          * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
              * entropyWeight (l2CoveringNumber P
                  {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                    g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^q * δ)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring

/-- Populate the population-net assumptions from the finite shell covers, then convert the
shifted series to the diagonal dyadic series. The population
nets are used for non-vacuity of the regularized series, not for the sample residual. -/
private theorem covering_clamped_chain_bound_dyadic
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ K : ℝ, 0 < K ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ξ, supNormOver
          (truncateClass
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (Real.sqrt n * κ * δ))
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal K
            * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
                * entropyWeight (l2CoveringNumber P
                    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                      g = fun ω => m θ ω - m θ₀ ω} ((1/2 : ℝ)^q * δ)) := by
  -- Realize each finite population covering number by an attaining net.
  obtain ⟨_C, _hC_pos, hshell⟩ := l2CoveringNumber_shell_le m θ₀ menv hmenv hLip
  refine covering_chain_tree_core P m θ₀ hm_meas menv hmenv hmenv_meas hLip μ X
    hX_meas hX_indep hX_id hX_law ?_
  intro δ hδ q
  have hε_pos : (0 : ℝ) < (1/2 : ℝ) ^ q * δ := by positivity
  have hε_le : (1/2 : ℝ) ^ q * δ ≤ δ := by
    calc (1/2 : ℝ) ^ q * δ ≤ 1 * δ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) hδ.le
      _ = δ := one_mul δ
  obtain ⟨N, hNle, _⟩ := hshell δ hδ ((1/2 : ℝ) ^ q * δ) hε_pos hε_le
  exact l2CoveringNumber_exists_min_net hNle

/-- **Covering Dudley bound over the CLAMPED shell class, vdV Thm 2.14.1 / Cor 19.35.**

This converts the diagonal population-series bound from
`covering_clamped_chain_bound_dyadic` into the population covering entropy integral via
`covering_dyadic_sum_le_l2CoveringEntropyIntegral`. The stochastic estimate used by the first bound
is the uniform finite-discrete/sample-`L²` chain, including its terminal residual.

For the fixed-center CLOSED shell `M̄_δ = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ ≤ δ}`, the empirical
modulus over its **envelope-clamped** truncation `truncateClass M̄_δ (√n·κ·δ)` (clamped at the
`δ`-proportional level `√n·κ·δ`, the same level whose *excess* is the envelope tail handled by
`supNorm_clamp_lift`) is bounded by the **scale-free covering entropy integral**, with a `δ`- and
`n`-free constant `c₁` and a `δ`- and `n`-free truncation scale `κ`:

    ∫⁻ ‖𝔾ₙ‖_{truncate M̄_δ (√n·κ·δ)} ≤ c₁ · l2CoveringEntropyIntegral δ M̄_δ P.

The preceding bound
`covering_clamped_chain_bound_dyadic` bounds the clamped modulus by
`ofReal K · Σ_q (1/2)^q·δ · √log(1 + N((1/2)^q·δ, M̄_δ))`; the telescope comparison
`covering_dyadic_sum_le_l2CoveringEntropyIntegral` bounds that dyadic series by
`2 · l2CoveringEntropyIntegral δ M̄_δ P`. With `c₁ = 2K` the two fold into the conclusion.
The `√log(1/δ)` cancels because the covering scale is *relative* to the shell radius `δ`.
The `supNorm_clamp_lift` inequality then adds the envelope tail at `√n·κ·δ`. -/
private theorem covering_clamped_chain_bound
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ξ, supNormOver
          (truncateClass
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (Real.sqrt n * κ * δ))
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal c₁
            * l2CoveringEntropyIntegral δ
                {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                  g = fun ω => m θ ω - m θ₀ ω} P := by
  obtain ⟨K, hK, κ, hκ, hcore⟩ := covering_clamped_chain_bound_dyadic P m θ₀ hm_meas
    menv hmenv hmenv_meas hLip μ X hX_meas hX_indep hX_id hX_law
  refine ⟨2 * K, by positivity, κ, hκ, fun δ hδ n hn => ?_⟩
  set Mδ : Set (Ω → ℝ) :=
    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
      g = fun ω => m θ ω - m θ₀ ω} with hMδdef
  calc ∫⁻ ξ, supNormOver (truncateClass Mδ (Real.sqrt n * κ * δ))
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ ENNReal.ofReal K * ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ)
            * entropyWeight (l2CoveringNumber P Mδ ((1/2 : ℝ)^q * δ)) := hcore δ hδ n hn
    _ ≤ ENNReal.ofReal K * (2 * l2CoveringEntropyIntegral δ Mδ P) := by
        gcongr
        exact covering_dyadic_sum_le_l2CoveringEntropyIntegral (P := P) (F := Mδ) hδ
    _ = ENNReal.ofReal (2 * K) * l2CoveringEntropyIntegral δ Mδ P := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        ring

/-- **Covering Dudley-chaining bound, vdV Thm 2.14.1 / Cor 19.35.**
This combines the clamp-lift split `supNorm_clamp_lift` and the clamped uniform-covering bound
`covering_clamped_chain_bound`.

For the fixed-center CLOSED shell `M̄_δ = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ ≤ δ}` (envelope
`δ·menv`) the empirical-process modulus splits, for `n ≥ 1`, into a **covering-entropy chain term**
(constant `c` times the scale-free covering entropy integral `l2CoveringEntropyIntegral δ M̄_δ P`)
plus an **envelope-tail term** at the `δ`-proportional truncation threshold `√n·κ` (a `δ`-free
level set `{√n·κ < |menv|}`, since the envelope `δ·menv` already carries the `δ`):

    ∫⁻ ‖𝔾ₙ‖_{M̄_δ} ≤ c·(covering entropy integral) + c·√n·∫⁻ δ|menv| 1_{√n·κ < |menv|}.

Take the truncation level `Mc = √n·κ·δ` (with `κ` from
`covering_clamped_chain_bound`) and the envelope `Φ = δ·|menv|`. Then:

* `supNorm_clamp_lift` splits `∫⁻ ‖𝔾ₙ‖_{M̄_δ}` into `∫⁻ ‖𝔾ₙ‖_{truncate M̄_δ Mc}` plus the tail
  `4√n·∫⁻ |Φ|·1{Mc<|Φ|}`;
* `covering_clamped_chain_bound` bounds the clamped modulus by
  `c₁·l2CoveringEntropyIntegral δ M̄_δ P`;
* the tail rewrites to `4√n·∫⁻ δ|menv|·1{√n·κ<|menv|}` since `|Φ| = δ|menv|` and, dividing by `δ>0`,
  `{Mc<|Φ|} = {√n·κ·δ < δ|menv|} = {√n·κ < |menv|}`.

With `c = c₁ + 4` both terms give the conclusion. -/
private theorem covering_chaining_shell_core
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ c : ℝ, 0 < c ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, 1 ≤ n →
      ∫⁻ ξ, supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal c
            * l2CoveringEntropyIntegral δ
                {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                  g = fun ω => m θ ω - m θ₀ ω} P
          + ENNReal.ofReal c
              * (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (δ * |menv ω|)
                      * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω ∂P) := by
  classical
  obtain ⟨c₁, hc₁, κ, hκ, hchain⟩ := covering_clamped_chain_bound P m θ₀ hm_meas menv
    hmenv hmenv_meas hLip μ X hX_meas hX_indep hX_id hX_law
  refine ⟨c₁ + 4, by linarith, κ, hκ, fun δ hδ n hn => ?_⟩
  set Mδ : Set (Ω → ℝ) :=
    {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
      g = fun ω => m θ ω - m θ₀ ω} with hMδdef
  set Φ : Ω → ℝ := fun ω => δ * |menv ω| with hΦdef
  set Mc : ℝ := Real.sqrt n * κ * δ with hMc_def
  have hsn_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hMc_nn : 0 ≤ Mc := by rw [hMc_def]; positivity
  have hΦ_meas : Measurable Φ := by rw [hΦdef]; exact (hmenv_meas.abs).const_mul δ
  have hΦ_env : IsEnvelope Mδ Φ := by
    rintro g ⟨θ, hθ, rfl⟩ ω
    rw [hΦdef]
    calc |m θ ω - m θ₀ ω| ≤ menv ω * ‖θ - θ₀‖ := hLip θ θ₀ ω
      _ ≤ |menv ω| * ‖θ - θ₀‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |menv ω| * δ := mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
      _ = δ * |menv ω| := by ring
  have hG_meas : ∀ h ∈ Mδ, Measurable h := by
    rintro h ⟨θ, hθ, rfl⟩; exact (hm_meas θ).sub (hm_meas θ₀)
  have hΦ_int : Integrable Φ P := by
    rw [hΦdef]; exact ((hmenv.integrable (by norm_num)).abs).const_mul δ
  have hlift := supNorm_clamp_lift P hX_meas hX_id hX_law Mδ Φ hΦ_meas hΦ_env hG_meas
    hΦ_int Mc hMc_nn n hn
  have hchain' : ∫⁻ ξ, supNormOver (truncateClass Mδ Mc)
        (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ ENNReal.ofReal c₁ * l2CoveringEntropyIntegral δ Mδ P := by
    rw [hMδdef, hMc_def]; exact hchain δ hδ n hn
  have hset : ∀ y, (Mc < |Φ y|) ↔ (Real.sqrt n * κ < |menv y|) := by
    intro y
    have hΦval : |Φ y| = |menv y| * δ := by
      rw [hΦdef]; simp only [abs_mul, abs_abs, abs_of_pos hδ]; ring
    rw [hMc_def, hΦval]
    constructor
    · intro h; exact lt_of_mul_lt_mul_right h hδ.le
    · intro h; exact mul_lt_mul_of_pos_right h hδ
  have htail_eq : ∫⁻ x, ENNReal.ofReal (|Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x) ∂P
      = ∫⁻ ω, ENNReal.ofReal (δ * |menv ω|)
          * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω ∂P := by
    refine lintegral_congr (fun x => ?_)
    have hΦabs : |Φ x| = δ * |menv x| := by
      rw [hΦdef]; simp only [abs_mul, abs_abs, abs_of_pos hδ]
    by_cases hx : Mc < |Φ x|
    · have hx' : Real.sqrt n * κ < |menv x| := (hset x).mp hx
      rw [Set.indicator_of_mem (show x ∈ {y | Mc < |Φ y|} from hx),
        Set.indicator_of_mem (show x ∈ {y | Real.sqrt n * κ < |menv y|} from hx'),
        Pi.one_apply, Pi.one_apply, mul_one, mul_one, hΦabs]
    · have hx' : ¬ Real.sqrt n * κ < |menv x| := fun h => hx ((hset x).mpr h)
      rw [Set.indicator_of_notMem (show x ∉ {y | Mc < |Φ y|} from hx),
        Set.indicator_of_notMem (show x ∉ {y | Real.sqrt n * κ < |menv y|} from hx'),
        mul_zero, ENNReal.ofReal_zero, mul_zero]
  calc ∫⁻ ξ, supNormOver Mδ
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
      ≤ (∫⁻ ξ, supNormOver (truncateClass Mδ Mc)
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ)
          + 4 * ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ x, ENNReal.ofReal (|Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x) ∂P := hlift
    _ ≤ ENNReal.ofReal c₁ * l2CoveringEntropyIntegral δ Mδ P
          + 4 * ENNReal.ofReal (Real.sqrt n)
              * ∫⁻ x, ENNReal.ofReal (|Φ x| * Set.indicator {y | Mc < |Φ y|} 1 x) ∂P :=
        add_le_add hchain' le_rfl
    _ = ENNReal.ofReal c₁ * l2CoveringEntropyIntegral δ Mδ P
          + 4 * ENNReal.ofReal (Real.sqrt n)
              * (∫⁻ ω, ENNReal.ofReal (δ * |menv ω|)
                  * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω ∂P) := by
        rw [htail_eq]
    _ ≤ ENNReal.ofReal (c₁ + 4) * l2CoveringEntropyIntegral δ Mδ P
          + ENNReal.ofReal (c₁ + 4)
              * (ENNReal.ofReal (Real.sqrt n)
                  * ∫⁻ ω, ENNReal.ofReal (δ * |menv ω|)
                      * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω ∂P) := by
        refine add_le_add ?_ ?_
        · gcongr
          linarith
        · rw [mul_assoc]
          gcongr
          rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp]
          exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Covering (uniform-entropy) localized maximal inequality over the closed shell**
(vdV Thm 2.14.1 / Cor 19.35).

The empirical-process modulus over the **fixed-center CLOSED shell**
`M̄_δ = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ ≤ δ}` grows linearly in `δ`, uniformly in `n`:

    ∫⁻ ξ, ‖𝔾ₙ‖_{M̄_δ} ∂μ ≤ C · δ   for all `δ > 0`, all `n`.

The clamped part follows the book's covering route: normalized covers uniformly over finite
discrete laws, conditional sample-`L²` Rademacher chaining (including the finest residual), and
symmetrization with expected sample-`L²` envelope control. Population `L²(P)` covering numbers
only package the population-entropy right-hand side; they are not used to control the sample
residual.
The result combines `covering_chaining_shell_core` with the scale-free covering entropy bound
`l2CoveringEntropyIntegral_shell_le` (`≤ C_d·δ`) and the Chebyshev envelope-tail bound
`shellEnvelope_tail_le` (`≤ C·δ`); the `n = 0` case is the trivial `𝔾₀ = 0`.
The theorem `centeredLipschitz_localizedModulus_bound` restricts this to the open shell via
`supNormOver_mono`). -/
theorem centeredLipschitz_shellModulus_bound_closed
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ n : ℕ,
      ∫⁻ ξ, supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal (C * δ) := by
  classical
  obtain ⟨Cd, hCd_pos, hentropy⟩ := l2CoveringEntropyIntegral_shell_le m θ₀ menv hmenv hLip
  obtain ⟨c, hc_pos, κ, hκ_pos, hcore⟩ := covering_chaining_shell_core P m θ₀ hm_meas
    menv hmenv hmenv_meas hLip μ X hX_meas hX_indep hX_id hX_law
  obtain ⟨CB, hCB_pos, htail⟩ := shellEnvelope_tail_le menv hmenv hκ_pos
  refine ⟨c * Cd + c * CB, add_pos (mul_pos hc_pos hCd_pos) (mul_pos hc_pos hCB_pos),
    fun δ hδ n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · -- `n = 0`: the empirical process is identically `0`, so the modulus vanishes.
    subst hn0
    have hz : (∫⁻ ξ, supNormOver
          {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
            g = fun ω => m θ ω - m θ₀ ω}
          (fun f => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) f) ∂μ) = 0 := by
      have hpt : (fun ξ => supNormOver
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (fun f => empiricalProcess P 0 (fun i : Fin 0 => X i.val ξ) f))
          = fun _ => (0 : ℝ≥0∞) := by
        funext ξ
        refine le_antisymm ?_ (zero_le)
        unfold supNormOver
        exact iSup₂_le fun f _ => by simp
      rw [hpt, lintegral_zero]
    rw [hz]; exact zero_le
  · -- `n ≥ 1`: chaining core + scale-free entropy bound + Chebyshev envelope tail.
    calc ∫⁻ ξ, supNormOver
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
        ≤ ENNReal.ofReal c
              * l2CoveringEntropyIntegral δ
                  {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ ≤ δ ∧
                    g = fun ω => m θ ω - m θ₀ ω} P
            + ENNReal.ofReal c
                * (ENNReal.ofReal (Real.sqrt n)
                    * ∫⁻ ω, ENNReal.ofReal (δ * |menv ω|)
                        * Set.indicator {x | Real.sqrt n * κ < |menv x|} 1 ω ∂P) :=
          hcore δ hδ n hn1
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal (Cd * δ)
            + ENNReal.ofReal c * ENNReal.ofReal (CB * δ) := by
          gcongr
          · exact hentropy δ hδ
          · exact htail δ hδ n
      _ = ENNReal.ofReal ((c * Cd + c * CB) * δ) := by
          rw [← ENNReal.ofReal_mul hc_pos.le, ← ENNReal.ofReal_mul hc_pos.le,
              ← ENNReal.ofReal_add
                (mul_nonneg hc_pos.le (mul_nonneg hCd_pos.le hδ.le))
                (mul_nonneg hc_pos.le (mul_nonneg hCB_pos.le hδ.le))]
          congr 1; ring

/-- **Uniform-entropy localized modulus bound (vdV Theorem 2.14.1 / Corollary 19.35).**

For `m` finite-dimensional (`θ ∈ ℝ^d`) with common `L²(P)` Lipschitz envelope `menv`, the expected
empirical modulus over the **open shell** `M_δ = {ω ↦ m_θ ω − m_{θ₀} ω : ‖θ − θ₀‖ < δ}` grows
linearly in the shell radius, uniformly in `n`:

    ∃ C > 0, ∃ ρ > 0, ∀ 0 < δ < ρ, ∀ n,   ∫⁻ ξ, ‖𝔾ₙ‖_{M_δ} ∂μ ≤ C · δ.

This is the conclusion used by `modulus_maximal_bound` in `MEstimator/Rate.lean`.
The bound is over the fixed-center shell `M_δ`, not
the pairwise-difference slice `localizedDifferenceClass` — the latter form is FALSE for nonlinear
Lipschitz `m` (vdV Lemma 19.38 note, book p.289; its envelope is `2·menv`, no `δ` in the covering
numerator, and the `√log(1/δ)` does not cancel). See `l2CoveringNumber_shell_le` for the
corresponding covering bound.

Proof: the covering-chaining core `centeredLipschitz_shellModulus_bound_closed` delivers the clean
`C·δ` bound over the *closed* shell `M̄_δ`; the open shell `M_δ ⊆ M̄_δ`, so `supNormOver_mono` +
`lintegral_mono` transports the bound. `ρ = 1` (any positive value works — the covering bound is
uniform in `δ > 0`; the `∃ ρ` binder is carried only to match `modulus_maximal_bound`). -/
theorem centeredLipschitz_localizedModulus_bound
    {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    -- LEAN-ONLY: explicit measurability of the criterion and envelope.
    (hm_meas : ∀ θ, Measurable (m θ))
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    -- USER-INPUT: an `L²(P)` envelope controls the criterion's Lipschitz modulus;
    -- vdV Corollary 19.35.
    (hLip : ∀ θ₁ θ₂ ω, |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- LEAN-ONLY: measurability of each sample coordinate.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: iid observations with common law `P`.
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧
      ∀ δ : ℝ, 0 < δ → δ < ρ → ∀ n : ℕ,
        ∫⁻ ξ, supNormOver
            {g : Ω → ℝ | ∃ θ : EuclideanSpace ℝ (Fin d), ‖θ - θ₀‖ < δ ∧
              g = fun ω => m θ ω - m θ₀ ω}
            (fun f => empiricalProcess P n (fun i : Fin n => X i.val ξ) f) ∂μ
          ≤ ENNReal.ofReal (C * δ) := by
  obtain ⟨C, hC_pos, hbound⟩ :=
    centeredLipschitz_shellModulus_bound_closed P m θ₀ hm_meas menv hmenv hmenv_meas hLip
      μ X hX_meas hX_indep hX_id hX_law
  refine ⟨C, hC_pos, 1, one_pos, fun δ hδ _ n => ?_⟩
  refine le_trans (lintegral_mono fun ξ => ?_) (hbound δ hδ n)
  refine supNormOver_mono ?_ _
  -- Open shell `M_δ ⊆ M̄_δ` (closed shell).
  rintro g ⟨θ, hθ, rfl⟩
  exact ⟨θ, hθ.le, rfl⟩

end AsymptoticStatistics.EmpiricalProcess
