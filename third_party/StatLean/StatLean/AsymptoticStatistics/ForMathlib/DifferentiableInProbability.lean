module
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import StatLean.AsymptoticStatistics.ForMathlib.TendstoInMeasureAlgebra

@[expose] public section

/-!
# Differentiability in probability

This file packages the probability-level differentiability used for
likelihood criteria in van der Vaart, *Asymptotic Statistics*, Theorem 5.39.
The reusable consequences below record the necessary domination condition:
convergence in probability alone does not imply `L²` convergence (moving-spike
examples show why a common `L²` envelope is necessary).
-/

namespace MeasureTheory

open Filter
open scoped ENNReal Topology

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace Ω]

/-- Differentiability at `θ₀` in `P`-probability, with samplewise continuous-linear
derivative `D`.

This is the book's normalized-remainder formulation: away from `θ₀`, divide
`m θ - m θ₀ - D (θ - θ₀)` by `‖θ - θ₀‖` and require convergence to zero in
measure as `θ → θ₀`.  Edge behavior: the punctured filter `𝓝[≠] θ₀` deliberately
excludes `θ = θ₀`, so no inverse-of-zero convention enters the definition.  If
`θ₀` is isolated, the punctured filter is degenerate and the condition carries
no nonzero-direction information. -/
def DifferentiableInProbabilityAt (P : Measure Ω) (m : E → Ω → ℝ)
    (D : Ω → E →L[ℝ] ℝ) (θ₀ : E) : Prop :=
  TendstoInMeasure P
    (fun θ ω => ‖θ - θ₀‖⁻¹ * (m θ ω - m θ₀ ω - D ω (θ - θ₀)))
    (𝓝[≠] θ₀) (fun _ => 0)

namespace DifferentiableInProbabilityAt

/-- A probability derivative has an `L²(P)` value in every fixed direction
when the local difference quotients share one pointwise `L²` envelope.

The envelope is the formal counterpart of vdV Theorem 5.39's local
log-Lipschitz function `dot m`.  `AEStronglyMeasurable` is the weakest
measurability input needed for `MemLp`; measurability of `D ω h` is derived
from convergence in measure rather than supplied as a derivative provider.
The zero direction is included. -/
theorem deriv_apply_memLp_two {P : Measure Ω} {m : E → Ω → ℝ}
    {D : Ω → E →L[ℝ] ℝ} {θ₀ : E}
    -- The defining probability-differentiability premise.
    (hdiff : DifferentiableInProbabilityAt P m D θ₀)
    -- Minimal measure-relative measurability of the criterion sections.
    (hm_meas : ∀ θ, AEStronglyMeasurable (m θ) P)
    -- vdV 5.39's common local log-Lipschitz envelope in `L²(P)`.
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    -- A nontrivial local neighborhood on which the envelope applies.
    (ρ : ℝ) (hρ : 0 < ρ)
    -- Pointwise local domination; moving spikes show that it is necessary.
    (henv : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
      |m θ ω - m θ₀ ω| ≤ ‖menv ω‖ * ‖θ - θ₀‖)
    (h : E) : MemLp (fun ω => D ω h) 2 P := by
  by_cases hh : h = 0
  · subst h
    simpa only [map_zero] using (MemLp.zero' : MemLp (fun _ : Ω => (0 : ℝ)) 2 P)
  let t : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  let θ : ℕ → E := fun n => θ₀ + t n • h
  let q : ℕ → Ω → ℝ := fun n ω =>
    (t n)⁻¹ * (m (θ n) ω - m θ₀ ω)
  have ht_pos (n : ℕ) : 0 < t n := by
    simp only [t, inv_pos, Nat.cast_add, Nat.cast_one]
    positivity
  have ht_ne (n : ℕ) : t n ≠ 0 := (ht_pos n).ne'
  have ht : Tendsto t atTop (nhds 0) := by
    simpa [t] using
      ((tendsto_add_atTop_iff_nat (f := fun n : ℕ => (((n : ℝ))⁻¹)) 1).2
        tendsto_inv_atTop_nhds_zero_nat)
  have hθ_nhds : Tendsto θ atTop (nhds θ₀) := by
    have hc : Tendsto (fun _ : ℕ => θ₀) atTop (nhds θ₀) := tendsto_const_nhds
    simpa [θ] using hc.add (ht.smul_const h)
  have hθ_ne (n : ℕ) : θ n ≠ θ₀ := by
    simp only [θ, ne_eq, add_eq_left]
    exact smul_ne_zero (ht_ne n) hh
  have hθ : Tendsto θ atTop (nhdsWithin θ₀ {θ₀}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hθ_nhds, Eventually.of_forall fun n => hθ_ne n⟩
  have hres := hdiff.comp hθ
  have hscaled : TendstoInMeasure P
      (fun n ω => ‖h‖ *
        (‖θ n - θ₀‖⁻¹ * (m (θ n) ω - m θ₀ ω - D ω (θ n - θ₀))))
      atTop (fun _ => 0) := hres.const_mul_zero ‖h‖
  have hsub : TendstoInMeasure P
      (fun n ω => q n ω - D ω h) atTop (fun _ => 0) := by
    refine hscaled.congr_left fun n => Eventually.of_forall fun ω => ?_
    simp only [q, θ, add_sub_cancel_left, map_smul, smul_eq_mul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ht_pos n)]
    field_simp [ht_ne n]
  have hq : TendstoInMeasure P q atTop (fun ω => D ω h) := by
    rw [tendstoInMeasure_iff_norm] at hsub ⊢
    simpa using hsub
  have hq_meas (n : ℕ) : AEStronglyMeasurable (q n) P := by
    exact ((hm_meas (θ n)).sub (hm_meas θ₀)).const_mul (t n)⁻¹
  have hq_bound : ∀ᶠ n in atTop,
      eLpNorm (q n) 2 P ≤ eLpNorm (fun ω => ‖h‖ * menv ω) 2 P := by
    filter_upwards [hθ_nhds.eventually (Metric.closedBall_mem_nhds θ₀ hρ)] with n hn
    apply eLpNorm_mono_ae
    filter_upwards with ω
    have hdom := henv (θ n) hn ω
    rw [Real.norm_eq_abs] at hdom
    simp only [q, Real.norm_eq_abs, abs_mul]
    rw [abs_of_pos (inv_pos.mpr (ht_pos n))]
    calc
      (t n)⁻¹ * |m (θ n) ω - m θ₀ ω|
          ≤ (t n)⁻¹ * (‖menv ω‖ * ‖θ n - θ₀‖) :=
            mul_le_mul_of_nonneg_left hdom (inv_nonneg.mpr (ht_pos n).le)
      _ = ‖h‖ * |menv ω| := by
        simp only [θ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (ht_pos n)]
        field_simp [ht_ne n]
      _ = |‖h‖| * |menv ω| := by
        rw [abs_of_nonneg (norm_nonneg h)]
  have hD_meas : AEStronglyMeasurable (fun ω => D ω h) P :=
    hq.aestronglyMeasurable hq_meas
  have hD_norm : eLpNorm (fun ω => D ω h) 2 P ≤
      eLpNorm (fun ω => ‖h‖ * menv ω) 2 P :=
    eLpNorm_le_of_tendstoInMeasure hq_bound hq hq_meas
  exact ⟨hD_meas, hD_norm.trans_lt (hmenv.const_mul ‖h‖).2⟩

/-- Fixed-direction local-scale `L²(P)` convergence obtained from
differentiability in probability and a common pointwise `L²` envelope.

For every fixed `h`, the normalized increment along
`θ₀ + (√n)⁻¹ h` converges in `L²(P)` to `D h`.  Edge behavior: no condition is
imposed at `n = 0`; the proof works on an eventual positive tail.  When `h = 0`
the conclusion reduces to the zero-function identity, so no positivity or
nonzero-direction hypothesis is required. -/
theorem eLpNorm_localScale [IsFiniteMeasure P] {m : E → Ω → ℝ}
    {D : Ω → E →L[ℝ] ℝ} {θ₀ : E}
    -- The defining probability-differentiability premise.
    (hdiff : DifferentiableInProbabilityAt P m D θ₀)
    -- Minimal measure-relative measurability of the criterion sections.
    (hm_meas : ∀ θ, AEStronglyMeasurable (m θ) P)
    -- vdV 5.39's common local log-Lipschitz envelope in `L²(P)`.
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    -- A nontrivial local neighborhood on which the envelope applies.
    (ρ : ℝ) (hρ : 0 < ρ)
    -- Pointwise local domination; moving spikes show that it is necessary.
    (henv : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
      |m θ ω - m θ₀ ω| ≤ ‖menv ω‖ * ‖θ - θ₀‖)
    (h : E) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun ω => Real.sqrt n *
        (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω) - D ω h) 2 P)
      atTop (𝓝 0) := by
  by_cases hh : h = 0
  · subst h
    simp
  let s : ℕ → ℝ := fun n => Real.sqrt n
  let t : ℕ → ℝ := fun n => (s n)⁻¹
  let θ : ℕ → E := fun n => θ₀ + t n • h
  let q : ℕ → Ω → ℝ := fun n ω => s n * (m (θ n) ω - m θ₀ ω)
  have hs : Tendsto s atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto t atTop (nhds 0) := by
    exact tendsto_inv_atTop_zero.comp hs
  have hθ_nhds : Tendsto θ atTop (nhds θ₀) := by
    have hc : Tendsto (fun _ : ℕ => θ₀) atTop (nhds θ₀) := tendsto_const_nhds
    simpa [θ] using hc.add (ht.smul_const h)
  have hs_pos : ∀ᶠ n in atTop, 0 < s n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hθ_ne : ∀ᶠ n in atTop, θ n ≠ θ₀ := by
    filter_upwards [hs_pos] with n hn
    simp only [θ, ne_eq, add_eq_left]
    exact smul_ne_zero (inv_ne_zero hn.ne') hh
  have hθ : Tendsto θ atTop (nhdsWithin θ₀ {θ₀}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hθ_nhds, hθ_ne⟩
  have hres := hdiff.comp hθ
  have hscaled : TendstoInMeasure P
      (fun n ω => ‖h‖ *
        (‖θ n - θ₀‖⁻¹ * (m (θ n) ω - m θ₀ ω - D ω (θ n - θ₀))))
      atTop (fun _ => 0) := hres.const_mul_zero ‖h‖
  have hsub : TendstoInMeasure P
      (fun n ω => q n ω - D ω h) atTop (fun _ => 0) := by
    refine hscaled.congr' ?_ EventuallyEq.rfl
    filter_upwards [hs_pos] with n hn
    filter_upwards with ω
    simp only [q, θ, t, add_sub_cancel_left, map_smul, smul_eq_mul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
    field_simp [hn.ne']
  have hq : TendstoInMeasure P q atTop (fun ω => D ω h) := by
    rw [tendstoInMeasure_iff_norm] at hsub ⊢
    simpa using hsub
  have hq_meas (n : ℕ) : AEStronglyMeasurable (q n) P := by
    exact ((hm_meas (θ n)).sub (hm_meas θ₀)).const_mul (s n)
  have hD : MemLp (fun ω => D ω h) 2 P :=
    hdiff.deriv_apply_memLp_two hm_meas menv hmenv ρ hρ henv h
  have hq_bound : ∀ᶠ n in atTop, ∀ ω,
      |q n ω| ≤ ‖h‖ * |menv ω| := by
    filter_upwards [hθ_nhds.eventually (Metric.closedBall_mem_nhds θ₀ hρ), hs_pos]
      with n hnθ hn ω
    have hdom := henv (θ n) hnθ ω
    simp only [q, abs_mul]
    rw [abs_of_pos hn]
    calc
      s n * |m (θ n) ω - m θ₀ ω|
          ≤ s n * (‖menv ω‖ * ‖θ n - θ₀‖) :=
            mul_le_mul_of_nonneg_left hdom hn.le
      _ = ‖h‖ * |menv ω| := by
        simp only [θ, t, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hn)]
        field_simp [hn.ne']
  obtain ⟨N, hN⟩ := eventually_atTop.1 hq_bound
  have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ => n) N).2 tendsto_id
  have hq_tail : TendstoInMeasure P (fun n => q (n + N)) atTop (fun ω => D ω h) := by
    simpa only [Function.comp_apply] using! hq.comp hshift
  have hG : MemLp (fun ω => ‖h‖ * menv ω) 2 P := hmenv.const_mul ‖h‖
  have hui : UnifIntegrable (fun n => q (n + N)) 2 P := by
    intro ε hε
    obtain ⟨δ, hδ, hGδ⟩ := hG.eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ, hδ, fun n u hu hPu => ?_⟩
    refine (eLpNorm_mono_ae ?_).trans (hGδ u hu hPu)
    filter_upwards with ω
    by_cases hω : ω ∈ u
    · simp only [Set.indicator_of_mem hω, Real.norm_eq_abs]
      simpa [abs_mul, abs_of_nonneg (norm_nonneg h)] using
        hN (n + N) (Nat.le_add_left N n) ω
    · simp [Set.indicator_of_notMem hω]
  have htail : Tendsto
      (fun n => eLpNorm ((fun ω => q (n + N) ω) - fun ω => D ω h) 2 P)
      atTop (𝓝 0) :=
    tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num)
      (fun n => hq_meas (n + N)) hD hui hq_tail
  apply (tendsto_add_atTop_iff_nat N).1
  simpa only [Pi.sub_apply, q, θ, t, s] using! htail

end DifferentiableInProbabilityAt

end MeasureTheory
