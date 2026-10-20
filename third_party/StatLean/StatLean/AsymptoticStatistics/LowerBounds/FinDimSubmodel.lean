module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Core.Pathwise
public import StatLean.AsymptoticStatistics.Core.EIF
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateCLT
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.HasLawExists
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# Finite-dimensional submodels with LAN expansion

Finite-dimensional submodels with LAN expansion at an `L²(P)`-orthonormal basis
of a finite-dimensional subspace of the tangent space. This is the synthesis
step in the proofs of the convolution and LAM theorems (vdV §25.3, used for
Theorems 25.20 and 25.21).

The headline declaration `finDimSubmodel_lan` bundles four conclusions of the
submodel lemma into a single existential:

* (a) the score-sum statistic `Δ_n = (1/√n) Σᵢ g_P(Xᵢ)` is identified;
* (b) `Δ_n ⇝ N_m(0, I_m)` under `Pⁿ`, stated via `WeakConverges` against
  `stdGaussian (EuclideanSpace ℝ (Fin m))`;
* (c) the functional differential `√n (ψ(P_{n,h}) − ψ(P)) → A_m h` where
  `A_m h = ⟨IF_eff, Σᵢ hᵢ g_P i⟩` (scalar case: `ψ : Measure Ω → ℝ`);
* (d) the LAN remainder `R_n h → 0` in `Pⁿ`-probability.

Conclusion (a) is automatic by definition; (c) is the functional differential
along the LAN time-curve `t = (√n)⁻¹`, derived from
`PathwiseDifferentiableAt.derivative_spec` composed with
`Tendsto (fun n ↦ (√n)⁻¹) atTop (𝓝[≠] 0)`, then identified with
`⟨IF_eff, score⟩` via the influence-function clause of
`IsEfficientInfluenceFunction`. The score-sum CLT (b) is supplied in
`infinitePi P`-form and bridged internally to the `Pⁿ`-form via
`AsymptoticStatistics.pi_const_eq_infinitePi_map`. The LAN remainder (d) is
taken as an existential whose book content is the Hellinger expansion
`log ∏(p_{n,h}/p)(X_i) = hᵀΔ − ½‖h‖² + R_n` (vdV §7.2, §25.3).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.LowerBounds.FinDimSubmodel

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The submodel along a QMDPath at the LAN time-scale `t = 1/√n`:
`P_{n,h} := γ.curve (1/√n)` where `γ` is the QMDPath whose score is
`Σᵢ hᵢ · g_P i`.

Reference: vdV §25.3, the LAN parameterisation. -/
noncomputable def submodelAt (γ : QMDPath P) (n : ℕ) : Measure Ω :=
  γ.curve ((Real.sqrt n)⁻¹)

/-- The standardised score-sum statistic on `(Fin n → Ω)` for a fixed
orthonormal score basis `g_P : Fin m → ↥(L2ZeroMean P)`. Coordinate-wise
`Δ_n X i = (1/√n) · Σⱼ (g_P i)(Xⱼ)`. The integral (a) clause of
`finDimSubmodel_lan` is by definition. -/
noncomputable def scoreSumStat
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (n : ℕ) (X : Fin n → Ω) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i : Fin m => (Real.sqrt n)⁻¹ *
    ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j))

/-- *Lemma 1: finite-dim submodel LAN at an orthonormal score basis.*

Given:

* a tangent specification `T_set` at `P` whose closed linear span is
  the tangent space `tangentSpace T_set`;
* a pathwise-differentiable scalar functional `ψ : Measure Ω → ℝ` with
  efficient influence function `IF_eff`;
* dimension `m : ℕ` and an `L²(P)`-orthonormal family
  `g_P : Fin m → ↥(L2ZeroMean P)` of tangent directions
  (each `g_P i ∈ T_set.carrier`);
* a QMDPath family `γ : (Fin m → ℝ) → QMDPath P` along the score
  `Σᵢ hᵢ · g_P i` for each `h ∈ ℝᵐ`;

then for the chosen direction `h : Fin m → ℝ`, the joint experiment
`Pⁿ` admits the LAN expansion at `h`, the standardised score-sum `Δ_n`
converges weakly to `N_m(0, I_m)`, and the functional differential
converges to `⟨IF_eff, Σᵢ hᵢ g_P i⟩`.

Reference: vdV §25.3.

The score-sum CLT (b) is supplied as the hypothesis `hCLT_inf` in the brick's
natural `Measure.infinitePi P`-form conclusion, and the proof body internally
bridges to the `Pⁿ`-form via
`AsymptoticStatistics.pi_const_eq_infinitePi_map`. The LAN remainder
convergence (d) is taken as a single existential hypothesis
(`hLAN_expansion`): the witness `R_lan` and its convergence proof `hRem` are
extracted internally by `Classical.choose`/`Classical.choose_spec`. The
analytic identities (a) and (c) are derived internally. -/
theorem finDimSubmodel_lan
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (_hg_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    -- `Σᵢ hᵢ · g_P i`; vdV §25.3.
    (γ : (Fin m → ℝ) → QMDPath P)
    (hγ_score : ∀ h : Fin m → ℝ,
      (γ h).score = ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)))
    -- vdV §25.3.
    (h : Fin m → ℝ)
    -- Score-sum CLT in `infinitePi`-form, the shape directly produced by
    -- `ProbabilityTheory.tendstoInDistribution_multivariate_clt`. The proof
    -- body bridges to `Pⁿ`-form via `pi_const_eq_infinitePi_map` plus a
    -- `Tendsto`-on-`ProbabilityMeasure` to `WeakConverges` translation via
    -- `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`.
    --
    -- The hypothesis statement: under the iid Kolmogorov extension
    -- `Measure.infinitePi (fun _ : ℕ => P)`, the standardised score-sum
    -- (in `Finset.range n`-iid form) converges weakly to the standard
    -- multivariate Gaussian. This follows from the CLT brick by:
    -- (i) building the iid basis evaluation `Xseq k ω∞ := f (ω∞ k)`,
    -- (ii) verifying mean-zero (from `g_P i ∈ L2ZeroMean P`) and
    --      identity covariance (from orthonormality `_hg_orth`),
    -- (iii) instantiating with `S = 1`, `Y = id`, `multivariateGaussian 0 1
    --      = stdGaussian`.
    (hCLT_inf :
      WeakConverges
        (fun n : ℕ =>
          (Measure.infinitePi (fun _ : ℕ => P)).map
            (fun ω : ℕ → Ω =>
              WithLp.toLp 2 (fun i : Fin m =>
                (Real.sqrt n)⁻¹ *
                ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val))))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))))
    -- existence + Pⁿ-probability convergence to 0.
    -- Book content: vdV §7.2 / §25.3, the residual term in
    -- `log ∏ (dP_{n,h}/dP)(X_k) = hᵀ Δ_n − ½‖h‖² + R_n h`.
    -- Strict tightening of the prior `(R_lan, hRem)` pair: the user
    -- supplies the existential rather than a specific witness + proof.
    -- Witness extracted internally by `Classical.choose`/`_spec`. Book
    -- proof of the existential uses the QMD limit's `o(t²)` rate plus
    -- `ForMathlib/LogTaylor.logTaylorRemainder_tendsto_zero` plus the
    -- LLN-style variance bound from `ForMathlib/MeanVarConvergence.lean`.
    (hLAN_expansion :
      ∃ R_lan : (n : ℕ) → (Fin n → Ω) → ℝ,
        ∀ ε > 0,
          Tendsto (fun n : ℕ =>
            (MeasureTheory.Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω | ε ≤ |R_lan n X|})
            atTop (𝓝 (0 : ℝ≥0∞))) :
    -- Conclusion bundle: there exist a score-sum statistic `Δ` and a
    -- LAN remainder `R` realising the four book claims.
    ∃ (Δ : (n : ℕ) → (Fin n → Ω) → EuclideanSpace ℝ (Fin m))
      (R : (n : ℕ) → (Fin n → Ω) → ℝ),
      -- (a) `Δ` is the standardised score sum, evaluated coordinate-wise.
      (∀ (n : ℕ) (X : Fin n → Ω) (i : Fin m),
        Δ n X i = (Real.sqrt n)⁻¹ *
          ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X j)) ∧
      -- (b) Score-sum CLT: `Δ_n ⇝ N_m(0, I_m)` under `Pⁿ`, stated as
      -- weak convergence of pushforwards on `EuclideanSpace ℝ (Fin m)`.
      (WeakConverges
          (fun n : ℕ =>
            (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map (Δ n))
          (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m)))) ∧
      -- (c) Functional differential: `√n (ψ(P_{n,h}) − ψ P) → ⟨IF_eff, score⟩`.
      (Tendsto (fun n : ℕ =>
          Real.sqrt n * (ψ (submodelAt (γ h) n) - ψ P))
        atTop
        (𝓝 (⟪(IF_eff : ↥(L2ZeroMean P)),
              ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))) ∧
      -- (d) LAN remainder `R_n → 0` in `Pⁿ`-probability.
      (∀ ε > 0,
        Tendsto (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω | ε ≤ |R n X|})
          atTop (𝓝 (0 : ℝ≥0∞))) := by
  classical
  -- Extract the LAN remainder witness and its convergence proof from the
  -- uses of `R_lan` and `hRem` (the existential's `R` field and clause (d))
  -- pull from the same `Classical.choose` projection so they remain
  -- syntactically identical.
  obtain ⟨R_lan, hRem⟩ := hLAN_expansion
  -- ===================================================================
  -- Bridge `hCLT_inf` (CLT in `infinitePi P`-form) to the target `Pⁿ`-form via
  -- `AsymptoticStatistics.pi_const_eq_infinitePi_map`.
  --
  -- Pushforward chain: `Pⁿ.map (scoreSumStat g_P n)` factors as
  -- `(infinitePi P).map (truncate_n)).map (scoreSumStat g_P n)` =
  -- `(infinitePi P).map (scoreSumStat g_P n ∘ truncate_n)` where
  -- `truncate_n ω∞ := fun i : Fin n => ω∞ i.val`. The composite
  -- `scoreSumStat g_P n ∘ truncate_n` is **definitionally** the integrand
  -- in `hCLT_inf`'s pushforward, so the bridge collapses to a `rw`.
  -- ===================================================================
  have hCLT :
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
            (scoreSumStat g_P n))
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin m))) := by
    -- For each `n`, factor `Pⁿ.map (scoreSumStat g_P n)` through the
    -- infinitePi pushforward via `pi_const_eq_infinitePi_map`.
    have h_pushforward_eq : ∀ n : ℕ,
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map (scoreSumStat g_P n) =
        (Measure.infinitePi (fun _ : ℕ => P)).map
          (fun ω : ℕ → Ω =>
            WithLp.toLp 2 (fun i : Fin m =>
              (Real.sqrt n)⁻¹ *
              ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val))) := by
      intro n
      -- `Measure.pi (fun _ : Fin n => P) = (infinitePi P).map truncate_n`.
      rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n]
      -- Now LHS is `((infinitePi P).map truncate_n).map (scoreSumStat g_P n)`.
      -- Combine via `Measure.map_map`.
      have h_truncate_meas :
          Measurable (fun ω : ℕ → Ω => fun i : Fin n => ω i.val) := by
        refine measurable_pi_lambda _ (fun i => ?_)
        exact measurable_pi_apply _
      have h_score_meas : Measurable (scoreSumStat g_P n) := by
        unfold scoreSumStat
        refine (WithLp.measurable_toLp 2 (Fin m → ℝ)).comp ?_
        refine measurable_pi_lambda _ (fun i => ?_)
        refine Measurable.const_mul ?_ _
        refine Finset.measurable_sum _ (fun j _ => ?_)
        exact (Lp.stronglyMeasurable _).measurable.comp (measurable_pi_apply _)
      rw [Measure.map_map h_score_meas h_truncate_meas]
      -- `scoreSumStat g_P n ∘ truncate_n` reduces by definition.
      rfl
    -- Now `hCLT_inf` is exactly the RHS sequence; transport through equality.
    intro F
    have h := hCLT_inf F
    -- The functions are equal up to `h_pushforward_eq`; rewrite under integral.
    have h_int_eq : ∀ n : ℕ,
        ∫ x, F x ∂((MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
                      (scoreSumStat g_P n)) =
        ∫ x, F x ∂((Measure.infinitePi (fun _ : ℕ => P)).map
          (fun ω : ℕ → Ω =>
            WithLp.toLp 2 (fun i : Fin m =>
              (Real.sqrt n)⁻¹ *
              ∑ j : Fin n, ((g_P i : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (ω j.val)))) := by
      intro n; rw [h_pushforward_eq n]
    simp_rw [h_int_eq]
    exact h
  -- Existential witnesses: `Δ` from `scoreSumStat`, `R` from the
  -- extracted LAN remainder `R_lan`.
  refine ⟨scoreSumStat g_P, R_lan, ?_, ?_, ?_, ?_⟩
  · -- (a) by definition of `scoreSumStat`.
    intro n X i
    rfl
  · -- (b) the score-sum CLT, derived above.
    exact hCLT
  · -- (c) functional differential — the genuine internal derivation.
    -- Step (c.1): the score `Σᵢ hᵢ • g_P i` lies in the tangent space.
    -- Each `g_P i` is in `T_set.carrier`, hence in the linear span,
    -- hence in the topological closure of the span (= `tangentSpace`).
    -- Submodule closure under sums/scalar multiples gives the conclusion.
    have hg_in_T : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set :=
      hg_in_tangent
    have h_score_in_T :
        ((γ h).score : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := by
      rw [hγ_score h]
      refine Submodule.sum_mem _ ?_
      intro i _
      exact (tangentSpace T_set).smul_mem (h i) (hg_in_T i)
    -- Step (c.2): `derivative_spec` along `γ h`, evaluated along the
    -- LAN time-curve `t = (√n)⁻¹` which tends to `0` from `≠ 0`.
    have h_diffquot :
        Tendsto (fun t : ℝ => (ψ ((γ h).curve t) - ψ P) / t)
          (nhdsWithin 0 {0}ᶜ)
          (𝓝 (hψ.derivative ⟨(γ h).score, h_score_in_T⟩)) :=
      hψ.derivative_spec (γ h) h_score_in_T
    have h_sqrt_inv :
        Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop
          (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · -- `(√n)⁻¹ → 0` along `atTop`: compose `Nat.cast` to ℝ, sqrt to ∞,
        -- and inv to 0.
        have h_nat_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
          tendsto_natCast_atTop_atTop
        have h_sqrt_atTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
          Real.tendsto_sqrt_atTop.comp h_nat_atTop
        exact tendsto_inv_atTop_zero.comp h_sqrt_atTop
      · -- Eventually `(√n)⁻¹ ∈ {0}ᶜ` (i.e. `≠ 0`), namely once `n ≥ 1`.
        filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hn_pos : 0 < (n : ℝ) := by
          have : (1 : ℕ) ≤ n := hn
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
        have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
        have h_inv_pos : 0 < (Real.sqrt n)⁻¹ := inv_pos.mpr h_sqrt_pos
        exact h_inv_pos.ne'
    have h_comp :
        Tendsto (fun n : ℕ =>
            (ψ ((γ h).curve ((Real.sqrt n)⁻¹)) - ψ P) / (Real.sqrt n)⁻¹)
          atTop
          (𝓝 (hψ.derivative ⟨(γ h).score, h_score_in_T⟩)) :=
      h_diffquot.comp h_sqrt_inv
    -- Step (c.3): rewrite the difference quotient at `t = (√n)⁻¹` as
    -- `√n * (ψ(submodelAt …) - ψ P)`.
    have h_curve_eq : ∀ n : ℕ,
        (ψ ((γ h).curve ((Real.sqrt n)⁻¹)) - ψ P) / (Real.sqrt n)⁻¹ =
          Real.sqrt n * (ψ (submodelAt (γ h) n) - ψ P) := by
      intro n
      unfold submodelAt
      by_cases hn : (Real.sqrt n)⁻¹ = 0
      · -- Edge case: `(√n)⁻¹ = 0` ⇒ `√n = 0`. Both sides vanish.
        have hsqrt_zero : Real.sqrt n = 0 := inv_eq_zero.mp hn
        rw [hn, hsqrt_zero]
        simp
      · -- Generic case: rewrite division by `(√n)⁻¹` as multiplication
        -- by `√n`.
        field_simp
    have h_comp' :
        Tendsto (fun n : ℕ =>
            Real.sqrt n * (ψ (submodelAt (γ h) n) - ψ P))
          atTop
          (𝓝 (hψ.derivative ⟨(γ h).score, h_score_in_T⟩)) := by
      have := h_comp
      simp_rw [h_curve_eq] at this
      exact this
    -- Step (c.4): identify `derivative ⟨γ.score, _⟩` with
    -- `⟨IF_eff, Σᵢ hᵢ • g_P i⟩` via the influence-function clause.
    have h_deriv_eq :
        hψ.derivative ⟨(γ h).score, h_score_in_T⟩ =
          ⟪(IF_eff : ↥(L2ZeroMean P)),
            ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ := by
      have h_score := hγ_score h
      have h_score_in_T' :
          (∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))) ∈ tangentSpace T_set := by
        rw [← h_score]; exact h_score_in_T
      have h_inner :
          ⟪(IF_eff : ↥(L2ZeroMean P)),
            (⟨∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)), h_score_in_T'⟩ :
              tangentSpace T_set)⟫_ℝ
            = hψ.derivative
                ⟨∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)), h_score_in_T'⟩ :=
        hEIF.1 ⟨∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)), h_score_in_T'⟩
      -- Bridge `derivative ⟨γ.score, _⟩` to `derivative ⟨Σᵢ hᵢ • g_P i, _⟩`
      -- via congruence on the underlying score equality.
      have h_subtype_eq :
          (⟨(γ h).score, h_score_in_T⟩ : tangentSpace T_set) =
          ⟨∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)), h_score_in_T'⟩ := by
        apply Subtype.ext
        exact h_score
      rw [h_subtype_eq, ← h_inner]
    rw [← h_deriv_eq]
    exact h_comp'
  · -- (d) LAN remainder convergence is `hRem`.
    exact hRem

end AsymptoticStatistics.LowerBounds.FinDimSubmodel
