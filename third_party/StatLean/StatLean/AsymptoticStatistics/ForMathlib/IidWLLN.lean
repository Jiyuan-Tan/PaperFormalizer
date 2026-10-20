module
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import StatLean.AsymptoticStatistics.ForMathlib.EmpiricalAverage
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public section

/-!
# Generic i.i.d. weak law of large numbers in probability

For an L¹(P) function `f`, the coordinatewise empirical mean
`(1/n) Σᵢ f(Xᵢ)` converges to `∫ f ∂P` in `Pⁿ`-probability, where
`Pⁿ := Measure.pi (fun _ : Fin n => P)`.

The statement is the Mathlib bridge from the strong law of large numbers
(`ProbabilityTheory.strong_law_ae_real`, a.s. convergence) to convergence in
probability (`MeasureTheory.tendstoInMeasure_of_tendsto_ae`, a.s. → in-prob on
finite measures). The a.s. statement lives on the Kolmogorov extension
`Measure.infinitePi (fun _ : ℕ => P)` over `ℕ → Ω`; it is transported to
`Measure.pi (fun _ : Fin n => P)` over `Fin n → Ω` via the truncation identity
`pi_meas_eq_infinitePi_meas_of_truncate`.

This file is theorem-agnostic (ForMathlib layer): the lemma is a reusable
probability brick with no dependence on the statistical-asymptotics machinery,
and is consumed by the one-step and Z-estimator discharge layers.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Function

namespace AsymptoticStatistics

/-- **Generic iid LLN in probability** under the product measure `Measure.pi`.

For an L¹(P) function `f`, the empirical mean of `f` along the i-th coordinate
converges to `∫ f ∂P` in `Pⁿ`-probability.

This is the Mathlib bridge from `ProbabilityTheory.strong_law_ae` (a.s.
convergence) + `tendstoInMeasure_of_tendsto_ae` (a.s. → in-prob for finite
measures). -/
lemma iid_lln_in_prob_l1
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (_hf : Integrable f P) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|})
      atTop (𝓝 0) := by
  classical
  -- Strategy: lift to the Kolmogorov extension `μ_inf := infinitePi (const P)` on
  -- `ℕ → Ω`, apply `strong_law_ae_real` to the iid sequence `Y i ω := f̃ (ω i)`
  -- (where `f̃` is the strongly measurable representative of `f`), convert
  -- a.s. → in measure via `tendstoInMeasure_of_tendsto_ae`, and pull the result
  -- back to `Measure.pi (Fin n → P)` via `pi_meas_eq_infinitePi_meas_of_truncate`.
  set μ_inf : Measure (ℕ → Ω) := Measure.infinitePi (fun _ : ℕ => P) with hμ_inf
  -- Strongly measurable representative `f̃` of `f`.
  have hf_aesm : AEStronglyMeasurable f P := _hf.aestronglyMeasurable
  set f' : Ω → ℝ := hf_aesm.mk f with hf'_def
  have hf'_meas : Measurable f' := hf_aesm.measurable_mk
  have hff' : f =ᵐ[P] f' := hf_aesm.ae_eq_mk
  have hf'_int : Integrable f' P := _hf.congr hff'
  have hf_integral : ∫ ω, f' ω ∂P = ∫ ω, f ω ∂P := integral_congr_ae hff'.symm
  -- Iid sequence on `(ℕ → Ω, μ_inf)`.
  set Y : ℕ → (ℕ → Ω) → ℝ := fun i ω => f' (ω i) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i =>
    hf'_meas.comp (measurable_pi_apply i)
  -- Each `eval i` is measure-preserving from `μ_inf` to `P`.
  have hMP : ∀ i : ℕ, MeasurePreserving (Function.eval i : (ℕ → Ω) → Ω) μ_inf P :=
    fun i => measurePreserving_eval_infinitePi (μ := fun _ : ℕ => P) i
  -- `Y 0` is integrable on `μ_inf` because `f'` is integrable on `P` and
  -- `eval 0` is measure-preserving.
  have hY0_int : Integrable (Y 0) μ_inf := by
    have := (hMP 0).integrable_comp hf'_meas.aestronglyMeasurable
    simpa [Y, Function.eval] using! this.mpr hf'_int
  -- Pairwise independence of the `Y i`'s.
  have h_iIndep : ProbabilityTheory.iIndepFun Y μ_inf := by
    simpa [Y, Function.eval] using
      (ProbabilityTheory.iIndepFun_infinitePi (Ω := fun _ : ℕ => Ω)
        (P := fun _ : ℕ => P) (X := fun _ : ℕ => f') (fun _ => hf'_meas))
  have h_pair :
      Pairwise ((fun X₁ X₂ : (ℕ → Ω) → ℝ => ProbabilityTheory.IndepFun X₁ X₂ μ_inf) on Y) :=
    fun i j hij => h_iIndep.indepFun hij
  -- All `Y i` are identically distributed: their `μ_inf`-pushforward equals
  -- `P.map f' = f'.map P` for every `i`.
  have hY_map : ∀ i, Measure.map (Y i) μ_inf = Measure.map f' P := by
    intro i
    have h_comp : Y i = f' ∘ (Function.eval i : (ℕ → Ω) → Ω) := by
      funext ω; rfl
    rw [h_comp, ← Measure.map_map hf'_meas (measurable_pi_apply i), (hMP i).map_eq]
  have h_ident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ_inf μ_inf := fun i =>
    { aemeasurable_fst := (hY_meas i).aemeasurable
      aemeasurable_snd := (hY_meas 0).aemeasurable
      map_eq := by rw [hY_map i, hY_map 0] }
  -- Mean of `Y 0`: `∫ Y 0 ∂μ_inf = ∫ f' ∂P = ∫ f ∂P`.
  -- Use `integral_map` (pure aemeasurable hypotheses) — `MeasurePreserving.integral_comp`
  -- requires a `MeasurableEmbedding`, which we don't have for `eval 0`.
  have h_mean : ∫ ω, Y 0 ω ∂μ_inf = ∫ ω, f ω ∂P := by
    have h_int : ∫ ω, f' ω ∂P = ∫ ω, Y 0 ω ∂μ_inf := by
      have hP_eq : P = Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf :=
        (hMP 0).map_eq.symm
      calc ∫ ω, f' ω ∂P
          = ∫ ω, f' ω ∂Measure.map (Function.eval 0 : (ℕ → Ω) → Ω) μ_inf := by rw [← hP_eq]
        _ = ∫ ω, f' ((Function.eval 0 : (ℕ → Ω) → Ω) ω) ∂μ_inf := by
            refine MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable ?_
            exact hf'_meas.aestronglyMeasurable
        _ = ∫ ω, Y 0 ω ∂μ_inf := by rfl
    rw [← h_int, hf_integral]
  -- Apply Etemadi's strong law: `(∑ i ∈ range n, Y i ω) / n → ∫ Y 0 ∂μ_inf` a.s.
  have h_sllN : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / n)
        atTop (𝓝 (∫ ω, Y 0 ω ∂μ_inf)) :=
    ProbabilityTheory.strong_law_ae_real Y hY0_int h_pair h_ident
  -- Bridge `(∑ range n, Y i ω) / n` to `(n : ℝ)⁻¹ * ∑ i : Fin n, f (ω i)`.
  -- We need to (a) rewrite the `Finset.range` sum as a `Fin n` sum, (b) convert
  -- `/n` to `(n : ℝ)⁻¹ * _`, and (c) replace `f' (ω i)` by `f (ω i)` a.e.
  -- Step (c): `f' (ω i) = f (ω i)` for all `i`, μ_inf-a.e.
  -- Uses `MeasurePreserving.quasiMeasurePreserving` + `QuasiMeasurePreserving.ae_eq`
  -- to lift `f =ᵐ[P] f'` along each evaluation `eval i : (ℕ → Ω) → Ω`, then
  -- intersects the resulting countable family of null sets.
  have h_ae_eq : ∀ᵐ ω ∂μ_inf, ∀ i : ℕ, f (ω i) = f' (ω i) := by
    rw [ae_all_iff]
    intro i
    have h_qmp : MeasureTheory.Measure.QuasiMeasurePreserving
        (fun ω : ℕ → Ω => ω i) μ_inf P := (hMP i).quasiMeasurePreserving
    -- `f ∘ eval i =ᵐ[μ_inf] f' ∘ eval i` from `f =ᵐ[P] f'`.
    have h_comp_ae : (fun ω : ℕ → Ω => f (ω i)) =ᵐ[μ_inf] fun ω => f' (ω i) :=
      h_qmp.ae_eq hff'
    exact h_comp_ae
  -- Build the goal-form a.s. convergence: `(n)⁻¹ * ∑ i : Fin n, f (ω i) → ∫ f ∂P`.
  have h_target_ae : ∀ᵐ ω ∂μ_inf,
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
        atTop (𝓝 (∫ ω, f ω ∂P)) := by
    filter_upwards [h_sllN, h_ae_eq] with ω h_lim h_eq_all
    -- Rewrite sequence on the LHS to match `h_lim`'s form.
    have h_seq_eq : ∀ n : ℕ,
        (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))
          = (∑ i ∈ Finset.range n, Y i ω) / n := by
      intro n
      have h_sum : (∑ i : Fin n, f (ω i)) = ∑ i ∈ Finset.range n, Y i ω := by
        rw [← Fin.sum_univ_eq_sum_range fun i => Y i ω]
        refine Finset.sum_congr rfl fun i _ => ?_
        -- Goal: `f (ω ↑i) = Y ↑i ω = f' (ω ↑i)`. Use `h_eq_all ↑i`.
        exact h_eq_all i.val
      rw [h_sum]
      ring
    have h_target_to_sllN :
        (fun n : ℕ => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
          = fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / n := funext h_seq_eq
    rw [h_target_to_sllN, ← h_mean]
    exact h_lim
  -- Convert a.s. convergence to convergence in measure on `μ_inf`.
  have hF_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω : ℕ → Ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i))) μ_inf := by
    intro n
    refine AEStronglyMeasurable.const_mul ?_ _
    refine Finset.aestronglyMeasurable_fun_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun i ω => f (ω i.val)) (μ := μ_inf) (fun i _ => ?_)
    have h_proj : MeasurePreserving (fun ω : ℕ → Ω => ω i.val) μ_inf P := hMP i.val
    exact hf_aesm.comp_measurePreserving h_proj
  have h_in_meas :
      MeasureTheory.TendstoInMeasure μ_inf
        (fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
        atTop (fun _ => ∫ ω, f ω ∂P) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hF_meas h_target_ae
  -- Translate to the `iff_norm` (= `abs` since target is ℝ) form, then transport
  -- to `Measure.pi (Fin n → P)` via the truncation bridge.
  have h_norm := (MeasureTheory.tendstoInMeasure_iff_norm
      (μ := μ_inf) (l := atTop)
      (f := fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)))
      (g := fun _ => ∫ ω, f ω ∂P)).mp h_in_meas
  intro ε hε
  have h_inf := h_norm ε hε
  -- For each n, bridge `μ_inf`-set-measure with `Measure.pi (Fin n → P)`-set-measure.
  -- We pass through the `f'`-version of the set (where `f'` is measurable, so the
  -- set is measurable), using the coordinatewise a.e. equality `f = f'`.
  have h_set_eq : ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|}
      = μ_inf {ω : ℕ → Ω |
          ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
    intro n
    -- Step 1: replace `f` by `f'` inside the `Measure.pi`-set (a.e. on Pⁿ).
    have h_pi_ae : (fun (X : Fin n → Ω) i => f (X i)) =ᵐ[Measure.pi (fun _ : Fin n => P)]
        fun (X : Fin n → Ω) i => f' (X i) :=
      MeasureTheory.Measure.ae_eq_pi (μ := fun _ : Fin n => P)
        (f := fun _ => f) (f' := fun _ => f') (fun _ => hff')
    have h_pi_set_eq :
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|}
        = (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_pi_ae] with X hX
      have hX_eq : ∀ i : Fin n, f (X i) = f' (X i) := fun i => congrFun hX i
      have h_sum_eq : (∑ i : Fin n, f (X i)) = (∑ i : Fin n, f' (X i)) :=
        Finset.sum_congr rfl fun i _ => hX_eq i
      -- Goal: `X ∈ {X | p_f X} = X ∈ {X | p_f' X}` (Prop equality from `Set.EventuallyEq`).
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f (X i)) - ∫ ω, f ω ∂P|) =
             (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|)
      rw [h_sum_eq]
    -- Step 2: bridge the `f'`-set via `pi_meas_eq_infinitePi_meas_of_truncate`.
    have hms_f' : MeasurableSet
        {X : Fin n → Ω |
          ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|} := by
      refine measurableSet_le measurable_const ?_
      refine (Measurable.sub ?_ measurable_const).abs
      refine Measurable.const_mul ?_ _
      exact Finset.measurable_sum _ fun i _ =>
        hf'_meas.comp (measurable_pi_apply i)
    have hbridge_f' :=
      AsymptoticStatistics.pi_meas_eq_infinitePi_meas_of_truncate (ν := P) n hms_f'
    -- Step 3: replace `f'` by `f` inside the `μ_inf`-set (a.e. on μ_inf).
    -- Note: after `hbridge_f'` rewrites, the LHS is in
    -- `{ω | (fun i : Fin n => ω i.val) ∈ {X | ε ≤ |…f' (X i)…|}}` form. We
    -- match that explicit form below.
    have h_inf_set_eq :
        μ_inf {ω : ℕ → Ω |
            (fun i : Fin n => ω i.val) ∈
              {X : Fin n → Ω |
                ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (X i)) - ∫ ω, f ω ∂P|}}
          = μ_inf {ω : ℕ → Ω |
            ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖} := by
      apply MeasureTheory.measure_congr
      filter_upwards [h_ae_eq] with ω hω
      have h_sum_eq : (∑ i : Fin n, f' (ω i.val)) = (∑ i : Fin n, f (ω i)) :=
        Finset.sum_congr rfl fun i _ => (hω i.val).symm
      -- Goal: `ω ∈ {ω | (fun i => ω i.val) ∈ {X | p_f' X}} = ω ∈ {ω | ‖…f (ω i)…‖ ≤ ε}`.
      change (ε ≤ |(n : ℝ)⁻¹ * (∑ i : Fin n, f' (ω i.val)) - ∫ ω, f ω ∂P|) =
             (ε ≤ ‖(n : ℝ)⁻¹ * (∑ i : Fin n, f (ω i)) - ∫ ω, f ω ∂P‖)
      rw [Real.norm_eq_abs, h_sum_eq]
    rw [h_pi_set_eq, hbridge_f', h_inf_set_eq]
  simp_rw [h_set_eq]
  exact h_inf

open AsymptoticStatistics.EmpiricalProcess in
/-- **C (single-base iid WLLN in probability).** For an `L¹(P)` function `g` and the
single-base i.i.d. quadruple `X : ℕ → Ξ → Ω` with `μ.map (X 0) = P`, the empirical
average `ℙₙ g = (1/n)∑_{i<n} g(Xᵢ)` converges to `∫ g ∂P` in `μ`-probability:

    `empiricalAvg g n (fun i : Fin n => X i.val ξ) − ∫ g ∂P →ₚ 0`.

This is the single-base (varying-base `TendstoInProbZero`) sibling of the `Measure.pi`
form `iid_lln_in_prob_l1`; the classical Z-estimator layer consumes this form (it matches
the `(Ξ, μ, X)` sample encoding of the headline theorems). The proof applies
`ProbabilityTheory.strong_law_ae` to the iid `ℝ`-sequence `g ∘ Xᵢ` on `(Ξ, μ)`
(mean `∫ g ∂P` via `μ.map (X 0) = P`) gives a.s. convergence of the prefix averages;
`MeasureTheory.tendstoInMeasure_of_tendsto_ae` upgrades a.s. → in-measure on the finite
measure `μ`; unfold `empiricalAvg` to the `Fin n` prefix average. This direct
argument does not require transport through `Measure.pi`. -/
theorem iid_lln_in_prob_seq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : Ω → ℝ) (hg_meas : Measurable g) (hg_int : Integrable g P)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => empiricalAvg g n (fun i : Fin n => X i.val ξ) - ∫ x, g x ∂P) := by
  classical
  -- The i.i.d. real sequence `Y i ξ = g (X i ξ)` on the single base `(Ξ, μ)`.
  set Y : ℕ → Ξ → ℝ := fun i ξ => g (X i ξ) with hY_def
  have hY_meas : ∀ i, Measurable (Y i) := fun i => hg_meas.comp (hX_meas i)
  -- (i) Independence: post-compose the i.i.d. family `X` with the measurable `g`.
  have hY_indep : ProbabilityTheory.iIndepFun Y μ := by
    simpa [Y, Function.comp_def] using
      hX_indep.comp (fun _ : ℕ => g) (fun _ => hg_meas)
  have hY_pair :
      Pairwise ((fun U V : Ξ → ℝ => ProbabilityTheory.IndepFun U V μ) on Y) :=
    fun i j hij => hY_indep.indepFun hij
  -- (ii) Identical distribution: `IdentDistrib.comp` along `g`.
  have hY_ident : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ := fun i =>
    (hX_id i).comp hg_meas
  -- (iii) Integrability of `Y 0 = g ∘ X 0`, transported along `μ.map (X 0) = P`.
  have hY0_int : Integrable (Y 0) μ := by
    have hiff := MeasureTheory.integrable_map_measure
      (μ := μ) (f := X 0) (g := g) (by rw [hX_law]; exact hg_meas.aestronglyMeasurable)
      (hX_meas 0).aemeasurable
    rw [hX_law] at hiff
    exact hiff.mp hg_int
  -- (iv) Mean of `Y 0` is `∫ g ∂P`, again via `μ.map (X 0) = P`.
  have hY0_mean : ∫ ξ, Y 0 ξ ∂μ = ∫ x, g x ∂P := by
    rw [← hX_law]
    exact (MeasureTheory.integral_map (hX_meas 0).aemeasurable
      hg_meas.aestronglyMeasurable).symm
  -- Etemadi's strong law on `(Ξ, μ)`: prefix averages converge a.s. to `∫ g ∂P`.
  have h_slln : ∀ᵐ ξ ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ξ) / n) atTop
        (𝓝 (∫ ξ, Y 0 ξ ∂μ)) :=
    ProbabilityTheory.strong_law_ae_real Y hY0_int hY_pair hY_ident
  -- Index bridge: `empiricalAvg` over `Fin n` = the `Finset.range n` prefix average.
  set F : ℕ → Ξ → ℝ := fun n ξ => empiricalAvg g n (fun i : Fin n => X i.val ξ) with hF_def
  have hF_eq : ∀ (n : ℕ) (ξ : Ξ), F n ξ = (∑ i ∈ Finset.range n, Y i ξ) / n := by
    intro n ξ
    rw [hF_def]
    simp only [empiricalAvg]
    rw [← Fin.sum_univ_eq_sum_range (fun i => Y i ξ) n]
    ring
  have hF_fun : ∀ n : ℕ, F n = fun ξ => (∑ i ∈ Finset.range n, Y i ξ) / n :=
    fun n => funext (fun ξ => hF_eq n ξ)
  have h_target_ae : ∀ᵐ ξ ∂μ, Tendsto (fun n : ℕ => F n ξ) atTop (𝓝 (∫ x, g x ∂P)) := by
    filter_upwards [h_slln] with ξ hξ
    rw [hY0_mean] at hξ
    have hseq : (fun n : ℕ => F n ξ) = fun n : ℕ => (∑ i ∈ Finset.range n, Y i ξ) / n :=
      funext (fun n => hF_eq n ξ)
    rw [hseq]
    exact hξ
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) μ := by
    intro n
    rw [hF_fun n]
    exact ((Finset.measurable_sum _ fun i _ => hY_meas i).div_const _).aestronglyMeasurable
  -- a.s. ⇒ in measure (μ is a probability measure, hence finite).
  have h_in_meas : MeasureTheory.TendstoInMeasure μ F atTop (fun _ => ∫ x, g x ∂P) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hF_meas h_target_ae
  have h_norm := (MeasureTheory.tendstoInMeasure_iff_norm (μ := μ) (l := atTop)
      (f := F) (g := fun _ => ∫ x, g x ∂P)).mp h_in_meas
  -- Finally convert the `ℝ≥0∞`-valued statement to the `Measure.real` form.
  intro ε hε
  have h_ennreal := h_norm ε hε
  have h_toReal := (ENNReal.tendsto_toReal (by simp)).comp h_ennreal
  simpa [Function.comp_def, measureReal_def] using h_toReal

end AsymptoticStatistics
