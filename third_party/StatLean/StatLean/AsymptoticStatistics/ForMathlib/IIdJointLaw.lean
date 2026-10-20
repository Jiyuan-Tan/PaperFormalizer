module
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-!
# iid joint-law bridge

Bridge between the "abstract iid" setup (`Ω := ℕ → 𝓧` with `Measure.infinitePiNat`) used
by `LANExpansion.LAN_expansion_iii` and the concrete `productMeasure` on `Fin n → 𝓧` used
by the `AsymptoticRepresentation` pipeline.

Core identity:
```
Measure.pi (fun _ : Fin n => ν)
  = (Measure.infinitePiNat (fun _ : ℕ => ν)).map (fun ω i => ω i.val)
```
whenever `ν` is a probability measure.

Combined with `TendstoInMeasure.map`-transport, this lets us pull the LAN residual
`→_P 0` conclusion (in abstract `infinitePiNat` form) down to its `productMeasure`-form
consumed by `AsymptoticRepresentation.slutsky_bridge_of_lanResidual`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics

theorem map_fin_restrict_eq_pi_of_iid
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (n : ℕ) :
    μ.map (fun ξ : Ξ => fun i : Fin n => X i.val ξ) =
      Measure.pi (fun _ : Fin n => P) := by
  have h_indep : ProbabilityTheory.iIndepFun (fun i : Fin n => X i.val) μ :=
    hX_iindep.precomp Fin.val_injective
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : Fin n => (hX_meas i.val).aemeasurable)).mp h_indep]
  congr with i
  rw [(hX_idem i.val).map_eq, hX_law]

theorem map_ghost_fin_restrict_eq_pi_prod_of_iid
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (n : ℕ) :
    (μ.prod μ).map (fun z : Ξ × Ξ =>
        ((fun i : Fin n => X i.val z.1), (fun i : Fin n => X i.val z.2))) =
      (Measure.pi (fun _ : Fin n => P)).prod
        (Measure.pi (fun _ : Fin n => P)) := by
  let Y : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
  have hY_meas : Measurable Y := measurable_pi_lambda _ fun i => hX_meas i.val
  have hY_law : μ.map Y = Measure.pi (fun _ : Fin n => P) :=
    map_fin_restrict_eq_pi_of_iid P μ X hX_meas hX_iindep hX_idem hX_law n
  rw [← hY_law, Measure.map_prod_map μ μ hY_meas hY_meas]
  rfl

/-- `Fin n` and the Finset-range coercion `↥(Finset.range n)` are canonically
equivalent (both are `{k : ℕ // k < n}` up to `Finset.mem_range`). Packaged
as an `Equiv` for use with `Measure.pi`'s reindexing lemmas. -/
def rangeEquivFin (n : ℕ) : ↥(Finset.range n) ≃ Fin n where
  toFun i := ⟨i.val, Finset.mem_range.mp i.prop⟩
  invFun i := ⟨i.val, Finset.mem_range.mpr i.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma rangeEquivFin_apply_val (n : ℕ) (i : ↥(Finset.range n)) :
    ((rangeEquivFin n) i).val = i.val := rfl

@[simp] lemma rangeEquivFin_symm_apply_val (n : ℕ) (i : Fin n) :
    ((rangeEquivFin n).symm i).val = i.val := rfl

/-- **iid product = finite restriction of the Kolmogorov extension**.

The `n`-fold product of a probability measure `ν` equals the pushforward of the
Kolmogorov extension `Measure.infinitePiNat (const ν)` under the `Fin n`-restriction
`ω ↦ fun i : Fin n => ω i.val`.

Proof: both sides agree on rectangles. The rectangle value on the RHS is computed
by unwinding the preimage under `Fin n`-restriction into a cylinder on `Finset.range n`,
then applying `Measure.infinitePiNat_map_restrict` + reindexing `↥(Finset.range n) ≃
Fin n` via `MeasureTheory.measurePreserving_piCongrLeft`. -/
theorem pi_const_eq_infinitePiNat_map
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν)
      = (Measure.infinitePiNat (fun _ : ℕ => ν)).map
          (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) := by
  classical
  -- The map `ω ↦ fun i : Fin n => ω i.val` factors as
  -- `Finset.range n`-restrict composed with pi-reindexing along `rangeEquivFin n`.
  set φ : (ℕ → 𝓧) → (Fin n → 𝓧) := fun ω i => ω i.val with hφ_def
  set ψ : (↥(Finset.range n) → 𝓧) → (Fin n → 𝓧) := fun f i =>
    f ((rangeEquivFin n).symm i) with hψ_def
  have hψ_meas : Measurable ψ := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact measurable_pi_apply _
  have h_factor : φ = ψ ∘ (Finset.range n).restrict := by
    funext ω i; rfl
  have h_restrict_meas :
      Measurable ((Finset.range n).restrict : (ℕ → 𝓧) → (↥(Finset.range n) → 𝓧)) := by
    refine measurable_pi_lambda _ (fun _ => ?_)
    exact measurable_pi_apply _
  -- `ψ` is a measurable isomorphism — `MeasurableEquiv.piCongrLeft` along `rangeEquivFin n`.
  -- Use `Measure.pi_map_piCongrLeft` (or measurePreserving) to transport via it.
  have h_step1 : (Measure.infinitePiNat (fun _ : ℕ => ν)).map
        (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
      = ((Measure.infinitePiNat (fun _ : ℕ => ν)).map (Finset.range n).restrict).map ψ := by
    rw [show (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
          = ψ ∘ (Finset.range n).restrict from h_factor,
      ← Measure.map_map hψ_meas h_restrict_meas]
  rw [h_step1, Measure.infinitePiNat_map_restrict]
  -- Identify the resulting reindexing map with `piCongrLeft`.
  -- `ψ = piCongrLeft (·↦𝓧) (rangeEquivFin n)` — reindexing from `↥(Finset.range n)` to
  -- `Fin n`; this map preserves the product measure.
  have h_ψ_eq : ψ = MeasurableEquiv.piCongrLeft (fun _ : Fin n => 𝓧)
      (rangeEquivFin n) := by
    funext f i
    rw [hψ_def, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [h_ψ_eq]
  have mp := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin n => ν) (rangeEquivFin n)
  exact mp.map_eq.symm

/-- **iid product = finite restriction of the Kolmogorov extension (`infinitePi` version)**.

Parallel to `pi_const_eq_infinitePiNat_map`, using `Measure.infinitePi` (the general
`ι`-indexed product) instead of `Measure.infinitePiNat`. This form is the natural
match for `ProbabilityTheory.iIndepFun_infinitePi`, which is stated for `infinitePi`.
-/
theorem pi_const_eq_infinitePi_map
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ) :
    Measure.pi (fun _ : Fin n => ν)
      = (Measure.infinitePi (fun _ : ℕ => ν)).map
          (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) := by
  classical
  set ψ : (↥(Finset.range n) → 𝓧) → (Fin n → 𝓧) := fun f i =>
    f ((rangeEquivFin n).symm i) with hψ_def
  have hψ_meas : Measurable ψ := by
    refine measurable_pi_lambda _ (fun i => ?_)
    exact measurable_pi_apply _
  have h_factor :
      (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
        = ψ ∘ (Finset.range n).restrict := by
    funext ω i; rfl
  have h_restrict_meas :
      Measurable ((Finset.range n).restrict : (ℕ → 𝓧) → (↥(Finset.range n) → 𝓧)) := by
    refine measurable_pi_lambda _ (fun _ => ?_)
    exact measurable_pi_apply _
  have h_step1 : (Measure.infinitePi (fun _ : ℕ => ν)).map
        (fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val)
      = ((Measure.infinitePi (fun _ : ℕ => ν)).map (Finset.range n).restrict).map ψ := by
    rw [h_factor, ← Measure.map_map hψ_meas h_restrict_meas]
  rw [h_step1, MeasureTheory.Measure.infinitePi_map_restrict]
  have h_ψ_eq : ψ = MeasurableEquiv.piCongrLeft (fun _ : Fin n => 𝓧)
      (rangeEquivFin n) := by
    funext f i
    rw [hψ_def, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [h_ψ_eq]
  have mp := MeasureTheory.measurePreserving_piCongrLeft
    (fun _ : Fin n => ν) (rangeEquivFin n)
  exact mp.map_eq.symm

/-- **`TendstoInMeasure` transports under measure pushforward**.

If the composed sequence `fun ω => g_n (φ ω)` converges to `0` in measure under `P`
and `g_n` is measurable for each `n`, then `g_n` converges to `0` in measure under
the pushforward `P.map φ`. Elementary change-of-variables argument using
`Measure.map_apply`. -/
theorem tendstoInMeasure_of_tendstoInMeasure_comp
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {P : Measure Ω} (φ : Ω → Ω') (hφ : Measurable φ)
    {E : Type*} [PseudoEMetricSpace E] [Zero E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E]
    {g_n : ℕ → Ω' → E}
    (hg_meas : ∀ n, Measurable (g_n n))
    (h : TendstoInMeasure P (fun n ω => g_n n (φ ω)) atTop (fun _ => (0 : E))) :
    TendstoInMeasure (P.map φ) g_n atTop (fun _ => (0 : E)) := by
  intro ε hε
  have h_pull : ∀ n, (P.map φ) {x | ε ≤ edist (g_n n x) 0}
      = P {ω | ε ≤ edist (g_n n (φ ω)) 0} := by
    intro n
    rw [Measure.map_apply hφ]
    · rfl
    · exact measurableSet_le measurable_const ((hg_meas n).edist measurable_const)
  simp_rw [h_pull]
  exact h ε hε

/-- **Pinf → Pⁿ measure-on-set bridge for varying truncation**.

For each `n`, the probability under `Measure.pi (fun _ : Fin n => ν)` of a
predicate on `Fin n → 𝓧` equals the probability under `Measure.infinitePi (const ν)`
of the predicate composed with the truncation `ω ↦ fun i : Fin n => ω i.val`. This
is the per-n measure-equality consequence of `pi_const_eq_infinitePi_map` plus
`Measure.map_apply`, packaged for use inside Slutsky-style `hDist`-arguments where
the base measure varies in `n` and the predicate is parametrised by `n`. -/
lemma pi_meas_eq_infinitePi_meas_of_truncate
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ)
    {s : Set (Fin n → 𝓧)} (hs : MeasurableSet s) :
    Measure.pi (fun _ : Fin n => ν) s
      = (Measure.infinitePi (fun _ : ℕ => ν))
          {ω | (fun i : Fin n => ω i.val) ∈ s} := by
  rw [pi_const_eq_infinitePi_map ν n]
  rw [Measure.map_apply (f := fun ω : ℕ → 𝓧 => fun i : Fin n => ω i.val) ?_ hs]
  · rfl
  · refine measurable_pi_lambda _ (fun _ => ?_)
    exact measurable_pi_apply _

/-- Real-valued (i.e. ENNReal-`toReal`) variant of the measure-on-set bridge. -/
lemma pi_real_eq_infinitePi_real_of_truncate
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    (ν : Measure 𝓧) [IsProbabilityMeasure ν] (n : ℕ)
    {s : Set (Fin n → 𝓧)} (hs : MeasurableSet s) :
    (Measure.pi (fun _ : Fin n => ν)).real s
      = (Measure.infinitePi (fun _ : ℕ => ν)).real
          {ω | (fun i : Fin n => ω i.val) ∈ s} := by
  change ((Measure.pi (fun _ : Fin n => ν)) s).toReal
       = ((Measure.infinitePi (fun _ : ℕ => ν))
            {ω | (fun i : Fin n => ω i.val) ∈ s}).toReal
  rw [pi_meas_eq_infinitePi_meas_of_truncate ν n hs]

end AsymptoticStatistics
