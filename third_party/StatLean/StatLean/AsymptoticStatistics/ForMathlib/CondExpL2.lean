module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section

/-!
# Doob-factorization helpers at the `Lp` level

When `f : α → β` is measurable, every `(σ_β.comap f)`-measurable function
on `α` factors as `g ∘ f` for some measurable `g : β → ℝ` (Doob's
factorization lemma). At the `L^p` level this gives an isometric
isomorphism between the `(σ_β.comap f)`-measurable subspace of
`Lp ℝ p μ` and `Lp ℝ p (μ.map f)`.

This file packages the Doob L² isomorphism (`doobL2Equiv`) plus its key
behavioral lemma as named declarations. The mathematical content is
standard (Bogachev II §10.4; Kallenberg, Theorem 6.4).
-/

open MeasureTheory
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.CondExpL2

/-- Lp-level congruence across an equality of measures (same σ-algebra).
Trivial via `subst`, but used as a building block to bridge the
`Measure.map f (μ.trim hf.comap_le) = μ.map f` equality at the Lp
layer where there is no `MeasurePreserving`/`MemLp` synthesis to
fight with. -/
noncomputable def lpCongrMeasure
    {γ : Type*} {mγ : MeasurableSpace γ} {ν ν' : @Measure γ mγ}
    (h : ν = ν') :
    @Lp γ ℝ mγ _ 2 ν ≃ₗᵢ[ℝ] @Lp γ ℝ mγ _ 2 ν' := by
  subst h
  exact LinearIsometryEquiv.refl ℝ _

/-- *Measure-preserving witness* for the comap-trim/map setup:
`f' : α' → β'` with the comap σ-algebra on `α'` is measure-preserving
from `μ'.trim hf'.comap_le` to `Measure.map f' (μ'.trim hf'.comap_le)`. -/
theorem lpTrimComapToMapTrim_hfmp
    {α' β' : Type*}
    {m0 : MeasurableSpace α'} {mβ : MeasurableSpace β'}
    {μ' : @Measure α' m0} {f' : α' → β'}
    (hf' : @Measurable α' β' m0 mβ f') :
    @MeasurePreserving α' β' (MeasurableSpace.comap f' mβ) mβ f'
      (μ'.trim hf'.comap_le)
      (@Measure.map α' β' (MeasurableSpace.comap f' mβ) mβ f'
        (μ'.trim hf'.comap_le)) := by
  letI : MeasurableSpace α' := MeasurableSpace.comap f' mβ
  exact (comap_measurable (f := f')).measurePreserving (μ'.trim hf'.comap_le)

/-- *Trim-side pullback isometry*, given by `Lp.compMeasurePreservingₗᵢ`
along the measure-preserving witness `lpTrimComapToMapTrim_hfmp`. -/
noncomputable def lpTrimComapToMapTrim_pull
    {α' β' : Type*}
    {m0 : MeasurableSpace α'} {mβ : MeasurableSpace β'}
    {μ' : @Measure α' m0} {f' : α' → β'}
    (hf' : @Measurable α' β' m0 mβ f') :
    @Lp β' ℝ mβ _ 2
        (@Measure.map α' β' (MeasurableSpace.comap f' mβ) mβ f'
          (μ'.trim hf'.comap_le))
      →ₗᵢ[ℝ]
    @Lp α' ℝ (MeasurableSpace.comap f' mβ) _ 2 (μ'.trim hf'.comap_le) :=
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  Lp.compMeasurePreservingₗᵢ
    (𝕜 := ℝ) (E := ℝ)
    (m := MeasurableSpace.comap f' mβ)
    (μ := μ'.trim hf'.comap_le)
    (μb := @Measure.map α' β' (MeasurableSpace.comap f' mβ) mβ f'
      (μ'.trim hf'.comap_le))
    (p := (2 : ℝ≥0∞))
    f' (lpTrimComapToMapTrim_hfmp hf')

/-- *Surjectivity of the trim-side pullback.* This is the meat of the
Doob factorization at the `L²` level: every `(comap f' mβ)`-measurable
`Lp` element on the source is the pullback of some `Lp` element on the
target. -/
theorem lpTrimComapToMapTrim_surj
    {α' β' : Type*}
    {m0 : MeasurableSpace α'} {mβ : MeasurableSpace β'}
    {μ' : @Measure α' m0} {f' : α' → β'}
    (hf' : @Measurable α' β' m0 mβ f') :
    Function.Surjective (lpTrimComapToMapTrim_pull (m0 := m0) (mβ := mβ)
      (μ' := μ') (f' := f') hf') := by
  intro u
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  let m : MeasurableSpace α' := MeasurableSpace.comap f' mβ
  let μtrim : @Measure α' m := μ'.trim hf'.comap_le
  let ν : @Measure β' mβ := @Measure.map α' β' m mβ f' μtrim
  obtain ⟨g, hg_sm, hgu⟩ :=
    (Lp.stronglyMeasurable (m := m) u).exists_eq_measurable_comp (f := f')
  have hmem : MemLp g 2 ν ↔ MemLp (g ∘ f') 2 μtrim := by
    simpa [ν, μtrim] using
      (memLp_map_measure_iff (f := f') (g := g) (μ := μtrim)
        (by simpa [ν] using hg_sm.aestronglyMeasurable)
        (by simpa using (comap_measurable (f := f')).aemeasurable))
  have hg_mem : MemLp g 2 ν :=
    hmem.2 (by simpa [μtrim, hgu] using (Lp.memLp (m := m) u))
  refine ⟨hg_mem.toLp g, ?_⟩
  change Lp.compMeasurePreserving f' (lpTrimComapToMapTrim_hfmp hf')
      (hg_mem.toLp g) = u
  calc
    Lp.compMeasurePreserving f' (lpTrimComapToMapTrim_hfmp hf') (hg_mem.toLp g)
        = (hg_mem.comp_measurePreserving (lpTrimComapToMapTrim_hfmp hf')).toLp
            (g ∘ f') := by
              simpa using
                (Lp.toLp_compMeasurePreserving (g := g) (f := f') hg_mem
                  (lpTrimComapToMapTrim_hfmp hf'))
    _ = (Lp.memLp (m := m) u).toLp ((u : @Lp α' ℝ m _ 2 μtrim) : α' → ℝ) :=
          MemLp.toLp_congr
            (hg_mem.comp_measurePreserving (lpTrimComapToMapTrim_hfmp hf'))
            (Lp.memLp (m := m) u)
            (Filter.Eventually.of_forall (fun x =>
              congrArg (fun h : α' → ℝ => h x) hgu.symm))
    _ = u := Lp.toLp_coeFn (m := m) u (Lp.memLp (m := m) u)

/-- *Trim-side Doob isometry, codomain `Measure.map f μtrim`.* The
codomain is intentionally kept as `Measure.map f (μ.trim hf.comap_le)`
(at the comap σ-algebra), *not* rewritten to `μ.map f`. The
cross-σ-algebra rewrite happens *afterwards* via
`lpCongrMeasure (map_trim_comap hf)` in `lpTrimComapToLpMap`.

Built from `lpTrimComapToMapTrim_pull` and `lpTrimComapToMapTrim_surj`. -/
noncomputable def lpTrimComapToMapTrim_aux
    {α' β' : Type*}
    {m0 : MeasurableSpace α'} {mβ : MeasurableSpace β'}
    {μ' : @Measure α' m0} {f' : α' → β'}
    (hf' : @Measurable α' β' m0 mβ f') :
    @Lp α' ℝ (MeasurableSpace.comap f' mβ) _ 2 (μ'.trim hf'.comap_le)
      ≃ₗᵢ[ℝ]
    @Lp β' ℝ mβ _ 2
      (@Measure.map α' β' (MeasurableSpace.comap f' mβ) mβ f'
        (μ'.trim hf'.comap_le)) :=
  (LinearIsometryEquiv.ofSurjective
    (lpTrimComapToMapTrim_pull (m0 := m0) (mβ := mβ)
      (μ' := μ') (f' := f') hf')
    (lpTrimComapToMapTrim_surj (m0 := m0) (mβ := mβ)
      (μ' := μ') (f' := f') hf')).symm

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {f : α → β} (hf : Measurable f)

/-- *First factor of `lpTrimComapToLpMap`.* The trim-side Doob isometry
`lpTrimComapToMapTrim_aux` specialized to the section's
`(α, β, μ, f, hf)` tuple. -/
noncomputable def lpTrimComapToLpMap_e1 :=
  lpTrimComapToMapTrim_aux
    (α' := α) (β' := β)
    (m0 := ‹MeasurableSpace α›) (mβ := ‹MeasurableSpace β›)
    (μ' := μ) (f' := f) hf

/-- *Second factor of `lpTrimComapToLpMap`.* Cross-σ-algebra transport
along `map_trim_comap hf`. -/
noncomputable def lpTrimComapToLpMap_e2 :=
  lpCongrMeasure
    (γ := β) (mγ := ‹MeasurableSpace β›)
    (ν :=
      @Measure.map α β (MeasurableSpace.comap f ‹MeasurableSpace β›)
        ‹MeasurableSpace β› f (μ.trim hf.comap_le))
    (ν' := @Measure.map α β ‹MeasurableSpace α› ‹MeasurableSpace β› f μ)
    (by simpa using (map_trim_comap (μ := μ) (f := f) hf))

/-- The trimmed-side Doob isometry:
`Lp ℝ 2 (μ.trim hf.comap_le) ≃ₗᵢ Lp ℝ 2 (μ.map f)`.

Built by composing `lpTrimComapToLpMap_e1` and `lpTrimComapToLpMap_e2`. -/
noncomputable def lpTrimComapToLpMap :
    Lp ℝ 2 (μ.trim hf.comap_le) ≃ₗᵢ[ℝ] Lp ℝ 2 (μ.map f) :=
  (lpTrimComapToLpMap_e1 hf).trans (lpTrimComapToLpMap_e2 hf)

/-- *Doob L² isomorphism.* For a measurable `f : α → β`, the
`(σ_β.comap f)`-measurable subspace of `Lp ℝ 2 μ` is isometrically
isomorphic to `Lp ℝ 2 (μ.map f)`.

Chains `lpMeasToLpTrimLie` (Mathlib's `lpMeas ≃ Lp(trim)`) with
`lpTrimComapToLpMap` (the Doob bridge `Lp(trim) ≃ Lp(map)`); the Doob
content is concentrated entirely in `lpTrimComapToLpMap`. -/
noncomputable def doobL2Equiv :
    lpMeas ℝ ℝ (MeasurableSpace.comap f ‹MeasurableSpace β›) 2 μ
      ≃ₗᵢ[ℝ] Lp ℝ 2 (μ.map f) :=
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  (lpMeasToLpTrimLie ℝ ℝ 2 μ hf.comap_le).trans (lpTrimComapToLpMap hf)

/-- `lpCongrMeasure` does not change the underlying function. -/
@[simp] private theorem lpCongrMeasure_coeFn
    {γ : Type*} {mγ : MeasurableSpace γ} {ν ν' : @Measure γ mγ}
    (h : ν = ν')
    (g : @Lp γ ℝ mγ _ 2 ν) :
    ((lpCongrMeasure (γ := γ) (mγ := mγ) h g :
        @Lp γ ℝ mγ _ 2 ν') : γ → ℝ) = g := by
  subst h
  rfl

/-- `lpTrimComapToLpMap_e2` does not change the underlying function. -/
private lemma lpTrimComapToLpMap_e2_coeFn
    (g : @Lp β ℝ ‹MeasurableSpace β› _ 2
      (@Measure.map α β (MeasurableSpace.comap f ‹MeasurableSpace β›)
        ‹MeasurableSpace β› f (μ.trim hf.comap_le))) :
    ((lpTrimComapToLpMap_e2 hf g : Lp ℝ 2 (μ.map f)) : β → ℝ)
      = (g : β → ℝ) := by
  unfold lpTrimComapToLpMap_e2
  exact lpCongrMeasure_coeFn _ _

/-- The trimmed-side behavioral identity for `lpTrimComapToMapTrim_aux`:
applying it to `u`, then composing with `f`, recovers `u` `μ`-a.e.

Proof idea: invoke `LinearIsometryEquiv.ofSurjective.apply_symm_apply`
and `Lp.coeFn_compMeasurePreserving`. -/
private theorem lpTrimComapToMapTrim_aux_comp_apply
    {α' β' : Type*}
    {m0 : MeasurableSpace α'} {mβ : MeasurableSpace β'}
    {μ' : @Measure α' m0} {f' : α' → β'}
    (hf' : @Measurable α' β' m0 mβ f')
    (u : @Lp α' ℝ (MeasurableSpace.comap f' mβ) _ 2 (μ'.trim hf'.comap_le)) :
    (fun a =>
      (lpTrimComapToMapTrim_aux
        (α' := α') (β' := β') (m0 := m0) (mβ := mβ)
        (μ' := μ') (f' := f') hf' u) (f' a))
      =ᵐ[μ'] u := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  set pull := lpTrimComapToMapTrim_pull (m0 := m0) (mβ := mβ)
    (μ' := μ') (f' := f') hf' with hpull_def
  set hfmp := lpTrimComapToMapTrim_hfmp (m0 := m0) (mβ := mβ)
    (μ' := μ') (f' := f') hf' with hfmp_def
  have hpull :
      pull
        (lpTrimComapToMapTrim_aux
          (α' := α') (β' := β') (m0 := m0) (mβ := mβ)
          (μ' := μ') (f' := f') hf' u) = u :=
    (LinearIsometryEquiv.ofSurjective pull
        (lpTrimComapToMapTrim_surj (m0 := m0) (mβ := mβ)
          (μ' := μ') (f' := f') hf')).apply_symm_apply u
  have hpull' :
      Lp.compMeasurePreserving f' hfmp
        (lpTrimComapToMapTrim_aux
          (α' := α') (β' := β') (m0 := m0) (mβ := mβ)
          (μ' := μ') (f' := f') hf' u) = u := by
    simpa [pull, lpTrimComapToMapTrim_pull] using! hpull
  have htrim :
      (u : α' → ℝ) =ᵐ[μ'.trim hf'.comap_le]
        (fun a =>
          (lpTrimComapToMapTrim_aux
            (α' := α') (β' := β') (m0 := m0) (mβ := mβ)
            (μ' := μ') (f' := f') hf' u) (f' a)) := by
    simpa [hpull', Function.comp] using!
      (Lp.coeFn_compMeasurePreserving
        (lpTrimComapToMapTrim_aux
          (α' := α') (β' := β') (m0 := m0) (mβ := mβ)
          (μ' := μ') (f' := f') hf' u) hfmp)
  exact (ae_eq_of_ae_eq_trim htrim).symm

/-- *Doob behavioral identity.* Applying the Doob L² isometry `doobL2Equiv`
to a `(σ_β.comap f)`-measurable element `g` of `Lp ℝ 2 μ`, then composing the
resulting function on `β` with `f`, recovers `g` `μ`-a.e.

This is the public form of the trim-side behavioral identity
`lpTrimComapToMapTrim_aux_comp_apply`, lifted through the
`lpMeasToLpTrimLie`/`lpTrimComapToLpMap` chain that defines `doobL2Equiv`.
Downstream consumers (information-loss operator, vdV §25.6) use it for
integral preservation along the coarsening map. -/
theorem doobL2Equiv_comp_apply
    (g : lpMeas ℝ ℝ (MeasurableSpace.comap f ‹MeasurableSpace β›) 2 μ) :
    (fun a => (doobL2Equiv hf g : Lp ℝ 2 (μ.map f)) (f a))
      =ᵐ[μ] ((g : Lp ℝ 2 μ) : α → ℝ) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  -- Name the intermediate trim-side element.
  set t : Lp ℝ 2 (μ.trim hf.comap_le) :=
    lpMeasToLpTrimLie ℝ ℝ 2 μ hf.comap_le g with ht_def
  -- The trim-side behavioral identity: `(e1 t) ∘ f =ᵐ[μ] t`, where
  -- `e1 t = lpTrimComapToLpMap_e1 hf t` by definition.
  have he1 :
      (fun a => (lpTrimComapToLpMap_e1 hf t) (f a)) =ᵐ[μ] (t : α → ℝ) :=
    lpTrimComapToMapTrim_aux_comp_apply hf t
  -- `e2` does not change the underlying function.
  have he2 :
      ((lpTrimComapToLpMap_e2 hf (lpTrimComapToLpMap_e1 hf t) :
          Lp ℝ 2 (μ.map f)) : β → ℝ)
        = ((lpTrimComapToLpMap_e1 hf t : _) : β → ℝ) :=
    lpTrimComapToLpMap_e2_coeFn hf _
  -- `t = lpMeasToLpTrimLie … g`, whose coercion is `g` `μ`-a.e.
  have ht_ae : (t : α → ℝ) =ᵐ[μ] ((g : Lp ℝ 2 μ) : α → ℝ) := by
    simpa [ht_def] using! lpMeasToLpTrim_ae_eq hf.comap_le g
  -- Assemble: `doobL2Equiv hf g = e2 (e1 t)` definitionally.
  have hstep : (fun a => (doobL2Equiv hf g : Lp ℝ 2 (μ.map f)) (f a))
      = (fun a => (lpTrimComapToLpMap_e1 hf t) (f a)) := by
    funext a
    exact congrArg (fun h : β → ℝ => h (f a)) he2
  rw [hstep]
  exact he1.trans ht_ae
end AsymptoticStatistics.ForMathlib.CondExpL2
