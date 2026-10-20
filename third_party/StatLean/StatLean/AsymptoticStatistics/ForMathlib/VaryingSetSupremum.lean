module
public import StatLean.AsymptoticStatistics.ForMathlib.SetConvergence
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Data.EReal.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

@[expose] public section

/-!
# Suprema over varying sets

Edge-safe supremum and the deterministic sandwich used in the proof of van der
Vaart Corollary 5.58.  Suprema live in `EReal`, so empty and unbounded sets are
represented honestly instead of inheriting `Real.sSup ∅ = 0`.
-/

open Filter Set Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib

/-- The extended-real supremum of `f` over `A`.

Edge behavior: the empty supremum is `⊥`; an unbounded-above real image has
supremum `⊤`.  This is the convention required for changing-set arguments and
is deliberately different from raw `Real.sSup` on degenerate inputs. -/
noncomputable def setSupEReal {D : Type*} (f : D → ℝ) (A : Set D) : EReal :=
  ⨆ h : A, (f h : EReal)

/-- A function has a finite real supremum on a set when the set is nonempty
and its image is bounded above.  This guard prevents the empty/unbounded
fallbacks of `Real.sSup` from leaking into book-facing process laws. -/
def HasFiniteSup {D : Type*} (f : D → ℝ) (A : Set D) : Prop :=
  A.Nonempty ∧ BddAbove (f '' A)

/-- The real supremum of a nonempty, bounded-above image.

Edge behavior is explicit in the type: callers must supply nonemptiness and
boundedness, so neither `Real.sSup ∅ = 0` nor the unbounded fallback can be
observed through this API.  General changing-set arguments use `setSupEReal`
instead. -/
noncomputable def setSupReal {D : Type*} (f : D → ℝ) (A : Set D)
    (_hfinite : HasFiniteSup f A) : ℝ :=
  sSup (f '' A)

/-- The local process carrier `ℓ∞(K)`: bounded real functions on the subtype
`K`, with the supremum norm (vdV §5.9 pp.80--81).

Edge behavior: when `K` is empty this is the one-point bounded-function space. -/
abbrev LinfOn {D : Type*} (K : Set D) : Type _ := lp (fun _ : K => ℝ) ∞

/-- Borel measurable structure on the local `ℓ∞(K)` carrier. -/
noncomputable instance instMeasurableSpaceLinfOn {D : Type*} (K : Set D) :
    MeasurableSpace (LinfOn K) := borel _

/-- The Borel structure on `LinfOn K` is induced by its norm topology. -/
instance instBorelSpaceLinfOn {D : Type*} (K : Set D) :
    BorelSpace (LinfOn K) := ⟨rfl⟩

/-- Restrict a function to `K` and package a supplied uniform-boundedness
witness as an element of `ℓ∞(K)`.

Edge behavior: for `K = ∅` the boundedness witness is automatic; no arbitrary
value outside `K` is introduced. -/
noncomputable def restrictToLinfOn {D : Type*} (K : Set D) (f : D → ℝ)
    (hf : Memℓp (fun h : K => f h) ∞) : LinfOn K :=
  ⟨fun h => f h, hf⟩

/-- The extended-real supremum of a local bounded path over the restricted set
`A ∩ K`; empty intersections give `⊥`. -/
noncomputable def linfSetSup {D : Type*} {K : Set D}
    (z : LinfOn K) (A : Set D) : EReal :=
  ⨆ h : {h : K // (h : D) ∈ A}, (z h.1 : EReal)

/-- Restricting a real path to `LinfOn K` and then taking its edge-safe
supremum over `A` equals the original-path supremum over `A ∩ K`.

Edge behavior: both sides are `⊥` when `A ∩ K` is empty; no finite-supremum
guard or fallback value is introduced. -/
theorem linfSetSup_restrictToLinfOn {D : Type*} (K A : Set D) (f : D → ℝ)
    (hf : Memℓp (fun h : K => f h) ∞) :
    linfSetSup (restrictToLinfOn K f hf) A = setSupEReal f (A ∩ K) := by
  unfold linfSetSup restrictToLinfOn setSupEReal
  apply le_antisymm
  · refine iSup_le fun h => ?_
    exact le_iSup_of_le
      (⟨(h.1 : D), ⟨h.2, h.1.2⟩⟩ : {x // x ∈ A ∩ K}) le_rfl
  · refine iSup_le fun h => ?_
    exact le_iSup_of_le
      (⟨⟨h.1, h.2.2⟩, h.2.1⟩ : {x : K // (x : D) ∈ A}) le_rfl

/-- Uniform convergence in `LinfOn K`, together with convergence of the
evaluation points and continuity of the limit path, implies convergence of
the moving evaluations. -/
private theorem tendsto_linf_apply_of_tendsto_of_tendsto
    {D : Type*} [TopologicalSpace D] {K : Set D}
    {zn : ℕ → LinfOn K} {z : LinfOn K}
    (hz : Tendsto zn atTop (𝓝 z)) {hn : ℕ → K} {h : K}
    (hh : Tendsto hn atTop (𝓝 h)) (hzcont : Continuous z) :
    Tendsto (fun n => zn n (hn n)) atTop (𝓝 (z h)) := by
  have hnorm : Tendsto (fun n => ‖zn n - z‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hz
  have hpointNorm :
      Tendsto (fun n => ‖zn n (hn n) - z (hn n)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall fun n => ?_) hnorm
    simpa only [lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero (zn n - z) (hn n)
  have herror :
      Tendsto (fun n => zn n (hn n) - z (hn n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hpointNorm
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
    herror.add ((hzcont.tendsto h).comp hh)

/-- Uniform convergence in `ℓ∞(K)` implies the full changing-set supremum
sandwich from vdV p.81.

`B` is precompact, its closure lies in the fixed compact carrier `K`, and the
limit path is continuous on that carrier. The extended-real formulation makes
both empty intersections and unbounded global sets honest:

`sup_(interior B ∩ H) z ≤ liminf sup_(B ∩ Hₙ) zₙ
  ≤ limsup sup_(B ∩ Hₙ) zₙ ≤ sup_(closure B ∩ H) z`.

The hypothesis `hBK` places every evaluation in the single carrier `LinfOn K`;
it does not strengthen the book's `B ⊆ K` localization because the proof uses
the closure of the precompact set. -/
theorem varyingSetSupremum_sandwich {D : Type*} [MetricSpace D]
    {Hn : ℕ → Set D} {H B K : Set D}
    (hset : SetConverges Hn H)
    (hB : IsCompact (closure B)) (hBK : closure B ⊆ K)
    {zn : ℕ → LinfOn K} {z : LinfOn K}
    (hz : Tendsto zn atTop (𝓝 z))
    (hzcont : Continuous z) :
    linfSetSup z (interior B ∩ H)
        ≤ liminf (fun n => linfSetSup (zn n) (B ∩ Hn n)) atTop ∧
      liminf (fun n => linfSetSup (zn n) (B ∩ Hn n)) atTop
        ≤ limsup (fun n => linfSetSup (zn n) (B ∩ Hn n)) atTop ∧
      limsup (fun n => linfSetSup (zn n) (B ∩ Hn n)) atTop
        ≤ linfSetSup z (closure B ∩ H) := by
  classical
  let s : ℕ → EReal := fun n => linfSetSup (zn n) (B ∩ Hn n)
  have hlower : linfSetSup z (interior B ∩ H) ≤ liminf s atTop := by
    rw [Filter.le_liminf_iff]
    intro y hy
    rw [linfSetSup, lt_iSup_iff] at hy
    obtain ⟨h, hyh⟩ := hy
    obtain ⟨u, huHn, hu⟩ := hset.exists_recovery h.2.2
    have huB : ∀ᶠ n in atTop, u n ∈ B :=
      Filter.Eventually.mono (hu (isOpen_interior.mem_nhds h.2.1))
        (fun _ hn => interior_subset hn)
    have huK : ∀ᶠ n in atTop, u n ∈ K :=
      huB.mono (fun _ hn => hBK (subset_closure hn))
    let uK : ℕ → K := fun n =>
      if hn : u n ∈ K then ⟨u n, hn⟩ else h.1
    have huK_eq : (fun n => (uK n : D)) =ᶠ[atTop] u :=
      huK.mono (fun n hn => by simp [uK, hn])
    have huK_lim : Tendsto uK atTop (𝓝 h.1) :=
      tendsto_subtype_rng.mpr (Tendsto.congr' huK_eq.symm hu)
    have heval : Tendsto (fun n => zn n (uK n)) atTop (𝓝 (z h.1)) :=
      tendsto_linf_apply_of_tendsto_of_tendsto hz huK_lim hzcont
    have hevalE :
        Tendsto (fun n => (zn n (uK n) : EReal)) atTop (𝓝 (z h.1 : EReal)) :=
      EReal.tendsto_coe.mpr heval
    filter_upwards [hevalE (eventually_gt_nhds hyh), huB, huK_eq] with n hyn hnB hnu
    have hmem : (uK n : D) ∈ B ∩ Hn n := by
      constructor
      · simpa [hnu] using hnB
      · simpa [hnu] using huHn n
    exact hyn.trans_le <| by
      unfold s linfSetSup
      exact le_iSup (fun q : {q : K // (q : D) ∈ B ∩ Hn n} =>
        (zn n q.1 : EReal)) ⟨uK n, hmem⟩
  have hupper : limsup s atTop ≤ linfSetSup z (closure B ∩ H) := by
    rw [Filter.limsup_le_iff]
    intro y hy
    obtain ⟨b, hb, hby⟩ := EReal.lt_iff_exists_real_btwn.mp hy
    have hevalBound :
        ∀ᶠ n in atTop, ∀ h : K, (h : D) ∈ B ∩ Hn n → zn n h ≤ b := by
      by_contra hnot
      have hfreq0 :
          ∃ᶠ n in atTop, ¬∀ h : K, (h : D) ∈ B ∩ Hn n → zn n h ≤ b :=
        Filter.not_eventually.mp hnot
      have hfreq :
          ∃ᶠ n in atTop, ∃ h : K, (h : D) ∈ B ∩ Hn n ∧ b < zn n h :=
        hfreq0.mono (fun _ hn => by
          obtain ⟨h, hn⟩ := not_forall.mp hn
          obtain ⟨hhmem, hhval⟩ := Classical.not_imp.mp hn
          exact ⟨h, hhmem, lt_of_not_ge hhval⟩)
      obtain ⟨φ, hφ, hbad⟩ := Filter.extraction_of_frequently_atTop hfreq
      choose x hx using hbad
      obtain ⟨x0, hx0, ψ, hψ, hxlim⟩ :=
        hB.tendsto_subseq (x := fun n => (x n : D))
          (fun n => subset_closure (hx n).1.1)
      have hxH : x0 ∈ H := hset.subsequence_limit_mem
          (hφ.comp hψ) (hn := fun n => (x (ψ n) : D))
          (fun n => by simpa [Function.comp_def] using (hx (ψ n)).1.2)
          (by simpa [Function.comp_def] using hxlim)
      let x0K : K := ⟨x0, hBK hx0⟩
      have hxlimK : Tendsto (fun n => x (ψ n)) atTop (𝓝 x0K) :=
        tendsto_subtype_rng.mpr (by simpa [x0K, Function.comp_def] using hxlim)
      have hzsub : Tendsto (fun n => zn (φ (ψ n))) atTop (𝓝 z) :=
        hz.comp (hφ.comp hψ).tendsto_atTop
      have heval :
          Tendsto (fun n => zn (φ (ψ n)) (x (ψ n))) atTop (𝓝 (z x0K)) :=
        tendsto_linf_apply_of_tendsto_of_tendsto hzsub hxlimK hzcont
      have hble : b ≤ z x0K :=
        ge_of_tendsto heval (Eventually.of_forall fun n => le_of_lt (hx (ψ n)).2)
      have hzle : (z x0K : EReal) ≤ linfSetSup z (closure B ∩ H) := by
        unfold linfSetSup
        exact le_iSup (fun q : {q : K // (q : D) ∈ closure B ∩ H} =>
          (z q.1 : EReal)) ⟨x0K, hx0, hxH⟩
      exact (not_le_of_gt hb) ((EReal.coe_le_coe_iff.mpr hble).trans hzle)
    filter_upwards [hevalBound] with n hn
    have hsle : s n ≤ (b : EReal) := by
      unfold s linfSetSup
      exact iSup_le fun h => EReal.coe_le_coe_iff.mpr (hn h.1 h.2)
    exact hsle.trans_lt hby
  exact ⟨hlower, Filter.liminf_le_limsup, hupper⟩

end AsymptoticStatistics.ForMathlib
