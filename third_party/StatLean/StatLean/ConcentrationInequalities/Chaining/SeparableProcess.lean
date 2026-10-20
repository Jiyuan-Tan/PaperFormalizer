module
public import StatLean.ConcentrationInequalities.Chaining.DyadicNets
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Metrizable.Basic

@[expose] public section

/-!
# Separable versions of a real-valued process

The version-selection layer for genuine `sup_{t ∈ T}` chaining statements
over an uncountable index set: `IsSeparableProcess X T μ` says some countable
`T₀ ⊆ T` a.s. captures every value `X t ω`, `t ∈ T`, in the closure of the
`T₀`-values. Constructors: any countable `T` (sure, not just a.e.), and a.e.
sample-path continuity on a topologically separable index set (with
`isSeparable_of_coveringNumber_ne_top` supplying separability from the
Dudley covering package). Transport lemmas convert the a.s. value-closure
into a.e. equalities of composed suprema over `T` and over the countable
witness — in `ℝ≥0∞` (single and pair form, lower-semicontinuous shapes) and
in `ℝ` (nonnegative continuous shapes) — plus the pointwise threshold bridge
`exists_lt_comp_of_mem_closure` used by the tail forms.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, p. 227 footnote ("we are assuming T is finite to
avoid measurability issues; the general case typically follows by
approximation") and Remark 7.2.1 — this file is the approximation, in the
form standard in the rigorous chaining literature (separable versions).

**Proof formalization notes.** The definition is **value-space** (Doob-style)
separability: no metric on the index type is needed, and it is weaker (hence
the theorems are stronger) than metric-dense-subset separability. It is a
genuine USER-INPUT: modifying each `X t` on a `t`-dependent null set
preserves `SubGaussianIncrements` (a per-pair a.e. condition) but can make
`sup_{t∈T} X t ≡ ∞` for uncountable `T`, so the hypothesis is
mathematically REQUIRED for any uncountable-sup statement and cannot be
derived. Edge behavior: for `T = ∅` the witness `T₀ = ∅` works vacuously;
for `T ≠ ∅` every witness is automatically nonempty (`closure ∅ = ∅`). The
`ℝ≥0∞` transport is stated for lower-semicontinuous shapes so that the pair
form can feed the countable sup of continuous shapes back through it; the
real transport carries a nonnegativity hypothesis `hφ0` — WITHOUT it the
equality is false at `T = Set.univ` with all-negative values (the `T`-side
supremum has no `Real.sSup ∅ = 0` junk branch while the `C`-side does).
Named-sorry fallback of this work item: the real transport
`biSup_real_comp_eq_of_forall_mem_closure`.

**Bibliographic comments.** Separable versions go back to J. L. Doob,
*Stochastic Processes*, Wiley 1953, Ch. II; the modern treatment for
chaining is R. van Handel, *Probability in High Dimension* (APC 550 notes,
Princeton, 2016), §5.3, and M. Talagrand, *Upper and Lower Bounds for
Stochastic Processes*, Springer 2014, §2.2.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Separable version of a real-valued process** (value-space Doob
separability; HDP p. 227 footnote, van Handel APM §5.3): some countable
`T₀ ⊆ T` a.s. captures every value `X t ω`, `t ∈ T`, in the closure of the
`T₀`-values.

This is the version-selection hypothesis that uncountable-`sup` chaining
statements mathematically REQUIRE: modifying each `X t` on a `t`-dependent
null set preserves `SubGaussianIncrements` while destroying this property
(and inflating the supremum arbitrarily). Edge behavior: `T = ∅` is
separable with witness `∅`; for `T ≠ ∅` every witness `T₀` is automatically
nonempty since `closure ∅ = ∅`. -/
def IsSeparableProcess {E : Type*} (X : E → Ω → ℝ) (T : Set E)
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∃ T₀ : Set E, T₀ ⊆ T ∧ T₀.Countable ∧
    ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω ∈ closure ((fun s => X s ω) '' T₀)

/-- A countable index set is its own separability witness (surely, not just
a.e.): each value lies in its own closure. -/
theorem IsSeparableProcess.of_countable {E : Type*} {X : E → Ω → ℝ}
    {T : Set E} {μ : Measure Ω}
    -- LEAN-ONLY: countable index set per the sup policy
    (hcnt : T.Countable) :
    IsSeparableProcess X T μ := by
  refine ⟨T, subset_rfl, hcnt, Filter.Eventually.of_forall fun ω t ht => ?_⟩
  exact subset_closure (Set.mem_image_of_mem _ ht)

/-- Finite covering numbers at all positive radii make the index set
topologically separable: the covering package is exactly total boundedness
(`totallyBounded_of_coveringNumber_ne_top`), and totally bounded sets in a
(pseudo)metric space are separable. -/
theorem isSeparable_of_coveringNumber_ne_top {E : Type*} [PseudoMetricSpace E]
    {T : Set E}
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤) :
    TopologicalSpace.IsSeparable T :=
  (totallyBounded_of_coveringNumber_ne_top hcov).isSeparable

/-- **Sample-path continuity criterion** (the standard sufficient condition
for a separable version; van Handel APM §5.3): a.e. path continuity on a
topologically separable index set yields `IsSeparableProcess`, through a
countable dense subset `T₀ ⊆ T` and `ContinuousWithinAt.mem_closure_image`.
Combine with `isSeparable_of_coveringNumber_ne_top` in the Dudley setting. -/
theorem IsSeparableProcess.of_continuousOn {E : Type*} [PseudoMetricSpace E]
    {X : E → Ω → ℝ} {T : Set E} {μ : Measure Ω}
    -- USER-INPUT: topologically separable index set; HDP p.227 footnote
    -- (supplied by `isSeparable_of_coveringNumber_ne_top` under `hcov`)
    (hT : TopologicalSpace.IsSeparable T)
    -- USER-INPUT: a.e. sample-path continuity on T; van Handel APM §5.3
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) T) :
    IsSeparableProcess X T μ := by
  obtain ⟨T₀, hT₀sub, hT₀cnt, hTcl⟩ := hT.exists_countable_dense_subset
  refine ⟨T₀, hT₀sub, hT₀cnt, ?_⟩
  filter_upwards [hcont] with ω hω t htT
  exact ((hω t htT).mono hT₀sub).mem_closure_image (hTcl htT)

/-- Transport of an `ℝ≥0∞`-valued composed supremum through value-space
closure: if every `T`-value is a closure point of the `C`-values, the `⨆` of
any lower-semicontinuous image over `T` equals that over `C`. Junk-free:
`ℝ≥0∞` is a complete lattice, and the `C = ∅` corner forces `T = ∅`
(`closure ∅ = ∅`). Lower semicontinuity (not continuity) so the pair
transport can route its inner countable sup back through this lemma. -/
lemma biSup_ennreal_comp_eq_of_forall_mem_closure {α : Type*} {T C : Set α}
    -- LEAN-ONLY: the approximating subfamily
    (hsub : C ⊆ T)
    {x : α → ℝ}
    -- LEAN-ONLY: value-space density (the separability payload at fixed ω)
    (hx : ∀ t ∈ T, x t ∈ closure (x '' C))
    {φ : ℝ → ℝ≥0∞}
    -- LEAN-ONLY: lower-semicontinuous integrand shape
    (hφ : LowerSemicontinuous φ) :
    ⨆ t ∈ T, φ (x t) = ⨆ t ∈ C, φ (x t) := by
  refine le_antisymm ?_ (biSup_mono hsub)
  refine iSup_le fun t => iSup_le fun ht => ?_
  refine le_of_forall_lt fun y hy => ?_
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp (hφ (x t) y hy)
  obtain ⟨w, hwU, s, hsC, rfl⟩ := _root_.mem_closure_iff.mp (hx t ht) U hUopen hUmem
  exact lt_of_lt_of_le (hUsub hwU) (le_biSup (fun s => φ (x s)) hsC)

/-- Real twin of `biSup_ennreal_comp_eq_of_forall_mem_closure`, for
NONNEGATIVE continuous shapes. The sign hypothesis is essential: without it
the equality fails at `T = Set.univ` with all-negative values (the `T`-side
supremum has no `Real.sSup ∅ = 0` junk branch while the `C`-side does). In
the bounded case both sides are honest and equal by density; in the
unbounded case both junk to the same `0` (the `C`-values are cofinal in the
`T`-values via closure). -/
lemma biSup_real_comp_eq_of_forall_mem_closure {α : Type*} {T C : Set α}
    -- LEAN-ONLY: the approximating subfamily
    (hsub : C ⊆ T)
    {x : α → ℝ}
    -- LEAN-ONLY: value-space density (the separability payload at fixed ω)
    (hx : ∀ t ∈ T, x t ∈ closure (x '' C))
    {φ : ℝ → ℝ}
    -- LEAN-ONLY: continuous integrand shape
    (hφ : Continuous φ)
    -- LEAN-ONLY: nonnegative shape (junk alignment across binder ranges;
    -- false without it at `T = Set.univ`)
    (hφ0 : ∀ v, 0 ≤ φ v) :
    ⨆ t ∈ T, φ (x t) = ⨆ t ∈ C, φ (x t) := by
  classical
  -- Pointwise evaluation of the `Prop`-indexed inner suprema (junk value `0`).
  have hTval : ∀ t, (⨆ (_ : t ∈ T), φ (x t)) = if t ∈ T then φ (x t) else 0 := by
    intro t
    by_cases ht : t ∈ T
    · rw [if_pos ht]; exact ciSup_pos ht
    · rw [if_neg ht]; simp [ht]
  have hCval : ∀ t, (⨆ (_ : t ∈ C), φ (x t)) = if t ∈ C then φ (x t) else 0 := by
    intro t
    by_cases ht : t ∈ C
    · rw [if_pos ht]; exact ciSup_pos ht
    · rw [if_neg ht]; simp [ht]
  have hTnn : ∀ t, 0 ≤ (⨆ (_ : t ∈ T), φ (x t)) := by
    intro t; rw [hTval]; split
    · exact hφ0 _
    · exact le_rfl
  have hCnn : ∀ t, 0 ≤ (⨆ (_ : t ∈ C), φ (x t)) := by
    intro t; rw [hCval]; split
    · exact hφ0 _
    · exact le_rfl
  have hCT : ∀ t, (⨆ (_ : t ∈ C), φ (x t)) ≤ (⨆ (_ : t ∈ T), φ (x t)) := by
    intro t
    by_cases ht : t ∈ C
    · rw [hCval, hTval, if_pos ht, if_pos (hsub ht)]
    · rw [hCval, if_neg ht]; exact hTnn t
  -- Any nonnegative bound on the `C`-values bounds the `T`-values: `{v | φ v ≤ M}`
  -- is closed and contains `x '' C`, hence its closure.
  have key : ∀ M : ℝ, (∀ s ∈ C, φ (x s) ≤ M) → ∀ t ∈ T, φ (x t) ≤ M := by
    intro M hCM t ht
    have hcl : IsClosed {v : ℝ | φ v ≤ M} := isClosed_le hφ continuous_const
    have himg : x '' C ⊆ {v : ℝ | φ v ≤ M} := by
      rintro _ ⟨s, hs, rfl⟩; exact hCM s hs
    exact hcl.closure_subset_iff.mpr himg (hx t ht)
  by_cases hb : BddAbove (Set.range fun t => ⨆ (_ : t ∈ C), φ (x t))
  · -- Bounded case: both suprema are honest, and the density transfer closes it.
    have hbT : BddAbove (Set.range fun t => ⨆ (_ : t ∈ T), φ (x t)) := by
      obtain ⟨M, hM⟩ := hb
      refine ⟨max M 0, ?_⟩
      rintro _ ⟨t, rfl⟩
      have hCM : ∀ s ∈ C, φ (x s) ≤ max M 0 := by
        intro s hs
        have hs' : (⨆ (_ : s ∈ C), φ (x s)) ≤ M := hM (Set.mem_range_self s)
        rw [hCval, if_pos hs] at hs'
        exact hs'.trans (le_max_left _ _)
      change (⨆ (_ : t ∈ T), φ (x t)) ≤ max M 0
      rw [hTval]
      by_cases ht : t ∈ T
      · rw [if_pos ht]; exact key _ hCM t ht
      · rw [if_neg ht]; exact le_max_right _ _
    refine le_antisymm ?_ ?_
    · refine Real.iSup_le (fun t => ?_) (Real.iSup_nonneg hCnn)
      change (⨆ (_ : t ∈ T), φ (x t)) ≤ ⨆ t, ⨆ (_ : t ∈ C), φ (x t)
      rw [hTval]
      by_cases ht : t ∈ T
      · rw [if_pos ht]
        refine key _ (fun s hs => ?_) t ht
        have hs' : (⨆ (_ : s ∈ C), φ (x s)) ≤ ⨆ t, ⨆ (_ : t ∈ C), φ (x t) := le_ciSup hb s
        rwa [hCval, if_pos hs] at hs'
      · rw [if_neg ht]; exact Real.iSup_nonneg hCnn
    · exact Real.iSup_le (fun t => (hCT t).trans (le_ciSup hbT t)) (Real.iSup_nonneg hTnn)
  · -- Unbounded case: the `T`-family is unbounded too, so both sides junk to `0`.
    have hbT : ¬ BddAbove (Set.range fun t => ⨆ (_ : t ∈ T), φ (x t)) := by
      rintro ⟨M, hM⟩
      exact hb ⟨M, by rintro _ ⟨t, rfl⟩; exact (hCT t).trans (hM (Set.mem_range_self t))⟩
    rw [Real.iSup_of_not_bddAbove hbT, Real.iSup_of_not_bddAbove hb]

/-- Pair transport through value-space closure: the nested `ℝ≥0∞` double
supremum of a separately lower-semicontinuous two-variable shape passes from
`T × T` to `C × C`. Proof shape: the single-variable transport in `s` for
each fixed `t`, then in `t` against the countable-sup shape
`v ↦ ⨆ s ∈ C, φ v (x s)`, which is lower semicontinuous as a supremum of
lower-semicontinuous shapes. -/
lemma biSup_pair_ennreal_comp_eq_of_forall_mem_closure {α : Type*}
    {T C : Set α}
    -- LEAN-ONLY: the approximating subfamily
    (hsub : C ⊆ T)
    {x : α → ℝ}
    -- LEAN-ONLY: value-space density (the separability payload at fixed ω)
    (hx : ∀ t ∈ T, x t ∈ closure (x '' C))
    {φ : ℝ → ℝ → ℝ≥0∞}
    -- LEAN-ONLY: lower semicontinuity in the first variable
    (hφ₁ : ∀ w, LowerSemicontinuous fun v => φ v w)
    -- LEAN-ONLY: lower semicontinuity in the second variable
    (hφ₂ : ∀ v, LowerSemicontinuous (φ v)) :
    ⨆ t ∈ T, ⨆ s ∈ T, φ (x t) (x s) = ⨆ t ∈ C, ⨆ s ∈ C, φ (x t) (x s) := by
  have hinner : ∀ v : ℝ, ⨆ s ∈ T, φ v (x s) = ⨆ s ∈ C, φ v (x s) := fun v =>
    biSup_ennreal_comp_eq_of_forall_mem_closure hsub hx (hφ₂ v)
  have houter : LowerSemicontinuous fun v => ⨆ s ∈ C, φ v (x s) :=
    lowerSemicontinuous_biSup fun s _ => hφ₁ (x s)
  calc ⨆ t ∈ T, ⨆ s ∈ T, φ (x t) (x s)
      = ⨆ t ∈ T, ⨆ s ∈ C, φ (x t) (x s) := by simp only [hinner]
    _ = ⨆ t ∈ C, ⨆ s ∈ C, φ (x t) (x s) :=
        biSup_ennreal_comp_eq_of_forall_mem_closure hsub hx houter

/-- Strict thresholds survive closure approximation: a closure point whose
continuous image exceeds `c` has an approximant in the set whose image does.
(The pointwise engine of the tail-form transports — no supremum involved.) -/
lemma exists_lt_comp_of_mem_closure {A : Set ℝ} {v : ℝ}
    -- LEAN-ONLY: the closure point being approximated
    (hv : v ∈ closure A)
    {φ : ℝ → ℝ}
    -- LEAN-ONLY: continuous threshold shape
    (hφ : Continuous φ)
    {c : ℝ}
    -- LEAN-ONLY: the strict threshold at the closure point
    (hlt : c < φ v) :
    ∃ a ∈ A, c < φ a := by
  obtain ⟨a, haU, haA⟩ :=
    _root_.mem_closure_iff.mp hv (φ ⁻¹' Set.Ioi c) (isOpen_Ioi.preimage hφ) hlt
  exact ⟨a, haA, haU⟩

end StatLean.ConcentrationInequalities
