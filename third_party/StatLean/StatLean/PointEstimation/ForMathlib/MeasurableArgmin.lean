module
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-!
# A measurable selection of minimizers of a parametrized convex scan

Given a family `f : Ω → ℝ → ℝ≥0∞` of convex, continuous, coercive functions of a real scan
variable, depending measurably on a parameter `ω`, there is a **measurable** map
`u : Ω → ℝ` picking a minimizer of `f ω` for every `ω`.

* `iInf_eq_iInf_rat_of_continuous` — a continuous `ℝ≥0∞`-valued function has the same
  infimum over `ℝ` as over `ℚ`;
* `exists_forall_le_of_continuous_of_coercive` — a continuous coercive function attains its
  infimum;
* `exists_measurable_argmin` — the measurable selection (continuous form);
* `exists_measurable_argmin_of_convex_of_finite` / `exists_measurable_argmin_of_convex` — the
  **convex** strengthening: continuity is replaced by lower semicontinuity, at the cost of a
  single finiteness point `f ω 0 < ⊤` (everywhere, resp. almost everywhere). This is what the
  conditional-risk consumers use, since an unbounded convex loss makes the objective jump to
  `∞` and the plain-continuity form does not apply.

This is the brick that makes "minimize the conditional risk pointwise, then read the answer
off as an estimator" legitimate: the pointwise minimizer must be a *measurable* function of
the conditioning variable before it can be called an estimator at all.

**On the lower-semicontinuous strengthening.** A *naive* weakening of `hcont` to plain
`LowerSemicontinuous (f ω)` is FALSE for the rational-relaxed-sublevel construction: a convex
lsc objective can be finite at a single *irrational* point (its finiteness domain a
singleton), where the minimum is invisible to the rationals, so `⨅ q : ℚ, f ω q ≠ ⨅ v, f ω v`
and measurability of `M` breaks. Convexity together with **one finiteness point** `f ω 0 < ⊤`
rules out exactly this pathology — the domain is then a nondegenerate (or singleton-at-`0`)
interval containing `0`, on whose rationals the infimum is approached from the `0`-side by the
convexity inequality (`convex_iInf_le_aux`), no continuity required. The consumers get their
finiteness point from the finite-risk hypothesis via disintegration.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.1 (First
Examples), supporting material for Theorem 1.10 and Corollary 1.11: a measurable selection of
minimizers of a parametrized convex scan. (`TPE2 §3.1 Thm 1.10, Cor 1.11`.)

**Proof formalization notes.**
* **Continuity, not lower semicontinuity — deliberate.** The natural hypothesis for a
  measurable-argmin theorem is lower semicontinuity in the scan variable, and the statement
  below does hold in that generality. Continuity is assumed instead because it keeps the
  selection *elementarily* provable: the relaxed sublevel sets can be tested on rationals
  (see the next item), whereas the lower semicontinuous version routes through a genuine
  selection theorem. Weakening `hcont` to `LowerSemicontinuous (f ω)` is a strengthening that
  can be made later without touching any call site.
* **Rational-relaxed-sublevel selection.** Take `u ω` to be the *leftmost* minimizer,
  `u ω = sInf {v | f ω v = ⨅ w, f ω w}` (nonempty by
  `exists_forall_le_of_continuous_of_coercive`, closed by continuity, bounded below by
  coercivity, and an interval by convexity). Measurability follows from
  `u ω < r ↔ ∃ q : ℚ, (q : ℝ) < r ∧ ⨅ v ∈ Set.Iic (q : ℝ), f ω v = ⨅ v, f ω v`, where each
  relativized infimum is again a countable infimum over rationals by the density argument of
  `iInf_eq_iInf_rat_of_continuous`. Every set on the right is measurable because `f` is
  jointly measurable, and the union is countable.
* `iInf_eq_iInf_rat_of_continuous` is stated globally over `ℝ`; the selection proof uses the
  same density argument relativized to `Set.Iic q`, which is the special case of
  `⨅ x ∈ closure s, g x = ⨅ x ∈ s, g x` for continuous `g`.
* **Convexity is `ConvexOn ℝ≥0 Set.univ`.** For an `ℝ≥0∞`-valued function this is the only
  convexity predicate that typechecks at this pin: `ConvexOn 𝕜` needs `SMul 𝕜 ℝ≥0∞`, and
  `ℝ≥0∞` is a module over `ℝ≥0` but not over `ℝ`. On `[0, ∞]`-valued functions of a real
  variable the `ℝ≥0`-coefficient definition is the usual midpoint-convexity condition, so
  nothing is lost.
* **Coercivity is `Tendsto (f ω) (cocompact ℝ) (𝓝 ⊤)`, not `… atTop`.** In `ℝ≥0∞`,
  `Filter.atTop = pure ⊤` (`OrderTop.atTop_eq`), so the `atTop` phrasing would read "`f ω`
  equals `⊤` off a compact set" — true but useless. The `𝓝 ⊤` form is the intended "`f ω`
  blows up at infinity"; for `ℝ`-valued scans (see `ForMathlib/ConvexMinimizers.lean`) the
  two coincide and `atTop` is used there.
* **Attainment is derived, never hypothesized.** The conclusion asserts
  `f ω (u ω) = ⨅ v, f ω v`, i.e. that the infimum *is attained at the selected point*; it is
  forced by continuity plus coercivity and so must not appear as a hypothesis.

**Bibliographic comments.** Measurable selections of set-valued maps are due to
K. Kuratowski and C. Ryll-Nardzewski ("A general theorem on selectors," *Bull. Acad. Polon.
Sci. Sér. Sci. Math. Astronom. Phys.* **13** (1965), 397–403); the special case of an
argmin selection for a Carathéodory integrand is the standard application of that theorem,
here replaced by the elementary leftmost-minimizer construction.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

/-- The infimum of a continuous `ℝ≥0∞`-valued function over `ℝ` is already attained as an
infimum over the rationals. -/
theorem iInf_eq_iInf_rat_of_continuous
    -- USER-INPUT: the function to be minimized; free choice
    {g : ℝ → ℝ≥0∞}
    -- USER-INPUT: continuity; the density argument fails for a merely measurable `g`
    (hg : Continuous g) :
    (⨅ x : ℝ, g x) = ⨅ q : ℚ, g (q : ℝ) := by
  refine le_antisymm (le_iInf fun q => iInf_le _ _) (le_iInf fun x => ?_)
  haveI hnb : (𝓝[Set.range ((↑) : ℚ → ℝ)] x).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (Rat.denseRange_cast x)
  have htend : Tendsto g (𝓝[Set.range ((↑) : ℚ → ℝ)] x) (𝓝 (g x)) :=
    (hg.tendsto x).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨q, rfl⟩ := hy
  exact iInf_le _ q

/-- A continuous coercive `ℝ≥0∞`-valued function on `ℝ` attains its infimum. -/
theorem exists_forall_le_of_continuous_of_coercive
    -- USER-INPUT: the function to be minimized; free choice
    {g : ℝ → ℝ≥0∞}
    -- USER-INPUT: continuity; closedness of sublevel sets
    (hg : Continuous g)
    -- USER-INPUT: coercivity; compactness of a nontrivial sublevel set. See the header for
    -- why the target filter is `𝓝 ⊤` rather than `atTop`.
    (hcoer : Tendsto g (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) :
    ∃ x : ℝ, ∀ y : ℝ, g x ≤ g y := by
  set s : ℝ≥0∞ := ⨅ y, g y with hs
  by_cases hstop : s = ⊤
  · exact ⟨0, fun y => by rw [iInf_eq_top.mp hstop y]; exact le_top⟩
  · -- choose a finite level `c` strictly above the infimum
    have hslt : s < ⊤ := lt_top_iff_ne_top.mpr hstop
    set c : ℝ≥0∞ := s + 1 with hc
    have hctop : c < ⊤ := by
      rw [hc]; exact ENNReal.add_lt_top.mpr ⟨hslt, ENNReal.one_lt_top⟩
    have hsc : s < c := by rw [hc]; exact ENNReal.lt_add_right hstop one_ne_zero
    obtain ⟨y₀, hy₀⟩ := iInf_lt_iff.mp hsc
    -- the sublevel set `{y | g y ≤ c}` is compact and nonempty
    have hmem : g ⁻¹' Set.Ioi c ∈ cocompact ℝ := hcoer (Ioi_mem_nhds hctop)
    obtain ⟨t, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hclosed : IsClosed {y | g y ≤ c} := isClosed_Iic.preimage hg
    have hsub : {y | g y ≤ c} ⊆ t := by
      intro y hy
      by_contra hyt
      exact absurd (ht_sub hyt) (by simpa using hy)
    have hcompact : IsCompact {y | g y ≤ c} := ht_comp.of_isClosed_subset hclosed hsub
    have hne : {y | g y ≤ c}.Nonempty := ⟨y₀, hy₀.le⟩
    obtain ⟨x, hx_mem, hx_min⟩ := hcompact.exists_isMinOn hne hg.continuousOn
    refine ⟨x, fun y => ?_⟩
    by_cases hy : g y ≤ c
    · exact isMinOn_iff.mp hx_min y hy
    · exact le_trans hx_mem (not_le.mp hy).le

/-- The infimum over `Iic q` equals the infimum of `v ↦ g (min v q)` over all of `ℝ`. -/
private theorem iInf_Iic_eq_iInf_comp_min (g : ℝ → ℝ≥0∞) (q : ℝ) :
    (⨅ v ∈ Set.Iic q, g v) = ⨅ v : ℝ, g (min v q) := by
  apply le_antisymm
  · exact le_iInf fun v => iInf₂_le (min v q) (min_le_right v q)
  · refine le_iInf₂ fun w hw => ?_
    calc ⨅ v : ℝ, g (min v q) ≤ g (min w q) := iInf_le _ w
      _ = g w := by rw [min_eq_left hw]

/-- A continuous coercive function attains its infimum over a lower half-line `Iic q`. -/
private theorem exists_argmin_Iic {g : ℝ → ℝ≥0∞} (hg : Continuous g)
    (hcoer : Tendsto g (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) (q : ℝ) :
    ∃ w ≤ q, g w = ⨅ v ∈ Set.Iic q, g v := by
  set mq : ℝ≥0∞ := ⨅ v ∈ Set.Iic q, g v with hmq
  by_cases hmqtop : mq = ⊤
  · refine ⟨q, le_refl q, ?_⟩
    have h : mq ≤ g q := by
      rw [hmq]; exact iInf₂_le q (Set.mem_Iic.mpr le_rfl)
    rw [hmqtop] at h ⊢
    exact top_le_iff.mp h
  · have hmqlt : mq < ⊤ := lt_top_iff_ne_top.mpr hmqtop
    set c : ℝ≥0∞ := mq + 1 with hc
    have hctop : c < ⊤ := by
      rw [hc]; exact ENNReal.add_lt_top.mpr ⟨hmqlt, ENNReal.one_lt_top⟩
    have hmc : mq < c := by rw [hc]; exact ENNReal.lt_add_right hmqtop one_ne_zero
    obtain ⟨v₀, hv₀q, hv₀c⟩ : ∃ v₀ ≤ q, g v₀ < c := by
      have h : (⨅ v ∈ Set.Iic q, g v) < c := hmc
      rw [iInf_lt_iff] at h
      obtain ⟨v, hv⟩ := h
      rw [iInf_lt_iff] at hv
      obtain ⟨hvq, hvc⟩ := hv
      exact ⟨v, hvq, hvc⟩
    have hmem : g ⁻¹' Set.Ioi c ∈ cocompact ℝ := hcoer (Ioi_mem_nhds hctop)
    obtain ⟨t, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hclosed : IsClosed (Set.Iic q ∩ {v | g v ≤ c}) :=
      isClosed_Iic.inter (isClosed_Iic.preimage hg)
    have hsub : (Set.Iic q ∩ {v | g v ≤ c}) ⊆ t := by
      intro v hv
      by_contra hvt
      exact absurd (ht_sub hvt) (by simpa using hv.2)
    have hcompact : IsCompact (Set.Iic q ∩ {v | g v ≤ c}) :=
      ht_comp.of_isClosed_subset hclosed hsub
    have hne : (Set.Iic q ∩ {v | g v ≤ c}).Nonempty := ⟨v₀, hv₀q, hv₀c.le⟩
    obtain ⟨w, hw_mem, hw_min⟩ := hcompact.exists_isMinOn hne hg.continuousOn
    refine ⟨w, hw_mem.1, ?_⟩
    rw [hmq]
    refine le_antisymm ?_ (iInf₂_le w hw_mem.1)
    refine le_iInf₂ fun v hv => ?_
    by_cases hvc : g v ≤ c
    · exact isMinOn_iff.mp hw_min v ⟨hv, hvc⟩
    · exact le_trans hw_mem.2 (not_le.mp hvc).le

/-- **Measurable argmin.** A jointly measurable family of convex, continuous, coercive
functions of a real scan variable admits a measurable minimizer selection. -/
theorem exists_measurable_argmin {Ω : Type*} [MeasurableSpace Ω]
    -- USER-INPUT: the parametrized objective (a conditional risk in applications)
    {f : Ω → ℝ → ℝ≥0∞}
    -- USER-INPUT: joint measurability; without it no selection can be measurable
    (hf : Measurable (Function.uncurry f))
    -- USER-INPUT: continuity in the scan variable; see the header on the LSC strengthening
    (hcont : ∀ ω, Continuous (f ω))
    -- USER-INPUT: convexity in the scan variable; makes the minimizer set an interval
    (hconv : ∀ ω, ConvexOn ℝ≥0 Set.univ (f ω))
    -- USER-INPUT: coercivity in the scan variable; forces attainment
    (hcoer : ∀ ω, Tendsto (f ω) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) :
    ∃ u : Ω → ℝ, Measurable u ∧ ∀ ω, f ω (u ω) = ⨅ v : ℝ, f ω v := by
  classical
  -- pointwise minimum value; measurable through a rational infimum
  have hfq : ∀ q : ℚ, Measurable (fun ω => f ω (q : ℝ)) := fun q =>
    hf.comp (measurable_id.prodMk measurable_const)
  set M : Ω → ℝ≥0∞ := fun ω => ⨅ v : ℝ, f ω v with hMdef
  have hM_meas : Measurable M := by
    have hEq : M = fun ω => ⨅ q : ℚ, f ω (q : ℝ) := by
      funext ω; exact iInf_eq_iInf_rat_of_continuous (hcont ω)
    rw [hEq]; exact Measurable.iInf hfq
  -- restricted minimum value over `Iic q`; measurable through the `min`-trick
  have hLq_meas : ∀ q : ℚ, Measurable (fun ω => ⨅ v ∈ Set.Iic (q : ℝ), f ω v) := by
    intro q
    have hEq : (fun ω => ⨅ v ∈ Set.Iic (q : ℝ), f ω v)
        = fun ω => ⨅ p : ℚ, f ω (min (p : ℝ) (q : ℝ)) := by
      funext ω
      rw [iInf_Iic_eq_iInf_comp_min (f ω) (q : ℝ)]
      exact iInf_eq_iInf_rat_of_continuous
        ((hcont ω).comp (continuous_id.min continuous_const))
    rw [hEq]
    exact Measurable.iInf fun p => hf.comp (measurable_id.prodMk measurable_const)
  -- the minimizer set and its leftmost point
  set S : Ω → Set ℝ := fun ω => {v | f ω v = M ω} with hSdef
  set u : Ω → ℝ := fun ω => sInf (S ω) with hudef
  have hclosedS : ∀ ω, IsClosed (S ω) := fun ω =>
    isClosed_singleton.preimage (hcont ω)
  have hneS : ∀ ω, (S ω).Nonempty := by
    intro ω
    obtain ⟨x, hx⟩ := exists_forall_le_of_continuous_of_coercive (hcont ω) (hcoer ω)
    exact ⟨x, le_antisymm (le_iInf hx) (iInf_le _ x)⟩
  have hbddS : ∀ ω, M ω < ⊤ → BddBelow (S ω) := by
    intro ω hlt
    have hmem : f ω ⁻¹' Set.Ioi (M ω) ∈ cocompact ℝ := (hcoer ω) (Ioi_mem_nhds hlt)
    obtain ⟨t, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hSsub : S ω ⊆ t := by
      intro v hv
      by_contra hvt
      have hlt2 : M ω < f ω v := ht_sub hvt
      rw [show f ω v = M ω from hv] at hlt2
      exact lt_irrefl _ hlt2
    exact ht_comp.bddBelow.mono hSsub
  -- attainment
  have hattain : ∀ ω, f ω (u ω) = M ω := by
    intro ω
    by_cases hMtop : M ω = ⊤
    · have h1 : M ω ≤ f ω (u ω) := iInf_le _ (u ω)
      rw [hMtop] at h1 ⊢
      exact top_le_iff.mp h1
    · have hlt : M ω < ⊤ := lt_top_iff_ne_top.mpr hMtop
      exact (hclosedS ω).csInf_mem (hneS ω) (hbddS ω hlt)
  -- leftmost-point characterisation of `{u ≤ q}`
  have hMle_biInf : ∀ ω (q : ℚ), M ω ≤ ⨅ v ∈ Set.Iic (q : ℝ), f ω v := fun ω q =>
    le_iInf₂ fun v _ => iInf_le _ v
  have hchar : ∀ ω (q : ℚ), u ω ≤ (q : ℝ) ↔
      (M ω = ⊤ ∧ (0 : ℝ) ≤ (q : ℝ)) ∨
      (M ω < ⊤ ∧ (⨅ v ∈ Set.Iic (q : ℝ), f ω v) = M ω) := by
    intro ω q
    by_cases hMtop : M ω = ⊤
    · -- here every point is a minimiser and `u ω = 0`
      have hSuniv : S ω = Set.univ := by
        ext v
        refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
        show f ω v = M ω
        exact le_antisymm (by rw [hMtop]; exact le_top) (iInf_le _ v)
      have hu0 : u ω = 0 := by
        show sInf (S ω) = 0
        rw [hSuniv]
        exact Real.sInf_of_not_bddBelow
          (not_bddBelow_iff.mpr fun x => ⟨x - 1, Set.mem_univ _, by linarith⟩)
      rw [hu0]
      constructor
      · intro h; exact Or.inl ⟨hMtop, h⟩
      · rintro (⟨_, h⟩ | ⟨hlt, _⟩)
        · exact h
        · exact absurd hMtop (ne_of_lt hlt)
    · have hlt : M ω < ⊤ := lt_top_iff_ne_top.mpr hMtop
      have hmem : u ω ∈ S ω := (hclosedS ω).csInf_mem (hneS ω) (hbddS ω hlt)
      constructor
      · intro h
        refine Or.inr ⟨hlt, le_antisymm ?_ (hMle_biInf ω q)⟩
        calc ⨅ v ∈ Set.Iic (q : ℝ), f ω v
            ≤ f ω (u ω) := iInf₂_le (u ω) (Set.mem_Iic.mpr h)
          _ = M ω := hmem
      · rintro (⟨hcontra, _⟩ | ⟨_, hbi⟩)
        · exact absurd hcontra hMtop
        · obtain ⟨w, hwq, hfw⟩ := exists_argmin_Iic (hcont ω) (hcoer ω) (q : ℝ)
          have hwS : w ∈ S ω := by show f ω w = M ω; rw [hfw, hbi]
          exact le_trans (csInf_le (hbddS ω hlt) hwS) hwq
  -- measurability of the selection
  refine ⟨u, ?_, fun ω => (hattain ω)⟩
  apply measurable_of_Iic
  intro r
  -- `{u ≤ r} = ⋂ (q:ℚ) (_ : r < q), {u ≤ q}`
  have hset : u ⁻¹' Set.Iic r
      = ⋂ (q : ℚ) (_ : r < (q : ℝ)), {ω | u ω ≤ (q : ℝ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h q _; exact le_trans h (le_of_lt ‹r < (q : ℝ)›)
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨q, hrq, hqu⟩ := exists_rat_btwn hlt
      exact absurd (h q hrq) (not_le.mpr hqu)
  rw [hset]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => ?_
  have hqset : {ω | u ω ≤ (q : ℝ)}
      = ((M ⁻¹' {⊤}) ∩ {ω | (0 : ℝ) ≤ (q : ℝ)}) ∪
        ((M ⁻¹' Set.Iio ⊤) ∩ {ω | (⨅ v ∈ Set.Iic (q : ℝ), f ω v) = M ω}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_Iio]
    rw [hchar ω q]
  rw [hqset]
  refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
  · exact hM_meas (measurableSet_singleton ⊤)
  · by_cases h : (0 : ℝ) ≤ (q : ℝ)
    · simp only [h, Set.setOf_true]; exact MeasurableSet.univ
    · simp only [h, Set.setOf_false]; exact MeasurableSet.empty
  · exact hM_meas measurableSet_Iio
  · exact measurableSet_eq_fun (hLq_meas q) hM_meas

/-!
### The convex (lower-semicontinuous) variant

The `Continuous` hypothesis of `exists_measurable_argmin` cannot simply be weakened to lower
semicontinuity: for a *convex* `ℝ≥0∞`-valued objective the finiteness domain can be a single
irrational point (e.g. `g w = ∫⁻ x, e^{(δ₀ x - w)²/2} dκ` for a heavy fibre `κ` is finite at
exactly one `w`), where the minimum is *not* approached along the rationals, so
`⨅ q : ℚ, g q ≠ ⨅ v, g v` and the rational-relaxed-sublevel measurability of
`exists_measurable_argmin` genuinely breaks. Convexity together with **one finiteness point**
`g 0 < ⊤` rules out exactly this pathology: the finiteness domain is then a nondegenerate (or
singleton-at-`0`) interval containing `0`, on whose rationals the infimum is approached from
the `0`-side by the convexity inequality — no continuity required. This is the exact
regularity the conditional-risk consumers can supply (their finiteness point comes from the
finite-risk hypothesis via disintegration). -/

/-- **Convexity replaces continuity (the density step).** For a convex `ℝ≥0∞`-valued `g`
finite at a base point `r`, any quantity `c` bounded by `g` on the rationals of the open
segment between `r` and `w` (and at `r` itself) is bounded by `g w`: rationals on that segment
approach `w`, and the convexity inequality against the finite `g r` passes to the limit. This
survives the jump to `⊤` at the boundary of the finiteness domain, where continuity fails. -/
private theorem convex_iInf_le_aux {g : ℝ → ℝ≥0∞} (hg : ConvexOn ℝ≥0 Set.univ g)
    {r w : ℝ} (hr : g r < ⊤) {c : ℝ≥0∞} (hcr : c ≤ g r)
    (hc : ∀ x ∈ Set.Ioo (min r w) (max r w), x ∈ Set.range ((↑) : ℚ → ℝ) → c ≤ g x) :
    c ≤ g w := by
  rcases eq_or_ne w r with rfl | hwr
  · exact hcr
  by_cases hgw : g w = ⊤
  · simp [hgw]
  have hwr' : w - r ≠ 0 := sub_ne_zero.mpr hwr
  set t : ℝ → ℝ := fun x => (x - r) / (w - r) with ht
  have hcont_t : Continuous t := (continuous_id.sub continuous_const).div_const _
  set B : ℝ → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (1 - t x) * g r + ENNReal.ofReal (t x) * g w with hB
  have htw : Filter.Tendsto t (𝓝 w) (𝓝 1) := by
    have hval : t w = 1 := by rw [ht]; simp [div_self hwr']
    rw [← hval]; exact hcont_t.tendsto w
  have hB_tendsto : Filter.Tendsto B (𝓝 w) (𝓝 (g w)) := by
    have h1 : Filter.Tendsto (fun x => ENNReal.ofReal (1 - t x)) (𝓝 w) (𝓝 0) := by
      have h0 : Filter.Tendsto (fun x => 1 - t x) (𝓝 w) (𝓝 (0 : ℝ)) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).sub htw
        simpa using this
      have := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h0
      simpa using! this
    have h2 : Filter.Tendsto (fun x => ENNReal.ofReal (t x)) (𝓝 w) (𝓝 1) := by
      have := (ENNReal.continuous_ofReal.tendsto (1 : ℝ)).comp htw
      simpa using! this
    have hL : Filter.Tendsto (fun x => ENNReal.ofReal (1 - t x) * g r) (𝓝 w) (𝓝 0) := by
      have := ENNReal.Tendsto.mul_const h1 (Or.inr hr.ne)
      simpa using this
    have hR : Filter.Tendsto (fun x => ENNReal.ofReal (t x) * g w) (𝓝 w) (𝓝 (g w)) := by
      have h := ENNReal.Tendsto.mul_const h2
        (show (1 : ℝ≥0∞) ≠ 0 ∨ g w ≠ ⊤ from Or.inl one_ne_zero)
      simpa using h
    have := hL.add hR
    simpa [hB] using this
  have hbound : ∀ x ∈ Set.Ioo (min r w) (max r w), g x ≤ B x := by
    intro x hx
    have e1t : 1 - t x = (w - x) / (w - r) := by rw [ht]; field_simp; ring
    have h0t : 0 ≤ t x := by
      rcases le_or_gt r w with hrw | hrw
      · rw [min_eq_left hrw, max_eq_right hrw] at hx
        exact div_nonneg (by linarith [hx.1]) (by linarith)
      · rw [min_eq_right hrw.le, max_eq_left hrw.le] at hx
        exact div_nonneg_of_nonpos (by linarith [hx.2]) (by linarith)
    have h1t : 0 ≤ 1 - t x := by
      rw [e1t]
      rcases le_or_gt r w with hrw | hrw
      · rw [min_eq_left hrw, max_eq_right hrw] at hx
        exact div_nonneg (by linarith [hx.2]) (by linarith)
      · rw [min_eq_right hrw.le, max_eq_left hrw.le] at hx
        exact div_nonneg_of_nonpos (by linarith [hx.1]) (by linarith)
    set α : ℝ≥0 := (1 - t x).toNNReal with hα
    set β : ℝ≥0 := (t x).toNNReal with hβ
    have hαβ : α + β = 1 := by
      have hsum : (1 - t x) + t x = 1 := by ring
      rw [hα, hβ, ← Real.toNNReal_add h1t h0t, hsum, Real.toNNReal_one]
    have hpt : α • r + β • w = x := by
      rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul, hα, hβ,
        Real.coe_toNNReal _ h1t, Real.coe_toNNReal _ h0t, ht]
      field_simp
      ring
    have hconv := hg.2 (Set.mem_univ r) (Set.mem_univ w) (zero_le (a := α)) (zero_le (a := β)) hαβ
    rw [hpt] at hconv
    refine hconv.trans_eq ?_
    simp only [hB, hα, hβ, ENNReal.smul_def, smul_eq_mul]
    rfl
  haveI hne : (𝓝[Set.Ioo (min r w) (max r w) ∩ Set.range ((↑) : ℚ → ℝ)] w).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    have hlt : min r w < max r w := min_lt_max.mpr (Ne.symm hwr)
    have hdense := Rat.denseRange_cast.open_subset_closure_inter
      (isOpen_Ioo (a := min r w) (b := max r w))
    have hsub : closure (Set.Ioo (min r w) (max r w))
        ⊆ closure (Set.Ioo (min r w) (max r w) ∩ Set.range ((↑) : ℚ → ℝ)) :=
      closure_minimal hdense isClosed_closure
    have hwIcc : w ∈ Set.Icc (min r w) (max r w) := ⟨min_le_right r w, le_max_right r w⟩
    rw [← closure_Ioo hlt.ne] at hwIcc
    exact hsub hwIcc
  refine ge_of_tendsto (hB_tendsto.mono_left (nhdsWithin_le_nhds
    (s := Set.Ioo (min r w) (max r w) ∩ Set.range ((↑) : ℚ → ℝ)))) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hc x hx.1 hx.2).trans (hbound x hx.1)

/-- The infimum of a convex `ℝ≥0∞`-valued function over `ℝ`, finite at `0`, is already
attained as an infimum over the rationals. The convex replacement for
`iInf_eq_iInf_rat_of_continuous`. -/
theorem iInf_eq_iInf_rat_of_convex {g : ℝ → ℝ≥0∞} (hg : ConvexOn ℝ≥0 Set.univ g)
    (h0 : g 0 < ⊤) :
    (⨅ x : ℝ, g x) = ⨅ q : ℚ, g (q : ℝ) := by
  refine le_antisymm (le_iInf fun q => iInf_le _ _) (le_iInf fun w => ?_)
  refine convex_iInf_le_aux hg (r := 0) (w := w) (by simpa using h0)
    (c := ⨅ q : ℚ, g (q : ℝ)) ?_ ?_
  · exact (iInf_le _ (0 : ℚ)).trans_eq (by norm_num)
  · intro x _ hx
    obtain ⟨q, rfl⟩ := hx
    exact iInf_le _ q

/-- A lower semicontinuous coercive `ℝ≥0∞`-valued function on `ℝ` attains its infimum. The
lower-semicontinuous replacement for `exists_forall_le_of_continuous_of_coercive`. -/
theorem exists_forall_le_of_lsc_of_coercive {g : ℝ → ℝ≥0∞}
    (hg : LowerSemicontinuous g)
    (hcoer : Tendsto g (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) :
    ∃ x : ℝ, ∀ y : ℝ, g x ≤ g y := by
  set s : ℝ≥0∞ := ⨅ y, g y with hs
  by_cases hstop : s = ⊤
  · exact ⟨0, fun y => by rw [iInf_eq_top.mp hstop y]; exact le_top⟩
  · have hslt : s < ⊤ := lt_top_iff_ne_top.mpr hstop
    set c : ℝ≥0∞ := s + 1 with hc
    have hctop : c < ⊤ := by
      rw [hc]; exact ENNReal.add_lt_top.mpr ⟨hslt, ENNReal.one_lt_top⟩
    have hsc : s < c := by rw [hc]; exact ENNReal.lt_add_right hstop one_ne_zero
    obtain ⟨y₀, hy₀⟩ := iInf_lt_iff.mp hsc
    have hmem : g ⁻¹' Set.Ioi c ∈ cocompact ℝ := hcoer (Ioi_mem_nhds hctop)
    obtain ⟨tt, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hclosed : IsClosed {y | g y ≤ c} := hg.isClosed_preimage c
    have hsub : {y | g y ≤ c} ⊆ tt := by
      intro y hy
      by_contra hyt
      exact absurd (ht_sub hyt) (by simpa using hy)
    have hcompact : IsCompact {y | g y ≤ c} := ht_comp.of_isClosed_subset hclosed hsub
    have hne : {y | g y ≤ c}.Nonempty := ⟨y₀, hy₀.le⟩
    obtain ⟨x, hx_mem, hx_min⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hne hcompact (hg.lowerSemicontinuousOn _)
    refine ⟨x, fun y => ?_⟩
    by_cases hy : g y ≤ c
    · exact isMinOn_iff.mp hx_min y hy
    · exact le_trans hx_mem (not_le.mp hy).le

/-- A lower semicontinuous coercive function attains its infimum over a lower half-line
`Iic q`. The lower-semicontinuous replacement for `exists_argmin_Iic`. -/
private theorem exists_argmin_Iic_lsc {g : ℝ → ℝ≥0∞} (hg : LowerSemicontinuous g)
    (hcoer : Tendsto g (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞))) (q : ℝ) :
    ∃ w ≤ q, g w = ⨅ v ∈ Set.Iic q, g v := by
  set mq : ℝ≥0∞ := ⨅ v ∈ Set.Iic q, g v with hmq
  by_cases hmqtop : mq = ⊤
  · refine ⟨q, le_refl q, ?_⟩
    have h : mq ≤ g q := by
      rw [hmq]; exact iInf₂_le q (Set.mem_Iic.mpr le_rfl)
    rw [hmqtop] at h ⊢
    exact top_le_iff.mp h
  · have hmqlt : mq < ⊤ := lt_top_iff_ne_top.mpr hmqtop
    set c : ℝ≥0∞ := mq + 1 with hc
    have hctop : c < ⊤ := by
      rw [hc]; exact ENNReal.add_lt_top.mpr ⟨hmqlt, ENNReal.one_lt_top⟩
    have hmc : mq < c := by rw [hc]; exact ENNReal.lt_add_right hmqtop one_ne_zero
    obtain ⟨v₀, hv₀q, hv₀c⟩ : ∃ v₀ ≤ q, g v₀ < c := by
      have h : (⨅ v ∈ Set.Iic q, g v) < c := hmc
      rw [iInf_lt_iff] at h
      obtain ⟨v, hv⟩ := h
      rw [iInf_lt_iff] at hv
      obtain ⟨hvq, hvc⟩ := hv
      exact ⟨v, hvq, hvc⟩
    have hmem : g ⁻¹' Set.Ioi c ∈ cocompact ℝ := hcoer (Ioi_mem_nhds hctop)
    obtain ⟨tt, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hclosed : IsClosed (Set.Iic q ∩ {v | g v ≤ c}) :=
      isClosed_Iic.inter (hg.isClosed_preimage c)
    have hsub : (Set.Iic q ∩ {v | g v ≤ c}) ⊆ tt := by
      intro v hv
      by_contra hvt
      exact absurd (ht_sub hvt) (by simpa using hv.2)
    have hcompact : IsCompact (Set.Iic q ∩ {v | g v ≤ c}) :=
      ht_comp.of_isClosed_subset hclosed hsub
    have hne : (Set.Iic q ∩ {v | g v ≤ c}).Nonempty := ⟨v₀, hv₀q, hv₀c.le⟩
    obtain ⟨w, hw_mem, hw_min⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hne hcompact (hg.lowerSemicontinuousOn _)
    refine ⟨w, hw_mem.1, ?_⟩
    rw [hmq]
    refine le_antisymm ?_ (iInf₂_le w hw_mem.1)
    refine le_iInf₂ fun v hv => ?_
    by_cases hvc : g v ≤ c
    · exact isMinOn_iff.mp hw_min v ⟨hv, hvc⟩
    · exact le_trans hw_mem.2 (not_le.mp hvc).le

/-- A convex `ℝ≥0∞`-valued function is finite on the segment spanned by two finiteness
points. -/
private theorem lt_top_of_convex_segment {g : ℝ → ℝ≥0∞} (hg : ConvexOn ℝ≥0 Set.univ g)
    {a b : ℝ} (ha : g a < ⊤) (hb : g b < ⊤) {u v : ℝ≥0} (huv : u + v = 1) :
    g (u • a + v • b) < ⊤ := by
  refine lt_of_le_of_lt (hg.2 (Set.mem_univ a) (Set.mem_univ b) (zero_le (a := u)) (zero_le (a := v)) huv) ?_
  rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.coe_lt_top ha,
    ENNReal.mul_lt_top ENNReal.coe_lt_top hb⟩

/-- The infimum over a lower half-line `Iic q`, for a convex function finite at `0`, is an
infimum over the rationals. Convex replacement for the density step relativized to `Iic q`. -/
private theorem iInf_Iic_eq_iInf_rat_min_of_convex {g : ℝ → ℝ≥0∞}
    (hg : ConvexOn ℝ≥0 Set.univ g) (h0 : g 0 < ⊤) (q : ℚ) :
    (⨅ v ∈ Set.Iic (q : ℝ), g v) = ⨅ p : ℚ, g (min (p : ℝ) (q : ℝ)) := by
  apply le_antisymm
  · refine le_iInf fun p => iInf₂_le (min (p : ℝ) (q : ℝ)) ?_
    exact Set.mem_Iic.mpr (min_le_right _ _)
  · refine le_iInf₂ fun w hw => ?_
    have hwq : w ≤ (q : ℝ) := hw
    set r : ℝ := min (0 : ℝ) (q : ℝ) with hr
    set c : ℝ≥0∞ := ⨅ p : ℚ, g (min (p : ℝ) (q : ℝ)) with hcdef
    have hrq : r ≤ (q : ℝ) := min_le_right _ _
    by_cases hrtop : g r < ⊤
    · have hmax : max r w ≤ (q : ℝ) := max_le hrq hwq
      refine convex_iInf_le_aux hg (r := r) (w := w) hrtop (c := c) ?_ ?_
      · calc c ≤ g (min ((0 : ℚ) : ℝ) (q : ℝ)) := iInf_le _ (0 : ℚ)
          _ = g r := by rw [hr]; norm_num
      · intro x hx hxr
        obtain ⟨p, rfl⟩ := hxr
        have hxq : (p : ℝ) ≤ (q : ℝ) := le_trans hx.2.le hmax
        exact (iInf_le _ p).trans_eq (by rw [min_eq_left hxq])
    · -- `g r = ⊤`: forces `q < 0`, `r = q`, and `g` is `⊤` on all of `Iic q`
      have hqneg : (q : ℝ) < 0 := by
        by_contra hq
        push_neg at hq
        exact hrtop (by rw [hr, min_eq_left hq]; exact h0)
      have hrq' : r = (q : ℝ) := by rw [hr, min_eq_right hqneg.le]
      have hgw : g w = ⊤ := by
        by_contra hwne
        have hwlt : g w < ⊤ := lt_top_iff_ne_top.mpr hwne
        have hwneg : w < 0 := lt_of_le_of_lt hwq hqneg
        set a : ℝ≥0 := ((q : ℝ) / w).toNNReal with ha
        set b : ℝ≥0 := (1 - (q : ℝ) / w).toNNReal with hb
        have haq : 0 ≤ (q : ℝ) / w := div_nonneg_of_nonpos hqneg.le hwneg.le
        have hbq : 0 ≤ 1 - (q : ℝ) / w := by
          have : 1 - (q : ℝ) / w = (w - q) / w := by field_simp [hwneg.ne]
          rw [this]; exact div_nonneg_of_nonpos (by linarith) hwneg.le
        have hab : a + b = 1 := by
          rw [ha, hb, ← Real.toNNReal_add haq hbq, show (q : ℝ) / w + (1 - (q : ℝ) / w) = 1 by
            ring, Real.toNNReal_one]
        have hpt : a • w + b • (0 : ℝ) = (q : ℝ) := by
          rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul, ha,
            Real.coe_toNNReal _ haq, mul_zero, add_zero]
          field_simp [hwneg.ne]
        have hfin := lt_top_of_convex_segment hg (a := w) (b := (0 : ℝ)) hwlt h0 hab
        rw [hpt] at hfin
        rw [hrq'] at hrtop
        exact hrtop hfin
      rw [hgw]; exact le_top

/-- **Measurable argmin, convex (lower-semicontinuous) form.** A jointly measurable family of
convex, lower-semicontinuous, coercive functions of a real scan variable, each **finite at
`0`**, admits a measurable minimizer selection. This is the exact strengthening the frozen
`exists_measurable_argmin` cannot supply: continuity is replaced by lower semicontinuity, at
the cost of a single finiteness point `f ω 0 < ⊤` (convexity + one finiteness point make the
rational-relaxed-sublevel construction valid, since the infimum is then approached from the
`0`-side along the rationals — see `convex_iInf_le_aux`). See the a.e. wrapper
`exists_measurable_argmin_of_convex` for the version the conditional-risk consumers use. -/
theorem exists_measurable_argmin_of_convex_of_finite {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hlsc : ∀ ω, LowerSemicontinuous (f ω))
    (hconv : ∀ ω, ConvexOn ℝ≥0 Set.univ (f ω))
    (hcoer : ∀ ω, Tendsto (f ω) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞)))
    (hf0 : ∀ ω, f ω 0 < ⊤) :
    ∃ u : Ω → ℝ, Measurable u ∧ ∀ ω, f ω (u ω) = ⨅ v : ℝ, f ω v := by
  classical
  have hfq : ∀ q : ℚ, Measurable (fun ω => f ω (q : ℝ)) := fun q =>
    hf.comp (measurable_id.prodMk measurable_const)
  set M : Ω → ℝ≥0∞ := fun ω => ⨅ v : ℝ, f ω v with hMdef
  have hM_meas : Measurable M := by
    have hEq : M = fun ω => ⨅ q : ℚ, f ω (q : ℝ) := by
      funext ω; exact iInf_eq_iInf_rat_of_convex (hconv ω) (hf0 ω)
    rw [hEq]; exact Measurable.iInf hfq
  have hLq_meas : ∀ q : ℚ, Measurable (fun ω => ⨅ v ∈ Set.Iic (q : ℝ), f ω v) := by
    intro q
    have hEq : (fun ω => ⨅ v ∈ Set.Iic (q : ℝ), f ω v)
        = fun ω => ⨅ p : ℚ, f ω (min (p : ℝ) (q : ℝ)) := by
      funext ω
      exact iInf_Iic_eq_iInf_rat_min_of_convex (hconv ω) (hf0 ω) q
    rw [hEq]
    exact Measurable.iInf fun p => hf.comp (measurable_id.prodMk measurable_const)
  set S : Ω → Set ℝ := fun ω => {v | f ω v = M ω} with hSdef
  set u : Ω → ℝ := fun ω => sInf (S ω) with hudef
  have hMle : ∀ ω (v : ℝ), M ω ≤ f ω v := fun ω v => iInf_le (f ω) v
  have hclosedS : ∀ ω, IsClosed (S ω) := by
    intro ω
    have hset : S ω = {v | f ω v ≤ M ω} := by
      ext v
      simp only [hSdef, Set.mem_setOf_eq]
      exact ⟨fun h => h.le, fun h => le_antisymm h (hMle ω v)⟩
    rw [hset]
    exact (hlsc ω).isClosed_preimage (M ω)
  have hneS : ∀ ω, (S ω).Nonempty := by
    intro ω
    obtain ⟨x, hx⟩ := exists_forall_le_of_lsc_of_coercive (hlsc ω) (hcoer ω)
    exact ⟨x, le_antisymm (le_iInf hx) (iInf_le _ x)⟩
  have hbddS : ∀ ω, M ω < ⊤ → BddBelow (S ω) := by
    intro ω hlt
    have hmem : f ω ⁻¹' Set.Ioi (M ω) ∈ cocompact ℝ := (hcoer ω) (Ioi_mem_nhds hlt)
    obtain ⟨t, ht_comp, ht_sub⟩ := mem_cocompact.mp hmem
    have hSsub : S ω ⊆ t := by
      intro v hv
      by_contra hvt
      have hlt2 : M ω < f ω v := ht_sub hvt
      rw [show f ω v = M ω from hv] at hlt2
      exact lt_irrefl _ hlt2
    exact ht_comp.bddBelow.mono hSsub
  have hattain : ∀ ω, f ω (u ω) = M ω := by
    intro ω
    by_cases hMtop : M ω = ⊤
    · have h1 : M ω ≤ f ω (u ω) := hMle ω (u ω)
      rw [hMtop] at h1 ⊢
      exact top_le_iff.mp h1
    · have hlt : M ω < ⊤ := lt_top_iff_ne_top.mpr hMtop
      exact (hclosedS ω).csInf_mem (hneS ω) (hbddS ω hlt)
  have hMle_biInf : ∀ ω (q : ℚ), M ω ≤ ⨅ v ∈ Set.Iic (q : ℝ), f ω v := fun ω q =>
    le_iInf₂ fun v _ => hMle ω v
  have hchar : ∀ ω (q : ℚ), u ω ≤ (q : ℝ) ↔
      (M ω = ⊤ ∧ (0 : ℝ) ≤ (q : ℝ)) ∨
      (M ω < ⊤ ∧ (⨅ v ∈ Set.Iic (q : ℝ), f ω v) = M ω) := by
    intro ω q
    by_cases hMtop : M ω = ⊤
    · have hSuniv : S ω = Set.univ := by
        ext v
        refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
        show f ω v = M ω
        exact le_antisymm (by rw [hMtop]; exact le_top) (hMle ω v)
      have hu0 : u ω = 0 := by
        show sInf (S ω) = 0
        rw [hSuniv]
        exact Real.sInf_of_not_bddBelow
          (not_bddBelow_iff.mpr fun x => ⟨x - 1, Set.mem_univ _, by linarith⟩)
      rw [hu0]
      constructor
      · intro h; exact Or.inl ⟨hMtop, h⟩
      · rintro (⟨_, h⟩ | ⟨hlt, _⟩)
        · exact h
        · exact absurd hMtop (ne_of_lt hlt)
    · have hlt : M ω < ⊤ := lt_top_iff_ne_top.mpr hMtop
      have hmem : u ω ∈ S ω := (hclosedS ω).csInf_mem (hneS ω) (hbddS ω hlt)
      constructor
      · intro h
        refine Or.inr ⟨hlt, le_antisymm ?_ (hMle_biInf ω q)⟩
        calc ⨅ v ∈ Set.Iic (q : ℝ), f ω v
            ≤ f ω (u ω) := iInf₂_le (u ω) (Set.mem_Iic.mpr h)
          _ = M ω := hmem
      · rintro (⟨hcontra, _⟩ | ⟨_, hbi⟩)
        · exact absurd hcontra hMtop
        · obtain ⟨w, hwq, hfw⟩ := exists_argmin_Iic_lsc (hlsc ω) (hcoer ω) (q : ℝ)
          have hwS : w ∈ S ω := by show f ω w = M ω; rw [hfw, hbi]
          exact le_trans (csInf_le (hbddS ω hlt) hwS) hwq
  refine ⟨u, ?_, fun ω => (hattain ω)⟩
  apply measurable_of_Iic
  intro r
  have hset : u ⁻¹' Set.Iic r
      = ⋂ (q : ℚ) (_ : r < (q : ℝ)), {ω | u ω ≤ (q : ℝ)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h q _; exact le_trans h (le_of_lt ‹r < (q : ℝ)›)
    · intro h
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨q, hrq, hqu⟩ := exists_rat_btwn hlt
      exact absurd (h q hrq) (not_le.mpr hqu)
  rw [hset]
  refine MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => ?_
  have hqset : {ω | u ω ≤ (q : ℝ)}
      = ((M ⁻¹' {⊤}) ∩ {ω | (0 : ℝ) ≤ (q : ℝ)}) ∪
        ((M ⁻¹' Set.Iio ⊤) ∩ {ω | (⨅ v ∈ Set.Iic (q : ℝ), f ω v) = M ω}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_Iio]
    rw [hchar ω q]
  rw [hqset]
  refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
  · exact hM_meas (measurableSet_singleton ⊤)
  · by_cases h : (0 : ℝ) ≤ (q : ℝ)
    · simp only [h, Set.setOf_true]; exact MeasurableSet.univ
    · simp only [h, Set.setOf_false]; exact MeasurableSet.empty
  · exact hM_meas measurableSet_Iio
  · exact measurableSet_eq_fun (hLq_meas q) hM_meas

/-- The surgery function `w ↦ ofReal (w²)`: convex, used to overwrite `f` on the null set
where `f ω 0 = ⊤` so that the everywhere-core hypotheses hold. -/
private lemma convexOn_ofReal_sq :
    ConvexOn ℝ≥0 Set.univ (fun w : ℝ => ENNReal.ofReal (w ^ 2)) := by
  refine ⟨convex_univ, fun a _ b _ u v hu hv huv => ?_⟩
  have hpt : u • a + v • b = (u : ℝ) * a + (v : ℝ) * b := by
    rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]
  rw [hpt, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
    show ((u : ℝ≥0∞)) = ENNReal.ofReal (u : ℝ) from (ENNReal.ofReal_coe_nnreal).symm,
    show ((v : ℝ≥0∞)) = ENNReal.ofReal (v : ℝ) from (ENNReal.ofReal_coe_nnreal).symm,
    ← ENNReal.ofReal_mul u.coe_nonneg, ← ENNReal.ofReal_mul v.coe_nonneg,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have huv' : (u : ℝ) + (v : ℝ) = 1 := by exact_mod_cast huv
  nlinarith [mul_nonneg (mul_nonneg u.coe_nonneg v.coe_nonneg) (sq_nonneg (a - b)),
    huv', u.coe_nonneg, v.coe_nonneg]

private lemma continuous_ofReal_sq : Continuous (fun w : ℝ => ENNReal.ofReal (w ^ 2)) :=
  ENNReal.continuous_ofReal.comp (continuous_pow 2)

private lemma tendsto_ofReal_sq_cocompact :
    Tendsto (fun w : ℝ => ENNReal.ofReal (w ^ 2)) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞)) := by
  refine ENNReal.tendsto_ofReal_nhds_top.2 ?_
  rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
  refine ⟨?_, tendsto_pow_atTop two_ne_zero⟩
  exact Tendsto.congr (fun w => by rw [Function.comp_apply]; ring)
    ((tendsto_pow_atTop (two_ne_zero)).comp tendsto_neg_atBot_atTop)

/-- **Measurable argmin, convex form (almost-everywhere).** The version the conditional-risk
consumers use: a jointly measurable family of convex, lower-semicontinuous, coercive functions
of a real scan variable, finite at `0` **for almost every** parameter, admits a measurable
minimizer selection valid almost everywhere. The a.e. finiteness point is exactly what the
finite-risk hypothesis of the location/scale MRE consumers supplies (via disintegration). -/
theorem exists_measurable_argmin_of_convex {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (hlsc : ∀ ω, LowerSemicontinuous (f ω))
    (hconv : ∀ ω, ConvexOn ℝ≥0 Set.univ (f ω))
    (hcoer : ∀ ω, Tendsto (f ω) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞)))
    (h0 : ∀ᵐ ω ∂μ, f ω 0 < ⊤) :
    ∃ u : Ω → ℝ, Measurable u ∧ ∀ᵐ ω ∂μ, f ω (u ω) = ⨅ v : ℝ, f ω v := by
  classical
  have hf00 : Measurable (fun ω => f ω 0) := hf.comp (measurable_id.prodMk measurable_const)
  -- overwrite `f` by `w ↦ ofReal (w²)` on the null set `{f ω 0 = ⊤}`
  set f' : Ω → ℝ → ℝ≥0∞ :=
    fun ω => if f ω 0 = ⊤ then (fun w => ENNReal.ofReal (w ^ 2)) else f ω with hf'def
  have hf'meas : Measurable (Function.uncurry f') := by
    have hB' : MeasurableSet {p : Ω × ℝ | f p.1 0 = ⊤} :=
      (hf00.comp measurable_fst) (measurableSet_singleton ⊤)
    have huncurry : Function.uncurry f'
        = fun p : Ω × ℝ => if f p.1 0 = ⊤ then ENNReal.ofReal (p.2 ^ 2) else f p.1 p.2 := by
      funext p
      simp only [Function.uncurry, hf'def]
      rw [apply_ite (fun g : ℝ → ℝ≥0∞ => g p.2)]
    rw [huncurry]
    exact Measurable.ite hB'
      (continuous_ofReal_sq.measurable.comp measurable_snd) hf
  have hlsc' : ∀ ω, LowerSemicontinuous (f' ω) := by
    intro ω; simp only [hf'def]; by_cases h : f ω 0 = ⊤
    · rw [if_pos h]; exact continuous_ofReal_sq.lowerSemicontinuous
    · rw [if_neg h]; exact hlsc ω
  have hconv' : ∀ ω, ConvexOn ℝ≥0 Set.univ (f' ω) := by
    intro ω; simp only [hf'def]; by_cases h : f ω 0 = ⊤
    · rw [if_pos h]; exact convexOn_ofReal_sq
    · rw [if_neg h]; exact hconv ω
  have hcoer' : ∀ ω, Tendsto (f' ω) (cocompact ℝ) (𝓝 (⊤ : ℝ≥0∞)) := by
    intro ω; simp only [hf'def]; by_cases h : f ω 0 = ⊤
    · rw [if_pos h]; exact tendsto_ofReal_sq_cocompact
    · rw [if_neg h]; exact hcoer ω
  have hf'0 : ∀ ω, f' ω 0 < ⊤ := by
    intro ω; simp only [hf'def]; by_cases h : f ω 0 = ⊤
    · rw [if_pos h]; simp
    · rw [if_neg h]; exact lt_top_iff_ne_top.mpr h
  obtain ⟨u, hu_meas, hu_min⟩ :=
    exists_measurable_argmin_of_convex_of_finite hf'meas hlsc' hconv' hcoer' hf'0
  refine ⟨u, hu_meas, ?_⟩
  filter_upwards [h0] with ω hω
  have heq : f' ω = f ω := by simp only [hf'def, if_neg (lt_top_iff_ne_top.mp hω)]
  have := hu_min ω
  rw [heq] at this
  exact this

end StatLean.PointEstimation
