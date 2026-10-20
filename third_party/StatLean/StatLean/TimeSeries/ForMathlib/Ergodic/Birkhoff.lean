module
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-!
# The pointwise (Birkhoff) ergodic theorem

The Mathlib pin carries the algebraic bookkeeping for `birkhoffSum`/`birkhoffAverage` and
von Neumann's *mean* (L²) ergodic theorem, but no maximal ergodic theorem and no a.e.
convergence statement. This file supplies them, for a measure-preserving map of a
probability space: the maximal ergodic theorem (Garsia's proof), a.e. convergence of
Birkhoff averages to the conditional expectation on the invariant σ-algebra, and the
ergodic corollary (limit = the space mean).

Consumed by `Mixing/LimitTheorems.slln_of_alphaMixing_debt` (FY Prop 2.8), whose closing
wave recorded the four-item build list this file is item (iii) of.

**Reference.** Birkhoff (1931); the maximal-inequality proof is Garsia (1965). FY cite
Doob 1953 / Ibragimov–Linnik 1971 for the mixing SLLN.

**Bibliographic comments.** The invariant σ-algebra and the condexp form follow the
standard modern treatment (e.g. Einsiedler–Ward, *Ergodic Theory*, ch. 2).
-/

open MeasureTheory Filter
open scoped Topology

namespace StatLean.TimeSeries

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → α}

/-- The **invariant σ-algebra** of a self-map: measurable sets with `f ⁻¹' s = s`.
Formalizes the almost-invariant information of the dynamics (edge behavior: for
non-measurable `f` this is still a σ-algebra, just not comparable to the ambient one
through `f`). -/
def invariantSigma (f : α → α) : MeasurableSpace α where
  MeasurableSet' s := MeasurableSet s ∧ f ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, by rw [Set.preimage_compl, hs.2]⟩
  measurableSet_iUnion g hg :=
    ⟨MeasurableSet.iUnion fun i => (hg i).1, by
      simp only [Set.preimage_iUnion]
      exact Set.iUnion_congr fun i => (hg i).2⟩

/-- The invariant σ-algebra is coarser than the ambient one.
-- LEAN-ONLY: needed to state the conditional expectation; no scope change -/
theorem invariantSigma_le (f : α → α) : invariantSigma f ≤ ‹MeasurableSpace α› :=
  fun _ hs => hs.1

/-! ### Garsia's running maximum

The proof of the maximal ergodic theorem below is Garsia's: with
`M_N x = max_{1 ≤ k ≤ N+1} S_k x` (`birkhoffMax`) one has the *pointwise* inequality
`M_N x ≤ g x + M_N⁺ (f x)`, which on `{M_N > 0}` reads `g ≥ M_N⁺ − M_N⁺ ∘ f`; integrating
and using measure preservation kills the right-hand side. -/

section Garsia

/-- Garsia's running maximum `max_{1 ≤ k ≤ N+1} birkhoffSum f g k x`.
-- LEAN-ONLY: auxiliary for `maximal_ergodic`; no scope change -/
private noncomputable def birkhoffMax (f : α → α) (g : α → ℝ) (N : ℕ) (x : α) : ℝ :=
  (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun k => birkhoffSum f g (k + 1) x

omit [MeasurableSpace α] in
private theorem le_birkhoffMax {g : α → ℝ} {N k : ℕ} (hk : k ≤ N) (x : α) :
    birkhoffSum f g (k + 1) x ≤ birkhoffMax f g N x :=
  Finset.le_sup' (fun k => birkhoffSum f g (k + 1) x) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))

omit [MeasurableSpace α] in
private theorem birkhoffMax_mono {g : α → ℝ} (x : α) :
    Monotone fun N => birkhoffMax f g N x := by
  intro M N hMN
  refine Finset.sup'_le _ _ fun k hk => ?_
  exact le_birkhoffMax ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)).trans hMN) x

omit [MeasurableSpace α] in
/-- The Garsia inequality: `M_N ≤ g + M_N⁺ ∘ f` pointwise. -/
private theorem birkhoffMax_le {g : α → ℝ} (N : ℕ) (x : α) :
    birkhoffMax f g N x ≤ g x + max (birkhoffMax f g N (f x)) 0 := by
  refine Finset.sup'_le _ _ fun k hk => ?_
  have hkN : k ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [birkhoffSum_succ']
  have h : birkhoffSum f g k (f x) ≤ max (birkhoffMax f g N (f x)) 0 := by
    cases k with
    | zero => simp
    | succ j =>
        exact (le_birkhoffMax (le_trans (Nat.le_succ j) hkN) (f x)).trans (le_max_left _ _)
  linarith

omit [MeasurableSpace α] in
private theorem birkhoffMax_succ (f : α → α) (g : α → ℝ) (N : ℕ) (x : α) :
    birkhoffMax f g (N + 1) x = max (birkhoffSum f g (N + 2) x) (birkhoffMax f g N x) := by
  refine le_antisymm (Finset.sup'_le _ _ fun k hk => ?_) ?_
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hk) with h | h
    · exact (le_birkhoffMax (Nat.lt_succ_iff.1 h) x).trans (le_max_right _ _)
    · subst h; exact le_max_left _ _
  · exact max_le (le_birkhoffMax (le_refl (N + 1)) x) (birkhoffMax_mono x (Nat.le_succ N))

private theorem measurable_birkhoffSum {g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (n : ℕ) : Measurable (birkhoffSum f g n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ fun k _ => hgm.comp (hfm.iterate k)

private theorem measurable_birkhoffMax {g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (N : ℕ) : Measurable (birkhoffMax f g N) := by
  unfold birkhoffMax
  exact Finset.measurable_range_sup'' fun k _ => measurable_birkhoffSum hfm hgm (k + 1)

private theorem integrable_birkhoffSum (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hg : Integrable g μ) (n : ℕ) : Integrable (birkhoffSum f g n) μ := by
  unfold birkhoffSum
  exact integrable_finset_sum _ fun k _ => (hf.iterate k).integrable_comp_of_integrable hg

private theorem integrable_birkhoffMax (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hg : Integrable g μ) (N : ℕ) : Integrable (birkhoffMax f g N) μ := by
  induction N with
  | zero =>
      have h : birkhoffMax f g 0 = g := by
        funext x
        simp [birkhoffMax, birkhoffSum_one]
      rw [h]; exact hg
  | succ N ih =>
      have h : birkhoffMax f g (N + 1) = birkhoffSum f g (N + 2) ⊔ birkhoffMax f g N := by
        funext x
        rw [birkhoffMax_succ]
        rfl
      rw [h]
      exact (integrable_birkhoffSum hf hg _).sup ih

/-- Measure preservation moves the map through the integral. -/
private theorem integral_comp_self (hf : MeasurePreserving f μ μ) {F : α → ℝ}
    (hFm : AEStronglyMeasurable F μ) : ∫ x, F (f x) ∂μ = ∫ x, F x ∂μ := by
  conv_rhs => rw [← hf.map_eq]
  rw [integral_map hf.measurable.aemeasurable (by rwa [hf.map_eq])]

/-- The maximal ergodic theorem for a *measurable* observable; the general case follows by
passing to a measurable representative. -/
private theorem maximal_ergodic_aux (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hgm : Measurable g) (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x}, g x ∂μ := by
  set E : ℕ → Set α := fun N => {x | 0 < birkhoffMax f g N x} with hE
  have hEm : ∀ N, MeasurableSet (E N) := fun N =>
    measurableSet_lt measurable_const (measurable_birkhoffMax hf.measurable hgm N)
  have hEmono : Monotone E := fun M N hMN x hx => lt_of_lt_of_le hx (birkhoffMax_mono x hMN)
  have hUnion : (⋃ N, E N) = {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x} := by
    ext x
    simp only [Set.mem_iUnion, hE, Set.mem_setOf_eq]
    constructor
    · rintro ⟨N, hN⟩
      obtain ⟨k, _, hk⟩ := (Finset.lt_sup'_iff _).1 hN
      exact ⟨k, hk⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, lt_of_lt_of_le hn (le_birkhoffMax (le_refl n) x)⟩
  -- Garsia's estimate on each level set
  have key : ∀ N, 0 ≤ ∫ x in E N, g x ∂μ := by
    intro N
    set M : α → ℝ := fun x => max (birkhoffMax f g N x) 0 with hM
    have hMmeas : Measurable M :=
      (measurable_birkhoffMax hf.measurable hgm N).max measurable_const
    have hMint : Integrable M μ := by
      refine Integrable.mono' (integrable_birkhoffMax hf hg N).abs
        hMmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      simp only [hM, Real.norm_eq_abs]
      rcases le_or_gt (birkhoffMax f g N x) 0 with h | h
      · simp [max_eq_right h, abs_nonneg]
      · simp [max_eq_left h.le]
    have hMnn : ∀ x, 0 ≤ M x := fun x => le_max_right _ _
    have hMcompf : Integrable (fun x => M (f x)) μ := hf.integrable_comp_of_integrable hMint
    have hpt : ∀ x ∈ E N, M x - M (f x) ≤ g x := by
      intro x hx
      have h1 : M x = birkhoffMax f g N x := max_eq_left (le_of_lt hx)
      have h2 : M (f x) = max (birkhoffMax f g N (f x)) 0 := rfl
      have h3 := birkhoffMax_le (f := f) (g := g) N x
      rw [h1, h2]; linarith
    have hint1 : ∫ x in E N, (M x - M (f x)) ∂μ ≤ ∫ x in E N, g x ∂μ :=
      setIntegral_mono_on (hMint.sub hMcompf).integrableOn hg.integrableOn (hEm N) hpt
    have hsplit : ∫ x in E N, (M x - M (f x)) ∂μ
        = (∫ x in E N, M x ∂μ) - ∫ x in E N, M (f x) ∂μ :=
      integral_sub hMint.integrableOn hMcompf.integrableOn
    have hA : ∫ x in E N, M x ∂μ = ∫ x, M x ∂μ := by
      refine setIntegral_eq_integral_of_ae_compl_eq_zero
        (Filter.Eventually.of_forall fun x hx => ?_)
      simp only [hM]
      exact max_eq_right (not_lt.1 hx)
    have hB : ∫ x in E N, M (f x) ∂μ ≤ ∫ x, M (f x) ∂μ :=
      setIntegral_le_integral hMcompf (Filter.Eventually.of_forall fun x => hMnn (f x))
    have hC : ∫ x, M (f x) ∂μ = ∫ x, M x ∂μ :=
      integral_comp_self hf hMmeas.aestronglyMeasurable
    linarith
  rw [← hUnion]
  exact ge_of_tendsto (tendsto_setIntegral_of_monotone hEm hEmono hg.integrableOn)
    (Filter.Eventually.of_forall key)

end Garsia

/-- **The maximal ergodic theorem** (Garsia): for integrable `g`, the integral of `g`
over the set where some Birkhoff sum is positive is nonnegative.
-- USER-INPUT: measure-preserving dynamics and integrable observable; Birkhoff/Garsia -/
theorem maximal_ergodic (hf : MeasurePreserving f μ μ) {g : α → ℝ}
    (hg : Integrable g μ) :
    0 ≤ ∫ x in {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x}, g x ∂μ := by
  -- replace `g` by a measurable representative; both the set and the integrand only change
  -- by a null set, because `f` is measure preserving
  set g' := hg.1.mk g with hg'def
  have hg'm : Measurable g' := hg.1.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[μ] g' := hg.1.ae_eq_mk
  have hg' : Integrable g' μ := hg.congr hgg'
  have hiter : ∀ᵐ x ∂μ, ∀ k : ℕ, g (f^[k] x) = g' (f^[k] x) := by
    rw [ae_all_iff]
    exact fun k => (hf.iterate k).quasiMeasurePreserving.ae hgg'
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, birkhoffSum f g (n + 1) x = birkhoffSum f g' (n + 1) x := by
    filter_upwards [hiter] with x hx n
    exact Finset.sum_congr rfl fun k _ => hx k
  have hset : {x | ∃ n : ℕ, 0 < birkhoffSum f g (n + 1) x}
      =ᵐ[μ] {x | ∃ n : ℕ, 0 < birkhoffSum f g' (n + 1) x} := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [hall] with x hx
    exact ⟨fun ⟨n, hn⟩ => ⟨n, (hx n) ▸ hn⟩, fun ⟨n, hn⟩ => ⟨n, (hx n).symm ▸ hn⟩⟩
  rw [setIntegral_congr_set hset,
    integral_congr_ae (ae_restrict_of_ae hgg' : g =ᵐ[μ.restrict _] g')]
  exact maximal_ergodic_aux hf hg'm hg'

/-! ### The pointwise theorem

Fix `ε > 0`, write `E = μ[g | invariantSigma f]` (which satisfies `E ∘ f = E` *exactly*,
because an `invariantSigma f`-measurable function has `invariantSigma f`-measurable level
sets) and put `h = g − E − ε/2`. The set

`B = {x | ∀ M : ℝ, ∃ᶠ n, M < birkhoffSum f h n x}`

of points whose `h`-Birkhoff sums are unbounded above is **exactly** `f`-invariant: by
`birkhoffSum_succ'`, `birkhoffSum f h n (f x) = birkhoffSum f h (n+1) x − h x`, and the shift
by the constant `h x` is absorbed by the quantifier over `M` — no limit argument and no
`limsup` are needed. This is what makes the argument formalizable without an `EReal`-valued
`limsup` calculus. Since `B` is invariant, `maximal_ergodic` applied to `h · 1_B` gives
`0 ≤ ∫_B h`, while `B ∈ invariantSigma f` gives `∫_B g = ∫_B E` and hence
`∫_B h = −(ε/2)·μ B`. So `μ B = 0`, and off `B` the sums `birkhoffSum f h n` are bounded
above, whence `birkhoffAverage f g n ≤ E + ε` eventually. -/

section Pointwise

private theorem frequently_succ_iff (p : ℕ → Prop) :
    (∃ᶠ n in atTop, p (n + 1)) ↔ ∃ᶠ n in atTop, p n := by
  simp only [Filter.frequently_atTop]
  constructor
  · intro hp a
    obtain ⟨b, hb, hpb⟩ := hp a
    exact ⟨b + 1, le_trans hb (Nat.le_succ b), hpb⟩
  · intro hp a
    obtain ⟨b, hb, hpb⟩ := hp (a + 1)
    exact ⟨b - 1, by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩

/-- One half of the pointwise ergodic theorem: the Birkhoff averages are eventually below
`μ[g | invariantSigma f] + ε`, almost everywhere. -/
private theorem birkhoff_ae_le [IsProbabilityMeasure μ] (hf : MeasurePreserving f μ μ)
    (hfm : Measurable f) {g : α → ℝ} (hgm : Measurable g) (hg : Integrable g μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop,
      birkhoffAverage ℝ f g n x ≤ (μ[g | invariantSigma f]) x + ε := by
  set E := μ[g | invariantSigma f] with hEdef
  have hEsm : StronglyMeasurable[invariantSigma f] E := stronglyMeasurable_condExp
  have hEint : Integrable E μ := integrable_condExp
  have hEmeas : Measurable E := hEsm.measurable.mono (invariantSigma_le f) le_rfl
  -- an `invariantSigma f`-measurable function is *pointwise* invariant
  have hEf : ∀ x, E (f x) = E x := by
    intro x
    have hm : MeasurableSet (E ⁻¹' {E x}) ∧ f ⁻¹' (E ⁻¹' {E x}) = E ⁻¹' {E x} :=
      hEsm.measurable (measurableSet_singleton (E x))
    have hx : x ∈ f ⁻¹' (E ⁻¹' {E x}) := by rw [hm.2]; rfl
    exact hx
  obtain ⟨c, hc, hεc⟩ : ∃ c : ℝ, 0 < c ∧ ε = c + c := ⟨ε / 2, by linarith, by ring⟩
  set φ : α → ℝ := fun y => E y + c with hφ
  set h : α → ℝ := fun y => g y - φ y with hh
  have hhPi : h = g - φ := by funext y; simp [hh]
  have hφf : φ ∘ f = φ := funext fun x => by simp [hφ, hEf x]
  have hφm : Measurable φ := hEmeas.add measurable_const
  have hφint : Integrable φ μ := hEint.add (integrable_const c)
  have hhm : Measurable h := hgm.sub hφm
  have hhint : Integrable h μ := hg.sub hφint
  have hSh : ∀ (n : ℕ) (x : α),
      birkhoffSum f h n x = birkhoffSum f g n x - (n : ℝ) * (E x + c) := by
    intro n x
    have hSφ : birkhoffSum f φ n x = (n : ℝ) * (E x + c) := by
      rw [birkhoffSum_of_comp_eq hφf]
      simp [hφ, Pi.smul_apply, nsmul_eq_mul]
      ring
    rw [hhPi, birkhoffSum_sub, hSφ]
  -- the invariant set of points with unbounded Birkhoff sums
  set B : Set α := {x | ∀ M : ℝ, ∃ᶠ n in atTop, M < birkhoffSum f h n x} with hB
  have hmemB : ∀ x, x ∈ B ↔ ∀ M : ℝ, ∃ᶠ n in atTop, M < birkhoffSum f h n x :=
    fun _ => Iff.rfl
  have hBm : MeasurableSet B := by
    have hEq : B = ⋂ m : ℕ, ⋂ N : ℕ, ⋃ n : ℕ, ⋃ (_ : N ≤ n),
        {x | (m : ℝ) < birkhoffSum f h n x} := by
      ext x
      simp only [hmemB, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq,
        Filter.frequently_atTop, ge_iff_le, exists_prop]
      refine ⟨fun hx m N => hx (m : ℝ) N, fun hx M N => ?_⟩
      obtain ⟨m, hm⟩ := exists_nat_gt M
      obtain ⟨n, hn1, hn2⟩ := hx m N
      exact ⟨n, hn1, lt_trans hm hn2⟩
    rw [hEq]
    exact MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
        measurableSet_lt measurable_const (measurable_birkhoffSum hfm hhm n)
  have hshift : ∀ (x : α) (n : ℕ),
      birkhoffSum f h n (f x) = birkhoffSum f h (n + 1) x - h x := by
    intro x n
    rw [birkhoffSum_succ']
    ring
  have hBinv : f ⁻¹' B = B := by
    ext x
    simp only [Set.mem_preimage, hmemB]
    constructor
    · intro hfx M
      have h1 := hfx (M - h x)
      simp only [hshift x] at h1
      exact (frequently_succ_iff _).1 (h1.mono fun n hn => by linarith)
    · intro hx M
      have h1 : ∃ᶠ n in atTop, M + h x < birkhoffSum f h (n + 1) x :=
        (frequently_succ_iff fun n => M + h x < birkhoffSum f h n x).2 (hx (M + h x))
      refine h1.mono fun n hn => ?_
      rw [hshift x n]
      linarith
  have hfB : ∀ x, f x ∈ B ↔ x ∈ B := fun x => Set.ext_iff.1 hBinv x
  have hBiter : ∀ (k : ℕ) (x : α), f^[k] x ∈ B ↔ x ∈ B := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply, ih (f x), hfB]
  -- `B` is contained in the set of the maximal ergodic theorem
  have hBD : ∀ x ∈ B, ∃ n : ℕ, 0 < birkhoffSum f h (n + 1) x := by
    intro x hx
    have h0 := (hmemB x).1 hx 0
    rw [Filter.frequently_atTop] at h0
    obtain ⟨n, hn1, hn2⟩ := h0 1
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact ⟨k, hn2⟩
  -- Birkhoff sums of the truncated observable
  have hSind : ∀ (n : ℕ) (x : α),
      birkhoffSum f (Set.indicator B h) n x = Set.indicator B (birkhoffSum f h n) x := by
    intro n x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      unfold birkhoffSum
      exact Finset.sum_congr rfl fun k _ => Set.indicator_of_mem ((hBiter k x).2 hx) h
    · rw [Set.indicator_of_notMem hx]
      unfold birkhoffSum
      exact Finset.sum_eq_zero fun k _ =>
        Set.indicator_of_notMem (fun hc' => hx ((hBiter k x).1 hc')) h
  have hmax := maximal_ergodic hf (hhint.indicator hBm)
  have hsetEq : {x | ∃ n : ℕ, 0 < birkhoffSum f (Set.indicator B h) (n + 1) x} = B := by
    ext x
    simp only [Set.mem_setOf_eq, hSind]
    constructor
    · rintro ⟨n, hn⟩
      by_contra hx
      rw [Set.indicator_of_notMem hx] at hn
      exact lt_irrefl 0 hn
    · intro hx
      obtain ⟨n, hn⟩ := hBD x hx
      exact ⟨n, by rwa [Set.indicator_of_mem hx]⟩
  rw [hsetEq, setIntegral_congr_fun hBm (fun x hx => Set.indicator_of_mem hx h)] at hmax
  -- but `B` is invariant, so the conditional expectation kills the `g − E` part
  have hBG : MeasurableSet[invariantSigma f] B := ⟨hBm, hBinv⟩
  have hgE : ∫ x in B, E x ∂μ = ∫ x in B, g x ∂μ :=
    setIntegral_condExp (invariantSigma_le f) hg hBG
  have hsplit : ∫ x in B, h x ∂μ
      = (∫ x in B, g x ∂μ) - (∫ x in B, E x ∂μ) - μ.real B * c := by
    have h1 : ∫ x in B, h x ∂μ = (∫ x in B, g x ∂μ) - ∫ x in B, φ x ∂μ := by
      simp only [hh]
      exact integral_sub hg.integrableOn hφint.integrableOn
    have h2 : ∫ x in B, φ x ∂μ = (∫ x in B, E x ∂μ) + μ.real B * c := by
      simp only [hφ]
      rw [integral_add hEint.integrableOn (integrable_const c).integrableOn,
        setIntegral_const, smul_eq_mul]
    rw [h1, h2]; ring
  have hμB : μ.real B = 0 := by
    rw [hsplit, hgE] at hmax
    have h2 : (0 : ℝ) ≤ μ.real B := measureReal_nonneg
    nlinarith
  have hμB0 : μ B = 0 := by
    rw [measureReal_def] at hμB
    rcases (ENNReal.toReal_eq_zero_iff (μ B)).1 hμB with h' | h'
    · exact h'
    · exact absurd h' (measure_ne_top μ B)
  have haeB : ∀ᵐ x ∂μ, x ∉ B := by
    rw [ae_iff]
    simpa using hμB0
  filter_upwards [haeB] with x hx
  -- off `B` the Birkhoff sums of `h` are bounded above; divide by `n`
  have hxB : ¬ ∀ M : ℝ, ∃ᶠ n in atTop, M < birkhoffSum f h n x := fun hc' => hx ((hmemB x).2 hc')
  push Not at hxB
  obtain ⟨M, hM'⟩ := hxB
  have hbig : ∀ᶠ n : ℕ in atTop, (2 * |M| / ε : ℝ) ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  filter_upwards [hM', hbig, eventually_ge_atTop 1] with n hn1 hn2 hn3
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn3
  have hMcn : M ≤ (n : ℝ) * c := by
    have h4 : 2 * |M| ≤ (n : ℝ) * ε := (div_le_iff₀ hε).1 hn2
    have h5 : M ≤ |M| := le_abs_self M
    have h6 : (n : ℝ) * ε = (n : ℝ) * c + (n : ℝ) * c := by rw [hεc]; ring
    linarith
  have hkey : birkhoffSum f g n x ≤ (n : ℝ) * (E x + ε) := by
    have h7 := hSh n x
    have h8 : (n : ℝ) * (E x + c) = (n : ℝ) * E x + (n : ℝ) * c := by ring
    have h9 : (n : ℝ) * (E x + ε) = (n : ℝ) * E x + (n : ℝ) * c + (n : ℝ) * c := by
      rw [hεc]; ring
    linarith
  calc birkhoffAverage ℝ f g n x = (n : ℝ)⁻¹ * birkhoffSum f g n x := by
        simp [birkhoffAverage, smul_eq_mul]
    _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * (E x + ε)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = E x + ε := by field_simp

end Pointwise

/-- **The pointwise (Birkhoff) ergodic theorem, conditional-expectation form**: for a
measure-preserving `f` on a probability space and integrable `g`, the Birkhoff averages
converge a.e. to the conditional expectation of `g` on the invariant σ-algebra.
-- USER-INPUT: measure-preserving dynamics and integrable observable; Birkhoff 1931 -/
theorem birkhoffAverage_ae_tendsto_condexp [IsProbabilityMeasure μ]
    (hf : MeasurePreserving f μ μ) (hfm : Measurable f) {g : α → ℝ}
    (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ f g n x) atTop
      (𝓝 ((μ[g | invariantSigma f]) x)) := by
  -- pass to a measurable representative
  set g' := hg.1.mk g with hg'def
  have hg'm : Measurable g' := hg.1.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[μ] g' := hg.1.ae_eq_mk
  have hg' : Integrable g' μ := hg.congr hgg'
  have hiter : ∀ᵐ x ∂μ, ∀ k : ℕ, g (f^[k] x) = g' (f^[k] x) := by
    rw [ae_all_iff]
    exact fun k => (hf.iterate k).quasiMeasurePreserving.ae hgg'
  have havg : ∀ᵐ x ∂μ, ∀ n : ℕ,
      birkhoffAverage ℝ f g n x = birkhoffAverage ℝ f g' n x := by
    filter_upwards [hiter] with x hx n
    simp only [birkhoffAverage, birkhoffSum]
    exact congrArg _ (Finset.sum_congr rfl fun k _ => hx k)
  have hcond : μ[g | invariantSigma f] =ᵐ[μ] μ[g' | invariantSigma f] := condExp_congr_ae hgg'
  -- the two one-sided bounds, for `g'` and for `-g'`
  have hup : ∀ᵐ x ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop,
      birkhoffAverage ℝ f g' n x ≤ (μ[g' | invariantSigma f]) x + 1 / (m + 1) := by
    rw [ae_all_iff]
    exact fun m => birkhoff_ae_le hf hfm hg'm hg' (by positivity)
  have hlo : ∀ᵐ x ∂μ, ∀ m : ℕ, ∀ᶠ n in atTop,
      (μ[g' | invariantSigma f]) x - 1 / (m + 1) ≤ birkhoffAverage ℝ f g' n x := by
    rw [ae_all_iff]
    intro m
    have hneg := birkhoff_ae_le (g := -g') hf hfm hg'm.neg hg'.neg
      (ε := 1 / (m + 1)) (by positivity)
    filter_upwards [hneg, condExp_neg g' (invariantSigma f)] with x hx hcx
    filter_upwards [hx] with n hn
    have h1 : birkhoffAverage ℝ f (-g') n x = -birkhoffAverage ℝ f g' n x := by
      simp [birkhoffAverage, birkhoffSum_neg]
    rw [h1, hcx] at hn
    simp only [Pi.neg_apply] at hn
    linarith
  filter_upwards [havg, hcond, hup, hlo] with x hx1 hx2 hx3 hx4
  rw [hx2, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hx3 m)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 (hx4 m)
  refine ⟨max N1 N2, fun n hn => ?_⟩
  have h1 := hN1 n (le_trans (le_max_left _ _) hn)
  have h2 := hN2 n (le_trans (le_max_right _ _) hn)
  rw [hx1 n, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Birkhoff for an ergodic map**: the averages converge a.e. to the space mean.
-- USER-INPUT: ergodic dynamics and integrable observable; Birkhoff 1931 -/
theorem birkhoffAverage_ae_tendsto_integral [IsProbabilityMeasure μ]
    (hf : Ergodic f μ) (hfm : Measurable f) {g : α → ℝ} (hg : Integrable g μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ f g n x) atTop (𝓝 (∫ x, g x ∂μ)) := by
  -- for an ergodic map every `invariantSigma`-measurable set is null or conull, so the
  -- conditional expectation on `invariantSigma f` is a.e. the space mean
  have hconst : (fun _ : α => ∫ x, g x ∂μ) =ᵐ[μ] μ[g | invariantSigma f] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (invariantSigma_le f) hg
      (fun s _ _ => (integrable_const _).integrableOn) (fun s hs _ => ?_)
      aestronglyMeasurable_const
    have hs' : MeasurableSet s ∧ f ⁻¹' s = s := hs
    rcases hf.ae_empty_or_univ hs'.1 hs'.2 with h | h
    · rw [setIntegral_congr_set h, setIntegral_congr_set h]
      simp
    · rw [setIntegral_congr_set h, setIntegral_congr_set h]
      simp
  filter_upwards [birkhoffAverage_ae_tendsto_condexp hf.toMeasurePreserving hfm hg, hconst]
    with x h1 h2
  rwa [h2]

end StatLean.TimeSeries
