module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.CDF

@[expose] public section

/-!
# Quantile (generalized inverse) of a distribution function — ForMathlib brick

The **quantile function** of a nondecreasing `F : ℝ → ℝ` is
`quantile F p = inf {x | p ≤ F x}`. Three uses drive this file:

* the **Galois property** `quantile F p ≤ x ↔ p ≤ F x` (for right-continuous nondecreasing
  `F`), the workhorse identity behind every quantile computation;
* the **critical constants of a randomized test**: for a law `P` on `ℝ` and a level
  `α ∈ (0,1)` there are `C` and `γ ∈ [0,1]` with `P(C,∞) + γ·P{C} = α`, i.e. the level can
  always be met exactly by randomizing on the boundary atom (`exists_critical_constants`);
* **inverse-transform sampling** `quantile F` pushes the uniform law on `[0,1]` to `P`, and
  the two convergence statements (deterministic, and in probability for random distribution
  functions) that quantile-based calibration arguments consume.

Mathlib-only; nothing here mentions tests or models.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.2 (Permutation and Randomization Tests), supporting material for the
randomization critical value: the generalized inverse of a distribution function. (`TSH4
§17.2`.)

**Proof formalization notes.**
* `quantile` uses the `Real.sInf` junk conventions: the infimum of an empty or
  unbounded-below set is `0`. Every statement below therefore carries either an explicit
  nonemptiness/bounded-below side condition or a hypothesis (`StrictMono F`, `F` a genuine
  distribution function, `0 < p < 1`) that rules the junk out. `map_quantile_uniform` is the
  one place where junk survives — at the two endpoints `p ∈ {0,1}` — and is harmless there,
  since a pushforward only depends on the map up to a Lebesgue-null set.
* Right continuity is written `ContinuousWithinAt F (Set.Ici y) y`; it is used exactly once,
  in the forward direction of `quantile_le_iff` (to know that the infimum is attained).
* `tendsto_quantile_of_tendsto` needs neither continuity of the limit `F` nor any tail
  behaviour of the approximants: strict monotonicity of `F` at the target point plus
  monotonicity of each approximant already gives the two-sided bracketing. The same
  bracketing, run under the measure, gives `tendstoInMeasure_quantile`; no measurability of
  the random distribution functions is required, because the argument only ever compares
  measures of nested sets.
* The concept layer of this area carries the same formula under the name `cdfPseudoInverse`
  (bootstrap data model). That duplicate predates this brick; the intended end state is for
  the concept-layer name to be an abbreviation of `quantile`, which the bottom layer cannot
  do itself (it must not import the concept layer).

**Bibliographic comments.** The generalized inverse of a distribution function and its Galois
property are classical folklore of measure-theoretic probability, with no single seminal
source; the quantile transform as a construction of a random variable with a prescribed law
goes back to the beginnings of the subject (cf. P. Lévy, *Théorie de l'addition des variables
aléatoires*, Gauthier-Villars, 1937). The existence of the boundary-randomization constants
`(C, γ)` realizing a prescribed level exactly is the device introduced by J. Neyman and
E. S. Pearson ("On the problem of the most efficient tests of statistical hypotheses,"
*Phil. Trans. R. Soc. A* **231** (1933), 289–337).
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace StatLean.HypothesisTesting

/-- The **quantile function** (generalized inverse) of `F`: `quantile F p = inf {x | p ≤ F x}`.

Junk conventions: the infimum of the empty set and of a set unbounded below is `0`, so for
`p` outside the range of a genuine distribution function this returns `0`. -/
noncomputable def quantile (F : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {x : ℝ | p ≤ F x}

/-- The quantile function is nondecreasing in the level. -/
theorem quantile_mono (F : ℝ → ℝ) {p q : ℝ}
    -- USER-INPUT: the two levels, ordered; classical
    (hpq : p ≤ q)
    -- LEAN-ONLY: excludes the `sInf` junk of an unbounded-below sublevel set
    (hbdd : BddBelow {x : ℝ | p ≤ F x})
    -- LEAN-ONLY: excludes the `sInf ∅ = 0` junk at the upper level
    (hne : {x : ℝ | q ≤ F x}.Nonempty) :
    quantile F p ≤ quantile F q := by
  apply csInf_le_csInf hbdd hne
  intro x hx
  exact le_trans hpq hx

/-- **Galois property** of the quantile function: for a nondecreasing, right-continuous `F`,
`quantile F p ≤ x` iff `p ≤ F x`.

(This is the statement listed as `le_quantile_iff` in the area outline; it is named here for
the side of the inequality it decides, following the Mathlib convention.) -/
theorem quantile_le_iff {F : ℝ → ℝ} {p x : ℝ}
    -- USER-INPUT: `F` is a distribution function — nondecreasing; classical
    (hmono : Monotone F)
    -- USER-INPUT: `F` is a distribution function — right-continuous; classical
    (hrc : ∀ y : ℝ, ContinuousWithinAt F (Set.Ici y) y)
    -- LEAN-ONLY: excludes the `sInf ∅ = 0` junk
    (hne : {y : ℝ | p ≤ F y}.Nonempty)
    -- LEAN-ONLY: excludes the `sInf` junk of an unbounded-below sublevel set
    (hbdd : BddBelow {y : ℝ | p ≤ F y}) :
    quantile F p ≤ x ↔ p ≤ F x := by
  have hc : p ≤ F (quantile F p) := by
    show p ≤ F (sInf {y : ℝ | p ≤ F y})
    have hglb : IsGLB {y : ℝ | p ≤ F y} (sInf {y : ℝ | p ≤ F y}) :=
      Real.isGLB_sInf hne hbdd
    have hmem : sInf {y : ℝ | p ≤ F y} ∈ closure {y : ℝ | p ≤ F y} :=
      hglb.mem_closure hne
    haveI hnb : (𝓝[{y : ℝ | p ≤ F y}] (sInf {y : ℝ | p ≤ F y})).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hmem
    have hsub : {y : ℝ | p ≤ F y} ⊆ Set.Ici (sInf {y : ℝ | p ≤ F y}) :=
      fun y hy => hglb.1 hy
    have htend : Tendsto F (𝓝[{y : ℝ | p ≤ F y}] (sInf {y : ℝ | p ≤ F y}))
        (𝓝 (F (sInf {y : ℝ | p ≤ F y}))) :=
      (hrc _).mono_left (nhdsWithin_mono _ hsub)
    have hev : ∀ᶠ y in 𝓝[{y : ℝ | p ≤ F y}] (sInf {y : ℝ | p ≤ F y}), p ≤ F y :=
      Filter.eventually_of_mem self_mem_nhdsWithin (fun y hy => hy)
    exact ge_of_tendsto htend hev
  constructor
  · intro h
    exact le_trans hc (hmono h)
  · intro h
    exact csInf_le hbdd h

/-- **Critical constants of a randomized test.** For any law `P` on `ℝ` and any level
`α ∈ (0,1)` there are a threshold `C` and a boundary weight `γ ∈ [0,1]` with
`P(C,∞) + γ·P{C} = α`: the level `α` can always be attained *exactly* by rejecting above `C`
and randomizing with probability `γ` on the atom at `C`.

This is the existence statement that every "there is a level-`α` test of the following form"
argument needs; the atom term is what makes it an equality rather than an inequality. -/
theorem exists_critical_constants (P : Measure ℝ) [IsProbabilityMeasure P] {α : ℝ}
    -- USER-INPUT: a nondegenerate level; Neyman–Pearson (1933)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C γ : ℝ, 0 ≤ γ ∧ γ ≤ 1 ∧
      (P {x : ℝ | C < x}).toReal + γ * (P {x : ℝ | x = C}).toReal = α := by
  set F : ℝ → ℝ := fun x => cdf P x with hFdef
  have hmono : Monotone F := monotone_cdf (μ := P)
  have hrc : ∀ y, ContinuousWithinAt F (Set.Ici y) y := fun y => (cdf P).right_continuous y
  have hne : {y : ℝ | 1 - α ≤ F y}.Nonempty := by
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop P).eventually_const_lt
        (show 1 - α < 1 by linarith)).exists
    exact ⟨y, le_of_lt hy⟩
  have hbdd : BddBelow {y : ℝ | 1 - α ≤ F y} := by
    obtain ⟨b, hb⟩ := eventually_atBot.mp
      ((tendsto_cdf_atBot P).eventually_lt_const (show (0 : ℝ) < 1 - α by linarith))
    refine ⟨b, fun y hy => ?_⟩
    by_contra h
    push_neg at h
    simp only [Set.mem_setOf_eq] at hy
    exact absurd (hb y h.le) (not_lt.mpr hy)
  set C := quantile F (1 - α) with hCdef
  have hA : 1 - α ≤ F C := (quantile_le_iff hmono hrc hne hbdd).mp le_rfl
  have hB : ∀ y, y < C → F y < 1 - α := by
    intro y hy
    by_contra h
    push_neg at h
    exact absurd ((quantile_le_iff hmono hrc hne hbdd).mpr h) (not_le.mpr hy)
  set L := Function.leftLim F C with hLdef
  have hLle : L ≤ F C := Monotone.leftLim_le hmono le_rfl
  have hLbound : L ≤ 1 - α := by
    have htend : Tendsto F (𝓝[<] C) (𝓝 L) := hmono.tendsto_leftLim C
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hB y hy).le
  have hg : (P {x : ℝ | C < x}).toReal = 1 - F C := by
    have hset : {x : ℝ | C < x} = Set.Ioi C := rfl
    rw [hset, ← measure_cdf (μ := P), (cdf P).measure_Ioi (tendsto_cdf_atTop P) C,
      ENNReal.toReal_ofReal (by linarith [cdf_le_one (μ := P) C])]
  have hj : (P {x : ℝ | x = C}).toReal = F C - L := by
    have hset : {x : ℝ | x = C} = {C} := by ext x; simp
    rw [hset, ← measure_cdf (μ := P), (cdf P).measure_singleton C,
      ENNReal.toReal_ofReal (by linarith [hLle])]
  have hgle : 1 - F C ≤ α := by linarith [hA]
  have hgnn : 0 ≤ 1 - F C := by linarith [cdf_le_one (μ := P) C]
  have hjnn : 0 ≤ F C - L := by linarith [hLle]
  have hαle : α ≤ (1 - F C) + (F C - L) := by linarith [hLbound]
  rcases eq_or_lt_of_le hjnn with hj0 | hjpos
  · refine ⟨C, 0, le_refl _, zero_le_one, ?_⟩
    rw [hg, hj]
    have hval : (1 - F C) = α := le_antisymm hgle (by linarith [hαle, hj0])
    rw [hval]; ring
  · refine ⟨C, (α - (1 - F C)) / (F C - L), div_nonneg (by linarith [hgle]) (le_of_lt hjpos),
      ?_, ?_⟩
    · rw [div_le_one hjpos]; linarith [hαle]
    · rw [hg, hj, div_mul_cancel₀ _ (ne_of_gt hjpos)]; ring

/-- **Inverse-transform sampling**: the quantile function of the distribution function of `P`
pushes the uniform law on `[0,1]` forward to `P`.

The junk values of `quantile` at the endpoints `0` and `1` are irrelevant: they affect the
map on a Lebesgue-null set only. -/
theorem map_quantile_uniform (P : Measure ℝ) [IsProbabilityMeasure P] (F : ℝ → ℝ)
    -- USER-INPUT: `F` is the distribution function of `P`; classical
    (hF : ∀ x : ℝ, F x = (P (Set.Iic x)).toReal) :
    (volume.restrict (Set.Icc (0 : ℝ) 1)).map (quantile F) = P := by
  have hFeq : F = ⇑(cdf P) := by
    funext x; rw [hF, cdf_eq_real]; rfl
  subst hFeq
  have hmono : Monotone ⇑(cdf P) := monotone_cdf (μ := P)
  have hrc : ∀ y, ContinuousWithinAt ⇑(cdf P) (Set.Ici y) y :=
    fun y => (cdf P).right_continuous y
  have hbdd : ∀ a : ℝ, 0 < a → BddBelow {x : ℝ | a ≤ cdf P x} := by
    intro a ha
    obtain ⟨b, hb⟩ := eventually_atBot.mp ((tendsto_cdf_atBot P).eventually_lt_const ha)
    refine ⟨b, fun y hy => ?_⟩
    simp only [Set.mem_setOf_eq] at hy
    by_contra hc; push_neg at hc
    exact absurd (hb y hc.le) (not_lt.mpr hy)
  have hne : ∀ a : ℝ, a < 1 → {x : ℝ | a ≤ cdf P x}.Nonempty := by
    intro a ha
    obtain ⟨y, hy⟩ := ((tendsto_cdf_atTop P).eventually_const_lt ha).exists
    exact ⟨y, hy.le⟩
  have hmonoOn : MonotoneOn (quantile ⇑(cdf P)) (Set.Ioo 0 1) := by
    intro a ha b hb hab
    exact quantile_mono _ hab (hbdd a ha.1) (hne b hb.2)
  have hIccIoo : Set.Icc (0 : ℝ) 1 =ᵐ[volume] Set.Ioo 0 1 := Ioo_ae_eq_Icc.symm
  have haem : AEMeasurable (quantile ⇑(cdf P)) (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    rw [Measure.restrict_congr_set hIccIoo]
    exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo hmonoOn
  haveI : IsFiniteMeasure ((volume.restrict (Set.Icc (0 : ℝ) 1)).map (quantile ⇑(cdf P))) := by
    constructor
    rw [Measure.map_apply_of_aemeasurable haem MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply_univ]
    exact measure_Icc_lt_top
  refine Measure.ext_of_Iic ((volume.restrict (Set.Icc 0 1)).map (quantile ⇑(cdf P))) P
    (fun t => ?_)
  rw [Measure.map_apply_of_aemeasurable haem measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Icc, ← ofReal_cdf P t]
  set a := cdf P t with hadef
  have ha0 : 0 ≤ a := cdf_nonneg P t
  have ha1 : a ≤ 1 := cdf_le_one P t
  -- On `Ioo 0 1` the Galois property turns the quantile preimage into an interval.
  have hstep : (quantile ⇑(cdf P) ⁻¹' Set.Iic t) ∩ Set.Ioo 0 1 = Set.Ioo 0 1 ∩ Set.Iic a := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ioo]
    constructor
    · rintro ⟨hqt, hu⟩
      exact ⟨hu, (quantile_le_iff hmono hrc (hne u hu.2) (hbdd u hu.1)).mp hqt⟩
    · rintro ⟨hu, hle⟩
      exact ⟨(quantile_le_iff hmono hrc (hne u hu.2) (hbdd u hu.1)).mpr hle, hu⟩
  have hcong : ((quantile ⇑(cdf P) ⁻¹' Set.Iic t) ∩ Set.Icc (0 : ℝ) 1 : Set ℝ)
      =ᵐ[volume] (Set.Ioo 0 1 ∩ Set.Iic a : Set ℝ) := by
    refine (Filter.EventuallyEq.inter (ae_eq_refl _) hIccIoo).trans ?_
    rw [hstep]
    exact ae_eq_refl _
  rw [measure_congr hcong]
  -- The interval `Ioo 0 1 ∩ Iic a` has the same volume as `Ioc 0 a`, namely `ofReal a`.
  have hae : (Set.Ioo (0 : ℝ) 1 ∩ Set.Iic a : Set ℝ) =ᵐ[volume] (Set.Ioc (0 : ℝ) a : Set ℝ) := by
    rw [ae_eq_set]
    refine ⟨?_, ?_⟩
    · convert measure_empty (μ := volume)
      rw [Set.diff_eq_empty]
      rintro u ⟨⟨h0, _⟩, hle⟩
      exact ⟨h0, hle⟩
    · refine measure_mono_null ?_ (Real.volume_singleton (a := 1))
      rintro u ⟨⟨h0, hle⟩, hnot⟩
      rw [Set.mem_singleton_iff]
      by_contra hu1
      exact hnot ⟨⟨h0, lt_of_le_of_ne (le_trans hle ha1) hu1⟩, hle⟩
  rw [measure_congr hae, Real.volume_Ioc, sub_zero]

/-- For a strictly increasing `F`, the quantile at an attained level is the attaining point.
The helper that identifies the limit in the two convergence statements below. -/
theorem quantile_eq_of_strictMono {F : ℝ → ℝ} {p q : ℝ}
    -- USER-INPUT: strict monotonicity of the limiting distribution function; classical
    (hF : StrictMono F)
    -- USER-INPUT: the level `p` is attained at `q`; classical
    (hq : F q = p) :
    quantile F p = q := by
  have hL : IsLeast {x : ℝ | p ≤ F x} q := by
    refine ⟨hq.ge, ?_⟩
    intro x hx
    have : F q ≤ F x := by rw [hq]; exact hx
    exact hF.le_iff_le.mp this
  exact hL.csInf_eq

/-- **Deterministic quantile convergence**: if nondecreasing `Fₙ` converge pointwise to a
strictly increasing `F` and the level `p` is attained by `F`, then the `Fₙ`-quantiles converge
to the `F`-quantile.

Neither continuity of `F` nor any tail behaviour of the `Fₙ` is needed: strict monotonicity of
`F` at the target already provides the two-sided bracketing. -/
theorem tendsto_quantile_of_tendsto {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {p q : ℝ}
    -- USER-INPUT: each approximant is a distribution function — nondecreasing; classical
    (hmono : ∀ n, Monotone (Fn n))
    -- USER-INPUT: strict monotonicity of the limiting distribution function; classical
    (hF : StrictMono F)
    -- USER-INPUT: the level `p` is attained at `q`; classical
    (hq : F q = p)
    -- USER-INPUT: pointwise convergence of the distribution functions; classical
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => quantile (Fn n) p) atTop (𝓝 (quantile F p)) := by
  rw [quantile_eq_of_strictMono hF hq, Metric.tendsto_atTop]
  intro ε hε
  set e := ε / 2 with he
  have hepos : 0 < e := by positivity
  have he1 : F (q - e) < p := by have := hF (show q - e < q by linarith); rw [hq] at this; linarith
  have he2 : p < F (q + e) := by have := hF (show q < q + e by linarith); rw [hq] at this; linarith
  have hlowev : ∀ᶠ n in atTop, Fn n (q - e) < p :=
    (hconv (q - e)).eventually_lt_const he1
  have hupev : ∀ᶠ n in atTop, p < Fn n (q + e) :=
    (hconv (q + e)).eventually_const_lt he2
  rw [Filter.eventually_atTop] at hlowev hupev
  obtain ⟨N₁, hN₁⟩ := hlowev
  obtain ⟨N₂, hN₂⟩ := hupev
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hlow : Fn n (q - e) < p := hN₁ n (le_of_max_le_left hn)
  have hup : p < Fn n (q + e) := hN₂ n (le_of_max_le_right hn)
  have hlb : q - e ∈ lowerBounds {x : ℝ | p ≤ Fn n x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra h
    push_neg at h
    have := (hmono n) h.le
    linarith
  have hmemup : (q + e) ∈ {x : ℝ | p ≤ Fn n x} := hup.le
  have h1 : q - e ≤ quantile (Fn n) p := le_csInf ⟨q + e, hmemup⟩ hlb
  have h2 : quantile (Fn n) p ≤ q + e := csInf_le ⟨q - e, hlb⟩ hmemup
  rw [Real.dist_eq]
  have hb : |quantile (Fn n) p - q| ≤ e := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **Quantile convergence in probability** for random distribution functions: if the random
nondecreasing `Fhat n ω` converge in probability, at every fixed argument, to a strictly
increasing `F`, then their `p`-quantiles converge in probability to the `F`-quantile.

The bracketing argument compares measures of nested sets only, so no measurability of
`ω ↦ Fhat n ω x` is assumed. -/
theorem tendstoInMeasure_quantile {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {Fhat : ℕ → Ω → ℝ → ℝ} {F : ℝ → ℝ} {p q : ℝ}
    -- USER-INPUT: each realized approximant is nondecreasing; classical
    (hmono : ∀ (n : ℕ) (ω : Ω), Monotone (Fhat n ω))
    -- USER-INPUT: strict monotonicity of the limiting distribution function; classical
    (hF : StrictMono F)
    -- USER-INPUT: the level `p` is attained at `q`; classical
    (hq : F q = p)
    -- USER-INPUT: pointwise convergence in probability of the random distribution functions
    (hconv : ∀ x : ℝ, TendstoInMeasure μ (fun n ω => Fhat n ω x) atTop (fun _ => F x)) :
    TendstoInMeasure μ (fun n ω => quantile (Fhat n ω) p) atTop (fun _ => quantile F p) := by
  have hqeq : quantile F p = q := quantile_eq_of_strictMono hF hq
  intro ε hε
  simp only [hqeq]
  -- Choose a positive real `e` with `ofReal e < ε`.
  obtain ⟨e, he0, heε⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e < ε := by
    rcases eq_or_ne ε ∞ with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · have hpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' h
      refine ⟨ε.toReal / 2, by positivity, ?_⟩
      calc ENNReal.ofReal (ε.toReal / 2) < ENNReal.ofReal ε.toReal :=
            (ENNReal.ofReal_lt_ofReal_iff hpos).mpr (by linarith)
        _ = ε := ENNReal.ofReal_toReal h
  have e1 : F (q - e) < p := by
    have := hF (show q - e < q by linarith); rw [hq] at this; linarith
  have e2 : p < F (q + e) := by
    have := hF (show q < q + e by linarith); rw [hq] at this; linarith
  -- The two "distribution function off by δ" sets whose measures vanish.
  have h1 : Tendsto (fun n => μ {ω | ENNReal.ofReal (p - F (q - e)) ≤
      edist (Fhat n ω (q - e)) (F (q - e))}) atTop (𝓝 0) := by
    simpa using hconv (q - e) (ENNReal.ofReal (p - F (q - e)))
      (ENNReal.ofReal_pos.mpr (by linarith [e1]))
  have h2 : Tendsto (fun n => μ {ω | ENNReal.ofReal (F (q + e) - p) ≤
      edist (Fhat n ω (q + e)) (F (q + e))}) atTop (𝓝 0) := by
    simpa using hconv (q + e) (ENNReal.ofReal (F (q + e) - p))
      (ENNReal.ofReal_pos.mpr (by linarith [e2]))
  -- Inclusion of the "quantile off by ε" set into the union.
  have hsub : ∀ n, {ω | ε ≤ edist (quantile (Fhat n ω) p) q} ⊆
      {ω | ENNReal.ofReal (p - F (q - e)) ≤ edist (Fhat n ω (q - e)) (F (q - e))} ∪
      {ω | ENNReal.ofReal (F (q + e) - p) ≤ edist (Fhat n ω (q + e)) (F (q + e))} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hgt : e < |quantile (Fhat n ω) p - q| := by
      by_contra hle'
      push_neg at hle'
      have hd : edist (quantile (Fhat n ω) p) q ≤ ENNReal.ofReal e := by
        rw [edist_dist, Real.dist_eq]; exact ENNReal.ofReal_le_ofReal hle'
      exact absurd (le_trans hω hd) (not_le.mpr heε)
    by_cases hleft : p ≤ Fhat n ω (q - e)
    · refine Or.inl ?_
      simp only [Set.mem_setOf_eq]
      rw [edist_dist, Real.dist_eq]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_nonneg (by linarith [e1] : (0 : ℝ) ≤ Fhat n ω (q - e) - F (q - e))]
      linarith
    · push_neg at hleft
      refine Or.inr ?_
      have hR : Fhat n ω (q + e) ≤ p := by
        by_contra hnot
        push_neg at hnot
        have hlb : q - e ∈ lowerBounds {x : ℝ | p ≤ Fhat n ω x} := by
          intro x hx
          simp only [Set.mem_setOf_eq] at hx
          by_contra hc
          push_neg at hc
          exact absurd hx (not_le.mpr (lt_of_le_of_lt ((hmono n ω) hc.le) hleft))
        have hmem : (q + e) ∈ {x : ℝ | p ≤ Fhat n ω x} := hnot.le
        have hle1 : q - e ≤ quantile (Fhat n ω) p := le_csInf ⟨q + e, hmem⟩ hlb
        have hle2 : quantile (Fhat n ω) p ≤ q + e := csInf_le ⟨q - e, hlb⟩ hmem
        have : |quantile (Fhat n ω) p - q| ≤ e := abs_le.mpr ⟨by linarith, by linarith⟩
        exact absurd this (not_le.mpr hgt)
      simp only [Set.mem_setOf_eq]
      rw [edist_dist, Real.dist_eq]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_nonpos (by linarith [e2] : Fhat n ω (q + e) - F (q + e) ≤ 0)]
      linarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using h1.add h2) (fun n => zero_le) (fun n => ?_)
  calc μ {ω | ε ≤ edist (quantile (Fhat n ω) p) q}
      ≤ μ ({ω | ENNReal.ofReal (p - F (q - e)) ≤ edist (Fhat n ω (q - e)) (F (q - e))} ∪
          {ω | ENNReal.ofReal (F (q + e) - p) ≤ edist (Fhat n ω (q + e)) (F (q + e))}) :=
        measure_mono (hsub n)
    _ ≤ _ := measure_union_le _ _

end StatLean.HypothesisTesting
