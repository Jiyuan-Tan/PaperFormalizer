module
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-!
# The Lipschitz class on `[0,1]` and its grid net — Exercise 8.9, part 1

The function class of HDP Eq. (8.24),
$$ \mathcal{F} \;=\; \{ f : [0,1] \to [0,1] \;:\; \|f\|_{\mathrm{Lip}} \le 1 \}, $$
realized as a subset of $C([0,1], \mathbb{R})$ with the uniform ($L^\infty$)
metric, together with the constructive grid net used to bound its covering
numbers: knots $t_j = j/m$, clamped $\pm 1$-step integer paths
$k_0, k_1, \dots, k_m$ (encoded as a start $k_0 \in \{0,\dots,m\}$ and steps in
$\{-1,0,1\}$), and the *cone-envelope* functions
$$ g(x) \;=\; \max\Bigl( \max_{0 \le j \le m}
   \bigl( v_j - |x - t_j| \bigr),\; 0 \Bigr), \qquad
   v_j = \mathrm{clamp}_{[0,1]}(k_j/m). $$
Every parameter choice yields a member of $\mathcal{F}$ (an *internal* net),
and the net has at most $(m+1)\cdot 3^m$ elements.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, Eq. (8.24) and Exercise 8.9.

**Proof formalization notes.** The domain is the subtype `unitInterval`
(compact, so `C(unitInterval, ℝ)` carries the genuine sup metric via
`ContinuousMap.instMetricSpace`); the book's "functions on $[0,1]$" is a
type-level input. The net member is a cone envelope, **not** the book's
piecewise-linear interpolation: 1-Lipschitz-ness is a finite sup of
1-Lipschitz cones (`lipschitzWith_finset_sup'`, a `ForMathlib` promotion
candidate), the range lies in $[0,1]$ by clamping (`gridValue`) plus the outer
`max 0`, and the cardinality bound is `Finset.card_image_le` with no
injectivity argument. Edge behavior: garbage paths (leaving $\{0,\dots,m\}$)
are clamped by `gridValue`, so *every* parameter is a class member and the
count `(m+1)·3^m` is an upper bound only. `coneMap`'s continuity field cites
`lipschitzWith_coneFun`, which is therefore **mandatory-close** for the
work item `hdp-emp-net`; the named-sorry fallback of this file is
`coneFun_mem_Icc`. `zero_mem_lipschitzNet` (the zero function is the
all-clamped-to-zero net member) provides the base point $0 \in T$ for the
Dudley plug in `LipschitzLLN.lean` (Eq. (8.25)).

**Bibliographic comments.** Covering numbers of Lipschitz balls, with the
$\log N(\varepsilon) \asymp 1/\varepsilon$ rate formalized here, are due to
A. N. Kolmogorov and V. M. Tikhomirov, "ε-entropy and ε-capacity of sets in
function spaces," *Uspekhi Mat. Nauk* 14 (1959), 3–86. The step-path
counting argument used here is standard.
-/

open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

/-- **The Lipschitz class** $\mathcal{F}$ of HDP §8.2, Eq. (8.24): continuous
functions on `[0,1]` that are `1`-Lipschitz with values in `[0,1]`, as a set
in `C(unitInterval, ℝ)` (which carries the sup metric — compact domain). Edge
behavior: membership constrains the *bundled* map; the ambient metric on
`C(unitInterval, ℝ)` is the genuine `L∞` distance. -/
def lipschitzUnitClass : Set C(unitInterval, ℝ) :=
  {f | LipschitzWith 1 ⇑f ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1}

/-- The zero function belongs to the class (HDP §8.2 p. 231; base point of
Eq. (8.25)). -/
theorem zero_mem_lipschitzUnitClass : (0 : C(unitInterval, ℝ)) ∈ lipschitzUnitClass := by
  refine ⟨?_, ?_⟩
  · simp only [ContinuousMap.coe_zero]
    exact (LipschitzWith.const (0 : ℝ)).weaken (by norm_num)
  · intro x
    simp only [ContinuousMap.zero_apply]
    exact ⟨le_refl 0, by norm_num⟩

/-- The class has `L∞`-diameter at most `1` (HDP §8.2 p. 231): all members take
values in `[0,1]`. Caps the entropy integral at radius `1`. -/
theorem dist_le_one_of_mem_lipschitzUnitClass {f g : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership of both points; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (hg : g ∈ lipschitzUnitClass) :
    dist f g ≤ 1 := by
  refine ContinuousMap.dist_le (by norm_num) |>.mpr ?_
  intro x
  rw [Real.dist_eq, abs_le]
  have h1 := hf.2 x
  have h2 := hg.2 x
  rw [Set.mem_Icc] at h1 h2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Grid knot** `t_j = j/m` (HDP Exercise 8.9), as a point of
`unitInterval`. Edge behavior: `j ≤ m` always (the index type is
`Fin (m+1)`), so no clamping is needed. -/
noncomputable def gridKnot (m : ℕ) [NeZero m] (j : Fin (m + 1)) : unitInterval :=
  ⟨(j : ℝ) / m,
    ⟨by positivity,
     div_le_one_of_le₀ (by exact_mod_cast Nat.lt_succ_iff.mp j.isLt) (by positivity)⟩⟩

/-- **±1-step integer path** (HDP Exercise 8.9): start `k₀` plus the partial
sums of the steps `step i − 1 ∈ {−1, 0, 1}` up to index `j`. Kept in `ℤ` to
avoid truncated `ℕ`-subtraction; values outside `{0, …, m}` are harmless
(clamped later by `gridValue`). -/
def gridPath (m : ℕ) (k₀ : Fin (m + 1)) (step : Fin m → Fin 3) (j : Fin (m + 1)) : ℤ :=
  (k₀ : ℤ) + ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < (j : ℕ)),
    ((step i : ℤ) - 1)

/-- **Clamped knot value** `clamp_{[0,1]}(k/m)` (HDP Exercise 8.9). Edge
behavior: garbage integers `k ∉ {0, …, m}` are clamped into `[0,1]`, so every
parameter choice below yields a `[0,1]`-valued net member. -/
noncomputable def gridValue (m : ℕ) (k : ℤ) : ℝ := min 1 (max ((k : ℝ) / m) 0)

/-- A finite sup of `K`-Lipschitz functions is `K`-Lipschitz (LEAN-ONLY
helper; induction on `LipschitzWith.max`; `ForMathlib` promotion candidate). -/
theorem lipschitzWith_finset_sup' {ι : Type*} {s : Finset ι}
    -- LEAN-ONLY: nonemptiness required by `Finset.sup'`; no book content
    (hs : s.Nonempty) {K : ℝ≥0} {F : ι → unitInterval → ℝ}
    -- LEAN-ONLY: per-member Lipschitz bound; no book content
    (hF : ∀ i ∈ s, LipschitzWith K (F i)) :
    LipschitzWith K (fun x => s.sup' hs (fun i => F i x)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    have : (fun x => ({a} : Finset ι).sup' (Finset.singleton_nonempty a)
        (fun i => F i x)) = F a := by
      funext x; simp [Finset.sup'_singleton]
    rw [this]; exact hF a (by simp)
  | cons a s ha hs ih =>
    have hkey : (fun x => (Finset.cons a s ha).sup' (Finset.cons_nonempty ha)
        (fun i => F i x)) = fun x => max (F a x) (s.sup' hs (fun i => F i x)) := by
      funext x
      rw [Finset.sup'_cons]
    rw [hkey]
    have hla : LipschitzWith K (F a) := hF a (by simp)
    have hls : LipschitzWith K (fun x => s.sup' hs (fun i => F i x)) :=
      ih (fun i hi => hF i (by simp [hi]))
    have := hla.max hls
    rwa [max_self] at this

/-- **Cone-envelope net function** (HDP Exercise 8.9): the max of the cones
`x ↦ v_j − |x − t_j|` over all knots, floored at `0`, where
`v_j = gridValue m (gridPath m k₀ step j)`. Edge behavior: the outer `max 0`
and the clamped values keep the range in `[0,1]` for *every* parameter, so
the net is internal; garbage paths yield valid (if useless) class members. -/
noncomputable def coneFun (m : ℕ) [NeZero m] (k₀ : Fin (m + 1))
    (step : Fin m → Fin 3) (x : unitInterval) : ℝ :=
  max (Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin (m + 1) => gridValue m (gridPath m k₀ step j) - |(x : ℝ) - (j : ℝ) / m|)) 0

/-- Net members are `1`-Lipschitz (HDP Exercise 8.9): a finite max of
`1`-Lipschitz cones is `1`-Lipschitz. MANDATORY-CLOSE for `hdp-emp-net`:
`coneMap`'s continuity field cites this lemma. -/
theorem lipschitzWith_coneFun (m : ℕ) [NeZero m] (k₀ : Fin (m + 1))
    (step : Fin m → Fin 3) :
    LipschitzWith 1 (coneFun m k₀ step) := by
  unfold coneFun
  have hinner : ∀ j : Fin (m + 1), LipschitzWith 1
      (fun x : unitInterval => gridValue m (gridPath m k₀ step j) - |(x : ℝ) - (j : ℝ) / m|) := by
    intro j
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    have hxy : dist x y = |(x : ℝ) - (y : ℝ)| := by rw [Subtype.dist_eq, Real.dist_eq]
    rw [hxy]
    have heq : (gridValue m (gridPath m k₀ step j) - |(x : ℝ) - (j : ℝ) / m|)
        - (gridValue m (gridPath m k₀ step j) - |(y : ℝ) - (j : ℝ) / m|)
        = |(y : ℝ) - (j : ℝ) / m| - |(x : ℝ) - (j : ℝ) / m| := by ring
    rw [heq]
    have hbound := abs_abs_sub_abs_le_abs_sub
      ((y : ℝ) - (j : ℝ) / m) ((x : ℝ) - (j : ℝ) / m)
    have hrw : ((y : ℝ) - (j : ℝ) / m) - ((x : ℝ) - (j : ℝ) / m) = (y : ℝ) - (x : ℝ) := by ring
    rw [hrw] at hbound
    rw [abs_sub_comm (y : ℝ) (x : ℝ)] at hbound
    exact hbound
  have hsup : LipschitzWith 1
      (fun x : unitInterval => Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m + 1) =>
          gridValue m (gridPath m k₀ step j) - |(x : ℝ) - (j : ℝ) / m|)) :=
    lipschitzWith_finset_sup' Finset.univ_nonempty (fun j _ => hinner j)
  have hconst : LipschitzWith 1 (fun _ : unitInterval => (0 : ℝ)) :=
    (LipschitzWith.const (0 : ℝ)).weaken zero_le_one
  have := hsup.max hconst
  rw [max_self] at this
  exact this

/-- Net members take values in `[0,1]` (HDP Exercise 8.9): clamping of knot
values plus the outer `max 0`. Named-sorry fallback of `hdp-emp-net`. -/
theorem coneFun_mem_Icc (m : ℕ) [NeZero m] (k₀ : Fin (m + 1))
    (step : Fin m → Fin 3) (x : unitInterval) :
    coneFun m k₀ step x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold coneFun
  rw [Set.mem_Icc]
  refine ⟨le_max_right _ _, ?_⟩
  apply max_le _ (by norm_num)
  apply Finset.sup'_le
  intro j _
  have hv : gridValue m (gridPath m k₀ step j) ≤ 1 := min_le_left _ _
  have habs : (0 : ℝ) ≤ |(x : ℝ) - (j : ℝ) / m| := abs_nonneg _
  linarith

/-- The cone envelope as a bundled continuous map (LEAN-ONLY bundling; the
continuity field cites `lipschitzWith_coneFun`). -/
noncomputable def coneMap (m : ℕ) [NeZero m] (k₀ : Fin (m + 1))
    (step : Fin m → Fin 3) : C(unitInterval, ℝ) :=
  ⟨coneFun m k₀ step, (lipschitzWith_coneFun m k₀ step).continuous⟩

open Classical in
/-- **The grid net** (HDP Exercise 8.9): the image of all `(start, steps)`
parameters under `coneMap`, as a `Finset` of `C(unitInterval, ℝ)`
(`Classical.decEq` for the image). Edge behavior: distinct parameters may
collide (clamping); only the upper bound `(m+1)·3^m` on the cardinality is
claimed. -/
noncomputable def lipschitzNet (m : ℕ) [NeZero m] : Finset C(unitInterval, ℝ) :=
  Finset.image (fun p : Fin (m + 1) × (Fin m → Fin 3) => coneMap m p.1 p.2) Finset.univ

/-- Every cone envelope is in the net (LEAN-ONLY `mem_image` witness). -/
theorem coneMap_mem_lipschitzNet (m : ℕ) [NeZero m] (k₀ : Fin (m + 1))
    (step : Fin m → Fin 3) :
    coneMap m k₀ step ∈ lipschitzNet m := by
  classical
  exact Finset.mem_image.mpr ⟨(k₀, step), Finset.mem_univ _, rfl⟩

/-- The net is **internal**: `N ⊆ F` (HDP Exercise 8.9; required by our
`IsEpsilonNet` / `Metric.coveringNumber` conventions). -/
theorem lipschitzNet_subset (m : ℕ) [NeZero m] :
    ↑(lipschitzNet m) ⊆ lipschitzUnitClass := by
  classical
  intro f hf
  rw [Finset.mem_coe, lipschitzNet, Finset.mem_image] at hf
  obtain ⟨p, _, rfl⟩ := hf
  exact ⟨lipschitzWith_coneFun m p.1 p.2, fun x => coneFun_mem_Icc m p.1 p.2 x⟩

/-- The net is nonempty (LEAN-ONLY; image of a nonempty parameter space). -/
theorem lipschitzNet_nonempty (m : ℕ) [NeZero m] : (lipschitzNet m).Nonempty := by
  classical
  exact Finset.univ_nonempty.image _

/-- The zero function is a net member (all knot values clamped to `0`): take
`k₀ = 0` and all steps `0` — the envelope `max(sup_j (0 − |x − t_j|), 0)` is
identically `0`. Provides the base point `0 ∈ T` for the Dudley plug in
`LipschitzLLN.lean` (HDP §8.2, Eq. (8.25)). -/
theorem zero_mem_lipschitzNet (m : ℕ) [NeZero m] :
    (0 : C(unitInterval, ℝ)) ∈ lipschitzNet m := by
  classical
  have hcm := coneMap_mem_lipschitzNet m 0 (fun _ => (0 : Fin 3))
  have heq : (0 : C(unitInterval, ℝ)) = coneMap m 0 (fun _ => (0 : Fin 3)) := by
    apply ContinuousMap.ext
    intro x
    rw [ContinuousMap.zero_apply]
    symm
    change coneFun m 0 (fun _ => (0 : Fin 3)) x = 0
    unfold coneFun
    -- each gridPath value is ≤ 0, so gridValue = 0, so each cone ≤ 0, sup' ≤ 0, max with 0 = 0
    have hpath : ∀ j : Fin (m + 1), gridPath m 0 (fun _ => (0 : Fin 3)) j ≤ 0 := by
      intro j
      unfold gridPath
      simp only [Fin.val_zero, Nat.cast_zero, zero_add]
      apply Finset.sum_nonpos
      intro i _
      norm_num
    have hval : ∀ j : Fin (m + 1), gridValue m (gridPath m 0 (fun _ => (0 : Fin 3)) j) = 0 := by
      intro j
      unfold gridValue
      have hle : (gridPath m 0 (fun _ => (0 : Fin 3)) j : ℝ) / m ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · exact_mod_cast hpath j
        · positivity
      rw [max_eq_right hle, min_eq_right (by norm_num)]
    have hsup_le : Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (m + 1) => gridValue m (gridPath m 0 (fun _ => (0 : Fin 3)) j)
          - |(x : ℝ) - (j : ℝ) / m|) ≤ 0 := by
      apply Finset.sup'_le
      intro j _
      rw [hval j]
      simp only [zero_sub, neg_nonpos]
      exact abs_nonneg _
    exact max_eq_right hsup_le
  rw [heq]
  exact hcm

/-- Cardinality bound `#N ≤ (m+1)·3^m` (HDP Exercise 8.9): starts times
step-sequences, via `Finset.card_image_le`. -/
theorem card_lipschitzNet_le (m : ℕ) [NeZero m] :
    (lipschitzNet m).card ≤ (m + 1) * 3 ^ m := by
  classical
  calc (lipschitzNet m).card
      ≤ (Finset.univ : Finset (Fin (m + 1) × (Fin m → Fin 3))).card :=
        Finset.card_image_le
    _ = (m + 1) * 3 ^ m := by
        rw [Finset.card_univ]
        simp [Fintype.card_prod, Fintype.card_fin]

end StatLean.ConcentrationInequalities
