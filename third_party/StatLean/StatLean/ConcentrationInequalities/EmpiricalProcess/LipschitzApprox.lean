module
public import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzNet
public import StatLean.ConcentrationInequalities.Maximal.CoveringNumbers
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-!
# Lipschitz approximation by the grid net — Exercise 8.9, part 2

Every member $f$ of the Lipschitz class $\mathcal{F}$ (HDP Eq. (8.24)) is
within $L^\infty$-distance $3/m$ of the cone envelope built from its
floor-snapped knot values:
$$ \Bigl\| f - \mathrm{cone}\bigl(\lfloor m f(t_j) \rfloor / m\bigr)
   \Bigr\|_\infty \;\le\; \frac{3}{m},
   \qquad t_j = \frac{j}{m}, $$
packaged as: the grid net `lipschitzNet m` is an $\varepsilon$-net of
$\mathcal{F}$ whenever $m \ge 3/\varepsilon$.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, Exercise 8.9.

**Proof formalization notes.** Approximation error $3/m$ (not the optimal
$2/m$): floor-knot error $1/m$ (we snap $x$ to $\lfloor mx \rfloor / m$, a
simpler `Nat.floor` proof than nearest-knot) + value-snap error $1/m$
($k_j = \lfloor m f(t_j) \rfloor$, so $0 \le f(t_j) - k_j/m < 1/m$) + cone
offset $1/m$. The $\pm 1$-step property of the snapped values comes from
1-Lipschitz-ness + `Nat.floor_add_one`; the reconstruction of the snapped
values as a `gridPath` is a telescoping induction kept entirely in `ℤ` (no
truncated `ℕ`-subtraction). `snapStep` decodes the increment
$k_{i+1} - k_i + 1 \in \{0,1,2\}$ by trichotomy; on non-class members the
clamps make it total but carry no claim (`gridPath_snapStep_eq` is stated
only for class members). Covering is closed via our `IsEpsilonNet` bridge
(`IsEpsilonNet.isCover` + `Metric.IsCover.coveringNumber_le_encard`) — not
the packing route. Named-sorry fallback of the work item `hdp-emp-approx`:
`exists_mem_lipschitzNet_dist_le` (all downstream statements compile against
it).

**Bibliographic comments.** The knot-snapping argument is the classical
Kolmogorov–Tikhomirov (1959) upper bound for the ε-entropy of Lipschitz
balls.
-/

open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

/-- Every point of `[0,1]` is within `1/m` of a grid knot (take
`j = ⌊m·x⌋₊`); HDP Exercise 8.9. -/
theorem exists_gridKnot_dist_le (m : ℕ) [NeZero m] (x : unitInterval) :
    ∃ j : Fin (m + 1), |(x : ℝ) - (j : ℝ) / m| ≤ 1 / m := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hx0 : 0 ≤ (x : ℝ) := unitInterval.nonneg x
  have hx1 : (x : ℝ) ≤ 1 := unitInterval.le_one x
  have hmx : (0 : ℝ) ≤ (m : ℝ) * x := by positivity
  -- `n = ⌊m·x⌋₊` fits in `Fin (m+1)`.
  have hle : ⌊(m : ℝ) * x⌋₊ ≤ m := by
    calc ⌊(m : ℝ) * x⌋₊ ≤ ⌊(m : ℝ)⌋₊ :=
          Nat.floor_mono (by nlinarith [Nat.cast_nonneg (α := ℝ) m])
      _ = m := Nat.floor_natCast m
  refine ⟨⟨⌊(m : ℝ) * x⌋₊, Nat.lt_succ_of_le hle⟩, ?_⟩
  set n := ⌊(m : ℝ) * x⌋₊ with hn
  have h1 : (n : ℝ) ≤ (m : ℝ) * x := Nat.floor_le hmx
  have h2 : (m : ℝ) * x < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hnn : 0 ≤ (x : ℝ) - (n : ℝ) / m := by
    rw [sub_nonneg, div_le_iff₀ hm]; nlinarith
  rw [abs_of_nonneg hnn]
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hm]
  nlinarith

/-- **Snapped knot values** `k_j = ⌊m·f(t_j)⌋₊` (HDP Exercise 8.9). Edge
behavior: `Nat.floor` sends negative reals to `0`, harmless since class
members are nonnegative; for `f ∉ 𝓕` the value is total garbage but never
used. -/
noncomputable def snapPath (m : ℕ) [NeZero m] (f : C(unitInterval, ℝ))
    (j : Fin (m + 1)) : ℕ :=
  ⌊(m : ℝ) * f (gridKnot m j)⌋₊

/-- The snapped start `k₀`, clamped into `Fin (m+1)` (LEAN-ONLY total clamp;
the clamp is the identity on class members since `k₀ ≤ m` by `snapPath_le`). -/
noncomputable def snapStart (m : ℕ) [NeZero m] (f : C(unitInterval, ℝ)) :
    Fin (m + 1) :=
  ⟨min (snapPath m f 0) m, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- The snapped step sequence: encodes `k_{i+1} − k_i + 1 ∈ {0,1,2}` by
trichotomy in `ℤ` (HDP Exercise 8.9). Edge behavior: total on all of
`C(unitInterval, ℝ)`; increments of magnitude `≥ 2` (impossible on class
members by `snapPath_step_le`) are clamped to the extreme codes `0` / `2`. -/
noncomputable def snapStep (m : ℕ) [NeZero m] (f : C(unitInterval, ℝ))
    (i : Fin m) : Fin 3 :=
  if (snapPath m f i.succ : ℤ) < (snapPath m f i.castSucc : ℤ) then 0
  else if (snapPath m f i.succ : ℤ) = (snapPath m f i.castSucc : ℤ) then 1
  else 2

/-- Snapped values stay in `{0, …, m}` on the class (from `f ≤ 1`);
HDP Exercise 8.9. -/
theorem snapPath_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    snapPath m f j ≤ m := by
  simp only [snapPath]
  have hy1 : f (gridKnot m j) ≤ 1 := (hf.2 _).2
  have hy0 : 0 ≤ f (gridKnot m j) := (hf.2 _).1
  have h : (m : ℝ) * f (gridKnot m j) ≤ (m : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  calc ⌊(m : ℝ) * f (gridKnot m j)⌋₊ ≤ ⌊(m : ℝ)⌋₊ := Nat.floor_mono h
    _ = m := Nat.floor_natCast m

/-- Value-snap error: `|f(t_j) − k_j/m| ≤ 1/m` (HDP Exercise 8.9). -/
theorem abs_snapPath_sub_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership (nonnegativity feeds `Nat.floor`); HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    |f (gridKnot m j) - (snapPath m f j : ℝ) / m| ≤ 1 / m := by
  simp only [snapPath]
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hy0 : 0 ≤ f (gridKnot m j) := (hf.2 _).1
  have hmy : (0 : ℝ) ≤ (m : ℝ) * f (gridKnot m j) := by positivity
  have h1 : (⌊(m : ℝ) * f (gridKnot m j)⌋₊ : ℝ) ≤ (m : ℝ) * f (gridKnot m j) :=
    Nat.floor_le hmy
  have h2 : (m : ℝ) * f (gridKnot m j) < (⌊(m : ℝ) * f (gridKnot m j)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hy_eq : f (gridKnot m j) - (⌊(m : ℝ) * f (gridKnot m j)⌋₊ : ℝ) / m
      = ((m : ℝ) * f (gridKnot m j) - ⌊(m : ℝ) * f (gridKnot m j)⌋₊) / m := by
    field_simp
  rw [hy_eq, abs_div, abs_of_pos hm]
  gcongr
  rw [abs_le]; constructor <;> linarith

/-- Floor lower bound: `k_j/m ≤ f(t_j)` (HDP Exercise 8.9). -/
theorem snapPath_div_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    (snapPath m f j : ℝ) / m ≤ f (gridKnot m j) := by
  simp only [snapPath]
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hy0 : 0 ≤ f (gridKnot m j) := (hf.2 _).1
  have h1 : (⌊(m : ℝ) * f (gridKnot m j)⌋₊ : ℝ) ≤ (m : ℝ) * f (gridKnot m j) :=
    Nat.floor_le (by positivity)
  rw [div_le_iff₀ hm]; nlinarith

/-- **±1-step property**: consecutive snapped values differ by at most `1`
(1-Lipschitz on a `1/m` grid + `Nat.floor_add_one`); HDP Exercise 8.9. -/
theorem snapPath_step_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership (the 1-Lipschitz bound); HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (i : Fin m) :
    |((snapPath m f i.succ : ℤ) - (snapPath m f i.castSucc : ℤ))| ≤ 1 := by
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  -- Knot values.
  set ya := f (gridKnot m i.succ) with hya
  set yb := f (gridKnot m i.castSucc) with hyb
  have hyb0 : 0 ≤ (m : ℝ) * yb := by
    have : 0 ≤ yb := (hf.2 _).1
    positivity
  -- 1-Lipschitz-ness on the `1/m`-spaced knots.
  have hLip : |ya - yb| ≤ 1 / m := by
    have h := hf.1.dist_le_mul (gridKnot m i.succ) (gridKnot m i.castSucc)
    simp only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_one, one_mul] at h
    rw [← hya, ← hyb] at h
    have hpos : (0 : ℝ) ≤ ((i : ℝ) + 1) / m - (i : ℝ) / m := by
      rw [show ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m from by ring]; positivity
    have hrhs : |((gridKnot m i.succ : unitInterval) : ℝ)
        - ((gridKnot m i.castSucc : unitInterval) : ℝ)| = 1 / m := by
      rw [show ((gridKnot m i.succ : unitInterval) : ℝ) = (i.succ : ℝ) / m from rfl,
        show ((gridKnot m i.castSucc : unitInterval) : ℝ) = (i.castSucc : ℝ) / m from rfl]
      have ha : ((i.succ : Fin (m + 1)) : ℝ) = (i : ℝ) + 1 := by simp [Fin.val_succ]
      have hb : ((i.castSucc : Fin (m + 1)) : ℝ) = (i : ℝ) := by simp [Fin.coe_castSucc]
      rw [ha, hb, abs_of_nonneg hpos]; ring
    rwa [hrhs] at h
  have habs : |(m : ℝ) * ya - (m : ℝ) * yb| ≤ 1 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ))]
    calc (m : ℝ) * |ya - yb| ≤ (m : ℝ) * (1 / m) := by gcongr
      _ = 1 := by field_simp
  rw [abs_le] at habs
  -- floor difference from real difference
  have hA : (⌊(m : ℝ) * ya⌋₊ : ℤ) ≤ (⌊(m : ℝ) * yb⌋₊ : ℤ) + 1 := by
    have : ⌊(m : ℝ) * ya⌋₊ ≤ ⌊(m : ℝ) * yb + 1⌋₊ := Nat.floor_mono (by linarith [habs.2])
    rw [Nat.floor_add_one hyb0] at this
    exact_mod_cast this
  have hyaB : 0 ≤ (m : ℝ) * ya := by
    have : 0 ≤ ya := (hf.2 _).1
    positivity
  have hB : (⌊(m : ℝ) * yb⌋₊ : ℤ) ≤ (⌊(m : ℝ) * ya⌋₊ : ℤ) + 1 := by
    have : ⌊(m : ℝ) * yb⌋₊ ≤ ⌊(m : ℝ) * ya + 1⌋₊ := Nat.floor_mono (by linarith [habs.1])
    rw [Nat.floor_add_one hyaB] at this
    exact_mod_cast this
  simp only [snapPath, ← hya, ← hyb]
  rw [abs_le]
  omega

/-- The grid path at the start index is the start value (empty filter). -/
private lemma gridPath_zero (m : ℕ) (k₀ : Fin (m + 1)) (step : Fin m → Fin 3) :
    gridPath m k₀ step 0 = (k₀ : ℤ) := by
  simp [gridPath]

/-- One-step recurrence for the grid path. -/
private lemma gridPath_succ (m : ℕ) (k₀ : Fin (m + 1)) (step : Fin m → Fin 3)
    (i : Fin m) :
    gridPath m k₀ step i.succ = gridPath m k₀ step i.castSucc + ((step i : ℤ) - 1) := by
  simp only [gridPath]
  rw [add_assoc]
  congr 1
  have hnotmem : i ∉ Finset.univ.filter (fun x : Fin m => (x : ℕ) < (i.castSucc : ℕ)) := by
    simp [Fin.coe_castSucc]
  have hins : Finset.univ.filter (fun x : Fin m => (x : ℕ) < (i.succ : ℕ))
      = insert i (Finset.univ.filter (fun x : Fin m => (x : ℕ) < (i.castSucc : ℕ))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.coe_castSucc]
    constructor
    · intro hx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | h)
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt h
  rw [hins, Finset.sum_insert hnotmem]
  ring

/-- Decode the snapped step into the exact integer increment. -/
private lemma snapStep_decode (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    (hf : f ∈ lipschitzUnitClass) (i : Fin m) :
    ((snapStep m f i : ℤ)) - 1
      = (snapPath m f i.succ : ℤ) - (snapPath m f i.castSucc : ℤ) := by
  have hstep := snapPath_step_le m hf i
  rw [abs_le] at hstep
  obtain ⟨hlo, hhi⟩ := hstep
  simp only [snapStep]
  split_ifs with h1 h2
  · have e0 : ((0 : Fin 3) : ℤ) = 0 := rfl
    rw [e0]; omega
  · have e1 : ((1 : Fin 3) : ℤ) = 1 := rfl
    rw [e1]; omega
  · have e2 : ((2 : Fin 3) : ℤ) = 2 := rfl
    rw [e2]; omega

/-- **Path reconstruction**: the grid path driven by the snapped start and
steps recovers the snapped values exactly (telescoping induction in `ℤ`);
HDP Exercise 8.9. -/
theorem gridPath_snapStep_eq (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership (rules out clamping in `snapStart`/`snapStep`); HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    gridPath m (snapStart m f) (snapStep m f) j = (snapPath m f j : ℤ) := by
  refine Fin.induction ?_ ?_ j
  · rw [gridPath_zero]
    have hval : (snapStart m f : ℕ) = snapPath m f 0 := min_eq_left (snapPath_le m hf 0)
    exact_mod_cast hval
  · intro i ih
    rw [gridPath_succ, ih, snapStep_decode m hf i]
    ring

/-- `gridValue` of a snapped value is `k_j/m` (clamps are the identity). -/
private lemma gridValue_snap_eq (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    (hf : f ∈ lipschitzUnitClass) (j : Fin (m + 1)) :
    gridValue m (snapPath m f j : ℤ) = (snapPath m f j : ℝ) / m := by
  unfold gridValue
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  push_cast
  have hnn : 0 ≤ (snapPath m f j : ℝ) / m := by positivity
  have hle : (snapPath m f j : ℝ) / m ≤ 1 := by
    rw [div_le_one hm]; exact_mod_cast snapPath_le m hf j
  rw [max_eq_left hnn, min_eq_right hle]

/-- Rewrite the snapped cone envelope in terms of the snapped values. -/
private lemma coneFun_eq_snap (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    (hf : f ∈ lipschitzUnitClass) (x : unitInterval) :
    coneFun m (snapStart m f) (snapStep m f) x
      = max (Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m + 1) => (snapPath m f j : ℝ) / m - |(x : ℝ) - (j : ℝ) / m|)) 0 := by
  unfold coneFun
  have hfun : (fun j : Fin (m + 1) =>
        gridValue m (gridPath m (snapStart m f) (snapStep m f) j) - |(x : ℝ) - (j : ℝ) / m|)
      = (fun j : Fin (m + 1) => (snapPath m f j : ℝ) / m - |(x : ℝ) - (j : ℝ) / m|) := by
    funext j
    rw [gridPath_snapStep_eq m hf j, gridValue_snap_eq m hf j]
  rw [hfun]

/-- 1-Lipschitz bound between `f x` and the knot value `f(t_j)`. -/
private lemma abs_f_sub_knot_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    (hf : f ∈ lipschitzUnitClass) (x : unitInterval) (j : Fin (m + 1)) :
    |f x - f (gridKnot m j)| ≤ |(x : ℝ) - (j : ℝ) / m| := by
  have h := hf.1.dist_le_mul x (gridKnot m j)
  simp only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_one, one_mul] at h
  rw [show ((gridKnot m j : unitInterval) : ℝ) = (j : ℝ) / m from rfl] at h
  exact h

/-- Lower envelope bound: the snapped cone envelope sits below `f`
(each cone `v_j − |x − t_j|` is under the graph of a 1-Lipschitz `f` with
`v_j ≤ f(t_j)`); HDP Exercise 8.9. -/
theorem coneFun_snap_le (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (x : unitInterval) :
    coneFun m (snapStart m f) (snapStep m f) x ≤ f x := by
  rw [coneFun_eq_snap m hf x]
  apply max_le
  · rw [Finset.sup'_le_iff]
    intro j _
    have h1 : (snapPath m f j : ℝ) / m ≤ f (gridKnot m j) := snapPath_div_le m hf j
    have habs := abs_f_sub_knot_le m hf x j
    rw [abs_le] at habs
    linarith [habs.1]
  · exact (hf.2 x).1

/-- Upper envelope bound: `f ≤ cone + 3/m` (floor-knot `1/m` + value-snap
`1/m` + cone offset `1/m`); HDP Exercise 8.9. -/
theorem le_coneFun_snap_add (m : ℕ) [NeZero m] {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (x : unitInterval) :
    f x ≤ coneFun m (snapStart m f) (snapStep m f) x + 3 / m := by
  rw [coneFun_eq_snap m hf x]
  obtain ⟨j, hj⟩ := exists_gridKnot_dist_le m x
  have habs := abs_f_sub_knot_le m hf x j
  rw [abs_le] at habs
  have hval := abs_snapPath_sub_le m hf j
  rw [abs_le] at hval
  have hterm : (snapPath m f j : ℝ) / m - |(x : ℝ) - (j : ℝ) / m|
      ≤ max (Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (m + 1) => (snapPath m f j : ℝ) / m - |(x : ℝ) - (j : ℝ) / m|)) 0 := by
    refine le_trans ?_ (le_max_left _ _)
    exact Finset.le_sup' (fun j : Fin (m + 1) =>
      (snapPath m f j : ℝ) / m - |(x : ℝ) - (j : ℝ) / m|) (Finset.mem_univ j)
  have hm3 : (3 : ℝ) / m = 1 / m + 1 / m + 1 / m := by ring
  linarith [hterm, hj, habs.1, habs.2, hval.1, hval.2]

/-- **Approximation lemma** (HDP Exercise 8.9): every class member is within
`L∞`-distance `3/m` of a net member (via `ContinuousMap.dist_le`).
Named-sorry fallback of `hdp-emp-approx`. -/
theorem exists_mem_lipschitzNet_dist_le (m : ℕ) [NeZero m]
    {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) :
    ∃ g ∈ lipschitzNet m, dist f g ≤ 3 / m := by
  refine ⟨coneMap m (snapStart m f) (snapStep m f),
    coneMap_mem_lipschitzNet m _ _, ?_⟩
  have hm : (0 : ℝ) ≤ 3 / m := by positivity
  rw [ContinuousMap.dist_le hm]
  intro x
  rw [Real.dist_eq]
  have h1 := coneFun_snap_le m hf x
  have h2 := le_coneFun_snap_add m hf x
  have hcm : (coneMap m (snapStart m f) (snapStep m f)) x
      = coneFun m (snapStart m f) (snapStep m f) x := rfl
  rw [hcm, abs_le]
  constructor <;> linarith

/-- **ε-net form** (HDP Exercise 8.9): for `m ≥ 3/ε` the grid net is an
internal ε-net of the Lipschitz class. -/
theorem isEpsilonNet_lipschitzNet {ε : ℝ}
    -- USER-INPUT: positive radius; HDP Exercise 8.9
    (hε : 0 < ε) {m : ℕ} [NeZero m]
    -- LEAN-ONLY: mesh fine enough for the 3/m approximation; no scope change
    (hm : 3 / ε ≤ (m : ℝ)) :
    IsEpsilonNet (↑(lipschitzNet m)) lipschitzUnitClass ε := by
  refine ⟨lipschitzNet_subset m, ?_⟩
  intro f hf
  obtain ⟨g, hg, hd⟩ := exists_mem_lipschitzNet_dist_le m hf
  refine ⟨g, hg, le_trans hd ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  rw [div_le_iff₀ hmpos, mul_comm]
  rwa [div_le_iff₀ hε] at hm

end StatLean.ConcentrationInequalities
