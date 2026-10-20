module
public import StatLean.ConcentrationInequalities.EmpiricalProcess.Defs
public import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzNet
public import StatLean.ConcentrationInequalities.EmpiricalProcess.LipschitzApprox

@[expose] public section

/-!
# Full-supremum honesty for the Lipschitz class — dense reduction chain

The deterministic, per-$\omega$ reduction of the supremum of $|X_f|$ over the
**genuine uncountable** $L$-Lipschitz class to a monotone limit of finite
maxima:
$$ \sup_{\|f\|_{\mathrm{Lip}} \le L} |X_f|
   \;\overset{\text{R1}}{=}\; L \sup_{\|f\|_{\mathrm{Lip}} \le 1} |X_f|
   \;\overset{\text{R2}}{=}\; L \sup_{f \in \mathcal{F}} |X_f|
   \;\overset{\text{R3}}{=}\; L \sup_{m \in \mathbb{N}}
      \max_{g \in N_m} |X_g|, $$
where $\mathcal{F}$ is the $[0,1]$-valued class (8.24) and $N_m$ is the
monotone finite exhaustion `lipschitzNetUnion m` of a countable
$L^\infty$-dense subfamily. No `Countable` hypothesis appears anywhere: the
recovery is deterministic, exactly as the fixed measurability/sup policy
prescribes.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, proof of Theorem 8.2.3, p. 230 (the two
"(Why?)" reductions to the class (8.24)) and Exercise 8.9 (density rate).

**Proof formalization notes.** All lemmas here are pointwise identities in
`ω`; no measure on `Ω` is involved. R1 (scaling) uses the bijection
`g ↦ L • g` with `empiricalProcess_const_mul`, `lipschitzWith_smul`, and
`Monotone.map_ciSup_of_continuousAt`; the degenerate `L = 0` case (0-Lipschitz
= constants, `X_const = 0`) is a separate lemma. R2 (translation) uses
`h := g − min g` (the min is attained: `g` continuous on the compact
`unitInterval`), `empiricalProcess_add_const` (`[NeZero n]`), and the range
bound from 1-Lipschitz-ness + `diam [0,1] ≤ 1`. R3 (dense net) uses the
deterministic oscillation bound `|X_f − X_g| ≤ 2 · dist f g`
(`abs_empiricalProcess_sub_le` + `ContinuousMap.dist_apply_le_dist`), density
`3/(m+1)` (`exists_mem_lipschitzNetUnion_dist_le`), and an ε-of-room
argument; `ℝ` is conditionally complete, so every `⨆` step carries explicit
`BddAbove` side conditions (`bddAbove_range_abs_empiricalProcess`, from
`|X_f| ≤ 2`). Edge behavior: `lipschitzNetUnion m` uses meshes `j + 1` so
every `lipschitzNet` call has its `NeZero` instance. Named-sorry fallback of
the work item `hdp-emp-dense`: `iSup_abs_empiricalProcess_eq_iSup_netUnion`
(R3; the R1/R2 rewrites must close for real).

**Bibliographic comments.** Reduction to a countable dense subclass is the
classical device for measurability of empirical suprema, systematized in
R. M. Dudley, *Uniform Central Limit Theorems*, Cambridge, 1999, §5.3, and
van der Vaart–Wellner, *Weak Convergence and Empirical Processes*, Springer,
1996, §1.7; this file makes the usually-suppressed argument explicit.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure unitInterval} {n : ℕ} {X : Fin n → Ω → unitInterval}

open Classical in
/-- **Monotone finite exhaustion** of a countable `L∞`-dense subfamily of the
class (8.24): the union of the grid nets of mesh `1, …, m+1` (HDP §8.1
footnote p. 227 / Exercise 8.9). Edge behavior: meshes are `j + 1 ≥ 1`, so
`NeZero` instances are automatic; the union is monotone in `m` by
construction. -/
noncomputable def lipschitzNetUnion (m : ℕ) : Finset C(unitInterval, ℝ) :=
  (Finset.range (m + 1)).biUnion (fun j => lipschitzNet (j + 1))

/-- A continuous function on the compact `unitInterval` is integrable for the
probability measure `P` (LEAN-ONLY regularity; bounded ⇒ integrable). -/
private theorem cont_integrable [IsProbabilityMeasure P]
    (f : C(unitInterval, ℝ)) : Integrable ⇑f P := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := unitInterval)).exists_bound_of_continuousOn
    f.continuous.continuousOn
  refine Integrable.mono' (integrable_const C) f.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs] using hC x (Set.mem_univ x)

/-- A Lipschitz plain function on `unitInterval` is integrable for `P`. -/
private theorem lip_integrable [IsProbabilityMeasure P] {K : ℝ≥0}
    {f : unitInterval → ℝ} (hf : LipschitzWith K f) : Integrable f P :=
  cont_integrable (P := P) ⟨f, hf.continuous⟩

/-- The exhaustion is nonempty (LEAN-ONLY; each grid net is nonempty). -/
theorem lipschitzNetUnion_nonempty (m : ℕ) : (lipschitzNetUnion m).Nonempty := by
  classical
  refine Finset.biUnion_nonempty.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos m), ?_⟩
  exact lipschitzNet_nonempty 1

/-- The exhaustion is internal: `N_m ⊆ 𝓕` (LEAN-ONLY; each grid net is). -/
theorem lipschitzNetUnion_subset (m : ℕ) :
    ↑(lipschitzNetUnion m) ⊆ lipschitzUnitClass := by
  classical
  intro f hf
  rw [Finset.mem_coe, lipschitzNetUnion, Finset.mem_biUnion] at hf
  obtain ⟨j, _, hj⟩ := hf
  exact lipschitzNet_subset (j + 1) (Finset.mem_coe.mpr hj)

/-- The exhaustion is monotone (LEAN-ONLY; `biUnion` over a growing range). -/
theorem lipschitzNetUnion_mono : Monotone lipschitzNetUnion := by
  classical
  intro a b hab
  intro x hx
  rw [lipschitzNetUnion, Finset.mem_biUnion] at hx ⊢
  obtain ⟨j, hj, hx⟩ := hx
  rw [Finset.mem_range] at hj
  exact ⟨j, Finset.mem_range.mpr (by omega), hx⟩

/-- Density at rate `3/(m+1)` (HDP Exercise 8.9): every class member is
within `L∞`-distance `3/(m+1)` of the `m`-th exhaustion stage. -/
theorem exists_mem_lipschitzNetUnion_dist_le {f : C(unitInterval, ℝ)}
    -- USER-INPUT: class membership; HDP §8.2, Eq. (8.24)
    (hf : f ∈ lipschitzUnitClass) (m : ℕ) :
    ∃ g ∈ lipschitzNetUnion m, dist f g ≤ 3 / (m + 1) := by
  classical
  obtain ⟨g, hg, hd⟩ := exists_mem_lipschitzNet_dist_le (m + 1) hf
  refine ⟨g, ?_, ?_⟩
  · rw [lipschitzNetUnion, Finset.mem_biUnion]
    exact ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), hg⟩
  · push_cast at hd ⊢
    exact hd

/-- The supremand family is bounded above by `2` (LEAN-ONLY `BddAbove` side
condition for `ℝ`-valued `⨆`; from `|X_f| ≤ 2·‖f‖∞ ≤ 2` via
`abs_empiricalProcess_le`). -/
theorem bddAbove_range_abs_empiricalProcess [IsProbabilityMeasure P] (ω : Ω) :
    BddAbove (Set.range
      (fun f : lipschitzUnitClass =>
        |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω|)) := by
  refine ⟨2, ?_⟩
  rintro y ⟨f, rfl⟩
  have hB : ∀ x, |(f : C(unitInterval, ℝ)) x| ≤ 1 :=
    fun x => abs_le.mpr ⟨by linarith [(f.2.2 x).1], (f.2.2 x).2⟩
  have := abs_empiricalProcess_le (P := P) (n := n) (X := X)
    (f := ⇑(f : C(unitInterval, ℝ))) hB ω
  linarith

/-- **R3, dense-net reduction** (measurability/sup policy; HDP §8.2): the
full supremum over the uncountable class (8.24) equals the countable
monotone limit of finite maxima over the exhaustion — deterministically, for
every `ω`. Engine: `|X_f − X_g| ≤ 2 · dist f g` + density `3/(m+1)` +
ε-of-room. Named-sorry fallback of `hdp-emp-dense`. -/
theorem iSup_abs_empiricalProcess_eq_iSup_netUnion [IsProbabilityMeasure P]
    (ω : Ω) :
    (⨆ f : lipschitzUnitClass,
        |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω|)
      = ⨆ m : ℕ, (lipschitzNetUnion m).sup' (lipschitzNetUnion_nonempty m)
          (fun g => |empiricalProcess P n X ⇑g ω|) := by
  haveI : Nonempty (lipschitzUnitClass) := ⟨⟨0, zero_mem_lipschitzUnitClass⟩⟩
  set T : ℕ → ℝ := fun m => (lipschitzNetUnion m).sup' (lipschitzNetUnion_nonempty m)
      (fun g => |empiricalProcess P n X ⇑g ω|) with hT
  -- Each finite maximum is bounded above by `2` (all members are in `𝓕`).
  have hTle : ∀ m, T m ≤ 2 := by
    intro m
    refine Finset.sup'_le _ _ (fun g hg => ?_)
    have hg' : g ∈ lipschitzUnitClass :=
      lipschitzNetUnion_subset m (Finset.mem_coe.mpr hg)
    have hB : ∀ x, |g x| ≤ 1 :=
      fun x => abs_le.mpr ⟨by linarith [(hg'.2 x).1], (hg'.2 x).2⟩
    have := abs_empiricalProcess_le (P := P) (n := n) (X := X) (f := ⇑g) hB ω
    linarith
  -- `S := ⨆ m, T m` is bounded above by `2`.
  have hbddT : BddAbove (Set.range T) := ⟨2, by rintro y ⟨m, rfl⟩; exact hTle m⟩
  set S : ℝ := ⨆ m, T m with hS
  have hSle : ∀ m, T m ≤ S := fun m => le_ciSup hbddT m
  have hbddF := bddAbove_range_abs_empiricalProcess (P := P) (n := n) (X := X) ω
  apply le_antisymm
  · -- LHS ≤ S : for each class member, an ε-of-room argument via density.
    apply ciSup_le
    intro f
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    -- Choose a mesh `m` with `6/(m+1) < ε`.
    obtain ⟨m, hm⟩ := exists_nat_gt (6 / ε)
    have hmpos : (0 : ℝ) < (m : ℝ) + 1 :=
      by have := Nat.cast_nonneg (α := ℝ) m; linarith
    have hm1 : (6 : ℝ) / ((m : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ hmpos]
      have h : (6 : ℝ) / ε < m := hm
      rw [div_lt_iff₀ hε] at h
      nlinarith [h, hε.le, Nat.cast_nonneg (α := ℝ) m]
    -- Density: a net member `g` within `3/(m+1)` of `f`.
    obtain ⟨g, hgmem, hgd⟩ := exists_mem_lipschitzNetUnion_dist_le f.2 m
    -- Oscillation bound `|X_f − X_g| ≤ 2·dist`.
    have hintf : Integrable ⇑(f : C(unitInterval, ℝ)) P := cont_integrable (P := P) _
    have hintg : Integrable ⇑g P := cont_integrable (P := P) _
    have hosc : |empiricalProcess P n X ⇑(f : C(unitInterval, ℝ)) ω
        - empiricalProcess P n X ⇑g ω| ≤ 2 * dist (f : C(unitInterval, ℝ)) g := by
      refine abs_empiricalProcess_sub_le hintf hintg (fun x => ?_) ω
      have := ContinuousMap.dist_apply_le_dist (f := (f : C(unitInterval, ℝ))) (g := g) x
      rwa [Real.dist_eq] at this
    have hgT : |empiricalProcess P n X ⇑g ω| ≤ T m :=
      Finset.le_sup' (fun h : C(unitInterval, ℝ) => |empiricalProcess P n X ⇑h ω|) hgmem
    calc |empiricalProcess P n X ⇑(f : C(unitInterval, ℝ)) ω|
        ≤ |empiricalProcess P n X ⇑g ω| + 2 * dist (f : C(unitInterval, ℝ)) g := by
          have := abs_sub_abs_le_abs_sub
            (empiricalProcess P n X ⇑(f : C(unitInterval, ℝ)) ω)
            (empiricalProcess P n X ⇑g ω)
          linarith [hosc]
      _ ≤ T m + 2 * (3 / ((m : ℝ) + 1)) := by
          have hd2 : 2 * dist (f : C(unitInterval, ℝ)) g ≤ 2 * (3 / ((m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left hgd (by norm_num)
          linarith [hgT]
      _ ≤ S + ε := by
          have h6 : 2 * (3 / ((m : ℝ) + 1)) = 6 / (m + 1) := by ring
          rw [h6]; linarith [hSle m, hm1.le]
  · -- S ≤ LHS : each net member is a class member.
    apply ciSup_le
    intro m
    refine Finset.sup'_le _ _ (fun g hg => ?_)
    have hg' : g ∈ lipschitzUnitClass :=
      lipschitzNetUnion_subset m (Finset.mem_coe.mpr hg)
    exact le_ciSup hbddF ⟨g, hg'⟩

/-- **R2, translation reduction** (HDP §8.2 p. 230, "(Why?)"): the supremum
over the 1-Lipschitz class equals the supremum over the `[0,1]`-valued class
(8.24), via `h := g − min g` (min attained on the compact domain) and
translation invariance `X_{g+c} = X_g`. -/
theorem iSup_abs_empiricalProcess_lipOne_eq [IsProbabilityMeasure P]
    [NeZero n] (ω : Ω) :
    (⨆ f : {f : unitInterval → ℝ // LipschitzWith 1 f},
        |empiricalProcess P n X (↑f) ω|)
      = ⨆ f : lipschitzUnitClass,
          |empiricalProcess P n X (⇑(f : C(unitInterval, ℝ))) ω| := by
  haveI : Nonempty {f : unitInterval → ℝ // LipschitzWith 1 f} :=
    ⟨⟨fun _ => 0, (LipschitzWith.const (0 : ℝ)).weaken (by norm_num)⟩⟩
  haveI : Nonempty (lipschitzUnitClass) :=
    ⟨⟨0, zero_mem_lipschitzUnitClass⟩⟩
  -- For a 1-Lipschitz `f`, subtracting its (attained) min gives a class member
  -- with the same empirical process value.
  have hshift : ∀ f : {f : unitInterval → ℝ // LipschitzWith 1 f},
      ∃ g : lipschitzUnitClass,
        |empiricalProcess P n X (↑f) ω|
          = |empiricalProcess P n X (⇑(g : C(unitInterval, ℝ))) ω| := by
    intro f
    obtain ⟨x₀, -, hx₀min⟩ := (isCompact_univ (X := unitInterval)).exists_isMinOn
      Set.univ_nonempty f.2.continuous.continuousOn
    have hx₀ : ∀ y, (↑f : unitInterval → ℝ) x₀ ≤ (↑f : unitInterval → ℝ) y :=
      fun y => hx₀min (Set.mem_univ y)
    set c₀ : ℝ := (↑f : unitInterval → ℝ) x₀ with hc₀
    have hcont : Continuous (fun x => (↑f : unitInterval → ℝ) x - c₀) :=
      f.2.continuous.sub continuous_const
    -- The shifted map as a bundled `ContinuousMap`.
    set h : C(unitInterval, ℝ) :=
      ⟨fun x => (↑f : unitInterval → ℝ) x - c₀, hcont⟩ with hh
    have hlip : LipschitzWith 1 ⇑h := by
      simpa [hh] using f.2.sub (LipschitzWith.const (α := unitInterval) c₀)
    have hIcc : ∀ x, h x ∈ Set.Icc (0 : ℝ) 1 := by
      intro x
      refine ⟨by simp only [hh, ContinuousMap.coe_mk]; linarith [hx₀ x], ?_⟩
      simp only [hh, ContinuousMap.coe_mk]
      have hdist : |(↑f : unitInterval → ℝ) x - c₀| ≤ 1 := by
        have hle := f.2.dist_le_mul x x₀
        rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq] at hle
        simp only [NNReal.coe_one, one_mul] at hle
        have hx01 := x.2
        have hx001 := x₀.2
        rw [Set.mem_Icc] at hx01 hx001
        calc |(↑f : unitInterval → ℝ) x - c₀| ≤ |(x : ℝ) - x₀| := hle
          _ ≤ 1 := by
              rw [abs_le]
              constructor <;> [linarith [hx01.1, hx001.2]; linarith [hx01.2, hx001.1]]
      rw [abs_le] at hdist; linarith [hdist.2]
    have hmem : h ∈ lipschitzUnitClass := ⟨hlip, hIcc⟩
    refine ⟨⟨h, hmem⟩, ?_⟩
    have hint : Integrable (↑f : unitInterval → ℝ) P := lip_integrable (P := P) f.2
    have heq : empiricalProcess P n X (fun x => (↑f : unitInterval → ℝ) x + (-c₀))
        = empiricalProcess P n X (↑f) := empiricalProcess_add_const hint (-c₀)
    have hval : (⇑(h : C(unitInterval, ℝ)) : unitInterval → ℝ)
        = fun x => (↑f : unitInterval → ℝ) x + (-c₀) := by
      funext x; simp only [hh, ContinuousMap.coe_mk]; ring
    rw [hval, heq]
  -- RHS is bounded above.
  have hbddR := bddAbove_range_abs_empiricalProcess (P := P) (n := n) (X := X) ω
  -- LHS is bounded above (via the shift, every value is a class value, hence ≤ 2).
  have hbddL : BddAbove (Set.range (fun f : {f : unitInterval → ℝ // LipschitzWith 1 f} =>
      |empiricalProcess P n X (↑f) ω|)) := by
    refine ⟨2, ?_⟩
    rintro y ⟨f, rfl⟩
    obtain ⟨g, hg⟩ := hshift f
    change |empiricalProcess P n X (↑f) ω| ≤ 2
    rw [hg]
    have hB : ∀ x, |(⇑(g : C(unitInterval, ℝ))) x| ≤ 1 :=
      fun x => abs_le.mpr ⟨by linarith [(g.2.2 x).1], (g.2.2 x).2⟩
    have := abs_empiricalProcess_le (P := P) (n := n) (X := X)
      (f := ⇑(g : C(unitInterval, ℝ))) hB ω
    linarith
  apply le_antisymm
  · -- each 1-Lipschitz value ≤ RHS via its class shift
    apply ciSup_le
    intro f
    obtain ⟨g, hg⟩ := hshift f
    rw [hg]
    exact le_ciSup hbddR g
  · -- each class member is 1-Lipschitz, so ≤ LHS
    apply ciSup_le
    intro g
    exact le_ciSup hbddL ⟨⇑(g : C(unitInterval, ℝ)), g.2.1⟩

/-- **R1, scaling reduction** (HDP §8.2 p. 230, "(Why?)"): for `L ≠ 0`, the
supremum over the `L`-Lipschitz class is `L` times the supremum over the
1-Lipschitz class, via the bijection `f ↦ L • f` and
`Monotone.map_ciSup_of_continuousAt`. -/
theorem iSup_abs_empiricalProcess_lip_smul {L : ℝ≥0}
    -- LEAN-ONLY: nondegenerate scaling (L = 0 is `iSup_abs_empiricalProcess_lipZero_eq`); no scope change
    (hL : L ≠ 0) [IsProbabilityMeasure P] (ω : Ω) :
    (⨆ f : {f : unitInterval → ℝ // LipschitzWith L f},
        |empiricalProcess P n X (↑f) ω|)
      = (L : ℝ) * ⨆ f : {f : unitInterval → ℝ // LipschitzWith 1 f},
          |empiricalProcess P n X (↑f) ω| := by
  have hLpos : (0 : ℝ) < L := by
    have : (0 : ℝ≥0) < L := pos_iff_ne_zero.mpr hL
    exact_mod_cast this
  -- The scaling map `g ↦ s • g` sends `c`-Lipschitz to `‖s‖₊*c`-Lipschitz.
  have hscale : ∀ (s : ℝ) {c : ℝ≥0} {g : unitInterval → ℝ}, LipschitzWith c g →
      LipschitzWith (‖s‖₊ * c) (fun x => s * g x) := by
    intro s c g hg
    have h := (lipschitzWith_smul (β := ℝ) s).comp hg
    simpa [Function.comp, smul_eq_mul] using! h
  have hLnn : ‖(L : ℝ)‖₊ = L := by
    rw [Real.nnnorm_of_nonneg hLpos.le]; rfl
  -- Bijection between the 1-Lipschitz and L-Lipschitz subtypes via `g ↦ L•g`.
  let e : {f : unitInterval → ℝ // LipschitzWith 1 f} ≃
      {f : unitInterval → ℝ // LipschitzWith L f} :=
    { toFun := fun g => ⟨fun x => (L : ℝ) * g.1 x, by
        have h := hscale (L : ℝ) g.2; rw [hLnn] at h; simpa using h⟩
      invFun := fun f => ⟨fun x => (L : ℝ)⁻¹ * f.1 x, by
        have h := hscale (L : ℝ)⁻¹ f.2
        have hn : ‖(L : ℝ)⁻¹‖₊ * L = 1 := by
          rw [Real.nnnorm_of_nonneg (inv_nonneg.mpr hLpos.le)]
          ext; push_cast; rw [inv_mul_cancel₀ hLpos.ne']
        rw [hn] at h; exact h⟩
      left_inv := fun g => by
        ext x; simp [← mul_assoc, inv_mul_cancel₀ hLpos.ne']
      right_inv := fun f => by
        ext x; simp [← mul_assoc, mul_inv_cancel₀ hLpos.ne'] }
  -- Reindex the L-Lipschitz sup along `e`.
  have hreindex : (⨆ f : {f : unitInterval → ℝ // LipschitzWith L f},
        |empiricalProcess P n X (↑f) ω|)
      = ⨆ g : {f : unitInterval → ℝ // LipschitzWith 1 f},
          |empiricalProcess P n X (↑(e g)) ω| :=
    (e.iSup_comp (g := fun f : {f : unitInterval → ℝ // LipschitzWith L f} =>
      |empiricalProcess P n X (↑f) ω|)).symm
  rw [hreindex]
  -- Pointwise: `|X_{e g}| = L * |X_g|`.
  have hpt : ∀ g : {f : unitInterval → ℝ // LipschitzWith 1 f},
      |empiricalProcess P n X (↑(e g)) ω| = (L : ℝ) * |empiricalProcess P n X (↑g) ω| := by
    intro g
    have hint : Integrable (↑g : unitInterval → ℝ) P := lip_integrable (P := P) g.2
    have : empiricalProcess P n X (↑(e g)) ω
        = (L : ℝ) * empiricalProcess P n X (↑g) ω := by
      change empiricalProcess P n X (fun x => (L : ℝ) * (↑g : unitInterval → ℝ) x) ω = _
      exact empiricalProcess_const_mul (L : ℝ) hint ω
    rw [this, abs_mul, abs_of_nonneg hLpos.le]
  rw [iSup_congr hpt, Real.mul_iSup_of_nonneg hLpos.le]

/-- Degenerate scaling `L = 0` (LEAN-ONLY edge case): 0-Lipschitz functions
are constants, and constants are invisible to the empirical process, so the
supremum vanishes. -/
theorem iSup_abs_empiricalProcess_lipZero_eq [IsProbabilityMeasure P]
    [NeZero n] (ω : Ω) :
    (⨆ f : {f : unitInterval → ℝ // LipschitzWith 0 f},
        |empiricalProcess P n X (↑f) ω|) = 0 := by
  have key : ∀ f : {f : unitInterval → ℝ // LipschitzWith 0 f},
      |empiricalProcess P n X (↑f) ω| = 0 := by
    intro f
    have hconst : (↑f : unitInterval → ℝ)
        = fun _ => (↑f : unitInterval → ℝ) ⟨0, by norm_num, by norm_num⟩ := by
      funext x
      have hd := f.2.dist_le_mul x ⟨0, by norm_num, by norm_num⟩
      simp only [NNReal.coe_zero, zero_mul] at hd
      have hz : dist ((↑f : unitInterval → ℝ) x)
          ((↑f : unitInterval → ℝ) ⟨0, by norm_num, by norm_num⟩) = 0 :=
        le_antisymm hd dist_nonneg
      rw [Real.dist_eq, abs_eq_zero, sub_eq_zero] at hz
      exact hz
    rw [hconst, empiricalProcess_const, abs_zero]
  haveI : Nonempty {f : unitInterval → ℝ // LipschitzWith 0 f} :=
    ⟨⟨fun _ => 0, (LipschitzWith.const (0 : ℝ))⟩⟩
  rw [iSup_congr key]
  exact ciSup_const

end StatLean.ConcentrationInequalities
