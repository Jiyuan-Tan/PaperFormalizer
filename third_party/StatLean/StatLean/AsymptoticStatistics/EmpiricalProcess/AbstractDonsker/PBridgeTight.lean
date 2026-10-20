module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.BrownianBridge
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.GPProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import Mathlib

@[expose] public section

/-!
# Compact modulus-balls in `ℓ∞(F)` (the topology half of `G_P`-tightness)

The tight `P`-Brownian-bridge law `G_P` concentrates on sets of paths that are
simultaneously sup-bounded and equicontinuous in the `distL2 P` semimetric. This
file proves the **pure-topology** half: such a "modulus ball"

`modulusBall P F M δ a = {z | (∀ f, |z f| ≤ M) ∧ ∀ k f g, distL2 f g ≤ δ k → |z f − z g| ≤ a k}`

is **compact** in `ℓ∞(F)`, by a hand-rolled Arzelà–Ascoli argument: it is closed,
and (when `a k → 0` and `↥F` is totally bounded in `distL2 P`) totally bounded.
Completeness of `ℓ∞(F)` (`lp.completeSpace`) then upgrades closed + totally bounded
to compact.

The compactness argument above is purely topological. The later
measure-theoretic argument shows that the bridge law `ν` concentrates on some
`modulusBall`.

## Main definitions

* `modulusBall P F M δ a` — the equibounded + equicontinuous-modulus subset of
  `ℓ∞(F)`.

## Main results

* `isClosed_modulusBall` — `modulusBall` is closed.
* `totallyBounded_modulusBall` — under `a k → 0` and finite bracketing entropy
  (⇒ `↥F` totally bounded in `distL2 P`), `modulusBall` is totally bounded.
* `isCompact_modulusBall` — `modulusBall` is compact.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Modulus ball in `ℓ∞(F)`.** The set of paths `z` that are uniformly bounded
by `M` and whose `distL2 P`-modulus of continuity is controlled by the schedule
`(δ k, a k)`: whenever `distL2 P f g ≤ δ k` the increment `|z f − z g|` is at most
`a k`. The tight bridge law `G_P` concentrates on such a set (with `a k → 0`). -/
def modulusBall (P : Measure Ω) (F : Set (Ω → ℝ)) (M : ℝ) (δ a : ℕ → ℝ) :
    Set (LinfF F) :=
  {z | (∀ f, |z f| ≤ M) ∧
    ∀ (k : ℕ) (f g : ↥F), distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k → |z f - z g| ≤ a k}

omit [MeasurableSpace Ω] in
/-- Coordinate evaluation `z ↦ z i` on `ℓ∞(F)` is continuous (1-Lipschitz). -/
theorem continuous_coordEval (F : Set (Ω → ℝ)) (i : ↥F) :
    Continuous (fun z : LinfF F => z i) := by
  have hlip : LipschitzWith 1 (fun z : LinfF F => z i) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have hsub : (z : ↥F → ℝ) i - (w : ↥F → ℝ) i = (z - w) i := by
      rw [lp.coeFn_sub z w]; rfl
    rw [show ‖(z : ↥F → ℝ) i - (w : ↥F → ℝ) i‖ = ‖(z - w) i‖ from by rw [hsub]]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) i
  exact hlip.continuous

/-- **`modulusBall` is closed.** Each defining constraint cuts out a closed set
(coordinate evaluations are continuous, `|·|` is continuous, `isClosed_le`); the
whole ball is an intersection of these. -/
theorem isClosed_modulusBall (P : Measure Ω) (F : Set (Ω → ℝ)) (M : ℝ) (δ a : ℕ → ℝ) :
    IsClosed (modulusBall P F M δ a) := by
  have hcont := continuous_coordEval F
  -- The bound part: `⋂_f {z | |z f| ≤ M}`.
  have hbound : IsClosed {z : LinfF F | ∀ f, |z f| ≤ M} := by
    have : {z : LinfF F | ∀ f, |z f| ≤ M} = ⋂ f : ↥F, {z : LinfF F | |z f| ≤ M} := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter (fun f => isClosed_le (hcont f).abs continuous_const)
  -- The modulus part: `⋂_k ⋂_f ⋂_g {z | distL2 f g ≤ δ k → |z f − z g| ≤ a k}`.
  have hmod : IsClosed {z : LinfF F | ∀ (k : ℕ) (f g : ↥F),
      distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k → |z f - z g| ≤ a k} := by
    have : {z : LinfF F | ∀ (k : ℕ) (f g : ↥F),
        distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k → |z f - z g| ≤ a k}
        = ⋂ k : ℕ, ⋂ f : ↥F, ⋂ g : ↥F,
          {z : LinfF F | distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k → |z f - z g| ≤ a k} := by
      ext z; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    refine isClosed_iInter (fun k => isClosed_iInter (fun f => isClosed_iInter (fun g => ?_)))
    by_cases hfg : distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k
    · have hset : {z : LinfF F |
          distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k → |z f - z g| ≤ a k}
          = {z : LinfF F | |z f - z g| ≤ a k} := by
        ext z; simp only [Set.mem_setOf_eq]; exact ⟨fun h => h hfg, fun h _ => h⟩
      rw [hset]
      exact isClosed_le (((hcont f).sub (hcont g)).abs) continuous_const
    · have hset : {z : LinfF F |
          distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k → |z f - z g| ≤ a k}
          = Set.univ := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact fun h => absurd h hfg
      rw [hset]; exact isClosed_univ
  have : modulusBall P F M δ a
      = {z : LinfF F | ∀ f, |z f| ≤ M} ∩ {z : LinfF F | ∀ (k : ℕ) (f g : ↥F),
        distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ≤ δ k → |z f - z g| ≤ a k} := by
    ext z; simp only [modulusBall, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [this]
  exact hbound.inter hmod

/-- **`modulusBall` is totally bounded** (the hand-rolled Ascoli core). Equibounded
plus equicontinuous on the totally-bounded index `↥F` forces sup-norm total
boundedness: given `ε`, pick `k` with `a k < ε/3`, take a finite `δ k`-net of `↥F`
(from `totallyBounded_L2`), and discretize the finitely-many coordinate values on a
`ε/3`-grid; the equicontinuity transfers a coordinate match into a uniform match. -/
theorem totallyBounded_modulusBall {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (M : ℝ) (δ a : ℕ → ℝ) (hδ : ∀ k, 0 < δ k)
    (ha : Filter.Tendsto a Filter.atTop (𝓝 0)) :
    TotallyBounded (modulusBall P F M δ a) := by
  classical
  -- Empty index: `ℓ∞(∅)` is a subsingleton, hence trivially totally bounded.
  by_cases hne : Nonempty ↥F
  swap
  · -- Empty index: `ℓ∞(∅)` is a subsingleton; a singleton net `{0}` covers everything.
    haveI hempty : IsEmpty ↥F := not_nonempty_iff.1 hne
    haveI hsub : Subsingleton (LinfF F) :=
      ⟨fun f g => lp.ext (Subsingleton.elim _ _)⟩
    refine Metric.totallyBounded_iff.2 (fun ε hε => ?_)
    refine ⟨{(0 : LinfF F)}, Set.finite_singleton _, fun z _ => ?_⟩
    refine Set.mem_iUnion₂.2 ⟨(0 : LinfF F), rfl, ?_⟩
    rw [Metric.mem_ball, Subsingleton.elim z (0 : LinfF F), dist_self]; exact hε
  haveI : Nonempty ↥F := hne
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- Choose `k` with `a k < ε/5`.
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 ha (ε / 5) (by linarith)
  set k := N with hkdef
  have hk : dist (a k) 0 < ε / 5 := hN k (le_refl N)
  have hak : a k < ε / 5 := by
    rw [Real.dist_eq, sub_zero] at hk
    exact (abs_lt.1 hk).2
  -- A finite `δ k`-net `S` of `F` in `distL2 P`.
  obtain ⟨S, hS_sub, hS_net⟩ := totallyBounded_L2 hF_ent (δ k) (hδ k)
  -- Lift each net point to the subtype `↥F`.
  -- Index type for `S`.
  let ι := {x : Ω → ℝ // x ∈ S}
  haveI : Fintype ι := FinsetCoe.fintype S
  -- The coordinate-evaluation tuple of a path `z` over the net `S`.
  let Φ : LinfF F → (ι → ℝ) := fun z i => z ⟨(i : Ω → ℝ), hS_sub i.2⟩
  -- The compact box `[-M, M]^ι` in `ι → ℝ`.
  have hbox_compact : IsCompact (Set.univ.pi (fun _ : ι => Set.Icc (-M) M)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hbox_tb : TotallyBounded (Set.univ.pi (fun _ : ι => Set.Icc (-M) M)) :=
    hbox_compact.totallyBounded
  -- For `z ∈ modulusBall`, `Φ z` lands in the box.
  have hΦ_mem : ∀ z ∈ modulusBall P F M δ a,
      Φ z ∈ Set.univ.pi (fun _ : ι => Set.Icc (-M) M) := by
    intro z hz i _
    have := hz.1 ⟨(i : Ω → ℝ), hS_sub i.2⟩
    exact abs_le.1 this
  -- Take a finite `ε/5`-net `T` of the box in the sup metric on `ι → ℝ`.
  obtain ⟨T, hT_fin, hT_cover⟩ :=
    (Metric.totallyBounded_iff.1 hbox_tb) (ε / 5) (by linarith)
  -- For each tuple `t ∈ T`, choose (if any) a path in `modulusBall` whose `Φ`
  -- lies within `ε/5` of `t`. These representatives form the net.
  let good : (ι → ℝ) → Prop := fun t => ∃ z ∈ modulusBall P F M δ a, Φ z ∈ Metric.ball t (ε / 5)
  let rep : (ι → ℝ) → LinfF F := fun t =>
    if h : good t then h.choose else (0 : LinfF F)
  refine ⟨rep '' (T ∩ {t | good t}), ?_, ?_⟩
  · -- finite
    exact (hT_fin.subset (Set.inter_subset_left)).image _
  · -- cover
    intro z hz
    -- `Φ z` is in the box, so some `t ∈ T` is within `ε/3`.
    have hΦz : Φ z ∈ Set.univ.pi (fun _ : ι => Set.Icc (-M) M) := hΦ_mem z hz
    obtain ⟨t, htT, htz⟩ := Set.mem_iUnion₂.1 (hT_cover hΦz)
    have hgt : good t := ⟨z, hz, htz⟩
    -- The chosen representative `rep t`.
    have hreptz : Φ (rep t) ∈ Metric.ball t (ε / 5) := by
      simp only [rep, dif_pos hgt]; exact hgt.choose_spec.2
    have hrep_mb : rep t ∈ modulusBall P F M δ a := by
      simp only [rep, dif_pos hgt]; exact hgt.choose_spec.1
    -- `rep t` is in the net image.
    refine Set.mem_iUnion₂.2 ⟨rep t, ⟨t, ⟨htT, hgt⟩, rfl⟩, ?_⟩
    -- `dist z (rep t) < ε`: coordinate match (`≤ ε/3` on net) + equicontinuity.
    rw [Metric.mem_ball]
    -- coordinate match: `|Φ z i − Φ (rep t) i| ≤ 2(ε/5)`.
    have hcoord : ∀ i : ι, |Φ z i - Φ (rep t) i| ≤ 2 * (ε / 5) := by
      intro i
      have h1 : |Φ z i - t i| < ε / 5 := by
        have hb := htz; rw [Metric.mem_ball] at hb
        have := lt_of_le_of_lt (dist_le_pi_dist (Φ z) t i) hb
        rwa [Real.dist_eq] at this
      have h2 : |Φ (rep t) i - t i| < ε / 5 := by
        have hb := hreptz; rw [Metric.mem_ball] at hb
        have := lt_of_le_of_lt (dist_le_pi_dist (Φ (rep t)) t i) hb
        rwa [Real.dist_eq] at this
      have htr : |Φ z i - Φ (rep t) i| ≤ |Φ z i - t i| + |Φ (rep t) i - t i| := by
        have e : Φ z i - Φ (rep t) i = (Φ z i - t i) - (Φ (rep t) i - t i) := by ring
        rw [e]; exact abs_sub _ _
      linarith
    -- Equicontinuity gives the per-coordinate sup-norm bound
    -- `2 a k + 2(ε/5) < 4ε/5`.
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (lp.norm_le_of_forall_le' (4 * ε / 5) ?_) (by linarith)
    intro f
    -- pick a net point `g ∈ S` with `distL2 f g < δ k`.
    obtain ⟨g, hgS, hfg⟩ := hS_net (f : Ω → ℝ) f.2
    -- `g` as a subtype element and as an index `i ∈ ι`.
    let gsub : ↥F := ⟨g, hS_sub hgS⟩
    let gι : ι := ⟨g, hgS⟩
    -- increment bounds from modulusBall.
    have hzf : |z f - z gsub| ≤ a k :=
      hz.2 k f gsub (le_of_lt hfg)
    have hrtf : |rep t f - rep t gsub| ≤ a k :=
      hrep_mb.2 k f gsub (le_of_lt hfg)
    -- coordinate match at index `gι`.
    have hmid : |z gsub - rep t gsub| ≤ 2 * (ε / 5) := by
      have := hcoord gι
      simpa only [Φ, gsub, gι] using this
    -- triangle: `|z f − rep t f| ≤ |z f − z g| + |z g − rep t g| + |rep t g − rep t f|`.
    have hsub_z : (z - rep t) f = z f - rep t f := by rw [lp.coeFn_sub z (rep t)]; rfl
    rw [Real.norm_eq_abs, hsub_z]
    have htri : |z f - rep t f|
        ≤ |z f - z gsub| + |z gsub - rep t gsub| + |rep t gsub - rep t f| := by
      have e : z f - rep t f
          = (z f - z gsub) + (z gsub - rep t gsub) + (rep t gsub - rep t f) := by ring
      rw [e]
      exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _)) (le_refl _))
    have hrtf' : |rep t gsub - rep t f| ≤ a k := by
      rw [abs_sub_comm]; exact hrtf
    have hfinal : |z f - rep t f| ≤ a k + 2 * (ε / 5) + a k := by
      calc |z f - rep t f|
          ≤ |z f - z gsub| + |z gsub - rep t gsub| + |rep t gsub - rep t f| := htri
        _ ≤ a k + 2 * (ε / 5) + a k := by
            exact add_le_add (add_le_add hzf hmid) hrtf'
    -- `a k + 2(ε/5) + a k < ε/5 + 2ε/5 + ε/5 = 4ε/5`.
    have : |z f - rep t f| ≤ 4 * ε / 5 := by nlinarith [hak]
    simpa using this

/-- **`modulusBall` is compact.** Closed + totally bounded + completeness of
`ℓ∞(F)` (`lp.completeSpace`). This is the topology half of the `G_P`-tightness
field. -/
theorem isCompact_modulusBall {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤)
    (M : ℝ) (δ a : ℕ → ℝ) (hδ : ∀ k, 0 < δ k)
    (ha : Filter.Tendsto a Filter.atTop (𝓝 0)) :
    IsCompact (modulusBall P F M δ a) :=
  (totallyBounded_modulusBall hF_ent M δ a hδ ha).isCompact_of_isClosed
    (isClosed_modulusBall P F M δ a)

/-! ## The measure half: `gpBridgeMeasure` is tight

The bridge law `ν = gpBridgeMeasure = iidStdGaussian.map gpPath` concentrates on
a compact modulus ball.  Given `ε > 0`:

* a **mass tail** at scale `J` (`summable_bigOsc` ⟹ the close-pair oscillation
  events `bigOsc gpX net j (a j)` have summable mass, so their tail `≤ ε/2`),
* a **bound `M`** (continuity of measure: a.e. `gpPath` is sup-bounded, so the
  decreasing events `{ω | M < ‖gpPath ω‖}` shrink to a null set),

then `K = modulusBall P F M (2^{-·}) η` (with `η J = a J + 2·∑' k, a (J+k) → 0`)
is compact (`isCompact_modulusBall`), and `gpPath ⁻¹ Kᶜ` is covered by
`{¬gpGood} ∪ {M < ‖gpPath‖} ∪ ⋃_{j ≥ J} bigOsc gpX net j (a j)`, the union of a
null set and the two tail picks, hence `ν Kᶜ ≤ ε`. -/

section Tight

open Filter IsonormalProcess GaussianChaining

variable {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
variable {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
variable (hF_meas : ∀ f ∈ F, Measurable f)
  (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)

/-- **Transport of the chaining modulus from net-pairs to all of `↥F`.** Fix a
"good" sample point `ω` (so
`gpPath ω = pathExtend ω`, the uniformly-continuous extension of the skeleton
path) that *avoids* every level oscillation event `bigOsc gpX net m (a m)` at
scales `m ≥ J`.  Then `gpPath ω` lies in the modulus ball
`modulusBall P F M (2^{-·}) η`, where `η k = a k + 2·∑' i, a (k + i)` is the
deterministic chaining schedule and `M` bounds the sup-norm of `gpPath ω`.

The bound part is `bddAbove_pathExtend_of_good` (good ⟹ sup-bounded).  The
modulus part is the genuine transport: `osc_le_of_avoid_bigOsc` controls the
`gpX`-increment of any two *skeleton* points within a dyadic scale by `η`, and
uniform continuity of `pathExtend` (= `gpPath ω` on the good set) lifts this to
**all** pairs `f g : ↥F` with `distL2 P f g ≤ 2^{-k}` by a density / continuity
limiting argument (skeleton sequences `fₙ → f`, `gₙ → g`, with the increment
bound stable under the `distL2`-uniform limit).

The alignment hypothesis `hskel` identifies the skeleton with the union of the
oscillation nets, `gpSkeleton = ⋃ j, net j`, so both estimates apply to the
same pairs. -/
theorem gpPath_mem_modulusBall_of_avoid
    (net : ℕ → Finset ↥F)
    (hnet : letI := distL2PseudoMetric hG_env hG hF_meas
      ∀ (j : ℕ) (t : ↥F), ∃ s ∈ net j, dist t s < (2 : ℝ) ^ (-(j : ℤ)))
    (hnet_mono : Monotone net)
    (hskel : gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      = ⋃ j : ℕ, (↑(net j) : Set ↥F))
    {a : ℕ → ℝ} (ha_pos : ∀ j, 0 < a j) (ha_summable : Summable a)
    (M : ℝ)
    {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω)
    (hM : ∀ f, |gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f| ≤ M)
    {J : ℕ}
    (havoid : letI := distL2PseudoMetric hG_env hG hF_meas
      ∀ m ≥ J, ω ∉ GaussianChaining.bigOsc
        (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep) net m (a m)) :
    gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω
      ∈ modulusBall P F M (fun k => (2 : ℝ) ^ (-((J + k : ℕ) : ℤ)))
          (fun k => a (J + k) + 2 * ∑' i : ℕ, a (J + k + i)) := by
  classical
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  set X := gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep with hXdef
  set pe := pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω with hpedef
  -- First-countability + Fréchet-Urysohn of the `distL2` pseudometric on `↥F`.
  haveI hfc : @FirstCountableTopology ↥F inst.toUniformSpace.toTopologicalSpace :=
    @UniformSpace.firstCountableTopology ↥F inst.toUniformSpace inferInstance
  haveI hfu : @FrechetUrysohnSpace ↥F inst.toUniformSpace.toTopologicalSpace :=
    @FirstCountableTopology.frechetUrysohnSpace ↥F inst.toUniformSpace.toTopologicalSpace hfc
  -- `pe` is (uniformly) continuous on `↥F` (good set).
  have huc := uniformContinuous_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω
  have hcont : @Continuous ↥F ℝ inst.toUniformSpace.toTopologicalSpace _ pe :=
    @UniformContinuous.continuous ↥F ℝ inst.toUniformSpace _ _ huc
  -- `pe` agrees with `X · ω` on the skeleton `⋃ net`.
  have hagree : ∀ u : ↥F, u ∈ (⋃ j : ℕ, (↑(net j) : Set ↥F)) → pe u = X u ω := by
    intro u hu
    have hu' : u ∈ gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne := by
      rw [hskel]; exact hu
    exact pathExtend_eq_on_skeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω ⟨u, hu'⟩
  -- The skeleton-pair bound at scale `J+k` from `osc_le_of_avoid_bigOsc'`.
  have hskelbound : ∀ (k : ℕ) (s t : ↥F),
      s ∈ (⋃ j : ℕ, (↑(net j) : Set ↥F)) → t ∈ (⋃ j : ℕ, (↑(net j) : Set ↥F)) →
      dist s t < 2 * (2 : ℝ) ^ (-((J + k : ℕ) : ℤ)) →
      |pe s - pe t| ≤ a (J + k) + 2 * ∑' i : ℕ, a (J + k + i) := by
    intro k s t hs ht hst
    rw [hagree s hs, hagree t ht]
    exact GaussianChaining.osc_le_of_avoid_bigOsc' (X := X) net hnet hnet_mono ha_pos ha_summable
      ω havoid (Nat.le_add_right J k) hs ht hst
  -- The preceding estimates give membership in the modulus ball.
  refine ⟨hM, ?_⟩
  intro k f g hfg
  -- Rewrite `gpPath ω · = pe ·` on the good set.
  rw [gpPath_apply_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω f,
    gpPath_apply_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω g]
  -- `hfg : distL2 P f g ≤ 2^{-(J+k)}`, i.e. `dist f g ≤ 2^{-(J+k)}` (defeq).
  have hfg' : dist f g ≤ (2 : ℝ) ^ (-((J + k : ℕ) : ℤ)) := hfg
  -- Skeleton sequences `fₙ → f`, `gₙ → g` (density + Fréchet-Urysohn).
  have hdense : @Dense ↥F inst.toUniformSpace.toTopologicalSpace
      (⋃ j : ℕ, (↑(net j) : Set ↥F)) := by
    rw [← hskel]
    exact (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1
  obtain ⟨fseq, hfseq_mem, hfseq_tend⟩ :=
    (@mem_closure_iff_seq_limit ↥F inst.toUniformSpace.toTopologicalSpace hfu _ _).mp
      (by rw [@Dense.closure_eq ↥F inst.toUniformSpace.toTopologicalSpace _ hdense]; trivial)
  obtain ⟨gseq, hgseq_mem, hgseq_tend⟩ :=
    (@mem_closure_iff_seq_limit ↥F inst.toUniformSpace.toTopologicalSpace hfu _ _).mp
      (by rw [@Dense.closure_eq ↥F inst.toUniformSpace.toTopologicalSpace _ hdense]; trivial
        : g ∈ @closure ↥F inst.toUniformSpace.toTopologicalSpace _)
  -- `pe fₙ → pe f`, `pe gₙ → pe g`.
  have hpf : Filter.Tendsto (fun n => pe (fseq n)) Filter.atTop (nhds (pe f)) :=
    (@Continuous.tendsto ↥F ℝ inst.toUniformSpace.toTopologicalSpace _ _ hcont f).comp hfseq_tend
  have hpg : Filter.Tendsto (fun n => pe (gseq n)) Filter.atTop (nhds (pe g)) :=
    (@Continuous.tendsto ↥F ℝ inst.toUniformSpace.toTopologicalSpace _ _ hcont g).comp hgseq_tend
  -- `|pe fₙ − pe gₙ| → |pe f − pe g|`.
  have habs_tend : Filter.Tendsto (fun n => |pe (fseq n) - pe (gseq n)|)
      Filter.atTop (nhds |pe f - pe g|) :=
    (hpf.sub hpg).abs
  -- `dist fₙ gₙ → dist f g`.
  have hdist_tend : Filter.Tendsto (fun n => dist (fseq n) (gseq n))
      Filter.atTop (nhds (dist f g)) :=
    Filter.Tendsto.dist hfseq_tend hgseq_tend
  -- Eventually `dist fₙ gₙ < 2·2^{-(J+k)}` (since `dist f g ≤ 2^{-(J+k)} < 2·2^{-(J+k)}`).
  have hbig : dist f g < 2 * (2 : ℝ) ^ (-((J + k : ℕ) : ℤ)) := by
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-((J + k : ℕ) : ℤ)) := by positivity
    linarith
  have hev : ∀ᶠ n in Filter.atTop, dist (fseq n) (gseq n) < 2 * (2 : ℝ) ^ (-((J + k : ℕ) : ℤ)) :=
    hdist_tend.eventually (gt_mem_nhds hbig)
  -- On those `n`, the skeleton-pair bound holds; pass to the limit.
  have hbound_ev : ∀ᶠ n in Filter.atTop,
      |pe (fseq n) - pe (gseq n)| ≤ a (J + k) + 2 * ∑' i : ℕ, a (J + k + i) := by
    filter_upwards [hev] with n hn
    exact hskelbound k (fseq n) (gseq n) (hfseq_mem n) (hgseq_mem n) hn
  exact le_of_tendsto habs_tend hbound_ev

/-- **A.e. sup-bound for `gpPath`.** On the good event (a.s. by `gpSkeleton_spec`)
the path `gpPath ω` has bounded range, hence finite sup-norm. -/
theorem ae_bddAbove_gpPath :
    ∀ᵐ ω ∂iidStdGaussian, BddAbove (Set.range
      (fun f : ↥F => |gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f|)) := by
  filter_upwards [(gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.2] with ω hω
  -- On the good set `gpPath ω = pathExtend ω`, whose range is bounded.
  have hb := bddAbove_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω
  obtain ⟨C, hC⟩ := hb
  refine ⟨C, ?_⟩
  rintro _ ⟨f, rfl⟩
  change |gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f| ≤ C
  rw [gpPath_apply_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω f]
  exact hC ⟨f, rfl⟩

/-- **Sup-norm overflow mass tends to `0`.** The events `{ω | M < ‖gpPath ω‖}`
decrease (in `M` along ℕ) to the null set `⋂ₙ {ω | n < ‖gpPath ω‖}` (a.e.
`gpPath ω` is sup-bounded), so by continuity of measure their mass tends to `0`.
Hence for any `ε > 0` there is `M` with
`iidStdGaussian {ω | M < ‖gpPath ω‖} ≤ ε`. -/
theorem exists_bound_mass {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ M : ℝ, iidStdGaussian {ω | M < ‖gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω‖} ≤ ε := by
  classical
  set g := gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne with hg
  -- `‖g ·‖` is a.e.-strongly-measurable.
  have hmeas : AEStronglyMeasurable (fun ω => ‖g ω‖) iidStdGaussian :=
    (gpPath_aestronglyMeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).norm
  -- Decreasing events `Eₙ = {ω | n < ‖g ω‖}`.
  set E : ℕ → Set (ℕ → ℝ) := fun n => {ω | (n : ℝ) < ‖g ω‖} with hE
  have hEmeas : ∀ n, NullMeasurableSet (E n) iidStdGaussian := by
    intro n
    have : E n = (fun ω => ‖g ω‖) ⁻¹' Set.Ioi (n : ℝ) := by
      ext ω; simp [hE, Set.mem_Ioi]
    rw [this]
    exact hmeas.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi
  have hanti : Antitone E := by
    intro m n hmn ω hω
    simp only [hE, Set.mem_setOf_eq] at hω ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hmn) hω
  -- `⋂ₙ Eₙ` is a.e.-null: a.e. `‖g ω‖` is finite, so eventually `n ≥ ‖g ω‖`.
  have hInter_null : iidStdGaussian (⋂ n, E n) = 0 := by
    refine measure_mono_null ?_ (measure_empty (μ := iidStdGaussian))
    intro ω hω
    simp only [Set.mem_iInter, hE, Set.mem_setOf_eq] at hω
    obtain ⟨n, hn⟩ := exists_nat_gt ‖g ω‖
    exact absurd (hω n) (not_lt.mpr hn.le)
  -- Continuity of measure: `μ (Eₙ) → μ (⋂ Eₙ) = 0`.
  have htendsto : Tendsto (fun n => iidStdGaussian (E n)) atTop (𝓝 (iidStdGaussian (⋂ n, E n))) :=
    tendsto_measure_iInter_atTop hEmeas hanti ⟨0, measure_ne_top _ _⟩
  rw [hInter_null] at htendsto
  -- Pick `n` with `μ (Eₙ) ≤ ε`.
  have hev : ∀ᶠ n in atTop, iidStdGaussian (E n) ≤ ε :=
    htendsto.eventually_le_const hε
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨(n : ℝ), hn⟩

/-- The complement `{ω | ‖gpPath ω‖ ≤ M}` translates the sup-norm bound into the
coordinatewise bound `∀ f, |gpPath ω f| ≤ M` used by `modulusBall`. -/
theorem forall_abs_le_of_norm_le {ω : ℕ → ℝ} {M : ℝ}
    (h : ‖gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω‖ ≤ M) (f : ↥F) :
    |gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f| ≤ M := by
  have := lp.norm_apply_le_norm ENNReal.top_ne_zero
    (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) f
  rw [Real.norm_eq_abs] at this
  exact this.trans h

/-- **`gpBridgeMeasure` is tight** (the measure half of the `G_P`-tightness field).
The singleton `{ν}` with `ν = iidStdGaussian.map gpPath` is a tight measure set on
`ℓ∞(F)`: given `ε > 0`, a compact modulus ball `K = modulusBall P F M δ η`
captures all but `ε` of the mass.

Route (`isTightMeasureSet_iff_exists_isCompact_measure_compl_le`):

* the chaining schedule `a` and its level masses come from `summable_bigOsc`
  (sub-Gaussian `gpX` increments with proxy `(distL2)²` + Dudley-finite entropy),
  so the level-oscillation tail `∑_{j ≥ J} μ(bigOsc gpX net j (a j)) ≤ ε/2` for
  some `J` (`ENNReal.tendsto_sum_nat_add`);
* a sup-bound `M` with `μ {M < ‖gpPath‖} ≤ ε/2` (`exists_bound_mass`, continuity
  of measure);
* `K = modulusBall P F M (2^{-(J+·)}) η`, `η k = a (J+k) + 2 ∑' i, a (J+k+i) → 0`,
  is compact (`isCompact_modulusBall`);
* `gpPath ⁻¹ Kᶜ ⊆ {¬gpGood} ∪ {M < ‖gpPath‖} ∪ ⋃_{j ≥ J} bigOsc gpX net j (a j)`,
  whose `iidStdGaussian`-mass is `0 + ε/2 + ε/2 = ε`
  (`gpPath_mem_modulusBall_of_avoid` lands every good, bounded, tail-avoiding `ω`
  in `K`). -/
theorem pBridge_tight :
    IsTightMeasureSet
      ({gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne} :
        Set (Measure (LinfF F))) := by
  classical
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  -- The Dudley dyadic net of `(↥F, distL2 P)` — *the same net the skeleton uses*
  -- (`gpSkeletonNet`), so `gpSkeleton = ⋃ j, net j` holds definitionally.
  set net : ℕ → Finset ↥F := gpSkeletonNet hF_meas hF_ent hF_ne with hnetdef
  obtain ⟨hnet, hmono, hDud⟩ := (exists_dudley_net hF_ent hF_ne).choose_spec
  -- Sub-Gaussian increments of `gpX` with proxy `K = 1` (proxy weakening as in `gpX_aeUC`).
  have hSG : ∀ s t : ↥F, ProbabilityTheory.HasSubgaussianMGF
      (fun ω => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep s ω
        - gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω)
      ⟨(1 : ℝ) ^ 2 * dist s t ^ 2, by positivity⟩ iidStdGaussian := by
    intro s t
    refine (gpX_subgaussian_increment ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep s t).mono_proxy ?_
    refine NNReal.coe_le_coe.mp ?_
    change distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2 ≤ (1 : ℝ) ^ 2 * dist s t ^ 2
    rw [one_pow, one_mul]
    change distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2 ≤ distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2
    exact le_refl _
  -- The chaining schedule `a` + level-mass summability.
  obtain ⟨a, ha_pos, ha_summable, ha_tsum⟩ :=
    GaussianChaining.summable_bigOsc (μ := iidStdGaussian) (X := gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep)
      (K := 1) zero_le_one net hSG hDud
  -- The deterministic modulus `η k = a (J + k) + 2 ∑' i, a (J + k + i)`; for any `J`
  -- it tends to `0` (shifted-tail summability), giving compactness of the ball.
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  -- Mass tail: pick `J` with `∑' k, μ (bigOsc gpX net (k + J) (a (k + J))) ≤ ε/2`.
  set bigm : ℕ → ℝ≥0∞ := fun j =>
    iidStdGaussian (GaussianChaining.bigOsc (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep) net j (a j))
    with hbigm
  have htail0 : Tendsto (fun J => ∑' k, bigm (k + J)) atTop (𝓝 0) :=
    ENNReal.tendsto_sum_nat_add bigm ha_tsum
  have hεhalf : (0 : ℝ≥0∞) < ε / 2 := ENNReal.half_pos (ne_of_gt hε)
  obtain ⟨J, hJ⟩ := (htail0.eventually_le_const hεhalf).exists
  -- Bound `M` with overflow mass `≤ ε/2`.
  obtain ⟨M, hMmass⟩ := exists_bound_mass hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hεhalf
  -- The compact modulus ball.
  set δ : ℕ → ℝ := fun k => (2 : ℝ) ^ (-((J + k : ℕ) : ℤ)) with hδdef
  set η : ℕ → ℝ := fun k => a (J + k) + 2 * ∑' i : ℕ, a (J + k + i) with hηdef
  have hδ_pos : ∀ k, 0 < δ k := fun k => by positivity
  have ha_shift_all : ∀ K : ℕ, Summable (fun i : ℕ => a (K + i)) := by
    intro K
    have := (summable_nat_add_iff K).mpr ha_summable
    simpa [add_comm] using this
  have hη_tendsto : Tendsto η atTop (𝓝 0) := by
    -- `a (J + ·) → 0` and the double-shifted tail `∑' i, a (J + · + i) → 0`.
    have hA : Tendsto (fun k => a (J + k)) atTop (𝓝 0) := by
      have h0 := ha_summable.tendsto_atTop_zero
      have : Tendsto (fun k => a (k + J)) atTop (𝓝 0) := h0.comp (tendsto_add_atTop_nat J)
      simpa [add_comm] using this
    have hTail : Tendsto (fun k => ∑' i : ℕ, a (J + k + i)) atTop (𝓝 0) := by
      -- `∑' i, a (J + k + i) = ∑' i, a (k + (J + i))`; tail of the summable `fun i => a (J + i)`.
      have hbase := tendsto_sum_nat_add (fun i => a (J + i))
      have hcongr : (fun k => ∑' i : ℕ, a (J + k + i))
          = (fun k => ∑' i : ℕ, (fun n => a (J + n)) (i + k)) := by
        funext k; congr 1; funext i; congr 1; omega
      rw [hcongr]; exact hbase
    have := hA.add (hTail.const_mul 2)
    simpa [hηdef] using this
  have hK_compact : IsCompact (modulusBall P F M δ η) :=
    isCompact_modulusBall hF_ent M δ η hδ_pos hη_tendsto
  refine ⟨modulusBall P F M δ η, hK_compact, ?_⟩
  intro μ hμ
  rw [Set.mem_singleton_iff] at hμ
  subst hμ
  -- `ν Kᶜ = iidStdGaussian (gpPath ⁻¹ Kᶜ)` (map_apply; `Kᶜ` measurable since `K` closed).
  have hKclosed : IsClosed (modulusBall P F M δ η) := isClosed_modulusBall P F M δ η
  have hKcompl_meas : MeasurableSet (modulusBall P F M δ η)ᶜ :=
    hKclosed.measurableSet.compl
  rw [gpBridgeMeasure,
    Measure.map_apply_of_aemeasurable
      (gpPath_aemeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) hKcompl_meas]
  -- The cover of the preimage.
  set good : Set (ℕ → ℝ) := {ω | gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω} with hgood
  set boundE : Set (ℕ → ℝ) :=
    {ω | M < ‖gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω‖} with hboundE
  set tailE : Set (ℕ → ℝ) := ⋃ j ∈ {j : ℕ | J ≤ j},
    GaussianChaining.bigOsc (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep) net j (a j) with htailE
  have hcover : gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ⁻¹'
      (modulusBall P F M δ η)ᶜ ⊆ goodᶜ ∪ boundE ∪ tailE := by
    intro ω hω
    rw [Set.mem_preimage, Set.mem_compl_iff] at hω
    by_contra hmem
    simp only [Set.mem_union, not_or] at hmem
    obtain ⟨⟨hng, hnb⟩, hnt⟩ := hmem
    -- `ω` is good, sup-bounded by `M`, and avoids the bigOsc tail ⟹ `gpPath ω ∈ K`.
    have hgω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω := by
      by_contra h; exact hng h
    have hboundω : ‖gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω‖ ≤ M := by
      rw [hboundE, Set.mem_setOf_eq, not_lt] at hnb; exact hnb
    have hMω : ∀ f, |gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f| ≤ M :=
      fun f => forall_abs_le_of_norm_le hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hboundω f
    have havoidω : ∀ m ≥ J, ω ∉ GaussianChaining.bigOsc
        (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep) net m (a m) := by
      intro m hm hmemb
      exact hnt (Set.mem_biUnion hm hmemb)
    -- Net–skeleton alignment: `gpSkeleton = ⋃ j, net j` (both from `exists_dudley_net`).
    have hskel : gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
        = ⋃ j : ℕ, (↑(net j) : Set ↥F) :=
      gpSkeleton_eq_iUnion_net hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
    have := gpPath_mem_modulusBall_of_avoid hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      net hnet hmono hskel ha_pos ha_summable M hgω hMω (J := J) havoidω
    -- The lemma lands `gpPath ω` in `modulusBall … δ η` (same schedules by definition).
    exact hω this
  -- Mass bound on the cover.
  calc iidStdGaussian (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ⁻¹'
          (modulusBall P F M δ η)ᶜ)
      ≤ iidStdGaussian (goodᶜ ∪ boundE ∪ tailE) := measure_mono hcover
    _ ≤ iidStdGaussian (goodᶜ ∪ boundE) + iidStdGaussian tailE := measure_union_le _ _
    _ ≤ (iidStdGaussian goodᶜ + iidStdGaussian boundE) + iidStdGaussian tailE := by
        gcongr; exact measure_union_le _ _
    _ ≤ (0 + ε / 2) + ε / 2 := by
        -- `goodᶜ` is null: `gpGood` holds a.e.
        have hgood0 : iidStdGaussian goodᶜ ≤ 0 := by
          have hae : ∀ᵐ ω ∂iidStdGaussian,
              gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω :=
            (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.2
          exact (ae_iff.mp hae).le
        -- `tailE` mass `≤ ∑' k, bigm (k + J) ≤ ε/2`.
        have htail2 : iidStdGaussian tailE ≤ ε / 2 := by
          refine le_trans ?_ hJ
          rw [htailE]
          calc iidStdGaussian (⋃ j ∈ {j : ℕ | J ≤ j},
                  GaussianChaining.bigOsc (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep) net j (a j))
              ≤ ∑' j : {j : ℕ // J ≤ j}, bigm j := by
                rw [Set.biUnion_eq_iUnion]
                exact measure_iUnion_le _
            _ = ∑' k : ℕ, bigm (k + J) := by
                -- reindex `{j // J ≤ j} ≃ ℕ` via `j ↦ j - J`, `k ↦ k + J`.
                let e : ℕ ≃ {j : ℕ // J ≤ j} :=
                  ⟨fun k => ⟨k + J, by omega⟩, fun j => j.1 - J, fun k => by simp,
                    fun j => by ext; simp; omega⟩
                rw [← Equiv.tsum_eq e (fun j : {j : ℕ // J ≤ j} => bigm j.1)]
                rfl
        exact add_le_add (add_le_add hgood0 hMmass) htail2
    _ = ε := by rw [zero_add, ENNReal.add_halves]

include hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne in
/-- **Existence of the tight `P`-Brownian-bridge law `G_P`.** Assembled from the
six `IsPBrownianBridge` field lemmas for the candidate law
`ν = gpBridgeMeasure` (`= iidStdGaussian.map gpPath`): probability measure
(`pBridge_isProbabilityMeasure`), Brownian-bridge covariance (`pBridge_cov`),
zero coordinate means (`pBridge_mean`), centred Gaussian finite-dimensional
marginals (`pBridge_isGaussian_fdd`), tightness of the Borel law
(`pBridge_tight`), and concentration on the `distL2 P`-uniformly-continuous
sample paths (`pBridge_ucPaths`).

The envelope and entropy assumptions are those of the bracketing criterion in
vdV §19.2, while the Hilbert-space assumptions select the Gaussian-process
construction used here:

* `hG_env` and `hG` give `F` a square-integrable envelope `G`.
* `hF_meas` makes every member of `F` measurable.
* `hH_inf` restricts the construction to an infinite-dimensional Gaussian
  Hilbert space; finite-dimensional carriers are handled by the separate
  finite-carrier construction.
* `hH_sep` supplies separability of the Gaussian Hilbert space. In this setting
  it also follows from `hF_ent` through `totallyBounded_L2`.
* `hF_ent` states finiteness of the bracketing-entropy integral.
* `hF_ne` states that `F` is nonempty. -/
theorem exists_pBrownianBridge :
    ∃ ν : Measure (LinfF F),
      IsPBrownianBridge F P ν :=
  ⟨gpBridgeMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne,
    { isProbabilityMeasure :=
        pBridge_isProbabilityMeasure hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      cov := pBridge_cov hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      mean := pBridge_mean hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      isGaussian_fdd := pBridge_isGaussian_fdd hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      tight := pBridge_tight hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      ucPaths := pBridge_ucPaths hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne }⟩

/-- The **`P`-Brownian-bridge law `G_P`** on `ℓ∞(F)`: the chosen witness of
`exists_pBrownianBridge`. This is the tight Gaussian limit to which the empirical
process `𝔾ₙ` converges (in outer expectation `⇝ₒ`) for a `P`-Donsker class. -/
noncomputable def gaussianPBridge : Measure (LinfF F) :=
  (exists_pBrownianBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).choose

include hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne in
/-- The chosen `gaussianPBridge` witness satisfies the `IsPBrownianBridge`
specification. -/
lemma isPBrownianBridge_gaussianPBridge :
    IsPBrownianBridge F P
      (gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :=
  (exists_pBrownianBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).choose_spec

include hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne in
/-- **Mean-zero coordinate marginals of `G_P`.** Each coordinate evaluation
`z ↦ z f` has integral `0` under the chosen Brownian-bridge law `gaussianPBridge`
(the `mean` field of `isPBrownianBridge_gaussianPBridge`). -/
lemma gaussianPBridge_mean (f : ↥F) :
    ∫ z : LinfF F, (z f)
        ∂(gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) = 0 :=
  (isPBrownianBridge_gaussianPBridge hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).mean f

end Tight

end AsymptoticStatistics.EmpiricalProcess
