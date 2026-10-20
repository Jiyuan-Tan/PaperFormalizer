module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.DonskerBracketing
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

/-!
# Example 19.7: a Lipschitz-parametrized class is `P`-Donsker

Let `Θ ⊆ ℝ^k` be bounded and let `ψ : Θ → (Fin k → (Ω → ℝ))` index a
finite-dimensional family of functions. Suppose the family is **Lipschitz in
the parameter**, uniformly over a common `L²(P)` envelope `m`:

  `|ψ_{θ₁, j}(x) − ψ_{θ₂, j}(x)| ≤ m(x) · ‖θ₁ − θ₂‖`,  `Pm² < ∞`.

Then the class `𝓕 = { ψ_{θ, j} : θ ∈ Θ, j ∈ Fin k }` has finite bracketing
entropy integral, hence is `P`-Donsker (vdV Example 19.7, book p.271-272,
PDF p.286-287). Concretely, an `ε`-net `S` of `Θ` induces `k · |S|` brackets
`[ψ_{c, j} − εm, ψ_{c, j} + εm]` of `L²(P)`-size `2ε‖m‖_{P,2}`, so
`N_{[]}(2ε‖m‖₂, 𝓕, L²(P)) ≤ k · |S| ≤ k · (C/ε)^k`; the polynomial covering
bound makes `∫₀¹ √(log N_{[]}) dε < ∞`.

The Donsker property supplies the asymptotic equicontinuity used in the
Z-estimator normality theorem via `IsPDonsker.asymptoticallyEquicontinuous`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology NNReal

/-- The **Lipschitz-parametrized class** `𝓕 = { ψ_{θ, j} : θ ∈ Θ, j ∈ Fin k }`:
all coordinate functions `ψ θ j` obtained as `θ` ranges over the parameter set
`Θ ⊆ ℝ^k` and `j` over the `k` fibers.

vdV Example 19.7 (book p.271): the class indexed by a bounded Euclidean
parameter set. The `j : Fin k` index gathers the `k` coordinate maps that share
the common `L²` envelope `m` and Lipschitz modulus. -/
def paramClass {k : ℕ} {Ω : Type*} (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (Θ : Set (EuclideanSpace ℝ (Fin k))) : Set (Ω → ℝ) :=
  {g | ∃ θ ∈ Θ, ∃ j, g = ψ θ j}

/-- **Finite-dimensional covering bound for a bounded Euclidean set.**

A bounded set `Θ ⊆ ℝ^k` admits, for every scale `ε > 0`, a finite `ε`-net `S`
(a finite subset with `Θ ⊆ ⋃_{c ∈ S} B(c, ε)`) whose cardinality is polynomial
in `1/ε`: `|S| ≤ (C/ε)^k` for a constant `C` depending only on `Θ`.

For vdV Example 19.7, take a maximal `ε`-separated
subset `S ⊆ Θ`; maximality forces `S` to be an `ε`-cover, and the disjoint
half-balls `B(c, ε/2)` all sit inside `B(x₀, R + ε/2)`, so the Haar-volume count
`|S| · vol(B(·, ε/2)) ≤ vol(B(·, R + ε/2))` with `vol(B(·, r)) ∝ r^k` gives the
bound. -/
theorem coveringNumber_le_of_bounded_euclidean {k : ℕ}
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ : Bornology.IsBounded Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ S : Finset (EuclideanSpace ℝ (Fin k)),
        ↑S ⊆ Θ ∧ Θ ⊆ ⋃ c ∈ S, Metric.ball c ε ∧ (S.card : ℝ) ≤ (C / ε) ^ k := by
  obtain ⟨R, hR⟩ := hΘ.subset_closedBall (0 : EuclideanSpace ℝ (Fin k))
  set R' := max R 0 with hR'def
  have hR'0 : (0 : ℝ) ≤ R' := le_max_right R 0
  have hΘR' : Θ ⊆ Metric.closedBall 0 R' :=
    hR.trans (Metric.closedBall_subset_closedBall (le_max_left R 0))
  refine ⟨4 * R' + 1, by positivity, fun ε hε hε1 => ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk1
  · -- k = 0: the ambient space is a subsingleton, so a single ball covers everything.
    subst hk0
    rcases Set.eq_empty_or_nonempty Θ with hΘe | ⟨x₀, hx₀⟩
    · refine ⟨∅, ?_, ?_, ?_⟩
      · simp
      · rw [hΘe]; exact Set.empty_subset _
      · simp
    · refine ⟨{x₀}, ?_, ?_, ?_⟩
      · rw [Finset.coe_singleton]; exact Set.singleton_subset_iff.mpr hx₀
      · intro x _
        simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop]
        exact ⟨x₀, rfl, by
          rw [Subsingleton.elim x x₀]; exact Metric.mem_ball_self hε⟩
      · simp
  · -- k ≥ 1: volume-packing count of a maximal (ε/2)-separated set.
    haveI : Nonempty (Fin k) := ⟨⟨0, hk1⟩⟩
    -- The Euclidean ball-volume constant `cst = √π^k / Γ(k/2+1)`.
    set cst : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt Real.pi ^ k / Real.Gamma ((k : ℝ) / 2 + 1))
      with hcst
    have hcst_top : cst ≠ ⊤ := ENNReal.ofReal_ne_top
    have hcst_pos : 0 < cst := by
      rw [hcst, ENNReal.ofReal_pos]
      exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) k)
        (Real.Gamma_pos_of_pos (by positivity))
    have hcst_ne : cst ≠ 0 := hcst_pos.ne'
    have hvol : ∀ (c : EuclideanSpace ℝ (Fin k)) (ρ : ℝ),
        volume (Metric.ball c ρ) = (ENNReal.ofReal ρ) ^ k * cst := by
      intro c ρ
      rw [EuclideanSpace.volume_ball, Fintype.card_fin, hcst]
    -- The separation radius `η = ε/2` as a nonnegative real.
    set η : ℝ≥0 := (ε / 2).toNNReal with hηdef
    have hη : (η : ℝ) = ε / 2 := Real.coe_toNNReal _ (by positivity)
    have hη_ne : η ≠ 0 := by
      rw [← NNReal.coe_ne_zero, hη]; exact (by positivity : (0 : ℝ) < ε / 2).ne'
    -- `Θ` is totally bounded (bounded in a proper space), so its packing number is finite.
    have htb : TotallyBounded Θ :=
      (ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin k)) R').totallyBounded.subset
        hΘR'
    obtain ⟨N, _hN_sub, hN_fin, hN_cover⟩ :=
      Metric.exists_finite_isCover_of_totallyBounded (div_ne_zero hη_ne two_ne_zero) htb
    have hpack_ne : Metric.packingNumber η Θ ≠ ⊤ := by
      have h1 : Metric.packingNumber (2 * (η / 2)) Θ ≤ Metric.externalCoveringNumber (η / 2) Θ :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber (η / 2) Θ
      have h2 : Metric.externalCoveringNumber (η / 2) Θ ≤ N.encard :=
        hN_cover.externalCoveringNumber_le_encard
      have h22 : (2 : ℝ≥0) * (η / 2) = η := by
        rw [mul_comm]; exact div_mul_cancel₀ η two_ne_zero
      rw [h22] at h1
      exact ne_top_of_le_ne_top hN_fin.encard_lt_top.ne (h1.trans h2)
    -- The maximal `η`-separated set `S`: it covers `Θ` and its half-balls are disjoint.
    set S : Set (EuclideanSpace ℝ (Fin k)) := Metric.maximalSeparatedSet η Θ with hSdef
    have hS_fin : S.Finite := by
      rw [← Set.encard_ne_top_iff, hSdef, Metric.encard_maximalSeparatedSet hpack_ne]
      exact hpack_ne
    have hS_cover : Metric.IsCover η Θ S := Metric.isCover_maximalSeparatedSet hpack_ne
    have hS_sep : Metric.IsSeparated (η : ℝ≥0∞) S := Metric.isSeparated_maximalSeparatedSet
    have hS_subΘ : S ⊆ Θ := Metric.maximalSeparatedSet_subset
    refine ⟨hS_fin.toFinset, ?_, ?_, ?_⟩
    · -- `S ⊆ Θ` (centers are points of `Θ`).
      rw [hS_fin.coe_toFinset]; exact hS_subΘ
    · -- Cover: closed `η`-balls of `S` sit inside open `ε`-balls (`η = ε/2 < ε`).
      intro x hx
      have hxc := hS_cover.subset_iUnion_closedBall hx
      simp only [Set.mem_iUnion, exists_prop] at hxc ⊢
      obtain ⟨y, hyS, hxy⟩ := hxc
      refine ⟨y, hS_fin.mem_toFinset.mpr hyS, ?_⟩
      rw [Metric.mem_closedBall] at hxy
      rw [Metric.mem_ball]
      calc dist x y ≤ (η : ℝ) := hxy
        _ = ε / 2 := hη
        _ < ε := by linarith
    · -- Cardinality: `|S| · vol(ball ε/4) ≤ vol(ball (R'+ε/4))`.
      have hdisj : (hS_fin.toFinset : Set (EuclideanSpace ℝ (Fin k))).PairwiseDisjoint
          (fun c => Metric.ball c (ε / 4)) := by
        intro a ha b hb hab
        rw [hS_fin.coe_toFinset] at ha hb
        have hsep := hS_sep ha hb hab
        have hsep' : ENNReal.ofReal (η : ℝ) < ENNReal.ofReal (dist a b) := by
          rw [ENNReal.ofReal_coe_nnreal, ← edist_dist]; exact hsep
        have hdd : (ε / 2 : ℝ) < dist a b := by
          have := (ENNReal.ofReal_lt_ofReal_iff'.mp hsep').1
          rwa [hη] at this
        exact Metric.ball_disjoint_ball (by linarith)
      have hsub : (⋃ c ∈ hS_fin.toFinset, Metric.ball c (ε / 4)) ⊆
          Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (R' + ε / 4) := by
        intro z hz
        simp only [Set.mem_iUnion, exists_prop] at hz
        obtain ⟨c, hcS, hzc⟩ := hz
        have hc_mem : c ∈ Θ := hS_subΘ (hS_fin.mem_toFinset.mp hcS)
        have hcR : dist c 0 ≤ R' := by rw [← Metric.mem_closedBall]; exact hΘR' hc_mem
        exact Metric.ball_subset_ball' (by linarith) hzc
      have hunion : volume (⋃ c ∈ hS_fin.toFinset, Metric.ball c (ε / 4))
          = ∑ c ∈ hS_fin.toFinset, volume (Metric.ball c (ε / 4)) :=
        measure_biUnion_finset hdisj (fun b _ => measurableSet_ball)
      have hsum : ∑ c ∈ hS_fin.toFinset, volume (Metric.ball c (ε / 4))
          = (hS_fin.toFinset.card : ℝ≥0∞) * ((ENNReal.ofReal (ε / 4)) ^ k * cst) := by
        rw [Finset.sum_congr rfl (fun c _ => hvol c (ε / 4)), Finset.sum_const, nsmul_eq_mul]
      have hle1 : (hS_fin.toFinset.card : ℝ≥0∞) * ((ENNReal.ofReal (ε / 4)) ^ k * cst)
          ≤ (ENNReal.ofReal (R' + ε / 4)) ^ k * cst := by
        rw [← hsum, ← hunion]
        exact (measure_mono hsub).trans_eq (hvol 0 (R' + ε / 4))
      rw [← mul_assoc] at hle1
      have hle2 : (hS_fin.toFinset.card : ℝ≥0∞) * (ENNReal.ofReal (ε / 4)) ^ k
          ≤ (ENNReal.ofReal (R' + ε / 4)) ^ k :=
        (ENNReal.mul_le_mul_iff_left hcst_ne hcst_top).mp hle1
      have hεk : (0 : ℝ) ≤ ε / 4 := by positivity
      have hRk : (0 : ℝ) ≤ R' + ε / 4 := by positivity
      have hfin_L : (hS_fin.toFinset.card : ℝ≥0∞) * (ENNReal.ofReal (ε / 4)) ^ k ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      have hfin_R : (ENNReal.ofReal (R' + ε / 4)) ^ k ≠ ⊤ :=
        ENNReal.pow_ne_top ENNReal.ofReal_ne_top
      have hle3 : (hS_fin.toFinset.card : ℝ) * (ε / 4) ^ k ≤ (R' + ε / 4) ^ k := by
        have h := (ENNReal.toReal_le_toReal hfin_L hfin_R).mpr hle2
        rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hεk,
          ENNReal.toReal_pow, ENNReal.toReal_ofReal hRk, ENNReal.toReal_natCast] at h
      have hr_pos : (0 : ℝ) < ε / 4 := by positivity
      have hcard_le : (hS_fin.toFinset.card : ℝ) ≤ ((R' + ε / 4) / (ε / 4)) ^ k := by
        rw [div_pow, le_div_iff₀ (pow_pos hr_pos k)]
        exact hle3
      have hratio : (R' + ε / 4) / (ε / 4) ≤ (4 * R' + 1) / ε := by
        rw [div_le_div_iff₀ hr_pos hε]
        nlinarith [mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 1 - ε), hR'0, hε.le]
      calc (hS_fin.toFinset.card : ℝ)
          ≤ ((R' + ε / 4) / (ε / 4)) ^ k := hcard_le
        _ ≤ ((4 * R' + 1) / ε) ^ k := by
            apply pow_le_pow_left₀ (by positivity) hratio

/-- **An `ε`-net of `Θ` (by points of `Θ`) yields a bracketing cover.**

Given an `ε`-net `S ⊆ Θ` of `Θ` (with `Θ ⊆ ⋃_{c ∈ S} B(c, ε)`), the `k · |S|`
brackets `[ψ_{c, j} − ε|m|, ψ_{c, j} + ε|m|]` for `(c, j) ∈ S × Fin k` form a
bracketing cover of `paramClass ψ Θ` in `L²(P)` of size `2ε‖m‖_{P,2}`. Indeed
for `g = ψ_{θ, j}` pick `c ∈ S` with `θ ∈ B(c, ε)`; the Lipschitz bound
`|ψ_{θ,j} − ψ_{c,j}| ≤ m · ‖θ − c‖ ≤ ε|m|` places `g` inside the `c`-bracket,
which has `L²(P)`-size `‖2ε|m|‖_{P,2} = 2ε‖m‖_{P,2}`.

The scale is a *strict* upper bound `2ε‖m‖_{P,2} < s` because `IsEpsBracket`
requires the strict size inequality; the harmless inflation is absorbed by the
entropy integral below. This is the covering-to-bracketing step in vdV
Example 19.7. -/
theorem bracketingNumber_le_of_lipschitz {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (Θ : Set (EuclideanSpace ℝ (Fin k)))
    (m : Ω → ℝ) (hm : MemLp m 2 P) (hm_meas : Measurable m)
    (hψ_meas : ∀ θ ∈ Θ, ∀ j, Measurable (ψ θ j))
    (hψ_L2 : ∀ θ ∈ Θ, ∀ j, MemLp (ψ θ j) 2 P)
    (hLip : ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ (j : Fin k) (x : Ω),
      |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖)
    {ε : ℝ} (hε : 0 < ε) {S : Finset (EuclideanSpace ℝ (Fin k))}
    (hSΘ : ↑S ⊆ Θ) (hnet : Θ ⊆ ⋃ c ∈ S, Metric.ball c ε)
    {s : ℝ} (hs : 2 * ε * (eLpNorm m 2 P).toReal < s) :
    bracketingNumber s (paramClass ψ Θ) 2 P ≤ ((k * S.card : ℕ) : ℕ∞) := by
  classical
  set M : ℝ := (eLpNorm m 2 P).toReal with hMdef
  have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
  have hs_pos : 0 < s := lt_of_le_of_lt (by positivity : (0:ℝ) ≤ 2 * ε * M) hs
  -- The per-center bracket `[ψ c j − ε|m|, ψ c j + ε|m|]` is an `s`-bracket.
  have hbracket : ∀ c ∈ Θ, ∀ j : Fin k,
      IsEpsBracket s (fun x => ψ c j x - ε * ‖m x‖) (fun x => ψ c j x + ε * ‖m x‖) 2 P := by
    intro c hc j
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; nlinarith [norm_nonneg (m x), hε.le]
    · exact (hψ_meas c hc j).sub (measurable_const.mul hm_meas.norm)
    · exact (hψ_meas c hc j).add (measurable_const.mul hm_meas.norm)
    · exact (hψ_L2 c hc j).sub (hm.norm.const_mul' ε)
    · exact (hψ_L2 c hc j).add (hm.norm.const_mul' ε)
    · -- Size: `eLpNorm (2ε|m|) 2 P = ofReal (2ε) * eLpNorm m 2 P = ofReal (2εM) < ofReal s`.
      have huml : (fun x => (ψ c j x + ε * ‖m x‖) - (ψ c j x - ε * ‖m x‖))
                  = (2 * ε) • (fun x => ‖m x‖) := by
        funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
      rw [huml, eLpNorm_const_smul, eLpNorm_norm]
      have hfin : eLpNorm m 2 P = ENNReal.ofReal M := (ENNReal.ofReal_toReal hm.2.ne).symm
      rw [hfin, Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff hs_pos).mpr hs
  -- Enumerate the `k · |S|` brackets via an equiv `Fin (k*|S|) ≃ Fin k × ↥S`.
  have hcard : Fintype.card (Fin k × ↥S) = k * S.card := by
    simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  let e : Fin (k * S.card) ≃ Fin k × ↥S := (Fintype.equivFinOfCardEq hcard).symm
  refine iInf_le_of_le (k * S.card) (iInf_le_of_le ?_ le_rfl)
  refine ⟨fun i => fun x => ψ (e i).2.1 (e i).1 x - ε * ‖m x‖,
          fun i => fun x => ψ (e i).2.1 (e i).1 x + ε * ‖m x‖, ?_, ?_⟩
  · -- every bracket is an `s`-bracket
    intro i
    exact hbracket (e i).2.1 (hSΘ (Finset.mem_coe.mpr (e i).2.2)) (e i).1
  · -- covering: each `ψ θ j` lands in the bracket of a nearby center
    rintro f ⟨θ, hθ, j, rfl⟩
    have hθU := hnet hθ
    simp only [Set.mem_iUnion, exists_prop] at hθU
    obtain ⟨c, hcS, hθc⟩ := hθU
    refine ⟨e.symm (j, ⟨c, hcS⟩), fun x => ?_⟩
    have hcΘ : c ∈ Θ := hSΘ (Finset.mem_coe.mpr hcS)
    -- reduce the bracket at index `e.symm (j, ⟨c, hcS⟩)` to the `(c, j)`-bracket
    simp only [Equiv.apply_symm_apply]
    -- `|ψ θ j x − ψ c j x| ≤ ε ‖m x‖`
    have hmc : ‖θ - c‖ ≤ ε := by
      rw [← dist_eq_norm]; exact le_of_lt (Metric.mem_ball.mp hθc)
    have hlip := hLip θ hθ c hcΘ j x
    have habs : |ψ θ j x - ψ c j x| ≤ ε * ‖m x‖ := by
      calc |ψ θ j x - ψ c j x| ≤ m x * ‖θ - c‖ := hlip
        _ ≤ ‖m x‖ * ‖θ - c‖ :=
            mul_le_mul_of_nonneg_right (Real.le_norm_self (m x)) (norm_nonneg _)
        _ ≤ ‖m x‖ * ε := mul_le_mul_of_nonneg_left hmc (norm_nonneg _)
        _ = ε * ‖m x‖ := mul_comm _ _
    have h := abs_le.mp habs
    exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Subadditivity of the square root: `√(a + b) ≤ √a + √b` for `a, b ≥ 0`.
(Mathlib has no packaged `Real.sqrt_add_le`; prove via `(√a + √b)² ≥ a + b`.) -/
private lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [show a + b = Real.sqrt a ^ 2 + Real.sqrt b ^ 2 by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]]
  calc Real.sqrt (Real.sqrt a ^ 2 + Real.sqrt b ^ 2)
      ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := by
        apply Real.sqrt_le_sqrt; nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

/-- **Finite bracketing entropy integral for the Lipschitz class.**

Combining the polynomial `ε`-net bound and the induced bracketing cover with the substitution
`ε = s / (4‖m‖_{P,2} + 1)` gives `N_{[]}(s, 𝓕, L²(P)) ≤ k · (C'/s)^k` for every
`0 < s ≤ 1`; the integrand `√(log(1 + k(C'/s)^k)) ≲ (√A + √k)·s^{-1/2}` is
Lebesgue-integrable on `(0, 1]`, so the bracketing entropy integral
`J_{[]}(1, 𝓕, L²(P))` is finite.

Requires each `ψ θ j` measurable (`hψ_meas`) and in `L²(P)` (`hψ_L2`) so that the
brackets `[ψ_c j − ε|m|, ψ_c j + ε|m|]` satisfy the `IsEpsBracket` data.

This is the entropy-integral step in vdV Example 19.7. -/
theorem parametricClass_bracketingEntropyIntegral_lt_top {k : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ : Bornology.IsBounded Θ)
    (m : Ω → ℝ) (hm : MemLp m 2 P) (hm_meas : Measurable m)
    (hψ_meas : ∀ θ ∈ Θ, ∀ j, Measurable (ψ θ j))
    (hψ_L2 : ∀ θ ∈ Θ, ∀ j, MemLp (ψ θ j) 2 P)
    (hLip : ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ (j : Fin k) (x : Ω),
      |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖) :
    bracketingEntropyIntegral 1 (paramClass ψ Θ) P < ⊤ := by
  obtain ⟨C, hC0, hE1⟩ := coveringNumber_le_of_bounded_euclidean Θ hΘ
  set M : ℝ := (eLpNorm m 2 P).toReal with hMdef
  have hMnn : 0 ≤ M := ENNReal.toReal_nonneg
  set C' : ℝ := C * (4 * M + 1) with hC'def
  have hC'0 : 0 < C' := by rw [hC'def]; positivity
  set A : ℝ := Real.log (1 + (k : ℝ) * C' ^ k) with hAdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    exact Real.log_nonneg (by nlinarith [mul_nonneg (Nat.cast_nonneg k) (pow_nonneg hC'0.le k)])
  set B : ℝ := Real.sqrt A + Real.sqrt (k : ℝ) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  -- Pointwise domination of the entropy integrand on `(0, 1]`.
  have hdom : ∀ s ∈ Set.Ioc (0 : ℝ) 1,
      entropyIntegrand s (paramClass ψ Θ) P ≤ ENNReal.ofReal (B * s ^ (-(1/2) : ℝ)) := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hden : (0 : ℝ) < 4 * M + 1 := by positivity
    set ε : ℝ := s / (4 * M + 1) with hεdef
    have hε0 : 0 < ε := by rw [hεdef]; positivity
    have hε1 : ε ≤ 1 := by rw [hεdef, div_le_one hden]; linarith [hMnn, hs1]
    obtain ⟨S, hSΘ, hcover, hScard⟩ := hE1 ε hε0 hε1
    -- The induced brackets have size `2εM < s`.
    have hlt : 2 * ε * M < s := by
      rw [hεdef, show 2 * (s / (4 * M + 1)) * M = (2 * M * s) / (4 * M + 1) by ring,
        div_lt_iff₀ hden]
      nlinarith [hs0, hMnn, mul_nonneg hs0.le hMnn]
    have hE2 := bracketingNumber_le_of_lipschitz P ψ Θ m hm hm_meas hψ_meas hψ_L2 hLip
      hε0 hSΘ hcover hlt
    -- `C / ε = C' / s`.
    have hCe : C / ε = C' / s := by rw [hεdef, hC'def]; field_simp
    have hcard_le : ((k * S.card : ℕ) : ℝ) ≤ (k : ℝ) * (C' / s) ^ k := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left (by rw [← hCe]; exact hScard) (Nat.cast_nonneg k)
    -- Analytic bound `√(log(1 + k(C'/s)^k)) ≤ B s^{-1/2}`.
    have hxpos : (0 : ℝ) < 1 / s := by positivity
    have hx1 : (1 : ℝ) ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
    have hpow1 : (1 : ℝ) ≤ (1 / s) ^ k := one_le_pow₀ hx1
    have hCs : (C' / s) ^ k = C' ^ k * (1 / s) ^ k := by rw [div_pow, one_div_pow]; ring
    have hstep1 : 1 + (k : ℝ) * (C' / s) ^ k ≤ (1 + (k : ℝ) * C' ^ k) * (1 / s) ^ k := by
      rw [hCs, show (1 + (k : ℝ) * C' ^ k) * (1 / s) ^ k
        = (1 / s) ^ k + (k : ℝ) * (C' ^ k * (1 / s) ^ k) by ring]
      linarith [hpow1]
    have harg_pos : (0 : ℝ) < 1 + (k : ℝ) * (C' / s) ^ k := by
      have : (0 : ℝ) ≤ (k : ℝ) * (C' / s) ^ k := by positivity
      linarith
    have hlog1 : Real.log (1 + (k : ℝ) * (C' / s) ^ k) ≤ A + (k : ℝ) * (1 / s) := by
      have hApos : (0 : ℝ) < 1 + (k : ℝ) * C' ^ k := by
        have : (0 : ℝ) ≤ (k : ℝ) * C' ^ k := by positivity
        linarith
      have hpk : (0 : ℝ) < (1 / s) ^ k := by positivity
      calc Real.log (1 + (k : ℝ) * (C' / s) ^ k)
          ≤ Real.log ((1 + (k : ℝ) * C' ^ k) * (1 / s) ^ k) := Real.log_le_log harg_pos hstep1
        _ = A + (k : ℝ) * Real.log (1 / s) := by
            rw [Real.log_mul hApos.ne' hpk.ne', Real.log_pow, hAdef]
        _ ≤ A + (k : ℝ) * (1 / s) := by
            have hls : Real.log (1 / s) ≤ 1 / s - 1 := Real.log_le_sub_one_of_pos hxpos
            nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ)), hls]
    have hsqrt_s_pos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
    have hsqrt_s_le : Real.sqrt s ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs1
    have hss : s ^ (-(1/2) : ℝ) = (Real.sqrt s)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs0.le]
    have hpoint : Real.sqrt (Real.log (1 + (k : ℝ) * (C' / s) ^ k)) ≤ B * s ^ (-(1/2) : ℝ) := by
      calc Real.sqrt (Real.log (1 + (k : ℝ) * (C' / s) ^ k))
          ≤ Real.sqrt (A + (k : ℝ) * (1 / s)) := Real.sqrt_le_sqrt hlog1
        _ ≤ Real.sqrt A + Real.sqrt ((k : ℝ) * (1 / s)) :=
            sqrt_add_le A ((k : ℝ) * (1 / s)) hAnn (by positivity)
        _ = Real.sqrt A + Real.sqrt (k : ℝ) / Real.sqrt s := by
            rw [Real.sqrt_mul (Nat.cast_nonneg k), one_div, Real.sqrt_inv]; ring
        _ ≤ Real.sqrt A / Real.sqrt s + Real.sqrt (k : ℝ) / Real.sqrt s := by
            have : Real.sqrt A ≤ Real.sqrt A / Real.sqrt s := by
              rw [le_div_iff₀ hsqrt_s_pos]; nlinarith [Real.sqrt_nonneg A, hsqrt_s_le]
            linarith
        _ = B * s ^ (-(1/2) : ℝ) := by rw [hBdef, hss]; ring
    -- Combine the bracketing bound with the analytic domination.
    have hEI := entropyWeight_mono hE2
    rw [entropyWeight_coe] at hEI
    refine le_trans hEI ?_
    apply ENNReal.ofReal_le_ofReal
    calc Real.sqrt (Real.log (1 + ((k * S.card : ℕ) : ℝ)))
        ≤ Real.sqrt (Real.log (1 + (k : ℝ) * (C' / s) ^ k)) := by
          apply Real.sqrt_le_sqrt
          apply Real.log_le_log (by positivity)
          linarith [hcard_le]
      _ ≤ B * s ^ (-(1/2) : ℝ) := hpoint
  -- Integrate the domination: the RHS is an integrable rpow.
  have hII : IntegrableOn (fun s : ℝ => s ^ (-(1/2) : ℝ)) (Set.Ioc (0 : ℝ) 1) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1/2))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] (fun s : ℝ => s ^ (-(1/2) : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Real.rpow_nonneg (le_of_lt hs.1) _
  have hInt_rpow : ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-(1/2) : ℝ)) ∂volume < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnn).mp hII.2
  rw [bracketingEntropyIntegral_eq_setLIntegral]
  apply lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioc hdom)
  have hsplit : (∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (B * s ^ (-(1/2) : ℝ)) ∂volume)
      = ENNReal.ofReal B * ∫⁻ s in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-(1/2) : ℝ)) ∂volume := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    rw [← ENNReal.ofReal_mul hB0]
  rw [hsplit]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hInt_rpow

/-- From a single anchor `ψ θ₀ j ∈ L²(P)` plus the Lipschitz/`L²`-envelope data,
every `ψ θ j` (`θ ∈ Θ`) lies in `L²(P)`: `ψ θ j = ψ θ₀ j + (ψ θ j − ψ θ₀ j)`, and
the difference is dominated by `(diam Θ)·|m| ∈ L²`. Thus a single
square-integrable anchor and the Lipschitz envelope imply square integrability
of the whole class. -/
private lemma memLp_two_psi_of_ref {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ : Bornology.IsBounded Θ)
    (m : Ω → ℝ) (hm : MemLp m 2 P)
    (hψ_meas : ∀ θ ∈ Θ, ∀ j, Measurable (ψ θ j))
    (hLip : ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ (j : Fin k) (x : Ω),
      |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ) (hψ0 : ∀ j, MemLp (ψ θ₀ j) 2 P) :
    ∀ θ ∈ Θ, ∀ j, MemLp (ψ θ j) 2 P := by
  obtain ⟨Δ₀, hΔ₀⟩ := hΘ.subset_closedBall θ₀
  set Δ : ℝ := max Δ₀ 0 with hΔdef
  intro θ hθ j
  have hbnd : ‖θ - θ₀‖ ≤ Δ := by
    rw [← dist_eq_norm]
    exact le_trans (Metric.mem_closedBall.mp (hΔ₀ hθ)) (le_max_left _ _)
  have hdiff : MemLp (fun x => ψ θ j x - ψ θ₀ j x) 2 P := by
    refine MemLp.mono' (hm.norm.const_mul' Δ)
      (((hψ_meas θ hθ j).sub (hψ_meas θ₀ hθ₀ j)).aestronglyMeasurable) ?_
    filter_upwards with x
    calc ‖ψ θ j x - ψ θ₀ j x‖ = |ψ θ j x - ψ θ₀ j x| := Real.norm_eq_abs _
      _ ≤ m x * ‖θ - θ₀‖ := hLip θ hθ θ₀ hθ₀ j x
      _ ≤ ‖m x‖ * ‖θ - θ₀‖ :=
          mul_le_mul_of_nonneg_right (Real.le_norm_self (m x)) (norm_nonneg _)
      _ ≤ ‖m x‖ * Δ := mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
      _ = Δ * ‖m x‖ := mul_comm _ _
  have heq : ψ θ j = fun x => ψ θ₀ j x + (ψ θ j x - ψ θ₀ j x) := by funext x; ring
  rw [heq]
  exact (hψ0 j).add hdiff

/-- **The class is pointwise-dense (VW pointwise-measurable).**

For a countable dense `D ⊆ Θ`, the countable subclass `F' = {ψ θ j : θ ∈ D, j}`
approximates every `ψ θ j` (`θ ∈ Θ`) pointwise: pick `θₘ ∈ D`, `θₘ → θ`, then the
Lipschitz bound `|ψ θₘ j x − ψ θ j x| ≤ m x‖θₘ − θ‖ → 0` gives `ψ θₘ j x → ψ θ j x`
for every `x`. The envelope `Φ = ∑_j |ψ θ₀ j| + (diam Θ)|m|` dominates the class
and is integrable. No separate continuity hypothesis is needed — the Lipschitz
condition supplies it, as required in vdV Example 19.7. -/
theorem parametricClass_empProcPointwiseDense {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ : Bornology.IsBounded Θ)
    (m : Ω → ℝ) (hm : MemLp m 2 P)
    (hLip : ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ (j : Fin k) (x : Ω),
      |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ) (hψ0_L2 : ∀ j, MemLp (ψ θ₀ j) 2 P) :
    EmpProcPointwiseDense (paramClass ψ Θ) P := by
  -- countable dense subset `D ⊆ Θ`.
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense (↥Θ)
  set D : Set (EuclideanSpace ℝ (Fin k)) := Subtype.val '' D₀ with hDdef
  have hD_sub : D ⊆ Θ := by rintro _ ⟨y, _, rfl⟩; exact y.2
  have hD_count : D.Countable := hD₀c.image _
  have hΘ_clD : Θ ⊆ closure D := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥Θ) ∈ closure D₀ := hD₀d ⟨x, hx⟩
    have hxim := image_closure_subset_closure_image continuous_subtype_val
      (Set.mem_image_of_mem Subtype.val hx')
    rw [hDdef]; exact hxim
  refine ⟨paramClass ψ D, ?_, ?_, ?_, ?_⟩
  · -- `F' ⊆ F`.
    rintro g ⟨θ, hθ, j, rfl⟩; exact ⟨θ, hD_sub hθ, j, rfl⟩
  · -- `F'` countable.
    have hsub : paramClass ψ D ⊆
        (fun p : EuclideanSpace ℝ (Fin k) × Fin k => ψ p.1 p.2) '' (D ×ˢ Set.univ) := by
      rintro g ⟨θ, hθ, j, rfl⟩; exact ⟨(θ, j), ⟨hθ, Set.mem_univ _⟩, rfl⟩
    exact Set.Countable.mono hsub ((hD_count.prod Set.countable_univ).image _)
  · -- approximating sequences.
    rintro f ⟨θ, hθ, j, rfl⟩
    obtain ⟨θseq, hθseq_mem, hθseq_lim⟩ := mem_closure_iff_seq_limit.mp (hΘ_clD hθ)
    refine ⟨fun n => ψ (θseq n) j, fun n => ⟨θseq n, hθseq_mem n, j, rfl⟩, fun x => ?_⟩
    have hnorm : Tendsto (fun n => ‖θseq n - θ‖) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => θseq n - θ) atTop (𝓝 0) := by
        simpa using hθseq_lim.sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => θ) atTop (𝓝 θ))
      simpa using! (continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin k))).comp h2
    have ha : Tendsto (fun n => ‖m x‖ * ‖θseq n - θ‖) atTop (𝓝 0) := by
      simpa using hnorm.const_mul ‖m x‖
    have hbd : ∀ n, ‖ψ (θseq n) j x - ψ θ j x‖ ≤ ‖m x‖ * ‖θseq n - θ‖ := by
      intro n
      calc ‖ψ (θseq n) j x - ψ θ j x‖ = |ψ (θseq n) j x - ψ θ j x| := Real.norm_eq_abs _
        _ ≤ m x * ‖θseq n - θ‖ := hLip (θseq n) (hD_sub (hθseq_mem n)) θ hθ j x
        _ ≤ ‖m x‖ * ‖θseq n - θ‖ :=
            mul_le_mul_of_nonneg_right (Real.le_norm_self (m x)) (norm_nonneg _)
    exact tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm hbd ha)
  · -- integrable envelope `Φ = ∑_j |ψ θ₀ j| + (diam Θ)|m|`.
    obtain ⟨Δ₀, hΔ₀⟩ := hΘ.subset_closedBall θ₀
    set Δ : ℝ := max Δ₀ 0 with hΔdef
    have hΔnn : 0 ≤ Δ := le_max_right _ _
    refine ⟨fun x => (∑ j, |ψ θ₀ j x|) + Δ * ‖m x‖, ?_, ?_⟩
    · exact (integrable_finset_sum _
        (fun j _ => ((hψ0_L2 j).integrable (by norm_num)).abs)).add
        ((hm.integrable (by norm_num)).norm.const_mul Δ)
    · rintro g ⟨θ, hθ, j, rfl⟩ x
      have hbnd : ‖θ - θ₀‖ ≤ Δ := by
        rw [← dist_eq_norm]
        exact le_trans (Metric.mem_closedBall.mp (hΔ₀ hθ)) (le_max_left _ _)
      have h1 : |ψ θ j x| ≤ |ψ θ₀ j x| + m x * ‖θ - θ₀‖ := by
        have key : |ψ θ j x| ≤ |ψ θ₀ j x| + |ψ θ j x - ψ θ₀ j x| := by
          have h := abs_add_le (ψ θ₀ j x) (ψ θ j x - ψ θ₀ j x)
          rwa [show ψ θ₀ j x + (ψ θ j x - ψ θ₀ j x) = ψ θ j x from by ring] at h
        linarith [key, hLip θ hθ θ₀ hθ₀ j x]
      have h2 : m x * ‖θ - θ₀‖ ≤ Δ * ‖m x‖ := by
        calc m x * ‖θ - θ₀‖ ≤ ‖m x‖ * ‖θ - θ₀‖ :=
              mul_le_mul_of_nonneg_right (Real.le_norm_self (m x)) (norm_nonneg _)
          _ ≤ ‖m x‖ * Δ := mul_le_mul_of_nonneg_left hbnd (norm_nonneg _)
          _ = Δ * ‖m x‖ := mul_comm _ _
      have h3 : |ψ θ₀ j x| ≤ ∑ j', |ψ θ₀ j' x| :=
        Finset.single_le_sum (f := fun j' => |ψ θ₀ j' x|) (fun i _ => abs_nonneg _)
          (Finset.mem_univ j)
      calc |ψ θ j x| ≤ |ψ θ₀ j x| + m x * ‖θ - θ₀‖ := h1
        _ ≤ (∑ j', |ψ θ₀ j' x|) + Δ * ‖m x‖ := by linarith [h2, h3]

/-- **The Lipschitz-parametrized class is `P`-Donsker.**

Feeding the finite bracketing entropy integral into vdV Theorem 19.5
(`isPDonsker_of_finite_bracketing_entropy_integral`) yields
`IsPDonsker (paramClass ψ Θ) P`. Its asymptotic-equicontinuity conclusion
supplies the condition `h_equicont` in Theorem 19.26.

The anchor data `(θ₀, hθ₀, hψ0_L2)` — one point of `Θ` with its `k` coordinate
functions in `L²(P)` — yields whole-class `L²` membership together with the
Lipschitz/envelope hypotheses. This is vdV Example 19.7. -/
theorem parametricClass_isPDonsker {k : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ : Bornology.IsBounded Θ)
    (m : Ω → ℝ) (hm : MemLp m 2 P) (hm_meas : Measurable m)
    (hLip : ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ (j : Fin k) (x : Ω),
      |ψ θ₁ j x - ψ θ₂ j x| ≤ m x * ‖θ₁ - θ₂‖)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ) (hψ0_L2 : ∀ j, MemLp (ψ θ₀ j) 2 P)
    (hmeas : ∀ g ∈ paramClass ψ Θ, Measurable g) :
    IsPDonsker (paramClass ψ Θ) P := by
  have hψ_meas : ∀ θ ∈ Θ, ∀ j, Measurable (ψ θ j) :=
    fun θ hθ j => hmeas (ψ θ j) ⟨θ, hθ, j, rfl⟩
  have hψ_L2 : ∀ θ ∈ Θ, ∀ j, MemLp (ψ θ j) 2 P :=
    memLp_two_psi_of_ref P ψ Θ hΘ m hm hψ_meas hLip θ₀ hθ₀ hψ0_L2
  exact isPDonsker_of_finite_bracketing_entropy_integral (paramClass ψ Θ) P hmeas
    (parametricClass_bracketingEntropyIntegral_lt_top P ψ Θ hΘ m hm hm_meas hψ_meas hψ_L2 hLip)

end AsymptoticStatistics.EmpiricalProcess
