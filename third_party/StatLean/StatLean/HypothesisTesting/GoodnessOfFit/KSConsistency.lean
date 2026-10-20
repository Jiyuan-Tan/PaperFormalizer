module
public import StatLean.HypothesisTesting.Bootstrap.Defs
public import StatLean.HypothesisTesting.ForMathlib.DKWUniform
public import StatLean.MultipleTesting.ForMathlib.EmpiricalCDF
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Order.Group.Lattice

@[expose] public section

/-!
# The Kolmogorov–Smirnov test: calibration and consistency

For i.i.d. real observations `X₁,…,Xₙ` with c.d.f. `F` and a fully specified null c.d.f.
`F₀`, the Kolmogorov–Smirnov statistic is
$$ T_n \;=\; \sup_{t\in\mathbb R} n^{1/2}\bigl|\hat F_n(t) - F_0(t)\bigr|
        \;=\; n^{1/2}\, d_K(\hat F_n, F_0), $$
where `d_K` is the sup (Kolmogorov) distance between distribution functions. This file
fixes the statistic (`ksStat`), fixes a **calibration** of the critical value, and states
the level and power theorems:

* `ksStat` — the statistic `Tₙ` above, built on the empirical c.d.f.;
* `ksThreshold` — the calibrated critical value (see the calibration note below);
* `ks_dkw_level` — the calibrated test has level `α` at every sample size;
* `ks_consistent` — pointwise consistency against every fixed `F ≠ F₀`;
* `ks_uniform_power` — power `→ 1` uniformly over `n^{1/2} d_K(F, F₀) ≥ εₙ → ∞`;
* `ks_power_lower_bound` — the nonasymptotic power bound behind the previous item.

**Calibration decision (documented deviation).** The classical calibration takes the
critical value to be the `1 − α` quantile `s_{n,1−α}` of the null law of `Tₙ`, whose
asymptotics rest on the Kolmogorov limit law
`P{Tₙ > d} → 2 ∑_{k≥1} (−1)^{k+1} exp(−2k²d²)`. We deliberately avoid that limit law and
calibrate instead through the uniform deviation bound of the sibling brick
`ForMathlib/DKWUniform`. Consequences, all of them documented deviations:

1. `ksThreshold α` does **not** depend on `n`; the level statement is nonasymptotic, and
   the classical step "`s_{n,1−α} → s_{1−α} < ∞`" disappears from every proof below.
2. No continuity assumption on `F₀` is needed anywhere in this file. (The classical
   calibration is distribution-free only for continuous `F₀`; for a discontinuous `F₀` it
   is conservative.)
3. The constants are not sharp. The sharp tail is `2 exp(−2d²)`; the brick delivers
   `4 exp(−d²/16)`, so the calibrated threshold is larger than the classical one and the
   nonasymptotic power bound below carries `4` and `(ε − s)²/16` in place of the classical
   `2` and `2(ε − s)²`. The test remains of level `α` — it is conservative, not wrong.

**Coupling with `ForMathlib/DKWUniform` (single point of contact).** `ksThreshold` is
defined by solving, for `s`, the equation `C e^{−c s²} = α` with the constants `C = 4`,
`c = 1/16` of that brick's `dkw_uniform`:
$$ \mathbb P\bigl\{\, n^{1/2} d_K(\hat F_n, F) \;\ge\; d \,\bigr\}
   \;\le\; 4\, e^{-d^{2}/16}, \qquad d \ge 0, $$
uniformly in `n ≥ 1` and in the sampling law. If those constants are sharpened, the *only*
edit required is the numeral `16 * Real.log (4 / α)` in `ksThreshold`: every statement in
this file and in `KSLocalPower.lean` continues to hold verbatim, because each of them is
phrased through `ksThreshold` and re-derives the level from the same equation.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 16 (Testing Goodness of
Fit), §16.2 (The Kolmogorov–Smirnov Test), Theorem 16.2.1 (pointwise consistency of the
Kolmogorov–Smirnov test) and Theorem 16.2.2 (uniform power when `√n · d_K ≥ εₙ → ∞`). (`TSH4
§16.2 Thm 16.2.1, Thm 16.2.2`.)

**Proof formalization notes.**
* `ksStat` reuses `MultipleTesting.empiricalCDF` (the counting c.d.f. `card {j | Xⱼ ≤ t}/n`)
  and the frozen `supCDFDist` of `Bootstrap/Defs.lean`, so the KS statistic, the bootstrap
  Kolmogorov distance and the multiple-testing empirical c.d.f. are the same objects.
* The sibling brick states its bound through its own `empCDF` / `ksDist`. The two
  presentations are reconciled once and for all by `empiricalCDF_eq_empCDF` and
  `ksStat_eq_sqrt_mul_ksDist`, which every proof below routes through; no statement in
  this file mentions `ksDist`.
* The rejection event involves an uncountable supremum. Rather than assuming its
  measurability at every use site, it is derived once in `measurable_ksStat` from right
  continuity of `F₀` (the empirical c.d.f. is right continuous by construction), i.e. the
  real supremum is a rational supremum.
* Null and alternative c.d.f.s are identified with Mathlib's `cdf` of the corresponding
  law by a single hypothesis `∀ t, F t = cdf μ t`; this supplies right continuity,
  monotonicity and the identification simultaneously.
* `ks_uniform_power` is stated in **sequence form**: the classical statement is an
  infimum of powers over the class `{F : n^{1/2} d_K(F, F₀) ≥ εₙ}`, and the two are
  equivalent (an infimum of a bounded family tends to `1` iff the value along every
  admissible selection does). The sequence form is also the form the classical proof
  argues in, and it is the form that types: each alternative carries its own sampling law,
  i.e. a triangular array `X : (n : ℕ) → Fin n → Ω → ℝ`.

**Bibliographic comments.** The statistic and its limit law are due to A. N. Kolmogorov
("Sulla determinazione empirica di una legge di distribuzione," *Giornale dell'Istituto
Italiano degli Attuari* **4** (1933), 83–91); the two-sample and further distribution
theory to N. V. Smirnov ("Table for estimating the goodness of fit of empirical
distributions," *Ann. Math. Statist.* **19** (1948), 279–281). The uniform deviation
inequality used for the calibration is due to A. Dvoretzky, J. Kiefer and J. Wolfowitz
("Asymptotic minimax character of the sample distribution function and of the classical
multinomial estimator," *Ann. Math. Statist.* **27** (1956), 642–669), with the sharp
constant obtained by P. Massart ("The tight constant in the Dvoretzky–Kiefer–Wolfowitz
inequality," *Ann. Probab.* **18** (1990), 1269–1283). The second, elementary consistency
argument transcribed in `ks_consistent` goes back to F. J. Massey ("A note on the power of
a non-parametric test," *Ann. Math. Statist.* **21** (1950), 440–443).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.MultipleTesting (empiricalCDF)

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The statistic and its calibration -/

/-- The **two-sided Kolmogorov–Smirnov statistic**
`Tₙ = sup_t n^{1/2} |F̂ₙ(t) − F₀(t)| = n^{1/2} d_K(F̂ₙ, F₀)` of a sample `X` against the
fully specified null c.d.f. `F₀`. Built on `MultipleTesting.empiricalCDF` (the empirical
c.d.f. `F̂ₙ`) and on `supCDFDist` (the Kolmogorov distance `d_K`). For `n = 0` the
empirical c.d.f. is identically `0` and the statistic is `0` (junk, guarded by `0 < n`
side conditions everywhere below). -/
noncomputable def ksStat {n : ℕ} (X : Fin n → Ω → ℝ) (F₀ : ℝ → ℝ) (ω : Ω) : ℝ :=
  Real.sqrt (n : ℝ) * supCDFDist (fun t => empiricalCDF X t ω) F₀

/-- The **DKW-calibrated critical value** of the Kolmogorov–Smirnov test at level `α`:
the solution `s` of `4 · exp(−s²/16) = α`, i.e.
$$ s_\alpha \;=\; \sqrt{16\,\log(4/\alpha)} . $$
It is a constant: it does not depend on the sample size, on the null c.d.f., or on the
sampling law. Degenerate inputs (`α ≤ 0`) fall back on the junk conventions of `Real.log`
and `Real.sqrt`; every statement below carries `0 < α < 1`.

COUPLING: the numerals `4` and `16` are the constants `C` and `1/c` of `dkw_uniform` in
`ForMathlib/DKWUniform`; see the module docstring for the reconciliation rule.

DOCUMENTED DEVIATION (constant, not statement). This definition previously read
`√(8 log(4/α))`, matching the frozen `dkw_uniform` exponent `c = 1/8`. That exponent was
*not* provable: the only elementary route to the in-expectation half of the DKW inequality
(symmetrisation, the sorted-prefix `±1` walk, and Lévy's maximal inequality) delivers
`√n · E Dₙ ≤ 4`, and `M = 4` provably breaks `4 e^{−d²/8}` on the band `d ∈ (3.330, 4)`.
Per the charter rule *state the constants that are actually provable*, `dkw_uniform` was
amended to `4 e^{−d²/16}` and this numeral to `16`; see the `ForMathlib/DKWUniform` header
for the full accounting and for the martingale route that would restore `8`. The effect is
that every calibrated threshold in this file is `√2` times larger, i.e. the tests are more
conservative; every statement below is phrased through `ksThreshold` and re-derives its
level from `4 e^{−s²/16} = α`, so all of them hold verbatim. -/
noncomputable def ksThreshold (α : ℝ) : ℝ :=
  Real.sqrt (16 * Real.log (4 / α))

/-! ### Reconciliation with the deviation brick -/

/-- The empirical c.d.f. of the multiple-testing library and the one of the deviation
brick agree: counting the sample points below a threshold is the same as summing their
indicators. -/
theorem empiricalCDF_eq_empCDF {n : ℕ} (X : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) :
    empiricalCDF X t ω = empCDF X ω t := by
  unfold empiricalCDF empCDF StatLean.MultipleTesting.countLE
  rw [Finset.sum_boole, div_eq_mul_inv, mul_comm]

/-- The Kolmogorov–Smirnov statistic against the c.d.f. of a law `μ` is `n^{1/2}` times the
Kolmogorov distance of `ForMathlib/DKWUniform`. This is the single bridge through which
every proof in this file and in `KSLocalPower.lean` reaches the deviation inequality. -/
theorem ksStat_eq_sqrt_mul_ksDist {n : ℕ} (X : Fin n → Ω → ℝ) (μ : Measure ℝ) (ω : Ω) :
    ksStat X (fun t => cdf μ t) ω = Real.sqrt (n : ℝ) * ksDist X μ ω := by
  simp only [ksStat, supCDFDist, ksDist, empiricalCDF_eq_empCDF]

/-- The step indicator `t ↦ 1{a ≤ t}` is right continuous: it is eventually constant on
every right neighbourhood. -/
private lemma rightCont_stepIndicator (a s : ℝ) :
    Tendsto (fun t => if a ≤ t then (1 : ℝ) else 0)
      (nhdsWithin s (Set.Ioi s)) (nhds (if a ≤ s then (1 : ℝ) else 0)) := by
  have hl : (fun _ : ℝ => if a ≤ s then (1 : ℝ) else 0)
      =ᶠ[nhdsWithin s (Set.Ioi s)] (fun t => if a ≤ t then (1 : ℝ) else 0) := by
    by_cases h : a ≤ s
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [if_pos h, if_pos (h.trans ht.le)]
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (not_le.mp h))] with t ht
      rw [if_neg h, if_neg (not_le.mpr ht)]
  exact Tendsto.congr' hl tendsto_const_nhds

/-- The empirical c.d.f. is right continuous in the threshold (it is a finite average of the
right-continuous step indicators of the sample points). -/
private lemma rightCont_empiricalCDF {n : ℕ} (X : Fin n → Ω → ℝ) (ω : Ω) (s : ℝ) :
    Tendsto (fun t => empiricalCDF X t ω) (nhdsWithin s (Set.Ioi s))
      (nhds (empiricalCDF X s ω)) := by
  have heq : ∀ t, empiricalCDF X t ω
      = (n : ℝ)⁻¹ * ∑ i, if X i ω ≤ t then (1 : ℝ) else 0 := by
    intro t; rw [empiricalCDF_eq_empCDF]; rfl
  simp_rw [heq]
  exact (tendsto_finset_sum Finset.univ
    (fun i _ => rightCont_stepIndicator (X i ω) s)).const_mul _

/-- A real supremum of a right-continuous function over `ℝ` agrees with the supremum over
the rationals: the rationals are dense from the right, so every value is approximated. -/
private lemma iSup_real_eq_iSup_rat (g : ℝ → ℝ)
    (hrc : ∀ s, Tendsto g (nhdsWithin s (Set.Ioi s)) (nhds (g s))) :
    ⨆ t : ℝ, g t = ⨆ q : ℚ, g (q : ℝ) := by
  by_cases hbdd : BddAbove (Set.range fun q : ℚ => g (q : ℝ))
  · -- The rational supremum is finite; right continuity makes it an upper bound on all of `ℝ`.
    have hle : ∀ t : ℝ, g t ≤ ⨆ q : ℚ, g (q : ℝ) := by
      intro t
      obtain ⟨u, hu_gt, hu_lt⟩ : ∃ u : ℕ → ℚ,
          (∀ k, t < (u k : ℝ)) ∧ (∀ k, (u k : ℝ) < t + 1 / ((k : ℝ) + 1)) := by
        choose u hu using fun k : ℕ =>
          exists_rat_btwn (show t < t + 1 / ((k : ℝ) + 1) from
            lt_add_of_pos_right t (by positivity))
        exact ⟨u, fun k => (hu k).1, fun k => (hu k).2⟩
      have hupper : Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) atTop (nhds t) := by
        have := (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      have hnhds : Tendsto (fun k => (u k : ℝ)) atTop (nhds t) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
          (Eventually.of_forall fun k => (hu_gt k).le)
          (Eventually.of_forall fun k => (hu_lt k).le)
      have htend : Tendsto (fun k => (u k : ℝ)) atTop (nhdsWithin t (Set.Ioi t)) :=
        tendsto_nhdsWithin_iff.mpr ⟨hnhds, Eventually.of_forall fun k => hu_gt k⟩
      exact le_of_tendsto ((hrc t).comp htend)
        (Eventually.of_forall fun k => le_ciSup hbdd (u k))
    have hbddR : BddAbove (Set.range g) :=
      ⟨⨆ q : ℚ, g (q : ℝ), by rintro _ ⟨t, rfl⟩; exact hle t⟩
    exact le_antisymm (ciSup_le hle) (ciSup_le fun q => le_ciSup hbddR (q : ℝ))
  · -- The rational supremum is unbounded, hence so is the real one; both are junk (`sSup ∅`).
    have hbddR : ¬ BddAbove (Set.range g) := by
      intro hR
      obtain ⟨M, hM⟩ := hR
      exact hbdd ⟨M, by rintro _ ⟨q, rfl⟩; exact hM ⟨(q : ℝ), rfl⟩⟩
    rw [ciSup_of_not_bddAbove hbddR, ciSup_of_not_bddAbove hbdd]

/-- Measurability of the Kolmogorov–Smirnov statistic. The supremum defining `d_K` ranges
over all of `ℝ`, but both competing functions are right continuous — the empirical c.d.f.
by construction, `F₀` by hypothesis — so the supremum is attained along the rationals and
the statistic is a countable supremum of measurable functions. -/
theorem measurable_ksStat {n : ℕ} (X : Fin n → Ω → ℝ) (F₀ : ℝ → ℝ)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: `F₀` is a c.d.f., in particular right continuous; Kolmogorov 1933
    (hF₀ : ∀ t : ℝ, Tendsto F₀ (nhdsWithin t (Set.Ioi t)) (nhds (F₀ t))) :
    Measurable (ksStat X F₀) := by
  -- measurability of `ω ↦ empiricalCDF X q ω` at a fixed threshold
  have hmeasEmp : ∀ t : ℝ, Measurable fun ω => empiricalCDF X t ω := by
    intro t
    simp_rw [empiricalCDF_eq_empCDF]
    unfold empCDF
    exact (Finset.univ.measurable_sum fun i _ =>
      Measurable.ite (measurableSet_le (hX i) measurable_const)
        measurable_const measurable_const).const_mul _
  -- reduce the real supremum to a countable (rational) one, pointwise in `ω`
  have hpt : ksStat X F₀
      = fun ω => Real.sqrt (n : ℝ) * ⨆ q : ℚ, |empiricalCDF X (q : ℝ) ω - F₀ (q : ℝ)| := by
    funext ω
    simp only [ksStat, supCDFDist]
    congr 1
    exact iSup_real_eq_iSup_rat (fun t => |empiricalCDF X t ω - F₀ t|)
      (fun s => Tendsto.abs ((rightCont_empiricalCDF X ω s).sub (hF₀ s)))
  rw [hpt]
  exact Measurable.const_mul
    (Measurable.iSup fun q : ℚ => Measurable.abs ((hmeasEmp (q : ℝ)).sub measurable_const)) _

/-! ### Level: the DKW calibration is exact -/

/-- The DKW envelope evaluated at the calibrated threshold equals the nominal level:
`4·exp(−(ksThreshold α)²/16) = α`. This is the defining equation of `ksThreshold`. -/
lemma dkw_envelope_threshold {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    4 * Real.exp (-(ksThreshold α) ^ 2 / 16) = α := by
  have h4a : 1 ≤ 4 / α := by rw [le_div_iff₀ hα]; linarith
  have hlog : 0 ≤ Real.log (4 / α) := Real.log_nonneg h4a
  have hsq : (ksThreshold α) ^ 2 = 16 * Real.log (4 / α) := by
    unfold ksThreshold
    exact Real.sq_sqrt (mul_nonneg (by norm_num) hlog)
  rw [hsq, show -(16 * Real.log (4 / α)) / 16 = -Real.log (4 / α) by ring,
    Real.exp_neg, Real.exp_log (by positivity), inv_div]
  field_simp

/-- **Level of the calibrated test.** Under the null hypothesis the test that rejects when
`Tₙ > ksThreshold α` has level `α` — nonasymptotically, at every sample size `n ≥ 1`, and
for an arbitrary (not necessarily continuous) null law.

This is the defining property of the calibration: `ksThreshold α` is exactly the point
where the uniform deviation envelope `4 · exp(−d²/16)` of `ForMathlib/DKWUniform` equals
`α`. -/
theorem ks_dkw_level {n : ℕ} {α : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → ℝ} {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F₀ : ℝ → ℝ}
    -- USER-INPUT: nondegenerate sample size; the statistic is junk at `n = 0`
    (hn : 0 < n)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are i.i.d.; Kolmogorov 1933
    (hindep : iIndepFun X P)
    -- USER-INPUT: the null hypothesis: every observation has the null law `μ₀`
    (hlaw : ∀ i, P.map (X i) = μ₀)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t) :
    P {ω | ksThreshold α < ksStat X F₀ ω} ≤ ENNReal.ofReal α := by
  have hF : F₀ = fun t => cdf μ₀ t := funext hF₀
  have hthr : 0 ≤ ksThreshold α := Real.sqrt_nonneg _
  calc P {ω | ksThreshold α < ksStat X F₀ ω}
      ≤ P {ω | ksThreshold α ≤ Real.sqrt (n : ℝ) * ksDist X μ₀ ω} := by
        apply measure_mono
        intro ω hω
        rw [Set.mem_setOf_eq, hF, ksStat_eq_sqrt_mul_ksDist] at hω
        exact le_of_lt hω
    _ ≤ ENNReal.ofReal (4 * Real.exp (-(ksThreshold α) ^ 2 / 16)) :=
        dkw_uniform hn μ₀ X hX hindep hlaw hthr
    _ = ENNReal.ofReal α := by rw [dkw_envelope_threshold hα hα1]

/-! ### Kolmogorov-distance geometry (triangle inequality) -/

/-- The sup (Kolmogorov) distance is symmetric. -/
lemma supCDFDist_comm (F G : ℝ → ℝ) : supCDFDist F G = supCDFDist G F := by
  unfold supCDFDist
  exact iSup_congr fun t => abs_sub_comm _ _

/-- The absolute difference of two `[0,1]`-valued functions is bounded (by `1`). -/
lemma bddAbove_absCDFDiff {F G : ℝ → ℝ} (hF : ∀ t, F t ∈ Set.Icc (0 : ℝ) 1)
    (hG : ∀ t, G t ∈ Set.Icc (0 : ℝ) 1) :
    BddAbove (Set.range fun t => |F t - G t|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  have h1 := hF t; have h2 := hG t
  simp only [Set.mem_Icc] at h1 h2
  rw [abs_le]; constructor <;> linarith

/-- Triangle inequality for the sup distance (given boundedness of the two sups). -/
lemma supCDFDist_triangle {F G H : ℝ → ℝ}
    (hFG : BddAbove (Set.range fun t => |F t - G t|))
    (hGH : BddAbove (Set.range fun t => |G t - H t|)) :
    supCDFDist F H ≤ supCDFDist F G + supCDFDist G H := by
  unfold supCDFDist
  refine ciSup_le fun t => ?_
  calc |F t - H t| ≤ |F t - G t| + |G t - H t| := abs_sub_le _ _ _
    _ ≤ (⨆ t, |F t - G t|) + (⨆ t, |G t - H t|) :=
        add_le_add (le_ciSup hFG t) (le_ciSup hGH t)

/-! ### Uniform consistency over shrinking alternatives -/

/-- **Nonasymptotic power bound.** If the sampling law is at Kolmogorov distance at least
`ε / n^{1/2}` from the null, then the calibrated test rejects with probability at least
`1 − 4 exp(−(ε − s)²/16)`, where `s = ksThreshold α`.

This is the calibrated form of the classical nonasymptotic bound
`P{Tₙ > s} ≥ 1 − 2 exp(−2(ε − s)²)`, with the same hypothesis `s < ε` and the constants of
the sibling brick in place of the sharp ones (documented deviation; see the module
docstring). Both come from the same two lines: the triangle inequality
`d_K(F, F₀) ≤ d_K(F, F̂ₙ) + d_K(F̂ₙ, F₀)` turns the event `n^{1/2} d_K(F̂ₙ, F) < ε − s`
into a rejection, and the deviation inequality bounds its complement. -/
theorem ks_power_lower_bound {n : ℕ} {α ε : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F F₀ : ℝ → ℝ}
    -- USER-INPUT: nondegenerate sample size; the statistic is junk at `n = 0`
    (hn : 0 < n)
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are i.i.d.; Dvoretzky–Kiefer–Wolfowitz 1956
    (hindep : iIndepFun X P)
    -- USER-INPUT: the alternative: every observation has law `μ`
    (hlaw : ∀ i, P.map (X i) = μ)
    -- USER-INPUT: `F` is the c.d.f. of the sampling law
    (hF : ∀ t : ℝ, F t = cdf μ t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the alternative is at distance `≥ ε/√n` from the null
    (hfar : ε ≤ Real.sqrt (n : ℝ) * supCDFDist F F₀)
    -- USER-INPUT: the separation exceeds the critical value (classical `εₙ > s_{n,1−α}`)
    (hgap : ksThreshold α < ε) :
    ENNReal.ofReal (1 - 4 * Real.exp (-((ε - ksThreshold α) ^ 2) / 16))
      ≤ P {ω | ksThreshold α < ksStat X F₀ ω} := by
  set s := ksThreshold α with hs
  have hsnn : 0 ≤ s := Real.sqrt_nonneg _
  have hd : 0 ≤ ε - s := by linarith
  -- `[0,1]`-valued CDFs and empirical CDF
  have hFIcc : ∀ t, F t ∈ Set.Icc (0 : ℝ) 1 := fun t => by
    rw [hF t]; exact ⟨cdf_nonneg μ t, cdf_le_one μ t⟩
  have hF₀Icc : ∀ t, F₀ t ∈ Set.Icc (0 : ℝ) 1 := fun t => by
    rw [hF₀ t]; exact ⟨cdf_nonneg μ₀ t, cdf_le_one μ₀ t⟩
  have hEIcc : ∀ ω, ∀ t, empCDF X ω t ∈ Set.Icc (0 : ℝ) 1 := fun ω t => by
    rw [← empiricalCDF_eq_empCDF]
    exact ⟨StatLean.MultipleTesting.empiricalCDF_nonneg X t ω,
      StatLean.MultipleTesting.empiricalCDF_le_one X t ω⟩
  -- the good event `{√n d_K(F̂ₙ, F) < ε − s}` forces rejection
  have hsubset : {ω | Real.sqrt (n : ℝ) * ksDist X μ ω < ε - s}
      ⊆ {ω | s < ksStat X F₀ ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hEval := hEIcc ω
    -- triangle: d_K(F, F₀) ≤ d_K(F, F̂ₙ) + d_K(F̂ₙ, F₀)
    have htri : supCDFDist F F₀
        ≤ supCDFDist F (fun t => empCDF X ω t) + supCDFDist (fun t => empCDF X ω t) F₀ :=
      supCDFDist_triangle (bddAbove_absCDFDiff hFIcc hEval) (bddAbove_absCDFDiff hEval hF₀Icc)
    -- identify the two summands with `ksDist` and `ksStat / √n`
    have hks : ksStat X F₀ ω = Real.sqrt (n : ℝ) * supCDFDist (fun t => empCDF X ω t) F₀ := by
      simp only [ksStat, supCDFDist, empiricalCDF_eq_empCDF]
    have hdist : ksDist X μ ω = supCDFDist F (fun t => empCDF X ω t) := by
      rw [supCDFDist_comm]
      unfold ksDist supCDFDist
      exact iSup_congr fun t => by rw [hF t]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
    have hchain : ε ≤ Real.sqrt (n : ℝ) * ksDist X μ ω + ksStat X F₀ ω := by
      calc ε ≤ Real.sqrt (n : ℝ) * supCDFDist F F₀ := hfar
        _ ≤ Real.sqrt (n : ℝ) * (supCDFDist F (fun t => empCDF X ω t)
              + supCDFDist (fun t => empCDF X ω t) F₀) := by
            exact mul_le_mul_of_nonneg_left htri hsqrt_nonneg
        _ = Real.sqrt (n : ℝ) * ksDist X μ ω + ksStat X F₀ ω := by
            rw [hks, hdist, mul_add]
    linarith
  -- combine with the deviation inequality via subadditivity
  set A := {ω | ε - s ≤ Real.sqrt (n : ℝ) * ksDist X μ ω} with hA
  have hdkw : P A ≤ ENNReal.ofReal (4 * Real.exp (-((ε - s) ^ 2) / 16)) :=
    dkw_uniform hn μ X hX hindep hlaw hd
  have hAc : {ω | Real.sqrt (n : ℝ) * ksDist X μ ω < ε - s} = Aᶜ := by
    rw [hA]; ext ω; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hsub : P Aᶜ ≤ P {ω | s < ksStat X F₀ ω} := by
    rw [← hAc]; exact measure_mono hsubset
  have hunion : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    have := measure_union_le (μ := P) A Aᶜ
    simpa [Set.union_compl_self, measure_univ] using this
  calc ENNReal.ofReal (1 - 4 * Real.exp (-((ε - s) ^ 2) / 16))
      = 1 - ENNReal.ofReal (4 * Real.exp (-((ε - s) ^ 2) / 16)) := by
        rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
    _ ≤ 1 - P A := by
        apply tsub_le_tsub_left hdkw
    _ ≤ P Aᶜ := by
        rw [tsub_le_iff_right, add_comm]; exact hunion
    _ ≤ P {ω | s < ksStat X F₀ ω} := hsub

/-- **Uniform consistency in power.** The power of the calibrated Kolmogorov–Smirnov test
tends to one uniformly over the alternatives `F` with `n^{1/2} d_K(F, F₀) ≥ εₙ`, whenever
`εₙ → ∞`.

Stated in sequence form (see the module docstring): the classical infimum over the class
of admissible alternatives at stage `n` is replaced by an arbitrary selection `μ n` of
sampling laws satisfying the constraint, carried by a triangular array `X n` of
observations. Specialising to a constant selection recovers uniform consistency over
`d_K(F, F₀) ≥ ϵ` for each fixed `ϵ > 0`. -/
theorem ks_uniform_power {α : ℝ} {P : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (P n)]
    {X : (n : ℕ) → Fin n → Ω → ℝ} {μ : ℕ → Measure ℝ} [∀ n, IsProbabilityMeasure (μ n)]
    {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀] {F : ℕ → ℝ → ℝ} {F₀ : ℝ → ℝ} {ε : ℕ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: at every stage each observation is measurable
    (hX : ∀ n, ∀ i, Measurable (X n i))
    -- USER-INPUT: at every stage the observations are i.i.d.; Kolmogorov 1933
    (hindep : ∀ n, iIndepFun (X n) (P n))
    -- USER-INPUT: at stage `n` every observation has law `μ n`
    (hlaw : ∀ n, ∀ i, (P n).map (X n i) = μ n)
    -- USER-INPUT: `F n` is the c.d.f. of the stage-`n` sampling law
    (hF : ∀ n, ∀ t : ℝ, F n t = cdf (μ n) t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the stage-`n` alternative satisfies `n^{1/2} d_K(Fₙ, F₀) ≥ εₙ`
    (hfar : ∀ n, ε n ≤ Real.sqrt (n : ℝ) * supCDFDist (F n) F₀)
    -- USER-INPUT: the separation diverges: `εₙ → ∞`
    (hε : Tendsto ε atTop atTop) :
    Tendsto (fun n => ((P n) {ω | ksThreshold α < ksStat (X n) F₀ ω}).toReal)
      atTop (nhds 1) := by
  set s := ksThreshold α with hs
  have hεs : Tendsto (fun n => ε n - s) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-s) hε
  have hexp0 : Tendsto (fun n => 4 * Real.exp (-((ε n - s) ^ 2) / 16)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n => (ε n - s) ^ 2 / 16) atTop atTop :=
      ((tendsto_pow_atTop two_ne_zero).comp hεs).atTop_div_const (by norm_num)
    have h2 : Tendsto (fun n => Real.exp (-((ε n - s) ^ 2 / 16))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := h2.const_mul 4
    simpa [neg_div] using h3
  have hLlim : Tendsto (fun n => 1 - 4 * Real.exp (-((ε n - s) ^ 2) / 16)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hexp0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n => 1 - 4 * Real.exp (-((ε n - s) ^ 2) / 16)) (h := fun _ => (1 : ℝ))
    hLlim tendsto_const_nhds ?_ ?_
  · filter_upwards [hε.eventually_gt_atTop s, eventually_ge_atTop 1] with n hgap hn1
    have hn : 0 < n := hn1
    have hlb := ks_power_lower_bound hn hα hα1 (hX n) (hindep n) (hlaw n) (hF n) hF₀
      (hfar n) hgap
    have hle : 1 - 4 * Real.exp (-((ε n - s) ^ 2) / 16)
        ≤ (ENNReal.ofReal (1 - 4 * Real.exp (-((ε n - s) ^ 2) / 16))).toReal := by
      by_cases h : 0 ≤ 1 - 4 * Real.exp (-((ε n - s) ^ 2) / 16)
      · rw [ENNReal.toReal_ofReal h]
      · exact le_trans (not_le.mp h).le ENNReal.toReal_nonneg
    exact hle.trans (ENNReal.toReal_mono (measure_ne_top _ _) hlb)
  · filter_upwards with n
    have h1 : (P n) {ω | s < ksStat (X n) F₀ ω} ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top h1

/-! ### Pointwise consistency against a fixed alternative -/

/-- **Pointwise consistency of the Kolmogorov–Smirnov test.** Against any fixed
alternative `F ≠ F₀` — equivalently, any `F` at positive Kolmogorov distance from `F₀` —
the power of the calibrated test tends to one.

The classical proof runs the Glivenko–Cantelli theorem (`d_K(F̂ₙ, F) → 0` a.s., hence
`Tₙ → ∞` a.s.) together with `s_{n,1−α} → s_{1−α} < ∞`; under the calibration of this file
the second ingredient is vacuous, since the critical value is a constant. Here the fixed
alternative is the constant selection of `ks_uniform_power` (`μ n = μ`, `F n = F`), whose
diverging separation `εₙ = √n · d_K(F, F₀) → ∞` is supplied by `d_K(F, F₀) > 0`. -/
theorem ks_consistent {α : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {μ₀ : Measure ℝ} [IsProbabilityMeasure μ₀]
    {F F₀ : ℝ → ℝ}
    -- USER-INPUT: the nominal level is a nondegenerate probability
    (hα : 0 < α) (hα1 : α < 1)
    -- USER-INPUT: each observation is measurable; part of the sampling model
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: the observations are i.i.d.; Kolmogorov 1933
    (hindep : iIndepFun X P)
    -- USER-INPUT: the alternative: every observation has law `μ`
    (hlaw : ∀ i, P.map (X i) = μ)
    -- USER-INPUT: `F` is the c.d.f. of the sampling law
    (hF : ∀ t : ℝ, F t = cdf μ t)
    -- USER-INPUT: `F₀` is the c.d.f. of the null law
    (hF₀ : ∀ t : ℝ, F₀ t = cdf μ₀ t)
    -- USER-INPUT: the alternative is genuinely different from the null: `d_K(F, F₀) > 0`
    (hne : 0 < supCDFDist F F₀) :
    Tendsto
      (fun n => (P {ω | ksThreshold α < ksStat (fun i : Fin n => X (i : ℕ)) F₀ ω}).toReal)
      atTop (nhds 1) := by
  -- A fixed alternative is the constant selection `μ n = μ`, `F n = F`, with the diverging
  -- separation `εₙ = √n · d_K(F, F₀)`; the result is exactly `ks_uniform_power`.
  haveI hPinst : ∀ n : ℕ, IsProbabilityMeasure ((fun _ : ℕ => P) n) := fun _ => inferInstance
  haveI hμinst : ∀ n : ℕ, IsProbabilityMeasure ((fun _ : ℕ => μ) n) := fun _ => inferInstance
  -- the separation `εₙ = √n · d_K(F, F₀)` diverges since `d_K(F, F₀) > 0`
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hε : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * supCDFDist F F₀) atTop atTop :=
    hsqrt.atTop_mul_const' hne
  exact ks_uniform_power (P := fun _ => P) (X := fun n i => X (i : ℕ)) (μ := fun _ => μ)
    (F := fun _ => F) (ε := fun n => Real.sqrt (n : ℝ) * supCDFDist F F₀)
    hα hα1 (fun n i => hX (i : ℕ)) (fun n => hindep.precomp Fin.val_injective)
    (fun n i => hlaw (i : ℕ)) (fun n t => hF t) hF₀ (fun n => le_refl _) hε

end StatLean.HypothesisTesting
