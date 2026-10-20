module
public import StatLean.HypothesisTesting.Bootstrap.Defs
public import StatLean.HypothesisTesting.ForMathlib.PolyaUniformCDF
public import StatLean.HypothesisTesting.ForMathlib.QuantileFunction
public import StatLean.HypothesisTesting.ForMathlib.LindebergCLT
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-!
# Bootstrap consistency: the sequence-class criterion

The bootstrap replaces the unknown law `P` by an estimate `Phat n` (typically the empirical
measure of the sample) inside the sampling distribution `J n` of a root. Consistency asks
that this substitution be asymptotically harmless. Following the sequence-class approach,
smoothness of `J` in its measure argument is expressed by a set of sequences `C_P` of laws:
along **every** sequence in `C_P` the sampling distribution functions converge to one and the
same continuous limit `Jlim`. The only stochastic ingredient is then that the estimated
sequence `n ↦ Phat n ω` belongs to `C_P` for almost every `ω`.

This file contains:

* `IsCDF` — the distribution-function predicate every `J n Q` is assumed to satisfy;
* `StrictIncAt` — strict increase of a distribution function at a point;
* `normalCDF`, `stdNormalCDF`, `stdNormalQuantile` — the Gaussian limit-law vocabulary used
  throughout the bootstrap cluster;
* `tendsto_supCDFDist_bootstrap` — almost sure uniform closeness of the bootstrap sampling
  distribution to the true one;
* `tendsto_bootstrapQuantile` — almost sure convergence of the bootstrap quantile;
* `tendsto_bootstrapCoverage` — asymptotic coverage of the bootstrap confidence set;
* `tendstoInMeasure_rowMean_triangular` — the triangular-array weak law used by the
  nonparametric-mean applications downstream.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.3 (Bootstrap Sampling Distributions), Theorem 18.3.1 (§18.3.1,
Introduction and Consistency): general bootstrap consistency via the sequence-class criterion,
with Theorem 18.3.2 (the uniform version and quantile consistency). (`TSH4 §18.3 Thm 18.3.1,
Thm 18.3.2`.)

**Designed deviation (metric-free formulation).** The reference tradition often describes
smoothness of `J` in `P` through a metric `d` on the space of laws (`d(P_n, P) → 0` implies
`J_n(P_n) ⇒ J(P)`). We deliberately keep the **sequence-class** form: `C_P` is an abstract set
of sequences, supplied as data together with its defining convergence property. This is the
weaker and more general of the two devices (any metric criterion produces such a class), it
avoids committing the library to one metric on measures, and it removes every measurability
requirement in the measure argument of `J`.

**Proof formalization notes.**
* The sampling-CDF field `J : ℕ → Measure 𝓧 → ℝ → ℝ` is theorem-level data. Its distribution
  function properties enter as the hypothesis `∀ n Q, IsCDF (J n Q)`; no measurability of
  `Q ↦ J n Q x` is ever assumed, which is what makes the almost-sure statements meaningful
  for a random `Phat n ω`.
* The uniform conclusion is the Polya step: pointwise convergence of distribution functions to
  a **continuous** limit upgrades to convergence in sup-distance. That upgrade is the sibling
  `PolyaUniformCDF` brick of this area (uniform convergence of monotone functions to a
  continuous limit); it is applied here to each fixed sequence in `C_P` and then transported
  to the random sequence on the almost sure event.
* The confidence set is the one attached to the root: `θ(P)` is covered exactly when the root
  evaluated at the true parameter does not exceed the estimated `1 − α` quantile. The coverage
  statement is phrased directly in that form, so no separate parameter-set machinery is needed.
* `IsCDF` deliberately omits `[0,1]`-valuedness: monotonicity together with the two tail limits
  forces it, so recording it as a field would be redundant.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods: another look
at the jackknife," *Ann. Statist.* **7** (1979), 1–26). Its first consistency theory is due to
P. J. Bickel and D. A. Freedman ("Some asymptotic theory for the bootstrap," *Ann. Statist.*
**9** (1981), 1196–1217) and K. Singh ("On the asymptotic accuracy of Efron's bootstrap,"
*Ann. Statist.* **9** (1981), 1187–1195). The formulation of consistency through classes of
converging sequences of laws follows R. Beran ("Bootstrap methods in statistics," *Jahresber.
Deutsch. Math.-Verein.* **86** (1984), 14–30) and D. N. Politis, J. P. Romano and M. Wolf,
*Subsampling*, Springer, 1999.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StatLean.HypothesisTesting

variable {𝓧 Ω : Type*} [MeasurableSpace 𝓧] [MeasurableSpace Ω]

/-! ## Distribution-function vocabulary -/

/-- A real function is a **distribution function**: nondecreasing, right-continuous, with
limit `0` at `−∞` and limit `1` at `+∞`. (`[0,1]`-valuedness is a consequence, not a field.) -/
structure IsCDF (F : ℝ → ℝ) : Prop where
  /-- Constitutive: a distribution function is nondecreasing. -/
  mono : Monotone F
  /-- Constitutive: a distribution function is right-continuous. -/
  right_continuous : ∀ x : ℝ, ContinuousWithinAt F (Set.Ici x) x
  /-- Constitutive: a distribution function vanishes at `−∞`. -/
  tendsto_atBot : Tendsto F atBot (𝓝 0)
  /-- Constitutive: a distribution function tends to `1` at `+∞`. -/
  tendsto_atTop : Tendsto F atTop (𝓝 1)

/-- `F` is **strictly increasing at** `x₀`: strictly smaller to the left, strictly larger to
the right. This is the exact regularity that makes the `x₀`-level quantile unique, and it is
what quantile convergence needs on top of continuity of the limit law. -/
def StrictIncAt (F : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  (∀ y, y < x₀ → F y < F x₀) ∧ (∀ z, x₀ < z → F x₀ < F z)

/-- The **normal distribution function** with mean `m` and variance `v`. -/
noncomputable def normalCDF (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (gaussianReal m v (Set.Iic x)).toReal

/-- The **standard normal distribution function** `Φ`. -/
noncomputable def stdNormalCDF (x : ℝ) : ℝ := normalCDF 0 1 x

/-- The **standard normal quantile** `z_p = Φ⁻¹(p)`, via the generalized inverse. -/
noncomputable def stdNormalQuantile (p : ℝ) : ℝ := cdfPseudoInverse stdNormalCDF p

/-! ## Distribution-function and continuity infrastructure -/

/-- The `toReal` of the `Iic`-measure of a probability law on the line is a distribution
function: this is exactly `ProbabilityTheory.cdf`, dressed as `IsCDF`. -/
lemma isCDF_toReal_measure_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsCDF (fun x => (ν (Set.Iic x)).toReal) := by
  have heq : (fun x => (ν (Set.Iic x)).toReal) = fun x => (ProbabilityTheory.cdf ν) x := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  rw [heq]
  exact
    { mono := (ProbabilityTheory.cdf ν).mono
      right_continuous := fun x => (ProbabilityTheory.cdf ν).right_continuous x
      tendsto_atBot := ProbabilityTheory.tendsto_cdf_atBot ν
      tendsto_atTop := ProbabilityTheory.tendsto_cdf_atTop ν }

/-- The distribution function of a probability law with no atoms is continuous. -/
lemma continuous_toReal_measure_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] : Continuous (fun x => (ν (Set.Iic x)).toReal) := by
  have heq : (fun x => (ν (Set.Iic x)).toReal) = fun x => (ProbabilityTheory.cdf ν) x := by
    funext x
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
  rw [heq]
  set f := ProbabilityTheory.cdf ν with hf
  refine continuous_iff_continuousAt.2 (fun x => ?_)
  have hleft : Function.leftLim f x = f x := by
    have hsing : f.measure {x} = 0 := by
      rw [ProbabilityTheory.measure_cdf]; exact measure_singleton x
    have hval := f.measure_singleton x
    rw [hsing] at hval
    have hle : Function.leftLim f x ≤ f x := f.mono.leftLim_le le_rfl
    have h0 : f x - Function.leftLim f x ≤ 0 := by
      by_contra h
      push_neg at h
      exact (ENNReal.ofReal_pos.mpr h).ne' hval.symm
    linarith
  have hright : Function.rightLim f x = f x := (f.right_continuous x).rightLim_eq
  exact (f.mono.continuousAt_iff_leftLim_eq_rightLim).2 (hleft.trans hright.symm)

/-- `normalCDF m v` is a distribution function. -/
lemma isCDF_normalCDF (m : ℝ) (v : ℝ≥0) : IsCDF (normalCDF m v) :=
  isCDF_toReal_measure_Iic (gaussianReal m v)

/-- `stdNormalCDF` is a distribution function. -/
lemma isCDF_stdNormalCDF : IsCDF stdNormalCDF := isCDF_normalCDF 0 1

/-- A nondegenerate normal distribution function is continuous. -/
lemma continuous_normalCDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Continuous (normalCDF m v) :=
  haveI : NullSingletonClass (gaussianReal m v) := nullSingletonClass_gaussianReal hv
  continuous_toReal_measure_Iic (gaussianReal m v)

/-- The standard normal distribution function is continuous. -/
lemma continuous_stdNormalCDF : Continuous stdNormalCDF :=
  continuous_normalCDF 0 one_ne_zero

/-- A nondegenerate normal distribution function is strictly increasing. -/
lemma strictMono_normalCDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : StrictMono (normalCDF m v) := by
  intro y z hyz
  have hpos : 0 < gaussianReal m v (Set.Ioc y z) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hvol := (gaussianReal_absolutelyContinuous' m hv) h0
    rw [Real.volume_Ioc] at hvol
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne' hvol
  have hdisj : gaussianReal m v (Set.Iic z)
      = gaussianReal m v (Set.Iic y) + gaussianReal m v (Set.Ioc y z) := by
    rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
      Set.Iic_union_Ioc_eq_Iic hyz.le]
  have hfin : gaussianReal m v (Set.Iic y) ≠ ⊤ := measure_ne_top _ _
  unfold normalCDF
  rw [hdisj, ENNReal.toReal_add hfin (measure_ne_top _ _)]
  have hp2 : 0 < (gaussianReal m v (Set.Ioc y z)).toReal :=
    ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  linarith

/-- The `1 − α` quantile of a nondegenerate normal distribution function is a point of strict
increase. -/
lemma strictIncAt_normalCDF (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x₀ : ℝ) :
    StrictIncAt (normalCDF m v) x₀ :=
  ⟨fun _ hy => strictMono_normalCDF m hv hy, fun _ hz => strictMono_normalCDF m hv hz⟩

/-- **Standardisation of a centred normal distribution function.** For a positive standard
deviation `σ`, the distribution function of the centred normal law with variance `σ ^ 2` is the
standard normal distribution function evaluated at `x / σ`. -/
theorem normalCDF_sq_eq_stdNormalCDF {sigma : ℝ} (hsigma : 0 < sigma) (x : ℝ) :
    normalCDF 0 (Real.toNNReal (sigma ^ 2)) x = stdNormalCDF (x / sigma) := by
  have hv : Real.toNNReal (sigma ^ 2) = ⟨sigma ^ 2, sq_nonneg sigma⟩ :=
    Real.toNNReal_of_nonneg (sq_nonneg sigma)
  have hmap : (gaussianReal 0 1).map (fun z : ℝ => sigma * z)
      = gaussianReal 0 (Real.toNNReal (sigma ^ 2)) := by
    rw [hv]
    simpa using! gaussianReal_map_const_mul (μ := 0) (v := 1) sigma
  have hmeas : Measurable (fun z : ℝ => sigma * z) := by fun_prop
  have hpre : (fun z : ℝ => sigma * z) ⁻¹' Set.Iic x = Set.Iic (x / sigma) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ hsigma, mul_comm z sigma]
  unfold stdNormalCDF normalCDF
  rw [← hmap, Measure.map_apply hmeas measurableSet_Iic, hpre]

/-! ## Sup-CDF distance: elementary calculus -/

section SupCDFDist

variable {F G H : ℝ → ℝ}

/-- A distribution function takes values in `[0,1]` (a consequence of the fields, recorded
here for the boundedness estimates below). -/
theorem IsCDF.mem_Icc (h : IsCDF F) (t : ℝ) : F t ∈ Set.Icc (0 : ℝ) 1 :=
  mem_Icc_of_monotone_of_tendsto h.mono h.tendsto_atBot h.tendsto_atTop t

/-- The pointwise `|F − G|` of two distribution functions is bounded above by `1`, hence the
sup defining `supCDFDist` is a genuine supremum. -/
theorem bddAbove_absSub (hF : IsCDF F) (hG : IsCDF G) :
    BddAbove (Set.range fun t => |F t - G t|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hf := hF.mem_Icc t
  have hg := hG.mem_Icc t
  exact abs_le.mpr ⟨by linarith [hf.1, hf.2, hg.1, hg.2], by linarith [hf.1, hf.2, hg.1, hg.2]⟩

/-- `supCDFDist` is symmetric. -/
theorem supCDFDist_comm (F G : ℝ → ℝ) : supCDFDist F G = supCDFDist G F := by
  unfold supCDFDist
  congr 1
  ext t
  rw [abs_sub_comm]

/-- Nonnegativity of the sup-CDF distance between two distribution functions. -/
theorem supCDFDist_nonneg (hF : IsCDF F) (hG : IsCDF G) : 0 ≤ supCDFDist F G :=
  le_trans (abs_nonneg _) (le_ciSup (bddAbove_absSub hF hG) 0)

/-- Triangle inequality for the sup-CDF distance among distribution functions. -/
theorem supCDFDist_triangle_of_isCDF (hF : IsCDF F) (hG : IsCDF G) (hH : IsCDF H) :
    supCDFDist F H ≤ supCDFDist F G + supCDFDist G H := by
  refine ciSup_le (fun t => ?_)
  have h1 : |F t - G t| ≤ supCDFDist F G := le_ciSup (bddAbove_absSub hF hG) t
  have h2 : |G t - H t| ≤ supCDFDist G H := le_ciSup (bddAbove_absSub hG hH) t
  calc |F t - H t| ≤ |F t - G t| + |G t - H t| := abs_sub_le _ _ _
    _ ≤ _ := by linarith

/-- **Pólya, sup-distance form.** If distribution functions `Fn` converge pointwise to a
continuous distribution function `F`, then their sup-CDF distance to `F` tends to `0`. -/
theorem tendsto_supCDFDist_zero {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    (hFn : ∀ n, IsCDF (Fn n)) (hFcont : Continuous F) (hFcdf : IsCDF F)
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => supCDFDist (Fn n) F) atTop (𝓝 0) := by
  have hunif : TendstoUniformly Fn F atTop :=
    tendstoUniformly_of_monotone_of_continuous (fun n => (hFn n).mono)
      (fun n => (hFn n).tendsto_atBot) (fun n => (hFn n).tendsto_atTop) hFcont
      hFcdf.tendsto_atBot hFcdf.tendsto_atTop hconv
  rw [Metric.tendstoUniformly_iff] at hunif
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  have hle : supCDFDist (Fn n) F ≤ ε / 2 := by
    refine ciSup_le (fun t => ?_)
    have := hn' t
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  have hnn : 0 ≤ supCDFDist (Fn n) F := supCDFDist_nonneg (hFn n) hFcdf
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end SupCDFDist

/-! ## Quantile of a continuous distribution function -/

section QuantileCDF

variable {F : ℝ → ℝ}

/-- Nonemptiness of the sublevel set `{t | p ≤ F t}` for a distribution function and a level
strictly below `1`: the total-mass-`1` tail eventually clears the level. -/
theorem sublevel_nonempty (hF : IsCDF F) {p : ℝ} (hp : p < 1) :
    {t : ℝ | p ≤ F t}.Nonempty := by
  obtain ⟨y, hy⟩ := (hF.tendsto_atTop.eventually_const_lt hp).exists
  exact ⟨y, hy.le⟩

/-- Bounded-belowness of the sublevel set `{t | p ≤ F t}` for a distribution function and a
level strictly above `0`: the vanishing left tail keeps the set away from `−∞`. -/
theorem sublevel_bddBelow (hF : IsCDF F) {p : ℝ} (hp : 0 < p) :
    BddBelow {t : ℝ | p ≤ F t} := by
  obtain ⟨b, hb⟩ := eventually_atBot.mp (hF.tendsto_atBot.eventually_lt_const hp)
  refine ⟨b, fun y hy => ?_⟩
  by_contra h
  push_neg at h
  simp only [Set.mem_setOf_eq] at hy
  exact absurd (hb y h.le) (not_lt.mpr hy)

/-- For a continuous distribution function `F` and a level `p ∈ (0,1)`, the generalized inverse
attains the level exactly: `F (cdfPseudoInverse F p) = p`. -/
theorem cdf_quantile_eq (hF : IsCDF F) (hcont : Continuous F) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : F (cdfPseudoInverse F p) = p := by
  set q := cdfPseudoInverse F p with hq
  have hne : {t : ℝ | p ≤ F t}.Nonempty := sublevel_nonempty hF hp1
  have hbdd : BddBelow {t : ℝ | p ≤ F t} := sublevel_bddBelow hF hp0
  have hglb : IsGLB {t : ℝ | p ≤ F t} q := Real.isGLB_sInf hne hbdd
  -- `p ≤ F q`, since `q` lies in the (closed) sublevel set.
  have hge : p ≤ F q := by
    have hmem : q ∈ closure {t : ℝ | p ≤ F t} := hglb.mem_closure hne
    have hclosed : IsClosed {t : ℝ | p ≤ F t} :=
      isClosed_le continuous_const hcont
    rw [hclosed.closure_eq] at hmem
    exact hmem
  -- `F q ≤ p`: otherwise continuity yields points below `q` still in the set.
  refine le_antisymm ?_ hge
  by_contra hlt
  push_neg at hlt
  have hopen : IsOpen {y : ℝ | p < F y} := isOpen_lt continuous_const hcont
  have hev : ∀ᶠ y in 𝓝 q, p < F y := hopen.mem_nhds hlt
  have hev' : ∀ᶠ y in 𝓝[<] q, p < F y := hev.filter_mono nhdsWithin_le_nhds
  obtain ⟨y, hyF, hylt⟩ := (hev'.and self_mem_nhdsWithin).exists
  exact absurd (hglb.1 hyF.le) (not_le.mpr hylt)

/-- **Deterministic quantile convergence at a point of strict increase.** If nondecreasing
`Fn` converge pointwise to `F` and `F` is strictly increasing at `q` with `F q = p`, then the
generalized inverses at level `p` converge to `q`. (A `StrictIncAt`-localized twin of the
brick `tendsto_quantile_of_tendsto`, which needs global strict monotonicity.) -/
theorem tendsto_cdfPseudoInverse_of_tendsto {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {p q : ℝ}
    (hmono : ∀ n, Monotone (Fn n)) (hstrict : StrictIncAt F q) (hq : F q = p)
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => cdfPseudoInverse (Fn n) p) atTop (𝓝 q) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := ε / 2 with he
  have hepos : 0 < e := by positivity
  have he1 : F (q - e) < p := by rw [← hq]; exact hstrict.1 _ (by linarith)
  have he2 : p < F (q + e) := by rw [← hq]; exact hstrict.2 _ (by linarith)
  have hlowev : ∀ᶠ n in atTop, Fn n (q - e) < p := (hconv (q - e)).eventually_lt_const he1
  have hupev : ∀ᶠ n in atTop, p < Fn n (q + e) := (hconv (q + e)).eventually_const_lt he2
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
    exact absurd ((hmono n) h.le) (not_le.mpr (lt_of_lt_of_le hlow hx))
  have hmemup : (q + e) ∈ {x : ℝ | p ≤ Fn n x} := hup.le
  have h1 : q - e ≤ cdfPseudoInverse (Fn n) p := le_csInf ⟨q + e, hmemup⟩ hlb
  have h2 : cdfPseudoInverse (Fn n) p ≤ q + e := csInf_le ⟨q - e, hlb⟩ hmemup
  rw [Real.dist_eq]
  have hb : |cdfPseudoInverse (Fn n) p - q| ≤ e := abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

/-- **The sublevel set of a distribution function is a closed ray.**

For a level `p ∈ (0,1)`, `{t | p ≤ F t} = [F⁻¹(p), ∞)`: the level is cleared strictly to the right
of the generalized inverse by the greatest-lower-bound property, and at the generalized inverse
itself by right continuity. This is what makes the generalized inverse *measurable* in a
parameter, since `{F⁻¹(p) ≤ c}` becomes the far simpler `{p ≤ F c}`. -/
theorem setOf_le_cdf_eq_Ici {F : ℝ → ℝ} (hF : IsCDF F) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    {t : ℝ | p ≤ F t} = Set.Ici (cdfPseudoInverse F p) := by
  set q := cdfPseudoInverse F p with hq
  have hne : {t : ℝ | p ≤ F t}.Nonempty := sublevel_nonempty hF hp1
  have hbdd : BddBelow {t : ℝ | p ≤ F t} := sublevel_bddBelow hF hp0
  have hglb : IsGLB {t : ℝ | p ≤ F t} q := Real.isGLB_sInf hne hbdd
  have habove : ∀ t, q < t → p ≤ F t := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have hlb : t ∈ lowerBounds {u : ℝ | p ≤ F u} := by
      intro u hu
      by_contra h
      push_neg at h
      exact absurd (le_trans hu (hF.mono h.le)) (not_le.mpr hcon)
    exact absurd (hglb.2 hlb) (not_le.mpr ht)
  have hatq : p ≤ F q := by
    have htend : Tendsto F (𝓝[>] q) (𝓝 (F q)) :=
      (hF.right_continuous q).mono_left (nhdsWithin_mono q Set.Ioi_subset_Ici_self)
    exact ge_of_tendsto htend (Filter.eventually_of_mem self_mem_nhdsWithin habove)
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · intro ht; exact csInf_le hbdd ht
  · intro ht
    rcases eq_or_lt_of_le ht with rfl | hlt
    · exact hatq
    · exact habove t hlt

/-- **Measurability of a generalized inverse.**

The `p`-quantile of a family of distribution functions depending measurably on a parameter is a
measurable function of that parameter, for every level `p ∈ (0,1)`. Only pointwise measurability
in the parameter is needed — no joint measurability in `(ω, t)` — because the sublevel sets of the
quantile are the sets `{p ≤ f ω c}` (`setOf_le_cdf_eq_Ici`). -/
theorem measurable_cdfPseudoInverse {f : Ω → ℝ → ℝ} {p : ℝ}
    -- USER-INPUT: each member of the family is a distribution function
    (hcdf : ∀ ω, IsCDF (f ω)) (hp0 : 0 < p) (hp1 : p < 1)
    -- USER-INPUT: the family depends measurably on the parameter, level by level
    (hf : ∀ t : ℝ, Measurable fun ω => f ω t) :
    Measurable fun ω => cdfPseudoInverse (f ω) p := by
  refine measurable_of_Iic (fun c => ?_)
  have hset : (fun ω => cdfPseudoInverse (f ω) p) ⁻¹' Set.Iic c = {ω | p ≤ f ω c} := by
    ext ω
    have hEq := setOf_le_cdf_eq_Ici (hcdf ω) hp0 hp1
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    constructor
    · intro h
      have hc : c ∈ Set.Ici (cdfPseudoInverse (f ω) p) := h
      rw [← hEq] at hc
      exact hc
    · intro h
      have hc : c ∈ {t : ℝ | p ≤ f ω t} := h
      rw [hEq] at hc
      exact hc
  rw [hset]
  exact measurableSet_le measurable_const (hf c)

end QuantileCDF

/-! ## From distribution functions to weak convergence -/

section CDFtoWeak

/-- **Distribution-function convergence implies weak convergence.**

If the distribution functions of `F n` converge to that of `Q` at every continuity point of the
limit, then `F n` converges weakly to `Q`. The continuity points of a monotone function are
co-countable, hence dense, and the half-open intervals with endpoints there form a π-system of
arbitrarily small neighbourhoods; Mathlib's
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` then gives convergence in the weak
topology. -/
lemma tendsto_integral_of_tendsto_cdf
    {F : ℕ → Measure ℝ} {Q : Measure ℝ} (hFp : ∀ n, IsProbabilityMeasure (F n))
    [IsProbabilityMeasure Q]
    (hcdf : ∀ x : ℝ, ContinuousAt (fun t => (Q (Set.Iic t)).toReal) x →
      Tendsto (fun n => ((F n) (Set.Iic x)).toReal) atTop (𝓝 ((Q (Set.Iic x)).toReal)))
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ t, f t ∂(F n)) atTop (𝓝 (∫ t, f t ∂Q)) := by
  classical
  set cdfQ : ℝ → ℝ := fun t => (Q (Set.Iic t)).toReal with hcdfQ
  have hmono : Monotone cdfQ := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hab))
  set C : Set ℝ := {x | ContinuousAt cdfQ x} with hCdef
  have hCdense : Dense C := by
    have hcount : Set.Countable {x : ℝ | ¬ ContinuousAt cdfQ x} :=
      hmono.countable_not_continuousAt
    have hd := Set.Countable.dense_compl ℝ hcount
    have heq : {x : ℝ | ¬ ContinuousAt cdfQ x}ᶜ = C := by
      rw [hCdef]; ext x; simp
    rwa [heq] at hd
  set S : Set (Set ℝ) := {s | ∃ a ∈ C, ∃ b ∈ C, s = Set.Ioc a b} with hSdef
  -- `S` is a π-system
  have hpi : IsPiSystem S := by
    rintro s ⟨a, ha, b, hb, rfl⟩ t ⟨c, hc, d, hd, rfl⟩ -
    refine ⟨max a c, ?_, min b d, ?_, Set.Ioc_inter_Ioc⟩
    · rcases le_total a c with h | h
      · rwa [max_eq_right h]
      · rwa [max_eq_left h]
    · rcases le_total b d with h | h
      · rwa [min_eq_left h]
      · rwa [min_eq_right h]
  have hmeas : ∀ s ∈ S, MeasurableSet s := by
    rintro s ⟨a, -, b, -, rfl⟩
    exact measurableSet_Ioc
  -- `S` contains arbitrarily small neighbourhoods
  have hnbhd : ∀ u : Set ℝ, IsOpen u → ∀ x ∈ u, ∃ s ∈ S, s ∈ 𝓝 x ∧ s ⊆ u := by
    intro u hu x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hu x hx
    have hne1 : (Set.Ioo (x - ε) x).Nonempty :=
      ⟨x - ε / 2, by simp only [Set.mem_Ioo]; constructor <;> linarith⟩
    have hne2 : (Set.Ioo x (x + ε)).Nonempty :=
      ⟨x + ε / 2, by simp only [Set.mem_Ioo]; constructor <;> linarith⟩
    obtain ⟨a, haC, ha⟩ := hCdense.exists_mem_open isOpen_Ioo hne1
    obtain ⟨b, hbC, hb⟩ := hCdense.exists_mem_open isOpen_Ioo hne2
    refine ⟨Set.Ioc a b, ⟨a, haC, b, hbC, rfl⟩, ?_, ?_⟩
    · exact Filter.mem_of_superset (Ioo_mem_nhds ha.2 hb.1) Set.Ioo_subset_Ioc_self
    · intro y hy
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor
      · have := ha.1; have := hy.1; linarith
      · have := hb.2; have := hy.2; linarith
  -- convergence on the π-system
  set μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨F n, hFp n⟩ with hμs
  set νQ : ProbabilityMeasure ℝ := ⟨Q, inferInstance⟩ with hνQ
  have hstep : ∀ s ∈ S, Tendsto (fun n => μs n s) atTop (𝓝 (νQ s)) := by
    rintro s ⟨a, haC, b, hbC, rfl⟩
    rw [← NNReal.tendsto_coe]
    have hcoe1 : ∀ n : ℕ, ((μs n (Set.Ioc a b) : ℝ≥0) : ℝ)
        = ((F n) (Set.Ioc a b)).toReal := fun n => rfl
    have hcoe2 : ((νQ (Set.Ioc a b) : ℝ≥0) : ℝ) = (Q (Set.Ioc a b)).toReal := rfl
    simp only [hcoe1, hcoe2]
    rcases lt_or_ge b a with hba | hab
    · have hempty : Set.Ioc a b = (∅ : Set ℝ) := Set.Ioc_eq_empty (not_lt.2 hba.le)
      simp [hempty]
    · have hsplit : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
          (μ (Set.Ioc a b)).toReal = (μ (Set.Iic b)).toReal - (μ (Set.Iic a)).toReal := by
        intro μ hμ
        have hdisj : μ (Set.Iic b) = μ (Set.Iic a) + μ (Set.Ioc a b) := by
          rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
            Set.Iic_union_Ioc_eq_Iic hab]
        rw [hdisj, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        ring
      simp only [hsplit _ (hFp _), hsplit _ ‹IsProbabilityMeasure Q›]
      exact (hcdf b hbC).sub (hcdf a haC)
  have hconv : Tendsto μs atTop (𝓝 νQ) :=
    hpi.tendsto_probabilityMeasure_of_tendsto_of_mem hmeas hnbhd hstep
  exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv f

end CDFtoWeak

/-! ## Comparing a statistic with a random threshold -/

section RandomThreshold

/-- **Real form of convergence in probability to a constant.** Convergence in measure of `f n` to
the constant `a` says that the `edist`-excess sets are asymptotically null; this is the same
statement with the real absolute value and a real `ε`, which is the form the coupling argument
below consumes. -/
theorem tendsto_measure_abs_sub_of_tendstoInMeasure {Pr : Measure Ω} [IsFiniteMeasure Pr]
    {f : ℕ → Ω → ℝ} {a : ℝ} (h : TendstoInMeasure Pr f atTop (fun _ => a))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Pr {ω | ε ≤ |f n ω - a|}).toReal) atTop (𝓝 0) := by
  have hset : ∀ n : ℕ,
      {ω | ε ≤ |f n ω - a|} = {ω | ENNReal.ofReal ε ≤ edist (f n ω) a} := by
    intro n
    ext ω
    simp only [Set.mem_setOf_eq, edist_dist, Real.dist_eq]
    exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).symm
  simp only [hset]
  have h' := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  simpa using! (ENNReal.tendsto_toReal (by simp)).comp h'

/-- **Slutsky coupling at a random threshold.**

If the distribution functions of `S n` converge pointwise to `F`, and the thresholds `c n`
converge in probability to a point `a` at which `F` is continuous, then the probability that
`S n` does not exceed the *random* threshold `c n` converges to `F a`.

This is the analytic core shared by the bootstrap coverage statement, the asymptotic level of a
bootstrap test and the local-power computation: in each of them a statistic is compared with an
estimated critical value. No measurability is required — only monotonicity of measures — and the
measures are allowed to vary with `n`, which is what the contiguous-alternative applications
need. -/
theorem tendsto_measure_le_of_tendsto_cdf {μ : ℕ → Measure Ω} [∀ n, IsFiniteMeasure (μ n)]
    {S c : ℕ → Ω → ℝ} {F : ℝ → ℝ} {a : ℝ}
    -- USER-INPUT: the limit law is continuous at the limiting threshold; without it the
    -- probability can jump and the conclusion fails
    (hFa : ContinuousAt F a)
    -- USER-INPUT: the distribution functions of the statistic converge pointwise to `F`
    (hcdf : ∀ x : ℝ, Tendsto (fun n => (μ n {ω | S n ω ≤ x}).toReal) atTop (𝓝 (F x)))
    -- USER-INPUT: the thresholds converge to `a` in probability
    (hc : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n {ω | ε ≤ |c n ω - a|}).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n {ω | S n ω ≤ c n ω}).toReal) atTop (𝓝 (F a)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.continuousAt_iff] at hFa
  obtain ⟨δ', hδ'pos, hδ'⟩ := hFa (ε / 4) (by positivity)
  set δ := δ' / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have hupabs : |F (a + δ) - F a| < ε / 4 := by
    have hd : dist (a + δ) a < δ' := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hδpos]; linarith
    have := hδ' hd; rwa [Real.dist_eq] at this
  have hloabs : |F (a - δ) - F a| < ε / 4 := by
    have hd : dist (a - δ) a < δ' := by
      rw [Real.dist_eq]
      have hne : a - δ - a = -δ := by ring
      rw [hne, abs_neg, abs_of_pos hδpos]; linarith
    have := hδ' hd; rwa [Real.dist_eq] at this
  rw [abs_lt] at hupabs hloabs
  -- the two coupling inclusions: a random threshold either behaves like the deterministic one
  -- shifted by `δ`, or it is `δ`-far from `a`
  have hUp : ∀ n, {ω | S n ω ≤ c n ω} ⊆
      {ω | S n ω ≤ a + δ} ∪ {ω | δ ≤ |c n ω - a|} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_or_gt (c n ω) (a + δ) with h | h
    · exact Or.inl (le_trans hω h)
    · refine Or.inr ?_
      rw [abs_of_pos (by linarith : (0 : ℝ) < c n ω - a)]; linarith
  have hLo : ∀ n, {ω | S n ω ≤ a - δ} ⊆
      {ω | S n ω ≤ c n ω} ∪ {ω | δ ≤ |c n ω - a|} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases lt_or_ge (c n ω) (a - δ) with h | h
    · refine Or.inr ?_
      rw [abs_of_neg (by linarith : c n ω - a < 0)]; linarith
    · exact Or.inl (le_trans hω h)
  have e1 : ∀ᶠ n in atTop, (μ n {ω | S n ω ≤ a + δ}).toReal < F a + ε / 2 :=
    (hcdf (a + δ)).eventually_lt_const (by linarith [hupabs.2])
  have e2 : ∀ᶠ n in atTop, F a - ε / 2 < (μ n {ω | S n ω ≤ a - δ}).toReal :=
    (hcdf (a - δ)).eventually_const_lt (by linarith [hloabs.1])
  have e3 : ∀ᶠ n in atTop, (μ n {ω | δ ≤ |c n ω - a|}).toReal < ε / 2 :=
    (hc δ hδpos).eventually_lt_const (by positivity)
  rw [Filter.eventually_atTop] at e1 e2 e3
  obtain ⟨N₁, hN₁⟩ := e1
  obtain ⟨N₂, hN₂⟩ := e2
  obtain ⟨N₃, hN₃⟩ := e3
  refine ⟨max (max N₁ N₂) N₃, fun n hn => ?_⟩
  have hn1 := hN₁ n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)
  have hn2 := hN₂ n (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn)
  have hn3 := hN₃ n (le_trans (le_max_right _ _) hn)
  have hup : (μ n {ω | S n ω ≤ c n ω}).toReal ≤
      (μ n {ω | S n ω ≤ a + δ}).toReal + (μ n {ω | δ ≤ |c n ω - a|}).toReal := by
    have hle : μ n {ω | S n ω ≤ c n ω} ≤
        μ n {ω | S n ω ≤ a + δ} + μ n {ω | δ ≤ |c n ω - a|} :=
      le_trans (measure_mono (hUp n)) (measure_union_le _ _)
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
  have hlo : (μ n {ω | S n ω ≤ a - δ}).toReal ≤
      (μ n {ω | S n ω ≤ c n ω}).toReal + (μ n {ω | δ ≤ |c n ω - a|}).toReal := by
    have hle : μ n {ω | S n ω ≤ a - δ} ≤
        μ n {ω | S n ω ≤ c n ω} + μ n {ω | δ ≤ |c n ω - a|} :=
      le_trans (measure_mono (hLo n)) (measure_union_le _ _)
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) hle
    rwa [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at this
  rw [Real.dist_eq, abs_lt]
  constructor <;> [linarith; linarith]

end RandomThreshold

/-! ## Consistency of the bootstrap sampling distribution -/

section Consistency

variable {Pr : Measure Ω} {P : Measure 𝓧} {J : ℕ → Measure 𝓧 → ℝ → ℝ}
  {C_P : Set (ℕ → Measure 𝓧)} {Jlim : ℝ → ℝ} {Phat : ℕ → Ω → Measure 𝓧} {R : ℕ → Ω → ℝ} {α : ℝ}

/-- **Bootstrap consistency, uniform (sup-distance) form.**

If the sampling distribution functions converge, along every sequence of the class `C_P`, to a
common continuous limit `Jlim`, if the constant sequence at the true law `P` belongs to `C_P`,
and if the estimated sequence `n ↦ Phat n ω` belongs to `C_P` for almost every `ω`, then the
bootstrap sampling distribution is uniformly close to the true one, almost surely:
`sup_x |J n P x − J n (Phat n ω) x| → 0`. -/
theorem tendsto_supCDFDist_bootstrap
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class; this
    -- is what ties the class to the law actually generating the sample
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: along every sequence of the class the sampling distribution functions
    -- converge pointwise to the common limit
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: the common limit law is continuous; this is the exact continuity requirement
    -- that turns pointwise convergence into uniform convergence
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: the estimated sequence of laws belongs to the class almost surely; the only
    -- stochastic ingredient of the criterion
    (hPhat_mem : ∀ᵐ ω ∂Pr, (fun n => Phat n ω) ∈ C_P) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => supCDFDist (J n P) (J n (Phat n ω))) atTop (𝓝 0) := by
  filter_upwards [hPhat_mem] with ω hω
  -- Both `J n P` and `J n (Phat n ω)` converge pointwise to the continuous limit `Jlim`.
  have hPconv : ∀ x, Tendsto (fun n => J n P x) atTop (𝓝 (Jlim x)) := hJconv _ hP_mem
  have hHconv : ∀ x, Tendsto (fun n => J n (Phat n ω) x) atTop (𝓝 (Jlim x)) := hJconv _ hω
  have hA : Tendsto (fun n => supCDFDist (J n P) Jlim) atTop (𝓝 0) :=
    tendsto_supCDFDist_zero (fun n => hJcdf n P) hJlim_cont hJlim_cdf hPconv
  have hB : Tendsto (fun n => supCDFDist Jlim (J n (Phat n ω))) atTop (𝓝 0) := by
    have h := tendsto_supCDFDist_zero (fun n => hJcdf n (Phat n ω)) hJlim_cont hJlim_cdf hHconv
    simpa only [supCDFDist_comm] using h
  -- Squeeze between `0` and `supCDFDist (J n P) Jlim + supCDFDist Jlim (J n Phat)`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ => (0 : ℝ))
    (h := fun n => supCDFDist (J n P) Jlim + supCDFDist Jlim (J n (Phat n ω)))
    tendsto_const_nhds (by simpa using hA.add hB) (fun n => ?_) (fun n => ?_)
  · exact supCDFDist_nonneg (hJcdf n P) (hJcdf n (Phat n ω))
  · exact supCDFDist_triangle_of_isCDF (hJcdf n P) hJlim_cdf (hJcdf n (Phat n ω))

/-- **Bootstrap quantile consistency.**

Under the hypotheses of `tendsto_supCDFDist_bootstrap`, if the limit law is in addition
strictly increasing at its `1 − α` quantile, then the estimated `1 − α` quantile converges
almost surely to the quantile of the limit law. -/
theorem tendsto_bootstrapQuantile
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: convergence of the sampling distribution functions along the class
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: continuity of the common limit law
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: almost sure membership of the estimated sequence in the class
    (hPhat_mem : ∀ᵐ ω ∂Pr, (fun n => Phat n ω) ∈ C_P)
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: the limit law is strictly increasing at the quantile being estimated; without
    -- it the quantile is not uniquely determined and need not converge
    (hstrict : StrictIncAt Jlim (cdfPseudoInverse Jlim (1 - α))) :
    ∀ᵐ ω ∂Pr, Tendsto (fun n => cdfPseudoInverse (J n (Phat n ω)) (1 - α)) atTop
      (𝓝 (cdfPseudoInverse Jlim (1 - α))) := by
  set q := cdfPseudoInverse Jlim (1 - α) with hqdef
  have hq : Jlim q = 1 - α :=
    cdf_quantile_eq hJlim_cdf hJlim_cont (by linarith [hα.2]) (by linarith [hα.1])
  filter_upwards [hPhat_mem] with ω hω
  have hHconv : ∀ x, Tendsto (fun n => J n (Phat n ω) x) atTop (𝓝 (Jlim x)) := hJconv _ hω
  exact tendsto_cdfPseudoInverse_of_tendsto (fun n => (hJcdf n (Phat n ω)).mono) hstrict hq hHconv

/-- **Asymptotic coverage of the bootstrap confidence set.**

The bootstrap confidence set for the parameter of interest consists of those parameter values
whose root does not exceed the estimated `1 − α` quantile; the true parameter is covered
exactly when `R n ω ≤ cdfPseudoInverse (J n (Phat n ω)) (1 − α)`, where `R n` is the root
evaluated at the true parameter. Its coverage probability converges to the nominal level. -/
theorem tendsto_bootstrapCoverage [IsProbabilityMeasure Pr]
    -- USER-INPUT: the constant sequence at the data-generating law belongs to the class
    (hP_mem : (fun _ => P) ∈ C_P)
    -- USER-INPUT: convergence of the sampling distribution functions along the class
    (hJconv : ∀ Q ∈ C_P, ∀ x : ℝ, Tendsto (fun n => J n (Q n) x) atTop (𝓝 (Jlim x)))
    -- USER-INPUT: continuity of the common limit law
    (hJlim_cont : Continuous Jlim)
    -- USER-INPUT: the common limit is a distribution function
    (hJlim_cdf : IsCDF Jlim)
    -- USER-INPUT: every sampling distribution is a distribution function
    (hJcdf : ∀ (n : ℕ) (Q : Measure 𝓧), IsCDF (J n Q))
    -- USER-INPUT: almost sure membership of the estimated sequence in the class
    (hPhat_mem : ∀ᵐ ω ∂Pr, (fun n => Phat n ω) ∈ C_P)
    -- USER-INPUT: nominal level strictly between `0` and `1`
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    -- USER-INPUT: strict increase of the limit law at the estimated quantile
    (hstrict : StrictIncAt Jlim (cdfPseudoInverse Jlim (1 - α)))
    -- USER-INPUT: at the data-generating law the field `J` is the exact sampling distribution
    -- function of the root; this is what makes `J` the object being bootstrapped
    (hJP : ∀ (n : ℕ) (x : ℝ), J n P x = (Pr {ω | R n ω ≤ x}).toReal)
    -- LEAN-ONLY: the root is measurable; needed for the coverage event to carry its measure
    (hRmeas : ∀ n, Measurable (R n))
    -- LEAN-ONLY: the estimated critical value is measurable in the sample; no measurability in
    -- the measure argument of `J` is assumed, so this is recorded directly
    (hqmeas : ∀ n, Measurable fun ω => cdfPseudoInverse (J n (Phat n ω)) (1 - α)) :
    Tendsto (fun n => (Pr {ω | R n ω ≤ cdfPseudoInverse (J n (Phat n ω)) (1 - α)}).toReal)
      atTop (𝓝 (1 - α)) := by
  set q := cdfPseudoInverse Jlim (1 - α) with hqdef
  have hq : Jlim q = 1 - α :=
    cdf_quantile_eq hJlim_cdf hJlim_cont (by linarith [hα.2]) (by linarith [hα.1])
  set qn : ℕ → Ω → ℝ := fun n ω => cdfPseudoInverse (J n (Phat n ω)) (1 - α) with hqndef
  -- The bootstrap critical values converge in probability to the limit quantile `q`.
  have hquant : ∀ᵐ ω ∂Pr, Tendsto (fun n => qn n ω) atTop (𝓝 q) :=
    tendsto_bootstrapQuantile hP_mem hJconv hJlim_cont hJlim_cdf hJcdf hPhat_mem hα hstrict
  have hInMeas : TendstoInMeasure Pr qn atTop (fun _ => q) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hqmeas n).aestronglyMeasurable) hquant
  -- The sampling distribution functions of the root at `P` are the ones supplied by `J`.
  have hcdf : ∀ x : ℝ, Tendsto (fun n => (Pr {ω | R n ω ≤ x}).toReal) atTop (𝓝 (Jlim x)) := by
    intro x
    simpa only [hJP] using hJconv (fun _ => P) hP_mem x
  have hmain := tendsto_measure_le_of_tendsto_cdf (μ := fun _ : ℕ => Pr) (S := R) (c := qn)
    hJlim_cont.continuousAt hcdf
    (fun ε hε => tendsto_measure_abs_sub_of_tendstoInMeasure hInMeas hε)
  rwa [hq] at hmain

end Consistency

/-! ## A weak law of large numbers for triangular arrays -/

/-- **Weak law of large numbers for a triangular array.**

Let `Y n 0, …, Y n (n−1)` be a triangular array of independent random variables, the entries of
row `n` all having distribution function `G n`. If `G n` converges in distribution to the law
`ν` (with distribution function `Glim`) and the first absolute moments converge to the — finite
— first absolute moment of `ν`, then the row averages converge in probability to the mean of
`ν`. This is the moment-convergence tool behind the nonparametric-mean applications. -/
theorem tendstoInMeasure_rowMean_triangular {Pr : Measure Ω} [IsProbabilityMeasure Pr]
    {Y : ℕ → ℕ → Ω → ℝ} {G : ℕ → ℝ → ℝ} {Glim : ℝ → ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    -- LEAN-ONLY: the array entries are measurable; the distribution-function hypotheses below
    -- would otherwise refer to outer measures of non-measurable sets
    (hYmeas : ∀ n i, Measurable (Y n i))
    -- USER-INPUT: the entries within each row are independent
    (hindep : ∀ n : ℕ, iIndepFun (fun i : Fin n => Y n i) Pr)
    -- USER-INPUT: the entries of row `n` all have distribution function `G n`
    (hGrow : ∀ n : ℕ, ∀ i < n, ∀ x : ℝ, G n x = (Pr {ω | Y n i ω ≤ x}).toReal)
    -- USER-INPUT: `Glim` is the distribution function of the limit law `ν`
    (hGlim : ∀ x : ℝ, Glim x = (ν (Set.Iic x)).toReal)
    -- USER-INPUT: the row laws converge in distribution to `ν`, i.e. their distribution
    -- functions converge at every continuity point of the limit
    (hGconv : ∀ x : ℝ, ContinuousAt Glim x → Tendsto (fun n => G n x) atTop (𝓝 (Glim x)))
    -- USER-INPUT: the limit law has a finite first absolute moment
    (hint : Integrable (fun t : ℝ => t) ν)
    -- USER-INPUT: every row has a finite first absolute moment.  This is the hypothesis added by
    -- the documented repair of `triangular_wlln_of_L1`: without it the Bochner integral in
    -- `habs` below is the junk value `0` for heavy-tailed rows and the weak law is FALSE (see
    -- the counterexample in the docstring of `triangular_wlln_of_L1`).
    (hYint : ∀ n : ℕ, Integrable (Y n 0) Pr)
    -- USER-INPUT: convergence of the first absolute moments to that of the limit law; this is
    -- the uniform-integrability substitute that upgrades weak convergence to a weak law
    (habs : Tendsto (fun n => ∫ ω, |Y n 0 ω| ∂Pr) atTop (𝓝 (∫ t, |t| ∂ν))) :
    TendstoInMeasure Pr (fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, Y n i ω)) atTop
      (fun _ => ∫ t, t ∂ν) := by
  -- the common law of the entries of row `n`
  set Gm : ℕ → Measure ℝ := fun n => Pr.map (Y n 0) with hGm
  haveI hGmprob : ∀ n, IsProbabilityMeasure (Gm n) := fun n =>
    Measure.isProbabilityMeasure_map (hYmeas n 0).aemeasurable
  -- every entry of a row carries the row law: they share a distribution function, and a finite
  -- measure on the line is determined by its values on the rays `Iic x`
  have hlaw : ∀ (n : ℕ) (i : Fin n), Pr.map (Y n (i : ℕ)) = Gm n := by
    intro n i
    refine Measure.ext_of_Iic _ _ (fun x => ?_)
    have h1 : Pr.map (Y n (i : ℕ)) (Set.Iic x) = Pr {ω | Y n (i : ℕ) ω ≤ x} := by
      rw [Measure.map_apply (hYmeas n (i : ℕ)) measurableSet_Iic]; rfl
    have h2 : Gm n (Set.Iic x) = Pr {ω | Y n 0 ω ≤ x} := by
      rw [hGm]
      simp only []
      rw [Measure.map_apply (hYmeas n 0) measurableSet_Iic]; rfl
    have hre : (Pr {ω | Y n (i : ℕ) ω ≤ x}).toReal = (Pr {ω | Y n 0 ω ≤ x}).toReal := by
      rw [← hGrow n (i : ℕ) i.isLt x, ← hGrow n 0 i.pos x]
    rw [h1, h2]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hre
  -- weak convergence of the row laws: the distribution-function hypothesis upgraded by the
  -- one-direction portmanteau brick of this file
  have hweak : ∀ f : ℝ →ᵇ ℝ, Tendsto (fun n => ∫ y, f y ∂(Gm n)) atTop (𝓝 (∫ y, f y ∂ν)) := by
    refine tendsto_integral_of_tendsto_cdf hGmprob (fun x hx => ?_)
    have hxc : ContinuousAt Glim x :=
      ContinuousAt.congr hx (Filter.Eventually.of_forall fun y => (hGlim y).symm)
    have hconv := hGconv x hxc
    rw [hGlim x] at hconv
    refine hconv.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [hGrow n 0 hn x, hGm]
    simp only []
    rw [Measure.map_apply (hYmeas n 0) measurableSet_Iic]
    rfl
  -- convergence of the first absolute moments, transported to the row laws
  have hL1 : Tendsto (fun n => ∫ y, |y| ∂(Gm n)) atTop (𝓝 (∫ y, |y| ∂ν)) := by
    refine habs.congr (fun n => ?_)
    rw [hGm]
    simp only []
    rw [integral_map (hYmeas n 0).aemeasurable (by fun_prop)]
  -- the repaired weak law needs the row laws to have a finite first absolute moment
  have hGmint : ∀ n, Integrable id (Gm n) := by
    intro n
    rw [hGm]
    simp only []
    exact (integrable_map_measure aestronglyMeasurable_id (hYmeas n 0).aemeasurable).mpr
      (by simpa using hYint n)
  have hmain := triangular_wlln_of_L1 (P := Pr) (Y := fun n (i : Fin n) => Y n (i : ℕ))
    (G := Gm) (ν := ν) (fun n i => hYmeas n (i : ℕ)) hindep hlaw hGmint hweak
    (by simpa using! hint) hL1
  have hfun : (fun (n : ℕ) ω => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, Y n i ω))
      = fun (n : ℕ) ω => (n : ℝ)⁻¹ * ∑ i : Fin n, Y n (i : ℕ) ω := by
    funext n ω
    rw [Fin.sum_univ_eq_sum_range (fun i => Y n i ω) n]
  rw [hfun]
  exact hmain

end StatLean.HypothesisTesting
