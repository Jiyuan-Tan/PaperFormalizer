module
public import StatLean.TimeSeries.Models.Defs
public import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity
-- `nlARKernel_geometricallyErgodic` (FY Thm 2.4(ii)) is stated here: its proof consumes
-- the Harris engine, and `HarrisTheorem` imports `GeometricErgodicity`, so the theorem
-- had to live on the far side of that import edge.
public import StatLean.TimeSeries.ForMathlib.Markov.HarrisTheorem
public import StatLean.TimeSeries.ForMathlib.Markov.TwoSidedChain
public import StatLean.TimeSeries.Process.Stationary
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Threshold autoregression: structure and stationarity (FY §4.1.1, Definition 4.1)

The `k`-regime TAR model is `Models/Defs.lean`'s `IsTAR` (FY eq. (4.1)). This file
carries the §4.1.1 structural facts:

* **SETAR** (`IsSETAR`): the interval-partition special case
  `A_i = (r_{i−1}, r_i]` with `−∞ = r_0 < ⋯ < r_k = +∞`, and the fact that a SETAR
  partition is a legitimate TAR partition;
* the **stationarity claim** of pp. 126–127 ("easy to see from Theorem 2.4"): under
  (a) equal regime scales `σ₁ = ⋯ = σ_k` *(the book prints `σ_p` — typo)* and
  (b) `max_i Σ_j |b_{ij}| < 1`, a strictly stationary solution exists. FY delegates
  this entirely to §2.1.4's Theorem 2.4 + Example 2.1, so we state it as a corollary
  of the Markov-layer theorem `nlARKernel_geometricallyErgodic` (PROVED in batch F,
  axiom-clean, in `ForMathlib/Markov/HarrisTheorem.lean`): the TAR autoregression
  function is the `nlARKernel`
  drift function, and the contraction condition (b) is the Lyapunov input;
* the **canonical toy instance** eq. (4.2), `X_t = ∓0.7 X_{t−1} + ε_t` according to the
  sign of `X_{t−1} − r`, exhibited as a two-regime SETAR satisfying (a)+(b).

**Scope.** FY Theorems 4.1 and 4.2 (Chan 1993a: strong consistency; `T(r̂ − r) = O_p(1)`
and the associated asymptotics) and their consumers were **descoped on 2026-08-04** at
the user's direction and are not stated anywhere in this area.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.1.1,
Definition 4.1, eqs. (4.1)–(4.3) and the stationarity discussion pp. 126–127.
(`FY §4.1.1`.)

**Bibliographic comments.** Threshold autoregression is H. Tong (1978; *Non-linear Time
Series: A Dynamical System Approach*, OUP 1990); the drift/ergodicity route for TAR
stationarity is An & Huang (1996) and Chan & Tong (1985).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The Gaussian density is continuous — the input `nlARKernel_geometricallyErgodic`
(FY Thm 2.4(ii)) asks for on top of positivity. The pin has `measurable_gaussianPDFReal`
but no continuity lemma, and it is immediate from the closed form. -/
private lemma continuous_gaussianPDF (m : ℝ) (v : NNReal) :
    Continuous (ProbabilityTheory.gaussianPDF m v) := by
  have h : Continuous (ProbabilityTheory.gaussianPDFReal m v) := by
    unfold ProbabilityTheory.gaussianPDFReal
    fun_prop
  exact ENNReal.continuous_ofReal.comp h

/-- The **SETAR interval partition** determined by ordered thresholds
`r : Fin (k − 1) → ℝ`: regime `i` is `(r_{i−1}, r_i]` with the conventions
`r_{−1} = −∞`, `r_{k−1} = +∞`. -/
def setarPartition {k : ℕ} (r : Fin k → ℝ) : Fin (k + 1) → Set ℝ := fun i =>
  {x : ℝ | (∀ j : Fin k, (j : ℕ) < (i : ℕ) → r j < x) ∧
    ∀ j : Fin k, (i : ℕ) ≤ (j : ℕ) → x ≤ r j}

-- The regime `i` is a finite intersection of half-lines: for each threshold index `j`
-- one of the two guards is vacuous and the other cuts out an `Ioi` resp. an `Iic`.
private lemma setarPartition_eq_iInter {k : ℕ} (r : Fin k → ℝ) (i : Fin (k + 1)) :
    setarPartition r i =
      (⋂ j : Fin k, {x : ℝ | (j : ℕ) < (i : ℕ) → r j < x}) ∩
        ⋂ j : Fin k, {x : ℝ | (i : ℕ) ≤ (j : ℕ) → x ≤ r j} := by
  ext x
  simp only [setarPartition, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]

-- The **regime index of a point**: the number of thresholds strictly below `x`. Under
-- `StrictMono r` the set `{j | r j < x}` is a down-closed initial segment of `Fin k`, so
-- its cardinality is exactly the index of the regime containing `x`.
private noncomputable def setarIndex {k : ℕ} (r : Fin k → ℝ) (x : ℝ) : Fin (k + 1) :=
  ⟨(Finset.univ.filter fun j : Fin k => r j < x).card,
    Nat.lt_succ_of_le (by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin k)) _)⟩

-- Existence: `x` lies in the regime indexed by its threshold count. Both halves are
-- cardinality arguments against the initial segment `Iio j` resp. `Iic j`.
private lemma mem_setarPartition_setarIndex {k : ℕ} {r : Fin k → ℝ} (hr : StrictMono r)
    (x : ℝ) : x ∈ setarPartition r (setarIndex r x) := by
  classical
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · -- `j` is below the count, so `r j < x`: otherwise `{j' | r j' < x} ⊆ Iio j`.
    by_contra hx
    push_neg at hx
    have hsub : (Finset.univ.filter fun j' : Fin k => r j' < x) ⊆ Finset.Iio j := by
      intro j' hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      simp only [Finset.mem_Iio]
      by_contra hle
      push_neg at hle
      exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hj' hx) (hr.monotone hle)) (lt_irrefl _)
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iio] at hcard
    simp only [setarIndex] at hj
    omega
  · -- `j` is at or above the count, so `x ≤ r j`: otherwise `Iic j ⊆ {j' | r j' < x}`.
    by_contra hx
    push_neg at hx
    have hsub : Finset.Iic j ⊆ Finset.univ.filter fun j' : Fin k => r j' < x := by
      intro j' hj'
      simp only [Finset.mem_Iic] at hj'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hr.monotone hj') hx
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hcard
    simp only [setarIndex] at hj
    omega

-- Uniqueness: a point cannot lie in two regimes. If `i < i'` then `j := i` is a legitimate
-- threshold index, and the two memberships give `r j < x` and `x ≤ r j`.
private lemma setarPartition_not_mem_of_lt {k : ℕ} {r : Fin k → ℝ} {x : ℝ}
    {i i' : Fin (k + 1)} (h : x ∈ setarPartition r i) (h' : x ∈ setarPartition r i')
    (hlt : (i : ℕ) < (i' : ℕ)) : False := by
  have hik : (i : ℕ) < k := lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp i'.isLt)
  have h1 : r ⟨(i : ℕ), hik⟩ < x := h'.1 ⟨(i : ℕ), hik⟩ hlt
  have h2 : x ≤ r ⟨(i : ℕ), hik⟩ := h.2 ⟨(i : ℕ), hik⟩ le_rfl
  linarith

/-- A SETAR partition is a measurable partition of `ℝ` (so `IsTAR` applies to it):
the regimes are measurable, pairwise disjoint, and cover the line. -/
theorem setarPartition_isPartition {k : ℕ} {r : Fin k → ℝ} (hr : StrictMono r) :
    (∀ i, MeasurableSet (setarPartition r i)) ∧
      (Pairwise fun i j => Disjoint (setarPartition r i) (setarPartition r j)) ∧
      (⋃ i, setarPartition r i) = Set.univ := by
  classical
  refine ⟨fun i => ?_, fun i i' hne => ?_, ?_⟩
  · rw [setarPartition_eq_iInter]
    refine MeasurableSet.inter (MeasurableSet.iInter fun j => ?_)
      (MeasurableSet.iInter fun j => ?_)
    · by_cases h : (j : ℕ) < (i : ℕ)
      · have he : {x : ℝ | (j : ℕ) < (i : ℕ) → r j < x} = Set.Ioi (r j) := by
          ext x; simp [h, Set.mem_Ioi]
        rw [he]; exact measurableSet_Ioi
      · have he : {x : ℝ | (j : ℕ) < (i : ℕ) → r j < x} = Set.univ := by
          ext x; simp [h]
        rw [he]; exact MeasurableSet.univ
    · by_cases h : (i : ℕ) ≤ (j : ℕ)
      · have he : {x : ℝ | (i : ℕ) ≤ (j : ℕ) → x ≤ r j} = Set.Iic (r j) := by
          ext x; simp [h, Set.mem_Iic]
        rw [he]; exact measurableSet_Iic
      · have he : {x : ℝ | (i : ℕ) ≤ (j : ℕ) → x ≤ r j} = Set.univ := by
          ext x; simp [h]
        rw [he]; exact MeasurableSet.univ
  · refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rcases lt_or_gt_of_ne (fun hcon : (i : ℕ) = (i' : ℕ) => hne (Fin.ext hcon)) with h | h
    · exact setarPartition_not_mem_of_lt hx hx' h
    · exact setarPartition_not_mem_of_lt hx' hx h
  · exact Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.mpr ⟨setarIndex r x, mem_setarPartition_setarIndex hr x⟩

/-- **SETAR model** (FY §4.1.1): a TAR whose regimes form an interval partition. -/
def IsSETAR {k P : ℕ} (b0 : Fin (k + 1) → ℝ) (b : Fin (k + 1) → Fin P → ℝ)
    (σ : Fin (k + 1) → ℝ) (r : Fin k → ℝ) (d : ℕ) (X ε : ℤ → Ω → ℝ)
    (μ : Measure Ω) : Prop :=
  StrictMono r ∧ IsTAR b0 b σ (setarPartition r) d X ε μ

/-- The **TAR autoregression function** on the state vector `(x_{t−1}, …, x_{t−P})`
extended with the threshold coordinate: `f(𝐱) = Σᵢ (b_{i0} + Σⱼ b_{ij} x_j)·1_{A_i}(x_d)`
(FY eq. (4.1) without the noise term). Used to instantiate the Markov layer's
`nlARKernel`. -/
noncomputable def tarDrift {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ)
    (A : Fin k → Set ℝ) (d : ℕ) (x : Fin (P + 1) → ℝ) : ℝ :=
  ∑ i, (A i).indicator
    (fun _ => b0 i + ∑ j : Fin P, b i j * x (j.castSucc)) (x ⟨min d P, by omega⟩)

/-! ### The TAR state chain

`nlARKernel`'s state at time `s` is `x j = X_{s−j}` (`j : Fin (P + 1)`), so in the
recursion `X_t = f(state at t − 1) + noise` the regressors `X_{t−1−j}` of eq. (4.1) are
the coordinates `x j.castSucc` (`j : Fin P`) and the threshold variable `X_{t−d}` is the
coordinate `d − 1`. `tarStateDrift` is eq. (4.1)'s autoregression function in exactly
those coordinates. (The public `tarDrift` above reads the threshold at `min d P`, which
in these coordinates is `X_{t−1−d}`; the shift by one is why the derivation below uses
its own drift.) -/

/-- The TAR autoregression function in the state-vector coordinates of `nlARKernel`. -/
private noncomputable def tarStateDrift {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ)
    (A : Fin k → Set ℝ) (d : ℕ) (x : Fin (P + 1) → ℝ) : ℝ :=
  ∑ i, (A i).indicator
    (fun _ => b0 i + ∑ j : Fin P, b i j * x (j.castSucc)) (x ⟨min (d - 1) P, by omega⟩)

-- On a partition exactly one indicator fires, so an indicator sum collapses to its
-- single active term.
private lemma sum_indicator_of_partition {k : ℕ} {A : Fin k → Set ℝ}
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) {y : ℝ} {i0 : Fin k} (hy : y ∈ A i0)
    (g : Fin k → ℝ) : ∑ i, (A i).indicator (fun _ => g i) y = g i0 := by
  classical
  have hone : (A i0).indicator (fun _ => g i0) y = g i0 := by
    simp only [Set.indicator_apply, if_pos hy]
  rw [← hone]
  refine Finset.sum_eq_single_of_mem i0 (Finset.mem_univ i0) fun i _ hne => ?_
  have hnot : y ∉ A i := fun hmem => Set.disjoint_left.mp (hdisj hne) hmem hy
  simp only [Set.indicator_apply, if_neg hnot]

-- Adding a constant to every branch of a partition indicator sum adds it once.
private lemma sum_indicator_add_const {k : ℕ} {A : Fin k → Set ℝ}
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j)) (hcov : (⋃ i, A i) = Set.univ)
    (g : Fin k → ℝ) (z y : ℝ) :
    ∑ i, (A i).indicator (fun _ => g i + z) y
      = (∑ i, (A i).indicator (fun _ => g i) y) + z := by
  have hmem : y ∈ ⋃ i, A i := by rw [hcov]; exact Set.mem_univ _
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hmem
  rw [sum_indicator_of_partition hdisj hi0 (fun i => g i + z),
    sum_indicator_of_partition hdisj hi0 g]

private lemma measurable_tarStateDrift {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ)
    {A : Fin k → Set ℝ} (hA : ∀ i, MeasurableSet (A i)) (d : ℕ) :
    Measurable (tarStateDrift b0 b A d) := by
  classical
  refine Finset.measurable_sum (Finset.univ : Finset (Fin k)) fun i _ => ?_
  simp only [Set.indicator_apply]
  refine Measurable.ite (measurable_pi_apply _ (hA i)) ?_ measurable_const
  exact measurable_const.add
    (Finset.measurable_sum (Finset.univ : Finset (Fin P)) fun j _ =>
      measurable_const.mul (measurable_pi_apply _))

-- The **contraction bound** (FY p. 126 condition (b)) in the form Theorem 2.4(ii) wants:
-- exactly one regime fires, so the drift is a single affine form whose slope mass is at
-- most `lam` and whose intercept is at most `c`.
private lemma tarStateDrift_bound {k P : ℕ} {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ}
    {A : Fin k → Set ℝ} (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcov : (⋃ i, A i) = Set.univ) (d : ℕ) {lam c : ℝ}
    (hlam : ∀ i, (∑ j, |b i j|) ≤ lam) (hc : ∀ i, |b0 i| ≤ c) (x : Fin (P + 1) → ℝ) :
    |tarStateDrift b0 b A d x| ≤ lam * (⨆ i, |x i|) + c := by
  classical
  have hmem : x ⟨min (d - 1) P, by omega⟩ ∈ ⋃ i, A i := by rw [hcov]; exact Set.mem_univ _
  obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hmem
  have hval : tarStateDrift b0 b A d x = b0 i0 + ∑ j : Fin P, b i0 j * x (j.castSucc) :=
    sum_indicator_of_partition hdisj hi0 _
  have hxb : ∀ j : Fin (P + 1), |x j| ≤ ⨆ i, |x i| := fun j =>
    le_ciSup (f := fun i : Fin (P + 1) => |x i|) (Finite.bddAbove_range _) j
  have hsup0 : (0 : ℝ) ≤ ⨆ i, |x i| := le_trans (abs_nonneg (x 0)) (hxb 0)
  have hstep : |∑ j : Fin P, b i0 j * x (j.castSucc)| ≤ (∑ j, |b i0 j|) * (⨆ i, |x i|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hxb _) (abs_nonneg _)
  have hmain : |b0 i0 + ∑ j : Fin P, b i0 j * x (j.castSucc)|
      ≤ c + (∑ j, |b i0 j|) * (⨆ i, |x i|) :=
    le_trans (abs_add_le _ _) (add_le_add (hc i0) hstep)
  have hlast : (∑ j, |b i0 j|) * (⨆ i, |x i|) ≤ lam * (⨆ i, |x i|) :=
    mul_le_mul_of_nonneg_right (hlam i0) hsup0
  rw [hval]
  linarith

/-- The nonlinear-AR kernel as a pushforward of the innovation law. -/
private lemma nlARKernel_apply {P : ℕ} {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : Fin (P + 1) → ℝ) :
    nlARKernel f ν x
      = ν.map (fun e => (Fin.cons (f x + e) (fun i => x i.castSucc) : Fin (P + 1) → ℝ)) := by
  have hmeas : Measurable fun xe : (Fin (P + 1) → ℝ) × ℝ =>
      (Fin.cons (f xe.1 + xe.2) (fun i => xe.1 i.castSucc) : Fin (P + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using! (hf.comp measurable_fst).add measurable_snd
    · exact fun i => by simpa using! (measurable_pi_apply i.castSucc).comp measurable_fst
  rw [nlARKernel, Kernel.map_apply _ hmeas, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hmeas measurable_prodMk_left]
  rfl

private lemma compProd_map_left' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ] {g : α → β} (hg : Measurable g)
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (μ.map g) ⊗ₘ η = (μ ⊗ₘ (η.comap g hg)).map (Prod.map g id) := by
  have hmap : Measurable (Prod.map g (id : γ → γ)) := hg.prodMap measurable_id
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hmap hs,
    Measure.compProd_apply (hs.preimage hmap),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hg]
  rfl

/-! ### The innovation-coordinate window law

Both independence clauses of `exists_stationary_nlAR_of_invariant` below reduce to one
identity: read in the **innovation coordinates** `e_i = w_{i+1}(0) − f(w_i)`, the window law
`chainWindowLaw (nlARKernel f ν) F k` of the vectorized nonlinear-AR chain is the plain
`k`-fold product `ν^{⊗k}` (`chainWindowLaw_map_innov`), and the one-step refinement
`chainWindowLaw_map_init_innov` additionally records that the *last* innovation is
independent of the whole preceding window. -/

/-- `Fin.snoc` carries `ν^{⊗n} ⊗ ν` to `ν^{⊗(n+1)}`. -/
private lemma map_snoc_prod_pi (n : ℕ) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ((Measure.pi fun _ : Fin n => ν).prod ν).map
        (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ))
      = Measure.pi (fun _ : Fin (n + 1) => ν) := by
  have hsnoc : Measurable fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.lastCases ?_ ?_
    · simpa using measurable_snd
    · exact fun i => by simpa using! (measurable_pi_apply i).comp measurable_fst
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hsnoc (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) ⁻¹'
      (Set.univ.pi s) = (Set.univ.pi fun i : Fin n => s i.castSucc) ×ˢ s (Fin.last n) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_prod]
    constructor
    · exact fun h => ⟨fun i => by simpa using h i.castSucc, by simpa using h (Fin.last n)⟩
    · rintro ⟨h1, h2⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using h2
      · simpa using h1 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  exact (Fin.prod_univ_castSucc fun i => ν (s i)).symm

/-- **One `nlARKernel` step in innovation coordinates.** Conditionally on the current state
`g a`, the increment `y 0 − f (g a)` is a fresh `ν`-draw, so the joint law of the state and
the increment is the product `μ ⊗ ν`. -/
private lemma nlAR_compProd_innov {α : Type*} [MeasurableSpace α] {P : ℕ}
    {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (μ : Measure α) [IsProbabilityMeasure μ] {g : α → (Fin (P + 1) → ℝ)} (hg : Measurable g) :
    (μ ⊗ₘ ((nlARKernel f ν).comap g hg)).map (fun p => (p.1, p.2 0 - f (g p.1)))
      = μ.prod ν := by
  haveI := isMarkovKernel_nlARKernel hf ν
  have hΦ : Measurable fun p : α × (Fin (P + 1) → ℝ) => (p.1, p.2 0 - f (g p.1)) :=
    measurable_fst.prodMk (((measurable_pi_apply 0).comp measurable_snd).sub
      (hf.comp (hg.comp measurable_fst)))
  ext s hs
  rw [Measure.map_apply hΦ hs, Measure.compProd_apply (hΦ hs), Measure.prod_apply hs]
  refine lintegral_congr fun a => ?_
  have hmc : Measurable fun e : ℝ =>
      (Fin.cons (f (g a) + e) (fun i => (g a) i.castSucc) : Fin (P + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using! measurable_const.add measurable_id
    · exact fun i => by simp
  rw [Kernel.comap_apply, nlARKernel_apply hf ν (g a),
    Measure.map_apply hmc (measurable_prodMk_left (hΦ hs))]
  congr 1
  ext e
  simp only [Set.mem_preimage, Fin.cons_zero, add_sub_cancel_left]

/-- **One-step innovation split of the window law.** Peeling the last coordinate off a
`nlARKernel` window law leaves the shorter window law together with an *independent*
`ν`-distributed innovation. -/
private lemma chainWindowLaw_map_init_innov {P : ℕ} {f : (Fin (P + 1) → ℝ) → ℝ}
    (hf : Measurable f) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (F : Measure (Fin (P + 1) → ℝ)) [IsProbabilityMeasure F] (k : ℕ) :
    (chainWindowLaw (nlARKernel f ν) F (k + 1)).map
        (fun w : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ) =>
          (Fin.init w, w (Fin.last (k + 1)) 0 - f (w (Fin.last k).castSucc)))
      = (chainWindowLaw (nlARKernel f ν) F k).prod ν := by
  haveI := isMarkovKernel_nlARKernel hf ν
  haveI := isProbabilityMeasure_chainWindowLaw (nlARKernel f ν) F k
  have hsnoc : Measurable fun wx : (Fin (k + 1) → (Fin (P + 1) → ℝ)) × (Fin (P + 1) → ℝ) =>
      (Fin.snoc wx.1 wx.2 : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ)) := by
    rw [measurable_pi_iff]
    refine Fin.lastCases ?_ ?_
    · simpa using measurable_snd
    · exact fun i => by simpa using! (measurable_pi_apply i).comp measurable_fst
  have hΘ : Measurable fun w : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ) =>
      (Fin.init w, w (Fin.last (k + 1)) 0 - f (w (Fin.last k).castSucc)) :=
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk
      (((measurable_pi_apply 0).comp (measurable_pi_apply _)).fun_sub
        (hf.comp (measurable_pi_apply _)))
  have hstep : chainWindowLaw (nlARKernel f ν) F (k + 1)
      = ((chainWindowLaw (nlARKernel f ν) F k) ⊗ₘ
          ((nlARKernel f ν).comap (fun w : Fin (k + 1) → (Fin (P + 1) → ℝ) => w (Fin.last k))
            (measurable_pi_apply _))).map
        (fun wx => (Fin.snoc wx.1 wx.2 : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ))) := rfl
  rw [hstep, Measure.map_map hΘ hsnoc]
  have hfac : ((fun w : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ) =>
        (Fin.init w, w (Fin.last (k + 1)) 0 - f (w (Fin.last k).castSucc))) ∘
      (fun wx : (Fin (k + 1) → (Fin (P + 1) → ℝ)) × (Fin (P + 1) → ℝ) =>
        (Fin.snoc wx.1 wx.2 : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ))))
      = fun wx => (wx.1, wx.2 0 - f (wx.1 (Fin.last k))) := by
    funext wx
    simp
  rw [hfac]
  exact nlAR_compProd_innov hf (chainWindowLaw (nlARKernel f ν) F k)
    (g := fun w : Fin (k + 1) → (Fin (P + 1) → ℝ) => w (Fin.last k))
    (measurable_pi_apply (Fin.last k))

/-- **The innovation-coordinate window law.** In the coordinates
`e_i = w_{i+1}(0) − f(w_i)` the `nlARKernel` window law is the `k`-fold product `ν^{⊗k}`:
the innovations of a stationary window are i.i.d. `ν`. -/
private lemma chainWindowLaw_map_innov {P : ℕ} {f : (Fin (P + 1) → ℝ) → ℝ}
    (hf : Measurable f) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (F : Measure (Fin (P + 1) → ℝ)) [IsProbabilityMeasure F] (k : ℕ) :
    (chainWindowLaw (nlARKernel f ν) F k).map
        (fun w (i : Fin k) => w i.succ 0 - f (w i.castSucc))
      = Measure.pi (fun _ : Fin k => ν) := by
  haveI := isMarkovKernel_nlARKernel hf ν
  induction k with
  | zero =>
    haveI := isProbabilityMeasure_chainWindowLaw (nlARKernel f ν) F 0
    have hconst : (fun (w : Fin 1 → (Fin (P + 1) → ℝ)) (i : Fin 0) =>
        w i.succ 0 - f (w i.castSucc)) = fun _ => (fun i : Fin 0 => (0 : ℝ)) := by
      funext w
      funext i
      exact i.elim0
    rw [hconst, Measure.map_const, measure_univ, one_smul,
      Measure.pi_of_empty (fun _ : Fin 0 => ν) (fun _ : Fin 0 => (0 : ℝ))]
  | succ k ih =>
    haveI := isProbabilityMeasure_chainWindowLaw (nlARKernel f ν) F k
    have hinnovk : Measurable fun w : Fin (k + 1) → (Fin (P + 1) → ℝ) =>
        fun i : Fin k => w i.succ 0 - f (w i.castSucc) :=
      measurable_pi_lambda _ fun _ =>
        ((measurable_pi_apply 0).comp (measurable_pi_apply _)).fun_sub
          (hf.comp (measurable_pi_apply _))
    have hΘ : Measurable fun w : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ) =>
        (Fin.init w, w (Fin.last (k + 1)) 0 - f (w (Fin.last k).castSucc)) :=
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk
        (((measurable_pi_apply 0).comp (measurable_pi_apply _)).fun_sub
          (hf.comp (measurable_pi_apply _)))
    have hsnocR : Measurable fun q : (Fin k → ℝ) × ℝ =>
        (Fin.snoc q.1 q.2 : Fin (k + 1) → ℝ) := by
      rw [measurable_pi_iff]
      refine Fin.lastCases ?_ ?_
      · simpa using measurable_snd
      · exact fun i => by simpa using! (measurable_pi_apply i).comp measurable_fst
    have hfac : (fun (w : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ)) (i : Fin (k + 1)) =>
          w i.succ 0 - f (w i.castSucc))
        = ((fun q : (Fin k → ℝ) × ℝ => (Fin.snoc q.1 q.2 : Fin (k + 1) → ℝ)) ∘
            (Prod.map (fun w : Fin (k + 1) → (Fin (P + 1) → ℝ) =>
              fun i : Fin k => w i.succ 0 - f (w i.castSucc)) id)) ∘
          (fun w : Fin (k + 1 + 1) → (Fin (P + 1) → ℝ) =>
            (Fin.init w, w (Fin.last (k + 1)) 0 - f (w (Fin.last k).castSucc))) := by
      funext w
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp only [Function.comp_apply, Prod.map_apply, id_eq, Fin.snoc_castSucc, Fin.init]
        rw [Fin.succ_castSucc]
    rw [hfac, ← Measure.map_map (hsnocR.comp (hinnovk.prodMap measurable_id)) hΘ,
      chainWindowLaw_map_init_innov hf F k,
      ← Measure.map_map hsnocR (hinnovk.prodMap measurable_id),
      ← Measure.map_prod_map _ _ hinnovk measurable_id, Measure.map_id, ih]
    exact map_snoc_prod_pi k ν

/-- The set of state pairs `(x, y)` in which `y` is `x` shifted by one coordinate. -/
private def shiftSet (P : ℕ) : Set ((Fin (P + 1) → ℝ) × (Fin (P + 1) → ℝ)) :=
  {p | ∀ j : Fin P, p.2 j.succ = p.1 j.castSucc}

private lemma measurableSet_shiftSet (P : ℕ) : MeasurableSet (shiftSet P) := by
  have h : shiftSet P = ⋂ j : Fin P, {p : (Fin (P + 1) → ℝ) × (Fin (P + 1) → ℝ) |
      p.2 j.succ = p.1 j.castSucc} := by
    ext p; simp [shiftSet]
  rw [h]
  refine MeasurableSet.iInter fun j => ?_
  exact measurableSet_eq_fun ((measurable_pi_apply _).comp measurable_snd)
    ((measurable_pi_apply _).comp measurable_fst)

/-- The one-step shift structure of the nonlinear-AR kernel, as a null set. -/
private lemma nlAR_pair_shift {P : ℕ} {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (F : Measure (Fin (P + 1) → ℝ))
    [IsProbabilityMeasure F] :
    (F ⊗ₘ nlARKernel f ν) (shiftSet P)ᶜ = 0 := by
  haveI := isMarkovKernel_nlARKernel hf ν
  have hA : MeasurableSet (shiftSet P) := measurableSet_shiftSet P
  rw [Measure.compProd_apply hA.compl]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards with x
  have hm : Measurable fun e : ℝ =>
      (Fin.cons (f x + e) (fun i => x i.castSucc) : Fin (P + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using! measurable_const.add measurable_id
    · exact fun i => by simp
  rw [nlARKernel_apply hf ν x,
    Measure.map_apply hm (measurable_prodMk_left hA.compl)]
  convert! measure_empty (μ := ν)
  ext e
  simp only [Set.mem_preimage, Set.mem_compl_iff, shiftSet, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_not]
  intro j
  simp

/-- The two-coordinate window law is the one-step pair law. -/
private lemma chainWindowLaw_one {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π] :
    (chainWindowLaw κ π 1).map (fun w : Fin 2 → S => (w 0, w 1)) = π ⊗ₘ κ := by
  have hc : Measurable (fun (x : S) (_ : Fin 1) => x) :=
    measurable_pi_lambda _ fun _ => measurable_id
  have hsnoc : Measurable fun wx : (Fin 1 → S) × S => (Fin.snoc wx.1 wx.2 : Fin 2 → S) := by
    rw [measurable_pi_iff]
    refine Fin.lastCases ?_ ?_
    · simpa using! measurable_snd
    · exact fun i => by simpa using! (measurable_pi_apply i).comp measurable_fst
  have hsel : Measurable fun w : Fin 2 → S => (w 0, w 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hstep : chainWindowLaw κ π 1
      = ((π.map (fun (x : S) (_ : Fin 1) => x)) ⊗ₘ
          (κ.comap (fun w : Fin 1 → S => w (Fin.last 0)) (measurable_pi_apply _))).map
        (fun wx => (Fin.snoc wx.1 wx.2 : Fin 2 → S)) := rfl
  rw [hstep, compProd_map_left' _ hc,
    Measure.map_map hsnoc (hc.prodMap measurable_id),
    Measure.map_map hsel ((hsnoc.comp (hc.prodMap measurable_id)))]
  have hid : ((fun w : Fin 2 → S => (w 0, w 1)) ∘
      ((fun wx : (Fin 1 → S) × S => (Fin.snoc wx.1 wx.2 : Fin 2 → S)) ∘
        Prod.map (fun (x : S) (_ : Fin 1) => x) id)) = id := by
    funext p
    simp [Fin.snoc]
  rw [hid, Measure.map_id]
  rfl

/-- **Kernel → two-sided process.** From an invariant law of the vectorized nonlinear-AR
kernel, a two-sided strictly stationary realization of the recursion driven by
standardized iid innovations.

The path space is now available: `ForMathlib/Markov/Markov/TwoSidedChain.lean`'s
`exists_twoSided_stationary_chain` (PROVED, axiom-clean) builds the two-sided stationary
chain by the *natural extension* — the time-reversed kernel obtained by disintegration
plus two Ionescu–Tulcea trajectories glued at the shared time-`0` value — so no
Kolmogorov extension over `ℤ` is needed. Instantiating it at `κ = nlARKernel f ν`
supplies the process `X'_t = (Y_t)_0` and the innovations
`ε'_t = ((Y_t)_0 − f (Y_{t−1}))/σ₀`, and the window-law family gives, below:

* the state vector is the past of its own first coordinate (`hcons`), hence the
  **recursion** clause;
* **strict stationarity**, through `isStrictlyStationary_iff_window`.

The two *independence* clauses come from the **innovation-coordinate window law**
`chainWindowLaw_map_innov` above: read in the coordinates `e_i = w_{i+1}(0) − f(w_i)`, the
window law is the plain product `ν^{⊗k}`. From it:

* `IsIIDNoise ε' 1 μ'` — every finite set of times embeds injectively into a consecutive
  window (`iIndepFun_iff_finset` + `iIndepFun.precomp`), on which the innovations are the
  coordinates of a `Measure.pi`; the moment clauses follow from `IdentDistrib` against `ν`
  itself, so the variance is `σ₀²/σ₀² = 1` by `hνvar`;
* independence of `ε'_t` from `sigmaLT X' t` — `ε'_t` is independent of every finite past
  window (the one-step refinement `chainWindowLaw_map_init_innov`), and those windows form
  a *monotone* `ℕ`-indexed family whose `⨆` dominates `sigmaLT X' t`, so
  `indep_iSup_of_monotone` lifts it; no π-system/monotone-class step is needed. -/
private theorem exists_stationary_nlAR_of_invariant {P : ℕ}
    {f : (Fin (P + 1) → ℝ) → ℝ} (hf : Measurable f)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν2 : MemLp id 2 ν) (hνmean : ∫ e, e ∂ν = 0)
    {σ0 : ℝ} (hσ : 0 < σ0) (hνvar : variance id ν = σ0 ^ 2)
    {F : Measure (Fin (P + 1) → ℝ)} [IsProbabilityMeasure F]
    (hinv : (nlARKernel f ν).Invariant F) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsIIDNoise ε' 1 μ' ∧
        (∀ t : ℤ, Indep (MeasurableSpace.comap (ε' t) inferInstance) (sigmaLT X' t) μ') ∧
        (∀ t : ℤ, X' t =ᵐ[μ']
          fun ω => f (fun j : Fin (P + 1) => X' (t - 1 - (j : ℕ)) ω) + σ0 * ε' t ω) ∧
        IsStrictlyStationary X' μ' := by
  haveI := isMarkovKernel_nlARKernel hf ν
  obtain ⟨Ω', mΩ', μ', Y, hprob, hYmeas, hwin⟩ :=
    exists_twoSided_stationary_chain (nlARKernel f ν) F hinv
  have hX'meas : ∀ t : ℤ, Measurable fun ω => Y t ω 0 :=
    fun t => (measurable_pi_apply 0).comp (hYmeas t)
  -- the one-step pair law
  have hsel : Measurable fun w : Fin 2 → (Fin (P + 1) → ℝ) => (w 0, w 1) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hpair : ∀ t : ℤ, μ'.map (fun ω => (Y (t - 1) ω, Y t ω)) = F ⊗ₘ nlARKernel f ν := by
    intro t
    have hbig : Measurable fun ω (i : Fin 2) => Y (t - 1 + (i : ℕ)) ω :=
      measurable_pi_lambda _ fun _ => hYmeas _
    have h2 := congrArg
      (fun μ => Measure.map (fun w : Fin 2 → (Fin (P + 1) → ℝ) => (w 0, w 1)) μ)
      (hwin (t - 1) 1)
    rw [Measure.map_map hsel hbig, chainWindowLaw_one] at h2
    rw [← h2]
    congr 1
    funext ω
    simp
  -- one-step coordinate shift, almost surely
  have hshift : ∀ t : ℤ, ∀ᵐ ω ∂μ', ∀ j : Fin P,
      Y t ω j.succ = Y (t - 1) ω j.castSucc := by
    intro t
    have hpm : Measurable fun ω => (Y (t - 1) ω, Y t ω) := (hYmeas _).prodMk (hYmeas _)
    have hnull := nlAR_pair_shift (ν := ν) hf F
    rw [← hpair t, Measure.map_apply hpm (measurableSet_shiftSet P).compl] at hnull
    have hae : ∀ᵐ ω ∂μ', (Y (t - 1) ω, Y t ω) ∈ shiftSet P := by
      rw [ae_iff]; exact hnull
    filter_upwards [hae] with ω hω
    simpa [shiftSet] using hω
  have hshiftAll : ∀ᵐ ω ∂μ', ∀ (t : ℤ) (j : Fin P),
      Y t ω j.succ = Y (t - 1) ω j.castSucc := ae_all_iff.mpr hshift
  -- the state vector is the past of its own first coordinate
  have hcons : ∀ᵐ ω ∂μ', ∀ (t : ℤ) (j : Fin (P + 1)), Y t ω j = Y (t - (j : ℕ)) ω 0 := by
    filter_upwards [hshiftAll] with ω hω
    have key : ∀ (j : ℕ) (hj : j < P + 1) (t : ℤ),
        Y t ω ⟨j, hj⟩ = Y (t - (j : ℤ)) ω 0 := by
      intro j
      induction j with
      | zero => intro hj t; simp
      | succ j ih =>
        intro hj t
        have hjP : j < P := by omega
        have h1 : (⟨j + 1, hj⟩ : Fin (P + 1)) = (⟨j, hjP⟩ : Fin P).succ := by
          apply Fin.ext; simp
        have h2 : ((⟨j, hjP⟩ : Fin P).castSucc : Fin (P + 1)) = ⟨j, by omega⟩ := by
          apply Fin.ext; simp
        rw [h1, hω t ⟨j, hjP⟩, h2, ih (by omega) (t - 1)]
        congr 1
        push_cast
        ring
    intro t j
    have := key (j : ℕ) j.isLt t
    simpa using this
  -- ### the innovations
  haveI := hprob
  have hσ0 : σ0 ≠ 0 := ne_of_gt hσ
  have hZmeas : ∀ t : ℤ, Measurable fun ω => Y t ω 0 - f (Y (t - 1) ω) :=
    fun t => (hX'meas t).sub (hf.comp (hYmeas _))
  have hεmeas : ∀ t : ℤ, Measurable fun ω => (Y t ω 0 - f (Y (t - 1) ω)) / σ0 :=
    fun t => (hZmeas t).div_const σ0
  have hdivmeas : Measurable fun e : ℝ => e / σ0 := measurable_id.div_const σ0
  -- consecutive innovations are i.i.d. `ν`: the innovation-coordinate window law
  have hinnovwin : ∀ (a : ℤ) (k : ℕ),
      μ'.map (fun ω (i : Fin k) => Y (a + (i : ℕ)) ω 0 - f (Y (a + (i : ℕ) - 1) ω))
        = Measure.pi (fun _ : Fin k => ν) := by
    intro a k
    have hbig : Measurable fun ω (i : Fin (k + 1)) => Y (a - 1 + (i : ℕ)) ω :=
      measurable_pi_lambda _ fun _ => hYmeas _
    have hinnov : Measurable fun w : Fin (k + 1) → (Fin (P + 1) → ℝ) =>
        fun i : Fin k => w i.succ 0 - f (w i.castSucc) :=
      measurable_pi_lambda _ fun _ =>
        ((measurable_pi_apply 0).comp (measurable_pi_apply _)).fun_sub
          (hf.comp (measurable_pi_apply _))
    have h2 := congrArg (fun mm => Measure.map (fun w : Fin (k + 1) → (Fin (P + 1) → ℝ) =>
      fun i : Fin k => w i.succ 0 - f (w i.castSucc)) mm) (hwin (a - 1) k)
    rw [Measure.map_map hinnov hbig, chainWindowLaw_map_innov hf F k] at h2
    rw [← h2]
    congr 1
    funext ω
    funext i
    have h3 : a - 1 + (((i.succ : Fin (k + 1)) : ℕ) : ℤ) = a + ((i : ℕ) : ℤ) := by
      simp only [Fin.val_succ]
      push_cast
      ring
    have h4 : a - 1 + (((i.castSucc : Fin (k + 1)) : ℕ) : ℤ) = a + ((i : ℕ) : ℤ) - 1 := by
      simp only [Fin.val_castSucc]
      ring
    simp only [Function.comp_apply]
    rw [h3, h4]
  -- the law of a single innovation
  have hZlaw : ∀ t : ℤ, μ'.map (fun ω => Y t ω 0 - f (Y (t - 1) ω)) = ν := by
    intro t
    have hwin1 : Measurable fun ω (i : Fin 1) =>
        Y (t + (i : ℕ)) ω 0 - f (Y (t + (i : ℕ) - 1) ω) :=
      measurable_pi_lambda _ fun _ => hZmeas _
    have hev : ((Measure.pi fun _ : Fin 1 => ν).map fun v : Fin 1 → ℝ => v 0) = ν :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin 1 => ν) 0).map_eq
    have h2 := congrArg (fun mm : Measure (Fin 1 → ℝ) => mm.map fun v : Fin 1 → ℝ => v 0)
      (hinnovwin t 1)
    rw [Measure.map_map (measurable_pi_apply 0) hwin1, hev] at h2
    rw [← h2]
    congr 1
    funext ω
    simp
  have hεlaw : ∀ t : ℤ, μ'.map (fun ω => (Y t ω 0 - f (Y (t - 1) ω)) / σ0)
      = ν.map (fun e : ℝ => e / σ0) := by
    intro t
    rw [← hZlaw t, Measure.map_map hdivmeas (hZmeas t)]
    rfl
  -- the innovation at time `0` is distributed as `ν` itself
  have hidZ : IdentDistrib (fun ω => Y 0 ω 0 - f (Y ((0 : ℤ) - 1) ω)) (id : ℝ → ℝ) μ' ν :=
    ⟨(hZmeas 0).aemeasurable, aemeasurable_id, by rw [Measure.map_id]; exact hZlaw 0⟩
  have hmemZ : MemLp (fun ω => Y 0 ω 0 - f (Y ((0 : ℤ) - 1) ω)) 2 μ' :=
    hidZ.symm.memLp_snd hν2
  have hmemLp : MemLp (fun ω => (Y 0 ω 0 - f (Y ((0 : ℤ) - 1) ω)) / σ0) 2 μ' := by
    simpa [div_eq_inv_mul] using hmemZ.const_mul σ0⁻¹
  refine ⟨Ω', mΩ', μ', (fun t ω => Y t ω 0),
    (fun t ω => (Y t ω 0 - f (Y (t - 1) ω)) / σ0), hprob, hX'meas, ?_, ?_, ?_, ?_⟩
  · -- `IsIIDNoise ε' 1 μ'`
    refine ⟨hεmeas, ?_, fun s t => ⟨(hεmeas s).aemeasurable, (hεmeas t).aemeasurable,
      by rw [hεlaw s, hεlaw t]⟩, hmemLp, ?_, ?_⟩
    · -- mutual independence: every finite set of times sits in a consecutive window,
      -- on which the innovations are the coordinates of a product measure
      have hfin : ∀ (a : ℤ) (k : ℕ), iIndepFun
          (fun (i : Fin k) (ω : Ω') =>
            (Y (a + (i : ℕ)) ω 0 - f (Y (a + (i : ℕ) - 1) ω)) / σ0) μ' := by
        intro a k
        have hbase : iIndepFun
            (fun (i : Fin k) (ω : Ω') =>
              Y (a + (i : ℕ)) ω 0 - f (Y (a + (i : ℕ) - 1) ω)) μ' := by
          rw [iIndepFun_iff_map_fun_eq_pi_map
              fun i : Fin k => (hZmeas (a + ((i : ℕ) : ℤ))).aemeasurable,
            hinnovwin a k]
          exact congrArg Measure.pi (funext fun i : Fin k => (hZlaw (a + ((i : ℕ) : ℤ))).symm)
        exact hbase.comp (fun _ => fun e : ℝ => e / σ0) fun _ => hdivmeas
      rw [iIndepFun_iff_finset]
      intro s
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ∈ s, (i : ℤ).natAbs ≤ N :=
        ⟨s.sup Int.natAbs, fun i hi => Finset.le_sup hi⟩
      have hginj : Function.Injective (fun i : ↥s =>
          (⟨((i : ℤ) + (N : ℤ)).toNat, by have := hN i i.2; omega⟩ : Fin (2 * N + 1))) := by
        intro i j hij
        have h0 : ((i : ℤ) + (N : ℤ)).toNat = ((j : ℤ) + (N : ℤ)).toNat := congrArg Fin.val hij
        have h1 := hN i i.2
        have h2 := hN j j.2
        exact Subtype.ext (by omega)
      have hres := (hfin (-(N : ℤ)) (2 * N + 1)).precomp hginj
      have heq : (fun (i : ↥s) (ω : Ω') =>
            (Y (-(N : ℤ) + ((((i : ℤ) + (N : ℤ)).toNat : ℕ) : ℤ)) ω 0
              - f (Y (-(N : ℤ) + ((((i : ℤ) + (N : ℤ)).toNat : ℕ) : ℤ) - 1) ω)) / σ0)
          = fun (i : ↥s) (ω : Ω') => (Y (i : ℤ) ω 0 - f (Y ((i : ℤ) - 1) ω)) / σ0 := by
        funext i
        funext ω
        have h1 := hN i i.2
        have hi : -(N : ℤ) + ((((i : ℤ) + (N : ℤ)).toNat : ℕ) : ℤ) = (i : ℤ) := by omega
        rw [hi]
      show iIndepFun (fun (i : ↥s) (ω : Ω') =>
        (Y (i : ℤ) ω 0 - f (Y ((i : ℤ) - 1) ω)) / σ0) μ'
      rw [← heq]
      exact hres
    · -- mean zero
      rw [integral_div, hidZ.integral_eq]
      simp only [id_eq]
      rw [hνmean, zero_div]
    · -- variance one
      have h1 : (fun ω => (Y 0 ω 0 - f (Y ((0 : ℤ) - 1) ω)) / σ0)
          = fun ω => σ0⁻¹ * (Y 0 ω 0 - f (Y ((0 : ℤ) - 1) ω)) :=
        funext fun ω => div_eq_inv_mul _ _
      rw [h1, variance_const_mul, hidZ.variance_eq, hνvar]
      field_simp
  · -- `Indep (comap (ε' t)) (sigmaLT X' t) μ'`: `ε'_t` is independent of every finite past
    -- window of `Y`, and those windows generate an increasing family whose `⨆` dominates
    -- `sigmaLT X' t`
    intro t
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ → MeasurableSpace Ω', ∀ j : ℕ,
        m j = MeasurableSpace.comap
          (fun ω (i : Fin (j + 1)) => Y (t - 1 - (j : ℤ) + (i : ℕ)) ω) inferInstance :=
      ⟨_, fun _ => rfl⟩
    have hWmeas : ∀ j : ℕ,
        Measurable fun ω (i : Fin (j + 1)) => Y (t - 1 - (j : ℤ) + (i : ℕ)) ω :=
      fun j => measurable_pi_lambda _ fun _ => hYmeas _
    have hmle : ∀ j : ℕ, m j ≤ mΩ' := fun j => by
      rw [hmdef j]; exact (hWmeas j).comap_le
    have hmono : Monotone m := by
      refine monotone_nat_of_le_succ fun j => ?_
      have hφ : Measurable fun w : Fin (j + 1 + 1) → (Fin (P + 1) → ℝ) =>
          fun i : Fin (j + 1) => w i.succ :=
        measurable_pi_lambda _ fun _ => measurable_pi_apply _
      have hcomp : (fun ω (i : Fin (j + 1)) => Y (t - 1 - (j : ℤ) + (i : ℕ)) ω)
          = (fun w : Fin (j + 1 + 1) → (Fin (P + 1) → ℝ) =>
              fun i : Fin (j + 1) => w i.succ) ∘
            (fun ω (i : Fin (j + 1 + 1)) =>
              Y (t - 1 - ((j + 1 : ℕ) : ℤ) + (i : ℕ)) ω) := by
        funext ω
        funext i
        simp only [Function.comp_apply, Fin.val_succ]
        congr 1
        push_cast
        ring
      rw [hmdef j, hmdef (j + 1), hcomp, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hφ.comap_le
    -- the strict past of `X'` sits inside the window family
    have hsig : sigmaLT (fun s (ω : Ω') => Y s ω 0) t ≤ ⨆ j : ℕ, m j := by
      refine iSup₂_le fun s hs => ?_
      have hslt : s < t := hs
      obtain ⟨j, hj⟩ : ∃ j : ℕ, t - 1 - (j : ℤ) = s := ⟨(t - 1 - s).toNat, by omega⟩
      show MeasurableSpace.comap (fun ω : Ω' => Y s ω 0) inferInstance ≤ ⨆ j : ℕ, m j
      refine le_trans ?_ (le_iSup m j)
      have hcomp : (fun ω : Ω' => Y s ω 0)
          = (fun w : Fin (j + 1) → (Fin (P + 1) → ℝ) => w 0 0) ∘
            (fun ω (i : Fin (j + 1)) => Y (t - 1 - (j : ℤ) + (i : ℕ)) ω) := by
        funext ω
        simp only [Function.comp_apply, Fin.val_zero, Nat.cast_zero, add_zero, hj]
      have hev : Measurable fun w : Fin (j + 1) → (Fin (P + 1) → ℝ) => w 0 0 :=
        (measurable_pi_apply (0 : Fin (P + 1))).comp (measurable_pi_apply (0 : Fin (j + 1)))
      rw [hmdef j, hcomp, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hev.comap_le
    -- `ε'_t` is independent of each window
    have hindepj : ∀ j : ℕ, Indep (m j)
        (MeasurableSpace.comap
          (fun ω : Ω' => (Y t ω 0 - f (Y (t - 1) ω)) / σ0) inferInstance) μ' := by
      intro j
      have hVmeas : Measurable fun ω (i : Fin (j + 1 + 1)) =>
          Y (t - 1 - (j : ℤ) + (i : ℕ)) ω :=
        measurable_pi_lambda _ fun _ => hYmeas _
      have hΘ : Measurable fun w : Fin (j + 1 + 1) → (Fin (P + 1) → ℝ) =>
          (Fin.init w, w (Fin.last (j + 1)) 0 - f (w (Fin.last j).castSucc)) :=
        (measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk
          (((measurable_pi_apply 0).comp (measurable_pi_apply _)).fun_sub
            (hf.comp (measurable_pi_apply _)))
      have hjoint : μ'.map (fun ω : Ω' =>
            ((fun i : Fin (j + 1) => Y (t - 1 - (j : ℤ) + (i : ℕ)) ω),
              Y t ω 0 - f (Y (t - 1) ω)))
          = (chainWindowLaw (nlARKernel f ν) F j).prod ν := by
        have h2 := congrArg (fun mm =>
          Measure.map (fun w : Fin (j + 1 + 1) → (Fin (P + 1) → ℝ) =>
            (Fin.init w, w (Fin.last (j + 1)) 0 - f (w (Fin.last j).castSucc))) mm)
          (hwin (t - 1 - (j : ℤ)) (j + 1))
        rw [Measure.map_map hΘ hVmeas, chainWindowLaw_map_init_innov hf F j] at h2
        rw [← h2]
        congr 1
        funext ω
        simp only [Function.comp_apply, Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · funext i
          simp only [Fin.init, Fin.val_castSucc]
        · have ha : t - 1 - (j : ℤ)
              + (((Fin.last (j + 1) : Fin (j + 1 + 1)) : ℕ) : ℤ) = t := by
            simp only [Fin.val_last]
            push_cast
            ring
          have hb : t - 1 - (j : ℤ)
              + ((((Fin.last j).castSucc : Fin (j + 1 + 1)) : ℕ) : ℤ) = t - 1 := by
            simp only [Fin.val_castSucc, Fin.val_last]
            ring
          rw [ha, hb]
      have hindepfun : IndepFun
          (fun ω : Ω' => fun i : Fin (j + 1) => Y (t - 1 - (j : ℤ) + (i : ℕ)) ω)
          (fun ω : Ω' => Y t ω 0 - f (Y (t - 1) ω)) μ' :=
        (indepFun_iff_map_prod_eq_prod_map_map (hWmeas j).aemeasurable
          (hZmeas t).aemeasurable).mpr (by
            rw [hwin (t - 1 - (j : ℤ)) j, hZlaw t]
            exact hjoint)
      rw [hmdef j]
      exact hindepfun.comp measurable_id hdivmeas
    have hbig : Indep (⨆ j : ℕ, m j)
        (MeasurableSpace.comap
          (fun ω : Ω' => (Y t ω 0 - f (Y (t - 1) ω)) / σ0) inferInstance) μ' :=
      indep_iSup_of_monotone hindepj hmle (hεmeas t).comap_le hmono
    exact (indep_of_indep_of_le_left hbig hsig).symm
  · -- the recursion
    intro t
    filter_upwards [hcons] with ω hω
    have hv : (fun j : Fin (P + 1) => Y (t - 1 - (j : ℕ)) ω 0) = Y (t - 1) ω := by
      funext j
      have := hω (t - 1) j
      rw [← this]
    simp only [hv]
    field_simp
    ring
  · -- strict stationarity
    rw [isStrictlyStationary_iff_window hX'meas]
    intro n k
    cases n with
    | zero =>
      congr 1
      funext ω i
      exact i.elim0
    | succ n =>
      have hsel2 : Measurable fun w : Fin (n + 1) → (Fin (P + 1) → ℝ) =>
          fun i : Fin (n + 1) => w i 0 :=
        measurable_pi_lambda _ fun _ => (measurable_pi_apply 0).comp (measurable_pi_apply _)
      have hstep : ∀ c : ℤ,
          (μ'.map fun ω (i : Fin (n + 1)) => Y ((i : ℕ) + 1 + c) ω 0)
            = (chainWindowLaw (nlARKernel f ν) F n).map
              (fun w : Fin (n + 1) → (Fin (P + 1) → ℝ) => fun i : Fin (n + 1) => w i 0) := by
        intro c
        have hbig : Measurable fun ω (i : Fin (n + 1)) => Y (1 + c + (i : ℕ)) ω :=
          measurable_pi_lambda _ fun _ => hYmeas _
        have h2 := congrArg
          (fun μ => Measure.map (fun w : Fin (n + 1) → (Fin (P + 1) → ℝ) =>
            fun i : Fin (n + 1) => w i 0) μ) (hwin (1 + c) n)
        rw [Measure.map_map hsel2 hbig] at h2
        rw [← h2]
        congr 1
        funext ω
        funext i
        change Y (((i : ℕ) : ℤ) + 1 + c) ω 0 = Y (1 + c + ((i : ℕ) : ℤ)) ω 0
        rw [show ((i : ℕ) : ℤ) + 1 + c = 1 + c + ((i : ℕ) : ℤ) from by ring]
      rw [hstep k, ← hstep 0]
      congr 1

/-- **FY §4.1.1, pp. 126–127 (delegated to Theorem 2.4)**: under equal regime scales and
the uniform contraction `max_i Σ_j |b_{ij}| < 1`, the TAR state chain is geometrically
ergodic, hence admits a strictly stationary solution. Stated as a corollary of the
Markov-layer statement `nlARKernel_geometricallyErgodic` (FY Thm 2.4(ii)), which is
PROVED and axiom-clean. That theorem additionally requires the innovation density to be
**continuous** (a documented strengthening); the Gaussian law used here supplies it via
`continuous_gaussianPDF` above.

The innovation law fed to Theorem 2.4 is taken to be `N(0, σ₀²)` rather than the
hypothesis' `ν`: the conclusion asks for a TAR in the sense of `IsTAR`, whose innovations
are `IID(0, 1)` and enter as `σ₀ ε_t`, and `ν` is not assumed to have variance `σ₀²`
(only a positive continuous density, mean zero and a finite second moment — exactly the
Theorem 2.4 hypotheses). `N(0, σ₀²)` satisfies those same hypotheses, so the delegation
to Theorem 2.4 is unchanged. -/
theorem exists_stationary_tar [IsProbabilityMeasure μ] {k P : ℕ}
    {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ} {σ0 : ℝ} {A : Fin k → Set ℝ} {d : ℕ}
    -- USER-INPUT: measurable partition of ℝ; FY Def 4.1
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcov : (⋃ i, A i) = Set.univ)
    -- USER-INPUT: equal regime scales (book prints σ_p — typo for σ₁ = ⋯ = σ_k);
    -- FY p. 126 condition (a)
    (hσ : 0 < σ0)
    -- USER-INPUT: uniform contraction; FY p. 126 condition (b)
    (hcontract : ∀ i, (∑ j, |b i j|) < 1)
    -- USER-INPUT: delay within the state window; FY Def 4.1
    (hd : 1 ≤ d) (hdP : d ≤ P)
    -- USER-INPUT: innovation law with a continuous positive density (the Theorem 2.4
    -- hypothesis, in the strengthened form documented in
    -- `ForMathlib/Markov/GeometricErgodicity.lean`); FY §2.1.4 Example 2.1
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, 0 < g x) ∧
      ν = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν) (hνmean : ∫ x, x ∂ν = 0) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
        IsTAR b0 b (fun _ => σ0) A d X' ε' μ' ∧ IsStrictlyStationary X' μ' := by
  classical
  -- the partition is nonempty (it covers `ℝ`)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · have h0 : (0 : ℝ) ∈ ⋃ i : Fin 0, A i := by rw [hcov]; exact Set.mem_univ _
      simp at h0
    · exact h
  haveI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hkpos
  -- the uniform contraction rate and the intercept mass
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Finset.univ.sup' Finset.univ_nonempty
      fun i : Fin k => ∑ j, |b i j| := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ c : ℝ, c = Finset.univ.sup' Finset.univ_nonempty
      fun i : Fin k => |b0 i| := ⟨_, rfl⟩
  have hlamle : ∀ i, (∑ j, |b i j|) ≤ lam := fun i => by
    rw [hlam]
    exact Finset.le_sup' (fun i' : Fin k => ∑ j, |b i' j|) (Finset.mem_univ i)
  have hcstle : ∀ i, |b0 i| ≤ cst := fun i => by
    rw [hcst]
    exact Finset.le_sup' (fun i' : Fin k => |b0 i'|) (Finset.mem_univ i)
  have hlam1 : lam < 1 := by
    rw [hlam]; exact Finset.sup'_lt_iff _ |>.mpr fun i _ => hcontract i
  have hlam0 : 0 ≤ lam :=
    le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hlamle (Classical.arbitrary _))
  have hcst0 : 0 ≤ cst := le_trans (abs_nonneg _) (hcstle (Classical.arbitrary _))
  -- the innovation law: `N(0, σ₀²)`, which has a continuous positive density, mean zero
  -- and variance `σ₀²` (see the docstring on the choice)
  obtain ⟨v, hv⟩ : ∃ v : NNReal, v = Real.toNNReal (σ0 ^ 2) := ⟨_, rfl⟩
  have hvne : v ≠ 0 := by
    rw [hv]
    exact ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  have hvcoe : ((v : NNReal) : ℝ) = σ0 ^ 2 := by
    rw [hv]; exact Real.coe_toNNReal _ (by positivity)
  -- the geometric ergodicity input, from the frozen Theorem 2.4(ii)
  obtain ⟨F, hFprob, hFgeo⟩ :=
    nlARKernel_geometricallyErgodic (f := tarStateDrift b0 b A d)
      (measurable_tarStateDrift b0 b hA d)
      (g := ProbabilityTheory.gaussianPDF 0 v)
      (ProbabilityTheory.measurable_gaussianPDF 0 v)
      (continuous_gaussianPDF 0 v)
      (ProbabilityTheory.gaussianPDF_pos 0 hvne)
      (ν := ProbabilityTheory.gaussianReal 0 v)
      (ProbabilityTheory.gaussianReal_of_var_ne_zero 0 hvne)
      (MemLp.integrable le_rfl (ProbabilityTheory.memLp_id_gaussianReal 1))
      ProbabilityTheory.integral_id_gaussianReal
      hlam0 hlam1 hcst0
      (tarStateDrift_bound hdisj hcov d hlamle hcstle)
  haveI := hFprob
  haveI := isMarkovKernel_nlARKernel
    (measurable_tarStateDrift b0 b hA d) (ProbabilityTheory.gaussianReal 0 v)
  -- the attracting law is invariant, and the brick turns it into a two-sided process
  have hinv : (nlARKernel (tarStateDrift b0 b A d)
      (ProbabilityTheory.gaussianReal 0 v)).Invariant F :=
    hFgeo.isErgodicKernel.invariant
  obtain ⟨Ω', mΩ', μ', X', ε', hprob, hXmeas, hiid, hindep, hrec, hstat⟩ :=
    exists_stationary_nlAR_of_invariant (measurable_tarStateDrift b0 b hA d)
      (ProbabilityTheory.memLp_id_gaussianReal 2)
      ProbabilityTheory.integral_id_gaussianReal hσ
      (by rw [ProbabilityTheory.variance_id_gaussianReal, hvcoe]) hinv
  refine ⟨Ω', mΩ', μ', X', ε', hprob, ⟨hd, fun _ => hσ, hA, hdisj, hcov, hXmeas, hiid,
    hindep, fun t => ?_⟩, hstat⟩
  -- the recursion in state coordinates is eq. (4.1): the threshold coordinate `d − 1`
  -- of the state at time `t − 1` is `X_{t−d}`, and the shared noise term factors out of
  -- the partition indicator sum
  filter_upwards [hrec t] with ω hω
  rw [hω]
  have harg : t - 1 - ((min (d - 1) P : ℕ) : ℤ) = t - (d : ℤ) := by
    have h1 : min (d - 1) P = d - 1 := min_eq_left (by omega)
    rw [h1]
    have h2 : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by omega
    rw [h2]; ring
  have hthr : (fun j : Fin (P + 1) => X' (t - 1 - (j : ℕ)) ω) ⟨min (d - 1) P, by omega⟩
      = X' (t - (d : ℤ)) ω := by
    simp only []
    rw [harg]
  rw [sum_indicator_add_const hdisj hcov
    (fun i => b0 i + ∑ j : Fin P, b i j * X' (t - 1 - (j : ℕ)) ω) (σ0 * ε' t ω)
    (X' (t - (d : ℤ)) ω)]
  rw [tarStateDrift, ← hthr]
  simp only [Fin.coe_castSucc]

/-- **FY eq. (4.2)** (the canonical toy SETAR): `X_t = −0.7 X_{t−1} + ε_t` when
`X_{t−1} ≤ r` and `X_t = 0.7 X_{t−1} + ε_t` when `X_{t−1} > r` satisfies the two
stationarity conditions of pp. 126–127, so a strictly stationary solution exists. -/
theorem exists_stationary_toy_setar [IsProbabilityMeasure μ] (r : ℝ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, 0 < g x) ∧
      ν = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν) (hνmean : ∫ x, x ∂ν = 0) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
        IsTAR (fun _ : Fin 2 => (0 : ℝ))
          (fun i : Fin 2 => fun _ : Fin 1 => if i = 0 then (-0.7 : ℝ) else 0.7)
          (fun _ => (1 : ℝ))
          (fun i : Fin 2 => if i = 0 then {x : ℝ | x ≤ r} else {x : ℝ | r < x})
          1 X' ε' μ' ∧
        IsStrictlyStationary X' μ' := by
  -- the two half-lines are a measurable partition, and `|∓0.7| = 0.7 < 1` is the
  -- contraction condition (b); `d = 1 ≤ P = 1` is the delay condition
  have hd01 : Disjoint {x : ℝ | x ≤ r} {x : ℝ | r < x} := by
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    have h1 : x ≤ r := hx
    have h2 : r < x := hx'
    linarith
  have hfin : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
  refine exists_stationary_tar (μ := μ) (b0 := fun _ : Fin 2 => (0 : ℝ))
    (b := fun i : Fin 2 => fun _ : Fin 1 => if i = 0 then (-0.7 : ℝ) else 0.7)
    (σ0 := 1)
    (A := fun i : Fin 2 => if i = 0 then {x : ℝ | x ≤ r} else {x : ℝ | r < x})
    (d := 1) ?_ ?_ ?_ one_pos ?_ le_rfl le_rfl hν hν2 hνmean
  · intro i
    by_cases h : i = 0
    · rw [if_pos h]; exact measurableSet_Iic
    · rw [if_neg h]; exact measurableSet_Ioi
  · intro i j hij
    by_cases hi : i = 0
    · have hj : j ≠ 0 := fun h => hij (hi.trans h.symm)
      rw [if_pos hi, if_neg hj]
      exact hd01
    · have hj : j = 0 := by
        by_contra hj0
        exact hij ((hfin i hi).trans (hfin j hj0).symm)
      rw [if_neg hi, if_pos hj]
      exact hd01.symm
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    rcases le_or_gt x r with h | h
    · exact ⟨0, by rw [if_pos rfl]; exact h⟩
    · exact ⟨1, by rw [if_neg (by decide : ¬((1 : Fin 2) = 0))]; exact h⟩
  · intro i
    by_cases h : i = 0
    · rw [Fin.sum_univ_one, if_pos h]
      norm_num
    · rw [Fin.sum_univ_one, if_neg h]
      norm_num

end StatLean.TimeSeries
