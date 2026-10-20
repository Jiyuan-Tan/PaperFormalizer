module
public import StatLean.RobustStatistics.HeavyTails.EmpiricalMeanBaseline
public import StatLean.RobustStatistics.LocationScale.Median
public import StatLean.RobustStatistics.LocationScale.Mean
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.SubGaussian.Bounded
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# The median-of-means estimator — sub-Gaussian deviation under two moments

The median-of-means estimator (`LM §2.1`; going back to Nemirovsky–Yudin (1983),
Jerrum–Valiant–Vazirani (1986) and Alon–Matias–Szegedy (1999)) partitions the sample
into `k` blocks of size `m`, averages within each block, and takes the (low) median of
the block means. Its deviation is *sub-Gaussian* under nothing but a finite variance
(`LM Theorem 2`): each block mean is within `σ√(4/m)` of `μ` with probability `≥ 3/4`
(Chebyshev), so the median misses only if at least `k/2` blocks do — a binomial tail
event of probability `≤ e^{−k/8}` (Hoeffding).

* `medianOfMeans` — `sampleMedian` of the `k` blockwise `sampleMean`s.
* `abs_medianOfMeans_sub_le_of_majority` — the deterministic median step: if strictly
  more than `k/2` block means lie within `a` of `μ₀`, so does the median-of-means.
* `iIndepFun_blockMean` — block means of jointly independent data are independent.
* `medianOfMeans_deviation` — `LM Theorem 2`, exponential form.
* `medianOfMeans_subGaussian` — `LM Theorem 2`, `k = ⌈8 log(1/δ)⌉` corollary.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §2.1, Theorem 2. The median step reuses Round-1's `sampleMedian` counting API;
the binomial tail is `ConcentrationInequalities.hoeffding` on indicator variables
(bounded, hence sub-Gaussian by `isSubGaussian_of_mem_Icc`).

**Bibliographic comments.** Median-of-means was invented independently in stochastic
optimization (Nemirovsky and Yudin, *Problem Complexity and Method Efficiency in
Optimization*, Wiley, 1983), approximate counting (Jerrum, Valiant and Vazirani, *Theoret.
Comput. Sci.* **43** (1986), 169–188), and streaming algorithms (Alon, Matias and Szegedy,
*J. Comput. System Sci.* **58** (1999), 137–147). Its role as a sub-Gaussian mean estimator
under bare second moments is Lerasle and Oliveira (arXiv:1112.3914, 2011) and Devroye,
Lerasle, Lugosi and Oliveira, "Sub-Gaussian mean estimators," *Ann. Statist.* **44**
(2016), 2695–2725; Hsu and Sabato (*J. Mach. Learn. Res.* **17** (2016)) carried it into
learning theory.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure ℝ} [IsProbabilityMeasure P]

/-- **The median-of-means estimator** (`LM §2.1`): partition the data into `k` blocks of
`m` observations each (the data is presented already blocked, `x j i` = observation `i`
of block `j`), average within blocks, and take the median of the block means. The median
is Round-1's low `sampleMedian`, which satisfies LM's defining property ("at least `k/2`
of the values on each side"); for `k = 0` both `sampleMedian` and this estimator are the
junk value `0`. -/
noncomputable def medianOfMeans {k m : ℕ} (x : Fin k → Fin m → ℝ) : ℝ :=
  sampleMedian (fun j => sampleMean (x j))

/-! ### Measurability and product-measure plumbing -/

/-- The sample mean is a measurable function of the sample. -/
private lemma measurable_sampleMean {m : ℕ} : Measurable fun w : Fin m → ℝ => sampleMean w := by
  simp only [sampleMean]
  exact (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).div_const _

omit [IsProbabilityMeasure P] in
/-- Independence transports backwards along a common measurable map: if the family `f` is
independent under the pushforward `μ.map Y`, then `f ∘ Y` is independent under `μ`. -/
private lemma iIndepFun_comp_left {Ω' : Type*} [MeasurableSpace Ω'] {ι : Type*} [Fintype ι]
    {Y : Ξ → Ω'} (hY : Measurable Y) {f : ι → Ω' → ℝ} (hf : ∀ i, Measurable (f i))
    (h : iIndepFun f (μprob.map Y)) : iIndepFun (fun i ξ => f i (Y ξ)) μprob := by
  haveI : IsProbabilityMeasure (μprob.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map (f := fun i ξ => f i (Y ξ))
    fun i => ((hf i).comp hY).aemeasurable]
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (hf i).aemeasurable] at h
  have h1 : (fun ξ i => f i (Y ξ)) = (fun ω i => f i ω) ∘ Y := rfl
  rw [h1, ← Measure.map_map (measurable_pi_lambda _ fun i => hf i) hY, h]
  congr 1
  funext i
  rw [Measure.map_map (hf i) hY]
  rfl

/-- Currying the index: a product measure over a product index type is, under the
curry map, the iterated product measure over the blocks. -/
private lemma pi_map_curry {k m : ℕ} (ν : Fin k × Fin m → Measure ℝ)
    [∀ q, IsProbabilityMeasure (ν q)] :
    (Measure.pi ν).map (fun (v : Fin k × Fin m → ℝ) (j : Fin k) (i : Fin m) => v (j, i))
      = Measure.pi fun j => Measure.pi fun i => ν (j, i) := by
  have hU : Measurable fun (w : Fin k → Fin m → ℝ) (q : Fin k × Fin m) => w q.1 q.2 :=
    measurable_pi_lambda _ fun q => (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)
  have hC : Measurable fun (v : Fin k × Fin m → ℝ) (j : Fin k) (i : Fin m) => v (j, i) :=
    measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => measurable_pi_apply _
  -- the uncurry map pushes the iterated product forward to the product over pairs
  have hA : (Measure.pi fun j => Measure.pi fun i => ν (j, i)).map
      (fun (w : Fin k → Fin m → ℝ) (q : Fin k × Fin m) => w q.1 q.2) = Measure.pi ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply hU (MeasurableSet.univ_pi hs)]
    have hpre : (fun (w : Fin k → Fin m → ℝ) (q : Fin k × Fin m) => w q.1 q.2) ⁻¹'
        Set.univ.pi s = Set.univ.pi fun j => Set.univ.pi fun i => s (j, i) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Prod.forall]
    rw [hpre, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  have hCU : (fun (v : Fin k × Fin m → ℝ) (j : Fin k) (i : Fin m) => v (j, i)) ∘
      (fun (w : Fin k → Fin m → ℝ) (q : Fin k × Fin m) => w q.1 q.2) = id := rfl
  calc (Measure.pi ν).map (fun v j i => v (j, i))
      = ((Measure.pi fun j => Measure.pi fun i => ν (j, i)).map
          (fun w q => w q.1 q.2)).map (fun v j i => v (j, i)) := by rw [hA]
    _ = Measure.pi fun j => Measure.pi fun i => ν (j, i) := by
        rw [Measure.map_map hC hU, hCU, Measure.map_id]

/-- The median step, stated directly for the values whose median is taken: if strictly more
than `k/2` of the `Z j` lie in `[μ₀ − a, μ₀ + a]`, then so does `sampleMedian Z`. The two
Round-1 counting bricks (`card_le_sampleMedian`, `card_sampleMedian_le`) pin the median from
both sides; the ℕ-division bookkeeping is discharged by `omega`. -/
private lemma abs_sampleMedian_sub_le_of_majority {k : ℕ} (hk : k ≠ 0) (Z : Fin k → ℝ)
    {μ₀ a : ℝ}
    (hmaj : k < 2 * (Finset.univ.filter fun j => |Z j - μ₀| ≤ a).card) :
    |sampleMedian Z - μ₀| ≤ a := by
  classical
  -- any set of indices missing the band is contained in the complement of the majority set
  have hcompl : ∀ S : Finset (Fin k), (∀ j ∈ S, a < |Z j - μ₀|) →
      S.card ≤ k - (Finset.univ.filter fun j => |Z j - μ₀| ≤ a).card := by
    intro S hS
    have hsub : S ⊆ Finset.univ \ (Finset.univ.filter fun j => |Z j - μ₀| ≤ a) := by
      intro j hj
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, ?_⟩
      simp only [Finset.mem_filter, not_and, not_le]
      exact fun _ => hS j hj
    calc S.card ≤ (Finset.univ \ (Finset.univ.filter fun j => |Z j - μ₀| ≤ a)).card :=
          Finset.card_le_card hsub
      _ = k - _ := by
          rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [abs_le]
  constructor
  · -- if the median undershot, every index below it would miss the band
    by_contra hcon
    rw [not_le] at hcon
    have hS : ∀ j ∈ Finset.univ.filter fun j => Z j ≤ sampleMedian Z, a < |Z j - μ₀| := by
      intro j hj
      have hle : Z j ≤ sampleMedian Z := (Finset.mem_filter.mp hj).2
      rw [lt_abs]
      exact Or.inr (by linarith)
    have h1 := hcompl _ hS
    have h2 := card_le_sampleMedian hk Z
    omega
  · -- if the median overshot, every index above it would miss the band
    by_contra hcon
    rw [not_le] at hcon
    have hS : ∀ j ∈ Finset.univ.filter fun j => sampleMedian Z ≤ Z j, a < |Z j - μ₀| := by
      intro j hj
      have hle : sampleMedian Z ≤ Z j := (Finset.mem_filter.mp hj).2
      rw [lt_abs]
      exact Or.inl (by linarith)
    have h1 := hcompl _ hS
    have h2 := card_sampleMedian_le hk Z
    omega

/-- **The deterministic median step** (`LM Theorem 2` proof, the counting display): if
strictly more than `k/2` of the block means lie in `[μ₀ − a, μ₀ + a]`, then so does the
median-of-means. Strict majority in ℕ is written `k < 2 * card`. -/
theorem abs_medianOfMeans_sub_le_of_majority {k m : ℕ} (hk : k ≠ 0)
    (x : Fin k → Fin m → ℝ) {μ₀ a : ℝ}
    (hmaj : k < 2 * (Finset.univ.filter
      fun j => |sampleMean (x j) - μ₀| ≤ a).card) :
    |medianOfMeans x - μ₀| ≤ a :=
  abs_sampleMedian_sub_le_of_majority hk _ hmaj

/-- **Block means of independent data are independent** (`LM Theorem 2` proof,
implicit): if the doubly-indexed family is jointly independent, the `k` blockwise sample
means are jointly independent, each being a function of its own block's coordinates. -/
theorem iIndepFun_blockMean {k m : ℕ} {X : Fin k → Fin m → Ξ → ℝ}
    -- LEAN-ONLY: coordinate measurability, to compose independence; LM §2.1 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n = k·m observations are jointly independent; LM Theorem 2
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob) :
    iIndepFun (fun j ξ => sampleMean (fun i => X j i ξ)) μprob := by
  classical
  haveI hνblock : ∀ (j : Fin k) (i : Fin m), IsProbabilityMeasure (μprob.map (X j i)) :=
    fun j i => Measure.isProbabilityMeasure_map (hX_meas j i).aemeasurable
  haveI hνprob : ∀ q : Fin k × Fin m, IsProbabilityMeasure (μprob.map (X q.1 q.2)) :=
    fun q => hνblock q.1 q.2
  have hYmeas : Measurable fun ξ (q : Fin k × Fin m) => X q.1 q.2 ξ :=
    measurable_pi_lambda _ fun q => hX_meas q.1 q.2
  -- Step 1: joint independence says the joint law is the product law.
  have hlaw : μprob.map (fun ξ (q : Fin k × Fin m) => X q.1 q.2 ξ)
      = Measure.pi fun (q : Fin k × Fin m) => μprob.map (X q.1 q.2) :=
    (iIndepFun_iff_map_fun_eq_pi_map
      fun (q : Fin k × Fin m) => (hX_meas q.1 q.2).aemeasurable).1 hX_indep
  -- Step 2: under a product law, functions of disjoint coordinate blocks are independent.
  have hblocks : iIndepFun
      (fun (j : Fin k) (v : Fin k × Fin m → ℝ) => sampleMean fun i => v (j, i))
      (Measure.pi fun (q : Fin k × Fin m) => μprob.map (X q.1 q.2)) := by
    have hpi : iIndepFun
        (fun (j : Fin k) (w : Fin k → Fin m → ℝ) => sampleMean (w j))
        (Measure.pi fun j => Measure.pi fun i => μprob.map (X j i)) :=
      iIndepFun_pi (X := fun (_ : Fin k) (w : Fin m → ℝ) => sampleMean w)
        fun _ => measurable_sampleMean.aemeasurable
    refine iIndepFun_comp_left (Y := fun (v : Fin k × Fin m → ℝ) (j : Fin k) (i : Fin m) =>
      v (j, i)) (measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i =>
        measurable_pi_apply _) (fun j => measurable_sampleMean.comp (measurable_pi_apply j)) ?_
    rw [pi_map_curry]
    exact hpi
  -- Step 3: transport the product-law statement back along the joint law.
  exact iIndepFun_comp_left hYmeas
    (fun j => measurable_sampleMean.comp
      (measurable_pi_lambda _ fun i => measurable_pi_apply _))
    (by rw [hlaw]; exact hblocks)

/-- **Median-of-means is sub-Gaussian, exponential form** (`LM Theorem 2`, first
display): for i.i.d. data with mean `μ₀` and variance `σ²`, arranged in `k` blocks of
size `m`,

  `P( |μ̂ − μ₀| > σ√(4/m) ) ≤ exp(−k/8)`.

Chebyshev puts each block mean within `σ√(4/m)` with probability `≥ 3/4`; missing the
band is an independent Bernoulli event of parameter `≤ 1/4` per block, and the median
misses only if at least `k/2` blocks do (Hoeffding's inequality on the indicators). -/
theorem medianOfMeans_deviation {k m : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    {X : Fin k → Fin m → Ξ → ℝ} {μ₀ σ2 : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.1 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n = k·m observations are jointly independent; LM Theorem 2
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob)
    -- USER-INPUT: common law P; LM Theorem 2 ("identically distributed")
    (hX_law : ∀ j i, μprob.map (X j i) = P)
    -- USER-INPUT: P is square-integrable; LM Theorem 2 ("with variance σ²")
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM Theorem 2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    -- USER-INPUT: nondegenerate variance (σ = 0 makes the band trivial); LM Theorem 2
    (hσ : 0 < σ2) :
    μprob.real {ξ | Real.sqrt σ2 * Real.sqrt (4 / m)
        < |medianOfMeans (fun j i => X j i ξ) - μ₀|}
      ≤ Real.exp (-(k : ℝ) / 8) := by
  classical
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin k → Ξ → ℝ, Z = fun j ξ => sampleMean fun i => X j i ξ :=
    ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.sqrt σ2 * Real.sqrt (4 / m) := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ℝ → ℝ, g = fun y => if a ≤ |y - μ₀| then (1 : ℝ) else 0 :=
    ⟨_, rfl⟩
  have hgapp : ∀ y, g y = if a ≤ |y - μ₀| then (1 : ℝ) else 0 := fun y => by rw [hgdef]
  -- the block means: measurable, independent, and each within the band w.p. ≥ 3/4
  have hZmeas : ∀ j, Measurable (Z j) := by
    intro j
    simp only [hZ]
    exact measurable_sampleMean.comp (measurable_pi_lambda _ fun i => hX_meas j i)
  have hZindep : iIndepFun Z μprob := by
    simp only [hZ]
    exact iIndepFun_blockMean hX_meas hX_indep
  have hcheb : ∀ j, μprob.real {ξ | a ≤ |Z j ξ - μ₀|} ≤ 1 / 4 := by
    intro j
    have hinj : Function.Injective fun i : Fin m => ((j, i) : Fin k × Fin m) := by
      intro i1 i2 h; simpa using h
    have hrow : iIndepFun (fun i => X j i) μprob :=
      hX_indep.precomp (g := fun i : Fin m => ((j, i) : Fin k × Fin m)) hinj
    have h := sampleMean_chebyshev_deviation (P := P) hm (fun i => hX_meas j i) hrow
      (fun i => hX_law j i) hL2 hmean hvar (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num) hσ
    have harg : Real.sqrt σ2 * Real.sqrt (1 / ((m : ℝ) * (1 / 4))) = a := by
      rw [ha]; congr 2; ring
    rw [harg] at h
    simpa [hZ] using h
  -- the per-block failure indicators
  have hgmeas : Measurable g := by
    rw [hgdef]
    exact Measurable.ite (measurableSet_le measurable_const
      (measurable_id.sub_const μ₀).abs) measurable_const measurable_const
  have hgIcc : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    rw [hgapp]
    split <;> norm_num
  have hVint : ∀ j, ∫ ξ, g (Z j ξ) ∂μprob = μprob.real {ξ | a ≤ |Z j ξ - μ₀|} := by
    intro j
    have hset : MeasurableSet {ξ | a ≤ |Z j ξ - μ₀|} :=
      measurableSet_le measurable_const ((hZmeas j).sub_const μ₀).abs
    have heq : (fun ξ => g (Z j ξ))
        = Set.indicator {ξ | a ≤ |Z j ξ - μ₀|} fun _ => (1 : ℝ) := by
      funext ξ
      by_cases h : a ≤ |Z j ξ - μ₀|
      · have hmem : ξ ∈ {ξ | a ≤ |Z j ξ - μ₀|} := h
        rw [hgapp, if_pos h, Set.indicator_of_mem hmem]
      · have hmem : ξ ∉ {ξ | a ≤ |Z j ξ - μ₀|} := h
        rw [hgapp, if_neg h, Set.indicator_of_notMem hmem]
    rw [heq, integral_indicator_const (1 : ℝ) hset, smul_eq_mul, mul_one]
  have hsubG : ∀ j, HasSubgaussianMGF
      (fun ξ => g (Z j ξ) - ∫ ξ', g (Z j ξ') ∂μprob) (1 / 4 : NNReal) μprob := by
    intro j
    have h := ConcentrationInequalities.isSubGaussian_of_mem_Icc
      (X := fun ξ => g (Z j ξ)) (a := 0) (b := 1) (μ := μprob)
      (hgmeas.comp (hZmeas j)).aemeasurable (ae_of_all _ fun ξ => hgIcc (Z j ξ))
    have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = (1 / 4 : NNReal) := by
      simp
      norm_num
    rwa [hc] at h
  have hWindep : iIndepFun
      (fun j ξ => g (Z j ξ) - ∫ ξ', g (Z j ξ') ∂μprob) μprob :=
    hZindep.comp (fun j y => g y - ∫ ξ', g (Z j ξ') ∂μprob) fun _ => hgmeas.sub_const _
  -- Hoeffding on the indicators
  have hhoef := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hWindep
    (s := Finset.univ) (c := fun _ : Fin k => (1 / 4 : NNReal)) (fun j _ => hsubG j)
    (ε := (k : ℝ) / 4) (by positivity)
  -- the median misses only if at least half the blocks do
  have hsubset : {ξ | a < |(sampleMedian fun j => Z j ξ) - μ₀|} ⊆
      {ξ | (k : ℝ) / 4 ≤ ∑ j, (g (Z j ξ) - ∫ ξ', g (Z j ξ') ∂μprob)} := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    -- a strict majority of blocks inside the band would pin the median inside it
    have hmaj : ¬ k < 2 * (Finset.univ.filter fun j => |Z j ξ - μ₀| ≤ a).card := fun hcon =>
      absurd (abs_sampleMedian_sub_le_of_majority hk (fun j => Z j ξ) hcon) (not_le.mpr hξ)
    rw [not_lt] at hmaj
    -- so at least `k/2` blocks miss the band; count them with the indicators
    have hAle : (Finset.univ.filter fun j => |Z j ξ - μ₀| ≤ a).card ≤ k := by
      calc (Finset.univ.filter fun j => |Z j ξ - μ₀| ≤ a).card
          ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
        _ = k := by simp
    have hcompl : Finset.univ \ (Finset.univ.filter fun j => |Z j ξ - μ₀| ≤ a)
        ⊆ Finset.univ.filter fun j => a ≤ |Z j ξ - μ₀| := by
      intro j hj
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, le_of_lt hj⟩
    have hcard := Finset.card_le_card hcompl
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin] at hcard
    have hAB : k ≤ (Finset.univ.filter fun j => |Z j ξ - μ₀| ≤ a).card
        + (Finset.univ.filter fun j => a ≤ |Z j ξ - μ₀|).card := by omega
    have hABr : (k : ℝ) ≤ ((Finset.univ.filter fun j => |Z j ξ - μ₀| ≤ a).card : ℝ)
        + ((Finset.univ.filter fun j => a ≤ |Z j ξ - μ₀|).card : ℝ) := by
      exact_mod_cast hAB
    have hmajr : 2 * ((Finset.univ.filter fun j => |Z j ξ - μ₀| ≤ a).card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hmaj
    -- the indicator sum counts the missing blocks
    have hsum : ∑ j, g (Z j ξ)
        = ((Finset.univ.filter fun j => a ≤ |Z j ξ - μ₀|).card : ℝ) := by
      simp only [hgapp]
      rw [Finset.sum_boole]
    have hmeanbd : ∑ j : Fin k, (∫ ξ', g (Z j ξ') ∂μprob) ≤ (k : ℝ) / 4 := by
      calc ∑ j : Fin k, (∫ ξ', g (Z j ξ') ∂μprob)
          ≤ ∑ _j : Fin k, (1 / 4 : ℝ) :=
            Finset.sum_le_sum fun j _ => (hVint j) ▸ hcheb j
        _ = (k : ℝ) / 4 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    rw [Finset.sum_sub_distrib, hsum]
    linarith
  -- assemble
  have hsetEq : {ξ | Real.sqrt σ2 * Real.sqrt (4 / m)
      < |medianOfMeans (fun j i => X j i ξ) - μ₀|}
      = {ξ | a < |(sampleMedian fun j => Z j ξ) - μ₀|} := by
    ext ξ
    simp only [Set.mem_setOf_eq, ha, hZ, medianOfMeans]
  rw [hsetEq]
  refine le_trans (measureReal_mono hsubset (measure_ne_top _ _)) (hhoef.trans (le_of_eq ?_))
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **Median-of-means is sub-Gaussian, confidence form** (`LM Theorem 2`, "in
particular"): choosing `k = ⌈8 log(1/δ)⌉` blocks, with probability at least `1 − δ`,

  `|μ̂ − μ₀| ≤ σ √((32 log(1/δ) + 4)/n)`.

**Constant note.** LM state the radius as `σ√(32 log(1/δ)/n)`, silently absorbing the
ceiling: with `k = ⌈8 log(1/δ)⌉ ≤ 8 log(1/δ) + 1` the provable radius is
`σ√(4k/n) ≤ σ√((32 log(1/δ) + 4)/n)`, and the `+4` cannot be dropped unless
`8 log(1/δ)` is an integer. We state the provable constant (project constants policy). -/
theorem medianOfMeans_subGaussian {k m n : ℕ} (hm : m ≠ 0)
    {X : Fin k → Fin m → Ξ → ℝ} {μ₀ σ2 δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §2.1 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n observations are jointly independent; LM Theorem 2
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob)
    -- USER-INPUT: common law P; LM Theorem 2
    (hX_law : ∀ j i, μprob.map (X j i) = P)
    -- USER-INPUT: P is square-integrable; LM Theorem 2
    (hL2 : MemLp id 2 P)
    -- USER-INPUT: mean and variance of P; LM Theorem 2
    (hmean : ∫ x, x ∂P = μ₀) (hvar : ∫ x, (x - μ₀) ^ 2 ∂P = σ2)
    (hσ : 0 < σ2)
    -- USER-INPUT: confidence level; LM Theorem 2
    (hδ : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: sample size and block count; LM Theorem 2 ("n = mk",
    -- "k = ⌈8 log(1/δ)⌉")
    (hn : n = k * m) (hkc : k = ⌈8 * Real.log (1 / δ)⌉₊) :
    μprob.real {ξ | Real.sqrt σ2 * Real.sqrt ((32 * Real.log (1 / δ) + 4) / n)
        < |medianOfMeans (fun j i => X j i ξ) - μ₀|}
      ≤ δ := by
  classical
  -- `log(1/δ) > 0`, hence `k = ⌈8 log(1/δ)⌉ ≥ 1` and `n = km ≥ 1`
  have hLpos : 0 < Real.log (1 / δ) := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  have hk : k ≠ 0 := by
    rw [hkc, ne_eq, Nat.ceil_eq_zero, not_le]
    linarith
  have hn0 : n ≠ 0 := by rw [hn]; exact Nat.mul_ne_zero hk hm
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hkR : (k : ℝ) ≤ 8 * Real.log (1 / δ) + 1 := by
    rw [hkc]
    exact le_of_lt (Nat.ceil_lt_add_one (by linarith))
  have hkL : 8 * Real.log (1 / δ) ≤ (k : ℝ) := by
    rw [hkc]; exact Nat.le_ceil _
  -- the stated radius dominates the `σ√(4/m)` radius of the exponential form
  have hradius : Real.sqrt σ2 * Real.sqrt (4 / m)
      ≤ Real.sqrt σ2 * Real.sqrt ((32 * Real.log (1 / δ) + 4) / n) := by
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
    have hfrac : (4 : ℝ) / (m : ℝ) = 4 * (k : ℝ) / (n : ℝ) := by
      rw [hn]
      push_cast
      field_simp
    rw [hfrac]
    gcongr
    linarith
  have hsub : {ξ | Real.sqrt σ2 * Real.sqrt ((32 * Real.log (1 / δ) + 4) / n)
        < |medianOfMeans (fun j i => X j i ξ) - μ₀|}
      ⊆ {ξ | Real.sqrt σ2 * Real.sqrt (4 / m)
        < |medianOfMeans (fun j i => X j i ξ) - μ₀|} :=
    fun ξ hξ => lt_of_le_of_lt hradius hξ
  refine le_trans (measureReal_mono hsub (measure_ne_top _ _)) ?_
  refine le_trans
    (medianOfMeans_deviation hk hm hX_meas hX_indep hX_law hL2 hmean hvar hσ) ?_
  -- `k ≥ 8 log(1/δ)` turns the exponential bound into `δ`
  have hlog : Real.log (1 / δ) = -Real.log δ := by rw [one_div, Real.log_inv]
  calc Real.exp (-(k : ℝ) / 8) ≤ Real.exp (Real.log δ) := by
        apply Real.exp_le_exp.mpr
        rw [hlog] at hkL
        linarith
    _ = δ := Real.exp_log hδ

end StatLean.RobustStatistics
