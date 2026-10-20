module
public import StatLean.Bayesian.BernsteinVonMises.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.SubGaussian.Bounded

@[expose] public section

/-!
# Boosting consistent tests to exponential power (far range)

The second half of vdV §10.2: given *any* uniformly consistent test sequence for
`H₀ : θ = θ₀` against `H₁ : ‖θ − θ₀‖ ≥ ε` (the uniform-tests condition), one can construct tests
whose
type-II error decays **exponentially** in `n`, uniformly over the far alternatives. The
construction blocks the sample into groups of a fixed size `kb`, applies the given level-`kb`
test to each block, and rejects when the average of the block tests exceeds `1/2`; Hoeffding's
inequality for `[0,1]`-valued iid block statistics gives the exponential bound.

* `bvmBlockAvg` — the average of a one-block statistic over the `⌊n/kb⌋` disjoint blocks;
* `blockAvg_typeII_tail` — the Hoeffding bound
  `P^n_θ(blockAvg < 1/2) ≤ exp(−⌊n/kb⌋/8)` when the one-block mean is `≥ 3/4`;
* `exists_boosted_tests` — the headline: exponentially consistent tests on
  `‖θ − θ₀‖ ≥ ε`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Lemma 10.3, p. 144 (second test sequence; blocks `Y_{n,1}, …, Y_{n,m}`).

**Proof formalization notes.** Under `productMeasure M μ θ n` the block statistics are iid
`[0,1]`-valued with mean `∫ φ_kb dP^{kb}_θ`; independence of the blocks follows from
`ProbabilityTheory.iIndepFun_pi` composed with the disjoint block-coordinate projections.
Hoeffding is `StatLean.ConcentrationInequalities.hoeffding` (with
`isSubGaussian_of_mem_Icc`). The auxiliary size-`kb` level and the threshold `1/2` follow
vdV's choice `P^{kb}_{θ₀} φ_{kb} < 1/4 < 3/4 ≤ P^{kb}_θ φ_{kb}`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open AsymptoticStatistics (ParametricFamily IsPDFOf)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)}

/-- Within-block index arithmetic: the `i`-th coordinate of the `j`-th length-`kb` block is a
valid sample index. -/
lemma bvmBlockIndex_lt {n kb : ℕ} (j : Fin (n / kb)) (i : Fin kb) :
    j.val * kb + i.val < n := by
  have h1 : j.val + 1 ≤ n / kb := j.isLt
  have h2 : (j.val + 1) * kb ≤ (n / kb) * kb := Nat.mul_le_mul_right kb h1
  have h3 : (n / kb) * kb ≤ n := Nat.div_mul_le_self n kb
  have h4 : j.val * kb + i.val < (j.val + 1) * kb := by
    rw [Nat.add_one_mul]; exact Nat.add_lt_add_left i.isLt _
  omega

/-- **Block average of a one-block statistic**: split `ω : Fin n → 𝓧` into `⌊n/kb⌋` disjoint
consecutive blocks of length `kb` and average `g` over the blocks. Junk behavior: for
`kb = 0` or `n < kb` the block count is `0` and the average is the empty-sum `0` scaled by
`(0 : ℝ)⁻¹ = 0`. -/
noncomputable def bvmBlockAvg (kb : ℕ) (g : (Fin kb → 𝓧) → ℝ) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  ((n / kb : ℕ) : ℝ)⁻¹ *
    ∑ j : Fin (n / kb), g fun i : Fin kb =>
      ω ⟨j.val * kb + i.val, bvmBlockIndex_lt j i⟩

/-! ### Private machinery: the block-projection map and its pushforward -/

/-- The map splitting a sample of size `n` into its `⌊n/kb⌋ disjoint blocks of length `kb`. -/
private def bvmBlockProj (n kb : ℕ) : (Fin n → 𝓧) → (Fin (n / kb) → (Fin kb → 𝓧)) :=
  fun ω j i => ω ⟨j.val * kb + i.val, bvmBlockIndex_lt j i⟩

private lemma measurable_bvmBlockProj (n kb : ℕ) :
    Measurable (bvmBlockProj (𝓧 := 𝓧) n kb) :=
  measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Within-block index arithmetic: `(j * kb + i) / kb = j` and `(j * kb + i) % kb = i`. -/
private lemma bvm_divMod {kb : ℕ} (hkb : 0 < kb) (j i : ℕ) (hi : i < kb) :
    (j * kb + i) / kb = j ∧ (j * kb + i) % kb = i := by
  rw [Nat.add_comm]
  refine ⟨?_, ?_⟩
  · rw [Nat.add_mul_div_right _ _ hkb, Nat.div_eq_of_lt hi, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

/-- **The blocks are an iid sample of block-samples**: the pushforward of the `n`-fold product
under `bvmBlockProj` is the `⌊n/kb⌋`-fold product of the `kb`-fold product. -/
private lemma map_bvmBlockProj (P : Measure 𝓧) [IsProbabilityMeasure P] (n : ℕ) {kb : ℕ}
    (hkb : 0 < kb) :
    (Measure.pi fun _ : Fin n => P).map (bvmBlockProj n kb)
      = Measure.pi fun _ : Fin (n / kb) => Measure.pi fun _ : Fin kb => P := by
  classical
  refine (Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => MeasureTheory.Measure.FiniteSpanningSetsIn.pi
      fun _ => P.toFiniteSpanningSetsIn) ?_).symm
  intro s hs
  choose t ht hts using hs
  have htm : ∀ j i, MeasurableSet (t j i) := fun j i => ht j i (Set.mem_univ i)
  -- the injective block-index embedding `Fin (n/kb) × Fin kb ↪ Fin n`
  set e : Fin (n / kb) × Fin kb → Fin n :=
    fun x => ⟨x.1.val * kb + x.2.val, bvmBlockIndex_lt x.1 x.2⟩ with he
  have hinj : Function.Injective e := by
    rintro ⟨j₁, i₁⟩ ⟨j₂, i₂⟩ hEq
    have hEq' : j₁.val * kb + i₁.val = j₂.val * kb + i₂.val := congrArg Fin.val hEq
    have h1 := bvm_divMod hkb j₁.val i₁.val i₁.isLt
    have h2 := bvm_divMod hkb j₂.val i₂.val i₂.isLt
    have hj : j₁.val = j₂.val := by rw [← h1.1, ← h2.1, hEq']
    have hi : i₁.val = i₂.val := by rw [← h1.2, ← h2.2, hEq']
    simp [Prod.ext_iff, Fin.ext_iff, hj, hi]
  -- the coordinate box in `Fin n` corresponding to the box-of-boxes `s`
  set u : Fin n → Set 𝓧 :=
    Function.extend e (fun x => t x.1 x.2) (fun _ => Set.univ) with hu
  have hue : ∀ x, u (e x) = t x.1 x.2 := fun x => hinj.extend_apply _ _ x
  have hurange : ∀ l, l ∉ Set.range e → u l = Set.univ := by
    intro l hl
    exact Function.extend_apply' _ _ l (by simpa [Set.mem_range] using hl)
  have hum : ∀ l, MeasurableSet (u l) := by
    intro l
    by_cases hl : l ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hl
      rw [hue]; exact htm _ _
    · rw [hurange l hl]; exact MeasurableSet.univ
  have hpre : bvmBlockProj n kb ⁻¹' Set.pi Set.univ s = Set.pi Set.univ u := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, ← hts, bvmBlockProj]
    constructor
    · intro h l
      by_cases hl : l ∈ Set.range e
      · obtain ⟨x, rfl⟩ := hl
        rw [hue]
        exact h x.1 x.2
      · rw [hurange l hl]; exact Set.mem_univ _
    · intro h j i
      have := h (e (j, i))
      rwa [hue (j, i)] at this
  rw [Measure.map_apply (measurable_bvmBlockProj n kb)
      (MeasurableSet.univ_pi fun j => by rw [← hts j]; exact MeasurableSet.univ_pi (htm j)),
    hpre, Measure.pi_pi]
  simp only [← hts, Measure.pi_pi]
  set A : Finset (Fin n) := Finset.image e Finset.univ with hA
  have hstep : ∏ l : Fin n, P (u l) = ∏ l ∈ A, P (u l) := by
    refine (Finset.prod_subset (Finset.subset_univ A) ?_).symm
    intro l _ hlA
    have hl : l ∉ Set.range e := by
      rintro ⟨x, rfl⟩
      exact hlA (Finset.mem_image_of_mem e (Finset.mem_univ x))
    rw [hurange l hl, measure_univ]
  rw [hstep, hA, Finset.prod_image (fun x _ y _ h => hinj h), Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun i _ => by rw [hue (j, i)]

/-- **Abstract Hoeffding bound for an average of iid `[0,1]`-variables with mean `≥ 3/4`.** -/
private lemma hoeffding_avg_le {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {m : ℕ} (hm : 1 ≤ m) (Y : Fin m → Ω → ℝ)
    (hYmeas : ∀ j, Measurable (Y j)) (hY01 : ∀ j ω, Y j ω ∈ Set.Icc (0 : ℝ) 1)
    (hindep : iIndepFun Y ν) (hmean : ∀ j, 3 / 4 ≤ ∫ ω, Y j ω ∂ν) :
    ν.real {ω | ((m : ℝ))⁻¹ * ∑ j, Y j ω ≤ 1 / 2} ≤ Real.exp (-(m : ℝ) / 8) := by
  classical
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set c : Fin m → ℝ := fun j => ∫ ω, -(Y j ω) ∂ν with hc
  have hcval : ∀ j, c j = -∫ ω, Y j ω ∂ν := fun j => by rw [hc]; exact integral_neg _
  set X : Fin m → Ω → ℝ := fun j ω => -(Y j ω) - c j with hX
  have hsub : ∀ j, HasSubgaussianMGF (X j) ((1 : ℝ≥0) / 4) ν := by
    intro j
    have h := StatLean.ConcentrationInequalities.isSubGaussian_of_mem_Icc
      (X := fun ω => -(Y j ω)) (a := -1) (b := 0) (μ := ν) (hYmeas j).neg.aemeasurable
      (Filter.Eventually.of_forall fun ω =>
        ⟨by linarith [(hY01 j ω).2], by linarith [(hY01 j ω).1]⟩)
    have hnn : ((‖(0 : ℝ) - (-1)‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
      apply NNReal.coe_injective
      push_cast [Real.norm_eq_abs]
      norm_num
    rw [hnn] at h
    exact h
  have hindepX : iIndepFun X ν :=
    hindep.comp (fun j (y : ℝ) => -y - c j) (fun j => measurable_neg.sub_const _)
  have hε : (0 : ℝ) ≤ (m : ℝ) / 4 := by positivity
  have hoeff := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (μ := ν) hindepX
    (c := fun _ : Fin m => ((1 : ℝ≥0) / 4)) (s := Finset.univ) (fun i _ => hsub i) hε
  have hsubset : {ω | ((m : ℝ))⁻¹ * ∑ j, Y j ω ≤ 1 / 2}
      ⊆ {ω | (m : ℝ) / 4 ≤ ∑ j ∈ Finset.univ, X j ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hXj : ∀ j : Fin m, X j ω = (∫ ω', Y j ω' ∂ν) - Y j ω := by
      intro j; rw [hX]; simp only [hcval j]; ring
    have hXsum : ∑ j ∈ Finset.univ, X j ω
        = (∑ j : Fin m, ∫ ω', Y j ω' ∂ν) - ∑ j : Fin m, Y j ω := by
      simp_rw [hXj]; rw [Finset.sum_sub_distrib]
    have h1 : (3 / 4 : ℝ) * m ≤ ∑ j : Fin m, ∫ ω', Y j ω' ∂ν := by
      calc (3 / 4 : ℝ) * m = ∑ _j : Fin m, (3 / 4 : ℝ) := by
            simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun j _ => hmean j
    have h2 : ∑ j : Fin m, Y j ω ≤ (m : ℝ) * (1 / 2) := by
      have h := mul_le_mul_of_nonneg_left hω (le_of_lt hm0)
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hm0), one_mul] at h
      linarith
    rw [hXsum]; linarith
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  refine le_trans (le_trans (measureReal_mono hsubset) hoeff) (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **The two-sided Hoeffding block bound**: `P(blockAvg ≤ 1/2) ≤ exp(−⌊n/kb⌋/8)` whenever
the one-block mean is `≥ 3/4`. Both tails of `blockAvg_typeII_tail` and of the size bound in
`exists_boosted_tests` are instances of this (the latter after replacing `g` by `1 − g`). -/
private lemma blockAvg_le_half_tail (P : Measure 𝓧) [IsProbabilityMeasure P]
    {kb : ℕ} (hkb : 1 ≤ kb) {g : (Fin kb → 𝓧) → ℝ} (hg_meas : Measurable g)
    (hg01 : ∀ ζ, g ζ ∈ Set.Icc (0 : ℝ) 1)
    (hpow : 3 / 4 ≤ ∫ ζ, g ζ ∂(Measure.pi fun _ : Fin kb => P)) {n : ℕ} (hn : kb ≤ n) :
    (Measure.pi fun _ : Fin n => P).real {ω | bvmBlockAvg kb g n ω ≤ 1 / 2}
      ≤ Real.exp (-(↑(n / kb) : ℝ) / 8) := by
  have hkb0 : 0 < kb := hkb
  have hm : 1 ≤ n / kb := (Nat.one_le_div_iff hkb0).mpr hn
  have hYmeas : ∀ j : Fin (n / kb),
      Measurable fun η : Fin (n / kb) → (Fin kb → 𝓧) => g (η j) :=
    fun j => hg_meas.comp (measurable_pi_apply j)
  have hmeanj : ∀ j : Fin (n / kb), (3 : ℝ) / 4 ≤ ∫ η, g (η j)
      ∂(Measure.pi fun _ : Fin (n / kb) => Measure.pi fun _ : Fin kb => P) := by
    intro j
    have hmp := (MeasureTheory.measurePreserving_eval
      (fun _ : Fin (n / kb) => Measure.pi fun _ : Fin kb => P) j).map_eq
    rw [← hmp, integral_map (measurable_pi_apply j).aemeasurable
      hg_meas.aestronglyMeasurable] at hpow
    exact hpow
  have hindep : iIndepFun
      (fun (j : Fin (n / kb)) (η : Fin (n / kb) → (Fin kb → 𝓧)) => g (η j))
      (Measure.pi fun _ : Fin (n / kb) => Measure.pi fun _ : Fin kb => P) :=
    iIndepFun_pi (X := fun _ : Fin (n / kb) => g) (fun _ => hg_meas.aemeasurable)
  have key := hoeffding_avg_le
    (Measure.pi fun _ : Fin (n / kb) => Measure.pi fun _ : Fin kb => P) hm
    (fun (j : Fin (n / kb)) (η : Fin (n / kb) → (Fin kb → 𝓧)) => g (η j))
    hYmeas (fun j η => hg01 (η j)) hindep hmeanj
  rw [← map_bvmBlockProj P n hkb0] at key
  have hS : MeasurableSet {η : Fin (n / kb) → (Fin kb → 𝓧) |
      ((n / kb : ℕ) : ℝ)⁻¹ * ∑ j, g (η j) ≤ 1 / 2} :=
    measurableSet_le (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => hYmeas j)) measurable_const
  rw [measureReal_def, Measure.map_apply (measurable_bvmBlockProj n kb) hS] at key
  exact key

/-- **Hoeffding bound for the block average** (vdV p. 144): if the one-block statistic `g`
takes values in `[0,1]` and has `P^{kb}_θ`-mean at least `3/4`, then
`P^n_θ(bvmBlockAvg < 1/2) ≤ exp(−⌊n/kb⌋/8)`. -/
theorem blockAvg_typeII_tail
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ) {kb : ℕ}
    -- LEAN-ONLY: nonempty blocks
    (hkb : 1 ≤ kb) {g : (Fin kb → 𝓧) → ℝ}
    -- LEAN-ONLY: measurable one-block statistic (regularity)
    (hg_meas : Measurable g)
    -- LEAN-ONLY: `[0,1]`-valued one-block statistic (a test)
    (hg01 : ∀ ζ, g ζ ∈ Set.Icc (0 : ℝ) 1)
    (θ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: one-block power `≥ 3/4` at `θ`; vdV p. 144
    (hpow : 3 / 4 ≤ ∫ ζ, g ζ ∂(productMeasure M μ θ kb)) {n : ℕ}
    -- LEAN-ONLY: at least one full block
    (hn : kb ≤ n) :
    (productMeasure M μ θ n).real {ω | bvmBlockAvg kb g n ω < 1 / 2}
      ≤ Real.exp (-(↑(n / kb) : ℝ) / 8) := by
  haveI hP : IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (M.density θ x)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ)
        (Filter.Eventually.of_forall (M.density_nonneg θ)),
      hPDF.density_integral_eq_one θ, ENNReal.ofReal_one]
  haveI : IsProbabilityMeasure (productMeasure M μ θ n) :=
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF θ n
  have h := blockAvg_le_half_tail (μ.withDensity fun x => ENNReal.ofReal (M.density θ x))
    hkb hg_meas hg01 hpow hn
  refine le_trans ?_ h
  refine measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)
  simp only [Set.mem_setOf_eq] at hω ⊢
  exact le_of_lt hω

/-- Reflecting the one-block statistic reflects the block average: `avg(1 − g) = 1 − avg g`. -/
private lemma bvmBlockAvg_one_sub {kb : ℕ} (g : (Fin kb → 𝓧) → ℝ) {n : ℕ}
    (hm : 1 ≤ n / kb) (ω : Fin n → 𝓧) :
    bvmBlockAvg kb (fun ζ => 1 - g ζ) n ω = 1 - bvmBlockAvg kb g n ω := by
  have hm0 : ((n / kb : ℕ) : ℝ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  simp only [bvmBlockAvg]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  field_simp

/-- **Exponentially consistent tests on the far range** (vdV §10.2, second test
sequence): under the uniform-tests condition, for every `ε > 0` there are measurable
`[0,1]`-tests with vanishing size at `θ₀` and type-II error `≤ exp(−c n)` uniformly over
`‖θ − θ₀‖ ≥ ε`, for `n` large. -/
theorem exists_boosted_tests
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the uniform-tests condition; vdV §10.2
    (hTests : UniformlyConsistentTests M μ θ₀) {ε : ℝ}
    -- LEAN-ONLY: nontrivial separation radius
    (hε : 0 < ε) :
    ∃ (φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ) (c : ℝ), 0 < c ∧
      (∀ n, Measurable (φ n)) ∧ (∀ n ω, φ n ω ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun n => ∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ θ, ε ≤ ‖θ - θ₀‖ →
        ∫ ω, (1 - φ n ω) ∂(productMeasure M μ θ n) ≤ Real.exp (-c * n) := by
  classical
  obtain ⟨φt, hφt_meas, hφt01, hφt_size, hφt_pow⟩ := hTests ε hε
  haveI hPfac : ∀ θ : EuclideanSpace ℝ (Fin k),
      IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (M.density θ x)) := by
    intro θ
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable θ)
        (Filter.Eventually.of_forall (M.density_nonneg θ)),
      hPDF.density_integral_eq_one θ, ENNReal.ofReal_one]
  haveI hPM : ∀ (θ : EuclideanSpace ℝ (Fin k)) (nn : ℕ),
      IsProbabilityMeasure (productMeasure M μ θ nn) := fun θ nn =>
    AsymptoticStatistics.AsymptoticRepresentation.productMeasure_isProbabilityMeasure
      M μ hPDF θ nn
  have hint : ∀ (θ : EuclideanSpace ℝ (Fin k)) (nn : ℕ),
      Integrable (φt nn) (productMeasure M μ θ nn) := by
    intro θ nn
    refine Integrable.mono' (integrable_const 1) (hφt_meas nn).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφt01 nn ω).1]
    exact (hφt01 nn ω).2
  have hsplit : ∀ (θ : EuclideanSpace ℝ (Fin k)) (nn : ℕ),
      ∫ ω, (1 - φt nn ω) ∂(productMeasure M μ θ nn)
        = 1 - ∫ ω, φt nn ω ∂(productMeasure M μ θ nn) := by
    intro θ nn
    rw [integral_sub (integrable_const 1) (hint θ nn), integral_const]
    simp
  -- choose the block size `kb`: uniform power `≥ 3/4` on the far range and size `≤ 1/4`
  have hev1 : ∀ᶠ nn in atTop, ∀ θ, ε ≤ ‖θ - θ₀‖ →
      ∫ ω, (1 - φt nn ω) ∂(productMeasure M μ θ nn) ≤ 1 / 4 :=
    hφt_pow (1 / 4) (by norm_num)
  have hev2 : ∀ᶠ nn in atTop, ∫ ω, φt nn ω ∂(productMeasure M μ θ₀ nn) ≤ 1 / 4 :=
    hφt_size.eventually_le_const (by norm_num)
  obtain ⟨kb, ⟨hkbpow, hkbsize⟩, hkb1⟩ :=
    ((hev1.and hev2).and (eventually_ge_atTop 1)).exists
  have hkb0 : 0 < kb := hkb1
  have hkbR : (0 : ℝ) < (kb : ℝ) := by exact_mod_cast hkb0
  have hkbne : (kb : ℝ) ≠ 0 := ne_of_gt hkbR
  have hcpos : (0 : ℝ) < 1 / (16 * (kb : ℝ)) :=
    div_pos one_pos (by linarith)
  have hBAmeas : ∀ nn, Measurable (bvmBlockAvg kb (φt kb) nn) := by
    intro nn
    unfold bvmBlockAvg
    exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      (hφt_meas kb).comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _))
  have hSmeas : ∀ nn, MeasurableSet {ω : Fin nn → 𝓧 | 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω} :=
    fun nn => measurableSet_le measurable_const (hBAmeas nn)
  -- the boosted test: reject when at least half of the blocks reject
  have hIφ : ∀ (nn : ℕ) (ν : Measure (Fin nn → 𝓧)),
      ∫ ω, Set.indicator {ω | 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω} 1 ω ∂ν
        = ν.real {ω | 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω} :=
    fun nn _ => integral_indicator_one (hSmeas nn)
  have hI1φ : ∀ (nn : ℕ) (ν : Measure (Fin nn → 𝓧)),
      ∫ ω, (1 - Set.indicator {ω | 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω} 1 ω) ∂ν
        = ν.real {ω | bvmBlockAvg kb (φt kb) nn ω < 1 / 2} := by
    intro nn ν
    have hfun : (fun ω => 1 - Set.indicator {ω | 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω}
        (1 : (Fin nn → 𝓧) → ℝ) ω)
        = Set.indicator {ω | bvmBlockAvg kb (φt kb) nn ω < 1 / 2} 1 := by
      funext ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      by_cases h : 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω
      · rw [if_pos h, if_neg (not_lt.mpr h)]; norm_num
      · rw [if_neg h, if_pos (not_le.mp h)]; norm_num
    rw [hfun]
    exact integral_indicator_one (measurableSet_lt (hBAmeas nn) measurable_const)
  -- `⌊n/kb⌋ ≥ n/(2 kb)`, so the block-count rate dominates the linear rate `c n`
  have hrate : ∀ nn : ℕ, kb ≤ nn → Real.exp (-(↑(nn / kb) : ℝ) / 8)
      ≤ Real.exp (-(1 / (16 * (kb : ℝ))) * nn) := by
    intro nn hnn
    have hq : 1 ≤ nn / kb := (Nat.one_le_div_iff hkb0).mpr hnn
    have hnle : nn ≤ 2 * (kb * (nn / kb)) := by
      calc nn = kb * (nn / kb) + nn % kb := (Nat.div_add_mod nn kb).symm
        _ ≤ kb * (nn / kb) + kb := Nat.add_le_add_left (le_of_lt (Nat.mod_lt _ hkb0)) _
        _ ≤ kb * (nn / kb) + kb * (nn / kb) :=
            Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hq) _
        _ = 2 * (kb * (nn / kb)) := by ring
    have hnleR : (nn : ℝ) ≤ 2 * ((kb : ℝ) * ((nn / kb : ℕ) : ℝ)) := by exact_mod_cast hnle
    refine Real.exp_le_exp.mpr ?_
    have heq : ((nn / kb : ℕ) : ℝ) / 8 - (1 / (16 * (kb : ℝ))) * nn
        = (2 * ((kb : ℝ) * ((nn / kb : ℕ) : ℝ)) - nn) / (16 * (kb : ℝ)) := by
      field_simp; ring
    have hnn0 : (0 : ℝ) ≤ (2 * ((kb : ℝ) * ((nn / kb : ℕ) : ℝ)) - nn) / (16 * (kb : ℝ)) :=
      div_nonneg (by linarith) (by linarith)
    linarith
  have hexp0 : Tendsto (fun nn : ℕ => Real.exp (-(1 / (16 * (kb : ℝ))) * nn)) atTop (𝓝 0) := by
    have hb : ∀ nn : ℕ, Real.exp (-(1 / (16 * (kb : ℝ))) * nn)
        = Real.exp (-(1 / (16 * (kb : ℝ)))) ^ nn := by
      intro nn
      rw [← Real.exp_nat_mul]
      ring_nf
    simp only [hb]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_nonneg _)
      (Real.exp_lt_one_iff.mpr (by linarith))
  -- size bound at `θ₀` (upper tail, obtained from the lower tail for `1 − φt kb`)
  have hsize_bd : ∀ nn, kb ≤ nn →
      (productMeasure M μ θ₀ nn).real {ω | 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω}
        ≤ Real.exp (-(↑(nn / kb) : ℝ) / 8) := by
    intro nn hnn
    have hm : 1 ≤ nn / kb := (Nat.one_le_div_iff hkb0).mpr hnn
    have hmean : (3 : ℝ) / 4 ≤ ∫ ζ, (1 - φt kb ζ) ∂(productMeasure M μ θ₀ kb) := by
      rw [hsplit θ₀ kb]; linarith
    have h := blockAvg_le_half_tail
      (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)) hkb1
      (measurable_const.fun_sub (hφt_meas kb))
      (fun ζ => ⟨by linarith [(hφt01 kb ζ).2], by linarith [(hφt01 kb ζ).1]⟩) hmean hnn
    refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _)) h
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [bvmBlockAvg_one_sub _ hm]
    linarith
  -- type-II bound on the far range (lower tail for `φt kb`)
  have htII_bd : ∀ nn, kb ≤ nn → ∀ θ, ε ≤ ‖θ - θ₀‖ →
      (productMeasure M μ θ nn).real {ω | bvmBlockAvg kb (φt kb) nn ω < 1 / 2}
        ≤ Real.exp (-(↑(nn / kb) : ℝ) / 8) := by
    intro nn hnn θ hθ
    have hmean : (3 : ℝ) / 4 ≤ ∫ ζ, φt kb ζ ∂(productMeasure M μ θ kb) := by
      have h1 := hkbpow θ hθ
      rw [hsplit θ kb] at h1
      linarith
    exact blockAvg_typeII_tail hPDF hkb1 (hφt_meas kb) (hφt01 kb) θ hmean hnn
  refine ⟨fun nn => Set.indicator {ω | 1 / 2 ≤ bvmBlockAvg kb (φt kb) nn ω} 1,
    1 / (16 * (kb : ℝ)), hcpos, fun nn => measurable_one.indicator (hSmeas nn),
    ?_, ?_, kb, ?_⟩
  · intro nn ω
    simp only [Set.indicator_apply, Pi.one_apply, Set.mem_Icc]
    split_ifs <;> norm_num
  · refine squeeze_zero' (Filter.Eventually.of_forall fun nn => ?_) ?_ hexp0
    · rw [hIφ]
      exact measureReal_nonneg
    · filter_upwards [eventually_ge_atTop kb] with nn hnn
      rw [hIφ]
      exact le_trans (hsize_bd nn hnn) (hrate nn hnn)
  · intro nn hnn θ hθ
    rw [hI1φ]
    exact le_trans (htII_bd nn hnn θ hθ) (hrate nn hnn)

end StatLean.Bayesian
