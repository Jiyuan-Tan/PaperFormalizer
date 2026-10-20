module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropyBracketingTransfer
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalMeasure
public import StatLean.AsymptoticStatistics.EmpiricalProcess.GlivenkoCantelli
public import StatLean.AsymptoticStatistics.EmpiricalProcess.IIDFiniteRestriction
public import StatLean.AsymptoticStatistics.EmpiricalProcess.IIDChebyshev
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterPeeling
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-!
# Uniform-entropy symmetrization for Glivenko--Cantelli classes

This file formalizes the random-net symmetrization argument in van der Vaart
Theorem 19.13. Its
definitions expose the pooled empirical law, admissibility split, ghost
sample, and Rademacher tails; all are derived from the stated assumptions.

The corresponding `r = 2` results supply the pooled-law, admissibility,
strict-net, ghost-sample, and Rademacher ingredients for the uniform-entropy
Donsker theorem. This file does not state the separate pairwise/bracketing
result.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, Theorem 19.13,
p.274.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal
open scoped BigOperators ENNReal NNReal Topology

open UniformEntropyStructural

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Concrete laws, nets, deviations, and bad events -/

/-- The probability law pooling the population law and two empirical laws.

This is the three-way law used by the random-net argument for vdV Theorem
19.13.  Edge behavior: at `n = 0` both empirical measures are zero and the
formula has total value `3⁻¹ • P`; probability-law consumers require
`[NeZero n]`. -/
noncomputable def pooledEmpiricalLaw (P : Measure Ω) (n : ℕ)
    (z z' : Fin n → Ω) : Measure Ω :=
  (3 : ℝ≥0∞)⁻¹ • (P + empiricalMeasure n z + empiricalMeasure n z')

/-- The `Lʳ` localization cut out by a nonnegative envelope-power majorant.

This is the localization used in vdV Theorems 19.13--19.14: `V` majorizes
`|G|ʳ`, so the cutoff `V ≤ Mʳ` forces the localized envelope below `M`.
Edge behavior: nonpositive `M` retains the literal `ENNReal.ofReal M ^ r`
cutoff; theorem consumers assume `0 < M` and `1 ≤ r`. -/
def lpLocalization (V : Ω → ℝ≥0∞) (r M : ℝ) : Set Ω :=
  {x | V x ≤ ENNReal.ofReal M ^ r}

/-- A strict absolute finite `Lʳ(Q)` net whose centers remain inside `F`.

This is the finite-net object used in vdV Theorem 19.13 after normalizing the
relative uniform cover.  Edge behavior: the empty finset is a net exactly
when `F` is empty; nonpositive radii retain the literal strict inequality and
all theorem consumers assume a positive radius. -/
def IsStrictFiniteLpClassNet (F : Set (Ω → ℝ)) (Q : Measure Ω)
    (r ρ : ℝ) (T : Finset (Ω → ℝ)) : Prop :=
  (↑T : Set (Ω → ℝ)) ⊆ F ∧
    (∀ g ∈ T, MemLp g (ENNReal.ofReal r) Q) ∧
    ∀ f ∈ F, ∃ g ∈ T, outerLpNorm Q (f - g) r < ENNReal.ofReal ρ

/-- The outer supremum empirical deviation `‖Pₙ-P‖_F`.

This is vdV's Glivenko--Cantelli deviation.  Edge behavior: `n = 0` uses the
zero empirical average, and the supremum over the empty class is zero. -/
noncomputable def gcDeviation {Ξ : Type*} (F : Set (Ω → ℝ)) (P : Measure Ω)
    (X : ℕ → Ξ → Ω) (n : ℕ) (ξ : Ξ) : ℝ≥0∞ :=
  supNormOver F (fun f =>
    empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P)

/-- The outer supremum difference between empirical and ghost samples.

Edge behavior: `n = 0` and the empty class both give zero. -/
noncomputable def ghostDeviation {Ξ : Type*} (F : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ) (ξ ξ' : Ξ) : ℝ≥0∞ :=
  supNormOver F (fun f =>
    empiricalAvg f n (fun i : Fin n => X i.val ξ) -
      empiricalAvg f n (fun i : Fin n => X i.val ξ'))

/-- The Rademacher-signed ghost-sample deviation for a fixed sign vector.

Signs are represented concretely by `Bool`, with `true` equal to `+1` and
`false` equal to `-1`.  Edge behavior: `n = 0` gives zero. -/
noncomputable def signedGhostDeviation (F : Set (Ω → ℝ)) (n : ℕ)
    (z z' : Fin n → Ω) (σ : Fin n → Bool) : ℝ≥0∞ :=
  supNormOver F (fun f => (n : ℝ)⁻¹ * ∑ i,
    (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i)))

/-- Bad event for the empirical deviation at threshold `ε`.

Edge behavior: nonpositive `ε` keeps the literal strict comparison. -/
def gcBad {Ξ : Type*} (F : Set (Ω → ℝ)) (P : Measure Ω)
    (X : ℕ → Ξ → Ω) (n : ℕ) (ε : ℝ) : Set Ξ :=
  {ξ | ENNReal.ofReal ε < gcDeviation F P X n ξ}

/-- Bad event for the empirical-versus-ghost deviation at threshold `ε`.

Edge behavior: nonpositive `ε` keeps the literal strict comparison. -/
def ghostBad {Ξ : Type*} (F : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω)
    (n : ℕ) (ε : ℝ) : Set (Ξ × Ξ) :=
  {ξ | ENNReal.ofReal ε < ghostDeviation F X n ξ.1 ξ.2}

/-- Dyadic-block bad event: some empirical deviation between indices `m`
and `N` exceeds `ε`.

Edge behavior: if the interval is empty, the event is empty. -/
def gcBlockBad {Ξ : Type*} (F : Set (Ω → ℝ)) (P : Measure Ω)
    (X : ℕ → Ξ → Ω) (m N : ℕ) (ε : ℝ) : Set Ξ :=
  {ξ | ∃ n ∈ Finset.Icc m N, ENNReal.ofReal ε < gcDeviation F P X n ξ}

/-- Conditional Rademacher tail of the signed ghost deviation.

The sign law is the uniform law on the finite Boolean cube, hence exactly a
product of fair signs.  Edge behavior: `n = 0` uses the singleton empty cube. -/
noncomputable def conditionalRademacherTail (F : Set (Ω → ℝ)) (n : ℕ)
    (z z' : Fin n → Ω) (ε : ℝ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
    {σ | ENNReal.ofReal ε < signedGhostDeviation F n z z' σ}

/-- Conditional fair-sign tail of the maximum over the dyadic block
`m ≤ j ≤ 2m` and the finite-net-augmented class `E ∪ T`.

For an endpoint `j`, the statistic uses the first `j` paired differences and
is normalized by `m`, exactly as in the block-maximal step of vdV Theorem
19.13.  Under the strict class-net hypothesis `T ⊆ E`, the displayed union
equals `E`; retaining it makes the selected random net visible. Edge behavior:
if the endpoint interval or class is empty, the event is empty. -/
noncomputable def conditionalRademacherBlockMaxTail (E : Set (Ω → ℝ))
    (T : Finset (Ω → ℝ)) (m : ℕ) (z z' : Fin (2 * m) → Ω)
    (ε : ℝ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin (2 * m) → Bool)).toMeasure {σ |
    ∃ j ∈ Finset.Icc m (2 * m),
      ENNReal.ofReal ε < supNormOver (E ∪ (↑T : Set (Ω → ℝ))) (fun f =>
        (m : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => i.val < j),
          (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i)))}

private theorem outerLpNorm_eq_eLpNorm_of_aemeasurable
    (Q : Measure Ω) (f : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hf : AEMeasurable f Q) :
    outerLpNorm Q f r = eLpNorm f (ENNReal.ofReal r) Q := by
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hpow : AEMeasurable (fun x => ENNReal.ofReal |f x| ^ r) Q := by
    fun_prop
  rw [outerLpNorm, outerExpectation_eq_lintegral_of_aemeasurable Q _ hpow,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top]
  simp only [ENNReal.toReal_ofReal hr.le, one_div, Real.enorm_eq_ofReal_abs]

private theorem outerLpNorm_mono_abs
    (Q : Measure Ω) (f g : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hfg : ∀ x, |f x| ≤ |g x|) :
    outerLpNorm Q f r ≤ outerLpNorm Q g r := by
  unfold outerLpNorm
  apply ENNReal.rpow_le_rpow _ (by positivity)
  apply outerExpectation_mono
  intro x
  exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hfg x)) hr.le

private theorem outerLpNorm_localized_le_conditionOn
    (Q : Measure Ω) [IsProbabilityMeasure Q] (A : Set Ω) (hA : MeasurableSet A)
    (hQA : 0 < Q A) (f : Ω → ℝ) (r : ℝ) (hr : 0 < r)
    (hf : Measurable f) :
    outerLpNorm Q (localizedFunction A f) r ≤ outerLpNorm (conditionOn Q A) f r := by
  let R : Measure Ω := conditionOn Q A
  have hRprob : IsProbabilityMeasure R := conditionOn_isProbabilityMeasure Q A hA hQA
  letI : IsProbabilityMeasure R := hRprob
  let p : ℝ≥0∞ := ENNReal.ofReal r
  have hp_top : p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQR : Q.restrict A = Q A • R := by
    change Q.restrict A = Q A • ((Q A)⁻¹ • Q.restrict A)
    rw [smul_smul, ENNReal.mul_inv_cancel hQA.ne' (measure_ne_top Q A), one_smul]
  change outerLpNorm Q (A.indicator f) r ≤ outerLpNorm R f r
  rw [outerLpNorm_eq_eLpNorm_of_aemeasurable Q _ r hr
      (hf.indicator hA).aemeasurable,
    outerLpNorm_eq_eLpNorm_of_aemeasurable R f r hr hf.aemeasurable]
  change eLpNorm (A.indicator f) p Q ≤ eLpNorm f p R
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hA, hQR,
    eLpNorm_smul_measure_of_ne_top hp_top]
  have hQAone : Q A ≤ 1 := by
    simpa only [measure_univ] using
      measure_mono (μ := Q) (Set.subset_univ A : A ⊆ Set.univ)
  have hexp : 0 ≤ (1 / p).toReal := ENNReal.toReal_nonneg
  have hfac : Q A ^ (1 / p).toReal ≤ 1 := by
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hQAone hexp
  exact mul_le_of_le_one_left (zero_le) hfac

/-! ### Symmetrization ingredients -/

/-- The three-way pooled empirical law is a probability measure
for every nonempty finite sample. -/
theorem pooledEmpiricalLaw_isProbabilityMeasure
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) [NeZero n]
    (z z' : Fin n → Ω) : IsProbabilityMeasure (pooledEmpiricalLaw P n z z') := by
  refine ⟨?_⟩
  rw [pooledEmpiricalLaw, Measure.smul_apply, Measure.add_apply,
    Measure.add_apply, measure_univ, measure_univ, measure_univ]
  have hthree : (1 + 1 + 1 : ℝ≥0∞) = 3 := by norm_num
  rw [hthree, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (show (3 : ℝ≥0∞) ≠ 0 by norm_num) (show (3 : ℝ≥0∞) ≠ ⊤ by norm_num)

/-- Almost every pair of samples gives either zero pooled outer
envelope norm or an admissible pooled law.  This step uses no independence. -/
theorem ae_pooledEmpiricalLaw_admissibleOrZero
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ξ → Ω) (n : ℕ) [NeZero n] (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (r : ℝ)
    (hr : 1 ≤ r) -- book-facing exponents are at least one.
    (hVmeas : Measurable V) -- measurable outer majorant.
    (hGV : ∀ x, ENNReal.ofReal |G x| ^ r ≤ V x)
      -- envelope-power domination used for pooled integrability.
    (hVint : ∫⁻ x, V x ∂P < ⊤) -- finite majorant moment.
    (hXmeas : ∀ i, Measurable (X i)) -- random-variable measurability.
    (hXlaw : ∀ i, μ.map (X i) = P) -- common marginal laws.
    : ∀ᵐ ξ ∂μ.prod μ,
      outerLpNorm (pooledEmpiricalLaw P n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2)) G r = 0 ∨
      IsAdmissibleMeasure G r (pooledEmpiricalLaw P n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2)) := by
  have hVfiniteP : ∀ᵐ x ∂P, V x < ⊤ :=
    ae_lt_top hVmeas hVint.ne
  have hVfiniteX (i : ℕ) : ∀ᵐ ξ ∂μ, V (X i ξ) < ⊤ := by
    exact (MeasurePreserving.mk (hXmeas i) (hXlaw i)).quasiMeasurePreserving.ae hVfiniteP
  have hVfiniteAll : ∀ᵐ ξ ∂μ, ∀ i : Fin n, V (X i.val ξ) < ⊤ :=
    ae_all_iff.2 fun i => hVfiniteX i.val
  have hleft : ∀ᵐ ξ ∂μ.prod μ, ∀ i : Fin n, V (X i.val ξ.1) < ⊤ :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hVfiniteAll
  have hright : ∀ᵐ ξ ∂μ.prod μ, ∀ i : Fin n, V (X i.val ξ.2) < ⊤ :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hVfiniteAll
  filter_upwards [hleft, hright] with ξ hξ hξ'
  let Q : Measure Ω := pooledEmpiricalLaw P n
    (fun i => X i.val ξ.1) (fun i => X i.val ξ.2)
  have hQprob : IsProbabilityMeasure Q :=
    pooledEmpiricalLaw_isProbabilityMeasure P n _ _
  letI : IsProbabilityMeasure Q := hQprob
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hncast : (0 : ℝ≥0∞) < n := by exact_mod_cast hnpos
  have hVQ : (∫⁻ x, V x ∂Q) < ⊤ := by
    rw [show Q = pooledEmpiricalLaw P n
      (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) by rfl]
    simp only [pooledEmpiricalLaw, lintegral_smul_measure, lintegral_add_measure,
      empiricalMeasure, lintegral_finset_sum_measure, lintegral_dirac' _ hVmeas,
      smul_eq_mul]
    exact ENNReal.mul_lt_top (by norm_num) <|
      ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hVint,
        ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hncast) <|
          ENNReal.sum_lt_top.2 fun i _ => hξ i⟩,
        ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hncast) <|
          ENNReal.sum_lt_top.2 fun i _ => hξ' i⟩
  have houter : outerExpectation Q (fun x => ENNReal.ofReal |G x| ^ r) < ⊤ := by
    calc
      outerExpectation Q (fun x => ENNReal.ofReal |G x| ^ r)
          ≤ outerExpectation Q V := outerExpectation_mono hGV
      _ = ∫⁻ x, V x ∂Q := outerExpectation_eq_lintegral hVmeas
      _ < ⊤ := hVQ
  have hnorm : outerLpNorm Q G r < ⊤ := by
    unfold outerLpNorm
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) houter.ne
  rcases eq_or_ne (outerLpNorm Q G r) 0 with hzero | hzero
  · exact Or.inl hzero
  · exact Or.inr ⟨hQprob, pos_iff_ne_zero.mpr hzero, hnorm⟩

/-- Uniform relative covering yields a uniformly cardinal-bounded
strict absolute net for every localized pooled empirical law. -/
theorem exists_localizedPooledClassNet
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (r : ℝ)
    (hr : 1 ≤ r) -- book-facing exponents are at least one.
    (hVmeas : Measurable V) -- measurable localization set.
    (hGV : ∀ x, ENNReal.ofReal |G x| ^ r ≤ V x)
      -- envelope-power domination by the localizing majorant.
    (hFmeas : ∀ f ∈ F, Measurable f) -- measurable class members.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV envelope condition.
    (hcover : ∀ η > 0, uniformLpCoveringNumber F G r η < ⊤)
      -- vdV uniform finite Lr covering condition.
    {M ρ : ℝ}
    (hM : 0 < M) -- positive localization cutoff.
    (hρ : 0 < ρ) -- strict-net radius.
    : ∃ N : ℕ, ∀ (n : ℕ) [NeZero n] (P : Measure Ω) [IsProbabilityMeasure P]
        (z z' : Fin n → Ω), ∃ T : Finset (Ω → ℝ),
      T.card ≤ N ∧
      IsStrictFiniteLpClassNet
        (localizedClass F (lpLocalization V r M))
        (pooledEmpiricalLaw P n z z') r ρ T := by
  classical
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let A : Set Ω := lpLocalization V r M
  have hA : MeasurableSet A := by
    exact measurableSet_Iic.preimage hVmeas
  by_cases hF : F.Nonempty
  · obtain ⟨f₀, hf₀⟩ := hF
    let η : ℝ := ρ / (4 * M)
    have hη : 0 < η := div_pos hρ (mul_pos (by norm_num) hM)
    let K : ℕ∞ := uniformLpCoveringNumber F G r η
    have hKtop : K < ⊤ := hcover η hη
    let N : ℕ := K.toNat + 1
    refine ⟨N, ?_⟩
    intro n _ P _ z z'
    let Q : Measure Ω := pooledEmpiricalLaw P n z z'
    have hQprob : IsProbabilityMeasure Q := pooledEmpiricalLaw_isProbabilityMeasure P n z z'
    letI : IsProbabilityMeasure Q := hQprob
    have hloc_meas : ∀ f ∈ localizedClass F A, Measurable f := by
      rintro _ ⟨f, hf, rfl⟩
      exact measurable_localizedFunction A f hA (hFmeas f hf)
    have hloc_bound : ∀ f ∈ localizedClass F A, ∀ x, |f x| ≤ M := by
      rintro _ ⟨f, hf, rfl⟩ x
      by_cases hx : x ∈ A
      · have hpow : ENNReal.ofReal |G x| ^ r ≤ ENNReal.ofReal M ^ r :=
          (hGV x).trans hx
        have hGM : ENNReal.ofReal |G x| ≤ ENNReal.ofReal M :=
          (ENNReal.rpow_le_rpow_iff hrpos).mp hpow
        have hGMreal : |G x| ≤ M :=
          (ENNReal.ofReal_le_ofReal_iff hM.le).mp hGM
        simpa [localizedFunction, hx] using
          (hEnv.2 f hf x).trans ((le_abs_self (G x)).trans hGMreal)
      · simp [localizedFunction, hx, hM.le]
    have hsingleton (hzero : Q A = 0) :
        IsStrictFiniteLpClassNet (localizedClass F A) Q r ρ
          {localizedFunction A f₀} := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hg
        subst g
        exact ⟨f₀, hf₀, rfl⟩
      · intro g hg
        simp only [Finset.mem_singleton] at hg
        subst g
        exact MemLp.of_bound ((measurable_localizedFunction A f₀ hA
          (hFmeas f₀ hf₀)).aestronglyMeasurable) M
          (Eventually.of_forall fun x => hloc_bound _ ⟨f₀, hf₀, rfl⟩ x)
      · rintro g ⟨f, hf, rfl⟩
        refine ⟨localizedFunction A f₀, Finset.mem_singleton_self _, ?_⟩
        have hsub : localizedFunction A f - localizedFunction A f₀ =
            localizedFunction A (f - f₀) := by
          funext x
          by_cases hx : x ∈ A <;> simp [localizedFunction, hx]
        have hsubmeas : AEMeasurable (localizedFunction A (f - f₀)) Q :=
          (measurable_localizedFunction A (f - f₀) hA
            ((hFmeas f hf).sub (hFmeas f₀ hf₀))).aemeasurable
        rw [hsub, outerLpNorm_eq_eLpNorm_of_aemeasurable Q _ r hrpos hsubmeas]
        change eLpNorm (A.indicator (f - f₀)) (ENNReal.ofReal r) Q < _
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hA,
          Measure.restrict_eq_zero.mpr hzero]
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
          (ENNReal.ofReal_pos.mpr hrpos).ne' ENNReal.ofReal_ne_top]
        simpa only [Pi.sub_apply, lintegral_zero_measure, one_div,
          ENNReal.toReal_ofReal hrpos.le,
          ENNReal.zero_rpow_of_pos (inv_pos.mpr hrpos), ENNReal.ofReal_pos] using hρ
    by_cases hQA : Q A = 0
    · refine ⟨{localizedFunction A f₀}, ?_, hsingleton hQA⟩
      simp [N]
    · have hQApos : 0 < Q A := pos_iff_ne_zero.mpr hQA
      let R : Measure Ω := conditionOn Q A
      have hRprob : IsProbabilityMeasure R := conditionOn_isProbabilityMeasure Q A hA hQApos
      letI : IsProbabilityMeasure R := hRprob
      have hRA : ∀ᵐ x ∂R, x ∈ A := by
        change ∀ᵐ x ∂(Q A)⁻¹ • Q.restrict A, x ∈ A
        exact Measure.ae_smul_measure
          ((ae_restrict_iff' hA).2 (Filter.Eventually.of_forall fun _ hx => hx)) _
      have hGnorm : outerLpNorm R G r ≤ ENNReal.ofReal M := by
        unfold outerLpNorm
        have houter : outerExpectation R (fun x => ENNReal.ofReal |G x| ^ r) ≤
            ENNReal.ofReal M ^ r := by
          let Z : Ω → ℝ≥0∞ := fun x =>
            if x ∈ A then ENNReal.ofReal |G x| ^ r else 0
          have hZeq : (fun x => ENNReal.ofReal |G x| ^ r) =ᵐ[R] Z :=
            hRA.mono fun x hx => by simp [Z, hx]
          calc
            outerExpectation R (fun x => ENNReal.ofReal |G x| ^ r)
                = outerExpectation R Z := outerExpectation_congr_ae hZeq
            _ ≤ outerExpectation R (fun _ => ENNReal.ofReal M ^ r) := by
                  apply outerExpectation_mono
                  intro x
                  by_cases hx : x ∈ A
                  · simpa [Z, hx] using (hGV x).trans hx
                  · simp [Z, hx]
            _ = ENNReal.ofReal M ^ r := by
              rw [outerExpectation_const, measure_univ, mul_one]
        calc
          (outerExpectation R (fun x => ENNReal.ofReal |G x| ^ r)) ^ r⁻¹
              ≤ (ENNReal.ofReal M ^ r) ^ r⁻¹ :=
                ENNReal.rpow_le_rpow houter (by positivity)
          _ = ENNReal.ofReal M := by
            rw [← ENNReal.rpow_mul]
            field_simp
            simp
      by_cases hGzero : outerLpNorm R G r = 0
      · refine ⟨{localizedFunction A f₀}, by simp [N], ?_⟩
        refine ⟨?_, ?_, ?_⟩
        · intro g hg
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hg
          subst g
          exact ⟨f₀, hf₀, rfl⟩
        · intro g hg
          simp only [Finset.mem_singleton] at hg
          subst g
          exact MemLp.of_bound ((measurable_localizedFunction A f₀ hA
            (hFmeas f₀ hf₀)).aestronglyMeasurable) M
            (Eventually.of_forall fun x => hloc_bound _ ⟨f₀, hf₀, rfl⟩ x)
        · rintro g ⟨f, hf, rfl⟩
          refine ⟨localizedFunction A f₀, Finset.mem_singleton_self _, ?_⟩
          have hfR : outerLpNorm R (f - f₀) r = 0 := by
            have hfzero : outerLpNorm R f r = 0 := by
              apply le_antisymm
              · rw [← hGzero]
                exact outerLpNorm_mono_abs R f G r hrpos fun x =>
                  (hEnv.2 f hf x).trans_eq (abs_of_nonneg (hEnv.1 x)).symm
              · exact bot_le
            have hf₀zero : outerLpNorm R f₀ r = 0 := by
              apply le_antisymm
              · rw [← hGzero]
                exact outerLpNorm_mono_abs R f₀ G r hrpos fun x =>
                  (hEnv.2 f₀ hf₀ x).trans_eq (abs_of_nonneg (hEnv.1 x)).symm
              · exact bot_le
            change outerLpNorm R (fun x => f x - f₀ x) r = 0
            rw [outerLpNorm_eq_eLpNorm_of_aemeasurable R _ r hrpos
              ((hFmeas f hf).fun_sub (hFmeas f₀ hf₀)).aemeasurable]
            rw [outerLpNorm_eq_eLpNorm_of_aemeasurable R f r hrpos
              (hFmeas f hf).aemeasurable] at hfzero
            rw [outerLpNorm_eq_eLpNorm_of_aemeasurable R f₀ r hrpos
              (hFmeas f₀ hf₀).aemeasurable] at hf₀zero
            apply le_antisymm
            · refine (eLpNorm_sub_le (hFmeas f hf).aestronglyMeasurable
                (hFmeas f₀ hf₀).aestronglyMeasurable ?_).trans ?_
              · exact ENNReal.one_le_ofReal.mpr hr
              · rw [hfzero, hf₀zero, add_zero]
            · exact bot_le
          have hsub : localizedFunction A f - localizedFunction A f₀ =
              localizedFunction A (f - f₀) := by
            funext x
            by_cases hx : x ∈ A <;> simp [localizedFunction, hx]
          rw [hsub]
          calc
            outerLpNorm Q (localizedFunction A (f - f₀)) r
                ≤ outerLpNorm R (f - f₀) r :=
                  outerLpNorm_localized_le_conditionOn Q A hA hQApos
                    (f - f₀) r hrpos ((hFmeas f hf).sub (hFmeas f₀ hf₀))
            _ = 0 := hfR
            _ < ENNReal.ofReal ρ := ENNReal.ofReal_pos.mpr hρ
      · have hGpos : 0 < outerLpNorm R G r := pos_iff_ne_zero.mpr hGzero
        have hGtop : outerLpNorm R G r < ⊤ :=
          hGnorm.trans_lt ENNReal.ofReal_lt_top
        have hRadm : IsAdmissibleMeasure G r R := ⟨hRprob, hGpos, hGtop⟩
        have hnum_le : finiteLpCoveringNumber F G R r η ≤ K := by
          dsimp [K]
          unfold uniformLpCoveringNumber
          exact le_iSup_of_le R (le_iSup_of_le hRadm le_rfl)
        have hKcoe : K = (K.toNat : ℕ∞) := (ENat.coe_toNat hKtop.ne).symm
        have hNcoe : K < (N : ℕ∞) := by
          rw [hKcoe]
          exact_mod_cast Nat.lt_succ_self K.toNat
        have hnum_lt : finiteLpCoveringNumber F G R r η < (N : ℕ∞) :=
          hnum_le.trans_lt hNcoe
        unfold finiteLpCoveringNumber at hnum_lt
        rw [iInf_lt_iff] at hnum_lt
        obtain ⟨S, hS⟩ := hnum_lt
        rw [iInf_lt_iff] at hS
        obtain ⟨hScover, hScard⟩ := hS
        let Good : (Ω → ℝ) → Prop := fun g =>
          ∃ f ∈ F, outerLpNorm R (f - g) r <
            ENNReal.ofReal η * outerLpNorm R G r
        let rep : (Ω → ℝ) → (Ω → ℝ) := fun g =>
          if hg : Good g then Classical.choose hg else f₀
        have hrep (g : Ω → ℝ) (hg : Good g) :
            rep g ∈ F ∧ outerLpNorm R (rep g - g) r <
              ENNReal.ofReal η * outerLpNorm R G r := by
          simpa only [rep, dif_pos hg] using Classical.choose_spec hg
        let S' : Finset (Ω → ℝ) := S.filter Good
        let T : Finset (Ω → ℝ) := S'.image (fun g => localizedFunction A (rep g))
        refine ⟨T, ?_, ?_⟩
        · calc
            T.card ≤ S'.card := Finset.card_image_le
            _ ≤ S.card := Finset.card_filter_le _ _
            _ ≤ N := (by exact_mod_cast hScard : S.card < N).le
        · refine ⟨?_, ?_, ?_⟩
          · intro g hg
            rw [Finset.coe_image] at hg
            obtain ⟨s, hsS', rfl⟩ := hg
            have hsGood : Good s := (Finset.mem_filter.mp hsS').2
            exact ⟨rep s, (hrep s hsGood).1, rfl⟩
          · intro g hg
            rw [Finset.mem_image] at hg
            obtain ⟨s, hsS', rfl⟩ := hg
            have hsGood : Good s := (Finset.mem_filter.mp hsS').2
            have hmem : localizedFunction A (rep s) ∈ localizedClass F A :=
              ⟨rep s, (hrep s hsGood).1, rfl⟩
            exact MemLp.of_bound (hloc_meas _ hmem).aestronglyMeasurable M
              (Eventually.of_forall fun x => hloc_bound _ hmem x)
          · rintro _ ⟨f, hf, rfl⟩
            obtain ⟨g, hgS, hfg⟩ := hScover.2 f hf
            have hgGood : Good g := ⟨f, hf, hfg⟩
            have hgS' : g ∈ S' := Finset.mem_filter.mpr ⟨hgS, hgGood⟩
            refine ⟨localizedFunction A (rep g),
              Finset.mem_image.mpr ⟨g, hgS', rfl⟩, ?_⟩
            have hrep' := (hrep g hgGood).2
            have hfg_meas : AEMeasurable (f - g) R :=
              (hFmeas f hf).aemeasurable.sub (hScover.1 g hgS).aemeasurable
            have hrg_meas : AEMeasurable (rep g - g) R :=
              (hFmeas (rep g) (hrep g hgGood).1).aemeasurable.sub
                (hScover.1 g hgS).aemeasurable
            rw [outerLpNorm_eq_eLpNorm_of_aemeasurable R _ r hrpos hfg_meas] at hfg
            rw [outerLpNorm_eq_eLpNorm_of_aemeasurable R _ r hrpos hrg_meas] at hrep'
            have htri : eLpNorm (f - rep g) (ENNReal.ofReal r) R ≤
                eLpNorm (f - g) (ENNReal.ofReal r) R +
                  eLpNorm (rep g - g) (ENNReal.ofReal r) R := by
              have hid : f - rep g = (f - g) - (rep g - g) := by
                funext x
                simp only [Pi.sub_apply]
                ring
              rw [hid]
              exact eLpNorm_sub_le hfg_meas.aestronglyMeasurable
                hrg_meas.aestronglyMeasurable (ENNReal.one_le_ofReal.mpr hr)
            have hRlt : outerLpNorm R (f - rep g) r < ENNReal.ofReal ρ := by
              change outerLpNorm R (fun x => f x - rep g x) r < ENNReal.ofReal ρ
              rw [outerLpNorm_eq_eLpNorm_of_aemeasurable R _ r hrpos
                ((hFmeas f hf).fun_sub (hFmeas (rep g) (hrep g hgGood).1)).aemeasurable]
              refine htri.trans_lt ((ENNReal.add_lt_add hfg hrep').trans_le ?_)
              calc
                (ENNReal.ofReal η * outerLpNorm R G r) +
                    ENNReal.ofReal η * outerLpNorm R G r
                    = 2 * (ENNReal.ofReal η * outerLpNorm R G r) := by ring
                _ ≤ 2 * (ENNReal.ofReal η * ENNReal.ofReal M) := by gcongr
                _ = ENNReal.ofReal (ρ / 2) := by
                  rw [← ENNReal.ofReal_mul hη.le]
                  norm_num [η]
                  field_simp
                  rw [← ENNReal.ofReal_ofNat 2,
                    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
                  congr 1
                  ring
                _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (by linarith)
            have hsub : localizedFunction A f - localizedFunction A (rep g) =
                localizedFunction A (f - rep g) := by
              funext x
              by_cases hx : x ∈ A <;> simp [localizedFunction, hx]
            rw [hsub]
            exact (outerLpNorm_localized_le_conditionOn Q A hA hQApos
              (f - rep g) r hrpos
              ((hFmeas f hf).sub (hFmeas (rep g) (hrep g hgGood).1))).trans_lt hRlt
  · refine ⟨0, ?_⟩
    intro n _ P _ z z'
    refine ⟨∅, by simp, ?_⟩
    refine ⟨?_, by simp, ?_⟩
    · intro g hg
      obtain ⟨f, hf, rfl⟩ := hg
    rintro f ⟨g, hg, rfl⟩
    exact (hF ⟨g, hg⟩).elim

/-- For a uniformly bounded class of measurable functions, the
empirical deviation is eventually controlled by the independent ghost-sample
deviation in outer probability. Pointwise measurability is not needed for this
single-witness symmetrization step. -/
private theorem outerMeasureStar_le_measure_symm
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (A : Set Ξ) :
    μ.outerMeasureStar A ≤ μ A := by
  rw [measure_eq_iInf]
  refine le_iInf fun t => le_iInf fun hAt => le_iInf fun ht => ?_
  rw [Measure.outerMeasureStar, outerExpectation]
  calc
    (⨅ U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U},
        ∫⁻ x, (U : Ξ → ℝ≥0∞) x ∂μ)
        ≤ ∫⁻ x, t.indicator 1 x ∂μ :=
      iInf_le (fun U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U} =>
        ∫⁻ x, (U : Ξ → ℝ≥0∞) x ∂μ)
        ⟨t.indicator 1, measurable_one.indicator ht, fun x => by
        by_cases hx : x ∈ A
        · simp [hx, hAt hx]
        · simp [hx]⟩
    _ = μ t := lintegral_indicator_one ht

private theorem outerMeasureStar_le_two_prod_of_sections
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (A : Set Ξ) (B : Set (Ξ × Ξ))
    (hsec : ∀ x ∈ A, (2 : ℝ≥0∞)⁻¹ ≤ μ (Prod.mk x ⁻¹' B)) :
    μ.outerMeasureStar A ≤ 2 * (μ.prod μ).outerMeasureStar B := by
  let C : Set (Ξ × Ξ) := toMeasurable (μ.prod μ) B
  have hCmeas : MeasurableSet C := measurableSet_toMeasurable _ _
  let D : Set Ξ := {x | (2 : ℝ≥0∞)⁻¹ ≤ μ (Prod.mk x ⁻¹' C)}
  have hDmeas : MeasurableSet D :=
    measurableSet_le measurable_const (measurable_measure_prodMk_left hCmeas)
  have hAD : A ⊆ D := by
    intro x hx
    exact (hsec x hx).trans (measure_mono fun y hy => subset_toMeasurable _ _ hy)
  have hhalf : (2 : ℝ≥0∞)⁻¹ * μ D ≤ μ.prod μ C := by
    rw [Measure.prod_apply hCmeas]
    calc
      (2 : ℝ≥0∞)⁻¹ * μ D =
          ∫⁻ x, D.indicator (fun _ => (2 : ℝ≥0∞)⁻¹) x ∂μ := by
            rw [lintegral_indicator hDmeas]
            simp
      _ ≤ ∫⁻ x, μ (Prod.mk x ⁻¹' C) ∂μ := by
        apply lintegral_mono
        intro x
        by_cases hx : x ∈ D
        · simpa [D, Set.indicator_of_mem hx] using hx
        · simp [Set.indicator_of_notMem hx]
  have houter : (μ.prod μ).outerMeasureStar B = μ.prod μ B :=
    le_antisymm (outerMeasureStar_le_measure_symm _ _) (measure_le_outerMeasureStar _ _)
  calc
    μ.outerMeasureStar A ≤ μ A := outerMeasureStar_le_measure_symm μ A
    _ ≤ μ D := measure_mono hAD
    _ = 2 * ((2 : ℝ≥0∞)⁻¹ * μ D) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 2 * μ.prod μ C := mul_le_mul_right hhalf 2
    _ = 2 * (μ.prod μ).outerMeasureStar B := by
      rw [houter, show μ.prod μ C = μ.prod μ B from measure_toMeasurable B]

private theorem bounded_iid_empirical_close_half
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (M ε : ℝ)
    (hFmeas : ∀ f ∈ E, Measurable f)
    (hbdd : ∀ f ∈ E, ∀ x, |f x| ≤ M)
    (hε : 0 < ε)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f ∈ E,
      (2 : ℝ≥0∞)⁻¹ ≤ μ {ξ |
        |empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P| < ε / 2} := by
  classical
  let B : ℝ := max M 0
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (8 * B ^ 2 / ε ^ 2)
  refine ⟨max 1 N₀, ?_⟩
  intro n hn f hf
  have hn₀ : N₀ ≤ n := (le_max_right 1 N₀).trans hn
  have hnpos : 0 < n := (le_max_left 1 N₀).trans hn
  have hnlarge : 8 * B ^ 2 / ε ^ 2 < (n : ℝ) := hN₀.trans_le (by exact_mod_cast hn₀)
  have hBnonneg : 0 ≤ B := le_max_right M 0
  have hfbdd : ∀ x, |f x| ≤ B := fun x => (hbdd f hf x).trans (le_max_left M 0)
  have hfL2 : MemLp f 2 P := MemLp.of_bound (hFmeas f hf).aestronglyMeasurable B
    (Eventually.of_forall hfbdd)
  have hf2int : ∫ x, f x ^ 2 ∂P ≤ B ^ 2 := by
    have hf2_integrable : Integrable (fun x => f x ^ 2) P := by
      simpa only [Pi.pow_apply] using hfL2.integrable_sq
    calc
      ∫ x, f x ^ 2 ∂P ≤ ∫ _x, B ^ 2 ∂P :=
        integral_mono_ae hf2_integrable (integrable_const _) (ae_of_all _ fun x => by
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (f x)) (hfbdd x) 2)
      _ = B ^ 2 := by simp
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have hthreshold : 0 < Real.sqrt (n : ℝ) * δ := mul_pos hsqrtn hδ
  let bad : Set Ξ := {ξ |
    δ ≤ |empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P|}
  have hbad_eq : bad = {ξ |
      Real.sqrt (n : ℝ) * δ ≤
        |empiricalProcess P n (fun i : Fin n => X i.val ξ) f|} := by
    ext ξ
    simp only [bad, Set.mem_setOf_eq, empiricalProcess, abs_mul,
      abs_of_pos hsqrtn]
    constructor <;> intro h <;> nlinarith [abs_nonneg
      (empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P)]
  have hcheb := empiricalProcess_chebyshev_tail P μ X hXmeas hXiindep hXid hXlaw
    n f hfL2 hthreshold
  have hratio : B ^ 2 / (Real.sqrt (n : ℝ) * δ) ^ 2 ≤ 1 / 2 := by
    have hepssq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hmul : 8 * B ^ 2 < (n : ℝ) * ε ^ 2 :=
      (div_lt_iff₀ hepssq).mp hnlarge
    have hden : 0 < (Real.sqrt (n : ℝ) * δ) ^ 2 := sq_pos_of_pos hthreshold
    apply (div_le_iff₀ hden).2
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
    dsimp [δ]
    nlinarith
  have hbad : μ bad ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [hbad_eq]
    calc
      μ {ξ | Real.sqrt (n : ℝ) * δ ≤
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) f|}
          ≤ ENNReal.ofReal ((∫ x, f x ^ 2 ∂P) /
            (Real.sqrt (n : ℝ) * δ) ^ 2) := hcheb
      _ ≤ ENNReal.ofReal (B ^ 2 / (Real.sqrt (n : ℝ) * δ) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        exact div_le_div_of_nonneg_right hf2int (sq_nonneg _)
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hratio
      _ = (2 : ℝ≥0∞)⁻¹ := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
  have havg_meas : Measurable (fun ξ =>
      empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P) := by
    unfold empiricalAvg
    apply Measurable.sub ?_ measurable_const
    apply Measurable.const_mul
    exact Finset.measurable_sum _ fun i _ =>
      (hFmeas f hf).comp (hXmeas i.val)
  have hbad_meas : MeasurableSet bad := by
    exact measurableSet_le measurable_const havg_meas.abs
  have hgood_eq : {ξ |
      |empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P| < ε / 2} = badᶜ := by
    ext ξ
    simp only [bad, δ, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  have hbadtop : μ bad ≠ ⊤ :=
    ne_of_lt (hbad.trans_lt (by norm_num : (2 : ℝ≥0∞)⁻¹ < ⊤))
  rw [hgood_eq, measure_compl hbad_meas hbadtop, measure_univ]
  apply ENNReal.le_sub_of_add_le_left hbadtop
  calc
    μ bad + (2 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ :=
      by simpa [add_comm] using add_le_add_left hbad (2 : ℝ≥0∞)⁻¹
    _ = 1 := by
      rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem empirical_ghost_symmetrization_outer
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (M ε : ℝ)
    (hFmeas : ∀ f ∈ E, Measurable f) -- measurable class members.
    (hbdd : ∀ f ∈ E, ∀ x, |f x| ≤ M) -- localized boundedness.
    (hε : 0 < ε) -- positive deviation threshold.
    (hXmeas : ∀ i, Measurable (X i)) -- coordinate measurability.
    (hXiindep : ProbabilityTheory.iIndepFun X μ) -- iid independence.
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
      -- identical marginals.
    (hXlaw : μ.map (X 0) = P) -- common law.
    : ∃ N : ℕ, ∀ n ≥ N,
      μ.outerMeasureStar (gcBad E P X n ε) ≤
        2 * (μ.prod μ).outerMeasureStar (ghostBad E X n (ε / 2)) := by
  classical
  obtain ⟨N, hclose⟩ := bounded_iid_empirical_close_half μ P E X M ε
    hFmeas hbdd hε hXmeas hXiindep hXid hXlaw
  refine ⟨N, fun n hn => outerMeasureStar_le_two_prod_of_sections μ
    (gcBad E P X n ε) (ghostBad E X n (ε / 2)) ?_⟩
  intro ξ hξ
  rw [gcBad, Set.mem_setOf_eq, gcDeviation, supNormOver] at hξ
  rw [lt_iSup_iff] at hξ
  obtain ⟨f, hξ⟩ := hξ
  rw [lt_iSup_iff] at hξ
  obtain ⟨hf, hξf⟩ := hξ
  have hdev : ε <
      |empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P| :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp hξf
  refine (hclose n hn f hf).trans (measure_mono ?_)
  intro ξ' hξ'
  simp only [Set.mem_setOf_eq] at hξ'
  change ENNReal.ofReal (ε / 2) < ghostDeviation E X n ξ ξ'
  rw [ghostDeviation]
  have hdiff : ε / 2 <
      |empiricalAvg f n (fun i : Fin n => X i.val ξ) -
        empiricalAvg f n (fun i : Fin n => X i.val ξ')| := by
    have htri := abs_sub_le
      (empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P)
      (empiricalAvg f n (fun i : Fin n => X i.val ξ') - ∫ x, f x ∂P)
      0
    have hid :
        (empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P) -
          (empiricalAvg f n (fun i : Fin n => X i.val ξ') - ∫ x, f x ∂P) =
        empiricalAvg f n (fun i : Fin n => X i.val ξ) -
          empiricalAvg f n (fun i : Fin n => X i.val ξ') := by ring
    rw [sub_zero, sub_zero, hid] at htri
    linarith
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity : 0 ≤ ε / 2)).mpr hdiff |>.trans_le
    (le_supNormOver hf)

omit [MeasurableSpace Ω] in
private theorem supNormOver_pairSum_eq_skeleton
    (E E₀ : Set (Ω → ℝ)) (hE₀sub : E₀ ⊆ E)
    (hE₀dense : ∀ f ∈ E, ∃ g : ℕ → (Ω → ℝ),
      (∀ k, g k ∈ E₀) ∧ ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x)))
    (n : ℕ) (z z' : Fin n → Ω) (a : Fin n → ℝ) :
    supNormOver E (fun f => (n : ℝ)⁻¹ * ∑ i, a i * (f (z i) - f (z' i))) =
      supNormOver E₀ (fun f => (n : ℝ)⁻¹ * ∑ i, a i * (f (z i) - f (z' i))) := by
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    obtain ⟨g, hgmem, hglim⟩ := hE₀dense f hf
    have hsum : Tendsto
        (fun k => (n : ℝ)⁻¹ * ∑ i, a i * (g k (z i) - g k (z' i)))
        atTop (𝓝 ((n : ℝ)⁻¹ * ∑ i, a i * (f (z i) - f (z' i)))) := by
      apply tendsto_const_nhds.mul
      apply tendsto_finset_sum
      intro i _
      exact tendsto_const_nhds.mul ((hglim (z i)).sub (hglim (z' i)))
    apply le_of_tendsto'
      ((ENNReal.continuous_ofReal.tendsto _).comp
        ((continuous_abs.tendsto _).comp hsum))
    intro k
    exact le_iSup_of_le (g k) (le_iSup_of_le (hgmem k) le_rfl)
  · refine iSup_le fun f => iSup_le fun hf => ?_
    exact le_iSup_of_le f (le_iSup_of_le (hE₀sub hf) le_rfl)

omit [MeasurableSpace Ω] in
private theorem supNormOver_eq_iSup_subtype
    (E : Set (Ω → ℝ)) (L : (Ω → ℝ) → ℝ) :
    supNormOver E L = ⨆ f : E, ENNReal.ofReal |L f| := by
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    exact le_iSup_of_le (⟨f, hf⟩ : E) le_rfl
  · refine iSup_le fun f => ?_
    exact le_iSup_of_le f.1 (le_iSup_of_le f.2 le_rfl)

private theorem measurable_ghostDeviation
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ)
    (hEmeas : ∀ f ∈ E, Measurable f)
    (hPM : IsPointwiseMeasurable E)
    (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (fun ξ : Ξ × Ξ => ghostDeviation E X n ξ.1 ξ.2) := by
  classical
  obtain ⟨E₀, hE₀count, hE₀sub, hE₀dense⟩ := hPM
  letI : Countable E₀ := hE₀count
  have heq (ξ : Ξ × Ξ) :
      ghostDeviation E X n ξ.1 ξ.2 =
        supNormOver E₀ (fun f =>
          empiricalAvg f n (fun i : Fin n => X i.val ξ.1) -
            empiricalAvg f n (fun i : Fin n => X i.val ξ.2)) := by
    rw [ghostDeviation]
    have hfun : (fun f =>
        empiricalAvg f n (fun i : Fin n => X i.val ξ.1) -
          empiricalAvg f n (fun i : Fin n => X i.val ξ.2)) =
        fun f => (n : ℝ)⁻¹ * ∑ i : Fin n, (1 : ℝ) *
          (f (X i.val ξ.1) - f (X i.val ξ.2)) := by
      funext f
      unfold empiricalAvg
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      simp only [one_mul]
    rw [hfun, supNormOver_pairSum_eq_skeleton E E₀ hE₀sub hE₀dense]
  simp_rw [heq]
  simp only [supNormOver_eq_iSup_subtype]
  apply Measurable.iSup
  intro f
  unfold empiricalAvg
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.sub
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun i _ =>
      (hEmeas f (hE₀sub f.property)).comp ((hXmeas i.val).comp measurable_fst)
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun i _ =>
      (hEmeas f (hE₀sub f.property)).comp ((hXmeas i.val).comp measurable_snd)

private theorem measurable_signedGhostDeviation
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ) (σ : Fin n → Bool)
    (hEmeas : ∀ f ∈ E, Measurable f)
    (hPM : IsPointwiseMeasurable E)
    (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (fun ξ : Ξ × Ξ => signedGhostDeviation E n
      (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ) := by
  classical
  obtain ⟨E₀, hE₀count, hE₀sub, hE₀dense⟩ := hPM
  letI : Countable E₀ := hE₀count
  have heq (ξ : Ξ × Ξ) :
      signedGhostDeviation E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) σ =
        supNormOver E₀ (fun f => (n : ℝ)⁻¹ * ∑ i,
          (if σ i then (1 : ℝ) else -1) *
            (f (X i.val ξ.1) - f (X i.val ξ.2))) := by
    rw [signedGhostDeviation]
    exact supNormOver_pairSum_eq_skeleton E E₀ hE₀sub hE₀dense n _ _ _
  simp_rw [heq]
  simp only [supNormOver_eq_iSup_subtype]
  apply Measurable.iSup
  intro f
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ =>
    (((hEmeas f.1 (hE₀sub f.property)).comp
        ((hXmeas i.val).comp measurable_fst)).sub
      ((hEmeas f.1 (hE₀sub f.property)).comp
        ((hXmeas i.val).comp measurable_snd))).const_mul _

private def pairedFiniteSample {Ξ : Type*} (X : ℕ → Ξ → Ω) (n : ℕ) :
    Ξ × Ξ → Fin n → Ω × Ω :=
  fun ξ i => (X i.val ξ.1, X i.val ξ.2)

private def swapFinitePairs {n : ℕ} (σ : Fin n → Bool) :
    (Fin n → Ω × Ω) → Fin n → Ω × Ω :=
  fun z i => if σ i then z i else (z i).swap

private noncomputable def pairedGhostDeviation (E : Set (Ω → ℝ)) (n : ℕ)
    (z : Fin n → Ω × Ω) : ℝ≥0∞ :=
  supNormOver E (fun f => (n : ℝ)⁻¹ * Finset.univ.sum
    (fun i : Fin n => f (z i).1 - f (z i).2))

private theorem measurable_pairedFiniteSample
    {Ξ : Type*} [MeasurableSpace Ξ] (X : ℕ → Ξ → Ω) (n : ℕ)
    (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (pairedFiniteSample X n) := by
  apply measurable_pi_lambda
  intro i
  exact ((hXmeas i.val).comp measurable_fst).prodMk
    ((hXmeas i.val).comp measurable_snd)

private theorem map_pairedFiniteSample_eq_pi_prod_map
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (n : ℕ)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ) :
    (μ.prod μ).map (pairedFiniteSample X n) =
      Measure.pi (fun i : Fin n =>
        (μ.map (X i.val)).prod (μ.map (X i.val))) := by
  let S : Ξ → Fin n → Ω := fun ξ i => X i.val ξ
  let q : Fin n → Measure Ω := fun i => μ.map (X i.val)
  have hSmeas : Measurable S := measurable_pi_lambda _ fun i => hXmeas i.val
  have hSmap : μ.map S = Measure.pi q := by
    exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin n => (hXmeas i.val).aemeasurable)).mp
        (hXiindep.precomp Fin.val_injective)
  let e := MeasurableEquiv.arrowProdEquivProdArrow Ω Ω (Fin n)
  rw [show pairedFiniteSample X n =
      e.symm ∘ Prod.map S S by
    funext ξ i
    rfl]
  rw [← Measure.map_map e.symm.measurable (hSmeas.prodMap hSmeas)]
  rw [← Measure.map_prod_map μ μ hSmeas hSmeas, hSmap]
  exact (measurePreserving_arrowProdEquivProdArrow Ω Ω (Fin n) q q).symm.map_eq

private theorem measurePreserving_swapFinitePairs
    {n : ℕ} (q : Fin n → Measure Ω) (σ : Fin n → Bool)
    [∀ i, IsProbabilityMeasure (q i)] :
    MeasurePreserving (swapFinitePairs σ)
      (Measure.pi fun i => (q i).prod (q i))
      (Measure.pi fun i => (q i).prod (q i)) := by
  change MeasurePreserving
    (fun z i => if σ i then z i else (z i).swap)
    (Measure.pi fun i => (q i).prod (q i))
    (Measure.pi fun i => (q i).prod (q i))
  exact measurePreserving_pi
    (fun i => (q i).prod (q i)) (fun i => (q i).prod (q i))
    (f := fun i z => if σ i then z else z.swap) fun i => by
      by_cases hi : σ i = true
      · simpa [hi] using!
          (MeasurePreserving.id (μ := (q i).prod (q i)))
      · have hi' : σ i = false := Bool.eq_false_of_not_eq_true hi
        simpa [hi'] using
          (Measure.measurePreserving_swap (μ := q i) (ν := q i))

private theorem measurable_pairGhostDeviation
    (E : Set (Ω → ℝ)) (n : ℕ)
    (hEmeas : ∀ f ∈ E, Measurable f)
    (hPM : IsPointwiseMeasurable E) :
    Measurable (pairedGhostDeviation E n) := by
  classical
  obtain ⟨E₀, hE₀count, hE₀sub, hE₀dense⟩ := hPM
  letI : Countable E₀ := hE₀count
  unfold pairedGhostDeviation
  have heq (z : Fin n → Ω × Ω) :
      supNormOver E (fun f : Ω → ℝ => (n : ℝ)⁻¹ * Finset.univ.sum
        (fun i : Fin n => f (z i).1 - f (z i).2)) =
        supNormOver E₀ (fun f : Ω → ℝ => (n : ℝ)⁻¹ * Finset.univ.sum
          (fun i : Fin n => f (z i).1 - f (z i).2)) := by
    have hfun : (fun f : Ω → ℝ => (n : ℝ)⁻¹ * Finset.univ.sum
        (fun i : Fin n => f (z i).1 - f (z i).2)) =
        fun f : Ω → ℝ => (n : ℝ)⁻¹ * Finset.univ.sum
          (fun i : Fin n => (1 : ℝ) * (f (z i).1 - f (z i).2)) := by
      funext f
      simp only [one_mul]
    rw [hfun, supNormOver_pairSum_eq_skeleton E E₀ hE₀sub hE₀dense n
      (fun i => (z i).1) (fun i => (z i).2) (fun _ => 1)]
  simp_rw [heq]
  simp only [supNormOver_eq_iSup_subtype]
  apply Measurable.iSup
  intro f
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ =>
    ((hEmeas f.1 (hE₀sub f.property)).comp
      (measurable_fst.comp (measurable_pi_apply i))).sub
    ((hEmeas f.1 (hE₀sub f.property)).comp
      (measurable_snd.comp (measurable_pi_apply i)))

omit [MeasurableSpace Ω] in
private theorem pairedGhostDeviation_pairedFiniteSample
    {Ξ : Type*} (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (n : ℕ) (ξ : Ξ × Ξ) :
    pairedGhostDeviation E n (pairedFiniteSample X n ξ) =
      ghostDeviation E X n ξ.1 ξ.2 := by
  unfold pairedGhostDeviation pairedFiniteSample ghostDeviation empiricalAvg
  congr 2 with f
  rw [← mul_sub, ← Finset.sum_sub_distrib]

omit [MeasurableSpace Ω] in
private theorem pairedGhostDeviation_swap_pairedFiniteSample
    {Ξ : Type*} (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (n : ℕ)
    (σ : Fin n → Bool) (ξ : Ξ × Ξ) :
    pairedGhostDeviation E n (swapFinitePairs σ (pairedFiniteSample X n ξ)) =
      signedGhostDeviation E n (fun i => X i.val ξ.1)
        (fun i => X i.val ξ.2) σ := by
  unfold pairedGhostDeviation swapFinitePairs pairedFiniteSample signedGhostDeviation
  congr 2 with f
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ i = true
  · simp [hi]
  · have hi' : σ i = false := Bool.eq_false_of_not_eq_true hi
    simp [hi']

/-- Swapping each measurable empirical/ghost pair converts the
ghost tail to the conditional fair-sign tail. Pointwise measurability makes
the class supremum accessible without assuming identical coordinate laws. -/
theorem ghostSwap_rademacher_outer_le
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (n : ℕ) (ε : ℝ)
    (hEmeas : ∀ f ∈ E, Measurable f) -- measurable class members.
    (hPM : IsPointwiseMeasurable E) -- suitable measurability.
    (hXmeas : ∀ i, Measurable (X i)) -- coordinate measurability.
    (hXiindep : ProbabilityTheory.iIndepFun X μ) -- iid independence.
    : (μ.prod μ).outerMeasureStar (ghostBad E X n ε) ≤
      outerExpectation (μ.prod μ) (fun ξ => conditionalRademacherTail E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) ε) := by
  classical
  let q : Fin n → Measure Ω := fun i => μ.map (X i.val)
  letI (i : Fin n) : IsProbabilityMeasure (q i) := by
    refine ⟨?_⟩
    dsimp [q]
    rw [Measure.map_apply (hXmeas i.val) MeasurableSet.univ]
    simp
  let D : Set (Fin n → Ω × Ω) :=
    {z | ENNReal.ofReal ε < pairedGhostDeviation E n z}
  let A : (Fin n → Bool) → Set (Ξ × Ξ) := fun σ =>
    {ξ | ENNReal.ofReal ε < signedGhostDeviation E n
      (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ}
  have hpairedMeas : Measurable (pairedFiniteSample X n) :=
    measurable_pairedFiniteSample X n hXmeas
  have hDmeas : MeasurableSet D :=
    measurableSet_lt measurable_const
      (measurable_pairGhostDeviation E n hEmeas hPM)
  have hAmeas (σ : Fin n → Bool) : MeasurableSet (A σ) := by
    exact measurableSet_lt measurable_const
      (measurable_signedGhostDeviation E X n σ hEmeas hPM hXmeas)
  have hpairedLaw : (μ.prod μ).map (pairedFiniteSample X n) =
      Measure.pi (fun i : Fin n => (q i).prod (q i)) := by
    simpa [q] using
      map_pairedFiniteSample_eq_pi_prod_map μ X n hXmeas hXiindep
  have hswap (σ : Fin n → Bool) :
      MeasurePreserving (swapFinitePairs σ)
        (Measure.pi fun i : Fin n => (q i).prod (q i))
        (Measure.pi fun i : Fin n => (q i).prod (q i)) :=
    measurePreserving_swapFinitePairs q σ
  have hghostPreimage :
      pairedFiniteSample X n ⁻¹' D = ghostBad E X n ε := by
    ext ξ
    change ENNReal.ofReal ε < pairedGhostDeviation E n
        (pairedFiniteSample X n ξ) ↔
      ENNReal.ofReal ε < ghostDeviation E X n ξ.1 ξ.2
    rw [pairedGhostDeviation_pairedFiniteSample]
  have hswapPreimage (σ : Fin n → Bool) :
      (swapFinitePairs σ ∘ pairedFiniteSample X n) ⁻¹' D = A σ := by
    ext ξ
    change ENNReal.ofReal ε < pairedGhostDeviation E n
        (swapFinitePairs σ (pairedFiniteSample X n ξ)) ↔
      ENNReal.ofReal ε < signedGhostDeviation E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ
    rw [pairedGhostDeviation_swap_pairedFiniteSample]
  have hswapLaw (σ : Fin n → Bool) :
      (μ.prod μ).map (swapFinitePairs σ ∘ pairedFiniteSample X n) =
        (μ.prod μ).map (pairedFiniteSample X n) := by
    rw [← Measure.map_map (hswap σ).measurable hpairedMeas, hpairedLaw,
      (hswap σ).map_eq]
  have hbadMeasure (σ : Fin n → Bool) :
      (μ.prod μ) (ghostBad E X n ε) = (μ.prod μ) (A σ) := by
    calc
      (μ.prod μ) (ghostBad E X n ε) =
          (μ.prod μ) (pairedFiniteSample X n ⁻¹' D) := by rw [hghostPreimage]
      _ = ((μ.prod μ).map (pairedFiniteSample X n)) D :=
        (Measure.map_apply hpairedMeas hDmeas).symm
      _ = ((μ.prod μ).map
          (swapFinitePairs σ ∘ pairedFiniteSample X n)) D := by rw [hswapLaw]
      _ = (μ.prod μ)
          ((swapFinitePairs σ ∘ pairedFiniteSample X n) ⁻¹' D) :=
        Measure.map_apply ((hswap σ).measurable.comp hpairedMeas) hDmeas
      _ = (μ.prod μ) (A σ) := by rw [hswapPreimage]
  let c : ℝ≥0∞ := (Fintype.card (Fin n → Bool) : ℝ≥0∞)⁻¹
  have htail (ξ : Ξ × Ξ) :
      conditionalRademacherTail E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) ε =
        ∑ σ : Fin n → Bool, (A σ).indicator (fun _ => c) ξ := by
    rw [conditionalRademacherTail, PMF.toMeasure_apply_fintype]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : ENNReal.ofReal ε < signedGhostDeviation E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ
    · simp [hσ, A, c]
    · simp [hσ, A, c]
  have htailMeas : Measurable (fun ξ : Ξ × Ξ =>
      conditionalRademacherTail E n (fun i => X i.val ξ.1)
        (fun i => X i.val ξ.2) ε) := by
    simp_rw [htail]
    exact Finset.measurable_sum _ fun σ _ => measurable_const.indicator (hAmeas σ)
  have htailIntegral :
      ∫⁻ ξ, conditionalRademacherTail E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) ε ∂(μ.prod μ) =
        (μ.prod μ) (ghostBad E X n ε) := by
    calc
      ∫⁻ ξ, conditionalRademacherTail E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) ε ∂(μ.prod μ) =
          ∫⁻ ξ, ∑ σ : Fin n → Bool,
            (A σ).indicator (fun _ => c) ξ ∂(μ.prod μ) :=
        lintegral_congr htail
      _ = ∑ σ : Fin n → Bool,
          ∫⁻ ξ, (A σ).indicator (fun _ => c) ξ ∂(μ.prod μ) := by
        rw [lintegral_finset_sum]
        intro σ _
        exact measurable_const.indicator (hAmeas σ)
      _ = ∑ σ : Fin n → Bool, c * (μ.prod μ) (A σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        exact lintegral_indicator_const (hAmeas σ) c
      _ = ∑ _σ : Fin n → Bool, c * (μ.prod μ) (ghostBad E X n ε) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [hbadMeasure σ]
      _ = (μ.prod μ) (ghostBad E X n ε) := by
        unfold c
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel]
        · simp
        · exact_mod_cast Fintype.card_ne_zero
        · simp
  calc
    (μ.prod μ).outerMeasureStar (ghostBad E X n ε) ≤
        (μ.prod μ) (ghostBad E X n ε) :=
      outerMeasureStar_le_measure_symm _ _
    _ = outerExpectation (μ.prod μ) (fun ξ => conditionalRademacherTail E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) ε) := by
      rw [outerExpectation_eq_lintegral htailMeas, htailIntegral]

private theorem map_uniformOfFintype_involutive
    {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → α) (hf : Function.Involutive f) :
    Measure.map f (PMF.uniformOfFintype α).toMeasure =
      (PMF.uniformOfFintype α).toMeasure := by
  rw [PMF.toMeasure_map f _ (measurable_of_finite f)]
  congr 1
  ext y
  rw [PMF.map_apply, tsum_eq_single (f y)]
  · simp [hf y]
  · intro x hx
    simp only [ite_eq_right_iff]
    intro hyx
    exfalso
    apply hx
    rw [← hf x, ← hyx]

private noncomputable def rademacherPartialSum {N : ℕ}
    (a : Fin N → ℝ) (σ : Fin N → Bool) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j),
    (if σ i then (1 : ℝ) else -1) * a i

private def HasRademacherCrossing {N : ℕ}
    (a : Fin N → ℝ) (t : ℝ) (σ : Fin N → Bool) : Prop :=
  ∃ j, j ≤ N ∧ t ≤ rademacherPartialSum a σ j

private noncomputable def firstRademacherCrossing {N : ℕ}
    (a : Fin N → ℝ) (t : ℝ) (σ : Fin N → Bool) : ℕ := by
  classical
  exact if h : HasRademacherCrossing a t σ then Nat.find h else N

private noncomputable def reflectAfterFirstCrossing {N : ℕ}
    (a : Fin N → ℝ) (t : ℝ) (σ : Fin N → Bool) : Fin N → Bool :=
  fun i => if firstRademacherCrossing a t σ ≤ i.val then !σ i else σ i

private theorem rademacherPartialSum_reflect_of_le_first
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) (σ : Fin N → Bool)
    {j : ℕ} (hj : j ≤ firstRademacherCrossing a t σ) :
    rademacherPartialSum a (reflectAfterFirstCrossing a t σ) j =
      rademacherPartialSum a σ j := by
  unfold rademacherPartialSum
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i.val < j := (Finset.mem_filter.mp hi).2
  have hnot : ¬firstRademacherCrossing a t σ ≤ i.val :=
    not_le.mpr (lt_of_lt_of_le hij hj)
  simp [reflectAfterFirstCrossing, hnot]

private theorem firstRademacherCrossing_reflect
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) (σ : Fin N → Bool) :
    firstRademacherCrossing a t (reflectAfterFirstCrossing a t σ) =
      firstRademacherCrossing a t σ := by
  classical
  by_cases h : HasRademacherCrossing a t σ
  · have hτ : firstRademacherCrossing a t σ = Nat.find h := by
      simp [firstRademacherCrossing, h]
    have hspec : Nat.find h ≤ N ∧
        t ≤ rademacherPartialSum a σ (Nat.find h) := Nat.find_spec h
    have hspec' : Nat.find h ≤ N ∧
        t ≤ rademacherPartialSum a (reflectAfterFirstCrossing a t σ) (Nat.find h) := by
      rw [rademacherPartialSum_reflect_of_le_first a t σ (by rw [hτ])]
      exact hspec
    have h' : HasRademacherCrossing a t (reflectAfterFirstCrossing a t σ) :=
      ⟨Nat.find h, hspec'⟩
    rw [firstRademacherCrossing, dif_pos h', hτ]
    symm
    apply Nat.find_congr (q := fun j => j ≤ N ∧
      t ≤ rademacherPartialSum a (reflectAfterFirstCrossing a t σ) j)
      (Nat.find_spec h)
    intro j hj
    rw [rademacherPartialSum_reflect_of_le_first a t σ]
    rw [hτ]
    exact hj
  · have hrefl : reflectAfterFirstCrossing a t σ = σ := by
      funext i
      have hi : ¬N ≤ i.val := not_le.mpr i.isLt
      simp [reflectAfterFirstCrossing, firstRademacherCrossing, h, hi]
    rw [hrefl]

private theorem reflectAfterFirstCrossing_involutive
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) :
    Function.Involutive (reflectAfterFirstCrossing a t) := by
  intro σ
  funext i
  rw [reflectAfterFirstCrossing, firstRademacherCrossing_reflect]
  by_cases hi : firstRademacherCrossing a t σ ≤ i.val
  · simp [reflectAfterFirstCrossing, hi]
  · simp [reflectAfterFirstCrossing, hi]

private theorem rademacherPartialSum_reflect_terminal
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) (σ : Fin N → Bool) :
    rademacherPartialSum a (reflectAfterFirstCrossing a t σ) N =
      2 * rademacherPartialSum a σ (firstRademacherCrossing a t σ) -
        rademacherPartialSum a σ N := by
  unfold rademacherPartialSum
  have hN : Finset.univ.filter (fun i : Fin N => i.val < N) = Finset.univ :=
    Finset.filter_eq_self.mpr fun i _ => i.isLt
  rw [hN, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : firstRademacherCrossing a t σ ≤ i.val
  · have hi' : ¬i.val < firstRademacherCrossing a t σ := not_lt.mpr hi
    cases hσ : σ i <;> simp [reflectAfterFirstCrossing, hi, hi', hσ]
  · have hi' : i.val < firstRademacherCrossing a t σ := lt_of_not_ge hi
    cases hσ : σ i <;> simp [reflectAfterFirstCrossing, hi, hi', hσ]
    <;> ring

private theorem firstRademacherCrossing_spec
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) (σ : Fin N → Bool)
    (h : HasRademacherCrossing a t σ) :
    firstRademacherCrossing a t σ ≤ N ∧
      t ≤ rademacherPartialSum a σ (firstRademacherCrossing a t σ) := by
  simpa [firstRademacherCrossing, h] using Nat.find_spec h

private theorem uniform_max_partial_le_two_terminal
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) :
    let ν := (PMF.uniformOfFintype (Fin N → Bool)).toMeasure
    ν {σ | HasRademacherCrossing a t σ} ≤
      2 * ν {σ | t ≤ rademacherPartialSum a σ N} := by
  classical
  let ν := (PMF.uniformOfFintype (Fin N → Bool)).toMeasure
  let B : Set (Fin N → Bool) := {σ | HasRademacherCrossing a t σ}
  let C : Set (Fin N → Bool) := {σ | t ≤ rademacherPartialSum a σ N}
  let R := reflectAfterFirstCrossing a t
  have hsub : B ⊆ C ∪ R ⁻¹' C := by
    intro σ hσ
    by_cases hterm : t ≤ rademacherPartialSum a σ N
    · exact Or.inl hterm
    · right
      change t ≤ rademacherPartialSum a (reflectAfterFirstCrossing a t σ) N
      rw [rademacherPartialSum_reflect_terminal]
      have hfirst := (firstRademacherCrossing_spec a t σ hσ).2
      linarith
  have hmap : Measure.map R ν = ν :=
    map_uniformOfFintype_involutive R (reflectAfterFirstCrossing_involutive a t)
  have hpre : ν (R ⁻¹' C) = ν C := by
    rw [← Measure.map_apply (measurable_of_finite R) (Set.toFinite C).measurableSet,
      hmap]
  calc
    ν B ≤ ν (C ∪ R ⁻¹' C) := measure_mono hsub
    _ ≤ ν C + ν (R ⁻¹' C) := measure_union_le _ _
    _ = 2 * ν C := by rw [hpre, two_mul]

private noncomputable def fairBoolMeasure : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

private instance : IsProbabilityMeasure fairBoolMeasure := by
  unfold fairBoolMeasure
  infer_instance

private def fairBoolSign (b : Bool) : ℝ := if b then 1 else -1

private theorem integral_fairBoolSign :
    ∫ b, fairBoolSign b ∂fairBoolMeasure = 0 := by
  rw [fairBoolMeasure, PMF.integral_eq_sum]
  simp [fairBoolSign]

private theorem fairBoolSign_hasSubgaussianMGF :
    ProbabilityTheory.HasSubgaussianMGF fairBoolSign 1 fairBoolMeasure := by
  have hmeas : AEMeasurable fairBoolSign fairBoolMeasure :=
    (measurable_of_finite fairBoolSign).aemeasurable
  have hbound : ∀ᵐ b ∂fairBoolMeasure, fairBoolSign b ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall fun b => by cases b <;> simp [fairBoolSign]
  convert ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := fairBoolSign) (μ := fairBoolMeasure) hmeas hbound integral_fairBoolSign using 1
  norm_num

private noncomputable def fairBoolCube (N : ℕ) : Measure (Fin N → Bool) :=
  Measure.pi (fun _ => fairBoolMeasure)

private instance (N : ℕ) : IsProbabilityMeasure (fairBoolCube N) := by
  unfold fairBoolCube
  infer_instance

private theorem fairBoolCube_eq_uniform (N : ℕ) :
    fairBoolCube N = (PMF.uniformOfFintype (Fin N → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro σ
  have hpoint (b : Bool) : fairBoolMeasure {b} = (2 : ℝ≥0∞)⁻¹ := by
    rw [fairBoolMeasure, PMF.toMeasure_apply_singleton,
      PMF.uniformOfFintype_apply, Fintype.card_bool]
    · norm_num
    · exact MeasurableSet.singleton b
  rw [fairBoolCube, Measure.pi_singleton, PMF.toMeasure_apply_fintype]
  simp_rw [hpoint]
  simp only [Set.indicator_singleton, PMF.uniformOfFintype_apply, Fintype.card_pi,
    Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Finset.sum_pi_single', Finset.mem_univ, if_true]
  exact ENNReal.inv_pow.symm

private theorem rademacherPartialSum_hasSubgaussianMGF
    {N : ℕ} (a : Fin N → ℝ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun σ : Fin N → Bool => rademacherPartialSum a σ N)
      (∑ i, ⟨(a i) ^ 2, sq_nonneg (a i)⟩)
      (PMF.uniformOfFintype (Fin N → Bool)).toMeasure := by
  have hindep : ProbabilityTheory.iIndepFun
      (fun i (σ : Fin N → Bool) => a i * fairBoolSign (σ i))
      (fairBoolCube N) := by
    unfold fairBoolCube
    have heval := ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin N => fairBoolMeasure)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    simpa [Function.comp_def] using heval.comp
      (fun i b => a i * fairBoolSign b) (fun _ => measurable_of_finite _)
  have hcoord (i : Fin N) : ProbabilityTheory.HasSubgaussianMGF
      (fun σ : Fin N → Bool => a i * fairBoolSign (σ i))
      ⟨(a i) ^ 2, sq_nonneg (a i)⟩ (fairBoolCube N) := by
    have hmapped : ProbabilityTheory.HasSubgaussianMGF
        (fun b => a i * fairBoolSign b) ⟨(a i) ^ 2, sq_nonneg (a i)⟩
        ((fairBoolCube N).map fun σ => σ i) := by
      rw [fairBoolCube,
        (measurePreserving_eval (fun _ : Fin N => fairBoolMeasure) i).map_eq]
      have h := fairBoolSign_hasSubgaussianMGF.const_mul (a i)
      have e : (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : NNReal) * 1 = ⟨(a i) ^ 2, sq_nonneg (a i)⟩ :=
        mul_one _
      exact e ▸ h
    simpa [Function.comp_def] using ProbabilityTheory.HasSubgaussianMGF.of_map
      (μ := fairBoolCube N) (Y := fun σ : Fin N → Bool => σ i)
      (X := fun b => a i * fairBoolSign b)
      (measurable_pi_apply i).aemeasurable hmapped
  rw [← fairBoolCube_eq_uniform N]
  have hsum := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
    (s := Finset.univ) hindep (fun i _ => hcoord i)
  simpa [rademacherPartialSum, fairBoolSign] using hsum

private theorem hasSubgaussianMGF_mono_proxy
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {Y : α → ℝ}
    {c d : ℝ≥0} (h : ProbabilityTheory.HasSubgaussianMGF Y c μ)
    (hcd : c ≤ d) : ProbabilityTheory.HasSubgaussianMGF Y d μ := by
  refine ⟨h.integrable_exp_mul, fun t => ?_⟩
  calc
    ProbabilityTheory.mgf Y μ t ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := h.mgf_le t
    _ ≤ Real.exp ((d : ℝ) * t ^ 2 / 2) := by gcongr

private theorem rademacherPartialSum_neg
    {N : ℕ} (a : Fin N → ℝ) (σ : Fin N → Bool) (j : ℕ) :
    rademacherPartialSum (-a) σ j = -rademacherPartialSum a σ j := by
  unfold rademacherPartialSum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp

private theorem uniform_abs_max_partial_tail
    {N : ℕ} (a : Fin N → ℝ) (t : ℝ) (v : ℝ≥0)
    (ht : 0 ≤ t)
    (hv : (∑ i, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : ℝ≥0)) ≤ v) :
    let ν := (PMF.uniformOfFintype (Fin N → Bool)).toMeasure
    ν {σ | ∃ j, j ≤ N ∧ t ≤ |rademacherPartialSum a σ j|} ≤
      4 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by
  classical
  let ν := (PMF.uniformOfFintype (Fin N → Bool)).toMeasure
  let B : Set (Fin N → Bool) :=
    {σ | ∃ j, j ≤ N ∧ t ≤ |rademacherPartialSum a σ j|}
  let Bpos : Set (Fin N → Bool) := {σ | HasRademacherCrossing a t σ}
  let Bneg : Set (Fin N → Bool) := {σ | HasRademacherCrossing (-a) t σ}
  let Cpos : Set (Fin N → Bool) := {σ | t ≤ rademacherPartialSum a σ N}
  let Cneg : Set (Fin N → Bool) := {σ | t ≤ rademacherPartialSum (-a) σ N}
  have hB : B ⊆ Bpos ∪ Bneg := by
    rintro σ ⟨j, hj, habs⟩
    rw [le_abs] at habs
    rcases habs with hpos | hneg
    · exact Or.inl ⟨j, hj, hpos⟩
    · exact Or.inr ⟨j, hj, by simpa [rademacherPartialSum_neg] using hneg⟩
  have hposLe : ν Bpos ≤ 2 * ν Cpos :=
    uniform_max_partial_le_two_terminal a t
  have hnegLe : ν Bneg ≤ 2 * ν Cneg :=
    uniform_max_partial_le_two_terminal (-a) t
  have hsubGpos := hasSubgaussianMGF_mono_proxy
    (rademacherPartialSum_hasSubgaussianMGF a) hv
  have hvneg : (∑ i,
      (⟨((-a) i) ^ 2, sq_nonneg ((-a) i)⟩ : ℝ≥0)) ≤ v := by
    simpa using hv
  have hsubGneg := hasSubgaussianMGF_mono_proxy
    (rademacherPartialSum_hasSubgaussianMGF (-a)) hvneg
  have hCpos : ν Cpos ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [ν, Cpos] using hsubGpos.measure_ge_le ht)
  have hCneg : ν Cneg ≤
      ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [ν, Cneg] using hsubGneg.measure_ge_le ht)
  calc
    ν B ≤ ν (Bpos ∪ Bneg) := measure_mono hB
    _ ≤ ν Bpos + ν Bneg := measure_union_le _ _
    _ ≤ 2 * ν Cpos + 2 * ν Cneg := add_le_add hposLe hnegLe
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) +
        2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by gcongr
    _ = 4 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by ring

private theorem pooled_close_sample_sum
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r ρ : ℝ) (m : ℕ) (z z' : Fin (2 * m) → Ω)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hr : 1 ≤ r) (hm : 0 < m) (hρ : 0 < ρ)
    (hclose : outerLpNorm (pooledEmpiricalLaw P (2 * m) z z') (f - g) r <
      ENNReal.ofReal ρ) :
    ∑ i : Fin (2 * m),
      (|(f - g) (z i)| + |(f - g) (z' i)|) < 6 * m * ρ := by
  let Q := pooledEmpiricalLaw P (2 * m) z z'
  haveI : NeZero (2 * m) := ⟨by positivity⟩
  letI : IsProbabilityMeasure Q := pooledEmpiricalLaw_isProbabilityMeasure P _ z z'
  have hfg : Measurable (f - g) := hf.sub hg
  have hL1 : outerLpNorm Q (f - g) 1 < ENNReal.ofReal ρ := by
    calc
      outerLpNorm Q (f - g) 1 = eLpNorm (f - g) 1 Q := by
        simpa using outerLpNorm_eq_eLpNorm_of_aemeasurable Q (f - g) 1
          zero_lt_one hfg.aemeasurable
      _ ≤ eLpNorm (f - g) (ENNReal.ofReal r) Q :=
        eLpNorm_le_eLpNorm_of_exponent_le
          (by simpa using ENNReal.ofReal_le_ofReal hr) hfg.aestronglyMeasurable
      _ = outerLpNorm Q (f - g) r := by
        symm
        exact outerLpNorm_eq_eLpNorm_of_aemeasurable Q (f - g) r
          (lt_of_lt_of_le zero_lt_one hr) hfg.aemeasurable
      _ < ENNReal.ofReal ρ := hclose
  let S : ℝ≥0∞ := ∑ i : Fin (2 * m),
    (ENNReal.ofReal |(f - g) (z i)| + ENNReal.ofReal |(f - g) (z' i)|)
  have hdirac (x : Ω) :
      (∫⁻ y, ENNReal.ofReal |(f - g) y| ∂Measure.dirac x) =
        ENNReal.ofReal |(f - g) x| := by
    exact lintegral_dirac' _ hfg.abs.ennreal_ofReal
  have hdiracSum (w : Fin (2 * m) → Ω) :
      (∑ i, ∫⁻ y, ENNReal.ofReal |f y - g y| ∂Measure.dirac (w i)) =
        ∑ i, ENNReal.ofReal |f (w i) - g (w i)| := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Pi.sub_apply] using hdirac (w i)
  have hsumENN : (3 : ℝ≥0∞)⁻¹ * ((2 * m : ℕ) : ℝ≥0∞)⁻¹ * S <
      ENNReal.ofReal ρ := by
    calc
      (3 : ℝ≥0∞)⁻¹ * ((2 * m : ℕ) : ℝ≥0∞)⁻¹ * S ≤
          ∫⁻ x, ENNReal.ofReal |(f - g) x| ∂Q := by
        dsimp [S, Q]
        simp only [pooledEmpiricalLaw, lintegral_smul_measure,
          lintegral_add_measure, empiricalMeasure, lintegral_finset_sum_measure,
          smul_eq_mul]
        rw [hdiracSum z, hdiracSum z']
        rw [Finset.sum_add_distrib]
        ring_nf
        exact le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ by positivity)
      _ = outerLpNorm Q (f - g) 1 := by
        rw [show outerLpNorm Q (f - g) 1 = eLpNorm (f - g) 1 Q by
          simpa using outerLpNorm_eq_eLpNorm_of_aemeasurable Q (f - g) 1
            zero_lt_one hfg.aemeasurable, eLpNorm_one_eq_lintegral_enorm]
        congr 1
        funext x
        exact (Real.enorm_eq_ofReal_abs _).symm
      _ < ENNReal.ofReal ρ := hL1
  have hStop : S ≠ ⊤ := by
    dsimp [S]
    change Finset.univ.sum (fun i =>
      (ENNReal.ofReal |(f - g) (z i)| + ENNReal.ofReal |(f - g) (z' i)|)) ≠ ⊤
    exact ENNReal.sum_ne_top.mpr fun i _ => by finiteness
  have hprodtop : (3 : ℝ≥0∞)⁻¹ * ((2 * m : ℕ) : ℝ≥0∞)⁻¹ * S ≠ ⊤ := by
    finiteness
  have hreal := (ENNReal.toReal_lt_toReal hprodtop ENNReal.ofReal_ne_top).2 hsumENN
  have hStoReal : S.toReal = ∑ i : Fin (2 * m),
      (|(f - g) (z i)| + |(f - g) (z' i)|) := by
    dsimp [S]
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i _
      simp [ENNReal.toReal_add, abs_nonneg]
    · intro i _
      finiteness
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, hStoReal,
    ENNReal.toReal_ofReal hρ.le] at hreal
  norm_num at hreal ⊢
  field_simp at hreal
  nlinarith

/-- Conditional finite-net block tail bound.

The bound uses an explicitly extracted strict class net. -/
theorem conditionalRademacher_finitePooledNet_blockMaxTail
    (E : Set (Ω → ℝ)) (P : Measure Ω) [IsProbabilityMeasure P]
    (r : ℝ) (m : ℕ) (M ε : ℝ) (T : Finset (Ω → ℝ))
    (hr : 1 ≤ r) -- book-facing exponents are at least one.
    (hm : 0 < m) -- nonempty dyadic block.
    (hM : 0 < M) -- positive localized bound.
    (hε : 0 < ε) -- positive tail threshold.
    (z z' : Fin (2 * m) → Ω)
    (hEmeas : ∀ f ∈ E, Measurable f) -- measurable class members.
    (hbdd : ∀ f ∈ E, ∀ x, |f x| ≤ M) -- localized boundedness.
    (hT : IsStrictFiniteLpClassNet E (pooledEmpiricalLaw P (2 * m) z z')
      r (ε / 16) T)
      -- concrete net extracted from the uniform cover.
    : conditionalRademacherBlockMaxTail E T m z z' ε ≤
      2 * T.card * ENNReal.ofReal
        (Real.exp (-((m : ℝ) * ε ^ 2) / (128 * M ^ 2))) := by
  classical
  rcases hT with ⟨hTsub, hTlp, hnet⟩
  let ν := (PMF.uniformOfFintype (Fin (2 * m) → Bool)).toMeasure
  let B : Set (Fin (2 * m) → Bool) := {σ |
    ∃ j ∈ Finset.Icc m (2 * m),
      ENNReal.ofReal ε < supNormOver (E ∪ (↑T : Set (Ω → ℝ))) (fun f =>
        (m : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => i.val < j),
          (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i)))}
  let C (g : T) : Set (Fin (2 * m) → Bool) := {σ |
    ∃ j, j ≤ 2 * m ∧ (m : ℝ) * ε / 2 ≤
      |rademacherPartialSum (fun i => g.1 (z i) - g.1 (z' i)) σ j|}
  have hBsub : B ⊆ ⋃ g : T, C g := by
    intro σ hσ
    rcases hσ with ⟨j, hj, hdev⟩
    rw [supNormOver, lt_iSup_iff] at hdev
    obtain ⟨f, hdev⟩ := hdev
    rw [lt_iSup_iff] at hdev
    obtain ⟨hf, hdev⟩ := hdev
    have hfE : f ∈ E := hf.elim id fun hfT => hTsub hfT
    have hfmeas := hEmeas f hfE
    obtain ⟨g, hgT, hfgclose⟩ := hnet f hfE
    have hgE : g ∈ E := hTsub hgT
    have hgmeas := hEmeas g hgE
    have hdevReal : ε <
        |(m : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter
          (fun i : Fin (2 * m) => i.val < j),
            (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i))| :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp hdev
    have hfull := pooled_close_sample_sum P r (ε / 16) m z z' f g
      hfmeas hgmeas hr hm (by positivity) hfgclose
    have hfull' : ∑ i : Fin (2 * m),
        (|(f - g) (z i)| + |(f - g) (z' i)|) <
          (3 / 8 : ℝ) * m * ε := by
      convert hfull using 1
      ring
    let I := Finset.univ.filter (fun i : Fin (2 * m) => i.val < j)
    have herrSum :
        |∑ i ∈ I, (if σ i then (1 : ℝ) else -1) *
          ((f - g) (z i) - (f - g) (z' i))| <
            (3 / 8 : ℝ) * m * ε := by
      calc
        |∑ i ∈ I, (if σ i then (1 : ℝ) else -1) *
            ((f - g) (z i) - (f - g) (z' i))| ≤
            ∑ i ∈ I, |(if σ i then (1 : ℝ) else -1) *
              ((f - g) (z i) - (f - g) (z' i))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ I, (|(f - g) (z i)| + |(f - g) (z' i)|) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hσi : σ i
          · simpa [hσi] using abs_sub ((f - g) (z i)) ((f - g) (z' i))
          · simpa [hσi, add_comm] using
              abs_sub ((f - g) (z' i)) ((f - g) (z i))
        _ ≤ ∑ i : Fin (2 * m),
            (|(f - g) (z i)| + |(f - g) (z' i)|) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
        _ < (3 / 8 : ℝ) * m * ε := hfull'
    let Af : ℝ := (m : ℝ)⁻¹ * ∑ i ∈ I,
      (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i))
    let Ag : ℝ := (m : ℝ)⁻¹ * ∑ i ∈ I,
      (if σ i then (1 : ℝ) else -1) * (g (z i) - g (z' i))
    have hdiff : Af - Ag = (m : ℝ)⁻¹ * ∑ i ∈ I,
        (if σ i then (1 : ℝ) else -1) *
          ((f - g) (z i) - (f - g) (z' i)) := by
      dsimp [Af, Ag]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      apply congrArg ((m : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
    have herr : |Af - Ag| < 3 * ε / 8 := by
      rw [hdiff, abs_mul]
      rw [abs_of_pos (inv_pos.mpr hmreal)]
      calc
        (m : ℝ)⁻¹ * |∑ i ∈ I, (if σ i then (1 : ℝ) else -1) *
            ((f - g) (z i) - (f - g) (z' i))| <
            (m : ℝ)⁻¹ * ((3 / 8 : ℝ) * m * ε) := by gcongr
        _ = 3 * ε / 8 := by field_simp
    have hdevAf : ε < |Af| := by simpa [Af, I] using hdevReal
    have hcenter : ε / 2 < |Ag| := by
      have habs := abs_sub_abs_le_abs_sub Af Ag
      nlinarith
    have hraw : (m : ℝ) * ε / 2 <
        |∑ i ∈ I, (if σ i then (1 : ℝ) else -1) *
          (g (z i) - g (z' i))| := by
      dsimp [Ag] at hcenter
      rw [abs_mul, abs_of_pos (inv_pos.mpr hmreal)] at hcenter
      field_simp at hcenter
      nlinarith
    rw [Set.mem_iUnion]
    refine ⟨⟨g, hgT⟩, ?_⟩
    exact ⟨j, (Finset.mem_Icc.mp hj).2,
      le_of_lt (by simpa [C, rademacherPartialSum, I] using hraw)⟩
  let v : ℝ≥0 := ⟨8 * (m : ℝ) * M ^ 2, by positivity⟩
  have hsquares (g : T) :
      (∑ i, (⟨(g.1 (z i) - g.1 (z' i)) ^ 2,
        sq_nonneg (g.1 (z i) - g.1 (z' i))⟩ : ℝ≥0)) ≤ v := by
    have hgE : g.1 ∈ E := hTsub g.2
    have hsumle : (∑ i, (⟨(g.1 (z i) - g.1 (z' i)) ^ 2,
        sq_nonneg (g.1 (z i) - g.1 (z' i))⟩ : ℝ≥0)) ≤
        ∑ _i : Fin (2 * m),
          (⟨(2 * M) ^ 2, sq_nonneg (2 * M)⟩ : ℝ≥0) := by
      apply Finset.sum_le_sum
      intro i _
      have ha : |g.1 (z i) - g.1 (z' i)| ≤ 2 * M := by
        calc
          |g.1 (z i) - g.1 (z' i)| ≤ |g.1 (z i)| + |g.1 (z' i)| :=
            abs_sub _ _
          _ ≤ M + M := add_le_add (hbdd g.1 hgE _) (hbdd g.1 hgE _)
          _ = 2 * M := by ring
      have hprod : 0 ≤ (2 * M - |g.1 (z i) - g.1 (z' i)|) *
          (2 * M + |g.1 (z i) - g.1 (z' i)|) :=
        mul_nonneg (sub_nonneg.mpr ha) (by positivity)
      change (g.1 (z i) - g.1 (z' i)) ^ 2 ≤ (2 * M) ^ 2
      nlinarith [sq_abs (g.1 (z i) - g.1 (z' i))]
    have heq : (∑ _i : Fin (2 * m),
        (⟨(2 * M) ^ 2, sq_nonneg (2 * M)⟩ : ℝ≥0)) = v := by
      apply Subtype.ext
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp [v]
      change (((2 * m : ℕ) : ℝ) * (2 * M) ^ 2) = 8 * (m : ℝ) * M ^ 2
      push_cast
      ring
    exact hsumle.trans_eq heq
  have hCtail (g : T) : ν (C g) ≤
      4 * ENNReal.ofReal
        (Real.exp (-((m : ℝ) * ε ^ 2) / (64 * M ^ 2))) := by
    have htail := uniform_abs_max_partial_tail
      (fun i => g.1 (z i) - g.1 (z' i)) ((m : ℝ) * ε / 2) v
      (by positivity) (hsquares g)
    change ν (C g) ≤ _ at htail
    calc
      ν (C g) ≤ 4 * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε / 2) ^ 2 / (2 * (v : ℝ)))) := htail
      _ = 4 * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (64 * M ^ 2))) := by
        congr 3
        rw [show (v : ℝ) = 8 * (m : ℝ) * M ^ 2 from rfl]
        field_simp
        ring
  change ν B ≤ _
  have hrawtail : ν B ≤ 4 * T.card * ENNReal.ofReal
      (Real.exp (-((m : ℝ) * ε ^ 2) / (64 * M ^ 2))) := by
    calc
      ν B ≤ ν (⋃ g : T, C g) := measure_mono hBsub
      _ ≤ ∑' g : T, ν (C g) := measure_iUnion_le _
      _ ≤ ∑' _g : T, 4 * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (64 * M ^ 2))) :=
        ENNReal.tsum_le_tsum hCtail
      _ = 4 * T.card * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (64 * M ^ 2))) := by
        rw [tsum_fintype]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe]
        simp only [nsmul_eq_mul]
        ring
  by_cases hTempty : T = ∅
  · simpa [hTempty] using hrawtail
  have hTcard : 1 ≤ T.card := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hTempty)
  let y : ℝ := (m : ℝ) * ε ^ 2 / (128 * M ^ 2)
  have hy : 0 < y := by dsimp [y]; positivity
  have h64 : -((m : ℝ) * ε ^ 2) / (64 * M ^ 2) = -(2 * y) := by
    dsimp [y]
    field_simp
    ring
  have h128 : -((m : ℝ) * ε ^ 2) / (128 * M ^ 2) = -y := by
    dsimp [y]
    ring
  rw [h128]
  by_cases hylarge : Real.log 2 ≤ y
  · have ha : Real.exp (-y) ≤ (1 / 2 : ℝ) := by
      calc
        Real.exp (-y) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by linarith)
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    have hexp2 : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
      rw [show -(2 * y) = -y + -y by ring, Real.exp_add]
    have hreal : 4 * Real.exp (-(2 * y)) ≤ 2 * Real.exp (-y) := by
      rw [hexp2]
      nlinarith [Real.exp_pos (-y)]
    have henn : 4 * ENNReal.ofReal (Real.exp (-(2 * y))) ≤
        2 * ENNReal.ofReal (Real.exp (-y)) := by
      have := ENNReal.ofReal_le_ofReal hreal
      norm_num [ENNReal.ofReal_mul] at this ⊢
      exact this
    calc
      ν B ≤ 4 * T.card * ENNReal.ofReal (Real.exp (-(2 * y))) := by
        simpa [h64] using hrawtail
      _ ≤ 2 * T.card * ENNReal.ofReal (Real.exp (-y)) := by
        calc
          4 * T.card * ENNReal.ofReal (Real.exp (-(2 * y))) =
              T.card * (4 * ENNReal.ofReal (Real.exp (-(2 * y)))) := by ring
          _ ≤ T.card * (2 * ENNReal.ofReal (Real.exp (-y))) := by gcongr
          _ = 2 * T.card * ENNReal.ofReal (Real.exp (-y)) := by ring
  · have hylt : y < Real.log 2 := lt_of_not_ge hylarge
    have ha : (1 / 2 : ℝ) < Real.exp (-y) := by
      calc
        (1 / 2 : ℝ) = Real.exp (-Real.log 2) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
        _ < Real.exp (-y) := Real.exp_lt_exp.mpr (by linarith)
    have hreal : (1 : ℝ) ≤ 2 * (T.card : ℝ) * Real.exp (-y) := by
      have hc : (1 : ℝ) ≤ T.card := by exact_mod_cast hTcard
      nlinarith [Real.exp_pos (-y)]
    have henn : (1 : ℝ≥0∞) ≤
        2 * T.card * ENNReal.ofReal (Real.exp (-y)) := by
      have := ENNReal.ofReal_le_ofReal hreal
      norm_num [ENNReal.ofReal_mul] at this ⊢
      exact this
    calc
      ν B ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ ≤ 2 * T.card * ENNReal.ofReal (Real.exp (-y)) := henn

private theorem paired_swap_outer_le_uniform_average
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (n : ℕ) (D : Set (Fin n → Ω × Ω))
    (hDmeas : MeasurableSet D)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ) :
    (μ.prod μ).outerMeasureStar (pairedFiniteSample X n ⁻¹' D) ≤
      outerExpectation (μ.prod μ) (fun ξ =>
        (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          {σ | swapFinitePairs σ (pairedFiniteSample X n ξ) ∈ D}) := by
  classical
  let q : Fin n → Measure Ω := fun i => μ.map (X i.val)
  letI (i : Fin n) : IsProbabilityMeasure (q i) := by
    refine ⟨?_⟩
    dsimp [q]
    rw [Measure.map_apply (hXmeas i.val) MeasurableSet.univ]
    simp
  let A : (Fin n → Bool) → Set (Ξ × Ξ) := fun σ =>
    (swapFinitePairs σ ∘ pairedFiniteSample X n) ⁻¹' D
  have hpairedMeas : Measurable (pairedFiniteSample X n) :=
    measurable_pairedFiniteSample X n hXmeas
  have hAmeas (σ : Fin n → Bool) : MeasurableSet (A σ) :=
    hDmeas.preimage ((measurePreserving_swapFinitePairs q σ).measurable.comp hpairedMeas)
  have hpairedLaw : (μ.prod μ).map (pairedFiniteSample X n) =
      Measure.pi (fun i : Fin n => (q i).prod (q i)) := by
    simpa [q] using map_pairedFiniteSample_eq_pi_prod_map μ X n hXmeas hXiindep
  have hswapLaw (σ : Fin n → Bool) :
      (μ.prod μ).map (swapFinitePairs σ ∘ pairedFiniteSample X n) =
        (μ.prod μ).map (pairedFiniteSample X n) := by
    rw [← Measure.map_map (measurePreserving_swapFinitePairs q σ).measurable
      hpairedMeas, hpairedLaw, (measurePreserving_swapFinitePairs q σ).map_eq]
  have hbadMeasure (σ : Fin n → Bool) :
      (μ.prod μ) (pairedFiniteSample X n ⁻¹' D) = (μ.prod μ) (A σ) := by
    calc
      (μ.prod μ) (pairedFiniteSample X n ⁻¹' D) =
          ((μ.prod μ).map (pairedFiniteSample X n)) D :=
        (Measure.map_apply hpairedMeas hDmeas).symm
      _ = ((μ.prod μ).map
          (swapFinitePairs σ ∘ pairedFiniteSample X n)) D := by rw [hswapLaw]
      _ = (μ.prod μ) (A σ) :=
        Measure.map_apply ((measurePreserving_swapFinitePairs q σ).measurable.comp
          hpairedMeas) hDmeas
  let c : ℝ≥0∞ := (Fintype.card (Fin n → Bool) : ℝ≥0∞)⁻¹
  have htail (ξ : Ξ × Ξ) :
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          {σ | swapFinitePairs σ (pairedFiniteSample X n ξ) ∈ D} =
        ∑ σ : Fin n → Bool, (A σ).indicator (fun _ => c) ξ := by
    rw [PMF.toMeasure_apply_fintype]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : swapFinitePairs σ (pairedFiniteSample X n ξ) ∈ D
    · simp [hσ, A, c]
    · simp [hσ, A, c]
  have htailMeas : Measurable (fun ξ : Ξ × Ξ =>
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        {σ | swapFinitePairs σ (pairedFiniteSample X n ξ) ∈ D}) := by
    simp_rw [htail]
    exact Finset.measurable_sum _ fun σ _ => measurable_const.indicator (hAmeas σ)
  have htailIntegral :
      ∫⁻ ξ, (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          {σ | swapFinitePairs σ (pairedFiniteSample X n ξ) ∈ D} ∂(μ.prod μ) =
        (μ.prod μ) (pairedFiniteSample X n ⁻¹' D) := by
    calc
      ∫⁻ ξ, (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          {σ | swapFinitePairs σ (pairedFiniteSample X n ξ) ∈ D} ∂(μ.prod μ) =
          ∫⁻ ξ, ∑ σ : Fin n → Bool,
            (A σ).indicator (fun _ => c) ξ ∂(μ.prod μ) := lintegral_congr htail
      _ = ∑ σ : Fin n → Bool,
          ∫⁻ ξ, (A σ).indicator (fun _ => c) ξ ∂(μ.prod μ) := by
        rw [lintegral_finset_sum]
        intro σ _
        exact measurable_const.indicator (hAmeas σ)
      _ = ∑ σ : Fin n → Bool, c * (μ.prod μ) (A σ) := by
        apply Finset.sum_congr rfl
        intro σ _
        exact lintegral_indicator_const (hAmeas σ) c
      _ = ∑ _σ : Fin n → Bool,
          c * (μ.prod μ) (pairedFiniteSample X n ⁻¹' D) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [hbadMeasure σ]
      _ = (μ.prod μ) (pairedFiniteSample X n ⁻¹' D) := by
        unfold c
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel]
        · simp
        · exact_mod_cast Fintype.card_ne_zero
        · simp
  calc
    (μ.prod μ).outerMeasureStar (pairedFiniteSample X n ⁻¹' D) ≤
        (μ.prod μ) (pairedFiniteSample X n ⁻¹' D) :=
      outerMeasureStar_le_measure_symm _ _
    _ = outerExpectation (μ.prod μ) (fun ξ =>
        (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          {σ | swapFinitePairs σ (pairedFiniteSample X n ξ) ∈ D}) := by
      rw [outerExpectation_eq_lintegral htailMeas, htailIntegral]

private def prefixFinitePairs (m n : ℕ) (hn : n ≤ 2 * m)
    (z : Fin (2 * m) → Ω × Ω) : Fin n → Ω × Ω :=
  fun i => z (Fin.castLE hn i)

private def pairedGhostBlockBad (E : Set (Ω → ℝ)) (m : ℕ) (ε : ℝ) :
    Set (Fin (2 * m) → Ω × Ω) :=
  ⋃ n : {n // n ∈ Finset.Icc m (2 * m)},
    {z | ENNReal.ofReal ε <
      pairedGhostDeviation E n.1
        (prefixFinitePairs m n.1 (Finset.mem_Icc.mp n.2).2 z)}

private theorem measurable_prefixFinitePairs
    (m n : ℕ) (hn : n ≤ 2 * m) :
    Measurable (prefixFinitePairs (Ω := Ω) m n hn) := by
  exact measurable_pi_lambda _ fun i => measurable_pi_apply (Fin.castLE hn i)

private theorem measurableSet_pairedGhostBlockBad
    (E : Set (Ω → ℝ)) (m : ℕ) (ε : ℝ)
    (hEmeas : ∀ f ∈ E, Measurable f)
    (hPM : IsPointwiseMeasurable E) :
    MeasurableSet (pairedGhostBlockBad E m ε) := by
  unfold pairedGhostBlockBad
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_lt measurable_const
    ((measurable_pairGhostDeviation E n.1 hEmeas hPM).comp
      (measurable_prefixFinitePairs m n.1 (Finset.mem_Icc.mp n.2).2))

omit [MeasurableSpace Ω] in
private theorem pairedGhostBlockBad_pairedFiniteSample
    {Ξ : Type*} (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (m : ℕ) (ε : ℝ) :
    pairedFiniteSample X (2 * m) ⁻¹' pairedGhostBlockBad E m ε =
      {ξ | ∃ n ∈ Finset.Icc m (2 * m),
        ENNReal.ofReal ε < ghostDeviation E X n ξ.1 ξ.2} := by
  ext ξ
  constructor
  · intro hξ
    change pairedFiniteSample X (2 * m) ξ ∈ pairedGhostBlockBad E m ε at hξ
    rw [pairedGhostBlockBad, Set.mem_iUnion] at hξ
    obtain ⟨n, hdev⟩ := hξ
    refine ⟨n.1, n.2, ?_⟩
    rw [← pairedGhostDeviation_pairedFiniteSample E X n ξ]
    convert! hdev using 1
  · rintro ⟨n, hnmem, hdev⟩
    change pairedFiniteSample X (2 * m) ξ ∈ pairedGhostBlockBad E m ε
    rw [pairedGhostBlockBad, Set.mem_iUnion]
    refine ⟨⟨n, hnmem⟩, ?_⟩
    rw [← pairedGhostDeviation_pairedFiniteSample E X n ξ] at hdev
    convert! hdev using 1

omit [MeasurableSpace Ω] in
private theorem pairedGhostBlockBad_swap
    (E : Set (Ω → ℝ)) (T : Finset (Ω → ℝ)) (m : ℕ)
    (z : Fin (2 * m) → Ω × Ω) (σ : Fin (2 * m) → Bool) (ε : ℝ)
    (hm : 0 < m) :
    swapFinitePairs σ z ∈ pairedGhostBlockBad E m ε →
      ∃ j ∈ Finset.Icc m (2 * m),
        ENNReal.ofReal ε < supNormOver (E ∪ (↑T : Set (Ω → ℝ))) (fun f =>
          (m : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter
            (fun i : Fin (2 * m) => i.val < j),
              (if σ i then (1 : ℝ) else -1) * (f (z i).1 - f (z i).2)) := by
  intro h
  rw [pairedGhostBlockBad, Set.mem_iUnion] at h
  obtain ⟨j, hdev⟩ := h
  refine ⟨j.1, j.2, ?_⟩
  have hjle := (Finset.mem_Icc.mp j.2).2
  have hscale (f : Ω → ℝ) : (j.1 : ℝ)⁻¹ * ∑ i : Fin j.1,
      (if σ (Fin.castLE hjle i) then (1 : ℝ) else -1) *
        (f (z (Fin.castLE hjle i)).1 - f (z (Fin.castLE hjle i)).2) =
      (m : ℝ) / j.1 *
        ((m : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter
          (fun i : Fin (2 * m) => i.val < j.1),
            (if σ i then (1 : ℝ) else -1) * (f (z i).1 - f (z i).2)) := by
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hjpos : 0 < j.1 := hm.trans_le (Finset.mem_Icc.mp j.2).1
    have hjreal : (j.1 : ℝ) ≠ 0 := by exact_mod_cast hjpos.ne'
    have hsum : (∑ i ∈ Finset.univ.filter
        (fun i : Fin (2 * m) => i.val < j.1),
          (if σ i then (1 : ℝ) else -1) * (f (z i).1 - f (z i).2)) =
        ∑ i : Fin j.1, (if σ (Fin.castLE hjle i) then (1 : ℝ) else -1) *
          (f (z (Fin.castLE hjle i)).1 - f (z (Fin.castLE hjle i)).2) := by
      apply Finset.sum_bij (fun i hi =>
        (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin j.1))
      · intro i hi
        simp
      · intro a ha b hb hab
        have habval := congrArg (fun x : Fin j.1 => x.val) hab
        apply Fin.ext
        exact habval
      · intro b hb
        refine ⟨Fin.castLE hjle b, ?_, ?_⟩
        · simp [Fin.castLE]
        · rfl
      · intro i hi
        rfl
    rw [← hsum]
    field_simp
  have hswapEq : pairedGhostDeviation E j.1
      (prefixFinitePairs m j.1 hjle (swapFinitePairs σ z)) =
      supNormOver E (fun f => (j.1 : ℝ)⁻¹ * ∑ i : Fin j.1,
        (if σ (Fin.castLE hjle i) then (1 : ℝ) else -1) *
          (f (z (Fin.castLE hjle i)).1 - f (z (Fin.castLE hjle i)).2)) := by
    unfold pairedGhostDeviation prefixFinitePairs swapFinitePairs
    congr 2 with f
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : σ (Fin.castLE hjle i)
    · simp [hi]
    · simp [hi]
  change ENNReal.ofReal ε < pairedGhostDeviation E j.1
    (prefixFinitePairs m j.1 hjle (swapFinitePairs σ z)) at hdev
  rw [hswapEq] at hdev
  simp_rw [hscale] at hdev
  have hmj : (m : ℝ) / j.1 ≤ 1 := by
    apply div_le_one_of_le₀
    · exact_mod_cast (Finset.mem_Icc.mp j.2).1
    · positivity
  have hmj0 : 0 ≤ (m : ℝ) / j.1 := by positivity
  rw [supNormOver] at hdev ⊢
  rw [lt_iSup_iff] at hdev
  obtain ⟨f, hdev⟩ := hdev
  rw [lt_iSup_iff] at hdev
  obtain ⟨hf, hdev⟩ := hdev
  let L : ℝ := (m : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter
    (fun i : Fin (2 * m) => i.val < j.1),
      (if σ i then (1 : ℝ) else -1) * (f (z i).1 - f (z i).2)
  have hfac : ENNReal.ofReal |(m : ℝ) / j.1 * L| ≤ ENNReal.ofReal |L| := by
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul, abs_of_nonneg hmj0]
    exact mul_le_of_le_one_left (abs_nonneg _) hmj
  dsimp [L] at hfac
  exact hdev.trans_le <| hfac.trans <|
    le_iSup_of_le f (le_iSup_of_le (Or.inl hf) le_rfl)

private theorem empirical_ghostBlock_symmetrization_outer
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (M ε : ℝ)
    (hFmeas : ∀ f ∈ E, Measurable f)
    (hbdd : ∀ f ∈ E, ∀ x, |f x| ≤ M)
    (hε : 0 < ε)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    ∃ N : ℕ, ∀ m ≥ N,
      μ.outerMeasureStar (gcBlockBad E P X m (2 * m) ε) ≤
        2 * (μ.prod μ).outerMeasureStar
          {ξ | ∃ n ∈ Finset.Icc m (2 * m),
            ENNReal.ofReal (ε / 2) < ghostDeviation E X n ξ.1 ξ.2} := by
  classical
  obtain ⟨N, hclose⟩ := bounded_iid_empirical_close_half μ P E X M ε
    hFmeas hbdd hε hXmeas hXiindep hXid hXlaw
  refine ⟨N, fun m hmN => outerMeasureStar_le_two_prod_of_sections μ
    (gcBlockBad E P X m (2 * m) ε)
    {ξ | ∃ n ∈ Finset.Icc m (2 * m),
      ENNReal.ofReal (ε / 2) < ghostDeviation E X n ξ.1 ξ.2} ?_⟩
  intro ξ hξ
  rcases hξ with ⟨n, hnmem, hξ⟩
  rw [gcDeviation, supNormOver, lt_iSup_iff] at hξ
  obtain ⟨f, hξ⟩ := hξ
  rw [lt_iSup_iff] at hξ
  obtain ⟨hf, hξf⟩ := hξ
  have hdev : ε <
      |empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P| :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp hξf
  refine (hclose n (hmN.trans (Finset.mem_Icc.mp hnmem).1) f hf).trans
    (measure_mono ?_)
  intro ξ' hξ'
  simp only [Set.mem_setOf_eq] at hξ' ⊢
  refine ⟨n, hnmem, ?_⟩
  change ENNReal.ofReal (ε / 2) < ghostDeviation E X n ξ ξ'
  rw [ghostDeviation]
  have hdiff : ε / 2 <
      |empiricalAvg f n (fun i : Fin n => X i.val ξ) -
        empiricalAvg f n (fun i : Fin n => X i.val ξ')| := by
    have htri := abs_sub_abs_le_abs_sub
      (empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P)
      (empiricalAvg f n (fun i : Fin n => X i.val ξ') - ∫ x, f x ∂P)
    have hghost : empiricalAvg f n (fun i : Fin n => X i.val ξ) -
        empiricalAvg f n (fun i : Fin n => X i.val ξ') =
        (empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P) -
          (empiricalAvg f n (fun i : Fin n => X i.val ξ') - ∫ x, f x ∂P) := by
      ring
    rw [hghost]
    nlinarith
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hdiff |>.trans_le
    (le_supNormOver hf)

private theorem ennrealSummable_of_tsum_lt_top {a : ℕ → ℝ≥0∞}
    (h : ∑' k, a k < ⊤) : Summable a := by
  by_cases h' : ∑' k, a k < ⊤
  · exact ENNReal.summable
  · exact (h' h).elim

omit [MeasurableSpace Ω] in
private theorem conditionalRademacherTail_le_blockMaxTail_endpoint
    (E : Set (Ω → ℝ)) (T : Finset (Ω → ℝ)) (m : ℕ)
    (z z' : Fin (2 * m) → Ω) (ε : ℝ) (hm : 0 < m) (hε : 0 < ε) :
    conditionalRademacherTail E (2 * m) z z' (ε / 2) ≤
      conditionalRademacherBlockMaxTail E T m z z' ε := by
  apply measure_mono
  intro σ hσ
  change ENNReal.ofReal (ε / 2) < signedGhostDeviation E (2 * m) z z' σ at hσ
  change ∃ j ∈ Finset.Icc m (2 * m), ENNReal.ofReal ε <
    supNormOver (E ∪ (↑T : Set (Ω → ℝ))) (fun f =>
      (m : ℝ)⁻¹ * ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * m) => i.val < j),
        (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i)))
  refine ⟨2 * m, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
  rw [signedGhostDeviation, supNormOver, lt_iSup_iff] at hσ
  obtain ⟨f, hσ⟩ := hσ
  rw [lt_iSup_iff] at hσ
  obtain ⟨hf, hσf⟩ := hσ
  rw [supNormOver, lt_iSup_iff]
  refine ⟨f, ?_⟩
  rw [lt_iSup_iff]
  refine ⟨Or.inl hf, ?_⟩
  have hfilter : Finset.univ.filter (fun i : Fin (2 * m) => i.val < 2 * m) =
      Finset.univ := by
    apply Finset.filter_eq_self.2
    intro i _
    exact i.isLt
  rw [hfilter]
  have hreal : ε / 2 < |((2 * m : ℕ) : ℝ)⁻¹ * ∑ i : Fin (2 * m),
      (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i))| :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hσf
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mpr
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [show ((2 * m : ℕ) : ℝ)⁻¹ = (2 : ℝ)⁻¹ * (m : ℝ)⁻¹ by
    push_cast
    field_simp] at hreal
  have heq : (2 : ℝ)⁻¹ * (m : ℝ)⁻¹ * ∑ i : Fin (2 * m),
      (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i)) =
      (1 / 2 : ℝ) * ((m : ℝ)⁻¹ * ∑ i : Fin (2 * m),
        (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i))) := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hreal
  nlinarith [abs_nonneg ((m : ℝ)⁻¹ * ∑ i : Fin (2 * m),
    (if σ i then (1 : ℝ) else -1) * (f (z i) - f (z' i)))]

/-- The dyadic block outer masses
have finite `ENNReal` sum.  This is the form consumed by Borel--Cantelli;
`Summable` alone is topologically vacuous for `ENNReal`. -/
private theorem localizedUniformCover_block_tsum_lt_top
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (X : ℕ → Ξ → Ω) (M ε : ℝ)
    (hFmeas : ∀ f ∈ F, Measurable f) -- measurable class members.
    (hPM : IsPointwiseMeasurable F) -- suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV envelope condition.
    (hGV : ∀ x, ENNReal.ofReal |G x| ≤ V x)
      -- measurable majorant domination.
    (hVmeas : Measurable V) -- localization-set measurability.
    (hcov : ∀ η > 0, uniformLpCoveringNumber F G 1 η < ⊤)
      -- vdV uniform finite `L¹` covering condition.
    (hM : 0 < M) -- positive localization level.
    (hε : 0 < ε) -- positive deviation threshold.
    (hXmeas : ∀ i, Measurable (X i)) -- coordinate measurability.
    (hXiindep : ProbabilityTheory.iIndepFun X μ) -- iid independence.
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
      -- identical marginals.
    (hXlaw : μ.map (X 0) = P) -- common marginal law.
    : (∑' k : ℕ, μ.outerMeasureStar
        (gcBlockBad (localizedClass F (lpLocalization V 1 M))
          P X (2 ^ k) (2 ^ (k + 1)) ε)) < ⊤ := by
  classical
  let A : Set Ω := lpLocalization V 1 M
  let E : Set (Ω → ℝ) := localizedClass F A
  have hAmeas : MeasurableSet A := measurableSet_Iic.preimage hVmeas
  have hEmeas : ∀ f ∈ E, Measurable f := by
    rintro _ ⟨f, hf, rfl⟩
    exact measurable_localizedFunction A f hAmeas (hFmeas f hf)
  have hEPM : IsPointwiseMeasurable E :=
    pointwiseMeasurable_localizedClass F A hPM
  have hEbdd : ∀ f ∈ E, ∀ x, |f x| ≤ M := by
    rintro _ ⟨f, hf, rfl⟩ x
    by_cases hx : x ∈ A
    · have hGMenn : ENNReal.ofReal |G x| ≤ ENNReal.ofReal M :=
        (hGV x).trans (by simpa [A, lpLocalization] using hx)
      have hGM : |G x| ≤ M :=
        (ENNReal.ofReal_le_ofReal_iff hM.le).mp hGMenn
      simpa [localizedFunction, hx] using
        (hEnv.2 f hf x).trans ((le_abs_self (G x)).trans hGM)
    · simp [localizedFunction, hx, hM.le]
  obtain ⟨Ncard, hnet⟩ := exists_localizedPooledClassNet F G V 1
    (by norm_num) hVmeas (by simpa using hGV) hFmeas hEnv hcov hM
    (show 0 < ε / 32 by positivity)
  obtain ⟨Nsym, hsym⟩ := empirical_ghostBlock_symmetrization_outer
    μ P E X M ε hEmeas hEbdd hε hXmeas hXiindep hXid hXlaw
  have hdyadic (k : ℕ) (hk : Nsym ≤ k) :
      μ.outerMeasureStar (gcBlockBad E P X (2 ^ k) (2 * (2 ^ k)) ε) ≤
        4 * Ncard * ENNReal.ofReal
          (Real.exp (-(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 / (512 * M ^ 2))) := by
    let m : ℕ := 2 ^ k
    have hm : 0 < m := by positivity
    have hmN : Nsym ≤ m := by
      calc
        Nsym ≤ 2 ^ Nsym := Nsym.lt_two_pow_self.le
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    have hghost : (μ.prod μ).outerMeasureStar
        {ξ | ∃ n ∈ Finset.Icc m (2 * m),
          ENNReal.ofReal (ε / 2) < ghostDeviation E X n ξ.1 ξ.2} ≤
        2 * Ncard * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (512 * M ^ 2))) := by
      let D : Set (Fin (2 * m) → Ω × Ω) := pairedGhostBlockBad E m (ε / 2)
      have hDmeas : MeasurableSet D :=
        measurableSet_pairedGhostBlockBad E m (ε / 2) hEmeas hEPM
      calc
        (μ.prod μ).outerMeasureStar
            {ξ | ∃ n ∈ Finset.Icc m (2 * m),
              ENNReal.ofReal (ε / 2) < ghostDeviation E X n ξ.1 ξ.2} =
            (μ.prod μ).outerMeasureStar (pairedFiniteSample X (2 * m) ⁻¹' D) := by
          rw [pairedGhostBlockBad_pairedFiniteSample E X m (ε / 2)]
        _ ≤ outerExpectation (μ.prod μ) (fun ξ =>
            (PMF.uniformOfFintype (Fin (2 * m) → Bool)).toMeasure
              {σ | swapFinitePairs σ (pairedFiniteSample X (2 * m) ξ) ∈ D}) :=
          paired_swap_outer_le_uniform_average μ X (2 * m) D hDmeas hXmeas hXiindep
        _ ≤ outerExpectation (μ.prod μ) (fun _ =>
            2 * Ncard * ENNReal.ofReal
              (Real.exp (-((m : ℝ) * ε ^ 2) / (512 * M ^ 2)))) := by
          apply outerExpectation_mono
          intro ξ
          obtain ⟨T, hTcard, hT⟩ := hnet (2 * m) P
            (fun i => (pairedFiniteSample X (2 * m) ξ i).1)
            (fun i => (pairedFiniteSample X (2 * m) ξ i).2)
          have hT' : IsStrictFiniteLpClassNet E
              (pooledEmpiricalLaw P (2 * m)
                (fun i => (pairedFiniteSample X (2 * m) ξ i).1)
                (fun i => (pairedFiniteSample X (2 * m) ξ i).2))
              1 ((ε / 2) / 16) T := by
            convert hT using 1
            ring
          calc
            (PMF.uniformOfFintype (Fin (2 * m) → Bool)).toMeasure
                {σ | swapFinitePairs σ (pairedFiniteSample X (2 * m) ξ) ∈ D} ≤
                conditionalRademacherBlockMaxTail E T m
                  (fun i => (pairedFiniteSample X (2 * m) ξ i).1)
                  (fun i => (pairedFiniteSample X (2 * m) ξ i).2) (ε / 2) :=
              measure_mono (pairedGhostBlockBad_swap E T m
                (pairedFiniteSample X (2 * m) ξ) · (ε / 2) hm)
            _ ≤ 2 * T.card * ENNReal.ofReal
                (Real.exp (-((m : ℝ) * (ε / 2) ^ 2) / (128 * M ^ 2))) :=
              conditionalRademacher_finitePooledNet_blockMaxTail E P 1 m M (ε / 2)
                T (by norm_num) hm hM (by positivity) _ _ hEmeas hEbdd hT'
            _ ≤ 2 * Ncard * ENNReal.ofReal
                (Real.exp (-((m : ℝ) * ε ^ 2) / (512 * M ^ 2))) := by
              have hexp : -((m : ℝ) * (ε / 2) ^ 2) / (128 * M ^ 2) =
                  -((m : ℝ) * ε ^ 2) / (512 * M ^ 2) := by
                field_simp
                ring
              rw [hexp]
              gcongr
        _ = 2 * Ncard * ENNReal.ofReal
            (Real.exp (-((m : ℝ) * ε ^ 2) / (512 * M ^ 2))) := by
          rw [outerExpectation_const, measure_univ, mul_one]
    calc
      μ.outerMeasureStar (gcBlockBad E P X m (2 * m) ε) ≤
          2 * (μ.prod μ).outerMeasureStar
            {ξ | ∃ n ∈ Finset.Icc m (2 * m),
              ENNReal.ofReal (ε / 2) < ghostDeviation E X n ξ.1 ξ.2} :=
        hsym m hmN
      _ ≤ 2 * (2 * Ncard * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (512 * M ^ 2)))) := by gcongr
      _ = 4 * Ncard * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (512 * M ^ 2))) := by ring
      _ = 4 * Ncard * ENNReal.ofReal
          (Real.exp (-(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 / (512 * M ^ 2))) := by
        dsimp [m]
        congr 3
        ring
  let c : ℝ := ε ^ 2 / (512 * M ^ 2)
  let b : ℕ → ℝ := fun k => if Nsym ≤ k then
    (4 * Ncard : ℝ) * Real.exp ((-c) * (((2 : ℕ) ^ k : ℕ) : ℝ)) else 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hexpSumm : Summable (fun k : ℕ =>
      Real.exp ((-c) * (((2 : ℕ) ^ k : ℕ) : ℝ))) := by
    apply Real.summable_exp_nat_mul_of_ge (by linarith : -c < 0)
    intro k
    exact_mod_cast k.lt_two_pow_self.le
  have hbSumm : Summable b := by
    apply ((hexpSumm.mul_left (4 * Ncard : ℝ)).congr_atTop ?_)
    filter_upwards [eventually_ge_atTop Nsym] with k hk
    simp [b, hk]
  have hbnonneg (k : ℕ) : 0 ≤ b k := by
    dsimp [b]
    split_ifs <;> positivity
  have hglobal (k : ℕ) :
      μ.outerMeasureStar
          (gcBlockBad (localizedClass F (lpLocalization V 1 M))
            P X (2 ^ k) (2 ^ (k + 1)) ε) ≤ ENNReal.ofReal (b k) := by
    by_cases hk : Nsym ≤ k
    · have hkbound := hdyadic k hk
      calc
        μ.outerMeasureStar
            (gcBlockBad (localizedClass F (lpLocalization V 1 M))
              P X (2 ^ k) (2 ^ (k + 1)) ε) =
            μ.outerMeasureStar (gcBlockBad E P X (2 ^ k) (2 * (2 ^ k)) ε) := by
          change μ.outerMeasureStar
              (gcBlockBad (localizedClass F (lpLocalization V 1 M))
                P X (2 ^ k) (2 ^ (k + 1)) ε) =
            μ.outerMeasureStar
              (gcBlockBad (localizedClass F (lpLocalization V 1 M))
                P X (2 ^ k) (2 * (2 ^ k)) ε)
          congr 3
          simp [pow_succ, mul_comm]
        _ ≤ 4 * Ncard * ENNReal.ofReal
            (Real.exp (-(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 /
              (512 * M ^ 2))) := hkbound
        _ = ENNReal.ofReal (b k) := by
          rw [show -(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 / (512 * M ^ 2) =
            (-c) * (((2 : ℕ) ^ k : ℕ) : ℝ) by dsimp [c]; ring]
          simp [b, hk, ENNReal.ofReal_mul]
    · calc
        μ.outerMeasureStar
            (gcBlockBad (localizedClass F (lpLocalization V 1 M))
              P X (2 ^ k) (2 ^ (k + 1)) ε) ≤ μ.outerMeasureStar Set.univ :=
          outerMeasureStar_mono μ (Set.subset_univ _)
        _ = 1 := by
          apply le_antisymm
          · simpa using outerMeasureStar_le_measure_symm μ (Set.univ : Set Ξ)
          · simpa using measure_le_outerMeasureStar μ (Set.univ : Set Ξ)
        _ = ENNReal.ofReal (b k) := by simp [b, hk]
  calc
    (∑' k, μ.outerMeasureStar
        (gcBlockBad (localizedClass F (lpLocalization V 1 M))
          P X (2 ^ k) (2 ^ (k + 1)) ε)) ≤
        ∑' k, ENNReal.ofReal (b k) := ENNReal.tsum_le_tsum hglobal
    _ = ENNReal.ofReal (∑' k, b k) :=
      (ENNReal.ofReal_tsum_of_nonneg hbnonneg hbSumm).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Localized uniform-cover block tails are summable, the
Borel--Cantelli input for the almost-sure conclusion. -/
theorem localizedUniformCover_block_summable
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (X : ℕ → Ξ → Ω) (M ε : ℝ)
    (hFmeas : ∀ f ∈ F, Measurable f) -- measurable class members.
    (hPM : IsPointwiseMeasurable F) -- suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV envelope condition.
    (hGV : ∀ x, ENNReal.ofReal |G x| ≤ V x)
      -- measurable majorant domination.
    (hVmeas : Measurable V) -- localization-set measurability.
    (hcov : ∀ η > 0, uniformLpCoveringNumber F G 1 η < ⊤)
      -- vdV uniform finite `L¹` covering condition.
    (hM : 0 < M) -- positive localization level.
    (hε : 0 < ε) -- positive deviation threshold.
    (hXmeas : ∀ i, Measurable (X i)) -- coordinate measurability.
    (hXiindep : ProbabilityTheory.iIndepFun X μ) -- iid independence.
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
      -- identical marginals.
    (hXlaw : μ.map (X 0) = P) -- common marginal law.
    : Summable (fun k : ℕ => μ.outerMeasureStar
        (gcBlockBad (localizedClass F (lpLocalization V 1 M))
          P X (2 ^ k) (2 ^ (k + 1)) ε)) := by
  apply ennrealSummable_of_tsum_lt_top
  exact localizedUniformCover_block_tsum_lt_top μ P F G V X M ε hFmeas hPM
    hEnv hGV hVmeas hcov hM hε hXmeas hXiindep hXid hXlaw

private theorem localizedUniformCover_endpoint_tsum_lt_top
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (X : ℕ → Ξ → Ω) (M ε : ℝ)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hGV : ∀ x, ENNReal.ofReal |G x| ≤ V x)
    (hVmeas : Measurable V)
    (hcov : ∀ η > 0, uniformLpCoveringNumber F G 1 η < ⊤)
    (hM : 0 < M) (hε : 0 < ε)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    (∑' k : ℕ, μ.outerMeasureStar
      (gcBad (localizedClass F (lpLocalization V 1 M)) P X (2 ^ (k + 1)) ε)) < ⊤ := by
  classical
  let A : Set Ω := lpLocalization V 1 M
  let E : Set (Ω → ℝ) := localizedClass F A
  have hAmeas : MeasurableSet A := measurableSet_Iic.preimage hVmeas
  have hEmeas : ∀ f ∈ E, Measurable f := by
    rintro _ ⟨f, hf, rfl⟩
    exact measurable_localizedFunction A f hAmeas (hFmeas f hf)
  have hEPM : IsPointwiseMeasurable E := pointwiseMeasurable_localizedClass F A hPM
  have hEbdd : ∀ f ∈ E, ∀ x, |f x| ≤ M := by
    rintro _ ⟨f, hf, rfl⟩ x
    by_cases hx : x ∈ A
    · have hGM : |G x| ≤ M := (ENNReal.ofReal_le_ofReal_iff hM.le).mp
          ((hGV x).trans (by simpa [A, lpLocalization] using hx))
      simpa [localizedFunction, hx] using
        (hEnv.2 f hf x).trans ((le_abs_self (G x)).trans hGM)
    · simp [localizedFunction, hx, hM.le]
  obtain ⟨Ncard, hnet⟩ := exists_localizedPooledClassNet F G V 1
    (by norm_num) hVmeas (by simpa using hGV) hFmeas hEnv hcov hM
    (show 0 < ε / 16 by positivity)
  obtain ⟨Nsym, hsym⟩ := empirical_ghost_symmetrization_outer μ P E X M ε
    hEmeas hEbdd hε hXmeas hXiindep hXid hXlaw
  have hdyadic (k : ℕ) (hk : Nsym ≤ k) :
      μ.outerMeasureStar (gcBad E P X (2 ^ (k + 1)) ε) ≤
        4 * Ncard * ENNReal.ofReal
          (Real.exp (-(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 / (128 * M ^ 2))) := by
    let m : ℕ := 2 ^ k
    have hm : 0 < m := by positivity
    have hmN : Nsym ≤ 2 * m := by
      calc
        Nsym ≤ 2 ^ Nsym := Nsym.lt_two_pow_self.le
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        _ ≤ 2 * m := by dsimp [m]; omega
    have hswap := ghostSwap_rademacher_outer_le μ E X (2 * m) (ε / 2)
      hEmeas hEPM hXmeas hXiindep
    have hcond : outerExpectation (μ.prod μ) (fun ξ => conditionalRademacherTail E
        (2 * m) (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) (ε / 2)) ≤
        2 * Ncard * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (128 * M ^ 2))) := by
      calc
        outerExpectation (μ.prod μ) (fun ξ => conditionalRademacherTail E
            (2 * m) (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) (ε / 2)) ≤
            outerExpectation (μ.prod μ) (fun _ => 2 * Ncard * ENNReal.ofReal
              (Real.exp (-((m : ℝ) * ε ^ 2) / (128 * M ^ 2)))) := by
          apply outerExpectation_mono
          intro ξ
          obtain ⟨T, hTcard, hT⟩ := hnet (2 * m) P
            (fun i => X i.val ξ.1) (fun i => X i.val ξ.2)
          calc
            conditionalRademacherTail E (2 * m) (fun i => X i.val ξ.1)
                (fun i => X i.val ξ.2) (ε / 2) ≤
                conditionalRademacherBlockMaxTail E T m (fun i => X i.val ξ.1)
                  (fun i => X i.val ξ.2) ε :=
              conditionalRademacherTail_le_blockMaxTail_endpoint E T m _ _ ε hm hε
            _ ≤ 2 * T.card * ENNReal.ofReal
                (Real.exp (-((m : ℝ) * ε ^ 2) / (128 * M ^ 2))) :=
              conditionalRademacher_finitePooledNet_blockMaxTail E P 1 m M ε T
                (by norm_num) hm hM hε _ _ hEmeas hEbdd hT
            _ ≤ 2 * Ncard * ENNReal.ofReal
                (Real.exp (-((m : ℝ) * ε ^ 2) / (128 * M ^ 2))) := by gcongr
        _ = 2 * Ncard * ENNReal.ofReal
            (Real.exp (-((m : ℝ) * ε ^ 2) / (128 * M ^ 2))) := by
          rw [outerExpectation_const, measure_univ, mul_one]
    calc
      μ.outerMeasureStar (gcBad E P X (2 ^ (k + 1)) ε) =
          μ.outerMeasureStar (gcBad E P X (2 * m) ε) := by
        congr 4
        simp [m, pow_succ, mul_comm]
      _ ≤ 2 * (μ.prod μ).outerMeasureStar (ghostBad E X (2 * m) (ε / 2)) :=
        hsym (2 * m) hmN
      _ ≤ 2 * outerExpectation (μ.prod μ) (fun ξ => conditionalRademacherTail E
          (2 * m) (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) (ε / 2)) := by gcongr
      _ ≤ 2 * (2 * Ncard * ENNReal.ofReal
          (Real.exp (-((m : ℝ) * ε ^ 2) / (128 * M ^ 2)))) := by gcongr
      _ = 4 * Ncard * ENNReal.ofReal
          (Real.exp (-(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 / (128 * M ^ 2))) := by
        dsimp [m]
        ring_nf
  let c : ℝ := ε ^ 2 / (128 * M ^ 2)
  let b : ℕ → ℝ := fun k => if Nsym ≤ k then
    (4 * Ncard : ℝ) * Real.exp ((-c) * (((2 : ℕ) ^ k : ℕ) : ℝ)) else 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hexpSumm : Summable (fun k : ℕ =>
      Real.exp ((-c) * (((2 : ℕ) ^ k : ℕ) : ℝ))) := by
    apply Real.summable_exp_nat_mul_of_ge (by linarith : -c < 0)
    intro k
    exact_mod_cast k.lt_two_pow_self.le
  have hbSumm : Summable b := by
    apply ((hexpSumm.mul_left (4 * Ncard : ℝ)).congr_atTop ?_)
    filter_upwards [eventually_ge_atTop Nsym] with k hk
    simp [b, hk]
  have hb0 (k : ℕ) : 0 ≤ b k := by dsimp [b]; split_ifs <;> positivity
  have hglobal (k : ℕ) : μ.outerMeasureStar
      (gcBad (localizedClass F (lpLocalization V 1 M)) P X (2 ^ (k + 1)) ε) ≤
        ENNReal.ofReal (b k) := by
    by_cases hk : Nsym ≤ k
    · calc
        μ.outerMeasureStar
            (gcBad (localizedClass F (lpLocalization V 1 M)) P X (2 ^ (k + 1)) ε) ≤
            4 * Ncard * ENNReal.ofReal
              (Real.exp (-(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 / (128 * M ^ 2))) :=
          hdyadic k hk
        _ = ENNReal.ofReal (b k) := by
          rw [show -(((2 : ℕ) ^ k : ℕ) : ℝ) * ε ^ 2 / (128 * M ^ 2) =
            (-c) * (((2 : ℕ) ^ k : ℕ) : ℝ) by dsimp [c]; ring]
          simp [b, hk, ENNReal.ofReal_mul]
    · calc
        μ.outerMeasureStar
            (gcBad (localizedClass F (lpLocalization V 1 M)) P X (2 ^ (k + 1)) ε) ≤
            μ.outerMeasureStar Set.univ := outerMeasureStar_mono μ (Set.subset_univ _)
        _ = 1 := by
          apply le_antisymm
          · simpa using outerMeasureStar_le_measure_symm μ (Set.univ : Set Ξ)
          · simpa using measure_le_outerMeasureStar μ (Set.univ : Set Ξ)
        _ = ENNReal.ofReal (b k) := by simp [b, hk]
  calc
    (∑' k, μ.outerMeasureStar
      (gcBad (localizedClass F (lpLocalization V 1 M)) P X (2 ^ (k + 1)) ε)) ≤
        ∑' k, ENNReal.ofReal (b k) := ENNReal.tsum_le_tsum hglobal
    _ = ENNReal.ofReal (∑' k, b k) := (ENNReal.ofReal_tsum_of_nonneg hb0 hbSumm).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

private theorem localizedUniformCover_gc_ae
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (X : ℕ → Ξ → Ω) (M : ℝ)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hGV : ∀ x, ENNReal.ofReal |G x| ≤ V x)
    (hVmeas : Measurable V)
    (hcov : ∀ η > 0, uniformLpCoveringNumber F G 1 η < ⊤)
    (hM : 0 < M)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n =>
      gcDeviation (localizedClass F (lpLocalization V 1 M)) P X n ξ)
        atTop (𝓝 0) := by
  let δ : ℕ → ℝ := fun q => (2 : ℝ)⁻¹ ^ q
  have hδpos (q : ℕ) : 0 < δ q := by simp [δ]
  have hbc (q : ℕ) : ∀ᵐ ξ ∂μ, ∀ᶠ k in atTop, ξ ∉
      gcBlockBad (localizedClass F (lpLocalization V 1 M)) P X
        (2 ^ k) (2 ^ (k + 1)) (δ q) := by
    have hstar := localizedUniformCover_block_tsum_lt_top μ P F G V X M (δ q)
      hFmeas hPM hEnv hGV hVmeas hcov hM (hδpos q) hXmeas hXiindep hXid hXlaw
    have hmeasure : (∑' k : ℕ, μ
        (gcBlockBad (localizedClass F (lpLocalization V 1 M)) P X
          (2 ^ k) (2 ^ (k + 1)) (δ q))) < ⊤ :=
      (ENNReal.tsum_le_tsum (fun k => measure_le_outerMeasureStar μ _)).trans_lt hstar
    exact ae_eventually_notMem (ne_of_lt hmeasure)
  have hbcEndpoint (q : ℕ) : ∀ᵐ ξ ∂μ, ∀ᶠ k in atTop, ξ ∉
      gcBad (localizedClass F (lpLocalization V 1 M)) P X (2 ^ (k + 1)) (δ q) := by
    have hstar := localizedUniformCover_endpoint_tsum_lt_top μ P F G V X M (δ q)
      hFmeas hPM hEnv hGV hVmeas hcov hM (hδpos q) hXmeas hXiindep hXid hXlaw
    have hmeasure : (∑' k : ℕ, μ
        (gcBad (localizedClass F (lpLocalization V 1 M)) P X
          (2 ^ (k + 1)) (δ q))) < ⊤ :=
      (ENNReal.tsum_le_tsum (fun k => measure_le_outerMeasureStar μ _)).trans_lt hstar
    exact ae_eventually_notMem (ne_of_lt hmeasure)
  have hbcAll : ∀ᵐ ξ ∂μ, ∀ q, ∀ᶠ k in atTop, ξ ∉
      gcBlockBad (localizedClass F (lpLocalization V 1 M)) P X
        (2 ^ k) (2 ^ (k + 1)) (δ q) := ae_all_iff.2 hbc
  have hbcEndpointAll : ∀ᵐ ξ ∂μ, ∀ q, ∀ᶠ k in atTop, ξ ∉
      gcBad (localizedClass F (lpLocalization V 1 M)) P X
        (2 ^ (k + 1)) (δ q) := ae_all_iff.2 hbcEndpoint
  filter_upwards [hbcAll, hbcEndpointAll] with ξ hξ hξEndpoint
  rw [tendsto_order]
  constructor
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro a ha
    obtain ⟨q, hqa⟩ := ENNReal.exists_inv_two_pow_lt ha.ne'
    have hδa : ENNReal.ofReal (δ q) < a := by
      calc
        ENNReal.ofReal (δ q) = (2 : ℝ≥0∞)⁻¹ ^ q := by
          rw [show δ q = (2 : ℝ)⁻¹ ^ q by rfl,
            ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
          norm_num
        _ < a := hqa
    obtain ⟨Kb, hKb⟩ := eventually_atTop.1 (hξ q)
    obtain ⟨Ke, hKe⟩ := eventually_atTop.1 (hξEndpoint q)
    let K : ℕ := max Kb (Ke + 1)
    refine eventually_atTop.2 ⟨2 ^ K, fun n hn => ?_⟩
    obtain ⟨k, hkn, hnk⟩ := exists_nat_pow_near
      (x := n) (y := 2) (by
        calc
          1 = 2 ^ 0 := by simp
          _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) (Nat.zero_le K)
          _ ≤ n := hn) (by norm_num)
    have hKk : K ≤ k := by
      by_contra hnot
      have hkK : k + 1 ≤ K := by omega
      have hp : 2 ^ (k + 1) ≤ 2 ^ K :=
        pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hkK
      omega
    have hnmem : n ∈ Finset.Icc (2 ^ k) (2 ^ (k + 1)) :=
      Finset.mem_Icc.mpr ⟨hkn, hnk.le⟩
    have hle : gcDeviation (localizedClass F (lpLocalization V 1 M)) P X n ξ ≤
        ENNReal.ofReal (δ q) := by
      by_cases hleft : n = 2 ^ k
      · have hkpos : 0 < k := by
          have : Ke + 1 ≤ k := (le_max_right Kb (Ke + 1)).trans hKk
          omega
        have hKe' : Ke ≤ k - 1 := by
          have : Ke + 1 ≤ k := (le_max_right Kb (Ke + 1)).trans hKk
          omega
        have hend := hKe (k - 1) hKe'
        apply not_lt.mp
        intro hbad
        apply hend
        change ENNReal.ofReal (δ q) < gcDeviation
          (localizedClass F (lpLocalization V 1 M)) P X (2 ^ ((k - 1) + 1)) ξ
        simpa [Nat.sub_add_cancel hkpos, hleft] using hbad
      · apply not_lt.mp
        intro hbad
        exact hKb k ((le_max_left Kb (Ke + 1)).trans hKk) ⟨n, hnmem, hbad⟩
    exact hle.trans_lt hδa

private theorem slln_ae_via_iid_real_joint
    {P : Measure Ω} {Ξ : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P)
    (g : Ω → ℝ) (hgmeas : Measurable g) (hgint : Integrable g P) :
    ∀ᵐ ξ ∂μ, Tendsto (fun n : ℕ =>
      empiricalAvg g n (fun i : Fin n => X i.val ξ)) atTop
        (𝓝 (∫ x, g x ∂P)) := by
  let Y : ℕ → Ξ → ℝ := fun i ξ => g (X i ξ)
  have hYindep : Pairwise (fun i j => ProbabilityTheory.IndepFun (Y i) (Y j) μ) :=
    fun _ _ hij => (hXiindep.indepFun hij).comp hgmeas hgmeas
  have hYid : ∀ i, ProbabilityTheory.IdentDistrib (Y i) (Y 0) μ μ :=
    fun i => (hXid i).comp hgmeas
  have hgmap : Integrable g (μ.map (X 0)) := by simpa [hXlaw] using hgint
  have hYint : Integrable (Y 0) μ :=
    (integrable_map_measure hgmap.aestronglyMeasurable
      (hXmeas 0).aemeasurable).mp hgmap
  have hint : ∫ x, g x ∂P = ∫ ξ, Y 0 ξ ∂μ := by
    rw [← hXlaw]
    exact integral_map (hXmeas 0).aemeasurable hgmap.aestronglyMeasurable
  filter_upwards [ProbabilityTheory.strong_law_ae_real Y hYint hYindep hYid] with ξ hξ
  rw [hint]
  convert hξ using 1
  ext n
  unfold empiricalAvg Y
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => g (X i ξ)) n

omit [MeasurableSpace Ω] in
private theorem abs_empiricalAvg_le_empiricalAvg
    (f t : Ω → ℝ) (n : ℕ) (z : Fin n → Ω)
    (hft : ∀ x, |f x| ≤ t x) :
    |empiricalAvg f n z| ≤ empiricalAvg t n z := by
  unfold empiricalAvg
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hft (z i))

private theorem gcDeviation_le_localized_add_tail
    (P : Measure Ω) (F : Set (Ω → ℝ)) (H : Ω → ℝ)
    (V : Ω → ℝ≥0∞) {X : ℕ → Ξ → Ω} (M : ℝ) (n : ℕ) (ξ : Ξ)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHmeas : Measurable H)
    (hHenv : UniformEntropyStructural.IsEnvelope F H)
    (hHint : Integrable H P)
    (hVmeas : Measurable V) :
    gcDeviation F P X n ξ ≤
      gcDeviation (localizedClass F (lpLocalization V 1 M)) P X n ξ +
        ENNReal.ofReal (empiricalAvg (tailReal V H M) n
          (fun i : Fin n => X i.val ξ)) +
        ENNReal.ofReal (∫ x, tailReal V H M x ∂P) := by
  let A : Set Ω := lpLocalization V 1 M
  let t : Ω → ℝ := tailReal V H M
  have hAmeas : MeasurableSet A := measurableSet_Iic.preimage hVmeas
  have htmeas : Measurable t := by
    exact hHmeas.indicator (measurableSet_Ioi.preimage hVmeas)
  have ht0 : ∀ x, 0 ≤ t x := by
    intro x
    by_cases hx : ENNReal.ofReal M < V x
    · simpa [t, tailReal, hx] using hHenv.1 x
    · simp [t, tailReal, hx]
  have htint : Integrable t P :=
    hHint.indicator (measurableSet_Ioi.preimage hVmeas)
  rw [gcDeviation, supNormOver]
  refine iSup₂_le fun f hf => ?_
  let fA : Ω → ℝ := localizedFunction A f
  let r : Ω → ℝ := f - fA
  have hfint : Integrable f P := by
    refine hHint.mono' (hFmeas f hf).aestronglyMeasurable ?_
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using hHenv.2 f hf x
  have hfAmeas : Measurable fA := measurable_localizedFunction A f hAmeas (hFmeas f hf)
  have hfAint : Integrable fA P := by
    refine hHint.mono' hfAmeas.aestronglyMeasurable ?_
    filter_upwards [] with x
    by_cases hx : x ∈ A
    · simpa [fA, localizedFunction, hx, Real.norm_eq_abs] using hHenv.2 f hf x
    · simp [fA, localizedFunction, hx, hHenv.1 x]
  have hrint : Integrable r P := hfint.sub hfAint
  have hrt : ∀ x, |r x| ≤ t x := by
    intro x
    by_cases hx : x ∈ A
    · simpa [r, fA, localizedFunction, hx] using ht0 x
    · have htail : ENNReal.ofReal M < V x := by
        simpa [A, lpLocalization] using hx
      simpa [r, fA, localizedFunction, t, tailReal, hx, htail,
        abs_of_nonneg (hHenv.1 x)] using hHenv.2 f hf x
  have havgr : |empiricalAvg r n (fun i : Fin n => X i.val ξ)| ≤
      empiricalAvg t n (fun i : Fin n => X i.val ξ) :=
    abs_empiricalAvg_le_empiricalAvg r t n _ hrt
  have hintr : |∫ x, r x ∂P| ≤ ∫ x, t x ∂P := by
    calc
      |∫ x, r x ∂P| ≤ ∫ x, |r x| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ x, t x ∂P := integral_mono_ae hrint.abs htint
        (Eventually.of_forall hrt)
  have hsplit :
      empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P =
        (empiricalAvg fA n (fun i : Fin n => X i.val ξ) - ∫ x, fA x ∂P) +
        (empiricalAvg r n (fun i : Fin n => X i.val ξ) - ∫ x, r x ∂P) := by
    have havg : empiricalAvg f n (fun i : Fin n => X i.val ξ) =
        empiricalAvg fA n (fun i : Fin n => X i.val ξ) +
          empiricalAvg r n (fun i : Fin n => X i.val ξ) := by
      unfold empiricalAvg r
      rw [← mul_add, ← Finset.sum_add_distrib]
      congr 2 with i
      simp [fA]
    have hrintEq : ∫ x, r x ∂P = (∫ x, f x ∂P) - ∫ x, fA x ∂P := by
      dsimp [r]
      exact integral_sub hfint hfAint
    rw [havg, hrintEq]
    ring
  have hreal : |empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P| ≤
      |empiricalAvg fA n (fun i : Fin n => X i.val ξ) - ∫ x, fA x ∂P| +
        empiricalAvg t n (fun i : Fin n => X i.val ξ) + ∫ x, t x ∂P := by
    rw [hsplit]
    calc
      |(empiricalAvg fA n (fun i : Fin n => X i.val ξ) - ∫ x, fA x ∂P) +
          (empiricalAvg r n (fun i : Fin n => X i.val ξ) - ∫ x, r x ∂P)| ≤
          |empiricalAvg fA n (fun i : Fin n => X i.val ξ) - ∫ x, fA x ∂P| +
            |empiricalAvg r n (fun i : Fin n => X i.val ξ) - ∫ x, r x ∂P| :=
        abs_add_le _ _
      _ ≤ |empiricalAvg fA n (fun i : Fin n => X i.val ξ) - ∫ x, fA x ∂P| +
          (|empiricalAvg r n (fun i : Fin n => X i.val ξ)| + |∫ x, r x ∂P|) := by
        gcongr
        exact abs_sub _ _
      _ ≤ |empiricalAvg fA n (fun i : Fin n => X i.val ξ) - ∫ x, fA x ∂P| +
          (empiricalAvg t n (fun i : Fin n => X i.val ξ) + ∫ x, t x ∂P) :=
        add_le_add_right (add_le_add havgr hintr) _
      _ = |empiricalAvg fA n (fun i : Fin n => X i.val ξ) - ∫ x, fA x ∂P| +
          empiricalAvg t n (fun i : Fin n => X i.val ξ) + ∫ x, t x ∂P := by ring
  calc
    ENNReal.ofReal |empiricalAvg f n (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P| ≤
        ENNReal.ofReal (|empiricalAvg fA n (fun i : Fin n => X i.val ξ) -
          ∫ x, fA x ∂P| + empiricalAvg t n (fun i : Fin n => X i.val ξ) +
            ∫ x, t x ∂P) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal |empiricalAvg fA n (fun i : Fin n => X i.val ξ) -
          ∫ x, fA x ∂P| + ENNReal.ofReal (empiricalAvg t n
            (fun i : Fin n => X i.val ξ)) + ENNReal.ofReal (∫ x, t x ∂P) := by
      have havg0 : 0 ≤ empiricalAvg t n (fun i : Fin n => X i.val ξ) := by
        unfold empiricalAvg
        exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ht0 _)
      have hint0 : 0 ≤ ∫ x, t x ∂P := integral_nonneg ht0
      rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) havg0) hint0,
        ENNReal.ofReal_add (abs_nonneg _) havg0]
    _ ≤ gcDeviation (localizedClass F (lpLocalization V 1 M)) P X n ξ +
          ENNReal.ofReal (empiricalAvg t n (fun i : Fin n => X i.val ξ)) +
            ENNReal.ofReal (∫ x, t x ∂P) := by
      gcongr
      exact le_supNormOver (show fA ∈ localizedClass F (lpLocalization V 1 M) from
        ⟨f, hf, rfl⟩)
    _ = _ := by rfl

/-- **Theorem 19.13 core.** Uniform finite `L¹` covering and finite
outer first envelope moment imply almost-sure uniform convergence for an iid
sample. -/
theorem uniformCovering_gc_iid_core
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (X : ℕ → Ξ → Ω)
    (hFmeas : ∀ f ∈ F, Measurable f) -- measurable class members.
    (hPM : IsPointwiseMeasurable F) -- vdV suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV envelope condition.
    (hG1 : outerLpNorm P G 1 < ⊤) -- finite outer first moment.
    (hcov : ∀ ε > 0, uniformLpCoveringNumber F G 1 ε < ⊤)
      -- vdV uniform finite `L¹` covering condition.
    (hXmeas : ∀ i, Measurable (X i)) -- coordinate measurability.
    (hXiindep : ProbabilityTheory.iIndepFun X μ) -- iid independence.
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
      -- identical marginals.
    (hXlaw : μ.map (X 0) = P) -- common marginal law.
    : ∀ᵐ ξ ∂μ, Tendsto (fun n => gcDeviation F P X n ξ) atTop (𝓝 0) := by
  obtain ⟨V, H, hVmeas, hGV, hVint, hHmeas, hHenv, hHint, hHV⟩ :=
    exists_localizingMajorants F G P hFmeas hPM hEnv hG1
  have hloc : ∀ᵐ ξ ∂μ, ∀ j : ℕ, Tendsto (fun n =>
      gcDeviation (localizedClass F (lpLocalization V 1 (j + 1 : ℕ))) P X n ξ)
        atTop (𝓝 0) := by
    apply ae_all_iff.2
    intro j
    exact localizedUniformCover_gc_ae μ P F G V X (j + 1 : ℕ) hFmeas hPM hEnv hGV
      hVmeas hcov (by positivity) hXmeas hXiindep hXid hXlaw
  have htail : ∀ᵐ ξ ∂μ, ∀ j : ℕ, Tendsto (fun n =>
      empiricalAvg (tailReal V H (j + 1 : ℕ)) n
        (fun i : Fin n => X i.val ξ)) atTop
          (𝓝 (∫ x, tailReal V H (j + 1 : ℕ) x ∂P)) := by
    apply ae_all_iff.2
    intro j
    have htmeas : Measurable (tailReal V H (j + 1 : ℕ)) :=
      hHmeas.indicator (measurableSet_Ioi.preimage hVmeas)
    have htint : Integrable (tailReal V H (j + 1 : ℕ)) P :=
      hHint.indicator (measurableSet_Ioi.preimage hVmeas)
    exact slln_ae_via_iid_real_joint hXmeas hXiindep hXid hXlaw _ htmeas htint
  filter_upwards [hloc, htail] with ξ hξloc hξtail
  rw [tendsto_order]
  constructor
  · intro a ha
    exact (not_lt_of_ge bot_le ha).elim
  · intro a ha
    obtain ⟨q, hqa⟩ := ENNReal.exists_inv_two_pow_lt ha.ne'
    let d : ℝ := (2 : ℝ)⁻¹ ^ q
    let η : ℝ := d / 8
    have hd : 0 < d := by simp [d]
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨M, hM, hMtail⟩ :=
      tailReal_small V H P hVmeas hVint hHV η hη
    let j : ℕ := ⌈M⌉₊
    let N : ℕ := j + 1
    have hMN : M ≤ (N : ℝ) := by
      calc
        M ≤ (j : ℝ) := by simpa [j] using (Nat.le_ceil M)
        _ ≤ (N : ℕ) := by simp [N]
    have htailMono : eLpNorm (tailReal V H N) 1 P ≤
        eLpNorm (tailReal V H M) 1 P := by
      apply eLpNorm_mono
      intro x
      by_cases hxN : ENNReal.ofReal (N : ℝ) < V x
      · have hxM : ENNReal.ofReal M < V x :=
          lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hMN) hxN
        have hxN' : x ∈ {x | ENNReal.ofReal (N : ℝ) < V x} := hxN
        have hxM' : x ∈ {x | ENNReal.ofReal M < V x} := hxM
        unfold tailReal
        rw [Set.indicator_of_mem hxN', Set.indicator_of_mem hxM']
      · have hxN' : x ∉ {x | ENNReal.ofReal (N : ℝ) < V x} := hxN
        unfold tailReal
        rw [Set.indicator_of_notMem hxN']
        simpa only [norm_zero] using! (norm_nonneg (tailReal V H M x))
    have hNtail : eLpNorm (tailReal V H N) 1 P < ENNReal.ofReal η :=
      htailMono.trans_lt hMtail
    have htmeas : Measurable (tailReal V H N) :=
      hHmeas.indicator (measurableSet_Ioi.preimage hVmeas)
    have ht0 : ∀ x, 0 ≤ tailReal V H N x := by
      intro x
      by_cases hx : ENNReal.ofReal (N : ℝ) < V x
      · have hx' : x ∈ {x | ENNReal.ofReal (N : ℝ) < V x} := hx
        unfold tailReal
        rw [Set.indicator_of_mem hx']
        exact hHenv.1 x
      · have hx' : x ∉ {x | ENNReal.ofReal (N : ℝ) < V x} := hx
        unfold tailReal
        rw [Set.indicator_of_notMem hx']
    have htint : Integrable (tailReal V H N) P :=
      hHint.indicator (measurableSet_Ioi.preimage hVmeas)
    have hintN : ∫ x, tailReal V H N x ∂P < η := by
      have heq : ENNReal.ofReal (∫ x, tailReal V H N x ∂P) =
          eLpNorm (tailReal V H N) 1 P := by
        rw [eLpNorm_one_eq_lintegral_enorm,
          ofReal_integral_eq_lintegral_ofReal htint (Eventually.of_forall ht0)]
        apply lintegral_congr
        intro x
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (ht0 x)]
      exact (ENNReal.ofReal_lt_ofReal_iff hη).mp (heq.trans_lt hNtail)
    have hlocN : Tendsto (fun n =>
        gcDeviation (localizedClass F (lpLocalization V 1 N)) P X n ξ)
          atTop (𝓝 0) := by simpa [N] using hξloc j
    have htailN : Tendsto (fun n => empiricalAvg (tailReal V H N) n
        (fun i : Fin n => X i.val ξ)) atTop
          (𝓝 (∫ x, tailReal V H N x ∂P)) := by
      simpa [N] using hξtail j
    have hlocEventually : ∀ᶠ n in atTop,
        gcDeviation (localizedClass F (lpLocalization V 1 N)) P X n ξ <
          ENNReal.ofReal (d / 4) :=
      (tendsto_order.1 hlocN).2 _ (ENNReal.ofReal_pos.mpr (by positivity))
    have htailEventually : ∀ᶠ n in atTop,
        empiricalAvg (tailReal V H N) n (fun i : Fin n => X i.val ξ) < 2 * η :=
      (tendsto_order.1 htailN).2 _ (hintN.trans (by linarith))
    filter_upwards [hlocEventually, htailEventually] with n hnloc hntail
    have havg0 : 0 ≤ empiricalAvg (tailReal V H N) n
        (fun i : Fin n => X i.val ξ) := by
      unfold empiricalAvg
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ht0 _)
    have hint0 : 0 ≤ ∫ x, tailReal V H N x ∂P :=
      integral_nonneg ht0
    have hnavg : ENNReal.ofReal (empiricalAvg (tailReal V H N) n
        (fun i : Fin n => X i.val ξ)) < ENNReal.ofReal (2 * η) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * η)).mpr hntail
    have hnint : ENNReal.ofReal (∫ x, tailReal V H N x ∂P) <
        ENNReal.ofReal η := (ENNReal.ofReal_lt_ofReal_iff hη).mpr hintN
    calc
      gcDeviation F P X n ξ ≤
          gcDeviation (localizedClass F (lpLocalization V 1 N)) P X n ξ +
            ENNReal.ofReal (empiricalAvg (tailReal V H N) n
              (fun i : Fin n => X i.val ξ)) +
            ENNReal.ofReal (∫ x, tailReal V H N x ∂P) :=
        gcDeviation_le_localized_add_tail P F H V N n ξ hFmeas hHmeas hHenv
          hHint hVmeas
      _ < ENNReal.ofReal (d / 4) + ENNReal.ofReal (2 * η) + ENNReal.ofReal η := by
        exact ENNReal.add_lt_add (ENNReal.add_lt_add hnloc hnavg) hnint
      _ = ENNReal.ofReal (d / 4 + 2 * η + η) := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ d / 4)
            (by positivity : 0 ≤ 2 * η),
          ← ENNReal.ofReal_add (by positivity : 0 ≤ d / 4 + 2 * η) hη.le]
      _ ≤ ENNReal.ofReal d := by
        apply ENNReal.ofReal_le_ofReal
        dsimp [η]
        linarith
      _ = (2 : ℝ≥0∞)⁻¹ ^ q := by
        rw [show d = (2 : ℝ)⁻¹ ^ q by rfl,
          ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      _ < a := hqa

/-! ### IID formulation -/

/-- IID-facing formulation of a `P`-Glivenko--Cantelli class using Mathlib's
joint-independence predicate.

This quantifies over jointly iid samples and is implied by the
pairwise-independence formulation. -/
def IsPGlivenkoCantelliIID (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∀ {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {X : ℕ → Ξ → Ω},
    (∀ i, Measurable (X i)) →
    ProbabilityTheory.iIndepFun X μ →
    (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
    μ.map (X 0) = P →
    ∀ᵐ ξ ∂μ, Tendsto (fun n => gcDeviation F P X n ξ) atTop (𝓝 0)

universe uSample

/-- The pairwise-independence GC predicate implies the joint-iid formulation
at the same sample-space universe. -/
theorem IsPGlivenkoCantelli.toIID {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hGC : IsPGlivenkoCantelli.{_, uSample} F P)
      -- GC certification at this sample universe.
    : IsPGlivenkoCantelliIID.{_, uSample} F P := by
  intro Ξ _ μ _ X hXmeas hXiindep hXid hXlaw
  have hpw : Pairwise (fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ) :=
    fun _ _ hij => hXiindep.indepFun hij
  have hsum (n : ℕ) (ξ : Ξ) (f : Ω → ℝ) :
      (∑ i : Fin n, f (X i.val ξ)) = ∑ i ∈ Finset.range n, f (X i ξ) :=
    Fin.sum_univ_eq_sum_range (fun i => f (X i ξ)) n
  simpa only [gcDeviation, empiricalAvg, hsum] using hGC hXmeas hpw hXid hXlaw

/-- IID-facing uniform-covering Glivenko--Cantelli conclusion of vdV Theorem
19.13. -/
theorem uniformCovering_isPGlivenkoCantelliIID
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    -- LEAN-ONLY: explicit measurability of the class members.
    (hFmeas : ∀ f ∈ F, Measurable f)
    -- USER-INPUT: pointwise measurability, an integrable envelope, and finite
    -- uniform `L¹` covering numbers; vdV Theorem 19.13.
    (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hG1 : outerLpNorm P G 1 < ⊤)
    (hcover : ∀ ε > 0, uniformLpCoveringNumber F G 1 ε < ⊤)
    : IsPGlivenkoCantelliIID F P := by
  intro Ξ _ μ _ X hXmeas hXiindep hXid hXlaw
  exact uniformCovering_gc_iid_core μ P F G X hFmeas hPM hEnv hG1 hcover
    hXmeas hXiindep hXid hXlaw

end AsymptoticStatistics.EmpiricalProcess
