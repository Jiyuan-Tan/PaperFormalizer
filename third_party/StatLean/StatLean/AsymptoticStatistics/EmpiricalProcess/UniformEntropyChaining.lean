module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformEntropySymmetrization
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.GaussianMaximal

@[expose] public section

/-!
# Conditional uniform-entropy chaining

Core lemmas for the conditional Rademacher/Dudley argument in van der
Vaart Theorem 19.14.  The schedule is selected separately for every admissible
law `Q`; uniformity enters through its cardinality ledger, not through an
incorrect common finite net for all laws.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, Theorem 19.14,
book p.274.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ENNReal ProbabilityTheory
open scoped BigOperators ENNReal Topology

open UniformEntropyStructural

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Measurable envelope and deterministic net schedule -/

/-- A possibly nonmeasurable envelope
with finite outer `L²(P)` norm admits a measurable square-integrable envelope.
The construction must majorize the whole class pointwise, not merely almost
everywhere.  Edge behavior: for `F = ∅` it may choose zero; if the supplied
outer norm is zero, the resulting majorant is zero `P`-a.e. but still dominates
the class pointwise. -/
theorem exists_measurable_l2_envelope
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
      -- vdV 19.14 measurable class members.
    (hPM : IsPointwiseMeasurable F)
      -- vdV 19.14 suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV 19.14 envelope, not assumed measurable.
    (hG2 : outerLpNorm P G 2 < ⊤)
      -- vdV 19.14 finite outer squared-envelope moment.
    : ∃ H : Ω → ℝ, Measurable H ∧
        UniformEntropyStructural.IsEnvelope F H ∧ MemLp H 2 P := by
  have houter : outerExpectation P
      (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) < ⊤ := by
    unfold outerLpNorm at hG2
    exact (ENNReal.rpow_lt_top_iff_of_pos
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).mp hG2
  let Majorants := {U : Ω → ℝ≥0∞ //
    Measurable U ∧ (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) ≤ U}
  have hU_exists : ∃ U : Majorants,
      (∫⁻ x, (U : Ω → ℝ≥0∞) x ∂P) < ⊤ := by
    by_contra hnone
    have h_all : ∀ U : Majorants,
        (∫⁻ x, (U : Ω → ℝ≥0∞) x ∂P) = ⊤ := by
      intro U
      exact top_unique (not_lt.mp ((not_exists.mp hnone) U))
    have htop : outerExpectation P
        (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) = ⊤ := by
      unfold outerExpectation
      apply top_unique
      refine le_iInf fun U => ?_
      rw [h_all U]
    rw [htop] at houter
    exact (lt_irrefl _ houter).elim
  obtain ⟨U, hUint⟩ := hU_exists
  obtain ⟨F₀, hF₀_countable, hF₀_sub, hF₀_dense⟩ := hPM
  letI : Countable (↥F₀) := hF₀_countable
  let W : Ω → ℝ≥0∞ := fun x =>
    ⨆ f : ↥F₀, ENNReal.ofReal |(f : Ω → ℝ) x|
  have hWmeas : Measurable W := by
    apply Measurable.iSup
    intro f
    exact (continuous_abs.measurable.comp
      (hFmeas f (hF₀_sub f.property))).ennreal_ofReal
  have hWG : ∀ x, W x ≤ ENNReal.ofReal |G x| := by
    intro x
    refine iSup_le fun f => ?_
    exact ENNReal.ofReal_le_ofReal
      ((hEnv.2 f (hF₀_sub f.property) x).trans_eq
        (abs_of_nonneg (hEnv.1 x)).symm)
  have hWtop : ∀ x, W x ≠ ⊤ := by
    intro x htop
    have hx := hWG x
    rw [htop] at hx
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hx)
  let H : Ω → ℝ := fun x => (W x).toReal
  have hHmeas : Measurable H := hWmeas.ennreal_toReal
  have hHnonneg : ∀ x, 0 ≤ H x := fun _ => ENNReal.toReal_nonneg
  have hHenv : UniformEntropyStructural.IsEnvelope F H := by
    refine ⟨hHnonneg, ?_⟩
    intro f hf x
    obtain ⟨g, hg_mem, hg_lim⟩ := hF₀_dense f hf
    have hbound : ∀ n, |g n x| ≤ H x := by
      intro n
      have hn : ENNReal.ofReal |g n x| ≤ W x :=
        le_iSup (fun k : ↥F₀ => ENNReal.ofReal |(k : Ω → ℝ) x|)
          ⟨g n, hg_mem n⟩
      rw [← ENNReal.ofReal_toReal (hWtop x)] at hn
      exact (ENNReal.ofReal_le_ofReal_iff (hHnonneg x)).mp hn
    exact le_of_tendsto' ((continuous_abs.tendsto (f x)).comp (hg_lim x)) hbound
  have hHmem : MemLp H 2 P := by
    refine ⟨hHmeas.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num) ENNReal.ofNat_ne_top]
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hUint
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hHnonneg x),
      ENNReal.ofReal_toReal (hWtop x)]
    simp only [ENNReal.toReal_ofNat]
    exact (ENNReal.rpow_le_rpow (hWG x) (by norm_num)).trans (U.2.2 x)
  exact ⟨H, hHmeas, hHenv, hHmem⟩

/-- A law-indexed nested Dudley schedule extracted from uniform `L²` covering
numbers.

Constitutive (vdV §19.2 p.274): for each admissible `Q`, `T Q hQ j` is a
finite subset of the class and a relative `2⁻ʲ`-net.  The raw arbitrary-center
cover is taken at the shifted radius `2⁻(j+1)`; choosing a class member in each
occupied ball costs the exact factor two in the radius.  Nesting is obtained by
retaining all earlier representatives, hence the cardinality is bounded by the
sum of the shifted covering numbers.  The summable series deliberately uses
`sqrt (log (2 * card))`, including its exact factor `2`.

Edge behavior: for the empty class every net is empty and the series is zero.
If `G` has zero `Q`-norm there is no admissibility proof, so no fictitious net
data are demanded. -/
structure UniformDudleySchedule (F : Set (Ω → ℝ)) (G : Ω → ℝ) where
  /-- Constitutive (vdV §19.2 p.274): the finite class-representative net at
  law `Q` and level `j`. -/
  net : ∀ (Q : Measure Ω), IsAdmissibleMeasure G 2 Q → ℕ → Finset ↥F
  /-- Constitutive (vdV §19.2 p.274): representatives are retained when the
  scale is refined, providing one coherent chaining schedule. -/
  nested : ∀ (Q : Measure Ω) (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ),
    net Q hQ j ⊆ net Q hQ (j + 1)
  /-- Constitutive (vdV §19.2 p.274): the selected representatives give the
  exact factor-two class net used by the dyadic chain. -/
  covers : ∀ (Q : Measure Ω) (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ)
    (f : ↥F), ∃ g ∈ net Q hQ j,
      outerLpNorm Q ((f : Ω → ℝ) - (g : Ω → ℝ)) 2 <
        ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * outerLpNorm Q G 2
  /-- Constitutive (vdV §19.2 p.274): the cumulative cardinality ledger at
  the shifted half-radius records the uniform-cover complexity. -/
  card_le : ∀ (Q : Measure Ω) (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ),
    ((net Q hQ j).card : ℕ∞) ≤
      ∑ k ∈ Finset.range (j + 1),
        uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (k + 1))
  /-- Constitutive (vdV §19.2 p.274): Dudley's dyadic entropy series is
  summable, with the book's `log (2 card)` guard. -/
  entropySummable : ∀ (Q : Measure Ω) (hQ : IsAdmissibleMeasure G 2 Q),
    Summable (fun j : ℕ =>
      (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (net Q hQ j).card)))

/-- Every positive radius has finite uniform covering number when the uniform
entropy integral on `(0,1]` is finite. -/
private theorem uniformLpCoveringNumber_lt_top_of_uniformEntropy
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) :
    uniformLpCoveringNumber F G 2 ε < ⊤ := by
  let ε₀ : ℝ := min ε 1
  have hε₀_pos : 0 < ε₀ := lt_min hε one_pos
  have hε₀_le_ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀_le_one : ε₀ ≤ 1 := min_le_right _ _
  refine lt_of_le_of_lt (uniformLpCoveringNumber_antitone_eps hε₀_le_ε) ?_
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hweight_top : ∀ ε' ∈ Set.Ioc (0 : ℝ) ε₀,
      entropyWeight (uniformLpCoveringNumber F G 2 ε') = ⊤ := by
    intro ε' hε'
    have hcover_top : uniformLpCoveringNumber F G 2 ε' = ⊤ :=
      top_unique (htop ▸ uniformLpCoveringNumber_antitone_eps hε'.2)
    rw [hcover_top, entropyWeight_top]
  have hJ_top : uniformEntropyIntegral 1 F G 2 = ⊤ := by
    unfold uniformEntropyIntegral
    refine top_le_iff.mp ?_
    calc
      (⊤ : ℝ≥0∞) = ∫⁻ _ε in Set.Ioc (0 : ℝ) ε₀, (⊤ : ℝ≥0∞) ∂volume := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero,
          ENNReal.top_mul (ENNReal.ofReal_ne_zero_iff.mpr hε₀_pos)]
      _ = ∫⁻ ε' in Set.Ioc (0 : ℝ) ε₀,
          entropyWeight (uniformLpCoveringNumber F G 2 ε') ∂volume :=
        (setLIntegral_congr_fun measurableSet_Ioc hweight_top).symm
      _ ≤ ∫⁻ ε' in Set.Ioc (0 : ℝ) 1,
          entropyWeight (uniformLpCoveringNumber F G 2 ε') ∂volume :=
        lintegral_mono_set (Set.Ioc_subset_Ioc_right hε₀_le_one)
  rw [hJ_top] at hJ
  exact (lt_irrefl _ hJ).elim

/-- Two functions lying in the same outer `L²` ball of radius `q` are at
outer `L²` distance strictly less than `2q`. -/
private theorem outerLpNorm_two_sub_lt_two_mul_of_shared_center
    (Q : Measure Ω) (f g c : Ω → ℝ) (q : ℝ≥0∞)
    (hf : outerLpNorm Q (f - c) 2 < q)
    (hg : outerLpNorm Q (g - c) 2 < q) :
    outerLpNorm Q (f - g) 2 < 2 * q := by
  let X : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal |(f - c) x| ^ (2 : ℝ)
  let Y : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal |(g - c) x| ^ (2 : ℝ)
  have hpoint : (fun x => ENNReal.ofReal |(f - g) x| ^ (2 : ℝ)) ≤
      fun x => 2 * (X x + Y x) := by
    intro x
    have hreal : |f x - g x| ^ 2 ≤
        2 * (|f x - c x| ^ 2 + |g x - c x| ^ 2) := by
      have htri : |f x - g x| ≤ |f x - c x| + |g x - c x| := by
        calc
          |f x - g x| = |(f x - c x) - (g x - c x)| := by
            congr 1
            ring
          _ ≤ |f x - c x| + |g x - c x| := abs_sub _ _
      nlinarith [abs_nonneg (f x - g x), abs_nonneg (f x - c x),
        abs_nonneg (g x - c x),
        sq_nonneg (|f x - c x| - |g x - c x|),
        sq_nonneg (|f x - c x| + |g x - c x| - |f x - g x|)]
    simpa [X, Y, Pi.sub_apply, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
      using ENNReal.ofReal_le_ofReal hreal
  have houter : outerExpectation Q
      (fun x => ENNReal.ofReal |(f - g) x| ^ (2 : ℝ)) ≤
      2 * (outerExpectation Q X + outerExpectation Q Y) := by
    calc
      outerExpectation Q (fun x => ENNReal.ofReal |(f - g) x| ^ (2 : ℝ))
          ≤ outerExpectation Q (fun x => 2 * (X x + Y x)) :=
        outerExpectation_mono hpoint
      _ = 2 * outerExpectation Q (X + Y) := by
        rw [show (fun x => 2 * (X x + Y x)) = (2 : ℝ≥0∞) • (X + Y) by
          funext x
          simp [Pi.smul_apply, smul_eq_mul]]
        exact outerExpectation_const_smul 2 (by norm_num) _
      _ ≤ 2 * (outerExpectation Q X + outerExpectation Q Y) := by
        gcongr
        exact outerExpectation_add_le X Y
  have hf' : outerExpectation Q X < q ^ (2 : ℝ) := by
    have hsquare := (ENNReal.rpow_lt_rpow_iff
      (by norm_num : (0 : ℝ) < 2)).mpr hf
    unfold outerLpNorm at hsquare
    rw [← ENNReal.rpow_mul] at hsquare
    norm_num at hsquare
    simpa [X] using hsquare
  have hg' : outerExpectation Q Y < q ^ (2 : ℝ) := by
    have hsquare := (ENNReal.rpow_lt_rpow_iff
      (by norm_num : (0 : ℝ) < 2)).mpr hg
    unfold outerLpNorm at hsquare
    rw [← ENNReal.rpow_mul] at hsquare
    norm_num at hsquare
    simpa [Y] using hsquare
  have houter' : outerExpectation Q
      (fun x => ENNReal.ofReal |(f - g) x| ^ (2 : ℝ)) <
      (2 * q) ^ (2 : ℝ) := by
    refine houter.trans_lt ?_
    calc
      2 * (outerExpectation Q X + outerExpectation Q Y)
          < 2 * (q ^ (2 : ℝ) + q ^ (2 : ℝ)) := by
        gcongr
        · norm_num
      _ = (2 * q) ^ (2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
        ring
  unfold outerLpNorm
  apply (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [← ENNReal.rpow_mul]
  norm_num
  simpa only [Pi.sub_apply, ENNReal.rpow_two] using houter'

/-- A finite strict-covering number is attained by a finite strict cover. -/
private theorem exists_minimal_strictFiniteLpCover
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} {Q : Measure Ω} {r ε : ℝ}
    (hfinite : finiteLpCoveringNumber F G Q r ε < ⊤) :
    ∃ S : Finset (Ω → ℝ), IsStrictFiniteLpCover F G Q r ε S ∧
      (S.card : ℕ∞) = finiteLpCoveringNumber F G Q r ε := by
  let C := {S : Finset (Ω → ℝ) // IsStrictFiniteLpCover F G Q r ε S}
  haveI : Nonempty C := by
    by_contra hnone
    have htop : finiteLpCoveringNumber F G Q r ε = ⊤ := by
      apply top_unique
      unfold finiteLpCoveringNumber
      refine le_iInf fun S => le_iInf fun hS => ?_
      exact (hnone ⟨S, hS⟩).elim
    rw [htop] at hfinite
    exact (lt_irrefl _ hfinite).elim
  obtain ⟨S, hS⟩ := ENat.exists_eq_iInf fun S : C => (S.val.card : ℕ∞)
  refine ⟨S, S.property, ?_⟩
  rw [hS]
  unfold finiteLpCoveringNumber
  simp only [iInf_subtype']
  rfl

/-- At every dyadic level, ambient-center covering produces a finite net of
class representatives at twice the ambient radius. -/
private theorem exists_dyadic_classRepresentativeNet
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
    (Q : Measure Ω) (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ) :
    ∃ T : Finset ↥F,
      ((T.card : ℕ∞) ≤
        uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1))) ∧
      ∀ f : ↥F, ∃ g ∈ T,
        outerLpNorm Q ((f : Ω → ℝ) - (g : Ω → ℝ)) 2 <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * outerLpNorm Q G 2 := by
  classical
  let η : ℝ := (1 / 2 : ℝ) ^ (j + 1)
  have hη : 0 < η := pow_pos (by norm_num) _
  have hUnif : uniformLpCoveringNumber F G 2 η < ⊤ :=
    uniformLpCoveringNumber_lt_top_of_uniformEntropy hη hJ
  have hQle : finiteLpCoveringNumber F G Q 2 η ≤
      uniformLpCoveringNumber F G 2 η := by
    unfold uniformLpCoveringNumber
    exact le_iSup_of_le Q (le_iSup_of_le hQ le_rfl)
  have hfinite : finiteLpCoveringNumber F G Q 2 η < ⊤ :=
    hQle.trans_lt hUnif
  obtain ⟨S, hScover, hScard⟩ :=
    exists_minimal_strictFiniteLpCover hfinite
  let Good : (Ω → ℝ) → Prop := fun c =>
    ∃ f : ↥F, outerLpNorm Q ((f : Ω → ℝ) - c) 2 <
      ENNReal.ofReal η * outerLpNorm Q G 2
  let rep : (c : Ω → ℝ) → Good c → ↥F := fun c hc => Classical.choose hc
  let SG : Finset ↥S := S.attach.filter fun c : ↥S => Good c.1
  let T : Finset ↥F := SG.attach.image
    (fun c => rep c.1.1 (by
      have hc : c.1 ∈ S.attach.filter fun d : ↥S => Good d.1 := by
        simp [SG]
      exact (Finset.mem_filter.mp hc).2))
  refine ⟨T, ?_, ?_⟩
  · calc
      (T.card : ℕ∞) ≤ (SG.card : ℕ) := by
        have hTcard : T.card ≤ SG.card := by
          calc
            T.card ≤ SG.attach.card := by
              dsimp only [T]
              exact Finset.card_image_le
            _ = SG.card := Finset.card_attach
        exact_mod_cast hTcard
      _ ≤ (S.card : ℕ∞) := by
        exact_mod_cast (Finset.card_filter_le _ _).trans_eq S.card_attach
      _ = finiteLpCoveringNumber F G Q 2 η := hScard
      _ ≤ uniformLpCoveringNumber F G 2 η := hQle
  · intro f
    obtain ⟨c, hcS, hfc⟩ := hScover.2 f f.property
    have hcGood : Good c := ⟨f, hfc⟩
    let cs : ↥S := ⟨c, hcS⟩
    have hcs : cs ∈ SG :=
      Finset.mem_filter.mpr ⟨Finset.mem_attach S cs, hcGood⟩
    let g : ↥F := rep c hcGood
    have hgc : outerLpNorm Q ((g : Ω → ℝ) - c) 2 <
        ENNReal.ofReal η * outerLpNorm Q G 2 := Classical.choose_spec hcGood
    have hgT : g ∈ T := by
      let csg : ↥SG := ⟨cs, hcs⟩
      refine Finset.mem_image.mpr ⟨csg, Finset.mem_attach SG csg, ?_⟩
      apply Subtype.ext
      rfl
    refine ⟨g, hgT, (outerLpNorm_two_sub_lt_two_mul_of_shared_center
      Q (f : Ω → ℝ) (g : Ω → ℝ) c
      (ENNReal.ofReal η * outerLpNorm Q G 2) hfc hgc).trans_le ?_⟩
    dsimp [η]
    rw [← mul_assoc]
    gcongr
    rw [← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    rw [pow_succ]
    ring
    exact le_rfl

/-- The positive dyadic half-open intervals partition `(0,1]`. -/
private theorem uniformEntropy_iUnion_dyadic_Ioc_eq :
    ⋃ q : ℕ, Set.Ioc ((1 / 2 : ℝ) ^ (q + 1)) ((1 / 2 : ℝ) ^ q) =
      Set.Ioc 0 1 := by
  apply Set.eq_of_subset_of_subset
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ioc] at hx
    obtain ⟨q, hlo, hhi⟩ := hx
    refine ⟨lt_trans (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ (q + 1)) hlo, ?_⟩
    exact hhi.trans (pow_le_one₀ (by norm_num) (by norm_num))
  · intro x hx
    simp only [Set.mem_Ioc] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hexists : ∃ q : ℕ, (1 / 2 : ℝ) ^ q < x := by
      exact exists_pow_lt_of_lt_one hx0 (by norm_num : (1 / 2 : ℝ) < 1)
    classical
    let q₀ := Nat.find hexists
    have hq₀ : (1 / 2 : ℝ) ^ q₀ < x := Nat.find_spec hexists
    have hq₀_pos : 1 ≤ q₀ := by
      rcases Nat.eq_zero_or_pos q₀ with hzero | hpos
      · rw [hzero] at hq₀
        simp only [pow_zero] at hq₀
        exact (not_lt.mpr hx1 hq₀).elim
      · exact hpos
    obtain ⟨q, hq⟩ : ∃ q, q₀ = q + 1 := ⟨q₀ - 1, by omega⟩
    have hprev : ¬ (1 / 2 : ℝ) ^ q < x :=
      Nat.find_min hexists (by omega : q < q₀)
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    exact ⟨q, hq ▸ hq₀, not_lt.mp hprev⟩

/-- One uniform-cover dyadic entropy term is controlled by the entropy mass
on its corresponding half-open interval. -/
private theorem uniformEntropy_dyadic_term_le_two_setLIntegral
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} (q : ℕ) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q))
      ≤ 2 * ∫⁻ ε in Set.Ioc ((1 / 2 : ℝ) ^ (q + 1)) ((1 / 2 : ℝ) ^ q),
          entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume := by
  let aq : ℝ := (1 / 2 : ℝ) ^ q
  let aq1 : ℝ := (1 / 2 : ℝ) ^ (q + 1)
  have haq_pos : 0 < aq := by simp only [aq]; positivity
  have haq1_eq : aq1 = (1 / 2 : ℝ) * aq := by
    simp only [aq1, aq, pow_succ]
    ring
  have haq1_le : aq1 ≤ aq := by rw [haq1_eq]; nlinarith
  have hconst_le :
      ∫⁻ _ε in Set.Ioc aq1 aq,
          entropyWeight (uniformLpCoveringNumber F G 2 aq) ∂volume
        ≤ ∫⁻ ε in Set.Ioc aq1 aq,
            entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume := by
    refine setLIntegral_mono' measurableSet_Ioc (fun ε hε => ?_)
    exact entropyWeight_mono (uniformLpCoveringNumber_antitone_eps hε.2)
  rw [setLIntegral_const, Real.volume_Ioc] at hconst_le
  have hlen : aq - aq1 = (1 / 2 : ℝ) * aq := by rw [haq1_eq]; ring
  rw [hlen] at hconst_le
  have hsplit : ENNReal.ofReal aq =
      2 * ENNReal.ofReal ((1 / 2 : ℝ) * aq) := by
    rw [← ENNReal.ofReal_ofNat (n := 2),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  change ENNReal.ofReal aq *
      entropyWeight (uniformLpCoveringNumber F G 2 aq) ≤ _
  calc
    ENNReal.ofReal aq * entropyWeight (uniformLpCoveringNumber F G 2 aq)
        = 2 * (entropyWeight (uniformLpCoveringNumber F G 2 aq) *
            ENNReal.ofReal ((1 / 2 : ℝ) * aq)) := by rw [hsplit]; ring
    _ ≤ 2 * ∫⁻ ε in Set.Ioc aq1 aq,
          entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume := by
      gcongr

/-- The dyadic uniform-cover entropy series is bounded by twice the uniform
entropy integral. -/
private theorem uniformEntropy_dyadic_sum_le_integral
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} :
    (∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q)))
      ≤ 2 * uniformEntropyIntegral 1 F G 2 := by
  let I : ℕ → Set ℝ := fun q =>
    Set.Ioc ((1 / 2 : ℝ) ^ (q + 1)) ((1 / 2 : ℝ) ^ q)
  have hI_meas : ∀ q, MeasurableSet (I q) := fun _ => measurableSet_Ioc
  have hscale_anti : ∀ {m n : ℕ}, m ≤ n →
      (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m := by
    intro m n hmn
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hI_disj : Pairwise (Function.onFun Disjoint I) := by
    intro m n hmn
    wlog hlt : m < n generalizing m n
    · exact (this hmn.symm (by omega)).symm
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    simp only [I, Set.mem_Ioc] at hxm hxn
    have hxle : x ≤ (1 / 2 : ℝ) ^ (m + 1) :=
      hxn.2.trans (hscale_anti (by omega))
    exact (not_lt.mpr hxle hxm.1).elim
  calc
    (∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q)))
        ≤ ∑' q : ℕ, 2 * ∫⁻ ε in I q,
            entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume :=
      ENNReal.tsum_le_tsum (fun q => uniformEntropy_dyadic_term_le_two_setLIntegral q)
    _ = 2 * ∑' q : ℕ, ∫⁻ ε in I q,
          entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume := by
      rw [ENNReal.tsum_mul_left]
    _ = 2 * ∫⁻ ε in ⋃ q, I q,
          entropyWeight (uniformLpCoveringNumber F G 2 ε) ∂volume := by
      rw [lintegral_iUnion hI_meas hI_disj]
    _ = 2 * uniformEntropyIntegral 1 F G 2 := by
      rw [show (⋃ q, I q) = Set.Ioc (0 : ℝ) 1 by
        simpa [I] using uniformEntropy_iUnion_dyadic_Ioc_eq]
      rfl

/-- The shifted dyadic series generated by links from level `q` to `q + 1`
costs at most a factor two over the on-diagonal dyadic series. -/
private theorem uniformEntropy_shifted_dyadic_series_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} :
    (∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (q + 1))))
      ≤ 2 * ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
          entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q)) := by
  have hstep : ∀ q : ℕ,
      ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
          entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (q + 1))) =
        2 * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (q + 1)) *
          entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (q + 1)))) := by
    intro q
    have hval : (1 / 2 : ℝ) ^ q = 2 * (1 / 2 : ℝ) ^ (q + 1) := by
      rw [pow_succ]
      ring
    rw [hval, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat]
    ring
  have htail :
      (∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (q + 1)) *
          entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (q + 1))))
        ≤ ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
          entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q)) :=
    ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
      (fun q => ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q)))
  calc
    (∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (q + 1)))) =
      ∑' q : ℕ, 2 * (ENNReal.ofReal ((1 / 2 : ℝ) ^ (q + 1)) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (q + 1)))) :=
      tsum_congr hstep
    _ = 2 * ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (q + 1)) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (q + 1))) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ 2 * ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q) *
        entropyWeight (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ q)) := by
      gcongr

/-- Uniform entropy produces a nested Dudley schedule. The construction
uses arbitrary `MemLp` cover centers only as an intermediate device and returns
class representatives.  It includes the empty-class and zero-envelope cases
described by `UniformDudleySchedule`. -/
theorem uniformDudleySchedule_nonempty
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
      -- vdV 19.14 uniform `L²` entropy-integral condition.
    : Nonempty (UniformDudleySchedule F G) := by
  classical
  let rawData : ∀ (Q : Measure Ω) (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ),
      {T : Finset ↥F //
        ((T.card : ℕ∞) ≤
          uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1))) ∧
        ∀ f : ↥F, ∃ g ∈ T,
          outerLpNorm Q ((f : Ω → ℝ) - (g : Ω → ℝ)) 2 <
            ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * outerLpNorm Q G 2} :=
    fun Q hQ j => ⟨Classical.choose (exists_dyadic_classRepresentativeNet hJ Q hQ j),
      Classical.choose_spec (exists_dyadic_classRepresentativeNet hJ Q hQ j)⟩
  let rawNet : ∀ (Q : Measure Ω), IsAdmissibleMeasure G 2 Q → ℕ → Finset ↥F :=
    fun Q hQ j => (rawData Q hQ j).1
  let net : ∀ (Q : Measure Ω), IsAdmissibleMeasure G 2 Q → ℕ → Finset ↥F :=
    fun Q hQ j => (Finset.range (j + 1)).biUnion (rawNet Q hQ)
  refine ⟨net, ?_, ?_, ?_, ?_⟩
  · intro Q hQ j
    have hrange : Finset.range (j + 1) ⊆ Finset.range (j + 1 + 1) :=
      Finset.range_mono (by omega)
    exact Finset.biUnion_subset_biUnion_of_subset_left (rawNet Q hQ) hrange
  · intro Q hQ j f
    obtain ⟨g, hgraw, hfg⟩ := (rawData Q hQ j).2.2 f
    refine ⟨g, ?_, hfg⟩
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), hgraw⟩
  · intro Q hQ j
    calc
      ((net Q hQ j).card : ℕ∞) ≤
          ((∑ k ∈ Finset.range (j + 1), (rawNet Q hQ k).card : ℕ) : ℕ∞) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ k ∈ Finset.range (j + 1),
          uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (k + 1)) := by
        simp only [Nat.cast_sum]
        exact Finset.sum_le_sum fun k _ => (rawData Q hQ k).2.1
  · intro Q hQ
    let Nfun : ℕ → ℕ := fun j =>
      (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1))).toNat
    have hN_lt : ∀ j : ℕ,
        uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1)) < ⊤ :=
      fun j => uniformLpCoveringNumber_lt_top_of_uniformEntropy (by positivity) hJ
    have hN_eq : ∀ j : ℕ,
        uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1)) =
          (Nfun j : ℕ∞) :=
      fun j => (ENat.coe_toNat (hN_lt j).ne).symm
    have hraw_card : ∀ j : ℕ, (rawNet Q hQ j).card ≤ Nfun j := by
      intro j
      have h : ((rawNet Q hQ j).card : ℕ∞) ≤ (Nfun j : ℕ∞) :=
        (rawData Q hQ j).2.1.trans_eq (hN_eq j)
      exact_mod_cast h
    have hN_antitone : ∀ {i j : ℕ}, i ≤ j → Nfun i ≤ Nfun j := by
      intro i j hij
      have hscale : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (i + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hcover := uniformLpCoveringNumber_antitone_eps
        (F := F) (G := G) (r := 2) hscale
      rw [hN_eq i, hN_eq j] at hcover
      exact_mod_cast hcover
    have hnet_card : ∀ j : ℕ, (net Q hQ j).card ≤ (j + 1) * Nfun j := by
      intro j
      calc
        (net Q hQ j).card
            ≤ ∑ i ∈ Finset.range (j + 1), (rawNet Q hQ i).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ Finset.range (j + 1), Nfun j := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact (hraw_card i).trans (hN_antitone
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
        _ = (j + 1) * Nfun j := by
          rw [Finset.sum_const, Finset.card_range]
          ring
    have hsplit : ∀ j : ℕ,
        (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (net Q hQ j).card)) ≤
          (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (j + 1))) +
          (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (1 + Nfun j)) := by
      intro j
      have hNfun_nn : (0 : ℝ) ≤ (Nfun j : ℝ) := Nat.cast_nonneg _
      have hN_ge_one : (1 : ℝ) ≤ 1 + (Nfun j : ℝ) := by linarith
      have hcard_le : (2 * (net Q hQ j).card : ℝ) ≤
          (2 * (j + 1)) * (1 + Nfun j) := by
        have hreal : ((net Q hQ j).card : ℝ) ≤
            (((j + 1) * Nfun j : ℕ) : ℝ) := by
          exact_mod_cast hnet_card j
        push_cast at hreal ⊢
        nlinarith [hreal, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      have hlog_le : Real.log (2 * (net Q hQ j).card) ≤
          Real.log (2 * (j + 1)) + Real.log (1 + Nfun j) := by
        rcases Nat.eq_zero_or_pos (net Q hQ j).card with hzero | hpos
        · have hleft : Real.log (2 * (net Q hQ j).card) = 0 := by
            rw [hzero]
            norm_num
          rw [hleft]
          exact add_nonneg
            (Real.log_nonneg (by
              exact_mod_cast (show (1 : ℕ) ≤ 2 * (j + 1) by omega)))
            (Real.log_nonneg hN_ge_one)
        · have hcard_pos : (0 : ℝ) < 2 * (net Q hQ j).card := by
            exact mul_pos (by norm_num) (Nat.cast_pos.mpr hpos)
          calc
            Real.log (2 * (net Q hQ j).card)
                ≤ Real.log ((2 * (j + 1)) * (1 + Nfun j)) :=
              Real.log_le_log hcard_pos hcard_le
            _ = Real.log (2 * (j + 1)) + Real.log (1 + Nfun j) := by
              rw [Real.log_mul (by positivity) (by positivity)]
      have ha : (0 : ℝ) ≤ Real.log (2 * (j + 1)) :=
        Real.log_nonneg (by
          exact_mod_cast (show (1 : ℕ) ≤ 2 * (j + 1) by omega))
      have hb : (0 : ℝ) ≤ Real.log (1 + Nfun j) :=
        Real.log_nonneg hN_ge_one
      have hsqrt : Real.sqrt (Real.log (2 * (net Q hQ j).card)) ≤
          Real.sqrt (Real.log (2 * (j + 1))) +
            Real.sqrt (Real.log (1 + Nfun j)) := by
        refine (Real.sqrt_le_sqrt hlog_le).trans ?_
        rw [show Real.sqrt (Real.log (2 * (j + 1))) +
              Real.sqrt (Real.log (1 + Nfun j)) =
            Real.sqrt ((Real.sqrt (Real.log (2 * (j + 1))) +
              Real.sqrt (Real.log (1 + Nfun j))) ^ 2) from
          (Real.sqrt_sq (by positivity)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
          Real.sqrt_nonneg (Real.log (2 * (j + 1))),
          Real.sqrt_nonneg (Real.log (1 + Nfun j)),
          mul_nonneg (Real.sqrt_nonneg (Real.log (2 * (j + 1))))
            (Real.sqrt_nonneg (Real.log (1 + Nfun j)))]
      calc
        (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (net Q hQ j).card))
            ≤ (1 / 2 : ℝ) ^ j *
                (Real.sqrt (Real.log (2 * (j + 1))) +
                  Real.sqrt (Real.log (1 + Nfun j))) := by gcongr
        _ = _ := by ring
    have hsum1 : Summable (fun j : ℕ =>
        (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (j + 1)))) := by
      have hcmp : ∀ j : ℕ,
          (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (j + 1))) ≤
            (2 * ((j : ℝ) + 1)) * (1 / 2 : ℝ) ^ j := by
        intro j
        rw [mul_comm]
        gcongr
        have hx : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by positivity
        have hlog : Real.log (2 * ((j : ℝ) + 1)) ≤
            2 * ((j : ℝ) + 1) := by
          nlinarith [Real.log_le_sub_one_of_pos hx]
        calc
          Real.sqrt (Real.log (2 * ((j : ℝ) + 1))) ≤
              Real.sqrt (2 * ((j : ℝ) + 1)) := Real.sqrt_le_sqrt hlog
          _ ≤ 2 * ((j : ℝ) + 1) := by
            nlinarith [Real.sq_sqrt hx.le,
              Real.sqrt_nonneg (2 * ((j : ℝ) + 1)),
              Real.one_le_sqrt.mpr (by
                have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
                linarith : (1 : ℝ) ≤ 2 * ((j : ℝ) + 1))]
      apply Summable.of_nonneg_of_le (fun _ => by positivity) hcmp
      have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
      have hlinear : Summable (fun j : ℕ =>
          ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) := by
        have h1 : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
          (summable_pow_mul_geometric_of_norm_lt_one 1 hr).congr
            (fun j => by rw [pow_one])
        have h2 : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
          summable_geometric_of_norm_lt_one hr
        exact (h1.add h2).congr (fun j => by ring)
      exact (hlinear.mul_left 2).congr (fun j => by ring)
    have hsum2 : Summable (fun j : ℕ =>
        (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (1 + Nfun j))) := by
      let a : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
        ((1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (1 + Nfun j)))
      have ha_eq : ∀ j : ℕ, a j = ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
          entropyWeight
            (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1))) := by
        intro j
        simp only [a]
        rw [hN_eq j, entropyWeight_coe,
          ← ENNReal.ofReal_mul (by positivity)]
      have hatsum_ne : (∑' j : ℕ, a j) ≠ ⊤ := by
        have hle : (∑' j : ℕ, a j) ≤
            2 * (2 * uniformEntropyIntegral 1 F G 2) := by
          calc
            (∑' j : ℕ, a j) =
                ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
                  entropyWeight (uniformLpCoveringNumber F G 2
                    ((1 / 2 : ℝ) ^ (j + 1))) := tsum_congr ha_eq
            _ ≤ 2 * ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
                  entropyWeight (uniformLpCoveringNumber F G 2
                    ((1 / 2 : ℝ) ^ j)) := uniformEntropy_shifted_dyadic_series_le
            _ ≤ 2 * (2 * uniformEntropyIntegral 1 F G 2) := by
              gcongr
              exact uniformEntropy_dyadic_sum_le_integral
        refine ne_top_of_le_ne_top ?_ hle
        exact ENNReal.mul_ne_top (by norm_num)
          (ENNReal.mul_ne_top (by norm_num) hJ.ne)
      have hreal := ENNReal.summable_toReal hatsum_ne
      apply hreal.congr
      intro j
      simp only [a]
      rw [ENNReal.toReal_ofReal (by positivity)]
    exact Summable.of_nonneg_of_le (fun _ => by positivity) hsplit (hsum1.add hsum2)

/-- The canonical law-indexed Dudley schedule obtained from finite uniform
entropy.

This is a choice of the internally constructed schedule, not data supplied by
a caller. Edge behavior is inherited from `uniformDudleySchedule_nonempty`,
including the empty-class and zero-envelope cases. -/
noncomputable def uniformDudleySchedule_of_uniformEntropy
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) : UniformDudleySchedule F G :=
  Classical.choice (uniformDudleySchedule_nonempty hJ)

/-! ## Exact conditional sub-Gaussian increment -/

/-- Empirical `L²` seminorm on a finite sample.

It is the root mean square `((1/n) ∑ |f(zᵢ)|²)¹ᐟ²`.  Edge behavior: for
`n = 0`, Lean's totalized inverse and the empty sum give zero. -/
noncomputable def sampleL2Seminorm {n : ℕ} (z : Fin n → Ω)
    (f : Ω → ℝ) : ℝ :=
  Real.sqrt ((n : ℝ)⁻¹ * ∑ i, |f (z i)| ^ 2)

/-- The conditionally Rademacher empirical-process increment
`n⁻¹ᐟ² ∑ εᵢ f(zᵢ)`.

Signs are Boolean fair signs (`true = +1`, `false = -1`). Edge behavior:
at `n = 0` the totalized normalization and empty sum give zero. -/
noncomputable def conditionalRademacherIncrement {n : ℕ} (z : Fin n → Ω)
    (σ : Fin n → Bool) (f : Ω → ℝ) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * f (z i)

private noncomputable def chainingFairBoolMeasure : Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

private instance : IsProbabilityMeasure chainingFairBoolMeasure := by
  unfold chainingFairBoolMeasure
  infer_instance

private def chainingFairBoolSign (b : Bool) : ℝ := if b then 1 else -1

private theorem integral_chainingFairBoolSign :
    ∫ b, chainingFairBoolSign b ∂chainingFairBoolMeasure = 0 := by
  rw [chainingFairBoolMeasure, PMF.integral_eq_sum]
  simp [chainingFairBoolSign]

private theorem chainingFairBoolSign_hasSubgaussianMGF :
    ProbabilityTheory.HasSubgaussianMGF
      chainingFairBoolSign 1 chainingFairBoolMeasure := by
  have hmeas : AEMeasurable chainingFairBoolSign chainingFairBoolMeasure :=
    (measurable_of_finite chainingFairBoolSign).aemeasurable
  have hbound : ∀ᵐ b ∂chainingFairBoolMeasure,
      chainingFairBoolSign b ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall fun b => by
      cases b <;> simp [chainingFairBoolSign]
  convert ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := chainingFairBoolSign) (μ := chainingFairBoolMeasure)
    hmeas hbound integral_chainingFairBoolSign using 1
  norm_num

private noncomputable def chainingFairBoolCube (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => chainingFairBoolMeasure)

private instance (n : ℕ) : IsProbabilityMeasure (chainingFairBoolCube n) := by
  unfold chainingFairBoolCube
  infer_instance

private theorem chainingFairBoolCube_eq_uniform (n : ℕ) :
    chainingFairBoolCube n =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro σ
  have hpoint (b : Bool) :
      chainingFairBoolMeasure {b} = (2 : ℝ≥0∞)⁻¹ := by
    rw [chainingFairBoolMeasure, PMF.toMeasure_apply_singleton,
      PMF.uniformOfFintype_apply, Fintype.card_bool]
    · norm_num
    · exact MeasurableSet.singleton b
  rw [chainingFairBoolCube, Measure.pi_singleton, PMF.toMeasure_apply_fintype]
  simp_rw [hpoint]
  simp only [Set.indicator_singleton, PMF.uniformOfFintype_apply,
    Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_pi_single',
    Finset.mem_univ, if_true]
  exact ENNReal.inv_pow.symm

private theorem chaining_rademacherSum_hasSubgaussianMGF
    {n : ℕ} (a : Fin n → ℝ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun σ : Fin n → Bool =>
        ∑ i, chainingFairBoolSign (σ i) * a i)
      (∑ i, ⟨(a i) ^ 2, sq_nonneg (a i)⟩)
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  have hindep : ProbabilityTheory.iIndepFun
      (fun i (σ : Fin n → Bool) => a i * chainingFairBoolSign (σ i))
      (chainingFairBoolCube n) := by
    unfold chainingFairBoolCube
    have heval := ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin n => chainingFairBoolMeasure)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
    simpa [Function.comp_def] using heval.comp
      (fun i b => a i * chainingFairBoolSign b) (fun _ => measurable_of_finite _)
  have hcoord (i : Fin n) : ProbabilityTheory.HasSubgaussianMGF
      (fun σ : Fin n → Bool => a i * chainingFairBoolSign (σ i))
      ⟨(a i) ^ 2, sq_nonneg (a i)⟩ (chainingFairBoolCube n) := by
    have hmapped : ProbabilityTheory.HasSubgaussianMGF
        (fun b => a i * chainingFairBoolSign b)
        ⟨(a i) ^ 2, sq_nonneg (a i)⟩
        ((chainingFairBoolCube n).map fun σ => σ i) := by
      rw [chainingFairBoolCube,
        (measurePreserving_eval
          (fun _ : Fin n => chainingFairBoolMeasure) i).map_eq]
      have h := chainingFairBoolSign_hasSubgaussianMGF.const_mul (a i)
      have e : (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : NNReal) * 1 = ⟨(a i) ^ 2, sq_nonneg (a i)⟩ :=
        mul_one _
      exact e ▸ h
    simpa [Function.comp_def] using ProbabilityTheory.HasSubgaussianMGF.of_map
      (μ := chainingFairBoolCube n) (Y := fun σ : Fin n → Bool => σ i)
      (X := fun b => a i * chainingFairBoolSign b)
      (measurable_pi_apply i).aemeasurable hmapped
  rw [← chainingFairBoolCube_eq_uniform n]
  have hsum := ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
    (s := Finset.univ) hindep (fun i _ => hcoord i)
  simpa [chainingFairBoolSign, mul_comm] using hsum

omit [MeasurableSpace Ω] in
/-- Exact conditional Hoeffding bound for one empirical-`L²` increment.

The variance proxy is exactly `sampleL2Seminorm z (f-g)²`, giving
`2 exp (-t²/(2d²))`.  No measurability of `f`, `g`, or the envelope is needed
because the conditional sign cube is finite.  The `n = 0` and `d = 0` cases
use the displayed totalized real expression and are included literally. -/
theorem conditionalRademacher_increment_tail
    {n : ℕ} (z : Fin n → Ω) (f g : Ω → ℝ) (t : ℝ) (ht : 0 < t)
      -- positivity isolates the nontrivial tail threshold.
    : (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        {σ | t < |conditionalRademacherIncrement z σ f -
          conditionalRademacherIncrement z σ g|} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) /
        (2 * sampleL2Seminorm z (f - g) ^ 2))) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hempty : {σ : Fin 0 → Bool | t <
        |conditionalRademacherIncrement z σ f -
          conditionalRademacherIncrement z σ g|} = ∅ := by
      ext σ
      simp [conditionalRademacherIncrement, not_lt_of_ge ht.le]
    rw [hempty]
    rw [measure_empty]
    exact (bot_le : (0 : ℝ≥0∞) ≤ _)
  let ν := (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  let a : Fin n → ℝ := fun i =>
    (Real.sqrt n)⁻¹ * ((f - g) (z i))
  let Y : (Fin n → Bool) → ℝ := fun σ =>
    ∑ i, chainingFairBoolSign (σ i) * a i
  let v : NNReal := ∑ i, NNReal.mk ((a i) ^ 2) (sq_nonneg (a i))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase : 0 ≤ (n : ℝ)⁻¹ * ∑ i, |(f - g) (z i)| ^ 2 := by positivity
  have hv : (v : ℝ) = sampleL2Seminorm z (f - g) ^ 2 := by
    rw [sampleL2Seminorm, Real.sq_sqrt hbase]
    simp only [v, NNReal.coe_sum, NNReal.coe_mk, a, mul_pow]
    rw [← Finset.mul_sum]
    congr 1
    · rw [inv_pow, Real.sq_sqrt hnpos.le]
    · apply Finset.sum_congr rfl
      intro i _
      rw [sq_abs]
  have hinc (σ : Fin n → Bool) :
      conditionalRademacherIncrement z σ f -
          conditionalRademacherIncrement z σ g = Y σ := by
    simp only [conditionalRademacherIncrement, Y, a, chainingFairBoolSign,
      Pi.sub_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases σ i <;> simp <;> ring
  have hsubG : ProbabilityTheory.HasSubgaussianMGF Y v ν := by
    simpa [Y, v, ν] using! chaining_rademacherSum_hasSubgaussianMGF a
  let B : Set (Fin n → Bool) := {σ | t < |Y σ|}
  let Bpos : Set (Fin n → Bool) := {σ | t ≤ Y σ}
  let Bneg : Set (Fin n → Bool) := {σ | t ≤ -Y σ}
  have hB : B ⊆ Bpos ∪ Bneg := by
    intro σ hσ
    change t < |Y σ| at hσ
    change t ≤ Y σ ∨ t ≤ -Y σ
    rw [lt_abs] at hσ
    rcases hσ with hpos | hneg
    · exact Or.inl hpos.le
    · exact Or.inr hneg.le
  have hpos : ν Bpos ≤ ENNReal.ofReal
      (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [ν, Bpos] using hsubG.measure_ge_le ht.le)
  have hneg : ν Bneg ≤ ENNReal.ofReal
      (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (by
      simpa [ν, Bneg] using hsubG.neg.measure_ge_le ht.le)
  rw [show {σ | t < |conditionalRademacherIncrement z σ f -
      conditionalRademacherIncrement z σ g|} = B by
        ext σ
        change (t < |conditionalRademacherIncrement z σ f -
          conditionalRademacherIncrement z σ g|) ↔ t < |Y σ|
        rw [hinc]]
  calc
    ν B ≤ ν (Bpos ∪ Bneg) := measure_mono hB
    _ ≤ ν Bpos + ν Bneg := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) +
        ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * (v : ℝ)))) :=
      add_le_add hpos hneg
    _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2) /
        (2 * sampleL2Seminorm z (f - g) ^ 2))) := by
      rw [← two_mul, ← ENNReal.ofReal_ofNat 2,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), hv]

omit [MeasurableSpace Ω] in
/-- Conditional Rademacher increments have the empirical RMS squared as their
exact sub-Gaussian proxy. -/
private theorem conditionalRademacherIncrement_sub_hasSubgaussianMGF
    {n : ℕ} (z : Fin n → Ω) (f g : Ω → ℝ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun σ : Fin n → Bool => conditionalRademacherIncrement z σ f -
        conditionalRademacherIncrement z σ g)
      ⟨sampleL2Seminorm z (f - g) ^ 2, sq_nonneg _⟩
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  classical
  by_cases hn : n = 0
  · subst n
    have hz : ProbabilityTheory.HasSubgaussianMGF
        (fun _ : Fin 0 → Bool => (0 : ℝ)) 0
        (PMF.uniformOfFintype (Fin 0 → Bool)).toMeasure :=
      ProbabilityTheory.HasSubgaussianMGF.fun_zero
    have hX : (fun σ : Fin 0 → Bool => conditionalRademacherIncrement z σ f -
        conditionalRademacherIncrement z σ g) = fun _ => (0 : ℝ) := by
      funext σ
      simp [conditionalRademacherIncrement, Finset.univ_eq_empty]
    have hc : (⟨sampleL2Seminorm z (f - g) ^ 2, sq_nonneg _⟩ : NNReal) = 0 := by
      ext
      simp [sampleL2Seminorm, Finset.univ_eq_empty]
    rw [hX, hc]
    exact hz
  let a : Fin n → ℝ := fun i => (Real.sqrt n)⁻¹ * ((f - g) (z i))
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hbase : 0 ≤ (n : ℝ)⁻¹ * ∑ i, |(f - g) (z i)| ^ 2 := by positivity
  have hv : (∑ i, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : NNReal) : ℝ) =
      sampleL2Seminorm z (f - g) ^ 2 := by
    rw [sampleL2Seminorm, Real.sq_sqrt hbase]
    simp only [a, mul_pow]
    rw [← Finset.mul_sum]
    congr 1
    · rw [inv_pow, Real.sq_sqrt hnpos.le]
    · apply Finset.sum_congr rfl
      intro i _
      rw [sq_abs]
  have hinc (σ : Fin n → Bool) :
      conditionalRademacherIncrement z σ f -
          conditionalRademacherIncrement z σ g =
        ∑ i, chainingFairBoolSign (σ i) * a i := by
    simp only [conditionalRademacherIncrement, a, chainingFairBoolSign, Pi.sub_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases σ i <;> simp <;> ring
  have hX : (fun σ : Fin n → Bool => conditionalRademacherIncrement z σ f -
      conditionalRademacherIncrement z σ g) =
      fun σ => ∑ i, chainingFairBoolSign (σ i) * a i := funext hinc
  have hc : (⟨sampleL2Seminorm z (f - g) ^ 2, sq_nonneg _⟩ : NNReal) =
      ∑ i, (⟨(a i) ^ 2, sq_nonneg (a i)⟩ : NNReal) := by
    ext
    exact hv.symm.trans (NNReal.coe_sum _ _).symm
  rw [hX, hc]
  exact chaining_rademacherSum_hasSubgaussianMGF a

private theorem hasSubgaussianMGF_mono_proxy_chaining
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {Y : α → ℝ}
    {c d : NNReal} (h : ProbabilityTheory.HasSubgaussianMGF Y c μ)
    (hcd : c ≤ d) : ProbabilityTheory.HasSubgaussianMGF Y d μ := by
  refine ⟨h.integrable_exp_mul, fun t => ?_⟩
  refine (h.mgf_le t).trans (Real.exp_le_exp.mpr ?_)
  have hcdR : (c : ℝ) ≤ (d : ℝ) := NNReal.coe_le_coe.mpr hcd
  nlinarith [sq_nonneg t]

omit [MeasurableSpace Ω] in
/-- Expected maximum of a finite family of conditional Rademacher increments,
at the exact empirical-RMS scale. -/
private theorem outerExpectation_iSup_abs_increment_le
    {n : ℕ} (z : Fin n → Ω) (T : Finset ((Ω → ℝ) × (Ω → ℝ)))
    (hT : T.Nonempty) (ρ : ℝ) (hρ : 0 < ρ)
    (hdist : ∀ p ∈ T, sampleL2Seminorm z (p.1 - p.2) ≤ ρ) :
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal (⨆ p : ↥T,
          |conditionalRademacherIncrement z σ p.1.1 -
            conditionalRademacherIncrement z σ p.1.2|)) ≤
      ENNReal.ofReal (Real.sqrt 2 * ρ *
        Real.sqrt (Real.log (2 * T.card))) := by
  classical
  let ν := (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  let Z : ↥T → (Fin n → Bool) → ℝ := fun p σ =>
    conditionalRademacherIncrement z σ p.1.1 -
      conditionalRademacherIncrement z σ p.1.2
  let c : NNReal := NNReal.mk (ρ ^ 2) (sq_nonneg ρ)
  letI : Nonempty ↥T := Set.nonempty_coe_sort.mpr (by simpa using hT)
  have hZ : ∀ p : ↥T, ProbabilityTheory.HasSubgaussianMGF (Z p) c ν := by
    intro p
    have hbase := conditionalRademacherIncrement_sub_hasSubgaussianMGF
      z p.1.1 p.1.2
    apply hasSubgaussianMGF_mono_proxy_chaining hbase
    apply NNReal.coe_le_coe.mp
    change sampleL2Seminorm z (p.1.1 - p.1.2) ^ 2 ≤ ρ ^ 2
    have hp := hdist p p.2
    have hsample : 0 ≤ sampleL2Seminorm z (p.1.1 - p.1.2) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (sampleL2Seminorm z (p.1.1 - p.1.2))]
  have hmax := ProbabilityTheory.expectation_iSup_abs_le_of_subgaussian
    (μ := ν) (c := c) (by simpa [c] using! sq_pos_of_pos hρ) hZ
  have hMint : Integrable (fun σ => ⨆ p : ↥T, |Z p σ|) ν :=
    ProbabilityTheory.integrable_iSup_of_forall_integrable
      (fun p => (hZ p).integrable.abs)
  have hMnonneg : ∀ᵐ σ ∂ν, 0 ≤ ⨆ p : ↥T, |Z p σ| :=
    Filter.Eventually.of_forall fun σ => (abs_nonneg _).trans (le_ciSup
      (Finite.bddAbove_range fun p : ↥T => |Z p σ|) (Classical.choice inferInstance))
  rw [outerExpectation_eq_lintegral (measurable_of_finite _),
    ← ofReal_integral_eq_lintegral_ofReal hMint hMnonneg]
  refine ENNReal.ofReal_le_ofReal (hmax.trans_eq ?_)
  simp only [c, NNReal.coe_mk]
  rw [Fintype.card_coe]
  have hlog : 0 ≤ Real.log (2 * T.card) := by
    apply Real.log_nonneg
    have hcard : (1 : ℝ) ≤ T.card := by exact_mod_cast hT.card_pos
    linarith
  rw [show 2 * ρ ^ 2 * Real.log (2 * T.card) =
      2 * (ρ ^ 2 * Real.log (2 * T.card)) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ.le]
  ring

/-- The sample root-mean-square is bounded by the outer `L²` norm under the
empirical law.  This is deliberately an inequality: on a coarse measurable
space the outer norm can exceed the sample seminorm. -/
private theorem sampleL2Seminorm_le_outerLpNorm_empirical
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω) (f : Ω → ℝ) :
    ENNReal.ofReal (sampleL2Seminorm z f) ≤
      outerLpNorm (empiricalMeasure n z) f 2 := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hnR : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  have hsum : (0 : ℝ) ≤ ∑ i, |f (z i)| ^ 2 := by positivity
  have hbase : (0 : ℝ) ≤ (n : ℝ)⁻¹ * ∑ i, |f (z i)| ^ 2 := mul_nonneg hnR hsum
  have hraw : ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i, |f (z i)| ^ 2) ≤
      outerExpectation (empiricalMeasure n z)
        (fun x => ENNReal.ofReal |f x| ^ (2 : ℝ)) := by
    unfold outerExpectation
    refine le_iInf fun U => ?_
    rw [empiricalMeasure, lintegral_smul_measure, lintegral_finset_sum_measure]
    simp_rw [lintegral_dirac' _ U.2.1]
    rw [smul_eq_mul, ← ENNReal.ofReal_natCast n,
      ← ENNReal.ofReal_inv_of_pos (by exact_mod_cast hnpos)]
    rw [ENNReal.ofReal_mul hnR]
    apply mul_le_mul_right
    calc
      ENNReal.ofReal (∑ i, |f (z i)| ^ 2) =
          ∑ i, ENNReal.ofReal (|f (z i)| ^ 2) :=
        ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _
      _ ≤ ∑ i, (U : Ω → ℝ≥0∞) (z i) :=
        Finset.sum_le_sum fun i _ => by
          calc
            ENNReal.ofReal (|f (z i)| ^ 2) =
                ENNReal.ofReal |f (z i)| ^ (2 : ℝ) := by
              rw [ENNReal.ofReal_pow (abs_nonneg _) 2, ENNReal.rpow_two]
            _ ≤ (U : Ω → ℝ≥0∞) (z i) := U.2.2 (z i)
  unfold sampleL2Seminorm outerLpNorm
  have hsqrt : ENNReal.ofReal
      (Real.sqrt ((n : ℝ)⁻¹ * ∑ i, |f (z i)| ^ 2)) =
      (ENNReal.ofReal ((n : ℝ)⁻¹ * ∑ i, |f (z i)| ^ 2)) ^ (2 : ℝ)⁻¹ := by
    rw [Real.sqrt_eq_rpow]
    simpa [one_div] using (ENNReal.ofReal_rpow_of_nonneg hbase
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)).symm
  rw [hsqrt]
  exact ENNReal.rpow_le_rpow hraw (by norm_num)

omit [MeasurableSpace Ω] in
/-- A conditional Rademacher increment is pointwise controlled by `√n` times
the empirical root-mean-square seminorm.  (The sharper RMS scale is its
conditional sub-Gaussian metric, not a pointwise Lipschitz bound.) -/
private theorem abs_conditionalRademacherIncrement_sub_le_sqrt_mul_sampleL2
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω) (σ : Fin n → Bool)
    (f g : Ω → ℝ) :
    |conditionalRademacherIncrement z σ f -
        conditionalRademacherIncrement z σ g| ≤
      Real.sqrt n * sampleL2Seminorm z (f - g) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let d : Fin n → ℝ := fun i => (f - g) (z i)
  have hrewrite : conditionalRademacherIncrement z σ f -
      conditionalRademacherIncrement z σ g =
        (Real.sqrt n)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) * d i := by
    simp only [conditionalRademacherIncrement, d, Pi.sub_apply]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    cases σ i <;> simp; ring
  have habs : |∑ i, (if σ i then (1 : ℝ) else -1) * d i| ≤ ∑ i, |d i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro i _
    cases σ i <;> simp
  have hcs : ∑ i, |d i| ≤ Real.sqrt n * Real.sqrt (∑ i, |d i| ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun _ : Fin n => (1 : ℝ)) (fun i => |d i|)
    simpa using h
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  rw [hrewrite, abs_mul, abs_of_pos (inv_pos.mpr hsqrtpos)]
  calc
    (Real.sqrt n)⁻¹ * |∑ i, (if σ i then (1 : ℝ) else -1) * d i|
        ≤ (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt (∑ i, |d i| ^ 2)) :=
          mul_le_mul_of_nonneg_left (habs.trans hcs) (by positivity)
    _ = Real.sqrt n * Real.sqrt ((n : ℝ)⁻¹ * ∑ i, |d i| ^ 2) := by
      rw [show (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt (∑ i, |d i| ^ 2)) =
          Real.sqrt (∑ i, |d i| ^ 2) by field_simp,
        ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    _ = Real.sqrt n * sampleL2Seminorm z (f - g) := by
      simp only [sampleL2Seminorm, d]

omit [MeasurableSpace Ω] in
private theorem sampleL2Seminorm_eq_euclideanNorm
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω) (f : Ω → ℝ) :
    sampleL2Seminorm z f =
      ‖(WithLp.toLp 2 (fun i : Fin n => (Real.sqrt n)⁻¹ * f (z i)) :
        EuclideanSpace ℝ (Fin n))‖ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [sampleL2Seminorm, EuclideanSpace.norm_eq]
  congr 1
  simp only [Real.norm_eq_abs, abs_mul, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt hnpos.le]

omit [MeasurableSpace Ω] in
/-- Minkowski's inequality for the finite-sample RMS seminorm. -/
private theorem sampleL2Seminorm_add_le
    {n : ℕ} (z : Fin n → Ω) (f g : Ω → ℝ) :
    sampleL2Seminorm z (f + g) ≤ sampleL2Seminorm z f + sampleL2Seminorm z g := by
  by_cases hn : n = 0
  · subst n
    simp [sampleL2Seminorm, Finset.univ_eq_empty]
  let vf : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => (Real.sqrt n)⁻¹ * f (z i))
  let vg : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun i => (Real.sqrt n)⁻¹ * g (z i))
  rw [sampleL2Seminorm_eq_euclideanNorm hn z f,
    sampleL2Seminorm_eq_euclideanNorm hn z g,
    sampleL2Seminorm_eq_euclideanNorm hn z (f + g)]
  have hsum : (WithLp.toLp 2
      (fun i : Fin n => (Real.sqrt n)⁻¹ * (f + g) (z i)) :
      EuclideanSpace ℝ (Fin n)) = vf + vg := by
    ext i
    simp [vf, vg, Pi.add_apply, mul_add]
  rw [hsum]
  exact norm_add_le _ _

/-! ## Squared-difference GC result -/

/-- Squared pairwise differences generated by `F`.

This is the random-metric class used to replace empirical squared distances by
their population counterparts. Edge behavior: it is empty exactly when `F` is
empty. -/
def squareDifferenceClass (F : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  {h | ∃ f ∈ F, ∃ g ∈ F, h = fun x => (f x - g x) ^ 2}

/-- The canonical envelope `4 G²` of the squared-difference class.

Edge behavior: it is identically zero when `G` is zero; measurability is not
asserted because Theorem 19.14 permits a nonmeasurable envelope. -/
def squareDifferenceEnvelope (G : Ω → ℝ) : Ω → ℝ :=
  fun x => 4 * G x ^ 2

/-- The outer `L¹` norm of the canonical squared-difference envelope is
exactly four times the square of the outer `L²` norm of the original
envelope. -/
private theorem outerLpNorm_squareDifferenceEnvelope_one
    (Q : Measure Ω) (G : Ω → ℝ) :
    outerLpNorm Q (squareDifferenceEnvelope G) 1 =
      4 * (outerLpNorm Q G 2) ^ 2 := by
  have hfun : (fun x => ENNReal.ofReal |squareDifferenceEnvelope G x|) =
      fun x => 4 * ENNReal.ofReal |G x| ^ (2 : ℝ) := by
    funext x
    simp only [squareDifferenceEnvelope]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * G x ^ 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (G x)) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 2
    simp
  unfold outerLpNorm
  simp only [inv_one, ENNReal.rpow_one]
  rw [hfun, show (fun x => 4 * ENNReal.ofReal |G x| ^ (2 : ℝ)) =
      (4 : ℝ≥0∞) • (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) by
        funext x
        simp [Pi.smul_apply, smul_eq_mul],
    outerExpectation_const_smul 4 (by norm_num), smul_eq_mul]
  congr 1
  rw [← ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Squaring converts two quarter-radius outer `L²` approximations into an
`L¹` approximation relative to `4G²`.  The proof uses a scaled Young
inequality and therefore does not assume measurability of the class members. -/
private theorem outerLpNorm_squareDifference_sub_lt
    {F : Set (Ω → ℝ)} {G f g a b : Ω → ℝ} {Q : Measure Ω}
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hf : f ∈ F) (hg : g ∈ F) {ε : ℝ} (hε : 0 < ε) (hε6 : ε < 6)
    (hGpos : 0 < outerLpNorm Q G 2)
    (hGtop : outerLpNorm Q G 2 < ⊤)
    (hfa : outerLpNorm Q (f - a) 2 <
      ENNReal.ofReal (ε / 4) * outerLpNorm Q G 2)
    (hgb : outerLpNorm Q (g - b) 2 <
      ENNReal.ofReal (ε / 4) * outerLpNorm Q G 2) :
    outerLpNorm Q
        ((fun x => (f x - g x) ^ 2) - (fun x => (a x - b x) ^ 2)) 1 <
      ENNReal.ofReal ε * outerLpNorm Q (squareDifferenceEnvelope G) 1 := by
  let d : Ω → ℝ := (f - a) - (g - b)
  let A : ℝ≥0∞ := outerExpectation Q (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ))
  let D : ℝ≥0∞ := outerExpectation Q (fun x => ENNReal.ofReal |d x| ^ (2 : ℝ))
  have hnormG_sq : (outerLpNorm Q G 2) ^ 2 = A := by
    change (outerLpNorm Q G 2) ^ 2 =
      outerExpectation Q (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ))
    rw [← ENNReal.rpow_two]
    unfold outerLpNorm
    rw [← ENNReal.rpow_mul]
    norm_num
  have hApos : 0 < A := by
    rw [← hnormG_sq]
    positivity
  have hAtop : A < ⊤ := by
    rw [← hnormG_sq]
    exact ENNReal.pow_lt_top hGtop
  have hd : outerLpNorm Q d 2 <
      2 * (ENNReal.ofReal (ε / 4) * outerLpNorm Q G 2) := by
    have hfa0 : outerLpNorm Q ((f - a) - 0) 2 <
        ENNReal.ofReal (ε / 4) * outerLpNorm Q G 2 := by
      simpa using hfa
    have hgb0 : outerLpNorm Q ((g - b) - 0) 2 <
        ENNReal.ofReal (ε / 4) * outerLpNorm Q G 2 := by
      simpa using hgb
    simpa only [d, Pi.sub_apply, sub_zero] using
      outerLpNorm_two_sub_lt_two_mul_of_shared_center Q
        (f - a) (g - b) 0
        (ENNReal.ofReal (ε / 4) * outerLpNorm Q G 2) hfa0 hgb0
  have hD_lt : D < ENNReal.ofReal (ε ^ 2 / 4) * A := by
    have hsquare := (ENNReal.rpow_lt_rpow_iff
      (by norm_num : (0 : ℝ) < 2)).mpr hd
    have hnormD_sq : (outerLpNorm Q d 2) ^ (2 : ℝ) = D := by
      change (outerLpNorm Q d 2) ^ (2 : ℝ) =
        outerExpectation Q (fun x => ENNReal.ofReal |d x| ^ (2 : ℝ))
      unfold outerLpNorm
      rw [← ENNReal.rpow_mul]
      norm_num
    rw [hnormD_sq] at hsquare
    have hsquare' : D <
        (2 * (ENNReal.ofReal (ε / 4) * outerLpNorm Q G 2)) ^ (2 : ℝ) :=
      hsquare
    refine hsquare'.trans_eq ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ε / 4), hnormG_sq]
    rw [← mul_assoc, show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 2
    field_simp
  have hpoint : (fun x => ENNReal.ofReal
      |((fun y => (f y - g y) ^ 2) - (fun y => (a y - b y) ^ 2)) x|) ≤
      fun x => ENNReal.ofReal (2 * ε) * ENNReal.ofReal |G x| ^ (2 : ℝ) +
        ENNReal.ofReal (2 / ε + 1) * ENNReal.ofReal |d x| ^ (2 : ℝ) := by
    intro x
    have hu : |f x - g x| ≤ 2 * G x := by
      calc
        |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
        _ ≤ G x + G x := add_le_add (hEnv.2 f hf x) (hEnv.2 g hg x)
        _ = 2 * G x := by ring
    have hd_eq : (f x - g x) - (a x - b x) = d x := by
      simp only [d, Pi.sub_apply]
      ring
    have hdiff : |(f x - g x) ^ 2 - (a x - b x) ^ 2| ≤
        4 * G x * |d x| + |d x| ^ 2 := by
      rw [sq_sub_sq, abs_mul, hd_eq]
      have hv : |(f x - g x) + (a x - b x)| ≤ 4 * G x + |d x| := by
        have hv' : a x - b x = (f x - g x) - d x := by
          rw [← hd_eq]
          ring
        rw [hv']
        calc
          |(f x - g x) + ((f x - g x) - d x)| ≤
              |f x - g x| + |(f x - g x) - d x| := abs_add_le _ _
          _ ≤ |f x - g x| + (|f x - g x| + |d x|) := by
            gcongr
            exact abs_sub _ _
          _ ≤ 4 * G x + |d x| := by linarith
      calc
        |(f x - g x) + (a x - b x)| * |d x| ≤
            (4 * G x + |d x|) * |d x| := by gcongr
        _ = 4 * G x * |d x| + |d x| ^ 2 := by ring
    have hyoung : 4 * G x * |d x| ≤
        2 * ε * G x ^ 2 + (2 / ε) * |d x| ^ 2 := by
      field_simp
      nlinarith [sq_nonneg (ε * G x - |d x|)]
    have hreal : |(f x - g x) ^ 2 - (a x - b x) ^ 2| ≤
        2 * ε * G x ^ 2 + (2 / ε + 1) * |d x| ^ 2 := by
      linarith
    have hGsq : ENNReal.ofReal (G x ^ 2) =
        ENNReal.ofReal |G x| ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (G x))
        (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two, sq_abs]
    have hdsq : ENNReal.ofReal (|d x| ^ 2) =
        ENNReal.ofReal |d x| ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (d x))
        (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two]
    refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
    rw [ENNReal.ofReal_add (by positivity : 0 ≤ 2 * ε * G x ^ 2)
        (by positivity : 0 ≤ (2 / ε + 1) * |d x| ^ 2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * ε),
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / ε + 1), hGsq, hdsq]
  have hone : outerLpNorm Q
        ((fun x => (f x - g x) ^ 2) - (fun x => (a x - b x) ^ 2)) 1 =
      outerExpectation Q (fun x => ENNReal.ofReal
        |((fun y => (f y - g y) ^ 2) - (fun y => (a y - b y) ^ 2)) x|) := by
    unfold outerLpNorm
    simp only [inv_one, ENNReal.rpow_one]
  rw [hone, outerLpNorm_squareDifferenceEnvelope_one, hnormG_sq]
  have houter := (outerExpectation_mono (μ := Q) hpoint).trans
    (outerExpectation_add_le (μ := Q)
      (fun x => ENNReal.ofReal (2 * ε) * ENNReal.ofReal |G x| ^ (2 : ℝ))
      (fun x => ENNReal.ofReal (2 / ε + 1) * ENNReal.ofReal |d x| ^ (2 : ℝ)))
  rw [show (fun x => ENNReal.ofReal (2 * ε) * ENNReal.ofReal |G x| ^ (2 : ℝ)) =
      ENNReal.ofReal (2 * ε) • (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) by
        funext x; simp [Pi.smul_apply, smul_eq_mul],
    show (fun x => ENNReal.ofReal (2 / ε + 1) * ENNReal.ofReal |d x| ^ (2 : ℝ)) =
      ENNReal.ofReal (2 / ε + 1) • (fun x => ENNReal.ofReal |d x| ^ (2 : ℝ)) by
        funext x; simp [Pi.smul_apply, smul_eq_mul],
    outerExpectation_const_smul _ ENNReal.ofReal_ne_top,
    outerExpectation_const_smul _ ENNReal.ofReal_ne_top,
    smul_eq_mul] at houter
  change _ ≤ ENNReal.ofReal (2 * ε) * A +
    ENNReal.ofReal (2 / ε + 1) * D at houter
  have hcoef : 2 * ε + (2 / ε + 1) * (ε ^ 2 / 4) < 4 * ε := by
    field_simp
    nlinarith [sq_nonneg ε]
  have hnum : ENNReal.ofReal (2 * ε) * A + ENNReal.ofReal (2 / ε + 1) * D <
      ENNReal.ofReal ε * (4 * A) := by
    calc
      ENNReal.ofReal (2 * ε) * A + ENNReal.ofReal (2 / ε + 1) * D
        < ENNReal.ofReal (2 * ε) * A +
            ENNReal.ofReal (2 / ε + 1) *
              (ENNReal.ofReal (ε ^ 2 / 4) * A) := by
          exact ENNReal.add_lt_add_left
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAtop.ne)
            (ENNReal.mul_lt_mul_right
              (ENNReal.ofReal_ne_zero_iff.mpr (by positivity : 0 < 2 / ε + 1))
              ENNReal.ofReal_ne_top hD_lt)
    _ = ENNReal.ofReal
          (2 * ε + (2 / ε + 1) * (ε ^ 2 / 4)) * A := by
      calc
        ENNReal.ofReal (2 * ε) * A + ENNReal.ofReal (2 / ε + 1) *
              (ENNReal.ofReal (ε ^ 2 / 4) * A) =
            (ENNReal.ofReal (2 * ε) + ENNReal.ofReal (2 / ε + 1) *
              ENNReal.ofReal (ε ^ 2 / 4)) * A := by ring
        _ = ENNReal.ofReal
              (2 * ε + (2 / ε + 1) * (ε ^ 2 / 4)) * A := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / ε + 1),
            ← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * ε)
              (by positivity : 0 ≤ (2 / ε + 1) * (ε ^ 2 / 4))]
    _ < ENNReal.ofReal (4 * ε) * A := by
      exact ENNReal.mul_lt_mul_left hApos.ne' hAtop.ne
        ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 4 * ε)).2 hcoef)
    _ = ENNReal.ofReal ε * (4 * A) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
        ← mul_assoc, ← ENNReal.ofReal_mul hε.le]
      congr 2
      ring
  exact houter.trans_lt hnum

/-- Uniform-cover inequality
`N₁(ε, (F-F)², 4G²) ≤ N₂(ε/4, F, G)²`.

The exact quarter-scale and square are retained.  Centers remain `MemLp` as
required by the structural covering definition; no bracketing hypothesis is
introduced. -/
theorem squareDifference_uniformLpCoveringNumber_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- the pointwise envelope needed for the square inequality.
    (ε : ℝ) (hε : 0 < ε)
      -- the book only uses positive covering radii.
    : uniformLpCoveringNumber (squareDifferenceClass F)
        (squareDifferenceEnvelope G) 1 ε ≤
      (uniformLpCoveringNumber F G 2 (ε / 4)) ^ 2 := by
  classical
  rcases F.eq_empty_or_nonempty with hFempty | hFne
  · subst F
    have hsquareEmpty : squareDifferenceClass (∅ : Set (Ω → ℝ)) = ∅ := by
      ext h
      simp [squareDifferenceClass]
    rw [hsquareEmpty, uniformLpCoveringNumber_empty,
      uniformLpCoveringNumber_empty]
    simp
  · let K : ℕ∞ := uniformLpCoveringNumber F G 2 (ε / 4)
    change (⨆ (Q : Measure Ω), ⨆ (_hQ : IsAdmissibleMeasure
        (squareDifferenceEnvelope G) 1 Q),
          finiteLpCoveringNumber (squareDifferenceClass F)
            (squareDifferenceEnvelope G) Q 1 ε) ≤ K ^ 2
    refine iSup_le fun Q => iSup_le fun hQsquare => ?_
    have hrelation := outerLpNorm_squareDifferenceEnvelope_one Q G
    have hGpos : 0 < outerLpNorm Q G 2 := by
      have hprod : 0 < 4 * (outerLpNorm Q G 2) ^ 2 := by
        rw [← hrelation]
        exact hQsquare.2.1
      have hne : outerLpNorm Q G 2 ≠ 0 := by
        intro hz
        rw [hz] at hprod
        simp at hprod
      exact bot_lt_iff_ne_bot.mpr hne
    have hGtop : outerLpNorm Q G 2 < ⊤ := by
      have hprod : 4 * (outerLpNorm Q G 2) ^ 2 < ⊤ := by
        rw [← hrelation]
        exact hQsquare.2.2
      by_contra htop
      rw [not_lt, top_le_iff] at htop
      rw [htop] at hprod
      simp at hprod
    have hQG : IsAdmissibleMeasure G 2 Q :=
      ⟨hQsquare.1, hGpos, hGtop⟩
    have hQle : finiteLpCoveringNumber F G Q 2 (ε / 4) ≤ K := by
      dsimp only [K]
      exact le_iSup_of_le Q (le_iSup_of_le hQG le_rfl)
    by_cases hε6 : ε < 6
    · by_cases hKtop : K = ⊤
      · rw [hKtop]
        simp
      · have hfinite : finiteLpCoveringNumber F G Q 2 (ε / 4) < ⊤ :=
          hQle.trans_lt (lt_top_iff_ne_top.mpr hKtop)
        obtain ⟨S, hScover, hScard⟩ :=
          exists_minimal_strictFiniteLpCover hfinite
        let T : Finset (Ω → ℝ) := (S.product S).image
          (fun p x => (p.1 x - p.2 x) ^ 2)
        have hTcover : IsStrictFiniteLpCover (squareDifferenceClass F)
            (squareDifferenceEnvelope G) Q 1 ε T := by
          refine ⟨?_, ?_⟩
          · intro c hc
            obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
            obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
            have hpSub := (hScover.1 p.1 hp1).sub (hScover.1 p.2 hp2)
            norm_num at hpSub ⊢
            exact memLp_one_iff_integrable.mpr (by
              simpa only [Pi.sub_apply] using hpSub.integrable_sq)
          · intro h hh
            obtain ⟨f, hf, g, hg, rfl⟩ := hh
            obtain ⟨a, haS, hfa⟩ := hScover.2 f hf
            obtain ⟨b, hbS, hgb⟩ := hScover.2 g hg
            refine ⟨(fun x => (a x - b x) ^ 2), ?_, ?_⟩
            · exact Finset.mem_image.mpr
                ⟨(a, b), Finset.mem_product.mpr ⟨haS, hbS⟩, rfl⟩
            · exact outerLpNorm_squareDifference_sub_lt hEnv hf hg hε hε6
                hGpos hGtop hfa hgb
        calc
          finiteLpCoveringNumber (squareDifferenceClass F)
              (squareDifferenceEnvelope G) Q 1 ε ≤ (T.card : ℕ∞) :=
            finiteLpCoveringNumber_le_of_cover hTcover
          _ ≤ ((S.product S).card : ℕ) := by
            exact_mod_cast Finset.card_image_le
          _ = (S.card : ℕ∞) ^ 2 := by
            exact_mod_cast (by simp [pow_two] : (S.product S).card = S.card ^ 2)
          _ = (finiteLpCoveringNumber F G Q 2 (ε / 4)) ^ 2 := by rw [hScard]
          _ ≤ K ^ 2 := pow_le_pow_left' hQle 2
    · have hεlarge : 1 < ε := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 6)
          (not_lt.mp hε6)
      let T : Finset (Ω → ℝ) := {0}
      have hTcover : IsStrictFiniteLpCover (squareDifferenceClass F)
          (squareDifferenceEnvelope G) Q 1 ε T := by
        refine ⟨?_, ?_⟩
        · intro c hc
          have hc0 : c = 0 := by simpa [T] using hc
          subst c
          exact MemLp.zero
        · intro h hh
          obtain ⟨f, hf, g, hg, rfl⟩ := hh
          refine ⟨0, by simp [T], ?_⟩
          have hnorm_le : outerLpNorm Q (fun x => (f x - g x) ^ 2) 1 ≤
              outerLpNorm Q (squareDifferenceEnvelope G) 1 := by
            unfold outerLpNorm
            simp only [inv_one, ENNReal.rpow_one]
            apply outerExpectation_mono
            intro x
            apply ENNReal.ofReal_le_ofReal
            have hfg : |f x - g x| ≤ 2 * G x := by
              calc
                |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
                _ ≤ G x + G x := add_le_add (hEnv.2 f hf x) (hEnv.2 g hg x)
                _ = 2 * G x := by ring
            simp only [squareDifferenceEnvelope,
              abs_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * G x ^ 2)]
            calc
              (f x - g x) ^ 2 = |f x - g x| ^ 2 := (sq_abs _).symm
              _ ≤ (2 * G x) ^ 2 :=
                (sq_le_sq₀ (abs_nonneg _)
                  (mul_nonneg (by norm_num) (hEnv.1 x))).2 hfg
              _ = 4 * G x ^ 2 := by ring
          have hscale : outerLpNorm Q (squareDifferenceEnvelope G) 1 <
              ENNReal.ofReal ε * outerLpNorm Q (squareDifferenceEnvelope G) 1 := by
            simpa only [one_mul] using
              ENNReal.mul_lt_mul_left hQsquare.2.1.ne' hQsquare.2.2.ne
                ((ENNReal.one_lt_ofReal).2 hεlarge)
          simpa using hnorm_le.trans_lt hscale
      have honeFinite : (1 : ℕ∞) ≤ finiteLpCoveringNumber F G Q 2 (ε / 4) := by
        unfold finiteLpCoveringNumber
        refine le_iInf fun S => le_iInf fun hS => ?_
        obtain ⟨f, hf⟩ := hFne
        obtain ⟨c, hc, _⟩ := hS.2 f hf
        exact_mod_cast Finset.one_le_card.mpr ⟨c, hc⟩
      have honeK : (1 : ℕ∞) ≤ K := honeFinite.trans hQle
      calc
        finiteLpCoveringNumber (squareDifferenceClass F)
            (squareDifferenceEnvelope G) Q 1 ε ≤ (T.card : ℕ∞) :=
          finiteLpCoveringNumber_le_of_cover hTcover
        _ = 1 := by simp [T]
        _ ≤ K ^ 2 := by
          simpa using pow_le_pow_left' honeK 2

/-- The squared-difference class is GC under the Theorem 19.14 inputs.

This is the IID form consumed by conditional chaining.  Its proof must derive
pointwise measurability, the `4G²` outer first moment, and every uniform `L¹`
cover internally via the exact square-cover inequality. -/
theorem squareDifference_uniformCovering_isPGlivenkoCantelliIID
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
      -- vdV 19.14 measurable class members.
    (hPM : IsPointwiseMeasurable F)
      -- vdV 19.14 suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV 19.14 envelope condition.
    (hG2 : outerLpNorm P G 2 < ⊤)
      -- vdV 19.14 finite outer squared-envelope moment.
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
      -- vdV 19.14 uniform entropy integral.
    : IsPGlivenkoCantelliIID (squareDifferenceClass F) P := by
  classical
  have hSqMeas : ∀ h ∈ squareDifferenceClass F, Measurable h := by
    rintro h ⟨f, hf, g, hg, rfl⟩
    exact ((hFmeas f hf).sub (hFmeas g hg)).pow_const 2
  have hSqPM : IsPointwiseMeasurable (squareDifferenceClass F) := by
    obtain ⟨F₀, hF₀count, hF₀sub, hF₀dense⟩ := hPM
    let pairSq : ((Ω → ℝ) × (Ω → ℝ)) → (Ω → ℝ) :=
      fun p x => (p.1 x - p.2 x) ^ 2
    let S₀ : Set (Ω → ℝ) := pairSq '' (F₀ ×ˢ F₀)
    refine ⟨S₀, (hF₀count.prod hF₀count).image pairSq, ?_, ?_⟩
    · rintro h ⟨⟨f, g⟩, hfg, rfl⟩
      exact ⟨f, hF₀sub hfg.1, g, hF₀sub hfg.2, rfl⟩
    · rintro h ⟨f, hf, g, hg, rfl⟩
      obtain ⟨f₀, hf₀mem, hf₀lim⟩ := hF₀dense f hf
      obtain ⟨g₀, hg₀mem, hg₀lim⟩ := hF₀dense g hg
      let k : ℕ → (Ω → ℝ) := fun n x => (f₀ n x - g₀ n x) ^ 2
      refine ⟨k, ?_, ?_⟩
      · intro n
        exact ⟨(f₀ n, g₀ n), ⟨hf₀mem n, hg₀mem n⟩, rfl⟩
      · intro x
        simpa only [k] using (hf₀lim x).sub (hg₀lim x) |>.pow 2
  have hSqEnv : UniformEntropyStructural.IsEnvelope
      (squareDifferenceClass F) (squareDifferenceEnvelope G) := by
    refine ⟨?_, ?_⟩
    · intro x
      dsimp only [squareDifferenceEnvelope]
      positivity
    · rintro h ⟨f, hf, g, hg, rfl⟩ x
      have hfg : |f x - g x| ≤ 2 * G x := by
        calc
          |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
          _ ≤ G x + G x := add_le_add (hEnv.2 f hf x) (hEnv.2 g hg x)
          _ = 2 * G x := by ring
      simp only [abs_sq, squareDifferenceEnvelope]
      calc
        (f x - g x) ^ 2 = |f x - g x| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * G x) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (hEnv.1 x))).2 hfg
        _ = 4 * G x ^ 2 := by ring
  have hSqG1 : outerLpNorm P (squareDifferenceEnvelope G) 1 < ⊤ := by
    rw [outerLpNorm_squareDifferenceEnvelope_one]
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.pow_lt_top hG2)
  have hSqCover : ∀ η > 0,
      uniformLpCoveringNumber (squareDifferenceClass F)
        (squareDifferenceEnvelope G) 1 η < ⊤ := by
    intro η hη
    refine (squareDifference_uniformLpCoveringNumber_le hEnv η hη).trans_lt ?_
    have hK := uniformLpCoveringNumber_lt_top_of_uniformEntropy
      (F := F) (G := G) (by positivity : 0 < η / 4) hJ
    exact ENat.pow_lt_top_iff.mpr (Or.inl hK)
  intro Ξ _ μ _ X hXmeas hXindep hXid hXlaw
  exact uniformCovering_isPGlivenkoCantelliIID
    (squareDifferenceClass F) (squareDifferenceEnvelope G) P
    hSqMeas hSqPM hSqEnv hSqG1 hSqCover hXmeas hXindep hXid hXlaw

/-! ## Conditional chain and outer local modulus -/

/-- A finite outer second moment is witnessed by a measurable pointwise
majorant of the squared envelope.  The witness is kept internal because the
book allows `G` itself to be nonmeasurable. -/
private theorem exists_measurable_outerSquareMajorant
    (G : Ω → ℝ) (P : Measure Ω) (hG2 : outerLpNorm P G 2 < ⊤) :
    ∃ V : Ω → ℝ≥0∞, Measurable V ∧
      (∀ x, ENNReal.ofReal |G x| ^ (2 : ℝ) ≤ V x) ∧
      ∫⁻ x, V x ∂P < ⊤ := by
  have houter : outerExpectation P
      (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) < ⊤ := by
    unfold outerLpNorm at hG2
    exact (ENNReal.rpow_lt_top_iff_of_pos
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).mp hG2
  let Majorants := {V : Ω → ℝ≥0∞ //
    Measurable V ∧ (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) ≤ V}
  by_contra hnone
  have h_all : ∀ V : Majorants, (∫⁻ x, (V : Ω → ℝ≥0∞) x ∂P) = ⊤ := by
    intro V
    exact top_unique (not_lt.mp (fun hlt =>
      hnone ⟨V.1, V.2.1, V.2.2, hlt⟩))
  have htop : outerExpectation P
      (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) = ⊤ := by
    unfold outerExpectation
    apply top_unique
    refine le_iInf fun V => ?_
    rw [h_all V]
  exact (not_lt_of_ge (le_of_eq htop.symm)) houter

private theorem empirical_outerLpNorm_lt_top_of_majorant
    {G : Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hVmeas : Measurable V)
    (hGV : ∀ x, ENNReal.ofReal |G x| ^ (2 : ℝ) ≤ V x)
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hVz : ∀ i, V (z i) < ⊤) :
    outerLpNorm (empiricalMeasure n z) G 2 < ⊤ := by
  letI : NeZero n := ⟨hn⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hncast : (0 : ℝ≥0∞) < n := by exact_mod_cast hnpos
  have hVemp : (∫⁻ x, V x ∂empiricalMeasure n z) < ⊤ := by
    simp only [empiricalMeasure, lintegral_smul_measure,
      lintegral_finset_sum_measure, lintegral_dirac' _ hVmeas, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 hncast)
      (ENNReal.sum_lt_top.2 fun i _ => hVz i)
  have houter : outerExpectation (empiricalMeasure n z)
      (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) < ⊤ := by
    calc
      outerExpectation (empiricalMeasure n z)
          (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) ≤
          outerExpectation (empiricalMeasure n z) V := outerExpectation_mono hGV
      _ = ∫⁻ x, V x ∂empiricalMeasure n z :=
        outerExpectation_eq_lintegral hVmeas
      _ < ⊤ := hVemp
  unfold outerLpNorm
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) houter.ne

private theorem ae_empirical_outerLpNorm_lt_top
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (P : Measure Ω) (X : ℕ → Ξ → Ω) (G : Ω → ℝ) (V : Ω → ℝ≥0∞)
    (hVmeas : Measurable V)
    (hGV : ∀ x, ENNReal.ofReal |G x| ^ (2 : ℝ) ≤ V x)
    (hVint : ∫⁻ x, V x ∂P < ⊤)
    (hXmeas : ∀ i, Measurable (X i)) (hXlaw : ∀ i, μ.map (X i) = P) :
    ∀ᵐ ξ ∂μ, ∀ n : ℕ, n ≠ 0 →
      outerLpNorm (empiricalMeasure n (fun i => X i.val ξ)) G 2 < ⊤ := by
  have hVfiniteP : ∀ᵐ x ∂P, V x < ⊤ := ae_lt_top hVmeas hVint.ne
  have hVfiniteX : ∀ᵐ ξ ∂μ, ∀ i : ℕ, V (X i ξ) < ⊤ :=
    ae_all_iff.2 fun i =>
      (MeasurePreserving.mk (hXmeas i) (hXlaw i)).quasiMeasurePreserving.ae hVfiniteP
  filter_upwards [hVfiniteX] with ξ hξ
  intro n hn
  exact empirical_outerLpNorm_lt_top_of_majorant hVmeas hGV hn _
    (fun i => hξ i.val)

omit [MeasurableSpace Ω] in
private theorem sampleL2Seminorm_sq_eq_empiricalAvg
    {n : ℕ} (z : Fin n → Ω) (f : Ω → ℝ) :
    sampleL2Seminorm z f ^ 2 = empiricalAvg (fun x => f x ^ 2) n z := by
  have hbase : 0 ≤ (n : ℝ)⁻¹ * ∑ i, |f (z i)| ^ 2 := by positivity
  rw [sampleL2Seminorm, Real.sq_sqrt hbase]
  unfold empiricalAvg
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact sq_abs (f (z i))

private theorem distL2_sq_eq_integral_sq
    {P : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 P) :
    distL2 P f 0 ^ 2 = ∫ x, f x ^ 2 ∂P := by
  have hint_nonneg : (0 : ℝ) ≤
      ∫ x, ‖f x‖ ^ (2 : ℝ≥0∞).toReal ∂P := integral_nonneg fun _ => by positivity
  rw [distL2, show f - 0 = f by ext; simp,
    hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hint_nonneg _)]
  rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hint_nonneg]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  rw [inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change ‖f x‖ ^ (2 : ℝ) = f x ^ 2
  rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, sq_abs]

private theorem sampleL2Seminorm_sq_le_distL2_sq_add_of_gcDeviation_le
    {Ξ : Type*} {F : Set (Ω → ℝ)} {P : Measure Ω}
    (X : ℕ → Ξ → Ω) {n : ℕ} (ξ : Ξ) {f g : Ω → ℝ}
    (hf : f ∈ F) (hg : g ∈ F) (hfgLp : MemLp (f - g) 2 P)
    {η : ℝ} (hη : 0 ≤ η)
    (hdev : gcDeviation (squareDifferenceClass F) P X n ξ ≤ ENNReal.ofReal η) :
    sampleL2Seminorm (fun i : Fin n => X i.val ξ) (f - g) ^ 2 ≤
      distL2 P f g ^ 2 + η := by
  let h : Ω → ℝ := fun x => (f x - g x) ^ 2
  have hh : h ∈ squareDifferenceClass F := ⟨f, hf, g, hg, rfl⟩
  have hterm : ENNReal.ofReal
      |empiricalAvg h n (fun i : Fin n => X i.val ξ) - ∫ x, h x ∂P| ≤
      gcDeviation (squareDifferenceClass F) P X n ξ := by
    exact le_supNormOver hh
  have habs : |empiricalAvg h n (fun i : Fin n => X i.val ξ) -
      ∫ x, h x ∂P| ≤ η := by
    have hof := hterm.trans hdev
    exact (ENNReal.ofReal_le_ofReal_iff hη).mp hof
  have hpop : distL2 P f g ^ 2 = ∫ x, h x ∂P := by
    have heq : f - g - 0 = f - g := by ext; simp
    have := distL2_sq_eq_integral_sq hfgLp
    rw [show distL2 P f g = distL2 P (f - g) 0 by
      unfold distL2; rw [heq]]
    simpa only [h, Pi.sub_apply] using this
  rw [sampleL2Seminorm_sq_eq_empiricalAvg]
  change empiricalAvg h n (fun i : Fin n => X i.val ξ) ≤ distL2 P f g ^ 2 + η
  rw [hpop]
  have hup : empiricalAvg h n (fun i : Fin n => X i.val ξ) -
      ∫ x, h x ∂P ≤ η :=
    (le_abs_self (empiricalAvg h n (fun i : Fin n => X i.val ξ) -
      ∫ x, h x ∂P)).trans habs
  linarith

private theorem distL2_sq_le_sampleL2Seminorm_sq_add_of_gcDeviation_le
    {Ξ : Type*} {F : Set (Ω → ℝ)} {P : Measure Ω}
    (X : ℕ → Ξ → Ω) {n : ℕ} (ξ : Ξ) {f g : Ω → ℝ}
    (hf : f ∈ F) (hg : g ∈ F) (hfgLp : MemLp (f - g) 2 P)
    {η : ℝ} (hη : 0 ≤ η)
    (hdev : gcDeviation (squareDifferenceClass F) P X n ξ ≤ ENNReal.ofReal η) :
    distL2 P f g ^ 2 ≤
      sampleL2Seminorm (fun i : Fin n => X i.val ξ) (f - g) ^ 2 + η := by
  let h : Ω → ℝ := fun x => (f x - g x) ^ 2
  have hh : h ∈ squareDifferenceClass F := ⟨f, hf, g, hg, rfl⟩
  have hterm : ENNReal.ofReal
      |empiricalAvg h n (fun i : Fin n => X i.val ξ) - ∫ x, h x ∂P| ≤
      gcDeviation (squareDifferenceClass F) P X n ξ := le_supNormOver hh
  have habs : |empiricalAvg h n (fun i : Fin n => X i.val ξ) -
      ∫ x, h x ∂P| ≤ η := by
    exact (ENNReal.ofReal_le_ofReal_iff hη).mp (hterm.trans hdev)
  have hpop : distL2 P f g ^ 2 = ∫ x, h x ∂P := by
    have heq : f - g - 0 = f - g := by ext; simp
    have := distL2_sq_eq_integral_sq hfgLp
    rw [show distL2 P f g = distL2 P (f - g) 0 by
      unfold distL2; rw [heq]]
    simpa only [h, Pi.sub_apply] using this
  rw [sampleL2Seminorm_sq_eq_empiricalAvg, hpop]
  have hlower : ∫ x, h x ∂P -
      empiricalAvg h n (fun i : Fin n => X i.val ξ) ≤ η := by
    calc
      ∫ x, h x ∂P - empiricalAvg h n (fun i : Fin n => X i.val ξ) =
          -(empiricalAvg h n (fun i : Fin n => X i.val ξ) - ∫ x, h x ∂P) := by ring
      _ ≤ |empiricalAvg h n (fun i : Fin n => X i.val ξ) - ∫ x, h x ∂P| :=
        neg_le_abs _
      _ ≤ η := habs
  change ∫ x, h x ∂P ≤ empiricalAvg h n (fun i : Fin n => X i.val ξ) + η
  linarith

private theorem classMember_memLp_of_l2Envelope
    {F : Set (Ω → ℝ)} {H : Ω → ℝ} {P : Measure Ω}
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    {f : Ω → ℝ} (hf : f ∈ F) : MemLp f 2 P := by
  apply hHLp.mono (hFmeas f hf).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hHenv.1 x)] using hHenv.2 f hf x

omit [MeasurableSpace Ω] in
private theorem sampleL2Seminorm_sub_le_two_envelope
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    {n : ℕ} (z : Fin n → Ω) {f g : Ω → ℝ} (hf : f ∈ F) (hg : g ∈ F) :
    sampleL2Seminorm z (f - g) ≤ 2 * sampleL2Seminorm z G := by
  have hsq : sampleL2Seminorm z (f - g) ^ 2 ≤
      4 * sampleL2Seminorm z G ^ 2 := by
    rw [sampleL2Seminorm_sq_eq_empiricalAvg,
      sampleL2Seminorm_sq_eq_empiricalAvg]
    unfold empiricalAvg
    calc
      (n : ℝ)⁻¹ * ∑ i, (f - g) (z i) ^ 2 ≤
          (n : ℝ)⁻¹ * ∑ i, 4 * G (z i) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        have hdiff : |f (z i) - g (z i)| ≤ 2 * G (z i) := by
          calc
            |f (z i) - g (z i)| ≤ |f (z i)| + |g (z i)| := abs_sub _ _
            _ ≤ G (z i) + G (z i) :=
              add_le_add (hEnv.2 f hf _) (hEnv.2 g hg _)
            _ = 2 * G (z i) := by ring
        calc
          (f - g) (z i) ^ 2 = |f (z i) - g (z i)| ^ 2 := by
            simp only [Pi.sub_apply, sq_abs]
          _ ≤ (2 * G (z i)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
          _ = 4 * G (z i) ^ 2 := by ring
      _ = 4 * ((n : ℝ)⁻¹ * ∑ i, G (z i) ^ 2) := by
        rw [← Finset.mul_sum]
        ring
  have hleft : 0 ≤ sampleL2Seminorm z (f - g) := by unfold sampleL2Seminorm; positivity
  have hright : 0 ≤ sampleL2Seminorm z G := by unfold sampleL2Seminorm; positivity
  nlinarith

private theorem sampleL2Seminorm_le_outerLpNorm_toReal
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω) (f : Ω → ℝ)
    (hfinite : outerLpNorm (empiricalMeasure n z) f 2 < ⊤) :
    sampleL2Seminorm z f ≤ (outerLpNorm (empiricalMeasure n z) f 2).toReal := by
  have hsample := sampleL2Seminorm_le_outerLpNorm_empirical hn z f
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hfinite.ne).2 hsample
  have hsnonneg : 0 ≤ sampleL2Seminorm z f := by
    unfold sampleL2Seminorm
    positivity
  rw [ENNReal.toReal_ofReal hsnonneg] at hreal
  exact hreal

private theorem sampleLocal_of_squareDeviation
    {Ξ : Type*} {F F₀ : Set (Ω → ℝ)} {G H : Ω → ℝ} {P : Measure Ω}
    (X : ℕ → Ξ → Ω) {n : ℕ} (hn : n ≠ 0) (ξ : Ξ)
    (hF₀sub : F₀ ⊆ F) (hFmeas : ∀ f ∈ F, Measurable f)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    {fstar gstar : Ω → ℝ} (hfstar : fstar ∈ F₀) (hgstar : gstar ∈ F₀)
    {d : ℝ} (hd : d = distL2 P fstar gstar) (hdpos : 0 < d)
    (J : ℕ) {δ : ℝ}
    (hδ : δ < (1 / 2 : ℝ) ^ J * d / 8)
    (hfinite : outerLpNorm
      (empiricalMeasure n (fun i : Fin n => X i.val ξ)) G 2 < ⊤)
    (hdev : gcDeviation (squareDifferenceClass F) P X n ξ ≤
      ENNReal.ofReal (((1 / 2 : ℝ) ^ J * d / 8) ^ 2)) :
    0 < outerLpNorm (empiricalMeasure n (fun i : Fin n => X i.val ξ)) G 2 ∧
      ∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g < δ →
        sampleL2Seminorm (fun i : Fin n => X i.val ξ) (f - g) <
          (1 / 2 : ℝ) ^ J *
            (outerLpNorm
              (empiricalMeasure n (fun i : Fin n => X i.val ξ)) G 2).toReal := by
  let a : ℝ := (1 / 2 : ℝ) ^ J * d / 8
  let z : Fin n → Ω := fun i => X i.val ξ
  let L := outerLpNorm (empiricalMeasure n z) G 2
  have ha0 : 0 ≤ a := by dsimp only [a]; positivity
  have ha_le : a ≤ d / 8 := by
    dsimp only [a]
    have hp : (1 / 2 : ℝ) ^ J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc
      (1 / 2 : ℝ) ^ J * d / 8 ≤ 1 * d / 8 := by gcongr
      _ = d / 8 := by ring
  have hfLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp
    (hF₀sub hfstar)
  have hgLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp
    (hF₀sub hgstar)
  have hanchorSq : d ^ 2 ≤ sampleL2Seminorm z (fstar - gstar) ^ 2 + a ^ 2 := by
    rw [hd]
    exact distL2_sq_le_sampleL2Seminorm_sq_add_of_gcDeviation_le
      X ξ (hF₀sub hfstar) (hF₀sub hgstar) (hfLp.sub hgLp)
        (sq_nonneg a) (by simpa only [a] using hdev)
  have hanchor : d / 2 < sampleL2Seminorm z (fstar - gstar) := by
    have hsamp0 : 0 ≤ sampleL2Seminorm z (fstar - gstar) := by
      unfold sampleL2Seminorm
      positivity
    by_contra hnot
    have hsamp : sampleL2Seminorm z (fstar - gstar) ≤ d / 2 := le_of_not_gt hnot
    nlinarith [sq_nonneg (d / 8 - a), sq_nonneg (d / 2 -
      sampleL2Seminorm z (fstar - gstar))]
  have hsampleG : sampleL2Seminorm z G ≤ L.toReal :=
    sampleL2Seminorm_le_outerLpNorm_toReal hn z G hfinite
  have hanchorEnv : sampleL2Seminorm z (fstar - gstar) ≤
      2 * sampleL2Seminorm z G :=
    sampleL2Seminorm_sub_le_two_envelope hEnv z
      (hF₀sub hfstar) (hF₀sub hgstar)
  have hLreal : d / 4 < L.toReal := by nlinarith
  have hLpos : 0 < L := by
    exact bot_lt_iff_ne_bot.mpr fun hzero => by
      rw [hzero] at hLreal
      norm_num at hLreal
      linarith
  refine ⟨hLpos, ?_⟩
  intro f hf g hg hfg
  have hfLp' := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp (hF₀sub hf)
  have hgLp' := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp (hF₀sub hg)
  have hlocalSq : sampleL2Seminorm z (f - g) ^ 2 ≤
      distL2 P f g ^ 2 + a ^ 2 :=
    sampleL2Seminorm_sq_le_distL2_sq_add_of_gcDeviation_le
      X ξ (hF₀sub hf) (hF₀sub hg) (hfLp'.sub hgLp') (sq_nonneg a)
        (by simpa only [a] using hdev)
  have hlocal : sampleL2Seminorm z (f - g) < 2 * a := by
    have hsamp0 : 0 ≤ sampleL2Seminorm z (f - g) := by
      unfold sampleL2Seminorm
      positivity
    have hfg_a : distL2 P f g < a := hfg.trans hδ
    have hdist0 : 0 ≤ distL2 P f g := by unfold distL2; positivity
    have ha_pos : 0 < a := by dsimp only [a]; positivity
    by_contra hnot
    have hsamp : 2 * a ≤ sampleL2Seminorm z (f - g) := le_of_not_gt hnot
    nlinarith
  have hpowpos : 0 < (1 / 2 : ℝ) ^ J := pow_pos (by norm_num) J
  calc
    sampleL2Seminorm z (f - g) < 2 * a := hlocal
    _ = (1 / 2 : ℝ) ^ J * (d / 4) := by dsimp only [a]; ring
    _ < (1 / 2 : ℝ) ^ J * L.toReal := by gcongr

private theorem ae_eventually_sampleL2Seminorm_sq_le_distL2_sq_add
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (F : Set (Ω → ℝ)) (P : Measure Ω) (X : ℕ → Ξ → Ω)
    (H : Ω → ℝ) (hFmeas : ∀ f ∈ F, Measurable f)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    (hSqGC : IsPGlivenkoCantelliIID.{_, 0} (squareDifferenceClass F) P)
    [IsProbabilityMeasure μ]
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    ∀ᵐ ξ ∂μ, ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      ∀ (f : ↥F) (g : ↥F),
        sampleL2Seminorm (fun i : Fin n => X i.val ξ)
            ((f : Ω → ℝ) - g) ^ 2 ≤
          distL2 P (f : Ω → ℝ) (g : Ω → ℝ) ^ 2 + η := by
  have hgc : ∀ᵐ ξ ∂μ, Tendsto
      (fun n => gcDeviation (squareDifferenceClass F) P X n ξ) atTop (𝓝 0) :=
    hSqGC (Ξ := Ξ) (μ := μ) (X := X) hXmeas hXiindep hXid hXlaw
  filter_upwards [hgc] with ξ hξ
  intro η hη
  have hev : ∀ᶠ n in atTop,
      gcDeviation (squareDifferenceClass F) P X n ξ ≤ ENNReal.ofReal η := by
    filter_upwards [hξ (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hη))] with n hn
    exact hn.le
  filter_upwards [hev] with n hn
  intro f g
  have hfLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp f.property
  have hgLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp g.property
  exact sampleL2Seminorm_sq_le_distL2_sq_add_of_gcDeviation_le
    X ξ f.property g.property (hfLp.sub hgLp) hη.le hn

/-- Pointwise skeleton approximation is also `L²(P)` approximation when all
terms remain in a class with one `L²` envelope. -/
private theorem tendsto_distL2_of_pointwise_under_envelope
    {F : Set (Ω → ℝ)} {H : Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    {f : Ω → ℝ} (hf : f ∈ F) {φ : ℕ → (Ω → ℝ)}
    (hφmem : ∀ m, φ m ∈ F)
    (hφlim : ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x))) :
    Tendsto (fun m => distL2 P (φ m) f) atTop (𝓝 0) := by
  have hboundInt : Integrable (fun x => 4 * H x ^ 2) P :=
    hHLp.integrable_sq.const_mul 4
  have hdom : ∀ m, ∀ᵐ x ∂P, ‖(φ m x - f x) ^ 2‖ ≤ 4 * H x ^ 2 := by
    intro m
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_sq]
    have hdiff : |φ m x - f x| ≤ 2 * H x := by
      calc
        |φ m x - f x| ≤ |φ m x| + |f x| := abs_sub _ _
        _ ≤ H x + H x := add_le_add (hHenv.2 _ (hφmem m) x) (hHenv.2 f hf x)
        _ = 2 * H x := by ring
    calc
      (φ m x - f x) ^ 2 = |φ m x - f x| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * H x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
      _ = 4 * H x ^ 2 := by ring
  have hsqInt : Tendsto (fun m => ∫ x, (φ m x - f x) ^ 2 ∂P) atTop
      (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence
      (fun x => 4 * H x ^ 2)
      (fun m => (((hFmeas _ (hφmem m)).sub (hFmeas f hf)).pow_const 2).aestronglyMeasurable)
      hboundInt hdom
      (Eventually.of_forall fun x => ((hφlim x).sub tendsto_const_nhds).pow 2)
    simpa using ht
  have hsq : ∀ m, distL2 P (φ m) f ^ 2 =
      ∫ x, (φ m x - f x) ^ 2 ∂P := by
    intro m
    simpa only [distL2, Pi.sub_apply, sub_zero] using
      (distL2_sq_eq_integral_sq
        ((classMember_memLp_of_l2Envelope hFmeas hHenv hHLp (hφmem m)).sub
          (classMember_memLp_of_l2Envelope hFmeas hHenv hHLp hf)))
  have hsqDist : Tendsto (fun m => distL2 P (φ m) f ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hsqInt
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsqDist
  convert hsqrt using 1
  · funext m
    change distL2 P (φ m) f = Real.sqrt (distL2 P (φ m) f ^ 2)
    exact (Real.sqrt_sq (by unfold distL2; exact ENNReal.toReal_nonneg)).symm
  · simp

/-- Population-local differences drawn from a fixed countable skeleton. -/
private def skeletonLocalDifferenceClass (F₀ : Set (Ω → ℝ))
    (P : Measure Ω) (δ : ℝ) : Set (Ω → ℝ) :=
  {h | ∃ f ∈ F₀, ∃ g ∈ F₀, distL2 P f g < δ ∧ h = f - g}

/-- Countable skeleton local supremum used as the measurable version of the
population-local empirical modulus. -/
private noncomputable def skeletonLocalProcessModulus {Ξ : Type*}
    (F₀ : Set (Ω → ℝ)) (P : Measure Ω) (X : ℕ → Ξ → Ω)
    (n : ℕ) (δ : ℝ) (ξ : Ξ) : ℝ≥0∞ :=
  supNormOver (skeletonLocalDifferenceClass F₀ P δ)
    (empiricalProcess P n (fun i : Fin n => X i.val ξ))

/-- Conditional oscillation of the Rademacher process over empirically
`L²`-close pairs.  Edge behavior: an empty class gives zero; nonpositive
`δ` retains the literal strict ball; at `n = 0` every increment is zero. -/
noncomputable def conditionalRademacherLocalOscillation
    (F : Set (Ω → ℝ)) {n : ℕ} (z : Fin n → Ω) (δ : ℝ)
    (σ : Fin n → Bool) : ℝ≥0∞ :=
  ⨆ (f : ↥F), ⨆ (g : ↥F),
    if sampleL2Seminorm z ((f : Ω → ℝ) - (g : Ω → ℝ)) < δ then
      ENNReal.ofReal |conditionalRademacherIncrement z σ (f : Ω → ℝ) -
        conditionalRademacherIncrement z σ (g : Ω → ℝ)|
    else 0

private theorem skeletonLocalDifferenceClass_countable
    {F₀ : Set (Ω → ℝ)} (hF₀ : F₀.Countable) (P : Measure Ω) (δ : ℝ) :
    (skeletonLocalDifferenceClass F₀ P δ).Countable := by
  let D : Set ((Ω → ℝ) × (Ω → ℝ)) :=
    {p | p.1 ∈ F₀ ∧ p.2 ∈ F₀ ∧ distL2 P p.1 p.2 < δ}
  have hD : D.Countable := by
    apply (hF₀.prod hF₀).mono
    intro p hp
    change p.1 ∈ F₀ ∧ p.2 ∈ F₀ ∧ distL2 P p.1 p.2 < δ at hp
    exact ⟨hp.1, hp.2.1⟩
  have himage : skeletonLocalDifferenceClass F₀ P δ =
      (fun p : (Ω → ℝ) × (Ω → ℝ) => p.1 - p.2) '' D := by
    ext h
    constructor
    · rintro ⟨f, hf, g, hg, hfg, rfl⟩
      exact ⟨(f, g), ⟨hf, hg, hfg⟩, rfl⟩
    · rintro ⟨⟨f, g⟩, ⟨hf, hg, hfg⟩, rfl⟩
      exact ⟨f, hf, g, hg, hfg, rfl⟩
  rw [himage]
  exact hD.image _

private theorem skeletonLocalDifferenceClass_measurable
    {F₀ : Set (Ω → ℝ)} (hFmeas : ∀ f ∈ F₀, Measurable f)
    (P : Measure Ω) (δ : ℝ) :
    ∀ h ∈ skeletonLocalDifferenceClass F₀ P δ, Measurable h := by
  rintro h ⟨f, hf, g, hg, -, rfl⟩
  exact (hFmeas f hf).sub (hFmeas g hg)

private theorem skeletonLocalDifferenceClass_pointwiseMeasurable
    {F₀ : Set (Ω → ℝ)} (hF₀ : F₀.Countable) (P : Measure Ω) (δ : ℝ) :
    IsPointwiseMeasurable (skeletonLocalDifferenceClass F₀ P δ) := by
  let E := skeletonLocalDifferenceClass F₀ P δ
  refine ⟨E, skeletonLocalDifferenceClass_countable hF₀ P δ, Set.Subset.rfl, ?_⟩
  intro h hh
  exact ⟨fun _ => h, fun _ => hh, fun x => tendsto_const_nhds⟩

omit [MeasurableSpace Ω] in
private theorem supNormOver_eq_iSup_subtype_chaining
    (E : Set (Ω → ℝ)) (L : (Ω → ℝ) → ℝ) :
    supNormOver E L = ⨆ f : E, ENNReal.ofReal |L f| := by
  apply le_antisymm
  · refine iSup_le fun f => iSup_le fun hf => ?_
    exact le_iSup_of_le (⟨f, hf⟩ : E) le_rfl
  · refine iSup_le fun f => ?_
    exact le_iSup_of_le f.1 (le_iSup_of_le f.2 le_rfl)

private theorem measurable_ghostDeviation_countable
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ) (hEcount : E.Countable)
    (hEmeas : ∀ f ∈ E, Measurable f) (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (fun ξ : Ξ × Ξ => ghostDeviation E X n ξ.1 ξ.2) := by
  letI : Countable E := hEcount
  unfold ghostDeviation
  rw [show (fun ξ : Ξ × Ξ => supNormOver E (fun f =>
      empiricalAvg f n (fun i : Fin n => X i.val ξ.1) -
        empiricalAvg f n (fun i : Fin n => X i.val ξ.2))) =
      fun ξ => ⨆ f : E, ENNReal.ofReal
        |empiricalAvg f n (fun i : Fin n => X i.val ξ.1) -
          empiricalAvg f n (fun i : Fin n => X i.val ξ.2)| by
    funext ξ
    exact supNormOver_eq_iSup_subtype_chaining E _]
  apply Measurable.iSup
  intro f
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.sub <;> unfold empiricalAvg <;> apply Measurable.const_mul
  · exact Finset.measurable_sum _ fun i _ =>
      (hEmeas f (f.property)).comp ((hXmeas i.val).comp measurable_fst)
  · exact Finset.measurable_sum _ fun i _ =>
      (hEmeas f (f.property)).comp ((hXmeas i.val).comp measurable_snd)

private theorem measurable_signedGhostDeviation_countable
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ) (σ : Fin n → Bool) (hEcount : E.Countable)
    (hEmeas : ∀ f ∈ E, Measurable f) (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (fun ξ : Ξ × Ξ => signedGhostDeviation E n
      (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ) := by
  letI : Countable E := hEcount
  unfold signedGhostDeviation
  rw [show (fun ξ : Ξ × Ξ => supNormOver E (fun f =>
      (n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) *
        (f (X i.val ξ.1) - f (X i.val ξ.2)))) =
      fun ξ => ⨆ f : E, ENNReal.ofReal
        |(n : ℝ)⁻¹ * ∑ i, (if σ i then (1 : ℝ) else -1) *
          (f.1 (X i.val ξ.1) - f.1 (X i.val ξ.2))| by
    funext ξ
    exact supNormOver_eq_iSup_subtype_chaining E _]
  apply Measurable.iSup
  intro f
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ =>
    (((hEmeas f (f.property)).comp ((hXmeas i.val).comp measurable_fst)).sub
      ((hEmeas f (f.property)).comp ((hXmeas i.val).comp measurable_snd))).const_mul _

omit [MeasurableSpace Ω] in
private theorem abs_empiricalAvg_le_chaining
    (f t : Ω → ℝ) (n : ℕ) (z : Fin n → Ω)
    (hft : ∀ x, |f x| ≤ t x) :
    |empiricalAvg f n z| ≤ empiricalAvg t n z := by
  unfold empiricalAvg
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hft (z i))

private theorem skeletonLocalDifference_abs_le_two_envelope
    {F F₀ : Set (Ω → ℝ)} {H : Ω → ℝ} {P : Measure Ω} {δ : ℝ}
    (hF₀sub : F₀ ⊆ F) (hHenv : UniformEntropyStructural.IsEnvelope F H)
    {h : Ω → ℝ} (hh : h ∈ skeletonLocalDifferenceClass F₀ P δ) (x : Ω) :
    |h x| ≤ 2 * H x := by
  obtain ⟨f, hf, g, hg, -, rfl⟩ := hh
  calc
    |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ H x + H x := add_le_add (hHenv.2 f (hF₀sub hf) x)
      (hHenv.2 g (hF₀sub hg) x)
    _ = 2 * H x := by ring

private theorem ghostDeviation_skeleton_le_envelope_samples
    {Ξ : Type*} {F F₀ : Set (Ω → ℝ)} {H : Ω → ℝ}
    (P : Measure Ω) (δ : ℝ) (X : ℕ → Ξ → Ω) (n : ℕ) (ξ ξ' : Ξ)
    (hF₀sub : F₀ ⊆ F) (hHenv : UniformEntropyStructural.IsEnvelope F H) :
    ghostDeviation (skeletonLocalDifferenceClass F₀ P δ) X n ξ ξ' ≤
      ENNReal.ofReal (2 * empiricalAvg H n (fun i : Fin n => X i.val ξ) +
        2 * empiricalAvg H n (fun i : Fin n => X i.val ξ')) := by
  unfold ghostDeviation supNormOver
  apply iSup_le
  intro h
  apply iSup_le
  intro hh
  apply ENNReal.ofReal_le_ofReal
  have hz := abs_empiricalAvg_le_chaining h (fun x => 2 * H x) n
    (fun i : Fin n => X i.val ξ)
    (skeletonLocalDifference_abs_le_two_envelope hF₀sub hHenv hh)
  have hz' := abs_empiricalAvg_le_chaining h (fun x => 2 * H x) n
    (fun i : Fin n => X i.val ξ')
    (skeletonLocalDifference_abs_le_two_envelope hF₀sub hHenv hh)
  rw [empiricalAvg_smul] at hz hz'
  exact (abs_sub _ _).trans (add_le_add hz hz')

private theorem signedGhostDeviation_skeleton_le_envelope_samples
    {F F₀ : Set (Ω → ℝ)} {H : Ω → ℝ}
    (P : Measure Ω) (δ : ℝ) {n : ℕ} (z z' : Fin n → Ω)
    (σ : Fin n → Bool) (hF₀sub : F₀ ⊆ F)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) :
    signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ) n z z' σ ≤
      ENNReal.ofReal (2 * empiricalAvg H n z + 2 * empiricalAvg H n z') := by
  unfold signedGhostDeviation supNormOver
  apply iSup_le
  intro h
  apply iSup_le
  intro hh
  apply ENNReal.ofReal_le_ofReal
  unfold empiricalAvg
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
  calc
    (n : ℝ)⁻¹ * |∑ i, (if σ i then (1 : ℝ) else -1) *
        (h (z i) - h (z' i))| ≤
        (n : ℝ)⁻¹ * ∑ i, (2 * H (z i) + 2 * H (z' i)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (n : ℝ)⁻¹)
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hsign : |if σ i then (1 : ℝ) else -1| = 1 := by
        cases σ i <;> simp
      rw [hsign, one_mul]
      exact (abs_sub _ _).trans (add_le_add
        (skeletonLocalDifference_abs_le_two_envelope hF₀sub hHenv hh (z i))
        (skeletonLocalDifference_abs_le_two_envelope hF₀sub hHenv hh (z' i)))
    _ = 2 * ((n : ℝ)⁻¹ * ∑ i, H (z i)) +
        2 * ((n : ℝ)⁻¹ * ∑ i, H (z' i)) := by
      have hzsum : ∑ i, 2 * H (z i) = 2 * ∑ i, H (z i) :=
        (Finset.mul_sum Finset.univ (fun i => H (z i)) 2).symm
      have hzsum' : ∑ i, 2 * H (z' i) = 2 * ∑ i, H (z' i) :=
        (Finset.mul_sum Finset.univ (fun i => H (z' i)) 2).symm
      rw [Finset.sum_add_distrib, hzsum, hzsum']
      ring

private theorem ghostDeviation_skeleton_ne_top
    {Ξ : Type*} {F F₀ : Set (Ω → ℝ)} {H : Ω → ℝ}
    (P : Measure Ω) (δ : ℝ) (X : ℕ → Ξ → Ω) (n : ℕ) (ξ ξ' : Ξ)
    (hF₀sub : F₀ ⊆ F) (hHenv : UniformEntropyStructural.IsEnvelope F H) :
    ghostDeviation (skeletonLocalDifferenceClass F₀ P δ) X n ξ ξ' ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (ghostDeviation_skeleton_le_envelope_samples P δ X n ξ ξ' hF₀sub hHenv)

private theorem signedGhostDeviation_skeleton_ne_top
    {F F₀ : Set (Ω → ℝ)} {H : Ω → ℝ}
    (P : Measure Ω) (δ : ℝ) {n : ℕ} (z z' : Fin n → Ω)
    (σ : Fin n → Bool) (hF₀sub : F₀ ⊆ F)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) :
    signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ) n z z' σ ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (signedGhostDeviation_skeleton_le_envelope_samples
      P δ z z' σ hF₀sub hHenv)

private theorem measurable_conditionalRademacherTail_countable
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ) (ε : ℝ) (hEcount : E.Countable)
    (hEmeas : ∀ f ∈ E, Measurable f) (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (fun ξ : Ξ × Ξ => conditionalRademacherTail E n
      (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) ε) := by
  classical
  let c : ℝ≥0∞ := (Fintype.card (Fin n → Bool) : ℝ≥0∞)⁻¹
  let A : (Fin n → Bool) → Set (Ξ × Ξ) := fun σ =>
    {ξ | ENNReal.ofReal ε < signedGhostDeviation E n
      (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ}
  have hAmeas (σ : Fin n → Bool) : MeasurableSet (A σ) :=
    measurableSet_lt measurable_const
      (measurable_signedGhostDeviation_countable E X n σ hEcount hEmeas hXmeas)
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
  simp_rw [htail]
  exact Finset.measurable_sum _ fun σ _ => measurable_const.indicator (hAmeas σ)

private theorem measurable_conditionalRademacherTail_joint_countable
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ) (hEcount : E.Countable)
    (hEmeas : ∀ f ∈ E, Measurable f) (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (fun p : (Ξ × Ξ) × ℝ => conditionalRademacherTail E n
      (fun i => X i.val p.1.1) (fun i => X i.val p.1.2) p.2) := by
  classical
  let c : ℝ≥0∞ := (Fintype.card (Fin n → Bool) : ℝ≥0∞)⁻¹
  let A : (Fin n → Bool) → Set ((Ξ × Ξ) × ℝ) := fun σ =>
    {p | ENNReal.ofReal p.2 < signedGhostDeviation E n
      (fun i => X i.val p.1.1) (fun i => X i.val p.1.2) σ}
  have hsigned (σ : Fin n → Bool) : Measurable (fun p : (Ξ × Ξ) × ℝ =>
      signedGhostDeviation E n (fun i => X i.val p.1.1)
        (fun i => X i.val p.1.2) σ) :=
    (measurable_signedGhostDeviation_countable E X n σ hEcount hEmeas hXmeas).comp
      measurable_fst
  have hAmeas (σ : Fin n → Bool) : MeasurableSet (A σ) :=
    measurableSet_lt measurable_snd.ennreal_ofReal (hsigned σ)
  have htail (p : (Ξ × Ξ) × ℝ) :
      conditionalRademacherTail E n (fun i => X i.val p.1.1)
          (fun i => X i.val p.1.2) p.2 =
        ∑ σ : Fin n → Bool, (A σ).indicator (fun _ => c) p := by
    rw [conditionalRademacherTail, PMF.toMeasure_apply_fintype]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : ENNReal.ofReal p.2 < signedGhostDeviation E n
        (fun i => X i.val p.1.1) (fun i => X i.val p.1.2) σ
    · simp [hσ, A, c]
    · simp [hσ, A, c]
  simp_rw [htail]
  exact Finset.measurable_sum _ fun σ _ => measurable_const.indicator (hAmeas σ)

omit [MeasurableSpace Ω] in
private theorem lintegral_signedGhostDeviation_eq_tail
    (E : Set (Ω → ℝ)) {n : ℕ} (z z' : Fin n → Ω)
    (hfinite : ∀ σ : Fin n → Bool, signedGhostDeviation E n z z' σ ≠ ⊤) :
    ∫⁻ σ, signedGhostDeviation E n z z' σ
        ∂(PMF.uniformOfFintype (Fin n → Bool)).toMeasure =
      ∫⁻ t in Set.Ioi (0 : ℝ), conditionalRademacherTail E n z z' t ∂volume := by
  let ν := (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  have hmeas : Measurable (fun σ : Fin n → Bool =>
      (signedGhostDeviation E n z z' σ).toReal) := measurable_of_finite _
  calc
    ∫⁻ σ, signedGhostDeviation E n z z' σ ∂ν =
        ∫⁻ σ, ENNReal.ofReal (signedGhostDeviation E n z z' σ).toReal ∂ν := by
      apply lintegral_congr
      intro σ
      exact (ENNReal.ofReal_toReal (hfinite σ)).symm
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          ν {σ | t < (signedGhostDeviation E n z z' σ).toReal} ∂volume :=
      lintegral_eq_lintegral_meas_lt ν
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hmeas.aemeasurable
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), conditionalRademacherTail E n z z' t ∂volume := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      rw [conditionalRademacherTail]
      apply congrArg ((PMF.uniformOfFintype (Fin n → Bool)).toMeasure)
      ext σ
      change (t < (signedGhostDeviation E n z z' σ).toReal) ↔
        ENNReal.ofReal t < signedGhostDeviation E n z z' σ
      exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hfinite σ)).symm

/-- Layer-cake integration upgrades the tail comparison to the
expected ghost/signed-process comparison needed by the local chaining step. -/
private theorem outerExpectation_ghostDeviation_le_signed
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (n : ℕ)
    (hEcount : E.Countable) (hEmeas : ∀ f ∈ E, Measurable f)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hghostfinite : ∀ ξ : Ξ × Ξ, ghostDeviation E X n ξ.1 ξ.2 ≠ ⊤)
    (hsignedfinite : ∀ (ξ : Ξ × Ξ) (σ : Fin n → Bool),
      signedGhostDeviation E n (fun i => X i.val ξ.1)
        (fun i => X i.val ξ.2) σ ≠ ⊤) :
    outerExpectation (μ.prod μ) (fun ξ => ghostDeviation E X n ξ.1 ξ.2) ≤
      outerExpectation (μ.prod μ) (fun ξ =>
        outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (fun σ => signedGhostDeviation E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) σ)) := by
  let ρ := μ.prod μ
  let ν := (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  have hPM : IsPointwiseMeasurable E :=
    ⟨E, hEcount, Set.Subset.rfl, fun f hf =>
      ⟨fun _ => f, fun _ => hf, fun _ => tendsto_const_nhds⟩⟩
  have hghostMeas : Measurable (fun ξ : Ξ × Ξ =>
      ghostDeviation E X n ξ.1 ξ.2) :=
    measurable_ghostDeviation_countable E X n hEcount hEmeas hXmeas
  have htailMeas (t : ℝ) : Measurable (fun ξ : Ξ × Ξ =>
      conditionalRademacherTail E n (fun i => X i.val ξ.1)
        (fun i => X i.val ξ.2) t) :=
    measurable_conditionalRademacherTail_countable
      E X n t hEcount hEmeas hXmeas
  have htailJoint : Measurable (fun p : (Ξ × Ξ) × ℝ =>
      conditionalRademacherTail E n (fun i => X i.val p.1.1)
        (fun i => X i.val p.1.2) p.2) :=
    measurable_conditionalRademacherTail_joint_countable
      E X n hEcount hEmeas hXmeas
  have hghostSet (t : ℝ) (ht : 0 < t) :
      {ξ : Ξ × Ξ | t < (ghostDeviation E X n ξ.1 ξ.2).toReal} =
        ghostBad E X n t := by
    ext ξ
    exact (ENNReal.ofReal_lt_iff_lt_toReal ht.le (hghostfinite ξ)).symm
  have htailBound (t : ℝ) (ht : 0 < t) :
      ρ {ξ : Ξ × Ξ | t < (ghostDeviation E X n ξ.1 ξ.2).toReal} ≤
        ∫⁻ ξ, conditionalRademacherTail E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) t ∂ρ := by
    have hbadMeas : MeasurableSet (ghostBad E X n t) := by
      rw [← hghostSet t ht]
      exact measurableSet_lt measurable_const hghostMeas.ennreal_toReal
    calc
      ρ {ξ : Ξ × Ξ | t < (ghostDeviation E X n ξ.1 ξ.2).toReal} =
          ρ (ghostBad E X n t) := congrArg ρ (hghostSet t ht)
      _ = ρ.outerMeasureStar (ghostBad E X n t) :=
        (outerMeasureStar_eq_measure hbadMeas).symm
      _ ≤ outerExpectation ρ (fun ξ => conditionalRademacherTail E n
          (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) t) :=
        ghostSwap_rademacher_outer_le μ E X n t hEmeas hPM hXmeas hXiindep
      _ = ∫⁻ ξ, conditionalRademacherTail E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) t ∂ρ :=
        outerExpectation_eq_lintegral (htailMeas t)
  have hinner (ξ : Ξ × Ξ) :
      outerExpectation ν (fun σ => signedGhostDeviation E n
          (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ) =
        ∫⁻ t in Set.Ioi (0 : ℝ), conditionalRademacherTail E n
          (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) t ∂volume := by
    rw [outerExpectation_eq_lintegral (measurable_of_finite _)]
    exact lintegral_signedGhostDeviation_eq_tail E _ _ (hsignedfinite ξ)
  have hrightMeas : Measurable (fun ξ : Ξ × Ξ =>
      ∫⁻ t in Set.Ioi (0 : ℝ), conditionalRademacherTail E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) t ∂volume) :=
    htailJoint.lintegral_prod_right'
  rw [outerExpectation_eq_lintegral hghostMeas]
  calc
    ∫⁻ ξ, ghostDeviation E X n ξ.1 ξ.2 ∂ρ =
        ∫⁻ ξ, ENNReal.ofReal (ghostDeviation E X n ξ.1 ξ.2).toReal ∂ρ := by
      apply lintegral_congr
      intro ξ
      exact (ENNReal.ofReal_toReal (hghostfinite ξ)).symm
    _ = ∫⁻ t in Set.Ioi (0 : ℝ),
          ρ {ξ : Ξ × Ξ | t < (ghostDeviation E X n ξ.1 ξ.2).toReal} ∂volume :=
      lintegral_eq_lintegral_meas_lt ρ
        (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        hghostMeas.ennreal_toReal.aemeasurable
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ ξ,
          conditionalRademacherTail E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) t ∂ρ ∂volume :=
      setLIntegral_mono' measurableSet_Ioi fun t ht => htailBound t ht
    _ = ∫⁻ ξ, ∫⁻ t in Set.Ioi (0 : ℝ),
          conditionalRademacherTail E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) t ∂volume ∂ρ := by
      exact lintegral_lintegral_swap
        ((htailJoint.comp measurable_swap).aemeasurable)
    _ = outerExpectation ρ (fun ξ => outerExpectation ν (fun σ =>
          signedGhostDeviation E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) σ)) := by
      rw [show (fun ξ : Ξ × Ξ => outerExpectation ν (fun σ =>
          signedGhostDeviation E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) σ)) = fun ξ =>
          ∫⁻ t in Set.Ioi (0 : ℝ), conditionalRademacherTail E n
            (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) t ∂volume by
        funext ξ
        exact hinner ξ]
      exact (outerExpectation_eq_lintegral hrightMeas).symm

/-- The layer-cake symmetrization remains valid after the deterministic
empirical-process scaling. -/
private theorem outerExpectation_scaled_ghostDeviation_le_signed
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (E : Set (Ω → ℝ)) (X : ℕ → Ξ → Ω) (n : ℕ)
    (hEcount : E.Countable) (hEmeas : ∀ f ∈ E, Measurable f)
    (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hghostfinite : ∀ ξ : Ξ × Ξ, ghostDeviation E X n ξ.1 ξ.2 ≠ ⊤)
    (hsignedfinite : ∀ (ξ : Ξ × Ξ) (σ : Fin n → Bool),
      signedGhostDeviation E n (fun i => X i.val ξ.1)
        (fun i => X i.val ξ.2) σ ≠ ⊤) :
    outerExpectation (μ.prod μ) (fun ξ => ENNReal.ofReal (Real.sqrt n) *
        ghostDeviation E X n ξ.1 ξ.2) ≤
      outerExpectation (μ.prod μ) (fun ξ =>
        outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (fun σ => ENNReal.ofReal (Real.sqrt n) *
            signedGhostDeviation E n (fun i => X i.val ξ.1)
              (fun i => X i.val ξ.2) σ)) := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt n)
  let ν := (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  have hc : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnode := outerExpectation_ghostDeviation_le_signed
    μ E X n hEcount hEmeas hXmeas hXiindep hghostfinite hsignedfinite
  have hleft : outerExpectation (μ.prod μ) (fun ξ =>
      c * ghostDeviation E X n ξ.1 ξ.2) =
      c * outerExpectation (μ.prod μ) (fun ξ =>
        ghostDeviation E X n ξ.1 ξ.2) := by
    rw [show (fun ξ : Ξ × Ξ => c * ghostDeviation E X n ξ.1 ξ.2) =
        c • (fun ξ => ghostDeviation E X n ξ.1 ξ.2) by
      funext ξ; simp [Pi.smul_apply, smul_eq_mul],
      outerExpectation_const_smul c hc, smul_eq_mul]
  have hinner (ξ : Ξ × Ξ) : outerExpectation ν (fun σ => c *
      signedGhostDeviation E n (fun i => X i.val ξ.1)
        (fun i => X i.val ξ.2) σ) =
      c * outerExpectation ν (fun σ =>
        signedGhostDeviation E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) σ) := by
    rw [show (fun σ => c * signedGhostDeviation E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ) =
        c • (fun σ => signedGhostDeviation E n
          (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ) by
      funext σ; simp [Pi.smul_apply, smul_eq_mul],
      outerExpectation_const_smul c hc, smul_eq_mul]
  rw [hleft]
  calc
    c * outerExpectation (μ.prod μ) (fun ξ =>
        ghostDeviation E X n ξ.1 ξ.2) ≤
        c * outerExpectation (μ.prod μ) (fun ξ =>
          outerExpectation ν (fun σ => signedGhostDeviation E n
            (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ)) :=
      mul_le_mul_right hnode c
    _ = outerExpectation (μ.prod μ) (fun ξ => c *
          outerExpectation ν (fun σ => signedGhostDeviation E n
            (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ)) := by
      rw [show (fun ξ : Ξ × Ξ => c * outerExpectation ν (fun σ =>
          signedGhostDeviation E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) σ)) =
          c • (fun ξ => outerExpectation ν (fun σ =>
            signedGhostDeviation E n (fun i => X i.val ξ.1)
              (fun i => X i.val ξ.2) σ)) by
        funext ξ; simp [Pi.smul_apply, smul_eq_mul],
        outerExpectation_const_smul c hc, smul_eq_mul]
    _ = outerExpectation (μ.prod μ) (fun ξ => outerExpectation ν (fun σ =>
          c * signedGhostDeviation E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) σ)) := by
      congr 1
      funext ξ
      exact (hinner ξ).symm

private theorem measurable_conditionalScaledSignedExpectation_countable
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ))
    (X : ℕ → Ξ → Ω) (n : ℕ) (hEcount : E.Countable)
    (hEmeas : ∀ f ∈ E, Measurable f) (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (fun ξ : Ξ × Ξ =>
      outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal (Real.sqrt n) *
          signedGhostDeviation E n (fun i => X i.val ξ.1)
            (fun i => X i.val ξ.2) σ)) := by
  let ν := (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  have heq (ξ : Ξ × Ξ) : outerExpectation ν (fun σ =>
      ENNReal.ofReal (Real.sqrt n) * signedGhostDeviation E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ) =
      ∑ σ : Fin n → Bool, (ENNReal.ofReal (Real.sqrt n) *
        signedGhostDeviation E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) σ) * ν {σ} := by
    rw [outerExpectation_eq_lintegral (measurable_of_finite _), lintegral_fintype]
  rw [show (fun ξ : Ξ × Ξ => outerExpectation ν (fun σ =>
      ENNReal.ofReal (Real.sqrt n) * signedGhostDeviation E n
        (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ)) =
      fun ξ => ∑ σ : Fin n → Bool, (ENNReal.ofReal (Real.sqrt n) *
        signedGhostDeviation E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) σ) * ν {σ} by
    funext ξ; exact heq ξ]
  exact Finset.measurable_sum _ fun σ _ =>
    (measurable_const.mul (measurable_signedGhostDeviation_countable
      E X n σ hEcount hEmeas hXmeas)).mul measurable_const

private theorem integral_empiricalAvg_eq
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) (X : ℕ → Ξ → Ω) (h : Ω → ℝ)
    (hhint : Integrable h P)
    (hXmeas : ∀ i, Measurable (X i)) (hXlaw : ∀ i, μ.map (X i) = P)
    (n : ℕ) (hn : n ≠ 0) :
    ∫ ξ, empiricalAvg h n (fun i : Fin n => X i.val ξ) ∂μ = ∫ x, h x ∂P := by
  have hhXint (i : Fin n) : Integrable (fun ξ => h (X i.val ξ)) μ := by
    have hm : AEStronglyMeasurable h (μ.map (X i.val)) := by
      rw [hXlaw i.val]
      exact hhint.aestronglyMeasurable
    exact (integrable_map_measure hm (hXmeas i.val).aemeasurable).mp (by
      rw [hXlaw i.val]
      exact hhint)
  have hhXintegral (i : Fin n) : ∫ ξ, h (X i.val ξ) ∂μ = ∫ x, h x ∂P := by
    rw [← hXlaw i.val]
    exact (integral_map (hXmeas i.val).aemeasurable
      (by rw [hXlaw i.val]; exact hhint.aestronglyMeasurable)).symm
  unfold empiricalAvg
  rw [integral_const_mul]
  rw [integral_finset_sum]
  · simp_rw [hhXintegral]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  · intro i _
    exact hhXint i

private theorem measurable_skeletonLocalProcessModulus
    {Ξ : Type*} [MeasurableSpace Ξ] {F₀ : Set (Ω → ℝ)}
    (hF₀count : F₀.Countable) (hF₀meas : ∀ f ∈ F₀, Measurable f)
    (P : Measure Ω) (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (n : ℕ) (δ : ℝ) :
    Measurable (skeletonLocalProcessModulus F₀ P X n δ) := by
  let E := skeletonLocalDifferenceClass F₀ P δ
  have hEcount : E.Countable := skeletonLocalDifferenceClass_countable hF₀count P δ
  letI : Countable E := hEcount
  change Measurable (fun ξ => supNormOver (skeletonLocalDifferenceClass F₀ P δ)
    (empiricalProcess P n (fun i : Fin n => X i.val ξ)))
  rw [show (fun ξ => supNormOver (skeletonLocalDifferenceClass F₀ P δ)
      (empiricalProcess P n (fun i : Fin n => X i.val ξ))) =
      fun ξ => ⨆ h : skeletonLocalDifferenceClass F₀ P δ,
        ENNReal.ofReal |empiricalProcess P n
          (fun i : Fin n => X i.val ξ) h.1| by
    funext ξ
    exact supNormOver_eq_iSup_subtype_chaining _ _]
  apply Measurable.iSup
  intro h
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  unfold empiricalProcess empiricalAvg
  apply Measurable.const_mul
  apply Measurable.sub
  · apply Measurable.const_mul
    exact Finset.measurable_sum _ fun i _ =>
      (skeletonLocalDifferenceClass_measurable hF₀meas P δ h h.property).comp
        (hXmeas i.val)
  · exact measurable_const

/-- Jensen's ghost-sample step for the measurable local skeleton. -/
private theorem outerExpectation_skeletonLocalProcessModulus_le_ghost
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (F F₀ : Set (Ω → ℝ)) (H : Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ξ → Ω)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    (hF₀count : F₀.Countable) (hF₀sub : F₀ ⊆ F)
    (hXmeas : ∀ i, Measurable (X i)) (hXlaw : ∀ i, μ.map (X i) = P)
    (n : ℕ) (hn : n ≠ 0) (δ : ℝ) :
    outerExpectation μ (skeletonLocalProcessModulus F₀ P X n δ) ≤
      outerExpectation (μ.prod μ) (fun ξ => ENNReal.ofReal (Real.sqrt n) *
        ghostDeviation (skeletonLocalDifferenceClass F₀ P δ) X n ξ.1 ξ.2) := by
  let E := skeletonLocalDifferenceClass F₀ P δ
  have hF₀meas : ∀ f ∈ F₀, Measurable f := fun f hf => hFmeas f (hF₀sub hf)
  have hEcount : E.Countable := skeletonLocalDifferenceClass_countable hF₀count P δ
  have hEmeas : ∀ h ∈ E, Measurable h :=
    skeletonLocalDifferenceClass_measurable hF₀meas P δ
  have hmodMeas : Measurable (skeletonLocalProcessModulus F₀ P X n δ) :=
    measurable_skeletonLocalProcessModulus hF₀count hF₀meas P X hXmeas n δ
  have hghostMeas : Measurable (fun ξ : Ξ × Ξ =>
      ENNReal.ofReal (Real.sqrt n) * ghostDeviation E X n ξ.1 ξ.2) :=
    measurable_const.mul
      (measurable_ghostDeviation_countable E X n hEcount hEmeas hXmeas)
  have hpoint (ξ : Ξ) : skeletonLocalProcessModulus F₀ P X n δ ξ ≤
      ∫⁻ ξ', ENNReal.ofReal (Real.sqrt n) * ghostDeviation E X n ξ ξ' ∂μ := by
    unfold skeletonLocalProcessModulus
    rw [supNormOver_eq_iSup_subtype_chaining]
    apply iSup_le
    intro h
    have hhmem : h.1 ∈ E := h.property
    have hhmem' := hhmem
    obtain ⟨f, hf, g, hg, -, hhfg⟩ := hhmem
    have hfLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp (hF₀sub hf)
    have hgLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp (hF₀sub hg)
    have hhLp : MemLp h.1 2 P := by simpa only [hhfg] using hfLp.sub hgLp
    have hhInt : Integrable h.1 P := memLp_one_iff_integrable.mp
      (hhLp.mono_exponent (by norm_num))
    have hAvgInt : Integrable (fun ξ' =>
        empiricalAvg h.1 n (fun i : Fin n => X i.val ξ')) μ := by
      unfold empiricalAvg
      apply Integrable.const_mul
      apply integrable_finset_sum
      intro i _
      have hm : AEStronglyMeasurable h.1 (μ.map (X i.val)) := by
        rw [hXlaw i.val]
        exact hhInt.aestronglyMeasurable
      exact (integrable_map_measure hm (hXmeas i.val).aemeasurable).mp (by
        rw [hXlaw i.val]
        exact hhInt)
    have hrepr : empiricalProcess P n (fun i : Fin n => X i.val ξ) h.1 =
        ∫ ξ', Real.sqrt n *
          (empiricalAvg h.1 n (fun i : Fin n => X i.val ξ) -
            empiricalAvg h.1 n (fun i : Fin n => X i.val ξ')) ∂μ := by
      rw [integral_const_mul]
      rw [integral_sub (integrable_const _) hAvgInt]
      rw [integral_const]
      norm_num
      rw [integral_empiricalAvg_eq μ P X h.1 hhInt
        hXmeas hXlaw n hn]
      rfl
    have hjensen : ENNReal.ofReal
        |empiricalProcess P n (fun i : Fin n => X i.val ξ) h.1| ≤
        ∫⁻ ξ', ENNReal.ofReal (Real.sqrt n) * ghostDeviation E X n ξ ξ' ∂μ := by
      have hjreal : |empiricalProcess P n (fun i : Fin n => X i.val ξ) h.1| ≤
          (∫⁻ ξ', ENNReal.ofReal |Real.sqrt n *
            (empiricalAvg h.1 n (fun i : Fin n => X i.val ξ) -
              empiricalAvg h.1 n (fun i : Fin n => X i.val ξ'))| ∂μ).toReal := by
        rw [hrepr]
        have hh := norm_integral_le_lintegral_norm (μ := μ) (fun ξ' =>
          Real.sqrt n * (empiricalAvg h.1 n (fun i : Fin n => X i.val ξ) -
            empiricalAvg h.1 n (fun i : Fin n => X i.val ξ')))
        simpa [Real.norm_eq_abs, Real.enorm_eq_ofReal_abs] using hh
      refine (ENNReal.ofReal_le_ofReal hjreal).trans ?_
      refine ENNReal.ofReal_toReal_le.trans ?_
      apply lintegral_mono
      intro ξ'
      change ENNReal.ofReal |Real.sqrt n *
          (empiricalAvg h.1 n (fun i : Fin n => X i.val ξ) -
            empiricalAvg h.1 n (fun i : Fin n => X i.val ξ'))| ≤
        ENNReal.ofReal (Real.sqrt n) * ghostDeviation E X n ξ ξ'
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      gcongr
      exact le_supNormOver hhmem'
    exact hjensen
  rw [outerExpectation_eq_lintegral hmodMeas,
    outerExpectation_eq_lintegral hghostMeas]
  calc
    ∫⁻ ξ, skeletonLocalProcessModulus F₀ P X n δ ξ ∂μ ≤
        ∫⁻ ξ, ∫⁻ ξ', ENNReal.ofReal (Real.sqrt n) *
          ghostDeviation E X n ξ ξ' ∂μ ∂μ := lintegral_mono hpoint
    _ = ∫⁻ ξ, ENNReal.ofReal (Real.sqrt n) *
          ghostDeviation E X n ξ.1 ξ.2 ∂(μ.prod μ) :=
      (lintegral_prod _ hghostMeas.aemeasurable).symm

private theorem scaled_signedGhostDeviation_le_localOscillations
    {F F₀ : Set (Ω → ℝ)} (hF₀sub : F₀ ⊆ F) (P : Measure Ω) (δ r r' : ℝ)
    {n : ℕ} (hn : n ≠ 0) (z z' : Fin n → Ω) (σ : Fin n → Bool)
    (hz : ∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g < δ →
      sampleL2Seminorm z (f - g) < r)
    (hz' : ∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g < δ →
      sampleL2Seminorm z' (f - g) < r') :
    ENNReal.ofReal (Real.sqrt n) *
        signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ) n z z' σ ≤
      conditionalRademacherLocalOscillation F z r σ +
        conditionalRademacherLocalOscillation F z' r' σ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hscale : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
    field_simp [ne_of_gt hsqrtpos, ne_of_gt hnpos]
    rw [Real.sq_sqrt hnpos.le]
  unfold signedGhostDeviation supNormOver
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro h
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro hh
  obtain ⟨f, hf, g, hg, hfg, hhdef⟩ := hh
  let s : Fin n → ℝ := fun i => if σ i then 1 else -1
  have hsum : ∑ i, s i * (h (z i) - h (z' i)) =
      (∑ i, s i * f (z i)) - (∑ i, s i * g (z i)) -
        ((∑ i, s i * f (z' i)) - (∑ i, s i * g (z' i))) := by
    calc
      ∑ i, s i * (h (z i) - h (z' i)) =
          ∑ i, (s i * h (z i) - s i * h (z' i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, s i * h (z i)) - (∑ i, s i * h (z' i)) := by
        simpa only using (Finset.sum_sub_distrib
          (s := Finset.univ) (fun i => s i * h (z i))
            (fun i => s i * h (z' i)))
      _ = _ := by
        subst h
        simp only [Pi.sub_apply]
        rw [show (∑ i, s i * (f (z i) - g (z i))) =
            (∑ i, s i * f (z i)) - (∑ i, s i * g (z i)) by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring]
        rw [show (∑ i, s i * (f (z' i) - g (z' i))) =
            (∑ i, s i * f (z' i)) - (∑ i, s i * g (z' i)) by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring]
  have hraw : Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i,
        (if σ i then (1 : ℝ) else -1) * (h (z i) - h (z' i))) =
      (conditionalRademacherIncrement z σ f -
          conditionalRademacherIncrement z σ g) -
        (conditionalRademacherIncrement z' σ f -
          conditionalRademacherIncrement z' σ g) := by
    simp only [conditionalRademacherIncrement, s] at hsum ⊢
    rw [← mul_assoc, hscale, hsum]
    ring
  have hzclose : sampleL2Seminorm z (f - g) < r := hz f hf g hg hfg
  have hz'close : sampleL2Seminorm z' (f - g) < r' := hz' f hf g hg hfg
  have hzle : ENNReal.ofReal |conditionalRademacherIncrement z σ f -
      conditionalRademacherIncrement z σ g| ≤
      conditionalRademacherLocalOscillation F z r σ := by
    exact le_iSup_of_le (⟨f, hF₀sub hf⟩ : ↥F)
      (le_iSup_of_le (⟨g, hF₀sub hg⟩ : ↥F) (by rw [if_pos hzclose]))
  have hz'le : ENNReal.ofReal |conditionalRademacherIncrement z' σ f -
      conditionalRademacherIncrement z' σ g| ≤
      conditionalRademacherLocalOscillation F z' r' σ := by
    exact le_iSup_of_le (⟨f, hF₀sub hf⟩ : ↥F)
      (le_iSup_of_le (⟨g, hF₀sub hg⟩ : ↥F) (by rw [if_pos hz'close]))
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  have habs : Real.sqrt n * |(n : ℝ)⁻¹ * ∑ i,
      (if σ i then (1 : ℝ) else -1) * (h (z i) - h (z' i))| =
      |Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i,
        (if σ i then (1 : ℝ) else -1) * (h (z i) - h (z' i)))| := by
    simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [habs, hraw]
  exact (ENNReal.ofReal_le_ofReal (abs_sub _ _)).trans
    (ENNReal.ofReal_add_le.trans (add_le_add hzle hz'le))

private def fourEnvelope (G : Ω → ℝ) : Ω → ℝ := fun x => 4 * G x

private theorem outerLpNorm_fourEnvelope (Q : Measure Ω) (G : Ω → ℝ) :
    outerLpNorm Q (fourEnvelope G) 2 = 4 * outerLpNorm Q G 2 := by
  have hfun : (fun x => ENNReal.ofReal |fourEnvelope G x| ^ (2 : ℝ)) =
      fun x => 16 * ENNReal.ofReal |G x| ^ (2 : ℝ) := by
    funext x
    simp only [fourEnvelope, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  unfold outerLpNorm
  rw [hfun, show (fun x => 16 * ENNReal.ofReal |G x| ^ (2 : ℝ)) =
      (16 : ℝ≥0∞) • (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) by
        funext x
        simp [Pi.smul_apply, smul_eq_mul],
    outerExpectation_const_smul 16 (by norm_num), smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
  have hsqrt16 : (16 : ℝ≥0∞) ^ (2 : ℝ)⁻¹ = 4 := by
    apply ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0)
    change ((16 : ℝ≥0∞) ^ (2 : ℝ)⁻¹) ^ (2 : ℝ) =
      (4 : ℝ≥0∞) ^ (2 : ℝ)
    rw [← ENNReal.rpow_mul]
    norm_num [ENNReal.rpow_natCast]
  rw [hsqrt16]

private def admissibleFourEnvelopeToBase {G : Ω → ℝ} {Q : Measure Ω}
    (hQ : IsAdmissibleMeasure (fourEnvelope G) 2 Q) :
    IsAdmissibleMeasure G 2 Q := by
  unfold IsAdmissibleMeasure at hQ ⊢
  rw [outerLpNorm_fourEnvelope] at hQ
  refine ⟨hQ.1, ?_, ?_⟩
  · exact (ENNReal.mul_pos_iff.mp hQ.2.1).2
  · exact (le_mul_of_one_le_left (zero_le) (by norm_num)).trans_lt hQ.2.2

private theorem uniformLpCoveringNumber_fourEnvelope_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ} (ε : ℝ) :
    uniformLpCoveringNumber F (fourEnvelope G) 2 ε ≤
      uniformLpCoveringNumber F G 2 ε := by
  unfold uniformLpCoveringNumber
  refine iSup_le fun Q => iSup_le fun hQ₄ => ?_
  have hfinite : finiteLpCoveringNumber F (fourEnvelope G) Q 2 ε ≤
      finiteLpCoveringNumber F G Q 2 ε := by
    unfold finiteLpCoveringNumber
    refine le_iInf fun T => le_iInf fun hT => ?_
    refine iInf_le_of_le T (iInf_le_of_le ?_ le_rfl)
    refine ⟨hT.1, ?_⟩
    intro f hf
    obtain ⟨g, hg, hfg⟩ := hT.2 f hf
    refine ⟨g, hg, hfg.trans_le ?_⟩
    rw [outerLpNorm_fourEnvelope]
    gcongr
    exact le_mul_of_one_le_left (zero_le) (by norm_num)
  exact hfinite.trans
    (le_iSup_of_le Q (le_iSup_of_le (admissibleFourEnvelopeToBase hQ₄) le_rfl))

/-- The unrestricted conditional oscillation, used only as an integrable
fallback on the exceptional square-GC event. -/
private noncomputable def conditionalRademacherGlobalOscillation
    (F : Set (Ω → ℝ)) {n : ℕ} (z : Fin n → Ω) (σ : Fin n → Bool) : ℝ≥0∞ :=
  ⨆ (f : ↥F), ⨆ (g : ↥F), ENNReal.ofReal
    |conditionalRademacherIncrement z σ (f : Ω → ℝ) -
      conditionalRademacherIncrement z σ (g : Ω → ℝ)|

omit [MeasurableSpace Ω] in
private theorem conditionalRademacherLocalOscillation_le_global
    (F : Set (Ω → ℝ)) {n : ℕ} (z : Fin n → Ω) (r : ℝ) (σ : Fin n → Bool) :
    conditionalRademacherLocalOscillation F z r σ ≤
      conditionalRademacherGlobalOscillation F z σ := by
  unfold conditionalRademacherLocalOscillation conditionalRademacherGlobalOscillation
  apply iSup_mono
  intro f
  apply iSup_mono
  intro g
  split_ifs
  · exact le_rfl
  · exact bot_le

private theorem conditionalRademacherGlobalOscillation_le_four_local
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hfinite : outerLpNorm (empiricalMeasure n z) G 2 < ⊤)
    (hpos : 0 < outerLpNorm (empiricalMeasure n z) G 2)
    (σ : Fin n → Bool) :
    conditionalRademacherGlobalOscillation F z σ ≤
      conditionalRademacherLocalOscillation F z
        ((outerLpNorm (empiricalMeasure n z) (fourEnvelope G) 2).toReal) σ := by
  let L := outerLpNorm (empiricalMeasure n z) G 2
  have hLreal : (outerLpNorm (empiricalMeasure n z) (fourEnvelope G) 2).toReal =
      4 * L.toReal := by
    rw [outerLpNorm_fourEnvelope, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  have hsampleG : sampleL2Seminorm z G ≤ L.toReal :=
    sampleL2Seminorm_le_outerLpNorm_toReal hn z G hfinite
  have hLrealpos : 0 < L.toReal := ENNReal.toReal_pos hpos.ne' hfinite.ne
  unfold conditionalRademacherGlobalOscillation conditionalRademacherLocalOscillation
  apply iSup_mono
  intro f
  apply iSup_mono
  intro g
  rw [if_pos]
  rw [hLreal]
  calc
    sampleL2Seminorm z ((f : Ω → ℝ) - (g : Ω → ℝ)) ≤
        2 * sampleL2Seminorm z G :=
      sampleL2Seminorm_sub_le_two_envelope hEnv z f.property g.property
    _ ≤ 2 * L.toReal := by gcongr
    _ < 4 * L.toReal := by linarith

private theorem conditionalRademacherGlobalOscillation_eq_zero
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hzero : outerLpNorm (empiricalMeasure n z) G 2 = 0)
    (σ : Fin n → Bool) :
    conditionalRademacherGlobalOscillation F z σ = 0 := by
  have hfinite : outerLpNorm (empiricalMeasure n z) G 2 < ⊤ := hzero ▸ ENNReal.zero_lt_top
  have hsampleG : sampleL2Seminorm z G = 0 := by
    have hle := sampleL2Seminorm_le_outerLpNorm_toReal hn z G hfinite
    rw [hzero] at hle
    norm_num at hle
    exact le_antisymm hle (by unfold sampleL2Seminorm; positivity)
  apply le_antisymm
  · unfold conditionalRademacherGlobalOscillation
    apply iSup_le
    intro f
    apply iSup_le
    intro g
    apply le_of_eq
    apply ENNReal.ofReal_eq_zero.mpr
    have hbound := abs_conditionalRademacherIncrement_sub_le_sqrt_mul_sampleL2
      hn z σ (f : Ω → ℝ) (g : Ω → ℝ)
    have hsample := sampleL2Seminorm_sub_le_two_envelope
      hEnv z f.property g.property
    have hsamplezero : sampleL2Seminorm z ((f : Ω → ℝ) - (g : Ω → ℝ)) = 0 := by
      rw [hsampleG] at hsample
      exact le_antisymm (by simpa using hsample) (by unfold sampleL2Seminorm; positivity)
    have : |conditionalRademacherIncrement z σ (f : Ω → ℝ) -
        conditionalRademacherIncrement z σ (g : Ω → ℝ)| ≤ 0 :=
      hbound.trans (by rw [hsamplezero, mul_zero])
    exact this
  · exact bot_le

private theorem scaled_signedGhostDeviation_le_globalOscillations
    {F F₀ : Set (Ω → ℝ)} (hF₀sub : F₀ ⊆ F)
    {G : Ω → ℝ} (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (P : Measure Ω) (δ : ℝ) {n : ℕ} (hn : n ≠ 0)
    (z z' : Fin n → Ω)
    (hfinite : outerLpNorm (empiricalMeasure n z) G 2 < ⊤)
    (hfinite' : outerLpNorm (empiricalMeasure n z') G 2 < ⊤)
    (σ : Fin n → Bool) :
    ENNReal.ofReal (Real.sqrt n) *
        signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ) n z z' σ ≤
      conditionalRademacherGlobalOscillation F z σ +
        conditionalRademacherGlobalOscillation F z' σ := by
  let r := 4 * ((outerLpNorm (empiricalMeasure n z) G 2).toReal +
    (outerLpNorm (empiricalMeasure n z') G 2).toReal + 1)
  have hzall : ∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g < δ →
      sampleL2Seminorm z (f - g) < r := by
    intro f hf g hg _
    have hsampleG := sampleL2Seminorm_le_outerLpNorm_toReal hn z G hfinite
    calc
      sampleL2Seminorm z (f - g) ≤ 2 * sampleL2Seminorm z G :=
        sampleL2Seminorm_sub_le_two_envelope hEnv z (hF₀sub hf) (hF₀sub hg)
      _ ≤ 2 * (outerLpNorm (empiricalMeasure n z) G 2).toReal := by gcongr
      _ < r := by
        dsimp only [r]
        have hL0 : 0 ≤ (outerLpNorm (empiricalMeasure n z) G 2).toReal :=
          ENNReal.toReal_nonneg
        have hL0' : 0 ≤ (outerLpNorm (empiricalMeasure n z') G 2).toReal :=
          ENNReal.toReal_nonneg
        linarith
  have hz'all : ∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g < δ →
      sampleL2Seminorm z' (f - g) < r := by
    intro f hf g hg _
    have hsampleG := sampleL2Seminorm_le_outerLpNorm_toReal hn z' G hfinite'
    calc
      sampleL2Seminorm z' (f - g) ≤ 2 * sampleL2Seminorm z' G :=
        sampleL2Seminorm_sub_le_two_envelope hEnv z' (hF₀sub hf) (hF₀sub hg)
      _ ≤ 2 * (outerLpNorm (empiricalMeasure n z') G 2).toReal := by gcongr
      _ < r := by
        dsimp only [r]
        have hL0 : 0 ≤ (outerLpNorm (empiricalMeasure n z) G 2).toReal :=
          ENNReal.toReal_nonneg
        have hL0' : 0 ≤ (outerLpNorm (empiricalMeasure n z') G 2).toReal :=
          ENNReal.toReal_nonneg
        linarith
  exact (scaled_signedGhostDeviation_le_localOscillations
    hF₀sub P δ r r hn z z' σ hzall hz'all).trans
      (add_le_add (conditionalRademacherLocalOscillation_le_global F z r σ)
        (conditionalRademacherLocalOscillation_le_global F z' r σ))

private theorem eventuallyGood_indicator_lintegral_tendsto_zero
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (b : Ξ → ℝ≥0∞) (hbmeas : Measurable b) (hbint : ∫⁻ ξ, b ξ ∂μ ≠ ⊤)
    (Good : ℕ → Set Ξ) (hGoodMeas : ∀ n, MeasurableSet (Good n))
    (hGood : ∀ᵐ ξ ∂μ, ∀ᶠ n in atTop, ξ ∈ Good n) :
    Tendsto (fun n => ∫⁻ ξ, (Good n)ᶜ.indicator b ξ ∂μ) atTop (𝓝 0) := by
  have ht : Tendsto (fun n => ∫⁻ ξ, (Good n)ᶜ.indicator b ξ ∂μ) atTop
      (𝓝 (∫⁻ _ξ : Ξ, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (μ := μ) (l := atTop) (F := fun n ξ => (Good n)ᶜ.indicator b ξ)
      (f := fun _ => 0) b ?_ ?_ hbint ?_
    · exact Eventually.of_forall fun n => hbmeas.indicator (hGoodMeas n).compl
    · exact Eventually.of_forall fun n => Eventually.of_forall fun ξ => by
        by_cases hξ : ξ ∈ (Good n)ᶜ
        · change (Good n)ᶜ.indicator b ξ ≤ b ξ
          rw [Set.indicator_of_mem hξ]
        · change (Good n)ᶜ.indicator b ξ ≤ b ξ
          rw [Set.indicator_of_notMem hξ]
          exact bot_le
    · filter_upwards [hGood] with ξ hξ
      apply tendsto_const_nhds.congr'
      filter_upwards [hξ] with n hn
      simp [hn]
  simpa using ht

private theorem measurable_gcDeviation_chaining
    {Ξ : Type*} [MeasurableSpace Ξ] (E : Set (Ω → ℝ)) (H : Ω → ℝ)
    (P : Measure Ω)
    (X : ℕ → Ξ → Ω) (n : ℕ)
    (hEmeas : ∀ f ∈ E, Measurable f) (hPM : IsPointwiseMeasurable E)
    (hHenv : UniformEntropyStructural.IsEnvelope E H) (hHint : Integrable H P)
    (hXmeas : ∀ i, Measurable (X i)) :
    Measurable (gcDeviation E P X n) := by
  obtain ⟨E₀, hE₀count, hE₀sub, hE₀dense⟩ := hPM
  letI : Countable E₀ := hE₀count
  have heq (ξ : Ξ) : gcDeviation E P X n ξ =
      supNormOver E₀ (fun f => empiricalAvg f n
        (fun i : Fin n => X i.val ξ) - ∫ x, f x ∂P) := by
    unfold gcDeviation
    apply le_antisymm
    · unfold supNormOver
      apply iSup_le
      intro f
      apply iSup_le
      intro hf
      obtain ⟨g, hgmem, hglim⟩ := hE₀dense f hf
      have havg : Tendsto (fun m => empiricalAvg (g m) n
          (fun i : Fin n => X i.val ξ)) atTop
          (𝓝 (empiricalAvg f n (fun i : Fin n => X i.val ξ))) := by
        unfold empiricalAvg
        exact tendsto_const_nhds.mul
          (tendsto_finset_sum Finset.univ fun i _ => hglim (X i.val ξ))
      have hint : Tendsto (fun m => ∫ x, g m x ∂P) atTop (𝓝 (∫ x, f x ∂P)) := by
        apply tendsto_integral_of_dominated_convergence H
        · intro m
          exact (hEmeas (g m) (hE₀sub (hgmem m))).aestronglyMeasurable
        · exact hHint
        · intro m
          exact Eventually.of_forall fun x => by
            rw [Real.norm_eq_abs]
            exact hHenv.2 (g m) (hE₀sub (hgmem m)) x
        · exact Eventually.of_forall hglim
      have ht := (ENNReal.continuous_ofReal.tendsto _).comp
        ((continuous_abs.tendsto _).comp (havg.sub hint))
      refine le_of_tendsto ht ?_
      filter_upwards [] with m
      exact le_supNormOver (hgmem m)
    · unfold supNormOver
      apply iSup_le
      intro f
      apply iSup_le
      intro hf
      exact le_iSup_of_le f (le_iSup_of_le (hE₀sub hf) le_rfl)
  change Measurable (fun ξ => gcDeviation E P X n ξ)
  simp_rw [heq, supNormOver_eq_iSup_subtype_chaining]
  apply Measurable.iSup
  intro f
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.sub
  · unfold empiricalAvg
    apply Measurable.const_mul
    exact Finset.measurable_sum _ fun i _ =>
      (hEmeas f (hE₀sub f.property)).comp (hXmeas i.val)
  · exact measurable_const

private noncomputable def empiricalMajorantRMS {Ξ : Type*}
    (V : Ω → ℝ≥0∞) (X : ℕ → Ξ → Ω) (n : ℕ) (ξ : Ξ) : ℝ≥0∞ :=
  (((n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, V (X i.val ξ)) ^ (2 : ℝ)⁻¹)

private theorem measurable_empiricalMajorantRMS
    {Ξ : Type*} [MeasurableSpace Ξ] (V : Ω → ℝ≥0∞) (X : ℕ → Ξ → Ω)
    (hVmeas : Measurable V) (hXmeas : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (empiricalMajorantRMS V X n) := by
  unfold empiricalMajorantRMS
  fun_prop

private theorem outerLpNorm_empirical_le_majorantRMS
    {Ξ : Type*} (G : Ω → ℝ) (V : Ω → ℝ≥0∞) (X : ℕ → Ξ → Ω)
    (hVmeas : Measurable V)
    (hGV : ∀ x, ENNReal.ofReal |G x| ^ (2 : ℝ) ≤ V x)
    {n : ℕ} (ξ : Ξ) :
    outerLpNorm (empiricalMeasure n (fun i => X i.val ξ)) G 2 ≤
      empiricalMajorantRMS V X n ξ := by
  unfold outerLpNorm empiricalMajorantRMS
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc
    outerExpectation (empiricalMeasure n (fun i : Fin n => X i.val ξ))
        (fun x => ENNReal.ofReal |G x| ^ (2 : ℝ)) ≤
        outerExpectation (empiricalMeasure n (fun i : Fin n => X i.val ξ)) V :=
      outerExpectation_mono hGV
    _ = ∫⁻ x, V x ∂empiricalMeasure n (fun i : Fin n => X i.val ξ) :=
      outerExpectation_eq_lintegral hVmeas
    _ = (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, V (X i.val ξ) := by
      simp [empiricalMeasure, lintegral_smul_measure,
        lintegral_finset_sum_measure, lintegral_dirac' _ hVmeas, smul_eq_mul]

private theorem lintegral_empiricalMajorantRMS_sq
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) (V : Ω → ℝ≥0∞) (X : ℕ → Ξ → Ω)
    (hVmeas : Measurable V) (hXmeas : ∀ i, Measurable (X i))
    (hXlaw : ∀ i, μ.map (X i) = P) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ ξ, (empiricalMajorantRMS V X n ξ) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, V x ∂P := by
  have hnpos : (0 : ℝ≥0∞) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnzero : (n : ℝ≥0∞) ≠ 0 := hnpos.ne'
  have hnTop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hpow (ξ : Ξ) : (empiricalMajorantRMS V X n ξ) ^ (2 : ℝ) =
      (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, V (X i.val ξ) := by
    unfold empiricalMajorantRMS
    rw [← ENNReal.rpow_mul]
    norm_num
  have hmap (i : Fin n) : ∫⁻ ξ, V (X i.val ξ) ∂μ = ∫⁻ x, V x ∂P := by
    rw [← hXlaw i.val]
    exact (lintegral_map hVmeas (hXmeas i.val)).symm
  simp_rw [hpow]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hnzero)]
  rw [lintegral_finset_sum]
  · simp_rw [hmap]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, ENNReal.inv_mul_cancel hnzero hnTop, one_mul]
  · intro i _
    exact hVmeas.comp (hXmeas i.val)

private theorem lintegral_indicator_le_rpow_two_mul_measure
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (f : Ξ → ℝ≥0∞)
    (hf : Measurable f) (A : Set Ξ) (hA : MeasurableSet A) :
    ∫⁻ ξ, A.indicator f ξ ∂μ ≤
      (∫⁻ ξ, (f ξ) ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ *
        (μ A) ^ (2 : ℝ)⁻¹ := by
  let oneA : Ξ → ℝ≥0∞ := A.indicator 1
  have honeMeas : Measurable oneA := measurable_const.indicator hA
  have hpoint : A.indicator f = f * oneA := by
    funext ξ
    by_cases hξ : ξ ∈ A <;> simp [oneA, hξ]
  rw [hpoint]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    Real.HolderConjugate.two_two hf.aemeasurable honeMeas.aemeasurable
  have honepow : (fun ξ => oneA ξ ^ (2 : ℝ)) = oneA := by
    funext ξ
    by_cases hξ : ξ ∈ A <;> simp [oneA, hξ]
  calc
    ∫⁻ ξ, (f * oneA) ξ ∂μ ≤
        (∫⁻ ξ, f ξ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ ξ, oneA ξ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hholder
    _ = (∫⁻ ξ, f ξ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ *
          (μ A) ^ (2 : ℝ)⁻¹ := by
      rw [honepow, show oneA = A.indicator (fun _ => (1 : ℝ≥0∞)) by rfl,
        show ∫⁻ ξ, A.indicator (fun _ => (1 : ℝ≥0∞)) ξ ∂μ = μ A by
          exact lintegral_indicator_one hA]
      norm_num

private theorem lintegral_pair_empiricalMajorantRMS_sq_le
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) (V : Ω → ℝ≥0∞) (X : ℕ → Ξ → Ω)
    (hVmeas : Measurable V) (hXmeas : ∀ i, Measurable (X i))
    (hXlaw : ∀ i, μ.map (X i) = P) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ ξ : Ξ × Ξ, (empiricalMajorantRMS V X n ξ.1 +
        empiricalMajorantRMS V X n ξ.2) ^ (2 : ℝ) ∂(μ.prod μ) ≤
      8 * ∫⁻ x, V x ∂P := by
  let R := empiricalMajorantRMS V X n
  have hRmeas : Measurable R :=
    measurable_empiricalMajorantRMS V X hVmeas hXmeas n
  have hpoint (ξ : Ξ × Ξ) : (R ξ.1 + R ξ.2) ^ (2 : ℝ) ≤
      4 * R ξ.1 ^ (2 : ℝ) + 4 * R ξ.2 ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two]
    by_cases h : R ξ.1 ≤ R ξ.2
    · calc
        (R ξ.1 + R ξ.2) ^ 2 ≤ (2 * R ξ.2) ^ 2 :=
          pow_le_pow_left' ((add_le_add h le_rfl).trans_eq (by ring)) 2
        _ = 4 * R ξ.2 ^ 2 := by ring
        _ ≤ 4 * R ξ.1 ^ 2 + 4 * R ξ.2 ^ 2 := le_add_left le_rfl
    · have h' : R ξ.2 ≤ R ξ.1 := le_of_not_ge h
      calc
        (R ξ.1 + R ξ.2) ^ 2 ≤ (2 * R ξ.1) ^ 2 :=
          pow_le_pow_left' ((add_le_add le_rfl h').trans_eq (by ring)) 2
        _ = 4 * R ξ.1 ^ 2 := by ring
        _ ≤ 4 * R ξ.1 ^ 2 + 4 * R ξ.2 ^ 2 := le_add_right le_rfl
  calc
    ∫⁻ ξ : Ξ × Ξ, (R ξ.1 + R ξ.2) ^ (2 : ℝ) ∂(μ.prod μ) ≤
        ∫⁻ ξ : Ξ × Ξ, (4 * R ξ.1 ^ (2 : ℝ) +
          4 * R ξ.2 ^ (2 : ℝ)) ∂(μ.prod μ) := lintegral_mono hpoint
    _ = 4 * (∫⁻ ξ, R ξ ^ (2 : ℝ) ∂μ) +
          4 * (∫⁻ ξ, R ξ ^ (2 : ℝ) ∂μ) := by
      change ∫⁻ ξ : Ξ × Ξ, ((fun ξ => 4 * R ξ.1 ^ (2 : ℝ)) ξ +
        (fun ξ => 4 * R ξ.2 ^ (2 : ℝ)) ξ) ∂(μ.prod μ) = _
      rw [lintegral_add_left
        (f := fun ξ : Ξ × Ξ => 4 * R ξ.1 ^ (2 : ℝ))
        (measurable_const.mul ((hRmeas.comp measurable_fst).pow_const 2))]
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_const_mul' _ _ (by norm_num)]
      congr 1
      · rw [lintegral_prod]
        · simp
        · exact ((hRmeas.comp measurable_fst).pow_const 2).aemeasurable
      · rw [lintegral_prod]
        · simp
        · exact ((hRmeas.comp measurable_snd).pow_const 2).aemeasurable
    _ = 8 * ∫⁻ x, V x ∂P := by
      rw [lintegral_empiricalMajorantRMS_sq μ P V X hVmeas hXmeas hXlaw hn]
      ring

private theorem lintegral_empiricalMajorantRMS_le
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure Ω) (V : Ω → ℝ≥0∞) (X : ℕ → Ξ → Ω)
    (hVmeas : Measurable V) (hXmeas : ∀ i, Measurable (X i))
    (hXlaw : ∀ i, μ.map (X i) = P) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ ξ, empiricalMajorantRMS V X n ξ ∂μ ≤
      (∫⁻ x, V x ∂P) ^ (2 : ℝ)⁻¹ := by
  let R := empiricalMajorantRMS V X n
  have hRmeas : Measurable R :=
    measurable_empiricalMajorantRMS V X hVmeas hXmeas n
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq (f := R)
    (g := fun _ : Ξ => (1 : ℝ≥0∞)) μ Real.HolderConjugate.two_two hRmeas.aemeasurable
      (show AEMeasurable (fun _ : Ξ => (1 : ℝ≥0∞)) μ from measurable_const.aemeasurable)
  simp only [Pi.mul_apply, mul_one] at hholder
  calc
    ∫⁻ ξ, R ξ ∂μ ≤
        (∫⁻ ξ, R ξ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ _ξ : Ξ, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hholder
    _ = (∫⁻ x, V x ∂P) ^ (2 : ℝ)⁻¹ := by
      rw [lintegral_empiricalMajorantRMS_sq μ P V X hVmeas hXmeas hXlaw hn,
        lintegral_const, measure_univ]
      norm_num

omit [MeasurableSpace Ω] in
private theorem ofReal_mul_toReal_mul_eq
    {C b : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b) {L : ℝ≥0∞} (hL : L ≠ ⊤) :
    ENNReal.ofReal (C * L.toReal * b) = ENNReal.ofReal (C * b) * L := by
  rw [show C * L.toReal * b = (C * b) * L.toReal by ring,
    ENNReal.ofReal_mul (mul_nonneg hC hb), ENNReal.ofReal_toReal hL]

private theorem tendsto_empiricalProcess_of_pointwise_under_envelope
    {F : Set (Ω → ℝ)} {H : Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    {f : Ω → ℝ} {φ : ℕ → (Ω → ℝ)}
    (hφmem : ∀ m, φ m ∈ F)
    (hφlim : ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (n : ℕ) (Y : Fin n → Ω) :
    Tendsto (fun m => empiricalProcess P n Y (φ m)) atTop
      (𝓝 (empiricalProcess P n Y f)) := by
  have hHint : Integrable H P :=
    memLp_one_iff_integrable.mp (hHLp.mono_exponent (by norm_num))
  have hint : Tendsto (fun m => ∫ x, φ m x ∂P) atTop (𝓝 (∫ x, f x ∂P)) :=
    tendsto_integral_of_dominated_convergence H
      (fun m => (hFmeas _ (hφmem m)).aestronglyMeasurable) hHint
      (fun m => Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hHenv.2 _ (hφmem m) x)
      (Eventually.of_forall hφlim)
  have hsum : Tendsto (fun m => ∑ i, φ m (Y i)) atTop
      (𝓝 (∑ i, f (Y i))) :=
    tendsto_finset_sum Finset.univ fun i _ => hφlim (Y i)
  unfold empiricalProcess empiricalAvg
  exact tendsto_const_nhds.mul (tendsto_const_nhds.mul hsum |>.sub hint)

/-- Tail of the exact Dudley series attached to a schedule and admissible law.

Edge behavior: the tail from level `J` is expressed by an indicator inside
`tsum`; for an empty class all terms are zero. -/
noncomputable def dudleyScheduleTail {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (J : ℕ) : ℝ :=
  ∑' j : ℕ, if J ≤ j then
    (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (S.net Q hQ j).card)) else 0

private def natTailEquiv (J : ℕ) : ℕ ≃ {j : ℕ // J ≤ j} where
  toFun k := ⟨J + k, Nat.le_add_right J k⟩
  invFun j := j.1 - J
  left_inv k := by simp
  right_inv j := by ext; exact Nat.add_sub_of_le j.2

private theorem dudleyScheduleTail_eq_tsum_nat_add
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (J : ℕ) :
    dudleyScheduleTail S Q hQ J =
      ∑' k : ℕ, (1 / 2 : ℝ) ^ (J + k) *
        Real.sqrt (Real.log (2 * (S.net Q hQ (J + k)).card)) := by
  let a : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j *
    Real.sqrt (Real.log (2 * (S.net Q hQ j).card))
  calc
    dudleyScheduleTail S Q hQ J =
        ∑' j : ℕ, (Set.Ici J).indicator a j := by
      apply tsum_congr
      intro j
      by_cases hj : J ≤ j
      · rw [if_pos hj, Set.indicator_of_mem]
        exact hj
      · rw [if_neg hj, Set.indicator_of_notMem]
        exact hj
    _ = ∑' j : {j : ℕ // J ≤ j}, a j := (tsum_subtype (Set.Ici J) a).symm
    _ = ∑' k : ℕ, a (natTailEquiv J k) :=
      (Equiv.tsum_eq (natTailEquiv J)
        (fun j : {j : ℕ // J ≤ j} => a j.1)).symm
    _ = ∑' k : ℕ, (1 / 2 : ℝ) ^ (J + k) *
        Real.sqrt (Real.log (2 * (S.net Q hQ (J + k)).card)) := by rfl

private theorem dudleyScheduleTail_nonneg
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (J : ℕ) :
    0 ≤ dudleyScheduleTail S Q hQ J := by
  rw [dudleyScheduleTail_eq_tsum_nat_add]
  exact tsum_nonneg fun _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- A deterministic summable ledger dominating every law-indexed schedule
term.  The two summands respectively pay for nesting the nets and for the
uniform covering number. -/
private noncomputable def uniformDudleyLedgerTerm
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (j + 1))) +
    (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log
      (1 + (uniformLpCoveringNumber F G 2
        ((1 / 2 : ℝ) ^ (j + 1))).toNat))

private theorem uniformDudleyLedgerTerm_nonneg
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (j : ℕ) :
    0 ≤ uniformDudleyLedgerTerm F G j := by
  unfold uniformDudleyLedgerTerm
  positivity

private theorem uniformDudleyLedgerTerm_summable
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) :
    Summable (uniformDudleyLedgerTerm F G) := by
  let Nfun : ℕ → ℕ := fun j =>
    (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1))).toNat
  have hN_lt : ∀ j : ℕ,
      uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1)) < ⊤ :=
    fun j => uniformLpCoveringNumber_lt_top_of_uniformEntropy (by positivity) hJ
  have hN_eq : ∀ j : ℕ,
      uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1)) =
        (Nfun j : ℕ∞) :=
    fun j => (ENat.coe_toNat (hN_lt j).ne).symm
  have hsum1 : Summable (fun j : ℕ =>
      (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (j + 1)))) := by
    have hcmp : ∀ j : ℕ,
        (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (j + 1))) ≤
          (2 * ((j : ℝ) + 1)) * (1 / 2 : ℝ) ^ j := by
      intro j
      rw [mul_comm]
      gcongr
      have hx : (0 : ℝ) < 2 * ((j : ℝ) + 1) := by positivity
      have hlog : Real.log (2 * ((j : ℝ) + 1)) ≤
          2 * ((j : ℝ) + 1) := by
        nlinarith [Real.log_le_sub_one_of_pos hx]
      calc
        Real.sqrt (Real.log (2 * ((j : ℝ) + 1))) ≤
            Real.sqrt (2 * ((j : ℝ) + 1)) := Real.sqrt_le_sqrt hlog
        _ ≤ 2 * ((j : ℝ) + 1) := by
          nlinarith [Real.sq_sqrt hx.le,
            Real.sqrt_nonneg (2 * ((j : ℝ) + 1)),
            Real.one_le_sqrt.mpr (by
              have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
              linarith : (1 : ℝ) ≤ 2 * ((j : ℝ) + 1))]
    apply Summable.of_nonneg_of_le (fun _ => by positivity) hcmp
    have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
    have hlinear : Summable (fun j : ℕ =>
        ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) := by
      have h1 : Summable (fun j : ℕ => (j : ℝ) * (1 / 2 : ℝ) ^ j) :=
        (summable_pow_mul_geometric_of_norm_lt_one 1 hr).congr
          (fun j => by rw [pow_one])
      have h2 : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
        summable_geometric_of_norm_lt_one hr
      exact (h1.add h2).congr (fun j => by ring)
    exact (hlinear.mul_left 2).congr (fun j => by ring)
  have hsum2 : Summable (fun j : ℕ =>
      (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (1 + Nfun j))) := by
    let a : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal
      ((1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (1 + Nfun j)))
    have ha_eq : ∀ j : ℕ, a j = ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
        entropyWeight
          (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (j + 1))) := by
      intro j
      simp only [a]
      rw [hN_eq j, entropyWeight_coe,
        ← ENNReal.ofReal_mul (by positivity)]
    have hatsum_ne : (∑' j : ℕ, a j) ≠ ⊤ := by
      have hle : (∑' j : ℕ, a j) ≤
          2 * (2 * uniformEntropyIntegral 1 F G 2) := by
        calc
          (∑' j : ℕ, a j) =
              ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
                entropyWeight (uniformLpCoveringNumber F G 2
                  ((1 / 2 : ℝ) ^ (j + 1))) := tsum_congr ha_eq
          _ ≤ 2 * ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) *
                entropyWeight (uniformLpCoveringNumber F G 2
                  ((1 / 2 : ℝ) ^ j)) := uniformEntropy_shifted_dyadic_series_le
          _ ≤ 2 * (2 * uniformEntropyIntegral 1 F G 2) := by
            gcongr
            exact uniformEntropy_dyadic_sum_le_integral
      refine ne_top_of_le_ne_top ?_ hle
      exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top (by norm_num) hJ.ne)
    have hreal := ENNReal.summable_toReal hatsum_ne
    apply hreal.congr
    intro j
    simp only [a]
    rw [ENNReal.toReal_ofReal (by positivity)]
  exact (hsum1.add hsum2).congr fun j => by
    simp only [uniformDudleyLedgerTerm, Nfun]

private theorem dudleyScheduleTerm_le_uniformLedger
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ) :
    (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (S.net Q hQ j).card)) ≤
      uniformDudleyLedgerTerm F G j := by
  let Nfun : ℕ → ℕ := fun k =>
    (uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (k + 1))).toNat
  have hN_lt : ∀ k : ℕ,
      uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (k + 1)) < ⊤ :=
    fun k => uniformLpCoveringNumber_lt_top_of_uniformEntropy (by positivity) hJ
  have hN_eq : ∀ k : ℕ,
      uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (k + 1)) =
        (Nfun k : ℕ∞) :=
    fun k => (ENat.coe_toNat (hN_lt k).ne).symm
  have hN_antitone : ∀ {i k : ℕ}, i ≤ k → Nfun i ≤ Nfun k := by
    intro i k hik
    have hscale : (1 / 2 : ℝ) ^ (k + 1) ≤ (1 / 2 : ℝ) ^ (i + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hcover := uniformLpCoveringNumber_antitone_eps
      (F := F) (G := G) (r := 2) hscale
    rw [hN_eq i, hN_eq k] at hcover
    exact_mod_cast hcover
  have hcard : (S.net Q hQ j).card ≤ (j + 1) * Nfun j := by
    have hsum := S.card_le Q hQ j
    have hsum' : (∑ k ∈ Finset.range (j + 1),
        uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (k + 1))) ≤
        ((j + 1) * Nfun j : ℕ∞) := by
      calc
        (∑ k ∈ Finset.range (j + 1),
            uniformLpCoveringNumber F G 2 ((1 / 2 : ℝ) ^ (k + 1))) =
            ∑ k ∈ Finset.range (j + 1), (Nfun k : ℕ∞) := by
              apply Finset.sum_congr rfl
              intro k _
              exact hN_eq k
        _ ≤ ∑ _k ∈ Finset.range (j + 1), (Nfun j : ℕ∞) := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact_mod_cast hN_antitone
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        _ = ((j + 1) * Nfun j : ℕ∞) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_cast
    have : ((S.net Q hQ j).card : ℕ∞) ≤ ((j + 1) * Nfun j : ℕ∞) :=
      hsum.trans hsum'
    exact_mod_cast this
  have hNfun_nn : (0 : ℝ) ≤ (Nfun j : ℝ) := Nat.cast_nonneg _
  have hN_ge_one : (1 : ℝ) ≤ 1 + (Nfun j : ℝ) := by linarith
  have hcard_le : (2 * (S.net Q hQ j).card : ℝ) ≤
      (2 * (j + 1)) * (1 + Nfun j) := by
    have hreal : ((S.net Q hQ j).card : ℝ) ≤
        (((j + 1) * Nfun j : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at hreal ⊢
    nlinarith [hreal, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hlog_le : Real.log (2 * (S.net Q hQ j).card) ≤
      Real.log (2 * (j + 1)) + Real.log (1 + Nfun j) := by
    rcases Nat.eq_zero_or_pos (S.net Q hQ j).card with hzero | hpos
    · rw [hzero]
      norm_num
      exact add_nonneg
        (Real.log_nonneg (by exact_mod_cast
          (show (1 : ℕ) ≤ 2 * (j + 1) by omega)))
        (Real.log_nonneg hN_ge_one)
    · have hp : (0 : ℝ) < 2 * (S.net Q hQ j).card :=
        mul_pos (by norm_num) (Nat.cast_pos.mpr hpos)
      calc
        Real.log (2 * (S.net Q hQ j).card) ≤
            Real.log ((2 * (j + 1)) * (1 + Nfun j)) :=
          Real.log_le_log hp hcard_le
        _ = _ := by rw [Real.log_mul (by positivity) (by positivity)]
  have ha : (0 : ℝ) ≤ Real.log (2 * (j + 1)) :=
    Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ 2 * (j + 1) by omega))
  have hb : (0 : ℝ) ≤ Real.log (1 + Nfun j) := Real.log_nonneg hN_ge_one
  have hsqrt : Real.sqrt (Real.log (2 * (S.net Q hQ j).card)) ≤
      Real.sqrt (Real.log (2 * (j + 1))) +
        Real.sqrt (Real.log (1 + Nfun j)) := by
    refine (Real.sqrt_le_sqrt hlog_le).trans ?_
    rw [show Real.sqrt (Real.log (2 * (j + 1))) +
          Real.sqrt (Real.log (1 + Nfun j)) =
        Real.sqrt ((Real.sqrt (Real.log (2 * (j + 1))) +
          Real.sqrt (Real.log (1 + Nfun j))) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      Real.sqrt_nonneg (Real.log (2 * (j + 1))),
      Real.sqrt_nonneg (Real.log (1 + Nfun j)),
      mul_nonneg (Real.sqrt_nonneg (Real.log (2 * (j + 1))))
        (Real.sqrt_nonneg (Real.log (1 + Nfun j)))]
  unfold uniformDudleyLedgerTerm
  change _ ≤ (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (2 * (j + 1))) +
    (1 / 2 : ℝ) ^ j * Real.sqrt (Real.log (1 + Nfun j))
  calc
    _ ≤ (1 / 2 : ℝ) ^ j *
        (Real.sqrt (Real.log (2 * (j + 1))) +
          Real.sqrt (Real.log (1 + Nfun j))) := by gcongr
    _ = _ := by ring

/-- Deterministic tail which dominates all schedule tails and tends to zero. -/
private noncomputable def uniformDudleyLedgerTail
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (J : ℕ) : ℝ :=
  ∑' k : ℕ, uniformDudleyLedgerTerm F G (J + k)

private theorem uniformDudleyLedgerTail_nonneg
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (J : ℕ) :
    0 ≤ uniformDudleyLedgerTail F G J := by
  exact tsum_nonneg fun k => uniformDudleyLedgerTerm_nonneg F G (J + k)

private theorem dudleyScheduleTail_le_uniformLedgerTail
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (J : ℕ) :
    dudleyScheduleTail S Q hQ J ≤ uniformDudleyLedgerTail F G J := by
  rw [dudleyScheduleTail_eq_tsum_nat_add]
  unfold uniformDudleyLedgerTail
  apply Summable.tsum_le_tsum
      (fun k => dudleyScheduleTerm_le_uniformLedger hJ S Q hQ (J + k))
  · exact (S.entropySummable Q hQ).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)
  · exact (uniformDudleyLedgerTerm_summable hJ).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)

private theorem uniformDudleyLedgerTail_tendsto_zero
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) :
    Tendsto (uniformDudleyLedgerTail F G) atTop (𝓝 0) := by
  let a := uniformDudleyLedgerTerm F G
  have ha : Summable a := uniformDudleyLedgerTerm_summable hJ
  have hpartial : Tendsto (fun J => ∑ k ∈ Finset.range J, a k) atTop
      (𝓝 (∑' k, a k)) := ha.hasSum.tendsto_sum_nat
  have hsub' : Tendsto (fun J => (∑' k, a k) - ∑ k ∈ Finset.range J, a k)
      atTop (𝓝 ((∑' k, a k) - ∑' k, a k)) :=
    tendsto_const_nhds.sub hpartial
  have hsub : Tendsto (fun J => (∑' k, a k) - ∑ k ∈ Finset.range J, a k)
      atTop (𝓝 0) := by simpa using hsub'
  apply hsub.congr'
  filter_upwards [] with J
  rw [show uniformDudleyLedgerTail F G J = ∑' k, a (k + J) by
    unfold uniformDudleyLedgerTail a
    apply tsum_congr
    intro k
    rw [Nat.add_comm]]
  linarith [ha.sum_add_tsum_nat_add J]

/-- A chosen representative from the law-indexed schedule. -/
private noncomputable def scheduleProj {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ) (f : ↥F) : ↥F :=
  Classical.choose (S.covers Q hQ j f)

private theorem scheduleProj_mem {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ) (f : ↥F) :
    scheduleProj S Q hQ j f ∈ S.net Q hQ j :=
  (Classical.choose_spec (S.covers Q hQ j f)).1

private theorem scheduleProj_outerLpNorm_lt {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) (Q : Measure Ω)
    (hQ : IsAdmissibleMeasure G 2 Q) (j : ℕ) (f : ↥F) :
    outerLpNorm Q ((f : Ω → ℝ) - scheduleProj S Q hQ j f) 2 <
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * outerLpNorm Q G 2 :=
  (Classical.choose_spec (S.covers Q hQ j f)).2

private theorem scheduleProj_sampleL2_lt
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z)) (j : ℕ) (f : ↥F) :
    sampleL2Seminorm z ((f : Ω → ℝ) - scheduleProj S (empiricalMeasure n z) hQ j f) <
      (1 / 2 : ℝ) ^ j * (outerLpNorm (empiricalMeasure n z) G 2).toReal := by
  let Q := empiricalMeasure n z
  let L := outerLpNorm Q G 2
  have hsample := sampleL2Seminorm_le_outerLpNorm_empirical hn z
    ((f : Ω → ℝ) - scheduleProj S Q hQ j f)
  have hcover := scheduleProj_outerLpNorm_lt S Q hQ j f
  have hLtop : L ≠ ⊤ := ne_of_lt hQ.2.2
  have hLpos : 0 < L.toReal := ENNReal.toReal_pos (ne_of_gt hQ.2.1) hLtop
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
  have hrhs : ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * L =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j * L.toReal) := by
    calc
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * L =
          ENNReal.ofReal ((1 / 2 : ℝ) ^ j) * ENNReal.ofReal L.toReal := by
        rw [ENNReal.ofReal_toReal hLtop]
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ j * L.toReal) :=
        (ENNReal.ofReal_mul hpow).symm
  have hof : ENNReal.ofReal (sampleL2Seminorm z
      ((f : Ω → ℝ) - scheduleProj S Q hQ j f)) <
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j * L.toReal) :=
    hsample.trans_lt (hrhs ▸ hcover)
  exact (ENNReal.ofReal_lt_ofReal_iff (mul_pos (by positivity) hLpos)).mp hof

omit [MeasurableSpace Ω] in
private theorem sampleL2Seminorm_sub_comm {n : ℕ} (z : Fin n → Ω)
    (f g : Ω → ℝ) :
    sampleL2Seminorm z (f - g) = sampleL2Seminorm z (g - f) := by
  unfold sampleL2Seminorm
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  rw [Pi.sub_apply, Pi.sub_apply, abs_sub_comm]

/-- All pairs in a finite class net whose empirical RMS distance is at most
`ρ`, coerced back to pairs of ambient functions. -/
private noncomputable def scheduleSamplePairs {F : Set (Ω → ℝ)}
    (T : Finset ↥F) {n : ℕ} (z : Fin n → Ω) (ρ : ℝ) :
    Finset ((Ω → ℝ) × (Ω → ℝ)) := by
  classical
  exact ((T.product T).filter fun p =>
    sampleL2Seminorm z ((p.1 : Ω → ℝ) - (p.2 : Ω → ℝ)) ≤ ρ).image
      (fun p => ((p.1 : Ω → ℝ), (p.2 : Ω → ℝ)))

omit [MeasurableSpace Ω] in
private theorem scheduleSamplePairs_card_le {F : Set (Ω → ℝ)}
    (T : Finset ↥F) {n : ℕ} (z : Fin n → Ω) (ρ : ℝ) :
    (scheduleSamplePairs T z ρ).card ≤ T.card ^ 2 := by
  classical
  calc
    (scheduleSamplePairs T z ρ).card ≤
        ((T.product T).filter fun p =>
          sampleL2Seminorm z ((p.1 : Ω → ℝ) - (p.2 : Ω → ℝ)) ≤ ρ).card :=
      by simpa [scheduleSamplePairs] using Finset.card_image_le
    _ ≤ (T.product T).card := Finset.card_filter_le _ _
    _ = T.card ^ 2 := by simp [pow_two]

omit [MeasurableSpace Ω] in
private theorem mem_scheduleSamplePairs {F : Set (Ω → ℝ)}
    (T : Finset ↥F) {n : ℕ} (z : Fin n → Ω) (ρ : ℝ) (f g : ↥F)
    (hf : f ∈ T) (hg : g ∈ T)
    (hfg : sampleL2Seminorm z ((f : Ω → ℝ) - (g : Ω → ℝ)) ≤ ρ) :
    ((f : Ω → ℝ), (g : Ω → ℝ)) ∈ scheduleSamplePairs T z ρ := by
  classical
  simp only [scheduleSamplePairs, Finset.mem_image]
  exact ⟨(f, g), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hf, hg⟩, hfg⟩, rfl⟩

omit [MeasurableSpace Ω] in
private theorem sqrt_log_scheduleSamplePairs_card_le {F : Set (Ω → ℝ)}
    (T : Finset ↥F) {n : ℕ} (z : Fin n → Ω) (ρ : ℝ)
    (hU : (scheduleSamplePairs T z ρ).Nonempty) :
    Real.sqrt (Real.log (2 * (scheduleSamplePairs T z ρ).card)) ≤
      2 * Real.sqrt (Real.log (2 * T.card)) := by
  have hUpos : 0 < (scheduleSamplePairs T z ρ).card := hU.card_pos
  have hTpos : 0 < T.card := by
    have hc := scheduleSamplePairs_card_le T z ρ
    by_contra h
    have hzero : T.card = 0 := Nat.eq_zero_of_not_pos h
    have hUzero : (scheduleSamplePairs T z ρ).card = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [hzero] using hc
    exact (Nat.ne_of_gt hUpos) hUzero
  have hcardR : ((scheduleSamplePairs T z ρ).card : ℝ) ≤ (T.card : ℝ) ^ 2 := by
    exact_mod_cast scheduleSamplePairs_card_le T z ρ
  have hargpos : (0 : ℝ) < 2 * (scheduleSamplePairs T z ρ).card := by positivity
  have hNpos : (0 : ℝ) < 2 * T.card := by positivity
  have hlog : Real.log (2 * (scheduleSamplePairs T z ρ).card) ≤
      2 * Real.log (2 * T.card) := by
    calc
      Real.log (2 * (scheduleSamplePairs T z ρ).card) ≤
          Real.log ((2 * T.card) ^ 2) := by
        apply Real.log_le_log hargpos
        nlinarith [hcardR]
      _ = 2 * Real.log (2 * T.card) := by rw [Real.log_pow]; norm_num
  have hlogN : 0 ≤ Real.log (2 * T.card) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ T.card := by exact_mod_cast hTpos
    linarith)
  calc
    Real.sqrt (Real.log (2 * (scheduleSamplePairs T z ρ).card)) ≤
        Real.sqrt (2 * Real.log (2 * T.card)) := Real.sqrt_le_sqrt hlog
    _ ≤ 2 * Real.sqrt (Real.log (2 * T.card)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [Real.sqrt_nonneg (Real.log (2 * T.card)),
        Real.sq_sqrt hlogN, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

omit [MeasurableSpace Ω] in
private theorem outerExpectation_scheduleSamplePairs_iSup_le
    {F : Set (Ω → ℝ)} (T : Finset ↥F) {n : ℕ} (z : Fin n → Ω)
    (ρ : ℝ) (hρ : 0 < ρ) (hU : (scheduleSamplePairs T z ρ).Nonempty) :
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal (⨆ p : ↥(scheduleSamplePairs T z ρ),
          |conditionalRademacherIncrement z σ p.1.1 -
            conditionalRademacherIncrement z σ p.1.2|)) ≤
      ENNReal.ofReal (2 * Real.sqrt 2 * ρ *
        Real.sqrt (Real.log (2 * T.card))) := by
  refine (outerExpectation_iSup_abs_increment_le z
    (scheduleSamplePairs T z ρ) hU ρ hρ fun p hp => ?_).trans ?_
  · simp only [scheduleSamplePairs, Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (Finset.mem_filter.mp hq).2
  · apply ENNReal.ofReal_le_ofReal
    have hsqrt := sqrt_log_scheduleSamplePairs_card_le T z ρ hU
    have hfac : 0 ≤ Real.sqrt 2 * ρ := mul_nonneg (Real.sqrt_nonneg _) hρ.le
    nlinarith

private theorem schedule_vertical_pair_mem
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z)) (j : ℕ) (f : ↥F) :
    let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
    let ρ := 2 * (1 / 2 : ℝ) ^ j * L
    ((scheduleProj S (empiricalMeasure n z) hQ j f : Ω → ℝ),
      (scheduleProj S (empiricalMeasure n z) hQ (j + 1) f : Ω → ℝ)) ∈
      scheduleSamplePairs (S.net (empiricalMeasure n z) hQ (j + 1)) z ρ := by
  dsimp only
  let Q := empiricalMeasure n z
  let L := (outerLpNorm Q G 2).toReal
  have h1 := scheduleProj_sampleL2_lt S hn z hQ j f
  have h2 := scheduleProj_sampleL2_lt S hn z hQ (j + 1) f
  have hhalf : (1 / 2 : ℝ) ^ (j + 1) * L ≤ (1 / 2 : ℝ) ^ j * L := by
    rw [pow_succ]
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
    have hL : 0 ≤ L := ENNReal.toReal_nonneg
    nlinarith
  have hdist : sampleL2Seminorm z
      ((scheduleProj S Q hQ j f : Ω → ℝ) -
        scheduleProj S Q hQ (j + 1) f) < 2 * (1 / 2 : ℝ) ^ j * L := by
    have hadd := sampleL2Seminorm_add_le z
      ((scheduleProj S Q hQ j f : Ω → ℝ) - f)
      ((f : Ω → ℝ) - scheduleProj S Q hQ (j + 1) f)
    have heq : ((scheduleProj S Q hQ j f : Ω → ℝ) - f) +
        ((f : Ω → ℝ) - scheduleProj S Q hQ (j + 1) f) =
        (scheduleProj S Q hQ j f : Ω → ℝ) -
          scheduleProj S Q hQ (j + 1) f := by
      ext x
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [heq] at hadd
    have h1' : sampleL2Seminorm z
        ((scheduleProj S Q hQ j f : Ω → ℝ) - f) < (1 / 2 : ℝ) ^ j * L := by
      rw [sampleL2Seminorm_sub_comm]
      exact h1
    linarith
  apply mem_scheduleSamplePairs
  · exact S.nested Q hQ j (scheduleProj_mem S Q hQ j f)
  · exact scheduleProj_mem S Q hQ (j + 1) f
  · exact hdist.le

private theorem schedule_horizontal_pair_mem
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z)) (J : ℕ) (f g : ↥F)
    (hfg : sampleL2Seminorm z ((f : Ω → ℝ) - g) <
      (1 / 2 : ℝ) ^ J * (outerLpNorm (empiricalMeasure n z) G 2).toReal) :
    let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
    let ρ := 3 * (1 / 2 : ℝ) ^ J * L
    ((scheduleProj S (empiricalMeasure n z) hQ J f : Ω → ℝ),
      (scheduleProj S (empiricalMeasure n z) hQ J g : Ω → ℝ)) ∈
      scheduleSamplePairs (S.net (empiricalMeasure n z) hQ J) z ρ := by
  dsimp only
  let Q := empiricalMeasure n z
  let L := (outerLpNorm Q G 2).toReal
  have hf := scheduleProj_sampleL2_lt S hn z hQ J f
  have hg := scheduleProj_sampleL2_lt S hn z hQ J g
  have hdist : sampleL2Seminorm z
      ((scheduleProj S Q hQ J f : Ω → ℝ) - scheduleProj S Q hQ J g) <
      3 * (1 / 2 : ℝ) ^ J * L := by
    let a : Ω → ℝ := (scheduleProj S Q hQ J f : Ω → ℝ) - f
    let b : Ω → ℝ := (f : Ω → ℝ) - g
    let c : Ω → ℝ := (g : Ω → ℝ) - scheduleProj S Q hQ J g
    have hab := sampleL2Seminorm_add_le z a b
    have habc := sampleL2Seminorm_add_le z (a + b) c
    have heq : a + b + c = (scheduleProj S Q hQ J f : Ω → ℝ) -
        scheduleProj S Q hQ J g := by
      ext x
      simp [a, b, c]
    rw [heq] at habc
    have hfa : sampleL2Seminorm z a < (1 / 2 : ℝ) ^ J * L := by
      rw [show a = (scheduleProj S Q hQ J f : Ω → ℝ) - f by rfl,
        sampleL2Seminorm_sub_comm]
      exact hf
    have hgc : sampleL2Seminorm z c < (1 / 2 : ℝ) ^ J * L := by
      exact hg
    linarith
  apply mem_scheduleSamplePairs
  · exact scheduleProj_mem S Q hQ J f
  · exact scheduleProj_mem S Q hQ J g
  · exact hdist.le

/-- The real maximum over the vertical links from level `j` to `j+1`. -/
private noncomputable def scheduleVerticalMaximum
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (j : ℕ) (σ : Fin n → Bool) : ℝ :=
  let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
  let ρ := 2 * (1 / 2 : ℝ) ^ j * L
  ⨆ p : ↥(scheduleSamplePairs
    (S.net (empiricalMeasure n z) hQ (j + 1)) z ρ),
      |conditionalRademacherIncrement z σ p.1.1 -
        conditionalRademacherIncrement z σ p.1.2|

private theorem scheduleVerticalPairs_nonempty
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (j : ℕ) :
    let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
    let ρ := 2 * (1 / 2 : ℝ) ^ j * L
    (scheduleSamplePairs (S.net (empiricalMeasure n z) hQ (j + 1)) z ρ).Nonempty := by
  obtain ⟨f, hf⟩ := hF
  exact ⟨_, schedule_vertical_pair_mem S hn z hQ j ⟨f, hf⟩⟩

private theorem scheduleVerticalMaximum_nonneg
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (j : ℕ) (σ : Fin n → Bool) :
    0 ≤ scheduleVerticalMaximum S z hQ j σ := by
  let U := scheduleSamplePairs (S.net (empiricalMeasure n z) hQ (j + 1)) z
    (2 * (1 / 2 : ℝ) ^ j * (outerLpNorm (empiricalMeasure n z) G 2).toReal)
  letI : Nonempty ↥U := Set.nonempty_coe_sort.mpr (by
    simpa [U] using scheduleVerticalPairs_nonempty S hn z hQ hF j)
  unfold scheduleVerticalMaximum
  exact (abs_nonneg _).trans (le_ciSup (Finite.bddAbove_range fun p : ↥U =>
    |conditionalRademacherIncrement z σ p.1.1 -
      conditionalRademacherIncrement z σ p.1.2|) (Classical.choice inferInstance))

private theorem scheduleVerticalMaximum_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (j : ℕ) (σ : Fin n → Bool) :
    scheduleVerticalMaximum S z hQ j σ ≤
      Real.sqrt n * (2 * (1 / 2 : ℝ) ^ j *
        (outerLpNorm (empiricalMeasure n z) G 2).toReal) := by
  let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
  let ρ := 2 * (1 / 2 : ℝ) ^ j * L
  let U := scheduleSamplePairs (S.net (empiricalMeasure n z) hQ (j + 1)) z ρ
  letI : Nonempty ↥U := Set.nonempty_coe_sort.mpr (by
    simpa [U, ρ, L] using scheduleVerticalPairs_nonempty S hn z hQ hF j)
  unfold scheduleVerticalMaximum
  apply ciSup_le
  intro p
  refine (abs_conditionalRademacherIncrement_sub_le_sqrt_mul_sampleL2
    hn z σ p.1.1 p.1.2).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hp := p.2
  simp only [scheduleSamplePairs, Finset.mem_image] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  have hd := (Finset.mem_filter.mp hq).2
  change sampleL2Seminorm z ((p.1.1 : Ω → ℝ) - (p.1.2 : Ω → ℝ)) ≤ ρ
  rw [← hqp]
  exact hd

private theorem scheduleVerticalMaximum_summable
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (σ : Fin n → Bool) :
    Summable (fun j => scheduleVerticalMaximum S z hQ j σ) := by
  have hgeo : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hdom : Summable (fun j : ℕ => Real.sqrt n * 2 *
      (outerLpNorm (empiricalMeasure n z) G 2).toReal * (1 / 2 : ℝ) ^ j) :=
    hgeo.mul_left _
  apply Summable.of_nonneg_of_le
    (fun j => scheduleVerticalMaximum_nonneg S hn z hQ hF j σ) _ hdom
  intro j
  convert scheduleVerticalMaximum_le S hn z hQ hF j σ using 1; ring

private theorem conditionalRademacherIncrement_scheduleProj_tendsto
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (σ : Fin n → Bool) (f : ↥F) :
    Tendsto (fun j => conditionalRademacherIncrement z σ
      (scheduleProj S (empiricalMeasure n z) hQ j f : Ω → ℝ)) atTop
      (𝓝 (conditionalRademacherIncrement z σ (f : Ω → ℝ))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hpow : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hbound : ∀ j, dist
      (conditionalRademacherIncrement z σ
        (scheduleProj S (empiricalMeasure n z) hQ j f : Ω → ℝ))
      (conditionalRademacherIncrement z σ (f : Ω → ℝ)) ≤
      Real.sqrt n * ((1 / 2 : ℝ) ^ j *
        (outerLpNorm (empiricalMeasure n z) G 2).toReal) := by
    intro j
    rw [Real.dist_eq]
    refine (abs_conditionalRademacherIncrement_sub_le_sqrt_mul_sampleL2
      hn z σ (scheduleProj S (empiricalMeasure n z) hQ j f) f).trans ?_
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    rw [sampleL2Seminorm_sub_comm]
    exact (scheduleProj_sampleL2_lt S hn z hQ j f).le
  apply squeeze_zero (fun _ => dist_nonneg) hbound
  simpa [mul_assoc, mul_comm, mul_left_comm] using (hpow.const_mul
    (Real.sqrt n * (outerLpNorm (empiricalMeasure n z) G 2).toReal))

private theorem schedule_vertical_leg_le_tsum
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (σ : Fin n → Bool) (J : ℕ) (f : ↥F) :
    |conditionalRademacherIncrement z σ (f : Ω → ℝ) -
        conditionalRademacherIncrement z σ
          (scheduleProj S (empiricalMeasure n z) hQ J f : Ω → ℝ)| ≤
      ∑' k : ℕ, scheduleVerticalMaximum S z hQ (J + k) σ := by
  let a : ℕ → ℝ := fun j => conditionalRademacherIncrement z σ
    (scheduleProj S (empiricalMeasure n z) hQ j f : Ω → ℝ)
  let b : ℕ → ℝ := fun m => |a (J + m) - a J|
  let c : ℕ → ℝ := fun m =>
    ∑ k ∈ Finset.range m, scheduleVerticalMaximum S z hQ (J + k) σ
  have hbc : ∀ m, b m ≤ c m := by
    intro m
    have htel : a (J + m) - a J =
        ∑ k ∈ Finset.range m, (a (J + k + 1) - a (J + k)) := by
      simpa [a, Nat.add_assoc] using (Finset.sum_range_sub (fun k => a (J + k)) m).symm
    rw [show b m = |a (J + m) - a J| by rfl, htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro k hk
    let f₁ := scheduleProj S (empiricalMeasure n z) hQ (J + k) f
    let f₂ := scheduleProj S (empiricalMeasure n z) hQ (J + k + 1) f
    have hp : ((f₁ : Ω → ℝ), (f₂ : Ω → ℝ)) ∈
        scheduleSamplePairs (S.net (empiricalMeasure n z) hQ (J + k + 1)) z
          (2 * (1 / 2 : ℝ) ^ (J + k) *
            (outerLpNorm (empiricalMeasure n z) G 2).toReal) := by
      simpa [f₁, f₂, Nat.add_assoc] using
        schedule_vertical_pair_mem S hn z hQ (J + k) f
    unfold scheduleVerticalMaximum
    refine le_ciSup_of_le (Finite.bddAbove_range fun p : ↥(scheduleSamplePairs
      (S.net (empiricalMeasure n z) hQ (J + k + 1)) z
        (2 * (1 / 2 : ℝ) ^ (J + k) *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal)) =>
      |conditionalRademacherIncrement z σ p.1.1 -
        conditionalRademacherIncrement z σ p.1.2|) ⟨_, hp⟩ ?_
    change |a (J + k + 1) - a (J + k)| ≤
      |conditionalRademacherIncrement z σ (f₁ : Ω → ℝ) -
        conditionalRademacherIncrement z σ (f₂ : Ω → ℝ)|
    simp only [a, f₁, f₂, Nat.add_assoc]
    rw [abs_sub_comm]
  have hb_tendsto : Tendsto b atTop (𝓝
      |conditionalRademacherIncrement z σ (f : Ω → ℝ) - a J|) := by
    have ha := conditionalRademacherIncrement_scheduleProj_tendsto S hn z hQ σ f
    have hsub : Tendsto (fun m => a (J + m) - a J) atTop
        (𝓝 (conditionalRademacherIncrement z σ (f : Ω → ℝ) - a J)) := by
      have hshift : Tendsto (fun m => a (J + m)) atTop
          (𝓝 (conditionalRademacherIncrement z σ (f : Ω → ℝ))) := by
        simpa [a, Function.comp_def, Nat.add_comm] using
          (ha.comp (tendsto_add_atTop_nat J))
      exact hshift.sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => a J) atTop (𝓝 (a J)))
    simpa [b, abs_sub_comm] using hsub.abs
  have hvsum := scheduleVerticalMaximum_summable S hn z hQ hF σ
  have hshift : Summable (fun k => scheduleVerticalMaximum S z hQ (J + k) σ) :=
    hvsum.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hc_tendsto : Tendsto c atTop
      (𝓝 (∑' k : ℕ, scheduleVerticalMaximum S z hQ (J + k) σ)) := by
    simpa [c] using hshift.hasSum.tendsto_sum_nat
  exact le_of_tendsto_of_tendsto hb_tendsto hc_tendsto (Eventually.of_forall hbc)

/-- The real maximum over empirically close projected pairs at level `J`. -/
private noncomputable def scheduleHorizontalMaximum
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (J : ℕ) (σ : Fin n → Bool) : ℝ :=
  let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
  let ρ := 3 * (1 / 2 : ℝ) ^ J * L
  ⨆ p : ↥(scheduleSamplePairs
    (S.net (empiricalMeasure n z) hQ J) z ρ),
      |conditionalRademacherIncrement z σ p.1.1 -
        conditionalRademacherIncrement z σ p.1.2|

private theorem scheduleHorizontalPairs_nonempty
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (J : ℕ) :
    let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
    let ρ := 3 * (1 / 2 : ℝ) ^ J * L
    (scheduleSamplePairs (S.net (empiricalMeasure n z) hQ J) z ρ).Nonempty := by
  dsimp only
  obtain ⟨f, hf⟩ := hF
  let p : ↥F := ⟨f, hf⟩
  refine ⟨_, mem_scheduleSamplePairs _ z _
    (scheduleProj S (empiricalMeasure n z) hQ J p)
    (scheduleProj S (empiricalMeasure n z) hQ J p)
    (scheduleProj_mem S _ hQ J p) (scheduleProj_mem S _ hQ J p) ?_⟩
  simp [sampleL2Seminorm]

private theorem scheduleHorizontalMaximum_nonneg
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (J : ℕ) (σ : Fin n → Bool) :
    0 ≤ scheduleHorizontalMaximum S z hQ J σ := by
  let U := scheduleSamplePairs (S.net (empiricalMeasure n z) hQ J) z
    (3 * (1 / 2 : ℝ) ^ J *
      (outerLpNorm (empiricalMeasure n z) G 2).toReal)
  letI : Nonempty ↥U := Set.nonempty_coe_sort.mpr (by
    simpa [U] using scheduleHorizontalPairs_nonempty S z hQ hF J)
  unfold scheduleHorizontalMaximum
  exact (abs_nonneg _).trans (le_ciSup (Finite.bddAbove_range fun p : ↥U =>
    |conditionalRademacherIncrement z σ p.1.1 -
      conditionalRademacherIncrement z σ p.1.2|) (Classical.choice inferInstance))

private theorem outerExpectation_scheduleHorizontalMaximum_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (J : ℕ) :
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal (scheduleHorizontalMaximum S z hQ J σ)) ≤
      ENNReal.ofReal (6 * Real.sqrt 2 * (1 / 2 : ℝ) ^ J *
        (outerLpNorm (empiricalMeasure n z) G 2).toReal *
        Real.sqrt (Real.log (2 * (S.net (empiricalMeasure n z) hQ J).card))) := by
  let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
  let ρ := 3 * (1 / 2 : ℝ) ^ J * L
  have hL : 0 < L := ENNReal.toReal_pos (ne_of_gt hQ.2.1) (ne_of_lt hQ.2.2)
  have hρ : 0 < ρ := by positivity
  have hU : (scheduleSamplePairs
      (S.net (empiricalMeasure n z) hQ J) z ρ).Nonempty := by
    simpa [ρ, L] using scheduleHorizontalPairs_nonempty S z hQ hF J
  have hmax := outerExpectation_scheduleSamplePairs_iSup_le
    (S.net (empiricalMeasure n z) hQ J) z ρ hρ hU
  simpa only [scheduleHorizontalMaximum, L, ρ] using hmax.trans_eq (by
    congr 1
    ring)

private theorem outerExpectation_scheduleVerticalMaximum_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (j : ℕ) :
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal (scheduleVerticalMaximum S z hQ j σ)) ≤
      ENNReal.ofReal (4 * Real.sqrt 2 * (1 / 2 : ℝ) ^ j *
        (outerLpNorm (empiricalMeasure n z) G 2).toReal *
        Real.sqrt (Real.log
          (2 * (S.net (empiricalMeasure n z) hQ (j + 1)).card))) := by
  let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
  let ρ := 2 * (1 / 2 : ℝ) ^ j * L
  have hL : 0 < L := ENNReal.toReal_pos (ne_of_gt hQ.2.1) (ne_of_lt hQ.2.2)
  have hρ : 0 < ρ := by positivity
  have hU : (scheduleSamplePairs
      (S.net (empiricalMeasure n z) hQ (j + 1)) z ρ).Nonempty := by
    simpa [ρ, L] using scheduleVerticalPairs_nonempty S hn z hQ hF j
  have hmax := outerExpectation_scheduleSamplePairs_iSup_le
    (S.net (empiricalMeasure n z) hQ (j + 1)) z ρ hρ hU
  simpa only [scheduleVerticalMaximum, L, ρ] using hmax.trans_eq (by
    congr 1
    ring)

private theorem outerExpectation_scheduleVerticalTail_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (J : ℕ) :
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal
          (∑' k : ℕ, scheduleVerticalMaximum S z hQ (J + k) σ)) ≤
      ∑' k : ℕ, ENNReal.ofReal
        (4 * Real.sqrt 2 * (1 / 2 : ℝ) ^ (J + k) *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal *
          Real.sqrt (Real.log
            (2 * (S.net (empiricalMeasure n z) hQ (J + k + 1)).card))) := by
  let V : ℕ → (Fin n → Bool) → ℝ := fun k σ =>
    scheduleVerticalMaximum S z hQ (J + k) σ
  have hVnonneg : ∀ k σ, 0 ≤ V k σ := fun k σ =>
    scheduleVerticalMaximum_nonneg S hn z hQ hF (J + k) σ
  have hVsum : ∀ σ, Summable (fun k => V k σ) := by
    intro σ
    exact (scheduleVerticalMaximum_summable S hn z hQ hF σ).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)
  have hpoint : (fun σ => ENNReal.ofReal (∑' k, V k σ)) =
      fun σ => ∑' k, ENNReal.ofReal (V k σ) := by
    funext σ
    exact ENNReal.ofReal_tsum_of_nonneg (fun k => hVnonneg k σ) (hVsum σ)
  rw [show (fun σ => ENNReal.ofReal
      (∑' k : ℕ, scheduleVerticalMaximum S z hQ (J + k) σ)) =
      (fun σ => ENNReal.ofReal (∑' k, V k σ)) by rfl,
    hpoint, outerExpectation_eq_lintegral (measurable_of_finite _),
    lintegral_tsum (fun k => (measurable_of_finite _).aemeasurable)]
  apply ENNReal.tsum_le_tsum
  intro k
  rw [← outerExpectation_eq_lintegral (measurable_of_finite _)]
  exact outerExpectation_scheduleVerticalMaximum_le S hn z hQ hF (J + k)

private theorem conditionalRademacherLocalOscillation_le_scheduleMaxima
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (J : ℕ) (σ : Fin n → Bool) :
    conditionalRademacherLocalOscillation F z
        ((1 / 2 : ℝ) ^ J *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal) σ ≤
      ENNReal.ofReal (scheduleHorizontalMaximum S z hQ J σ +
        2 * ∑' k : ℕ, scheduleVerticalMaximum S z hQ (J + k) σ) := by
  apply iSup_le
  intro f
  apply iSup_le
  intro g
  split_ifs with hfg
  · apply ENNReal.ofReal_le_ofReal
    let rf := conditionalRademacherIncrement z σ (f : Ω → ℝ)
    let rg := conditionalRademacherIncrement z σ (g : Ω → ℝ)
    let rpf := conditionalRademacherIncrement z σ
      (scheduleProj S (empiricalMeasure n z) hQ J f : Ω → ℝ)
    let rpg := conditionalRademacherIncrement z σ
      (scheduleProj S (empiricalMeasure n z) hQ J g : Ω → ℝ)
    let V := ∑' k : ℕ, scheduleVerticalMaximum S z hQ (J + k) σ
    have hfV : |rf - rpf| ≤ V := by
      simpa [rf, rpf, V] using schedule_vertical_leg_le_tsum S hn z hQ hF σ J f
    have hgV : |rpg - rg| ≤ V := by
      rw [abs_sub_comm]
      simpa [rg, rpg, V] using schedule_vertical_leg_le_tsum S hn z hQ hF σ J g
    have hp : ((scheduleProj S (empiricalMeasure n z) hQ J f : Ω → ℝ),
        (scheduleProj S (empiricalMeasure n z) hQ J g : Ω → ℝ)) ∈
        scheduleSamplePairs (S.net (empiricalMeasure n z) hQ J) z
          (3 * (1 / 2 : ℝ) ^ J *
            (outerLpNorm (empiricalMeasure n z) G 2).toReal) :=
      schedule_horizontal_pair_mem S hn z hQ J f g hfg
    have hmid : |rpf - rpg| ≤ scheduleHorizontalMaximum S z hQ J σ := by
      unfold scheduleHorizontalMaximum
      refine le_ciSup_of_le (Finite.bddAbove_range fun p : ↥(scheduleSamplePairs
        (S.net (empiricalMeasure n z) hQ J) z
          (3 * (1 / 2 : ℝ) ^ J *
            (outerLpNorm (empiricalMeasure n z) G 2).toReal)) =>
        |conditionalRademacherIncrement z σ p.1.1 -
          conditionalRademacherIncrement z σ p.1.2|) ⟨_, hp⟩ ?_
      rfl
    have htri : |rf - rg| ≤ |rf - rpf| + |rpf - rpg| + |rpg - rg| := by
      calc
        |rf - rg| = |(rf - rpf) + (rpf - rpg) + (rpg - rg)| := by ring_nf
        _ ≤ |rf - rpf| + |rpf - rpg| + |rpg - rg| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    dsimp only [rf, rg] at htri ⊢
    nlinarith
  · exact bot_le

private theorem outerExpectation_conditionalRademacherLocalOscillation_le
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G) {n : ℕ} (hn : n ≠ 0) (z : Fin n → Ω)
    (hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z))
    (hF : F.Nonempty) (J : ℕ) :
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (conditionalRademacherLocalOscillation F z
          ((1 / 2 : ℝ) ^ J *
            (outerLpNorm (empiricalMeasure n z) G 2).toReal)) ≤
      ENNReal.ofReal (40 * (outerLpNorm (empiricalMeasure n z) G 2).toReal *
        dudleyScheduleTail S (empiricalMeasure n z) hQ J) := by
  let μ := (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
  let L := (outerLpNorm (empiricalMeasure n z) G 2).toReal
  let H : (Fin n → Bool) → ℝ := fun σ => scheduleHorizontalMaximum S z hQ J σ
  let V : (Fin n → Bool) → ℝ := fun σ =>
    ∑' k : ℕ, scheduleVerticalMaximum S z hQ (J + k) σ
  let a : ℕ → ℝ := fun j => (1 / 2 : ℝ) ^ j *
    Real.sqrt (Real.log (2 * (S.net (empiricalMeasure n z) hQ j).card))
  let b : ℕ → ℝ := fun k => 4 * Real.sqrt 2 * (1 / 2 : ℝ) ^ (J + k) * L *
    Real.sqrt (Real.log
      (2 * (S.net (empiricalMeasure n z) hQ (J + k + 1)).card))
  let hB : ℝ := 6 * Real.sqrt 2 * (1 / 2 : ℝ) ^ J * L *
    Real.sqrt (Real.log (2 * (S.net (empiricalMeasure n z) hQ J).card))
  have hH0 : ∀ σ, 0 ≤ H σ := fun σ =>
    scheduleHorizontalMaximum_nonneg S z hQ hF J σ
  have hV0 : ∀ σ, 0 ≤ V σ := fun σ => tsum_nonneg fun k =>
    scheduleVerticalMaximum_nonneg S hn z hQ hF (J + k) σ
  have hsplit : (fun σ => ENNReal.ofReal (H σ + 2 * V σ)) =
      fun σ => ENNReal.ofReal (H σ) + 2 * ENNReal.ofReal (V σ) := by
    funext σ
    rw [ENNReal.ofReal_add (hH0 σ) (mul_nonneg (by norm_num) (hV0 σ)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hHexp : outerExpectation μ (fun σ => ENNReal.ofReal (H σ)) ≤
      ENNReal.ofReal hB := by
    simpa [μ, H, hB, L] using
      outerExpectation_scheduleHorizontalMaximum_le S z hQ hF J
  have hVexp : outerExpectation μ (fun σ => ENNReal.ofReal (V σ)) ≤
      ∑' k : ℕ, ENNReal.ofReal (b k) := by
    simpa [μ, V, b, L] using
      outerExpectation_scheduleVerticalTail_le S hn z hQ hF J
  have hb0 : ∀ k, 0 ≤ b k := fun k => by
    dsimp only [b]
    positivity
  have haSum := S.entropySummable (empiricalMeasure n z) hQ
  have haShift : Summable (fun k => a (J + k + 1)) := by
    exact haSum.comp_injective (fun _ _ h => by omega)
  have hb_eq : b = fun k => 8 * Real.sqrt 2 * L * a (J + k + 1) := by
    funext k
    simp only [b, a, pow_succ]
    ring
  have hbSum : Summable b := by
    rw [hb_eq]
    exact haShift.mul_left _
  have hb_tsum : ∑' k, b k =
      8 * Real.sqrt 2 * L * ∑' k, a (J + k + 1) := by
    rw [hb_eq, tsum_mul_left]
  have haShiftJ : Summable (fun k => a (J + k)) := by
    exact haSum.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have htail_split : dudleyScheduleTail S (empiricalMeasure n z) hQ J =
      a J + ∑' k, a (J + k + 1) := by
    rw [dudleyScheduleTail_eq_tsum_nat_add]
    simpa only [a, Nat.add_zero, Nat.add_assoc] using haShiftJ.tsum_eq_zero_add
  have ha0 : ∀ j, 0 ≤ a j := fun _ => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ hB := by dsimp only [hB]; positivity
  have hreal : hB + 2 * ∑' k, b k ≤
      40 * L * dudleyScheduleTail S (empiricalMeasure n z) hQ J := by
    have hsqrt : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
    have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
    have haJ0 := ha0 J
    have htail0 : 0 ≤ ∑' k, a (J + k + 1) := tsum_nonneg fun k => ha0 _
    have hB_eq : hB = 6 * Real.sqrt 2 * L * a J := by
      dsimp only [hB, a]
      ring
    rw [hb_tsum, hB_eq, htail_split]
    calc
      6 * Real.sqrt 2 * L * a J +
          2 * (8 * Real.sqrt 2 * L * ∑' k, a (J + k + 1)) =
          Real.sqrt 2 * (6 * L * a J) +
            Real.sqrt 2 * (16 * L * ∑' k, a (J + k + 1)) := by ring
      _ ≤ 2 * (6 * L * a J) +
          2 * (16 * L * ∑' k, a (J + k + 1)) :=
        add_le_add
          (mul_le_mul_of_nonneg_right hsqrt (by positivity))
          (mul_le_mul_of_nonneg_right hsqrt (by positivity))
      _ ≤ 40 * L * (a J + ∑' k, a (J + k + 1)) := by
        have hLa : 0 ≤ L * a J := mul_nonneg hL0 haJ0
        have hLt : 0 ≤ L * ∑' k, a (J + k + 1) := mul_nonneg hL0 htail0
        nlinarith
  have hof_eq : ENNReal.ofReal hB + 2 * (∑' k, ENNReal.ofReal (b k)) =
      ENNReal.ofReal (hB + 2 * ∑' k, b k) := by
    rw [ENNReal.ofReal_add hB0 (mul_nonneg (by norm_num) (tsum_nonneg hb0)),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_tsum_of_nonneg hb0 hbSum]
    norm_num
  calc
    outerExpectation μ (conditionalRademacherLocalOscillation F z
        ((1 / 2 : ℝ) ^ J * L)) ≤
        outerExpectation μ (fun σ => ENNReal.ofReal (H σ + 2 * V σ)) :=
      outerExpectation_mono fun σ => by
        simpa [H, V, L] using
          conditionalRademacherLocalOscillation_le_scheduleMaxima
            S hn z hQ hF J σ
    _ = outerExpectation μ (fun σ =>
          ENNReal.ofReal (H σ) + 2 * ENNReal.ofReal (V σ)) := by rw [hsplit]
    _ ≤ outerExpectation μ (fun σ => ENNReal.ofReal (H σ)) +
          outerExpectation μ (fun σ => 2 * ENNReal.ofReal (V σ)) :=
      outerExpectation_add_le _ _
    _ = outerExpectation μ (fun σ => ENNReal.ofReal (H σ)) +
          2 * outerExpectation μ (fun σ => ENNReal.ofReal (V σ)) := by
      congr 1
      rw [show (fun σ => 2 * ENNReal.ofReal (V σ)) =
          (2 : ℝ≥0∞) • (fun σ => ENNReal.ofReal (V σ)) by
        funext σ; simp [Pi.smul_apply, smul_eq_mul],
        outerExpectation_const_smul 2 (by norm_num), smul_eq_mul]
    _ ≤ ENNReal.ofReal hB + 2 * (∑' k, ENNReal.ofReal (b k)) := by
      exact add_le_add hHexp (mul_le_mul_right hVexp 2)
    _ = ENNReal.ofReal (hB + 2 * ∑' k, b k) := hof_eq
    _ ≤ ENNReal.ofReal (40 * L *
          dudleyScheduleTail S (empiricalMeasure n z) hQ J) :=
      ENNReal.ofReal_le_ofReal hreal

/-- Conditional uniform-cover chaining. There is one universal
constant controlling every sample whose empirical envelope norm is finite. If
that norm vanishes, the oscillation is zero; otherwise the empirical law is
constructed internally as an admissible law and the expectation is bounded by
the schedule tail. This disjunction records the zero-norm branch explicitly.
For an iid sample, `uniformEntropy_outer_local_modulus` derives empirical-norm
finiteness almost surely from `hG2` and applies this deterministic bound on that
full-measure event. -/
theorem conditionalRademacher_chaining
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (S : UniformDudleySchedule F G)
      -- Theorem 19.14 uses `uniformDudleySchedule_of_uniformEntropy hJ`.
    : ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (_hn : n ≠ 0) (z : Fin n → Ω) (J : ℕ),
      outerLpNorm (empiricalMeasure n z) G 2 < ⊤ →
      outerLpNorm (empiricalMeasure n z) G 2 = 0 ∨
        ∃ hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z),
          outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
              (conditionalRademacherLocalOscillation F z
                ((1 / 2 : ℝ) ^ J *
                  (outerLpNorm (empiricalMeasure n z) G 2).toReal)) ≤
            ENNReal.ofReal (C * (outerLpNorm (empiricalMeasure n z) G 2).toReal *
              dudleyScheduleTail S (empiricalMeasure n z) hQ J) := by
  refine ⟨40, by norm_num, ?_⟩
  intro n hn z J hfinite
  by_cases hzero : outerLpNorm (empiricalMeasure n z) G 2 = 0
  · exact Or.inl hzero
  right
  letI : NeZero n := ⟨hn⟩
  have hpos : 0 < outerLpNorm (empiricalMeasure n z) G 2 :=
    bot_lt_iff_ne_bot.mpr hzero
  let hQ : IsAdmissibleMeasure G 2 (empiricalMeasure n z) :=
    ⟨inferInstance, hpos, hfinite⟩
  refine ⟨hQ, ?_⟩
  by_cases hF : F.Nonempty
  · exact outerExpectation_conditionalRademacherLocalOscillation_le
      S hn z hQ hF J
  · have hFempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF
    have hleft : outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (conditionalRademacherLocalOscillation F z
          ((1 / 2 : ℝ) ^ J *
            (outerLpNorm (empiricalMeasure n z) G 2).toReal)) = 0 := by
      rw [hFempty]
      have hosc : conditionalRademacherLocalOscillation (∅ : Set (Ω → ℝ)) z
          ((1 / 2 : ℝ) ^ J *
            (outerLpNorm (empiricalMeasure n z) G 2).toReal) = fun _ => 0 := by
        funext σ
        apply le_antisymm
        · apply iSup_le
          intro f
          exact f.2.elim
        · exact bot_le
      rw [hosc, outerExpectation_const, zero_mul]
    rw [hleft]
    exact bot_le

/-- The four-envelope schedule makes the unrestricted conditional process an
integrable fallback while retaining the original entropy ledger. -/
private theorem conditionalRademacher_global_chaining
    {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (_hn : n ≠ 0) (z : Fin n → Ω),
      outerLpNorm (empiricalMeasure n z) G 2 < ⊤ →
      outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (conditionalRademacherGlobalOscillation F z) ≤
        ENNReal.ofReal (C * (outerLpNorm (empiricalMeasure n z) G 2).toReal *
          uniformDudleyLedgerTail F (fourEnvelope G) 0) := by
  have hJ4 : uniformEntropyIntegral 1 F (fourEnvelope G) 2 < ⊤ := by
    apply lt_of_le_of_lt _ hJ
    unfold uniformEntropyIntegral
    refine setLIntegral_mono' measurableSet_Ioc fun ε _ => ?_
    exact entropyWeight_mono (uniformLpCoveringNumber_fourEnvelope_le ε)
  let S₄ : UniformDudleySchedule F (fourEnvelope G) :=
    uniformDudleySchedule_of_uniformEntropy hJ4
  obtain ⟨C₄, hC₄, hchain⟩ := conditionalRademacher_chaining S₄
  refine ⟨4 * C₄, by positivity, ?_⟩
  intro n hn z hfinite
  let L := outerLpNorm (empiricalMeasure n z) G 2
  have hfinite4 : outerLpNorm (empiricalMeasure n z) (fourEnvelope G) 2 < ⊤ := by
    rw [outerLpNorm_fourEnvelope]
    exact ENNReal.mul_lt_top (by norm_num) hfinite
  by_cases hzero : L = 0
  · have hglobal : conditionalRademacherGlobalOscillation F z = fun _ => 0 := by
      funext σ
      exact conditionalRademacherGlobalOscillation_eq_zero hEnv hn z hzero σ
    rw [hglobal, outerExpectation_const, zero_mul]
    exact bot_le
  · have hpos : 0 < L := bot_lt_iff_ne_bot.mpr hzero
    have hfour_ne : outerLpNorm (empiricalMeasure n z) (fourEnvelope G) 2 ≠ 0 := by
      rw [outerLpNorm_fourEnvelope]
      exact mul_ne_zero (by norm_num) hzero
    obtain hbad | ⟨hQ₄, hlocal⟩ := hchain hn z 0 hfinite4
    · exact (hfour_ne hbad).elim
    have hglobalLocal : ∀ σ : Fin n → Bool,
        conditionalRademacherGlobalOscillation F z σ ≤
          conditionalRademacherLocalOscillation F z
            ((1 / 2 : ℝ) ^ (0 : ℕ) *
              (outerLpNorm (empiricalMeasure n z) (fourEnvelope G) 2).toReal) σ := by
      intro σ
      simpa using conditionalRademacherGlobalOscillation_le_four_local
        hEnv hn z hfinite hpos σ
    have houter : outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (conditionalRademacherGlobalOscillation F z) ≤
        ENNReal.ofReal (C₄ *
          (outerLpNorm (empiricalMeasure n z) (fourEnvelope G) 2).toReal *
          dudleyScheduleTail S₄ (empiricalMeasure n z) hQ₄ 0) :=
      (outerExpectation_mono hglobalLocal).trans hlocal
    refine houter.trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [outerLpNorm_fourEnvelope, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
    have htail := dudleyScheduleTail_le_uniformLedgerTail hJ4 S₄
      (empiricalMeasure n z) hQ₄ 0
    have hL0 : 0 ≤ L.toReal := ENNReal.toReal_nonneg
    have hcoeff : 0 ≤ C₄ * 4 * L.toReal := by positivity
    calc
      C₄ * (4 * L.toReal) * dudleyScheduleTail S₄
          (empiricalMeasure n z) hQ₄ 0 =
          (C₄ * 4 * L.toReal) * dudleyScheduleTail S₄
            (empiricalMeasure n z) hQ₄ 0 := by ring
      _ ≤ (C₄ * 4 * L.toReal) *
          uniformDudleyLedgerTail F (fourEnvelope G) 0 :=
        mul_le_mul_of_nonneg_left htail hcoeff
      _ = 4 * C₄ * L.toReal *
          uniformDudleyLedgerTail F (fourEnvelope G) 0 := by ring

/-- The unrestricted conditional fallback controls every population-local
skeleton, without imposing an empirical localization event. -/
private theorem conditionalRademacher_skeletonGlobal_chaining
    {F F₀ : Set (Ω → ℝ)} {G : Ω → ℝ} (P : Measure Ω)
    (hF₀sub : F₀ ⊆ F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) {n : ℕ} (_hn : n ≠ 0)
      (z z' : Fin n → Ω),
      outerLpNorm (empiricalMeasure n z) G 2 < ⊤ →
      outerLpNorm (empiricalMeasure n z') G 2 < ⊤ →
      outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (fun σ => ENNReal.ofReal (Real.sqrt n) *
            signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ)
              n z z' σ) ≤
        ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal *
            uniformDudleyLedgerTail F (fourEnvelope G) 0) +
        ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z') G 2).toReal *
            uniformDudleyLedgerTail F (fourEnvelope G) 0) := by
  obtain ⟨C, hC, hglobal⟩ := conditionalRademacher_global_chaining hEnv hJ
  refine ⟨C, hC, ?_⟩
  intro δ n hn z z' hfinite hfinite'
  have hpoint (σ : Fin n → Bool) : ENNReal.ofReal (Real.sqrt n) *
      signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ) n z z' σ ≤
      conditionalRademacherGlobalOscillation F z σ +
        conditionalRademacherGlobalOscillation F z' σ :=
    scaled_signedGhostDeviation_le_globalOscillations
      hF₀sub hEnv P δ hn z z' hfinite hfinite' σ
  calc
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal (Real.sqrt n) *
          signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ)
            n z z' σ) ≤
        outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (fun σ => conditionalRademacherGlobalOscillation F z σ +
            conditionalRademacherGlobalOscillation F z' σ) :=
      outerExpectation_mono hpoint
    _ ≤ outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (conditionalRademacherGlobalOscillation F z) +
        outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (conditionalRademacherGlobalOscillation F z') :=
      outerExpectation_add_le _ _
    _ ≤ ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal *
            uniformDudleyLedgerTail F (fourEnvelope G) 0) +
        ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z') G 2).toReal *
            uniformDudleyLedgerTail F (fourEnvelope G) 0) :=
      add_le_add (hglobal hn z hfinite) (hglobal hn z' hfinite')

/-- On a square-GC good pair, the paired signed local skeleton is controlled
by the same deterministic ledger tail on both empirical laws. -/
private theorem conditionalRademacher_skeletonLocal_chaining
    {F F₀ : Set (Ω → ℝ)} {G : Ω → ℝ} (P : Measure Ω)
    (hF₀sub : F₀ ⊆ F)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
    (S : UniformDudleySchedule F G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ : ℝ) {n : ℕ} (_hn : n ≠ 0)
      (z z' : Fin n → Ω) (J : ℕ),
      outerLpNorm (empiricalMeasure n z) G 2 < ⊤ →
      outerLpNorm (empiricalMeasure n z') G 2 < ⊤ →
      0 < outerLpNorm (empiricalMeasure n z) G 2 →
      0 < outerLpNorm (empiricalMeasure n z') G 2 →
      (∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g < δ →
        sampleL2Seminorm z (f - g) < (1 / 2 : ℝ) ^ J *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal) →
      (∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g < δ →
        sampleL2Seminorm z' (f - g) < (1 / 2 : ℝ) ^ J *
          (outerLpNorm (empiricalMeasure n z') G 2).toReal) →
      outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (fun σ => ENNReal.ofReal (Real.sqrt n) *
            signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ)
              n z z' σ) ≤
        ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal *
            uniformDudleyLedgerTail F G J) +
        ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z') G 2).toReal *
            uniformDudleyLedgerTail F G J) := by
  obtain ⟨C, hC, hchain⟩ := conditionalRademacher_chaining S
  refine ⟨C, hC, ?_⟩
  intro δ n hn z z' J hfinite hfinite' hpos hpos' hz hz'
  have hpoint (σ : Fin n → Bool) : ENNReal.ofReal (Real.sqrt n) *
      signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ) n z z' σ ≤
      conditionalRademacherLocalOscillation F z
          ((1 / 2 : ℝ) ^ J *
            (outerLpNorm (empiricalMeasure n z) G 2).toReal) σ +
        conditionalRademacherLocalOscillation F z'
          ((1 / 2 : ℝ) ^ J *
            (outerLpNorm (empiricalMeasure n z') G 2).toReal) σ :=
    scaled_signedGhostDeviation_le_localOscillations
      hF₀sub P δ _ _ hn z z' σ hz hz'
  obtain hzero | ⟨hQ, hlocal⟩ := hchain hn z J hfinite
  · exact (ne_of_gt hpos hzero).elim
  obtain hzero' | ⟨hQ', hlocal'⟩ := hchain hn z' J hfinite'
  · exact (ne_of_gt hpos' hzero').elim
  have hledger := dudleyScheduleTail_le_uniformLedgerTail hJ S
    (empiricalMeasure n z) hQ J
  have hledger' := dudleyScheduleTail_le_uniformLedgerTail hJ S
    (empiricalMeasure n z') hQ' J
  have hL0 : 0 ≤ (outerLpNorm (empiricalMeasure n z) G 2).toReal :=
    ENNReal.toReal_nonneg
  have hL0' : 0 ≤ (outerLpNorm (empiricalMeasure n z') G 2).toReal :=
    ENNReal.toReal_nonneg
  have htail0 := dudleyScheduleTail_nonneg S (empiricalMeasure n z) hQ J
  have htail0' := dudleyScheduleTail_nonneg S (empiricalMeasure n z') hQ' J
  calc
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
        (fun σ => ENNReal.ofReal (Real.sqrt n) *
          signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ)
            n z z' σ) ≤
        outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (fun σ => conditionalRademacherLocalOscillation F z
              ((1 / 2 : ℝ) ^ J *
                (outerLpNorm (empiricalMeasure n z) G 2).toReal) σ +
            conditionalRademacherLocalOscillation F z'
              ((1 / 2 : ℝ) ^ J *
                (outerLpNorm (empiricalMeasure n z') G 2).toReal) σ) :=
      outerExpectation_mono hpoint
    _ ≤ outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (conditionalRademacherLocalOscillation F z
            ((1 / 2 : ℝ) ^ J *
              (outerLpNorm (empiricalMeasure n z) G 2).toReal)) +
        outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
          (conditionalRademacherLocalOscillation F z'
            ((1 / 2 : ℝ) ^ J *
              (outerLpNorm (empiricalMeasure n z') G 2).toReal)) :=
      outerExpectation_add_le _ _
    _ ≤ ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z) G 2).toReal *
            uniformDudleyLedgerTail F G J) +
        ENNReal.ofReal (C *
          (outerLpNorm (empiricalMeasure n z') G 2).toReal *
            uniformDudleyLedgerTail F G J) := by
      exact add_le_add
        (hlocal.trans (ENNReal.ofReal_le_ofReal (by gcongr)))
        (hlocal'.trans (ENNReal.ofReal_le_ofReal (by gcongr)))

/-- Outer empirical-process modulus over `distL2 P`-close class pairs.

Edge behavior: the empty class gives zero, a nonpositive `δ` retains the strict
ball, and the empirical process is zero when `n = 0`. -/
noncomputable def empiricalProcessLocalModulus {Ξ : Type*}
    (F : Set (Ω → ℝ)) (P : Measure Ω) (X : ℕ → Ξ → Ω)
    (n : ℕ) (δ : ℝ) (ξ : Ξ) : ℝ≥0∞ :=
  ⨆ (f : ↥F), ⨆ (g : ↥F),
    if distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ then
      ENNReal.ofReal |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ) -
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (g : Ω → ℝ)|
    else 0

private theorem empiricalProcessLocalModulus_le_skeleton
    {Ξ : Type*} {F F₀ : Set (Ω → ℝ)} {H : Ω → ℝ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ξ → Ω)
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    (hF₀sub : F₀ ⊆ F)
    (hF₀dense : ∀ f ∈ F, ∃ g : ℕ → (Ω → ℝ), (∀ n, g n ∈ F₀) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (ξ : Ξ) :
    empiricalProcessLocalModulus F P X n δ ξ ≤
      skeletonLocalProcessModulus F₀ P X n (2 * δ) ξ := by
  unfold empiricalProcessLocalModulus
  apply iSup_le
  intro f
  apply iSup_le
  intro g
  by_cases hfg : distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < δ
  · rw [if_pos hfg]
    obtain ⟨f₀, hf₀mem, hf₀lim⟩ := hF₀dense f f.property
    obtain ⟨g₀, hg₀mem, hg₀lim⟩ := hF₀dense g g.property
    have hdf := tendsto_distL2_of_pointwise_under_envelope
      (F := F) (H := H) (P := P) hFmeas hHenv hHLp
      f.property (fun m => hF₀sub (hf₀mem m)) hf₀lim
    have hdg := tendsto_distL2_of_pointwise_under_envelope
      (F := F) (H := H) (P := P) hFmeas hHenv hHLp
      g.property (fun m => hF₀sub (hg₀mem m)) hg₀lim
    have hdg' : Tendsto (fun m => distL2 P (g : Ω → ℝ) (g₀ m)) atTop
        (𝓝 0) := by
      convert hdg using 1
      funext m
      exact (distL2_comm (P := P) (g₀ m) (g : Ω → ℝ)).symm
    have hlocal : ∀ᶠ m in atTop, distL2 P (f₀ m) (g₀ m) < 2 * δ := by
      have ht : Tendsto (fun m => distL2 P (f₀ m) (f : Ω → ℝ) +
          distL2 P (f : Ω → ℝ) (g : Ω → ℝ) +
          distL2 P (g : Ω → ℝ) (g₀ m)) atTop
          (𝓝 (distL2 P (f : Ω → ℝ) (g : Ω → ℝ))) := by
        simpa only [zero_add, add_zero] using
          (hdf.add tendsto_const_nhds).add hdg'
      filter_upwards [ht (Iio_mem_nhds (show
          distL2 P (f : Ω → ℝ) (g : Ω → ℝ) < 2 * δ by linarith))] with m hm
      change distL2 P (f₀ m) (f : Ω → ℝ) +
        distL2 P (f : Ω → ℝ) (g : Ω → ℝ) +
        distL2 P (g : Ω → ℝ) (g₀ m) < 2 * δ at hm
      have hf₀Lp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp
        (hF₀sub (hf₀mem m))
      have hg₀Lp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp
        (hF₀sub (hg₀mem m))
      have hfLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp f.property
      have hgLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp g.property
      calc
        distL2 P (f₀ m) (g₀ m) ≤
            distL2 P (f₀ m) (f : Ω → ℝ) +
              distL2 P (f : Ω → ℝ) (g₀ m) :=
          distL2_triangle_of_memLp hf₀Lp hfLp hg₀Lp
        _ ≤ distL2 P (f₀ m) (f : Ω → ℝ) +
            (distL2 P (f : Ω → ℝ) (g : Ω → ℝ) +
              distL2 P (g : Ω → ℝ) (g₀ m)) := by
          gcongr
          exact distL2_triangle_of_memLp hfLp hgLp hg₀Lp
        _ < 2 * δ := by linarith
    have hpf := tendsto_empiricalProcess_of_pointwise_under_envelope
      (F := F) (H := H) (P := P)
      hFmeas hHenv hHLp (fun m => hF₀sub (hf₀mem m)) hf₀lim n
        (fun i : Fin n => X i.val ξ)
    have hpg := tendsto_empiricalProcess_of_pointwise_under_envelope
      (F := F) (H := H) (P := P)
      hFmeas hHenv hHLp (fun m => hF₀sub (hg₀mem m)) hg₀lim n
        (fun i : Fin n => X i.val ξ)
    have hproc : Tendsto (fun m =>
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (f₀ m) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) (g₀ m)) atTop
        (𝓝 (empiricalProcess P n (fun i : Fin n => X i.val ξ) (f : Ω → ℝ) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) (g : Ω → ℝ))) :=
      hpf.sub hpg
    have hcont := (ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_abs.tendsto _).comp hproc)
    refine le_of_tendsto hcont ?_
    filter_upwards [hlocal] with m hm
    let h : Ω → ℝ := f₀ m - g₀ m
    have hh : h ∈ skeletonLocalDifferenceClass F₀ P (2 * δ) :=
      ⟨f₀ m, hf₀mem m, g₀ m, hg₀mem m, hm, rfl⟩
    have hfint : Integrable (f₀ m) P := memLp_one_iff_integrable.mp
      ((classMember_memLp_of_l2Envelope hFmeas hHenv hHLp
        (hF₀sub (hf₀mem m))).mono_exponent (by norm_num))
    have hgint : Integrable (g₀ m) P := memLp_one_iff_integrable.mp
      ((classMember_memLp_of_l2Envelope hFmeas hHenv hHLp
        (hF₀sub (hg₀mem m))).mono_exponent (by norm_num))
    have hlin : empiricalProcess P n (fun i : Fin n => X i.val ξ) h =
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (f₀ m) -
          empiricalProcess P n (fun i : Fin n => X i.val ξ) (g₀ m) := by
      simpa only [h, Pi.sub_apply] using! empiricalProcess_sub P n
        (fun i : Fin n => X i.val ξ) (f₀ m) (g₀ m) hfint hgint
    change ENNReal.ofReal
      |empiricalProcess P n (fun i : Fin n => X i.val ξ) (f₀ m) -
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (g₀ m)| ≤
      skeletonLocalProcessModulus F₀ P X n (2 * δ) ξ
    rw [← hlin]
    exact le_supNormOver hh
  · rw [if_neg hfg]
    exact bot_le

/-- If the countable skeleton has zero `L²(P)` diameter, every one of its
empirical-process increments vanishes simultaneously almost surely. -/
private theorem outerExpectation_skeletonLocal_eq_zero_of_distL2
    {F F₀ : Set (Ω → ℝ)} {H : Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    (hF₀count : F₀.Countable) (hF₀sub : F₀ ⊆ F)
    (hzero : ∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g = 0)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXlaw : ∀ i, μ.map (X i) = P) (n : ℕ) (δ : ℝ) :
    outerExpectation μ (skeletonLocalProcessModulus F₀ P X n δ) = 0 := by
  let E := skeletonLocalDifferenceClass F₀ P δ
  have hEcount : E.Countable := skeletonLocalDifferenceClass_countable hF₀count P δ
  letI : Countable E := hEcount
  have hEzero (h : E) : (h.1 : Ω → ℝ) =ᵐ[P] 0 := by
    obtain ⟨f, hf, g, hg, -, hh⟩ := h.property
    have hfLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp (hF₀sub hf)
    have hgLp := classMember_memLp_of_l2Envelope hFmeas hHenv hHLp (hF₀sub hg)
    have hfgLp : MemLp (f - g) 2 P := hfLp.sub hgLp
    have hnorm : eLpNorm (f - g) 2 P = 0 := by
      have hreal : (eLpNorm (f - g) 2 P).toReal = 0 := by
        simpa only [distL2] using hzero f hf g hg
      exact (ENNReal.toReal_eq_zero_iff _).mp hreal |>.resolve_right hfgLp.eLpNorm_ne_top
    have hae : (f - g : Ω → ℝ) =ᵐ[P] 0 :=
      (eLpNorm_eq_zero_iff hfgLp.aestronglyMeasurable (by norm_num)).mp hnorm
    simpa only [hh] using hae
  have hsampleZero : ∀ᵐ ξ ∂μ, ∀ h : E, ∀ i : ℕ, h.1 (X i ξ) = 0 := by
    rw [ae_all_iff]
    intro h
    rw [ae_all_iff]
    intro i
    exact (MeasurePreserving.mk (hXmeas i) (hXlaw i)).quasiMeasurePreserving.ae
      (hEzero h)
  have hmodZero : skeletonLocalProcessModulus F₀ P X n δ =ᵐ[μ]
      (fun _ => 0) := by
    filter_upwards [hsampleZero] with ξ hξ
    apply le_antisymm
    · unfold skeletonLocalProcessModulus
      rw [supNormOver_eq_iSup_subtype_chaining]
      apply iSup_le
      intro h
      apply le_of_eq
      apply ENNReal.ofReal_eq_zero.mpr
      unfold empiricalProcess empiricalAvg
      have hsum : ∑ i : Fin n, h.1 (X i.val ξ) = 0 := by
        exact Finset.sum_eq_zero fun i _ => hξ h i.val
      rw [hsum, mul_zero, integral_eq_zero_of_ae (hEzero h)]
      norm_num
    · exact bot_le
  calc
    outerExpectation μ (skeletonLocalProcessModulus F₀ P X n δ) =
        outerExpectation μ (fun _ => 0) := outerExpectation_congr_ae hmodZero
    _ = 0 := by
      rw [outerExpectation_const]
      simp

/-- At a fixed dyadic scale, square-GC embeds every population-local skeleton
pair in the empirical balls used by `conditionalRademacher_chaining`.  The
complement of that event is
removed by a second-moment bound for a measurable majorant of the possibly
nonmeasurable envelope. -/
private theorem limsup_outerExpectation_skeletonLocal_le_fixedScale
    {F F₀ : Set (Ω → ℝ)} {G H : Ω → ℝ} {P : Measure Ω}
    [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
    (hPM : IsPointwiseMeasurable F)
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
    (hHenv : UniformEntropyStructural.IsEnvelope F H) (hHLp : MemLp H 2 P)
    (hG2 : outerLpNorm P G 2 < ⊤)
    (V : Ω → ℝ≥0∞) (hVmeas : Measurable V)
    (hGV : ∀ x, ENNReal.ofReal |G x| ^ (2 : ℝ) ≤ V x)
    (hVint : ∫⁻ x, V x ∂P < ⊤)
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
    (hF₀count : F₀.Countable) (hF₀sub : F₀ ⊆ F)
    {fstar gstar : Ω → ℝ} (hfstar : fstar ∈ F₀) (hgstar : gstar ∈ F₀)
    {d : ℝ} (hd : d = distL2 P fstar gstar) (hdpos : 0 < d)
    (S : UniformDudleySchedule F G) (J : ℕ) {δ : ℝ}
    (hδ : δ < (1 / 2 : ℝ) ^ J * d / 8)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hXmeas : ∀ i, Measurable (X i))
    (hXiindep : ProbabilityTheory.iIndepFun X μ)
    (hXid : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hXlaw : μ.map (X 0) = P) :
    limsup (fun n => outerExpectation μ
      (skeletonLocalProcessModulus F₀ P X n δ)) atTop ≤
      ENNReal.ofReal ((conditionalRademacher_skeletonLocal_chaining
        P hF₀sub hJ S).choose * uniformDudleyLedgerTail F G J) *
        (2 * (∫⁻ x, V x ∂P) ^ (2 : ℝ)⁻¹) := by
  classical
  let A : ℝ≥0∞ := ∫⁻ x, V x ∂P
  let a : ℝ := (1 / 2 : ℝ) ^ J * d / 8
  have ha : 0 < a := by dsimp only [a]; positivity
  have hXlawAll : ∀ i, μ.map (X i) = P :=
    fun i => (hXid i).map_eq.trans hXlaw
  have hSqMeas : ∀ h ∈ squareDifferenceClass F, Measurable h := by
    rintro h ⟨f, hf, g, hg, rfl⟩
    exact ((hFmeas f hf).sub (hFmeas g hg)).pow_const 2
  have hSqPM : IsPointwiseMeasurable (squareDifferenceClass F) := by
    obtain ⟨D, hDcount, hDsub, hDdense⟩ := hPM
    let pairSq : ((Ω → ℝ) × (Ω → ℝ)) → (Ω → ℝ) :=
      fun p x => (p.1 x - p.2 x) ^ 2
    let Dsq : Set (Ω → ℝ) := pairSq '' (D ×ˢ D)
    refine ⟨Dsq, (hDcount.prod hDcount).image pairSq, ?_, ?_⟩
    · rintro h ⟨⟨f, g⟩, hfg, rfl⟩
      exact ⟨f, hDsub hfg.1, g, hDsub hfg.2, rfl⟩
    · rintro h ⟨f, hf, g, hg, rfl⟩
      obtain ⟨f₀, hf₀, hflim⟩ := hDdense f hf
      obtain ⟨g₀, hg₀, hglim⟩ := hDdense g hg
      refine ⟨fun n x => (f₀ n x - g₀ n x) ^ 2, ?_, ?_⟩
      · intro n
        exact ⟨(f₀ n, g₀ n), ⟨hf₀ n, hg₀ n⟩, rfl⟩
      · intro x
        exact ((hflim x).sub (hglim x)).pow 2
  have hSqEnvH : UniformEntropyStructural.IsEnvelope
      (squareDifferenceClass F) (squareDifferenceEnvelope H) := by
    refine ⟨fun x => by unfold squareDifferenceEnvelope; positivity, ?_⟩
    rintro h ⟨f, hf, g, hg, rfl⟩ x
    have hfg : |f x - g x| ≤ 2 * H x := by
      calc
        |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
        _ ≤ H x + H x := add_le_add (hHenv.2 f hf x) (hHenv.2 g hg x)
        _ = 2 * H x := by ring
    simp only [abs_sq, squareDifferenceEnvelope]
    calc
      (f x - g x) ^ 2 = |f x - g x| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * H x) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (hHenv.1 x))).2 hfg
      _ = 4 * H x ^ 2 := by ring
  have hSqIntH : Integrable (squareDifferenceEnvelope H) P := by
    unfold squareDifferenceEnvelope
    exact hHLp.integrable_sq.const_mul 4
  have hdevMeas (n : ℕ) : Measurable
      (gcDeviation (squareDifferenceClass F) P X n) :=
    measurable_gcDeviation_chaining (squareDifferenceClass F)
      (squareDifferenceEnvelope H) P X n hSqMeas hSqPM hSqEnvH hSqIntH hXmeas
  let Good : ℕ → Set Ξ := fun n =>
    {ξ | gcDeviation (squareDifferenceClass F) P X n ξ ≤ ENNReal.ofReal (a ^ 2)}
  have hGoodMeas (n : ℕ) : MeasurableSet (Good n) :=
    measurableSet_le (hdevMeas n) measurable_const
  have hSqGC : IsPGlivenkoCantelliIID (squareDifferenceClass F) P :=
    squareDifference_uniformCovering_isPGlivenkoCantelliIID
    F G P hFmeas hPM hEnv hG2 hJ
  have hgc : ∀ᵐ ξ ∂μ, Tendsto
      (fun n => gcDeviation (squareDifferenceClass F) P X n ξ) atTop (𝓝 0) :=
    hSqGC hXmeas hXiindep hXid hXlaw
  have hGood : ∀ᵐ ξ ∂μ, ∀ᶠ n in atTop, ξ ∈ Good n := by
    filter_upwards [hgc] with ξ hξ
    filter_upwards [hξ (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ha)))]
      with n hn
    change gcDeviation (squareDifferenceClass F) P X n ξ <
      ENNReal.ofReal (a ^ 2) at hn
    exact hn.le
  let GoodPair : ℕ → Set (Ξ × Ξ) := fun n => Good n ×ˢ Good n
  have hGoodPairMeas (n : ℕ) : MeasurableSet (GoodPair n) :=
    (hGoodMeas n).prod (hGoodMeas n)
  have hGoodPair : ∀ᵐ ξ ∂(μ.prod μ), ∀ᶠ n in atTop, ξ ∈ GoodPair n := by
    have hfst : ∀ᵐ ξ ∂(μ.prod μ), ∀ᶠ n in atTop, ξ.1 ∈ Good n :=
      Measure.quasiMeasurePreserving_fst.ae hGood
    have hsnd : ∀ᵐ ξ ∂(μ.prod μ), ∀ᶠ n in atTop, ξ.2 ∈ Good n :=
      Measure.quasiMeasurePreserving_snd.ae hGood
    filter_upwards [hfst, hsnd] with ξ hξ hξ'
    filter_upwards [hξ, hξ'] with n hn hn'
    exact ⟨hn, hn'⟩
  have hBadMeasure : Tendsto
      (fun n => (μ.prod μ) (GoodPair n)ᶜ) atTop (𝓝 0) := by
    have ht := eventuallyGood_indicator_lintegral_tendsto_zero
      (μ.prod μ) (fun _ => 1) measurable_const (by simp)
      GoodPair hGoodPairMeas hGoodPair
    have heq : (fun n => ∫⁻ ξ : Ξ × Ξ,
        (GoodPair n)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ξ ∂(μ.prod μ)) =
        fun n => (μ.prod μ) (GoodPair n)ᶜ := by
      funext n
      exact lintegral_indicator_one (hGoodPairMeas n).compl
    rw [heq] at ht
    exact ht
  have hfinite : ∀ᵐ ξ ∂μ, ∀ n : ℕ, n ≠ 0 →
      outerLpNorm (empiricalMeasure n (fun i => X i.val ξ)) G 2 < ⊤ :=
    ae_empirical_outerLpNorm_lt_top μ P X G V hVmeas hGV hVint
      hXmeas hXlawAll
  have hfinitePair : ∀ᵐ ξ ∂(μ.prod μ), ∀ n : ℕ, n ≠ 0 →
      outerLpNorm (empiricalMeasure n (fun i => X i.val ξ.1)) G 2 < ⊤ ∧
      outerLpNorm (empiricalMeasure n (fun i => X i.val ξ.2)) G 2 < ⊤ := by
    have hfst : ∀ᵐ ξ : Ξ × Ξ ∂(μ.prod μ), ∀ n : ℕ, n ≠ 0 →
        outerLpNorm (empiricalMeasure n (fun i => X i.val ξ.1)) G 2 < ⊤ :=
      Measure.quasiMeasurePreserving_fst.ae hfinite
    have hsnd : ∀ᵐ ξ : Ξ × Ξ ∂(μ.prod μ), ∀ n : ℕ, n ≠ 0 →
        outerLpNorm (empiricalMeasure n (fun i => X i.val ξ.2)) G 2 < ⊤ :=
      Measure.quasiMeasurePreserving_snd.ae hfinite
    filter_upwards [hfst, hsnd] with ξ hξ hξ'
    exact fun n hn => ⟨hξ n hn, hξ' n hn⟩
  let C : ℝ := (conditionalRademacher_skeletonLocal_chaining
    P hF₀sub hJ S).choose
  have hClocal := (conditionalRademacher_skeletonLocal_chaining
    P hF₀sub hJ S).choose_spec
  have hC : 0 < C := hClocal.1
  have hlocal := hClocal.2
  obtain ⟨C₀, hC₀, hglobal⟩ :=
    conditionalRademacher_skeletonGlobal_chaining P hF₀sub hEnv hJ
  let bJ : ℝ := uniformDudleyLedgerTail F G J
  let b₀ : ℝ := uniformDudleyLedgerTail F (fourEnvelope G) 0
  have hbJ : 0 ≤ bJ := uniformDudleyLedgerTail_nonneg F G J
  have hb₀ : 0 ≤ b₀ := uniformDudleyLedgerTail_nonneg F (fourEnvelope G) 0
  let qJ : ℝ≥0∞ := ENNReal.ofReal (C * bJ)
  let q₀ : ℝ≥0∞ := ENNReal.ofReal (C₀ * b₀)
  let R : ℕ → Ξ → ℝ≥0∞ := fun n => empiricalMajorantRMS V X n
  have hRmeas (n : ℕ) : Measurable (R n) :=
    measurable_empiricalMajorantRMS V X hVmeas hXmeas n
  let K : ℕ → Ξ × Ξ → ℝ≥0∞ := fun n ξ =>
    outerExpectation (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
      (fun σ => ENNReal.ofReal (Real.sqrt n) *
        signedGhostDeviation (skeletonLocalDifferenceClass F₀ P δ) n
          (fun i => X i.val ξ.1) (fun i => X i.val ξ.2) σ)
  have hKmeas (n : ℕ) : Measurable (K n) :=
    measurable_conditionalScaledSignedExpectation_countable
      (skeletonLocalDifferenceClass F₀ P δ) X n
      (skeletonLocalDifferenceClass_countable hF₀count P δ)
      (skeletonLocalDifferenceClass_measurable
        (fun f hf => hFmeas f (hF₀sub hf)) P δ) hXmeas
  have hKbound : ∀ n : ℕ, n ≠ 0 → ∀ᵐ ξ ∂(μ.prod μ), K n ξ ≤
      qJ * (R n ξ.1 + R n ξ.2) +
        (GoodPair n)ᶜ.indicator (fun ξ => q₀ * (R n ξ.1 + R n ξ.2)) ξ := by
    intro n hn
    filter_upwards [hfinitePair] with ξ hξ
    have hfin := hξ n hn
    let L₁ := outerLpNorm
      (empiricalMeasure n (fun i : Fin n => X i.val ξ.1)) G 2
    let L₂ := outerLpNorm
      (empiricalMeasure n (fun i : Fin n => X i.val ξ.2)) G 2
    have hL₁R : L₁ ≤ R n ξ.1 := outerLpNorm_empirical_le_majorantRMS
      G V X hVmeas hGV ξ.1
    have hL₂R : L₂ ≤ R n ξ.2 := outerLpNorm_empirical_le_majorantRMS
      G V X hVmeas hGV ξ.2
    have hqJ₁ : ENNReal.ofReal (C * L₁.toReal * bJ) = qJ * L₁ := by
      exact ofReal_mul_toReal_mul_eq hC.le hbJ hfin.1.ne
    have hqJ₂ : ENNReal.ofReal (C * L₂.toReal * bJ) = qJ * L₂ := by
      exact ofReal_mul_toReal_mul_eq hC.le hbJ hfin.2.ne
    have hq₀₁ : ENNReal.ofReal (C₀ * L₁.toReal * b₀) = q₀ * L₁ := by
      exact ofReal_mul_toReal_mul_eq hC₀.le hb₀ hfin.1.ne
    have hq₀₂ : ENNReal.ofReal (C₀ * L₂.toReal * b₀) = q₀ * L₂ := by
      exact ofReal_mul_toReal_mul_eq hC₀.le hb₀ hfin.2.ne
    by_cases hgood : ξ ∈ GoodPair n
    · have hloc₁ := sampleLocal_of_squareDeviation X hn ξ.1 hF₀sub hFmeas
        hEnv hHenv hHLp hfstar hgstar hd hdpos J hδ hfin.1 hgood.1
      have hloc₂ := sampleLocal_of_squareDeviation X hn ξ.2 hF₀sub hFmeas
        hEnv hHenv hHLp hfstar hgstar hd hdpos J hδ hfin.2 hgood.2
      have hk := hlocal δ hn _ _ J hfin.1 hfin.2 hloc₁.1 hloc₂.1 hloc₁.2 hloc₂.2
      rw [Set.indicator_of_notMem (by simpa using hgood)]
      simp only [add_zero]
      dsimp only [K]
      rw [show uniformDudleyLedgerTail F G J = bJ by rfl] at hk
      rw [hqJ₁, hqJ₂] at hk
      exact hk.trans (by
        rw [mul_add]
        exact add_le_add (mul_le_mul_right hL₁R qJ)
          (mul_le_mul_right hL₂R qJ))
    · have hk := hglobal δ hn _ _ hfin.1 hfin.2
      rw [Set.indicator_of_mem (by simpa using hgood)]
      dsimp only [K]
      rw [show uniformDudleyLedgerTail F (fourEnvelope G) 0 = b₀ by rfl] at hk
      rw [hq₀₁, hq₀₂] at hk
      exact hk.trans (by
        rw [mul_add]
        calc
          q₀ * L₁ + q₀ * L₂ ≤ q₀ * R n ξ.1 + q₀ * R n ξ.2 :=
            add_le_add (mul_le_mul_right hL₁R q₀)
              (mul_le_mul_right hL₂R q₀)
          _ = q₀ * (R n ξ.1 + R n ξ.2) := (mul_add _ _ _).symm
          _ ≤ (qJ * R n ξ.1 + qJ * R n ξ.2) +
                q₀ * (R n ξ.1 + R n ξ.2) :=
            le_add_of_nonneg_left (zero_le))
  have houterBound : ∀ n : ℕ, n ≠ 0 →
      outerExpectation μ (skeletonLocalProcessModulus F₀ P X n δ) ≤
        qJ * (2 * A ^ (2 : ℝ)⁻¹) +
          q₀ * ((8 * A) ^ (2 : ℝ)⁻¹ *
            ((μ.prod μ) (GoodPair n)ᶜ) ^ (2 : ℝ)⁻¹) := by
    intro n hn
    let E := skeletonLocalDifferenceClass F₀ P δ
    have hEcount : E.Countable := skeletonLocalDifferenceClass_countable hF₀count P δ
    have hEmeas : ∀ f ∈ E, Measurable f :=
      skeletonLocalDifferenceClass_measurable
        (fun f hf => hFmeas f (hF₀sub hf)) P δ
    have hghostfinite : ∀ ξ : Ξ × Ξ, ghostDeviation E X n ξ.1 ξ.2 ≠ ⊤ :=
      fun ξ => ghostDeviation_skeleton_ne_top P δ X n ξ.1 ξ.2 hF₀sub hHenv
    have hsignedfinite : ∀ (ξ : Ξ × Ξ) (σ : Fin n → Bool),
        signedGhostDeviation E n (fun i => X i.val ξ.1)
          (fun i => X i.val ξ.2) σ ≠ ⊤ :=
      fun ξ σ => signedGhostDeviation_skeleton_ne_top P δ _ _ σ hF₀sub hHenv
    have hsymm := outerExpectation_scaled_ghostDeviation_le_signed
      μ E X n hEcount hEmeas hXmeas hXiindep hghostfinite hsignedfinite
    have hJensen := outerExpectation_skeletonLocalProcessModulus_le_ghost
      μ F F₀ H P X hFmeas hHenv hHLp hF₀count hF₀sub hXmeas hXlawAll n hn δ
    have hBmeas : Measurable (fun ξ : Ξ × Ξ =>
        qJ * (R n ξ.1 + R n ξ.2) +
          (GoodPair n)ᶜ.indicator
            (fun ξ => q₀ * (R n ξ.1 + R n ξ.2)) ξ) :=
      (measurable_const.mul
        ((hRmeas n).comp measurable_fst |>.add
          ((hRmeas n).comp measurable_snd))).add
        ((measurable_const.mul
          ((hRmeas n).comp measurable_fst |>.add
            ((hRmeas n).comp measurable_snd))).indicator
              (hGoodPairMeas n).compl)
    calc
      outerExpectation μ (skeletonLocalProcessModulus F₀ P X n δ) ≤
          outerExpectation (μ.prod μ) (fun ξ => ENNReal.ofReal (Real.sqrt n) *
            ghostDeviation E X n ξ.1 ξ.2) := hJensen
      _ ≤ outerExpectation (μ.prod μ) (K n) := hsymm
      _ = ∫⁻ ξ, K n ξ ∂(μ.prod μ) := outerExpectation_eq_lintegral (hKmeas n)
      _ ≤ ∫⁻ ξ, (qJ * (R n ξ.1 + R n ξ.2) +
          (GoodPair n)ᶜ.indicator
            (fun ξ => q₀ * (R n ξ.1 + R n ξ.2)) ξ) ∂(μ.prod μ) :=
        lintegral_mono_ae (hKbound n hn)
      _ = outerExpectation (μ.prod μ) (fun ξ =>
          qJ * (R n ξ.1 + R n ξ.2) +
            (GoodPair n)ᶜ.indicator
              (fun ξ => q₀ * (R n ξ.1 + R n ξ.2)) ξ) :=
        (outerExpectation_eq_lintegral hBmeas).symm
      _ ≤ qJ * (2 * A ^ (2 : ℝ)⁻¹) +
          q₀ * ((8 * A) ^ (2 : ℝ)⁻¹ *
            ((μ.prod μ) (GoodPair n)ᶜ) ^ (2 : ℝ)⁻¹) := by
        have hRfst : Measurable (fun ξ : Ξ × Ξ => R n ξ.1) :=
          (hRmeas n).comp measurable_fst
        have hRsnd : Measurable (fun ξ : Ξ × Ξ => R n ξ.2) :=
          (hRmeas n).comp measurable_snd
        have hRone := lintegral_empiricalMajorantRMS_le
          μ P V X hVmeas hXmeas hXlawAll hn
        have hfstIntegral : ∫⁻ ξ : Ξ × Ξ, R n ξ.1 ∂(μ.prod μ) =
            ∫⁻ ξ : Ξ, R n ξ ∂μ := by
          rw [lintegral_prod]
          · simp
          · exact hRfst.aemeasurable
        have hsndIntegral : ∫⁻ ξ : Ξ × Ξ, R n ξ.2 ∂(μ.prod μ) =
            ∫⁻ ξ : Ξ, R n ξ ∂μ := by
          rw [lintegral_prod]
          · simp
          · exact hRsnd.aemeasurable
        have hRsum : ∫⁻ ξ : Ξ × Ξ, (R n ξ.1 + R n ξ.2) ∂(μ.prod μ) ≤
            2 * A ^ (2 : ℝ)⁻¹ := by
          rw [lintegral_add_left hRfst, hfstIntegral, hsndIntegral]
          dsimp only [R, A]
          exact (add_le_add hRone hRone).trans_eq (by ring)
        rw [outerExpectation_eq_lintegral hBmeas,
          lintegral_add_left
            (measurable_const.fun_mul (hRfst.fun_add hRsnd))]
        apply add_le_add
        · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact mul_le_mul_right hRsum qJ
        · rw [show (GoodPair n)ᶜ.indicator
              (fun ξ => q₀ * (R n ξ.1 + R n ξ.2)) =
              fun ξ => q₀ * (GoodPair n)ᶜ.indicator
                (fun ξ => R n ξ.1 + R n ξ.2) ξ by
            funext ξ
            by_cases hξ : ξ ∈ (GoodPair n)ᶜ <;> simp [hξ],
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          apply mul_le_mul_right
          have hholder := lintegral_indicator_le_rpow_two_mul_measure
            (μ.prod μ) (fun ξ => R n ξ.1 + R n ξ.2)
              (hRfst.add hRsnd) (GoodPair n)ᶜ (hGoodPairMeas n).compl
          refine hholder.trans ?_
          apply mul_le_mul_left
          exact ENNReal.rpow_le_rpow
            (lintegral_pair_empiricalMajorantRMS_sq_le
              μ P V X hVmeas hXmeas hXlawAll hn) (by norm_num)
  let B : ℕ → ℝ≥0∞ := fun n => qJ * (2 * A ^ (2 : ℝ)⁻¹) +
    q₀ * ((8 * A) ^ (2 : ℝ)⁻¹ *
      ((μ.prod μ) (GoodPair n)ᶜ) ^ (2 : ℝ)⁻¹)
  have hBtendsto : Tendsto B atTop (𝓝 (qJ * (2 * A ^ (2 : ℝ)⁻¹))) := by
    have hpow : Tendsto
        (fun n => ((μ.prod μ) (GoodPair n)ᶜ) ^ (2 : ℝ)⁻¹) atTop
        (nhds ((0 : ℝ≥0∞) ^ (2 : ℝ)⁻¹)) :=
      (ENNReal.continuous_rpow_const.tendsto 0).comp hBadMeasure
    have hbad0 : Tendsto (fun n => ((μ.prod μ) (GoodPair n)ᶜ) ^ (2 : ℝ)⁻¹)
        atTop (𝓝 0) := by
      simpa only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
        using hpow
    have h8top : (8 * A) ^ (2 : ℝ)⁻¹ ≠ ⊤ := by
      apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      exact ENNReal.mul_ne_top (by norm_num) hVint.ne
    have htail1 := ENNReal.Tendsto.const_mul hbad0 (Or.inr h8top)
    have hq₀top : q₀ ≠ ⊤ := by
      dsimp only [q₀]
      exact ENNReal.ofReal_ne_top
    have htail : Tendsto (fun n => q₀ * ((8 * A) ^ (2 : ℝ)⁻¹ *
        ((μ.prod μ) (GoodPair n)ᶜ) ^ (2 : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul htail1 (Or.inr hq₀top)
    simpa only [B, mul_zero, add_zero] using
      (tendsto_const_nhds.add htail)
  have hlim : limsup (fun n => outerExpectation μ
      (skeletonLocalProcessModulus F₀ P X n δ)) atTop ≤ limsup B atTop :=
    limsup_le_limsup (eventually_atTop.2 ⟨1, fun n hn =>
      houterBound n (Nat.ne_of_gt hn)⟩) isCobounded_le_of_bot
      (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  calc
    limsup (fun n => outerExpectation μ
        (skeletonLocalProcessModulus F₀ P X n δ)) atTop ≤ limsup B atTop := hlim
    _ = qJ * (2 * A ^ (2 : ℝ)⁻¹) := hBtendsto.limsup_eq
    _ = ENNReal.ofReal (C * uniformDudleyLedgerTail F G J) *
        (2 * (∫⁻ x, V x ∂P) ^ (2 : ℝ)⁻¹) := by
      rfl

/-- A deterministic gauge tending to
zero controls the limsup of the outer expected empirical-process modulus,
uniformly over every iid realization of `P`.

The proof combines conditional chaining with tail truncation and the
squared-difference GC result. The gauge is fixed independently of the iid
realization. -/
theorem uniformEntropy_outer_local_modulus
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
      -- vdV 19.14 measurable class members.
    (hPM : IsPointwiseMeasurable F)
      -- vdV 19.14 suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV 19.14 envelope condition.
    (hG2 : outerLpNorm P G 2 < ⊤)
      -- vdV 19.14 finite outer squared-envelope moment.
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
      -- vdV 19.14 uniform entropy integral.
    : ∃ ψ : ℝ → ℝ≥0∞, Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      ∀ {Ξ : Type} [_inst : MeasurableSpace Ξ] (μ : Measure Ξ)
        [_inst2 : IsProbabilityMeasure μ] (X : ℕ → Ξ → Ω),
        (∀ i, Measurable (X i)) →
        ProbabilityTheory.iIndepFun X μ →
        (∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) →
        μ.map (X 0) = P →
        ∀ δ : ℝ, 0 < δ →
          limsup (fun n => outerExpectation μ
            (empiricalProcessLocalModulus F P X n δ)) atTop ≤ ψ δ := by
  classical
  obtain ⟨H, hHmeas, hHenv, hHLp⟩ :=
    exists_measurable_l2_envelope hFmeas hPM hEnv hG2
  obtain ⟨V, hVmeas, hGV, hVint⟩ :=
    exists_measurable_outerSquareMajorant G P hG2
  have hPMcopy := hPM
  obtain ⟨F₀, hF₀count, hF₀sub, hF₀dense⟩ := hPM
  let S : UniformDudleySchedule F G := uniformDudleySchedule_of_uniformEntropy hJ
  let M : ℝ≥0∞ := 2 * (∫⁻ x, V x ∂P) ^ (2 : ℝ)⁻¹
  have hMtop : M ≠ ⊤ := by
    apply ENNReal.mul_ne_top (by norm_num)
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    exact hVint.ne
  by_cases hdiam : ∃ f ∈ F₀, ∃ g ∈ F₀, 0 < distL2 P f g
  · obtain ⟨fstar, hfstar, gstar, hgstar, hdpos⟩ := hdiam
    let d : ℝ := distL2 P fstar gstar
    let C : ℝ := (conditionalRademacher_skeletonLocal_chaining
      P hF₀sub hJ S).choose
    have hC : 0 < C := (conditionalRademacher_skeletonLocal_chaining
      P hF₀sub hJ S).choose_spec.1
    let R : ℕ → ℝ≥0∞ := fun J =>
      ENNReal.ofReal (C * uniformDudleyLedgerTail F G J) * M
    let a : ℕ → ℝ := fun J => (1 / 2 : ℝ) ^ J * d / 16
    let ψ : ℝ → ℝ≥0∞ := fun δ => ⨅ J : ℕ, if δ < a J then R J else ⊤
    have hRtendsto : Tendsto R atTop (𝓝 0) := by
      have htail := uniformDudleyLedgerTail_tendsto_zero hJ
      have htailC : Tendsto (fun J => C * uniformDudleyLedgerTail F G J)
          atTop (nhds 0) := by
        simpa only [mul_zero] using htail.const_mul C
      have hreal := (ENNReal.continuous_ofReal.tendsto 0).comp htailC
      simpa only [R, ENNReal.ofReal_zero, zero_mul] using!
        ENNReal.Tendsto.mul_const hreal (Or.inr hMtop)
    have hψ : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      have hev : ∀ᶠ J in atTop, R J < ε := hRtendsto (Iio_mem_nhds hε)
      obtain ⟨J, hRJ⟩ := hev.exists
      have haJ : 0 < a J := by dsimp only [a, d]; positivity
      filter_upwards [Ioo_mem_nhdsGT haJ] with δ hδ
      change (⨅ J : ℕ, if δ < a J then R J else ⊤) ≤ ε
      refine (iInf_le_of_le J ?_).trans hRJ.le
      rw [if_pos hδ.2]
    refine ⟨ψ, hψ, ?_⟩
    intro Ξ _ μ _ X hXmeas hXiindep hXid hXlaw δ hδ
    have hXlawAll : ∀ i, μ.map (X i) = P :=
      fun i => (hXid i).map_eq.trans hXlaw
    have hmain : ∀ J : ℕ, δ < a J →
        limsup (fun n => outerExpectation μ
          (empiricalProcessLocalModulus F P X n δ)) atTop ≤ R J := by
      intro J hsmall
      have hδscale : 2 * δ < (1 / 2 : ℝ) ^ J * d / 8 := by
        dsimp only [a] at hsmall
        linarith
      have hskel := limsup_outerExpectation_skeletonLocal_le_fixedScale
        hFmeas hPMcopy hEnv hHenv hHLp hG2 V hVmeas hGV hVint
        hJ hF₀count hF₀sub
        hfstar hgstar (d := d) rfl hdpos S J hδscale μ X
        hXmeas hXiindep hXid hXlaw
      have hpoint (n : ℕ) : outerExpectation μ
          (empiricalProcessLocalModulus F P X n δ) ≤
          outerExpectation μ (skeletonLocalProcessModulus F₀ P X n (2 * δ)) :=
        outerExpectation_mono fun ξ => empiricalProcessLocalModulus_le_skeleton
          P X hFmeas hHenv hHLp hF₀sub hF₀dense n δ hδ ξ
      exact (limsup_le_limsup (Eventually.of_forall hpoint)
        isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)).trans
        (by simpa only [R, M] using hskel)
    unfold ψ
    apply le_iInf
    intro J
    by_cases hj : δ < a J
    · rw [if_pos hj]
      exact hmain J hj
    · rw [if_neg hj]
      exact le_top
  · have hzero : ∀ f ∈ F₀, ∀ g ∈ F₀, distL2 P f g = 0 := by
      intro f hf g hg
      exact le_antisymm (le_of_not_gt fun hpos => hdiam ⟨f, hf, g, hg, hpos⟩)
        (by unfold distL2; positivity)
    refine ⟨fun _ => 0, tendsto_const_nhds, ?_⟩
    intro Ξ _ μ _ X hXmeas _ hXid hXlaw δ hδ
    have hXlawAll : ∀ i, μ.map (X i) = P :=
      fun i => (hXid i).map_eq.trans hXlaw
    have hpoint (n : ℕ) : outerExpectation μ
        (empiricalProcessLocalModulus F P X n δ) = 0 := by
      have hle : outerExpectation μ (empiricalProcessLocalModulus F P X n δ) ≤
          outerExpectation μ (skeletonLocalProcessModulus F₀ P X n (2 * δ)) :=
        outerExpectation_mono (fun ξ =>
          empiricalProcessLocalModulus_le_skeleton P X hFmeas hHenv hHLp
            hF₀sub hF₀dense n δ hδ ξ)
      rw [outerExpectation_skeletonLocal_eq_zero_of_distL2
        hFmeas hHenv hHLp hF₀count hF₀sub hzero μ X hXmeas hXlawAll n (2 * δ)] at hle
      exact le_antisymm hle bot_le
    have heq : (fun n => outerExpectation μ
        (empiricalProcessLocalModulus F P X n δ)) = fun _ => 0 := by
      funext n
      exact hpoint n
    rw [heq, limsup_const]

/-- Asymptotic equicontinuity from uniform entropy. This is the
Theorem 18.14(ii) conclusion, derived from `uniformEntropy_outer_local_modulus`
by outer Markov and a
right-neighborhood choice of the modulus radius.  No equicontinuity or Dudley
data are requested from the caller. -/
theorem uniformEntropy_asymptoticallyEquicontinuous
    (F : Set (Ω → ℝ)) (G : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hFmeas : ∀ f ∈ F, Measurable f)
      -- vdV 19.14 measurable class members.
    (hPM : IsPointwiseMeasurable F)
      -- vdV 19.14 suitable measurability.
    (hEnv : UniformEntropyStructural.IsEnvelope F G)
      -- vdV 19.14 envelope condition.
    (hG2 : outerLpNorm P G 2 < ⊤)
      -- vdV 19.14 finite outer squared-envelope moment.
    (hJ : uniformEntropyIntegral 1 F G 2 < ⊤)
      -- vdV 19.14 uniform entropy integral.
    : IsAsymptoticallyEquicontinuous F P := by
  obtain ⟨ψ, hψ, hmod⟩ := uniformEntropy_outer_local_modulus
    F G P hFmeas hPM hEnv hG2 hJ
  intro Ξ _ μ _ X hXmeas hXiindep hXid hXlaw ε η hε hη
  have hηε : 0 < η * ε := mul_pos hη hε
  have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      ψ δ < ENNReal.ofReal (η * ε) :=
    hψ (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hηε))
  have hpositive : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ :=
    self_mem_nhdsWithin
  haveI : (𝓝[>] (0 : ℝ)).NeBot := inferInstance
  obtain ⟨δ, hδ, hψδ⟩ := (hpositive.and hsmall).exists
  refine ⟨δ, hδ, ?_⟩
  let M : ℕ → Ξ → ℝ≥0∞ := fun n => empiricalProcessLocalModulus F P X n δ
  let A : ℕ → Set Ξ := fun n =>
    {ξ | ∃ s t : ↥F, distL2 P (s : Ω → ℝ) (t : Ω → ℝ) < δ ∧
      ε < |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ) -
        empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)|}
  have hεE_ne : ENNReal.ofReal ε ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hε
  have hεE_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hkey (n : ℕ) : μ.outerMeasureStar (A n) ≤
      outerExpectation μ (M n) / ENNReal.ofReal ε := by
    have hsub : A n ⊆ {ξ | ENNReal.ofReal ε ≤ M n ξ} := by
      rintro ξ ⟨s, t, hst, hosc⟩
      have hterm : ENNReal.ofReal
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (s : Ω → ℝ) -
            empiricalProcess P n (fun i : Fin n => X i.val ξ) (t : Ω → ℝ)| ≤
          M n ξ := by
        unfold M empiricalProcessLocalModulus
        refine le_iSup_of_le s (le_iSup_of_le t ?_)
        rw [if_pos hst]
      exact (ENNReal.ofReal_le_ofReal hosc.le).trans hterm
    exact (outerMeasureStar_mono μ hsub).trans
      (outerExpectation_markov (ENNReal.ofReal ε) hεE_ne hεE_top)
  have hmean : limsup (fun n => outerExpectation μ (M n)) atTop ≤ ψ δ := by
    simpa [M] using hmod μ X hXmeas hXiindep hXid hXlaw δ hδ
  have hinvtop : (ENNReal.ofReal ε)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr hεE_ne
  have hdiv : limsup (fun n => outerExpectation μ (M n) /
      ENNReal.ofReal ε) atTop ≤ ψ δ / ENNReal.ofReal ε := by
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [ENNReal.limsup_const_mul_of_ne_top hinvtop]
    gcongr
  have htarget : ψ δ / ENNReal.ofReal ε ≤ ENNReal.ofReal η := by
    calc
      ψ δ / ENNReal.ofReal ε ≤
          ENNReal.ofReal (η * ε) / ENNReal.ofReal ε :=
        ENNReal.div_le_div_right hψδ.le _
      _ = ENNReal.ofReal η := by
        rw [ENNReal.ofReal_mul hη.le]
        exact ENNReal.mul_div_cancel_right
          hεE_ne hεE_top
  change limsup (fun n => μ.outerMeasureStar (A n)) atTop ≤ ENNReal.ofReal η
  exact (limsup_le_limsup (Eventually.of_forall hkey)
    isCobounded_le_of_bot (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)).trans
      (hdiv.trans htarget)

end AsymptoticStatistics.EmpiricalProcess
