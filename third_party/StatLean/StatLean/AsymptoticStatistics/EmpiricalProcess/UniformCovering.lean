module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalMeasure

@[expose] public section

/-!
# Uniform finite-discrete covering entropy

This file defines a finite-discrete variant of the uniform covering
entropy, sufficient for conditional empirical chaining.  Van der Vaart p.274
takes the supremum over all probability measures; no claim of definitional
identity is made here.  The covering radius is normalized by the
finite-discrete `L²` size of the envelope.

The zero-denominator convention is explicit: when `Q Φ² = 0`, the normalized
covering number is `1`.

Declarations marked with `omit [MeasurableSpace Ω]` are intentionally stated
without that inert instance: they use only finite sums, functions, and order
structure. The measure-valued and empirical realizations retain the
measurable-space assumption where it is required.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A finite discrete probability law, represented by finitely many atoms and
nonnegative weights summing to one.

This representation is intentionally independent of ambient measurability:
its `L²` seminorm is a finite weighted sum.  A measure-valued realization is
provided separately when singletons are measurable. -/
structure FiniteDiscreteProbability (Ω : Type*) where
  /-- A finite discrete law has finitely many atoms. -/
  atomCount : ℕ
  /-- Locations of the atoms; repetitions are allowed. -/
  atom : Fin atomCount → Ω
  /-- Each atom carries a nonnegative weight. -/
  weight : Fin atomCount → ℝ≥0
  /-- Probability weights have total mass one. -/
  weight_sum : ∑ i, weight i = 1

namespace FiniteDiscreteProbability

/-- The probability measure represented by a finite discrete probability
bundle.  Repeated atoms have their weights added by the finite sum.  Edge
behavior: `atomCount = 0` cannot occur because `weight_sum` would assert
`0 = 1`. -/
noncomputable def measure (Q : FiniteDiscreteProbability Ω) : Measure Ω :=
  ∑ i, (Q.weight i : ℝ≥0∞) • Measure.dirac (Q.atom i)

/-- The measure represented by a finite discrete bundle has total mass one. -/
theorem measure_isProbability
    (Q : FiniteDiscreteProbability Ω) : IsProbabilityMeasure Q.measure := by
  refine ⟨?_⟩
  unfold measure
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul, mul_one]
  exact_mod_cast Q.weight_sum

/-- The finite-discrete `L²(Q)` seminorm
`(Σᵢ qᵢ |f(xᵢ)|²)¹ᐟ²`.

Edge behavior is total: repeated atoms contribute repeatedly according to
their weights, and the impossible zero-atom probability bundle needs no
special branch. -/
noncomputable def l2Seminorm (Q : FiniteDiscreteProbability Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt (∑ i, (Q.weight i : ℝ) * |f (Q.atom i)| ^ 2)

/-- The semidistance induced by the finite-discrete `L²(Q)` seminorm. -/
noncomputable def distL2 (Q : FiniteDiscreteProbability Ω)
    (f g : Ω → ℝ) : ℝ :=
  Q.l2Seminorm (f - g)

omit [MeasurableSpace Ω] in
lemma l2Seminorm_nonneg (Q : FiniteDiscreteProbability Ω) (f : Ω → ℝ) :
    0 ≤ Q.l2Seminorm f :=
  Real.sqrt_nonneg _

omit [MeasurableSpace Ω] in
/-- Pointwise domination in absolute value contracts the finite-discrete
`L²` seminorm. -/
lemma l2Seminorm_mono_abs (Q : FiniteDiscreteProbability Ω)
    (f g : Ω → ℝ) (h : ∀ x, |f x| ≤ |g x|) :
    Q.l2Seminorm f ≤ Q.l2Seminorm g := by
  unfold l2Seminorm
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith [abs_nonneg (f (Q.atom i)), abs_nonneg (g (Q.atom i)), h (Q.atom i)]

omit [MeasurableSpace Ω] in
lemma l2Seminorm_mul (Q : FiniteDiscreteProbability Ω)
    (c : ℝ) (f : Ω → ℝ) :
    Q.l2Seminorm (fun x => c * f x) = |c| * Q.l2Seminorm f := by
  unfold l2Seminorm
  have hsum :
      (∑ i, (Q.weight i : ℝ) * |c * f (Q.atom i)| ^ 2) =
        c ^ 2 * ∑ i, (Q.weight i : ℝ) * |f (Q.atom i)| ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [abs_mul, mul_pow, sq_abs]
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

omit [MeasurableSpace Ω] in
lemma distL2_mul (Q : FiniteDiscreteProbability Ω)
    (c : ℝ) (f g : Ω → ℝ) :
    Q.distL2 (fun x => c * f x) (fun x => c * g x) =
      |c| * Q.distL2 f g := by
  unfold distL2
  rw [show (fun x => c * f x) - (fun x => c * g x) =
      fun x => c * (f - g) x by
    funext x
    simp only [Pi.sub_apply]
    ring]
  exact l2Seminorm_mul Q c (f - g)

/-- Every nonempty empirical measure has a finite-discrete representation,
and its finite-sum `L²` seminorm is the empirical root-mean-square.

This representation is used after conditioning on a realized sample in
uniform-entropy chaining. -/
theorem exists_empirical_adapter {n : ℕ} [NeZero n] (X : Fin n → Ω) :
    ∃ Q : FiniteDiscreteProbability Ω,
      Q.measure = empiricalMeasure n X ∧
      ∀ f : Ω → ℝ,
        Q.l2Seminorm f = Real.sqrt (empiricalAvg (fun x => |f x| ^ 2) n X) := by
  let Q : FiniteDiscreteProbability Ω :=
    { atomCount := n
      atom := X
      weight := fun _ => (n : ℝ≥0)⁻¹
      weight_sum := by
        simp [Finset.sum_const, nsmul_eq_mul, NeZero.ne n] }
  refine ⟨Q, ?_, fun f => ?_⟩
  · simp [Q, measure, empiricalMeasure, Finset.smul_sum]
  · simp only [Q, l2Seminorm, empiricalAvg, NNReal.coe_inv, NNReal.coe_natCast,
      sq_abs]
    rw [← Finset.mul_sum, Real.sqrt_mul (by positivity), Real.sqrt_inv]

end FiniteDiscreteProbability

/-- The covering number in one finite-discrete `L²(Q)` semimetric, normalized
at radius `ε ‖Φ‖_{Q,2}`.

This is the finite-discrete variant sufficient for conditional
empirical chaining.  Van der Vaart p.274 takes the supremum over all
probability measures; no claim of definitional identity is made here.  The
ambient-center convention follows vdV: centers need not belong to `F`.
Edge behavior: if
`Q Φ² = 0`, equivalently `‖Φ‖_{Q,2}=0`, the value is defined to be `1` rather
than exposing a zero-radius or division-by-zero artifact.  Otherwise the
infimum is `⊤` when no finite net exists. -/
noncomputable def normalizedL2CoveringNumber
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (ε : ℝ) : ℕ∞ :=
  if Q.l2Seminorm Φ = 0 then 1 else
    ⨅ (S : Finset (Ω → ℝ))
      (_ : ∀ f ∈ F, ∃ g ∈ S,
        Q.distL2 f g < ε * Q.l2Seminorm Φ),
      (S.card : ℕ∞)

/-- The uniform normalized covering number
`sup_Q N(ε ‖Φ‖_{Q,2}, F, L²(Q))`, where `Q` ranges over finite discrete
probability laws.

This is a finite-discrete supremum, not vdV p.274's supremum over all
probability measures.  It is sufficient once the chaining argument conditions
on an empirical sample.

Edge behavior is inherited pointwise from `normalizedL2CoveringNumber`: every
zero-envelope denominator contributes exactly `1`.  The definition is an
extended natural and hence records lack of a finite cover as `⊤`. -/
noncomputable def uniformL2CoveringNumber
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (ε : ℝ) : ℕ∞ :=
  ⨆ Q : FiniteDiscreteProbability Ω,
    normalizedL2CoveringNumber Q F Φ ε

/-- The relative finite-discrete radius
`θ(Q,F,Φ) = sup_f ‖f‖_{Q,2} / ‖Φ‖_{Q,2}` used in Lemma 19.38.

This encodes the radius displayed in vdV Lemma 19.38 p.289: its square is
`sup_f Qf² / QΦ²`. Edge behavior: when
`Q Φ² = 0`, the radius is defined to be zero. -/
noncomputable def finiteDiscreteRelativeRadius
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) : ℝ≥0∞ :=
  if Q.l2Seminorm Φ = 0 then 0 else
    ⨆ f ∈ F, ENNReal.ofReal (Q.l2Seminorm f / Q.l2Seminorm Φ)

/-- The uniform covering entropy integral
`J(δ,F,L₂) = ∫₀^δ √log(1 + sup_Q N(ε‖Φ‖_{Q,2},F,L₂(Q))) dε`.

Finite-discrete variant sufficient for conditional empirical
chaining; vdV p.274 takes the supremum over all probability measures; no claim
of definitional identity.  Edge behavior: `δ ≤ 0` gives the integral over the
empty interval and hence zero; an infinite covering number on a positive-
measure set yields `∞`. -/
noncomputable def uniformCoveringEntropyIntegral
    (δ : ℝ) (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 δ,
    entropyWeight (uniformL2CoveringNumber F Φ ε) ∂volume

omit [MeasurableSpace Ω] in
/-- The zero-denominator convention for one finite-discrete law. -/
@[simp] lemma normalizedL2CoveringNumber_of_l2Seminorm_eq_zero
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (ε : ℝ) (hΦ : Q.l2Seminorm Φ = 0) :
    normalizedL2CoveringNumber Q F Φ ε = 1 := by
  simp [normalizedL2CoveringNumber, hΦ]

omit [MeasurableSpace Ω] in
/-- The Lemma 19.38 relative radius is zero when its envelope denominator is
zero. -/
@[simp] lemma finiteDiscreteRelativeRadius_of_l2Seminorm_eq_zero
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    (hΦ : Q.l2Seminorm Φ = 0) :
    finiteDiscreteRelativeRadius Q F Φ = 0 := by
  simp [finiteDiscreteRelativeRadius, hΦ]

omit [MeasurableSpace Ω] in
/-- A normalized cover for a particular finite-discrete law is bounded by the
uniform covering number. -/
lemma normalizedL2CoveringNumber_le_uniform
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (ε : ℝ) :
    normalizedL2CoveringNumber Q F Φ ε ≤
      uniformL2CoveringNumber F Φ ε := by
  exact le_iSup (fun Q' : FiniteDiscreteProbability Ω =>
    normalizedL2CoveringNumber Q' F Φ ε) Q

omit [MeasurableSpace Ω] in
/-- The uniform normalized covering number is monotone in the function class. -/
lemma uniformL2CoveringNumber_mono_class
    {F G : Set (Ω → ℝ)} (hFG : F ⊆ G) (Φ : Ω → ℝ) (ε : ℝ) :
    uniformL2CoveringNumber F Φ ε ≤
      uniformL2CoveringNumber G Φ ε := by
  unfold uniformL2CoveringNumber
  refine iSup_le fun Q => ?_
  refine (show normalizedL2CoveringNumber Q F Φ ε ≤
    normalizedL2CoveringNumber Q G Φ ε from ?_).trans
      (le_iSup (fun Q' : FiniteDiscreteProbability Ω =>
        normalizedL2CoveringNumber Q' G Φ ε) Q)
  by_cases hΦ : Q.l2Seminorm Φ = 0
  · simp [normalizedL2CoveringNumber, hΦ]
  · simp only [normalizedL2CoveringNumber, if_neg hΦ]
    refine le_iInf (α := ℕ∞) fun S => le_iInf (α := ℕ∞) fun hS => ?_
    exact iInf_le_of_le S (iInf_le_of_le (fun f hf => hS f (hFG hf)) le_rfl)

omit [MeasurableSpace Ω] in
/-- The uniform normalized covering number is antitone in the relative radius. -/
lemma uniformL2CoveringNumber_antitone_eps
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    uniformL2CoveringNumber F Φ ε₂ ≤
      uniformL2CoveringNumber F Φ ε₁ := by
  unfold uniformL2CoveringNumber
  refine iSup_le fun Q => ?_
  refine (show normalizedL2CoveringNumber Q F Φ ε₂ ≤
    normalizedL2CoveringNumber Q F Φ ε₁ from ?_).trans
      (le_iSup (fun Q' : FiniteDiscreteProbability Ω =>
        normalizedL2CoveringNumber Q' F Φ ε₁) Q)
  by_cases hΦ : Q.l2Seminorm Φ = 0
  · simp [normalizedL2CoveringNumber, hΦ]
  · simp only [normalizedL2CoveringNumber, if_neg hΦ]
    refine le_iInf (α := ℕ∞) fun S => le_iInf (α := ℕ∞) fun hS => ?_
    refine iInf_le_of_le S (iInf_le_of_le (fun f hf => ?_) le_rfl)
    obtain ⟨g, hgS, hfg⟩ := hS f hf
    exact ⟨g, hgS, lt_of_lt_of_le hfg (mul_le_mul_of_nonneg_right hε
      (FiniteDiscreteProbability.l2Seminorm_nonneg Q Φ))⟩

omit [MeasurableSpace Ω] in
private lemma normalizedL2CoveringNumber_smul_le
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (c ε : ℝ) (hc : c ≠ 0) :
    normalizedL2CoveringNumber Q
        ((fun f : Ω → ℝ => fun x => c * f x) '' F)
        (fun x => |c| * Φ x) ε ≤
      normalizedL2CoveringNumber Q F Φ ε := by
  classical
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hΦscale : Q.l2Seminorm (fun x => |c| * Φ x) = |c| * Q.l2Seminorm Φ := by
    simpa using FiniteDiscreteProbability.l2Seminorm_mul Q |c| Φ
  by_cases hΦ : Q.l2Seminorm Φ = 0
  · have hΦscale0 : Q.l2Seminorm (fun x => |c| * Φ x) = 0 := by
      rw [hΦscale, hΦ, mul_zero]
    simp [normalizedL2CoveringNumber, hΦ, hΦscale0]
  · have hΦscale_ne : Q.l2Seminorm (fun x => |c| * Φ x) ≠ 0 := by
      rw [hΦscale]
      exact mul_ne_zero (abs_ne_zero.mpr hc) hΦ
    simp only [normalizedL2CoveringNumber, if_neg hΦscale_ne, if_neg hΦ]
    refine le_iInf (α := ℕ∞) fun S => le_iInf (α := ℕ∞) fun hS => ?_
    let S' := S.image (fun g x => c * g x)
    refine iInf_le_of_le S' (iInf_le_of_le ?_ ?_)
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨g, hgS, hfg⟩ := hS f hf
      refine ⟨fun x => c * g x, Finset.mem_image_of_mem _ hgS, ?_⟩
      rw [FiniteDiscreteProbability.distL2_mul, hΦscale]
      calc
        |c| * Q.distL2 f g < |c| * (ε * Q.l2Seminorm Φ) :=
          mul_lt_mul_of_pos_left hfg hcabs
        _ = ε * (|c| * Q.l2Seminorm Φ) := by ring
    · exact_mod_cast Finset.card_image_le

omit [MeasurableSpace Ω] in
private lemma normalizedL2CoveringNumber_smul
    (Q : FiniteDiscreteProbability Ω) (F : Set (Ω → ℝ))
    (Φ : Ω → ℝ) (c ε : ℝ) (hc : c ≠ 0) :
    normalizedL2CoveringNumber Q
        ((fun f : Ω → ℝ => fun x => c * f x) '' F)
        (fun x => |c| * Φ x) ε =
      normalizedL2CoveringNumber Q F Φ ε := by
  apply le_antisymm (normalizedL2CoveringNumber_smul_le Q F Φ c ε hc)
  have hclass :
      (fun f : Ω → ℝ => fun x => c⁻¹ * f x) ''
          ((fun f : Ω → ℝ => fun x => c * f x) '' F) = F := by
    ext f
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      simpa [hc] using hg
    · intro hf
      refine ⟨fun x => c * f x, ⟨f, hf, rfl⟩, ?_⟩
      funext x
      simp [hc]
  have henv : (fun x => |c⁻¹| * (|c| * Φ x)) = Φ := by
    funext x
    simp [abs_inv, hc]
  have hrev := normalizedL2CoveringNumber_smul_le Q
    ((fun f : Ω → ℝ => fun x => c * f x) '' F)
    (fun x => |c| * Φ x) c⁻¹ ε (inv_ne_zero hc)
  rw [hclass, henv] at hrev
  exact hrev

omit [MeasurableSpace Ω] in
/-- Simultaneously scaling a class and its envelope by a nonzero scalar leaves
the normalized uniform covering number unchanged. -/
lemma uniformL2CoveringNumber_smul
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (c ε : ℝ) (hc : c ≠ 0) :
    uniformL2CoveringNumber
        ((fun f : Ω → ℝ => fun x => c * f x) '' F)
        (fun x => |c| * Φ x) ε =
      uniformL2CoveringNumber F Φ ε := by
  unfold uniformL2CoveringNumber
  apply le_antisymm
  · refine iSup_le fun Q => ?_
    exact (normalizedL2CoveringNumber_smul Q F Φ c ε hc).le.trans
      (le_iSup (fun Q' : FiniteDiscreteProbability Ω =>
        normalizedL2CoveringNumber Q' F Φ ε) Q)
  · refine iSup_le fun Q => ?_
    exact (normalizedL2CoveringNumber_smul Q F Φ c ε hc).ge.trans
      (le_iSup (fun Q' : FiniteDiscreteProbability Ω =>
        normalizedL2CoveringNumber Q'
          ((fun f : Ω → ℝ => fun x => c * f x) '' F)
          (fun x => |c| * Φ x) ε) Q)

omit [MeasurableSpace Ω] in
/-- The uniform covering entropy integral vanishes at a nonpositive endpoint. -/
lemma uniformCoveringEntropyIntegral_of_nonpos
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) {δ : ℝ} (hδ : δ ≤ 0) :
    uniformCoveringEntropyIntegral δ F Φ = 0 := by
  simp [uniformCoveringEntropyIntegral, Set.Ioc_eq_empty (not_lt.mpr hδ)]

omit [MeasurableSpace Ω] in
/-- The uniform covering entropy integral is monotone in its upper endpoint. -/
lemma uniformCoveringEntropyIntegral_mono_delta
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) {δ₁ δ₂ : ℝ}
    (hδ : δ₁ ≤ δ₂) :
    uniformCoveringEntropyIntegral δ₁ F Φ ≤
      uniformCoveringEntropyIntegral δ₂ F Φ := by
  unfold uniformCoveringEntropyIntegral
  exact lintegral_mono_set (Set.Ioc_subset_Ioc_right hδ)

private lemma uniformCovering_iUnion_dyadic_Ioc_eq {δ : ℝ} (hδ : 0 < δ) :
    ⋃ q : ℕ, Set.Ioc ((1 / 2 : ℝ) ^ (q + 1) * δ) ((1 / 2 : ℝ) ^ q * δ) =
      Set.Ioc 0 δ := by
  have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hapos : ∀ q : ℕ, 0 < (1 / 2 : ℝ) ^ q * δ := fun q => by positivity
  apply Set.eq_of_subset_of_subset
  · intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ioc] at hx
    obtain ⟨q, hlo, hhi⟩ := hx
    refine ⟨lt_trans (hapos (q + 1)) hlo, hhi.trans ?_⟩
    calc
      (1 / 2 : ℝ) ^ q * δ ≤ 1 * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ.le
        exact pow_le_one₀ hhalf_pos.le (by norm_num)
      _ = δ := one_mul δ
  · intro x hx
    simp only [Set.mem_Ioc] at hx
    obtain ⟨hx0, hxδ⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    have hexists : ∃ q : ℕ, (1 / 2 : ℝ) ^ q * δ < x := by
      obtain ⟨q, hq⟩ := exists_pow_lt_of_lt_one
        (by positivity : (0 : ℝ) < x / δ) (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨q, (lt_div_iff₀ hδ).mp hq⟩
    classical
    let q₀ := Nat.find hexists
    have hq₀ : (1 / 2 : ℝ) ^ q₀ * δ < x := Nat.find_spec hexists
    have hq₀_pos : 1 ≤ q₀ := by
      rcases Nat.eq_zero_or_pos q₀ with hzero | hpos
      · exfalso
        rw [hzero] at hq₀
        simp only [pow_zero, one_mul] at hq₀
        exact (not_lt.mpr hxδ) hq₀
      · exact hpos
    obtain ⟨p, hp⟩ : ∃ p, q₀ = p + 1 := ⟨q₀ - 1, by omega⟩
    have hprev : ¬(1 / 2 : ℝ) ^ p * δ < x :=
      Nat.find_min hexists (by omega : p < q₀)
    refine ⟨p, ?_, not_lt.mp hprev⟩
    rw [hp] at hq₀
    exact hq₀

omit [MeasurableSpace Ω] in
private lemma uniformCovering_dyadic_term_le
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
        entropyWeight (uniformL2CoveringNumber F Φ ((1 / 2 : ℝ) ^ q * δ)) ≤
      2 * ∫⁻ ε in Set.Ioc ((1 / 2 : ℝ) ^ (q + 1) * δ)
          ((1 / 2 : ℝ) ^ q * δ),
        entropyWeight (uniformL2CoveringNumber F Φ ε) ∂volume := by
  set aq : ℝ := (1 / 2 : ℝ) ^ q * δ with haq
  set aq1 : ℝ := (1 / 2 : ℝ) ^ (q + 1) * δ with haq1
  have haq_pos : 0 < aq := by rw [haq]; positivity
  have haq1_eq : aq1 = (1 / 2 : ℝ) * aq := by rw [haq1, haq]; ring
  have hconst_le :
      ∫⁻ _ε in Set.Ioc aq1 aq,
          entropyWeight (uniformL2CoveringNumber F Φ aq) ∂volume ≤
        ∫⁻ ε in Set.Ioc aq1 aq,
          entropyWeight (uniformL2CoveringNumber F Φ ε) ∂volume := by
    refine setLIntegral_mono' measurableSet_Ioc (fun ε hε => ?_)
    exact entropyWeight_mono
      (uniformL2CoveringNumber_antitone_eps F Φ hε.2)
  rw [setLIntegral_const, Real.volume_Ioc] at hconst_le
  have hlen : aq - aq1 = (1 / 2 : ℝ) * aq := by rw [haq1_eq]; ring
  rw [hlen] at hconst_le
  have hsplit : ENNReal.ofReal aq =
      2 * ENNReal.ofReal ((1 / 2 : ℝ) * aq) := by
    rw [← ENNReal.ofReal_ofNat (n := 2),
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  calc
    ENNReal.ofReal aq * entropyWeight (uniformL2CoveringNumber F Φ aq) =
        2 * (entropyWeight (uniformL2CoveringNumber F Φ aq) *
          ENNReal.ofReal ((1 / 2 : ℝ) * aq)) := by rw [hsplit]; ring
    _ ≤ 2 * ∫⁻ ε in Set.Ioc aq1 aq,
        entropyWeight (uniformL2CoveringNumber F Φ ε) ∂volume := by gcongr

omit [MeasurableSpace Ω] in
theorem uniformCovering_dyadic_sum_le_entropyIntegral
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∑' q : ℕ,
        ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
          entropyWeight
            (uniformL2CoveringNumber F Φ
              ((1 / 2 : ℝ) ^ q * δ)) ≤
      2 * uniformCoveringEntropyIntegral δ F Φ := by
  set I : ℕ → Set ℝ := fun q =>
    Set.Ioc ((1 / 2 : ℝ) ^ (q + 1) * δ) ((1 / 2 : ℝ) ^ q * δ) with hI
  have hI_meas : ∀ q, MeasurableSet (I q) := fun _ => measurableSet_Ioc
  have hscale_anti : ∀ {m n : ℕ}, m ≤ n →
      (1 / 2 : ℝ) ^ n * δ ≤ (1 / 2 : ℝ) ^ m * δ := by
    intro m n hmn
    apply mul_le_mul_of_nonneg_right _ hδ.le
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hI_disj : Pairwise (Function.onFun Disjoint I) := by
    intro m n hmn
    wlog hlt : m < n generalizing m n
    · exact (this hmn.symm (by omega)).symm
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    simp only [hI, Set.mem_Ioc] at hxm hxn
    have hx : x ≤ (1 / 2 : ℝ) ^ (m + 1) * δ :=
      hxn.2.trans (hscale_anti (by omega))
    exact (not_lt.mpr hx) hxm.1
  calc
    ∑' q : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
        entropyWeight (uniformL2CoveringNumber F Φ ((1 / 2 : ℝ) ^ q * δ)) ≤
      ∑' q : ℕ, 2 * ∫⁻ ε in I q,
        entropyWeight (uniformL2CoveringNumber F Φ ε) ∂volume :=
      ENNReal.tsum_le_tsum (fun q => uniformCovering_dyadic_term_le F Φ hδ q)
    _ = 2 * ∑' q : ℕ, ∫⁻ ε in I q,
        entropyWeight (uniformL2CoveringNumber F Φ ε) ∂volume := by
      rw [ENNReal.tsum_mul_left]
    _ = 2 * ∫⁻ ε in ⋃ q, I q,
        entropyWeight (uniformL2CoveringNumber F Φ ε) ∂volume := by
      rw [lintegral_iUnion hI_meas hI_disj]
    _ = 2 * uniformCoveringEntropyIntegral δ F Φ := by
      unfold uniformCoveringEntropyIntegral
      rw [hI, uniformCovering_iUnion_dyadic_Ioc_eq hδ]

omit [MeasurableSpace Ω] in
theorem uniformL2CoveringNumber_dyadic_ne_top_of_entropyIntegral_ne_top
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ)
    {δ : ℝ} (hδ : 0 < δ)
    (hJ : uniformCoveringEntropyIntegral δ F Φ ≠ ⊤)
    (q : ℕ) :
    uniformL2CoveringNumber F Φ
      ((1 / 2 : ℝ) ^ q * δ) ≠ ⊤ := by
  intro htop
  have hcoeff : ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hterm :
      ENNReal.ofReal ((1 / 2 : ℝ) ^ q * δ) *
          entropyWeight
            (uniformL2CoveringNumber F Φ ((1 / 2 : ℝ) ^ q * δ)) = ⊤ := by
    rw [htop, entropyWeight_top, ENNReal.mul_top hcoeff]
  have hsum_ne :
      (∑' k : ℕ,
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k * δ) *
          entropyWeight
            (uniformL2CoveringNumber F Φ
              ((1 / 2 : ℝ) ^ k * δ))) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) hJ)
      (uniformCovering_dyadic_sum_le_entropyIntegral F Φ hδ)
  exact hsum_ne (ENNReal.tsum_eq_top_of_eq_top ⟨q, hterm⟩)

/-- The empirical finite-discrete representation places every normalized empirical
cover below the uniform covering number, as required by sample-`L²` chaining. -/
theorem empirical_normalizedCoveringNumber_le_uniform
    {n : ℕ} [NeZero n] (X : Fin n → Ω)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (ε : ℝ) :
    ∃ Q : FiniteDiscreteProbability Ω,
      Q.measure = empiricalMeasure n X ∧
      (∀ f : Ω → ℝ,
        Q.l2Seminorm f = Real.sqrt (empiricalAvg (fun x => |f x| ^ 2) n X)) ∧
      normalizedL2CoveringNumber Q F Φ ε ≤
        uniformL2CoveringNumber F Φ ε := by
  obtain ⟨Q, hQ, hL2⟩ := FiniteDiscreteProbability.exists_empirical_adapter X
  exact ⟨Q, hQ, hL2, normalizedL2CoveringNumber_le_uniform Q F Φ ε⟩

end AsymptoticStatistics.EmpiricalProcess
