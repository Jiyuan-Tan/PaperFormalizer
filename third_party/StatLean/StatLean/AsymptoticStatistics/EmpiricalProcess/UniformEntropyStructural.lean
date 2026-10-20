module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation

@[expose] public section

/-!
# Structural uniform covering entropy

This file isolates the definitions used by van der Vaart Theorems 19.13 and
19.14.  Covering radii are relative to an explicit nonnegative envelope, and
the supremum ranges only over probability measures for which the outer
envelope norm is positive and finite.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, p.274.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

namespace UniformEntropyStructural

/-- A class is pointwise measurable when it has a countable skeleton from
which every class member is obtained as a pointwise sequential limit.

This is the sufficient interpretation of “suitably measurable” given after
vdV Theorem 19.14. Edge behavior: the empty class has the empty skeleton. -/
def IsPointwiseMeasurable (F : Set (Ω → ℝ)) : Prop :=
  ∃ F₀ : Set (Ω → ℝ), F₀.Countable ∧ F₀ ⊆ F ∧
    ∀ f ∈ F, ∃ g : ℕ → (Ω → ℝ), (∀ n, g n ∈ F₀) ∧
      ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (f x))

/-- A nonnegative envelope for a real-valued function class.

This definition records nonnegativity even when `F` is empty. This makes the
zero-envelope branch explicit. Edge behavior: `G = 0` envelopes exactly the
classes whose members vanish pointwise. -/
def IsEnvelope (F : Set (Ω → ℝ)) (G : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ G x) ∧ ∀ f ∈ F, ∀ x, |f x| ≤ G x

/-- The outer `Lʳ(Q)` norm used in vdV's uniform covering numbers.

It is defined from outer expectation, so no measurability of the argument is
silently assumed. Edge behavior: at `r = 0` the reciprocal exponent is zero;
all book-facing theorems restrict to `1 ≤ r`. -/
noncomputable def outerLpNorm (Q : Measure Ω) (f : Ω → ℝ) (r : ℝ) : ℝ≥0∞ :=
  (outerExpectation Q (fun x => ENNReal.ofReal |f x| ^ r)) ^ r⁻¹

/-- An admissible measure in a uniform covering supremum.

Constitutive (vdV §19.2 p.274): `Q` is a probability measure and the envelope
has positive finite outer `Lʳ(Q)` norm. Thus zero- and infinite-norm laws are
excluded. For `r > 0`, zero norm means that the envelope is `Q`-almost
everywhere zero, not that it is pointwise identically zero. -/
def IsAdmissibleMeasure (G : Ω → ℝ) (r : ℝ) (Q : Measure Ω) : Prop :=
  IsProbabilityMeasure Q ∧ 0 < outerLpNorm Q G r ∧ outerLpNorm Q G r < ⊤

/-- A finite strict relative `Lʳ(Q)` cover of `F` at scale `ε`.

Every center belongs to `Lʳ(Q)`. The radius is `ε * ‖G‖*_{Q,r}` and the ball
inequality is strict. Edge behavior: the empty finset covers the empty class. -/
def IsStrictFiniteLpCover (F : Set (Ω → ℝ)) (G : Ω → ℝ) (Q : Measure Ω)
    (r ε : ℝ) (S : Finset (Ω → ℝ)) : Prop :=
  (∀ g ∈ S, MemLp g (ENNReal.ofReal r) Q) ∧
    ∀ f ∈ F, ∃ g ∈ S,
      outerLpNorm Q (f - g) r < ENNReal.ofReal ε * outerLpNorm Q G r

/-- The strict relative `Lʳ(Q)` covering number, valued in `ℕ∞`.

It is the infimum of cardinalities of finite strict covers. Edge behavior: it
is `0` for the empty class and `⊤` when no finite cover exists. -/
noncomputable def finiteLpCoveringNumber (F : Set (Ω → ℝ)) (G : Ω → ℝ)
    (Q : Measure Ω) (r ε : ℝ) : ℕ∞ :=
  ⨅ (S : Finset (Ω → ℝ)) (_ : IsStrictFiniteLpCover F G Q r ε S),
    (S.card : ℕ∞)

/-- The uniform relative `Lʳ` covering number.

The supremum ranges only over admissible probability measures. Edge behavior:
if there is no admissible measure (in particular for the zero envelope), the
supremum is the bottom element `0`. -/
noncomputable def uniformLpCoveringNumber (F : Set (Ω → ℝ)) (G : Ω → ℝ)
    (r ε : ℝ) : ℕ∞ :=
  ⨆ (Q : Measure Ω), ⨆ (_hQ : IsAdmissibleMeasure G r Q),
    finiteLpCoveringNumber F G Q r ε

/-- The uniform entropy integral
`∫₀^δ √log(1 + sup_Q N(ε ‖G‖_{Q,r}, F, Lʳ(Q))) dε`.

Edge behavior: a zero or negative upper endpoint gives the integral over the
empty interval; an infinite covering number contributes `⊤` through
`entropyWeight`. -/
noncomputable def uniformEntropyIntegral (δ : ℝ) (F : Set (Ω → ℝ))
    (G : Ω → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 δ, entropyWeight (uniformLpCoveringNumber F G r ε) ∂volume

/-- Any concrete strict finite cover bounds the corresponding covering number. -/
theorem finiteLpCoveringNumber_le_of_cover {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    {Q : Measure Ω} {r ε : ℝ} {S : Finset (Ω → ℝ)}
    (hS : IsStrictFiniteLpCover F G Q r ε S) :
    finiteLpCoveringNumber F G Q r ε ≤ (S.card : ℕ∞) := by
  unfold finiteLpCoveringNumber
  exact iInf_le_of_le S (iInf_le_of_le hS le_rfl)

/-- Covering numbers are antitone in the radius. -/
theorem finiteLpCoveringNumber_antitone_eps {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    {Q : Measure Ω} {r ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    finiteLpCoveringNumber F G Q r ε₂ ≤ finiteLpCoveringNumber F G Q r ε₁ := by
  unfold finiteLpCoveringNumber
  refine le_iInf fun S => le_iInf fun hS => ?_
  refine iInf_le_of_le S (iInf_le_of_le ?_ le_rfl)
  refine ⟨hS.1, ?_⟩
  intro f hf
  obtain ⟨g, hgS, hfg⟩ := hS.2 f hf
  exact ⟨g, hgS, hfg.trans_le (mul_le_mul_left (ENNReal.ofReal_le_ofReal hε) _)⟩

/-- Uniform covering numbers are antitone in the radius. -/
theorem uniformLpCoveringNumber_antitone_eps {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    {r ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    uniformLpCoveringNumber F G r ε₂ ≤ uniformLpCoveringNumber F G r ε₁ := by
  unfold uniformLpCoveringNumber
  refine iSup_le fun Q => iSup_le fun hQ => ?_
  exact le_iSup_of_le Q (le_iSup_of_le hQ (finiteLpCoveringNumber_antitone_eps hε))

/-- Restricting a class cannot increase its uniform covering number when the
same envelope is retained. -/
theorem uniformLpCoveringNumber_mono_class {F₁ F₂ : Set (Ω → ℝ)} {G : Ω → ℝ}
    {r ε : ℝ} (hF : F₁ ⊆ F₂) :
    uniformLpCoveringNumber F₁ G r ε ≤ uniformLpCoveringNumber F₂ G r ε := by
  unfold uniformLpCoveringNumber
  refine iSup_le fun Q => iSup_le fun hQ => ?_
  refine le_iSup_of_le Q (le_iSup_of_le hQ ?_)
  unfold finiteLpCoveringNumber
  refine le_iInf fun S => le_iInf fun hS => ?_
  refine iInf_le_of_le S (iInf_le_of_le ?_ le_rfl)
  exact ⟨hS.1, fun f hf => hS.2 f (hF hf)⟩

/-- The empty class has uniform covering number zero. -/
theorem uniformLpCoveringNumber_empty (G : Ω → ℝ) (r ε : ℝ) :
    uniformLpCoveringNumber (∅ : Set (Ω → ℝ)) G r ε = 0 := by
  apply le_antisymm
  · unfold uniformLpCoveringNumber
    refine iSup_le fun Q => iSup_le fun _hQ => ?_
    refine (finiteLpCoveringNumber_le_of_cover (S := ∅) ?_).trans ?_
    · constructor
      · simp
      · intro f hf
        exact (Set.notMem_empty f hf).elim
    · simp
  · exact bot_le

/-- A zero envelope has no admissible measure and hence uniform covering
number zero. -/
theorem uniformLpCoveringNumber_zeroEnvelope (F : Set (Ω → ℝ)) (r ε : ℝ)
    (hr : 0 < r) : uniformLpCoveringNumber F (fun _ => 0) r ε = 0 := by
  have hzero (Q : Measure Ω) : outerLpNorm Q (fun _ => 0) r = 0 := by
    simp [outerLpNorm, ENNReal.zero_rpow_of_pos hr,
      ENNReal.zero_rpow_of_pos (inv_pos.mpr hr), outerExpectation_const]
  apply le_antisymm
  · unfold uniformLpCoveringNumber
    refine iSup_le fun Q => iSup_le fun hQ => ?_
    rw [IsAdmissibleMeasure, hzero Q] at hQ
    exact (not_lt_of_ge le_rfl hQ.2.1).elim
  · exact bot_le

end UniformEntropyStructural

end AsymptoticStatistics.EmpiricalProcess
