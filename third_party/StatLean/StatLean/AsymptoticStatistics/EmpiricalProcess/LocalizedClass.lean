module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.PointwiseDense
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Localization foundations for the §19.2 chaining argument

The (unrestricted and localized) **difference classes**
`F − F := {f − g : f, g ∈ F}` and
`F_{δq} := {f − g : f, g ∈ F, ‖f − g‖_{L²(P)} ≤ δq}`, their elementary
membership facts, and the bracketing-entropy-integral proportionality for the
difference class (vdV Lemma 19.31).

These definitions lie below both the Donsker-via-bracketing assembly
(`DonskerBracketing.lean`) and the localized chaining bound
(`ChainingAssembly.lean`), so both modules can use them without a cyclic
dependency.

vdV §19.2 chaining localization; vdV Lemma 19.31.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal Filter
open scoped ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Localization foundations (vdV §19.2 chaining localization)

The vdV §19.2 chaining proof of asymptotic equicontinuity localizes to the
shrinking **difference slice** `F_{δq} := {f − g : f, g ∈ F, ‖f − g‖_{L²(P)} ≤ δq}`
(the class of differences with small `L²(P)`-radius), and bounds the maximal
empirical-process oscillation over it by the bracketing-entropy integral of the
full difference class `F − F`. These definitions name those two classes and
record their elementary membership facts; the entropy wrapper at the end ties
the `F − F` entropy to `F`'s own entropy via vdV Lemma 19.31. -/

/-- The **(unrestricted) difference class** `F − F := {f − g : f, g ∈ F}`.

This is the index set of the localized empirical process in the vdV §19.2
chaining argument before the `L²`-radius restriction is imposed; its bracketing
entropy is controlled by `F`'s via vdV Lemma 19.31
(`hasFiniteBracketingCover_difference_class`). The set-builder shape matches the
inline form used by that lemma. -/
def differenceClass (F : Set (Ω → ℝ)) : Set (Ω → ℝ) :=
  {h : Ω → ℝ | ∃ f g, f ∈ F ∧ g ∈ F ∧ h = fun x => f x - g x}

omit [MeasurableSpace Ω] in
/-- **Envelope of the difference class.** If `Φ` is an envelope for `F`
(`|f x| ≤ Φ x` for every `f ∈ F`), then `2Φ` is an envelope for the difference
class `differenceClass F = {f − g : f, g ∈ F}`: for `h = f − g`,
`|h x| = |f x − g x| ≤ |f x| + |g x| ≤ Φ x + Φ x = 2 Φ x` (`abs_sub`). -/
lemma isEnvelope_differenceClass_two {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    (hΦ : IsEnvelope F Φ) : IsEnvelope (differenceClass F) (fun x => 2 * Φ x) := by
  rintro h ⟨f, g, hf, hg, rfl⟩ x
  calc |f x - g x| ≤ |f x| + |g x| := abs_sub (f x) (g x)
    _ ≤ Φ x + Φ x := by gcongr <;> [exact hΦ f hf x; exact hΦ g hg x]
    _ = 2 * Φ x := by ring

/-- The **localized difference class** `F_{δq} := {f − g : f, g ∈ F,
‖f − g‖_{L²(P)} ≤ δq}` — the differences `f − g` of class members whose
`L²(P)`-radius is at most `δq`.

This is the shrinking slice the vdV §19.2 chaining argument localizes to:
the bad event `{‖fhat n − ghat n‖_{L²(P)} > δq}` is pushed to `μ`-measure 0 by
the `L²`-consistency hypothesis, and on its complement the random pair
`(fhat n ξ − ghat n ξ)` lands in `localizedDifferenceClass F P δq`, where the
maximal-inequality bound applies. -/
def localizedDifferenceClass (F : Set (Ω → ℝ)) (P : Measure Ω) (δq : ℝ) :
    Set (Ω → ℝ) :=
  {h : Ω → ℝ | ∃ f ∈ F, ∃ g ∈ F,
      h = (fun x => f x - g x) ∧ eLpNorm h 2 P ≤ ENNReal.ofReal δq}

/-- **L1 (membership ⇒ radius bound).** Every `h ∈ localizedDifferenceClass F P δq`
has `L²(P)`-radius at most `δq`. Immediate from the radius conjunct of the
membership predicate. -/
lemma localizedDifferenceClass_hF_L2 {F : Set (Ω → ℝ)} {P : Measure Ω} {δq : ℝ}
    {h : Ω → ℝ} (hh : h ∈ localizedDifferenceClass F P δq) :
    eLpNorm h 2 P ≤ ENNReal.ofReal δq := by
  obtain ⟨_f, _hf, _g, _hg, _heq, hradius⟩ := hh
  exact hradius

/-- **L1′ (localized slice ⊆ full difference class).** Forgetting the radius
restriction lands in `differenceClass F`. The cover-lift / entropy bounds are
stated for `differenceClass F`, so the localized slice inherits them by
monotonicity (`bracketingEntropyIntegral_mono_class`). -/
lemma localizedDifferenceClass_subset {F : Set (Ω → ℝ)} {P : Measure Ω} {δq : ℝ} :
    localizedDifferenceClass F P δq ⊆ differenceClass F := by
  rintro h ⟨f, hf, g, hg, heq, _⟩
  exact ⟨f, g, hf, hg, heq⟩

/-- **L2 (`eLpNorm`-form membership).** A difference `f − g` of class members
whose `L²(P)`-radius is `≤ δq` lies in `localizedDifferenceClass F P δq`. This is
the def-native form (matching the `eLpNorm` radius spelling used by the bracket
lemmas, e.g. `chain_head_dyadic_bound`'s `hF_L2`). -/
lemma mem_localizedDifferenceClass {F : Set (Ω → ℝ)} {P : Measure Ω} {δq : ℝ}
    {f g : Ω → ℝ} (hf : f ∈ F) (hg : g ∈ F)
    (hradius : eLpNorm (fun x => f x - g x) 2 P ≤ ENNReal.ofReal δq) :
    (fun x => f x - g x) ∈ localizedDifferenceClass F P δq :=
  ⟨f, hf, g, hg, rfl, hradius⟩

/-- **`eLpNorm`–`∫·²` bridge for the `L²`-good event.** For `MemLp f 2 P`,
`(eLpNorm f 2 P).toReal = √(∫ f²)`. Proved inline (rather than importing the
`ForMathlib.QMDAnalytic` clone) to keep the `EmpiricalProcess` import graph
self-contained; same `MemLp.eLpNorm_eq_integral_rpow_norm` derivation. -/
private lemma sqrt_integral_sq_eq_eLpNorm_toReal' {P : Measure Ω} {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    Real.sqrt (∫ ω, f ω ^ 2 ∂P) = (eLpNorm f 2 P).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have h_int_eq :
      (fun ω => ‖f ω‖ ^ (2 : ℝ≥0∞).toReal) = (fun ω => f ω ^ 2) := by
    funext ω
    rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h_int_eq]
  have h_int_nn : 0 ≤ ∫ ω, f ω ^ 2 ∂P :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _), h2, Real.sqrt_eq_rpow]
  norm_num

/-- **L2′ (`∫·²`-form membership).** The form the consumer in `Maximal.lean`
(~l.1786) produces: the `L²`-good event is stated as `∫ x, (f x − g x)² ∂P < δq²`.
Bridged to the `eLpNorm` radius via `sqrt_integral_sq_eq_eLpNorm_toReal'`, which
needs `MemLp (f − g) 2 P` (without it the Bochner integral of a non-`L²` square
is `0` and the implication fails). The `<` good event gives `≤ δq` after `√`. -/
lemma mem_localizedDifferenceClass_of_integral_sq {F : Set (Ω → ℝ)} {P : Measure Ω}
    {δq : ℝ} (hδq : 0 ≤ δq) {f g : Ω → ℝ} (hf : f ∈ F) (hg : g ∈ F)
    (hmem : MemLp (fun x => f x - g x) 2 P)
    (hgood : ∫ x, (f x - g x) ^ 2 ∂P < δq ^ 2) :
    (fun x => f x - g x) ∈ localizedDifferenceClass F P δq := by
  refine mem_localizedDifferenceClass hf hg ?_
  -- Bridge `∫(f−g)² < δq²` to `eLpNorm (f−g) 2 P ≤ ofReal δq`.
  -- `(eLpNorm (f−g) 2 P).toReal = √(∫(f−g)²) ≤ √(δq²) = δq`, then back to `ℝ≥0∞`.
  have htoReal : (eLpNorm (fun x => f x - g x) 2 P).toReal
      = Real.sqrt (∫ x, (f x - g x) ^ 2 ∂P) :=
    (sqrt_integral_sq_eq_eLpNorm_toReal' hmem).symm
  have hsqrt_le : Real.sqrt (∫ x, (f x - g x) ^ 2 ∂P) ≤ δq := by
    calc Real.sqrt (∫ x, (f x - g x) ^ 2 ∂P)
        ≤ Real.sqrt (δq ^ 2) := Real.sqrt_le_sqrt hgood.le
      _ = δq := by rw [Real.sqrt_sq hδq]
  have htoReal_le : (eLpNorm (fun x => f x - g x) 2 P).toReal ≤ δq := by
    rw [htoReal]; exact hsqrt_le
  -- Lift `toReal ≤ δq` to `· ≤ ofReal δq` using finiteness of the L² norm.
  rw [← ENNReal.ofReal_toReal hmem.eLpNorm_lt_top.ne]
  exact ENNReal.ofReal_le_ofReal htoReal_le

/-- **vdV Lemma 19.31, raw-cover-data core**.

The size-`k → k²` cover-lifting map: a concrete size-`k` `(η/2)`-bracketing
cover of `F` (raw `Fin k`-indexed data, **not** the size-quantified
`HasFiniteBracketingCover` predicate) is lifted to a concrete size-`k * k`
`η`-bracketing cover of the difference class `differenceClass F`, via the
pairing `[l_i - u_j, u_i - l_j]` indexed by `Fin (k * k)` through
`finProdFinEquiv`.

This raw-data form is exactly the `hlift` hypothesis of
`bracketingEntropyIntegral_diff_le` (`Bracketing.lean`), which feeds the lift the
*minimal* cover at each scale and reads off the size-`k²` output to bound the
bracketing number; the size `k * k` must therefore be preserved syntactically
(the `HasFiniteBracketingCover` wrapper would hide it behind an existential).
`hasFiniteBracketingCover_difference_class` is the predicate-level wrapper. -/
private lemma cover_lift_difference_class
    {F : Set (Ω → ℝ)} {P : Measure Ω} {η : ℝ} (hη : 0 < η) (k : ℕ)
    (h : ∃ l u : Fin k → Ω → ℝ,
        (∀ i, IsEpsBracket (η / 2) (l i) (u i) 2 P) ∧
        (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)) :
    ∃ l u : Fin (k * k) → Ω → ℝ,
        (∀ i, IsEpsBracket η (l i) (u i) 2 P) ∧
        (∀ hd ∈ differenceClass F, ∃ i, ∀ x, l i x ≤ hd x ∧ hd x ≤ u i x) := by
  -- vdV Lemma 19.31. Pair the `(η/2)`-brackets of `F` into `η`-brackets of
  -- `F - F` via `[l_i - u_j, u_i - l_j]`, indexed by `Fin (k * k)` through
  -- `finProdFinEquiv`. Algebra: `(u_i - l_j) - (l_i - u_j) =
  -- (u_i - l_i) + (u_j - l_j)`; triangle in L² gives the η bound.
  obtain ⟨l, u, hbr, hcov⟩ := h
  have hη2 : (0 : ℝ) ≤ η / 2 := by linarith
  refine ⟨
    fun ij x => l (finProdFinEquiv.symm ij).1 x - u (finProdFinEquiv.symm ij).2 x,
    fun ij x => u (finProdFinEquiv.symm ij).1 x - l (finProdFinEquiv.symm ij).2 x,
    ?_, ?_⟩
  · -- each pair `[l i - u j, u i - l j]` is an η-bracket in L²(P)
    intro ij
    set p := finProdFinEquiv.symm ij
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      have h1 := (hbr p.1).isBracket x
      have h2 := (hbr p.2).isBracket x
      linarith
    · exact (hbr p.1).measurable_lower.sub (hbr p.2).measurable_upper
    · exact (hbr p.1).measurable_upper.sub (hbr p.2).measurable_lower
    · exact (hbr p.1).memLp_lower.sub (hbr p.2).memLp_upper
    · exact (hbr p.1).memLp_upper.sub (hbr p.2).memLp_lower
    · -- size bound: triangle + the two (η/2)-bracket bounds
      have hexpand :
          (fun x => (u p.1 x - l p.2 x) - (l p.1 x - u p.2 x)) =
          (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) := by
        funext x; ring
      rw [hexpand]
      have hmeas1 : AEStronglyMeasurable (fun x => u p.1 x - l p.1 x) P :=
        ((hbr p.1).memLp_upper.sub (hbr p.1).memLp_lower).aestronglyMeasurable
      have hmeas2 : AEStronglyMeasurable (fun x => u p.2 x - l p.2 x) P :=
        ((hbr p.2).memLp_upper.sub (hbr p.2).memLp_lower).aestronglyMeasurable
      have htri : eLpNorm (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) 2 P ≤
          eLpNorm (fun x => u p.1 x - l p.1 x) 2 P +
            eLpNorm (fun x => u p.2 x - l p.2 x) 2 P :=
        eLpNorm_add_le hmeas1 hmeas2 one_le_two
      have hi : eLpNorm (fun x => u p.1 x - l p.1 x) 2 P < ENNReal.ofReal (η / 2) :=
        (hbr p.1).size_lt
      have hj : eLpNorm (fun x => u p.2 x - l p.2 x) 2 P < ENNReal.ofReal (η / 2) :=
        (hbr p.2).size_lt
      have hsum :
          ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add hη2 hη2]
        congr 1; ring
      calc eLpNorm (fun x => (u p.1 x - l p.1 x) + (u p.2 x - l p.2 x)) 2 P
          ≤ eLpNorm (fun x => u p.1 x - l p.1 x) 2 P +
              eLpNorm (fun x => u p.2 x - l p.2 x) 2 P := htri
        _ < ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := ENNReal.add_lt_add hi hj
        _ = ENNReal.ofReal η := hsum
  · -- cover: every `hd = f - g` lies in some bracket `[l i - u j, u i - l j]`
    rintro hd ⟨f, g, hf, hg, h_eq⟩
    obtain ⟨i, hfi⟩ := hcov f hf
    obtain ⟨j, hgj⟩ := hcov g hg
    refine ⟨finProdFinEquiv (i, j), fun x => ?_⟩
    simp only [Equiv.symm_apply_apply, h_eq]
    refine ⟨?_, ?_⟩
    · have h1 := (hfi x).1
      have h2 := (hgj x).2
      linarith
    · have h1 := (hfi x).2
      have h2 := (hgj x).1
      linarith

/-- **vdV Lemma 19.31: bracketing of the difference class**.

If `F` has a finite `(η/2)`-bracketing cover in `L²(P)`, then the
**difference class** `differenceClass F = F - F := {f - g : f, g ∈ F}` has a
finite `η`-bracketing cover in `L²(P)`.

The textbook construction (vdV §19.5): for each pair `(i, j)`
of brackets `[l_i, u_i]`, `[l_j, u_j]` from the `(η/2)`-cover of `F`,
the pair `[l_i - u_j, u_i - l_j]` brackets `f - g` whenever `f ∈ [l_i,
u_i]` and `g ∈ [l_j, u_j]`. Its L² size is
`‖(u_i - l_j) - (l_i - u_j)‖_2 = ‖(u_i - l_i) + (u_j - l_j)‖_2 ≤
η/2 + η/2 = η`. Predicate-level wrapper over `cover_lift_difference_class`. -/
private lemma hasFiniteBracketingCover_difference_class
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    {η : ℝ} (hη : 0 < η)
    (hF : HasFiniteBracketingCover F (η / 2) 2 P) :
    HasFiniteBracketingCover (differenceClass F) η 2 P := by
  obtain ⟨k, hk⟩ := hF
  obtain ⟨l', u', hbr', hcov'⟩ := cover_lift_difference_class hη k hk
  exact ⟨k * k, l', u', hbr', hcov'⟩

/-- **Number-level difference-class bracketing bound** (vdV Lemma 19.31, raw count):
`N_{[]}(η, F − F, L²(P)) ≤ N_{[]}(η/2, F, L²(P))²`.  Number-level companion of
`bracketingEntropyIntegral_diff_le_class`.  Public wrapper feeding the relative-bracketing
shell bound (`shell_localizedDiff_bracketingNumber_le`); must live here because the
size-`k → k*k` cover lift `cover_lift_difference_class` is `private` to this file. -/
lemma bracketingNumber_differenceClass_le_sq
    {F : Set (Ω → ℝ)} {P : Measure Ω} {η : ℝ} (hη : 0 < η)
    (hcover : HasFiniteBracketingCover F (η / 2) 2 P) :
    bracketingNumber η (differenceClass F) 2 P ≤ (bracketingNumber (η / 2) F 2 P) ^ 2 :=
  bracketingNumber_le_sq_of_cover_lift hcover (fun k hk => cover_lift_difference_class hη k hk)

/-- **L4 wrapper: entropy-integral proportionality for the difference class.**

Instantiates the abstract `bracketingEntropyIntegral_diff_le` (`Bracketing.lean`)
at the concrete difference class `G = differenceClass F`, supplying the
cover-lifting hypothesis from `cover_lift_difference_class` (vdV Lemma 19.31's
raw `k → k²` map). Conclusion:
`J_{[]}(δ, F − F, L²(P)) ≤ 2√2 · J_{[]}(δ, F, L²(P))`.

The `2√2` factor decomposes as `√2` (cost of squaring the count, vdV Lemma 19.31
`N(η, F−F) ≤ N(η/2, F)²`) times `2` (the Jacobian of the `ε ↦ ε/2` scale change
folded into the entropy integral). The hypothesis `hcover` (`F` has a finite
`(ε/2)`-bracketing cover at every scale) is the genuine class input; under
`bracketingEntropyIntegral 1 F P < ⊤` it is discharged at the needed scales by
`hasFiniteBracketingCover_of_entropyIntegral_lt_top` (`Bracketing.lean`), so the
downstream localization consumer supplies it from `h_int`, not as a standing
hypothesis. -/
lemma bracketingEntropyIntegral_diff_le_class
    {F : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F (ε / 2) 2 P) :
    bracketingEntropyIntegral δ (differenceClass F) P
      ≤ ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δ F P :=
  bracketingEntropyIntegral_diff_le hδ hcover
    (fun _ε hε k hk => cover_lift_difference_class hε k hk)

/-! ## Pointwise-density closure of the difference class (S6)

This reusable closure remains available to consumers that need VW pointwise density.
The finite-entropy localized chaining bounds derive the measurability they use directly
from class-member measurability and therefore carry no pointwise-density hypothesis. -/

/-- **S6: difference-class closure of pointwise density.** If `F` is VW
pointwise-dense (`EmpProcPointwiseDense`), so is its difference class
`differenceClass F = {f − g : f, g ∈ F}`.

Construction (mirrors `EmpProcPointwiseDense`'s three clauses):

* **separant** `F'' = differenceClass F'` (the difference set of `F`'s countable
  separant `F'`); countable as the `Set.image2`-subtraction of `F' × F'`, and
  `⊆ differenceClass F` since `F' ⊆ F`;
* **density**: each `h = f − g ∈ differenceClass F` (with `f, g ∈ F`) has
  approximating `φ_k → f`, `ψ_k → g` in `F'`; then `φ_k − ψ_k → f − g` pointwise
  (`Tendsto.sub`) with each `φ_k − ψ_k ∈ F''`;
* **dominator** `2Φ`: `Integrable (2 · Φ) P` (`Integrable.const_mul`), and for
  `h = f − g ∈ differenceClass F`, `|h x| = |f x − g x| ≤ |f x| + |g x| ≤ 2 Φ x`
  (`abs_sub`). -/
theorem EmpProcPointwiseDense_differenceClass {F : Set (Ω → ℝ)} {P : Measure Ω}
    (h : EmpProcPointwiseDense F P) :
    EmpProcPointwiseDense (differenceClass F) P := by
  obtain ⟨F', hF'sub, hF'ct, hApprox, Φ, hΦ_int, hΦ_dom⟩ := h
  -- separant: the difference set of `F'`
  refine ⟨differenceClass F', ?_, ?_, ?_, ?_⟩
  · -- `differenceClass F' ⊆ differenceClass F` since `F' ⊆ F`
    rintro h' ⟨f', g', hf', hg', rfl⟩
    exact ⟨f', g', hF'sub hf', hF'sub hg', rfl⟩
  · -- countable: image of `F' × F'` under subtraction
    have : differenceClass F'
        = Set.image2 (fun f' g' => fun x => f' x - g' x) F' F' := by
      ext h'
      constructor
      · rintro ⟨f', g', hf', hg', rfl⟩; exact ⟨f', hf', g', hg', rfl⟩
      · rintro ⟨f', hf', g', hg', rfl⟩; exact ⟨f', g', hf', hg', rfl⟩
    rw [this]
    exact hF'ct.image2 hF'ct _
  · -- density: `f − g` approximated by `φ_k − ψ_k`
    rintro h' ⟨f, g, hf, hg, rfl⟩
    obtain ⟨φ, hφmem, hφlim⟩ := hApprox f hf
    obtain ⟨ψ, hψmem, hψlim⟩ := hApprox g hg
    refine ⟨fun m x => φ m x - ψ m x, fun m => ?_, fun x => ?_⟩
    · exact ⟨φ m, ψ m, hφmem m, hψmem m, rfl⟩
    · exact (hφlim x).sub (hψlim x)
  · -- dominator `2Φ`
    refine ⟨fun x => 2 * Φ x, hΦ_int.const_mul 2, ?_⟩
    rintro h' ⟨f, g, hf, hg, rfl⟩ x
    calc |f x - g x| ≤ |f x| + |g x| := abs_sub (f x) (g x)
      _ ≤ Φ x + Φ x := by gcongr <;> [exact hΦ_dom f hf x; exact hΦ_dom g hg x]
      _ = 2 * Φ x := by ring

end AsymptoticStatistics.EmpiricalProcess
