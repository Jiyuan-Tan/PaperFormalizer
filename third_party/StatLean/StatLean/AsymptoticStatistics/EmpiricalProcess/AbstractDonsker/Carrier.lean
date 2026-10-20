module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalProcess
public import StatLean.AsymptoticStatistics.EmpiricalProcess.FunctionClass
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Bracketing
public import Mathlib.Analysis.Normed.Lp.lpSpace

@[expose] public section

/-!
# The carrier `ℓ∞(F)` and the empirical process as an `ℓ∞(F)`-valued map

The abstract-Donsker theory (van der Vaart, *Asymptotic Statistics* §18.1, §19.2;
van der Vaart–Wellner, *Weak Convergence and Empirical Processes* Ch. 2) views
the empirical process `𝔾ₙ : f ↦ √n · (Pₙ f − P f)` as a single random element of
the space `ℓ∞(F)` of **bounded** real functions on the index set `↥F`, equipped
with the supremum norm. Weak convergence of `𝔾ₙ` in `ℓ∞(F)` (in the
van der Vaart–Wellner outer sense `⇝ₒ`) to a tight `P`-Brownian-bridge limit is
the literal statement of `F` being a `P`-Donsker class.

## Main definitions

* `LinfF F` — the carrier `ℓ∞(F) = lp (fun _ : ↥F => ℝ) ∞` (bounded functions on
  `↥F`, sup norm). Carries a `PseudoMetricSpace` (from `lp.normedAddCommGroup`
  via `fact_one_le_top_ennreal`) and the Borel `MeasurableSpace`.
* `empiricalProcessLinf X hmem` — the empirical process `f ↦ 𝔾ₙ f` packaged as an
  element of `LinfF F` (membership supplied by `memℓp_empiricalProcess`).
* `distL2 P f g` — the `L²(P)` (semi)distance `(eLpNorm (f − g) 2 P).toReal`, the
  intrinsic semimetric on `F` for the asymptotic-equicontinuity side.

## Main results

* `memℓp_empiricalProcess` — when `F` has an integrable envelope, the function
  `f ↦ 𝔾ₙ f` is `ℓ∞`-bounded (the bound `√n · (Pₙ|G| + P|G|)` is **uniform in
  `f`**), hence a genuine element of `ℓ∞(F)`.
* `totallyBounded_L2` — under a finite bracketing-entropy integral, `F` is totally
  bounded in the `L²(P)` semimetric (the precompactness input the limit needs).

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §18.1, §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The carrier **`ℓ∞(F)`**: bounded real-valued functions on the index set `↥F`,
equipped with the supremum norm `lp … ∞`.

Membership `Memℓp z ∞` unfolds to `BddAbove (Set.range fun i => ‖z i‖)`
(`memℓp_infty_iff`); on the real fibres `‖·‖ = |·|`. The `NormedAddCommGroup`
(hence `PseudoMetricSpace`) instance comes from `lp.normedAddCommGroup` via
`fact_one_le_top_ennreal : Fact ((1 : ℝ≥0∞) ≤ ∞)`.

vdV §18.1 / van der Vaart–Wellner Ch. 2.1: the empirical process as a random
element of `ℓ∞(F)`. -/
abbrev LinfF (F : Set (Ω → ℝ)) : Type _ := lp (fun _ : ↥F => ℝ) ∞

/-- Borel `σ`-algebra on the carrier `ℓ∞(F)`, induced by its sup-norm topology.
`lp` does not auto-carry a `MeasurableSpace`, so we install the Borel one (the
standard choice for weak-convergence statements). -/
noncomputable instance instMeasurableSpaceLinfF (F : Set (Ω → ℝ)) :
    MeasurableSpace (LinfF F) := borel _

instance instBorelSpaceLinfF (F : Set (Ω → ℝ)) :
    BorelSpace (LinfF F) := ⟨rfl⟩

/-- **Uniform `ℓ∞`-boundedness of the empirical process.** When `F` has an
envelope `G ∈ L¹(P)`, the map `f ↦ 𝔾ₙ f` on `↥F` is bounded in sup norm, so it
is a genuine element of `ℓ∞(F)`.

Key point (the "bounded over an infinite index" item): the bound
`√n · (Pₙ|G| + P|G|)` is **uniform in `f`** — no interchange of `sup` and limit
is needed. Pointwise `|f| ≤ G` gives `|Pf| ≤ P|G|` (monotonicity of the integral)
and `|Pₙ f| ≤ Pₙ|G|`, whence `|𝔾ₙ f| = √n·|Pₙf − Pf| ≤ √n·(Pₙ|G| + P|G|)`. -/
lemma memℓp_empiricalProcess {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF_env : ∃ G, IsEnvelope F G ∧ Integrable G P) {n : ℕ} (X : Fin n → Ω) :
    Memℓp (fun f : ↥F => empiricalProcess P n X (f : Ω → ℝ)) ∞ := by
  obtain ⟨G, hG_env, hG_int⟩ := hF_env
  -- The uniform bound `B = √n · (empiricalAvg |G| n X + ∫ |G| dP)`.
  set B : ℝ := Real.sqrt n * (empiricalAvg (fun x => |G x|) n X + ∫ x, |G x| ∂P) with hB
  refine memℓp_infty ⟨B, ?_⟩
  rintro _ ⟨f, rfl⟩
  -- `‖𝔾ₙ f‖ = |𝔾ₙ f| ≤ B`, uniformly in `f`.
  simp only [Real.norm_eq_abs]
  -- `|f x| ≤ G x ≤ |G x|` pointwise (envelope), hence the average/integral bounds.
  have hf_le : ∀ x, |f.1 x| ≤ G x := hG_env f.1 f.2
  have hf_le_abs : ∀ x, |f.1 x| ≤ |G x| := fun x => (hf_le x).trans (le_abs_self _)
  -- `|empiricalAvg f| ≤ empiricalAvg |G|`.
  have hPn : |empiricalAvg (f : Ω → ℝ) n X| ≤ empiricalAvg (fun x => |G x|) n X := by
    unfold empiricalAvg
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |∑ i, (f : Ω → ℝ) (X i)| ≤ ∑ i, |(f : Ω → ℝ) (X i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |G (X i)| := Finset.sum_le_sum (fun i _ => hf_le_abs (X i))
  -- `|∫ f dP| ≤ ∫ |G| dP`. We split on whether `f` is integrable; if not, the
  -- Bochner integral is `0` by convention and the bound is trivial. This avoids
  -- needing a measurability hypothesis on `f`.
  have hG_abs_int : Integrable (fun x => |G x|) P := hG_int.abs
  have hP : |∫ x, (f : Ω → ℝ) x ∂P| ≤ ∫ x, |G x| ∂P := by
    by_cases hf_int : Integrable (f : Ω → ℝ) P
    · calc |∫ x, (f : Ω → ℝ) x ∂P| ≤ ∫ x, |(f : Ω → ℝ) x| ∂P :=
            abs_integral_le_integral_abs
        _ ≤ ∫ x, |G x| ∂P :=
            integral_mono hf_int.abs hG_abs_int (fun x => hf_le_abs x)
    · rw [integral_undef hf_int, abs_zero]
      exact integral_nonneg (fun x => (abs_nonneg _).trans (hf_le_abs x))
  -- Combine.
  unfold empiricalProcess
  rw [hB, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  calc |empiricalAvg (f : Ω → ℝ) n X - ∫ x, (f : Ω → ℝ) x ∂P|
        ≤ |empiricalAvg (f : Ω → ℝ) n X| + |∫ x, (f : Ω → ℝ) x ∂P| := abs_sub _ _
    _ ≤ empiricalAvg (fun x => |G x|) n X + ∫ x, |G x| ∂P := add_le_add hPn hP

/-- The empirical process `f ↦ 𝔾ₙ f` packaged as an element of the carrier
`ℓ∞(F)`. The `ℓ∞`-membership is supplied as an argument (produced by
`memℓp_empiricalProcess` from an integrable envelope). -/
noncomputable def empiricalProcessLinf {F : Set (Ω → ℝ)} {P : Measure Ω} {n : ℕ}
    (X : Fin n → Ω)
    (hmem : Memℓp (fun f : ↥F => empiricalProcess P n X (f : Ω → ℝ)) ∞) :
    LinfF F :=
  ⟨fun f => empiricalProcess P n X (f : Ω → ℝ), hmem⟩

/-- The **`L²(P)` (semi)distance** between two functions:
`distL2 P f g = (eLpNorm (f − g) 2 P).toReal`. This is the intrinsic semimetric
`ρ_P(f, g) = (P(f − g)²)^{1/2}` of van der Vaart §19.2, in which the
asymptotic-equicontinuity / total-boundedness conditions are stated. -/
noncomputable def distL2 (P : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  (eLpNorm (f - g) 2 P).toReal

/-- **Total boundedness of `F` in the `L²(P)` semimetric.** A finite
bracketing-entropy integral forces a finite ε-bracketing cover at every scale,
which yields a finite ε-net for `distL2 P`, i.e. `F` is totally bounded in
`L²(P)`. This is the precompactness input the tight limit `G_P` is concentrated
on.

Stated directly as an **ε-net** condition in the `distL2 P` semimetric (avoiding
committing to a `UniformSpace` instance on the subtype `↥F`): for every `ε > 0`
there is a finite subset `S ⊆ F` such that every `f ∈ F` is within `ε` of some
`g ∈ S`. This is the `Metric.totallyBounded_iff` content of "`F` totally bounded
in `L²(P)`", in the form used in Theorem 18.14. (vdV §19.2.) -/
lemma totallyBounded_L2 {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : bracketingEntropyIntegral 1 F P < ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Ω → ℝ), (↑S ⊆ F) ∧
      ∀ f ∈ F, ∃ g ∈ S, distL2 P f g < ε := by
  classical
  intro ε hε
  -- Step 1: extract a finite `ε`-bracketing cover at this scale.
  obtain ⟨k, l, u, hbr, hcov⟩ :=
    hasFiniteBracketingCover_of_entropyIntegral_lt_top hF hε
  -- The indices `i : Fin k` whose bracket actually contains some element of `F`.
  set Q : Fin k → Prop := fun i => ∃ f, f ∈ F ∧ ∀ x, l i x ≤ f x ∧ f x ≤ u i x with hQ
  -- For each such index pick a representative `rep i ∈ F` lying in bracket `i`.
  have hrep : ∀ i, Q i → ∃ g, g ∈ F ∧ ∀ x, l i x ≤ g x ∧ g x ≤ u i x := fun i hi => hi
  let rep : Fin k → (Ω → ℝ) := fun i =>
    if hi : Q i then (hrep i hi).choose else (0 : Ω → ℝ)
  -- The net = the representatives of the covering brackets.
  refine ⟨(Finset.univ.filter Q).image rep, ?_, ?_⟩
  · -- `S ⊆ F`: every representative lies in `F`.
    intro g hg
    simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ,
      true_and, Set.mem_image, Set.mem_setOf_eq] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    simp only [rep, dif_pos hi]
    exact (hrep i hi).choose_spec.1
  · -- ε-net bound.
    intro f hf
    -- `f` lies in some bracket `i`.
    obtain ⟨i, hi_cov⟩ := hcov f hf
    -- Bracket `i` is a covering bracket (it contains `f ∈ F`), so it has a rep.
    have hQi : Q i := ⟨f, hf, hi_cov⟩
    refine ⟨rep i, ?_, ?_⟩
    · -- `rep i ∈ S`.
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨i, hQi, rfl⟩
    · -- `distL2 P f (rep i) < ε`.
      -- `rep i` lies in the same bracket `i`.
      have hrep_spec : ∀ x, l i x ≤ rep i x ∧ rep i x ≤ u i x := by
        simp only [rep, dif_pos hQi]
        exact (hrep i hQi).choose_spec.2
      -- Pointwise: `|f x - rep i x| ≤ u i x - l i x`.
      have h_ptwise : ∀ x, ‖(f - rep i) x‖ ≤ ‖(fun y => u i y - l i y) x‖ := by
        intro x
        have hl_f := (hi_cov x).1
        have hf_u := (hi_cov x).2
        have hl_r := (hrep_spec x).1
        have hr_u := (hrep_spec x).2
        simp only [Pi.sub_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ u i x - l i x)]
        rw [abs_sub_le_iff]
        constructor <;> linarith
      -- Hence `eLpNorm (f - rep i) 2 P ≤ eLpNorm (u i - l i) 2 P < ofReal ε`.
      have h_eLp_le : eLpNorm (f - rep i) 2 P ≤ eLpNorm (fun y => u i y - l i y) 2 P :=
        eLpNorm_mono h_ptwise
      have h_size : eLpNorm (fun y => u i y - l i y) 2 P < ENNReal.ofReal ε :=
        (hbr i).size_lt
      have h_lt : eLpNorm (f - rep i) 2 P < ENNReal.ofReal ε :=
        lt_of_le_of_lt h_eLp_le h_size
      -- Transfer to the real-valued `distL2`.
      exact ENNReal.toReal_lt_of_lt_ofReal h_lt

/-- **`L²`-membership of every `f ∈ F` under an `L²` envelope.** If `F` has an
envelope `G ∈ L²(P)` and every member of `F` is `(P-a.e.) strongly measurable`,
then each `f ∈ F` is itself in `L²(P)`. The bound `|f x| ≤ G x` (`IsEnvelope`)
dominated by `G ∈ L²` gives `MemLp f 2 P` via `MemLp.mono'`.

The measurability hypothesis `hF_meas` is genuinely required: `IsEnvelope` is a
pointwise size bound and carries no measurability of `F`'s members, while
`MemLp.mono'` needs `AEStronglyMeasurable f P`. In vdV, `F` is a class of
measurable functions. -/
lemma memLp_of_mem_F {F : Set (Ω → ℝ)} {P : Measure Ω} {G : Ω → ℝ}
    (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    {f : Ω → ℝ} (hf : f ∈ F) : MemLp f 2 P :=
  hG.mono' (hF_meas f hf).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hG_env f hf x)

/-- `distL2 P f f = 0`: the `L²` distance of a function to itself vanishes
(`eLpNorm 0 = 0`). -/
lemma distL2_self {P : Measure Ω} (f : Ω → ℝ) : distL2 P f f = 0 := by
  unfold distL2
  rw [sub_self, eLpNorm_zero, ENNReal.toReal_zero]

/-- `distL2 P f g = distL2 P g f`: symmetry, from `eLpNorm (f - g) = eLpNorm (g - f)`. -/
lemma distL2_comm {P : Measure Ω} (f g : Ω → ℝ) : distL2 P f g = distL2 P g f := by
  unfold distL2
  rw [eLpNorm_sub_comm]

/-- **Triangle inequality for `distL2` from direct `L²` membership.**

For any three `L²(P)` functions, the `L²(P)` semidistance satisfies
`distL2 P f h ≤ distL2 P f g + distL2 P g h`.  This is the carrier-independent
form used when one endpoint is only in the `L²(P)` closure of a function class.

The `ℝ≥0∞`-level triangle inequality `eLpNorm_add_le` (using
`AEStronglyMeasurable` of the summands and `1 ≤ 2`) transfers to `.toReal` because
both summands are finite by `MemLp`, so `ENNReal.toReal_add` is additive and
`ENNReal.toReal_mono` is monotone. -/
lemma distL2_triangle_of_memLp {P : Measure Ω} {f g h : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) (hh : MemLp h 2 P) :
    distL2 P f h ≤ distL2 P f g + distL2 P g h := by
  unfold distL2
  -- Finiteness of all three `eLpNorm`s, from `L²`-membership.
  have hfg_ne : eLpNorm (f - g) 2 P ≠ ⊤ := (hf.sub hg).eLpNorm_ne_top
  have hgh_ne : eLpNorm (g - h) 2 P ≠ ⊤ := (hg.sub hh).eLpNorm_ne_top
  -- `ℝ≥0∞` triangle inequality: `eLpNorm (f - h) ≤ eLpNorm (f - g) + eLpNorm (g - h)`.
  have h_tri : eLpNorm (f - h) 2 P ≤ eLpNorm (f - g) 2 P + eLpNorm (g - h) 2 P := by
    have hfh_eq : f - h = (f - g) + (g - h) := by ring
    rw [hfh_eq]
    exact eLpNorm_add_le
      (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)
      (hg.aestronglyMeasurable.sub hh.aestronglyMeasurable) (by norm_num)
  -- Transfer to `.toReal`: monotone (RHS finite) + additive (both summands finite).
  rw [← ENNReal.toReal_add hfg_ne hgh_ne]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfg_ne, hgh_ne⟩) h_tri

/-- **Triangle inequality for `distL2` on an enveloped class.** For `f, g, h ∈ F`
with an `L²` envelope and measurable members,
`distL2 P f h ≤ distL2 P f g + distL2 P g h`. -/
lemma distL2_triangle {F : Set (Ω → ℝ)} {P : Measure Ω} {G : Ω → ℝ}
    (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    {f g h : Ω → ℝ} (hf : f ∈ F) (hg : g ∈ F) (hh : h ∈ F) :
    distL2 P f h ≤ distL2 P f g + distL2 P g h :=
  distL2_triangle_of_memLp
    (memLp_of_mem_F hG_env hG hF_meas hf)
    (memLp_of_mem_F hG_env hG hF_meas hg)
    (memLp_of_mem_F hG_env hG hF_meas hh)

/-- The **`distL2` pseudometric on the subtype `↥F`.** Under an `L²` envelope and
measurability of `F`'s members, `distL2 P f.1 g.1` is a genuine pseudometric on
`↥F` (the self / symmetry / triangle axioms are `distL2_self` / `distL2_comm` /
`distL2_triangle`). The `edist`, uniformity and bornology are left to the
`PseudoMetricSpace.mk` defaults derived from `dist`.

This is a `def` (not a global `instance`) because it depends on the hypotheses
`hG_env`, `hG`, and `hF_meas`. -/
@[reducible]
noncomputable def distL2PseudoMetric {F : Set (Ω → ℝ)} {P : Measure Ω} {G : Ω → ℝ}
    (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f) :
    PseudoMetricSpace (↥F) where
  dist f g := distL2 P f.1 g.1
  dist_self f := distL2_self f.1
  dist_comm f g := distL2_comm f.1 g.1
  dist_triangle f g h := distL2_triangle hG_env hG hF_meas f.2 g.2 h.2

end AsymptoticStatistics.EmpiricalProcess
