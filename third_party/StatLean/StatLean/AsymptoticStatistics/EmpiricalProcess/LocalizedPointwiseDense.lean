module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedClass
public import StatLean.AsymptoticStatistics.ForMathlib.LpDominatedConvergence

@[expose] public section

/-!
# Pointwise density for strict localized difference classes

The strict `L²(P)` slice of a difference class inherits pointwise density from
the original class.  Strict localization is essential: `L²` convergence of
the approximating differences then puts a tail of the sequence inside the
same slice.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Differences of members of `F` whose `L²(P)` seminorm is strictly below
`r`.  The strict inequality makes this class stable under sufficiently close
`L²` approximation. -/
def strictLocalizedDifferenceClass
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (P : Measure Ω) (r : ℝ) : Set (Ω → ℝ) :=
  {h | ∃ f ∈ F, ∃ g ∈ F,
    h = (fun x => f x - g x) ∧
      eLpNorm h 2 P < ENNReal.ofReal r}

/-- Forgetting the strict radius restriction leaves an unrestricted
difference of two class members. -/
theorem strictLocalizedDifferenceClass_subset_differenceClass
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (P : Measure Ω) (r : ℝ) :
    strictLocalizedDifferenceClass F P r ⊆ differenceClass F := by
  rintro h ⟨f, hf, g, hg, heq, -⟩
  exact ⟨f, g, hf, hg, heq⟩

/-- A nonempty class contributes its zero self-difference to every strictly
positive localized slice. -/
theorem zero_mem_strictLocalizedDifferenceClass
    {Ω : Type*} [MeasurableSpace Ω]
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    (hF : F.Nonempty) {r : ℝ} (hr : 0 < r) :
    (fun _ : Ω => 0) ∈ strictLocalizedDifferenceClass F P r := by
  obtain ⟨f, hf⟩ := hF
  refine ⟨f, hf, f, hf, by funext x; simp, ?_⟩
  simpa using ENNReal.ofReal_pos.2 hr

/-- Pointwise density passes to the strict localized difference class.

Approximate both endpoints through the original countable separant.  Dominated
convergence gives `L²` convergence of their differences, and strictness of the
target radius places a tail of those differences back in the localized slice. -/
theorem EmpProcPointwiseDense_strictLocalizedDifferenceClass
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hΦ : IsEnvelope F Φ)
    (hΦ_memLp : MemLp Φ 2 P)
    (r : ℝ) :
    EmpProcPointwiseDense (strictLocalizedDifferenceClass F P r) P := by
  obtain ⟨F', hF'sub, hF'ct, hApprox, -⟩ := hDense
  refine ⟨strictLocalizedDifferenceClass F' P r, ?_, ?_, ?_, ?_⟩
  · rintro h ⟨f, hf, g, hg, heq, hr⟩
    exact ⟨f, hF'sub hf, g, hF'sub hg, heq, hr⟩
  · have hdiff_count : (differenceClass F').Countable := by
      rw [show differenceClass F' =
          Set.image2 (fun f g => fun x => f x - g x) F' F' by
        ext h
        constructor
        · rintro ⟨f, g, hf, hg, rfl⟩
          exact ⟨f, hf, g, hg, rfl⟩
        · rintro ⟨f, hf, g, hg, rfl⟩
          exact ⟨f, g, hf, hg, rfl⟩]
      exact hF'ct.image2 hF'ct _
    exact hdiff_count.mono
      (strictLocalizedDifferenceClass_subset_differenceClass F' P r)
  · rintro h ⟨f, hf, g, hg, rfl, hr⟩
    obtain ⟨φ, hφmem, hφlim⟩ := hApprox f hf
    obtain ⟨ψ, hψmem, hψlim⟩ := hApprox g hg
    have hΦ_nonneg : ∀ x, 0 ≤ Φ x := fun x =>
      (abs_nonneg (f x)).trans (hΦ f hf x)
    have hdom_memLp : MemLp (fun x => 2 * Φ x) 2 P := by
      simpa [smul_eq_mul] using hΦ_memLp.const_mul 2
    have hL2 : Tendsto
        (fun m => eLpNorm
          (fun x => (φ m x - ψ m x) - (f x - g x)) 2 P)
        atTop (𝓝 0) :=
      tendsto_eLpNorm_sub_zero_of_pointwise_of_memLp_dominator P
        (fun m => ((hF_meas _ (hF'sub (hφmem m))).sub
          (hF_meas _ (hF'sub (hψmem m)))).aestronglyMeasurable)
        hdom_memLp
        (fun m x => by
          rw [Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (by norm_num) (hΦ_nonneg x))]
          calc
            |φ m x - ψ m x| ≤ |φ m x| + |ψ m x| := abs_sub _ _
            _ ≤ Φ x + Φ x := by
              gcongr
              · exact hΦ _ (hF'sub (hφmem m)) x
              · exact hΦ _ (hF'sub (hψmem m)) x
            _ = 2 * Φ x := by ring)
        (fun x => (hφlim x).sub (hψlim x))
    have hclose : ∀ᶠ m in atTop,
        eLpNorm (fun x => (φ m x - ψ m x) - (f x - g x)) 2 P <
          ENNReal.ofReal r - eLpNorm (fun x => f x - g x) 2 P :=
      hL2.eventually_lt_const (tsub_pos_of_lt hr)
    have hlocal : ∀ᶠ m in atTop,
        (fun x => φ m x - ψ m x) ∈
          strictLocalizedDifferenceClass F' P r := by
      filter_upwards [hclose] with m hm
      refine ⟨φ m, hφmem m, ψ m, hψmem m, rfl, ?_⟩
      calc
        eLpNorm (fun x => φ m x - ψ m x) 2 P =
            eLpNorm (fun x =>
              ((φ m x - ψ m x) - (f x - g x)) + (f x - g x)) 2 P := by
              congr 2
              funext x
              ring
        _ ≤ eLpNorm (fun x => (φ m x - ψ m x) - (f x - g x)) 2 P +
            eLpNorm (fun x => f x - g x) 2 P := by
              apply eLpNorm_add_le
              · exact (((hF_meas _ (hF'sub (hφmem m))).sub
                  (hF_meas _ (hF'sub (hψmem m)))).sub
                    ((hF_meas _ hf).sub (hF_meas _ hg))).aestronglyMeasurable
              · exact ((hF_meas _ hf).sub (hF_meas _ hg)).aestronglyMeasurable
              · norm_num
        _ < (ENNReal.ofReal r - eLpNorm (fun x => f x - g x) 2 P) +
            eLpNorm (fun x => f x - g x) 2 P :=
              ENNReal.add_lt_add_right
                (lt_of_lt_of_le hr le_top).ne hm
        _ = ENNReal.ofReal r := tsub_add_cancel_of_le hr.le
    obtain ⟨N, hN⟩ := eventually_atTop.1 hlocal
    refine ⟨fun m x => φ (m + N) x - ψ (m + N) x, ?_, ?_⟩
    · intro m
      exact hN (m + N) (Nat.le_add_left N m)
    · intro x
      exact ((hφlim x).sub (hψlim x)).comp (tendsto_add_atTop_nat N)
  · refine ⟨fun x => 2 * Φ x, ?_, ?_⟩
    · exact (memLp_one_iff_integrable.mp
        (hΦ_memLp.mono_exponent (by norm_num))).const_mul 2
    · rintro h ⟨f, hf, g, hg, rfl, -⟩ x
      calc
        |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
        _ ≤ Φ x + Φ x := by gcongr <;> [exact hΦ f hf x; exact hΦ g hg x]
        _ = 2 * Φ x := by ring

end AsymptoticStatistics.EmpiricalProcess
