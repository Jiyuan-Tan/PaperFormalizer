module
public import StatLean.Bayesian.MCMC.Defs

@[expose] public section

/-!
# Metropolis–Hastings correctness: reversibility and stationarity

Correctness of the Metropolis–Hastings kernel on a countable state space (Gelman §11.2):

* the kernel is **Markov** (2F.2): acceptance mass plus rejection mass is one;
* **detailed balance** (2F.3): `π{x}·K(x, {y}) = π{y}·K(y, {x})` — in kernel form,
  `Kernel.IsReversible (mhKernel π q) π`;
* **stationarity** (2F.1/2F.4): reversibility implies invariance, `π·K = π`, loaded from the
  pinned `Kernel.IsReversible.invariant`.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §11.2
(Metropolis and Metropolis–Hastings), p. 278.

**Proof formalization notes.** The pointwise engine is the symmetry lemma `mhAccept_mul_symm`
(`π{x}·q(x,{y})·α(x,y) = π{y}·q(y,{x})·α(y,x)`), an `ℝ≥0∞` computation via the helper
`c · min 1 (d/c) = min c d` (case-split `c ∈ {0, ∞}`; masses are finite for finite `π` and Markov
`q`). Reversibility integrates it over `A × B` with `lintegral_countable'`-style indicator sums
(`ENNReal.tsum_comm` for the swap); the rejection part is diagonal-supported and symmetric by
construction. Stationarity is the pinned `IsReversible.invariant` — the textbook-named wrapper
`invariant_of_isReversible` (2F.1) records Gelman's phrasing; we load, not reprove.

**Bibliographic comments.** Metropolis et al. (1953) introduced the symmetric-proposal algorithm
for statistical mechanics; Hastings (1970) the general ratio used here. That detailed balance
(reversibility) suffices for stationarity is the classical reversible-chain argument (A. N.
Kolmogorov's reversibility criterion, 1936), with the convergence theory (irreducibility, Harris
recurrence, ergodic theorems) deferred to Meyn–Tweedie-style analysis outside this batch's scope.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {S : Type*} [mS : MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]

/-- `ℝ≥0∞` helper: `c · min 1 (d/c) = min c d` for finite `c` (both sides `0` at `c = 0`). -/
theorem mul_min_one_div {c d : ℝ≥0∞}
    -- LEAN-ONLY: finiteness of the reference mass (holds for finite `π`, Markov `q`)
    (hc : c ≠ ∞) :
    c * min 1 (d / c) = min c d := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  · rw [mul_min, mul_one,
      ENNReal.mul_div_cancel' (fun h => absurd h hc0) (fun h => absurd h hc)]

/-- **The MH kernel is Markov** (2F.2): acceptance mass plus rejection mass is one. -/
theorem isMarkovKernel_mhKernel (π : Measure S) (q : Kernel S S) [IsMarkovKernel q] :
    IsMarkovKernel (mhKernel π q) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have ht : (∫⁻ y, mhAccept π q x y ∂(q x)) ≤ 1 := by
    calc ∫⁻ y, mhAccept π q x y ∂(q x)
        ≤ ∫⁻ _, 1 ∂(q x) := lintegral_mono (fun y => min_le_left _ _)
      _ = 1 := by rw [lintegral_one, measure_univ]
  rw [mhKernel_apply, Measure.add_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one,
    add_tsub_cancel_of_le ht]

/-- Pointwise detailed balance of the acceptance flow:
`π{x}·q(x,{y})·α(x,y) = π{y}·q(y,{x})·α(y,x)`. -/
theorem mhAccept_mul_symm (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    [IsMarkovKernel q] (x y : S) :
    π {x} * (q x {y} * mhAccept π q x y) = π {y} * (q y {x} * mhAccept π q y x) := by
  have ha : π {x} * q x {y} ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top (q x) _)
  have hb : π {y} * q y {x} ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top π _) (measure_ne_top (q y) _)
  unfold mhAccept
  rw [← mul_assoc, ← mul_assoc, mul_min_one_div ha, mul_min_one_div hb, min_comm]

/-- Symmetry of the acceptance flow between two measurable sets: the discrete double sum of
`π{x}·q(x,{y})·α(x,y)` over `A × B` is symmetric under swapping `A` and `B`, by the pointwise
`mhAccept_mul_symm` and Fubini for `ℝ≥0∞`-tsums. -/
private theorem accFlow_symm (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    [IsMarkovKernel q] {A B : Set S} :
    ∫⁻ x in A, (∫⁻ y in B, mhAccept π q x y ∂(q x)) ∂π
      = ∫⁻ x in B, (∫⁻ y in A, mhAccept π q x y ∂(q x)) ∂π := by
  have inner : ∀ (x : S) (C : Set S),
      ∫⁻ y in C, mhAccept π q x y ∂(q x) = ∑' y : C, mhAccept π q x (y : S) * q x {(y : S)} :=
    fun x C => lintegral_countable _ C.to_countable
  simp_rw [inner]
  rw [lintegral_countable (fun x => ∑' y : B, mhAccept π q x (y : S) * q x {(y : S)})
      A.to_countable,
    lintegral_countable (fun x => ∑' y : A, mhAccept π q x (y : S) * q x {(y : S)})
      B.to_countable]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun b => tsum_congr fun a => ?_
  have h := mhAccept_mul_symm π q (a : S) (b : S)
  calc mhAccept π q (a : S) (b : S) * q (a : S) {(b : S)} * π {(a : S)}
      = π {(a : S)} * (q (a : S) {(b : S)} * mhAccept π q (a : S) (b : S)) := by ring
    _ = π {(b : S)} * (q (b : S) {(a : S)} * mhAccept π q (b : S) (a : S)) := h
    _ = mhAccept π q (b : S) (a : S) * q (b : S) {(a : S)} * π {(b : S)} := by ring

/-- Symmetry of the rejection flow: the diagonal-supported rejection mass is symmetric, since both
sides equal the integral of the rejection probability over `A ∩ B`. -/
private theorem rejFlow_symm (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, (1 - ∫⁻ y, mhAccept π q x y ∂(q x)) * (Measure.dirac x B) ∂π
      = ∫⁻ x in B, (1 - ∫⁻ y, mhAccept π q x y ∂(q x)) * (Measure.dirac x A) ∂π := by
  have key : ∀ (C D : Set S), MeasurableSet C → MeasurableSet D →
      ∫⁻ x in C, (1 - ∫⁻ y, mhAccept π q x y ∂(q x)) * (Measure.dirac x D) ∂π
        = ∫⁻ x in C ∩ D, (1 - ∫⁻ y, mhAccept π q x y ∂(q x)) ∂π := by
    intro C D hC hD
    rw [← lintegral_indicator hC, ← lintegral_indicator (hC.inter hD)]
    refine lintegral_congr fun x => ?_
    by_cases hxC : x ∈ C <;> by_cases hxD : x ∈ D <;>
      simp [Measure.dirac_apply' _ hD, hxC, hxD, Set.mem_inter_iff]
  rw [key A B hA hB, key B A hB hA, Set.inter_comm]

/-- **Metropolis–Hastings detailed balance** (2F.3; Gelman §11.2): the MH
kernel is reversible with respect to its target. -/
theorem isReversible_mhKernel (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    [IsMarkovKernel q] :
    Kernel.IsReversible (mhKernel π q) π := by
  intro A B hA hB
  have hval : ∀ (C : Set S), MeasurableSet C → ∀ (x : S),
      mhKernel π q x C
        = (∫⁻ y in C, mhAccept π q x y ∂(q x))
          + (1 - ∫⁻ y, mhAccept π q x y ∂(q x)) * (Measure.dirac x C) := by
    intro C hC x
    rw [mhKernel_apply, Measure.add_apply, withDensity_apply _ hC, Measure.smul_apply,
      smul_eq_mul]
  simp_rw [hval B hB, hval A hA]
  rw [lintegral_add_left Measurable.of_discrete, lintegral_add_left Measurable.of_discrete,
    accFlow_symm π q, rejFlow_symm π q hA hB]

/-- **Detailed balance implies stationarity** (2F.1; Gelman §11.2) — textbook-named
wrapper of the pinned `Kernel.IsReversible.invariant`. -/
theorem invariant_of_isReversible {κ : Kernel S S} [IsMarkovKernel κ] {π : Measure S}
    -- USER-INPUT: detailed balance of the chain; Gelman §11.2
    (h : Kernel.IsReversible κ π) :
    Kernel.Invariant κ π :=
  h.invariant

/-- **Metropolis–Hastings stationarity** (2F.4; Gelman §11.2): the target is invariant
for the MH kernel. -/
theorem invariant_mhKernel (π : Measure S) [IsFiniteMeasure π] (q : Kernel S S)
    [IsMarkovKernel q] :
    Kernel.Invariant (mhKernel π q) π := by
  haveI := isMarkovKernel_mhKernel π q
  exact (isReversible_mhKernel π q).invariant

end StatLean.Bayesian
