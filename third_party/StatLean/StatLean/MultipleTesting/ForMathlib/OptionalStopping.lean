module
public import Mathlib.Probability.Martingale.OptionalStopping

@[expose] public section

/-!
# Optional stopping for supermartingales — `ForMathlib` layer (Optimal Stopping Theorem discharge)

Theorem-agnostic bricks (pure math, Mathlib-only). **Reference.** Junwei Lu, *Big Data Analysis*,
Springer Nature Switzerland, 2025 (ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off),
§21.3 (Knock-Off), Theorem 21.1 (Optimal Stopping Theorem): for a bounded stopping time `τ`,
`E[Xτ] = E[X₀]` if `X` is a martingale, and `E[Xτ] ≤ E[X₀]` if `X` is a supermartingale.

Mathlib already proves the submartingale optional-stopping inequality
`MeasureTheory.Submartingale.expected_stoppedValue_mono`
(`∫ stoppedValue f τ ≤ ∫ stoppedValue f π` for stopping times `τ ≤ π` with `π` bounded). We
**bridge**, not reprove: dualizing to supermartingales (via `Supermartingale.neg`) and
specializing the earlier stopping time to the constant `0` gives the two book statements below,
in the exact form the knock-off proof (`Knockoff.lean`) consumes.
-/

open MeasureTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
  {𝒢 : Filtration ℕ m0} [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → ℝ}

/-- Optional stopping, supermartingale monotonicity: for stopping times `τ ≤ π` with `π` bounded,
the *later* stopped value has the *smaller* integral. Dual of
`MeasureTheory.Submartingale.expected_stoppedValue_mono`. -/
theorem supermartingale_expected_stoppedValue_antitone
    {τ π : Ω → ℕ∞} (hf : Supermartingale f 𝒢 μ)
    (hτ : IsStoppingTime 𝒢 τ) (hπ : IsStoppingTime 𝒢 π) (hle : τ ≤ π)
    {N : ℕ} (hbdd : ∀ ω, π ω ≤ (N : ℕ∞)) :
    ∫ x, stoppedValue f π x ∂μ ≤ ∫ x, stoppedValue f τ x ∂μ := by
  have hmono := hf.neg.expected_stoppedValue_mono hτ hπ hle hbdd
  -- stoppedValue (-f) σ ω = -(stoppedValue f σ ω) by unfolding Pi.neg and stoppedValue
  have h1 : ∀ ω, stoppedValue (-f) τ ω = -(stoppedValue f τ ω) := fun _ => rfl
  have h2 : ∀ ω, stoppedValue (-f) π ω = -(stoppedValue f π ω) := fun _ => rfl
  simp_rw [h1, h2] at hmono
  rw [integral_neg, integral_neg] at hmono
  linarith

/-- Optimal Stopping Theorem, supermartingale half (Lu-BDA Ch21 §21.3, Theorem 21.1):
`E[Xτ] ≤ E[X₀]` for a bounded stopping time `τ`. Specialization of
`supermartingale_expected_stoppedValue_antitone` with the earlier stopping time `≡ 0`. -/
theorem supermartingale_integral_stoppedValue_le
    {τ : Ω → ℕ∞} (hf : Supermartingale f 𝒢 μ) (hτ : IsStoppingTime 𝒢 τ)
    {N : ℕ} (hbdd : ∀ ω, τ ω ≤ (N : ℕ∞)) :
    ∫ x, stoppedValue f τ x ∂μ ≤ ∫ x, f 0 x ∂μ := by
  have h0 : IsStoppingTime 𝒢 (fun _ : Ω => (0 : ℕ∞)) := isStoppingTime_const 𝒢 (0 : ℕ)
  have hle : (fun _ : Ω => (0 : ℕ∞)) ≤ τ := fun _ => zero_le
  -- stoppedValue_const is proved by rfl, so stoppedValue f (fun _ => 0) = f 0 definitionally.
  exact supermartingale_expected_stoppedValue_antitone hf h0 hτ hle hbdd

end StatLean.MultipleTesting
