module
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
# Second-order Taylor upper bound for a function with bounded second derivative

`ψ(a+h) − ψ(a) − h·ψ'(a) ≤ (B²/2)·h²` whenever the second derivative satisfies `ψ'' ≤ B²`.
The single analytic brick behind the GLM score's sub-Gaussian MGF (Wainwright, *High-Dimensional
Statistics*, proof of Corollary 9.26, p. 288): `log 𝔼[e^{−tVᵢⱼ}] = ψ(ηᵢ+txᵢⱼ) − ψ(ηᵢ) − txᵢⱼψ'(ηᵢ) ≤ B²t²xᵢⱼ²/2`.

`ForMathlib` layer — Mathlib-only, theorem-agnostic. The bound holds for all `h` (both signs):
`g(h) := ψ(a+h) − ψ(a) − h·ψ'(a)` satisfies `g(0) = 0`, `g'(0) = 0`, and `g'' = ψ''(a+·) ≤ B²`, so
`g(h) − (B²/2)h²` is concave with a maximum (value `0`) at `h = 0`.
-/

namespace StatLean.HighDimensionalStatistics

/-- Second-order Taylor upper bound under `ψ'' ≤ B²`:
`ψ(a + h) − ψ(a) − h·ψ'(a) ≤ (B²/2)·h²` for every `a, h`. Only the upper bound on `ψ''` is needed
(no lower bound): `h ↦ g(h) − (B²/2)h²` is concave with `g(0) = g'(0) = 0`. -/
theorem psi_taylor_upper (ψ ψ' ψ'' : ℝ → ℝ) (B : ℝ)
    -- USER-INPUT: `ψ'` is the derivative of `ψ`; Wainwright §9.1 (partition function, smooth).
    (hψ' : ∀ x, HasDerivAt ψ (ψ' x) x)
    -- USER-INPUT: `ψ''` is the derivative of `ψ'`; Wainwright §9.1.
    (hψ'' : ∀ x, HasDerivAt ψ' (ψ'' x) x)
    -- USER-INPUT: bounded second derivative `ψ'' ≤ B²` (G2); Wainwright §9.5 (G2).
    (hbound : ∀ x, ψ'' x ≤ B ^ 2)
    (a h : ℝ) :
    ψ (a + h) - ψ a - h * ψ' a ≤ B ^ 2 / 2 * h ^ 2 := by
  -- `G t = (B²/2)t² − (ψ(a+t) − ψ a − t·ψ'(a))` is convex (`G'' = B² − ψ''(a+·) ≥ 0`) with
  -- `G 0 = 0`, `G'(0) = 0`, so it is minimized at `0`; hence `G h ≥ 0`, which is the claim.
  set G : ℝ → ℝ := fun t => B ^ 2 / 2 * t ^ 2 - (ψ (a + t) - ψ a - t * ψ' a) with hGdef
  have hG' : ∀ t, HasDerivAt G (B ^ 2 * t - (ψ' (a + t) - ψ' a)) t := by
    intro t
    rw [hGdef]
    have h1 : HasDerivAt (fun s => ψ (a + s)) (ψ' (a + t)) t := by
      simpa using! (hψ' (a + t)).comp t ((hasDerivAt_id t).const_add a)
    have h2 : HasDerivAt (fun s : ℝ => B ^ 2 / 2 * s ^ 2) (B ^ 2 * t) t := by
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
      have := hsq.const_mul (B ^ 2 / 2)
      convert! this using 1
      ring
    have h3 : HasDerivAt (fun s : ℝ => s * ψ' a) (ψ' a) t := by
      simpa using (hasDerivAt_id t).mul_const (ψ' a)
    exact h2.sub ((h1.sub_const (ψ a)).sub h3)
  have hGcont : Continuous G :=
    Differentiable.continuous (fun x => (hG' x).differentiableAt)
  have hgder : ∀ t, HasDerivAt (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a))
      (B ^ 2 - ψ'' (a + t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => B ^ 2 * s) (B ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul (B ^ 2)
    have h2 : HasDerivAt (fun s => ψ' (a + s)) (ψ'' (a + t)) t := by
      simpa using! (hψ'' (a + t)).comp t ((hasDerivAt_id t).const_add a)
    exact h1.sub (h2.sub_const (ψ' a))
  have hmono : Monotone (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hgder x).differentiableAt
    · intro x
      rw [(hgder x).deriv]
      linarith [hbound (a + x)]
  have hg0 : (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) (0 : ℝ) = 0 := by simp
  have hG0 : G 0 = 0 := by rw [hGdef]; simp
  have hGh : G h = B ^ 2 / 2 * h ^ 2 - (ψ (a + h) - ψ a - h * ψ' a) := by rw [hGdef]
  rw [← sub_nonneg, ← hGh]
  rcases lt_trichotomy h 0 with hlt | heq | hgt
  · obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope G (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) hlt
        hGcont.continuousOn (fun x _ => hG' x)
    have hgc : (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) c ≤ 0 := by
      have := hmono (le_of_lt hc.2); rwa [hg0] at this
    have hh : (0 : ℝ) < 0 - h := by linarith
    have hnum : G 0 - G h ≤ 0 := by
      have hp : (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) c * (0 - h) ≤ 0 :=
        mul_nonpos_iff.mpr (Or.inr ⟨hgc, hh.le⟩)
      simp only [] at hp
      rwa [hslope, div_mul_cancel₀ _ hh.ne'] at hp
    linarith [hG0]
  · rw [heq]; exact hG0.ge
  · obtain ⟨c, hc, hslope⟩ :=
      exists_hasDerivAt_eq_slope G (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) hgt
        hGcont.continuousOn (fun x _ => hG' x)
    have hgc : (0 : ℝ) ≤ (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) c := by
      have := hmono (le_of_lt hc.1); rwa [hg0] at this
    have hh : (0 : ℝ) < h - 0 := by linarith
    have hnum : 0 ≤ G h - G 0 := by
      have hp : (0 : ℝ) ≤ (fun s => B ^ 2 * s - (ψ' (a + s) - ψ' a)) c * (h - 0) :=
        mul_nonneg hgc hh.le
      simp only [] at hp
      rwa [hslope, div_mul_cancel₀ _ hh.ne'] at hp
    linarith [hG0]

end StatLean.HighDimensionalStatistics
