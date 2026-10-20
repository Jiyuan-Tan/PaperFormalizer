module
/-
Copyright (c) 2026 StatLean contributors. All rights reserved.
-/
public import StatLean.TimeSeries.ForMathlib.Markov.HarrisTheorem

@[expose] public section

/-!
# Minorization for random-coefficient (iterated-function-system) autoregressions

`ForMathlib/Markov/HarrisTheorem.lean` supplies the Harris engine and, as its worked
instance, the **additive** nonlinear autoregression `X_t = f(𝐗_{t−1}) + ε_t`
(`nlARKernel`, `hasMinorization_nlAR_pow`). The conditionally heteroscedastic models of
FY §4.2 are **not** of that shape: their innovation enters *multiplicatively*, through a
state-dependent scale. This file builds the corresponding brick for

  `X_t = f(X_{t−1}, …, X_{t−p−1}) + s(X_{t−1}, …, X_{t−p−1}) · ε_t`,        (⋆)

the *scaled-noise* (equivalently: random-coefficient / iterated-function-system)
autoregression, whose kernel is `sclARKernel f s ν`.

## What is proved

* `sclARKernel`, `isMarkovKernel_sclARKernel`, `sclARKernel_apply_eq` — the kernel of (⋆).
* `sclDens` and `sclAR_lintegral` — **the value-coordinate identity**, the technical heart:
  substituting `u = f(𝐱) + s(𝐱)·ε` for the innovation turns the noise density `g` into the
  *value* density `g((u − f 𝐱)/s 𝐱) / s 𝐱`. This is the multiplicative analogue of
  `nlAR_lintegral`; the change of variables is a translation composed with a dilation, so
  the only "Jacobian" that appears is the scalar `1/s(𝐱)` — no determinants, exactly as in
  the additive case. It is proved from `Real.map_volume_mul_left` and translation
  invariance of Lebesgue measure.
* `pow_ge_window_scl` — the induction on the number of steps ("value-coordinate peeling"):
  as long as the state stays in the box and the *value* density is `≥ δ` on the window `J`,
  the `k`-step law dominates `δᵏ` times the pushforward of the `k`-fold window measure.
  Verbatim the shape of `pow_ge_window`, with `sclDens` in place of `g (u − f x)`; it
  reuses `shiftPush`, `iterPush`, `map_iterPush_succ` and `iterPush_full` unchanged, since
  those describe the *state bookkeeping*, which (⋆) shares with the additive recursion.
* `hasMinorization_sclAR_pow` — **the brick**: after `p+1` steps every coordinate has been
  refreshed, so `κ^{p+1}(𝐱, ·)` dominates `δ^{p+1} ·` a *fixed* window measure, uniformly
  over the Lyapunov sublevel set `{V ≤ R}`, where
  `δ = γ / (λ_s R_b + c_s)` and `γ` is the minimum of `g` over the compact window
  `|t| ≤ (R_b + B)/s₀`. The two new hypotheses relative to the additive case are exactly
  the two things the scale must satisfy:
  * `hslo : ∀ x, s₀ ≤ s x` with `0 < s₀` — a **uniform positive floor** for the scale.
    Without it the value density `g(·)/s(𝐱)` degenerates (the one-step law collapses onto a
    point as `s(𝐱) → 0`) and no minorization of a fixed window is possible; this is the
    formal counterpart of the "collapse region" recorded in `Mixing/Relations.lean`'s
    GARCH obstruction note.
  * `hsup : ∀ x, s x ≤ λ_s (⨆ᵢ |xᵢ|) + c_s` — **linear growth** of the scale, which is what
    bounds `1/s` away from `0` *from below* on the box and hence produces a positive `δ`.

## Scope: which models this covers, and which it does not

For an **ARCH(p)** process `X_t = σ_t ε_t`, `σ_t² = c₀ + Σᵢ bᵢ X_{t−i}²` with `c₀ > 0`, (⋆)
holds *exactly* with `f = 0` and `s(𝐱) = √(c₀ + Σᵢ bᵢ xᵢ²)`: the floor is `s₀ = √c₀ > 0`
and the growth bound is `s(𝐱) ≤ √c₀ + √(Σᵢ bᵢ) · ⨆ᵢ|xᵢ|`. So the ARCH state chain is
covered by `hasMinorization_sclAR_pow` as it stands. Note that the coordinates must be the
**signed** `X`'s, not the squares: in squared coordinates the innovation enters through
`ε²`, the map is not a bijection of the new value, and the one-step law is supported on a
curve.

For a **GARCH(p, q)** with `q ≥ 1` the scale `σ_t` also depends on the `σ²` lags, which are
not coordinates of `(X_{t−1}, …, X_{t−p})`; the state must be enlarged to
`(X_{t−1}, …, X_{t−p}, σ_{t−1}², …, σ_{t−q+1}²)` and its update is *not* of `shiftPush`
shape (only the `X`-block shifts; the `σ²`-block is a deterministic function of both
blocks). Generalising `shiftPush`/`iterPush` to "shift one block, recompute the other" is
the remaining state-bookkeeping gap for GARCH; the analytic ingredient — this file's
`sclAR_lintegral` and `pow_ge_window_scl` — is not what is missing.

## The drift half

Deliberately **not** included. The additive drift `hasLyapunovDrift_nlAR` uses the
Lyapunov function `V(𝐱) = ⨆ᵢ θⁱ|xᵢ|` and the pointwise bound
`V(shiftPush 𝐱 (f 𝐱 + e)) ≤ θV(𝐱) + c + |e|`, in which the noise contributes *additively*
and can be integrated out against a constant. Under (⋆) the noise contributes
`s(𝐱)|e|`, i.e. a term that is **linear in the state times the noise**, so the same
argument gives contraction `θ + λ_s E|ε| θ^{−p}`, which is `≥ θ` and cannot be made `< 1`
by choosing `θ`. The correct Lyapunov function for a multiplicative recursion is the
*squared* weighted sup-norm `⨆ᵢ θⁱ xᵢ²` (equivalently `‖·‖₁` on the squared state), under
which the drift becomes the second-moment contraction `Σᵢ bᵢ + Σⱼ aⱼ < 1` of
Basrak–Davis–Mikosch — which is exactly what `Mixing/Relations.lean`'s `hsum` supplies.
Recording this here because the naive transfer of `hasLyapunovDrift_nlAR` is a real trap:
it typechecks up to the final inequality and then fails.

**Bibliographic comments.** Random-coefficient/iterated-function-system minorization:
persistent in the Markov-chain literature since M. F. Barnsley and S. Demko,
*Iterated function systems and the global construction of fractals* (Proc. Roy. Soc. London
A 399 (1985)); for GARCH specifically, B. Basrak, R. A. Davis and T. Mikosch,
*Regular variation of GARCH processes* (Stoch. Proc. Appl. 99 (2002), 95–115), and
M. Bougerol and N. Picard, *Strict stationarity of generalized autoregressive processes*
(Ann. Probab. 20 (1992), 1714–1730). The Harris-theorem packaging is Hairer–Mattingly, as
in `HarrisTheorem.lean`.
-/

open MeasureTheory ProbabilityTheory Filter StatLean.Minimaxity
open scoped ENNReal Topology

namespace StatLean.TimeSeries

variable {p : ℕ}

/-- The transition kernel of the **scaled-noise (random-coefficient) autoregression**
`X_t = f(X_{t−1}, …, X_{t−p−1}) + s(X_{t−1}, …, X_{t−p−1}) · ε_t`. -/
noncomputable def sclARKernel (f s : (Fin (p + 1) → ℝ) → ℝ) (ν : Measure ℝ) :
    Kernel (Fin (p + 1) → ℝ) (Fin (p + 1) → ℝ) :=
  ((Kernel.id : Kernel (Fin (p + 1) → ℝ) (Fin (p + 1) → ℝ)).prod
    (Kernel.const _ ν)).map fun xe =>
      (Fin.cons (f xe.1 + s xe.1 * xe.2) (fun i => xe.1 i.castSucc) : Fin (p + 1) → ℝ)

private theorem measurable_sclStep {f s : (Fin (p + 1) → ℝ) → ℝ}
    (hf : Measurable f) (hs : Measurable s) :
    Measurable fun xe : (Fin (p + 1) → ℝ) × ℝ =>
      (Fin.cons (f xe.1 + s xe.1 * xe.2) (fun i => xe.1 i.castSucc) : Fin (p + 1) → ℝ) := by
  rw [measurable_pi_iff]
  refine Fin.cases ?_ ?_
  · simpa using! (hf.comp measurable_fst).add ((hs.comp measurable_fst).mul measurable_snd)
  · exact fun i => by simpa using! (measurable_pi_apply i.castSucc).comp measurable_fst

theorem isMarkovKernel_sclARKernel {f s : (Fin (p + 1) → ℝ) → ℝ}
    (hf : Measurable f) (hs : Measurable s) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsMarkovKernel (sclARKernel f s ν) :=
  Kernel.IsMarkovKernel.map _ (measurable_sclStep hf hs)

theorem sclARKernel_apply_eq {f s : (Fin (p + 1) → ℝ) → ℝ}
    (hf : Measurable f) (hs : Measurable s) (ν : Measure ℝ) [SFinite ν]
    (x : Fin (p + 1) → ℝ) :
    sclARKernel f s ν x = Measure.map (fun e : ℝ => shiftPush x (f x + s x * e)) ν := by
  have hmeas := measurable_sclStep hf hs
  rw [sclARKernel, Kernel.map_apply _ hmeas, Kernel.prod_apply]
  simp only [Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod, Measure.map_map hmeas measurable_prodMk_left]
  rfl

/-- The **value-coordinate density** of the scaled-noise step. -/
noncomputable def sclDens (f s : (Fin (p + 1) → ℝ) → ℝ) (g : ℝ → ℝ≥0∞)
    (x : Fin (p + 1) → ℝ) (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (s x)⁻¹ * g ((u - f x) / s x)

/-- **One step, in value coordinates.** -/
theorem sclAR_lintegral {f s : (Fin (p + 1) → ℝ) → ℝ}
    (hf : Measurable f) (hs : Measurable s) {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    {ν : Measure ℝ} [SFinite ν] (hν : ν = MeasureTheory.volume.withDensity g)
    (hspos : ∀ x, 0 < s x) (x : Fin (p + 1) → ℝ)
    {h : (Fin (p + 1) → ℝ) → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ y, h y ∂(sclARKernel f s ν x) = ∫⁻ u, sclDens f s g x u * h (shiftPush x u) := by
  have ha : 0 < s x := hspos x
  have hane : s x ≠ 0 := ha.ne'
  have hsp : Measurable fun u : ℝ => shiftPush x u :=
    measurable_shiftPush.comp (measurable_const.prodMk measurable_id)
  have hΦ : Measurable fun e : ℝ => f x + s x * e :=
    measurable_const.add (measurable_const_mul _)
  have hcomp : Measurable fun e : ℝ => shiftPush x (f x + s x * e) := hsp.comp hΦ
  have step1 : ∫⁻ y, h y ∂(sclARKernel f s ν x)
      = ∫⁻ e, g e * h (shiftPush x (f x + s x * e)) := by
    rw [sclARKernel_apply_eq hf hs ν x, lintegral_map hh hcomp]
    subst hν
    exact lintegral_withDensity_eq_lintegral_mul _ hg (hh.comp hcomp)
  have hΨm : Measurable fun u : ℝ => sclDens f s g x u * h (shiftPush x u) := by
    refine Measurable.mul ?_ (hh.comp hsp)
    exact measurable_const.mul (hg.comp ((measurable_id.sub measurable_const).div_const _))
  have hmapΦ : Measure.map (fun e : ℝ => f x + s x * e) volume
      = ENNReal.ofReal (s x)⁻¹ • (volume : Measure ℝ) := by
    have h1 : Measure.map (fun e : ℝ => s x * e) volume
        = ENNReal.ofReal |(s x)⁻¹| • (volume : Measure ℝ) := Real.map_volume_mul_left hane
    have h2 : Measure.map (fun v : ℝ => f x + v) volume = (volume : Measure ℝ) :=
      (measurePreserving_add_left volume (f x)).map_eq
    have hcompm : (fun e : ℝ => f x + s x * e)
        = (fun v : ℝ => f x + v) ∘ (fun e : ℝ => s x * e) := rfl
    rw [hcompm, ← Measure.map_map (measurable_const_add _) (measurable_const_mul _), h1,
      Measure.map_smul, h2, abs_of_pos (inv_pos.2 ha)]
  have step2 : ∫⁻ e, (fun u => sclDens f s g x u * h (shiftPush x u)) (f x + s x * e)
      = ENNReal.ofReal (s x)⁻¹ * ∫⁻ u, sclDens f s g x u * h (shiftPush x u) := by
    rw [← lintegral_map hΨm hΦ, hmapΦ, lintegral_smul_measure, smul_eq_mul]
  have hpt : ∀ e : ℝ, g e * h (shiftPush x (f x + s x * e))
      = ENNReal.ofReal (s x) *
        ((fun u => sclDens f s g x u * h (shiftPush x u)) (f x + s x * e)) := by
    intro e
    have hval : (f x + s x * e - f x) / s x = e := by
      rw [add_sub_cancel_left]; field_simp
    simp only [sclDens, hval]
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ hane,
      ENNReal.ofReal_one, one_mul]
  rw [step1, lintegral_congr hpt]
  have hcm : ∫⁻ e, ENNReal.ofReal (s x) *
      ((fun u => sclDens f s g x u * h (shiftPush x u)) (f x + s x * e))
      = ENNReal.ofReal (s x) * ∫⁻ e,
        ((fun u => sclDens f s g x u * h (shiftPush x u)) (f x + s x * e)) :=
    lintegral_const_mul _ (hΨm.comp hΦ)
  rw [hcm, step2, ← mul_assoc, ← ENNReal.ofReal_mul ha.le, mul_inv_cancel₀ hane,
    ENNReal.ofReal_one, one_mul]

/-- **The window minorization, by induction on the number of steps** (scaled-noise version
of `pow_ge_window`). -/
theorem pow_ge_window_scl {f s : (Fin (p + 1) → ℝ) → ℝ} (hf : Measurable f) (hs : Measurable s)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν = MeasureTheory.volume.withDensity g) (hspos : ∀ x, 0 < s x)
    {J : Set ℝ} (hJ : MeasurableSet J) {Rb δ : ℝ}
    (hstab : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J, ∀ i, |shiftPush x u i| ≤ Rb)
    (hdens : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J,
      ENNReal.ofReal δ ≤ sclDens f s g x u) :
    ∀ (k : ℕ) (x : Fin (p + 1) → ℝ), (∀ i, |x i| ≤ Rb) →
      ∀ A : Set (Fin (p + 1) → ℝ), MeasurableSet A →
      ENNReal.ofReal δ ^ k *
          (Measure.map (iterPush k x) (Measure.pi fun _ : Fin k => volume.restrict J)) A
        ≤ ((sclARKernel f s ν) ^ k) x A := by
  haveI : IsMarkovKernel (sclARKernel f s ν) := isMarkovKernel_sclARKernel hf hs ν
  intro k
  induction k with
  | zero =>
      intro x _ A hA
      have hmass : (Measure.pi fun _ : Fin 0 => (volume.restrict J : Measure ℝ)) Set.univ = 1 := by
        rw [show (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi fun _ => Set.univ by simp,
          Measure.pi_pi]
        simp
      have hd : Measure.map (iterPush 0 x) (Measure.pi fun _ : Fin 0 => volume.restrict J)
          = Measure.dirac x := by
        rw [show (iterPush 0 x) = fun _ : Fin 0 → ℝ => x from rfl, Measure.map_const, hmass,
          one_smul]
      rw [hd, pow_zero, one_mul, pow_zero]
      exact le_of_eq rfl
  | succ k ih =>
      intro x hx A hA
      have hδne : (ENNReal.ofReal δ) ^ (k + 1) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
      have hcoe : Measurable fun y : Fin (p + 1) → ℝ => ((sclARKernel f s ν ^ k) y A) :=
        Kernel.measurable_coe _ hA
      have hstepR : ((sclARKernel f s ν) ^ (k + 1)) x A
          = ∫⁻ u, sclDens f s g x u * ((sclARKernel f s ν ^ k) (shiftPush x u) A) := by
        have h0 : ((sclARKernel f s ν) ^ (k + 1)) x
            = ((sclARKernel f s ν) x).bind ((sclARKernel f s ν) ^ k) := by
          rw [pow_succ]
          exact Kernel.comp_apply ((sclARKernel f s ν) ^ k) (sclARKernel f s ν) x
        rw [h0, Measure.bind_apply hA (Kernel.aemeasurable _)]
        exact sclAR_lintegral hf hs hg hν hspos x hcoe
      rw [hstepR, map_iterPush_succ J k x hA, ← lintegral_const_mul' _ _ hδne]
      refine le_trans (lintegral_mono_ae ((ae_restrict_iff' hJ).2
        (Filter.Eventually.of_forall fun u hu => ?_)))
        (lintegral_mono' Measure.restrict_le_self le_rfl)
      have hIH := ih (shiftPush x u) (hstab x hx u hu) A hA
      calc ENNReal.ofReal δ ^ (k + 1) *
            (Measure.map (iterPush k (shiftPush x u))
              (Measure.pi fun _ : Fin k => volume.restrict J)) A
          = ENNReal.ofReal δ * (ENNReal.ofReal δ ^ k *
              (Measure.map (iterPush k (shiftPush x u))
                (Measure.pi fun _ : Fin k => volume.restrict J)) A) := by
            rw [pow_succ']; ring
        _ ≤ sclDens f s g x u * ((sclARKernel f s ν ^ k) (shiftPush x u) A) :=
            mul_le_mul' (hdens x hx u hu) hIH

/-- **Minorization of the `(p+1)`-step scaled-noise kernel.** -/
theorem hasMinorization_sclAR_pow
    {f s : (Fin (p + 1) → ℝ) → ℝ} (hf : Measurable f) (hs : Measurable s)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) (hgc : Continuous g) (hgpos : ∀ t, 0 < g t)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν = MeasureTheory.volume.withDensity g)
    {lam c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ x : Fin (p + 1) → ℝ, |f x| ≤ lam * (⨆ i, |x i|) + c)
    {s0 lams cs : ℝ} (hs0 : 0 < s0) (hslo : ∀ x, s0 ≤ s x) (hlams : 0 ≤ lams)
    (hsup : ∀ x : Fin (p + 1) → ℝ, s x ≤ lams * (⨆ i, |x i|) + cs)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {R : ℝ} (hR0 : 0 < R) :
    ∃ (α : ℝ) (ρ : Measure (Fin (p + 1) → ℝ)),
      HasMinorization ((sclARKernel f s ν) ^ (p + 1)) (lyapV θ) R α ρ := by
  haveI : IsMarkovKernel (sclARKernel f s ν) := isMarkovKernel_sclARKernel hf hs ν
  have hspos : ∀ x, 0 < s x := fun x => lt_of_lt_of_le hs0 (hslo x)
  -- the box the level set lives in
  obtain ⟨Rb, hRbdef⟩ : ∃ r : ℝ, r = R / θ ^ p := ⟨_, rfl⟩
  have hRb0 : 0 < Rb := hRbdef ▸ div_pos hR0 (pow_pos hθ0 p)
  have hbox : ∀ x : Fin (p + 1) → ℝ, lyapV θ x ≤ R → ∀ i, |x i| ≤ Rb := by
    intro x hx i
    rw [hRbdef, le_div_iff₀ (pow_pos hθ0 p)]
    have h1 : θ ^ p ≤ θ ^ (i : ℕ) :=
      pow_le_pow_of_le_one hθ0.le hθ1.le (Nat.lt_succ_iff.mp i.isLt)
    calc |x i| * θ ^ p = θ ^ p * |x i| := mul_comm _ _
      _ ≤ θ ^ (i : ℕ) * |x i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ lyapV θ x := le_lyapV θ x i
      _ ≤ R := hx
  obtain ⟨J, hJdef⟩ : ∃ t : Set ℝ, t = Set.Icc (-Rb) Rb := ⟨_, rfl⟩
  have hJm : MeasurableSet J := hJdef ▸ measurableSet_Icc
  have hJmem : ∀ u ∈ J, |u| ≤ Rb := fun u hu => by
    rw [hJdef] at hu; exact abs_le.2 ⟨hu.1, hu.2⟩
  have hstab : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J, ∀ i,
      |shiftPush x u i| ≤ Rb := by
    intro x hx u hu i
    refine Fin.cases ?_ ?_ i
    · simpa [shiftPush] using hJmem u hu
    · intro j; simpa [shiftPush] using hx j.castSucc
  -- the drift and the scale are bounded on the box
  obtain ⟨B, hBdef⟩ : ∃ b : ℝ, b = |lam| * Rb + c := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ by positivity
  have hfB : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → |f x| ≤ B := by
    intro x hx
    refine (hbound x).trans ?_
    have hsup' : (⨆ i, |x i|) ≤ Rb := ciSup_le hx
    have hnn : 0 ≤ ⨆ i, |x i| := ciSup_abs_nonneg x
    have : lam * (⨆ i, |x i|) ≤ |lam| * Rb := by
      calc lam * (⨆ i, |x i|) ≤ |lam| * (⨆ i, |x i|) :=
            mul_le_mul_of_nonneg_right (le_abs_self lam) hnn
        _ ≤ |lam| * Rb := mul_le_mul_of_nonneg_left hsup' (abs_nonneg _)
    rw [hBdef]; linarith
  obtain ⟨S1, hS1def⟩ : ∃ t : ℝ, t = lams * Rb + cs := ⟨_, rfl⟩
  have hsS1 : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → s x ≤ S1 := by
    intro x hx
    refine (hsup x).trans ?_
    have hsup' : (⨆ i, |x i|) ≤ Rb := ciSup_le hx
    rw [hS1def]
    have : lams * (⨆ i, |x i|) ≤ lams * Rb := mul_le_mul_of_nonneg_left hsup' hlams
    linarith
  have hS10 : 0 < S1 := by
    have h1 := hslo (fun _ => 0)
    have h2 := hsS1 (fun _ => 0) (fun i => by simpa using hRb0.le)
    linarith
  -- the density is bounded below on the (compact) relevant window
  obtain ⟨T, hTdef⟩ : ∃ t : ℝ, t = (Rb + B) / s0 := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hTdef ▸ by positivity
  have hne : (Set.Icc (-T) T).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨t₀, ht₀mem, ht₀min⟩ := isCompact_Icc.exists_isMinOn hne hgc.continuousOn
  obtain ⟨γ, hγdef⟩ : ∃ d : ℝ, d = (min (g t₀) 1).toReal := ⟨_, rfl⟩
  have hminne : min (g t₀) 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hofγ : ENNReal.ofReal γ = min (g t₀) 1 := by
    rw [hγdef, ENNReal.ofReal_toReal hminne]
  have hγ0 : 0 < γ := by
    have : 0 < min (g t₀) 1 := lt_min (hgpos t₀) one_pos
    rw [hγdef]
    exact ENNReal.toReal_pos this.ne' hminne
  have hγg : ∀ t : ℝ, |t| ≤ T → ENNReal.ofReal γ ≤ g t := by
    intro t ht
    rw [hofγ]
    refine (min_le_left _ _).trans (ht₀min ?_)
    exact ⟨by linarith [neg_abs_le t, le_abs_self t], by linarith [le_abs_self t]⟩
  obtain ⟨δ, hδdef⟩ : ∃ d : ℝ, d = γ / S1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδdef ▸ div_pos hγ0 hS10
  have hdens : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J,
      ENNReal.ofReal δ ≤ sclDens f s g x u := by
    intro x hx u hu
    have hsx0 : 0 < s x := hspos x
    have harg : |(u - f x) / s x| ≤ T := by
      rw [abs_div, abs_of_pos hsx0, div_le_iff₀ hsx0, hTdef, div_mul_eq_mul_div,
        le_div_iff₀ hs0]
      have h1 : |u - f x| ≤ Rb + B := (abs_sub _ _).trans (add_le_add (hJmem u hu) (hfB x hx))
      have h2 : s0 ≤ s x := hslo x
      nlinarith [abs_nonneg (u - f x)]
    have h1 : ENNReal.ofReal γ ≤ g ((u - f x) / s x) := hγg _ harg
    have h2 : ENNReal.ofReal S1⁻¹ ≤ ENNReal.ofReal (s x)⁻¹ :=
      ENNReal.ofReal_le_ofReal (by
        have := hsS1 x hx
        exact inv_anti₀ hsx0 this)
    calc ENNReal.ofReal δ = ENNReal.ofReal S1⁻¹ * ENNReal.ofReal γ := by
          rw [← ENNReal.ofReal_mul (by positivity), hδdef]
          congr 1
          field_simp
      _ ≤ ENNReal.ofReal (s x)⁻¹ * g ((u - f x) / s x) := mul_le_mul' h2 h1
  -- the `(p+1)`-step window law, which does not depend on the starting state
  obtain ⟨Q, hQdef⟩ : ∃ m : Measure (Fin (p + 1) → ℝ),
      m = Measure.map (iterPush (p + 1) (0 : Fin (p + 1) → ℝ))
        (Measure.pi fun _ : Fin (p + 1) => volume.restrict J) := ⟨_, rfl⟩
  have hmapQ : ∀ x : Fin (p + 1) → ℝ,
      Measure.map (iterPush (p + 1) x) (Measure.pi fun _ : Fin (p + 1) => volume.restrict J)
        = Q := by
    intro x
    have hfun : iterPush (p + 1) x = iterPush (p + 1) (0 : Fin (p + 1) → ℝ) :=
      funext fun u => iterPush_full x 0 u
    rw [hQdef, hfun]
  have hvolJ : volume J = ENNReal.ofReal (2 * Rb) := by
    rw [hJdef, Real.volume_Icc]; ring_nf
  have hQuniv : Q Set.univ = ENNReal.ofReal (2 * Rb) ^ (p + 1) := by
    rw [hQdef, Measure.map_apply (measurable_iterPush' _ _) MeasurableSet.univ,
      Set.preimage_univ,
      show (Set.univ : Set (Fin (p + 1) → ℝ)) = Set.univ.pi fun _ => Set.univ by simp,
      Measure.pi_pi]
    simp [hvolJ]
  obtain ⟨m, hmdef⟩ : ∃ t : ℝ≥0∞, t = ENNReal.ofReal (2 * Rb) ^ (p + 1) := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := by
    rw [hmdef]
    exact pow_ne_zero _ (by simp [ENNReal.ofReal_eq_zero]; linarith)
  have hmtop : m ≠ ⊤ := by rw [hmdef]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hmtr : 0 < m.toReal := ENNReal.toReal_pos hm0 hmtop
  refine ⟨min (δ ^ (p + 1) * m.toReal) 1, m⁻¹ • Q, ?_⟩
  have hρuniv : (m⁻¹ • Q) Set.univ = 1 := by
    rw [Measure.smul_apply, smul_eq_mul, hQuniv, ← hmdef, ENNReal.inv_mul_cancel hm0 hmtop]
  refine ⟨⟨lt_min (by positivity) one_pos, min_le_right _ _⟩, ⟨hρuniv⟩, fun x hx A hA => ?_⟩
  have hw := pow_ge_window_scl hf hs hg hν hspos hJm hstab hdens (p + 1) x (hbox x hx) A hA
  rw [hmapQ x] at hw
  refine le_trans ?_ hw
  rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  have hle1 : ENNReal.ofReal (min (δ ^ (p + 1) * m.toReal) 1)
      ≤ ENNReal.ofReal δ ^ (p + 1) * m := by
    calc ENNReal.ofReal (min (δ ^ (p + 1) * m.toReal) 1)
        ≤ ENNReal.ofReal (δ ^ (p + 1) * m.toReal) :=
          ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = ENNReal.ofReal δ ^ (p + 1) * m := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hδ0.le,
            ENNReal.ofReal_toReal hmtop]
  calc ENNReal.ofReal (min (δ ^ (p + 1) * m.toReal) 1) * m⁻¹
      ≤ (ENNReal.ofReal δ ^ (p + 1) * m) * m⁻¹ := mul_le_mul_left hle1 _
    _ = ENNReal.ofReal δ ^ (p + 1) := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hm0 hmtop, mul_one]

end StatLean.TimeSeries
