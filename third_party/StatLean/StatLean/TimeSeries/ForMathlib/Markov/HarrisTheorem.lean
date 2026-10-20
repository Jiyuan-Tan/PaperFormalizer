module
public import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity

@[expose] public section

/-!
# Harris' ergodic theorem, Hairer–Mattingly form

The elementary route to geometric ergodicity of a Markov kernel: **Lyapunov drift plus
minorization on a level set imply a contraction in a weighted total-variation
distance**, hence a unique invariant law approached at a geometric rate.

* `lyapDist β V μ ν = ∫ (1 + β V) d|μ − ν|` — the weighted TV distance (`weightedTV`
  below; the `β = 0` case is `2·tvDist`);
* `HasLyapunovDrift κ V γ K` — `P V ≤ γ V + K` pointwise with `γ < 1`;
* `HasMinorization κ S α` — `κ x ≥ α · ρ` on the level set `S` for a common probability
  measure `ρ`;
* `harris_contraction` — the Hairer–Mattingly estimate: for suitable `β`, `κ` contracts
  `lyapDist` by a factor `ᾱ < 1`;
* `harris_theorem` — the packaged conclusion: a unique invariant probability measure
  `π`, with `tvDist (κⁿ x) π ≤ C(x)·ρ̄ⁿ` — exactly the envelope `IsErgodicWithRate`
  (and hence `IsGeometricallyErgodic`) needs;
* `IsGeometricallyErgodic.of_pow` — the glue that lifts geometric ergodicity of the
  `p`-step kernel `κ^p` back to `κ` (needed because the minorization for the nonlinear
  AR kernel of FY Theorem 2.4 only holds after `p` steps, once every coordinate has
  been refreshed).

This file exists to discharge the last structural debt of the TimeSeries area,
`nlARKernel_geometricallyErgodic` (FY Theorem 2.4(ii)); the Meyn–Tweedie
ψ-irreducibility/petite-set apparatus is deliberately avoided. **That debt is now closed
here**, in the `NLAR` section at the foot of the file:

* `HasLyapunovDrift.pow` — the drift iterates: `κ^n` drifts with `γⁿ` and `K/(1−γ)`;
* `hasLyapunovDrift_nlAR` — the geometrically weighted sup-norm `V(𝐱) = ⨆ᵢ θⁱ|xᵢ|` is a
  Lyapunov function for the nonlinear-AR kernel, with `θ = λ^{1/(p+1)}`;
* `pow_ge_window` / `hasMinorization_nlAR_pow` — after `p+1` steps every coordinate has
  been refreshed, so the law is a fixed multiple of a *state-independent* window measure;
* `nlARKernel_geometricallyErgodic` — **FY Theorem 2.4(ii)**, assembled from the above by
  `harris_theorem` on `κ^{p+1}`, `eq_of_invariant_of_isErgodicKernel` (to move invariance
  back to `κ`) and `IsGeometricallyErgodic.of_pow`.

The statement of FY Theorem 2.4(ii) used to live in `GeometricErgodicity.lean` as a named
`sorry`; it had to move here because its proof consumes this file's engine while this file
imports that one. Nothing outside its own file referenced it.

**STATUS.** All five headline results are proved and axiom-clean. Three features of the
formalization are worth flagging, because each replaces a step of the textbook argument:

* **No coupling.** Hairer–Mattingly close the contraction with a coupling construction.
  Here the same estimate falls out of the *minimality* of the Jordan decomposition,
  `jPos_add_le_of_add_eq`: from `μ + B = ν + A` with a common piece `m ≤ A`, `m ≤ B` one
  gets `jPos μ ν + m ≤ A` directly, and taking `m = α·min(aL, bL)·ρ` subtracts the
  minorization mass from both halves at once. The scalar core, `harris_num`, needs no
  finiteness at all — every step is monotone in `ℝ≥0∞`, so the estimate is true verbatim
  when the weighted distance is infinite.
* **No completeness argument.** The invariant law is built *explicitly* rather than as the
  limit of a TV-Cauchy sequence: writing `a n`, `b n` for the one-step Jordan parts of the
  chain from a fixed `x₀`, the identity `μ n + b n = μ (n+1) + a n` telescopes to
  `μ N + Σ_{n<N} a n = μ 0 + Σ_{n<N} b n`, both series converge geometrically (their masses
  are exactly what the contraction bounds), and `π := (μ 0 + Σ b) − Σ a` is the limit —
  with the *tails* of the two series as the explicit total-variation error.
* **No change of variables, no Jacobian.** The `p+1`-step minorization is usually written
  with the density `∏ₖ g(y_k − m_k(𝐱, y_{<k}))` of the triangular value map. Here that
  density is never formed: the chain is rewritten *in value coordinates* once
  (`nlAR_lintegral`, a one-dimensional translation of Lebesgue measure), and the induction
  `pow_ge_window` peels one value at a time, so the only product structure needed is
  `Measure.pi` over `Fin (p+1)` reassociated by `Fin.cons` (`map_iterPush_succ`). The
  minorizing law is then *defined* as the pushforward of the window measure, so it needs no
  identification with Lebesgue measure on a cube — only the fact that it does not depend on
  the starting state, which `iterPush_congr` proves from index arithmetic alone.

The two definitions this file rests on were each *refuted* in an earlier pass and have
since been repaired:

* `weightedTV` used to be built from `Measure.singularPart` rather than from the Jordan
  decomposition of `μ − ν`, so it ignored every absolutely-continuous overlap of the two
  laws and did not even separate measures; `harris_contraction` was false against it.
* `HasLyapunovDrift.drift` used to be stated with the *Bochner* integral, which Mathlib
  sets to `0` on non-integrable functions, so the drift hypothesis said nothing at states
  where `∫⁻ V d(κ x) = ∞`; a chain could escape to infinity, and `harris_theorem` was
  false against it.

Both machine-checked counterexamples are **retained below as block comments** (search for
`REFUTATION`). They no longer type-check — that is the point: each was a witness against a
definition that no longer exists, and against the repaired definitions the very same data
is harmless (for the first witness the honest `|μ − ν|` weighting drops from `1 + 10β` to
`1 + 5.5β` in one step; for the second the `∫⁻` drift simply fails at every nonzero state).
They are kept verbatim, demoted to comments, because they are the record of *why* the
definitions read the way they now do.

Note that the uniqueness proof here does **not** go through any contraction: it splits
`π − π'` by a Hahn set, shows each half is separately `κ`-invariant, and then uses the
drift (through `level_set_pos`) and the minorization to make the minorizing measure
vanish. So the downstream consumers that only need uniqueness are unaffected.

**Reference.** M. Hairer and J. C. Mattingly, *Yet another look at Harris' ergodic
theorem for Markov chains*, in Seminar on Stochastic Analysis, Random Fields and
Applications VI, Progr. Probab. 63, Birkhäuser (2011), 109–117. Consumed by
FY §2.1.4 Theorem 2.4 (An & Huang 1996; Bhattacharya & Lee 1995).
(`Hairer–Mattingly 2011` in tags.)

**Bibliographic comments.** Harris' theorem is T. E. Harris (1956); the drift/
minorization formulation is Meyn & Tweedie, *Markov Chains and Stochastic Stability*
(1993), ch. 15–16; the weighted-TV contraction proof formalized here is the
Hairer–Mattingly simplification, which needs no irreducibility theory.
-/

open MeasureTheory ProbabilityTheory Filter StatLean.Minimaxity StatLean.Bayesian
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S]

-- Kernel powers of a Markov kernel are Markov (the same one-line induction as the private
-- `isMarkovKernel_pow` of `GeometricErgodicity`, repeated here because that one is file-scoped).
private theorem markov_pow (κ : Kernel S S) [IsMarkovKernel κ] :
    ∀ n : ℕ, IsMarkovKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel S S))
  | n + 1 => by
      haveI := markov_pow κ n
      rw [pow_succ]
      exact Kernel.IsMarkovKernel.comp (κ ^ n) κ

-- **Kernel averaging is a total-variation contraction** (the private `tvDist_bind_le` of
-- `GeometricErgodicity`, repeated here for the same reason): on a measurable `s` the two sides
-- are the integrals of the `[0,1]`-valued measurable function `y ↦ κ y s`, which moves by at
-- most `1 * tvDist μ ν`.
private theorem tvDist_bind_le (κ : Kernel S S) [IsMarkovKernel κ] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (μ.bind κ) (ν.bind κ) ≤ tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
  refine tsub_le_iff_left.mpr ?_
  simpa using
    lintegral_le_lintegral_add_tvDist μ ν (κ.measurable_coe hs) (B := 1) fun _ => prob_le_one

-- Kernel averaging is additive in the initial law.
private theorem bind_add' (κ : Kernel S S) [IsSFiniteKernel κ] (μ ν : Measure S) :
    (μ + ν).bind κ = μ.bind κ + ν.bind κ := by
  ext t ht
  rw [Measure.bind_apply ht κ.aemeasurable, Measure.add_apply,
    Measure.bind_apply ht κ.aemeasurable, Measure.bind_apply ht κ.aemeasurable,
    lintegral_add_measure]

/-- The **weighted total-variation distance** `∫ (1 + βV) d|μ − ν|` of Hairer–Mattingly
(their `ρ_β`). The total-variation measure `|μ − ν|` is realized as
`|dμ/dλ − dν/dλ| · λ` for the common dominating measure `λ = μ + ν`; in `ℝ≥0∞` the
absolute difference is the sum of the two truncated subtractions. At `β = 0` this is
twice `StatLean.Minimaxity.tvDist`.

**Definition repaired 2026-08-09.** The first version used
`μ.singularPart ν + ν.singularPart μ`, which is *not* the Jordan decomposition of the
signed difference — it discards the absolutely-continuous disagreement entirely — and a
machine-checked counterexample (`cNoContraction`, retained below) refuted the
contraction theorem stated against it. -/
noncomputable def weightedTV (β : ℝ) (V : S → ℝ) (μ ν : Measure S) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1 + β * V x) *
    ((μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x)
      + (ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x)) ∂(μ + ν)

/-! ### The Jordan decomposition of `μ − ν`, in the `rnDeriv`-against-`μ + ν` form

`weightedTV` integrates against `|μ − ν| = jPos μ ν + jPos ν μ`, where `jPos μ ν` is the
positive part. Everything the contraction proof needs about `jPos` is here: it is the
`μ`-part where `μ` dominates (`jPos_le_left`), the two parts are exchanged by the identity
`μ + jPos ν μ = ν + jPos μ ν` (`add_jPos_comm`), and — the only nontrivial fact — that
identity is *minimal*: any other pair of measures realizing the same difference dominates
the Jordan parts, even after a common piece is removed (`jPos_add_le_of_add_eq`). That
minimality is what replaces Hairer–Mattingly's coupling step. -/

/-- The positive part of the Jordan decomposition of `μ − ν`, realized as a density against
`λ = μ + ν`. This is the measure `weightedTV` integrates against (together with `jPos ν μ`). -/
private noncomputable def jPos (μ ν : Measure S) : Measure S :=
  (μ + ν).withDensity fun x => μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x

private theorem jPos_swap (μ ν : Measure S) :
    jPos ν μ = (μ + ν).withDensity fun x => ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x := by
  rw [jPos, add_comm ν μ]

private theorem jPos_apply (μ ν : Measure S) {s : Set S} (hs : MeasurableSet s) :
    jPos μ ν s = ∫⁻ x in s, (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x) ∂(μ + ν) := by
  rw [jPos, withDensity_apply _ hs]

/-- `weightedTV` is the `(1 + βV)`-weighted mass of `|μ − ν| = jPos μ ν + jPos ν μ`. -/
private theorem weightedTV_eq (β : ℝ) {V : S → ℝ} (hV : Measurable V) (μ ν : Measure S) :
    weightedTV β V μ ν = (∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos μ ν))
      + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos ν μ) := by
  have hf : Measurable fun x => μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x :=
    (Measure.measurable_rnDeriv _ _).sub (Measure.measurable_rnDeriv _ _)
  have hg : Measurable fun x => ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x :=
    (Measure.measurable_rnDeriv _ _).sub (Measure.measurable_rnDeriv _ _)
  have hw : Measurable fun x => ENNReal.ofReal (1 + β * V x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add ((measurable_const : Measurable
      fun _ : S => β).mul hV))
  calc weightedTV β V μ ν
      = ∫⁻ x, (ENNReal.ofReal (1 + β * V x) * (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x)
          + ENNReal.ofReal (1 + β * V x) * (ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x))
            ∂(μ + ν) := by
        rw [weightedTV]; exact lintegral_congr fun x => by ring
    _ = (∫⁻ x, ENNReal.ofReal (1 + β * V x) * (μ.rnDeriv (μ + ν) x - ν.rnDeriv (μ + ν) x)
            ∂(μ + ν))
          + ∫⁻ x, ENNReal.ofReal (1 + β * V x) * (ν.rnDeriv (μ + ν) x - μ.rnDeriv (μ + ν) x)
            ∂(μ + ν) := lintegral_add_left (hw.mul hf) _
    _ = _ := by
        rw [jPos, jPos_swap, lintegral_withDensity_eq_lintegral_mul _ hf hw,
          lintegral_withDensity_eq_lintegral_mul _ hg hw]
        congr 1 <;> exact lintegral_congr fun x => by simp only [Pi.mul_apply]; ring

/-- The positive part is dominated by the measure it comes from. -/
private theorem jPos_le_left (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    jPos μ ν ≤ μ := by
  have hac : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  calc jPos μ ν
      ≤ (μ + ν).withDensity (μ.rnDeriv (μ + ν)) :=
        withDensity_mono (Filter.Eventually.of_forall fun _ => tsub_le_self)
    _ = μ := Measure.withDensity_rnDeriv_eq _ _ hac

private instance jPos_isFiniteMeasure (μ ν : Measure S) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] : IsFiniteMeasure (jPos μ ν) :=
  ⟨lt_of_le_of_lt (jPos_le_left μ ν _) (measure_lt_top μ _)⟩

/-- The defining identity of the Jordan decomposition, in additive (subtraction-free) form:
`μ − ν = jPos μ ν − jPos ν μ`. Both sides are `λ.withDensity (max (dμ/dλ) (dν/dλ))`. -/
private theorem add_jPos_comm (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ + jPos ν μ = ν + jPos μ ν := by
  have hacμ : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hacν : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hμ : (μ + ν).withDensity (μ.rnDeriv (μ + ν)) = μ :=
    Measure.withDensity_rnDeriv_eq _ _ hacμ
  have hν : (μ + ν).withDensity (ν.rnDeriv (μ + ν)) = ν :=
    Measure.withDensity_rnDeriv_eq _ _ hacν
  -- `p·λ + (q − p)·λ = max p q · λ`, applied in both orders
  have hmax : ∀ p q : S → ℝ≥0∞, Measurable p →
      (μ + ν).withDensity p + (μ + ν).withDensity (fun x => q x - p x)
        = (μ + ν).withDensity fun x => max (p x) (q x) := by
    intro p q hp
    rw [← withDensity_add_left hp fun x => q x - p x]
    refine withDensity_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    exact add_tsub_eq_max
  have e1 : μ + jPos ν μ
      = (μ + ν).withDensity fun x => max (μ.rnDeriv (μ + ν) x) (ν.rnDeriv (μ + ν) x) := by
    have h := hmax (μ.rnDeriv (μ + ν)) (ν.rnDeriv (μ + ν)) (Measure.measurable_rnDeriv _ _)
    rw [hμ] at h
    rw [jPos_swap]
    exact h
  have e2 : ν + jPos μ ν
      = (μ + ν).withDensity fun x => max (ν.rnDeriv (μ + ν) x) (μ.rnDeriv (μ + ν) x) := by
    have h := hmax (ν.rnDeriv (μ + ν)) (μ.rnDeriv (μ + ν)) (Measure.measurable_rnDeriv _ _)
    rw [hν] at h
    rw [jPos]
    exact h
  rw [e1, e2]
  exact withDensity_congr_ae (Filter.Eventually.of_forall fun x => max_comm _ _)

/-- The two Jordan parts of a pair of probability measures carry the same mass. -/
private theorem jPos_mass_eq (μ ν : Measure S) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : jPos μ ν Set.univ = jPos ν μ Set.univ := by
  have h := congrArg (fun m => m Set.univ) (add_jPos_comm μ ν)
  simp only [Measure.add_apply, measure_univ] at h
  exact ((ENNReal.add_right_inj ENNReal.one_ne_top).1 h).symm

/-- **Minimality of the Jordan decomposition**, in the form the contraction needs: if
`μ + B = ν + A` and a common piece `m` sits under both `A` and `B`, then `jPos μ ν + m ≤ A`.
(With `m = 0` this is the usual minimality; the extra `m` is where the minorization mass is
subtracted from both sides at once.) -/
private theorem jPos_add_le_of_add_eq {μ ν A B m : Measure S} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : μ + B = ν + A) (hmA : m ≤ A) (hmB : m ≤ B) :
    jPos μ ν + m ≤ A := by
  have hfm : Measurable (μ.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hgm : Measurable (ν.rnDeriv (μ + ν)) := Measure.measurable_rnDeriv _ _
  have hacμ : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hacν : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have hμ : (μ + ν).withDensity (μ.rnDeriv (μ + ν)) = μ :=
    Measure.withDensity_rnDeriv_eq _ _ hacμ
  have hν : (μ + ν).withDensity (ν.rnDeriv (μ + ν)) = ν :=
    Measure.withDensity_rnDeriv_eq _ _ hacν
  -- `D` is a Hahn set for the pair: off `D` the positive part has no mass.
  set D : Set S := {x | ν.rnDeriv (μ + ν) x ≤ μ.rnDeriv (μ + ν) x} with hDdef
  have hD : MeasurableSet D := measurableSet_le hgm hfm
  refine Measure.le_iff.2 fun s hs => ?_
  have hsD : MeasurableSet (s ∩ D) := hs.inter hD
  have hsDc : MeasurableSet (s \ D) := hs.diff hD
  have hmuD : ∫⁻ x in s ∩ D, μ.rnDeriv (μ + ν) x ∂(μ + ν) = μ (s ∩ D) := by
    rw [← withDensity_apply _ hsD, hμ]
  have hnuD : ∫⁻ x in s ∩ D, ν.rnDeriv (μ + ν) x ∂(μ + ν) = ν (s ∩ D) := by
    rw [← withDensity_apply _ hsD, hν]
  -- the positive part lives on `D`
  have hloc : jPos μ ν s = jPos μ ν (s ∩ D) := by
    have hz : jPos μ ν (s \ D) = 0 := by
      rw [jPos_apply _ _ hsDc]
      refine setLIntegral_eq_zero hsDc fun x hx => ?_
      exact tsub_eq_zero_of_le (le_of_not_ge fun hc => hx.2 hc)
    have hsplit := measure_inter_add_diff (μ := jPos μ ν) s hD
    rw [hz, add_zero] at hsplit
    exact hsplit.symm
  -- on `D` the positive part is exactly the difference of the two masses
  have hjord : jPos μ ν (s ∩ D) + ν (s ∩ D) = μ (s ∩ D) := by
    rw [jPos_apply _ _ hsD, ← hnuD, ← hmuD, ← lintegral_add_left (hfm.fun_sub hgm)]
    refine setLIntegral_congr_fun hsD fun x hx => ?_
    rw [tsub_add_eq_max, max_eq_left hx.2]
  -- the hypothesis `μ + B = ν + A`, read on `s ∩ D`
  have hkey : jPos μ ν (s ∩ D) + B (s ∩ D) = A (s ∩ D) := by
    have h1 : μ (s ∩ D) + B (s ∩ D) = ν (s ∩ D) + A (s ∩ D) := by
      have h2 := congrArg (fun m => m (s ∩ D)) h
      simpa only [Measure.add_apply] using h2
    have h3 : ν (s ∩ D) + (jPos μ ν (s ∩ D) + B (s ∩ D)) = ν (s ∩ D) + A (s ∩ D) := by
      rw [← add_assoc, add_comm (ν (s ∩ D)) (jPos μ ν (s ∩ D)), hjord]; exact h1
    exact (ENNReal.add_right_inj (measure_ne_top ν _)).1 h3
  calc (jPos μ ν + m) s
      = jPos μ ν (s ∩ D) + (m (s ∩ D) + m (s \ D)) := by
        rw [Measure.add_apply, hloc, measure_inter_add_diff (μ := m) s hD]
    _ ≤ jPos μ ν (s ∩ D) + B (s ∩ D) + A (s \ D) := by
        rw [add_assoc]
        exact add_le_add le_rfl (add_le_add (hmB _) (hmA _))
    _ = A s := by rw [hkey, measure_inter_add_diff (μ := A) s hD]


/-- **Lyapunov drift condition**: `∫ V d(κ x) ≤ γ V x + K` with a contraction factor
`γ < 1` (Hairer–Mattingly Assumption 1). -/
structure HasLyapunovDrift (κ : Kernel S S) (V : S → ℝ) (γ K : ℝ) : Prop where
  /-- Constitutive (H–M Assumption 1): the Lyapunov function is nonnegative. -/
  V_nonneg : ∀ x, 0 ≤ V x
  /-- Constitutive (H–M Assumption 1): `V` is measurable. -/
  V_measurable : Measurable V
  /-- Constitutive (H–M Assumption 1): the contraction factor is in `(0, 1)`. -/
  gamma_mem : 0 < γ ∧ γ < 1
  /-- Constitutive (H–M Assumption 1): the additive constant is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- Constitutive (H–M Assumption 1): the drift inequality `PV ≤ γV + K`, stated with
  the **lower** integral. Repaired 2026-08-09: with the Bochner integral, Mathlib's
  `integral_undef` convention makes the inequality vacuous at every state where `V` is
  not `κ x`-integrable (both sides are then trivially ordered), so the hypothesis
  constrained nothing where it mattered most and both existence and uniqueness failed. -/
  drift : ∀ x, (∫⁻ y, ENNReal.ofReal (V y) ∂(κ x)) ≤ ENNReal.ofReal (γ * V x + K)

/-- **Minorization on a sublevel set**: on `{V ≤ R}` the kernel dominates `α·ρ` for a
fixed probability measure `ρ` (Hairer–Mattingly Assumption 2). -/
structure HasMinorization (κ : Kernel S S) (V : S → ℝ) (R α : ℝ) (ρ : Measure S) :
    Prop where
  /-- Constitutive (H–M Assumption 2): the minorization strength is in `(0, 1]`. -/
  alpha_mem : 0 < α ∧ α ≤ 1
  /-- Constitutive (H–M Assumption 2): the minorizing measure is a probability
  measure. -/
  isProbability : IsProbabilityMeasure ρ
  /-- Constitutive (H–M Assumption 2): domination on the level set. -/
  minorize : ∀ x, V x ≤ R → ∀ A : Set S, MeasurableSet A →
    ENNReal.ofReal α * ρ A ≤ κ x A

/-- **Iterating the drift**: `n` steps contract by `γⁿ` with the geometric-series constant
`K/(1−γ)`. -/
theorem HasLyapunovDrift.lintegral_pow_le {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ}
    {γ K : ℝ} (h : HasLyapunovDrift κ V γ K) (n : ℕ) (x : S) :
    ∫⁻ y, ENNReal.ofReal (V y) ∂((κ ^ n) x)
      ≤ ENNReal.ofReal (γ ^ n * V x + K / (1 - γ)) := by
  obtain ⟨hγ0, hγ1⟩ := h.gamma_mem
  have h1γ : (0 : ℝ) < 1 - γ := by linarith
  have hKq : 0 ≤ K / (1 - γ) := div_nonneg h.K_nonneg h1γ.le
  have hVm : Measurable fun y : S => ENNReal.ofReal (V y) :=
    ENNReal.measurable_ofReal.comp h.V_measurable
  induction n with
  | zero =>
      have h0 : (κ ^ 0) x = Measure.dirac x := by rw [pow_zero]; rfl
      rw [h0, lintegral_dirac' _ hVm, pow_zero, one_mul]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  | succ n ih =>
      haveI := markov_pow κ n
      have h0 : (κ ^ (n + 1)) x = ((κ ^ n) x).bind κ := by
        rw [pow_succ']; exact Kernel.comp_apply κ (κ ^ n) x
      rw [h0, Measure.lintegral_bind (Kernel.aemeasurable _) hVm.aemeasurable]
      have hpt : ∀ z : S, (∫⁻ y, ENNReal.ofReal (V y) ∂(κ z))
          ≤ ENNReal.ofReal γ * ENNReal.ofReal (V z) + ENNReal.ofReal K := by
        intro z
        refine (h.drift z).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_add (by nlinarith [h.V_nonneg z]) h.K_nonneg,
          ENNReal.ofReal_mul hγ0.le]
      calc ∫⁻ z, (∫⁻ y, ENNReal.ofReal (V y) ∂(κ z)) ∂((κ ^ n) x)
          ≤ ∫⁻ z, (ENNReal.ofReal γ * ENNReal.ofReal (V z) + ENNReal.ofReal K) ∂((κ ^ n) x) :=
            lintegral_mono hpt
        _ = ENNReal.ofReal γ * (∫⁻ z, ENNReal.ofReal (V z) ∂((κ ^ n) x)) + ENNReal.ofReal K := by
            rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal γ * ENNReal.ofReal (γ ^ n * V x + K / (1 - γ))
              + ENNReal.ofReal K := by gcongr
        _ = ENNReal.ofReal (γ ^ (n + 1) * V x + K / (1 - γ)) := by
            have hVx : (0 : ℝ) ≤ γ ^ n * V x := mul_nonneg (pow_nonneg hγ0.le n) (h.V_nonneg x)
            have hnn1 : (0 : ℝ) ≤ γ * (γ ^ n * V x + K / (1 - γ)) := by nlinarith
            have hne : (1 : ℝ) - γ ≠ 0 := ne_of_gt h1γ
            rw [← ENNReal.ofReal_mul hγ0.le, ← ENNReal.ofReal_add hnn1 h.K_nonneg]
            congr 1
            field_simp
            ring

/-- The `n`-step kernel inherits a Lyapunov drift, with contraction `γⁿ`. -/
theorem HasLyapunovDrift.pow {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (h : HasLyapunovDrift κ V γ K) {n : ℕ} (hn : 0 < n) :
    HasLyapunovDrift (κ ^ n) V (γ ^ n) (K / (1 - γ)) := by
  obtain ⟨hγ0, hγ1⟩ := h.gamma_mem
  exact ⟨h.V_nonneg, h.V_measurable, ⟨pow_pos hγ0 n, pow_lt_one₀ hγ0.le hγ1 hn.ne'⟩,
    div_nonneg h.K_nonneg (by linarith), fun x => h.lintegral_pow_le n x⟩


-- ## REFUTATION of `harris_contraction` against the *old* `weightedTV` (historical record)
--
-- Everything from here to the end of the `cNoContraction` block is **demoted to a comment**:
-- it was a machine-checked refutation of `harris_contraction` as stated against the previous,
-- `singularPart`-based `weightedTV`, and it no longer type-checks against the repaired
-- definition — which is exactly the outcome one wants.  Re-run on the repaired `weightedTV`
-- the same data is no longer a counterexample: `|μ − ν|` is `½δ₀ + ½δ₁`, so the distance is
-- `1 + 10β`, and after one step `|δ₂ − (½δ₀+½δ₂)| = ½δ₀ + ½δ₂` gives `1 + 5.5β < 1 + 10β`.
-- The analysis is kept because it is the reason the definition reads the way it now does.
--
-- `weightedTV` used to be built from `Measure.singularPart`, **not** from the Jordan decomposition
-- of the signed difference `μ − ν`: it sees only the parts of `μ` and `ν` that are *mutually
-- singular*, and drops every absolutely-continuous overlap.  (In particular `weightedTV β V μ ν
-- = 0` whenever `μ ≪ ν ≪ μ` with `μ ≠ ν`, so it does not separate measures.)  That makes the
-- frozen contraction statement false: mixing an `ε` of one law into the other can annihilate an
-- arbitrarily large share of the right-hand side while leaving the left-hand side untouched.
--
-- The witness below lives on `ℕ` with `V = (0, 20, 11, 11, …)`, `γ = 1/2`, `K = 1`, `R = 10`
-- (so `2K/(1−γ) = 4 < 10`), `α = 1`, `ρ = δ₀`, and the deterministic kernel `1 ↦ 2`, `n ↦ 0`
-- otherwise.  For `μ = δ₁` and `ν = ½δ₀ + ½δ₁`:
--   * `μ` is `ν`-absolutely continuous, so `singularPart μ ν = 0` and `weightedTV β V μ ν
--     = ∫(1+βV) d(½δ₀) = ½`;
--   * one step sends `μ ↦ δ₂` and `ν ↦ ½δ₀ + ½δ₂`, the *same* configuration, so the pushed
--     distance is again `½`.
-- Hence `½ ≤ ᾱ · ½` for every admissible `β`, forcing `1 ≤ ᾱ` — no `ᾱ < 1` can work.
-- `cNoContraction (harris_contraction cDrift cMinorize cHR)` has type `False` (checked).
--
-- The defect is *only* about `weightedTV`: every kernel below is a Dirac, so `V` is integrable
-- at every step and the Bochner/`∫⁻` forms of the drift agree.  The counterexample therefore
-- survives the drift repair described before `harris_theorem`.
--
-- The repair is to define `weightedTV` from the Jordan decomposition of `μ − ν` (equivalently,
-- from a Hahn set for the pair), which is what Hairer–Mattingly's `ρ_β` actually is.  With that
-- definition the contraction *is* provable without any coupling step: writing `μ − ν = a − b`
-- with `a ⊥ b` and `a S = b S = c`, one subtracts the common minorization mass
-- `m = α·min(a L, b L)·ρ` from both `a.bind κ` and `b.bind κ` (Jordan minimality gives
-- `a₁ ≤ a.bind κ − m`, `b₁ ≤ b.bind κ − m`), and the drift plus Markov's inequality
-- `a Lᶜ ≤ (∫V da)/R` close the estimate with
-- `ᾱ = max (1 + βK − α) (γ + 2α/(βR))` for any `2α/(R(1−γ)) < β < α/K`; such a `β` exists
-- exactly when `2K/(1−γ) < R`, i.e. under `hR`.  (The equal masses `a S = b S` are what the
-- `singularPart` version lacks, and are the whole reason the frozen version fails.)

/- BEGIN historical refutation block (does not compile against the repaired `weightedTV`).

/-- Counterexample data: `V 0 = 0`, `V 1 = 20`, `V n = 11` otherwise. -/
private noncomputable def cV : ℕ → ℝ := fun n => if n = 0 then 0 else if n = 1 then 20 else 11

/-- Counterexample kernel: `1 ↦ 2`, everything else `↦ 0`. -/
private noncomputable def cK : Kernel ℕ ℕ :=
  ⟨fun n => if n = 1 then Measure.dirac 2 else Measure.dirac 0, Measurable.of_discrete⟩

private theorem cK_apply (n : ℕ) :
    cK n = if n = 1 then Measure.dirac 2 else Measure.dirac 0 := rfl

private instance : IsMarkovKernel cK :=
  ⟨fun n => by rw [cK_apply]; split <;> infer_instance⟩

/-- The half-and-half mixture `½δ_a + ½δ_b`. -/
private noncomputable def cMix (a b : ℕ) : Measure ℕ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac a + (2 : ℝ≥0∞)⁻¹ • Measure.dirac b

private instance (a b : ℕ) : IsProbabilityMeasure (cMix a b) := by
  refine ⟨?_⟩
  rw [cMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [measure_univ, mul_one]
  exact ENNReal.inv_two_add_inv_two

private theorem cMix_apply (a b : ℕ) (s : Set ℕ) :
    cMix a b s = (2 : ℝ≥0∞)⁻¹ * Measure.dirac a s + (2 : ℝ≥0∞)⁻¹ * Measure.dirac b s := by
  rw [cMix, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]

private theorem sing_dirac_mix (a b : ℕ) :
    (Measure.dirac b : Measure ℕ).singularPart (cMix a b) = 0 := by
  refine (Measure.singularPart_eq_zero _ _).2 ?_
  refine Measure.AbsolutelyContinuous.mk fun s hs hzero => ?_
  rw [cMix_apply] at hzero
  have h := (add_eq_zero.1 hzero).2
  simpa using h

private theorem sing_mix_dirac (a b : ℕ) (hab : a ≠ b) :
    (cMix a b).singularPart (Measure.dirac b) = (2 : ℝ≥0∞)⁻¹ • Measure.dirac a := by
  refine (Measure.eq_singularPart (f := fun _ => (2 : ℝ≥0∞)⁻¹) measurable_const ?_ ?_).symm
  · refine ⟨{a}ᶜ, (MeasurableSet.singleton a).compl, ?_, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (MeasurableSet.singleton a).compl]
      simp
    · rw [compl_compl, Measure.dirac_apply' _ (MeasurableSet.singleton a)]
      simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
      exact if_neg fun h => hab h.symm
  · rw [withDensity_const, cMix]

private theorem lintegral_smul_dirac (c : ℝ≥0∞) (a : ℕ) (f : ℕ → ℝ≥0∞) :
    ∫⁻ x, f x ∂(c • Measure.dirac a) = c * f a := by
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

private theorem cWeightedTV (β : ℝ) (a b : ℕ) (hab : a ≠ b) :
    weightedTV β cV (Measure.dirac b) (cMix a b)
      = (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (1 + β * cV a) := by
  rw [weightedTV, sing_dirac_mix, sing_mix_dirac a b hab, lintegral_zero_measure, zero_add,
    lintegral_smul_dirac]


private theorem cDrift : HasLyapunovDrift cK cV (1/2) 1 where
  V_nonneg x := by rw [cV]; split_ifs <;> norm_num
  V_measurable := Measurable.of_discrete
  gamma_mem := ⟨by norm_num, by norm_num⟩
  K_nonneg := by norm_num
  drift x := by
    have hnn : ∀ y : ℕ, (0:ℝ) ≤ cV y := fun y => by rw [cV]; split_ifs <;> norm_num
    rw [cK_apply]
    split_ifs with h
    · subst h
      rw [integral_dirac]
      norm_num [cV]
    · rw [integral_dirac]
      have : cV 0 = 0 := by norm_num [cV]
      rw [this]
      nlinarith [hnn x]

private theorem cMinorize : HasMinorization cK cV 10 1 (Measure.dirac 0) where
  alpha_mem := ⟨one_pos, le_rfl⟩
  isProbability := inferInstance
  minorize x hx A _ := by
    have hx0 : x = 0 := by
      by_contra hne
      rw [cV, if_neg hne] at hx
      split_ifs at hx <;> norm_num at hx
    subst hx0
    rw [cK_apply, if_neg (by norm_num), ENNReal.ofReal_one, one_mul]

private theorem cHR : 2 * (1:ℝ) / (1 - 1/2) < 10 := by norm_num

private theorem cNoContraction :
    ¬ ∃ β ᾱ : ℝ, 0 < β ∧ 0 < ᾱ ∧ ᾱ < 1 ∧
      ∀ μ ν : Measure ℕ, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        weightedTV β cV (μ.bind cK) (ν.bind cK) ≤ ENNReal.ofReal ᾱ * weightedTV β cV μ ν := by
  rintro ⟨β, ᾱ, hβ, hα0, hα1, h⟩
  have hV0 : cV 0 = 0 := by norm_num [cV]
  have hbind1 : (Measure.dirac 1 : Measure ℕ).bind cK = Measure.dirac 2 := by
    rw [Measure.dirac_bind cK.measurable, cK_apply, if_pos rfl]
  have hbind0 : (Measure.dirac 0 : Measure ℕ).bind cK = Measure.dirac 0 := by
    rw [Measure.dirac_bind cK.measurable, cK_apply, if_neg (by norm_num)]
  have hbindmix : (cMix 0 1).bind cK = cMix 0 2 := by
    rw [cMix, bind_add', Measure.bind_smul, Measure.bind_smul, hbind0, hbind1, cMix]
  have key := h (Measure.dirac 1) (cMix 0 1) inferInstance inferInstance
  rw [hbind1, hbindmix, cWeightedTV β 0 2 (by norm_num), cWeightedTV β 0 1 (by norm_num),
    hV0] at key
  norm_num at key
  have hcancel : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ᾱ := by
    have h2 : (1 : ℝ≥0∞) * (2:ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal ᾱ * (2:ℝ≥0∞)⁻¹ := by
      rw [one_mul]; exact key
    exact (ENNReal.mul_le_mul_iff_left (by simp) (by simp)).1 h2
  have : ENNReal.ofReal ᾱ < 1 := ENNReal.ofReal_lt_one.2 hα1
  exact absurd hcancel (not_le.2 this)

END historical refutation block. -/

-- The minorization, integrated: one step from any initial law dominates `α·ρ` on the mass that
-- the law puts on the level set.
private theorem minorize_bind {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {R α : ℝ}
    {ρ : Measure S} (hmin : HasMinorization κ V R α ρ)
    (ξ : Measure S) {A : Set S} (hA : MeasurableSet A) :
    ENNReal.ofReal α * ρ A * ξ {x | V x ≤ R} ≤ (ξ.bind κ) A := by
  rw [Measure.bind_apply hA κ.aemeasurable]
  calc ENNReal.ofReal α * ρ A * ξ {x | V x ≤ R}
      = ∫⁻ _ in {x | V x ≤ R}, ENNReal.ofReal α * ρ A ∂ξ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in {x | V x ≤ R}, κ x A ∂ξ :=
        setLIntegral_mono (κ.measurable_coe hA) fun x hx => hmin.minorize x hx A hA
    _ ≤ ∫⁻ x, κ x A ∂ξ := setLIntegral_le_lintegral _ _


/-! ### The three analytic inputs of the contraction -/

-- The drift, read on the weight `1 + βV`: one kernel step of the weight is bounded by the affine
-- function `1 + βK + βγ·V` of the current state.
private theorem drift_weight {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {β : ℝ} (hβ : 0 ≤ β) (x : S) :
    ∫⁻ y, ENNReal.ofReal (1 + β * V y) ∂(κ x)
      ≤ ENNReal.ofReal (1 + β * K + β * γ * V x) := by
  have hVm : Measurable fun y => ENNReal.ofReal (V y) :=
    ENNReal.measurable_ofReal.comp hdrift.V_measurable
  have hnn : (0:ℝ) ≤ β * (γ * V x + K) :=
    mul_nonneg hβ (add_nonneg (mul_nonneg hdrift.gamma_mem.1.le (hdrift.V_nonneg x))
      hdrift.K_nonneg)
  calc ∫⁻ y, ENNReal.ofReal (1 + β * V y) ∂(κ x)
      = ∫⁻ y, (1 + ENNReal.ofReal β * ENNReal.ofReal (V y)) ∂(κ x) :=
        lintegral_congr fun y => by
          rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hβ (hdrift.V_nonneg y)),
            ENNReal.ofReal_mul hβ, ENNReal.ofReal_one]
    _ = 1 + ENNReal.ofReal β * ∫⁻ y, ENNReal.ofReal (V y) ∂(κ x) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ hVm]
    _ ≤ 1 + ENNReal.ofReal β * ENNReal.ofReal (γ * V x + K) :=
        add_le_add le_rfl (mul_le_mul_right (hdrift.drift x) _)
    _ = ENNReal.ofReal (1 + β * (γ * V x + K)) := by
        rw [ENNReal.ofReal_add zero_le_one hnn, ENNReal.ofReal_one, ENNReal.ofReal_mul hβ]
    _ = ENNReal.ofReal (1 + β * K + β * γ * V x) := by congr 1; ring

-- The weight is affine in `V`, so its `ξ`-mass splits into a mass term and a `V`-term.
private theorem lintegral_affine_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {V : S → ℝ}
    (hVm : Measurable V) (hVnn : ∀ x, 0 ≤ V x) (ξ : Measure S) :
    ∫⁻ x, ENNReal.ofReal (a + b * V x) ∂ξ
      = ENNReal.ofReal a * ξ Set.univ + ENNReal.ofReal b * ∫⁻ x, ENNReal.ofReal (V x) ∂ξ := by
  have hVe : Measurable fun x => ENNReal.ofReal (V x) := ENNReal.measurable_ofReal.comp hVm
  have h : ∀ x, ENNReal.ofReal (a + b * V x)
      = ENNReal.ofReal a + ENNReal.ofReal b * ENNReal.ofReal (V x) := fun x => by
    rw [ENNReal.ofReal_add ha (mul_nonneg hb (hVnn x)), ENNReal.ofReal_mul hb]
  rw [lintegral_congr h, lintegral_add_left measurable_const, lintegral_const,
    lintegral_const_mul _ hVe]

-- Markov's inequality on the level set `{V ≤ R}`: the mass outside it costs `∫ V / R`.
private theorem markov_level {V : S → ℝ} (hVm : Measurable V) (_hVnn : ∀ x, 0 ≤ V x)
    {R : ℝ} (_hR : 0 ≤ R) (ξ : Measure S) :
    ENNReal.ofReal R * ξ Set.univ
      ≤ ENNReal.ofReal R * ξ {x | V x ≤ R} + ∫⁻ x, ENNReal.ofReal (V x) ∂ξ := by
  have hms : MeasurableSet {x | V x ≤ R} := hVm measurableSet_Iic
  have hVe : Measurable fun x => ENNReal.ofReal (V x) := ENNReal.measurable_ofReal.comp hVm
  have hsub : {x | V x ≤ R}ᶜ ⊆ {x | ENNReal.ofReal R ≤ ENNReal.ofReal (V x)} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
    exact ENNReal.ofReal_le_ofReal hx.le
  have hmk : ENNReal.ofReal R * ξ {x | V x ≤ R}ᶜ ≤ ∫⁻ x, ENNReal.ofReal (V x) ∂ξ :=
    le_trans (mul_le_mul_right (measure_mono hsub) _)
      (mul_meas_ge_le_lintegral₀ hVe.aemeasurable _)
  rw [← measure_add_measure_compl (μ := ξ) hms, mul_add]
  exact add_le_add le_rfl hmk

-- The scalar heart of the Hairer–Mattingly estimate, isolated from all measure theory: with
-- `ᾱ ≥ max (1 + βK − α) (γ + 2α/(βR))` the drift bound plus the Markov bound close the loop.
-- No finiteness is needed anywhere — every step is monotone.
private theorem harris_num {β γ K R α ᾱ : ℝ} (hβ : 0 < β) (hγ0 : 0 < γ) (_hK : 0 ≤ K)
    (hRpos : 0 < R) (hα0 : 0 < α) (hᾱ0 : 0 < ᾱ)
    (h1 : 1 + β * K - α ≤ ᾱ) (h2 : γ + 2 * α / (β * R) ≤ ᾱ)
    (c Va Vb mL : ℝ≥0∞)
    (hmark : ENNReal.ofReal R * c ≤ ENNReal.ofReal R * mL + (Va + Vb)) :
    (ENNReal.ofReal (1 + β * K) * c + ENNReal.ofReal (β * γ) * Va)
      + (ENNReal.ofReal (1 + β * K) * c + ENNReal.ofReal (β * γ) * Vb)
      ≤ ENNReal.ofReal ᾱ * ((c + ENNReal.ofReal β * Va) + (c + ENNReal.ofReal β * Vb))
        + (ENNReal.ofReal α * mL + ENNReal.ofReal α * mL) := by
  have hRne : (R : ℝ) ≠ 0 := hRpos.ne'
  have hβne : (β : ℝ) ≠ 0 := hβ.ne'
  have h2αR : (0:ℝ) ≤ 2 * α / R := (div_pos (by linarith) hRpos).le
  -- (i) `1 + βK ≤ ᾱ + α`
  have e1 : ENNReal.ofReal (1 + β * K) ≤ ENNReal.ofReal ᾱ + ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_add hᾱ0.le hα0.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hcoef : ENNReal.ofReal (2 * α / R) * ENNReal.ofReal R
      = ENNReal.ofReal α + ENNReal.ofReal α := by
    rw [← ENNReal.ofReal_mul h2αR, ← ENNReal.ofReal_add hα0.le hα0.le]
    congr 1
    field_simp
    ring
  -- (ii) Markov's inequality, scaled by `2α/R`
  have e2 : ENNReal.ofReal α * c + ENNReal.ofReal α * c
      ≤ (ENNReal.ofReal α * mL + ENNReal.ofReal α * mL)
        + ENNReal.ofReal (2 * α / R) * (Va + Vb) := by
    have h := mul_le_mul_right hmark (ENNReal.ofReal (2 * α / R))
    calc ENNReal.ofReal α * c + ENNReal.ofReal α * c
        = ENNReal.ofReal (2 * α / R) * (ENNReal.ofReal R * c) := by
          rw [← mul_assoc, hcoef, add_mul]
      _ ≤ ENNReal.ofReal (2 * α / R) * (ENNReal.ofReal R * mL + (Va + Vb)) := h
      _ = ENNReal.ofReal (2 * α / R) * ENNReal.ofReal R * mL
            + ENNReal.ofReal (2 * α / R) * (Va + Vb) := by ring
      _ = _ := by rw [hcoef, add_mul]
  -- (iii) `βγ + 2α/R ≤ ᾱβ`
  have e3 : ENNReal.ofReal (β * γ) + ENNReal.ofReal (2 * α / R)
      ≤ ENNReal.ofReal ᾱ * ENNReal.ofReal β := by
    rw [← ENNReal.ofReal_add (mul_nonneg hβ.le hγ0.le) h2αR, ← ENNReal.ofReal_mul hᾱ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmul : (γ + 2 * α / (β * R)) * β ≤ ᾱ * β := mul_le_mul_of_nonneg_right h2 hβ.le
    have hrw : (γ + 2 * α / (β * R)) * β = β * γ + 2 * α / R := by field_simp
    linarith [hrw ▸ hmul]
  calc (ENNReal.ofReal (1 + β * K) * c + ENNReal.ofReal (β * γ) * Va)
        + (ENNReal.ofReal (1 + β * K) * c + ENNReal.ofReal (β * γ) * Vb)
      = (ENNReal.ofReal (1 + β * K) * c + ENNReal.ofReal (1 + β * K) * c)
          + ENNReal.ofReal (β * γ) * (Va + Vb) := by ring
    _ ≤ ((ENNReal.ofReal ᾱ + ENNReal.ofReal α) * c + (ENNReal.ofReal ᾱ + ENNReal.ofReal α) * c)
          + ENNReal.ofReal (β * γ) * (Va + Vb) :=
        add_le_add (add_le_add (mul_le_mul_left e1 c) (mul_le_mul_left e1 c)) le_rfl
    _ = (ENNReal.ofReal ᾱ * c + ENNReal.ofReal ᾱ * c)
          + ((ENNReal.ofReal α * c + ENNReal.ofReal α * c)
              + ENNReal.ofReal (β * γ) * (Va + Vb)) := by ring
    _ ≤ (ENNReal.ofReal ᾱ * c + ENNReal.ofReal ᾱ * c)
          + (((ENNReal.ofReal α * mL + ENNReal.ofReal α * mL)
              + ENNReal.ofReal (2 * α / R) * (Va + Vb))
              + ENNReal.ofReal (β * γ) * (Va + Vb)) :=
        add_le_add le_rfl (add_le_add e2 le_rfl)
    _ = (ENNReal.ofReal ᾱ * c + ENNReal.ofReal ᾱ * c)
          + (ENNReal.ofReal (β * γ) + ENNReal.ofReal (2 * α / R)) * (Va + Vb)
          + (ENNReal.ofReal α * mL + ENNReal.ofReal α * mL) := by ring
    _ ≤ (ENNReal.ofReal ᾱ * c + ENNReal.ofReal ᾱ * c)
          + ENNReal.ofReal ᾱ * ENNReal.ofReal β * (Va + Vb)
          + (ENNReal.ofReal α * mL + ENNReal.ofReal α * mL) :=
        add_le_add (add_le_add le_rfl (mul_le_mul_left e3 _)) le_rfl
    _ = _ := by ring

-- The contraction estimate at a fixed admissible pair `(β, ᾱ)`. This is where the Jordan
-- minimality lemma `jPos_add_le_of_add_eq` does the work that Hairer–Mattingly do by coupling.
private theorem harris_contraction_aux {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ}
    {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) {β ᾱ : ℝ} (hβpos : 0 < β) (hᾱpos : 0 < ᾱ)
    (hRpos : 0 < R) (hᾱ1 : 1 + β * K - α ≤ ᾱ) (hᾱ2 : γ + 2 * α / (β * R) ≤ ᾱ)
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    weightedTV β V (μ.bind κ) (ν.bind κ) ≤ ENNReal.ofReal ᾱ * weightedTV β V μ ν := by
  haveI := hmin.isProbability
  obtain ⟨hγ0, hγ1⟩ := hdrift.gamma_mem
  obtain ⟨hα0, hα1⟩ := hmin.alpha_mem
  have hK := hdrift.K_nonneg
  have hVnn := hdrift.V_nonneg
  have hVm := hdrift.V_measurable
  have hwm : Measurable fun x => ENNReal.ofReal (1 + β * V x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul hVm))
  haveI : IsProbabilityMeasure (μ.bind κ) :=
    ⟨by rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]; simp⟩
  haveI : IsProbabilityMeasure (ν.bind κ) :=
    ⟨by rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]; simp⟩
  obtain ⟨mL, hmL⟩ : ∃ t : ℝ≥0∞,
      t = min ((jPos μ ν) {x | V x ≤ R}) ((jPos ν μ) {x | V x ≤ R}) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ n : Measure S, n = (ENNReal.ofReal α * mL) • ρ := ⟨_, rfl⟩
  -- the common minorization mass sits under both pushed Jordan parts
  have hmle : ∀ ξ : Measure S, mL ≤ ξ {x | V x ≤ R} → m ≤ ξ.bind κ := by
    intro ξ hξ
    refine Measure.le_iff.2 fun t ht => ?_
    rw [hm, Measure.smul_apply, smul_eq_mul, mul_right_comm]
    exact le_trans (mul_le_mul_right hξ _) (minorize_bind hmin ξ ht)
  have hmA : m ≤ (jPos μ ν).bind κ := hmle _ (by rw [hmL]; exact min_le_left _ _)
  have hmB : m ≤ (jPos ν μ).bind κ := hmle _ (by rw [hmL]; exact min_le_right _ _)
  -- one kernel step of the Jordan identity, then minimality
  have hid : (μ.bind κ) + (jPos ν μ).bind κ = (ν.bind κ) + (jPos μ ν).bind κ := by
    have h : (μ + jPos ν μ).bind κ = (ν + jPos μ ν).bind κ := by rw [add_jPos_comm]
    rwa [bind_add', bind_add'] at h
  have hA : jPos (μ.bind κ) (ν.bind κ) + m ≤ (jPos μ ν).bind κ :=
    jPos_add_le_of_add_eq hid hmA hmB
  have hB : jPos (ν.bind κ) (μ.bind κ) + m ≤ (jPos ν μ).bind κ :=
    jPos_add_le_of_add_eq hid.symm hmB hmA
  have hintA : (∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (μ.bind κ) (ν.bind κ)))
      + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂m
      ≤ ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂((jPos μ ν).bind κ) := by
    rw [← lintegral_add_measure]
    exact lintegral_mono' hA le_rfl
  have hintB : (∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (ν.bind κ) (μ.bind κ)))
      + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂m
      ≤ ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂((jPos ν μ).bind κ) := by
    rw [← lintegral_add_measure]
    exact lintegral_mono' hB le_rfl
  -- the minorization mass, measured in the weight (the weight is `≥ 1`)
  have hJm : ENNReal.ofReal α * mL ≤ ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂m := by
    rw [hm, lintegral_smul_measure]
    refine le_mul_of_one_le_right' ?_
    calc (1:ℝ≥0∞) = ∫⁻ _, (1:ℝ≥0∞) ∂ρ := by rw [lintegral_one, measure_univ]
      _ ≤ ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂ρ :=
          lintegral_mono fun x => by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (by nlinarith [hVnn x])
  -- the drift, integrated against each Jordan part
  have hdriftint : ∀ ξ : Measure S, ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(ξ.bind κ)
      ≤ ENNReal.ofReal (1 + β * K) * ξ Set.univ
        + ENNReal.ofReal (β * γ) * ∫⁻ x, ENNReal.ofReal (V x) ∂ξ := by
    intro ξ
    rw [Measure.lintegral_bind κ.aemeasurable hwm.aemeasurable]
    calc ∫⁻ x, (∫⁻ y, ENNReal.ofReal (1 + β * V y) ∂(κ x)) ∂ξ
        ≤ ∫⁻ x, ENNReal.ofReal (1 + β * K + β * γ * V x) ∂ξ :=
          lintegral_mono fun x => drift_weight hdrift hβpos.le x
      _ = _ := lintegral_affine_ofReal (by nlinarith [mul_nonneg hβpos.le hK])
                (mul_nonneg hβpos.le hγ0.le) hVm hVnn _
  -- Markov's inequality on the smaller of the two level-set masses
  have hmark : ENNReal.ofReal R * (jPos μ ν) Set.univ
      ≤ ENNReal.ofReal R * mL
        + ((∫⁻ x, ENNReal.ofReal (V x) ∂(jPos μ ν))
            + ∫⁻ x, ENNReal.ofReal (V x) ∂(jPos ν μ)) := by
    rcases min_cases ((jPos μ ν) {x | V x ≤ R}) ((jPos ν μ) {x | V x ≤ R}) with
      ⟨he, _⟩ | ⟨he, _⟩
    · rw [hmL, he]
      exact le_trans (markov_level hVm hVnn hRpos.le _) (add_le_add le_rfl le_self_add)
    · rw [hmL, he, jPos_mass_eq μ ν]
      exact le_trans (markov_level hVm hVnn hRpos.le _) (add_le_add le_rfl le_add_self)
  -- the two distances, in the mass/`V` coordinates
  have hWmu : weightedTV β V μ ν
      = ((jPos μ ν) Set.univ + ENNReal.ofReal β * ∫⁻ x, ENNReal.ofReal (V x) ∂(jPos μ ν))
        + ((jPos μ ν) Set.univ
            + ENNReal.ofReal β * ∫⁻ x, ENNReal.ofReal (V x) ∂(jPos ν μ)) := by
    rw [weightedTV_eq β hVm μ ν, lintegral_affine_ofReal zero_le_one hβpos.le hVm hVnn,
      lintegral_affine_ofReal zero_le_one hβpos.le hVm hVnn, ENNReal.ofReal_one, one_mul,
      one_mul, ← jPos_mass_eq μ ν]
  -- the doubled minorization mass is finite, so it can be cancelled at the end
  have hmLne : mL ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top (jPos μ ν) _) (by rw [hmL]; exact min_le_left _ _)
  have hfin : ENNReal.ofReal α * mL + ENNReal.ofReal α * mL ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmLne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmLne⟩
  rw [weightedTV_eq β hVm (μ.bind κ) (ν.bind κ), hWmu]
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  calc ((∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (μ.bind κ) (ν.bind κ)))
          + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (ν.bind κ) (μ.bind κ)))
        + (ENNReal.ofReal α * mL + ENNReal.ofReal α * mL)
      ≤ ((∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (μ.bind κ) (ν.bind κ)))
            + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂m)
          + ((∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (ν.bind κ) (μ.bind κ)))
            + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂m) := by
        have hrw : ((∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (μ.bind κ) (ν.bind κ)))
              + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (ν.bind κ) (μ.bind κ)))
              + (ENNReal.ofReal α * mL + ENNReal.ofReal α * mL)
            = ((∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (μ.bind κ) (ν.bind κ)))
                + ENNReal.ofReal α * mL)
              + ((∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos (ν.bind κ) (μ.bind κ)))
                + ENNReal.ofReal α * mL) := by ring
        rw [hrw]
        exact add_le_add (add_le_add le_rfl hJm) (add_le_add le_rfl hJm)
    _ ≤ (∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂((jPos μ ν).bind κ))
          + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂((jPos ν μ).bind κ) := add_le_add hintA hintB
    _ ≤ (ENNReal.ofReal (1 + β * K) * (jPos μ ν) Set.univ
            + ENNReal.ofReal (β * γ) * ∫⁻ x, ENNReal.ofReal (V x) ∂(jPos μ ν))
          + (ENNReal.ofReal (1 + β * K) * (jPos μ ν) Set.univ
            + ENNReal.ofReal (β * γ) * ∫⁻ x, ENNReal.ofReal (V x) ∂(jPos ν μ)) := by
        refine add_le_add (hdriftint (jPos μ ν)) ?_
        rw [jPos_mass_eq μ ν]
        exact hdriftint (jPos ν μ)
    _ ≤ _ := harris_num hβpos hγ0 hK hRpos hα0 hᾱpos hᾱ1 hᾱ2 _ _ _ _ hmark

/-- **Harris contraction** (Hairer–Mattingly Theorem 1.3): under a Lyapunov drift and a
minorization on a high enough level set, the kernel contracts the weighted TV distance
`weightedTV β V` for a suitable `β > 0`, uniformly over initial laws. -/
theorem harris_contraction {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ)
    -- USER-INPUT: the level set is high enough to see the drift (H–M Thm 1.3);
    -- `R > 2K/(1 − γ)`
    (hR : 2 * K / (1 - γ) < R) :
    ∃ β ᾱ : ℝ, 0 < β ∧ 0 < ᾱ ∧ ᾱ < 1 ∧
      ∀ μ ν : Measure S, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        weightedTV β V (μ.bind κ) (ν.bind κ)
          ≤ ENNReal.ofReal ᾱ * weightedTV β V μ ν := by
  obtain ⟨hγ0, hγ1⟩ := hdrift.gamma_mem
  obtain ⟨hα0, hα1⟩ := hmin.alpha_mem
  have hK := hdrift.K_nonneg
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  have hRpos : (0:ℝ) < R := lt_of_le_of_lt (by positivity) hR
  have hKR : 2 * K < R * (1 - γ) := by rw [div_lt_iff₀ h1γ] at hR; linarith
  -- the admissible window `2α/(R(1−γ)) < β < α/K` is nonempty *exactly* under `hR`
  obtain ⟨b0, hb0pos, hb0K, hb0R⟩ :
      ∃ b : ℝ, 0 < b ∧ b * K < α ∧ b * (R * (1 - γ)) = 2 * α := by
    have hne : R * (1 - γ) ≠ 0 := (mul_pos hRpos h1γ).ne'
    refine ⟨2 * α / (R * (1 - γ)), div_pos (by linarith) (mul_pos hRpos h1γ), ?_, by field_simp⟩
    rw [div_mul_eq_mul_div, div_lt_iff₀ (mul_pos hRpos h1γ)]
    nlinarith [mul_lt_mul_of_pos_left hKR hα0]
  obtain ⟨β, hβpos, hβK, hβR⟩ :
      ∃ β : ℝ, 0 < β ∧ β * K < α ∧ 2 * α < β * (R * (1 - γ)) := by
    have hE : (0:ℝ) < α - b0 * K := by linarith
    have hd : (0:ℝ) < (α - b0 * K) / (2 * (K + 1)) := div_pos hE (by linarith)
    refine ⟨b0 + (α - b0 * K) / (2 * (K + 1)), by linarith, ?_, ?_⟩
    · have hlt : (α - b0 * K) / (2 * (K + 1)) * K < α - b0 * K := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : (0:ℝ) < 2 * (K + 1))]
        nlinarith
      rw [add_mul]
      linarith
    · rw [add_mul, hb0R]
      nlinarith [mul_pos hd (mul_pos hRpos h1γ)]
  obtain ⟨ᾱ, hᾱ1, hᾱ2, hᾱpos, hᾱlt⟩ :
      ∃ a : ℝ, 1 + β * K - α ≤ a ∧ γ + 2 * α / (β * R) ≤ a ∧ 0 < a ∧ a < 1 := by
    refine ⟨max (1 + β * K - α) (γ + 2 * α / (β * R)), le_max_left _ _, le_max_right _ _, ?_, ?_⟩
    · refine lt_of_lt_of_le ?_ (le_max_right _ _)
      have : (0:ℝ) < 2 * α / (β * R) := div_pos (by linarith) (mul_pos hβpos hRpos)
      linarith
    · refine max_lt (by linarith) ?_
      have hlt : 2 * α / (β * R) < 1 - γ := by
        rw [div_lt_iff₀ (mul_pos hβpos hRpos)]
        nlinarith
      linarith
  refine ⟨β, ᾱ, hβpos, hᾱpos, hᾱlt, fun μ ν hμ hν => ?_⟩
  haveI := hμ
  haveI := hν
  exact harris_contraction_aux hdrift hmin hβpos hᾱpos hRpos hᾱ1 hᾱ2 μ ν

-- ## REFUTATION of `harris_theorem` against the *old* Bochner drift (historical record)
--
-- As with the block above, everything down to the end of `tNoErgodic` is **demoted to a
-- comment**: it refuted `harris_theorem` as stated against the previous, Bochner-integral
-- form of `HasLyapunovDrift.drift`, and `tDrift` no longer type-checks — because with the
-- `∫⁻` drift the witness kernel simply *fails* the hypothesis at every nonzero state
-- (`∫⁻ V dν = ∞ > ofReal (γ V x + K)`), which is precisely the repair.  The chain itself is
-- still genuinely non-ergodic; it is only the drift hypothesis that it no longer satisfies.
--
-- `HasLyapunovDrift.drift` used to be stated with the **Bochner** integral `∫ y, V y ∂(κ x)`, which
-- Mathlib defines to be `0` when the integrand is not integrable (`integral_undef`).  Since
-- `V ≥ 0` and `γ V x + K ≥ 0`, the drift hypothesis is therefore **vacuous at every state `x`
-- where `∫⁻ V d(κ x) = ∞`** — it constrains nothing there.  A chain may then leave the level set
-- forever, and both existence *and* uniqueness of an attracting law fail.
--
-- The witness below lives on `ℕ` with `V 0 = 0`, `V n = 4ⁿ` (`n ≥ 1`), `γ = 1/2`, `K = 0`,
-- `R = 1` (so `2K/(1−γ) = 0 < 1`), `α = 1`, `ρ = δ₀`, and the kernel `0 ↦ δ₀`, `n ↦ ν`
-- (`n ≥ 1`) for the heavy-tailed law `ν = Σⱼ 2^{-(j+1)} δ_{j+1}`, which satisfies
-- `∫⁻ V dν = Σⱼ 2^{j+1} = ∞`.  The level set is `{0}`, where the minorization is exact; the
-- drift holds genuinely at `0` and vacuously everywhere else.  But `κⁿ(0,·) = δ₀` and
-- `κⁿ(1,·) = ν` for all `n ≥ 1`, and `δ₀ ≠ ν`, so no single law attracts every state:
-- `tNoErgodic (harris_theorem tDrift tMinorize tHR)` has type `False` (checked).
--
-- The repair is at the level of `HasLyapunovDrift`: state the drift as
-- `∫⁻ y, ENNReal.ofReal (V y) ∂(κ x) ≤ ENNReal.ofReal (γ * V x + K)` (or add `∀ x, Integrable V
-- (κ x)`).  `harris_invariant_unique` above is unaffected: its `Integrable V π` hypotheses buy
-- exactly the `π`-a.e. `∫⁻` form of the drift, which is what `drift_lintegral_ae` extracts.

/- BEGIN historical refutation block (does not compile against the repaired `drift`).

private noncomputable def tV : ℕ → ℝ := fun n => if n = 0 then 0 else 4 ^ n

private noncomputable def tNu : Measure ℕ :=
  Measure.sum fun j : ℕ => ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) • Measure.dirac (j + 1)

private noncomputable def tK : Kernel ℕ ℕ :=
  ⟨fun n => if n = 0 then Measure.dirac 0 else tNu, Measurable.of_discrete⟩

private theorem tK_apply (n : ℕ) : tK n = if n = 0 then Measure.dirac 0 else tNu := rfl

private theorem tNu_apply {s : Set ℕ} (hs : MeasurableSet s) :
    tNu s = ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * Measure.dirac (j + 1) s := by
  rw [tNu, Measure.sum_apply _ hs]
  exact tsum_congr fun j => by rw [Measure.smul_apply, smul_eq_mul]

private theorem tsum_half : ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) = 1 := by
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) = ((2 : ℝ≥0∞)⁻¹) ^ j * (2 : ℝ≥0∞)⁻¹ :=
    fun j => pow_succ _ _
  rw [tsum_congr h, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
    inv_inv]
  exact ENNReal.mul_inv_cancel two_ne_zero (by simp)

private instance : IsProbabilityMeasure tNu := by
  refine ⟨?_⟩
  rw [tNu_apply MeasurableSet.univ]
  simpa using tsum_half

private theorem tNu_zero : tNu {0} = 0 := by
  rw [tNu_apply (MeasurableSet.singleton 0)]
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * Measure.dirac (j + 1) {0} = 0 := by
    intro j
    rw [Measure.dirac_apply' _ (MeasurableSet.singleton 0)]
    simp
  rw [tsum_congr h, tsum_zero]

private instance : IsMarkovKernel tK :=
  ⟨fun n => by rw [tK_apply]; split <;> infer_instance⟩

private theorem tNu_not_integrable : ¬ Integrable tV tNu := by
  intro hint
  have hlt : ∫⁻ y, ENNReal.ofReal (tV y) ∂tNu < ∞ := by
    have h2 := hint.2
    rw [HasFiniteIntegral] at h2
    refine lt_of_le_of_lt (le_of_eq ?_) h2
    refine lintegral_congr fun y => (Real.enorm_eq_ofReal ?_).symm
    rw [tV]; split_ifs <;> positivity
  refine absurd hlt (not_lt.2 (le_of_eq ?_))
  symm
  rw [tNu, lintegral_sum_measure]
  have hterm : ∀ j : ℕ, ∫⁻ y, ENNReal.ofReal (tV y) ∂(((2 : ℝ≥0∞)⁻¹) ^ (j + 1) •
      Measure.dirac (j + 1)) = (2 : ℝ≥0∞) ^ (j + 1) := by
    intro j
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul, tV, if_neg (Nat.succ_ne_zero j),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4), ← mul_pow]
    norm_num
    congr 1
    rw [show (4:ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero (by simp), one_mul]
  rw [tsum_congr hterm]
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)) ^ (j + 1) = ((2 : ℝ≥0∞)) ^ j * (2 : ℝ≥0∞) :=
    fun j => pow_succ _ _
  rw [tsum_congr h, ENNReal.tsum_mul_right, ENNReal.tsum_geometric,
    show (1 : ℝ≥0∞) - 2 = 0 by simp [tsub_eq_zero_of_le], ENNReal.inv_zero,
    ENNReal.top_mul (by norm_num)]

private theorem tDrift : HasLyapunovDrift tK tV (1/2) 0 where
  V_nonneg x := by rw [tV]; split_ifs <;> positivity
  V_measurable := Measurable.of_discrete
  gamma_mem := ⟨by norm_num, by norm_num⟩
  K_nonneg := le_rfl
  drift x := by
    have hnn : (0:ℝ) ≤ tV x := by rw [tV]; split_ifs <;> positivity
    rw [tK_apply]
    split_ifs with h
    · subst h
      rw [integral_dirac]
      norm_num [tV]
    · rw [integral_undef tNu_not_integrable]
      nlinarith

private theorem tMinorize : HasMinorization tK tV 1 1 (Measure.dirac 0) where
  alpha_mem := ⟨one_pos, le_rfl⟩
  isProbability := inferInstance
  minorize x hx A _ := by
    have hx0 : x = 0 := by
      by_contra hne
      rw [tV, if_neg hne] at hx
      have : (4:ℝ) ^ x ≥ 4 ^ 1 := by
        refine pow_le_pow_right₀ (by norm_num) ?_
        omega
      norm_num at this
      linarith
    subst hx0
    rw [tK_apply, if_pos rfl, ENNReal.ofReal_one, one_mul]

private theorem tHR : 2 * (0:ℝ) / (1 - 1/2) < 1 := by norm_num


private theorem tNu_lintegral (f : ℕ → ℝ≥0∞) :
    ∫⁻ x, f x ∂tNu = ∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * f (j + 1) := by
  rw [tNu, lintegral_sum_measure]
  exact tsum_congr fun j => by rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

private theorem tNu_invariant : Kernel.Invariant tK tNu := by
  ext s hs
  rw [Measure.bind_apply hs tK.aemeasurable, tNu_lintegral]
  have h : ∀ j : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * (tK (j + 1)) s
      = ((2 : ℝ≥0∞)⁻¹) ^ (j + 1) * tNu s := by
    intro j; rw [tK_apply, if_neg (Nat.succ_ne_zero j)]
  rw [tsum_congr h, ENNReal.tsum_mul_right, tsum_half, one_mul]

private theorem tPow_succ_apply (n : ℕ) (x : ℕ) : (tK ^ (n + 1)) x = ((tK ^ n) x).bind tK := by
  rw [pow_succ']
  exact Kernel.comp_apply tK (tK ^ n) x

private theorem tK_pow_zero : ∀ n : ℕ, (tK ^ n) 0 = Measure.dirac 0
  | 0 => by rw [pow_zero]; rfl
  | n + 1 => by
      rw [tPow_succ_apply, tK_pow_zero n, Measure.dirac_bind tK.measurable, tK_apply, if_pos rfl]

private theorem tK_pow_one : ∀ n : ℕ, (tK ^ (n + 1)) 1 = tNu
  | 0 => by rw [pow_one, tK_apply, if_neg one_ne_zero]
  | n + 1 => by rw [tPow_succ_apply, tK_pow_one n]; exact tNu_invariant.def

private theorem tv_le_of_zero {μ ν : Measure ℕ} (h : tvDist μ ν = 0) {s : Set ℕ}
    (hs : MeasurableSet s) : μ s ≤ ν s := by
  have h1 : μ s - ν s ≤ tvDist μ ν :=
    le_iSup₂ (f := fun t (_ : MeasurableSet t) => μ t - ν t) s hs
  rw [h] at h1
  exact tsub_eq_zero_iff_le.mp (le_antisymm h1 (zero_le))

private theorem tNoErgodic : ¬ ∃ π : Measure ℕ, IsProbabilityMeasure π ∧
    Kernel.Invariant tK π ∧ IsGeometricallyErgodic tK π := by
  rintro ⟨π, hπp, -, ρ, hρ1, hrate⟩
  haveI := hπp
  have e0 : tvDist (Measure.dirac 0 : Measure ℕ) π = 0 := by
    have h : Tendsto (fun _ : ℕ => tvDist (Measure.dirac 0 : Measure ℕ) π) atTop (𝓝 0) := by
      simpa [tK_pow_zero] using hrate.tendsto_tvDist 0
    exact tendsto_nhds_unique (tendsto_const_nhds (α := ℕ) (f := atTop)) h
  have e1 : tvDist tNu π = 0 := by
    have h : Tendsto (fun _ : ℕ => tvDist tNu π) atTop (𝓝 0) := by
      have h2 := (hrate.tendsto_tvDist 1).comp (tendsto_add_atTop_nat 1)
      simp only [Function.comp_def, tK_pow_one] at h2
      exact h2
    exact tendsto_nhds_unique (tendsto_const_nhds (α := ℕ) (f := atTop)) h
  have hlow : (1 : ℝ≥0∞) ≤ π {0} := by
    have := tv_le_of_zero e0 (MeasurableSet.singleton 0)
    simpa using this
  have hhigh : π {0} ≤ 0 := by
    have h := tv_le_of_zero (by rwa [tvDist_comm] at e1) (MeasurableSet.singleton 0)
    rwa [tNu_zero] at h
  exact absurd (le_trans hlow hhigh) (by simp)

END historical refutation block. -/

/-! ### From the contraction to the invariant law

The limit is built **explicitly**, with no completeness argument: the Jordan identity
`μ n + b n = μ (n+1) + a n` for the chain `μ n = κⁿ(x₀,·)` telescopes to
`μ N + Σ_{n<N} a n = μ 0 + Σ_{n<N} b n`, the two series of nonnegative measures converge
geometrically (their masses are bounded by the contraction), and
`π := (μ 0 + Σ b) − Σ a` is the limit, with the tails of the two series as the explicit
total-variation error. -/

private theorem kpow_succ_apply (κ : Kernel S S) (n : ℕ) (x : S) :
    (κ ^ (n + 1)) x = ((κ ^ n) x).bind κ := by
  rw [pow_succ']
  exact Kernel.comp_apply κ (κ ^ n) x

-- The weight is `≥ 1`, so the weighted distance dominates the mass of the positive Jordan part.
private theorem jPos_univ_le_weightedTV {β : ℝ} (hβ : 0 ≤ β) {V : S → ℝ} (hVm : Measurable V)
    (hVnn : ∀ x, 0 ≤ V x) (μ ν : Measure S) :
    (jPos μ ν) Set.univ ≤ weightedTV β V μ ν := by
  rw [weightedTV_eq β hVm μ ν]
  refine le_trans ?_ le_self_add
  calc (jPos μ ν) Set.univ = ∫⁻ _, (1:ℝ≥0∞) ∂(jPos μ ν) := by rw [lintegral_one]
    _ ≤ ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(jPos μ ν) :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by nlinarith [hVnn x])

-- ... and hence the total-variation distance itself, because the positive Jordan part already
-- dominates every one-sided set difference.
private theorem tvDist_le_weightedTV {β : ℝ} (hβ : 0 ≤ β) {V : S → ℝ} (hVm : Measurable V)
    (hVnn : ∀ x, 0 ≤ V x) (μ ν : Measure S) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν ≤ weightedTV β V μ ν := by
  refine le_trans (iSup_le fun s => iSup_le fun _ => ?_)
    (jPos_univ_le_weightedTV hβ hVm hVnn μ ν)
  have h := congrArg (fun t : Measure S => t s) (add_jPos_comm μ ν)
  simp only [Measure.add_apply] at h
  refine le_trans (tsub_le_iff_left.2 ?_) (measure_mono (Set.subset_univ s))
  calc μ s ≤ μ s + (jPos ν μ) s := le_self_add
    _ = ν s + (jPos μ ν) s := h

-- The crude upper bound on the weighted distance (each Jordan part is under its own measure).
private theorem weightedTV_le_add {β : ℝ} {V : S → ℝ} (hVm : Measurable V) (μ ν : Measure S)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    weightedTV β V μ ν ≤ (∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂μ)
      + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂ν := by
  rw [weightedTV_eq β hVm μ ν]
  exact add_le_add (lintegral_mono' (jPos_le_left μ ν) le_rfl)
    (lintegral_mono' (jPos_le_left ν μ) le_rfl)

/-- **Harris' theorem with its quantitative Lyapunov envelope.**

Same hypotheses and same construction as `harris_theorem` (which is the corollary
immediately below, with its statement unchanged); the conclusion additionally *exports* the
pointwise geometric bound

`‖κⁿ(x, ·) − π‖_TV ≤ (c + b · V x) · rⁿ`,   `b, c ≥ 0`,  `0 ≤ r < 1`,

which the proof of `harris_theorem` already establishes internally (the step `hbound`) and
then discards when it packages the weaker pointwise-rate statement `IsGeometricallyErgodic`.
The affine-in-`V` envelope is exactly what a `π`-**integrable** dominating constant needs:
combined with `∫ V dπ < ∞` (which is *not* an output of Harris' theorem — see
`Mixing/Relations.lean`'s `lintegral_lyap_le_of_isErgodicWithRate`, which derives it from
the ergodic limit) it supplies the integrable envelope `A` of FY eq. (2.59) and of
`Mixing/Relations.lean`'s `HasGeometricStateChain`.

Concretely the proof returns `b = β`, `r = ᾱ` (the Harris contraction parameters of
`harris_contraction`) and `c = 2 + β V(x₀) + C`, where `x₀` is the arbitrary base point and
`C` the summed telescoping mass; the bound is `hbound` composed with `weightedTV_le_add` on
the two Dirac measures. -/
theorem harris_theorem_envelope {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧
      IsGeometricallyErgodic κ π ∧
      ∃ b c r : ℝ, 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ r ∧ r < 1 ∧
        ∀ (x : S) (n : ℕ),
          tvDist ((κ ^ n) x) π ≤ ENNReal.ofReal ((c + b * V x) * r ^ n) := by
  haveI := hmin.isProbability
  have hVnn := hdrift.V_nonneg
  have hVm := hdrift.V_measurable
  obtain ⟨β, ᾱ, hβpos, hᾱpos, hᾱlt, hcon⟩ := harris_contraction hdrift hmin hR
  have hwm : Measurable fun x => ENNReal.ofReal (1 + β * V x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add (measurable_const.mul hVm))
  -- the state space is nonempty: it carries the minorizing probability measure
  haveI hne : Nonempty S := by
    rcases isEmpty_or_nonempty S with h | h
    · exact absurd (measure_univ (μ := ρ))
        (by rw [Set.univ_eq_empty_iff.2 h, measure_empty]; exact zero_ne_one)
    · exact h
  obtain ⟨x₀⟩ := id hne
  have hprob : ∀ (n : ℕ) (x : S), IsProbabilityMeasure ((κ ^ n) x) := fun n x => by
    haveI := markov_pow κ n; infer_instance
  have h0 : ∀ x : S, (κ ^ 0) x = Measure.dirac x := fun x => by rw [pow_zero]; rfl
  have hstep : ∀ (n : ℕ) (x : S), (κ ^ (n + 1)) x = ((κ ^ n) x).bind κ :=
    fun n x => kpow_succ_apply κ n x
  -- ## Step 1: geometric decay along the chain, and between two chains
  obtain ⟨W, hWdef⟩ : ∃ t : ℝ≥0∞, weightedTV β V (Measure.dirac x₀) (κ x₀) = t := ⟨_, rfl⟩
  have hWne : W ≠ ⊤ := by
    haveI := hprob 1 x₀
    rw [← hWdef]
    refine ne_top_of_le_ne_top ?_ (weightedTV_le_add (β := β) hVm (Measure.dirac x₀) (κ x₀))
    rw [lintegral_dirac' _ hwm]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (drift_weight hdrift hβpos.le x₀)⟩
  have hdiracne : ∀ x y : S, weightedTV β V (Measure.dirac x) (Measure.dirac y) ≠ ⊤ := by
    intro x y
    refine ne_top_of_le_ne_top ?_
      (weightedTV_le_add (β := β) hVm (Measure.dirac x) (Measure.dirac y))
    rw [lintegral_dirac' _ hwm, lintegral_dirac' _ hwm]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hpair : ∀ (x y : S) (n : ℕ), weightedTV β V ((κ ^ n) x) ((κ ^ n) y)
      ≤ ENNReal.ofReal ᾱ ^ n * weightedTV β V (Measure.dirac x) (Measure.dirac y) := by
    intro x y n
    induction n with
    | zero => rw [h0 x, h0 y, pow_zero, one_mul]
    | succ n ih =>
        haveI := hprob n x
        haveI := hprob n y
        have h := hcon ((κ ^ n) x) ((κ ^ n) y) inferInstance inferInstance
        rw [← hstep n x, ← hstep n y] at h
        refine h.trans ?_
        calc ENNReal.ofReal ᾱ * weightedTV β V ((κ ^ n) x) ((κ ^ n) y)
            ≤ ENNReal.ofReal ᾱ *
                (ENNReal.ofReal ᾱ ^ n * weightedTV β V (Measure.dirac x) (Measure.dirac y)) :=
              mul_le_mul_right ih _
          _ = _ := by ring
  have hgeo : ∀ n : ℕ, weightedTV β V ((κ ^ n) x₀) ((κ ^ (n + 1)) x₀)
      ≤ ENNReal.ofReal ᾱ ^ n * W := by
    intro n
    induction n with
    | zero =>
        have e1 : (κ ^ (0 + 1)) x₀ = κ x₀ := by rw [zero_add, pow_one]
        rw [h0 x₀, e1, hWdef, pow_zero, one_mul]
    | succ n ih =>
        haveI := hprob n x₀
        haveI := hprob (n + 1) x₀
        have h := hcon ((κ ^ n) x₀) ((κ ^ (n + 1)) x₀) inferInstance inferInstance
        rw [← hstep n x₀, ← hstep (n + 1) x₀] at h
        refine h.trans ?_
        calc ENNReal.ofReal ᾱ * weightedTV β V ((κ ^ n) x₀) ((κ ^ (n + 1)) x₀)
            ≤ ENNReal.ofReal ᾱ * (ENNReal.ofReal ᾱ ^ n * W) := mul_le_mul_right ih _
          _ = _ := by ring
  -- ## Step 2: the two telescoping series of Jordan parts
  obtain ⟨a, ha⟩ : ∃ f : ℕ → Measure S, ∀ n, f n = jPos ((κ ^ n) x₀) ((κ ^ (n + 1)) x₀) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ f : ℕ → Measure S, ∀ n, f n = jPos ((κ ^ (n + 1)) x₀) ((κ ^ n) x₀) :=
    ⟨_, fun _ => rfl⟩
  have hmassa : ∀ n, (a n) Set.univ ≤ ENNReal.ofReal ᾱ ^ n * W := by
    intro n
    rw [ha]
    exact le_trans (jPos_univ_le_weightedTV hβpos.le hVm hVnn _ _) (hgeo n)
  have hmassb : ∀ n, (b n) Set.univ = (a n) Set.univ := by
    intro n
    haveI := hprob n x₀
    haveI := hprob (n + 1) x₀
    rw [ha, hb]
    exact (jPos_mass_eq ((κ ^ n) x₀) ((κ ^ (n + 1)) x₀)).symm
  have htel : ∀ N : ℕ, (κ ^ N) x₀ + ∑ n ∈ Finset.range N, a n
      = (κ ^ 0) x₀ + ∑ n ∈ Finset.range N, b n := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        haveI := hprob N x₀
        haveI := hprob (N + 1) x₀
        have hj : (κ ^ N) x₀ + b N = (κ ^ (N + 1)) x₀ + a N := by
          rw [ha, hb]; exact add_jPos_comm _ _
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        calc (κ ^ (N + 1)) x₀ + ((∑ n ∈ Finset.range N, a n) + a N)
            = ((κ ^ (N + 1)) x₀ + a N) + ∑ n ∈ Finset.range N, a n := by abel
          _ = ((κ ^ N) x₀ + b N) + ∑ n ∈ Finset.range N, a n := by rw [hj]
          _ = ((κ ^ N) x₀ + ∑ n ∈ Finset.range N, a n) + b N := by abel
          _ = ((κ ^ 0) x₀ + ∑ n ∈ Finset.range N, b n) + b N := by rw [ih]
          _ = (κ ^ 0) x₀ + ((∑ n ∈ Finset.range N, b n) + b N) := by abel
  -- splitting a series of measures at its `N`-th term
  have htsum : ∀ (g : ℕ → ℝ≥0∞) (N : ℕ),
      ∑' n, g n = (∑ n ∈ Finset.range N, g n) + ∑' k, g (k + N) := fun g N =>
    (Summable.sum_add_tsum_nat_add' (f := g) (k := N) ENNReal.summable).symm
  have hsplit : ∀ (f : ℕ → Measure S) (N : ℕ),
      Measure.sum f = (∑ n ∈ Finset.range N, f n) + Measure.sum fun k => f (k + N) := by
    intro f N
    ext s hs
    rw [Measure.sum_apply _ hs, Measure.add_apply, Measure.finset_sum_apply,
      Measure.sum_apply _ hs]
    exact htsum (fun n => f n s) N
  -- the geometric bound on every tail mass
  have hᾱ1 : ENNReal.ofReal ᾱ < 1 := ENNReal.ofReal_lt_one.2 hᾱlt
  have hinvne : (1 - ENNReal.ofReal ᾱ)⁻¹ ≠ ⊤ := by
    rw [Ne, ENNReal.inv_eq_top, tsub_eq_zero_iff_le]
    exact not_le.2 hᾱ1
  obtain ⟨C, hCdef⟩ : ∃ t : ℝ≥0∞, (1 - ENNReal.ofReal ᾱ)⁻¹ * W = t := ⟨_, rfl⟩
  have hCne : C ≠ ⊤ := by rw [← hCdef]; exact ENNReal.mul_ne_top hinvne hWne
  have hmassA : ∀ N : ℕ, (Measure.sum fun k => a (k + N)) Set.univ
      ≤ ENNReal.ofReal ᾱ ^ N * C := by
    intro N
    rw [Measure.sum_apply _ MeasurableSet.univ, ← hCdef]
    calc ∑' k, (a (k + N)) Set.univ
        ≤ ∑' k, ENNReal.ofReal ᾱ ^ (k + N) * W := ENNReal.tsum_le_tsum fun k => hmassa (k + N)
      _ = ∑' k, ENNReal.ofReal ᾱ ^ k * (ENNReal.ofReal ᾱ ^ N * W) :=
          tsum_congr fun k => by rw [pow_add]; ring
      _ = (∑' k : ℕ, ENNReal.ofReal ᾱ ^ k) * (ENNReal.ofReal ᾱ ^ N * W) := ENNReal.tsum_mul_right
      _ = _ := by rw [ENNReal.tsum_geometric]; ring
  have hAfin : (Measure.sum a) Set.univ ≠ ⊤ := by
    have h := hmassA 0
    simp only [add_zero, pow_zero, one_mul] at h
    exact ne_top_of_le_ne_top hCne h
  have hABuniv : (Measure.sum a) Set.univ = (Measure.sum b) Set.univ := by
    rw [Measure.sum_apply _ MeasurableSet.univ, Measure.sum_apply _ MeasurableSet.univ]
    exact tsum_congr fun n => (hmassb n).symm
  have hBfin : (Measure.sum b) Set.univ ≠ ⊤ := hABuniv ▸ hAfin
  -- ## Step 3: the invariant law, as `(μ 0 + Σ b) − Σ a`
  have hpart : ∀ N : ℕ, (∑ n ∈ Finset.range N, a n) ≤ Measure.sum a := by
    intro N
    rw [hsplit a N]
    exact Measure.le_add_right le_rfl
  have hAle : Measure.sum a ≤ (κ ^ 0) x₀ + Measure.sum b := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.sum_apply _ hs, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    rw [← Measure.finset_sum_apply]
    calc (∑ n ∈ Finset.range N, a n) s
        ≤ ((κ ^ N) x₀ + ∑ n ∈ Finset.range N, a n) s := by
          rw [Measure.add_apply]; exact le_add_self
      _ = ((κ ^ 0) x₀ + ∑ n ∈ Finset.range N, b n) s := by rw [htel N]
      _ ≤ ((κ ^ 0) x₀ + Measure.sum b) s := by
          rw [Measure.add_apply, Measure.add_apply]
          refine add_le_add le_rfl ?_
          rw [Measure.finset_sum_apply, Measure.sum_apply _ hs]
          exact ENNReal.sum_le_tsum _
  haveI hAfinm : IsFiniteMeasure (Measure.sum a) := ⟨lt_top_iff_ne_top.2 hAfin⟩
  obtain ⟨π, hπdef⟩ : ∃ m : Measure S, m = ((κ ^ 0) x₀ + Measure.sum b) - Measure.sum a :=
    ⟨_, rfl⟩
  have hπapp : ∀ s, MeasurableSet s →
      π s + (Measure.sum a) s = ((κ ^ 0) x₀) s + (Measure.sum b) s := by
    intro s hs
    rw [hπdef, Measure.sub_apply hs hAle, tsub_add_cancel_of_le (Measure.le_iff'.1 hAle s),
      Measure.add_apply]
  haveI hπprob : IsProbabilityMeasure π := by
    haveI := hprob 0 x₀
    refine ⟨?_⟩
    have h := hπapp Set.univ MeasurableSet.univ
    rw [hABuniv, show ((κ ^ 0) x₀) Set.univ = 1 from measure_univ,
      add_comm (π Set.univ) ((Measure.sum b) Set.univ),
      add_comm (1 : ℝ≥0∞) ((Measure.sum b) Set.univ)] at h
    exact (ENNReal.add_right_inj hBfin).1 h
  -- ## Step 4: the tail of the `a`-series *is* the total-variation error
  have hdist : ∀ N : ℕ, tvDist ((κ ^ N) x₀) π ≤ ENNReal.ofReal ᾱ ^ N * C := by
    intro N
    refine le_trans (iSup_le fun s => iSup_le fun hs => ?_) (hmassA N)
    have hAN : (∑ n ∈ Finset.range N, a n) s ≠ ⊤ :=
      ne_top_of_le_ne_top (ne_top_of_le_ne_top hAfin (measure_mono (Set.subset_univ s)))
        (Measure.le_iff'.1 (hpart N) s)
    have e1 := hπapp s hs
    have e2 := congrArg (fun m : Measure S => m s) (htel N)
    simp only [Measure.add_apply] at e2
    have e3 := congrArg (fun m : Measure S => m s) (hsplit a N)
    simp only [Measure.add_apply] at e3
    have e4 := congrArg (fun m : Measure S => m s) (hsplit b N)
    simp only [Measure.add_apply] at e4
    refine le_trans (tsub_le_iff_left.2 ?_) (measure_mono (Set.subset_univ s))
    refine (ENNReal.add_le_add_iff_right hAN).1 ?_
    calc ((κ ^ N) x₀) s + (∑ n ∈ Finset.range N, a n) s
        ≤ (((κ ^ N) x₀) s + (∑ n ∈ Finset.range N, a n) s)
            + (Measure.sum fun k => b (k + N)) s := le_self_add
      _ = (((κ ^ 0) x₀) s + (∑ n ∈ Finset.range N, b n) s)
            + (Measure.sum fun k => b (k + N)) s := by rw [e2]
      _ = ((κ ^ 0) x₀) s + (Measure.sum b) s := by rw [e4]; ring
      _ = π s + (Measure.sum a) s := e1.symm
      _ = π s + ((∑ n ∈ Finset.range N, a n) s + (Measure.sum fun k => a (k + N)) s) := by
            rw [e3]
      _ = (π s + (Measure.sum fun k => a (k + N)) s) + (∑ n ∈ Finset.range N, a n) s := by ring
  -- ## Step 5: geometric ergodicity from every starting point
  obtain ⟨r, hrdef⟩ : ∃ t : ℝ, t = (ᾱ + 1) / 2 := ⟨_, rfl⟩
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrlt : r < 1 := by rw [hrdef]; linarith
  have hαr : ᾱ / r < 1 := by rw [div_lt_one hrpos, hrdef]; linarith
  have hbound : ∀ (x : S) (n : ℕ), tvDist ((κ ^ n) x) π
      ≤ ENNReal.ofReal ᾱ ^ n * (weightedTV β V (Measure.dirac x) (Measure.dirac x₀) + C) := by
    intro x n
    haveI := hprob n x
    haveI := hprob n x₀
    calc tvDist ((κ ^ n) x) π
        ≤ tvDist ((κ ^ n) x) ((κ ^ n) x₀) + tvDist ((κ ^ n) x₀) π := tvDist_triangle _ _ _
      _ ≤ ENNReal.ofReal ᾱ ^ n * weightedTV β V (Measure.dirac x) (Measure.dirac x₀)
            + ENNReal.ofReal ᾱ ^ n * C :=
          add_le_add (le_trans (tvDist_le_weightedTV hβpos.le hVm hVnn _ _) (hpair x x₀ n))
            (hdist n)
      _ = _ := by ring
  have hge : IsGeometricallyErgodic κ π := by
    refine ⟨ENNReal.ofReal r, ENNReal.ofReal_lt_one.2 hrlt,
      ⟨ENNReal.ofReal_pos.2 hrpos, (ENNReal.ofReal_lt_one.2 hrlt).le, fun x => ?_⟩⟩
    obtain ⟨D, hDdef⟩ : ∃ t : ℝ≥0∞,
        weightedTV β V (Measure.dirac x) (Measure.dirac x₀) + C = t := ⟨_, rfl⟩
    have hDne : D ≠ ⊤ := by
      rw [← hDdef]; exact ENNReal.add_ne_top.2 ⟨hdiracne x x₀, hCne⟩
    have hq : ENNReal.ofReal ᾱ * (ENNReal.ofReal r)⁻¹ = ENNReal.ofReal (ᾱ / r) := by
      rw [ENNReal.ofReal_div_of_pos hrpos, div_eq_mul_inv]
    have hmaj : Tendsto (fun n : ℕ => ENNReal.ofReal (ᾱ / r) ^ n * D) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.ofReal_lt_one.2 hαr)
      simpa using ENNReal.Tendsto.mul_const h (Or.inr hDne)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    calc (ENNReal.ofReal r)⁻¹ ^ n * tvDist ((κ ^ n) x) π
        ≤ (ENNReal.ofReal r)⁻¹ ^ n * (ENNReal.ofReal ᾱ ^ n * D) := by
          rw [← hDdef]; exact mul_le_mul_right (hbound x n) _
      _ = (ENNReal.ofReal ᾱ * (ENNReal.ofReal r)⁻¹) ^ n * D := by rw [mul_pow]; ring
      _ = ENNReal.ofReal (ᾱ / r) ^ n * D := by rw [hq]
  -- ## Step 6: export the envelope carried by `hbound`
  have hCt : (0:ℝ) ≤ C.toReal := ENNReal.toReal_nonneg
  have hVx₀ : (0:ℝ) ≤ β * V x₀ := mul_nonneg hβpos.le (hVnn x₀)
  refine ⟨π, hπprob, hge.isErgodicKernel.invariant, hge, β, 2 + β * V x₀ + C.toReal, ᾱ,
    hβpos.le, by linarith, hᾱpos.le, hᾱlt, fun x n => ?_⟩
  have hVx : (0:ℝ) ≤ β * V x := mul_nonneg hβpos.le (hVnn x)
  have hdir : weightedTV β V (Measure.dirac x) (Measure.dirac x₀)
      ≤ ENNReal.ofReal (1 + β * V x) + ENNReal.ofReal (1 + β * V x₀) := by
    refine (weightedTV_le_add (β := β) hVm (Measure.dirac x) (Measure.dirac x₀)).trans ?_
    rw [lintegral_dirac' _ hwm, lintegral_dirac' _ hwm]
  have hsum : weightedTV β V (Measure.dirac x) (Measure.dirac x₀) + C
      ≤ ENNReal.ofReal ((2 + β * V x₀ + C.toReal) + β * V x) := by
    refine le_trans (add_le_add hdir (le_of_eq (ENNReal.ofReal_toReal hCne).symm)) ?_
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), ← ENNReal.ofReal_add (by linarith) hCt]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc tvDist ((κ ^ n) x) π
      ≤ ENNReal.ofReal ᾱ ^ n * (weightedTV β V (Measure.dirac x) (Measure.dirac x₀) + C) :=
        hbound x n
    _ ≤ ENNReal.ofReal ᾱ ^ n * ENNReal.ofReal ((2 + β * V x₀ + C.toReal) + β * V x) :=
        mul_le_mul_right hsum _
    _ = ENNReal.ofReal ((2 + β * V x₀ + C.toReal + β * V x) * ᾱ ^ n) := by
        rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_pow hᾱpos.le, mul_comm]

/-- **Harris' theorem** (Hairer–Mattingly): drift + minorization give a unique invariant
probability measure and a geometric total-variation rate from every starting point —
packaged exactly as `IsGeometricallyErgodic` needs it. The quantitative envelope that the
proof establishes on the way is exported separately as `harris_theorem_envelope`. -/
theorem harris_theorem {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧
      IsGeometricallyErgodic κ π := by
  obtain ⟨π, hπ, hinv, hge, -⟩ := harris_theorem_envelope hdrift hmin hR
  exact ⟨π, hπ, hinv, hge⟩

-- Since the repair of `HasLyapunovDrift.drift` (2026-08-09) the drift is *already* the `∫⁻`
-- statement, so this wrapper is now a one-liner; it is kept (with its hypotheses inert) so that
-- `level_set_pos` below reads the same as before the repair.
private theorem drift_lintegral_ae {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {μ : Measure S} [IsProbabilityMeasure μ]
    (_hμinv : Kernel.Invariant κ μ) (_hV : Integrable V μ) :
    ∀ᵐ x ∂μ, ∫⁻ y, ENNReal.ofReal (V y) ∂(κ x) ≤ ENNReal.ofReal (γ * V x + K) :=
  Filter.Eventually.of_forall hdrift.drift


-- Under the drift, every nonzero `κ`-invariant sub-measure of an invariant law that integrates
-- `V` charges the level set `{V ≤ R}` (this is where `2K/(1−γ) < R` is spent).
private theorem level_set_pos {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R : ℝ} (hR : 2 * K / (1 - γ) < R)
    {μ : Measure S} [IsProbabilityMeasure μ] (hμinv : Kernel.Invariant κ μ) (hV : Integrable V μ)
    {ξ : Measure S} (hξμ : ξ ≤ μ) (hξinv : Kernel.Invariant κ ξ) (hc : ξ Set.univ ≠ 0) :
    ξ {x | V x ≤ R} ≠ 0 := by
  obtain ⟨hγ0, hγ1⟩ := hdrift.gamma_mem
  have hK := hdrift.K_nonneg
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  have hRpos : (0:ℝ) < R := lt_of_le_of_lt (by positivity) hR
  have hVm : Measurable fun y => ENNReal.ofReal (V y) :=
    ENNReal.measurable_ofReal.comp hdrift.V_measurable
  set t := ∫⁻ y, ENNReal.ofReal (V y) ∂ξ with htdef
  have htfin : t ≠ ∞ := by
    have hle : t ≤ ∫⁻ y, ENNReal.ofReal (V y) ∂μ := lintegral_mono' hξμ le_rfl
    have hfin : ∫⁻ y, ENNReal.ofReal (V y) ∂μ ≠ ∞ := by
      have h2 := hV.2
      rw [HasFiniteIntegral] at h2
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
      exact lintegral_congr fun y => (Real.enorm_eq_ofReal (hdrift.V_nonneg y)).symm
    exact ne_top_of_le_ne_top hfin hle
  have hξfin : ξ Set.univ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ _) (hξμ _)
  -- the drift, integrated against `ξ`
  have key : t ≤ ENNReal.ofReal γ * t + ENNReal.ofReal K * ξ Set.univ := by
    have hac : ξ ≪ μ := Measure.absolutelyContinuous_of_le hξμ
    have hstep : ∀ᵐ x ∂ξ, ∫⁻ y, ENNReal.ofReal (V y) ∂(κ x) ≤ ENNReal.ofReal (γ * V x + K) :=
      hac.ae_le (drift_lintegral_ae hdrift hμinv hV)
    calc t = ∫⁻ x, (∫⁻ y, ENNReal.ofReal (V y) ∂(κ x)) ∂ξ := by
            conv_lhs => rw [htdef, ← hξinv.def]
            exact Measure.lintegral_bind κ.aemeasurable hVm.aemeasurable
      _ ≤ ∫⁻ x, ENNReal.ofReal (γ * V x + K) ∂ξ := lintegral_mono_ae hstep
      _ = ∫⁻ x, (ENNReal.ofReal γ * ENNReal.ofReal (V x) + ENNReal.ofReal K) ∂ξ := by
            refine lintegral_congr fun x => ?_
            rw [ENNReal.ofReal_add (mul_nonneg hγ0.le (hdrift.V_nonneg x)) hK,
              ENNReal.ofReal_mul hγ0.le]
      _ = ENNReal.ofReal γ * t + ENNReal.ofReal K * ξ Set.univ := by
            rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hVm,
              lintegral_const]
  -- read the drift bound off in `ℝ`
  set T := t.toReal with hTdef
  set c := (ξ Set.univ).toReal with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]; exact ENNReal.toReal_pos hc hξfin
  have hTle : T ≤ γ * T + K * c := by
    have hmono := ENNReal.toReal_mono (by finiteness) key
    rwa [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hγ0.le, ENNReal.toReal_ofReal hK] at hmono
  by_contra hzero
  -- if the level set is null, Markov's inequality forces `R·c ≤ T`
  have hcompl : ξ Set.univ = ξ {x | ¬ V x ≤ R} := by
    have hms : MeasurableSet {x | V x ≤ R} := hdrift.V_measurable measurableSet_Iic
    have := measure_add_measure_compl (μ := ξ) hms
    rw [hzero, zero_add] at this
    exact this.symm
  have hmarkov : ENNReal.ofReal R * ξ Set.univ ≤ t := by
    have hsub : {x | ¬ V x ≤ R} ⊆ {x | ENNReal.ofReal R ≤ ENNReal.ofReal (V x)} :=
      fun x hx => ENNReal.ofReal_le_ofReal (not_le.mp hx).le
    calc ENNReal.ofReal R * ξ Set.univ
        = ENNReal.ofReal R * ξ {x | ¬ V x ≤ R} := by rw [← hcompl]
      _ ≤ ENNReal.ofReal R * ξ {x | ENNReal.ofReal R ≤ ENNReal.ofReal (V x)} :=
          mul_le_mul_right (measure_mono hsub) _
      _ ≤ t := mul_meas_ge_le_lintegral₀ hVm.aemeasurable _
  have hRc : R * c ≤ T := by
    have := ENNReal.toReal_mono htfin hmarkov
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hRpos.le] at this
  have hTbound : (1 - γ) * T ≤ K * c := by linarith
  have hKR : 2 * K < R * (1 - γ) := by rw [div_lt_iff₀ h1γ] at hR; linarith
  nlinarith [hRc, hTbound, hcpos, h1γ, hKR, hK]


/-- **Uniqueness** of the invariant law under the Harris hypotheses. -/
theorem harris_invariant_unique {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ}
    {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R)
    {π π' : Measure S} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π')
    -- LEAN-ONLY: both invariant laws integrate the Lyapunov function (automatic for
    -- the constructed one; needed to compare in the weighted distance)
    (hV : Integrable V π) (hV' : Integrable V π') :
    π = π' := by
  haveI := hmin.isProbability
  obtain ⟨hα0, hα1⟩ := hmin.alpha_mem
  -- Hahn: `π' ≤ π` on `E` and `π ≤ π'` off `E`
  obtain ⟨E, hE, hE1, hE2⟩ := hahn_decomposition π π'
  have hle1 : π'.restrict E ≤ π.restrict E := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hE1 _ (ht.inter hE) Set.inter_subset_right
  have hle2 : π.restrict Eᶜ ≤ π'.restrict Eᶜ := by
    refine Measure.le_iff.2 fun t ht => ?_
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht]
    exact hE2 _ (ht.inter hE.compl) Set.inter_subset_right
  obtain ⟨P, hPdef⟩ : ∃ P : Measure S, P = π.restrict E - π'.restrict E := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : Measure S, N = π'.restrict Eᶜ - π.restrict Eᶜ := ⟨_, rfl⟩
  have hPapp : ∀ t, MeasurableSet t → P t = π (t ∩ E) - π' (t ∩ E) := fun t ht => by
    rw [hPdef, Measure.sub_apply ht hle1, Measure.restrict_apply ht, Measure.restrict_apply ht]
  have hNapp : ∀ t, MeasurableSet t → N t = π' (t ∩ Eᶜ) - π (t ∩ Eᶜ) := fun t ht => by
    rw [hNdef, Measure.sub_apply ht hle2, Measure.restrict_apply ht, Measure.restrict_apply ht]
  have hPle : P ≤ π := by rw [hPdef]; exact le_trans Measure.sub_le Measure.restrict_le_self
  have hNle : N ≤ π' := by rw [hNdef]; exact le_trans Measure.sub_le Measure.restrict_le_self
  haveI : IsFiniteMeasure P :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hPle Set.univ) (measure_lt_top π Set.univ)⟩
  haveI : IsFiniteMeasure N :=
    ⟨lt_of_le_of_lt (Measure.le_iff'.1 hNle Set.univ) (measure_lt_top π' Set.univ)⟩
  have hPEc : P Eᶜ = 0 := by rw [hPapp _ hE.compl]; simp
  have hNE : N E = 0 := by rw [hNapp _ hE]; simp
  -- `π − π' = P − N`, in the additive form `π + N = π' + P`
  have hsum : π + N = π' + P := by
    ext t ht
    have hb : π (t ∩ Eᶜ) ≤ π' (t ∩ Eᶜ) := hE2 _ (ht.inter hE.compl) Set.inter_subset_right
    have ha : π' (t ∩ E) ≤ π (t ∩ E) := hE1 _ (ht.inter hE) Set.inter_subset_right
    have h1 : π (t ∩ Eᶜ) + (π' (t ∩ Eᶜ) - π (t ∩ Eᶜ)) = π' (t ∩ Eᶜ) := add_tsub_cancel_of_le hb
    have h2 : π' (t ∩ E) + (π (t ∩ E) - π' (t ∩ E)) = π (t ∩ E) := add_tsub_cancel_of_le ha
    have hsπ : π t = π (t ∩ E) + π (t ∩ Eᶜ) := by
      rw [← Set.diff_eq]; exact (measure_inter_add_diff t hE).symm
    have hsπ' : π' t = π' (t ∩ E) + π' (t ∩ Eᶜ) := by
      rw [← Set.diff_eq]; exact (measure_inter_add_diff t hE).symm
    rw [Measure.add_apply, Measure.add_apply, hPapp t ht, hNapp t ht]
    calc π t + (π' (t ∩ Eᶜ) - π (t ∩ Eᶜ))
        = π (t ∩ E) + (π (t ∩ Eᶜ) + (π' (t ∩ Eᶜ) - π (t ∩ Eᶜ))) := by rw [hsπ, add_assoc]
      _ = π (t ∩ E) + π' (t ∩ Eᶜ) := by rw [h1]
      _ = (π' (t ∩ E) + (π (t ∩ E) - π' (t ∩ E))) + π' (t ∩ Eᶜ) := by rw [h2]
      _ = π' t + (π (t ∩ E) - π' (t ∩ E)) := by rw [hsπ']; ring
  -- both halves have the same (finite) mass
  have hmassPN : N Set.univ = P Set.univ := by
    have := congrArg (fun m => m Set.univ) hsum
    simp only [Measure.add_apply, measure_univ] at this
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 this
  -- one kernel step of the identity `π + N = π' + P`
  have hbind : π + N.bind κ = π' + P.bind κ := by
    have h := congrArg (fun m => m.bind κ) hsum
    simpa [bind_add', hπ.def, hπ'.def] using h
  have hmassbind : ∀ ξ : Measure S, (ξ.bind κ) Set.univ = ξ Set.univ := fun ξ => by
    rw [Measure.bind_apply MeasurableSet.univ κ.aemeasurable]
    simp
  -- `P` is invariant: it is dominated by its own image, with the same total mass
  have hPQ : ∀ t, MeasurableSet t → t ⊆ E → P t ≤ (P.bind κ) t := by
    intro t ht htE
    have hNt : N t = 0 := le_antisymm (hNE ▸ measure_mono htE) (zero_le)
    have e1 : π t + N t = π' t + P t := by
      have := congrArg (fun m => m t) hsum; simpa [Measure.add_apply] using this
    have e2 : π t + (N.bind κ) t = π' t + (P.bind κ) t := by
      have := congrArg (fun m => m t) hbind; simpa [Measure.add_apply] using this
    rw [hNt, add_zero] at e1
    rw [e1] at e2
    have : P t + (N.bind κ) t ≤ (P.bind κ) t := by
      rw [add_assoc] at e2
      exact le_of_eq ((ENNReal.add_right_inj (measure_ne_top π' t)).1 e2)
    exact le_trans le_self_add this
  have hQEc : (P.bind κ) Eᶜ = 0 := by
    have h1 : P Set.univ = P E := by
      have := measure_add_measure_compl (μ := P) hE
      rw [hPEc, add_zero] at this; exact this.symm
    have h2 : P E ≤ (P.bind κ) E := hPQ E hE subset_rfl
    have h3 : (P.bind κ) E + (P.bind κ) Eᶜ = P Set.univ := by
      rw [measure_add_measure_compl (μ := P.bind κ) hE, hmassbind]
    have h4 : (P.bind κ) Eᶜ ≤ 0 := by
      have : (P.bind κ) E + (P.bind κ) Eᶜ ≤ (P.bind κ) E + 0 := by
        rw [h3, add_zero, h1]; exact h2
      exact (ENNReal.add_le_add_iff_left (measure_ne_top _ _)).1 this
    exact le_antisymm h4 (zero_le)
  have hPQ' : P ≤ P.bind κ := by
    refine Measure.le_iff.2 fun t ht => ?_
    have h1 : P t = P (t ∩ E) := by
      have := measure_inter_add_diff t hE (μ := P)
      have h0 : P (t \ E) = 0 := by
        refine le_antisymm ?_ (zero_le)
        rw [Set.diff_eq]
        exact le_trans (measure_mono Set.inter_subset_right) (le_of_eq hPEc)
      rw [h0, add_zero] at this; exact this.symm
    have h2 : (P.bind κ) (t ∩ E) ≤ (P.bind κ) t := measure_mono Set.inter_subset_left
    exact h1 ▸ le_trans (hPQ _ (ht.inter hE) Set.inter_subset_right) h2
  have hPinv : Kernel.Invariant κ P := by
    refine le_antisymm ?_ hPQ'
    refine Measure.le_iff.2 fun t ht => ?_
    have h1 : (P.bind κ) t + P tᶜ ≤ (P.bind κ) t + (P.bind κ) tᶜ :=
      add_le_add le_rfl (Measure.le_iff'.1 hPQ' _)
    rw [measure_add_measure_compl (μ := P.bind κ) ht, hmassbind,
      ← measure_add_measure_compl (μ := P) ht] at h1
    exact (ENNReal.add_le_add_iff_right (measure_ne_top P tᶜ)).1 h1
  -- and so is `N`
  have hME : (N.bind κ) E = 0 := by
    have h1 : ∀ t, MeasurableSet t → t ⊆ Eᶜ → N t = (N.bind κ) t := by
      intro t ht htE
      have hPt : P t = 0 := le_antisymm (hPEc ▸ measure_mono htE) (zero_le)
      have hQt : (P.bind κ) t = 0 := le_antisymm (hQEc ▸ measure_mono htE) (zero_le)
      have e1 : π t + N t = π' t + P t := by
        have := congrArg (fun m => m t) hsum; simpa [Measure.add_apply] using this
      have e2 : π t + (N.bind κ) t = π' t + (P.bind κ) t := by
        have := congrArg (fun m => m t) hbind; simpa [Measure.add_apply] using this
      rw [hPt, add_zero] at e1
      rw [hQt, add_zero] at e2
      rw [← e2] at e1
      exact (ENNReal.add_right_inj (measure_ne_top π t)).1 e1
    have h2 : N Set.univ = N Eᶜ := by
      have := measure_add_measure_compl (μ := N) hE
      rw [hNE, zero_add] at this; exact this.symm
    have h3 : (N.bind κ) E + (N.bind κ) Eᶜ = N Set.univ := by
      rw [measure_add_measure_compl (μ := N.bind κ) hE, hmassbind]
    rw [← h1 Eᶜ hE.compl subset_rfl, ← h2] at h3
    have : (N.bind κ) E ≤ 0 := by
      have h4 : (N.bind κ) E + N Set.univ ≤ 0 + N Set.univ := by rw [h3, zero_add]
      exact (ENNReal.add_le_add_iff_right (measure_ne_top N _)).1 h4
    exact le_antisymm this (zero_le)
  have hNinv : Kernel.Invariant κ N := by
    have hNQ : N ≤ N.bind κ := by
      refine Measure.le_iff.2 fun t ht => ?_
      have h1 : N t = N (t ∩ Eᶜ) := by
        have h := measure_inter_add_diff t hE.compl (μ := N)
        have h0 : N (t \ Eᶜ) = 0 := by
          refine le_antisymm ?_ (zero_le)
          rw [Set.diff_eq, compl_compl]
          exact le_trans (measure_mono Set.inter_subset_right) (le_of_eq hNE)
        rw [h0, add_zero] at h; exact h.symm
      have h2 : N (t ∩ Eᶜ) ≤ (N.bind κ) (t ∩ Eᶜ) := by
        have hPt : P (t ∩ Eᶜ) = 0 :=
          le_antisymm (hPEc ▸ measure_mono Set.inter_subset_right) (zero_le)
        have hQt : (P.bind κ) (t ∩ Eᶜ) = 0 :=
          le_antisymm (hQEc ▸ measure_mono Set.inter_subset_right) (zero_le)
        have e1 : π (t ∩ Eᶜ) + N (t ∩ Eᶜ) = π' (t ∩ Eᶜ) + P (t ∩ Eᶜ) := by
          have := congrArg (fun m => m (t ∩ Eᶜ)) hsum; simpa [Measure.add_apply] using this
        have e2 : π (t ∩ Eᶜ) + (N.bind κ) (t ∩ Eᶜ) = π' (t ∩ Eᶜ) + (P.bind κ) (t ∩ Eᶜ) := by
          have := congrArg (fun m => m (t ∩ Eᶜ)) hbind; simpa [Measure.add_apply] using this
        rw [hPt, add_zero] at e1
        rw [hQt, add_zero] at e2
        rw [← e2] at e1
        exact le_of_eq ((ENNReal.add_right_inj (measure_ne_top π _)).1 e1)
      exact h1 ▸ le_trans h2 (measure_mono Set.inter_subset_left)
    refine le_antisymm ?_ hNQ
    refine Measure.le_iff.2 fun t ht => ?_
    have h1 : (N.bind κ) t + N tᶜ ≤ (N.bind κ) t + (N.bind κ) tᶜ :=
      add_le_add le_rfl (Measure.le_iff'.1 hNQ _)
    rw [measure_add_measure_compl (μ := N.bind κ) ht, hmassbind,
      ← measure_add_measure_compl (μ := N) ht] at h1
    exact (ENNReal.add_le_add_iff_right (measure_ne_top N tᶜ)).1 h1
  -- if the two halves were nonzero they would be mutually singular invariant laws, each
  -- charging the level set — impossible, because the minorizing measure would have to vanish
  by_cases hc : P Set.univ = 0
  · have hP0 : P = 0 := by simpa using Measure.measure_univ_eq_zero.1 hc
    have hN0 : N = 0 := by
      have : N Set.univ = 0 := by rw [hmassPN, hc]
      simpa using Measure.measure_univ_eq_zero.1 this
    rw [hP0, hN0] at hsum
    simpa using hsum
  · exfalso
    have hcN : N Set.univ ≠ 0 := by rw [hmassPN]; exact hc
    have hPL : P {x | V x ≤ R} ≠ 0 := level_set_pos hdrift hR hπ hV hPle hPinv hc
    have hNL : N {x | V x ≤ R} ≠ 0 := level_set_pos hdrift hR hπ' hV' hNle hNinv hcN
    have hρEc : ρ Eᶜ = 0 := by
      have h := minorize_bind hmin P hE.compl
      rw [hPinv.def, hPEc] at h
      have h0 : ENNReal.ofReal α * ρ Eᶜ * P {x | V x ≤ R} = 0 := le_antisymm h (zero_le)
      rcases mul_eq_zero.1 h0 with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 (by simp [ENNReal.ofReal_eq_zero, not_le, hα0])
        · exact h2
      · exact absurd h1 hPL
    have hρE : ρ E = 0 := by
      have h := minorize_bind hmin N hE
      rw [hNinv.def, hNE] at h
      have h0 : ENNReal.ofReal α * ρ E * N {x | V x ≤ R} = 0 := le_antisymm h (zero_le)
      rcases mul_eq_zero.1 h0 with h1 | h1
      · rcases mul_eq_zero.1 h1 with h2 | h2
        · exact absurd h2 (by simp [ENNReal.ofReal_eq_zero, not_le, hα0])
        · exact h2
      · exact absurd h1 hNL
    have : (1 : ℝ≥0∞) = 0 := by
      rw [← measure_univ (μ := ρ), ← measure_add_measure_compl (μ := ρ) hE, hρE, hρEc, add_zero]
    exact one_ne_zero this

/-- **Lifting from the `p`-step kernel**: if `κ^p` is geometrically ergodic with
invariant law `π` and `π` is invariant for `κ` itself, then `κ` is geometrically
ergodic. (The nonlinear-AR kernel of FY Theorem 2.4 is only minorized after `p` steps,
so this is the last glue step of that proof.) -/
theorem IsGeometricallyErgodic.of_pow {κ : Kernel S S} [IsMarkovKernel κ]
    {π : Measure S} [IsProbabilityMeasure π] {p : ℕ} (hp : 0 < p)
    (hpow : IsGeometricallyErgodic (κ ^ p) π) (hinv : Kernel.Invariant κ π) :
    IsGeometricallyErgodic κ π := by
  obtain ⟨ρ, hρ1, hρ⟩ := hpow
  have hpinv : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hbase : (1 : ℝ≥0∞) ≤ ρ⁻¹ := ENNReal.one_le_inv.mpr hρ.rho_le_one
  refine ⟨ρ ^ ((p : ℝ)⁻¹), ENNReal.rpow_lt_one hρ1 hpinv,
    ⟨ENNReal.rpow_pos hρ.rho_pos hρ1.ne_top, (ENNReal.rpow_lt_one hρ1 hpinv).le, fun x => ?_⟩⟩
  -- the `q`-step envelope of the `p`-step kernel, scaled by the fixed constant `ρ⁻¹`
  have hq : Tendsto (fun n : ℕ => n / p) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b * p, fun _ ha => (Nat.le_div_iff_mul_le hp).2 ha⟩
  have hmaj : Tendsto
      (fun n : ℕ => ρ⁻¹ * (ρ⁻¹ ^ (n / p) * tvDist (((κ ^ p) ^ (n / p)) x) π)) atTop (𝓝 0) := by
    have h := (hρ.tendsto x).comp hq
    simpa using ENNReal.Tendsto.const_mul h (Or.inr (by simp [hρ.rho_pos.ne']))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  set q := n / p with hqdef
  set r := n % p with hrdef
  have hnr : n = r + p * q := by rw [hrdef, hqdef, Nat.mod_add_div]
  haveI := markov_pow κ (p * q)
  haveI := markov_pow κ r
  -- Distance: the leftover `r = n % p` steps, applied *last*, can only contract (`π` is
  -- `κ^r`-invariant), so the `n`-step distance is at most the `pq`-step one.
  have hdist : tvDist ((κ ^ n) x) π ≤ tvDist (((κ ^ p) ^ q) x) π := by
    have hπ : π = π.bind (κ ^ r) := ((invariant_pow hinv r).def).symm
    have hstep : (κ ^ n) x = ((κ ^ (p * q)) x).bind (κ ^ r) := by
      rw [hnr, pow_add]
      exact Kernel.comp_apply (κ ^ r) (κ ^ (p * q)) x
    rw [hstep, ← pow_mul]
    nth_rewrite 1 [hπ]
    exact tvDist_bind_le (κ ^ r) ((κ ^ (p * q)) x) π
  -- Rate: `(ρ^{1/p})⁻ⁿ ≤ ρ⁻¹ · ρ⁻ᵠ` because `n/p ≤ q + 1`.
  have hrate : (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n ≤ ρ⁻¹ * ρ⁻¹ ^ q := by
    have hexp : ((p : ℝ)⁻¹) * (n : ℝ) ≤ (q : ℝ) + 1 := by
      have hnp : (n : ℝ) ≤ (p : ℝ) * ((q : ℝ) + 1) := by
        have hr : r < p := by rw [hrdef]; exact Nat.mod_lt n hp
        have hpq : p * (q + 1) = p * q + p := by ring
        have hle : n ≤ p * (q + 1) := by omega
        exact_mod_cast hle
      rw [inv_mul_le_iff₀ (by exact_mod_cast hp)]
      linarith
    calc (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n
        = (ρ⁻¹ ^ ((p : ℝ)⁻¹)) ^ ((n : ℕ) : ℝ) := by
          rw [ENNReal.inv_rpow, ENNReal.rpow_natCast]
      _ = ρ⁻¹ ^ (((p : ℝ)⁻¹) * (n : ℝ)) := (ENNReal.rpow_mul _ _ _).symm
      _ ≤ ρ⁻¹ ^ ((q : ℝ) + 1) := ENNReal.rpow_le_rpow_of_exponent_le hbase hexp
      _ = ρ⁻¹ ^ (q + 1) := by rw [← ENNReal.rpow_natCast ρ⁻¹ (q + 1)]; norm_num
      _ = ρ⁻¹ * ρ⁻¹ ^ q := by rw [pow_succ]; ring
  calc (ρ ^ ((p : ℝ)⁻¹))⁻¹ ^ n * tvDist ((κ ^ n) x) π
      ≤ (ρ⁻¹ * ρ⁻¹ ^ q) * tvDist (((κ ^ p) ^ q) x) π := mul_le_mul' hrate hdist
    _ = ρ⁻¹ * (ρ⁻¹ ^ q * tvDist (((κ ^ p) ^ q) x) π) := by ring

section NLAR

variable {p : ℕ}

/-- The state update of the vectorized autoregression, parametrized by the **new value**
`u` rather than by the noise: `shiftPush x u = (u, x₀, …, x_{p−1})`. -/
def shiftPush (x : Fin (p + 1) → ℝ) (u : ℝ) : Fin (p + 1) → ℝ :=
  Fin.cons u (fun i => x i.castSucc)

theorem measurable_shiftPush :
    Measurable fun q : (Fin (p + 1) → ℝ) × ℝ => shiftPush q.1 q.2 := by
  rw [measurable_pi_iff]
  refine Fin.cases ?_ ?_
  · simpa [shiftPush] using measurable_snd
  · exact fun i => by simpa [shiftPush] using! (measurable_pi_apply i.castSucc).comp measurable_fst

theorem nlARKernel_apply_eq {f : (Fin (p + 1) → ℝ) → ℝ} (hf : Measurable f) (ν : Measure ℝ)
    [SFinite ν] (x : Fin (p + 1) → ℝ) :
    nlARKernel f ν x =
      Measure.map (fun e : ℝ => shiftPush x (f x + e)) ν := by
  have hmeas : Measurable fun xe : (Fin (p + 1) → ℝ) × ℝ =>
      (Fin.cons (f xe.1 + xe.2) (fun i => xe.1 i.castSucc) : Fin (p + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using! (hf.comp measurable_fst).add measurable_snd
    · exact fun i => by simpa using! (measurable_pi_apply i.castSucc).comp measurable_fst
  rw [nlARKernel, Kernel.map_apply _ hmeas, Kernel.prod_apply]
  simp only [Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod, Measure.map_map hmeas measurable_prodMk_left]
  rfl

/-- **One step, in value coordinates.** Substituting `u = f x + ε` turns the noise integral
into a Lebesgue integral over the *new value* `u`, with the shifted density `g (u − f x)`. -/
theorem nlAR_lintegral {f : (Fin (p + 1) → ℝ) → ℝ} (hf : Measurable f) {g : ℝ → ℝ≥0∞}
    (hg : Measurable g) {ν : Measure ℝ} [SFinite ν] (hν : ν = MeasureTheory.volume.withDensity g)
    (x : Fin (p + 1) → ℝ) {h : (Fin (p + 1) → ℝ) → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ y, h y ∂(nlARKernel f ν x) = ∫⁻ u, g (u - f x) * h (shiftPush x u) := by
  have hsp : Measurable fun u : ℝ => shiftPush x u :=
    measurable_shiftPush.comp (measurable_const.prodMk measurable_id)
  have hcomp : Measurable fun e : ℝ => shiftPush x (f x + e) :=
    hsp.comp (measurable_const.add measurable_id)
  rw [nlARKernel_apply_eq hf ν x, lintegral_map hh hcomp]
  subst hν
  have hhc : Measurable fun e : ℝ => h (shiftPush x (f x + e)) := hh.comp hcomp
  rw [lintegral_withDensity_eq_lintegral_mul _ hg hhc]
  have key := lintegral_add_right_eq_self
    (μ := (volume : Measure ℝ)) (fun u => g (u - f x) * h (shiftPush x u)) (f x)
  simp only [add_sub_cancel_right] at key
  rw [← key]
  refine lintegral_congr fun e => ?_
  simp [add_comm]

/-! ### The Lyapunov function -/

/-- The geometrically weighted sup-norm `V(x) = ⨆ᵢ θⁱ |xᵢ|`. -/
noncomputable def lyapV (θ : ℝ) (x : Fin (p + 1) → ℝ) : ℝ :=
  ⨆ i : Fin (p + 1), θ ^ (i : ℕ) * |x i|

theorem bddAbove_lyap (θ : ℝ) (x : Fin (p + 1) → ℝ) :
    BddAbove (Set.range fun i : Fin (p + 1) => θ ^ (i : ℕ) * |x i|) :=
  (Set.finite_range _).bddAbove

theorem le_lyapV (θ : ℝ) (x : Fin (p + 1) → ℝ) (i : Fin (p + 1)) :
    θ ^ (i : ℕ) * |x i| ≤ lyapV θ x :=
  le_ciSup (f := fun i : Fin (p + 1) => θ ^ (i : ℕ) * |x i|) (bddAbove_lyap θ x) i

theorem lyapV_le {θ : ℝ} {x : Fin (p + 1) → ℝ} {b : ℝ}
    (h : ∀ i : Fin (p + 1), θ ^ (i : ℕ) * |x i| ≤ b) : lyapV θ x ≤ b :=
  ciSup_le h

theorem lyapV_nonneg (θ : ℝ) (x : Fin (p + 1) → ℝ) : 0 ≤ lyapV θ x := by
  refine le_trans ?_ (le_lyapV θ x 0)
  simp

theorem measurable_lyapV (θ : ℝ) : Measurable (lyapV (p := p) θ) := by
  unfold lyapV
  refine Measurable.iSup fun i : Fin (p + 1) => measurable_const.mul ?_
  fun_prop

theorem bddAbove_abs (x : Fin (p + 1) → ℝ) :
    BddAbove (Set.range fun i : Fin (p + 1) => |x i|) := (Set.finite_range _).bddAbove

theorem ciSup_abs_nonneg (x : Fin (p + 1) → ℝ) : 0 ≤ ⨆ i, |x i| :=
  le_trans (abs_nonneg (x 0)) (le_ciSup (bddAbove_abs x) 0)

/-- The sup-norm is controlled by the weighted one: `θᵖ · ‖x‖_∞ ≤ V(x)`. -/
theorem pow_mul_ciSup_abs_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (x : Fin (p + 1) → ℝ) :
    θ ^ p * (⨆ i, |x i|) ≤ lyapV θ x := by
  have hpow : (0 : ℝ) < θ ^ p := pow_pos hθ0 p
  rw [← le_div_iff₀' hpow]
  refine ciSup_le fun i : Fin (p + 1) => ?_
  rw [le_div_iff₀' hpow]
  refine le_trans ?_ (le_lyapV θ x i)
  have hle : θ ^ p ≤ θ ^ (i : ℕ) :=
    pow_le_pow_of_le_one hθ0.le hθ1 (Nat.lt_succ_iff.mp i.isLt)
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

/-- One shift-push step of the Lyapunov function. -/
theorem lyapV_shiftPush_le {θ : ℝ} (hθ0 : 0 ≤ θ) (x : Fin (p + 1) → ℝ) (u : ℝ) :
    lyapV θ (shiftPush x u) ≤ max |u| (θ * lyapV θ x) := by
  refine lyapV_le fun j => ?_
  refine Fin.cases ?_ ?_ j
  · simp [shiftPush]
  · intro i
    refine le_trans ?_ (le_max_right |u| (θ * lyapV θ x))
    have h1 : θ ^ ((i.succ : Fin (p + 1)) : ℕ) * |shiftPush x u i.succ|
        = θ * (θ ^ (i : ℕ) * |x i.castSucc|) := by
      simp only [shiftPush, Fin.cons_succ, Fin.val_succ, pow_succ]
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_left (le_lyapV θ x i.castSucc) hθ0

/-- Pointwise one-step bound on the Lyapunov function, with the contraction supplied by
`lam ≤ θ^{p+1}`. -/
theorem lyapV_step_le {θ lam c : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hlam : lam ≤ θ ^ (p + 1)) (hc : 0 ≤ c)
    {f : (Fin (p + 1) → ℝ) → ℝ} (hbound : ∀ x, |f x| ≤ lam * (⨆ i, |x i|) + c)
    (x : Fin (p + 1) → ℝ) (e : ℝ) :
    lyapV θ (shiftPush x (f x + e)) ≤ θ * lyapV θ x + c + |e| := by
  have hS := ciSup_abs_nonneg x
  have hkey : lam * (⨆ i, |x i|) ≤ θ * lyapV θ x := by
    have h1 : lam * (⨆ i, |x i|) ≤ θ ^ (p + 1) * (⨆ i, |x i|) :=
      mul_le_mul_of_nonneg_right hlam hS
    have h2 : θ ^ (p + 1) * (⨆ i, |x i|) = θ * (θ ^ p * (⨆ i, |x i|)) := by ring
    have h3 : θ * (θ ^ p * (⨆ i, |x i|)) ≤ θ * lyapV θ x :=
      mul_le_mul_of_nonneg_left (pow_mul_ciSup_abs_le hθ0 hθ1 x) hθ0.le
    linarith [h1, h2 ▸ h1]
  have habs : |f x + e| ≤ θ * lyapV θ x + c + |e| := by
    have := hbound x
    have h4 : |f x + e| ≤ |f x| + |e| := abs_add_le _ _
    linarith
  refine (lyapV_shiftPush_le hθ0.le x _).trans (max_le habs ?_)
  have := lyapV_nonneg θ x
  linarith [abs_nonneg e]

/-- **Lyapunov drift for the nonlinear-AR kernel** (one step). -/
theorem hasLyapunovDrift_nlAR {θ lam c : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hlam : lam ≤ θ ^ (p + 1)) (hc : 0 ≤ c)
    {f : (Fin (p + 1) → ℝ) → ℝ} (hf : Measurable f)
    (hbound : ∀ x, |f x| ≤ lam * (⨆ i, |x i|) + c)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hint : Integrable (fun e : ℝ => e) ν) :
    HasLyapunovDrift (nlARKernel f ν) (lyapV θ) θ (c + ∫ e, |e| ∂ν) := by
  have hE : 0 ≤ ∫ e, |e| ∂ν := integral_nonneg fun e => abs_nonneg e
  have hEeq : ∫⁻ e, ENNReal.ofReal |e| ∂ν = ENNReal.ofReal (∫ e, |e| ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hint.abs
      (Filter.Eventually.of_forall fun e => abs_nonneg e)).symm
  refine ⟨lyapV_nonneg θ, measurable_lyapV θ, ⟨hθ0, hθ1⟩, by linarith, fun x => ?_⟩
  have hnn : 0 ≤ θ * lyapV θ x + c := by
    have := lyapV_nonneg θ x; nlinarith
  have hsp : Measurable fun u : ℝ => shiftPush x u :=
    measurable_shiftPush.comp (measurable_const.prodMk measurable_id)
  have hcomp : Measurable fun e : ℝ => shiftPush x (f x + e) :=
    hsp.comp (measurable_const.add measurable_id)
  have hVm : Measurable fun y : Fin (p + 1) → ℝ => ENNReal.ofReal (lyapV θ y) :=
    ENNReal.measurable_ofReal.comp (measurable_lyapV θ)
  rw [nlARKernel_apply_eq hf ν x, lintegral_map hVm hcomp]
  have hmono : ∀ e : ℝ, ENNReal.ofReal (lyapV θ (shiftPush x (f x + e)))
      ≤ ENNReal.ofReal (θ * lyapV θ x + c) + ENNReal.ofReal |e| := by
    intro e
    rw [← ENNReal.ofReal_add (hnn) (abs_nonneg e)]
    exact ENNReal.ofReal_le_ofReal (by linarith [lyapV_step_le hθ0 hθ1.le hlam hc hbound x e])
  calc ∫⁻ e, ENNReal.ofReal (lyapV θ (shiftPush x (f x + e))) ∂ν
      ≤ ∫⁻ e, (ENNReal.ofReal (θ * lyapV θ x + c) + ENNReal.ofReal |e|) ∂ν :=
        lintegral_mono hmono
    _ = ENNReal.ofReal (θ * lyapV θ x + c) + ENNReal.ofReal (∫ e, |e| ∂ν) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one, hEeq]
    _ = ENNReal.ofReal (θ * lyapV θ x + (c + ∫ e, |e| ∂ν)) := by
        rw [← ENNReal.ofReal_add (hnn) hE]; ring_nf

/-! ### The `(p+1)`-step map in value coordinates -/

/-- The state reached from `x` after `k` steps whose successive **new values** are
`u 0, …, u (k−1)`. -/
def iterPush : (k : ℕ) → (Fin (p + 1) → ℝ) → (Fin k → ℝ) → (Fin (p + 1) → ℝ)
  | 0, x, _ => x
  | k + 1, x, u => iterPush k (shiftPush x (u 0)) (Fin.tail u)

theorem iterPush_cons (k : ℕ) (x : Fin (p + 1) → ℝ) (a : ℝ) (v : Fin k → ℝ) :
    iterPush (k + 1) x (Fin.cons a v) = iterPush k (shiftPush x a) v := by
  simp [iterPush]

theorem measurable_iterPush (k : ℕ) :
    Measurable fun q : (Fin (p + 1) → ℝ) × (Fin k → ℝ) => iterPush k q.1 q.2 := by
  induction k with
  | zero => exact measurable_fst
  | succ k ih =>
      have hstep : Measurable fun q : (Fin (p + 1) → ℝ) × (Fin (k + 1) → ℝ) =>
          ((shiftPush q.1 (q.2 0) : Fin (p + 1) → ℝ), (Fin.tail q.2 : Fin k → ℝ)) :=
        (measurable_shiftPush.comp
            (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))).prodMk
          (measurable_pi_iff.2 fun i => (measurable_pi_apply i.succ).comp measurable_snd)
      exact ih.comp hstep

/-- **The state forgets its initial value after `p+1` steps.** After `k` steps the state
depends on `x` only through the coordinates `i` with `i + k ≤ p`. -/
theorem iterPush_congr : ∀ (k : ℕ) (x x' : Fin (p + 1) → ℝ) (u : Fin k → ℝ),
    (∀ i : Fin (p + 1), (i : ℕ) + k < p + 1 → x i = x' i) → iterPush k x u = iterPush k x' u := by
  intro k
  induction k with
  | zero =>
      intro x x' u h
      have : x = x' := funext fun i => h i (by simpa using i.isLt)
      simp [iterPush, this]
  | succ k ih =>
      intro x x' u h
      refine ih _ _ _ fun i => ?_
      refine Fin.cases ?_ ?_ i
      · intro _; simp [shiftPush]
      · intro j hj
        simp only [shiftPush, Fin.cons_succ]
        refine h j.castSucc ?_
        simp only [Fin.val_succ] at hj
        simp only [Fin.val_castSucc]
        omega

/-- After `p+1` steps the state is a function of the new values alone. -/
theorem iterPush_full (x x' : Fin (p + 1) → ℝ) (u : Fin (p + 1) → ℝ) :
    iterPush (p + 1) x u = iterPush (p + 1) x' u :=
  iterPush_congr (p + 1) x x' u fun i hi => absurd hi (by omega)

/-! ### The window measure and its one-step recursion -/

theorem measurePreserving_consBox (J : Set ℝ) (k : ℕ) :
    MeasurePreserving (fun z : ℝ × (Fin k → ℝ) => (Fin.cons z.1 z.2 : Fin (k + 1) → ℝ))
      ((volume.restrict J).prod (Measure.pi fun _ : Fin k => volume.restrict J))
      (Measure.pi fun _ : Fin (k + 1) => volume.restrict J) := by
  have h := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => (volume.restrict J : Measure ℝ)) 0).symm
  have hfun : (fun z : ℝ × (Fin k → ℝ) => (Fin.cons z.1 z.2 : Fin (k + 1) → ℝ))
      = ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm := by
    ext z i
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  rw [hfun]
  exact h

theorem measurable_iterPush' (k : ℕ) (x : Fin (p + 1) → ℝ) :
    Measurable (iterPush k x) :=
  (measurable_iterPush k).comp (measurable_const.prodMk measurable_id)

/-- **The window measure recursion**: pushing the `(k+1)`-fold window forward through the
chain map is the `J`-average of the `k`-fold pushforwards from the once-updated state. -/
theorem map_iterPush_succ (J : Set ℝ) (k : ℕ) (x : Fin (p + 1) → ℝ)
    {A : Set (Fin (p + 1) → ℝ)} (hA : MeasurableSet A) :
    (Measure.map (iterPush (k + 1) x) (Measure.pi fun _ : Fin (k + 1) => volume.restrict J)) A
      = ∫⁻ u in J, (Measure.map (iterPush k (shiftPush x u))
          (Measure.pi fun _ : Fin k => volume.restrict J)) A := by
  have hcons : Measurable fun z : ℝ × (Fin k → ℝ) => (Fin.cons z.1 z.2 : Fin (k + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using measurable_fst
    · exact fun i => by simpa using! (measurable_pi_apply i).comp measurable_snd
  have hmk : Measurable (iterPush (k + 1) x) := measurable_iterPush' _ x
  rw [← (measurePreserving_consBox J k).map_eq, Measure.map_map hmk hcons,
    Measure.map_apply (hmk.comp hcons) hA, Measure.prod_apply ((hmk.comp hcons) hA)]
  refine lintegral_congr fun u => ?_
  rw [Measure.map_apply (measurable_iterPush' k _) hA]
  congr 1

/-! ### The `k`-step lower bound -/

/-- **The window minorization, by induction on the number of steps.** As long as the state
stays inside the box `{‖·‖_∞ ≤ Rb}` and the innovation density is at least `δ` on the
relevant window, the `k`-step law dominates `δᵏ` times the pushforward of the `k`-fold
window measure. -/
theorem pow_ge_window {f : (Fin (p + 1) → ℝ) → ℝ} (hf : Measurable f)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν = MeasureTheory.volume.withDensity g) {J : Set ℝ} (hJ : MeasurableSet J)
    {Rb δ : ℝ}
    (hstab : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J, ∀ i, |shiftPush x u i| ≤ Rb)
    (hdens : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J,
      ENNReal.ofReal δ ≤ g (u - f x)) :
    ∀ (k : ℕ) (x : Fin (p + 1) → ℝ), (∀ i, |x i| ≤ Rb) →
      ∀ A : Set (Fin (p + 1) → ℝ), MeasurableSet A →
      ENNReal.ofReal δ ^ k *
          (Measure.map (iterPush k x) (Measure.pi fun _ : Fin k => volume.restrict J)) A
        ≤ ((nlARKernel f ν) ^ k) x A := by
  haveI : IsMarkovKernel (nlARKernel f ν) := isMarkovKernel_nlARKernel hf ν
  intro k
  induction k with
  | zero =>
      intro x _ A hA
      have hmass : (Measure.pi fun _ : Fin 0 => (volume.restrict J : Measure ℝ)) Set.univ = 1 := by
        rw [show (Set.univ : Set (Fin 0 → ℝ)) = Set.univ.pi fun _ => Set.univ by simp,
          Measure.pi_pi]
        simp
      have : Measure.map (iterPush 0 x) (Measure.pi fun _ : Fin 0 => volume.restrict J)
          = Measure.dirac x := by
        rw [show (iterPush 0 x) = fun _ : Fin 0 → ℝ => x from rfl, Measure.map_const, hmass,
          one_smul]
      rw [this, pow_zero, one_mul, pow_zero]
      exact le_of_eq rfl
  | succ k ih =>
      intro x hx A hA
      have hδne : (ENNReal.ofReal δ) ^ (k + 1) ≠ ⊤ := by
        exact (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      have hcoe : Measurable fun y : Fin (p + 1) → ℝ => ((nlARKernel f ν ^ k) y A) :=
        Kernel.measurable_coe _ hA
      -- the `(k+1)`-step law, in value coordinates
      have hstepR : ((nlARKernel f ν) ^ (k + 1)) x A
          = ∫⁻ u, g (u - f x) * ((nlARKernel f ν ^ k) (shiftPush x u) A) := by
        have h0 : ((nlARKernel f ν) ^ (k + 1)) x
            = ((nlARKernel f ν) x).bind ((nlARKernel f ν) ^ k) := by
          rw [pow_succ]
          exact Kernel.comp_apply ((nlARKernel f ν) ^ k) (nlARKernel f ν) x
        rw [h0, Measure.bind_apply hA (Kernel.aemeasurable _)]
        exact nlAR_lintegral hf hg hν x hcoe
      rw [hstepR, map_iterPush_succ J k x hA,
        ← lintegral_const_mul' _ _ hδne]
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
        _ ≤ g (u - f x) * ((nlARKernel f ν ^ k) (shiftPush x u) A) :=
            mul_le_mul' (hdens x hx u hu) hIH

/-- **Minorization of the `(p+1)`-step kernel.** After `p+1` steps every coordinate has been
refreshed, so the law dominates a fixed multiple of (normalized) Lebesgue measure on a cube,
uniformly over the Lyapunov sublevel set `{V ≤ R}`. -/
theorem hasMinorization_nlAR_pow
    {f : (Fin (p + 1) → ℝ) → ℝ} (hf : Measurable f)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) (hgc : Continuous g) (hgpos : ∀ t, 0 < g t)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : ν = MeasureTheory.volume.withDensity g)
    {lam c : ℝ} (hlam0 : 0 ≤ lam) (hc : 0 ≤ c)
    (hbound : ∀ x : Fin (p + 1) → ℝ, |f x| ≤ lam * (⨆ i, |x i|) + c)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {R : ℝ} (hR0 : 0 < R) :
    ∃ (α : ℝ) (ρ : Measure (Fin (p + 1) → ℝ)),
      HasMinorization ((nlARKernel f ν) ^ (p + 1)) (lyapV θ) R α ρ := by
  haveI : IsMarkovKernel (nlARKernel f ν) := isMarkovKernel_nlARKernel hf ν
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
  obtain ⟨J, hJdef⟩ : ∃ s : Set ℝ, s = Set.Icc (-Rb) Rb := ⟨_, rfl⟩
  have hJm : MeasurableSet J := hJdef ▸ measurableSet_Icc
  have hJmem : ∀ u ∈ J, |u| ≤ Rb := fun u hu => by
    rw [hJdef] at hu; exact abs_le.2 ⟨hu.1, hu.2⟩
  have hstab : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J, ∀ i,
      |shiftPush x u i| ≤ Rb := by
    intro x hx u hu i
    refine Fin.cases ?_ ?_ i
    · simpa [shiftPush] using hJmem u hu
    · intro j; simpa [shiftPush] using hx j.castSucc
  -- the drift function is bounded on the box
  obtain ⟨B, hBdef⟩ : ∃ b : ℝ, b = lam * Rb + c := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hBdef ▸ by positivity
  have hfB : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → |f x| ≤ B := by
    intro x hx
    refine (hbound x).trans ?_
    have hsup : (⨆ i, |x i|) ≤ Rb := ciSup_le hx
    rw [hBdef]
    nlinarith
  -- the density is bounded below on the (compact) relevant window
  have hne : (Set.Icc (-(Rb + B)) (Rb + B)).Nonempty := ⟨0, by constructor <;> linarith⟩
  obtain ⟨t₀, ht₀mem, ht₀min⟩ := isCompact_Icc.exists_isMinOn hne hgc.continuousOn
  obtain ⟨δ, hδdef⟩ : ∃ d : ℝ, d = (min (g t₀) 1).toReal := ⟨_, rfl⟩
  have hminne : min (g t₀) 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have hofδ : ENNReal.ofReal δ = min (g t₀) 1 := by
    rw [hδdef, ENNReal.ofReal_toReal hminne]
  have hδ0 : 0 < δ := by
    have : 0 < min (g t₀) 1 := lt_min (hgpos t₀) one_pos
    rw [hδdef]
    exact ENNReal.toReal_pos this.ne' hminne
  have hδg : ∀ t : ℝ, |t| ≤ Rb + B → ENNReal.ofReal δ ≤ g t := by
    intro t ht
    rw [hofδ]
    refine (min_le_left _ _).trans (ht₀min ?_)
    exact ⟨by linarith [neg_abs_le t, le_abs_self t], by linarith [le_abs_self t]⟩
  have hdens : ∀ x : Fin (p + 1) → ℝ, (∀ i, |x i| ≤ Rb) → ∀ u ∈ J,
      ENNReal.ofReal δ ≤ g (u - f x) := by
    intro x hx u hu
    refine hδg _ ?_
    calc |u - f x| ≤ |u| + |f x| := abs_sub _ _
      _ ≤ Rb + B := add_le_add (hJmem u hu) (hfB x hx)
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
  -- its total mass
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
  have hw := pow_ge_window hf hg hν hJm hstab hdens (p + 1) x (hbox x hx) A hA
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

/-- **FY Theorem 2.4(ii)** — the drift/contraction criterion for the vectorized nonlinear
autoregression `X_t = f(X_{t−1}, …, X_{t−p−1}) + ε_t`. If the autoregression function is a
sup-norm contraction up to a constant, `|f(𝐱)| ≤ λ‖𝐱‖_∞ + c` with `λ < 1`, and the noise
has an everywhere-positive **continuous** density and a finite first moment, then the chain
is geometrically ergodic toward a (unique) stationary probability law.

This is the statement that used to sit in `GeometricErgodicity.lean` as a named `sorry`; it
moved here because its proof consumes this file's Harris engine, and this file imports that
one. It is the last structural debt of the TimeSeries area.

**Proof.** `V(𝐱) := ⨆ᵢ θⁱ|xᵢ|` with `θ := λ'^{1/(p+1)}`, `λ' := max λ ½` (the boost keeps
`θ > 0` when `λ = 0`), is a Lyapunov function: the shifted coordinates each gain a factor
`θ`, and the new coordinate `f(𝐱) + ε` costs `λ·θ^{−p} ≤ θ`, so
`E V(next) ≤ θ V + (c + E|ε|)` (`hasLyapunovDrift_nlAR`). After `p+1` steps every
coordinate has been refreshed and the state no longer depends on where it started
(`iterPush_full`), so `κ^{p+1}(𝐱, ·)` dominates `δ^{p+1}` times a *fixed* window measure —
Lebesgue measure on a cube, pushed through the (bijective, triangular) value map — where
`δ > 0` is the minimum of the density over a compact window (`hasMinorization_nlAR_pow`).
`harris_theorem` on `κ^{p+1}` then supplies the invariant law and the geometric rate;
`eq_of_invariant_of_isErgodicKernel` transports invariance from `κ^{p+1}` back to `κ`, and
`IsGeometricallyErgodic.of_pow` finishes. Petite sets and ψ-irreducibility are avoided
throughout — that is exactly what the continuity strengthening buys.

**Statement strengthening (documented).** FY assume only that `ε_t` has a positive density.
We additionally assume that density **continuous** (`hgc`): without it the density has no
positive lower bound on a compact window (`{g ≥ 1/n}` may have measure zero on every
interval for every fixed `n` only up to null sets, and the natural repair — restricting the
*noise* rather than the *value* — makes the `p+1`-step window law depend on the starting
state, which destroys the minorization). Every consumer of this theorem in the project
already supplies continuity: `Threshold/TAR.lean`'s `exists_stationary_tar` and
`exists_stationary_toy_setar` both hypothesize `∃ g, Continuous g ∧ (∀ x, 0 < g x) ∧ …`.
The mean-zero hypothesis `hmean` is not needed by the proof and is kept only because it is
part of the frozen FY statement. -/
theorem nlARKernel_geometricallyErgodic
    {f : (Fin (p + 1) → ℝ) → ℝ}
    -- USER-INPUT: the autoregression function, measurable; FY §2.1.4 Thm 2.4
    (hf : Measurable f)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    -- USER-INPUT: the innovation density is *continuous* — the documented strengthening of
    -- FY's hypothesis, see the docstring; supplied by every consumer
    (hgc : Continuous g)
    -- USER-INPUT: the noise has an (everywhere) positive density; FY §2.1.4 Thm 2.4
    (hgpos : ∀ x, 0 < g x)
    {ν : Measure ℝ} (hν : ν = MeasureTheory.volume.withDensity g)
    [IsProbabilityMeasure ν]
    -- USER-INPUT: integrable, mean-zero noise; FY §2.1.4 Thm 2.4 (`hmean` is unused)
    (hint : Integrable (fun x : ℝ => x) ν) (hmean : ∫ x, x ∂ν = 0)
    {lam c : ℝ}
    -- USER-INPUT: sup-norm contraction |f(x)| ≤ λ maxᵢ|xᵢ| + c with λ < 1; FY Thm 2.4(ii)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1) (hc : 0 ≤ c)
    (hbound : ∀ x, |f x| ≤ lam * (⨆ i, |x i|) + c) :
    ∃ F : Measure (Fin (p + 1) → ℝ), IsProbabilityMeasure F ∧
      IsGeometricallyErgodic (nlARKernel f ν) F := by
  haveI : IsMarkovKernel (nlARKernel f ν) := isMarkovKernel_nlARKernel hf ν
  -- the contraction factor, boosted away from `0` and taken to the `(p+1)`-st root
  obtain ⟨lam', hlam'def⟩ : ∃ t : ℝ, t = max lam (1 / 2) := ⟨_, rfl⟩
  have hlam'0 : 0 < lam' := hlam'def ▸ lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hlam'1 : lam' < 1 := hlam'def ▸ max_lt hlam (by norm_num)
  have hlamle : lam ≤ lam' := hlam'def ▸ le_max_left _ _
  obtain ⟨θ, hθdef⟩ : ∃ t : ℝ, t = lam' ^ ((((p + 1 : ℕ) : ℝ))⁻¹) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := hθdef ▸ Real.rpow_pos_of_pos hlam'0 _
  have hθp : θ ^ (p + 1) = lam' := by
    rw [hθdef]; exact Real.rpow_inv_natCast_pow hlam'0.le (Nat.succ_ne_zero p)
  have hθ1 : θ < 1 := by
    by_contra hcon
    rw [not_lt] at hcon
    have := one_le_pow₀ (n := p + 1) hcon
    rw [hθp] at this
    linarith
  have hlamθ : lam ≤ θ ^ (p + 1) := hθp ▸ hlamle
  -- the drift, one step and then `p+1` steps
  have hdr := hasLyapunovDrift_nlAR hθ0 hθ1 hlamθ hc hf hbound hint
  have hdrP := hdr.pow (n := p + 1) (Nat.succ_pos p)
  obtain ⟨K, hKdef⟩ : ∃ t : ℝ, t = c + ∫ e, |e| ∂ν := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hKdef ▸ by
    have : 0 ≤ ∫ e, |e| ∂ν := integral_nonneg fun e => abs_nonneg e
    linarith
  rw [← hKdef] at hdrP
  have hKq : 0 ≤ K / (1 - θ) := div_nonneg hK0 (by linarith)
  have hγ1 : θ ^ (p + 1) < 1 := pow_lt_one₀ hθ0.le hθ1 (Nat.succ_ne_zero p)
  obtain ⟨R, hRdef⟩ : ∃ t : ℝ, t = 2 * (K / (1 - θ)) / (1 - θ ^ (p + 1)) + 1 := ⟨_, rfl⟩
  have hRpos : 0 < R := by
    rw [hRdef]
    have : 0 ≤ 2 * (K / (1 - θ)) / (1 - θ ^ (p + 1)) :=
      div_nonneg (by linarith) (by linarith)
    linarith
  have hR : 2 * (K / (1 - θ)) / (1 - θ ^ (p + 1)) < R := by rw [hRdef]; linarith
  -- the minorization of the `(p+1)`-step kernel
  obtain ⟨α, ρ, hmin⟩ :=
    hasMinorization_nlAR_pow hf hg hgc hgpos hν hlam0 hc hbound hθ0 hθ1 hRpos
  haveI := markov_pow (nlARKernel f ν) (p + 1)
  obtain ⟨π, hπprob, hπinv, hπge⟩ := harris_theorem hdrP hmin hR
  haveI := hπprob
  -- `π` is invariant for the one-step kernel too
  have hξprob : IsProbabilityMeasure (π.bind (nlARKernel f ν)) := by
    refine ⟨?_⟩
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable _)]
    simp
  haveI := hξprob
  have hξinv : Kernel.Invariant ((nlARKernel f ν) ^ (p + 1)) (π.bind (nlARKernel f ν)) := by
    change (π.bind (nlARKernel f ν)).bind ((nlARKernel f ν) ^ (p + 1)) = π.bind (nlARKernel f ν)
    have hcomm : ((nlARKernel f ν) ^ (p + 1)) ∘ₖ (nlARKernel f ν)
        = (nlARKernel f ν) ∘ₖ ((nlARKernel f ν) ^ (p + 1)) := by
      change ((nlARKernel f ν) ^ (p + 1)) * (nlARKernel f ν)
        = (nlARKernel f ν) * ((nlARKernel f ν) ^ (p + 1))
      rw [← pow_succ, ← pow_succ']
    rw [Measure.comp_assoc (μ := π) (κ := nlARKernel f ν) (η := (nlARKernel f ν) ^ (p + 1)),
      hcomm,
      ← Measure.comp_assoc (μ := π) (κ := (nlARKernel f ν) ^ (p + 1)) (η := nlARKernel f ν),
      hπinv.def]
  have hinv : Kernel.Invariant (nlARKernel f ν) π :=
    eq_of_invariant_of_isErgodicKernel hπge.isErgodicKernel hξinv
  exact ⟨π, hπprob, IsGeometricallyErgodic.of_pow (Nat.succ_pos p) hπge hinv⟩

end NLAR

end StatLean.TimeSeries
