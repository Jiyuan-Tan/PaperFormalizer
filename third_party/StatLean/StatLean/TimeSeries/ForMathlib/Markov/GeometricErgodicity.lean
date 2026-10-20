module
public import StatLean.TimeSeries.ForMathlib.Markov.Chain
public import StatLean.Minimaxity.ForMathlib.TotalVariation
public import StatLean.Bayesian.ForMathlib.TVDist
public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Ergodicity and geometric ergodicity of Markov kernels (FY Definition 2.4)

FY Definition 2.4: the chain with kernel `κ` is *ergodic* (rate `ρ = 1`) resp.
*geometrically ergodic* (rate `ρ < 1`) toward a law `F` when
`ρ⁻ⁿ ‖κⁿ(x, ·) − F‖_TV → 0` for every starting state `x`. We phrase total variation via
the cross-area brick `StatLean.Minimaxity.tvDist` (the sup-over-events distance, half of
the book's `L¹` norm — a constant factor immaterial to every convergence-to-zero
statement, documented deviation).

Also here: the transition kernel `nlARKernel` of the vectorized nonlinear autoregression
`X_t = f(X_{t-1}, …, X_{t-p-1}) + ε_t` (FY eqs. (2.7)–(2.8)), and
`eq_of_invariant_of_isErgodicKernel` — the converse of `IsErgodicKernel.invariant`, i.e.
the fact that an ergodic kernel has *only one* invariant law.

**FY Theorem 2.4(ii)** — the drift/contraction criterion for geometric ergodicity of that
chain — was carried here as a named `sorry` (§2.1.4 is excluded from the formalization scope
by project decision, `TimeSeries_plan.md`, but its Theorem 2.4 is the certificate that
§2.1.5's remark and §4.1's TAR stationarity claims consume). It is now **proved**, in
`ForMathlib/Markov/HarrisTheorem.lean`, which is where the Harris engine it consumes lives;
see the comment at the foot of this file.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.4:
Definition 2.4 with eq. (2.10) (p. 34), eqs. (2.7)–(2.8) (vectorization), Theorem 2.4
(p. 35). (`FY §2.1.4 Def 2.4, Thm 2.4`.)

**Proof formalization notes.**
* `tvDist` is `ℝ≥0∞`-valued; the rate condition multiplies by `ρ⁻¹ ^ n` in `ℝ≥0∞`
  (for `0 < ρ ≤ 1` the inverse is finite except at `ρ = 1`, where `ρ⁻¹ = 1`).
* `IsErgodicKernel.invariant` consumes two cross-area `ForMathlib` total-variation bricks:
  `StatLean.Minimaxity.tvDist_comm` (symmetry on probability measures) and
  `StatLean.Bayesian.tvDist_triangle` / `lintegral_le_lintegral_add_tvDist` (the latter is
  the `≤`-mover that makes kernel averaging a `tvDist` contraction — see the private
  `tvDist_bind_le` below). Neither carries Bayesian content; both are staged-for-Mathlib
  measure-theoretic lemmas.
* `nlARKernel` pushes `(x, ε) ↦ (f(x) + ε, x₀, …, x_{p-1})` through `id ×ₖ const ν`;
  the book's misprint `f(x₁)` for `f(𝐱)` in the vectorization display is corrected.
* Theorem 2.4's "`ε_t` has a positive density" is formalized as `ν = volume.withDensity g`
  with everywhere-positive `g`; "mean zero" as `∫ x dν = 0` plus integrability.

**Bibliographic comments.** Geometric ergodicity and drift criteria are the
Foster–Lyapunov tradition: F. G. Foster (1953), R. L. Tweedie ("Sufficient conditions for
ergodicity and recurrence of Markov chains on a general state space", *Stoch. Proc.
Appl.* **3** (1975), 385–403), and S. P. Meyn and R. L. Tweedie, *Markov Chains and
Stochastic Stability*, Springer, 1993. The nonlinear-AR criteria cited by FY are H. Z. An
and F. C. Huang (*Statist. Sinica* **6** (1996), 943–956) and R. Bhattacharya and C. Lee
(*Statist. Probab. Lett.* **22** (1995), 311–315). Harris-type ergodicity: T. E. Harris
(1956); W. Feller, *An Introduction to Probability Theory and Its Applications* II,
§8.7.
-/

open MeasureTheory ProbabilityTheory Filter StatLean.Minimaxity StatLean.Bayesian
open scoped ENNReal Topology

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S]

/-- **Ergodicity with rate** (FY Definition 2.4, eq. (2.10)): `F` attracts every starting
state in total variation at rate `ρ ∈ (0, 1]`, i.e. `ρ⁻ⁿ ‖κⁿ(x,·) − F‖_TV → 0` for all
`x`. `ρ = 1` is plain (Harris-type) ergodicity; `ρ < 1` is geometric ergodicity. -/
structure IsErgodicWithRate (κ : Kernel S S) (F : Measure S) (ρ : ℝ≥0∞) : Prop where
  /-- Constitutive (FY Def 2.4): the rate is positive. -/
  rho_pos : 0 < ρ
  /-- Constitutive (FY Def 2.4): the rate is at most one. -/
  rho_le_one : ρ ≤ 1
  /-- Constitutive (FY eq. (2.10)): rated total-variation convergence from every state
  (`tvDist` symmetrized against the book's `‖·‖` only by the constant factor 2). -/
  tendsto : ∀ x : S,
    Tendsto (fun n : ℕ => ρ⁻¹ ^ n * tvDist ((κ ^ n) x) F) atTop (𝓝 0)

/-- **Ergodic kernel** (FY Definition 2.4 with `ρ = 1`). -/
def IsErgodicKernel (κ : Kernel S S) (F : Measure S) : Prop :=
  IsErgodicWithRate κ F 1

/-- **Geometrically ergodic kernel** (FY Definition 2.4 with some `ρ < 1`). -/
def IsGeometricallyErgodic (κ : Kernel S S) (F : Measure S) : Prop :=
  ∃ ρ : ℝ≥0∞, ρ < 1 ∧ IsErgodicWithRate κ F ρ

/-- Rated convergence implies plain total-variation convergence (`ρ⁻¹ ^ n ≥ 1`). -/
theorem IsErgodicWithRate.tendsto_tvDist {κ : Kernel S S} {F : Measure S} {ρ : ℝ≥0∞}
    (h : IsErgodicWithRate κ F ρ) (x : S) :
    Tendsto (fun n : ℕ => tvDist ((κ ^ n) x) F) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h.tendsto x)
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  have h1 : (1 : ℝ≥0∞) ≤ ρ⁻¹ ^ n :=
    one_le_pow_of_one_le' (ENNReal.one_le_inv.mpr h.rho_le_one) n
  calc tvDist ((κ ^ n) x) F = 1 * tvDist ((κ ^ n) x) F := (one_mul _).symm
    _ ≤ ρ⁻¹ ^ n * tvDist ((κ ^ n) x) F := mul_le_mul_left h1 _

/-- Geometric ergodicity is ergodicity. -/
theorem IsGeometricallyErgodic.isErgodicKernel {κ : Kernel S S} {F : Measure S}
    (h : IsGeometricallyErgodic κ F) : IsErgodicKernel κ F := by
  obtain ⟨ρ, -, hr⟩ := h
  exact
    { rho_pos := zero_lt_one
      rho_le_one := le_rfl
      tendsto := fun x => by simpa using hr.tendsto_tvDist x }

-- Kernel powers of a Markov kernel are Markov (no such instance in the pin; a one-line
-- induction over the `Monoid (Kernel S S)` structure, whose `one` is `Kernel.id` and whose
-- `mul` is `∘ₖ`, both of which carry `IsMarkovKernel` instances).
private theorem isMarkovKernel_pow (κ : Kernel S S) [IsMarkovKernel κ] :
    ∀ n : ℕ, IsMarkovKernel (κ ^ n)
  | 0 => by rw [pow_zero]; exact (inferInstance : IsMarkovKernel (Kernel.id : Kernel S S))
  | n + 1 => by
      haveI := isMarkovKernel_pow κ n
      rw [pow_succ]
      exact Kernel.IsMarkovKernel.comp (κ ^ n) κ

-- Chapman–Kolmogorov at a single starting point: one more step is one more `bind`.
-- (`pow_succ'` puts the fresh factor on the left, and `Kernel.comp_apply` turns the left
-- factor into the outer `bind`.)
private theorem pow_succ_apply (κ : Kernel S S) (n : ℕ) (x : S) :
    (κ ^ (n + 1)) x = ((κ ^ n) x).bind κ := by
  rw [pow_succ']
  exact Kernel.comp_apply κ (κ ^ n) x

-- **Kernel averaging is a total-variation contraction.** Directly from the sup-over-events
-- form of `tvDist`: on a measurable `s` the two sides are the integrals of the `[0,1]`-valued
-- measurable function `y ↦ κ y s`, which moves by at most `1 * tvDist μ ν`.
private theorem tvDist_bind_le (κ : Kernel S S) [IsMarkovKernel κ] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (μ.bind κ) (ν.bind κ) ≤ tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => ?_
  rw [Measure.bind_apply hs κ.aemeasurable, Measure.bind_apply hs κ.aemeasurable]
  refine tsub_le_iff_left.mpr ?_
  simpa using
    lintegral_le_lintegral_add_tvDist μ ν (κ.measurable_coe hs) (B := 1) fun _ => prob_le_one

-- One half of "`tvDist = 0` separates points": the sup-form bound on a single event.
private theorem measure_le_of_tvDist_eq_zero {μ ν : Measure S} (h : tvDist μ ν = 0)
    {s : Set S} (hs : MeasurableSet s) : μ s ≤ ν s := by
  have h1 : μ s - ν s ≤ tvDist μ ν :=
    le_iSup₂ (f := fun t (_ : MeasurableSet t) => μ t - ν t) s hs
  rw [h] at h1
  exact tsub_eq_zero_iff_le.mp (le_antisymm h1 (zero_le))

-- `tvDist` separates probability measures (apply the previous lemma in both directions,
-- using symmetry of `tvDist` on probability measures).
private theorem eq_of_tvDist_eq_zero {μ ν : Measure S} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (h : tvDist μ ν = 0) : μ = ν := by
  have h' : tvDist ν μ = 0 := by rwa [tvDist_comm] at h
  ext s hs
  exact le_antisymm (measure_le_of_tvDist_eq_zero h hs) (measure_le_of_tvDist_eq_zero h' hs)

/-- The attracting law of an ergodic Markov kernel is invariant (the invariance half of
FY Theorem 2.2): kernel averaging is a total-variation contraction, so `F = lim κⁿ⁺¹(x,·)
= κ ∘ lim κⁿ(x,·) = κ ∘ F`. -/
theorem IsErgodicKernel.invariant {κ : Kernel S S} [IsMarkovKernel κ] {F : Measure S}
    [IsProbabilityMeasure F] (h : IsErgodicKernel κ F) [Nonempty S] :
    κ.Invariant F := by
  obtain ⟨x⟩ := ‹Nonempty S›
  have hdt : Tendsto (fun n : ℕ => tvDist ((κ ^ n) x) F) atTop (𝓝 0) :=
    IsErgodicWithRate.tendsto_tvDist h x
  -- `F` is within `tvDist F (κⁿ⁺¹(x,·))` plus a contraction of `tvDist (κⁿ(x,·)) F` of `F ∘ κ`.
  have key : ∀ n : ℕ,
      tvDist F (F.bind κ) ≤ tvDist ((κ ^ (n + 1)) x) F + tvDist ((κ ^ n) x) F := by
    intro n
    haveI := isMarkovKernel_pow κ n
    haveI := isMarkovKernel_pow κ (n + 1)
    -- one more step of the chain is one more kernel average, which contracts `tvDist`
    have hstep : tvDist ((κ ^ (n + 1)) x) (F.bind κ) ≤ tvDist ((κ ^ n) x) F := by
      rw [pow_succ_apply]
      exact tvDist_bind_le κ ((κ ^ n) x) F
    have htri : tvDist F (F.bind κ)
        ≤ tvDist F ((κ ^ (n + 1)) x) + tvDist ((κ ^ (n + 1)) x) (F.bind κ) :=
      tvDist_triangle F ((κ ^ (n + 1)) x) (F.bind κ)
    rw [tvDist_comm F ((κ ^ (n + 1)) x)] at htri
    exact htri.trans (add_le_add le_rfl hstep)
  have hlim : Tendsto
      (fun n : ℕ => tvDist ((κ ^ (n + 1)) x) F + tvDist ((κ ^ n) x) F) atTop (𝓝 0) := by
    simpa using (hdt.comp (tendsto_add_atTop_nat 1)).add hdt
  have h0 : tvDist F (F.bind κ) = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall key)) (zero_le)
  exact (eq_of_tvDist_eq_zero h0).symm

-- `∫⁻ a − ∫⁻ b ≤ ∫⁻ (a − b)` in `ℝ≥0∞` (truncated subtraction), for measurable `b`. The
-- `≤`-mover behind the dominated-convergence step of `eq_of_invariant_of_isErgodicKernel`.
private theorem lintegral_sub_le_lintegral_sub {μ : Measure S} (a b : S → ℝ≥0∞)
    (hb : Measurable b) :
    (∫⁻ y, a y ∂μ) - (∫⁻ y, b y ∂μ) ≤ ∫⁻ y, (a y - b y) ∂μ := by
  refine tsub_le_iff_right.2 ?_
  rw [← lintegral_add_right _ hb]
  exact lintegral_mono fun y => le_tsub_add

/-- **Ergodicity pins down the invariant law.** If `κ` attracts every starting state to `F`
in total variation, then `F` is its *only* invariant probability law: for an invariant `ξ`
and a measurable `s`, `ξ s = ∫ κⁿ(y, s) dξ(y)` for every `n`, and the integrand converges to
`F s` uniformly enough (it is `[0,1]`-valued) for dominated convergence to apply. The
converse of `IsErgodicKernel.invariant`, and the uniqueness statement the Harris route needs
in order to transport an invariant law of `κ^p` back to `κ`. -/
theorem eq_of_invariant_of_isErgodicKernel {κ : Kernel S S} [IsMarkovKernel κ]
    {F ξ : Measure S} [IsProbabilityMeasure F] [IsProbabilityMeasure ξ]
    (hF : IsErgodicKernel κ F) (hξ : Kernel.Invariant κ ξ) : ξ = F := by
  ext s hs
  have hstep : ∀ n : ℕ, ξ s = ∫⁻ y, ((κ ^ n) y) s ∂ξ := by
    intro n
    conv_lhs => rw [← (invariant_pow hξ n).def]
    rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  have hmeas : ∀ n : ℕ, Measurable fun y : S => ((κ ^ n) y) s := fun n =>
    Kernel.measurable_coe _ hs
  have hcst : (∫⁻ _ : S, F s ∂ξ) = F s := by simp
  -- a `[0,1]`-valued sequence dominated by the ergodic envelope integrates to zero
  have hDCT : ∀ G : ℕ → S → ℝ≥0∞, (∀ n, Measurable (G n)) →
      (∀ n y, G n y ≤ tvDist ((κ ^ n) y) F) →
      Tendsto (fun n => ∫⁻ y, G n y ∂ξ) atTop (𝓝 0) := by
    intro G hGm hGle
    have := tendsto_lintegral_of_dominated_convergence (μ := ξ) (F := G) (f := fun _ => 0)
      (fun _ => 1) hGm (fun n => Eventually.of_forall fun y => ?_)
      (by simp) (Eventually.of_forall fun y => ?_)
    · simpa using this
    · haveI := isMarkovKernel_pow κ n
      exact (hGle n y).trans (tvDist_le_one _ _)
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (hF.tendsto_tvDist y) (Eventually.of_forall fun n => zero_le)
        (Eventually.of_forall fun n => hGle n y)
  refine le_antisymm ?_ ?_
  · have hb : ∀ n : ℕ, ξ s - F s ≤ ∫⁻ y, (((κ ^ n) y) s - F s) ∂ξ := by
      intro n
      have h := lintegral_sub_le_lintegral_sub (μ := ξ)
        (fun y => ((κ ^ n) y) s) (fun _ => F s) measurable_const
      rwa [hcst, ← hstep n] at h
    have hlim := hDCT (fun n y => ((κ ^ n) y) s - F s) (fun n => (hmeas n).sub measurable_const)
      (fun n y => le_iSup₂ (f := fun t (_ : MeasurableSet t) => ((κ ^ n) y) t - F t) s hs)
    exact tsub_eq_zero_iff_le.1
      (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hb)) (zero_le))
  · have hb : ∀ n : ℕ, F s - ξ s ≤ ∫⁻ y, (F s - ((κ ^ n) y) s) ∂ξ := by
      intro n
      have h := lintegral_sub_le_lintegral_sub (μ := ξ)
        (fun _ => F s) (fun y => ((κ ^ n) y) s) (hmeas n)
      rwa [hcst, ← hstep n] at h
    have hlim := hDCT (fun n y => F s - ((κ ^ n) y) s) (fun n => measurable_const.sub (hmeas n))
      (fun n y => by
        haveI := isMarkovKernel_pow κ n
        rw [tvDist_comm]
        exact le_iSup₂ (f := fun t (_ : MeasurableSet t) => F t - ((κ ^ n) y) t) s hs)
    exact tsub_eq_zero_iff_le.1
      (le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hb)) (zero_le))

/-- Transition kernel of the **vectorized nonlinear autoregression** (FY eqs.
(2.7)–(2.8)): from state `x = (X_{t-1}, …, X_{t-p-1})` draw `ε ∼ ν` and move to
`(f(x) + ε, x₀, …, x_{p-1})`. -/
noncomputable def nlARKernel {p : ℕ} (f : (Fin (p + 1) → ℝ) → ℝ) (ν : Measure ℝ) :
    Kernel (Fin (p + 1) → ℝ) (Fin (p + 1) → ℝ) :=
  ((Kernel.id : Kernel (Fin (p + 1) → ℝ) (Fin (p + 1) → ℝ)).prod
    (Kernel.const _ ν)).map fun xe =>
      (Fin.cons (f xe.1 + xe.2) (fun i => xe.1 i.castSucc) : Fin (p + 1) → ℝ)

/-- The nonlinear-AR kernel is Markov for measurable `f` and a probability noise law. -/
theorem isMarkovKernel_nlARKernel {p : ℕ} {f : (Fin (p + 1) → ℝ) → ℝ}
    (hf : Measurable f) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsMarkovKernel (nlARKernel f ν) := by
  have hmeas : Measurable fun xe : (Fin (p + 1) → ℝ) × ℝ =>
      (Fin.cons (f xe.1 + xe.2) (fun i => xe.1 i.castSucc) : Fin (p + 1) → ℝ) := by
    rw [measurable_pi_iff]
    refine Fin.cases ?_ ?_
    · simpa using! (hf.comp measurable_fst).add measurable_snd
    · exact fun i => by simpa using! (measurable_pi_apply i.castSucc).comp measurable_fst
  exact Kernel.IsMarkovKernel.map _ hmeas

-- **FY Theorem 2.4(ii)** (`nlARKernel_geometricallyErgodic`) used to be stated here as a
-- named `sorry`.  It is now **PROVED**, and lives one file downstream, in
-- `ForMathlib/Markov/HarrisTheorem.lean`: its proof consumes `harris_theorem`,
-- `IsGeometricallyErgodic.of_pow` and `HasLyapunovDrift`, all of which are defined there,
-- and `HarrisTheorem.lean` imports *this* file (for `IsGeometricallyErgodic`,
-- `IsErgodicWithRate` and `nlARKernel`), so the statement cannot stay on this side of the
-- import edge.  Nothing outside its own file referenced it, so no consumer moved with it.

end StatLean.TimeSeries
