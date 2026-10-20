module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.SupMeasurability
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

/-!
# Pointwise-dense (VW pointwise-measurable) foundation for empirical-process suprema

This file replaces the **unsatisfiable** `EmpProcSeparable` predicate
(`SupMeasurability.lean`, which `empProcSeparable_singleton_forces_zero` shows
is unsatisfiable for uncountable `F`) with a satisfiable, book-faithful
van der Vaart–Wellner **pointwise-measurable / pointwise-dense** predicate
(`EmpProcPointwiseDense`).

The fatal flaw of `EmpProcSeparable` was its `∀ S ⊆ F` quantifier: applied to
a singleton `S = {f}` with `f ∈ F \ F'` it forces the empirical process to
vanish at `f` (generically false). The fix is the genuine VW form:

> there is a *countable* `F' ⊆ F` such that **every** `f ∈ F` is the pointwise
> limit of a sequence drawn from `F'`, with a single integrable envelope `Φ`
> dominating the whole class.

This is an **existential approximating-sequence-per-`f`** predicate, never a
`∀ S` sup-equality. It is satisfiable (a pointwise-dense countable subclass is
exactly what a separable / pointwise-measurable class supplies), and the
whole-class sup-equality the measurability bridge needs is **derived** inside
the proof from the per-`f` approximating sequences via dominated convergence,
not carried as a hypothesis.

## Main declarations

* `EmpProcPointwiseDense` — the VW pointwise-dense predicate.
* `measurable_biSup_ofReal_abs_transformedEmpProcess_dense` — the
  load-bearing whole-class measurability bridge, with its `AEMeasurable`
  corollary for raw, truncated, and link-term suprema.
* `empProcPointwiseDense_dominator_of_envelope` — turns the project's
  `IsEnvelope` + `MemLp Φ 2 P` envelope hypotheses into the predicate's
  dominator clause.

Reference: van der Vaart & Wellner, *Weak Convergence and Empirical Processes*
(Springer, 1996), §2.3.3 (pointwise-measurable class); van der Vaart,
*Asymptotic Statistics* (Cambridge, 1998), §2.3.3 / §19 (measurability of
suprema via a countable pointwise-dense subclass).
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The pointwise-density predicate -/

/-- **Pointwise-dense (VW pointwise-measurable) class** for the empirical
process. There is a *countable* subclass `F' ⊆ F` such that:

* every `f ∈ F` is the **pointwise limit** of a sequence `φ : ℕ → (Ω → ℝ)`
  drawn entirely from `F'` (`∀ m, φ m ∈ F'` and `φ m x → f x` for every `x`);
* the whole class `F` has a single **integrable envelope** `Φ` (`|g x| ≤ Φ x`
  for every `g ∈ F` and every `x`).

This is the satisfiable replacement for the unsatisfiable `EmpProcSeparable`:
it is an *existential approximating-sequence-per-`f`* statement, never a
`∀ S ⊆ F` sup-equality, so the singleton-forces-zero collapse
(`empProcSeparable_singleton_forces_zero`) does not apply. The whole-class
sup-equality needed for measurability is *derived* from these data inside
`measurable_biSup_ofReal_abs_transformedEmpProcess_dense` via dominated
convergence. -/
def EmpProcPointwiseDense (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop :=
  ∃ F' ⊆ F, F'.Countable ∧
    (∀ f ∈ F, ∃ φ : ℕ → (Ω → ℝ),
        (∀ m, φ m ∈ F') ∧ (∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))) ∧
    (∃ Φ : Ω → ℝ, Integrable Φ P ∧ ∀ g ∈ F, ∀ x, |g x| ≤ Φ x)

/-! ### Whole-class measurability

The proof has four steps:

1. extract `F'`, the per-`f` approximating sequences, and the envelope `Φ`;
2. **DCT-continuity** — for a fixed sample `ξ`, the transformed empirical
   process is continuous along `φ_k → f` (finite sample sum is continuous;
   the `∫ ((f−a)·b) dP` term converges by dominated convergence);
3. **whole-class sup-equality** — derived *pointwise in `ξ`* from step 2, with
   no `∀ S` quantifier and no forced vanishing;
4. close with `Measurable.biSup` over the countable `F'`.
-/

variable {Ξ : Type*} [MeasurableSpace Ξ] {P : Measure Ω}

/-- **DCT-continuity of the transformed empirical process along a pointwise
limit.** If `φ_k → f` pointwise, every `φ_k` and `f` are dominated by `Φ`
(so that the integrands `(φ_k − a)·b` and `(f − a)·b` are dominated by the
fixed integrable bound `(Φ + |a|)·|b|`), then for any fixed sample `Y` the
real values `transformedEmpProcess P n Y a b (φ_k)` converge to
`transformedEmpProcess P n Y a b f`.

The finite empirical-average sum converges by `tendsto_finsetSum` (continuity
of finite sums under pointwise convergence of the integrand evaluations); the
population integral converges by `tendsto_integral_of_dominated_convergence`. -/
lemma tendsto_transformedEmpProcess_of_tendsto
    (n : ℕ) (Y : Fin n → Ω) {a b : Ω → ℝ} {f : Ω → ℝ} {φ : ℕ → (Ω → ℝ)}
    {Φ_dom : Ω → ℝ}
    (hφ_lim : ∀ x, Tendsto (fun m => φ m x) atTop (𝓝 (f x)))
    (hbound : Integrable (fun x => (Φ_dom x + |a x|) * |b x|) P)
    (hφ_meas : ∀ m, AEStronglyMeasurable (fun x => (φ m x - a x) * b x) P)
    (hφ_dom : ∀ m, ∀ x, |φ m x| ≤ Φ_dom x) :
    Tendsto (fun m => transformedEmpProcess P n Y a b (φ m)) atTop
      (𝓝 (transformedEmpProcess P n Y a b f)) := by
  -- bound `|(g − a)·b| ≤ (Φ + |a|)·|b|` pointwise for any `g` dominated by `Φ`
  have hpt : ∀ (g : Ω → ℝ), (∀ x, |g x| ≤ Φ_dom x) → ∀ x,
      ‖(g x - a x) * b x‖ ≤ (Φ_dom x + |a x|) * |b x| := by
    intro g hg x
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |g x - a x| ≤ Φ_dom x + |a x| :=
      (abs_sub (g x) (a x)).trans (by gcongr; exact hg x)
    exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  unfold transformedEmpProcess empiricalProcess empiricalAvg
  -- the population-integral term converges by DCT
  have hint : Tendsto (fun m => ∫ x, (φ m x - a x) * b x ∂P) atTop
      (𝓝 (∫ x, (f x - a x) * b x ∂P)) :=
    tendsto_integral_of_dominated_convergence
      (fun x => (Φ_dom x + |a x|) * |b x|) hφ_meas hbound
      (fun m => Eventually.of_forall (hpt (φ m) (hφ_dom m)))
      (Eventually.of_forall (fun x =>
        ((hφ_lim x).sub tendsto_const_nhds).mul tendsto_const_nhds))
  -- the finite empirical-average sum converges by continuity of finite sums
  have hsum : Tendsto (fun m => ∑ i, (φ m (Y i) - a (Y i)) * b (Y i)) atTop
      (𝓝 (∑ i, (f (Y i) - a (Y i)) * b (Y i))) :=
    tendsto_finset_sum Finset.univ
      (fun i _ => ((hφ_lim (Y i)).sub tendsto_const_nhds).mul tendsto_const_nhds)
  exact (tendsto_const_nhds.mul
    (((tendsto_const_nhds.mul hsum)).sub hint))

/-- **Whole-class measurability bridge.**

Given pointwise-density of `F`, per-index measurability, and a dominator clause
ensuring the affine integrand `(f − a)·b` is `L¹(P)`-dominated uniformly over
`f ∈ F`, the map
`ξ ↦ ⨆ f ∈ F, ofReal|𝔾ₙ((f − a)·b)(ξ)|` is measurable.

Proof in four steps: extract the countable `F'`, the per-`f`
approximating sequences, and the envelope; show DCT-continuity of
`f ↦ ofReal|𝔾ₙ((f−a)·b)(ξ)|` along `φ_k → f`; *derive* (pointwise in `ξ`, with
no `∀ S` quantifier) the sup-equality `⨆_{f∈F} = ⨆_{g∈F'}`; close with
`Measurable.biSup` over the countable `F'`. -/
lemma measurable_biSup_ofReal_abs_transformedEmpProcess_dense
    {F : Set (Ω → ℝ)} (hDense : EmpProcPointwiseDense F P)
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    -- The dominator clause supplies the uniform bound required by DCT: an
    -- integrable bound `Φ` for `F` such that `(Φ + |a|)·|b|` is integrable.
    {Φ_dom : Ω → ℝ} (hΦ_dom : ∀ g ∈ F, ∀ x, |g x| ≤ Φ_dom x)
    (hbound : Integrable (fun x => (Φ_dom x + |a x|) * |b x|) P)
    (n : ℕ) :
    Measurable (fun ξ : Ξ =>
      ⨆ f ∈ F, ENNReal.ofReal
        |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f|) := by
  obtain ⟨F', hF'sub, hF'ct, hApprox, -⟩ := hDense
  -- measurability of the affine integrand for any measurable `g`
  have hg_meas : ∀ {g : Ω → ℝ}, Measurable g →
      AEStronglyMeasurable (fun x => (g x - a x) * b x) P :=
    fun hg => ((hg.sub ha).mul hb).aestronglyMeasurable
  -- STEP 3: derive the whole-class sup-equality, pointwise in ξ
  have hsup_eq : ∀ (ξ : Ξ),
      (⨆ f ∈ F, ENNReal.ofReal
        |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f|)
        = ⨆ g ∈ F', ENNReal.ofReal
            |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b g| := by
    intro ξ
    apply le_antisymm
    · -- `≤` : each `f ∈ F` is a limit of `F'`-terms, each `≤ ⨆_{F'}`
      refine iSup₂_le (fun f hf => ?_)
      -- Extract `f`'s approximating sequence `φf ⊆ F'`.
      obtain ⟨φf, hφmem, hφlim⟩ := hApprox f hf
      -- DCT-continuity: `ofReal|T (φf m)| → ofReal|T f|`
      have htend := tendsto_transformedEmpProcess_of_tendsto
        (Φ_dom := Φ_dom) n (fun i : Fin n => X i.val ξ) hφlim hbound
        (fun m => hg_meas (hF_meas _ (hF'sub (hφmem m))))
        (fun m x => hΦ_dom _ (hF'sub (hφmem m)) x)
      have hcont : Tendsto (fun m =>
            ENNReal.ofReal |transformedEmpProcess P n
              (fun i : Fin n => X i.val ξ) a b (φf m)|) atTop
          (𝓝 (ENNReal.ofReal |transformedEmpProcess P n
              (fun i : Fin n => X i.val ξ) a b f|)) :=
        (ENNReal.continuous_ofReal.tendsto _).comp
          ((continuous_abs.tendsto _).comp htend)
      refine le_of_tendsto' hcont (fun m => ?_)
      exact le_iSup₂ (f := fun g _ => ENNReal.ofReal |transformedEmpProcess P n
        (fun i : Fin n => X i.val ξ) a b g|) (φf m) (hφmem m)
    · -- `≥` : `F' ⊆ F`
      exact iSup₂_mono' (fun g hg => ⟨g, hF'sub hg, le_refl _⟩)
  -- STEP 4: rewrite by the sup-equality and close over the countable `F'`
  have hrw : (fun ξ : Ξ =>
        ⨆ f ∈ F, ENNReal.ofReal
          |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f|)
      = (fun ξ : Ξ =>
        ⨆ g ∈ F', ENNReal.ofReal
          |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b g|) :=
    funext hsup_eq
  rw [hrw]
  refine Measurable.biSup F' hF'ct (fun g hg => ?_)
  exact measurable_ofReal_abs_transformedEmpProcess hX_meas n
    (hF_meas g (hF'sub hg)) ha hb

/-- **`AEMeasurable` corollary of the whole-class bridge** (the form
`lintegral_add` / `lintegral_tsum` consume to split `∫⁻ (Σ …) = Σ ∫⁻ …`). -/
lemma aemeasurable_biSup_ofReal_abs_transformedEmpProcess_dense
    {F : Set (Ω → ℝ)} (hDense : EmpProcPointwiseDense F P)
    {X : ℕ → Ξ → Ω} (hX_meas : ∀ i, Measurable (X i))
    (hF_meas : ∀ f ∈ F, Measurable f)
    {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b)
    {Φ_dom : Ω → ℝ} (hΦ_dom : ∀ g ∈ F, ∀ x, |g x| ≤ Φ_dom x)
    (hbound : Integrable (fun x => (Φ_dom x + |a x|) * |b x|) P)
    (n : ℕ) (μ : Measure Ξ) :
    AEMeasurable (fun ξ : Ξ =>
      ⨆ f ∈ F, ENNReal.ofReal
        |transformedEmpProcess P n (fun i : Fin n => X i.val ξ) a b f|) μ :=
  (measurable_biSup_ofReal_abs_transformedEmpProcess_dense hDense hX_meas hF_meas
    ha hb hΦ_dom hbound n).aemeasurable

/-! ### Dominator construction

Turns the project's existing envelope hypotheses (`IsEnvelope F Φ`,
`MemLp Φ 2 P`) into the predicate's dominator clause. Thus no separate
dominator is needed. On a probability measure, `MemLp Φ 2 P` implies
`Integrable Φ P` via `MemLp.mono_exponent` (`2 ≥ 1`) + `memLp_one_iff_integrable`. -/

/-- **Dominator builder.** An `L²` envelope on a probability measure gives
the predicate's integrable-dominator clause. -/
lemma empProcPointwiseDense_dominator_of_envelope
    [IsProbabilityMeasure P] {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    (hEnv : IsEnvelope F Φ) (hΦ : MemLp Φ 2 P) :
    ∃ Φ' : Ω → ℝ, Integrable Φ' P ∧ ∀ g ∈ F, ∀ x, |g x| ≤ Φ' x := by
  refine ⟨Φ, ?_, fun g hg x => hEnv g hg x⟩
  exact memLp_one_iff_integrable.mp (hΦ.mono_exponent (by norm_num))

end AsymptoticStatistics.EmpiricalProcess
