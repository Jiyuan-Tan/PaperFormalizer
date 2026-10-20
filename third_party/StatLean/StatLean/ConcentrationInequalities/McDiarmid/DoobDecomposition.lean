module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Process.Filtration
public import StatLean.ConcentrationInequalities.McDiarmid.CondHoeffding

@[expose] public section

/-! # Doob-martingale MGF bound (Lu-BDA §5.1, Theorem 5.1, McDiarmid Inequality)

We prove that McDiarmid's bounded-differences function satisfies
`HasSubgaussianMGF (f(X) − E[f(X)]) (∑ₖ (‖cₖ‖₊/2)²) μ`
by building the Doob martingale Mₖ = E[f(X) | σ(X₀,...,Xₖ₋₁)] and applying
Mathlib's Azuma–Hoeffding tower theorem `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`.

MGF bound: `∀ λ, E[exp(λ(f(X) − E[f(X)]))] ≤ exp(λ² ∑ₖ cₖ²/8)`.

**Architecture:**
1. `allVars`, `natFiltration`, `doobMartingale`, `doobIncrement` — the core objects.
2. Independence-factorization machinery (`§5.1`): `projVars`/`combineAt`/`condMean`,
   `condDistrib_eq_const_of_indepFun` (independence ⇒ conditional law = marginal),
   `condExpKernel_ae_eq_const_of_measurable` (fiber-constancy), `increment_factorization`
   (`Mⱼ = condMean` of the prefix block), `condMean_update_le` (oscillation `≤ cₖ`).
3. `increment_bounded_of_bounded_differences` — the per-increment `[−cₖ, cₖ]` / fiber-wise
   `[a, a+cₖ]` bounds, assembled from the §5.1 machinery (zero `sorry`).
4. `increment_hasCondSubgaussianMGF` — proved by wrapping `condExp_hoeffding_mgf`
   (CondHoeffding.lean) fiber-by-fiber.
5. `mgf_sub_expectation_le` — proved rigorously via
   `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

section FiberConstancy

-- Variable order `{m} [mΩ]` keeps `mΩ` as the canonical `MeasurableSpace Ω` instance for
-- `Measure Ω`, while exposing the sub-σ-algebra `m` as a hypothesis (cf. Mathlib's
-- `condExpKernel` API). This block is `β`-free, so it lives outside `DoobDecomposition`.
variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {α : Type*} [MeasurableSpace α] [MeasurableEq α]

/-- **Helper.** Any `m`-measurable function is a.e. constant (equal to its value at `ω'`) on the
fiber `condExpKernel μ m ω'`. Proof: under `μ.trim hm ⊗ₘ condExpKernel μ m` the pair `(ω', ω)`
is supported on the diagonal, so `g ω = g ω'` a.e. -/
private lemma condExpKernel_ae_eq_const_of_measurable (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → α} (hg : Measurable[m] g) :
    ∀ᵐ ω' ∂(μ.trim hm), ∀ᵐ ω ∂(condExpKernel μ m ω'), g ω = g ω' := by
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim hm
  have hcompProd :
      ∀ᵐ p ∂((μ.trim hm) ⊗ₘ condExpKernel μ m), g p.2 = g p.1 := by
    rw [compProd_trim_condExpKernel hm]
    have hdiag : @AEMeasurable Ω (Ω × Ω) (m.prod mΩ) mΩ (fun ω => (id ω, id ω)) μ :=
      @Measurable.aemeasurable Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω => (id ω, id ω)) μ
        (@Measurable.prodMk Ω mΩ Ω Ω m mΩ id id (measurable_id'' hm) measurable_id)
    have hset : MeasurableSet[m.prod mΩ] {p : Ω × Ω | g p.2 = g p.1} :=
      measurableSet_eq_fun ((hg.mono hm le_rfl).comp measurable_snd) (hg.comp measurable_fst)
    exact (@ae_map_iff Ω (Ω × Ω) mΩ (m.prod mΩ) μ (fun ω => (id ω, id ω))
      hdiag (fun p => g p.2 = g p.1) hset).mpr (ae_of_all _ (fun ω => rfl))
  exact Measure.ae_ae_of_ae_compProd hcompProd

end FiberConstancy

section DoobDecomposition

variable {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {β : Fin n → Type*} [(i : Fin n) → MeasurableSpace (β i)]
  -- LEAN-ONLY: standard-Borel coordinate spaces; needed for condDistrib / condExpKernel
  -- disintegration of the per-coordinate conditional laws. Polish/finite/countable
  -- coordinate spaces all qualify, so this is a mild standard restriction.
  [∀ i, StandardBorelSpace (β i)] [∀ i, Nonempty (β i)]

/-! ### §1 Objects -/

/-- Pack `n` random variables into a product-valued map.
    Constitutive (Lu-BDA §5.1): the joint observable. -/
def allVars (X : ∀ i : Fin n, Ω → β i) : Ω → Π i : Fin n, β i :=
  fun ω i => X i ω

/-- Natural filtration Fₖ = σ(X₀,...,Xₖ₋₁).
    Constitutive (Lu-BDA §5.1): reveals coordinates one at a time. -/
noncomputable def natFiltration
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i)) :
    Filtration ℕ mΩ where
  seq k := ⨆ j : {j : Fin n // (j : ℕ) < k}, MeasurableSpace.comap (X j.1) inferInstance
  mono' {k l} hkl := iSup_le fun ⟨j, hj⟩ => le_iSup_of_le ⟨j, hj.trans_le hkl⟩ le_rfl
  -- LEAN-ONLY: after destructuring {j : Fin n // j.val < k}, j : Fin n so hX j applies.
  le' k := iSup_le fun ⟨j, _⟩ => measurable_iff_comap_le.mp (hX j)

/-- Doob martingale Mₖ = E[f(X) | Fₖ]. -/
noncomputable def doobMartingale
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  fun k => μ[f ∘ allVars X | (natFiltration X hX) k]

/-- Doob increment: Δ₀ = 0, Δₖ₊₁ = Mₖ₊₁ − Mₖ. -/
noncomputable def doobIncrement
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω) : ℕ → Ω → ℝ
  | 0 => 0
  | k + 1 => doobMartingale X hX f μ (k + 1) - doobMartingale X hX f μ k

/-! ### §2 Structural lemmas -/

private lemma natFiltration_zero_eq_bot
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i)) :
    (natFiltration X hX) 0 = ⊥ := by
  show (⨆ j : {j : Fin n // (j : ℕ) < 0},
        MeasurableSpace.comap (X j.1) inferInstance) = ⊥
  exact le_antisymm
    (iSup_le (fun ⟨_, hj⟩ => absurd hj (Nat.not_lt_zero _)))
    bot_le

private lemma natFiltration_n_stronglyMeasurable
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f) :
    StronglyMeasurable[(natFiltration X hX) n] (f ∘ allVars X) := by
  -- Override the ambient MeasurableSpace Ω with (natFiltration X hX) n so that
  -- standard lemmas (measurable_pi_lambda, measurable_iff_comap_le) produce the
  -- correct domain sigma-algebra without explicit @ annotations.
  letI : MeasurableSpace Ω := (natFiltration X hX) n
  suffices h : Measurable (f ∘ allVars X) from h.stronglyMeasurable
  apply hf.comp
  apply measurable_pi_lambda
  intro i
  -- X i is measurable w.r.t. (natFiltration X hX) n because
  -- comap (X i) inferInstance ≤ ⨆ j, comap (X j) inferInstance = (natFiltration X hX) n.
  exact measurable_iff_comap_le.mpr
    (le_iSup_of_le (⟨i, i.isLt⟩ : {j : Fin n // (j : ℕ) < n}) le_rfl)

private lemma doobMartingale_zero_eq_mean
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) {μ : Measure Ω} [IsProbabilityMeasure μ] :
    doobMartingale X hX f μ 0 = fun _ => ∫ ω', f (allVars X ω') ∂μ := by
  simp only [doobMartingale]
  rw [show (natFiltration X hX) 0 = ⊥ from natFiltration_zero_eq_bot X hX]
  simp [condExp_bot, Function.comp]

private lemma doobMartingale_n_eq_f
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f) {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hf_int : Integrable (f ∘ allVars X) μ) :
    doobMartingale X hX f μ n = f ∘ allVars X := by
  simp only [doobMartingale]
  -- SigmaFinite (μ.trim hm) is derived from IsFiniteMeasure, which follows from
  -- IsProbabilityMeasure μ + isFiniteMeasure_trim.
  haveI : IsFiniteMeasure (μ.trim ((natFiltration X hX).le n)) :=
    isFiniteMeasure_trim ((natFiltration X hX).le n)
  exact condExp_of_stronglyMeasurable ((natFiltration X hX).le n)
    (natFiltration_n_stronglyMeasurable X hX f hf) hf_int

private lemma sum_doobIncrement_telescope
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω)
    (k : ℕ) (ω : Ω) :
    ∑ i ∈ Finset.range (k + 1), doobIncrement X hX f μ i ω =
      doobMartingale X hX f μ k ω - doobMartingale X hX f μ 0 ω := by
  induction k with
  | zero => simp [doobIncrement]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [doobIncrement, Pi.sub_apply]
    ring

private lemma doobIncrement_stronglyAdapted
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    StronglyAdapted (natFiltration X hX) (doobIncrement X hX f μ) := by
  intro k
  match k with
  | 0 => exact stronglyMeasurable_const
  | k + 1 =>
    -- Unfold to: StronglyMeasurable[(natFiltration X hX) (k+1)]
    --   (μ[f ∘ allVars X | (natFiltration X hX) (k+1)] - μ[f ∘ allVars X | (natFiltration X hX) k])
    simp only [doobIncrement, doobMartingale]
    exact stronglyMeasurable_condExp.sub
      (stronglyMeasurable_condExp.mono ((natFiltration X hX).mono' (Nat.le_succ k)))

/-! ### §3 Sub-Gaussian parameter book-keeping -/

private noncomputable def doobCY (c : Fin n → ℝ) : ℕ → ℝ≥0
  | 0 => 0
  | k + 1 => if hk : k < n then (‖c ⟨k, hk⟩‖₊ / 2) ^ 2 else 0

private lemma doobCY_zero (c : Fin n → ℝ) : doobCY c 0 = 0 := rfl

private lemma doobCY_succ (c : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    doobCY c (k + 1) = (‖c ⟨k, hk⟩‖₊ / 2) ^ 2 := by simp [doobCY, hk]

private lemma sum_doobCY_eq (c : Fin n → ℝ) :
    ∑ i ∈ Finset.range (n + 1), doobCY c i = ∑ k : Fin n, (‖c k‖₊ / 2) ^ 2 := by
  -- sum_range_succ' rewrites ∑_{i<n+1} = ∑_{i<n} f(i+1) + f(0).
  rw [Finset.sum_range_succ', doobCY_zero, add_zero]
  -- sum_fin_eq_sum_range rewrites ∑_{k:Fin n} = ∑_{i<n} if h:i<n then f⟨i,h⟩ else 0.
  rw [Finset.sum_fin_eq_sum_range]
  -- Both sums now over range n; each term equals doobCY c (i+1) = if h:i<n then ... else 0.
  -- congr 1 closes by definitional equality of doobCY.
  congr 1

/-! ### §5.1 Independence factorization machinery -/

/-- Coordinates of `X` in the index set `S`, with coordinates outside `S` replaced by an
    arbitrary fixed value. LEAN-ONLY: packages the `σ(Xᵢ : i ∈ S)`-measurable "block" of
    `allVars X` as a single map into the (standard-Borel) product space, so we can feed it
    to `condDistrib` / `condExp_prod_ae_eq_integral_condDistrib`. -/
private noncomputable def projVars (X : ∀ i : Fin n, Ω → β i) (S : Finset (Fin n)) :
    Ω → Π i : Fin n, β i :=
  fun ω i => if i ∈ S then X i ω else Classical.arbitrary (β i)

/-- Reassemble a product value from its `S`-block (`w`) and `Sᶜ`-block (`v`). -/
private def combineAt (S : Finset (Fin n)) (w v : Π i : Fin n, β i) : Π i : Fin n, β i :=
  fun i => if i ∈ S then w i else v i

/-- The prefix index set `{i : Fin n | (i : ℕ) < j}`, generating the filtration level `Fⱼ`. -/
private def headSet (j : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < j)

private lemma measurable_projVars (X : ∀ i : Fin n, Ω → β i)
    (hX : ∀ i : Fin n, Measurable (X i)) (S : Finset (Fin n)) :
    Measurable (projVars X S) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i ∈ S
  · simp only [projVars, h, if_true]; exact hX i
  · simp only [projVars, h, if_false]; exact measurable_const

private lemma measurable_combineAt (S : Finset (Fin n)) :
    Measurable (fun p : (Π i : Fin n, β i) × (Π i : Fin n, β i) => combineAt S p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i ∈ S
  · simp only [combineAt, h, if_true]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [combineAt, h, if_false]; exact (measurable_pi_apply i).comp measurable_snd

/-- On the `S`-block / `Sᶜ`-block decomposition, recombining reproduces `allVars X`. -/
private lemma combineAt_projVars (X : ∀ i : Fin n, Ω → β i) (S : Finset (Fin n)) (ω : Ω) :
    combineAt S (projVars X S ω) (projVars X Sᶜ ω) = allVars X ω := by
  funext i
  by_cases h : i ∈ S
  · simp only [combineAt, projVars, h, if_true, allVars]
  · have hc : i ∈ Sᶜ := Finset.mem_compl.mpr h
    simp only [combineAt, projVars, h, if_false, hc, if_true, allVars]

/-- **Helper (STEP 1).** If `W` and `Z` are independent, the conditional distribution of `Z`
given `W` is a.e. the constant kernel returning `Z`'s marginal law `μ.map Z`. -/
private lemma condDistrib_eq_const_of_indepFun
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {γ : Type*} [MeasurableSpace γ]
    {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    {W : α → γ} {Z : α → δ} (hW : Measurable W) (hZ : Measurable Z)
    (h : IndepFun W Z μ) :
    condDistrib Z W μ =ᵐ[μ.map W] Kernel.const γ (μ.map Z) := by
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  have h2 : μ.map (fun a => (W a, Z a)) = (μ.map W) ⊗ₘ (Kernel.const γ (μ.map Z)) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hZ.aemeasurable).1 h,
        Measure.compProd_const]
  exact condDistrib_ae_eq_of_measure_eq_compProd W hZ.aemeasurable h2

/-- The σ-algebra generated by the prefix block `projVars X (headSet j)` is exactly the
filtration level `Fⱼ = σ(X₀,...,Xⱼ₋₁)`. -/
private lemma comap_projVars_headSet
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i)) (j : ℕ) :
    MeasurableSpace.comap (projVars X (headSet j)) inferInstance = (natFiltration X hX) j := by
  apply le_antisymm
  · -- `comap ≤ Fⱼ`: `projVars X (headSet j)` is `Fⱼ`-measurable.
    letI : MeasurableSpace Ω := (natFiltration X hX) j
    refine measurable_iff_comap_le.mp ?_
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases h : i ∈ headSet j
    · have hij : (i : ℕ) < j := by simpa [headSet, Finset.mem_filter] using h
      simp only [projVars, h, if_true]
      exact measurable_iff_comap_le.mpr
        (le_iSup_of_le (⟨i, hij⟩ : {l : Fin n // (l : ℕ) < j}) le_rfl)
    · simp only [projVars, h, if_false]; exact measurable_const
  · -- `Fⱼ ≤ comap`: each generator `comap (X l)` (with `l < j`) factors through `projVars`.
    refine iSup_le ?_
    rintro ⟨l, hl⟩
    have hxl : X l = (fun w : Π i : Fin n, β i => w l) ∘ (projVars X (headSet j)) := by
      funext ω
      have hmem : l ∈ headSet j := by simp [headSet, Finset.mem_filter, hl]
      simp only [Function.comp_apply, projVars, hmem, if_true]
    calc MeasurableSpace.comap (X l) inferInstance
        = MeasurableSpace.comap (projVars X (headSet j))
            (MeasurableSpace.comap (fun w : Π i : Fin n, β i => w l) inferInstance) := by
          rw [hxl, ← MeasurableSpace.comap_comp]
      _ ≤ MeasurableSpace.comap (projVars X (headSet j)) inferInstance :=
          MeasurableSpace.comap_mono (le_iSup (fun a => MeasurableSpace.comap
            (fun w : Π i : Fin n, β i => w a) inferInstance) l)

/-- The prefix block `projVars X S` and its complement `projVars X Sᶜ` are independent,
inherited from the mutual independence of the family `X`. -/
private lemma indepFun_projVars (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    {μ : Measure Ω} (hX_indep : iIndepFun X μ) (S : Finset (Fin n)) :
    IndepFun (projVars X S) (projVars X Sᶜ) μ := by
  classical
  -- Fill a `T`-indexed tuple back into the full product (others arbitrary).
  let fill : ∀ (T : Finset (Fin n)), (Π i : T, β i) → (Π i : Fin n, β i) :=
    fun _ t i => if h : i ∈ _ then t ⟨i, h⟩ else Classical.arbitrary (β i)
  have hfill : ∀ T, Measurable (fill T) := by
    intro T
    refine measurable_pi_lambda _ (fun i => ?_)
    by_cases h : i ∈ T
    · simp only [fill, h, dif_pos]; exact measurable_pi_apply _
    · simp only [fill, h, dif_neg, not_false_iff]; exact measurable_const
  have hcomp : ∀ T, projVars X T = (fill T) ∘ (fun a (i : T) => X i a) := by
    intro T; funext ω i
    by_cases h : i ∈ T
    · simp only [projVars, h, if_true, Function.comp, fill, dif_pos]
    · simp only [projVars, h, if_false, Function.comp, fill, dif_neg, not_false_iff]
  rw [hcomp S, hcomp Sᶜ]
  exact (hX_indep.indepFun_finset S Sᶜ disjoint_compl_right hX).comp (hfill S) (hfill Sᶜ)

/-- The "future-averaged conditional mean": for a prefix value `w` (the `S`-block), integrate `f`
over the `Sᶜ`-block against its marginal law. This is the function `g` in McDiarmid's argument:
`Mⱼ = condMean … (Fⱼ-block of X)`. -/
private noncomputable def condMean (X : ∀ i : Fin n, Ω → β i) (f : (Π i : Fin n, β i) → ℝ)
    (μ : Measure Ω) (S : Finset (Fin n)) (w : Π i : Fin n, β i) : ℝ :=
  ∫ v, f (combineAt S w v) ∂(μ.map (projVars X Sᶜ))

/-- **Helper (factorization).** Under independence, the Doob martingale `Mⱼ = E[f(X) | Fⱼ]` equals
`condMean` evaluated at the `Fⱼ`-block of `X`. Proof: `condExp_prod_ae_eq_integral_condDistrib`
turns the conditional expectation into an integral against `condDistrib`, then `STEP 1`
(`condDistrib_eq_const_of_indepFun`) replaces that kernel by the `Sᶜ`-block marginal. -/
private lemma increment_factorization
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (hf_int : Integrable (f ∘ allVars X) μ)
    (hX_indep : iIndepFun X μ) (j : ℕ) :
    doobMartingale X hX f μ j =ᵐ[μ] condMean X f μ (headSet j) ∘ projVars X (headSet j) := by
  set S := headSet j with hS
  set W := projVars X S with hW_def
  set V := projVars X Sᶜ with hV_def
  set F : (Π i : Fin n, β i) × (Π i : Fin n, β i) → ℝ :=
    fun p => f (combineAt S p.1 p.2) with hF_def
  have hW : Measurable W := measurable_projVars X hX S
  have hV : Measurable V := measurable_projVars X hX Sᶜ
  have hF : StronglyMeasurable F := (hf.comp (measurable_combineAt S)).stronglyMeasurable
  have hFWV : (fun ω => F (W ω, V ω)) = f ∘ allVars X := by
    funext ω; simp only [hF_def, Function.comp_apply, hW_def, hV_def, combineAt_projVars]
  have hFint : Integrable (fun ω => F (W ω, V ω)) μ := by rw [hFWV]; exact hf_int
  have hce := condExp_prod_ae_eq_integral_condDistrib (μ := μ) hW hV.aemeasurable hF hFint
  have hfilt : (natFiltration X hX) j = MeasurableSpace.comap W inferInstance :=
    (comap_projVars_headSet X hX j).symm
  have hindep : IndepFun W V μ := indepFun_projVars X hX hX_indep S
  have hcd := condDistrib_eq_const_of_indepFun hW hV hindep
  have hpull : (fun ω => ∫ v, F (W ω, v) ∂(condDistrib V W μ (W ω)))
      =ᵐ[μ] (fun ω => ∫ v, F (W ω, v) ∂(μ.map V)) := by
    have hΦΨ : (fun a => ∫ v, F (a, v) ∂(condDistrib V W μ a))
        =ᵐ[μ.map W] (fun a => ∫ v, F (a, v) ∂(μ.map V)) := by
      filter_upwards [hcd] with a ha
      rw [ha, Kernel.const_apply]
    exact ae_eq_comp hW.aemeasurable hΦΨ
  have hdoob : doobMartingale X hX f μ j
      = μ[fun a => F (W a, V a) | MeasurableSpace.comap W inferInstance] := by
    simp only [doobMartingale]; rw [hfilt, ← hFWV]
  have hlast : (fun ω => ∫ v, F (W ω, v) ∂(μ.map V)) = condMean X f μ S ∘ projVars X S := by
    funext ω; simp only [condMean, Function.comp_apply, hF_def, hV_def, hW_def]
  calc doobMartingale X hX f μ j
      =ᵐ[μ] (fun ω => ∫ v, F (W ω, v) ∂(condDistrib V W μ (W ω))) := by rw [hdoob]; exact hce
    _ =ᵐ[μ] (fun ω => ∫ v, F (W ω, v) ∂(μ.map V)) := hpull
    _ = condMean X f μ S ∘ projVars X S := hlast

private lemma measurable_combineAt_right (S : Finset (Fin n)) (w : Π i : Fin n, β i) :
    Measurable (fun v : Π i : Fin n, β i => combineAt S w v) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  by_cases h : i ∈ S
  · simp only [combineAt, h, if_true]; exact measurable_const
  · simp only [combineAt, h, if_false]; exact measurable_pi_apply i

/-- Updating coordinate `i₀ ∈ S` in the `S`-block commutes with recombining. -/
private lemma combineAt_update (S : Finset (Fin n)) {i0 : Fin n} (hi0 : i0 ∈ S)
    (w v : Π i : Fin n, β i) (y : β i0) :
    combineAt S (Function.update w i0 y) v = Function.update (combineAt S w v) i0 y := by
  funext i
  by_cases hik : i = i0
  · subst hik; simp only [combineAt, hi0, if_true, Function.update_self]
  · rw [Function.update_of_ne hik]
    by_cases h : i ∈ S
    · simp only [combineAt, h, if_true, Function.update_of_ne hik]
    · simp only [combineAt, h, if_false]

/-- **Helper (oscillation).** `condMean` has oscillation `≤ b` in any single coordinate `i₀ ∈ S`,
where `b` bounds the corresponding bounded difference of `f`. (If the integrals diverge, both
`condMean` values are `0`, so the bound holds trivially.) -/
private lemma condMean_update_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    {i0 : Fin n} {b : ℝ}
    (hb : ∀ x : Π i : Fin n, β i, ∀ z : β i0, |f x - f (Function.update x i0 z)| ≤ b)
    (S : Finset (Fin n)) (hi0 : i0 ∈ S) (w : Π i : Fin n, β i) (y : β i0) :
    |condMean X f μ S w - condMean X f μ S (Function.update w i0 y)| ≤ b := by
  classical
  haveI : IsProbabilityMeasure (μ.map (projVars X Sᶜ)) :=
    Measure.isProbabilityMeasure_map (measurable_projVars X hX Sᶜ).aemeasurable
  have ha_meas : Measurable (fun v => f (combineAt S w v)) :=
    hf.comp (measurable_combineAt_right S w)
  have hb_meas : Measurable (fun v => f (Function.update (combineAt S w v) i0 y)) := by
    refine hf.comp (measurable_pi_lambda _ (fun i => ?_))
    by_cases hik : i = i0
    · subst hik; simp only [Function.update_self]; exact measurable_const
    · simp only [Function.update_of_ne hik]; exact (measurable_combineAt_right S w).eval
  have hgbound : ∀ v, |f (combineAt S w v) - f (Function.update (combineAt S w v) i0 y)| ≤ b :=
    fun v => hb (combineAt S w v) y
  have hg_int : Integrable (fun v => f (combineAt S w v)
      - f (Function.update (combineAt S w v) i0 y)) (μ.map (projVars X Sᶜ)) :=
    Integrable.mono' (integrable_const b)
      (ha_meas.aestronglyMeasurable.sub hb_meas.aestronglyMeasurable)
      (ae_of_all _ (fun v => by rw [Real.norm_eq_abs]; exact hgbound v))
  have hrw : condMean X f μ S (Function.update w i0 y)
      = ∫ v, f (Function.update (combineAt S w v) i0 y) ∂(μ.map (projVars X Sᶜ)) := by
    unfold condMean
    refine integral_congr_ae (ae_of_all _ (fun v => ?_))
    change f (combineAt S (Function.update w i0 y) v) = f (Function.update (combineAt S w v) i0 y)
    rw [combineAt_update S hi0 w v y]
  rw [hrw, show condMean X f μ S w
      = ∫ v, f (combineAt S w v) ∂(μ.map (projVars X Sᶜ)) from rfl]
  by_cases hint : Integrable (fun v => f (combineAt S w v)) (μ.map (projVars X Sᶜ))
  · have hbb_int : Integrable (fun v => f (Function.update (combineAt S w v) i0 y))
        (μ.map (projVars X Sᶜ)) := by
      refine (hint.sub hg_int).congr (ae_of_all _ (fun v => ?_))
      simp only [Pi.sub_apply]; ring
    rw [← integral_sub hint hbb_int]
    refine abs_integral_le_integral_abs.trans ?_
    calc ∫ v, |f (combineAt S w v) - f (Function.update (combineAt S w v) i0 y)|
            ∂(μ.map (projVars X Sᶜ))
        ≤ ∫ _, b ∂(μ.map (projVars X Sᶜ)) :=
          integral_mono hg_int.abs (integrable_const b) hgbound
      _ = b := by simp
  · have hbb_nint : ¬ Integrable (fun v => f (Function.update (combineAt S w v) i0 y))
        (μ.map (projVars X Sᶜ)) := fun hbb => hint (by
          refine (hbb.add hg_int).congr (ae_of_all _ (fun v => ?_))
          simp only [Pi.add_apply]; ring)
    rw [integral_undef hint, integral_undef hbb_nint, sub_zero, abs_zero]
    exact (abs_nonneg _).trans (hb (Classical.arbitrary _) (Classical.arbitrary _))

/-- **Helper (tower).** On the trim measure, `Mₖ` is the `condExpKernel`-fiber average of
`Mₖ₊₁`, via the tower property `Mₖ = E[Mₖ₊₁ | Fₖ]`. -/
private lemma doobMartingale_eq_integral_condExpKernel
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (k : ℕ) :
    doobMartingale X hX f μ k =ᵐ[μ.trim ((natFiltration X hX).le k)]
      fun ω' => ∫ ω, doobMartingale X hX f μ (k + 1) ω
        ∂(condExpKernel μ ((natFiltration X hX) k) ω') := by
  have hm := (natFiltration X hX).le k
  have htower : doobMartingale X hX f μ k =ᵐ[μ]
      μ[doobMartingale X hX f μ (k + 1) | (natFiltration X hX) k] := by
    simp only [doobMartingale]
    exact (Filtration.condExp_condExp (f ∘ allVars X) (natFiltration X hX) (Nat.le_succ k)).symm
  have htower_trim : doobMartingale X hX f μ k =ᵐ[μ.trim hm]
      μ[doobMartingale X hX f μ (k + 1) | (natFiltration X hX) k] := by
    refine StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm ?_
      stronglyMeasurable_condExp htower
    simp only [doobMartingale]; exact stronglyMeasurable_condExp
  exact htower_trim.trans (condExp_ae_eq_trim_integral_condExpKernel hm integrable_condExp)

/-! ### §4 Conditional sub-Gaussianity of each increment -/

/-- Under `iIndepFun X μ` and the bounded-differences condition, the Doob increment
    `Δₖ₊₁ = Mₖ₊₁ − Mₖ` is globally a.e. bounded in `[−cₖ, cₖ]` and fiber-wise a.e. bounded in an
    interval of length exactly `cₖ`.

    Proof: by `increment_factorization`, `Mₖ₊₁ = condMean (Fₖ₊₁-block)`; on a `Fₖ`-fiber the past
    coordinates are frozen (`condExpKernel_ae_eq_const_of_measurable`), so `Mₖ₊₁` reduces to a
    function `φ` of `Xₖ` whose oscillation is `≤ cₖ` (`condMean_update_le`). Subtracting the
    fiber-constant `Mₖ` lands `Δₖ₊₁` in `[inf φ − Mₖ, inf φ − Mₖ + cₖ]`; since `Mₖ` is the fiber
    average of `Mₖ₊₁` (`doobMartingale_eq_integral_condExpKernel`) it lies in `[inf φ, inf φ + cₖ]`,
    so the lower endpoint is in `[−cₖ, 0]`, yielding the global bound by transfer back to `μ`. -/
private lemma increment_bounded_of_bounded_differences
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (hf_int : Integrable (f ∘ allVars X) μ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences Dᵢf ≤ cᵢ; Lu-BDA §5.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §5.1.
    (hX_indep : iIndepFun X μ)
    (k : ℕ) (hk : k < n) :
    -- Global a.e. bound (used for integrable_exp_mul).
    (∀ᵐ ω ∂μ, doobIncrement X hX f μ (k + 1) ω ∈ Set.Icc (-(c ⟨k, hk⟩)) (c ⟨k, hk⟩)) ∧
    -- Fiber-wise bound of length cₖ (used for the tight MGF constant).
    (∀ᵐ ω' ∂(μ.trim ((natFiltration X hX).le k)),
      ∃ a : ℝ, ∀ᵐ ω ∂(condExpKernel μ ((natFiltration X hX) k) ω'),
        doobIncrement X hX f μ (k + 1) ω ∈ Set.Icc a (a + c ⟨k, hk⟩)) := by
  classical
  set i0 : Fin n := ⟨k, hk⟩ with hi0_def
  set S : Finset (Fin n) := headSet (k + 1) with hS_def
  set Sp : Finset (Fin n) := headSet k with hSp_def
  have hi0val : (i0 : ℕ) = k := rfl
  have hi0S : i0 ∈ S := by
    rw [hS_def]
    simp only [headSet, Finset.mem_filter, Finset.mem_univ, true_and, hi0val]; omega
  -- Factorization of Mₖ₊₁ as `condMean` of the prefix block.
  have hfact : doobMartingale X hX f μ (k + 1) =ᵐ[μ]
      fun ω => condMean X f μ S (projVars X S ω) := by
    have h := increment_factorization X hX f hf hf_int hX_indep (k + 1)
    rw [← hS_def] at h; exact h
  -- Pointwise: the (≤k)-block equals the (<k)-block with coordinate `i0` reset to `Xₖ`.
  have hWW' : ∀ ω, projVars X S ω = Function.update (projVars X Sp ω) i0 (X i0 ω) := by
    intro ω; funext i
    by_cases hii0 : i = i0
    · subst hii0; simp only [projVars, Function.update_self, if_pos hi0S]
    · rw [Function.update_of_ne hii0]
      have hval : (i : ℕ) ≠ k := fun h => hii0 (by rw [hi0_def]; exact Fin.ext h)
      by_cases hiS : i ∈ S
      · have hiSp : i ∈ Sp := by
          simp only [hS_def, headSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiS
          simp only [hSp_def, headSet, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        simp only [projVars, if_pos hiS, if_pos hiSp]
      · have hiSp : i ∉ Sp := by
          simp only [hS_def, headSet, Finset.mem_filter, Finset.mem_univ, true_and] at hiS
          simp only [hSp_def, headSet, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        simp only [projVars, if_neg hiS, if_neg hiSp]
  -- The (<k)-block is `Fₖ`-measurable.
  have hW'meas : Measurable[(natFiltration X hX) k] (projVars X Sp) := by
    rw [measurable_iff_comap_le, hSp_def]; exact le_of_eq (comap_projVars_headSet X hX k)
  -- `MeasurableEq` on the (standard-Borel) product space, for the fiber-constancy of the past.
  haveI hMEq : MeasurableEq (Π i : Fin n, β i) := by
    letI := upgradeStandardBorel (Π i : Fin n, β i); infer_instance
  have hconst_W' := condExpKernel_ae_eq_const_of_measurable (μ := μ)
    ((natFiltration X hX).le k) hW'meas
  have hM0meas : Measurable[(natFiltration X hX) k] (doobMartingale X hX f μ k) := by
    simp only [doobMartingale]; exact stronglyMeasurable_condExp.measurable
  have hconst_M0 := condExpKernel_ae_eq_const_of_measurable (μ := μ)
    ((natFiltration X hX).le k) hM0meas
  have hfact_fiber : ∀ᵐ ω' ∂(μ.trim ((natFiltration X hX).le k)),
      ∀ᵐ ω ∂(condExpKernel μ ((natFiltration X hX) k) ω'),
        doobMartingale X hX f μ (k + 1) ω = condMean X f μ S (projVars X S ω) :=
    Measure.ae_ae_of_ae_comp
      (by rw [condExpKernel_comp_trim ((natFiltration X hX).le k)]; exact hfact)
  have hM0_int := doobMartingale_eq_integral_condExpKernel (μ := μ) X hX f k
  have hM1_int_fiber : ∀ᵐ ω' ∂(μ.trim ((natFiltration X hX).le k)),
      Integrable (doobMartingale X hX f μ (k + 1))
        (condExpKernel μ ((natFiltration X hX) k) ω') := by
    have h1 : Integrable (doobMartingale X hX f μ (k + 1))
        (condExpKernel μ ((natFiltration X hX) k) ∘ₘ μ.trim ((natFiltration X hX).le k)) := by
      rw [condExpKernel_comp_trim ((natFiltration X hX).le k)]; exact integrable_condExp
    exact Measure.ae_integrable_of_integrable_comp h1
  -- Core per-fiber claim: a length-`cₖ` interval `[a, a+cₖ]` with `a ∈ [−cₖ, 0]`.
  have hcore : ∀ᵐ ω' ∂(μ.trim ((natFiltration X hX).le k)), ∃ a : ℝ,
      a ∈ Set.Icc (-(c i0)) 0 ∧ ∀ᵐ ω ∂(condExpKernel μ ((natFiltration X hX) k) ω'),
        doobIncrement X hX f μ (k + 1) ω ∈ Set.Icc a (a + c i0) := by
    filter_upwards [hconst_W', hconst_M0, hfact_fiber, hM0_int, hM1_int_fiber]
      with ω' hcW' hcM0 hfacω' hM0eq hM1int
    set φ : β i0 → ℝ := fun y => condMean X f μ S (Function.update (projVars X Sp ω') i0 y)
      with hφ_def
    have hosc : ∀ y y' : β i0, |φ y - φ y'| ≤ c i0 := by
      intro y y'
      simp only [hφ_def]
      have h := condMean_update_le (μ := μ) X hX f hf (fun x z => hbd i0 x z) S hi0S
        (Function.update (projVars X Sp ω') i0 y) y'
      rwa [Function.update_idem] at h
    have hbdd : BddBelow (Set.range φ) :=
      ⟨φ (Classical.arbitrary (β i0)) - c i0, by
        rintro z ⟨y, rfl⟩
        have h := abs_le.mp (hosc (Classical.arbitrary (β i0)) y); linarith [h.2]⟩
    have hsinf_le : ∀ y, sInf (Set.range φ) ≤ φ y := fun y => csInf_le hbdd ⟨y, rfl⟩
    have hle_sinf : ∀ y, φ y ≤ sInf (Set.range φ) + c i0 := by
      intro y
      have hlb : φ y - c i0 ≤ sInf (Set.range φ) :=
        le_csInf (Set.range_nonempty φ) (by
          rintro z ⟨y', rfl⟩
          have h := abs_le.mp (hosc y y'); linarith [h.2])
      linarith
    -- On the fiber, `Mₖ₊₁ = φ(Xₖ)`.
    have hM1φ : ∀ᵐ ω ∂(condExpKernel μ ((natFiltration X hX) k) ω'),
        doobMartingale X hX f μ (k + 1) ω = φ (X i0 ω) := by
      filter_upwards [hfacω', hcW'] with ω hfa hcw
      rw [hfa, hWW' ω, hcw]
    -- `Mₖ(ω')` is the fiber average of `Mₖ₊₁`, hence in `[inf φ, inf φ + cₖ]`.
    have hM0_mem : doobMartingale X hX f μ k ω' ∈
        Set.Icc (sInf (Set.range φ)) (sInf (Set.range φ) + c i0) := by
      rw [hM0eq]
      have hbound_fiber : ∀ᵐ ω ∂(condExpKernel μ ((natFiltration X hX) k) ω'),
          sInf (Set.range φ) ≤ doobMartingale X hX f μ (k + 1) ω ∧
          doobMartingale X hX f μ (k + 1) ω ≤ sInf (Set.range φ) + c i0 := by
        filter_upwards [hM1φ] with ω hM1; rw [hM1]; exact ⟨hsinf_le _, hle_sinf _⟩
      refine ⟨?_, ?_⟩
      · calc sInf (Set.range φ)
            = ∫ _, sInf (Set.range φ) ∂(condExpKernel μ ((natFiltration X hX) k) ω') := by simp
          _ ≤ _ := integral_mono_ae (integrable_const _) hM1int
              (hbound_fiber.mono (fun ω h => h.1))
      · calc ∫ ω, doobMartingale X hX f μ (k + 1) ω ∂(condExpKernel μ ((natFiltration X hX) k) ω')
            ≤ ∫ _, sInf (Set.range φ) + c i0 ∂(condExpKernel μ ((natFiltration X hX) k) ω') :=
              integral_mono_ae hM1int (integrable_const _) (hbound_fiber.mono (fun ω h => h.2))
          _ = sInf (Set.range φ) + c i0 := by simp
    refine ⟨sInf (Set.range φ) - doobMartingale X hX f μ k ω', ?_, ?_⟩
    · rw [Set.mem_Icc]; exact ⟨by linarith [hM0_mem.2], by linarith [hM0_mem.1]⟩
    · filter_upwards [hM1φ, hcM0] with ω hM1 hcm0
      have hΔval : doobIncrement X hX f μ (k + 1) ω
          = φ (X i0 ω) - doobMartingale X hX f μ k ω' := by
        simp only [doobIncrement, Pi.sub_apply]; rw [hM1, hcm0]
      rw [hΔval, Set.mem_Icc]
      exact ⟨by linarith [hsinf_le (X i0 ω)], by linarith [hle_sinf (X i0 ω)]⟩
  refine ⟨?_, ?_⟩
  · -- Global bound: transfer the fiber inclusion `[a,a+cₖ] ⊆ [−cₖ,cₖ]` back to `μ`.
    have hglobal_fiber : ∀ᵐ ω' ∂(μ.trim ((natFiltration X hX).le k)),
        ∀ᵐ ω ∂(condExpKernel μ ((natFiltration X hX) k) ω'),
          doobIncrement X hX f μ (k + 1) ω ∈ Set.Icc (-(c i0)) (c i0) := by
      filter_upwards [hcore] with ω' h
      obtain ⟨a, ha_mem, ha_bd⟩ := h
      rw [Set.mem_Icc] at ha_mem
      filter_upwards [ha_bd] with ω hω
      rw [Set.mem_Icc] at hω ⊢
      exact ⟨le_trans ha_mem.1 hω.1, le_trans hω.2 (by linarith [ha_mem.2])⟩
    have hΔmeas : Measurable (doobIncrement X hX f μ (k + 1)) := by
      have h1 : Measurable (doobMartingale X hX f μ (k + 1)) := by
        simp only [doobMartingale]
        exact (stronglyMeasurable_condExp.mono ((natFiltration X hX).le (k + 1))).measurable
      have h2 : Measurable (doobMartingale X hX f μ k) := by
        simp only [doobMartingale]
        exact (stronglyMeasurable_condExp.mono ((natFiltration X hX).le k)).measurable
      simp only [doobIncrement]; exact h1.sub h2
    have hres := Measure.ae_comp_of_ae_ae (hΔmeas measurableSet_Icc) hglobal_fiber
    rwa [condExpKernel_comp_trim ((natFiltration X hX).le k)] at hres
  · -- Fiber bound: drop the `a ∈ [−cₖ,0]` witness.
    filter_upwards [hcore] with ω' h
    obtain ⟨a, _, ha_bd⟩ := h
    exact ⟨a, ha_bd⟩

/-- Each Doob increment `Δₖ₊₁ = Mₖ₊₁ − Mₖ` satisfies `HasCondSubgaussianMGF` w.r.t. `Fₖ`
    with parameter `(‖cₖ‖₊/2)²`.

    **Proof:** The tower property `E[Mₖ₊₁|Fₖ] = Mₖ` gives zero conditional mean.
    The bounded-differences bound gives the fiber-wise range. Apply
    `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` fiber-by-fiber. -/
lemma increment_hasCondSubgaussianMGF
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (hf_int : Integrable (f ∘ allVars X) μ)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences; Lu-BDA §5.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §5.1.
    (hX_indep : iIndepFun X μ)
    (k : ℕ) (hk : k < n) :
    HasCondSubgaussianMGF ((natFiltration X hX) k) ((natFiltration X hX).le k)
      (doobIncrement X hX f μ (k + 1)) ((‖c ⟨k, hk⟩‖₊ / 2) ^ 2) μ := by
  -- hm_k is a proof term, not a MeasurableSpace instance; safe to use `have`.
  have hm_k : (natFiltration X hX) k ≤ mΩ := (natFiltration X hX).le k
  -- Δ : Ω → ℝ, not a typeclass — `let` is fine.
  let Δ := doobIncrement X hX f μ (k + 1)
  -- Integrability: Δ = Mₖ₊₁ − Mₖ, both integrable as conditional expectations.
  have h_int_k1 : Integrable (doobMartingale X hX f μ (k + 1)) μ := integrable_condExp
  have h_int_k : Integrable (doobMartingale X hX f μ k) μ := integrable_condExp
  have hΔ_int : Integrable Δ μ := h_int_k1.sub h_int_k
  have hΔ_aem : AEMeasurable Δ μ := hΔ_int.1.aemeasurable
  -- Tower: μ[Δ | Fₖ] = 0 a.e.
  -- condExp_sub gives μ[Mₖ₊₁ − Mₖ | Fₖ] = μ[Mₖ₊₁|Fₖ] − μ[Mₖ|Fₖ].
  have h_sub : μ[Δ | (natFiltration X hX) k] =ᵐ[μ]
      μ[doobMartingale X hX f μ (k + 1) | (natFiltration X hX) k] -
      μ[doobMartingale X hX f μ k | (natFiltration X hX) k] :=
    condExp_sub h_int_k1 h_int_k ((natFiltration X hX) k)
  -- Tower: μ[Mₖ₊₁ | Fₖ] = μ[μ[f∘X|Fₖ₊₁] | Fₖ] = μ[f∘X|Fₖ] = Mₖ.
  have htower :
      μ[doobMartingale X hX f μ (k + 1) | (natFiltration X hX) k] =ᵐ[μ]
      doobMartingale X hX f μ k :=
    Filtration.condExp_condExp (f ∘ allVars X) (natFiltration X hX) (Nat.le_succ k)
  -- Mₖ is Fₖ-measurable, so μ[Mₖ | Fₖ] = Mₖ (plain eq, lifted to ae).
  have hMk :
      μ[doobMartingale X hX f μ k | (natFiltration X hX) k] =ᵐ[μ]
      doobMartingale X hX f μ k :=
    ae_of_all μ (congr_fun
      (condExp_of_stronglyMeasurable hm_k stronglyMeasurable_condExp h_int_k))
  have h_condExp_zero : μ[Δ | (natFiltration X hX) k] =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [h_sub, htower, hMk] with ω h1 h2 h3
    simp only [Pi.sub_apply, Pi.zero_apply] at *
    linarith
  -- Disintegration: condExp via kernel integral.
  have hμ_eq :
      condExpKernel μ ((natFiltration X hX) k) ∘ₘ μ.trim hm_k = μ :=
    condExpKernel_comp_trim hm_k
  have h_condExp_zero_trim :
      μ[Δ | (natFiltration X hX) k] =ᵐ[μ.trim hm_k] (0 : Ω → ℝ) :=
    stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable hm_k
      stronglyMeasurable_zero h_condExp_zero
  have h_disint :
      μ[Δ | (natFiltration X hX) k] =ᵐ[μ.trim hm_k]
      fun ω' => ∫ y, Δ y ∂(condExpKernel μ ((natFiltration X hX) k) ω') :=
    condExp_ae_eq_trim_integral_condExpKernel hm_k hΔ_int
  -- Per-fiber zero mean.
  have h_fiber_zero : ∀ᵐ ω' ∂(μ.trim hm_k),
      ∫ y, Δ y ∂(condExpKernel μ ((natFiltration X hX) k) ω') = 0 := by
    filter_upwards [h_disint.symm.trans h_condExp_zero_trim] with ω' h
    simpa using h
  -- Per-fiber AEMeasurable.
  have h_fiber_aem : ∀ᵐ ω' ∂(μ.trim hm_k),
      AEMeasurable Δ (condExpKernel μ ((natFiltration X hX) k) ω') := by
    have h1 : Integrable Δ (condExpKernel μ ((natFiltration X hX) k) ∘ₘ μ.trim hm_k) := by
      rw [hμ_eq]; exact hΔ_int
    filter_upwards [Measure.ae_integrable_of_integrable_comp h1] with ω' hI
    exact hI.aestronglyMeasurable.aemeasurable
  -- Bounded differences → global bound + fiber-wise bound.
  obtain ⟨h_global, h_fiber_bound⟩ :=
    increment_bounded_of_bounded_differences X hX f hf hf_int c hc hbd hX_indep k hk
  -- Build HasCondSubgaussianMGF = Kernel.HasSubgaussianMGF.
  refine ⟨?_, ?_⟩
  · -- integrable_exp_mul: use global bound [−cₖ, cₖ].
    intro t
    rw [hμ_eq]
    exact integrable_exp_mul_of_mem_Icc hΔ_aem h_global
  · -- mgf_le: fiber-by-fiber, tight interval [a, a + cₖ].
    filter_upwards [h_fiber_bound, h_fiber_zero, h_fiber_aem] with ω' h_bd_ex h_mean h_aem
    obtain ⟨a, h_bd⟩ := h_bd_ex
    intro t
    -- Apply Hoeffding fiber-by-fiber; interval length exactly cₖ.
    have h_subg : HasSubgaussianMGF Δ ((‖c ⟨k, hk⟩‖₊ / 2) ^ 2)
        (condExpKernel μ ((natFiltration X hX) k) ω') := by
      have h' := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero h_aem h_bd h_mean
      rwa [show ‖(a + c ⟨k, hk⟩) - a‖₊ = ‖c ⟨k, hk⟩‖₊ from by congr 1; ring] at h'
    exact h_subg.mgf_le t

/-! ### §5 Main theorem: McDiarmid MGF bound -/

/-- **Doob-martingale MGF bound for McDiarmid** (Lu-BDA §5.1, Theorem 5.1 (McDiarmid
Inequality)).

Reference: Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0).

For `n` independent random variables `X = (X₀,...,Xₙ₋₁)` and a function `f` satisfying the
bounded-differences condition with constants `c : Fin n → ℝ`, the centered evaluation
`f(X) − E[f(X)]` is sub-Gaussian with parameter `∑ₖ (‖cₖ‖₊/2)²`:

  `HasSubgaussianMGF (f(X) − E[f(X)]) (∑ₖ (‖cₖ‖₊/2)²) μ`

MGF bound: `∀ λ, E[exp(λ(f(X) − E[f(X)]))] ≤ exp((∑ₖ cₖ²/4) · λ²/2) = exp(λ² ∑ₖ cₖ²/8)`.

The proof uses Mathlib's `HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF` (Azuma tower
theorem), feeding `increment_hasCondSubgaussianMGF` for each step. -/
theorem mgf_sub_expectation_le
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences; Lu-BDA §5.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §5.1.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: f(X) integrable; Lu-BDA §5.1 (implicit regularity).
    (hf_int : Integrable (f ∘ allVars X) μ) :
    HasSubgaussianMGF (fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)
      (∑ k : Fin n, (‖c k‖₊ / 2) ^ 2) μ := by
  -- Step 1: Apply Azuma tower theorem to doobIncrement / doobCY.
  -- Provide `cY := doobCY c` explicitly; Lean cannot infer it from a per-point constraint.
  have h_sum : HasSubgaussianMGF
      (fun ω => ∑ i ∈ Finset.range (n + 1), doobIncrement X hX f μ i ω)
      (∑ i ∈ Finset.range (n + 1), doobCY c i) μ := by
    apply HasSubgaussianMGF.sum_of_hasCondSubgaussianMGF (cY := doobCY c)
      (doobIncrement_stronglyAdapted X hX f μ) HasSubgaussianMGF.zero (n + 1)
    intro i hi
    rw [doobCY_succ c i (by omega)]
    exact increment_hasCondSubgaussianMGF X hX f hf hf_int c hc hbd hX_indep i (by omega)
  -- Step 2: Simplify the parameter sum.
  rw [sum_doobCY_eq] at h_sum
  -- Step 3: Identify ∑ doobIncrement = f(X) − E[f(X)] pointwise.
  have h_eq : (fun ω => ∑ i ∈ Finset.range (n + 1), doobIncrement X hX f μ i ω) =
      fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ := by
    funext ω
    -- Telescope: ∑ Δᵢ = M_n − M_0.
    rw [sum_doobIncrement_telescope X hX f μ n ω]
    -- M_n = f ∘ allVars X (a.e., here pointwise via condExp_of_stronglyMeasurable).
    have hn := congr_fun (doobMartingale_n_eq_f X hX f hf hf_int) ω
    -- M_0 = fun _ => E[f(X)].
    have h0 := congr_fun (doobMartingale_zero_eq_mean (μ := μ) X hX f) ω
    simp only [Function.comp] at hn
    simp only [h0, hn]
  rwa [h_eq] at h_sum

end DoobDecomposition

end StatLean.ConcentrationInequalities
