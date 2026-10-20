module
public import StatLean.Bayesian.DirichletLaplace.Defs
public import StatLean.Bayesian.ForMathlib.PiLintegralFintype
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# Coordinate splitting and tensorization of the DL posterior ratio (C11)

**This is the riskiest file of the milestone** — it carries the whole `WithLp.toLp` / subtype-pi /
product-measure transport stack, plus the `ℝ≥0∞`-cancellation that turns the full-model posterior
ratio into the sub-model posterior ratio (BPPD eq. (26), tensorization).

For a support set `S ⊆ ι` (with the true support `S₀` the intended instance), split every
coordinate object of the normal-means model along `S` and its complement `Sᶜ`:

* `projS S` / `extendS S` — the coordinate restriction `ℝ^ι → ℝ^{S}` and the zero-padding section
  `ℝ^{S} → ℝ^ι`;
* `norm_sq_split` — `‖θ‖² = ‖projS S θ‖² + ‖projS Sᶜ θ‖²` (Pythagoras over the coordinate partition);
* `dlPrior_map_projS` / `dlPrior_prod_apply` — the DL product prior marginalizes to the sub-prior and
  factorizes on product sets;
* `dlLR_split` — the Gaussian likelihood ratio factorizes, `dlLR θ₀ θ y = dlLR_S · dlLR_{Sᶜ}`;
* `dlNumer_cylinder` — on a cylinder over `S` the `S`-factor of the numerator peels off (the `Sᶜ`
  coordinates integrate to the sub-model denominator);
* `dlRatio_cylinder` — **tensorization (BPPD eq. (26))**: on a cylinder over `Sᶜ`, the full posterior
  ratio equals the `Sᶜ`-sub-model posterior ratio, the `S`-factor cancelling between numerator and
  denominator (which requires the `S`-factor to be finite and nonzero, `dlDenom_pos_lt_top`);
* `gaussShift_map_projS` — the data measure `N(θ, I)` marginalizes to `N(projS S θ, I)` on the
  sub-space.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). §6, eq. (26) (reduction of the posterior on `S₀ᶜ`-cylinders to the `S₀ᶜ`
sub-model, using the product structure of the prior and the likelihood).

**Proof formalization notes.** The subtype `{j // j ∈ S}` inherits `Fintype` from `[Fintype ι]` and
`[DecidablePred (· ∈ S)]`, so the sub-space `EuclideanSpace ℝ {j // j ∈ S}` and the sub-prior
`dlPrior a {j // j ∈ S}` are well-typed. The transport uses `WithLp.toLp` / `WithLp.ofLp` to move
between `EuclideanSpace ℝ ι` and the plain pi type, `measurePreserving_piEquivPiSubtypeProd` for the
`ℝ^ι ≃ ℝ^{S} × ℝ^{Sᶜ}` measure isomorphism, and `pi_map_restrict_subtype` / `lintegral_pi_split`
(from `ForMathlib.PiLintegralFintype`) for the marginal and the split-Tonelli. `dlLR_split` combines
`norm_sq_split` with the analogous inner-product split and `ENNReal.ofReal (exp a) * ENNReal.ofReal
(exp b) = ENNReal.ofReal (exp (a + b))`. In `dlRatio_cylinder` the `S`-factor
`dlDenom (projS S θ₀) (dlPrior a {j // j ∈ S}) (projS S y)` is in `(0, ∞)` (integrand bounded by
`exp(½‖·‖²)`, prior a probability measure), so it cancels in the `ℝ≥0∞` quotient. **Fallback** (per
plan): if the `ℝ≥0∞` cancellation is intractable, prove only the `≤` direction `PosteriorCompressibility` consumes,
or leave `dlRatio_cylinder` as the single named debt (its statement layer insulates the consumers).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Coordinate restriction to `S`** `ℝ^ι → ℝ^{S}` (BPPD §6, tensorization setup).

`projS S θ` keeps the coordinates of `θ` indexed by `S`, as an element of
`EuclideanSpace ℝ {j // j ∈ S}`. Edge behaviour: `S = ∅` gives a map into the zero space. -/
noncomputable def projS (S : Set ι) [DecidablePred (· ∈ S)] :
    EuclideanSpace ℝ ι → EuclideanSpace ℝ {j // j ∈ S} :=
  fun θ => WithLp.toLp 2 (fun i : {j // j ∈ S} => θ (i : ι))

/-- **Zero-padding extension** `ℝ^{S} → ℝ^ι` (BPPD §6, tensorization setup).

`extendS S u` places the coordinates of `u` at the indices in `S` and fills the complement with `0`;
it is a linear section of `projS S`. Edge behaviour: coordinates outside `S` are set to `0`. -/
noncomputable def extendS (S : Set ι) [DecidablePred (· ∈ S)] :
    EuclideanSpace ℝ {j // j ∈ S} → EuclideanSpace ℝ ι :=
  fun u => WithLp.toLp 2 (fun i : ι => if h : i ∈ S then u ⟨i, h⟩ else 0)

/-- `projS S` is measurable (coordinate restriction composed with the `WithLp` equivs). -/
private lemma measurable_projS (S : Set ι) [DecidablePred (· ∈ S)] :
    Measurable (projS (ι := ι) S) :=
  (WithLp.measurable_toLp _ _).comp
    (measurable_pi_lambda _ fun i => (measurable_pi_apply (i : ι)).comp (WithLp.measurable_ofLp 2 _))

/-- `projS S` respects subtraction (it is a linear coordinate restriction). -/
private lemma projS_sub (S : Set ι) [DecidablePred (· ∈ S)] (a b : EuclideanSpace ℝ ι) :
    projS S (a - b) = projS S a - projS S b := by
  unfold projS
  rw [← WithLp.toLp_sub]
  congr 1

/-- `projS S` respects addition (it is a linear coordinate restriction). -/
private lemma projS_add (S : Set ι) [DecidablePred (· ∈ S)] (a b : EuclideanSpace ℝ ι) :
    projS S (a + b) = projS S a + projS S b := by
  unfold projS
  rw [← WithLp.toLp_add]
  congr 1

/-- The `S`-coordinate of `projS S θ` is the corresponding coordinate of `θ`. -/
private lemma projS_ofLp (S : Set ι) [DecidablePred (· ∈ S)] (θ : EuclideanSpace ℝ ι)
    (i : {j // j ∈ S}) : (projS S θ).ofLp i = θ.ofLp i.val := rfl

/-- **Pythagoras over the coordinate partition**: `‖θ‖² = ‖projS S θ‖² + ‖projS Sᶜ θ‖²`. -/
lemma norm_sq_split (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ : EuclideanSpace ℝ ι) :
    ‖θ‖ ^ 2 = ‖projS S θ‖ ^ 2 + ‖projS Sᶜ θ‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq θ, EuclideanSpace.real_norm_sq_eq (projS S θ),
      EuclideanSpace.real_norm_sq_eq (projS Sᶜ θ)]
  simp_rw [projS_ofLp]
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ S)) (fun x => by simp)
        (fun j => θ.ofLp j ^ 2),
      ← Finset.sum_subtype (Finset.univ.filter (· ∈ Sᶜ)) (fun x => by simp)
        (fun j => θ.ofLp j ^ 2),
      show (Finset.univ.filter (· ∈ Sᶜ)) = (Finset.univ.filter (· ∈ S))ᶜ from by
        ext j; simp [Set.mem_compl_iff],
      Finset.sum_add_sum_compl]

/-- **The DL product prior marginalizes to the sub-prior**:
`(dlPrior a ι).map (projS S) = dlPrior a {j // j ∈ S}`. The product structure of the prior means
the `S`-coordinates are jointly `dlPrior a {j // j ∈ S}`, independent of the rest. -/
lemma dlPrior_map_projS (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] :
    (dlPrior a ι).map (projS S) = dlPrior a {j // j ∈ S} := by
  have hrestrict : Measurable (fun x : ι → ℝ => fun i : {j // j ∈ S} => x i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ι)
  rw [dlPrior, dlPrior, Measure.map_map (measurable_projS S) (WithLp.measurable_toLp _ _),
    show (projS S ∘ WithLp.toLp 2)
        = (WithLp.toLp 2) ∘ (fun x : ι → ℝ => fun i : {j // j ∈ S} => x i.val) from rfl,
    ← Measure.map_map (WithLp.measurable_toLp _ _) hrestrict,
    pi_map_restrict_subtype (fun _ : ι => dlMarginal a) (· ∈ S)]

/-- Reduce an lintegral against `dlPrior a κ` to an lintegral against the underlying product measure
(pulling back through the `WithLp.toLp` transport). -/
private lemma lintegral_dlPrior_eq_pi (a : ℝ) (κ : Type*) [Fintype κ]
    {F : EuclideanSpace ℝ κ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ξ, F ξ ∂(dlPrior a κ)
      = ∫⁻ x, F (WithLp.toLp 2 x) ∂(Measure.pi fun _ : κ => dlMarginal a) := by
  rw [dlPrior, lintegral_map hF (WithLp.measurable_toLp _ _)]

/-- Reindexing bridge: an lintegral over the negated-predicate subtype `{i // i ∉ S}` equals the
lintegral against `dlPrior a {j // j ∈ Sᶜ}` (the two subtypes carry different `Fintype` instances but
are definitionally the same type). -/
private lemma lintegral_pi_toLp_compl (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ Sᶜ)] {g : EuclideanSpace ℝ {j // j ∈ Sᶜ} → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x : {i // i ∉ S} → ℝ, g (WithLp.toLp 2 x) ∂(Measure.pi fun _ => dlMarginal a)
      = ∫⁻ ζ, g ζ ∂(dlPrior a {j // j ∈ Sᶜ}) := by
  have hgtoLp : Measurable (fun z : {j // j ∈ Sᶜ} → ℝ => g (WithLp.toLp 2 z)) :=
    hg.comp (WithLp.measurable_toLp _ _)
  rw [lintegral_dlPrior_eq_pi a {j // j ∈ Sᶜ} hg,
    ← (measurePreserving_piCongrLeft (fun _ : {j // j ∈ Sᶜ} => dlMarginal a)
        (Equiv.subtypeEquivRight fun i => (Set.mem_compl_iff S i).symm)).lintegral_comp hgtoLp]
  refine lintegral_congr fun x => ?_
  congr 1

/-- **Tensorization of `dlPrior`-integrals** (BPPD eq. (26), master lemma). An integrand that
factorizes as an `S`-function of `projS S θ` times an `Sᶜ`-function of `projS Sᶜ θ` integrates to the
product of the two sub-model integrals. -/
private lemma lintegral_dlPrior_split (a : ℝ) (S : Set ι)
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    {FS : EuclideanSpace ℝ {j // j ∈ S} → ℝ≥0∞}
    {FSc : EuclideanSpace ℝ {j // j ∈ Sᶜ} → ℝ≥0∞}
    (hFS : Measurable FS) (hFSc : Measurable FSc) :
    ∫⁻ θ, FS (projS S θ) * FSc (projS Sᶜ θ) ∂(dlPrior a ι)
      = (∫⁻ ξ, FS ξ ∂(dlPrior a {j // j ∈ S}))
        * (∫⁻ ζ, FSc ζ ∂(dlPrior a {j // j ∈ Sᶜ})) := by
  have hmul : Measurable (fun θ : EuclideanSpace ℝ ι => FS (projS S θ) * FSc (projS Sᶜ θ)) :=
    (hFS.comp (measurable_projS S)).mul (hFSc.comp (measurable_projS Sᶜ))
  have hmulpi : Measurable
      (fun x : ι → ℝ => FS (projS S (WithLp.toLp 2 x)) * FSc (projS Sᶜ (WithLp.toLp 2 x))) :=
    hmul.comp (WithLp.measurable_toLp _ _)
  rw [lintegral_dlPrior_eq_pi a ι (F := fun θ => FS (projS S θ) * FSc (projS Sᶜ θ)) hmul]
  simp only []
  rw [lintegral_pi_split (fun _ : ι => dlMarginal a) (· ∈ S)
      (f := fun x => FS (projS S (WithLp.toLp 2 x)) * FSc (projS Sᶜ (WithLp.toLp 2 x))) hmulpi]
  have hS : ∀ (xS : {j // j ∈ S} → ℝ) (xSc : {i // ¬ (i ∈ S)} → ℝ),
      projS S (WithLp.toLp 2
          ((Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ : ι => ℝ)).symm (xS, xSc)))
        = WithLp.toLp 2 xS := by
    intro xS xSc; unfold projS; congr 1; funext i
    change (Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ : ι => ℝ)).symm (xS, xSc) (i : ι) = xS i
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]; exact dif_pos i.property
  have hSc : ∀ (xS : {j // j ∈ S} → ℝ) (xSc : {i // ¬ (i ∈ S)} → ℝ),
      projS Sᶜ (WithLp.toLp 2
          ((Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ : ι => ℝ)).symm (xS, xSc)))
        = WithLp.toLp 2 xSc := by
    intro xS xSc; unfold projS; congr 1; funext i
    change (Equiv.piEquivPiSubtypeProd (· ∈ S) (fun _ : ι => ℝ)).symm (xS, xSc) (i : ι) = xSc i
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]; exact dif_neg i.property
  have hFStoLp : Measurable (fun x : {j // j ∈ S} → ℝ => FS (WithLp.toLp 2 x)) :=
    hFS.comp (WithLp.measurable_toLp _ _)
  have hFSctoLp : Measurable (fun x : {i // i ∉ S} → ℝ => FSc (WithLp.toLp 2 x)) :=
    hFSc.comp (WithLp.measurable_toLp _ _)
  simp only [hS, hSc]
  rw [lintegral_dlPrior_eq_pi a {j // j ∈ S} hFS, ← lintegral_pi_toLp_compl a S hFSc]
  exact lintegral_lintegral_mul hFStoLp.aemeasurable hFSctoLp.aemeasurable

/-- **Product-set factorization of the DL prior**: on a "box" `projS S ⁻¹' A ∩ projS Sᶜ ⁻¹' B`
(constrain the `S`-coordinates to `A` and the `Sᶜ`-coordinates to `B`),
`dlPrior a ι (·) = dlPrior a {j // j ∈ S} A · dlPrior a {j // j ∈ Sᶜ} B`. -/
lemma dlPrior_prod_apply (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    {A : Set (EuclideanSpace ℝ {j // j ∈ S})} {B : Set (EuclideanSpace ℝ {j // j ∈ Sᶜ})}
    -- LEAN-ONLY: `A` measurable (product-measure factorization regularity)
    (hA : MeasurableSet A)
    -- LEAN-ONLY: `B` measurable (product-measure factorization regularity)
    (hB : MeasurableSet B) :
    dlPrior a ι (projS S ⁻¹' A ∩ projS Sᶜ ⁻¹' B)
      = dlPrior a {j // j ∈ S} A * dlPrior a {j // j ∈ Sᶜ} B := by
  have hE : MeasurableSet (projS S ⁻¹' A ∩ projS Sᶜ ⁻¹' B) :=
    ((measurable_projS S) hA).inter ((measurable_projS Sᶜ) hB)
  have hpt : ∀ θ, (projS S ⁻¹' A ∩ projS Sᶜ ⁻¹' B).indicator (fun _ => (1 : ℝ≥0∞)) θ
      = A.indicator (fun _ => (1 : ℝ≥0∞)) (projS S θ)
        * B.indicator (fun _ => (1 : ℝ≥0∞)) (projS Sᶜ θ) := by
    intro θ
    simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage]
    by_cases hθA : projS S θ ∈ A <;> by_cases hθB : projS Sᶜ θ ∈ B <;> simp [hθA, hθB]
  have key : dlPrior a ι (projS S ⁻¹' A ∩ projS Sᶜ ⁻¹' B)
      = ∫⁻ θ, A.indicator (fun _ => (1 : ℝ≥0∞)) (projS S θ)
              * B.indicator (fun _ => (1 : ℝ≥0∞)) (projS Sᶜ θ) ∂(dlPrior a ι) := by
    rw [← setLIntegral_one, ← lintegral_indicator hE]
    exact lintegral_congr hpt
  rw [key,
    lintegral_dlPrior_split a S (measurable_const.indicator hA) (measurable_const.indicator hB),
    lintegral_indicator hA, setLIntegral_one, lintegral_indicator hB, setLIntegral_one]

/-- **Inner product splits over the coordinate partition**:
`⟪a, b⟫ = ⟪projS S a, projS S b⟫ + ⟪projS Sᶜ a, projS Sᶜ b⟫`. -/
private lemma inner_split (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (a b : EuclideanSpace ℝ ι) :
    (inner ℝ a b : ℝ) = inner ℝ (projS S a) (projS S b) + inner ℝ (projS Sᶜ a) (projS Sᶜ b) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply]
  simp_rw [projS_ofLp]
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ S)) (fun x => by simp)
        (fun j => (inner ℝ (a.ofLp j) (b.ofLp j) : ℝ)),
      ← Finset.sum_subtype (Finset.univ.filter (· ∈ Sᶜ)) (fun x => by simp)
        (fun j => (inner ℝ (a.ofLp j) (b.ofLp j) : ℝ)),
      show (Finset.univ.filter (· ∈ Sᶜ)) = (Finset.univ.filter (· ∈ S))ᶜ from by
        ext j; simp [Set.mem_compl_iff],
      Finset.sum_add_sum_compl]

/-- **The Gaussian likelihood ratio factorizes** over the coordinate partition:
`dlLR θ₀ θ y = dlLR (projS S θ₀) (projS S θ) (projS S y) · dlLR (projS Sᶜ θ₀) (projS Sᶜ θ)
(projS Sᶜ y)`. Both the inner product `⟪θ − θ₀, y − θ₀⟫` and the penalty `‖θ − θ₀‖²/2` split as a
sum over `S` and `Sᶜ`, and `exp` turns the sum into a product. -/
lemma dlLR_split (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ₀ θ y : EuclideanSpace ℝ ι) :
    dlLR θ₀ θ y
      = dlLR (projS S θ₀) (projS S θ) (projS S y)
        * dlLR (projS Sᶜ θ₀) (projS Sᶜ θ) (projS Sᶜ y) := by
  unfold dlLR
  have key : (inner ℝ (θ - θ₀) (y - θ₀) : ℝ) - ‖θ - θ₀‖ ^ 2 / 2
      = ((inner ℝ (projS S θ - projS S θ₀) (projS S y - projS S θ₀) : ℝ)
          - ‖projS S θ - projS S θ₀‖ ^ 2 / 2)
        + ((inner ℝ (projS Sᶜ θ - projS Sᶜ θ₀) (projS Sᶜ y - projS Sᶜ θ₀) : ℝ)
          - ‖projS Sᶜ θ - projS Sᶜ θ₀‖ ^ 2 / 2) := by
    rw [← projS_sub S θ θ₀, ← projS_sub Sᶜ θ θ₀, ← projS_sub S y θ₀, ← projS_sub Sᶜ y θ₀,
        inner_split S (θ - θ₀) (y - θ₀), norm_sq_split S (θ - θ₀)]
    ring
  rw [key, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

/-- **The denominator is finite and nonzero, pointwise** (the `S`-factor of the tensorization).

For any finite index type `κ`, `dlDenom θ₀ (dlPrior a κ) y ∈ (0, ∞)`: the integrand
`dlLR θ₀ θ y = exp(½‖y − θ₀‖²)·exp(−½‖θ − y‖²)` is strictly positive and bounded above by
`exp(½‖y − θ₀‖²)`, and `dlPrior a κ` is a probability measure. This lets the `S`-factor cancel in the
`ℝ≥0∞` quotient of `dlRatio_cylinder`. -/
lemma dlDenom_pos_lt_top (a : ℝ) {κ : Type*} [Fintype κ] (θ₀ y : EuclideanSpace ℝ κ) :
    0 < dlDenom θ₀ (dlPrior a κ) y ∧ dlDenom θ₀ (dlPrior a κ) y < ⊤ := by
  have hmeas : Measurable (fun θ : EuclideanSpace ℝ κ => dlLR θ₀ θ y) := by
    unfold dlLR; fun_prop
  have hpos : ∀ θ, 0 < dlLR θ₀ θ y := fun θ => by
    rw [dlLR]; exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  refine ⟨?_, ?_⟩
  · rw [dlDenom, dlNumer, Measure.restrict_univ, pos_iff_ne_zero]
    intro h
    rw [lintegral_eq_zero_iff hmeas] at h
    rw [Filter.EventuallyEq, ae_iff] at h
    simp only [Pi.zero_apply] at h
    have huniv : {θ : EuclideanSpace ℝ κ | ¬ dlLR θ₀ θ y = 0} = Set.univ :=
      Set.eq_univ_of_forall fun θ => (hpos θ).ne'
    rw [huniv, measure_univ] at h
    exact one_ne_zero h
  · rw [dlDenom, dlNumer, Measure.restrict_univ]
    have hbound : ∀ θ, dlLR θ₀ θ y ≤ ENNReal.ofReal (Real.exp (‖y - θ₀‖ ^ 2 / 2)) := by
      intro θ
      rw [dlLR]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hcs : (inner ℝ (θ - θ₀) (y - θ₀) : ℝ) ≤ ‖θ - θ₀‖ * ‖y - θ₀‖ := real_inner_le_norm _ _
      nlinarith [sq_nonneg (‖y - θ₀‖ - ‖θ - θ₀‖)]
    calc ∫⁻ θ, dlLR θ₀ θ y ∂(dlPrior a κ)
        ≤ ∫⁻ _, ENNReal.ofReal (Real.exp (‖y - θ₀‖ ^ 2 / 2)) ∂(dlPrior a κ) :=
          lintegral_mono hbound
      _ = ENNReal.ofReal (Real.exp (‖y - θ₀‖ ^ 2 / 2)) * (dlPrior a κ) Set.univ := by
          rw [lintegral_const]
      _ < ⊤ := by rw [measure_univ, mul_one]; exact ENNReal.ofReal_lt_top

/-- **The `S`-factor of the numerator peels off on a cylinder over `S`.**

For a cylinder `projS S ⁻¹' A` (constrain only the `S`-coordinates to `A`), the un-normalized
numerator factorizes as an `S`-sub-model numerator over `A` times the full `Sᶜ`-sub-model
denominator:

  `dlNumer θ₀ (dlPrior a ι) (projS S ⁻¹' A) y
      = dlNumer (projS S θ₀) (dlPrior a {j // j ∈ S}) A (projS S y)
        · dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y)`. -/
lemma dlNumer_cylinder (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ₀ y : EuclideanSpace ℝ ι) {A : Set (EuclideanSpace ℝ {j // j ∈ S})}
    -- LEAN-ONLY: `A` measurable (Tonelli split regularity)
    (hA : MeasurableSet A) :
    dlNumer θ₀ (dlPrior a ι) (projS S ⁻¹' A) y
      = dlNumer (projS S θ₀) (dlPrior a {j // j ∈ S}) A (projS S y)
        * dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y) := by
  have hmS : Measurable
      (fun ξ : EuclideanSpace ℝ {j // j ∈ S} => dlLR (projS S θ₀) ξ (projS S y)) := by
    unfold dlLR; fun_prop
  have hmSc : Measurable
      (fun ζ : EuclideanSpace ℝ {j // j ∈ Sᶜ} => dlLR (projS Sᶜ θ₀) ζ (projS Sᶜ y)) := by
    unfold dlLR; fun_prop
  have hFS : Measurable (fun ξ : EuclideanSpace ℝ {j // j ∈ S} =>
      A.indicator (fun _ => (1 : ℝ≥0∞)) ξ * dlLR (projS S θ₀) ξ (projS S y)) :=
    (measurable_const.indicator hA).mul hmS
  have hpt : ∀ θ, (projS S ⁻¹' A).indicator (fun θ' => dlLR θ₀ θ' y) θ
      = (A.indicator (fun _ => (1 : ℝ≥0∞)) (projS S θ) * dlLR (projS S θ₀) (projS S θ) (projS S y))
        * dlLR (projS Sᶜ θ₀) (projS Sᶜ θ) (projS Sᶜ y) := by
    intro θ
    simp only [Set.indicator_apply, Set.mem_preimage]
    rw [dlLR_split S θ₀ θ y]
    by_cases hθ : projS S θ ∈ A <;> simp [hθ]
  have key : dlNumer θ₀ (dlPrior a ι) (projS S ⁻¹' A) y
      = ∫⁻ θ, (A.indicator (fun _ => (1 : ℝ≥0∞)) (projS S θ)
                * dlLR (projS S θ₀) (projS S θ) (projS S y))
              * dlLR (projS Sᶜ θ₀) (projS Sᶜ θ) (projS Sᶜ y) ∂(dlPrior a ι) := by
    rw [dlNumer, ← lintegral_indicator ((measurable_projS S) hA)]
    exact lintegral_congr hpt
  rw [key, lintegral_dlPrior_split a S hFS hmSc]
  congr 1
  · rw [dlNumer, ← lintegral_indicator hA]
    apply lintegral_congr
    intro ξ
    by_cases hξ : ξ ∈ A <;> simp [Set.indicator_apply, hξ]
  · rw [dlDenom, dlNumer, Measure.restrict_univ]

/-- **Tensorization / posterior-ratio reduction to the `Sᶜ`-sub-model** (BPPD eq. (26)).

When the truth is supported on `S` (`projS Sᶜ θ₀ = 0`), the full-model posterior ratio of a cylinder
`projS Sᶜ ⁻¹' B` over the complement coordinates equals the `Sᶜ`-sub-model posterior ratio of `B`:

  `dlNumer θ₀ Π (projS Sᶜ ⁻¹' B) y / dlDenom θ₀ Π y
      = dlNumer (projS Sᶜ θ₀) Π_{Sᶜ} B (projS Sᶜ y) / dlDenom (projS Sᶜ θ₀) Π_{Sᶜ} (projS Sᶜ y)`,

where `Π = dlPrior a ι` and `Π_{Sᶜ} = dlPrior a {j // j ∈ Sᶜ}`. The `S`-factor
`dlDenom (projS S θ₀) (dlPrior a {j // j ∈ S}) (projS S y)` appears in both numerator and denominator
(via `dlNumer_cylinder` and `dlPrior_prod_apply`) and cancels because it is in `(0, ∞)`
(`dlDenom_pos_lt_top`). **Riskiest lemma of the milestone.** -/
lemma dlRatio_cylinder (a : ℝ) (S : Set ι) [DecidablePred (· ∈ S)] [DecidablePred (· ∈ Sᶜ)]
    (θ₀ y : EuclideanSpace ℝ ι)
    -- USER-INPUT: truth supported on `S` (θ₀ vanishes off `S`, i.e. `S ⊇ supp θ₀`); BPPD eq. (26) (S = S₀)
    (hθ₀ : projS Sᶜ θ₀ = 0)
    -- LEAN-ONLY: `B` measurable (cylinder regularity)
    {B : Set (EuclideanSpace ℝ {j // j ∈ Sᶜ})} (hB : MeasurableSet B) :
    dlNumer θ₀ (dlPrior a ι) (projS Sᶜ ⁻¹' B) y / dlDenom θ₀ (dlPrior a ι) y
      = dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) B (projS Sᶜ y)
          / dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y) := by
  have hmS : Measurable
      (fun ξ : EuclideanSpace ℝ {j // j ∈ S} => dlLR (projS S θ₀) ξ (projS S y)) := by
    unfold dlLR; fun_prop
  have hmSc : Measurable
      (fun ζ : EuclideanSpace ℝ {j // j ∈ Sᶜ} => dlLR (projS Sᶜ θ₀) ζ (projS Sᶜ y)) := by
    unfold dlLR; fun_prop
  -- Denominator: full-model normalizer tensorizes into the two sub-model normalizers.
  have hden : dlDenom θ₀ (dlPrior a ι) y
      = dlDenom (projS S θ₀) (dlPrior a {j // j ∈ S}) (projS S y)
        * dlDenom (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) (projS Sᶜ y) := by
    rw [dlDenom, dlNumer, Measure.restrict_univ,
        lintegral_congr (fun θ => dlLR_split S θ₀ θ y),
        lintegral_dlPrior_split a S hmS hmSc]
    congr 1 <;> rw [dlDenom, dlNumer, Measure.restrict_univ]
  -- Numerator over an `Sᶜ`-cylinder: the `S`-factor is the full `S`-sub-model normalizer.
  have hnum : dlNumer θ₀ (dlPrior a ι) (projS Sᶜ ⁻¹' B) y
      = dlDenom (projS S θ₀) (dlPrior a {j // j ∈ S}) (projS S y)
        * dlNumer (projS Sᶜ θ₀) (dlPrior a {j // j ∈ Sᶜ}) B (projS Sᶜ y) := by
    have hFSc : Measurable (fun ζ : EuclideanSpace ℝ {j // j ∈ Sᶜ} =>
        B.indicator (fun _ => (1 : ℝ≥0∞)) ζ * dlLR (projS Sᶜ θ₀) ζ (projS Sᶜ y)) :=
      (measurable_const.indicator hB).mul hmSc
    have hpt : ∀ θ, (projS Sᶜ ⁻¹' B).indicator (fun θ' => dlLR θ₀ θ' y) θ
        = dlLR (projS S θ₀) (projS S θ) (projS S y)
          * (B.indicator (fun _ => (1 : ℝ≥0∞)) (projS Sᶜ θ)
              * dlLR (projS Sᶜ θ₀) (projS Sᶜ θ) (projS Sᶜ y)) := by
      intro θ
      simp only [Set.indicator_apply, Set.mem_preimage]
      rw [dlLR_split S θ₀ θ y]
      by_cases hθ : projS Sᶜ θ ∈ B <;> simp [hθ]
    rw [dlNumer, ← lintegral_indicator ((measurable_projS Sᶜ) hB), lintegral_congr hpt,
        lintegral_dlPrior_split a S hmS hFSc]
    congr 1
    · rw [dlDenom, dlNumer, Measure.restrict_univ]
    · rw [dlNumer, ← lintegral_indicator hB]
      apply lintegral_congr
      intro ζ
      by_cases hζ : ζ ∈ B <;> simp [Set.indicator_apply, hζ]
  obtain ⟨hX0, hXtop⟩ := dlDenom_pos_lt_top a (projS S θ₀) (projS S y)
  rw [hnum, hden, ENNReal.mul_div_mul_left _ _ hX0.ne' hXtop.ne]

/-- **The standard Gaussian marginalizes to the sub-space standard Gaussian** under coordinate
restriction: `(stdGaussian (EuclideanSpace ℝ ι)).map (projS S) = stdGaussian (EuclideanSpace ℝ {S})`.
-/
private lemma stdGaussian_map_projS (S : Set ι) [DecidablePred (· ∈ S)] :
    (stdGaussian (EuclideanSpace ℝ ι)).map (projS S)
      = stdGaussian (EuclideanSpace ℝ {j // j ∈ S}) := by
  have hrestrict : Measurable (fun x : ι → ℝ => fun i : {j // j ∈ S} => x i.val) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ι)
  rw [← map_pi_eq_stdGaussian (ι := ι),
    Measure.map_map (measurable_projS S) (WithLp.measurable_toLp _ _),
    show (projS S ∘ WithLp.toLp 2)
        = (WithLp.toLp 2) ∘ (fun x : ι → ℝ => fun i : {j // j ∈ S} => x i.val) from rfl,
    ← Measure.map_map (WithLp.measurable_toLp _ _) hrestrict,
    pi_map_restrict_subtype (fun _ : ι => gaussianReal 0 1) (· ∈ S),
    map_pi_eq_stdGaussian (ι := {j // j ∈ S})]

/-- **The data measure marginalizes to the sub-model data measure**:
`(gaussShiftKernel ι θ).map (projS S) = gaussShiftKernel {j // j ∈ S} (projS S θ)`. Marginalizing
`N(θ, I)` onto the `S`-coordinates gives `N(projS S θ, I)` on the sub-space. -/
lemma gaussShift_map_projS (S : Set ι) [DecidablePred (· ∈ S)] (θ : EuclideanSpace ℝ ι) :
    (gaussShiftKernel ι θ).map (projS S) = gaussShiftKernel {j // j ∈ S} (projS S θ) := by
  rw [gaussShiftKernel_apply, gaussShiftKernel_apply,
    Measure.map_map (measurable_projS S) (by fun_prop : Measurable (· + θ)),
    show (projS S ∘ (· + θ))
        = (fun u => u + projS S θ) ∘ (projS (ι := ι) S) from by
      funext x; simp only [Function.comp_apply, projS_add],
    ← Measure.map_map (by fun_prop : Measurable (· + projS S θ)) (measurable_projS S),
    stdGaussian_map_projS]

end StatLean.Bayesian
