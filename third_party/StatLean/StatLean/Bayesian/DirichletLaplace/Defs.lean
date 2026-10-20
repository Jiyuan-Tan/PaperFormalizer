module
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import StatLean.Bayesian.ForMathlib.LaplaceDist
public import StatLean.Bayesian.ForMathlib.GammaBounds

@[expose] public section

/-!
# Dirichlet–Laplace contraction — core data model (laptop-only `Defs`)

Shared definitions for the posterior-contraction milestone (Bhattacharya–Pati–Pillai–Dunson,
*Dirichlet–Laplace priors for optimal shrinkage*, JASA 2015 / arXiv:1401.5398; tag `BPPD §X.Y`).

The Dirichlet–Laplace prior is taken in its **product / scale-mixture form** (BPPD eq. (10)):
each coordinate is, marginally, `θ | ψ ~ Laplace(ψ)`, `ψ ~ Gamma(shape a, rate 1/2)`. We do **not**
formalize the Dirichlet-normalized form (BPPD eq. (9)) nor the Bessel-function marginal density of
Proposition 3.1 — both are documented non-goals (the entire Section 3/6 proof uses only form (10)).

Objects defined here:
* `dlMarginal a` — the univariate DL marginal, as a mixture `bind`. A junk-guard returns
  `Measure.dirac 0` for `a ≤ 0`, so `dlMarginal a` is **unconditionally** a probability measure and
  the `n`-fold prior and the posterior operator `†` elaborate at every sequence index.
* `dlPrior a ι` — the `ι`-fold product prior on `EuclideanSpace ℝ ι`.
* `dlSuppCount δ θ` — the number of coordinates of `θ` exceeding `δ` in absolute value (BPPD's
  `|supp_δ(θ)|`, the approximate model size).
* `gaussShiftKernel ι` — the normal-means likelihood kernel `θ ↦ N(θ, I)` (BPPD model (1)).
* `dlLR θ₀ θ y` — the Gaussian likelihood ratio `dN(θ,I)/dN(θ₀,I) (y)`.
* `dlNumer / dlDenom` — the (un-normalized) numerator `∫_C dlLR dΠ` and denominator `∫ dlLR dΠ` of
  the posterior ratio; the whole Section 3/6 analysis is carried out on these pointwise functions,
  with the passage to Mathlib's abstract posterior `κ†Π` made exactly once (in `NormalMeansModel`).

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). Model (1), prior (10), §3.

**Proof formalization notes.** Laptop-only shared data model. `dlMarginal`'s guard makes
`IsProbabilityMeasure` a global instance. `gaussShiftKernel` is built truth-free as
`(id ×ₖ const _ (stdGaussian E)).map (+)` so that no `θ₀` is baked in. A handful of the basic
API proofs here (the probability-measure instance, the kernel-evaluation identity, and
`dlSuppCount` measurability) are laptop-closed against the `ForMathlib` bricks once those land; they
are marked with `-- LAPTOP-DEBT`.

**Bibliographic comments.** The normal means / sparse-sequence problem is classical (Donoho–Johnstone
1994; Johnstone–Silverman 2004); the DL prior and its posterior-contraction theory are due to the
BPPD paper formalized here, in the posterior-contraction framework of Ghosal–Ghosh–van der Vaart
(*Ann. Statist.* 28 (2000), 500–531) and Castillo–van der Vaart (*Ann. Statist.* 40 (2012),
2069–2101).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-! ### The Dirichlet–Laplace marginal and prior -/

/-- **Dirichlet–Laplace univariate marginal** `DLₐ` (BPPD eq. (10)): the scale mixture
`θ | ψ ~ Laplace(ψ)`, `ψ ~ Gamma(shape a, rate 1/2)`, realized as a `bind`. For `a ≤ 0` it falls
back to `Measure.dirac 0` so that the object is a probability measure for every real `a`
(convenience for sequence-indexed statements at junk indices; all content lemmas assume `0 < a`). -/
noncomputable def dlMarginal (a : ℝ) : Measure ℝ :=
  if 0 < a then (gammaMeasure a 2⁻¹).bind laplaceMeasure else Measure.dirac 0

/-- On `0 < a`, `dlMarginal a` unfolds to the mixture `bind`. -/
lemma dlMarginal_eq_bind {a : ℝ} (ha : 0 < a) :
    dlMarginal a = (gammaMeasure a 2⁻¹).bind laplaceMeasure := if_pos ha

/-- `dlMarginal a` is a probability measure for every `a` (dirac branch trivial; mixture branch uses
the Laplace probability-mass identity and the positivity of the Gamma support). -/
instance isProbabilityMeasure_dlMarginal (a : ℝ) : IsProbabilityMeasure (dlMarginal a) := by
  rw [dlMarginal]
  split
  · rename_i ha
    haveI : IsProbabilityMeasure (gammaMeasure a 2⁻¹) :=
      isProbabilityMeasure_gammaMeasure ha (by norm_num)
    have hmeas : Measurable (fun b => laplaceMeasure b) :=
      Measure.measurable_of_measurable_coe _ (fun s hs => measurable_laplaceMeasure_apply hs)
    refine ⟨?_⟩
    rw [Measure.bind_apply MeasurableSet.univ hmeas.aemeasurable]
    -- `gammaMeasure` is supported on `Ioi 0`, and `laplaceMeasure b` is a probability measure there.
    have hpos : ∀ᵐ b ∂(gammaMeasure a 2⁻¹), (0 : ℝ) < b := by
      rw [ae_iff]
      simp only [not_lt]
      exact gammaMeasure_Iic_eq_zero ha (by norm_num)
    have hae : (fun b => laplaceMeasure b Set.univ) =ᵐ[gammaMeasure a 2⁻¹] fun _ => 1 := by
      filter_upwards [hpos] with b hb
      haveI := isProbabilityMeasure_laplaceMeasure hb
      exact measure_univ
    rw [lintegral_congr_ae hae, lintegral_one, measure_univ]
  · infer_instance

/-- **Dirichlet–Laplace product prior** `DLₐ` on `ℝ^ι` (BPPD eq. (10), joint form): the `ι`-fold
product of `dlMarginal a`, transported onto `EuclideanSpace ℝ ι`. -/
noncomputable def dlPrior (a : ℝ) (ι : Type*) [Fintype ι] : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi fun _ : ι => dlMarginal a).map (WithLp.toLp 2)

instance isProbabilityMeasure_dlPrior (a : ℝ) (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (dlPrior a ι) := by
  rw [dlPrior]
  haveI : ∀ _i : ι, IsProbabilityMeasure (dlMarginal a) := fun _ => isProbabilityMeasure_dlMarginal a
  refine ⟨?_⟩
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-! ### Approximate model size -/

/-- **δ-support size** `|supp_δ(θ)|` (BPPD §3): the number of coordinates of `θ` with `|θⱼ| > δ`. -/
noncomputable def dlSuppCount (δ : ℝ) (θ : EuclideanSpace ℝ ι) : ℕ :=
  (Finset.univ.filter fun j => δ < |θ j|).card

/-- `θ ↦ dlSuppCount δ θ` is measurable (finite combination of the measurable level sets
`{θ | δ < |θ j|}`). -/
lemma measurable_dlSuppCount (δ : ℝ) :
    Measurable (fun θ : EuclideanSpace ℝ ι => dlSuppCount δ θ) := by
  classical
  simp only [dlSuppCount, Finset.card_filter]
  refine Finset.measurable_sum _ (fun j _ => ?_)
  refine Measurable.ite (measurableSet_lt measurable_const ?_) measurable_const measurable_const
  exact (measurable_pi_apply j).comp ((MeasurableEquiv.toLp 2 (ι → ℝ)).symm).measurable |>.abs

/-! ### The normal-means model -/

/-- **Normal-means likelihood kernel** `K θ = N(θ, I)` (BPPD model (1)), built truth-free as
`(id ×ₖ const _ (stdGaussian E)).map (·+·)`: on input `θ` it returns the standard Gaussian shifted
by `θ`. -/
noncomputable def gaussShiftKernel (ι : Type*) [Fintype ι] :
    Kernel (EuclideanSpace ℝ ι) (EuclideanSpace ℝ ι) :=
  (Kernel.id ×ₖ Kernel.const _ (stdGaussian (EuclideanSpace ℝ ι))).map (fun p => p.1 + p.2)

instance isMarkovKernel_gaussShiftKernel (ι : Type*) [Fintype ι] :
    IsMarkovKernel (gaussShiftKernel ι) := by
  rw [gaussShiftKernel]
  haveI : IsProbabilityMeasure (stdGaussian (EuclideanSpace ℝ ι)) := inferInstance
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- `gaussShiftKernel ι θ = N(θ, I) = stdGaussian shifted by θ`. -/
lemma gaussShiftKernel_apply (θ : EuclideanSpace ℝ ι) :
    gaussShiftKernel ι θ = (stdGaussian (EuclideanSpace ℝ ι)).map (· + θ) := by
  have hadd : Measurable (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι => p.1 + p.2) := by
    fun_prop
  rw [gaussShiftKernel, Kernel.map_apply _ hadd, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hadd (by fun_prop)]
  congr 1
  ext x
  simp [Function.comp, add_comm]

/-! ### Likelihood ratio and the un-normalized posterior ratio -/

/-- **Gaussian likelihood ratio** `dN(θ,I)/dN(θ₀,I)(y) = exp(⟪θ−θ₀, y−θ₀⟫ − ‖θ−θ₀‖²/2)`
(the DL posterior integrand, BPPD §6). -/
noncomputable def dlLR (θ₀ θ y : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (⟪θ - θ₀, y - θ₀⟫ - ‖θ - θ₀‖ ^ 2 / 2))

lemma measurable_dlLR_uncurry (θ₀ : EuclideanSpace ℝ ι) :
    Measurable (Function.uncurry fun θ y : EuclideanSpace ℝ ι => dlLR θ₀ θ y) := by
  unfold Function.uncurry dlLR
  fun_prop

/-- **Un-normalized posterior numerator** `∫_C exp(LR) dΠ` at data `y` (BPPD §6). -/
noncomputable def dlNumer (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    (C : Set (EuclideanSpace ℝ ι)) (y : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ∫⁻ θ in C, dlLR θ₀ θ y ∂π

/-- **Un-normalized posterior denominator** `∫ exp(LR) dΠ = m(y)` at data `y` (BPPD §6). -/
noncomputable def dlDenom (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    (y : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  dlNumer θ₀ π Set.univ y

lemma dlNumer_le_dlDenom (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    (C : Set (EuclideanSpace ℝ ι)) (y : EuclideanSpace ℝ ι) :
    dlNumer θ₀ π C y ≤ dlDenom θ₀ π y := by
  rw [dlDenom, dlNumer, dlNumer, setLIntegral_univ]
  exact setLIntegral_le_lintegral _ _

lemma dlNumer_mono (θ₀ : EuclideanSpace ℝ ι) (π : Measure (EuclideanSpace ℝ ι))
    {C D : Set (EuclideanSpace ℝ ι)} (hCD : C ⊆ D) (y : EuclideanSpace ℝ ι) :
    dlNumer θ₀ π C y ≤ dlNumer θ₀ π D y := by
  rw [dlNumer, dlNumer]
  exact lintegral_mono' (Measure.restrict_mono hCD le_rfl) le_rfl

end StatLean.Bayesian
