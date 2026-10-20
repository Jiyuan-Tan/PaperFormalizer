module
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

@[expose] public section

/-!
# The isonormal (Gaussian) process over a separable real Hilbert space

This file builds the **isonormal process**, a theorem-agnostic construction used
for the Brownian-bridge limit process.

Mathematical content.  Fix a separable real Hilbert space `H` with a countable
Hilbert basis `b : HilbertBasis ℕ ℝ H`, and an i.i.d. standard-Gaussian sequence
`(ξₙ)` realised as the coordinate maps on the infinite product measure
`iidStdGaussian := Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)`.
The **isonormal process** is the linear *isometry*

  `W : H →ₗᵢ[ℝ] L²(Ω)`,  `W h = ∑' n, ⟪bₙ, h⟫ • ξₙ`

(the series converging in `L²(Ω)`), with `‖W h‖²_{L²} = ‖h‖²_H` and each `W h`
a centred Gaussian.

Construction.  In the Hilbert space `L²(Ω) = Lp ℝ 2 iidStdGaussian` the images
`eₙ := (ξₙ as an L² element)` form an **orthonormal family** (independence +
mean `0` + variance `1`).  An orthonormal family in a complete inner-product
space induces an isometry `ℓ²(ℕ, ℝ) → L²(Ω)` (`OrthogonalFamily.linearIsometry`);
precomposing with the Hilbert-basis representation `b.repr : H ≃ₗᵢ ℓ²(ℕ, ℝ)`
gives `W`.  **No Kolmogorov extension is used** — only `Measure.infinitePi`.

This avoids the Kolmogorov-extension wall: we never build a process on a path
space by projective limits; the only product measure is the i.i.d. one, which
Mathlib already supplies via `Measure.infinitePi`.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

/-! ## A `ℕ`-indexed Hilbert basis of a separable infinite-dimensional Hilbert space

The isonormal construction below is parameterised by a *countable* Hilbert basis
`b : HilbertBasis ℕ ℝ H`.  Mathlib's `exists_hilbertBasis` only supplies a
`Set`-indexed basis `HilbertBasis s ℝ H`; for a separable infinite-dimensional
space `H` that index set `s` is countably infinite, so we can reindex it by `ℕ`
and obtain a genuine `HilbertBasis ℕ ℝ H`.

This is a theorem-agnostic `ForMathlib` brick: it is the existence witness that
feeds the isonormal process for any separable infinite-dimensional real Hilbert
space (e.g. the `L²(P)`-type spaces of the Donsker / `G_P` construction). -/

namespace HilbertBasis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An orthonormal index set in a **separable** real Hilbert space is countable.
The orthonormal vectors are pairwise at distance `√2 ≥ 1`, so the open balls of
radius `1/2` around them are pairwise disjoint; in a separable space a pairwise
disjoint family of nonempty open sets is countable. -/
theorem countable_of_separable_index [TopologicalSpace.SeparableSpace H] {s : Set H}
    (b : HilbertBasis s ℝ H) : Countable s := by
  -- pairwise-disjoint open balls of radius `1/2` around the orthonormal vectors
  have hdisj : (Set.univ : Set s).PairwiseDisjoint
      (fun x : s => Metric.ball (b x) (1 / 2 : ℝ)) := by
    intro x _ y _ hxy
    have hbxy : b x ≠ b y := fun h =>
      hxy (b.orthonormal.linearIndependent.injective h)
    -- `dist (b x) (b y) = √2`
    have hdist : dist (b x) (b y) = Real.sqrt 2 := by
      rw [dist_eq_norm]
      have hsq : ‖b x - b y‖ ^ 2 = 2 := by
        rw [norm_sub_sq_real, b.orthonormal.1 x, b.orthonormal.1 y]
        have : (inner ℝ (b x) (b y) : ℝ) = 0 := by
          have := b.orthonormal.2 (i := x) (j := y) (by exact fun h => hbxy (by rw [h]))
          simpa using this
        rw [this]; norm_num
      have hnn : (0 : ℝ) ≤ ‖b x - b y‖ := norm_nonneg _
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
        sq_nonneg (‖b x - b y‖ - Real.sqrt 2)]
    refine Metric.ball_disjoint_ball ?_
    rw [hdist]
    have : (1 : ℝ) ≤ Real.sqrt 2 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    linarith
  have hcount : (Set.univ : Set s).Countable :=
    hdisj.countable_of_isOpen (fun x _ => Metric.isOpen_ball)
      (fun x _ => ⟨b x, Metric.mem_ball_self (by norm_num)⟩)
  exact Set.countable_univ_iff.mp hcount

/-- The index set of a Hilbert basis of an **infinite-dimensional** Hilbert space
is infinite.  If it were finite, the (closed) span of the finitely many basis
vectors would be all of `H`, making `H` finite-dimensional. -/
theorem infinite_of_not_finiteDimensional (h : ¬ FiniteDimensional ℝ H)
    {s : Set H} (b : HilbertBasis s ℝ H) : Infinite s := by
  rw [← not_finite_iff_infinite]
  intro hfin
  apply h
  -- `Finite s ⟹ range b finite ⟹ span (range b) finite-dim and closed ⟹ = ⊤`
  haveI : Finite s := hfin
  have hrangefin : (Set.range b).Finite := Set.finite_range b
  haveI : FiniteDimensional ℝ ↥(Submodule.span ℝ (Set.range b)) :=
    FiniteDimensional.span_of_finite ℝ hrangefin
  have hclosed : (Submodule.span ℝ (Set.range b)).topologicalClosure
      = Submodule.span ℝ (Set.range b) :=
    Submodule.topologicalClosure_eq_self _
  have htop : Submodule.span ℝ (Set.range b) = ⊤ := by
    rw [← hclosed, b.dense_span]
  -- `H` is the finite-dimensional span
  haveI : FiniteDimensional ℝ ↥(⊤ : Submodule ℝ H) := htop ▸ inferInstance
  exact Module.Finite.equiv (Submodule.topEquiv (R := ℝ) (M := H))

/-- **A separable infinite-dimensional real Hilbert space admits a `ℕ`-indexed
Hilbert basis.**

`exists_hilbertBasis` provides a `Set`-indexed basis `HilbertBasis s ℝ H`;
separability makes `s` countable and infinite-dimensionality makes it infinite,
so `s ≃ ℕ`; reindexing the basis along that equivalence (the reindexed family is
still orthonormal with the same dense span) and applying `HilbertBasis.mk`
yields the desired `HilbertBasis ℕ ℝ H`.

The infinite-dimensionality hypothesis `¬ FiniteDimensional ℝ H` is genuine: in
finite dimension the basis is finite and no `ℕ`-indexing exists. -/
theorem exists_hilbertBasis_nat [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (hH : ¬ FiniteDimensional ℝ H) : Nonempty (HilbertBasis ℕ ℝ H) := by
  classical
  obtain ⟨s, b, hb⟩ := exists_hilbertBasis ℝ H
  haveI : Countable s := countable_of_separable_index b
  haveI : Infinite s := infinite_of_not_finiteDimensional hH b
  -- reindex `s ≃ ℕ`
  obtain ⟨e0⟩ : Nonempty (s ≃ ℕ) := nonempty_equiv_of_countable
  let e : ℕ ≃ s := e0.symm
  -- the reindexed orthonormal family
  let v : ℕ → H := fun n => b (e n)
  have hv : Orthonormal ℝ v := b.orthonormal.comp e e.injective
  -- its range equals `range b`, whose span is dense
  have hrange : Set.range v = Set.range b := by
    change Set.range (b ∘ e) = Set.range b
    exact EquivLike.range_comp (⇑b) e
  have hsp : ⊤ ≤ (Submodule.span ℝ (Set.range v)).topologicalClosure := by
    rw [hrange]
    exact le_of_eq b.dense_span.symm
  exact ⟨HilbertBasis.mk hv hsp⟩

end HilbertBasis

namespace IsonormalProcess

noncomputable section

/-! ## The i.i.d. standard-Gaussian sequence -/

/-- The law of an i.i.d. standard-Gaussian sequence: the infinite product of
`N(0,1)` measures over `ℕ`.  This is the only product measure used in the whole
construction — there is no Kolmogorov extension. -/
def iidStdGaussian : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

instance : IsProbabilityMeasure iidStdGaussian := by
  unfold iidStdGaussian; infer_instance

/-- The coordinate maps `ξ n ω = ω n`. Each is the `n`-th standard Gaussian. -/
def coord (n : ℕ) : (ℕ → ℝ) → ℝ := fun ω => ω n

@[fun_prop]
theorem measurable_coord (n : ℕ) : Measurable (coord n) :=
  measurable_pi_apply n

/-- The coordinate maps are i.i.d.: as functions of `iidStdGaussian` they are
mutually independent. -/
theorem iIndepFun_coord : iIndepFun coord iidStdGaussian := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun (_ : ℕ) => (id : ℝ → ℝ)) (fun _ => measurable_id)
  simpa only [coord, iidStdGaussian, id_eq] using! h

/-- Each coordinate map is measure-preserving onto the standard Gaussian. -/
theorem measurePreserving_coord (n : ℕ) :
    MeasurePreserving (coord n) iidStdGaussian (gaussianReal 0 1) := by
  have := measurePreserving_eval_infinitePi (μ := fun _ : ℕ => gaussianReal 0 1) n
  simpa only [coord, iidStdGaussian, Function.eval] using! this

/-- The law of each coordinate map is the standard Gaussian `N(0,1)`. -/
theorem map_coord (n : ℕ) : iidStdGaussian.map (coord n) = gaussianReal 0 1 :=
  (measurePreserving_coord n).map_eq

/-- `coord n` has law `N(0,1)`, hence is integrable with mean `0`. -/
theorem integral_coord (n : ℕ) : ∫ ω, coord n ω ∂iidStdGaussian = 0 := by
  have hmap : ∫ y, (id : ℝ → ℝ) y ∂(iidStdGaussian.map (coord n))
      = ∫ ω, coord n ω ∂iidStdGaussian :=
    integral_map (measurable_coord n).aemeasurable aestronglyMeasurable_id
  rw [← hmap, map_coord]
  simp [integral_id_gaussianReal]

/-- Each coordinate is in `L²`: standard Gaussians have finite second moment. -/
theorem memLp_coord (n : ℕ) : MemLp (coord n) 2 iidStdGaussian := by
  have h : MemLp (id : ℝ → ℝ) 2 (gaussianReal 0 1) := memLp_id_gaussianReal' 2 (by simp)
  have := h.comp_measurePreserving (measurePreserving_coord n)
  simpa only [Function.comp_def, id_eq] using this

/-- `coord n` is `L²`-integrable. -/
theorem integrable_coord_sq (n : ℕ) :
    Integrable (fun ω => coord n ω * coord n ω) iidStdGaussian :=
  (memLp_coord n).integrable_mul (memLp_coord n)

/-- The product of two distinct coordinates is integrable. -/
theorem integrable_coord_mul {m n : ℕ} :
    Integrable (fun ω => coord m ω * coord n ω) iidStdGaussian :=
  (memLp_coord m).integrable_mul (memLp_coord n)

/-! ## The orthonormal family `(eₙ)` in `L²(Ω)` -/

/-- `coord n` as an element of `L²(Ω)`. -/
def e (n : ℕ) : Lp ℝ 2 iidStdGaussian := (memLp_coord n).toLp

/-- The integral of the second moment of a standard Gaussian is `1`
(the variance, since the mean is `0`). -/
theorem integral_coord_sq (n : ℕ) :
    ∫ ω, coord n ω * coord n ω ∂iidStdGaussian = 1 := by
  have hmap : iidStdGaussian.map (coord n) = gaussianReal 0 1 := map_coord n
  have hvar : variance (coord n) iidStdGaussian = 1 := by
    rw [← variance_id_map (measurable_coord n).aemeasurable, hmap]
    simp [variance_id_gaussianReal]
  -- variance = E[X²] - (E X)², and E X = 0
  have hmean : ∫ ω, coord n ω ∂iidStdGaussian = 0 := integral_coord n
  have hsq : Integrable (fun ω => coord n ω ^ 2) iidStdGaussian := by
    simpa [pow_two] using integrable_coord_sq n
  have hX : Integrable (coord n) iidStdGaussian := (memLp_coord n).integrable (by norm_num)
  rw [variance_eq_integral hX.aemeasurable] at hvar
  rw [hmean] at hvar
  simpa [pow_two, sub_zero] using hvar

/-- For `m ≠ n`, the product of two distinct coordinates has integral `0`
(independence + mean `0`). -/
theorem integral_coord_mul_of_ne {m n : ℕ} (hmn : m ≠ n) :
    ∫ ω, coord m ω * coord n ω ∂iidStdGaussian = 0 := by
  have hindep : IndepFun (coord m) (coord n) iidStdGaussian :=
    iIndepFun_coord.indepFun hmn
  have := hindep.integral_mul_eq_mul_integral
    (memLp_coord m).aestronglyMeasurable (memLp_coord n).aestronglyMeasurable
  rw [integral_coord m, zero_mul] at this
  simpa [Pi.mul_apply] using this

/-- The `L²`-inner product of two coordinate elements is the integral of their
pointwise product. -/
theorem inner_e (m n : ℕ) :
    ⟪e m, e n⟫_ℝ = ∫ ω, coord m ω * coord n ω ∂iidStdGaussian := by
  rw [e, e, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_coord m).coeFn_toLp, (memLp_coord n).coeFn_toLp]
    with ω hm hn
  rw [hm, hn]
  change (coord n ω) * (coord m ω) = coord m ω * coord n ω
  ring

/-- The coordinate elements form an **orthonormal family** in `L²(Ω)`. -/
theorem orthonormal_e : Orthonormal ℝ e := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [inner_e]
  by_cases hmn : m = n
  · subst hmn; simp [integral_coord_sq]
  · simp [hmn, integral_coord_mul_of_ne hmn]

/-! ## The isonormal isometry `W : H →ₗᵢ[ℝ] L²(Ω)` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The orthogonal family of one-dimensional subspaces spanned by the `eₙ`. -/
def orthogonalFamily_e : OrthogonalFamily ℝ (fun _ : ℕ => ℝ)
    (fun n => LinearIsometry.toSpanSingleton ℝ (Lp ℝ 2 iidStdGaussian)
      (orthonormal_e.1 n)) :=
  orthonormal_e.orthogonalFamily

/-- The isometry `ℓ²(ℕ, ℝ) → L²(Ω)` sending a square-summable coefficient
sequence `c` to `∑' n, cₙ • eₙ`.  This is the heart of the construction:
`L²`-convergence of the series is supplied by `OrthogonalFamily.linearIsometry`,
which holds precisely because `(eₙ)` is orthonormal and the coefficients are
square-summable. -/
def fromCoeffs : lp (fun _ : ℕ => ℝ) 2 →ₗᵢ[ℝ] Lp ℝ 2 iidStdGaussian :=
  orthogonalFamily_e.linearIsometry

/-- The **isonormal process** as a linear isometry `H →ₗᵢ[ℝ] L²(Ω)`.
It is the composition of the Hilbert-basis coefficient map `b.repr` (an
isometric equivalence `H ≃ₗᵢ ℓ²(ℕ, ℝ)`) with `fromCoeffs`. -/
def isonormal (b : HilbertBasis ℕ ℝ H) : H →ₗᵢ[ℝ] Lp ℝ 2 iidStdGaussian :=
  fromCoeffs.comp b.repr.toLinearIsometry

/-- **Isometry of the isonormal process**: `‖W h‖_{L²} = ‖h‖_H`. -/
theorem isonormal_norm (b : HilbertBasis ℕ ℝ H) (h : H) :
    ‖isonormal b h‖ = ‖h‖ := by
  rw [isonormal, LinearIsometry.norm_map]

/-- **Isometry of the isonormal process (squared form)**: `‖W h‖²_{L²} = ‖h‖²_H`. -/
theorem isonormal_isometry_norm (b : HilbertBasis ℕ ℝ H) (h : H) :
    ‖isonormal b h‖ ^ 2 = ‖h‖ ^ 2 := by
  rw [isonormal_norm]

/-- **Covariance of the isonormal process**: `E[(W h)(W h')] = ⟪h, h'⟫_H`.

The isonormal map is a linear isometry `H →ₗᵢ[ℝ] L²(Ω)`, so it preserves the
inner product: `⟪W h, W h'⟫_{L²} = ⟪h, h'⟫_H` (`LinearIsometry.inner_map_map`).
The `L²`-inner product is `∫ (W h)·(W h')` (`L2.inner_def` + the real inner
reducing to multiplication), giving the covariance identity directly. -/
theorem isonormal_cov (b : HilbertBasis ℕ ℝ H) (h h' : H) :
    ∫ ω, (isonormal b h ω) * (isonormal b h' ω) ∂iidStdGaussian = ⟪h, h'⟫_ℝ := by
  have hiso : ⟪(isonormal b h : Lp ℝ 2 iidStdGaussian), isonormal b h'⟫_ℝ = ⟪h, h'⟫_ℝ :=
    (isonormal b).inner_map_map h h'
  rw [← hiso, L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  change (isonormal b h ω) * (isonormal b h' ω) = (isonormal b h' ω) * (isonormal b h ω)
  ring

/-- **Series formula**: `W h = ∑' n, ⟪bₙ, h⟫ • eₙ`, the series converging in
`L²(Ω)`. -/
theorem isonormal_eq_tsum (b : HilbertBasis ℕ ℝ H) (h : H) :
    isonormal b h = ∑' n, b.repr h n • e n := by
  rw [isonormal, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, fromCoeffs,
    OrthogonalFamily.linearIsometry_apply]
  simp only [LinearIsometry.toSpanSingleton_apply]

/-- **Convergence of the defining series** (`HasSum` form): the partial sums of
`∑ ⟪bₙ, h⟫ • eₙ` converge to `W h` in `L²(Ω)`. This is exactly Cauchy-ness of
the partial sums via the Parseval/Bessel orthogonality estimate, packaged by
`OrthogonalFamily.hasSum_linearIsometry`. -/
theorem hasSum_isonormal (b : HilbertBasis ℕ ℝ H) (h : H) :
    HasSum (fun n => b.repr h n • e n) (isonormal b h) := by
  have hsum := orthogonalFamily_e.hasSum_linearIsometry (b.repr h)
  rw [isonormal, LinearIsometry.coe_comp, Function.comp_apply,
    LinearIsometryEquiv.coe_toLinearIsometry, fromCoeffs]
  refine hsum.congr_fun ?_
  intro n
  simp only [LinearIsometry.toSpanSingleton_apply]

/-! ## Gaussian law of `W h` -/

/-- Each coordinate map has a (standard) Gaussian law. -/
theorem hasGaussianLaw_coord (n : ℕ) : HasGaussianLaw (coord n) iidStdGaussian := by
  have : IsGaussian (iidStdGaussian.map (coord n)) := by
    rw [map_coord]; infer_instance
  exact IsGaussian.hasGaussianLaw

/-- The finite partial sum `∑_{n ∈ s} ⟪bₙ, h⟫ • ξₙ`, as a function on `Ω`.
Being a finite linear combination of independent Gaussians, it is Gaussian. -/
def partialSum (b : HilbertBasis ℕ ℝ H) (h : H) (s : Finset ℕ) : (ℕ → ℝ) → ℝ :=
  fun ω => ∑ n ∈ s, b.repr h n * coord n ω

/-- Each partial sum `∑_{n ∈ s} ⟪bₙ, h⟫ ξₙ` is centred Gaussian: it is a finite
sum of independent (scaled) standard Gaussians.

This finite-dimensional Gaussian closure is proved here from
`iIndepFun.hasGaussianLaw_fun_sum`; closure under the `L²` limit is established
separately below. -/
theorem hasGaussianLaw_partialSum (b : HilbertBasis ℕ ℝ H) (h : H) (s : Finset ℕ) :
    HasGaussianLaw (partialSum b h s) iidStdGaussian := by
  classical
  -- Index the sum over the finite subtype `↥s`.
  set Y : ↥s → (ℕ → ℝ) → ℝ := fun n ω => b.repr h n * coord n ω with hY
  -- each `Y n` is Gaussian (scalar multiple of a Gaussian coordinate)
  have hGauss : ∀ n : ↥s, HasGaussianLaw (Y n) iidStdGaussian := by
    intro n
    have := (hasGaussianLaw_coord (n : ℕ)).fun_smul (b.repr h n)
    simpa [hY, smul_eq_mul] using this
  -- independence of the subfamily (restriction of `iIndepFun coord` along `(↑)`,
  -- then scaled coordinatewise by the measurable map `x ↦ b.repr h n * x`)
  have hIndep : iIndepFun Y iidStdGaussian := by
    have hsub : iIndepFun (fun n : ↥s => coord (n : ℕ)) iidStdGaussian :=
      iIndepFun_coord.precomp Subtype.val_injective
    have hcomp := hsub.comp (fun n : ↥s => fun x : ℝ => b.repr h n * x)
      (fun n => by fun_prop)
    have : Y = fun n : ↥s => (fun x : ℝ => b.repr h n * x) ∘ coord (n : ℕ) := by
      funext n ω; simp [hY]
    rw [this]
    exact hcomp
  have hsum := hIndep.hasGaussianLaw_fun_sum hGauss
  have heq : (fun ω => ∑ n : ↥s, Y n ω) = partialSum b h s := by
    funext ω
    rw [partialSum, ← Finset.sum_attach s (fun n => b.repr h n * coord n ω)]
    rfl
  rwa [heq] at hsum

/-- **Bounded convergence under convergence in measure.**  If `Sₙ → X` in measure
on a finite measure space and `g : ℝ → ℂ` is continuous and bounded, then
`∫ g(Sₙ) → ∫ g(X)`. This is the bounded-continuous test-function bridge from
convergence in measure to convergence of expectations.

Proof: every subsequence of `(Sₙ)` still converges in measure to `X`, hence has a
further subsequence converging `a.e.`; along it `g ∘ Sₙ → g ∘ X` pointwise and is
dominated by the constant bound, so dominated convergence applies.  The
subsequence-principle `tendsto_of_subseq_tendsto` upgrades this to the full
sequence. -/
theorem tendsto_integral_comp_of_tendstoInMeasure
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {S : ℕ → Ω → ℝ} {X : Ω → ℝ} (hS : ∀ n, AEMeasurable (S n) P)
    (hMeas : MeasureTheory.TendstoInMeasure P S Filter.atTop X)
    {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ} (hgb : ∀ z, ‖g z‖ ≤ C) :
    Filter.Tendsto (fun n => ∫ ω, g (S n ω) ∂P) Filter.atTop
      (nhds (∫ ω, g (X ω) ∂P)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  -- restrict the in-measure convergence to the subsequence `ns`
  have hMeas' : MeasureTheory.TendstoInMeasure P (fun k => S (ns k)) Filter.atTop X :=
    hMeas.comp hns
  -- pass to an a.e.-convergent further subsequence `ms`
  obtain ⟨ms, _hms_mono, hae⟩ := hMeas'.exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  -- dominated convergence along the double subsequence
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun k =>
      (hg.aestronglyMeasurable.comp_aemeasurable (hS (ns (ms k))))
  · refine Filter.Eventually.of_forall fun k => Filter.Eventually.of_forall fun ω => hgb _
  · exact (integrable_const C)
  · filter_upwards [hae] with ω hω
    exact (hg.tendsto (X ω)).comp hω

/-- The coercion of the finite `L²`-sum `∑_{i ∈ s} ⟪bᵢ, h⟫ • eᵢ` agrees almost
everywhere with the pointwise partial sum `partialSum b h s`.  Pure `Lp`-algebra
(coercion of sum/smul/`toLp` commute a.e.), proved by `Finset` induction. -/
theorem coeFn_lp_partialSum (b : HilbertBasis ℕ ℝ H) (h : H) (s : Finset ℕ) :
    (⇑(∑ i ∈ s, b.repr h i • e i) : (ℕ → ℝ) → ℝ)
      =ᵐ[iidStdGaussian] partialSum b h s := by
  classical
  induction s using Finset.induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := iidStdGaussian)] with ω hω
    simp only [Finset.sum_empty] at *
    rw [hω]
    simp [partialSum]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hadd := Lp.coeFn_add (b.repr h a • e a) (∑ i ∈ s, b.repr h i • e i)
    have hsmul := Lp.coeFn_smul (b.repr h a) (e a)
    have hea : (⇑(e a) : (ℕ → ℝ) → ℝ) =ᵐ[iidStdGaussian] coord a :=
      (memLp_coord a).coeFn_toLp
    filter_upwards [hadd, hsmul, hea, ih] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]
    simp only [partialSum, Finset.sum_insert ha, smul_eq_mul]

/-- The coercion of the finite `L²`-sum has a (centred) Gaussian law: it is a.e.
equal to `partialSum b h s`, which is Gaussian (`hasGaussianLaw_partialSum`). -/
theorem hasGaussianLaw_lp_partialSum (b : HilbertBasis ℕ ℝ H) (h : H) (s : Finset ℕ) :
    HasGaussianLaw (⇑(∑ i ∈ s, b.repr h i • e i) : (ℕ → ℝ) → ℝ) iidStdGaussian :=
  (hasGaussianLaw_partialSum b h s).congr (coeFn_lp_partialSum b h s).symm

/-- For a real `L²` function, `‖f‖² = ∫ f·f`. -/
theorem lp_norm_sq_eq_integral_mul (f : Lp ℝ 2 iidStdGaussian) :
    ‖f‖ ^ 2 = ∫ ω, (f : (ℕ → ℝ) → ℝ) ω * (f : (ℕ → ℝ) → ℝ) ω ∂iidStdGaussian := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]; rfl

/-- The integral of a real `L²` function is its inner product with the constant `1`. -/
theorem integral_eq_inner_one (f : Lp ℝ 2 iidStdGaussian) :
    (∫ ω, (f : (ℕ → ℝ) → ℝ) ω ∂iidStdGaussian)
      = ⟪(indicatorConstLp 2 MeasurableSet.univ
          (by simp) (1 : ℝ)), f⟫_ℝ := by
  rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
  simp only [Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  change (f : (ℕ → ℝ) → ℝ) ω = (f : (ℕ → ℝ) → ℝ) ω * 1
  rw [mul_one]

/-- **Characteristic function of the isonormal image.**  For every `t`, the
characteristic function of the pushforward law `iidStdGaussian.map (W h)` is the
centred-Gaussian form `exp(-‖h‖²·t²/2)`.

`W h` is the `L²`-limit of the centred Gaussians `Sₙ = ∑_{i<n} ⟪bᵢ, h⟫ • eᵢ`
(`hasSum_isonormal`); each `Sₙ`'s characteristic function is
`exp(E[⟪t,Sₙ⟫] I − Var[⟪t,Sₙ⟫]/2) = exp(-t²‖Sₙ‖²/2)` (mean `0`, variance `t²‖Sₙ‖²`),
and these converge to `charFun (P.map (W h)) t` (bounded convergence under
convergence in measure) and to `exp(-t²‖h‖²/2)` (norm continuity).  Uniqueness of
limits identifies the two. -/
theorem isonormal_charFun (b : HilbertBasis ℕ ℝ H) (h : H) (t : ℝ) :
    charFun (iidStdGaussian.map (isonormal b h)) t
      = Complex.exp (((- (‖h‖ ^ 2 * t ^ 2) / 2 : ℝ) : ℂ)) := by
  classical
  set P := iidStdGaussian
  set X : (ℕ → ℝ) → ℝ := ⇑(isonormal b h) with hX
  -- The partial sums, as honest functions on `Ω`.
  set S : ℕ → (ℕ → ℝ) → ℝ := fun n => ⇑(∑ i ∈ Finset.range n, b.repr h i • e i) with hS
  -- `Sₙ → X` in `L²`, hence in measure.
  have hTendstoLp : Filter.Tendsto
      (fun n => (∑ i ∈ Finset.range n, b.repr h i • e i)) Filter.atTop
      (nhds (isonormal b h)) := (hasSum_isonormal b h).tendsto_sum_nat
  have hMeas : MeasureTheory.TendstoInMeasure P S Filter.atTop X :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hTendstoLp
  -- Each partial sum is Gaussian.
  have hGaussS : ∀ n, HasGaussianLaw (S n) P := fun n =>
    hasGaussianLaw_lp_partialSum b h (Finset.range n)
  have hXmeas : AEMeasurable X P := (Lp.aestronglyMeasurable _).aemeasurable
  -- charFun in integral form for any a.e.-measurable real random variable
  have hcf : ∀ (Y : (ℕ → ℝ) → ℝ) (s : ℝ), AEMeasurable Y P →
      charFun (P.map Y) s = ∫ ω, Complex.exp (↑(s * Y ω) * Complex.I) ∂P := by
    intro Y s hY
    rw [charFun_apply, integral_map hY (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    norm_cast
  -- (A) the characteristic function of the limit is the limit of the
  -- characteristic functions of the partial sums.
  have hA : Filter.Tendsto (fun n => charFun (P.map (S n)) t) Filter.atTop
      (nhds (charFun (P.map X) t)) := by
    have hgcont : Continuous (fun z : ℝ => Complex.exp (↑(t * z) * Complex.I)) := by
      fun_prop
    have hgb : ∀ z : ℝ, ‖Complex.exp (↑(t * z) * Complex.I)‖ ≤ 1 := by
      intro z
      rw [Complex.norm_exp]
      simp [mul_comm, Complex.I_re, Complex.I_im]
    have hconv := tendsto_integral_comp_of_tendstoInMeasure
      (fun n => (hGaussS n).aemeasurable) hMeas hgcont hgb
    have hSrw : (fun n => charFun (P.map (S n)) t)
        = fun n => ∫ ω, Complex.exp (↑(t * S n ω) * Complex.I) ∂P := by
      funext n; exact hcf (S n) t (hGaussS n).aemeasurable
    have hXrw : charFun (P.map X) t = ∫ ω, Complex.exp (↑(t * X ω) * Complex.I) ∂P :=
      hcf X t hXmeas
    rw [hSrw, hXrw]
    exact hconv
  -- (B) the Gaussian form of each partial sum's characteristic function.
  have hBform : ∀ n, charFun (P.map (S n)) t
      = Complex.exp (↑(∫ ω, (⟪t, S n ω⟫_ℝ : ℝ) ∂P) * Complex.I
          - ↑(Var[fun ω => ⟪t, S n ω⟫_ℝ ; P]) / 2) :=
    fun n => (hGaussS n).charFun_map_eq t
  -- `⟪t, Sₙ ω⟫_ℝ = t * Sₙ ω` and `Sₙ =ᵐ partialSum`.
  have hinnerS : ∀ n, (fun ω => ⟪t, S n ω⟫_ℝ)
      =ᵐ[P] (fun ω => t * partialSum b h (Finset.range n) ω) := by
    intro n
    filter_upwards [coeFn_lp_partialSum b h (Finset.range n)] with ω hω
    simp only [hS]
    rw [hω]
    change partialSum b h (Finset.range n) ω * t = t * partialSum b h (Finset.range n) ω
    ring
  -- each `partialSum` is integrable (finite sum of integrable scaled coordinates)
  have hintPS : ∀ n, Integrable (partialSum b h (Finset.range n)) P := by
    intro n
    unfold partialSum
    refine integrable_finset_sum _ (fun i _ => ?_)
    exact ((memLp_coord i).integrable (by norm_num)).const_mul _
  -- Mean of each `⟪t, Sₙ⟫`: zero, since `E[partialSum] = 0`.
  have hmeanPS : ∀ n, ∫ ω, partialSum b h (Finset.range n) ω ∂P = 0 := by
    intro n
    unfold partialSum
    rw [integral_finset_sum _ (fun i _ => ((memLp_coord i).integrable (by norm_num)).const_mul _)]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [integral_const_mul, integral_coord, mul_zero]
  have hmeanS : ∀ n, ∫ ω, (⟪t, S n ω⟫_ℝ : ℝ) ∂P = 0 := by
    intro n
    rw [integral_congr_ae (hinnerS n), integral_const_mul, hmeanPS n, mul_zero]
  -- `‖Sₙ‖² → ‖h‖²` (norm continuity of the `L²`-convergent partial sums).
  have hSnorm : Filter.Tendsto (fun n => ‖∑ i ∈ Finset.range n, b.repr h i • e i‖ ^ 2)
      Filter.atTop (nhds (‖h‖ ^ 2)) := by
    have := (hTendstoLp.norm).pow 2
    rwa [isonormal_norm] at this
  -- variance of each partial sum: `Var[⟪t,Sₙ⟫] = t² ‖Sₙ‖²` (centred + `L²` norm).
  have hvarS : ∀ n, Var[fun ω => ⟪t, S n ω⟫_ℝ ; P]
      = t ^ 2 * ‖∑ i ∈ Finset.range n, b.repr h i • e i‖ ^ 2 := by
    intro n
    rw [variance_congr (hinnerS n), variance_const_mul]
    rw [variance_of_integral_eq_zero (hintPS n).aemeasurable (hmeanPS n)]
    rw [lp_norm_sq_eq_integral_mul]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [coeFn_lp_partialSum b h (Finset.range n)] with ω hω
    rw [pow_two, hω]
  -- assemble: charFun of `X` is the limit of the partial-sum charFuns,
  -- each equal to `exp(- t² ‖Sₙ‖² / 2)`, whose limit is `exp(- t² ‖h‖² / 2)`.
  set expo : ℕ → ℝ := fun n =>
    - (t ^ 2 * ‖∑ i ∈ Finset.range n, b.repr h i • e i‖ ^ 2) / 2 with hexpo
  refine tendsto_nhds_unique hA ?_
  have hform : ∀ n, charFun (P.map (S n)) t = Complex.exp ((↑(expo n) : ℂ)) := by
    intro n
    rw [hBform n, hmeanS n, hvarS n, hexpo]
    push_cast
    ring_nf
  rw [Filter.tendsto_congr hform]
  refine (Complex.continuous_exp.tendsto _).comp ?_
  refine (Complex.continuous_ofReal.tendsto _).comp ?_
  rw [hexpo]
  have hlimexpo : Filter.Tendsto
      (fun n => - (t ^ 2 * ‖∑ i ∈ Finset.range n, b.repr h i • e i‖ ^ 2) / 2)
      Filter.atTop (nhds (- (‖h‖ ^ 2 * t ^ 2) / 2)) := by
    apply Filter.Tendsto.div_const
    apply Filter.Tendsto.neg
    rw [mul_comm]
    exact (tendsto_const_nhds (x := t ^ 2)).mul hSnorm
  exact hlimexpo

/-- **`L²`-limit closure of Gaussian laws.**
The isonormal image `W h` has a Gaussian law: it is the `L²`-limit of the
centred Gaussians `∑_{i<n} ⟪bᵢ, h⟫ • eᵢ` (`hasSum_isonormal`), and Gaussianity is
closed under convergence in distribution.

This closure is not supplied by the imported API and is proved here via
characteristic functions.

The proof uses characteristic-function results from the imported API:
`HasGaussianLaw X P` is equivalent to its characteristic function having the
Gaussian form `charFun (P.map X) t = exp(E[⟪t,X⟫] I − Var[⟪t,X⟫]/2)`
(`hasGaussianLaw_iff_charFun_map_eq`).  Each partial sum `Sₙ` is Gaussian, so its
characteristic function has exactly that form (`HasGaussianLaw.charFun_map_eq`).
`Sₙ → X` in `L²` gives convergence in measure, hence (along a subsequence)
`a.e.`; the integrand `ω ↦ exp(t·· I)` is bounded by `1`, so dominated
convergence makes `charFun (P.map Sₙ) t → charFun (P.map X) t`, while the
right-hand Gaussian form converges because `L²` convergence carries the mean and
the variance to their limits.  Both sides of the equality at `Sₙ` therefore pass
to the limit, identifying `charFun (P.map X) t` with the Gaussian form.
The "every subsequence has a convergent sub-subsequence ⟹ convergence" step is
`tendsto_of_subseq_tendsto`; the limit identity is then `Measure.ext_of_charFun`
packaged inside `hasGaussianLaw_iff_charFun_map_eq`. -/
theorem hasGaussianLaw_of_l2_limit (b : HilbertBasis ℕ ℝ H) (h : H) :
    HasGaussianLaw (isonormal b h : (ℕ → ℝ) → ℝ) iidStdGaussian := by
  classical
  set P := iidStdGaussian
  set X : (ℕ → ℝ) → ℝ := ⇑(isonormal b h) with hX
  -- The partial sums, as honest functions on `Ω`.
  set S : ℕ → (ℕ → ℝ) → ℝ := fun n => ⇑(∑ i ∈ Finset.range n, b.repr h i • e i) with hS
  -- `Sₙ → X` in `L²`, hence in measure.
  have hTendstoLp : Filter.Tendsto
      (fun n => (∑ i ∈ Finset.range n, b.repr h i • e i)) Filter.atTop
      (nhds (isonormal b h)) := (hasSum_isonormal b h).tendsto_sum_nat
  have hMeas : MeasureTheory.TendstoInMeasure P S Filter.atTop X :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp hTendstoLp
  -- Each partial sum is Gaussian.
  have hGaussS : ∀ n, HasGaussianLaw (S n) P := fun n =>
    hasGaussianLaw_lp_partialSum b h (Finset.range n)
  have hXmeas : AEMeasurable X P := (Lp.aestronglyMeasurable _).aemeasurable
  -- charFun in integral form for any a.e.-measurable real random variable
  have hcf : ∀ (Y : (ℕ → ℝ) → ℝ) (s : ℝ), AEMeasurable Y P →
      charFun (P.map Y) s = ∫ ω, Complex.exp (↑(s * Y ω) * Complex.I) ∂P := by
    intro Y s hY
    rw [charFun_apply, integral_map hY (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    norm_cast
  -- It suffices that the characteristic function of `X` is the Gaussian one
  -- `exp(-‖h‖² t² / 2)`; from this `P.map X` is Gaussian, hence `HasGaussianLaw`.
  suffices hCharX : ∀ t : ℝ, charFun (P.map X) t
      = Complex.exp (((- (‖h‖ ^ 2 * t ^ 2) / 2 : ℝ) : ℂ)) by
    refine ⟨isGaussian_iff_gaussian_charFun.mpr
      ⟨0, ‖h‖ ^ 2 • ContinuousLinearMap.mul ℝ ℝ, ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, ?_⟩⟩
    · simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.mul_apply', smul_eq_mul]
      ring
    · simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.mul_apply', smul_eq_mul]
      exact mul_nonneg (sq_nonneg _) (mul_self_nonneg x)
    · intro t
      rw [hCharX t]
      congr 1
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul,
        inner_zero_right]
      push_cast
      ring
  -- The per-`t` Gaussian-form charFun computation is the standalone lemma
  -- `isonormal_charFun` (extracted below): `charFun (P.map X) t = exp(-‖h‖²t²/2)`.
  exact isonormal_charFun b h

/-- **Gaussian law of the isonormal process**.
`W h` has law `N(0, ‖h‖²)`: it is the `L²`-limit of the centred Gaussians
`partialSum b h s`, and Gaussianity is closed under `L²`-limits.

The proof uses **`L²`-limit closure of Gaussian laws**
(`hasGaussianLaw_of_l2_limit`): the finite partial sums are Gaussian
(`hasGaussianLaw_partialSum`, proved) and converge to `W h` in `L²`
(`hasSum_isonormal`, proved). The imported API supplies Gaussianity of finite
independent sums and characteristic-function uniqueness;
`hasGaussianLaw_of_l2_limit` combines these with convergence in measure and
dominated convergence to prove closure under this `L²` limit. -/
theorem isonormal_hasGaussianLaw (b : HilbertBasis ℕ ℝ H) (h : H) :
    HasGaussianLaw (isonormal b h : (ℕ → ℝ) → ℝ) iidStdGaussian :=
  hasGaussianLaw_of_l2_limit b h

/-- **Explicit pushforward law of the isonormal image.**  `W h` has law `N(0, ‖h‖²)`:
the pushforward `iidStdGaussian.map (W h)` equals the real Gaussian `gaussianReal 0 ‖h‖²`.

Both measures are finite (a pushforward of a probability measure, resp. a Gaussian),
and `Measure.ext_of_charFun` reduces equality to equality of characteristic functions.
On the left `isonormal_charFun` gives `charFun … t = exp(-‖h‖²t²/2)`; on the right
`charFun_gaussianReal` gives `exp(t·0·I − ‖h‖²·t²/2)`, whose mean term vanishes. -/
theorem isonormal_map_eq_gaussianReal (b : HilbertBasis ℕ ℝ H) (h : H) :
    iidStdGaussian.map (isonormal b h) = gaussianReal 0 ⟨‖h‖ ^ 2, sq_nonneg _⟩ := by
  show iidStdGaussian.map (isonormal b h) = gaussianReal 0 (NNReal.mk (‖h‖ ^ 2) (sq_nonneg _))
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [isonormal_charFun b h t, charFun_gaussianReal t]
  push_cast
  ring_nf

/-- The coercion of a finite `Lp`-sum equals the pointwise sum of coercions, `a.e.` -/
theorem coeFn_lp_finset_sum {ι : Type*} (f : ι → Lp ℝ 2 iidStdGaussian) (s : Finset ι) :
    (⇑(∑ i ∈ s, f i) : (ℕ → ℝ) → ℝ)
      =ᵐ[iidStdGaussian] fun ω => ∑ i ∈ s, (f i : (ℕ → ℝ) → ℝ) ω := by
  classical
  induction s using Finset.induction with
  | empty =>
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := iidStdGaussian)] with ω hω
    simp only [Finset.sum_empty]
    rw [hω]; rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with ω h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

/-- **Multivariate Gaussian law of the isonormal tuple.**  For a finite tuple
`h : Fin m → H`, the joint readout `ω ↦ (isonormal b (h k) ω)ₖ : (ℕ → ℝ) → (Fin m → ℝ)`
has a (centred, multivariate) Gaussian law under `iidStdGaussian`.

By `hasGaussianLaw_iff_charFunDual_map_eq`, it suffices to check, for
each dual `L : StrongDual ℝ (Fin m → ℝ)`, the centred-Gaussian charFunDual identity.
Writing `combo L := ∑ k, L(Pi.single k 1) • h k : H`, the composite `L ∘ X` agrees `a.e.`
with the **scalar** isonormal image `isonormal b (combo L)` (linearity of `isonormal` +
`Lp.coeFn_sum`/`Lp.coeFn_smul`), which has a 1-D Gaussian law (`isonormal_hasGaussianLaw`).
Transporting the scalar `charFunDual_map_eq` along `Measure.map_map`/`charFunDual_map`
(with the identity dual on `ℝ`) gives exactly the required form. -/
theorem isonormal_hasGaussianLaw_tuple {m : ℕ} (b : HilbertBasis ℕ ℝ H) (h : Fin m → H) :
    HasGaussianLaw
      (fun ω => (fun k => isonormal b (h k) ω) : (ℕ → ℝ) → (Fin m → ℝ)) iidStdGaussian := by
  classical
  set P := iidStdGaussian
  set X : (ℕ → ℝ) → (Fin m → ℝ) := fun ω k => isonormal b (h k) ω with hX
  -- `X` is a.e.-measurable (each coordinate is, and the codomain is a finite product).
  have hXmeas : AEMeasurable X P := by
    apply aemeasurable_pi_iff.mpr
    intro k
    exact (Lp.aestronglyMeasurable (isonormal b (h k))).aemeasurable
  rw [hasGaussianLaw_iff_charFunDual_map_eq hXmeas]
  intro L
  -- `combo L = ∑ k, L(Pi.single k 1) • h k`, and `L ∘ X =ᵐ isonormal b (combo L)`.
  set combo : H := ∑ k, L (Pi.single k 1) • h k with hcombo
  have hLX_ae : (fun ω => L (X ω)) =ᵐ[P] (isonormal b combo : (ℕ → ℝ) → ℝ) := by
    -- coeFn of the `Lp` linear combination equals the pointwise sum, a.e.
    have hiso_sum : (isonormal b combo : Lp ℝ 2 P)
        = ∑ k, (L (Pi.single k 1)) • isonormal b (h k) := by
      rw [hcombo, map_sum]
      simp_rw [map_smul]
    have hcoe : (isonormal b combo : (ℕ → ℝ) → ℝ)
        =ᵐ[P] fun ω => ∑ k, (L (Pi.single k 1)) * (isonormal b (h k) ω) := by
      rw [hiso_sum]
      refine (coeFn_lp_finset_sum (fun k => (L (Pi.single k 1)) • isonormal b (h k))
        Finset.univ).trans ?_
      have hsmul : ∀ k : Fin m, (⇑((L (Pi.single k 1)) • isonormal b (h k)) : (ℕ → ℝ) → ℝ)
          =ᵐ[P] fun ω => (L (Pi.single k 1)) * (isonormal b (h k) ω) := by
        intro k
        filter_upwards [Lp.coeFn_smul (L (Pi.single k 1)) (isonormal b (h k))] with ω hω
        rw [hω]; rfl
      filter_upwards [(ae_all_iff.mpr hsmul)] with ω hω
      exact Finset.sum_congr rfl (fun k _ => hω k)
    filter_upwards [hcoe] with ω hω
    -- `L (X ω) = ∑ k, (X ω k) • L(Pi.single k 1) = ∑ k, L(Pi.single k 1) * isonormal b (h k) ω`.
    rw [hω]
    have hdecomp : L (X ω) = ∑ k, (X ω k) • L (Pi.single k 1) := by
      conv_lhs => rw [show (X ω : Fin m → ℝ) = ∑ k, (X ω k) • (Pi.single k 1 : Fin m → ℝ) from
        pi_eq_sum_univ' (X ω)]
      rw [map_sum]
      simp only [map_smul]
    rw [hdecomp]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hX, smul_eq_mul]
    ring
  -- `L ∘ X` is Gaussian (a.e.-equal to the 1-D isonormal image).
  have hLX_gauss : HasGaussianLaw (fun ω => L (X ω)) P :=
    (isonormal_hasGaussianLaw b combo).congr hLX_ae.symm
  -- Transport the scalar `charFunDual_map_eq` to the vector `charFunDual (P.map X) L`.
  have hidR : (ContinuousLinearMap.id ℝ ℝ : StrongDual ℝ ℝ) ∘L L = L :=
    ContinuousLinearMap.id_comp L
  have hmapmap : P.map (fun ω => L (X ω)) = (P.map X).map L := by
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hXmeas]
    rfl
  calc charFunDual (P.map X) L
      = charFunDual (P.map X) ((ContinuousLinearMap.id ℝ ℝ) ∘L L) := by rw [hidR]
    _ = charFunDual ((P.map X).map L) (ContinuousLinearMap.id ℝ ℝ) :=
        (charFunDual_map L (ContinuousLinearMap.id ℝ ℝ)).symm
    _ = charFunDual (P.map (fun ω => L (X ω))) (ContinuousLinearMap.id ℝ ℝ) := by rw [hmapmap]
    _ = Complex.exp ((∫ ω, (ContinuousLinearMap.id ℝ ℝ) (L (X ω)) ∂P : ℝ) * Complex.I
          - Var[fun ω => (ContinuousLinearMap.id ℝ ℝ) (L (X ω)) ; P] / 2) :=
        hLX_gauss.charFunDual_map_eq_fun (ContinuousLinearMap.id ℝ ℝ)
    _ = Complex.exp ((∫ ω, L (X ω) ∂P : ℝ) * Complex.I
          - Var[fun ω => L (X ω) ; P] / 2) := by simp only [ContinuousLinearMap.id_apply]
    _ = Complex.exp ((P[(L : (Fin m → ℝ) →L[ℝ] ℝ) ∘ X] : ℝ) * Complex.I
          - Var[(L : (Fin m → ℝ) →L[ℝ] ℝ) ∘ X ; P] / 2) := by
        simp only [Function.comp_def]

end

end IsonormalProcess
