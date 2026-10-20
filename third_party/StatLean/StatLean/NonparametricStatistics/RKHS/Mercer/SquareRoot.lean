module
public import StatLean.NonparametricStatistics.RKHS.Mercer.Theorem
public import StatLean.NonparametricStatistics.RKHS.RangeSpace
public import StatLean.NonparametricStatistics.RKHS.Uniqueness
public import StatLean.NonparametricStatistics.RKHS.Papadakis
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# The square root of a Mercer operator and the RKHS `H(K)`

Let `K` be a Mercer kernel with eigensystem `{(eₙ, λₙ)}` against a full-support finite
Borel measure `μ`.  The **square-root symbol** `S(x,y) = ∑ₙ √λₙ eₙ(x) conj (eₙ(y))`
(convergent in `L²` sense in each variable, though generally not continuous) defines a
bounded positive integral operator `T_S` with `T_S² = T_K`, and it exhibits the measure-
independent RKHS `H(K)` as a range space:

* `range T_S = H(K)` (as sets of functions on `X`), and `T_S` is an isometry of
  `(ker T_K)ᗮ` onto `H(K)`;
* `{√λₙ eₙ}` is an orthonormal basis of `H(K)`;
* `H(K)` consists exactly of the sums `∑ₙ aₙ eₙ` with `∑ₙ |aₙ|²/λₙ < ∞`.

Also here: `T_K²` is the integral operator with symbol the box product `K □ K`, and
`(∫ K(t,t) dμ)·K − K □ K` is again a Mercer kernel, whence `range T_K ⊆ H(K)`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 11, §11.3, Propositions 11.16–11.17 ($T_K^2$ and the Cholesky domination $CK -
K^{(2)}$) and Theorem 11.18 (the square root $T_S$, $\mathcal{H}(K)$ as its range, the orthonormal
basis $\{\sqrt{\lambda_n} e_n\}$, and the spectral membership test).

**Proof formalization notes.** The square-root symbol must NOT be defined as a pointwise unordered
sum: for a scalar family `∑'` is absolute summability, and $\|\sqrt{\lambda_n}
e_n(x)\overline{e_n(y)}\|$ is generically non-summable — on the circle with $K = \sum_n
(1+n^2)^{-1} e^{in(x-y)}$ the terms decay like $|n|^{-1}$, the `tsum` junk-defaults to $0$, and
the square-root theory would be false (the counterexample is preserved in the `sqrtSectionLp`
docstring). Instead the section $S(x,\cdot)$ is the $L^2$-valued `tsum` of the orthogonal family
$(\sqrt{\lambda_n} e_n(x))\cdot\overline{e_n}$, convergent since $\sum_n \lambda_n |e_n(x)|^2 \le
\mathrm{re}\,K(x,x)$. All of Theorem 11.18 flows from the master identity $T_S g(x) = \sum_n
\sqrt{\lambda_n}\, e_n(x)\langle e_n, g\rangle$; the $\mathcal{H}(K)$-side statements are
transported from the range space of $S$ (where $S \square S^* = K$) through the kernel-uniqueness
isometry, and the orthonormal basis claim goes through Papadakis' Parseval-frame criterion.

**Bibliographic comments.** The square-root factorization of Mercer operators and the
spectral description of `H(K)` are classical; see H. König, *Eigenvalue Distribution of
Compact Operators* (Birkhäuser, 1986), and E. Parzen, *Statistical inference on time
series by Hilbert space methods* (1959) for the statistical reading.
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

section BoxSquare

omit [MeasurableSpace X] [BorelSpace X] in
/-- Uniform bound on a continuous kernel over the compact square. -/
private theorem exists_bnd {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : X, ‖K x y‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun p : X × X => K p.1 p.2) hKc.continuousOn
  exact ⟨max M 0, le_max_right _ _,
    fun x y => le_trans (hM (x, y) (Set.mem_univ _)) (le_max_left _ _)⟩

/-- The box square of a continuous symbol on a compact space is continuous. -/
theorem continuous_boxProd {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    Continuous fun p : X × X => boxProd μ K K p.1 p.2 := by
  obtain ⟨M, hM0, hM⟩ := exists_bnd hKc
  refine continuous_of_dominated (bound := fun _ : X => M * M) ?_ ?_ (integrable_const _) ?_
  · intro p
    exact (((hKc.comp' (continuous_const.prodMk continuous_id))).mul
      (hKc.comp' (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · intro p
    filter_upwards with t
    rw [norm_mul]
    exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hM0
  · filter_upwards with t
    exact (hKc.comp' (continuous_fst.prodMk continuous_const)).mul
      (hKc.comp' (continuous_const.prodMk continuous_snd))


/-- **`T_K²` is the integral operator with symbol `K □ K`.** -/
theorem mercerCLM_comp_self {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    (mercerCLM μ hKc).comp (mercerCLM μ hKc)
      = mercerCLM (K := boxProd μ K K) μ (continuous_boxProd (μ := μ) hKc) := by
  obtain ⟨M, hM0, hM⟩ := exists_bnd hKc
  refine ContinuousLinearMap.ext fun g => ?_
  refine Lp.ext ?_
  filter_upwards [mercerCLM_coeFn_ae hKc (mercerCLM μ hKc g),
    mercerCLM_coeFn_ae (K := boxProd μ K K) (continuous_boxProd (μ := μ) hKc) g] with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  have hg1 : Integrable (fun z => (g : X → 𝕜) z) μ := (Lp.memLp g).integrable (by norm_num)
  have hstep1 : integralOp μ K (mercerCLM μ hKc g) x
      = ∫ y, K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) ∂μ := by
    rw [integralOp]
    refine integral_congr_ae ?_
    filter_upwards [mercerCLM_coeFn_ae hKc g] with y hy
    rw [hy, integralOp]
  have hint : Integrable (Function.uncurry fun y z => K x y * K y z * (g : X → 𝕜) z)
      (μ.prod μ) := by
    have hg2 : Integrable (fun p : X × X => (g : X → 𝕜) p.2) (μ.prod μ) :=
      MeasureTheory.Integrable.comp_snd hg1 μ
    refine hg2.bdd_mul (c := M * M) ?_ ?_
    · exact ((hKc.comp' (continuous_const.prodMk continuous_fst)).mul
        (hKc.comp' (continuous_fst.prodMk continuous_snd))).aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul]
      exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hM0
  have hswap : ∫ y, K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) ∂μ
      = ∫ z, (∫ y, K x y * K y z ∂μ) * (g : X → 𝕜) z ∂μ := by
    have h1' : ∫ y, K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) ∂μ
        = ∫ y, ∫ z, K x y * K y z * (g : X → 𝕜) z ∂μ ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have e := integral_const_mul (μ := μ) (K x y) (fun z => K y z * (g : X → 𝕜) z)
      change K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) = ∫ z, K x y * K y z * (g : X → 𝕜) z ∂μ
      rw [← e]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [h1', integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have e := integral_mul_const (μ := μ) ((g : X → 𝕜) z) (fun y => K x y * K y z)
    change (∫ y, K x y * K y z * (g : X → 𝕜) z ∂μ) = (∫ y, K x y * K y z ∂μ) * (g : X → 𝕜) z
    rw [← e]
  rw [hstep1, hswap, integralOp]
  rfl

/-- A continuous function on a compact space is integrable against a finite measure. -/
private theorem integrable_of_cont {f : X → 𝕜} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => hM x (Set.mem_univ _)))

/-- **`(∫ K(t,t) dμ) · K − K □ K` is a Mercer kernel** (Cholesky-style domination of the
box square by the trace multiple of `K`). -/
theorem isMercerKernel_trace_smul_sub_boxProd {K : X → X → 𝕜}
    (hK : IsMercerKernel 𝕜 K) :
    IsMercerKernel 𝕜 fun x y =>
      ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K x y - boxProd μ K K x y := by
  have hcont : Continuous fun p : X × X =>
      ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K p.1 p.2 - boxProd μ K K p.1 p.2 :=
    (continuous_const.mul hK.continuous).sub (continuous_boxProd (μ := μ) hK.continuous)
  -- the diagonal of `K` is real, so the trace constant is the integral of `K t t`
  have hreal : ∀ t : X, ((RCLike.re (K t t) : ℝ) : 𝕜) = K t t := fun t =>
    RCLike.conj_eq_iff_re.mp (hK.isKernelFun.conj_symm t t)
  have htrace : ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) = ∫ t, K t t ∂μ := by
    rw [← integral_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall hreal)
  -- the kernel is a `t`-integral of the elementary Cholesky kernels
  have hpt : ∀ x y : X,
      ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K x y - boxProd μ K K x y
        = ∫ t, (K t t * K x y - K x t * K t y) ∂μ := by
    intro x y
    have i1 : Integrable (fun t => K t t * K x y) μ :=
      integrable_of_cont ((hK.continuous.comp' (continuous_id.prodMk continuous_id)).mul
        continuous_const)
    have i2 : Integrable (fun t => K x t * K t y) μ :=
      integrable_of_cont ((hK.continuous.comp' (continuous_const.prodMk continuous_id)).mul
        (hK.continuous.comp' (continuous_id.prodMk continuous_const)))
    rw [integral_sub i1 i2, htrace, boxProd, integral_mul_const]
  refine ⟨hcont, ⟨fun x y => ?_, fun n x a => ?_⟩⟩
  · rw [hpt, hpt, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [map_sub, map_mul, hK.isKernelFun.conj_symm]
    ring
  · obtain ⟨H₀, _, _, _, _, hKH⟩ := hK.isKernelFun.exists_rkhs
    have hker : ∀ p q : X, K p q = ⟪kernelFun H₀ p, kernelFun H₀ q⟫_𝕜 := by
      intro p q
      rw [← hKH, scalarKernel_eq_inner]
    set v : H₀ := ∑ j, a j • kernelFun H₀ (x j) with hv
    have hsum1 : (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j)) = ⟪v, v⟫_𝕜 := by
      have key : (∑ i, ∑ j, conj (a i) * a j * ⟪kernelFun H₀ (x i), kernelFun H₀ (x j)⟫_𝕜)
          = ⟪∑ i, a i • kernelFun H₀ (x i), ∑ j, a j • kernelFun H₀ (x j)⟫_𝕜 := by
        rw [sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_smul_left, inner_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right]; ring
      simp_rw [hker]
      rw [key, hv]
    have hsum2 : ∀ t : X, (∑ i, ∑ j, conj (a i) * a j * (K (x i) t * K t (x j)))
        = ⟪v, kernelFun H₀ t⟫_𝕜 * ⟪kernelFun H₀ t, v⟫_𝕜 := by
      intro t
      have key : ⟪v, kernelFun H₀ t⟫_𝕜 * ⟪kernelFun H₀ t, v⟫_𝕜
          = (∑ i, conj (a i) * ⟪kernelFun H₀ (x i), kernelFun H₀ t⟫_𝕜) *
            (∑ j, a j * ⟪kernelFun H₀ t, kernelFun H₀ (x j)⟫_𝕜) := by
        rw [hv, sum_inner, inner_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => inner_smul_left _ _ _
        · exact Finset.sum_congr rfl fun j _ => inner_smul_right _ _ _
      rw [key, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hker, hker]
      ring
    have hcomb : ∀ t : X,
        (∑ i, ∑ j, conj (a i) * a j * (K t t * K (x i) (x j) - K (x i) t * K t (x j)))
          = ((‖kernelFun H₀ t‖ ^ 2 * ‖v‖ ^ 2 - ‖⟪kernelFun H₀ t, v⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
      intro t
      have hstep : (∑ i, ∑ j, conj (a i) * a j * (K t t * K (x i) (x j) - K (x i) t * K t (x j)))
          = K t t * (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j))
            - ∑ i, ∑ j, conj (a i) * a j * (K (x i) t * K t (x j)) := by
        calc (∑ i, ∑ j, conj (a i) * a j * (K t t * K (x i) (x j) - K (x i) t * K t (x j)))
            = ∑ i, ∑ j, (K t t * (conj (a i) * a j * K (x i) (x j))
                - conj (a i) * a j * (K (x i) t * K t (x j))) :=
              Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ i, (K t t * (∑ j, conj (a i) * a j * K (x i) (x j))
                - ∑ j, conj (a i) * a j * (K (x i) t * K t (x j))) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
          _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hstep, hsum1, hsum2 t]
      have h1 : K t t = ((‖kernelFun H₀ t‖ : 𝕜)) ^ 2 := by
        rw [← hKH]; exact scalarKernel_self H₀ t
      have h2 : ⟪v, v⟫_𝕜 = ((‖v‖ : 𝕜)) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) v
      have h3 : ⟪v, kernelFun H₀ t⟫_𝕜 * ⟪kernelFun H₀ t, v⟫_𝕜
          = ((‖⟪kernelFun H₀ t, v⟫_𝕜‖ : 𝕜)) ^ 2 := by
        rw [← inner_conj_symm v (kernelFun H₀ t), RCLike.conj_mul]
      rw [h1, h2, h3]
      push_cast
      ring
    -- integrate the elementary quadratic forms
    have hintbl : ∀ i j : Fin n,
        Integrable (fun t => conj (a i) * a j *
          (K t t * K (x i) (x j) - K (x i) t * K t (x j))) μ := by
      intro i j
      refine (integrable_of_cont ?_).const_mul _
      exact ((hK.continuous.comp' (continuous_id.prodMk continuous_id)).mul
        continuous_const).sub
        ((hK.continuous.comp' (continuous_const.prodMk continuous_id)).mul
          (hK.continuous.comp' (continuous_id.prodMk continuous_const)))
    have hfinal : (∑ i, ∑ j, conj (a i) * a j *
        (((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K (x i) (x j) - boxProd μ K K (x i) (x j)))
        = ((∫ t, (‖kernelFun H₀ t‖ ^ 2 * ‖v‖ ^ 2
            - ‖⟪kernelFun H₀ t, v⟫_𝕜‖ ^ 2) ∂μ : ℝ) : 𝕜) := by
      have e1 : ∀ i j : Fin n, conj (a i) * a j *
          (((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K (x i) (x j) - boxProd μ K K (x i) (x j))
          = ∫ t, conj (a i) * a j *
              (K t t * K (x i) (x j) - K (x i) t * K t (x j)) ∂μ := by
        intro i j
        rw [hpt, integral_const_mul]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        (integral_finset_sum Finset.univ fun j _ => hintbl i j).symm]
      rw [← integral_finset_sum Finset.univ
        fun i _ => integrable_finset_sum Finset.univ fun j _ => hintbl i j]
      rw [← integral_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall hcomb)
    rw [hfinal, RCLike.ofReal_re]
    refine integral_nonneg fun t => ?_
    simp only [Pi.zero_apply]
    have hcs := norm_inner_le_norm (𝕜 := 𝕜) (kernelFun H₀ t) v
    have hsq := mul_self_le_mul_self (norm_nonneg (⟪kernelFun H₀ t, v⟫_𝕜)) hcs
    nlinarith [hsq, norm_nonneg (kernelFun H₀ t), norm_nonneg v]


end BoxSquare

section SquareRoot

variable {K : X → X → 𝕜} {hKc : Continuous fun p : X × X => K p.1 p.2}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

variable (d : MercerEigensystem μ K hKc)

/-- The `x`-section of the **square-root symbol**, as an element of `L²(X, μ)`:
`S(x, ·) = ∑ₙ √λₙ eₙ(x) conj (eₙ(·))`, with the sum taken **in `L²`** — the `tsum` is
computed in the Banach space `Lp 𝕜 2 μ`, where the scaled family is orthogonal with
square norms `λₙ ‖eₙ(x)‖²` summing to `re K(x,x) < ∞`, so it converges unconditionally.

The sum must NOT be taken pointwise: for a scalar family the unordered `∑'` is
equivalent to absolute summability, and `‖√λₙ eₙ(x) conj (eₙ(y))‖` is generically not
summable (on the circle with `K x y = ∑_{n ∈ ℤ} (1+n²)⁻¹ e^{i n (x−y)}` one gets
`λₙ = (1+n²)⁻¹`, `eₙ = e^{i n ·}`, and section terms `∼ |n|⁻¹`); a pointwise `tsum`
definition would junk-default to `0` and make the square-root theory false.  Even
a.e.-pointwise convergence cannot rescue a pointwise definition: an `ℓ²`-coefficient
series along a general orthonormal system need not converge a.e. (Menshov–Rademacher),
and unordered pointwise summability fails regardless (the circle example above). -/
noncomputable def sqrtSectionLp (x : X) : Lp 𝕜 2 μ :=
  ∑' n, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) •
    ContinuousMap.toLp 2 μ 𝕜 (star (d.eigfun n))

/-- The **square-root symbol** `S` of a Mercer eigensystem: the chosen representative of
the `L²` section `sqrtSectionLp d x`.  Its pointwise values in the second variable are
only meaningful up to a.e.-equivalence; all statements below access it through
`integralOp` and `L²` pairings, which see only the class. -/
noncomputable def sqrtSymbol : X → X → 𝕜 := fun x => sqrtSectionLp d x

-- Conjugation of an eigenfunction conjugates its `L²` inner products.
private theorem inner_toLp_star (n m : d.ι) :
    ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)),
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun m))⟫_𝕜
      = conj ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n),
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m)⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards
    [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (star (d.eigfun n)),
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (star (d.eigfun m)),
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n),
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun m)]
    with a h1 h2 h3 h4
  rw [h1, h2, h3, h4, RCLike.inner_apply, RCLike.inner_apply]
  simp [RCLike.star_def]

-- The conjugated eigenfunctions are again orthonormal in `L²(X, μ)`.
private theorem orthonormal_toLp_star :
    Orthonormal 𝕜 fun n : d.ι => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)) := by
  constructor
  · intro n
    have h1 : ((‖ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))‖ : 𝕜)) ^ 2 = 1 := by
      rw [← inner_self_eq_norm_sq_to_K, inner_toLp_star d n n, inner_self_eq_norm_sq_to_K,
        d.orthonormal.1 n]
      norm_num
    have h2 : ‖ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))‖ ^ 2 = 1 :=
      RCLike.ofReal_inj.mp (by push_cast; exact h1)
    nlinarith [norm_nonneg (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))]
  · intro n m hnm
    rw [inner_toLp_star d n m, d.orthonormal.2 hnm, map_zero]

-- The diagonal of the (proved) Mercer expansion, in real form.
private theorem hasSum_diag (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure] (x : X) :
    HasSum (fun n => d.eigval n * ‖d.eigfun n x‖ ^ 2) (RCLike.re (K x x)) := by
  refine ((d.hasSum_kernel hK x x).map
    (RCLike.reCLM (K := 𝕜)).toLinearMap.toAddMonoidHom RCLike.reCLM.continuous).congr_fun
    fun n => ?_
  change d.eigval n * ‖d.eigfun n x‖ ^ 2
      = RCLike.re ((d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n x)))
  rw [RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

-- The squared modulus of the `n`-th coefficient of the section at `x`.
private theorem norm_sq_sqrtCoeff (n : d.ι) (x : X) :
    ‖((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x‖ ^ 2
      = d.eigval n * ‖d.eigfun n x‖ ^ 2 := by
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (d.eigval_pos n).le]

-- The defining series of `sqrtSectionLp` really converges (orthogonal family with
-- square-summable coefficients).
private theorem hasSum_sqrtSectionLp (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure] (x : X) :
    HasSum (fun n => (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) •
      ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))) (sqrtSectionLp d x) := by
  have hon := (orthonormal_toLp_star d).orthogonalFamily
  have hiff := hon.summable_iff_norm_sq_summable
    (fun n => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x)
  simp only [LinearIsometry.toSpanSingleton_apply] at hiff
  refine Summable.hasSum (hiff.mpr ?_)
  exact ((hasSum_diag d hK x).summable).congr fun n => (norm_sq_sqrtCoeff d n x).symm

-- The `n`-th coefficient is recovered by pairing with the `n`-th conjugated eigenfunction.
private theorem inner_toLp_star_sqrtSectionLp (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (x : X) (n : d.ι) :
    ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)), sqrtSectionLp d x⟫_𝕜
      = ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x := by
  classical
  have h := (hasSum_sqrtSectionLp d hK x).mapL
    (innerSL 𝕜 (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))))
  refine h.unique ?_
  have hfun : ∀ m : d.ι,
      ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)),
        (((Real.sqrt (d.eigval m) : ℝ) : 𝕜) * d.eigfun m x) •
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun m))⟫_𝕜
      = if m = n then ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x else 0 := by
    intro m
    have hself : ∀ k : d.ι, ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun k)),
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun k))⟫_𝕜 = 1 := by
      intro k
      rw [inner_self_eq_norm_sq_to_K, (orthonormal_toLp_star d).1 k]
      norm_num
    rw [inner_smul_right]
    by_cases hmn : m = n
    · subst hmn
      rw [if_pos rfl, hself m, mul_one]
    · rw [if_neg hmn, (orthonormal_toLp_star d).2 (Ne.symm hmn), mul_zero]
  exact (hasSum_ite_eq n (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x)).congr_fun
    fun m => hfun m

-- The `L²` norm of the section is the kernel diagonal.
private theorem norm_sq_sqrtSectionLp (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure] (x : X) :
    ‖sqrtSectionLp d x‖ ^ 2 = RCLike.re (K x x) := by
  have h := (hasSum_sqrtSectionLp d hK x).mapL (innerSL 𝕜 (sqrtSectionLp d x))
  have hre := h.map (RCLike.reCLM (K := 𝕜)).toLinearMap.toAddMonoidHom RCLike.reCLM.continuous
  have hval : ∀ n : d.ι,
      RCLike.re (⟪sqrtSectionLp d x, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))⟫_𝕜)
      = d.eigval n * ‖d.eigfun n x‖ ^ 2 := by
    intro n
    rw [inner_smul_right, ← inner_conj_symm, inner_toLp_star_sqrtSectionLp d hK x n,
      RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    exact norm_sq_sqrtCoeff d n x
  have h2 : RCLike.re (K x x) = RCLike.re (⟪sqrtSectionLp d x, sqrtSectionLp d x⟫_𝕜) :=
    (hasSum_diag d hK x).unique (hre.congr_fun fun n => (hval n).symm)
  rw [h2, ← norm_sq_eq_re_inner (𝕜 := 𝕜)]

-- The conjugate of an `L²` function, as an `L²` function.
private noncomputable def starLp (g : Lp 𝕜 2 μ) : Lp 𝕜 2 μ := ((Lp.memLp g).star).toLp _

private theorem coeFn_starLp (g : Lp 𝕜 2 μ) :
    (starLp g : X → 𝕜) =ᵐ[μ] fun y => conj ((g : X → 𝕜) y) :=
  MemLp.coeFn_toLp _

private theorem norm_starLp (f : Lp 𝕜 2 μ) : ‖starLp f‖ = ‖f‖ := by
  rw [starLp, Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun y => by simp)

private theorem norm_sq_eq_integral (u : Lp 𝕜 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖(u : X → 𝕜) x‖ ^ 2 ∂μ := by
  have h1 : ⟪u, u⟫_𝕜 = ((∫ x, ‖(u : X → 𝕜) x‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
    rw [L2.inner_def, ← integral_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ⟪(u : X → 𝕜) x, (u : X → 𝕜) x⟫_𝕜 = ((‖(u : X → 𝕜) x‖ ^ 2 : ℝ) : 𝕜)
    rw [RCLike.inner_apply, RCLike.mul_conj, ← RCLike.ofReal_pow]
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), h1, RCLike.ofReal_re]

variable (μ) in
/-- The **bilinear** `L²` pairing `f ↦ ∫ f y · g y dμ` (no conjugation), packaged as a
continuous additive map — this is the functional through which `integralOp` reads a
symbol section, and it is what transports the `L²`-convergent series defining
`sqrtSectionLp` into a scalar series. -/
private noncomputable def pairAdd (g : Lp 𝕜 2 μ) : Lp 𝕜 2 μ →+ 𝕜 where
  toFun f := conj ⟪f, starLp g⟫_𝕜
  map_zero' := by simp
  map_add' f₁ f₂ := by rw [inner_add_left, map_add]

private theorem continuous_pairAdd (g : Lp 𝕜 2 μ) : Continuous (pairAdd μ g) := by
  change Continuous fun f : Lp 𝕜 2 μ => conj ⟪f, starLp g⟫_𝕜
  exact RCLike.continuous_conj.comp (continuous_id.inner continuous_const)

private theorem pairAdd_apply (g f : Lp 𝕜 2 μ) :
    pairAdd μ g f = ∫ y, (f : X → 𝕜) y * (g : X → 𝕜) y ∂μ := by
  change conj ⟪f, starLp g⟫_𝕜 = _
  rw [L2.inner_def]
  have hcongr : (∫ y, ⟪(f : X → 𝕜) y, (starLp g : X → 𝕜) y⟫_𝕜 ∂μ)
      = ∫ y, conj ((f : X → 𝕜) y * (g : X → 𝕜) y) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_starLp g] with y hy
    rw [RCLike.inner_apply, hy, map_mul, mul_comm]
  rw [hcongr, integral_conj, RCLike.conj_conj]

private theorem pairAdd_toLp_star (g : Lp 𝕜 2 μ) (n : d.ι) :
    pairAdd μ g (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))
      = ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 := by
  rw [pairAdd_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards
    [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (star (d.eigfun n)),
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n)] with y h1 h2
  rw [h1, h2, RCLike.inner_apply, mul_comm]
  simp [RCLike.star_def]

/-- **Master identity for the square-root operator**: `T_S g (x) = ∑ₙ √λₙ eₙ(x) ⟪eₙ, g⟫`,
the scalar series obtained by pushing the `L²`-convergent series defining the section
through the bilinear pairing against `g`. -/
private theorem hasSum_integralOp_sqrtSymbol (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (g : Lp 𝕜 2 μ) (x : X) :
    HasSum (fun n => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜)
      (integralOp μ (sqrtSymbol d) g x) := by
  have h := (hasSum_sqrtSectionLp d hK x).map (pairAdd μ g) (continuous_pairAdd g)
  have hval : ∀ n : d.ι,
      pairAdd μ g ((((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))
      = ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 := by
    intro n
    change conj ⟪_ • _, starLp g⟫_𝕜 = _
    rw [inner_smul_left, map_mul, RCLike.conj_conj]
    change _ * (pairAdd μ g (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))) = _
    rw [pairAdd_toLp_star d g n]
  have hgoal : pairAdd μ g (sqrtSectionLp d x) = integralOp μ (sqrtSymbol d) g x := by
    rw [pairAdd_apply]; rfl
  rw [← hgoal]
  exact h.congr_fun fun n => (hval n).symm

-- Off-diagonal `L²` pairing of two sections: `⟪S(x,·), S(x',·)⟫ = K(x', x)`.
private theorem inner_sqrtSectionLp (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure] (x x' : X) :
    ⟪sqrtSectionLp d x, sqrtSectionLp d x'⟫_𝕜 = K x' x := by
  have h := (hasSum_sqrtSectionLp d hK x').mapL (innerSL 𝕜 (sqrtSectionLp d x))
  have hval : ∀ n : d.ι,
      (d.eigval n : 𝕜) * (d.eigfun n x' * conj (d.eigfun n x))
      = ⟪sqrtSectionLp d x, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x') •
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))⟫_𝕜 := by
    intro n
    rw [inner_smul_right, ← inner_conj_symm, inner_toLp_star_sqrtSectionLp d hK x n, map_mul,
      RCLike.conj_ofReal]
    have hsq : ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)
        = (d.eigval n : 𝕜) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (d.eigval_pos n).le]
    calc (d.eigval n : 𝕜) * (d.eigfun n x' * conj (d.eigfun n x))
        = (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)) *
            (d.eigfun n x' * conj (d.eigfun n x)) := by rw [hsq]
      _ = _ := by ring
  exact (((d.hasSum_kernel hK x' x).congr_fun fun n => (hval n).symm).unique h).symm

-- The `L²`-section map is continuous (same proof shape as `continuous_kernelFun`: the
-- squared increment is the four-term kernel combination).
private theorem continuous_sqrtSectionLp (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure] :
    Continuous fun x : X => sqrtSectionLp d x := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have heq : (fun x : X => ‖sqrtSectionLp d x - sqrtSectionLp d x₀‖)
      = fun x : X => Real.sqrt (RCLike.re (K x x - K x₀ x - K x x₀ + K x₀ x₀)) := by
    funext x
    rw [← Real.sqrt_sq (norm_nonneg (sqrtSectionLp d x - sqrtSectionLp d x₀))]
    congr 1
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), inner_sub_sub_self, inner_sqrtSectionLp d hK x x,
      inner_sqrtSectionLp d hK x x₀, inner_sqrtSectionLp d hK x₀ x,
      inner_sqrtSectionLp d hK x₀ x₀]
  have hcont : Continuous fun x : X => RCLike.re (K x x - K x₀ x - K x x₀ + K x₀ x₀) :=
    RCLike.continuous_re.comp'
      ((((hKc.comp' (continuous_id.prodMk continuous_id)).sub
        (hKc.comp' (continuous_const.prodMk continuous_id))).sub
        (hKc.comp' (continuous_id.prodMk continuous_const))).add continuous_const)
  change Filter.Tendsto (fun x : X => sqrtSectionLp d x) (nhds x₀) (nhds (sqrtSectionLp d x₀))
  rw [tendsto_iff_norm_sub_tendsto_zero, heq]
  have hct : Filter.Tendsto
      (fun x : X => Real.sqrt (RCLike.re (K x x - K x₀ x - K x x₀ + K x₀ x₀))) (nhds x₀)
      (nhds (Real.sqrt (RCLike.re (K x₀ x₀ - K x₀ x₀ - K x₀ x₀ + K x₀ x₀)))) :=
    (Real.continuous_sqrt.comp' hcont).continuousAt
  simpa using hct

/-- The square-root symbol has square-integrable sections:
`∫ ‖S(x,y)‖² dμ(y) = ∑ₙ λₙ ‖eₙ(x)‖² = K(x,x)`. -/
-- With the `L²`-limit definition of `sqrtSymbol` (this revision) the sections are `Lp`
-- representatives by construction: `Lp.memLp (sqrtSectionLp d x)`.
theorem isL2Symbol_sqrtSymbol (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure] :
    IsL2Symbol μ (sqrtSymbol d) := fun x => Lp.memLp (sqrtSectionLp d x)

-- `T_S g` is a continuous function of `x` (the section map is continuous and the pairing
-- against `g` is a continuous functional).
private theorem integralOp_sqrtSymbol_eq (g : Lp 𝕜 2 μ) :
    integralOp μ (sqrtSymbol d) g = fun x => pairAdd μ g (sqrtSectionLp d x) := by
  funext x
  rw [pairAdd_apply]
  rfl

private theorem continuous_integralOp_sqrtSymbol (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure] (g : Lp 𝕜 2 μ) : Continuous (integralOp μ (sqrtSymbol d) g) := by
  rw [integralOp_sqrtSymbol_eq d g]
  exact (continuous_pairAdd g).comp (continuous_sqrtSectionLp d hK)

private theorem norm_integralOp_sqrtSymbol_le (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    {M : ℝ} (hM : ∀ x y : X, ‖K x y‖ ≤ M) (g : Lp 𝕜 2 μ) (x : X) :
    ‖integralOp μ (sqrtSymbol d) g x‖ ≤ Real.sqrt M * ‖g‖ := by
  have h1 : ‖integralOp μ (sqrtSymbol d) g x‖ ≤ ‖sqrtSectionLp d x‖ * ‖g‖ := by
    have h0 : integralOp μ (sqrtSymbol d) g x = conj ⟪sqrtSectionLp d x, starLp g⟫_𝕜 :=
      congrFun (integralOp_sqrtSymbol_eq d g) x
    rw [h0, RCLike.norm_conj, ← norm_starLp g]
    exact norm_inner_le_norm _ _
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  have h2 : ‖sqrtSectionLp d x‖ ^ 2 ≤ M := by
    rw [norm_sq_sqrtSectionLp d hK x]
    exact le_trans (RCLike.re_le_norm _) (hM x x)
  calc ‖sqrtSectionLp d x‖ = Real.sqrt (‖sqrtSectionLp d x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt M := Real.sqrt_le_sqrt h2

/-- The image of the square-root operator is square-integrable. -/
theorem memLp_integralOp_sqrtSymbol (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (g : Lp 𝕜 2 μ) :
    MemLp (integralOp μ (sqrtSymbol d) g) 2 μ := by
  -- Route: `norm_integralOp_le` (IntegralOperator) plus `Lp.norm_le_of_ae_bound`, as in
  -- `memLp_integralOp_of_continuous` (Mercer/Defs); the pointwise bound
  -- `‖sqrtSectionLp d x‖ ≤ √(re K(x,x))` comes from the orthogonal series
  -- (`∑ₙ λₙ ‖eₙ(x)‖² ≤ re K(x,x)`, the diagonal of the PROVED `hasSum_kernel`).
  obtain ⟨M, hM0, hM⟩ := exists_bnd (K := K) hKc
  exact MemLp.of_bound (continuous_integralOp_sqrtSymbol d hK g).aestronglyMeasurable
    (Real.sqrt M * ‖g‖)
    (Filter.Eventually.of_forall fun x => norm_integralOp_sqrtSymbol_le d hK hM g x)

variable (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]

/-- **The square root of the Mercer operator**: the bounded integral operator with
symbol `sqrtSymbol d`, i.e. `T_S g = ∑ₙ √λₙ ⟪eₙ, g⟫ eₙ`. -/
noncomputable def sqrtCLM : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun g => (memLp_integralOp_sqrtSymbol d hK g).toLp _
      -- Route: linearity via `integralOp_eq_inner` plus `inner_add_right`/
      -- `inner_smul_right` verbatim as in `mercerCLM` (Mercer/Defs); the bound is
      -- `‖T_S g‖ ≤ √(sup_x re K(x,x)) · √μ(X) · ‖g‖`.
      map_add' := by
        intro g h
        rw [← MemLp.toLp_add]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 (Filter.Eventually.of_forall fun x => ?_)
        change integralOp μ (sqrtSymbol d) (g + h) x
            = integralOp μ (sqrtSymbol d) g x + integralOp μ (sqrtSymbol d) h x
        rw [integralOp_eq_inner _ (isL2Symbol_sqrtSymbol d hK),
          integralOp_eq_inner _ (isL2Symbol_sqrtSymbol d hK),
          integralOp_eq_inner _ (isL2Symbol_sqrtSymbol d hK), inner_add_right]
      map_smul' := by
        intro c g
        change (memLp_integralOp_sqrtSymbol d hK (c • g)).toLp _
          = c • (memLp_integralOp_sqrtSymbol d hK g).toLp _
        rw [← MemLp.toLp_const_smul]
        refine (MemLp.toLp_eq_toLp_iff _ _).2 (Filter.Eventually.of_forall fun x => ?_)
        change integralOp μ (sqrtSymbol d) (c • g) x = c • integralOp μ (sqrtSymbol d) g x
        rw [integralOp_eq_inner _ (isL2Symbol_sqrtSymbol d hK),
          integralOp_eq_inner _ (isL2Symbol_sqrtSymbol d hK), inner_smul_right, smul_eq_mul] }
    (by
      obtain ⟨M, hM0, hM⟩ := exists_bnd (K := K) hKc
      refine ⟨(measureUnivNNReal μ : ℝ) ^ ((2 : ENNReal).toReal)⁻¹ * Real.sqrt M, fun g => ?_⟩
      rw [mul_assoc]
      refine Lp.norm_le_of_ae_bound (by positivity) ?_
      filter_upwards [MemLp.coeFn_toLp (μ := μ) (p := 2)
        (memLp_integralOp_sqrtSymbol d hK g)] with x hx
      change ‖(((memLp_integralOp_sqrtSymbol d hK g).toLp (integralOp μ (sqrtSymbol d) g) :
        Lp 𝕜 2 μ) : X → 𝕜) x‖ ≤ _
      rw [hx]
      exact norm_integralOp_sqrtSymbol_le d hK hM g x)

-- Coefficientwise description of a finite `L²` combination.
omit [μ.IsOpenPosMeasure] in
private theorem coeFn_finset_sum_smul {ι : Type*} (s : Finset ι) (c : ι → 𝕜)
    (F : ι → Lp 𝕜 2 μ) :
    ((∑ i ∈ s, c i • F i : Lp 𝕜 2 μ) : X → 𝕜)
      =ᵐ[μ] fun x => ∑ i ∈ s, c i * (F i : X → 𝕜) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! Lp.coeFn_zero 𝕜 2 μ
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (c a • F a) (∑ i ∈ t, c i • F i),
        Lp.coeFn_smul (c a) (F a), ih] with x h1 h2 h3
      rw [h1]
      simp only [Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_insert ha]

-- Pythagoras against a finite piece of an orthonormal family whose coefficients are the
-- Fourier coefficients of `u`.
omit [μ.IsOpenPosMeasure] in
private theorem norm_sq_sub_partial_aux {ι : Type*} (u : Lp 𝕜 2 μ) (v : ι → Lp 𝕜 2 μ)
    (hv : Orthonormal 𝕜 v) (c : ι → 𝕜) (hcu : ∀ n, ⟪v n, u⟫_𝕜 = c n) (s : Finset ι) :
    ‖u - ∑ n ∈ s, c n • v n‖ ^ 2 = ‖u‖ ^ 2 - ∑ n ∈ s, ‖c n‖ ^ 2 := by
  classical
  have hvv : ∀ m : ι, ⟪v m, v m⟫_𝕜 = 1 := by
    intro m
    rw [inner_self_eq_norm_sq_to_K, hv.1 m]
    norm_num
  have hvP : ∀ m ∈ s, ⟪v m, ∑ n ∈ s, c n • v n⟫_𝕜 = c m := by
    intro m hm
    rw [inner_sum, Finset.sum_eq_single m]
    · rw [inner_smul_right, hvv m, mul_one]
    · intro n _ hnm
      rw [inner_smul_right, hv.2 (Ne.symm hnm), mul_zero]
    · intro hms
      exact absurd hm hms
  have hPS : ⟪∑ n ∈ s, c n • v n, u⟫_𝕜 = ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : 𝕜) := by
    rw [sum_inner, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_smul_left, hcu n, RCLike.conj_mul, ← RCLike.ofReal_pow]
  have hPP : ⟪∑ n ∈ s, c n • v n, ∑ n ∈ s, c n • v n⟫_𝕜 = ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : 𝕜) := by
    rw [sum_inner, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [inner_smul_left, hvP n hn, RCLike.conj_mul, ← RCLike.ofReal_pow]
  have hSP : ⟪u, ∑ n ∈ s, c n • v n⟫_𝕜 = ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← inner_conj_symm, hPS, RCLike.conj_ofReal]
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), inner_sub_sub_self, hSP, hPS, hPP]
  have hsimp : ⟪u, u⟫_𝕜 - ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : 𝕜) - ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : 𝕜)
      + ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : 𝕜) = ⟪u, u⟫_𝕜 - ((∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) : 𝕜) := by
    ring
  rw [hsimp, map_sub, RCLike.ofReal_re, ← norm_sq_eq_re_inner (𝕜 := 𝕜)]

omit [μ.IsOpenPosMeasure] in
private theorem pairAdd_smul (g : Lp 𝕜 2 μ) (c : 𝕜) (u : Lp 𝕜 2 μ) :
    pairAdd μ g (c • u) = c * pairAdd μ g u := by
  change conj ⟪c • u, starLp g⟫_𝕜 = c * conj ⟪u, starLp g⟫_𝕜
  rw [inner_smul_left, map_mul, RCLike.conj_conj]

omit [μ.IsOpenPosMeasure] in
private theorem norm_pairAdd_le (g u : Lp 𝕜 2 μ) : ‖pairAdd μ g u‖ ≤ ‖u‖ * ‖g‖ := by
  change ‖conj ⟪u, starLp g⟫_𝕜‖ ≤ _
  rw [RCLike.norm_conj, ← norm_starLp g]
  exact norm_inner_le_norm _ _

-- The eigenfunctions have unit `L²` mass.
omit [μ.IsOpenPosMeasure] in
private theorem integral_normSq_eigfun' (n : d.ι) : ∫ z, ‖d.eigfun n z‖ ^ 2 ∂μ = 1 := by
  have h1 : ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n),
      ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq_to_K, d.orthonormal.1 n]
    norm_num
  rw [L2.inner_def] at h1
  have h2 : ((∫ z, ‖d.eigfun n z‖ ^ 2 ∂μ : ℝ) : 𝕜) = 1 := by
    rw [← h1, ← integral_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜)
      (d.eigfun n)] with z hz
    rw [hz, RCLike.inner_apply, RCLike.mul_conj, ← RCLike.ofReal_pow]
  exact_mod_cast h2

-- Continuous real functions on the compact base space are integrable.
omit [μ.IsOpenPosMeasure] in
private theorem integrable_of_cont_real {f : X → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => hC z (Set.mem_univ _)))

private theorem sqrtCLM_coeFn_ae (g : Lp 𝕜 2 μ) :
    (sqrtCLM d hK g : X → 𝕜) =ᵐ[μ] integralOp μ (sqrtSymbol d) g :=
  MemLp.coeFn_toLp (memLp_integralOp_sqrtSymbol d hK g)

-- The `L²` error of the `s`-th partial sum, controlled by the tail of the trace.
private theorem norm_partial_sub_le (g : Lp 𝕜 2 μ) (s : Finset d.ι) :
    ‖(∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)) - sqrtCLM d hK g‖
      ≤ ‖g‖ * Real.sqrt ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n) := by
  classical
  -- (1) the coefficientwise description of the difference
  have hcoe : (((∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)) - sqrtCLM d hK g : Lp 𝕜 2 μ) : X → 𝕜)
      =ᵐ[μ] fun x => (∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) * d.eigfun n x)
        - integralOp μ (sqrtSymbol d) g x := by
    filter_upwards [Lp.coeFn_sub (∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)) (sqrtCLM d hK g),
      coeFn_finset_sum_smul s (fun n => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜)
        (fun n => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
      sqrtCLM_coeFn_ae d hK g,
      (Filter.eventually_all_finset s).2 (fun n _ =>
        ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n))]
      with x h1 h2 h3 h4
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h3]
    congr 1
    exact Finset.sum_congr rfl fun n hn => by rw [h4 n hn]
  -- (2) the pointwise bound through the bilinear pairing
  have hpt : ∀ x : X, ‖(∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) * d.eigfun n x)
        - integralOp μ (sqrtSymbol d) g x‖ ^ 2
      ≤ (RCLike.re (K x x) - ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2) * ‖g‖ ^ 2 := by
    intro x
    have hP : pairAdd μ g (∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) •
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))
        = ∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
            ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) * d.eigfun n x := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [pairAdd_smul, pairAdd_toLp_star d g n]
      ring
    have hS : pairAdd μ g (sqrtSectionLp d x) = integralOp μ (sqrtSymbol d) g x :=
      (congrFun (integralOp_sqrtSymbol_eq d g) x).symm
    have hdiff : (∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) * d.eigfun n x)
        - integralOp μ (sqrtSymbol d) g x
        = pairAdd μ g ((∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))) - sqrtSectionLp d x) := by
      rw [map_sub, hP, hS]
    have hps : ‖sqrtSectionLp d x - ∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
          d.eigfun n x) • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n))‖ ^ 2
        = RCLike.re (K x x) - ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 := by
      rw [norm_sq_sub_partial_aux (sqrtSectionLp d x)
        (fun n => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))
        (orthonormal_toLp_star d)
        (fun n => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x)
        (fun n => inner_toLp_star_sqrtSectionLp d hK x n) s, norm_sq_sqrtSectionLp d hK x]
      congr 1
      exact Finset.sum_congr rfl fun n _ => norm_sq_sqrtCoeff d n x
    rw [hdiff]
    have hb := norm_pairAdd_le g ((∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
      d.eigfun n x) • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))
      - sqrtSectionLp d x)
    rw [norm_sub_rev] at hb
    have hsq := mul_self_le_mul_self (norm_nonneg _) hb
    nlinarith [hps, norm_nonneg g, norm_nonneg (sqrtSectionLp d x -
      ∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (star (d.eigfun n)))]
  -- (3) integrate the pointwise bound
  have hcontK : Continuous fun x : X => RCLike.re (K x x) :=
    (RCLike.continuous_re (K := 𝕜)).comp' (hKc.comp' (continuous_id.prodMk continuous_id))
  have hcontS : Continuous fun x : X => ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 :=
    continuous_finset_sum s fun n _ =>
      continuous_const.mul (((d.eigfun n).continuous.norm).pow 2)
  have hintb : Integrable (fun x : X =>
      (RCLike.re (K x x) - ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2) * ‖g‖ ^ 2) μ :=
    (integrable_of_cont_real (hcontK.sub hcontS)).mul_const _
  have hintegral : (∫ x, (RCLike.re (K x x) - ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2)
        * ‖g‖ ^ 2 ∂μ)
      = ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n) * ‖g‖ ^ 2 := by
    rw [integral_mul_const, integral_sub (integrable_of_cont_real hcontK)
      (integrable_of_cont_real hcontS)]
    congr 2
    rw [integral_finset_sum s fun n _ =>
      (integrable_of_cont_real (((d.eigfun n).continuous.norm).fun_pow 2)).const_mul _]
    exact Finset.sum_congr rfl fun n _ => by
      rw [integral_const_mul, integral_normSq_eigfun' d n, mul_one]
  have hnorm : ‖(∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)) - sqrtCLM d hK g‖ ^ 2
      ≤ ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n) * ‖g‖ ^ 2 := by
    rw [norm_sq_eq_integral, ← hintegral]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hintb ?_
    filter_upwards [hcoe] with x hx
    rw [hx]
    exact hpt x
  -- (4) take square roots
  have hR0 : 0 ≤ (∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n := by
    have := sum_le_hasSum s (fun n _ => (d.eigval_pos n).le) (d.hasSum_eigval hK)
    linarith
  have hsq : (‖g‖ * Real.sqrt ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n)) ^ 2
      = ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n) * ‖g‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR0]
    ring
  calc ‖(∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)) - sqrtCLM d hK g‖
      = Real.sqrt (‖(∑ n ∈ s, (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)) - sqrtCLM d hK g‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖g‖ *
          Real.sqrt ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n)) ^ 2) := by
        rw [hsq]; exact Real.sqrt_le_sqrt hnorm
    _ = ‖g‖ * Real.sqrt ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n) :=
        Real.sqrt_sq (by positivity)

/-- Diagonalization of the square root: `T_S g = ∑ₙ √λₙ ⟪eₙ, g⟫ eₙ`. -/
theorem sqrtCLM_hasSum (g : Lp 𝕜 2 μ) :
    HasSum
      (fun n => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) •
        (⟪ContinuousMap.toLp 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 •
          ContinuousMap.toLp 2 μ 𝕜 (d.eigfun n)))
      (sqrtCLM d hK g) := by
  -- Route (TRUE after the `L²`-limit redefinition of `sqrtSymbol`, this revision):
  -- `integralOp μ (sqrtSymbol d) g x = ⟪star-section, g⟫`; expand `sqrtSectionLp` through
  -- the continuous pairing (`HasSum.mapL` of `innerSL`), identify coefficientwise with
  -- `∑ₙ √λₙ ⟪eₙ, g⟫ eₙ(x)` and lift the `L²`-convergent series through `MemLp.toLp`.
  classical
  have hrw : (fun n : d.ι => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) •
        (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 •
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)))
      = fun n : d.ι => (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
          ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n) := by
    funext n
    rw [smul_smul]
  rw [hrw, HasSum, tendsto_iff_norm_sub_tendsto_zero]
  have htail : Filter.Tendsto
      (fun s : Finset d.ι =>
        ‖g‖ * Real.sqrt ((∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n))
      Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun s : Finset d.ι => ∑ n ∈ s, d.eigval n) Filter.atTop
        (nhds (∫ x, RCLike.re (K x x) ∂μ)) := d.hasSum_eigval hK
    have h2 : Filter.Tendsto
        (fun s : Finset d.ι => (∫ x, RCLike.re (K x x) ∂μ) - ∑ n ∈ s, d.eigval n)
        Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun _ : Finset d.ι => (∫ x, RCLike.re (K x x) ∂μ))
          Filter.atTop (nhds (∫ x, RCLike.re (K x x) ∂μ)) := tendsto_const_nhds
      simpa using h0.sub h1
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h3
    simpa using h3.const_mul ‖g‖
  exact squeeze_zero (fun s => norm_nonneg _) (fun s => norm_partial_sub_le d hK g s) htail

/-- The square root is a positive operator. -/
theorem sqrtCLM_isPositive : (sqrtCLM d hK).IsPositive := by
  -- OPEN.  Statement TRUE (vacuously so under the frozen `tsum` definition, where the
  -- operator is `0`).  With the `L²`-limit repair of `sqrtSymbol` it is immediate from
  -- `sqrtCLM_hasSum`: `⟪g, T_S g⟫ = ∑ₙ √λₙ ‖⟪eₙ, g⟫‖² ≥ 0`, and symmetry by the same
  -- uniqueness-of-sums argument used in `isPositive_mercerCLM`.
  have key : ∀ h g : Lp 𝕜 2 μ,
      HasSum (fun n : d.ι => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 *
          ⟪h, ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)⟫_𝕜))
        ⟪h, sqrtCLM d hK g⟫_𝕜 := by
    intro h g
    refine ((sqrtCLM_hasSum d hK g).mapL (innerSL 𝕜 h)).congr_fun fun n => ?_
    change _ = ⟪h, ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) •
      (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n))⟫_𝕜
    rw [inner_smul_right, inner_smul_right]
  refine ⟨fun h g => ?_, fun g => ?_⟩
  · simp only [ContinuousLinearMap.coe_coe]
    have h1 := key h g
    have h2 : HasSum (fun n : d.ι => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 *
          ⟪h, ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)⟫_𝕜))
        (conj ⟪g, sqrtCLM d hK h⟫_𝕜) := by
      refine ((key g h).map ((starRingEnd 𝕜).toAddMonoidHom)
        RCLike.continuous_conj).congr_fun fun n => ?_
      change _ = conj (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), h⟫_𝕜 *
          ⟪g, ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)⟫_𝕜))
      rw [map_mul, map_mul, RCLike.conj_ofReal, inner_conj_symm, inner_conj_symm]
      ring
    rw [h1.unique h2, inner_conj_symm]
  · have h2 : HasSum (fun n : d.ι => Real.sqrt (d.eigval n) *
        ‖⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜‖ ^ 2)
        (RCLike.re ⟪g, sqrtCLM d hK g⟫_𝕜) := by
      refine ((key g g).map (RCLike.reCLM (K := 𝕜)).toLinearMap.toAddMonoidHom
        RCLike.reCLM.continuous).congr_fun fun n => ?_
      change _ = RCLike.re (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 *
          ⟪g, ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)⟫_𝕜))
      rw [← inner_conj_symm g (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
        RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
    have h3 : (0 : ℝ) ≤ RCLike.re ⟪g, sqrtCLM d hK g⟫_𝕜 := by
      have hs := sum_le_hasSum (∅ : Finset d.ι)
        (fun n _ => mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) h2
      simpa using hs
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
    exact h3

/-- **`T_S` squares to `T_K`**: `T_S ∘ T_S = T_K`. -/
theorem sqrtCLM_comp_self : (sqrtCLM d hK).comp (sqrtCLM d hK) = mercerCLM μ hKc := by
  -- Route (TRUE after the `L²`-limit redefinition, this revision): the proof is
  -- `sqrtCLM_hasSum` twice plus `d.opExpansion`: both sides send `g` to
  -- `∑ₙ λₙ ⟪eₙ, g⟫ eₙ`, and `HasSum.unique` in `L²` plus orthonormality closes it.
  classical
  have hone : ∀ m : d.ι, ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m),
      ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m)⟫_𝕜 = 1 := by
    intro m
    rw [inner_self_eq_norm_sq_to_K, d.orthonormal.1 m]
    norm_num
  refine ContinuousLinearMap.ext fun g => ?_
  have hinner : ∀ n : d.ι, ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), sqrtCLM d hK g⟫_𝕜
      = ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 := by
    intro n
    have h := (sqrtCLM_hasSum d hK g).mapL
      (innerSL 𝕜 (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)))
    have hite : HasSum (fun m : d.ι => ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n),
        ((Real.sqrt (d.eigval m) : ℝ) : 𝕜) •
          (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m), g⟫_𝕜 •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m))⟫_𝕜)
        (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) := by
      refine (hasSum_ite_eq n (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) *
        ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜)).congr_fun fun m => ?_
      rw [inner_smul_right, inner_smul_right]
      by_cases hmn : m = n
      · subst hmn
        rw [if_pos rfl, hone m, mul_one]
      · rw [if_neg hmn, d.orthonormal.2 (Ne.symm hmn), mul_zero, mul_zero]
    exact h.unique hite
  have h2 : HasSum (fun n : d.ι => (d.eigval n : 𝕜) •
      (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)))
      (sqrtCLM d hK (sqrtCLM d hK g)) := by
    refine (sqrtCLM_hasSum d hK (sqrtCLM d hK g)).congr_fun fun n => ?_
    rw [hinner n, smul_smul, smul_smul]
    congr 1
    rw [← mul_assoc, ← RCLike.ofReal_mul, Real.mul_self_sqrt (d.eigval_pos n).le]
  rw [ContinuousLinearMap.comp_apply]
  exact h2.unique (d.opExpansion g)

omit [μ.IsOpenPosMeasure] in
private theorem inner_starLp (u v : Lp 𝕜 2 μ) : ⟪starLp u, starLp v⟫_𝕜 = conj ⟪u, v⟫_𝕜 := by
  rw [L2.inner_def, L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_starLp u, coeFn_starLp v] with y h1 h2
  rw [h1, h2, RCLike.inner_apply, RCLike.inner_apply]
  simp

private theorem symbolConjLp_sqrt (x : X) :
    symbolConjLp μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) x = starLp (sqrtSectionLp d x) :=
  rfl

include hK in
-- **`S □ S* = K`**: the box square of the square-root symbol is the kernel itself.
private theorem boxProd_sqrtSymbol (x z : X) :
    boxProd μ (sqrtSymbol d) (symbolAdjoint (sqrtSymbol d)) x z = K x z := by
  rw [boxProd_symbolAdjoint_eq_featureKernel (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK)]
  change ⟪symbolConjLp μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) x,
    symbolConjLp μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) z⟫_𝕜 = K x z
  rw [symbolConjLp_sqrt d hK x, symbolConjLp_sqrt d hK z, inner_starLp,
    inner_sqrtSectionLp d hK x z]
  exact hK.isKernelFun.conj_symm z x

-- The eigenvalue equation in `L²`.
omit [μ.IsOpenPosMeasure] in
private theorem mercerCLM_eigfun (j : d.ι) :
    mercerCLM μ hKc (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j))
      = (d.eigval j : 𝕜) • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j) := by
  refine Lp.ext ?_
  filter_upwards [mercerCLM_coeFn_ae hKc (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j)),
    Lp.coeFn_smul ((d.eigval j : 𝕜)) (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j)),
    ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun j)] with z h1 h2 h3
  rw [h1, h2, Pi.smul_apply, smul_eq_mul, h3, d.eigen_eq j z]

include hK in
-- The range space of the square-root symbol has reproducing kernel `K`.
private theorem rangeSpaceScalarKernel_sqrt :
    rangeSpaceScalarKernel μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) = K := by
  funext x z
  rw [rangeSpace_scalarKernel]
  exact boxProd_sqrtSymbol d hK x z

/-- **`range T_S = H(K)`**: the square-root operator maps `L²(X, μ)` onto exactly the
functions of the (measure-independent!) RKHS of `K`. -/
theorem range_integralOp_sqrtSymbol_eq
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) :
    Set.range (integralOp μ (sqrtSymbol d))
      = Set.range fun f : H => (f : X → 𝕜) := by
  -- Route (TRUE after the `L²`-limit redefinition, this revision): the left
  -- side is `{0}` and `H(K) ≠ {0}`.  After the `L²`-limit repair the route is:
  -- `S □ S* = K` (from `sqrtCLM_comp_self` and Hermitian symmetry of `S`), so
  -- `RangeSpace.lean`'s range space of `S` is an RKHS with kernel `K`, and
  -- `Uniqueness.range_coe_eq_of_scalarKernel_eq` transports the range to `H`.
  have hK : IsMercerKernel 𝕜 K := ⟨hKc, by rw [← hKH]; exact isKernelFun_scalarKernel (H := H)⟩
  have hS : IsL2Symbol μ (sqrtSymbol d) := isL2Symbol_sqrtSymbol d hK
  have hker : rangeSpaceScalarKernel μ (sqrtSymbol d) hS = scalarKernel (X := X) H := by
    funext x z
    rw [hKH, rangeSpace_scalarKernel]
    exact boxProd_sqrtSymbol d hK x z
  letI := rangeSpaceRKHS μ (sqrtSymbol d) hS
  rw [range_integralOp_eq_range_coe (sqrtSymbol d) hS]
  exact @range_coe_eq_of_scalarKernel_eq 𝕜 _ X (rangeSpaceCarrier μ (sqrtSymbol d) hS) _ _
    (rangeSpaceCompleteSpace μ (sqrtSymbol d) hS) H _ _ _
    (rangeSpaceRKHS μ (sqrtSymbol d) hS) _ hker

/-- **`T_S` is an isometry of `(ker T_K)ᗮ` onto `H(K)`**: for `g ⊥ ker T_K`, the
function `T_S g` is realized in `H` with equal norm. -/
theorem sqrtCLM_isometry_on_ker_orthogonal
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K)
    {g : Lp 𝕜 2 μ} (hg : g ∈ (LinearMap.ker (mercerCLM μ hKc).toLinearMap)ᗮ) :
    ∃ f : H, (f : X → 𝕜) = integralOp μ (sqrtSymbol d) g ∧ ‖f‖ = ‖g‖ := by
  -- Route (TRUE after the `L²`-limit redefinition, this revision): same route as
  -- `range_integralOp_sqrtSymbol_eq`, plus the fact that the range space's norm agrees
  -- with `‖g‖` on `(ker T_S)ᗮ = (ker T_K)ᗮ` (`rangeSpace_*`).
  have hK : IsMercerKernel 𝕜 K := ⟨hKc, by rw [← hKH]; exact isKernelFun_scalarKernel (H := H)⟩
  have hker : rangeSpaceScalarKernel μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK)
      = scalarKernel (X := X) H := by
    rw [hKH]
    exact rangeSpaceScalarKernel_sqrt d hK
  -- `ker T_K = (ker T_S) = (rangeSpaceCarrier)ᗮ`
  have hzero : ∀ g₀ : Lp 𝕜 2 μ,
      sqrtCLM d hK g₀ = 0 ↔ ∀ x, integralOp μ (sqrtSymbol d) g₀ x = 0 := by
    intro g₀
    constructor
    · intro h0 x
      have hae : integralOp μ (sqrtSymbol d) g₀ =ᵐ[μ] fun _ : X => (0 : 𝕜) := by
        filter_upwards [(sqrtCLM_coeFn_ae d hK g₀).symm,
          Lp.coeFn_zero (E := 𝕜) (p := 2) (μ := μ)] with a ha hb
        rw [ha, h0, hb]
        rfl
      exact congrFun ((Continuous.ae_eq_iff_eq (μ := μ)
        (continuous_integralOp_sqrtSymbol d hK g₀) continuous_const).mp hae) x
    · intro h0
      refine Lp.ext ?_
      filter_upwards [sqrtCLM_coeFn_ae d hK g₀, Lp.coeFn_zero (E := 𝕜) (p := 2) (μ := μ)]
        with a ha hb
      rw [ha, hb, h0 a]
      rfl
  have hkerEq : LinearMap.ker (mercerCLM μ hKc).toLinearMap
      = (rangeSpaceCarrier μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK))ᗮ := by
    have hstep : ∀ g₀ : Lp 𝕜 2 μ, mercerCLM μ hKc g₀ = 0 ↔ sqrtCLM d hK g₀ = 0 := by
      intro g₀
      constructor
      · intro h0
        have hsym := (sqrtCLM_isPositive d hK).1 g₀ (sqrtCLM d hK g₀)
        simp only [ContinuousLinearMap.coe_coe] at hsym
        have h2 : sqrtCLM d hK (sqrtCLM d hK g₀) = mercerCLM μ hKc g₀ := by
          rw [← ContinuousLinearMap.comp_apply, sqrtCLM_comp_self]
        have h1 : ⟪sqrtCLM d hK g₀, sqrtCLM d hK g₀⟫_𝕜 = 0 := by
          rw [hsym, h2, h0, inner_zero_right]
        exact inner_self_eq_zero.mp h1
      · intro h0
        rw [← sqrtCLM_comp_self d hK, ContinuousLinearMap.comp_apply, h0, map_zero]
    ext g₀
    rw [LinearMap.mem_ker]
    change (mercerCLM μ hKc).toLinearMap g₀ = 0 ↔ _
    rw [show (mercerCLM μ hKc).toLinearMap g₀ = mercerCLM μ hKc g₀ from rfl, hstep g₀,
      hzero g₀, Submodule.mem_orthogonal]
    constructor
    · intro h0 u hu
      have hle : rangeSpaceCarrier μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK)
          ≤ (𝕜 ∙ g₀)ᗮ := by
        refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        refine Submodule.mem_orthogonal_singleton_iff_inner_left.mpr ?_
        rw [← integralOp_eq_inner (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) g₀ x]
        exact h0 x
      exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hu)
    · intro h0 x
      rw [integralOp_eq_inner (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) g₀ x]
      refine h0 _ ?_
      have := (rangeSpaceKernelFun μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) x).2
      rwa [rangeSpace_kernelFun] at this
  have hgmem : g ∈ rangeSpaceCarrier μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) := by
    rw [hkerEq, Submodule.orthogonal_orthogonal_eq_closure] at hg
    exact Submodule.topologicalClosure_minimal _ le_rfl
      (Submodule.isClosed_topologicalClosure _) hg
  obtain ⟨e, he⟩ := @exists_isometryEquiv_of_scalarKernel_eq 𝕜 _ X
    (rangeSpaceCarrier μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK)) _ _
    (rangeSpaceCompleteSpace μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK)) H _ _ _
    (rangeSpaceRKHS μ (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK)) _ hker
  refine ⟨e ⟨g, hgmem⟩, funext fun x => ?_, ?_⟩
  · rw [he ⟨g, hgmem⟩ x]
    exact rangeSpace_apply (sqrtSymbol d) (isL2Symbol_sqrtSymbol d hK) ⟨g, hgmem⟩ x
  · exact e.norm_map ⟨g, hgmem⟩

/-- **`{√λₙ eₙ}` is an orthonormal basis of `H(K)`**: the rescaled eigenfunctions are
realized in `H`, are orthonormal there, and their span is dense. -/
theorem exists_orthonormalBasis_sqrt_eigfun
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) :
    ∃ b : d.ι → H,
      (∀ n, (b n : X → 𝕜) = fun x =>
        ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) ∧
      Orthonormal 𝕜 b ∧
      (Submodule.span 𝕜 (Set.range b)).topologicalClosure = ⊤ := by
  -- OPEN.  Statement TRUE and no longer blocked on the (false) `sqrtSymbol` route.
  -- Here `d` is mentioned in the statement, so `d` and `hKc` ARE in scope (unlike in
  -- `range_mercerCLM_subset` below); `hK` is not, but `IsMercerKernel 𝕜 K` is recovered
  -- as `⟨hKc, hKH ▸ isKernelFun_scalarKernel⟩`.  Complete route, in three steps:
  -- (1) *the members are in `H`*: for `h : Lp 𝕜 2 μ` the Bochner integral
  --     `∫ y, h y • kernelFun H y ∂μ : H` (integrable because `‖kernelFun H y‖` is
  --     bounded on the compact `X` by `continuous_kernelFun H` and `h ∈ L¹`) coerces to
  --     `x ↦ ∫ y, K x y * h y ∂μ = integralOp μ K h x`, by `inner_kernelFun` and
  --     `integral_inner`.  Taking `h := ContinuousMap.toLp 2 μ 𝕜 (d.eigfun m)` and using
  --     `d.eigen_eq` gives `λₘ • eₘ ∈ H`, hence `bₘ := (λₘ)^{-1/2} • (that element)`
  --     has coercion `x ↦ √λₘ eₘ(x)`.
  -- (2) *Parseval frame*: `MercerEigensystem.hasSum_kernel` (PROVED) rewritten through
  --     `hKH` is exactly the hypothesis of `isParsevalFrame_of_hasSum_scalarKernel`
  --     (Papadakis, PROVED), so `{bₙ}` is a Parseval frame of `H`.
  -- (3) *orthonormality and density*: frame reconstruction gives
  --     `b_j = ∑ᵢ ⟪bᵢ, b_j⟫ bᵢ` in `H`, hence pointwise; pairing with `conj (e_k(·))` and
  --     integrating against `μ` (legitimate by `L²`-convergence of the reconstruction and
  --     `d.orthonormal`) yields `√λ_j δ_{jk} = ⟪b_k, b_j⟫ √λ_k`, i.e. `⟪b_k, b_j⟫ = δ_{jk}`
  --     since `λ_k > 0`.  Density of the span is the frame property (a vector orthogonal
  --     to every `bᵢ` has norm `0` by the Parseval identity).
  classical
  have hK : IsMercerKernel 𝕜 K := ⟨hKc, by rw [← hKH]; exact isKernelFun_scalarKernel (H := H)⟩
  -- the eigenfunctions are orthogonal to `ker T_K`
  have hmem : ∀ j : d.ι, ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j)
      ∈ (LinearMap.ker (mercerCLM μ hKc).toLinearMap)ᗮ := by
    intro j
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu0 : mercerCLM μ hKc u = 0 := by
      rw [LinearMap.mem_ker] at hu
      exact hu
    have hsym := (isPositive_mercerCLM hK).1 u
      (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j))
    simp only [ContinuousLinearMap.coe_coe] at hsym
    rw [hu0, inner_zero_left, mercerCLM_eigfun d j, inner_smul_right] at hsym
    rcases mul_eq_zero.mp hsym.symm with h | h
    · exact absurd h (RCLike.ofReal_ne_zero.mpr (d.eigval_pos j).ne')
    · exact h
  -- the square root sends the `j`-th eigenfunction to `√λⱼ eⱼ`, everywhere
  have hval : ∀ (j : d.ι) (x : X),
      integralOp μ (sqrtSymbol d) (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j)) x
        = ((Real.sqrt (d.eigval j) : ℝ) : 𝕜) * d.eigfun j x := by
    intro j x
    refine (hasSum_integralOp_sqrtSymbol d hK
      (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun j)) x).unique ?_
    refine (hasSum_ite_eq j (((Real.sqrt (d.eigval j) : ℝ) : 𝕜) * d.eigfun j x)).congr_fun
      fun n => ?_
    by_cases hnj : n = j
    · subst hnj
      rw [if_pos rfl, inner_self_eq_norm_sq_to_K, d.orthonormal.1 n]
      norm_num
    · rw [if_neg hnj, d.orthonormal.2 hnj, mul_zero]
  choose b hb1 hb2 using fun j => sqrtCLM_isometry_on_ker_orthogonal d hKH (hmem j)
  have hbcoe : ∀ j : d.ι, (b j : X → 𝕜)
      = fun x => ((Real.sqrt (d.eigval j) : ℝ) : 𝕜) * d.eigfun j x := by
    intro j
    rw [hb1 j]
    funext x
    exact hval j x
  have hbnorm : ∀ j : d.ι, ‖b j‖ = 1 := by
    intro j
    rw [hb2 j]
    exact d.orthonormal.1 j
  -- Papadakis: the family is a Parseval frame
  have hframe : IsParsevalFrame 𝕜 b := by
    refine isParsevalFrame_of_hasSum_scalarKernel fun x y => ?_
    rw [hKH]
    refine (d.hasSum_kernel hK x y).congr_fun fun n => ?_
    rw [hbcoe n]
    change ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x *
      conj (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n y) = _
    rw [map_mul, RCLike.conj_ofReal]
    have hsq : ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)
        = (d.eigval n : 𝕜) := by
      rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (d.eigval_pos n).le]
    calc ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x *
          (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * conj (d.eigfun n y))
        = (((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)) *
            (d.eigfun n x * conj (d.eigfun n y)) := by ring
      _ = _ := by rw [hsq]
  refine ⟨b, hbcoe, ⟨hbnorm, fun i j hij => ?_⟩, ?_⟩
  · -- orthogonality: a unit-norm Parseval frame is orthonormal
    have hjj : ‖⟪b j, b j⟫_𝕜‖ ^ 2 = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hbnorm j]
      norm_num
    have hsum := sum_le_hasSum ({i, j} : Finset d.ι) (fun n _ => sq_nonneg _) (hframe (b j))
    rw [Finset.sum_pair hij, hjj, hbnorm j] at hsum
    have hle : ‖⟪b i, b j⟫_𝕜‖ ^ 2 ≤ 0 := by nlinarith
    have h0 : ‖⟪b i, b j⟫_𝕜‖ ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (⟪b i, b j⟫_𝕜)])
  · -- density: a vector orthogonal to the whole frame has norm zero
    have hbot : (Submodule.span 𝕜 (Set.range b))ᗮ = ⊥ := by
      refine Submodule.eq_bot_iff _ |>.2 fun v hv => ?_
      have hzero : ∀ i : d.ι, ⟪b i, v⟫_𝕜 = 0 := fun i =>
        hv _ (Submodule.subset_span ⟨i, rfl⟩)
      have hns : HasSum (fun _ : d.ι => (0 : ℝ)) (‖v‖ ^ 2) := by
        refine (hframe v).congr_fun fun i => ?_
        rw [hzero i]
        norm_num
      have : ‖v‖ ^ 2 = 0 := (hasSum_zero.unique hns).symm
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
    rw [← Submodule.orthogonal_orthogonal_eq_closure, hbot, Submodule.bot_orthogonal_eq_top]

/-- **Spectral membership test for `H(K)`**: a function lies in `H(K)` iff it is a
pointwise sum `∑ₙ aₙ eₙ` with `∑ₙ |aₙ|²/λₙ < ∞`. -/
theorem mem_range_coe_iff_summable
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (g₀ : X → 𝕜) :
    (∃ f : H, (f : X → 𝕜) = g₀)
      ↔ ∃ a : d.ι → 𝕜,
          Summable (fun n => ‖a n‖ ^ 2 / d.eigval n) ∧
          ∀ x, HasSum (fun n => a n * d.eigfun n x) (g₀ x) := by
  -- OPEN.  Statement TRUE, and independent of the false `sqrtSymbol` route.  Immediate
  -- from `exists_orthonormalBasis_sqrt_eigfun` (whose full route is documented there):
  -- expand `f` in the orthonormal basis `{√λₙ eₙ}` and set `aₙ := √λₙ ⟪bₙ, f⟫`, so that
  -- `∑ₙ ‖aₙ‖²/λₙ = ∑ₙ ‖⟪bₙ, f⟫‖² = ‖f‖²`; the pointwise `HasSum` is the RKHS
  -- norm-to-pointwise convergence (`Basic.lean`) applied to the partial sums.
  classical
  obtain ⟨b, hbcoe, hborth, hbdense⟩ := exists_orthonormalBasis_sqrt_eigfun d hKH
  have hsp : ⊤ ≤ (Submodule.span 𝕜 (Set.range b)).topologicalClosure := by rw [hbdense]
  have hframe : IsParsevalFrame 𝕜 b := by
    have hpf := HilbertBasis.isParsevalFrame (𝕜 := 𝕜) (HilbertBasis.mk hborth hsp)
    rwa [HilbertBasis.coe_mk] at hpf
  have hsqrt_ne : ∀ n : d.ι, ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) ≠ 0 := fun n =>
    RCLike.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (d.eigval_pos n))
  have hnormsq : ∀ (n : d.ι) (z : 𝕜),
      ‖((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * z‖ ^ 2 = d.eigval n * ‖z‖ ^ 2 := by
    intro n z
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (d.eigval_pos n).le]
  constructor
  · rintro ⟨f, rfl⟩
    refine ⟨fun n => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * ⟪b n, f⟫_𝕜, ?_, fun x => ?_⟩
    · refine (hframe f).summable.congr fun n => ?_
      have hne : d.eigval n ≠ 0 := (d.eigval_pos n).ne'
      rw [hnormsq n]
      field_simp
    · have hrec := (hframe.hasSum_reconstruction f).mapL (evalCLM 𝕜 H x)
      refine hrec.congr_fun fun n => ?_
      rw [map_smul, smul_eq_mul, evalCLM_apply,
        show (b n : X → 𝕜) x = ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x from
          congrFun (hbcoe n) x]
      ring
  · rintro ⟨a, hsum, hpt⟩
    have hcsum : Summable fun n : d.ι =>
        ‖a n / ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)‖ ^ 2 := by
      refine hsum.congr fun n => ?_
      rw [norm_div, div_pow, RCLike.norm_ofReal, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (d.eigval_pos n).le]
    have hiff := hborth.orthogonalFamily.summable_iff_norm_sq_summable
      (fun n : d.ι => a n / ((Real.sqrt (d.eigval n) : ℝ) : 𝕜))
    simp only [LinearIsometry.toSpanSingleton_apply] at hiff
    have hsummable : Summable fun n : d.ι =>
        (a n / ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)) • b n := hiff.mpr hcsum
    refine ⟨∑' n, (a n / ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)) • b n, funext fun x => ?_⟩
    have hx : HasSum (fun n : d.ι => a n * d.eigfun n x)
        (evalCLM 𝕜 H x (∑' n, (a n / ((Real.sqrt (d.eigval n) : ℝ) : 𝕜)) • b n)) := by
      refine (hsummable.hasSum.mapL (evalCLM 𝕜 H x)).congr_fun fun n => ?_
      have hne := hsqrt_ne n
      rw [map_smul, smul_eq_mul, evalCLM_apply,
        show (b n : X → 𝕜) x = ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x from
          congrFun (hbcoe n) x]
      field_simp
    exact hx.unique (hpt x)

include hKc in
/-- `range T_K ⊆ H(K)`: the (non-square-rooted) Mercer operator maps into the RKHS.
(The continuity of `K` is included: without any regularity of `K` the statement has no
access to a route — the section hypothesis `hKc` is pulled in explicitly.) -/
theorem range_mercerCLM_subset
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (g : Lp 𝕜 2 μ) :
    ∃ f : H, (f : X → 𝕜) = integralOp μ K g := by
  -- Route (Bochner-integral, written out by the round-2 session): from `hKH ▸ hKc` get
  -- `hKsc : Continuous (scalarKernel H ·×·)`, hence `continuous_kernelFun H hKsc` and a
  -- uniform bound `C` on `‖kernelFun H y‖` by compactness; `y ↦ g y • kernelFun H y` is
  -- integrable (`Integrable.mono'` against `‖g ·‖ * C`), and
  -- `f := ∫ y, g y • kernelFun H y ∂μ : H` satisfies
  -- `f x = ⟪kernelFun H x, f⟫ = ∫ y, g y * K x y ∂μ = integralOp μ K g x`
  -- by `inner_kernelFun` and `integral_inner`.
  haveI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  have hKsc : Continuous fun p : X × X => scalarKernel H p.1 p.2 := by
    simp only [hKH]; exact hKc
  have hkf : Continuous fun y : X => kernelFun (𝕜 := 𝕜) H y := continuous_kernelFun H hKsc
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hkf.continuousOn
  have hgi : Integrable (fun y => (g : X → 𝕜) y) μ := (Lp.memLp g).integrable (by norm_num)
  have hint : Integrable (fun y => (g : X → 𝕜) y • kernelFun (𝕜 := 𝕜) H y) μ := by
    refine Integrable.mono' (hgi.norm.mul_const C) ?_ ?_
    · exact (Lp.aestronglyMeasurable g).smul hkf.aestronglyMeasurable
    · filter_upwards with y
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC y (Set.mem_univ _)) (norm_nonneg _)
  refine ⟨∫ y, (g : X → 𝕜) y • kernelFun (𝕜 := 𝕜) H y ∂μ, funext fun x => ?_⟩
  rw [← inner_kernelFun x, ← integral_inner hint, integralOp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change ⟪kernelFun (𝕜 := 𝕜) H x, (g : X → 𝕜) y • kernelFun (𝕜 := 𝕜) H y⟫_𝕜
      = K x y * (g : X → 𝕜) y
  rw [inner_smul_right, ← scalarKernel_eq_inner, hKH, mul_comm]


end SquareRoot

end StatLean.NonparametricStatistics
