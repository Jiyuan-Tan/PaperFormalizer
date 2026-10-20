module
public import StatLean.NonparametricStatistics.RKHS.Mercer.Compact
public import StatLean.NonparametricStatistics.RKHS.Mercer.OperatorLemmas
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section

/-!
# Mercer's theorem

For a Mercer kernel `K` on a compact metric space `X` and a finite Borel measure `μ` of
full support, the integral operator `T_K` on `L²(X, μ)` admits a countable orthonormal
system of *continuous* eigenfunctions `e_n` with positive eigenvalues `λ_n` such that

* `T_K g = ∑ₙ λₙ ⟪eₙ, g⟫ eₙ` for every `g ∈ L²`;
* `K(x, y) = ∑ₙ λₙ eₙ(x) conj (eₙ(y))`, converging absolutely and uniformly on `X × X`.

The eigen-data is packaged in the structure `MercerEigensystem`.  Existence is obtained
from the spectral theorem for compact self-adjoint operators
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) applied to the
compact positive operator `T_K` (`isCompactOperator_mercerCLM`,
`isPositive_mercerCLM`): eigenspaces for distinct nonzero eigenvalues are
finite-dimensional and mutually orthogonal, eigenfunctions of nonzero eigenvalues have
continuous representatives (`e = λ⁻¹ T_K e` and `T_K` has continuous range), and the
uniform kernel expansion follows from the positivity of the residual kernels and Dini's
theorem (`tendstoUniformly_scalarKernel`).

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 11, §11.3, Theorem 11.15 (Mercer's theorem): countable orthonormal continuous
eigenfunctions with positive eigenvalues, the diagonalization of $T_K$, the pointwise and uniform
kernel expansions, and the trace formula $\sum_n \lambda_n = \int K(x,x)\,d\mu$.

**Proof formalization notes.** The eigensystem is produced from Mathlib's spectral theorem for
compact self-adjoint operators rather than the book's Arzelà–Ascoli iteration: countability of the
positive spectrum is built from total boundedness of the image of the unit ball (orthonormal
eigenvectors with eigenvalues $\ge \varepsilon$ are $\sqrt{2}\varepsilon$-separated), the index is
re-encoded into a `Type 0` via `Encodable`, and eigenfunctions get *continuous representatives*
$\lambda^{-1} T_K e$ — so the pointwise eigen-equation holds everywhere by construction, with full
support (`IsOpenPosMeasure`) used to identify the `L²` classes. The kernel expansion follows the
residual-kernel route: each residual $K_s = K - \sum_{n \in s}\lambda_n e_n \overline{e_n}$ has
positive operator, hence is a Mercer kernel by the (proved) converse, giving the diagonal bound;
residual operator norms tend to $0$, and a continuous kernel with vanishing operator vanishes
identically (averaging argument applied to $\pm K_\infty$).

**Bibliographic comments.** J. Mercer, *Functions of positive and negative type and
their connection with the theory of integral equations*, Philos. Trans. Roy. Soc. A
**209** (1909), 415–446; modern treatments in F. Smithies, *Integral Equations* (1958),
Ch. 7, and H. König, *Eigenvalue Distribution of Compact Operators* (Birkhäuser, 1986).
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace ENNReal Topology

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]

/-- **A Mercer eigensystem** for the kernel `K` against the measure `μ`: a countable
orthonormal family of continuous eigenfunctions of the integral operator `T_K` with
positive eigenvalues, through which `T_K` diagonalizes. -/
structure MercerEigensystem (μ : Measure X) [IsFiniteMeasure μ] (K : X → X → 𝕜)
    (hKc : Continuous fun p : X × X => K p.1 p.2) where
  /-- Index type of the eigensystem. -/
  ι : Type
  /-- The eigensystem is countable. -/
  countable : Countable ι
  /-- The eigenfunctions, as continuous functions on `X`. -/
  eigfun : ι → C(X, 𝕜)
  /-- The eigenvalues. -/
  eigval : ι → ℝ
  /-- Only the strictly positive part of the spectrum is enumerated.  Constitutive:
  the kernel of `T_K` contributes nothing to the expansion. -/
  eigval_pos : ∀ n, 0 < eigval n
  /-- The eigenfunctions are orthonormal in `L²(X, μ)`. -/
  orthonormal : Orthonormal 𝕜 fun n => ContinuousMap.toLp 2 μ 𝕜 (eigfun n)
  /-- The pointwise eigenfunction equation `(T_K eₙ)(x) = λₙ eₙ(x)` — everywhere, not
  just a.e., by continuity and full support. -/
  eigen_eq : ∀ n x,
    integralOp μ K (ContinuousMap.toLp 2 μ 𝕜 (eigfun n)) x = (eigval n : 𝕜) * eigfun n x
  /-- Diagonalization of `T_K`: `T_K g = ∑ₙ λₙ ⟪eₙ, g⟫ eₙ` for every `g ∈ L²(X, μ)`. -/
  opExpansion : ∀ g : Lp 𝕜 2 μ,
    HasSum
      (fun n => (eigval n : 𝕜) •
        (⟪ContinuousMap.toLp 2 μ 𝕜 (eigfun n), g⟫_𝕜 • ContinuousMap.toLp 2 μ 𝕜 (eigfun n)))
      (mercerCLM μ hKc g)

variable {μ : Measure X} [IsFiniteMeasure μ]

/-- `L²` of a finite Borel measure on a compact metric space is separable. -/
private theorem separableSpace_Lp (𝕜 : Type*) [RCLike 𝕜] {X : Type*} [MetricSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    TopologicalSpace.SeparableSpace (Lp 𝕜 2 μ) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance


/-- An orthonormal family in a separable inner product space has a countable index type. -/
private theorem countable_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [TopologicalSpace.SeparableSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal 𝕜 v) : Countable ι := by
  have hdist : ∀ i j : ι, i ≠ j → (1 : ℝ) ≤ dist (v i) (v j) := by
    intro i j hij
    have h : ‖v i - v j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq 𝕜, hv.1 i, hv.1 j, hv.2 hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j), h]
  refine Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (1 / 2)) ?_ (fun i => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  exact Metric.ball_disjoint_ball (by linarith [hdist i j hij])


open Module.End in
/-- Spectral data of a compact positive operator on a separable Hilbert space. -/
private theorem exists_eigen_data {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (T : E →L[𝕜] E) (hTc : IsCompactOperator T) (hTp : T.IsPositive) :
    ∃ (ι : Type) (v : ι → E) (lam : ι → ℝ),
      Countable ι ∧ (∀ n, 0 < lam n) ∧ Orthonormal 𝕜 v ∧
      (∀ n, T (v n) = (lam n : 𝕜) • v n) ∧
      ∀ g : E, HasSum (fun n => (lam n : 𝕜) • (⟪v n, g⟫_𝕜 • v n)) (T g) := by
  classical
  have hTs : (T : E →ₗ[𝕜] E).IsSymmetric := hTp.isSymmetric
  set Pos : Type := {r : ℝ // 0 < r ∧ HasEigenvalue (T : E →ₗ[𝕜] E) ((r : ℝ) : 𝕜)} with hPos
  set W : Pos → Submodule 𝕜 E := fun p => eigenspace (T : E →ₗ[𝕜] E) (((p : ℝ) : 𝕜)) with hW
  haveI hfd : ∀ p : Pos, FiniteDimensional 𝕜 (W p) := by
    intro p
    exact ContinuousLinearMap.finite_dimensional_eigenspace hTc _
      (RCLike.ofReal_ne_zero.mpr p.2.1.ne')
  set b : (p : Pos) → OrthonormalBasis (Fin (Module.finrank 𝕜 (W p))) 𝕜 (W p) :=
    fun p => stdOrthonormalBasis 𝕜 (W p) with hb
  set ι : Type := Σ p : Pos, Fin (Module.finrank 𝕜 (W p)) with hι
  set v : ι → E := fun n => ((b n.1 n.2 : W n.1) : E) with hv
  set lam : ι → ℝ := fun n => (n.1 : ℝ) with hlam
  -- orthonormality of the eigenvector family
  have hON : Orthonormal 𝕜 v := by
    constructor
    · rintro ⟨p, i⟩
      exact (b p).orthonormal.1 i
    · rintro ⟨p, i⟩ ⟨q, j⟩ hij
      by_cases hpq : p = q
      · subst hpq
        have hij' : i ≠ j := fun h => hij (by rw [h])
        have := (b p).orthonormal.2 hij'
        simpa using this
      · have hne : (((p : ℝ) : 𝕜)) ≠ (((q : ℝ) : 𝕜)) := fun h =>
          hpq (Subtype.ext (RCLike.ofReal_inj.mp h))
        exact hTs.orthogonalFamily_eigenspaces hne (b p i) (b q j)
  -- the eigenvalue equation
  have heig : ∀ n, T (v n) = ((lam n : ℝ) : 𝕜) • v n := by
    rintro ⟨p, i⟩
    exact mem_eigenspace_iff.mp (b p i).2
  -- the kernel of `T` and a Hilbert basis of it
  obtain ⟨N, hN⟩ : ∃ N : Submodule 𝕜 E, N = LinearMap.ker (T : E →ₗ[𝕜] E) := ⟨_, rfl⟩
  haveI hNc : CompleteSpace N := by rw [hN]; infer_instance
  obtain ⟨w, e, he⟩ := @exists_hilbertBasis 𝕜 _ N _ _ hNc
  set vAll : ι ⊕ w → E := Sum.elim v (fun k => ((e k : N) : E)) with hvAll
  -- membership facts
  have hvW : ∀ n : ι, v n ∈ W n.1 := fun n => (b n.1 n.2).2
  have heN : ∀ k : w, ((e k : N) : E) ∈ N := fun k => (e k).2
  have hkerN : ∀ k : w, T (((e k : N)) : E) = 0 := by
    intro k
    have h1 : ((e k : N) : E) ∈ LinearMap.ker (T : E →ₗ[𝕜] E) := by
      rw [← hN]; exact heN k
    exact h1
  have hONall : Orthonormal 𝕜 vAll := by
    constructor
    · rintro (n | k)
      · exact hON.1 n
      · exact e.orthonormal.1 k
    · rintro (n | k) (m | l) hne
      · exact hON.2 (fun h => hne (by rw [h]))
      · have h0 : (((n.1 : ℝ)) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr n.1.2.1.ne'
        have hmem : ((e l : N) : E) ∈ eigenspace (T : E →ₗ[𝕜] E) 0 := by
          rw [eigenspace_zero, ← hN]; exact heN l
        exact hTs.orthogonalFamily_eigenspaces h0 ⟨v n, hvW n⟩ ⟨_, hmem⟩
      · have h0 : (0 : 𝕜) ≠ (((m.1 : ℝ)) : 𝕜) :=
          (RCLike.ofReal_ne_zero.mpr m.1.2.1.ne').symm
        have hmem : ((e k : N) : E) ∈ eigenspace (T : E →ₗ[𝕜] E) 0 := by
          rw [eigenspace_zero, ← hN]; exact heN k
        exact hTs.orthogonalFamily_eigenspaces h0 ⟨_, hmem⟩ ⟨v m, hvW m⟩
      · exact e.orthonormal.2 (fun h => hne (by rw [h]))
  -- the combined family spans a dense subspace
  have hbot : (Submodule.span 𝕜 (Set.range vAll))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hperp : ∀ i, ⟪vAll i, g⟫_𝕜 = 0 := fun i =>
      (Submodule.mem_orthogonal _ _).mp hg _ (Submodule.subset_span ⟨i, rfl⟩)
    -- `g` is orthogonal to the whole kernel
    have hgN : ∀ y : N, ⟪(y : E), g⟫_𝕜 = 0 := by
      have hMle : (Submodule.span 𝕜 (Set.range (e : w → N))).topologicalClosure
          ≤ LinearMap.ker (((innerSL 𝕜 g).comp N.subtypeL : ↥N →L[𝕜] 𝕜) : ↥N →ₗ[𝕜] 𝕜) := by
        refine Submodule.topologicalClosure_minimal _ ?_
          (ContinuousLinearMap.isClosed_ker _)
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨k, rfl⟩
        have hz : ⟪((e k : N) : E), g⟫_𝕜 = 0 := hperp (Sum.inr k)
        simp only [SetLike.mem_coe, LinearMap.mem_ker]
        show ⟪g, ((e k : N) : E)⟫_𝕜 = 0
        rw [← inner_conj_symm, hz, map_zero]
      intro y
      have h2 := hMle (e.dense_span.ge (Submodule.mem_top (x := y)))
      rw [LinearMap.mem_ker] at h2
      have h3 : ⟪g, (y : E)⟫_𝕜 = 0 := h2
      rw [← inner_conj_symm, h3, map_zero]
    -- `g` is orthogonal to every eigenspace
    have hgE : ∀ (c : 𝕜) (y : E), y ∈ eigenspace (T : E →ₗ[𝕜] E) c → ⟪y, g⟫_𝕜 = 0 := by
      intro c y hy
      rcases eq_or_ne c 0 with rfl | hc
      · rw [eigenspace_zero, ← hN] at hy
        exact hgN ⟨y, hy⟩
      · by_cases hev : eigenspace (T : E →ₗ[𝕜] E) c = ⊥
        · rw [hev, Submodule.mem_bot] at hy
          simp [hy]
        · have hHE : HasEigenvalue (T : E →ₗ[𝕜] E) c := hev
          have hcr : (((RCLike.re c : ℝ)) : 𝕜) = c :=
            RCLike.conj_eq_iff_re.mp (hTs.conj_eigenvalue_eq_self hHE)
          have hnn : ∀ x : E, 0 ≤ RCLike.re ⟪x, (T : E →ₗ[𝕜] E) x⟫_𝕜 := by
            intro x
            rw [← hTs x x]
            exact hTp.2 x
          have hge : (0 : ℝ) ≤ RCLike.re c :=
            eigenvalue_nonneg_of_nonneg (by rw [hcr]; exact hHE) hnn
          have hrne : RCLike.re c ≠ 0 := by
            intro h0
            exact hc (by rw [← hcr, h0, RCLike.ofReal_zero])
          have hrpos : 0 < RCLike.re c := lt_of_le_of_ne hge (Ne.symm hrne)
          set p : Pos := ⟨RCLike.re c, hrpos, by rw [hcr]; exact hHE⟩ with hp
          have hyW : y ∈ W p := by rw [hW]; simpa [hp, hcr] using hy
          have hexp := (b p).sum_repr ⟨y, hyW⟩
          have hy' : y = ∑ i, ((b p).repr ⟨y, hyW⟩ i) • v ⟨p, i⟩ := by
            have := congrArg (fun z : W p => (z : E)) hexp
            simpa using this.symm
          rw [hy', sum_inner]
          refine Finset.sum_eq_zero fun i _ => ?_
          have hI : ⟪v ⟨p, i⟩, g⟫_𝕜 = 0 := hperp (Sum.inl ⟨p, i⟩)
          rw [inner_smul_left, hI, mul_zero]
    -- conclude via the spectral theorem
    have hle : (⨆ c, eigenspace (T : E →ₗ[𝕜] E) c) ≤ (𝕜 ∙ g)ᗮ := by
      refine iSup_le fun c => ?_
      intro y hy
      rw [Submodule.mem_orthogonal]
      intro u hu
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [inner_smul_left]
      have : ⟪g, y⟫_𝕜 = 0 := by
        rw [← inner_conj_symm, hgE c y hy, map_zero]
      rw [this, mul_zero]
    have hmem : g ∈ (⨆ c, eigenspace (T : E →ₗ[𝕜] E) c)ᗮ :=
      Submodule.orthogonal_le hle
        (Submodule.le_orthogonal_orthogonal _ (Submodule.mem_span_singleton_self g))
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs] at hmem
    simpa using hmem
  set bAll : HilbertBasis (ι ⊕ w) 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot hONall hbot with hbAll
  have hcoe : ⇑bAll = vAll := HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  refine ⟨ι, v, lam, countable_of_orthonormal hON, fun n => n.1.2.1, hON, heig, ?_⟩
  intro g
  have hrep : HasSum (fun i => ⟪vAll i, g⟫_𝕜 • vAll i) g := by
    have h := bAll.hasSum_repr g
    simp only [hcoe, HilbertBasis.repr_apply_apply] at h
    exact h
  have hTsum := hrep.mapL T
  simp only [map_smul] at hTsum
  have hvan : ∀ x ∉ Set.range (Sum.inl : ι → ι ⊕ w),
      (fun i => ⟪vAll i, g⟫_𝕜 • T (vAll i)) x = 0 := by
    rintro (n | k) hx
    · exact absurd ⟨n, rfl⟩ hx
    · simp [hvAll, hkerN k]
  have := (Sum.inl_injective (β := w)).hasSum_iff (f := fun i => ⟪vAll i, g⟫_𝕜 • T (vAll i))
    (a := T g) hvan
  rw [← this] at hTsum
  convert hTsum using 2 with n
  have h1 : vAll (Sum.inl n) = v n := rfl
  rw [Function.comp_apply, h1, heig n, smul_comm]


/-- **Mercer's theorem, existence of the eigensystem**: every Mercer kernel against a
finite Borel measure of full support admits a Mercer eigensystem. -/
theorem exists_mercerEigensystem {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: the measure has full support
    [μ.IsOpenPosMeasure] :
    Nonempty (MercerEigensystem μ K hK.continuous) := by
  haveI := separableSpace_Lp 𝕜 μ
  obtain ⟨ι, v, lam, hcount, hpos, hON, heig, hexp⟩ :=
    exists_eigen_data (mercerCLM μ hK.continuous) (isCompactOperator_mercerCLM hK)
      (isPositive_mercerCLM hK)
  have hlne : ∀ n, ((lam n : ℝ) : 𝕜) ≠ 0 := fun n => RCLike.ofReal_ne_zero.mpr (hpos n).ne'
  -- the continuous representative `λ⁻¹ T_K eₙ` of the eigenvector `eₙ`
  set F : ι → C(X, 𝕜) := fun n =>
    ⟨fun x => ((lam n : ℝ) : 𝕜)⁻¹ * integralOp μ K (v n) x,
      continuous_const.mul (continuous_integralOp_of_continuous hK.continuous (v n))⟩ with hF
  have htoLp : ∀ n, ContinuousMap.toLp 2 μ 𝕜 (F n) = v n := by
    intro n
    have h4 : ((mercerCLM μ hK.continuous (v n) : Lp 𝕜 2 μ) : X → 𝕜)
        =ᵐ[μ] ((((lam n : ℝ) : 𝕜) • v n : Lp 𝕜 2 μ) : X → 𝕜) := by rw [heig n]
    refine Lp.ext ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (F n),
      mercerCLM_coeFn_ae hK.continuous (v n), h4,
      Lp.coeFn_smul (((lam n : ℝ) : 𝕜)) (v n)] with x h1 h2 h3 h5
    rw [h1]
    change ((lam n : ℝ) : 𝕜)⁻¹ * integralOp μ K (v n) x = _
    rw [← h2, h3, h5]
    change ((lam n : ℝ) : 𝕜)⁻¹ * (((lam n : ℝ) : 𝕜) * ((v n : X → 𝕜) x)) = _
    rw [inv_mul_cancel_left₀ (hlne n)]
  have hfun : (fun n => ContinuousMap.toLp 2 μ 𝕜 (F n)) = v := funext htoLp
  refine ⟨⟨ι, hcount, F, lam, hpos, by rw [hfun]; exact hON, ?_, ?_⟩⟩
  · intro n x
    rw [htoLp n]
    change _ = ((lam n : ℝ) : 𝕜) * (((lam n : ℝ) : 𝕜)⁻¹ * integralOp μ K (v n) x)
    rw [mul_inv_cancel_left₀ (hlne n)]
  · intro g
    simp only [htoLp]
    exact hexp g

section Residual

variable {K : X → X → 𝕜} {hKc : Continuous fun p : X × X => K p.1 p.2}

/-- Coefficientwise description of a finite `L²` combination. -/
private theorem coeFn_finset_sum_smul' {ι : Type*} (s : Finset ι) (c : ι → 𝕜)
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

/-- The residual symbol of a Mercer eigensystem after removing a finite set of modes. -/
private noncomputable def residualSymbol (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    X → X → 𝕜 :=
  fun x y => K x y - ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))

private theorem continuous_residualSymbol (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    Continuous fun p : X × X => residualSymbol d s p.1 p.2 :=
  hKc.sub (continuous_finset_sum s fun n _ =>
    continuous_const.mul (((d.eigfun n).continuous.comp continuous_fst).mul
      (RCLike.continuous_conj.comp ((d.eigfun n).continuous.comp continuous_snd))))

private theorem symbolConjLp_residual (d : MercerEigensystem μ K hKc) (s : Finset d.ι) (x : X) :
    symbolConjLp μ (residualSymbol d s)
        (isL2Symbol_of_continuous (continuous_residualSymbol d s)) x
      = symbolConjLp μ K (isL2Symbol_of_continuous hKc) x
        - ∑ n ∈ s, ((d.eigval n : 𝕜) * conj (d.eigfun n x)) •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n) := by
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (μ := μ) (p := 2)
      ((IsL2Symbol.conj _ (isL2Symbol_of_continuous (continuous_residualSymbol d s))) x),
    MemLp.coeFn_toLp (μ := μ) (p := 2)
      ((IsL2Symbol.conj _ (isL2Symbol_of_continuous hKc)) x),
    Lp.coeFn_sub (symbolConjLp μ K (isL2Symbol_of_continuous hKc) x)
      (∑ n ∈ s, ((d.eigval n : 𝕜) * conj (d.eigfun n x)) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    coeFn_finset_sum_smul' s (fun n => (d.eigval n : 𝕜) * conj (d.eigfun n x))
      (fun n => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    (Filter.eventually_all_finset s).2 (fun n _ =>
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n))]
    with y h1 h2 h3 h4 h5
  rw [h3]
  simp only [symbolConjLp, Pi.sub_apply]
  rw [h1, h2, h4]
  simp only [residualSymbol, map_sub, map_sum, map_mul, RCLike.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [h5 n hn, RCLike.conj_ofReal]
  ring

private theorem integralOp_residual (d : MercerEigensystem μ K hKc) (s : Finset d.ι)
    (g : Lp 𝕜 2 μ) (x : X) :
    integralOp μ (residualSymbol d s) g x
      = integralOp μ K g x
        - ∑ n ∈ s, (d.eigval n : 𝕜) *
            (d.eigfun n x * ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) := by
  rw [integralOp_eq_inner _ (isL2Symbol_of_continuous (continuous_residualSymbol d s)),
    integralOp_eq_inner _ (isL2Symbol_of_continuous hKc), symbolConjLp_residual,
    inner_sub_left, sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_smul_left, map_mul, RCLike.conj_ofReal, RCLike.conj_conj]
  ring

private theorem mercerCLM_residual (d : MercerEigensystem μ K hKc) (s : Finset d.ι)
    (g : Lp 𝕜 2 μ) :
    mercerCLM μ (continuous_residualSymbol d s) g
      = mercerCLM μ hKc g
        - ∑ n ∈ s, ((d.eigval n : 𝕜) *
            ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
              ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n) := by
  refine Lp.ext ?_
  filter_upwards [mercerCLM_coeFn_ae (continuous_residualSymbol d s) g,
    mercerCLM_coeFn_ae hKc g,
    Lp.coeFn_sub (mercerCLM μ hKc g)
      (∑ n ∈ s, ((d.eigval n : 𝕜) * ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    coeFn_finset_sum_smul' s
      (fun n => (d.eigval n : 𝕜) * ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜)
      (fun n => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    (Filter.eventually_all_finset s).2 (fun n _ =>
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n))]
    with x h1 h2 h3 h4 h5
  rw [h1, h3, Pi.sub_apply, h2, h4, integralOp_residual]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [h5 n hn]
  ring

/-- The quadratic form of `T_K` expands over the eigensystem with nonnegative terms. -/
private theorem hasSum_re_quadratic (d : MercerEigensystem μ K hKc) (g : Lp 𝕜 2 μ) :
    HasSum
      (fun n => d.eigval n *
        ‖⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜‖ ^ 2)
      (RCLike.re ⟪g, mercerCLM μ hKc g⟫_𝕜) := by
  refine (((d.opExpansion g).mapL (innerSL 𝕜 g)).map
    (RCLike.reCLM (K := 𝕜)).toLinearMap.toAddMonoidHom RCLike.reCLM.continuous).congr_fun
    fun n => ?_
  show d.eigval n * ‖⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜‖ ^ 2
      = RCLike.re ⟪g, (d.eigval n : 𝕜) •
          (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n))⟫_𝕜
  rw [inner_smul_right, inner_smul_right,
    ← inner_conj_symm g (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

private theorem isPositive_residual (hK : IsMercerKernel 𝕜 K)
    (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    (mercerCLM μ (continuous_residualSymbol d s)).IsPositive := by
  have hTsym : ∀ a b : Lp 𝕜 2 μ,
      ⟪mercerCLM μ hKc a, b⟫_𝕜 = ⟪a, mercerCLM μ hKc b⟫_𝕜 :=
    fun a b => (isPositive_mercerCLM hK).1 a b
  constructor
  · intro h g
    show ⟪mercerCLM μ (continuous_residualSymbol d s) h, g⟫_𝕜
      = ⟪h, mercerCLM μ (continuous_residualSymbol d s) g⟫_𝕜
    rw [mercerCLM_residual, mercerCLM_residual, inner_sub_left, inner_sub_right, sum_inner,
      inner_sum, hTsym h g]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_smul_left, inner_smul_right, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal,
      inner_conj_symm]
    ring
  · intro g
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, mercerCLM_residual, inner_sub_left,
      sum_inner, map_sub, map_sum]
    have hkey := hasSum_re_quadratic d g
    have hre : RCLike.re ⟪mercerCLM μ hKc g, g⟫_𝕜 = RCLike.re ⟪g, mercerCLM μ hKc g⟫_𝕜 :=
      inner_re_symm _ _
    rw [hre]
    have hterm : ∀ n : d.ι,
        RCLike.re (⟪((d.eigval n : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜)
          = d.eigval n * ‖⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜‖ ^ 2 := by
      intro n
      rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
        RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
    simp only [hterm]
    have := sum_le_hasSum s
      (fun n _ => mul_nonneg (d.eigval_pos n).le (by positivity)) hkey
    linarith

/-- **Bessel-type bound**: the truncated diagonal sums are dominated by the kernel
diagonal.  This is the analytic heart of Mercer's theorem. -/
private theorem eig_diag_bound (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (s : Finset d.ι) (x : X) :
    ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 ≤ RCLike.re (K x x) := by
  have hsym : ∀ a b : X, conj (residualSymbol d s a b) = residualSymbol d s b a := by
    intro a b
    simp only [residualSymbol, map_sub, map_sum, map_mul, RCLike.conj_conj,
      RCLike.conj_ofReal, hK.isKernelFun.conj_symm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  have hM := isMercerKernel_of_isPositive (continuous_residualSymbol d s) hsym
    (isPositive_residual hK d s)
  have h1 := hM.isKernelFun.re_sum_nonneg 1 (fun _ => x) (fun _ => 1)
  simp only [Fin.sum_univ_one, map_one, one_mul] at h1
  have h2 : RCLike.re (residualSymbol d s x x)
      = RCLike.re (K x x) - ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 := by
    simp only [residualSymbol, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  rw [h2] at h1
  linarith

/-- Finite Cauchy–Schwarz for the eigen-expansion. -/
private theorem sq_norm_sum_eig_le (d : MercerEigensystem μ K hKc) (t : Finset d.ι) (x y : X) :
    ‖∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖ ^ 2
      ≤ (∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2) *
        (∑ n ∈ t, d.eigval n * ‖d.eigfun n y‖ ^ 2) := by
  have hsq : ∀ n : d.ι, ∀ z : X,
      (Real.sqrt (d.eigval n) * ‖d.eigfun n z‖) ^ 2 = d.eigval n * ‖d.eigfun n z‖ ^ 2 := by
    intro n z
    rw [mul_pow, Real.sq_sqrt (d.eigval_pos n).le]
  have h1 : ‖∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖
      ≤ ∑ n ∈ t, (Real.sqrt (d.eigval n) * ‖d.eigfun n x‖) *
          (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_ofReal,
      abs_of_pos (d.eigval_pos n)]
    have hs : Real.sqrt (d.eigval n) * Real.sqrt (d.eigval n) = d.eigval n :=
      Real.mul_self_sqrt (d.eigval_pos n).le
    have he : Real.sqrt (d.eigval n) * ‖d.eigfun n x‖ *
        (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖)
        = d.eigval n * (‖d.eigfun n x‖ * ‖d.eigfun n y‖) := by
      rw [show Real.sqrt (d.eigval n) * ‖d.eigfun n x‖ *
        (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖)
        = (Real.sqrt (d.eigval n) * Real.sqrt (d.eigval n)) *
          (‖d.eigfun n x‖ * ‖d.eigfun n y‖) from by ring, hs]
    exact le_of_eq he.symm
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq t
      (fun n => Real.sqrt (d.eigval n) * ‖d.eigfun n x‖)
      (fun n => Real.sqrt (d.eigval n) * ‖d.eigfun n y‖)
  simp only [hsq] at h2
  have h0 : (0 : ℝ) ≤ ∑ n ∈ t, (Real.sqrt (d.eigval n) * ‖d.eigfun n x‖) *
      (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖) :=
    Finset.sum_nonneg fun n _ => by positivity
  nlinarith [norm_nonneg (∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))]

/-- The diagonal series of a Mercer eigensystem is summable. -/
private theorem summable_eig_diag (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x : X) :
    Summable fun n => d.eigval n * ‖d.eigfun n x‖ ^ 2 :=
  summable_of_sum_le (fun n => mul_nonneg (d.eigval_pos n).le (sq_nonneg _))
    (fun s => eig_diag_bound hK d s x)

/-- The off-diagonal series of a Mercer eigensystem is summable. -/
private theorem summable_eig_prod (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x y : X) :
    Summable fun n => (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)) := by
  refine Summable.of_norm_bounded
    (((summable_eig_diag hK d x).add (summable_eig_diag hK d y)).div_const 2) fun n => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_ofReal, abs_of_pos (d.eigval_pos n)]
  nlinarith [sq_nonneg (‖d.eigfun n x‖ - ‖d.eigfun n y‖), (d.eigval_pos n).le,
    norm_nonneg (d.eigfun n x), norm_nonneg (d.eigfun n y)]

/-- The kernel diagonal is bounded on the compact base space. -/
private theorem exists_diag_bound (hKc : Continuous fun p : X × X => K p.1 p.2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : X, RCLike.re (K y y) ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun y : X => RCLike.re (K y y))
    ((RCLike.reCLM (K := 𝕜)).continuous.comp'
      (hKc.comp' (continuous_id.prodMk continuous_id))).continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y => ?_⟩
  exact le_trans (le_trans (le_abs_self _) (hM y (Set.mem_univ _))) (le_max_left _ _)

/-- Tail estimate for the eigen-expansion, uniform in the second variable. -/
private theorem norm_tsum_sub_sum_le (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x y : X) (t : Finset d.ι) :
    ‖(∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
        - ∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖
      ≤ Real.sqrt ((∑' n, d.eigval n * ‖d.eigfun n x‖ ^ 2)
            - ∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2) *
          Real.sqrt (RCLike.re (K y y)) := by
  classical
  have hsx := summable_eig_diag hK d x
  have hf := (summable_eig_prod hK d x y).hasSum
  have hlim : Filter.Tendsto
      (fun u : Finset d.ι =>
        ‖(∑ n ∈ u, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
          - ∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖)
      Filter.atTop
      (𝓝 ‖(∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
          - ∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖) :=
    (continuous_norm.tendsto _).comp (hf.sub_const _)
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop t] with u hu
  have hsplit : (∑ n ∈ u, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
      - ∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))
      = ∑ n ∈ u \ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)) := by
    rw [← Finset.sum_sdiff hu]
    ring
  rw [hsplit]
  have hcs := sq_norm_sum_eig_le d (u \ t) x y
  have hAx : (∑ n ∈ u \ t, d.eigval n * ‖d.eigfun n x‖ ^ 2)
      ≤ (∑' n, d.eigval n * ‖d.eigfun n x‖ ^ 2)
        - ∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2 := by
    have h1 : (∑ n ∈ u \ t, d.eigval n * ‖d.eigfun n x‖ ^ 2)
        + ∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2
        = ∑ n ∈ u, d.eigval n * ‖d.eigfun n x‖ ^ 2 := Finset.sum_sdiff hu
    have h2 : (∑ n ∈ u, d.eigval n * ‖d.eigfun n x‖ ^ 2)
        ≤ ∑' n, d.eigval n * ‖d.eigfun n x‖ ^ 2 :=
      Summable.sum_le_tsum u (fun n _ => mul_nonneg (d.eigval_pos n).le (sq_nonneg _)) hsx
    linarith
  have hAy : (∑ n ∈ u \ t, d.eigval n * ‖d.eigfun n y‖ ^ 2) ≤ RCLike.re (K y y) :=
    eig_diag_bound hK d (u \ t) y
  have hAx0 : (0 : ℝ) ≤ ∑ n ∈ u \ t, d.eigval n * ‖d.eigfun n x‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => mul_nonneg (d.eigval_pos n).le (sq_nonneg _)
  have hAy0 : (0 : ℝ) ≤ ∑ n ∈ u \ t, d.eigval n * ‖d.eigfun n y‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => mul_nonneg (d.eigval_pos n).le (sq_nonneg _)
  have hstep : ‖∑ n ∈ u \ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖
      ≤ Real.sqrt (∑ n ∈ u \ t, d.eigval n * ‖d.eigfun n x‖ ^ 2) *
        Real.sqrt (∑ n ∈ u \ t, d.eigval n * ‖d.eigfun n y‖ ^ 2) := by
    have h := Real.sqrt_le_sqrt hcs
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hAx0] at h
  refine le_trans hstep ?_
  gcongr


/-- The eigen-expansion converges uniformly in the second variable. -/
private theorem tendstoUniformly_eig (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x : X) :
    TendstoUniformly
      (fun t : Finset d.ι => fun y =>
        ∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
      (fun y => ∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
      Filter.atTop := by
  obtain ⟨M, hM0, hM⟩ := exists_diag_bound (K := K) hKc
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hsx := summable_eig_diag hK d x
  have hMs : (0 : ℝ) < Real.sqrt M + 1 := by positivity
  have hq0 : (0 : ℝ) ≤ ε / (Real.sqrt M + 1) := by positivity
  have hδ0 : (0 : ℝ) < (ε / (Real.sqrt M + 1)) ^ 2 := by positivity
  have htend : Filter.Tendsto
      (fun t : Finset d.ι => (∑' n, d.eigval n * ‖d.eigfun n x‖ ^ 2)
        - ∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2) Filter.atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := ∑' n, d.eigval n * ‖d.eigfun n x‖ ^ 2)
      (f := Filter.atTop (α := Finset d.ι))).sub hsx.hasSum
    rwa [sub_self] at h
  filter_upwards [htend.eventually_lt_const hδ0] with t ht
  intro y
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_tsum_sub_sum_le hK d x y t) ?_
  have h1 : Real.sqrt ((∑' n, d.eigval n * ‖d.eigfun n x‖ ^ 2)
      - ∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2) ≤ ε / (Real.sqrt M + 1) := by
    have := Real.sqrt_le_sqrt ht.le
    rwa [Real.sqrt_sq hq0] at this
  have h2 : Real.sqrt (RCLike.re (K y y)) ≤ Real.sqrt M := Real.sqrt_le_sqrt (hM y)
  have h3 : Real.sqrt ((∑' n, d.eigval n * ‖d.eigfun n x‖ ^ 2)
      - ∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2) * Real.sqrt (RCLike.re (K y y))
      ≤ (ε / (Real.sqrt M + 1)) * Real.sqrt M := by
    refine mul_le_mul h1 h2 (Real.sqrt_nonneg _) hq0
  refine lt_of_le_of_lt h3 ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ hMs]
  nlinarith [Real.sqrt_nonneg M, hε]

/-- The limit of the eigen-expansion is continuous in the second variable. -/
private theorem continuous_eig_tsum (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x : X) :
    Continuous fun y => ∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)) :=
  (tendstoUniformly_eig hK d x).continuous
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t =>
      continuous_finset_sum t fun n _ =>
        continuous_const.mul (continuous_const.mul
          (RCLike.continuous_conj.comp' (d.eigfun n).continuous))))


end Residual

/-- **Mercer's theorem, kernel expansion**: `K(x, y) = ∑ₙ λₙ eₙ(x) conj (eₙ(y))`
pointwise (unordered absolute convergence). -/
theorem MercerEigensystem.hasSum_kernel {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    -- USER-INPUT: positivity of the kernel (with `hKc`, a Mercer kernel)
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x y : X) :
    HasSum (fun n => (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))) (K x y) := by
  classical
  -- the eigenfunctions as `L²` classes, and the section `conj K(x, ·)`
  have hL2 : IsL2Symbol μ K := isL2Symbol_of_continuous hKc
  have hkx : ∀ g : Lp 𝕜 2 μ, ⟪symbolConjLp μ K hL2 x, g⟫_𝕜 = integralOp μ K g x :=
    fun g => (integralOp_eq_inner K hL2 g x).symm
  have hTsym : ∀ a b : Lp 𝕜 2 μ,
      ⟪mercerCLM μ hKc a, b⟫_𝕜 = ⟪a, mercerCLM μ hKc b⟫_𝕜 :=
    fun a b => (isPositive_mercerCLM hK).1 a b
  -- (α) the eigenvalue equation in `L²`
  have heigL : ∀ n, mercerCLM μ hKc (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)) = (d.eigval n : 𝕜) • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n) := by
    intro n
    refine Lp.ext ?_
    filter_upwards [mercerCLM_coeFn_ae hKc (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
      Lp.coeFn_smul ((d.eigval n : 𝕜)) (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n)]
      with z h1 h2 h3
    rw [h1, h2, Pi.smul_apply, smul_eq_mul, h3, d.eigen_eq n z]
  -- (γ) the integral operator vanishes pointwise on its kernel
  have hker0 : ∀ g₀ : Lp 𝕜 2 μ, mercerCLM μ hKc g₀ = 0 → ∀ z, integralOp μ K g₀ z = 0 := by
    intro g₀ h0 z
    have hae : integralOp μ K g₀ =ᵐ[μ] fun _ : X => (0 : 𝕜) := by
      filter_upwards [(mercerCLM_coeFn_ae hKc g₀).symm,
        Lp.coeFn_zero (E := 𝕜) (p := 2) (μ := μ)] with a ha hb
      rw [ha, h0, hb]
      rfl
    have := (Continuous.ae_eq_iff_eq (μ := μ)
      (continuous_integralOp_of_continuous hKc g₀) continuous_const).mp hae
    exact congrFun this z
  -- (β) the eigenfunctions are orthogonal to the kernel of `T_K`
  have hEEker : ∀ (n : d.ι) (g₀ : Lp 𝕜 2 μ), mercerCLM μ hKc g₀ = 0 → ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g₀⟫_𝕜 = 0 := by
    intro n g₀ h0
    have h1 : ⟪mercerCLM μ hKc (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)), g₀⟫_𝕜 = ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), mercerCLM μ hKc g₀⟫_𝕜 := hTsym _ _
    rw [heigL n, h0, inner_zero_right, inner_smul_left, RCLike.conj_ofReal] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (RCLike.ofReal_ne_zero.mpr (d.eigval_pos n).ne')
    · exact h
  -- the continuous limit of the conjugated expansion, as an element of `C(X, 𝕜)`
  have hSc : Continuous fun z : X =>
      conj (∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n z))) :=
    RCLike.continuous_conj.comp' (continuous_eig_tsum hK d x)
  set Sc : C(X, 𝕜) := ⟨_, hSc⟩ with hScdef
  set G : Finset d.ι → C(X, 𝕜) := fun t =>
    ∑ n ∈ t, ((d.eigval n : 𝕜) * conj (d.eigfun n x)) • d.eigfun n with hGdef
  have hUC : TendstoUniformly (fun t : Finset d.ι => fun z => G t z) (fun z => Sc z)
      Filter.atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp (tendstoUniformly_eig hK d x)) ε hε]
      with t ht z
    have hGz : G t z
        = conj (∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n z))) := by
      rw [map_sum, hGdef]
      simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul, map_mul, RCLike.conj_conj, RCLike.conj_ofReal]
      ring
    have hScz : Sc z = conj (∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n z))) := rfl
    rw [hGz, hScz, dist_eq_norm, ← map_sub, RCLike.norm_conj, ← dist_eq_norm]
    exact ht z
  have hGtend : Filter.Tendsto G Filter.atTop (nhds Sc) :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mpr hUC
  have hw : HasSum (fun n => ((d.eigval n : 𝕜) * conj (d.eigfun n x)) • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n))
      (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 Sc) := by
    have h := ((ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜).continuous.tendsto Sc).comp hGtend
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, hGdef, map_sum, map_smul]
  -- the coefficients of `w` and of `conj K(x, ·)` against the eigenfunctions agree
  have hEEw : ∀ m : d.ι, ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m), ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 Sc⟫_𝕜
      = (d.eigval m : 𝕜) * conj (d.eigfun m x) := by
    intro m
    have h := hw.mapL (innerSL 𝕜 (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m)))
    have heq : (fun n => (innerSL 𝕜 (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m))) (((d.eigval n : 𝕜) * conj (d.eigfun n x)) • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)))
        = fun n => if n = m then (d.eigval m : 𝕜) * conj (d.eigfun m x) else 0 := by
      funext n
      rw [innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.mp d.orthonormal m n]
      by_cases hnm : n = m
      · subst hnm; simp
      · simp [hnm, Ne.symm hnm]
    rw [heq] at h
    exact ((hasSum_ite_eq m ((d.eigval m : 𝕜) * conj (d.eigfun m x))).unique h).symm
  have hEEk : ∀ m : d.ι, ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m), symbolConjLp μ K hL2 x⟫_𝕜
      = (d.eigval m : 𝕜) * conj (d.eigfun m x) := by
    intro m
    rw [← inner_conj_symm, hkx, d.eigen_eq m x, map_mul, RCLike.conj_ofReal]
  -- both are orthogonal to the kernel of `T_K`
  have hg0w : ∀ g₀ : Lp 𝕜 2 μ, mercerCLM μ hKc g₀ = 0 →
      ⟪g₀, ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 Sc⟫_𝕜 = 0 := by
    intro g₀ h0
    have h := hw.mapL (innerSL 𝕜 g₀)
    have heq : (fun n => (innerSL 𝕜 g₀) (((d.eigval n : 𝕜) * conj (d.eigfun n x)) • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)))
        = fun _ : d.ι => (0 : 𝕜) := by
      funext n
      rw [innerSL_apply_apply, inner_smul_right, ← inner_conj_symm, hEEker n g₀ h0,
        map_zero, mul_zero]
    rw [heq] at h
    exact (hasSum_zero.unique h).symm
  have hg0k : ∀ g₀ : Lp 𝕜 2 μ, mercerCLM μ hKc g₀ = 0 →
      ⟪g₀, symbolConjLp μ K hL2 x⟫_𝕜 = 0 := by
    intro g₀ h0
    rw [← inner_conj_symm, hkx, hker0 g₀ h0 x, map_zero]
  -- the difference is in the kernel and orthogonal to it, hence zero
  set ψ : Lp 𝕜 2 μ := ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 Sc - symbolConjLp μ K hL2 x with hψdef
  have hψE : ∀ m : d.ι, ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun m), ψ⟫_𝕜 = 0 := by
    intro m
    rw [hψdef, inner_sub_right, hEEw m, hEEk m, sub_self]
  have hψker : mercerCLM μ hKc ψ = 0 := by
    have h := d.opExpansion ψ
    have heq : (fun n => (d.eigval n : 𝕜) • (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), ψ⟫_𝕜 • ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)))
        = fun _ : d.ι => (0 : Lp 𝕜 2 μ) := by
      funext n
      rw [hψE n, zero_smul, smul_zero]
    rw [heq] at h
    exact (hasSum_zero.unique h).symm
  have hψ0 : ψ = 0 := by
    have h1 : ⟪ψ, ψ⟫_𝕜 = 0 := by
      rw [hψdef, inner_sub_right, hg0w ψ hψker, hg0k ψ hψker, sub_zero]
    exact inner_self_eq_zero.mp h1
  -- conclude: the two continuous functions agree a.e., hence everywhere
  have hwk : ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 Sc = symbolConjLp μ K hL2 x :=
    sub_eq_zero.mp hψ0
  have hae : (fun z : X => conj (∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n z))))
      =ᵐ[μ] fun z : X => conj (K x z) := by
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) Sc,
      MemLp.coeFn_toLp (μ := μ) (p := 2) ((IsL2Symbol.conj K hL2) x)] with z h1 h2
    have h3 : ((ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 Sc : Lp 𝕜 2 μ) : X → 𝕜) z
        = ((symbolConjLp μ K hL2 x : Lp 𝕜 2 μ) : X → 𝕜) z := by rw [hwk]
    rw [h3] at h1
    simp only [symbolConjLp] at h1
    rw [h2] at h1
    exact h1.symm
  have heverywhere : (fun z : X => conj (∑' n, (d.eigval n : 𝕜) *
      (d.eigfun n x * conj (d.eigfun n z)))) = fun z : X => conj (K x z) :=
    (Continuous.ae_eq_iff_eq (μ := μ) hSc
      (RCLike.continuous_conj.comp' (hKc.comp' (continuous_const.prodMk continuous_id)))).mp hae
  have hxy : (∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))) = K x y := by
    have := congrFun heverywhere y
    have h4 : conj (conj (∑' n, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))))
        = conj (conj (K x y)) := by rw [this]
    rwa [RCLike.conj_conj, RCLike.conj_conj] at h4
  rw [← hxy]
  exact (summable_eig_prod hK d x y).hasSum


section Trace

variable {K : X → X → 𝕜} {hKc : Continuous fun p : X × X => K p.1 p.2}

/-- Diagonal case of the kernel expansion, in real form. -/
private theorem hasSum_diag_eig (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x : X) :
    HasSum (fun n => d.eigval n * ‖d.eigfun n x‖ ^ 2) (RCLike.re (K x x)) := by
  refine ((d.hasSum_kernel hK x x).map
    (RCLike.reCLM (K := 𝕜)).toLinearMap.toAddMonoidHom RCLike.reCLM.continuous).congr_fun
    fun n => ?_
  show d.eigval n * ‖d.eigfun n x‖ ^ 2
      = RCLike.re ((d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n x)))
  rw [RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- Dini: the diagonal partial sums converge uniformly. -/
private theorem tendstoUniformly_diag_eig (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    TendstoUniformly
      (fun s : Finset d.ι => fun x : X => ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2)
      (fun x => RCLike.re (K x x)) Filter.atTop := by
  refine Monotone.tendstoUniformly_of_forall_tendsto ?_ ?_ ?_ ?_
  · exact fun s => continuous_finset_sum s fun n _ =>
      continuous_const.mul (((d.eigfun n).continuous.norm).pow 2)
  · exact fun s t hst x => Finset.sum_le_sum_of_subset_of_nonneg hst
      fun n _ _ => mul_nonneg (d.eigval_pos n).le (sq_nonneg _)
  · exact (RCLike.continuous_re (K := 𝕜)).comp'
      (hK.continuous.comp' (continuous_id.prodMk continuous_id))
  · exact fun x => hasSum_diag_eig hK d x

/-- Continuous real functions on the compact base space are integrable. -/
private theorem integrable_of_cont' {f : X → ℝ} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => hM z (Set.mem_univ _)))

/-- The eigenfunctions have unit `L²` mass. -/
private theorem integral_normSq_eigfun (d : MercerEigensystem μ K hKc) (n : d.ι) :
    ∫ z, ‖d.eigfun n z‖ ^ 2 ∂μ = 1 := by
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

/-- The truncated eigenvalue sum is the integral of the truncated diagonal expansion. -/
private theorem sum_eigval_eq_integral (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    (∑ n ∈ s, d.eigval n) = ∫ x, ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 ∂μ := by
  rw [integral_finset_sum s fun n _ =>
    (integrable_of_cont' (((d.eigfun n).continuous.norm).fun_pow 2)).const_mul _]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_normSq_eigfun d n, mul_one]

/-- Continuity of the truncated diagonal expansion. -/
private theorem continuous_diag_partial (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    Continuous fun x : X => ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 :=
  continuous_finset_sum s fun n _ =>
    continuous_const.mul (((d.eigfun n).continuous.norm).pow 2)

end Trace

/-- **Mercer's theorem, uniform convergence**: the finite partial sums of the
eigen-expansion converge to `K` uniformly on `X × X`. -/
theorem MercerEigensystem.tendstoUniformly_kernel {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    TendstoUniformly
      (fun s : Finset d.ι => fun p : X × X =>
        ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n p.1 * conj (d.eigfun n p.2)))
      (fun p => K p.1 p.2) Filter.atTop := by
  classical
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hδ0 : (0 : ℝ) < ε / 2 := by positivity
  have hdiag := (Metric.tendstoUniformly_iff.mp (tendstoUniformly_diag_eig hK d)) _ hδ0
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp hdiag
  refine Filter.eventually_atTop.mpr ⟨s₀, fun s hs p => ?_⟩
  obtain ⟨x, y⟩ := p
  have hpart : ∀ (z : X) (u : Finset d.ι),
      ∑ n ∈ u, d.eigval n * ‖d.eigfun n z‖ ^ 2 ≤ RCLike.re (K z z) := fun z u =>
    sum_le_hasSum u (fun n _ => mul_nonneg (d.eigval_pos n).le (sq_nonneg _))
      (hasSum_diag_eig hK d z)
  have htail : ∀ (z : X) (u : Finset d.ι), s ⊆ u →
      ∑ n ∈ u \ s, d.eigval n * ‖d.eigfun n z‖ ^ 2 ≤ ε / 2 := by
    intro z u hsu
    have h1 : (∑ n ∈ u \ s, d.eigval n * ‖d.eigfun n z‖ ^ 2)
        + ∑ n ∈ s, d.eigval n * ‖d.eigfun n z‖ ^ 2
        = ∑ n ∈ u, d.eigval n * ‖d.eigfun n z‖ ^ 2 := Finset.sum_sdiff hsu
    have h2 := hpart z u
    have h3 := hs₀ s hs z
    rw [Real.dist_eq] at h3
    have h4 := abs_lt.mp h3
    linarith [h4.1, h4.2]
  have hkey : ∀ u : Finset d.ι, s ⊆ u →
      ‖(∑ n ∈ u, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
        - ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖ ≤ ε / 2 := by
    intro u hsu
    have hsplit : (∑ n ∈ u, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
        - ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))
        = ∑ n ∈ u \ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)) := by
      rw [← Finset.sum_sdiff hsu]; ring
    rw [hsplit]
    have hcs := sq_norm_sum_eig_le d (u \ s) x y
    have hx := htail x u hsu
    have hy := htail y u hsu
    have hnx : (0 : ℝ) ≤ ∑ n ∈ u \ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => mul_nonneg (d.eigval_pos n).le (sq_nonneg _)
    have hny : (0 : ℝ) ≤ ∑ n ∈ u \ s, d.eigval n * ‖d.eigfun n y‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => mul_nonneg (d.eigval_pos n).le (sq_nonneg _)
    nlinarith [norm_nonneg (∑ n ∈ u \ s,
      (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))]
  have hlim : Filter.Tendsto
      (fun u : Finset d.ι => ‖(∑ n ∈ u, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
        - ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖)
      Filter.atTop
      (nhds ‖K x y - ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖) := by
    have hT : Filter.Tendsto
        (fun u : Finset d.ι =>
          ∑ n ∈ u, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))
        Filter.atTop (nhds (K x y)) := d.hasSum_kernel hK x y
    exact (hT.sub tendsto_const_nhds).norm
  have hfin : ‖K x y - ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖
      ≤ ε / 2 :=
    le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨s, fun u hsu => hkey u hsu⟩)
  rw [dist_eq_norm]
  linarith

/-- The eigenvalues of a Mercer eigensystem are square-summable (they are dominated by
the trace `∫ K(x,x) dμ`; in fact they are summable). -/
theorem MercerEigensystem.summable_eigval {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    Summable d.eigval := by
  have hcontK : Continuous fun x : X => RCLike.re (K x x) :=
    (RCLike.continuous_re (K := 𝕜)).comp'
      (hK.continuous.comp' (continuous_id.prodMk continuous_id))
  refine summable_of_sum_le (fun n => (d.eigval_pos n).le)
    (c := ∫ x, RCLike.re (K x x) ∂μ) fun s => ?_
  rw [sum_eigval_eq_integral d s]
  exact integral_mono (integrable_of_cont' (continuous_diag_partial d s))
    (integrable_of_cont' hcontK) fun x => eig_diag_bound hK d s x

/-- The trace formula: `∑ₙ λₙ = ∫ K(x, x) dμ(x)`. -/
theorem MercerEigensystem.hasSum_eigval {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    HasSum d.eigval (∫ x, RCLike.re (K x x) ∂μ) := by
  have hcontK : Continuous fun x : X => RCLike.re (K x x) :=
    (RCLike.continuous_re (K := 𝕜)).comp'
      (hK.continuous.comp' (continuous_id.prodMk continuous_id))
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  have hmu : (0 : ℝ) ≤ μ.real Set.univ := ENNReal.toReal_nonneg
  have hε' : (0 : ℝ) < ε / (μ.real Set.univ + 1) := by positivity
  have hdiag := (Metric.tendstoUniformly_iff.mp (tendstoUniformly_diag_eig hK d)) _ hε'
  filter_upwards [hdiag] with s hs
  rw [sum_eigval_eq_integral d s, dist_eq_norm,
    ← integral_sub (integrable_of_cont' (continuous_diag_partial d s))
    (integrable_of_cont' hcontK)]
  have hbd : ‖∫ x, ((∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2) - RCLike.re (K x x)) ∂μ‖
      ≤ (ε / (μ.real Set.univ + 1)) * μ.real Set.univ := by
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun x => ?_)
    have := hs x
    rw [Real.dist_eq, abs_sub_comm] at this
    rw [Real.norm_eq_abs]
    exact this.le
  refine lt_of_le_of_lt hbd ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith [hmu, hε]

end StatLean.NonparametricStatistics
