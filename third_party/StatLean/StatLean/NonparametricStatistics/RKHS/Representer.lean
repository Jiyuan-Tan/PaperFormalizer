module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.RCLike.Lemmas

@[expose] public section

/-!
# The representer theorem

Regularized empirical risk minimization over an RKHS:
`J(f) = W(‖f‖²) + L(f(x₁), …, f(xₙ))`, with `W` increasing and `L` depending only on
the values at the data points.

* **Representer theorem**: if `W` is *strictly* increasing, every minimizer of `J` lies
  in `span {k_{x₁}, …, k_{xₙ}}` — the problem is intrinsically finite-dimensional.
  (For merely monotone `W`, the orthogonal projection of a minimizer onto the span is
  again a minimizer with the same data values.)
* **Existence and uniqueness** for the ridge form `J(f) = ‖f‖² + L(...)` with `L`
  convex and continuous: the parallelogram law gives uniqueness, and coercivity via an
  affine minorant of `L` gives existence.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 8, §8.6, Theorem 8.7 (the representer theorem) and Theorem 8.8 (existence and
uniqueness for convex ridge losses).

**Proof formalization notes.** Theorem 8.7 is split by the strength of monotonicity: for
*strictly* increasing $W$ every minimizer lies in the data span (the book's proof implicitly uses
strictness in its strict inequality), while for merely monotone $W$ the projection of a minimizer
is again a minimizer. In Theorem 8.8 the continuity of the convex loss is *derived* (convex
functions on the finite-dimensional value space are continuous), existence comes from an affine
minorant (`ConvexOn.exists_affine_le`) giving coercivity, hence a minimum on a large closed ball
of the finite-dimensional data span, and uniqueness is the book's parallelogram/midpoint argument.

**Bibliographic comments.** G. Kimeldorf and G. Wahba, *Some results on Tchebycheffian
spline functions*, J. Math. Anal. Appl. **33** (1971), 82–95; the general form with an
arbitrary increasing regularizer is due to B. Schölkopf, R. Herbrich and A. J. Smola,
*A generalized representer theorem*, COLT (2001).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]
variable {n : ℕ}

/-- The span of the kernel functions at the data points — the finite-dimensional
subspace in which representer solutions live. -/
def dataSpan (x : Fin n → X) : Submodule 𝕜 H :=
  Submodule.span 𝕜 (Set.range fun i => kernelFun H (x i))

instance (x : Fin n → X) : FiniteDimensional 𝕜 (dataSpan (H := H) x) := by
  unfold dataSpan
  exact FiniteDimensional.span_of_finite 𝕜 (Set.finite_range fun i => kernelFun H (x i))

instance (x : Fin n → X) : IsClosed ((dataSpan (H := H) x : Submodule 𝕜 H) : Set H) :=
  Submodule.closed_of_finiteDimensional _

/-- Functions orthogonal to the data span vanish at the data points. -/
theorem apply_eq_zero_of_mem_dataSpan_orthogonal {x : Fin n → X} {h : H}
    (hh : h ∈ (dataSpan x)ᗮ) (i : Fin n) : h (x i) = 0 := by
  have hmem : kernelFun H (x i) ∈ dataSpan (H := H) x := Submodule.subset_span ⟨i, rfl⟩
  have := (Submodule.mem_orthogonal _ _).mp hh _ hmem
  rwa [inner_kernelFun] at this

/-- Projecting onto the data span preserves the data values. -/
theorem starProjection_dataSpan_apply {x : Fin n → X} (f : H) (i : Fin n) :
    ((dataSpan x).starProjection f) (x i) = f (x i) := by
  have h := apply_eq_zero_of_mem_dataSpan_orthogonal
    (Submodule.sub_starProjection_mem_orthogonal (K := dataSpan (H := H) x) f) i
  simp only [RKHS.coe_sub, Pi.sub_apply, sub_eq_zero] at h
  exact h.symm

/-- **The representer theorem**: for `W` strictly increasing and any data-dependent loss
`L`, every minimizer of `f ↦ W(‖f‖²) + L(f ∘ x)` lies in the span of the kernel
functions of the data points. -/
theorem representer_mem_dataSpan (x : Fin n → X) (W : ℝ → ℝ)
    -- USER-INPUT: strictly increasing regularizer
    (hW : StrictMono W)
    (L : (Fin n → 𝕜) → ℝ) (f₀ : H)
    -- USER-INPUT: `f₀` minimizes the regularized empirical risk
    (hmin : ∀ f : H, W (‖f₀‖ ^ 2) + L (fun i => f₀ (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i))) :
    f₀ ∈ dataSpan x := by
  set g : H := (dataSpan x).starProjection f₀ with hg
  have hval : ∀ i, g (x i) = f₀ (x i) := fun i => starProjection_dataSpan_apply f₀ i
  have hle : W (‖f₀‖ ^ 2) ≤ W (‖g‖ ^ 2) := by
    have := hmin g
    simp only [hval] at this
    linarith
  have hnorm : ‖f₀‖ ^ 2 ≤ ‖g‖ ^ 2 := (hW.le_iff_le).mp hle
  have hle' : ‖g‖ ≤ ‖f₀‖ := Submodule.norm_starProjection_apply_le _ f₀
  have : ‖g‖ = ‖f₀‖ := by nlinarith [norm_nonneg f₀, norm_nonneg g]
  exact ((dataSpan x).mem_iff_norm_starProjection f₀).mpr this

/-- Representer theorem, weak (monotone) form: the projection of a minimizer onto the
data span is again a minimizer. -/
theorem representer_starProjection_isMin (x : Fin n → X) (W : ℝ → ℝ)
    -- USER-INPUT: monotone regularizer
    (hW : Monotone W)
    (L : (Fin n → 𝕜) → ℝ) (f₀ : H)
    -- USER-INPUT: `f₀` minimizes the regularized empirical risk
    (hmin : ∀ f : H, W (‖f₀‖ ^ 2) + L (fun i => f₀ (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i))) :
    ∀ f : H, W (‖(dataSpan x).starProjection f₀‖ ^ 2)
        + L (fun i => ((dataSpan x).starProjection f₀) (x i))
      ≤ W (‖f‖ ^ 2) + L (fun i => f (x i)) := by
  intro f
  have hval : ∀ i, ((dataSpan x).starProjection f₀) (x i) = f₀ (x i) :=
    fun i => starProjection_dataSpan_apply f₀ i
  have hle' : ‖(dataSpan x).starProjection f₀‖ ≤ ‖f₀‖ :=
    Submodule.norm_starProjection_apply_le _ f₀
  have hW' : W (‖(dataSpan x).starProjection f₀‖ ^ 2) ≤ W (‖f₀‖ ^ 2) :=
    hW (by nlinarith [norm_nonneg f₀, norm_nonneg ((dataSpan x).starProjection f₀)])
  simp only [hval]
  have := hmin f
  linarith

/-!
### Coercivity of the ridge objective

A convex real-valued function on a finite-dimensional space is continuous, hence bounded
below on the closed unit ball; convexity along rays then upgrades that to a global affine
minorant `B − M‖w‖`.  Against the quadratic regularizer `‖f‖²` this makes the objective
coercive, which is what produces a minimizer on a (compact) ball of the data span.
-/

private lemma exists_linear_minorant (L : (Fin n → 𝕜) → ℝ)
    (hL : ConvexOn ℝ Set.univ L) :
    ∃ B M : ℝ, 0 ≤ M ∧ ∀ w : Fin n → 𝕜, B - M * ‖w‖ ≤ L w := by
  have hcont : Continuous L := continuousOn_univ.mp (hL.continuousOn isOpen_univ)
  obtain ⟨u₀, hu₀mem, hu₀min⟩ :=
    (isCompact_closedBall (0 : Fin n → 𝕜) 1).exists_isMinOn
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩ hcont.continuousOn
  have hBle : ∀ w : Fin n → 𝕜, ‖w‖ ≤ 1 → L u₀ ≤ L w := by
    intro w hw
    exact hu₀min (by simpa [Metric.mem_closedBall, dist_zero_right] using hw)
  have hB0 : L u₀ ≤ L 0 := hBle 0 (by simp)
  refine ⟨L u₀, L 0 - L u₀, by linarith, fun w => ?_⟩
  rcases le_or_gt ‖w‖ 1 with hw | hw
  · have h := hBle w hw
    nlinarith [norm_nonneg w]
  · have ht0 : (0 : ℝ) < ‖w‖ := by linarith
    have hinv1 : ‖w‖⁻¹ ≤ 1 := by
      nlinarith [mul_inv_cancel₀ (ne_of_gt ht0), inv_pos.mpr ht0]
    have hLc := hL.2
    have hconv := hLc (Set.mem_univ (0 : Fin n → 𝕜)) (Set.mem_univ w)
      (a := 1 - ‖w‖⁻¹) (b := ‖w‖⁻¹) (by linarith)
      (le_of_lt (inv_pos.mpr ht0)) (by ring)
    have hsimp : ((1 - ‖w‖⁻¹) • (0 : Fin n → 𝕜) + ‖w‖⁻¹ • w) = ‖w‖⁻¹ • w := by
      simp
    rw [hsimp] at hconv
    have hnu : ‖(‖w‖⁻¹ • w : Fin n → 𝕜)‖ ≤ 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht0,
        inv_mul_cancel₀ (ne_of_gt ht0)]
    have hstart : L u₀ ≤ (1 - ‖w‖⁻¹) * L 0 + ‖w‖⁻¹ * L w :=
      le_trans (hBle _ hnu) hconv
    have hmul : ‖w‖ * L u₀ ≤ ‖w‖ * ((1 - ‖w‖⁻¹) * L 0 + ‖w‖⁻¹ * L w) :=
      mul_le_mul_of_nonneg_left hstart ht0.le
    have hexp : ‖w‖ * ((1 - ‖w‖⁻¹) * L 0 + ‖w‖⁻¹ * L w) = ‖w‖ * L 0 - L 0 + L w := by
      field_simp
    rw [hexp] at hmul
    nlinarith

/-- Existence half of `representer_existsUnique_of_convex`: the objective is coercive, so
it attains its minimum on a closed ball of the (finite-dimensional, hence proper) data
span, and the orthogonal projection makes that a global minimum. -/
private lemma exists_ridge_min (x : Fin n → X) (L : (Fin n → 𝕜) → ℝ)
    (hL : ConvexOn ℝ Set.univ L) :
    ∃ f₀ : H, ∀ f : H, ‖f₀‖ ^ 2 + L (fun i => f₀ (x i))
      ≤ ‖f‖ ^ 2 + L (fun i => f (x i)) := by
  obtain ⟨B, M, hM0, hminor⟩ := exists_linear_minorant L hL
  have hcontL : Continuous L := continuousOn_univ.mp (hL.continuousOn isOpen_univ)
  set Val : H →L[𝕜] (Fin n → 𝕜) := ContinuousLinearMap.pi fun i => evalCLM 𝕜 H (x i)
    with hValdef
  have hVal : ∀ f : H, Val f = fun i => f (x i) := by
    intro f; funext i
    simp [hValdef, ContinuousLinearMap.pi_apply, evalCLM_apply]
  set C := ‖Val‖ with hCdef
  have hC0 : 0 ≤ C := norm_nonneg _
  set J : H → ℝ := fun f => ‖f‖ ^ 2 + L (fun i => f (x i)) with hJdef
  have hJlow : ∀ f : H, ‖f‖ ^ 2 - M * C * ‖f‖ + B ≤ J f := by
    intro f
    have h1 : B - M * ‖(fun i => f (x i) : Fin n → 𝕜)‖ ≤ L (fun i => f (x i)) := hminor _
    have h2 : ‖(fun i => f (x i) : Fin n → 𝕜)‖ ≤ C * ‖f‖ := by
      rw [← hVal f]; exact Val.le_opNorm f
    have h3 : M * ‖(fun i => f (x i) : Fin n → 𝕜)‖ ≤ M * (C * ‖f‖) :=
      mul_le_mul_of_nonneg_left h2 hM0
    simp only [hJdef]
    nlinarith
  have hMC : 0 ≤ M * C := mul_nonneg hM0 hC0
  set R := M * C + |B| + |J 0| + 1 with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; linarith [abs_nonneg B, abs_nonneg (J 0)]
  have hRMC : M * C ≤ R := by rw [hRdef]; linarith [abs_nonneg B, abs_nonneg (J 0)]
  have hcoer : ∀ f : H, R ≤ ‖f‖ → J 0 < J f := by
    intro f hf
    have h1 := hJlow f
    have hfMC : M * C ≤ ‖f‖ := le_trans hRMC hf
    have hstep : R * (R - M * C) ≤ ‖f‖ * (‖f‖ - M * C) :=
      mul_le_mul hf (by linarith) (by linarith) (by linarith)
    have hRsub : R - M * C = |B| + |J 0| + 1 := by rw [hRdef]; ring
    have hbig : |B| + |J 0| + 1 ≤ R * (R - M * C) := by
      rw [hRsub]; nlinarith [abs_nonneg B, abs_nonneg (J 0)]
    nlinarith [le_abs_self B, neg_abs_le B, le_abs_self (J 0)]
  -- minimize over a compact ball of the data span
  have hgcont : Continuous fun z : dataSpan (H := H) x => J (z : H) := by
    have h1 : Continuous fun z : dataSpan (H := H) x => ‖(z : H)‖ ^ 2 :=
      continuous_subtype_val.norm.pow 2
    have h2 : Continuous fun z : dataSpan (H := H) x => L (fun i => (z : H) (x i)) := by
      have hrw : (fun z : dataSpan (H := H) x => L (fun i => (z : H) (x i)))
          = fun z : dataSpan (H := H) x => L (Val (z : H)) := by
        funext z; rw [hVal]
      rw [hrw]
      exact hcontL.comp (Val.continuous.comp continuous_subtype_val)
    exact h1.add h2
  obtain ⟨z₀, -, hz₀min⟩ :=
    (isCompact_closedBall (0 : dataSpan (H := H) x) R).exists_isMinOn
      ⟨0, Metric.mem_closedBall_self (by linarith)⟩ hgcont.continuousOn
  refine ⟨(z₀ : H), fun f => ?_⟩
  change J (z₀ : H) ≤ J f
  have hz0le : J (z₀ : H) ≤ J (0 : H) := by
    have h := hz₀min (Metric.mem_closedBall_self (by linarith :
      (0:ℝ) ≤ R) : (0 : dataSpan (H := H) x) ∈ Metric.closedBall (0 : dataSpan (H := H) x) R)
    simpa using h
  by_cases hfR : R ≤ ‖f‖
  · linarith [hcoer f hfR]
  · rw [not_le] at hfR
    have hPmem : (dataSpan x).starProjection f ∈ dataSpan (H := H) x :=
      Submodule.starProjection_apply_mem _ f
    have hPnorm : ‖(dataSpan x).starProjection f‖ ≤ ‖f‖ :=
      Submodule.norm_starProjection_apply_le _ f
    have hPJ : J ((dataSpan x).starProjection f) ≤ J f := by
      simp only [hJdef, starProjection_dataSpan_apply]
      nlinarith [norm_nonneg f, norm_nonneg ((dataSpan (H := H) x).starProjection f)]
    have hmemball : (⟨(dataSpan x).starProjection f, hPmem⟩ : dataSpan (H := H) x)
        ∈ Metric.closedBall (0 : dataSpan (H := H) x) R := by
      have hd : dist (⟨(dataSpan x).starProjection f, hPmem⟩ : dataSpan (H := H) x) 0
          = ‖(dataSpan x).starProjection f‖ := by
        simp [Subtype.dist_eq]
      rw [Metric.mem_closedBall, hd]
      exact le_of_lt (lt_of_le_of_lt hPnorm hfR)
    have h : J (z₀ : H) ≤ J ((dataSpan x).starProjection f) := hz₀min hmemball
    linarith

omit [CompleteSpace H] in
/-- Uniqueness half of `representer_existsUnique_of_convex`: two minimizers are compared
at their midpoint, where convexity of `L` and the parallelogram law force `‖f − g‖ = 0`. -/
private lemma ridge_min_unique (x : Fin n → X) (L : (Fin n → 𝕜) → ℝ)
    (hL : ConvexOn ℝ Set.univ L) {f g : H}
    (hf : ∀ h : H, ‖f‖ ^ 2 + L (fun i => f (x i)) ≤ ‖h‖ ^ 2 + L (fun i => h (x i)))
    (hg : ∀ h : H, ‖g‖ ^ 2 + L (fun i => g (x i)) ≤ ‖h‖ ^ 2 + L (fun i => h (x i))) :
    f = g := by
  have hnorm2 : ‖(2 : 𝕜)⁻¹‖ = 1 / 2 := by
    rw [norm_inv, RCLike.norm_two]; norm_num
  set m : H := (2 : 𝕜)⁻¹ • (f + g) with hm
  have hmnorm : ‖m‖ = ‖f + g‖ / 2 := by rw [hm, norm_smul, hnorm2]; ring
  have hmval : (fun i => m (x i))
      = (1 / 2 : ℝ) • (fun i => f (x i)) + (1 / 2 : ℝ) • (fun i => g (x i)) := by
    funext i
    simp only [hm, RKHS.coe_smul, RKHS.coe_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul]
    push_cast
    ring
  have hLm : L (fun i => m (x i))
      ≤ (1 / 2 : ℝ) * L (fun i => f (x i)) + (1 / 2 : ℝ) * L (fun i => g (x i)) := by
    rw [hmval]
    exact hL.2 (Set.mem_univ _) (Set.mem_univ _) (by norm_num) (by norm_num) (by norm_num)
  have hJf := hf m
  have hfg : ‖f‖ ^ 2 + L (fun i => f (x i)) = ‖g‖ ^ 2 + L (fun i => g (x i)) :=
    le_antisymm (hf g) (hg f)
  have hsq : ‖m‖ ^ 2 = ‖f + g‖ ^ 2 / 4 := by rw [hmnorm]; ring
  have hpar : ‖f + g‖ ^ 2 + ‖f - g‖ ^ 2 = 2 * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
    simpa [sq] using parallelogram_law_with_norm 𝕜 f g
  have hzero : ‖f - g‖ ^ 2 ≤ 0 := by nlinarith
  have h0 : ‖f - g‖ = 0 := by nlinarith [norm_nonneg (f - g)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h0)

/-- **Existence and uniqueness for convex ridge losses**: with the regularizer `‖f‖²`
and `L` convex, the regularized empirical risk has a unique minimizer.  (Continuity of
`L` on the finite-dimensional value space is automatic from convexity.) -/
theorem representer_existsUnique_of_convex (x : Fin n → X) (L : (Fin n → 𝕜) → ℝ)
    -- USER-INPUT: convex loss (in the data values, over the real structure)
    (hL : ConvexOn ℝ Set.univ L) :
    ∃! f₀ : H, ∀ f : H, ‖f₀‖ ^ 2 + L (fun i => f₀ (x i))
      ≤ ‖f‖ ^ 2 + L (fun i => f (x i)) := by
  obtain ⟨f₀, hf₀⟩ := exists_ridge_min (H := H) x L hL
  exact ⟨f₀, hf₀, fun g hg => ridge_min_unique x L hL hg hf₀⟩

/-- The hinge loss `v ↦ ∑ᵢ max(0, 1 − λᵢ·vᵢ)` of the soft-margin classifier is convex,
so the soft-margin problem has a unique solution in the data span. -/
theorem convexOn_hinge (lab : Fin n → ℝ) :
    ConvexOn ℝ Set.univ fun v : Fin n → ℝ => ∑ i, max 0 (1 - lab i * v i) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hai : (1 : ℝ) - lab i * ((s • a + t • b) i)
      = s * (1 - lab i * a i) + t * (1 - lab i * b i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [hst]
  refine max_le ?_ ?_
  · have h1 : 0 ≤ s * max 0 (1 - lab i * a i) := mul_nonneg hs (le_max_left _ _)
    have h2 : 0 ≤ t * max 0 (1 - lab i * b i) := mul_nonneg ht (le_max_left _ _)
    linarith
  · rw [hai]
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) hs)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) ht)

end StatLean.NonparametricStatistics
