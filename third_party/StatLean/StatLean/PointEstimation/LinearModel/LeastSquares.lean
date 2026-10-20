module
public import StatLean.PointEstimation.LinearModel.Canonical
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Least squares: unbiased optimality in the original coordinates

The canonical-form optimality statements are transported back to the original observation
vector. With the mean vector `ξ` constrained to a subspace `W` and the variance `σ²`
unknown, the least-squares estimator `ξ̂ = P_W y` supplies the optimal unbiased estimator of
every linear functional of `ξ`, and the residual sum of squares supplies the optimal
unbiased estimator of `σ²`:

* `linearModelFull W` — the model with *both* `ξ ∈ W` and `σ² > 0` unknown;
* `inner_lse_eq_inner_starProjection` — `⟪γ, ξ̂⟫ = ⟪P_W γ, y⟫`, the identity that makes the
  least-squares functional a linear statistic;
* `isUMVU_lse_functional` — `y ↦ ⟪γ, ξ̂(y)⟫` is UMVU for `ξ ↦ ⟪γ, ξ⟫`;
* `isUMVU_residualSumSq` — `‖y − ξ̂(y)‖² / (n − dim W)` is UMVU for `σ²`;
* `isUMVU_linear_functional_of_mean` — transfer of the optimality to any parametrization
  whose coordinates are linear functions of the mean vector (the mechanism behind the
  regression forms, both of full rank and of deficient rank with side conditions).

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.4 (Normal
Linear Models), Theorem 4.8 (the least-squares projection is UMVU and MRE for the subspace
mean) and Theorem 4.10 (the general `s`-dimensional extension). (`TPE2 §3.4 Thm 4.8, Thm
4.10`.)

**Proof formalization notes.**
* *Estimand normalization.* The estimand is stated for `γ ∈ W`. This is no restriction:
  for `ξ ∈ W` one has `⟪γ, ξ⟫ = ⟪P_W γ, ξ⟫` and `⟪γ, ξ̂⟫ = ⟪P_W γ, ξ̂⟫`, so a general
  coefficient vector is replaced by its projection without changing either the estimand or
  the estimator.
* The intended proof route is the classical one: an orthogonal basis adapted to `W` carries
  `linearModelFull W` to `canonicalModel`, under which `⟪γ, ξ̂⟫` becomes a linear
  combination of the signal block and `‖y − ξ̂‖²` becomes the residual sum of squares; the
  conclusions are then the canonical-model statements pulled back.
* `n − dim W` is a real subtraction of casts (never truncated natural subtraction); the
  standing dimension condition `dim W < n` keeps it positive.

**Bibliographic comments.** Least squares and the optimality of its linear functionals are
due to C. F. Gauss (*Theoria combinationis observationum erroribus minimis obnoxiae*,
1821/1823) and A. A. Markov (*Wahrscheinlichkeitsrechnung*, Teubner, 1912); the
coordinate-free formulation used here follows W. Kruskal ("When are Gauss–Markov and least
squares estimators identical?" in *Essays in Probability and Statistics*, 1965),
H. Scheffé (*The Analysis of Variance*, Wiley, 1959) and C. R. Rao (*Linear Statistical
Inference and Its Applications*, 2nd ed., Wiley, 1973). The minimum-variance property in
the normal model rests on E. L. Lehmann and H. Scheffé ("Completeness, similar regions,
and unbiased estimation," *Sankhyā* **10** (1950), 305–340).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {n : ℕ}

/-- The **normal linear model with unknown variance**: the mean vector ranges over the
subspace `W` and the common variance ranges over the positive reals, both unknown. -/
noncomputable def linearModelFull (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (p : ↥W × PosVar) : Measure (EuclideanSpace ℝ (Fin n)) :=
  linearModel W p.2.1 p.1

/-- The least-squares functional is a **linear statistic**: `⟪γ, P_W y⟫ = ⟪P_W γ, y⟫`
(self-adjointness of the orthogonal projection). -/
theorem inner_lse_eq_inner_starProjection (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection] (γ y : EuclideanSpace ℝ (Fin n)) :
    ⟪γ, lse W y⟫_ℝ = ⟪W.starProjection γ, y⟫_ℝ := by
  show ⟪γ, W.starProjection y⟫_ℝ = ⟪W.starProjection γ, y⟫_ℝ
  rw [← Submodule.inner_starProjection_left_eq_right]

/-! ## Gaussian isometry-invariance (private scaffolding)

The optimality statements are transported to the canonical model by an orthonormal-basis
rotation. The measure-theoretic core is that the isotropic Gaussian vector is invariant
under an orthogonal change of coordinates: `(gaussianVector ξ σ²).map L = gaussianVector (L ξ)
σ²` for any linear isometry equivalence `L`. This is built from Mathlib's `stdGaussian_map`
(isometry invariance of the standard Gaussian) together with the affine representation of
`gaussianVector` as a scaled-and-shifted standard Gaussian. -/

/-- **Centered isotropic Gaussian vector as a scaled standard Gaussian.** -/
private lemma gaussianVector_zero_eq_map_smul_stdGaussian {N : ℕ} (σ2 : ℝ≥0) :
    gaussianVector (0 : EuclideanSpace ℝ (Fin N)) σ2
      = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin N))).map
          (fun z => (Real.sqrt (σ2 : ℝ)) • z) := by
  set a : ℝ := Real.sqrt (σ2 : ℝ) with ha
  have hmeas_toLp : Measurable (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) :=
    WithLp.measurable_toLp 2 _
  have hmeas_smul : Measurable (fun z : EuclideanSpace ℝ (Fin N) => a • z) :=
    measurable_const_smul a
  have hmeas_g : Measurable (fun x : Fin N → ℝ => fun i => a * x i) := by fun_prop
  have hcoord : (gaussianReal (0 : ℝ) 1).map (fun x => a * x) = gaussianReal 0 σ2 := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    apply NNReal.coe_injective
    simp [ha, Real.sq_sqrt (NNReal.coe_nonneg σ2)]
  haveI hsf : ∀ i : Fin N, SigmaFinite ((gaussianReal (0 : ℝ) 1).map (fun x => a * x)) := by
    intro _; rw [hcoord]; infer_instance
  -- rewrite the left-hand side into the same product-of-Gaussians form
  have hLHS : gaussianVector (0 : EuclideanSpace ℝ (Fin N)) σ2
      = (Measure.pi (fun _ : Fin N => gaussianReal (0 : ℝ) σ2)).map (WithLp.toLp 2) := rfl
  rw [hLHS, ← ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin N),
    Measure.map_map hmeas_smul hmeas_toLp]
  have hcomp : (fun z : EuclideanSpace ℝ (Fin N) => a • z) ∘
      (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      = (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) ∘ (fun x => fun i => a * x i) := by
    funext x; rfl
  rw [hcomp, ← Measure.map_map hmeas_toLp hmeas_g,
    Measure.pi_map_pi (f := fun (_ : Fin N) (c : ℝ) => a * c)
      (fun _ => (show Measurable (fun c : ℝ => a * c) by fun_prop).aemeasurable)]
  simp only [hcoord]

/-- **Translation of the Gaussian vector**: shifting by a constant shifts the mean. -/
private lemma gaussianVector_map_add_const {N : ℕ} (ξ b : EuclideanSpace ℝ (Fin N)) (σ2 : ℝ≥0) :
    (gaussianVector ξ σ2).map (fun z => z + b) = gaussianVector (ξ + b) σ2 := by
  have hmeas_toLp : Measurable (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) :=
    WithLp.measurable_toLp 2 _
  have hmeas_add : Measurable (fun z : EuclideanSpace ℝ (Fin N) => z + b) := by fun_prop
  have hmeas_g : Measurable (fun x : Fin N → ℝ => fun i => x i + b i) := by fun_prop
  have hcoord : ∀ i : Fin N,
      (gaussianReal (ξ i) σ2).map (fun x => x + b i) = gaussianReal (ξ i + b i) σ2 :=
    fun i => gaussianReal_map_add_const (b i)
  haveI hsf : ∀ i : Fin N, SigmaFinite ((gaussianReal (ξ i) σ2).map (fun x => x + b i)) := by
    intro i; rw [hcoord i]; infer_instance
  have hLHS : gaussianVector ξ σ2
      = (Measure.pi (fun i : Fin N => gaussianReal (ξ i) σ2)).map (WithLp.toLp 2) := rfl
  have hRHS : gaussianVector (ξ + b) σ2
      = (Measure.pi (fun i : Fin N => gaussianReal ((ξ + b) i) σ2)).map (WithLp.toLp 2) := rfl
  rw [hLHS, hRHS, Measure.map_map hmeas_add hmeas_toLp]
  have hcomp : (fun z : EuclideanSpace ℝ (Fin N) => z + b) ∘
      (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N))
      = (WithLp.toLp 2 : (Fin N → ℝ) → EuclideanSpace ℝ (Fin N)) ∘ (fun x => fun i => x i + b i) := by
    funext x; rfl
  rw [hcomp, ← Measure.map_map hmeas_toLp hmeas_g,
    Measure.pi_map_pi (f := fun (i : Fin N) (c : ℝ) => c + b i)
      (fun i => (show Measurable (fun c : ℝ => c + b i) by fun_prop).aemeasurable)]
  simp only [hcoord]
  rfl

open scoped RealInnerProductSpace in
/-- **Gaussian isometry invariance.** The isotropic Gaussian vector transforms covariantly
under an orthogonal change of coordinates. This is the measure-theoretic core enabling the
transport of the linear-model optimality statements to the canonical form. -/
lemma gaussianVector_map_linearIsometryEquiv {N₁ N₂ : ℕ}
    (L : EuclideanSpace ℝ (Fin N₁) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N₂))
    (ξ : EuclideanSpace ℝ (Fin N₁)) (σ2 : ℝ≥0) :
    (gaussianVector ξ σ2).map L = gaussianVector (L ξ) σ2 := by
  have hLmeas : Measurable (L : EuclideanSpace ℝ (Fin N₁) → EuclideanSpace ℝ (Fin N₂)) :=
    L.continuous.measurable
  have hsmul₁ : Measurable (fun z : EuclideanSpace ℝ (Fin N₁) => Real.sqrt (σ2 : ℝ) • z) :=
    measurable_const_smul _
  have hsmul₂ : Measurable (fun z : EuclideanSpace ℝ (Fin N₂) => Real.sqrt (σ2 : ℝ) • z) :=
    measurable_const_smul _
  have haddξ : Measurable (fun z : EuclideanSpace ℝ (Fin N₁) => z + ξ) := by fun_prop
  -- rotation invariance of the centred vector
  have hrot : (gaussianVector (0 : EuclideanSpace ℝ (Fin N₁)) σ2).map L
      = gaussianVector (0 : EuclideanSpace ℝ (Fin N₂)) σ2 := by
    rw [gaussianVector_zero_eq_map_smul_stdGaussian, Measure.map_map hLmeas hsmul₁]
    have hcomm : (L : EuclideanSpace ℝ (Fin N₁) → EuclideanSpace ℝ (Fin N₂)) ∘
        (fun z => Real.sqrt (σ2 : ℝ) • z)
        = (fun z : EuclideanSpace ℝ (Fin N₂) => Real.sqrt (σ2 : ℝ) • z) ∘ L := by
      funext z; simp [map_smul]
    rw [hcomm, ← Measure.map_map hsmul₂ hLmeas, ProbabilityTheory.stdGaussian_map L,
      ← gaussianVector_zero_eq_map_smul_stdGaussian]
  -- decompose the general vector into rotation ∘ translation
  have hξ : gaussianVector ξ σ2
      = (gaussianVector (0 : EuclideanSpace ℝ (Fin N₁)) σ2).map (fun z => z + ξ) := by
    rw [gaussianVector_map_add_const, zero_add]
  rw [hξ, Measure.map_map hLmeas haddξ]
  have hcomm : (L : EuclideanSpace ℝ (Fin N₁) → EuclideanSpace ℝ (Fin N₂)) ∘ (fun z => z + ξ)
      = (fun z : EuclideanSpace ℝ (Fin N₂) => z + L ξ) ∘ L := by
    funext z; simp [map_add]
  rw [hcomm, ← Measure.map_map (by fun_prop) hLmeas, hrot,
    gaussianVector_map_add_const, zero_add]

/-- **Transport of `IsUMVU` along a measurable equivalence of the sample space.** If the
model `P` pushes forward to `Q` under `e`, then a UMVU estimator for `Q` pulls back to a UMVU
estimator for `P`: unbiasedness and `L²`-membership transfer along the change of variables,
and the variance-minimality transfers because competitors correspond bijectively. -/
private theorem isUMVU_map_equiv {Θ 𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]
    {P : Θ → Measure 𝓧} {Q : Θ → Measure 𝓨} (e : 𝓧 ≃ᵐ 𝓨)
    (hPQ : ∀ θ, (P θ).map e = Q θ)
    {g : Θ → ℝ} {δ : 𝓨 → ℝ} (h : IsUMVU Q g δ) :
    IsUMVU P g (fun x => δ (e x)) := by
  obtain ⟨hunb, hL2, hmin⟩ := h
  have hemeas : Measurable e := e.measurable
  have hδae : ∀ θ, AEStronglyMeasurable δ ((P θ).map e) := by
    intro θ; rw [hPQ θ]; exact (hL2 θ).aestronglyMeasurable
  have hPθ' : ∀ θ', P θ' = (Q θ').map e.symm := by
    intro θ'; rw [← hPQ θ', Measure.map_map e.symm.measurable hemeas]; simp
  refine ⟨fun θ => ?_, fun θ => ?_, fun δ' hunb' hL2' θ => ?_⟩
  · rw [← integral_map hemeas.aemeasurable (hδae θ), hPQ θ]
    exact hunb θ
  · have hm : MemLp δ 2 ((P θ).map e) := by rw [hPQ θ]; exact hL2 θ
    exact (memLp_map_measure_iff (hδae θ) hemeas.aemeasurable).mp hm
  · -- competitor `δ'` on `𝓧` corresponds to `δ' ∘ e.symm` on `𝓨`
    have hL2Y : ∀ θ', MemLp (fun y => δ' (e.symm y)) 2 (Q θ') := by
      intro θ'
      have hm : MemLp δ' 2 ((Q θ').map e.symm) := by rw [← hPθ' θ']; exact hL2' θ'
      exact (memLp_map_measure_iff (hPθ' θ' ▸ (hL2' θ').aestronglyMeasurable)
        e.symm.measurable.aemeasurable).mp hm
    have hunbY : IsUnbiased Q g (fun y => δ' (e.symm y)) := by
      intro θ'
      rw [← integral_map e.symm.measurable.aemeasurable
            (hPθ' θ' ▸ (hL2' θ').aestronglyMeasurable), ← hPθ' θ']
      exact hunb' θ'
    have hkey := hmin (fun y => δ' (e.symm y)) hunbY hL2Y θ
    have hv1 : variance (fun x => δ (e x)) (P θ) = variance δ (Q θ) := by
      rw [← hPQ θ]; exact (variance_map_equiv δ e).symm
    have hv2 : variance δ' (P θ) = variance (fun y => δ' (e.symm y)) (Q θ) := by
      rw [← hPQ θ, variance_map_equiv (fun y => δ' (e.symm y)) e]
      congr 1; funext x; simp
    rw [hv1, hv2]; exact hkey

/-- Reparametrization transport of `IsUMVU` along a surjective reindexing of the parameter. -/
private theorem isUMVU_reparam' {Θ Θ' 𝓧 : Type*} [MeasurableSpace 𝓧]
    (P : Θ → Measure 𝓧) (φ : Θ' → Θ) (hφ : Function.Surjective φ)
    (g : Θ → ℝ) (δ : 𝓧 → ℝ) (h : IsUMVU P g δ) :
    IsUMVU (fun t => P (φ t)) (fun t => g (φ t)) δ := by
  obtain ⟨hunb, hL2, hmin⟩ := h
  refine ⟨fun t => hunb (φ t), fun t => hL2 (φ t), ?_⟩
  intro δ' hunb' hL2' t
  have hunbP : IsUnbiased P g δ' := fun θ => by obtain ⟨t', rfl⟩ := hφ θ; exact hunb' t'
  have hL2P : MemEstL2 P δ' := fun θ => by obtain ⟨t', rfl⟩ := hφ θ; exact hL2' t'
  exact hmin δ' hunbP hL2P (φ t)

open scoped RealInnerProductSpace in
/-- **Adapted-basis rotation to canonical coordinates (remaining geometric brick).** An
orthonormal change of coordinates `L` carrying the mean subspace `W` onto the canonical head
subspace, together with the four consequences needed to transport the canonical-model
optimality statements. This isolates the *only* remaining debt behind `isUMVU_lse_functional`
and `isUMVU_residualSumSq`: the measure-theoretic core (Gaussian isometry invariance,
`gaussianVector_map_linearIsometryEquiv`, and the `IsUMVU` sample transport,
`isUMVU_map_equiv`) is proved above, 0-sorry. -/
lemma exists_headSubspace_isometry (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection] (hW : Module.finrank ℝ W < n) :
    ∃ (m : ℕ) (_ : 0 < m) (_ : Module.finrank ℝ W + m = n)
      (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
          EuclideanSpace ℝ (Fin (Module.finrank ℝ W + m))),
      (∀ x ∈ W, L x = canonicalMean (canonicalHead (L x))) ∧
      Function.Surjective (fun x : ↥W => canonicalHead (L (x : EuclideanSpace ℝ (Fin n)))) ∧
      (∀ y, canonicalRSS (L y) = residualSumSq W y) ∧
      (∀ γ ∈ W, ∀ y, ⟪γ, lse W y⟫_ℝ
        = ∑ i, canonicalHead (L γ) i * canonicalHead (L y) i) := by
  classical
  -- Build an orthonormal basis whose first `s = finrank W` vectors are an orthonormal basis of
  -- `W` and whose last `m = finrank Wᗮ` vectors are an orthonormal basis of `Wᗮ`; the isometry
  -- `L` is its Riesz representation. The four facts read off the block structure.
  set s := Module.finrank ℝ W with hs
  set m := Module.finrank ℝ Wᗮ with hm
  have hsum : s + m = n := by
    have h := W.finrank_add_finrank_orthogonal
    rw [finrank_euclideanSpace_fin] at h
    exact h
  have hmpos : 0 < m := by omega
  let bW : OrthonormalBasis (Fin s) ℝ ↥W := stdOrthonormalBasis ℝ W
  let bP : OrthonormalBasis (Fin m) ℝ ↥Wᗮ := stdOrthonormalBasis ℝ Wᗮ
  set g : Fin (s + m) → EuclideanSpace ℝ (Fin n) :=
    Fin.append (fun i => (bW i : EuclideanSpace ℝ (Fin n)))
      (fun j => (bP j : EuclideanSpace ℝ (Fin n))) with hgdef
  have hne : ∀ (a : Fin s) (b : Fin m), Fin.castAdd m a ≠ Fin.natAdd s b := by
    intro a b hh
    have ha := a.isLt
    have h2 : (Fin.castAdd m a).val = (Fin.natAdd s b).val := by rw [hh]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h2
    omega
  have hgon : Orthonormal ℝ g := by
    rw [orthonormal_iff_ite]
    intro i j
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · simp only [hgdef, Fin.append_left, ← Submodule.coe_inner]
      by_cases h : i' = j'
      · subst h; rw [orthonormal_iff_ite.mp bW.orthonormal i' i', if_pos rfl, if_pos rfl]
      · rw [orthonormal_iff_ite.mp bW.orthonormal i' j', if_neg h,
          if_neg (fun hc => h (Fin.castAdd_injective _ _ hc))]
    · simp only [hgdef, Fin.append_left, Fin.append_right]
      rw [Submodule.inner_right_of_mem_orthogonal (SetLike.coe_mem (bW i'))
            (SetLike.coe_mem (bP j')), if_neg (hne i' j')]
    · simp only [hgdef, Fin.append_left, Fin.append_right]
      rw [Submodule.inner_left_of_mem_orthogonal (SetLike.coe_mem (bW j'))
            (SetLike.coe_mem (bP i')), if_neg (hne j' i').symm]
    · simp only [hgdef, Fin.append_right, ← Submodule.coe_inner]
      by_cases h : i' = j'
      · subst h; rw [orthonormal_iff_ite.mp bP.orthonormal i' i', if_pos rfl, if_pos rfl]
      · rw [orthonormal_iff_ite.mp bP.orthonormal i' j', if_neg h,
          if_neg (fun hc => h (Fin.natAdd_injective _ _ hc))]
  haveI : Nonempty (Fin (s + m)) := ⟨⟨0, by omega⟩⟩
  have hcard : Fintype.card (Fin (s + m))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [Fintype.card_fin, finrank_euclideanSpace_fin]; exact hsum
  let ob : OrthonormalBasis (Fin (s + m)) ℝ (EuclideanSpace ℝ (Fin n)) :=
    (basisOfOrthonormalOfCardEqFinrank hgon hcard).toOrthonormalBasis
      (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hgon)
  have hob : ⇑ob = g := by
    show ⇑((basisOfOrthonormalOfCardEqFinrank hgon hcard).toOrthonormalBasis _) = g
    rw [Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]
  have hLapp : ∀ (v : EuclideanSpace ℝ (Fin n)) (k : Fin (s + m)),
      ob.repr v k = ⟪g k, v⟫_ℝ := by
    intro v k
    rw [OrthonormalBasis.repr_apply_apply, hob]
  have hhead : ∀ (v : EuclideanSpace ℝ (Fin n)) (i : Fin s),
      canonicalHead (ob.repr v) i = ⟪(bW i : EuclideanSpace ℝ (Fin n)), v⟫_ℝ := by
    intro v i
    show ob.repr v (Fin.castAdd m i) = _
    rw [hLapp v (Fin.castAdd m i)]
    simp only [hgdef, Fin.append_left]
  have hres : ∀ (v : EuclideanSpace ℝ (Fin n)) (j : Fin m),
      ob.repr v (Fin.natAdd s j) = ⟪(bP j : EuclideanSpace ℝ (Fin n)), v⟫_ℝ := by
    intro v j
    rw [hLapp v (Fin.natAdd s j)]
    simp only [hgdef, Fin.append_right]
  refine ⟨m, hmpos, hsum, ob.repr, ?_, ?_, ?_, ?_⟩
  · -- fact 1: `L x` has vanishing residual block for `x ∈ W`
    intro x hx
    ext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · show ob.repr x (Fin.castAdd m i)
        = (canonicalMean (canonicalHead (ob.repr x))) (Fin.castAdd m i)
      rw [show (canonicalMean (canonicalHead (ob.repr x))) (Fin.castAdd m i)
            = Fin.append (canonicalHead (ob.repr x)) (0 : Fin m → ℝ) (Fin.castAdd m i) from rfl,
          Fin.append_left]
      rfl
    · show ob.repr x (Fin.natAdd s j)
        = (canonicalMean (canonicalHead (ob.repr x))) (Fin.natAdd s j)
      rw [show (canonicalMean (canonicalHead (ob.repr x))) (Fin.natAdd s j)
            = Fin.append (canonicalHead (ob.repr x)) (0 : Fin m → ℝ) (Fin.natAdd s j) from rfl,
          Fin.append_right, Pi.zero_apply, hres x j]
      exact Submodule.inner_left_of_mem_orthogonal hx (SetLike.coe_mem (bP j))
  · -- fact 2: surjectivity of the head block on `W`
    intro t
    refine ⟨bW.repr.symm ((WithLp.toLp 2 : (Fin s → ℝ) → EuclideanSpace ℝ (Fin s)) t), ?_⟩
    funext i
    show canonicalHead (ob.repr
        ((bW.repr.symm ((WithLp.toLp 2 : (Fin s → ℝ) → EuclideanSpace ℝ (Fin s)) t) :
          EuclideanSpace ℝ (Fin n)))) i = t i
    rw [hhead, ← Submodule.coe_inner, ← OrthonormalBasis.repr_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
  · -- fact 3: the residual sum of squares
    intro y
    have hcoord : ∀ j : Fin m,
        ob.repr y (Fin.natAdd s j)
          = ⟪(bP j : EuclideanSpace ℝ (Fin n)), y - W.starProjection y⟫_ℝ := by
      intro j
      rw [hres y j, inner_sub_right,
        Submodule.inner_left_of_mem_orthogonal (W.starProjection_apply_mem y)
          (SetLike.coe_mem (bP j)), sub_zero]
    have hnorm : ∑ j : Fin m,
        ⟪(bP j : EuclideanSpace ℝ (Fin n)), y - W.starProjection y⟫_ℝ ^ 2
          = ‖y - W.starProjection y‖ ^ 2 :=
      OrthonormalBasis.sum_sq_inner_right bP
        (⟨y - W.starProjection y, Submodule.sub_starProjection_mem_orthogonal y⟩ : ↥Wᗮ)
    show ∑ j : Fin m, (ob.repr y (Fin.natAdd s j)) ^ 2 = residualSumSq W y
    rw [show residualSumSq W y = ‖y - W.starProjection y‖ ^ 2 from rfl, ← hnorm]
    exact Finset.sum_congr rfl (fun j _ => by rw [hcoord j])
  · -- fact 4: the least-squares functional
    intro γ hγ y
    have hproj : W.starProjection y
        = ∑ i, ⟪(bW i : EuclideanSpace ℝ (Fin n)), y⟫_ℝ • (bW i : EuclideanSpace ℝ (Fin n)) := by
      rw [Submodule.starProjection_apply, bW.orthogonalProjection_apply_eq_sum y,
        Submodule.coe_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [Submodule.coe_smul])
    rw [show lse W y = W.starProjection y from rfl, hproj, inner_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_smul_right, hhead γ i, hhead y i,
      real_inner_comm γ (bW i : EuclideanSpace ℝ (Fin n)), mul_comm]

/-- **Optimality of the least-squares functional**: with the mean vector constrained to `W`
and the variance unknown, `y ↦ ⟪γ, ξ̂(y)⟫` is the UMVU estimator of `ξ ↦ ⟪γ, ξ⟫`. -/
theorem isUMVU_lse_functional (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model, without which the variance is not estimable
    (hW : Module.finrank ℝ W < n)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional, taken
    -- inside the mean subspace (see the estimand-normalization note above)
    {γ : EuclideanSpace ℝ (Fin n)} (hγ : γ ∈ W) :
    IsUMVU (linearModelFull W) (fun p => ⟪γ, (p.1 : EuclideanSpace ℝ (Fin n))⟫_ℝ)
      (fun y => ⟪γ, lse W y⟫_ℝ) := by
  -- Rotate onto the canonical model by the adapted-basis isometry `L`, reducing to
  -- `isUMVU_linear_combination` via the reparametrization + sample-transport lemmas.
  obtain ⟨m, hm, hsm, L, hmean, hsurj, _, hlse⟩ := exists_headSubspace_isometry W hW
  have hφsurj : Function.Surjective
      (fun p : ↥W × PosVar =>
        ((canonicalHead (L p.1), p.2) : CanonicalParam (Module.finrank ℝ W))) := by
    rintro ⟨a, σ2⟩; obtain ⟨x, hx⟩ := hsurj a; exact ⟨(x, σ2), by simp [hx]⟩
  have hPQ : ∀ p : ↥W × PosVar,
      (linearModelFull W p).map L.toHomeomorph.toMeasurableEquiv
        = canonicalModel (canonicalHead (L p.1), p.2) := by
    intro p
    have hmap : (gaussianVector (p.1 : EuclideanSpace ℝ (Fin n)) p.2.1).map
          L.toHomeomorph.toMeasurableEquiv
        = gaussianVector (L (p.1 : EuclideanSpace ℝ (Fin n))) p.2.1 :=
      gaussianVector_map_linearIsometryEquiv L (p.1 : EuclideanSpace ℝ (Fin n)) p.2.1
    show (gaussianVector (p.1 : EuclideanSpace ℝ (Fin n)) p.2.1).map
        L.toHomeomorph.toMeasurableEquiv = _
    rw [hmap]
    show gaussianVector (L (p.1 : EuclideanSpace ℝ (Fin n))) p.2.1
      = gaussianVector (canonicalMean (canonicalHead (L (p.1 : EuclideanSpace ℝ (Fin n))))) p.2.1
    congr 1
    exact hmean (p.1 : EuclideanSpace ℝ (Fin n)) p.1.2
  have hrep := isUMVU_reparam' (canonicalModel (s := Module.finrank ℝ W) (m := m))
    (fun p : ↥W × PosVar => (canonicalHead (L p.1), p.2)) hφsurj
    (fun q => ∑ i, canonicalHead (L γ) i * q.1 i)
    (fun z => ∑ i, canonicalHead (L γ) i * canonicalHead z i)
    (isUMVU_linear_combination (s := Module.finrank ℝ W) (m := m) hm (canonicalHead (L γ)))
  have htrans := isUMVU_map_equiv L.toHomeomorph.toMeasurableEquiv hPQ hrep
  have hgm : (fun p : ↥W × PosVar => ⟪γ, (p.1 : EuclideanSpace ℝ (Fin n))⟫_ℝ)
      = fun p => ∑ i, canonicalHead (L γ) i * canonicalHead (L (p.1 : _)) i := by
    funext p
    have hself : lse W (p.1 : EuclideanSpace ℝ (Fin n)) = (p.1 : EuclideanSpace ℝ (Fin n)) :=
      Submodule.starProjection_eq_self_iff.mpr p.1.2
    conv_lhs => rw [← hself]
    exact hlse γ hγ (p.1 : EuclideanSpace ℝ (Fin n))
  have hgδ : (fun y => ⟪γ, lse W y⟫_ℝ)
      = fun y => ∑ i, canonicalHead (L γ) i
          * canonicalHead (L.toHomeomorph.toMeasurableEquiv y) i := by
    funext y
    rw [show L.toHomeomorph.toMeasurableEquiv y = L y from rfl]
    exact hlse γ hγ y
  rw [hgm, hgδ]
  exact htrans

/-- **Optimality of the residual variance estimator**: `‖y − ξ̂(y)‖²/(n − dim W)` is the
UMVU estimator of `σ²`. -/
theorem isUMVU_residualSumSq (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model
    (hW : Module.finrank ℝ W < n) :
    IsUMVU (linearModelFull W) (fun p => (p.2.1 : ℝ))
      (fun y => residualSumSq W y / ((n : ℝ) - (Module.finrank ℝ W : ℝ))) := by
  -- Rotate onto the canonical model by the adapted-basis isometry `L`, reducing to
  -- `isUMVU_residual_variance` via the reparametrization + sample-transport lemmas.
  obtain ⟨m, hm, hsm, L, hmean, hsurj, hRSS, _⟩ := exists_headSubspace_isometry W hW
  have hφsurj : Function.Surjective
      (fun p : ↥W × PosVar =>
        ((canonicalHead (L p.1), p.2) : CanonicalParam (Module.finrank ℝ W))) := by
    rintro ⟨a, σ2⟩; obtain ⟨x, hx⟩ := hsurj a; exact ⟨(x, σ2), by simp [hx]⟩
  have hPQ : ∀ p : ↥W × PosVar,
      (linearModelFull W p).map L.toHomeomorph.toMeasurableEquiv
        = canonicalModel (canonicalHead (L p.1), p.2) := by
    intro p
    have hmap : (gaussianVector (p.1 : EuclideanSpace ℝ (Fin n)) p.2.1).map
          L.toHomeomorph.toMeasurableEquiv
        = gaussianVector (L (p.1 : EuclideanSpace ℝ (Fin n))) p.2.1 :=
      gaussianVector_map_linearIsometryEquiv L (p.1 : EuclideanSpace ℝ (Fin n)) p.2.1
    show (gaussianVector (p.1 : EuclideanSpace ℝ (Fin n)) p.2.1).map
        L.toHomeomorph.toMeasurableEquiv = _
    rw [hmap]
    show gaussianVector (L (p.1 : EuclideanSpace ℝ (Fin n))) p.2.1
      = gaussianVector (canonicalMean (canonicalHead (L (p.1 : EuclideanSpace ℝ (Fin n))))) p.2.1
    congr 1
    exact hmean (p.1 : EuclideanSpace ℝ (Fin n)) p.1.2
  have hrep := isUMVU_reparam' (canonicalModel (s := Module.finrank ℝ W) (m := m))
    (fun p : ↥W × PosVar => (canonicalHead (L p.1), p.2)) hφsurj
    (fun q => (q.2.1 : ℝ)) (fun z => canonicalRSS z / (m : ℝ))
    (isUMVU_residual_variance (s := Module.finrank ℝ W) (m := m) hm)
  have htrans := isUMVU_map_equiv L.toHomeomorph.toMeasurableEquiv hPQ hrep
  have hns : (n : ℝ) - (Module.finrank ℝ W : ℝ) = (m : ℝ) := by
    have : (Module.finrank ℝ W : ℝ) + (m : ℝ) = (n : ℝ) := by exact_mod_cast hsm
    linarith
  have hfinal : (fun y => residualSumSq W y / ((n : ℝ) - (Module.finrank ℝ W : ℝ)))
      = fun y => canonicalRSS (L.toHomeomorph.toMeasurableEquiv y) / (m : ℝ) := by
    funext y
    rw [show L.toHomeomorph.toMeasurableEquiv y = L y from rfl, hRSS y, hns]
  rw [hfinal]
  exact htrans

/-- **Transfer of optimality along a linear reparametrization**: if an estimand `T` agrees
on the mean subspace with a linear functional of the mean vector, then evaluating `T` at
the least-squares estimator gives the UMVU estimator of `T(ξ)`.

This is the mechanism by which the optimality statements extend from the mean vector to
regression coefficients: coefficients defined by a design of full row rank, and
coefficients defined by a deficient-rank design together with identifying side conditions,
are in both cases linear functions of the mean vector. -/
theorem isUMVU_linear_functional_of_mean (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    [W.HasOrthogonalProjection]
    -- USER-INPUT: the mean subspace is a proper subspace (`s < n`); standing dimension
    -- condition of the model
    (hW : Module.finrank ℝ W < n)
    (T : EuclideanSpace ℝ (Fin n) → ℝ) {γ : EuclideanSpace ℝ (Fin n)}
    -- USER-INPUT: on the mean subspace the estimand is the linear functional `⟪γ, ·⟫`;
    -- this is what the identification of a regression parametrization supplies
    (hT : ∀ ζ ∈ W, T ζ = ⟪γ, ζ⟫_ℝ) :
    IsUMVU (linearModelFull W) (fun p => T (p.1 : EuclideanSpace ℝ (Fin n)))
      (fun y => T (lse W y)) := by
  -- On the mean subspace, `T` agrees with the inner product against the *projected* vector
  -- `P_W γ ∈ W`; the statement is then a relabelling of `isUMVU_lse_functional`.
  have hkey : ∀ ζ ∈ W, T ζ = ⟪W.starProjection γ, ζ⟫_ℝ := by
    intro ζ hζ
    rw [hT ζ hζ, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hζ]
  have hbase := isUMVU_lse_functional W hW (γ := W.starProjection γ) (W.starProjection_apply_mem γ)
  have hg : (fun p : ↥W × PosVar => T (p.1 : EuclideanSpace ℝ (Fin n)))
      = fun p => ⟪W.starProjection γ, (p.1 : EuclideanSpace ℝ (Fin n))⟫_ℝ := by
    funext p; exact hkey _ p.1.2
  have hδ : (fun y => T (lse W y)) = fun y => ⟪W.starProjection γ, lse W y⟫_ℝ := by
    funext y; exact hkey _ (W.starProjection_apply_mem y)
  rw [hg, hδ]; exact hbase

end StatLean.PointEstimation
