module
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-!
# Parseval frames in a Hilbert space

A family `{f_i}` in a Hilbert space `E` is a **Parseval frame** if the first Parseval
identity `‖h‖² = ∑ᵢ |⟪f_i, h⟫|²` holds for all `h` — orthonormality and even linear
independence are *not* required.  We prove the standard characterizations:

* the projection of an orthonormal basis of `E` onto a closed subspace `M` is a Parseval
  frame for `M`;
* `{f_i}` is a Parseval frame iff the analysis operator `h ↦ (⟪f_i, h⟫)ᵢ` is a
  well-defined isometry into `ℓ²(ι)`, iff the reconstruction formula
  `h = ∑ᵢ ⟪f_i, h⟫ • f_i` holds;
* the polarized Parseval identity `⟪h₁, h₂⟫ = ∑ᵢ ⟪h₁, f_i⟫ ⟪f_i, h₂⟫`;
* (dilation) every Parseval frame is the compression of an orthonormal basis of a larger
  Hilbert space: there is an isometry `V : E → ℓ²(ι)` with `V* (δ_i) = f_i`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.1, Definition 2.6 (Parseval frames), Proposition 2.7 (compressions of
orthonormal bases), Proposition 2.8 (analysis-operator and reconstruction characterizations),
Proposition 2.9 (the Han–Larson dilation).

**Proof formalization notes.** Frames are defined by the unordered `HasSum` Parseval identity; the
analysis operator lands in `lp (fun _ : ι => 𝕜) 2` and the equivalence of the three
characterizations goes through `Memℓp` of the coefficient family plus the `lp`-norm/`HasSum`
dictionary. The dilation (Proposition 2.9) is stated via the adjoint on the canonical basis,
`V.toContinuousLinearMap.adjoint (lp.single 2 i 1) = f i`, which requires `[DecidableEq ι]` for
`lp.single`.

**Bibliographic comments.** Frames originate with R. J. Duffin and A. C. Schaeffer,
*A class of nonharmonic Fourier series*, Trans. Amer. Math. Soc. **72** (1952), 341–366.
The dilation theorem is due to D. Han and D. R. Larson, *Frames, bases and group
representations*, Mem. Amer. Math. Soc. **147** (2000), no. 697.
-/

open ComplexConjugate
open scoped InnerProductSpace ENNReal

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- **Parseval frame**: a family `f : ι → E` such that `‖h‖² = ∑ᵢ |⟪f_i, h⟫|²`
(unordered sum) for every `h ∈ E`. -/
def IsParsevalFrame (f : ι → E) : Prop :=
  ∀ h : E, HasSum (fun i => ‖⟪f i, h⟫_𝕜‖ ^ 2) (‖h‖ ^ 2)

/-- `⟪h, f i⟫ · ⟪f i, h⟫` is the real scalar `‖⟪f i, h⟫‖²`. -/
private theorem inner_mul_inner_self (f : ι → E) (h : E) (i : ι) :
    ⟪h, f i⟫_𝕜 * ⟪f i, h⟫_𝕜 = ((‖⟪f i, h⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← inner_conj_symm (𝕜 := 𝕜) (f i) h, RCLike.mul_conj, RCLike.norm_conj]
  norm_cast

/-- `⟪h, h⟫` is the real scalar `‖h‖²`. -/
private theorem inner_self_ofReal (h : E) : ⟪h, h⟫_𝕜 = ((‖h‖ ^ 2 : ℝ) : 𝕜) := by
  rw [inner_self_eq_norm_sq_to_K]; push_cast; ring

/-- The real Parseval identity at `h` is equivalent to its `𝕜`-valued (polarized at
`h₁ = h₂ = h`) form. -/
private theorem hasSum_sq_iff {f : ι → E} {h : E} :
    HasSum (fun i => ‖⟪f i, h⟫_𝕜‖ ^ 2) (‖h‖ ^ 2) ↔
      HasSum (fun i => ⟪h, f i⟫_𝕜 * ⟪f i, h⟫_𝕜) ⟪h, h⟫_𝕜 := by
  constructor
  · intro H
    have := H.mapL (RCLike.ofRealCLM (K := 𝕜))
    simpa only [Function.comp_def, RCLike.ofRealCLM_apply, inner_mul_inner_self,
      inner_self_ofReal] using this
  · intro H
    have := H.mapL (RCLike.reCLM (K := 𝕜))
    simpa only [Function.comp_def, RCLike.reCLM_apply, inner_mul_inner_self, inner_self_ofReal,
      RCLike.ofReal_re] using this

/-- The defining `HasSum` of the `ℓ²` norm, specialized to `p = 2`. -/
private theorem lp2_hasSum_sq (x : lp (fun _ : ι => 𝕜) 2) :
    HasSum (fun i => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
  have h2 : (0:ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  simpa using lp.hasSum_norm h2 x

/-- An orthonormal basis (as a Hilbert basis) is a Parseval frame. -/
theorem HilbertBasis.isParsevalFrame [CompleteSpace E] (e : HilbertBasis ι 𝕜 E) :
    IsParsevalFrame 𝕜 (e : ι → E) :=
  fun h => hasSum_sq_iff.2 (e.hasSum_inner_mul_inner h h)

/-- **Compressions of orthonormal bases are Parseval frames**: the orthogonal projection
of a Hilbert basis of `E` onto a closed subspace `M` is a Parseval frame for `M`. -/
theorem isParsevalFrame_orthogonalProjection [CompleteSpace E]
    (e : HilbertBasis ι 𝕜 E) (M : Submodule 𝕜 E) [CompleteSpace M] :
    IsParsevalFrame 𝕜 fun i => M.orthogonalProjection (e i) := by
  intro h
  have := HilbertBasis.isParsevalFrame (𝕜 := 𝕜) e (h : E)
  simpa using this

/-- A Parseval frame is norm-bounded by `1`. -/
theorem IsParsevalFrame.norm_le_one {f : ι → E} (hf : IsParsevalFrame 𝕜 f) (i : ι) :
    ‖f i‖ ≤ 1 := by
  have H := hf (f i)
  have hle := le_hasSum H i (fun j _ => by positivity)
  rw [inner_self_ofReal] at hle
  rw [RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at hle
  nlinarith [norm_nonneg (f i), sq_nonneg (‖f i‖ - 1), sq_nonneg (‖f i‖ + 1)]

/-- **Analysis-operator characterization**: `f` is a Parseval frame iff
`h ↦ (⟪f_i, h⟫)ᵢ` is a well-defined linear isometry into `ℓ²(ι)`. -/
theorem isParsevalFrame_iff_exists_isometry {f : ι → E} :
    IsParsevalFrame 𝕜 f
      ↔ ∃ V : E →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2, ∀ h i, V h i = ⟪f i, h⟫_𝕜 := by
  constructor
  · intro hf
    have hmem : ∀ h : E, Memℓp (fun i => ⟪f i, h⟫_𝕜) 2 := by
      intro h
      refine memℓp_gen ?_
      simpa using (hf h).summable
    let L : E →ₗ[𝕜] lp (fun _ : ι => 𝕜) 2 :=
      { toFun := fun h => ⟨fun i => ⟪f i, h⟫_𝕜, hmem h⟩
        map_add' := by intro x y; ext i; simp only [inner_add_right]; rfl
        map_smul' := by intro c x; ext i; simp [inner_smul_right, Pi.smul_apply] }
    have hL : ∀ (h : E) (i : ι), (L h) i = ⟪f i, h⟫_𝕜 := fun _ _ => rfl
    have hnorm : ∀ h : E, ‖L h‖ = ‖h‖ := by
      intro h
      have h1 := lp2_hasSum_sq (L h)
      simp only [hL] at h1
      have h2 := h1.unique (hf h)
      rw [← Real.sqrt_sq (norm_nonneg (L h)), h2, Real.sqrt_sq (norm_nonneg h)]
    exact ⟨⟨L, hnorm⟩, hL⟩
  · rintro ⟨V, hV⟩ h
    have := lp2_hasSum_sq (V h)
    simpa [hV] using this

/-- The adjoint of the analysis operator sends the canonical `ℓ²` basis vector `δ_i` to the
frame vector `f i`. -/
private theorem adjoint_single [CompleteSpace E] [DecidableEq ι] {f : ι → E}
    (V : E →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2) (hV : ∀ h i, V h i = ⟪f i, h⟫_𝕜) (i : ι) :
    ContinuousLinearMap.adjoint V.toContinuousLinearMap (lp.single 2 i (1 : 𝕜)) = f i := by
  refine ext_inner_right 𝕜 fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left, RCLike.inner_apply]
  simp [hV]

/-- The adjoint of the analysis operator is a left inverse of it. -/
private theorem adjoint_analysis_apply [CompleteSpace E]
    (V : E →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2) (h : E) :
    ContinuousLinearMap.adjoint V.toContinuousLinearMap (V h) = h := by
  refine ext_inner_right 𝕜 fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact V.inner_map_map h v

/-- **Reconstruction formula**: for a Parseval frame, `h = ∑ᵢ ⟪f_i, h⟫ • f_i`
(unordered norm convergence). -/
theorem IsParsevalFrame.hasSum_reconstruction [CompleteSpace E] {f : ι → E}
    (hf : IsParsevalFrame 𝕜 f) (h : E) :
    HasSum (fun i => ⟪f i, h⟫_𝕜 • f i) h := by
  classical
  obtain ⟨V, hV⟩ := isParsevalFrame_iff_exists_isometry.1 hf
  have hs := (lp.hasSum_single (p := 2) (by norm_num) (V h)).mapL
    (ContinuousLinearMap.adjoint V.toContinuousLinearMap)
  rw [adjoint_analysis_apply V h] at hs
  convert hs using 2 with i
  have e1 : lp.single 2 i (V h i)
      = (V h i) • (lp.single 2 i (1 : 𝕜) : lp (fun _ : ι => 𝕜) 2) := by
    rw [← lp.single_smul]; simp
  rw [e1, map_smul, adjoint_single V hV i, hV]

/-- Conversely, the reconstruction formula for all vectors makes `f` a Parseval frame. -/
theorem isParsevalFrame_of_hasSum_reconstruction [CompleteSpace E] {f : ι → E}
    (hrec : ∀ h : E, HasSum (fun i => ⟪f i, h⟫_𝕜 • f i) h) :
    IsParsevalFrame 𝕜 f := by
  intro h
  refine hasSum_sq_iff.2 ?_
  have := (hrec h).mapL (innerSL 𝕜 h)
  simpa [inner_smul_right, mul_comm] using this

/-- **Polarized Parseval identity** for a Parseval frame:
`⟪h₁, h₂⟫ = ∑ᵢ ⟪h₁, f_i⟫ · ⟪f_i, h₂⟫`. -/
theorem IsParsevalFrame.hasSum_inner [CompleteSpace E] {f : ι → E}
    (hf : IsParsevalFrame 𝕜 f) (h₁ h₂ : E) :
    HasSum (fun i => ⟪h₁, f i⟫_𝕜 * ⟪f i, h₂⟫_𝕜) ⟪h₁, h₂⟫_𝕜 := by
  obtain ⟨V, hV⟩ := isParsevalFrame_iff_exists_isometry.1 hf
  have H := lp.hasSum_inner (𝕜 := 𝕜) (G := fun _ : ι => 𝕜) (V h₁) (V h₂)
  rw [V.inner_map_map] at H
  convert H using 2 with i
  rw [hV, hV, RCLike.inner_apply, inner_conj_symm]
  ring

/-- **Dilation (Han–Larson)**: every Parseval frame for `E` is the compression of the
canonical orthonormal basis of `ℓ²(ι)`: there is a linear isometry `V : E → ℓ²(ι)`
whose adjoint maps the canonical basis vectors to the frame vectors. -/
theorem IsParsevalFrame.exists_dilation [CompleteSpace E] [DecidableEq ι] {f : ι → E}
    (hf : IsParsevalFrame 𝕜 f) :
    ∃ V : E →ₗᵢ[𝕜] lp (fun _ : ι => 𝕜) 2,
      ∀ i, V.toContinuousLinearMap.adjoint (lp.single 2 i (1 : 𝕜)) = f i := by
  obtain ⟨V, hV⟩ := isParsevalFrame_iff_exists_isometry.1 hf
  exact ⟨V, adjoint_single V hV⟩

end StatLean.NonparametricStatistics
