module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.IsonormalProcess
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.SubgaussianGaussian
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.GaussianChaining
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.Carrier
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.GPNet
public import Mathlib

@[expose] public section

/-!
# The isonormal `F`-indexed Gaussian process `gpX`

This file builds the candidate limit process `G_P` of the abstract-Donsker theory
(van der Vaart, *Asymptotic Statistics* §18.1, §19.2) as a genuine, jointly
measurable family of random variables indexed by `↥F`, realised on the i.i.d.
standard-Gaussian product space `iidStdGaussian` of the isonormal construction.

## Mathematical content

The `P`-Brownian-bridge process is the centred Gaussian process `(G_P f)_{f ∈ F}`
with covariance `Cov(G_P f, G_P g) = P(fg) − Pf · Pg`, i.e. the covariance of the
centred functions `f − Pf` in `L²(P)`. We realise it as the **isonormal process**
`W : H →ₗᵢ[ℝ] L²(iidStdGaussian)` applied to the embedding of each centred
`f − Pf` into the closed subspace `H ⊆ L²(P)` spanned by the centred members of
`F`. The isonormal process preserves inner products, so

  `Cov(W (f−Pf), W (g−Pg)) = ⟪f − Pf, g − Pg⟫_{L²(P)} = P(fg) − Pf·Pg`,

which is exactly the Brownian-bridge covariance.

## Construction

* `centredLp f` — the centred function `f − ∫ f ∂P` as an element of `L²(P)`.
* `gpH` — the closed subspace of `L²(P)` spanned by `{centredLp f : f ∈ F}`.
* `gpEmbed f` — the embedding `↥F → ↥gpH` of each member of `F`.
* `gpBasis` — a `ℕ`-indexed Hilbert basis of `gpH` (from the infinite-
  dimensionality + separability hypotheses).
* `gpX f` — the measurable representative of `isonormal gpBasis (gpEmbed f)`, a
  genuine measurable map `(ℕ → ℝ) → ℝ`.

## Main results

* `gpX_measurable` — each `gpX f` is measurable.
* `gpX_hasGaussianLaw` — each `gpX f` has a Gaussian law under `iidStdGaussian`.
* `gpX_cov` — `∫ gpX f · gpX g = P(fg) − Pf·Pg`, the Brownian-bridge covariance.

## Hypotheses

The construction assumes `hF_meas` (measurability of `F`'s members), `hH_inf`
(infinite-dimensionality of the centred span), and `hH_sep` (separability of the
centred span). Thus `gpH` is a separable infinite-dimensional Hilbert space, the
setting of `HilbertBasis.exists_hilbertBasis_nat`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §18.1, §19.2.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory IsonormalProcess
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {F : Set (Ω → ℝ)} {P : Measure Ω} [IsProbabilityMeasure P]
variable (hF_env : ∃ G, IsEnvelope F G ∧ MemLp G 2 P)
variable (hF_meas : ∀ f ∈ F, Measurable f)

/-! ## The centred `L²` element -/

include hF_env hF_meas in
/-- The centred member `f − ∫ f ∂P` of `F` is in `L²(P)`: `f ∈ L²(P)`
(`memLp_of_mem_F`) and the constant `∫ f ∂P` is in `L²(P)` on a probability
measure (`memLp_const`), so their difference is too (`MemLp.sub`). -/
theorem memLp_centred {f : Ω → ℝ} (hf : f ∈ F) :
    MemLp (fun x => f x - ∫ y, f y ∂P) 2 P := by
  obtain ⟨G, hG_env, hG⟩ := hF_env
  have hfLp : MemLp f 2 P := memLp_of_mem_F hG_env hG hF_meas hf
  have hc : MemLp (fun _ : Ω => ∫ y, f y ∂P) 2 P := memLp_const _
  exact hfLp.sub hc

/-- The centred member of `F` packaged as an element of `L²(P)`. -/
def centredLp (f : ↥F) : Lp ℝ 2 P :=
  (memLp_centred hF_env hF_meas f.2).toLp _

/-! ## The centred span `gpH` and its Hilbert structure -/

/-- The closed subspace of `L²(P)` spanned by the centred members of `F`. The
isonormal process will be built on this space; its inner product reproduces the
Brownian-bridge covariance. -/
def gpH : Submodule ℝ (Lp ℝ 2 P) :=
  (Submodule.span ℝ (Set.range (fun f : ↥F => centredLp hF_env hF_meas f))).topologicalClosure

instance instIsClosedGpH : IsClosed (gpH hF_env hF_meas : Set (Lp ℝ 2 P)) := by
  rw [gpH]; exact Submodule.isClosed_topologicalClosure _

/-- The embedding `↥F → ↥gpH` sending `f` to the (centred) `L²` element
`f − Pf`, which lies in the span (hence in its closure `gpH`). -/
def gpEmbed (f : ↥F) : ↥(gpH hF_env hF_meas) :=
  ⟨centredLp hF_env hF_meas f, subset_closure (Submodule.subset_span ⟨f, rfl⟩)⟩

/-- `gpEmbed f`, as an ambient `L²(P)` element, is `centredLp f`. -/
@[simp] theorem coe_gpEmbed (f : ↥F) :
    ((gpEmbed hF_env hF_meas f : ↥(gpH hF_env hF_meas)) : Lp ℝ 2 P)
      = centredLp hF_env hF_meas f := rfl

/-! ## The Hilbert basis and the process

The span `gpH` of the centred members is a closed subspace of `L²(P)`, hence a
real Hilbert space (`Submodule.innerProductSpace` + `CompleteSpace`). Under the
infinite-dimensionality and separability hypotheses it admits a `ℕ`-indexed
Hilbert basis (`HilbertBasis.exists_hilbertBasis_nat`), and we run the isonormal
construction over that basis. -/

variable (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH hF_env hF_meas))
variable (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH hF_env hF_meas))

/-- A `ℕ`-indexed Hilbert basis of the centred span `gpH`. Exists because `gpH`
is a separable infinite-dimensional real Hilbert space
(`HilbertBasis.exists_hilbertBasis_nat`). -/
def gpBasis (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH hF_env hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH hF_env hF_meas)) :
    HilbertBasis ℕ ℝ ↥(gpH hF_env hF_meas) := by
  haveI hcl : IsClosed (gpH hF_env hF_meas : Set (Lp ℝ 2 P)) := by
    rw [gpH]; exact Submodule.isClosed_topologicalClosure _
  haveI hcs : CompleteSpace ↥(gpH hF_env hF_meas) := hcl.completeSpace_coe
  letI : TopologicalSpace.SeparableSpace ↥(gpH hF_env hF_meas) := hH_sep
  exact (@HilbertBasis.exists_hilbertBasis_nat ↥(gpH hF_env hF_meas) _ _ hcs hH_sep hH_inf).some

/-- **The isonormal `F`-indexed Gaussian process `G_P`** as a genuine measurable
family `↥F → (ℕ → ℝ) → ℝ`. For each `f`, `gpX f` is the measurable representative
(`.mk`) of the isonormal image `W (f − Pf)`, an element of `L²(iidStdGaussian)`. -/
def gpX (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH hF_env hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH hF_env hF_meas)) (f : ↥F) :
    (ℕ → ℝ) → ℝ :=
  (Lp.aestronglyMeasurable
    (isonormal (gpBasis hF_env hF_meas hH_inf hH_sep) (gpEmbed hF_env hF_meas f))).mk

/-! ## Measurability, a.e. identification, Gaussian law -/

/-- Each `gpX f` is measurable. -/
theorem gpX_measurable (f : ↥F) :
    Measurable (gpX hF_env hF_meas hH_inf hH_sep f) := by
  rw [gpX]
  exact (Lp.aestronglyMeasurable
    (isonormal (gpBasis hF_env hF_meas hH_inf hH_sep) (gpEmbed hF_env hF_meas f))).measurable_mk

/-- `gpX f` agrees a.e. with the isonormal image `W (f − Pf)`. -/
theorem gpX_aeeq (f : ↥F) :
    gpX hF_env hF_meas hH_inf hH_sep f
      =ᵐ[iidStdGaussian]
      ⇑(isonormal (gpBasis hF_env hF_meas hH_inf hH_sep) (gpEmbed hF_env hF_meas f)) := by
  rw [gpX]
  exact ((Lp.aestronglyMeasurable
    (isonormal (gpBasis hF_env hF_meas hH_inf hH_sep) (gpEmbed hF_env hF_meas f))).ae_eq_mk).symm

/-- **Gaussian law of `gpX f`.** Each `gpX f` has a Gaussian law under
`iidStdGaussian`: the isonormal image `W (f − Pf)` does
(`isonormal_hasGaussianLaw`), and `gpX f` agrees with it a.e.
(`HasGaussianLaw.congr`). -/
theorem gpX_hasGaussianLaw (f : ↥F) :
    HasGaussianLaw (gpX hF_env hF_meas hH_inf hH_sep f) iidStdGaussian :=
  (isonormal_hasGaussianLaw (gpBasis hF_env hF_meas hH_inf hH_sep)
    (gpEmbed hF_env hF_meas f)).congr (gpX_aeeq hF_env hF_meas hH_inf hH_sep f).symm

/-! ## Covariance: the Brownian-bridge structure -/

include hF_env hF_meas in
/-- The inner product of two centred `L²` elements is the covariance of the
underlying functions: `⟪f − Pf, g − Pg⟫_{L²(P)} = P(fg) − Pf·Pg`. Expand the
product `(f − Pf)(g − Pg)` and integrate, using `∫ (Pf) ∂P = Pf` (prob. measure)
and linearity of the integral. -/
theorem inner_centredLp (f g : ↥F) :
    (⟪centredLp hF_env hF_meas f, centredLp hF_env hF_meas g⟫ : ℝ)
      = (∫ x, (f : Ω → ℝ) x * (g : Ω → ℝ) x ∂P)
        - (∫ x, (f : Ω → ℝ) x ∂P) * (∫ x, (g : Ω → ℝ) x ∂P) := by
  -- L² inner product as an integral of the pointwise product.
  rw [L2.inner_def]
  -- abbreviations for the two centred functions
  set cf : ℝ := ∫ y, (f : Ω → ℝ) y ∂P with hcf
  set cg : ℝ := ∫ y, (g : Ω → ℝ) y ∂P with hcg
  -- L²-membership of f, g (for integrability bookkeeping)
  obtain ⟨G, hG_env, hG⟩ := id hF_env
  have hfLp : MemLp (f : Ω → ℝ) 2 P := memLp_of_mem_F hG_env hG hF_meas f.2
  have hgLp : MemLp (g : Ω → ℝ) 2 P := memLp_of_mem_F hG_env hG hF_meas g.2
  have hf_int : Integrable (f : Ω → ℝ) P := hfLp.integrable (by norm_num)
  have hg_int : Integrable (g : Ω → ℝ) P := hgLp.integrable (by norm_num)
  -- the integrand of the L² inner product equals (f − cf)(g − cg) a.e.
  have hpt : (fun a => (⟪(centredLp hF_env hF_meas f : Lp ℝ 2 P) a,
        (centredLp hF_env hF_meas g : Lp ℝ 2 P) a⟫ : ℝ))
      =ᵐ[P] fun x => ((f : Ω → ℝ) x - cf) * ((g : Ω → ℝ) x - cg) := by
    have hcoef : (⇑(centredLp hF_env hF_meas f) : Ω → ℝ)
        =ᵐ[P] fun x => (f : Ω → ℝ) x - cf :=
      (memLp_centred hF_env hF_meas f.2).coeFn_toLp
    have hcoeg : (⇑(centredLp hF_env hF_meas g) : Ω → ℝ)
        =ᵐ[P] fun x => (g : Ω → ℝ) x - cg :=
      (memLp_centred hF_env hF_meas g.2).coeFn_toLp
    filter_upwards [hcoef, hcoeg] with x hx hy
    -- ⟪a, b⟫_ℝ for reals reduces to multiplication (in flipped order, §7.2)
    change (centredLp hF_env hF_meas g : Lp ℝ 2 P) x
        * (centredLp hF_env hF_meas f : Lp ℝ 2 P) x = _
    rw [hx, hy]
    ring
  rw [integral_congr_ae hpt]
  -- expand the product and integrate term by term
  have hexp : (fun x => ((f : Ω → ℝ) x - cf) * ((g : Ω → ℝ) x - cg))
      = fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x
          - cg * (f : Ω → ℝ) x - cf * (g : Ω → ℝ) x + cf * cg := by
    funext x; ring
  rw [hexp]
  -- integrability of each piece
  have hfg_int : Integrable (fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x) P :=
    hfLp.integrable_mul hgLp
  have h1 : Integrable (fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x - cg * (f : Ω → ℝ) x) P :=
    hfg_int.sub (hf_int.const_mul cg)
  have h2 : Integrable (fun x => (f : Ω → ℝ) x * (g : Ω → ℝ) x
      - cg * (f : Ω → ℝ) x - cf * (g : Ω → ℝ) x) P :=
    h1.sub (hg_int.const_mul cf)
  rw [integral_add h2 (integrable_const _),
      integral_sub h1 (hg_int.const_mul cf),
      integral_sub hfg_int (hf_int.const_mul cg),
      integral_const_mul, integral_const_mul, integral_const]
  -- ∫ f = cf, ∫ g = cg, and ∫ 1 = 1 (probability measure)
  rw [← hcf, ← hcg]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

/-- **Covariance of the `F`-indexed Gaussian process** (Brownian-bridge form):
`∫ gpX f · gpX g ∂iidStdGaussian = P(fg) − Pf·Pg`.

Proof chain: `gpX f =ᵐ W (f−Pf)` (×2) gives the integral over the isonormal
images; `isonormal_cov` reduces that to the `gpH`-inner product `⟪f−Pf, g−Pg⟫`;
the subspace inner product is the ambient `L²(P)` inner product
(`Submodule.coe_inner`), which `inner_centredLp` evaluates to `P(fg) − Pf·Pg`. -/
theorem gpX_cov (f g : ↥F) :
    ∫ ω, gpX hF_env hF_meas hH_inf hH_sep f ω
        * gpX hF_env hF_meas hH_inf hH_sep g ω ∂iidStdGaussian
      = (∫ x, (f : Ω → ℝ) x * (g : Ω → ℝ) x ∂P)
        - (∫ x, (f : Ω → ℝ) x ∂P) * (∫ x, (g : Ω → ℝ) x ∂P) := by
  set b := gpBasis hF_env hF_meas hH_inf hH_sep with hb
  -- replace gpX by the isonormal images a.e.
  have haef := gpX_aeeq hF_env hF_meas hH_inf hH_sep f
  have haeg := gpX_aeeq hF_env hF_meas hH_inf hH_sep g
  have hpt : (fun ω => gpX hF_env hF_meas hH_inf hH_sep f ω
        * gpX hF_env hF_meas hH_inf hH_sep g ω)
      =ᵐ[iidStdGaussian]
      fun ω => (isonormal b (gpEmbed hF_env hF_meas f) ω)
        * (isonormal b (gpEmbed hF_env hF_meas g) ω) := by
    filter_upwards [haef, haeg] with ω hf hg
    rw [hf, hg]
  rw [integral_congr_ae hpt]
  -- isonormal covariance = gpH-inner product = ambient L²(P) inner product
  rw [isonormal_cov b (gpEmbed hF_env hF_meas f) (gpEmbed hF_env hF_meas g)]
  rw [Submodule.coe_inner]
  -- the underlying ambient elements are the centred L² functions
  rw [coe_gpEmbed, coe_gpEmbed]
  rw [inner_centredLp hF_env hF_meas f g]

/-! ## Helper C: the centred-embedding norm is dominated by the `L²` distance -/

/-- **`L²` norm as a real square-root integral.** For `MemLp f 2 P`, the real
`Lp`-norm `(eLpNorm f 2 P).toReal` equals `√(∫ f² ∂P)`, by
`MemLp.eLpNorm_eq_integral_rpow_norm`. -/
private theorem eLpNorm_toReal_eq_sqrt_integral_sq {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (eLpNorm f 2 μ).toReal = Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have h_int_eq :
      (fun ω => ‖f ω‖ ^ (2 : ℝ≥0∞).toReal) = (fun ω => f ω ^ 2) := by
    funext ω; rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h_int_eq]
  have h_int_nn : 0 ≤ ∫ ω, f ω ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _), h2, Real.sqrt_eq_rpow]
  norm_num

include hF_env hF_meas in
/-- **Centring is `L²`-norm-nonincreasing.** The `gpH`-norm of the difference of
two centred embeddings is at most the raw `L²(P)` distance of the underlying
functions: `‖gpEmbed s − gpEmbed t‖ ≤ distL2 P s t`.

Mathematically: writing `Y := s − t` and `c := ∫ Y ∂P`, the underlying function
of `gpEmbed s − gpEmbed t` is `Y − c` (centring), so
`‖gpEmbed s − gpEmbed t‖ = √(∫ (Y − c)² ∂P)` and `distL2 P s t = √(∫ Y² ∂P)`.
Expanding `∫ (Y − c)² = ∫ Y² − c²  ≤ ∫ Y²` (since `c = ∫ Y`) and applying
`Real.sqrt_le_sqrt` gives the claim. This is the only genuinely analytic input
feeding the sub-Gaussian proxy of the increments. -/
theorem norm_gpEmbed_sub_le (s t : ↥F) :
    ‖gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t‖
      ≤ distL2 P (s : Ω → ℝ) (t : Ω → ℝ) := by
  obtain ⟨G, hG_env, hG⟩ := id hF_env
  -- L²-membership of `Y := s − t` and the centred difference.
  have hsLp : MemLp (s : Ω → ℝ) 2 P := memLp_of_mem_F hG_env hG hF_meas s.2
  have htLp : MemLp (t : Ω → ℝ) 2 P := memLp_of_mem_F hG_env hG hF_meas t.2
  set Y : Ω → ℝ := fun x => (s : Ω → ℝ) x - (t : Ω → ℝ) x with hY
  set c : ℝ := ∫ x, Y x ∂P with hc
  have hYLp : MemLp Y 2 P := hsLp.sub htLp
  have hYc : MemLp (fun x => Y x - c) 2 P := hYLp.sub (memLp_const _)
  have hY_int : Integrable Y P := hYLp.integrable (by norm_num)
  -- the underlying fn of `centredLp s − centredLp t` is `Y − c` a.e.
  have hcoe : ⇑(centredLp hF_env hF_meas s - centredLp hF_env hF_meas t)
      =ᵐ[P] fun x => Y x - c := by
    have hs := (memLp_centred hF_env hF_meas s.2).coeFn_toLp
    have ht := (memLp_centred hF_env hF_meas t.2).coeFn_toLp
    have hsub := MeasureTheory.Lp.coeFn_sub
      (centredLp hF_env hF_meas s) (centredLp hF_env hF_meas t)
    filter_upwards [hs, ht, hsub] with x hsx htx hsubx
    rw [hsubx, Pi.sub_apply]
    -- `centredLp` is defeq to the `MemLp.toLp`; expose it so `hsx`/`htx` apply.
    change (centredLp hF_env hF_meas s : Lp ℝ 2 P) x
        - (centredLp hF_env hF_meas t : Lp ℝ 2 P) x = Y x - c
    rw [show (centredLp hF_env hF_meas s : Lp ℝ 2 P) x
          = (memLp_centred hF_env hF_meas s.2).toLp _ x from rfl,
        show (centredLp hF_env hF_meas t : Lp ℝ 2 P) x
          = (memLp_centred hF_env hF_meas t.2).toLp _ x from rfl,
        hsx, htx]
    -- close the pointwise identity: `(↑s x − ∫↑s) − (↑t x − ∫↑t) = (↑s x − ↑t x) − ∫(↑s − ↑t)`.
    simp only [hY, hc]
    rw [MeasureTheory.integral_sub (hsLp.integrable (by norm_num))
        (htLp.integrable (by norm_num))]
    ring
  -- Step 1: rewrite the embedding norm as `√(∫ (Y − c)² ∂P)`.
  have hnorm_centred : ‖gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t‖
      = Real.sqrt (∫ x, (Y x - c) ^ 2 ∂P) := by
    rw [Submodule.coe_norm, Submodule.coe_sub, coe_gpEmbed, coe_gpEmbed,
        Lp.norm_def, MeasureTheory.eLpNorm_congr_ae hcoe,
        eLpNorm_toReal_eq_sqrt_integral_sq hYc]
  -- Step 2: rewrite the `L²` distance as `√(∫ Y² ∂P)`.
  have hdist : distL2 P (s : Ω → ℝ) (t : Ω → ℝ) = Real.sqrt (∫ x, Y x ^ 2 ∂P) := by
    rw [distL2]
    have hYeq : (s : Ω → ℝ) - (t : Ω → ℝ) = Y := by funext x; rfl
    rw [hYeq, eLpNorm_toReal_eq_sqrt_integral_sq hYLp]
  rw [hnorm_centred, hdist]
  -- Step 3: `∫ (Y − c)² ≤ ∫ Y²`, then `Real.sqrt_le_sqrt`.
  apply Real.sqrt_le_sqrt
  -- expand `(Y − c)² = Y² + (−2c·Y + c²)` and integrate term by term.
  have hYsq : Integrable (fun x => Y x ^ 2) P := by
    have := hYLp.integrable_sq; simpa [pow_two] using this
  have hlin : Integrable (fun x => (-(2 * c)) * Y x + c ^ 2) P :=
    (hY_int.const_mul (-(2 * c))).add (integrable_const _)
  have hexp : (fun x => (Y x - c) ^ 2)
      = fun x => Y x ^ 2 + ((-(2 * c)) * Y x + c ^ 2) := by funext x; ring
  have hinteq : (∫ x, (Y x - c) ^ 2 ∂P) = (∫ x, Y x ^ 2 ∂P) - c ^ 2 := by
    rw [hexp, MeasureTheory.integral_add hYsq hlin,
        MeasureTheory.integral_add (hY_int.const_mul (-(2 * c))) (integrable_const _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    rw [← hc]; ring
  rw [hinteq]
  nlinarith [sq_nonneg c]
  -- Note: the final RHS `∫ (s − t)²` matches `∫ Y²` definitionally (`Y = s − t`).

/-! ## Sub-Gaussian increments -/

/-- **Sub-Gaussian increments of `gpX`.** The increment `gpX f − gpX g` has a
centred Gaussian law of variance `‖gpEmbed f − gpEmbed g‖²`, hence is sub-Gaussian
with proxy variance `(distL2 P f g)²` (using `norm_gpEmbed_sub_le`). -/
theorem gpX_subgaussian_increment (s t : ↥F) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => gpX hF_env hF_meas hH_inf hH_sep s ω
        - gpX hF_env hF_meas hH_inf hH_sep t ω)
      ⟨(distL2 P (s : Ω → ℝ) (t : Ω → ℝ)) ^ 2, sq_nonneg _⟩ iidStdGaussian := by
  set b := gpBasis hF_env hF_meas hH_inf hH_sep with hb
  set h' := gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t with hh'
  -- Step 1: the increment agrees a.e. with the isonormal image of `h'`.
  have haeeq : (fun ω => gpX hF_env hF_meas hH_inf hH_sep s ω
        - gpX hF_env hF_meas hH_inf hH_sep t ω)
      =ᵐ[iidStdGaussian] ⇑(isonormal b h') := by
    have haf := gpX_aeeq hF_env hF_meas hH_inf hH_sep s
    have hat := gpX_aeeq hF_env hF_meas hH_inf hH_sep t
    have hmap : (isonormal b) h' = (isonormal b) (gpEmbed hF_env hF_meas s)
        - (isonormal b) (gpEmbed hF_env hF_meas t) := by rw [hh', map_sub]
    have hsub := MeasureTheory.Lp.coeFn_sub
      ((isonormal b) (gpEmbed hF_env hF_meas s))
      ((isonormal b) (gpEmbed hF_env hF_meas t))
    filter_upwards [haf, hat, hsub] with ω hfω htω hsubω
    rw [hfω, htω, hmap, hsubω, Pi.sub_apply]
  -- Step 2+3: the pushforward law of the increment is `N(0, ‖h'‖²)`.
  have hmeas_diff : Measurable (fun ω => gpX hF_env hF_meas hH_inf hH_sep s ω
      - gpX hF_env hF_meas hH_inf hH_sep t ω) :=
    (gpX_measurable hF_env hF_meas hH_inf hH_sep s).sub
      (gpX_measurable hF_env hF_meas hH_inf hH_sep t)
  have hlaw : iidStdGaussian.map (fun ω => gpX hF_env hF_meas hH_inf hH_sep s ω
        - gpX hF_env hF_meas hH_inf hH_sep t ω)
      = gaussianReal 0 ⟨‖h'‖ ^ 2, sq_nonneg _⟩ := by
    rw [Measure.map_congr haeeq, isonormal_map_eq_gaussianReal b h']
  -- Step 4: sub-Gaussian with proxy `‖h'‖²`.
  have hSG := hasSubgaussianMGF_of_map_eq_gaussianReal hmeas_diff.aemeasurable hlaw
  -- Step 5: weaken the proxy to `(distL2 P s t)²` using `norm_gpEmbed_sub_le`.
  refine hSG.mono_proxy ?_
  -- `‖h'‖² ≤ (distL2 P s t)²` (square both sides of `norm_gpEmbed_sub_le`).
  have hle : ‖h'‖ ≤ distL2 P (s : Ω → ℝ) (t : Ω → ℝ) := by
    rw [hh']; exact norm_gpEmbed_sub_le hF_env hF_meas s t
  refine NNReal.coe_le_coe.mp ?_
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- **`L²`-norm of the increment is bounded by the `L²` distance.** Since
`gpX s − gpX t` agrees a.e. with the isonormal image `W h'` (`h' = gpEmbed s −
gpEmbed t`), and `W` is an isometry into `L²(iidStdGaussian)`, the `eLpNorm` of the
increment equals `‖h'‖_H`, which is `≤ distL2 P s t` by `norm_gpEmbed_sub_le`. -/
theorem eLpNorm_gpX_sub_le (s t : ↥F) :
    eLpNorm (fun ω => gpX hF_env hF_meas hH_inf hH_sep s ω
        - gpX hF_env hF_meas hH_inf hH_sep t ω) 2 iidStdGaussian
      ≤ ENNReal.ofReal (distL2 P (s : Ω → ℝ) (t : Ω → ℝ)) := by
  set b := gpBasis hF_env hF_meas hH_inf hH_sep with hb
  set h' := gpEmbed hF_env hF_meas s - gpEmbed hF_env hF_meas t with hh'
  -- the increment agrees a.e. with the isonormal image of `h'` (same as in
  -- `gpX_subgaussian_increment`).
  have haeeq : (fun ω => gpX hF_env hF_meas hH_inf hH_sep s ω
        - gpX hF_env hF_meas hH_inf hH_sep t ω)
      =ᵐ[iidStdGaussian] ⇑(isonormal b h') := by
    have haf := gpX_aeeq hF_env hF_meas hH_inf hH_sep s
    have hat := gpX_aeeq hF_env hF_meas hH_inf hH_sep t
    have hmap : (isonormal b) h' = (isonormal b) (gpEmbed hF_env hF_meas s)
        - (isonormal b) (gpEmbed hF_env hF_meas t) := by rw [hh', map_sub]
    have hsub := MeasureTheory.Lp.coeFn_sub
      ((isonormal b) (gpEmbed hF_env hF_meas s))
      ((isonormal b) (gpEmbed hF_env hF_meas t))
    filter_upwards [haf, hat, hsub] with ω hfω htω hsubω
    rw [hfω, htω, hmap, hsubω, Pi.sub_apply]
  -- `eLpNorm (increment) = eLpNorm (W h')`; the latter's `.toReal` is the `Lp` norm.
  rw [eLpNorm_congr_ae haeeq]
  -- `eLpNorm (W h') 2 μ = ofReal ‖W h'‖`, and `‖W h'‖ = ‖h'‖ ≤ distL2 P s t`.
  have hfin : eLpNorm (⇑(isonormal b h')) 2 iidStdGaussian ≠ ⊤ :=
    (Lp.memLp (isonormal b h')).eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  rw [show (eLpNorm (⇑(isonormal b h')) 2 iidStdGaussian).toReal
        = ‖isonormal b h'‖ from (Lp.norm_def _).symm,
      isonormal_norm]
  rw [hh']; exact norm_gpEmbed_sub_le hF_env hF_meas s t

/-! ## Almost-sure uniform continuity from Gaussian chaining -/

/-- **A.s. uniformly continuous, bounded paths of `gpX` on a dense countable
skeleton.** Instantiating the Gaussian chaining theorem `gaussianChaining_UC` for
the `F`-indexed process `gpX` on the `distL2`-pseudometric space `↥F`:

* the sub-Gaussian increments come from `gpX_subgaussian_increment` (proxy
  `(distL2 f g)² = 1² · dist f g ²` under the `distL2PseudoMetric` `letI`);
* the Dudley dyadic net + summability come from `exists_dudley_net` (finite
  bracketing-entropy integral).

The conclusion is a countable dense `T₀ ⊆ ↥F` on which, almost surely, the path
`f ↦ gpX f ω` is bounded and uniformly continuous. The hypothesis
`hF_ne : F.Nonempty` supplies the nonempty carrier needed for the dense
skeleton. -/
theorem gpX_aeUC {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty) :
    letI inst := distL2PseudoMetric hG_env hG hF_meas
    ∃ T₀ : Set ↥F, T₀.Countable
        ∧ @Dense ↥F inst.toUniformSpace.toTopologicalSpace T₀ ∧
      (∀ᵐ ω ∂iidStdGaussian,
        (BddAbove (Set.range
          (fun t : T₀ => |gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω|))) ∧
        @UniformContinuousOn ↥F ℝ inst.toUniformSpace _
          (fun t => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω) T₀) := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  obtain ⟨net, hnet, hmono, hDud⟩ := exists_dudley_net hF_ent hF_ne
  refine _root_.GaussianChaining.gaussianChaining_UC (μ := iidStdGaussian) (K := 1) zero_le_one
    (gpX_measurable ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep) net hnet hmono
    (fun s t => ?_) hDud
  -- Sub-Gaussian proxy: `dist s t = distL2 P s t` (defeq under the `letI`), and the
  -- chaining wants `⟨1² · dist s t², _⟩ = ⟨distL2 P s t², _⟩` (`1² · x = x`).
  refine (gpX_subgaussian_increment ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep s t).mono_proxy ?_
  refine NNReal.coe_le_coe.mp ?_
  -- `dist s t = distL2 P ↑s ↑t` (defeq under the `@[reducible]` pseudometric `letI`).
  change distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2 ≤ 1 ^ 2 * distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2
  rw [one_pow, one_mul]

/-! ## The bounded `ℓ∞(F)`-valued path `gpPath`

`gpX f ω` is, for each fixed `f`, a measurable representative; but the naive path
`fun f => gpX f ω` is not a.s. bounded over all of `↥F` (each `gpX f` is an
arbitrary `.mk` representative, so the uncountable supremum is uncontrolled).

We build the genuine path as the **uniformly-continuous extension** of the
restriction of `f ↦ gpX f ω` to the countable dense skeleton `T₀` produced by
`gpX_aeUC`. On the good set (where that restriction is bounded and uniformly
continuous on `T₀`), the extension is uniformly continuous on the totally-bounded
space `↥F`, hence bounded, hence an element of `ℓ∞(F)`. Off the good set, the path
is `0`. -/

section GpPath

variable {G : Ω → ℝ} (hG_env : IsEnvelope F G) (hG : MemLp G 2 P)

/-- The **Dudley dyadic net** of `(↥F, distL2 P)` used to build the skeleton: the
`Classical.choose` of `exists_dudley_net`. Fixed independently of `ω`. The skeleton
`gpSkeleton` is its dyadic union `⋃ j, net j`, used for the chaining modulus in
`PBridgeTight`. -/
def gpSkeletonNet (hF_meas : ∀ f ∈ F, Measurable f)
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty) : ℕ → Finset ↥F :=
  (exists_dudley_net hF_ent hF_ne).choose

/-- The countable dense skeleton `T₀ = ⋃ j, gpSkeletonNet j ⊆ ↥F`, defined as the
dyadic union of the Dudley net. The identity `gpSkeleton = ⋃ j, net j` is used in
the chaining-modulus argument in `PBridgeTight`. -/
def gpSkeleton (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty) : Set ↥F :=
  ⋃ j : ℕ, (↑(gpSkeletonNet hF_meas hF_ent hF_ne j) : Set ↥F)

/-- **Net–skeleton alignment.** The skeleton is the dyadic union of its net by
definition. -/
theorem gpSkeleton_eq_iUnion_net (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty) :
    gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      = ⋃ j : ℕ, (↑(gpSkeletonNet hF_meas hF_ent hF_ne j) : Set ↥F) :=
  rfl

/-- The specification of `gpSkeleton`: countable, dense (in the `distL2`
pseudometric topology), and a.s. carrying bounded uniformly-continuous paths.
Proved by instantiating `gaussianChaining_UC` on the explicit Dudley net
`gpSkeletonNet`, whose `T₀`-witness is exactly `⋃ j, net j = gpSkeleton`. -/
theorem gpSkeleton_spec (hF_meas : ∀ f ∈ F, Measurable f)
    (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
    (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty) :
    letI inst := distL2PseudoMetric hG_env hG hF_meas
    (gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).Countable
      ∧ @Dense ↥F inst.toUniformSpace.toTopologicalSpace
          (gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) ∧
      (∀ᵐ ω ∂iidStdGaussian,
        (BddAbove (Set.range
          (fun t : gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne =>
            |gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω|))) ∧
        @UniformContinuousOn ↥F ℝ
          (distL2PseudoMetric hG_env hG hF_meas).toUniformSpace _
          (fun t => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω)
          (gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)) := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  -- Specs of the explicit Dudley net (= `gpSkeletonNet` by definition).
  obtain ⟨hnet, hmono, hDud⟩ := (exists_dudley_net hF_ent hF_ne).choose_spec
  -- The chaining theorem gives countability, density, and almost-sure bounded
  -- uniform continuity on `⋃ j, net j = gpSkeleton`.
  exact _root_.GaussianChaining.gaussianChaining_UC_iUnion (μ := iidStdGaussian) (K := 1)
    zero_le_one (gpX_measurable ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep)
    (gpSkeletonNet hF_meas hF_ent hF_ne) hnet hmono
    (fun s t => (gpX_subgaussian_increment ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep s t).mono_proxy
      (by
        refine NNReal.coe_le_coe.mp ?_
        change distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2
          ≤ 1 ^ 2 * distL2 P (s : Ω → ℝ) (t : Ω → ℝ) ^ 2
        rw [one_pow, one_mul])) hDud

variable (hF_meas : ∀ f ∈ F, Measurable f)
  (hH_inf : ¬ FiniteDimensional ℝ ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hH_sep : TopologicalSpace.SeparableSpace ↥(gpH ⟨G, hG_env, hG⟩ hF_meas))
  (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) (hF_ne : F.Nonempty)

/-- The **good-set predicate** for `ω`: on the skeleton `T₀ = gpSkeleton`, the path
`t ↦ gpX t ω` is bounded and uniformly continuous (in the `distL2` pseudometric).
This is the a.s. event of `gpSkeleton_spec`; `gpPath ω` uses the UC extension on
this event and is `0` off it. -/
def gpGood (ω : ℕ → ℝ) : Prop :=
    (BddAbove (Set.range
      (fun t : gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne =>
        |gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω|)))
    ∧ @UniformContinuousOn ↥F ℝ
        (distL2PseudoMetric hG_env hG hF_meas).toUniformSpace _
        (fun t => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω)
        (gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)

/-- The **uniformly-continuous extension** of the skeleton path `t ↦ gpX t ω`
(restricted to `T₀ = gpSkeleton`) to all of `↥F`, in the `distL2` pseudometric
uniformity. Defined unconditionally via `Dense.extend`; its good properties (UC,
boundedness, agreement on `T₀`) hold on the good set. -/
def pathExtend (ω : ℕ → ℝ) : ↥F → ℝ :=
    letI inst := distL2PseudoMetric hG_env hG hF_meas
    @Dense.extend ↥F ℝ inst.toUniformSpace.toTopologicalSpace _
      (gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)
      (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1
      ((gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).restrict
        (fun t => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω))

/-- On the good set, the restriction of the skeleton path to `T₀` is uniformly
continuous (in the `distL2` pseudometric uniformity on the subtype `↥T₀`). -/
theorem uniformContinuous_restrict_of_good {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) :
    letI inst := distL2PseudoMetric hG_env hG hF_meas
    @UniformContinuous _ ℝ
      (@instUniformSpaceSubtype ↥F _ inst.toUniformSpace) _
      ((gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).restrict
        (fun t => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep t ω)) := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  exact (@uniformContinuousOn_iff_restrict ↥F ℝ inst.toUniformSpace _ _ _).mp hω.2

/-- On the good set, the UC extension `pathExtend ω` is uniformly continuous on
all of `↥F` (in the `distL2` pseudometric uniformity). -/
theorem uniformContinuous_pathExtend_of_good {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) :
    letI inst := distL2PseudoMetric hG_env hG hF_meas
    @UniformContinuous _ ℝ inst.toUniformSpace _
      (pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  exact @Dense.uniformContinuous_extend ↥F ℝ inst.toUniformSpace _ _ _ _
    (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1
    (uniformContinuous_restrict_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω)

omit [IsProbabilityMeasure P] in
/-- **`↥F` is totally bounded** in the `distL2` pseudometric. A finite `ε`-net of
`F` (from `totallyBounded_L2`, via the finite bracketing cover) yields a finite
`ε`-net of the subtype `↥F`, which is `Metric.totallyBounded_iff`. -/
theorem totallyBounded_F (hF_ent : bracketingEntropyIntegral 1 F P < ⊤) :
    letI inst := distL2PseudoMetric hG_env hG hF_meas
    @TotallyBounded ↥F inst.toUniformSpace Set.univ := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  rw [@Metric.totallyBounded_iff ↥F inst]
  intro ε hε
  obtain ⟨S, hS_sub, hS_net⟩ := totallyBounded_L2 hF_ent ε hε
  -- Lift each net point of `F` to the subtype `↥F`.
  refine ⟨{g : ↥F | (g : Ω → ℝ) ∈ S}, ?_, ?_⟩
  · -- finite: injects via `Subtype.val` into the finite `↑S`.
    apply Set.Finite.of_finite_image (f := (Subtype.val : ↥F → (Ω → ℝ)))
    · exact (S.finite_toSet).subset (by rintro _ ⟨g, hg, rfl⟩; exact hg)
    · exact Set.injOn_of_injective Subtype.val_injective
  · intro f _
    obtain ⟨g, hgS, hfg⟩ := hS_net (f : Ω → ℝ) f.2
    refine Set.mem_iUnion.mpr ⟨⟨g, hS_sub hgS⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hgS, ?_⟩
    -- `dist f ⟨g,_⟩ = distL2 P f g < ε` (defeq under the pseudometric).
    rw [@Metric.mem_ball ↥F inst]
    change distL2 P (f : Ω → ℝ) g < ε
    exact hfg

/-- On the good set, the UC extension `pathExtend ω` is **bounded** over all of
`↥F`: `BddAbove (range fun f => |pathExtend ω f|)`. The UC image of the
totally-bounded `↥F` is totally bounded, hence bounded; `|·|` is Lipschitz, so the
range of `|pathExtend ω|` is bounded, hence bounded above. -/
theorem bddAbove_pathExtend_of_good {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) :
    BddAbove (Set.range
      (fun f : ↥F => |pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f|)) := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  -- UC image of the totally-bounded `↥F` is totally bounded, hence bounded.
  have htb : @TotallyBounded ℝ _
      (pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω '' Set.univ) :=
    @TotallyBounded.image ↥F ℝ inst.toUniformSpace _ _ _
      (totallyBounded_F hG_env hG hF_meas hF_ent)
      (uniformContinuous_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω)
  rw [Set.image_univ] at htb
  have hb : Bornology.IsBounded
      (Set.range (pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω)) :=
    htb.isBounded
  -- A bounded set of reals has a uniform `‖·‖`-bound, which bounds `|pathExtend ω ·|`.
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  refine ⟨C, ?_⟩
  rintro _ ⟨f, rfl⟩
  have := hC _ (Set.mem_range_self f)
  simpa only [Real.norm_eq_abs] using this

/-- On the good set, `pathExtend ω` agrees with `gpX · ω` on the skeleton `T₀`. -/
theorem pathExtend_eq_on_skeleton {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω)
    (t : gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :
    pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω (t : ↥F)
      = gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t : ↥F) ω := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  have := @Dense.extend_of_ind ↥F ℝ inst.toUniformSpace _ _ _ _
    (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1
    (uniformContinuous_restrict_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω) t
  simpa [pathExtend, Set.restrict_apply] using! this

/-- On the good set, `pathExtend ω` is an `ℓ∞(F)` element: its range is bounded in
`‖·‖` (`bddAbove_pathExtend_of_good`, since `‖·‖ = |·|` on ℝ), which is
`memℓp_infty_iff`. -/
theorem memℓp_pathExtend_of_good {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) :
    Memℓp (fun f : ↥F => pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f) ∞ := by
  rw [memℓp_infty_iff]
  simpa only [Real.norm_eq_abs] using
    bddAbove_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω

open scoped Classical in
/-- **The `ℓ∞(F)`-valued path `gpPath`.** On the good set (`gpGood ω`) it is the
uniformly-continuous extension `pathExtend ω` of the skeleton path, packaged as an
element of `ℓ∞(F)` via `memℓp_pathExtend_of_good`. Off the good set it is `0`.

This is a bounded realisation of the `P`-Brownian-bridge candidate limit used in
Theorem 18.14. -/
noncomputable def gpPath (ω : ℕ → ℝ) : LinfF F :=
  if hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω then
    ⟨fun f => pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f,
      memℓp_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω⟩
  else 0

/-- On the good set, the coordinate `gpPath ω f` is `pathExtend ω f`. -/
theorem gpPath_apply_of_good {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) (f : ↥F) :
    gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f
      = pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f := by
  classical
  rw [gpPath, dif_pos hω]

/-- **Coordinate a.e.-agreement of `gpPath` with `gpX`.** For each fixed `f ∈ F`,
the `f`-coordinate of the path `gpPath ω` agrees almost surely with `gpX f ω`.

On the good set, `gpPath ω f = pathExtend ω f`, the UC extension. Picking a
skeleton sequence `tₙ ∈ T₀` with `tₙ → f` (density + first-countability), the
isometry bound `eLpNorm (gpX tₙ − gpX f) ≤ distL2 P tₙ f → 0` gives convergence in
measure, hence an a.e.-convergent subsequence `gpX t_{nₖ} ω → gpX f ω`. Meanwhile
`pathExtend ω` is continuous (UC) and agrees with `gpX · ω` on `T₀`, so
`gpX t_{nₖ} ω = pathExtend ω t_{nₖ} → pathExtend ω f`. Uniqueness of limits in `ℝ`
pins `pathExtend ω f = gpX f ω` a.e. -/
theorem gpPath_aeeq_coord (f : ↥F) :
    (fun ω => gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f)
      =ᵐ[iidStdGaussian] gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  -- First-countability + Fréchet-Urysohn of the `distL2` pseudometric on `↥F`.
  haveI hfc : @FirstCountableTopology ↥F inst.toUniformSpace.toTopologicalSpace :=
    @UniformSpace.firstCountableTopology ↥F inst.toUniformSpace inferInstance
  haveI hfu : @FrechetUrysohnSpace ↥F inst.toUniformSpace.toTopologicalSpace :=
    @FirstCountableTopology.frechetUrysohnSpace ↥F inst.toUniformSpace.toTopologicalSpace hfc
  -- `T₀ = gpSkeleton` is dense, so `f ∈ closure T₀`; first-countability gives a
  -- skeleton sequence `tₙ → f`.
  have hdense := (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1
  have hf_mem : f ∈ @closure ↥F inst.toUniformSpace.toTopologicalSpace
      (gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) := by
    rw [@Dense.closure_eq ↥F inst.toUniformSpace.toTopologicalSpace _ hdense]; trivial
  obtain ⟨t, ht_mem, ht_tendsto⟩ :=
    (@mem_closure_iff_seq_limit ↥F inst.toUniformSpace.toTopologicalSpace hfu _ _).mp hf_mem
  -- Convergence in measure of `gpX (tₙ)` to `gpX f`, from the isometry bound.
  have hae_meas : ∀ n, AEStronglyMeasurable
      (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t n)) iidStdGaussian :=
    fun n => (gpX_measurable ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t n)).aestronglyMeasurable
  have hae_meas_f : AEStronglyMeasurable
      (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f) iidStdGaussian :=
    (gpX_measurable ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f).aestronglyMeasurable
  -- `eLpNorm (gpX tₙ − gpX f) 2 → 0`.
  have htendsto_eLp : Filter.Tendsto
      (fun n => eLpNorm (fun ω => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t n) ω
          - gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f ω) 2 iidStdGaussian)
      Filter.atTop (nhds 0) := by
    -- squeeze between `0` and `ofReal (distL2 P (t n) f) → 0`.
    have hdist0 : Filter.Tendsto
        (fun n => ENNReal.ofReal (distL2 P (t n : Ω → ℝ) (f : Ω → ℝ)))
        Filter.atTop (nhds 0) := by
      have : Filter.Tendsto (fun n => distL2 P (t n : Ω → ℝ) (f : Ω → ℝ))
          Filter.atTop (nhds 0) := by
        have hconv := (@tendsto_iff_dist_tendsto_zero ↥F ℕ inst _ _ _).mp ht_tendsto
        -- `dist (t n) f = distL2 P (t n) f` (defeq under the `inst` pseudometric).
        simpa only [show (fun n => dist (t n) f)
          = (fun n => distL2 P (t n : Ω → ℝ) (f : Ω → ℝ)) from rfl] using hconv
      have h0 : (0 : ℝ≥0∞) = ENNReal.ofReal 0 := by simp
      rw [h0]
      exact (ENNReal.continuous_ofReal.tendsto 0).comp this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hdist0
      (Filter.Eventually.of_forall (fun n => zero_le))
      (Filter.Eventually.of_forall (fun n =>
        eLpNorm_gpX_sub_le ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t n) f))
  have htim : TendstoInMeasure iidStdGaussian
      (fun n => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t n)) Filter.atTop
      (gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep f) :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hae_meas hae_meas_f htendsto_eLp
  obtain ⟨ns, hns_mono, hns_ae⟩ := htim.exists_seq_tendsto_ae
  -- The good event.
  have hgood := (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.2
  filter_upwards [hgood, hns_ae] with ω hgood_ω hns_ae_ω
  -- On the good set: `gpPath ω f = pathExtend ω f`.
  rw [gpPath_apply_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hgood_ω f]
  -- Two limits of `fun k => gpX (t (ns k)) ω`: `gpX f ω` and `pathExtend ω f`.
  -- (1) `gpX (t (ns k)) ω → gpX f ω` (a.e. subsequence).
  -- (2) `gpX (t (ns k)) ω = pathExtend ω (t (ns k)) → pathExtend ω f` (continuity).
  have huc := uniformContinuous_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
    hgood_ω
  have hcont : @Continuous ↥F ℝ inst.toUniformSpace.toTopologicalSpace _
      (pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) :=
    @UniformContinuous.continuous ↥F ℝ inst.toUniformSpace _ _ huc
  -- `t (ns k) → f` (subsequence of a convergent sequence), in the `inst` topology.
  have htsub : @Filter.Tendsto ℕ ↥F (fun k => t (ns k)) Filter.atTop
      (@nhds ↥F inst.toUniformSpace.toTopologicalSpace f) :=
    ht_tendsto.comp hns_mono.tendsto_atTop
  have hpath_tendsto : Filter.Tendsto
      (fun k => pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω (t (ns k)))
      Filter.atTop (nhds (pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f)) :=
    (@Continuous.tendsto ↥F ℝ inst.toUniformSpace.toTopologicalSpace _ _ hcont f).comp htsub
  -- agreement on `T₀`: `pathExtend ω (t (ns k)) = gpX (t (ns k)) ω`.
  have hagree : ∀ k, pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω (t (ns k))
      = gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t (ns k)) ω := by
    intro k
    exact pathExtend_eq_on_skeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hgood_ω
      ⟨t (ns k), ht_mem (ns k)⟩
  -- so `gpX (t (ns k)) ω → pathExtend ω f`.
  have hgpX_tendsto_path : Filter.Tendsto
      (fun k => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (t (ns k)) ω)
      Filter.atTop (nhds (pathExtend hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω f)) := by
    refine hpath_tendsto.congr (fun k => hagree k)
  -- and `gpX (t (ns k)) ω → gpX f ω` (a.e. subsequence).
  exact tendsto_nhds_unique hgpX_tendsto_path hns_ae_ω

/-! ## Strong measurability of `gpPath` and its law `ν`

`gpPath` is **not** directly Borel-measurable into `ℓ∞(F)` (the UC extension
`Dense.extend` is a choice-based cluster-point limit with no measurable-in-`ω`
structure, and `ℓ∞(F)` over the uncountable `↥F` is not second-countable, so
coordinatewise measurability does not imply Borel measurability). Instead we
exhibit `gpPath` as an a.e. limit of **strongly-measurable simple functions**
`approxₙ`, each of which sends `ω` to the finitely-many `gpX` values on the first
`n+1` skeleton points, interpolated by nearest-skeleton-point assignment. Each
`approxₙ` factors through a continuous (1-Lipschitz) map out of a finite-
dimensional tuple, hence is strongly measurable; and `approxₙ ω → gpPath ω` in
sup norm for every good `ω` (a.e.), because nearest-skeleton distances tend to
`0` uniformly (total boundedness + density) and the UC extension is uniformly
continuous. `aestronglyMeasurable_of_tendsto_ae` then gives the result. -/

section GpPathMeasurable

/-- A `ℕ`-enumeration of the skeleton `T₀ = gpSkeleton` with `range = T₀`
exactly. Exists because `T₀` is countable and nonempty (it is dense in the
nonempty `↥F`). -/
def gpEnum : ℕ → ↥F :=
  (Set.Countable.exists_eq_range
    (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).1
    (by
      letI inst := distL2PseudoMetric hG_env hG hF_meas
      have hne : Nonempty ↥F := hF_ne.to_subtype
      exact @Dense.nonempty ↥F inst.toUniformSpace.toTopologicalSpace _ hne
        (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1)).choose

/-- Each `gpEnum k` lies in the skeleton `T₀`. -/
theorem gpEnum_mem (k : ℕ) :
    gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne k
      ∈ gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne := by
  have hsp := (Set.Countable.exists_eq_range
    (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).1
    (by
      letI inst := distL2PseudoMetric hG_env hG hF_meas
      have hne : Nonempty ↥F := hF_ne.to_subtype
      exact @Dense.nonempty ↥F inst.toUniformSpace.toTopologicalSpace _ hne
        (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1)).choose_spec
  rw [hsp]; exact ⟨k, rfl⟩

/-- Every skeleton point is `gpEnum k` for some index `k` (the enumeration is
onto `T₀`). -/
theorem gpEnum_surjOn {t : ↥F}
    (ht : t ∈ gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) :
    ∃ k, gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne k = t := by
  have hsp := (Set.Countable.exists_eq_range
    (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).1
    (by
      letI inst := distL2PseudoMetric hG_env hG hF_meas
      have hne : Nonempty ↥F := hF_ne.to_subtype
      exact @Dense.nonempty ↥F inst.toUniformSpace.toTopologicalSpace _ hne
        (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1)).choose_spec
  rw [hsp] at ht
  obtain ⟨k, hk⟩ := ht
  exact ⟨k, hk⟩

open scoped Classical in
/-- The set of indices `{0, …, n}` whose enumeration points form the first
`n+1` skeleton points — the support of the `n`-th simple approximation. -/
def gpFinset (n : ℕ) : Finset ↥F :=
  (Finset.range (n + 1)).image (gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)

/-- `gpFinset n` is nonempty (it contains `gpEnum 0`). -/
theorem gpFinset_nonempty (n : ℕ) :
    (gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n).Nonempty := by
  classical
  exact ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), rfl⟩⟩

/-- Every element of `gpFinset n` lies in the skeleton `T₀`. -/
theorem gpFinset_subset_skeleton (n : ℕ) {x : ↥F}
    (hx : x ∈ gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) :
    x ∈ gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne := by
  classical
  rw [gpFinset, Finset.mem_image] at hx
  obtain ⟨k, _, rfl⟩ := hx
  exact gpEnum_mem hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne k

/-- The skeleton point in `gpFinset n` nearest (in `distL2`) to `f`. Deterministic
in `f`, independent of `ω`. Realised as the `Finset.exists_min_image` argmin. -/
def gpNearest (n : ℕ) (f : ↥F) : ↥F :=
  (Finset.exists_min_image
    (gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n)
    (fun g => distL2 P (g : Ω → ℝ) (f : Ω → ℝ))
    (gpFinset_nonempty hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n)).choose

/-- `gpNearest n f` is a member of `gpFinset n`. -/
theorem gpNearest_mem (n : ℕ) (f : ↥F) :
    gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f
      ∈ gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n :=
  (Finset.exists_min_image
    (gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n)
    (fun g => distL2 P (g : Ω → ℝ) (f : Ω → ℝ))
    (gpFinset_nonempty hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n)).choose_spec.1

/-- `gpNearest n f` lies in the skeleton `T₀`. -/
theorem gpNearest_mem_skeleton (n : ℕ) (f : ↥F) :
    gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f
      ∈ gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne :=
  gpFinset_subset_skeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n
    (gpNearest_mem hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f)

/-- `gpNearest n f` minimises `distL2 · f` over `gpFinset n`: for any other member
`g`, `distL2 (gpNearest n f) f ≤ distL2 g f`. -/
theorem gpNearest_min (n : ℕ) (f : ↥F) {g : ↥F}
    (hg : g ∈ gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) :
    distL2 P (gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f : Ω → ℝ)
        (f : Ω → ℝ)
      ≤ distL2 P (g : Ω → ℝ) (f : Ω → ℝ) :=
  (Finset.exists_min_image
    (gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n)
    (fun g => distL2 P (g : Ω → ℝ) (f : Ω → ℝ))
    (gpFinset_nonempty hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n)).choose_spec.2 g hg

/-! ### The simple approximations `approxₙ` and their strong measurability

`approxₙ ω = gpLin n (gpTuple n ω)`, factoring through the finite-dimensional
tuple `gpTuple n ω : ↥(gpFinset n) → ℝ` (Measurable in `ω`, hence StronglyMeasurable
since the codomain is second-countable) and the **1-Lipschitz** map
`gpLin n : (↥(gpFinset n) → ℝ) → ℓ∞(F)` (Continuous). -/

/-- `gpLin n x` sends each coordinate `f` to the `x`-value at the nearest skeleton
point `gpNearest n f` (an element of `gpFinset n`). The range is finite (`x`
ranges over the finite `↥(gpFinset n)`), hence bounded, so this is in `ℓ∞(F)`. -/
def gpLin (n : ℕ)
    (x : ↥(gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) → ℝ) :
    LinfF F :=
  ⟨fun f => x ⟨gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f,
      gpNearest_mem hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f⟩, by
    change Memℓp _ ∞
    rw [memℓp_infty_iff]
    -- range ⊆ range of `‖x ·‖` over the finite index `↥(gpFinset n)`, hence bounded.
    refine (Set.Finite.bddAbove
      (Set.finite_range (fun g => ‖x g‖))).mono ?_
    rintro _ ⟨f, rfl⟩
    exact ⟨⟨gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f,
      gpNearest_mem hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f⟩, rfl⟩⟩

/-- `gpLin n` is 1-Lipschitz: `‖gpLin n x − gpLin n y‖∞ ≤ ‖x − y‖∞`, because each
coordinate difference `|x(near f) − y(near f)|` is `≤ ‖x − y‖∞`. -/
theorem lipschitz_gpLin (n : ℕ) :
    LipschitzWith 1 (gpLin hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm]
  -- bound `‖gpLin x − gpLin y‖∞ ≤ dist x y` coordinatewise.
  apply lp.norm_le_of_forall_le dist_nonneg
  intro f
  -- coordinate `f`: `‖(gpLin x − gpLin y) f‖ = |x(near f) − y(near f)| ≤ dist x y`.
  rw [lp.coeFn_sub, Pi.sub_apply]
  change ‖x ⟨gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f, _⟩
      - y ⟨gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f, _⟩‖ ≤ dist x y
  rw [← dist_eq_norm]
  exact dist_le_pi_dist x y _

/-- `gpLin n` is continuous (from `lipschitz_gpLin`). -/
theorem continuous_gpLin (n : ℕ) :
    Continuous (gpLin hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) :=
  (lipschitz_gpLin hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n).continuous

/-- The finite tuple `gpTuple n ω : ↥(gpFinset n) → ℝ` of `gpX`-values on the
first `n+1` skeleton points. Measurable in `ω` (finite product of measurable
`gpX`). -/
def gpTuple (n : ℕ) (ω : ℕ → ℝ) :
    ↥(gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) → ℝ :=
  fun g => gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (g : ↥F) ω

/-- `gpTuple n` is measurable (each coordinate is a `gpX`, which is measurable). -/
theorem measurable_gpTuple (n : ℕ) :
    Measurable (gpTuple hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) := by
  rw [measurable_pi_iff]
  intro g
  exact gpX_measurable ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep (g : ↥F)

/-- The `n`-th **simple approximation** `approxₙ ω = gpLin n (gpTuple n ω)`. For
each good `ω`, `approxₙ ω → gpPath ω` in `ℓ∞(F)`. -/
def gpApprox (n : ℕ) (ω : ℕ → ℝ) : LinfF F :=
  gpLin hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n
    (gpTuple hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n ω)

/-- The `f`-coordinate of `gpApprox n ω` is `gpX (gpNearest n f) ω`. -/
theorem gpApprox_apply (n : ℕ) (ω : ℕ → ℝ) (f : ↥F) :
    gpApprox hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n ω f
      = gpX ⟨G, hG_env, hG⟩ hF_meas hH_inf hH_sep
          (gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f) ω := rfl

/-- Each `gpApprox n` is `StronglyMeasurable`: it is the composition of the
continuous `gpLin n` with the measurable (hence, into the second-countable finite
product, strongly measurable) tuple `gpTuple n`. -/
theorem stronglyMeasurable_gpApprox (n : ℕ) :
    StronglyMeasurable (gpApprox hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n) := by
  apply Continuous.comp_stronglyMeasurable
    (continuous_gpLin hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n)
  exact (measurable_gpTuple hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n).stronglyMeasurable

/-! ### Convergence `approxₙ ω → gpPath ω` and `AEStronglyMeasurable gpPath` -/

/-- **The first `n+1` skeleton points eventually form a `δ`-net of `↥F`.** For
every `δ > 0` there is `N` such that for all `n ≥ N` and all `f`, the nearest
skeleton point `gpNearest n f` is within `δ` (in `distL2`) of `f`. This is the
quantitative core of the uniform approximation: total boundedness of `↥F` gives a
finite `δ/2`-net, density places each net point within `δ/2` of a skeleton point,
and finitely many skeleton-point indices are all `≤ N` for `N` large. -/
theorem gpNearest_eventually_close {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ f : ↥F,
      distL2 P (gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f : Ω → ℝ)
          (f : Ω → ℝ) < δ := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  -- finite `δ/2`-net `S` of `↥F` (total boundedness).
  obtain ⟨S, hS_fin, hS_cover⟩ :=
    (@Metric.totallyBounded_iff ↥F inst _).mp
      (totallyBounded_F hG_env hG hF_meas hF_ent) (δ / 2) (by positivity)
  -- For each net point `s`, a skeleton point within `δ/2` and its index.
  have hdense := (gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.1
  have hskel : ∀ s : ↥F, ∃ k : ℕ,
      dist (gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne k) s < δ / 2 := by
    intro s
    have hmem : s ∈ @closure ↥F inst.toUniformSpace.toTopologicalSpace
        (gpSkeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) := by
      rw [@Dense.closure_eq ↥F inst.toUniformSpace.toTopologicalSpace _ hdense]; trivial
    obtain ⟨σ, hσ_mem, hσ_dist⟩ := (@Metric.mem_closure_iff ↥F inst _ _).mp hmem (δ / 2)
      (by positivity)
    obtain ⟨k, hk⟩ := gpEnum_surjOn hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hσ_mem
    refine ⟨k, ?_⟩
    rw [hk, dist_comm]; exact hσ_dist
  choose idx hidx using hskel
  -- `N := 1 + sup over the finite net `S` of the chosen indices`.
  refine ⟨1 + hS_fin.toFinset.sup idx, fun n hn f => ?_⟩
  -- pick a net point `s ∈ S` within `δ/2` of `f`.
  have hfmem : f ∈ ⋃ y ∈ S, @Metric.ball ↥F inst y (δ / 2) := hS_cover (Set.mem_univ f)
  rw [Set.mem_iUnion₂] at hfmem
  obtain ⟨s, hsS, hfs⟩ := hfmem
  rw [@Metric.mem_ball ↥F inst] at hfs
  -- the skeleton point `gpEnum (idx s)` is within `δ/2` of `s`, and its index ≤ n.
  have hidx_le : idx s ≤ n := by
    have : idx s ≤ hS_fin.toFinset.sup idx :=
      Finset.le_sup (by rw [Set.Finite.mem_toFinset]; exact hsS)
    omega
  have hmem_finset : gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (idx s)
      ∈ gpFinset hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n := by
    classical
    rw [gpFinset, Finset.mem_image]
    exact ⟨idx s, Finset.mem_range.mpr (Nat.lt_succ_of_le hidx_le), rfl⟩
  -- `gpNearest n f ≤ dist (gpEnum (idx s)) f ≤ dist (gpEnum (idx s)) s + dist s f < δ`.
  have hnear_le := gpNearest_min hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f hmem_finset
  -- bridge `distL2` ↔ `dist` (defeq under `inst`).
  have hbridge : dist (gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f) f
      = distL2 P (gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f : Ω → ℝ)
          (f : Ω → ℝ) := rfl
  have hbridge2 : dist (gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (idx s)) f
      = distL2 P (gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (idx s) : Ω → ℝ)
          (f : Ω → ℝ) := rfl
  calc distL2 P (gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f : Ω → ℝ)
        (f : Ω → ℝ)
      ≤ distL2 P (gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (idx s) : Ω → ℝ)
          (f : Ω → ℝ) := hnear_le
    _ = dist (gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (idx s)) f := hbridge2.symm
    _ ≤ dist (gpEnum hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne (idx s)) s + dist s f :=
        dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := by
        apply add_lt_add (hidx s)
        rw [dist_comm]; exact hfs
    _ = δ := by ring

/-- **`approxₙ ω → gpPath ω` in `ℓ∞(F)` for every good `ω`.** For good `ω`, each
coordinate is `gpApprox n ω f = gpX (gpNearest n f) ω = pathExtend ω (gpNearest n f)`
(agreement on the skeleton), and `gpPath ω f = pathExtend ω f`. Given `ε > 0`,
uniform continuity of `pathExtend ω` supplies `δ` with `distL2 a b < δ ⟹
|pathExtend ω a − pathExtend ω b| ≤ ε/2`; `gpNearest_eventually_close` makes the
nearest-skeleton distance `< δ` for all `f` once `n ≥ N`. The sup-norm bound
`lp.norm_le_of_forall_le` then gives `‖approxₙ ω − gpPath ω‖ ≤ ε/2 < ε`. -/
theorem tendsto_gpApprox_of_good {ω : ℕ → ℝ}
    (hω : gpGood hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) :
    Filter.Tendsto (fun n => gpApprox hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n ω)
      Filter.atTop (nhds (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω)) := by
  letI inst := distL2PseudoMetric hG_env hG hF_meas
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- ε/2-δ uniform continuity of `pathExtend ω` on the good set.
  have huc := uniformContinuous_pathExtend_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω
  rw [Metric.uniformContinuous_iff] at huc
  obtain ⟨δ, hδ, hδ_uc⟩ := huc (ε / 2) (half_pos hε)
  -- eventually every `gpNearest n f` is within `δ` of `f`.
  obtain ⟨N, hN⟩ := gpNearest_eventually_close hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hδ
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  -- sup-norm bound: every coordinate of `approxₙ ω − gpPath ω` is `≤ ε/2`.
  have hcoord : ∀ f : ↥F,
      ‖(↑(gpApprox hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n ω
            - gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω) : ↥F → ℝ) f‖ ≤ ε / 2 := by
    intro f
    rw [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs]
    -- `approxₙ ω f = pathExtend ω (gpNearest n f)`.
    rw [gpApprox_apply hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n ω f,
      ← pathExtend_eq_on_skeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω
        ⟨gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f,
          gpNearest_mem_skeleton hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f⟩,
      gpPath_apply_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω f]
    -- `|pathExtend ω (gpNearest n f) − pathExtend ω f| = dist (pathExtend …) (pathExtend …)`.
    rw [← Real.dist_eq]
    -- distance `< δ` between `gpNearest n f` and `f` ⟹ `dist (pathExtend …) < ε/2`.
    have hclose : dist (gpNearest hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n f) f < δ :=
      hN n hn f
    exact le_of_lt (hδ_uc hclose)
  calc ‖gpApprox hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne n ω
          - gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne ω‖
      ≤ ε / 2 := lp.norm_le_of_forall_le (le_of_lt (half_pos hε)) hcoord
    _ < ε := by linarith

/-- **`gpPath` is `AEStronglyMeasurable`** under `iidStdGaussian`. It is the a.e.
limit of the strongly-measurable simple approximations `approxₙ`: on the good
set (an a.s. event by `gpSkeleton_spec`), `approxₙ ω → gpPath ω` in `ℓ∞(F)`
(`tendsto_gpApprox_of_good`), and `aestronglyMeasurable_of_tendsto_ae` lifts the
per-`n` strong measurability through the a.e. limit. -/
theorem gpPath_aestronglyMeasurable :
    AEStronglyMeasurable (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) iidStdGaussian := by
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (fun n => (stronglyMeasurable_gpApprox hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne
      n).aestronglyMeasurable) ?_
  -- the a.s. good event of `gpSkeleton_spec`.
  filter_upwards [(gpSkeleton_spec hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).2.2] with ω hω
  exact tendsto_gpApprox_of_good hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne hω

/-- **`gpPath` is `AEMeasurable`** under `iidStdGaussian` (from its
`AEStronglyMeasurable`ness). -/
theorem gpPath_aemeasurable :
    AEMeasurable (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne) iidStdGaussian :=
  (gpPath_aestronglyMeasurable hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne).aemeasurable

/-- **The law `ν = gpBridgeMeasure`** of the `ℓ∞(F)`-valued path `gpPath` under
`iidStdGaussian`: the candidate `P`-Brownian-bridge measure on `ℓ∞(F)` for
Theorem 18.14. -/
noncomputable def gpBridgeMeasure : Measure (LinfF F) :=
  iidStdGaussian.map (gpPath hG_env hG hF_meas hH_inf hH_sep hF_ent hF_ne)

end GpPathMeasurable

end GpPath

end

end AsymptoticStatistics.EmpiricalProcess
