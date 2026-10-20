module
public import StatLean.ConcentrationInequalities.EmpiricalProcess.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Defs
public import StatLean.ConcentrationInequalities.SubGaussian.Bounded
public import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
public import StatLean.ConcentrationInequalities.Orlicz.Defs
public import StatLean.ConcentrationInequalities.Orlicz.TailToNorm
public import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-!
# Sub-Gaussian increments of the empirical process — Theorem 8.2.3, Step 1

For i.i.d. data $X_1, \dots, X_n \sim P$ and bounded $f, g$ with
$\|f - g\|_\infty \le \delta$, the empirical-process increment is mean-zero
and sub-Gaussian with variance proxy **exactly** $\delta^2 / n$:
$$ \mathbb{E}\, X_f = 0, \qquad
   \mathbb{E}\exp\bigl(\lambda (X_f - X_g)\bigr)
   \le \exp\Bigl(\frac{\lambda^2 \delta^2}{2n}\Bigr), $$
whence the $\psi_2$-norm increment bound
$\|X_f - X_g\|_{\psi_2} \le \sqrt{6}\,\|f - g\|_\infty / \sqrt{n}$, i.e. the
sub-Gaussian-increments hypothesis of Dudley's inequality (HDP Definition
8.1.1) over the index space $C([0,1], \mathbb{R})$ with the sup metric.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.2, proof of Theorem 8.2.3, Step 1 (and §8.1,
Definition 8.1.1 for the increment condition).

**Proof formalization notes.** The MGF-level route is strictly better than
the book's Step 1 (Proposition 2.7.1 + centering Lemma 2.7.8, which lose
absolute constants): per summand, $(f-g)(X_i) \in [c - \delta, c + \delta]$
gives the Hoeffding proxy $((b-a)/2)^2 = \delta^2$
(`hasSubgaussianMGF_of_mem_Icc`), `HasSubgaussianMGF.sum_of_iIndepFun` gives
$n\delta^2$, and scaling by $n^{-1}$ (`isSubGaussian_const_mul`) gives
$\delta^2/n$ — **no constant loss**. The only constant enters at the
$\psi_2$-conversion: the Orlicz bridge `subGaussianNorm_le_of_isSubGaussian`
(B3) with its frozen carrier $\sqrt{6\sigma^2}$, giving explicit $\sqrt{6}$
factors (no alias constants). The common law is encoded by the map
hypothesis `μ.map (X i) = P` (`ProbabilityTheory.HasLaw` is absent at pin);
independence by the pin's `iIndepFun X μ`. Edge behavior: non-integrable `f`
never arises (all lemmas assume explicit sup bounds, hence integrability
under the probability `P` is derived in proofs, not exported). The
`SubGaussianIncrements` package is stated with `T = Set.univ` over all of
`C(unitInterval, ℝ)` and is restricted downstream via
`SubGaussianIncrements.mono_set`. Named-sorry fallback of the work item
`hdp-emp-increments`: `subGaussianNorm_empiricalProcess_sub_le_dist` (the
MGF-level core and the `δ`-form must close for real).

**Bibliographic comments.** The bounded-difference MGF bound is
W. Hoeffding, "Probability inequalities for sums of bounded random
variables," *J. Amer. Statist. Assoc.* 58 (1963), 13–30; the sub-Gaussian
increment condition for processes is R. M. Dudley, *J. Funct. Anal.* 1
(1967), 290–330.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {μ : Measure Ω} {P : Measure Ω'} {n : ℕ} {X : Fin n → Ω → Ω'}

/-- Integrability transfers along a law identity (LEAN-ONLY change-of-variables;
`ProbabilityTheory.HasLaw` is absent at pin, so the law is the map equation). -/
theorem integrable_comp_of_map_eq {Y : Ω → Ω'} {f : Ω' → ℝ}
    -- LEAN-ONLY: a.e.-measurability of the data map; regularity, no book content
    (hY : AEMeasurable Y μ)
    -- USER-INPUT: Y has law P; HDP §8.2 ("points X_i drawn from P")
    (hlaw : μ.map Y = P)
    -- LEAN-ONLY: integrability under the population law; derived from boundedness at call sites
    (hf_int : Integrable f P) :
    Integrable (fun ω => f (Y ω)) μ := by
  rw [← hlaw] at hf_int
  exact hf_int.comp_aemeasurable hY

/-- **The empirical process is mean-zero** (HDP §8.2, Definition 8.2.5):
`E[X_f] = n⁻¹ ∑ᵢ E f(Xᵢ) − ∫ f dP = 0` since each `Xᵢ` has law `P`. -/
theorem integral_empiricalProcess [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f : Ω' → ℝ}
    -- LEAN-ONLY: integrability under P; derived from boundedness at call sites
    (hf_int : Integrable f P)
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    ∫ ω, empiricalProcess P n X f ω ∂μ = 0 := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- integrability of each `f ∘ X i` under `μ`
  have hint : ∀ i, Integrable (fun ω => f (X i ω)) μ := fun i =>
    integrable_comp_of_map_eq (hX i).aemeasurable (hlaw i) hf_int
  -- each has expectation `∫ f dP`
  have hEi : ∀ i, ∫ ω, f (X i ω) ∂μ = ∫ x, f x ∂P := by
    intro i
    have hasm : AEStronglyMeasurable f (μ.map (X i)) := (hlaw i) ▸ hf_int.aestronglyMeasurable
    rw [← hlaw i, integral_map (hX i).aemeasurable hasm]
  have hsum_int : Integrable (fun ω => ∑ i, f (X i ω)) μ :=
    integrable_finset_sum _ (fun i _ => hint i)
  simp only [empiricalProcess]
  rw [integral_sub ((hsum_int.const_mul _)) (integrable_const _), integral_const,
    integral_const_mul, integral_finset_sum _ (fun i _ => hint i)]
  simp only [hEi]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    probReal_univ, one_smul, ← mul_assoc,
    inv_mul_cancel₀ hn, one_mul, sub_self]

/-- Sum-level Hoeffding bound (HDP §2.6 / §8.2 Step 1): the centered sum
`∑ᵢ (f(Xᵢ) − E_P f)` has sub-Gaussian MGF with proxy `n·δ²`
(per-summand `Icc(−δ, δ)`-membership proxy `δ²` + `sum_of_iIndepFun`). -/
theorem hasSubgaussianMGF_sum_centered_comp [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] {f : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class member; regularity, no book content
    (hf : Measurable f)
    -- USER-INPUT: uniform bound ‖f‖∞ ≤ δ; HDP §8.2 Step 1
    (hfδ : ∀ x, |f x| ≤ (δ : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF (fun ω => ∑ i, (f (X i ω) - ∫ x, f x ∂P))
      ((n : ℝ≥0) * δ ^ 2) μ := by
  have hf_int : Integrable f P :=
    (integrable_const (δ : ℝ)).mono' hf.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hfδ x)
  -- expectation of each `f ∘ X i` equals `∫ f dP`
  have hEi : ∀ i, ∫ ω, f (X i ω) ∂μ = ∫ x, f x ∂P := by
    intro i
    have hasm : AEStronglyMeasurable f (μ.map (X i)) := (hlaw i) ▸ hf.aestronglyMeasurable
    rw [← hlaw i, integral_map (hX i).aemeasurable hasm]
  -- per-summand sub-Gaussian MGF with proxy `δ ^ 2`
  have hproxy : ((‖(δ : ℝ) - -(δ : ℝ)‖₊ / 2) ^ 2) = δ ^ 2 := by
    have h1 : ‖(δ : ℝ) - -(δ : ℝ)‖₊ = 2 * δ := by
      rw [← NNReal.coe_inj]
      push_cast
      rw [sub_neg_eq_add, ← two_mul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * δ)]
    rw [h1]
    have h2 : (2 : ℝ≥0) * δ / 2 = δ := by
      rw [mul_comm, mul_div_assoc, div_self (by norm_num : (2 : ℝ≥0) ≠ 0), mul_one]
    rw [h2]
  have hsub : ∀ i, HasSubgaussianMGF (fun ω => f (X i ω) - ∫ x, f x ∂P) (δ ^ 2) μ := by
    intro i
    have hmem : IsSubGaussian (fun ω => f (X i ω)) ((‖(δ : ℝ) - -(δ : ℝ)‖₊ / 2) ^ 2) μ :=
      isSubGaussian_of_mem_Icc ((hf.comp (hX i)).aemeasurable)
        (ae_of_all _ fun ω => by
          constructor
          · have := (abs_le.mp (hfδ (X i ω))).1; linarith
          · exact (abs_le.mp (hfδ (X i ω))).2)
    rw [isSubGaussian_iff] at hmem
    rw [hproxy] at hmem
    simpa only [hEi i] using hmem
  -- independence of the centered composed family
  have hindep' : iIndepFun (fun i ω => f (X i ω) - ∫ x, f x ∂P) μ := by
    have := hindep.comp (fun _ => fun x : Ω' => f x - ∫ x, f x ∂P)
      (fun _ => hf.sub measurable_const)
    exact this
  have := HasSubgaussianMGF.sum_of_iIndepFun hindep' (c := fun _ => δ ^ 2)
    (s := Finset.univ) (fun i _ => hsub i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact this

/-- Core single-function MGF bound: for a bounded `h` with `‖h‖∞ ≤ δ`, the
empirical process `X_h = n⁻¹ ∑ h(Xᵢ) − ∫ h dP` has sub-Gaussian MGF with proxy
`δ²/n`. This factors `X_h = n⁻¹ · ∑(h(Xᵢ) − ∫h dP)` (a single function, so no
integral-splitting is needed) and scales the sum-level bound by `n⁻¹`. -/
private theorem hasSubgaussianMGF_empiricalProcess_core [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {h : Ω' → ℝ} {δ : ℝ≥0}
    (hh : Measurable h) (hhδ : ∀ x, |h x| ≤ (δ : ℝ))
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF (empiricalProcess P n X h) (δ ^ 2 / n) μ := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  -- sum-level bound
  have hsum := hasSubgaussianMGF_sum_centered_comp (n := n) (X := X) hh hhδ hX hindep hlaw
  -- scale by n⁻¹
  have hscaled := hsum.const_mul ((n : ℝ)⁻¹)
  -- `X_h = n⁻¹ · ∑(h(Xᵢ) − ∫h dP)` as functions
  have hfun : (fun ω => (n : ℝ)⁻¹ * ∑ i, (h (X i ω) - ∫ x, h x ∂P))
      = empiricalProcess P n X h := by
    funext ω
    rw [empiricalProcess, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_sub, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  rw [hfun] at hscaled
  -- proxy equality `(n⁻¹)² · (n · δ²) = δ²/n`
  have hn' : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  convert hscaled using 1
  apply NNReal.coe_injective
  change ((δ ^ 2 / n : ℝ≥0) : ℝ) = (n : ℝ)⁻¹ ^ 2 * ((n * δ ^ 2 : ℝ≥0) : ℝ)
  push_cast
  field_simp

/-- Increment MGF from an explicit integrability witness for the difference:
if `f − g` is `P`-integrable *and* the population terms telescope
(`∫ f dP − ∫ g dP = ∫ (f − g) dP`), then `X_f − X_g = X_{f−g}` and the
single-function core applies. This is the honest, integrability-aware core of
the increment bound; the `dist`-form call site (continuous `f, g`) supplies both
witnesses. -/
private theorem hasSubgaussianMGF_empiricalProcess_sub_of_integrable
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P] [NeZero n]
    {f g : Ω' → ℝ} {δ : ℝ≥0}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ x, |f x - g x| ≤ (δ : ℝ))
    (hf_int : Integrable f P) (hg_int : Integrable g P)
    (hX : ∀ i, Measurable (X i)) (hindep : iIndepFun X μ)
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF
      (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω)
      (δ ^ 2 / n) μ := by
  have hkey : (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω)
      = empiricalProcess P n X (f - g) := by
    funext ω; rw [empiricalProcess_sub hf_int hg_int ω]
  rw [hkey]
  exact hasSubgaussianMGF_empiricalProcess_core (h := f - g) (δ := δ)
    (hf.sub hg) (fun x => by simpa [Pi.sub_apply] using hfg x) hX hindep hlaw

/-- **Step 1, MGF level** (HDP §8.2, proof of Theorem 8.2.3): the increment
`X_f − X_g` has sub-Gaussian MGF with proxy **exactly** `δ²/n` where
`‖f − g‖∞ ≤ δ`.

**Formalization note.** As stated over an abstract sample space `Ω'` with only a
*difference* bound `‖f − g‖∞ ≤ δ`, the two population terms `∫ f dP` and
`∫ g dP` need not individually be finite, and `HasSubgaussianMGF` of the raw
difference forces its mean to vanish, i.e. `∫ f dP − ∫ g dP = ∫ (f − g) dP`.
When `f, g` are `P`-integrable (as at every call site — bounded/continuous
classes) this holds and the bound follows from
`hasSubgaussianMGF_empiricalProcess_sub_of_integrable`. -/
theorem hasSubgaussianMGF_empiricalProcess_sub [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f g : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class members; regularity, no book content
    (hf : Measurable f) (hg : Measurable g)
    -- USER-INPUT: sup-distance bound ‖f − g‖∞ ≤ δ; HDP §8.2 Step 1
    (hfg : ∀ x, |f x - g x| ≤ (δ : ℝ))
    -- LEAN-ONLY: individual integrability — REQUIRED (statement fix at the
    -- debt gate: without it the population terms are Bochner junk and the
    -- claim is FALSE, e.g. non-integrable f with g = f − 1 makes the
    -- increment the constant 1; holds at every call site since class
    -- members are bounded)
    (hf_int : Integrable f P) (hg_int : Integrable g P)
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF
      (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω)
      (δ ^ 2 / n) μ :=
  hasSubgaussianMGF_empiricalProcess_sub_of_integrable hf hg hfg hf_int hg_int
    hX hindep hlaw

/-- Single-function corollary (`g = 0`): `X_f` itself is sub-Gaussian with
proxy `B²/n` when `‖f‖∞ ≤ B` (HDP §8.2). -/
theorem hasSubgaussianMGF_empiricalProcess [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f : Ω' → ℝ} {B : ℝ≥0}
    -- LEAN-ONLY: measurability of the class member; regularity, no book content
    (hf : Measurable f)
    -- USER-INPUT: uniform bound ‖f‖∞ ≤ B; HDP §8.2
    (hfB : ∀ x, |f x| ≤ (B : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    HasSubgaussianMGF (empiricalProcess P n X f) (B ^ 2 / n) μ :=
  hasSubgaussianMGF_empiricalProcess_core hf hfB hX hindep hlaw

/-- Repackaging into the project predicate `IsSubGaussian` — the exact input
shape of the Orlicz bridge B3 (`subGaussianNorm_le_of_isSubGaussian`). -/
theorem isSubGaussian_empiricalProcess_sub [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f g : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class members; regularity, no book content
    (hf : Measurable f) (hg : Measurable g)
    -- USER-INPUT: sup-distance bound ‖f − g‖∞ ≤ δ; HDP §8.2 Step 1
    (hfg : ∀ x, |f x - g x| ≤ (δ : ℝ))
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    IsSubGaussian
      (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω)
      (δ ^ 2 / n) μ := by
  -- Centering is automatic in `IsSubGaussian`: the increment `Y = X_f − X_g`
  -- differs from the genuinely centered sum `V = X_{f−g}` by the constant
  -- `K = ∫(f−g)dP − (∫f dP − ∫g dP)`, and `Y − ∫Y = V` exactly (the constant
  -- cancels), so no individual integrability of `f, g` is needed.
  rw [isSubGaussian_iff]
  set h : Ω' → ℝ := fun x => f x - g x with hh_def
  have hh_meas : Measurable h := hf.sub hg
  have hhδ : ∀ x, |h x| ≤ (δ : ℝ) := fun x => hfg x
  -- the centered scaled sum `V` and its MGF (from the core, single function `h`)
  have hV : HasSubgaussianMGF (empiricalProcess P n X h) (δ ^ 2 / n) μ :=
    hasSubgaussianMGF_empiricalProcess_core hh_meas hhδ hX hindep hlaw
  -- `Y = V + K` pointwise, with `K` a constant
  set Y : Ω → ℝ := fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω
    with hY_def
  set K : ℝ := (∫ x, h x ∂P) - ((∫ x, f x ∂P) - ∫ x, g x ∂P) with hK_def
  have hYV : ∀ ω, Y ω = empiricalProcess P n X h ω + K := by
    intro ω
    simp only [hY_def, hK_def, empiricalProcess, hh_def, Finset.sum_sub_distrib, mul_sub]
    ring
  -- `V` is mean-zero, so `∫ Y = K`
  have hh_int : Integrable h P :=
    (integrable_const (δ : ℝ)).mono' hh_meas.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hhδ x)
  have hVmean : ∫ ω, empiricalProcess P n X h ω ∂μ = 0 :=
    integral_empiricalProcess hh_int hX hlaw
  have hYmean : ∫ ω, Y ω ∂μ = K := by
    simp only [hYV]
    rw [integral_add hV.integrable (integrable_const K), hVmean, integral_const,
      probReal_univ, one_smul, zero_add]
  -- hence `Y − ∫Y = V` as functions, transferring the MGF bound
  have hfun : (fun ω => Y ω - ∫ x, Y x ∂μ) = empiricalProcess P n X h := by
    funext ω; rw [hYmean, hYV]; ring
  rw [show (fun ω => (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω) ω
      - ∫ x, (empiricalProcess P n X f x - empiricalProcess P n X g x) ∂μ)
      = (fun ω => Y ω - ∫ x, Y x ∂μ) from rfl, hfun]
  exact hV

/-- **Step 1, ψ₂ level** (HDP §8.2 Step 1):
`‖X_f − X_g‖_{ψ₂} ≤ √(6·δ²/n) = √6·δ/√n` — the Orlicz bridge B3 applied at
`σ² = δ²/n`, carrier `√(6σ²)` verbatim (explicit `√6`, no alias constant). -/
theorem subGaussianNorm_empiricalProcess_sub_le [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P] [NeZero n] {f g : Ω' → ℝ} {δ : ℝ≥0}
    -- LEAN-ONLY: measurability of the class members; regularity, no book content
    (hf : Measurable f) (hg : Measurable g)
    -- USER-INPUT: sup-distance bound ‖f − g‖∞ ≤ δ; HDP §8.2 Step 1
    (hfg : ∀ x, |f x - g x| ≤ (δ : ℝ))
    -- LEAN-ONLY: individual integrability — REQUIRED (statement fix at the
    -- debt gate: without it the population terms are Bochner junk and the
    -- claim is FALSE, e.g. non-integrable f with g = f − 1 makes the
    -- increment the constant 1; holds at every call site since class
    -- members are bounded)
    (hf_int : Integrable f P) (hg_int : Integrable g P)
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    subGaussianNorm
      (fun ω => empiricalProcess P n X f ω - empiricalProcess P n X g ω) μ
      ≤ (NNReal.sqrt (6 * (δ ^ 2 / n)) : ℝ≥0∞) :=
  subGaussianNorm_le_of_hasSubgaussianMGF
    (hasSubgaussianMGF_empiricalProcess_sub hf hg hfg hf_int hg_int hX hindep
      hlaw)

/-- **Increment condition over `C([0,1], ℝ)`** (HDP §8.1, Definition 8.1.1):
`‖X_f − X_g‖_{ψ₂} ≤ (√6/√n) · dist f g` for *all* continuous `f, g` on the
sup-metric index space (`dist_apply_le_dist` supplies the pointwise bound).
Named-sorry fallback of `hdp-emp-increments`. -/
theorem subGaussianNorm_empiricalProcess_sub_le_dist [IsProbabilityMeasure μ]
    {P : Measure unitInterval} [IsProbabilityMeasure P] [NeZero n]
    {X : Fin n → Ω → unitInterval} {f g : C(unitInterval, ℝ)}
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    subGaussianNorm
      (fun ω => empiricalProcess P n X ⇑f ω - empiricalProcess P n X ⇑g ω) μ
      ≤ ENNReal.ofReal (Real.sqrt 6 / Real.sqrt n * dist f g) := by
  -- continuous functions on the compact interval are bounded, hence integrable
  set δ : ℝ≥0 := (dist f g).toNNReal with hδ_def
  have hdist_nonneg : (0 : ℝ) ≤ dist f g := dist_nonneg
  have hδcoe : (δ : ℝ) = dist f g := Real.coe_toNNReal _ hdist_nonneg
  have hfg : ∀ x, |f x - g x| ≤ (δ : ℝ) := by
    intro x
    rw [hδcoe]
    have := ContinuousMap.dist_apply_le_dist (f := f) (g := g) x
    simpa [Real.dist_eq] using this
  have hfm : Measurable (⇑f) := f.continuous.measurable
  have hgm : Measurable (⇑g) := g.continuous.measurable
  have hf_int : Integrable (⇑f) P :=
    (integrable_const (‖f‖ : ℝ)).mono' hfm.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using (f.norm_coe_le_norm x))
  have hg_int : Integrable (⇑g) P :=
    (integrable_const (‖g‖ : ℝ)).mono' hgm.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using (g.norm_coe_le_norm x))
  have hmgf := hasSubgaussianMGF_empiricalProcess_sub_of_integrable
    hfm hgm hfg hf_int hg_int hX hindep hlaw
  have hbound := subGaussianNorm_le_of_hasSubgaussianMGF hmgf
  refine hbound.trans (le_of_eq ?_)
  -- `√(6·(δ²/n)) = √6/√n · dist f g` in `ℝ≥0∞`
  rw [ENNReal.coe_nnreal_eq]
  congr 1
  rw [Real.coe_sqrt]
  push_cast
  rw [hδcoe]
  have hnn : (0 : ℝ) ≤ Real.sqrt 6 / Real.sqrt n * dist f g := by positivity
  rw [show (6 : ℝ) * (dist f g ^ 2 / n)
      = (Real.sqrt 6 / Real.sqrt n * dist f g) ^ 2 by
    have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    have hnsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    rw [mul_pow, div_pow, h6, hnsq]; ring]
  exact Real.sqrt_sq hnn

/-- **Packaged increments** (HDP §8.1, Definition 8.1.1): the empirical
process indexed by `C(unitInterval, ℝ)` has `K`-sub-Gaussian increments with
`K = √6/√n`, stated on `T = Set.univ` (restrict downstream via
`SubGaussianIncrements.mono_set`). -/
theorem subGaussianIncrements_empiricalProcess [IsProbabilityMeasure μ]
    {P : Measure unitInterval} [IsProbabilityMeasure P] [NeZero n]
    {X : Fin n → Ω → unitInterval}
    -- LEAN-ONLY: measurability of the data; regularity, no book content
    (hX : ∀ i, Measurable (X i))
    -- USER-INPUT: independence of the sample; HDP §8.2, Theorem 8.2.3
    (hindep : iIndepFun X μ)
    -- USER-INPUT: common law P of the data on [0,1]; HDP §8.2, Theorem 8.2.3
    (hlaw : ∀ i, μ.map (X i) = P) :
    SubGaussianIncrements (fun (f : C(unitInterval, ℝ)) => empiricalProcess P n X ⇑f)
      (Real.toNNReal (Real.sqrt 6 / Real.sqrt n)) Set.univ μ := by
  intro s _ t _
  -- apply the `dist`-form increment bound with roles `f := t`, `g := s`
  have hbound := subGaussianNorm_empiricalProcess_sub_le_dist
    (μ := μ) (P := P) (n := n) (X := X) (f := t) (g := s) hX hindep hlaw
  refine hbound.trans (le_of_eq ?_)
  -- `ofReal (√6/√n · dist t s) = (√6/√n).toNNReal * edist s t`
  rw [edist_dist, dist_comm t s,
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Real.sqrt 6 / Real.sqrt n)]
  rfl

end StatLean.ConcentrationInequalities
