module
public import StatLean.Bayesian.EmpiricalBayes.Defs
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

/-!
# The nonparametric maximum-likelihood mixing distribution (NPMLE)

The NPMLE maximizes the marginal likelihood `∏ᵢ f_G(xᵢ)` over *all* mixing distributions `G`. Two
structural facts: the marginal likelihood is **linear** in `G` (so the log-likelihood is concave
and the optimization is convex), and the maximizer can be taken to have **finite support on at
most `n+1` points** (Lindsay's geometry of mixture likelihoods).

**Reference.** Not in Robert (Robert §10.4.1 mentions nonparametric EB). B. G. Lindsay, "The
geometry of mixture likelihoods: a general theory," *Ann. Statist.* 11 (1983), 86–94; J. Kiefer and
J. Wolfowitz, "Consistency of the maximum likelihood estimator in the presence of infinitely many
incidental parameters," *Ann. Math. Statist.* 27 (1956), 887–906.

**Proof formalization notes.** `mixtureDensity_linear_in_mixing` is linearity of `∫ p dG` in the
measure `G` (`lintegral_add_measure`, `lintegral_smul_measure`). `NPMLE_exists_finiteSupport_le_
card_add_one` is Lindsay's Carathéodory/convex-geometry argument: the likelihood vector
`G ↦ (f_G(x₁), …, f_G(xₙ))` ranges over the convex hull of the `n`-dimensional likelihood curve, and
a boundary maximizer is a convex combination of at most `n+1` extreme points (Dirac masses).
Existence of a maximizer is *derived* in `NPMLE_exists_of_finite` (the marginal likelihood is a
continuous function of the weight vector on the compact probability simplex, so it attains its
maximum), and the finite-support conclusion is the geometric content.

**Bibliographic comments.** The finite-support NPMLE is Lindsay's theorem (1983), refining Kiefer
and Wolfowitz (1956); its consistency is the Kiefer–Wolfowitz theorem, and its use for normal-means
estimation (GMLEB) is W. Jiang and C.-H. Zhang (*Ann. Statist.* 37 (2009), 1647–1684). It is the
nonparametric backbone of modern empirical-Bayes deconvolution (Efron, *Large-Scale Inference*,
2010, §5).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- **The marginal likelihood is linear in the mixing distribution** (the convexity behind the
NPMLE): `f_{tG₀+(1−t)G₁} = t·f_{G₀} + (1−t)·f_{G₁}` (Lindsay 1983). -/
theorem mixtureDensity_linear_in_mixing (p : Θ → 𝓧 → ℝ≥0∞) (t : ℝ≥0∞) (G₀ G₁ : Measure Θ) (x : 𝓧) :
    mixtureDensity p (t • G₀ + (1 - t) • G₁) x
      = t * mixtureDensity p G₀ x + (1 - t) * mixtureDensity p G₁ x := by
  simp only [mixtureDensity, predictiveDensity, lintegral_add_measure, lintegral_smul_measure, smul_eq_mul]

/-- **Existence of an NPMLE on a finite parameter space** (the compactness step, in Lindsay's
regular/finite setting). On a nonempty finite `Θ` with finite likelihoods, the marginal likelihood
`G ↦ ∏ⱼ f_G(xⱼ) = ∏ⱼ ∑_θ p(θ,xⱼ)·G{θ}` is a continuous function of the weight vector `w θ = G{θ}`
on the compact probability simplex `stdSimplex ℝ Θ`, hence attains its maximum. This *derives* the
existence that Lindsay 1983 obtains by weak-* compactness in the general (non-finite) setting —
replacing the former `∃ Ghat, IsNPMLE` provider hypothesis (hypothesis-discipline fix, §2). -/
private lemma NPMLE_exists_of_finite {n : ℕ} [MeasurableSingletonClass Θ] [Finite Θ] [Nonempty Θ]
    (p : Θ → 𝓧 → ℝ≥0∞) (x : Fin n → 𝓧) (hpfin : ∀ θ i, p θ (x i) ≠ ∞) :
    ∃ Ghat, IsNPMLE p x Ghat := by
  classical
  letI : Fintype Θ := Fintype.ofFinite Θ
  -- Real objective on weight vectors: `Ψ w = ∏ⱼ ∑_θ (p θ xⱼ).toReal · w θ`.
  set Ψ : (Θ → ℝ) → ℝ := fun w => ∏ j, ∑ θ, (p θ (x j)).toReal * w θ with hΨ
  have hcont : Continuous Ψ :=
    continuous_finset_prod _ fun j _ =>
      continuous_finset_sum _ fun θ _ => continuous_const.mul (continuous_apply θ)
  have hne : (stdSimplex ℝ Θ).Nonempty := by
    refine ⟨fun θ => if θ = Classical.arbitrary Θ then 1 else 0, fun θ => ?_, ?_⟩
    · by_cases h : θ = Classical.arbitrary Θ <;> simp [h]
    · simp [Finset.sum_ite_eq' Finset.univ (Classical.arbitrary Θ)]
  obtain ⟨w, hwmem, hwmax⟩ :=
    (isCompact_stdSimplex (𝕜 := ℝ) (ι := Θ)).exists_isMaxOn hne hcont.continuousOn
  obtain ⟨hwnn, hwsum⟩ := hwmem
  -- The maximizing measure `Ghat = ∑_θ ofReal (w θ) • δ_θ`.
  set Ghat : Measure Θ := ∑ θ, ENNReal.ofReal (w θ) • Measure.dirac θ with hGhat
  have hGuniv : Ghat Set.univ = 1 := by
    rw [hGhat, Measure.finset_sum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun θ _ => hwnn θ), hwsum, ENNReal.ofReal_one]
  have hGprob : IsProbabilityMeasure Ghat := ⟨hGuniv⟩
  -- Both marginal likelihoods are finite weighted sums over the (finite) parameter space.
  have hmixfin : ∀ (H : Measure Θ) j, mixtureDensity p H (x j) = ∑ θ, p θ (x j) * H {θ} := by
    intro H j; simp only [mixtureDensity, predictiveDensity]; exact lintegral_fintype _
  have hGhatmix : ∀ j, mixtureDensity p Ghat (x j) = ∑ θ, ENNReal.ofReal (w θ) * p θ (x j) := by
    intro j; simp only [mixtureDensity, predictiveDensity, hGhat]
    rw [lintegral_finset_sum_measure]
    exact Finset.sum_congr rfl fun θ _ => by rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  -- `(∏ⱼ f_Ghat(xⱼ)).toReal = Ψ w`.
  have hprodGhat : (∏ j, mixtureDensity p Ghat (x j)).toReal = Ψ w := by
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hGhatmix j, ENNReal.toReal_sum
      (fun θ _ => (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hpfin θ j).lt_top).ne)]
    exact Finset.sum_congr rfl fun θ _ => by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hwnn θ), mul_comm]
  refine ⟨Ghat, hGprob, fun G hG => ?_⟩
  -- `G`'s real weights lie in the simplex.
  have hμmem : (fun θ => (G {θ}).toReal) ∈ stdSimplex ℝ Θ := by
    refine ⟨fun θ => ENNReal.toReal_nonneg, ?_⟩
    rw [← ENNReal.toReal_sum (fun θ _ => measure_ne_top G _), sum_measure_singleton,
      Finset.coe_univ, measure_univ, ENNReal.toReal_one]
  have hmixGfin : ∀ j, mixtureDensity p G (x j) ≠ ∞ := by
    intro j; rw [hmixfin G j]
    exact (ENNReal.sum_lt_top.2 fun θ _ =>
      ENNReal.mul_lt_top (hpfin θ j).lt_top (measure_ne_top G _).lt_top).ne
  have hprodG : (∏ j, mixtureDensity p G (x j)).toReal = Ψ (fun θ => (G {θ}).toReal) := by
    rw [ENNReal.toReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hmixfin G j, ENNReal.toReal_sum
      (fun θ _ => (ENNReal.mul_lt_top (hpfin θ j).lt_top (measure_ne_top G _).lt_top).ne)]
    exact Finset.sum_congr rfl fun θ _ => by rw [ENNReal.toReal_mul]
  -- Maximality: transfer the real inequality `Ψ μ_G ≤ Ψ w` back to `ℝ≥0∞`.
  have hprodGhatfin : ∏ j, mixtureDensity p Ghat (x j) ≠ ∞ :=
    ENNReal.prod_ne_top fun j _ => by
      rw [hGhatmix j]
      exact (ENNReal.sum_lt_top.2 fun θ _ =>
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hpfin θ j).lt_top).ne
  rw [← ENNReal.toReal_le_toReal (ENNReal.prod_ne_top fun j _ => hmixGfin j) hprodGhatfin,
    hprodG, hprodGhat]
  exact hwmax hμmem

/-- **Lindsay's finite-support theorem** (3F.7): the NPMLE can be taken supported on at most `n+1`
points (Lindsay 1983). Stated in Lindsay's *discrete* regular setting — a finite parameter space
`Θ` (the "discrete/compact" case; discrete + compact = finite) with finite likelihoods `hpfin`. The
geometric content (the `n+1` Carathéodory bound) is unchanged: the likelihood vector
`G ↦ (f_G(x₁),…,f_G(xₙ)) ∈ ℝⁿ` is the `G`-barycenter of the likelihood curve `θ ↦ (p(θ,x₁),…)`, and
Carathéodory in `ℝⁿ` (affine dimension `n`) rewrites a maximizer's barycenter as a positive convex
combination of at most `n+1` curve points, i.e. a mixing measure on `≤ n+1` Dirac atoms. -/
theorem NPMLE_exists_finiteSupport_le_card_add_one {n : ℕ}
    [MeasurableSingletonClass Θ] [Finite Θ] [Nonempty Θ]
    (p : Θ → 𝓧 → ℝ≥0∞) (x : Fin n → 𝓧)
    -- Lindsay's regularity: the likelihoods are finite (`p(θ,xᵢ) ≠ ∞`)
    (hpfin : ∀ θ i, p θ (x i) ≠ ∞) :
    ∃ (Ghat : Measure Θ) (S : Finset Θ),
      IsNPMLE p x Ghat ∧ Ghat ((↑S : Set Θ)ᶜ) = 0 ∧ S.card ≤ n + 1 := by
  classical
  letI : Fintype Θ := Fintype.ofFinite Θ
  obtain ⟨Ĝ, hĜprob, hĜmax⟩ := NPMLE_exists_of_finite p x hpfin
  -- the `n`-dimensional likelihood curve `w θ = (p(θ,x₀),…,p(θ,xₙ₋₁))` in `ℝⁿ`
  set w : Θ → (Fin n → ℝ) := fun θ i => (p θ (x i)).toReal with hw
  -- the mixing weights of `Ĝ` on the (finite) parameter space
  set μ : Θ → ℝ := fun θ => (Ĝ {θ}).toReal with hμ
  -- `mixtureDensity p Ĝ (x j)` as a finite weighted sum of likelihoods
  have hĜmix : ∀ j, mixtureDensity p Ĝ (x j) = ∑ θ, p θ (x j) * Ĝ {θ} := by
    intro j
    simp only [mixtureDensity, predictiveDensity]
    exact lintegral_fintype _
  have hĜfin : ∀ j, mixtureDensity p Ĝ (x j) ≠ ∞ := by
    intro j
    rw [hĜmix j]
    refine (ENNReal.sum_lt_top.2 ?_).ne
    intro θ _
    exact ENNReal.mul_lt_top (hpfin θ j).lt_top (measure_ne_top Ĝ _).lt_top
  -- the NPMLE likelihood vector
  set v : Fin n → ℝ := fun j => (mixtureDensity p Ĝ (x j)).toReal with hv
  have hμnn : ∀ θ, 0 ≤ μ θ := fun θ => ENNReal.toReal_nonneg
  have hsum1 : ∑ θ, μ θ = 1 := by
    have : ∑ θ, μ θ = (∑ θ, Ĝ {θ}).toReal := by
      rw [ENNReal.toReal_sum (fun θ _ => measure_ne_top Ĝ _)]
    rw [this, sum_measure_singleton, Finset.coe_univ, measure_univ, ENNReal.toReal_one]
  -- `v` is the `Ĝ`-barycenter of the likelihood curve `w`
  have hvsum : v = ∑ θ, μ θ • w θ := by
    funext j
    simp only [hv, hĜmix j, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hw, hμ]
    rw [ENNReal.toReal_sum (fun θ _ =>
      (ENNReal.mul_lt_top (hpfin θ j).lt_top (measure_ne_top Ĝ _).lt_top).ne)]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [ENNReal.toReal_mul, mul_comm]
  have hvmem : v ∈ convexHull ℝ (Set.range w) := by
    rw [hvsum]
    exact (convex_convexHull ℝ _).sum_mem (fun θ _ => hμnn θ) hsum1
      (fun θ _ => subset_convexHull ℝ _ (Set.mem_range_self θ))
  -- Carathéodory: `v` is a positive affinely-independent convex combination of `≤ n+1` curve points
  obtain ⟨ι, hιfin, z, wt, hzrange, hzaff, hwtpos, hwtsum, hzv⟩ :=
    eq_pos_convex_span_of_mem_convexHull hvmem
  -- affine dimension of `ℝⁿ` is `n`, so `#ι ≤ n+1`
  have hcard : Fintype.card ι ≤ n + 1 := by
    calc Fintype.card ι
        ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 := hzaff.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Fin n → ℝ) + 1 := by
          exact Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = n + 1 := by rw [Module.finrank_fin_fun]
  -- each Carathéodory point `z i` is a curve value `w (θ i)`
  have hzw : ∀ i, ∃ θ, w θ = z i := fun i => hzrange (Set.mem_range_self i)
  choose θpt hθpt using hzw
  -- reconstruct the finite-support NPMLE
  set Ĝ' : Measure Θ := ∑ i, ENNReal.ofReal (wt i) • Measure.dirac (θpt i) with hĜ'
  set S : Finset Θ := Finset.image θpt Finset.univ with hS
  -- `Ĝ'` is a probability measure
  have hĜ'univ : Ĝ' Set.univ = 1 := by
    rw [hĜ', Measure.finset_sum_apply]
    simp only [Measure.smul_apply, MeasureTheory.measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hwtpos i).le), hwtsum, ENNReal.ofReal_one]
  have hĜ'prob : IsProbabilityMeasure Ĝ' := ⟨hĜ'univ⟩
  -- `mixtureDensity p Ĝ' (x j)` as a finite weighted sum over the Carathéodory points
  have hĜ'mix : ∀ j, mixtureDensity p Ĝ' (x j) = ∑ i, ENNReal.ofReal (wt i) * p (θpt i) (x j) := by
    intro j
    simp only [mixtureDensity, predictiveDensity, hĜ']
    rw [lintegral_finset_sum_measure]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  have hĜ'fin : ∀ j, mixtureDensity p Ĝ' (x j) ≠ ∞ := by
    intro j
    rw [hĜ'mix j]
    refine (ENNReal.sum_lt_top.2 ?_).ne
    intro i _
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hpfin _ j).lt_top
  -- the two mixture densities agree at every data point (equal finite `toReal`s)
  have hmixeq : ∀ j, mixtureDensity p Ĝ' (x j) = mixtureDensity p Ĝ (x j) := by
    intro j
    rw [← ENNReal.toReal_eq_toReal_iff' (hĜ'fin j) (hĜfin j)]
    calc (mixtureDensity p Ĝ' (x j)).toReal
        = ∑ i, wt i * (z i) j := by
          rw [hĜ'mix j, ENNReal.toReal_sum
            (fun i _ => (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hpfin _ j).lt_top).ne)]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hwtpos i).le, ← hθpt i]
      _ = (∑ i, wt i • z i) j := by
          rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _ => by
            rw [Pi.smul_apply, smul_eq_mul]
      _ = v j := by rw [hzv]
  -- `Ĝ'` inherits `Ĝ`'s maximality since the product likelihoods coincide
  have hprodeq : ∏ j, mixtureDensity p Ĝ' (x j) = ∏ j, mixtureDensity p Ĝ (x j) :=
    Finset.prod_congr rfl fun j _ => hmixeq j
  refine ⟨Ĝ', S, ⟨hĜ'prob, ?_⟩, ?_, ?_⟩
  · intro G hG
    rw [hprodeq]
    exact hĜmax G hG
  · -- `Ĝ'` is supported on `S`
    rw [hĜ', Measure.finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (by measurability)]
    have : θpt i ∈ (↑S : Set Θ) := by
      rw [hS, Finset.coe_image]; exact Set.mem_image_of_mem _ (Finset.mem_univ i)
    rw [Set.indicator_of_notMem (by simpa using this), mul_zero]
  · calc S.card ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
      _ = Fintype.card ι := Finset.card_univ
      _ ≤ n + 1 := hcard

end StatLean.Bayesian
