module
public import StatLean.ConcentrationInequalities.Orlicz.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Orlicz norm — order and algebra API

Order/algebra properties of the Luxemburg infimum requiring no limiting
arguments: upward closure of the gauge set, witness extraction from the
`⨅`, a.e.-congruence and domination monotonicity
$$ |X| \le |Y| \text{ a.e.} \implies \|X\|_\psi \le \|Y\|_\psi, $$
sign/abs invariance, the norm of the zero function, and abs-homogeneity
$$ \|cX\|_\psi = |c| \, \|X\|_\psi $$
(the second half of the B4 norm-axioms bridge; the triangle inequality is
`Orlicz/Triangle.lean`).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Exercise 2.42 (norm axioms for `‖·‖_{ψ₂}`),
Exercise 2.43 (general Orlicz norm), §2.6.1 and §2.8.2 folklore properties.

**Proof formalization notes.** Everything here is `⨅`-manipulation over the
gauge set `orliczSet` plus pointwise integrand comparisons — no monotone
convergence (that is `Orlicz/Attainment.lean`). Homogeneity is an exact
gauge-set bijection `K ↦ ‖c‖₊·K`, unconditional for `c ≠ 0`; the `c = 0` edge
needs `ψ 0 ≤ 0` (else the zero function might have positive norm) and is split
off as `orliczNorm_const_mul_zero`. The witness extraction
`exists_mem_orliczSet_lt_of_orliczNorm_lt` is the ε-free workhorse consumed by
Lemmas 2.8.5/2.8.6 and the attainment lemma. Named-sorry fallback of this work
item: `orliczNorm_const_mul` (the gauge-set bijection under scaling).

**Bibliographic comments.** The norm axioms for Luxemburg functionals are due
to W. A. J. Luxemburg, *Banach function spaces*, Thesis, Delft, 1955; the
sub-Gaussian/sub-exponential instances are Vershynin's Exercises 2.42–2.43.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ψ : ℝ → ℝ}

/-- The gauge set is upward closed: a larger scale makes the integrand
smaller (HDP §2.6.1 folklore). -/
lemma orliczSet_upward
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ : MonotoneOn ψ (Set.Ici 0))
    {X : Ω → ℝ} {μ : Measure Ω} {K K' : ℝ≥0}
    -- LEAN-ONLY: comparison of the two scales; no book scope change
    (hKK' : K ≤ K')
    -- LEAN-ONLY: gauge-set membership of the smaller scale; caller witness
    (hK : K ∈ orliczSet ψ X μ) :
    K' ∈ orliczSet ψ X μ := by
  obtain ⟨hKpos, hKint⟩ := hK
  have hK'pos : 0 < K' := lt_of_lt_of_le hKpos hKK'
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hKK'R : (K : ℝ) ≤ (K' : ℝ) := by exact_mod_cast hKK'
  refine ⟨hK'pos, le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_) hKint⟩
  have hdiv : |X ω| / (K' : ℝ) ≤ |X ω| / (K : ℝ) := by gcongr
  exact hψ (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by positivity)) hdiv

/-- Unfolded form of `orliczNorm_le_of_mem`: a verified `ψ`-moment condition
at scale `K` bounds the norm by `K`. -/
theorem orliczNorm_le_of_lintegral_le {X : Ω → ℝ} {μ : Measure Ω} {K : ℝ≥0}
    -- LEAN-ONLY: positive scale; K = 0 is excluded from the gauge set by definition
    (hK : 0 < K)
    -- LEAN-ONLY: the Luxemburg condition at scale K; caller witness, no book content
    (h : ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K : ℝ))) ∂μ ≤ 1) :
    orliczNorm ψ X μ ≤ (K : ℝ≥0∞) :=
  orliczNorm_le_of_mem ⟨hK, h⟩

/-- Witness extraction from the Luxemburg infimum: any strict upper bound on
the norm is beaten by a genuine gauge-set member (ε-free `⨅` workhorse for
Lemmas 2.8.5/2.8.6 and the attainment lemma). -/
theorem exists_mem_orliczSet_lt_of_orliczNorm_lt {X : Ω → ℝ} {μ : Measure Ω}
    {c : ℝ≥0∞}
    -- LEAN-ONLY: strict bound on the infimum; pure order-theoretic input
    (h : orliczNorm ψ X μ < c) :
    ∃ K ∈ orliczSet ψ X μ, (K : ℝ≥0∞) < c := by
  rw [orliczNorm] at h
  simpa only [iInf_lt_iff, exists_prop] using h

/-- The Orlicz norm only depends on the a.e.-class of `X`. -/
theorem orliczNorm_congr_ae {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e. equality; lintegral_congr_ae transport, no book scope
    (h : X =ᵐ[μ] Y) :
    orliczNorm ψ X μ = orliczNorm ψ Y μ := by
  have hint : ∀ K : ℝ≥0, ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K : ℝ))) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (ψ (|Y ω| / (K : ℝ))) ∂μ := by
    intro K
    refine lintegral_congr_ae ?_
    filter_upwards [h] with ω hω
    rw [hω]
  have hset : orliczSet ψ X μ = orliczSet ψ Y μ := by
    ext K
    rw [mem_orliczSet_iff, mem_orliczSet_iff, hint K]
  unfold orliczNorm
  rw [hset]

/-- Domination monotonicity: `|X| ≤ |Y|` a.e. implies `‖X‖_ψ ≤ ‖Y‖_ψ`
(HDP §2.6/§2.8 folklore; used by Lemma 2.8.6). -/
theorem orliczNorm_mono_ae
    -- USER-INPUT: ψ increasing on [0,∞); HDP Exercise 2.42 (Orlicz function)
    (hψ : MonotoneOn ψ (Set.Ici 0))
    {X Y : Ω → ℝ} {μ : Measure Ω}
    -- USER-INPUT: a.e. domination |X| ≤ |Y|; HDP §2.6/§2.8 folklore hypothesis
    (h : ∀ᵐ ω ∂μ, |X ω| ≤ |Y ω|) :
    orliczNorm ψ X μ ≤ orliczNorm ψ Y μ := by
  rw [show orliczNorm ψ Y μ = ⨅ K ∈ orliczSet ψ Y μ, (K : ℝ≥0∞) from rfl]
  refine le_iInf₂ fun K hKmem => orliczNorm_le_of_mem ?_
  obtain ⟨hKpos, hKint⟩ := hKmem
  refine ⟨hKpos, le_trans (lintegral_mono_ae ?_) hKint⟩
  filter_upwards [h] with ω hω
  refine ENNReal.ofReal_le_ofReal
    (hψ (Set.mem_Ici.mpr (by positivity)) (Set.mem_Ici.mpr (by positivity)) ?_)
  gcongr

/-- Sign invariance (`|−x| = |x|`); the two-sided step of Bernstein 2.9.1. -/
@[simp] theorem orliczNorm_neg (ψ : ℝ → ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    orliczNorm ψ (fun ω => -X ω) μ = orliczNorm ψ X μ := by
  have hset : orliczSet ψ (fun ω => -X ω) μ = orliczSet ψ X μ := by
    ext K; simp only [mem_orliczSet_iff, abs_neg]
  unfold orliczNorm; rw [hset]

/-- Abs invariance (`||x|| = |x|`). -/
@[simp] theorem orliczNorm_abs (ψ : ℝ → ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    orliczNorm ψ (fun ω => |X ω|) μ = orliczNorm ψ X μ := by
  have hset : orliczSet ψ (fun ω => |X ω|) μ = orliczSet ψ X μ := by
    ext K; simp only [mem_orliczSet_iff, abs_abs]
  unfold orliczNorm; rw [hset]

/-- The zero function has Orlicz norm `0` (HDP Exercise 2.42): every `K > 0`
is a gauge once `ψ 0 ≤ 0`. -/
theorem orliczNorm_zero
    -- USER-INPUT: ψ(0) ≤ 0 (book: ψ(0) = 0); HDP Exercise 2.42 (Orlicz function)
    (hψ0 : ψ 0 ≤ 0)
    (μ : Measure Ω) :
    orliczNorm ψ (fun _ => (0 : ℝ)) μ = 0 := by
  have hmem : ∀ K : ℝ≥0, 0 < K → K ∈ orliczSet ψ (fun _ => (0 : ℝ)) μ := by
    intro K hK
    refine ⟨hK, ?_⟩
    have h0 : ENNReal.ofReal (ψ (|(0 : ℝ)| / (K : ℝ))) = 0 := by
      rw [abs_zero, zero_div]; exact ENNReal.ofReal_eq_zero.mpr hψ0
    simp only [h0, lintegral_zero]
    exact zero_le_one
  refine le_antisymm ?_ (zero_le)
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  rw [zero_add]
  exact orliczNorm_le_of_mem (hmem ε hε)

/-- Abs-homogeneity `‖c·X‖_ψ = |c|·‖X‖_ψ` for `c ≠ 0` (HDP Exercise 2.42,
B4 part 2); exact gauge-set bijection `K ↦ ‖c‖₊·K`. -/
theorem orliczNorm_const_mul {X : Ω → ℝ} {μ : Measure Ω} {c : ℝ}
    -- LEAN-ONLY: c ≠ 0 keeps the gauge-set bijection exact; c = 0 edge split
    -- off as orliczNorm_const_mul_zero (needs ψ 0 ≤ 0)
    (hc : c ≠ 0) :
    orliczNorm ψ (fun ω => c * X ω) μ = (‖c‖₊ : ℝ≥0∞) * orliczNorm ψ X μ := by
  set c₀ : ℝ≥0 := ‖c‖₊ with hc₀def
  have hc₀0 : c₀ ≠ 0 := by rw [hc₀def, ne_eq, nnnorm_eq_zero]; exact hc
  have hc₀pos : (0 : ℝ≥0) < c₀ := zero_lt_iff.mpr hc₀0
  have habs : (c₀ : ℝ) = |c| := by rw [hc₀def]; simp [Real.norm_eq_abs]
  have hcabs0 : |c| ≠ 0 := abs_ne_zero.mpr hc
  -- pointwise integrand identity at scale `c₀ * K'`
  have hInt : ∀ K' : ℝ≥0,
      ∫⁻ ω, ENNReal.ofReal (ψ (|c * X ω| / ((c₀ * K' : ℝ≥0) : ℝ))) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (ψ (|X ω| / (K' : ℝ))) ∂μ := by
    intro K'
    refine lintegral_congr (fun ω => ?_)
    have harg : |c * X ω| / ((c₀ * K' : ℝ≥0) : ℝ) = |X ω| / (K' : ℝ) := by
      rw [abs_mul, NNReal.coe_mul, habs, mul_div_mul_left _ _ hcabs0]
    rw [harg]
  -- gauge set of `c·X` is the `c₀`-scaling of the gauge set of `X`
  have hset : orliczSet ψ (fun ω => c * X ω) μ
      = (fun K' : ℝ≥0 => c₀ * K') '' orliczSet ψ X μ := by
    ext K
    simp only [Set.mem_image, mem_orliczSet_iff]
    constructor
    · rintro ⟨hKpos, hKint⟩
      refine ⟨K / c₀, ⟨div_pos hKpos hc₀pos, ?_⟩, mul_div_cancel₀ K hc₀0⟩
      have hcancel : c₀ * (K / c₀) = K := mul_div_cancel₀ K hc₀0
      rw [← hInt (K / c₀), hcancel]; exact hKint
    · rintro ⟨K', ⟨hK'pos, hK'int⟩, rfl⟩
      exact ⟨mul_pos hc₀pos hK'pos, by rw [hInt K']; exact hK'int⟩
  have hane : (c₀ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc₀0
  simp only [orliczNorm, hset, iInf_image, ENNReal.coe_mul,
    ENNReal.mul_iInf_of_ne hane ENNReal.coe_ne_top]

/-- The `c = 0` edge of homogeneity, via `orliczNorm_zero`. -/
theorem orliczNorm_const_mul_zero
    -- USER-INPUT: ψ(0) ≤ 0 (book: ψ(0) = 0); HDP Exercise 2.42 (Orlicz function)
    (hψ0 : ψ 0 ≤ 0)
    (X : Ω → ℝ) (μ : Measure Ω) :
    orliczNorm ψ (fun ω => (0 : ℝ) * X ω) μ = 0 := by
  have hae : (fun ω => (0 : ℝ) * X ω) =ᵐ[μ] fun _ => (0 : ℝ) := by
    filter_upwards with ω; rw [zero_mul]
  rw [orliczNorm_congr_ae hae]
  exact orliczNorm_zero hψ0 μ

/-- Sign invariance of the sub-Gaussian norm (ψ₂ instance). -/
theorem subGaussianNorm_neg (X : Ω → ℝ) (μ : Measure Ω) :
    subGaussianNorm (fun ω => -X ω) μ = subGaussianNorm X μ := by
  rw [subGaussianNorm_def, subGaussianNorm_def, orliczNorm_neg]

/-- Abs-homogeneity of the sub-Gaussian norm (B4 instantiation, HDP
Exercise 2.42). -/
theorem subGaussianNorm_const_mul {X : Ω → ℝ} {μ : Measure Ω} {c : ℝ}
    -- LEAN-ONLY: c ≠ 0 as in orliczNorm_const_mul; c = 0 edge via ψ₂(0) = 0
    (hc : c ≠ 0) :
    subGaussianNorm (fun ω => c * X ω) μ = (‖c‖₊ : ℝ≥0∞) * subGaussianNorm X μ := by
  unfold subGaussianNorm
  exact orliczNorm_const_mul hc

/-- Abs-homogeneity of the sub-exponential norm (B4 instantiation;
Corollary 2.9.2 ingredient). -/
theorem subExponentialNorm_const_mul {X : Ω → ℝ} {μ : Measure Ω} {c : ℝ}
    -- LEAN-ONLY: c ≠ 0 as in orliczNorm_const_mul; c = 0 edge via ψ₁(0) = 0
    (hc : c ≠ 0) :
    subExponentialNorm (fun ω => c * X ω) μ
      = (‖c‖₊ : ℝ≥0∞) * subExponentialNorm X μ := by
  unfold subExponentialNorm
  exact orliczNorm_const_mul hc

end StatLean.ConcentrationInequalities
