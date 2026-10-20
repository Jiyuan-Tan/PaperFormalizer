module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

/-!
# Moments and limits of coordinate averages under product measures

The first- and second-moment identities and the strong-law limit for the average
`x ↦ (1/n)·Σᵢ g(xᵢ)` of a function of the coordinates under the canonical i.i.d.
laws `Measure.pi (fun _ : Fin n => P)` and `Measure.infinitePi (fun _ : ℕ => P)`:

* `integral_avg_eval_pi` — `E[X̄] = μ`;
* `variance_avg_eval_pi` — `Var(X̄) = σ²/n`;
* `integral_sq_dev_avg_eval_pi` — the mean-squared error of the average is `σ²/n`;
* `tendsto_avg_eval_infinitePi` — `X̄ₙ → μ` almost surely (SLLN transport).

These four facts are used throughout StatLean (bootstrap root laws, Lindeberg
CLT bricks, empirical-process parameter estimation) but were previously inlined
at each use site from `ProbabilityTheory.IndepFun.variance_sum`; this file
packages them once, at the bottom layer, for reuse.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §2.2 (Monte Carlo estimation, eqs. (2.8)–(2.9), and
the law-of-large-numbers discussion on p. 53).  (`ECS §X.Y`.)

**Proof formalization notes.**

* The sample space is the canonical product; the coordinate maps are
  measure-preserving (`MeasureTheory.measurePreserving_eval`) and independent
  (`ProbabilityTheory.iIndepFun_pi`) — both loaded from the pinned Mathlib, not
  reproved.
* `[NeZero n]` rules out the `n = 0` junk value `(0 : ℝ)⁻¹ = 0` of the average.
* The strong-law statement is in `Finset.range`-sum form on the sequence space
  `ℕ → 𝓧`; the `Fin`-indexed Monte Carlo wrapper lives in
  `MonteCarlo/Estimation.lean`.

**Bibliographic comments.** The variance identity for sample means is classical
(Laplace); the almost-sure law of large numbers is Kolmogorov's (1933), here
obtained from Mathlib's Etemadi-style `ProbabilityTheory.strong_law_ae_real`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace StatLean.ComputationalStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {P : Measure 𝓧} [IsProbabilityMeasure P]
  {n : ℕ} {g : 𝓧 → ℝ}

/-- The coordinate reads of the product law are measure preserving. -/
private lemma mp_eval (i : Fin n) :
    MeasurePreserving (fun x : Fin n → 𝓧 => x i) (Measure.pi fun _ : Fin n => P) P :=
  measurePreserving_eval (fun _ : Fin n => P) i

/-- Each summand of the coordinate average is integrable. -/
private lemma integrable_eval_pi (i : Fin n) (hg : Integrable g P) :
    Integrable (fun x : Fin n → 𝓧 => g (x i)) (Measure.pi fun _ : Fin n => P) :=
  (mp_eval i).integrable_comp_of_integrable hg

/-- Each summand of the coordinate average has the same integral as `g`. -/
private lemma integral_eval_pi (i : Fin n) (hg : Integrable g P) :
    ∫ x, g (x i) ∂(Measure.pi fun _ : Fin n => P) = ∫ z, g z ∂P := by
  have hmp := mp_eval (P := P) i
  have h1 : AEStronglyMeasurable g
      ((Measure.pi fun _ : Fin n => P).map fun x : Fin n → 𝓧 => x i) := by
    rw [hmp.map_eq]; exact hg.aestronglyMeasurable
  refine .symm ?_
  conv_lhs => rw [← hmp.map_eq]
  exact integral_map hmp.measurable.aemeasurable h1

/-- **Unbiasedness of the coordinate average** (ECS §2.2, eq. (2.8)): under the
i.i.d. product law, the average of `g` over the coordinates integrates to
`∫ g dP`. -/
theorem integral_avg_eval_pi [NeZero n]
    -- USER-INPUT: the integrand has a finite first moment; ECS §2.2
    (hg : Integrable g P) :
    ∫ x, (n : ℝ)⁻¹ * ∑ i, g (x i) ∂(Measure.pi fun _ : Fin n => P)
      = ∫ z, g z ∂P := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [integral_const_mul,
    integral_finset_sum _ fun i _ => integrable_eval_pi i hg]
  simp only [integral_eval_pi _ hg, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Variance of the coordinate average** (ECS §2.2, eq. (2.9) discussion):
`Var(X̄) = Var_P(g)/n` under the i.i.d. product law. -/
theorem variance_avg_eval_pi [NeZero n]
    -- USER-INPUT: the integrand has a finite second moment; ECS §2.2
    (hg : MemLp g 2 P) :
    variance (fun x : Fin n → 𝓧 => (n : ℝ)⁻¹ * ∑ i, g (x i))
        (Measure.pi fun _ : Fin n => P)
      = variance g P / n := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hsum := variance_sum_pi (μ := fun _ : Fin n => P) (X := fun _ : Fin n => g)
    fun _ => hg
  have hfun : (∑ _i : Fin n, fun x : Fin n → 𝓧 => g (x _i))
      = fun x : Fin n → 𝓧 => ∑ i, g (x i) := by
    funext x; simp
  rw [hfun] at hsum
  rw [variance_const_mul, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Mean-squared error of the coordinate average** (ECS §2.2): since the
average is unbiased, its mean-squared deviation from `∫ g dP` is `Var_P(g)/n`. -/
theorem integral_sq_dev_avg_eval_pi [NeZero n]
    -- USER-INPUT: the integrand has a finite second moment; ECS §2.2
    (hg : MemLp g 2 P) :
    ∫ x, ((n : ℝ)⁻¹ * ∑ i, g (x i) - ∫ z, g z ∂P) ^ 2
        ∂(Measure.pi fun _ : Fin n => P)
      = variance g P / n := by
  have hgi : Integrable g P := hg.integrable (by norm_num)
  have hmem : MemLp (fun x : Fin n → 𝓧 => ∑ i, g (x i)) 2
      (Measure.pi fun _ : Fin n => P) :=
    memLp_finset_sum Finset.univ fun i _ => hg.comp_measurePreserving (mp_eval i)
  have hae : AEMeasurable (fun x : Fin n → 𝓧 => (n : ℝ)⁻¹ * ∑ i, g (x i))
      (Measure.pi fun _ : Fin n => P) :=
    hmem.aestronglyMeasurable.aemeasurable.const_mul _
  rw [← variance_avg_eval_pi hg, variance_eq_integral hae,
    integral_avg_eval_pi hgi]

/-- **Strong law for coordinate averages** (ECS §2.2, p. 53): on the canonical
sequence space, the running averages of `g` over the coordinates converge to
`∫ g dP` almost surely. -/
theorem tendsto_avg_eval_infinitePi {g : 𝓧 → ℝ}
    -- USER-INPUT: the integrand has a finite first moment; ECS §2.2
    (hg : Integrable g P)
    -- LEAN-ONLY: measurability of the integrand (regularity)
    (hgm : Measurable g) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => P),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, g (ω i))
        atTop (𝓝 (∫ z, g z ∂P)) := by
  have hmp : ∀ i : ℕ, MeasurePreserving (fun ω : ℕ → 𝓧 => ω i)
      (Measure.infinitePi fun _ : ℕ => P) P :=
    fun i => measurePreserving_eval_infinitePi (fun _ : ℕ => P) i
  set X : ℕ → (ℕ → 𝓧) → ℝ := fun i ω => g (ω i) with hXdef
  have hint : Integrable (X 0) (Measure.infinitePi fun _ : ℕ => P) :=
    (hmp 0).integrable_comp_of_integrable hg
  have hiIndep : iIndepFun X (Measure.infinitePi fun _ : ℕ => P) :=
    iIndepFun_infinitePi (X := fun _ : ℕ => g) fun _ => hgm
  have hlaw : ∀ i : ℕ, (Measure.infinitePi fun _ : ℕ => P).map (X i) = P.map g := by
    intro i
    have hcomp : X i = g ∘ fun ω : ℕ → 𝓧 => ω i := rfl
    rw [hcomp, ← Measure.map_map hgm (hmp i).measurable, (hmp i).map_eq]
  have hident : ∀ i, IdentDistrib (X i) (X 0)
      (Measure.infinitePi fun _ : ℕ => P) (Measure.infinitePi fun _ : ℕ => P) := fun i =>
    { aemeasurable_fst := (hgm.comp (measurable_pi_apply i)).aemeasurable
      aemeasurable_snd := (hgm.comp (measurable_pi_apply 0)).aemeasurable
      map_eq := by rw [hlaw i, hlaw 0] }
  have hmean : ∫ ω, X 0 ω ∂(Measure.infinitePi fun _ : ℕ => P) = ∫ z, g z ∂P := by
    have h1 : AEStronglyMeasurable g
        ((Measure.infinitePi fun _ : ℕ => P).map fun ω : ℕ → 𝓧 => ω 0) := by
      rw [(hmp 0).map_eq]; exact hg.aestronglyMeasurable
    refine .symm ?_
    conv_lhs => rw [← (hmp 0).map_eq]
    exact integral_map (hmp 0).measurable.aemeasurable h1
  have hsl := strong_law_ae_real X hint (fun _ _ hij => hiIndep.indepFun hij) hident
  rw [hmean] at hsl
  filter_upwards [hsl] with ω hω
  simpa [hXdef, div_eq_inv_mul] using hω

end StatLean.ComputationalStatistics
