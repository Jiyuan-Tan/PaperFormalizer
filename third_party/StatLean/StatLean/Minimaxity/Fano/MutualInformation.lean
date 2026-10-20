module
public import StatLean.Minimaxity.Defs
public import StatLean.Minimaxity.ForMathlib.KLDivergence

@[expose] public section

/-!
# Mutual information of the M-ary testing problem and its convexity (KL) bound

Consider the $M$-ary testing problem: an index $J$ is drawn uniformly from $\{1,\dots,M\}$, and one
observes $Z \sim P_{\theta^J}$. The **mutual information** $I(Z; J)$ measures how much the observation
reveals about the index. It is defined as the Kullback–Leibler divergence between the joint law of
$(Z, J)$ and the product of its marginals,
$$ I(Z; J) = D\!\left(\mathbb{Q}_{Z,J} \,\big\|\, \mathbb{Q}_Z \otimes \mathbb{Q}_J\right), $$
which equals the average KL divergence between each component and the uniform mixture,
$$ I(Z; J) = \frac{1}{M} \sum_{j=1}^{M} D\!\left(P_{\theta^j} \,\big\|\, \bar Q\right),
\qquad \bar Q = \frac{1}{M} \sum_{j=1}^{M} P_{\theta^j}. $$
We take this averaged form as the definition (it is the expression used in the lower bounds) and
prove the convexity upper bound
$$ I(Z; J) \le \frac{1}{M^2} \sum_{j=1}^{M} \sum_{k=1}^{M}
   D\!\left(P_{\theta^j} \,\big\|\, P_{\theta^k}\right), $$
which controls the mutual information by the pairwise KL divergences and is the key ingredient for
local-packing minimax lower bounds.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.1 and §15.3.3
(Bounds based on local packings), Eq. (15.29), (15.30) (definition) and Eq. (15.34) (convexity bound).

**Proof formalization notes.** The mutual information is *defined* here directly in its averaged
form (Eq. (15.30)), `I(Z; J) = (1/M) Σⱼ D(P_{θʲ} ‖ Q̄)`, rather than via the joint-vs-product KL
divergence (Eq. (15.29)); the two are equal, and the averaged form is what the bounds consume.
The convexity bound (Eq. (15.34)) is obtained from convexity of the KL divergence in its second
argument: `D(Q j ‖ Q̄) ≤ (1/M) Σₖ D(Q j ‖ Q k)` (lemma `klDiv_le_avg`), summed over `j`. Since
Mathlib does not package the joint convexity of `klDiv`, that lemma is proved from scratch: the
non-absolutely-continuous case gives an infinite right-hand side; the absolutely-continuous case
reduces, via `klDiv_eq_lintegral_klFun_of_ac` against the reference `mixture Q` and the
Radon–Nikodym chain rule `Measure.rnDeriv_mul_rnDeriv`, to the pointwise real inequality
`klFun_le_avg_real`. The latter is the analytic heart — the perspective `(p, q) ↦ q · klFun(p/q)`
is jointly convex — and, after expanding `klFun x = x log x + 1 - x`, follows from concavity of
`log` (`Real.strictConcaveOn_log_Ioi`) via Jensen's inequality.

**Bibliographic comments.** Mutual information originates with C. E. Shannon, "A Mathematical
Theory of Communication," *Bell System Technical Journal* **27** (1948), 379–423 and 623–656, where
it appears (in the entropy form `H(Z) - H(Z|J)`, equivalent to the KL form above) as the channel
information rate. The convexity (KL) bound stated here is textbook synthesis / folklore: it is the
standard "convexity of KL in the second argument" step underlying the local Fano / Hasminskii
(1978) local-packing minimax machinery (the global metric-entropy method of Yang–Barron, 1999,
belongs to Wainwright §15.3.5 and is not what Eq. (15.34) is), and has no single seminal origin
beyond the joint convexity of the KL divergence
itself. We follow Wainwright's presentation (Eq. (15.34)).
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- **Mutual information** of the M-ary testing problem (Wainwright Eq. (15.30)):
`I(Z; J) = (1/M) Σⱼ D(P_{θʲ} ‖ Q̄)`, the average KL divergence between each component `Q j = P_{θʲ}`
and the uniform mixture `Q̄`. Equivalent to the KL divergence between the joint and product laws
(Eq. (15.29)).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.1, Eq. (15.30). -/
noncomputable def mutualInformation {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) : ℝ≥0∞ :=
  (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)

/-- The uniform mixture written as an explicit scaled finite sum:
`Q̄ = Q ∘ₘ Unif[M] = (1/M) Σₖ Q k`. This unfolds the kernel/prior composition `mixture` into the
sum form used by the convexity estimates. -/
lemma mixture_eq_inv_smul_sum {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) :
    mixture Q = (M : ℝ≥0∞)⁻¹ • ∑ k, Q k := by
  rw [mixture, Measure.comp_eq_sum_of_countable, Measure.sum_fintype]
  have hpt : ∀ k : Fin M, (uniformPrior M) {k} = (M : ℝ≥0∞)⁻¹ := by
    intro k
    rw [uniformPrior, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k),
      PMF.uniformOfFintype_apply, Fintype.card_fin]
  simp_rw [hpt]
  rw [← Finset.smul_sum]

open Real in
/-- **Pointwise convexity of `klFun` along the perspective direction.** For `A ≥ 0`, weights
`B k ≥ 0` summing to `M`, and any `D k` with `D k · B k = A` (so `D k = A / B k` where `B k > 0`),
the value `klFun A` is bounded by the `B`-average of `klFun (D k)`:
`klFun A ≤ (1/M) Σₖ B k · klFun (D k)`. This is the real-analytic heart of the second-argument
convexity of `klDiv` (the perspective `(p, q) ↦ q · klFun(p/q)` is jointly convex); the proof
reduces, after expanding `klFun x = x log x + 1 - x`, to concavity of `log`
(`Real.strictConcaveOn_log_Ioi`), which forces `(1/M) Σₖ log (B k) ≤ log 1 = 0`. -/
private lemma klFun_le_avg_real {M : ℕ} (hM : 0 < M) {A : ℝ} (hA : 0 ≤ A)
    {B D : Fin M → ℝ} (hB : ∀ k, 0 ≤ B k) (hBD : ∀ k, D k * B k = A)
    (hsumB : ∑ k, B k = (M : ℝ)) :
    klFun A ≤ (M : ℝ)⁻¹ * ∑ k, B k * klFun (D k) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  rcases hA.lt_or_eq with hApos | hA0
  · -- `0 < A`: every weight is positive and `D k = A / B k`.
    have hBpos : ∀ k, 0 < B k := by
      intro k
      rcases (hB k).lt_or_eq with h | h
      · exact h
      · exfalso; have hk := hBD k; rw [← h, mul_zero] at hk; exact hApos.ne' hk.symm
    have hD : ∀ k, D k = A / B k := fun k => by
      rw [eq_div_iff (hBpos k).ne']; exact hBD k
    have hterm : ∀ k, B k * klFun (D k) = A * log A - A * log (B k) + B k - A := by
      intro k
      rw [hD k, klFun_apply, Real.log_div hApos.ne' (hBpos k).ne']
      field_simp [(hBpos k).ne']
    have key : ∑ k, B k * klFun (D k)
        = (M : ℝ) * (A * log A + 1 - A) - A * ∑ k, log (B k) := by
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hsumB]
      ring
    have hjensen : (M : ℝ)⁻¹ * ∑ k, log (B k) ≤ 0 := by
      have hconc := (strictConcaveOn_log_Ioi).concaveOn
      have hw : ∀ k ∈ (Finset.univ : Finset (Fin M)), (0 : ℝ) ≤ (M : ℝ)⁻¹ :=
        fun k _ => by positivity
      have hw1 : ∑ _k : Fin M, (M : ℝ)⁻¹ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_inv_cancel₀ hMr.ne']
      have hmem : ∀ k ∈ (Finset.univ : Finset (Fin M)), B k ∈ Set.Ioi (0 : ℝ) :=
        fun k _ => hBpos k
      have hjs := hconc.le_map_sum hw hw1 hmem
      simp only [smul_eq_mul, ← Finset.mul_sum, hsumB] at hjs
      rwa [inv_mul_cancel₀ hMr.ne', Real.log_one] at hjs
    have hAjensen : A * ((M : ℝ)⁻¹ * ∑ k, log (B k)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hApos.le hjensen
    rw [klFun_apply]
    have hrhs : (M : ℝ)⁻¹ * ∑ k, B k * klFun (D k)
        = (A * log A + 1 - A) - A * ((M : ℝ)⁻¹ * ∑ k, log (B k)) := by
      rw [key, mul_sub, ← mul_assoc, inv_mul_cancel₀ hMr.ne', one_mul]; ring
    rw [hrhs]; linarith
  · -- `A = 0`: each term equals `B k`, so the average is `1 = klFun 0`.
    have hterm0 : ∀ k, B k * klFun (D k) = B k := by
      intro k
      rcases (hB k).lt_or_eq with h | h
      · have hDk : D k = 0 := by
          have hk := hBD k
          rw [← hA0, mul_eq_zero] at hk
          rcases hk with h1 | h2
          · exact h1
          · exact absurd h2 h.ne'
        rw [hDk, klFun_zero, mul_one]
      · rw [← h, zero_mul]
    have hL : klFun A = 1 := by rw [← hA0]; exact klFun_zero
    have hR : (M : ℝ)⁻¹ * ∑ k, B k * klFun (D k) = 1 := by
      rw [Finset.sum_congr rfl (fun k _ => hterm0 k), hsumB, inv_mul_cancel₀ hMr.ne']
    exact le_of_eq (hL.trans hR.symm)

/-- Radon–Nikodym derivative of a finite sum of (finite) measures splits over the sum, a.e. with
respect to a common dominating measure. Proved by induction from the two-term `rnDeriv_add'`. -/
private lemma rnDeriv_finsetSum_ae {ι : Type*} (s : Finset ι) (P : ι → Measure 𝓧)
    (ξ : Measure 𝓧) [SigmaFinite ξ] [∀ i, IsFiniteMeasure (P i)] :
    (∑ i ∈ s, P i).rnDeriv ξ =ᵐ[ξ] ∑ i ∈ s, (P i).rnDeriv ξ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Measure.rnDeriv_add' (P i) (∑ k ∈ s, P k) ξ, ih] with x h1 h2
      rw [Finset.sum_insert hi, Pi.add_apply, h1, Pi.add_apply, h2]

/-- **Convexity of the KL divergence in its second argument** (Jensen): the divergence from a
fixed component `Q j` to the uniform mixture `Q̄ = (1/M) Σₖ Q k` is at most the average of the
divergences to the components, `D(Q j ‖ Q̄) ≤ (1/M) Σₖ D(Q j ‖ Q k)`. This is the analytic core of
Wainwright Eq. (15.34); it follows from the joint convexity of `(p, q) ↦ q · klFun(p/q)` (the
perspective of the strictly convex `klFun`), which Mathlib does not yet package for `klDiv`.

The non-absolutely-continuous case is discharged here (the right-hand side is `∞`); the remaining
absolutely-continuous case reduces, via `klDiv_eq_lintegral_klFun_of_ac` against the reference
`mixture Q` and the Radon–Nikodym chain rule `Measure.rnDeriv_mul_rnDeriv`, to the pointwise bound
`klFun_le_avg_real` integrated over `mixture Q`. -/
private lemma klDiv_le_avg {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    (j : Fin M) :
    klDiv (Q j) (mixture Q) ≤ (M : ℝ≥0∞)⁻¹ * ∑ k, klDiv (Q j) (Q k) := by
  by_cases hAC : ∀ k, Q j ≪ Q k
  · -- absolutely-continuous case: lift `klFun_le_avg_real` to the lintegral form.
    have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have hMne : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    have hMinv_ne : (M : ℝ≥0∞)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)
    haveI : IsProbabilityMeasure (mixture Q) := by unfold mixture; infer_instance
    -- absolute continuity of each component (and of `Q j`) w.r.t. the mixture
    have hjξ : Q j ≪ mixture Q := by
      rw [mixture_eq_inv_smul_sum]
      exact (Measure.absolutelyContinuous_of_le
        (Finset.single_le_sum (f := fun k => Q k) (fun i _ => Measure.zero_le _)
          (Finset.mem_univ j))).smul_right hMinv_ne
    have hkξ : ∀ k, Q k ≪ mixture Q := fun k => by
      rw [mixture_eq_inv_smul_sum]
      exact (Measure.absolutelyContinuous_of_le
        (Finset.single_le_sum (f := fun k => Q k) (fun i _ => Measure.zero_le _)
          (Finset.mem_univ k))).smul_right hMinv_ne
    -- the components' rnDerivs sum to `M`, a.e. w.r.t. the mixture
    have hsum_ae : (fun x => ∑ k, (Q k).rnDeriv (mixture Q) x)
        =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
      have hS : (M : ℝ≥0∞) • mixture Q = ∑ k, Q k := by
        rw [mixture_eq_inv_smul_sum, smul_smul,
          ENNReal.mul_inv_cancel hMne (ENNReal.natCast_ne_top M), one_smul]
      have h1 := rnDeriv_finsetSum_ae Finset.univ (fun k => Q k) (mixture Q)
      have h2 : (∑ k, Q k).rnDeriv (mixture Q) =ᵐ[mixture Q] (fun _ => (M : ℝ≥0∞)) := by
        rw [← hS]
        filter_upwards [Measure.rnDeriv_smul_left_of_ne_top (mixture Q) (mixture Q)
            (ENNReal.natCast_ne_top M), Measure.rnDeriv_self (mixture Q)] with x hx hx2
        simp [hx, Pi.smul_apply, hx2]
      filter_upwards [h1, h2] with x e1 e2
      rw [← Finset.sum_apply, ← e1, e2]
    -- the Radon–Nikodym chain rule, simultaneously for all components
    have hchain_ae : ∀ᵐ x ∂(mixture Q), ∀ k,
        (Q j).rnDeriv (Q k) x * (Q k).rnDeriv (mixture Q) x
          = (Q j).rnDeriv (mixture Q) x := by
      rw [ae_all_iff]
      intro k
      filter_upwards [Measure.rnDeriv_mul_rnDeriv (hAC k)] with x hx
      rwa [Pi.mul_apply] at hx
    have hktop_ae : ∀ᵐ x ∂(mixture Q), ∀ k, (Q k).rnDeriv (mixture Q) x ≠ ∞ := by
      rw [ae_all_iff]; intro k; exact Measure.rnDeriv_ne_top (Q k) (mixture Q)
    -- rewrite both sides as single lintegrals against the mixture
    rw [klDiv_eq_lintegral_klFun_of_ac hjξ]
    have hRHS : ∀ k, klDiv (Q j) (Q k)
        = ∫⁻ x, (Q k).rnDeriv (mixture Q) x
            * ENNReal.ofReal (klFun ((Q j).rnDeriv (Q k) x).toReal) ∂(mixture Q) := by
      intro k
      rw [klDiv_eq_lintegral_klFun_of_ac (hAC k),
        ← lintegral_rnDeriv_mul (hkξ k) (by fun_prop)]
    rw [Finset.sum_congr rfl (fun k _ => hRHS k),
      ← lintegral_finset_sum _ (fun k _ => by fun_prop),
      ← lintegral_const_mul _ (Finset.measurable_sum _ (fun k _ => by fun_prop))]
    refine lintegral_mono_ae ?_
    filter_upwards [hsum_ae, hchain_ae, hktop_ae,
      Measure.rnDeriv_ne_top (Q j) (mixture Q)] with x hsum hchain hktop hjtop
    -- pointwise: apply the real convexity lemma `klFun_le_avg_real`
    set A := ((Q j).rnDeriv (mixture Q) x).toReal with hA_def
    set B := fun k => ((Q k).rnDeriv (mixture Q) x).toReal with hB_def
    set D := fun k => ((Q j).rnDeriv (Q k) x).toReal with hD_def
    have hBD : ∀ k, D k * B k = A := fun k => by
      simp only [hD_def, hB_def, hA_def, ← ENNReal.toReal_mul, hchain k]
    have hsumB : ∑ k, B k = (M : ℝ) := by
      simp only [hB_def]
      rw [← ENNReal.toReal_sum (fun k _ => hktop k), hsum, ENNReal.toReal_natCast]
    have hbase := klFun_le_avg_real hMpos (A := A) ENNReal.toReal_nonneg
      (B := B) (D := D) (fun _ => ENNReal.toReal_nonneg) hBD hsumB
    have hRnonneg : ∀ k, 0 ≤ B k * klFun (D k) := fun k =>
      mul_nonneg ENNReal.toReal_nonneg (klFun_nonneg ENNReal.toReal_nonneg)
    calc ENNReal.ofReal (klFun A)
        ≤ ENNReal.ofReal ((M : ℝ)⁻¹ * ∑ k, B k * klFun (D k)) :=
          ENNReal.ofReal_le_ofReal hbase
      _ = (M : ℝ≥0∞)⁻¹ * ∑ k, (Q k).rnDeriv (mixture Q) x
            * ENNReal.ofReal (klFun (D k)) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_inv_of_pos (by exact_mod_cast hMpos), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun k _ => hRnonneg k)]
          refine congrArg _ (Finset.sum_congr rfl (fun k _ => ?_))
          simp only [hB_def, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (hktop k)]
  · rw [not_forall] at hAC
    obtain ⟨k₀, hk₀⟩ := hAC
    have htop : klDiv (Q j) (Q k₀) = ⊤ := klDiv_of_not_ac hk₀
    have hle : klDiv (Q j) (Q k₀) ≤ ∑ k, klDiv (Q j) (Q k) :=
      Finset.single_le_sum (f := fun k => klDiv (Q j) (Q k)) (fun i _ => zero_le)
        (Finset.mem_univ k₀)
    have hsum : ∑ k, klDiv (Q j) (Q k) = ⊤ := top_le_iff.mp (htop ▸ hle)
    rw [hsum, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M))]
    exact le_top

/-- **Convexity bound on the mutual information** (Wainwright Eq. (15.34)):
`I(Z; J) ≤ (1/M²) Σⱼ Σₖ D(P_{θʲ} ‖ P_{θᵏ})`. Obtained from the convexity of the KL divergence in its
second argument (the mixture minimizes the average divergence).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.3
(Bounds based on local packings), Eq. (15.34). -/
theorem mutualInformation_le_avg_pairwise_kl {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧)
    [IsMarkovKernel Q] :
    mutualInformation Q ≤ ((M : ℝ≥0∞) ^ 2)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k) := by
  unfold mutualInformation
  calc (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)
      ≤ (M : ℝ≥0∞)⁻¹ * ∑ j, ((M : ℝ≥0∞)⁻¹ * ∑ k, klDiv (Q j) (Q k)) := by
        gcongr with j
        exact klDiv_le_avg Q j
    _ = (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k)) := by
        rw [← Finset.mul_sum]
    _ = ((M : ℝ≥0∞) ^ 2)⁻¹ * ∑ j, ∑ k, klDiv (Q j) (Q k) := by
        rw [← mul_assoc, sq,
          ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top M))
            (Or.inl (ENNReal.natCast_ne_top M))]

end StatLean.Minimaxity
