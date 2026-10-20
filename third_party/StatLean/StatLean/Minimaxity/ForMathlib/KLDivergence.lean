module
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
# Kullback–Leibler divergence — book form, tensorization, and mixture minimization

For probability measures $\mathbb{Q} \ll \mathbb{P}$ with densities $q, p$ relative to a common
dominating measure $\nu$, the **Kullback–Leibler divergence** is
$$D(\mathbb{Q} \,\|\, \mathbb{P}) \;=\; \int q \,\log\!\frac{q}{p}\, d\nu \;\ge\; 0,$$
with the convention $D(\mathbb{Q}\,\|\,\mathbb{P}) = +\infty$ when $\mathbb{Q} \not\ll \mathbb{P}$
(Wainwright Eq. (15.7); nonnegativity is Gibbs' inequality). This file aligns Wainwright's KL
divergence with Mathlib's `InformationTheory.klDiv` and proves three book identities:

* **Additivity over products** (Eq. (15.11a), two-factor case): for product measures,
  $$D(\mathbb{P}_1 \otimes \mathbb{P}_2 \,\|\, \mathbb{Q}_1 \otimes \mathbb{Q}_2)
    \;=\; D(\mathbb{P}_1 \,\|\, \mathbb{Q}_1) + D(\mathbb{P}_2 \,\|\, \mathbb{Q}_2).$$
* **I.i.d. tensorization** (Eq. (15.11b)): for the $n$-fold product measures,
  $$D\bigl(\mathbb{P}^{\otimes n} \,\|\, \mathbb{Q}^{\otimes n}\bigr) \;=\; n \, D(\mathbb{P} \,\|\, \mathbb{Q}).$$
* **The mixture minimizes the average KL divergence** (Exercise 15.11): for any distribution
  $\mathbb{Q}$, the uniform mixture $\bar{\mathbb{Q}} = \frac{1}{M}\sum_{j} \mathbb{P}_j$ satisfies
  $$\sum_{j} D(\mathbb{P}_j \,\|\, \bar{\mathbb{Q}}) \;\le\; \sum_{j} D(\mathbb{P}_j \,\|\, \mathbb{Q}),$$
  which is the variational property underlying the Yang–Barron mutual-information bound (Eq. (15.52)).

*Alignment with the Lean statement.* Wainwright's $D(\mathbb{Q}\,\|\,\mathbb{P})$ coincides with
Mathlib's `klDiv ℚ ℙ` on probability measures: the integrated argument — $q$, the density of
$\mathbb{Q}$ — is the *first* argument in both conventions, so no argument-swap is needed. KL
divergence is `ℝ≥0∞`-valued in Mathlib, so nonnegativity is automatic and the
$\mathbb{Q}\not\ll\mathbb{P}$ branch returns `⊤`. All three results carry probability-measure
instance hypotheses on every factor; the mixture result is stated for an $M$-indexed family
$\mathbb{P} : \mathrm{Fin}\,M \to \text{Measure}$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.7),
(15.11a), (15.11b); §15.6, Exercise 15.11.

**Proof formalization notes.** We reuse Mathlib's `klDiv` directly and add only the
Wainwright-facing algebra.

* `klDiv_prod_eq_add` follows from the Mathlib chain rule `klDiv_compProd_eq_add` applied to each
  product written as a composition–product with a constant kernel, using the auxiliary
  `klDiv_prod_const_fst` (a common first factor collapses to the second-factor divergence, proved
  by swapping coordinates via `Measure.prod_swap` and applying `klDiv_compProd_left`).
* `klDiv_pi_eq_nsmul` is an induction on $n$: the base case uses `Measure.pi_of_empty` and
  `klDiv_self`; the step peels off coordinate $0$ via `measurePreserving_piFinSuccAbove` and
  `MeasurableEquiv.piFinSuccAbove`, reducing to `klDiv_prod_eq_add`. Both proofs rely on the
  pushforward-invariance lemma `klDiv_map_measurableEquiv` (reparametrization invariance of the
  $f$-divergence, from the log-likelihood-ratio integral form and `MeasurableEmbedding.rnDeriv_map`).
* `sum_klDiv_mixture_le` is the crux of Exercise 15.11 (the variational/convexity property of
  `klDiv` in its second argument, which Mathlib does not expose directly). The proof splits on
  absolute continuity: if some $\mathbb{P}_{j_0} \not\ll \mathbb{Q}$ the right side is $\infty$;
  otherwise it lifts a pointwise *compensation inequality* (`klFun_compensation_le`, deficit exactly
  $M \cdot \mathrm{klFun}(W) \ge 0$, encoding the Gibbs identity
  $\sum_j D(\mathbb{P}_j\,\|\,\mathbb{Q}) = \sum_j D(\mathbb{P}_j\,\|\,\bar{\mathbb{Q}}) + M\,D(\bar{\mathbb{Q}}\,\|\,\mathbb{Q})$)
  to lintegrals against the common reference $\mathbb{Q}$, using the Radon–Nikodym chain rule and
  the splitting `rnDeriv_finsetSum_ae` of the mixture density.

**Bibliographic comments.** The KL divergence itself originates with S. Kullback and R. A. Leibler,
"On Information and Sufficiency," *The Annals of Mathematical Statistics* **22** (1951), no. 1,
79–86 (DOI 10.1214/aoms/1177729694), where Eq. (2.5) defines the mean information for
discrimination. The additivity/tensorization identities and the mixture-minimization
(compensation) property are textbook folklore with no single seminal origin — they follow from the
chain rule for relative entropy and Gibbs' inequality, and are stated here in the form given by
Wainwright (2019). The use of the mixture as the average-KL minimizer to control redundancy traces
to Y. Yang and A. Barron, "Information-theoretic determination of minimax rates of convergence,"
*The Annals of Statistics* **27** (1999), no. 5, 1564–1599, which is the source of the
mutual-information minimax bound (Wainwright Eq. (15.52)).
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- KL divergence is invariant under pushforward by a measurable equivalence. This is the
standard reparametrization-invariance of an `f`-divergence; we prove it from the
log-likelihood-ratio integral form together with `MeasurableEmbedding.rnDeriv_map`. -/
private lemma klDiv_map_measurableEquiv (e : α ≃ᵐ γ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  have hf := e.measurableEmbedding
  haveI : IsFiniteMeasure (μ.map e) := μ.isFiniteMeasure_map e
  haveI : IsFiniteMeasure (ν.map e) := ν.isFiniteMeasure_map e
  by_cases hμν : μ ≪ ν
  · have hμν' : μ.map e ≪ ν.map e := hf.absolutelyContinuous_map hμν
    rw [klDiv_eq_lintegral_klFun_of_ac hμν', klDiv_eq_lintegral_klFun_of_ac hμν,
      hf.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · have hne : ¬ (μ.map e ≪ ν.map e) := by
      intro hac
      apply hμν
      have h := hac.map e.symm.measurable
      rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at h
    rw [klDiv_of_not_ac hμν, klDiv_of_not_ac hne]

/-- The residual term in the product chain rule: for product measures with a common first
factor `μ₁` (a probability measure), the KL divergence collapses to the second-factor
divergence. Proved by swapping coordinates (`Measure.prod_swap`) so the common factor becomes
the conditional kernel, then applying `klDiv_compProd_left`. -/
private lemma klDiv_prod_const_fst (μ₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) = klDiv μ₂ ν₂ := by
  rw [← klDiv_map_measurableEquiv (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)
    (μ₁.prod μ₂) (μ₁.prod ν₂),
    show ⇑(MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) = Prod.swap from rfl,
    Measure.prod_swap, Measure.prod_swap, ← Measure.compProd_const, ← Measure.compProd_const,
    klDiv_compProd_left]

/-- **Additivity of KL over products** (Wainwright Eq. (15.11a), two-factor case):
`D(ℙ₁⊗ℙ₂ ‖ ℚ₁⊗ℚ₂) = D(ℙ₁ ‖ ℚ₁) + D(ℙ₂ ‖ ℚ₂)`. Follows from the Mathlib chain rule
`klDiv_compProd_eq_add` applied to the product written as a composition–product with a
constant kernel.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.11a). -/
theorem klDiv_prod_eq_add
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  rw [← Measure.compProd_const (μ := μ₁) (ν := μ₂),
    ← Measure.compProd_const (μ := ν₁) (ν := ν₂), klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const, klDiv_prod_const_fst]

/-- **I.i.d. tensorization of KL** (Wainwright Eq. (15.11b)):
`D(ℙ^{1:n} ‖ ℚ^{1:n}) = n · D(ℙ ‖ ℚ)` for the `n`-fold product measures.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.11b). -/
theorem klDiv_pi_eq_nsmul (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      = n • klDiv μ ν := by
  induction n with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty, klDiv_self, zero_nsmul]
  | succ n ih =>
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
    rw [← klDiv_map_measurableEquiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0)
      (Measure.pi fun _ : Fin (n + 1) => μ) (Measure.pi fun _ : Fin (n + 1) => ν),
      hμ, hν, klDiv_prod_eq_add, ih, succ_nsmul, add_comm]

open Real in
/-- **Compensation identity, pointwise form.** For weight `W ≥ 0`, components `R k ≥ 0`, masses
`Q k = R k · W` summing to `M · W`, the perspective inequality
`∑ₖ W · klFun (R k) ≤ ∑ₖ klFun (Q k)` holds, with deficit exactly `M · klFun W ≥ 0`. This is the
per-point heart of the Gibbs/compensation identity `∑ⱼ D(Pⱼ‖Q) = ∑ⱼ D(Pⱼ‖Q̄) + M·D(Q̄‖Q)`. -/
private lemma klFun_compensation_le {M : ℕ} (_hM : 0 < M) {W : ℝ} (hW : 0 ≤ W)
    {Q R : Fin M → ℝ} (_hQ : ∀ k, 0 ≤ Q k) (hR : ∀ k, 0 ≤ R k)
    (hQR : ∀ k, Q k = R k * W) (hsum : ∑ k, Q k = (M : ℝ) * W) :
    ∑ k, W * klFun (R k) ≤ ∑ k, klFun (Q k) := by
  have hterm : ∀ k, klFun (Q k) - W * klFun (R k) = Q k * Real.log W + 1 - W := by
    intro k
    rw [klFun_apply, klFun_apply]
    rcases eq_or_lt_of_le (hR k) with h0 | hRpos
    · have hQk : Q k = 0 := by rw [hQR k, ← h0, zero_mul]
      rw [hQk, ← h0]; simp
    · rcases eq_or_lt_of_le hW with hw0 | hWpos
      · have hQk : Q k = 0 := by rw [hQR k, ← hw0, mul_zero]
        rw [hQk, ← hw0]; simp
      · have hlog : Real.log (Q k) = Real.log (R k) + Real.log W := by
          rw [hQR k, Real.log_mul hRpos.ne' hWpos.ne']
        linear_combination (Real.log (R k) - 1) * (hQR k) + Q k * hlog
  have key : ∑ k, (klFun (Q k) - W * klFun (R k)) = (M : ℝ) * klFun W := by
    rw [Finset.sum_congr rfl (fun k _ => hterm k), klFun_apply,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hsum,
      Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  have hnn : 0 ≤ (M : ℝ) * klFun W :=
    mul_nonneg (Nat.cast_nonneg M) (klFun_nonneg hW)
  rw [Finset.sum_sub_distrib] at key
  linarith

/-- Radon–Nikodym derivative of a finite sum of (finite) measures splits over the sum, a.e. with
respect to a common dominating measure. Proved by induction from the two-term `rnDeriv_add'`. -/
private lemma rnDeriv_finsetSum_ae {ι : Type*} (s : Finset ι) (P : ι → Measure α)
    (ξ : Measure α) [SigmaFinite ξ] [∀ i, IsFiniteMeasure (P i)] :
    (∑ i ∈ s, P i).rnDeriv ξ =ᵐ[ξ] ∑ i ∈ s, (P i).rnDeriv ξ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      filter_upwards [Measure.rnDeriv_add' (P i) (∑ k ∈ s, P k) ξ, ih] with x h1 h2
      rw [Finset.sum_insert hi, Pi.add_apply, h1, Pi.add_apply, h2]

-- Crux of Exercise 15.11: the uniform mixture minimizes the average KL divergence. This is
-- the variational/convexity property of `klDiv` in its second argument, which Mathlib does not
-- yet expose in a directly usable form. The non-absolutely-continuous case (some `P j` not `≪ Q`)
-- is discharged here; the remaining case is the Gibbs identity below.
private lemma klDiv_mixture_minimizes {M : ℕ} (P : Fin M → Measure α) (Q : Measure α)
    [∀ j, IsProbabilityMeasure (P j)] [IsProbabilityMeasure Q] :
    ∑ j, klDiv (P j) ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) ≤ ∑ j, klDiv (P j) Q := by
  rcases eq_or_ne M 0 with rfl | hM0
  · simp
  haveI : NeZero M := ⟨hM0⟩
  by_cases hAC : ∀ j, P j ≪ Q
  · -- absolutely-continuous case: lift the pointwise compensation inequality to lintegrals,
    -- integrating both averages against the common reference `Q`.
    have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
    have hMne : (M : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne M)
    have hMinv_ne : (M : ℝ≥0∞)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top M)
    haveI hfin : IsFiniteMeasure ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) := by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hMne).lt_top (measure_lt_top _ _)
    -- `Q̄ ≪ Q`, and each `P j ≪ Q̄`
    have hSQ : (∑ k, P k) ≪ Q := by
      refine Finset.sum_induction _ (· ≪ Q) (fun _ _ => Measure.AbsolutelyContinuous.add_left)
        (Measure.AbsolutelyContinuous.zero Q) (fun k _ => hAC k)
    have hQbarQ : ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) ≪ Q :=
      (Measure.smul_absolutelyContinuous).trans hSQ
    have hPjQbar : ∀ j, P j ≪ (M : ℝ≥0∞)⁻¹ • ∑ k, P k := fun j =>
      (Measure.absolutelyContinuous_of_le
        (Finset.single_le_sum (f := fun k => P k) (fun i _ => Measure.zero_le _)
          (Finset.mem_univ j))).smul_right hMinv_ne
    -- the components' rnDerivs sum to `M · (dQ̄/dQ)`, a.e. w.r.t. `Q`
    have hsum_ae : (fun x => ∑ k, (P k).rnDeriv Q x)
        =ᵐ[Q] (fun x => (M : ℝ≥0∞) * ((M : ℝ≥0∞)⁻¹ • ∑ k, P k).rnDeriv Q x) := by
      have hS : (M : ℝ≥0∞) • ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) = ∑ k, P k := by
        rw [smul_smul, ENNReal.mul_inv_cancel hMne (ENNReal.natCast_ne_top M), one_smul]
      have h1 := rnDeriv_finsetSum_ae Finset.univ (fun k => P k) Q
      have h2 : (∑ k, P k).rnDeriv Q
          =ᵐ[Q] (fun x => (M : ℝ≥0∞) * ((M : ℝ≥0∞)⁻¹ • ∑ k, P k).rnDeriv Q x) := by
        nth_rewrite 1 [← hS]
        filter_upwards [Measure.rnDeriv_smul_left_of_ne_top
          ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) Q (ENNReal.natCast_ne_top M)] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
      filter_upwards [h1, h2] with x e1 e2
      rw [← Finset.sum_apply, ← e1, e2]
    -- the Radon–Nikodym chain rule, simultaneously for all components
    have hchain_ae : ∀ᵐ x ∂Q, ∀ j,
        (P j).rnDeriv ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) x * ((M : ℝ≥0∞)⁻¹ • ∑ k, P k).rnDeriv Q x
          = (P j).rnDeriv Q x := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Measure.rnDeriv_mul_rnDeriv (hPjQbar j)] with x hx
      rwa [Pi.mul_apply] at hx
    have hPktop : ∀ᵐ x ∂Q, ∀ k, (P k).rnDeriv Q x ≠ ∞ := by
      rw [ae_all_iff]; intro k; exact Measure.rnDeriv_ne_top (P k) Q
    -- rewrite both averages as single lintegrals against `Q`
    have hLHS : ∀ j, klDiv (P j) ((M : ℝ≥0∞)⁻¹ • ∑ k, P k)
        = ∫⁻ x, ((M : ℝ≥0∞)⁻¹ • ∑ k, P k).rnDeriv Q x
            * ENNReal.ofReal (klFun ((P j).rnDeriv ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) x).toReal) ∂Q := by
      intro j
      rw [klDiv_eq_lintegral_klFun_of_ac (hPjQbar j),
        ← lintegral_rnDeriv_mul hQbarQ (by fun_prop)]
    have hRHS : ∀ j, klDiv (P j) Q
        = ∫⁻ x, ENNReal.ofReal (klFun ((P j).rnDeriv Q x).toReal) ∂Q :=
      fun j => klDiv_eq_lintegral_klFun_of_ac (hAC j)
    rw [Finset.sum_congr rfl (fun j _ => hLHS j),
      Finset.sum_congr rfl (fun j _ => hRHS j),
      ← lintegral_finset_sum _ (fun j _ => by fun_prop),
      ← lintegral_finset_sum _ (fun j _ => by fun_prop)]
    refine lintegral_mono_ae ?_
    filter_upwards [hsum_ae, hchain_ae, hPktop,
      Measure.rnDeriv_ne_top ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) Q] with x hsum hchain hktop hWtop
    -- pointwise: apply the real compensation lemma
    set W := (((M : ℝ≥0∞)⁻¹ • ∑ k, P k).rnDeriv Q x).toReal with hW_def
    set Qr := fun k => ((P k).rnDeriv Q x).toReal with hQr_def
    set Rr := fun k => ((P k).rnDeriv ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) x).toReal with hRr_def
    have hQR : ∀ k, Qr k = Rr k * W := fun k => by
      simp only [hQr_def, hRr_def, hW_def, ← ENNReal.toReal_mul, hchain k]
    have hsumB : ∑ k, Qr k = (M : ℝ) * W := by
      simp only [hQr_def, hW_def]
      rw [← ENNReal.toReal_sum (fun k _ => hktop k), hsum, ENNReal.toReal_mul,
        ENNReal.toReal_natCast]
    have hbase := klFun_compensation_le hMpos (W := W) ENNReal.toReal_nonneg
      (Q := Qr) (R := Rr) (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
      hQR hsumB
    have hRnonneg : ∀ k, 0 ≤ W * klFun (Rr k) := fun k =>
      mul_nonneg ENNReal.toReal_nonneg (klFun_nonneg ENNReal.toReal_nonneg)
    calc ∑ k, ((M : ℝ≥0∞)⁻¹ • ∑ k, P k).rnDeriv Q x
            * ENNReal.ofReal (klFun (Rr k))
        = ENNReal.ofReal (∑ k, W * klFun (Rr k)) := by
          rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hRnonneg k)]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          simp only [hW_def, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal hWtop]
      _ ≤ ENNReal.ofReal (∑ k, klFun (Qr k)) := ENNReal.ofReal_le_ofReal hbase
      _ = ∑ k, ENNReal.ofReal (klFun (Qr k)) :=
          ENNReal.ofReal_sum_of_nonneg
            (fun k _ => klFun_nonneg ENNReal.toReal_nonneg)
  · rw [not_forall] at hAC
    obtain ⟨j₀, hj₀⟩ := hAC
    have htop : klDiv (P j₀) Q = ⊤ := klDiv_of_not_ac hj₀
    have hle : klDiv (P j₀) Q ≤ ∑ j, klDiv (P j) Q :=
      Finset.single_le_sum (f := fun j => klDiv (P j) Q) (fun i _ => zero_le)
        (Finset.mem_univ j₀)
    have hsum : ∑ j, klDiv (P j) Q = ⊤ := top_le_iff.mp (htop ▸ hle)
    rw [hsum]
    exact le_top

/-- **The mixture minimizes the average KL divergence** (Wainwright Exercise 15.11):
for any distribution `Q`, the uniform mixture `Q̄ = (1/M) Σⱼ ℙⱼ` satisfies
`Σⱼ D(ℙⱼ ‖ Q̄) ≤ Σⱼ D(ℙⱼ ‖ Q)`. Used to obtain the Yang–Barron mutual-information bound.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.11. -/
theorem sum_klDiv_mixture_le {M : ℕ} (P : Fin M → Measure α) (Q : Measure α)
    [∀ j, IsProbabilityMeasure (P j)] [IsProbabilityMeasure Q] :
    ∑ j, klDiv (P j) ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) ≤ ∑ j, klDiv (P j) Q :=
  klDiv_mixture_minimizes P Q

end StatLean.Minimaxity
