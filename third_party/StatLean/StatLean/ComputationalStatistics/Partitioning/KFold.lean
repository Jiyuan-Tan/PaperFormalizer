module
public import StatLean.ComputationalStatistics.Partitioning.Holdout
public import StatLean.ComputationalStatistics.Resampling.Jackknife
public import StatLean.ComputationalStatistics.ForMathlib.PiMarginal

@[expose] public section

/-!
# K-fold and leave-one-out cross validation

The fold estimators of ECS §3.2 and the correct basic theorem about them:
cross validation is unbiased **for the expected risk of the rule trained on
one fold less** — not for the risk of the full-sample rule (that statement is
generally false, and is deliberately not made).

* `kFoldEstimate` — data as `K + 1` folds of size `m`; each fold is held out
  once against the rule trained on the remaining `K` folds (deletion is the
  jackknife's `Fin.succAbove`);
* `kFold_unbiased` — `E[CV] = E_{S ~ D^{K·m}}[R(A(S))]`;
* `looEstimate`, `loo_unbiased` — leave-one-out (`m = 1` in spirit; stated
  directly over `Fin (n+1)` observations); Allen's PRESS (ECS eq. (3.4)) is
  `looEstimate` with squared-error loss.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §3.2 (K-fold cross validation, pp. 72–73; PRESS,
eq. (3.4)).  (`ECS §3.2`.)

**Proof formalization notes.**

* Fold structure is a *matrix* `z : Fin (K+1) → Fin m → Z` (folds ×
  observations), so fold deletion is `jackknifeDelete` at the outer index and
  no `n/K` divisibility bookkeeping ever appears; the flat-sample version is
  recoverable through the `Fin (K+1) × Fin m ≃ Fin ((K+1)·m)` reindexing and
  is deferred.
* The probabilistic step is `pi_map_deleteSplit` (the held-out fold is
  independent of the training folds); each of the `K + 1` summands then has
  the same expectation, by exchangeability of the folds.
* The training set of each fold has size `K·m`, so the theorem compares CV to
  the risk of the *reduced-size* rule — the honest statement (Stone 1974).

**Bibliographic comments.** M. Stone, "Cross-validatory choice and assessment
of statistical predictions," *J. Roy. Statist. Soc. B* **36** (1974), 111–147;
D. M. Allen, "The relationship between variable selection and data
augmentation and a method for prediction," *Technometrics* **16** (1974),
125–127 (PRESS); Geisser (1975) for the K-fold form.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {ℓ : H → Z → ℝ}

/-- **The K-fold cross-validation estimate** (ECS §3.2): data organized as
`K + 1` folds of `m` observations; fold `k` is held out and scored against the
rule trained on the other `K` folds, and the fold scores are averaged. -/
noncomputable def kFoldEstimate {K m : ℕ} (ℓ : H → Z → ℝ)
    (A : (Fin K → Fin m → Z) → H) (z : Fin (K + 1) → Fin m → Z) : ℝ :=
  ((K : ℝ) + 1)⁻¹ * ∑ k, mcEstimate (ℓ (A (jackknifeDelete k z))) (z k)

/-- **The leave-one-out cross-validation estimate** (ECS §3.2): every single
observation is held out once against the rule trained on the rest.  With
squared-error loss this is Allen's PRESS/(n+1) (ECS eq. (3.4)). -/
noncomputable def looEstimate {n : ℕ} (ℓ : H → Z → ℝ)
    (A : (Fin n → Z) → H) (x : Fin (n + 1) → Z) : ℝ :=
  ((n : ℝ) + 1)⁻¹ * ∑ i, ℓ (A (jackknifeDelete i x)) (x i)

/-- The common measure-theoretic core of `loo_unbiased` and `kFold_unbiased`: for a
score `F` of a (training block, held-out block) pair, the delete-one average of
`F` over a `Q^{N+1}` sample has the product-measure expectation.  Deleting the
`i`-th block carries `Q^{N+1}` to `Q^N ⊗ Q` (`pi_map_deleteSplit` composed with
`Prod.swap`), so every one of the `N + 1` summands has the same integral. -/
private theorem integral_avg_delete_pair {W : Type*} [MeasurableSpace W]
    {Q : Measure W} [IsProbabilityMeasure Q] {N : ℕ} (F : (Fin N → W) × W → ℝ)
    (hF : Integrable F ((Measure.pi fun _ : Fin N => Q).prod Q)) :
    ∫ x, ((N : ℝ) + 1)⁻¹ * ∑ i, F (jackknifeDelete i x, x i)
        ∂(Measure.pi fun _ : Fin (N + 1) => Q)
      = ∫ s, ∫ w, F (s, w) ∂Q ∂(Measure.pi fun _ : Fin N => Q) := by
  have hn : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hm₀ : ∀ i : Fin (N + 1),
      Measurable (fun x : Fin (N + 1) → W => (x i, x ∘ i.succAbove)) := fun i =>
    (measurable_pi_apply i).prodMk (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
  have hm : ∀ i : Fin (N + 1),
      Measurable (fun x : Fin (N + 1) → W => (jackknifeDelete i x, x i)) := fun i =>
    (measurable_pi_lambda _ fun _ => measurable_pi_apply _).prodMk (measurable_pi_apply i)
  -- the deleted block and the held-out block are independent, in that order
  have hmap : ∀ i : Fin (N + 1),
      (Measure.pi fun _ : Fin (N + 1) => Q).map (fun x => (jackknifeDelete i x, x i))
        = (Measure.pi fun _ : Fin N => Q).prod Q := by
    intro i
    have h₁ : ((Measure.pi fun _ : Fin (N + 1) => Q).map
          (fun x => (x i, x ∘ i.succAbove))).map Prod.swap
        = (Measure.pi fun _ : Fin (N + 1) => Q).map
          (fun x => (jackknifeDelete i x, x i)) := by
      rw [Measure.map_map measurable_swap (hm₀ i)]
      rfl
    rw [← h₁, pi_map_deleteSplit i, Measure.prod_swap]
  have hFi : ∀ i : Fin (N + 1),
      Integrable (fun x => F (jackknifeDelete i x, x i))
        (Measure.pi fun _ : Fin (N + 1) => Q) := fun i =>
    (integrable_map_measure (by rw [hmap i]; exact hF.aestronglyMeasurable)
      (hm i).aemeasurable).mp (by rw [hmap i]; exact hF)
  have hEach : ∀ i : Fin (N + 1),
      ∫ x, F (jackknifeDelete i x, x i) ∂(Measure.pi fun _ : Fin (N + 1) => Q)
        = ∫ s, ∫ w, F (s, w) ∂Q ∂(Measure.pi fun _ : Fin N => Q) := by
    intro i
    have h₁ : ∫ p, F p ∂((Measure.pi fun _ : Fin N => Q).prod Q)
        = ∫ x, F (jackknifeDelete i x, x i) ∂(Measure.pi fun _ : Fin (N + 1) => Q) := by
      rw [← hmap i]
      exact integral_map (hm i).aemeasurable
        (by rw [hmap i]; exact hF.aestronglyMeasurable)
    rw [← h₁]
    exact integral_prod _ hF
  rw [integral_const_mul, integral_finset_sum _ fun i _ => hFi i]
  simp only [hEach, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- **K-fold cross validation estimates the reduced-size expected risk**
(ECS §3.2, pp. 72–73): over i.i.d. folds, `E[CV_K]` equals the expected
prediction risk of the rule trained on `K` folds (`K·m` observations) — not
of the full-sample rule. -/
theorem kFold_unbiased {K m : ℕ} [NeZero m] (A : (Fin K → Fin m → Z) → H)
    -- USER-INPUT: the fold loss has a finite joint mean; ECS §3.2
    (hint : Integrable
      (fun p : (Fin K → Fin m → Z) × (Fin m → Z) =>
        mcEstimate (ℓ (A p.1)) p.2)
      ((Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin m => D).prod
        (Measure.pi fun _ : Fin m => D)))
    -- LEAN-ONLY: per-training-outcome integrability, for the inner holdout identity
    (hloss : ∀ s, Integrable (ℓ (A s)) D) :
    ∫ z, kFoldEstimate ℓ A z
        ∂(Measure.pi fun _ : Fin (K + 1) => Measure.pi fun _ : Fin m => D)
      = ∫ s, predictionRisk D ℓ (A s)
          ∂(Measure.pi fun _ : Fin K => Measure.pi fun _ : Fin m => D) := by
  unfold kFoldEstimate
  rw [integral_avg_delete_pair _ hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
    holdout_unbiased (A s) (hloss s))

/-- **Leave-one-out cross validation estimates the delete-one expected risk**
(ECS §3.2): `E[LOO]` equals the expected prediction risk of the rule trained
on `n` of the `n + 1` observations. -/
theorem loo_unbiased {n : ℕ} (A : (Fin n → Z) → H)
    -- USER-INPUT: the trained-rule loss has a finite joint mean; ECS §3.2
    (hint : Integrable
      (fun p : (Fin n → Z) × Z => ℓ (A p.1) p.2)
      ((Measure.pi fun _ : Fin n => D).prod D)) :
    ∫ x, looEstimate ℓ A x ∂(Measure.pi fun _ : Fin (n + 1) => D)
      = ∫ s, predictionRisk D ℓ (A s) ∂(Measure.pi fun _ : Fin n => D) := by
  unfold looEstimate
  rw [integral_avg_delete_pair _ hint]
  rfl

end StatLean.ComputationalStatistics

