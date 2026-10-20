module
public import StatLean.ComputationalStatistics.Core.Defs
public import StatLean.ComputationalStatistics.ForMathlib.PiMoments
public import Mathlib.MeasureTheory.Measure.Prod

public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Holdout validation

The basic correctness statement of data partitioning (ECS §3.2): a test set
that is independent of the training data gives an unbiased estimate of the
prediction risk of the *trained* rule — not of the full-sample rule, which is
the standard overclaim this file deliberately avoids.

* `predictionRisk` — `R(h) = ∫ ℓ(h, z) dD(z)`;
* `holdout_unbiased` — for a *fixed* trained hypothesis (equivalently:
  conditionally on the training data), the test-sample average loss has
  expectation `R(h)` (ECS §3.2, eq. (3.2));
* `holdout_integrated` — the tower version over a random training sample:
  `E_{S,T}[holdout] = E_S[R(A(S))]`.

**Reference.** James E. Gentle, *Elements of Computational Statistics*, Springer,
2002 (ISBN 0-387-95489-9), §3.2 (cross validation for smoothing and fitting:
the training/validation split, eqs. (3.1)–(3.2), and the warning that the
apparent error (3.1) is optimistic).  (`ECS §3.2`.)

**Proof formalization notes.**

* "Conditionally on the training data" is formalized by making the trained
  hypothesis a parameter: `holdout_unbiased` holds for every `h`, hence for
  `h = A(s)` at every training outcome `s`; the conditional-expectation
  phrasing adds nothing at this layer and is deferred.
* `predictionRisk` deliberately coexists with
  `StatLean.StatisticalLearning.risk` (concept layer of another area, not
  importable here); the SSBD-side single-fresh-point analogue of
  `holdout_integrated` is `integral_loss_fresh_eq_integral_risk` there.
* `[NeZero k]` excludes the empty test set (junk average `0`).

**Bibliographic comments.** Training/validation splitting is folklore going
back at least to Larson (1931); the modern account follows M. Stone,
"Cross-validatory choice and assessment of statistical predictions," *J. Roy.
Statist. Soc. B* **36** (1974), 111–147.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace StatLean.ComputationalStatistics

variable {Z H : Type*} [MeasurableSpace Z] {D : Measure Z}
  [IsProbabilityMeasure D] {ℓ : H → Z → ℝ}

/-- The **prediction risk** of a hypothesis `h` under the data distribution
`D`: `R(h) = ∫ ℓ(h, z) dD(z)` (ECS §3.2).  Coexists with
`StatLean.StatisticalLearning.risk`, per the per-area-reference convention. -/
noncomputable def predictionRisk (D : Measure Z) (ℓ : H → Z → ℝ) (h : H) : ℝ :=
  ∫ z, ℓ h z ∂D

/-- **Holdout validation is conditionally unbiased** (ECS §3.2, eq. (3.2)):
for a fixed trained hypothesis — equivalently, conditionally on the training
data — the average loss over an independent test sample of size `k` has
expectation the prediction risk of that hypothesis. -/
theorem holdout_unbiased {k : ℕ} [NeZero k] (h : H)
    -- USER-INPUT: the loss of the trained rule has a finite mean; ECS §3.2
    (hint : Integrable (ℓ h) D) :
    ∫ t, mcEstimate (ℓ h) t ∂(Measure.pi fun _ : Fin k => D)
      = predictionRisk D ℓ h := by
  unfold mcEstimate predictionRisk
  exact integral_avg_eval_pi hint

/-- **Integrated holdout identity** (ECS §3.2): averaging also over the
training sample, the holdout estimate has expectation the *expected risk of
the trained rule* — not the risk of any fixed rule. -/
theorem holdout_integrated {m k : ℕ} [NeZero k] (A : (Fin m → Z) → H)
    -- USER-INPUT: the trained-rule loss has a finite joint mean; ECS §3.2
    (hint : Integrable
      (fun p : (Fin m → Z) × (Fin k → Z) => mcEstimate (ℓ (A p.1)) p.2)
      ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin k => D)))
    -- LEAN-ONLY: per-training-outcome integrability, for the inner identity
    (hloss : ∀ s, Integrable (ℓ (A s)) D) :
    ∫ p, mcEstimate (ℓ (A p.1)) p.2
        ∂((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin k => D))
      = ∫ s, predictionRisk D ℓ (A s) ∂(Measure.pi fun _ : Fin m => D) := by
  rw [integral_prod _ hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
    holdout_unbiased (A s) (hloss s))

end StatLean.ComputationalStatistics
