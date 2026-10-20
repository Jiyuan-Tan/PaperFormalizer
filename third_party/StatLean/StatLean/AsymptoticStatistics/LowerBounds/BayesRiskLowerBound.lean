module
public import StatLean.AsymptoticStatistics.LowerBounds.FinDimSubmodel
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianShift
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

/-!
# Finite-sample minimax risk lower bound via limit-experiment Bayes risk

For any finite subset $I_0 \subset \mathbb{R}^m$ of score directions, a
prior $\pi$ on $I_0$ (nonnegative weights summing to $1$), and a bounded,
uniformly continuous loss function $\ell$, the limit inferior of the
per-direction maximum risk along the LAN-perturbed submodels
$P_{n,h} = \gamma_h\big(1/\sqrt{n}\big)$ is bounded below by the infimum,
over deterministic estimators in the Gaussian limit experiment, of the
prior-weighted Bayes risk:
$$
\liminf_{n} \ \max_{h \in I_0} \ \mathbb{E}_{P_{n,h}^{\,n}}
  \Big[ \ell\big(\sqrt{n}\,(T_n - \psi(P_{n,h}))\big) \Big]
\ \ge\
\inf_{T} \ \mathbb{E}_{X \sim N(0, I_m)}
  \Big[ \sum_{h \in I_0} \pi(h)\,
    \exp\!\big(\langle h, X\rangle - \tfrac{1}{2}\|h\|^2\big)\,
    \ell\big(T(X) - \langle \tilde\ell_{\mathrm{eff}}, \textstyle\sum_i h_i\, g_i\rangle\big) \Big].
$$
Here $\exp(\langle h, X\rangle - \tfrac{1}{2}\|h\|^2)$ is the Gaussian-shift
Radon–Nikodym density $dP_h/dP_0$ relating the shifted Gaussian $N(h, I_m)$
to the centred Gaussian $N(0, I_m)$, the centring term
$\langle \tilde\ell_{\mathrm{eff}}, \sum_i h_i g_i\rangle$ is the
limit-experiment estimand evaluated against the efficient influence
function $\tilde\ell_{\mathrm{eff}}$ and the orthonormal score basis
$(g_i)$, and the infimum is over all estimators $T : \mathbb{R}^m \to \mathbb{R}$
in the limit experiment.

The headline declaration is `bayes_risk_lower_bound`.

*Deviation from the book.* The infimum on the right is taken over
**measurable** estimators $T$ only (rather than all functions). This is a
Lean-side regularity restriction: it makes the per-direction integrand
$\exp(\cdot)\,\ell(T(\cdot) - c_h)$ AE-strongly-measurable (hence
integrable), and does not change the infimum over any reasonable estimator
class, since deterministic measurable estimators are dense in the natural
topology. The book leaves this measurability implicit.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge
Series in Statistical and Probabilistic Mathematics, Cambridge University
Press, 1998, Chapter 25 (Semiparametric Models), §25.3, synthesis step in
the proof of the local asymptotic minimax theorem (Theorem 25.21).

**Proof formalization notes.** The argument is the synthesis step of the
local asymptotic minimax bound, formalized in three stages (detailed in the
docstring of `bayes_risk_lower_bound`).

* *Step 1 (max ≥ Bayes; pure arithmetic):* for each $n$, the per-direction
  maximum risk dominates the prior-weighted Bayes risk
  $B_n(\pi) = \sum_{h \in I_0} \pi(h)\,\mathbb{E}_{P_{n,h}^n}[\ell(\cdots)]$,
  via $\sum \pi = 1$ and $\pi \ge 0$.
* *Step 2 (Le Cam passage; supplied as the hypothesis
  `hBayes_n_to_limitBayes`):* the liminf of $B_n(\pi)$ dominates the
  infimum over deterministic estimators of the prior-weighted Bayes risk in
  the shifted limit experiment $N(h, I_m)$. This packages the deep
  weak-convergence content of §25.3 (likelihood-ratio convergence under
  contiguity, uniform integrability via tightness, the extended continuous
  mapping theorem, and Le Cam's third lemma).
* *Step 3 (Gaussian-shift density swap + Tonelli):* each shifted Gaussian
  integral is rewritten as a centred-Gaussian integral against the
  Gaussian-shift density $\exp(\langle h, X\rangle - \tfrac{1}{2}\|h\|^2)$
  (`gaussianShift_change_of_measure`), and integral linearity
  (`integral_finset_sum`) exchanges the finite sum over $h$ with the
  integral, identifying the inner integrand with the goal's right-hand side.

The boundedness and uniform continuity of $\ell$ supply the
`IsBoundedUnder` / `IsCoboundedUnder` side-conditions for
`Filter.liminf_le_liminf` and the integrability needed in Step 3.

**Bibliographic comments.** The local asymptotic minimax theorem
originates with J. Hájek, *Local asymptotic minimax and admissibility in
estimation*, in Proceedings of the Sixth Berkeley Symposium on Mathematical
Statistics and Probability, Vol. 1, University of California Press, 1972,
pp. 175–194, which proved the asymptotic minimax lower bound for the
maximum risk of estimators in locally asymptotically normal experiments
(companion to Hájek's 1970 convolution theorem, *A characterization of
limiting distributions of regular estimates*, Z. Wahrsch. Verw. Gebiete 14
(1970), 323–330). The reduction of the asymptotic minimax problem to a
Bayes-risk computation in the Gaussian limit experiment is due to L. Le Cam
(see *Asymptotic Methods in Statistical Decision Theory*, Springer, 1986).
The formalization here follows the synthesis of this Hájek–Le Cam theory
for semiparametric models in vdV §25.3, Theorem 25.21.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics.LowerBounds.BayesRiskLowerBound

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.LowerBounds.FinDimSubmodel
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Finite-sample max-risk lower bound by limit-experiment Bayes risk.

For an `L²(P)`-orthonormal score basis `g_P : Fin m → L²₀(P)` of a
finite-dim subspace of the tangent space, a finite set `I_0 ⊂ ℝᵐ` of
score directions, a prior `π : I_0 → ℝ` (probability weights summing to
1), and a bounded uniformly continuous loss `ℓ : ℝ → ℝ`: along the
LAN-perturbed submodels `P_{n,h} = γ_h.curve(1/√n)`, the limit-inferior
of the per-`h` maximum risk is bounded below by the infimum (over
deterministic estimators in the Gaussian limit experiment) of the
prior-weighted Bayes risk.

Reference: vdV §25.3.

Proof structure, in three steps.

Step 1 ("max ≥ Bayes"; pure arithmetic): for each `n`,
the per-`h` maximum risk dominates the prior-weighted Bayes risk
`B_n(π) := Σ_{h∈I_0} π(h) · E_{Pⁿ_{n,h}}[ℓ(√n(T_n − ψ(P_{n,h})))]`.
This step is closed in the proof body using
`Finset.sum_le_sum` + `mul_le_mul_of_nonneg_left` + `_hπ_sum`.

Step 2 (Le Cam passage; supplied by `hBayes_n_to_limitBayes`):
the per-`n` prior-weighted Bayes risk's liminf dominates the infimum
(over deterministic estimators) of the prior-weighted Bayes risk in
the *shifted* limit experiment `N(h, I_m)`:

```
liminf_n B_n(π) ≥ ⨅_T Σ_{h∈I_0} π(h) · ∫_{N(h, I_m)} ℓ(T(X) − A_m h) dX
```

This is the Le Cam content (steps 1–4 of the book proof: LR convergence
under contiguity, uniform integrability via tightness, extended CMT,
and the per-`h` change-of-measure to `P_{n,h}^n`).

Step 3 (Gaussian-shift density swap + Tonelli): each shifted
Gaussian integral rewrites as a centred-Gaussian integral against the
Gaussian-shift density `exp(⟨h, X⟩ − ‖h‖²/2)`:

```
∫_{N(h, I_m)} ℓ(T(X) − A_m h) dX
  = ∫_{N(0, I_m)} exp(⟨h, X⟩ − ‖h‖²/2) · ℓ(T(X) − A_m h) dX.
```

This is closed by `ProbabilityTheory.gaussianShift_change_of_measure`.
With it in hand, integral linearity (`MeasureTheory.integral_finset_sum`)
exchanges `Σ_h π(h) ∫_{N(0, I_m)} = ∫_{N(0, I_m)} Σ_h π(h) ·`,
identifying the inner integrand with the goal RHS. -/
theorem bayes_risk_lower_bound
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (_hg_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (_hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    (γ : (Fin m → ℝ) → QMDPath P)
    (_hγ_score : ∀ h : Fin m → ℝ,
      (γ h).score = ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P)))
    (I_0 : Finset (Fin m → ℝ)) (π : (Fin m → ℝ) → ℝ)
    (hπ_nn : ∀ h ∈ I_0, 0 ≤ π h)
    (hπ_sum : ∑ h ∈ I_0, π h = 1)
    (ℓ : ℝ → ℝ) (hℓ_bdd : ∃ B, ∀ x, |ℓ x| ≤ B)
    (_hℓ_uc : UniformContinuous ℓ)
    -- risks dominates the infimum (over deterministic estimators) of the
    -- prior-weighted Bayes risk in the *shifted* limit experiment
    -- `N(h, I_m)`. This is the deep weak-convergence + UI + extended-CMT
    -- passage of vdV §25.3 (by Le Cam's third lemma and the extended
    -- continuous mapping theorem, the Bayes risk converges). The
    -- limit-experiment Bayes risk on the right uses
    -- `Measure.pi (fun i => gaussianReal (h i) 1)` (= `N(h, I_m)` on
    -- `Fin m → ℝ`).
    (hBayes_n_to_limitBayes :
      Filter.liminf
        (fun n : ℕ =>
          ∑ h ∈ I_0, π h *
            ∫ X : Fin n → Ω, ℓ (Real.sqrt n *
              (T_n n X - ψ (submodelAt (γ h) n)))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin n => submodelAt (γ h) n)))
        atTop
        ≥
      ⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1)))) :
    -- Conclusion: liminf_n max_{h∈I_0} E_{Pⁿ}[ℓ(√n(T_n − ψ(γh.curve(1/√n))))]
    -- ≥ inf_{T : measurable estimator} E_{X∼N(0,I_m)}
    --     [ Σ_{h∈I_0} π(h) · exp(⟨h,X⟩ − ‖h‖²/2)
    --       · ℓ(T(X) − ⟨IF_eff, Σᵢ hᵢ g_P i⟩) ].
    --
    -- The iInf ranges over **measurable** estimators only: necessary so
    -- that the per-`h` integrand `exp(...) * ℓ(T X − c_h)` is
    -- AE-strongly-measurable (hence integrable; cf.
    -- `gaussianShift_integrable`). Restricting to measurable `T` does
    -- not change the iInf in any reasonable estimator class
    -- (deterministic measurable estimators are dense in the natural
    -- topology), but is required to make the integrability machinery
    -- of the proof body apply.
    Filter.liminf
      (fun n : ℕ =>
        I_0.sup' (Finset.nonempty_of_sum_ne_zero (f := π)
          (by have : (1 : ℝ) ≠ 0 := one_ne_zero; rw [← hπ_sum] at this;
              exact this))
          (fun h =>
            ∫ X : Fin n → Ω, ℓ (Real.sqrt n *
              (T_n n X - ψ (submodelAt (γ h) n)))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin n => submodelAt (γ h) n))))
      atTop
      ≥
    ⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
      ∫ X : (Fin m → ℝ),
        (∑ h ∈ I_0, π h *
          Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
          ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
            ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
        ∂(MeasureTheory.Measure.pi
            (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
  -- Local abbreviation for the per-`h` `n`-sample risk used both in the
  -- Bayes sum (`hBayes_n_to_limitBayes`) and in the per-`h` `sup'` (the
  -- goal). Defined as a local `let`-binder; we use the literal integral
  -- form in both occurrences and chain through `riskEq` definitional
  -- rewrites.
  let risk : ℕ → (Fin m → ℝ) → ℝ := fun n h =>
    ∫ X : Fin n → Ω, ℓ (Real.sqrt n *
      (T_n n X - ψ (submodelAt (γ h) n)))
        ∂(MeasureTheory.Measure.pi (fun _ : Fin n => submodelAt (γ h) n))
  -- Nonempty witness for `I_0` extracted from `∑ π = 1`.
  have hI_ne : I_0.Nonempty :=
    Finset.nonempty_of_sum_ne_zero
      (by have : (1 : ℝ) ≠ 0 := one_ne_zero; rw [← hπ_sum] at this; exact this)
  -- Step 1 (pure arithmetic): for each `n`, the prior-weighted Bayes
  -- risk `Σ_h π(h) risk(n,h)` is dominated by the per-`h` maximum risk
  -- `sup'_{h ∈ I_0} risk(n,h)`. Uses `Σ π = 1` and `π ≥ 0`.
  have h_bayes_le_max :
      ∀ n : ℕ, (∑ h ∈ I_0, π h * risk n h) ≤ I_0.sup' hI_ne (risk n) := by
    intro n
    -- Bound each summand by `π h * sup'`, then sum out using `∑ π = 1`.
    have hbound : ∀ h ∈ I_0,
        π h * risk n h ≤ π h * I_0.sup' hI_ne (risk n) := by
      intro h hh
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' (f := risk n) hh) (hπ_nn h hh)
    calc
      ∑ h ∈ I_0, π h * risk n h
          ≤ ∑ _ ∈ I_0, π _ * I_0.sup' hI_ne (risk n) :=
            Finset.sum_le_sum hbound
      _ = (∑ h ∈ I_0, π h) * I_0.sup' hI_ne (risk n) := by
            rw [← Finset.sum_mul]
      _ = 1 * I_0.sup' hI_ne (risk n) := by rw [hπ_sum]
      _ = I_0.sup' hI_ne (risk n) := by rw [one_mul]
  -- Boundedness of `ℓ` by `B`: extracted once and reused for the
  -- `IsBoundedUnder`/`IsCoboundedUnder` side-conditions of
  -- `Filter.liminf_le_liminf`.
  obtain ⟨B, hB⟩ := hℓ_bdd
  -- Pointwise bound on each per-`h` integrated risk by `B`: every
  -- single-`h` integral has absolute value ≤ B (since `|ℓ| ≤ B` and the
  -- pushforward measure is a probability measure).
  have habs_risk : ∀ (k : ℕ) (h : Fin m → ℝ), |risk k h| ≤ B := by
    intro k h
    -- `submodelAt (γ h) k = (γ h).curve ((√k)⁻¹)` is a probability
    -- measure; the `Measure.pi` over `Fin k` then is too.
    haveI hPM_curve : IsProbabilityMeasure (submodelAt (γ h) k) :=
      (γ h).curve_isProbability _
    haveI hPM_pi : IsProbabilityMeasure
        (MeasureTheory.Measure.pi
          (fun _ : Fin k => submodelAt (γ h) k)) := by
      infer_instance
    -- `|∫ ℓ(…)| ≤ ∫ |ℓ(…)| ≤ ∫ B = B · μ(univ) = B`.
    refine (abs_integral_le_integral_abs).trans ?_
    have h_le_const : ∀ X : Fin k → Ω,
        |ℓ (Real.sqrt k * (T_n k X - ψ (submodelAt (γ h) k)))| ≤ B :=
      fun X => hB _
    have h_int_const : MeasureTheory.Integrable
        (fun _ : Fin k → Ω => B)
        (MeasureTheory.Measure.pi (fun _ : Fin k => submodelAt (γ h) k)) :=
      MeasureTheory.integrable_const _
    calc
      ∫ X : Fin k → Ω,
          |ℓ (Real.sqrt k * (T_n k X - ψ (submodelAt (γ h) k)))|
            ∂(MeasureTheory.Measure.pi (fun _ : Fin k => submodelAt (γ h) k))
          ≤ ∫ _ : Fin k → Ω, B
              ∂(MeasureTheory.Measure.pi (fun _ : Fin k => submodelAt (γ h) k))
          := MeasureTheory.integral_mono_of_nonneg
              (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
              h_int_const
              (Filter.Eventually.of_forall h_le_const)
      _ = B := by
            rw [MeasureTheory.integral_const]
            simp
  -- Step 2 (chain via `liminf` monotonicity): both `liminf` arguments
  -- are eventually in `[-B, B]`, supplying the boundedness side-
  -- conditions of `Filter.liminf_le_liminf`.
  -- LHS sequence (Bayes risks) is bounded below by `-B`.
  have hBayes_bdd_below_pt : ∀ k : ℕ,
      -B ≤ ∑ h ∈ I_0, π h * risk k h := by
    intro k
    have hsum_neg : -B = ∑ h ∈ I_0, π h * (-B) := by
      rw [← Finset.sum_mul, hπ_sum, one_mul]
    rw [hsum_neg]
    refine Finset.sum_le_sum (fun h hh => ?_)
    exact mul_le_mul_of_nonneg_left
      (neg_le_of_abs_le (habs_risk k h)) (hπ_nn h hh)
  have hBayes_bdd_below : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop
      (fun k : ℕ => ∑ h ∈ I_0, π h * risk k h) :=
    Filter.isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall hBayes_bdd_below_pt)
  -- RHS sequence (per-`h` max risks) is bounded above by `B`.
  have hMax_bdd_above_pt : ∀ k : ℕ,
      I_0.sup' hI_ne (risk k) ≤ B := by
    intro k
    refine Finset.sup'_le hI_ne (risk k) ?_
    intro h _
    exact le_of_abs_le (habs_risk k h)
  have hMax_bdd_above : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun k : ℕ => I_0.sup' hI_ne (risk k)) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall hMax_bdd_above_pt)
  -- `IsCoboundedUnder ≥` from `IsBoundedUnder ≤`.
  have hMax_cobdd : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop
      (fun k : ℕ => I_0.sup' hI_ne (risk k)) :=
    hMax_bdd_above.isCoboundedUnder_ge
  -- Boundedness ingredients reused inside the per-`T` Gaussian-shift step.
  -- The bound `B` and `|ℓ| ≤ B` were extracted above; restate as a `‖·‖`
  -- bound for the `Integrable.mul_bdd` API in `gaussianShift_integrable`.
  have hℓ_norm_bdd : ∀ x : ℝ, ‖ℓ x‖ ≤ B := fun x => (Real.norm_eq_abs _).symm ▸ hB x
  -- Continuity of `ℓ` (from `_hℓ_uc`) gives measurability.
  have hℓ_meas : Measurable ℓ := _hℓ_uc.continuous.measurable
  -- Step 3 (Gaussian-shift density swap + Tonelli). The goal RHS
  -- is `⨅ T (_ : Measurable T), ∫_{N(0,I_m)} Σ_h π(h) · exp(⟨h,X⟩ − ‖h‖²/2)
  -- · ℓ(...) dX`. We show this equals `⨅ T (_ : Measurable T), Σ_h π(h)
  -- · ∫_{N(h, I_m)} ℓ(...) dX`, the RHS of `hBayes_n_to_limitBayes`. Two
  -- sub-steps: (i) per-`h` Gaussian-shift identity from
  -- `gaussianShift_change_of_measure`; (ii) integral linearity
  -- (`integral_finset_sum`) to swap `Σ` and `∫`. Step (ii) needs
  -- integrability of each per-`h` summand, supplied by
  -- `gaussianShift_integrable` using `Measurable T` to derive
  -- AE-strong-measurability of the loss-composition `ℓ ∘ (T - c_h)`.
  have h_Bayes_inner_eq :
      ∀ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1)))
        =
        ∫ X : (Fin m → ℝ),
          (∑ h ∈ I_0, π h *
            Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
              ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
    intro T hT_meas
    -- Per-`h` AE-strong-measurability of `fun X => ℓ (T X - c_h)`.
    have h_inner_aesm : ∀ h : Fin m → ℝ,
        AEStronglyMeasurable
          (fun X : Fin m → ℝ =>
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
          (MeasureTheory.Measure.pi
            (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
      intro h
      have : Measurable
          (fun X : Fin m → ℝ =>
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)) :=
        hℓ_meas.comp (hT_meas.sub_const _)
      exact this.aestronglyMeasurable
    -- Step 3.i: rewrite each per-`h` shifted integral via the Gaussian-shift
    -- identity. After the rewrite, every summand integrates against the
    -- common centred Gaussian `Measure.pi (fun _ => gaussianReal 0 1)`.
    have h_after_shift :
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1)))
        =
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
              ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                  ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
      refine Finset.sum_congr rfl ?_
      intro h _hh
      rw [ProbabilityTheory.gaussianShift_change_of_measure h
        (fun X => ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
            ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))]
    -- Step 3.ii: pull `Σ` inside `∫` via integral linearity. Each scaled
    -- integrand is integrable by `gaussianShift_integrable` (multiplied by
    -- the nonnegative weight `π h`).
    have h_Sum_into_integral :
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
              ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                  ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1)))
        =
        ∫ X : (Fin m → ℝ),
          (∑ h ∈ I_0, π h *
            (Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
              ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)))
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
      -- Each summand is `π h * ∫ f_h = ∫ (π h * f_h)` via `integral_const_mul`,
      -- then `∑ ∫ f_h = ∫ ∑ f_h` via `integral_finset_sum`.
      have h_each :
          ∀ h ∈ I_0,
            π h *
              ∫ X : (Fin m → ℝ),
                Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
                  ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                      ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1)))
            =
              ∫ X : (Fin m → ℝ),
                π h *
                  (Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
                    ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                        ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
                ∂(MeasureTheory.Measure.pi
                    (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
        intro h _
        rw [MeasureTheory.integral_const_mul]
      rw [Finset.sum_congr rfl h_each]
      -- Now `∑ ∫ (π h * f_h) = ∫ ∑ (π h * f_h)`. Each scaled integrand
      -- is integrable by `gaussianShift_integrable` (bounded × Gaussian
      -- shift density, both AE-strongly-measurable) followed by
      -- `Integrable.const_mul` for the `π h` factor.
      have h_int_each :
          ∀ h ∈ I_0,
            MeasureTheory.Integrable
              (fun X : Fin m → ℝ =>
                π h *
                  (Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
                    ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                        ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)))
              (MeasureTheory.Measure.pi
                (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
        intro h _hh
        -- Bound on the composed loss: `‖ℓ (T X - c_h)‖ ≤ B`.
        have h_comp_bdd :
            ∀ X : Fin m → ℝ,
              ‖ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                  ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)‖ ≤ B :=
          fun X => hℓ_norm_bdd _
        exact (ProbabilityTheory.gaussianShift_integrable h
          (h_inner_aesm h) h_comp_bdd).const_mul (π h)
      rw [← MeasureTheory.integral_finset_sum I_0 h_int_each]
    -- Combine the two steps. The final integral matches the goal modulo
    -- the associativity `π h * (exp · ℓ) = π h * exp · ℓ`, applied
    -- summand-wise via `Finset.sum_congr`.
    rw [h_after_shift, h_Sum_into_integral]
    refine MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun X => ?_))
    refine Finset.sum_congr rfl ?_
    intro h _
    ring
  -- Step 4 (combine the inf-monotonicity). The bound from
  -- `hBayes_n_to_limitBayes` uses the LHS form
  -- `⨅ T (_ : Measurable T), Σ_h π(h) · ∫_{N(h, I_m)} ℓ`; the goal uses
  -- `⨅ T (_ : Measurable T), ∫_{N(0, I_m)} Σ_h π(h) · exp · ℓ`. By
  -- `h_Bayes_inner_eq`, the bodies of the two `⨅` are pointwise equal
  -- on the `Measurable T` quantifier, so the `⨅`s coincide.
  have h_iInf_eq :
      (⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
        ∑ h ∈ I_0, π h *
          ∫ X : (Fin m → ℝ),
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
                ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ)
            ∂(MeasureTheory.Measure.pi
                (fun i : Fin m => (ProbabilityTheory.gaussianReal (h i) 1))))
      =
      (⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
        ∫ X : (Fin m → ℝ),
          (∑ h ∈ I_0, π h *
            Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
              ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1)))) := by
    refine iInf_congr ?_
    intro T
    refine iInf_congr ?_
    intro hT
    exact h_Bayes_inner_eq T hT
  -- Lift `hBayes_n_to_limitBayes` to the goal RHS by rewriting through
  -- the `iInf` equality.
  have hBayes_to_goalRHS :
      Filter.liminf
        (fun n : ℕ =>
          ∑ h ∈ I_0, π h * risk n h)
        atTop
        ≥
      ⨅ (T : (Fin m → ℝ) → ℝ) (_hT : Measurable T),
        ∫ X : (Fin m → ℝ),
          (∑ h ∈ I_0, π h *
            Real.exp ((∑ i, h i * X i) - (∑ i, (h i)^2) / 2) *
            ℓ (T X - ⟪(IF_eff : ↥(L2ZeroMean P)),
              ∑ i, (h i) • (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin m => (ProbabilityTheory.gaussianReal 0 1))) := by
    rw [← h_iInf_eq]
    exact hBayes_n_to_limitBayes
  -- Final chain: `RHS_goal ≤ liminf Bayes ≤ liminf max-risk`.
  refine le_trans hBayes_to_goalRHS ?_
  exact Filter.liminf_le_liminf
    (Filter.Eventually.of_forall h_bayes_le_max)
    hBayes_bdd_below hMax_cobdd

end AsymptoticStatistics.LowerBounds.BayesRiskLowerBound
