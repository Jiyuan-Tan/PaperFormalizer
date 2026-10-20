module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimator
public import StatLean.AsymptoticStatistics.Core.PathwiseVec
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.Dirac

@[expose] public section

/-!
# Vector-valued regular-estimator predicate

This file formalizes the Hájek-style *regular-estimator* predicate for a
vector-valued functional, the regularity hypothesis underlying the
semiparametric convolution (Hájek–Le Cam) theorem.

Fix a probability measure $P$ on the sample space, a tangent set
$\dot{\mathcal P}_P$ (the closure of the score directions of the smooth
submodels through $P$), and a functional
$\psi : \mathcal P \to \mathbb R^k$ that is pathwise differentiable at $P$
with efficient influence function $\tilde\psi_P$. A sequence of estimators
$T_n : \Omega^n \to \mathbb R^k$ is **regular** at $P$ with limit law $L$ if,
for every score direction $g$ in the linear span of the tangent set, there is a
quadratic-mean-differentiable submodel $t \mapsto P_{t,g}$ with score $g$ along
which the local-perturbation, recentered, rescaled estimator converges weakly to
the **same** limit $L$, free of the direction:
$$
\sqrt n\,\bigl(T_n - \psi(P_{1/\sqrt n,\,g})\bigr)
\ \overset{P_{1/\sqrt n,\,g}^{\,n}}{\rightsquigarrow}\ L .
$$
The local parametrization uses the $1/\sqrt n$ contiguity scale, so the
$n$-fold product law is taken at the perturbed parameter
$P_{1/\sqrt n,\,g}$ rather than at $P$ itself.

Two forms are provided. The **canonical** form `IsRegularEstimator_vec` is the
verbatim van der Vaart definition (one *selected* submodel per score direction,
quantified by an existential over a chosen family). The **broad** /
*all-paths* form `IsRegularEstimator_broad_vec` requires the same weak-convergence
conclusion for **every** realising quadratic-mean path with the given score, and
is therefore a strictly stronger hypothesis; it is retained as a labeled internal
variant used in the convolution-theorem proof. The two are equivalent
(`broad ⇒ canonical` trivially; `canonical ⇒ broad` via a Cramér–Wold reduction).
This is the vector-codomain generalization of the scalar predicate in
`RegularEstimator`; it differs only in the codomain
($\mathbb R^k$ in place of $\mathbb R$, hence scalar action `•` for `*`) and the
tuple-valued efficient influence function.

Main declarations: `IsRegularEstimator_broad_vec`, `IsRegularEstimator_vec`,
`IsRegularEstimator_broad_vec.shift`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information), §25.3.2
(regular-estimator definition, the paragraph preceding Theorem 25.20),
generalized here to a vector codomain.

**Proof formalization notes.** The local parametrization is at scale
$1/\sqrt n$, so the $n$-fold product law in the weak-convergence statement is
taken at the perturbed parameter `curve.curve ((√n)⁻¹)` rather than at `P`. The
canonical form quantifies over a *chosen family* of submodels (one per score
direction), matching the book's "for every $g$, write $P_{t,g}$ for a submodel";
the broad form replaces this with a universal quantifier over all
quadratic-mean paths realising the score. `broad ⇒ canonical` is immediate
(instantiate the chosen family at any realiser, e.g. `canonicalPath`); the
converse `canonical ⇒ broad` is the Cramér–Wold reduction to the scalar
chosen-family reverse direction (`isRegularEstimator_vec_implies_broad`). The
headline convolution theorem `semiparametric_convolution_theorem_vec` consumes
the canonical form, so the presented hypothesis matches the book.
`IsRegularEstimator_broad_vec.shift` is a direct unfolding of the broad
predicate. See the per-declaration docstrings for the precise correspondence.

**Bibliographic comments.** The regular-estimator concept and the convolution
theorem it feeds originate with J. Hájek, "A characterization of limiting
distributions of regular estimates," *Zeitschrift für Wahrscheinlichkeitstheorie
und verwandte Gebiete* **14** (1970), 323–330, building on the earlier
asymptotic-minimax program of L. Le Cam ("On the asymptotic theory of estimation
and testing hypotheses," *Proc. Third Berkeley Sympos. Math. Statist. Probab.*,
1956). Hájek's theorem states that for a regular estimator the limit law is a
convolution of an optimal Gaussian component with an arbitrary independent factor;
the regularity condition formalized here is exactly the local-uniformity (free of
the direction $g$) hypothesis of that theorem. van der Vaart §25.3 presents the
semiparametric (infinite-dimensional tangent space) version; the vector-valued
specialization here corresponds to a finite-dimensional functional
$\psi : \mathcal P \to \mathbb R^k$.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds.RegularEstimatorVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.PathwiseVec
open AsymptoticStatistics.Core.EIF
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.LowerBounds.RegularEstimator
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Hájek-style vector regular-estimator predicate (all-paths / broad form).**

A sequence of vector estimators `T_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin k)`
is regular at `P` relative to a tangent set `T_set`, with limit law `L`.

This is the *all-paths* (`∀ curve`) strengthening of the vdV-canonical
chosen-family form `IsRegularEstimator_vec`: it requires the weak-convergence
conclusion for **every** realising `QMDPath` with score `g`, not merely for one
*selected* submodel per direction. As a written proposition `broad ⇒ canonical`
holds trivially, so the broad form is a strictly stronger hypothesis; it is kept
as a **labeled internal variant** for the convolution-theorem proof, while the
unlabeled canonical name `IsRegularEstimator_vec` denotes the vdV p.365 form. The
two are equivalent via `isRegularEstimator_vec_implies_broad` (and its trivial
converse).

Reference: vdV §25.3.2 (generalized to vector codomain), all-paths strengthening.
-/
def IsRegularEstimator_broad_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {k : ℕ}
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin k))
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    (_hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L] : Prop :=
  ∀ (g : ↥(L2ZeroMean P))
    (_hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (curve : QMDPath P)
    (_hscore : curve.score = g),
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))))
      L

/-- **Hájek-style vector regular-estimator predicate (vdV §25.3.2 p.365 canonical
form).**

A sequence of vector estimators `T_n : (Fin n → Ω) → EuclideanSpace ℝ (Fin k)` is
*regular* at `P` relative to the tangent set `T_set`, with limit law `L`, iff
there exists a chosen family of `QMDPath`s — one *selected* submodel per score
direction `g ∈ tangentSpace T_set` — such that along each chosen path the rescaled
estimator, recentered at the perturbed truth, converges weakly to the **same**
limit law `L`:

```
√n • (T_n − ψ((chosenFamily g hg).curve ((√n)⁻¹)))  ⇀  L .
```

This is the verbatim vdV form: vdV §25.3.2 p.365 reads "for every `g ∈ Ṗ_P`,
**write `P_{t,g}` for a submodel** …", i.e. *one selected submodel per score
direction*. It is the vector analogue of the scalar
`IsRegularEstimator_narrow`, differing only in the codomain
(`EuclideanSpace ℝ (Fin k)` in place of `ℝ`, hence `•` for `*`) and the `_vec`
efficient-influence-function tuple.

The all-paths (`∀ curve`) strengthening is `IsRegularEstimator_broad_vec`. The two
are equivalent: `broad ⇒ canonical` trivially (instantiate `chosenFamily` at any
realiser, e.g. `canonicalPath`), and `canonical ⇒ broad` via
`isRegularEstimator_vec_implies_broad` (Cramér–Wold reduction to the scalar
chosen-family reverse direction). The headline convolution theorem
`semiparametric_convolution_theorem_vec` consumes **this** canonical form, so the
presented hypothesis byte-matches the book.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.3.2
(regular-estimator definition, paragraph preceding Theorem 25.20), generalized to
vector codomain. -/
def IsRegularEstimator_vec
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    {k : ℕ}
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin k))
    {IF_eff : Fin k → ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ)
    (_hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (L : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure L] : Prop :=
  ∃ chosenFamily :
      ∀ (g : ↥(L2ZeroMean P)),
        (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier → QMDPath P,
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
      (chosenFamily g hg).score = g) ∧
    (∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
      WeakConverges
        (fun n : ℕ =>
          (MeasureTheory.Measure.pi
              (fun _ : Fin n => (chosenFamily g hg).curve ((Real.sqrt n)⁻¹))).map
            (fun X : Fin n → Ω =>
              Real.sqrt n •
                (T_n n X - ψ ((chosenFamily g hg).curve ((Real.sqrt n)⁻¹)))))
        L)

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {T_set : TangentSpec P}
variable {k : ℕ}
variable {ψ : Measure Ω → EuclideanSpace ℝ (Fin k)}
variable {IF_eff : Fin k → ↥(L2ZeroMean P)}
variable {hψ : PathwiseDifferentiableAt_vec P (tangentSpace T_set) ψ}
variable {hEIF : IsEfficientInfluenceFunction_vec (P := P) (T := tangentSpace T_set)
                  hψ.derivative IF_eff}
variable {T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k)}
variable {L : Measure (EuclideanSpace ℝ (Fin k))}

/-- **Direct unfolding of `IsRegularEstimator_broad_vec`.** -/
theorem IsRegularEstimator_broad_vec.shift [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator_broad_vec P T_set ψ hψ hEIF T_n L)
    (g : ↥(L2ZeroMean P))
    (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (curve : QMDPath P) (hscore : curve.score = g) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n •
              (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))))
      L :=
  hReg g hg curve hscore

end AsymptoticStatistics.LowerBounds.RegularEstimatorVec
