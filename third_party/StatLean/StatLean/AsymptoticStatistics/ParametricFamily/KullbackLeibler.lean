module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import Mathlib.InformationTheory.KullbackLeibler.Basic

@[expose] public section

/-!
# Kullback--Leibler identifiability for subprobability models

This file formalizes van der Vaart, Lemma 5.35.  Mathlib's `klDiv` is the
finite-measure extension

`integral llr + mass(second) - mass(first)`.

The book's raw negative log-likelihood objective therefore corresponds to
`klDiv + mass(first) - mass(second)`.  Keeping the objective in `EReal`
preserves the convention `log 0 = -infinity`; in particular no `toReal` is
applied to an infinite divergence.
-/

open MeasureTheory Set
open scoped ENNReal

namespace AsymptoticStatistics.ParametricFamily

/-- The nonnegative divergence whose negative is vdV's population log-likelihood
objective in Lemma 5.35.

For measures `P theta0` and `P theta`, Mathlib's `klDiv` already contains the
finite-measure correction `mass(P theta) - mass(P theta0)`.  The additional
truncated mass difference cancels that correction under the subprobability / true
probability hypotheses of Lemma 5.35, recovering the raw log-likelihood ratio.

Edge behavior: if absolute continuity or log-integrability fails, `klDiv = infinity`,
so this definition is `infinity` and its negation in `EReal` is `-infinity`, matching
the book's `log 0 = -infinity` convention. -/
noncomputable def subprobKLDivergence
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (P : Theta -> Measure X) (theta0 theta : Theta) : EReal :=
  ((InformationTheory.klDiv (P theta0) (P theta)
      + (P theta0 univ - P theta univ) : ENNReal) : EReal)

/-- **van der Vaart, Lemma 5.35 (KL identifiability).**

For a family of subprobability measures whose true member is a probability,
the extended-real population log-likelihood `-subprobKLDivergence` has a strict
maximum at the truth whenever the truth is identifiable.  Strictness is derived
from `InformationTheory.klDiv_eq_zero_iff`; it is not a caller hypothesis. -/
theorem kl_uniquely_maximized_at_truth
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (P : Theta -> Measure X) (theta0 : Theta)
    (hsub : forall theta, P theta univ <= 1)
    (hP0 : P theta0 univ = 1)
    (hident : forall theta, P theta = P theta0 -> theta = theta0)
    (theta : Theta) (htheta : theta ≠ theta0) :
    -subprobKLDivergence P theta0 theta <
      -subprobKLDivergence P theta0 theta0 := by
  letI : IsFiniteMeasure (P theta0) :=
    ⟨by rw [hP0]; exact ENNReal.one_lt_top⟩
  letI : IsFiniteMeasure (P theta) :=
    ⟨(hsub theta).trans_lt ENNReal.one_lt_top⟩
  have hmeasure_ne : P theta0 ≠ P theta := by
    intro hmeasure
    exact htheta (hident theta hmeasure.symm)
  have hkl_ne : InformationTheory.klDiv (P theta0) (P theta) ≠ 0 := by
    intro hkl
    exact hmeasure_ne (InformationTheory.klDiv_eq_zero_iff.mp hkl)
  have hkl_pos : 0 < InformationTheory.klDiv (P theta0) (P theta) :=
    pos_iff_ne_zero.mpr hkl_ne
  have hdiv_pos :
      0 < InformationTheory.klDiv (P theta0) (P theta)
        + (P theta0 univ - P theta univ) :=
    hkl_pos.trans_le (le_add_right le_rfl)
  have hdiv_pos' :
      (0 : EReal) <
        ((InformationTheory.klDiv (P theta0) (P theta)
          + (P theta0 univ - P theta univ) : ENNReal) : EReal) :=
    EReal.coe_ennreal_pos.mpr hdiv_pos
  simpa [subprobKLDivergence, hP0] using EReal.neg_lt_neg_iff.mpr hdiv_pos'

end AsymptoticStatistics.ParametricFamily
