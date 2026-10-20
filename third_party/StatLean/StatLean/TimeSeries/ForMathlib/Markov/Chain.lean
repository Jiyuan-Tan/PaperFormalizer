module
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.Probability.Kernel.Composition.Comp

@[expose] public section

/-!
# Markov chains from iterated kernels — invariance glue

A time-homogeneous Markov chain on a state space `S` is the data of a transition kernel
`κ : Kernel S S`; its `n`-step behaviour is the kernel power `κ ^ n` (Mathlib's `Monoid`
structure on `Kernel S S`, with the Chapman–Kolmogorov identities), and the `n`-step
marginal from an initial law `μ₀` is `nstep κ μ₀ n = μ₀.bind (κ ^ n)`.

This file provides the thin glue between Mathlib's `Kernel.Invariant` (`μ.bind κ = μ`)
and the iterated-kernel picture: invariance propagates to all powers, so a chain started
at an invariant law has all one-dimensional marginals equal — the marginal core of FY
Theorem 2.2 ("ergodicity ⇒ initializing at the stationary law gives a strictly
stationary process"; the full finite-dimensional statement needs the path-space
construction and is deferred to the batch that builds it).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.4
(pp. 33–35): the Markov-chain framework, eq. (2.9) (`n`-step laws), Theorem 2.2.
(`FY §2.1.4`.)

**Proof formalization notes.** `Measure.bind` along a kernel keeps measurability
side-conditions inside Mathlib's `Kernel` API; `nstep_succ` is associativity of `bind`
specialised to kernels, and `invariant_nstep_eq` is induction from `Kernel.Invariant`.

**Bibliographic comments.** Chapman–Kolmogorov and the invariant-measure formulation of
stationarity go back to A. A. Markov (1906) and A. N. Kolmogorov ("Über die analytischen
Methoden in der Wahrscheinlichkeitsrechnung", *Math. Ann.* **104** (1931), 415–458).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S]

/-- The **`n`-step marginal** of the chain with transition kernel `κ` started at `μ₀`
(FY eq. (2.9)'s `F_n`, as a measure-valued map). -/
noncomputable def nstep (κ : Kernel S S) (μ0 : Measure S) (n : ℕ) : Measure S :=
  μ0.bind (κ ^ n : Kernel S S)

/-- Zero steps: the initial law (for an s-finite initial law). -/
theorem nstep_zero (κ : Kernel S S) (μ0 : Measure S) [SFinite μ0] :
    nstep κ μ0 0 = μ0 := by
  rw [nstep, pow_zero]
  exact Measure.id_comp

/-- One step of Chapman–Kolmogorov: `nstep (n+1) = (nstep n).bind κ`. -/
theorem nstep_succ (κ : Kernel S S) [IsSFiniteKernel κ] (μ0 : Measure S) [SFinite μ0]
    (n : ℕ) : nstep κ μ0 (n + 1) = (nstep κ μ0 n).bind κ := by
  rw [nstep, nstep, pow_succ']
  exact (Measure.comp_assoc (μ := μ0) (κ := (κ ^ n : Kernel S S)) (η := κ)).symm

/-- Invariance propagates to kernel powers. -/
theorem invariant_pow {κ : Kernel S S} [IsSFiniteKernel κ] {μ : Measure S} [SFinite μ]
    (h : κ.Invariant μ) (n : ℕ) : (κ ^ n).Invariant μ := by
  induction n with
  | zero => rw [pow_zero]; exact Measure.id_comp
  | succ n ih => rw [pow_succ]; exact ih.comp h

/-- A chain started at an invariant law has all `n`-step marginals equal to it
(the marginal core of FY Theorem 2.2). -/
theorem invariant_nstep_eq {κ : Kernel S S} [IsSFiniteKernel κ] {μ : Measure S}
    [SFinite μ] (h : κ.Invariant μ) (n : ℕ) : nstep κ μ n = μ := by
  rw [nstep]
  exact (invariant_pow h n).def

end StatLean.TimeSeries
