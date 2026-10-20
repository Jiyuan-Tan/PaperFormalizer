module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Topology.Order.Monotone

@[expose] public section

/-!
# Markov's inequality and the Chernoff bound

Two foundational tail bounds. Both are reference results in Lu's §4.2 setup for
sub-Gaussian theory but are themselves general (no sub-Gaussian hypothesis).

**Markov's inequality.** For a nonnegative integrable random variable $X$ and a
threshold $t > 0$,
$$ \mathbb{P}(X \ge t) \;\le\; \frac{\mathbb{E}[X]}{t}. $$
The book states this with the strict event $\{X > t\}$; the inequality $\le$ is
preserved by enlarging the event to $\{X \ge t\}$, so the form proved here
($t \le X$) majorises and is strictly stronger than the book's version.

**Chernoff bound.** Let $\psi(\lambda) = \log \mathbb{E}\big[e^{\lambda (X - \mathbb{E}[X])}\big]$
be the centered cumulant generating function (log-MGF) and let
$\psi^*(t) = \sup_{\lambda \ge 0}\big(\lambda t - \psi(\lambda)\big)$
be its Fenchel–Legendre dual. Then for every $t \ge 0$,
$$ \mathbb{P}\big(X - \mathbb{E}[X] \ge t\big) \;\le\; e^{-\psi^*(t)}. $$
The Lean statement makes no sign assumption on $t$, so it is strictly stronger
than the book's $t \ge 0$ version (for $t < 0$ the bound may be vacuous, but it
remains valid).

The Chernoff statement carries two side conditions that are forced by the Lean
formalisation rather than the book text (see the `-- LEAN-ONLY` tags on the
hypotheses): a uniform MGF-finiteness hypothesis on $[0, \infty)$ (so the
per-$\lambda$ exponential Markov step applies at every $\lambda$), and a
bounded-above hypothesis on $\{\lambda t - \psi(\lambda) : \lambda \ge 0\}$ (so
the real-valued supremum defining $\psi^*$ agrees with the textbook sup;
otherwise it falls back on the junk value $0$, making $e^{-\psi^*} = 1$ and the
bound vacuous).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland,
2025 (ISBN 978-3-032-03160-0), Chapter 4 (Concentration Inequalities), §4.2
(Sub-Gaussian Random Variables): Markov's inequality and Theorem 4.4 (Chernoff
Bound).

**Proof formalization notes.**

* `markov` — a thin wrapper around Mathlib's
  `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`, proving the $t \le X$ form
  (which majorises the book's strict $X > t$ form).

* `chernoff` — for each $\lambda \ge 0$, Mathlib's
  `ProbabilityTheory.measure_ge_le_exp_cgf` (Markov applied to the exponential
  moment) gives
  $\mathbb{P}(X - \mathbb{E}[X] \ge t) \le e^{-\lambda t + \psi(\lambda)}
   = e^{-(\lambda t - \psi(\lambda))}$.
  Taking the infimum over $\lambda \ge 0$: since $x \mapsto e^{-x}$ is antitone
  and continuous, $\inf_{\lambda \ge 0} e^{-(\lambda t - \psi(\lambda))}
   = e^{-\psi^*(t)}$. This last step is delegated to
  `Antitone.map_csSup_of_continuousAt` on `Real.exp ∘ Neg.neg`. The two
  `-- LEAN-ONLY` side conditions described above guard the formalisation; there
  is no book-vs-Lean constant deviation.

**Bibliographic comments.** *Markov's inequality* is classical folklore with no
single seminal paper; it is named after A. A. Markov and generalises the bound
of his teacher P. L. Chebyshev (Chebyshev, "Des valeurs moyennes", *Journal de
mathématiques pures et appliquées*, 1867). The *Chernoff bound* — optimising the
exponential Markov inequality over the tilt parameter $\lambda$ — originates with
H. Chernoff, "A measure of asymptotic efficiency for tests of a hypothesis based
on the sum of observations", *Annals of Mathematical Statistics* **23** (1952),
no. 4, 493–507; the exponential-rate / large-deviation argument appears there in
the analysis of error probabilities (Chernoff credits the key inequality to
Herman Rubin). The Legendre-dual rate function $\psi^*$ is the same object that
governs Cramér's large-deviation theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Markov's inequality -/

/-- **Markov's inequality** (Lu-BDA §4.2, "Markov"): for a nonnegative
integrable random variable `X` and `t > 0`,
`μ{X ≥ t} ≤ (∫ X ∂μ) / t`.

The book's statement uses the strict event `X > t`; the inequality `≤` is
preserved by enlarging the event to `X ≥ t`, so the form proved here is
strictly stronger.

Delegates to `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`. -/
theorem markov
    {X : Ω → ℝ} {μ : Measure Ω} {t : ℝ}
    -- USER-INPUT: X is a.e. nonneg; Lu-BDA §4.2 (Markov)
    (hX_nn : 0 ≤ᵐ[μ] X)
    -- USER-INPUT: E[X] is finite; Lu-BDA §4.2 (Markov)
    (hX_int : Integrable X μ)
    -- USER-INPUT: t > 0 so we can divide by t; Lu-BDA §4.2 (Markov)
    (ht : 0 < t) :
    μ.real {ω | t ≤ X ω} ≤ (∫ x, X x ∂μ) / t := by
  have h := mul_meas_ge_le_integral_of_nonneg hX_nn hX_int t
  rw [le_div_iff₀ ht, mul_comm]
  exact h

/-! ### Chernoff bound -/

/-- Centered log-MGF (cumulant generating function)
`ψ(λ) = log E[exp(λ (X − E[X]))]`, expressed via Mathlib's `cgf` on the
centered variable. -/
noncomputable def psi (X : Ω → ℝ) (μ : Measure Ω) (lam : ℝ) : ℝ :=
  cgf (fun ω => X ω - ∫ x, X x ∂μ) μ lam

/-- Fenchel–Legendre dual of the centered log-MGF restricted to nonneg `λ`:
`ψ*(t) = ⨆_{λ ≥ 0} (λ t − ψ(λ))`.

If the set `{λ t − ψ(λ) : λ ≥ 0}` is unbounded above (a degenerate case where
`ψ` decays sub-linearly in `λ`), the real-valued `iSup` returns its junk value
`0`, in which case the bound `exp(−ψ*(t)) = 1` is vacuously true; the
`BddAbove` hypothesis on `chernoff` rules this case out and recovers the
textbook meaning of the sup. -/
noncomputable def psiStar (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  ⨆ lam : {lam : ℝ // 0 ≤ lam}, lam.val * t - psi X μ lam.val

/-- **Chernoff bound** (Lu-BDA §4.2, Theorem 4.4 (Chernoff Bound)): with the centered log-MGF
`ψ(λ) = log E[exp(λ (X − E[X]))]` and its Legendre dual
`ψ*(t) = ⨆_{λ ≥ 0} (λ t − ψ(λ))`,
`P(X − E[X] ≥ t) ≤ exp(−ψ*(t))`.

The book states this for `t ≥ 0`; the Lean form is strictly stronger as it
makes no sign assumption on `t` (for `t < 0` the bound may be vacuous because
`ψ*(t)` can be small or non-positive, but it is still valid).

Proof sketch: for each `λ ≥ 0`, Mathlib's `measure_ge_le_exp_cgf` (Markov on
the exponential moment) gives
`P(X − E X ≥ t) ≤ exp(−λ t + ψ(λ)) = exp(−(λ t − ψ(λ)))`. Take the
infimum over `λ ≥ 0`; since `x ↦ exp(−x)` is antitone and continuous,
`inf_{λ ≥ 0} exp(−(λ t − ψ(λ))) = exp(−ψ*(t))`. -/
theorem chernoff
    {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] {t : ℝ}
    -- USER-INPUT: MGF of the centered variable is finite on [0, ∞);
    -- Lu-BDA §4.2 (Chernoff) (the book uses pointwise Markov which silently
    -- assumes the same MGF finiteness)
    (hInt : ∀ lam, 0 ≤ lam →
      Integrable (fun ω => Real.exp (lam * (X ω - ∫ x, X x ∂μ))) μ)
    -- LEAN-ONLY: real-valued `iSup` over an unbounded set returns 0 (junk),
    -- which would make `exp(−ψ*) = 1` and the bound vacuous; assuming
    -- `BddAbove` aligns `psiStar` with the textbook sup.
    (hBdd : BddAbove (Set.range (fun lam : {lam : ℝ // 0 ≤ lam} =>
      lam.val * t - psi X μ lam.val))) :
    μ.real {ω | t ≤ X ω - ∫ x, X x ∂μ} ≤ Real.exp (-psiStar X μ t) := by
  -- Notation: `Y` is the centered variable.
  set Y : Ω → ℝ := fun ω => X ω - ∫ x, X x ∂μ with hYdef
  -- Set whose supremum is `ψ*(t)`.
  set S : Set ℝ := Set.range (fun lam : {lam : ℝ // 0 ≤ lam} =>
    lam.val * t - psi X μ lam.val) with hSdef
  -- `S` is nonempty (take `λ = 0`).
  have hSne : S.Nonempty := ⟨_, ⟨⟨0, le_refl 0⟩, rfl⟩⟩
  -- Per-`λ` Markov-on-the-MGF bound.
  have hPerLam : ∀ x ∈ S, μ.real {ω | t ≤ Y ω} ≤ Real.exp (-x) := by
    rintro x ⟨⟨lam, hlam⟩, rfl⟩
    have hmark := measure_ge_le_exp_cgf (X := Y) (μ := μ) t hlam (hInt lam hlam)
    have hrw : -(lam * t - psi X μ lam) = -lam * t + cgf Y μ lam := by
      change -(lam * t - cgf Y μ lam) = -lam * t + cgf Y μ lam
      ring
    rw [hrw]
    exact hmark
  -- Apply `Antitone.map_csSup_of_continuousAt` to `x ↦ exp(−x)`.
  have hAnt : Antitone (fun x : ℝ => Real.exp (-x)) := by
    intro a b hab
    exact Real.exp_le_exp.mpr (neg_le_neg hab)
  have hCont : ContinuousAt (fun x : ℝ => Real.exp (-x)) (sSup S) := by
    fun_prop
  have hMap : Real.exp (-(sSup S)) = sInf ((fun x : ℝ => Real.exp (-x)) '' S) :=
    hAnt.map_csSup_of_continuousAt hCont hSne hBdd
  -- `psiStar` = `sSup S` by definition of `iSup`.
  have hpsiStar : psiStar X μ t = sSup S := rfl
  -- Image is nonempty and bounded below (by `0`).
  have hIne : ((fun x : ℝ => Real.exp (-x)) '' S).Nonempty := hSne.image _
  -- Per-`λ` bound translates to "`μ.real {…}` is a lower bound on the image".
  have hLB : ∀ y ∈ ((fun x : ℝ => Real.exp (-x)) '' S),
      μ.real {ω | t ≤ Y ω} ≤ y := by
    rintro y ⟨x, hx, rfl⟩
    exact hPerLam x hx
  calc
    μ.real {ω | t ≤ Y ω}
        ≤ sInf ((fun x : ℝ => Real.exp (-x)) '' S) := le_csInf hIne hLB
    _ = Real.exp (-sSup S) := hMap.symm
    _ = Real.exp (-psiStar X μ t) := by rw [hpsiStar]

end StatLean.ConcentrationInequalities
