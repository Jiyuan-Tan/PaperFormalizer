module
public import StatLean.ConcentrationInequalities.McDiarmid.DoobDecomposition

@[expose] public section

/-!
# McDiarmid's bounded-differences inequality

Let $X = (X_0, \dots, X_{n-1})$ be $n$ independent random variables and let
$f$ be a real-valued function satisfying the **bounded-differences condition**
with constants $c_0, \dots, c_{n-1} \ge 0$: changing the $k$-th coordinate of the
argument changes the value of $f$ by at most $c_k$, i.e.
$$\bigl|f(x) - f(x_{-k}, y)\bigr| \le c_k \quad\text{for all } x \text{ and all } y,$$
where $(x_{-k}, y)$ denotes $x$ with its $k$-th coordinate replaced by $y$. Then the
centered evaluation $f(X) - \mathbb{E}[f(X)]$ has the Gaussian-style upper tail, for
every $t \ge 0$,
$$\mathbb{P}\bigl(f(X) - \mathbb{E}[f(X)] > t\bigr) \le \exp\!\left(\frac{-2 t^2}{\sum_{k} c_k^2}\right),$$
and the corresponding two-sided form
$$\mathbb{P}\bigl(\bigl|f(X) - \mathbb{E}[f(X)]\bigr| > t\bigr) \le 2\,\exp\!\left(\frac{-2 t^2}{\sum_{k} c_k^2}\right).$$

Two alignments with the Lean statement. First, the book states the bound for $t > 0$; the
Lean statement uses the weaker hypothesis $t \ge 0$, which is strictly stronger (the $t = 0$
case is trivial). Second, the bounded-differences constants are taken nonnegative; this is a
harmless normalization, since a difference bound is vacuous for negative $c_k$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 5 (Sub-exponential Random Variables), §5.1,
Theorem 5.1 (McDiarmid Inequality).

**Proof formalization notes.** The proof is a pure Chernoff bound on the sub-Gaussian MGF
already established in `McDiarmid/DoobDecomposition.lean`:
`mgf_sub_expectation_le` gives `HasSubgaussianMGF (f(X) − E[f(X)]) σ² μ` with proxy
`σ² = ∑ₖ (‖cₖ‖₊/2)² = (∑ₖ cₖ²)/4`. Mathlib's
`ProbabilityTheory.HasSubgaussianMGF.measure_ge_le` then yields the right-tail bound
`μ.real {t ≤ ·} ≤ exp(−t²/(2σ²))`, and `−t²/(2σ²) = −t²/(2·(∑cₖ²)/4) = −2t²/(∑cₖ²)`.
The `μ.real → ENNReal` bridge mirrors `SubGaussian/TailBounds.lean`. For the two-sided
form, `t < |Y|` splits as `t < Y ∨ t < −Y`; the left tail is the right tail of `−Y` via
`HasSubgaussianMGF.neg`, and the two are combined by `measure_union_le`.

The strict inequality `<` on the event is faithful to the book; the brick gives `≤`, and
the slack is absorbed via the inclusion `{t < y} ⊆ {t ≤ y}`. This file rests on the fully
proved `mgf_sub_expectation_le` (DoobDecomposition); the whole McDiarmid chain is
`sorry`-free.

**Bibliographic comments.** The independent bounded-differences inequality is due to
C. McDiarmid, "On the method of bounded differences", in *Surveys in Combinatorics, 1989*
(J. Siemons, ed.), London Mathematical Society Lecture Note Series 141, Cambridge University
Press, 1989, pp. 148–188 (the inequality is stated there as Lemma (1.2)). The underlying
technique — controlling the Doob martingale of $f(X)$ via a martingale exponential bound —
goes back to W. Hoeffding, "Probability inequalities for sums of bounded random variables",
*Journal of the American Statistical Association* **58** (1963), 13–30, and to K. Azuma,
"Weighted sums of certain dependent random variables", *Tôhoku Mathematical Journal* **19**
(1967), 357–367; for this reason the result is often called the Azuma–Hoeffding bounded-
differences inequality.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

section McDiarmid

variable {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {β : Fin n → Type*} [(i : Fin n) → MeasurableSpace (β i)]
  -- LEAN-ONLY: standard-Borel coordinate spaces; threaded to `mgf_sub_expectation_le`.
  [∀ i, StandardBorelSpace (β i)] [∀ i, Nonempty (β i)]

/-- The Doob sub-Gaussian proxy `∑ₖ (‖cₖ‖₊/2)²` (an `ℝ≥0`) coerces to `(∑ₖ cₖ²)/4` as a real,
using `‖cₖ‖ = |cₖ| = cₖ` for the nonnegative constants `cₖ`. -/
private lemma coe_doob_proxy (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ((∑ k : Fin n, (‖c k‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = (∑ k : Fin n, c k ^ 2) / 4 := by
  rw [NNReal.coe_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [Real.norm_eq_abs, abs_of_nonneg (hc k)]
  ring

/-- The McDiarmid right-tail exponent rewrite: with proxy `σ² = ∑ₖ (‖cₖ‖₊/2)²`,
`−t²/(2σ²) = −2t²/(∑ₖ cₖ²)`. Holds unconditionally — both sides degenerate to `0`
when `∑ₖ cₖ² = 0` (Lean's `x/0 = 0`). -/
private lemma doob_exp_eq (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) (t : ℝ) :
    Real.exp (-t ^ 2 / (2 * ((∑ k : Fin n, (‖c k‖₊ / 2) ^ 2 : ℝ≥0) : ℝ)))
      = Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2)) := by
  congr 1
  rw [coe_doob_proxy c hc]
  ring

/-- **McDiarmid's bounded-differences inequality** (Lu-BDA Ch5 §5.1, Theorem 5.1
(McDiarmid Inequality)), one-sided upper tail.

For `n` independent random variables `X = (X₀,…,Xₙ₋₁)` and `f` satisfying the
bounded-differences condition with constants `c : Fin n → ℝ`, the centered evaluation has
the upper tail bound, for `0 ≤ t`,

  `μ {ω | t < f(X ω) − ∫ f(X) dμ} ≤ exp(−2 t² / (∑ₖ cₖ²))`.

Proof: Chernoff on the sub-Gaussian MGF `mgf_sub_expectation_le` (proxy `(∑cₖ²)/4`) via
`HasSubgaussianMGF.measure_ge_le`, then `−t²/(2σ²) = −2t²/(∑cₖ²)`. -/
theorem McDiarmid
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences Dᵢf ≤ cᵢ; Lu-BDA §5.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §5.1.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: f(X) integrable; Lu-BDA §5.1 (implicit regularity).
    (hf_int : Integrable (f ∘ allVars X) μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §5.1.
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
  have hsg : HasSubgaussianMGF (fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)
      (∑ k : Fin n, (‖c k‖₊ / 2) ^ 2) μ :=
    mgf_sub_expectation_le X hX f hf c hc hbd hX_indep hf_int
  -- Mathlib Chernoff brick, then rewrite the exponent to the book form.
  have hbrick := hsg.measure_ge_le ht
  rw [doob_exp_eq c hc t] at hbrick
  -- {t < ·} ⊆ {t ≤ ·}; bridge μ.real → ENNReal exactly as in TailBounds.
  have hsub : {ω | t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ⊆ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ} := by
    intro ω hω
    have hω' : t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ := hω
    exact hω'.le
  calc μ {ω | t < f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ≤ μ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ} := measure_mono hsub
    _ ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
        rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
        exact ENNReal.ofReal_le_ofReal hbrick

/-- **McDiarmid's bounded-differences inequality** (Lu-BDA Ch5 §5.1, Theorem 5.1
(McDiarmid Inequality)), two-sided form.

For `0 ≤ t`,

  `μ {ω | t < |f(X ω) − ∫ f(X) dμ|} ≤ 2 · exp(−2 t² / (∑ₖ cₖ²))`.

Proof: `t < |Y|` splits as `t < Y ∨ t < −Y` (`lt_abs`); apply the one-sided Chernoff bound
to `Y := f(X) − E[f(X)]` (right tail) and to `−Y` via `HasSubgaussianMGF.neg` (left tail),
then combine with `measure_union_le`. -/
theorem McDiarmid_abs
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ∀ i : Fin n, Ω → β i) (hX : ∀ i : Fin n, Measurable (X i))
    (f : (Π i : Fin n, β i) → ℝ) (hf : Measurable f)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    -- USER-INPUT: bounded differences Dᵢf ≤ cᵢ; Lu-BDA §5.1.
    (hbd : ∀ k : Fin n, ∀ x : Π i : Fin n, β i, ∀ y : β k,
        |f x - f (Function.update x k y)| ≤ c k)
    -- USER-INPUT: independence of (X i); Lu-BDA §5.1.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: f(X) integrable; Lu-BDA §5.1 (implicit regularity).
    (hf_int : Integrable (f ∘ allVars X) μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §5.1.
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ|}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
  have hsg : HasSubgaussianMGF (fun ω => f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)
      (∑ k : Fin n, (‖c k‖₊ / 2) ^ 2) μ :=
    mgf_sub_expectation_le X hX f hf c hc hbd hX_indep hf_int
  -- Right tail.
  have hbrickR := hsg.measure_ge_le ht
  rw [doob_exp_eq c hc t] at hbrickR
  -- Left tail via negation.
  have hbrickL := hsg.neg.measure_ge_le ht
  rw [doob_exp_eq c hc t] at hbrickL
  simp only [Pi.neg_apply] at hbrickL
  -- Bridge each tail μ.real → ENNReal.
  have hR : μ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hbrickR
  have hL : μ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)}
      ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal hbrickL
  have hexp_nn : 0 ≤ Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2)) := (Real.exp_pos _).le
  have hsub : {ω | t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ|}
      ⊆ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
        ∪ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)} := by
    intro ω hω
    have hω' : t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ| := hω
    rcases lt_abs.mp hω' with h | h
    · exact Or.inl h.le
    · exact Or.inr h.le
  calc μ {ω | t < |f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ|}
      ≤ μ ({ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
            ∪ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)}) := measure_mono hsub
    _ ≤ μ {ω | t ≤ f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ}
          + μ {ω | t ≤ -(f (allVars X ω) - ∫ ω', f (allVars X ω') ∂μ)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2)))
          + ENNReal.ofReal (Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := add_le_add hR hL
    _ = ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / (∑ k : Fin n, c k ^ 2))) := by
        rw [← ENNReal.ofReal_add hexp_nn hexp_nn]
        ring_nf

end McDiarmid

end StatLean.ConcentrationInequalities
