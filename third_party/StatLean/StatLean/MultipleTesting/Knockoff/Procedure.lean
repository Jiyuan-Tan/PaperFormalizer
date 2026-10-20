module
public import StatLean.MultipleTesting.FDP.Defs
public import StatLean.MultipleTesting.Knockoff.Defs

@[expose] public section

/-!
# Knock-off procedure — definitions

The deterministic data of the knock-off filter at level $\alpha$, over a knock-off score vector
$W = (W_1,\dots,W_d)$ (a measurable map $W_j : \Omega \to \mathbb{R}$ for each coordinate $j$) and
a true-null index set $H_0 \subseteq \{1,\dots,d\}$. For a threshold level $t \ge 0$ define the two
sign-split selection sets
$$ S^+(t) = \{\, j : |W_j| \ge t,\ W_j > 0 \,\}, \qquad S^-(t) = \{\, j : |W_j| \ge t,\ W_j < 0 \,\}, $$
their restrictions to the true nulls $V_+(t) = \#\bigl(S^+(t) \cap H_0\bigr)$ and
$V_-(t) = \#\bigl(S^-(t) \cap H_0\bigr)$, and the **estimated false-discovery proportion**
$$ \widehat{\mathrm{FDP}}(t) = \frac{\#S^-(t) + 1}{\#S^+(t) \vee 1}, \qquad a \vee b := \max\{a,b\}. $$
The knock-off filter then selects the **data-dependent threshold**
$$ t^* = \min\bigl\{\, t \in \{|W_1|,\dots,|W_d|\} : \widehat{\mathrm{FDP}}(t) \le \alpha \,\bigr\} $$
and **rejects** the null $H_{0j}$ exactly when $j \in S^+(t^*)$.

The "$+1$" in the numerator of $\widehat{\mathrm{FDP}}$ is the more conservative **knock-off+**
form of the filter (the variant that controls the FDR exactly in finite samples), not the plain
knock-off estimate $\#S^-(t) / (\#S^+(t) \vee 1)$.

This file provides the shared **concept layer** of definitions (`Splus`, `Sminus`, `Vplus`,
`Vminus`, `FDPhat`, `tStar`, `knockoffRejects`) reused by the knock-off assembly files (`FdpBound`,
`Initial`, `Supermartingale`, the final `Knockoff`). It is theorem-agnostic and laptop-owned.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off), §21.3 (Knock-Off): Definition 21.1
(Knock-Off Score), the display
$\widehat{\mathrm{FDP}}(t) = (\#S^-(t)+1)/(\#S^+(t)\vee 1)$, and the threshold rule
$t^* = \arg\min_t \{ \widehat{\mathrm{FDP}}(t) \le \alpha \}$ with rejection set $S^+(t^*)$, whose
exact finite-sample FDR control is Theorem 21.2 (Knock-Off). (The declarations are tagged
`Lu-BDA §21.3`; the source file `chapters/chapter19.tex` is scrambled and compiles to Chapter 21 of
the book.)

**Proof formalization notes.** This is a definitions-only concept file, so the "proof" content is
the modeling fidelity of the encodings:

* $S^+, S^-, V_+, V_-, \widehat{\mathrm{FDP}}$ transcribe the book displays verbatim, with the
  natural-number cardinalities cast to $\mathbb{R}$ inside `FDPhat` so the ratio is real-valued and
  the $\vee 1$ guards a zero denominator.
* The candidate threshold grid is the finite set of observed magnitudes $\{|W_j|\}_j$ (the book's
  $\min_t$ over the realized score magnitudes), implemented as `Finset.univ.image (|W · ω|)`.
* **Degenerate-case convention for `tStar`.** When no candidate magnitude achieves
  $\widehat{\mathrm{FDP}}(t) \le \alpha$, `tStar` returns a value strictly **above every magnitude**,
  $1 + \sum_j |W_j|$, so that $S^+(t^*) = S^-(t^*) = \varnothing$ — nothing is rejected, matching
  `knockoffRejects`, and the null ratio $V_+(t^*)/(1 + V_-(t^*)) = 0$. This realizes Barber &
  Candès's "$T = +\infty$ if no such $t$ exists" convention with a finite surrogate. The earlier
  `0` fallback left `knockoffRejects = ∅` while $V_+(0)/(1+V_-(0)) \ne 0$, an inconsistency that
  broke the order-statistic bridge `ratio_eq_Yproc_hittingIdx`; see the `tStar` docstring.

**Bibliographic comments.** The knock-off filter originates with R. F. Barber and E. J. Candès,
"Controlling the false discovery rate via knockoffs," *The Annals of Statistics* **43**(5):
2055–2085, 2015. The objects formalized here are their Definition 1 (Knockoff) and Definition 2
(Knockoff+): the plain knock-off threshold is eq. (1.8),
$T = \min\{ t \in \mathcal{W} : \#\{j : W_j \le -t\} / (\#\{j : W_j \ge t\} \vee 1) \le q \}$, and the
knock-off+ threshold is eq. (1.9),
$T = \min\{ t \in \mathcal{W} : (1 + \#\{j : W_j \le -t\}) / (\#\{j : W_j \ge t\} \vee 1) \le q \}$,
with selection set $\hat{S} = \{ j : W_j \ge T \}$. The `+1`-numerator `FDPhat` used here is the
knock-off+ form, whose exact finite-sample FDR control is their Theorem 2 (the plain knock-off form
controls only the modified FDR, their Theorem 1; their estimate $\widehat{\mathrm{FDP}}$ appears in
eq. (1.11)). Lu's *Big Data Analysis* presents this filter as textbook material; the original
research result is the Barber–Candès paper.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- `S⁺(t)`: indices with magnitude `≥ t` and positive sign (Lu-BDA §21.3). -/
noncomputable def Splus (W : Fin d → Ω → ℝ) (t : ℝ) (ω : Ω) : Finset (Fin d) :=
  Finset.univ.filter (fun j => t ≤ |W j ω| ∧ 0 < W j ω)

/-- `S⁻(t)`: indices with magnitude `≥ t` and negative sign (Lu-BDA §21.3). -/
noncomputable def Sminus (W : Fin d → Ω → ℝ) (t : ℝ) (ω : Ω) : Finset (Fin d) :=
  Finset.univ.filter (fun j => t ≤ |W j ω| ∧ W j ω < 0)

/-- `V₊(t) = #{ j ∈ H₀ : j ∈ S⁺(t) }`, the number of *null* positives above threshold `t`. -/
noncomputable def Vplus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) : ℕ :=
  ((Splus W t ω) ∩ H₀).card

/-- `V₋(t) = #{ j ∈ H₀ : j ∈ S⁻(t) }`, the number of *null* negatives above threshold `t`. -/
noncomputable def Vminus (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (t : ℝ) (ω : Ω) : ℕ :=
  ((Sminus W t ω) ∩ H₀).card

/-- Estimated FDP `FDPhat(t) = (#S⁻(t) + 1)/(#S⁺(t) ∨ 1)` (Lu-BDA §21.3). -/
noncomputable def FDPhat (W : Fin d → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ((Sminus W t ω).card + 1 : ℝ) / max ((Splus W t ω).card : ℝ) 1

/-- The knock-off threshold `t* = min{ t ∈ {|Wⱼ|} : FDPhat(t) ≤ α }` (Lu-BDA §21.3). In the
degenerate case (no candidate magnitude achieves `FDPhat ≤ α`) we return a value strictly **above
every magnitude**, `1 + ∑ⱼ |Wⱼ|`, so that `S⁺(t*) = S⁻(t*) = ∅` — i.e. nothing is rejected, matching
`knockoffRejects`, and the null ratio `V₊(t*)/(1+V₋(t*)) = 0`. (The former `0` convention left
`knockoffRejects = ∅` while `V₊(0)/(1+V₋(0)) ≠ 0`, an inconsistency that broke the order-statistic
bridge `ratio_eq_Yproc_hittingIdx`.) -/
noncomputable def tStar (W : Fin d → Ω → ℝ) (α : ℝ) (ω : Ω) : ℝ :=
  let cands := (Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α)
  if h : cands.Nonempty then cands.min' h else 1 + ∑ j, |W j ω|

/-- Knock-off rejection set: `S⁺(t*)` (Lu-BDA §21.3). In the degenerate case (no candidate
threshold achieves `FDPhat ≤ α`) nothing is rejected. -/
noncomputable def knockoffRejects (W : Fin d → Ω → ℝ) (α : ℝ) (ω : Ω) : Finset (Fin d) :=
  let cands := (Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α)
  if h : cands.Nonempty then Splus W (cands.min' h) ω else ∅

end StatLean.MultipleTesting
