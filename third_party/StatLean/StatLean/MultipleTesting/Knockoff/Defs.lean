module
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Knock-off score — definition

Concept-layer data model for the knock-off filter.

A **knock-off score** is a vector of feature statistics $W = (W_1, \dots, W_d)$, $W_j : \Omega \to
\mathbb{R}$, for which large positive values flag relevant features. Its defining distributional
property is the *coin-flip property* for null features: conditional on the magnitudes
$\lvert W_1\rvert, \dots, \lvert W_d\rvert$, the signs of the null coordinates
$\{\operatorname{sign} W_j : j \in H_0\}$ are independent and identically distributed fair coins,
each $\pm 1$ with probability $\tfrac12$, and independent of all observed data. We formalize exactly
that property — the only thing the FDR-control proof consumes — as three fields on `KnockoffScore`:

* `signs_iIndep`     — the null signs $\{\operatorname{sign} W_j : j \in H_0\}$ are jointly
  independent;
* `signs_fair`       — each null sign is fair, $\Pr(W_j \ge 0) = \tfrac12$;
* `signs_indep_outer` — the null sign vector is independent of the *outer data* (the magnitudes
  $\lvert W_1\rvert, \dots, \lvert W_d\rvert$ together with the non-null signs), the data the count
  filtration conditions on.

Together these say: *conditional on the magnitudes and the non-null signs, the null signs are i.i.d.
$\mathrm{Ber}(\tfrac12)$* (Definition 21.1 (Knock-Off Score), condition 3). The book's antisymmetry (condition 1)
is an upstream property of the *construction* of $W$ that guarantees this coin-flip property;
condition 2 ($W_j \stackrel{d}{=} -W_j$ for nulls) is a consequence of the three fields. The
procedure ($S_\pm$, $\widehat{\mathrm{FDP}}$, the data-dependent threshold $t^*$, the rejection set)
lives in the assembly file `Knockoff.lean`.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off), §21.3 (Knock-Off), Definition 21.1 (Knock-Off
Score), condition 3. Equivalently — and this is the original source of the coin-flip property —
E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University, 2023
(knockoffs lecture, "i.i.d. sign" lemma).

**Proof formalization notes.** We keep only the distributional consequence the supermartingale
argument actually uses, rather than the antisymmetric *construction* of $W$. The third field
`signs_indep_outer` strengthens an earlier `signs_indep_mag` (which asserted independence from the
magnitudes only): the null sign vector is required independent of the magnitudes **together with**
the non-null signs, encoded — as in `cproc` — by the padded vector
`fun j => if j ∈ H₀ then 0 else sgn Wⱼ`. This is the genuine model-X knock-off property (null signs
are fresh fair coins independent of all observed data) and is exactly what the exchangeable
supermartingale step (`count_condExp`) consumes; conditioning only on the magnitudes is too weak.
`sgnReal` uses the convention $\operatorname{sign}(W_j) = +1$ when $W_j \ge 0$ and $-1$ otherwise;
under the no-ties assumption $W_j \ne 0$ a.s. (supplied as a theorem hypothesis downstream) this
agrees with the genuine sign. The `meas` field records that each $W_j$ is measurable, needed for the
natural filtration / adaptedness / integrability machinery in `Knockoff/Supermartingale.lean`.

**Bibliographic comments.** The fixed-design knock-off filter and its key distributional engine — for
null features, the contrast statistics $W_j$ are symmetric about zero with signs that are i.i.d.
fair coin flips, independent of the magnitudes — originate with R. F. Barber and E. J. Candès,
"Controlling the false discovery rate via knockoffs," *Annals of Statistics* **43**(5) (2015),
2055–2085 (the i.i.d.-sign property is their Lemma 1). The model-X generalization formalized here,
in which the null signs are independent of all observed data rather than of a single sufficient
statistic, is due to E. Candès, Y. Fan, L. Janson and J. Lv, "Panning for gold: 'model-X' knockoffs
for high-dimensional controlled variable selection," *Journal of the Royal Statistical Society:
Series B* **80**(3) (2018), 551–577.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- Real-valued sign of `Wⱼ`: `+1` if `Wⱼ ≥ 0`, else `−1` (Lu-BDA §21.3). Under the no-ties
assumption `Wⱼ ≠ 0` a.s. (supplied as a theorem hypothesis) this is the genuine sign. -/
noncomputable def sgnReal (W : Fin d → Ω → ℝ) (j : Fin d) (ω : Ω) : ℝ :=
  if 0 ≤ W j ω then 1 else -1

/-- `KnockoffScore W H₀ μ`: the statistic `W : Fin d → Ω → ℝ` is a knock-off score for the true
null set `H₀` under `μ` (Lu-BDA §21.3, Definition 21.1 (Knock-Off Score) condition 3) — the null
signs are i.i.d. fair coins given the magnitudes. -/
structure KnockoffScore (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (μ : Measure Ω) : Prop where
  /-- Constitutive (Lu-BDA §21.3, Definition 21.1 (Knock-Off Score) cond. 3): the null signs
  `{sign Wⱼ : j ∈ H₀}` are jointly independent. -/
  signs_iIndep : iIndepFun (fun (j : H₀) (ω : Ω) => sgnReal W (j : Fin d) ω) μ
  /-- Constitutive (Lu-BDA §21.3, Definition 21.1 (Knock-Off Score) cond. 3): each null sign is a
  fair coin, `P(Wⱼ ≥ 0) = ½` (with a probability measure). -/
  signs_fair : ∀ j ∈ H₀, μ {ω | 0 ≤ W j ω} = 1 / 2
  /-- Constitutive (Lu-BDA §21.3, Definition 21.1 (Knock-Off Score) cond. 3): the null sign vector
  is independent of the *outer data* — the magnitude vector `(|Wⱼ|)ⱼ` **together with the non-null signs** (encoded, as in
  `cproc`, by the padded vector `fun j => if j ∈ H₀ then 0 else sgn Wⱼ`). This is the data the count
  filtration `𝒢rev` conditions on; with `signs_iIndep`/`signs_fair` it gives: conditional on the
  magnitudes and non-null signs, the null signs are i.i.d. `Ber(½)` — exactly what the exchangeable
  supermartingale step (`count_condExp`) consumes. Strengthens the former `signs_indep_mag` (⊥
  magnitudes only); ⊥ (magnitudes ⊕ non-null signs) is the genuine model-X knock-off property (null
  signs are fresh fair coins independent of all observed data). -/
  signs_indep_outer :
    IndepFun (fun ω (j : H₀) => sgnReal W (j : Fin d) ω)
      (fun ω => ((fun j => |W j ω|), (fun j => if j ∈ H₀ then (0 : ℝ) else sgnReal W j ω)))
      μ
  /-- Constitutive (Lu-BDA §21.3, Definition 21.1 (Knock-Off Score)): a knock-off *score* is a
  statistic, so each `Wⱼ` is measurable. Needed for the martingale construction (natural filtration, adaptedness,
  integrability, conditional expectation) in `Knockoff/Supermartingale.lean`. -/
  meas : ∀ j, Measurable (W j)

end StatLean.MultipleTesting
