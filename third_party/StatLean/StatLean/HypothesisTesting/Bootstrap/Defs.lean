module
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Bootstrap — core data model

The bootstrap estimates the sampling distribution `J_n(P)` of a root
`R_n(X_1,…,X_n; θ(P))` by the plug-in `J_n(P̂_n)`, where `P̂_n` is the empirical
measure of the observed sample. The area's consistency theory is phrased over
**sequence classes**: a set `C_P` of sequences of laws along which the sampling CDFs
converge to a common continuous limit, membership of the (random) empirical sequence in
`C_P` being the only stochastic ingredient. This file fixes the deterministic
carriers:

* `empiricalMeasure x` — the empirical measure `n⁻¹ ∑ δ_{xᵢ}` of a finite sample;
* `supCDFDist F G` — the Kolmogorov (sup) distance between two CDFs;
* `cdfPseudoInverse F p` — the generalized inverse (quantile) `inf {t | p ≤ F t}`.

The sampling-CDF field `J : ℕ → Measure 𝓧 → ℝ → ℝ` and the class
`C_P : Set (ℕ → Measure 𝓧)` are theorem-level *data*, supplied with their defining
properties as hypotheses; no measurability in the measure argument is ever assumed.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 18 (Bootstrap and
Subsampling Methods), §18.3 (Bootstrap Sampling Distributions), the bootstrap sampling
distribution and the empirical-measure resampling scheme. (`TSH4 §18.3`.)

**Proof formalization notes.**
* `empiricalMeasure` is a probability measure for `n > 0` (proved where used); `n = 0`
  gives the zero measure (junk, guarded by side conditions).
* `supCDFDist` is a real supremum; for genuine CDFs it lies in `[0,1]`, and statements
  restrict to that case, so the unbounded-supremum junk (`sSup ∅`-style) is never hit.
* `cdfPseudoInverse` uses `sInf` with the standard junk conventions of `Real.sInf`
  (empty set ↦ 0); quantile statements carry the nonemptiness side conditions.

**Bibliographic comments.** The bootstrap is due to B. Efron ("Bootstrap methods:
another look at the jackknife," *Ann. Statist.* **7** (1979), 1–26); its first
consistency theory to P. J. Bickel and D. A. Freedman ("Some asymptotic theory for the
bootstrap," *Ann. Statist.* **9** (1981), 1196–1217) and K. Singh ("On the asymptotic
accuracy of Efron's bootstrap," *Ann. Statist.* **9** (1981), 1187–1195); the
sequence-class formulation of consistency follows R. Beran ("Bootstrap methods in
statistics," *Jahresber. Deutsch. Math.-Verein.* **86** (1984), 14–30) and
D. N. Politis, J. P. Romano, M. Wolf, *Subsampling*, Springer, 1999. Higher-order
accuracy is treated in P. Hall, *The Bootstrap and Edgeworth Expansion*, Springer,
1992.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- The **empirical measure** `n⁻¹ ∑ᵢ δ_{xᵢ}` of a finite sample (zero measure when
`n = 0`). -/
noncomputable def empiricalMeasure {n : ℕ} (x : Fin n → 𝓧) : Measure 𝓧 :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (x i)

/-- The **Kolmogorov (sup-CDF) distance** `sup_t |F t − G t|`. -/
noncomputable def supCDFDist (F G : ℝ → ℝ) : ℝ :=
  ⨆ t : ℝ, |F t - G t|

/-- The **generalized inverse (quantile function)** of a CDF-like function:
`F⁻¹(p) = inf {t | p ≤ F t}`. -/
noncomputable def cdfPseudoInverse (F : ℝ → ℝ) (p : ℝ) : ℝ :=
  sInf {t : ℝ | p ≤ F t}

end StatLean.HypothesisTesting
