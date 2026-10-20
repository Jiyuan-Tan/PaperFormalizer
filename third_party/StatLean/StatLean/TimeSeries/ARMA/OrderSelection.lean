module
public import StatLean.TimeSeries.ARMA.Likelihood
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Order determination: KL information and the AIC family (FY §3.4)

* **Kullback–Leibler information** of a candidate density `g` against the truth `f`
  (FY eq. (3.15)) and its **nonnegativity** — the in-text Jensen proof (a clean
  self-contained target);
* the **AIC** (3.17)/(3.18), **AICC** (3.19), **FPE**, and **BIC** (3.23)/(3.24)
  criteria for ARMA order selection, defined on the profiled likelihood criterion of
  `ARMA/Likelihood.lean` with FY's penalties;
* the **Taylor equivalence** `AICC = AIC + O(1/T)`-form (in-text; the FPE display
  absorbs an additive constant, harmless for argmin);
* literature DEBTS: the Akaike bias approximation `≈ p_m/T` (Akaike 1973) — the book
  cites it without proof. BIC consistency (Hannan 1980) was carried here as a debt over
  two sorried residues and has been removed; see **Removed** below.

**Removed (2026-08-10, user directive).** The BIC-consistency assembly — the module's two
sorried residues, the headline they were assembled into, and the two `private` helpers used
only by that headline — was deleted. The criterion definitions (`armaAIC`, `armaAICC`,
`armaBIC`, `armaBICmin`), the KL apparatus and the Taylor equivalence are untouched and
remain proved.
* `bic_underfit_residue` — residue (U): asserted that each *underfitting* grid cell
  (`p < p₀` or `q < q₀`) has selection probability `→ 0`, the contrast-gap mechanism.
* `bic_overfit_residue` — residue (O): the same for each *overfitting* cell
  (`p₀ ≤ p`, `q₀ ≤ q`, `(p,q) ≠ (p₀,q₀)`), the penalty-vs-likelihood-ratio race.
* `bic_consistency_debt` — the headline (Hannan 1980; FY §3.4.3): a measurable
  BIC-minimizing order selection over a fixed grid containing `(p₀, q₀)` picks the true
  orders with probability `→ 1`. Proved from (U) and (O), hence deleted with them.
* `measurableSet_sel`, `tendsto_sel_of_cells` (both `private`, both **proved**) — the
  measurability of a selection cell and the grid union bound reducing the headline to the
  cells. They had no other consumer.

Recover from `bdc8143f`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.4,
eqs. (3.15)–(3.24) (pp. 99–109). (`FY §3.4`.)

**Bibliographic comments.** KL information: Kullback & Leibler (1951). AIC: Akaike
(1973, 2nd Int. Symp. Information Theory); AICC: Hurvich & Tsai (1989); FPE: Akaike
(1969); BIC: Schwarz (1978) and Akaike (1977); BIC consistency for ARMA orders:
Hannan (1980, Ann. Statist.).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- **Kullback–Leibler information** (FY eq. (3.15)) of a candidate density `g`
relative to the true density `f`, both w.r.t. Lebesgue on ℝ^d modeled as a σ-finite
measure `ν`: `KL(f, g) = ∫ f log(f/g) dν` (junk under non-integrability, by the
integral convention). -/
noncomputable def klInfo {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f g : α → ℝ) : ℝ :=
  ∫ v, f v * Real.log (f v / g v) ∂ν

/-- **FY §3.4.1 (Jensen)**: the KL information is nonnegative for probability
densities: if `f, g ≥ 0` integrate to `1` against `ν` and `g > 0` on `{f > 0}`, then
`KL(f, g) ≥ 0`. In-text proof: `−log` is convex, Jensen against the probability
measure `f dν`. -/
theorem klInfo_nonneg {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [SigmaFinite ν] {f g : α → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ v, 0 ≤ f v) (hg0 : ∀ v, 0 ≤ g v)
    -- USER-INPUT: probability densities; FY §3.4.1
    (hf1 : ∫ v, f v ∂ν = 1) (hg1 : ∫ v, g v ∂ν = 1)
    -- USER-INPUT: absolute continuity on the support; FY §3.4.1 (implicit)
    (hsupp : ∀ v, 0 < f v → 0 < g v)
    -- LEAN-ONLY: integrability of the KL integrand (finite KL); junk otherwise
    (hint : Integrable (fun v => f v * Real.log (f v / g v)) ν) :
    0 ≤ klInfo ν f g := by
  -- Both densities are integrable: a non-integrable function has integral `0 ≠ 1`.
  have hfi : Integrable f ν := by
    by_contra h
    rw [integral_undef h] at hf1
    exact zero_ne_one hf1
  have hgi : Integrable g ν := by
    by_contra h
    rw [integral_undef h] at hg1
    exact zero_ne_one hg1
  -- The pointwise comparison `f − g ≤ f log(f/g)`, i.e. `log x ≤ x − 1` at `x = g/f`.
  have hkey : ∀ v, f v - g v ≤ f v * Real.log (f v / g v) := by
    intro v
    rcases eq_or_lt_of_le (hf0 v) with h | h
    · -- `f v = 0`: the integrand vanishes (`0 · log` junk included) and `−g v ≤ 0`.
      rw [← h]
      simp only [zero_sub, zero_mul, neg_nonpos]
      exact hg0 v
    · have hgv : 0 < g v := hsupp v h
      have hlog : Real.log (g v / f v) ≤ g v / f v - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hneg : Real.log (f v / g v) = -Real.log (g v / f v) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      rw [hneg]
      have h2 : f v * (1 - g v / f v) ≤ f v * (-Real.log (g v / f v)) :=
        mul_le_mul_of_nonneg_left (by linarith) (le_of_lt h)
      calc f v - g v = f v * (1 - g v / f v) := by field_simp
        _ ≤ _ := h2
  -- Integrate: `KL ≥ ∫ (f − g) = 1 − 1 = 0`.
  have hcomp : ∫ v, (f v - g v) ∂ν ≤ ∫ v, f v * Real.log (f v / g v) ∂ν :=
    integral_mono (hfi.sub hgi) hint hkey
  rw [integral_sub hfi hgi, hf1, hg1] at hcomp
  simpa [klInfo] using hcomp

/-- **AIC** (FY eq. (3.18), profiled form): `T·ℓ*(b, a) + 2(p + q)` — stated as a
definition on the profiled criterion; the `argmin` semantics live with the
estimator hypotheses of the consumers. -/
noncomputable def armaAIC {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) {T : ℕ}
    (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * armaProfileCriterion b a x + 2 * ((p : ℝ) + (q : ℝ))

/-- **AICC** (FY eq. (3.19), Hurvich–Tsai small-sample correction):
`T·ℓ* + 2(p+q)T/(T − p − q − 1)`. -/
noncomputable def armaAICC {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) {T : ℕ}
    (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * armaProfileCriterion b a x
    + 2 * ((p : ℝ) + (q : ℝ)) * (T : ℝ) / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1)

/-- **BIC** (FY eq. (3.23)): `T·ℓ* + (p + q)·log T`. -/
noncomputable def armaBIC {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) {T : ℕ}
    (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * armaProfileCriterion b a x + ((p : ℝ) + (q : ℝ)) * Real.log T

/-- **Taylor equivalence** (FY §3.4.3, in-text): the AICC and AIC penalties differ by
`O(1/T)` uniformly over bounded orders: for `p + q ≤ m` and `T ≥ 2(m + 1)`,
`|armaAICC − armaAIC| ≤ 2(m + 1)²·2/T`-shaped bound. Stated with the explicit
constant `4(m+1)²/T`. -/
theorem armaAICC_sub_armaAIC_le {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) {m : ℕ}
    (hm : p + q ≤ m) (hT : 2 * (m + 1) ≤ T) :
    |armaAICC b a x - armaAIC b a x| ≤ 4 * ((m : ℝ) + 1) ^ 2 / T := by
  have hm' : (p : ℝ) + (q : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hT' : 2 * ((m : ℝ) + 1) ≤ (T : ℝ) := by exact_mod_cast hT
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hTpos : (0 : ℝ) < (T : ℝ) := by linarith
  -- `p + q + 1 ≤ m + 1 ≤ T/2`, so the AICC denominator is at least `T/2`.
  have hden : (T : ℝ) / 2 ≤ (T : ℝ) - (p : ℝ) - (q : ℝ) - 1 := by linarith
  have hdenpos : (0 : ℝ) < (T : ℝ) - (p : ℝ) - (q : ℝ) - 1 := by linarith
  -- The penalties differ by `2(p+q)(p+q+1)/(T − p − q − 1)`.
  have hdiff : armaAICC b a x - armaAIC b a x
      = 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
        / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1) := by
    simp only [armaAICC, armaAIC]
    field_simp
    ring
  rw [hdiff, abs_of_nonneg (by positivity)]
  have h1 : 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
      ≤ 2 * ((m : ℝ) + 1) ^ 2 := by nlinarith
  have h2 : 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
        / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1)
      ≤ 2 * ((m : ℝ) + 1) ^ 2 / ((T : ℝ) / 2) := by
    gcongr
  calc 2 * ((p : ℝ) + (q : ℝ)) * (((p : ℝ) + (q : ℝ)) + 1)
        / ((T : ℝ) - (p : ℝ) - (q : ℝ) - 1)
      ≤ 2 * ((m : ℝ) + 1) ^ 2 / ((T : ℝ) / 2) := h2
    _ = 4 * ((m : ℝ) + 1) ^ 2 / (T : ℝ) := by
        rw [div_div_eq_mul_div]; ring

/-- The order-level BIC **value function**: the infimum of `armaBIC` over parameters
in the constraint set at fixed orders `(p, q)` (junk by the `iInf` convention when
unbounded below). -/
noncomputable def armaBICmin (p q : ℕ) {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  ⨅ ba : {ba : (Fin p → ℝ) × (Fin q → ℝ) // ARMAInvertibleParams ba.1 ba.2},
    armaBIC ba.val.1 ba.val.2 x

end StatLean.TimeSeries
