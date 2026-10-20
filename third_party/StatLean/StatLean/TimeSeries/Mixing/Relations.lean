module
public import StatLean.TimeSeries.Mixing.Defs
public import StatLean.TimeSeries.Mixing.MarkovBridge
public import StatLean.TimeSeries.ForMathlib.Markov.IFSMinorization
public import StatLean.TimeSeries.Process.Stationary
public import StatLean.TimeSeries.Models.WhiteNoise
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Relations between the mixing coefficients (FY §2.6.1, pp. 68–71)

Basic properties of the five dependence coefficients of `Mixing/Defs.lean` and the
classical implication chain `ψ-mixing ⇒ φ-mixing ⇒ {β-, ρ-mixing} ⇒ α-mixing`
(FY §2.6.1 "basic facts", cited to Bradley 1986):

* set-level basics: the description sets are nonempty and bounded, the coefficients
  nonnegative; `α ≤ 1`, monotone in both σ-algebra arguments; process coefficients
  antitone in the lag;
* provable coefficient inequalities: `2α ≤ β`, `α ≤ φ`, `β ≤ φ`, `φ ≤ 2ψ`-form,
  `α ≤ ¼ρ` (FY's display `α(k) ≤ ¼ρ(k)`);
* the Bradley square-root relation `ρ ≤ 2√φ` (giving FY's `¼ρ(k) ≤ ½φ^{1/2}(k)`) —
  **PROVED** (2026-08-09) via Ibragimov's covariance inequality
  `|Cov(f,g)| ≤ 2 φ^{1/2} ‖f‖₂ ‖g‖₂`;
* heredity under instantaneous measurable transforms;
* the shift lemma: under strict stationarity the anchored coefficients equal the
  coefficients between any `k`-shifted past/future pair (the property FY uses silently
  in every block argument);
* the in-text non-example (ix): a deterministic recursion `X_{t+1} = m(X_t)` with a
  non-degenerate event is not α-mixing;
* literature statement DEBTS: Pham–Tran (causal ARMA is exponentially β-mixing),
  Basrak–Davis–Mikosch (GARCH is exponentially α-mixing), Kolmogorov–Rozanov (Gaussian:
  ρ-mixing ⇔ α-mixing) — **all three removed**; see **Removed** below.

**Removed (2026-08-10, user directive).** The module's four sorried bricks and the three
headline debts proved from them were deleted, together with three `private` helpers left
with no surviving consumer. This removes the whole of the module's literature-debt tail; the
mixing-coefficient theory above it — every inequality, the shift lemma, the non-example, the
Bradley `ρ ≤ 2√φ` relation — is untouched, as is the Harris/Lyapunov apparatus that was
built to feed the deleted bricks.

*Sorried bricks (the four listed in the directive):*
* `arma_stateChain_brick` — a stationary causal ARMA with iid innovations of continuous
  positive density has `HasGeometricStateChain`; residue was model-side (the causal
  representation, and the two-block state update for `q ≥ 1`).
* `garch_stateChain_brick` — the same conclusion for a strictly stationary GARCH(p, q).
* `gaussian_rho_linear_brick` — BRICK 1 of the Gaussian comparison: Gaussian maximal
  correlation is carried by the linear span (Wiener–Itô/Hermite reduction).
* `gaussian_pair_corr_le_alpha_brick` — BRICK 2: the two-variable Kolmogorov–Rozanov bound
  via Sheppard's bivariate orthant identity.

*Headline consumers, deleted because their proofs consume a deleted brick:*
* `arma_betaCoeff_exponential_debt` — **Pham–Tran 1985 / FY §2.6.1(v)**: a stationary causal
  ARMA process with iid innovations admitting a continuous positive density is exponentially
  **β-mixing**.
* `garch_alphaCoeff_exponential_debt` — **Basrak–Davis–Mikosch 2002 / FY §2.6.1(x)**: a
  strictly stationary GARCH(p, q) is exponentially **α-mixing**.
* `gaussian_rho_le_alpha_debt` — **Kolmogorov–Rozanov 1960 / FY §2.6.1(viii)**: for a
  stationary Gaussian process, `ρ(k) ≤ 2π α(k)`.

*`private`, proved, left without a consumer:* `linComb` (the linear functional
`∑_{s ∈ S} a_s X_s`) and its two measurability lemmas `measurable_linComb_sigmaLE`,
`measurable_linComb_sigmaGE`.

*Kept:* the entire coefficient theory, the state-chain transfer machinery
`alphaCoeff_exponential_of_hasGeometricStateChain` /
`betaCoeff_exponential_of_hasGeometricStateChain` (which the deleted headlines were the only
callers of, but which are public and remain usable), and the quantitative Harris envelope
`exists_invariant_geometric_envelope_of_harris` with
`lintegral_lyap_le_of_isErgodicWithRate` / `integrable_lyap_of_isErgodicWithRate`.

Recover from `bdc8143f`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.1
(pp. 68–71). (`FY §2.6.1`.)

**Proof formalization notes.**
* `2α ≤ β`: the four-set partition `{A, Aᶜ} × {B, Bᶜ}` has partition sum
  `4|P(A∩B) − P(A)P(B)|`.
* `α ≤ φ`: `|P(A∩B) − P(A)P(B)| = P(A)·|P(B|A) − P(B)| ≤ φ` (the `P(A) = 0` term
  vanishes).
* `β ≤ φ`: for a partition pair, `Σ_j |P(B_j|A_i) − P(B_j)| ≤ 2 sup_B |P(B|A_i) − P(B)|`
  (split the sum by sign; each signed half is a single event).
* `α ≤ ¼ρ`: centered indicators, `Cov(1_A, 1_B) = P(A∩B) − P(A)P(B)` and
  `Var(1_A) = P(A)(1−P(A)) ≤ ¼`.
* The shift lemma transports the description sets through the path map; strict
  stationarity is exactly invariance of the path law under the shift.
* `ρ ≤ 2√φ`: two Cauchy–Schwarz passes on a partition pair against the row bound
  `Σ_j |P(A ∩ B_j) − P(A)P(B_j)| ≤ 2 P(A) φ` (the second pass against
  `Σ_i (∫_{A_i} g² + P(A_i)∫g²) = 2∫g²`, which is what makes the constant `2` sharp), then
  transport to general `L²` by simple-function approximation and dominated convergence.

**Bibliographic comments.** The implication chain and the sharp constants are collected
in R. C. Bradley, *Basic properties of strong mixing conditions* (in Eberlein–Taqqu,
1986) and his 2005 survey; `ρ ≤ 2√φ` is due to Peligrad (after Cogburn and Ibragimov).
Pham & Tran, *Some mixing properties of time series models*, SPA 1985; Basrak, Davis &
Mikosch, *Regular variation of GARCH processes*, SPA 2002; Kolmogorov & Rozanov 1960
for the Gaussian ρ ⇔ α equivalence. The Gaussian comparison `ρ ≤ 2π α` had been reduced
here to two named bricks — the Wiener–Itô/Hermite reduction of the maximal correlation to
the linear span, and Sheppard's bivariate orthant identity — both removed with the debt they
served.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-! ### Set-level basics

Two-σ-algebra statements follow the Mathlib `condExp` binder convention: the ambient
σ-algebra `mΩ` is a plain implicit bound *after* the sub-σ-algebras and immediately
before `μ`, so that local-instance resolution and unification agree (an
instance-implicit ambient would be shadowed by the sub-σ-algebra binders). -/

section TwoAlgebras

variable {Ω : Type*}

/-- On a probability space every measure is at most `1` after `toReal`. -/
private lemma toReal_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (s : Set Ω) : (μ s).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono (measure_ne_top μ Set.univ) (measure_mono (Set.subset_univ s))

/-- Every value in the α description set is bounded by `1`. -/
private lemma abs_alpha_term_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A B : Set Ω) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| ≤ 1 := by
  have h1 := toReal_le_one (μ := μ) (A ∩ B)
  have h2 := toReal_le_one (μ := μ) A
  have h3 := toReal_le_one (μ := μ) B
  have h0 : (0 : ℝ) ≤ (μ (A ∩ B)).toReal := ENNReal.toReal_nonneg
  have h0a : (0 : ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h0b : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;> nlinarith

/-- The α description set contains `0` (take `A = ∅`). -/
theorem alphaMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω) :
    (0 : ℝ) ∈ {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|} :=
  ⟨∅, ∅, @MeasurableSet.empty Ω m₁, @MeasurableSet.empty Ω m₂, by simp⟩

/-- On a probability space the α description set is bounded above by `1`. -/
theorem alphaMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    BddAbove {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      r = |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, B, -, -, rfl⟩
  exact abs_alpha_term_le_one A B

/-- `0 ≤ α`. -/
theorem alphaMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    0 ≤ alphaMixCoeff μ m₁ m₂ :=
  le_csSup (alphaMixCoeff_set_bddAbove (mΩ := mΩ)) (alphaMixCoeff_set_nonempty (mΩ := mΩ) μ)

/-- `α ≤ 1` (indeed `α ≤ ¼`, but FY only uses boundedness). -/
theorem alphaMixCoeff_le_one {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    alphaMixCoeff μ m₁ m₂ ≤ 1 :=
  Real.sSup_le (by rintro r ⟨A, B, -, -, rfl⟩; exact abs_alpha_term_le_one A B) zero_le_one

/-- α is monotone in both σ-algebra arguments. -/
theorem alphaMixCoeff_mono {m₁ m₂ m₁' m₂' mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁' ≤ m₁) (h₂ : m₂' ≤ m₂) :
    alphaMixCoeff μ m₁' m₂' ≤ alphaMixCoeff μ m₁ m₂ := by
  refine csSup_le_csSup (alphaMixCoeff_set_bddAbove (mΩ := mΩ))
    ⟨0, alphaMixCoeff_set_nonempty (mΩ := mΩ) μ⟩ ?_
  rintro r ⟨A, B, hA, hB, rfl⟩
  exact ⟨A, B, h₁ _ hA, h₂ _ hB, rfl⟩

end TwoAlgebras

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The process α-coefficient is antitone in the lag (FY: "monotone nonincreasing",
used silently; from `sigmaGE X (n+1) ≤ sigmaGE X n`). -/
theorem alphaCoeff_antitone [IsProbabilityMeasure μ] (X : ℤ → Ω → ℝ) :
    Antitone fun n : ℕ => alphaCoeff X μ n := by
  intro a b hab
  refine alphaMixCoeff_mono le_rfl ?_
  refine iSup₂_le fun s hs => ?_
  have hs' : (b : ℤ) ≤ s := hs
  refine le_iSup₂_of_le s (Set.mem_Ici.mpr ?_) le_rfl
  exact le_trans (by exact_mod_cast hab) hs'

end Process

/-! ### Provable coefficient inequalities (FY §2.6.1 basic facts) -/

section TwoAlgebras2

variable {Ω : Type*}

private lemma toReal_inter_le {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A B : Set Ω) : (μ (A ∩ B)).toReal ≤ (μ A).toReal :=
  ENNReal.toReal_mono (measure_ne_top μ A) (measure_mono Set.inter_subset_left)

/-- Finite measurable partitions split any measurable set additively. -/
private lemma sum_toReal_inter {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {J : ℕ} {B : Fin J → Set Ω} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise fun j j' => Disjoint (B j) (B j')) (hcov : (⋃ j, B j) = Set.univ)
    {S : Set Ω} (hS : MeasurableSet S) :
    ∑ j, (μ (S ∩ B j)).toReal = (μ S).toReal := by
  have hmeas : μ S = ∑ j, μ (S ∩ B j) := by
    calc μ S = μ (⋃ j, S ∩ B j) := by rw [← Set.inter_iUnion, hcov, Set.inter_univ]
      _ = ∑' j, μ (S ∩ B j) :=
          measure_iUnion (fun j j' hjj' =>
            (hd hjj').mono Set.inter_subset_right Set.inter_subset_right)
            (fun j => hS.inter (hB j))
      _ = ∑ j, μ (S ∩ B j) := tsum_fintype _
  rw [hmeas, ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]

/-- The φ description set contains `0` (take `A = univ`, `B = ∅`). -/
private lemma phiMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (0 : ℝ) ∈ {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      0 < (μ A).toReal ∧
      r = |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|} :=
  ⟨Set.univ, ∅, @MeasurableSet.univ Ω m₁, @MeasurableSet.empty Ω m₂, by simp, by simp⟩

private lemma abs_phi_term_le_one {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : 0 < (μ A).toReal) :
    |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal| ≤ 1 := by
  have h1 : (0 : ℝ) ≤ (μ (A ∩ B)).toReal / (μ A).toReal :=
    div_nonneg ENNReal.toReal_nonneg hA.le
  have h2 : (μ (A ∩ B)).toReal / (μ A).toReal ≤ 1 :=
    (div_le_one hA).2 (toReal_inter_le A B)
  have h3 := toReal_le_one (μ := μ) B
  have h4 : (0 : ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

private lemma phiMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    BddAbove {r : ℝ | ∃ A B : Set Ω, MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      0 < (μ A).toReal ∧
      r = |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, B, -, -, hA, rfl⟩
  exact abs_phi_term_le_one hA

private lemma phiMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] : 0 ≤ phiMixCoeff μ m₁ m₂ :=
  le_csSup (phiMixCoeff_set_bddAbove (mΩ := mΩ)) (phiMixCoeff_set_nonempty (mΩ := mΩ) μ)

/-- The core estimate behind both `α ≤ φ` and `β ≤ φ`. -/
private lemma abs_alpha_term_le_mul_phi {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A B : Set Ω} (hA : MeasurableSet[m₁] A)
    (hB : MeasurableSet[m₂] B) :
    |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
      ≤ (μ A).toReal * phiMixCoeff μ m₁ m₂ := by
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : (0:ℝ) ≤ (μ A).toReal) with h0 | hpos
  · have hA0 : μ A = 0 := by
      have := (ENNReal.toReal_eq_zero_iff (μ A)).1 h0.symm
      exact this.resolve_right (measure_ne_top μ A)
    have hAB : μ (A ∩ B) = 0 := measure_mono_null Set.inter_subset_left hA0
    simp [hAB, hA0]
  · have key : |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        = (μ A).toReal * |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal| := by
      have hne : (μ A).toReal ≠ 0 := ne_of_gt hpos
      have e1 : (μ A).toReal * ((μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal)
          = -((μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal) := by
        field_simp
        ring
      have e2 : |(μ A).toReal| * |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|
          = |(μ A).toReal * ((μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal)| :=
        (abs_mul _ _).symm
      rw [abs_of_pos hpos] at e2
      rw [e2, e1, abs_neg]
    rw [key]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    exact le_csSup (phiMixCoeff_set_bddAbove (mΩ := mΩ)) ⟨A, B, hA, hB, hpos, rfl⟩

/-- Splitting a set along a sub-family of a finite disjoint measurable family. -/
private lemma toReal_inter_biUnion {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {J : ℕ} {B : Fin J → Set Ω} (hB : ∀ j, MeasurableSet (B j))
    (hd : Pairwise fun j j' => Disjoint (B j) (B j')) (S : Finset (Fin J))
    {T : Set Ω} (hT : MeasurableSet T) :
    (μ (T ∩ ⋃ j ∈ S, B j)).toReal = ∑ j ∈ S, (μ (T ∩ B j)).toReal := by
  have hset : T ∩ (⋃ j ∈ S, B j) = ⋃ j ∈ S, (T ∩ B j) := by
    simp [Set.inter_iUnion]
  rw [hset, measure_biUnion_finset
      (fun j _ j' _ hjj' => (hd hjj').mono Set.inter_subset_right Set.inter_subset_right)
      (fun j _ => hT.inter (hB j)),
    ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]

/-- The partition sum defining `β` is at most `2φ`; the engine behind `β ≤ φ`. -/
private lemma beta_sum_le_two_mul_phi {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {I J : ℕ} {A : Fin I → Set Ω} {B : Fin J → Set Ω}
    (hA : ∀ i, MeasurableSet[m₁] (A i)) (hB : ∀ j, MeasurableSet[m₂] (B j))
    (hdA : Pairwise fun i i' => Disjoint (A i) (A i'))
    (hcA : (⋃ i, A i) = Set.univ)
    (hdB : Pairwise fun j j' => Disjoint (B j) (B j')) :
    ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ 2 * phiMixCoeff μ m₁ m₂ := by
  have hBm : ∀ j, MeasurableSet (B j) := fun j => h₂ _ (hB j)
  have hAm : ∀ i, MeasurableSet (A i) := fun i => h₁ _ (hA i)
  -- Row bound: each `i`-row is at most `2 P(A i) φ`, by splitting the `j`'s by sign.
  have hrow : ∀ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ 2 * ((μ (A i)).toReal * phiMixCoeff μ m₁ m₂) := by
    intro i
    set d : Fin J → ℝ := fun j =>
      (μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal with hd
    -- The signed groups, each a single `m₂`-event.
    have hgroup : ∀ S : Finset (Fin J), ∑ j ∈ S, d j
        = (μ (A i ∩ ⋃ j ∈ S, B j)).toReal
          - (μ (A i)).toReal * (μ (⋃ j ∈ S, B j)).toReal := by
      intro S
      have h1 := toReal_inter_biUnion (μ := μ) hBm hdB S (hAm i)
      have huniv : MeasurableSet (Set.univ : Set Ω) := MeasurableSet.univ
      have h2 := toReal_inter_biUnion (μ := μ) hBm hdB S huniv
      simp only [Set.univ_inter] at h2
      rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have habs : ∀ S : Finset (Fin J), |∑ j ∈ S, d j|
        ≤ (μ (A i)).toReal * phiMixCoeff μ m₁ m₂ := by
      intro S
      rw [hgroup S]
      have hUm : MeasurableSet[m₂] (⋃ j ∈ S, B j) :=
        Finset.measurableSet_biUnion S (fun j _ => hB j)
      exact abs_alpha_term_le_mul_phi (hA i) hUm
    set P : Fin J → Prop := fun j => 0 ≤ d j with hP
    classical
    have hsplit : ∑ j, |d j|
        = (∑ j ∈ Finset.univ.filter P, d j)
          + (-∑ j ∈ Finset.univ.filter (fun j => ¬ P j), d j) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P (fun j => |d j|),
        ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun j hj => abs_of_nonneg (Finset.mem_filter.1 hj).2
      · exact Finset.sum_congr rfl fun j hj =>
          abs_of_neg (lt_of_not_ge (Finset.mem_filter.1 hj).2)
    rw [hsplit]
    have e1 := (le_abs_self _).trans (habs (Finset.univ.filter P))
    have e2 := (neg_le_abs _).trans (habs (Finset.univ.filter (fun j => ¬ P j)))
    linarith
  calc ∑ i, ∑ j, |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|
      ≤ ∑ i, 2 * ((μ (A i)).toReal * phiMixCoeff μ m₁ m₂) :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = 2 * phiMixCoeff μ m₁ m₂ * ∑ i, (μ (A i)).toReal := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = 2 * phiMixCoeff μ m₁ m₂ := by
        have : ∑ i, (μ (A i)).toReal = 1 := by
          have huniv : MeasurableSet (Set.univ : Set Ω) := MeasurableSet.univ
          have := sum_toReal_inter (μ := μ) hAm hdA hcA huniv
          simpa using this
        rw [this, mul_one]

/-- The β description set contains `0` (the trivial one-cell partitions). -/
private lemma betaMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (0 : ℝ) ∈ {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
      (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
      (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
      (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
      (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
      r = (1 / 2) * ∑ i, ∑ j,
        |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
  refine ⟨1, 1, fun _ => Set.univ, fun _ => Set.univ, fun _ => MeasurableSet.univ,
    fun _ => MeasurableSet.univ, fun i i' h => absurd (Subsingleton.elim i i') h,
    fun j j' h => absurd (Subsingleton.elim j j') h,
    Set.univ_subset_iff.mp (Set.subset_iUnion (fun _ : Fin 1 => (Set.univ : Set Ω)) 0),
    Set.univ_subset_iff.mp (Set.subset_iUnion (fun _ : Fin 1 => (Set.univ : Set Ω)) 0), ?_⟩
  simp

private lemma betaMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    BddAbove {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
      (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
      (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
      (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
      (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
      r = (1 / 2) * ∑ i, ∑ j,
        |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
  refine ⟨phiMixCoeff μ m₁ m₂, ?_⟩
  rintro r ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  have := beta_sum_le_two_mul_phi (μ := μ) h₁ h₂ hA hB hdA hcA hdB
  linarith

private lemma betaMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) : 0 ≤ betaMixCoeff μ m₁ m₂ :=
  le_csSup (betaMixCoeff_set_bddAbove h₁ h₂) (betaMixCoeff_set_nonempty (mΩ := mΩ) μ)

theorem alphaMixCoeff_le_phiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    alphaMixCoeff μ m₁ m₂ ≤ phiMixCoeff μ m₁ m₂ := by
  refine Real.sSup_le ?_ (phiMixCoeff_nonneg (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂))
  rintro r ⟨A, B, hA, hB, rfl⟩
  refine (abs_alpha_term_le_mul_phi hA hB).trans ?_
  have h1 := toReal_le_one (μ := μ) A
  have h2 : (0 : ℝ) ≤ phiMixCoeff μ m₁ m₂ :=
    phiMixCoeff_nonneg (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂)
  nlinarith

theorem betaMixCoeff_le_phiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    betaMixCoeff μ m₁ m₂ ≤ phiMixCoeff μ m₁ m₂ := by
  refine Real.sSup_le ?_ (phiMixCoeff_nonneg (mΩ := mΩ) (μ := μ) (m₁ := m₁) (m₂ := m₂))
  rintro r ⟨I, J, A, B, hA, hB, hdA, hdB, hcA, hcB, rfl⟩
  have := beta_sum_le_two_mul_phi (μ := μ) h₁ h₂ hA hB hdA hcA hdB
  linarith

/-- `μ (A ∩ Bᶜ) = μ A − μ (A ∩ B)` after `toReal`. -/
private lemma toReal_inter_compl {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (A : Set Ω) {B : Set Ω} (hB : MeasurableSet B) :
    (μ (A ∩ Bᶜ)).toReal = (μ A).toReal - (μ (A ∩ B)).toReal := by
  have h := measure_inter_add_diff (μ := μ) A hB
  have h2 : (μ (A ∩ B)).toReal + (μ (A \ B)).toReal = (μ A).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h]
  rw [Set.diff_eq] at h2
  linarith

theorem two_mul_alphaMixCoeff_le_betaMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    2 * alphaMixCoeff μ m₁ m₂ ≤ betaMixCoeff μ m₁ m₂ := by
  have hβ0 : 0 ≤ betaMixCoeff μ m₁ m₂ := betaMixCoeff_nonneg h₁ h₂
  have key : alphaMixCoeff μ m₁ m₂ ≤ betaMixCoeff μ m₁ m₂ / 2 := by
    refine Real.sSup_le ?_ (by linarith)
    rintro r ⟨A, B, hA, hB, rfl⟩
    have hAm : MeasurableSet A := h₁ _ hA
    have hBm : MeasurableSet B := h₂ _ hB
    -- The four cells of `{A, Aᶜ} × {B, Bᶜ}` all have the same discrepancy.
    have eAc : (μ Aᶜ).toReal = 1 - (μ A).toReal := by
      have := toReal_inter_compl (μ := μ) Set.univ hAm
      simpa using this
    have eBc : (μ Bᶜ).toReal = 1 - (μ B).toReal := by
      have := toReal_inter_compl (μ := μ) Set.univ hBm
      simpa using this
    have e01 : (μ (A ∩ Bᶜ)).toReal = (μ A).toReal - (μ (A ∩ B)).toReal :=
      toReal_inter_compl (μ := μ) A hBm
    have e10 : (μ (Aᶜ ∩ B)).toReal = (μ B).toReal - (μ (A ∩ B)).toReal := by
      have := toReal_inter_compl (μ := μ) B hAm
      rwa [Set.inter_comm B Aᶜ, Set.inter_comm B A] at this
    have e11 : (μ (Aᶜ ∩ Bᶜ)).toReal = (μ Aᶜ).toReal - (μ (Aᶜ ∩ B)).toReal :=
      toReal_inter_compl (μ := μ) Aᶜ hBm
    set A' : Fin 2 → Set Ω := ![A, Aᶜ] with hA'
    set B' : Fin 2 → Set Ω := ![B, Bᶜ] with hB'
    have hmem : 2 * |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        ∈ {r : ℝ | ∃ (I J : ℕ) (A : Fin I → Set Ω) (B : Fin J → Set Ω),
          (∀ i, MeasurableSet[m₁] (A i)) ∧ (∀ j, MeasurableSet[m₂] (B j)) ∧
          (Pairwise fun i i' => Disjoint (A i) (A i')) ∧
          (Pairwise fun j j' => Disjoint (B j) (B j')) ∧
          (⋃ i, A i) = Set.univ ∧ (⋃ j, B j) = Set.univ ∧
          r = (1 / 2) * ∑ i, ∑ j,
            |(μ (A i ∩ B j)).toReal - (μ (A i)).toReal * (μ (B j)).toReal|} := by
      refine ⟨2, 2, A', B', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hA', hA, hA.compl]
      · intro j; fin_cases j <;> simp [hB', hB, hB.compl]
      · intro i i' h; fin_cases i <;> fin_cases i' <;>
          simp_all [disjoint_compl_right, disjoint_compl_left]
      · intro j j' h; fin_cases j <;> fin_cases j' <;>
          simp_all [disjoint_compl_right, disjoint_compl_left]
      · refine Set.univ_subset_iff.mp fun x _ => ?_
        by_cases hx : x ∈ A
        · exact Set.mem_iUnion.2 ⟨0, by simpa [hA'] using hx⟩
        · exact Set.mem_iUnion.2 ⟨1, by simpa [hA'] using hx⟩
      · refine Set.univ_subset_iff.mp fun x _ => ?_
        by_cases hx : x ∈ B
        · exact Set.mem_iUnion.2 ⟨0, by simpa [hB'] using hx⟩
        · exact Set.mem_iUnion.2 ⟨1, by simpa [hB'] using hx⟩
      · rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
        simp only [hA', hB', Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [e01, e11, e10, eAc, eBc]
        have t2 : (μ A).toReal - (μ (A ∩ B)).toReal
            - (μ A).toReal * (1 - (μ B).toReal)
            = -((μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal) := by ring
        have t3 : (μ B).toReal - (μ (A ∩ B)).toReal
            - (1 - (μ A).toReal) * (μ B).toReal
            = -((μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal) := by ring
        have t4 : 1 - (μ A).toReal - ((μ B).toReal - (μ (A ∩ B)).toReal)
            - (1 - (μ A).toReal) * (1 - (μ B).toReal)
            = (μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal := by ring
        rw [t2, t3, t4, abs_neg]
        ring
    have hcs : 2 * |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
        ≤ betaMixCoeff μ m₁ m₂ := le_csSup (betaMixCoeff_set_bddAbove h₁ h₂) hmem
    linarith
  linarith

/-- `φ ≤ ψ` in the calibrated form `|P(B) − P(B|A)| = P(B)|1 − P(B|A)/P(B)|`
(the `P(B) = 0` cell contributes `0` on both sides).

**Statement repaired 2026-08-05**: the unconditional form is FALSE — the classical
ψ-coefficient may be `+∞`, the ψ description set is then unbounded, and Lean's
`Real.sSup` junk convention makes `psiMixCoeff = 0` (formally verified counterexample
recorded in the proof body below). The finiteness hypothesis `hψbdd` restores the
classical statement (Bradley ch. 3: `φ ≤ ψ` whenever `ψ < ∞`). -/
theorem phiMixCoeff_le_psiMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    -- USER-INPUT: finiteness of ψ (the classical coefficient may be +∞); Bradley ch. 3
    (hψbdd : BddAbove {r : ℝ | ∃ A B : Set Ω,
      MeasurableSet[m₁] A ∧ MeasurableSet[m₂] B ∧
      0 < (μ A).toReal ∧ 0 < (μ B).toReal ∧
      r = |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal|}) :
    phiMixCoeff μ m₁ m₂ ≤ psiMixCoeff μ m₁ m₂ := by
  -- **FALSE AS FROZEN — unplanned debt (formally verified counterexample).**
  -- The ψ description set `{|1 − P(A∩B)/(P(A)P(B))| : P(A)P(B) > 0}` is *unbounded above*
  -- in general (the classical ψ-coefficient may be `+∞`; Bradley, *Introduction to Strong
  -- Mixing Conditions*), and Lean's `Real.sSup` junk convention then returns `0`
  -- (`Real.sSup_of_not_bddAbove`), so `psiMixCoeff μ m₁ m₂ = 0` while `φ` stays positive.
  --
  -- Witness (checked in Lean, 0 sorries, against these very definitions):
  --   `μ₀ := volume.restrict (Set.Icc (0:ℝ) 1)` on `Ω = ℝ`, `m₁ = m₂ = mΩ = Borel ℝ`.
  --   * `A = B = Set.Icc 0 (1/(n+2))` gives the ψ-value `|1 − a/(a·a)| = n + 1` for every
  --     `n : ℕ`, so the ψ set is not `BddAbove` and `psiMixCoeff μ₀ = 0`;
  --   * `A = B = Set.Icc 0 (1/2)` gives the φ-value `|1/2 − (1/2)/(1/2)| = 1/2`, and the
  --     φ set *is* bounded by `1`, so `phiMixCoeff μ₀ ≥ 1/2 > 0 = psiMixCoeff μ₀`.
  --
  -- REPAIR APPLIED (2026-08-05, wave `ts/c-sweep-mixing`): the hypothesis `hψbdd`
  -- ("ψ is finite") is now part of the statement, and the intended proof below closes it:
  -- for a φ-witness `(A, B)` with `P(A) > 0`, either `P(B) = 0` (both sides `0`) or
  -- `|P(B) − P(A∩B)/P(A)| = P(B)·|1 − P(A∩B)/(P(A)P(B))| ≤ 1·ψ`.
  have hψnn : 0 ≤ psiMixCoeff μ m₁ m₂ :=
    le_csSup hψbdd ⟨Set.univ, Set.univ, @MeasurableSet.univ Ω m₁, @MeasurableSet.univ Ω m₂,
      by simp, by simp, by simp⟩
  refine Real.sSup_le ?_ hψnn
  rintro r ⟨A, B, hA, hB, hApos, rfl⟩
  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg : (0:ℝ) ≤ (μ B).toReal) with hB0 | hBpos
  · -- `P(B) = 0`: the φ value is `0`
    have hB0' : μ B = 0 :=
      ((ENNReal.toReal_eq_zero_iff (μ B)).1 hB0.symm).resolve_right (measure_ne_top μ B)
    have hAB : μ (A ∩ B) = 0 := measure_mono_null Set.inter_subset_right hB0'
    simpa [hAB, hB0'] using hψnn
  · -- `P(B) > 0`: calibrate the φ value against the ψ witness at the same pair
    have hAne : (μ A).toReal ≠ 0 := ne_of_gt hApos
    have hBne : (μ B).toReal ≠ 0 := ne_of_gt hBpos
    have hmem : |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal| ≤ psiMixCoeff μ m₁ m₂ :=
      le_csSup hψbdd ⟨A, B, hA, hB, hApos, hBpos, rfl⟩
    have e1 : (μ B).toReal * (1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal)
        = (μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal := by
      field_simp
    have key : |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|
        = (μ B).toReal * |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal| := by
      calc |(μ B).toReal - (μ (A ∩ B)).toReal / (μ A).toReal|
          = |(μ B).toReal * (1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal)| := by
            rw [e1]
        _ = |(μ B).toReal| * |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal| :=
            abs_mul _ _
        _ = (μ B).toReal * |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal| := by
            rw [abs_of_pos hBpos]
    rw [key]
    have hnn : (0:ℝ) ≤ |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal| := abs_nonneg _
    have hle1 := toReal_le_one (μ := μ) B
    nlinarith

/-- Cauchy–Schwarz for real `L²` integrals. -/
private lemma abs_integral_mul_le {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ| ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  set F : Lp ℝ 2 μ := hf.toLp f with hFdef
  set G : Lp ℝ 2 μ := hg.toLp g with hGdef
  have hFae : (F : Ω → ℝ) =ᵐ[μ] f := MemLp.coeFn_toLp hf
  have hGae : (G : Ω → ℝ) =ᵐ[μ] g := MemLp.coeFn_toLp hg
  have hFG : (inner ℝ F G : ℝ) = ∫ ω, f ω * g ω ∂μ := by
    rw [MeasureTheory.L2.inner_def F G]
    refine integral_congr_ae ?_
    filter_upwards [hFae, hGae] with ω h1 h2
    rw [show (inner ℝ (F ω) (G ω) : ℝ) = G ω * F ω from rfl, h1, h2, mul_comm]
  have hFF : (‖F‖ : ℝ) = Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
    have h : (‖F‖ : ℝ) ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def F F]
      refine integral_congr_ae ?_
      filter_upwards [hFae] with ω h1
      rw [show (inner ℝ (F ω) (F ω) : ℝ) = F ω * F ω from rfl, h1, sq]
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  have hGG : (‖G‖ : ℝ) = Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
    have h : (‖G‖ : ℝ) ^ 2 = ∫ ω, g ω ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def G G]
      refine integral_congr_ae ?_
      filter_upwards [hGae] with ω h1
      rw [show (inner ℝ (G ω) (G ω) : ℝ) = G ω * G ω from rfl, h1, sq]
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  rw [← hFG, ← hFF, ← hGG]
  exact abs_real_inner_le_norm _ _

/-- Cauchy–Schwarz for the covariance. -/
private lemma abs_covariance_le_sqrt_mul {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |cov[f, g; μ]| ≤ Real.sqrt (variance f μ) * Real.sqrt (variance g μ) := by
  have hF : MemLp (fun ω => f ω - μ[f]) 2 μ := hf.sub (memLp_const _)
  have hG : MemLp (fun ω => g ω - μ[g]) 2 μ := hg.sub (memLp_const _)
  have hcov : cov[f, g; μ] = ∫ ω, (f ω - μ[f]) * (g ω - μ[g]) ∂μ := rfl
  rw [hcov, variance_eq_integral hf.aestronglyMeasurable.aemeasurable,
    variance_eq_integral hg.aestronglyMeasurable.aemeasurable]
  exact abs_integral_mul_le hF hG

/-- The ρ description set contains `0` (take `f = g = 0`). -/
private lemma rhoMixCoeff_set_nonempty {m₁ m₂ mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    (0 : ℝ) ∈ {r : ℝ | ∃ f g : Ω → ℝ, Measurable[m₁] f ∧ Measurable[m₂] g ∧
      MemLp f 2 μ ∧ MemLp g 2 μ ∧
      r = |cov[f, g; μ]| / (Real.sqrt (variance f μ) * Real.sqrt (variance g μ))} := by
  refine ⟨fun _ => 0, fun _ => 0, measurable_const, measurable_const,
    memLp_const 0, memLp_const 0, ?_⟩
  simp [covariance]

private lemma rhoMixCoeff_set_bddAbove {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] :
    BddAbove {r : ℝ | ∃ f g : Ω → ℝ, Measurable[m₁] f ∧ Measurable[m₂] g ∧
      MemLp f 2 μ ∧ MemLp g 2 μ ∧
      r = |cov[f, g; μ]| / (Real.sqrt (variance f μ) * Real.sqrt (variance g μ))} := by
  refine ⟨1, ?_⟩
  rintro r ⟨f, g, -, -, hf, hg, rfl⟩
  exact div_le_one_of_le₀ (abs_covariance_le_sqrt_mul hf hg)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private lemma rhoMixCoeff_nonneg {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] : 0 ≤ rhoMixCoeff μ m₁ m₂ :=
  le_csSup (rhoMixCoeff_set_bddAbove (mΩ := mΩ)) (rhoMixCoeff_set_nonempty (mΩ := mΩ) μ)

/-- **FY's display** `α ≤ ¼ρ` (centered indicators; `Var 1_A ≤ ¼`). -/
theorem alphaMixCoeff_le_quarter_mul_rhoMixCoeff {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    alphaMixCoeff μ m₁ m₂ ≤ (1 / 4) * rhoMixCoeff μ m₁ m₂ := by
  have hρ0 : 0 ≤ rhoMixCoeff μ m₁ m₂ := rhoMixCoeff_nonneg (mΩ := mΩ) (μ := μ)
  refine Real.sSup_le ?_ (by linarith)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hAm : MeasurableSet A := h₁ _ hA
  have hBm : MeasurableSet B := h₂ _ hB
  set f : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hfdef
  set g : Ω → ℝ := B.indicator (fun _ => (1 : ℝ)) with hgdef
  have hfmeas : Measurable[m₁] f := Measurable.indicator measurable_const hA
  have hgmeas : Measurable[m₂] g := Measurable.indicator measurable_const hB
  have hfL : MemLp f 2 μ := MemLp.indicator hAm (memLp_const 1)
  have hgL : MemLp g 2 μ := MemLp.indicator hBm (memLp_const 1)
  have hfint : ∫ ω, f ω ∂μ = (μ A).toReal := by
    rw [hfdef]
    simpa using! integral_indicator_const (μ := μ) (1 : ℝ) hAm
  have hgint : ∫ ω, g ω ∂μ = (μ B).toReal := by
    rw [hgdef]
    simpa using! integral_indicator_const (μ := μ) (1 : ℝ) hBm
  have hmulint : ∫ ω, f ω * g ω ∂μ = (μ (A ∩ B)).toReal := by
    have he : (fun ω => f ω * g ω) = (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simpa [hfdef, hgdef] using (Set.inter_indicator_mul (fun _ => (1:ℝ)) (fun _ => (1:ℝ)) ω).symm
    rw [he]
    simpa using! integral_indicator_const (μ := μ) (1 : ℝ) (hAm.inter hBm)
  have hcov : cov[f, g; μ] = (μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal := by
    rw [covariance_eq_sub hfL hgL]
    have : μ[f * g] = ∫ ω, f ω * g ω ∂μ := by simp [Pi.mul_apply]
    rw [this, hmulint, hfint, hgint]
  -- `Var 1_A = P(A)(1 − P(A)) ≤ ¼`.
  have hsqf : (fun ω => f ω ^ 2) = f := by
    funext ω
    by_cases hx : ω ∈ A <;>
      simp [hfdef, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hsqg : (fun ω => g ω ^ 2) = g := by
    funext ω
    by_cases hx : ω ∈ B <;>
      simp [hgdef, Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hvarf : variance f μ = (μ A).toReal - (μ A).toReal ^ 2 := by
    rw [variance_eq_sub hfL]
    have : μ[f ^ 2] = ∫ ω, f ω ^ 2 ∂μ := by simp [Pi.pow_apply]
    rw [this, hsqf, hfint]
  have hvarg : variance g μ = (μ B).toReal - (μ B).toReal ^ 2 := by
    rw [variance_eq_sub hgL]
    have : μ[g ^ 2] = ∫ ω, g ω ^ 2 ∂μ := by simp [Pi.pow_apply]
    rw [this, hsqg, hgint]
  have hsf : Real.sqrt (variance f μ) ≤ 1 / 2 := by
    have h1 := toReal_le_one (μ := μ) A
    have h0 : (0:ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
    have hb : variance f μ ≤ (1 / 2) ^ 2 := by
      rw [hvarf]; nlinarith [sq_nonneg ((μ A).toReal - 1 / 2)]
    calc Real.sqrt (variance f μ) ≤ Real.sqrt ((1/2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  have hsg : Real.sqrt (variance g μ) ≤ 1 / 2 := by
    have h1 := toReal_le_one (μ := μ) B
    have h0 : (0:ℝ) ≤ (μ B).toReal := ENNReal.toReal_nonneg
    have hb : variance g μ ≤ (1 / 2) ^ 2 := by
      rw [hvarg]; nlinarith [sq_nonneg ((μ B).toReal - 1 / 2)]
    calc Real.sqrt (variance g μ) ≤ Real.sqrt ((1/2 : ℝ) ^ 2) := Real.sqrt_le_sqrt hb
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  set D : ℝ := Real.sqrt (variance f μ) * Real.sqrt (variance g μ) with hD
  have hD0 : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hD4 : D ≤ 1 / 4 := by
    have := mul_le_mul hsf hsg (Real.sqrt_nonneg _) (by norm_num)
    calc D ≤ (1/2 : ℝ) * (1/2) := this
      _ = 1 / 4 := by norm_num
  rcases eq_or_lt_of_le hD0 with hD0' | hDpos
  · -- degenerate: Cauchy–Schwarz forces a vanishing covariance
    have := abs_covariance_le_sqrt_mul hfL hgL
    rw [← hD, ← hD0'] at this
    rw [← hcov]
    linarith [abs_nonneg (cov[f, g; μ])]
  · have hmem : |cov[f, g; μ]| / D ≤ rhoMixCoeff μ m₁ m₂ :=
      le_csSup (rhoMixCoeff_set_bddAbove (mΩ := mΩ)) ⟨f, g, hfmeas, hgmeas, hfL, hgL, rfl⟩
    have hkey : |cov[f, g; μ]| = (|cov[f, g; μ]| / D) * D := by
      field_simp
    rw [← hcov, hkey]
    have h1 : 0 ≤ |cov[f, g; μ]| / D := div_nonneg (abs_nonneg _) hD0
    nlinarith

/-! #### The square-root relation `ρ ≤ 2√φ` (Ibragimov's covariance inequality)

The engine is Ibragimov's `L²`-`L²` covariance inequality
`|Cov(f, g)| ≤ 2 φ^{1/2} ‖f‖₂ ‖g‖₂`, proved here for finite-range (simple) `f`, `g` by a
two-fold Cauchy–Schwarz against the row bound `Σ_j |P(A ∩ B_j) − P(A)P(B_j)| ≤ 2 P(A) φ`,
and then transported to general `L²` functions by simple-function approximation and
dominated convergence. -/


private lemma toReal_inter_biUnion_finset {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [DecidableEq ι] {B : ι → Set Ω}
    (hB : ∀ j, MeasurableSet (B j)) (S : Finset ι)
    (hdB : ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' → Disjoint (B j) (B j'))
    {T : Set Ω} (hT : MeasurableSet T) :
    (μ (T ∩ ⋃ j ∈ S, B j)).toReal = ∑ j ∈ S, (μ (T ∩ B j)).toReal := by
  have hset : T ∩ (⋃ j ∈ S, B j) = ⋃ j ∈ S, (T ∩ B j) := by
    simp [Set.inter_iUnion]
  rw [hset, measure_biUnion_finset
      (fun j hj j' hj' hjj' =>
        (hdB j hj j' hj' hjj').mono Set.inter_subset_right Set.inter_subset_right)
      (fun j _ => hT.inter (hB j)),
    ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)]

private lemma sum_toReal_inter_finset {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [DecidableEq ι] {T : Finset ι} {B : ι → Set Ω}
    (hB : ∀ j, MeasurableSet (B j))
    (hdB : ∀ j ∈ T, ∀ j' ∈ T, j ≠ j' → Disjoint (B j) (B j'))
    (hcov : ∀ ω, ∃ j ∈ T, ω ∈ B j)
    {S : Set Ω} (hS : MeasurableSet S) :
    ∑ j ∈ T, (μ (S ∩ B j)).toReal = (μ S).toReal := by
  have huniv : (⋃ j ∈ T, B j) = (Set.univ : Set Ω) := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true, exists_prop]
    exact hcov ω
  rw [← toReal_inter_biUnion_finset hB T hdB hS, huniv, Set.inter_univ]

private lemma phi_row_bound_finset {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (B : ι → Set Ω) (hB : ∀ j, MeasurableSet[m₂] (B j))
    (hdB : ∀ j ∈ T, ∀ j' ∈ T, j ≠ j' → Disjoint (B j) (B j'))
    {A : Set Ω} (hA : MeasurableSet[m₁] A) :
    ∑ j ∈ T, |(μ (A ∩ B j)).toReal - (μ A).toReal * (μ (B j)).toReal|
      ≤ 2 * ((μ A).toReal * phiMixCoeff μ m₁ m₂) := by
  classical
  have hBm : ∀ j, MeasurableSet (B j) := fun j => h₂ _ (hB j)
  have hAm : MeasurableSet A := h₁ _ hA
  set d : ι → ℝ := fun j =>
    (μ (A ∩ B j)).toReal - (μ A).toReal * (μ (B j)).toReal with hd
  have hgroup : ∀ S : Finset ι, S ⊆ T → ∑ j ∈ S, d j
      = (μ (A ∩ ⋃ j ∈ S, B j)).toReal
        - (μ A).toReal * (μ (⋃ j ∈ S, B j)).toReal := by
    intro S hS
    have hdS : ∀ j ∈ S, ∀ j' ∈ S, j ≠ j' → Disjoint (B j) (B j') :=
      fun j hj j' hj' hne => hdB j (hS hj) j' (hS hj') hne
    have h1 := toReal_inter_biUnion_finset (μ := μ) hBm S hdS hAm
    have h2 := toReal_inter_biUnion_finset (μ := μ) hBm S hdS (MeasurableSet.univ (α := Ω))
    simp only [Set.univ_inter] at h2
    rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have habs : ∀ S : Finset ι, S ⊆ T → |∑ j ∈ S, d j|
      ≤ (μ A).toReal * phiMixCoeff μ m₁ m₂ := by
    intro S hS
    rw [hgroup S hS]
    have hUm : MeasurableSet[m₂] (⋃ j ∈ S, B j) :=
      Finset.measurableSet_biUnion S (fun j _ => hB j)
    exact abs_alpha_term_le_mul_phi hA hUm
  set P : ι → Prop := fun j => 0 ≤ d j with hP
  have hsplit : ∑ j ∈ T, |d j|
      = (∑ j ∈ T.filter P, d j) + (-∑ j ∈ T.filter (fun j => ¬ P j), d j) := by
    rw [← Finset.sum_filter_add_sum_filter_not T P (fun j => |d j|),
      ← Finset.sum_neg_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun j hj => abs_of_nonneg (Finset.mem_filter.1 hj).2
    · exact Finset.sum_congr rfl fun j hj =>
        abs_of_neg (lt_of_not_ge (Finset.mem_filter.1 hj).2)
  rw [hsplit]
  have e1 := (le_abs_self _).trans (habs (T.filter P) (Finset.filter_subset _ _))
  have e2 := (neg_le_abs _).trans (habs (T.filter (fun j => ¬ P j)) (Finset.filter_subset _ _))
  linarith

private lemma cov_partition_arith {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (a : ι → ℝ) (b : κ → ℝ) (P : ι → ℝ) (Q : κ → ℝ) (R : ι → κ → ℝ) (φ : ℝ)
    (hφ : 0 ≤ φ) (hP : ∀ i, 0 ≤ P i) (hQ : ∀ j, 0 ≤ Q j) (hR : ∀ i j, 0 ≤ R i j)
    (hrow : ∀ i ∈ S, ∑ j ∈ T, |R i j - P i * Q j| ≤ 2 * (P i * φ))
    (hcolsum : ∀ j ∈ T, ∑ i ∈ S, R i j = Q j)
    (htot : ∑ i ∈ S, P i = 1) :
    |∑ i ∈ S, ∑ j ∈ T, a i * b j * R i j
        - (∑ i ∈ S, a i * P i) * (∑ j ∈ T, b j * Q j)|
      ≤ 2 * Real.sqrt φ * Real.sqrt (∑ i ∈ S, a i ^ 2 * P i)
          * Real.sqrt (∑ j ∈ T, b j ^ 2 * Q j) := by
  classical
  have hWnn : ∀ i, (0:ℝ) ≤ (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) := fun i =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _)
      (by have h1 := hR i j; have h2 := mul_nonneg (hP i) (hQ j); linarith)
  have hX : (0:ℝ) ≤ ∑ i ∈ S, a i ^ 2 * P i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hP i)
  have hY : (0:ℝ) ≤ ∑ j ∈ T, b j ^ 2 * Q j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hQ j)
  have hid : (∑ i ∈ S, ∑ j ∈ T, a i * b j * R i j
        - (∑ i ∈ S, a i * P i) * (∑ j ∈ T, b j * Q j))
      = ∑ i ∈ S, ∑ j ∈ T, a i * b j * (R i j - P i * Q j) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hid]
  have hstep1 : |∑ i ∈ S, ∑ j ∈ T, a i * b j * (R i j - P i * Q j)|
      ≤ ∑ i ∈ S, |a i| * ∑ j ∈ T, |b j| * |R i j - P i * Q j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul, mul_assoc]
  refine hstep1.trans ?_
  have hrowCS : ∀ i ∈ S, ∑ j ∈ T, |b j| * |R i j - P i * Q j|
      ≤ Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) * Real.sqrt (2 * (P i * φ)) := by
    intro i hi
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul T
      (r := fun j => |b j| * |R i j - P i * Q j|)
      (f := fun j => b j ^ 2 * |R i j - P i * Q j|)
      (g := fun j => |R i j - P i * Q j|)
      (fun j _ => mul_nonneg (sq_nonneg _) (abs_nonneg _)) (fun j _ => abs_nonneg _)
      (fun j _ => by rw [mul_pow, sq_abs (b j)]; ring)
    have hnn : (0:ℝ) ≤ ∑ j ∈ T, |b j| * |R i j - P i * Q j| :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have h1 : ∑ j ∈ T, b j ^ 2 * |R i j - P i * Q j| ≤ (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) :=
      Finset.sum_le_sum fun j _ => by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [abs_le]
        have h1 := hR i j
        have h2 := mul_nonneg (hP i) (hQ j)
        constructor <;> linarith
    have h2 := hrow i hi
    have hg0 : (0:ℝ) ≤ ∑ j ∈ T, |R i j - P i * Q j| :=
      Finset.sum_nonneg fun j _ => abs_nonneg _
    have hb : (∑ j ∈ T, |b j| * |R i j - P i * Q j|) ^ 2
        ≤ (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) * (2 * (P i * φ)) :=
      hCS.trans (mul_le_mul h1 h2 hg0 (hWnn i))
    calc ∑ j ∈ T, |b j| * |R i j - P i * Q j|
        = Real.sqrt ((∑ j ∈ T, |b j| * |R i j - P i * Q j|) ^ 2) := (Real.sqrt_sq hnn).symm
      _ ≤ Real.sqrt ((∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) * (2 * (P i * φ))) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) * Real.sqrt (2 * (P i * φ)) := Real.sqrt_mul (hWnn i) _
  have hstep2 : ∑ i ∈ S, |a i| * ∑ j ∈ T, |b j| * |R i j - P i * Q j|
      ≤ ∑ i ∈ S, |a i| * (Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) * Real.sqrt (2 * (P i * φ))) :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hrowCS i hi) (abs_nonneg _)
  refine hstep2.trans ?_
  have h2φ : (0:ℝ) ≤ 2 * φ := by linarith
  have hfac : ∀ i ∈ S, |a i| * (Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) * Real.sqrt (2 * (P i * φ)))
      = Real.sqrt (2 * φ) * (|a i| * Real.sqrt (P i) * Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))) := by
    intro i _
    have hsp : Real.sqrt (2 * (P i * φ)) = Real.sqrt (2 * φ) * Real.sqrt (P i) := by
      rw [← Real.sqrt_mul h2φ (P i)]
      congr 1
      ring
    rw [hsp]; ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  have hCS2 := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul S
    (r := fun i => |a i| * Real.sqrt (P i) * Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)))
    (f := fun i => a i ^ 2 * P i)
    (g := fun i => (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)))
    (fun i _ => mul_nonneg (sq_nonneg _) (hP i)) (fun i _ => hWnn i)
    (fun i _ => by
      rw [mul_pow, mul_pow, sq_abs (a i), Real.sq_sqrt (hP i), Real.sq_sqrt (hWnn i)])
  have hWsum : ∑ i ∈ S, (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) = 2 * ∑ j ∈ T, b j ^ 2 * Q j := by
    have e1 : ∀ i ∈ S, (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))
        = (∑ j ∈ T, b j ^ 2 * R i j) + P i * ∑ j ∈ T, b j ^ 2 * Q j := by
      intro i _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.sum_mul, htot, one_mul,
      Finset.sum_comm]
    have e2 : ∀ j ∈ T, ∑ i ∈ S, b j ^ 2 * R i j = b j ^ 2 * Q j := by
      intro j hj
      rw [← Finset.mul_sum, hcolsum j hj]
    rw [Finset.sum_congr rfl e2]
    ring
  have hrnn : (0:ℝ) ≤ ∑ i ∈ S, |a i| * Real.sqrt (P i) * Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j)) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hfin : ∑ i ∈ S, |a i| * Real.sqrt (P i) * Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))
      ≤ Real.sqrt (∑ i ∈ S, a i ^ 2 * P i) * Real.sqrt (2 * ∑ j ∈ T, b j ^ 2 * Q j) := by
    calc ∑ i ∈ S, |a i| * Real.sqrt (P i) * Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))
        = Real.sqrt ((∑ i ∈ S, |a i| * Real.sqrt (P i) * Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))) ^ 2) :=
          (Real.sqrt_sq hrnn).symm
      _ ≤ Real.sqrt ((∑ i ∈ S, a i ^ 2 * P i) * ∑ i ∈ S, (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))) := Real.sqrt_le_sqrt hCS2
      _ = Real.sqrt (∑ i ∈ S, a i ^ 2 * P i) * Real.sqrt (∑ i ∈ S, (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))) :=
          Real.sqrt_mul hX _
      _ = Real.sqrt (∑ i ∈ S, a i ^ 2 * P i) * Real.sqrt (2 * ∑ j ∈ T, b j ^ 2 * Q j) := by
          rw [hWsum]
  have hnum : Real.sqrt (2 * φ) * Real.sqrt (2 * ∑ j ∈ T, b j ^ 2 * Q j)
      = 2 * Real.sqrt φ * Real.sqrt (∑ j ∈ T, b j ^ 2 * Q j) := by
    rw [← Real.sqrt_mul h2φ]
    have e : (2 * φ) * (2 * ∑ j ∈ T, b j ^ 2 * Q j)
        = 2 ^ 2 * (φ * ∑ j ∈ T, b j ^ 2 * Q j) := by ring
    rw [e, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2 ^ 2),
      Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_mul hφ]
    ring
  calc Real.sqrt (2 * φ) * ∑ i ∈ S, |a i| * Real.sqrt (P i) * Real.sqrt (∑ j ∈ T, b j ^ 2 * (R i j + P i * Q j))
      ≤ Real.sqrt (2 * φ)
          * (Real.sqrt (∑ i ∈ S, a i ^ 2 * P i) * Real.sqrt (2 * ∑ j ∈ T, b j ^ 2 * Q j)) :=
        mul_le_mul_of_nonneg_left hfin (Real.sqrt_nonneg _)
    _ = Real.sqrt (∑ i ∈ S, a i ^ 2 * P i)
          * (Real.sqrt (2 * φ) * Real.sqrt (2 * ∑ j ∈ T, b j ^ 2 * Q j)) := by ring
    _ = 2 * Real.sqrt φ * Real.sqrt (∑ i ∈ S, a i ^ 2 * P i)
          * Real.sqrt (∑ j ∈ T, b j ^ 2 * Q j) := by rw [hnum]; ring


private lemma finiteRange_pointwise {f : Ω → ℝ} (hfin : (Set.range f).Finite) (F : ℝ → ℝ) (ω : Ω) :
    F (f ω) = ∑ y ∈ hfin.toFinset, (f ⁻¹' {y}).indicator (fun _ => F y) ω := by
  classical
  rw [Finset.sum_eq_single (f ω)]
  · rw [Set.indicator_of_mem (by simp : ω ∈ f ⁻¹' {f ω})]
  · intro y _ hne
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fun h => hne h.symm
  · intro h
    exact absurd (hfin.mem_toFinset.mpr (Set.mem_range_self (f := f) ω)) h

private lemma indicator_inter_mul_const {E₁ E₂ : Set Ω} (c₁ c₂ : ℝ) (ω : Ω) :
    (E₁.indicator (fun _ => c₁) ω) * (E₂.indicator (fun _ => c₂) ω)
      = (E₁ ∩ E₂).indicator (fun _ => c₁ * c₂) ω := by
  by_cases h1 : ω ∈ E₁ <;> by_cases h2 : ω ∈ E₂ <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]

private lemma finiteRange_pointwise_mul {f g : Ω → ℝ} (hff : (Set.range f).Finite)
    (hgf : (Set.range g).Finite) (F G : ℝ → ℝ) (ω : Ω) :
    F (f ω) * G (g ω)
      = ∑ y ∈ hff.toFinset, ∑ z ∈ hgf.toFinset,
          ((f ⁻¹' {y}) ∩ (g ⁻¹' {z})).indicator (fun _ => F y * G z) ω := by
  classical
  rw [finiteRange_pointwise hff F ω, finiteRange_pointwise hgf G ω, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ =>
    indicator_inter_mul_const _ _ ω

private lemma integral_finiteRange {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hfin : (Set.range f).Finite) (hmeas : ∀ y : ℝ, MeasurableSet (f ⁻¹' {y}))
    (F : ℝ → ℝ) :
    ∫ ω, F (f ω) ∂μ = ∑ y ∈ hfin.toFinset, F y * (μ (f ⁻¹' {y})).toReal := by
  classical
  have hfun : (fun ω => F (f ω))
      = fun ω => ∑ y ∈ hfin.toFinset, (f ⁻¹' {y}).indicator (fun _ => F y) ω :=
    funext fun ω => finiteRange_pointwise hfin F ω
  have hsum := integral_finset_sum (μ := μ) hfin.toFinset
      (f := fun (y : ℝ) (ω : Ω) => (f ⁻¹' {y}).indicator (fun _ => F y) ω)
      (fun y _ => (integrable_const (F y)).indicator (hmeas y))
  rw [hfun, hsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [integral_indicator_const (F y) (hmeas y), smul_eq_mul, mul_comm]
  rfl

private lemma integral_finiteRange_mul {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hff : (Set.range f).Finite) (hgf : (Set.range g).Finite)
    (hfm : ∀ y : ℝ, MeasurableSet (f ⁻¹' {y})) (hgm : ∀ z : ℝ, MeasurableSet (g ⁻¹' {z}))
    (F G : ℝ → ℝ) :
    ∫ ω, F (f ω) * G (g ω) ∂μ
      = ∑ y ∈ hff.toFinset, ∑ z ∈ hgf.toFinset,
          F y * G z * (μ ((f ⁻¹' {y}) ∩ (g ⁻¹' {z}))).toReal := by
  classical
  have hfun : (fun ω => F (f ω) * G (g ω))
      = fun ω => ∑ y ∈ hff.toFinset, ∑ z ∈ hgf.toFinset,
          ((f ⁻¹' {y}) ∩ (g ⁻¹' {z})).indicator (fun _ => F y * G z) ω :=
    funext fun ω => finiteRange_pointwise_mul hff hgf F G ω
  have hsum := integral_finset_sum (μ := μ) hff.toFinset
      (f := fun (y : ℝ) (ω : Ω) => ∑ z ∈ hgf.toFinset,
        ((f ⁻¹' {y}) ∩ (g ⁻¹' {z})).indicator (fun _ => F y * G z) ω)
      (fun y _ => integrable_finset_sum _ (fun z _ =>
        (integrable_const (F y * G z)).indicator ((hfm y).inter (hgm z))))
  rw [hfun, hsum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hsum2 := integral_finset_sum (μ := μ) hgf.toFinset
      (f := fun (z : ℝ) (ω : Ω) => ((f ⁻¹' {y}) ∩ (g ⁻¹' {z})).indicator (fun _ => F y * G z) ω)
      (fun z _ => (integrable_const (F y * G z)).indicator ((hfm y).inter (hgm z)))
  rw [hsum2]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [integral_indicator_const (F y * G z) ((hfm y).inter (hgm z)), smul_eq_mul, mul_comm]
  rfl

private lemma preimage_fiber_disjoint (h : Ω → ℝ) {y y' : ℝ} (hne : y ≠ y') :
    Disjoint (h ⁻¹' {y}) (h ⁻¹' {y'}) := by
  refine Set.disjoint_left.mpr fun ω hy hy' => hne ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy hy'
  rw [← hy, ← hy']

private lemma abs_cov_le_of_finiteRange {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    (hff : (Set.range f).Finite) (hgf : (Set.range g).Finite) :
    |∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
      ≤ 2 * Real.sqrt (phiMixCoeff μ m₁ m₂) * Real.sqrt (∫ ω, f ω ^ 2 ∂μ)
          * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  classical
  have hA : ∀ y : ℝ, MeasurableSet[m₁] (f ⁻¹' {y}) := fun y => hf (measurableSet_singleton y)
  have hB : ∀ z : ℝ, MeasurableSet[m₂] (g ⁻¹' {z}) := fun z => hg (measurableSet_singleton z)
  have hAm : ∀ y : ℝ, MeasurableSet (f ⁻¹' {y}) := fun y => h₁ _ (hA y)
  have hBm : ∀ z : ℝ, MeasurableSet (g ⁻¹' {z}) := fun z => h₂ _ (hB z)
  have hcovf : ∀ ω, ∃ y ∈ hff.toFinset, ω ∈ f ⁻¹' {y} :=
    fun ω => ⟨f ω, hff.mem_toFinset.mpr (Set.mem_range_self ω), by simp⟩
  have hcovg : ∀ ω, ∃ z ∈ hgf.toFinset, ω ∈ g ⁻¹' {z} :=
    fun ω => ⟨g ω, hgf.mem_toFinset.mpr (Set.mem_range_self ω), by simp⟩
  have e1 : ∫ ω, f ω * g ω ∂μ
      = ∑ y ∈ hff.toFinset, ∑ z ∈ hgf.toFinset,
          y * z * (μ (f ⁻¹' {y} ∩ g ⁻¹' {z})).toReal :=
    integral_finiteRange_mul hff hgf hAm hBm (fun t => t) (fun t => t)
  have e2 : ∫ ω, f ω ∂μ = ∑ y ∈ hff.toFinset, y * (μ (f ⁻¹' {y})).toReal :=
    integral_finiteRange hff hAm (fun t => t)
  have e3 : ∫ ω, g ω ∂μ = ∑ z ∈ hgf.toFinset, z * (μ (g ⁻¹' {z})).toReal :=
    integral_finiteRange hgf hBm (fun t => t)
  have e4 : ∫ ω, f ω ^ 2 ∂μ = ∑ y ∈ hff.toFinset, y ^ 2 * (μ (f ⁻¹' {y})).toReal :=
    integral_finiteRange hff hAm (fun t => t ^ 2)
  have e5 : ∫ ω, g ω ^ 2 ∂μ = ∑ z ∈ hgf.toFinset, z ^ 2 * (μ (g ⁻¹' {z})).toReal :=
    integral_finiteRange hgf hBm (fun t => t ^ 2)
  rw [e1, e2, e3, e4, e5]
  refine cov_partition_arith hff.toFinset hgf.toFinset (fun t => t) (fun t => t)
    (fun y => (μ (f ⁻¹' {y})).toReal) (fun z => (μ (g ⁻¹' {z})).toReal)
    (fun y z => (μ (f ⁻¹' {y} ∩ g ⁻¹' {z})).toReal) (phiMixCoeff μ m₁ m₂)
    (phiMixCoeff_nonneg (mΩ := mΩ)) (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg) ?_ ?_ ?_
  · intro y _
    exact phi_row_bound_finset h₁ h₂ hgf.toFinset (fun z => g ⁻¹' {z}) hB
      (fun z _ z' _ hne => preimage_fiber_disjoint g hne) (hA y)
  · intro z _
    show ∑ y ∈ hff.toFinset, (μ (f ⁻¹' {y} ∩ g ⁻¹' {z})).toReal = (μ (g ⁻¹' {z})).toReal
    have := sum_toReal_inter_finset (μ := μ) (T := hff.toFinset) (B := fun y => f ⁻¹' {y}) hAm
      (fun y _ y' _ hne => preimage_fiber_disjoint f hne) hcovf (hBm z)
    rw [← this]
    exact Finset.sum_congr rfl fun y _ => by rw [Set.inter_comm]
  · have := sum_toReal_inter_finset (μ := μ) (T := hff.toFinset) (B := fun y => f ⁻¹' {y}) hAm
      (fun y _ y' _ hne => preimage_fiber_disjoint f hne) hcovf (MeasurableSet.univ (α := Ω))
    simpa using this

/-- Simple-function approximation inside a single measurable structure. -/
private lemma exists_simple_approx {Ω' : Type*} [MeasurableSpace Ω'] {f : Ω' → ℝ} (hf : Measurable f) :
    ∃ u : ℕ → Ω' → ℝ, (∀ n, Measurable (u n)) ∧ (∀ n, (Set.range (u n)).Finite) ∧
      (∀ n ω, |u n ω| ≤ 2 * |f ω|) ∧ (∀ ω, Tendsto (fun n => u n ω) atTop (𝓝 (f ω))) := by
  refine ⟨fun n => ⇑(SimpleFunc.approxOn f hf Set.univ 0 (Set.mem_univ 0) n),
    fun n => SimpleFunc.measurable _, fun n => SimpleFunc.finite_range _,
    fun n ω => ?_, fun ω => ?_⟩
  · have h := SimpleFunc.norm_approxOn_zero_le hf (Set.mem_univ (0 : ℝ)) ω n
    simpa [Real.norm_eq_abs, two_mul] using h
  · exact SimpleFunc.tendsto_approxOn hf (Set.mem_univ (0 : ℝ)) (by simp)

private lemma abs_cov_le_of_memLp {m₁ m₂ mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    {f g : Ω → ℝ} (hf : Measurable[m₁] f) (hg : Measurable[m₂] g)
    (hfL : MemLp f 2 μ) (hgL : MemLp g 2 μ) :
    |∫ ω, f ω * g ω ∂μ - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ)|
      ≤ 2 * Real.sqrt (phiMixCoeff μ m₁ m₂) * Real.sqrt (∫ ω, f ω ^ 2 ∂μ)
          * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  classical
  obtain ⟨u, hum, huf, hubd, hutd⟩ := @exists_simple_approx Ω m₁ f hf
  obtain ⟨v, hvm, hvf, hvbd, hvtd⟩ := @exists_simple_approx Ω m₂ g hg
  have humΩ : ∀ n, Measurable (u n) := fun n => (hum n).mono h₁ le_rfl
  have hvmΩ : ∀ n, Measurable (v n) := fun n => (hvm n).mono h₂ le_rfl
  have hfI : Integrable f μ := hfL.integrable (by norm_num)
  have hgI : Integrable g μ := hgL.integrable (by norm_num)
  have hf2I : Integrable (fun ω => f ω ^ 2) μ := by
    have h := hfL.integrable_mul hfL
    have he : (f * f) = fun ω => f ω ^ 2 := by funext ω; simp [Pi.mul_apply, sq]
    rwa [he] at h
  have hg2I : Integrable (fun ω => g ω ^ 2) μ := by
    have h := hgL.integrable_mul hgL
    have he : (g * g) = fun ω => g ω ^ 2 := by funext ω; simp [Pi.mul_apply, sq]
    rwa [he] at h
  have hfgI : Integrable (fun ω => |f ω| * |g ω|) μ := by
    have h := (hfL.integrable_mul hgL).abs
    have he : (fun ω => |(f * g) ω|) = fun ω => |f ω| * |g ω| := by
      funext ω; simp [Pi.mul_apply, abs_mul]
    rwa [he] at h
  have T1 : Tendsto (fun n => ∫ ω, u n ω ∂μ) atTop (𝓝 (∫ ω, f ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => 2 * |f ω|)
      (fun n => (humΩ n).aestronglyMeasurable) (hfI.abs.const_mul 2)
      (fun n => Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hubd n ω)
      (Filter.Eventually.of_forall hutd)
  have T3 : Tendsto (fun n => ∫ ω, v n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => 2 * |g ω|)
      (fun n => (hvmΩ n).aestronglyMeasurable) (hgI.abs.const_mul 2)
      (fun n => Filter.Eventually.of_forall fun ω => by
        simpa [Real.norm_eq_abs] using hvbd n ω)
      (Filter.Eventually.of_forall hvtd)
  have T2 : Tendsto (fun n => ∫ ω, u n ω ^ 2 ∂μ) atTop (𝓝 (∫ ω, f ω ^ 2 ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => 4 * f ω ^ 2)
      (fun n => ((humΩ n).pow_const 2).aestronglyMeasurable) (hf2I.const_mul 4)
      (fun n => Filter.Eventually.of_forall fun ω => by
        have h := hubd n ω
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs (u n ω), sq_abs (f ω), abs_nonneg (f ω), abs_nonneg (u n ω)])
      (Filter.Eventually.of_forall fun ω => (hutd ω).pow 2)
  have T4 : Tendsto (fun n => ∫ ω, v n ω ^ 2 ∂μ) atTop (𝓝 (∫ ω, g ω ^ 2 ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => 4 * g ω ^ 2)
      (fun n => ((hvmΩ n).pow_const 2).aestronglyMeasurable) (hg2I.const_mul 4)
      (fun n => Filter.Eventually.of_forall fun ω => by
        have h := hvbd n ω
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [sq_abs (v n ω), sq_abs (g ω), abs_nonneg (g ω), abs_nonneg (v n ω)])
      (Filter.Eventually.of_forall fun ω => (hvtd ω).pow 2)
  have T5 : Tendsto (fun n => ∫ ω, u n ω * v n ω ∂μ) atTop (𝓝 (∫ ω, f ω * g ω ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun ω => 4 * (|f ω| * |g ω|))
      (fun n => ((humΩ n).mul (hvmΩ n)).aestronglyMeasurable) (hfgI.const_mul 4)
      (fun n => Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := hubd n ω
        have h2 := hvbd n ω
        nlinarith [abs_nonneg (u n ω), abs_nonneg (v n ω), abs_nonneg (f ω), abs_nonneg (g ω)])
      (Filter.Eventually.of_forall fun ω => (hutd ω).mul (hvtd ω))
  refine le_of_tendsto_of_tendsto'
    (f := fun n => |∫ ω, u n ω * v n ω ∂μ - (∫ ω, u n ω ∂μ) * (∫ ω, v n ω ∂μ)|)
    (g := fun n => 2 * Real.sqrt (phiMixCoeff μ m₁ m₂) * Real.sqrt (∫ ω, u n ω ^ 2 ∂μ)
      * Real.sqrt (∫ ω, v n ω ^ 2 ∂μ))
    ((T5.sub (T1.mul T3)).abs) ((tendsto_const_nhds.mul T2.sqrt).mul T4.sqrt) (fun n => ?_)
  exact abs_cov_le_of_finiteRange h₁ h₂ (hum n) (hvm n) (huf n) (hvf n)

/-- **DEBT (Bradley/Peligrad; FY §2.6.1 display `¼ρ ≤ ½√φ`)**: the square-root
relation `ρ ≤ 2√φ`. Literature-level; the proof needs the L²-duality description of
`ρ` and a two-sided conditional Cauchy–Schwarz argument. -/
theorem rhoMixCoeff_le_two_mul_sqrt_phiMixCoeff_debt {m₁ m₂ mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ) :
    rhoMixCoeff μ m₁ m₂ ≤ 2 * Real.sqrt (phiMixCoeff μ m₁ m₂) := by
  have hφ0 : 0 ≤ phiMixCoeff μ m₁ m₂ := phiMixCoeff_nonneg (mΩ := mΩ)
  refine Real.sSup_le ?_ (by positivity)
  rintro r ⟨f, g, hfm, hgm, hfL, hgL, rfl⟩
  set c : ℝ := ∫ ω, f ω ∂μ with hc
  set d : ℝ := ∫ ω, g ω ∂μ with hd
  have hf'm : Measurable[m₁] (fun ω => f ω - c) := hfm.sub measurable_const
  have hg'm : Measurable[m₂] (fun ω => g ω - d) := hgm.sub measurable_const
  have hf'L : MemLp (fun ω => f ω - c) 2 μ := hfL.sub (memLp_const _)
  have hg'L : MemLp (fun ω => g ω - d) 2 μ := hgL.sub (memLp_const _)
  have hf'0 : ∫ ω, (f ω - c) ∂μ = 0 := by
    rw [integral_sub (hfL.integrable (by norm_num)) (integrable_const _), integral_const]
    simp [hc]
  have hg'0 : ∫ ω, (g ω - d) ∂μ = 0 := by
    rw [integral_sub (hgL.integrable (by norm_num)) (integrable_const _), integral_const]
    simp [hd]
  have hmain := abs_cov_le_of_memLp h₁ h₂ hf'm hg'm hf'L hg'L
  rw [hf'0, hg'0] at hmain
  have hcov : cov[f, g; μ] = ∫ ω, (f ω - c) * (g ω - d) ∂μ := rfl
  have hvf : variance f μ = ∫ ω, (f ω - c) ^ 2 ∂μ :=
    variance_eq_integral hfL.aestronglyMeasurable.aemeasurable
  have hvg : variance g μ = ∫ ω, (g ω - d) ^ 2 ∂μ :=
    variance_eq_integral hgL.aestronglyMeasurable.aemeasurable
  have hkey : |cov[f, g; μ]|
      ≤ 2 * Real.sqrt (phiMixCoeff μ m₁ m₂)
          * Real.sqrt (variance f μ) * Real.sqrt (variance g μ) := by
    rw [hcov, hvf, hvg]
    simpa using hmain
  set D : ℝ := Real.sqrt (variance f μ) * Real.sqrt (variance g μ) with hD
  have hD0 : 0 ≤ D := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le hD0 with hD0' | hDpos
  · rw [← hD0']
    simp [Real.sqrt_nonneg]
  · rw [div_le_iff₀ hDpos]
    calc |cov[f, g; μ]|
        ≤ 2 * Real.sqrt (phiMixCoeff μ m₁ m₂)
            * Real.sqrt (variance f μ) * Real.sqrt (variance g μ) := hkey
      _ = 2 * Real.sqrt (phiMixCoeff μ m₁ m₂) * D := by rw [hD]; ring

end TwoAlgebras2

/-! ### Mixing-class implications (FY Definition 2.11 chain) -/

section Process2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The process past σ-algebra sits inside the ambient one once the coordinates are
measurable. -/
private lemma sigmaLE_le_ambient {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaLE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

/-- The process future σ-algebra sits inside the ambient one. -/
private lemma sigmaGE_le_ambient {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) (n : ℤ) :
    sigmaGE X n ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun s _ => (hmeas s).comap_le

/-- ψ-mixing ⇒ φ-mixing.

**Statement repaired 2026-08-05**: needs per-lag finiteness of ψ, for the same reason
as `phiMixCoeff_le_psiMixCoeff` (formally verified counterexample in the proof body:
constant-in-time process on `[0,1]` has junk `ψ ≡ 0` but `φ ≥ 1/2`). -/
theorem IsPsiMixing.isPhiMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsPsiMixing X μ)
    -- USER-INPUT: per-lag finiteness of ψ; Bradley ch. 3 / FY Def 2.11 implicit
    (hψbdd : ∀ n : ℕ, BddAbove {r : ℝ | ∃ A B : Set Ω,
      MeasurableSet[sigmaLE X 0] A ∧ MeasurableSet[sigmaGE X (n : ℤ)] B ∧
      0 < (μ A).toReal ∧ 0 < (μ B).toReal ∧
      r = |1 - (μ (A ∩ B)).toReal / (μ A).toReal / (μ B).toReal|}) :
    IsPhiMixing X μ := by
  -- **FALSE AS FROZEN — unplanned debt (formally verified counterexample).** The process
  -- shadow of `phiMixCoeff_le_psiMixCoeff`'s falsity: with `μ₀ = volume.restrict (Icc 0 1)`
  -- on `Ω = ℝ` and the constant-in-time process `X t ω = ω`, both flanking σ-algebras are
  -- the full Borel σ-algebra (`sigmaLE X c = sigmaGE X c = Borel ℝ`), so
  -- `psiCoeff X μ₀ n = 0` for every `n` (junk value of an unbounded `Real.sSup`) — hence
  -- `IsPsiMixing X μ₀` holds — while `phiCoeff X μ₀ n ≥ 1/2` for every `n`, so
  -- `IsPhiMixing X μ₀` fails. Checked in Lean with 0 sorries.
  -- REPAIR APPLIED (2026-08-05, wave `ts/c-sweep-mixing`): with `hψbdd` in the statement,
  -- `phiMixCoeff_le_psiMixCoeff` gives `φ(n) ≤ ψ(n)` at every lag and the squeeze against
  -- `0 ≤ φ(n)` closes this.
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ phiMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ)) :=
    fun _ => phiMixCoeff_nonneg (mΩ := ‹MeasurableSpace Ω›)
  have hle : ∀ n : ℕ, phiMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ))
      ≤ psiMixCoeff μ (sigmaLE X 0) (sigmaGE X (n : ℤ)) := fun n =>
    phiMixCoeff_le_psiMixCoeff (sigmaLE_le_ambient hmeas 0)
      (sigmaGE_le_ambient hmeas (n : ℤ)) (hψbdd n)
  exact squeeze_zero hnn hle h

/-- φ-mixing ⇒ β-mixing. -/
theorem IsPhiMixing.isBetaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsPhiMixing X μ) : IsBetaMixing X μ :=
  squeeze_zero
    (fun n => betaMixCoeff_nonneg (sigmaLE_le_ambient hmeas 0) (sigmaGE_le_ambient hmeas n))
    (fun n => betaMixCoeff_le_phiMixCoeff (sigmaLE_le_ambient hmeas 0)
      (sigmaGE_le_ambient hmeas n)) h

/-- β-mixing ⇒ α-mixing. -/
theorem IsBetaMixing.isAlphaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsBetaMixing X μ) : IsAlphaMixing X μ := by
  have hg : Tendsto (fun n : ℕ => 1 / 2 * betaCoeff X μ n) atTop (𝓝 0) := by
    have := h.const_mul (1 / 2 : ℝ)
    simpa using this
  refine squeeze_zero (fun n => alphaMixCoeff_nonneg (μ := μ)) (fun n => ?_) hg
  have := two_mul_alphaMixCoeff_le_betaMixCoeff (μ := μ)
    (sigmaLE_le_ambient hmeas 0) (sigmaGE_le_ambient hmeas n)
  unfold alphaCoeff betaCoeff
  linarith

/-- ρ-mixing ⇒ α-mixing. -/
theorem IsRhoMixing.isAlphaMixing [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hmeas : ∀ t, Measurable (X t)) (h : IsRhoMixing X μ) : IsAlphaMixing X μ := by
  have hg : Tendsto (fun n : ℕ => 1 / 4 * rhoCoeff X μ n) atTop (𝓝 0) := by
    have := h.const_mul (1 / 4 : ℝ)
    simpa using this
  refine squeeze_zero (fun n => alphaMixCoeff_nonneg (μ := μ)) (fun n => ?_) hg
  show alphaCoeff X μ n ≤ 1 / 4 * rhoCoeff X μ n
  unfold alphaCoeff rhoCoeff
  exact alphaMixCoeff_le_quarter_mul_rhoMixCoeff (μ := μ)
    (sigmaLE_le_ambient hmeas 0) (sigmaGE_le_ambient hmeas n)

/-! ### Heredity and the shift lemma -/

/-- **Heredity** (FY §2.6.1(iv)): an instantaneous measurable transform
`Y_t = g(X_t)` has smaller past/future σ-algebras, hence smaller α-coefficients; α-mixing
is inherited. (The same argument applies verbatim to β, ρ, φ, ψ via
`alphaMixCoeff_mono`-analogues; α is the one consumed downstream.) -/
theorem IsAlphaMixing.comp [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (h : IsAlphaMixing X μ) {g : ℝ → ℝ} (hg : Measurable g) :
    IsAlphaMixing (fun t ω => g (X t ω)) μ := by
  -- `σ(g ∘ X_s) = comap (X s) (comap g Borel) ≤ σ(X_s)`, so both flanking σ-algebras shrink.
  have hcomap : ∀ s : ℤ,
      MeasurableSpace.comap (fun ω => g (X s ω)) inferInstance
        ≤ MeasurableSpace.comap (X s) inferInstance := by
    intro s
    have he : MeasurableSpace.comap (fun ω => g (X s ω)) (inferInstance : MeasurableSpace ℝ)
        = MeasurableSpace.comap (X s) (MeasurableSpace.comap g inferInstance) :=
      (MeasurableSpace.comap_comp).symm
    rw [he]
    exact MeasurableSpace.comap_mono hg.comap_le
  refine squeeze_zero (fun n => alphaMixCoeff_nonneg (μ := μ)) (fun n => ?_) h
  exact alphaMixCoeff_mono (iSup₂_mono fun s _ => hcomap s) (iSup₂_mono fun s _ => hcomap s)

omit [MeasurableSpace Ω] in
/-- The path map of a shifted process pulls the coordinate σ-algebras back to the process
σ-algebras. -/
private lemma comap_path_cylinderEvents (X : ℤ → Ω → ℝ) (k : ℤ) (S : Set ℤ) :
    MeasurableSpace.comap (fun ω (t : ℤ) => X (t + k) ω) (cylinderEvents S)
      = ⨆ s ∈ S, MeasurableSpace.comap (X (s + k)) inferInstance := by
  unfold cylinderEvents
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun s => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_congr fun _ => ?_
  rw [MeasurableSpace.comap_comp]
  rfl

omit [MeasurableSpace Ω] in
private lemma iSup_Iic_shift (X : ℤ → Ω → ℝ) (c k : ℤ) :
    (⨆ s ∈ Set.Iic c, MeasurableSpace.comap (X (s + k)) inferInstance) = sigmaLE X (c + k) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (iSup₂_le fun u hu => ?_)
  · exact le_iSup₂_of_le (s + k) (Set.mem_Iic.mpr (by have : s ≤ c := hs; omega)) le_rfl
  · refine le_iSup₂_of_le (u - k) (Set.mem_Iic.mpr (by have : u ≤ c + k := hu; omega)) ?_
    exact le_of_eq (by rw [sub_add_cancel])

omit [MeasurableSpace Ω] in
private lemma iSup_Ici_shift (X : ℤ → Ω → ℝ) (c k : ℤ) :
    (⨆ s ∈ Set.Ici c, MeasurableSpace.comap (X (s + k)) inferInstance) = sigmaGE X (c + k) := by
  refine le_antisymm (iSup₂_le fun s hs => ?_) (iSup₂_le fun u hu => ?_)
  · exact le_iSup₂_of_le (s + k) (Set.mem_Ici.mpr (by have : c ≤ s := hs; omega)) le_rfl
  · refine le_iSup₂_of_le (u - k) (Set.mem_Ici.mpr (by have : c + k ≤ u := hu; omega)) ?_
    exact le_of_eq (by rw [sub_add_cancel])

omit [MeasurableSpace Ω] in
private lemma cylinderEvents_le (S : Set ℤ) :
    cylinderEvents (X := fun _ : ℤ => ℝ) S ≤ MeasurableSpace.pi :=
  iSup₂_le fun i _ => (measurable_pi_apply i).comap_le

/-- Strict stationarity transported to a finite index set: the law of `(X_{i+k})_{i ∈ s}`
is the law of `(X_i)_{i ∈ s}`. -/
private lemma map_finsetTuple_shift {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℤ) (s : Finset ℤ) :
    (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω)
      = μ.map fun ω (i : s) => X (i : ℤ) ω := by
  classical
  set e : s ≃ Fin s.card := s.equivFin with he
  set t : Fin s.card → ℤ := fun j => ((e.symm j : s) : ℤ) with ht
  set Φ : (Fin s.card → ℝ) → (∀ _ : s, ℝ) := fun p i => p (e i) with hΦdef
  have hΦ : Measurable Φ := measurable_pi_lambda _ fun i => measurable_pi_apply (e i)
  have hte : ∀ i : s, t (e i) = (i : ℤ) := by
    intro i; simp [ht]
  have hcomp : ∀ c : ℤ, Measurable fun ω (j : Fin s.card) => X (t j + c) ω :=
    fun c => measurable_pi_lambda _ fun j => hmeas _
  have hpush : ∀ c : ℤ,
      (μ.map fun ω (j : Fin s.card) => X (t j + c) ω).map Φ
        = μ.map fun ω (i : s) => X ((i : ℤ) + c) ω := by
    intro c
    rw [Measure.map_map hΦ (hcomp c)]
    congr 1
    funext ω i
    simp [hΦdef, hte i]
  have h0 : (μ.map fun ω (j : Fin s.card) => X (t j + 0) ω)
      = μ.map fun ω (j : Fin s.card) => X (t j) ω := by simp
  calc (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω)
      = (μ.map fun ω (j : Fin s.card) => X (t j + k) ω).map Φ := (hpush k).symm
    _ = (μ.map fun ω (j : Fin s.card) => X (t j) ω).map Φ := by rw [hstat s.card t k]
    _ = (μ.map fun ω (j : Fin s.card) => X (t j + 0) ω).map Φ := by rw [h0]
    _ = μ.map fun ω (i : s) => X ((i : ℤ) + 0) ω := hpush 0
    _ = μ.map fun ω (i : s) => X (i : ℤ) ω := by simp

/-- **Strict stationarity = shift-invariance of the path law.** -/
private lemma map_path_shift {X : ℤ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hstat : IsStrictlyStationary X μ) (hmeas : ∀ t, Measurable (X t)) (k : ℤ) :
    (μ.map fun ω (u : ℤ) => X (u + k) ω) = μ.map fun ω (u : ℤ) => X u ω := by
  have hTm : Measurable fun ω (u : ℤ) => X (u + k) ω :=
    measurable_pi_lambda _ fun _ => hmeas _
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  refine ext_of_generate_finite (measurableCylinders fun _ : ℤ => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro C hC
    obtain ⟨s, S, hSm, rfl⟩ := (mem_measurableCylinders C).mp hC
    have hcyl : MeasurableSet (cylinder s S) := MeasurableSet.cylinder (α := fun _ : ℤ => ℝ) s hSm
    have hT : Measurable fun ω (i : s) => X ((i : ℤ) + k) ω :=
      measurable_pi_lambda _ fun _ => hmeas _
    have hU : Measurable fun ω (i : s) => X (i : ℤ) ω :=
      measurable_pi_lambda _ fun _ => hmeas _
    have eT : (μ.map fun ω (u : ℤ) => X (u + k) ω) (cylinder s S)
        = (μ.map fun ω (i : s) => X ((i : ℤ) + k) ω) S := by
      rw [Measure.map_apply hTm hcyl, Measure.map_apply hT hSm]
      rfl
    have eU : (μ.map fun ω (u : ℤ) => X u ω) (cylinder s S)
        = (μ.map fun ω (i : s) => X (i : ℤ) ω) S := by
      rw [Measure.map_apply hUm hcyl, Measure.map_apply hU hSm]
      rfl
    rw [eT, eU, map_finsetTuple_shift hstat hmeas k s]
  · rw [Measure.map_apply hTm MeasurableSet.univ, Measure.map_apply hUm MeasurableSet.univ]
    simp

/-- The α-coefficient between two pulled-back σ-algebras only depends on the pushforward
law. -/
private lemma alphaMixCoeff_comap {V : Ω → (ℤ → ℝ)} (hV : Measurable V)
    {ν : Measure (ℤ → ℝ)} (hν : μ.map V = ν)
    (m₁ m₂ : MeasurableSpace (ℤ → ℝ)) (h₁ : m₁ ≤ MeasurableSpace.pi)
    (h₂ : m₂ ≤ MeasurableSpace.pi) :
    alphaMixCoeff μ (m₁.comap V) (m₂.comap V)
      = @alphaMixCoeff (ℤ → ℝ) MeasurableSpace.pi ν m₁ m₂ := by
  have hval : ∀ {S : Set (ℤ → ℝ)},
      @MeasurableSet (ℤ → ℝ) MeasurableSpace.pi S → ν S = μ (V ⁻¹' S) := by
    intro S hS
    rw [← hν]
    exact Measure.map_apply hV hS
  unfold alphaMixCoeff
  refine congrArg sSup (Set.ext fun r => ?_)
  constructor
  · rintro ⟨A, B, ⟨A', hA', rfl⟩, ⟨B', hB', rfl⟩, rfl⟩
    refine ⟨A', B', hA', hB', ?_⟩
    have e3 : ν (A' ∩ B') = μ (V ⁻¹' A' ∩ V ⁻¹' B') := by
      rw [hval (@MeasurableSet.inter (ℤ → ℝ) MeasurableSpace.pi _ _ (h₁ _ hA') (h₂ _ hB')),
        Set.preimage_inter]
    rw [hval (h₁ _ hA'), hval (h₂ _ hB'), e3]
  · rintro ⟨A', B', hA', hB', rfl⟩
    refine ⟨V ⁻¹' A', V ⁻¹' B', ⟨A', hA', rfl⟩, ⟨B', hB', rfl⟩, ?_⟩
    have e3 : ν (A' ∩ B') = μ (V ⁻¹' A' ∩ V ⁻¹' B') := by
      rw [hval (@MeasurableSet.inter (ℤ → ℝ) MeasurableSpace.pi _ _ (h₁ _ hA') (h₂ _ hB')),
        Set.preimage_inter]
    rw [hval (h₁ _ hA'), hval (h₂ _ hB'), e3]

/-- **Shift lemma** (used silently by every FY block argument): under strict
stationarity, the α-coefficient between the past up to `k` and the future from `k + n`
does not depend on the anchor `k`. -/
theorem IsStrictlyStationary.alphaMixCoeff_shift [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hstat : IsStrictlyStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) (k : ℤ) (n : ℕ) :
    alphaMixCoeff μ (sigmaLE X k) (sigmaGE X (k + n)) = alphaCoeff X μ n := by
  have hTm : Measurable fun ω (u : ℤ) => X (u + k) ω := measurable_pi_lambda _ fun _ => hmeas _
  have hUm : Measurable fun ω (u : ℤ) => X u ω := measurable_pi_lambda _ fun _ => hmeas _
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (ℤ → ℝ), (μ.map fun ω (u : ℤ) => X u ω) = ν := ⟨_, rfl⟩
  have hνT : (μ.map fun ω (u : ℤ) => X (u + k) ω) = ν := by
    rw [← hν]; exact map_path_shift hstat hmeas k
  have hLk : MeasurableSpace.comap (fun ω (u : ℤ) => X (u + k) ω) (cylinderEvents (Set.Iic 0))
      = sigmaLE X k := by
    rw [comap_path_cylinderEvents X k (Set.Iic 0), iSup_Iic_shift X 0 k, zero_add]
  have hGk : MeasurableSpace.comap (fun ω (u : ℤ) => X (u + k) ω)
      (cylinderEvents (Set.Ici (n : ℤ))) = sigmaGE X (k + n) := by
    rw [comap_path_cylinderEvents X k (Set.Ici (n : ℤ)), iSup_Ici_shift X (n : ℤ) k, add_comm]
  have hL0 : MeasurableSpace.comap (fun ω (u : ℤ) => X u ω) (cylinderEvents (Set.Iic 0))
      = sigmaLE X 0 := by
    have h := comap_path_cylinderEvents X 0 (Set.Iic 0)
    simp only [add_zero] at h
    exact h
  have hG0 : MeasurableSpace.comap (fun ω (u : ℤ) => X u ω) (cylinderEvents (Set.Ici (n : ℤ)))
      = sigmaGE X (n : ℤ) := by
    have h := comap_path_cylinderEvents X 0 (Set.Ici (n : ℤ))
    simp only [add_zero] at h
    exact h
  calc alphaMixCoeff μ (sigmaLE X k) (sigmaGE X (k + n))
      = alphaMixCoeff μ ((cylinderEvents (Set.Iic 0)).comap fun ω (u : ℤ) => X (u + k) ω)
          ((cylinderEvents (Set.Ici (n : ℤ))).comap fun ω (u : ℤ) => X (u + k) ω) := by
        rw [hLk, hGk]
    _ = @alphaMixCoeff (ℤ → ℝ) MeasurableSpace.pi ν (cylinderEvents (Set.Iic 0))
          (cylinderEvents (Set.Ici (n : ℤ))) :=
        alphaMixCoeff_comap hTm hνT _ _ (cylinderEvents_le _) (cylinderEvents_le _)
    _ = alphaMixCoeff μ ((cylinderEvents (Set.Iic 0)).comap fun ω (u : ℤ) => X u ω)
          ((cylinderEvents (Set.Ici (n : ℤ))).comap fun ω (u : ℤ) => X u ω) :=
        (alphaMixCoeff_comap hUm hν _ _ (cylinderEvents_le _) (cylinderEvents_le _)).symm
    _ = alphaCoeff X μ n := by rw [hL0, hG0]; rfl

/-! ### The deterministic non-example (FY §2.6.1(ix)) -/

/-- **FY §2.6.1(ix), quantitative core**: for a deterministic recursion
`X_{t+1} = m(X_t)` every event of the time-`n` state lies in the past σ-algebra as
well, so `α(n) ≥ P(X_n ∈ C)(1 − P(X_n ∈ C))`. -/
theorem alphaCoeff_ge_of_deterministic [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) {m : ℝ → ℝ} (hm : Measurable m)
    -- USER-INPUT: deterministic recursion; FY §2.6.1(ix)
    (hrec : ∀ t : ℤ, ∀ ω, X (t + 1) ω = m (X t ω))
    {C : Set ℝ} (hC : MeasurableSet C) (n : ℕ) :
    (μ (X n ⁻¹' C)).toReal * (1 - (μ (X n ⁻¹' C)).toReal)
      ≤ alphaCoeff X μ n := by
  -- The recursion solves as `X_n = m^[n] ∘ X_0`, so the time-`n` state is `𝓕_{-∞}^0`-measurable.
  have hiter : ∀ (k : ℕ) (ω : Ω), X (k : ℤ) ω = m^[k] (X 0 ω) := by
    intro k
    induction k with
    | zero => intro ω; simp
    | succ k ih =>
      intro ω
      have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hcast, hrec (k : ℤ) ω, ih ω]
      exact (Function.iterate_succ_apply' m k (X 0 ω)).symm
  have hDm : MeasurableSet (m^[n] ⁻¹' C) := (hm.iterate n) hC
  have hset : X (n : ℤ) ⁻¹' C = X 0 ⁻¹' (m^[n] ⁻¹' C) := by
    ext ω; simp [Set.mem_preimage, hiter n ω]
  set A : Set Ω := X (n : ℤ) ⁻¹' C with hAdef
  have hA1 : MeasurableSet[sigmaLE X 0] A := by
    have hcomap : MeasurableSpace.comap (X 0) inferInstance ≤ sigmaLE X 0 :=
      le_iSup₂_of_le (0 : ℤ) (Set.mem_Iic.mpr le_rfl) le_rfl
    refine hcomap _ ?_
    exact ⟨m^[n] ⁻¹' C, hDm, hset.symm⟩
  have hA2 : MeasurableSet[sigmaGE X (n : ℤ)] A := by
    have hcomap : MeasurableSpace.comap (X (n : ℤ)) inferInstance ≤ sigmaGE X (n : ℤ) :=
      le_iSup₂_of_le (n : ℤ) (Set.mem_Ici.mpr le_rfl) le_rfl
    exact hcomap _ ⟨C, hC, rfl⟩
  have hp0 : (0 : ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hp1 : (μ A).toReal ≤ 1 := toReal_le_one (μ := μ) A
  have hval : (μ A).toReal * (1 - (μ A).toReal)
      = |(μ (A ∩ A)).toReal - (μ A).toReal * (μ A).toReal| := by
    rw [Set.inter_self]
    rw [abs_of_nonneg (by nlinarith : (0:ℝ) ≤ (μ A).toReal - (μ A).toReal * (μ A).toReal)]
    ring
  rw [hval]
  have hbdd := alphaMixCoeff_set_bddAbove (μ := μ) (m₁ := sigmaLE X 0) (m₂ := sigmaGE X (n : ℤ))
  exact le_csSup hbdd ⟨A, A, hA1, hA2, rfl⟩

/-- **FY §2.6.1(ix)**: a deterministic recursion with uniformly non-degenerate events is
not α-mixing. -/
theorem not_isAlphaMixing_of_deterministic [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t)) {m : ℝ → ℝ} (hm : Measurable m)
    (hrec : ∀ t : ℤ, ∀ ω, X (t + 1) ω = m (X t ω))
    -- USER-INPUT: uniform non-degeneracy of some tail events; FY §2.6.1(ix)
    {c : ℝ} (hc : 0 < c) (hc' : c ≤ 1 / 2)
    (hC : ∀ n : ℕ, ∃ C : Set ℝ, MeasurableSet C ∧
      c ≤ (μ (X n ⁻¹' C)).toReal ∧ (μ (X n ⁻¹' C)).toReal ≤ 1 - c) :
    ¬ IsAlphaMixing X μ := by
  intro hmix
  have hpos : 0 < c * (1 - c) := by nlinarith
  obtain ⟨n, hn⟩ := (hmix.eventually (gt_mem_nhds hpos)).exists
  obtain ⟨C, hCm, hc1, hc2⟩ := hC n
  have hge := alphaCoeff_ge_of_deterministic (μ := μ) hmeas hm hrec hCm n
  have hprod : 0 ≤ ((μ (X n ⁻¹' C)).toReal - c) * (1 - (μ (X n ⁻¹' C)).toReal - c) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-! ### Literature statement DEBTS (FY §2.6.1(v), (viii), (x))

**Import note (2026-08-09, wave 5, authorized).** This file now imports
`Mixing/MarkovBridge.lean` and the `ForMathlib/Markov` stack. The earlier
`USER-INPUT` comment on `hroot` recorded a *deliberate separation* of this concept-layer
file from the model/Markov layers; that separation is **superseded** — importing an
area-`ForMathlib` stack from a concept file is charter-legal, and every ingredient of the
two model debts below lives on the other side of that edge, so keeping the edge unbuilt
served no purpose. (The `hroot` hypothesis is still stated inline rather than imported from
`Stationarity/ARMAExistence`, which is a *concept-to-concept* edge and stays closed.)

### The engine now available

Wave 5 built, `sorry`-free and axiom-clean, everything that the two model statements need
*outside the models themselves*:

* `MarkovBridge.IsMarkovOf` and the whole Bradley/Davydov bridge, over an **arbitrary
  measurable state space** (`Kernel E E`) — this removes, verbatim, the "vector-valued
  bridge" gap that wave 4 recorded as a prerequisite for both debts;
* `MarkovBridge.alphaMixCoeff_two_marginal_le_of_envelope` — an *inequality* form of
  Davydov's (2.58) at the α level, which needs **no** measurable Hahn selection and is
  therefore independent of the one still-open brick of `MarkovBridge.lean`;
* `MarkovBridge.alphaMixCoeff_le_of_measurable_state` /
  `MarkovBridge.betaMixCoeff_le_of_measurable_state` — the process-vs-state comparison
  `α_X(n) ≤ α_V(n−1)` (resp. β), for `X_s` a measurable function of the state `V_{s+1}`;
* `MarkovBridge.alphaCoeff_le_of_state_envelope` — their composite:
  `α_X(n) ≤ (∫ A dF) ρ^{n−1}`;
* `ForMathlib/Markov/IFSMinorization.lean` — `hasMinorization_sclAR_pow`, the minorization
  for the **multiplicative** recursion `X_t = f(𝐗) + s(𝐗)·ε_t`, which is what the GARCH
  obstruction note identified as the sharp missing ingredient. (Its docstring records that
  ARCH(p) is covered verbatim in *signed* coordinates and that GARCH(p, q) with `q ≥ 1`
  additionally needs a two-block state update.)

Consequently each of the two debts is now reduced to **one named model-side brick**: the
existence of the state chain together with its geometric total-variation envelope. The
step from that brick to the frozen FY statement is proved below. -/


/-! #### The state-chain brick, and the two model debts over it -/

/-- The *shape* of the model-side input that both debts now reduce to: the model's **state
chain**, together with its geometric total-variation envelope. Concretely: a state process
`V` with values in some `ℝ^k`, whose one-step law is a Markov kernel `κ`, whose observed
series `X_s` is a measurable function of the *next* state `V_{s+1}` (that is where the
fresh innovation is recorded), whose one-dimensional marginals do not depend on time, and
whose `m`-step law converges to the stationary law `F = μ ∘ V_0⁻¹` in total variation at a
geometric rate with an `F`-integrable constant.

Everything downstream of this is proved (`MarkovBridge.alphaCoeff_le_of_state_envelope`);
everything upstream is model-specific. -/
def HasGeometricStateChain (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ (k : ℕ) (V : ℤ → Ω → (Fin k → ℝ))
    (κ : ProbabilityTheory.Kernel (Fin k → ℝ) (Fin k → ℝ)),
    ProbabilityTheory.IsMarkovKernel κ ∧
    (∀ t, Measurable (V t)) ∧
    (∀ s t : ℤ, μ.map (V s) = μ.map (V t)) ∧
    IsMarkovOf V κ μ ∧
    (∀ s : ℤ, Measurable[MeasurableSpace.comap (V (s + 1)) inferInstance] (X s)) ∧
    ∃ (A : (Fin k → ℝ) → ℝ) (r : ℝ), (∀ x, 0 ≤ A x) ∧ Integrable A (μ.map (V 0)) ∧
      0 ≤ r ∧ r < 1 ∧
      ∀ (x : Fin k → ℝ) (m : ℕ),
        StatLean.Minimaxity.tvDist ((κ ^ m) x) (μ.map (V 0)) ≤ ENNReal.ofReal (A x * r ^ m)

/-- **From a geometrically ergodic state chain to exponential α-mixing of the observed
series.** This is the whole `Mixing`-side content of FY §2.6.1(v) and (x); it is proved
from `MarkovBridge.alphaCoeff_le_of_state_envelope` plus the bookkeeping that turns the
lag shift `ρ^{n−1}` and the junk value at `n = 0` into the frozen `C · r^n` shape. -/
theorem alphaCoeff_exponential_of_hasGeometricStateChain [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hchain : HasGeometricStateChain X μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n : ℕ, alphaCoeff X μ n ≤ C * r ^ n := by
  obtain ⟨k, V, κ, hκ, hVm, hmarg, hmarkov, hXV, A, ρ, hA0, hAint, hρ0, hρ1, henv⟩ := hchain
  haveI := hκ
  obtain ⟨I, hIdef⟩ : ∃ t : ℝ, t = ∫ x, A x ∂(μ.map (V 0)) := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := hIdef ▸ integral_nonneg hA0
  obtain ⟨r, hrdef⟩ : ∃ t : ℝ, t = max ρ (1 / 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := hrdef ▸ lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr1 : r < 1 := hrdef ▸ max_lt hρ1 (by norm_num)
  have hρr : ρ ≤ r := hrdef ▸ le_max_left _ _
  refine ⟨max (I / r) 1, le_trans zero_le_one (le_max_right _ _), r, hr0.le, hr1, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine le_trans alphaMixCoeff_le_one ?_
    simpa using le_max_right (I / r) 1
  · have hstep := alphaCoeff_le_of_state_envelope hVm hXV hmarg hmarkov hA0 hAint hρ0 henv hn
    rw [← hIdef] at hstep
    refine hstep.trans (le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left (I / r) 1)
      (pow_nonneg hr0.le n)))
    have hpow : I * ρ ^ (n - 1) ≤ I * r ^ (n - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρr _) hI0
    refine hpow.trans (le_of_eq ?_)
    have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    have hpr : r ^ n = r ^ (n - 1) * r := by
      conv_lhs => rw [← hn1]
      rw [pow_succ]
    rw [hpr]
    field_simp

/-- **From a geometrically ergodic state chain to exponential β-mixing of the observed
series** — the β-analogue of `alphaCoeff_exponential_of_hasGeometricStateChain`, proved
from `MarkovBridge.betaCoeff_le_of_state_envelope`. It became available once the `≤` half
of Davydov's identity (`MarkovBridge.betaMixCoeff_two_marginal_le_of_envelope`) was proved;
the still-open `≥` half is not needed. -/
theorem betaCoeff_exponential_of_hasGeometricStateChain [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hchain : HasGeometricStateChain X μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ n : ℕ, betaCoeff X μ n ≤ C * r ^ n := by
  obtain ⟨k, V, κ, hκ, hVm, hmarg, hmarkov, hXV, A, ρ, hA0, hAint, hρ0, hρ1, henv⟩ := hchain
  haveI := hκ
  obtain ⟨I, hIdef⟩ : ∃ t : ℝ, t = ∫ x, A x ∂(μ.map (V 0)) := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := hIdef ▸ integral_nonneg hA0
  obtain ⟨r, hrdef⟩ : ∃ t : ℝ, t = max ρ (1 / 2) := ⟨_, rfl⟩
  have hr0 : 0 < r := hrdef ▸ lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr1 : r < 1 := hrdef ▸ max_lt hρ1 (by norm_num)
  have hρr : ρ ≤ r := hrdef ▸ le_max_left _ _
  refine ⟨max (I / r) 1, le_trans zero_le_one (le_max_right _ _), r, hr0.le, hr1, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hXm : ∀ s : ℤ, Measurable (X s) := fun s =>
      (hXV s).mono (hVm (s + 1)).comap_le le_rfl
    refine le_trans (betaMixCoeff_le_one (mΩ := (inferInstance : MeasurableSpace Ω))
      (iSup₂_le fun s _ => (hXm s).comap_le) (iSup₂_le fun s _ => (hXm s).comap_le)) ?_
    simpa using le_max_right (I / r) 1
  · have hstep := betaCoeff_le_of_state_envelope hVm hXV hmarg hmarkov hA0 hAint hρ0 henv hn
    rw [← hIdef] at hstep
    refine hstep.trans (le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left (I / r) 1)
      (pow_nonneg hr0.le n)))
    have hpow : I * ρ ^ (n - 1) ≤ I * r ^ (n - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ0 hρr _) hI0
    refine hpow.trans (le_of_eq ?_)
    have hn1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn
    have hpr : r ^ n = r ^ (n - 1) * r := by
      conv_lhs => rw [← hn1]
      rw [pow_succ]
    rw [hpr]
    field_simp

/-! #### The invariant moment bound of a Lyapunov drift (wave 6)

The one *genuinely new* ingredient of the named follow-up
*"`IsGeometricallyErgodic` with a Lyapunov envelope"*, which the two (since removed)
state-chain bricks listed as an open input. The other ingredient — the envelope proper — is
already proved inside `harris_theorem` and only needs exporting; wave 5 was wrong to treat
this one as free. Proved here, axiom-clean, so that only the *export* is left outside this
lane's touch set. -/

/-- Truncations of a finite `ℝ≥0∞` value exhaust it. -/
private lemma iSup_min_natCast_of_ne_top {a : ENNReal} (ha : a ≠ ⊤) :
    ⨆ n : ℕ, min a (n : ENNReal) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ha
  exact le_iSup_of_le n (le_min le_rfl hn.le)

/-- **The invariant measure of a Lyapunov drift has a finite `V`-moment**:
`∫ V dπ ≤ K/(1 − γ)`.

This is *not* an output of `harris_theorem` (which returns only invariance and
`IsGeometricallyErgodic`, and `IsErgodicWithRate` carries just a pointwise limit), and it is
*not* reachable from the drift and invariance alone by the naive truncation: the pointwise
step `(γV + K) ∧ n ≤ γ(V ∧ n) + K` **fails** on `{V > n}` as soon as `n > K/(1 − γ)`. The
proof below therefore consumes the *ergodic limit*: each truncation `V ∧ n` is bounded, so
`StatLean.Bayesian.lintegral_le_lintegral_add_tvDist` transfers its `π`-integral to the
chain started at any `x₀` at a cost `n · tvDist ((κ^m) x₀) π → 0`, while
`HasLyapunovDrift.lintegral_pow_le` bounds `∫⁻ V d((κ^m) x₀)` by
`γ^m V(x₀) + K/(1 − γ)` uniformly in `m`; monotone convergence in `n` finishes. -/
private theorem lintegral_lyap_le_of_isErgodicWithRate {S : Type*} [MeasurableSpace S]
    {κ : ProbabilityTheory.Kernel S S} [ProbabilityTheory.IsMarkovKernel κ]
    {V : S → ℝ} {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K)
    {π : Measure S} [IsProbabilityMeasure π] {ρ : ENNReal}
    (herg : IsErgodicWithRate κ π ρ) (x₀ : S) :
    ∫⁻ y, ENNReal.ofReal (V y) ∂π ≤ ENNReal.ofReal (K / (1 - γ)) := by
  obtain ⟨hγ0, hγ1⟩ := hdrift.gamma_mem
  have hVm : Measurable V := hdrift.V_measurable
  have h1γ : (0:ℝ) < 1 - γ := by linarith
  have hK : (0:ℝ) ≤ K := hdrift.K_nonneg
  have hprob : ∀ (m : ℕ), IsProbabilityMeasure ((κ ^ m) x₀) := by
    intro m
    haveI : ProbabilityTheory.IsMarkovKernel (κ ^ m) := by
      induction m with
      | zero =>
          rw [pow_zero]
          exact (inferInstance : ProbabilityTheory.IsMarkovKernel
            (ProbabilityTheory.Kernel.id : ProbabilityTheory.Kernel S S))
      | succ k ih =>
          rw [pow_succ]
          exact ProbabilityTheory.Kernel.IsMarkovKernel.comp (κ ^ k) κ
    infer_instance
  have htv : Tendsto (fun m : ℕ => StatLean.Minimaxity.tvDist ((κ ^ m) x₀) π) atTop (𝓝 0) :=
    herg.tendsto_tvDist x₀
  have hWm : ∀ n : ℕ, Measurable fun y => min (ENNReal.ofReal (V y)) (n : ENNReal) :=
    fun n => (hVm.ennreal_ofReal).min measurable_const
  have key : ∀ n : ℕ, ∫⁻ y, min (ENNReal.ofReal (V y)) (n : ENNReal) ∂π
      ≤ ENNReal.ofReal (K / (1 - γ)) := by
    intro n
    have hstep : ∀ m : ℕ, ∫⁻ y, min (ENNReal.ofReal (V y)) (n : ENNReal) ∂π
        ≤ ENNReal.ofReal (γ ^ m * V x₀ + K / (1 - γ))
          + (n : ENNReal) * StatLean.Minimaxity.tvDist ((κ ^ m) x₀) π := by
      intro m
      haveI := hprob m
      have htransfer := StatLean.Bayesian.lintegral_le_lintegral_add_tvDist
        π ((κ ^ m) x₀) (hWm n) (B := (n : ENNReal)) (fun _ => min_le_right _ _)
      have hdrm : ∫⁻ y, min (ENNReal.ofReal (V y)) (n : ENNReal) ∂((κ ^ m) x₀)
          ≤ ENNReal.ofReal (γ ^ m * V x₀ + K / (1 - γ)) :=
        le_trans (lintegral_mono fun _ => min_le_left _ _) (hdrift.lintegral_pow_le m x₀)
      refine htransfer.trans ?_
      rw [StatLean.Minimaxity.tvDist_comm π ((κ ^ m) x₀)]
      exact add_le_add hdrm le_rfl
    have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (γ ^ m * V x₀ + K / (1 - γ))
        + (n : ENNReal) * StatLean.Minimaxity.tvDist ((κ ^ m) x₀) π) atTop
        (𝓝 (ENNReal.ofReal (K / (1 - γ)))) := by
      have h1 : Tendsto (fun m : ℕ => ENNReal.ofReal (γ ^ m * V x₀ + K / (1 - γ))) atTop
          (𝓝 (ENNReal.ofReal (K / (1 - γ)))) := by
        have hp : Tendsto (fun m : ℕ => γ ^ m * V x₀ + K / (1 - γ)) atTop
            (𝓝 (0 * V x₀ + K / (1 - γ))) :=
          ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1).mul_const _).add_const _
        simpa using! (ENNReal.continuous_ofReal.tendsto _).comp hp
      have h2 : Tendsto (fun m : ℕ =>
          (n : ENNReal) * StatLean.Minimaxity.tvDist ((κ ^ m) x₀) π) atTop (𝓝 0) := by
        simpa using ENNReal.Tendsto.const_mul htv (Or.inr (by simp))
      simpa using h1.add h2
    exact ge_of_tendsto hlim (Eventually.of_forall hstep)
  have hsup : ∫⁻ y, ENNReal.ofReal (V y) ∂π
      = ⨆ n : ℕ, ∫⁻ y, min (ENNReal.ofReal (V y)) (n : ENNReal) ∂π := by
    rw [← lintegral_iSup hWm]
    · refine lintegral_congr fun y => ?_
      exact (iSup_min_natCast_of_ne_top (a := ENNReal.ofReal (V y)) ENNReal.ofReal_ne_top).symm
    · intro m n hmn y
      exact min_le_min le_rfl (by exact_mod_cast Nat.cast_le.mpr hmn)
  rw [hsup]
  exact iSup_le key

/-- The form `HasGeometricStateChain` actually consumes: the Lyapunov function of a drift is
`π`-**integrable** whenever the kernel is ergodic with a rate. Together with the (already
proved, not yet exported) envelope of `harris_theorem` this is exactly the integrable
constant `A` of `HasGeometricStateChain`. -/
private theorem integrable_lyap_of_isErgodicWithRate {S : Type*} [MeasurableSpace S]
    {κ : ProbabilityTheory.Kernel S S} [ProbabilityTheory.IsMarkovKernel κ]
    {V : S → ℝ} {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K)
    {π : Measure S} [IsProbabilityMeasure π] {ρ : ENNReal}
    (herg : IsErgodicWithRate κ π ρ) (x₀ : S) :
    Integrable V π := by
  refine ⟨hdrift.V_measurable.aestronglyMeasurable, ?_⟩
  have he : ∀ y, ‖V y‖ₑ = ENNReal.ofReal (V y) := fun y => by
    rw [Real.enorm_eq_ofReal (hdrift.V_nonneg y)]
  rw [HasFiniteIntegral, lintegral_congr he]
  exact lt_of_le_of_lt (lintegral_lyap_le_of_isErgodicWithRate hdrift herg x₀)
    ENNReal.ofReal_lt_top

/-- **The quantitative Harris envelope, in the form `HasGeometricStateChain` consumes.**

Drift + minorization give an invariant probability measure `π` together with an
**`π`-integrable** dominating constant `A` and a rate `r < 1` such that
`‖κᵐ(x, ·) − π‖_TV ≤ A(x) rᵐ` for every state `x` and every `m`.

This closes, as one theorem, the named follow-up *"`IsGeometricallyErgodic` with a Lyapunov
envelope"* that the two (since removed) state-chain bricks, for ARMA and for GARCH, listed
as an open input. Its two parts:

* the envelope itself — `harris_theorem_envelope`, the statement-level export (added in
  `ForMathlib/Markov/HarrisTheorem.lean`) of the step `hbound` that Harris' theorem already
  proves internally and then discards. It returns `A` **affine in the Lyapunov function**,
  `A x = c + b · V x`;
* the integrability of that `A` — `integrable_lyap_of_isErgodicWithRate` above, i.e.
  `∫ V dπ < ∞`, which is *not* an output of Harris' theorem and is not reachable from drift
  plus invariance by the naive truncation (see `lintegral_lyap_le_of_isErgodicWithRate`).

`IsGeometricallyErgodic` alone is strictly weaker than this: it carries only the pointwise
rate `ρ⁻ᵐ ‖κᵐ(x, ·) − π‖_TV → 0`, with no `x`-uniform integrable constant, and FY eq. (2.59)
cannot be integrated against it. -/
theorem exists_invariant_geometric_envelope_of_harris {S : Type*} [MeasurableSpace S]
    {κ : ProbabilityTheory.Kernel S S} [ProbabilityTheory.IsMarkovKernel κ]
    {V : S → ℝ} {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K)
    {R α : ℝ} {ν : Measure S} (hmin : HasMinorization κ V R α ν)
    (hR : 2 * K / (1 - γ) < R) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ ProbabilityTheory.Kernel.Invariant κ π ∧
      ∃ (A : S → ℝ) (r : ℝ), (∀ x, 0 ≤ A x) ∧ Integrable A π ∧ 0 ≤ r ∧ r < 1 ∧
        ∀ (x : S) (m : ℕ),
          StatLean.Minimaxity.tvDist ((κ ^ m) x) π ≤ ENNReal.ofReal (A x * r ^ m) := by
  haveI := hmin.isProbability
  -- the state space is nonempty: it carries the minorizing probability measure
  haveI hne : Nonempty S := by
    rcases isEmpty_or_nonempty S with h | h
    · exact absurd (measure_univ (μ := ν))
        (by rw [Set.univ_eq_empty_iff.2 h, measure_empty]; exact zero_ne_one)
    · exact h
  obtain ⟨x₀⟩ := id hne
  obtain ⟨π, hπprob, hinv, hge, b, c, r, hb0, hc0, hr0, hr1, henv⟩ :=
    harris_theorem_envelope hdrift hmin hR
  haveI := hπprob
  obtain ⟨ρ, _, herg⟩ := hge
  have hVint : Integrable V π := integrable_lyap_of_isErgodicWithRate hdrift herg x₀
  refine ⟨π, hπprob, hinv, fun x => c + b * V x, r, fun x =>
    add_nonneg hc0 (mul_nonneg hb0 (hdrift.V_nonneg x)), ?_, hr0, hr1, henv⟩
  exact (integrable_const c).add (hVint.const_mul b)

end Process2

end StatLean.TimeSeries
