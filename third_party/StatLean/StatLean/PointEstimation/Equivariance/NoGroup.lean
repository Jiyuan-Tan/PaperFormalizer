module
public import StatLean.PointEstimation.Equivariance.Defs
public import Mathlib.MeasureTheory.Measure.Count

@[expose] public section

/-!
# A family with no nontrivial invariance

The equivariance principle is only available when the model admits symmetries. This file
exhibits a family for which it is not: the **power series family** on `ℕ`,

`P_θ{X = k} = c_k θ^k h(θ)`,   `k = 0, 1, 2, …`,  `θ > 0`,

with all coefficients `c_k` strictly positive. For such a family the *only* bijection of
the sample space leaving the family invariant is the identity, so the invariance group is
trivial and the equivariance principle has no content.

* `powerSeriesFamily` — the family, as a density with respect to the counting measure on
  `ℕ`, normalized by the total sum;
* `powerSeriesFamily_invariant_affine` — the structural step: an invariance-preserving
  bijection has constant successive increments;
* `powerSeriesFamily_invariant_perm_eq_one` — the conclusion: such a bijection is the
  identity;
* `powerSeriesFamily_invariantPerms_eq_singleton` — the same statement packaged as "the
  set of invariance-preserving permutations is `{1}`".

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.2 (The
Principle of Equivariance), Theorem 2.17 (the power-series family application, where the
invariance group is trivial). (`TPE2 §3.2 Thm 2.17`.)

**Proof formalization notes.**
* The classical conclusion really is the general "the transformation is the identity"
  claim (not a two-point comparison), so it is transcribed as such, with the bijection
  modelled as `Equiv.Perm ℕ`.
* The argument runs as follows. Write `a_k = g(k)`. Matching point masses gives
  `c_k θ^k h(θ) = c_{a_k} μ^{a_k} h(μ)` for the transported parameter `μ`; taking ratios
  of consecutive `k` twice shows `μ^{a_{k+2} − a_{k+1}}` is proportional to
  `μ^{a_{k+1} − a_k}` *throughout an interval of `μ`*, whence the exponents agree and
  `a_k = a_0 + kΔ`. Being a permutation of `ℕ` forces `Δ = 1` and `a_0 = 0`.
* Because the exponent-matching step needs `μ` to range over an interval, the parameter
  set is taken to be an interval `Ioo 0 R` on which the series converges, rather than the
  informal "`0 < θ < ∞`". The increments are recorded in `ℤ`, since `ℕ`-subtraction would
  truncate and the increments are not known to be nonnegative before the final step.
* The strict positivity of every coefficient is essential and not cosmetic: when
  `c_k = 0` for all `k` beyond some threshold the conclusion fails — the binomial family
  is invariant under `k ↦ n − k`, whose induced parameter map is `p ↦ 1 − p`.
* Edge behaviour of `powerSeriesFamily`: the normalizer is the total sum
  `∑' j, c_j θ^j`, so the definition returns the zero measure where the series diverges
  and the junk `∞`-valued density where it vanishes. Theorems carry the convergence
  hypothesis.

**Bibliographic comments.** The group-theoretic framework in which "the model admits no
nontrivial symmetries" is the relevant negative statement is due to G. A. Hunt and
C. Stein (unpublished manuscript, 1946), first reported in print by M. A. Girshick and
L. J. Savage, "Bayes and minimax estimates for quadratic loss functions," *Proc. Second
Berkeley Symp. Math. Statist. Probab.*, Univ. California Press, 1951, 53–73.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.PointEstimation

/-- The **power series family** on `ℕ` with coefficients `a`: the law with density
`k ↦ a k · θ^k / ∑' j, a j · θ^j` with respect to the counting measure.

The normalizer is the total sum, so this is a probability measure exactly where that sum
is finite and nonzero; elsewhere the definition takes the junk value coming from
`ℝ≥0∞`-division (zero measure when the sum is infinite, `∞`-valued density when it
vanishes). Theorems carry the corresponding convergence hypotheses. -/
noncomputable def powerSeriesFamily (a : ℕ → ℝ≥0∞) (θ : ℝ) : Measure ℕ :=
  Measure.count.withDensity fun k =>
    (a k * (ENNReal.ofReal θ) ^ k) / (∑' j, a j * (ENNReal.ofReal θ) ^ j)

/-- Point mass of the power series family at `{k}`: the density value. -/
private lemma powerSeriesFamily_singleton (a : ℕ → ℝ≥0∞) (θ : ℝ) (k : ℕ) :
    powerSeriesFamily a θ {k}
      = (a k * (ENNReal.ofReal θ) ^ k) / (∑' j, a j * (ENNReal.ofReal θ) ^ j) := by
  unfold powerSeriesFamily
  rw [withDensity_apply _ (measurableSet_singleton k),
    ← lintegral_indicator (measurableSet_singleton k), lintegral_count,
    tsum_eq_single k fun b hb => Set.indicator_of_notMem (by simpa using hb) _]
  exact Set.indicator_of_mem (Set.mem_singleton_iff.mpr rfl) _

/-- A linear relation `α · log θ = C` holding throughout an interval of `θ`, with `C`
independent of `θ`, forces `α = 0` (`log` is nonconstant on any interval of positives). -/
private lemma eq_zero_of_mul_log_eq_const {R C : ℝ} (hR : 0 < R) {α : ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) R, α * Real.log θ = C) : α = 0 := by
  have h2 := h (R / 2) ⟨by linarith, by linarith⟩
  have h3 := h (R / 3) ⟨by linarith, by linarith⟩
  have hlog : Real.log (R / 2) ≠ Real.log (R / 3) := by
    intro he
    have hRR : R / 2 = R / 3 :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) he
    exact absurd (by linarith : R = 0) hR.ne'
  have hd : α * (Real.log (R / 2) - Real.log (R / 3)) = 0 := by
    rw [mul_sub, h2, h3, sub_self]
  rcases mul_eq_zero.mp hd with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hlog

/-- Analytic core of `powerSeriesFamily_invariant_affine`: density matching plus the
coefficient-ratio / exponent arithmetic-progression argument.

Matching point masses of `(P θ).map g = P θ'` gives, for every `k`,
`a k · θ^k / Z(θ) = a (g k) · θ'^(g k) / Z(θ')`. Passing to positive reals and taking
`log`, the equation for index `k` minus that for index `0` reads
`(log Rₖ − log R₀) + k·log θ = (log R_{gk} − log R_{g0}) + (gk − g0)·log θ'`,
where `Rᵢ = (a i).toReal`. Eliminating `log θ'` between the relations for indices `k` and
`1` (a linear combination) yields `(e·k − (gk−g0))·log θ = C` with `e = g1 − g0` and `C`
independent of `θ`; as this holds throughout the interval, `e·k = gk − g0`, i.e.
`gk = g0 + k·e`, so `g(k+1) − gk = e` is constant. -/
private theorem powerSeriesFamily_invariant_affine_core {a : ℕ → ℝ≥0∞}
    (ha₀ : ∀ k, a k ≠ 0) (ha : ∀ k, a k ≠ ∞) {R : ℝ} (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞)
    (g : Equiv.Perm ℕ)
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ') :
    ∃ d : ℤ, ∀ k : ℕ, (g (k + 1) : ℤ) - (g k : ℤ) = d := by
  classical
  -- real coefficients, all strictly positive
  set Rr : ℕ → ℝ := fun i => (a i).toReal with hRr
  have hRrpos : ∀ i, 0 < Rr i := fun i => ENNReal.toReal_pos (ha₀ i) (ha i)
  have hgmeas : Measurable (g : ℕ → ℕ) := measurable_of_countable _
  have hpre : ∀ j : ℕ, (g : ℕ → ℕ) ⁻¹' {g j} = {j} := by
    intro j; ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, g.injective.eq_iff]
  -- the leftmost increment
  set e : ℤ := (g 1 : ℤ) - (g 0 : ℤ) with hedef
  -- the closed form `g k = g 0 + k · e`
  have hform : ∀ k : ℕ, (g k : ℤ) = (g 0 : ℤ) + (k : ℤ) * e := by
    intro k
    -- per-`θ` log-linear relation, then eliminate `log θ'` and pass to the interval
    have hα : ((g 1 : ℝ) - (g 0 : ℝ)) * (k : ℝ) - ((g k : ℝ) - (g 0 : ℝ)) = 0 := by
      refine eq_zero_of_mul_log_eq_const (C :=
        ((g 1 : ℝ) - (g 0 : ℝ)) * (Real.log (Rr (g k)) - Real.log (Rr (g 0)))
          - ((g k : ℝ) - (g 0 : ℝ)) * (Real.log (Rr (g 1)) - Real.log (Rr (g 0)))
          - ((g 1 : ℝ) - (g 0 : ℝ)) * (Real.log (Rr k) - Real.log (Rr 0))
          + ((g k : ℝ) - (g 0 : ℝ)) * (Real.log (Rr 1) - Real.log (Rr 0))) hR ?_
      intro θ hθ
      obtain ⟨θ', hθ'mem, hmap⟩ := hg θ hθ
      -- point-mass matching, then to positive reals
      have hmatch : ∀ j : ℕ,
          (a j * (ENNReal.ofReal θ) ^ j) / (∑' i, a i * (ENNReal.ofReal θ) ^ i)
            = (a (g j) * (ENNReal.ofReal θ') ^ (g j))
              / (∑' i, a i * (ENNReal.ofReal θ') ^ i) := by
        intro j
        have h1 : ((powerSeriesFamily a θ).map (g : ℕ → ℕ)) {g j}
            = powerSeriesFamily a θ' {g j} := by rw [hmap]
        rw [Measure.map_apply hgmeas (measurableSet_singleton (g j)), hpre j,
          powerSeriesFamily_singleton, powerSeriesFamily_singleton] at h1
        exact h1
      -- positivity of the normalisers as reals
      set Wθ : ℝ := (∑' i, a i * (ENNReal.ofReal θ) ^ i).toReal with hWθ
      set Wθ' : ℝ := (∑' i, a i * (ENNReal.ofReal θ') ^ i).toReal with hWθ'
      have hZθ0 : (∑' i, a i * (ENNReal.ofReal θ) ^ i) ≠ 0 := by
        refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum 0))
        simpa using (pos_iff_ne_zero.mpr (ha₀ 0))
      have hZθ'0 : (∑' i, a i * (ENNReal.ofReal θ') ^ i) ≠ 0 := by
        refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum 0))
        simpa using (pos_iff_ne_zero.mpr (ha₀ 0))
      have hWθpos : 0 < Wθ := ENNReal.toReal_pos hZθ0 (hconv θ hθ)
      have hWθ'pos : 0 < Wθ' := ENNReal.toReal_pos hZθ'0 (hconv θ' hθ'mem)
      -- real division form of the matching
      have hRE : ∀ j : ℕ, Rr j * θ ^ j / Wθ = Rr (g j) * θ' ^ (g j) / Wθ' := by
        intro j
        have := congrArg ENNReal.toReal (hmatch j)
        rwa [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofReal hθ.1.le,
          ENNReal.toReal_ofReal hθ'mem.1.le] at this
      -- log-linear relation for each index
      have hLG : ∀ j : ℕ, Real.log (Rr j) + (j : ℝ) * Real.log θ - Real.log Wθ
          = Real.log (Rr (g j)) + (g j : ℝ) * Real.log θ' - Real.log Wθ' := by
        intro j
        have hnum : Rr j * θ ^ j ≠ 0 :=
          ne_of_gt (mul_pos (hRrpos j) (pow_pos hθ.1 j))
        have hnum' : Rr (g j) * θ' ^ (g j) ≠ 0 :=
          ne_of_gt (mul_pos (hRrpos (g j)) (pow_pos hθ'mem.1 (g j)))
        have := congrArg Real.log (hRE j)
        rwa [Real.log_div hnum hWθpos.ne', Real.log_div hnum' hWθ'pos.ne',
          Real.log_mul (hRrpos j).ne' (pow_ne_zero _ hθ.1.ne'),
          Real.log_mul (hRrpos (g j)).ne' (pow_ne_zero _ hθ'mem.1.ne'),
          Real.log_pow, Real.log_pow] at this
      -- differences against index 0 remove the normalisers; eliminate `log θ'`
      have hIk := hLG k
      have hI1 := hLG 1
      have hI0 := hLG 0
      -- combine: `e·(hLG k − hLG 0) − (gk−g0)·(hLG 1 − hLG 0)`
      linear_combination ((g 1 : ℝ) - (g 0 : ℝ)) * hIk - ((g k : ℝ) - (g 0 : ℝ)) * hI1
        - (((g 1 : ℝ) - (g 0 : ℝ)) - ((g k : ℝ) - (g 0 : ℝ))) * hI0
    -- turn the real identity into the integer closed form
    have hαr : (g k : ℝ) - (g 0 : ℝ) = ((g 1 : ℝ) - (g 0 : ℝ)) * (k : ℝ) := by linarith
    have : ((g k : ℤ) : ℝ) = (((g 0 : ℤ) + (k : ℤ) * e : ℤ) : ℝ) := by
      push_cast [hedef]; push_cast at hαr; linarith
    exact_mod_cast this
  -- conclude the constant increment
  refine ⟨e, fun k => ?_⟩
  rw [hform (k + 1), hform k]; push_cast; ring

/-- **Structural step towards triviality of the invariance group.** A bijection of the
sample space that maps every member of a power series family to another member has
constant successive increments, `g(k+1) − g(k) = Δ` for all `k`. -/
theorem powerSeriesFamily_invariant_affine {a : ℕ → ℝ≥0∞}
    -- USER-INPUT: every coefficient is strictly positive (the family has full support)
    (ha₀ : ∀ k, a k ≠ 0)
    -- LEAN-ONLY: coefficients are finite, so the densities are genuine real numbers
    (ha : ∀ k, a k ≠ ∞)
    {R : ℝ}
    -- USER-INPUT: the parameter ranges over an interval, on which the series converges
    (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞)
    (g : Equiv.Perm ℕ)
    -- USER-INPUT: `g` leaves the family invariant — it maps each member to a member
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ') :
    ∃ d : ℤ, ∀ k : ℕ, (g (k + 1) : ℤ) - (g k : ℤ) = d :=
  powerSeriesFamily_invariant_affine_core ha₀ ha hR hconv g hg

/-- **A power series family with strictly positive coefficients admits no nontrivial
symmetry of the sample space.** Any bijection of `ℕ` mapping every member of the family
to a member of the family is the identity.

Since the equivariance principle only has content relative to a group of transformations
leaving the model invariant, it is vacuous for such families. -/
theorem powerSeriesFamily_invariant_perm_eq_one {a : ℕ → ℝ≥0∞}
    -- USER-INPUT: every coefficient is strictly positive; the conclusion is false
    -- without this, as the binomial family shows
    (ha₀ : ∀ k, a k ≠ 0)
    -- LEAN-ONLY: coefficients are finite
    (ha : ∀ k, a k ≠ ∞)
    {R : ℝ}
    -- USER-INPUT: the parameter ranges over an interval, on which the series converges
    (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞)
    (g : Equiv.Perm ℕ)
    -- USER-INPUT: `g` leaves the family invariant
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ') :
    g = 1 := by
  obtain ⟨d, hd⟩ := powerSeriesFamily_invariant_affine ha₀ ha hR hconv g hg
  -- closed form of the (integer) values along the arithmetic progression
  have hform : ∀ k : ℕ, (g k : ℤ) = (g 0 : ℤ) + k * d := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      have hstep : (g (n + 1) : ℤ) = (g n : ℤ) + d := by linarith [hd n]
      rw [hstep, ih]; push_cast; ring
  have hnn : ∀ k : ℕ, (0 : ℤ) ≤ (g k : ℤ) := fun k => Int.natCast_nonneg _
  -- `d ≠ 0` (else `g` is not injective)
  have hd_ne : d ≠ 0 := by
    intro h0
    have h1 : (g 1 : ℤ) = (g 0 : ℤ) := by rw [hform 1, h0]; simp
    exact one_ne_zero (g.injective (by exact_mod_cast h1))
  -- `d > 0` (else the values eventually go negative)
  have hd_pos : 0 < d := by
    rcases lt_or_gt_of_ne hd_ne with hneg | hpos
    · exfalso
      have hk := hform (g 0 + 1)
      have hge := hnn (g 0 + 1)
      rw [hk] at hge
      push_cast at hge
      nlinarith [hnn 0, hge, hneg]
    · exact hpos
  -- `g 0 = 0` (surjectivity hits `0`)
  have hg0 : (g 0 : ℤ) = 0 := by
    obtain ⟨k, hk⟩ := g.surjective 0
    have := hform k
    rw [hk] at this
    push_cast at this
    nlinarith [hnn 0, mul_nonneg (Int.natCast_nonneg k) hd_pos.le, this]
  -- `d = 1` (surjectivity hits `1`)
  have hd1 : d = 1 := by
    obtain ⟨k, hk⟩ := g.surjective 1
    have hval := hform k
    rw [hk, hg0] at hval
    push_cast at hval
    -- `1 = k * d`, with `d > 0`, forces `d = 1`
    have hdvd : d ∣ 1 := ⟨(k : ℤ), by linarith [hval]⟩
    exact Int.eq_one_of_dvd_one hd_pos.le hdvd
  -- conclude `g = id`
  ext k
  have := hform k
  rw [hg0, hd1] at this
  simp only [Equiv.Perm.coe_one, id_eq]
  have hgk : (g k : ℤ) = (k : ℤ) := by rw [this]; ring
  exact_mod_cast hgk

/-- The invariance group of a power series family with strictly positive coefficients is
trivial: the set of permutations of the sample space leaving the family invariant is the
one-element set containing the identity. -/
theorem powerSeriesFamily_invariantPerms_eq_singleton {a : ℕ → ℝ≥0∞}
    -- USER-INPUT: every coefficient is strictly positive
    (ha₀ : ∀ k, a k ≠ 0)
    -- LEAN-ONLY: coefficients are finite
    (ha : ∀ k, a k ≠ ∞)
    {R : ℝ}
    -- USER-INPUT: the parameter ranges over an interval, on which the series converges
    (hR : 0 < R)
    (hconv : ∀ θ ∈ Set.Ioo (0 : ℝ) R, (∑' j, a j * (ENNReal.ofReal θ) ^ j) ≠ ∞) :
    {g : Equiv.Perm ℕ | ∀ θ ∈ Set.Ioo (0 : ℝ) R, ∃ θ' ∈ Set.Ioo (0 : ℝ) R,
      (powerSeriesFamily a θ).map (g : ℕ → ℕ) = powerSeriesFamily a θ'} = {1} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨fun θ hθ => ⟨θ, hθ, ?_⟩, ?_⟩
  · rw [Equiv.Perm.coe_one, Measure.map_id]
  · intro g hg
    exact powerSeriesFamily_invariant_perm_eq_one ha₀ ha hR hconv g hg

end StatLean.PointEstimation
