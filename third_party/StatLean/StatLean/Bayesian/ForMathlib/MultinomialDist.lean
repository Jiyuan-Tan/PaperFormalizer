module
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.MeasureTheory.Measure.Count

@[expose] public section

/-!
# The multinomial distribution (counts of `n` trials over `m` categories)

The **multinomial distribution** `ℳ_m(n; q₁, …, q_m)`: the law of the counts vector
`v : Fin m → ℕ` of `n` independent trials over `m` categories with probability vector `q`,
$$f(v \mid q) = \binom{n}{v_1\,\cdots\,v_m} \prod_{i=1}^m q_i^{v_i}
  \quad\text{on } \textstyle\sum_i v_i = n .$$
We define the weight (pmf against counting measure), the parametrized kernel over `q : Fin m → ℝ`,
and prove its total mass is `1` exactly on the probability simplex (multinomial theorem) — off the
simplex the weight is defined to vanish, so the kernel is finite (sub-Markov) rather than Markov;
the Bayesian machinery of this area only needs `IsFiniteKernel`.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §3.4
(multinomial model), p. 69.

**Proof formalization notes.** Pinned Mathlib has `Nat.multinomial` and the multinomial theorem
`Finset.sum_pow_eq_sum_piAntidiag` but no multinomial *distribution* — built here (candidate for
upstreaming). The counts space `Fin m → ℕ` is countable with singletons measurable, so
`Measure.count` is σ-finite and the kernel is `Kernel.withDensity (Kernel.const _ Measure.count)`;
mass-on-simplex uses `tsum_eq_sum` over the finite support `Finset.piAntidiag univ n`. The weight
takes real `q` and clamps by the simplex indicator: junk value `0` off `{q | (∀ i, 0 ≤ q i) ∧
∑ q i = 1 ∧ ∑ v i = n}`.

**Bibliographic comments.** The multinomial law goes back to the earliest combinatorial
probability (J. Bernoulli, *Ars Conjectandi*, 1713; A. De Moivre, *The Doctrine of Chances*,
1718), the multinomial coefficient being the enumeration of arrangements. It is the canonical
finite-category sampling model, conjugate to the Dirichlet prior.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- **Multinomial weight** (pmf against counting measure): `multinomial coefficient × ∏ qᵢ^{vᵢ}`
on the event `{∑ vᵢ = n}` when `q` lies in the probability simplex, and `0` otherwise
(Gelman §3.4). -/
noncomputable def multinomialWeight (m n : ℕ) (q : Fin m → ℝ) : (Fin m → ℕ) → ℝ≥0∞ :=
  fun v =>
    if (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧ ∑ i, v i = n then
      ENNReal.ofReal ((Nat.multinomial Finset.univ v : ℝ) * ∏ i, q i ^ v i)
    else 0

/-- Joint measurability of the multinomial weight in `(q, v)`. -/
theorem measurable_uncurry_multinomialWeight (m n : ℕ) :
    Measurable (Function.uncurry (multinomialWeight m n)) := by
  apply measurable_from_prod_countable_left
  intro v
  simp only [Function.uncurry_apply_pair, multinomialWeight]
  refine Measurable.ite ?_ ?_ measurable_const
  · -- the condition set in `q` (the `∑ v = n` conjunct is `q`-independent)
    have hA : MeasurableSet {q : Fin m → ℝ | ∀ i, 0 ≤ q i} := by
      rw [Set.setOf_forall]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le measurable_const (measurable_pi_apply i)
    have hB : MeasurableSet {q : Fin m → ℝ | ∑ i, q i = 1} :=
      (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i) (measurableSet_singleton 1)
    have hC : MeasurableSet {_q : Fin m → ℝ | ∑ i, v i = n} :=
      measurable_const (measurableSet_singleton n)
    simp only [Set.setOf_and]
    exact hA.inter (hB.inter hC)
  · exact (((Finset.univ.measurable_prod
      fun i _ => (measurable_pi_apply i).pow_const (v i)).const_mul
      (Nat.multinomial Finset.univ v : ℝ)).ennreal_ofReal)

/-- The **multinomial kernel** `q ↦ ℳ_m(n; q)` over the full parameter vector `q : Fin m → ℝ`
(mass `1` on the simplex, `0` off it — sub-Markov junk documented in the module docstring). -/
noncomputable def multinomialKernel (m n : ℕ) : Kernel (Fin m → ℝ) (Fin m → ℕ) :=
  Kernel.withDensity (Kernel.const _ Measure.count) (multinomialWeight m n)

/-- On the probability simplex, the multinomial masses sum to `1` (multinomial theorem). -/
theorem multinomialKernel_apply_univ_of_mem_simplex (m n : ℕ) {q : Fin m → ℝ}
    -- USER-INPUT: `q` is a probability vector; Gelman §3.4
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∑ i, q i = 1) :
    multinomialKernel m n q Set.univ = 1 := by
  rw [multinomialKernel, Kernel.withDensity_apply' _ (measurable_uncurry_multinomialWeight m n),
    Kernel.const_apply, Measure.restrict_univ, lintegral_count]
  -- terms vanish outside the finite support `piAntidiag univ n`
  have hsupp : ∀ v ∉ Finset.piAntidiag Finset.univ n, multinomialWeight m n q v = 0 := by
    intro v hv
    have hne : ∑ i, v i ≠ n := fun h =>
      hv (Finset.mem_piAntidiag.mpr ⟨h, fun i _ => Finset.mem_univ i⟩)
    simp only [multinomialWeight]
    rw [if_neg]
    rintro ⟨-, -, h3⟩
    exact hne h3
  rw [tsum_eq_sum hsupp]
  have hval : ∀ v ∈ Finset.piAntidiag Finset.univ n,
      multinomialWeight m n q v
        = ENNReal.ofReal ((Nat.multinomial Finset.univ v : ℝ) * ∏ i, q i ^ v i) := by
    intro v hv
    rw [Finset.mem_piAntidiag] at hv
    simp only [multinomialWeight]
    rw [if_pos ⟨hq0, hq1, hv.1⟩]
  rw [Finset.sum_congr rfl hval,
    ← ENNReal.ofReal_sum_of_nonneg (fun v _ =>
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun i _ => pow_nonneg (hq0 i) _)),
    ← Finset.sum_pow_eq_sum_piAntidiag, hq1, one_pow, ENNReal.ofReal_one]

/-- The multinomial kernel is a finite kernel (mass `≤ 1` everywhere). -/
instance (m n : ℕ) : IsFiniteKernel (multinomialKernel m n) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun q => ?_⟩⟩
  by_cases hs : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1
  · exact le_of_eq (multinomialKernel_apply_univ_of_mem_simplex m n hs.1 hs.2)
  · have hz : ∀ v, multinomialWeight m n q v = 0 := by
      intro v
      simp only [multinomialWeight]
      rw [if_neg]
      rintro ⟨h1, h2, -⟩
      exact hs ⟨h1, h2⟩
    have : multinomialKernel m n q Set.univ = 0 := by
      rw [multinomialKernel,
        Kernel.withDensity_apply' _ (measurable_uncurry_multinomialWeight m n),
        Kernel.const_apply, Measure.restrict_univ, lintegral_count]
      simp only [hz, tsum_zero]
    exact this ▸ (zero_le (a := 1))

/-- Pointwise value on singletons: the pmf formula. -/
theorem multinomialKernel_apply_singleton (m n : ℕ) (q : Fin m → ℝ) (v : Fin m → ℕ) :
    multinomialKernel m n q {v} = multinomialWeight m n q v := by
  rw [multinomialKernel, Kernel.withDensity_apply' _ (measurable_uncurry_multinomialWeight m n),
    Kernel.const_apply, lintegral_singleton, Measure.count_singleton, mul_one]

end StatLean.Bayesian
