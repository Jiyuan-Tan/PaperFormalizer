module
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import StatLean.ExperimentalDesign.ForMathlib.PMFExpectation

@[expose] public section

/-!
# Product designs: independent randomization across strata

Blocked experiments and stratified surveys randomize **independently within each
block/stratum**.  The common probabilistic core is the finite product design: given
per-stratum designs `D b : PMF (Ω b)` over finitely many strata `b : B`, the product
design on `∀ b, Ω b` has mass `∏ b, D b (ω b)`.  This file constructs it and proves
the independence calculus that every blockwise moment computation reduces to:
factorization of expectations, marginals, vanishing covariance across strata, and
additivity of variances of stratum-wise sums:
$$\mathbb E\Bigl[\prod_b f_b(\omega_b)\Bigr] = \prod_b \mathbb E_{D_b}[f_b], \qquad
  \operatorname{Var}\Bigl(\sum_b f_b(\omega_b)\Bigr)
    = \sum_b \operatorname{Var}_{D_b}(f_b).$$

## Main results

* `productDesign`, `productDesign_apply` — the construction.
* `pmfExpect_productDesign_comp` — marginals.
* `pmfExpect_productDesign_prod` — factorization over strata.
* `pmfCov_productDesign_of_ne` — independence across strata.
* `pmfVar_productDesign_comp`, `pmfVar_productDesign_sum` — variance calculus.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988, §9.4:
"randomisation is independent in different blocks" — the property that kills the
cross-block terms in the randomisation-theory variance computations; §9.6 (practical
randomisation block by block).  (`Mead §9.4`, `Mead §9.6`.)

**Proof formalization notes.**
* Normalisation of the product mass is the finite Fubini identity
  `∑_{ω : ∀ b, Ω b} ∏ b, D b (ω b) = ∏ b, ∑_{x : Ω b}, D b x = 1` in `ℝ≥0∞`
  (`Finset.prod_univ_sum` shape), stated separately as `sum_prod_pmf` so the
  `PMF.ofFintype` obligation is a named lemma.
* All moment identities then follow from the same Fubini rearrangement in `ℝ`; the
  cross-stratum covariance vanishes because expectations factor.
* `pmfVar_productDesign_sum` combines `pmfVar_sum` with the vanishing off-diagonal
  covariances; it is the "no cross-block terms" step of `Mead §9.4`.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {Ω : B → Type*} [∀ b, Fintype (Ω b)] [∀ b, DecidableEq (Ω b)]

/-- Finite Fubini over a dependent product type, in any commutative semiring:
`∑_{ω ∈ ∏ Ω_b} ∏_b g_b(ω_b) = ∏_b ∑_x g_b(x)`. -/
private lemma sum_pi_prod {R : Type*} [CommSemiring R] (g : ∀ b, Ω b → R) :
    ∑ ω : ∀ b, Ω b, ∏ b, g b (ω b) = ∏ b, ∑ x, g b x := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

/-- Normalisation of the product mass: the total mass of `ω ↦ ∏ b, D b (ω b)` is
one (finite Fubini in `ℝ≥0∞`). -/
theorem sum_prod_pmf (D : ∀ b, PMF (Ω b)) :
    ∑ ω : ∀ b, Ω b, ∏ b, D b (ω b) = 1 := by
  refine (sum_pi_prod fun b => (D b : Ω b → ℝ≥0∞)).trans ?_
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]

/-- The **product design**: independent randomization across the strata, with mass
`∏ b, D b (ω b)` (`Mead §9.4`, independence of randomisation in different blocks). -/
noncomputable def productDesign (D : ∀ b, PMF (Ω b)) : PMF (∀ b, Ω b) :=
  PMF.ofFintype (fun ω => ∏ b, D b (ω b)) (sum_prod_pmf D)

@[simp]
theorem productDesign_apply (D : ∀ b, PMF (Ω b)) (ω : ∀ b, Ω b) :
    productDesign D ω = ∏ b, D b (ω b) :=
  rfl

/-- **Marginals of the product design**: a statistic of one stratum has its
single-stratum expectation. -/
theorem pmfExpect_productDesign_comp (D : ∀ b, PMF (Ω b)) (b₀ : B)
    (f : Ω b₀ → ℝ) :
    pmfExpect (productDesign D) (fun ω => f (ω b₀)) = pmfExpect (D b₀) f := by
  classical
  set F : ∀ b, Ω b → ℝ := Function.update (fun b => fun _ : Ω b => (1 : ℝ)) b₀ f
    with hF
  have hFb₀ : F b₀ = f := by rw [hF, Function.update_self]
  have hFne : ∀ b, b ≠ b₀ → F b = fun _ => (1 : ℝ) := fun b hb => by
    rw [hF, Function.update_of_ne hb]
  unfold pmfExpect
  calc ∑ ω : ∀ b, Ω b, (productDesign D ω).toReal * f (ω b₀)
      = ∑ ω : ∀ b, Ω b, ∏ b, ((D b (ω b)).toReal * F b (ω b)) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hprodF : (∏ b, F b (ω b)) = f (ω b₀) := by
          rw [Finset.prod_eq_single b₀ (fun b _ hb => by rw [hFne b hb])
            (fun h => absurd (Finset.mem_univ b₀) h), hFb₀]
        rw [productDesign_apply, ENNReal.toReal_prod, Finset.prod_mul_distrib, hprodF]
    _ = ∏ b, ∑ x, (D b x).toReal * F b x :=
        sum_pi_prod fun b x => (D b x).toReal * F b x
    _ = ∑ x, (D b₀ x).toReal * f x := by
        rw [Finset.prod_eq_single b₀ (fun b _ hb => by
            rw [hFne b hb]
            simpa using sum_pmf_toReal (D b))
          (fun h => absurd (Finset.mem_univ b₀) h), hFb₀]

/-- **Factorization over strata**: the expectation of a product of per-stratum
statistics is the product of expectations. -/
theorem pmfExpect_productDesign_prod (D : ∀ b, PMF (Ω b))
    (f : ∀ b, Ω b → ℝ) :
    pmfExpect (productDesign D) (fun ω => ∏ b, f b (ω b))
      = ∏ b, pmfExpect (D b) (f b) := by
  classical
  unfold pmfExpect
  calc ∑ ω : ∀ b, Ω b, (productDesign D ω).toReal * ∏ b, f b (ω b)
      = ∑ ω : ∀ b, Ω b, ∏ b, ((D b (ω b)).toReal * f b (ω b)) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [productDesign_apply, ENNReal.toReal_prod, Finset.prod_mul_distrib]
    _ = ∏ b, ∑ x, (D b x).toReal * f b x :=
        sum_pi_prod fun b x => (D b x).toReal * f b x

/-- Factorization of the joint expectation of two statistics of distinct strata. -/
private lemma pmfExpect_productDesign_mul (D : ∀ b, PMF (Ω b)) {b b' : B}
    (hbb' : b ≠ b') (f : Ω b → ℝ) (g : Ω b' → ℝ) :
    pmfExpect (productDesign D) (fun ω => f (ω b) * g (ω b'))
      = pmfExpect (D b) f * pmfExpect (D b') g := by
  classical
  set F : ∀ c, Ω c → ℝ :=
    Function.update (Function.update (fun c => fun _ : Ω c => (1 : ℝ)) b f) b' g
    with hF
  have hFb : F b = f := by
    rw [hF, Function.update_of_ne hbb', Function.update_self]
  have hFb' : F b' = g := by rw [hF, Function.update_self]
  have hFother : ∀ c, c ≠ b → c ≠ b' → F c = fun _ => (1 : ℝ) := fun c hcb hcb' => by
    rw [hF, Function.update_of_ne hcb', Function.update_of_ne hcb]
  have hb'mem : b' ∈ Finset.univ.erase b :=
    Finset.mem_erase.mpr ⟨Ne.symm hbb', Finset.mem_univ b'⟩
  have hpt : ∀ ω : ∀ c, Ω c, f (ω b) * g (ω b') = ∏ c, F c (ω c) := by
    intro ω
    rw [← Finset.mul_prod_erase Finset.univ (fun c => F c (ω c)) (Finset.mem_univ b),
      ← Finset.mul_prod_erase _ (fun c => F c (ω c)) hb'mem]
    have hrest : ∏ c ∈ (Finset.univ.erase b).erase b', F c (ω c) = 1 := by
      refine Finset.prod_eq_one fun c hc => ?_
      have h1 := Finset.mem_erase.mp hc
      have h2 := Finset.mem_erase.mp h1.2
      rw [hFother c h2.1 h1.1]
    rw [hrest, mul_one, hFb, hFb']
  calc pmfExpect (productDesign D) (fun ω => f (ω b) * g (ω b'))
      = pmfExpect (productDesign D) (fun ω => ∏ c, F c (ω c)) := by
        exact congrArg _ (funext fun ω => hpt ω)
    _ = ∏ c, pmfExpect (D c) (F c) := pmfExpect_productDesign_prod D F
    _ = pmfExpect (D b) f * pmfExpect (D b') g := by
        rw [← Finset.mul_prod_erase Finset.univ (fun c => pmfExpect (D c) (F c))
            (Finset.mem_univ b),
          ← Finset.mul_prod_erase _ (fun c => pmfExpect (D c) (F c)) hb'mem]
        have hrest : ∏ c ∈ (Finset.univ.erase b).erase b', pmfExpect (D c) (F c) = 1 := by
          refine Finset.prod_eq_one fun c hc => ?_
          have h1 := Finset.mem_erase.mp hc
          have h2 := Finset.mem_erase.mp h1.2
          rw [hFother c h2.1 h1.1]
          exact pmfExpect_const (D c) 1
        rw [hrest, mul_one, hFb, hFb']

/-- **Independence across strata**: statistics of distinct strata are
uncorrelated. -/
theorem pmfCov_productDesign_of_ne (D : ∀ b, PMF (Ω b)) {b b' : B}
    -- LEAN-ONLY: distinct strata; within one stratum the covariance is unconstrained
    (hbb' : b ≠ b') (f : Ω b → ℝ) (g : Ω b' → ℝ) :
    pmfCov (productDesign D) (fun ω => f (ω b)) (fun ω => g (ω b')) = 0 := by
  classical
  have h1 : pmfExpect (productDesign D) (fun ω => f (ω b)) = pmfExpect (D b) f :=
    pmfExpect_productDesign_comp D b f
  have h2 : pmfExpect (productDesign D) (fun ω => g (ω b')) = pmfExpect (D b') g :=
    pmfExpect_productDesign_comp D b' g
  have key : pmfCov (productDesign D) (fun ω => f (ω b)) (fun ω => g (ω b'))
      = pmfExpect (productDesign D)
          (fun ω => (f (ω b) - pmfExpect (D b) f) * (g (ω b') - pmfExpect (D b') g)) := by
    unfold pmfCov
    rw [h1, h2]
  rw [key]
  calc pmfExpect (productDesign D)
        (fun ω => (f (ω b) - pmfExpect (D b) f) * (g (ω b') - pmfExpect (D b') g))
      = pmfExpect (D b) (fun x => f x - pmfExpect (D b) f)
          * pmfExpect (D b') (fun x => g x - pmfExpect (D b') g) :=
        pmfExpect_productDesign_mul D hbb' (fun x => f x - pmfExpect (D b) f)
          (fun x => g x - pmfExpect (D b') g)
    _ = 0 := by
        rw [pmfExpect_sub, pmfExpect_const, sub_self, zero_mul]

/-- The variance of a single-stratum statistic under the product design is its
single-stratum variance. -/
theorem pmfVar_productDesign_comp (D : ∀ b, PMF (Ω b)) (b₀ : B)
    (f : Ω b₀ → ℝ) :
    pmfVar (productDesign D) (fun ω => f (ω b₀)) = pmfVar (D b₀) f := by
  classical
  have hm : pmfExpect (productDesign D) (fun ω => f (ω b₀)) = pmfExpect (D b₀) f :=
    pmfExpect_productDesign_comp D b₀ f
  unfold pmfVar
  rw [hm]
  exact pmfExpect_productDesign_comp D b₀ fun x => (f x - pmfExpect (D b₀) f) ^ 2

/-- **Additivity of variance over strata** (`Mead §9.4`, no cross-block terms):
the variance of a sum of per-stratum statistics is the sum of the per-stratum
variances. -/
theorem pmfVar_productDesign_sum (D : ∀ b, PMF (Ω b)) (f : ∀ b, Ω b → ℝ) :
    pmfVar (productDesign D) (fun ω => ∑ b, f b (ω b))
      = ∑ b, pmfVar (D b) (f b) := by
  classical
  rw [pmfVar_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single b]
  · rw [pmfCov_self]
    exact pmfVar_productDesign_comp D b (f b)
  · intro b' _ hb'
    exact pmfCov_productDesign_of_ne D (Ne.symm hb') (f b) (f b')
  · intro h
    exact absurd (Finset.mem_univ b) h

end StatLean.ExperimentalDesign
