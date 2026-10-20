module
public import StatLean.ConcentrationInequalities.Symmetrization.GaussianVector
public import StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-!
# Expected maximum of independent standard Gaussians

For $g_1, \dots, g_N$ i.i.d. standard Gaussians ($N \ge 1$),
$$ \mathbb{E}\,\max_{i \le N} |g_i| \;\le\; \sqrt{2 \log (2N)}, $$
equivalently $\mathbb{E}\,\|g\|_\infty \le \sqrt{2\log(2N)}$ for the Pi
sup-norm on $\mathrm{Fin}\,N \to \mathbb{R}$. This is the explicit-constant
replacement for the book's "$\mathbb{E}\|g\|_\infty \le C\sqrt{\log N}$"
(cited from Exercise 2.38(a)) in the lower bound of Lemma 6.6.2.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.6, p. 186 (in the proof of Lemma 6.6.2);
the underlying maximal inequality is §2.5, Exercise 2.38(a).

**Proof formalization notes.** We reuse our
`Maximal/FiniteMaximal.expectation_max_le` **verbatim** on the `2N`-fold
one-sided family `(gᵢ, −gᵢ)` reindexed along `finSumFinEquiv` (each member
centered sub-Gaussian with `σ² = 1` by
`isSubGaussian_eval_gaussVec`/`isSubGaussian_neg_eval_gaussVec`), giving
`√1·√(2 log(2N))`. **Documented deviation:** the `2N` inside the logarithm
(vs. the book's unnamed `C√(log N)`) is the standard union-bound cost of the
two-sided maximum; the `N ≥ 2` corollary consumed by
`gaussian_symmetrization_lower_log` absorbs it via `log(2N) ≤ 2 log N`.
The Pi-norm ↔ `ciSup`-of-abs bridge `pi_norm_eq_ciSup_abs` is `LEAN-ONLY`
glue (`pi_norm_le_iff_of_nonneg` + `norm_le_pi_norm`). Named-sorry fallback
of this work item: `integral_ciSup_abs_gaussVec_le` (the bridge lemma
proven); `expectation_max_le` is reused, never re-derived.

**Bibliographic comments.** The $\sqrt{2\log N}$ growth of Gaussian maxima is
classical extreme-value theory (Cramér, 1946); the sub-Gaussian
maximal-inequality route used here is the standard argument of
Boucheron–Lugosi–Massart, *Concentration Inequalities* (2013), §2.5.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The `Fintype` Pi norm on `ι → ℝ` is the supremum of the coordinate
absolute values. -/
-- LEAN-ONLY: norm/ciSup bridge; via pi_norm_le_iff_of_nonneg + norm_le_pi_norm.
theorem pi_norm_eq_ciSup_abs {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → ℝ) :
    ‖v‖ = ⨆ i, |v i| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (Real.iSup_nonneg (fun i => abs_nonneg _))).mpr (fun i => ?_)
    rw [Real.norm_eq_abs]
    exact le_ciSup (Finite.bddAbove_range fun k => |v k|) i
  · exact ciSup_le (fun i => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i)

/-- The two-sided reindexing equivalence `Fin (2N) ≃ Fin N ⊕ Fin N`. -/
private def twoSidedEquiv (N : ℕ) : Fin (2 * N) ≃ Fin N ⊕ Fin N :=
  (finCongr (two_mul N)).trans finSumFinEquiv.symm

/-- The `2N`-fold one-sided family `(gᵢ, −gᵢ)` on `Fin N → ℝ`. -/
private noncomputable def twoSidedFam (N : ℕ) : Fin (2 * N) → (Fin N → ℝ) → ℝ :=
  fun j g => Sum.elim (fun i => g i) (fun i => -g i) (twoSidedEquiv N j)

private theorem twoSided_center (N : ℕ) (j : Fin (2 * N)) :
    ∫ g, twoSidedFam N j g ∂(gaussVec N) = 0 := by
  unfold twoSidedFam
  rcases h : twoSidedEquiv N j with i | i
  · simp only [Sum.elim_inl]; exact integral_eval_gaussVec N i
  · simp only [Sum.elim_inr]
    rw [integral_neg, integral_eval_gaussVec, neg_zero]

private theorem twoSided_subG (N : ℕ) (j : Fin (2 * N)) :
    IsSubGaussian (twoSidedFam N j) 1 (gaussVec N) := by
  unfold twoSidedFam
  rcases h : twoSidedEquiv N j with i | i
  · simp only [Sum.elim_inl]; exact isSubGaussian_eval_gaussVec N i
  · simp only [Sum.elim_inr]; exact isSubGaussian_neg_eval_gaussVec N i

/-- **Expected two-sided Gaussian maximum** (HDP §6.6, p. 186, explicit
constant): `E max_i |gᵢ| ≤ √(2 log(2N))`. The `2N` is the union-bound cost of
two-sidedness (documented deviation from the book's `C√(log N)`). Named-sorry
debt candidate of this work item; reuses `expectation_max_le` on the
`2N`-family `(gᵢ, −gᵢ)`. -/
theorem integral_ciSup_abs_gaussVec_le (N : ℕ) [NeZero N] :
    ∫ g, ⨆ i, |g i| ∂(gaussVec N) ≤ Real.sqrt (2 * Real.log (2 * N)) := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero N)
  haveI : NeZero (2 * N) := ⟨Nat.mul_ne_zero (by norm_num) (NeZero.ne N)⟩
  -- Pointwise: `⨆ᵢ |gᵢ| = ⨆ⱼ (two-sided family)ⱼ`.
  have hpt : ∀ g : Fin N → ℝ, ⨆ i, |g i| = ⨆ j, twoSidedFam N j g := by
    intro g
    apply le_antisymm
    · refine ciSup_le (fun i => ?_)
      rcases le_total 0 (g i) with hg | hg
      · rw [abs_of_nonneg hg]
        refine le_ciSup_of_le (Finite.bddAbove_range _) ((twoSidedEquiv N).symm (Sum.inl i)) ?_
        simp [twoSidedFam, Equiv.apply_symm_apply]
      · rw [abs_of_nonpos hg]
        refine le_ciSup_of_le (Finite.bddAbove_range _) ((twoSidedEquiv N).symm (Sum.inr i)) ?_
        simp [twoSidedFam, Equiv.apply_symm_apply]
    · refine ciSup_le (fun j => ?_)
      rcases h : twoSidedEquiv N j with i | i
      · have hval : twoSidedFam N j g = g i := by simp [twoSidedFam, h]
        rw [hval]
        exact (le_abs_self _).trans (le_ciSup (Finite.bddAbove_range fun k : Fin N => |g k|) i)
      · have hval : twoSidedFam N j g = -g i := by simp [twoSidedFam, h]
        rw [hval]
        exact (neg_le_abs _).trans (le_ciSup (Finite.bddAbove_range fun k : Fin N => |g k|) i)
  simp_rw [hpt]
  refine (expectation_max_le (twoSided_center N) (twoSided_subG N)).trans_eq ?_
  rw [NNReal.coe_one, Real.sqrt_one, one_mul]
  congr 1
  push_cast
  ring

/-- **Expected sup-norm of the Gaussian vector** (HDP §6.6, p. 186):
`E‖g‖_∞ ≤ √(2 log(2N))`; the Pi-norm phrasing of
`integral_ciSup_abs_gaussVec_le`. -/
theorem integral_pi_norm_gaussVec_le (N : ℕ) [NeZero N] :
    ∫ g, ‖g‖ ∂(gaussVec N) ≤ Real.sqrt (2 * Real.log (2 * N)) := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero N)
  simp_rw [pi_norm_eq_ciSup_abs]
  exact integral_ciSup_abs_gaussVec_le N

end StatLean.ConcentrationInequalities
