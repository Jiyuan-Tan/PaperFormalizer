module
public import StatLean.Bayesian.ForMathlib.DirichletDist
public import StatLean.Bayesian.ForMathlib.MultinomialDist
public import StatLean.Bayesian.Conjugacy.Criterion

@[expose] public section

/-!
# Dirichlet-Multinomial conjugacy

For category probabilities with a Dirichlet prior (corner parametrization, `k + 1` categories)
and one multinomial observation of `n` trials:
$$\theta \sim \mathcal D_{k+1}(\alpha), \quad v \mid \theta \sim \mathcal M_{k+1}(n;
\mathrm{simplexExtend}\ \theta) \ \Longrightarrow\
\theta \mid v \sim \mathcal D_{k+1}(\alpha + v) \qquad \text{predictive-a.e.}$$

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §3.4
(multinomial model for categorical data), p. 69.

**Proof formalization notes.** The conjugacy kernel `dmKernel` is the multinomial kernel pulled
back along `simplexExtend`, so it is dominated by counting measure on the countable data space
`Fin (k+1) → ℕ` — the Batch-1 dominated machinery applies verbatim. Pointwise algebra on the open
corner: `dirichletWeight α θ · q(v | simplexExtend θ) = multinomial coefficient ·
dirichletWeight (α + v) θ` (`Real.rpow_natCast`, `rpow_add` on positive coordinates,
`Fin.snoc_castSucc`/`snoc_last`, `Fin.prod_univ_castSucc`); off the corner both sides vanish. The
recognized constant is `(dirichletZ α)⁻¹ · multinomial · dirichletZ (α + v)`, nondegenerate by
`dirichletZ_pos`/`dirichletZ_lt_top`, and the criterion closes the identification.

**Bibliographic comments.** Dirichlet-multinomial updating — "add the counts to the
concentrations" — is the categorical analogue of Laplace smoothing and the conjugate core of
finite mixture models, latent Dirichlet allocation (D. M. Blei, A. Y. Ng, M. I. Jordan, "Latent
Dirichlet allocation," *J. Mach. Learn. Res.* 3 (2003), 993–1022), and, in the infinite limit, the
Dirichlet-process machinery of Bayesian nonparametrics (T. S. Ferguson, *Ann. Statist.* 1 (1973),
209–230). The pair is one of the natural conjugate families of Raiffa–Schlaifer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {k : ℕ}

/-- The **Dirichlet-Multinomial conjugacy kernel**: the multinomial experiment on the full
probability vector, pulled back to the corner parametrization. -/
@[reducible]
noncomputable def dmKernel (k n : ℕ) : Kernel (Fin k → ℝ) (Fin (k + 1) → ℕ) :=
  (multinomialKernel (k + 1) n).comap simplexExtend measurable_simplexExtend

/-- On the corner, the extended vector `simplexExtend θ` is a genuine probability vector:
all coordinates are strictly positive and they sum to `1`. -/
private theorem simplexExtend_mem_simplex {θ : Fin k → ℝ} (hc : θ ∈ simplexCorner k) :
    (∀ i, 0 < simplexExtend θ i) ∧ ∑ i, simplexExtend θ i = 1 := by
  refine ⟨?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [simplexExtend, Fin.snoc_last]; linarith [hc.2]
    · intro j; rw [simplexExtend, Fin.snoc_castSucc]; exact hc.1 j
  · rw [Fin.sum_univ_castSucc]
    simp only [simplexExtend, Fin.snoc_castSucc, Fin.snoc_last]
    ring

/-- Pointwise weight algebra on the corner: Dirichlet weight times multinomial likelihood is the
multinomial coefficient times the updated Dirichlet weight. Off the corner both sides vanish. -/
theorem dirichletWeight_mul_multinomialWeight {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Gelman §3.4
    (hα : ∀ i, 0 < α i) (n : ℕ) (v : Fin (k + 1) → ℕ)
    -- USER-INPUT: the observed counts total `n` trials; Gelman §3.4
    (hv : ∑ i, v i = n) (θ : Fin k → ℝ) :
    dirichletWeight α θ * multinomialWeight (k + 1) n (simplexExtend θ) v
      = ENNReal.ofReal (Nat.multinomial Finset.univ v : ℝ)
          * dirichletWeight (α + fun i => (v i : ℝ)) θ := by
  by_cases hc : θ ∈ simplexCorner k
  · obtain ⟨hpos, hsum⟩ := simplexExtend_mem_simplex hc
    -- multinomial `if` takes its positive branch
    have hcond : (∀ i, 0 ≤ simplexExtend θ i) ∧ (∑ i, simplexExtend θ i = 1)
        ∧ (∑ i, v i = n) := ⟨fun i => (hpos i).le, hsum, hv⟩
    rw [dirichletWeight, if_pos hc, dirichletWeight, if_pos hc, multinomialWeight, if_pos hcond]
    have hAnn : (0 : ℝ) ≤ ∏ i, simplexExtend θ i ^ (α i - 1) :=
      Finset.prod_nonneg fun i _ => (Real.rpow_pos_of_pos (hpos i) _).le
    have hMnn : (0 : ℝ) ≤ (Nat.multinomial Finset.univ v : ℝ) := Nat.cast_nonneg _
    rw [← ENNReal.ofReal_mul hAnn, ← ENNReal.ofReal_mul hMnn]
    congr 1
    -- factor-wise merge of the two products via `rpow_add`
    have hprod : (∏ i, simplexExtend θ i ^ (α i - 1)) * ∏ i, simplexExtend θ i ^ v i
        = ∏ i, simplexExtend θ i ^ (α i + (v i : ℝ) - 1) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Real.rpow_natCast (simplexExtend θ i) (v i), ← Real.rpow_add (hpos i)]
      congr 1; ring
    simp only [Pi.add_apply]
    rw [show (∏ i, simplexExtend θ i ^ (α i - 1))
          * ((Nat.multinomial Finset.univ v : ℝ) * ∏ i, simplexExtend θ i ^ v i)
          = (Nat.multinomial Finset.univ v : ℝ)
            * ((∏ i, simplexExtend θ i ^ (α i - 1)) * ∏ i, simplexExtend θ i ^ v i) from by ring,
      hprod]
  · have h1 : dirichletWeight α θ = 0 := by rw [dirichletWeight, if_neg hc]
    have h2 : dirichletWeight (α + fun i => (v i : ℝ)) θ = 0 := by rw [dirichletWeight, if_neg hc]
    rw [h1, h2, zero_mul, mul_zero]

/-- **Dirichlet-Multinomial posterior** (Gelman §3.4): observing counts `v` updates
`𝒟(α)` to `𝒟(α + v)`, predictive-a.e. -/
theorem dirichlet_multinomial_posterior_ae {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Gelman §3.4
    (hα : ∀ i, 0 < α i)
    -- LEAN-ONLY: instance plumbing, derivable from hα via `isProbabilityMeasure_dirichletMeasure`
    [IsFiniteMeasure (dirichletMeasure α)] (n : ℕ) :
    ∀ᵐ v ∂(dmKernel k n ∘ₘ dirichletMeasure α),
      ((dmKernel k n)†(dirichletMeasure α)) v
        = dirichletMeasure (α + fun i => (v i : ℝ)) := by
  have hp : Measurable (Function.uncurry
      (fun (θ : Fin k → ℝ) (v : Fin (k + 1) → ℕ) =>
        multinomialWeight (k + 1) n (simplexExtend θ) v)) :=
    (measurable_uncurry_multinomialWeight (k + 1) n).comp
      (measurable_simplexExtend.prodMap measurable_id)
  refine posterior_ae_eq_of_withDensity_eq_smul
    (ν := Measure.count)
    (p := fun θ v => multinomialWeight (k + 1) n (simplexExtend θ) v)
    (ρ := fun v => dirichletMeasure (α + fun i => (v i : ℝ)))
    (c := fun v => if ∑ i, v i = n then
        (dirichletZ α)⁻¹ * ENNReal.ofReal (Nat.multinomial Finset.univ v : ℝ)
          * dirichletZ (α + fun i => (v i : ℝ))
      else 0)
    hp ?_ ?_ ?_
  · -- dominated model: `dmKernel k n θ = count.withDensity (multinomialWeight … (simplexExtend θ))`
    intro θ
    simp only [dmKernel, multinomialKernel]
    rw [Kernel.comap_apply,
      Kernel.withDensity_apply _ (measurable_uncurry_multinomialWeight (k + 1) n),
      Kernel.const_apply]
  · -- candidate posteriors are probability measures (positivity `α i + v i > 0`)
    intro v
    exact isProbabilityMeasure_dirichletMeasure
      (fun i => by simpa using add_pos_of_pos_of_nonneg (hα i) (Nat.cast_nonneg (v i)))
  · -- recognized form at every data point
    intro v
    have hg : Measurable (fun θ => multinomialWeight (k + 1) n (simplexExtend θ) v) :=
      hp.comp (measurable_id.prodMk measurable_const)
    by_cases hv : ∑ i, v i = n
    · have hαv : ∀ i, 0 < (α + fun i => (v i : ℝ)) i :=
        fun i => by simpa using add_pos_of_pos_of_nonneg (hα i) (Nat.cast_nonneg (v i))
      have hZ0 : dirichletZ (α + fun i => (v i : ℝ)) ≠ 0 := (dirichletZ_pos hαv).ne'
      have hZt : dirichletZ (α + fun i => (v i : ℝ)) ≠ ∞ := (dirichletZ_lt_top hαv).ne
      have hfun : dirichletWeight α * (fun θ => multinomialWeight (k + 1) n (simplexExtend θ) v)
          = ENNReal.ofReal (Nat.multinomial Finset.univ v : ℝ)
            • dirichletWeight (α + fun i => (v i : ℝ)) := by
        funext θ
        simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
        exact dirichletWeight_mul_multinomialWeight hα n v hv θ
      rw [if_pos hv]
      simp only [dirichletMeasure]
      rw [withDensity_smul_measure, ← withDensity_mul _ (measurable_dirichletWeight α) hg, hfun,
        withDensity_smul' _ _ ENNReal.ofReal_ne_top, smul_smul, smul_smul,
        mul_assoc _ (dirichletZ (α + fun i => (v i : ℝ))) _,
        ENNReal.mul_inv_cancel hZ0 hZt, mul_one]
    · have hz : (fun θ => multinomialWeight (k + 1) n (simplexExtend θ) v) = 0 := by
        funext θ
        simp only [multinomialWeight, Pi.zero_apply]
        rw [if_neg]
        rintro ⟨-, -, h3⟩; exact hv h3
      rw [hz, withDensity_zero, if_neg hv, zero_smul]

end StatLean.Bayesian
