module
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Beta

@[expose] public section

/-!
# The Dirichlet distribution (corner parametrization)

The **Dirichlet distribution** `𝒟_{k+1}(α₀, …, α_k)` on the probability simplex over `k + 1`
categories, in the *corner parametrization*: the first `k` probabilities `θ : Fin k → ℝ` are free
coordinates on
$$\mathrm{simplexCorner}\ k = \{\theta \mid \forall i,\ 0 < \theta_i \ \wedge\ \textstyle\sum_i
\theta_i < 1\},$$
and the last probability is `1 − ∑ θᵢ` (`simplexExtend`). The density against Lebesgue measure on
`Fin k → ℝ` is
$$w_\alpha(\theta) = \mathbf{1}_{\mathrm{corner}}(\theta)\,
  \prod_{i=0}^{k} (\mathrm{simplexExtend}\,\theta)_i^{\alpha_i - 1},$$
and `dirichletMeasure α = Z(α)⁻¹ • volume.withDensity w_α` with the **abstract normalization**
`Z(α) = ∫⁻ w_α`. Conjugacy (`StatLean.Bayesian.Conjugacy.DirichletMultinomial`) needs only
`0 < Z(α) < ∞`, never the closed form `Z(α) = ∏Γ(αᵢ)/Γ(∑αᵢ)` (a stretch goal).

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §3.4
(multinomial/Dirichlet) and Appendix A (standard distributions), p. 69.

**Proof formalization notes.** Gelman's §3.4 writes the density in `k + 1` symmetric coordinates on
the null set `{∑ xᵢ = 1}`; the corner parametrization used here is the standard
Lebesgue-absolutely-continuous realization (drop the last coordinate), which keeps all measure
theory on `Fin k → ℝ` where `volume` is the pi measure and `StandardBorelSpace` is automatic.
Positivity of `Z` is a sub-box lower bound. Finiteness is the batch's hardest analysis: peel one
coordinate with `MeasureTheory.measurePreserving_piFinSuccAbove`, rescale the remaining corner by
`(1 − t)`, and reduce to the one-dimensional Beta integral `lintegral_Ioo_rpow_mul_rpow`, itself
derived from the pinned `lintegral_betaPDF_eq_one`. Exponents use `Real.rpow`; mind
`Real.rpow_add` needing a positive base (true on the open corner).

**Bibliographic comments.** The distribution is named for P. G. L. Dirichlet, whose evaluation of
the multivariate integral `∫ ∏ xᵢ^{αᵢ−1}` over the simplex ("Sur une nouvelle méthode pour la
détermination des intégrales multiples," *J. Math. Pures Appl.* 4 (1839), 164–168) gives the
normalizing constant. As the conjugate prior of the multinomial it enters Bayesian statistics with
the conjugate-family program of H. Raiffa and R. Schlaifer (*Applied Statistical Decision Theory*,
Harvard, 1961), and it underlies the Dirichlet-process prior of T. S. Ferguson ("A Bayesian
analysis of some nonparametric problems," *Ann. Statist.* 1 (1973), 209–230) at the heart of
Bayesian nonparametrics.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- The open **corner simplex**: the first `k` category probabilities, positive with sum `< 1`
(Gelman §3.4, in the corner parametrization). -/
def simplexCorner (k : ℕ) : Set (Fin k → ℝ) :=
  {θ | (∀ i, 0 < θ i) ∧ ∑ i, θ i < 1}

/-- Extend `k` free probabilities to the full vector of `k + 1` category probabilities, the last
being `1 − ∑ θᵢ`. -/
noncomputable def simplexExtend {k : ℕ} (θ : Fin k → ℝ) : Fin (k + 1) → ℝ :=
  Fin.snoc θ (1 - ∑ i, θ i)

theorem measurable_simplexExtend {k : ℕ} : Measurable (simplexExtend (k := k)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simp only [simplexExtend, Fin.snoc_last]
    exact measurable_const.sub (Finset.univ.measurable_sum fun j _ => measurable_pi_apply j)
  · intro j
    simp only [simplexExtend, Fin.snoc_castSucc]
    exact measurable_pi_apply j

theorem measurableSet_simplexCorner (k : ℕ) : MeasurableSet (simplexCorner k) := by
  rw [simplexCorner, Set.setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_const (measurable_pi_apply i)
  · exact measurableSet_lt
      (Finset.univ.measurable_sum fun i _ => measurable_pi_apply i) measurable_const

open Classical in
/-- **Dirichlet weight** (unnormalized density against Lebesgue on the corner):
`𝟙_corner(θ) · ∏ᵢ (simplexExtend θ)ᵢ^(αᵢ − 1)` (Gelman §3.4). -/
noncomputable def dirichletWeight {k : ℕ} (α : Fin (k + 1) → ℝ) : (Fin k → ℝ) → ℝ≥0∞ :=
  fun θ =>
    if θ ∈ simplexCorner k then
      ENNReal.ofReal (∏ i, simplexExtend θ i ^ (α i - 1))
    else 0

theorem measurable_dirichletWeight {k : ℕ} (α : Fin (k + 1) → ℝ) :
    Measurable (dirichletWeight α) := by
  unfold dirichletWeight
  refine Measurable.ite (measurableSet_simplexCorner k) ?_ measurable_const
  refine Measurable.ennreal_ofReal ?_
  refine Finset.univ.measurable_prod fun i _ => ?_
  exact ((measurable_pi_apply i).comp measurable_simplexExtend).pow measurable_const

/-- The **Dirichlet normalization** `Z(α) = ∫⁻ w_α dLeb`. Conjugacy needs only `0 < Z < ∞`;
the closed form `∏Γ(αᵢ)/Γ(∑αᵢ)` is a stretch goal. -/
noncomputable def dirichletZ {k : ℕ} (α : Fin (k + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, dirichletWeight α θ

/-- The **Dirichlet distribution** in the corner parametrization (Gelman §3.4). Junk: the
zero measure when `Z(α) ∈ {0, ∞}` (excluded for `α > 0` by `dirichletZ_pos`/`dirichletZ_lt_top`). -/
noncomputable def dirichletMeasure {k : ℕ} (α : Fin (k + 1) → ℝ) : Measure (Fin k → ℝ) :=
  (dirichletZ α)⁻¹ • (volume : Measure (Fin k → ℝ)).withDensity (dirichletWeight α)

/-- One-dimensional Beta integral in `ℝ≥0∞` form, derived from the pinned Beta-distribution
normalization: `∫⁻ t in Ioo 0 1, ofReal (t^(a−1) (1−t)^(b−1)) = ofReal (B(a, b))`. -/
theorem lintegral_Ioo_rpow_mul_rpow {a b : ℝ}
    -- USER-INPUT: positive shape parameters; Gelman §3.4
    (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1))
      = ENNReal.ofReal (ProbabilityTheory.beta a b) := by
  have hc : 0 < ProbabilityTheory.beta a b := ProbabilityTheory.beta_pos ha hb
  set I := ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (a - 1) * (1 - t) ^ (b - 1)) with hI
  have key : ENNReal.ofReal (1 / ProbabilityTheory.beta a b) * I = 1 := by
    have h1 := ProbabilityTheory.lintegral_betaPDF_eq_one ha hb
    rw [ProbabilityTheory.lintegral_betaPDF] at h1
    rw [hI, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← h1]
    apply lintegral_congr
    intro t
    rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr hc.le)]
    congr 1
    ring
  calc I = ENNReal.ofReal (ProbabilityTheory.beta a b)
            * (ENNReal.ofReal (1 / ProbabilityTheory.beta a b) * I) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, mul_one_div, div_self hc.ne',
            ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (ProbabilityTheory.beta a b) := by rw [key, mul_one]

/-- The Dirichlet normalization is positive for positive parameters (sub-box lower bound). -/
theorem dirichletZ_pos {k : ℕ} {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Gelman §3.4
    (hα : ∀ i, 0 < α i) :
    0 < dirichletZ α := by
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  set lo : ℝ := 1 / (2 * ((k : ℝ) + 1)) with hlo
  set hi : ℝ := 1 / ((k : ℝ) + 1) with hhi
  have hlopos : 0 < lo := by rw [hlo]; positivity
  have hlohi : lo < hi := by
    rw [hlo, hhi]; exact one_div_lt_one_div_of_lt hkpos (by linarith)
  set B : Set (Fin k → ℝ) := Set.univ.pi (fun _ => Set.Ioo lo hi) with hB
  -- On the sub-box `B`, the density is strictly positive: `B ⊆ support wₐ`.
  have hBsub : B ⊆ Function.support (dirichletWeight α) := by
    intro θ hθ
    simp only [hB, Set.mem_univ_pi, Set.mem_Ioo] at hθ
    have hcorner : θ ∈ simplexCorner k := by
      refine ⟨fun i => hlopos.trans (hθ i).1, ?_⟩
      calc ∑ i, θ i ≤ ∑ _i : Fin k, hi := Finset.sum_le_sum fun i _ => (hθ i).2.le
        _ = (k : ℝ) * hi := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < 1 := by rw [hhi, mul_one_div, div_lt_one hkpos]; linarith
    have hpos : ∀ i, 0 < simplexExtend θ i := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · rw [simplexExtend, Fin.snoc_last]; linarith [hcorner.2]
      · intro j; rw [simplexExtend, Fin.snoc_castSucc]; exact hcorner.1 j
    have : dirichletWeight α θ ≠ 0 := by
      rw [dirichletWeight, if_pos hcorner, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos i) _
    exact this
  rw [dirichletZ, lintegral_pos_iff_support (measurable_dirichletWeight α)]
  refine lt_of_lt_of_le ?_ (measure_mono hBsub)
  rw [hB, volume_pi_pi, pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  rw [Real.volume_Ioo, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact sub_pos.mpr hlohi

open Classical in
/-- **Coordinate-peel pointwise identity.** Writing the first free coordinate as `t` and rescaling
the remaining `k` coordinates by `1 − t` (`η ↦ (1 − t) • η`), the Dirichlet weight factors as a
`t`/`(1 − t)`-power times the *tail* Dirichlet weight (parameters `α ∘ succ`). This is the pointwise
core of the recursion `Z(α) = B(α₀, ∑_{i≥1} αᵢ) · Z(tail α)`. -/
private theorem dirichletWeight_cons_smul {k : ℕ} (α : Fin (k + 2) → ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (η : Fin k → ℝ) :
    dirichletWeight α (Fin.cons t ((1 - t) • η))
      = ENNReal.ofReal (t ^ (α 0 - 1) * (1 - t) ^ ((∑ i : Fin (k + 1), α i.succ) - ((k : ℝ) + 1)))
        * dirichletWeight (fun i => α i.succ) η := by
  set τ : Fin (k + 1) → ℝ := fun i => α i.succ with hτ
  set φ : Fin (k + 1) → ℝ := Fin.cons t ((1 - t) • η) with hφ
  have h1t : (0 : ℝ) < 1 - t := by linarith
  -- The sum `∑ φ = t + (1 - t) · ∑ η`.
  have hsumφ : ∑ i, φ i = t + (1 - t) * ∑ i, η i := by
    rw [hφ, Fin.sum_univ_succ, Fin.cons_zero]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
  by_cases hcorner : η ∈ simplexCorner k
  · obtain ⟨hηpos, hηsum⟩ := hcorner
    -- `φ` lands in the bigger corner.
    have hφcorner : φ ∈ simplexCorner (k + 1) := by
      refine ⟨fun i => ?_, ?_⟩
      · refine Fin.cases ?_ ?_ i
        · rw [hφ, Fin.cons_zero]; exact ht0
        · intro j; rw [hφ, Fin.cons_succ, Pi.smul_apply, smul_eq_mul]
          exact mul_pos h1t (hηpos j)
      · rw [hsumφ]; nlinarith [hηsum, h1t]
    rw [dirichletWeight, if_pos hφcorner, dirichletWeight, if_pos ⟨hηpos, hηsum⟩,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    -- Real product identity.
    set S := ∑ i, η i with hS
    have h1S : (0 : ℝ) < 1 - S := by rw [hS]; linarith
    -- Middle product: `∏_{i} simplexExtend φ i.castSucc = t^(α₀-1) · ∏_j ((1-t)ηⱼ)^…`.
    have hmid : (∏ i : Fin (k + 1), simplexExtend φ i.castSucc ^ (α i.castSucc - 1))
        = t ^ (α 0 - 1) * ∏ j : Fin k, ((1 - t) * η j) ^ (α (j.succ).castSucc - 1) := by
      have hsc : ∀ i : Fin (k + 1), simplexExtend φ i.castSucc = φ i :=
        fun i => by rw [simplexExtend, Fin.snoc_castSucc]
      rw [Fin.prod_univ_succ]
      simp only [hsc]
      simp only [hφ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero, Pi.smul_apply, smul_eq_mul]
    -- Expand the `(k+2)`-fold product over `simplexExtend φ`.
    have hLHS : (∏ i, simplexExtend φ i ^ (α i - 1))
        = (t ^ (α 0 - 1) * ∏ j : Fin k, ((1 - t) * η j) ^ (α (j.succ).castSucc - 1))
          * ((1 - t) * (1 - S)) ^ (α (Fin.last (k + 1)) - 1) := by
      rw [Fin.prod_univ_castSucc, hmid, simplexExtend, Fin.snoc_last,
        show (1 - ∑ i, φ i) = (1 - t) * (1 - S) by rw [hsumφ, hS]; ring]
    -- Expand the tail `(k+1)`-fold product over `simplexExtend η`.
    have hRHS : (∏ i, simplexExtend η i ^ (τ i - 1))
        = (∏ j : Fin k, η j ^ (α (j.succ).castSucc - 1))
          * (1 - S) ^ (α (Fin.last (k + 1)) - 1) := by
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun j _ => ?_
        simp only [simplexExtend, Fin.snoc_castSucc, hτ, Fin.succ_castSucc]
      · have hlast : τ (Fin.last k) = α (Fin.last (k + 1)) := by
          simp only [hτ, Fin.succ_last]
        rw [simplexExtend, Fin.snoc_last, ← hS, hlast]
    rw [hLHS, hRHS]
    -- Push out the `(1 - t)` powers.
    have hsumexp : (∑ j : Fin k, (α (j.succ).castSucc - 1)) + (α (Fin.last (k + 1)) - 1)
        = (∑ i, τ i) - ((k : ℝ) + 1) := by
      rw [Fin.sum_univ_castSucc (f := τ)]
      simp only [hτ, Fin.succ_castSucc, Fin.succ_last]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      ring
    have hmulrpow : ∀ j : Fin k, ((1 - t) * η j) ^ (α (j.succ).castSucc - 1)
        = (1 - t) ^ (α (j.succ).castSucc - 1) * η j ^ (α (j.succ).castSucc - 1) :=
      fun j => Real.mul_rpow h1t.le (hηpos j).le
    have hcomb : (1 - t) ^ (∑ j : Fin k, (α (j.succ).castSucc - 1))
          * (1 - t) ^ (α (Fin.last (k + 1)) - 1)
        = (1 - t) ^ ((∑ i, τ i) - ((k : ℝ) + 1)) := by
      rw [← Real.rpow_add h1t, hsumexp]
    simp only [hmulrpow]
    rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos h1t, Real.mul_rpow h1t.le h1S.le, ← hcomb]
    ring
  · -- Off the corner both sides vanish.
    have hφoff : φ ∉ simplexCorner (k + 1) := by
      intro hφmem
      apply hcorner
      obtain ⟨hpos, hsum⟩ := hφmem
      refine ⟨fun j => ?_, ?_⟩
      · have hj := hpos j.succ
        rw [hφ, Fin.cons_succ, Pi.smul_apply, smul_eq_mul] at hj
        have : η j = ((1 - t) * η j) / (1 - t) := by field_simp
        rw [this]; exact div_pos hj h1t
      · rw [hsumφ] at hsum; nlinarith [hsum, h1t]
    rw [dirichletWeight, if_neg hφoff, dirichletWeight, if_neg hcorner, mul_zero]

open Classical in
/-- Off the interval `(0, 1)` the first coordinate forces the point out of the corner, so the
Dirichlet weight vanishes. -/
private theorem dirichletWeight_cons_eq_zero {k : ℕ} (α : Fin (k + 2) → ℝ)
    {t : ℝ} (ht : t ≤ 0 ∨ 1 ≤ t) (ζ : Fin k → ℝ) :
    dirichletWeight α (Fin.cons t ζ) = 0 := by
  rw [dirichletWeight, if_neg]
  rintro ⟨hpos, hsum⟩
  rcases ht with h | h
  · have h0 := hpos 0; rw [Fin.cons_zero] at h0; linarith
  · rw [Fin.sum_univ_succ] at hsum
    simp only [Fin.cons_zero, Fin.cons_succ] at hsum
    have hζ : (0 : ℝ) ≤ ∑ j, ζ j :=
      Finset.sum_nonneg fun j _ => by have := hpos j.succ; rw [Fin.cons_succ] at this; linarith
    linarith

/-- Consing a fixed first coordinate is measurable. -/
private theorem measurable_cons_right {k : ℕ} (t : ℝ) :
    Measurable (fun ζ : Fin k → ℝ => (Fin.cons t ζ : Fin (k + 1) → ℝ)) := by
  rw [measurable_pi_iff]; intro i
  refine Fin.cases ?_ ?_ i
  · simp only [Fin.cons_zero]; exact measurable_const
  · intro j; simp only [Fin.cons_succ]; exact measurable_pi_apply j

/-- **Inner marginal.** For `t ∈ (0, 1)`, integrating out the remaining `k` coordinates (rescaled by
`1 − t`) gives the one-dimensional `t`-density times the tail normalization. -/
private theorem dirichletZ_inner {k : ℕ} (α : Fin (k + 2) → ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ ζ : Fin k → ℝ, dirichletWeight α (Fin.cons t ζ)
      = ENNReal.ofReal (t ^ (α 0 - 1) * (1 - t) ^ ((∑ i : Fin (k + 1), α i.succ) - 1))
        * dirichletZ (fun i => α i.succ) := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  set F : (Fin k → ℝ) → ℝ≥0∞ := fun ζ => dirichletWeight α (Fin.cons t ζ) with hF
  have hFmeas : Measurable F := (measurable_dirichletWeight α).comp (measurable_cons_right t)
  -- Change of variables `ζ = (1 − t) • η`, Jacobian `(1 − t)^k`.
  have hmap : Measure.map (fun η : Fin k → ℝ => (1 - t) • η) volume
      = ENNReal.ofReal (((1 - t) ^ k)⁻¹) • (volume : Measure (Fin k → ℝ)) := by
    rw [Measure.map_addHaar_smul volume (by positivity : (1 - t) ≠ 0)]
    congr 2
    rw [Module.finrank_fin_fun, abs_of_pos (by positivity)]
  have hcov : ∫⁻ ζ, F ζ = ENNReal.ofReal ((1 - t) ^ k) * ∫⁻ η, F ((1 - t) • η) := by
    have hmapint := lintegral_map (μ := (volume : Measure (Fin k → ℝ))) hFmeas
      (measurable_const_smul (1 - t))
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at hmapint
    have hck : ENNReal.ofReal ((1 - t) ^ k) * ENNReal.ofReal (((1 - t) ^ k)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
        ENNReal.ofReal_one]
    calc ∫⁻ ζ, F ζ
        = 1 * ∫⁻ ζ, F ζ := (one_mul _).symm
      _ = ENNReal.ofReal ((1 - t) ^ k)
            * (ENNReal.ofReal (((1 - t) ^ k)⁻¹) * ∫⁻ ζ, F ζ) := by rw [← hck, mul_assoc]
      _ = ENNReal.ofReal ((1 - t) ^ k) * ∫⁻ η, F ((1 - t) • η) := by rw [hmapint]
  rw [hcov]
  simp only [hF, dirichletWeight_cons_smul α ht0 ht1]
  rw [lintegral_const_mul _ (measurable_dirichletWeight _), ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg h1t.le k)]
  congr 1
  congr 1
  rw [← Real.rpow_natCast (1 - t) k, ← mul_assoc, mul_comm ((1 - t) ^ (k : ℝ)) (t ^ (α 0 - 1)),
    mul_assoc, ← Real.rpow_add h1t,
    show (k : ℝ) + ((∑ i : Fin (k + 1), α i.succ) - ((k : ℝ) + 1))
      = (∑ i : Fin (k + 1), α i.succ) - 1 by ring]

/-- **Exact Dirichlet normalization** `Z(α) = ∏ᵢ Γ(αᵢ) / Γ(∑ᵢ αᵢ)` (Gelman §3.4). Batch-3
target closing the carried debt: the coordinate-peel recursion `Z(α) = B(α₀, ∑_{i≥1} αᵢ)·Z(tail α)`
with the pinned real Beta–Gamma identity `ProbabilityTheory.beta a b = Γ(a)Γ(b)/Γ(a+b)`
(`beta_eq_betaIntegralReal`) telescopes to `∏Γ/Γ(∑)`; `dirichletZ_lt_top` is then an immediate
corollary. -/
theorem dirichletZ_eq_prod_Gamma_div {k : ℕ} {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Gelman §3.4
    (hα : ∀ i, 0 < α i) :
    dirichletZ α = ENNReal.ofReal ((∏ i, Real.Gamma (α i)) / Real.Gamma (∑ i, α i)) := by
  induction k with
  | zero =>
    -- One category: `Z = 1 = Γ(α₀)/Γ(α₀)`.
    have hw : ∀ θ : Fin 0 → ℝ, dirichletWeight α θ = 1 := by
      intro θ
      have hmem : θ ∈ simplexCorner 0 := ⟨fun i => i.elim0, by simp⟩
      have h0 : simplexExtend θ (0 : Fin 1) = 1 := by
        rw [simplexExtend, show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]; simp
      rw [dirichletWeight, if_pos hmem, Fin.prod_univ_one, h0]
      simp
    rw [dirichletZ]
    simp only [hw, lintegral_one, Fin.prod_univ_succ, Fin.sum_univ_succ, Finset.univ_eq_empty,
      Finset.prod_empty, Finset.sum_empty, mul_one, add_zero]
    rw [div_self (Real.Gamma_pos_of_pos (hα 0)).ne', ENNReal.ofReal_one, volume_pi,
      Measure.pi_univ]
    simp
  | succ k ih =>
    -- Peel coordinate `0` and apply Tonelli.
    have h1 : ∀ i : Fin (k + 1), 0 < α i.succ := fun i => hα i.succ
    have hb : 0 < ∑ i : Fin (k + 1), α i.succ :=
      Finset.sum_pos (fun i _ => hα i.succ) ⟨0, Finset.mem_univ 0⟩
    have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm
    have hfae : AEMeasurable (fun z : ℝ × (Fin k → ℝ) => dirichletWeight α
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm z))
        ((volume : Measure ℝ).prod volume) :=
      ((measurable_dirichletWeight α).comp
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm.measurable).aemeasurable
    rw [dirichletZ,
      hmp.lintegral_map_equiv (dirichletWeight α)
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm,
      Measure.volume_eq_prod, lintegral_prod _ hfae]
    have hesymm : ∀ (x : ℝ) (y : Fin k → ℝ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm (x, y)
          = Fin.cons x y := by
      intro x y
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' x y
    simp only [hesymm]
    -- Restrict the outer integral to `(0, 1)`.
    have hzero : ∀ t : ℝ, t ∉ Set.Ioo (0 : ℝ) 1 →
        (∫⁻ ζ, dirichletWeight α (Fin.cons t ζ)) = 0 := by
      intro t ht
      have ht' : t ≤ 0 ∨ 1 ≤ t := by
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at ht; exact ht
      simp only [dirichletWeight_cons_eq_zero α ht', lintegral_zero]
    have hgind : (fun t => ∫⁻ ζ, dirichletWeight α (Fin.cons t ζ))
        = Set.indicator (Set.Ioo 0 1) (fun t => ∫⁻ ζ, dirichletWeight α (Fin.cons t ζ)) := by
      ext t
      by_cases h : t ∈ Set.Ioo (0 : ℝ) 1
      · rw [Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, hzero t h]
    rw [hgind, lintegral_indicator measurableSet_Ioo,
      setLIntegral_congr_fun measurableSet_Ioo (fun t ht => dirichletZ_inner α ht.1 ht.2)]
    have hmeas : Measurable fun t : ℝ =>
        ENNReal.ofReal (t ^ (α 0 - 1) * (1 - t) ^ ((∑ i : Fin (k + 1), α i.succ) - 1)) := by
      fun_prop
    rw [lintegral_mul_const _ hmeas, lintegral_Ioo_rpow_mul_rpow (hα 0) hb,
      ih (α := fun i => α i.succ) h1,
      ← ENNReal.ofReal_mul (ProbabilityTheory.beta_pos (hα 0) hb).le]
    congr 1
    -- Telescope `B(α₀, S₁) · ∏τΓ/Γ(S₁) = ∏Γ/Γ(∑)`.
    rw [ProbabilityTheory.beta]
    simp only [Fin.prod_univ_succ (f := fun i => Real.Gamma (α i)), Fin.sum_univ_succ (f := α)]
    have hΓ1 : Real.Gamma (∑ i : Fin (k + 1), α i.succ) ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
    have hΓ2 : Real.Gamma (α 0 + ∑ i : Fin (k + 1), α i.succ) ≠ 0 :=
      (Real.Gamma_pos_of_pos (add_pos (hα 0) hb)).ne'
    field_simp
    -- `field_simp` clears the (nonzero) `Γ` denominators; the remaining identity is definitional.

/-- The Dirichlet normalization is finite for positive parameters (immediate from the exact form
`dirichletZ_eq_prod_Gamma_div`; `Real.Gamma` is positive, hence finite, for positive arguments). -/
theorem dirichletZ_lt_top {k : ℕ} {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Gelman §3.4
    (hα : ∀ i, 0 < α i) :
    dirichletZ α < ∞ := by
  rw [dirichletZ_eq_prod_Gamma_div hα]; exact ENNReal.ofReal_lt_top

/-- The Dirichlet distribution is a probability measure for positive parameters. -/
theorem isProbabilityMeasure_dirichletMeasure {k : ℕ} {α : Fin (k + 1) → ℝ}
    -- USER-INPUT: positive Dirichlet parameters; Gelman §3.4
    (hα : ∀ i, 0 < α i) :
    IsProbabilityMeasure (dirichletMeasure α) := by
  refine ⟨?_⟩
  rw [dirichletMeasure, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ← dirichletZ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (dirichletZ_pos hα).ne' (dirichletZ_lt_top hα).ne

end StatLean.Bayesian
