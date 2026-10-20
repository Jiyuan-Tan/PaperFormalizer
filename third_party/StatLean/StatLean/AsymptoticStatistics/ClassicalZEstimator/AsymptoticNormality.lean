module
public import StatLean.AsymptoticStatistics.ClassicalZEstimator.TaylorDomination
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterSlutsky

@[expose] public section

/-!
# Classical Z-estimator asymptotic normality (vdV Theorem 5.41, book p.68)

Under the classical conditions of vdV §*5.6,
smoothness conditions (`θ ↦ ψ_θ(x)` twice continuously differentiable with second-order
partials dominated by an integrable `ψ̈`, `Pψ_{θ₀} = 0`, `P‖ψ_{θ₀}‖² < ∞`, and `V = Pψ̇_{θ₀}`
nonsingular), **every** consistent root sequence `θ̂ₙ` of `ℙₙψ_θ = 0` satisfies

    √n(θ̂ₙ − θ₀) = −V⁻¹ 𝔾ₙψ_{θ₀} + o_P(1)   and   √n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ψψᵀ] V⁻ᵀ).

## Proof route (vdV p.68)

Taylor-expand `0 = ℙₙψ_{θ̂ₙ}` around `θ₀`: `ℙₙψ_{θ₀} + (ℙₙψ̇_{θ₀})(θ̂ₙ − θ₀) + R = 0` with
the remainder `R` bounded by `½(ℙₙψ̈)‖θ̂ₙ − θ₀‖²` (`empirical_taylor_random`). The CLT gives
`√n ℙₙψ_{θ₀} ⇝ N(0, Pψψᵀ)`; the WLLN gives `ℙₙψ̇_{θ₀} →ₚ V` (`empiricalPsiDot_tendsto`) and
`ℙₙψ̈ = O_P(1)` (`empiricalPsiDdot_OP`); the remainder is `O_P(1)·o_P(1)² = o_P(1)`
(`tendstoInProbZero_of_isBoundedInProb_mul`). Solving for `√n(θ̂ₙ − θ₀)` and multiplying by
`(V + o_P(1))⁻¹` gives the linear representation (`classical_linear_representation`), and the
CLT, continuous mapping, and Slutsky's theorem give asymptotic normality via
`empiricalProcessVec_weakConverges` and the Gaussian pushforward
`multivariateGaussian_map_toEuclideanCLM`, exactly as in vdV Theorem 5.21.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace Matrix

namespace AsymptoticStatistics.ClassicalZEstimator

open AsymptoticStatistics.EmpiricalProcess

/-! ### WLLN for the empirical Jacobian -/

/-- **`ℙₙψ̇_{θ₀} →ₚ V` entrywise.** For each entry `(j, i)`, the empirical average of the
Jacobian entry converges in `μ`-probability to `Vmat P ψ θ₀ ⱼᵢ = ∫ ψ̇_{θ₀}ⱼᵢ ∂P`. Direct
application of the single-base WLLN `iid_lln_in_prob_seq` to `g := fun x => psiDot ψ θ₀ x j i`
(integrable by `hVint`). This is vdV's "By the law of large numbers it converges in
probability to the matrix `V = Pψ̇_{θ₀}`" (book p.68). -/
theorem empiricalPsiDot_tendsto {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (hVmeas : ∀ j i, Measurable (fun x => psiDot ψ θ₀ x j i))
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∀ j i, TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => empiricalAvg (fun x => psiDot ψ θ₀ x j i) n (fun i : Fin n => X i.val ξ)
        - Vmat P ψ θ₀ j i) := by
  intro j i
  -- `Vmat P ψ θ₀ j i` is by definition `∫ x, psiDot ψ θ₀ x j i ∂P`, so this is the
  -- single-base WLLN at `g := fun x => psiDot ψ θ₀ x j i`.
  simpa only [Vmat, Matrix.of_apply] using
    iid_lln_in_prob_seq P (fun x => psiDot ψ θ₀ x j i) (hVmeas j i) (hVint j i)
      μ X hX_meas hX_indep hX_id hX_law

/-! ### Boundedness in probability of the empirical second-derivative bound -/

/-- **`ℙₙψ̈ = O_P(1)`.** The empirical average of the dominating function `ψ̈` is bounded
in probability. This is vdV's "This is bounded in probability by the law of large numbers"
(book p.68), the boundedness of the second-derivative term controlling the Taylor remainder.

Proof route: a *uniform-in-`n`* Markov bound rather than the WLLN. Each `ψ̈ ∘ Xᵢ` has law `P`
(`hX_id` + `hX_law`), so the triangle inequality gives `E_μ|ℙₙψ̈| ≤ P|ψ̈| =: C` for **every**
`n`, and Markov turns this into `μ{|ℙₙψ̈| > M} ≤ C/M ≤ ε` for `M := C/ε + 1`, simultaneously
for all `n`. The WLLN route (`iid_lln_in_prob_seq`, converge to `Pψ̈` hence `O_P(1)`) would
only control the tail `n ≥ N` and still needs a separate argument for the finitely many small
`n`; the `L¹` bound handles all `n` at once and needs no independence. -/
theorem empiricalPsiDdot_OP {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)) := by
  classical
  -- Every `X i` has law `P`.
  have hlaw : ∀ i : ℕ, μ.map (X i) = P := fun i => by rw [(hX_id i).map_eq]; exact hX_law
  have hasm : ∀ i : ℕ, AEStronglyMeasurable ψddot (μ.map (X i)) := fun i => by
    rw [hlaw i]; exact hψddot_meas.aestronglyMeasurable
  have hint : ∀ i : ℕ, Integrable (fun ξ => ψddot (X i ξ)) μ := by
    intro i
    have h : Integrable ψddot (μ.map (X i)) := by rw [hlaw i]; exact hψddot_int
    exact (integrable_map_measure (hasm i) (hX_meas i).aemeasurable).mp h
  have hC_nonneg : (0 : ℝ) ≤ ∫ x, |ψddot x| ∂P := integral_nonneg fun _ => abs_nonneg _
  -- Each summand has the same `L¹` norm as `ψ̈` under `P`.
  have habs_eq : ∀ i : ℕ, ∫ ξ, |ψddot (X i ξ)| ∂μ = ∫ x, |ψddot x| ∂P := by
    intro i
    rw [← hlaw i, integral_map (hX_meas i).aemeasurable
      (hψddot_meas.abs).aestronglyMeasurable]
  -- `ℙₙψ̈` is `μ`-integrable.
  have hAint : ∀ n : ℕ,
      Integrable (fun ξ => empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)) μ := by
    intro n
    simp only [empiricalAvg]
    exact (integrable_finset_sum _ fun i _ => hint i.val).const_mul _
  -- Uniform `L¹` bound: `E_μ|ℙₙψ̈| ≤ P|ψ̈|` for every `n`.
  have hAbound : ∀ n : ℕ,
      ∫ ξ, |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)| ∂μ ≤ ∫ x, |ψddot x| ∂P := by
    intro n
    have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := by positivity
    have hpt : ∀ ξ, |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)|
        = (n : ℝ)⁻¹ * |∑ i : Fin n, ψddot (X i.val ξ)| := by
      intro ξ
      simp only [empiricalAvg, abs_mul, abs_of_nonneg hinv]
    calc ∫ ξ, |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)| ∂μ
        = (n : ℝ)⁻¹ * ∫ ξ, |∑ i : Fin n, ψddot (X i.val ξ)| ∂μ := by
          rw [← integral_const_mul]
          exact integral_congr_ae (Eventually.of_forall hpt)
      _ ≤ (n : ℝ)⁻¹ * ∫ ξ, ∑ i : Fin n, |ψddot (X i.val ξ)| ∂μ := by
          refine mul_le_mul_of_nonneg_left ?_ hinv
          exact integral_mono ((integrable_finset_sum _ fun i _ => hint i.val).abs)
            (integrable_finset_sum _ fun i _ => (hint i.val).abs)
            (fun ξ => Finset.abs_sum_le_sum_abs _ _)
      _ = (n : ℝ)⁻¹ * ((n : ℝ) * ∫ x, |ψddot x| ∂P) := by
          rw [integral_finset_sum _ fun i _ => (hint i.val).abs]
          simp [habs_eq]
      _ ≤ ∫ x, |ψddot x| ∂P := by
          rcases Nat.eq_zero_or_pos n with hn | hn
          · simp [hn, hC_nonneg]
          · rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul]
  -- Markov, uniformly in `n`.
  intro ε hε
  refine ⟨(∫ x, |ψddot x| ∂P) / ε + 1, fun n => ?_⟩
  set C : ℝ := ∫ x, |ψddot x| ∂P with hC
  set M : ℝ := C / ε + 1 with hM
  have hM_pos : 0 < M := by
    have : 0 ≤ C / ε := div_nonneg hC_nonneg hε.le
    rw [hM]; linarith
  have hmark : M * μ.real {ξ | M ≤ |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)|}
      ≤ ∫ ξ, |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)| ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
      (hAint n).abs M
  have hsub : {ξ | M < ‖empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)‖}
      ⊆ {ξ | M ≤ |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)|} := by
    intro ξ hξ
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hξ ⊢
    exact hξ.le
  have hkey : M * μ.real {ξ | M < ‖empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)‖} ≤ C :=
    calc M * μ.real {ξ | M < ‖empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)‖}
        ≤ M * μ.real {ξ | M ≤ |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)|} :=
          mul_le_mul_of_nonneg_left (measureReal_mono hsub) hM_pos.le
      _ ≤ ∫ ξ, |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)| ∂μ := hmark
      _ ≤ C := hAbound n
  have hMe : M * ε = C + ε := by
    rw [hM]; field_simp
  nlinarith [hkey, hM_pos, hε, hMe]

/-! ### Auxiliary estimates

These estimates give a lower bound for an invertible matrix, two Euclidean
coordinate/norm comparisons, and the deterministic core
of vdV's "solve the Taylor expansion for `√n(θ̂ − θ₀)`" step. -/

/-- **Invertible matrix ⇒ bounded below.** If `V.det` is a unit, then `toEuclideanCLM V`
is bounded below: `‖x‖ = ‖V⁻¹(Vx)‖ ≤ ‖V⁻¹‖‖Vx‖`, so `b := 1/(‖V⁻¹‖ + 1)` works. This is
the quantitative form of vdV's "`V` is nonsingular" used to solve for `√n(θ̂ − θ₀)`. -/
private lemma euclideanCLM_lower_bound {k : ℕ} (V : Matrix (Fin k) (Fin k) ℝ)
    (hV : IsUnit V.det) :
    ∃ b : ℝ, 0 < b ∧ ∀ x : EuclideanSpace ℝ (Fin k),
      b * ‖x‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x‖ := by
  set S := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹ with hS
  set T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V with hT
  have hInv : S * T = 1 := by
    rw [hS, hT, ← map_mul, Matrix.nonsing_inv_mul V hV, map_one]
  have hST : ∀ x : EuclideanSpace ℝ (Fin k), S (T x) = x := by
    intro x
    rw [← ContinuousLinearMap.mul_apply, hInv, ContinuousLinearMap.one_apply]
  refine ⟨1 / (‖S‖ + 1), by positivity, fun x => ?_⟩
  have h1 : ‖x‖ ≤ ‖S‖ * ‖T x‖ := by
    conv_lhs => rw [← hST x]
    exact S.le_opNorm _
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (T x), norm_nonneg S]

/-- **Coordinate bound ⇒ Euclidean norm bound.** `‖y‖ ≤ √k · B` when every coordinate
satisfies `|y j| ≤ B`. -/
private lemma euclidean_norm_le_of_coord {k : ℕ} (y : EuclideanSpace ℝ (Fin k)) {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ j, |y j| ≤ B) : ‖y‖ ≤ Real.sqrt k * B := by
  have hnorm_sq : ‖y‖ ^ 2 = ∑ j, |y j| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.norm_eq_abs]
  have hsum : ∑ j, |y j| ^ 2 ≤ (k : ℝ) * B ^ 2 := by
    calc ∑ j, |y j| ^ 2 ≤ ∑ _j : Fin k, B ^ 2 :=
          Finset.sum_le_sum fun j _ => by nlinarith [h j, abs_nonneg (y j)]
      _ = (k : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hC : (Real.sqrt k * B) ^ 2 = (k : ℝ) * B ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  nlinarith [norm_nonneg y, mul_nonneg (Real.sqrt_nonneg (k : ℝ)) hB, hnorm_sq, hsum, hC]

/-- **A coordinate is dominated by the Euclidean norm.** -/
private lemma euclidean_coord_abs_le {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    |x j| ≤ ‖x‖ := by
  have hnn : (0 : ℝ) ≤ ∑ i, ‖x i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have h1 : |x j| ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 := by
    have : ‖x j‖ ^ 2 ≤ ∑ i, ‖x i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j)
    rwa [Real.norm_eq_abs] at this
  rw [EuclideanSpace.norm_eq]
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∑ i, ‖x i‖ ^ 2), abs_nonneg (x j)]

/-- **Coordinates of `toEuclideanCLM M x`.** -/
private lemma toEuclideanCLM_coord {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) (j : Fin k) :
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M x) j = ∑ i, M j i * x i := rfl

/-- **Deterministic core of vdV's inversion step.** Suppose `V` is bounded below by `b`,
`M` is a `r₂`-perturbation of `V` in the direction `A`, and the Taylor remainder satisfies
`‖MA + G‖ ≤ r₁‖A‖`. If `r₁ + r₂ ≤ b/2` then

* `‖A‖ ≤ 2‖G‖/b` (this is vdV's `√n(θ̂ − θ₀) = O_P(1)`, bootstrapped from the equation
  itself rather than assumed), and
* `‖A + V⁻¹G‖ ≤ 2(r₁ + r₂)‖G‖/b²` (the linear representation, whose right-hand side is
  `o_P(1)` once `r₁, r₂ → 0` and `‖G‖ = O_P(1)`).

Only the second is exported; the first is the intermediate `have`. -/
private lemma classical_repr_deterministic {k : ℕ}
    (V M : Matrix (Fin k) (Fin k) ℝ) (A G : EuclideanSpace ℝ (Fin k))
    {b r₁ r₂ : ℝ} (hb : 0 < b) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂)
    (hVlow : ∀ x : EuclideanSpace ℝ (Fin k),
      b * ‖x‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V x‖)
    (hVinv : ∀ y : EuclideanSpace ℝ (Fin k),
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹ y) = y)
    (hrem : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M A + G‖ ≤ r₁ * ‖A‖)
    (hpert : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M A
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V A‖ ≤ r₂ * ‖A‖)
    (hsmall : r₁ + r₂ ≤ b / 2) :
    ‖A + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹ G‖
      ≤ 2 * (r₁ + r₂) * ‖G‖ / b ^ 2 := by
  set Vc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V with hVc
  set Mc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M with hMc
  set Vic := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V⁻¹ with hVic
  -- `‖VA + G‖ ≤ (r₁ + r₂)‖A‖`: replace `M` by `V` at the cost of the perturbation.
  have hVAG : ‖Vc A + G‖ ≤ (r₁ + r₂) * ‖A‖ := by
    have hrw : Vc A + G = (Mc A + G) - (Mc A - Vc A) := by abel
    rw [hrw]
    calc ‖(Mc A + G) - (Mc A - Vc A)‖ ≤ ‖Mc A + G‖ + ‖Mc A - Vc A‖ := norm_sub_le _ _
      _ ≤ r₁ * ‖A‖ + r₂ * ‖A‖ := add_le_add hrem hpert
      _ = (r₁ + r₂) * ‖A‖ := by ring
  -- `‖A‖ ≤ 2‖G‖/b`: this is the `O_P(1)` bootstrap.
  have hVA : ‖Vc A‖ ≤ ‖Vc A + G‖ + ‖G‖ := by
    calc ‖Vc A‖ = ‖(Vc A + G) - G‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖Vc A + G‖ + ‖G‖ := norm_sub_le _ _
  have hAbound : b * ‖A‖ ≤ 2 * ‖G‖ := by
    have h1 := hVlow A
    nlinarith [norm_nonneg A, norm_nonneg G, hVAG, hVA, hsmall, hr₁, hr₂]
  -- The representation: apply `V` to `A + V⁻¹G` and use the lower bound again.
  have hkey : Vc (A + Vic G) = Vc A + G := by rw [map_add, hVinv]
  have h2 : b * ‖A + Vic G‖ ≤ ‖Vc A + G‖ := by
    have := hVlow (A + Vic G); rwa [hkey] at this
  have hprod : b * (b * ‖A + Vic G‖) ≤ (r₁ + r₂) * (2 * ‖G‖) := by
    calc b * (b * ‖A + Vic G‖) ≤ b * ‖Vc A + G‖ :=
          mul_le_mul_of_nonneg_left h2 hb.le
      _ ≤ b * ((r₁ + r₂) * ‖A‖) := mul_le_mul_of_nonneg_left hVAG hb.le
      _ = (r₁ + r₂) * (b * ‖A‖) := by ring
      _ ≤ (r₁ + r₂) * (2 * ‖G‖) := mul_le_mul_of_nonneg_left hAbound (by linarith)
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < b ^ 2)]
  nlinarith [hprod]

/-- **Entrywise closeness ⇒ operator closeness along a vector.** If every entry of `M − V`
is at most `ζ` in absolute value, then `‖MA − VA‖ ≤ √k·k·ζ·‖A‖`. This turns the
entrywise `ℙₙψ̇_{θ₀} →ₚ V` into the perturbation hypothesis of
`classical_repr_deterministic`. -/
private lemma euclideanCLM_pert_bound {k : ℕ} (M V : Matrix (Fin k) (Fin k) ℝ)
    (A : EuclideanSpace ℝ (Fin k)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (h : ∀ j i, |M j i - V j i| ≤ ζ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M A
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V A‖
      ≤ Real.sqrt k * ((k : ℝ) * ζ) * ‖A‖ := by
  have hcoord : ∀ j, |(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M A
      - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V A) j| ≤ (k : ℝ) * ζ * ‖A‖ := by
    intro j
    have hj : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M A
        - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V A) j
        = ∑ i, (M j i - V j i) * A i := by
      change (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M A) j
        - (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V A) j = _
      rw [toEuclideanCLM_coord, toEuclideanCLM_coord, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hj]
    calc |∑ i, (M j i - V j i) * A i| ≤ ∑ i, |(M j i - V j i) * A i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, ζ * ‖A‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (h j i) (euclidean_coord_abs_le A i) (abs_nonneg _) hζ
      _ = (k : ℝ) * ζ * ‖A‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) M A
        - Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V A‖
      ≤ Real.sqrt k * ((k : ℝ) * ζ * ‖A‖) :=
        euclidean_norm_le_of_coord _ (by positivity) hcoord
    _ = Real.sqrt k * ((k : ℝ) * ζ) * ‖A‖ := by ring

/-- **The `√n`-scaled Taylor expansion at a root** (vdV p.68, "Taylor-expand and multiply
by `√n`"). This is a deterministic consequence of `empirical_taylor_random` together with
`ℙₙψ_{θ̂} = 0` (`hroot`) and `Pψ_{θ₀} = 0` (`hPθ₀_zero`): on the event `θ̂ ∈ closedBall θ₀ ρ`,
the empirical Jacobian applied to `√n(θ̂ − θ₀)` reproduces `−𝔾ₙψ_{θ₀}` up to a remainder
bounded by `√k·½|ℙₙψ̈|·‖θ̂ − θ₀‖ · ‖√n(θ̂ − θ₀)‖`. -/
private lemma classical_scaled_taylor {k : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ψ : EuclideanSpace ℝ (Fin k) → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ψddot : Ω → ℝ) {ρ : ℝ}
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hbound : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      |ψ θ j x - ψ θ₀ j x - ∑ i, psiDot ψ θ₀ x j i * (θ - θ₀) i|
        ≤ (1 / 2) * ψddot x * ‖θ - θ₀‖ ^ 2)
    (n : ℕ) (Xs : Fin n → Ω) (t : EuclideanSpace ℝ (Fin k))
    (ht : t ∈ Metric.closedBall θ₀ ρ)
    (hroot : ∀ j : Fin k, empiricalAvg (ψ t j) n Xs = 0) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
          (Matrix.of fun j i => empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs)
          (Real.sqrt n • (t - θ₀))
        + empiricalProcessVec P ψ θ₀ n Xs‖
      ≤ Real.sqrt k * (1 / 2 * |empiricalAvg ψddot n Xs| * ‖t - θ₀‖)
        * ‖Real.sqrt n • (t - θ₀)‖ := by
  have hAnorm : ‖Real.sqrt n • (t - θ₀)‖ = Real.sqrt n * ‖t - θ₀‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hcoord : ∀ j : Fin k,
      |(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
          (Matrix.of fun j i => empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs)
          (Real.sqrt n • (t - θ₀)) + empiricalProcessVec P ψ θ₀ n Xs) j|
        ≤ 1 / 2 * |empiricalAvg ψddot n Xs| * ‖t - θ₀‖ * (Real.sqrt n * ‖t - θ₀‖) := by
    intro j
    -- Coordinate `j` of the empirical process, using `Pψ_{θ₀} = 0`.
    have hGj : (empiricalProcessVec P ψ θ₀ n Xs) j
        = Real.sqrt n * empiricalAvg (ψ θ₀ j) n Xs := by
      change empiricalProcess P n Xs (ψ θ₀ j) = _
      rw [empiricalProcess, hPθ₀_zero j, sub_zero]
    -- Coordinate `j` of the empirical Jacobian applied to `√n(θ̂ − θ₀)`.
    have hMj : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
          (Matrix.of fun j i => empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs)
          (Real.sqrt n • (t - θ₀))) j
        = Real.sqrt n
          * ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (t - θ₀) i := by
      rw [toEuclideanCLM_coord, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Matrix.of_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hadd : (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
          (Matrix.of fun j i => empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs)
          (Real.sqrt n • (t - θ₀)) + empiricalProcessVec P ψ θ₀ n Xs) j
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
            (Matrix.of fun j i => empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs)
            (Real.sqrt n • (t - θ₀))) j + (empiricalProcessVec P ψ θ₀ n Xs) j := rfl
    -- The empirical Taylor expansion with the root condition substituted.
    have hTb := empirical_taylor_random ψ θ₀ ψddot hbound n Xs t ht j
    rw [hroot j] at hTb
    rw [hadd, hMj, hGj]
    have hAbs : |Real.sqrt n
          * ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (t - θ₀) i
        + Real.sqrt n * empiricalAvg (ψ θ₀ j) n Xs|
        = Real.sqrt n * |0 - empiricalAvg (ψ θ₀ j) n Xs
            - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (t - θ₀) i| := by
      rw [show Real.sqrt n
            * ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (t - θ₀) i
          + Real.sqrt n * empiricalAvg (ψ θ₀ j) n Xs
          = -(Real.sqrt n * (0 - empiricalAvg (ψ θ₀ j) n Xs
              - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (t - θ₀) i)) from by
          ring, abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hAbs]
    have hinner : |0 - empiricalAvg (ψ θ₀ j) n Xs
        - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (t - θ₀) i|
        ≤ 1 / 2 * |empiricalAvg ψddot n Xs| * ‖t - θ₀‖ ^ 2 := by
      refine hTb.trans ?_
      nlinarith [le_abs_self (empiricalAvg ψddot n Xs), sq_nonneg ‖t - θ₀‖]
    calc Real.sqrt n * |0 - empiricalAvg (ψ θ₀ j) n Xs
            - ∑ i, empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs * (t - θ₀) i|
        ≤ Real.sqrt n * (1 / 2 * |empiricalAvg ψddot n Xs| * ‖t - θ₀‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hinner (Real.sqrt_nonneg _)
      _ = 1 / 2 * |empiricalAvg ψddot n Xs| * ‖t - θ₀‖ * (Real.sqrt n * ‖t - θ₀‖) := by ring
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
          (Matrix.of fun j i => empiricalAvg (fun x => psiDot ψ θ₀ x j i) n Xs)
          (Real.sqrt n • (t - θ₀)) + empiricalProcessVec P ψ θ₀ n Xs‖
      ≤ Real.sqrt k * (1 / 2 * |empiricalAvg ψddot n Xs| * ‖t - θ₀‖
          * (Real.sqrt n * ‖t - θ₀‖)) :=
        euclidean_norm_le_of_coord _ (by positivity) hcoord
    _ = Real.sqrt k * (1 / 2 * |empiricalAvg ψddot n Xs| * ‖t - θ₀‖)
          * ‖Real.sqrt n • (t - θ₀)‖ := by rw [hAnorm]; ring

/-! ### Linear representation -/

set_option maxHeartbeats 400000 in
-- The five-event probability assembly exceeds the default elaboration budget.
/-- **Linear representation of the classical Z-estimator.** Under the stated
hypotheses, the estimator admits the `o_P(1)` linear expansion

    `√n(θ̂ₙ − θ₀) = −V⁻¹ 𝔾ₙψ_{θ₀} + o_P(1)`,

stated as `√n(θ̂ₙ − θ₀) + V⁻¹ 𝔾ₙψ_{θ₀} →ₚ 0` (`empiricalProcessVec P ψ θ₀` reduces to
`√n ℙₙψ_{θ₀}` because `Pψ_{θ₀} = 0`). Assembly: Taylor expansion of `0 = ℙₙψ_{θ̂ₙ}` (`G`),
`ℙₙψ̇_{θ₀} →ₚ V` (`D`), `ℙₙψ̈ = O_P(1)` (`E`), `𝔾ₙψ_{θ₀} = O_P(1)` (CLT +
`isBoundedInProb_of_weakConverges`).

The rate `√n(θ̂ₙ − θ₀) = O_P(1)` is **not** assumed: as in vdV it is bootstrapped from the
expansion itself. On the event where `‖θ̂ₙ − θ₀‖ < δ`, `ℙₙψ̇_{θ₀}` is `ζ`-close to `V`
entrywise, and `ℙₙψ̈`, `𝔾ₙψ_{θ₀}` are below their `O_P(1)` thresholds, the expansion reads
`(V + O(ζ + δ))·√n(θ̂ₙ − θ₀) = −𝔾ₙψ_{θ₀}`; since `V` is bounded below by `b > 0`, choosing
`ζ, δ` so that the perturbation is `≤ b/2` gives `‖√n(θ̂ₙ − θ₀)‖ ≤ 2‖𝔾ₙψ_{θ₀}‖/b` and then
`‖√n(θ̂ₙ − θ₀) + V⁻¹𝔾ₙψ_{θ₀}‖ ≤ 2(r₁ + r₂)‖𝔾ₙψ_{θ₀}‖/b²` (`classical_repr_deterministic`).
The four analytic hypotheses and the inner root witness hold off an event of mass `< η`,
which is what `→ₚ 0` requires. -/
theorem classical_linear_representation
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ)
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hV : IsUnit (Vmat P ψ θ₀).det)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hroot : TendstoInnerProbOne μ (fun n => {ξ | ∀ j,
      empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
        (fun i : Fin n => X i.val ξ) = 0}))
    (hcons : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))) := by
  classical
  -- Quantitative nonsingularity of `V` and the right-inverse identity.
  obtain ⟨b, hb_pos, hVlow⟩ := euclideanCLM_lower_bound (Vmat P ψ θ₀) hV
  have hVinv : ∀ y : EuclideanSpace ℝ (Fin k),
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹ y) = y := by
    intro y
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, Matrix.mul_nonsing_inv _ hV, map_one,
      ContinuousLinearMap.one_apply]
  -- Measurability of the Jacobian entries and the pointwise Taylor bound.
  have hVmeas := psiDot_measurable ψ θ₀ Θ hΘ_open hθ₀ hψ_meas hC2
  have hbound := pointwise_taylor_bound ψ θ₀ Θ ψddot hρ hΘ_open hball hC2 hdom
  -- The empirical Jacobian converges entrywise and the derivative envelope is `O_P(1)`.
  have hD := empiricalPsiDot_tendsto P ψ θ₀ hVmeas hVint μ X hX_meas hX_indep hX_id hX_law
  have hE := empiricalPsiDdot_OP P ψddot hψddot_meas hψddot_int μ X hX_meas hX_indep hX_id
    hX_law
  -- CLT ⇒ `𝔾ₙψ_{θ₀} = O_P(1)`.
  have hG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hc : ∀ h : Fin k, Measurable
        (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)) := by
      intro h
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun l _ => (hψ_meas θ₀ h).comp (hX_meas l.val))
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp (measurable_pi_iff.mpr hc)
  have hG_bdd : IsBoundedInProb (fun _ : ℕ => μ) (fun n ξ =>
      empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)) :=
    isBoundedInProb_of_weakConverges hG_meas
      (empiricalProcessVec_weakConverges P ψ θ₀ μ X hX_meas hX_indep hX_id hX_law
        (hψ_meas θ₀) hψ_L2 hPθ₀_zero)
  -- The probabilistic assembly.
  intro ε hε
  refine Metric.tendsto_atTop.mpr fun η hη => ?_
  -- Uniform `O_P(1)` thresholds for `ℙₙψ̈` and `𝔾ₙψ_{θ₀}`.
  obtain ⟨MK₀, hMK₀⟩ := hE (η / 8) (by positivity)
  obtain ⟨MG₀, hMG₀⟩ := hG_bdd (η / 8) (by positivity)
  set MK : ℝ := max MK₀ 1 with hMK_def
  set MG : ℝ := max MG₀ 1 with hMG_def
  have hMK_pos : 0 < MK := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMG_pos : 0 < MG := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  -- Smallness budget: `s` is the total slack allowed in `r₁ + r₂ ≤ b/2`.
  set s : ℝ := min (b / 2) (ε * b ^ 2 / (4 * MG)) with hs_def
  have hs_pos : 0 < s := lt_min (by positivity) (by positivity)
  set δ : ℝ := min ρ (s / (Real.sqrt k * MK + 1)) with hδ_def
  have hδ_pos : 0 < δ := lt_min hρ (by positivity)
  set ζ : ℝ := s / (2 * (Real.sqrt k * k + 1)) with hζ_def
  have hζ_pos : 0 < ζ := by positivity
  -- The two `→ₚ 0` events (consistency; entrywise Jacobian WLLN over the `k²` entries).
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp (hcons δ hδ_pos) (η / 8) (by positivity)
  have hMsum : Tendsto (fun n => ∑ p : Fin k × Fin k, μ.real
      {ξ | ζ ≤ ‖empiricalAvg (fun x => psiDot ψ θ₀ x p.1 p.2) n (fun i : Fin n => X i.val ξ)
        - Vmat P ψ θ₀ p.1 p.2‖}) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin k × Fin k))
      (fun p _ => hD p.1 p.2 ζ hζ_pos)
    simpa using h
  obtain ⟨N₄, hN₄⟩ := Metric.tendsto_atTop.mp hMsum (η / 8) (by positivity)
  -- The measurable inner witness for the root event has a vanishing complement.
  obtain ⟨Eroot, hEroot_meas, hEroot_sub, hEroot_lim⟩ := hroot
  have hEroot_compl : Tendsto (fun n => μ.real (Eroot n)ᶜ) atTop (𝓝 0) := by
    have hcomp : Tendsto (fun n => (1 : ℝ) - μ.real (Eroot n)) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hEroot_lim
      simpa only [sub_self] using h
    convert hcomp using 1
    ext n
    rw [measureReal_compl (hEroot_meas n)]
    simp
  obtain ⟨N₅, hN₅⟩ := Metric.tendsto_atTop.mp hEroot_compl (η / 8) (by positivity)
  refine ⟨max (max N₃ N₄) N₅, fun n hn => ?_⟩
  -- The five bad events, including failure of the measurable inner root witness.
  set S1 : Set Ξ := {ξ | MK < ‖empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)‖} with hS1
  set S2 : Set Ξ :=
    {ξ | MG < ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖} with hS2
  set S3 : Set Ξ := {ξ | δ ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖} with hS3
  set S4 : Set Ξ := ⋃ p : Fin k × Fin k,
    {ξ | ζ ≤ ‖empiricalAvg (fun x => psiDot ψ θ₀ x p.1 p.2) n (fun i : Fin n => X i.val ξ)
      - Vmat P ψ θ₀ p.1 p.2‖} with hS4
  set S5 : Set Ξ := (Eroot n)ᶜ with hS5
  -- Off the bad events the deterministic core gives the representation below `ε`.
  have hkey : ∀ ξ : Ξ, ξ ∉ S1 → ξ ∉ S2 → ξ ∉ S3 → ξ ∉ S4 → ξ ∉ S5 →
      ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖ < ε := by
    intro ξ h1 h2 h3 h4 h5
    rw [hS1] at h1; rw [hS2] at h2; rw [hS3] at h3; rw [hS4] at h4; rw [hS5] at h5
    simp only [Set.mem_setOf_eq, not_lt, Real.norm_eq_abs] at h1
    simp only [Set.mem_setOf_eq, not_lt] at h2
    simp only [Set.mem_setOf_eq, not_le] at h3
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le, Real.norm_eq_abs] at h4
    simp only [Set.mem_compl_iff, not_not] at h5
    -- `θ̂ₙ` lies in the ball where the Taylor bound is valid.
    have hδρ : δ ≤ ρ := min_le_left _ _
    have ht : θ_hat n (fun i : Fin n => X i.val ξ) ∈ Metric.closedBall θ₀ ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_lt (lt_of_lt_of_le h3 hδρ)
    -- The remainder coefficient `r₁` and the perturbation coefficient `r₂`.
    set r₁ : ℝ := Real.sqrt k * (1 / 2 * |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)|
      * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) with hr₁_def
    set r₂ : ℝ := Real.sqrt k * ((k : ℝ) * ζ) with hr₂_def
    have hr₁_nonneg : 0 ≤ r₁ := by rw [hr₁_def]; positivity
    have hr₂_nonneg : 0 ≤ r₂ := by rw [hr₂_def]; positivity
    -- `r₁ ≤ s/2` : `|ℙₙψ̈| ≤ MK` and `‖θ̂ₙ − θ₀‖ < δ ≤ s/(√k·MK + 1)`.
    have hr₁_small : r₁ ≤ s / 2 := by
      have hδs : δ ≤ s / (Real.sqrt k * MK + 1) := min_le_right _ _
      have hden : (0 : ℝ) < Real.sqrt k * MK + 1 := by positivity
      have hδs' : δ * (Real.sqrt k * MK + 1) ≤ s := (le_div_iff₀ hden).mp hδs
      have hsk : (0 : ℝ) ≤ Real.sqrt k := Real.sqrt_nonneg _
      have hDlt : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ ≤ δ := h3.le
      have hDnn : (0 : ℝ) ≤ ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ := norm_nonneg _
      have habs : (0 : ℝ) ≤ |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)| :=
        abs_nonneg _
      rw [hr₁_def]
      calc Real.sqrt k * (1 / 2 * |empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)|
              * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖)
          ≤ Real.sqrt k * (1 / 2 * MK * δ) := by
            refine mul_le_mul_of_nonneg_left ?_ hsk
            nlinarith [mul_le_mul h1 hDlt hDnn hMK_pos.le]
        _ = Real.sqrt k * MK * δ / 2 := by ring
        _ ≤ (Real.sqrt k * MK + 1) * δ / 2 := by nlinarith [hδ_pos]
        _ = δ * (Real.sqrt k * MK + 1) / 2 := by ring
        _ ≤ s / 2 := by linarith [hδs']
    -- `r₂ ≤ s/2` by the choice of `ζ`.
    have hr₂_small : r₂ ≤ s / 2 := by
      have hζ' : ζ * (2 * (Real.sqrt k * k + 1)) = s := by
        rw [hζ_def]; field_simp
      have hsk : (0 : ℝ) ≤ Real.sqrt k := Real.sqrt_nonneg _
      have hkk : (0 : ℝ) ≤ Real.sqrt k * k := by positivity
      rw [hr₂_def]
      calc Real.sqrt k * ((k : ℝ) * ζ) = Real.sqrt k * k * ζ := by ring
        _ ≤ (Real.sqrt k * k + 1) * ζ :=
            mul_le_mul_of_nonneg_right (by linarith) hζ_pos.le
        _ = s / 2 := by rw [← hζ']; ring
    have hsb : s ≤ b / 2 := min_le_left _ _
    -- The scaled Taylor expansion at the root, and the entrywise perturbation bound.
    have hrem := classical_scaled_taylor P ψ θ₀ ψddot hPθ₀_zero hbound n
      (fun i : Fin n => X i.val ξ) (θ_hat n (fun i : Fin n => X i.val ξ)) ht
      (fun j => hEroot_sub n h5 j)
    have hpert := euclideanCLM_pert_bound
      (Matrix.of fun j i =>
        empiricalAvg (fun x => psiDot ψ θ₀ x j i) n (fun i : Fin n => X i.val ξ))
      (Vmat P ψ θ₀) (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
      hζ_pos.le (fun j i => by
        simpa only [Matrix.of_apply] using (h4 (j, i)).le)
    -- The deterministic inversion.
    have hfin := classical_repr_deterministic (Vmat P ψ θ₀)
      (Matrix.of fun j i =>
        empiricalAvg (fun x => psiDot ψ θ₀ x j i) n (fun i : Fin n => X i.val ξ))
      (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
      (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))
      hb_pos hr₁_nonneg hr₂_nonneg hVlow hVinv hrem hpert (by linarith)
    -- Numerics: `2(r₁ + r₂)‖𝔾ₙ‖/b² ≤ 2·s·MG/b² ≤ ε/2 < ε`.
    have hGle : ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖ ≤ MG := h2
    have hGnn : (0 : ℝ) ≤ ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖ :=
      norm_nonneg _
    have hsMG : s * (4 * MG) ≤ ε * b ^ 2 :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    have hmul : ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖ * b ^ 2
        ≤ 2 * (r₁ + r₂) * ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖ :=
      (le_div_iff₀ (by positivity)).mp hfin
    have hstep1 : 2 * (r₁ + r₂)
        * ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖ ≤ 2 * s * MG := by
      have h1 : r₁ + r₂ ≤ s := by linarith
      have h2 : (r₁ + r₂)
          * ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖ ≤ s * MG :=
        mul_le_mul h1 hGle hGnn hs_pos.le
      linarith
    have hbsq : (0 : ℝ) < b ^ 2 := by positivity
    have hstep3 : ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖ * b ^ 2
        ≤ ε * b ^ 2 / 2 := by linarith
    nlinarith [hstep3, hbsq, mul_pos hε hbsq]
  -- Hence the `ε`-exceedance set is contained in the union of the five bad events.
  have hsub : {ξ : Ξ | ε ≤ ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
            (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖}
      ⊆ S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 := by
    intro ξ hξ
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩ := hcon
    exact absurd (hkey ξ q1 q2 q3 q4 q5) (not_lt.mpr hξ)
  -- Mass of each bad event.
  have hb1 : μ.real S1 ≤ η / 8 := by
    have hsub1 : S1 ⊆ {ξ | MK₀ < ‖empiricalAvg ψddot n (fun i : Fin n => X i.val ξ)‖} := by
      rw [hS1]; exact fun ξ hξ => lt_of_le_of_lt (le_max_left MK₀ 1) hξ
    exact le_trans (measureReal_mono hsub1) (hMK₀ n)
  have hb2 : μ.real S2 ≤ η / 8 := by
    have hsub2 : S2 ⊆
        {ξ | MG₀ < ‖empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)‖} := by
      rw [hS2]; exact fun ξ hξ => lt_of_le_of_lt (le_max_left MG₀ 1) hξ
    exact le_trans (measureReal_mono hsub2) (hMG₀ n)
  have hn34 : max N₃ N₄ ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : N₃ ≤ n := le_trans (le_max_left _ _) hn34
  have hn4 : N₄ ≤ n := le_trans (le_max_right _ _) hn34
  have hn5 : N₅ ≤ n := le_trans (le_max_right _ _) hn
  have hb3 : μ.real S3 < η / 8 := by
    have h := hN₃ n hn3
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    exact h
  have hb4 : μ.real S4 < η / 8 := by
    have h := hN₄ n hn4
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg
      fun _ _ => measureReal_nonneg)] at h
    refine lt_of_le_of_lt ?_ h
    rw [hS4]
    exact measureReal_iUnion_fintype_le _
  have hb5 : μ.real S5 < η / 8 := by
    have h := hN₅ n hn5
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at h
    rw [hS5]
    exact h
  -- Sum up.
  have a1 := measureReal_union_le (μ := μ) (((S1 ∪ S2) ∪ S3) ∪ S4) S5
  have a2 := measureReal_union_le (μ := μ) ((S1 ∪ S2) ∪ S3) S4
  have a3 := measureReal_union_le (μ := μ) (S1 ∪ S2) S3
  have a4 := measureReal_union_le (μ := μ) S1 S2
  have hle := measureReal_mono (μ := μ) hsub
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  linarith

/-- The measurable leading term `-V⁻¹ 𝔾ₙψ_{θ₀}` and its Gaussian weak limit. -/
private theorem classical_leading_term_limit
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    (∀ n, Measurable (fun ξ : Ξ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
        (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))) ∧
      WeakConverges (fun n => μ.map (fun ξ : Ξ =>
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
          (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))))
        (multivariateGaussian 0
          ((Vmat P ψ θ₀)⁻¹ * psiCov P ψ θ₀ * ((Vmat P ψ θ₀)⁻¹)ᵀ)) := by
  have hCLT := empiricalProcessVec_weakConverges P ψ θ₀ μ X hX_meas hX_indep hX_id hX_law
    (hψ_meas θ₀) hψ_L2 hPθ₀_zero
  have hPSD := psiCov_posSemidef P ψ θ₀ hψ_L2
  have hG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hc : ∀ h : Fin k, Measurable
        (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ h)) := by
      intro h
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun l _ => (hψ_meas θ₀ h).comp (hX_meas l.val))
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp (measurable_pi_iff.mpr hc)
  have hmap := WeakConverges.map hCLT
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)).continuous
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)).continuous.measurable
  rw [multivariateGaussian_map_toEuclideanCLM (-(Vmat P ψ θ₀)⁻¹) 0 hPSD] at hmap
  have hcov : (-(Vmat P ψ θ₀)⁻¹) * psiCov P ψ θ₀ * (-(Vmat P ψ θ₀)⁻¹)ᴴ
      = (Vmat P ψ θ₀)⁻¹ * psiCov P ψ θ₀ * ((Vmat P ψ θ₀)⁻¹)ᵀ := by
    have hHT : ((Vmat P ψ θ₀)⁻¹)ᴴ = ((Vmat P ψ θ₀)⁻¹)ᵀ := by
      ext i j
      rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
    rw [Matrix.conjTranspose_neg, hHT]
    simp only [neg_mul, mul_neg]
    exact neg_neg _
  rw [hcov, map_zero] at hmap
  refine ⟨fun n => (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k)
    (-(Vmat P ψ θ₀)⁻¹)).continuous.measurable.comp (hG_meas n), ?_⟩
  have hfun : (fun n => μ.map (fun ξ : Ξ =>
        Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
          (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))))
      = (fun n => (μ.map (fun ξ : Ξ =>
          empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))).map
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹))) := by
    funext n
    exact (Measure.map_map
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)).continuous.measurable
      (hG_meas n)).symm
  rw [hfun]
  exact hmap

/-! ### Asymptotic normality (vdV Theorem 5.41) -/

/-- **Classical Z-estimator asymptotic normality — vdV Theorem 5.41** (§*5.6, book p.68).

For each `θ` in an open subset `Θ` of Euclidean space let `θ ↦ ψ_θ(x)` be twice
continuously differentiable for every `x` (`hC2`). Suppose `Pψ_{θ₀} = 0` (`hPθ₀_zero`),
`P‖ψ_{θ₀}‖² < ∞` (`hψ_L2`), and the matrix `V = Pψ̇_{θ₀}` exists (`hVint`) and is
nonsingular (`hV`). Assume the second-order partial derivatives are dominated by a fixed
integrable function `ψ̈(x)` for every `θ` in a neighborhood of `θ₀` (`hdom`, `hψddot_int`).
Then every consistent estimator sequence `θ̂ₙ` whose exact-root event has inner probability tending
to one (`hroot`, `hcons`) satisfies vdV's displayed representation and its "in particular"
asymptotic normality. The literal exact-for-all-samples premise is recovered by
`classical_zEstimator_normality_of_exact_root` below.

    √n(θ̂ₙ − θ₀) = −V⁻¹ 𝔾ₙψ_{θ₀} + o_P(1)   and   √n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ψψᵀ] V⁻ᵀ).

The theorem `classical_linear_representation` gives the representation;
`empiricalProcessVec_weakConverges` (CLT) + `multivariateGaussian_map_toEuclideanCLM` (CMT
by `−V⁻¹`) + `WeakConverges.slutsky_of_tendstoInMeasure_dist` transport it to the Gaussian
limit, exactly as in vdV Theorem 5.21. -/
theorem classical_zEstimator_normality
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ)
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hV : IsUnit (Vmat P ψ θ₀).det)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hθhat_meas : ∀ n, Measurable (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    (hroot : TendstoInnerProbOne μ (fun n => {ξ | ∀ j,
      empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
        (fun i : Fin n => X i.val ξ) = 0}))
    (hcons : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
    ∧ WeakConverges
        (fun n => μ.map (fun ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0 ((Vmat P ψ θ₀)⁻¹ * psiCov P ψ θ₀ * ((Vmat P ψ θ₀)⁻¹)ᵀ)) := by
  classical
  -- vdV's displayed linear representation.
  have hlin := classical_linear_representation P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero
    hψ_L2 hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom θ_hat μ X hX_meas hX_indep
    hX_id hX_law hroot hcons
  refine ⟨hlin, ?_⟩
  -- The "in particular": CLT + continuous mapping by `−V⁻¹` + Slutsky.
  obtain ⟨hlead_meas, hmap'⟩ := classical_leading_term_limit P ψ θ₀ hψ_meas hPθ₀_zero
    hψ_L2 μ X hX_meas hX_indep hX_id hX_law
  -- Slutsky: transport the Gaussian limit along the `o_P(1)` difference.
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ξ => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
      (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
    (Y := fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    (fun n => (hlead_meas n).aemeasurable)
    (fun n => (((hθhat_meas n).sub measurable_const).const_smul (Real.sqrt n)).aemeasurable)
    hmap' ?_
  intro ε hε
  have hset : ∀ n, {ξ : Ξ | ε ≤ dist
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
          (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
        (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))}
      = {ξ : Ξ | ε ≤ ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖} := by
    intro n
    ext ξ
    simp only [Set.mem_setOf_eq, dist_eq_norm, map_neg, ContinuousLinearMap.neg_apply]
    rw [show -Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
          (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))
        - Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
      = -(Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
        from by abel, norm_neg]
  simp only [hset]
  exact hlin ε hε

/-- **Classical Z-estimator outer asymptotic normality — vdV Theorem 5.41.**
This form does not require measurability of the selected approximate root. -/
theorem classical_zEstimator_normality_outer
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ)
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hV : IsUnit (Vmat P ψ θ₀).det)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hroot : TendstoInnerProbOne μ (fun n => {ξ | ∀ j,
      empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
        (fun i : Fin n => X i.val ξ) = 0}))
    (hcons : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
    ∧ WeakConvergesOuter (fun _ : ℕ => μ)
        (fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
        (multivariateGaussian 0
          ((Vmat P ψ θ₀)⁻¹ * psiCov P ψ θ₀ * ((Vmat P ψ θ₀)⁻¹)ᵀ)) := by
  classical
  have hlin := classical_linear_representation P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero
    hψ_L2 hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom θ_hat μ X hX_meas hX_indep
    hX_id hX_law hroot hcons
  refine ⟨hlin, ?_⟩
  obtain ⟨hlead_meas, hlead⟩ := classical_leading_term_limit P ψ θ₀ hψ_meas hPθ₀_zero
    hψ_L2 μ X hX_meas hX_indep hX_id hX_law
  have hlead_outer : WeakConvergesOuter (fun _ : ℕ => μ)
      (fun n ξ => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
        (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
      (multivariateGaussian 0
        ((Vmat P ψ θ₀)⁻¹ * psiCov P ψ θ₀ * ((Vmat P ψ θ₀)⁻¹)ᵀ)) :=
    (weakConvergesOuter_of_measurable hlead_meas).2 hlead
  refine WeakConvergesOuter.slutsky_of_tendstoInOuterProbability_dist
    (X := fun n ξ => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
      (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
    (Y := fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    hlead_outer ?_
  intro ε hε
  have hset : ∀ n, {ξ : Ξ | ε ≤ dist
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (-(Vmat P ψ θ₀)⁻¹)
          (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
        (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))}
      = {ξ : Ξ | ε ≤ ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))‖} := by
    intro n
    ext ξ
    simp only [Set.mem_setOf_eq, dist_eq_norm, map_neg, ContinuousLinearMap.neg_apply]
    rw [show -Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
          (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ))
        - Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
      = -(Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
        from by abel, norm_neg]
  simp only [hset]
  exact hlin ε hε

/-- **Exact-root form of vdV Theorem 5.41.** Its premise supplies `univ` as a
measurable inner witness, so the inner-probability theorem applies without an
additional assumption. -/
theorem classical_zEstimator_normality_of_exact_root
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Set (EuclideanSpace ℝ (Fin k))) (hΘ_open : IsOpen Θ)
    (ψ : EuclideanSpace ℝ (Fin k) → Fin k → Ω → ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ ∈ Θ)
    (hψ_meas : ∀ θ j, Measurable (ψ θ j))
    (hC2 : ∀ (j : Fin k) (x : Ω), ContDiffOn ℝ 2 (fun θ => ψ θ j x) Θ)
    (hPθ₀_zero : ∀ j, ∫ x, ψ θ₀ j x ∂P = 0)
    (hψ_L2 : MemLp (psiVec ψ θ₀) 2 P)
    (hVint : ∀ j i, Integrable (fun x => psiDot ψ θ₀ x j i) P)
    (hV : IsUnit (Vmat P ψ θ₀).det)
    (ψddot : Ω → ℝ) (hψddot_meas : Measurable ψddot) (hψddot_int : Integrable ψddot P)
    {ρ : ℝ} (hρ : 0 < ρ) (hball : Metric.closedBall θ₀ ρ ⊆ Θ)
    (hdom : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ (j : Fin k) (x : Ω),
      ‖iteratedFDeriv ℝ 2 (fun θ' => ψ θ' j x) θ‖ ≤ ψddot x)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hθhat_meas : ∀ n, Measurable (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ)))
    (hroot : ∀ (n : ℕ) (xs : Fin n → Ω) (j : Fin k),
      empiricalAvg (ψ (θ_hat n xs) j) n xs = 0)
    (hcons : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (Vmat P ψ θ₀)⁻¹
              (empiricalProcessVec P ψ θ₀ n (fun i : Fin n => X i.val ξ)))
    ∧ WeakConverges
        (fun n => μ.map (fun ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
        (multivariateGaussian 0 ((Vmat P ψ θ₀)⁻¹ * psiCov P ψ θ₀ * ((Vmat P ψ θ₀)⁻¹)ᵀ)) := by
  have hroot_inner : TendstoInnerProbOne μ (fun n => {ξ | ∀ j,
      empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ)) j) n
        (fun i : Fin n => X i.val ξ) = 0}) := by
    refine ⟨fun _ => Set.univ, fun _ => MeasurableSet.univ, ?_, ?_⟩
    · intro n ξ _ j
      exact hroot n (fun i : Fin n => X i.val ξ) j
    · simp
  exact classical_zEstimator_normality P Θ hΘ_open ψ θ₀ hθ₀ hψ_meas hC2 hPθ₀_zero hψ_L2
    hVint hV ψddot hψddot_meas hψddot_int hρ hball hdom θ_hat μ X hX_meas hX_indep hX_id
    hX_law hθhat_meas hroot_inner hcons

end AsymptoticStatistics.ClassicalZEstimator
