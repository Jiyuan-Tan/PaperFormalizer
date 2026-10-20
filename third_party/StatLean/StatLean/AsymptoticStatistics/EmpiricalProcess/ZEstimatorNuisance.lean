module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
public import StatLean.AsymptoticStatistics.EmpiricalProcess.Donsker
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformRandomFunctions
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterProbAsymptotics
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability

@[expose] public section

/-!
# Z-estimator with an estimated nuisance parameter (vdV Theorem 5.31)

This file generalizes the finite-dimensional Z-estimator
asymptotic linear representation of vdV §5.3 (`zEstimator_asymptotic_normality`,
Theorem 5.21) to the case where an **estimated nuisance** `η̂ₙ` rides along
(vdV §*5.4 "Estimated Parameters", book p.60). For `θ ∈` an open subset of `ℝᵏ`,
`η` in a metric space, and estimating functions `x ↦ ψ_{θ,η}(x)` whose pair class
`{ψ_{θ,η} : ‖θ − θ₀‖ < δ, d(η,η₀) < δ}` is Donsker, with `Pψ_{θ₀,η₀} = 0` and
`θ ↦ Pψ_{θ,η}` Fréchet-differentiable at `θ₀` uniformly in `η` (nonsingular
derivative `V_{θ₀,η} → V_{θ₀,η₀}`): if `√n ℙₙψ_{θ̂ₙ,η̂ₙ} = o_P(1)` and
`(θ̂ₙ, η̂ₙ) →ᴾ (θ₀, η₀)`, then the **linear representation with drift**

    √n(θ̂ₙ − θ₀) = −V⁻¹_{η₀} √n P ψ_{θ₀,η̂ₙ} − V⁻¹_{η₀} 𝔾ₙ ψ_{θ₀,η₀}
                    + o_P(1 + √n‖P ψ_{θ₀,η̂ₙ}‖).

The conclusion is encoded as a scaled `TendstoInProbZero` with weight
`wDrift n ξ := 1 + √n‖driftVec P ψ θ₀ η̂ₙ‖`:

    wDrift⁻¹ • ( √n•(θ̂ₙ−θ₀) + V⁻¹_{η₀}(√n•driftVec) + V⁻¹_{η₀}(𝔾ₙψ_{θ₀,η₀}) ) →ₚ 0.

vdV gives no separate proof (*"The proof follows the same steps as the proof of
Theorem 5.21."*). The Theorem 19.26 result `infinite_dim_z_estimator` does not
apply directly because it has fixed `V` at
`θ₀`, `Pψ_{θ₀}=0`, drift-free, unweighted bootstrap); only its components are
reused, together with the weighted `o_P`/`O_P` predicates from
`OuterProbAsymptotics` and the guarded metric-space random functions from
`UniformRandomFunctions`.

The Donsker assumption is stated as `IsPDonsker (pairClass ψ (ball ×ˢ ball)) P`.
Neighborhood nonsingularity is derived from `IsUnit (V η₀).det` and
`ContinuousAt V η₀`; the `L²` property is derived from `hDonsker`. The conclusion
is the book's linear representation with drift and makes no normality claim.
The `pairClass` renders the `ℝᵏ`-valued class in van der Vaart, Theorem 5.31,
as the union of its scalar coordinate slices because `IsPDonsker` is a scalar
predicate. For finite `k`, Donsker convergence of this union yields the required
vector convergence; stated as a hypothesis, it is the stronger direction of
this comparison.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace Matrix ProbabilityTheory

/-! ### Setup and abbreviations -/

/-- **The pair-indexed function class** `𝓕 = {ψ_{θ,η,j} : (θ,η) ∈ S, j ∈ Fin k}`.
It collects the coordinate estimating functions `ψ p.1 p.2 j` as the pair
`p = (θ,η)` ranges over `S ⊆ ℝᵏ × H` and `j` over the `k` fibers. It is the
nuisance analogue of `paramClass` and appears in the Donsker hypothesis
`IsPDonsker (pairClass ψ (ball ×ˢ ball)) P`. (vdV §5.4 p.60: "the class of functions {ψ_{θ,η} : ‖θ−θ₀‖ < δ,
d(η,η₀) < δ}".) -/
def pairClass {k : ℕ} {Ω : Type*} {H : Type*}
    (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (S : Set (EuclideanSpace ℝ (Fin k) × H)) : Set (Ω → ℝ) :=
  {g | ∃ p ∈ S, ∃ j, g = ψ p.1 p.2 j}

/-- **The drift vector** `P ψ_{θ₀,η}` bundled into `EuclideanSpace ℝ (Fin k)`.
Coordinate `j` is the mean `∫ ψ_{θ₀,η,j} dP`; at the true nuisance
`Pψ_{θ₀,η₀} = 0`, but for the estimated `η̂ₙ` it is the nonzero **drift** whose
norm sets the weight `wDrift`. (vdV §5.4 p.60: the `√n P ψ_{θ₀,η̂ₙ}` term of the
linear representation.) -/
noncomputable def driftVec {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] {H : Type*}
    (P : Measure Ω) (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η : H) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j => ∫ x, ψ θ₀ η j x ∂P)

/-! ### Master identity with drift -/

/-- **Pair master identity** (pure algebra; vdV §5.4 / 5.21 rearrangement
with the nuisance drift term). For a realized `b : ℝᵏ` (= `θ̂ₙ`), nuisance
`η : H` (= `η̂ₙ`), sample `Xs`, and coordinate `j`:

    √n Vlin(V η)(b − θ₀)_j + 𝔾ₙψ_{θ₀,η₀,j} + √n Pψ_{θ₀,η,j}
      = √n ℙₙψ_{b,η,j} − (𝔾ₙψ_{b,η,j} − 𝔾ₙψ_{θ₀,η₀,j}) − S_{n,j}

with `S_{n,j} := √n(Pψ_{b,η,j} − Pψ_{θ₀,η,j}) − √n Vlin(V η)(b − θ₀)_j`. Proved by
unfolding `empiricalProcess`; no hypothesis needed (mirror `master_identity`,
`InfiniteDimZEstimator.lean`). -/
theorem pair_master_identity
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] {H : Type*}
    (P : Measure Ω) (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η₀ : H) (V : H → Matrix (Fin k) (Fin k) ℝ)
    (n : ℕ) (Xs : Fin n → Ω) (b : EuclideanSpace ℝ (Fin k)) (η : H) (j : Fin k) :
    Real.sqrt n * Vlin (V η) (b - θ₀) j
        + empiricalProcess P n Xs (ψ θ₀ η₀ j)
        + Real.sqrt n * (∫ x, ψ θ₀ η j x ∂P)
      = Real.sqrt n * empiricalAvg (ψ b η j) n Xs
        - (empiricalProcess P n Xs (ψ b η j) - empiricalProcess P n Xs (ψ θ₀ η₀ j))
        - (Real.sqrt n * (∫ x, ψ b η j x ∂P) - Real.sqrt n * (∫ x, ψ θ₀ η j x ∂P)
            - Real.sqrt n * Vlin (V η) (b - θ₀) j) := by
  simp only [empiricalProcess]
  ring

/-! ### The uniform Fréchet remainder -/

/-- **Pair Fréchet remainder bound.** With
`r_n(ξ) := √n‖θ̂ₙ − θ₀‖` and remainder
`S_{n,ξ,j} := √n(Pψ_{θ̂ₙ,η̂ₙ,j} − Pψ_{θ₀,η̂ₙ,j}) − √n Vlin(V η̂ₙ)(θ̂ₙ − θ₀)_j`, the
`η`-uniform Fréchet `ε-δ` bound (`hfrechet_unif`) gives `sup_j |S| ≤ ε·r_n` on
`{‖θ̂ₙ−θ₀‖ < δ} ∩ {d(η̂ₙ,η₀) < δ}`, and both consistencies kill the complement.
Hence for every `ε > 0`, `μ*{ξ | ∃j, ε·r_n < |S|} → 0`. Mirror of
`frechet_remainder_sup_bound`; the difference form `Pψ_{θ̂,η̂}−Pψ_{θ₀,η̂}` needs no
`Pψ₀=0`. The threshold uses `r_n = √n‖θ̂−θ₀‖`. -/
theorem frechet_remainder_pair_sup_bound
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] {H : Type*} [MetricSpace H]
    (P : Measure Ω) (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η₀ : H) (V : H → Matrix (Fin k) (Fin k) ℝ)
    (hfrechet_unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (η : H), dist η η₀ < δ →
        ∀ θ : EuclideanSpace ℝ (Fin k), 0 < ‖θ - θ₀‖ → ‖θ - θ₀‖ < δ →
        (⨆ h, ENNReal.ofReal
            |∫ x, ψ θ η h x ∂P - ∫ x, ψ θ₀ η h x ∂P - Vlin (V η) (θ - θ₀) h|)
          ≤ ENNReal.ofReal (ε * ‖θ - θ₀‖))
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (eta_hat : ∀ n, (Fin n → Ω) → H) (X : ℕ → Ξ → Ω)
    (h_consist_θ : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0))
    (h_consist_η : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      μ.outerMeasureStar {ξ | ∃ j,
        ε * (Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) <
          |Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ))
              (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
            - Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
            - Real.sqrt n * Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
                (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j|})
      atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hbd⟩ := hfrechet_unif ε hε
  -- Squeeze `μ*(Eₙ)` between `0` and `μ{δ/2 < ‖θ̂ₙ−θ₀‖} + μ{δ/2 < dist(η̂ₙ,η₀)} → 0`.
  have hsum : Tendsto (fun n => μ {ξ | δ / 2 < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}
      + μ {ξ | δ / 2 < dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) atTop (𝓝 0) := by
    simpa using (h_consist_θ (δ / 2) (half_pos hδ)).add (h_consist_η (δ / 2) (half_pos hδ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  -- `μ*(Eₙ) ≤ μ*(A ∪ B) ≤ μ*(A) + μ*(B) ≤ μ(A) + μ(B)`.
  refine (outerMeasureStar_mono μ ?_).trans
    ((outerMeasureStar_union_le μ _ _).trans
      (add_le_add (outerMeasureStar_le_measure μ _) (outerMeasureStar_le_measure μ _)))
  -- Inclusion `Eₙ ⊆ {δ/2 < ‖θ̂ₙ−θ₀‖} ∪ {δ/2 < dist(η̂ₙ,η₀)}`.
  intro ξ hξ
  obtain ⟨j, hj⟩ := hξ
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra hcon
  rw [not_or, not_lt, not_lt] at hcon
  obtain ⟨hnA, hnB⟩ := hcon
  set b := θ_hat n (fun i : Fin n => X i.val ξ) with hbdef
  set η := eta_hat n (fun i : Fin n => X i.val ξ) with hηdef
  -- `|S_j| ≤ ε · rₙ`, contradicting `hj`.
  have hkey : |Real.sqrt n * (∫ x, ψ b η j x ∂P)
      - Real.sqrt n * (∫ x, ψ θ₀ η j x ∂P)
      - Real.sqrt n * Vlin (V η) (b - θ₀) j|
      ≤ ε * (Real.sqrt n * ‖b - θ₀‖) := by
    rcases eq_or_lt_of_le (norm_nonneg (b - θ₀)) with hzero | hpos
    · -- `b = θ₀`: the remainder vanishes.
      have hb0 : b - θ₀ = 0 := norm_eq_zero.1 hzero.symm
      have hbθ : b = θ₀ := by rwa [sub_eq_zero] at hb0
      simp [hbθ, map_zero]
    · -- `0 < ‖b−θ₀‖ ≤ δ/2 < δ` and `dist η η₀ ≤ δ/2 < δ`: use the Fréchet bound.
      have hδ' : ‖b - θ₀‖ < δ := lt_of_le_of_lt hnA (by linarith)
      have hdist' : dist η η₀ < δ := lt_of_le_of_lt hnB (by linarith)
      have hsup := hbd η hdist' b hpos hδ'
      have hle : ENNReal.ofReal
          |∫ x, ψ b η j x ∂P - ∫ x, ψ θ₀ η j x ∂P - Vlin (V η) (b - θ₀) j|
          ≤ ENNReal.ofReal (ε * ‖b - θ₀‖) :=
        le_trans (le_iSup (fun h' : Fin k => ENNReal.ofReal
          |∫ x, ψ b η h' x ∂P - ∫ x, ψ θ₀ η h' x ∂P - Vlin (V η) (b - θ₀) h'|) j) hsup
      have hreal : |∫ x, ψ b η j x ∂P - ∫ x, ψ θ₀ η j x ∂P - Vlin (V η) (b - θ₀) j|
          ≤ ε * ‖b - θ₀‖ :=
        (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hε.le (norm_nonneg _))).1 hle
      calc |Real.sqrt n * (∫ x, ψ b η j x ∂P)
            - Real.sqrt n * (∫ x, ψ θ₀ η j x ∂P)
            - Real.sqrt n * Vlin (V η) (b - θ₀) j|
          = Real.sqrt n
              * |∫ x, ψ b η j x ∂P - ∫ x, ψ θ₀ η j x ∂P - Vlin (V η) (b - θ₀) j| := by
            rw [← mul_sub, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ Real.sqrt n * (ε * ‖b - θ₀‖) :=
            mul_le_mul_of_nonneg_left hreal (Real.sqrt_nonneg _)
        _ = ε * (Real.sqrt n * ‖b - θ₀‖) := by ring
  exact absurd hkey (not_le.2 hj)

/-! ### Uniform boundedness below on a nuisance neighborhood -/

/-- **Neighborhood bounded-below derivative.** From
`IsUnit (V η₀).det` and `ContinuousAt V η₀`, there is a nuisance ball
`{η : d(η,η₀) < δV}` on which `Vlin (V η)` is uniformly bounded below:
`∃ c > 0, δV > 0, ∀ η, d(η,η₀) < δV → ∀ b, ofReal(c‖b‖) ≤ ⨆ⱼ ofReal|Vlin(V η) b_j|`.
The proof uses `matrix_bddbelow_of_isUnit_det` to obtain `c₀` for `V η₀`;
entrywise continuity of `V` at `η₀` makes `V η` close to `V η₀`, so
`⨆ⱼ|V η b_j| ≥ ⨆ⱼ|V η₀ b_j| −
k·maxent(Δ)·‖b‖`; take `c := c₀/2`. This also proves that nearby `V η` are
nonsingular, without an additional nonsingularity hypothesis. -/
theorem matrix_bddbelow_near
    {k : ℕ} {H : Type*} [MetricSpace H]
    (V : H → Matrix (Fin k) (Fin k) ℝ) (η₀ : H)
    (hV : IsUnit (V η₀).det) (hV_cont : ContinuousAt V η₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ δV : ℝ, 0 < δV ∧ ∀ η : H, dist η η₀ < δV →
      ∀ b : EuclideanSpace ℝ (Fin k),
        ENNReal.ofReal (c * ‖b‖) ≤ ⨆ j, ENNReal.ofReal |Vlin (V η) b j| := by
  -- `c₀` for the true matrix `V η₀`.
  obtain ⟨c₀, hc₀_pos, hc₀_bd⟩ := matrix_bddbelow_of_isUnit_det (V η₀) hV
  -- Entrywise total deviation `F η = ∑ⱼ∑ᵢ |V η j i − V η₀ j i|` is continuous at η₀.
  have hF_cont : ContinuousAt
      (fun η : H => ∑ j, ∑ i, |(V η) j i - (V η₀) j i|) η₀ := by
    have hg : Continuous
        (fun M : Matrix (Fin k) (Fin k) ℝ => ∑ j, ∑ i, |M j i - (V η₀) j i|) := by
      refine continuous_finset_sum _ (fun j _ => continuous_finset_sum _ (fun i _ => ?_))
      exact ((continuous_id.matrix_elem j i).sub continuous_const).abs
    exact hg.continuousAt.comp hV_cont
  -- Extract `δV` from continuity with tolerance `c₀/2`.
  rw [Metric.continuousAt_iff] at hF_cont
  obtain ⟨δV, hδV_pos, hδV⟩ := hF_cont (c₀ / 2) (by positivity)
  refine ⟨c₀ / 2, by positivity, δV, hδV_pos, fun η hη b => ?_⟩
  -- `F η < c₀/2`.
  have hFη : ∑ j, ∑ i, |(V η) j i - (V η₀) j i| < c₀ / 2 := by
    have hd := hδV hη
    simp only [Real.dist_eq] at hd
    have hFη0 : (∑ j, ∑ i, |(V η₀) j i - (V η₀) j i|) = 0 := by simp
    rwa [hFη0, sub_zero, abs_of_nonneg (Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ => abs_nonneg _)] at hd
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: `‖b‖ = 0`, so the LHS is `0`.
    have hb : ‖b‖ = 0 := by rw [EuclideanSpace.norm_eq]; subst hk0; simp
    rw [hb, mul_zero, ENNReal.ofReal_zero]; exact zero_le
  · haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    -- Coordinate formula for `Vlin`.
    have hVlin_coord : ∀ (M : Matrix (Fin k) (Fin k) ℝ) (j : Fin k),
        Vlin M b j = ∑ i, M j i * b i := fun M j => rfl
    -- Coordinate bound `|b i| ≤ ‖b‖`.
    have hcoordbd : ∀ i, |b i| ≤ ‖b‖ := by
      intro i
      have h1 : ‖b i‖ ≤ ‖b‖ := by
        rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (b i))]
        apply Real.sqrt_le_sqrt
        exact Finset.single_le_sum (f := fun j => ‖b j‖ ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rwa [Real.norm_eq_abs] at h1
    -- Per-coordinate perturbation bound.
    have hpert : ∀ j, |Vlin (V η) b j - Vlin (V η₀) b j|
        ≤ (∑ i, |(V η) j i - (V η₀) j i|) * ‖b‖ := by
      intro j
      rw [hVlin_coord, hVlin_coord, ← Finset.sum_sub_distrib]
      have hstep : ∀ i, (V η) j i * b i - (V η₀) j i * b i
          = ((V η) j i - (V η₀) j i) * b i := fun i => by ring
      simp_rw [hstep]
      calc |∑ i, ((V η) j i - (V η₀) j i) * b i|
          ≤ ∑ i, |((V η) j i - (V η₀) j i) * b i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |(V η) j i - (V η₀) j i| * ‖b‖ := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hcoordbd i) (abs_nonneg _)
        _ = (∑ i, |(V η) j i - (V η₀) j i|) * ‖b‖ := by rw [Finset.sum_mul]
    -- Maximizing coordinate of `V η₀`.
    obtain ⟨h₀, hmax⟩ := Finite.exists_max (fun j => |Vlin (V η₀) b j|)
    have hsup_eq : (⨆ j, ENNReal.ofReal |Vlin (V η₀) b j|)
        = ENNReal.ofReal |Vlin (V η₀) b h₀| :=
      le_antisymm (iSup_le fun j => ENNReal.ofReal_le_ofReal (hmax j))
        (le_iSup (fun j => ENNReal.ofReal |Vlin (V η₀) b j|) h₀)
    have hc₀_real : c₀ * ‖b‖ ≤ |Vlin (V η₀) b h₀| := by
      have hb := hc₀_bd b
      rw [hsup_eq] at hb
      exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).1 hb
    -- Perturbation at `h₀` is `≤ (c₀/2)‖b‖`.
    have hpert0 : |Vlin (V η) b h₀ - Vlin (V η₀) b h₀| ≤ (c₀ / 2) * ‖b‖ := by
      refine le_trans (hpert h₀) (mul_le_mul_of_nonneg_right (le_trans ?_ hFη.le)
        (norm_nonneg _))
      exact Finset.single_le_sum
        (f := fun j => ∑ i, |(V η) j i - (V η₀) j i|)
        (fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ h₀)
    -- Reverse triangle: `(c₀/2)‖b‖ ≤ |Vlin (V η) b h₀|`.
    have hlower : (c₀ / 2) * ‖b‖ ≤ |Vlin (V η) b h₀| := by
      have hrt := abs_sub_abs_le_abs_sub (Vlin (V η₀) b h₀) (Vlin (V η) b h₀)
      rw [abs_sub_comm (Vlin (V η₀) b h₀) (Vlin (V η) b h₀)] at hrt
      linarith [hrt, hpert0, hc₀_real]
    calc ENNReal.ofReal (c₀ / 2 * ‖b‖)
        ≤ ENNReal.ofReal |Vlin (V η) b h₀| := ENNReal.ofReal_le_ofReal hlower
      _ ≤ ⨆ j, ENNReal.ofReal |Vlin (V η) b j| :=
          le_iSup (fun j => ENNReal.ofReal |Vlin (V η) b j|) h₀

/-! ### The derivative swap `V η₀ ↔ V η̂` -/

/-- **Derivative-swap remainder.** The family
`fun n ξ j => √n Vlin(V η₀ − V η̂ₙ)(θ̂ₙ − θ₀)_j` is weighted-`o_P` relative to
`wDrift`. The bound `|gap_j| ≤ k·maxent(V η₀ − V η̂ₙ)·‖θ̂ₙ − θ₀‖`, the entrywise
modulus `maxent(V η₀ − V η̂ₙ) →ₚ 0` (`hV_cont` ε-δ + η-consistency), and the
rate `√n‖θ̂ₙ − θ₀‖ = O_P(wDrift)` (`h_rate`) combine through
`oPWt_of_coeff_mul_rate`. -/
theorem vSwap_oPWt
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] {H : Type*} [MetricSpace H]
    (P : Measure Ω) (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η₀ : H) (V : H → Matrix (Fin k) (Fin k) ℝ)
    (hV_cont : ContinuousAt V η₀)
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (eta_hat : ∀ n, (Fin n → Ω) → H) (X : ℕ → Ξ → Ω)
    (h_consist_η : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) atTop (𝓝 0))
    (h_rate : IsBoundedInOuterProbScalarWt μ
      (fun n ξ => 1 + Real.sqrt n *
        ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)
      (fun n ξ => Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖)) :
    TendstoZeroInOuterProbSupWt μ
      (fun n ξ => 1 + Real.sqrt n *
        ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)
      (fun n ξ j => Real.sqrt n *
        Vlin (V η₀ - V (eta_hat n (fun i : Fin n => X i.val ξ)))
          (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j) := by
  -- The weight is `≥ 1`.
  have hw : ∀ (n : ℕ) (ξ : Ξ), (1 : ℝ) ≤ 1 + Real.sqrt n *
      ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ := by
    intro n ξ
    have h0 : 0 ≤ Real.sqrt n *
        ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    linarith
  -- Coordinate bound `|b i| ≤ ‖b‖` on `EuclideanSpace`.
  have hcoordbd : ∀ (b : EuclideanSpace ℝ (Fin k)) (i : Fin k), |b i| ≤ ‖b‖ := by
    intro b i
    have h1 : ‖b i‖ ≤ ‖b‖ := by
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (b i))]
      apply Real.sqrt_le_sqrt
      exact Finset.single_le_sum (f := fun j => ‖b j‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    rwa [Real.norm_eq_abs] at h1
  -- Entrywise total deviation `F η = ∑ⱼ∑ᵢ |(V η₀ − V η) j i|` is continuous at `η₀`.
  have hF_cont : ContinuousAt
      (fun η : H => ∑ j, ∑ i, |(V η₀ - V η) j i|) η₀ := by
    have hg : Continuous
        (fun M : Matrix (Fin k) (Fin k) ℝ => ∑ j, ∑ i, |(V η₀ - M) j i|) := by
      simp only [Matrix.sub_apply]
      refine continuous_finset_sum _ (fun j _ => continuous_finset_sum _ (fun i _ => ?_))
      exact (continuous_const.sub (continuous_id.matrix_elem j i)).abs
    exact hg.continuousAt.comp hV_cont
  rw [Metric.continuousAt_iff] at hF_cont
  -- The entrywise modulus is `→ₚ 0` (`hV_cont` ε-δ + η-consistency).
  have h_coeff : TendstoZeroInOuterProbScalar μ
      (fun n ξ => ∑ j, ∑ i,
        |(V η₀ - V (eta_hat n (fun i : Fin n => X i.val ξ))) j i|) := by
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := hF_cont ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h_consist_η (δ / 2) (half_pos hδ_pos))
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    refine (outerMeasureStar_mono μ ?_).trans (outerMeasureStar_le_measure μ _)
    -- `{ε < coeff} ⊆ {δ/2 < dist(η̂ₙ, η₀)}`.
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    by_contra hcon
    push_neg at hcon
    have hd : dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀ < δ :=
      lt_of_le_of_lt hcon (by linarith)
    have hFsmall := hδ hd
    have hnonneg : ∀ η : H, (0 : ℝ) ≤ ∑ j, ∑ i, |(V η₀ - V η) j i| := fun η =>
      Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _
    have hF0 : (∑ j, ∑ i, |(V η₀ - V η₀) j i|) = 0 := by simp
    rw [Real.dist_eq, hF0, sub_zero, abs_of_nonneg (hnonneg _)] at hFsmall
    rw [abs_of_nonneg (hnonneg _)] at hξ
    linarith
  -- Entrywise domination `|√n · Vlin(V η₀ − V η̂ₙ)(θ̂ₙ − θ₀)_j| ≤ coeff · rate`.
  have h_dom : ∀ (n : ℕ) (ξ : Ξ) (j : Fin k),
      |Real.sqrt n * Vlin (V η₀ - V (eta_hat n (fun i : Fin n => X i.val ξ)))
          (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j|
        ≤ (∑ j', ∑ i, |(V η₀ - V (eta_hat n (fun i : Fin n => X i.val ξ))) j' i|)
          * (Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖) := by
    intro n ξ j
    set M := V η₀ - V (eta_hat n (fun i : Fin n => X i.val ξ)) with hMdef
    set b := θ_hat n (fun i : Fin n => X i.val ξ) - θ₀ with hbdef
    have hVlin_coord : Vlin M b j = ∑ i, M j i * b i := rfl
    have h1 : |Vlin M b j| ≤ (∑ i, |M j i|) * ‖b‖ := by
      rw [hVlin_coord]
      calc |∑ i, M j i * b i| ≤ ∑ i, |M j i * b i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, |M j i| * ‖b‖ := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left (hcoordbd b i) (abs_nonneg _)
        _ = (∑ i, |M j i|) * ‖b‖ := by rw [Finset.sum_mul]
    have h2 : (∑ i, |M j i|) ≤ ∑ j', ∑ i, |M j' i| :=
      Finset.single_le_sum (f := fun j' => ∑ i, |M j' i|)
        (fun j' _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ j)
    calc |Real.sqrt n * Vlin M b j| = Real.sqrt n * |Vlin M b j| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt n * ((∑ j', ∑ i, |M j' i|) * ‖b‖) := by
          refine mul_le_mul_of_nonneg_left (le_trans h1 ?_) (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = (∑ j', ∑ i, |M j' i|) * (Real.sqrt n * ‖b‖) := by ring
  -- Combine: `coeff →ₚ 0` times the `O_P(wDrift)` rate.
  exact oPWt_of_coeff_mul_rate hw
    (fun n ξ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => abs_nonneg _)
    (fun n ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    h_coeff h_rate h_dom

/-! ### `L²` membership and marginal tightness at the `η₀` slice -/

/-- **`ψ_{·,η₀}` is `L²(P)`.** The bundled
estimating function `psiVec ψ(·,η₀) θ₀` is square-integrable, derived from
`hDonsker.marginalCLT.memLp` (each `ψ_{θ₀,η₀,j} ∈ 𝓕` is `L²`) and the coordinatewise
`MemLp` theorem on `PiLp 2`. Thus it follows from the Donsker assumption of vdV
Theorem 5.31. -/
theorem pair_hpsi_L2
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] {H : Type*} [MetricSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η₀ : H) (δcls : ℝ) (hδcls : 0 < δcls)
    (hDonsker : IsPDonsker
      (pairClass ψ (Metric.ball θ₀ δcls ×ˢ Metric.ball η₀ δcls)) P) :
    MemLp (psiVec (fun θ h => ψ θ η₀ h) θ₀) 2 P := by
  -- `MemLp` on `PiLp 2` is coordinatewise; each coordinate lies in the Donsker class.
  refine MemLp.of_eval_piLp (fun j => ?_)
  have hmem : ψ θ₀ η₀ j ∈ pairClass ψ (Metric.ball θ₀ δcls ×ˢ Metric.ball η₀ δcls) :=
    ⟨(θ₀, η₀), ⟨Metric.mem_ball_self hδcls, Metric.mem_ball_self hδcls⟩, j, rfl⟩
  exact hDonsker.marginalCLT.memLp _ hmem

/-- **Marginal tightness of `𝔾ₙψ_{θ₀,η₀}`.** The `η₀`-slice
empirical process is `O_P(1)` in the `ℓ∞(Fin k)` sup, derived from the vector CLT
(`empiricalProcessVec_weakConverges` at slice `ψ(·,η₀)`) via
`isBoundedInProb_of_weakConverges` and the finite-coordinate collapse. This
supplies the `hA` and `h_tight` assumptions used in the weighted bootstrap. -/
theorem pair_h_tight
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] {H : Type*} [MetricSpace H]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η₀ : H)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hψθ₀_meas : ∀ h, Measurable (ψ θ₀ η₀ h))
    (hψ_L2 : MemLp (psiVec (fun θ h => ψ θ η₀ h) θ₀) 2 P)
    (hPθ₀_zero : ∀ h, ∫ x, ψ θ₀ η₀ h x ∂P = 0) :
    IsBoundedInOuterProbSup μ (fun n ξ h =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ h)) := by
  -- The `η₀`-slice vector empirical process converges weakly, hence is `O_P(1)`.
  haveI : IsProbabilityMeasure
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k))
        (psiCov P (fun θ h => ψ θ η₀ h) θ₀)) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  have hC := empiricalProcessVec_weakConverges P (fun θ h => ψ θ η₀ h) θ₀ μ X hX_meas
    hX_indep hX_id hX_law hψθ₀_meas hψ_L2 hPθ₀_zero
  have heproc_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hpi : Measurable (fun ξ : Ξ =>
        (fun h => empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ h) :
          Fin k → ℝ)) := by
      refine measurable_pi_iff.mpr (fun h => ?_)
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hψθ₀_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin k → ℝ)).measurable.comp hpi
  have hbdd := isBoundedInProb_of_weakConverges (P := fun _ : ℕ => μ) heproc_meas hC
  intro η hη
  obtain ⟨MM, hMM⟩ := hbdd η hη
  refine ⟨MM, ?_⟩
  -- Each coordinate of a Euclidean vector is bounded by its norm.
  have hcoordbd : ∀ (v : EuclideanSpace ℝ (Fin k)) (h : Fin k), |v h| ≤ ‖v‖ := by
    intro v h
    have h1 : ‖v h‖ ≤ ‖v‖ := by
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (v h))]
      apply Real.sqrt_le_sqrt
      exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ h)
    rwa [Real.norm_eq_abs] at h1
  -- The `∃h` exceedance sits inside the Euclidean-norm exceedance.
  have hsub : ∀ n, {ξ | ∃ h, MM <
        |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ h)|}
      ⊆ {ξ | MM < ‖empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
        (fun i : Fin n => X i.val ξ)‖} := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    obtain ⟨h, hh⟩ := hξ
    have hcoord : empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ h)
        = (empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
            (fun i : Fin n => X i.val ξ)) h := rfl
    rw [hcoord] at hh
    exact lt_of_lt_of_le hh (hcoordbd _ h)
  have hb : ∀ n, μ.outerMeasureStar {ξ | ∃ h, MM <
      |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ h)|}
      ≤ ENNReal.ofReal η := by
    intro n
    calc μ.outerMeasureStar {ξ | ∃ h, MM <
          |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ h)|}
        ≤ μ.outerMeasureStar {ξ | MM < ‖empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
            (fun i : Fin n => X i.val ξ)‖} :=
          outerMeasureStar_mono μ (hsub n)
      _ ≤ μ {ξ | MM < ‖empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
            (fun i : Fin n => X i.val ξ)‖} :=
          outerMeasureStar_le_measure μ _
      _ ≤ ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_toReal (measure_ne_top μ
            {ξ | MM < ‖empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
              (fun i : Fin n => X i.val ξ)‖})]
          exact ENNReal.ofReal_le_ofReal (hMM n)
  calc limsup (fun n => μ.outerMeasureStar {ξ | ∃ h, MM <
        |empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ h)|}) atTop
      ≤ limsup (fun _ : ℕ => ENNReal.ofReal η) atTop :=
        limsup_le_limsup (Eventually.of_forall hb) isCobounded_le_of_bot
          (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ = ENNReal.ofReal η := limsup_const _

/-! ### Weighted `o_P(wDrift)` bound for the assembled residual -/

/-- Weighted `o_P` is closed under negation: `|−x| = |x|`,
so the two weighted exceedance events coincide. -/
theorem TendstoZeroInOuterProbSupWt.neg {Ξ H : Type*} [MeasurableSpace Ξ]
    {μ : Measure Ξ} {w : ℕ → Ξ → ℝ} {g : ℕ → Ξ → H → ℝ}
    (h : TendstoZeroInOuterProbSupWt μ w g) :
    TendstoZeroInOuterProbSupWt μ w (fun n ξ h => -g n ξ h) := by
  intro ε hε
  simpa only [abs_neg] using h ε hε

/-- With a weight `w ≥ 1`, an unweighted `o_P(1)` family is
automatically `o_P(w)`: `ε ≤ ε · w`, so the weighted exceedance event
`{∃h, ε·w < |g|}` is contained in the unweighted one `{∃h, ε < |g|}`. -/
theorem tendstoZeroInOuterProbSupWt_of_tendstoZeroInOuterProbSup
    {Ξ H : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} {w : ℕ → Ξ → ℝ}
    (hw : ∀ n ξ, 1 ≤ w n ξ) {g : ℕ → Ξ → H → ℝ}
    (h : TendstoZeroInOuterProbSup μ g) :
    TendstoZeroInOuterProbSupWt μ w g := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h ε hε)
    (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
  refine outerMeasureStar_mono μ fun ξ hξ => ?_
  obtain ⟨h', hh'⟩ := hξ
  exact ⟨h', lt_of_le_of_lt (le_mul_of_one_le_right hε.le (hw n ξ)) hh'⟩

/-- An unweighted `O_P(1)` family plus a family dominated
by the weight is `O_P(w)` (for `w ≥ 1`). Exactly the shape the `hA` input of
`rate_bootstrap_oP_wt` needs in the nuisance core: the `O_P(1)` part is
`√nℙₙψ_{θ̂,η̂} − (𝔾ₙψ_{θ̂,η̂} − 𝔾ₙψ_{θ₀,η₀}) − 𝔾ₙψ_{θ₀,η₀}` and the dominated part is
the drift `−√n(Pψ_{θ₀,η̂ₙ})_j`, whose modulus is `≤ √n‖Pψ_{θ₀,η̂ₙ}‖ ≤ wDrift`. -/
theorem isBoundedInOuterProbSupWt_add_wt_dominated
    {Ξ H : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} {w : ℕ → Ξ → ℝ}
    (hw : ∀ n ξ, 1 ≤ w n ξ) {g₁ g₂ : ℕ → Ξ → H → ℝ}
    (h₁ : IsBoundedInOuterProbSup μ g₁) (h₂ : ∀ n ξ h, |g₂ n ξ h| ≤ w n ξ) :
    IsBoundedInOuterProbSupWt μ w (fun n ξ h => g₁ n ξ h + g₂ n ξ h) := by
  intro η hη
  obtain ⟨M, hM⟩ := h₁ η hη
  refine ⟨max M 0 + 1, le_trans (limsup_le_limsup (Eventually.of_forall fun n =>
    outerMeasureStar_mono μ ?_) isCobounded_le_of_bot
    (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)) hM⟩
  intro ξ hξ
  obtain ⟨h', hh'⟩ := hξ
  refine ⟨h', ?_⟩
  have hexp : (max M 0 + 1) * w n ξ = max M 0 * w n ξ + w n ξ := by ring
  rw [hexp] at hh'
  have htri : |g₁ n ξ h' + g₂ n ξ h'| ≤ |g₁ n ξ h'| + |g₂ n ξ h'| := abs_add_le _ _
  have hmul : max M 0 ≤ max M 0 * w n ξ :=
    le_mul_of_one_le_right (le_max_right _ _) (hw n ξ)
  have hMle : M ≤ max M 0 := le_max_left _ _
  linarith [h₂ n ξ h']

/-- **Weighted nuisance remainder.** The coordinatewise residual

    fun n ξ j => √n Vlin(V η₀)(θ̂ₙ − θ₀)_j + 𝔾ₙψ_{θ₀,η₀,j} + √n (driftVec η̂ₙ)_j

is weighted-`o_P` relative to `wDrift n ξ = 1 + √n‖driftVec η̂ₙ‖`. Mirroring
`infinite_dim_z_estimator`, `pair_master_identity` rewrites the residual
into the `o_P` estimating equation (`h_est_eq`) minus the uniform-19.24 remainder
(`guardedRandomFunction` and `uniform_donsker_random_function_consistency`) minus
the Fréchet remainder (`rate_bootstrap_oP_wt`, using the bounded-below estimate
on the guard event `bad := {η̂ₙ outside δV}`), with the derivative swap and the drift
absorbed by weight domination (`isBoundedInOuterProbSupWt_of_le_wt`);
`oP_supWt_add` combines. -/
theorem nuisance_weighted_core
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {H : Type*} [MetricSpace H]
    (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η₀ : H)
    (V : H → Matrix (Fin k) (Fin k) ℝ)
    (hV : IsUnit (V η₀).det) (hV_cont : ContinuousAt V η₀)
    (δcls : ℝ) (hδcls : 0 < δcls)
    (hDonsker : IsPDonsker
      (pairClass ψ (Metric.ball θ₀ δcls ×ˢ Metric.ball η₀ δcls)) P)
    (hL2_cont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : EuclideanSpace ℝ (Fin k)) (η : H),
        ‖θ - θ₀‖ < δ → dist η η₀ < δ →
        ∑ j, ∫ x, (ψ θ η j x - ψ θ₀ η₀ j x)^2 ∂P < ε)
    (hPθ₀_zero : ∀ h, ∫ x, ψ θ₀ η₀ h x ∂P = 0)
    (hfrechet_unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (η : H), dist η η₀ < δ →
        ∀ θ : EuclideanSpace ℝ (Fin k), 0 < ‖θ - θ₀‖ → ‖θ - θ₀‖ < δ →
        (⨆ h, ENNReal.ofReal
            |∫ x, ψ θ η h x ∂P - ∫ x, ψ θ₀ η h x ∂P - Vlin (V η) (θ - θ₀) h|)
          ≤ ENNReal.ofReal (ε * ‖θ - θ₀‖))
    (hψ_meas : ∀ (θ : EuclideanSpace ℝ (Fin k)) (η : H) (j : Fin k), Measurable (ψ θ η j))
    (hψ_L2 : MemLp (psiVec (fun θ h => ψ θ η₀ h) θ₀) 2 P)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (eta_hat : ∀ n, (Fin n → Ω) → H)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (h_consist_θ : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0))
    (h_consist_η : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) atTop (𝓝 0))
    (h_est_eq : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
        (eta_hat n (fun i : Fin n => X i.val ξ)) h) n (fun i : Fin n => X i.val ξ))) :
    TendstoZeroInOuterProbSupWt μ
      (fun n ξ => 1 + Real.sqrt n *
        ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)
      (fun n ξ j =>
        Real.sqrt n * Vlin (V η₀) (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
        + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
        + Real.sqrt n *
            (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j) := by
  classical
  -- ======================= Setup / elementary facts =======================
  -- The drift weight is `≥ 1`.
  have hw : ∀ (n : ℕ) (ξ : Ξ), (1 : ℝ) ≤ 1 + Real.sqrt n *
      ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ := by
    intro n ξ
    have h0 : (0 : ℝ) ≤ Real.sqrt n *
        ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    linarith
  -- Coordinates of the drift vector are the coordinate means.
  have hdrift_coord : ∀ (η : H) (j : Fin k),
      driftVec P ψ θ₀ η j = ∫ x, ψ θ₀ η j x ∂P := fun _ _ => rfl
  -- Euclidean coordinate bound `|v j| ≤ ‖v‖`.
  have hcoord_le : ∀ (v : EuclideanSpace ℝ (Fin k)) (j : Fin k), |v j| ≤ ‖v‖ := by
    intro v j
    have h1 : ‖v j‖ ≤ ‖v‖ := by
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg (v j))]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j))
    rwa [Real.norm_eq_abs] at h1
  -- `Vlin` is additive in the matrix argument.
  have hlin : ∀ (A B : Matrix (Fin k) (Fin k) ℝ) (b : EuclideanSpace ℝ (Fin k))
      (j : Fin k), Vlin (A - B) b j = Vlin A b j - Vlin B b j := by
    intro A B b j
    have hc : ∀ M : Matrix (Fin k) (Fin k) ℝ, Vlin M b j = ∑ i, M j i * b i :=
      fun _ => rfl
    rw [hc, hc, hc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.sub_apply, sub_mul]
  -- The derivative is bounded below on a nuisance ball around `η₀`.
  obtain ⟨c, hc_pos, δV, hδV_pos, hV_bd⟩ := matrix_bddbelow_near V η₀ hV hV_cont
  -- The uniform Lemma 19.24 remainder `Rhat` is `o_P(1)`.
  -- Pair consistency `(θ̂ₙ, η̂ₙ) →ₚ (θ₀, η₀)` in the max-metric of the product.
  have h_pair_consist : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < dist ((θ_hat n (fun i : Fin n => X i.val ξ),
        eta_hat n (fun i : Fin n => X i.val ξ)) :
          EuclideanSpace ℝ (Fin k) × H) (θ₀, η₀)}) atTop (𝓝 0) := by
    intro ε hε
    have hsum : Tendsto (fun n =>
        μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}
        + μ {ξ | ε < dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) atTop (𝓝 0) := by
      simpa using (h_consist_θ ε hε).add (h_consist_η ε hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ξ hξ
    simp only [Set.mem_setOf_eq, Prod.dist_eq, lt_max_iff, dist_eq_norm] at hξ
    simp only [Set.mem_union, Set.mem_setOf_eq]
    exact hξ
  -- Uniform `L²`-continuity of the plug-in pair `(θ̂ₙ, η̂ₙ)`.
  have h_sup : TendstoZeroInOuterProbSup μ (fun n ξ (j : Fin k) =>
      distL2 P (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
        (eta_hat n (fun i : Fin n => X i.val ξ)) j) (ψ θ₀ η₀ j)) := by
    have hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ t : EuclideanSpace ℝ (Fin k) × H, dist t (θ₀, η₀) < δ →
        (⨆ j : Fin k, ENNReal.ofReal (distL2 P (ψ t.1 t.2 j) (ψ θ₀ η₀ j)))
          ≤ ENNReal.ofReal ε := by
      intro ε hε
      obtain ⟨δ, hδpos, hbd⟩ := hL2_cont (ε ^ 2) (by positivity)
      refine ⟨δ, hδpos, fun t ht => ?_⟩
      rw [Prod.dist_eq, max_lt_iff] at ht
      have ht1 : ‖t.1 - θ₀‖ < δ := by
        have ht1' := ht.1
        rwa [dist_eq_norm] at ht1'
      have hsum := hbd t.1 t.2 ht1 ht.2
      refine iSup_le fun j => ENNReal.ofReal_le_ofReal ?_
      have hj : ∫ x, (ψ t.1 t.2 j x - ψ θ₀ η₀ j x) ^ 2 ∂P < ε ^ 2 :=
        lt_of_le_of_lt (Finset.single_le_sum
          (f := fun j' => ∫ x, (ψ t.1 t.2 j' x - ψ θ₀ η₀ j' x) ^ 2 ∂P)
          (fun j' _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ j)) hsum
      by_contra hcon
      rw [not_le] at hcon
      have hge := distL2_ge_imp_integral_ge (hψ_meas t.1 t.2 j).aestronglyMeasurable
        (hψ_meas θ₀ η₀ j).aestronglyMeasurable hε hcon.le
      linarith
    exact sup_distL2_tendsto_zero_of_unif_L2_cont_metric P
      (fun (t : EuclideanSpace ℝ (Fin k) × H) (j : Fin k) => ψ t.1 t.2 j) (θ₀, η₀)
      hunif μ (fun n Xs => (θ_hat n Xs, eta_hat n Xs)) X h_pair_consist
  -- The guard: both estimates inside the Donsker-class balls.
  have h_bad_good : Tendsto (fun n => μ {ξ |
      ¬ (‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls
        ∧ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀ < δcls)}) atTop (𝓝 0) := by
    have hsum : Tendsto (fun n =>
        μ {ξ | δcls / 2 < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}
        + μ {ξ | δcls / 2 < dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀})
        atTop (𝓝 0) := by
      simpa using (h_consist_θ (δcls / 2) (half_pos hδcls)).add
        (h_consist_η (δcls / 2) (half_pos hδcls))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    intro ξ hξ
    simp only [Set.mem_setOf_eq, not_and_or, not_lt] at hξ
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases hξ with h1 | h2
    · exact Or.inl (by linarith [half_lt_self hδcls])
    · exact Or.inr (by linarith [half_lt_self hδcls])
  have hθ₀_mem : ∀ j : Fin k,
      ψ θ₀ η₀ j ∈ pairClass ψ (Metric.ball θ₀ δcls ×ˢ Metric.ball η₀ δcls) :=
    fun j => ⟨(θ₀, η₀), ⟨Metric.mem_ball_self hδcls, Metric.mem_ball_self hδcls⟩, j, rfl⟩
  have h_tail := guardedRandomFunction_tail P
    (fun n ξ => ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls
      ∧ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀ < δcls)
    (fun n ξ (j : Fin k) => ψ (θ_hat n (fun i : Fin n => X i.val ξ))
      (eta_hat n (fun i : Fin n => X i.val ξ)) j)
    (ψ θ₀ η₀) μ h_sup h_bad_good
  have h_mem := guardedRandomFunction_mem
    (fun n ξ => ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls
      ∧ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀ < δcls)
    (fun n ξ (j : Fin k) => ψ (θ_hat n (fun i : Fin n => X i.val ξ))
      (eta_hat n (fun i : Fin n => X i.val ξ)) j)
    (ψ θ₀ η₀) (pairClass ψ (Metric.ball θ₀ δcls ×ˢ Metric.ball η₀ δcls))
    (fun n ξ hg j => ⟨(θ_hat n (fun i : Fin n => X i.val ξ),
      eta_hat n (fun i : Fin n => X i.val ξ)),
      ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hg.1,
       Metric.mem_ball.2 hg.2⟩, j, rfl⟩)
    hθ₀_mem
  have Rmod_oP := uniform_donsker_random_function_consistency
    (pairClass ψ (Metric.ball θ₀ δcls ×ˢ Metric.ball η₀ δcls)) P
    hDonsker.asymptoticallyEquicontinuous μ X hX_meas hX_indep hX_id hX_law
    (guardedRandomFunction
      (fun n ξ => ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls
        ∧ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀ < δcls)
      (fun n ξ (j : Fin k) => ψ (θ_hat n (fun i : Fin n => X i.val ξ))
        (eta_hat n (fun i : Fin n => X i.val ξ)) j)
      (ψ θ₀ η₀))
    h_mem (ψ θ₀ η₀) hθ₀_mem h_tail
  have Rhat_oP : TendstoZeroInOuterProbSup μ (fun n ξ (j : Fin k) =>
      empiricalProcess P n (fun i : Fin n => X i.val ξ)
          (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
            (eta_hat n (fun i : Fin n => X i.val ξ)) j)
        - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)) := by
    refine tendstoZeroInOuterProbSup_of_eq_off_vanishing Rmod_oP h_bad_good ?_
    intro n ξ hb j
    have hg : ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ < δcls
        ∧ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀ < δcls := by
      simpa only [Set.mem_setOf_eq, not_not] using hb
    rw [guardedRandomFunction_eq_on_good _ _ _ n ξ j hg]
  -- Combine the Fréchet remainder with the weighted rate bootstrap.
  have hS := frechet_remainder_pair_sup_bound P ψ θ₀ η₀ V hfrechet_unif μ θ_hat eta_hat X
    h_consist_θ h_consist_η
  have hbad : Tendsto (fun n => μ.outerMeasureStar
      {ξ | δV ≤ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (h_consist_η (δV / 2) (half_pos hδV_pos))
      (Eventually.of_forall fun n => zero_le) (Eventually.of_forall fun n => ?_)
    refine le_trans (outerMeasureStar_le_measure μ _) (measure_mono ?_)
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    linarith [half_lt_self hδV_pos]
  -- Lower bound on `Vfam` off the guard event.
  have hlb : ∀ (n : ℕ) (ξ : Ξ),
      ξ ∉ {ξ | δV ≤ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀} →
      ENNReal.ofReal (c * (Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖))
        ≤ ⨆ (j : Fin k), ENNReal.ofReal |Real.sqrt n *
            Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
              (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j| := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq, not_le] at hξ
    have hkey := hV_bd (eta_hat n (fun i : Fin n => X i.val ξ)) hξ
      (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    have hnorm : ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)‖
        = Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hnorm] at hkey
    have hVs : ∀ j : Fin k, Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
        (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) j
        = Real.sqrt n * Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
            (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j := by
      intro j; rw [map_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [hVs] at hkey
    exact hkey
  -- Master-identity decomposition `Vfam = Afam − Sfam` in the `ℝ≥0∞` sup form.
  have hW : ∀ (n : ℕ) (ξ : Ξ),
      (⨆ (j : Fin k), ENNReal.ofReal |Real.sqrt n *
          Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
            (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j|)
        ≤ (⨆ (j : Fin k), ENNReal.ofReal
            |-empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
              + Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                  (eta_hat n (fun i : Fin n => X i.val ξ)) j) n (fun i : Fin n => X i.val ξ)
              + -(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                    (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                      (eta_hat n (fun i : Fin n => X i.val ξ)) j)
                  - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j))
              + -(Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P))|)
          + (⨆ (j : Fin k), ENNReal.ofReal
            |Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
              - Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
              - Real.sqrt n * Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
                  (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j|) := by
    intro n ξ
    refine iSup_le fun j => ?_
    have hmi := pair_master_identity P ψ θ₀ η₀ V n (fun i : Fin n => X i.val ξ)
      (θ_hat n (fun i : Fin n => X i.val ξ)) (eta_hat n (fun i : Fin n => X i.val ξ)) j
    have hVAS : Real.sqrt n * Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
          (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
        = (-empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
            + Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                (eta_hat n (fun i : Fin n => X i.val ξ)) j) n (fun i : Fin n => X i.val ξ)
            + -(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                    (eta_hat n (fun i : Fin n => X i.val ξ)) j)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j))
            + -(Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)))
          - (Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
              - Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
              - Real.sqrt n * Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
                  (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j) := by
      linarith [hmi]
    rw [hVAS]
    refine le_trans (ENNReal.ofReal_le_ofReal (abs_sub _ _)) ?_
    rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact add_le_add (le_iSup (α := ℝ≥0∞) _ j) (le_iSup (α := ℝ≥0∞) _ j)
  -- `Afam = O_P(wDrift)`: `O_P(1)` bulk plus the weight-dominated drift.
  have h_tight := pair_h_tight P ψ θ₀ η₀ μ X hX_meas hX_indep hX_id hX_law
    (fun j => hψ_meas θ₀ η₀ j) hψ_L2 hPθ₀_zero
  have hdom : ∀ (n : ℕ) (ξ : Ξ) (j : Fin k),
      |-(Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P))|
        ≤ 1 + Real.sqrt n *
          ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ := by
    intro n ξ j
    rw [abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : |∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P|
        ≤ ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ := by
      have h2 := hcoord_le (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j
      rwa [hdrift_coord] at h2
    have h3 := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg (n : ℝ))
    linarith
  have hA := isBoundedInOuterProbSupWt_add_wt_dominated hw
    (OP_add_oP_sup (OP_add_oP_sup h_tight.neg h_est_eq) Rhat_oP.neg) hdom
  -- Apply the weighted rate bootstrap.
  obtain ⟨hrate, Sfam_oPWt⟩ := rate_bootstrap_oP_wt μ
    (fun (n : ℕ) (ξ : Ξ) (j : Fin k) => Real.sqrt n *
      Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
        (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j)
    (fun (n : ℕ) (ξ : Ξ) (j : Fin k) =>
      -empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
        + Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
            (eta_hat n (fun i : Fin n => X i.val ξ)) j) n (fun i : Fin n => X i.val ξ)
        + -(empiricalProcess P n (fun i : Fin n => X i.val ξ)
              (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                (eta_hat n (fun i : Fin n => X i.val ξ)) j)
            - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j))
        + -(Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)))
    (fun (n : ℕ) (ξ : Ξ) (j : Fin k) =>
      Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ))
          (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
        - Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
        - Real.sqrt n * Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
            (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j)
    (fun (n : ℕ) (ξ : Ξ) => Real.sqrt n * ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖)
    (fun (n : ℕ) (ξ : Ξ) => 1 + Real.sqrt n *
      ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)
    (fun n ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hw
    (fun n => {ξ | δV ≤ dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) hbad
    c hc_pos hlb hW hA hS
  -- =================== STEP 1c: assemble (V-swap enters here). ===================
  have hgoal_eq : (fun (n : ℕ) (ξ : Ξ) (j : Fin k) =>
        Real.sqrt n * Vlin (V η₀) (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
          + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
          + Real.sqrt n *
              (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j)
      = (fun (n : ℕ) (ξ : Ξ) (j : Fin k) =>
          (Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                (eta_hat n (fun i : Fin n => X i.val ξ)) j) n (fun i : Fin n => X i.val ξ)
            + -(empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                    (eta_hat n (fun i : Fin n => X i.val ξ)) j)
                - empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j))
            + -(Real.sqrt n * (∫ x, ψ (θ_hat n (fun i : Fin n => X i.val ξ))
                    (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
                - Real.sqrt n * (∫ x, ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)) j x ∂P)
                - Real.sqrt n * Vlin (V (eta_hat n (fun i : Fin n => X i.val ξ)))
                    (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j))
          + Real.sqrt n * Vlin (V η₀ - V (eta_hat n (fun i : Fin n => X i.val ξ)))
              (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j) := by
    funext n ξ j
    have hmi := pair_master_identity P ψ θ₀ η₀ V n (fun i : Fin n => X i.val ξ)
      (θ_hat n (fun i : Fin n => X i.val ξ)) (eta_hat n (fun i : Fin n => X i.val ξ)) j
    rw [hlin (V η₀) (V (eta_hat n (fun i : Fin n => X i.val ξ)))
      (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j, hdrift_coord]
    linear_combination hmi
  rw [hgoal_eq]
  exact oP_supWt_add hw (oP_supWt_add hw (oP_supWt_add hw
      (tendstoZeroInOuterProbSupWt_of_tendstoZeroInOuterProbSup hw h_est_eq)
      (tendstoZeroInOuterProbSupWt_of_tendstoZeroInOuterProbSup hw Rhat_oP.neg))
      Sfam_oPWt.neg)
    (vSwap_oPWt P ψ θ₀ η₀ V hV_cont μ θ_hat eta_hat X h_consist_η hrate)

/-! ### Weighted finite-`H` collapse to Euclidean `→ₚ 0` -/

/-- **Weighted finite-`H` collapse.** For finite index `Fin k`, weighted
`o_P(w)` in the sup (`TendstoZeroInOuterProbSupWt`) upgrades to `→ₚ 0` of the
`w⁻¹`-scaled `EuclideanSpace`-bundled family. As in
`tendstoInProbZero_of_tendstoZeroInOuterProbSup_fin`, `ε ≤ ‖w⁻¹•v‖ ↔ ε·w ≤ ‖v‖`
(since `w ≥ 1 > 0`) and the Euclidean norm is controlled by `√k·maxⱼ|·|`, so the
`ε`-exceedance is dominated by the `∃j` weighted event, whose outer measure
vanishes. This bridges the weighted supremum to vector-valued
`TendstoInProbZero`.

No measurability hypotheses are needed: the squeeze runs
`μ E ≤ μ* E ≤ μ* (∃j-event) → 0` through `measure_le_outerMeasureStar`, which
holds for arbitrary sets, so neither `w` nor `g` needs to be measurable. -/
theorem tendstoInProbZero_of_tendstoZeroInOuterProbSupWt_fin
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) {k : ℕ}
    (w : ℕ → Ξ → ℝ) (hw : ∀ n ξ, 1 ≤ w n ξ)
    (g : ℕ → Ξ → Fin k → ℝ)
    (h : TendstoZeroInOuterProbSupWt μ w g) :
    TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => (w n ξ)⁻¹ • ((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
        EuclideanSpace ℝ (Fin k))) := by
  intro ε hε
  set sk : ℝ := Real.sqrt k with hsk_def
  have hsk_nonneg : 0 ≤ sk := Real.sqrt_nonneg _
  have hsk_sq : sk ^ 2 = (k : ℝ) := Real.sq_sqrt (Nat.cast_nonneg k)
  have hsk1_pos : 0 < sk + 1 := by linarith
  set ε' : ℝ := ε / (sk + 1) with hε'_def
  have hε'_pos : 0 < ε' := div_pos hε hsk1_pos
  have hε'eq : ε' * (sk + 1) = ε := by
    rw [hε'_def, div_mul_cancel₀ _ (ne_of_gt hsk1_pos)]
  -- The `ε`-exceedance of the `w⁻¹`-scaled Euclidean norm forces a weighted coordinate
  -- above `ε' · w`.
  have hTS : ∀ n,
      {ξ | ε ≤ ‖(w n ξ)⁻¹ • ((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
          EuclideanSpace ℝ (Fin k))‖}
        ⊆ {ξ | ∃ j, ε' * w n ξ < |g n ξ j|} := by
    intro n ξ hξ
    simp only [Set.mem_setOf_eq] at hξ ⊢
    have hw1 : (1 : ℝ) ≤ w n ξ := hw n ξ
    have hwpos : (0 : ℝ) < w n ξ := lt_of_lt_of_le one_pos hw1
    -- Unscale: `ε ≤ w⁻¹‖v‖` becomes `ε · w ≤ ‖v‖`.
    have hunscaled : ε * w n ξ ≤ ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
        EuclideanSpace ℝ (Fin k))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwpos)] at hξ
      have hmul := mul_le_mul_of_nonneg_right hξ hwpos.le
      have hid : (w n ξ)⁻¹ * ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
          EuclideanSpace ℝ (Fin k))‖ * w n ξ
          = ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
            EuclideanSpace ℝ (Fin k))‖ := by
        field_simp
      rwa [hid] at hmul
    by_contra hcon
    push_neg at hcon
    have hnorm_sq :
        ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) : EuclideanSpace ℝ (Fin k))‖ ^ 2
          = ∑ i, |g n ξ i| ^ 2 := by
      rw [EuclideanSpace.norm_eq,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change ‖g n ξ i‖ ^ 2 = |g n ξ i| ^ 2
      rw [Real.norm_eq_abs]
    have hsum_le : ∑ i, |g n ξ i| ^ 2 ≤ (k : ℝ) * (ε' * w n ξ) ^ 2 := by
      calc ∑ i, |g n ξ i| ^ 2 ≤ ∑ _i : Fin k, (ε' * w n ξ) ^ 2 :=
            Finset.sum_le_sum (fun i _ => by
              nlinarith [hcon i, abs_nonneg (g n ξ i), hε'_pos.le, hwpos.le])
        _ = (k : ℝ) * (ε' * w n ξ) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hεsq : (ε * w n ξ) ^ 2 ≤ (k : ℝ) * (ε' * w n ξ) ^ 2 := by
      have h1 : (ε * w n ξ) ^ 2 ≤ ‖((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
          EuclideanSpace ℝ (Fin k))‖ ^ 2 := by
        nlinarith [norm_nonneg ((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) :
          EuclideanSpace ℝ (Fin k)), mul_pos hε hwpos]
      rw [hnorm_sq] at h1
      exact le_trans h1 hsum_le
    -- `(ε w)² = (ε'(sk+1)w)² > sk²(ε'w)² = k(ε'w)²`, contradiction.
    have hXpos : (0 : ℝ) < (ε' * w n ξ) ^ 2 := pow_pos (mul_pos hε'_pos hwpos) 2
    have hεsq' : (sk + 1) ^ 2 * (ε' * w n ξ) ^ 2 ≤ sk ^ 2 * (ε' * w n ξ) ^ 2 := by
      rw [hsk_sq]
      calc (sk + 1) ^ 2 * (ε' * w n ξ) ^ 2 = (ε * w n ξ) ^ 2 := by rw [← hε'eq]; ring
        _ ≤ (k : ℝ) * (ε' * w n ξ) ^ 2 := hεsq
    have hle : (sk + 1) ^ 2 ≤ sk ^ 2 := le_of_mul_le_mul_right hεsq' hXpos
    nlinarith [hsk_nonneg, hle]
  -- The `ε`-events are dominated by the weighted outer-measure events, which vanish.
  have hμ_tendsto : Tendsto (fun n => μ {ξ | ε ≤ ‖(w n ξ)⁻¹ •
      ((WithLp.equiv 2 (Fin k → ℝ)).symm (g n ξ) : EuclideanSpace ℝ (Fin k))‖})
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h ε' hε'_pos)
      (Eventually.of_forall fun n => zero_le)
      (Eventually.of_forall fun n =>
        (measure_le_outerMeasureStar μ _).trans (outerMeasureStar_mono μ (hTS n)))
  simp only [measureReal_def]
  have hcomp := (ENNReal.tendsto_toReal (by simp)).comp hμ_tendsto
  rwa [ENNReal.toReal_zero] at hcomp

/-! ### Nuisance linear representation (vdV Theorem 5.31) -/

/-- **Asymptotic linear representation of the Z-estimator with an
estimated nuisance** (vdV Theorem 5.31, §*5.4 book p.60). Carries van der Vaart's
stated hypotheses: the pair class is Donsker
(`hDonsker`), `L²`-continuity at the truth (`hL2_cont`), `Pψ_{θ₀,η₀} = 0`
(`hPθ₀_zero`), `η`-uniform Fréchet differentiability with derivative `V`
(`hfrechet_unif`, `hV`, `hV_cont`), the `o_P(n^{-1/2})` estimating equation
(`h_est_eq`) and pair consistency (`h_consist_θ`, `h_consist_η`). Concludes the
book's **linear representation with drift**, encoded as the scaled
`TendstoInProbZero`:

    wDrift⁻¹ • ( √n•(θ̂ₙ−θ₀) + V⁻¹_{η₀}(√n•driftVec) + V⁻¹_{η₀}(𝔾ₙψ_{θ₀,η₀}) ) →ₚ 0.

`nuisance_weighted_core` gives the weighted supremum `o_P`; the finite-index lemma collapses
to Euclidean `→ₚ 0`; `tendstoInProbZero_clm` with `(V η₀)⁻¹` (the scalar `wDrift⁻¹•`
commutes with the CLM) and `nonsing_inv_mul` collapse the first term, as in
`zEstimator_linear_representation`. The book makes no asymptotic-normality claim here. -/
theorem zEstimator_nuisance_linear_representation
    {k : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {H : Type*} [MetricSpace H]
    (ψ : EuclideanSpace ℝ (Fin k) → H → Fin k → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (η₀ : H)
    (V : H → Matrix (Fin k) (Fin k) ℝ)
    (hV : IsUnit (V η₀).det) (hV_cont : ContinuousAt V η₀)
    (δcls : ℝ) (hδcls : 0 < δcls)
    (hDonsker : IsPDonsker (pairClass ψ (Metric.ball θ₀ δcls ×ˢ Metric.ball η₀ δcls)) P)
    (hL2_cont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : EuclideanSpace ℝ (Fin k)) (η : H),
        ‖θ - θ₀‖ < δ → dist η η₀ < δ →
        ∑ j, ∫ x, (ψ θ η j x - ψ θ₀ η₀ j x)^2 ∂P < ε)
    (hPθ₀_zero : ∀ h, ∫ x, ψ θ₀ η₀ h x ∂P = 0)
    (hfrechet_unif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (η : H), dist η η₀ < δ →
        ∀ θ : EuclideanSpace ℝ (Fin k), 0 < ‖θ - θ₀‖ → ‖θ - θ₀‖ < δ →
        (⨆ h, ENNReal.ofReal
            |∫ x, ψ θ η h x ∂P - ∫ x, ψ θ₀ η h x ∂P - Vlin (V η) (θ - θ₀) h|)
          ≤ ENNReal.ofReal (ε * ‖θ - θ₀‖))
    (hψ_meas : ∀ (θ : EuclideanSpace ℝ (Fin k)) (η : H) (j : Fin k), Measurable (ψ θ η j))
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin k))
    (eta_hat : ∀ n, (Fin n → Ω) → H)
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (h_consist_θ : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < ‖θ_hat n (fun i : Fin n => X i.val ξ) - θ₀‖}) atTop (𝓝 0))
    (h_consist_η : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      μ {ξ | ε < dist (eta_hat n (fun i : Fin n => X i.val ξ)) η₀}) atTop (𝓝 0))
    (h_est_eq : TendstoZeroInOuterProbSup μ (fun n ξ h =>
      Real.sqrt n * empiricalAvg (ψ (θ_hat n (fun i : Fin n => X i.val ξ))
        (eta_hat n (fun i : Fin n => X i.val ξ)) h) n (fun i : Fin n => X i.val ξ))) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (1 + Real.sqrt n * ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)⁻¹ •
        (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (V η₀)⁻¹
              (Real.sqrt n • driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)))
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (V η₀)⁻¹
              (empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
                (fun i : Fin n => X i.val ξ)))) := by
  classical
  -- Derive `L²` membership of the `η₀` slice from `hDonsker`.
  have hψ_L2 := pair_hpsi_L2 P ψ θ₀ η₀ δcls hδcls hDonsker
  -- Establish the weighted `ℓ∞(Fin k)` remainder bound.
  have hN8 := nuisance_weighted_core P ψ θ₀ η₀ V hV hV_cont δcls hδcls hDonsker
    hL2_cont hPθ₀_zero hfrechet_unif hψ_meas hψ_L2 θ_hat eta_hat μ X hX_meas
    hX_indep hX_id hX_law h_consist_θ h_consist_η h_est_eq
  -- The drift weight is `≥ 1`.
  have hw : ∀ (n : ℕ) (ξ : Ξ), (1 : ℝ) ≤ 1 + Real.sqrt n *
      ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ := by
    intro n ξ
    have h0 : (0 : ℝ) ≤ Real.sqrt n *
        ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    linarith
  -- Collapse the finite weighted supremum to Euclidean `→ₚ 0`.
  have h_N9 := tendstoInProbZero_of_tendstoZeroInOuterProbSupWt_fin μ
    (fun n ξ => 1 + Real.sqrt n *
      ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖) hw _ hN8
  -- Apply the (Lipschitz) inverse-derivative endomorphism `toEuclideanCLM (V η₀)⁻¹`.
  have h_clm := tendstoInProbZero_clm μ
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)⁻¹) h_N9
  -- `(V η₀)⁻¹ ∘ (V η₀) = id` on `EuclideanSpace ℝ (Fin k)`.
  have hVV : ∀ w : EuclideanSpace ℝ (Fin k),
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)⁻¹
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀) w) = w := by
    intro w
    have hInv : Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)⁻¹
          * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀) = 1 := by
      rw [← map_mul, Matrix.nonsing_inv_mul (V η₀) hV, map_one]
    calc Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)⁻¹
            (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀) w)
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)⁻¹
            * Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)) w := by
          rw [ContinuousLinearMap.mul_apply]
      _ = w := by rw [hInv, ContinuousLinearMap.one_apply]
  -- Pointwise identification of the collapsed vector with the target.
  have hpt : ∀ (n : ℕ) (ξ : Ξ),
      (1 + Real.sqrt n * ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)⁻¹ •
        (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (V η₀)⁻¹
              (Real.sqrt n • driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)))
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (V η₀)⁻¹
              (empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
                (fun i : Fin n => X i.val ξ)))
      = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)⁻¹
          ((1 + Real.sqrt n *
              ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)⁻¹ •
            ((WithLp.equiv 2 (Fin k → ℝ)).symm
              (fun j => Real.sqrt n *
                  Vlin (V η₀) (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
                + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
                + Real.sqrt n *
                    (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j) :
              EuclideanSpace ℝ (Fin k))) := by
    intro n ξ
    have hsymm : ((WithLp.equiv 2 (Fin k → ℝ)).symm
          (fun j => Real.sqrt n *
              Vlin (V η₀) (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
            + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
            + Real.sqrt n *
                (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j) :
            EuclideanSpace ℝ (Fin k))
        = Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)
            (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
          + Real.sqrt n • driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))
          + empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
              (fun i : Fin n => X i.val ξ) := by
      apply (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).injective
      rw [map_add, map_add]
      funext j
      rw [Pi.add_apply, Pi.add_apply]
      change Real.sqrt n * Vlin (V η₀) (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
            + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
            + Real.sqrt n *
                (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j
        = Vlin (V η₀) (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)) j
            + Real.sqrt n *
                (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j
            + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsymm]
    simp only [map_smul, map_add, hVV]
  have hfun : (fun (n : ℕ) (ξ : Ξ) =>
        (1 + Real.sqrt n *
            ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)⁻¹ •
          (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
            + Matrix.toEuclideanCLM (𝕜 := ℝ) (V η₀)⁻¹
                (Real.sqrt n • driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ)))
            + Matrix.toEuclideanCLM (𝕜 := ℝ) (V η₀)⁻¹
                (empiricalProcessVec P (fun θ h => ψ θ η₀ h) θ₀ n
                  (fun i : Fin n => X i.val ξ))))
      = (fun (n : ℕ) (ξ : Ξ) => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) (V η₀)⁻¹
          ((1 + Real.sqrt n *
              ‖driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))‖)⁻¹ •
            ((WithLp.equiv 2 (Fin k → ℝ)).symm
              (fun j => Real.sqrt n *
                  Vlin (V η₀) (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀) j
                + empiricalProcess P n (fun i : Fin n => X i.val ξ) (ψ θ₀ η₀ j)
                + Real.sqrt n *
                    (driftVec P ψ θ₀ (eta_hat n (fun i : Fin n => X i.val ξ))) j) :
              EuclideanSpace ℝ (Fin k)))) :=
    funext fun n => funext fun ξ => hpt n ξ
  rw [hfun]
  exact h_clm

end AsymptoticStatistics.EmpiricalProcess
