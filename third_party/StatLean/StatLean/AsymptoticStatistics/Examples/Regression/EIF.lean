module
public import StatLean.AsymptoticStatistics.Examples.Regression.Model

@[expose] public section

/-!
# Efficient influence function for the regression model (vdV Example 25.28)

The EIF half of the concrete-EIF verification for the regression model
`Y = g_θ(X) + e`, `E(e | X) = 0` of van der Vaart, *Asymptotic Statistics*,
Example 25.28 (§25.4, p.370-371).

The book's efficient influence function is `Ĩ⁻¹ · ℓ̃_{θ,η}`, the efficient score
normalized by the efficient information, with

    ℓ̃_{θ,η}(X, Y) = (Y − g_θ(X))·ġ_θ(X) / E(e² | X),   Ĩ = E(ġ²/E(e²|X)).

This file derives `ℓ̃ = ℓ̇ − Π_nuis ℓ̇` and applies
`StrictModel.EfficientScore.eif_from_efficientScore'`, the projection form of
vdV Lemma 25.25. Its hypotheses are:

* `lscore : ↥(L²₀(P))` — the ordinary θ-score `ℓ̇ = −(η₂/η)·ġ` (QMD score of the
  θ-submodel), exactly as in vdV §25.4;
* `T_nuis` with the characterization `hchar` that it is the **orthocomplement
  of the error-shape space `ēH = {e·h(X)}`** — vdV's definition of the nuisance
  tangent (Example 25.28), phrased as raw `L²(P)`-orthogonality;
* the model's **moment / smoothness conditions**, isolated as named integral
  identities (vdV: "qualitative smoothness conditions that ensure existence of
  score functions, and the existence of moments"):
  - `hEmean` : `E(e | X) = 0` (the defining regression relation),
  - `hSigma` : `σ² = E(e² | X)` (definition of the conditional error variance),
  - `hIBP`   : `E(e·ℓ̇ | X) = ġ`, the **integration-by-parts identity**
    `∫ η₂(x,e)·e de = −∫ η(x,e) de` used in Example 25.28;
* the θ-functional `ψ` with its pathwise differentiability (`hpd`) and the
  θ-coordinate identity (`h_deriv_eq`) — vdV eq (25.26), Lemma 25.25.

From these, `regression_efficientScore_eq` computes `ℓ̃ = ℓ̇ − Π_nuis ℓ̇ = e·ġ/σ²`
(the projection algebra of Example 25.28), and `regression_isEIF` concludes the
EIF via `eif_from_efficientScore'`. The conditions `hchar`, `hEmean`, `hSigma`,
and `hIBP` are stated in terms of the ordinary score and the model primitives;
the efficient-score projection is then obtained by the theorem.

Main declaration: `regression_isEIF`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.StrictModel.EfficientScore

namespace AsymptoticStatistics.Examples.Regression

variable {X : Type*} [MeasurableSpace X]
variable {P : Measure (RegObs X)} [IsProbabilityMeasure P]

/-- Inner product of two mean-zero `L²(P)` elements as an integral of the
pointwise product. (Real inner product reverses the order.) -/
private lemma l2zm_inner_eq_integral (v w : ↥(L2ZeroMean P)) :
    ⟪v, w⟫_ℝ
      = ∫ o, ((w : Lp ℝ 2 P) : RegObs X → ℝ) o
              * ((v : Lp ℝ 2 P) : RegObs X → ℝ) o ∂P := by
  change ⟪(v : Lp ℝ 2 P), (w : Lp ℝ 2 P)⟫_ℝ = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with o
  rfl

/-- The `L²(P)`-membership of the coercion of an `L²₀(P)` element. -/
private lemma memLp_coeFn (v : ↥(L2ZeroMean P)) :
    MemLp ((v : Lp ℝ 2 P) : RegObs X → ℝ) 2 P :=
  Lp.memLp (v : Lp ℝ 2 P)

/-- The **efficient-score candidate** `ℓ̃ = e·ġ/σ²` bundled into `L²₀(P)`.

Square-integrability (`hLp2`) is a moment condition of Example 25.28; mean-zero
is *derived* from `E(e | X) = 0` (`hEmean`): `∫ e·(ġ/σ²) dP = 0`. -/
noncomputable def regression_scoreCandidate (g gdot sigma2 : X → ℝ)
    (hLp2 : MemLp (regression_efficientScore g gdot sigma2) 2 P)
    (hEmean : ∀ (k : X → ℝ),
        Integrable (fun o => regression_error g o * k o.x) P →
        ∫ o, regression_error g o * k o.x ∂P = 0) :
    CandidateIF P where
  raw := regression_efficientScore g gdot sigma2
  memLp2 := hLp2
  mean_zero := by
    have h_eq : (fun o => regression_efficientScore g gdot sigma2 o)
        = fun o => regression_error g o * (fun x => gdot x / sigma2 x) o.x := by
      funext o; exact regression_efficientScore_eq_errorShape g gdot sigma2 o
    rw [h_eq]
    exact hEmean (fun x => gdot x / sigma2 x)
      (by rw [← h_eq]; exact hLp2.integrable (by norm_num))

variable {g gdot sigma2 : X → ℝ}
variable {lscore : ↥(L2ZeroMean P)}
variable {T_nuis : Submodule ℝ ↥(L2ZeroMean P)}

/-- The efficient-score candidate is orthogonal to the nuisance tangent space
`T_nuis` (which, by `hchar`, is the orthocomplement of the error-shape space):
`ℓ̃ = e·ġ/σ²` is itself an error-shape function (`h = ġ/σ²`), hence lies in
`ēH ⊆ (ēH)ᗮᗮ = T_nuisᗮ`. -/
theorem regression_candidate_mem_orthogonal
    (hLp2 : MemLp (regression_efficientScore g gdot sigma2) 2 P)
    (hEmean : ∀ (k : X → ℝ),
        Integrable (fun o => regression_error g o * k o.x) P →
        ∫ o, regression_error g o * k o.x ∂P = 0)
    (hchar : ∀ (w : ↥(L2ZeroMean P)), w ∈ T_nuis ↔
        ∀ (h : X → ℝ), MemLp (regression_errorShape g h) 2 P →
          ∫ o, ((w : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P = 0) :
    (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean ∈ T_nuisᗮ := by
  set φ₀ := (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean with hφ₀
  -- `ℓ̃ = e·(ġ/σ²)` is an error shape.
  have hφ₀_ae : ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ)
      =ᵐ[P] regression_errorShape g (fun x => gdot x / sigma2 x) := by
    refine (CandidateIF.coeFn_toL2ZeroMean _).trans ?_
    filter_upwards with o
    exact regression_efficientScore_eq_errorShape g gdot sigma2 o
  have h_es_memLp : MemLp (regression_errorShape g (fun x => gdot x / sigma2 x)) 2 P :=
    hLp2.ae_eq (Filter.Eventually.of_forall
      (fun o => regression_efficientScore_eq_errorShape g gdot sigma2 o))
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [l2zm_inner_eq_integral w φ₀]
  -- `∫ φ₀ · w = ∫ w · (e·ġ/σ²) = 0` by `hchar`.
  rw [show (∫ o, ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ) o
              * ((w : Lp ℝ 2 P) : RegObs X → ℝ) o ∂P)
        = ∫ o, ((w : Lp ℝ 2 P) : RegObs X → ℝ) o
              * regression_errorShape g (fun x => gdot x / sigma2 x) o ∂P from by
      apply integral_congr_ae
      filter_upwards [hφ₀_ae] with o ho
      rw [ho]; ring]
  exact (hchar w).mp hw (fun x => gdot x / sigma2 x) h_es_memLp

/-- The residual `ℓ̇ − ℓ̃` of the ordinary score after subtracting the
efficient-score candidate lies in the nuisance tangent space `T_nuis`.

This is where the **integration-by-parts** content enters: for every error
shape `e·h(X)`,
`⟪ℓ̇ − ℓ̃, e·h⟫ = E(e·ℓ̇·h) − E(e²·(ġ/σ²)·h) = E(ġ·h) − E(σ²·(ġ/σ²)·h) = 0`,
using `hIBP` (`E(e·ℓ̇|X) = ġ`) and `hSigma` (`σ² = E(e²|X)`). -/
theorem regression_score_sub_candidate_mem
    (hLp2 : MemLp (regression_efficientScore g gdot sigma2) 2 P)
    (hEmean : ∀ (k : X → ℝ),
        Integrable (fun o => regression_error g o * k o.x) P →
        ∫ o, regression_error g o * k o.x ∂P = 0)
    (hsigma_pos : ∀ o : RegObs X, 0 < sigma2 o.x)
    (hchar : ∀ (w : ↥(L2ZeroMean P)), w ∈ T_nuis ↔
        ∀ (h : X → ℝ), MemLp (regression_errorShape g h) 2 P →
          ∫ o, ((w : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P = 0)
    (hSigma : ∀ (k : X → ℝ),
        Integrable (fun o => (regression_error g o) ^ 2 * k o.x) P →
        ∫ o, (regression_error g o) ^ 2 * k o.x ∂P = ∫ o, sigma2 o.x * k o.x ∂P)
    (hIBP : ∀ (h : X → ℝ), MemLp (regression_errorShape g h) 2 P →
        ∫ o, ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_error g o * h o.x ∂P
          = ∫ o, gdot o.x * h o.x ∂P) :
    lscore - (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean ∈ T_nuis := by
  set φ₀ := (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean with hφ₀
  rw [hchar]
  intro h h_memLp
  -- coeFn a.e. identities
  have hφ₀_ae : ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ)
      =ᵐ[P] regression_efficientScore g gdot sigma2 :=
    CandidateIF.coeFn_toL2ZeroMean _
  have hsub_ae : (((lscore - φ₀ : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : RegObs X → ℝ)
      =ᵐ[P] fun o => ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o
              - ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ) o := by
    have h1 : ((lscore - φ₀ : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        = (lscore : Lp ℝ 2 P) - (φ₀ : Lp ℝ 2 P) := by
      rfl
    rw [h1]; exact Lp.coeFn_sub _ _
  -- `MemLp` witnesses.
  have h_lscore_L2 : MemLp ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) 2 P := memLp_coeFn lscore
  have h_φ₀_L2 : MemLp ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ) 2 P := memLp_coeFn φ₀
  have h_es_L2 : MemLp (regression_errorShape g h) 2 P := h_memLp
  -- Integrability of the two products.
  have hInt_lscore : Integrable
      (fun o => ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o) P :=
    h_lscore_L2.integrable_mul h_es_L2
  have hInt_φ₀ : Integrable
      (fun o => ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o) P :=
    h_φ₀_L2.integrable_mul h_es_L2
  -- `∫ ℓ̇·(e·h) = ∫ ġ·h` (IBP).
  have hL : ∫ o, ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P
      = ∫ o, gdot o.x * h o.x ∂P := by
    rw [show (∫ o, ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P)
          = ∫ o, ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_error g o * h o.x ∂P from by
        apply integral_congr_ae; filter_upwards with o
        simp only [regression_errorShape]; ring]
    exact hIBP h h_memLp
  -- `∫ ℓ̃·(e·h) = ∫ ġ·h` (σ² definition + division cancels).
  have hR : ∫ o, ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P
      = ∫ o, gdot o.x * h o.x ∂P := by
    set k : X → ℝ := fun x => gdot x * h x / sigma2 x with hk
    have hInt_e2k : Integrable (fun o => (regression_error g o) ^ 2 * k o.x) P := by
      refine hInt_φ₀.congr ?_
      filter_upwards [hφ₀_ae] with o ho
      rw [ho]
      simp only [regression_efficientScore, regression_errorShape, regression_error, hk]
      have hσ := (hsigma_pos o).ne'
      field_simp
    have h1 : ∫ o, ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P
        = ∫ o, (regression_error g o) ^ 2 * k o.x ∂P := by
      apply integral_congr_ae
      filter_upwards [hφ₀_ae] with o ho
      rw [ho]
      simp only [regression_efficientScore, regression_errorShape, regression_error, hk]
      have hσ := (hsigma_pos o).ne'
      field_simp
    have h2 : ∫ o, sigma2 o.x * k o.x ∂P = ∫ o, gdot o.x * h o.x ∂P := by
      apply integral_congr_ae
      filter_upwards with o
      simp only [hk]
      have hσ := (hsigma_pos o).ne'
      field_simp
    rw [h1, hSigma k hInt_e2k, h2]
  -- Assemble: `∫ (ℓ̇ − ℓ̃)·(e·h) = ∫ ℓ̇·(e·h) − ∫ ℓ̃·(e·h) = 0`.
  rw [show (∫ o, (((lscore - φ₀ : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : RegObs X → ℝ) o
            * regression_errorShape g h o ∂P)
        = (∫ o, ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P)
          - (∫ o, ((φ₀ : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P) from by
      rw [← integral_sub hInt_lscore hInt_φ₀]
      apply integral_congr_ae
      filter_upwards [hsub_ae] with o ho
      rw [ho]; ring]
  rw [hL, hR, sub_self]

/-- **The efficient score equals `e·ġ/σ²`** (the projection algebra of vdV
Example 25.28). From `regression_candidate_mem_orthogonal` and
`regression_score_sub_candidate_mem`, the orthogonal projection of the ordinary
score onto `T_nuis` is `ℓ̇ − ℓ̃`, so
`efficientScore = ℓ̇ − Π_nuis ℓ̇ = ℓ̃ = e·ġ/σ²`. -/
theorem regression_efficientScore_eq
    [T_nuis.HasOrthogonalProjection]
    (hLp2 : MemLp (regression_efficientScore g gdot sigma2) 2 P)
    (hEmean : ∀ (k : X → ℝ),
        Integrable (fun o => regression_error g o * k o.x) P →
        ∫ o, regression_error g o * k o.x ∂P = 0)
    (hsigma_pos : ∀ o : RegObs X, 0 < sigma2 o.x)
    (hchar : ∀ (w : ↥(L2ZeroMean P)), w ∈ T_nuis ↔
        ∀ (h : X → ℝ), MemLp (regression_errorShape g h) 2 P →
          ∫ o, ((w : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P = 0)
    (hSigma : ∀ (k : X → ℝ),
        Integrable (fun o => (regression_error g o) ^ 2 * k o.x) P →
        ∫ o, (regression_error g o) ^ 2 * k o.x ∂P = ∫ o, sigma2 o.x * k o.x ∂P)
    (hIBP : ∀ (h : X → ℝ), MemLp (regression_errorShape g h) 2 P →
        ∫ o, ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_error g o * h o.x ∂P
          = ∫ o, gdot o.x * h o.x ∂P) :
    efficientScore (regression_ordinaryScore lscore) T_nuis 1
      = (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean := by
  set φ₀ := (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean with hφ₀
  have h_perp := regression_candidate_mem_orthogonal (T_nuis := T_nuis) hLp2 hEmean hchar
  have h_res := regression_score_sub_candidate_mem (T_nuis := T_nuis) hLp2 hEmean
    hsigma_pos hchar hSigma hIBP
  -- `proj_{T_nuis} lscore = lscore - φ₀`.
  have h_proj : T_nuis.starProjection lscore = lscore - φ₀ :=
    Submodule.eq_starProjection_of_mem_orthogonal' h_res h_perp (by rw [sub_add_cancel])
  rw [efficientScore, regression_ordinaryScore_one, h_proj, sub_sub_cancel]

/-- Every tangent direction of `Ṗ = lin(ℓ̇) ⊔ T_nuis` splits as `u • ℓ̇ + g_nuis`
with `g_nuis ∈ T_nuis` (vdV §25.4, p.368 tangent-set structure). -/
theorem regression_tangent_decomp (lscore : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P))
    (w : regression_tangent lscore T_nuis) :
    ∃ (u : ℝ) (g_nuis : ↥(L2ZeroMean P)),
      g_nuis ∈ T_nuis ∧
      (w : ↥(L2ZeroMean P)) = regression_ordinaryScore lscore u + g_nuis := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp w.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  exact ⟨c, b, hb, by rw [regression_ordinaryScore_apply, hc, hab]⟩

/-- **Efficient influence function for the regression model (vdV Example 25.28).**

The book's candidate `ℓ̃ = e·ġ/σ²`, normalized by the efficient information `Ĩ`,
is the efficient influence function of the regression θ-functional `ψ` over the
tangent space `Ṗ = lin(ℓ̇) ⊔ T_nuis`.

The theorem `regression_efficientScore_eq` identifies
`efficientScore = ℓ̇ − Π_nuis ℓ̇` with `e·ġ/σ²` by the integration-by-parts
projection of Example 25.28. Applying `eif_from_efficientScore'` (Lemma 25.25)
to `hpd.derivative` then yields the concrete efficient influence function. -/
theorem regression_isEIF
    [T_nuis.HasOrthogonalProjection]
    (hLp2 : MemLp (regression_efficientScore g gdot sigma2) 2 P)
    (hEmean : ∀ (k : X → ℝ),
        Integrable (fun o => regression_error g o * k o.x) P →
        ∫ o, regression_error g o * k o.x ∂P = 0)
    (hsigma_pos : ∀ o : RegObs X, 0 < sigma2 o.x)
    (hchar : ∀ (w : ↥(L2ZeroMean P)), w ∈ T_nuis ↔
        ∀ (h : X → ℝ), MemLp (regression_errorShape g h) 2 P →
          ∫ o, ((w : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_errorShape g h o ∂P = 0)
    (hSigma : ∀ (k : X → ℝ),
        Integrable (fun o => (regression_error g o) ^ 2 * k o.x) P →
        ∫ o, (regression_error g o) ^ 2 * k o.x ∂P = ∫ o, sigma2 o.x * k o.x ∂P)
    (hIBP : ∀ (h : X → ℝ), MemLp (regression_errorShape g h) 2 P →
        ∫ o, ((lscore : Lp ℝ 2 P) : RegObs X → ℝ) o * regression_error g o * h o.x ∂P
          = ∫ o, gdot o.x * h o.x ∂P)
    -- vdV p.371: nonsingular efficient information Ĩ = ‖ℓ̃‖² > 0
    (hEffScore_ne : (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean ≠ 0)
    -- vdV Ex 25.28 / Lem 25.25: the θ-functional ψ, its differentiability, θ-coordinate
    (ψ : Measure (RegObs X) → ℝ)
    (hpd : PathwiseDifferentiableAt P (regression_tangent lscore T_nuis) ψ)
    (h_deriv_eq : ∀ (u : ℝ) (g_nuis : ↥(L2ZeroMean P)) (_ : g_nuis ∈ T_nuis)
        (hmem : u • lscore + g_nuis ∈ regression_tangent lscore T_nuis),
        hpd.derivative ⟨u • lscore + g_nuis, hmem⟩ = u) :
    IsEfficientInfluenceFunction P (regression_tangent lscore T_nuis)
      hpd.derivative
      ((1 / efficientInformation (regression_ordinaryScore lscore) T_nuis 1)
        • (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean) := by
  set φ₀ := (regression_scoreCandidate g gdot sigma2 hLp2 hEmean).toL2ZeroMean with hφ₀
  -- The efficient score equals the concrete candidate `ℓ̃ = e·ġ/σ²`.
  have hes : efficientScore (regression_ordinaryScore lscore) T_nuis 1 = φ₀ :=
    regression_efficientScore_eq hLp2 hEmean hsigma_pos hchar hSigma hIBP
  -- `Ĩ = ‖ℓ̃‖²`, positive.
  have hI_eq : efficientInformation (regression_ordinaryScore lscore) T_nuis 1 = ‖φ₀‖ ^ 2 := by
    rw [efficientInformation, hes]
  have hI_pos : 0 < efficientInformation (regression_ordinaryScore lscore) T_nuis 1 := by
    rw [hI_eq]
    have : ‖φ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hEffScore_ne
    positivity
  rw [show φ₀ = efficientScore (regression_ordinaryScore lscore) T_nuis 1 from hes.symm]
  refine eif_from_efficientScore' (regression_ordinaryScore lscore) T_nuis 1
    (regression_tangent lscore T_nuis) ψ hpd
    (fun w => regression_tangent_decomp lscore T_nuis w) ?_ ?_ hI_pos ?_
  · -- h_deriv_eq: derivative reads off `u = ⟪(1 : ℝ), u⟫_ℝ`
    intro u g_nuis hg_nuis hmem
    have hval : hpd.derivative ⟨regression_ordinaryScore lscore u + g_nuis, hmem⟩ = u :=
      h_deriv_eq u g_nuis hg_nuis hmem
    rw [hval]
    change u = u * 1
    rw [mul_one]
  · -- h_gram: ⟪ℓ̃(1), ℓ̃(u)⟫ = Ĩ · ⟪(1 : ℝ), u⟫
    intro u
    -- `ℓ̃(u) = u • ℓ̃(1) = u • φ₀` (homogeneity of the efficient score).
    have key : efficientScore (regression_ordinaryScore lscore) T_nuis u = u • φ₀ := by
      have h1 := efficientScore_smul (regression_ordinaryScore lscore) T_nuis u (1 : ℝ)
      rw [smul_eq_mul, mul_one] at h1
      rw [h1, hes]
    rw [hes, key, real_inner_smul_right, hI_eq, real_inner_self_eq_norm_sq]
    change u * ‖φ₀‖ ^ 2 = ‖φ₀‖ ^ 2 * (u * 1)
    ring
  · -- membership: (1/Ĩ) • efficientScore ∈ Ṗ
    apply Submodule.smul_mem
    rw [efficientScore, regression_ordinaryScore_one, regression_tangent]
    apply Submodule.sub_mem
    · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self lscore)
    · exact Submodule.mem_sup_right (T_nuis.starProjection_apply_mem lscore)

end AsymptoticStatistics.Examples.Regression
