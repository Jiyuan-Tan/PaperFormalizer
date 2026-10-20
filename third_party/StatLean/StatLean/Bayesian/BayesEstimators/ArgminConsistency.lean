module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.MeasureTheory.MeasurableSpace.Basic

@[expose] public section

/-!
# Deterministic argmin consistency

The elementary analytic lemma behind vdV's application of the argmax theorem in the
Bayes-point-estimator theorem
(Corollary 5.58 there): if a sequence of `ℝ≥0∞`-valued criteria converges to a **fixed**
continuous function `g` with a unique minimizer, uniformly on a ball containing the relevant
points, then approximate minimizers converge to the minimizer. Deterministic sequences only —
the in-probability version is obtained pointwise on good events in `PointEstimatorLimits.lean`.

* `exists_gap_of_unique_argmin` — well-separation on balls: continuity + uniqueness of the
  minimizer produce a positive gap `g(u₀) + η ≤ g(u)` for `‖u − u₀‖ ≥ ρ`, `‖u‖ ≤ R`
  (compactness of the annulus; no coercivity needed);
* `argmin_tendsto_of_uniform_approx` — approximate minimizers of criteria that two-sidedly
  approximate `g` on a ball, and stay in the ball, converge to `u₀`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 5, §5.9
(Corollary 5.58) and Chapter 10, §10.3 (its use in Theorem 10.8, p. 149).

**Proof formalization notes.** This replaces the `ℓ^∞(K)`-valued weak-convergence route of
the book by a direct in-probability argument (the limit criterion in the Bayes-point-estimator
theorem is `g`
recentred by the random `Δₙ`, so after recentring the limit is *deterministic*); recorded as
a formalization deviation in `PointEstimatorLimits.lean`.
-/

open Filter Topology
open scoped ENNReal

namespace StatLean.Bayesian

variable {k : ℕ}

/-- The closed annulus `{‖u‖ ≤ R} ∩ {ρ ≤ ‖u − u₀‖}` on which the gap is produced. -/
private def annulus (u₀ : EuclideanSpace ℝ (Fin k)) (R ρ : ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) R ∩ (Metric.ball u₀ ρ)ᶜ

private theorem mem_annulus_iff {u₀ : EuclideanSpace ℝ (Fin k)} {R ρ : ℝ}
    {u : EuclideanSpace ℝ (Fin k)} :
    u ∈ annulus u₀ R ρ ↔ ‖u‖ ≤ R ∧ ρ ≤ ‖u - u₀‖ := by
  simp [annulus, Metric.mem_closedBall, Metric.mem_ball, dist_eq_norm, not_lt]

private theorem isCompact_annulus (u₀ : EuclideanSpace ℝ (Fin k)) (R ρ : ℝ) :
    IsCompact (annulus u₀ R ρ) :=
  (isCompact_closedBall _ _).inter_right Metric.isOpen_ball.isClosed_compl

/-- **Well-separation of a unique minimizer on balls**: if `g` is continuous with
`g u₀ < g u` for every `u ≠ u₀`, then for every radius `R > ‖u₀‖` and every `ρ > 0` there is
a positive gap `η` with `g u₀ + η ≤ g u` whenever `‖u‖ ≤ R` and `ρ ≤ ‖u − u₀‖`. -/
theorem exists_gap_of_unique_argmin {g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: continuity of the limit criterion (derived from the Gaussian density)
    (hg : Continuous g) {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: uniqueness of the minimizer; vdV §10.3 ("any two minimizers coincide")
    (hunique : ∀ u, u ≠ u₀ → g u₀ < g u)
    {R : ℝ}
    -- LEAN-ONLY: the ball contains the minimizer
    (hR : ‖u₀‖ < R) {ρ : ℝ}
    -- LEAN-ONLY: nontrivial exclusion radius
    (hρ : 0 < ρ) :
    ∃ η : ℝ≥0∞, 0 < η ∧
      ∀ u, ‖u‖ ≤ R → ρ ≤ ‖u - u₀‖ → g u₀ + η ≤ g u := by
  rcases (annulus u₀ R ρ).eq_empty_or_nonempty with hKe | hKne
  · -- vacuous: no point of the ball sits outside the exclusion radius
    refine ⟨1, zero_lt_one, fun u hu hu' => ?_⟩
    exact absurd (mem_annulus_iff.2 ⟨hu, hu'⟩) (hKe ▸ Set.notMem_empty u)
  · -- the continuous `g` attains its minimum over the compact annulus, at some `u₁ ≠ u₀`
    obtain ⟨u₁, hu₁K, hu₁min⟩ :=
      (isCompact_annulus u₀ R ρ).exists_isMinOn hKne hg.continuousOn
    have hu₁ρ : ρ ≤ ‖u₁ - u₀‖ := (mem_annulus_iff.1 hu₁K).2
    have hne : u₁ ≠ u₀ := by
      intro h
      rw [h, sub_self, norm_zero] at hu₁ρ
      exact absurd hu₁ρ (not_le.2 hρ)
    have hlt : g u₀ < g u₁ := hunique u₁ hne
    refine ⟨g u₁ - g u₀, tsub_pos_of_lt hlt, fun u hu hu' => ?_⟩
    calc g u₀ + (g u₁ - g u₀) = g u₁ := add_tsub_cancel_of_le hlt.le
      _ ≤ g u := hu₁min (mem_annulus_iff.2 ⟨hu, hu'⟩)

/-- **Deterministic argmin consistency**: let `τₘ` be `εₘ`-approximate minimizers over the
ball `B̄(0,R)` of criteria `zₘ` that two-sidedly approximate `g` on the ball within `δₘ`,
with `εₘ, δₘ → 0` and `‖τₘ‖ ≤ R`; if `g` is continuous with unique minimizer `u₀`,
`‖u₀‖ < R`, then `τₘ → u₀`. -/
theorem argmin_tendsto_of_uniform_approx {g : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    -- LEAN-ONLY: continuity of the limit criterion (derived from the Gaussian density)
    (hg : Continuous g) {u₀ : EuclideanSpace ℝ (Fin k)}
    -- USER-INPUT: uniqueness of the minimizer; vdV §10.3 ("any two minimizers coincide")
    (hunique : ∀ u, u ≠ u₀ → g u₀ < g u)
    {R : ℝ}
    -- LEAN-ONLY: the ball contains the minimizer
    (hR : ‖u₀‖ < R)
    {z : ℕ → EuclideanSpace ℝ (Fin k) → ℝ≥0∞} {τ : ℕ → EuclideanSpace ℝ (Fin k)}
    {εseq δseq : ℕ → ℝ≥0∞}
    -- LEAN-ONLY: vanishing approximation tolerances
    (hε : Tendsto εseq atTop (𝓝 0)) (hδ : Tendsto δseq atTop (𝓝 0))
    -- LEAN-ONLY: the candidate minimizers stay in the ball (tightness, established upstream)
    (hτR : ∀ m, ‖τ m‖ ≤ R)
    -- LEAN-ONLY: two-sided uniform approximation of `g` on the ball
    (happrox : ∀ m, ∀ u, ‖u‖ ≤ R →
      z m u ≤ g u + δseq m ∧ g u ≤ z m u + δseq m)
    -- USER-INPUT: `τₘ` approximately minimizes `zₘ` over the ball; vdV §10.3, p. 147
    (hτ : ∀ m, ∀ u, ‖u‖ ≤ R → z m (τ m) ≤ z m u + εseq m) :
    Tendsto τ atTop (𝓝 u₀) := by
  rw [Metric.tendsto_atTop]
  intro ρ hρ
  obtain ⟨η, hη, hgap⟩ := exists_gap_of_unique_argmin hg hunique hR hρ
  -- the total slack `εₘ + 2δₘ` eventually undercuts the gap
  have hsum : Tendsto (fun m => εseq m + (δseq m + δseq m)) atTop (𝓝 0) := by
    simpa using hε.add (hδ.add hδ)
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hsum).2 η hη)
  refine ⟨m₀, fun m hm => ?_⟩
  rw [dist_eq_norm]
  by_contra hcon'
  have hcon : ρ ≤ ‖τ m - u₀‖ := not_lt.1 hcon'
  have hne : τ m ≠ u₀ := by
    intro h
    rw [h, sub_self, norm_zero] at hcon
    exact absurd hcon (not_le.2 hρ)
  have hfin : g u₀ ≠ ∞ := ne_top_of_lt (hunique _ hne)
  have hlow : g u₀ + η ≤ g (τ m) := hgap _ (hτR m) hcon
  have hup : g (τ m) ≤ g u₀ + (εseq m + (δseq m + δseq m)) :=
    calc g (τ m) ≤ z m (τ m) + δseq m := (happrox m (τ m) (hτR m)).2
      _ ≤ z m u₀ + εseq m + δseq m := by gcongr; exact hτ m u₀ hR.le
      _ ≤ g u₀ + δseq m + εseq m + δseq m := by gcongr; exact (happrox m u₀ hR.le).1
      _ = g u₀ + (εseq m + (δseq m + δseq m)) := by ring
  exact absurd ((ENNReal.add_le_add_iff_left hfin).1 (hlow.trans hup)) (not_le.2 (hm₀ m hm))

end StatLean.Bayesian

