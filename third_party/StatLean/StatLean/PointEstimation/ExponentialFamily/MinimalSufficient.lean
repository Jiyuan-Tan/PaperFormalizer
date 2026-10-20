module
public import StatLean.PointEstimation.ExponentialFamily.Basic
public import StatLean.PointEstimation.Sufficiency.Factorization
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Independent
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Convex.Intrinsic

@[expose] public section

/-!
# Minimal sufficiency of the natural statistic

For a canonical exponential family the natural statistic `T` is minimal sufficient as soon as
the parameter set is rich enough to separate the coordinates of `T`: it must contain `s + 1`
natural parameters that do not lie in a proper affine subspace of the parameter space. The
likelihood ratios based on such a configuration are
$$ \frac{p_{\eta^{(j)}}(x)}{p_{\eta^{(0)}}(x)}
   \;=\; \exp\bigl(\langle \eta^{(j)} - \eta^{(0)}, T(x)\rangle
         - A(\eta^{(j)}) + A(\eta^{(0)})\bigr), $$
a one-to-one function of the vector `(⟨η^{(j)} − η^{(0)}, T(x)⟩)_j`; when the differences
`η^{(j)} − η^{(0)}` span the parameter space this vector determines `T(x)`, so `T` is
equivalent to the minimal sufficient statistic of the finite subfamily.

* `ExpFamily.fullRank_exists_affineSpan` — a full-rank parameter set contains such a
  configuration;
* `ExpFamily.isMinimalSufficient_stat` — minimal sufficiency of the natural statistic under
  the affine-span condition.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), Corollary 6.16 (in a canonical exponential family of full rank the
natural statistic is minimal sufficient). (`TPE2 §1.6 Cor 6.16`.)

**Proof formalization notes.**
* The two classical hypotheses — full rank, and the existence of an affinely spanning
  configuration of `s + 1` parameters — are kept apart. The affine-span condition is what the
  minimality proof actually uses, so it is the hypothesis of the headline theorem;
  `fullRank_exists_affineSpan` supplies it from full rank, and consumes only the
  nonempty-interior half of `ExpFamily.FullRank` (an open ball in a finite-dimensional space
  contains an affinely spanning configuration). Affine independence of the statistic, the
  other half of full rank, is what makes the parametrization identifiable; it is not needed
  here.
* Sufficiency of `T` itself is the factorization criterion: the density of `P_η` against the
  reference measure is `exp(⟨η, T⟩ − A(η))`, a function of `T` alone. σ-finiteness of the
  reference measure is required for the passage from that factorization to the θ-free
  conditional determinations demanded by `IsSufficient`; every dominated statistical model
  supplies it.
* Members of a canonical exponential family are mutually equivalent measures — the density
  `exp(⟨η, T⟩ − A(η))` is strictly positive — so the classical "common support" proviso of the
  minimal-sufficiency theory holds automatically and does not appear as a hypothesis.
* The span condition is stated as `affineSpan ℝ (Set.range η') = ⊤` with the ambient
  `AffineSubspace ℝ V` pinned by ascription. The equivalent working form, and the one the
  proof will use, is that the differences `η' i − η' 0` span `V` as a submodule.

**Bibliographic comments.** Minimal sufficiency and the likelihood-ratio construction are due
to E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased estimation,"
*Sankhyā* **10** (1950), 305–340) and R. R. Bahadur ("Sufficiency and statistical decision
functions," *Ann. Math. Statist.* **25** (1954), 423–462; "On unbiased estimates of uniformly
minimum variance," *Sankhyā* **18** (1957), 211–224). The characterization of sufficient
statistics by exponential structure goes back to R. A. Fisher (*Proc. R. Soc. Lond. A* **144**
(1934), 285–307), G. Darmois (*C. R. Acad. Sci. Paris* **200** (1935), 1265–1266),
B. O. Koopman (*Trans. Amer. Math. Soc.* **39** (1936), 399–409) and E. J. G. Pitman (*Proc.
Camb. Phil. Soc.* **32** (1936), 567–579); see also E. B. Dynkin ("Necessary and sufficient
statistics for a family of probability distributions," *Uspekhi Mat. Nauk* **6** (1951),
68–90) and O. Barndorff-Nielsen (*Information and Exponential Families in Statistical
Theory*, Wiley, 1978, Ch. 8).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace StatLean.PointEstimation

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [SecondCountableTopology V]

namespace ExpFamily

/-- A **full-rank parameter set contains an affinely spanning configuration**: from a
parameter set with nonempty interior in a finite-dimensional parameter space one can extract
`finrank ℝ V + 1` points that lie in no proper affine subspace. Only the nonempty-interior
part of `ExpFamily.FullRank` is used. -/
theorem fullRank_exists_affineSpan [FiniteDimensional ℝ V] (E : ExpFamily 𝓧 V) (Ξ' : Set V)
    -- USER-INPUT: the classical full-rank condition on the parameter set
    (hFR : E.FullRank Ξ') :
    ∃ η' : Fin (Module.finrank ℝ V + 1) → V, (∀ i, η' i ∈ Ξ') ∧
      affineSpan ℝ (Set.range η') = (⊤ : AffineSubspace ℝ V) := by
  obtain ⟨-, hint, -⟩ := hFR
  -- a nonempty-interior set affinely spans the whole space
  have hspanΞ : affineSpan ℝ Ξ' = (⊤ : AffineSubspace ℝ V) := by
    obtain ⟨x₀, hx₀⟩ := hint
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
    have hballspan : affineSpan ℝ (Metric.ball x₀ r) = (⊤ : AffineSubspace ℝ V) :=
      (convex_ball x₀ r).interior_nonempty_iff_affineSpan_eq_top.mp
        (by rw [Metric.isOpen_ball.interior_eq]; exact ⟨x₀, Metric.mem_ball_self hr⟩)
    have hle := affineSpan_mono ℝ hball
    rw [hballspan] at hle
    exact top_le_iff.mp hle
  -- extract an affinely independent spanning subset of `Ξ'`
  obtain ⟨t, hts, htspan, htind⟩ := exists_affineIndependent ℝ V Ξ'
  rw [hspanΞ] at htspan
  haveI : Finite t := finite_of_fin_dim_affineIndependent ℝ htind
  haveI : Fintype t := Fintype.ofFinite t
  have htspan' : affineSpan ℝ (Set.range (Subtype.val : t → V)) = (⊤ : AffineSubspace ℝ V) := by
    rwa [Subtype.range_coe]
  have hcard : Fintype.card t = Module.finrank ℝ V + 1 :=
    htind.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htspan'
  let e : Fin (Module.finrank ℝ V + 1) ≃ t := (Fintype.equivFinOfCardEq hcard).symm
  have hrange : Set.range (fun i => ((e i : t) : V)) = (t : Set V) := by
    ext v
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hv; exact ⟨e.symm ⟨v, hv⟩, by simp⟩
  refine ⟨fun i => ((e i : t) : V), fun i => hts (e i).2, ?_⟩
  rw [hrange]; exact htspan

/-- **Linear reconstruction from spanning inner products.** If a finite family `d : ι → V`
spans the parameter space, the coordinate vector `v ↦ (⟨d i, v⟩)_i` determines `v`, and the
inverse is realized by a continuous (hence measurable) map on the finite-dimensional coordinate
space `ι → ℝ`. This is the linear-algebra core of the minimal-sufficiency inversion. -/
private theorem exists_reconstruction {ι : Type*} [Fintype ι] (d : ι → V)
    (hspan : Submodule.span ℝ (Set.range d) = (⊤ : Submodule ℝ V)) :
    ∃ Ψ : (ι → ℝ) → V, Continuous Ψ ∧ ∀ v : V, Ψ (fun i => ⟪d i, v⟫_ℝ) = v := by
  classical
  -- the coordinate map `Φ v = (⟨d i, v⟩)_i` as a linear map
  let Φ : V →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun v i => ⟪d i, v⟫_ℝ
      map_add' := fun v w => by funext i; simp only [Pi.add_apply]; rw [inner_add_right]
      map_smul' := fun c v => by
        funext i; simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [real_inner_smul_right] }
  -- `Φ` is injective: `Φ v = 0` means `v ⟂ span (range d) = ⊤`, so `v = 0`
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hvi : ∀ i, ⟪d i, v⟫_ℝ = 0 := fun i => congrFun hv i
    have hvspan : ∀ w ∈ Submodule.span ℝ (Set.range d), ⟪w, v⟫_ℝ = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw => obtain ⟨i, rfl⟩ := hw; exact hvi i
      | zero => simp
      | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [real_inner_smul_left, ha, mul_zero]
    have hvv : ⟪v, v⟫_ℝ = 0 := hvspan v (by rw [hspan]; exact Submodule.mem_top)
    exact inner_self_eq_zero.mp hvv
  obtain ⟨Ψ, hΨ⟩ := Φ.exists_leftInverse_of_injective hker
  refine ⟨Ψ, Ψ.continuous_of_finiteDimensional, fun v => ?_⟩
  have h := LinearMap.congr_fun hΨ v
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  exact h

/-- **The natural statistic is minimal sufficient** for a canonical exponential family whose
parameter set contains `s + 1` natural parameters spanning the parameter space affinely. -/
theorem isMinimalSufficient_stat {s : ℕ} (E : ExpFamily 𝓧 V)
    -- LEAN-ONLY: σ-finiteness of the reference measure; needed to turn the density
    -- factorization into the θ-free conditional determinations of `IsSufficient`
    [SigmaFinite E.base] (Ξ' : Set V)
    -- USER-INPUT: the parameter set lies in the natural parameter set, so every member is a
    -- genuine probability measure of the family
    (hΞ : Ξ' ⊆ E.natSet)
    -- USER-INPUT: nondegenerate reference measure
    (hbase : E.base ≠ 0)
    -- USER-INPUT: the parameter set contains `s + 1` points lying in no proper affine
    -- subspace; the classical rank condition for minimality
    (hspan : ∃ η' : Fin (s + 1) → V, (∀ i, η' i ∈ Ξ') ∧
      affineSpan ℝ (Set.range η') = (⊤ : AffineSubspace ℝ V)) :
    IsMinimalSufficient (fun θ : Ξ' => E.P (θ : V)) E.stat := by
  classical
  set P : Ξ' → Measure 𝓧 := fun θ => E.P (θ : V) with hPdef
  haveI hProb : ∀ θ : Ξ', IsProbabilityMeasure (P θ) :=
    fun θ => isProbabilityMeasure_P E hbase (hΞ θ.2)
  -- the density `dP_θ/dν = exp(⟨θ, T⟩ - A(θ))`
  set p : Ξ' → 𝓧 → ℝ≥0∞ :=
    fun θ x => ENNReal.ofReal (Real.exp (⟪(θ : V), E.stat x⟫_ℝ - E.logPartition (θ : V)))
    with hpdef
  have hp : ∀ θ : Ξ', Measurable (p θ) := fun θ =>
    (((continuous_const.inner continuous_id).measurable.comp E.stat_meas).sub
      measurable_const).exp.ennreal_ofReal
  have hP : ∀ θ : Ξ', P θ = E.base.withDensity (p θ) := fun θ => P_eq_withDensity E (hΞ θ.2)
  -- (1) Sufficiency of `E.stat` via the Fisher–Neyman factorization `p_θ = (g_θ ∘ T)·1`.
  have hSuf : IsSufficient P E.stat :=
    isSufficient_of_isFactorizedDensity P E.base p hp hP E.stat_meas
      (g := fun θ t => ENNReal.ofReal (Real.exp (⟪(θ : V), t⟫_ℝ - E.logPartition (θ : V))))
      (h := fun _ => 1)
      (fun θ => (((continuous_const.inner continuous_id).measurable).sub
        measurable_const).exp.ennreal_ofReal)
      measurable_const
      (fun θ => Filter.Eventually.of_forall fun x => (mul_one _).symm)
  refine ⟨hSuf, ?_⟩
  -- (2) Minimality: reconstruct `T` from any competing sufficient statistic `U`.
  intro S' _ U hU hSufU
  obtain ⟨η', hmem, hAS⟩ := hspan
  set d : Fin (s + 1) → V := fun i => η' i - η' 0 with hddef
  -- the differences `η' i - η' 0` span `V`
  have hspan_d : Submodule.span ℝ (Set.range d) = (⊤ : Submodule ℝ V) := by
    have hvs : vectorSpan ℝ (Set.range η') = (⊤ : Submodule ℝ V) := by
      have h := congrArg AffineSubspace.direction hAS
      rwa [direction_affineSpan, AffineSubspace.direction_top] at h
    have hdeq : d = (fun w => w -ᵥ η' 0) ∘ η' := by funext i; simp [hddef, vsub_eq_sub]
    rw [hdeq, Set.range_comp, ← vectorSpan_eq_span_vsub_set_right ℝ
      (show η' 0 ∈ Set.range η' from ⟨0, rfl⟩), hvs]
  obtain ⟨Ψ, hΨcont, hΨv⟩ := exists_reconstruction d hspan_d
  -- `U` sufficient ⇒ densities factor through `U`
  obtain ⟨g', h', hg'meas, _, hfac⟩ :=
    isFactorizedDensity_of_isSufficient P E.base p hp hP hU hSufU
  set θi : Fin (s + 1) → Ξ' := fun i => ⟨η' i, hmem i⟩ with hθidef
  have hpθi : ∀ (i : Fin (s + 1)) (x : 𝓧),
      p (θi i) x = ENNReal.ofReal (Real.exp (⟪η' i, E.stat x⟫_ℝ - E.logPartition (η' i))) :=
    fun _ _ => rfl
  -- the reconstruction coordinates, a `U`-measurable function
  set φ : Fin (s + 1) → S' → ℝ :=
    fun i u => (E.logPartition (η' i) - E.logPartition (η' 0))
      + Real.log ((g' (θi i) u).toReal) - Real.log ((g' (θi 0) u).toReal) with hφdef
  have hφmeas : ∀ i, Measurable (φ i) := fun i =>
    (measurable_const.add (Real.measurable_log.comp (hg'meas (θi i)).ennreal_toReal)).sub
      (Real.measurable_log.comp (hg'meas (θi 0)).ennreal_toReal)
  set H : S' → V := fun u => Ψ (fun i => φ i u) with hHdef
  have hHmeas : Measurable H :=
    hΨcont.measurable.comp (measurable_pi_lambda _ fun i => hφmeas i)
  -- core: `φ i (U x) = ⟨d i, T x⟩` a.e. under the reference measure
  have hphi : ∀ i, ∀ᵐ x ∂E.base, φ i (U x) = ⟪d i, E.stat x⟫_ℝ := by
    intro i
    filter_upwards [hfac (θi i), hfac (θi 0)] with x hxi hx0
    have hEi : Real.exp (⟪η' i, E.stat x⟫_ℝ - E.logPartition (η' i))
        = (g' (θi i) (U x)).toReal * (h' x).toReal := by
      have h := congrArg ENNReal.toReal hxi
      rw [hpθi i x, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_mul] at h
      exact h
    have hE0 : Real.exp (⟪η' 0, E.stat x⟫_ℝ - E.logPartition (η' 0))
        = (g' (θi 0) (U x)).toReal * (h' x).toReal := by
      have h := congrArg ENNReal.toReal hx0
      rw [hpθi 0 x, ENNReal.toReal_ofReal (Real.exp_pos _).le, ENNReal.toReal_mul] at h
      exact h
    have hb_nn : (0 : ℝ) ≤ (h' x).toReal := ENNReal.toReal_nonneg
    have hai_nn : (0 : ℝ) ≤ (g' (θi i) (U x)).toReal := ENNReal.toReal_nonneg
    have ha0_nn : (0 : ℝ) ≤ (g' (θi 0) (U x)).toReal := ENNReal.toReal_nonneg
    have hprodi : 0 < (g' (θi i) (U x)).toReal * (h' x).toReal := hEi ▸ Real.exp_pos _
    have hprod0 : 0 < (g' (θi 0) (U x)).toReal * (h' x).toReal := hE0 ▸ Real.exp_pos _
    have hbpos : 0 < (h' x).toReal := by
      rcases lt_or_ge 0 (h' x).toReal with hb | hb
      · exact hb
      · nlinarith [hprod0, ha0_nn, hb]
    have hapos_i : 0 < (g' (θi i) (U x)).toReal := by
      rcases lt_or_ge 0 (g' (θi i) (U x)).toReal with ha | ha
      · exact ha
      · nlinarith [hprodi, hb_nn, ha]
    have hapos_0 : 0 < (g' (θi 0) (U x)).toReal := by
      rcases lt_or_ge 0 (g' (θi 0) (U x)).toReal with ha | ha
      · exact ha
      · nlinarith [hprod0, hb_nn, ha]
    have hlogi : ⟪η' i, E.stat x⟫_ℝ - E.logPartition (η' i)
        = Real.log ((g' (θi i) (U x)).toReal) + Real.log ((h' x).toReal) := by
      rw [← Real.log_exp (⟪η' i, E.stat x⟫_ℝ - E.logPartition (η' i)), hEi,
        Real.log_mul (ne_of_gt hapos_i) (ne_of_gt hbpos)]
    have hlog0 : ⟪η' 0, E.stat x⟫_ℝ - E.logPartition (η' 0)
        = Real.log ((g' (θi 0) (U x)).toReal) + Real.log ((h' x).toReal) := by
      rw [← Real.log_exp (⟪η' 0, E.stat x⟫_ℝ - E.logPartition (η' 0)), hE0,
        Real.log_mul (ne_of_gt hapos_0) (ne_of_gt hbpos)]
    simp only [hφdef, hddef, inner_sub_left]
    linarith [hlogi, hlog0]
  -- assemble `H ∘ U = T` a.e. under the reference, then transport to every member
  have hbaseAE : (fun x => H (U x)) =ᵐ[E.base] E.stat := by
    have hall : ∀ᵐ x ∂E.base, ∀ i, φ i (U x) = ⟪d i, E.stat x⟫_ℝ := (ae_all_iff).2 hphi
    filter_upwards [hall] with x hx
    show Ψ (fun i => φ i (U x)) = E.stat x
    rw [show (fun i => φ i (U x)) = fun i => ⟪d i, E.stat x⟫_ℝ from funext hx]
    exact hΨv (E.stat x)
  refine ⟨H, hHmeas, fun θ => ?_⟩
  have hac : P θ ≪ E.base := by rw [hP θ]; exact withDensity_absolutelyContinuous E.base (p θ)
  exact hbaseAE.filter_mono hac.ae_le

end ExpFamily

end StatLean.PointEstimation
