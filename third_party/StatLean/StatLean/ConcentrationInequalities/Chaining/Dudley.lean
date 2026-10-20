module
public import StatLean.ConcentrationInequalities.Chaining.DiscreteDudley
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-!
# Dudley's integral inequality (Theorem 8.1.3 / Eqs. (8.13)–(8.16))

Integral-form Dudley from the discrete core via the comparison
$\Sigma \le 2 I$: for a process with sub-gaussian increments on a finite
index set $T$ with $\operatorname{diam} T \le D$,
$$ \mathbb{E}\Bigl[\max_{t \in T} X_t\Bigr] \;\le\;
     12\sqrt{3}\; K \int_0^{D} \sqrt{\log \mathcal{N}(T,d,\varepsilon)}\,
     d\varepsilon \quad (\text{mean-zero}), $$
$$ \mathbb{E}\Bigl[\sup_{t \in T} |X_t - X_{t_0}|\Bigr]
     \le 40\, K \int_0^{D}\!\sqrt{\log \mathcal{N}}, \qquad
   \mathbb{E}\Bigl[\sup_{s,t \in T} |X_t - X_s|\Bigr]
     \le 80\, K \int_0^{D}\!\sqrt{\log \mathcal{N}}, $$
plus the $\int_0^\infty$ display of Theorem 8.1.3 and the ONE countable lift
mandated by the sup policy. Assembly file.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.3, Eqs. (8.13), (8.14), and
Eq. (8.16) / Remark 8.1.7; the countable form realizes the p. 227 footnote
("the general case follows by approximation").

**Proof formalization notes.** Frozen constants: `12√3 = 2 × 6√3` (mean-zero,
via `dudleySum_le_two_mul_dudleyIntegral`), `40 = 2 × 20` (abs form),
`80 = 2 × 40` (pair form, triangle through a fixed `t₀`), countable lift
`40` (per-finite-subset engine against the entropy of `T` itself — the former
`ε/2` subset-covering loss and its factor `2` are gone). The diameter-capped
Eq. (8.16) is the PRIMARY
statement; the `∫_0^∞` shape of Theorem 8.1.3 is a display corollary via
`dudleyIntegral_Ioi_eq` (the `diam = 0` corner handled separately). The
mean-zero forms carry the LEAN-ONLY hypothesis
`hint : ∀ t ∈ T, Integrable (X t) μ` ruling out Bochner-junk means. The
countable lift is stated wholly in `ℝ≥0∞` (`∫⁻` of
`⨆ ENNReal.ofReal |X_t − X_{t₀}|` against `dudleyLIntegral`) so neither side
can be junk; it goes by monotone convergence (`lintegral_iSup`) over a finite
exhaustion `S_n ↑ T`, with the subset step costing exactly the factor `2`
above. Uncountable-sup statements are left to consumers per the sup policy
(ℚ-grid + right-continuity for Glivenko–Cantelli; `L^∞`-dense subfamilies for
Lipschitz classes). Named-sorry fallback of this work item:
`dudley_inequality_countable` (all finite-`T` integral forms proved; the
MCT/change-of-variables lift is the isolated hard part).

**Bibliographic comments.** R. M. Dudley, "The sizes of compact subsets of
Hilbert space and continuity of Gaussian processes," *J. Funct. Anal.* 1
(1967), 290–330. The entropy-integral formulation for sub-gaussian processes
appears in M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*,
Springer, 2014, §2.3, and in M. Ledoux and M. Talagrand, *Probability in
Banach Spaces*, Springer, 1991, Ch. 11.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- **Dudley's inequality, mean-zero capped form** (HDP §8.1, Theorem 8.1.3
+ Eq. (8.16)): `E max_{t ∈ T} X_t ≤ 12√3 · K · ∫_0^D √(log 𝒩)`. Book constant
frozen to `12√3 = 2 × 6√3`.

Carrier note (statement fix at the debt gate): the finite maximum is stated
with the junk-free `Finset.sup'` carrier, inherited verbatim from
`discrete_dudley_of_finite` (see its docstring for the `|T| = 1` counterexample to the
old set-bounded `⨆ t ∈ T` form). -/
theorem dudley_inequality_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness so the (junk-free) `Finset.sup'` is defined
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap; the D = 0 corner degenerates to a point
    (hD0 : 0 < D) :
    ∫ ω, hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hne) (fun t => X t ω) ∂μ
      ≤ 12 * Real.sqrt 3 * K * dudleyIntegral T D := by
  calc ∫ ω, hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hne) (fun t => X t ω) ∂μ
      ≤ 6 * Real.sqrt 3 * K * dudleySum T :=
        discrete_dudley_of_finite hfin hne hmeas hint hmean hinc
    _ ≤ 6 * Real.sqrt 3 * K * (2 * dudleyIntegral T D) := by
        refine mul_le_mul_of_nonneg_left
          (dudleySum_le_two_mul_dudleyIntegral hfin hne hD hD0) ?_
        positivity
    _ = 12 * Real.sqrt 3 * K * dudleyIntegral T D := by ring

/-- **Dudley's inequality, absolute form** (HDP §8.1, Eq. (8.13), capped):
`E sup |X_t − X_{t₀}| ≤ 40 · K · ∫_0^D √(log 𝒩)`, NO mean-zero — THE
consumer-facing form. Book constant frozen to `40 = 2 × 20`. -/
theorem dudley_inequality_abs_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 40 * K * dudleyIntegral T D := by
  calc ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ
      ≤ 20 * K * dudleySum T :=
        discrete_dudley_abs_of_finite hfin hne hmeas hinc ht₀
    _ ≤ 20 * K * (2 * dudleyIntegral T D) := by
        refine mul_le_mul_of_nonneg_left
          (dudleySum_le_two_mul_dudleyIntegral hfin hne hD hD0) ?_
        positivity
    _ = 40 * K * dudleyIntegral T D := by ring

/-- **Dudley's inequality, pair form** (HDP §8.1, Eq. (8.14), capped):
`E sup_{s,t} |X_t − X_s| ≤ 80 · K · ∫_0^D √(log 𝒩)` via the triangle
inequality through a fixed `t₀`. Book constant frozen to `80 = 2 × 40`. -/
theorem dudley_inequality_abs_pair_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫ ω, ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω| ∂μ
      ≤ 80 * K * dudleyIntegral T D := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F ↔ t ∈ T := fun t => hfin.mem_toFinset
  set t₀ := hne.some with ht₀def
  have ht₀ : t₀ ∈ T := hne.some_mem
  -- Set ↔ Finset conversion for suprema.
  have setToF : ∀ g : E → ℝ, (⨆ x ∈ T, g x) = ⨆ x ∈ F, g x :=
    fun g => iSup_congr fun x => by rw [hfin.mem_toFinset]
  -- The anchored single supremum and its integrability (Eq. (8.13) form).
  set A : Ω → ℝ := fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω| with hAdef
  have hIntA : MeasureTheory.Integrable A μ :=
    integrable_biSup_sub hfin hne hmeas hinc ht₀
  -- The double supremum as a supremum over the product Finset.
  have hPne : (F ×ˢ F).Nonempty := hFne.product hFne
  -- Integrability of the pair supremum via `integrable_biSup_abs` over `P`.
  have hIntP : MeasureTheory.Integrable
      (fun ω => ⨆ p ∈ (F ×ˢ F), |X p.1 ω - X p.2 ω|) μ := by
    refine integrable_biSup_abs hPne (L := K * Real.toNNReal (Metric.diam T))
      (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      exact (hmeas p.1 ((hmemT p.1).mp hp1)).sub (hmeas p.2 ((hmemT p.2).mp hp2))
    · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have h1 : p.1 ∈ T := (hmemT p.1).mp hp1
      have h2 : p.2 ∈ T := (hmemT p.2).mp hp2
      refine (hinc p.2 h2 p.1 h1).trans ?_
      have hde : edist p.2 p.1 ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd h2 h1)
      calc (K : ℝ≥0∞) * edist p.2 p.1
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
  -- Identify the double supremum with the product supremum, pointwise.
  have hpair_eq : (fun ω => ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|)
      = fun ω => ⨆ p ∈ (F ×ˢ F), |X p.1 ω - X p.2 ω| := by
    funext ω
    have e1 : (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|)
        = F.sup' hFne (fun t => F.sup' hFne (fun s => |X t ω - X s ω|)) := by
      have hinner : ∀ t, (⨆ s ∈ T, |X t ω - X s ω|)
          = F.sup' hFne (fun s => |X t ω - X s ω|) := fun t => by
        rw [setToF (fun s => |X t ω - X s ω|),
          biSup_finset_eq_sup' hFne (fun s => |X t ω - X s ω|)
            (fun _ _ => abs_nonneg _)]
      calc (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|)
          = ⨆ t ∈ T, F.sup' hFne (fun s => |X t ω - X s ω|) :=
            iSup_congr fun t => iSup_congr fun _ => hinner t
        _ = F.sup' hFne (fun t => F.sup' hFne (fun s => |X t ω - X s ω|)) := by
            rw [setToF (fun t => F.sup' hFne (fun s => |X t ω - X s ω|)),
              biSup_finset_eq_sup' hFne
                (fun t => F.sup' hFne (fun s => |X t ω - X s ω|))
                (fun t _ => (abs_nonneg (X t ω - X t₀ ω)).trans
                  (Finset.le_sup' (fun s => |X t ω - X s ω|) ((hmemT t₀).mpr ht₀)))]
    rw [e1, biSup_finset_eq_sup' hPne (fun p => |X p.1 ω - X p.2 ω|)
        (fun _ _ => abs_nonneg _),
      Finset.sup'_product_left hPne (fun p => |X p.1 ω - X p.2 ω|)]
  -- Pointwise: the double sup is at most twice the anchored sup.
  have hpt : ∀ ω, (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|) ≤ 2 * A ω := by
    intro ω
    have hanch : ∀ t ∈ T, |X t ω - X t₀ ω| ≤ A ω := by
      intro t ht
      simp only [hAdef]
      rw [setToF (fun u => |X u ω - X t₀ ω|)]
      exact le_biSup_finset (fun u => |X u ω - X t₀ ω|) ((hmemT t).mpr ht)
    rw [show (⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω|)
          = ⨆ p ∈ (F ×ˢ F), |X p.1 ω - X p.2 ω| from congrFun hpair_eq ω,
      biSup_finset_eq_sup' hPne (fun p => |X p.1 ω - X p.2 ω|)
        (fun _ _ => abs_nonneg _)]
    refine Finset.sup'_le hPne _ (fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have htri : |X p.1 ω - X p.2 ω| ≤ |X p.1 ω - X t₀ ω| + |X p.2 ω - X t₀ ω| := by
      have h := abs_sub_le (X p.1 ω) (X t₀ ω) (X p.2 ω)
      rwa [abs_sub_comm (X t₀ ω) (X p.2 ω)] at h
    have h1 := hanch p.1 ((hmemT p.1).mp hp1)
    have h2 := hanch p.2 ((hmemT p.2).mp hp2)
    linarith
  -- Assemble the integral bound.
  calc ∫ ω, ⨆ t ∈ T, ⨆ s ∈ T, |X t ω - X s ω| ∂μ
      ≤ ∫ ω, 2 * A ω ∂μ := by
        refine integral_mono_ae ?_ (hIntA.const_mul 2) (ae_of_all _ hpt)
        rw [hpair_eq]; exact hIntP
    _ = 2 * ∫ ω, A ω ∂μ := integral_const_mul 2 A
    _ ≤ 2 * (40 * K * dudleyIntegral T D) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact dudley_inequality_abs_of_finite hfin hne hmeas hinc ht₀ hD hD0
    _ = 80 * K * dudleyIntegral T D := by ring

/-- **Dudley's inequality, `∫_0^∞` display** (HDP §8.1, Theorem 8.1.3
verbatim shape): via `dudleyIntegral_Ioi_eq`; the `diam = 0` corner is
handled separately in the proof. `Finset.sup'` carrier as in
`dudley_inequality_of_finite` (junk-free honest maximum; statement fix at the debt
gate). -/
theorem dudley_inequality_Ioi_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness so the (junk-free) `Finset.sup'` is defined
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hne) (fun t => X t ω) ∂μ
      ≤ 12 * Real.sqrt 3 * K * ∫ ε in Set.Ioi (0 : ℝ), sqrtLogCov T ε := by
  have hDpos : (0 : ℝ) < Metric.diam T + 1 := by
    have := Metric.diam_nonneg (s := T); linarith
  have hDle : Metric.diam T ≤ Metric.diam T + 1 := by linarith
  rw [dudleyIntegral_Ioi_eq hfin hne hDle hDpos]
  exact dudley_inequality_of_finite hfin hne hmeas hint hmean hinc hDle hDpos

/-- Subset change-of-radius for the entropy integrand: for `S ⊆ T`, at radius
`ε ≥ 0`, `√log 𝒩(S, ε) ≤ √log 𝒩(T, ε/2)` (the `ε/2` covering loss of
`Metric.coveringNumber_subset_le`; junk zone at `𝒩(S,ε) = 0` handled). -/
private lemma sqrtLogCov_subset_half_le {S T : Set E} (hST : S ⊆ T) {ε : ℝ}
    (hε : 0 ≤ ε) (htop : coveringNumber T (ε / 2) ≠ ⊤) :
    sqrtLogCov S ε ≤ sqrtLogCov T (ε / 2) := by
  have hcn : coveringNumber S ε ≤ coveringNumber T (ε / 2) := by
    unfold coveringNumber
    have h := Metric.coveringNumber_subset_le (ε := Real.toNNReal ε) hST
    rwa [show Real.toNNReal ε / 2 = Real.toNNReal (ε / 2) by
      rw [Real.toNNReal_div hε]; norm_num] at h
  have hnat : (coveringNumber S ε).toNat ≤ (coveringNumber T (ε / 2)).toNat :=
    ENat.toNat_le_toNat hcn htop
  unfold sqrtLogCov
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos (coveringNumber S ε).toNat with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hnat)

/-- The `ℝ≥0∞` entropy integral of a subset is at most twice that of the
superset (the `ε/2` covering loss + a change of variables `ε = 2u`,
frozen factor `2`). Pure `∫⁻` statement: no integrability of the superset
integrand is needed. -/
private lemma dudleyLIntegral_subset_le_two {S T : Set E} (hST : S ⊆ T) {D : ℝ}
    (hD0 : 0 ≤ D) (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤) :
    dudleyLIntegral S D ≤ 2 * dudleyLIntegral T D := by
  unfold dudleyLIntegral
  set g : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (sqrtLogCov T u) with hgdef
  have hg_meas : Measurable g := (measurable_sqrtLogCov T).ennreal_ofReal
  -- (a) subset-half pointwise bound on `Ioc 0 D`.
  have ha : ∫⁻ ε in Set.Ioc (0:ℝ) D, ENNReal.ofReal (sqrtLogCov S ε)
      ≤ ∫⁻ ε in Set.Ioc (0:ℝ) D, g (ε / 2) := by
    refine setLIntegral_mono' measurableSet_Ioc (fun ε hε => ?_)
    exact ENNReal.ofReal_le_ofReal
      (sqrtLogCov_subset_half_le hST hε.1.le (hcov (ε / 2) (by linarith [hε.1])))
  -- (b) change of variables `ε = 2u`.
  have hb : ∫⁻ ε in Set.Ioc (0:ℝ) D, g (ε / 2)
      = 2 * ∫⁻ u in Set.Ioc (0:ℝ) (D / 2), g u := by
    have hF : Measurable (Set.indicator (Set.Ioc (0:ℝ) D) (fun ε => g (ε / 2))) :=
      (hg_meas.comp (measurable_id.div_const 2)).indicator measurableSet_Ioc
    have step1 :
        ∫⁻ u, Set.indicator (Set.Ioc (0:ℝ) D) (fun ε => g (ε / 2)) (2 * u) ∂volume
          = ENNReal.ofReal (|(2:ℝ)⁻¹|)
              * ∫⁻ ε, Set.indicator (Set.Ioc (0:ℝ) D) (fun ε => g (ε / 2)) ε ∂volume := by
      rw [← lintegral_map hF (measurable_const_mul 2),
        Real.map_volume_mul_left (by norm_num : (2:ℝ) ≠ 0), lintegral_smul_measure,
        smul_eq_mul]
    rw [lintegral_indicator measurableSet_Ioc] at step1
    have hLHS :
        ∫⁻ u, Set.indicator (Set.Ioc (0:ℝ) D) (fun ε => g (ε / 2)) (2 * u) ∂volume
          = ∫⁻ u in Set.Ioc (0:ℝ) (D / 2), g u := by
      rw [← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ Set.Ioc (0:ℝ) (D / 2)
      · have h2u : 2 * u ∈ Set.Ioc (0:ℝ) D := ⟨by linarith [hu.1], by linarith [hu.2]⟩
        rw [Set.indicator_of_mem h2u, Set.indicator_of_mem hu]
        show g (2 * u / 2) = g u
        congr 1; ring
      · have h2u : 2 * u ∉ Set.Ioc (0:ℝ) D := by
          intro hmem; exact hu ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
        rw [Set.indicator_of_notMem h2u, Set.indicator_of_notMem hu]
    rw [hLHS] at step1
    have hc2 : (2:ℝ≥0∞) * ENNReal.ofReal (|(2:ℝ)⁻¹|) = 1 := by
      rw [abs_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹),
        show (2:ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    rw [step1, ← mul_assoc, hc2, one_mul]
  -- (c) shrink the cap `D/2 ≤ D`.
  have hc : ∫⁻ u in Set.Ioc (0:ℝ) (D / 2), g u ≤ ∫⁻ u in Set.Ioc (0:ℝ) D, g u :=
    lintegral_mono_set (Set.Ioc_subset_Ioc_right (by linarith))
  calc ∫⁻ ε in Set.Ioc (0:ℝ) D, ENNReal.ofReal (sqrtLogCov S ε)
      ≤ ∫⁻ ε in Set.Ioc (0:ℝ) D, g (ε / 2) := ha
    _ = 2 * ∫⁻ u in Set.Ioc (0:ℝ) (D / 2), g u := hb
    _ ≤ 2 * ∫⁻ u in Set.Ioc (0:ℝ) D, g u := by gcongr

/-! ### Faithful general forms (arbitrary `T`; HDP Remark 7.2.1)

Theorem 8.1.3 and Eqs. (8.13)/(8.14)/(8.16) are stated in HDP for a general
metric space `(T, d)`; `E sup_{t∈T}` is read per Remark 7.2.1 as the
supremum over finite subsets. The statements below quantify over a finite
`F ⊆ T`, measure the entropy on the full `T`, replace `T.Finite` by the
finite-covering package `hcov`, and carry the RHS in `ℝ≥0∞`
(`dudleyLIntegral`) so a divergent entropy integral is an honest `⊤`. -/

/-- **Dudley's integral inequality, mean-zero capped form** (HDP §8.1,
Theorem 8.1.3 + Eq. (8.16); faithful general-`T` form): for every finite
subset `F ⊆ T`,
`E max_{t∈F} X_t ≤ 12√3 · K · ∫₀^D √(log 𝒩(T,d,ε)) dε` in `ℝ≥0∞`. Constant
`12√3 = 2 × 6√3` as in the finite form. -/
theorem dudley_inequality {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter (Eq (8.16)); HDP §8.1
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap; the D = 0 corner degenerates to a point
    (hD0 : 0 < D)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
  calc ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T :=
        discrete_dudley hcov hne hmeas hint hmean hinc hF hFne
    _ ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * (2 * dudleyLIntegral T D) := by
        gcongr
        exact dudleyLSum_le_two_mul_dudleyLIntegral hcov hne hD hD0
    _ = ENNReal.ofReal (12 * Real.sqrt 3) * K * dudleyLIntegral T D := by
        have h2 : ENNReal.ofReal (12 * Real.sqrt 3)
            = 2 * ENNReal.ofReal (6 * Real.sqrt 3) := by
          rw [show (12 : ℝ) * Real.sqrt 3 = 2 * (6 * Real.sqrt 3) by ring,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
        rw [h2]; ring

/-- **Dudley's inequality, absolute form** (HDP §8.1, Eq. (8.13), capped;
faithful general-`T` form): for every finite subset `F ⊆ T` and anchor
`t₀ ∈ T`, `E max_{t∈F} |X_t − X_{t₀}| ≤ 40 · K · ∫₀^D √(log 𝒩(T,d,ε)) dε`
in `ℝ≥0∞`, NO mean-zero. Constant `40` as in the finite form. -/
theorem dudley_inequality_abs {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
      ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D := by
  calc ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T :=
        discrete_dudley_abs hcov hne hmeas hinc ht₀ hF hFne
    _ ≤ ENNReal.ofReal 20 * K * (2 * dudleyLIntegral T D) := by
        gcongr
        exact dudleyLSum_le_two_mul_dudleyLIntegral hcov hne hD hD0
    _ = ENNReal.ofReal 40 * K * dudleyLIntegral T D := by
        rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]; ring

/-- **Dudley's inequality, pair form** (HDP §8.1, Eq. (8.14), capped;
faithful general-`T` form): for every finite subset `F ⊆ T`,
`E max_{s,t∈F} |X_t − X_s| ≤ 80 · K · ∫₀^D √(log 𝒩(T,d,ε)) dε` in `ℝ≥0∞`.
Constant `80 = 2 × 40` as in the finite form. -/
theorem dudley_inequality_abs_pair {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the cap dominates the diameter; HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : Metric.diam T ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal
        (∫ ω, (F ×ˢ F).sup' (hFne.product hFne) (fun p => |X p.1 ω - X p.2 ω|) ∂μ)
      ≤ ENNReal.ofReal 80 * K * dudleyLIntegral T D := by
  classical
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  set t₀ := hne.some with ht₀def
  have ht₀ : t₀ ∈ T := hne.some_mem
  set L : ℝ≥0 := K * Real.toNNReal (Metric.diam T) with hLdef
  have hPne : (F ×ˢ F).Nonempty := hFne.product hFne
  -- Integrability of the anchored single supremum (leg), via its biSup twin.
  have hIntLegB : MeasureTheory.Integrable
      (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|) μ := by
    refine integrable_biSup_abs hFne (L := L) (fun t ht => ?_) (fun t ht => ?_)
    · exact (hmeas t (hF (Finset.mem_coe.mpr ht))).sub (hmeas t₀ ht₀)
    · have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
      refine (hinc t₀ ht₀ t htT).trans ?_
      have hde : edist t₀ t ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd ht₀ htT)
      calc (K : ℝ≥0∞) * edist t₀ t
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = (L : ℝ≥0∞) := by rw [hLdef]; push_cast; ring
  have hlegeq : (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|)
      = fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|) :=
    funext fun ω => biSup_finset_eq_sup' hFne (fun t => |X t ω - X t₀ ω|)
      (fun _ _ => abs_nonneg _)
  have hIntLeg : MeasureTheory.Integrable
      (fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|)) μ := by
    rw [← hlegeq]; exact hIntLegB
  -- Integrability of the pair supremum, via its biSup twin.
  have hIntPairB : MeasureTheory.Integrable
      (fun ω => ⨆ p ∈ (F ×ˢ F), |X p.1 ω - X p.2 ω|) μ := by
    refine integrable_biSup_abs hPne (L := L) (fun p hp => ?_) (fun p hp => ?_)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      exact (hmeas p.1 (hF (Finset.mem_coe.mpr hp1))).sub
        (hmeas p.2 (hF (Finset.mem_coe.mpr hp2)))
    · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have h1 : p.1 ∈ T := hF (Finset.mem_coe.mpr hp1)
      have h2 : p.2 ∈ T := hF (Finset.mem_coe.mpr hp2)
      refine (hinc p.2 h2 p.1 h1).trans ?_
      have hde : edist p.2 p.1 ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd h2 h1)
      calc (K : ℝ≥0∞) * edist p.2 p.1
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = (L : ℝ≥0∞) := by rw [hLdef]; push_cast; ring
  have hpaireq : (fun ω => ⨆ p ∈ (F ×ˢ F), |X p.1 ω - X p.2 ω|)
      = fun ω => (F ×ˢ F).sup' hPne (fun p => |X p.1 ω - X p.2 ω|) :=
    funext fun ω => biSup_finset_eq_sup' hPne (fun p => |X p.1 ω - X p.2 ω|)
      (fun _ _ => abs_nonneg _)
  have hIntPair : MeasureTheory.Integrable
      (fun ω => (F ×ˢ F).sup' hPne (fun p => |X p.1 ω - X p.2 ω|)) μ := by
    rw [← hpaireq]; exact hIntPairB
  -- Pointwise: the pair sup is at most twice the anchored single sup (triangle).
  have hpt : ∀ ω, (F ×ˢ F).sup' hPne (fun p => |X p.1 ω - X p.2 ω|)
      ≤ 2 * F.sup' hFne (fun t => |X t ω - X t₀ ω|) := by
    intro ω
    refine Finset.sup'_le hPne _ (fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    have htri : |X p.1 ω - X p.2 ω|
        ≤ |X p.1 ω - X t₀ ω| + |X p.2 ω - X t₀ ω| := by
      have h := abs_sub_le (X p.1 ω) (X t₀ ω) (X p.2 ω)
      rwa [abs_sub_comm (X t₀ ω) (X p.2 ω)] at h
    have h1 : |X p.1 ω - X t₀ ω| ≤ F.sup' hFne (fun t => |X t ω - X t₀ ω|) :=
      Finset.le_sup' (fun t => |X t ω - X t₀ ω|) hp1
    have h2 : |X p.2 ω - X t₀ ω| ≤ F.sup' hFne (fun t => |X t ω - X t₀ ω|) :=
      Finset.le_sup' (fun t => |X t ω - X t₀ ω|) hp2
    linarith
  -- Integral form of the pointwise bound.
  have hint_le : ∫ ω, (F ×ˢ F).sup' hPne (fun p => |X p.1 ω - X p.2 ω|) ∂μ
      ≤ 2 * ∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ := by
    calc ∫ ω, (F ×ˢ F).sup' hPne (fun p => |X p.1 ω - X p.2 ω|) ∂μ
        ≤ ∫ ω, 2 * F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ :=
          integral_mono_ae hIntPair (hIntLeg.const_mul 2) (ae_of_all _ hpt)
      _ = 2 * ∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ :=
          integral_const_mul 2 _
  -- Assemble the ℝ≥0∞ bound.
  calc ENNReal.ofReal (∫ ω, (F ×ˢ F).sup' hPne (fun p => |X p.1 ω - X p.2 ω|) ∂μ)
      ≤ ENNReal.ofReal (2 * ∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ) :=
        ENNReal.ofReal_le_ofReal hint_le
    _ = 2 * ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ 2 * (ENNReal.ofReal 40 * K * dudleyLIntegral T D) := by
        gcongr
        exact dudley_inequality_abs hcov hne hmeas hinc ht₀ hD hD0 hF hFne
    _ = ENNReal.ofReal 80 * K * dudleyLIntegral T D := by
        rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]; ring

/-- **Dudley's inequality, `∫₀^∞` display** (HDP §8.1, Theorem 8.1.3
verbatim shape; faithful general-`T` form): via `dudleyLIntegral_Ioi_eq`,
the capped form with `D := diam T + 1`. -/
theorem dudley_inequality_Ioi {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii; HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.3
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
      ≤ ENNReal.ofReal (12 * Real.sqrt 3) * K
          * ∫⁻ ε in Set.Ioi (0 : ℝ), ENNReal.ofReal (sqrtLogCov T ε) := by
  have hDpos : (0 : ℝ) < Metric.diam T + 1 := by
    have := Metric.diam_nonneg (s := T); linarith
  have hDle : Metric.diam T ≤ Metric.diam T + 1 := by linarith
  rw [dudleyLIntegral_Ioi_eq hcov hne hDle hDpos]
  exact dudley_inequality hcov hne hmeas hint hmean hinc hDle hDpos hF hFne

/-- **Dudley's inequality, countable lift** (HDP §8.1, Eq. (8.13), countable
form; p. 227 footnote "general case by approximation"): stated wholly in
`ℝ≥0∞` so neither side can be junk; monotone convergence over a finite
exhaustion of `T` fed into the general per-finite-subset `dudley_inequality_abs`
below, which measures the entropy of `T` directly — so the former
`coveringNumber_subset_le` `ε/2` loss disappears and the constant improves
`80 → 40`. -/
theorem dudley_inequality_countable {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: countable T per the sup policy (uncountable sups are left
    -- to consumers)
    (hcnt : T.Countable)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: T totally bounded, as finite covering numbers; HDP p.227
    -- footnote
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- USER-INPUT: the anchor point; HDP §8.1, Eq (8.13)
    {t₀ : E} (ht₀ : t₀ ∈ T)
    -- USER-INPUT: uniform diameter bound (T bounded); HDP §8.1, Eq (8.16)
    {D : ℝ} (hD : ∀ s ∈ T, ∀ t ∈ T, dist s t ≤ D)
    -- LEAN-ONLY: positive cap
    (hD0 : 0 < D) :
    ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      ≤ ENNReal.ofReal (40 * K) * dudleyLIntegral T D := by
  -- Constant improved 80 → 40: the per-F general engine measures the
  -- entropy of T directly (no subset-covering ε/2 step); see the ledger.
  classical
  -- Enumerate the countable index set and build a finite exhaustion `S n ↑ T`
  -- through the anchor `t₀`.
  obtain ⟨f, hf⟩ := hcnt.exists_eq_range hne
  set S : ℕ → Finset E := fun n => insert t₀ ((Finset.range n).image f) with hS
  have ht₀S : ∀ n, t₀ ∈ S n := fun n => Finset.mem_insert_self _ _
  have hSne : ∀ n, (S n).Nonempty := fun n => ⟨t₀, ht₀S n⟩
  have hSsub : ∀ n, (↑(S n) : Set E) ⊆ T := by
    intro n x hx
    rw [hS, Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact ht₀
    · rw [Finset.coe_image] at hx
      obtain ⟨k, _, rfl⟩ := hx
      rw [hf]; exact Set.mem_range_self k
  have hSmono : Monotone S := by
    intro m n hmn
    apply Finset.insert_subset_insert
    exact Finset.image_subset_image (Finset.range_subset_range.mpr hmn)
  have hUnion : (⋃ n, (↑(S n) : Set E)) = T := by
    refine Set.Subset.antisymm (Set.iUnion_subset hSsub) ?_
    rw [hf]
    rintro x ⟨k, rfl⟩
    refine Set.mem_iUnion.2 ⟨k + 1, ?_⟩
    rw [hS, Finset.coe_insert, Set.mem_insert_iff, Finset.coe_image]
    exact Or.inr ⟨k, by simp [Finset.mem_range], rfl⟩
  -- `↑(S n)`-biSup as a `Finset.sup'` (real and `ℝ≥0∞`).
  have Ssup : ∀ (h : E → ℝ) (n : ℕ), (∀ t ∈ S n, 0 ≤ h t) →
      (⨆ t ∈ (↑(S n) : Set E), h t) = (S n).sup' (hSne n) h := fun h n h0 => by
    rw [Finset.iSup_coe, biSup_finset_eq_sup' (hSne n) h h0]
  have SsupE : ∀ (h : E → ℝ≥0∞) (n : ℕ),
      (⨆ t ∈ (↑(S n) : Set E), h t) = (S n).sup' (hSne n) h := fun h n => by
    rw [Finset.iSup_coe, ← Finset.sup_eq_iSup, Finset.sup'_eq_sup]
  -- The monotone-convergence integrand family.
  set Φ : ℕ → Ω → ℝ≥0∞ :=
    fun n ω => ⨆ t ∈ (↑(S n) : Set E), ENNReal.ofReal |X t ω - X t₀ ω| with hΦ
  have hΦmeas : ∀ n, AEMeasurable (Φ n) μ := by
    intro n
    simp only [hΦ]
    refine AEMeasurable.biSup (↑(S n) : Set E) (S n).countable_toSet (fun t ht => ?_)
    exact ((hmeas t (hSsub n ht)).sub (hmeas t₀ ht₀)).abs.ennreal_ofReal
  have hΦmono : ∀ ω, Monotone (fun n => Φ n ω) := by
    intro ω m n hmn
    simp only [hΦ]
    exact iSup_le_iSup_of_subset (Finset.coe_subset.mpr (hSmono hmn))
  -- `⨆ t ∈ T = ⨆ n ⨆ t ∈ S n`.
  have hA : ∀ ω, (⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω|) = ⨆ n, Φ n ω := by
    intro ω
    rw [← hUnion, iSup_iUnion]
  -- Honest diameter cap of `T` from the uniform pairwise-distance bound.
  have hdiamT : Metric.diam T ≤ D := Metric.diam_le_of_forall_dist_le hD0.le hD
  -- Per-level bound via the general (faithful) absolute Dudley inequality,
  -- measuring the entropy of `T` DIRECTLY (constant `40`, no `ε/2` step).
  have hbound : ∀ n, ∫⁻ ω, Φ n ω ∂μ
      ≤ ENNReal.ofReal (40 * K) * dudleyLIntegral T D := by
    intro n
    have ht₀A : t₀ ∈ (↑(S n) : Set E) := Finset.mem_coe.mpr (ht₀S n)
    have hAne : (↑(S n) : Set E).Nonempty := ⟨t₀, ht₀A⟩
    have hIntA : MeasureTheory.Integrable
        (fun ω => ⨆ t ∈ (↑(S n) : Set E), |X t ω - X t₀ ω|) μ :=
      integrable_biSup_sub (S n).finite_toSet hAne
        (fun t ht => hmeas t (hSsub n ht)) (hinc.mono_set (hSsub n)) ht₀A
    have hAnn : ∀ ω, 0 ≤ ⨆ t ∈ (↑(S n) : Set E), |X t ω - X t₀ ω| := by
      intro ω
      rw [Ssup (fun t => |X t ω - X t₀ ω|) n (fun _ _ => abs_nonneg _)]
      refine le_trans ?_ (Finset.le_sup' (fun t => |X t ω - X t₀ ω|) (ht₀S n))
      rw [sub_self, abs_zero]
    have hΦeq : ∀ ω, Φ n ω
        = ENNReal.ofReal (⨆ t ∈ (↑(S n) : Set E), |X t ω - X t₀ ω|) := by
      intro ω
      simp only [hΦ]
      rw [SsupE (fun t => ENNReal.ofReal |X t ω - X t₀ ω|) n,
        Ssup (fun t => |X t ω - X t₀ ω|) n (fun _ _ => abs_nonneg _),
        Finset.comp_sup'_eq_sup'_comp (hSne n) ENNReal.ofReal
          (fun x y => ENNReal.ofReal_max x y)]
      rfl
    -- Bridge the `↑(S n)`-biSup Bochner integrand to the `Finset.sup'` carrier
    -- of the general theorem.
    have hbridge : ∫ ω, ⨆ t ∈ (↑(S n) : Set E), |X t ω - X t₀ ω| ∂μ
        = ∫ ω, (S n).sup' (hSne n) (fun t => |X t ω - X t₀ ω|) ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      exact Ssup (fun t => |X t ω - X t₀ ω|) n (fun _ _ => abs_nonneg _)
    calc ∫⁻ ω, Φ n ω ∂μ
        = ∫⁻ ω, ENNReal.ofReal (⨆ t ∈ (↑(S n) : Set E), |X t ω - X t₀ ω|) ∂μ := by
          apply lintegral_congr; intro ω; exact hΦeq ω
      _ = ENNReal.ofReal (∫ ω, ⨆ t ∈ (↑(S n) : Set E), |X t ω - X t₀ ω| ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hIntA (ae_of_all _ hAnn)).symm
      _ = ENNReal.ofReal
            (∫ ω, (S n).sup' (hSne n) (fun t => |X t ω - X t₀ ω|) ∂μ) := by
          rw [hbridge]
      _ ≤ ENNReal.ofReal 40 * K * dudleyLIntegral T D :=
          dudley_inequality_abs hcov hne hmeas hinc ht₀ hdiamT hD0 (hSsub n) (hSne n)
      _ = ENNReal.ofReal (40 * K) * dudleyLIntegral T D := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40), ENNReal.ofReal_coe_nnreal]
  calc ∫⁻ ω, ⨆ t ∈ T, ENNReal.ofReal |X t ω - X t₀ ω| ∂μ
      = ∫⁻ ω, ⨆ n, Φ n ω ∂μ := by
        apply lintegral_congr; intro ω; exact hA ω
    _ = ⨆ n, ∫⁻ ω, Φ n ω ∂μ := lintegral_iSup' hΦmeas (ae_of_all _ hΦmono)
    _ ≤ ENNReal.ofReal (40 * K) * dudleyLIntegral T D := iSup_le hbound

end StatLean.ConcentrationInequalities
