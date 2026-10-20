module
public import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
public import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
public import StatLean.ConcentrationInequalities.Chaining.PsiTwoMaximal
public import StatLean.ConcentrationInequalities.Chaining.DyadicNets

@[expose] public section

/-!
# Residual bounds for chaining a finite subset through nets of the carrier

The faithful infinite-`T` chaining statements (HDP Theorems 8.1.3/8.1.4/8.5.2
read through Remark 7.2.1: $\mathbb{E}\sup_{t \in T} X_t$ *is* the supremum
over finite subsets $F \subseteq T$ of $\mathbb{E}\max_{t \in F} X_t$) chain
each finite $F$ through $\varepsilon$-nets **of the full carrier $T$**. For
infinite $T$ the walk cannot stop at a finest net identifying with $T$ (the
finite-$T$ device `exists_fine_scale`); instead the chain is truncated at an
arbitrary level and the **residual** $\max_{t\in F}(X_t - X_{\pi t})$ — a
maximum of $|F|$ variables that are $\psi_2$-small of scale $K\varepsilon$ —
is bounded and sent to $0$ as $\varepsilon \to 0$ with $F$ fixed. This file
provides the three residual bounds (mean-zero expectation, absolute
expectation, tail), one per consuming assembly.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Remark 7.2.1 (the finite-subset reading of
E sup) and §8.1 (the chaining set-up whose truncation these residuals
close); the p. 227 footnote ("the general case typically follows by
approximation") is exactly this approximation.

**Proof formalization notes.** Each lemma is a direct application of the
Batch-10 finite maximal inequalities to the family
`fun t => X t ω − X (netProj N t) ω` indexed by the finite subset `F`: the
mean-zero form via the B2 bridge (`SubGaussianIncrements.isSubGaussian_sub`,
proxy `3(K·nndist)² ≤ 3(K·ε)²`) + `expectation_max_finset_le`
(bound `√3·Kε·√(2 log |F|)`); the absolute form via `expectation_abs_max_le`
(bound `2·Kε·√(log(2|F|))`); the tail via `tail_abs_max_le`
(bound `2|F|·exp(−δ²/(Kε)²)`). All three vanish as `ε → 0` for fixed finite
`F`, which is the only limit the faithful assemblies need. Named-sorry
fallback of this work item: `residual_tail_le` (the two expectation forms
land first).

**Bibliographic comments.** The truncation-and-limit reading of the chaining
argument for non-finite index sets is folklore, implicit in R. M. Dudley,
"The sizes of compact subsets of Hilbert space and continuity of Gaussian
processes," *J. Funct. Anal.* 1 (1967), 290–330, and standard in
M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*, Springer,
2014, §2.2 (where processes are handled through their finite-dimensional
marginals throughout).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Net projections of carrier points stay in the carrier. -/
lemma netProj_mem_of_subset {N : Finset E} {T : Set E}
    -- LEAN-ONLY: the net lives inside the carrier
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness so `netProj` picks a genuine net point
    (hNne : N.Nonempty) (t : E) :
    netProj N t ∈ T :=
  hNsub (Finset.mem_coe.mpr (netProj_mem hNne t))

/-- **Mean-zero chaining residual** (HDP §8.1 truncation; Remark 7.2.1
approximation): for a finite subset `F` of the carrier and an `ε`-net `N` of
the carrier, the expected maximum of the truncation residuals is at most
`√3 · Kε · √(2 log |F|)` — vanishing as `ε → 0` for fixed `F`. -/
theorem residual_expectation_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    {N : Finset E}
    -- LEAN-ONLY: the net lives inside the carrier (internal covering)
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness of the net
    (hNne : N.Nonempty)
    {ε : ℝ}
    -- LEAN-ONLY: nonnegative net radius
    (hε : 0 ≤ ε)
    -- LEAN-ONLY: `N` is an ε-net of the carrier
    (hprox : ∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε)
    {F : Finset E}
    -- LEAN-ONLY: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ∫ ω, F.sup' hFne (fun t => X t ω - X (netProj N t) ω) ∂μ
      ≤ Real.sqrt 3 * ((K : ℝ) * ε) * Real.sqrt (2 * Real.log (F.card : ℝ)) := by
  classical
  set σ2 : ℝ≥0 := 3 * (K * Real.toNNReal ε) ^ 2 with hσ2def
  -- local proxy monotonicity for `IsSubGaussian` (re-derived; the DiscreteDudley
  -- helper is `private`)
  have mono : ∀ {Y : Ω → ℝ} {a b : ℝ≥0}, IsSubGaussian Y a μ → a ≤ b →
      IsSubGaussian Y b μ := by
    intro Y a b hYa hab
    refine ⟨hYa.integrable_exp_mul, fun t => (hYa.mgf_le t).trans ?_⟩
    have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    gcongr
  -- the residual increments are centered …
  have hcenter : ∀ t ∈ F, ∫ ω, (X t ω - X (netProj N t) ω) ∂μ = 0 := by
    intro t ht
    have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
    have hpT : netProj N t ∈ T := netProj_mem_of_subset hNsub hNne t
    rw [integral_sub (hint t htT) (hint (netProj N t) hpT),
      hmean t htT, hmean (netProj N t) hpT, sub_zero]
  -- … and sub-Gaussian with proxy `σ2 = 3(K·ε)²`.
  have hSG : ∀ t ∈ F, IsSubGaussian (fun ω => X t ω - X (netProj N t) ω) σ2 μ := by
    intro t ht
    have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
    have hpT : netProj N t ∈ T := netProj_mem_of_subset hNsub hNne t
    refine mono (hinc.isSubGaussian_sub (hmeas (netProj N t) hpT) (hmeas t htT)
      hpT htT (hcenter t ht)) ?_
    rw [hσ2def]
    have hnn : nndist (netProj N t) t ≤ Real.toNNReal ε := by
      rw [nndist_dist, dist_comm]
      exact Real.toNNReal_le_toNNReal (dist_netProj_le (hprox t htT))
    gcongr
  have hsqrtσ : Real.sqrt (σ2 : ℝ) = Real.sqrt 3 * ((K : ℝ) * ε) := by
    have hcoe : ((σ2 : ℝ≥0) : ℝ) = 3 * ((K : ℝ) * ε) ^ 2 := by
      rw [hσ2def]; push_cast [Real.coe_toNNReal ε hε]; ring
    rw [hcoe, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_sq (mul_nonneg (NNReal.coe_nonneg K) hε)]
  calc ∫ ω, F.sup' hFne (fun t => X t ω - X (netProj N t) ω) ∂μ
      ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log F.card) :=
        expectation_max_finset_le hFne hcenter hSG
    _ = Real.sqrt 3 * ((K : ℝ) * ε) * Real.sqrt (2 * Real.log (F.card : ℝ)) := by
        rw [hsqrtσ]

/-- **Absolute chaining residual** (HDP §8.1 truncation, no mean-zero): the
expected maximum of `|X_t − X_{π t}|` over a finite subset is at most
`2 · Kε · √(log(2|F|))`. -/
theorem residual_abs_expectation_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    {N : Finset E}
    -- LEAN-ONLY: the net lives inside the carrier
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness of the net
    (hNne : N.Nonempty)
    {ε : ℝ}
    -- LEAN-ONLY: positive net radius (the ψ₂ scale `Kε` must be positive
    -- for the maximal engine; the assemblies' dyadic radii are positive)
    (hε : 0 < ε)
    -- LEAN-ONLY: nondegenerate increment constant (K = 0 is handled by the
    -- degenerate branches of the assemblies)
    (hK : 0 < K)
    -- LEAN-ONLY: `N` is an ε-net of the carrier
    (hprox : ∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε)
    {F : Finset E}
    -- LEAN-ONLY: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ∫ ω, F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|) ∂μ
      ≤ 2 * ((K : ℝ) * ε) * Real.sqrt (Real.log (2 * (F.card : ℝ))) := by
  classical
  set L : ℝ≥0 := K * Real.toNNReal ε with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact mul_pos hK (Real.toNNReal_pos.mpr hε)
  have hm : ∀ t ∈ F, AEMeasurable (fun ω => X t ω - X (netProj N t) ω) μ := by
    intro t ht
    have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
    have hpT : netProj N t ∈ T := netProj_mem_of_subset hNsub hNne t
    exact (hmeas t htT).sub (hmeas (netProj N t) hpT)
  have hY : ∀ t ∈ F, subGaussianNorm (fun ω => X t ω - X (netProj N t) ω) μ
      ≤ (L : ℝ≥0∞) := by
    intro t ht
    have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
    have hpT : netProj N t ∈ T := netProj_mem_of_subset hNsub hNne t
    refine (hinc (netProj N t) hpT t htT).trans ?_
    have hde : edist (netProj N t) t ≤ (Real.toNNReal ε : ℝ≥0∞) := by
      rw [edist_dist, dist_comm]
      exact ENNReal.ofReal_le_ofReal (dist_netProj_le (hprox t htT))
    calc (K : ℝ≥0∞) * edist (netProj N t) t
        ≤ (K : ℝ≥0∞) * (Real.toNNReal ε : ℝ≥0∞) := by gcongr
      _ = (L : ℝ≥0∞) := by rw [hLdef]; push_cast; ring
  have hpt : ∀ ω, F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|)
      = ⨆ i ∈ F, |X i ω - X (netProj N i) ω| := by
    intro ω
    exact (biSup_finset_eq_sup' hFne (fun t => |X t ω - X (netProj N t) ω|)
      (fun _ _ => abs_nonneg _)).symm
  have hLcoe : (L : ℝ) = (K : ℝ) * ε := by
    rw [hLdef]; push_cast [Real.coe_toNNReal ε hε.le]; ring
  calc ∫ ω, F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|) ∂μ
      = ∫ ω, ⨆ i ∈ F, |X i ω - X (netProj N i) ω| ∂μ := by simp_rw [hpt]
    _ ≤ 2 * (L : ℝ) * Real.sqrt (Real.log (2 * F.card)) :=
        expectation_abs_max_le hFne hLpos hm hY
    _ = 2 * ((K : ℝ) * ε) * Real.sqrt (Real.log (2 * (F.card : ℝ))) := by rw [hLcoe]

/-- **Chaining residual, tail form** (HDP §8.1 / Remark 8.1.6 truncation):
the maximum truncation residual over a finite subset exceeds `δ ≥ 0` with
probability at most `2|F| · exp(−δ²/(Kε)²)` — vanishing as `ε → 0` for fixed
`F` and `δ > 0`, which is the δ-slack the faithful tail assembly sends to
zero by continuity from below. -/
theorem residual_tail_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ] {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    {N : Finset E}
    -- LEAN-ONLY: the net lives inside the carrier
    (hNsub : ↑N ⊆ T)
    -- LEAN-ONLY: nonemptiness of the net
    (hNne : N.Nonempty)
    {ε : ℝ}
    -- LEAN-ONLY: positive net radius (ψ₂ scale positivity)
    (hε : 0 < ε)
    -- LEAN-ONLY: nondegenerate increment constant
    (hK : 0 < K)
    -- LEAN-ONLY: `N` is an ε-net of the carrier
    (hprox : ∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε)
    {F : Finset E}
    -- LEAN-ONLY: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty)
    {δ : ℝ}
    -- LEAN-ONLY: nonnegative threshold
    (hδ : 0 ≤ δ) :
    μ {ω | δ < F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|)}
      ≤ ENNReal.ofReal
          (2 * (F.card : ℝ) * Real.exp (-δ ^ 2 / ((K : ℝ) * ε) ^ 2)) := by
  classical
  set L : ℝ≥0 := K * Real.toNNReal ε with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact mul_pos hK (Real.toNNReal_pos.mpr hε)
  have hm : ∀ t ∈ F, AEMeasurable (fun ω => X t ω - X (netProj N t) ω) μ := by
    intro t ht
    have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
    have hpT : netProj N t ∈ T := netProj_mem_of_subset hNsub hNne t
    exact (hmeas t htT).sub (hmeas (netProj N t) hpT)
  have hY : ∀ t ∈ F, subGaussianNorm (fun ω => X t ω - X (netProj N t) ω) μ
      ≤ (L : ℝ≥0∞) := by
    intro t ht
    have htT : t ∈ T := hF (Finset.mem_coe.mpr ht)
    have hpT : netProj N t ∈ T := netProj_mem_of_subset hNsub hNne t
    refine (hinc (netProj N t) hpT t htT).trans ?_
    have hde : edist (netProj N t) t ≤ (Real.toNNReal ε : ℝ≥0∞) := by
      rw [edist_dist, dist_comm]
      exact ENNReal.ofReal_le_ofReal (dist_netProj_le (hprox t htT))
    calc (K : ℝ≥0∞) * edist (netProj N t) t
        ≤ (K : ℝ≥0∞) * (Real.toNNReal ε : ℝ≥0∞) := by gcongr
      _ = (L : ℝ≥0∞) := by rw [hLdef]; push_cast; ring
  have hpt : ∀ ω, F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|)
      = ⨆ i ∈ F, |X i ω - X (netProj N i) ω| := by
    intro ω
    exact (biSup_finset_eq_sup' hFne (fun t => |X t ω - X (netProj N t) ω|)
      (fun _ _ => abs_nonneg _)).symm
  have hLcoe : (L : ℝ) = (K : ℝ) * ε := by
    rw [hLdef]; push_cast [Real.coe_toNNReal ε hε.le]; ring
  have hset : {ω | δ < F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|)}
      = {ω | δ < ⨆ i ∈ F, |X i ω - X (netProj N i) ω|} := by
    ext ω; simp only [Set.mem_setOf_eq]; rw [hpt ω]
  calc μ {ω | δ < F.sup' hFne (fun t => |X t ω - X (netProj N t) ω|)}
      = μ {ω | δ < ⨆ i ∈ F, |X i ω - X (netProj N i) ω|} := by rw [hset]
    _ ≤ ENNReal.ofReal (2 * (F.card : ℝ) * Real.exp (-δ ^ 2 / (L : ℝ) ^ 2)) :=
        tail_abs_max_le hFne hLpos hm hY hδ
    _ = ENNReal.ofReal (2 * (F.card : ℝ) * Real.exp (-δ ^ 2 / ((K : ℝ) * ε) ^ 2)) := by
        rw [hLcoe]

end StatLean.ConcentrationInequalities
