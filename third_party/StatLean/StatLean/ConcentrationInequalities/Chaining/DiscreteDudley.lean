module
public import StatLean.ConcentrationInequalities.Chaining.SubGaussianIncrements
public import StatLean.ConcentrationInequalities.Chaining.SubsetChaining
public import StatLean.ConcentrationInequalities.Chaining.FinsetMaximal
public import StatLean.ConcentrationInequalities.Chaining.PsiTwoMaximal
public import StatLean.ConcentrationInequalities.Chaining.DyadicNets
public import StatLean.ConcentrationInequalities.Chaining.EntropySum
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Discrete Dudley inequality (Theorem 8.1.4)

The chaining workhorse: for a process with sub-gaussian increments
(parameter $K$) on a finite index set $T$,
$$ \mathbb{E}\Bigl[\max_{t \in T} X_t\Bigr]
     \;\le\; 6\sqrt{3}\; K \sum_{k \in \mathbb{Z}} 2^{-k}
       \sqrt{\log \mathcal{N}(T, d, 2^{-k})} $$
under mean-zero coordinates, and the no-mean-zero absolute deviation form
$$ \mathbb{E}\Bigl[\sup_{t \in T} |X_t - X_{t_0}|\Bigr]
     \;\le\; 20\, K \sum_{k \in \mathbb{Z}} 2^{-k}
       \sqrt{\log \mathcal{N}(T, d, 2^{-k})}. $$
Assembly file.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Theorem 8.1.4 and Eq. (8.2); the absolute
form is the discrete Remark 8.1.5 (the book stresses no mean-zero is needed
for the `|X_t − X_{t₀}|` forms).

**Proof formalization notes.** Book constant `C` frozen to `6√3` for the
mean-zero form: per level, the increment MGF bridge (B2 normalization
`C = 3`) gives each close-pair increment variance proxy `3·(3K·2^{−k})²`,
the pair count over `closePairs` is `≤ N_k²`, and
`expectation_max_finset_le` yields per-level cost
`√(3·(3K·2^{−k})²)·√(2·log N_k²) = 6√3·K·2^{−k}·√(log N_k)`; summing gives
`6√3·K·dudleySum`. (The per-link radius is `ε_k + ε_{k−1} = 3·2^{−k}`,
sharper than the book's rounding to `4·2^{−k}`.) The abs form re-anchors the
chain at the finest scale `κ'` with covering number `1` (so every window
level has `N_k ≥ 2`, killing spurious `√log 2` terms) and reconnects `t₀` by
ONE first-moment bound `E|X_{t₀'} − X_{t₀}| ≤ √π·K·diam T`
(`integral_abs_le_of_subGaussianNorm_le`), absorbed via
`diam·√log2 ≤ 4·dudleySum`; total frozen to `20` (`6√3 ≈ 10.4` chaining +
`4√π/√log 2 ≈ 8.52` re-anchoring, with slack). The mean-zero form carries
the LEAN-ONLY hypothesis `hint : ∀ t ∈ T, Integrable (X t) μ` ruling out
Bochner-junk means (a non-integrable `X t` satisfies `∫ X t = 0` vacuously);
increment means are then derived. The pseudometric chain end is identified
a.e. via `ae_eq_zero_of_subGaussianNorm_eq_zero` over the finitely many
points. Named-sorry fallback of this work item: `discrete_dudley_abs_of_finite`
(the mean-zero headline `discrete_dudley_of_finite` lands first).

**Bibliographic comments.** Dudley's bound is from R. M. Dudley, "The sizes
of compact subsets of Hilbert space and continuity of Gaussian processes,"
*J. Funct. Anal.* 1 (1967), 290–330 (for Gaussian processes; the
sub-gaussian extension is folklore).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {E : Type*} [PseudoMetricSpace E]

/-- Monotonicity of the sub-Gaussian variance proxy: a smaller proxy is still a
valid proxy (larger proxy Gaussian dominates). Used to feed the per-level
close-pair increments (proxy `3(K·nndist)²`) into `expectation_max_finset_le`
with a uniform per-level proxy `3(K·3ε)²`. -/
private lemma isSubGaussian_mono {Y : Ω → ℝ} {σ2 σ2' : ℝ≥0}
    (h : IsSubGaussian Y σ2 μ) (hle : σ2 ≤ σ2') : IsSubGaussian Y σ2' μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  have hσ : (σ2 : ℝ) ≤ (σ2' : ℝ) := by exact_mod_cast hle
  gcongr

/-- **Discrete Dudley inequality, mean-zero form** (HDP §8.1, Theorem 8.1.4,
Eq. (8.2)): `E max_{t ∈ T} X_t ≤ 6√3 · K · dudleySum T`. Book's unnamed
absolute constant `C` frozen to `6√3` (see file notes for the derivation).

Carrier note (statement fix at the debt gate): the finite maximum is stated
with the junk-free `Finset.sup'` over `hfin.toFinset` — the honest
`max_{t ∈ T} X_t` of the book. The previous set-bounded `⨆ t ∈ T, X t ω` form
was **false**: for `ι ⊋ T` that biSup equals `(max_{t ∈ T} X t ω)⁺`, and at
`|T| = 1` the left side degenerates to `∫ (X_c)⁺ > 0` while the right side is
`0` (all covering numbers are `1`). The `|·|`-valued forms
(`discrete_dudley_abs_of_finite` and downstream) keep the biSup carrier, which is
junk-free there since the family is nonnegative. -/
theorem discrete_dudley_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG, HDP p.224 / p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness so the (junk-free) `Finset.sup'` is defined
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ) :
    ∫ ω, hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hne) (fun t => X t ω) ∂μ
      ≤ 6 * Real.sqrt 3 * K * dudleySum T := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hfin.mem_toFinset.mp ht
  have ht' : hne.some ∈ T := hne.some_mem
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hD0 | hDpos
  · -- Degenerate case: `diam T = 0`, all coordinates coincide a.e.
    set c := hne.some with hcdef
    have hcT : c ∈ T := hne.some_mem
    have hzero : ∀ t ∈ T, dist c t = 0 := by
      intro t ht
      have hle := Metric.dist_le_diam_of_mem hbd hcT ht
      rw [← hD0] at hle
      exact le_antisymm hle dist_nonneg
    have hae : ∀ t ∈ T, (fun ω => X t ω - X c ω) =ᵐ[μ] 0 := by
      intro t ht
      exact hinc.sub_ae_eq_zero (hmeas c hcT) (hmeas t ht) hcT ht (hzero t ht)
    have haeeq : (fun ω => F.sup' hFne (fun t => X t ω)) =ᵐ[μ] fun ω => X c ω := by
      have hall : ∀ᵐ ω ∂μ, ∀ t ∈ T, X t ω = X c ω := by
        rw [hfin.eventually_all]
        intro t ht
        filter_upwards [hae t ht] with ω hω
        have : X t ω - X c ω = 0 := hω
        linarith
      filter_upwards [hall] with ω hω
      apply le_antisymm
      · exact Finset.sup'_le hFne _ (fun t ht => le_of_eq (hω t (hmemT t ht)))
      · exact Finset.le_sup' (fun t => X t ω) (hfin.mem_toFinset.mpr hcT)
    calc ∫ ω, F.sup' hFne (fun t => X t ω) ∂μ
        = ∫ ω, X c ω ∂μ := integral_congr_ae haeeq
      _ = 0 := hmean c hcT
      _ ≤ 6 * Real.sqrt 3 * K * dudleySum T :=
          mul_nonneg (by positivity) (dudleySum_nonneg T)
  · -- Main case: `diam T > 0`, dyadic chaining.
    obtain ⟨κ, hκ1, hκ2⟩ := exists_coarse_scale hDpos
    set ε : ℕ → ℝ := fun j => (2 : ℝ) ^ (-(κ + (j : ℤ))) with hεdef
    have hεval : ∀ j : ℕ, ε j = (2 : ℝ) ^ (-(κ + (j : ℤ))) := fun j => by rw [hεdef]
    have hεpos : ∀ j : ℕ, 0 < ε j := fun j => by rw [hεval]; exact zpow_pos (by norm_num) _
    have hεrec : ∀ j : ℕ, ε j = 2 * ε (j + 1) := by
      intro j
      rw [hεval, hεval,
        show (-(κ + ((j + 1 : ℕ) : ℤ))) = (-(κ + (j : ℤ))) - 1 by push_cast; ring,
        zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp only [zpow_one]; ring
    have hεle : ∀ j : ℕ, ε (j + 1) ≤ ε j := fun j => by
      rw [hεrec j]; linarith [hεpos (j + 1)]
    -- Dyadic nets at every scale.
    have hnet : ∀ j : ℕ, ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧
        (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε j) ∧ (N.card : ℕ∞) = coveringNumber T (ε j) :=
      fun j => exists_finset_net hfin hne (hεpos j)
    choose N hN using hnet
    have hprojT : ∀ i : ℕ, ∀ t : E, netProj (N i) t ∈ T :=
      fun i t => (hN i).1 (Finset.mem_coe.mpr (netProj_mem (hN i).2.1 t))
    have hproj : ∀ i : ℕ, ∀ t ∈ T, dist t (netProj (N i) t) ≤ ε i :=
      fun i t ht => dist_netProj_le ((hN i).2.2.1 t ht)
    -- Coarse net is a singleton; its point `c` anchors the chain.
    have hcov1 : coveringNumber T (ε 0) = 1 := by
      apply coveringNumber_eq_one_of_diam_le hne hbd (le_of_lt (hεpos 0))
      rw [hεval]; push_cast; simpa using hκ1
    have hcard0 : (N 0).card = 1 := by
      have h := (hN 0).2.2.2; rw [hcov1] at h; exact_mod_cast h
    obtain ⟨c, hc0⟩ := Finset.card_eq_one.mp hcard0
    have hcT : c ∈ T := (hN 0).1 (Finset.mem_coe.mpr (hc0 ▸ Finset.mem_singleton_self c))
    have hπ0 : ∀ t : E, netProj (N 0) t = c := by
      intro t
      rw [hc0]
      have hmem := netProj_mem (Finset.singleton_nonempty c) t
      rwa [Finset.mem_singleton] at hmem
    -- Fine scale where the finest net identifies with `T` a.e.
    obtain ⟨n, hn_pos, hfineScale⟩ := exists_fine_scale hfin κ
    have hfine0 : ∀ t ∈ T, dist t (netProj (N n) t) = 0 := by
      intro t ht
      apply hfineScale t ht (netProj (N n) t) (hprojT n t)
      rw [← hεval n]; exact hproj n t ht
    have hclean : ∀ᵐ ω ∂μ, ∀ t ∈ T, X (netProj (N n) t) ω = X t ω := by
      rw [hfin.eventually_all]
      intro t ht
      have hsub := hinc.sub_ae_eq_zero (hmeas t ht) (hmeas (netProj (N n) t) (hprojT n t))
        ht (hprojT n t) (hfine0 t ht)
      filter_upwards [hsub] with ω hω
      have : X (netProj (N n) t) ω - X t ω = 0 := hω
      linarith
    -- Per-level suprema and close-pair suprema (`Finset.sup'`-carried: the
    -- junk-free honest maxima; see the theorem's carrier note).
    set S : ℕ → Ω → ℝ := fun j ω =>
      F.sup' hFne (fun t => X (netProj (N (j + 1)) t) ω - X (netProj (N j) t) ω) with hSdef
    set CP : ℕ → Finset (E × E) := fun j =>
      closePairs (N (j + 1)) (N j) (ε (j + 1) + ε j) with hCPdef
    have hCPne : ∀ j : ℕ, (CP j).Nonempty := fun j =>
      ⟨(netProj (N (j + 1)) hne.some, netProj (N j) hne.some),
        proj_pair_mem_closePairs (hproj (j + 1) hne.some ht') (hproj j hne.some ht')
          (hN (j + 1)).2.1 (hN j).2.1⟩
    set CPS : ℕ → Ω → ℝ := fun j ω =>
      (CP j).sup' (hCPne j) (fun p => X p.1 ω - X p.2 ω) with hCPSdef
    have hCPmem : ∀ j : ℕ, ∀ p ∈ CP j, p.1 ∈ T ∧ p.2 ∈ T := by
      intro j p hp
      rw [hCPdef] at hp
      simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨(hN (j + 1)).1 (Finset.mem_coe.mpr hp.1.1), (hN j).1 (Finset.mem_coe.mpr hp.1.2)⟩
    -- Integrability of all suprema.
    have hIntS : ∀ j : ℕ, MeasureTheory.Integrable (S j) μ := fun j =>
      integrable_sup'_finset hFne fun t ht =>
        (hint _ (hprojT (j + 1) t)).sub (hint _ (hprojT j t))
    have hIntCPS : ∀ j : ℕ, MeasureTheory.Integrable (CPS j) μ := fun j =>
      integrable_sup'_finset (hCPne j) fun p hp =>
        (hint _ (hCPmem j p hp).1).sub (hint _ (hCPmem j p hp).2)
    have hIntSupX : MeasureTheory.Integrable (fun ω => F.sup' hFne (fun t => X t ω)) μ :=
      integrable_sup'_finset hFne fun t ht => hint t (hmemT t ht)
    have hIntSupA : MeasureTheory.Integrable
        (fun ω => F.sup' hFne (fun t => X t ω - X c ω)) μ :=
      integrable_sup'_finset hFne fun t ht => (hint t (hmemT t ht)).sub (hint c hcT)
    -- Per-level term is dominated by its supremum.
    have term_le_S : ∀ j : ℕ, ∀ t ∈ T, ∀ ω,
        (X (netProj (N (j + 1)) t) ω - X (netProj (N j) t) ω) ≤ S j ω := by
      intro j t ht ω
      rw [hSdef]; simp only
      exact Finset.le_sup'
        (fun s => X (netProj (N (j + 1)) s) ω - X (netProj (N j) s) ω)
        (hfin.mem_toFinset.mpr ht)
    -- STEP A: reduce to the `X_t - X_c` sup via mean-zero anchoring at `c`.
    have hstepA : (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
        ≤ ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ := by
      have hpt : ∀ ω, F.sup' hFne (fun t => X t ω)
          ≤ X c ω + F.sup' hFne (fun t => X t ω - X c ω) := by
        intro ω
        refine Finset.sup'_le hFne _ (fun t ht => ?_)
        have hle : (X t ω - X c ω) ≤ F.sup' hFne (fun s => X s ω - X c ω) :=
          Finset.le_sup' (fun s => X s ω - X c ω) ht
        linarith
      calc (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
          ≤ ∫ ω, (X c ω + F.sup' hFne (fun t => X t ω - X c ω)) ∂μ :=
            integral_mono_ae hIntSupX ((hint c hcT).add hIntSupA) (ae_of_all _ hpt)
        _ = (∫ ω, X c ω ∂μ) + ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ :=
            integral_add (hint c hcT) hIntSupA
        _ = ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ := by rw [hmean c hcT, zero_add]
    -- STEP B1: split the anchored sup along the chain.
    have hB1 : (∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ)
        ≤ ∑ j ∈ Finset.range n, ∫ ω, S j ω ∂μ := by
      rw [← integral_finset_sum (Finset.range n) (fun j _ => hIntS j)]
      refine integral_mono_ae hIntSupA
        (integrable_finset_sum _ (fun j _ => hIntS j)) ?_
      filter_upwards [hclean] with ω hω
      refine Finset.sup'_le hFne _ (fun t ht => ?_)
      have htT := hmemT t ht
      have htel : X t ω - X c ω
          = ∑ i ∈ Finset.range n,
              (X (netProj (N (i + 1)) t) ω - X (netProj (N i) t) ω) := by
        have h0 : X (netProj (N 0) t) ω = X c ω := by rw [hπ0 t]
        have hnn : X (netProj (N n) t) ω = X t ω := hω t htT
        rw [← hnn, ← h0]
        exact chain_telescope (fun i => X (netProj (N i) t) ω)
      rw [htel]
      exact Finset.sum_le_sum (fun i _ => term_le_S i t htT ω)
    -- STEP B2: bound each level by `6√3 K` times the dyadic summand.
    have hB2 : ∀ j ∈ Finset.range n,
        (∫ ω, S j ω ∂μ) ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) := by
      intro j _
      set r : ℝ := ε (j + 1) + ε j with hrdef
      have hrpos : 0 < r := by rw [hrdef]; linarith [hεpos (j + 1), hεpos j]
      have hr3 : r = 3 * ε (j + 1) := by rw [hrdef, hεrec j]; ring
      set σ2 : ℝ≥0 := 3 * (K * Real.toNNReal r) ^ 2 with hσ2def
      -- centering & sub-Gaussianity of every close-pair increment
      have hcenter : ∀ p ∈ CP j, ∫ ω, (X p.1 ω - X p.2 ω) ∂μ = 0 := by
        intro p hp
        rw [integral_sub (hint _ (hCPmem j p hp).1) (hint _ (hCPmem j p hp).2),
          hmean _ (hCPmem j p hp).1, hmean _ (hCPmem j p hp).2, sub_zero]
      have hSG : ∀ p ∈ CP j, IsSubGaussian (fun ω => X p.1 ω - X p.2 ω) σ2 μ := by
        intro p hp
        have hdle : dist p.1 p.2 ≤ r := by
          rw [hCPdef] at hp
          simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
          exact hp.2
        refine isSubGaussian_mono
          (hinc.isSubGaussian_sub (hmeas _ (hCPmem j p hp).2) (hmeas _ (hCPmem j p hp).1)
            (hCPmem j p hp).2 (hCPmem j p hp).1 (hcenter p hp)) ?_
        rw [hσ2def]
        have hnn : nndist p.2 p.1 ≤ Real.toNNReal r := by
          rw [nndist_dist, dist_comm]; exact Real.toNNReal_le_toNNReal hdle
        gcongr
      -- close-pair cardinality control
      set Mnat : ℕ := (N (j + 1)).card with hMnatdef
      set M : ℝ := (Mnat : ℝ) with hMdef
      have hNjle : (N j).card ≤ (N (j + 1)).card := by
        have h1 := (hN j).2.2.2
        have h2 := (hN (j + 1)).2.2.2
        have hanti : coveringNumber T (ε j) ≤ coveringNumber T (ε (j + 1)) :=
          coveringNumber_anti (hεle j)
        rw [← h1, ← h2] at hanti
        exact_mod_cast hanti
      have hcardCPnat : (CP j).card ≤ Mnat ^ 2 := by
        calc (CP j).card ≤ (N (j + 1)).card * (N j).card := card_closePairs_le _ _ _
          _ ≤ (N (j + 1)).card * (N (j + 1)).card := by gcongr
          _ = Mnat ^ 2 := by rw [hMnatdef, sq]
      have hcard1nat : 0 < (CP j).card := Finset.card_pos.mpr (hCPne j)
      have hM1nat : 0 < Mnat := Finset.card_pos.mpr (hN (j + 1)).2.1
      have hcardCP : ((CP j).card : ℝ) ≤ M ^ 2 := by rw [hMdef]; exact_mod_cast hcardCPnat
      -- identify the covering number toNat with the net cardinality
      have hcov : (coveringNumber T (ε (j + 1))).toNat = (N (j + 1)).card := by
        have h := (hN (j + 1)).2.2.2; rw [← h]; simp
      have hslc : sqrtLogCov T (ε (j + 1)) = Real.sqrt (Real.log M) := by
        unfold sqrtLogCov; rw [hcov, hMdef, hMnatdef]
      -- √(σ2) = √3 · (K·r)
      have hsqrtσ : Real.sqrt (σ2 : ℝ) = Real.sqrt 3 * ((K : ℝ) * r) := by
        have hcoe : ((σ2 : ℝ≥0) : ℝ) = 3 * ((K : ℝ) * r) ^ 2 := by
          rw [hσ2def]; push_cast [Real.coe_toNNReal r hrpos.le]; ring
        rw [hcoe, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_sq (mul_nonneg (NNReal.coe_nonneg K) hrpos.le)]
      -- √(2 log |CP|) ≤ 2 · sqrtLogCov
      have hstep : Real.sqrt (2 * Real.log ((CP j).card : ℝ))
          ≤ 2 * sqrtLogCov T (ε (j + 1)) := by
        have hR : 2 * sqrtLogCov T (ε (j + 1)) = Real.sqrt (4 * Real.log M) := by
          rw [hslc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt 4 = 2 from by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        rw [hR]
        apply Real.sqrt_le_sqrt
        have hlogcard : Real.log ((CP j).card : ℝ) ≤ 2 * Real.log M := by
          have hpos : (0 : ℝ) < ((CP j).card : ℝ) := by exact_mod_cast hcard1nat
          have h := Real.log_le_log hpos hcardCP
          rw [Real.log_pow] at h; push_cast at h; linarith
        linarith
      -- dyadic summand identity
      have hdud : dudleySummand T (κ + 1 + (j : ℤ))
          = ε (j + 1) * sqrtLogCov T (ε (j + 1)) := by
        have hkk : (-(κ + 1 + (j : ℤ))) = (-(κ + ((j + 1 : ℕ) : ℤ))) := by push_cast; ring
        simp only [dudleySummand]
        rw [hkk, hεval (j + 1)]
      -- assemble the level bound
      calc (∫ ω, S j ω ∂μ)
          ≤ ∫ ω, CPS j ω ∂μ := by
            refine integral_mono_ae (hIntS j) (hIntCPS j) (ae_of_all _ (fun ω => ?_))
            rw [hSdef, hCPSdef]; simp only
            refine Finset.sup'_le hFne _ (fun t ht => ?_)
            have htT := hmemT t ht
            exact Finset.le_sup' (fun p => X p.1 ω - X p.2 ω)
              (proj_pair_mem_closePairs (hproj (j + 1) t htT) (hproj j t htT)
                (hN (j + 1)).2.1 (hN j).2.1)
        _ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (CP j).card) := by
            rw [hCPSdef]; simp only
            exact expectation_max_finset_le (hCPne j) hcenter hSG
        _ ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) := by
            rw [hsqrtσ, hdud]
            calc Real.sqrt 3 * ((K : ℝ) * r) * Real.sqrt (2 * Real.log (CP j).card)
                ≤ Real.sqrt 3 * ((K : ℝ) * r) * (2 * sqrtLogCov T (ε (j + 1))) := by
                  apply mul_le_mul_of_nonneg_left hstep
                  exact mul_nonneg (Real.sqrt_nonneg 3)
                    (mul_nonneg (NNReal.coe_nonneg K) hrpos.le)
              _ = 6 * Real.sqrt 3 * K * (ε (j + 1) * sqrtLogCov T (ε (j + 1))) := by
                  rw [hr3]; ring
    -- WINDOW SUM: the level costs sum below the full dyadic entropy sum.
    have hwin : ∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)) ≤ dudleySum T := by
      have hemb : Function.Injective (fun j : ℕ => κ + 1 + (j : ℤ)) := by
        intro a b hab; simp only at hab; omega
      rw [show (∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)))
            = ∑ k ∈ (Finset.range n).map ⟨fun j : ℕ => κ + 1 + (j : ℤ), hemb⟩, dudleySummand T k
          from by rw [Finset.sum_map]; rfl]
      exact sum_window_le_dudleySum hfin hne _
    -- COMBINE.
    calc (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
        ≤ ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ := hstepA
      _ ≤ ∑ j ∈ Finset.range n, ∫ ω, S j ω ∂μ := hB1
      _ ≤ ∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) :=
          Finset.sum_le_sum hB2
      _ ≤ 6 * Real.sqrt 3 * K * dudleySum T := by
          have heq : ∑ j ∈ Finset.range n,
                6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + 1 + (j : ℤ))
              = 6 * Real.sqrt 3 * K * ∑ j ∈ Finset.range n, dudleySummand T (κ + 1 + (j : ℤ)) := by
            rw [Finset.mul_sum]
          rw [heq]
          exact mul_le_mul_of_nonneg_left hwin (by positivity)

/-- Integrability of the anchored supremum, exported for `Chaining/Dudley.lean`
and the countable lift (derived from the increment tails, never
hypothesized). -/
lemma integrable_biSup_sub {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (finite sup domination)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    MeasureTheory.Integrable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  have hFne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]; exact hne
  set L : ℝ≥0 := K * Real.toNNReal (Metric.diam T) with hL
  have key : MeasureTheory.Integrable
      (fun ω => ⨆ t ∈ hfin.toFinset, |X t ω - X t₀ ω|) μ := by
    refine integrable_biSup_abs hFne (L := L) (fun t ht => ?_) (fun t ht => ?_)
    · exact (hmeas t (hfin.mem_toFinset.mp ht)).sub (hmeas t₀ ht₀)
    · have htT : t ∈ T := hfin.mem_toFinset.mp ht
      refine (hinc t₀ ht₀ t htT).trans ?_
      have hde : edist t₀ t ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd ht₀ htT)
      calc (K : ℝ≥0∞) * edist t₀ t
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = (L : ℝ≥0∞) := by rw [hL]; push_cast; ring
  have hcongr : (fun ω => ⨆ t ∈ hfin.toFinset, |X t ω - X t₀ ω|)
      = fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω| := by
    funext ω
    exact iSup_congr fun t => by rw [hfin.mem_toFinset]
  rwa [hcongr] at key

/-- **Discrete Dudley inequality, absolute form** (HDP §8.1, Remark 8.1.5,
discrete): `E sup_{t ∈ T} |X_t − X_{t₀}| ≤ 20 · K · dudleySum T`, with NO
mean-zero hypothesis (as the book stresses for Eq. (8.13)). Book constant
frozen to `20` (`6√3` chaining + `4√π/√log 2` re-anchoring, slack). -/
theorem discrete_dudley_abs_of_finite {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: T finite (book WLOG, HDP p.224 / p.227 footnote)
    (hfin : T.Finite)
    -- LEAN-ONLY: nonemptiness guards the real biSup junk value
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- USER-INPUT: sub-gaussian increments only (NO mean-zero); HDP §8.1
    (hinc : SubGaussianIncrements X K T μ)
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T) :
    ∫ ω, ⨆ t ∈ T, |X t ω - X t₀ ω| ∂μ ≤ 20 * K * dudleySum T := by
  classical
  have hbd : Bornology.IsBounded T := hfin.isBounded
  set F := hfin.toFinset with hFdef
  have hFne : F.Nonempty := by rw [hFdef, Set.Finite.toFinset_nonempty]; exact hne
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hfin.mem_toFinset.mp ht
  have setToF : ∀ f : E → ℝ, (⨆ t ∈ F, f t) = ⨆ t ∈ T, f t :=
    fun f => iSup_congr fun t => by rw [hfin.mem_toFinset]
  -- Integrability of the anchored abs-sup (exported below).
  have hIntSup : MeasureTheory.Integrable (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) μ :=
    integrable_biSup_sub hfin hne hmeas hinc ht₀
  have hIntSupF : MeasureTheory.Integrable (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|) μ := by
    rw [show (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|)
          = (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) from funext fun ω => setToF _]
    exact hIntSup
  -- Degenerate `K = 0`: every increment vanishes a.e. (ψ₂-norm ≤ 0).
  rcases eq_or_lt_of_le (zero_le (a := K)) with hK0 | hKpos
  · have hae : ∀ t ∈ T, (fun ω => X t ω - X t₀ ω) =ᵐ[μ] 0 := by
      intro t ht
      have hle : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ ≤ 0 := by
        refine (hinc t₀ ht₀ t ht).trans ?_
        rw [← hK0]; simp
      exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas t₀ ht₀))
        (le_antisymm hle (by positivity))
    have haeeq : (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) =ᵐ[μ] fun _ => (0 : ℝ) := by
      have hall : ∀ᵐ ω ∂μ, ∀ t ∈ T, |X t ω - X t₀ ω| = 0 := by
        rw [hfin.eventually_all]
        intro t ht
        filter_upwards [hae t ht] with ω hω
        have : X t ω - X t₀ ω = 0 := hω
        rw [this, abs_zero]
      filter_upwards [hall] with ω hω
      rw [← setToF (fun t => |X t ω - X t₀ ω|),
        biSup_finset_eq_sup' hFne _ (fun _ _ => abs_nonneg _)]
      apply le_antisymm
      · exact Finset.sup'_le hFne _ (fun t ht => le_of_eq (hω t (hmemT t ht)))
      · calc (0 : ℝ) = |X t₀ ω - X t₀ ω| := by rw [sub_self, abs_zero]
          _ ≤ _ := Finset.le_sup' (fun t => |X t ω - X t₀ ω|) (hfin.mem_toFinset.mpr ht₀)
    rw [integral_congr_ae haeeq, integral_zero]
    exact mul_nonneg (by positivity) (dudleySum_nonneg T)
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hD0 | hDpos
  · -- Degenerate case `diam T = 0`: every coordinate equals `X t₀` a.e.
    have hzero : ∀ t ∈ T, dist t₀ t = 0 := by
      intro t ht
      have hle := Metric.dist_le_diam_of_mem hbd ht₀ ht
      rw [← hD0] at hle
      exact le_antisymm hle dist_nonneg
    have hae : ∀ t ∈ T, (fun ω => X t ω - X t₀ ω) =ᵐ[μ] 0 := fun t ht =>
      hinc.sub_ae_eq_zero (hmeas t₀ ht₀) (hmeas t ht) ht₀ ht (hzero t ht)
    have haeeq : (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|) =ᵐ[μ] fun _ => (0 : ℝ) := by
      have hall : ∀ᵐ ω ∂μ, ∀ t ∈ T, |X t ω - X t₀ ω| = 0 := by
        rw [hfin.eventually_all]
        intro t ht
        filter_upwards [hae t ht] with ω hω
        have : X t ω - X t₀ ω = 0 := hω
        rw [this, abs_zero]
      filter_upwards [hall] with ω hω
      rw [← setToF (fun t => |X t ω - X t₀ ω|),
        biSup_finset_eq_sup' hFne _ (fun _ _ => abs_nonneg _)]
      apply le_antisymm
      · exact Finset.sup'_le hFne _ (fun t ht => le_of_eq (hω t (hmemT t ht)))
      · calc (0 : ℝ) = |X t₀ ω - X t₀ ω| := by rw [sub_self, abs_zero]
          _ ≤ _ := Finset.le_sup' (fun t => |X t ω - X t₀ ω|) (hfin.mem_toFinset.mpr ht₀)
    rw [integral_congr_ae haeeq, integral_zero]
    exact mul_nonneg (by positivity) (dudleySum_nonneg T)
  · -- Main case `diam T > 0`: re-anchored dyadic chaining in absolute value.
    obtain ⟨κ, hκ1, hκ2⟩ := exists_coarse_scale hDpos
    set ε : ℕ → ℝ := fun j => (2 : ℝ) ^ (-(κ + (j : ℤ))) with hεdef
    have hεval : ∀ j : ℕ, ε j = (2 : ℝ) ^ (-(κ + (j : ℤ))) := fun j => by rw [hεdef]
    have hεpos : ∀ j : ℕ, 0 < ε j := fun j => by rw [hεval]; exact zpow_pos (by norm_num) _
    have hεrec : ∀ j : ℕ, ε j = 2 * ε (j + 1) := by
      intro j
      rw [hεval, hεval,
        show (-(κ + ((j + 1 : ℕ) : ℤ))) = (-(κ + (j : ℤ))) - 1 by push_cast; ring,
        zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp only [zpow_one]; ring
    have hεle : ∀ j : ℕ, ε (j + 1) ≤ ε j := fun j => by
      rw [hεrec j]; linarith [hεpos (j + 1)]
    -- Dyadic nets at every scale.
    have hnet : ∀ j : ℕ, ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧
        (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε j) ∧ (N.card : ℕ∞) = coveringNumber T (ε j) :=
      fun j => exists_finset_net hfin hne (hεpos j)
    choose N hN using hnet
    have hprojT : ∀ i : ℕ, ∀ t : E, netProj (N i) t ∈ T :=
      fun i t => (hN i).1 (Finset.mem_coe.mpr (netProj_mem (hN i).2.1 t))
    have hproj : ∀ i : ℕ, ∀ t ∈ T, dist t (netProj (N i) t) ≤ ε i :=
      fun i t ht => dist_netProj_le ((hN i).2.2.1 t ht)
    -- Net cardinality equals the covering-number `toNat`.
    have hcardcov : ∀ j : ℕ, (N j).card = (coveringNumber T (ε j)).toNat := by
      intro j; have h := (hN j).2.2.2; rw [← h]; simp
    -- Coarse net (`j = 0`) has covering number `1`.
    have hcov1 : coveringNumber T (ε 0) = 1 := by
      apply coveringNumber_eq_one_of_diam_le hne hbd (le_of_lt (hεpos 0))
      rw [hεval]; push_cast; simpa using hκ1
    -- Fine scale where the finest net identifies with `T` a.e.
    obtain ⟨nf, hnf_pos, hfineScale⟩ := exists_fine_scale hfin κ
    -- **Re-anchoring**: `m` = the finest scale index (≤ nf) whose net is a singleton.
    set G : Finset ℕ := (Finset.range (nf + 1)).filter (fun j => coveringNumber T (ε j) = 1)
      with hGdef
    have h0G : (0 : ℕ) ∈ G := by
      rw [hGdef, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr (by omega), hcov1⟩
    have hGne : G.Nonempty := ⟨0, h0G⟩
    set m : ℕ := G.max' hGne with hmdef
    have hmG : m ∈ G := G.max'_mem hGne
    have hmcov1 : coveringNumber T (ε m) = 1 := (Finset.mem_filter.mp hmG).2
    have hmle : m ≤ nf := by
      have := (Finset.mem_filter.mp hmG).1; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
    -- Above `m` (but ≤ nf) the net has ≥ 2 points: since `m` is the finest 𝒩 = 1 scale.
    have hcov2 : ∀ j : ℕ, m < j → j ≤ nf → 2 ≤ (N j).card := by
      intro j hjm hjnf
      have hjne : coveringNumber T (ε j) ≠ 1 := by
        intro hj1
        have : j ∈ G := by
          rw [hGdef, Finset.mem_filter]
          exact ⟨Finset.mem_range.mpr (by omega), hj1⟩
        exact absurd (G.le_max' j this) (by omega)
      have hpos : 1 ≤ (N j).card := (hN j).2.1.card_pos
      rcases Nat.lt_or_ge (N j).card 2 with h2 | h2
      · exfalso; apply hjne
        have : (N j).card = 1 := by omega
        have hc := (hN j).2.2.2; rw [this] at hc; exact_mod_cast hc.symm
      · exact h2
    -- The single anchor point `c` at scale `m`.
    have hcard_m : (N m).card = 1 := by rw [hcardcov, hmcov1]; rfl
    obtain ⟨c, hc0⟩ := Finset.card_eq_one.mp hcard_m
    have hcT : c ∈ T := (hN m).1 (Finset.mem_coe.mpr (hc0 ▸ Finset.mem_singleton_self c))
    have hπm : ∀ t : E, netProj (N m) t = c := by
      intro t; rw [hc0]
      have hmem := netProj_mem (Finset.singleton_nonempty c) t
      rwa [Finset.mem_singleton] at hmem
    -- Fine identification: `π_{nf} t = t` a.e.
    have hfine0 : ∀ t ∈ T, dist t (netProj (N nf) t) = 0 := by
      intro t ht
      apply hfineScale t ht (netProj (N nf) t) (hprojT nf t)
      rw [← hεval nf]; exact hproj nf t ht
    have hclean : ∀ᵐ ω ∂μ, ∀ t ∈ T, X (netProj (N nf) t) ω = X t ω := by
      rw [hfin.eventually_all]
      intro t ht
      have hsub := hinc.sub_ae_eq_zero (hmeas t ht) (hmeas (netProj (N nf) t) (hprojT nf t))
        ht (hprojT nf t) (hfine0 t ht)
      filter_upwards [hsub] with ω hω
      have : X (netProj (N nf) t) ω - X t ω = 0 := hω
      linarith
    -- The number of chaining levels.
    set n : ℕ := nf - m with hndef
    have hmn : m + n = nf := by omega
    -- **Per-level abs suprema over close pairs** (window index `j`, scale `m+j`).
    set CP : ℕ → Finset (E × E) := fun j =>
      closePairs (N (m + j + 1)) (N (m + j)) (ε (m + j + 1) + ε (m + j)) with hCPdef
    set CPS : ℕ → Ω → ℝ := fun j ω =>
      ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| with hCPSdef
    have hCPne : ∀ j : ℕ, (CP j).Nonempty := fun j =>
      ⟨(netProj (N (m + j + 1)) hne.some, netProj (N (m + j)) hne.some),
        proj_pair_mem_closePairs
          (hproj (m + j + 1) hne.some hne.some_mem) (hproj (m + j) hne.some hne.some_mem)
          (hN (m + j + 1)).2.1 (hN (m + j)).2.1⟩
    have hCPmem : ∀ j : ℕ, ∀ p ∈ CP j, p.1 ∈ T ∧ p.2 ∈ T := by
      intro j p hp
      rw [hCPdef] at hp
      simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨(hN (m + j + 1)).1 (Finset.mem_coe.mpr hp.1.1),
        (hN (m + j)).1 (Finset.mem_coe.mpr hp.1.2)⟩
    -- ψ₂-norm control for every close pair at window level `j`, with scale `L j`.
    set Lj : ℕ → ℝ≥0 := fun j => K * Real.toNNReal (ε (m + j + 1) + ε (m + j)) with hLjdef
    have hSGpair : ∀ j : ℕ, ∀ p ∈ CP j,
        subGaussianNorm (fun ω => X p.1 ω - X p.2 ω) μ ≤ (Lj j : ℝ≥0∞) := by
      intro j p hp
      have hdle : dist p.1 p.2 ≤ ε (m + j + 1) + ε (m + j) := by
        rw [hCPdef] at hp
        simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.2
      have hrpos : 0 ≤ ε (m + j + 1) + ε (m + j) := by
        linarith [hεpos (m + j + 1), hεpos (m + j)]
      refine (hinc p.2 (hCPmem j p hp).2 p.1 (hCPmem j p hp).1).trans ?_
      have hde : edist p.2 p.1 ≤ (Real.toNNReal (ε (m + j + 1) + ε (m + j)) : ℝ≥0∞) := by
        rw [edist_dist, dist_comm]
        exact ENNReal.ofReal_le_ofReal hdle
      calc (K : ℝ≥0∞) * edist p.2 p.1
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (ε (m + j + 1) + ε (m + j)) : ℝ≥0∞) := by gcongr
        _ = (Lj j : ℝ≥0∞) := by rw [hLjdef]; push_cast; ring
    -- Integrability of the close-pair abs-suprema (via the ψ₂ tail).
    have hIntCPS : ∀ j : ℕ, MeasureTheory.Integrable (CPS j) μ := fun j =>
      integrable_biSup_abs (hCPne j)
        (fun p hp => ((hmeas _ (hCPmem j p hp).1).sub (hmeas _ (hCPmem j p hp).2)))
        (hSGpair j)
    -- **STEP A: anchored split** `|X_t − X_{t₀}| ≤ |X_t − X_c| + |X_c − X_{t₀}|`,
    -- and `E|X_c − X_{t₀}| ≤ √π·K·diam T`.
    set AS : Ω → ℝ := fun ω => ⨆ t ∈ F, |X t ω - X c ω| with hASdef
    have hASne : ∀ ω, ∀ t ∈ F, |X t ω - X c ω| ≤ AS ω := by
      intro ω t ht
      rw [hASdef]; simp only
      exact le_biSup_finset (fun s => |X s ω - X c ω|) ht
    have hIntAS : MeasureTheory.Integrable AS μ := by
      have hkey := integrable_biSup_sub (X := X) (K := K) (T := T) hfin hne hmeas hinc hcT
      rw [hASdef, show (fun ω => ⨆ t ∈ F, |X t ω - X c ω|)
            = (fun ω => ⨆ t ∈ T, |X t ω - X c ω|) from funext fun ω => setToF _]
      exact hkey
    -- ψ₂-norm of the anchor increment `X_c − X_{t₀}` (distance ≤ diam T).
    have hAnchorSG : subGaussianNorm (fun ω => X c ω - X t₀ ω) μ
        ≤ ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by
      refine (hinc t₀ ht₀ c hcT).trans ?_
      have hde : edist t₀ c ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd ht₀ hcT)
      calc (K : ℝ≥0∞) * edist t₀ c
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    have hAnchorInt : (∫ ω, |X c ω - X t₀ ω| ∂μ)
        ≤ Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T) := by
      have h := integral_abs_le_of_subGaussianNorm_le
        ((hmeas c hcT).sub (hmeas t₀ ht₀)) hAnchorSG
      refine h.trans (le_of_eq ?_)
      rw [NNReal.coe_mul, Real.coe_toNNReal _ Metric.diam_nonneg]
    -- Integrability of the anchor increment `|X_c − X_{t₀}|` (dominated by the
    -- integrable anchored abs-sup, since `c ∈ T`).
    have hIntAnchor : MeasureTheory.Integrable (fun ω => |X c ω - X t₀ ω|) μ := by
      refine hIntSup.mono' ((hmeas c hcT).sub (hmeas t₀ ht₀)).abs.aestronglyMeasurable ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_abs, ← setToF (fun t => |X t ω - X t₀ ω|)]
      exact le_biSup_finset (fun t => |X t ω - X t₀ ω|) (hfin.mem_toFinset.mpr hcT)
    -- **STEP B: split the anchored abs-sup along the chain plus the anchor.**
    have hB : (∫ ω, ⨆ t ∈ F, |X t ω - X t₀ ω| ∂μ)
        ≤ (∑ j ∈ Finset.range n, ∫ ω, CPS j ω ∂μ)
          + ∫ ω, |X c ω - X t₀ ω| ∂μ := by
      -- pointwise: `⨆_t |X_t − X_{t₀}| ≤ (∑_j CPS_j) + |X_c − X_{t₀}|` a.e.
      have hpt : ∀ᵐ ω ∂μ, (⨆ t ∈ F, |X t ω - X t₀ ω|)
          ≤ (∑ j ∈ Finset.range n, CPS j ω) + |X c ω - X t₀ ω| := by
        filter_upwards [hclean] with ω hω
        rw [biSup_finset_eq_sup' hFne _ (fun _ _ => abs_nonneg _)]
        refine Finset.sup'_le hFne _ (fun t ht => ?_)
        have htT := hmemT t ht
        -- telescope `X_t − X_c = ∑_{i<n} (X_{π_{m+i+1}t} − X_{π_{m+i}t})` a.e.
        have htel : X t ω - X c ω
            = ∑ i ∈ Finset.range n,
                (X (netProj (N (m + i + 1)) t) ω - X (netProj (N (m + i)) t) ω) := by
          have hshift : ∀ i : ℕ,
              (fun i => X (netProj (N (m + i)) t) ω) (i + 1)
                - (fun i => X (netProj (N (m + i)) t) ω) i
              = X (netProj (N (m + i + 1)) t) ω - X (netProj (N (m + i)) t) ω := by
            intro i; simp only; rw [show m + (i + 1) = m + i + 1 from by ring]
          have h0 : X (netProj (N (m + 0)) t) ω = X c ω := by
            rw [show m + 0 = m from by ring, hπm t]
          have hnn : X (netProj (N (m + n)) t) ω = X t ω := by
            rw [hmn]; exact hω t htT
          have := chain_telescope (n := n) (fun i => X (netProj (N (m + i)) t) ω)
          rw [show m + n = m + n from rfl] at this
          rw [hnn, h0] at this
          rw [this]
          exact Finset.sum_congr rfl (fun i _ => hshift i)
        -- each telescope term ≤ its abs ≤ CPS
        have hbound : |X t ω - X c ω| ≤ ∑ i ∈ Finset.range n, CPS i ω := by
          rw [htel]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hmem : (netProj (N (m + i + 1)) t, netProj (N (m + i)) t) ∈ CP i :=
            proj_pair_mem_closePairs (hproj (m + i + 1) t htT) (hproj (m + i) t htT)
              (hN (m + i + 1)).2.1 (hN (m + i)).2.1
          rw [hCPSdef]; simp only
          exact le_biSup_finset (fun p => |X p.1 ω - X p.2 ω|) hmem
        calc |X t ω - X t₀ ω|
            ≤ |X t ω - X c ω| + |X c ω - X t₀ ω| := by
              rw [show X t ω - X t₀ ω = (X t ω - X c ω) + (X c ω - X t₀ ω) from by ring]
              exact abs_add_le _ _
          _ ≤ (∑ i ∈ Finset.range n, CPS i ω) + |X c ω - X t₀ ω| := by
              linarith [hbound]
      have hIntRHS : MeasureTheory.Integrable
          (fun ω => (∑ j ∈ Finset.range n, CPS j ω) + |X c ω - X t₀ ω|) μ :=
        (integrable_finset_sum _ (fun j _ => hIntCPS j)).add hIntAnchor
      calc (∫ ω, ⨆ t ∈ F, |X t ω - X t₀ ω| ∂μ)
          ≤ ∫ ω, (∑ j ∈ Finset.range n, CPS j ω) + |X c ω - X t₀ ω| ∂μ :=
            integral_mono_ae hIntSupF hIntRHS hpt
        _ = (∑ j ∈ Finset.range n, ∫ ω, CPS j ω ∂μ) + ∫ ω, |X c ω - X t₀ ω| ∂μ := by
            rw [integral_add (integrable_finset_sum _ (fun j _ => hIntCPS j)) hIntAnchor,
              integral_finset_sum _ (fun j _ => hIntCPS j)]
    -- **STEP C: per-level bound** `E[CPS_j] ≤ 6√3·K·dudleySummand(κ+m+1+j)`.
    have hC : ∀ j ∈ Finset.range n,
        (∫ ω, CPS j ω ∂μ) ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)) := by
      intro j hj
      have hjrange : j < n := Finset.mem_range.mp hj
      set r : ℝ := ε (m + j + 1) + ε (m + j) with hrdef
      have hrpos : 0 < r := by rw [hrdef]; linarith [hεpos (m + j + 1), hεpos (m + j)]
      have hr3 : r = 3 * ε (m + j + 1) := by rw [hrdef, hεrec (m + j)]; ring
      -- net card at scale `m+j+1` is ≥ 2 (re-anchoring pays off).
      have hNcard2 : 2 ≤ (N (m + j + 1)).card := hcov2 (m + j + 1) (by omega) (by omega)
      set Mnat : ℕ := (N (m + j + 1)).card with hMnatdef
      set M : ℝ := (Mnat : ℝ) with hMdef
      have hM2 : (2 : ℝ) ≤ M := by rw [hMdef, hMnatdef]; exact_mod_cast hNcard2
      have hM1nat : 0 < Mnat := by omega
      have hcardCPnat : (CP j).card ≤ Mnat ^ 2 := by
        have hNjle : (N (m + j)).card ≤ (N (m + j + 1)).card := by
          have h1 := (hN (m + j)).2.2.2
          have h2 := (hN (m + j + 1)).2.2.2
          have hanti : coveringNumber T (ε (m + j)) ≤ coveringNumber T (ε (m + j + 1)) :=
            coveringNumber_anti (hεle (m + j))
          rw [← h1, ← h2] at hanti
          exact_mod_cast hanti
        calc (CP j).card ≤ (N (m + j + 1)).card * (N (m + j)).card := card_closePairs_le _ _ _
          _ ≤ (N (m + j + 1)).card * (N (m + j + 1)).card := by gcongr
          _ = Mnat ^ 2 := by rw [hMnatdef, sq]
      -- `sqrtLogCov` identity at scale `m+j+1`.
      have hslc : sqrtLogCov T (ε (m + j + 1)) = Real.sqrt (Real.log M) := by
        unfold sqrtLogCov; rw [← hcardcov (m + j + 1), hMdef, hMnatdef]
      have hlogM_pos : 0 < Real.log M := Real.log_pos (by linarith)
      -- `√(log(2·card CP)) ≤ √3·sqrtLogCov`
      have hstep : Real.sqrt (Real.log (2 * ((CP j).card : ℝ)))
          ≤ Real.sqrt 3 * sqrtLogCov T (ε (m + j + 1)) := by
        rw [hslc, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
        apply Real.sqrt_le_sqrt
        -- log(2·card) ≤ log(2 M²) ≤ log(M³) = 3 log M
        have hcard_le : (2 : ℝ) * ((CP j).card : ℝ) ≤ M ^ 3 := by
          have h1 : ((CP j).card : ℝ) ≤ M ^ 2 := by
            rw [hMdef]; exact_mod_cast hcardCPnat
          have h2 : (2 : ℝ) * M ^ 2 ≤ M ^ 3 := by nlinarith [hM2, sq_nonneg M]
          nlinarith [h1, hM2]
        have hposc : (0 : ℝ) < 2 * ((CP j).card : ℝ) := by
          have hc : 0 < (CP j).card := (hCPne j).card_pos
          have : (0 : ℝ) < ((CP j).card : ℝ) := by exact_mod_cast hc
          linarith
        have hlog := Real.log_le_log hposc hcard_le
        rw [show M ^ 3 = M ^ (3 : ℕ) from rfl, Real.log_pow] at hlog
        push_cast at hlog; linarith
      -- dyadic summand identity at the shifted index.
      have hdud : dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))
          = ε (m + j + 1) * sqrtLogCov T (ε (m + j + 1)) := by
        have hkk : (-(κ + (m : ℤ) + 1 + (j : ℤ))) = (-(κ + ((m + j + 1 : ℕ) : ℤ))) := by
          push_cast; ring
        simp only [dudleySummand]
        rw [hkk, hεval (m + j + 1)]
      -- assemble via `expectation_abs_max_le`.
      have hLjpos : 0 < Lj j := by
        rw [hLjdef]
        have hrpos' : 0 < Real.toNNReal r := Real.toNNReal_pos.mpr hrpos
        exact mul_pos hKpos hrpos'
      have hExp : (∫ ω, CPS j ω ∂μ)
          ≤ 2 * (Lj j : ℝ) * Real.sqrt (Real.log (2 * (CP j).card)) := by
        rw [hCPSdef]
        exact expectation_abs_max_le (hCPne j) hLjpos
          (fun p hp => ((hmeas _ (hCPmem j p hp).1).sub (hmeas _ (hCPmem j p hp).2)))
          (hSGpair j)
      refine hExp.trans ?_
      have hLjval : (Lj j : ℝ) = (K : ℝ) * r := by
        rw [hLjdef, NNReal.coe_mul, Real.coe_toNNReal _ hrpos.le, hrdef]
      rw [hLjval, hdud]
      calc 2 * ((K : ℝ) * r) * Real.sqrt (Real.log (2 * (CP j).card))
          ≤ 2 * ((K : ℝ) * r) * (Real.sqrt 3 * sqrtLogCov T (ε (m + j + 1))) := by
            apply mul_le_mul_of_nonneg_left hstep
            positivity
        _ = 6 * Real.sqrt 3 * K * (ε (m + j + 1) * sqrtLogCov T (ε (m + j + 1))) := by
            rw [hr3]; ring
    -- **WINDOW SUM**: the chaining levels sum below the full dyadic entropy sum.
    have hwin : ∑ j ∈ Finset.range n, dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))
        ≤ dudleySum T := by
      have hemb : Function.Injective (fun j : ℕ => κ + (m : ℤ) + 1 + (j : ℤ)) := by
        intro a b hab; simp only at hab; omega
      rw [show (∑ j ∈ Finset.range n, dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
            = ∑ k ∈ (Finset.range n).map ⟨fun j : ℕ => κ + (m : ℤ) + 1 + (j : ℤ), hemb⟩,
                dudleySummand T k
          from by rw [Finset.sum_map]; rfl]
      exact sum_window_le_dudleySum hfin hne _
    -- **ANCHOR ABSORPTION**: `√π·K·diam T ≤ (4√π/√log2)·K·dudleySum ≤ (20 − 6√3)·K·dudleySum`.
    have hlog2pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
    have hAnchorAbsorb : Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T)
        ≤ (20 - 6 * Real.sqrt 3) * K * dudleySum T := by
      have hdiam := diam_mul_sqrt_log_two_le_four_mul_dudleySum hfin hne
      -- `diam T = (diam·√log2)/√log2 ≤ 4·dudleySum/√log2`.
      have hdiam' : Metric.diam T ≤ 4 * dudleySum T / Real.sqrt (Real.log 2) := by
        rw [le_div_iff₀ hlog2pos]; linarith [hdiam]
      have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
      have hds : 0 ≤ dudleySum T := dudleySum_nonneg T
      -- √π · K · diam ≤ √π · K · (4 dudleySum / √log2)
      have hstep1 : Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T)
          ≤ Real.sqrt Real.pi * ((K : ℝ) * (4 * dudleySum T / Real.sqrt (Real.log 2))) := by
        gcongr
      refine hstep1.trans ?_
      -- reduce to the scalar inequality `4√π/√log2 ≤ 20 − 6√3`.
      have hconst : Real.sqrt Real.pi * (4 / Real.sqrt (Real.log 2))
          ≤ 20 - 6 * Real.sqrt 3 := by
        -- `4√π/√log2 ≈ 8.52`, `20 − 6√3 ≈ 9.61`.
        have hpi : Real.sqrt Real.pi ≤ 1.773 := by
          rw [show (1.773 : ℝ) = Real.sqrt (1.773 ^ 2) from
            (Real.sqrt_sq (by norm_num)).symm]
          apply Real.sqrt_le_sqrt
          nlinarith [Real.pi_lt_d4]
        have hlog2 : 0.693 ≤ Real.log 2 := by
          have := Real.log_two_gt_d9; linarith
        have hslog2 : 0.832 ≤ Real.sqrt (Real.log 2) := by
          rw [show (0.832 : ℝ) = Real.sqrt (0.832 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          apply Real.sqrt_le_sqrt; nlinarith [hlog2]
        have hsqrt3 : Real.sqrt 3 ≤ 1.7321 := by
          rw [show (1.7321 : ℝ) = Real.sqrt (1.7321 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
          apply Real.sqrt_le_sqrt; norm_num
        have hslog2pos : (0 : ℝ) < 0.832 := by norm_num
        have hdivle : (4 : ℝ) / Real.sqrt (Real.log 2) ≤ 4 / 0.832 :=
          div_le_div_of_nonneg_left (by norm_num) hslog2pos hslog2
        have hpinn : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
        calc Real.sqrt Real.pi * (4 / Real.sqrt (Real.log 2))
            ≤ 1.773 * (4 / 0.832) := by
              apply mul_le_mul hpi hdivle (by positivity) (by norm_num)
          _ ≤ 20 - 6 * Real.sqrt 3 := by nlinarith [hsqrt3]
      calc Real.sqrt Real.pi * ((K : ℝ) * (4 * dudleySum T / Real.sqrt (Real.log 2)))
          = (Real.sqrt Real.pi * (4 / Real.sqrt (Real.log 2))) * ((K : ℝ) * dudleySum T) := by
            ring
        _ ≤ (20 - 6 * Real.sqrt 3) * ((K : ℝ) * dudleySum T) := by
            apply mul_le_mul_of_nonneg_right hconst
            exact mul_nonneg hKnn hds
        _ = (20 - 6 * Real.sqrt 3) * K * dudleySum T := by ring
    -- **COMBINE.**
    rw [show (fun ω => ⨆ t ∈ T, |X t ω - X t₀ ω|)
        = (fun ω => ⨆ t ∈ F, |X t ω - X t₀ ω|) from funext fun ω => (setToF _).symm]
    calc (∫ ω, ⨆ t ∈ F, |X t ω - X t₀ ω| ∂μ)
        ≤ (∑ j ∈ Finset.range n, ∫ ω, CPS j ω ∂μ) + ∫ ω, |X c ω - X t₀ ω| ∂μ := hB
      _ ≤ (∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * K * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
            + Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T) := by
          apply add_le_add (Finset.sum_le_sum hC) hAnchorInt
      _ ≤ 6 * Real.sqrt 3 * K * dudleySum T
            + (20 - 6 * Real.sqrt 3) * K * dudleySum T := by
          apply add_le_add _ hAnchorAbsorb
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left hwin (by positivity)
      _ = 20 * K * dudleySum T := by ring

/-! ### Faithful general forms (arbitrary `T`; HDP Remark 7.2.1)

HDP states Theorem 8.1.4 for a process on a general metric space `(T, d)`,
reading `E sup_{t∈T} X_t` per Remark 7.2.1 (p. 199) as the supremum over all
finite subsets `T₀ ⊆ T` of `E max_{t∈T₀} X_t`. The faithful Lean statements
therefore quantify over a finite subset `F ⊆ T` while measuring the entropy
on the FULL `T`; finiteness of `T` is replaced by finiteness of the covering
numbers (`hcov`, the totally-bounded package), and the RHS is carried in
`ℝ≥0∞` (`dudleyLSum`) so that a divergent entropy series is an honest `⊤`
(the real `dudleySum` tsum would junk to `0`). The chain runs through nets
of `T` and is truncated at an arbitrary level; the truncation residual over
the fixed finite `F` vanishes (`SubsetChaining.residual_expectation_le`),
replacing the finite-`T` fine-scale stop of `discrete_dudley_of_finite`. -/

/-- **Discrete Dudley inequality** (HDP §8.1, Theorem 8.1.4, Eq. (8.2);
faithful general-`T` form): for every finite subset `F ⊆ T`,
`E max_{t∈F} X_t ≤ 6√3 · K · dudleyLSum T` — the Remark 7.2.1 reading of
`E sup_{t∈T} X_t ≤ CK Σ_k 2^{−k}√(log 𝒩(T,d,2^{−k}))`, with `C` frozen to
`6√3` exactly as in the finite form. -/
theorem discrete_dudley {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: finite covering numbers at all positive radii (the
    -- totally-bounded package; junk-guard for `sqrtLogCov`); HDP §8.1
    (hcov : ∀ ε : ℝ, 0 < ε → coveringNumber T ε ≠ ⊤)
    -- LEAN-ONLY: nonemptiness of the carrier
    (hne : T.Nonempty)
    -- LEAN-ONLY: a.e.-measurability of the coordinates (Orlicz bridges)
    (hmeas : ∀ t ∈ T, AEMeasurable (X t) μ)
    -- LEAN-ONLY: rules out Bochner-junk means; increment means then derive
    (hint : ∀ t ∈ T, MeasureTheory.Integrable (X t) μ)
    -- USER-INPUT: mean-zero coordinates; HDP §8.1, Theorem 8.1.4
    (hmean : ∀ t ∈ T, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Def 8.1.1
    (hinc : SubGaussianIncrements X K T μ)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
      ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
  classical
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hF (Finset.mem_coe.mpr ht)
  set c₀ := hne.some with hc₀def
  have hc₀T : c₀ ∈ T := hne.some_mem
  -- Common degenerate conclusion: if all coordinates equal `X c₀` a.e., the
  -- integral is `0` (`≤` anything).
  have hdegen : (∀ t ∈ T, (fun ω => X t ω - X c₀ ω) =ᵐ[μ] 0) →
      ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
        ≤ ENNReal.ofReal (6 * Real.sqrt 3) * K * dudleyLSum T := by
    intro hae
    have haeeq : (fun ω => F.sup' hFne (fun t => X t ω)) =ᵐ[μ] fun ω => X c₀ ω := by
      have hall : ∀ᵐ ω ∂μ, ∀ t ∈ F, X t ω = X c₀ ω := by
        rw [F.eventually_all]
        intro t ht
        filter_upwards [hae t (hmemT t ht)] with ω hω
        have : X t ω - X c₀ ω = 0 := hω
        linarith
      filter_upwards [hall] with ω hω
      apply le_antisymm
      · exact Finset.sup'_le hFne _ (fun t ht => le_of_eq (hω t ht))
      · have h1 : X c₀ ω = X hFne.choose ω := (hω hFne.choose hFne.choose_spec).symm
        rw [h1]; exact Finset.le_sup' (fun t => X t ω) hFne.choose_spec
    have hz : (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ) = 0 := by
      rw [integral_congr_ae haeeq]; exact hmean c₀ hc₀T
    rw [hz, ENNReal.ofReal_zero]; exact zero_le
  -- Degenerate `K = 0`: every increment vanishes a.e.
  rcases eq_or_lt_of_le (zero_le (a := K)) with hK0 | hKpos
  · apply hdegen
    intro t ht
    have hle : subGaussianNorm (fun ω => X t ω - X c₀ ω) μ ≤ 0 := by
      refine (hinc c₀ hc₀T t ht).trans ?_
      rw [← hK0]; simp
    exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas c₀ hc₀T))
      (le_antisymm hle (by positivity))
  -- Degenerate `diam T = 0`: all coordinates coincide a.e.
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hD0 | hDpos
  · apply hdegen
    intro t ht
    have hzero : dist c₀ t = 0 := by
      have hle := Metric.dist_le_diam_of_mem hbd hc₀T ht
      rw [← hD0] at hle; exact le_antisymm hle dist_nonneg
    exact hinc.sub_ae_eq_zero (hmeas c₀ hc₀T) (hmeas t ht) hc₀T ht hzero
  · -- Main case `diam T > 0`: dyadic chaining, truncated + residual → limit.
    obtain ⟨κ, hκ1, hκ2⟩ := exists_coarse_scale hDpos
    set ε : ℕ → ℝ := fun j => (2 : ℝ) ^ (-(κ + (j : ℤ))) with hεdef
    have hεval : ∀ j : ℕ, ε j = (2 : ℝ) ^ (-(κ + (j : ℤ))) := fun j => by rw [hεdef]
    have hεpos : ∀ j : ℕ, 0 < ε j := fun j => by rw [hεval]; exact zpow_pos (by norm_num) _
    have hεrec : ∀ j : ℕ, ε j = 2 * ε (j + 1) := by
      intro j
      rw [hεval, hεval,
        show (-(κ + ((j + 1 : ℕ) : ℤ))) = (-(κ + (j : ℤ))) - 1 by push_cast; ring,
        zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp only [zpow_one]; ring
    have hεle : ∀ j : ℕ, ε (j + 1) ≤ ε j := fun j => by
      rw [hεrec j]; linarith [hεpos (j + 1)]
    -- Dyadic nets of the carrier at every scale (via `hcov`).
    have hnet : ∀ j : ℕ, ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧
        (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε j) ∧ (N.card : ℕ∞) = coveringNumber T (ε j) :=
      fun j => exists_finset_net_of_cov_ne_top (hcov (ε j) (hεpos j)) hne (hεpos j)
    choose N hN using hnet
    have hprojT : ∀ i : ℕ, ∀ t : E, netProj (N i) t ∈ T :=
      fun i t => (hN i).1 (Finset.mem_coe.mpr (netProj_mem (hN i).2.1 t))
    have hproj : ∀ i : ℕ, ∀ t ∈ T, dist t (netProj (N i) t) ≤ ε i :=
      fun i t ht => dist_netProj_le ((hN i).2.2.1 t ht)
    have ht' : hne.some ∈ T := hne.some_mem
    -- Coarse net is a singleton; its point `c` anchors the chain.
    have hcov1 : coveringNumber T (ε 0) = 1 := by
      apply coveringNumber_eq_one_of_diam_le hne hbd (le_of_lt (hεpos 0))
      rw [hεval]; push_cast; simpa using hκ1
    have hcard0 : (N 0).card = 1 := by
      have h := (hN 0).2.2.2; rw [hcov1] at h; exact_mod_cast h
    obtain ⟨c, hc0⟩ := Finset.card_eq_one.mp hcard0
    have hcT : c ∈ T := (hN 0).1 (Finset.mem_coe.mpr (hc0 ▸ Finset.mem_singleton_self c))
    have hπ0 : ∀ t : E, netProj (N 0) t = c := by
      intro t
      rw [hc0]
      have hmem := netProj_mem (Finset.singleton_nonempty c) t
      rwa [Finset.mem_singleton] at hmem
    -- Per-level suprema over `F` and close-pair suprema over the nets.
    set S : ℕ → Ω → ℝ := fun j ω =>
      F.sup' hFne (fun t => X (netProj (N (j + 1)) t) ω - X (netProj (N j) t) ω) with hSdef
    set CP : ℕ → Finset (E × E) := fun j =>
      closePairs (N (j + 1)) (N j) (ε (j + 1) + ε j) with hCPdef
    have hCPne : ∀ j : ℕ, (CP j).Nonempty := fun j =>
      ⟨(netProj (N (j + 1)) hne.some, netProj (N j) hne.some),
        proj_pair_mem_closePairs (hproj (j + 1) hne.some ht') (hproj j hne.some ht')
          (hN (j + 1)).2.1 (hN j).2.1⟩
    set CPS : ℕ → Ω → ℝ := fun j ω =>
      (CP j).sup' (hCPne j) (fun p => X p.1 ω - X p.2 ω) with hCPSdef
    have hCPmem : ∀ j : ℕ, ∀ p ∈ CP j, p.1 ∈ T ∧ p.2 ∈ T := by
      intro j p hp
      rw [hCPdef] at hp
      simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨(hN (j + 1)).1 (Finset.mem_coe.mpr hp.1.1), (hN j).1 (Finset.mem_coe.mpr hp.1.2)⟩
    have hIntS : ∀ j : ℕ, MeasureTheory.Integrable (S j) μ := fun j =>
      integrable_sup'_finset hFne fun t ht =>
        (hint _ (hprojT (j + 1) t)).sub (hint _ (hprojT j t))
    have hIntCPS : ∀ j : ℕ, MeasureTheory.Integrable (CPS j) μ := fun j =>
      integrable_sup'_finset (hCPne j) fun p hp =>
        (hint _ (hCPmem j p hp).1).sub (hint _ (hCPmem j p hp).2)
    have hIntSupX : MeasureTheory.Integrable (fun ω => F.sup' hFne (fun t => X t ω)) μ :=
      integrable_sup'_finset hFne fun t ht => hint t (hmemT t ht)
    have hIntSupA : MeasureTheory.Integrable
        (fun ω => F.sup' hFne (fun t => X t ω - X c ω)) μ :=
      integrable_sup'_finset hFne fun t ht => (hint t (hmemT t ht)).sub (hint c hcT)
    have term_le_S : ∀ j : ℕ, ∀ t ∈ F, ∀ ω,
        (X (netProj (N (j + 1)) t) ω - X (netProj (N j) t) ω) ≤ S j ω := by
      intro j t ht ω
      rw [hSdef]; simp only
      exact Finset.le_sup'
        (fun s => X (netProj (N (j + 1)) s) ω - X (netProj (N j) s) ω) ht
    -- STEP A: mean-zero anchoring at `c`.
    have hstepA : (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
        ≤ ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ := by
      have hpt : ∀ ω, F.sup' hFne (fun t => X t ω)
          ≤ X c ω + F.sup' hFne (fun t => X t ω - X c ω) := by
        intro ω
        refine Finset.sup'_le hFne _ (fun t ht => ?_)
        have hle : (X t ω - X c ω) ≤ F.sup' hFne (fun s => X s ω - X c ω) :=
          Finset.le_sup' (fun s => X s ω - X c ω) ht
        linarith
      calc (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
          ≤ ∫ ω, (X c ω + F.sup' hFne (fun t => X t ω - X c ω)) ∂μ :=
            integral_mono_ae hIntSupX ((hint c hcT).add hIntSupA) (ae_of_all _ hpt)
        _ = (∫ ω, X c ω ∂μ) + ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ :=
            integral_add (hint c hcT) hIntSupA
        _ = ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ := by rw [hmean c hcT, zero_add]
    -- STEP B1: truncated telescope + residual, per level `n`.
    have hB1n : ∀ n : ℕ, (∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ)
        ≤ (∑ j ∈ Finset.range n, ∫ ω, S j ω ∂μ)
          + ∫ ω, F.sup' hFne (fun t => X t ω - X (netProj (N n) t) ω) ∂μ := by
      intro n
      set R : Ω → ℝ := fun ω => F.sup' hFne (fun t => X t ω - X (netProj (N n) t) ω) with hRdef
      have hIntR : MeasureTheory.Integrable R μ := integrable_sup'_finset hFne
        (fun t ht => (hint t (hmemT t ht)).sub (hint _ (hprojT n t)))
      have hpt : ∀ ω, F.sup' hFne (fun t => X t ω - X c ω)
          ≤ (∑ j ∈ Finset.range n, S j ω) + R ω := by
        intro ω
        refine Finset.sup'_le hFne _ (fun t ht => ?_)
        have htT := hmemT t ht
        have htel : X t ω - X c ω
            = (∑ i ∈ Finset.range n,
                (X (netProj (N (i + 1)) t) ω - X (netProj (N i) t) ω))
              + (X t ω - X (netProj (N n) t) ω) := by
          have h0 : X (netProj (N 0) t) ω = X c ω := by rw [hπ0 t]
          have htele := chain_telescope (n := n) (fun i => X (netProj (N i) t) ω)
          rw [h0] at htele
          linarith [htele]
        rw [htel]
        have hsum_le :
            (∑ i ∈ Finset.range n, (X (netProj (N (i + 1)) t) ω - X (netProj (N i) t) ω))
              ≤ ∑ i ∈ Finset.range n, S i ω :=
          Finset.sum_le_sum (fun i _ => term_le_S i t ht ω)
        have hR_le : X t ω - X (netProj (N n) t) ω ≤ R ω := by
          rw [hRdef]; exact Finset.le_sup' (fun s => X s ω - X (netProj (N n) s) ω) ht
        linarith
      calc (∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ)
          ≤ ∫ ω, ((∑ j ∈ Finset.range n, S j ω) + R ω) ∂μ :=
            integral_mono_ae hIntSupA
              ((integrable_finset_sum _ (fun j _ => hIntS j)).add hIntR) (ae_of_all _ hpt)
        _ = (∑ j ∈ Finset.range n, ∫ ω, S j ω ∂μ) + ∫ ω, R ω ∂μ := by
            rw [integral_add (integrable_finset_sum _ (fun j _ => hIntS j)) hIntR,
              integral_finset_sum _ (fun j _ => hIntS j)]
    -- STEP B2: per-level bound (identical to the finite proof's machinery).
    have hB2 : ∀ j : ℕ,
        (∫ ω, S j ω ∂μ) ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) := by
      intro j
      set r : ℝ := ε (j + 1) + ε j with hrdef
      have hrpos : 0 < r := by rw [hrdef]; linarith [hεpos (j + 1), hεpos j]
      have hr3 : r = 3 * ε (j + 1) := by rw [hrdef, hεrec j]; ring
      set σ2 : ℝ≥0 := 3 * (K * Real.toNNReal r) ^ 2 with hσ2def
      have hcenter : ∀ p ∈ CP j, ∫ ω, (X p.1 ω - X p.2 ω) ∂μ = 0 := by
        intro p hp
        rw [integral_sub (hint _ (hCPmem j p hp).1) (hint _ (hCPmem j p hp).2),
          hmean _ (hCPmem j p hp).1, hmean _ (hCPmem j p hp).2, sub_zero]
      have hSG : ∀ p ∈ CP j, IsSubGaussian (fun ω => X p.1 ω - X p.2 ω) σ2 μ := by
        intro p hp
        have hdle : dist p.1 p.2 ≤ r := by
          rw [hCPdef] at hp
          simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
          exact hp.2
        refine isSubGaussian_mono
          (hinc.isSubGaussian_sub (hmeas _ (hCPmem j p hp).2) (hmeas _ (hCPmem j p hp).1)
            (hCPmem j p hp).2 (hCPmem j p hp).1 (hcenter p hp)) ?_
        rw [hσ2def]
        have hnn : nndist p.2 p.1 ≤ Real.toNNReal r := by
          rw [nndist_dist, dist_comm]; exact Real.toNNReal_le_toNNReal hdle
        gcongr
      set Mnat : ℕ := (N (j + 1)).card with hMnatdef
      set M : ℝ := (Mnat : ℝ) with hMdef
      have hNjle : (N j).card ≤ (N (j + 1)).card := by
        have h1 := (hN j).2.2.2
        have h2 := (hN (j + 1)).2.2.2
        have hanti : coveringNumber T (ε j) ≤ coveringNumber T (ε (j + 1)) :=
          coveringNumber_anti (hεle j)
        rw [← h1, ← h2] at hanti
        exact_mod_cast hanti
      have hcardCPnat : (CP j).card ≤ Mnat ^ 2 := by
        calc (CP j).card ≤ (N (j + 1)).card * (N j).card := card_closePairs_le _ _ _
          _ ≤ (N (j + 1)).card * (N (j + 1)).card := by gcongr
          _ = Mnat ^ 2 := by rw [hMnatdef, sq]
      have hcard1nat : 0 < (CP j).card := Finset.card_pos.mpr (hCPne j)
      have hM1nat : 0 < Mnat := Finset.card_pos.mpr (hN (j + 1)).2.1
      have hcardCP : ((CP j).card : ℝ) ≤ M ^ 2 := by rw [hMdef]; exact_mod_cast hcardCPnat
      have hcov : (coveringNumber T (ε (j + 1))).toNat = (N (j + 1)).card := by
        have h := (hN (j + 1)).2.2.2; rw [← h]; simp
      have hslc : sqrtLogCov T (ε (j + 1)) = Real.sqrt (Real.log M) := by
        unfold sqrtLogCov; rw [hcov, hMdef, hMnatdef]
      have hsqrtσ : Real.sqrt (σ2 : ℝ) = Real.sqrt 3 * ((K : ℝ) * r) := by
        have hcoe : ((σ2 : ℝ≥0) : ℝ) = 3 * ((K : ℝ) * r) ^ 2 := by
          rw [hσ2def]; push_cast [Real.coe_toNNReal r hrpos.le]; ring
        rw [hcoe, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_sq (mul_nonneg (NNReal.coe_nonneg K) hrpos.le)]
      have hstep : Real.sqrt (2 * Real.log ((CP j).card : ℝ))
          ≤ 2 * sqrtLogCov T (ε (j + 1)) := by
        have hR : 2 * sqrtLogCov T (ε (j + 1)) = Real.sqrt (4 * Real.log M) := by
          rw [hslc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt 4 = 2 from by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        rw [hR]
        apply Real.sqrt_le_sqrt
        have hlogcard : Real.log ((CP j).card : ℝ) ≤ 2 * Real.log M := by
          have hpos : (0 : ℝ) < ((CP j).card : ℝ) := by exact_mod_cast hcard1nat
          have h := Real.log_le_log hpos hcardCP
          rw [Real.log_pow] at h; push_cast at h; linarith
        linarith
      have hdud : dudleySummand T (κ + 1 + (j : ℤ))
          = ε (j + 1) * sqrtLogCov T (ε (j + 1)) := by
        have hkk : (-(κ + 1 + (j : ℤ))) = (-(κ + ((j + 1 : ℕ) : ℤ))) := by push_cast; ring
        simp only [dudleySummand]
        rw [hkk, hεval (j + 1)]
      calc (∫ ω, S j ω ∂μ)
          ≤ ∫ ω, CPS j ω ∂μ := by
            refine integral_mono_ae (hIntS j) (hIntCPS j) (ae_of_all _ (fun ω => ?_))
            rw [hSdef, hCPSdef]; simp only
            refine Finset.sup'_le hFne _ (fun t ht => ?_)
            have htT := hmemT t ht
            exact Finset.le_sup' (fun p => X p.1 ω - X p.2 ω)
              (proj_pair_mem_closePairs (hproj (j + 1) t htT) (hproj j t htT)
                (hN (j + 1)).2.1 (hN j).2.1)
        _ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log (CP j).card) := by
            rw [hCPSdef]; simp only
            exact expectation_max_finset_le (hCPne j) hcenter hSG
        _ ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + 1 + (j : ℤ)) := by
            rw [hsqrtσ, hdud]
            calc Real.sqrt 3 * ((K : ℝ) * r) * Real.sqrt (2 * Real.log (CP j).card)
                ≤ Real.sqrt 3 * ((K : ℝ) * r) * (2 * sqrtLogCov T (ε (j + 1))) := by
                  apply mul_le_mul_of_nonneg_left hstep
                  exact mul_nonneg (Real.sqrt_nonneg 3)
                    (mul_nonneg (NNReal.coe_nonneg K) hrpos.le)
              _ = 6 * Real.sqrt 3 * K * (ε (j + 1) * sqrtLogCov T (ε (j + 1))) := by
                  rw [hr3]; ring
    -- Residual bound at truncation level `n`.
    set B : ℕ → ℝ := fun n =>
      Real.sqrt 3 * ((K : ℝ) * ε n) * Real.sqrt (2 * Real.log (F.card : ℝ)) with hBdef
    have hBnn : ∀ n : ℕ, 0 ≤ B n := fun n => by
      rw [hBdef]; simp only
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg K.coe_nonneg (hεpos n).le)) (Real.sqrt_nonneg _)
    have hres : ∀ n : ℕ,
        (∫ ω, F.sup' hFne (fun t => X t ω - X (netProj (N n) t) ω) ∂μ) ≤ B n := by
      intro n
      rw [hBdef]; simp only
      exact residual_expectation_le hmeas hint hmean hinc (hN n).1 (hN n).2.1
        (hεpos n).le (hN n).2.2.1 hF hFne
    -- ℝ≥0∞ window bound.
    have hwinL : ∀ n : ℕ,
        (∑ j ∈ Finset.range n, ENNReal.ofReal (dudleySummand T (κ + 1 + (j : ℤ))))
          ≤ dudleyLSum T := by
      intro n
      have hemb : Function.Injective (fun j : ℕ => κ + 1 + (j : ℤ)) := by
        intro a b hab; simp only at hab; omega
      rw [show (∑ j ∈ Finset.range n, ENNReal.ofReal (dudleySummand T (κ + 1 + (j : ℤ))))
            = ∑ k ∈ (Finset.range n).map ⟨fun j : ℕ => κ + 1 + (j : ℤ), hemb⟩,
                ENNReal.ofReal (dudleySummand T k)
          from by rw [Finset.sum_map]; rfl]
      exact sum_window_le_dudleyLSum _
    -- `ofReal` of the chaining partial sum is below the RHS.
    have hAle : ∀ n : ℕ,
        ENNReal.ofReal
            (∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + 1 + (j : ℤ)))
          ≤ ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T := by
      intro n
      have hterm : ∀ j : ℕ,
          ENNReal.ofReal (6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + 1 + (j : ℤ)))
            = ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞)
                * ENNReal.ofReal (dudleySummand T (κ + 1 + (j : ℤ))) := by
        intro j
        rw [mul_assoc (6 * Real.sqrt 3) (K : ℝ), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
      calc ENNReal.ofReal
              (∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * (K : ℝ)
                  * dudleySummand T (κ + 1 + (j : ℤ)))
          = ∑ j ∈ Finset.range n,
              ENNReal.ofReal (6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + 1 + (j : ℤ))) :=
            ENNReal.ofReal_sum_of_nonneg
              (fun j _ => mul_nonneg (by positivity) (dudleySummand_nonneg T _))
        _ = ∑ j ∈ Finset.range n,
              ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞)
                * ENNReal.ofReal (dudleySummand T (κ + 1 + (j : ℤ))) :=
            Finset.sum_congr rfl (fun j _ => hterm j)
        _ = ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞)
              * ∑ j ∈ Finset.range n, ENNReal.ofReal (dudleySummand T (κ + 1 + (j : ℤ))) := by
            rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T := by
            gcongr; exact hwinL n
    -- Per-level real core: `∫ ≤ (chaining sum) + B n`.
    have hmain : ∀ n : ℕ,
        ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
          ≤ ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T
              + ENNReal.ofReal (B n) := by
      intro n
      have hApos : (0 : ℝ) ≤
          ∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + 1 + (j : ℤ)) :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (dudleySummand_nonneg T _))
      have hcore : (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
          ≤ (∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * (K : ℝ)
                * dudleySummand T (κ + 1 + (j : ℤ))) + B n := by
        calc (∫ ω, F.sup' hFne (fun t => X t ω) ∂μ)
            ≤ ∫ ω, F.sup' hFne (fun t => X t ω - X c ω) ∂μ := hstepA
          _ ≤ (∑ j ∈ Finset.range n, ∫ ω, S j ω ∂μ)
                + ∫ ω, F.sup' hFne (fun t => X t ω - X (netProj (N n) t) ω) ∂μ := hB1n n
          _ ≤ (∑ j ∈ Finset.range n, 6 * Real.sqrt 3 * (K : ℝ)
                  * dudleySummand T (κ + 1 + (j : ℤ))) + B n :=
              add_le_add (Finset.sum_le_sum (fun j _ => hB2 j)) (hres n)
      refine (ENNReal.ofReal_le_ofReal hcore).trans ?_
      rw [ENNReal.ofReal_add hApos (hBnn n)]
      exact add_le_add (hAle n) le_rfl
    -- Send `n → ∞`: the residual `B n → 0`, so the RHS tends to the target.
    have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) := by
      have hgeom : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (-κ) * (1 / 2 : ℝ) ^ n)
          Filter.atTop (nhds ((2 : ℝ) ^ (-κ) * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at hgeom
      refine hgeom.congr (fun n => ?_)
      rw [hεval n, show (-(κ + (n : ℤ))) = (-κ) + (-(n : ℤ)) from by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    have hBlim : Filter.Tendsto B Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n => (K : ℝ) * ε n) Filter.atTop (nhds 0) := by
        have := hεlim.const_mul (K : ℝ); simpa using this
      have h2 : Filter.Tendsto
          (fun n => Real.sqrt 3 * ((K : ℝ) * ε n) * Real.sqrt (2 * Real.log (F.card : ℝ)))
          Filter.atTop (nhds 0) := by
        have := (h1.const_mul (Real.sqrt 3)).mul_const
          (Real.sqrt (2 * Real.log (F.card : ℝ)))
        simpa using this
      rw [hBdef]; exact h2
    have hCtendsto : Filter.Tendsto
        (fun n => ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T
            + ENNReal.ofReal (B n))
        Filter.atTop (nhds (ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T)) := by
      have hofB : Filter.Tendsto (fun n => ENNReal.ofReal (B n)) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hBlim
        simpa using! this
      have := (tendsto_const_nhds
        (x := ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T)).add hofB
      simpa using this
    exact ge_of_tendsto' hCtendsto (fun n => hmain n)

/-- **Discrete Dudley inequality, absolute form** (HDP §8.1, Remark 8.1.5
discrete; faithful general-`T` form): for every finite subset `F ⊆ T` and any
anchor `t₀ ∈ T` (not necessarily in `F`),
`E max_{t∈F} |X_t − X_{t₀}| ≤ 20 · K · dudleyLSum T`, with NO mean-zero
hypothesis. Constant `20` as in the finite form. -/
theorem discrete_dudley_abs {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E}
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
    -- USER-INPUT: the anchor point; HDP §8.1, Remark 8.1.5
    {t₀ : E} (ht₀ : t₀ ∈ T)
    {F : Finset E}
    -- USER-INPUT: the finite subset of Remark 7.2.1
    (hF : ↑F ⊆ T)
    -- LEAN-ONLY: nonemptiness so `Finset.sup'` is defined
    (hFne : F.Nonempty) :
    ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
      ≤ ENNReal.ofReal 20 * K * dudleyLSum T := by
  classical
  have hbd : Bornology.IsBounded T := isBounded_of_coveringNumber_ne_top hcov
  have hmemT : ∀ t, t ∈ F → t ∈ T := fun t ht => hF (Finset.mem_coe.mpr ht)
  -- Integrability of every increment `|X_u − X_v|` from the ψ₂ tail (no mean-zero
  -- / integrability hypothesis is available in the absolute form).
  have hint_abs : ∀ u v : E, u ∈ T → v ∈ T →
      MeasureTheory.Integrable (fun ω => |X u ω - X v ω|) μ := by
    intro u v hu hv
    have hSG : subGaussianNorm (fun ω => X u ω - X v ω) μ
        ≤ ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by
      refine (hinc v hv u hu).trans ?_
      have hde : edist v u ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd hv hu)
      calc (K : ℝ≥0∞) * edist v u
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    have hbi := integrable_biSup_abs (s := ({u} : Finset E))
      (Finset.singleton_nonempty u) (Y := fun _ => fun ω => X u ω - X v ω)
      (fun i _ => (hmeas u hu).sub (hmeas v hv)) (fun i _ => hSG)
    have hEq : (fun ω => ⨆ _ ∈ ({u} : Finset E), |X u ω - X v ω|)
        = fun ω => |X u ω - X v ω| := by
      funext ω
      rw [biSup_finset_eq_sup' (Finset.singleton_nonempty u)
        (fun _ => |X u ω - X v ω|) (fun _ _ => abs_nonneg _), Finset.sup'_singleton]
    rwa [hEq] at hbi
  -- Common degenerate conclusion: if all `|X_t − X_{t₀}|` vanish a.e., the
  -- integral is `0`.
  have hdegen : (∀ t ∈ T, (fun ω => X t ω - X t₀ ω) =ᵐ[μ] 0) →
      ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
        ≤ ENNReal.ofReal 20 * K * dudleyLSum T := by
    intro hae
    have haeeq : (fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|)) =ᵐ[μ] fun _ => (0 : ℝ) := by
      have hall : ∀ᵐ ω ∂μ, ∀ t ∈ F, |X t ω - X t₀ ω| = 0 := by
        rw [F.eventually_all]
        intro t ht
        filter_upwards [hae t (hmemT t ht)] with ω hω
        have : X t ω - X t₀ ω = 0 := hω
        rw [this, abs_zero]
      filter_upwards [hall] with ω hω
      apply le_antisymm
      · exact Finset.sup'_le hFne _ (fun t ht => le_of_eq (hω t ht))
      · obtain ⟨t₁, ht₁⟩ := hFne
        exact le_trans (abs_nonneg _) (Finset.le_sup' (fun t => |X t ω - X t₀ ω|) ht₁)
    rw [integral_congr_ae haeeq, integral_zero, ENNReal.ofReal_zero]; exact zero_le
  -- Degenerate `K = 0`.
  rcases eq_or_lt_of_le (zero_le (a := K)) with hK0 | hKpos
  · apply hdegen
    intro t ht
    have hle : subGaussianNorm (fun ω => X t ω - X t₀ ω) μ ≤ 0 := by
      refine (hinc t₀ ht₀ t ht).trans ?_
      rw [← hK0]; simp
    exact ae_eq_zero_of_subGaussianNorm_eq_zero ((hmeas t ht).sub (hmeas t₀ ht₀))
      (le_antisymm hle (by positivity))
  -- Degenerate `diam T = 0`.
  rcases eq_or_lt_of_le (Metric.diam_nonneg (s := T)) with hD0 | hDpos
  · apply hdegen
    intro t ht
    have hzero : dist t₀ t = 0 := by
      have hle := Metric.dist_le_diam_of_mem hbd ht₀ ht
      rw [← hD0] at hle; exact le_antisymm hle dist_nonneg
    exact hinc.sub_ae_eq_zero (hmeas t₀ ht₀) (hmeas t ht) ht₀ ht hzero
  · -- Main case: re-anchored dyadic chaining in absolute value, truncated.
    obtain ⟨κ, hκ1, hκ2⟩ := exists_coarse_scale hDpos
    set ε : ℕ → ℝ := fun j => (2 : ℝ) ^ (-(κ + (j : ℤ))) with hεdef
    have hεval : ∀ j : ℕ, ε j = (2 : ℝ) ^ (-(κ + (j : ℤ))) := fun j => by rw [hεdef]
    have hεpos : ∀ j : ℕ, 0 < ε j := fun j => by rw [hεval]; exact zpow_pos (by norm_num) _
    have hεrec : ∀ j : ℕ, ε j = 2 * ε (j + 1) := by
      intro j
      rw [hεval, hεval,
        show (-(κ + ((j + 1 : ℕ) : ℤ))) = (-(κ + (j : ℤ))) - 1 by push_cast; ring,
        zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp only [zpow_one]; ring
    have hεle : ∀ j : ℕ, ε (j + 1) ≤ ε j := fun j => by
      rw [hεrec j]; linarith [hεpos (j + 1)]
    -- `ε → 0` (used both for the re-anchor bound and the residual limit).
    have hεlim : Filter.Tendsto ε Filter.atTop (nhds 0) := by
      have hgeom : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ (-κ) * (1 / 2 : ℝ) ^ n)
          Filter.atTop (nhds ((2 : ℝ) ^ (-κ) * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul _
      rw [mul_zero] at hgeom
      refine hgeom.congr (fun n => ?_)
      rw [hεval n, show (-(κ + (n : ℤ))) = (-κ) + (-(n : ℤ)) from by ring,
        zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    -- Dyadic nets of the carrier at every scale.
    have hnet : ∀ j : ℕ, ∃ N : Finset E, ↑N ⊆ T ∧ N.Nonempty ∧
        (∀ t ∈ T, ∃ a ∈ N, dist t a ≤ ε j) ∧ (N.card : ℕ∞) = coveringNumber T (ε j) :=
      fun j => exists_finset_net_of_cov_ne_top (hcov (ε j) (hεpos j)) hne (hεpos j)
    choose N hN using hnet
    have hprojT : ∀ i : ℕ, ∀ t : E, netProj (N i) t ∈ T :=
      fun i t => (hN i).1 (Finset.mem_coe.mpr (netProj_mem (hN i).2.1 t))
    have hproj : ∀ i : ℕ, ∀ t ∈ T, dist t (netProj (N i) t) ≤ ε i :=
      fun i t ht => dist_netProj_le ((hN i).2.2.1 t ht)
    have hcardcov : ∀ j : ℕ, (N j).card = (coveringNumber T (ε j)).toNat := by
      intro j; have h := (hN j).2.2.2; rw [← h]; simp
    have hcov1 : coveringNumber T (ε 0) = 1 := by
      apply coveringNumber_eq_one_of_diam_le hne hbd (le_of_lt (hεpos 0))
      rw [hεval]; push_cast; simpa using hκ1
    -- Two carrier points at positive distance (from `diam T > 0`).
    obtain ⟨a, haT, b, hbT, hab⟩ : ∃ a ∈ T, ∃ b ∈ T, 0 < dist a b := by
      by_contra h
      push_neg at h
      exact absurd (Metric.diam_le_of_forall_dist_le le_rfl (fun x hx y hy => h x hx y hy))
        (not_le.mpr hDpos)
    -- A level `J` beyond which every net has ≥ 2 points (`2·ε_j < dist a b`).
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ i : ℕ, J ≤ i → 1 < coveringNumber T (ε i) := by
      have h2εlim : Filter.Tendsto (fun i => 2 * ε i) Filter.atTop (nhds 0) := by
        have := hεlim.const_mul (2 : ℝ); simpa using this
      obtain ⟨J, hJ'⟩ := Filter.eventually_atTop.1 (h2εlim.eventually_lt_const hab)
      exact ⟨J, fun i hi =>
        one_lt_coveringNumber_of_two_mul_lt_dist (hεpos i).le haT hbT (hJ' i hi)⟩
    -- **Re-anchoring**: `m` = the finest scale (≤ J) whose net is a singleton.
    set G : Finset ℕ := (Finset.range (J + 1)).filter (fun j => coveringNumber T (ε j) = 1)
      with hGdef
    have h0G : (0 : ℕ) ∈ G := by
      rw [hGdef, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr (by omega), hcov1⟩
    have hGne : G.Nonempty := ⟨0, h0G⟩
    set m : ℕ := G.max' hGne with hmdef
    have hmG : m ∈ G := G.max'_mem hGne
    have hmcov1 : coveringNumber T (ε m) = 1 := (Finset.mem_filter.mp hmG).2
    -- Above `m` the net has ≥ 2 points.
    have hcov2 : ∀ j : ℕ, m < j → 2 ≤ (N j).card := by
      intro j hjm
      have hjne : coveringNumber T (ε j) ≠ 1 := by
        intro hj1
        by_cases hjJ : j ≤ J
        · have hjG : j ∈ G := by
            rw [hGdef, Finset.mem_filter]; exact ⟨Finset.mem_range.mpr (by omega), hj1⟩
          exact absurd (G.le_max' j hjG) (by omega)
        · push_neg at hjJ
          have h2 := hJ j (le_of_lt hjJ)
          rw [hj1] at h2; exact lt_irrefl 1 h2
      have hpos : 1 ≤ (N j).card := (hN j).2.1.card_pos
      rcases Nat.lt_or_ge (N j).card 2 with h2 | h2
      · exfalso; apply hjne
        have hc1 : (N j).card = 1 := by omega
        have hc := (hN j).2.2.2; rw [hc1] at hc; exact_mod_cast hc.symm
      · exact h2
    -- The single anchor point `c` at scale `m`.
    have hcard_m : (N m).card = 1 := by rw [hcardcov, hmcov1]; rfl
    obtain ⟨c, hc0⟩ := Finset.card_eq_one.mp hcard_m
    have hcT : c ∈ T := (hN m).1 (Finset.mem_coe.mpr (hc0 ▸ Finset.mem_singleton_self c))
    have hπm : ∀ t : E, netProj (N m) t = c := by
      intro t; rw [hc0]
      have hmem := netProj_mem (Finset.singleton_nonempty c) t
      rwa [Finset.mem_singleton] at hmem
    -- **Per-level abs suprema over close pairs** (window index `j`, scale `m+j`).
    set CP : ℕ → Finset (E × E) := fun j =>
      closePairs (N (m + j + 1)) (N (m + j)) (ε (m + j + 1) + ε (m + j)) with hCPdef
    set CPS : ℕ → Ω → ℝ := fun j ω =>
      ⨆ p ∈ CP j, |X p.1 ω - X p.2 ω| with hCPSdef
    have hCPne : ∀ j : ℕ, (CP j).Nonempty := fun j =>
      ⟨(netProj (N (m + j + 1)) hne.some, netProj (N (m + j)) hne.some),
        proj_pair_mem_closePairs
          (hproj (m + j + 1) hne.some hne.some_mem) (hproj (m + j) hne.some hne.some_mem)
          (hN (m + j + 1)).2.1 (hN (m + j)).2.1⟩
    have hCPmem : ∀ j : ℕ, ∀ p ∈ CP j, p.1 ∈ T ∧ p.2 ∈ T := by
      intro j p hp
      rw [hCPdef] at hp
      simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨(hN (m + j + 1)).1 (Finset.mem_coe.mpr hp.1.1),
        (hN (m + j)).1 (Finset.mem_coe.mpr hp.1.2)⟩
    set Lj : ℕ → ℝ≥0 := fun j => K * Real.toNNReal (ε (m + j + 1) + ε (m + j)) with hLjdef
    have hSGpair : ∀ j : ℕ, ∀ p ∈ CP j,
        subGaussianNorm (fun ω => X p.1 ω - X p.2 ω) μ ≤ (Lj j : ℝ≥0∞) := by
      intro j p hp
      have hdle : dist p.1 p.2 ≤ ε (m + j + 1) + ε (m + j) := by
        rw [hCPdef] at hp
        simp only [closePairs, Finset.mem_filter, Finset.mem_product] at hp
        exact hp.2
      refine (hinc p.2 (hCPmem j p hp).2 p.1 (hCPmem j p hp).1).trans ?_
      have hde : edist p.2 p.1 ≤ (Real.toNNReal (ε (m + j + 1) + ε (m + j)) : ℝ≥0∞) := by
        rw [edist_dist, dist_comm]
        exact ENNReal.ofReal_le_ofReal hdle
      calc (K : ℝ≥0∞) * edist p.2 p.1
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (ε (m + j + 1) + ε (m + j)) : ℝ≥0∞) := by gcongr
        _ = (Lj j : ℝ≥0∞) := by rw [hLjdef]; push_cast; ring
    have hIntCPS : ∀ j : ℕ, MeasureTheory.Integrable (CPS j) μ := fun j =>
      integrable_biSup_abs (hCPne j)
        (fun p hp => ((hmeas _ (hCPmem j p hp).1).sub (hmeas _ (hCPmem j p hp).2)))
        (hSGpair j)
    -- Residual (level `m+n`) abs-sup and the anchor increment.
    set R : ℕ → Ω → ℝ := fun n ω =>
      F.sup' hFne (fun t => |X t ω - X (netProj (N (m + n)) t) ω|) with hRdef
    have hIntR : ∀ n : ℕ, MeasureTheory.Integrable (R n) μ := fun n =>
      integrable_sup'_finset hFne
        (fun t ht => hint_abs t (netProj (N (m + n)) t) (hmemT t ht) (hprojT (m + n) t))
    have hIntAnchor : MeasureTheory.Integrable (fun ω => |X c ω - X t₀ ω|) μ :=
      hint_abs c t₀ hcT ht₀
    have hIntSupF : MeasureTheory.Integrable
        (fun ω => F.sup' hFne (fun t => |X t ω - X t₀ ω|)) μ :=
      integrable_sup'_finset hFne
        (fun t ht => hint_abs t t₀ (hmemT t ht) ht₀)
    -- Anchor first-moment: `E|X_c − X_{t₀}| ≤ √π·K·diam T`.
    have hAnchorSG : subGaussianNorm (fun ω => X c ω - X t₀ ω) μ
        ≤ ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by
      refine (hinc t₀ ht₀ c hcT).trans ?_
      have hde : edist t₀ c ≤ (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (Metric.dist_le_diam_of_mem hbd ht₀ hcT)
      calc (K : ℝ≥0∞) * edist t₀ c
          ≤ (K : ℝ≥0∞) * (Real.toNNReal (Metric.diam T) : ℝ≥0∞) := by gcongr
        _ = ((K * Real.toNNReal (Metric.diam T) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    have hAnchorInt : (∫ ω, |X c ω - X t₀ ω| ∂μ)
        ≤ Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T) := by
      have h := integral_abs_le_of_subGaussianNorm_le
        ((hmeas c hcT).sub (hmeas t₀ ht₀)) hAnchorSG
      refine h.trans (le_of_eq ?_)
      rw [NNReal.coe_mul, Real.coe_toNNReal _ Metric.diam_nonneg]
    -- **STEP B: truncated chain split** per level `n`.
    have hstepB : ∀ n : ℕ, (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
        ≤ (∑ j ∈ Finset.range n, ∫ ω, CPS j ω ∂μ) + (∫ ω, R n ω ∂μ)
          + ∫ ω, |X c ω - X t₀ ω| ∂μ := by
      intro n
      have hpt : ∀ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|)
          ≤ (∑ j ∈ Finset.range n, CPS j ω) + R n ω + |X c ω - X t₀ ω| := by
        intro ω
        refine Finset.sup'_le hFne _ (fun t ht => ?_)
        have htT := hmemT t ht
        have htel : X t ω - X c ω
            = (∑ i ∈ Finset.range n,
                (X (netProj (N (m + i + 1)) t) ω - X (netProj (N (m + i)) t) ω))
              + (X t ω - X (netProj (N (m + n)) t) ω) := by
          have hshift : ∀ i : ℕ,
              (fun i => X (netProj (N (m + i)) t) ω) (i + 1)
                - (fun i => X (netProj (N (m + i)) t) ω) i
              = X (netProj (N (m + i + 1)) t) ω - X (netProj (N (m + i)) t) ω := by
            intro i; simp only; rw [show m + (i + 1) = m + i + 1 from by ring]
          have h0 : X (netProj (N (m + 0)) t) ω = X c ω := by
            rw [show m + 0 = m from by ring, hπm t]
          have htele := chain_telescope (n := n) (fun i => X (netProj (N (m + i)) t) ω)
          rw [h0] at htele
          rw [show (∑ i ∈ Finset.range n,
                (X (netProj (N (m + i + 1)) t) ω - X (netProj (N (m + i)) t) ω))
              = ∑ i ∈ Finset.range n,
                ((fun i => X (netProj (N (m + i)) t) ω) (i + 1)
                  - (fun i => X (netProj (N (m + i)) t) ω) i)
            from Finset.sum_congr rfl (fun i _ => (hshift i).symm)]
          linarith [htele]
        have hbound : |X t ω - X c ω| ≤ (∑ i ∈ Finset.range n, CPS i ω) + R n ω := by
          rw [htel]
          refine (abs_add_le _ _).trans ?_
          have hs1 :
              |∑ i ∈ Finset.range n,
                  (X (netProj (N (m + i + 1)) t) ω - X (netProj (N (m + i)) t) ω)|
                ≤ ∑ i ∈ Finset.range n, CPS i ω := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            refine Finset.sum_le_sum (fun i _ => ?_)
            have hmem : (netProj (N (m + i + 1)) t, netProj (N (m + i)) t) ∈ CP i :=
              proj_pair_mem_closePairs (hproj (m + i + 1) t htT) (hproj (m + i) t htT)
                (hN (m + i + 1)).2.1 (hN (m + i)).2.1
            rw [hCPSdef]; simp only
            exact le_biSup_finset (fun p => |X p.1 ω - X p.2 ω|) hmem
          have hs2 : |X t ω - X (netProj (N (m + n)) t) ω| ≤ R n ω := by
            rw [hRdef]; simp only
            exact Finset.le_sup' (fun s => |X s ω - X (netProj (N (m + n)) s) ω|) ht
          linarith
        calc |X t ω - X t₀ ω|
            ≤ |X t ω - X c ω| + |X c ω - X t₀ ω| := by
              rw [show X t ω - X t₀ ω = (X t ω - X c ω) + (X c ω - X t₀ ω) from by ring]
              exact abs_add_le _ _
          _ ≤ (∑ i ∈ Finset.range n, CPS i ω) + R n ω + |X c ω - X t₀ ω| := by
              linarith [hbound]
      have hIntRHS : MeasureTheory.Integrable
          (fun ω => (∑ j ∈ Finset.range n, CPS j ω) + R n ω + |X c ω - X t₀ ω|) μ :=
        ((integrable_finset_sum _ (fun j _ => hIntCPS j)).add (hIntR n)).add hIntAnchor
      calc (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
          ≤ ∫ ω, ((∑ j ∈ Finset.range n, CPS j ω) + R n ω + |X c ω - X t₀ ω|) ∂μ :=
            integral_mono_ae hIntSupF hIntRHS (ae_of_all _ hpt)
        _ = (∑ j ∈ Finset.range n, ∫ ω, CPS j ω ∂μ) + (∫ ω, R n ω ∂μ)
              + ∫ ω, |X c ω - X t₀ ω| ∂μ := by
            rw [show (∫ ω, ((∑ j ∈ Finset.range n, CPS j ω) + R n ω + |X c ω - X t₀ ω|) ∂μ)
                  = (∫ ω, ((∑ j ∈ Finset.range n, CPS j ω) + R n ω) ∂μ)
                      + ∫ ω, |X c ω - X t₀ ω| ∂μ
                from integral_add
                  ((integrable_finset_sum _ (fun j _ => hIntCPS j)).add (hIntR n)) hIntAnchor,
              integral_add (integrable_finset_sum _ (fun j _ => hIntCPS j)) (hIntR n),
              integral_finset_sum _ (fun j _ => hIntCPS j)]
    -- **STEP C: per-level bound** `E[CPS_j] ≤ 6√3·K·dudleySummand(κ+m+1+j)`.
    have hC : ∀ j : ℕ,
        (∫ ω, CPS j ω ∂μ) ≤ 6 * Real.sqrt 3 * K * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)) := by
      intro j
      set r : ℝ := ε (m + j + 1) + ε (m + j) with hrdef
      have hrpos : 0 < r := by rw [hrdef]; linarith [hεpos (m + j + 1), hεpos (m + j)]
      have hr3 : r = 3 * ε (m + j + 1) := by rw [hrdef, hεrec (m + j)]; ring
      have hNcard2 : 2 ≤ (N (m + j + 1)).card := hcov2 (m + j + 1) (by omega)
      set Mnat : ℕ := (N (m + j + 1)).card with hMnatdef
      set M : ℝ := (Mnat : ℝ) with hMdef
      have hM2 : (2 : ℝ) ≤ M := by rw [hMdef, hMnatdef]; exact_mod_cast hNcard2
      have hM1nat : 0 < Mnat := by omega
      have hcardCPnat : (CP j).card ≤ Mnat ^ 2 := by
        have hNjle : (N (m + j)).card ≤ (N (m + j + 1)).card := by
          have h1 := (hN (m + j)).2.2.2
          have h2 := (hN (m + j + 1)).2.2.2
          have hanti : coveringNumber T (ε (m + j)) ≤ coveringNumber T (ε (m + j + 1)) :=
            coveringNumber_anti (hεle (m + j))
          rw [← h1, ← h2] at hanti
          exact_mod_cast hanti
        calc (CP j).card ≤ (N (m + j + 1)).card * (N (m + j)).card := card_closePairs_le _ _ _
          _ ≤ (N (m + j + 1)).card * (N (m + j + 1)).card := by gcongr
          _ = Mnat ^ 2 := by rw [hMnatdef, sq]
      have hslc : sqrtLogCov T (ε (m + j + 1)) = Real.sqrt (Real.log M) := by
        unfold sqrtLogCov; rw [← hcardcov (m + j + 1), hMdef, hMnatdef]
      have hlogM_pos : 0 < Real.log M := Real.log_pos (by linarith)
      have hstep : Real.sqrt (Real.log (2 * ((CP j).card : ℝ)))
          ≤ Real.sqrt 3 * sqrtLogCov T (ε (m + j + 1)) := by
        rw [hslc, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        apply Real.sqrt_le_sqrt
        have hcard_le : (2 : ℝ) * ((CP j).card : ℝ) ≤ M ^ 3 := by
          have h1 : ((CP j).card : ℝ) ≤ M ^ 2 := by
            rw [hMdef]; exact_mod_cast hcardCPnat
          have h2 : (2 : ℝ) * M ^ 2 ≤ M ^ 3 := by nlinarith [hM2, sq_nonneg M]
          nlinarith [h1, hM2]
        have hposc : (0 : ℝ) < 2 * ((CP j).card : ℝ) := by
          have hc : 0 < (CP j).card := (hCPne j).card_pos
          have : (0 : ℝ) < ((CP j).card : ℝ) := by exact_mod_cast hc
          linarith
        have hlog := Real.log_le_log hposc hcard_le
        rw [show M ^ 3 = M ^ (3 : ℕ) from rfl, Real.log_pow] at hlog
        push_cast at hlog; linarith
      have hdud : dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))
          = ε (m + j + 1) * sqrtLogCov T (ε (m + j + 1)) := by
        have hkk : (-(κ + (m : ℤ) + 1 + (j : ℤ))) = (-(κ + ((m + j + 1 : ℕ) : ℤ))) := by
          push_cast; ring
        simp only [dudleySummand]
        rw [hkk, hεval (m + j + 1)]
      have hLjpos : 0 < Lj j := by
        rw [hLjdef]
        have hrpos' : 0 < Real.toNNReal r := Real.toNNReal_pos.mpr hrpos
        exact mul_pos hKpos hrpos'
      have hExp : (∫ ω, CPS j ω ∂μ)
          ≤ 2 * (Lj j : ℝ) * Real.sqrt (Real.log (2 * (CP j).card)) := by
        rw [hCPSdef]
        exact expectation_abs_max_le (hCPne j) hLjpos
          (fun p hp => ((hmeas _ (hCPmem j p hp).1).sub (hmeas _ (hCPmem j p hp).2)))
          (hSGpair j)
      refine hExp.trans ?_
      have hLjval : (Lj j : ℝ) = (K : ℝ) * r := by
        rw [hLjdef, NNReal.coe_mul, Real.coe_toNNReal _ hrpos.le, hrdef]
      rw [hLjval, hdud]
      calc 2 * ((K : ℝ) * r) * Real.sqrt (Real.log (2 * (CP j).card))
          ≤ 2 * ((K : ℝ) * r) * (Real.sqrt 3 * sqrtLogCov T (ε (m + j + 1))) := by
            apply mul_le_mul_of_nonneg_left hstep
            positivity
        _ = 6 * Real.sqrt 3 * K * (ε (m + j + 1) * sqrtLogCov T (ε (m + j + 1))) := by
            rw [hr3]; ring
    -- Residual real bound at level `m+n`.
    set B : ℕ → ℝ := fun n =>
      2 * ((K : ℝ) * ε (m + n)) * Real.sqrt (Real.log (2 * (F.card : ℝ))) with hBdef
    have hBnn : ∀ n : ℕ, 0 ≤ B n := fun n => by
      rw [hBdef]; simp only
      exact mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg K.coe_nonneg (hεpos (m + n)).le)) (Real.sqrt_nonneg _)
    have hres : ∀ n : ℕ, (∫ ω, R n ω ∂μ) ≤ B n := by
      intro n
      rw [hBdef, hRdef]; simp only
      exact residual_abs_expectation_le hmeas hinc (hN (m + n)).1 (hN (m + n)).2.1
        (hεpos (m + n)) hKpos (hN (m + n)).2.2.1 hF hFne
    -- ℝ≥0∞ window bound at the shifted index.
    have hwinL : ∀ n : ℕ,
        (∑ j ∈ Finset.range n, ENNReal.ofReal (dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))))
          ≤ dudleyLSum T := by
      intro n
      have hemb : Function.Injective (fun j : ℕ => κ + (m : ℤ) + 1 + (j : ℤ)) := by
        intro x y hxy; simp only at hxy; omega
      rw [show (∑ j ∈ Finset.range n, ENNReal.ofReal (dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))))
            = ∑ k ∈ (Finset.range n).map ⟨fun j : ℕ => κ + (m : ℤ) + 1 + (j : ℤ), hemb⟩,
                ENNReal.ofReal (dudleySummand T k)
          from by rw [Finset.sum_map]; rfl]
      exact sum_window_le_dudleyLSum _
    -- `ofReal` of the chaining partial sum is below `ofReal(6√3)·K·dudleyLSum`.
    have hAle : ∀ n : ℕ,
        ENNReal.ofReal
            (∑ j ∈ Finset.range n,
              6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
          ≤ ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T := by
      intro n
      have hterm : ∀ j : ℕ,
          ENNReal.ofReal
              (6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
            = ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞)
                * ENNReal.ofReal (dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))) := by
        intro j
        rw [mul_assoc (6 * Real.sqrt 3) (K : ℝ), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
      calc ENNReal.ofReal
              (∑ j ∈ Finset.range n,
                6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
          = ∑ j ∈ Finset.range n,
              ENNReal.ofReal
                (6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))) :=
            ENNReal.ofReal_sum_of_nonneg
              (fun j _ => mul_nonneg (by positivity) (dudleySummand_nonneg T _))
        _ = ∑ j ∈ Finset.range n,
              ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞)
                * ENNReal.ofReal (dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))) :=
            Finset.sum_congr rfl (fun j _ => hterm j)
        _ = ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞)
              * ∑ j ∈ Finset.range n,
                  ENNReal.ofReal (dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ))) := by
            rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T := by
            gcongr; exact hwinL n
    -- Numeric absorber constant `4√π/√log2 ≤ 20 − 6√3`.
    have hlog2pos : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
    have hsqrt3le : Real.sqrt 3 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 from by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h20nn : (0 : ℝ) ≤ 20 - 6 * Real.sqrt 3 := by nlinarith [hsqrt3le]
    have hconst : Real.sqrt Real.pi * (4 / Real.sqrt (Real.log 2)) ≤ 20 - 6 * Real.sqrt 3 := by
      have hpi : Real.sqrt Real.pi ≤ 1.773 := by
        rw [show (1.773 : ℝ) = Real.sqrt (1.773 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        apply Real.sqrt_le_sqrt
        nlinarith [Real.pi_lt_d4]
      have hlog2 : 0.693 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
      have hslog2 : 0.832 ≤ Real.sqrt (Real.log 2) := by
        rw [show (0.832 : ℝ) = Real.sqrt (0.832 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        apply Real.sqrt_le_sqrt; nlinarith [hlog2]
      have hsqrt3 : Real.sqrt 3 ≤ 1.7321 := by
        rw [show (1.7321 : ℝ) = Real.sqrt (1.7321 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        apply Real.sqrt_le_sqrt; norm_num
      have hdivle : (4 : ℝ) / Real.sqrt (Real.log 2) ≤ 4 / 0.832 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hslog2
      calc Real.sqrt Real.pi * (4 / Real.sqrt (Real.log 2))
          ≤ 1.773 * (4 / 0.832) := by
            apply mul_le_mul hpi hdivle (by positivity) (by norm_num)
        _ ≤ 20 - 6 * Real.sqrt 3 := by nlinarith [hsqrt3]
    -- ℝ≥0∞ anchor absorber: `ofReal(√π·K·diam) ≤ ofReal(20−6√3)·K·dudleyLSum`.
    have hAbsorbL : ENNReal.ofReal (Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T))
        ≤ ENNReal.ofReal (20 - 6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T := by
      have hs2 : Real.sqrt (Real.log 2) ≠ 0 := ne_of_gt hlog2pos
      have hrw : Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T)
          = ((K : ℝ) * (Real.sqrt Real.pi / Real.sqrt (Real.log 2)))
              * (Metric.diam T * Real.sqrt (Real.log 2)) := by
        field_simp
      rw [hrw, ENNReal.ofReal_mul
            (by positivity : (0 : ℝ) ≤ (K : ℝ) * (Real.sqrt Real.pi / Real.sqrt (Real.log 2))),
          ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
      calc (K : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt Real.pi / Real.sqrt (Real.log 2))
              * ENNReal.ofReal (Metric.diam T * Real.sqrt (Real.log 2))
          ≤ (K : ℝ≥0∞) * ENNReal.ofReal (Real.sqrt Real.pi / Real.sqrt (Real.log 2))
              * (4 * dudleyLSum T) := by
            gcongr
            exact ofReal_diam_mul_sqrt_log_two_le_four_mul_dudleyLSum hcov hne
        _ = (ENNReal.ofReal (Real.sqrt Real.pi / Real.sqrt (Real.log 2)) * 4)
              * ((K : ℝ≥0∞) * dudleyLSum T) := by ring
        _ ≤ ENNReal.ofReal (20 - 6 * Real.sqrt 3) * ((K : ℝ≥0∞) * dudleyLSum T) := by
            gcongr
            rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 from (ENNReal.ofReal_ofNat 4).symm,
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (by
              rw [div_mul_eq_mul_div, mul_div_assoc]; exact hconst)
        _ = ENNReal.ofReal (20 - 6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T := by
            rw [mul_assoc]
    -- Per-level `ℝ≥0∞` bound: `ofReal(∫) ≤ ofReal(20)·K·dudleyLSum + ofReal(B n)`.
    have hmain : ∀ n : ℕ,
        ENNReal.ofReal (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
          ≤ ENNReal.ofReal 20 * (K : ℝ≥0∞) * dudleyLSum T + ENNReal.ofReal (B n) := by
      intro n
      have hchain_nn : (0 : ℝ) ≤
          ∑ j ∈ Finset.range n,
            6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)) :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (dudleySummand_nonneg T _))
      have hanchor_nn : (0 : ℝ) ≤ Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T) := by
        positivity
      have hcore : (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
          ≤ (∑ j ∈ Finset.range n,
              6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
            + B n + Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T) := by
        calc (∫ ω, F.sup' hFne (fun t => |X t ω - X t₀ ω|) ∂μ)
            ≤ (∑ j ∈ Finset.range n, ∫ ω, CPS j ω ∂μ) + (∫ ω, R n ω ∂μ)
                + ∫ ω, |X c ω - X t₀ ω| ∂μ := hstepB n
          _ ≤ (∑ j ∈ Finset.range n,
                6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
              + B n + Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T) :=
            add_le_add (add_le_add (Finset.sum_le_sum (fun j _ => hC j)) (hres n)) hAnchorInt
      refine (ENNReal.ofReal_le_ofReal hcore).trans ?_
      rw [ENNReal.ofReal_add (add_nonneg hchain_nn (hBnn n)) hanchor_nn,
        ENNReal.ofReal_add hchain_nn (hBnn n)]
      have hcombine :
          ENNReal.ofReal
              (∑ j ∈ Finset.range n,
                6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
            + ENNReal.ofReal (Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T))
          ≤ ENNReal.ofReal 20 * (K : ℝ≥0∞) * dudleyLSum T := by
        have hsum20 : ENNReal.ofReal (6 * Real.sqrt 3) + ENNReal.ofReal (20 - 6 * Real.sqrt 3)
            = ENNReal.ofReal 20 := by
          rw [← ENNReal.ofReal_add (by positivity) h20nn]; congr 1; ring
        calc ENNReal.ofReal
                (∑ j ∈ Finset.range n,
                  6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
              + ENNReal.ofReal (Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T))
            ≤ ENNReal.ofReal (6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T
                + ENNReal.ofReal (20 - 6 * Real.sqrt 3) * (K : ℝ≥0∞) * dudleyLSum T :=
              add_le_add (hAle n) hAbsorbL
          _ = (ENNReal.ofReal (6 * Real.sqrt 3) + ENNReal.ofReal (20 - 6 * Real.sqrt 3))
                * (K : ℝ≥0∞) * dudleyLSum T := by rw [add_mul, add_mul]
          _ = ENNReal.ofReal 20 * (K : ℝ≥0∞) * dudleyLSum T := by rw [hsum20]
      calc ENNReal.ofReal
              (∑ j ∈ Finset.range n,
                6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
            + ENNReal.ofReal (B n)
            + ENNReal.ofReal (Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T))
          = (ENNReal.ofReal
                (∑ j ∈ Finset.range n,
                  6 * Real.sqrt 3 * (K : ℝ) * dudleySummand T (κ + (m : ℤ) + 1 + (j : ℤ)))
              + ENNReal.ofReal (Real.sqrt Real.pi * ((K : ℝ) * Metric.diam T)))
              + ENNReal.ofReal (B n) := by ring
        _ ≤ ENNReal.ofReal 20 * (K : ℝ≥0∞) * dudleyLSum T + ENNReal.ofReal (B n) :=
            add_le_add hcombine le_rfl
    -- Send `n → ∞`: the residual `B n → 0`.
    have hBlim : Filter.Tendsto B Filter.atTop (nhds 0) := by
      have hεm : Filter.Tendsto (fun n => ε (m + n)) Filter.atTop (nhds 0) := by
        have h := hεlim.comp (Filter.tendsto_add_atTop_nat m)
        simp only [Function.comp_def] at h
        rwa [show (fun n => ε (n + m)) = (fun n => ε (m + n)) from by
          funext n; rw [Nat.add_comm]] at h
      have h1 : Filter.Tendsto (fun n => (K : ℝ) * ε (m + n)) Filter.atTop (nhds 0) := by
        have := hεm.const_mul (K : ℝ); simpa using this
      have h2 : Filter.Tendsto
          (fun n => 2 * ((K : ℝ) * ε (m + n)) * Real.sqrt (Real.log (2 * (F.card : ℝ))))
          Filter.atTop (nhds 0) := by
        have := (h1.const_mul (2 : ℝ)).mul_const (Real.sqrt (Real.log (2 * (F.card : ℝ))))
        simpa using this
      rw [hBdef]; exact h2
    have hCtendsto : Filter.Tendsto
        (fun n => ENNReal.ofReal 20 * (K : ℝ≥0∞) * dudleyLSum T + ENNReal.ofReal (B n))
        Filter.atTop (nhds (ENNReal.ofReal 20 * (K : ℝ≥0∞) * dudleyLSum T)) := by
      have hofB : Filter.Tendsto (fun n => ENNReal.ofReal (B n)) Filter.atTop (nhds 0) := by
        have := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hBlim
        simpa using! this
      have := (tendsto_const_nhds
        (x := ENNReal.ofReal 20 * (K : ℝ≥0∞) * dudleyLSum T)).add hofB
      simpa using this
    exact ge_of_tendsto' hCtendsto (fun n => hmain n)

end StatLean.ConcentrationInequalities
