module
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Pólya's theorem: pointwise convergence of distribution functions is uniform — ForMathlib brick

If nondecreasing functions `Fₙ : ℝ → ℝ` with limits `0` at `−∞` and `1` at `+∞` converge
pointwise to a **continuous** function `F` with the same tail limits, then the convergence is
**uniform** on `ℝ`:
$$ \sup_{x \in \mathbb{R}} |F_n(x) - F(x)| \longrightarrow 0 . $$

This is the bridge from "convergence in distribution" to "the approximation is uniform in the
argument", which every calibration argument (critical values, p-values, bootstrap thresholds)
needs before it may pass from a pointwise limit law to a statement about the level attained.

Mathlib-only; the conclusion is stated with Mathlib's `TendstoUniformly`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 11 (Basic Large-Sample
Theory), §11.2 (Weak Convergence and Central Limit Theorems), **Theorem 11.2.9** (Polyá's Theorem):
pointwise convergence of distribution functions to a continuous limit is uniform.
(`TSH4 §11.2 Thm 11.2.9`.)

**Proof formalization notes.**
* Standard proof: fix `ε > 0` and choose a finite grid `x₀ < ⋯ < x_k` with `F x₀ < ε`,
  `F x_k > 1 − ε` and `F xᵢ₊₁ − F xᵢ < ε` (continuity of `F` plus the tail limits make this
  possible — this is the only place continuity is used). On the grid, pointwise convergence
  gives a uniform-in-`i` bound for large `n`; between grid points, monotonicity of `Fₙ` and of
  `F` interpolates it; on the two tails the tail limits of `F` and of each `Fₙ` close the
  argument.
* Monotonicity of the limit `F` is *not* a hypothesis: it is forced by monotonicity of the
  `Fₙ` together with pointwise convergence, and is derived in the proof body.
* The tail limits of the approximants (`hFn_atBot`, `hFn_atTop`) are genuinely needed and not
  cosmetic: `Fₙ = F − n·1_{(−∞,−n)}` is nondecreasing and converges pointwise to a continuous
  distribution function while `sup |Fₙ − F| = n → ∞`. The helper
  `mem_Icc_of_monotone_of_tendsto` is what those hypotheses are used through.

**Bibliographic comments.** The theorem is due to G. Pólya ("Über den zentralen Grenzwertsatz
der Wahrscheinlichkeitsrechnung und das Momentenproblem," *Math. Z.* **8** (1920), 171–181),
where it is used to upgrade the central limit theorem to a uniform approximation statement.
-/

open Filter
open scoped Topology

namespace StatLean.HypothesisTesting

/-- A nondecreasing function with limits `0` at `−∞` and `1` at `+∞` takes values in `[0,1]`.

Helper for Pólya's theorem: this is what pins the approximants in the two tails. -/
theorem mem_Icc_of_monotone_of_tendsto {f : ℝ → ℝ}
    -- USER-INPUT: `f` is a distribution function — nondecreasing; classical
    (hmono : Monotone f)
    -- USER-INPUT: `f` is a distribution function — vanishing at `−∞`; classical
    (h0 : Tendsto f atBot (𝓝 0))
    -- USER-INPUT: `f` is a distribution function — total mass `1` at `+∞`; classical
    (h1 : Tendsto f atTop (𝓝 1))
    (x : ℝ) :
    f x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · exact le_of_tendsto h0 ((eventually_le_atBot x).mono fun y hy => hmono hy)
  · exact ge_of_tendsto h1 ((eventually_ge_atTop x).mono fun y hy => hmono hy)

/-- **Pólya's theorem**: pointwise convergence of distribution functions to a *continuous*
distribution function is uniform. -/
theorem tendstoUniformly_of_monotone_of_continuous {Fn : ℕ → ℝ → ℝ} {F : ℝ → ℝ}
    -- USER-INPUT: each approximant is a distribution function — nondecreasing; classical
    (hmono : ∀ n, Monotone (Fn n))
    -- USER-INPUT: each approximant vanishes at `−∞`; classical
    (hFn_atBot : ∀ n, Tendsto (Fn n) atBot (𝓝 0))
    -- USER-INPUT: each approximant has total mass `1` at `+∞`; classical
    (hFn_atTop : ∀ n, Tendsto (Fn n) atTop (𝓝 1))
    -- USER-INPUT: the limit is continuous — the hypothesis of the theorem; Pólya (1920)
    (hFcont : Continuous F)
    -- USER-INPUT: the limit vanishes at `−∞`; classical
    (hF_atBot : Tendsto F atBot (𝓝 0))
    -- USER-INPUT: the limit has total mass `1` at `+∞`; classical
    (hF_atTop : Tendsto F atTop (𝓝 1))
    -- USER-INPUT: pointwise convergence of the distribution functions; classical
    (hconv : ∀ x : ℝ, Tendsto (fun n => Fn n x) atTop (𝓝 (F x))) :
    TendstoUniformly Fn F atTop := by
  -- `F` is monotone: forced by monotonicity of the approximants and pointwise convergence.
  have hFmono : Monotone F := fun p q hpq =>
    le_of_tendsto_of_tendsto' (hconv p) (hconv q) fun n => hmono n hpq
  -- `[0,1]` bounds for the limit and each approximant.
  have hFIcc : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1 :=
    fun x => mem_Icc_of_monotone_of_tendsto hFmono hF_atBot hF_atTop x
  have hFnIcc : ∀ n x, Fn n x ∈ Set.Icc (0 : ℝ) 1 :=
    fun n x => mem_Icc_of_monotone_of_tendsto (hmono n) (hFn_atBot n) (hFn_atTop n) x
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  -- Work with `δ = ε / 2`.
  set δ : ℝ := ε / 2 with hδ_def
  have hδ0 : 0 < δ := by positivity
  -- Tail thresholds for `F`: `F < δ` far left, `F > 1 - δ` far right.
  obtain ⟨A₀, hA₀⟩ := eventually_atBot.mp (hF_atBot.eventually (eventually_lt_nhds hδ0))
  obtain ⟨B₀, hB₀⟩ :=
    eventually_atTop.mp (hF_atTop.eventually (eventually_gt_nhds (by linarith : (1 : ℝ) - δ < 1)))
  -- Pad to a genuine compact core `[a, b]` with `a < b`.
  set a : ℝ := min A₀ B₀ - 1 with ha_def
  set b : ℝ := max A₀ B₀ + 1 with hb_def
  have hab : a < b := by
    have h1 : min A₀ B₀ ≤ max A₀ B₀ := min_le_max
    rw [ha_def, hb_def]; linarith
  have hFa : ∀ y ≤ a, F y < δ := fun y hy =>
    hA₀ y (le_trans hy (by rw [ha_def]; have := min_le_left A₀ B₀; linarith))
  have hFb : ∀ y, b ≤ y → 1 - δ < F y := fun y hy =>
    hB₀ y (le_trans (by rw [hb_def]; have := le_max_right A₀ B₀; linarith) hy)
  -- Heine–Cantor: `F` is uniformly continuous on the compact core.
  have huc : UniformContinuousOn F (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hFcont.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη0, hη⟩ := huc δ hδ0
  -- Choose a uniform mesh of width `h < η`.
  obtain ⟨k, hk⟩ := exists_nat_gt ((b - a) / η)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (div_pos (by linarith) hη0).le hk
  have hkne : (k : ℝ) ≠ 0 := hk0.ne'
  set h : ℝ := (b - a) / k with hh_def
  have hh0 : 0 < h := by rw [hh_def]; exact div_pos (by linarith) hk0
  have hhne : h ≠ 0 := hh0.ne'
  have hkh : (k : ℝ) * h = b - a := by rw [hh_def, mul_comm]; exact div_mul_cancel₀ _ hkne
  have hhη : h < η := by
    have hba_lt : b - a < (k : ℝ) * η := by
      have := mul_lt_mul_of_pos_right hk hη0
      rwa [div_mul_cancel₀ _ hη0.ne'] at this
    have hlt : h * (k : ℝ) < η * (k : ℝ) := by
      rw [mul_comm h (k : ℝ), hkh, mul_comm η (k : ℝ)]; exact hba_lt
    exact lt_of_mul_lt_mul_right hlt hk0.le
  -- The mesh points `a + c·h` (for `0 ≤ c ≤ k`) live in the core.
  have hmem : ∀ c : ℝ, 0 ≤ c → c ≤ (k : ℝ) → a + c * h ∈ Set.Icc a b := by
    intro c hc0 hck
    refine ⟨by nlinarith [mul_nonneg hc0 hh0.le], ?_⟩
    have : c * h ≤ (k : ℝ) * h := mul_le_mul_of_nonneg_right hck hh0.le
    rw [hkh] at this; linarith
  -- Pointwise convergence at the finitely many mesh points, uniformly for large `n`.
  have hclose : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (k + 1),
      |Fn n (a + (i : ℝ) * h) - F (a + (i : ℝ) * h)| < δ := by
    rw [Finset.eventually_all]
    intro i _
    exact ((Metric.tendsto_nhds.mp (hconv (a + (i : ℝ) * h))) δ hδ0).mono
      fun n hn => by rwa [Real.dist_eq] at hn
  filter_upwards [hclose] with n hn
  intro x
  rw [Real.dist_eq, abs_sub_comm]
  have hFx := Set.mem_Icc.mp (hFIcc x)
  have hFnx := Set.mem_Icc.mp (hFnIcc n x)
  rcases le_or_gt x a with hxa | hxa
  · -- Left tail `x ≤ a`.
    have close0 := hn 0 (Finset.mem_range.mpr (by omega))
    rw [Nat.cast_zero, zero_mul, add_zero, abs_lt] at close0
    have hFa_x : F x < δ := hFa x hxa
    have hFax : F a < δ := hFa a le_rfl
    have hmono_x : Fn n x ≤ Fn n a := hmono n hxa
    rw [abs_sub_lt_iff]
    exact ⟨by linarith [hFx.1, close0.2], by linarith [hFnx.1, hFa_x]⟩
  · rcases le_or_gt b x with hxb | hxb
    · -- Right tail `b ≤ x`.
      have closek := hn k (Finset.mem_range.mpr (by omega))
      rw [show a + (k : ℝ) * h = b by rw [hkh]; ring, abs_lt] at closek
      have hFb_x : 1 - δ < F x := hFb x hxb
      have hFbx : 1 - δ < F b := hFb b le_rfl
      have hmono_x : Fn n b ≤ Fn n x := hmono n hxb
      rw [abs_sub_lt_iff]
      exact ⟨by linarith [hFnx.2, hFb_x], by linarith [hFx.2, closek.1]⟩
    · -- Interior `a < x < b`: locate `x` in mesh cell `[i, i+1]`.
      set t : ℝ := (x - a) / h with ht_def
      have ht0 : 0 ≤ t := by rw [ht_def]; exact div_nonneg (by linarith) hh0.le
      have hth : t * h = x - a := by rw [ht_def]; exact div_mul_cancel₀ _ hhne
      have htk : t < (k : ℝ) := by
        rw [ht_def, div_lt_iff₀ hh0]; linarith [hkh]
      set i : ℕ := ⌊t⌋₊ with hi_def
      have hi_le_t : (i : ℝ) ≤ t := Nat.floor_le ht0
      have ht_lt_i1 : t < (i : ℝ) + 1 := Nat.lt_floor_add_one t
      have hi_lt_k : i < k := (Nat.floor_lt ht0).mpr htk
      have hi1_le_k : i + 1 ≤ k := hi_lt_k
      have hxi_le : a + (i : ℝ) * h ≤ x := by
        have : (i : ℝ) * h ≤ t * h := mul_le_mul_of_nonneg_right hi_le_t hh0.le
        rw [hth] at this; linarith
      have hx_le_xi1 : x ≤ a + ((i : ℝ) + 1) * h := by
        have : t * h < ((i : ℝ) + 1) * h := mul_lt_mul_of_pos_right ht_lt_i1 hh0
        rw [hth] at this; linarith
      have close_i := hn i (Finset.mem_range.mpr (by omega))
      have close_i1 := hn (i + 1) (Finset.mem_range.mpr (by omega))
      push_cast at close_i1
      rw [abs_lt] at close_i close_i1
      -- Cell `F`-width `< δ` from uniform continuity (`|x_{i+1} - x_i| = h < η`).
      have hcell : |F (a + (i : ℝ) * h) - F (a + ((i : ℝ) + 1) * h)| < δ := by
        have hmi : a + (i : ℝ) * h ∈ Set.Icc a b :=
          hmem (i : ℝ) (by positivity) (by exact_mod_cast hi_lt_k.le)
        have hmi1 : a + ((i : ℝ) + 1) * h ∈ Set.Icc a b :=
          hmem ((i : ℝ) + 1) (by positivity) (by exact_mod_cast hi1_le_k)
        have hdist : dist (a + (i : ℝ) * h) (a + ((i : ℝ) + 1) * h) < η := by
          rw [Real.dist_eq, show a + (i : ℝ) * h - (a + ((i : ℝ) + 1) * h) = -h by ring,
            abs_neg, abs_of_pos hh0]
          exact hhη
        have := hη _ hmi _ hmi1 hdist
        rwa [Real.dist_eq] at this
      rw [abs_lt] at hcell
      have hm1 : Fn n (a + (i : ℝ) * h) ≤ Fn n x := hmono n hxi_le
      have hm2 : Fn n x ≤ Fn n (a + ((i : ℝ) + 1) * h) := hmono n hx_le_xi1
      have hM1 : F (a + (i : ℝ) * h) ≤ F x := hFmono hxi_le
      have hM2 : F x ≤ F (a + ((i : ℝ) + 1) * h) := hFmono hx_le_xi1
      rw [abs_sub_lt_iff]
      exact ⟨by linarith [hm2, hM1, close_i1.2, hcell.1],
        by linarith [hm1, hM2, close_i.1, hcell.1]⟩

end StatLean.HypothesisTesting
