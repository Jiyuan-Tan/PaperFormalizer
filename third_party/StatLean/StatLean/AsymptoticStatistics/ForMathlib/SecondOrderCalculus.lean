module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas

@[expose] public section

/-!
# Second-order calculus bricks for the classical Z-estimator (vdV §*5.6)

Theorem-agnostic (`ForMathlib` layer) helpers used by the local-maximum assertion of
vdV Theorem 5.42 (`ClassicalZEstimator/GradientLocalMax.lean`) and by the diagonal
δ-extraction of the root-existence proof (`ClassicalZEstimator/RootExistence.lean`).

Contents:

* `isLocalMax_of_negdef_hessian` (U) — a point `θ₀` that is a critical point of `f`
  (no first-order term) with a **negative-definite** Hessian `H` (`⟪x, Hx⟫ ≤ −c‖x‖²`)
  and a second-order little-o Taylor expansion is a local maximum of `f`.
* `hessian_negSemidef_of_isLocalMax` — the second-order **necessary** condition: at an
  interior local maximum with a second-order Taylor expansion, the Hessian `H` is
  negative semidefinite (`⟪x, Hx⟫ ≤ 0`).
* `exists_seq_tendsto_zero_of_forall_tendsto` — the standard diagonal argument: from a
  family of probabilities `p n δ ≤ 1` with `p n δ →ₙ 1` for every fixed `δ > 0`, extract
  a sequence `δₙ ↓ 0` with `p n (δₙ) →ₙ 1`.

The Hessian is represented as a `Matrix (Fin k) (Fin k) ℝ` acting through
`Matrix.toEuclideanCLM`, matching the encoding of `MEstimator/ArgmaxLocalization.lean`.
The second-order Taylor form (little-o remainder + no linear term) packages "critical
point" and "locally Lipschitz Hessian" into a single hypothesis; it is the honest
mathematical content and matches the `hTaylor` convention of the M-estimator theorem
(vdV 5.23).
-/

open Filter
open scoped RealInnerProductSpace Matrix Topology

namespace AsymptoticStatistics

/-- **U: a critical point with negative-definite Hessian is a local maximum.**

If `f` admits the second-order little-o expansion
`f θ − f θ₀ = ½⟪θ − θ₀, H(θ − θ₀)⟫ + o(‖θ − θ₀‖²)` (the absence of a linear term encodes
"`θ₀` is a critical point") and `H` is uniformly negative definite
(`⟪x, Hx⟫ ≤ −c‖x‖²`, `c > 0`), then `θ₀` is a local maximum of `f`. Route: the quadratic
term is `≤ −(c/2)‖θ − θ₀‖²`, which eventually dominates the `o(‖θ − θ₀‖²)` remainder, so
`f θ ≤ f θ₀` near `θ₀`. -/
theorem isLocalMax_of_negdef_hessian {k : ℕ}
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (H : Matrix (Fin k) (Fin k) ℝ) {c : ℝ} (hc : 0 < c)
    (hHneg : ∀ x : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) H x⟫ ≤ - c * ‖x‖ ^ 2)
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => f θ - f θ₀ - (1 / 2) *
        ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) H (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2)) :
    IsLocalMax f θ₀ := by
  have hc4 : (0 : ℝ) < c / 4 := by linarith
  have h := hTaylor.def hc4
  filter_upwards [h] with θ hθ
  have hq := hHneg (θ - θ₀)
  have hnorm : ‖(‖θ - θ₀‖ ^ 2 : ℝ)‖ = ‖θ - θ₀‖ ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
  rw [hnorm, Real.norm_eq_abs, abs_le] at hθ
  nlinarith [hθ.2, hq, sq_nonneg ‖θ - θ₀‖]

/-- **Second-order necessary condition.** At an interior local maximum `θ₀` of `f` that
admits the second-order little-o expansion
`f θ − f θ₀ = ½⟪θ − θ₀, H(θ − θ₀)⟫ + o(‖θ − θ₀‖²)`, the (symmetric) Hessian `H` is
negative semidefinite: `⟪x, Hx⟫ ≤ 0` for every `x`. Route: probe along the ray
`θ = θ₀ + t x`, `t ↓ 0`; `f(θ₀ + t x) ≤ f θ₀` forces `½ t²⟪x, Hx⟫ + o(t²) ≤ 0`, and
dividing by `t²` and letting `t ↓ 0` gives `⟪x, Hx⟫ ≤ 0`. -/
theorem hessian_negSemidef_of_isLocalMax {k : ℕ}
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (H : Matrix (Fin k) (Fin k) ℝ)
    (hmax : IsLocalMax f θ₀)
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => f θ - f θ₀ - (1 / 2) *
        ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) H (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2)) :
    ∀ x : EuclideanSpace ℝ (Fin k),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) H x⟫ ≤ 0 := by
  intro x
  by_contra hcon'
  have hcon : 0 < ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) H x⟫ := not_le.mp hcon'
  clear hcon'
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hcon
  have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
  have hxne : (‖x‖ : ℝ) ≠ 0 := ne_of_gt hxpos
  set q : ℝ := ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) H x⟫ with hqdef
  set ε : ℝ := q / (4 * ‖x‖ ^ 2) with hεdef
  have hεpos : 0 < ε := div_pos hcon (by positivity)
  have hεx : ε * ‖x‖ ^ 2 = q / 4 := by
    rw [hεdef]; field_simp
  -- pull the two `𝓝 θ₀`-eventual facts back along the ray `t ↦ θ₀ + t • x`
  have hT := hTaylor.def hεpos
  have hcont : Continuous fun t : ℝ => θ₀ + t • x :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hγ : Tendsto (fun t : ℝ => θ₀ + t • x) (𝓝[>] (0 : ℝ)) (𝓝 θ₀) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    simpa using hcont.tendsto 0
  have hpos_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t := eventually_mem_nhdsWithin
  obtain ⟨t, ht_pos, hmax_t, hbd_t⟩ := (hpos_ev.and (hγ.eventually (hmax.and hT))).exists
  -- along the ray the quadratic form and the norm scale by `t²`
  have hsub : θ₀ + t • x - θ₀ = t • x := by abel
  rw [hsub] at hbd_t
  have hinner :
      ⟪t • x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) H (t • x)⟫ = t ^ 2 * q := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, hqdef]; ring
  have hnrm : ‖(t : ℝ) • x‖ = t * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
  rw [hinner, hnrm, Real.norm_of_nonneg (sq_nonneg (t * ‖x‖)), Real.norm_eq_abs,
    abs_le] at hbd_t
  have hkey : ε * (t * ‖x‖) ^ 2 = t ^ 2 * q / 4 := by
    have h1 : ε * (t * ‖x‖) ^ 2 = t ^ 2 * (ε * ‖x‖ ^ 2) := by ring
    rw [h1, hεx]; ring
  have ht2q : 0 < t ^ 2 * q := mul_pos (pow_pos ht_pos 2) hcon
  linarith [hbd_t.1, hmax_t, hkey, ht2q]

/-- **Diagonal δ-extraction.** Given a doubly-indexed family of "probabilities"
`p n δ ≤ 1` such that for every fixed `δ > 0` the section `n ↦ p n δ` tends to `1`, there
is a sequence `δₙ ↓ 0` (all positive) with `n ↦ p n (δₙ)` still tending to `1`. Standard
diagonal argument: choose increasing thresholds `Nₘ` with `p n (1/m) ≥ 1 − 1/m` for
`n ≥ Nₘ`, set `δₙ := 1/m(n)` for the largest `m` with `Nₘ ≤ n`, and squeeze between
`1 − 1/m(n) → 1` and the upper bound `1`. -/
theorem exists_seq_tendsto_zero_of_forall_tendsto
    (p : ℕ → ℝ → ℝ) (hp_le : ∀ n δ, p n δ ≤ 1)
    (hp : ∀ δ : ℝ, 0 < δ → Tendsto (fun n => p n δ) atTop (𝓝 1)) :
    ∃ δseq : ℕ → ℝ, (∀ n, 0 < δseq n) ∧ Tendsto δseq atTop (𝓝 0)
      ∧ Tendsto (fun n => p n (δseq n)) atTop (𝓝 1) := by
  -- Step 1: for each `m`, a threshold past which `p n (1/(m+1))` is within `1/(m+1)` of `1`.
  have key : ∀ m : ℕ, ∃ Nm : ℕ, ∀ n, Nm ≤ n →
      1 - 1 / (m + 1 : ℝ) ≤ p n (1 / (m + 1 : ℝ)) := by
    intro m
    have hpos : (0 : ℝ) < 1 / (m + 1) := by positivity
    obtain ⟨Nm, hNm⟩ := Metric.tendsto_atTop.mp (hp _ hpos) (1 / (m + 1)) hpos
    refine ⟨Nm, fun n hn => ?_⟩
    have h := hNm n hn
    rw [Real.dist_eq, abs_lt] at h
    linarith [h.1]
  choose N hN using key
  -- Step 2: inflate the thresholds so that `m ≤ N' m` (needed for `Nat.le_findGreatest`).
  obtain ⟨N', hN'_ge, hN_le⟩ : ∃ N' : ℕ → ℕ, (∀ m, m ≤ N' m) ∧ (∀ m, N m ≤ N' m) :=
    ⟨fun m => max m (N m), fun m => le_max_left _ _, fun m => le_max_right _ _⟩
  -- Step 3: the diagonal index `M n = ` the largest `m ≤ n` whose threshold has been passed.
  obtain ⟨M, hM_ge, hM_spec⟩ : ∃ M : ℕ → ℕ,
      (∀ m n, N' m ≤ n → m ≤ M n) ∧ (∀ n, N' 0 ≤ n → N' (M n) ≤ n) := by
    refine ⟨fun n => Nat.findGreatest (fun m => N' m ≤ n) n, fun m n hn => ?_, fun n hn => ?_⟩
    · exact Nat.le_findGreatest (le_trans (hN'_ge m) hn) hn
    · exact Nat.findGreatest_spec (P := fun m => N' m ≤ n) (Nat.zero_le n) hn
  -- Step 4: `δseq n := 1/(M n + 1)` tends to `0`, because `M n → ∞`.
  have hδ0 : Tendsto (fun n => 1 / (M n + 1 : ℝ)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    refine ⟨N' m, fun n hn => ?_⟩
    have hMn : (m : ℝ) + 1 ≤ (M n : ℝ) + 1 := by
      have := hM_ge m n hn
      exact_mod_cast Nat.succ_le_succ this
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    calc 1 / (M n + 1 : ℝ) ≤ 1 / (m + 1 : ℝ) :=
          one_div_le_one_div_of_le (by positivity) hMn
      _ < ε := hm
  -- Step 5: squeeze `p n (δseq n)` between `1 − 1/(M n + 1)` and `1`.
  refine ⟨fun n => 1 / (M n + 1 : ℝ), fun n => by positivity, hδ0, ?_⟩
  have hlow : Tendsto (fun n => 1 - 1 / (M n + 1 : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hδ0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall fun n => hp_le _ _)
  filter_upwards [eventually_ge_atTop (N' 0)] with n hn
  exact hN (M n) n (le_trans (hN_le (M n)) (hM_spec n hn))

end AsymptoticStatistics
