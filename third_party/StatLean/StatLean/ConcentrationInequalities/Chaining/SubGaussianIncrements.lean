module
public import StatLean.ConcentrationInequalities.Orlicz.Defs
public import StatLean.ConcentrationInequalities.Orlicz.SubGaussianTail
public import StatLean.ConcentrationInequalities.Orlicz.SubGaussianMGF
public import StatLean.ConcentrationInequalities.Orlicz.Attainment
public import StatLean.ConcentrationInequalities.SubGaussian.Defs

@[expose] public section

/-!
# Sub-gaussian increments of a random process

A random process $(X_t)_{t \in T}$ on a pseudo-metric space $(T, d)$ has
*sub-gaussian increments* with parameter $K \ge 0$ if
$$ \|X_t - X_s\|_{\psi_2} \;\le\; K\, d(s,t) \qquad \text{for all } s, t \in T. $$
This file defines the carrier `SubGaussianIncrements` and derives from it the
two probabilistic consequences every chaining argument consumes: the
per-increment Gaussian tail
$\mathbb{P}(|X_t - X_s| \ge \tau) \le 2\exp(-\tau^2/(K d(s,t))^2)$
and the per-increment MGF bound
(`HasSubgaussianMGF` with variance proxy $3 (K d(s,t))^2$).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.1, Definition 8.1.1, Eq. (8.1); the tail
consequence is Eq. (8.3)-flavored and the MGF consequence is Step 2 of the
proof of Theorem 8.1.4.

**Proof formalization notes.** ALL consumption of the Orlicz bridge lemmas
(B1 tail `measure_abs_ge_le_of_subGaussianNorm_le`, B2 MGF
`hasSubgaussianMGF_of_subGaussianNorm_le`) is confined to this file and to
`Chaining/PsiTwoMaximal.lean`; downstream chaining files consume only the
lemmas here. Constants: B1 is normalized with $c = 1$ (tail
$2\exp(-\tau^2/L^2)$) and B2 with $C = 3$ (variance proxy $3L^2$), frozen
numerals `2` and `3`. The index set `T : Set E` is an explicit argument
(applications only control increments on the class); `K : ℝ≥0` carries **no**
`K ≠ 0` hypothesis (book: "∃ K ≥ 0") — the `K = 0` and `dist = 0` corners are
handled by `ae_eq_zero_of_subGaussianNorm_eq_zero`, which is a thin
instantiation of `Orlicz/Attainment.orliczNorm_eq_zero_iff` at `ψ = psiTwo`
(no independent derivation). The mean-zero hypothesis of
`hasSubgaussianMGF_sub` is stated **on the increment**
(`∫ (X t − X s) dμ = 0`), which is junk-proof for non-integrable `X t`.
Named-sorry fallback of this work item: `ae_eq_zero_of_subGaussianNorm_eq_zero`
(the `psiTwo` instantiation plumbing), keeping the two bridge repackagings
proved.

**Bibliographic comments.** Processes with sub-gaussian increments as the
natural setting for chaining go back to R. M. Dudley, "The sizes of compact
subsets of Hilbert space and continuity of Gaussian processes," *J. Funct.
Anal.* 1 (1967), 290–330, abstracting Kolmogorov's continuity criterion
(1930s); the ψ₂-increment formulation used here follows Talagrand, *Upper
and Lower Bounds for Stochastic Processes*, Springer 2014, §2.2.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*} [PseudoMetricSpace E]
variable {μ : Measure Ω} {X : E → Ω → ℝ} {K : ℝ≥0} {T : Set E} {s t : E}

/-- **Sub-gaussian increments** (HDP §8.1, Definition 8.1.1, Eq. (8.1)):
the process `X` indexed by the pseudo-metric space `E` has sub-gaussian
increments with parameter `K` on the index set `T` if
`‖X t − X s‖_{ψ₂} ≤ K · d(s,t)` for all `s, t ∈ T`, stated with `edist` so
the inequality lives in `ℝ≥0∞` (the ψ₂-norm carrier). Edge behavior: `K = 0`
or `dist s t = 0` forces `subGaussianNorm = 0`, i.e. `X t = X s` a.e.
(see `ae_eq_zero_of_subGaussianNorm_eq_zero`); no `K ≠ 0` hypothesis is
carried. -/
def SubGaussianIncrements (X : E → Ω → ℝ) (K : ℝ≥0) (T : Set E)
    (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ s ∈ T, ∀ t ∈ T, subGaussianNorm (fun ω => X t ω - X s ω) μ ≤ (K : ℝ≥0∞) * edist s t

/-- Restriction of sub-gaussian increments to a subset of the index set. -/
lemma SubGaussianIncrements.mono_set (h : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: restriction to a sub-index-set; no scope change; HDP §8.1
    {S : Set E} (hST : S ⊆ T) :
    SubGaussianIncrements X K S μ := fun s hs t ht => h s (hST hs) t (hST ht)

/-- Weakening the increment parameter. -/
lemma SubGaussianIncrements.mono_const (h : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: monotone weakening of the constant; no scope change; HDP §8.1
    {K' : ℝ≥0} (hK : K ≤ K') :
    SubGaussianIncrements X K' T μ := by
  intro s hs t ht
  refine (h s hs t ht).trans ?_
  exact mul_le_mul_left (by exact_mod_cast hK) _

/-- A random variable with vanishing ψ₂-norm vanishes a.e.

Thin instantiation of `orliczNorm_eq_zero_iff` (`Orlicz/Attainment.lean`) at
`ψ = psiTwo` — no independent derivation. Needed for the pseudometric
`dist = 0` chain ends and the `K = 0` corner of chaining. Stated *without*
`IsProbabilityMeasure`. -/
lemma ae_eq_zero_of_subGaussianNorm_eq_zero {Y : Ω → ℝ}
    -- LEAN-ONLY: a.e.-measurability so the Orlicz zero-iff applies; HDP §8.1
    (hm : AEMeasurable Y μ)
    -- LEAN-ONLY: vanishing ψ₂-norm, the degenerate-increment input; HDP §8.1
    (h : subGaussianNorm Y μ = 0) :
    Y =ᵐ[μ] 0 := by
  rw [subGaussianNorm_def] at h
  exact (orliczNorm_eq_zero_iff psiTwo_monotoneOn psiTwo_zero.le
    psiTwo_tendsto_atTop hm).mp h

/-- Pseudometric chain-end identification: indices at distance `0` carry
a.e.-equal process values (HDP §8.1, the `T_K = T` step in the proof of
Theorem 8.1.4, adapted to pseudo-metric index sets). -/
lemma SubGaussianIncrements.sub_ae_eq_zero (h : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: a.e.-measurability of the two coordinates; HDP §8.1
    (hms : AEMeasurable (X s) μ) (hmt : AEMeasurable (X t) μ)
    -- LEAN-ONLY: membership in the index set; HDP §8.1
    (hs : s ∈ T) (ht : t ∈ T)
    -- LEAN-ONLY: zero pseudo-distance (the pseudometric degeneracy); HDP §8.1
    (hd : dist s t = 0) :
    (fun ω => X t ω - X s ω) =ᵐ[μ] 0 := by
  have hedist : edist s t = 0 := by rw [edist_dist, hd]; simp
  have hle := h s hs t ht
  rw [hedist, mul_zero, nonpos_iff_eq_zero] at hle
  exact ae_eq_zero_of_subGaussianNorm_eq_zero (hmt.sub hms) hle

/-- **Increment tail bound** (HDP §8.1, Eq. (8.3) flavor): a sub-gaussian
increment satisfies the Gaussian-type tail
`μ {|X_t − X_s| ≥ τ} ≤ 2 exp(−τ²/(K d(s,t))²)`. Bridge-B1 consumption,
normalization `c = 1` frozen. -/
theorem SubGaussianIncrements.measure_abs_sub_ge_le
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Definition 8.1.1
    (h : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B1
    (hms : AEMeasurable (X s) μ) (hmt : AEMeasurable (X t) μ)
    -- LEAN-ONLY: membership in the index set; HDP §8.1
    (hs : s ∈ T) (ht : t ∈ T)
    -- LEAN-ONLY: non-degenerate scale so the tail RHS is meaningful; the
    -- degenerate case is `sub_ae_eq_zero`
    (hK : 0 < (K : ℝ) * dist s t)
    -- USER-INPUT: τ ≥ 0; HDP §8.1
    {τ : ℝ} (hτ : 0 ≤ τ) :
    μ {ω | τ ≤ |X t ω - X s ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-τ ^ 2 / ((K : ℝ) * dist s t) ^ 2)) := by
  set K' : ℝ≥0 := K * nndist s t with hK'def
  have hcoe : (K' : ℝ) = (K : ℝ) * dist s t := by
    rw [hK'def, NNReal.coe_mul, coe_nndist]
  have hbound : subGaussianNorm (fun ω => X t ω - X s ω) μ ≤ (K' : ℝ≥0∞) := by
    have hh := h s hs t ht
    rwa [edist_nndist, ← ENNReal.coe_mul] at hh
  have hK'pos : 0 < K' := by rw [← NNReal.coe_pos, hcoe]; exact hK
  have hmain := measure_abs_ge_le_of_subGaussianNorm_le (hmt.sub hms) hK'pos hbound hτ
  rwa [hcoe] at hmain

/-- **Increment MGF bound** (HDP §8.1, proof of Theorem 8.1.4, Step 2): a
mean-zero sub-gaussian increment has `HasSubgaussianMGF` with variance proxy
`3 (K d(s,t))²`. Bridge-B2 consumption, constant `C = 3` frozen. The
mean-zero hypothesis is on the **increment** (junk-proof for non-integrable
coordinates). -/
theorem SubGaussianIncrements.hasSubgaussianMGF_sub
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Definition 8.1.1
    (h : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B2
    (hms : AEMeasurable (X s) μ) (hmt : AEMeasurable (X t) μ)
    -- LEAN-ONLY: membership in the index set; HDP §8.1
    (hs : s ∈ T) (ht : t ∈ T)
    -- USER-INPUT: mean-zero increment; HDP §8.1, Theorem 8.1.4 hypothesis
    (hmean : ∫ ω, (X t ω - X s ω) ∂μ = 0) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => X t ω - X s ω)
      (3 * (K * nndist s t) ^ 2) μ := by
  set K' : ℝ≥0 := K * nndist s t with hK'def
  have hbound : subGaussianNorm (fun ω => X t ω - X s ω) μ ≤ (K' : ℝ≥0∞) := by
    have hh := h s hs t ht
    rwa [edist_nndist, ← ENNReal.coe_mul] at hh
  rcases eq_or_lt_of_le (zero_le (a := K')) with hK0 | hK0
  · -- degenerate scale `K' = 0`: the increment vanishes a.e.
    have hz : subGaussianNorm (fun ω => X t ω - X s ω) μ = 0 := by
      have hle : subGaussianNorm (fun ω => X t ω - X s ω) μ ≤ 0 := by
        rw [← hK0] at hbound; simpa using hbound
      exact le_antisymm hle (zero_le)
    have hae : (fun ω => X t ω - X s ω) =ᵐ[μ] 0 :=
      ae_eq_zero_of_subGaussianNorm_eq_zero (hmt.sub hms) hz
    have hgoal : (3 * K' ^ 2 : ℝ≥0) = 0 := by rw [← hK0]; ring
    rw [hgoal]
    exact (ProbabilityTheory.HasSubgaussianMGF.zero).congr hae.symm
  · -- non-degenerate scale: bridge B2
    exact hasSubgaussianMGF_of_subGaussianNorm_le (hmt.sub hms) hK0 hbound hmean

/-- Repackaging of `hasSubgaussianMGF_sub` into the project carrier
`IsSubGaussian` (the centering in `IsSubGaussian` is a no-op under `hmean`). -/
theorem SubGaussianIncrements.isSubGaussian_sub
    -- USER-INPUT: probability-space context; HDP §8.1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: sub-gaussian increments Eq (8.1); HDP §8.1, Definition 8.1.1
    (h : SubGaussianIncrements X K T μ)
    -- LEAN-ONLY: a.e.-measurability, required by the Orlicz bridge B2
    (hms : AEMeasurable (X s) μ) (hmt : AEMeasurable (X t) μ)
    -- LEAN-ONLY: membership in the index set; HDP §8.1
    (hs : s ∈ T) (ht : t ∈ T)
    -- USER-INPUT: mean-zero increment; HDP §8.1, Theorem 8.1.4 hypothesis
    (hmean : ∫ ω, (X t ω - X s ω) ∂μ = 0) :
    IsSubGaussian (fun ω => X t ω - X s ω) (3 * (K * nndist s t) ^ 2) μ := by
  rw [isSubGaussian_iff, hmean]
  simp only [sub_zero]
  exact hasSubgaussianMGF_sub h hms hmt hs ht hmean

end StatLean.ConcentrationInequalities
