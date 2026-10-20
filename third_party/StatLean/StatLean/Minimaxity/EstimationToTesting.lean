module
public import StatLean.Minimaxity.Defs

@[expose] public section

/-!
# From estimation to testing (Proposition 15.1)

The fundamental reduction underlying every minimax lower bound in the chapter: the minimax
risk is lower bounded by $\Phi(\delta)$ times the error probability of an $M$-ary hypothesis
test built from a $2\delta$-separated family.

Fix an increasing distortion function $\Phi$ and a finite family of parameters
$\{\theta^1,\dots,\theta^M\}$ that is **$2\delta$-separated** in the semimetric $\rho$ on the
functional values, i.e. $\rho\big(g(\theta^j), g(\theta^k)\big) \ge 2\delta$ for all $j \ne k$.
Let $J$ be uniform on $\{1,\dots,M\}$ and, given $J$, draw $Z$ from $P_{\theta^J}$, and write
$\mathbb{Q}$ for the joint law of $(Z, J)$. Then the minimax risk for estimating the functional
$g(\theta)$ under the distortion loss $\Phi\circ\rho$ satisfies
$$
  \mathfrak{M}\big(g(\theta);\,\Phi\circ\rho\big)
    \;\ge\; \Phi(\delta)\,\cdot\, \inf_{\psi}\; \mathbb{Q}\big[\psi(Z) \ne J\big],
  \qquad (\text{Eq. } (15.3))
$$
where the infimum runs over all (randomized) tests $\psi$. In the Lean statement the right-hand
testing error is `multiwayTestingError`, the loss is `distortionLoss Φ g`, the family is
`θfam : Fin M → Θ`, separation is the hypothesis `IsSeparatedFamily g θfam δ`, and "increasing"
is `Monotone Φ`; the semimetric $\rho$ is taken to be the extended distance `edist` on the
functional values $g(\theta)$.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2, Proposition 15.1,
Eq. (15.3).

**Proof formalization notes.** Restricting the supremum over `𝒫` to the finite subfamily can only
decrease it (`minimaxRisk_precomp_le`), and the maximum over the subfamily dominates the uniform
average — the Bayes risk — via `bayesRisk_le_avgRisk`. The geometric core (Wainwright Figure 15.1)
is that the nearest-point test $\psi(Z) = \arg\min_\ell \rho\big(\hat\theta, g(\theta^\ell)\big)$
errs only when $\rho\big(\hat\theta, g(\theta^J)\big) \ge \delta$: by the triangle inequality and
$2\delta$-separation, a wrong test answer forces $\rho \ge \delta$, so by monotonicity of $\Phi$,
$\mathbb{E}\big[\Phi(\rho(\hat\theta, g(\theta^J)))\big] \ge \Phi(\delta)\,\mathbb{P}[\psi \ne J]$.
Measurability of the $\arg\min$ selector is supplied by `exists_measurable_nearestPoint` under the
`[OpensMeasurableSpace Ω]` instance, which makes each distance $y \mapsto \mathrm{edist}(g(\theta^\ell), y)$
continuous, hence measurable.

**Bibliographic comments.** This estimation-to-testing reduction is **folklore** with no single
seminal origin: it is the common abstract scaffold behind the classical Le Cam, Assouad, and Fano
lower-bound methods. The idea of reducing estimation to a multiple-hypothesis testing problem and
bounding the minimax risk by a separation $\times$ testing-error product traces to L. Le Cam,
*Convergence of estimates under dimensionality restrictions*, Annals of Statistics 1 (1973),
38–53, and to I. A. Ibragimov and R. Z. Has'minskii, *Statistical Estimation: Asymptotic Theory*
(Springer, 1981). The packaging used here — increasing distortion $\Phi$, $2\delta$-separated
family, and the nearest-point test — follows Wainwright's Proposition 15.1 and the survey
exposition of B. Yu, *Assouad, Fano, and Le Cam*, in *Festschrift for Lucien Le Cam* (Springer,
1997), 423–435. No original research paper states exactly Eq. (15.3) in this form; it is textbook
synthesis.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {Θ Ω 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [mΩ : MeasurableSpace Ω]
  [m𝓧 : MeasurableSpace 𝓧]

/-- **Restricting to a sub-family decreases the minimax risk.** For a measurable reindexing
`e : ι → Θ`, the minimax risk of the pulled-back model `P.comap e` with the precomposed loss is at
most the minimax risk of the full model: restricting the supremum over parameters to the image of
`e` can only decrease it. This is the first step of Wainwright's Proposition 15.1 (§15.1.2). -/
private lemma minimaxRisk_precomp_le {𝓨 ι : Type*} [MeasurableSpace 𝓨] [MeasurableSpace ι]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (e : ι → Θ) (he : Measurable e) :
    minimaxRisk (fun i => ℓ (e i)) (P.comap e he) ≤ minimaxRisk ℓ P := by
  refine iInf₂_mono fun κ _ => iSup_le fun i => le_iSup_of_le (e i) ?_
  have hcomp : (κ ∘ₖ (P.comap e he)) i = (κ ∘ₖ P) (e i) := by
    rw [Kernel.comp_apply, Kernel.comp_apply, Kernel.comap_apply]
  rw [hcomp]

/-- **Measurable nearest-point selector.** On a pseudo-EMetric space carrying its Borel structure
(`[OpensMeasurableSpace Ω]`), the index `ℓ ∈ Fin M` minimizing `edist (g (θfam ℓ)) y` can be chosen
measurably in `y`. Each distance `y ↦ edist (g (θfam ℓ)) y` is continuous, hence measurable; the
argmin is built via `Nat.find` over `ℕ` (cast into `Fin M`), whose minimizer-predicate has a
measurable witness set (a finite intersection of `{y | dₗ y ≤ d_k y}`), so `measurable_find` applies.
Reused by `LeCam/ConvexHull.lean`. -/
private lemma exists_measurable_nearestPoint
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {M : ℕ} [NeZero M]
    (g : Θ → Ω) (θfam : Fin M → Θ) :
    ∃ T : Ω → Fin M, Measurable T ∧
      ∀ y ℓ, edist (g (θfam (T y))) y ≤ edist (g (θfam ℓ)) y := by
  classical
  -- Each distance `dₗ : y ↦ edist (g (θfam ℓ)) y` is continuous, hence measurable.
  have hmeas : ∀ ℓ : Fin M, Measurable (fun y => edist (g (θfam ℓ)) y) :=
    fun ℓ => (continuous_const.edist continuous_id).measurable
  -- Predicate: `n` (cast into `Fin M`) is a minimizer of the distance at `y`.
  set p : Ω → ℕ → Prop :=
    fun y n => ∀ j : Fin M, edist (g (θfam (Fin.ofNat M n))) y ≤ edist (g (θfam j)) y with hp
  -- A minimizer always exists (`Fin M` is finite and nonempty).
  have hex : ∀ y, ∃ n, p y n := by
    intro y
    obtain ⟨ℓ₀, hℓ₀⟩ := Finite.exists_min (fun ℓ => edist (g (θfam ℓ)) y)
    refine ⟨ℓ₀.val, fun j => ?_⟩
    have hval : Fin.ofNat M ℓ₀.val = ℓ₀ := Fin.ext (Nat.mod_eq_of_lt ℓ₀.isLt)
    rw [hval]
    exact hℓ₀ j
  -- The minimizer-witness set is a finite intersection of measurable `≤`-sets.
  have hpmeas : ∀ n, MeasurableSet {y | p y n} := by
    intro n
    simp only [hp, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_le (hmeas _) (hmeas j)
  refine ⟨fun y => Fin.ofNat M (Nat.find (hex y)), ?_, fun y ℓ => Nat.find_spec (hex y) ℓ⟩
  exact (measurable_from_nat (f := Fin.ofNat M)).comp (measurable_find hex hpmeas)

/-- **Geometric core of Proposition 15.1 given a measurable nearest-point selector.** If the test
`T : Ω → Fin M` is measurable and its value at `y` realizes the nearest functional value
`g (θfam (T y))` to `y`, then `Φ(δ)` times the M-ary testing error of the sub-model is at most the
(restricted) minimax risk.
The estimation-to-testing reduction (Wainwright §15.1.2, Figure 15.1): post-compose any estimator
`κ` with `T` to obtain a test, and use the `2δ`-separation to bound the 0–1 loss by `Φ(ρ)/Φ(δ)`. -/
private lemma mul_multiwayTestingError_le
    [PseudoEMetricSpace Ω] {M : ℕ} [NeZero M]
    {Φ : ℝ≥0∞ → ℝ≥0∞} {g : Θ → Ω} (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    {θfam : Fin M → Θ} (hθ : Measurable θfam) {δ : ℝ≥0∞}
    (hΦ : Monotone Φ) (hsep : IsSeparatedFamily g θfam δ)
    {T : Ω → Fin M} (hT : Measurable T)
    (hTmin : ∀ y ℓ, edist (g (θfam (T y))) y ≤ edist (g (θfam ℓ)) y) :
    Φ δ * multiwayTestingError (P.comap θfam hθ)
      ≤ minimaxRisk (fun j => distortionLoss Φ g (θfam j)) (P.comap θfam hθ) := by
  set Q := P.comap θfam hθ with hQ
  haveI : IsMarkovKernel Q := Kernel.IsMarkovKernel.comap P hθ
  -- Pointwise geometric bound: `Φ(δ)·𝟙[T y ≠ j] ≤ Φ(ρ(g(θfam j), y))`.
  have hpt : ∀ (j : Fin M) (y : Ω),
      Φ δ * zeroOneLoss M j (T y) ≤ distortionLoss Φ g (θfam j) y := by
    intro j y
    unfold distortionLoss zeroOneLoss
    by_cases hjy : j = T y
    · simp [hjy]
    · rw [if_neg hjy, mul_one]
      apply hΦ
      have hsep' := hsep j (T y) hjy
      have htri : edist (g (θfam j)) (g (θfam (T y)))
          ≤ edist (g (θfam j)) y + edist (g (θfam (T y))) y := by
        calc edist (g (θfam j)) (g (θfam (T y)))
            ≤ edist (g (θfam j)) y + edist y (g (θfam (T y))) := edist_triangle _ _ _
          _ = edist (g (θfam j)) y + edist (g (θfam (T y))) y := by rw [edist_comm y]
      have hmin := hTmin y j
      have h2 : 2 * δ ≤ 2 * edist (g (θfam j)) y := by
        calc 2 * δ ≤ edist (g (θfam j)) (g (θfam (T y))) := hsep'
          _ ≤ edist (g (θfam j)) y + edist (g (θfam (T y))) y := htri
          _ ≤ edist (g (θfam j)) y + edist (g (θfam j)) y := by gcongr
          _ = 2 * edist (g (θfam j)) y := (two_mul _).symm
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
  -- Reduce the minimax risk to a per-estimator bound.
  rw [multiwayTestingError, minimaxRisk]
  refine le_iInf₂ fun κ hκ => ?_
  haveI := hκ
  -- The post-composed test `ψ = T ∘ κ`.
  haveI : IsMarkovKernel (Kernel.deterministic T hT) := Kernel.isMarkovKernel_deterministic hT
  set ψ : Kernel 𝓧 (Fin M) := (Kernel.deterministic T hT).comp κ with hψ
  have hψcomp : ψ ∘ₖ Q = (κ ∘ₖ Q).map T := by
    rw [hψ, Kernel.comp_assoc, Kernel.deterministic_comp_eq_map]
  have hB : avgRisk (zeroOneLoss M) Q ψ (uniformPrior M)
      = ∫⁻ j, ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) := by
    unfold avgRisk
    refine lintegral_congr fun j => ?_
    have hfm : Measurable (zeroOneLoss M j) := measurable_of_countable _
    rw [hψcomp, Kernel.map_apply (κ ∘ₖ Q) hT]
    exact lintegral_map hfm hT
  calc Φ δ * bayesRisk (zeroOneLoss M) Q (uniformPrior M)
      ≤ Φ δ * avgRisk (zeroOneLoss M) Q ψ (uniformPrior M) := by
        gcongr; exact bayesRisk_le_avgRisk _ _ _ _
    _ = Φ δ * ∫⁻ j, ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) := by rw [hB]
    _ ≤ ∫⁻ j, Φ δ * ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ j, ∫⁻ y, distortionLoss Φ g (θfam j) y ∂((κ ∘ₖ Q) j) ∂(uniformPrior M) := by
        refine lintegral_mono fun j => ?_
        calc Φ δ * ∫⁻ y, zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j)
            ≤ ∫⁻ y, Φ δ * zeroOneLoss M j (T y) ∂((κ ∘ₖ Q) j) := lintegral_const_mul_le _ _
          _ ≤ ∫⁻ y, distortionLoss Φ g (θfam j) y ∂((κ ∘ₖ Q) j) :=
              lintegral_mono fun y => hpt j y
    _ ≤ ⨆ j, ∫⁻ y, distortionLoss Φ g (θfam j) y ∂((κ ∘ₖ Q) j) := lintegral_le_iSup _

/-- **From estimation to testing** (Wainwright Proposition 15.1, Eq. (15.3)): for any increasing
distortion `Φ` and any `2δ`-separated family `θfam : Fin M → Θ` in the semimetric `ρ = edist` on
the functional values, the minimax risk is lower bounded by `Φ(δ)` times the M-ary testing error
of the induced sub-model `j ↦ P_{θfam j}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.2, Eq. (15.3). -/
theorem minimax_ge_testing_error
    [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω] {M : ℕ} [NeZero M]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (g : Θ → Ω) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (θfam : Fin M → Θ) (hθ : Measurable θfam) (δ : ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.1.2, Prop 15.1.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `{θfam j}` is a `2δ`-separated set in the semimetric `ρ`; Wainwright §15.1.2.
    (hsep : IsSeparatedFamily g θfam δ) :
    Φ δ * multiwayTestingError (P.comap θfam hθ) ≤ minimaxRiskDist Φ g P := by
  unfold minimaxRiskDist
  refine le_trans ?_ (minimaxRisk_precomp_le (distortionLoss Φ g) P θfam hθ)
  -- Supply a *measurable* nearest-point selector `T : Ω → Fin M`; the `[OpensMeasurableSpace Ω]`
  -- instance makes each distance `y ↦ edist (g (θfam ℓ)) y` measurable, so the `argmin`-test is
  -- measurable. Given `⟨T, hT, hTmin⟩` the bound closes via `mul_multiwayTestingError_le`.
  obtain ⟨T, hT, hTmin⟩ := exists_measurable_nearestPoint g θfam
  exact mul_multiwayTestingError_le P hθ hΦ hsep hT hTmin

end StatLean.Minimaxity
