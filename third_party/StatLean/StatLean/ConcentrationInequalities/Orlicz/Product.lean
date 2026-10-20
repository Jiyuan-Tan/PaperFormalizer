module
public import StatLean.ConcentrationInequalities.Orlicz.Basic
public import StatLean.ConcentrationInequalities.Orlicz.Generators
public import StatLean.ConcentrationInequalities.Orlicz.Attainment

@[expose] public section

/-!
# Sub-Gaussian / sub-exponential product calculus

The two product lemmas of HDP §2.8:
$$ \bigl\|X^2\bigr\|_{\psi_1} = \|X\|_{\psi_2}^2
   \qquad \text{(Lemma 2.8.5, exact equality)}, $$
$$ \|XY\|_{\psi_1} \le \|X\|_{\psi_2}\,\|Y\|_{\psi_2}
   \qquad \text{(Lemma 2.8.6, constant 1)}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, Lemma 2.8.5 and Lemma 2.8.6.

**Proof formalization notes.** Both constants are `1` (book-exact; the
book's "check!" in 2.8.5 confirmed — the integrands
`ψ₁(|X²|/k²)` and `ψ₂(|X|/k)` are *literally equal* after `sq_abs`/`div_pow`
rewrites, so 2.8.5 is an exact gauge-set bijection
`K ∈ orliczSet ψ₁ X² ↔ NNReal.sqrt K ∈ orliczSet ψ₂ X`; hence no
hypotheses). The `ℝ≥0∞` squaring of the `⨅` is done by two `≤`-proofs using
the ε-free witness extraction `exists_mem_orliczSet_lt_of_orliczNorm_lt`
rather than an `OrderIso`. For 2.8.6, `hXfin`/`hYfin` (norm ≠ ⊤) are the
book's "X and Y are sub-Gaussian" inputs; the zero-norm edge (`0 · ⊤` in
`ℝ≥0∞`) is handled by case split on `orliczNorm_eq_zero_iff` (X = 0 a.e. ⇒
XY = 0 a.e.); the pointwise chain is Young's split
`|xy|/(ab) ≤ (x/a)²/2 + (y/b)²/2` followed by AM–GM
`e^{u+v} ≤ (e^{2u} + e^{2v})/2` (inline `nlinarith`). Named-sorry fallback of
this work item: `subExponentialNorm_sq` (the `ℝ≥0∞` biInf-squaring
gymnastics); Lemma 2.8.6 must close.

**Bibliographic comments.** The ψ₂–ψ₁ product/squaring calculus is the
standard Orlicz-space Hölder inequality specialized to conjugate Young
functions (Rao–Ren, *Theory of Orlicz Spaces*, 1991, §IV).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Young/AM–GM at the level of the generators: `ψ₁(uv) ≤ ½ψ₂(u) + ½ψ₂(v)`,
holding for all reals via `uv ≤ (u²+v²)/2` and convexity of `exp`
(`e^{(s+t)/2} ≤ (e^s + e^t)/2`). Pointwise engine of Lemma 2.8.6. -/
private lemma young_psiOne_le (u v : ℝ) :
    psiOne (u * v) ≤ (1 / 2) * psiTwo u + (1 / 2) * psiTwo v := by
  simp only [psiOne_apply, psiTwo_apply]
  have hpq : Real.exp ((u ^ 2 + v ^ 2) / 2)
      = Real.exp (u ^ 2 / 2) * Real.exp (v ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hPuv : Real.exp (u ^ 2)
      = Real.exp (u ^ 2 / 2) * Real.exp (u ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hQvv : Real.exp (v ^ 2)
      = Real.exp (v ^ 2 / 2) * Real.exp (v ^ 2 / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle1 : Real.exp (u * v) ≤ Real.exp (u ^ 2 / 2) * Real.exp (v ^ 2 / 2) := by
    rw [← hpq]; exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (u - v)])
  have hle2 : Real.exp (u ^ 2 / 2) * Real.exp (v ^ 2 / 2)
      ≤ (Real.exp (u ^ 2 / 2) * Real.exp (u ^ 2 / 2)
          + Real.exp (v ^ 2 / 2) * Real.exp (v ^ 2 / 2)) / 2 := by
    nlinarith [sq_nonneg (Real.exp (u ^ 2 / 2) - Real.exp (v ^ 2 / 2))]
  rw [hPuv, hQvv]; linarith

/-- **Lemma 2.8.5** (HDP; exact, no hypotheses): `‖X²‖_{ψ₁} = ‖X‖_{ψ₂}²` —
the gauge sets correspond exactly under `K ↦ K²` since the integrands are
literally equal. -/
theorem subExponentialNorm_sq (X : Ω → ℝ) (μ : Measure Ω) :
    subExponentialNorm (fun ω => (X ω) ^ 2) μ = (subGaussianNorm X μ) ^ 2 := by
  -- Pointwise integrand equality `ψ₁(|X²|/J²) = ψ₂(|X|/J)`.
  have hpe : ∀ (J : ℝ≥0) (ω : Ω),
      ENNReal.ofReal (psiOne (|(X ω) ^ 2| / ((J ^ 2 : ℝ≥0) : ℝ)))
        = ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ))) := by
    intro J ω
    congr 1
    simp only [psiOne_apply, psiTwo_apply, abs_of_nonneg (sq_nonneg (X ω)),
      NNReal.coe_pow, div_pow, sq_abs]
  -- Forward: `J ∈ ψ₂-gauge(X) ⇒ J² ∈ ψ₁-gauge(X²)`.
  have hfwd : ∀ J ∈ orliczSet psiTwo X μ,
      (J ^ 2) ∈ orliczSet psiOne (fun ω => (X ω) ^ 2) μ := by
    intro J hJ
    obtain ⟨hJpos, hJint⟩ := hJ
    refine ⟨pow_pos hJpos 2, ?_⟩
    have hcongr : ∫⁻ ω, ENNReal.ofReal (psiOne (|(X ω) ^ 2| / ((J ^ 2 : ℝ≥0) : ℝ))) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ))) ∂μ :=
      lintegral_congr (fun ω => hpe J ω)
    rw [hcongr]; exact hJint
  -- Backward: `K ∈ ψ₁-gauge(X²) ⇒ √K ∈ ψ₂-gauge(X)`.
  have hbwd : ∀ K ∈ orliczSet psiOne (fun ω => (X ω) ^ 2) μ,
      NNReal.sqrt K ∈ orliczSet psiTwo X μ := by
    intro K hK
    obtain ⟨hKpos, hKint⟩ := hK
    refine ⟨NNReal.sqrt_pos.mpr hKpos, ?_⟩
    have hsqK : (NNReal.sqrt K) ^ 2 = K := NNReal.sq_sqrt K
    have hcongr : ∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / ((NNReal.sqrt K : ℝ≥0) : ℝ))) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (psiOne (|(X ω) ^ 2| / ((K : ℝ≥0) : ℝ))) ∂μ := by
      refine lintegral_congr (fun ω => ?_)
      rw [← hpe (NNReal.sqrt K) ω, hsqK]
    rw [hcongr]; exact hKint
  -- `‖X²‖_{ψ₁} = ⨅_{J ∈ ψ₂-gauge(X)} (J : ℝ≥0∞)²`.
  have hA : orliczNorm psiOne (fun ω => (X ω) ^ 2) μ
      = ⨅ J ∈ orliczSet psiTwo X μ, ((J : ℝ≥0∞)) ^ 2 := by
    apply le_antisymm
    · apply le_iInf₂
      intro J hJ
      calc orliczNorm psiOne (fun ω => (X ω) ^ 2) μ
          ≤ ((J ^ 2 : ℝ≥0) : ℝ≥0∞) := orliczNorm_le_of_mem (hfwd J hJ)
        _ = ((J : ℝ≥0∞)) ^ 2 := by rw [ENNReal.coe_pow]
    · have hle : (⨅ J ∈ orliczSet psiTwo X μ, ((J : ℝ≥0∞)) ^ 2)
          ≤ ⨅ K ∈ orliczSet psiOne (fun ω => (X ω) ^ 2) μ, ((K : ℝ≥0) : ℝ≥0∞) := by
        apply le_iInf₂
        intro K hK
        calc (⨅ J ∈ orliczSet psiTwo X μ, ((J : ℝ≥0∞)) ^ 2)
            ≤ ((NNReal.sqrt K : ℝ≥0∞)) ^ 2 := iInf₂_le (NNReal.sqrt K) (hbwd K hK)
          _ = ((K : ℝ≥0) : ℝ≥0∞) := by rw [← ENNReal.coe_pow, NNReal.sq_sqrt]
      simpa only [orliczNorm] using hle
  -- `(‖X‖_{ψ₂})² = ⨅_{J ∈ ψ₂-gauge(X)} (J : ℝ≥0∞)²`.
  have hB : (subGaussianNorm X μ) ^ 2
      = ⨅ J ∈ orliczSet psiTwo X μ, ((J : ℝ≥0∞)) ^ 2 := by
    have hsub : subGaussianNorm X μ
        = ⨅ i : (orliczSet psiTwo X μ), ((i : ℝ≥0) : ℝ≥0∞) := by
      rw [subGaussianNorm_def]
      simp only [orliczNorm]
      exact (iInf_subtype'' (orliczSet psiTwo X μ) (fun K => (K : ℝ≥0∞))).symm
    have hsub2 : (⨅ J ∈ orliczSet psiTwo X μ, ((J : ℝ≥0∞)) ^ 2)
        = ⨅ i : (orliczSet psiTwo X μ), ((i : ℝ≥0) : ℝ≥0∞) ^ 2 :=
      (iInf_subtype'' (orliczSet psiTwo X μ) (fun K => (K : ℝ≥0∞) ^ 2)).symm
    rcases Set.eq_empty_or_nonempty (orliczSet psiTwo X μ) with he | hne
    · have hb : subGaussianNorm X μ = ⊤ := by
        rw [subGaussianNorm_def]; simp only [orliczNorm, he]; exact iInf_emptyset
      rw [hb, he, iInf_emptyset]
      simp
    · have hnei : Nonempty (orliczSet psiTwo X μ) := hne.to_subtype
      rw [hsub, hsub2, sq]
      rw [ENNReal.iInf_mul_iInf (f := fun i : (orliczSet psiTwo X μ) => ((i : ℝ≥0) : ℝ≥0∞))
          (g := fun i : (orliczSet psiTwo X μ) => ((i : ℝ≥0) : ℝ≥0∞))
          ⟨Classical.choice hnei, ENNReal.coe_ne_top⟩
          ⟨Classical.choice hnei, ENNReal.coe_ne_top⟩ ?_]
      · simp only [sq]
      · intro i j
        rcases le_total ((i : ℝ≥0) : ℝ≥0∞) ((j : ℝ≥0) : ℝ≥0∞) with hij | hij
        · exact ⟨i, by exact mul_le_mul' le_rfl hij⟩
        · exact ⟨j, by exact mul_le_mul' hij le_rfl⟩
  rw [subExponentialNorm_def, hA, hB]

/-- **Lemma 2.8.6** (HDP; constant 1): the product of two sub-Gaussian
variables is sub-exponential, `‖XY‖_{ψ₁} ≤ ‖X‖_{ψ₂}·‖Y‖_{ψ₂}`. -/
theorem subExponentialNorm_mul_le {X Y : Ω → ℝ} {μ : Measure Ω}
    -- LEAN-ONLY: a.e.-measurability of X; gauge-condition regularity
    (hX : AEMeasurable X μ)
    -- LEAN-ONLY: a.e.-measurability of Y; gauge-condition regularity
    (hY : AEMeasurable Y μ)
    -- USER-INPUT: X sub-Gaussian (finite ψ₂ norm); HDP Lemma 2.8.6 hypothesis
    (hXfin : subGaussianNorm X μ ≠ ⊤)
    -- USER-INPUT: Y sub-Gaussian (finite ψ₂ norm); HDP Lemma 2.8.6 hypothesis
    (hYfin : subGaussianNorm Y μ ≠ ⊤) :
    subExponentialNorm (fun ω => X ω * Y ω) μ
      ≤ subGaussianNorm X μ * subGaussianNorm Y μ := by
  have haX : AEMeasurable (fun ω => |X ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hX
  have haY : AEMeasurable (fun ω => |Y ω|) μ :=
    continuous_abs.measurable.comp_aemeasurable hY
  -- For gauges `J` of `X` and `L` of `Y` (ψ₂), `J·L` is a ψ₁-gauge of `XY`.
  have hmem : ∀ J ∈ orliczSet psiTwo X μ, ∀ L ∈ orliczSet psiTwo Y μ,
      (J * L) ∈ orliczSet psiOne (fun ω => X ω * Y ω) μ := by
    intro J hJ L hL
    obtain ⟨hJpos, hJint⟩ := hJ
    obtain ⟨hLpos, hLint⟩ := hL
    refine ⟨mul_pos hJpos hLpos, ?_⟩
    have hmX : AEMeasurable (fun ω => ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ)))) μ :=
      (psiTwo_measurable.comp_aemeasurable (haX.div_const _)).ennreal_ofReal
    -- Pointwise Young split at the `ℝ≥0∞` level.
    have hpt : ∀ ω, ENNReal.ofReal (psiOne (|X ω * Y ω| / ((J * L : ℝ≥0) : ℝ)))
        ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ)))
          + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|Y ω| / (L : ℝ))) := by
      intro ω
      have harg : |X ω * Y ω| / ((J * L : ℝ≥0) : ℝ)
          = (|X ω| / (J : ℝ)) * (|Y ω| / (L : ℝ)) := by
        rw [NNReal.coe_mul, abs_mul, mul_div_mul_comm]
      rw [harg]
      have hnn1 : (0 : ℝ) ≤ (1 / 2) * psiTwo (|X ω| / (J : ℝ)) := by
        have := psiTwo_nonneg (|X ω| / (J : ℝ)); linarith
      have hnn2 : (0 : ℝ) ≤ (1 / 2) * psiTwo (|Y ω| / (L : ℝ)) := by
        have := psiTwo_nonneg (|Y ω| / (L : ℝ)); linarith
      calc ENNReal.ofReal (psiOne ((|X ω| / (J : ℝ)) * (|Y ω| / (L : ℝ))))
          ≤ ENNReal.ofReal ((1 / 2) * psiTwo (|X ω| / (J : ℝ))
              + (1 / 2) * psiTwo (|Y ω| / (L : ℝ))) :=
            ENNReal.ofReal_le_ofReal (young_psiOne_le _ _)
        _ = ENNReal.ofReal ((1 / 2) * psiTwo (|X ω| / (J : ℝ)))
            + ENNReal.ofReal ((1 / 2) * psiTwo (|Y ω| / (L : ℝ))) :=
            ENNReal.ofReal_add hnn1 hnn2
        _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ)))
            + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|Y ω| / (L : ℝ))) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    have hcne : ENNReal.ofReal (1 / 2) ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
    calc ∫⁻ ω, ENNReal.ofReal (psiOne (|X ω * Y ω| / ((J * L : ℝ≥0) : ℝ))) ∂μ
        ≤ ∫⁻ ω, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ)))
            + ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|Y ω| / (L : ℝ)))) ∂μ :=
          lintegral_mono hpt
      _ = (∫⁻ ω, ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ))) ∂μ)
          + ∫⁻ ω, ENNReal.ofReal (1 / 2) * ENNReal.ofReal (psiTwo (|Y ω| / (L : ℝ))) ∂μ :=
          lintegral_add_left' (hmX.const_mul _) _
      _ = ENNReal.ofReal (1 / 2) * (∫⁻ ω, ENNReal.ofReal (psiTwo (|X ω| / (J : ℝ))) ∂μ)
          + ENNReal.ofReal (1 / 2) * (∫⁻ ω, ENNReal.ofReal (psiTwo (|Y ω| / (L : ℝ))) ∂μ) := by
          rw [lintegral_const_mul' _ _ hcne, lintegral_const_mul' _ _ hcne]
      _ ≤ ENNReal.ofReal (1 / 2) * 1 + ENNReal.ofReal (1 / 2) * 1 := by
          gcongr
      _ = 1 := by
          rw [mul_one, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
  -- Both gauge sets are nonempty (finite ψ₂ norms).
  have hSX : (orliczSet psiTwo X μ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hXfin
    rw [subGaussianNorm_def]
    simp only [orliczNorm, h]
    exact iInf_emptyset
  have hSY : (orliczSet psiTwo Y μ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hYfin
    rw [subGaussianNorm_def]
    simp only [orliczNorm, h]
    exact iInf_emptyset
  -- Reindex the sub-Gaussian norms over the gauge subtypes and combine.
  have hXeq : subGaussianNorm X μ
      = ⨅ i : (orliczSet psiTwo X μ), ((i : ℝ≥0) : ℝ≥0∞) := by
    rw [subGaussianNorm_def]
    simp only [orliczNorm]
    exact (iInf_subtype'' (orliczSet psiTwo X μ) (fun K => (K : ℝ≥0∞))).symm
  have hYeq : subGaussianNorm Y μ
      = ⨅ i : (orliczSet psiTwo Y μ), ((i : ℝ≥0) : ℝ≥0∞) := by
    rw [subGaussianNorm_def]
    simp only [orliczNorm]
    exact (iInf_subtype'' (orliczSet psiTwo Y μ) (fun K => (K : ℝ≥0∞))).symm
  rw [hXeq, hYeq]
  apply ENNReal.le_iInf_mul_iInf
  · exact ⟨⟨hSX.choose, hSX.choose_spec⟩, ENNReal.coe_ne_top⟩
  · exact ⟨⟨hSY.choose, hSY.choose_spec⟩, ENNReal.coe_ne_top⟩
  · intro i j
    rw [subExponentialNorm_def]
    have hm := orliczNorm_le_of_mem (hmem i.1 i.2 j.1 j.2)
    rwa [ENNReal.coe_mul] at hm

end StatLean.ConcentrationInequalities
