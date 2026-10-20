module
public import StatLean.PointEstimation.Sufficiency.HalmosSavageCriterion
public import StatLean.PointEstimation.ForMathlib.HalmosSavage

@[expose] public section

/-!
# The factorization theorem

The working criterion for sufficiency in a dominated model: if the members of the family
have densities `p_θ` with respect to a σ-finite measure `μ`, then a statistic `T` is
sufficient exactly when the densities split into a factor that sees the data only through
`T` and a factor that does not see the parameter at all,
$$ p_\theta(x) \;=\; g_\theta\bigl(T(x)\bigr)\, h(x) \qquad (\mu\text{-a.e.}). $$

* `isSufficient_of_isFactorizedDensity` — a factorization makes `T` sufficient;
* `isFactorizedDensity_of_isSufficient` — a sufficient `T` produces a factorization.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), the factorization criterion; in the general dominated form it is E.L.
Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed., Springer Nature
Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 2 (The Probability Background), §2.6
(Sufficient Statistics), Corollary 2.6.1 (Fisher–Neyman factorization). (`TPE2 §1.6`; `TSH4
Cor 2.6.1`.)

**Proof formalization notes.**
* Both directions are stated relative to an arbitrary σ-finite dominating measure `μ` and
  fixed densities `p`, matching the classical statement. The bridge to the mixture form is
  the criterion of `Sufficiency.HalmosSavageCriterion`: writing `ν = ∑ᵢ cᵢ P_{θᵢ}` for an
  equivalent mixture, one direction takes `h = dν/dμ` (finite `ν` over σ-finite `μ`, so the
  derivative exists), and the other rescales, `g*_θ(t) = g_θ(t)/k(t)` with
  `k(t) = ∑ᵢ cᵢ g_{θᵢ}(t)`, choosing an arbitrary value where `k` vanishes. Consequently
  this file consumes the *existence* of an equivalent countable mixture for a dominated
  family; the criterion file itself takes the mixture as data.
* The factorization is the `μ`-a.e. predicate `IsFactorizedDensity` of `Sufficiency.Defs`,
  not a pointwise identity: the rescaling step above genuinely only controls a.e. behavior,
  and no downstream consumer needs more.
* All densities are `ℝ≥0∞`-valued, so there are no positivity or finiteness side conditions;
  measurability of `p_θ`, `g_θ` and `h` is what the change-of-variables steps consume.
* The existential direction returns the factorization data (`g`, `h`) rather than asserting
  it for a caller-supplied pair, because the classical construction determines `h` only up to
  the choice of mixture.

**Bibliographic comments.** The criterion is due to J. Neyman ("Sur un teorema concernente le
cosiddette statistiche sufficienti," *Giorn. Ist. Ital. Attuari* **6** (1935), 320–334),
following the introduction of sufficiency by R. A. Fisher ("On the mathematical foundations
of theoretical statistics," *Phil. Trans. R. Soc. A* **222** (1922), 309–368); its
measure-theoretic form for arbitrary dominated families, which is what is stated here, is due
to P. R. Halmos and L. J. Savage ("Application of the Radon–Nikodym theorem to the theory of
sufficient statistics," *Ann. Math. Statist.* **20** (1949), 225–241).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- Multiplying an a.e.-equality under a tilt `μ.withDensity w` by `w` yields an
a.e.-equality under `μ`: the tilt only sees `{w ≠ 0}`. -/
private theorem mul_ae_eq_of_ae_eq_withDensity {μ : Measure 𝓧} {w f₁ f₂ : 𝓧 → ℝ≥0∞}
    (hw : Measurable w) (h : f₁ =ᵐ[μ.withDensity w] f₂) :
    (fun x => w x * f₁ x) =ᵐ[μ] fun x => w x * f₂ x := by
  rw [Filter.EventuallyEq, ae_withDensity_iff hw] at h
  filter_upwards [h] with x hx
  rcases eq_or_ne (w x) 0 with h0 | h0
  · simp [h0]
  · rw [hx h0]

/-- **Factorization ⇒ sufficiency.** If the densities of a dominated family split as
`p_θ = (g_θ ∘ T) · h` almost everywhere, then `T` is sufficient. -/
theorem isSufficient_of_isFactorizedDensity (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure 𝓧) [SigmaFinite μ] (p : Θ → 𝓧 → ℝ≥0∞)
    -- LEAN-ONLY: measurability of the densities
    (hp : ∀ θ, Measurable (p θ))
    -- USER-INPUT: the model is dominated by `μ` with densities `p`; the classical setup
    (hP : ∀ θ, P θ = μ.withDensity (p θ)) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T) {g : Θ → S → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the parameter-dependent factor
    (hg : ∀ θ, Measurable (g θ)) {h : 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: measurability of the carrier
    (hh : Measurable h)
    -- USER-INPUT: the Fisher–Neyman factorization of the densities
    (hfac : IsFactorizedDensity p μ T g h) :
    IsSufficient P T := by
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · exact fun A _ => ⟨fun _ => 0, measurable_const, fun _ => zero_le_one,
      fun θ => (hΘ.false θ).elim⟩
  have hdomμ : ∀ θ, P θ ≪ μ := fun θ => (hP θ) ▸ withDensity_absolutelyContinuous μ (p θ)
  obtain ⟨θs, c, ν, hν, hcpos, hcsum, hdomν, -⟩ :=
    exists_equivalent_countable_mixture P μ hdomμ
  haveI : IsProbabilityMeasure ν := ⟨by
    rw [hν, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hcsum⟩
  -- the mixture as a density over `μ`, and its statistic-side aggregate
  set G : S → ℝ≥0∞ := fun t => ∑' i, c i * g (θs i) t with hGdef
  have hGm : Measurable G := Measurable.ennreal_tsum fun i => measurable_const.mul (hg (θs i))
  set k : 𝓧 → ℝ≥0∞ := fun x => ∑' i, c i * p (θs i) x with hkdef
  have hkm : Measurable k := Measurable.ennreal_tsum fun i => measurable_const.mul (hp (θs i))
  have hνk : ν = μ.withDensity k := by
    rw [hν]
    have he : (fun x => ∑' i, c i * p (θs i) x) = ∑' i, fun x => c i * p (θs i) x := by
      ext x; rw [ENNReal.tsum_apply]
    rw [hkdef, he, withDensity_tsum (fun i => measurable_const.fun_mul (hp (θs i)))]
    refine congrArg Measure.sum (funext fun i => ?_)
    rw [hP (θs i), ← withDensity_smul (c i) (hp (θs i))]
    congr 1
  have hkne : ∫⁻ x, k x ∂μ ≠ ∞ := by
    rw [← setLIntegral_univ, ← withDensity_apply k MeasurableSet.univ, ← hνk]
    exact measure_ne_top ν Set.univ
  have hkfin : ∀ᵐ x ∂μ, k x < ∞ := ae_lt_top hkm hkne
  have hkeq : k =ᵐ[μ] fun x => h x * G (T x) := by
    have hall : ∀ᵐ x ∂μ, ∀ i, p (θs i) x = g (θs i) (T x) * h x := by
      rw [ae_all_iff]; exact fun i => hfac (θs i)
    filter_upwards [hall] with x hx
    simp only [hkdef, hGdef]
    calc ∑' i, c i * p (θs i) x = ∑' i, c i * g (θs i) (T x) * h x :=
          tsum_congr fun i => by rw [hx i, ← mul_assoc]
      _ = (∑' i, c i * g (θs i) (T x)) * h x := ENNReal.tsum_mul_right
      _ = h x * ∑' i, c i * g (θs i) (T x) := mul_comm _ _
  have hEmeas : MeasurableSet {x | G (T x) = 0} := (hGm.comp hT) (measurableSet_singleton 0)
  have hνE : ν {x | G (T x) = 0} = 0 := by
    rw [hνk, withDensity_apply k hEmeas, lintegral_congr_ae (ae_restrict_of_ae hkeq),
        setLIntegral_congr_fun hEmeas (g := 0) (fun x hx => by
          simp only [Set.mem_setOf_eq] at hx; simp [hx])]
    simp
  -- for every member, `dPθ/dν` factors through `T`; then apply the criterion
  refine isSufficient_of_rnDeriv_comp P hT θs c ν hν hdomν (fun θ => ?_)
  have hpθE : ∀ᵐ x ∂μ, G (T x) = 0 → p θ x = 0 := by
    have h0 : P θ {x | G (T x) = 0} = 0 := hdomν θ hνE
    rw [hP θ, withDensity_apply (p θ) hEmeas] at h0
    have hz := (lintegral_eq_zero_iff' (hp θ).aemeasurable.restrict).mp h0
    rw [Filter.EventuallyEq, ae_restrict_iff' hEmeas] at hz
    filter_upwards [hz] with x hx using hx
  have hg'T : Measurable (fun x => g θ (T x) / G (T x)) := ((hg θ).div hGm).comp hT
  have hPθν : P θ = ν.withDensity (fun x => g θ (T x) / G (T x)) := by
    rw [hνk, ← withDensity_mul μ hkm hg'T, hP θ]
    refine withDensity_congr_ae ?_
    filter_upwards [hkeq, hkfin, hpθE, hfac θ] with x hkx hkfx hpz hpfac
    show p θ x = k x * (g θ (T x) / G (T x))
    rw [hkx]
    rcases eq_or_ne (G (T x)) 0 with hb0 | hb0
    · rw [hpz hb0, hb0]; simp
    · rcases eq_or_ne (G (T x)) ⊤ with hbt | hbt
      · have hh0 : h x = 0 := by
          by_contra hh0
          rw [hkx, hbt, ENNReal.mul_top hh0] at hkfx
          exact (lt_irrefl _ hkfx).elim
        rw [hpfac, hh0]; simp
      · rw [hpfac, mul_comm (h x * G (T x)) (g θ (T x) / G (T x)),
            mul_comm (h x) (G (T x)), ← mul_assoc, ENNReal.div_mul_cancel hb0 hbt]
  refine ⟨fun t => g θ t / G t, (hg θ).div hGm, ?_⟩
  have hrn := Measure.rnDeriv_withDensity ν hg'T
  rwa [← hPθν] at hrn

/-- **Sufficiency ⇒ factorization.** A sufficient statistic for a dominated family produces
a Fisher–Neyman factorization of its densities. -/
theorem isFactorizedDensity_of_isSufficient (P : Θ → Measure 𝓧)
    [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure 𝓧) [SigmaFinite μ] (p : Θ → 𝓧 → ℝ≥0∞)
    -- LEAN-ONLY: measurability of the densities
    (hp : ∀ θ, Measurable (p θ))
    -- USER-INPUT: the model is dominated by `μ` with densities `p`; the classical setup
    (hP : ∀ θ, P θ = μ.withDensity (p θ)) {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the statistic
    (hT : Measurable T)
    -- USER-INPUT: sufficiency of `T` in the per-event sense
    (hsuf : IsSufficient P T) :
    ∃ (g : Θ → S → ℝ≥0∞) (h : 𝓧 → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧ Measurable h ∧
      IsFactorizedDensity p μ T g h := by
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · exact ⟨fun _ _ => 0, fun _ => 0, fun _ => measurable_const, measurable_const,
      fun θ => (hΘ.false θ).elim⟩
  have hdomμ : ∀ θ, P θ ≪ μ := fun θ => (hP θ) ▸ withDensity_absolutelyContinuous μ (p θ)
  obtain ⟨θs, c, ν, hν, -, hcsum, hdomν, -⟩ :=
    exists_equivalent_countable_mixture P μ hdomμ
  haveI : IsProbabilityMeasure ν := ⟨by
    rw [hν, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]; exact hcsum⟩
  have hνμ : ν ≪ μ := by
    refine Measure.AbsolutelyContinuous.mk fun E hE hμE => ?_
    rw [hν, Measure.sum_apply _ hE]
    exact ENNReal.tsum_eq_zero.mpr fun i => by
      rw [Measure.smul_apply, smul_eq_mul, hdomμ (θs i) hμE, mul_zero]
  have hfwd := rnDeriv_comp_of_isSufficient P hT θs c ν hν hdomν hsuf
  refine ⟨fun θ => (hfwd θ).choose, ν.rnDeriv μ, fun θ => (hfwd θ).choose_spec.1,
    Measure.measurable_rnDeriv _ _, fun θ => ?_⟩
  set g := fun θ => (hfwd θ).choose with hgdef
  have hgeq : (P θ).rnDeriv ν =ᵐ[ν] fun x => g θ (T x) := (hfwd θ).choose_spec.2
  -- pθ =ᵐ dPθ/dμ =ᵐ (dPθ/dν)·(dν/dμ) =ᵐ (gθ∘T)·(dν/dμ)
  have hpμ : (P θ).rnDeriv μ =ᵐ[μ] p θ := by
    rw [hP θ]; exact Measure.rnDeriv_withDensity μ (hp θ)
  have hchain : (P θ).rnDeriv ν * ν.rnDeriv μ =ᵐ[μ] (P θ).rnDeriv μ :=
    Measure.rnDeriv_mul_rnDeriv (hdomν θ)
  have hwd : μ.withDensity (ν.rnDeriv μ) = ν := Measure.withDensity_rnDeriv_eq ν μ hνμ
  have hbridge := mul_ae_eq_of_ae_eq_withDensity (μ := μ) (w := ν.rnDeriv μ)
    (Measure.measurable_rnDeriv ν μ)
    (show (P θ).rnDeriv ν =ᵐ[μ.withDensity (ν.rnDeriv μ)] fun x => g θ (T x) by
      rw [hwd]; exact hgeq)
  filter_upwards [hpμ, hchain, hbridge] with x hpμx hchainx hbridgex
  calc p θ x = (P θ).rnDeriv μ x := hpμx.symm
    _ = (P θ).rnDeriv ν x * ν.rnDeriv μ x := hchainx.symm
    _ = ν.rnDeriv μ x * (P θ).rnDeriv ν x := mul_comm _ _
    _ = ν.rnDeriv μ x * g θ (T x) := hbridgex
    _ = g θ (T x) * ν.rnDeriv μ x := mul_comm _ _

end StatLean.PointEstimation
