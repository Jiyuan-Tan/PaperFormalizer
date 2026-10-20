module
public import StatLean.Minimaxity.Fano.MutualInformation

@[expose] public section

/-!
# Yang–Barron mutual-information bound (Lemma 15.21)

The Yang–Barron refinement bounds the mutual information $I(Z; J)$ between a parameter index $J$
(uniform over $\{1, \dots, M\}$) and the observation $Z$ directly by the *global* metric entropy of
the family in the square-root Kullback–Leibler divergence, with no need to construct a local
packing. If $N_{\mathrm{KL}}(\varepsilon; \mathcal{P})$ denotes the $\varepsilon$-covering number of
the family $\mathcal{P}$ in the square-root KL pseudo-distance, then
$$
  I(Z; J) \;\le\; \inf_{\varepsilon > 0}\, \bigl\{\, \varepsilon^{2} \;+\; \log N_{\mathrm{KL}}(\varepsilon; \mathcal{P}) \,\bigr\},
$$
which is Lemma 15.21, Eq. (15.51).

We formalize the **per-cover form**: given a finite family $\{\gamma_k\}_{k < N}$ of probability
measures that $\varepsilon$-covers the model $\{Q_j\}_{j < M}$ in $\sqrt{\mathrm{KL}}$ — meaning for
each $j$ there exists $k$ with $D(Q_j \,\|\, \gamma_k) \le \varepsilon^{2}$ — the mutual information
satisfies $I(Z; J) \le \varepsilon^{2} + \log N$. The infimum form (Eq. (15.51)) follows by
optimizing over covers. No constants are changed from the book; the cover components are taken to be
probability measures, as in Wainwright §15.3.5.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Lemma 15.21,
Eqs. (15.51)–(15.52).

**Proof formalization notes.** Writing $I(Z; J) = \tfrac{1}{M} \sum_j D(Q_j \,\|\, \bar{Q})$ for the
uniform mixture $\bar{Q}$, the bound reduces to controlling the unnormalized sum
$\sum_j D(Q_j \,\|\, \bar{Q}) \le M\,(\varepsilon^{2} + \log N)$, in two book steps (Eq. (15.52)):
1. **Mixture minimization** — replace the data mixture $\bar{Q}$ by the *cover* mixture
   $G = \tfrac{1}{N}\sum_k \gamma_k$, using $\sum_j D(Q_j \,\|\, \bar{Q}) \le \sum_j D(Q_j \,\|\, G)$
   (`sum_klDiv_mixture_le`), since the mixture of the model minimizes the average divergence.
2. **Drop the other terms** — for each $j$, pick a cover atom $\gamma_{k(j)}$ within $\varepsilon^2$
   and bound $D(Q_j \,\|\, G) \le D(Q_j \,\|\, \gamma_{k(j)}) + \log N$ (`klDiv_le_cover_mixture`).
   The key pointwise fact is $(1/N)\,\gamma_{k(j)} \le G$, which forces $d\gamma_{k(j)}/dG \le N$
   a.e.; the log-likelihood-ratio decomposition then adds at most $\log N$. Integrability of the
   resulting log-density is obtained by domination (positive part $\le \mathrm{llr} + \log N$,
   negative part $\le dG/dQ_j - 1$). Each $D(Q_j \,\|\, \gamma_{k(j)}) \le \varepsilon^2$ by the
   cover hypothesis. Combining and dividing by $M$ gives the bound. The helper lemmas
   `klDiv_le_cover_mixture` and `yang_barron_sum_le` carry the detailed Lean proof obligations.

**Bibliographic comments.** The result originates with Y. Yang and A. Barron,
"Information-theoretic determination of minimax rates of convergence," *Annals of Statistics*,
27(5):1564–1599, 1999 (see their Section 2 and the mutual-information / metric-entropy bounds used
to derive minimax rates; the global-entropy device replacing local packings is the paper's central
contribution). Wainwright's Lemma 15.21 presents this device; the formalized
statement follows Wainwright's notation and constants.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- **Drop-the-other-terms step** (Wainwright Eq. (15.52), second half). For probability measures
`ρ, γₖ, G` with `(1/N)·γₖ ≤ G` (so `G` dominates a `1/N`-share of the cover component `γₖ`), the
divergence to the cover mixture `G` exceeds the divergence to `γₖ` by at most `log N`:
`D(ρ ‖ G) ≤ D(ρ ‖ γₖ) + log N`. Proof: `(1/N)·γₖ ≤ G` forces `dγₖ/dG ≤ N` a.e., so
`log(dρ/dG) = log(dρ/dγₖ) + log(dγₖ/dG) ≤ llr ρ γₖ + log N`; integrating against `ρ` (both
probability measures, so the finite-measure correction terms vanish) gives the bound. Integrability
of `llr ρ G` is obtained by domination: its positive part is `≤ llr ρ γₖ + log N`, its negative part
is `≤ -log(dρ/dG) ≤ dG/dρ - 1 ≤ (dG/dρ).toReal`, and `∫ (dG/dρ) dρ ≤ G univ = 1`. -/
private lemma klDiv_le_cover_mixture {N : ℕ} (hN : N ≠ 0) (ρ γk G : Measure 𝓧)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure γk] [IsProbabilityMeasure G]
    -- LEAN-ONLY: `(1/N)·γₖ ≤ G`; supplied internally from `γₖ ≤ Σ γ` and `G = (1/N) Σ γ`.
    (hle : (N : ℝ≥0∞)⁻¹ • γk ≤ G) :
    klDiv ρ G ≤ klDiv ρ γk + ENNReal.ofReal (Real.log (N : ℝ)) := by
  rcases eq_or_ne (klDiv ρ γk) ⊤ with htop | hfin
  · rw [htop]; exact le_trans le_top le_top
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hfin
  have hNℝ : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hlogN_nonneg : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNℝ
  have hNcast_ne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN
  have hNcast_top : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  have hNinv_ne : (N : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hNcast_top
  have hγkG : γk ≪ G :=
    (Measure.AbsolutelyContinuous.smul_right Measure.AbsolutelyContinuous.rfl hNinv_ne).trans
      (Measure.absolutelyContinuous_of_le hle)
  have hρG : ρ ≪ G := hac.trans hγkG
  -- a.e.ρ bundle of pointwise facts
  have hbase : ∀ᵐ x ∂ρ, 0 < ρ.rnDeriv γk x ∧ ρ.rnDeriv γk x < ⊤
      ∧ 0 < γk.rnDeriv G x ∧ γk.rnDeriv G x < ⊤
      ∧ ρ.rnDeriv γk x * γk.rnDeriv G x = ρ.rnDeriv G x
      ∧ γk.rnDeriv G x ≤ (N:ℝ≥0∞) := by
    have hrn_le : (fun x => (γk.rnDeriv G x)) ≤ᵐ[G] (fun _ => (N : ℝ≥0∞)) := by
      have h1 : ((N : ℝ≥0∞)⁻¹ • γk).rnDeriv G ≤ᵐ[G] 1 := Measure.rnDeriv_le_one_of_le hle
      have h2 := Measure.rnDeriv_smul_left_of_ne_top γk G (r := (N:ℝ≥0∞)⁻¹)
        (ENNReal.inv_ne_top.mpr hNcast_ne)
      filter_upwards [h1, h2] with x hx1 hx2
      rw [hx2, Pi.smul_apply, smul_eq_mul] at hx1
      have hx1' : (N:ℝ≥0∞)⁻¹ * γk.rnDeriv G x ≤ 1 := by simpa [Pi.one_apply] using hx1
      calc γk.rnDeriv G x = (N:ℝ≥0∞) * ((N:ℝ≥0∞)⁻¹ * γk.rnDeriv G x) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hNcast_ne hNcast_top, one_mul]
        _ ≤ (N:ℝ≥0∞) * 1 := by gcongr
        _ = (N:ℝ≥0∞) := mul_one _
    have hchain : ρ.rnDeriv γk * γk.rnDeriv G =ᵐ[G] ρ.rnDeriv G :=
      Measure.rnDeriv_mul_rnDeriv hac
    filter_upwards [Measure.rnDeriv_pos hac, hac.ae_le (Measure.rnDeriv_lt_top ρ γk),
        hac.ae_le (Measure.rnDeriv_pos hγkG), hac.ae_le (hγkG.ae_le (Measure.rnDeriv_lt_top γk G)),
        hρG.ae_le hchain, hρG.ae_le hrn_le]
      with x h1 h2 h3 h4 h5 h6
    rw [Pi.mul_apply] at h5
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  -- upper bound on `llr ρ G`
  have hllr_le : llr ρ G ≤ᵐ[ρ] (fun x => llr ρ γk x + Real.log (N:ℝ)) := by
    filter_upwards [hbase] with x hx
    obtain ⟨hp1, hlt1, hp3, hlt3, hchain, hle6⟩ := hx
    simp only [llr_def]
    have hne1 : (ρ.rnDeriv γk x).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp1.ne', hlt1.ne⟩
    have hne3 : (γk.rnDeriv G x).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp3.ne', hlt3.ne⟩
    rw [← hchain, ENNReal.toReal_mul, Real.log_mul hne1 hne3]
    have hpos3 : 0 < (γk.rnDeriv G x).toReal := ENNReal.toReal_pos hp3.ne' hlt3.ne
    gcongr
    calc (γk.rnDeriv G x).toReal ≤ ((N:ℝ≥0∞)).toReal := ENNReal.toReal_mono hNcast_top hle6
      _ = (N:ℝ) := by simp
  -- integrability of `llr ρ G` by domination
  have hint_rnGρ : Integrable (fun x => (G.rnDeriv ρ x).toReal) ρ := by
    refine integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv G ρ).aemeasurable ?_
    exact ne_top_of_le_ne_top (by simp) (Measure.lintegral_rnDeriv_le)
  have hint_G : Integrable (llr ρ G) ρ := by
    have hdom : Integrable
        (fun x => |llr ρ γk x| + Real.log (N:ℝ) + (G.rnDeriv ρ x).toReal) ρ :=
      (hint.abs.add (integrable_const _)).add hint_rnGρ
    refine Integrable.mono' hdom (stronglyMeasurable_llr ρ G).aestronglyMeasurable ?_
    filter_upwards [hllr_le, Measure.rnDeriv_pos hρG, hρG.ae_le (Measure.rnDeriv_lt_top ρ G),
        Measure.inv_rnDeriv hρG] with x hxle hxpos hxlt hxinv
    rw [Real.norm_eq_abs, abs_le]
    have hpos' : 0 < (ρ.rnDeriv G x).toReal := ENNReal.toReal_pos hxpos.ne' hxlt.ne
    have hGρnn : (0:ℝ) ≤ (G.rnDeriv ρ x).toReal := ENNReal.toReal_nonneg
    constructor
    · have hb : -(G.rnDeriv ρ x).toReal ≤ llr ρ G x := by
        rw [llr_def]
        have h1 : Real.log ((ρ.rnDeriv G x).toReal)⁻¹ ≤ ((ρ.rnDeriv G x).toReal)⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have hinv : ((ρ.rnDeriv G x).toReal)⁻¹ = (G.rnDeriv ρ x).toReal := by
          rw [← ENNReal.toReal_inv]
          have : (ρ.rnDeriv G x)⁻¹ = G.rnDeriv ρ x := by
            have := hxinv; simpa [Pi.inv_apply] using this
          rw [this]
        rw [Real.log_inv, hinv] at h1
        linarith
      linarith [hb, abs_nonneg (llr ρ γk x)]
    · have h := le_abs_self (llr ρ γk x)
      linarith [hxle]
  have hfinG : klDiv ρ G ≠ ⊤ := klDiv_ne_top hρG hint_G
  -- compare via `toReal` (both probability measures: no correction term)
  have hreal : (klDiv ρ G).toReal ≤ (klDiv ρ γk).toReal + Real.log (N:ℝ) := by
    rw [toReal_klDiv_of_measure_eq hρG (by simp), toReal_klDiv_of_measure_eq hac (by simp)]
    calc ∫ x, llr ρ G x ∂ρ ≤ ∫ x, (llr ρ γk x + Real.log (N:ℝ)) ∂ρ :=
          integral_mono_ae hint_G (hint.add (integrable_const _)) hllr_le
      _ = ∫ x, llr ρ γk x ∂ρ + Real.log (N:ℝ) := by
          rw [integral_add hint (integrable_const _), integral_const, measureReal_def,
            measure_univ]; simp
  calc klDiv ρ G = ENNReal.ofReal (klDiv ρ G).toReal := (ENNReal.ofReal_toReal hfinG).symm
    _ ≤ ENNReal.ofReal ((klDiv ρ γk).toReal + Real.log (N:ℝ)) := ENNReal.ofReal_le_ofReal hreal
    _ = klDiv ρ γk + ENNReal.ofReal (Real.log (N:ℝ)) := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hlogN_nonneg, ENNReal.ofReal_toReal hfin]

/-- **Yang–Barron cover bound crux** (Wainwright Lemma 15.21, Eq. (15.52)): the unnormalized sum of
the divergences to the uniform mixture `Q̄ = mixture Q` is controlled by `M·(ε² + log N)` against an
`ε`-cover `{γ k}` of probability measures in √KL. Two book steps: mixture minimization
`Σⱼ D(Qⱼ ‖ Q̄) ≤ Σⱼ D(Qⱼ ‖ G)` for the cover mixture `G = (1/N) Σₖ γ k` (a probability measure, via
`sum_klDiv_mixture_le`), then drop-the-other-terms `D(Qⱼ ‖ G) ≤ D(Qⱼ ‖ γ_{k(j)}) + log N`
(`klDiv_le_cover_mixture`), bounding each `D(Qⱼ ‖ γ_{k(j)}) ≤ ε²` by the cover hypothesis. -/
private lemma yang_barron_sum_le {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    {N : ℕ} (γ : Fin N → Measure 𝓧) [∀ k, IsProbabilityMeasure (γ k)] (ε : ℝ≥0∞)
    (hcover : ∀ j, ∃ k, klDiv (Q j) (γ k) ≤ ε ^ 2) :
    ∑ j, klDiv (Q j) (mixture Q)
      ≤ (M : ℝ≥0∞) * (ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ))) := by
  -- `N = 0` is vacuous: `hcover j` would assert `∃ k : Fin 0, …`.
  rcases eq_or_ne N 0 with rfl | hN
  · obtain ⟨k, _⟩ := hcover (Classical.arbitrary _); exact absurd k.2 (by omega)
  have hNcast_ne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN
  have hNcast_top : (N : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top N
  -- the uniform cover mixture `G = (1/N) Σₖ γ k`, a probability measure.
  set G : Measure 𝓧 := (N : ℝ≥0∞)⁻¹ • ∑ k, γ k with hG_def
  have hGsum_univ : (∑ k, γ k) Set.univ = (N : ℝ≥0∞) := by
    rw [Measure.coe_finset_sum]; simp [measure_univ, Finset.card_univ]
  haveI hGprob : IsProbabilityMeasure G := by
    refine ⟨?_⟩
    rw [hG_def, Measure.smul_apply, smul_eq_mul, hGsum_univ,
      ENNReal.inv_mul_cancel hNcast_ne hNcast_top]
  -- Step 1 (mixture minimization): `Σⱼ D(Qⱼ ‖ Q̄) ≤ Σⱼ D(Qⱼ ‖ G)`.
  have hstep1 : ∑ j, klDiv (Q j) (mixture Q) ≤ ∑ j, klDiv (Q j) G := by
    have h := sum_klDiv_mixture_le (fun j => Q j) G
    rwa [← mixture_eq_inv_smul_sum] at h
  -- Step 2 (drop other terms): `D(Qⱼ ‖ G) ≤ D(Qⱼ ‖ γ_{k(j)}) + log N ≤ ε² + log N`.
  have hstep2 : ∑ j, klDiv (Q j) G
      ≤ ∑ _j : Fin M, (ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ))) := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    obtain ⟨k, hk⟩ := hcover j
    have hle : (N : ℝ≥0∞)⁻¹ • γ k ≤ G := by
      rw [hG_def]
      have hsub : γ k ≤ ∑ k, γ k :=
        Finset.single_le_sum (fun i _ => Measure.zero_le _) (Finset.mem_univ k)
      rw [Measure.le_iff']
      intro s
      rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
      gcongr
    calc klDiv (Q j) G ≤ klDiv (Q j) (γ k) + ENNReal.ofReal (Real.log (N : ℝ)) :=
          klDiv_le_cover_mixture hN (Q j) (γ k) G hle
      _ ≤ ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ)) := by gcongr
  -- Combine and evaluate the constant sum.
  refine (hstep1.trans hstep2).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Yang–Barron mutual-information bound** (Wainwright Lemma 15.21, Eq. (15.51), per-cover form):
if `{γ k}_{k<N}` is an `ε`-cover of the family `{Q j}` in the square-root KL divergence — meaning
for each `j` there is `k` with `D(Q j ‖ γ k) ≤ ε²` — then `I(Z; J) ≤ ε² + log N`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.5, Lemma 15.21. -/
theorem yang_barron {M : ℕ} [NeZero M] (Q : Kernel (Fin M) 𝓧) [IsMarkovKernel Q]
    {N : ℕ} (γ : Fin N → Measure 𝓧) [∀ k, IsProbabilityMeasure (γ k)] (ε : ℝ≥0∞)
    -- USER-INPUT: cover components γ k are probability measures; Wainwright §15.3.5.
    -- USER-INPUT: `{γ k}` is an `ε`-cover of `{Q j}` in √KL; Wainwright §15.3.5.
    (hcover : ∀ j, ∃ k, klDiv (Q j) (γ k) ≤ ε ^ 2) :
    mutualInformation Q ≤ ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ)) := by
  -- `I = (1/M) Σⱼ D(Qⱼ ‖ Q̄)`; the crux bounds the sum by `M·(ε² + log N)`, then `(1/M)·M = 1`.
  rw [mutualInformation]
  calc (M : ℝ≥0∞)⁻¹ * ∑ j, klDiv (Q j) (mixture Q)
      ≤ (M : ℝ≥0∞)⁻¹ * ((M : ℝ≥0∞) * (ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ)))) := by
        gcongr
        exact yang_barron_sum_le Q γ ε hcover
    _ = ε ^ 2 + ENNReal.ofReal (Real.log (N : ℝ)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne M))
          (ENNReal.natCast_ne_top M), one_mul]

end StatLean.Minimaxity
