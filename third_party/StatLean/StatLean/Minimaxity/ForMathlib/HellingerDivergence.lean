module
public import StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct

@[expose] public section

/-!
# Squared Hellinger distance: book form, range [0, 2], and i.i.d. tensorization

For two probability measures $\mathbb{P}, \mathbb{Q}$ dominated by a common measure $\nu$ with
densities $p = d\mathbb{P}/d\nu$ and $q = d\mathbb{Q}/d\nu$, the **squared Hellinger distance** is
the squared $L^2(\nu)$-distance between the square-root densities,
$$ H^2(\mathbb{P} \,\|\, \mathbb{Q}) \;=\; \int \bigl(\sqrt{p} - \sqrt{q}\bigr)^2 \, d\nu. $$
This file establishes the two basic facts of the textbook account:

* **Range.** $0 \le H^2(\mathbb{P} \,\|\, \mathbb{Q}) \le 2$, with the upper bound a consequence of
  expanding the square and using $\int p \, d\nu = \int q \, d\nu = 1$ together with the
  nonnegativity of the affinity $\int \sqrt{p}\,\sqrt{q}\, d\nu \ge 0$.
* **I.i.d. tensorization.** For the $n$-fold product measures,
  $$ H^2\!\bigl(\mathbb{P}^{\otimes n} \,\|\, \mathbb{Q}^{\otimes n}\bigr) \;\le\; n \cdot
     H^2(\mathbb{P} \,\|\, \mathbb{Q}), $$
  obtained from the product form of the affinity (the affinity of a product is the product of the
  affinities) together with the elementary inequality $1 - (1 - x)^n \le n\,x$ for $x \in [0,1]$.

To make the definition canonical and free of an external choice of dominating measure, we take
$\nu = \mathbb{P} + \mathbb{Q}$ throughout, with $p = d\mathbb{P}/d(\mathbb{P}+\mathbb{Q})$ and
$q = d\mathbb{Q}/d(\mathbb{P}+\mathbb{Q})$; the value is independent of this choice (see
`sqHellWith_transfer`). The tensorization properties reuse the StatLean Hellinger-product
machinery (`StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct`, a cross-area `ForMathlib`
import).

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9) (definition
and the range $[0,2]$) and Eq. (15.12a)/(15.12b) (the affinity-product identity and the i.i.d.
tensorization bound).

**Proof formalization notes.** The headline results map to two theorems:

* `sqHellinger_le_two` — the upper bound $H^2 \le 2$ (Wainwright Eq. (15.9)). Proved via the Bochner
  bridge `sqHellinger_eq_ofReal_integral` (the `ℝ≥0∞`-valued lintegral equals `ENNReal.ofReal` of the
  real $L^2$-residual integral, the integrand being nonnegative and integrable), then expanding the
  square and discarding the nonnegative affinity term `integral_sqrt_mul_sqrt_nonneg`.
* `sqHellinger_pi_le_nsmul` — the i.i.d. bound $H^2(\mathbb{P}^{\otimes n} \,\|\, \mathbb{Q}^{\otimes
  n}) \le n \cdot H^2(\mathbb{P} \,\|\, \mathbb{Q})$ (Wainwright Eq. (15.12b)), via
  `1 - (1 - x)^n \le n x`.

Two supporting facts about the squared Hellinger functional are packaged separately:
`sqHellWith_transfer` (invariance of the squared-Hellinger lintegral under the choice of common
dominating measure, proved from the Radon–Nikodym chain rule `Measure.rnDeriv_mul_rnDeriv`) and
`sqHellinger_pi_factor` (coordinatewise factorisation of the product Radon–Nikodym derivative,
proved from `MeasureTheory.PiWithDensity.pi_withDensity_prod`). The definition is taken against the
canonical reference $\mathbb{P} + \mathbb{Q}$ rather than a user-supplied $\nu$; this is a
presentation choice (no added hypotheses) and the value coincides with any other common dominating
measure by `sqHellWith_transfer`.

**Bibliographic comments.** The Hellinger distance is named after Ernst Hellinger, who introduced
the underlying square-root-density geometry in E. Hellinger, "Neue Begründung der Theorie
quadratischer Formen von unendlichvielen Veränderlichen", *Journal für die reine und angewandte
Mathematik* **136** (1909), 210–271. Its modern use in statistics — the squared form, the range
$[0,2]$, and the tensorization across i.i.d. coordinates — is textbook folklore with no single
seminal statistical paper; the specific equation numbering followed here is that of Wainwright (2019,
§15.1.3). The functional is closely related to (and a monotone transform of) the Bhattacharyya
affinity / Bhattacharyya coefficient, A. Bhattacharyya, "On a measure of divergence between two
statistical populations defined by their probability distributions", *Bulletin of the Calcutta
Mathematical Society* **35** (1943), 99–109.
-/

open MeasureTheory
open scoped ENNReal
open AsymptoticStatistics.ForMathlib.HellingerProduct

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Squared Hellinger distance** (Wainwright Eq. (15.9)): `H²(ℙ ‖ ℚ) = ∫ (√p − √q)² dν`,
the squared `L²`-distance between square-root densities, taken here against the common
dominating measure `ξ = ℙ + ℚ` (`p = dℙ/dξ`, `q = dℚ/dξ`).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9). -/
noncomputable def sqHellinger (μ ν : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    ((Real.sqrt (μ.rnDeriv (μ + ν) x).toReal
      - Real.sqrt (ν.rnDeriv (μ + ν) x).toReal) ^ 2) ∂(μ + ν)

/-- The squared Hellinger distance is symmetric. -/
theorem sqHellinger_comm (μ ν : Measure α) : sqHellinger μ ν = sqHellinger ν μ := by
  unfold sqHellinger
  rw [add_comm ν μ]
  refine lintegral_congr (fun x => ?_)
  congr 1
  ring

/-- Common absolute-continuity facts for the canonical dominating measure `ξ = μ + ν`. -/
private theorem absCont_left (μ ν : Measure α) : μ ≪ μ + ν :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)

private theorem absCont_right (μ ν : Measure α) : ν ≪ μ + ν :=
  Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)

/-- **Bridge to the Bochner form.** The `ℝ≥0∞`-valued definition of `sqHellinger` equals
`ENNReal.ofReal` of the real `L²`-residual integral `∫ (√p − √q)² dξ` (with `ξ = μ + ν`),
since the integrand is nonnegative and integrable (the square-root density residual is in
`L²(ξ)`). This lets us reuse the real-valued StatLean affinity machinery. -/
private theorem sqHellinger_eq_ofReal_integral (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger μ ν = ENNReal.ofReal
      (∫ ω, (Real.sqrt (μ.rnDeriv (μ + ν) ω).toReal
              - Real.sqrt (ν.rnDeriv (μ + ν) ω).toReal) ^ 2 ∂(μ + ν)) := by
  have hμ := absCont_left μ ν
  have hν := absCont_right μ ν
  have hint :=
    (hellinger_per_sample_residual_memLp_two hμ hν).integrable_sq
  unfold sqHellinger
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm

/-- **The squared Hellinger distance lies in `[0, 2]`** (Wainwright Eq. (15.9)).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.9). -/
theorem sqHellinger_le_two (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger μ ν ≤ 2 := by
  have hμ := absCont_left μ ν
  have hν := absCont_right μ ν
  rw [sqHellinger_eq_ofReal_integral, integral_per_sample_residual_sq_eq hμ hν]
  have hA := integral_sqrt_mul_sqrt_nonneg μ ν (μ + ν)
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The squared-Hellinger lintegral against an *arbitrary* common dominating reference `ξ`
(`sqHellinger μ ν` is the special case `ξ = μ + ν`). Introduced only as scaffolding for the
dominating-measure-invariance lemma `sqHellWith_transfer`. -/
private noncomputable def sqHellWith (A B ξ : Measure α) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal
    ((Real.sqrt (A.rnDeriv ξ x).toReal - Real.sqrt (B.rnDeriv ξ x).toReal) ^ 2) ∂ξ

/-- **Dominating-measure invariance.** If `ξ' ≪ ξ` (all σ-finite) with `A ≪ ξ'`, `B ≪ ξ'`, the
squared-Hellinger lintegral against `ξ'` equals the one against `ξ`. The squared `L²`-distance
between square-root densities does not depend on the choice of common dominating measure; we prove
it from the Radon–Nikodym chain rule `Measure.rnDeriv_mul_rnDeriv` together with the
change-of-reference identity `ξ' = ξ.withDensity (ξ'.rnDeriv ξ)`. -/
private theorem sqHellWith_transfer (A B ξ' ξ : Measure α)
    [SigmaFinite A] [SigmaFinite B] [SigmaFinite ξ'] [SigmaFinite ξ]
    (hAξ' : A ≪ ξ') (hBξ' : B ≪ ξ') (hξ'ξ : ξ' ≪ ξ) :
    sqHellWith A B ξ' = sqHellWith A B ξ := by
  unfold sqHellWith
  set w := ξ'.rnDeriv ξ with hw
  have hw_meas : Measurable w := Measure.measurable_rnDeriv _ _
  have hξ'eq : ξ' = ξ.withDensity w := (Measure.withDensity_rnDeriv_eq _ _ hξ'ξ).symm
  set F : α → ℝ≥0∞ := fun x => ENNReal.ofReal
      ((Real.sqrt (A.rnDeriv ξ' x).toReal - Real.sqrt (B.rnDeriv ξ' x).toReal) ^ 2) with hF
  have hF_meas : Measurable F := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow _ measurable_const
    exact ((((Measure.measurable_rnDeriv A ξ').ennreal_toReal).sqrt).sub
      (((Measure.measurable_rnDeriv B ξ').ennreal_toReal).sqrt))
  rw [hξ'eq, lintegral_withDensity_eq_lintegral_mul ξ hw_meas hF_meas]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := ξ) hAξ',
    Measure.rnDeriv_mul_rnDeriv (κ := ξ) hBξ',
    Measure.rnDeriv_lt_top ξ' ξ] with x hAx hBx hwx
  rw [Pi.mul_apply] at hAx hBx
  set wr := (w x).toReal with hwr
  have hwr_nn : 0 ≤ wr := ENNReal.toReal_nonneg
  set a' := (A.rnDeriv ξ' x).toReal with ha'
  set b' := (B.rnDeriv ξ' x).toReal with hb'
  have ha_eq : (A.rnDeriv ξ x).toReal = wr * a' := by
    rw [← hAx, ENNReal.toReal_mul, hwr, ha']; ring
  have hb_eq : (B.rnDeriv ξ x).toReal = wr * b' := by
    rw [← hBx, ENNReal.toReal_mul, hwr, hb']; ring
  change (w x * F x) = ENNReal.ofReal
      ((Real.sqrt (A.rnDeriv ξ x).toReal - Real.sqrt (B.rnDeriv ξ x).toReal) ^ 2)
  rw [hF]
  simp only []
  rw [show w x = ENNReal.ofReal wr from (ENNReal.ofReal_toReal hwx.ne).symm,
    ← ENNReal.ofReal_mul hwr_nn]
  congr 1
  rw [ha_eq, hb_eq, Real.sqrt_mul hwr_nn, Real.sqrt_mul hwr_nn]
  have hsq : Real.sqrt wr ^ 2 = wr := Real.sq_sqrt hwr_nn
  have hexp : (Real.sqrt wr * Real.sqrt a' - Real.sqrt wr * Real.sqrt b') ^ 2
       = Real.sqrt wr ^ 2 * (Real.sqrt a' - Real.sqrt b') ^ 2 := by ring
  rw [hexp, hsq]

open AsymptoticStatistics.ForMathlib.HellingerProduct in
/-- **Absolute continuity of i.i.d. products** under coordinatewise domination
`μ ≪ μ + ν`. Proved from the product Radon–Nikodym factorisation
`MeasureTheory.PiWithDensity.pi_withDensity_prod`. -/
private theorem pi_absCont_add (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (Measure.pi fun _ : Fin n => μ) ≪ (Measure.pi fun _ : Fin n => (μ + ν)) := by
  have hμ : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  set ξ : Measure α := μ + ν with hξ
  have hfμ : Measurable (μ.rnDeriv ξ) := Measure.measurable_rnDeriv _ _
  haveI : ∀ _ : Fin n, SigmaFinite ((ξ).withDensity (μ.rnDeriv ξ)) := by
    intro _; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]; infer_instance
  have hpiμ : (Measure.pi fun _ : Fin n => μ)
      = (Measure.pi fun _ : Fin n => ξ).withDensity (fun x => ∏ j, μ.rnDeriv ξ (x j)) := by
    rw [pi_withDensity_prod (fun _ => hfμ)]
    congr 1; ext i; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]
  rw [hpiμ]
  exact withDensity_absolutelyContinuous _ _

open AsymptoticStatistics.ForMathlib.HellingerProduct in
/-- **Product factorisation.** The squared-Hellinger lintegral of the products, taken against the
common dominating reference `Measure.pi (μ + ν)`, equals `ENNReal.ofReal` of the
per-coordinate-product residual integral. Proved from the product Radon–Nikodym factorisation
`pi_withDensity_prod` (giving `(Measure.pi μ).rnDeriv (Measure.pi ξ) =ᵃᵉ ∏ⱼ μ.rnDeriv ξ`) and the
Bochner bridge `ofReal_integral_eq_lintegral_ofReal`. -/
private theorem sqHellinger_pi_factor (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellWith (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
        (Measure.pi fun _ : Fin n => (μ + ν))
      = ENNReal.ofReal
          (∫ X : Fin n → α,
            ((∏ j, Real.sqrt (μ.rnDeriv (μ + ν) (X j)).toReal)
              - ∏ j, Real.sqrt (ν.rnDeriv (μ + ν) (X j)).toReal) ^ 2
            ∂(Measure.pi fun _ : Fin n => (μ + ν))) := by
  have hμ : μ ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hν : ν ≪ μ + ν := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set ξ : Measure α := μ + ν with hξ
  have hfμ : Measurable (μ.rnDeriv ξ) := Measure.measurable_rnDeriv _ _
  have hfν : Measurable (ν.rnDeriv ξ) := Measure.measurable_rnDeriv _ _
  haveI : ∀ _ : Fin n, SigmaFinite ((ξ).withDensity (μ.rnDeriv ξ)) := by
    intro _; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]; infer_instance
  haveI : ∀ _ : Fin n, SigmaFinite ((ξ).withDensity (ν.rnDeriv ξ)) := by
    intro _; rw [Measure.withDensity_rnDeriv_eq _ _ hν]; infer_instance
  have hpiμ : (Measure.pi fun _ : Fin n => μ)
      = (Measure.pi fun _ : Fin n => ξ).withDensity (fun x => ∏ j, μ.rnDeriv ξ (x j)) := by
    rw [pi_withDensity_prod (fun _ => hfμ)]
    congr 1; ext i; rw [Measure.withDensity_rnDeriv_eq _ _ hμ]
  have hpiν : (Measure.pi fun _ : Fin n => ν)
      = (Measure.pi fun _ : Fin n => ξ).withDensity (fun x => ∏ j, ν.rnDeriv ξ (x j)) := by
    rw [pi_withDensity_prod (fun _ => hfν)]
    congr 1; ext i; rw [Measure.withDensity_rnDeriv_eq _ _ hν]
  have hrnμ : (Measure.pi fun _ : Fin n => μ).rnDeriv (Measure.pi fun _ : Fin n => ξ)
      =ᵐ[Measure.pi fun _ : Fin n => ξ] (fun x => ∏ j, μ.rnDeriv ξ (x j)) := by
    conv_lhs => rw [hpiμ]
    exact Measure.rnDeriv_withDensity _
      (Finset.measurable_prod _ (fun j _ => hfμ.comp (measurable_pi_apply j)))
  have hrnν : (Measure.pi fun _ : Fin n => ν).rnDeriv (Measure.pi fun _ : Fin n => ξ)
      =ᵐ[Measure.pi fun _ : Fin n => ξ] (fun x => ∏ j, ν.rnDeriv ξ (x j)) := by
    conv_lhs => rw [hpiν]
    exact Measure.rnDeriv_withDensity _
      (Finset.measurable_prod _ (fun j _ => hfν.comp (measurable_pi_apply j)))
  unfold sqHellWith
  rw [show (Measure.pi fun _ : Fin n => (μ + ν)) = (Measure.pi fun _ : Fin n => ξ) from rfl]
  rw [lintegral_congr_ae (g := fun X => ENNReal.ofReal
      (((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
        - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2))]
  · rw [← ofReal_integral_eq_lintegral_ofReal]
    · exact (hellinger_product_residual_memLp_two_perCoord (μ := μ) (ν := ν) (ξ := ξ)
        (n := n) hμ hν).integrable_sq
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  · filter_upwards [hrnμ, hrnν] with x hx hy
    rw [hx, hy, ← prod_sqrt_eq_sqrt_prod_toReal, ← prod_sqrt_eq_sqrt_prod_toReal]

/-- **Bridge to the StatLean product form.** The squared Hellinger distance of the `n`-fold
i.i.d. products, against its canonical dominating measure `Measure.pi μ + Measure.pi ν`, equals
`ENNReal.ofReal` of the per-coordinate-product residual integral against `Measure.pi (μ + ν)`
(the dominating measure used by `StatLean.AsymptoticStatistics.ForMathlib.HellingerProduct`).

This packages two standard measure-theoretic facts about the squared Hellinger functional:
(i) the Radon–Nikodym derivative of a product measure factorises coordinatewise,
`(Measure.pi μ).rnDeriv (Measure.pi ξ) =ᵃᵉ ∏ⱼ μ.rnDeriv ξ`, and
(ii) the squared Hellinger integral is invariant under the choice of common dominating measure
(here switching `Measure.pi μ + Measure.pi ν` for `Measure.pi (μ + ν)`).

This is discharged via two helper lemmas below: `sqHellWith_transfer` (dominating-measure
invariance of the squared-Hellinger lintegral, proved from the Radon–Nikodym chain rule
`Measure.rnDeriv_mul_rnDeriv`) and `sqHellinger_pi_factor` (the product factorisation, proved
from `MeasureTheory.PiWithDensity.pi_withDensity_prod`). -/
private theorem sqHellinger_pi_eq_ofReal_product_integral (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      = ENNReal.ofReal
          (∫ X : Fin n → α,
            ((∏ j, Real.sqrt (μ.rnDeriv (μ + ν) (X j)).toReal)
              - ∏ j, Real.sqrt (ν.rnDeriv (μ + ν) (X j)).toReal) ^ 2
            ∂(Measure.pi fun _ : Fin n => (μ + ν))) := by
  set A := Measure.pi fun _ : Fin n => μ with hA
  set B := Measure.pi fun _ : Fin n => ν with hB
  set P := Measure.pi fun _ : Fin n => (μ + ν) with hP
  have hAP : A ≪ P := pi_absCont_add n μ ν
  have hBP : B ≪ P := by
    have := pi_absCont_add n ν μ
    rwa [add_comm ν μ] at this
  have hAAB : A ≪ A + B := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hBAB : B ≪ A + B := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set ζ := (A + B) + P with hζ
  have hABζ : (A + B) ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hPζ : P ≪ ζ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  -- `sqHellinger A B` is by definition `sqHellWith A B (A + B)`.
  change sqHellWith A B (A + B) = _
  rw [sqHellWith_transfer A B (A + B) ζ hAAB hBAB hABζ,
      ← sqHellWith_transfer A B P ζ hAP hBP hPζ]
  exact sqHellinger_pi_factor n μ ν

/-- **I.i.d. tensorization bound for the squared Hellinger distance** (Wainwright Eq. (15.12b)):
`H²(ℙ^{1:n} ‖ ℚ^{1:n}) ≤ n · H²(ℙ ‖ ℚ)`, obtained from the affinity-product identity (Eq. (15.12a))
and the elementary inequality `1 − (1 − x)ⁿ ≤ n x`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.12b). -/
theorem sqHellinger_pi_le_nsmul (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      ≤ n • sqHellinger μ ν := by
  have hμ := absCont_left μ ν
  have hν := absCont_right μ ν
  rw [sqHellinger_pi_eq_ofReal_product_integral, sqHellinger_eq_ofReal_integral,
      ← ENNReal.ofReal_nsmul]
  apply ENNReal.ofReal_le_ofReal
  rw [nsmul_eq_mul]
  exact hellinger_product_residual_sq_le_n_per_sample hμ hν

end StatLean.Minimaxity
