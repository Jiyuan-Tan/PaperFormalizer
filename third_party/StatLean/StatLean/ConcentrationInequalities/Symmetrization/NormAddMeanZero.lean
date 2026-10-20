module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Adding an independent mean-zero term can only increase the expected norm

HDP Eq. (6.13): if $Y$ and $Z$ are independent random vectors in a Banach
space with $\mathbb{E} Z = 0$, then
$$ \mathbb{E}\,\|Y\| \;\le\; \mathbb{E}\,\|Y + Z\|. $$
Formalized on an explicit product of measures (independence holds by
construction): the pointwise core is
$$ \|y\| \;=\; \Bigl\| \int (y + g(z))\, dP_2(z) \Bigr\|
   \;\le\; \int \|y + g(z)\|\, dP_2(z) $$
(Jensen for norms), and the product form follows by integrating over $P_1$.
Both directions of the symmetrization Lemma 6.3.2, the Gaussian
symmetrization Lemma 6.6.2, and Exercise 8.11 consume this one lemma.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3, Eq. (6.13) (stated with "(Check it!)";
we prove it in full).

**Proof formalization notes.** Pointwise core: `integral_const_add` writes
`y = ∫ (y + g z) ∂P₂` using `∫ g ∂P₂ = 0` and `P₂` a probability measure, then
`norm_integral_le_integral_norm` (Jensen for the norm — no convexity API
needed). Product form: integrate the pointwise inequality over `P₁` with
`integral_mono`; the Fubini side conditions are discharged by
`Integrable.integral_norm_prod_left` and
`MeasurePreserving.integrable_comp` along `measurePreserving_fst`/`snd`.
Integrability of `f` and `g` is a genuine hypothesis (the book's
`E‖·‖ < ∞` standing assumption). Named-sorry fallback of this work item:
`integral_norm_le_integral_norm_add_prod` (the product/Fubini form), with the
pointwise core fully proven.

**Bibliographic comments.** This inequality is folklore (a one-line
consequence of Jensen's inequality for the norm); in the Banach-space
literature it appears as the standard "centering increases moments" step, see
Ledoux–Talagrand, *Probability in Banach Spaces* (1991), Lemma 6.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Pointwise core of HDP Eq. (6.13)**: for integrable mean-zero `g` under a
probability measure, `‖y‖ ≤ ∫ ‖y + g z‖ ∂P` — insert the mean of `g` inside
the norm and apply Jensen (`norm_integral_le_integral_norm`). -/
theorem norm_le_integral_norm_add {β : Type*} {mβ : MeasurableSpace β}
    {P : Measure β} [IsProbabilityMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : β → E}
    -- LEAN-ONLY: integrability so the Bochner mean of g is genuine; implicit
    -- in the book's E‖Z‖ < ∞ standing assumption
    (hg : Integrable g P)
    -- USER-INPUT: E Z = 0; HDP Eq. (6.13)
    (hg0 : ∫ z, g z ∂P = 0)
    (y : E) :
    ‖y‖ ≤ ∫ z, ‖y + g z‖ ∂P := by
  have hy : ∫ z, (y + g z) ∂P = y := by
    rw [integral_add (integrable_const y) hg, integral_const, hg0, add_zero,
        probReal_univ, one_smul]
  calc ‖y‖ = ‖∫ z, (y + g z) ∂P‖ := by rw [hy]
    _ ≤ ∫ z, ‖y + g z‖ ∂P := norm_integral_le_integral_norm _

/-- **HDP Eq. (6.13)**, product form: for independent `Y ∼ P₁`-component `f`
and mean-zero `Z ∼ P₂`-component `g` (independence by construction on
`P₁.prod P₂`), `E‖Y‖ ≤ E‖Y + Z‖`. Named-sorry debt candidate of this work
item. -/
theorem integral_norm_le_integral_norm_add_prod {α β : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (P₁ : Measure α) (P₂ : Measure β)
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : α → E} {g : β → E}
    -- LEAN-ONLY: integrability of the Y-component; book's E‖Y‖ < ∞
    (hf : Integrable f P₁)
    -- LEAN-ONLY: integrability of the Z-component; book's E‖Z‖ < ∞
    (hg : Integrable g P₂)
    -- USER-INPUT: E Z = 0; HDP Eq. (6.13)
    (hg0 : ∫ z, g z ∂P₂ = 0) :
    ∫ x, ‖f x‖ ∂P₁ ≤ ∫ p, ‖f p.1 + g p.2‖ ∂(P₁.prod P₂) := by
  have hF : Integrable (fun p : α × β => ‖f p.1 + g p.2‖) (P₁.prod P₂) :=
    ((hf.comp_fst P₂).add (hg.comp_snd P₁)).norm
  rw [integral_prod _ hF]
  refine integral_mono hf.norm hF.integral_prod_left (fun x => ?_)
  exact norm_le_integral_norm_add hg hg0 (f x)

end StatLean.ConcentrationInequalities
