module
public import StatLean.AsymptoticStatistics.Examples.MARMean.Tangent
public import StatLean.AsymptoticStatistics.Core.BoundedLinearFunctional

@[expose] public section

/-!
# Efficient influence function for the MAR-mean parameter (vdV Example 25.43)

The verification half of the missing-at-random (MAR) mean concrete-EIF example
of van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), Example 25.43
(§25.5.3, p.383), building on Lemma 25.41 (p.381-382) and Theorem 25.40 (p.380).

## The book content

For the MAR observation `X = (W, R, R·Y)` with propensity `π(W) = P(R = 1 | W)`,
Lemma 25.41 characterizes **all** influence functions of the mean `ψ = E(Y)` as

    φ_IPW + b,     φ_IPW(x) = (R/π(W))·(Y − ψ),

where `b` ranges over the coarsening scores (`E_R(b | Y) = 0`). Example 25.43
specializes this to MAR: the coarsening scores are exactly `b_c = ((R − π)/π)·c(W)`,
and the **efficient** influence function is found by minimizing variance over `c`,
with solution `c = E(χ_Q(Y) | X) = m(W) − ψ` (`m = E(Y | W)`). The result is the
AIPW form

    φ = (R/π(W))·(Y − m(W)) + m(W) − ψ.

The heart of the example is the **orthogonality relation** vdV verifies (p.383):
`φ ⊥ b_c` for every `c`, which places `φ` inside the (closed) tangent space and
hence certifies it as the efficient influence function.

## Formalized scope

The theorem `marMean_isEIF` uses the induced law `marObsMeasure Q r`
and the constructed closed tangent `marObservedTangent Q r`. The bridge from the
latent full-data/kernel representation to abstract Theorem 25.40 is derived in
`MARMean/Tangent.lean`.

* **orthogonality / efficiency membership**: the relation
  `marMean_eif_orthogonal_coarsening` is proved from the MAR moment identities, and
  `mem_marObservedTangent_iff` converts it to membership in the constructed tangent;
* **influence-function property** (`⟪φ, g⟫ = ψ̇(g)`): from the decomposition
  `φ = φ_IPW − b_{m−ψ}` (`marMean_eif_eq_ipw_sub_coarsening`), the coarsening
  correction is `T`-orthogonal, so `φ` inherits the IF property of `φ_IPW`.

The genuine external inputs are the response-kernel linkage, propensity /
complete-case / Bernoulli-variance
moment identities (`hProp`, `hReg`, `hVar` — vdV's model structure, mentioning only
`π`, `m`, `R`, `Y`, never `φ`) and the stated moment regularity. The separate `L²`
theorem `marMean_isEIF_of_pathwise` instead assumes a tangent space `T`, its
orthogonality characterization `hT_char`, pathwise differentiability `hpd`, and
the Lemma-25.41 base representer property `hipw_c_IF`.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.MassMethod

namespace AsymptoticStatistics.Examples.MARMean

variable {X : Type*} [MeasurableSpace X]
variable {P : Measure (MARObs X)} [IsProbabilityMeasure P]

/-! ### L²₀ inner-product / integrability helpers (shared with the other examples) -/

/-- Inner product of two mean-zero `L²(P)` elements as an integral of the
pointwise product. (Real inner product reverses the order.) -/
private lemma l2zm_inner_eq_integral (v w : ↥(L2ZeroMean P)) :
    ⟪v, w⟫_ℝ
      = ∫ o, ((w : Lp ℝ 2 P) : MARObs X → ℝ) o
              * ((v : Lp ℝ 2 P) : MARObs X → ℝ) o ∂P := by
  change ⟪(v : Lp ℝ 2 P), (w : Lp ℝ 2 P)⟫_ℝ = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards with o
  rfl

/-- The `L²(P)`-membership of the coercion of an `L²₀(P)` element. -/
private lemma memLp_coeFn (v : ↥(L2ZeroMean P)) :
    MemLp ((v : Lp ℝ 2 P) : MARObs X → ℝ) 2 P :=
  Lp.memLp (v : Lp ℝ 2 P)

/-! ### The MAR moment identities (vdV Example 25.43 model structure)

These are the genuine external inputs: the conditional-moment structure of the MAR
model. They mention only the propensity `π`, the outcome regression `m`, and the
raw data `R`, `Y` — never the efficient influence function — so nothing about the
answer is assumed.

They are stated in the *unconditional* weak form `∀ (test function), ∫ … = ∫ …`,
i.e. the conditional-moment identities `E(R | W) = π`, `E(R·Y | W) = π·m`,
`E((R−π)² | W) = π(1−π)` hold against every integrable test function of the
observed covariate. This is the natural L¹-formulation of the three MAR moments;
the user supplies a model where they hold. -/

/-- Propensity identity `E(R | W) = π(W)`, in integral form `E(R·f) = E(π·f)`
for every test function `f` (vdV: `π(y) = P(δ = 1 | Y = y)`). -/
def MARPropensity (π : X → ℝ) (P : Measure (MARObs X)) : Prop :=
  ∀ (f : X → ℝ), ∫ o, ind o.r * f o.x ∂P = ∫ o, π o.x * f o.x ∂P

/-- Complete-case regression identity `E(R·Y | W) = π(W)·m(W)`, in integral form
`E(R·Y·g) = E(π·m·g)` (MAR: `δ ⟂ Y | W`, and `m = E(Y | W)`). -/
def MARRegression (π m : X → ℝ) (P : Measure (MARObs X)) : Prop :=
  ∀ (g : X → ℝ), ∫ o, ind o.r * o.ry * g o.x ∂P = ∫ o, π o.x * m o.x * g o.x ∂P

/-- Bernoulli-variance identity `E((R − π)² | W) = π(1 − π)`, in integral form
`E((R − π)²·h) = E(π(1 − π)·h)` (`R | W ∼ Bernoulli(π)`). -/
def MARVariance (π : X → ℝ) (P : Measure (MARObs X)) : Prop :=
  ∀ (h : X → ℝ),
    ∫ o, (ind o.r - π o.x) ^ 2 * h o.x ∂P = ∫ o, π o.x * (1 - π o.x) * h o.x ∂P

omit [IsProbabilityMeasure P] in
/-- **The IPW functional equals the outcome-regression (plug-in) functional**:
`marMean_Ψ π P = ∫ m(W) dP` under the complete-case regression identity `hReg`
(`m = E(Y | W)`).

This is the in-model faithful statement of the MAR-mean *identification*. The
observed-data `MARObs` model carries no unconditional outcome `Y`, so vdV's target
parameter `ψ = E[Y]` is *represented* by the IPW functional `marMean_Ψ = ∫ R·Y/π`;
this lemma shows it coincides with the regression form `∫ m`. Both equal `E[Y]` in a
full-data model (tower property `E[E(Y|W)] = E[Y]`), but that last identification
lives outside this observed-data model. vdV Ex 25.43 / §25.5.3. -/
theorem marMean_Ψ_eq_regression (π m : X → ℝ)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hReg : MARRegression π m P) :
    marMean_Ψ π P = ∫ o, m o.x ∂P := by
  change (∫ o, ind o.r * o.ry / π o.x ∂P) = ∫ o, m o.x ∂P
  rw [show (∫ o, ind o.r * o.ry / π o.x ∂P) = ∫ o, ind o.r * o.ry * (1 / π o.x) ∂P from
      integral_congr_ae (by filter_upwards with o; rw [mul_one_div])]
  rw [hReg (fun x => 1 / π x)]
  exact integral_congr_ae (by filter_upwards with o; have hne := hπ o; field_simp)

/-! ### Mean-zero of the AIPW EIF -/

/-- The AIPW efficient influence function integrates to zero (the centering
`ψ = marMean_Ψ π P` together with the propensity identity). Needed to lift it to
`L²₀(P)`.

`hm_int` (`m = E(Y | W)` has a mean) and `hInt_weight` (the IPW weight `R/π` is
integrable — automatic when `π` is bounded away from 0, vdV Lem 25.41) are vdV's
"existence of moments" conditions. -/
theorem marMean_eif_mean_zero (π m : X → ℝ)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hProp : MARPropensity π P)
    (hm_int : Integrable (fun o => m o.x) P)
    (hInt_weight : Integrable (fun o => ind o.r / π o.x) P)
    (hLp_ipw : MemLp (marMean_ipwRep π (marMean_Ψ π P)) 2 P)
    (hLp_coar : MemLp (marMean_coarseningScore π (fun x => m x - marMean_Ψ π P)) 2 P) :
    ∫ o, marMean_eif π m (marMean_Ψ π P) o ∂P = 0 := by
  set ψ₀ := marMean_Ψ π P with hψ₀
  have hipw_int : Integrable (marMean_ipwRep π ψ₀) P := hLp_ipw.integrable one_le_two
  have hcoar_int : Integrable (marMean_coarseningScore π (fun x => m x - ψ₀)) P :=
    hLp_coar.integrable one_le_two
  have hmψ_int : Integrable (fun o => m o.x - ψ₀) P := hm_int.sub (integrable_const ψ₀)
  -- pointwise expansions of `b_{m−ψ₀}` and `φ_IPW`
  have hb_pt : ∀ o : MARObs X, marMean_coarseningScore π (fun x => m x - ψ₀) o
      = ind o.r * (m o.x - ψ₀) / π o.x - (m o.x - ψ₀) := by
    intro o
    simp only [marMean_coarseningScore]
    have hne := hπ o
    field_simp
  have hipw_pt : ∀ o : MARObs X, marMean_ipwRep π ψ₀ o
      = ind o.r * o.ry / π o.x - ψ₀ * (ind o.r / π o.x) := by
    intro o
    simp only [marMean_ipwRep]
    have hne := hπ o
    field_simp
  -- derived integrabilities of the split pieces
  have hind_mψ_int : Integrable (fun o => ind o.r * (m o.x - ψ₀) / π o.x) P := by
    have hrw : (fun o : MARObs X => ind o.r * (m o.x - ψ₀) / π o.x)
        = fun o => marMean_coarseningScore π (fun x => m x - ψ₀) o + (m o.x - ψ₀) := by
      funext o; rw [hb_pt]; ring
    rw [hrw]; exact hcoar_int.add hmψ_int
  have hnum_int : Integrable (fun o => ind o.r * o.ry / π o.x) P := by
    have hrw : (fun o : MARObs X => ind o.r * o.ry / π o.x)
        = fun o => marMean_ipwRep π ψ₀ o + ψ₀ * (ind o.r / π o.x) := by
      funext o; rw [hipw_pt]; ring
    rw [hrw]; exact hipw_int.add (hInt_weight.const_mul ψ₀)
  -- ∫ eif = ∫ φ_IPW − ∫ b_{m−ψ₀}
  have hsplit : ∫ o, marMean_eif π m ψ₀ o ∂P
      = (∫ o, marMean_ipwRep π ψ₀ o ∂P)
        - ∫ o, marMean_coarseningScore π (fun x => m x - ψ₀) o ∂P := by
    rw [← integral_sub hipw_int hcoar_int]
    exact integral_congr_ae (by
      filter_upwards with o; exact marMean_eif_eq_ipw_sub_coarsening π m ψ₀ o (hπ o))
  rw [hsplit]
  -- ∫ b_{m−ψ₀} = 0
  have hb_zero : ∫ o, marMean_coarseningScore π (fun x => m x - ψ₀) o ∂P = 0 := by
    have hprop := hProp (fun x => (m x - ψ₀) / π x)
    have hLHS : (∫ o, ind o.r * ((m o.x - ψ₀) / π o.x) ∂P)
        = ∫ o, ind o.r * (m o.x - ψ₀) / π o.x ∂P :=
      integral_congr_ae (by filter_upwards with o; rw [mul_div_assoc])
    have hRHS : (∫ o, π o.x * ((m o.x - ψ₀) / π o.x) ∂P) = ∫ o, (m o.x - ψ₀) ∂P :=
      integral_congr_ae (by filter_upwards with o; have hne := hπ o; field_simp)
    have hbsplit : (∫ o, marMean_coarseningScore π (fun x => m x - ψ₀) o ∂P)
        = (∫ o, ind o.r * (m o.x - ψ₀) / π o.x ∂P) - ∫ o, (m o.x - ψ₀) ∂P := by
      rw [← integral_sub hind_mψ_int hmψ_int]
      exact integral_congr_ae (by filter_upwards with o; rw [hb_pt])
    rw [hbsplit, ← hLHS, hprop, hRHS, sub_self]
  -- ∫ φ_IPW = 0
  have hipw_zero : ∫ o, marMean_ipwRep π ψ₀ o ∂P = 0 := by
    have hnum : ∫ o, ind o.r * o.ry / π o.x ∂P = ψ₀ := by
      simp only [hψ₀, marMean_Ψ]
    have hweight : ∫ o, ind o.r / π o.x ∂P = 1 := by
      have hprop := hProp (fun x => 1 / π x)
      have hLHS : (∫ o, ind o.r * (1 / π o.x) ∂P) = ∫ o, ind o.r / π o.x ∂P :=
        integral_congr_ae (by filter_upwards with o; rw [mul_one_div])
      have hRHS : (∫ o, π o.x * (1 / π o.x) ∂P) = 1 := by
        have h1 : (fun o : MARObs X => π o.x * (1 / π o.x)) =ᵐ[P] fun _ => (1 : ℝ) := by
          filter_upwards with o; have hne := hπ o; field_simp
        rw [integral_congr_ae h1]; simp
      rw [← hLHS, hprop, hRHS]
    have hisplit : (∫ o, marMean_ipwRep π ψ₀ o ∂P)
        = (∫ o, ind o.r * o.ry / π o.x ∂P) - ψ₀ * ∫ o, ind o.r / π o.x ∂P := by
      have h1 : (∫ o, marMean_ipwRep π ψ₀ o ∂P)
          = ∫ o, (ind o.r * o.ry / π o.x - ψ₀ * (ind o.r / π o.x)) ∂P :=
        integral_congr_ae (by filter_upwards with o; rw [hipw_pt])
      rw [h1, integral_sub hnum_int (hInt_weight.const_mul ψ₀), integral_const_mul]
    rw [hisplit, hnum, hweight, mul_one, sub_self]
  rw [hipw_zero, hb_zero, sub_zero]

/-- The AIPW efficient influence function as an element of `L²₀(P)`. -/
noncomputable def marMean_eifCandidate (π m : X → ℝ)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hProp : MARPropensity π P)
    (hLp : MemLp (marMean_eif π m (marMean_Ψ π P)) 2 P)
    (hLp_ipw : MemLp (marMean_ipwRep π (marMean_Ψ π P)) 2 P)
    (hLp_coar : MemLp (marMean_coarseningScore π (fun x => m x - marMean_Ψ π P)) 2 P)
    (hm_int : Integrable (fun o => m o.x) P)
    (hInt_weight : Integrable (fun o => ind o.r / π o.x) P) :
    CandidateIF P where
  raw := marMean_eif π m (marMean_Ψ π P)
  memLp2 := hLp
  mean_zero := marMean_eif_mean_zero π m hπ hProp hm_int hInt_weight hLp_ipw hLp_coar

/-! ### The orthogonality relation — the heart of Example 25.43 -/

/-- **Orthogonality of the AIPW EIF to every coarsening score** (vdV Example 25.43,
the variance-minimizing orthogonality relation, p.383).

For every `c : X → ℝ`, `∫ φ · b_c dP = 0`, where `φ = marMean_eif π m ψ` is the
AIPW efficient influence function and `b_c = marMean_coarseningScore π c`. Splitting
`φ = φ_IPW − b_{m−ψ}` on the first minus sign, both `∫ φ_IPW·b_c` and
`∫ b_{m−ψ}·b_c` reduce to `∫ (m − ψ)·c·(1 − π)/π dP`, so their difference vanishes.

This is the efficiency content: it places `φ` in the orthocomplement of the
coarsening scores, i.e. inside the closed observed tangent space (Theorem 25.40).

Proof: expand `φ·b_c` pointwise into three summands
`S₁ = R·Y·(R−π)·c/π²`, `S₂ = −b_m·b_c`, `S₃ = −ψ·b_c` (`b_m = coarseningScore π m`).
Then:
* `∫ S₃ = −ψ·∫ b_c = 0` (`b_c` is mean-zero, from `hProp`);
* `∫ S₁ = ∫ π·m·(1−π)c/π²` — rewrite `R·(R−π) = R·(1−π)` (`ind² = ind`) so the
  weight becomes a function of the covariate, then apply `hReg`;
* `∫ S₂ = −∫ π·(1−π)·mc/π²` via `hVar`;
* `∫ S₁ + ∫ S₂ = 0` (equal integrands).

`hc_int` (`c` integrable) and `hLp_bm` (`b_m ∈ L²`) are vdV's "square integrability"
moment conditions on the coarsening directions. -/
theorem marMean_eif_orthogonal_coarsening (π m : X → ℝ)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hProp : MARPropensity π P)
    (hReg : MARRegression π m P)
    (hVar : MARVariance π P)
    (c : X → ℝ)
    (hc_int : Integrable (fun o => c o.x) P)
    (hLp_eif : MemLp (marMean_eif π m (marMean_Ψ π P)) 2 P)
    (hLp_c : MemLp (marMean_coarseningScore π c) 2 P)
    (hLp_bm : MemLp (marMean_coarseningScore π m) 2 P) :
    ∫ o, marMean_eif π m (marMean_Ψ π P) o
        * marMean_coarseningScore π c o ∂P = 0 := by
  set ψ₀ := marMean_Ψ π P with hψ₀
  have hind_sq : ∀ o : MARObs X, ind o.r * ind o.r = ind o.r := by
    intro o; cases o.r <;> simp [ind]
  have hbc_int : Integrable (marMean_coarseningScore π c) P := hLp_c.integrable one_le_two
  -- `b_c` is mean-zero (from the propensity identity).
  have hbc_zero : ∫ o, marMean_coarseningScore π c o ∂P = 0 := by
    have hpt : ∀ o : MARObs X,
        marMean_coarseningScore π c o = ind o.r * (c o.x / π o.x) - c o.x := by
      intro o; simp only [marMean_coarseningScore]; have hne := hπ o; field_simp
    have hind_c_int : Integrable (fun o => ind o.r * (c o.x / π o.x)) P :=
      (hbc_int.add hc_int).congr
        (by filter_upwards with o; simp only [Pi.add_apply]; linear_combination hpt o)
    have hsplit : (∫ o, marMean_coarseningScore π c o ∂P)
        = (∫ o, ind o.r * (c o.x / π o.x) ∂P) - ∫ o, c o.x ∂P := by
      rw [← integral_sub hind_c_int hc_int]
      exact integral_congr_ae (by filter_upwards with o; rw [hpt])
    have hR : (∫ o, π o.x * (c o.x / π o.x) ∂P) = ∫ o, c o.x ∂P :=
      integral_congr_ae (by filter_upwards with o; have hne := hπ o; field_simp)
    rw [hsplit, hProp (fun x => c x / π x), hR, sub_self]
  -- three-term expansion `φ·b_c = S₁ + S₂ + S₃` (pure algebra, no `ind² = ind`).
  have hexp : ∀ o : MARObs X, marMean_eif π m ψ₀ o * marMean_coarseningScore π c o
      = ind o.r * o.ry * (ind o.r - π o.x) * c o.x / π o.x ^ 2
        + -(marMean_coarseningScore π m o * marMean_coarseningScore π c o)
        + -(ψ₀ * marMean_coarseningScore π c o) := by
    intro o
    simp only [marMean_eif, marMean_coarseningScore]
    have hne := hπ o
    field_simp
    ring
  -- integrabilities of the three summands
  have hI_bc : Integrable
      (fun o => marMean_eif π m ψ₀ o * marMean_coarseningScore π c o) P :=
    hLp_eif.integrable_mul hLp_c
  have hI_S2 : Integrable
      (fun o => -(marMean_coarseningScore π m o * marMean_coarseningScore π c o)) P :=
    (hLp_bm.integrable_mul hLp_c).neg
  have hI_S3 : Integrable (fun o => -(ψ₀ * marMean_coarseningScore π c o)) P :=
    (hbc_int.const_mul ψ₀).neg
  have hI_S1 : Integrable
      (fun o => ind o.r * o.ry * (ind o.r - π o.x) * c o.x / π o.x ^ 2) P :=
    ((hI_bc.sub hI_S2).sub hI_S3).congr (by
      filter_upwards with o
      simp only [Pi.sub_apply]
      linear_combination hexp o)
  -- explicitly-typed integrability of `S₁ + S₂` (so `integral_add` matches the goal)
  have hI_S12 : Integrable (fun o =>
      ind o.r * o.ry * (ind o.r - π o.x) * c o.x / π o.x ^ 2
        + -(marMean_coarseningScore π m o * marMean_coarseningScore π c o)) P :=
    hI_S1.add hI_S2
  -- split `∫ φ·b_c = ∫ S₁ + ∫ S₂ + ∫ S₃`
  have hsplit3 : (∫ o, marMean_eif π m ψ₀ o * marMean_coarseningScore π c o ∂P)
      = (∫ o, ind o.r * o.ry * (ind o.r - π o.x) * c o.x / π o.x ^ 2 ∂P)
        + (∫ o, -(marMean_coarseningScore π m o * marMean_coarseningScore π c o) ∂P)
        + ∫ o, -(ψ₀ * marMean_coarseningScore π c o) ∂P := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
      integral_add hI_S12 hI_S3, integral_add hI_S1 hI_S2]
  -- `∫ S₃ = 0`
  have hS3 : (∫ o, -(ψ₀ * marMean_coarseningScore π c o) ∂P) = 0 := by
    rw [integral_neg, integral_const_mul, hbc_zero, mul_zero, neg_zero]
  -- `∫ S₁ = ∫ π·m·(1−π)c/π²` (rewrite `R·(R−π) = R·(1−π)`, then `hReg`)
  have hS1 : (∫ o, ind o.r * o.ry * (ind o.r - π o.x) * c o.x / π o.x ^ 2 ∂P)
      = ∫ o, π o.x * m o.x * ((1 - π o.x) * c o.x / π o.x ^ 2) ∂P := by
    rw [integral_congr_ae (g := fun o =>
        ind o.r * o.ry * ((1 - π o.x) * c o.x / π o.x ^ 2)) (by
      filter_upwards with o
      have key : ind o.r * (ind o.r - π o.x) = ind o.r * (1 - π o.x) := by
        rw [mul_sub, mul_sub, hind_sq o, mul_one]
      linear_combination (o.ry * c o.x / π o.x ^ 2) * key)]
    exact hReg (fun x => (1 - π x) * c x / π x ^ 2)
  -- `∫ S₂ = −∫ π·(1−π)·mc/π²` (via `hVar`)
  have hS2 : (∫ o, -(marMean_coarseningScore π m o * marMean_coarseningScore π c o) ∂P)
      = -∫ o, π o.x * (1 - π o.x) * (m o.x * c o.x / π o.x ^ 2) ∂P := by
    rw [integral_neg]
    congr 1
    rw [integral_congr_ae (g := fun o =>
        (ind o.r - π o.x) ^ 2 * (m o.x * c o.x / π o.x ^ 2)) (by
      filter_upwards with o
      simp only [marMean_coarseningScore]
      ring)]
    exact hVar (fun x => m x * c x / π x ^ 2)
  -- assemble: `∫ S₁ + ∫ S₂ = 0`, `∫ S₃ = 0`
  rw [hsplit3, hS3, add_zero, hS1, hS2,
    integral_congr_ae (g := fun o => π o.x * (1 - π o.x) * (m o.x * c o.x / π o.x ^ 2))
      (by filter_upwards with o; ring),
    add_neg_cancel]

/-! ### The two conditions of the EIF definition -/

/-- Under the supplied characterization `hT_char`, the AIPW candidate lies in
the tangent space `T`. Its orthogonality to every coarsening score follows from
`marMean_eif_orthogonal_coarsening`. -/
theorem marMean_eif_mem_T (π m : X → ℝ)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hProp : MARPropensity π P)
    (hReg : MARRegression π m P)
    (hVar : MARVariance π P)
    (hLp : MemLp (marMean_eif π m (marMean_Ψ π P)) 2 P)
    (hLp_ipw : MemLp (marMean_ipwRep π (marMean_Ψ π P)) 2 P)
    (hLp_coar : MemLp (marMean_coarseningScore π (fun x => m x - marMean_Ψ π P)) 2 P)
    (hm_int : Integrable (fun o => m o.x) P)
    (hInt_weight : Integrable (fun o => ind o.r / π o.x) P)
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (hT_char : ∀ (w : ↥(L2ZeroMean P)), w ∈ T ↔
        ∀ (c : X → ℝ), Integrable (fun o => c o.x) P →
          MemLp (marMean_coarseningScore π c) 2 P →
          ∫ o, ((w : Lp ℝ 2 P) : MARObs X → ℝ) o
                * marMean_coarseningScore π c o ∂P = 0)
    (hLp_bm : MemLp (marMean_coarseningScore π m) 2 P) :
    (marMean_eifCandidate π m hπ hProp hLp hLp_ipw hLp_coar hm_int hInt_weight).toL2ZeroMean
      ∈ T := by
  rw [hT_char]
  intro c hc_int hLp_c
  set eifL2 :=
    (marMean_eifCandidate π m hπ hProp hLp hLp_ipw hLp_coar hm_int hInt_weight).toL2ZeroMean
    with heifL2
  -- coeFn of the candidate agrees a.e. with the raw AIPW formula.
  have hcoe : ((eifL2 : Lp ℝ 2 P) : MARObs X → ℝ) =ᵐ[P] marMean_eif π m (marMean_Ψ π P) :=
    CandidateIF.coeFn_toL2ZeroMean _
  rw [show (∫ o, ((eifL2 : Lp ℝ 2 P) : MARObs X → ℝ) o * marMean_coarseningScore π c o ∂P)
        = ∫ o, marMean_eif π m (marMean_Ψ π P) o * marMean_coarseningScore π c o ∂P from by
      apply integral_congr_ae
      filter_upwards [hcoe] with o ho
      rw [ho]]
  exact marMean_eif_orthogonal_coarsening π m hπ hProp hReg hVar c hc_int hLp hLp_c hLp_bm

/-- The AIPW EIF is an influence function for `marMean_Ψ π` (the *influence-function*
half). From the decomposition `φ = (R·Y/π − ψ) − b_m` and the fact that the coarsening
correction `b_m` is orthogonal to every `g ∈ T`, `φ` inherits the IF identity of the
**centered IPW representer** `φ_c := R·Y/π − ψ` (`hipw_c_IF`).

`φ_c` is the canonical influence function of the *linear* functional
`marMean_Ψ = ∫ R·Y/π`. In `marMean_isEIF`, this identity follows from the
mass method (`pathwiseDifferentiableAt_of_TVFrechet`); in
`marMean_isEIF_of_pathwise`, it is an explicit hypothesis. -/
theorem marMean_eif_isIF (π m : X → ℝ)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hProp : MARPropensity π P)
    (hLp : MemLp (marMean_eif π m (marMean_Ψ π P)) 2 P)
    (hLp_ipw : MemLp (marMean_ipwRep π (marMean_Ψ π P)) 2 P)
    (hLp_coar : MemLp (marMean_coarseningScore π (fun x => m x - marMean_Ψ π P)) 2 P)
    (hLp_bm : MemLp (marMean_coarseningScore π m) 2 P)
    (hm_int : Integrable (fun o => m o.x) P)
    (hInt_weight : Integrable (fun o => ind o.r / π o.x) P)
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (hT_char : ∀ (w : ↥(L2ZeroMean P)), w ∈ T ↔
        ∀ (c : X → ℝ), Integrable (fun o => c o.x) P →
          MemLp (marMean_coarseningScore π c) 2 P →
          ∫ o, ((w : Lp ℝ 2 P) : MARObs X → ℝ) o
                * marMean_coarseningScore π c o ∂P = 0)
    (dψ : T →L[ℝ] ℝ)
    -- The centered IPW representer `φ_c = R·Y/π − ψ` and its influence-function identity.
    (φ_c : ↥(L2ZeroMean P))
    (hφ_c_ae : ((φ_c : Lp ℝ 2 P) : MARObs X → ℝ)
        =ᵐ[P] fun o => ind o.r * o.ry / π o.x - marMean_Ψ π P)
    (hipw_c_IF : IsInfluenceFunction P T dψ φ_c) :
    IsInfluenceFunction P T dψ
      (marMean_eifCandidate π m hπ hProp hLp hLp_ipw hLp_coar hm_int hInt_weight).toL2ZeroMean := by
  intro g
  set ψ₀ := marMean_Ψ π P with hψ₀
  set eifL2 :=
    (marMean_eifCandidate π m hπ hProp hLp hLp_ipw hLp_coar hm_int hInt_weight).toL2ZeroMean
    with heifL2
  -- L²-membership of the coeFns, and Hölder integrability of the two products.
  have hg2 : MemLp (((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : MARObs X → ℝ) 2 P :=
    memLp_coeFn (g : ↥(L2ZeroMean P))
  have hφ2 : MemLp (((φ_c : Lp ℝ 2 P)) : MARObs X → ℝ) 2 P := memLp_coeFn φ_c
  have hInt_gφ : Integrable (fun o =>
      (((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : MARObs X → ℝ) o
        * (((φ_c : Lp ℝ 2 P)) : MARObs X → ℝ) o) P :=
    hg2.integrable_mul hφ2
  have hInt_gb : Integrable (fun o =>
      (((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : MARObs X → ℝ) o
        * marMean_coarseningScore π m o) P :=
    hg2.integrable_mul hLp_bm
  -- `eifL2`'s coeFn agrees a.e. with `φ_c − b_m` (candidate coeFn + centered decomp).
  have hcoe_eif : ((eifL2 : Lp ℝ 2 P) : MARObs X → ℝ) =ᵐ[P] marMean_eif π m ψ₀ :=
    CandidateIF.coeFn_toL2ZeroMean _
  have hdecomp_ae : ((eifL2 : Lp ℝ 2 P) : MARObs X → ℝ)
      =ᵐ[P] fun o => (((φ_c : Lp ℝ 2 P)) : MARObs X → ℝ) o
              - marMean_coarseningScore π m o := by
    filter_upwards [hcoe_eif, hφ_c_ae] with o hoe hoi
    rw [hoe, marMean_eif_eq_centeredIpw_sub_coarsening π m ψ₀ o (hπ o), hoi]
  -- `⟪eifL2, g⟫ = ∫ g·eif = ∫ g·φ_c − ∫ g·b_m = ⟪φ_c, g⟫ − 0 = dψ g`.
  rw [l2zm_inner_eq_integral eifL2 (g : ↥(L2ZeroMean P))]
  have hmul_ae : (fun o => (((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : MARObs X → ℝ) o
        * ((eifL2 : Lp ℝ 2 P) : MARObs X → ℝ) o)
      =ᵐ[P] fun o => (((g : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : MARObs X → ℝ) o
        * ((((φ_c : Lp ℝ 2 P)) : MARObs X → ℝ) o
            - marMean_coarseningScore π m o) := by
    filter_upwards [hdecomp_ae] with o ho
    rw [ho]
  rw [integral_congr_ae hmul_ae]
  simp_rw [mul_sub]
  rw [integral_sub hInt_gφ hInt_gb,
    (hT_char (g : ↥(L2ZeroMean P))).mp g.2 m hm_int hLp_bm,
    sub_zero, ← l2zm_inner_eq_integral φ_c (g : ↥(L2ZeroMean P)), hipw_c_IF g]

/-! ### Pathwise differentiability and efficiency -/

/-- **Pathwise differentiability of the MAR-mean functional over `T`.**
`marMean_Ψ = ∫ R·Y/π = meanFunctional (R·Y/π)` is a *linear* functional; when its
representer `R·Y/π` is bounded and measurable, its score identity
(`meanFunctional_isTVFrechetExpansion`, vdV Ex 25.24) is a **theorem**, fed to
`pathwiseDifferentiableAt_of_TVFrechet` to get pathwise differentiability over the full
nonparametric tangent `⊤`, with derivative the inner product against the centered
representer `φ_c = R·Y/π − ψ`. This restricts to any `T ⊆ ⊤`; the derivative on `T` is
`g ↦ ⟪φ_c, g⟫`.

The regularity inputs `h_ipwMeas` and `h_ipwBdd` suffice to derive both pathwise
differentiability and the influence-function property. The bounded IPW
representer assumption subsumes vdV Lemma 25.41's condition that `R(C|y)` is
bounded away from zero (via `π ≥ δ`) together with bounded observed response. -/
noncomputable def marMean_pathwise (π : X → ℝ)
    (h_ipwMeas : Measurable (fun o : MARObs X => ind o.r * o.ry / π o.x))
    (h_ipwBdd : ∃ C : ℝ, ∀ o : MARObs X, |ind o.r * o.ry / π o.x| ≤ C)
    (T : Submodule ℝ ↥(L2ZeroMean P)) :
    PathwiseDifferentiableAt P T (marMean_Ψ π) where
  derivative :=
    (innerSL ℝ ((centeredCandidate (fun o : MARObs X => ind o.r * o.ry / π o.x)
        (memLp_two_of_bounded (P := P) h_ipwMeas h_ipwBdd)).toL2ZeroMean)).comp
      (Submodule.subtypeL T)
  derivative_spec := by
    intro γ h_in_T
    exact (pathwiseDifferentiableAt_of_TVFrechet (memLp_two_of_bounded (P := P) h_ipwMeas h_ipwBdd)
      (meanFunctional_isTVFrechetExpansion (P := P) h_ipwMeas h_ipwBdd)).derivative_spec γ
      Submodule.mem_top

/-- **Pathwise differentiability of the globally bounded MAR extension.**

Unlike `marMean_pathwise`, this helper does not claim differentiability of the
raw IPW functional from an almost-everywhere bound.  It differentiates the
explicit global extension `marMeanBounded_Ψ π C`; the latter agrees with the raw
functional at the MAR model law under `h_ipwBddAE` and stays bounded along
unrestricted QMD paths. -/
noncomputable def marMeanBounded_pathwise (π : X → ℝ) (C : ℝ)
    (h_ipwMeas : Measurable (fun o : MARObs X => ind o.r * o.ry / π o.x))
    (T : Submodule ℝ ↥(L2ZeroMean P)) :
    PathwiseDifferentiableAt P T (marMeanBounded_Ψ π C) := by
  exact clippedMeanFunctional_pathwise C h_ipwMeas T

/-- **Efficient influence function for the MAR-mean parameter (vdV Example 25.43).**

For the MAR observation model on `MARObs X` with propensity `π` and outcome
regression `m`, the AIPW formula
`φ = (R/π)·(Y − m) + m − ψ` is the **efficient influence function** of the mean
functional `marMeanBounded_Ψ π C` at the induced observed law `marObsMeasure Q r`,
over the constructed closed tangent `marObservedTangent Q r`.  Under the explicit
`P`-a.e. bound this extension has the same base-point value as `marMean_Ψ π`.

The analytic and Example-25.43 algebraic content is combined with the concrete
latent-model bridge:
* `φ ∈ marObservedTangent Q r` (efficiency) — `marMean_eif_mem_T` derives the
  needed orthogonality from the MAR moment identities, while
  `mem_marObservedTangent_iff` derives the tangent characterization from the
  induced law `(Q ⊗ₘ r).map marObsMap` and abstract Theorem 25.40;
* `⟪φ, g⟫ = ψ̇(g)` (influence function) — `marMean_eif_isIF`, from the decomposition
  `φ = φ_c − b_m` (`φ_c = R·Y/π − ψ` the centered IPW representer) plus the
  influence-function identity of `φ_c`, which is itself **derived** from the mass
  method for the globally clipped extension (`marMeanBounded_pathwise`), followed
  by the `P`-a.e. centered-representer transport.

The pathwise derivative is that of the globally clipped extension
`marMeanBounded_Ψ π C`, as supplied by `marMeanBounded_pathwise`.
It agrees at the observed law with the raw IPW estimand under `h_ipwBddAE`, but
unrestricted QMD paths remain globally controlled.  The stronger bounded-response
restriction is explicit and independent of tangent identification. The tangent
space is the constructed `marObservedTangent Q r`; its characterization follows
from the latent MAR model. -/
theorem marMean_isEIF
    (Q : Measure (X × ℝ)) [IsProbabilityMeasure Q]
    (r : Kernel (X × ℝ) Bool) [IsMarkovKernel r]
    (π m : X → ℝ)
    -- USER-INPUT: MAR response model, propensity, regression, and conditional
    -- variance identities; vdV Example 25.43, p. 383.
    (hπr : MARResponseKernel π r)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hProp : MARPropensity π (marObsMeasure Q r))
    (hReg : MARRegression π m (marObsMeasure Q r))
    (hVar : MARVariance π (marObsMeasure Q r))
    -- USER-INPUT: square-integrability of the influence-function and coarsening-score
    -- representatives; vdV Example 25.43's moment conditions.
    (hLp : MemLp (marMean_eif π m (marMean_Ψ π (marObsMeasure Q r))) 2
      (marObsMeasure Q r))
    (hLp_ipw : MemLp (marMean_ipwRep π (marMean_Ψ π (marObsMeasure Q r))) 2
      (marObsMeasure Q r))
    (hLp_coar : MemLp
      (marMean_coarseningScore π (fun x => m x - marMean_Ψ π (marObsMeasure Q r))) 2
      (marObsMeasure Q r))
    (hLp_bm : MemLp (marMean_coarseningScore π m) 2 (marObsMeasure Q r))
    -- USER-INPUT: integrability of `m = E(Y|W)` and the IPW weight `R/π`;
    -- vdV Example 25.43's moment conditions.
    (hm_int : Integrable (fun o : MARObs X => m o.x) (marObsMeasure Q r))
    (hInt_weight : Integrable (fun o : MARObs X => ind o.r / π o.x) (marObsMeasure Q r))
    -- LEAN-ONLY: measurability of the IPW integrand used to define the clipped extension.
    (h_ipwMeas : Measurable (fun o : MARObs X => ind o.r * o.ry / π o.x))
    (C : ℝ)
    -- USER-INPUT: bounded observed IPW response; this strengthened regularity
    -- identifies the clipped extension with the raw estimand at the model law.
    (h_ipwBddAE : ∀ᵐ o ∂(marObsMeasure Q r), |ind o.r * o.ry / π o.x| ≤ C)
    :
    IsEfficientInfluenceFunction (marObsMeasure Q r) (marObservedTangent Q r)
      (marMeanBounded_pathwise π C h_ipwMeas (marObservedTangent Q r)).derivative
      (marMean_eifCandidate π m hπ hProp hLp hLp_ipw hLp_coar hm_int hInt_weight).toL2ZeroMean := by
  have hπ' : ∀ x, π x ≠ 0 := fun x ↦ hπ ⟨x, false, 0⟩
  have hT_char : ∀ (w : ↥(L2ZeroMean (marObsMeasure Q r))),
      w ∈ marObservedTangent Q r ↔
        ∀ (c : X → ℝ), Integrable (fun o : MARObs X ↦ c o.x) (marObsMeasure Q r) →
          MemLp (marMean_coarseningScore π c) 2 (marObsMeasure Q r) →
          ∫ o, ((w : Lp ℝ 2 (marObsMeasure Q r)) : MARObs X → ℝ) o
                * marMean_coarseningScore π c o ∂(marObsMeasure Q r) = 0 :=
    fun w ↦ mem_marObservedTangent_iff Q r π hπr hπ' w
  let hf : MemLp (clippedFunction (fun o : MARObs X ↦ ind o.r * o.ry / π o.x) C) 2
      (marObsMeasure Q r) :=
    memLp_two_of_bounded (measurable_clippedFunction h_ipwMeas)
      ⟨|C + 1|, fun o ↦ abs_clippedFunction_le o⟩
  let φ_c := (centeredCandidate
      (P := marObsMeasure Q r)
      (clippedFunction (fun o : MARObs X ↦ ind o.r * o.ry / π o.x) C) hf).toL2ZeroMean
  have hφ_c_ae :
      (((φ_c : ↥(L2ZeroMean (marObsMeasure Q r))) : Lp ℝ 2 (marObsMeasure Q r)) :
          MARObs X → ℝ)
        =ᵐ[marObsMeasure Q r]
          fun o ↦ ind o.r * o.ry / π o.x - marMean_Ψ π (marObsMeasure Q r) := by
    exact centeredCandidate_clipped_ae_eq_raw_centered h_ipwMeas h_ipwBddAE
  have hipw_c_IF : IsInfluenceFunction (marObsMeasure Q r) (marObservedTangent Q r)
      (marMeanBounded_pathwise π C h_ipwMeas (marObservedTangent Q r)).derivative φ_c := by
    intro g
    rfl
  exact ⟨marMean_eif_isIF π m hπ hProp hLp hLp_ipw hLp_coar hLp_bm hm_int hInt_weight
      (marObservedTangent Q r) hT_char
      (marMeanBounded_pathwise π C h_ipwMeas (marObservedTangent Q r)).derivative
      φ_c hφ_c_ae hipw_c_IF,
    marMean_eif_mem_T π m hπ hProp hReg hVar hLp hLp_ipw hLp_coar hm_int hInt_weight
      (marObservedTangent Q r) hT_char hLp_bm⟩

/-- Concrete jointly satisfiable instance of the bounded MAR assumptions.

The finite latent model uses `X = Unit`, `Q = dirac ((),0)`, the fair Bool
response kernel, `π ≡ 1/2`, and `m ≡ 0`. The conjunction covers every external
input of `marMean_isEIF`, together with positive observed/missing atoms and a
nonzero concrete coarsening score. -/
theorem fairMAR_bounded_headline_inputs :
    let Q : Measure (Unit × ℝ) := Measure.dirac ((), 0)
    let r : Kernel (Unit × ℝ) Bool := fairBoolKernel
    let P : Measure (MARObs Unit) := marObsMeasure Q r
    let π : Unit → ℝ := fun _ ↦ 1 / 2
    let m : Unit → ℝ := fun _ ↦ 0
    let C : ℝ := 0
    MARResponseKernel π r ∧
    (∀ o : MARObs Unit, π o.x ≠ 0) ∧
    MARPropensity π P ∧
    MARRegression π m P ∧
    MARVariance π P ∧
    MemLp (marMean_eif π m (marMean_Ψ π P)) 2 P ∧
    MemLp (marMean_ipwRep π (marMean_Ψ π P)) 2 P ∧
    MemLp (marMean_coarseningScore π (fun x => m x - marMean_Ψ π P)) 2 P ∧
    MemLp (marMean_coarseningScore π m) 2 P ∧
    Integrable (fun o : MARObs Unit => m o.x) P ∧
    Integrable (fun o : MARObs Unit => ind o.r / π o.x) P ∧
    Measurable (fun o : MARObs Unit => ind o.r * o.ry / π o.x) ∧
    (∀ᵐ o ∂P, |ind o.r * o.ry / π o.x| ≤ C) ∧
    0 < P {o : MARObs Unit | o.r = true} ∧
    0 < P {o : MARObs Unit | o.r = false} ∧
    ¬ (marMean_coarseningScore π (fun _ => 1) =ᵐ[P] fun _ => 0) := by
  dsimp only
  let obs : Bool → MARObs Unit := fun b ↦ ⟨(), b, 0⟩
  have hobs : Measurable obs := by
    have hsource : Measurable (fun b : Bool ↦ (((), (0 : ℝ)), b)) := by fun_prop
    simpa [obs, marObsMap] using! (measurable_marObsMap (X := Unit)).comp hsource
  have htuple : Measurable (fun o : MARObs Unit ↦ (o.x, o.r, o.ry)) :=
    Measurable.of_comap_le le_rfl
  have hx : Measurable (fun o : MARObs Unit ↦ o.x) := measurable_fst.comp htuple
  have hr : Measurable (fun o : MARObs Unit ↦ o.r) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hry : Measurable (fun o : MARObs Unit ↦ o.ry) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hind : Measurable (fun o : MARObs Unit ↦ ind o.r) :=
    (measurable_of_finite ind).comp hr
  have hrawMeas : Measurable
      (fun o : MARObs Unit ↦ ind o.r * o.ry / (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x) :=
    (hind.mul hry).div measurable_const
  have hweightMeas : Measurable
      (fun o : MARObs Unit ↦ ind o.r / (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x) :=
    hind.div measurable_const
  have hP : marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel =
      fairBoolMeasure.map obs := by
    rw [marObsMeasure, fairBoolKernel, Measure.compProd_const, Measure.dirac_prod,
      Measure.map_map]
    · congr 1
      funext b
      cases b <;> rfl
    · exact measurable_marObsMap
    · fun_prop
  have hIntegral (F : MARObs Unit → ℝ) (hF : StronglyMeasurable F) :
      ∫ o, F o ∂marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel =
        (F (obs false) + F (obs true)) / 2 := by
    rw [hP, integral_map_of_stronglyMeasurable hobs hF, fairBoolMeasure,
      integral_fintype Integrable.of_finite]
    simp [measureReal_def, PMF.uniformOfFintype_apply]
    ring
  have hraw_zero :
      (fun o : MARObs Unit ↦ ind o.r * o.ry / (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x)
        =ᵐ[marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel] fun _ ↦ 0 := by
    rw [hP, Filter.EventuallyEq,
      ae_map_iff hobs.aemeasurable (measurableSet_eq_fun hrawMeas measurable_const)]
    filter_upwards with b
    cases b <;> norm_num [obs, ind]
  have hψ : marMean_Ψ (fun _ : Unit ↦ (1 / 2 : ℝ))
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) = 0 := by
    unfold marMean_Ψ
    rw [integral_congr_ae hraw_zero, integral_zero]
  have hProp : MARPropensity (fun _ : Unit ↦ (1 / 2 : ℝ))
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) := by
    intro f
    have hf : Measurable f := measurable_of_finite f
    calc
      ∫ o, ind o.r * f o.x
          ∂marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel =
          ((fun o : MARObs Unit ↦ ind o.r * f o.x) (obs false) +
            (fun o : MARObs Unit ↦ ind o.r * f o.x) (obs true)) / 2 :=
        hIntegral _ ((hind.mul (hf.comp hx)).stronglyMeasurable)
      _ = (((fun x : Unit ↦ (1 / 2 : ℝ)) (obs false).x * f (obs false).x) +
            ((fun x : Unit ↦ (1 / 2 : ℝ)) (obs true).x * f (obs true).x)) / 2 := by
        simp [obs, ind]
        ring
      _ = ∫ o, (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x * f o.x
            ∂marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel :=
        (hIntegral _ ((measurable_const.mul (hf.comp hx)).stronglyMeasurable)).symm
  have hReg : MARRegression (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ 0)
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) := by
    intro g
    have hg : Measurable g := measurable_of_finite g
    calc
      ∫ o, ind o.r * o.ry * g o.x
          ∂marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel =
          ((fun o : MARObs Unit ↦ ind o.r * o.ry * g o.x) (obs false) +
            (fun o : MARObs Unit ↦ ind o.r * o.ry * g o.x) (obs true)) / 2 :=
        hIntegral _ (((hind.mul hry).mul (hg.comp hx)).stronglyMeasurable)
      _ = (((fun x : Unit ↦ (1 / 2 : ℝ)) (obs false).x * (fun _ : Unit ↦ 0)
              (obs false).x * g (obs false).x) +
            ((fun x : Unit ↦ (1 / 2 : ℝ)) (obs true).x * (fun _ : Unit ↦ 0)
              (obs true).x * g (obs true).x)) / 2 := by
        simp [obs, ind]
      _ = ∫ o, (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x * (fun _ : Unit ↦ 0) o.x * g o.x
            ∂marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel :=
        (hIntegral _ (((measurable_const.mul measurable_const).mul
          (hg.comp hx)).stronglyMeasurable)).symm
  have hVar : MARVariance (fun _ : Unit ↦ (1 / 2 : ℝ))
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) := by
    intro h
    apply integral_congr_ae
    filter_upwards with o
    cases o.r <;> norm_num [ind]
  have hEIFzero :
      marMean_eif (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ (0 : ℝ))
          (marMean_Ψ (fun _ : Unit ↦ (1 / 2 : ℝ))
            (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel))
        =ᵐ[marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel] fun _ ↦ 0 := by
    filter_upwards [hraw_zero] with o ho
    rw [marMean_eif, hψ]
    simp only [mul_zero, sub_zero]
    exact ho
  have hIPWzero :
      marMean_ipwRep (fun _ : Unit ↦ (1 / 2 : ℝ))
          (marMean_Ψ (fun _ : Unit ↦ (1 / 2 : ℝ))
            (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel))
        =ᵐ[marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel] fun _ ↦ 0 := by
    filter_upwards [hraw_zero] with o ho
    rw [marMean_ipwRep, hψ, sub_zero]
    exact ho
  have hLp_eif : MemLp
      (marMean_eif (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ (0 : ℝ))
        (marMean_Ψ (fun _ : Unit ↦ (1 / 2 : ℝ))
          (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel))) 2
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) :=
    (memLp_congr_ae hEIFzero).2 (memLp_const 0)
  have hLp_ipw : MemLp
      (marMean_ipwRep (fun _ : Unit ↦ (1 / 2 : ℝ))
        (marMean_Ψ (fun _ : Unit ↦ (1 / 2 : ℝ))
          (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel))) 2
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) :=
    (memLp_congr_ae hIPWzero).2 (memLp_const 0)
  have hLp_coar : MemLp
      (marMean_coarseningScore (fun _ : Unit ↦ (1 / 2 : ℝ))
        (fun x ↦ (fun _ : Unit ↦ (0 : ℝ)) x -
          marMean_Ψ (fun _ : Unit ↦ (1 / 2 : ℝ))
            (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel))) 2
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) := by
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun o ↦ ?_)).2 (memLp_const 0)
    rw [hψ]
    simp [marMean_coarseningScore]
  have hLp_bm : MemLp
      (marMean_coarseningScore (fun _ : Unit ↦ (1 / 2 : ℝ)) (fun _ ↦ (0 : ℝ))) 2
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) := by
    apply (memLp_congr_ae (Filter.Eventually.of_forall fun o ↦ ?_)).2 (memLp_const 0)
    simp [marMean_coarseningScore]
  have hm_int : Integrable (fun _ : MARObs Unit ↦ (0 : ℝ))
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) := by
    exact integrable_const 0
  have hweight_bdd : ∀ o : MARObs Unit,
      |ind o.r / (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x| ≤ 2 := by
    intro o
    cases o.r <;> norm_num [ind]
  have hweight_int : Integrable
      (fun o : MARObs Unit ↦ ind o.r / (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x)
      (marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel) :=
    (memLp_two_of_bounded hweightMeas ⟨(2 : ℝ), hweight_bdd⟩).integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hraw_bdd : ∀ᵐ o ∂marObsMeasure (Measure.dirac ((), (0 : ℝ))) fairBoolKernel,
      |ind o.r * o.ry / (fun _ : Unit ↦ (1 / 2 : ℝ)) o.x| ≤ 0 := by
    filter_upwards [hraw_zero] with o ho
    rw [ho]
    norm_num
  have hAtoms := fairMAR_atoms_positive
  dsimp only at hAtoms
  have hNonzero := fairMAR_coarseningScore_nonzero
  dsimp only at hNonzero
  exact ⟨fairBoolKernel_isMAR, by intro o; norm_num, hProp, hReg, hVar,
    hLp_eif, hLp_ipw, hLp_coar, hLp_bm, hm_int, hweight_int, hrawMeas, hraw_bdd,
    hAtoms.1, hAtoms.2, hNonzero⟩

/-- **Conditional `L²` MAR-mean EIF criterion for vdV Example 25.43.**

This theorem assumes pathwise differentiability of `marMean_Ψ` and the base
representer identity, rather than imposing the global boundedness used by
`marMean_isEIF`. Its two conclusion-critical hypotheses are:
* `hpd` — `marMean_Ψ` is pathwise differentiable on `T`;
* `hipw_c_IF` — the derivative is represented by the centered IPW representer
  `φ_c = R·Y/π − ψ` (vdV Lem 25.41's representer `1{δ∈C}/R(C|y)·χ_Q`).

The AIPW algebra and orthogonality are derived by the shared
`marMean_eif_isIF` and `marMean_eif_mem_T` theorems. Membership in `T` uses the
supplied orthogonality characterization `hT_char`. -/
theorem marMean_isEIF_of_pathwise (π m : X → ℝ)
    (hπ : ∀ o : MARObs X, π o.x ≠ 0)
    (hProp : MARPropensity π P)
    (hReg : MARRegression π m P)
    (hVar : MARVariance π P)
    (hLp : MemLp (marMean_eif π m (marMean_Ψ π P)) 2 P)
    (hLp_ipw : MemLp (marMean_ipwRep π (marMean_Ψ π P)) 2 P)
    (hLp_coar : MemLp (marMean_coarseningScore π (fun x => m x - marMean_Ψ π P)) 2 P)
    (hLp_bm : MemLp (marMean_coarseningScore π m) 2 P)
    (hm_int : Integrable (fun o => m o.x) P)
    (hInt_weight : Integrable (fun o => ind o.r / π o.x) P)
    (hf : MemLp (fun o : MARObs X => ind o.r * o.ry / π o.x) 2 P)
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (hT_char : ∀ (w : ↥(L2ZeroMean P)), w ∈ T ↔
        ∀ (c : X → ℝ), Integrable (fun o => c o.x) P →
          MemLp (marMean_coarseningScore π c) 2 P →
          ∫ o, ((w : Lp ℝ 2 P) : MARObs X → ℝ) o
                * marMean_coarseningScore π c o ∂P = 0)
    -- vdV Lemma 25.41: `marMean_Ψ` is pathwise differentiable, with derivative
    -- represented by the centered IPW term `φ_c = R·Y/π − ψ`.
    (hpd : PathwiseDifferentiableAt P T (marMean_Ψ π))
    (hipw_c_IF : IsInfluenceFunction P T hpd.derivative
      (centeredCandidate (fun o : MARObs X => ind o.r * o.ry / π o.x) hf).toL2ZeroMean) :
    IsEfficientInfluenceFunction P T hpd.derivative
      (marMean_eifCandidate π m hπ hProp hLp hLp_ipw hLp_coar hm_int hInt_weight).toL2ZeroMean := by
  set φ_c := (centeredCandidate (fun o : MARObs X => ind o.r * o.ry / π o.x) hf).toL2ZeroMean
    with hφ_c_def
  have hφ_c_ae : ((φ_c : Lp ℝ 2 P) : MARObs X → ℝ)
      =ᵐ[P] fun o => ind o.r * o.ry / π o.x - marMean_Ψ π P :=
    CandidateIF.coeFn_toL2ZeroMean _
  exact ⟨marMean_eif_isIF π m hπ hProp hLp hLp_ipw hLp_coar hLp_bm hm_int hInt_weight T hT_char
      hpd.derivative φ_c hφ_c_ae hipw_c_IF,
    marMean_eif_mem_T π m hπ hProp hReg hVar hLp hLp_ipw hLp_coar hm_int hInt_weight
      T hT_char hLp_bm⟩

end AsymptoticStatistics.Examples.MARMean
