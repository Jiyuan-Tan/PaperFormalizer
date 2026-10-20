module
public import StatLean.AsymptoticStatistics.Core.Pathwise
public import StatLean.AsymptoticStatistics.Core.CandidateIF

@[expose] public section

/-!
# The reusable efficient-influence-function (EIF) theorem package

Fix a probability measure $P$ and a tangent space $T$, realized as a linear
subspace of the mean-zero square-integrable functions $L^2_0(P)$. For a smooth
parameter $\psi$ with pathwise derivative $\dot\psi : T \to \mathbb{R}$, an
*influence function* is an element $\tilde\psi$ of $L^2_0(P)$ representing the
derivative through the inner product, $\langle \tilde\psi, g\rangle = \dot\psi(g)$
for every $g \in T$. The *efficient influence function* is the influence
function that additionally lies in the tangent space $T$. This package collects
the pure-Hilbert facts about it:

* **Existence/sufficiency.** An influence function that lies in $T$ is the
  efficient influence function.
* **Projection characterization.** The orthogonal projection onto $T$ of any
  influence function is the efficient influence function; equivalently, the
  efficient influence function is the projection of any influence function onto
  the closed linear span of the tangent set.
* **Efficiency bound.** Among all influence functions for the same derivative,
  the efficient influence function $\tilde\psi$ has minimal $L^2(P)$ norm:
  $\|\tilde\psi\| \le \|\tilde\psi'\|$ for every influence function $\tilde\psi'$.
  Dually, $\sup_{g \in T} \langle \tilde\psi, g\rangle^2 / \|g\|^2 = \|\tilde\psi\|^2$
  (lem:25.19, operational form), with the degenerate term $0/0$ read as $0$.

All theorems take the pathwise derivative $\dot\psi : T \to \mathbb{R}$ directly
as a (continuous linear) parameter; they do not mention parametric paths or
curves. The two convenience wrappers at the end (`eif_of_influence_tangent_eq_top`,
`influence_on_sup_of_subtract_proj_nuisance`) and the verification entry points
(`candidate_isEIF_of_full_tangent`, `candidate_isEIF_of_membership`) package the
full-tangent and nuisance-correction regimes used in concrete model examples.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information):
definition of the efficient influence function as the projection of any
influence function onto the closed linear span of the tangent set, and
Lemma 25.19 (the squared-norm/supremum efficiency bound). The full lower-bound
interpretation — that $\|\tilde\psi\|^2$ is the asymptotic-variance lower bound
for *any* regular estimator — relies on the Le Cam / LAM machinery of
Theorems 25.20–25.21 and is recorded separately in
`semiparametric_convolution_theorem`.

**Proof formalization notes.** All four core results are elementary Hilbert-space
geometry over $L^2_0(P)$:
* `eif_of_representation_and_membership` is immediate from the definition.
* `eif_eq_orthogonalProjection` uses that the residual $\tilde\psi -
  \Pi_T\tilde\psi$ lies in $T^\perp$, so $\langle \Pi_T\tilde\psi, g\rangle =
  \langle \tilde\psi, g\rangle = \dot\psi(g)$ for $g \in T$. The
  `[T.HasOrthogonalProjection]` hypothesis is a standard side-condition,
  automatic when $T$ is closed in a complete inner-product space.
* `efficient_bound_eq_sqNorm` is Pythagoras: the cross term $\langle \tilde\psi,
  \tilde\psi' - \tilde\psi\rangle$ vanishes because both functions represent
  $\dot\psi$ on $T$ and $\tilde\psi \in T$, giving $\|\tilde\psi'\|^2 =
  \|\tilde\psi\|^2 + \|\tilde\psi' - \tilde\psi\|^2 \ge \|\tilde\psi\|^2$.
* `efficient_bound_eq_sup_ratio` is Cauchy–Schwarz for the upper bound on each
  ratio term, with equality attained at $g = \tilde\psi$ (available via the EIF
  membership clause). This is the dual face of `efficient_bound_eq_sqNorm`; the
  two together exhaust the operational content of lem:25.19. The book's
  $\sup$ over $\overline{\operatorname{lin}}(\text{tangent set})$ matches our
  submodule $T$ when $T$ is closed.

**Bibliographic comments.** The characterization of the efficient influence
function as the orthogonal projection of any influence function onto the tangent
space, and the resulting asymptotic-variance lower bound equal to its squared
$L^2$ norm, originate in the semiparametric-efficiency literature rather than
with a single source. The seminal references are J. M. Begun, W. J. Hall,
W.-M. Huang, and J. A. Wellner, "Information and Asymptotic Efficiency in
Parametric–Nonparametric Models", *The Annals of Statistics* 11(2), 432–452
(1983), which established the representation/minimax lower bounds via
Hellinger-differentiable root-densities and the effective (orthogonalized)
score; and the monograph P. J. Bickel, C. A. J. Klaassen, Y. Ritov, and J. A.
Wellner, *Efficient and Adaptive Estimation for Semiparametric Models*, Johns
Hopkins University Press (1993; reprinted Springer, 1998), which gives the
projection-onto-tangent-space formulation in full generality. The underlying
lower bound is the semiparametric form of the Hájek convolution theorem (J.
Hájek, "A characterization of limiting distributions of regular estimates",
*Z. Wahrscheinlichkeitstheorie verw. Gebiete* 14, 323–330 (1970)). van der Vaart
§25.3 is an exposition of this body of work.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.EIF

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {T : Submodule ℝ ↥(L2ZeroMean P)}

/-- *Sufficient conditions for EIF.* If `IF` represents the derivative
`dψ : T →L[ℝ] ℝ` on `T` (i.e. is an influence function) and `IF` lies in
`T`, then `IF` is the efficient influence function for `dψ`.

Reference: vdV §25.3, definition of efficient influence function (immediate
consequence of the definition).

Edge behavior: when `T = ⊥`, only `IF = 0` is an influence function
(vacuously) and lies in `T`, recovering `dψ = 0`. -/
theorem eif_of_representation_and_membership
    {dψ : T →L[ℝ] ℝ} {IF : ↥(L2ZeroMean P)}
    (hRep : IsInfluenceFunction P T dψ IF) (hMem : IF ∈ T) :
    IsEfficientInfluenceFunction P T dψ IF :=
  ⟨hRep, hMem⟩

/-- *Projection of any influence function to the EIF.* For any influence
function `IF` of `dψ : T →L[ℝ] ℝ` (not necessarily in `T`), the orthogonal
projection of `IF` onto `T` is an efficient influence function for `dψ`.

Reference: vdV §25.3, immediately after the definition of efficient
influence function.

The `[T.HasOrthogonalProjection]` hypothesis is a standard side-condition
for orthogonal projection in a Hilbert space, automatic when `T` is closed
in a complete inner-product space.

Proof: the projected element lies in `T` by `starProjection_apply_mem`. For
the inner-product condition: for any `g : T`, the residual
`IF - T.starProjection IF ∈ Tᗮ`, so `⟪IF - T.starProjection IF, g⟫ = 0`.
By linearity of inner product, `⟪T.starProjection IF, g⟫ = ⟪IF, g⟫ = dψ g`. -/
theorem eif_eq_orthogonalProjection
    [T.HasOrthogonalProjection]
    {dψ : T →L[ℝ] ℝ} {IF : ↥(L2ZeroMean P)}
    (hIF : IsInfluenceFunction P T dψ IF) :
    IsEfficientInfluenceFunction P T dψ (T.starProjection IF) := by
  refine ⟨?_, T.starProjection_apply_mem IF⟩
  intro g
  have h_orth : ⟪IF - T.starProjection IF, (g : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
    have h_mem_perp : IF - T.starProjection IF ∈ Tᗮ :=
      T.sub_starProjection_mem_orthogonal IF
    -- `g ∈ T` gives `⟪g, y⟫ = 0` for any `y ∈ Tᗮ`; swap to get the form we need.
    have hgy :
        ⟪(g : ↥(L2ZeroMean P)), IF - T.starProjection IF⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal _ _).mp h_mem_perp (g : ↥(L2ZeroMean P)) g.2
    rw [real_inner_comm] at hgy
    exact hgy
  have h_split :
      ⟪T.starProjection IF, (g : ↥(L2ZeroMean P))⟫_ℝ
        = ⟪IF, (g : ↥(L2ZeroMean P))⟫_ℝ
          - ⟪IF - T.starProjection IF, (g : ↥(L2ZeroMean P))⟫_ℝ := by
    rw [inner_sub_left]; ring
  rw [h_split, h_orth, sub_zero]
  exact hIF g

/-- *Operational efficiency bound.* Among all influence functions `IF` for a
fixed pathwise derivative `dψ : T →L[ℝ] ℝ`, the EIF `IF_eff` has minimal
`L²(P)` norm. Equivalently, `‖IF_eff‖² ≤ ‖IF‖²` for any other influence
function `IF`.

Reference: vdV lem:25.19 (operational form). The full lower-bound
interpretation — that `‖IF_eff‖²` is the asymptotic-variance lower bound for
*any* regular estimator — depends on Le Cam / LAM machinery (vdV thm:25.20,
thm:25.21).

Proof (Pythagoras): `IF = IF_eff + (IF - IF_eff)`. The cross term vanishes:
  - For any `g ∈ T`, both `hEIF.1 g` and `hIF g` give
    `⟪IF_eff, g⟫ = ⟪IF, g⟫ = dψ g`, so `⟪IF - IF_eff, g⟫ = 0`.
  - In particular `g := ⟨IF_eff, hEIF.2⟩ ∈ T`, giving
    `⟪IF - IF_eff, IF_eff⟫ = 0`, hence `⟪IF_eff, IF - IF_eff⟫ = 0`.
Then `‖IF‖² = ‖IF_eff‖² + ‖IF - IF_eff‖² ≥ ‖IF_eff‖²`, and the conclusion
follows by taking square roots. -/
theorem efficient_bound_eq_sqNorm
    {dψ : T →L[ℝ] ℝ} {IF_eff IF : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P T dψ IF_eff)
    (hIF : IsInfluenceFunction P T dψ IF) :
    ‖IF_eff‖ ≤ ‖IF‖ := by
  -- Cross-term vanishing: ⟪IF_eff, IF - IF_eff⟫ = 0.
  have h_cross : ⟪IF_eff, IF - IF_eff⟫_ℝ = 0 := by
    have h_diff_g :
        ∀ g : T,
          ⟪IF - IF_eff, (g : ↥(L2ZeroMean P))⟫_ℝ = 0 := by
      intro g
      have h1 := hIF g          -- ⟪IF, g⟫ = dψ g
      have h2 := hEIF.1 g       -- ⟪IF_eff, g⟫ = dψ g
      rw [inner_sub_left, h1, h2, sub_self]
    have h_g_in_T : (⟨IF_eff, hEIF.2⟩ : T) = ⟨IF_eff, hEIF.2⟩ := rfl
    have h_diff_eff : ⟪IF - IF_eff, IF_eff⟫_ℝ = 0 := by
      have := h_diff_g ⟨IF_eff, hEIF.2⟩
      simpa using this
    -- Swap to get ⟪IF_eff, IF - IF_eff⟫ = 0.
    rw [real_inner_comm] at h_diff_eff
    exact h_diff_eff
  -- Pythagoras: ‖IF‖² = ‖IF_eff + (IF - IF_eff)‖² = ‖IF_eff‖² + ‖IF - IF_eff‖².
  have h_pythagoras : ‖IF‖^2 = ‖IF_eff‖^2 + ‖IF - IF_eff‖^2 := by
    have h_eq := @norm_add_sq_real _ _ _ IF_eff (IF - IF_eff)
    rw [h_cross, mul_zero, add_zero] at h_eq
    -- h_eq : ‖IF_eff + (IF - IF_eff)‖² = ‖IF_eff‖² + ‖IF - IF_eff‖²
    have h_sum : IF_eff + (IF - IF_eff) = IF := by abel
    rw [h_sum] at h_eq
    exact h_eq
  -- ‖IF_eff‖² ≤ ‖IF‖² (since the residual term is non-negative).
  have h_sq_le : ‖IF_eff‖^2 ≤ ‖IF‖^2 := by
    rw [h_pythagoras]; nlinarith [sq_nonneg ‖IF - IF_eff‖]
  -- Take square roots (both norms non-negative).
  have h_sqrt := Real.sqrt_le_sqrt h_sq_le
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt

/-- *Book form of the operational efficiency bound (vdV lem:25.19).* The
supremum of the squared inner-product ratio `⟪ψ̃, g⟫² / ‖g‖²` over the
tangent space `T` equals `‖ψ̃‖²`.

Reference: vdV lem:25.19:

> sup over `g ∈ closure(lin tangent set)` of `⟨ψ̃, g⟩² / ⟨g, g⟩ = P ψ̃²`.

Our `T : Submodule ℝ ↥(L2ZeroMean P)` is already a submodule (linear span)
of `L²₀(P)`; if `T` is closed, it equals `closure(lin(tangent set))` and
this matches the book statement.

Convention for the `g = 0` term: the ratio is `0 / 0 = 0` in real division,
which does not affect the supremum.

Proof: Cauchy–Schwarz gives the upper bound `⟪ψ̃, g⟫² ≤ ‖ψ̃‖² · ‖g‖²` on
each term. Equality is attained at `g = ψ̃`, which lies in `T` by the EIF
membership clause of `IsEfficientInfluenceFunction`.

This is the *dual face* of `efficient_bound_eq_sqNorm` (norm-minimality
among IFs); the two together exhaust the operational content of lem:25.19.
The full lower-bound interpretation — that `‖ψ̃‖²` is the asymptotic-variance
lower bound for *every* regular estimator — is clause (a) of
`semiparametric_convolution_theorem`. -/
theorem efficient_bound_eq_sup_ratio
    {dψ : T →L[ℝ] ℝ} {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P T dψ IF_eff) :
    ⨆ g : T, (⟪IF_eff, (g : ↥(L2ZeroMean P))⟫_ℝ) ^ 2
        / ‖(g : ↥(L2ZeroMean P))‖ ^ 2 = ‖IF_eff‖ ^ 2 := by
  -- Cauchy–Schwarz: every term ≤ ‖IF_eff‖².
  have h_bound : ∀ g : T,
      (⟪IF_eff, (g : ↥(L2ZeroMean P))⟫_ℝ) ^ 2
        / ‖(g : ↥(L2ZeroMean P))‖ ^ 2 ≤ ‖IF_eff‖ ^ 2 := by
    intro g
    set x : ↥(L2ZeroMean P) := (g : ↥(L2ZeroMean P)) with hx_def
    by_cases hx : ‖x‖ = 0
    · have hx2 : ‖x‖ ^ 2 = 0 := by rw [hx]; ring
      rw [hx2, div_zero]; positivity
    · have h_pos : 0 < ‖x‖ ^ 2 := by
        have h_nn : 0 ≤ ‖x‖ := norm_nonneg x
        have h_pos1 : 0 < ‖x‖ := lt_of_le_of_ne h_nn (Ne.symm hx)
        positivity
      rw [div_le_iff₀ h_pos]
      -- Cauchy–Schwarz: |⟪IF_eff, x⟫| ≤ ‖IF_eff‖ * ‖x‖.
      have h_cs : (⟪IF_eff, x⟫_ℝ) ^ 2 ≤ ‖IF_eff‖ ^ 2 * ‖x‖ ^ 2 := by
        have h_abs := abs_real_inner_le_norm IF_eff x
        have h_nn : 0 ≤ |⟪IF_eff, x⟫_ℝ| := abs_nonneg _
        have h_pow : |⟪IF_eff, x⟫_ℝ| ^ 2 ≤ (‖IF_eff‖ * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ h_nn h_abs 2
        rw [sq_abs, mul_pow] at h_pow
        exact h_pow
      linarith
  -- Achieved at g = IF_eff (using EIF membership).
  have hMem : IF_eff ∈ T := hEIF.2
  set g_eff : T := ⟨IF_eff, hMem⟩ with hg_eff_def
  have h_eq :
      (⟪IF_eff, (g_eff : ↥(L2ZeroMean P))⟫_ℝ) ^ 2
        / ‖(g_eff : ↥(L2ZeroMean P))‖ ^ 2 = ‖IF_eff‖ ^ 2 := by
    have h_coe : (g_eff : ↥(L2ZeroMean P)) = IF_eff := rfl
    rw [h_coe]
    rw [real_inner_self_eq_norm_mul_norm]
    by_cases h0 : ‖IF_eff‖ = 0
    · simp [h0]
    · have h_pos_sq : 0 < ‖IF_eff‖ ^ 2 := by
        have h_nn : 0 ≤ ‖IF_eff‖ := norm_nonneg _
        have h_pos : 0 < ‖IF_eff‖ := lt_of_le_of_ne h_nn (Ne.symm h0)
        positivity
      field_simp
  apply le_antisymm
  · exact ciSup_le h_bound
  · have h_bdd : BddAbove (Set.range (fun g : T =>
        (⟪IF_eff, (g : ↥(L2ZeroMean P))⟫_ℝ) ^ 2
          / ‖(g : ↥(L2ZeroMean P))‖ ^ 2)) :=
      ⟨‖IF_eff‖ ^ 2, by rintro _ ⟨g, rfl⟩; exact h_bound g⟩
    rw [← h_eq]
    exact le_ciSup h_bdd g_eff

/-! ## Convenience wrappers for concrete-model EIF proofs

The two theorems below are model-agnostic shortcuts that recur in
example proofs. They sit on top of `eif_of_representation_and_membership`
and the orthogonal-projection geometry, and are added to keep concrete
example files short.

References:
- vdV thm:25.40 (full-tangent regime, e.g. unrestricted MAR/CAR) — the
  full-tangent shortcut.
- vdV cor:25.42 (subtract nuisance projection) — the abstract correction.
-/

/-- *Full-tangent shortcut.* If the tangent space is the
whole `L²₀(P)`, then any influence function is automatically the
efficient influence function — the "EIF in T" requirement reduces to
`IF ∈ ⊤`, which is trivial.

Reference: vdV thm:25.40 specialises this for unrestricted CAR / MAR
models, where the tangent space is shown to equal all of L²₀(P). The
wrapper itself is purely abstract.

Proof: invoke `eif_of_representation_and_membership` with the
membership discharged by `Submodule.mem_top` after rewriting via `hT`. -/
theorem eif_of_influence_tangent_eq_top
    {dψ : T →L[ℝ] ℝ} {IF : ↥(L2ZeroMean P)}
    (hT : T = ⊤)
    (hIF : IsInfluenceFunction P T dψ IF) :
    IsEfficientInfluenceFunction P T dψ IF :=
  eif_of_representation_and_membership hIF (by rw [hT]; exact Submodule.mem_top)

/-- *Orthogonal nuisance-correction.* Suppose the tangent
space splits as `T_main ⊔ T_nuis` with `T_main ⊥ T_nuis`. If `φ₀`
represents the derivative `dψ` on `T_main` and `dψ` vanishes on
`T_nuis`, then subtracting the projection of `φ₀` onto `T_nuis` yields
an influence function on the whole sum.

This handles the *derivation* use case — when the EIF is unknown and must be
constructed from a known IF on a sub-tangent plus the missingness-
score projection (vdV cor:25.42 / ex:25.43). When the candidate IF is
*supplied* and only needs to be **verified** as the EIF, prefer
`candidate_isEIF_of_full_tangent` (full-tangent regime) or
`candidate_isEIF_of_membership` (strict-tangent regime) below — those
require only the pathwise-derivative identity, no projection algebra.

Abstract Hilbert content of vdV cor:25.42 (subtract the missingness-score
projection). Concrete CAR/MAR examples instantiate it with `T_main`
the full-data tangent space and `T_nuis` the missingness-score space.

The `[T_nuis.HasOrthogonalProjection]` hypothesis is a side-condition:
`[CompleteSpace ↥(L2ZeroMean P)]` does not always auto-synthesize on
Submodule-coerced types, so we take the projection instance explicitly.

Proof outline. Take any `g : T_main ⊔ T_nuis`. By `Submodule.mem_sup`,
`g.val = u + v` with `u ∈ T_main` and `v ∈ T_nuis`. Then:
- `⟪proj_nuis φ₀, u⟫ = 0` since `proj_nuis φ₀ ∈ T_nuis ⊥ T_main`.
- `⟪φ₀ - proj_nuis φ₀, v⟫ = 0` since the residual lies in `T_nuisᗮ`.
- `⟪φ₀ - proj_nuis φ₀, u⟫ = ⟪φ₀, u⟫ = dψ ⟨u, mem_sup_left⟩` by `hMain`.
- `dψ ⟨v, mem_sup_right⟩ = 0` by `hZero`.
Combining via inner-product additivity and `dψ.map_add` closes the goal. -/
theorem influence_on_sup_of_subtract_proj_nuisance
    {T_main T_nuis : Submodule ℝ ↥(L2ZeroMean P)}
    [T_nuis.HasOrthogonalProjection]
    {dψ : (T_main ⊔ T_nuis : Submodule ℝ ↥(L2ZeroMean P)) →L[ℝ] ℝ}
    {φ₀ : ↥(L2ZeroMean P)}
    (hOrth : ∀ u ∈ T_main, ∀ v ∈ T_nuis, ⟪u, v⟫_ℝ = (0 : ℝ))
    (hMain : ∀ (u : ↥(L2ZeroMean P)) (hu : u ∈ T_main),
        ⟪φ₀, u⟫_ℝ = dψ ⟨u, Submodule.mem_sup_left hu⟩)
    (hZero : ∀ (v : ↥(L2ZeroMean P)) (hv : v ∈ T_nuis),
        dψ ⟨v, Submodule.mem_sup_right hv⟩ = 0) :
    IsInfluenceFunction P (T_main ⊔ T_nuis) dψ
      (φ₀ - T_nuis.starProjection φ₀) := by
  intro g
  obtain ⟨u, hu, v, hv, hsum⟩ := Submodule.mem_sup.mp g.2
  have h_proj_mem : T_nuis.starProjection φ₀ ∈ T_nuis :=
    T_nuis.starProjection_apply_mem φ₀
  have h_resid_perp : φ₀ - T_nuis.starProjection φ₀ ∈ T_nuisᗮ :=
    T_nuis.sub_starProjection_mem_orthogonal φ₀
  -- ⟪φ₀ - proj_nuis φ₀, v⟫ = 0
  have h_inner_resid_v :
      ⟪φ₀ - T_nuis.starProjection φ₀, v⟫_ℝ = 0 := by
    have hv_perp :
        ⟪v, φ₀ - T_nuis.starProjection φ₀⟫_ℝ = 0 :=
      (Submodule.mem_orthogonal _ _).mp h_resid_perp v hv
    rw [real_inner_comm] at hv_perp
    exact hv_perp
  -- ⟪proj_nuis φ₀, u⟫ = 0
  have h_inner_proj_u :
      ⟪T_nuis.starProjection φ₀, u⟫_ℝ = 0 := by
    have huv := hOrth u hu (T_nuis.starProjection φ₀) h_proj_mem
    rw [real_inner_comm] at huv
    exact huv
  -- ⟪φ₀ - proj_nuis φ₀, u⟫ = ⟪φ₀, u⟫
  have h_inner_resid_u :
      ⟪φ₀ - T_nuis.starProjection φ₀, u⟫_ℝ = ⟪φ₀, u⟫_ℝ := by
    rw [inner_sub_left, h_inner_proj_u, sub_zero]
  -- LHS rewritten as ⟪φ₀, u⟫
  have hLHS :
      ⟪φ₀ - T_nuis.starProjection φ₀,
          (g : ↥(L2ZeroMean P))⟫_ℝ = ⟪φ₀, u⟫_ℝ := by
    have hg_val : (g : ↥(L2ZeroMean P)) = u + v := hsum.symm
    rw [hg_val, inner_add_right, h_inner_resid_u, h_inner_resid_v, add_zero]
  -- RHS: dψ g = dψ ⟨u, _⟩ + dψ ⟨v, _⟩
  have hg_eq :
      g = ⟨u, Submodule.mem_sup_left hu⟩
            + (⟨v, Submodule.mem_sup_right hv⟩
                : (T_main ⊔ T_nuis : Submodule ℝ ↥(L2ZeroMean P))) := by
    apply Subtype.ext
    change (g : ↥(L2ZeroMean P)) = u + v
    exact hsum.symm
  have hRHS :
      dψ g = dψ ⟨u, Submodule.mem_sup_left hu⟩
              + dψ ⟨v, Submodule.mem_sup_right hv⟩ := by
    rw [hg_eq, ContinuousLinearMap.map_add]
  rw [hLHS, hRHS, hZero v hv, add_zero, hMain u hu]

/-! ## Verification entry points for candidate-given EIF proofs

When the candidate raw influence function is **supplied** (the
"verification" use case, contrasted with the "derivation" use case
of `influence_on_sup_of_subtract_proj_nuisance` above), the proof
obligation collapses to: tangent characterization, the pathwise-derivative
identity, membership, and conclusion. The two theorems below are the
standardized entry points for the two common regimes.
-/

/-- *Verification: full-tangent regime.* When the tangent space equals
all of `L²₀(P)` (e.g. nonparametric, unrestricted CAR/MAR, saturated
working models), a `CandidateIF` is the EIF as soon as it satisfies
the pathwise-derivative identity. No projection algebra; no
membership obligation; no nuisance scores. -/
theorem candidate_isEIF_of_full_tangent
    {T : Submodule ℝ ↥(L2ZeroMean P)} (hT : T = ⊤)
    {dψ : T →L[ℝ] ℝ} {φ : AsymptoticStatistics.Core.CandidateIF P}
    (hPath : ∀ g : T,
        ⟪φ.toL2ZeroMean, (g : ↥(L2ZeroMean P))⟫_ℝ = dψ g) :
    IsEfficientInfluenceFunction P T dψ φ.toL2ZeroMean :=
  eif_of_influence_tangent_eq_top hT hPath

/-- *Verification: strict-tangent regime.* When the tangent space is
a proper subspace of `L²₀(P)`, a `CandidateIF` is the EIF iff it
satisfies the pathwise-derivative identity *and* lies in the tangent
space. The user supplies both directly (the second is often a one-line
construction from the candidate's spanning representation). No
projection algebra needed. -/
theorem candidate_isEIF_of_membership
    {T : Submodule ℝ ↥(L2ZeroMean P)}
    {dψ : T →L[ℝ] ℝ} {φ : AsymptoticStatistics.Core.CandidateIF P}
    (hPath : ∀ g : T,
        ⟪φ.toL2ZeroMean, (g : ↥(L2ZeroMean P))⟫_ℝ = dψ g)
    (hMem : φ.toL2ZeroMean ∈ T) :
    IsEfficientInfluenceFunction P T dψ φ.toL2ZeroMean :=
  eif_of_representation_and_membership hPath hMem

end AsymptoticStatistics.Core.EIF
