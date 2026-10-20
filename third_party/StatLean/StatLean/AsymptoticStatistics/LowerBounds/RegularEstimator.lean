module
public import StatLean.AsymptoticStatistics.Core.Pathwise
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.Dirac

@[expose] public section

/-!
# Hájek-style regular-estimator predicate (semiparametric)

This file defines the thin user-facing predicate `IsRegularEstimator` and
its basic consumers.

Let $P$ be the true distribution and $\psi : \mathcal{P} \to \mathbb{R}$ a
functional that is pathwise differentiable at $P$ relative to a tangent set
$\dot{\mathcal{P}}_P$. A sequence of scalar estimators $T_n = T_n(X_1,\dots,X_n)$
is called *regular* at $P$ for estimating $\psi(P)$ (relative to
$\dot{\mathcal{P}}_P$) if there exists a probability measure $L$ such that, for
every score direction $g$ in the tangent set realised by a one-dimensional
submodel $t \mapsto P_{t,g}$ with score $g$,
$$
\sqrt{n}\,\bigl(T_n - \psi(P_{1/\sqrt{n},\,g})\bigr) \;\rightsquigarrow\; L
\qquad\text{under } P_{1/\sqrt{n},\,g},\quad\text{for every } g \in \dot{\mathcal{P}}_P,
$$
i.e. the rescaled estimator, computed under the local-perturbation law and
*recentered at the perturbed truth* $\psi(P_{1/\sqrt{n},\,g})$, converges weakly
to the **same** limit law $L$, independently of the direction $g$. This is the
shift-invariance form of the regularity requirement: the limit $L$ does not
depend on $g$.

In the Lean formalization the one-dimensional submodel is supplied as a
`QMDPath P` (differentiability in quadratic mean) whose score equals $g$, and
the local perturbation $P_{1/\sqrt{n},\,g}$ is the curve evaluated at
$(\sqrt{n})^{-1}$. Compared with the book statement, the Lean predicate carries
two extra parameters that have no proof obligation: the pathwise-differentiability
witness `hψ` and the efficient-influence-function witness `_hEIF`. They are
included only so that the derived Hájek-shift form
(`IsRegularEstimator.hajek_shift_form`) can be stated within the same predicate's
data; they impose nothing on the definition itself.

Headline declarations:

* `IsRegularEstimator` — the predicate itself.
* `IsRegularEstimator.shift` — direct unfolding for a chosen direction.
* `IsRegularEstimator.weak_limit_at_zero` — specialisation at `g = 0`.
* `IsRegularEstimator.hajek_shift_form` — the derived Hájek-shift form,
  recentering at the unperturbed truth `ψ(P)` and picking up the
  deterministic Slutsky shift `(dirac ⟪IF_eff, g⟫) ∗ L`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998,
Chapter 25 (Semiparametric Models), §25.3 (Tangent Spaces and Information),
definition of a *regular* estimator sequence (p. 365, the displayed equation
immediately preceding Theorem 25.20). The associated convolution theorem is
vdV Theorem 25.20; the local asymptotic minimax theorem is vdV Theorem 25.21.

**Proof formalization notes.** The canonical definition recenters at the
*perturbed* truth $\psi(P_{1/\sqrt{n},\,g})$, exactly as in vdV, so that the
limit law $L$ is the same for every direction $g$ and the predicate's structural
content is immediately visible.

The **Hájek-shift form** (`IsRegularEstimator.hajek_shift_form`) is a *theorem*
derived from this definition, not an alternative definition: recentering at the
unperturbed truth $\psi(P)$ yields weak convergence of
$\sqrt{n}\,(T_n - \psi(P))$ to $(\delta_{\langle \tilde\psi_P, g\rangle}) \ast L$,
the limit law $L$ shifted by the deterministic Slutsky shift
$\langle \mathrm{IF}_{\mathrm{eff}}, g\rangle$. The two forms are mathematically
equivalent under pathwise differentiability of $\psi$. The derivation proceeds by:

* taking the perturbed-truth convergence to $L$ from the regularity hypothesis;
* identifying $\sqrt{n}\,(\psi(P_{1/\sqrt{n},g}) - \psi(P)) \to
  \langle \mathrm{IF}_{\mathrm{eff}}, g\rangle$ via pathwise differentiability of
  $\psi$ (the difference quotient $(\psi(P_t) - \psi(P))/t$ along the curve,
  evaluated as $t = (\sqrt{n})^{-1} \to 0$);
* continuous mapping of the deterministic shift on the weak limit; and
* absorbing the vanishing deterministic gap via Slutsky
  (`WeakConverges.slutsky_of_tendstoInMeasure_dist`), the pointwise distance
  between the two recenterings being the deterministic, vanishing
  $|\langle \mathrm{IF}_{\mathrm{eff}}, g\rangle - a_n|$.

This Hájek-shift form is what Le Cam-bridge arguments need: a single fixed
recentering at $\psi(P)$, independent of the local perturbation direction $g$.

**Bibliographic comments.** The notion of a *regular* estimator and the
accompanying convolution theorem (vdV Theorem 25.20) originate with
J. Hájek, "A characterization of limiting distributions of regular estimates,"
*Zeitschrift für Wahrscheinlichkeitstheorie und verwandte Gebiete* **14** (1970),
323–330; the same characterization was obtained independently by
T. Inagaki, "On the limiting distribution of a sequence of estimators with
uniformity property," *Annals of the Institute of Statistical Mathematics* **22**
(1970), 1–13. The companion local asymptotic minimax theorem (vdV Theorem 25.21)
is due to J. Hájek, "Local asymptotic minimax and admissibility in estimation,"
*Proc. Sixth Berkeley Symp. Math. Statist. Probab.*, vol. 1 (1972), 175–194,
building on L. Le Cam's asymptotic decision theory. The semiparametric phrasing
formalized here — regularity *relative to a tangent set* $\dot{\mathcal{P}}_P$
with limit-law $L$ independent of the score direction — follows van der Vaart's
synthesis in Chapter 25.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds.RegularEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- *Hájek-style regular-estimator predicate (vdV §25.3.2 canonical form).*

A sequence of scalar estimators `T_n : (Fin n → Ω) → ℝ` is regular at
`P` relative to the tangent set `T_set`, with limit law `L`, if for
every score direction `g` in `tangentSpace T_set` realised by some
`QMDPath P` with `curve.score = g`, the rescaled estimator computed
under the local-perturbation curve `curve.curve ((√n)⁻¹)` and
**recentered at the perturbed truth** `ψ(curve.curve ((√n)⁻¹))`
converges weakly to the **same** limit law `L`, regardless of the
direction `g`:

```
√n · (T_n − ψ(curve.curve ((√n)⁻¹)))  ⇀  L .
```

This is the classical vdV §25.3.2 "shift-invariance" form: under the
local perturbation `curve.curve ((√n)⁻¹)`, the recentered (at the
perturbed truth) statistic has the *same* limit law `L` as it would
under the unperturbed `P` — the limit `L` does not depend on the
direction `g`.

Reference: vdV §25.3.2 (the paragraph preceding the convolution
theorem 25.20), in the recentering-at-perturbed-truth convention.

Note. The Hájek-shift form (recenter at unperturbed `ψ(P)`, pick up the
deterministic Slutsky shift `(dirac ⟪IF_eff, g⟫_ℝ) ∗ L`) is a
**theorem** derived from this definition via Slutsky and the pathwise
differentiability of `ψ`; see `IsRegularEstimator.hajek_shift_form`. The
two forms are mathematically equivalent under pathwise
differentiability, but the canonical definition uses recentering at the
perturbed truth so that the limit `L` is the same for every direction
`g`, making the predicate's structural content immediately visible.

The arguments `hψ` and `_hEIF` carry no proof obligation here; they are
included in the signature so the shift form derived in
`hajek_shift_form` can be stated within the same predicate's data.

Edge behavior: when `g = 0` and `tangentSpace T_set` contains `0`
(always true — it is a submodule), the QMDPath with `score = 0`
specialises the conclusion to weak convergence of the perturbed-truth-
recentered statistic to `L` (see `IsRegularEstimator.weak_limit_at_zero`). -/
def IsRegularEstimator
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T_set : TangentSpec P)
    (ψ : Measure Ω → ℝ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L] : Prop :=
  ∀ (g : ↥(L2ZeroMean P))
    (_hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (curve : QMDPath P)
    (_hscore : curve.score = g),
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))))
      L

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {T_set : TangentSpec P}
variable {ψ : Measure Ω → ℝ}
variable {IF_eff : ↥(L2ZeroMean P)}
variable {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
variable {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
                  hψ.derivative IF_eff}
variable {T_n : ∀ n, (Fin n → Ω) → ℝ}
variable {L : Measure ℝ}

/-- *Direct unfolding of `IsRegularEstimator`.*

Direct destructuring of `IsRegularEstimator` for a chosen score
direction `g` realised by a `QMDPath`. The conclusion is the canonical
vdV §25.3.2 form (recenter at the perturbed truth, limit law `L`).

For the Hájek-shift form (recenter at `ψ(P)`, pick up the deterministic
shift `(dirac ⟪IF_eff, g⟫) ∗ L`), see
`IsRegularEstimator.hajek_shift_form`.

Reference: vdV §25.3.2 (direct unfolding of the definition). -/
theorem IsRegularEstimator.shift [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    (g : ↥(L2ZeroMean P))
    (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (curve : QMDPath P) (hscore : curve.score = g) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))))
      L :=
  hReg g hg curve hscore

/-- *At-zero specialization.*

When the regularity predicate is instantiated at the zero score
direction `g = 0` (necessarily an element of every tangent space, since
it is a submodule), provided some `QMDPath` realises that score and
exists-as-a-witness, the conclusion is plain weak convergence to `L`.

In the canonical (perturbed-truth-recentered) definition this is just a
direct specialisation of `IsRegularEstimator` at `g = 0`; the conclusion
is `L` regardless of the direction.

NOTE: this lemma states the weak limit *along the curve at the
parameter* `(√n)⁻¹` — *not* along the constant family `P`, because the
curve at `(√n)⁻¹` is in general not equal to `P` even though
`zero_curve.curve 0 = P`. The collapse of the *probability law* (RHS)
is nonetheless to `L`. -/
theorem IsRegularEstimator.weak_limit_at_zero [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    (zero_curve : QMDPath P) (h_zero : zero_curve.score = 0)
    (h_zero_in : (0 : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => zero_curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n *
              (T_n n X - ψ (zero_curve.curve ((Real.sqrt n)⁻¹)))))
      L :=
  hReg 0 h_zero_in zero_curve h_zero

/-- **Hájek-shift form of the regular-estimator hypothesis.**

If the estimator is regular in the canonical vdV §25.3.2 sense
(recenter at the perturbed truth `ψ(curve.curve ((√n)⁻¹))`, limit `L`),
and the functional `ψ` is pathwise differentiable at `P` along the
tangent space, then the rescaled estimator computed under the same
perturbation curve but **recentered at the unperturbed truth** `ψ P`
converges weakly to `(dirac ⟪IF_eff, g⟫) ∗ L`:

```
√n · (T_n − ψ P)  ⇀  (dirac ⟪IF_eff, g⟫_ℝ) ∗ L .
```

This is the Hájek-shift form needed for Le Cam-bridge arguments where
a single fixed recentering at `ψ(P)` (independent of the local
perturbation direction `g`) is required.

Proof strategy. Apply Slutsky in the deterministic-shift form:

* From `hReg`: `√n · (T_n − ψ(curve.curve ((√n)⁻¹)))` weakly converges
  to `L` under `(curve.curve ((√n)⁻¹))^n`.
* From pathwise differentiability of `ψ`:
  `a_n := √n · (ψ(curve.curve ((√n)⁻¹)) − ψ P)
        = (ψ(curve.curve ((√n)⁻¹)) − ψ P) / (√n)⁻¹
        → hψ.derivative ⟨g, hg⟩ = ⟪IF_eff, g⟫_ℝ`.
* Continuous mapping of the deterministic shift `· + ⟪IF_eff, g⟫_ℝ`
  on the `hReg` weak limit gives weak convergence of the shifted
  statistic to `(dirac ⟪IF_eff, g⟫_ℝ) ∗ L`.
* The pointwise distance between the constant-shifted statistic and
  the target `√n · (T_n − ψ P)` is `|a_n − ⟪IF_eff, g⟫_ℝ|`, which is
  deterministic and tends to `0` as `n → ∞`.
* Apply `WeakConverges.slutsky_of_tendstoInMeasure_dist` to absorb
  the vanishing deterministic shift.

Reference: vdV §25.3.2 (the equivalence of the perturbed-truth and
unperturbed-truth recentering conventions, modulo the Slutsky shift
identified by pathwise differentiability of `ψ`). -/
theorem IsRegularEstimator.hajek_shift_form [IsProbabilityMeasure L]
    (hReg : IsRegularEstimator P T_set ψ hψ hEIF T_n L)
    (hT_meas : ∀ n, Measurable (T_n n))
    (g : ↥(L2ZeroMean P))
    (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (curve : QMDPath P) (hscore : curve.score = g) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P)))
      ((MeasureTheory.Measure.dirac
          (⟪(IF_eff : ↥(L2ZeroMean P)), g⟫_ℝ)) ∗ L) := by
  classical
  -- The regularity hypothesis quantifies `g` over the algebraic span; lift to the
  -- closure to invoke `hEIF` / `hψ` (which live over `tangentSpace T_set`).
  have hg_cl : (g : ↥(L2ZeroMean P)) ∈ tangentSpace T_set :=
    span_carrier_le_tangentSpace _ hg
  -- Notation.
  set c : ℝ := ⟪(IF_eff : ↥(L2ZeroMean P)), g⟫_ℝ with hc_def
  -- Per-`n` base measure on the (varying) sample space `Fin n → Ω`.
  set Pn : ∀ n : ℕ, Measure (Fin n → Ω) :=
    fun n => MeasureTheory.Measure.pi
      (fun _ : Fin n => curve.curve ((Real.sqrt n)⁻¹)) with hPn_def
  haveI hPn_prob : ∀ n, IsProbabilityMeasure (Pn n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (curve.curve ((Real.sqrt n)⁻¹)) :=
      fun _ => curve.curve_isProbability _
    rw [hPn_def]
    infer_instance
  -- Inner / outer recentering functionals.
  set Xinner : ∀ n : ℕ, (Fin n → Ω) → ℝ :=
    fun n X => Real.sqrt n * (T_n n X - ψ (curve.curve ((Real.sqrt n)⁻¹)))
    with hXinner_def
  set Yfun : ∀ n : ℕ, (Fin n → Ω) → ℝ :=
    fun n X => Real.sqrt n * (T_n n X - ψ P) with hYfun_def
  -- Shifted version of `Xinner` by the limiting deterministic shift `c`.
  set Xshift : ∀ n : ℕ, (Fin n → Ω) → ℝ :=
    fun n X => Xinner n X + c with hXshift_def
  -- Deterministic shift sequence.
  set a : ℕ → ℝ :=
    fun n => Real.sqrt n * (ψ (curve.curve ((Real.sqrt n)⁻¹)) - ψ P) with ha_def
  -- Step 1: identify `c` with the pathwise derivative at `g`.
  have hc_eq_deriv : c = hψ.derivative ⟨(g : ↥(L2ZeroMean P)), hg_cl⟩ := by
    have h_IF : ⟪(IF_eff : ↥(L2ZeroMean P)),
        ((⟨(g : ↥(L2ZeroMean P)), hg_cl⟩ : tangentSpace T_set) :
          ↥(L2ZeroMean P))⟫_ℝ
            = hψ.derivative ⟨(g : ↥(L2ZeroMean P)), hg_cl⟩ :=
      hEIF.1 ⟨(g : ↥(L2ZeroMean P)), hg_cl⟩
    simpa [hc_def] using h_IF
  -- Step 2: `(√n)⁻¹` tends to `0` along the punctured neighbourhood `𝓝[≠] 0`.
  have h_inv_to_zero : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp <|
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_inv_ne_zero : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < Real.sqrt n := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hn1)
    exact inv_ne_zero hpos.ne'
  have h_inv_punctured :
      Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h_inv_to_zero, h_inv_ne_zero.mono fun n hn => hn⟩
  -- Step 3: `a n → c` by pathwise differentiability of `ψ` along `curve`.
  have h_qmdscore_in : (curve.score : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := by
    rw [hscore]; exact hg_cl
  have h_diff_quotient :
      Tendsto (fun t : ℝ => (ψ (curve.curve t) - ψ P) / t)
        (nhdsWithin 0 {0}ᶜ)
        (𝓝 (hψ.derivative ⟨(curve.score : ↥(L2ZeroMean P)), h_qmdscore_in⟩)) :=
    hψ.derivative_spec curve h_qmdscore_in
  have h_a_to_c : Tendsto a atTop (𝓝 c) := by
    -- Replace the derivative target by `c`: re-anchor along `g = curve.score`.
    have h_target_eq :
        hψ.derivative ⟨(curve.score : ↥(L2ZeroMean P)), h_qmdscore_in⟩ = c := by
      have h_arg_eq :
          (⟨(curve.score : ↥(L2ZeroMean P)), h_qmdscore_in⟩ :
              tangentSpace T_set)
            = ⟨(g : ↥(L2ZeroMean P)), hg_cl⟩ := by
        apply Subtype.ext
        simpa using hscore
      rw [h_arg_eq, ← hc_eq_deriv]
    rw [← h_target_eq]
    -- Compose: `a n = (ψ(curve.curve ((√n)⁻¹)) - ψ P) / (√n)⁻¹`.
    have h_a_form : a = fun n : ℕ =>
        (ψ (curve.curve ((Real.sqrt n)⁻¹)) - ψ P) / (Real.sqrt n)⁻¹ := by
      funext n
      by_cases hn : Real.sqrt n = 0
      · simp [ha_def, hn]
      · have h_inv_ne : (Real.sqrt n)⁻¹ ≠ 0 := inv_ne_zero hn
        rw [ha_def]
        field_simp
    rw [h_a_form]
    exact h_diff_quotient.comp h_inv_punctured
  -- Step 4: `Pn n .map Xinner n ⇝ L` (this is `hReg` directly).
  have h_inner_weak :
      WeakConverges (fun n => (Pn n).map (Xinner n)) L := by
    intro f
    have := hReg g hg curve hscore f
    simpa [hPn_def, hXinner_def] using this
  -- Step 5: `Pn n .map Xshift n ⇝ L.map (· + c) = (dirac c) ∗ L`.
  -- Build measurabilities first.
  have hXinner_meas : ∀ n, Measurable (Xinner n) := by
    intro n
    refine Measurable.const_mul ?_ _
    exact (hT_meas n).sub measurable_const
  have hXshift_meas : ∀ n, Measurable (Xshift n) := fun n =>
    (hXinner_meas n).add_const c
  have hY_meas : ∀ n, Measurable (Yfun n) := by
    intro n
    refine Measurable.const_mul ?_ _
    exact (hT_meas n).sub measurable_const
  -- Pushforward identity: `Pn n .map Xshift n = ((Pn n).map (Xinner n)).map (· + c)`.
  have h_push_eq : ∀ n,
      (Pn n).map (Xshift n) = ((Pn n).map (Xinner n)).map (fun y : ℝ => y + c) := by
    intro n
    rw [Measure.map_map (by fun_prop) (hXinner_meas n)]
    rfl
  -- Continuous mapping of the deterministic shift on the `hReg` weak limit.
  have h_shift_weak :
      WeakConverges (fun n => (Pn n).map (Xshift n)) (L.map (fun y : ℝ => y + c)) := by
    have h_map :
        WeakConverges (fun n => ((Pn n).map (Xinner n)).map (fun y : ℝ => y + c))
          (L.map (fun y : ℝ => y + c)) :=
      h_inner_weak.map (continuous_id.add continuous_const)
        (measurable_id.add_const c)
    intro f
    have := h_map f
    simpa [h_push_eq] using this
  -- `L.map (· + c) = (dirac c) ∗ L`. By `dirac_conv`,
  -- `(dirac c) ∗ L = L.map (fun y ↦ c + y)`; then `c + y = y + c` by `add_comm`.
  have h_target_eq : (MeasureTheory.Measure.dirac c) ∗ L
      = L.map (fun y : ℝ => y + c) := by
    rw [MeasureTheory.Measure.dirac_conv]
    congr 1
    funext y; exact add_comm c y
  -- Step 6: apply Slutsky to absorb the vanishing deterministic shift.
  haveI : IsProbabilityMeasure (L.map (fun y : ℝ => y + c)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map (by fun_prop)
  have h_distance_to_zero :
      ∀ ε > 0,
        Tendsto (fun n : ℕ =>
            (Pn n).real {ω : Fin n → Ω | ε ≤ dist (Xshift n ω) (Yfun n ω)})
          atTop (𝓝 0) := by
    intro ε hε
    -- The pointwise distance is the constant `|c - a n|` (independent of `ω`).
    have h_dist_const : ∀ n (ω : Fin n → Ω),
        dist (Xshift n ω) (Yfun n ω) = |c - a n| := by
      intro n ω
      rw [Real.dist_eq]
      congr 1
      simp only [hXshift_def, hXinner_def, hYfun_def, ha_def]
      ring
    -- The deterministic shift `|c - a n|` tends to `0`.
    have h_close : Tendsto (fun n => |c - a n|) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n => c - a n) atTop (𝓝 (c - c)) :=
        tendsto_const_nhds.sub h_a_to_c
      rw [sub_self] at h0
      have h1 : Tendsto (fun n => |c - a n|) atTop (𝓝 |0|) :=
        (continuous_abs.tendsto _).comp h0
      simpa using h1
    -- Eventually `|c - a n| < ε`, in which case the set is empty.
    have hev : ∀ᶠ n : ℕ in atTop, |c - a n| < ε := by
      have := (Metric.tendsto_nhds.mp h_close) ε hε
      filter_upwards [this] with n hn
      rwa [Real.dist_eq, sub_zero, abs_abs] at hn
    have h_eventually_empty :
        ∀ᶠ n : ℕ in atTop,
          {ω : Fin n → Ω | ε ≤ dist (Xshift n ω) (Yfun n ω)} = (∅ : Set _) := by
      filter_upwards [hev] with n hn
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [h_dist_const]
      exact hn
    -- A set being empty makes its real-valued measure `0`.
    have h_real_zero :
        ∀ᶠ n : ℕ in atTop,
          (Pn n).real {ω : Fin n → Ω | ε ≤ dist (Xshift n ω) (Yfun n ω)} = 0 := by
      filter_upwards [h_eventually_empty] with n hn
      rw [hn]; simp
    exact (tendsto_congr' h_real_zero).mpr tendsto_const_nhds
  have h_slutsky :
      WeakConverges (fun n => (Pn n).map (Yfun n)) (L.map (fun y : ℝ => y + c)) :=
    AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
      (X := Xshift) (Y := Yfun)
      (hX_meas := fun n => (hXshift_meas n).aemeasurable)
      (hY_meas := fun n => (hY_meas n).aemeasurable)
      (hX := h_shift_weak)
      (hDist := h_distance_to_zero)
  -- Repackage into the convolution form.
  intro f
  have := h_slutsky f
  simpa [hPn_def, hYfun_def, h_target_eq] using this

end AsymptoticStatistics.LowerBounds.RegularEstimator
