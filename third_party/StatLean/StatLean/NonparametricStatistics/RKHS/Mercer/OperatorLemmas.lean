module
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

/-!
# Norm-attaining vectors of positive operators are eigenvectors

Two Hilbert-space lemmas feeding the constructive proof of Mercer's theorem:

* if `‖A h‖ = ‖A‖` for a unit vector `h`, then `A` maps the orthogonal complement of `h`
  into the orthogonal complement of `A h` (a first-derivative argument on
  `t ↦ ‖A(cos t · h + sin t · k)‖²`);
* consequently, a unit vector at which a *positive* operator attains its norm is an
  eigenvector with eigenvalue `‖P‖`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 11, §11.3, Lemmas 11.13–11.14 (norm-attaining vectors of positive operators are
eigenvectors).

**Proof formalization notes.** The book differentiates $t \mapsto \|A(\cos t\, h + \sin t\,
k)\|^2$ at a maximum; here the derivative is avoided entirely: for all real $s$, $\|A(h + s k)\|^2
\le \|A\|^2\|h + s k\|^2$ expands to $2 s\, \mathrm{re}\langle Ah, Ak\rangle \le s^2 D$, and
choosing $s = \pm\varepsilon/(D+1)$ kills the real part; a unimodular twist of $k$ kills the
imaginary part. Lemma 11.14 then follows the book's decomposition $Ph = c h + k$ with the
degenerate case handled via the tilt $h - Ph$.

**Bibliographic comments.** Classical operator theory; see F. Riesz and B. Sz.-Nagy,
*Functional Analysis* (1955), §93 (norm-attaining vectors of symmetric operators).
-/

open scoped InnerProductSpace ComplexOrder

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Auxiliary: the *real part* of `⟪A h, A k⟫` vanishes for `k ⊥ h`, obtained from the
inequality `‖A (h + s • k)‖² ≤ ‖A‖² ‖h + s • k‖²` for real `s` (the linear-in-`s` term of
a quadratic dominated by a quadratic with matching constant term must vanish). -/
private theorem re_inner_map_eq_zero_of_norm_attaining (A : E →L[𝕜] E) {h : E}
    (hh : ‖h‖ = 1) (hA : ‖A h‖ = ‖A‖) {k : E} (hk : ⟪h, k⟫_𝕜 = 0) :
    RCLike.re ⟪A h, A k⟫_𝕜 = 0 := by
  set r := RCLike.re ⟪A h, A k⟫_𝕜 with hrdef
  set D := ‖A‖ ^ 2 * ‖k‖ ^ 2 - ‖A k‖ ^ 2 with hDdef
  have hD : 0 ≤ D := by
    have h1 : ‖A k‖ ≤ ‖A‖ * ‖k‖ := A.le_opNorm k
    nlinarith [norm_nonneg (A k), norm_nonneg k, norm_nonneg A]
  have key : ∀ s : ℝ, 2 * s * r ≤ s ^ 2 * D := by
    intro s
    have e1 : ‖h + (s : 𝕜) • k‖ ^ 2 = 1 + s ^ 2 * ‖k‖ ^ 2 := by
      rw [norm_add_sq (𝕜 := 𝕜), inner_smul_right, hk, mul_zero, map_zero, norm_smul, hh]
      simp [mul_pow, sq_abs]
    have e2 : ‖A (h + (s : 𝕜) • k)‖ ^ 2 = ‖A‖ ^ 2 + 2 * s * r + s ^ 2 * ‖A k‖ ^ 2 := by
      rw [map_add, map_smul, norm_add_sq (𝕜 := 𝕜), inner_smul_right, norm_smul, hA]
      simp [mul_pow, sq_abs]
      ring
    have h3 : ‖A (h + (s : 𝕜) • k)‖ ≤ ‖A‖ * ‖h + (s : 𝕜) • k‖ := A.le_opNorm _
    have h4 : ‖A (h + (s : 𝕜) • k)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖h + (s : 𝕜) • k‖ ^ 2 := by
      nlinarith [norm_nonneg (A (h + (s : 𝕜) • k)), norm_nonneg (h + (s : 𝕜) • k),
        norm_nonneg A]
    rw [e1, e2] at h4
    nlinarith [h4]
  have hup : ∀ ε : ℝ, 0 < ε → 2 * r ≤ 0 + ε := by
    intro ε hε
    have ht : 0 < ε / (D + 1) := div_pos hε (by linarith)
    have hkey := key (ε / (D + 1))
    have hmul : (ε / (D + 1)) * (D + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hkey, ht, hmul, hD, hε]
  have hdown : ∀ ε : ℝ, 0 < ε → -(2 * r) ≤ 0 + ε := by
    intro ε hε
    have ht : 0 < ε / (D + 1) := div_pos hε (by linarith)
    have hkey := key (-(ε / (D + 1)))
    have hmul : (ε / (D + 1)) * (D + 1) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hkey, ht, hmul, hD, hε]
  have h1 : 2 * r ≤ 0 := le_of_forall_pos_le_add hup
  have h2 : -(2 * r) ≤ 0 := le_of_forall_pos_le_add hdown
  linarith

/-- If a bounded operator attains its norm at the unit vector `h`, then vectors
orthogonal to `h` are mapped to vectors orthogonal to `A h`. -/
theorem inner_map_eq_zero_of_norm_attaining (A : E →L[𝕜] E) {h : E}
    -- USER-INPUT: unit vector attaining the operator norm
    (hh : ‖h‖ = 1) (hA : ‖A h‖ = ‖A‖)
    {k : E} (hk : ⟪h, k⟫_𝕜 = 0) :
    ⟪A h, A k⟫_𝕜 = 0 := by
  set w := ⟪A h, A k⟫_𝕜 with hw
  have hk' : ⟪h, (starRingEnd 𝕜) w • k⟫_𝕜 = 0 := by rw [inner_smul_right, hk, mul_zero]
  have h1 := re_inner_map_eq_zero_of_norm_attaining A hh hA hk'
  rw [map_smul, inner_smul_right, ← hw, RCLike.conj_mul, ← RCLike.ofReal_pow,
    RCLike.ofReal_re] at h1
  have hwz : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
  exact norm_eq_zero.mp hwz

/-- **Norm-attaining vectors of positive operators are eigenvectors**: if a positive
operator `P` attains its norm at the unit vector `h`, then `P h = ‖P‖ • h`. -/
theorem isEigenvector_of_norm_attaining {P : E →L[𝕜] E}
    -- USER-INPUT: positivity of the operator
    (hP : P.IsPositive) {h : E}
    -- USER-INPUT: unit vector attaining the operator norm
    (hh : ‖h‖ = 1) (hn : ‖P h‖ = ‖P‖) :
    P h = ((‖P‖ : ℝ) : 𝕜) • h := by
  have hhh : ⟪h, h⟫_𝕜 = 1 := by rw [inner_self_eq_norm_sq_to_K, hh]; norm_num
  set c := ⟪h, P h⟫_𝕜 with hc
  set k := P h - c • h with hkdef
  have hk : ⟪h, k⟫_𝕜 = 0 := by
    rw [hkdef, inner_sub_right, inner_smul_right, hhh, mul_one, ← hc, sub_self]
  have hkh : ⟪k, h⟫_𝕜 = 0 := by rw [← inner_conj_symm, hk, map_zero]
  have h0 : ⟪P h, P k⟫_𝕜 = 0 := inner_map_eq_zero_of_norm_attaining P hh hn hk
  have h0' : ⟪P k, P h⟫_𝕜 = 0 := by rw [← inner_conj_symm, h0, map_zero]
  have hPkh : ⟪P k, h⟫_𝕜 = ⟪k, k⟫_𝕜 := by
    rw [hP.inner_left_eq_inner_right k h]
    have hsplit : P h = k + c • h := by rw [hkdef]; abel
    rw [hsplit, inner_add_right, inner_smul_right, hkh, mul_zero, add_zero]
  have hPkk : ⟪P k, k⟫_𝕜 = -c * ⟪k, k⟫_𝕜 := by
    rw [hkdef, inner_sub_right, inner_smul_right]
    rw [show ⟪P (P h - c • h), P h⟫_𝕜 = 0 from h0', hPkh, hkdef]
    ring
  have hcnn : (0 : 𝕜) ≤ c := hP.inner_nonneg_right h
  have hrec : 0 ≤ RCLike.re c := (RCLike.nonneg_iff.mp hcnn).1
  have hkk : ⟪k, k⟫_𝕜 = ((‖k‖ ^ 2 : ℝ) : 𝕜) := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
  have hre : 0 ≤ RCLike.re ⟪P k, k⟫_𝕜 := hP.re_inner_nonneg_left k
  rw [hPkk, hkk] at hre
  have hre2 : RCLike.re c * ‖k‖ ^ 2 ≤ 0 := by
    have hrw : RCLike.re (-c * ((‖k‖ ^ 2 : ℝ) : 𝕜)) = -(RCLike.re c) * ‖k‖ ^ 2 := by
      simp [RCLike.mul_re]
    rw [hrw] at hre; linarith
  have hzero : RCLike.re c * ‖k‖ ^ 2 = 0 := le_antisymm hre2 (mul_nonneg hrec (sq_nonneg _))
  rcases mul_eq_zero.mp hzero with hc0 | hkn
  · -- `re c = 0`: then `c = 0`, and the tilt `h - P h` forces `P h = 0`.
    have hcz : c = 0 := by
      have him : RCLike.im c = 0 := (RCLike.nonneg_iff.mp hcnn).2
      exact RCLike.ext (by simpa using hc0) (by simpa using him)
    have hkPh : k = P h := by rw [hkdef, hcz, zero_smul, sub_zero]
    have hPP : RCLike.re ⟪P (P h), P h⟫_𝕜 = 0 := by
      have hz := hPkk
      rw [hcz, hkPh] at hz
      rw [hz]; simp
    have hkey := hP.re_inner_nonneg_left (h - P h)
    have hexp : ⟪P (h - P h), h - P h⟫_𝕜
        = ⟪P h, h⟫_𝕜 - ⟪P h, P h⟫_𝕜 - ⟪P (P h), h⟫_𝕜 + ⟪P (P h), P h⟫_𝕜 := by
      rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]; ring
    have hPPh : ⟪P (P h), h⟫_𝕜 = ⟪P h, P h⟫_𝕜 := hP.inner_left_eq_inner_right _ _
    have hPhh : RCLike.re ⟪P h, h⟫_𝕜 = 0 := by
      have hconj : ⟪P h, h⟫_𝕜 = (starRingEnd 𝕜) c := by rw [hc, inner_conj_symm]
      rw [hconj, hcz]; simp
    rw [hexp, hPPh] at hkey
    simp only [map_add, map_sub] at hkey
    rw [hPhh, hPP] at hkey
    have hnorm : ⟪P h, P h⟫_𝕜 = ((‖P h‖ ^ 2 : ℝ) : 𝕜) := by
      rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
    rw [hnorm] at hkey
    simp only [RCLike.ofReal_re] at hkey
    have hPh0 : ‖P h‖ = 0 := by nlinarith [norm_nonneg (P h)]
    have hPz : P h = 0 := norm_eq_zero.mp hPh0
    rw [hPz, ← hn, hPh0]
    simp
  · -- `k = 0`: then `P h = c • h` with `c ≥ 0` real and `‖c‖ = ‖P‖`.
    have hk0 : k = 0 := by
      have hkn0 : ‖k‖ = 0 := by nlinarith [norm_nonneg k]
      exact norm_eq_zero.mp hkn0
    have hPhc : P h = c • h := by
      have hz := hkdef ▸ hk0
      rw [sub_eq_zero] at hz
      exact hz
    have hnc : ‖c‖ = ‖P‖ := by
      rw [← hn, hPhc, norm_smul, hh, mul_one]
    rw [hPhc, ← hnc, RCLike.norm_of_nonneg' hcnn]

end StatLean.NonparametricStatistics
