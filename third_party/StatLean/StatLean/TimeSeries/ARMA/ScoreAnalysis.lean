module
public import StatLean.TimeSeries.ARMA.Likelihood
public import StatLean.TimeSeries.ForMathlib.Probability.MartingaleCLT.Defs
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

@[expose] public section

/-!
# Score analysis for ARMA maximum likelihood (FY §3.3.2, eq. (3.14); Hannan program)

The analytic layer of the commissioned Hannan Theorem 3.2 proof (time-domain route,
`notes/time_series/roadmap.md`): residual inversion, the auxiliary AR processes, the
information matrix, and the martingale-difference property of the quasi-score.

* `armaPi` — the **AR(∞) inversion coefficients** `π(z) = b(z)/a(z)` (invertibility
  makes them geometrically decaying: `summable_abs_armaPi`);
* `maCrossACVF` — cross-covariances of two MA(∞) filters driven by a common unit
  white noise;
* `hannanVarZ` — **FY eq. (3.14)**: the covariance matrix of
  `Z_t = (U_{t−1}, …, U_{t−p}, V_{t−1}, …, V_{t−q})`, where `U` is the AR(p) process
  `b(B)U = ε` and `V` the AR(q) process `a(B)V = ε` driven by a **common** `WN(0,1)`;
  the asymptotic covariance of the MLE is `W = (hannanVarZ)⁻¹`;
* `hannanVarZ_posDef` — positive-definiteness **under coprimality** of the AR and MA
  polynomials (the ARMA(1,1) degeneracy at `a + b = 0` noted by FY shows coprimality
  is genuinely needed; FY's `(b₀, a₀) ∈ 𝓑` implicitly assumes minimal orders);
* `armaResidual` — the θ-residual process `ε_t(θ) = Σ_j π_j(θ) X_{t−j}` as an `L²`
  limit, recovering the innovations at the true parameter
  (`armaResidual_eq_noise`);
* the **score-as-MDS** structure: at the true parameter the derivative array of the
  residual sum of squares is a stationary martingale-difference sequence against the
  noise filtration (`armaScore_condexp_zero`) with conditional variance proportional
  to `hannanVarZ` in the limit — the inputs Brown's CLT needs
  (`ARMA/MLEAsymptotics.lean` assembles).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.3.2,
eq. (3.14) and Theorem 3.2 remarks (pp. 96–99); proof route from E. J. Hannan, *The
asymptotic theory of linear time-series models*, J. Appl. Probab. **10** (1973),
130–145, as streamlined in Brockwell & Davis (1991) §10.8. (`FY §3.3.2 / Hannan 1973`.)

**Bibliographic comments.** The auxiliary-AR representation of the ARMA information
matrix is due to Whittle (1953) and Walker (1962); Hannan (1973) gave the ergodic
proof; the martingale-difference score route is Hall–Heyde (1980) §6.2 and Yao &
Brockwell (2001, personal-communication route cited by FY).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- The **AR(∞) inversion coefficients** `π_n = [zⁿ] b(z)/a(z)` (FY §3.3.1's
invertibility expansion; junk-total via the formal power-series inverse, well-defined
since `a(0) = 1`). -/
noncomputable def armaPi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n
    (((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
      (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)

section PiCoeff

/-- Negating the coefficients turns the MA polynomial into the AR polynomial (the two
differ only by FY's sign convention). -/
private lemma maPoly_neg {p : ℕ} (b : Fin p → ℝ) :
    maPoly (fun i => -b i) = arPoly b := by
  simp only [maPoly, arPoly, map_neg, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- ... and symmetrically: the AR polynomial of the negated MA coefficients is the MA
polynomial. -/
private lemma arPoly_neg {q : ℕ} (a : Fin q → ℝ) :
    arPoly (fun j => -a j) = maPoly a := by
  simp only [maPoly, arPoly, map_neg, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]

/-- **The inversion coefficients are the transfer coefficients with the roles of the two
lag polynomials swapped**: `π(z) = b(z)/a(z) = ψ(z)` for the parameters `(−a, −b)`. -/
private lemma armaPi_eq_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    armaPi b a n = armaPsi (fun j => -a j) (fun i => -b i) n := by
  rw [armaPi, armaPsi, maPoly_neg, arPoly_neg]

/-- Invertibility of `a` is root-freeness of the AR polynomial of `−a`. -/
private lemma noRootClosedDisc_neg {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) : NoRootClosedDisc (fun j => -a j) := by
  intro z hz
  rw [arPoly_neg]
  exact hB.2 z hz

end PiCoeff

/-- Geometric decay of the inversion coefficients on the constraint set. -/
theorem summable_abs_armaPi {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Summable fun n : ℕ => |armaPi b a n| := by
  simpa only [armaPi_eq_armaPsi] using
    summable_abs_armaPsi (fun i => -b i) (noRootClosedDisc_neg hB)

/-- **Cross-ACVF of two one-sided filters over a common unit white noise**:
`E[(Σᵢ ψᵢ ε_{s−i})(Σⱼ φⱼ ε_{t−j})]` at lag `k = t − s` is `Σⱼ ψⱼ φ_{j+k}` (terms with
negative index vanish). -/
noncomputable def maCrossACVF (ψ φ : ℕ → ℝ) (k : ℤ) : ℝ :=
  ∑' j : ℕ, ψ j * (if h : 0 ≤ (j : ℤ) + k then φ ((j : ℤ) + k).toNat else 0)

/-- **FY eq. (3.14)**: the covariance matrix of the auxiliary vector
`Z = (U_{t−1..t−p}, V_{t−1..t−q})`, `b(B)U = ε`, `a(B)V = ε`, common `WN(0,1)`.
Block entries through `armaPsi`/`maCrossACVF`: `ψᵇ = armaPsi b elim0` are the
coefficients of `1/b`, `ψᵃ = armaPsi (fun j => −a j) elim0` those of `1/a`. -/
noncomputable def hannanVarZ {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.of fun s t =>
    match s, t with
    | .inl i, .inl i' =>
        maCrossACVF (armaPsi b (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi b (Fin.elim0 : Fin 0 → ℝ)) ((i' : ℤ) - (i : ℤ))
    | .inl i, .inr j =>
        maCrossACVF (armaPsi b (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ)) ((j : ℤ) - (i : ℤ))
    | .inr j, .inl i =>
        maCrossACVF (armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi b (Fin.elim0 : Fin 0 → ℝ)) ((i : ℤ) - (j : ℤ))
    | .inr j, .inr j' =>
        maCrossACVF (armaPsi (fun j'' => -a j'') (Fin.elim0 : Fin 0 → ℝ))
          (armaPsi (fun j'' => -a j'') (Fin.elim0 : Fin 0 → ℝ)) ((j' : ℤ) - (j : ℤ))

/-! ### Positive-definiteness of `hannanVarZ`

`hannanVarZ b a` is the **Gram matrix** of the family of `ℓ²` sequences

  `g_i(n) = ψᵇ_{n − (p+q−i)}`  (`i < p`),   `h_j(n) = ψᵃ_{n − (p+q−j)}`  (`j < q`),

where `ψᵇ` are the coefficients of `1/b` and `ψᵃ` those of `1/a`; the *common* shift
base `p + q` is what makes the cross-block lags come out as `j − i`. So the quadratic
form is `Σ_n (Σ_i cᵢ g_i(n) + Σ_j dⱼ h_j(n))²` — nonnegative for free — and definiteness
is the statement that no nontrivial combination of the two filter families vanishes.

In generating-function form a vanishing combination reads `C(z)/b(z) + D(z)/a(z) = 0`
with `C(z) = Σ_i cᵢ z^{p+q−i}` and `D(z) = Σ_j dⱼ z^{p+q−j}`, i.e. `C·a + D·b = 0`.
Coprimality gives `b ∣ C`; since `b(0) = 1`, `b` is also coprime to `z`, so `b` divides
the *reduced* factor `C₀(z) = Σ_i cᵢ z^{p−1−i}` of degree `< p`. Under `hbdeg`
(`deg b = p`, FY's minimal-orders convention) that forces `C₀ = 0`, hence `c = 0`, and
then `D·b = 0` gives `d = 0`. Without `hbdeg` the argument breaks exactly at the degree
count, and the counterexample recorded at `hannanVarZ_posDef` is available. -/

private lemma hannanCoeffArPolyZero {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  simp [arPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

private lemma hannanCoeffMaPolyZero {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

private lemma hannanArPolyNeZero {p : ℕ} (b : Fin p → ℝ) : arPoly b ≠ 0 := by
  intro h
  have h1 := hannanCoeffArPolyZero b
  rw [h] at h1
  simp at h1

private lemma hannanMaPolyElim0 : maPoly (Fin.elim0 : Fin 0 → ℝ) = 1 := by simp [maPoly]

/-! ## Step 1: shifted sequences and the cross-ACVF -/

/-- Right shift of a coefficient sequence by `d` (zero on the first `d` slots). -/
def hannanShiftSeq (ψ : ℕ → ℝ) (d n : ℕ) : ℝ := if d ≤ n then ψ (n - d) else 0

lemma hannanShiftSeq_of_lt {ψ : ℕ → ℝ} {d n : ℕ} (h : n < d) :
    hannanShiftSeq ψ d n = 0 := by
  simp [hannanShiftSeq, Nat.not_le.2 h]

lemma hannanShiftSeq_add (ψ : ℕ → ℝ) (d j : ℕ) : hannanShiftSeq ψ d (j + d) = ψ j := by
  simp [hannanShiftSeq]

private lemma coeff_X_pow_mul_eq_hannanShiftSeq (Φ : PowerSeries ℝ) (d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ d * Φ)
      = hannanShiftSeq (fun m => PowerSeries.coeff m Φ) d n := by
  rw [PowerSeries.coeff_X_pow_mul', hannanShiftSeq]

/-- The `ℓ²` inner product of two shifted sequences is the cross-ACVF at the lag
given by the difference of the shifts. -/
lemma tsum_hannanShiftSeq_mul (ψ φ : ℕ → ℝ) (d e : ℕ) :
    ∑' n : ℕ, hannanShiftSeq ψ d n * hannanShiftSeq φ e n
      = maCrossACVF ψ φ ((d : ℤ) - (e : ℤ)) := by
  have hinj : Function.Injective (fun j : ℕ => j + d) := fun u v h => by
    dsimp only at h; omega
  have hsupp : Function.support (fun n : ℕ => hannanShiftSeq ψ d n * hannanShiftSeq φ e n)
      ⊆ Set.range (fun j : ℕ => j + d) := by
    intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    have hd : d ≤ n := by
      by_contra hlt
      exact hn (by rw [hannanShiftSeq_of_lt (Nat.not_le.1 hlt), zero_mul])
    exact ⟨n - d, by dsimp only; omega⟩
  rw [← hinj.tsum_eq hsupp, maCrossACVF]
  refine tsum_congr fun j => ?_
  rw [hannanShiftSeq_add]
  congr 1
  rw [hannanShiftSeq]
  by_cases h : e ≤ j + d
  · rw [if_pos h, dif_pos (by omega)]
    congr 1
    omega
  · rw [if_neg h, dif_neg (by omega)]

/-- Absolute summability is preserved by shifting. -/
lemma summable_abs_hannanShiftSeq {ψ : ℕ → ℝ} (hψ : Summable fun n => |ψ n|) (d : ℕ) :
    Summable fun n => |hannanShiftSeq ψ d n| := by
  have hinj : Function.Injective (fun j : ℕ => j + d) := fun u v h => by
    dsimp only at h; omega
  refine (hinj.summable_iff ?_).1 ?_
  · intro n hn
    have : n < d := by
      by_contra hle
      exact hn ⟨n - d, by dsimp only; omega⟩
    rw [hannanShiftSeq_of_lt this, abs_zero]
  · have hcomp : ((fun n => |hannanShiftSeq ψ d n|) ∘ fun j : ℕ => j + d) = fun j => |ψ j| := by
      funext j; simp only [Function.comp_apply, hannanShiftSeq_add]
    rw [hcomp]
    exact hψ

lemma hannanAbsLeTsumAbs {u : ℕ → ℝ} (hu : Summable fun n => |u n|) (n : ℕ) :
    |u n| ≤ ∑' m, |u m| :=
  hu.le_tsum n fun _ _ => abs_nonneg _

/-- A product of two absolutely summable sequences is summable. -/
lemma hannanSummableMul {u v : ℕ → ℝ} (hu : Summable fun n => |u n|)
    (hv : Summable fun n => |v n|) : Summable fun n => u n * v n := by
  refine Summable.of_norm_bounded (g := fun n => (∑' m, |v m|) * |u n|)
    (hu.mul_left _) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |u n| * |v n| ≤ |u n| * ∑' m, |v m| :=
        mul_le_mul_of_nonneg_left (hannanAbsLeTsumAbs hv n) (abs_nonneg _)
    _ = (∑' m, |v m|) * |u n| := mul_comm _ _

/-! ## Step 2: `hannanVarZ` as a Gram matrix -/

/-- The common shift base: any `K` with `K ≥ p − 1` and `K ≥ q − 1` works; `p + q` is
the convenient uniform choice. -/
def hannanShift (p q : ℕ) : Fin p ⊕ Fin q → ℕ
  | .inl i => p + q - (i : ℕ)
  | .inr j => p + q - (j : ℕ)

/-- The `ℓ²` vector attached to a coordinate: the `1/b`-filter for an AR slot, the
`1/a`-filter for an MA slot. -/
noncomputable def hannanSeq {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    Fin p ⊕ Fin q → ℕ → ℝ
  | .inl _ => armaPsi b (Fin.elim0 : Fin 0 → ℝ)
  | .inr _ => armaPsi (fun j => -a j) (Fin.elim0 : Fin 0 → ℝ)

noncomputable def hannanVec {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (s : Fin p ⊕ Fin q) (n : ℕ) : ℝ :=
  hannanShiftSeq (hannanSeq b a s) (hannanShift p q s) n

lemma hannanVec_apply {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (s : Fin p ⊕ Fin q) (n : ℕ) :
    hannanVec b a s n = hannanShiftSeq (hannanSeq b a s) (hannanShift p q s) n := rfl

lemma hannanVarZ_gram {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (s t : Fin p ⊕ Fin q) :
    hannanVarZ b a s t = ∑' n : ℕ, hannanVec b a s n * hannanVec b a t n := by
  cases s with
  | inl i =>
    cases t with
    | inl i' =>
      have hlag : ((hannanShift p q (Sum.inl i) : ℕ) : ℤ)
          - ((hannanShift p q (Sum.inl i' : Fin p ⊕ Fin q) : ℕ) : ℤ) = (i' : ℤ) - (i : ℤ) := by
        have h1 := i.isLt; have h2 := i'.isLt
        simp only [hannanShift]; omega
      simp only [hannanVec_apply]
      rw [tsum_hannanShiftSeq_mul, hlag]
      rfl
    | inr j =>
      have hlag : ((hannanShift p q (Sum.inl i) : ℕ) : ℤ)
          - ((hannanShift p q (Sum.inr j : Fin p ⊕ Fin q) : ℕ) : ℤ) = (j : ℤ) - (i : ℤ) := by
        have h1 := i.isLt; have h2 := j.isLt
        simp only [hannanShift]; omega
      simp only [hannanVec_apply]
      rw [tsum_hannanShiftSeq_mul, hlag]
      rfl
  | inr j =>
    cases t with
    | inl i =>
      have hlag : ((hannanShift p q (Sum.inr j : Fin p ⊕ Fin q) : ℕ) : ℤ)
          - ((hannanShift p q (Sum.inl i : Fin p ⊕ Fin q) : ℕ) : ℤ) = (i : ℤ) - (j : ℤ) := by
        have h1 := i.isLt; have h2 := j.isLt
        simp only [hannanShift]; omega
      simp only [hannanVec_apply]
      rw [tsum_hannanShiftSeq_mul, hlag]
      rfl
    | inr j' =>
      have hlag : ((hannanShift p q (Sum.inr j : Fin p ⊕ Fin q) : ℕ) : ℤ)
          - ((hannanShift p q (Sum.inr j' : Fin p ⊕ Fin q) : ℕ) : ℤ) = (j' : ℤ) - (j : ℤ) := by
        have h1 := j.isLt; have h2 := j'.isLt
        simp only [hannanShift]; omega
      simp only [hannanVec_apply]
      rw [tsum_hannanShiftSeq_mul, hlag]
      rfl

lemma summable_abs_hannanVec {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (s : Fin p ⊕ Fin q) :
    Summable fun n => |hannanVec b a s n| := by
  cases s with
  | inl i => exact summable_abs_hannanShiftSeq (summable_abs_armaPsi _ hB.1) _
  | inr j => exact summable_abs_hannanShiftSeq (summable_abs_armaPsi _ (noRootClosedDisc_neg hB)) _

lemma summable_abs_hannanCombo {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (x : Fin p ⊕ Fin q → ℝ) :
    Summable fun n => |∑ s, x s * hannanVec b a s n| := by
  refine Summable.of_norm_bounded
    (g := fun n => ∑ s, |x s| * |hannanVec b a s n|) ?_ fun n => ?_
  · exact summable_sum fun s _ => ((summable_abs_hannanVec hB s).mul_left _)
  · rw [Real.norm_eq_abs, abs_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun s _ => abs_mul _ _

/-! ## Step 3: the quadratic form is a sum of squares -/

lemma hannanVarZ_quadForm {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (x : Fin p ⊕ Fin q → ℝ) :
    ∑ s, x s * ∑ t, hannanVarZ b a s t * x t
      = ∑' n : ℕ, (∑ s, x s * hannanVec b a s n) ^ 2 := by
  have hsum : ∀ s t : Fin p ⊕ Fin q,
      Summable fun n => (x s * hannanVec b a s n) * (x t * hannanVec b a t n) := by
    intro s t
    have h0 := hannanSummableMul
      (summable_abs_hannanVec hB s) (summable_abs_hannanVec hB t)
    exact (h0.mul_left (x s * x t)).congr fun n => by ring
  have hstep : ∀ n : ℕ, (∑ s, x s * hannanVec b a s n) ^ 2
      = ∑ s, ∑ t, (x s * hannanVec b a s n) * (x t * hannanVec b a t n) := by
    intro n; rw [sq, Finset.sum_mul_sum]
  rw [tsum_congr hstep,
    Summable.tsum_finsetSum (fun s _ => summable_sum fun t _ => hsum s t)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Summable.tsum_finsetSum (fun t _ => hsum s t), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hfac : (∑' n : ℕ, (x s * hannanVec b a s n) * (x t * hannanVec b a t n))
      = (x s * x t) * ∑' n : ℕ, hannanVec b a s n * hannanVec b a t n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  rw [hfac, hannanVarZ_gram]
  ring

/-! ### The **backward** Gram — the covariance of the score vector (finding 26)

`hannanVarZ` is the Gram matrix of the family with shifts `p + q − i` (`hannanShift`),
which decrease in `i`: it is the covariance matrix of the **forward** auxiliary vector
`(U_{t−(p+q)+i})_{i<p} ⌢ (V_{t−(p+q)+j})_{j<q}`, i.e. of a vector whose two blocks are
*right*-aligned at the common time `t − (p+q)`.

The vector the ARMA score actually contracts against is the **backward** one,
`Z_t = (U_{t−1−i})_{i<p} ⌢ (V_{t−1−j})_{j<q}` (`MLEAsymptotics.scoreSeq`): its shifts
`1 + i` *increase* in `i`, so its two blocks are *left*-aligned at the common time
`t − 1`. Both matrices are Gram matrices of the same two filter families, so their
diagonal blocks agree (an autocovariance is even), but the AR–MA cross-blocks are read at
the **opposite lag**, and a cross-covariance is not even. They therefore differ whenever
`p, q ≥ 1` and `max (p, q) ≥ 2` — the smallest case is ARMA(2,1), and
`hannanVarZ_quadForm_ne_back` below is a two-line witness there.

For `p = q` the two are conjugate by the block-wise reversal permutation, and for
`q = 0` or `p = 0` they are equal; ARMA(1,1) — the case every textbook prints — is the
largest case in which nothing goes wrong, which is presumably why the discrepancy
survived. -/

/-- The **backward** shift base `1 + i`: the shifts of the score vector `Z_t`. -/
def hannanShiftBack (p q : ℕ) : Fin p ⊕ Fin q → ℕ
  | .inl i => 1 + (i : ℕ)
  | .inr j => 1 + (j : ℕ)

/-- The `ℓ²` vector attached to a coordinate of the **score** vector `Z_t`. -/
noncomputable def hannanVecBack {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (s : Fin p ⊕ Fin q) (n : ℕ) : ℝ :=
  hannanShiftSeq (hannanSeq b a s) (hannanShiftBack p q s) n

/-- **The covariance matrix of the ARMA score vector** `Z_t = (U_{t−1−i}, V_{t−1−j})`,
i.e. the true Hannan information matrix. Compare `hannanVarZ`, which is the same Gram
with the *forward* shifts; see the section docstring and finding 26. -/
noncomputable def hannanVarZBack {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℝ :=
  Matrix.of fun s t => maCrossACVF (hannanSeq b a s) (hannanSeq b a t)
    ((hannanShiftBack p q s : ℤ) - (hannanShiftBack p q t : ℤ))

lemma hannanVarZBack_gram {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (s t : Fin p ⊕ Fin q) :
    hannanVarZBack b a s t = ∑' n : ℕ, hannanVecBack b a s n * hannanVecBack b a t n := by
  simp only [hannanVecBack]
  rw [tsum_hannanShiftSeq_mul]
  rfl

lemma summable_abs_hannanVecBack {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (s : Fin p ⊕ Fin q) :
    Summable fun n => |hannanVecBack b a s n| := by
  cases s with
  | inl i => exact summable_abs_hannanShiftSeq (summable_abs_armaPsi _ hB.1) _
  | inr j => exact summable_abs_hannanShiftSeq (summable_abs_armaPsi _ (noRootClosedDisc_neg hB)) _

lemma summable_abs_hannanComboBack {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (x : Fin p ⊕ Fin q → ℝ) :
    Summable fun n => |∑ s, x s * hannanVecBack b a s n| := by
  refine Summable.of_norm_bounded
    (g := fun n => ∑ s, |x s| * |hannanVecBack b a s n|) ?_ fun n => ?_
  · exact summable_sum fun s _ => ((summable_abs_hannanVecBack hB s).mul_left _)
  · rw [Real.norm_eq_abs, abs_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    exact Finset.sum_congr rfl fun s _ => abs_mul _ _

/-- The backward quadratic form is the `ℓ²` norm of the combined filter — the same
computation as `hannanVarZ_quadForm`, with the score's shifts. -/
lemma hannanVarZBack_quadForm {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (x : Fin p ⊕ Fin q → ℝ) :
    ∑ s, x s * ∑ t, hannanVarZBack b a s t * x t
      = ∑' n : ℕ, (∑ s, x s * hannanVecBack b a s n) ^ 2 := by
  have hsum : ∀ s t : Fin p ⊕ Fin q,
      Summable fun n => (x s * hannanVecBack b a s n) * (x t * hannanVecBack b a t n) := by
    intro s t
    have h0 := hannanSummableMul
      (summable_abs_hannanVecBack hB s) (summable_abs_hannanVecBack hB t)
    exact (h0.mul_left (x s * x t)).congr fun n => by ring
  have hstep : ∀ n : ℕ, (∑ s, x s * hannanVecBack b a s n) ^ 2
      = ∑ s, ∑ t, (x s * hannanVecBack b a s n) * (x t * hannanVecBack b a t n) := by
    intro n; rw [sq, Finset.sum_mul_sum]
  rw [tsum_congr hstep,
    Summable.tsum_finsetSum (fun s _ => summable_sum fun t _ => hsum s t)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Summable.tsum_finsetSum (fun t _ => hsum s t), Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hfac : (∑' n : ℕ, (x s * hannanVecBack b a s n) * (x t * hannanVecBack b a t n))
      = (x s * x t) * ∑' n : ℕ, hannanVecBack b a s n * hannanVecBack b a t n := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  rw [hfac, hannanVarZBack_gram]
  ring

/-- The cross-ACVF is symmetric under swapping the filters and negating the lag. -/
lemma maCrossACVF_symm (ψ φ : ℕ → ℝ) (k : ℤ) :
    maCrossACVF ψ φ k = maCrossACVF φ ψ (-k) := by
  have key : ∀ (u v : ℕ → ℝ) (m : ℕ), maCrossACVF u v (m : ℤ) = maCrossACVF v u (-(m : ℤ)) := by
    intro u v m
    have h1 := tsum_hannanShiftSeq_mul u v m 0
    have h2 := tsum_hannanShiftSeq_mul v u 0 m
    have h3 : (∑' n : ℕ, hannanShiftSeq u m n * hannanShiftSeq v 0 n)
        = ∑' n : ℕ, hannanShiftSeq v 0 n * hannanShiftSeq u m n :=
      tsum_congr fun n => mul_comm _ _
    rw [h1, h2] at h3
    simpa using h3
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk with m
    exact key ψ φ m
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    subst hm
    rw [neg_neg]
    exact (key φ ψ m).symm

/-- An autocovariance is even. -/
lemma maCrossACVF_self_neg (ψ : ℕ → ℝ) (k : ℤ) :
    maCrossACVF ψ ψ k = maCrossACVF ψ ψ (-k) := maCrossACVF_symm ψ ψ k

/-- **The damage of finding 26 is confined to genuinely mixed models.** With no MA part
(`q = 0`) the forward and backward Grams coincide: only the AR–AR block survives, and an
autocovariance is even. Hence the two `q = 0` members of the Hannan chain — the sample-PACF
linearization and the LS = YW = MLE equivalence, both since removed from
`ARMA/MLEAsymptotics.lean` — were unaffected by finding 26. -/
theorem hannanVarZ_eq_back_of_pure_ar {p : ℕ} (b : Fin p → ℝ) :
    hannanVarZ b (Fin.elim0 : Fin 0 → ℝ) = hannanVarZBack b (Fin.elim0 : Fin 0 → ℝ) := by
  ext s t
  match s, t with
  | .inl i, .inl i' =>
    simp only [hannanVarZ, hannanVarZBack, hannanSeq, hannanShiftBack, Matrix.of_apply]
    rw [maCrossACVF_self_neg (armaPsi b (Fin.elim0 : Fin 0 → ℝ)) ((i' : ℤ) - (i : ℤ))]
    congr 1
    push_cast
    ring
  | .inl i, .inr j => exact absurd j.isLt (by omega)
  | .inr j, _ => exact absurd j.isLt (by omega)

/-- The mirror statement with no AR part (`p = 0`). -/
theorem hannanVarZ_eq_back_of_pure_ma {q : ℕ} (a : Fin q → ℝ) :
    hannanVarZ (Fin.elim0 : Fin 0 → ℝ) a = hannanVarZBack (Fin.elim0 : Fin 0 → ℝ) a := by
  ext s t
  match s, t with
  | .inr j, .inr j' =>
    simp only [hannanVarZ, hannanVarZBack, hannanSeq, hannanShiftBack, Matrix.of_apply]
    rw [maCrossACVF_self_neg (armaPsi (fun j'' => -a j'') (Fin.elim0 : Fin 0 → ℝ))
      ((j' : ℤ) - (j : ℤ))]
    congr 1
    push_cast
    ring
  | .inr j, .inl i => exact absurd i.isLt (by omega)
  | .inl i, _ => exact absurd i.isLt (by omega)

/-! #### FINDING 26 — the forward and backward Grams genuinely differ (ARMA(2,1))

The witness is the smallest possible: `p = 2`, `q = 1`, `b(z) = 1 − z/2` (padded with a
zero second coefficient, so the *order* is 2), `a(z) = 1` (padded likewise). Then
`ψᵇ_n = 2^{−n}` and `ψᵃ = δ₀`, so the AR–MA cross-correlation is one-sided:
`C(k) = Σ_m ψᵇ_m ψᵃ_{m+k}` is `ψᵇ_{−k}` for `k ≤ 0` and `0` for `k > 0` — as asymmetric
as a cross-correlation can be.

Contracting against `x = (0, 1) ⌢ (1)` picks out exactly the `(inl 1, inr 0)` cross-entry,
at lag `j − i = −1` in `hannanVarZ` (value `ψᵇ_1 = 1/2`) and at lag
`(1+i) − (1+j) = +1` in `hannanVarZBack` (value `0`). Both quadratic forms contain the
same — and, for this statement, uncomputed — diagonal contributions
`maCrossACVF ψᵇ ψᵇ 0` and `maCrossACVF ψᵃ ψᵃ 0`, so the difference of the two forms is
exactly `2 · 1/2 = 1`. -/

/-- Witness AR side: `b(z) = 1 − z/2`, order `2`. -/
noncomputable def findB : Fin 2 → ℝ := ![1/2, 0]

/-- Witness MA side: `a(z) = 1`, order `1`. -/
def findA : Fin 1 → ℝ := ![0]

private lemma findB_arPoly :
    arPoly findB = 1 - Polynomial.C (1/2 : ℝ) * Polynomial.X := by
  simp [arPoly, findB, Fin.sum_univ_two]

private lemma findA_maPoly : maPoly findA = 1 := by
  simp [maPoly, findA]

private lemma findA_neg_arPoly : arPoly (fun j => -findA j) = 1 := by
  simp [arPoly, findA]

/-- `ψᵃ = δ₀`: the MA side of the witness inverts the constant polynomial. -/
private lemma findA_psi (n : ℕ) :
    armaPsi (fun j => -findA j) (Fin.elim0 : Fin 0 → ℝ) n = if n = 0 then 1 else 0 := by
  unfold armaPsi
  rw [hannanMaPolyElim0, findA_neg_arPoly]
  simp [PowerSeries.coeff_one]

private lemma findB_psi_zero : armaPsi findB (Fin.elim0 : Fin 0 → ℝ) 0 = 1 :=
  armaPsi_zero _ _

/-- `ψᵇ_1 = 1/2`, read off the convolution identity `b ∗ ψ = a` at `n = 1`. -/
private lemma findB_psi_one : armaPsi findB (Fin.elim0 : Fin 0 → ℝ) 1 = 1 / 2 := by
  have hconv := arPoly_conv_armaPsi findB (Fin.elim0 : Fin 0 → ℝ) 1
  rw [Finset.sum_range_succ, Finset.sum_range_one, hannanMaPolyElim0] at hconv
  rw [findB_arPoly] at hconv
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
    Polynomial.coeff_X] at hconv
  norm_num [findB_psi_zero] at hconv
  linarith [hconv]

/-- Pairing a filter with `δ₀` on the right: only the lag `≤ 0` side survives. -/
private lemma maCrossACVF_delta_right (ψ : ℕ → ℝ) (φ : ℕ → ℝ)
    (hφ : ∀ n, φ n = if n = 0 then 1 else 0) (m : ℕ) :
    maCrossACVF ψ φ (-(m : ℤ)) = ψ m ∧ maCrossACVF ψ φ ((m : ℤ) + 1) = 0 := by
  constructor
  · rw [maCrossACVF]
    refine tsum_eq_single m ?_ |>.trans ?_
    · intro j hj
      by_cases h : 0 ≤ (j : ℤ) + -(m : ℤ)
      · rw [dif_pos h, hφ]
        rw [if_neg (by omega), mul_zero]
      · rw [dif_neg h, mul_zero]
    · rw [dif_pos (by omega), hφ]
      simp
  · rw [maCrossACVF]
    refine (tsum_congr fun j => ?_).trans tsum_zero
    rw [dif_pos (by omega), hφ, if_neg (by omega), mul_zero]

/-- Pairing `δ₀` with a filter on the left: the mirror statement. -/
private lemma maCrossACVF_delta_left (ψ : ℕ → ℝ) (φ : ℕ → ℝ)
    (hφ : ∀ n, φ n = if n = 0 then 1 else 0) (m : ℕ) :
    maCrossACVF φ ψ ((m : ℤ)) = ψ m ∧ maCrossACVF φ ψ (-((m : ℤ) + 1)) = 0 := by
  constructor
  · rw [maCrossACVF]
    refine tsum_eq_single 0 ?_ |>.trans ?_
    · intro j hj
      rw [hφ, if_neg hj, zero_mul]
    · rw [dif_pos (by omega), hφ]
      simp
  · rw [maCrossACVF]
    refine (tsum_congr fun j => ?_).trans tsum_zero
    by_cases h : 0 ≤ (j : ℤ) + -((m : ℤ) + 1)
    · rw [hφ, if_neg (by omega), zero_mul]
    · rw [dif_neg h, mul_zero]

/-- **FINDING 26.** The forward Gram `hannanVarZ` — the matrix the frozen Hannan
statements use — and the backward Gram `hannanVarZBack` — the covariance of the score
vector `Z_t` that `MLEAsymptotics.scoreSeq` actually contracts — have **different**
quadratic forms already at ARMA(2,1), the smallest order at which the AR–MA cross-block
can be read at two different lags. The gap here is exactly `1`. -/
theorem hannanVarZ_quadForm_ne_back :
    ∃ (x : Fin 2 ⊕ Fin 1 → ℝ),
      (∑ s, x s * ∑ t, hannanVarZ findB findA s t * x t)
        = (∑ s, x s * ∑ t, hannanVarZBack findB findA s t * x t) + 1 := by
  classical
  refine ⟨Sum.elim ![0, 1] ![1], ?_⟩
  have hd := findA_psi
  -- the four cross-entries, at the two opposite lags
  have h1 : maCrossACVF (armaPsi findB (Fin.elim0 : Fin 0 → ℝ))
      (armaPsi (fun j => -findA j) (Fin.elim0 : Fin 0 → ℝ)) (-(1 : ℤ)) = 1 / 2 := by
    have := (maCrossACVF_delta_right (armaPsi findB (Fin.elim0 : Fin 0 → ℝ)) _ hd 1).1
    rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from rfl] at this
    rw [this, findB_psi_one]
  have h2 : maCrossACVF (armaPsi findB (Fin.elim0 : Fin 0 → ℝ))
      (armaPsi (fun j => -findA j) (Fin.elim0 : Fin 0 → ℝ)) (1 : ℤ) = 0 := by
    have := (maCrossACVF_delta_right (armaPsi findB (Fin.elim0 : Fin 0 → ℝ)) _ hd 0).2
    simpa using this
  have h3 : maCrossACVF (armaPsi (fun j => -findA j) (Fin.elim0 : Fin 0 → ℝ))
      (armaPsi findB (Fin.elim0 : Fin 0 → ℝ)) (1 : ℤ) = 1 / 2 := by
    have := (maCrossACVF_delta_left (armaPsi findB (Fin.elim0 : Fin 0 → ℝ)) _ hd 1).1
    rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from rfl] at this
    rw [this, findB_psi_one]
  have h4 : maCrossACVF (armaPsi (fun j => -findA j) (Fin.elim0 : Fin 0 → ℝ))
      (armaPsi findB (Fin.elim0 : Fin 0 → ℝ)) (-(1 : ℤ)) = 0 := by
    have := (maCrossACVF_delta_left (armaPsi findB (Fin.elim0 : Fin 0 → ℝ)) _ hd 0).2
    simpa using this
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one, Sum.elim_inl,
    Sum.elim_inr, hannanVarZ, hannanVarZBack, hannanSeq, hannanShiftBack, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [h1, h2, h3, h4]
  ring

/-! ## Step 4: a vanishing combination forces a polynomial identity -/

private lemma coeff_arPolyInv {p : ℕ} (b : Fin p → ℝ) (n : ℕ) :
    PowerSeries.coeff n ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = armaPsi b (Fin.elim0 : Fin 0 → ℝ) n := by
  rw [armaPsi, hannanMaPolyElim0]
  simp

private lemma coeff_maPolyInv {q : ℕ} (a : Fin q → ℝ) (n : ℕ) :
    PowerSeries.coeff n ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = armaPsi (fun j => -a j) (Fin.elim0 : Fin 0 → ℝ) n := by
  rw [armaPsi, hannanMaPolyElim0, arPoly_neg]
  simp

private noncomputable def hannanPolyC {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ i : Fin p, Polynomial.C (x (Sum.inl i)) * Polynomial.X ^ (p + q - (i : ℕ))

private noncomputable def hannanPolyD {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ j : Fin q, Polynomial.C (x (Sum.inr j)) * Polynomial.X ^ (p + q - (j : ℕ))

private noncomputable def hannanPolyC0 {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ i : Fin p, Polynomial.C (x (Sum.inl i)) * Polynomial.X ^ (p - 1 - (i : ℕ))

private noncomputable def hannanPolyD0 {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ j : Fin q, Polynomial.C (x (Sum.inr j)) * Polynomial.X ^ (q - 1 - (j : ℕ))

private lemma hannanPolyC_factor {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    hannanPolyC x = Polynomial.X ^ (q + 1) * hannanPolyC0 x := by
  rw [hannanPolyC, hannanPolyC0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi := i.isLt
  have hexp : q + 1 + (p - 1 - (i : ℕ)) = p + q - (i : ℕ) := by omega
  calc Polynomial.C (x (Sum.inl i)) * Polynomial.X ^ (p + q - (i : ℕ))
      = Polynomial.C (x (Sum.inl i)) * Polynomial.X ^ (q + 1 + (p - 1 - (i : ℕ))) := by
        rw [hexp]
    _ = Polynomial.X ^ (q + 1) * (Polynomial.C (x (Sum.inl i))
          * Polynomial.X ^ (p - 1 - (i : ℕ))) := by rw [pow_add]; ring

private lemma hannanPolyD_factor {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    hannanPolyD x = Polynomial.X ^ (p + 1) * hannanPolyD0 x := by
  rw [hannanPolyD, hannanPolyD0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj := j.isLt
  have hexp : p + 1 + (q - 1 - (j : ℕ)) = p + q - (j : ℕ) := by omega
  calc Polynomial.C (x (Sum.inr j)) * Polynomial.X ^ (p + q - (j : ℕ))
      = Polynomial.C (x (Sum.inr j)) * Polynomial.X ^ (p + 1 + (q - 1 - (j : ℕ))) := by
        rw [hexp]
    _ = Polynomial.X ^ (p + 1) * (Polynomial.C (x (Sum.inr j))
          * Polynomial.X ^ (q - 1 - (j : ℕ))) := by rw [pow_add]; ring

private lemma coe_hannanPolyC {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    ((hannanPolyC x : Polynomial ℝ) : PowerSeries ℝ)
      = ∑ i : Fin p, PowerSeries.C (x (Sum.inl i)) * PowerSeries.X ^ (p + q - (i : ℕ)) := by
  rw [hannanPolyC, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

private lemma coe_hannanPolyD {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    ((hannanPolyD x : Polynomial ℝ) : PowerSeries ℝ)
      = ∑ j : Fin q, PowerSeries.C (x (Sum.inr j)) * PowerSeries.X ^ (p + q - (j : ℕ)) := by
  rw [hannanPolyD, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

private lemma coeff_hannanPolyC_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (x : Fin p ⊕ Fin q → ℝ) (n : ℕ) :
    PowerSeries.coeff n (((hannanPolyC x : Polynomial ℝ) : PowerSeries ℝ)
        * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = ∑ i : Fin p, x (Sum.inl i) * hannanVec b a (Sum.inl i) n := by
  rw [coe_hannanPolyC, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hseq : (fun m => PowerSeries.coeff m
      ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)) = hannanSeq b a (Sum.inl i) :=
    funext fun m => coeff_arPolyInv b m
  rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq_hannanShiftSeq, hannanVec_apply, hseq]
  simp only [hannanShift]

private lemma coeff_hannanPolyD_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (x : Fin p ⊕ Fin q → ℝ) (n : ℕ) :
    PowerSeries.coeff n (((hannanPolyD x : Polynomial ℝ) : PowerSeries ℝ)
        * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = ∑ j : Fin q, x (Sum.inr j) * hannanVec b a (Sum.inr j) n := by
  rw [coe_hannanPolyD, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hseq : (fun m => PowerSeries.coeff m
      ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)) = hannanSeq b a (Sum.inr j) :=
    funext fun m => coeff_maPolyInv a m
  rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq_hannanShiftSeq, hannanVec_apply, hseq]
  simp only [hannanShift]

/-- `arPoly b` has constant coefficient `1`, hence is coprime to `X`. -/
private lemma isCoprime_arPoly_X {p : ℕ} (b : Fin p → ℝ) :
    IsCoprime (arPoly b) (Polynomial.X : Polynomial ℝ) := by
  refine ⟨1, ∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ), ?_⟩
  have hs : (∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)) * Polynomial.X
      = ∑ i : Fin p, Polynomial.C (b i) * Polynomial.X ^ ((i : ℕ) + 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, ← pow_succ]
  rw [one_mul, arPoly, hs]
  ring

/-! ## Step 5: the identifiability core -/

private lemma eq_zero_of_hannanVec_combo {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hcop : IsCoprime (arPoly b) (maPoly a)) (hbdeg : (arPoly b).natDegree = p)
    (x : Fin p ⊕ Fin q → ℝ)
    (hx : ∀ n : ℕ, ∑ s, x s * hannanVec b a s n = 0) : x = 0 := by
  have hbne : PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, hannanCoeffArPolyZero]; exact one_ne_zero
  have hane : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, hannanCoeffMaPolyZero]; exact one_ne_zero
  have hb1 := PowerSeries.mul_inv_cancel _ hbne
  have ha1 := PowerSeries.mul_inv_cancel _ hane
  have hzero : ((hannanPolyC x : Polynomial ℝ) : PowerSeries ℝ)
        * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹
      + ((hannanPolyD x : Polynomial ℝ) : PowerSeries ℝ)
        * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹ = 0 := by
    refine PowerSeries.ext fun n => ?_
    rw [map_add, coeff_hannanPolyC_mul b a, coeff_hannanPolyD_mul b a, map_zero]
    have hn := hx n
    rwa [Fintype.sum_sum_type] at hn
  have hkey : ((hannanPolyC x : Polynomial ℝ) : PowerSeries ℝ)
        * ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
      + ((hannanPolyD x : Polynomial ℝ) : PowerSeries ℝ)
        * ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) = 0 := by
    have h2 : (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          * ((maPoly a : Polynomial ℝ) : PowerSeries ℝ))
        * (((hannanPolyC x : Polynomial ℝ) : PowerSeries ℝ)
            * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹
          + ((hannanPolyD x : Polynomial ℝ) : PowerSeries ℝ)
            * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
        = ((hannanPolyC x : Polynomial ℝ) : PowerSeries ℝ)
            * ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
            * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
              * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
          + ((hannanPolyD x : Polynomial ℝ) : PowerSeries ℝ)
            * ((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
            * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
              * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹) := by ring
    rw [hzero, mul_zero, hb1, ha1, mul_one, mul_one] at h2
    exact h2.symm
  have hpoly : hannanPolyC x * maPoly a + hannanPolyD x * arPoly b = 0 := by
    apply Polynomial.coe_injective ℝ
    simpa using hkey
  -- `arPoly b` divides `C`, hence (being coprime to `X`) divides `C₀`, which has too
  -- low a degree to be a nonzero multiple.
  have hdvdC : arPoly b ∣ hannanPolyC x :=
    hcop.dvd_of_dvd_mul_right ⟨-hannanPolyD x, by linear_combination hpoly⟩
  have hdvdC0 : arPoly b ∣ hannanPolyC0 x := by
    rw [hannanPolyC_factor] at hdvdC
    exact ((isCoprime_arPoly_X b).pow_right).dvd_of_dvd_mul_left hdvdC
  have hC0 : hannanPolyC0 x = 0 := by
    by_contra hne
    have hp : p ≠ 0 := by
      rintro rfl
      exact hne (by simp [hannanPolyC0])
    have h1 : (arPoly b).natDegree ≤ (hannanPolyC0 x).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvdC0 hne
    have h2 : (hannanPolyC0 x).natDegree ≤ p - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      omega
    omega
  have hCz : hannanPolyC x = 0 := by rw [hannanPolyC_factor, hC0, mul_zero]
  have hDz : hannanPolyD x = 0 := by
    rw [hCz, zero_mul, zero_add] at hpoly
    rcases mul_eq_zero.1 hpoly with h | h
    · exact h
    · exact absurd h (hannanArPolyNeZero b)
  have hD0 : hannanPolyD0 x = 0 := by
    rw [hannanPolyD_factor] at hDz
    rcases mul_eq_zero.1 hDz with h | h
    · exact absurd h (pow_ne_zero _ Polynomial.X_ne_zero)
    · exact h
  funext s
  cases s with
  | inl i =>
    have hcoeff : (hannanPolyC0 x).coeff (p - 1 - (i : ℕ)) = x (Sum.inl i) := by
      rw [hannanPolyC0, Polynomial.finset_sum_coeff, Finset.sum_eq_single i]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro i' _ hne'
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
        have h1 := i.isLt
        have h2 := i'.isLt
        have h3 : (i : ℕ) ≠ (i' : ℕ) := fun h => hne' (Fin.ext h.symm)
        omega
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hC0] at hcoeff
    simpa using hcoeff.symm
  | inr j =>
    have hcoeff : (hannanPolyD0 x).coeff (q - 1 - (j : ℕ)) = x (Sum.inr j) := by
      rw [hannanPolyD0, Polynomial.finset_sum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro j' _ hne'
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
        have h1 := j.isLt
        have h2 := j'.isLt
        have h3 : (j : ℕ) ≠ (j' : ℕ) := fun h => hne' (Fin.ext h.symm)
        omega
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hD0] at hcoeff
    simpa using hcoeff.symm


/-- **Positive-definiteness of the information matrix** under coprimality of the lag
polynomials (FY's implicit minimal-orders assumption; the ARMA(1,1) `a + b = 0`
degeneracy shows it is necessary). -/
theorem hannanVarZ_posDef {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a)
    -- USER-INPUT: coprime lag polynomials; FY §3.3.2 implicit, explicit in Hannan 1973
    (hcop : IsCoprime (arPoly b) (maPoly a))
    -- USER-INPUT: FY's minimal-orders convention *in full* — the lag polynomials
    -- genuinely have degrees `p` and `q` (i.e. `b_{p−1} ≠ 0`, `a_{q−1} ≠ 0`).
    -- Added 2026-08-09 after a machine-checked counterexample showed coprimality alone
    -- is insufficient: with `b = (1/2, 0)`, `a = (1/3, 0)` (degrees 1 < p = q = 2) the
    -- Gram matrix is singular, since `(U_t − ½U_{t−1}) − (V_t + ⅓V_{t−1}) = 0`.
    -- Hannan 1973 §2 assumes the orders are exact; FY inherits it silently.
    (hbdeg : (arPoly b).natDegree = p) (hadeg : (maPoly a).natDegree = q) :
    (hannanVarZ b a).PosDef := by
  -- **Was FALSE as originally frozen**; the degree hypotheses above were added by the
  -- laptop session on 2026-08-09 in response to the counterexample recorded below,
  -- which is kept as documentation. Under `hbdeg` the Bézout argument closes — see the
  -- section header above for the route. (Only `hbdeg` is consumed: once `C = 0` the
  -- identity collapses to `D · b = 0` and `b ≠ 0` finishes, so the symmetric hypothesis
  -- `hadeg` is redundant. It is kept in the signature as FY's minimal-orders convention
  -- and because the mirror-image argument would use it instead of `hbdeg`.)
  --
  -- Witness for the *old* signature (verified exactly): `p = q = 2`, `b = (1/2, 0)`,
  -- `a = (1/3, 0)`, so `arPoly b = 1 - z/2` and `maPoly a = 1 + z/3`. Both are root-free
  -- on the closed unit disc (roots `2` and `-3`), so `hB` holds; they are coprime, with
  -- the Bézout identity `(2/5)·(1 - z/2) + (3/5)·(1 + z/3) = 1`, so `hcop` holds. Yet
  -- with `ψᵇ_n = 2^{-n}`, `ψᵃ_n = (-3)^{-n}` the vector `c = (-1/2, 1, -1/3, -1)`
  -- (order `inl 0, inl 1, inr 0, inr 1`) satisfies `(hannanVarZ b a) *ᵥ c = 0`: the
  -- corresponding process combination is
  -- `(U_t - (1/2)U_{t-1}) - (V_t + (1/3)V_{t-1}) = ε_t - ε_t = 0`. Its lag polynomials
  -- have degree `1 < p = q = 2`, so `hbdeg` now excludes it.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · -- A Gram matrix is symmetric.
    ext s t
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [hannanVarZ_gram, hannanVarZ_gram]
    exact tsum_congr fun n => mul_comm _ _
  · intro x hx
    have hsq : Summable fun n : ℕ => (∑ s, x s * hannanVec b a s n) ^ 2 := by
      have h0 := hannanSummableMul (summable_abs_hannanCombo hB x)
        (summable_abs_hannanCombo hB x)
      exact h0.congr fun n => by rw [sq]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (∑ s, x s * hannanVec b a s n) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (eq_zero_of_hannanVec_combo hcop hbdeg x hall)
    have hpos : 0 < (∑ s, x s * hannanVec b a s n) ^ 2 := by positivity
    have hle : (∑ s, x s * hannanVec b a s n) ^ 2
        ≤ ∑' m : ℕ, (∑ s, x s * hannanVec b a s m) ^ 2 :=
      hsq.le_tsum n fun m _ => sq_nonneg _
    have hgoal : dotProduct (star x) (Matrix.mulVec (hannanVarZ b a) x)
        = ∑' m : ℕ, (∑ s, x s * hannanVec b a s m) ^ 2 := by
      rw [← hannanVarZ_quadForm hB x]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
    rw [hgoal]
    linarith

/-! ### Positive-definiteness of the **backward** Gram (finding 26)

`hannanVarZBack` is the Gram matrix of the *same* two filter families as `hannanVarZ`,
read at the score's shifts `1 + i` instead of the forward shifts `p + q − i`, so the
identifiability argument of `hannanVarZ_posDef` runs verbatim with

  `C(z) = Σ_i cᵢ z^{1+i}`,  `D(z) = Σ_j dⱼ z^{1+j}`

in place of the forward pair. The reduced factors `C₀(z) = Σ_i cᵢ zⁱ`,
`D₀(z) = Σ_j dⱼ z^j` are one power of `z` lighter than the forward ones, so the degree
count that closes the argument (`deg C₀ ≤ p − 1 < p = deg b`, under `hbdeg`) is if
anything more comfortable; the hypotheses are exactly those of `hannanVarZ_posDef`.

**FINDING 29 (wave `ts/f1c-hannan-orientation`, 2026-08-09).** This has to be **proved**,
not transported: the two Grams are conjugate by the block-wise reversal permutation only
when `p = q`, and `hannanVarZ_quadForm_ne_back` witnesses that they are genuinely different
quadratic forms at ARMA(2,1). The permutation route fails for a reason worth recording,
since it is what makes finding 26 possible at all: a *common* shift of all coordinates
leaves a Gram matrix unchanged, and the reversal `i ↦ p−1−i` turns the backward AR shifts
`1+i` into `p−i` and the backward MA shifts `1+j` into `q−j`, whereas the forward shifts
are `p+q−i` and `p+q−j`. The two offsets are `q−1` and `p`, which agree only when `p = q`
— the shift is common within each block but *not across the blocks*, and that is exactly
the misalignment of the cross-block. (For `q = 0` or `p = 0` the
transport is available — `hannanVarZ_eq_back_of_pure_ar`, `hannanVarZ_eq_back_of_pure_ma`
— but that covers none of the mixed cases the repair is for.) -/

private noncomputable def hannanPolyCBack {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ i : Fin p, Polynomial.C (x (Sum.inl i)) * Polynomial.X ^ (1 + (i : ℕ))

private noncomputable def hannanPolyDBack {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ j : Fin q, Polynomial.C (x (Sum.inr j)) * Polynomial.X ^ (1 + (j : ℕ))

private noncomputable def hannanPolyC0Back {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ i : Fin p, Polynomial.C (x (Sum.inl i)) * Polynomial.X ^ (i : ℕ)

private noncomputable def hannanPolyD0Back {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) : Polynomial ℝ :=
  ∑ j : Fin q, Polynomial.C (x (Sum.inr j)) * Polynomial.X ^ (j : ℕ)

private lemma hannanPolyCBack_factor {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    hannanPolyCBack x = Polynomial.X * hannanPolyC0Back x := by
  rw [hannanPolyCBack, hannanPolyC0Back, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_add, pow_one]
  ring

private lemma hannanPolyDBack_factor {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    hannanPolyDBack x = Polynomial.X * hannanPolyD0Back x := by
  rw [hannanPolyDBack, hannanPolyD0Back, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_one]
  ring

private lemma coe_hannanPolyCBack {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    ((hannanPolyCBack x : Polynomial ℝ) : PowerSeries ℝ)
      = ∑ i : Fin p, PowerSeries.C (x (Sum.inl i)) * PowerSeries.X ^ (1 + (i : ℕ)) := by
  rw [hannanPolyCBack, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

private lemma coe_hannanPolyDBack {p q : ℕ} (x : Fin p ⊕ Fin q → ℝ) :
    ((hannanPolyDBack x : Polynomial ℝ) : PowerSeries ℝ)
      = ∑ j : Fin q, PowerSeries.C (x (Sum.inr j)) * PowerSeries.X ^ (1 + (j : ℕ)) := by
  rw [hannanPolyDBack, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

private lemma coeff_hannanPolyCBack_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (x : Fin p ⊕ Fin q → ℝ) (n : ℕ) :
    PowerSeries.coeff n (((hannanPolyCBack x : Polynomial ℝ) : PowerSeries ℝ)
        * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = ∑ i : Fin p, x (Sum.inl i) * hannanVecBack b a (Sum.inl i) n := by
  rw [coe_hannanPolyCBack, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hseq : (fun m => PowerSeries.coeff m
      ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)) = hannanSeq b a (Sum.inl i) :=
    funext fun m => coeff_arPolyInv b m
  rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq_hannanShiftSeq]
  simp only [hannanVecBack, hannanShiftBack, hseq]

private lemma coeff_hannanPolyDBack_mul {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (x : Fin p ⊕ Fin q → ℝ) (n : ℕ) :
    PowerSeries.coeff n (((hannanPolyDBack x : Polynomial ℝ) : PowerSeries ℝ)
        * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = ∑ j : Fin q, x (Sum.inr j) * hannanVecBack b a (Sum.inr j) n := by
  rw [coe_hannanPolyDBack, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hseq : (fun m => PowerSeries.coeff m
      ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)) = hannanSeq b a (Sum.inr j) :=
    funext fun m => coeff_maPolyInv a m
  rw [mul_assoc, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq_hannanShiftSeq]
  simp only [hannanVecBack, hannanShiftBack, hseq]

/-- The identifiability core at the **score's** shifts: no nontrivial combination of the
two filter families, left-aligned at `t − 1`, vanishes. -/
private lemma eq_zero_of_hannanVecBack_combo {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hcop : IsCoprime (arPoly b) (maPoly a)) (hbdeg : (arPoly b).natDegree = p)
    (x : Fin p ⊕ Fin q → ℝ)
    (hx : ∀ n : ℕ, ∑ s, x s * hannanVecBack b a s n = 0) : x = 0 := by
  have hbne : PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, hannanCoeffArPolyZero]; exact one_ne_zero
  have hane : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, hannanCoeffMaPolyZero]; exact one_ne_zero
  have hb1 := PowerSeries.mul_inv_cancel _ hbne
  have ha1 := PowerSeries.mul_inv_cancel _ hane
  have hzero : ((hannanPolyCBack x : Polynomial ℝ) : PowerSeries ℝ)
        * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹
      + ((hannanPolyDBack x : Polynomial ℝ) : PowerSeries ℝ)
        * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹ = 0 := by
    refine PowerSeries.ext fun n => ?_
    rw [map_add, coeff_hannanPolyCBack_mul b a, coeff_hannanPolyDBack_mul b a, map_zero]
    have hn := hx n
    rwa [Fintype.sum_sum_type] at hn
  have hkey : ((hannanPolyCBack x : Polynomial ℝ) : PowerSeries ℝ)
        * ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
      + ((hannanPolyDBack x : Polynomial ℝ) : PowerSeries ℝ)
        * ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) = 0 := by
    have h2 : (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
          * ((maPoly a : Polynomial ℝ) : PowerSeries ℝ))
        * (((hannanPolyCBack x : Polynomial ℝ) : PowerSeries ℝ)
            * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹
          + ((hannanPolyDBack x : Polynomial ℝ) : PowerSeries ℝ)
            * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
        = ((hannanPolyCBack x : Polynomial ℝ) : PowerSeries ℝ)
            * ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
            * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
              * (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
          + ((hannanPolyDBack x : Polynomial ℝ) : PowerSeries ℝ)
            * ((arPoly b : Polynomial ℝ) : PowerSeries ℝ)
            * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)
              * (((maPoly a : Polynomial ℝ) : PowerSeries ℝ))⁻¹) := by ring
    rw [hzero, mul_zero, hb1, ha1, mul_one, mul_one] at h2
    exact h2.symm
  have hpoly : hannanPolyCBack x * maPoly a + hannanPolyDBack x * arPoly b = 0 := by
    apply Polynomial.coe_injective ℝ
    simpa using hkey
  have hdvdC : arPoly b ∣ hannanPolyCBack x :=
    hcop.dvd_of_dvd_mul_right ⟨-hannanPolyDBack x, by linear_combination hpoly⟩
  have hdvdC0 : arPoly b ∣ hannanPolyC0Back x := by
    rw [hannanPolyCBack_factor] at hdvdC
    exact (isCoprime_arPoly_X b).dvd_of_dvd_mul_left hdvdC
  have hC0 : hannanPolyC0Back x = 0 := by
    by_contra hne
    have hp : p ≠ 0 := by
      rintro rfl
      exact hne (by simp [hannanPolyC0Back])
    have h1 : (arPoly b).natDegree ≤ (hannanPolyC0Back x).natDegree :=
      Polynomial.natDegree_le_of_dvd hdvdC0 hne
    have h2 : (hannanPolyC0Back x).natDegree ≤ p - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow]
      have := i.isLt
      omega
    omega
  have hCz : hannanPolyCBack x = 0 := by rw [hannanPolyCBack_factor, hC0, mul_zero]
  have hDz : hannanPolyDBack x = 0 := by
    rw [hCz, zero_mul, zero_add] at hpoly
    rcases mul_eq_zero.1 hpoly with h | h
    · exact h
    · exact absurd h (hannanArPolyNeZero b)
  have hD0 : hannanPolyD0Back x = 0 := by
    rw [hannanPolyDBack_factor] at hDz
    rcases mul_eq_zero.1 hDz with h | h
    · exact absurd h Polynomial.X_ne_zero
    · exact h
  funext s
  cases s with
  | inl i =>
    have hcoeff : (hannanPolyC0Back x).coeff (i : ℕ) = x (Sum.inl i) := by
      rw [hannanPolyC0Back, Polynomial.finset_sum_coeff, Finset.sum_eq_single i]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro i' _ hne'
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
        exact fun h => hne' (Fin.ext h.symm)
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hC0] at hcoeff
    simpa using hcoeff.symm
  | inr j =>
    have hcoeff : (hannanPolyD0Back x).coeff (j : ℕ) = x (Sum.inr j) := by
      rw [hannanPolyD0Back, Polynomial.finset_sum_coeff, Finset.sum_eq_single j]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro j' _ hne'
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
        exact fun h => hne' (Fin.ext h.symm)
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hD0] at hcoeff
    simpa using hcoeff.symm

/-- **Positive-definiteness of the true (score) information matrix** — the backward twin
of `hannanVarZ_posDef`, under exactly the same hypotheses (finding 26). This is the
invertibility statement the repaired Hannan chain consumed: the asymptotic covariance of
the (since removed) FY Thm 3.2 headline was `(hannanVarZBack b₀ a₀)⁻¹`. -/
theorem hannanVarZBack_posDef {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a)
    -- USER-INPUT: coprime lag polynomials; FY §3.3.2 implicit, explicit in Hannan 1973
    (hcop : IsCoprime (arPoly b) (maPoly a))
    -- USER-INPUT: FY's minimal-orders convention in full (`deg b = p`, `deg a = q`).
    -- `hbdeg` cannot be dropped here either: the counterexample recorded at
    -- `hannanVarZ_posDef` (`p = q = 2`, `b = (1/2, 0)`, `a = (1/3, 0)`) refutes the
    -- backward Gram as well — at `p = q` the two matrices are conjugate by the
    -- block-wise reversal permutation, so one is positive definite iff the other is,
    -- and the singular direction is the reversal of `c = (-1/2, 1, -1/3, -1)`.
    (hbdeg : (arPoly b).natDegree = p) (hadeg : (maPoly a).natDegree = q) :
    (hannanVarZBack b a).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext s t
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [hannanVarZBack_gram, hannanVarZBack_gram]
    exact tsum_congr fun n => mul_comm _ _
  · intro x hx
    have hsq : Summable fun n : ℕ => (∑ s, x s * hannanVecBack b a s n) ^ 2 := by
      have h0 := hannanSummableMul (summable_abs_hannanComboBack hB x)
        (summable_abs_hannanComboBack hB x)
      exact h0.congr fun n => by rw [sq]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (∑ s, x s * hannanVecBack b a s n) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (eq_zero_of_hannanVecBack_combo hcop hbdeg x hall)
    have hpos : 0 < (∑ s, x s * hannanVecBack b a s n) ^ 2 := by positivity
    have hle : (∑ s, x s * hannanVecBack b a s n) ^ 2
        ≤ ∑' m : ℕ, (∑ s, x s * hannanVecBack b a s m) ^ 2 :=
      hsq.le_tsum n fun m _ => sq_nonneg _
    have hgoal : dotProduct (star x) (Matrix.mulVec (hannanVarZBack b a) x)
        = ∑' m : ℕ, (∑ s, x s * hannanVecBack b a s m) ^ 2 := by
      rw [← hannanVarZBack_quadForm hB x]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
    rw [hgoal]
    linarith

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **θ-residual process** in the `L²` sense: `ε_t(θ)` is the `L²` limit of
`Σ_{j<N} π_j(θ) X_{t−j}` (the AR(∞) inversion applied to the data). -/
def IsARMAResidualOf {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (r X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ t : ℤ, Tendsto
    (fun N : ℕ => eLpNorm
      (fun ω => r t ω - ∑ j ∈ Finset.range N, armaPi b a j * X (t - (j : ℕ)) ω) 2 μ)
    atTop (𝓝 0)

section ResidualAux

variable {X : ℤ → Ω → ℝ} {φ : ℕ → ℝ}

/-- `inner ℝ` on the reals is multiplication. -/
private lemma real_inner_mul (x y : ℝ) : inner ℝ x y = x * y := by
  rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply]
  simp [mul_comm]

/-- The `L²` inner product of two classes is the integral of the product. -/
private lemma inner_toLp {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [real_inner_mul, h1, h2]

/-- The one-sided partial sum `Σ_{j<N} φ_j X_{t−j}` of the inversion filter. -/
private noncomputable def rpsum (φ : ℕ → ℝ) (X : ℤ → Ω → ℝ) (t : ℤ) (N : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.range N, φ j * X (t - (j : ℕ)) ω

private lemma memLp_rpsum (hX : IsStationary X μ) (t : ℤ) (N : ℕ) :
    MemLp (rpsum φ X t N) 2 μ :=
  memLp_finset_sum _ fun j _ => (hX.memLp (t - (j : ℕ))).const_mul (φ j)

private noncomputable def rpsumLp (hX : IsStationary X μ) (φ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    Lp ℝ 2 μ := (memLp_rpsum (φ := φ) hX t N).toLp _

private lemma coeFn_rpsumLp (hX : IsStationary X μ) (φ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    ⇑(rpsumLp hX φ t N) =ᵐ[μ] rpsum φ X t N :=
  (memLp_rpsum (φ := φ) hX t N).coeFn_toLp

/-- The `L²` norm of a stationary process is the same at every time. -/
private lemma norm_toLp_stationary [IsProbabilityMeasure μ] (hX : IsStationary X μ) (s : ℤ) :
    ‖(hX.memLp s).toLp (X s)‖ = ‖(hX.memLp 0).toLp (X 0)‖ := by
  have key : ∀ u : ℤ, ‖(hX.memLp u).toLp (X u)‖ ^ 2 = acvf X μ 0 + (∫ ω, X 0 ω ∂μ) ^ 2 := by
    intro u
    rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have h := covariance_eq_sub (hX.memLp u) (hX.memLp u)
    have hcov : cov[X u, X u; μ] = acvf X μ 0 := by
      have h1 := hX.cov_eq_acvf u u
      rwa [sub_self] at h1
    have hmul : μ[X u * X u] = ∫ ω, X u ω * X u ω ∂μ := by simp [Pi.mul_apply]
    rw [hcov, hmul, hX.integral_eq u 0] at h
    have hsq : (∫ ω, X 0 ω ∂μ) ^ 2 = (∫ ω, X 0 ω ∂μ) * (∫ ω, X 0 ω ∂μ) := sq _
    linarith
  have e1 := Real.sqrt_sq (norm_nonneg ((hX.memLp s).toLp (X s)))
  have e2 := Real.sqrt_sq (norm_nonneg ((hX.memLp 0).toLp (X 0)))
  rw [← e1, ← e2, key s, key 0]

/-- Successive partial sums differ by the single term `φ_N X_{t−N}`. -/
private lemma dist_rpsumLp_succ [IsProbabilityMeasure μ] (hX : IsStationary X μ)
    (φ : ℕ → ℝ) (t : ℤ) (N : ℕ) :
    dist (rpsumLp hX φ t N) (rpsumLp hX φ t (N + 1))
      = |φ N| * ‖(hX.memLp 0).toLp (X 0)‖ := by
  rw [dist_comm, Lp.dist_def]
  have hae : (⇑(rpsumLp hX φ t (N + 1)) - ⇑(rpsumLp hX φ t N))
      =ᵐ[μ] (φ N • X (t - (N : ℕ))) := by
    filter_upwards [coeFn_rpsumLp hX φ t (N + 1), coeFn_rpsumLp hX φ t N] with ω h1 h2
    simp only [Pi.sub_apply, h1, h2, rpsum, Finset.sum_range_succ, Pi.smul_apply, smul_eq_mul]
    ring
  rw [eLpNorm_congr_ae hae, eLpNorm_const_smul, ENNReal.toReal_mul]
  have h : ((eLpNorm (X (t - (N : ℕ))) 2 μ)).toReal = ‖(hX.memLp 0).toLp (X 0)‖ := by
    rw [← Lp.norm_toLp _ (hX.memLp (t - (N : ℕ))), norm_toLp_stationary hX]
  rw [h]
  simp

/-- The `L²` limit of the one-sided partial sums exists for `ℓ¹` coefficients over a
stationary input (the one-sided instance of `exists_isFilteredBy`). -/
private lemma exists_rpsum_limit [IsProbabilityMeasure μ] (hφ : Summable fun n => |φ n|)
    (hX : IsStationary X μ) (t : ℤ) :
    ∃ f : Ω → ℝ, Measurable f ∧
      Tendsto (fun N => eLpNorm (fun ω => f ω - rpsum φ X t N ω) 2 μ) atTop (𝓝 0) := by
  have hsum : Summable fun N : ℕ =>
      dist (rpsumLp hX φ t N) (rpsumLp hX φ t N.succ) :=
    (hφ.mul_right ‖(hX.memLp 0).toLp (X 0)‖).congr fun N => (dist_rpsumLp_succ hX φ t N).symm
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)
  refine ⟨(Lp.aestronglyMeasurable L).mk _,
    (Lp.aestronglyMeasurable L).stronglyMeasurable_mk.measurable, ?_⟩
  have heq : ∀ N : ℕ,
      eLpNorm (fun ω => ((Lp.aestronglyMeasurable L).mk _) ω - rpsum φ X t N ω) 2 μ
        = edist (rpsumLp hX φ t N) L := by
    intro N
    rw [edist_comm, Lp.edist_def]
    refine eLpNorm_congr_ae ?_
    filter_upwards [(Lp.aestronglyMeasurable L).ae_eq_mk, coeFn_rpsumLp hX φ t N] with ω h1 h2
    simp only [Pi.sub_apply, ← h1, h2]
  simp_rw [heq, edist_dist]
  simpa using ENNReal.tendsto_ofReal (tendsto_iff_dist_tendsto_zero.mp hL)

end ResidualAux

/-- Existence of the residual process on the constraint set (geometric `π`-decay +
stationarity, mirroring `exists_isFilteredBy`). -/
theorem exists_isARMAResidualOf [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {X : ℤ → Ω → ℝ}
    (hB : ARMAInvertibleParams b a) (hstat : IsStationary X μ)
    (hmeas : ∀ t, Measurable (X t)) :
    ∃ r : ℤ → Ω → ℝ, (∀ t, Measurable (r t)) ∧ IsARMAResidualOf b a r X μ := by
  choose r hrm hrlim using fun t : ℤ =>
    exists_rpsum_limit (φ := armaPi b a) (summable_abs_armaPi hB) hstat t
  exact ⟨r, hrm, hrlim⟩

/-- A finite linear combination of `L²`-approximable families is `L²`-approximable. -/
private lemma tendsto_eLpNorm_comb [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {F : ι → Ω → ℝ} {G : ι → ℕ → Ω → ℝ} (α : ι → ℝ)
    (hm : ∀ (i : ι) (N : ℕ), AEStronglyMeasurable (fun ω => F i ω - G i N ω) μ)
    (hconv : ∀ i : ι, Tendsto (fun N => eLpNorm (fun ω => F i ω - G i N ω) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun N => eLpNorm (fun ω => (∑ i, α i * F i ω) - ∑ i, α i * G i N ω) 2 μ)
      atTop (𝓝 0) := by
  have hfun : ∀ N : ℕ, (fun ω => (∑ i, α i * F i ω) - ∑ i, α i * G i N ω)
      = ∑ i : ι, (α i • fun ω => F i ω - G i N ω) := by
    intro N
    funext ω
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
  have hbd : ∀ N : ℕ, eLpNorm (fun ω => (∑ i, α i * F i ω) - ∑ i, α i * G i N ω) 2 μ
      ≤ ∑ i : ι, ‖α i‖ₑ * eLpNorm (fun ω => F i ω - G i N ω) 2 μ := by
    intro N
    rw [hfun N]
    refine (eLpNorm_sum_le (fun i _ => (hm i N).const_smul _) one_le_two).trans ?_
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by rw [eLpNorm_const_smul])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun N => zero_le) hbd
  have hterm : ∀ i : ι, Tendsto
      (fun N : ℕ => ‖α i‖ₑ * eLpNorm (fun ω => F i ω - G i N ω) 2 μ) atTop (𝓝 0) := fun i => by
    simpa using ENNReal.Tendsto.const_mul (a := ‖α i‖ₑ) (hconv i) (Or.inr (by simp))
  have hsum := tendsto_finset_sum (Finset.univ : Finset ι) fun i (_ : i ∈ Finset.univ) => hterm i
  simpa using hsum

section ResidualId

/-- The constant coefficient of the AR polynomial is `1`. -/
private lemma coeff_zero_arPoly {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- The constant coefficient of the MA polynomial is `1`. -/
private lemma coeff_zero_maPoly {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

/-- **`π ∗ ψ = δ₀`**: the inversion coefficients (`b/a`) and the transfer coefficients
(`a/b`) are mutually inverse power series, so their convolution is the unit. -/
private lemma armaPi_conv_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), armaPi b a k * armaPsi b a (m - k)
      = if m = 0 then 1 else 0 := by
  have hA : PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_zero_arPoly]
    exact one_ne_zero
  have hMA : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_zero_maPoly]
    exact one_ne_zero
  have h1 := PowerSeries.mul_inv_cancel _ hA
  have h2 := PowerSeries.mul_inv_cancel _ hMA
  have key : ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))
        * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
      * (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))
        * ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) = 1 := by
    calc ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))
          * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        * (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))
          * ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        = ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ))
            * ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
          * (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))
            * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  have hc := congrArg (PowerSeries.coeff m) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one] at hc
  exact hc

variable {ε : ℤ → Ω → ℝ} {σ2 : ℝ}

/-- The `L²` norm of white noise is the same at every time. -/
private lemma eLpNorm_noise_eq [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ) (s : ℤ) :
    eLpNorm (ε s) 2 μ = ENNReal.ofReal (Real.sqrt σ2) := by
  have hsq : ‖(hε.memLp s).toLp (ε s)‖ ^ 2 = σ2 := by
    rw [← real_inner_self_eq_norm_sq, inner_toLp]
    have hc := covariance_eq_sub (hε.memLp s) (hε.memLp s)
    rw [hε.integral_eq_zero s, zero_mul, sub_zero,
      covariance_self (hε.memLp s).aestronglyMeasurable.aemeasurable, hε.variance_eq s] at hc
    have h2 : μ[ε s * ε s] = ∫ ω, ε s ω * ε s ω ∂μ := by simp [Pi.mul_apply]
    rw [h2] at hc
    exact hc.symm
  have hnorm : ‖(hε.memLp s).toLp (ε s)‖ = Real.sqrt σ2 := by
    have hh := Real.sqrt_sq (norm_nonneg ((hε.memLp s).toLp (ε s)))
    rw [hsq] at hh
    exact hh.symm
  rw [Lp.norm_toLp] at hnorm
  rw [← hnorm, ENNReal.ofReal_toReal (hε.memLp s).2.ne]

/-- The `L²` norm of a finite noise combination is at most the `ℓ¹` mass of the
coefficients times the noise scale. -/
private lemma eLpNorm_noise_comb_le [IsProbabilityMeasure μ] (hε : IsWhiteNoise ε σ2 μ)
    {ι : Type*} (s : Finset ι) (cc : ι → ℝ) (u : ι → ℤ) :
    eLpNorm (fun ω => ∑ i ∈ s, cc i * ε (u i) ω) 2 μ
      ≤ ENNReal.ofReal (∑ i ∈ s, |cc i|) * ENNReal.ofReal (Real.sqrt σ2) := by
  have hfun : (fun ω => ∑ i ∈ s, cc i * ε (u i) ω) = ∑ i ∈ s, fun ω => cc i * ε (u i) ω := by
    funext ω; simp
  rw [hfun]
  refine (eLpNorm_sum_le (fun i _ =>
    ((hε.measurable (u i)).const_mul (cc i)).aestronglyMeasurable) one_le_two).trans ?_
  have hterm : ∀ i, eLpNorm (fun ω => cc i * ε (u i) ω) 2 μ
      = ENNReal.ofReal |cc i| * ENNReal.ofReal (Real.sqrt σ2) := by
    intro i
    have hsm : (fun ω => cc i * ε (u i) ω) = cc i • (ε (u i)) := by funext ω; simp
    rw [hsm, eLpNorm_const_smul, eLpNorm_noise_eq hε]
    congr 1
    simp [Real.enorm_eq_ofReal_abs]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]

end ResidualId

/-- **Residuals at the truth recover the innovations**: for a stationary causal
invertible ARMA at its true parameters, `ε_t(θ₀) = ε_t` a.e. -/
theorem isARMAResidualOf_eq_noise [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε r : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    (hr : IsARMAResidualOf b a r X μ) (hrmeas : ∀ t, Measurable (r t)) (t : ℤ) :
    r t =ᵐ[μ] ε t := by
  classical
  have hεWN : IsWhiteNoise ε σ2 μ := h.whiteNoise
  -- Opaque copies of the two coefficient sequences: their power-series definitions must
  -- never be unfolded during elaboration (`PowerSeries.inv` is well-founded recursion).
  obtain ⟨π, hπdef⟩ : ∃ f : ℕ → ℝ, f = armaPi b a := ⟨_, rfl⟩
  obtain ⟨ψc, hψdef⟩ : ∃ f : ℕ → ℝ, f = armaPsi b a := ⟨_, rfl⟩
  have hπ : Summable fun n : ℕ => |π n| := by
    rw [hπdef]; exact summable_abs_armaPi hB
  have hψ : Summable fun n : ℕ => |ψc n| := by
    rw [hψdef]; exact summable_abs_armaPsi a hB.1
  have hconv0 : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), π k * ψc (m - k)
      = if m = 0 then 1 else 0 := by
    rw [hπdef, hψdef]; exact armaPi_conv_armaPsi b a
  have hlin : ∀ s : ℤ, Tendsto (fun M : ℕ => eLpNorm
      (fun ω => X s ω - ∑ l ∈ Finset.range M, ψc l * ε (s - (l : ℕ)) ω) 2 μ) atTop (𝓝 0) := by
    rw [hψdef]; exact hcausal
  have hres : Tendsto (fun N : ℕ => eLpNorm
      (fun ω => r t ω - ∑ j ∈ Finset.range N, π j * X (t - (j : ℕ)) ω) 2 μ) atTop (𝓝 0) := by
    rw [hπdef]; exact hr t
  have hXmem : ∀ s, MemLp (X s) 2 μ :=
    hcausal.memLp (summable_abs_armaPsi a hB.1) hεWN hmeas
  have hF : Summable fun x : ℕ × ℕ => |π x.1| * |ψc x.2| :=
    hπ.mul_of_nonneg hψ (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  -- the triangular exhaustion of the coefficient index set
  obtain ⟨Tri, hTri⟩ : ∃ T : ℕ → Finset (ℕ × ℕ), T = fun N =>
      (Finset.range N ×ˢ Finset.range N).filter fun x => x.1 + x.2 < N := ⟨_, rfl⟩
  have hTriMem : ∀ (N : ℕ) (x : ℕ × ℕ), x ∈ Tri N ↔ x.1 + x.2 < N := by
    intro N x
    simp only [hTri, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  -- each antidiagonal contributes the convolution `π ∗ ψ`, i.e. `δ₀`
  have hantidiag : ∀ (m : ℕ) (ω : Ω),
      ∑ x ∈ Finset.antidiagonal m, (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω
        = (if m = 0 then 1 else 0) * ε (t - (m : ℕ)) ω := by
    intro m ω
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    have hcong : ∀ k ∈ Finset.range (m + 1),
        (π k * ψc (m - k)) * ε (t - (k : ℕ) - ((m - k : ℕ) : ℕ)) ω
          = (π k * ψc (m - k)) * ε (t - (m : ℕ)) ω := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hidx : t - (k : ℤ) - ((m - k : ℕ) : ℤ) = t - (m : ℤ) := by omega
      rw [hidx]
    rw [Finset.sum_congr rfl hcong, ← Finset.sum_mul, hconv0]
  -- so the triangle sums telescope to the innovation itself
  have hTriSum : ∀ (N : ℕ) (ω : Ω),
      ∑ x ∈ Tri (N + 1), (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω = ε t ω := by
    intro N ω
    induction N with
    | zero =>
      have h1 : Tri 1 = {((0 : ℕ), (0 : ℕ))} := by
        ext x
        rw [hTriMem]
        simp only [Finset.mem_singleton, Prod.ext_iff]
        omega
      have h0 : π 0 * ψc 0 = 1 := by
        have hh := hconv0 0
        simpa using hh
      rw [h1, Finset.sum_singleton, h0]
      simp
    | succ n ih =>
      have hsplit : Tri (n + 2) = Tri (n + 1) ∪ Finset.antidiagonal (n + 1) := by
        ext x
        rw [Finset.mem_union, hTriMem, hTriMem, Finset.mem_antidiagonal]
        omega
      have hdisj : Disjoint (Tri (n + 1)) (Finset.antidiagonal (n + 1)) := by
        rw [Finset.disjoint_left]
        intro x hx hx2
        rw [hTriMem] at hx
        rw [Finset.mem_antidiagonal] at hx2
        omega
      rw [hsplit, Finset.sum_union hdisj, ih, hantidiag]
      simp
  -- the one-sided partial sums of the inversion filter and their noise expansions
  obtain ⟨S, hS⟩ : ∃ S : ℕ → Ω → ℝ, S = fun N ω =>
    ∑ j ∈ Finset.range N, π j * X (t - (j : ℕ)) ω := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ → Ω → ℝ, P = fun N M ω =>
    ∑ x ∈ Finset.range N ×ˢ Finset.range M,
      (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω := ⟨_, rfl⟩
  have hSmeas : ∀ N, Measurable (S N) := by
    intro N
    rw [hS]
    exact Finset.measurable_sum _ fun j _ => (hmeas _).const_mul _
  have hPmeas : ∀ N M, Measurable (P N M) := by
    intro N M
    rw [hP]
    exact Finset.measurable_sum _ fun x _ => (hεWN.measurable _).const_mul _
  -- for a fixed number of `π`-terms the noise expansion converges in `L²`
  have hSP : ∀ N : ℕ, Tendsto (fun M => eLpNorm (fun ω => S N ω - P N M ω) 2 μ)
      atTop (𝓝 0) := by
    intro N
    have hcomb := tendsto_eLpNorm_comb (μ := μ)
      (F := fun i : Fin N => X (t - (i : ℕ)))
      (G := fun (i : Fin N) (M : ℕ) ω =>
        ∑ l ∈ Finset.range M, ψc l * ε (t - (i : ℕ) - (l : ℕ)) ω)
      (fun i : Fin N => π i)
      (fun i M => (hmeas _).aestronglyMeasurable.sub
        (Finset.measurable_sum _ fun l _ => (hεWN.measurable _).const_mul _).aestronglyMeasurable)
      (fun i => hlin (t - (i : ℕ)))
    refine hcomb.congr fun M => congrArg (fun f => eLpNorm f 2 μ) (funext fun ω => ?_)
    simp only [hS, hP]
    rw [Finset.sum_product]
    congr 1
    · exact Fin.sum_univ_eq_sum_range (fun j => π j * X (t - (j : ℕ)) ω) N
    · rw [← Fin.sum_univ_eq_sum_range (fun j => ∑ l ∈ Finset.range M,
        (π j * ψc l) * ε (t - (j : ℕ) - (l : ℕ)) ω) N]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
  -- the coefficient mass outside the triangle
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℝ, E = fun N =>
    (∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|) - ∑ x ∈ Tri N, |π x.1| * |ψc x.2| := ⟨_, rfl⟩
  have hPε : ∀ N M : ℕ, N + 1 ≤ M →
      eLpNorm (fun ω => P (N + 1) M ω - ε t ω) 2 μ
        ≤ ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2) := by
    intro N M hNM
    obtain ⟨D, hD⟩ : ∃ D : Finset (ℕ × ℕ),
        D = (Finset.range (N + 1) ×ˢ Finset.range M) \ Tri (N + 1) := ⟨_, rfl⟩
    have hsub : Tri (N + 1) ⊆ Finset.range (N + 1) ×ˢ Finset.range M := by
      intro x hx
      rw [hTriMem] at hx
      simp only [Finset.mem_product, Finset.mem_range]
      omega
    have hdiff : (fun ω => P (N + 1) M ω - ε t ω)
        = fun ω => ∑ x ∈ D, (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω := by
      funext ω
      have hsd := Finset.sum_sdiff (f := fun x : ℕ × ℕ =>
        (π x.1 * ψc x.2) * ε (t - (x.1 : ℕ) - (x.2 : ℕ)) ω) hsub
      rw [hD]
      simp only [hP]
      rw [← hsd, hTriSum N ω]
      ring
    have hmass : ∑ x ∈ D, |π x.1 * ψc x.2| ≤ E (N + 1) := by
      have hdj : Disjoint D (Tri (N + 1)) := by
        rw [hD]; exact Finset.sdiff_disjoint
      have hunion := Finset.sum_union (f := fun x : ℕ × ℕ => |π x.1| * |ψc x.2|) hdj
      have hle : ∑ x ∈ D ∪ Tri (N + 1), |π x.1| * |ψc x.2|
          ≤ ∑' x : ℕ × ℕ, |π x.1| * |ψc x.2| :=
        hF.sum_le_tsum _ fun x _ => by positivity
      rw [hE]
      simp only [abs_mul]
      linarith
    rw [hdiff]
    refine (eLpNorm_noise_comb_le hεWN D (fun x => π x.1 * ψc x.2)
      (fun x => t - (x.1 : ℕ) - (x.2 : ℕ))).trans ?_
    -- (`mul_le_mul_left` is deprecated upstream; the ENNReal `gcongr` route needs the
    -- same side goal, so keep the explicit form)
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hmass) _
  -- the tail mass vanishes
  have hTriTendsto : Tendsto (fun N => ∑ x ∈ Tri N, |π x.1| * |ψc x.2|)
      atTop (𝓝 (∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|)) := by
    refine hF.hasSum.comp (tendsto_atTop_finset_of_monotone ?_ ?_)
    · intro m n hmn
      intro x hx
      rw [hTriMem] at hx ⊢
      omega
    · intro x
      exact ⟨x.1 + x.2 + 1, (hTriMem _ _).2 (by omega)⟩
  have hE0 : Tendsto E atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => ∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|) atTop
        (𝓝 (∑' x : ℕ × ℕ, |π x.1| * |ψc x.2|)) := tendsto_const_nhds
    rw [hE]
    simpa using hconst.sub hTriTendsto
  -- hence the `π`-partial sums converge to the innovation
  have hSε : ∀ N : ℕ, eLpNorm (fun ω => S (N + 1) ω - ε t ω) 2 μ
      ≤ ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2) := by
    intro N
    have hlim : Tendsto (fun M => eLpNorm (fun ω => S (N + 1) ω - P (N + 1) M ω) 2 μ
        + ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2)) atTop
        (𝓝 (ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2))) := by
      simpa using (hSP (N + 1)).add tendsto_const_nhds
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop (N + 1)] with M hM
    have hfun : (fun ω => S (N + 1) ω - ε t ω)
        = (fun ω => S (N + 1) ω - P (N + 1) M ω) + fun ω => P (N + 1) M ω - ε t ω := by
      funext ω
      simp only [Pi.add_apply]
      ring
    calc eLpNorm (fun ω => S (N + 1) ω - ε t ω) 2 μ
        ≤ eLpNorm (fun ω => S (N + 1) ω - P (N + 1) M ω) 2 μ
          + eLpNorm (fun ω => P (N + 1) M ω - ε t ω) 2 μ := by
          rw [hfun]
          exact eLpNorm_add_le ((hSmeas _).sub (hPmeas _ _)).aestronglyMeasurable
            ((hPmeas _ _).sub (hεWN.measurable t)).aestronglyMeasurable one_le_two
      _ ≤ _ := add_le_add le_rfl (hPε N M hM)
  have hStend : Tendsto (fun N => eLpNorm (fun ω => S N ω - ε t ω) 2 μ) atTop (𝓝 0) := by
    have hb : Tendsto (fun N : ℕ =>
        ENNReal.ofReal (E (N + 1)) * ENNReal.ofReal (Real.sqrt σ2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => ENNReal.ofReal (E (N + 1))) atTop (𝓝 0) := by
        have h2 := ENNReal.tendsto_ofReal (hE0.comp (tendsto_add_atTop_nat 1))
        simpa using h2
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inr ENNReal.ofReal_ne_top)
    have hshift : Tendsto (fun N => eLpNorm (fun ω => S (N + 1) ω - ε t ω) 2 μ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
        (fun N => zero_le) hSε
    exact (tendsto_add_atTop_iff_nat 1).1 hshift
  -- ... and the residual is that same limit
  have hrS : Tendsto (fun N => eLpNorm (fun ω => r t ω - S N ω) 2 μ) atTop (𝓝 0) := by
    simpa only [hS] using hres
  have hzero : eLpNorm (fun ω => r t ω - ε t ω) 2 μ = 0 := by
    have hlim : Tendsto (fun N => eLpNorm (fun ω => r t ω - S N ω) 2 μ
        + eLpNorm (fun ω => S N ω - ε t ω) 2 μ) atTop (𝓝 0) := by
      simpa using hrS.add hStend
    refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun N => ?_)) (zero_le)
    have hfun : (fun ω => r t ω - ε t ω)
        = (fun ω => r t ω - S N ω) + fun ω => S N ω - ε t ω := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hfun]
    exact eLpNorm_add_le ((hrmeas t).sub (hSmeas N)).aestronglyMeasurable
      ((hSmeas N).sub (hεWN.measurable t)).aestronglyMeasurable one_le_two
  have hae := (eLpNorm_eq_zero_iff
    ((hrmeas t).sub (hεWN.measurable t)).aestronglyMeasurable two_ne_zero).1 hzero
  filter_upwards [hae] with ω hω
  have hω' : r t ω - ε t ω = 0 := hω
  linarith

section ScoreAux

omit [MeasurableSpace Ω] in
private lemma comap_le_sigmaLT {Z : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    MeasurableSpace.comap (Z s) inferInstance ≤ sigmaLT Z t :=
  le_iSup₂ (f := fun s (_ : s ∈ Set.Iio t) => MeasurableSpace.comap (Z s) inferInstance) s hst

private lemma sigmaLT_le {Z : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (Z t)) (t : ℤ) :
    sigmaLT Z t ≤ (inferInstance : MeasurableSpace Ω) :=
  iSup₂_le fun _ _ => (hm _).comap_le

omit [MeasurableSpace Ω] in
/-- Past values are measurable for the strict past. -/
private lemma measurable_sigmaLT {Z : ℤ → Ω → ℝ} {s t : ℤ} (hst : s < t) :
    Measurable[sigmaLT Z t] (Z s) :=
  (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (Z s) inferInstance))).mono
    (comap_le_sigmaLT hst) le_rfl

/-- **One-vs-past independence of i.i.d. noise**: `ε_t` is independent of
`σ(ε_s : s < t)` (the `Stationarity/ARCH.lean` pull, replayed here).

**Made public 2026-08-09** (wave `ts/s1b-arma-finish`), as the cross-file scope blocker
recorded at what was then `MLEAsymptotics.hannanScore_brownInputs` (since removed): inputs
(1) and (3) of that debt both consumed this independence, and it was not citeable while
`private`. -/
lemma indep_noise_sigmaLT {ε : ℤ → Ω → ℝ} (hm : ∀ t, Measurable (ε t))
    (hi : iIndepFun ε μ) (t : ℤ) :
    Indep (MeasurableSpace.comap (ε t) inferInstance) (sigmaLT ε t) μ := by
  have hdisj : Disjoint ({t} : Set ℤ) (Set.Iio t) :=
    Set.disjoint_singleton_left.2 (by simp)
  have := indep_iSup_of_disjoint
    (m := fun s : ℤ => MeasurableSpace.comap (ε s) inferInstance)
    (fun s => (hm s).comap_le) hi hdisj
  simpa using! this

/-- `E[ε_t | 𝓕_{t−1}] = 0`: independence of the past plus the vanishing mean. -/
private lemma condExp_noise_eq_zero [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) :
    μ[ε t | sigmaLT ε t] =ᵐ[μ] 0 := by
  have hle : sigmaLT ε t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le hiid.measurable t
  have hmean : ∫ ω, ε t ω ∂μ = 0 := by
    rw [(hiid.identDistrib t 0).integral_eq, hiid.integral_eq_zero]
  have h := condExp_indep_eq (hiid.measurable t).comap_le hle
    (Measurable.stronglyMeasurable
      (Measurable.of_comap_le (le_refl (MeasurableSpace.comap (ε t) inferInstance))))
    (indep_noise_sigmaLT hiid.measurable hiid.iIndep t)
  filter_upwards [h] with ω hω
  rw [hω, hmean]
  rfl

/-- **The martingale-difference brick**: if `W` is the `L²` limit of a sequence of
`σ(ε_s : s < t)`-measurable variables, then `E[ε_t · W | σ(ε_s : s < t)] = 0`. The
`L²` approximants are only *approximately* past-measurable, so the pull-out is applied
to them and the limit is taken in `L¹` (no measurable version of `W` is needed). -/
private lemma condExp_noise_mul_eq_zero [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hiid : IsIIDNoise ε σ2 μ) (t : ℤ) {W : Ω → ℝ} (hW : MemLp W 2 μ) {WN : ℕ → Ω → ℝ}
    (hWNmeas : ∀ N, StronglyMeasurable[sigmaLT ε t] (WN N))
    (hWNmem : ∀ N, MemLp (WN N) 2 μ)
    (hconv : Tendsto (fun N => eLpNorm (fun ω => W ω - WN N ω) 2 μ) atTop (𝓝 0)) :
    μ[fun ω => ε t ω * W ω | sigmaLT ε t] =ᵐ[μ] 0 := by
  have hεL2 : MemLp (ε t) 2 μ := ((hiid.identDistrib t 0).memLp_iff).2 hiid.memLp
  have hεint : Integrable (ε t) μ := hεL2.integrable one_le_two
  have hprod : ∀ g : Ω → ℝ, MemLp g 2 μ → Integrable (ε t * g) μ :=
    fun g hg => hεL2.integrable_mul hg
  have hlam : (fun ω => ε t ω * W ω) = ε t * W := rfl
  rw [hlam]
  -- the pull-out kills every approximant
  have hzeroN : ∀ N, μ[ε t * WN N | sigmaLT ε t] =ᵐ[μ] 0 := by
    intro N
    have hpull : μ[ε t * WN N | sigmaLT ε t] =ᵐ[μ] μ[ε t | sigmaLT ε t] * WN N :=
      condExp_mul_of_stronglyMeasurable_right (hWNmeas N) (hprod _ (hWNmem N)) hεint
    filter_upwards [hpull, condExp_noise_eq_zero hiid t] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
    simp
  -- the difference is small in `L¹`
  have hsplit : ∀ N, μ[ε t * W | sigmaLT ε t]
      =ᵐ[μ] μ[ε t * (W - WN N) | sigmaLT ε t] := by
    intro N
    have hadd : μ[ε t * WN N + ε t * (W - WN N) | sigmaLT ε t]
        =ᵐ[μ] μ[ε t * WN N | sigmaLT ε t] + μ[ε t * (W - WN N) | sigmaLT ε t] :=
      condExp_add (hprod _ (hWNmem N)) (hprod _ (hW.sub (hWNmem N))) _
    have hfun : (ε t * WN N + ε t * (W - WN N)) = ε t * W := by
      funext ω
      simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
      ring
    rw [hfun] at hadd
    filter_upwards [hadd, hzeroN N] with ω h1 h2
    rw [h1, Pi.add_apply, h2]
    simp
  -- ... and the `L¹` norm of the conditional expectation is dominated by it
  have hbound : ∀ N, eLpNorm (μ[ε t * W | sigmaLT ε t]) 1 μ
      ≤ eLpNorm (ε t) 2 μ * eLpNorm (fun ω => W ω - WN N ω) 2 μ := by
    intro N
    rw [eLpNorm_congr_ae (hsplit N)]
    refine (eLpNorm_one_condExp_le_eLpNorm _).trans ?_
    have hsmul : (ε t * (W - WN N)) = (ε t) • (fun ω => W ω - WN N ω) := by
      funext ω
      simp [smul_eq_mul]
    rw [hsmul]
    exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
      (hpqr := ENNReal.HolderConjugate.instTwoTwo)
      ((hW.sub (hWNmem N)).aestronglyMeasurable) hεL2.aestronglyMeasurable
  have hlim : Tendsto (fun N => eLpNorm (ε t) 2 μ * eLpNorm (fun ω => W ω - WN N ω) 2 μ)
      atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := eLpNorm (ε t) 2 μ) hconv (Or.inr hεL2.2.ne)
    simpa using this
  have hzero : eLpNorm (μ[ε t * W | sigmaLT ε t]) 1 μ = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) (zero_le)
  -- (the `mono` keeps the elaborator from unifying `sigmaLT ε t` with the ambient σ-algebra)
  have hle : sigmaLT ε t ≤ (inferInstance : MeasurableSpace Ω) := sigmaLT_le hiid.measurable t
  exact (eLpNorm_eq_zero_iff
    (stronglyMeasurable_condExp.mono hle).aestronglyMeasurable one_ne_zero).1 hzero

end ScoreAux

/-- **The score is a martingale-difference sequence at the truth** (the Brown-CLT
input of the Hannan program): with `U/V` the auxiliary filtered processes of the data
(`U_t = Σ ψᵇ_j ε_{t−j}` etc. realized through the residual machinery), the score
coordinates `s_t = ε_t · Z_{t}` satisfy `E[s_t | σ(ε_s, s < t)] = 0`. Stated for the
generic coordinate combination `c`: the combined score is an MDS against the noise
past. -/
theorem armaScore_condexp_zero [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε U V : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ)
    (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the auxiliary AR processes driven by the innovations; FY §3.3.2
    (hU : IsLinearProcessOf (armaPsi b (Fin.elim0 : Fin 0 → ℝ)) U ε μ)
    (hV : IsLinearProcessOf (armaPsi (fun j => -a j) (Fin.elim0 : Fin 0 → ℝ)) V ε μ)
    (hUmeas : ∀ t, Measurable (U t)) (hVmeas : ∀ t, Measurable (V t))
    (c : Fin p ⊕ Fin q → ℝ) (t : ℤ) :
    μ[fun ω => ε t ω *
        ((∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω) +
          ∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
      | sigmaLT ε t] =ᵐ[μ] 0 := by
  classical
  have hε : IsWhiteNoise ε σ2 μ := h.whiteNoise
  have hψb : Summable fun n => |armaPsi b (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) hB.1
  have hψa : Summable fun n => |armaPsi (fun j => -a j) (Fin.elim0 : Fin 0 → ℝ) n| :=
    summable_abs_armaPsi (Fin.elim0 : Fin 0 → ℝ) (noRootClosedDisc_neg hB)
  have hUmem : ∀ s, MemLp (U s) 2 μ := hU.memLp hψb hε hUmeas
  have hVmem : ∀ s, MemLp (V s) 2 μ := hV.memLp hψa hε hVmeas
  have hlt : ∀ k n : ℕ, t - 1 - (k : ℕ) - (n : ℕ) < t := by
    intro k n
    have h1 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
    have h2 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    omega
  refine condExp_noise_mul_eq_zero hiid t ?_
    (WN := fun N ω =>
      (∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
          armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
        + ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
            armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
              * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω) ?_ ?_ ?_
  · exact (memLp_finset_sum _ fun i _ => (hUmem _).const_mul _).add
      (memLp_finset_sum _ fun j _ => (hVmem _).const_mul _)
  · intro N
    refine Measurable.stronglyMeasurable (Measurable.add ?_ ?_) <;>
      exact Finset.measurable_sum _ fun i _ => measurable_const.mul
        (Finset.measurable_sum _ fun n _ => measurable_const.mul (measurable_sigmaLT (hlt _ _)))
  · intro N
    exact (memLp_finset_sum _ fun i _ =>
        (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _).add
      (memLp_finset_sum _ fun j _ =>
        (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _)
  · -- the two blocks converge separately
    have hUconv := tendsto_eLpNorm_comb (μ := μ)
      (F := fun i : Fin p => U (t - 1 - (i : ℕ)))
      (G := fun (i : Fin p) (N : ℕ) ω => ∑ n ∈ Finset.range N,
        armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
      (fun i => c (.inl i))
      (fun i N => (hUmeas _).aestronglyMeasurable.sub
        (Finset.measurable_sum _ fun n _ => (hε.measurable _).const_mul _).aestronglyMeasurable)
      (fun i => hU (t - 1 - (i : ℕ)))
    have hVconv := tendsto_eLpNorm_comb (μ := μ)
      (F := fun j : Fin q => V (t - 1 - (j : ℕ)))
      (G := fun (j : Fin q) (N : ℕ) ω => ∑ n ∈ Finset.range N,
        armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
          * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω)
      (fun j => c (.inr j))
      (fun j N => (hVmeas _).aestronglyMeasurable.sub
        (Finset.measurable_sum _ fun n _ => (hε.measurable _).const_mul _).aestronglyMeasurable)
      (fun j => hV (t - 1 - (j : ℕ)))
    have hbd : ∀ N : ℕ,
        eLpNorm (fun ω =>
          ((∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
              + ∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
            - ((∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                  armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
                + ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                    armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                      * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω)) 2 μ
        ≤ eLpNorm (fun ω => (∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
              - ∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                  armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω) 2 μ
          + eLpNorm (fun ω => (∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
              - ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                  armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                    * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω) 2 μ := by
      intro N
      have hfun : (fun ω =>
          ((∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
              + ∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
            - ((∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                  armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
                + ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                    armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                      * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω))
          = (fun ω => (∑ i : Fin p, c (.inl i) * U (t - 1 - (i : ℕ)) ω)
                - ∑ i : Fin p, c (.inl i) * ∑ n ∈ Finset.range N,
                    armaPsi b (Fin.elim0 : Fin 0 → ℝ) n * ε (t - 1 - (i : ℕ) - (n : ℕ)) ω)
            + (fun ω => (∑ j : Fin q, c (.inr j) * V (t - 1 - (j : ℕ)) ω)
                - ∑ j : Fin q, c (.inr j) * ∑ n ∈ Finset.range N,
                    armaPsi (fun j' => -a j') (Fin.elim0 : Fin 0 → ℝ) n
                      * ε (t - 1 - (j : ℕ) - (n : ℕ)) ω) := by
        funext ω; simp only [Pi.add_apply]; ring
      rw [hfun]
      refine eLpNorm_add_le ?_ ?_ one_le_two
      · exact ((memLp_finset_sum _ fun i _ => (hUmem _).const_mul _).sub
          (memLp_finset_sum _ fun i _ =>
            (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _)).1
      · exact ((memLp_finset_sum _ fun j _ => (hVmem _).const_mul _).sub
          (memLp_finset_sum _ fun j _ =>
            (memLp_finset_sum _ fun n _ => (hε.memLp _).const_mul _).const_mul _)).1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun N => zero_le) hbd
    simpa using hUconv.add hVconv

end Process

end StatLean.TimeSeries
