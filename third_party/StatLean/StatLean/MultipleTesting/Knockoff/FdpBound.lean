module
public import StatLean.MultipleTesting.FDP.Defs
public import StatLean.MultipleTesting.Knockoff.Procedure

@[expose] public section

/-!
# Knock-off deterministic FDP bound

Let $W_1,\dots,W_d$ be knock-off scores for testing the hypotheses $\{H_{0j}\}_{j=1}^d$, and let
$\alpha > 0$ be the target FDR level. For a threshold $t$ write
$S^+(t) = \{j : W_j \ge t\}$ for the rejected set and
$S^-(t) = \{j : W_j \le -t\}$ for its negative counterpart, and let
$V_+(t) = \#\{j \in H_0 : W_j \ge t\}$ and $V_-(t) = \#\{j \in H_0 : W_j \le -t\}$ count the
null indices on each side. The conservative FDP estimate is
$\widehat{\mathrm{FDP}}(t) = \bigl(1 + \#S^-(t)\bigr)\big/\bigl(\#S^+(t) \vee 1\bigr)$,
and the knock-off threshold is $t^* = \arg\min_t \{\, \widehat{\mathrm{FDP}}(t) \le \alpha \,\}$,
with the procedure rejecting $H_{0j}$ exactly when $j \in S^+(t^*)$.

This file proves the **first display** in the proof of FDR control: the purely deterministic
(per-sample, counting-and-algebra) bound
$$\mathrm{FDP}(t^*) \;=\; \frac{V_+(t^*)}{\#S^+(t^*) \vee 1}
  \;\le\; \alpha \cdot \frac{V_+(t^*)}{1 + V_-(t^*)}.$$
It is a pointwise inequality holding for every outcome $\omega$ — no probabilistic hypotheses are
needed; the subsequent (super)martingale / optional-stopping argument that turns this into the
FDR bound $\mathbb{E}[\mathrm{FDP}(t^*)] \le \alpha$ is **not** part of this result.

The constant matches the book exactly (target level $\alpha$, denominator $1 + V_-(t^*)$ from the
"knock-off+" estimate with the extra $+1$).

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 21 (Knock-Off), §21.3, Theorem 21.2 (Knock-Off), first display
of the proof. Dual citation: E. J. Candès, *STAT 300C:
Theory of Statistics*, Lecture Notes, Stanford University, 2023, Lecture 11, equation (11.1) and
the FDP chain in the proof deferred to §11.5.

**Proof formalization notes.** The bound is purely deterministic (counting + algebra), proved by
`fdp_le_core`: $V \le |S|$ (here `Vplus`/`Vminus` are subsets of the rejected/negative sets, so
`Finset.card_le_card Finset.inter_subset_left` gives $V_- \le \#S^-$), the threshold property
$\widehat{\mathrm{FDP}}(t^*) \le \alpha$ extracted from `tStar`'s defining `min'` over the filtered
candidate set, and the definitional identity
$\mathrm{FDP} = V_+(t^*)/(\#S^+(t^*) \vee 1)$ for the knock-off rejection set. The empty-candidate
branch (no threshold meets the level, so the rejection set is empty) gives $\mathrm{FDP} = 0$,
bounded by the non-negative right-hand side.

**Bibliographic comments.** The knock-off filter and this deterministic FDP step originate with
R. F. Barber and E. J. Candès, "Controlling the false discovery rate via knockoffs," *Annals of
Statistics* 43(5):2055–2085, 2015 — the inequality here is the opening identity of their FDR-control
proof (Theorem 1; the "+1" in the denominator is the knockoff+ variant). The model-X generalization
that the Candès lecture notes follow is E. Candès, Y. Fan, L. Janson, and J. Lv, "Panning for gold:
'model-X' knockoffs for high dimensional controlled variable selection," *Journal of the Royal
Statistical Society: Series B* 80(3):551–577, 2018. The underlying conservative SeqStep estimate of
the FDP is due to R. F. Barber and E. J. Candès, "A knockoff filter for high-dimensional selective
inference," *Annals of Statistics* 47(5):2504–2537, 2019.
-/

open MeasureTheory

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ}

/-- Core algebraic inequality: `vp/max(sp,1) ≤ α·vp/(1+vm)` given `(sm+1)/max(sp,1) ≤ α`,
`vm ≤ sm`, `α > 0`. -/
private lemma fdp_le_core (α : ℝ) (hα : 0 < α) (vp sp vm sm : ℕ) (hvm : vm ≤ sm)
    (hfdphat : ((sm : ℝ) + 1) / max (sp : ℝ) 1 ≤ α) :
    (vp : ℝ) / max (sp : ℝ) 1 ≤ α * (vp : ℝ) / (1 + (vm : ℝ)) := by
  have hM : (0 : ℝ) < max (↑sp) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hvm1 : (0 : ℝ) < 1 + (↑vm : ℝ) := by positivity
  rcases Nat.eq_zero_or_pos vp with rfl | hvp0
  · simp
  · have hkey : (1 : ℝ) + ↑vm ≤ α * max (↑sp) 1 := by
      have h1 : (↑sm : ℝ) + 1 ≤ α * max (↑sp) 1 := (div_le_iff₀ hM).mp hfdphat
      have h2 : (↑vm : ℝ) ≤ ↑sm := Nat.cast_le.mpr hvm
      linarith
    rw [div_le_div_iff₀ hM hvm1]
    have hvp_r : (0 : ℝ) ≤ ↑vp := Nat.cast_nonneg _
    have key : (↑vp : ℝ) * (1 + ↑vm) ≤ ↑vp * (α * max (↑sp) 1) :=
      mul_le_mul_of_nonneg_left hkey hvp_r
    linarith [show (↑vp : ℝ) * (α * max (↑sp : ℝ) 1) = α * ↑vp * max (↑sp : ℝ) 1 from by ring]

/-- Deterministic FDP bound (Lu-BDA Ch. 21 (Knock-Off) §21.3, Theorem 21.2 (Knock-Off), first display of the proof):
`FDP(t*) ≤ α · V₊(t*)/(1 + V₋(t*))`.
**Reference.** Lu-BDA Ch. 21 (Knock-Off) §21.3, Theorem 21.2 (Knock-Off), first display of the proof;
Candès STAT 300C Lecture 11, eq. (11.1). -/
theorem knockoff_fdp_le (α : ℝ) (hα : 0 < α) (W : Fin d → Ω → ℝ) (H₀ : Finset (Fin d)) (ω : Ω) :
    FDP H₀ (knockoffRejects W α) ω
      ≤ α * (Vplus W H₀ (tStar W α ω) ω : ℝ) / (1 + (Vminus W H₀ (tStar W α ω) ω : ℝ)) := by
  simp only [FDP, numFalseRejections, numRejections, knockoffRejects, tStar, Vplus, Vminus]
  split_ifs with h
  · -- Nonempty: t* = cands.min' h; FDPhat(t*) ≤ α from filter membership
    have hfdphat : FDPhat W
        ((Finset.univ.image (fun j => |W j ω|)).filter (fun t => FDPhat W t ω ≤ α) |>.min' h) ω ≤ α :=
      (Finset.mem_filter.mp (Finset.min'_mem _ h)).2
    simp only [FDPhat] at hfdphat
    exact fdp_le_core α hα _ _ _ _ (Finset.card_le_card Finset.inter_subset_left) hfdphat
  · -- Empty: knockoffRejects = ∅, FDP = 0 ≤ nonneg RHS
    simp only [Finset.empty_inter, Finset.card_empty, Nat.cast_zero, zero_div]
    exact div_nonneg (mul_nonneg hα.le (Nat.cast_nonneg _)) (by positivity)

end StatLean.MultipleTesting
