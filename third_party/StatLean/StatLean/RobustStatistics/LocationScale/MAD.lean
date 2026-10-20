module
public import StatLean.RobustStatistics.LocationScale.Median
public import StatLean.RobustStatistics.Core.Equivariance

@[expose] public section

/-!
# The median absolute deviation (MAD)

The MAD is the robust dispersion estimator obtained by centering at the median and taking
the median of the absolute deviations (`MMY §2.6`, eq. (2.60)):

$$\operatorname{MAD}(x) = \operatorname{Med}_i\,|x_i - \operatorname{Med}(x)|.$$

Its basic properties — nonnegativity, location invariance, absolute scale equivariance,
vanishing on constant samples — make it the canonical high-breakdown companion dispersion
for M-estimation with previously computed scale (`MMY §2.7.1`).

**Scope (odd `n` for scale equivariance).** With the low-median convention the identity
`Med(cx) = c·Med(x)` for negative `c` needs the middle index to be reversal-invariant,
which holds exactly for odd `n`; the scale-equivariance and dispersion statements are
therefore given for odd `n`. Location invariance holds for every `n`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §2.6 (eq.
(2.58), (2.60), (2.63)), §2.7.1.

**Bibliographic comments.** The median absolute deviation was advocated as *the* robust
scale estimate by F. R. Hampel ("The influence curve and its role in robust estimation,"
*J. Amer. Statist. Assoc.* **69** (1974), 383–393, where it is the "median deviation");
its normalization and higher-efficiency alternatives are P. J. Rousseeuw and C. Croux,
"Alternatives to the median absolute deviation," *J. Amer. Statist. Assoc.* **88** (1993),
1273–1283.
-/

namespace StatLean.RobustStatistics

variable {n : ℕ}

/-- The **sample MAD** (`MMY §2.6`, eq. (2.60)): the median of the absolute deviations
from the median. Junk value `0` when `n = 0`. -/
noncomputable def sampleMAD (x : Fin n → ℝ) : ℝ :=
  sampleMedian fun i => |x i - sampleMedian x|

/-- The MAD is nonnegative. -/
theorem sampleMAD_nonneg (x : Fin n → ℝ) : 0 ≤ sampleMAD x := by
  by_cases hn : n = 0
  · subst hn; simp [sampleMAD, sampleMedian]
  · rw [sampleMAD, sampleMedian_eq_orderStat hn]
    exact orderStat_nonneg _ (fun i => abs_nonneg _) _

/-- **The MAD is location invariant** (`MMY` eq. (2.58), first condition). -/
theorem sampleMAD_add_const (x : Fin n → ℝ) (a : ℝ) :
    sampleMAD (x + a • (1 : Fin n → ℝ)) = sampleMAD x := by
  by_cases hn : n = 0
  · subst hn; simp [sampleMAD, sampleMedian]
  -- The median shifts with the data, so the absolute deviations are unchanged.
  have hmed : sampleMedian (x + a • (1 : Fin n → ℝ)) = sampleMedian x + a :=
    sampleMedian_locEquivariant hn a x
  have hdev : (fun i => |(x + a • (1 : Fin n → ℝ)) i - sampleMedian (x + a • (1 : Fin n → ℝ))|)
      = fun i => |x i - sampleMedian x| := by
    funext i
    rw [hmed]
    have hxi : (x + a • (1 : Fin n → ℝ)) i = x i + a := by simp
    rw [hxi]
    congr 1
    ring
  rw [sampleMAD, sampleMAD, hdev]

/-- **The MAD is absolutely scale equivariant for odd `n`** (`MMY` eq. (2.58), second
condition): `MAD(cx) = |c|·MAD(x)`. -/
theorem sampleMAD_const_mul {k : ℕ} (hn : n = 2 * k + 1) (c : ℝ) (x : Fin n → ℝ) :
    sampleMAD (fun i => c * x i) = |c| * sampleMAD x := by
  -- `Med(cx) = c·Med(x)` (odd `n`), so the deviations get multiplied by `|c|`.
  have hmed : sampleMedian (fun i => c * x i) = c * sampleMedian x :=
    sampleMedian_const_mul_of_odd hn c x
  have hdev : (fun i => |c * x i - sampleMedian fun i => c * x i|)
      = fun i => |c| * |x i - sampleMedian x| := by
    funext i
    rw [hmed, ← mul_sub, abs_mul]
  simp only [sampleMAD]
  rw [hdev, sampleMedian_const_mul_of_nonneg (abs_nonneg c)]

/-- **The MAD is a dispersion estimator for odd `n`** (`MMY` eq. (2.58)). -/
theorem sampleMAD_isDispersionEstimator {k : ℕ} (hn : n = 2 * k + 1) :
    IsDispersionEstimator (sampleMAD (n := n)) := by
  refine ⟨fun a x => sampleMAD_add_const x a, fun c x => ?_⟩
  have hsmul : (c • x) = fun i => c * x i := by funext i; simp
  rw [hsmul, sampleMAD_const_mul hn]

/-- The MAD of a constant sample vanishes (`MMY §2.7.1`, the degenerate case handled
there by the convention `μ̂ = Med(x)`). -/
theorem sampleMAD_const (a : ℝ) : sampleMAD (fun _ : Fin n => a) = 0 := by
  by_cases hn : n = 0
  · subst hn; simp [sampleMAD, sampleMedian]
  -- Both medians collapse: the deviations from the median `a` are all `|a - a| = 0`.
  simp only [sampleMAD, sampleMedian_const hn]
  simp

end StatLean.RobustStatistics
