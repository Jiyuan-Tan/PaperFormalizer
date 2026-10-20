module
public import StatLean.HypothesisTesting.Randomization.PairCLT

@[expose] public section

/-!
# A Slutsky theorem for randomization distributions

Randomization distributions are usually built from a statistic that is itself a rescaled
and recentred version of a simpler one — studentization being the canonical example. This
file supplies the Slutsky-type transfer: if the base statistic satisfies the joint
asymptotic-independence condition, and the random scaling and shift stabilize at
constants, then the randomization distribution of the affine combination converges to the
law of the correspondingly transformed limit.

Given statistic sequences $T_n$, $A_n$, $B_n$, write
$$ \hat R_n^{AT+B}(t) \;=\; |\mathbf{G}_n|^{-1} \sum_{g \in \mathbf{G}_n}
   \mathbf{1}\bigl\{A_n(gX^n)\,T_n(gX^n) + B_n(gX^n) \le t\bigr\} $$
for the randomization distribution of the transformed statistic. If
$(T_n(G_nX^n), T_n(G_n'X^n)) \xrightarrow{d} (T, T')$ with $T, T'$ independent and
$R$-distributed, and if $A_n(G_nX^n) \xrightarrow{P} a$, $B_n(G_nX^n) \xrightarrow{P} b$,
then
$$ \hat R_n^{AT+B}(t) \;\xrightarrow{P}\; R^{aT+b}(t) $$
at every continuity point of the law $R^{aT+b}$ of $aT + b$.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 17 (Permutation and
Randomization Tests), §17.3 (Two-Sample Permutation Tests), Theorem 17.3.2 (a Slutsky theorem
for randomization distributions). (`TSH4 §17.3 Thm 17.3.2`.)

**Proof formalization notes.**
* *The exact requirement on the random scalings.* No invariance of $A_n$ or $B_n$ under
  the group is assumed — this is worth stating plainly, because it is the natural guess
  and it is not what the hypothesis says. What is required is that the scalings converge
  in probability **when evaluated at the randomized data** $G_nX^n$, with $G_n$ uniform on
  the group and independent of $X^n$ — not at $X^n$ itself. Since the group is finite and
  $G_n$ is uniform, that is the mixture statement
  $|\mathbf{G}_n|^{-1}\sum_g P_n\{|A_n(g\cdot x) - a| \ge \varepsilon\} \to 0$, which is
  the definition of `TendstoInProbRandomized`. In the studentized application the scaling
  is a pooled sample variance, which is *not* invariant under the group; what is true, and
  what the hypothesis captures, is that it converges in probability under a random
  relabelling.
* Correspondingly, the randomization distribution being transformed evaluates $A_n$ and
  $B_n$ at $gX^n$ too, matching the display above; the statistic whose randomization
  distribution is taken is the pointwise combination `fun y => A n y * T n y + B n y`.
* The limit law is written as the pushforward `R.map (fun u => a * u + b)`, i.e. the law of
  $aT + b$.
* *A caveat on the inversion formula.* The classical parenthetical
  $R^{aT+b}(t) = R^{T}((t-b)/a)$ "for $a \ne 0$" is correct only for $a > 0$: for $a < 0$
  the affine map reverses order and the identity picks up a reflection,
  $P\{aT + b \le t\} = 1 - P\{T < (t-b)/a\}$, which differs from
  $R^{T}((t-b)/a)$ unless $R^{T}$ is continuous there. `cdf_map_affine` is therefore stated
  for `0 < a` only; that is the case every application needs (scalings are positive).
* The setting is the same triangular array as `Randomization/Asymptotics`, whose
  `TendstoInProbTriangular` and `randPairLaw` are reused verbatim.

**Bibliographic comments.** The transfer principle for randomization distributions under
random rescaling, and its use to justify studentized permutation tests, is due to
A. Janssen ("Studentized permutation tests for non-i.i.d. hypotheses and the generalized
Behrens–Fisher problem," *Statist. Probab. Lett.* **36** (1997), 9–21) and was developed
into a general theory by E. Chung and J. P. Romano ("Exact and asymptotically robust
permutation tests," *Ann. Statist.* **41** (2013), 484–507), building on
J. P. Romano ("Bootstrap and randomization tests of some nonparametric hypotheses," *Ann.
Statist.* **17** (1989), 141–159; "On the behavior of randomization tests without a group
invariance assumption," *J. Amer. Statist. Assoc.* **85** (1990), 686–692) and on the
large-sample framework of W. Hoeffding ("The large-sample power of tests based on
permutations of observations," *Ann. Math. Statist.* **23** (1952), 169–192).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)

/-- **Convergence in probability at randomized data.** `A n` evaluated at `g • x`, with
`g` uniform on the finite group and independent of the data, converges in probability to
`a`. Written out as the mixture over the group, this is
`|Gₙ|⁻¹ ∑_g Pₙ{|Aₙ(g·x) − a| ≥ ε} → 0` for every `ε > 0`.

Note what this does **not** say: `A n` is not assumed invariant under the group. -/
def TendstoInProbRandomized {𝓨 : ℕ → Type*} [∀ n, MeasurableSpace (𝓨 n)]
    (G : ℕ → Type*) [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓨 n)]
    (P : ∀ n, Measure (𝓨 n)) (A : ∀ n, 𝓨 n → ℝ) (a : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), Tendsto
    (fun n => (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, (P n).real {x | ε ≤ |A n (g • x) - a|}) atTop (𝓝 0)

/-- The c.d.f. of an affine image, for a **positive** scaling:
`R^{aT+b}(t) = R^{T}((t − b)/a)`. See the file notes for why `a < 0` is excluded rather
than folded in. -/
lemma cdf_map_affine (R : Measure ℝ) [IsProbabilityMeasure R] {a : ℝ}
    -- USER-INPUT: positive scaling; the order-preserving case
    (ha : 0 < a) (b t : ℝ) :
    cdf (R.map (fun u => a * u + b)) t = cdf R ((t - b) / a) := by
  have hf : Measurable (fun u : ℝ => a * u + b) := by fun_prop
  have : IsProbabilityMeasure (R.map (fun u => a * u + b)) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  rw [cdf_eq_real, cdf_eq_real, Measure.real, Measure.real,
    Measure.map_apply hf measurableSet_Iic]
  congr 2
  ext u
  simp only [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ ha]
  constructor
  · intro h; linarith
  · intro h; linarith

section Slutsky

variable {𝓧 : ℕ → Type*} [∀ n, MeasurableSpace (𝓧 n)]
  {G : ℕ → Type*} [∀ n, Group (G n)] [∀ n, Fintype (G n)] [∀ n, MulAction (G n) (𝓧 n)]

/-- **Slutsky's theorem for randomization distributions.** If the base statistic satisfies
the joint asymptotic-independence condition with limit law `R`, and the random scaling and
shift converge in probability *at the randomized data* to constants `a` and `b`, then the
randomization distribution of `AₙTₙ + Bₙ` converges in probability to the law of `aT + b`
at each of its continuity points. -/
theorem randDist_affine_tendstoInProb (P : ∀ n, Measure (𝓧 n))
    [∀ n, IsProbabilityMeasure (P n)] (T A B : ∀ n, 𝓧 n → ℝ) (R : Measure ℝ)
    [IsProbabilityMeasure R] {a b t : ℝ}
    -- LEAN-ONLY (regularity amendment): the three statistics and the group action are
    -- measurable. The frozen signature omitted these; they are *not* removable. `randPairLaw`
    -- is `Measure.map` of the statistic, and `Measure.map` of a non-measurable map is the zero
    -- measure, so for a non-measurable `Aₙ` the conclusion's randomization distribution and the
    -- hypothesis `hjoint` would be computed with incompatible junk conventions. The sibling
    -- engines `randDist_tendstoInProb_cdf` and `randQuantile_tendstoInProb` in
    -- `Randomization/Asymptotics` carry exactly the same two hypotheses for the same reason.
    (hTmeas : ∀ n, Measurable (T n)) (hAmeas : ∀ n, Measurable (A n))
    (hBmeas : ∀ n, Measurable (B n))
    (hsmul : ∀ (n : ℕ) (g : G n), Measurable (fun x : 𝓧 n => g • x))
    -- USER-INPUT: joint weak convergence of the base statistic at two independent uniform
    -- group elements, to a product law (asymptotic independence)
    (hjoint : WeakConverges (fun n => randPairLaw (G n) (T n) (P n)) (R.prod R))
    -- USER-INPUT: the random scaling converges in probability **at randomized data** to
    -- the constant `a`; no group invariance of `A` is assumed
    (hA : TendstoInProbRandomized G P A a)
    -- USER-INPUT: the random shift converges in probability **at randomized data** to the
    -- constant `b`; no group invariance of `B` is assumed
    (hB : TendstoInProbRandomized G P B b)
    -- USER-INPUT: `t` is a continuity point of the limit law of `aT + b`
    (hcont : ContinuousAt (cdf (R.map (fun u => a * u + b))) t) :
    TendstoInProbTriangular P
      (fun n x => randDist (G n) (fun y => A n y * T n y + B n y) x t)
      (cdf (R.map (fun u => a * u + b)) t) := by
  classical
  set φ : ℝ → ℝ := fun u => a * u + b with hφdef
  have hφmeas : Measurable φ := by fun_prop
  have hφcont : Continuous φ := by fun_prop
  haveI : IsProbabilityMeasure (R.map φ) := Measure.isProbabilityMeasure_map hφmeas.aemeasurable
  -- `L` is the *deterministic* affine image, `S` the actual (randomly rescaled) statistic.
  set L : ∀ n, 𝓧 n → ℝ := fun n x => φ (T n x) with hLdef
  set S : ∀ n, 𝓧 n → ℝ := fun n x => A n x * T n x + B n x with hSdef
  have hLmeas : ∀ n, Measurable (L n) := fun n => hφmeas.comp (hTmeas n)
  have hSmeas : ∀ n, Measurable (S n) := fun n => ((hAmeas n).mul (hTmeas n)).add (hBmeas n)
  haveI hprob : ∀ n, IsProbabilityMeasure (randPairLaw (G n) (T n) (P n)) := fun n =>
    isProbabilityMeasure_randPairLaw (G n) (P n) (T n) (hTmeas n) (hsmul n)
  -- Step 1: the deterministic affine image already has the affine-image randomized limit.
  have hconvL : WeakConverges (fun n => randPairLaw (G n) (L n) (P n))
      ((R.map φ).prod (R.map φ)) := by
    have hmapped := hjoint.map (f := Prod.map φ φ) (hφcont.prodMap hφcont)
      (hφmeas.prodMap hφmeas)
    rw [← Measure.map_prod_map R R hφmeas hφmeas] at hmapped
    have heq : ∀ n, randPairLaw (G n) (L n) (P n)
        = (randPairLaw (G n) (T n) (P n)).map (Prod.map φ φ) := fun n =>
      randPairLaw_map (G n) (P n) (T n) (hTmeas n) (hsmul n) hφmeas
    simpa only [heq] using hmapped
  -- Step 2: the remainder `(Aₙ − a)Tₙ + (Bₙ − b)` vanishes in probability at randomized data.
  -- Tightness of the randomized base statistic — read off `hjoint` — is what controls the
  -- product `(Aₙ − a)Tₙ`.
  have hmarg : WeakConverges
      (fun n => (randPairLaw (G n) (T n) (P n)).map Prod.fst) R := by
    have hmapped := hjoint.map (f := Prod.fst) continuous_fst measurable_fst
    simpa using hmapped
  haveI : ∀ n, IsProbabilityMeasure ((randPairLaw (G n) (T n) (P n)).map Prod.fst) := fun n =>
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hrem : ∀ δ > (0 : ℝ), Tendsto (fun n => (Fintype.card (G n) : ℝ)⁻¹ *
      ∑ g : G n, (P n).real {x | δ ≤ ‖S n (g • x) - L n (g • x)‖}) atTop (𝓝 0) := by
    intro δ hδ
    rw [NormedAddGroup.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨M, hMpos, hMev⟩ :=
      exists_tight_bound_of_weakConverges hmarg (show (0 : ℝ) < ε / 4 by positivity)
    have hmeasM : MeasurableSet {y : ℝ | M ≤ |y|} :=
      measurableSet_le measurable_const continuous_abs.measurable
    have hδM : (0 : ℝ) < δ / (2 * M) := by positivity
    have h1 := (hA (δ / (2 * M)) hδM).eventually
      (eventually_lt_nhds (show (0 : ℝ) < ε / 4 by positivity))
    have h3 := (hB (δ / 2) (by positivity)).eventually
      (eventually_lt_nhds (show (0 : ℝ) < ε / 4 by positivity))
    filter_upwards [hMev, h1, h3] with n hn0 hn1 hn3
    -- The tightness bound, rewritten as a group mixture.
    have hmargval : ((randPairLaw (G n) (T n) (P n)).map Prod.fst).real {y : ℝ | M ≤ |y|}
        = (Fintype.card (G n) : ℝ)⁻¹ *
            ∑ g : G n, (P n).real {x | M ≤ |T n (g • x)|} := by
      have hset : (Prod.fst ⁻¹' {y : ℝ | M ≤ |y|} : Set (ℝ × ℝ))
          = {y : ℝ | M ≤ |y|} ×ˢ (Set.univ : Set ℝ) := by
        ext z; simp [Set.mem_prod]
      rw [Measure.real, Measure.map_apply measurable_fst hmeasM, hset]
      exact real_randPairLaw_prod_univ (G n) (P n) (T n) (hTmeas n) (hsmul n) hmeasM
    rw [hmargval] at hn0
    -- The three-way inclusion, at each group element.
    have hincl : ∀ g : G n, {x : 𝓧 n | δ ≤ ‖S n (g • x) - L n (g • x)‖}
        ⊆ ({x : 𝓧 n | δ / (2 * M) ≤ |A n (g • x) - a|}
            ∪ {x : 𝓧 n | M ≤ |T n (g • x)|})
          ∪ {x : 𝓧 n | δ / 2 ≤ |B n (g • x) - b|} := by
      intro g x hx
      simp only [Set.mem_setOf_eq] at hx
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hcon
      obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hcon
      have hval : S n (g • x) - L n (g • x)
          = (A n (g • x) - a) * T n (g • x) + (B n (g • x) - b) := by
        simp only [hSdef, hLdef, hφdef]; ring
      have hcM : δ / (2 * M) * M = δ / 2 := by field_simp
      have hprod : |A n (g • x) - a| * |T n (g • x)| < δ / 2 := by
        nlinarith [mul_pos (sub_pos.mpr hc1) hMpos,
          mul_nonneg (abs_nonneg (A n (g • x) - a)) (sub_nonneg.mpr hc2.le), hcM]
      have hlt : ‖S n (g • x) - L n (g • x)‖ < δ := by
        rw [Real.norm_eq_abs, hval]
        calc |(A n (g • x) - a) * T n (g • x) + (B n (g • x) - b)|
            ≤ |(A n (g • x) - a) * T n (g • x)| + |B n (g • x) - b| := abs_add_le _ _
          _ < δ / 2 + δ / 2 := by rw [abs_mul]; linarith
          _ = δ := by ring
      linarith
    -- Sum the inclusion over the group.
    have hstep : ∀ g : G n, (P n).real {x | δ ≤ ‖S n (g • x) - L n (g • x)‖}
        ≤ (P n).real {x | δ / (2 * M) ≤ |A n (g • x) - a|}
          + (P n).real {x | M ≤ |T n (g • x)|}
          + (P n).real {x | δ / 2 ≤ |B n (g • x) - b|} := by
      intro g
      have hu := measureReal_union_le (μ := P n)
        ({x : 𝓧 n | δ / (2 * M) ≤ |A n (g • x) - a|} ∪ {x : 𝓧 n | M ≤ |T n (g • x)|})
        {x : 𝓧 n | δ / 2 ≤ |B n (g • x) - b|}
      have hu' := measureReal_union_le (μ := P n)
        {x : 𝓧 n | δ / (2 * M) ≤ |A n (g • x) - a|} {x : 𝓧 n | M ≤ |T n (g • x)|}
      have hm := measureReal_mono (μ := P n) (hincl g)
      linarith
    have hsum := Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset (G n))) => hstep g)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hc0 : (0 : ℝ) ≤ (Fintype.card (G n) : ℝ)⁻¹ := by positivity
    have hnn : 0 ≤ (Fintype.card (G n) : ℝ)⁻¹ *
        ∑ g : G n, (P n).real {x | δ ≤ ‖S n (g • x) - L n (g • x)‖} :=
      mul_nonneg hc0 (Finset.sum_nonneg fun g _ => measureReal_nonneg)
    have hbound : (Fintype.card (G n) : ℝ)⁻¹ *
        ∑ g : G n, (P n).real {x | δ ≤ ‖S n (g • x) - L n (g • x)‖}
        ≤ ((Fintype.card (G n) : ℝ)⁻¹ *
              ∑ g : G n, (P n).real {x | δ / (2 * M) ≤ |A n (g • x) - a|})
          + ((Fintype.card (G n) : ℝ)⁻¹ * ∑ g : G n, (P n).real {x | M ≤ |T n (g • x)|})
          + ((Fintype.card (G n) : ℝ)⁻¹ *
              ∑ g : G n, (P n).real {x | δ / 2 ≤ |B n (g • x) - b|}) := by
      calc (Fintype.card (G n) : ℝ)⁻¹ *
            ∑ g : G n, (P n).real {x | δ ≤ ‖S n (g • x) - L n (g • x)‖}
          ≤ (Fintype.card (G n) : ℝ)⁻¹ *
              ((∑ g : G n, (P n).real {x | δ / (2 * M) ≤ |A n (g • x) - a|}
                  + ∑ g : G n, (P n).real {x | M ≤ |T n (g • x)|})
                + ∑ g : G n, (P n).real {x | δ / 2 ≤ |B n (g • x) - b|}) :=
            mul_le_mul_of_nonneg_left hsum hc0
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    linarith
  -- Step 3: transfer the limit from `L` to `S`, then run the forward engine.
  have hconvS : WeakConverges (fun n => randPairLaw (G n) (S n) (P n))
      ((R.map φ).prod (R.map φ)) :=
    weakConverges_randPairLaw_of_tendstoInProb_avg P S L hSmeas hLmeas hsmul hrem hconvL
  have hfinal := randDist_tendstoInProb_cdf P S (R.map φ) hSmeas hsmul hconvS hcont
  simpa only [hSdef, hφdef] using hfinal

end Slutsky

end StatLean.HypothesisTesting
