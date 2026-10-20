module
public import StatLean.AsymptoticStatistics.ForMathlib.SqrtLogProduct
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Data.ENat.Lattice

@[expose] public section

/-!
# Brackets and bracketing covers for empirical-process theory

A **bracket** `[l, u]` is a pair of functions `l ≤ u` pointwise. An
**ε-bracket** in `L_r(P)` is one whose `L_r(P)`-size `‖u − l‖_{P,r}`
is less than `ε`. A class `F` of measurable functions admits a
**finite ε-bracketing cover** if there are finitely many ε-brackets
that cover `F`: every `f ∈ F` lies pointwise inside some bracket. This
is the combinatorial input to vdV's bracketing-entropy theorems (vdV
§19.2, Theorems 19.4, 19.5).

Principal declarations: `IsBracket`, `IsEpsBracket`,
`HasFiniteBracketingCover`, `bracketingNumber`, `bracketingEntropyIntegral`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ENNReal
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A pair `(l, u)` is a **bracket** if `l ≤ u` pointwise.

vdV §19.2: the underlying combinatorial unit of bracketing entropy. -/
def IsBracket (l u : Ω → ℝ) : Prop := ∀ x, l x ≤ u x

/-- An **ε-bracket** in `L_r(P)`: a bracket `[l, u]` with `l, u` measurable,
both in `L_r(P)`, and `‖u − l‖_{P,r} < ε`.

The integrability conditions on `l` and `u` are bundled here so that the
strong-LLN invocation in the proof of Theorem 19.4 can fire directly on
the bracket bounds: vdV §19.2 requires the bracketing functions `l` and
`u` to have finite `L_r(P)`-norms. Measurability is included so that
`IndepFun.comp` and `IdentDistrib.comp` can post-compose the iid sequence
by `l` / `u`.

vdV §19.2: `‖u − l‖_{P,r} < ε`. -/
def IsEpsBracket (ε : ℝ) (l u : Ω → ℝ) (r : ℝ≥0∞) (P : Measure Ω) : Prop :=
  IsBracket l u ∧ Measurable l ∧ Measurable u ∧ MemLp l r P ∧ MemLp u r P ∧
    eLpNorm (fun x => u x - l x) r P < ENNReal.ofReal ε

namespace IsEpsBracket

variable {ε : ℝ} {l u : Ω → ℝ} {r : ℝ≥0∞} {P : Measure Ω}

lemma isBracket (h : IsEpsBracket ε l u r P) : IsBracket l u := h.1

lemma measurable_lower (h : IsEpsBracket ε l u r P) : Measurable l := h.2.1

lemma measurable_upper (h : IsEpsBracket ε l u r P) : Measurable u := h.2.2.1

lemma memLp_lower (h : IsEpsBracket ε l u r P) : MemLp l r P := h.2.2.2.1

lemma memLp_upper (h : IsEpsBracket ε l u r P) : MemLp u r P := h.2.2.2.2.1

lemma size_lt (h : IsEpsBracket ε l u r P) :
    eLpNorm (fun x => u x - l x) r P < ENNReal.ofReal ε := h.2.2.2.2.2

/-- An `ε₁`-bracket is an `ε₂`-bracket whenever `ε₁ ≤ ε₂`: the size bound
`‖u − l‖_{P,r} < ε` is monotone in `ε`. -/
lemma mono_eps {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (h : IsEpsBracket ε₁ l u r P) :
    IsEpsBracket ε₂ l u r P :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    lt_of_lt_of_le h.2.2.2.2.2 (ENNReal.ofReal_le_ofReal hε)⟩

end IsEpsBracket

/-- `F` admits a **finite ε-bracketing cover** in `L_r(P)`: there are
finitely many ε-brackets `[l_i, u_i]` such that every `f ∈ F` lies
pointwise inside some `[l_i, u_i]`.

vdV §19.2: `N_{[]}(ε, F, L_r(P)) < ∞`. The finite collection is encoded
as `Fin k`-indexed lower- and upper-bound functions; this matches the
proof of Theorem 19.4 where the strong LLN is applied to each `l i` and
`u i`.

Edge case: `F = ∅ ⇒ k = 0` works trivially. -/
def HasFiniteBracketingCover (F : Set (Ω → ℝ)) (ε : ℝ) (r : ℝ≥0∞) (P : Measure Ω) : Prop :=
  ∃ (k : ℕ) (l u : Fin k → Ω → ℝ),
    (∀ i, IsEpsBracket ε (l i) (u i) r P) ∧
    (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)

lemma HasFiniteBracketingCover.empty (ε : ℝ) (r : ℝ≥0∞) (P : Measure Ω) :
    HasFiniteBracketingCover (∅ : Set (Ω → ℝ)) ε r P := by
  refine ⟨0, Fin.elim0, Fin.elim0, ?_, ?_⟩
  · intro i; exact i.elim0
  · intro f hf; exact absurd hf (Set.notMem_empty f)

lemma HasFiniteBracketingCover.mono {F F' : Set (Ω → ℝ)} {ε : ℝ} {r : ℝ≥0∞} {P : Measure Ω}
    (h : HasFiniteBracketingCover F ε r P) (hF' : F' ⊆ F) :
    HasFiniteBracketingCover F' ε r P := by
  obtain ⟨k, l, u, hbr, hcov⟩ := h
  exact ⟨k, l, u, hbr, fun f hf => hcov f (hF' hf)⟩

/-- The **bracketing number** `N_{[]}(ε, F, L_r(P))` — the minimum size
of an ε-bracketing cover, valued in `ℕ∞`.

`bracketingNumber ε F r P = ⊤` iff no finite ε-bracketing cover exists;
otherwise it returns the smallest cover size as a finite `ℕ`.

vdV §19.2. -/
noncomputable def bracketingNumber
    (ε : ℝ) (F : Set (Ω → ℝ)) (r : ℝ≥0∞) (P : Measure Ω) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : ∃ l u : Fin k → Ω → ℝ,
      (∀ i, IsEpsBracket ε (l i) (u i) r P) ∧
      (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)),
    (k : ℕ∞)

/-- `bracketingNumber ε F r P < ⊤` iff `F` admits a finite ε-bracketing cover. -/
lemma bracketingNumber_lt_top_iff_HasFiniteBracketingCover
    {F : Set (Ω → ℝ)} {ε : ℝ} {r : ℝ≥0∞} {P : Measure Ω} :
    bracketingNumber ε F r P < ⊤ ↔ HasFiniteBracketingCover F ε r P := by
  refine ⟨?_, ?_⟩
  · intro hlt
    by_contra h_no_cover
    have h_all_top : ∀ k : ℕ,
        ¬ (∃ l u : Fin k → Ω → ℝ,
            (∀ i, IsEpsBracket ε (l i) (u i) r P) ∧
            (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)) := by
      intro k ⟨l, u, hbr, hcov⟩
      exact h_no_cover ⟨k, l, u, hbr, hcov⟩
    have h_top : bracketingNumber ε F r P = ⊤ := by
      unfold bracketingNumber
      apply le_antisymm le_top
      refine le_iInf fun k => ?_
      refine le_iInf fun hk => ?_
      exact absurd hk (h_all_top k)
    rw [h_top] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨k, l, u, hbr, hcov⟩
    refine lt_of_le_of_lt ?_ (ENat.coe_lt_top k)
    refine iInf_le_of_le k ?_
    exact iInf_le_of_le ⟨l, u, hbr, hcov⟩ le_rfl

/-- **Achieved-infimum extraction for the bracketing number.**

When `F` admits a finite ε-bracketing cover, the infimum defining
`bracketingNumber` is *achieved*: there is a concrete cover of some size `k`
(the minimal one, `Nat.find` of the "has a cover of size `k`" predicate) with
`bracketingNumber ε F 2 P = k`. This is the constructive counterpart of
`bracketingNumber_lt_top_iff_HasFiniteBracketingCover`: the latter only says the
number is finite, while this lemma hands back the witnessing cover *and* the
exact equality, which the nested-partition construction
(`nestedBracketPartition_of_finiteEntropy`) needs to set its per-level
`coverCard` equal to `bracketingNumber`.

The minimal size is `Nat.find` of `Q k := ∃ l u, (brackets ∧ cover)`; the
equality is by `le_antisymm` against the double `iInf` (one direction
`iInf_le`, the other `le_iInf` + `Nat.find_min'`). -/
theorem exists_minimal_bracketingCover {Ω} [MeasurableSpace Ω] {F : Set (Ω → ℝ)}
    {ε : ℝ} {P : Measure Ω}
    (h : HasFiniteBracketingCover F ε 2 P) :
    ∃ (k : ℕ) (l u : Fin k → Ω → ℝ),
      (∀ i, IsEpsBracket ε (l i) (u i) 2 P) ∧
      (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x) ∧
      bracketingNumber ε F 2 P = (k : ℕ∞) := by
  classical
  -- The predicate `Q k := there is a cover of size exactly `k``.
  set Q : ℕ → Prop := fun k => ∃ l u : Fin k → Ω → ℝ,
      (∀ i, IsEpsBracket ε (l i) (u i) 2 P) ∧
      (∀ f ∈ F, ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x) with hQ
  have hex : ∃ k, Q k := by obtain ⟨k, l, u, hbr, hcov⟩ := h; exact ⟨k, l, u, hbr, hcov⟩
  -- The minimal cover size.
  set k := Nat.find hex with hk
  obtain ⟨l, u, hbr, hcov⟩ : Q k := Nat.find_spec hex
  refine ⟨k, l, u, hbr, hcov, ?_⟩
  -- `bracketingNumber = k` by antisymmetry against the double infimum.
  apply le_antisymm
  · -- `≤`: the size-`k` cover is an admissible index.
    refine iInf_le_of_le k ?_
    exact iInf_le_of_le ⟨l, u, hbr, hcov⟩ le_rfl
  · -- `≥`: any admissible size `m` has `k ≤ m` by minimality of `Nat.find`.
    refine le_iInf fun m => ?_
    refine le_iInf fun hm => ?_
    have : k ≤ m := Nat.find_min' hex hm
    exact_mod_cast this

/-- **Antitonicity of the bracketing number in the scale `ε`.**

A smaller tolerance forces at least as many brackets: if `ε₁ ≤ ε₂` then
`N_{[]}(ε₂, F, L_r(P)) ≤ N_{[]}(ε₁, F, L_r(P))`. Indeed every `ε₁`-bracketing
cover is an `ε₂`-bracketing cover (`IsEpsBracket.mono_eps`), so the infimum
defining `bracketingNumber ε₂` ranges over a superset of admissible sizes. -/
lemma bracketingNumber_antitone_eps
    {F : Set (Ω → ℝ)} {ε₁ ε₂ : ℝ} {r : ℝ≥0∞} {P : Measure Ω} (hε : ε₁ ≤ ε₂) :
    bracketingNumber ε₂ F r P ≤ bracketingNumber ε₁ F r P := by
  unfold bracketingNumber
  refine iInf_mono fun k => ?_
  refine iInf_mono' fun hk => ?_
  obtain ⟨l, u, hbr, hcov⟩ := hk
  exact ⟨⟨l, u, fun i => (hbr i).mono_eps hε, hcov⟩, le_rfl⟩

/-- **A nonempty class has bracketing number at least one.**

For any nonempty `F`, every admissible bracketing cover must have positive size:
the size-`0` cover is impossible, because its cover clause `∀ f ∈ F, ∃ i : Fin 0, …`
applied to any `f₀ ∈ F` would produce an index `i : Fin 0`, which is empty. Hence
`1 ≤ N_{[]}(ε, F, L_2(P))` for every scale `ε`. This is the positivity input that
makes the entropy integrand `√(log (1 + N))` bounded below by `√(log 2) > 0`
pointwise, hence the entropy integral strictly positive
(`bracketingEntropyIntegral_pos_of_nonempty`). -/
lemma one_le_bracketingNumber_of_nonempty
    {F : Set (Ω → ℝ)} {P : Measure Ω} (hF : F.Nonempty) (ε : ℝ) :
    1 ≤ bracketingNumber ε F 2 P := by
  unfold bracketingNumber
  refine le_iInf fun k => le_iInf fun hk => ?_
  -- It suffices that `k ≠ 0`; then `1 ≤ (k : ℕ∞)`.
  have hk_ne : k ≠ 0 := by
    rintro rfl
    obtain ⟨_l, _u, _hbr, hcov⟩ := hk
    obtain ⟨f₀, hf₀⟩ := hF
    obtain ⟨i, _⟩ := hcov f₀ hf₀
    exact i.elim0
  have : (1 : ℕ) ≤ k := Nat.one_le_iff_ne_zero.mpr hk_ne
  exact_mod_cast this

open Filter

/-- The **bracketing entropy integral** `J_{[]}(δ, F, L_2(P))` —
the cumulative bracketing-entropy "size" of `F` from scale `0` up to `δ`,
weighted by `√(log N_{[]}(ε, F, L_2(P)))`.

vdV §19.2: `J_{[]}(δ, F, L_2(P)) = ∫_0^δ √(log N_{[]}(ε, F, L_2(P))) dε`.

The integrand at scale `ε` is obtained from `bracketingNumber ε F 2 P : ℕ∞`
by `ENat.recTopCoe`:
* if `bracketingNumber ε F 2 P = ⊤` (no finite ε-bracketing cover), the
  integrand value is `⊤ : ℝ≥0∞`;
* otherwise, with `n : ℕ` the underlying count, the integrand is
  `ENNReal.ofReal (√(log (1 + n)))` (the `1 +` regularizer matches vdV
  Lemma 19.33's `log(1 + |F|)`).

The integral is taken over `Set.Ioc 0 δ` against Lebesgue `volume`. With
this convention `J_{[]}(δ, F, L_2(P)) = ⊤` whenever `bracketingNumber`
fails to be finite on a positive-measure subset of `(0, δ]`, faithfully
reflecting the textbook content.

vdV §19.2. -/
noncomputable def bracketingEntropyIntegral
    (δ : ℝ) (F : Set (Ω → ℝ)) (P : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ε in Set.Ioc 0 δ,
    ENat.recTopCoe (⊤ : ℝ≥0∞)
      (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (1 + (n : ℝ)))))
      (bracketingNumber ε F 2 P)
      ∂volume

/-- The weight `N ↦ √(log (1 + N))` on `ℕ∞` with the `⊤` convention, as a plain
(non-dependent) function so its monotonicity can be stated cleanly.

The `1 +` regularizer (matching vdV Lemma 19.33's `log(1 + |F|)`) keeps the
weight strictly positive even when the bracketing count is `0` or `1`, so the
chaining leaves' nonzero `levelJumpSup`/`levelOscSup` are dominated by a nonzero
right-hand side. -/
noncomputable def entropyWeight (N : ℕ∞) : ℝ≥0∞ :=
  ENat.recTopCoe (⊤ : ℝ≥0∞)
    (fun n : ℕ => ENNReal.ofReal (Real.sqrt (Real.log (1 + (n : ℝ))))) N

@[simp] lemma entropyWeight_top : entropyWeight ⊤ = ⊤ := rfl

@[simp] lemma entropyWeight_coe (n : ℕ) :
    entropyWeight (n : ℕ∞) = ENNReal.ofReal (Real.sqrt (Real.log (1 + (n : ℝ)))) := rfl

lemma entropyWeight_mul_le (N M : ℕ∞) :
    entropyWeight (N * M) ≤ entropyWeight N + entropyWeight M := by
  rcases eq_or_ne N ⊤ with rfl | hN
  · simp
  rcases eq_or_ne M ⊤ with rfl | hM
  · simp
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hN
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hM
  rw [show (n : ℕ∞) * (m : ℕ∞) = ((n * m : ℕ) : ℕ∞) by norm_cast,
    entropyWeight_coe, entropyWeight_coe, entropyWeight_coe,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hprod : (1 : ℝ) + (n : ℝ) * m ≤ (1 + n) * (1 + m) := by
    nlinarith [hn, hm, mul_nonneg hn hm]
  have hnpos : (0 : ℝ) < 1 + n := by positivity
  have hmpos : (0 : ℝ) < 1 + m := by positivity
  calc
    Real.sqrt (Real.log (1 + ((n * m : ℕ) : ℝ))) =
        Real.sqrt (Real.log (1 + (n : ℝ) * m)) := by push_cast; ring
    _ ≤ Real.sqrt (Real.log ((1 + (n : ℝ)) * (1 + m))) := by
      apply Real.sqrt_le_sqrt
      exact Real.log_le_log (by positivity) hprod
    _ = Real.sqrt (Real.log (1 + (n : ℝ)) + Real.log (1 + m)) := by
      rw [Real.log_mul hnpos.ne' hmpos.ne']
    _ ≤ Real.sqrt (Real.log (1 + (n : ℝ))) +
        Real.sqrt (Real.log (1 + m)) :=
      ForMathlib.Real.sqrt_add_le (Real.log_nonneg (by linarith))
        (Real.log_nonneg (by linarith))

/-- The **pointwise integrand** of `bracketingEntropyIntegral`: the value
`√(log (1 + N_{[]}(ε, F, L_2(P))))` at scale `ε`, with the `⊤` convention when no
finite ε-bracketing cover exists. By definition

`bracketingEntropyIntegral δ F P = ∫⁻ ε in Ioc 0 δ, entropyIntegrand ε F P`.

This is the `ENat.recTopCoe` expression occurring in
`bracketingEntropyIntegral`; in particular,
`dyadic_sum_le_bracketingEntropyIntegral` applies its monotonicity directly. -/
noncomputable def entropyIntegrand
    (ε : ℝ) (F : Set (Ω → ℝ)) (P : Measure Ω) : ℝ≥0∞ :=
  entropyWeight (bracketingNumber ε F 2 P)

lemma bracketingEntropyIntegral_eq_setLIntegral
    (δ : ℝ) (F : Set (Ω → ℝ)) (P : Measure Ω) :
    bracketingEntropyIntegral δ F P
      = ∫⁻ ε in Set.Ioc 0 δ, entropyIntegrand ε F P ∂volume := rfl

/-- **Monotonicity of the entropy weight in the bracketing count.**
`entropyWeight` is monotone in `N : ℕ∞`: `n ↦ log (1 + n)` is monotone on the
naturals with argument always `≥ 1` (no `n = 0` carve-out needed), `√` and
`ENNReal.ofReal` are monotone, and `⊤` is the greatest value. -/
lemma entropyWeight_mono : Monotone entropyWeight := by
  intro N₁ N₂ h
  rcases eq_or_ne N₂ ⊤ with hN₂ | hN₂
  · subst hN₂; simp
  · -- `N₂` finite, hence `N₁` finite and `N₁ ≤ N₂` as naturals
    obtain ⟨n₂, rfl⟩ := ENat.ne_top_iff_exists.mp hN₂
    obtain ⟨n₁, rfl⟩ := ENat.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top hN₂ h)
    rw [entropyWeight_coe, entropyWeight_coe]
    have hn : n₁ ≤ n₂ := by exact_mod_cast h
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    -- `1 + n₁ ≥ 1 > 0`, so `log` is monotone on `[1 + n₁, 1 + n₂]` with no
    -- `n = 0` special case (the `1 +` regularizer is what removes it).
    apply Real.log_le_log (by positivity)
    have : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
    linarith

/-- **Antitonicity of the entropy integrand in the scale `ε`.**
Since `bracketingNumber` is antitone in `ε` (`bracketingNumber_antitone_eps`)
and the weighting is monotone in the count (`entropyWeight_mono`), the
integrand decreases as `ε` grows: `ε₁ ≤ ε₂ → entropyIntegrand ε₂ ≤ entropyIntegrand ε₁`. -/
lemma entropyIntegrand_antitone_eps
    {F : Set (Ω → ℝ)} {P : Measure Ω} {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) :
    entropyIntegrand ε₂ F P ≤ entropyIntegrand ε₁ F P :=
  entropyWeight_mono (bracketingNumber_antitone_eps hε)

/-- **The entropy integrand dominates `√(log 2)` for a nonempty class.**

At any scale `ε`, a nonempty `F` has `1 ≤ N_{[]}(ε, F, L²(P))`
(`one_le_bracketingNumber_of_nonempty`), and `entropyWeight` is monotone, so
`entropyIntegrand ε F P ≥ entropyWeight 1 = ofReal (√(log 2))`. The `1 +`
regularizer in the integrand is what makes this lower bound positive. -/
lemma sqrt_log_two_le_entropyIntegrand
    {F : Set (Ω → ℝ)} {P : Measure Ω} (hF : F.Nonempty) (ε : ℝ) :
    ENNReal.ofReal (Real.sqrt (Real.log 2)) ≤ entropyIntegrand ε F P := by
  have h1 : (1 : ℕ∞) ≤ bracketingNumber ε F 2 P :=
    one_le_bracketingNumber_of_nonempty hF ε
  calc ENNReal.ofReal (Real.sqrt (Real.log 2))
      = entropyWeight (1 : ℕ∞) := by
        rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, entropyWeight_coe]
        norm_num
    _ ≤ entropyWeight (bracketingNumber ε F 2 P) := entropyWeight_mono h1

/-- **Strict positivity of the bracketing entropy integral for a nonempty class.**

For any nonempty `F` and any positive scale `δ' > 0`, the entropy integral
`J_{[]}(δ', F, L²(P))` is strictly positive. The integrand
`√(log (1 + N_{[]}(ε, F, L_2(P))))` is bounded below pointwise on `(0, δ']` by
`√(log 2) > 0` (`sqrt_log_two_le_entropyIntegrand`): a nonempty class has
`N_{[]}(ε, F, L_2(P)) ≥ 1`, so by monotonicity of the weight the integrand is
`≥ entropyWeight 1 = ofReal (√(log 2))`. Hence
`J ≥ ofReal (√(log 2)) · volume (Ioc 0 δ') = ofReal (√(log 2)) · ofReal δ' > 0`.

Thus a separate positivity assumption on `J` is unnecessary: it follows from
the nonemptiness of `F`, as in vdV Theorem 19.5. -/
lemma bracketingEntropyIntegral_pos_of_nonempty
    {F : Set (Ω → ℝ)} {P : Measure Ω} {δ' : ℝ} (hF : F.Nonempty) (hδ : 0 < δ') :
    0 < bracketingEntropyIntegral δ' F P := by
  rw [bracketingEntropyIntegral_eq_setLIntegral]
  -- The constant lower bound `c₀ := ofReal (√(log 2))` on the integrand.
  set c₀ : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (Real.log 2)) with hc₀
  -- The integral dominates the integral of the constant `c₀` (pointwise bound
  -- `c₀ ≤ entropyIntegrand ε F P` from `sqrt_log_two_le_entropyIntegrand`).
  have h_mono : ∫⁻ _ε in Set.Ioc 0 δ', c₀ ∂volume
      ≤ ∫⁻ ε in Set.Ioc 0 δ', entropyIntegrand ε F P ∂volume :=
    lintegral_mono fun ε => sqrt_log_two_le_entropyIntegrand hF ε
  -- `∫⁻ const = c₀ · volume (Ioc 0 δ')`.
  rw [MeasureTheory.setLIntegral_const] at h_mono
  -- `volume (Ioc 0 δ') = ofReal δ'`.
  rw [Real.volume_Ioc, sub_zero] at h_mono
  -- Both factors are strictly positive, hence so is the product, hence the integral.
  have h_c₀_pos : (0 : ℝ≥0∞) < c₀ := by
    rw [hc₀, ENNReal.ofReal_pos]
    exact Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  have h_vol_pos : (0 : ℝ≥0∞) < ENNReal.ofReal δ' := ENNReal.ofReal_pos.mpr hδ
  have h_prod_pos : (0 : ℝ≥0∞) < c₀ * ENNReal.ofReal δ' :=
    ENNReal.mul_pos h_c₀_pos.ne' h_vol_pos.ne'
  exact lt_of_lt_of_le h_prod_pos h_mono

/-- **Finite bracketing cover at every scale from a finite entropy integral.**

If the bracketing entropy integral `J_{[]}(1, F, L²(P))` is finite, then `F`
admits a finite `ε`-bracketing cover (`HasFiniteBracketingCover F ε 2 P`) at
*every* scale `ε > 0`. This is the for-all-`ε` strengthening of the
existence-at-some-`ε` extraction used in the marginal-CLT step.

**Proof.** It suffices to show `bracketingNumber ε F 2 P < ⊤` for all `ε > 0`
(then `bracketingNumber_lt_top_iff_HasFiniteBracketingCover` gives the cover).
Set `ε₀ = min ε 1 ∈ (0, 1]`; antitonicity in the scale reduces the goal to
`bracketingNumber ε₀ F 2 P < ⊤`. Suppose not: `bracketingNumber ε₀ F 2 P = ⊤`.
Then for every `ε' ∈ (0, ε₀]` antitonicity forces `bracketingNumber ε' F 2 P =
⊤`, hence `entropyIntegrand ε' F P = entropyWeight ⊤ = ⊤`. Lower-bounding the
entropy integral over `Ioc 0 1` by the integral over the sub-interval
`Ioc 0 ε₀` (where the integrand is identically `⊤`) gives
`⊤ · volume(Ioc 0 ε₀) = ⊤ · ε₀ = ⊤` (as `ε₀ > 0`), contradicting finiteness. -/
lemma hasFiniteBracketingCover_of_entropyIntegral_lt_top
    {F : Set (Ω → ℝ)} {P : Measure Ω}
    (h_int : bracketingEntropyIntegral 1 F P < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    HasFiniteBracketingCover F ε 2 P := by
  rw [← bracketingNumber_lt_top_iff_HasFiniteBracketingCover]
  -- Reduce to the scale `ε₀ = min ε 1 ∈ (0, 1]` by antitonicity.
  set ε₀ : ℝ := min ε 1 with hε₀
  have hε₀_pos : 0 < ε₀ := lt_min hε one_pos
  have hε₀_le_ε : ε₀ ≤ ε := min_le_left _ _
  have hε₀_le_one : ε₀ ≤ 1 := min_le_right _ _
  -- `bracketingNumber ε ≤ bracketingNumber ε₀`, so finiteness at `ε₀` suffices.
  refine lt_of_le_of_lt (bracketingNumber_antitone_eps hε₀_le_ε) ?_
  -- Suppose the bracketing number at scale `ε₀` is infinite.
  by_contra h_top
  rw [not_lt, top_le_iff] at h_top
  -- Then the integrand is `⊤` on the whole sub-interval `Ioc 0 ε₀`.
  have h_integrand_top : ∀ ε' ∈ Set.Ioc (0 : ℝ) ε₀, entropyIntegrand ε' F P = ⊤ := by
    intro ε' hε'
    have h_bn_top : bracketingNumber ε' F 2 P = ⊤ :=
      top_unique (h_top ▸ bracketingNumber_antitone_eps hε'.2)
    rw [entropyIntegrand, h_bn_top, entropyWeight_top]
  -- The entropy integral over `Ioc 0 1` dominates the one over `Ioc 0 ε₀ = ⊤`.
  have h_eq_top : bracketingEntropyIntegral 1 F P = ⊤ := by
    rw [bracketingEntropyIntegral_eq_setLIntegral]
    refine top_le_iff.mp ?_
    calc (⊤ : ℝ≥0∞)
        = ∫⁻ _ε in Set.Ioc (0 : ℝ) ε₀, (⊤ : ℝ≥0∞) ∂volume := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
            ENNReal.top_mul (ENNReal.ofReal_ne_zero_iff.mpr hε₀_pos)]
      _ = ∫⁻ ε' in Set.Ioc (0 : ℝ) ε₀, entropyIntegrand ε' F P ∂volume :=
          (setLIntegral_congr_fun measurableSet_Ioc h_integrand_top).symm
      _ ≤ ∫⁻ ε' in Set.Ioc (0 : ℝ) 1, entropyIntegrand ε' F P ∂volume :=
          lintegral_mono_set (Set.Ioc_subset_Ioc_right hε₀_le_one)
  rw [h_eq_top] at h_int
  exact (lt_irrefl _ h_int).elim

/-- The dyadic scales `(1/2)^q · δ` strictly decrease and tend to `0`; the
half-open intervals `Ioc ((1/2)^{q+1}·δ) ((1/2)^q·δ)` therefore partition
`Ioc 0 δ`. This is the geometric covering used by
`dyadic_sum_le_bracketingEntropyIntegral`. -/
private lemma iUnion_dyadic_Ioc_eq {δ : ℝ} (hδ : 0 < δ) :
    ⋃ q : ℕ, Set.Ioc ((1/2 : ℝ)^(q+1) * δ) ((1/2 : ℝ)^q * δ) = Set.Ioc 0 δ := by
  have hhalf_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have hapos : ∀ q : ℕ, 0 < (1/2 : ℝ)^q * δ := fun q => by positivity
  apply Set.eq_of_subset_of_subset
  · -- each interval sits inside `Ioc 0 δ`
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_Ioc] at hx
    obtain ⟨q, hlo, hhi⟩ := hx
    refine ⟨lt_trans (hapos (q+1)) hlo, ?_⟩
    refine le_trans hhi ?_
    -- (1/2)^q * δ ≤ δ
    calc (1/2 : ℝ)^q * δ ≤ 1 * δ := by
            apply mul_le_mul_of_nonneg_right _ hδ.le
            exact pow_le_one₀ hhalf_pos.le (by norm_num)
      _ = δ := one_mul δ
  · -- every `x ∈ Ioc 0 δ` lies in some dyadic interval
    intro x hx
    simp only [Set.mem_Ioc] at hx
    obtain ⟨hx0, hxδ⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    -- least `q` with `(1/2)^q * δ < x`; it is ≥ 1 since `(1/2)^0 * δ = δ ≥ x`
    have hexists : ∃ q : ℕ, (1/2 : ℝ)^q * δ < x := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : (0:ℝ) < x / δ)
        (by norm_num : (1/2 : ℝ) < 1)
      exact ⟨n, (lt_div_iff₀ hδ).mp hn⟩
    classical
    let q₀ := Nat.find hexists
    have hq₀ : (1/2 : ℝ)^q₀ * δ < x := Nat.find_spec hexists
    have hq₀_pos : 1 ≤ q₀ := by
      rcases Nat.eq_zero_or_pos q₀ with h0 | h; swap; · exact h
      exfalso
      rw [show q₀ = 0 from h0] at hq₀; simp only [pow_zero, one_mul] at hq₀
      exact absurd hq₀ (not_lt.mpr hxδ)
    -- set `p := q₀ - 1`; the previous index `p` does NOT satisfy the bound
    obtain ⟨p, hp⟩ : ∃ p, q₀ = p + 1 := ⟨q₀ - 1, by omega⟩
    have hprev : ¬ (1/2 : ℝ)^p * δ < x :=
      Nat.find_min hexists (by omega : p < q₀)
    refine ⟨p, ?_, not_lt.mp hprev⟩
    rw [hp] at hq₀
    exact hq₀

/-- **Per-dyadic-interval lower bound.** On the interval
`Ioc ((1/2)^{q+1}·δ) ((1/2)^q·δ)` of length `(1/2)^{q+1}·δ`, the entropy
integrand is `≥` its value at the right endpoint `(1/2)^q·δ` (antitonicity).
Multiplying length by that value and doubling recovers `(1/2)^q·δ` as the
weight, giving
`ofReal((1/2)^q·δ) · entropyIntegrand((1/2)^q·δ) ≤ 2 · ∫⁻ over the interval`. -/
private lemma dyadic_term_le_two_setLIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hδ : 0 < δ) (q : ℕ) :
    ENNReal.ofReal ((1/2 : ℝ)^q * δ) * entropyIntegrand ((1/2 : ℝ)^q * δ) F P
      ≤ 2 * ∫⁻ ε in Set.Ioc ((1/2 : ℝ)^(q+1) * δ) ((1/2 : ℝ)^q * δ),
            entropyIntegrand ε F P ∂volume := by
  set aq : ℝ := (1/2 : ℝ)^q * δ with haq
  set aq1 : ℝ := (1/2 : ℝ)^(q+1) * δ with haq1
  have haq_pos : 0 < aq := by rw [haq]; positivity
  have haq1_eq : aq1 = (1/2 : ℝ) * aq := by rw [haq1, haq]; ring
  have haq1_le : aq1 ≤ aq := by rw [haq1_eq]; nlinarith [haq_pos]
  -- lower-bound the lintegral by the constant `entropyIntegrand aq` times the length
  have hconst_le : ∫⁻ ε in Set.Ioc aq1 aq, entropyIntegrand aq F P ∂volume
      ≤ ∫⁻ ε in Set.Ioc aq1 aq, entropyIntegrand ε F P ∂volume := by
    refine setLIntegral_mono' measurableSet_Ioc (fun ε hε => ?_)
    exact entropyIntegrand_antitone_eps hε.2
  rw [setLIntegral_const, Real.volume_Ioc] at hconst_le
  -- length = aq - aq1 = (1/2) aq, so the constant integral = g(aq) * ofReal((1/2)aq)
  have hlen : aq - aq1 = (1/2 : ℝ) * aq := by rw [haq1_eq]; ring
  rw [hlen] at hconst_le
  -- ofReal(aq) = 2 * ofReal((1/2) aq)
  have hsplit : ENNReal.ofReal aq = 2 * ENNReal.ofReal ((1/2 : ℝ) * aq) := by
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; ring
  calc ENNReal.ofReal aq * entropyIntegrand aq F P
      = 2 * (entropyIntegrand aq F P * ENNReal.ofReal ((1/2 : ℝ) * aq)) := by
        rw [hsplit]; ring
    _ ≤ 2 * ∫⁻ ε in Set.Ioc aq1 aq, entropyIntegrand ε F P ∂volume := by
        gcongr

/-- **Dyadic entropy series dominated by the entropy integral.**

For `δ > 0`, the dyadic series `∑_q (1/2)^q·δ · √(log N_{[]}((1/2)^q·δ))`
(the `q`-th term covering the interval whose right endpoint is `(1/2)^q·δ`,
the head term `q = 0` covering `(δ/2, δ]`) is bounded by twice the bracketing
entropy integral `J_{[]}(δ, F, L_2(P))`.

The factor `2` is exact: on each dyadic interval `Ioc ((1/2)^{q+1}·δ) ((1/2)^q·δ)`
the integrand is `≥` its right-endpoint value (antitonicity in `ε`), and the
interval length `(1/2)^{q+1}·δ` is exactly half the dyadic weight `(1/2)^q·δ`;
summing the disjoint pieces, whose union is `Ioc 0 δ`, reassembles the integral.

Reference: vdV §19.6 p.286-288 (dyadic entropy series vs entropy integral;
implicit in the proof of Lemma 19.34 / Theorem 19.5). -/
theorem dyadic_sum_le_bracketingEntropyIntegral
    {F : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hδ : 0 < δ) :
    ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ) * entropyIntegrand ((1/2 : ℝ)^q * δ) F P
      ≤ 2 * bracketingEntropyIntegral δ F P := by
  -- intervals and their basic properties
  set I : ℕ → Set ℝ := fun q => Set.Ioc ((1/2 : ℝ)^(q+1) * δ) ((1/2 : ℝ)^q * δ) with hI
  have hI_meas : ∀ q, MeasurableSet (I q) := fun q => measurableSet_Ioc
  -- strict antitonicity of the dyadic scale gives pairwise disjointness
  have hscale_anti : ∀ {m n : ℕ}, m ≤ n → (1/2 : ℝ)^n * δ ≤ (1/2 : ℝ)^m * δ := by
    intro m n hmn
    apply mul_le_mul_of_nonneg_right _ hδ.le
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hI_disj : Pairwise (Function.onFun Disjoint I) := by
    intro m n hmn
    -- WLOG m < n; then I n ⊆ Iic (aₙ) ⊆ Iic (a_{m+1}) and I m ⊆ Ioi (a_{m+1})
    wlog hlt : m < n generalizing m n
    · exact (this hmn.symm (by omega)).symm
    rw [Function.onFun, Set.disjoint_left]
    intro x hxm hxn
    simp only [hI, Set.mem_Ioc] at hxm hxn
    -- x > a_{m+1} from I m, but x ≤ aₙ ≤ a_{m+1} from I n (since m+1 ≤ n)
    have : x ≤ (1/2 : ℝ)^(m+1) * δ := le_trans hxn.2 (hscale_anti (by omega))
    exact absurd hxm.1 (not_lt.mpr this)
  -- bound termwise, then sum, then collapse the disjoint union to the integral
  calc ∑' q : ℕ, ENNReal.ofReal ((1/2 : ℝ)^q * δ) * entropyIntegrand ((1/2 : ℝ)^q * δ) F P
      ≤ ∑' q : ℕ, 2 * ∫⁻ ε in I q, entropyIntegrand ε F P ∂volume :=
        ENNReal.tsum_le_tsum (fun q => dyadic_term_le_two_setLIntegral hδ q)
    _ = 2 * ∑' q : ℕ, ∫⁻ ε in I q, entropyIntegrand ε F P ∂volume := by
        rw [ENNReal.tsum_mul_left]
    _ = 2 * ∫⁻ ε in ⋃ q, I q, entropyIntegrand ε F P ∂volume := by
        rw [lintegral_iUnion hI_meas hI_disj]
    _ = 2 * bracketingEntropyIntegral δ F P := by
        rw [hI, iUnion_dyadic_Ioc_eq hδ, ← bracketingEntropyIntegral_eq_setLIntegral]

/-! ## Monotonicity of the entropy quantities in the function class

These three lemmas (`*_mono_class`) say that enlarging the class `F` can only
increase its bracketing number, entropy integrand, and entropy integral: a
cover of the larger class restricts to a cover of the smaller one. They are
reusable `Bracketing`-layer infrastructure — any localization argument that
passes to a sub-class (e.g. restricting to `{f − f₀ : ‖f − f₀‖ < δ}`) needs
them. -/

/-- **Monotonicity of the bracketing number in the class.**
If `F' ⊆ F''` then `N_{[]}(ε, F', L_r(P)) ≤ N_{[]}(ε, F'', L_r(P))`: every
ε-bracketing cover of the larger class `F''` is in particular a cover of the
smaller class `F'`, so the infimum defining `bracketingNumber ε F'` ranges over
a superset of admissible sizes. Clone of `bracketingNumber_antitone_eps`,
restricting the cover via `HasFiniteBracketingCover.mono`. -/
lemma bracketingNumber_mono_class
    {F' F'' : Set (Ω → ℝ)} {ε : ℝ} {r : ℝ≥0∞} {P : Measure Ω} (hF' : F' ⊆ F'') :
    bracketingNumber ε F' r P ≤ bracketingNumber ε F'' r P := by
  unfold bracketingNumber
  refine iInf_mono fun k => ?_
  refine iInf_mono' fun hk => ?_
  obtain ⟨l, u, hbr, hcov⟩ := hk
  exact ⟨⟨l, u, hbr, fun f hf => hcov f (hF' hf)⟩, le_rfl⟩

/-- **Monotonicity of the entropy integrand in the class.**
`F' ⊆ F'' → entropyIntegrand ε F' P ≤ entropyIntegrand ε F'' P`, from
`bracketingNumber_mono_class` and `entropyWeight_mono`. Pattern of
`entropyIntegrand_antitone_eps`. -/
lemma entropyIntegrand_mono_class
    {F' F'' : Set (Ω → ℝ)} {P : Measure Ω} {ε : ℝ} (hF' : F' ⊆ F'') :
    entropyIntegrand ε F' P ≤ entropyIntegrand ε F'' P :=
  entropyWeight_mono (bracketingNumber_mono_class hF')

/-- **Monotonicity of the entropy integral in the class.**
`F' ⊆ F'' → J_{[]}(δ, F', L²(P)) ≤ J_{[]}(δ, F'', L²(P))`, from
`entropyIntegrand_mono_class` integrated over `Ioc 0 δ` via `setLIntegral_mono'`. -/
lemma bracketingEntropyIntegral_mono_class
    {F' F'' : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hF' : F' ⊆ F'') :
    bracketingEntropyIntegral δ F' P ≤ bracketingEntropyIntegral δ F'' P := by
  rw [bracketingEntropyIntegral_eq_setLIntegral, bracketingEntropyIntegral_eq_setLIntegral]
  exact setLIntegral_mono' measurableSet_Ioc (fun ε _ => entropyIntegrand_mono_class hF')

/-! ## Difference-class entropy bounds (localization input)

vdV Lemma 19.31 (proved at the cover level in `DonskerBracketing`) gives
`N_{[]}(η, F − F) ≤ N_{[]}(η/2, F)²`. The two lemmas below turn that combinatorial
bound into the analytic facts the localization needs:
`entropyWeight (N²) ≤ √2 · entropyWeight N`, and the resulting entropy-integral
proportionality `J_{[]}(δ, F − F) ≤ 2√2 · J_{[]}(δ, F)` (the factor `2`
from the `η/2`-scale change of variables, the `√2` from squaring the count).

They are stated abstractly over an auxiliary class `G` and a *cover-lifting*
hypothesis (the size-`k → k²` map that `hasFiniteBracketingCover_difference_class`
realizes for `G = F − F`), so they live in `Bracketing` without referencing the
difference class by name; `DonskerBracketing` instantiates them. -/

/-- **Squaring the bracketing count costs at most a factor `√2` in the weight.**
`entropyWeight (N²) ≤ √2 · entropyWeight N`. For `N = ⊤` both sides are `⊤`;
for finite `N = n`, `1 + n² ≤ (1 + n)²` gives `log(1 + n²) ≤ 2 log(1 + n)`, hence
`√(log(1 + n²)) ≤ √2 · √(log(1 + n))`. -/
lemma entropyWeight_sq_le (N : ℕ∞) :
    entropyWeight (N ^ 2) ≤ ENNReal.ofReal (Real.sqrt 2) * entropyWeight N := by
  rcases eq_or_ne N ⊤ with hN | hN
  · subst hN
    rw [show (⊤ : ℕ∞) ^ 2 = ⊤ by simp [pow_two], entropyWeight_top]
    rw [ENNReal.mul_top (by positivity : ENNReal.ofReal (Real.sqrt 2) ≠ 0)]
  · obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hN
    rw [show ((n : ℕ∞)) ^ 2 = ((n ^ 2 : ℕ) : ℕ∞) by push_cast; ring,
      entropyWeight_coe, entropyWeight_coe, ← ENNReal.ofReal_mul (Real.sqrt_nonneg 2),
      ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    -- `log(1 + n²) ≤ 2 * log(1 + n)`
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hsq : (1 : ℝ) + ((n : ℝ) ^ 2) ≤ (1 + (n : ℝ)) ^ 2 := by nlinarith [hnn]
    have hpos : (0 : ℝ) < 1 + ((n : ℝ) ^ 2) := by positivity
    calc Real.log (1 + ((n ^ 2 : ℕ) : ℝ))
        = Real.log (1 + (n : ℝ) ^ 2) := by push_cast; ring_nf
      _ ≤ Real.log ((1 + (n : ℝ)) ^ 2) := Real.log_le_log hpos hsq
      _ = 2 * Real.log (1 + (n : ℝ)) := by
          rw [Real.log_pow]; push_cast; ring

/-- **Abstract difference-class bracketing-number bound.**
If every size-`k` `α`-bracketing cover of `F'` can be lifted to a size-`k * k`
`β`-bracketing cover of an auxiliary class `G` (the `Fin k → Fin (k*k)` pairing
of `hasFiniteBracketingCover_difference_class`), and `F'` has a finite
`α`-cover, then `N_{[]}(β, G) ≤ N_{[]}(α, F')²`.

The minimal `α`-cover of `F'` (`exists_minimal_bracketingCover`) has size
`N_{[]}(α, F')`; lifting it gives a `β`-cover of `G` of size `N²`, which the
infimum `N_{[]}(β, G)` undercuts. -/
lemma bracketingNumber_le_sq_of_cover_lift
    {F' G : Set (Ω → ℝ)} {α β : ℝ} {P : Measure Ω}
    (hF'cover : HasFiniteBracketingCover F' α 2 P)
    (hlift : ∀ k : ℕ, (∃ l u : Fin k → Ω → ℝ,
          (∀ i, IsEpsBracket α (l i) (u i) 2 P) ∧
          (∀ f ∈ F', ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)) →
        ∃ l u : Fin (k * k) → Ω → ℝ,
          (∀ i, IsEpsBracket β (l i) (u i) 2 P) ∧
          (∀ h ∈ G, ∃ i, ∀ x, l i x ≤ h x ∧ h x ≤ u i x)) :
    bracketingNumber β G 2 P ≤ (bracketingNumber α F' 2 P) ^ 2 := by
  obtain ⟨k, l, u, hbr, hcov, hk_eq⟩ := exists_minimal_bracketingCover hF'cover
  obtain ⟨l', u', hbr', hcov'⟩ := hlift k ⟨l, u, hbr, hcov⟩
  rw [hk_eq]
  -- `N(β, G) ≤ k*k = k^2`
  refine le_trans ?_ (le_of_eq (by push_cast; ring :
    ((k * k : ℕ) : ℕ∞) = ((k : ℕ∞)) ^ 2))
  unfold bracketingNumber
  exact iInf_le_of_le (k * k) (iInf_le_of_le ⟨l', u', hbr', hcov'⟩ le_rfl)

/-- The entropy integrand `ε ↦ entropyIntegrand ε F P` is antitone in `ε`
(`entropyIntegrand_antitone_eps`), hence measurable — the side condition
`setLIntegral_map` / `lintegral_const_mul` need for the change-of-variables and
constant pull-out in `bracketingEntropyIntegral_diff_le`. -/
lemma measurable_entropyIntegrand (F : Set (Ω → ℝ)) (P : Measure Ω) :
    Measurable (fun ε => entropyIntegrand ε F P) :=
  Antitone.measurable (fun _ _ h => entropyIntegrand_antitone_eps h)

/-- **Change of variables for the `ε/2` scale shift on `(0, δ]`.**
`∫⁻ ε in Ioc 0 δ, g (ε/2) = 2 · ∫⁻ u in Ioc 0 (δ/2), g u`, for measurable `g`.
Substitute `u = ε/2` (equivalently push forward by `(2 · ·)`): with
`Real.map_volume_mul_left`, `map (2 · ·) volume = (1/2) • volume`, and
`(2 · ·) ⁻¹' Ioc 0 δ = Ioc 0 (δ/2)`. -/
lemma setLIntegral_Ioc_comp_half {δ : ℝ}
    {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ε in Set.Ioc (0 : ℝ) δ, g (ε / 2) ∂volume
      = 2 * ∫⁻ u in Set.Ioc (0 : ℝ) (δ / 2), g u ∂volume := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hmap : Measurable (fun x : ℝ => 2 * x) := measurable_const_mul 2
  have hpre : (fun x : ℝ => 2 * x) ⁻¹' Set.Ioc (0 : ℝ) δ = Set.Ioc (0 : ℝ) (δ / 2) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2'⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2'⟩; exact ⟨by linarith, by linarith⟩
  -- Apply `setLIntegral_map` with integrand `fun y => g (y/2)`, map `(2 * ·)`.
  have key := setLIntegral_map (μ := volume) (s := Set.Ioc (0 : ℝ) δ)
    (f := fun y : ℝ => g (y / 2))
    (g := fun x : ℝ => (2 : ℝ) * x) measurableSet_Ioc (hg.comp (measurable_id.div_const 2)) hmap
  -- LHS: push forward by `(2·)`; `map (2·) volume = ofReal |2⁻¹| • volume`.
  rw [Real.map_volume_mul_left h2, setLIntegral_smul_measure, hpre] at key
  -- `g ((2 * x)/2) = g x` collapses the RHS integrand.
  have hgcollapse : (fun x : ℝ => g ((2 * x) / 2)) = g := by
    funext x; congr 1; ring
  rw [hgcollapse] at key
  -- `key : ofReal |2⁻¹| • ∫_{Ioc 0 δ} g(y/2) = ∫_{Ioc 0 (δ/2)} g`.
  have habs : ENNReal.ofReal |(2 : ℝ)⁻¹| = (2 : ℝ≥0∞)⁻¹ := by
    rw [abs_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat]
  rw [habs, smul_eq_mul] at key
  -- `key : 2⁻¹ * ∫_{Ioc 0 δ} g(·/2) = ∫_{Ioc 0 (δ/2)} g`; multiply by `2`.
  rw [← key, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- **Abstract difference-class entropy-integral bound.**
With the same cover-lifting hypothesis as `bracketingNumber_le_sq_of_cover_lift`
holding at *every* scale (`α = ε/2`, `β = ε`), the entropy integral of the
auxiliary class `G` is bounded by `2√2` times that of `F'`:
`J_{[]}(δ, G) ≤ 2√2 · J_{[]}(δ, F')`. The `√2` is the cost of squaring the
count (`entropyWeight_sq_le`); the `2` is the Jacobian of the `ε ↦ ε/2`
change of variables (`setLIntegral_Ioc_comp_half`). -/
lemma bracketingEntropyIntegral_diff_le
    {F' G : Set (Ω → ℝ)} {P : Measure Ω} {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∀ ε : ℝ, 0 < ε → HasFiniteBracketingCover F' (ε / 2) 2 P)
    (hlift : ∀ ε : ℝ, 0 < ε → ∀ k : ℕ, (∃ l u : Fin k → Ω → ℝ,
          (∀ i, IsEpsBracket (ε / 2) (l i) (u i) 2 P) ∧
          (∀ f ∈ F', ∃ i, ∀ x, l i x ≤ f x ∧ f x ≤ u i x)) →
        ∃ l u : Fin (k * k) → Ω → ℝ,
          (∀ i, IsEpsBracket ε (l i) (u i) 2 P) ∧
          (∀ h ∈ G, ∃ i, ∀ x, l i x ≤ h x ∧ h x ≤ u i x)) :
    bracketingEntropyIntegral δ G P
      ≤ ENNReal.ofReal (2 * Real.sqrt 2) * bracketingEntropyIntegral δ F' P := by
  -- Pointwise on `Ioc 0 δ`: `entropyIntegrand ε G ≤ √2 · entropyIntegrand (ε/2) F'`.
  have hpoint : ∀ ε ∈ Set.Ioc (0 : ℝ) δ,
      entropyIntegrand ε G P
        ≤ ENNReal.ofReal (Real.sqrt 2) * entropyIntegrand (ε / 2) F' P := by
    intro ε hε
    have hεpos : 0 < ε := hε.1
    have hNbound : bracketingNumber ε G 2 P ≤ (bracketingNumber (ε / 2) F' 2 P) ^ 2 :=
      bracketingNumber_le_sq_of_cover_lift (hcover ε hεpos) (hlift ε hεpos)
    calc entropyIntegrand ε G P
        = entropyWeight (bracketingNumber ε G 2 P) := rfl
      _ ≤ entropyWeight ((bracketingNumber (ε / 2) F' 2 P) ^ 2) := entropyWeight_mono hNbound
      _ ≤ ENNReal.ofReal (Real.sqrt 2) * entropyWeight (bracketingNumber (ε / 2) F' 2 P) :=
          entropyWeight_sq_le _
      _ = ENNReal.ofReal (Real.sqrt 2) * entropyIntegrand (ε / 2) F' P := rfl
  -- `ofReal (2√2) = ofReal 2 * ofReal √2 = 2 * ofReal √2`.
  have hKsplit : ENNReal.ofReal (2 * Real.sqrt 2)
      = ENNReal.ofReal (Real.sqrt 2) * 2 := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    ring
  rw [bracketingEntropyIntegral_eq_setLIntegral, hKsplit]
  calc ∫⁻ ε in Set.Ioc (0 : ℝ) δ, entropyIntegrand ε G P ∂volume
      ≤ ∫⁻ ε in Set.Ioc (0 : ℝ) δ,
          ENNReal.ofReal (Real.sqrt 2) * entropyIntegrand (ε / 2) F' P ∂volume :=
        setLIntegral_mono' measurableSet_Ioc hpoint
    _ = ENNReal.ofReal (Real.sqrt 2)
          * ∫⁻ ε in Set.Ioc (0 : ℝ) δ, entropyIntegrand (ε / 2) F' P ∂volume := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (Real.sqrt 2)
          * (2 * ∫⁻ u in Set.Ioc (0 : ℝ) (δ / 2), entropyIntegrand u F' P ∂volume) := by
        rw [setLIntegral_Ioc_comp_half (measurable_entropyIntegrand F' P)]
    _ ≤ ENNReal.ofReal (Real.sqrt 2)
          * (2 * ∫⁻ u in Set.Ioc (0 : ℝ) δ, entropyIntegrand u F' P ∂volume) := by
        have hsub : Set.Ioc (0 : ℝ) (δ / 2) ⊆ Set.Ioc (0 : ℝ) δ :=
          Set.Ioc_subset_Ioc_right (by linarith)
        gcongr
    _ = ENNReal.ofReal (Real.sqrt 2) * 2 * bracketingEntropyIntegral δ F' P := by
        rw [bracketingEntropyIntegral_eq_setLIntegral, mul_assoc]

end AsymptoticStatistics.EmpiricalProcess
