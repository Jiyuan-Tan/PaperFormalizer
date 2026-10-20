module
public import StatLean.ConcentrationInequalities.VC.Defs
public import StatLean.ConcentrationInequalities.ForMathlib.BinomialSumBound
public import Mathlib.Combinatorics.SetFamily.Shatter

@[expose] public section

/-!
# Pajor and Sauer–Shelah lemmas for set-encoded classes

For a class $\mathcal{C} \subseteq \mathcal{P}(\Omega)$ with VC dimension at
most $d$ and any finite $\Lambda \subseteq \Omega$ with $|\Lambda| \le n$,
$$ \bigl|\mathcal{C}|_\Lambda\bigr|
   \;\le\; \#\{T \subseteq \Lambda : \mathcal{C} \text{ shatters } T\}
   \;\le\; \sum_{k=0}^{d} \binom{|\Lambda|}{k}
   \;\le\; \Bigl(\frac{e\,n}{d}\Bigr)^{d}, $$
together with the growth-function bounds
$2^{d} \le \Pi_{\mathcal{C}}(n) \le \sum_{k \le d} \binom{n}{k}$ of
Eq. (8.30).

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.3.2 Lemma 8.3.7 (Pajor), §8.3.3 Lemma 8.3.9
(Sauer–Shelah), §8.3.4 Eq. (8.30) (growth-function bounds).

**Proof formalization notes.** Maximal Mathlib reuse: Pajor's lemma is
`Finset.card_le_card_shatterer` on the `traceFamily` bridge
(`shatters_traceFamily_iff` identifies Mathlib's `Finset.Shatters` of the
trace family with our set-level `Shatters` — beware, `Finset.Shatters` and
our `Shatters` coexist in scope, so Mathlib's must stay dot- or fully
qualified). Mathlib's `Finset.card_shatterer_le_sum_vcDim` requires
`[Fintype Ω]` and is unusable for `Ω = ℝⁿ`; instead we count Λ-relatively:
every trace-shattered `T` is `C`-shattered (hence `T.card ≤ d`) and `T ⊆ Λ`,
so `Finset.card_powersetCard` bounds the count by `∑_{k ≤ d} C(|Λ|, k)`.
The closed form is `sum_choose_le_exp_mul_pow`
(`ForMathlib/BinomialSumBound.lean`). Constants are the book's exactly.
Edge/degenerate behavior: `two_pow_le_growthFunction` needs `[Infinite Ω]`
and attainment of the `ℕ∞`-valued `vcDim` (`exists_shatters_card_eq`) —
nothing downstream consumes it, so it is this file's allowed named-sorry
fallback together with `pajor` decorations; the one lemma Theorem 8.3.13
needs is `card_traceFamily_le_sum_choose`.

**Bibliographic comments.** The counting lemma was found independently by
V. N. Vapnik and A. Ya. Chervonenkis (*Theory Probab. Appl.* 16 (1971),
264–280), N. Sauer (*J. Combin. Theory Ser. A* 13 (1972), 145–147), and
S. Shelah (*Pacific J. Math.* 41 (1972), 247–261). The sharper
"count shattered sets" form is due to A. Pajor, *Sous-espaces $\ell_1^n$ des
espaces de Banach*, Hermann, Paris, 1985.
-/

open Finset

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*}

/-- Bridge between Mathlib's `Finset.Shatters` of the trace family and our
set-level `Shatters` (LEAN-ONLY: encoding bridge, no book content). -/
lemma shatters_traceFamily_iff [DecidableEq Ω] {C : Set (Set Ω)}
    {Λ Λ' : Finset Ω}
    -- LEAN-ONLY: the trace is only faithful on subsets of Λ; encoding-side
    -- condition, no scope change.
    (h : Λ' ⊆ Λ) :
    (traceFamily C Λ).Shatters Λ' ↔ Shatters C Λ' := by
  have hcoe : (↑Λ' : Set Ω) ⊆ ↑Λ := Finset.coe_subset.mpr h
  constructor
  · intro hsh T hT
    obtain ⟨u, hu, huT⟩ := hsh hT
    obtain ⟨huΛ, S, hS, hSeq⟩ := mem_traceFamily.mp hu
    refine ⟨S, hS, ?_⟩
    calc (↑Λ' : Set Ω) ∩ S
        = (↑Λ' ∩ ↑Λ) ∩ S := by rw [Set.inter_eq_self_of_subset_left hcoe]
      _ = ↑Λ' ∩ (↑Λ ∩ S) := by rw [Set.inter_assoc]
      _ = ↑Λ' ∩ ↑u := by rw [hSeq]
      _ = ↑(Λ' ∩ u) := by rw [Finset.coe_inter]
      _ = ↑T := by rw [huT]
  · intro hsh t ht
    obtain ⟨S, hS, hSeq⟩ := hsh t ht
    obtain ⟨U, hUΛ, hUeq⟩ :=
      exists_finset_coe_of_subset_coe
        (Set.inter_subset_left : (↑Λ : Set Ω) ∩ S ⊆ ↑Λ)
    have hcoeq : (↑(Λ' ∩ U) : Set Ω) = ↑t := by
      rw [Finset.coe_inter, hUeq]
      calc (↑Λ' : Set Ω) ∩ (↑Λ ∩ S)
          = (↑Λ' ∩ ↑Λ) ∩ S := by rw [← Set.inter_assoc]
        _ = ↑Λ' ∩ S := by rw [Set.inter_eq_self_of_subset_left hcoe]
        _ = ↑t := hSeq
    exact ⟨U, mem_traceFamily.mpr ⟨hUΛ, S, hS, hUeq.symm⟩,
      Finset.coe_injective hcoeq⟩

open Classical in
/-- **Pajor's lemma** (HDP §8.3.2, Lemma 8.3.7): the trace family has at most
as many members as there are subsets of `Λ` shattered by `C`. Via
`Finset.card_le_card_shatterer` and the `shatters_traceFamily_iff` bridge. -/
theorem pajor [DecidableEq Ω] (C : Set (Set Ω)) (Λ : Finset Ω) :
    (traceFamily C Λ).card ≤ (Λ.powerset.filter fun T => Shatters C T).card := by
  refine (Finset.card_le_card_shatterer (traceFamily C Λ)).trans ?_
  refine Finset.card_le_card ?_
  intro s hs
  rw [Finset.mem_shatterer] at hs
  obtain ⟨t, ht, hst⟩ := hs.exists_superset
  have htΛ : t ⊆ Λ := (mem_traceFamily.mp ht).1
  have hsΛ : s ⊆ Λ := hst.trans htΛ
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsΛ, (shatters_traceFamily_iff hsΛ).mp hs⟩

/-- **Sauer–Shelah, binomial form** (HDP §8.3.3, Lemma 8.3.9, first
inequality): `|C|_Λ| ≤ ∑_{k ≤ d} C(|Λ|, k)` when `vc(C) ≤ d`. Pajor + (every
shattered set has card ≤ d) + `Finset.card_powersetCard`. -/
theorem card_traceFamily_le_sum_choose {C : Set (Set Ω)} {d : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.3, Lemma 8.3.9.
    (hd : vcDim C ≤ (d : ℕ∞)) (Λ : Finset Ω) :
    (traceFamily C Λ).card ≤ ∑ k ∈ Finset.Iic d, Λ.card.choose k := by
  classical
  refine (pajor C Λ).trans ?_
  have hsub : (Λ.powerset.filter fun T => Shatters C T)
      ⊆ (Finset.Iic d).biUnion (fun k => Λ.powersetCard k) := by
    intro T hT
    rw [Finset.mem_filter, Finset.mem_powerset] at hT
    obtain ⟨hTΛ, hShT⟩ := hT
    have hcard : (T.card : ℕ∞) ≤ (d : ℕ∞) := hShT.card_le_vcDim.trans hd
    have hcard' : T.card ≤ d := by exact_mod_cast hcard
    rw [Finset.mem_biUnion]
    exact ⟨T.card, Finset.mem_Iic.mpr hcard',
      Finset.mem_powersetCard.mpr ⟨hTΛ, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun k _ => ?_)
  rw [Finset.card_powersetCard]

/-- **Sauer–Shelah, closed form** (HDP §8.3.3, Lemma 8.3.9, second
inequality): `|C|_Λ| ≤ (e·n/d)^d` for `|Λ| ≤ n`, via
`sum_choose_le_exp_mul_pow` and monotonicity of `Nat.choose` in `n`. -/
theorem card_traceFamily_le_pow {C : Set (Set Ω)} {d n : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.3, Lemma 8.3.9.
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d (nondegenerate dimension); HDP Exercise 0.6 regime.
    (hd1 : 1 ≤ d) {Λ : Finset Ω}
    -- USER-INPUT: sample-size bound |Λ| ≤ n; HDP §8.3.3, Lemma 8.3.9.
    (hΛ : Λ.card ≤ n)
    -- USER-INPUT: d ≤ n (the closed form's regime); HDP Exercise 0.6.
    (hdn : d ≤ n) :
    ((traceFamily C Λ).card : ℝ) ≤ (Real.exp 1 * n / d) ^ d := by
  have h1 : (traceFamily C Λ).card ≤ ∑ k ∈ Finset.Iic d, Λ.card.choose k :=
    card_traceFamily_le_sum_choose hd Λ
  have h2 : (∑ k ∈ Finset.Iic d, Λ.card.choose k)
      ≤ ∑ k ∈ Finset.Iic d, n.choose k :=
    Finset.sum_le_sum fun k _ => Nat.choose_le_choose k hΛ
  have h3 : ((traceFamily C Λ).card : ℝ) ≤ ∑ k ∈ Finset.Iic d, (n.choose k : ℝ) := by
    have hnat : (traceFamily C Λ).card ≤ ∑ k ∈ Finset.Iic d, n.choose k := h1.trans h2
    calc ((traceFamily C Λ).card : ℝ)
        ≤ ((∑ k ∈ Finset.Iic d, n.choose k : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ∑ k ∈ Finset.Iic d, (n.choose k : ℝ) := by push_cast; rfl
  exact h3.trans (sum_choose_le_exp_mul_pow hd1 hdn)

/-- Growth-function upper bound (HDP §8.3.4, Eq. (8.30), right inequality,
`ℕ∞` form): `Π_C(n) ≤ ∑_{k ≤ d} C(n, k)` when `vc(C) ≤ d`. -/
theorem growthFunction_le_sum_choose {C : Set (Set Ω)} {d n : ℕ}
    -- USER-INPUT: VC dimension bound; HDP §8.3.4, Eq. (8.30).
    (hd : vcDim C ≤ (d : ℕ∞)) :
    growthFunction C n ≤ ((∑ k ∈ Finset.Iic d, n.choose k : ℕ) : ℕ∞) := by
  refine iSup₂_le fun Λ hΛ => ?_
  have hc := card_traceFamily_le_sum_choose hd Λ
  rw [hΛ] at hc
  exact_mod_cast hc

/-- Attainment of the `ℕ∞`-valued `vcDim` supremum at a finite value
(LEAN-ONLY: `iSup` attainment in `ℕ∞`, no book content). -/
theorem exists_shatters_card_eq {C : Set (Set Ω)} {d : ℕ}
    -- LEAN-ONLY: a nonempty class shatters ∅, so the iSup ranges over a
    -- nonempty family; no scope change.
    (hC : C.Nonempty)
    -- USER-INPUT: exact finite VC dimension; HDP §8.3.4, Eq. (8.30).
    (hd : vcDim C = (d : ℕ∞)) :
    ∃ Λ : Finset Ω, Shatters C Λ ∧ Λ.card = d := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · exact ⟨∅, shatters_empty_iff.mpr hC, by simp [hd0]⟩
  · by_contra hcon
    push_neg at hcon
    have hub : vcDim C ≤ ((d - 1 : ℕ) : ℕ∞) := by
      rw [vcDim_le_iff]
      intro Λ hΛ
      have hle : (Λ.card : ℕ∞) ≤ (d : ℕ∞) := hd ▸ hΛ.card_le_vcDim
      have hle' : Λ.card ≤ d := by exact_mod_cast hle
      have hne : Λ.card ≠ d := hcon Λ hΛ
      have hdec : Λ.card ≤ d - 1 := by omega
      exact_mod_cast hdec
    rw [hd] at hub
    have hnat : d ≤ d - 1 := by exact_mod_cast hub
    omega

/-- Growth-function lower bound (HDP §8.3.4, Eq. (8.30), left inequality):
`2^d ≤ Π_C(n)` for `n ≥ d = vc(C)`. Decorative for downstream (nothing
consumes it); allowed to degrade to a named sorry. -/
theorem two_pow_le_growthFunction [Infinite Ω] {C : Set (Set Ω)} {d n : ℕ}
    -- LEAN-ONLY: nonempty class so a shattered d-set exists; no scope change.
    (hC : C.Nonempty)
    -- USER-INPUT: exact finite VC dimension; HDP §8.3.4, Eq. (8.30).
    (hd : vcDim C = (d : ℕ∞))
    -- USER-INPUT: n ≥ d so a shattered d-set extends to an n-point set;
    -- HDP §8.3.4, Eq. (8.30). ([Infinite Ω] is LEAN-ONLY: an n-point
    -- superset must exist inside Ω.)
    (hn : d ≤ n) :
    (2 ^ d : ℕ∞) ≤ growthFunction C n := by
  classical
  -- a shattered `d`-set exists at the exact VC dimension
  obtain ⟨Λ₀, hΛ₀sh, hΛ₀card⟩ := exists_shatters_card_eq hC hd
  -- extend it to an `n`-point set (possible since `Ω` is infinite and `d ≤ n`)
  obtain ⟨Λ, hsub, hΛcard⟩ :=
    Infinite.exists_superset_card_eq Λ₀ n (by rw [hΛ₀card]; exact hn)
  -- the trace family shatters `Λ₀` (Mathlib's `Finset.Shatters` via the bridge)
  have hshtrace : (traceFamily C Λ).Shatters Λ₀ :=
    (shatters_traceFamily_iff hsub).mpr hΛ₀sh
  -- so its `Λ₀ ∩ ·` image realizes all `2^d` subsets of `Λ₀`
  have himg : (traceFamily C Λ).image (fun t => Λ₀ ∩ t) = Λ₀.powerset :=
    shatters_iff.mp hshtrace
  have hcard : 2 ^ d ≤ (traceFamily C Λ).card := by
    calc 2 ^ d = 2 ^ Λ₀.card := by rw [hΛ₀card]
      _ = Λ₀.powerset.card := (Finset.card_powerset Λ₀).symm
      _ = ((traceFamily C Λ).image (fun t => Λ₀ ∩ t)).card := by rw [himg]
      _ ≤ (traceFamily C Λ).card := Finset.card_image_le
  have hcast : (2 ^ d : ℕ∞) ≤ ((traceFamily C Λ).card : ℕ∞) := by exact_mod_cast hcard
  exact hcast.trans (le_iSup₂ (f := fun (Λ : Finset Ω) (_ : Λ.card = n) =>
    ((traceFamily C Λ).card : ℕ∞)) Λ hΛcard)

end StatLean.ConcentrationInequalities
