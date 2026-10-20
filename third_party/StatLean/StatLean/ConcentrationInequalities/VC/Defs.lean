module
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Data.ENat.Lattice

@[expose] public section

/-!
# VC dimension — shattering, trace family, growth function, empirical fraction

A class of Boolean functions on $\Omega$ is encoded as a class of *sets*
$\mathcal{C} \subseteq \mathcal{P}(\Omega)$ (a classifier is identified with
the set it indicates). A finite set $\Lambda \subseteq \Omega$ is *shattered*
by $\mathcal{C}$ if every subset of $\Lambda$ is cut out by some member:
$\{\Lambda \cap S : S \in \mathcal{C}\} = \mathcal{P}(\Lambda)$. The
*VC dimension* $\mathrm{vc}(\mathcal{C})$ is the supremum of cardinalities of
shattered sets. The *trace family* $\mathcal{C}|_\Lambda$ and *growth
function* $\Pi_{\mathcal{C}}(n)$ count realized restrictions; the *empirical
fraction* $\mu_n(S) = n^{-1}\#\{i : x_i \in S\}$ realizes the empirical
measure used in the $L^2(\mu_n)$ arguments of §8.3.5–8.3.6.

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press: Definition 8.3.1 (shattering, VC dimension),
§8.3.4 Definition 8.3.10 (growth function), §8.3.5 Eq. (8.32) (empirical
measure/fraction).

**Proof formalization notes.** Classes are `Set (Set Ω)` — this serves both
the combinatorial side (the `traceFamily` bridges to Mathlib's
`Finset.Shatters`/`Finset.shatterer`, whose Pajor lemma
`Finset.card_le_card_shatterer` we reuse in `VC/SauerShelah.lean` rather than
re-prove) and the probabilistic side (indicators into `ℝ` via `empFrac`).
`vcDim` is `ℕ∞`-valued: `⊤` when arbitrarily large sets are shattered (HDP's
"largest cardinality, `∞` if no largest exists"). Edge behavior: an *empty*
class shatters nothing (not even `∅`, since no witness set exists), so
`vcDim ∅ = ⨆ over empty = 0` — degenerate but harmless: every downstream
theorem assumes a nonempty class. `empFrac` at `n = 0` is `0` (junk `0⁻¹`
times empty sum). This file is a laptop-only Defs surface: definitions plus
`Iff.rfl`/short API only, everything proved (0-sorry).

**Bibliographic comments.** VC dimension is due to V. N. Vapnik and A. Ya.
Chervonenkis, "On the uniform convergence of relative frequencies of events
to their probabilities," *Theory Probab. Appl.* 16 (1971), 264–280. The
growth function and its polynomial bound trace to the same paper and,
independently, N. Sauer, *J. Combin. Theory Ser. A* 13 (1972), 145–147, and
S. Shelah, *Pacific J. Math.* 41 (1972), 247–261.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*}

/-- **Shattering** (HDP Definition 8.3.1, set-class form): `Λ` is shattered by
`C` iff every subset of `Λ` is realized as `Λ ∩ S` for some `S ∈ C`. -/
def Shatters (C : Set (Set Ω)) (Λ : Finset Ω) : Prop :=
  ∀ T ⊆ Λ, ∃ S ∈ C, (↑Λ : Set Ω) ∩ S = ↑T

/-- **VC dimension** (HDP Definition 8.3.1): the supremum of cardinalities of
shattered finite sets, valued in `ℕ∞` (`⊤` if unbounded). Edge behavior: the
empty class shatters nothing, giving the degenerate value `0`. -/
noncomputable def vcDim (C : Set (Set Ω)) : ℕ∞ :=
  ⨆ (Λ : Finset Ω) (_ : Shatters C Λ), (Λ.card : ℕ∞)

lemma Shatters.mono_left {C C' : Set (Set Ω)} {Λ : Finset Ω}
    (h : C ⊆ C') (hC : Shatters C Λ) : Shatters C' Λ := by
  intro T hT
  obtain ⟨S, hS, hST⟩ := hC T hT
  exact ⟨S, h hS, hST⟩

/-- Subsets of shattered sets are shattered (HDP §8.3.1). -/
lemma Shatters.mono_right {C : Set (Set Ω)} {Λ Λ' : Finset Ω}
    (h : Λ' ⊆ Λ) (hC : Shatters C Λ) : Shatters C Λ' := by
  intro T hT
  obtain ⟨S, hS, hST⟩ := hC T (hT.trans h)
  refine ⟨S, hS, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hxΛ : x ∈ (↑Λ : Set Ω) ∩ S := ⟨Finset.coe_subset.mpr h hx.1, hx.2⟩
    rw [hST] at hxΛ
    exact hxΛ
  · intro x hx
    have hxΛS : x ∈ (↑Λ : Set Ω) ∩ S := by
      rw [hST]
      exact hx
    exact ⟨Finset.coe_subset.mpr hT hx, hxΛS.2⟩

lemma shatters_empty_iff {C : Set (Set Ω)} : Shatters C ∅ ↔ C.Nonempty := by
  constructor
  · intro h
    obtain ⟨S, hS, -⟩ := h ∅ (Finset.Subset.refl _)
    exact ⟨S, hS⟩
  · rintro ⟨S, hS⟩ T hT
    rw [Finset.subset_empty] at hT
    subst hT
    exact ⟨S, hS, by simp⟩

lemma Shatters.card_le_vcDim {C : Set (Set Ω)} {Λ : Finset Ω}
    (h : Shatters C Λ) : (Λ.card : ℕ∞) ≤ vcDim C :=
  le_iSup₂ (f := fun (Λ : Finset Ω) (_ : Shatters C Λ) => (Λ.card : ℕ∞)) Λ h

lemma vcDim_le_iff {C : Set (Set Ω)} {d : ℕ∞} :
    vcDim C ≤ d ↔ ∀ Λ : Finset Ω, Shatters C Λ → (Λ.card : ℕ∞) ≤ d :=
  iSup₂_le_iff

lemma vcDim_mono {C C' : Set (Set Ω)} (h : C ⊆ C') : vcDim C ≤ vcDim C' :=
  iSup₂_le fun _Λ hΛ => (hΛ.mono_left h).card_le_vcDim

/-- Finset/Set coercion helper for trace and symmetric-difference bridges
(LEAN-ONLY). -/
lemma exists_finset_coe_of_subset_coe {Λ : Finset Ω} {s : Set Ω}
    (h : s ⊆ ↑Λ) : ∃ T : Finset Ω, T ⊆ Λ ∧ (↑T : Set Ω) = s := by
  classical
  refine ⟨Λ.filter (· ∈ s), Finset.filter_subset _ _, ?_⟩
  ext x
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe]
  exact ⟨fun hx => hx.2, fun hx => ⟨h hx, hx⟩⟩

open Classical in
/-- **Trace family** `C|_Λ` (HDP §8.3.4): the family of restrictions
`Λ ∩ S`, `S ∈ C`, as a `Finset (Finset Ω)`. Edge behavior: empty class gives
the empty trace family. -/
noncomputable def traceFamily (C : Set (Set Ω)) (Λ : Finset Ω) :
    Finset (Finset Ω) :=
  Λ.powerset.filter fun T => ∃ S ∈ C, (↑Λ : Set Ω) ∩ S = ↑T

lemma mem_traceFamily {C : Set (Set Ω)} {Λ T : Finset Ω} :
    T ∈ traceFamily C Λ ↔ T ⊆ Λ ∧ ∃ S ∈ C, (↑Λ : Set Ω) ∩ S = ↑T := by
  simp [traceFamily, Finset.mem_filter, Finset.mem_powerset]

/-- **Growth function** `Π_C(n)` (HDP Definition 8.3.10): the largest number
of distinct restrictions of `C` to an `n`-point set, `ℕ∞`-valued (`⨆` over
all `n`-point sets; `0` when `Ω` has fewer than `n` points). -/
noncomputable def growthFunction (C : Set (Set Ω)) (n : ℕ) : ℕ∞ :=
  ⨆ (Λ : Finset Ω) (_ : Λ.card = n), ((traceFamily C Λ).card : ℕ∞)

/-- **Empirical fraction** (HDP §8.3.5, Eq. (8.32)): `μ_n(S)` for the
empirical measure of the sample `x`, as a plain real number
`n⁻¹ ∑ᵢ 𝟙_S(xᵢ)`. Edge behavior: `n = 0` gives `0` (junk `0⁻¹` times an
empty sum). Applied at `S := S₁ ∆ S₂` this is the squared empirical
`L²(μ_n)` distance between the indicators of `S₁` and `S₂`. -/
noncomputable def empFrac {n : ℕ} (x : Fin n → Ω) (S : Set Ω) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, S.indicator (fun _ => (1 : ℝ)) (x i)

lemma empFrac_nonneg {n : ℕ} (x : Fin n → Ω) (S : Set Ω) :
    0 ≤ empFrac x S :=
  mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
    (Finset.sum_nonneg fun _i _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) _)

lemma empFrac_le_one {n : ℕ} (x : Fin n → Ω) (S : Set Ω) :
    empFrac x S ≤ 1 := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [empFrac]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hone : ∀ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (x i) ≤ 1 := by
      intro i
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    have h1 : (∑ i, S.indicator (fun _ => (1 : ℝ)) (x i)) ≤ (n : ℝ) := by
      calc (∑ i, S.indicator (fun _ => (1 : ℝ)) (x i))
          ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hone i
        _ = (n : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_one]
    calc empFrac x S
        ≤ (n : ℝ)⁻¹ * (n : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hn'.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hn')

/-- Positivity of the empirical fraction detects a sample point in `S`
(LEAN-ONLY: distinct-trace extraction device for Theorem 8.3.13). -/
lemma empFrac_pos_iff {n : ℕ} [NeZero n] {x : Fin n → Ω} {S : Set Ω} :
    0 < empFrac x S ↔ ∃ i, x i ∈ S := by
  classical
  have hn' : (0 : ℝ) < n :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    have hzero : empFrac x S = 0 := by
      unfold empFrac
      rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
      rw [Set.indicator_apply, if_neg (hno i)]
    rw [hzero] at h
    exact lt_irrefl 0 h
  · rintro ⟨i, hi⟩
    unfold empFrac
    refine mul_pos (inv_pos.mpr hn') ?_
    refine Finset.sum_pos' (fun j _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) _) ?_
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [Set.indicator_apply, if_pos hi]
    norm_num

/-- Measurability of the empirical fraction along a measurable data stream
(LEAN-ONLY regularity). -/
lemma measurable_empFrac [MeasurableSpace Ω] {Ξ : Type*} [MeasurableSpace Ξ]
    {n : ℕ} {X : ℕ → Ξ → Ω} (hX : ∀ i, Measurable (X i)) {S : Set Ω}
    (hS : MeasurableSet S) :
    Measurable fun ξ => empFrac (fun i : Fin n => X i ξ) S := by
  have hsum : Measurable fun ξ =>
      ∑ i : Fin n, S.indicator (fun _ => (1 : ℝ)) (X i ξ) :=
    Finset.measurable_sum (Finset.univ : Finset (Fin n)) fun i _ =>
      (measurable_const.indicator hS).comp (hX i)
  unfold empFrac
  exact hsum.const_mul ((n : ℝ)⁻¹)

end StatLean.ConcentrationInequalities
