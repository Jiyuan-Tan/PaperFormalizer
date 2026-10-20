module
public import StatLean.StatisticalLearning.Core.Defs

@[expose] public section

/-!
# Rademacher complexity — finite-average definition

The Rademacher complexity of a set of vectors `A ⊆ ℝⁿ` (SSBD Eq. (26.5)),
`R(A) = (1/n) E_{σ∼{±1}ⁿ} sup_{a∈A} ∑ᵢ σᵢ aᵢ`, and its instantiation to a
loss family evaluated on a sample, `R(ℓ∘𝓗∘S)` (SSBD Eq. (26.4)).

**Reference.** SSBD §26.1. Transcriptions:
`notes/statistical_learning/book_statements/ch26-31-appB.md`.

**Formalization notes.**
* The `σ`-expectation is a **finite average over all `2ⁿ` sign patterns**
  (`σ : Fin n → Bool`), not an integral — no measure theory in the definition.
  The bridge to the `signVec` product-measure world of
  `ConcentrationInequalities/Symmetrization/` is
  `Rademacher/Symmetrization.lean`'s `signAvg_eq_integral_signVec`.
* The sup over the class is `sSup` of an **image** (not a real `⨆ a ∈ A`,
  whose junk floor at `0` is a known trap). Edge behavior: `sSup ∅ = 0` and
  `sSup` of an unbounded image is `0` — theorems carry
  nonemptiness/boundedness (typically finiteness) hypotheses.
* This file is a laptop-only Defs surface: definitions only, 0-sorry.

**Bibliographic comments.** Rademacher averages as a complexity measure are
due to V. Koltchinskii, "Rademacher penalties and structural risk
minimization," *IEEE Trans. Inf. Theory* 47 (2001), 1902–1914, and
P. L. Bartlett & S. Mendelson, "Rademacher and Gaussian complexities: risk
bounds and structural results," *JMLR* 3 (2002), 463–482.
-/

open scoped BigOperators

namespace StatLean.StatisticalLearning

variable {n : ℕ} {ι Z : Type*}

/-- The `±1` vector of a Boolean sign pattern: `true ↦ 1`, `false ↦ -1`. -/
def signOf (σ : Fin n → Bool) : Fin n → ℝ :=
  fun i => if σ i then 1 else -1

/-- Average of `g` over all `2ⁿ` sign vectors — the finite-sum reading of
`E_{σ ∼ {±1}ⁿ}[g(σ)]` (SSBD §26.1). -/
noncomputable def signAvg (n : ℕ) (g : (Fin n → ℝ) → ℝ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool, g (signOf σ)

/-- **Rademacher complexity of a set of vectors** `A ⊆ ℝⁿ` (SSBD Eq. (26.5)):
`R(A) = (1/n) E_σ sup_{a ∈ A} ⟨σ, a⟩`, with the sup as `sSup` of the image.
Edge behavior: junk `0` for `A = ∅`, for an unbounded image, or for `n = 0`. -/
noncomputable def radComplexity (A : Set (Fin n → ℝ)) : ℝ :=
  (n : ℝ)⁻¹ * signAvg n (fun ε => sSup ((fun a => ∑ i, ε i * a i) '' A))

/-- The evaluation image `F ∘ S` of a loss/function family on a sample (SSBD
§26.1's `𝓕 ∘ S = {(f(z₁),…,f(zₙ)) : f ∈ 𝓕}`), for an index set `K`. -/
def evalFamily (F : ι → Z → ℝ) (K : Set ι) (s : Sample Z n) :
    Set (Fin n → ℝ) :=
  (fun k => fun i => F k (s i)) '' K

/-- **Empirical Rademacher complexity of a family on a sample** (SSBD
Eq. (26.4)): `R(F ∘ S)`. -/
noncomputable def empRad (F : ι → Z → ℝ) (K : Set ι) (s : Sample Z n) : ℝ :=
  radComplexity (evalFamily F K s)

end StatLean.StatisticalLearning
