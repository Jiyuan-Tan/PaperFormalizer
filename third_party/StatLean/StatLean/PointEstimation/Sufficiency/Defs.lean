module
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-!
# Sufficient statistics — core data model

A statistic `T : 𝓧 → S` is **sufficient** for a family `P : Θ → Measure 𝓧` when the
conditional distribution of the data given `T` admits a determination that does not
depend on `θ`. This file fixes the three equivalent carriers of that idea used in the
area, plus minimal sufficiency:

* `IsSufficient P T` — the per-event form: for every measurable `A ⊆ 𝓧` there is a
  θ-free measurable `κA : S → ℝ≥0∞` (a determination of `P_θ(A ∣ T = t)`) satisfying
  the defining property of conditional probability under every `P θ`;
* `HasSufficientKernel P T` — the regular-conditional form: a single θ-free Markov
  kernel `Q : S ⇝ 𝓧` disintegrating the graph law of `(T, id)` under every `P θ`,
  `(P θ).map (x ↦ (T x, x)) = ((P θ).map T) ⊗ₘ Q`;
* `IsFactorizedDensity p μ T g h` — the Fisher–Neyman factorization
  `p_θ = (g_θ ∘ T) · h` (`μ`-a.e., for every `θ`) of a dominated family's densities;
* `statLaw P T θ` — the law of the statistic, `(P θ).map T`;
* `IsMinimalSufficient P T` — sufficient, and a.e.-factoring through every other
  sufficient statistic.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.6
(Sufficient Statistics), the definition of a sufficient statistic via θ-free conditional
distributions. (`TPE2 §1.6`.)

**Proof formalization notes.**
* The compProd (graph) form of `HasSufficientKernel` is deliberately stronger-looking
  than the reconstruction form `P θ = Q ∘ₖ' (statLaw)`: taking second marginals recovers
  reconstruction, while the graph form additionally pins the kernel to the fibers
  (`Q t {x | T x = t} = 1` a.e., proved in `Sufficiency.Basic`) — which Basu's theorem
  and the risk-equality theorem need. On standard Borel spaces the two are equivalent.
* `IsSufficient` phrases the defining property via `∫⁻` against `κA ∘ T` on
  `T`-cylinders; `κA ≤ 1` keeps determinations honest sub-probabilities.
* Minimal sufficiency quantifies over competitor statistics `U : 𝓧 → S'` with `S'` in
  a fixed universe; the factoring map is required measurable (as delivered by the
  likelihood-ratio construction) with the identity holding `P θ`-a.e. for every `θ`.

**Bibliographic comments.** Sufficiency is due to R. A. Fisher ("On the mathematical
foundations of theoretical statistics," *Phil. Trans. R. Soc. A* **222** (1922),
309–368); the factorization criterion to J. Neyman ("Sur un teorema concernente le
cosiddette statistiche sufficienti," *Giorn. Ist. Ital. Attuari* **6** (1935), 320–334);
the measure-theoretic theory — dominated families, the equivalent-mixture device, and
the factorization theorem in its modern form — to P. R. Halmos and L. J. Savage
("Application of the Radon–Nikodym theorem to the theory of sufficient statistics,"
*Ann. Math. Statist.* **20** (1949), 225–241). Minimal sufficiency is due to
E. L. Lehmann and H. Scheffé ("Completeness, similar regions, and unbiased estimation,"
*Sankhyā* **10** (1950), 305–340) and R. R. Bahadur ("Sufficiency and statistical
decision functions," *Ann. Math. Statist.* **25** (1954), 423–462).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

universe u

variable {Θ 𝓧 S : Type*} [MeasurableSpace 𝓧] [MeasurableSpace S]

/-- The **law of the statistic** `T` under `P θ`. -/
noncomputable def statLaw (P : Θ → Measure 𝓧) (T : 𝓧 → S) (θ : Θ) : Measure S :=
  (P θ).map T

/-- **Sufficiency, per-event form**: for every measurable event `A` there is a θ-free
measurable determination `κA` of the conditional probability of `A` given `T`, i.e.
`∫⁻_{T⁻¹ B} κA (T x) dP_θ = P_θ (A ∩ T⁻¹ B)` for all measurable `B ⊆ S` and all `θ`. -/
def IsSufficient (P : Θ → Measure 𝓧) (T : 𝓧 → S) : Prop :=
  ∀ ⦃A : Set 𝓧⦄, MeasurableSet A →
    ∃ κA : S → ℝ≥0∞, Measurable κA ∧ (∀ s, κA s ≤ 1) ∧
      ∀ θ, ∀ ⦃B : Set S⦄, MeasurableSet B →
        ∫⁻ x in T ⁻¹' B, κA (T x) ∂(P θ) = P θ (A ∩ T ⁻¹' B)

/-- **Sufficiency, regular-conditional (graph/compProd) form**: a single θ-free Markov
kernel `Q : S ⇝ 𝓧` such that under every `P θ` the joint law of `(T(X), X)` is
`(law of T) ⊗ₘ Q`. This is the conclusion of the classical Euclidean/standard-Borel
sufficiency theorem and the workhorse form for risk arguments. -/
def HasSufficientKernel (P : Θ → Measure 𝓧) (T : 𝓧 → S) : Prop :=
  ∃ Q : Kernel S 𝓧, IsMarkovKernel Q ∧
    ∀ θ, (P θ).map (fun x => (T x, x)) = (statLaw P T θ) ⊗ₘ Q

/-- **Fisher–Neyman factorized densities** (a.e. form): for every `θ`,
`p_θ = (g_θ ∘ T) · h` holds `μ`-almost everywhere. -/
def IsFactorizedDensity (p : Θ → 𝓧 → ℝ≥0∞) (μ : Measure 𝓧) (T : 𝓧 → S)
    (g : Θ → S → ℝ≥0∞) (h : 𝓧 → ℝ≥0∞) : Prop :=
  ∀ θ, p θ =ᵐ[μ] fun x => g θ (T x) * h x

/-- **Minimal sufficiency**: `T` is sufficient and factors `P θ`-a.e. (for every `θ`)
through every sufficient statistic `U`, via a measurable map. -/
def IsMinimalSufficient (P : Θ → Measure 𝓧) (T : 𝓧 → S) : Prop :=
  IsSufficient P T ∧
    ∀ {S' : Type u} [MeasurableSpace S'] (U : 𝓧 → S'), Measurable U →
      IsSufficient P U →
        ∃ H : S' → S, Measurable H ∧ ∀ θ, (fun x => H (U x)) =ᵐ[P θ] T

end StatLean.PointEstimation
