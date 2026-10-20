module
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ProductMeasure

@[expose] public section

/-!
# The model calculus — operations on families of probability measures

The compositional operations that build structured statistical models from simpler ones, all
defined on the bare carrier `P : Θ → Measure 𝓧` over an arbitrary parameter type `Θ`:

* `pushforward P T` — the model for the statistic `T(X)`: `θ ↦ (P θ).map T`;
* `observe P κ` — **observation/coarsening** through a θ-free Markov kernel `κ : 𝓧 ⇝ 𝓨`
  (`θ ↦ κ ∘ₘ P θ`): the ignorable-mechanism case covering censoring readouts, missingness
  masks, measurement error and randomized coarsening;
* `mix P K` — **latent-variable marginalization** through a θ-dependent kernel family
  (`θ ↦ K θ ∘ₘ P θ`): mixed effects, frailty, latent classes, mixtures;
* `condProd P K` — the **regression joint law** on `𝓧 × 𝓨`: covariate marginal `P θ` composed
  with response kernel `K θ` (`θ ↦ P θ ⊗ₘ K θ`);
* `iid P n`, `indepProd P`, `iidSeq P` — replication: `n`-fold iid product (`Measure.pi`),
  independent-not-identical product, and the infinite iid sequence (`Measure.infinitePi`).

Reparameterization and restriction are deliberately **not** new definitions — they are function
composition `P ∘ g` and `P ∘ Subtype.val`; their content is the identifiability transfer lemmas
in `Identifiability.Transfer`.

**Reference.** Model construction by transformation, coarsening, mixing, conditioning and
replication: A. C. Davison, *Statistical Models*, Cambridge Series in Statistical and
Probabilistic Mathematics, Cambridge University Press, 2003 (ISBN 0-521-77339-3), Chapter 5
(Models), §5.1–5.2 (verify §). Observation/coarsening as a Markov kernel on the full data:
D. F. Heitjan and D. B. Rubin, "Ignorability and coarse data," *Ann. Statist.* **19** (1991),
no. 4, 2244–2253, §2.

**Proof formalization notes.** Laptop-only data model — definitions only; all lemmas (algebra
of the operations, probability-preservation instances, marginals) live in `Calculus.Compose`
and `Calculus.Marginal`. The θ-free `observe` is the primary observation operation (its laws
are hypothesis-free and it is the case in which identifiability and risk theorems live);
`observe P κ = mix P (fun _ => κ)` definitionally, so nothing is lost. Everything is a thin
wrapper over Mathlib: `Measure.map`, `Measure.bind` (`∘ₘ`), `Measure.compProd` (`⊗ₘ`),
`Measure.pi`, `Measure.infinitePi` — no bespoke measure constructions, hence full
interoperability with the rest of the library and with Mathlib's kernel algebra
(`Model.KernelAgreement`).

**Bibliographic comments.** Randomization/observation channels acting on statistical models go
back to L. Le Cam, "Sufficiency and approximate sufficiency," *Ann. Math. Statist.* **35**
(1964), 1419–1455 (transitions between experiments); latent-structure mixing is classical —
see B. G. Lindsay, *Mixture Models: Theory, Geometry and Applications*, IMS NSF-CBMS Regional
Conference Series **5** (1995), §1 (verify §). The iid replication of an experiment is the
product experiment of asymptotic statistics (Le Cam 1986, Ch. 3).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

variable {Θ : Type*} {𝓧 𝓨 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓨]

/-- **Pushforward model**: the family of laws of the statistic `T` — `θ ↦ (P θ).map T`
(the model for transformed/derived data; TPE2 §1.1, Davison §5 (verify §)). -/
noncomputable def pushforward (P : Θ → Measure 𝓧) (T : 𝓧 → 𝓨) : Θ → Measure 𝓨 :=
  fun θ => (P θ).map T

/-- **Observation/coarsening by a θ-free Markov kernel** (the ignorable-mechanism case,
Heitjan–Rubin §2): the observed-data model `θ ↦ κ ∘ₘ P θ`. Deterministic observation
recovers `pushforward` (`Calculus.Compose.observe_deterministic`). -/
noncomputable def observe (P : Θ → Measure 𝓧) (κ : Kernel 𝓧 𝓨) : Θ → Measure 𝓨 :=
  fun θ => κ ∘ₘ P θ

/-- **Latent-variable marginalization / mixing** by a θ-dependent kernel family: the observed
model `θ ↦ K θ ∘ₘ P θ` when `P` is the latent-variable model and `K θ` the conditional law of
the observation given the latent variable (mixed effects, frailty, latent classes;
Lindsay §1 (verify §)). -/
noncomputable def mix (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨) : Θ → Measure 𝓨 :=
  fun θ => K θ ∘ₘ P θ

/-- **Conditional product (regression joint law)**: covariate marginal `P θ` composed with the
response kernel `K θ`, giving the joint law of `(X, Y)` on `𝓧 × 𝓨` — `θ ↦ P θ ⊗ₘ K θ`
(Davison §5 regression models (verify §)). Its `snd`-marginal is `mix P K`
(`Calculus.Marginal.pushforward_condProd_snd`). -/
noncomputable def condProd (P : Θ → Measure 𝓧) (K : Θ → Kernel 𝓧 𝓨) :
    Θ → Measure (𝓧 × 𝓨) :=
  fun θ => P θ ⊗ₘ K θ

/-- **`n`-fold iid replication**: the model for an iid sample of size `n`,
`θ ↦ (P θ)^{⊗ n}` on `Fin n → 𝓧`, packaged directly as `Measure.pi` (TPE2 §1.1). -/
noncomputable def iid (P : Θ → Measure 𝓧) (n : ℕ) : Θ → Measure (Fin n → 𝓧) :=
  fun θ => Measure.pi fun _ : Fin n => P θ

/-- **Independent, not identically distributed replication** (fixed designs, rows of
triangular arrays): coordinate `i` follows its own family `P i`. -/
noncomputable def indepProd {ι : Type*} [Fintype ι] (P : ι → Θ → Measure 𝓧) :
    Θ → Measure (ι → 𝓧) :=
  fun θ => Measure.pi fun i => P i θ

/-- **Infinite iid sequence model** `θ ↦ (P θ)^{⊗ ℕ}` on `ℕ → 𝓧`, packaged directly as
`Measure.infinitePi` (the sequential-sampling model of asymptotic statistics). -/
noncomputable def iidSeq (P : Θ → Measure 𝓧) [∀ θ, IsProbabilityMeasure (P θ)] :
    Θ → Measure (ℕ → 𝓧) :=
  fun θ => Measure.infinitePi fun _ : ℕ => P θ

end StatLean.StatisticalModels
