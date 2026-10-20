module
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

/-!
# Function classes for empirical-process theory: envelopes and sup-norm

A function class $\mathcal{F} \subseteq \{f : \Omega \to \mathbb{R}\}$ is the
indexing set for the empirical process $f \mapsto \mathbb{G}_n f$. This file
fixes two basic data attached to such a class:

* an **envelope** $F : \Omega \to \mathbb{R}$ dominating every member of the
  class pointwise, i.e. $|f(x)| \le F(x)$ for all $f \in \mathcal{F}$ and all
  $x \in \Omega$. (We write the envelope `G` in the Lean source to avoid a
  clash with the class name `F`.) The envelope controls the tail behaviour of
  the empirical process: a square-integrable envelope, $F \in L^2(P)$, is the
  standard side condition under which the Donsker-class machinery applies.
* the **sup-norm** $\|z\|_{\mathcal{F}} = \sup_{f \in \mathcal{F}} |z(f)|$ of an
  evaluator $z : \{f : \Omega \to \mathbb{R}\} \to \mathbb{R}$, measured in
  $[0, +\infty]$ so the unbounded case is handled cleanly. This is the norm in
  which Glivenko–Cantelli reads $\|\mathbb{P}_n - P\|_{\mathcal{F}} \to 0$ and
  in which Donsker's theorem asserts asymptotic tightness in $\ell^\infty(\mathcal{F})$.

Headline declarations: `IsEnvelope`, `supNormOver`, together with their
monotonicity and basic order lemmas.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series
in Statistical and Probabilistic Mathematics, Cambridge University Press, 1998.
Chapter 19 (Empirical Processes), §19.2 (Donsker classes); the
envelope-tail term appears in Lemma 19.34 (the maximal inequality for the
empirical process), where the integrable/square-integrable envelope enters the
remainder bound.

**Proof formalization notes.** These are definitions plus elementary order
facts, not a theorem with a proof to outline.

* `IsEnvelope F G := ∀ f ∈ F, ∀ x, |f x| ≤ G x` is the pointwise domination
  condition. `IsEnvelope.nonneg` records $F(x) \ge 0$ whenever the class is
  nonempty (it follows from $0 \le |f(x)| \le F(x)$), and `IsEnvelope.mono`
  notes that an envelope for a class is also an envelope for any subclass.
* `supNormOver F z := ⨆ f ∈ F, ENNReal.ofReal |z f|`, valued in
  $\mathbb{R}_{\ge 0}^\infty$. Edge behaviour: the empty class gives
  $\|z\|_\emptyset = 0$ (supremum over the empty index is $\bot = 0$ in
  $[0,+\infty]$). `le_supNormOver` is the defining lower bound
  $|z(f)| \le \|z\|_{\mathcal{F}}$ for each member, and `supNormOver_mono`
  records monotonicity of the sup-norm in the class.

**Bibliographic comments.** The notions of an envelope function for a class and
of the supremum norm over a class indexing an empirical process are standard
infrastructure of empirical-process theory rather than results with a
single seminal origin; they pervade the modern treatment in van der Vaart and
Wellner, *Weak Convergence and Empirical Processes* (Springer, 1996), and the
account in van der Vaart's *Asymptotic Statistics* (1998), Chapter 19. No
attribution to a specific research paper is warranted — these are folklore
definitions.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open scoped ENNReal

variable {Ω : Type*}

/-- A function `G : Ω → ℝ` is an **envelope** for a class `F` if
`|f x| ≤ G x` for every `f ∈ F` and every `x ∈ Ω`.

The envelope's role is to control the tail behaviour of the empirical
process: vdV §19.2 + Lem 19.34 use `G ∈ L^2(P)` (or similar) as a
hypothesis for Donsker-class results.

vdV §19.2: `G_n`'s sample paths are uniformly bounded when `F` has an
integrable envelope; envelope-driven tail conditions appear throughout §19. -/
def IsEnvelope (F : Set (Ω → ℝ)) (G : Ω → ℝ) : Prop :=
  ∀ f ∈ F, ∀ x, |f x| ≤ G x

lemma IsEnvelope.nonneg {F : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hG : IsEnvelope F G) {f : Ω → ℝ} (hf : f ∈ F) (x : Ω) : 0 ≤ G x :=
  (abs_nonneg (f x)).trans (hG f hf x)

lemma IsEnvelope.mono {F F' : Set (Ω → ℝ)} {G : Ω → ℝ}
    (hG : IsEnvelope F G) (hF' : F' ⊆ F) : IsEnvelope F' G :=
  fun f hf x => hG f (hF' hf) x

/-- The **sup-norm** `‖z‖_F = sup_{f ∈ F} |z f|` of an evaluator
`z : (Ω → ℝ) → ℝ` over a class `F`, measured in `ℝ≥0∞` to handle
the unbounded case cleanly.

Edge: `F = ∅ ⇒ 0` (the supremum over an empty index is `⊥ = 0` in
`ℝ≥0∞`).

Used to state the `‖P_n − P‖_F` form of Glivenko–Cantelli conclusions
and the asymptotic-tightness side of Donsker's theorem. -/
noncomputable def supNormOver (F : Set (Ω → ℝ)) (z : (Ω → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ f ∈ F, ENNReal.ofReal |z f|

lemma le_supNormOver {F : Set (Ω → ℝ)} {z : (Ω → ℝ) → ℝ}
    {f : Ω → ℝ} (hf : f ∈ F) :
    ENNReal.ofReal |z f| ≤ supNormOver F z :=
  le_iSup₂ (f := fun f _ => ENNReal.ofReal |z f|) f hf

lemma supNormOver_mono {F F' : Set (Ω → ℝ)} (hF : F ⊆ F') (z : (Ω → ℝ) → ℝ) :
    supNormOver F z ≤ supNormOver F' z :=
  iSup₂_le fun _ hf => le_supNormOver (hF hf)

end AsymptoticStatistics.EmpiricalProcess
