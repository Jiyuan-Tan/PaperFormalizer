module
public import StatLean.TimeSeries.ForMathlib.Markov.Chain
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-!
# Two-sided stationary realization of an invariant Markov kernel

The Mathlib pin supplies Ionescu–Tulcea on `ℕ` (`ProbabilityTheory.Kernel.traj`) but no
Kolmogorov extension over `ℤ`, so a two-sided stationary chain cannot be obtained as a
projective limit. This file takes the **natural-extension route instead, which needs no
extension theorem at all**: on a standard Borel state space the time-reversed transition
kernel exists by *disintegration* (`MeasureTheory.Measure.condKernel`), and the two-sided
chain is realized on the concrete space `S × (ℕ → S) × (ℕ → S)` — time-0 value, forward
trajectory (Ionescu–Tulcea for `κ`), and backward trajectory (Ionescu–Tulcea for the
reverse kernel), conditionally independent given time 0.

The single exported interface is `exists_twoSided_stationary_chain`: every finite window
of the constructed `ℤ`-indexed process has the iterated-`compProd` chain law
`chainWindowLaw κ π k`, uniformly in the starting time. Strict stationarity, the Markov
property, and (for autoregression kernels) innovation extraction are all finite-
dimensional consequences of that one equality family, so consumers never touch the
construction.

**Reference.** Natural extension: Rokhlin (1961); the reverse-kernel construction of a
stationary two-sided Markov chain is classical (e.g. Meyn & Tweedie, *Markov Chains and
Stochastic Stability*, ch. 3 notes). Consumed by `Threshold/TAR.lean`
(`exists_stationary_nlAR_of_invariant`, FY §4.1.1) — the last structurally-blocked debt
of the TimeSeries area.

**Bibliographic comments.** The disintegration input is Mathlib's
`Measure.condKernel` (standard Borel); the one-sided trajectory input is
`ProbabilityTheory.Kernel.traj` (Ionescu–Tulcea).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

-- Almost all of the private plumbing below is `Fin`-window and `compProd` bookkeeping that does
-- not touch the standard-Borel/nonemptiness structure of `S`; the section variables carrying it
-- are therefore unused in most of those declarations.
set_option linter.unusedSectionVars false

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]

/-- The **stationary pair law** `(X₀, X₁) ∼ π ⊗ₘ κ` of one chain step started from `π`.
Formalizes the two-dimensional marginal of the stationary chain (edge behavior: no
hypotheses — invariance is only needed for the *reversal* results below). -/
noncomputable def pairLaw (κ : ProbabilityTheory.Kernel S S) (π : Measure S) :
    Measure (S × S) := π ⊗ₘ κ

instance (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] : IsProbabilityMeasure (pairLaw κ π) := by
  unfold pairLaw; infer_instance

instance (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] :
    IsProbabilityMeasure ((pairLaw κ π).map Prod.swap) :=
  Measure.isProbabilityMeasure_map measurable_swap.aemeasurable

/-- The **time-reversed transition kernel**: the disintegration in the *second*
coordinate of the swapped stationary pair law. On a standard Borel space this exists by
`Measure.condKernel`. Formalizes the backward transition probability
`P(X₀ ∈ · | X₁ = x)` of the stationary chain (edge behavior: for non-invariant `π` it is
still a Markov kernel, just not a chain reversal). -/
noncomputable def reverseKernel (κ : ProbabilityTheory.Kernel S S) (π : Measure S)
    [IsProbabilityMeasure π] [ProbabilityTheory.IsMarkovKernel κ] :
    ProbabilityTheory.Kernel S S :=
  ((pairLaw κ π).map Prod.swap).condKernel

private instance instMarkovReverseKernel {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    [Nonempty S] (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π] :
    IsMarkovKernel (reverseKernel κ π) := by
  unfold reverseKernel; infer_instance

/-- `μ.map g ⊗ₘ η` seen on the source space. -/
private lemma compProd_map_left {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ] {g : α → β} (hg : Measurable g)
    (η : Kernel β γ) [IsSFiniteKernel η] :
    (μ.map g) ⊗ₘ η = (μ ⊗ₘ (η.comap g hg)).map (Prod.map g id) := by
  have hmap : Measurable (Prod.map g (id : γ → γ)) := hg.prodMap measurable_id
  ext s hs
  rw [Measure.compProd_apply hs, Measure.map_apply hmap hs,
    Measure.compProd_apply (hs.preimage hmap),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hg]
  rfl

-- the coordinate of `Fin.cons x w` at the last index
private lemma measurable_consLast (k : ℕ) :
    Measurable fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) (Fin.last k) := by
  cases k with
  | zero => simpa using measurable_fst
  | succ k => simpa using! (measurable_pi_apply (Fin.last k)).comp measurable_snd

private lemma measurable_finCons (k : ℕ) :
    Measurable fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) := by
  rw [measurable_pi_iff]
  refine Fin.cases ?_ ?_
  · simpa using measurable_fst
  · exact fun i => by simpa using! (measurable_pi_apply i).comp measurable_snd

private lemma measurable_finSnoc' (k : ℕ) :
    Measurable fun p : (Fin k → S) × S => (Fin.snoc p.1 p.2 : Fin (k + 1) → S) := by
  rw [measurable_pi_iff]
  refine Fin.lastCases ?_ ?_
  · simpa using measurable_snd
  · exact fun i => by simpa using! (measurable_pi_apply i).comp measurable_fst

/-- The **iterated-`compProd` chain window law** on `Fin (k+1) → S`: the law of
`(X₀, …, X_k)` for the chain started from `π`. Formalizes the finite-dimensional
distributions of the stationary chain; `k = 0` is the marginal `π` itself. -/
noncomputable def chainWindowLaw (κ : ProbabilityTheory.Kernel S S) (π : Measure S) :
    (k : ℕ) → Measure (Fin (k + 1) → S)
  | 0 => π.map (fun x _ => x)
  | (k + 1) =>
      ((chainWindowLaw κ π k) ⊗ₘ
          (κ.comap (fun w => w (Fin.last k)) (measurable_pi_apply _))).map
        (fun wx => Fin.snoc wx.1 wx.2)

/-- `chainWindowLaw` is a probability measure.
-- LEAN-ONLY: bookkeeping for the recursion; no scope change -/
theorem isProbabilityMeasure_chainWindowLaw
    (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π] (k : ℕ) :
    IsProbabilityMeasure (chainWindowLaw κ π k) := by
  induction k with
  | zero =>
    exact Measure.isProbabilityMeasure_map
      (measurable_pi_lambda _ fun _ => measurable_id).aemeasurable
  | succ k ih =>
    haveI := ih
    exact Measure.isProbabilityMeasure_map (measurable_finSnoc' (k + 1)).aemeasurable

/-- **Reversal disintegration**: under invariance, the swapped pair law disintegrates
through `reverseKernel` with first marginal `π` again.
-- USER-INPUT: κ-invariance of π; the defining property of the stationary reversal -/
theorem pairLaw_swap_eq_compProd_reverseKernel
    (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π]
    (hinv : ProbabilityTheory.Kernel.Invariant κ π) :
    (pairLaw κ π).map Prod.swap = π ⊗ₘ reverseKernel κ π := by
  have hfst : ((pairLaw κ π).map Prod.swap).fst = π := by
    rw [Measure.fst_map_swap]
    change (π ⊗ₘ κ).snd = π
    rw [Measure.snd_compProd]
    exact hinv
  conv_lhs =>
    rw [← Measure.disintegrate ((pairLaw κ π).map Prod.swap)
      ((pairLaw κ π).map Prod.swap).condKernel]
  rw [hfst]
  rfl

/-- The strict-future window kernel: `chainWindowKernel κ k x` is the law of
`(X₁, …, X_k)` for the chain started at `x`. -/
private noncomputable def chainWindowKernel (κ : Kernel S S) : (k : ℕ) → Kernel S (Fin k → S)
  | 0 => Kernel.deterministic (fun _ => Fin.elim0) measurable_const
  | (k + 1) =>
      ((chainWindowKernel κ k) ⊗ₖ
        (κ.comap (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) (Fin.last k))
          (measurable_consLast k))).map (fun p => Fin.snoc p.1 p.2)

private instance instMarkovChainWindowKernel (κ : Kernel S S) [IsMarkovKernel κ] (k : ℕ) :
    IsMarkovKernel (chainWindowKernel κ k) := by
  induction k with
  | zero => rw [chainWindowKernel]; infer_instance
  | succ k ih =>
      rw [chainWindowKernel]
      exact Kernel.IsMarkovKernel.map _ (measurable_finSnoc' k)



section K1
variable (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π]

/-- (K1) The window law is the start law composed with the strict-future window kernel. -/
private theorem chainWindowLaw_eq_compProd (k : ℕ) :
    chainWindowLaw κ π k
      = (π ⊗ₘ chainWindowKernel κ k).map (fun p => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) := by
  induction k with
  | zero =>
    rw [chainWindowLaw, chainWindowKernel, Measure.compProd_deterministic,
      Measure.map_map (measurable_finCons 0) (by fun_prop)]
    refine congrArg (fun f => Measure.map f π) (funext fun x => funext fun i => ?_)
    refine Fin.cases ?_ (fun j => j.elim0) i
    simp
  | succ k ih =>
    haveI := isProbabilityMeasure_chainWindowLaw κ π k
    set η : Kernel (S × (Fin k → S)) S :=
      κ.comap (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S) (Fin.last k))
        (measurable_consLast k) with hη
    have hcomap : (κ.comap (fun w : Fin (k + 1) → S => w (Fin.last k))
        (measurable_pi_apply _)).comap (fun p : S × (Fin k → S) =>
          (Fin.cons p.1 p.2 : Fin (k + 1) → S)) (measurable_finCons k) = η := by
      rw [hη]; rfl
    have hG : Measurable fun p : (S × (Fin k → S)) × S =>
        (Fin.cons p.1.1 (Fin.snoc p.1.2 p.2) : Fin (k + 1 + 1) → S) :=
      (measurable_finCons (k + 1)).comp
        (measurable_fst.fst.prodMk ((measurable_finSnoc' k).comp (measurable_fst.snd.prodMk
          measurable_snd)))
    calc chainWindowLaw κ π (k + 1)
        = ((chainWindowLaw κ π k) ⊗ₘ (κ.comap (fun w => w (Fin.last k))
            (measurable_pi_apply _))).map (fun wx => Fin.snoc wx.1 wx.2) := rfl
      _ = (((π ⊗ₘ chainWindowKernel κ k) ⊗ₘ η).map
            (Prod.map (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) id)).map
            (fun wx => Fin.snoc wx.1 wx.2) := by
            rw [ih, compProd_map_left _ (measurable_finCons k), hcomap]
      _ = ((π ⊗ₘ chainWindowKernel κ k) ⊗ₘ η).map
            (fun p => (Fin.cons p.1.1 (Fin.snoc p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
            rw [Measure.map_map (measurable_finSnoc' (k + 1))
              ((measurable_finCons k).prodMap measurable_id)]
            refine congrArg (fun f => Measure.map f ((π ⊗ₘ chainWindowKernel κ k) ⊗ₘ η))
              (funext fun p => ?_)
            simp only [Function.comp_apply]
            exact (Fin.cons_snoc_eq_snoc_cons p.1.1 p.1.2 p.2).symm
      _ = ((π ⊗ₘ (chainWindowKernel κ k ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm).map
            (fun p => (Fin.cons p.1.1 (Fin.snoc p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
            rw [Measure.compProd_assoc]
      _ = (π ⊗ₘ (chainWindowKernel κ k ⊗ₖ η)).map
            (fun q => (Fin.cons q.1 (Fin.snoc q.2.1 q.2.2) : Fin (k + 1 + 1) → S)) := by
            rw [Measure.map_map hG MeasurableEquiv.prodAssoc.symm.measurable]; rfl
      _ = ((π ⊗ₘ (chainWindowKernel κ k ⊗ₖ η)).map
            (Prod.map id (fun p : (Fin k → S) × S => (Fin.snoc p.1 p.2 : Fin (k + 1) → S)))).map
            (fun p => (Fin.cons p.1 p.2 : Fin (k + 1 + 1) → S)) := by
            rw [Measure.map_map (measurable_finCons (k + 1))
              (measurable_id.prodMap (measurable_finSnoc' k))]; rfl
      _ = (π ⊗ₘ chainWindowKernel κ (k + 1)).map
            (fun p => (Fin.cons p.1 p.2 : Fin (k + 1 + 1) → S)) := by
            rw [chainWindowKernel, ← Measure.compProd_map (measurable_finSnoc' k)]

end K1

section Front
variable (κ : Kernel S S) [IsMarkovKernel κ]

private lemma kernel_compProd_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (κ' : Kernel α β) [IsSFiniteKernel κ']
    (η : Kernel (α × β) γ) [IsSFiniteKernel η] (a : α) :
    (κ' ⊗ₖ η) a = (κ' a) ⊗ₘ (η.comap (Prod.mk a) measurable_prodMk_left) := by
  ext s hs
  rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
  rfl

/-- (K3′) The strict future of the chain started at `x` is the chain started from `κ x`. -/
private theorem chainWindowKernel_succ_apply (k : ℕ) (x : S) :
    chainWindowKernel κ (k + 1) x = chainWindowLaw κ (κ x) k := by
  induction k with
  | zero =>
    have hc : (κ.comap (fun p : S × (Fin 0 → S) =>
        (Fin.cons p.1 p.2 : Fin 1 → S) (Fin.last 0)) (measurable_consLast 0)).comap
        (Prod.mk x) measurable_prodMk_left = Kernel.const (Fin 0 → S) (κ x) := rfl
    rw [chainWindowKernel, Kernel.map_apply _ (measurable_finSnoc' 0), kernel_compProd_apply,
      chainWindowKernel, Kernel.deterministic_apply, hc, Measure.compProd_const,
      Measure.dirac_prod, Measure.map_map (measurable_finSnoc' 0) measurable_prodMk_left,
      chainWindowLaw]
    refine congrArg (fun f => Measure.map f (κ x)) (funext fun y => funext fun i => ?_)
    refine Fin.cases ?_ (fun j => j.elim0) i
    simp [Fin.snoc]
  | succ k ih =>
    have hfin : ∀ w : Fin (k + 1) → S,
        (Fin.cons x w : Fin (k + 1 + 1) → S) (Fin.last (k + 1)) = w (Fin.last k) := by
      intro w; rw [← Fin.succ_last, Fin.cons_succ]
    have hc : (κ.comap (fun p : S × (Fin (k + 1) → S) =>
        (Fin.cons p.1 p.2 : Fin (k + 1 + 1) → S) (Fin.last (k + 1)))
        (measurable_consLast (k + 1))).comap (Prod.mk x) measurable_prodMk_left
          = κ.comap (fun w : Fin (k + 1) → S => w (Fin.last k)) (measurable_pi_apply _) :=
      Kernel.ext fun w => by
        rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply, hfin w]
    rw [chainWindowKernel, Kernel.map_apply _ (measurable_finSnoc' (k + 1)),
      kernel_compProd_apply, hc, ih, chainWindowLaw]

/-- (K3) Front recursion of the window kernel. -/
private theorem chainWindowKernel_succ (k : ℕ) :
    chainWindowKernel κ (k + 1)
      = (κ ⊗ₖ (chainWindowKernel κ k).comap Prod.snd measurable_snd).map
        (fun p => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) := by
  refine Kernel.ext fun x => ?_
  rw [Kernel.map_apply _ (measurable_finCons k), kernel_compProd_apply,
    chainWindowKernel_succ_apply κ k x, chainWindowLaw_eq_compProd κ (κ x) k]
  rfl

/-- (P) Front extension of the window law: peel off the first coordinate. -/
private theorem chainWindowLaw_succ_front (π : Measure S) [IsProbabilityMeasure π] (k : ℕ) :
    chainWindowLaw κ π (k + 1)
      = ((π ⊗ₘ κ) ⊗ₘ (chainWindowKernel κ k).comap Prod.snd measurable_snd).map
        (fun p => (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
  have hG : Measurable fun p : (S × S) × (Fin k → S) =>
      (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp
      (measurable_fst.fst.prodMk ((measurable_finCons k).comp
        (measurable_fst.snd.prodMk measurable_snd)))
  rw [chainWindowLaw_eq_compProd κ π (k + 1), chainWindowKernel_succ κ k,
    Measure.compProd_map (measurable_finCons k),
    Measure.map_map (measurable_finCons (k + 1)) (measurable_id.prodMap (measurable_finCons k)),
    ← Measure.compProd_assoc,
    Measure.map_map hG MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

end Front

section Backward
variable (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π]

private lemma compProd_comap_fst_swap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (κ₁ : Kernel α β) [IsMarkovKernel κ₁]
    (κ₂ : Kernel α γ) [IsMarkovKernel κ₂] :
    (κ₁ ⊗ₖ (κ₂.comap Prod.fst measurable_fst)).map Prod.swap
      = κ₂ ⊗ₖ (κ₁.comap Prod.fst measurable_fst) := by
  refine Kernel.ext fun x => ?_
  have h1 : (κ₂.comap Prod.fst measurable_fst).comap (Prod.mk x) measurable_prodMk_left
      = Kernel.const β (κ₂ x) := rfl
  have h2 : (κ₁.comap Prod.fst measurable_fst).comap (Prod.mk x) measurable_prodMk_left
      = Kernel.const γ (κ₁ x) := rfl
  rw [Kernel.map_apply _ measurable_swap, kernel_compProd_apply, kernel_compProd_apply, h1, h2,
    Measure.compProd_const, Measure.compProd_const, Measure.prod_swap]

/-- (II) **Backward extension**: prepending one `reverseKernel` step to the stationary window
law gives the window law one step longer. -/
private theorem chainWindowLaw_cons_reverseKernel (hinv : Kernel.Invariant κ π) (k : ℕ) :
    ((chainWindowLaw κ π k) ⊗ₘ
        ((reverseKernel κ π).comap (fun w : Fin (k + 1) → S => w 0)
          (measurable_pi_apply 0))).map
      (fun p => (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S)) = chainWindowLaw κ π (k + 1) := by
  set ρ := reverseKernel κ π with hρ
  set W := chainWindowKernel κ k with hW
  have hcons : ∀ p : S × (Fin k → S), (Fin.cons p.1 p.2 : Fin (k + 1) → S) 0 = p.1 :=
    fun p => Fin.cons_zero _ _
  have hc1 : (ρ.comap (fun w : Fin (k + 1) → S => w 0) (measurable_pi_apply 0)).comap
      (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) (measurable_finCons k)
      = ρ.comap Prod.fst measurable_fst :=
    Kernel.ext fun p => by
      rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply, hcons p]
  have hSC : Measurable fun p : (Fin (k + 1) → S) × S =>
      (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.prodMk measurable_fst)
  have hG1 : Measurable fun p : (S × (Fin k → S)) × S =>
      (Fin.cons p.2 (Fin.cons p.1.1 p.1.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.prodMk
      ((measurable_finCons k).comp (measurable_fst.fst.prodMk measurable_fst.snd)))
  have hG2 : Measurable fun q : S × ((Fin k → S) × S) =>
      (Fin.cons q.2.2 (Fin.cons q.1 q.2.1) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.snd.prodMk
      ((measurable_finCons k).comp (measurable_fst.prodMk measurable_snd.fst)))
  have hG3 : Measurable fun r : S × (S × (Fin k → S)) =>
      (Fin.cons r.2.1 (Fin.cons r.1 r.2.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_snd.fst.prodMk
      ((measurable_finCons k).comp (measurable_fst.prodMk measurable_snd.snd)))
  have hG4 : Measurable fun p : (S × S) × (Fin k → S) =>
      (Fin.cons p.1.2 (Fin.cons p.1.1 p.2) : Fin (k + 1 + 1) → S) :=
    (measurable_finCons (k + 1)).comp (measurable_fst.snd.prodMk
      ((measurable_finCons k).comp (measurable_fst.fst.prodMk measurable_snd)))
  calc ((chainWindowLaw κ π k) ⊗ₘ (ρ.comap (fun w : Fin (k + 1) → S => w 0)
          (measurable_pi_apply 0))).map (fun p => (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S))
      = (((π ⊗ₘ W) ⊗ₘ (ρ.comap Prod.fst measurable_fst)).map
          (Prod.map (fun p : S × (Fin k → S) => (Fin.cons p.1 p.2 : Fin (k + 1) → S)) id)).map
          (fun p => (Fin.cons p.2 p.1 : Fin (k + 1 + 1) → S)) := by
          rw [hW, chainWindowLaw_eq_compProd κ π k, compProd_map_left _ (measurable_finCons k),
            hc1]
    _ = ((π ⊗ₘ W) ⊗ₘ (ρ.comap Prod.fst measurable_fst)).map
          (fun p => (Fin.cons p.2 (Fin.cons p.1.1 p.1.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hSC ((measurable_finCons k).prodMap measurable_id)]; rfl
    _ = ((π ⊗ₘ (W ⊗ₖ (ρ.comap Prod.fst measurable_fst))).map
          MeasurableEquiv.prodAssoc.symm).map
          (fun p => (Fin.cons p.2 (Fin.cons p.1.1 p.1.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.compProd_assoc]
    _ = (π ⊗ₘ (W ⊗ₖ (ρ.comap Prod.fst measurable_fst))).map
          (fun q => (Fin.cons q.2.2 (Fin.cons q.1 q.2.1) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hG1 MeasurableEquiv.prodAssoc.symm.measurable]; rfl
    _ = (π ⊗ₘ (ρ ⊗ₖ (W.comap Prod.fst measurable_fst))).map
          (fun r => (Fin.cons r.2.1 (Fin.cons r.1 r.2.2) : Fin (k + 1 + 1) → S)) := by
          rw [← compProd_comap_fst_swap W ρ, Measure.compProd_map measurable_swap,
            Measure.map_map hG3 (measurable_id.prodMap measurable_swap)]
          rfl
    _ = (((π ⊗ₘ ρ) ⊗ₘ (W.comap Prod.fst measurable_fst)).map MeasurableEquiv.prodAssoc).map
          (fun r => (Fin.cons r.2.1 (Fin.cons r.1 r.2.2) : Fin (k + 1 + 1) → S)) := by
          rw [← Measure.compProd_assoc, Measure.map_map MeasurableEquiv.prodAssoc.measurable
            MeasurableEquiv.prodAssoc.symm.measurable]
          simp
    _ = ((π ⊗ₘ ρ) ⊗ₘ (W.comap Prod.fst measurable_fst)).map
          (fun p => (Fin.cons p.1.2 (Fin.cons p.1.1 p.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hG3 MeasurableEquiv.prodAssoc.measurable]; rfl
    _ = (((π ⊗ₘ κ) ⊗ₘ (W.comap Prod.snd measurable_snd)).map (Prod.map Prod.swap id)).map
          (fun p => (Fin.cons p.1.2 (Fin.cons p.1.1 p.2) : Fin (k + 1 + 1) → S)) := by
          rw [hρ, ← pairLaw_swap_eq_compProd_reverseKernel κ π hinv]
          show ((pairLaw κ π).map Prod.swap ⊗ₘ _).map _ = _
          rw [compProd_map_left _ measurable_swap]
          rfl
    _ = ((π ⊗ₘ κ) ⊗ₘ (W.comap Prod.snd measurable_snd)).map
          (fun p => (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (k + 1 + 1) → S)) := by
          rw [Measure.map_map hG4 (measurable_swap.prodMap measurable_id)]; rfl
    _ = chainWindowLaw κ π (k + 1) := (chainWindowLaw_succ_front κ π k).symm

end Backward

section Traj
open Preorder
variable (κ : Kernel S S) [IsMarkovKernel κ]

/-- The constant kernel family fed to Ionescu–Tulcea. -/
private noncomputable def stepFam (n : ℕ) : Kernel ((i : ↥(Finset.Iic n)) → S) S :=
  κ.comap (fun w => w ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

private instance (n : ℕ) : IsMarkovKernel (stepFam κ n) := by unfold stepFam; infer_instance

/-- Reindexing `Iic n` as `Fin (n+1)`. -/
private def iicToFin (n : ℕ) (w : (i : ↥(Finset.Iic n)) → S) : Fin (n + 1) → S :=
  fun i => w ⟨(i : ℕ), Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp i.isLt)⟩

private lemma measurable_iicToFin (n : ℕ) : Measurable (iicToFin (S := S) n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The Ionescu–Tulcea trajectory law of the chain started from `π`. -/
private noncomputable def trajLaw (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) :
    Measure (ℕ → S) :=
  Kernel.trajMeasure (X := fun _ => S) π (stepFam κ)

/-- (T1) The `Iic n` window of the Ionescu–Tulcea trajectory measure is the chain window law. -/
private theorem trajMeasure_map_window (π : Measure S) [IsProbabilityMeasure π] (n : ℕ) :
    (trajLaw κ π).map (fun ω (i : Fin (n + 1)) => ω (i : ℕ))
      = chainWindowLaw κ π n := by
  haveI hprob : IsProbabilityMeasure (trajLaw κ π) := by rw [trajLaw]; infer_instance
  induction n with
  | zero =>
    have h1 : (trajLaw κ π).map (frestrictLe 0)
        = π.map (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm := by
      rw [trajLaw, Kernel.trajMeasure, Measure.map_comp _ _ (measurable_frestrictLe 0),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
    have h2 : (fun (ω : ℕ → S) (i : Fin 1) => ω (i : ℕ))
        = (iicToFin (S := S) 0) ∘ (frestrictLe 0) := rfl
    rw [h2, ← Measure.map_map (measurable_iicToFin 0) (measurable_frestrictLe 0), h1,
      Measure.map_map (measurable_iicToFin 0)
        (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm.measurable,
      chainWindowLaw]
    refine congrArg (fun f => Measure.map f π) (funext fun x => funext fun i => ?_)
    simp [iicToFin, MeasurableEquiv.piUnique]
  | succ n ih =>
    have hsnoc : Measurable fun p : ((i : ↥(Finset.Iic n)) → S) × S =>
        (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S) :=
      (measurable_finSnoc' (n + 1)).comp
        (((measurable_iicToFin n).comp measurable_fst).prodMk measurable_snd)
    have hpair : Measurable fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1)) :=
      (measurable_frestrictLe n).prodMk (measurable_pi_apply _)
    have hfac : (fun (ω : ℕ → S) (i : Fin (n + 1 + 1)) => ω (i : ℕ))
        = (fun p : ((i : ↥(Finset.Iic n)) → S) × S =>
            (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S))
          ∘ (fun ω => (frestrictLe n ω, ω (n + 1))) := by
      funext ω i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp
      · simp [iicToFin]
    have hih : ((trajLaw κ π).map (frestrictLe n)).map (iicToFin n)
        = chainWindowLaw κ π n := by
      rw [Measure.map_map (measurable_iicToFin n) (measurable_frestrictLe n)]; exact ih
    haveI : IsProbabilityMeasure ((trajLaw κ π).map (frestrictLe n)) :=
      Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
    have key : ((trajLaw κ π).map (frestrictLe n)) ⊗ₘ stepFam κ n
        = (trajLaw κ π).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    haveI : IsProbabilityMeasure ((trajLaw κ π).map (frestrictLe n)) :=
      Measure.isProbabilityMeasure_map (measurable_frestrictLe n).aemeasurable
    have key : ((trajLaw κ π).map (frestrictLe n)) ⊗ₘ stepFam κ n
        = (trajLaw κ π).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    have hcomap : (κ.comap (fun w : Fin (n + 1) → S => w (Fin.last n))
        (measurable_pi_apply _)).comap (iicToFin n) (measurable_iicToFin n) = stepFam κ n := rfl
    calc (trajLaw κ π).map (fun ω (i : Fin (n + 1 + 1)) => ω (i : ℕ))
        = ((trajLaw κ π).map (fun ω => (frestrictLe n ω, ω (n + 1)))).map
            (fun p => (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S)) := by
            rw [hfac, ← Measure.map_map hsnoc hpair]
      _ = (((trajLaw κ π).map (frestrictLe n)) ⊗ₘ stepFam κ n).map
            (fun p => (Fin.snoc (iicToFin n p.1) p.2 : Fin (n + 1 + 1) → S)) := by
            rw [key]
      _ = ((chainWindowLaw κ π n) ⊗ₘ (κ.comap (fun w : Fin (n + 1) → S => w (Fin.last n))
            (measurable_pi_apply _))).map (fun p => (Fin.snoc p.1 p.2 : Fin (n + 1 + 1) → S)) := by
            rw [← hih, compProd_map_left _ (measurable_iicToFin n), hcomap,
              Measure.map_map (measurable_finSnoc' (n + 1))
                ((measurable_iicToFin n).prodMap measurable_id)]
            rfl
      _ = chainWindowLaw κ π (n + 1) := rfl

/-- The Ionescu–Tulcea trajectory kernel of `κ` (index `0` carries the starting point). -/
private noncomputable def trajKernel (κ : Kernel S S) [IsMarkovKernel κ] : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) (stepFam κ) 0).comap
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm
    (MeasurableEquiv.piUnique (fun _ : ↥(Finset.Iic 0) => S)).symm.measurable

private instance : IsMarkovKernel (trajKernel κ) := by unfold trajKernel; infer_instance

private lemma trajLaw_eq (π : Measure S) : trajLaw κ π = (trajKernel κ) ∘ₘ π := by
  rw [trajLaw, Kernel.trajMeasure, trajKernel, ← Kernel.comp_deterministic_eq_comap,
    ← Measure.comp_assoc, Measure.deterministic_comp_eq_map]

private lemma trajLaw_dirac (x : S) : trajLaw κ (Measure.dirac x) = trajKernel κ x := by
  rw [trajLaw_eq]
  exact Measure.dirac_bind (Kernel.measurable _) x

private lemma measurable_finTail (n : ℕ) :
    Measurable (Fin.tail : (Fin (n + 1) → S) → (Fin n → S)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- (T2) The strict future of the trajectory kernel is the chain window kernel. -/
private theorem trajKernel_map_window (n : ℕ) :
    (trajKernel κ).map (fun ω (i : Fin n) => ω ((i : ℕ) + 1)) = chainWindowKernel κ n := by
  have hidx : Measurable fun ω : ℕ → S => fun i : Fin n => ω ((i : ℕ) + 1) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hwin : Measurable fun ω : ℕ → S => fun i : Fin (n + 1) => ω (i : ℕ) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  refine Kernel.ext fun x => ?_
  have hcx : Measurable fun w : Fin n → S => (Fin.cons x w : Fin (n + 1) → S) :=
    (measurable_finCons n).comp (measurable_const.prodMk measurable_id)
  rw [Kernel.map_apply _ hidx]
  have h1 : (trajKernel κ x).map (fun ω (i : Fin (n + 1)) => ω (i : ℕ))
      = chainWindowLaw κ (Measure.dirac x) n := by
    rw [← trajLaw_dirac κ x]; exact trajMeasure_map_window κ (Measure.dirac x) n
  have hd : (Measure.dirac x ⊗ₘ chainWindowKernel κ n)
      = (chainWindowKernel κ n x).map (Prod.mk x) := by
    ext s hs
    rw [Measure.dirac_compProd_apply hs, Measure.map_apply measurable_prodMk_left hs]
  have h2 : chainWindowLaw κ (Measure.dirac x) n
      = (chainWindowKernel κ n x).map (fun w => (Fin.cons x w : Fin (n + 1) → S)) := by
    rw [chainWindowLaw_eq_compProd, hd,
      Measure.map_map (measurable_finCons n) measurable_prodMk_left]
    rfl
  have h3 := congrArg (fun μ : Measure (Fin (n + 1) → S) => μ.map Fin.tail) (h1.trans h2)
  rw [Measure.map_map (measurable_finTail n) hwin,
    Measure.map_map (measurable_finTail n) hcx] at h3
  have h4 : (Fin.tail ∘ fun w : Fin n → S => (Fin.cons x w : Fin (n + 1) → S)) = id :=
    funext fun w => by simp [Fin.tail_cons]
  rw [h4, Measure.map_id] at h3
  rw [← h3]
  rfl

end Traj

section SubWindow
variable (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π]

private lemma measurable_finInit (N : ℕ) :
    Measurable (Fin.init : (Fin (N + 1) → S) → (Fin N → S)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Dropping the last coordinate of a window law. -/
private theorem chainWindowLaw_map_init (N : ℕ) :
    (chainWindowLaw κ π (N + 1)).map Fin.init = chainWindowLaw κ π N := by
  haveI := isProbabilityMeasure_chainWindowLaw κ π N
  rw [show chainWindowLaw κ π (N + 1) = ((chainWindowLaw κ π N) ⊗ₘ
      (κ.comap (fun w : Fin (N + 1) → S => w (Fin.last N)) (measurable_pi_apply _))).map
      (fun wx => (Fin.snoc wx.1 wx.2 : Fin (N + 1 + 1) → S)) from rfl,
    Measure.map_map (measurable_finInit (N + 1)) (measurable_finSnoc' (N + 1))]
  have hfac : (Fin.init ∘ fun wx : (Fin (N + 1) → S) × S =>
      (Fin.snoc wx.1 wx.2 : Fin (N + 1 + 1) → S)) = Prod.fst :=
    funext fun wx => by simp
  rw [hfac]
  exact Measure.fst_compProd _ _

/-- Dropping the first coordinate of a *stationary* window law. -/
private theorem chainWindowLaw_map_tail (hinv : Kernel.Invariant κ π) (N : ℕ) :
    (chainWindowLaw κ π (N + 1)).map Fin.tail = chainWindowLaw κ π N := by
  have hG : Measurable fun p : (S × S) × (Fin N → S) =>
      (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (N + 1 + 1) → S) :=
    (measurable_finCons (N + 1)).comp
      (measurable_fst.fst.prodMk ((measurable_finCons N).comp
        (measurable_fst.snd.prodMk measurable_snd)))
  have hH : Measurable fun p : (S × S) × (Fin N → S) =>
      (Fin.cons p.1.2 p.2 : Fin (N + 1) → S) :=
    (measurable_finCons N).comp (measurable_fst.snd.prodMk measurable_snd)
  rw [chainWindowLaw_succ_front κ π N, Measure.map_map (measurable_finTail (N + 1)) hG]
  have hfac : (Fin.tail ∘ fun p : (S × S) × (Fin N → S) =>
      (Fin.cons p.1.1 (Fin.cons p.1.2 p.2) : Fin (N + 1 + 1) → S))
      = fun p => (Fin.cons p.1.2 p.2 : Fin (N + 1) → S) :=
    funext fun p => Fin.tail_cons _ _
  rw [hfac, show (fun p : (S × S) × (Fin N → S) => (Fin.cons p.1.2 p.2 : Fin (N + 1) → S))
      = (fun q : S × (Fin N → S) => (Fin.cons q.1 q.2 : Fin (N + 1) → S)) ∘
        (Prod.map Prod.snd id) from rfl,
    ← Measure.map_map (measurable_finCons N) (measurable_snd.prodMap measurable_id),
    ← compProd_map_left _ measurable_snd]
  have hsnd : (π ⊗ₘ κ).map Prod.snd = π := by
    change (π ⊗ₘ κ).snd = π
    rw [Measure.snd_compProd]; exact hinv
  rw [hsnd, ← chainWindowLaw_eq_compProd]

/-- Every sub-window of a stationary window law is again a window law. -/
private theorem chainWindowLaw_map_sub (hinv : Kernel.Invariant κ π) :
    ∀ (N j k : ℕ) (h : j + k ≤ N),
      (chainWindowLaw κ π N).map
          (fun w (i : Fin (k + 1)) => w ⟨j + (i : ℕ), by omega⟩)
        = chainWindowLaw κ π k := by
  intro N
  induction N with
  | zero =>
    intro j k h
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ k = 0 := by omega
    have hid : (fun (w : Fin 1 → S) (i : Fin 1) => w ⟨0 + (i : ℕ), by omega⟩) = id :=
      funext fun w => funext fun i => congrArg w (Fin.ext (by simp))
    rw [hid, Measure.map_id]
  | succ N ih =>
    intro j k h
    have hmeas : ∀ (M m : ℕ) (hM : m + k ≤ M),
        Measurable fun (w : Fin (M + 1) → S) (i : Fin (k + 1)) => w ⟨m + (i : ℕ), by omega⟩ :=
      fun M m hM => measurable_pi_lambda _ fun _ => measurable_pi_apply _
    cases j with
    | succ j =>
      have hle : j + k ≤ N := by omega
      have hfac : (fun (w : Fin (N + 1) → S) (i : Fin (k + 1)) => w ⟨j + (i : ℕ), by omega⟩)
          ∘ (Fin.tail : (Fin (N + 1 + 1) → S) → (Fin (N + 1) → S))
          = fun (w : Fin (N + 1 + 1) → S) (i : Fin (k + 1)) => w ⟨j + 1 + (i : ℕ), by omega⟩ :=
        funext fun w => funext fun i => congrArg w (Fin.ext (by simp; omega))
      rw [← hfac, ← Measure.map_map (hmeas N j hle) (measurable_finTail (N + 1)),
        chainWindowLaw_map_tail κ π hinv N]
      exact ih j k hle
    | zero =>
      by_cases hk : k ≤ N
      · have hfac : (fun (w : Fin (N + 1) → S) (i : Fin (k + 1)) => w ⟨0 + (i : ℕ), by omega⟩)
            ∘ (Fin.init : (Fin (N + 1 + 1) → S) → (Fin (N + 1) → S))
            = fun (w : Fin (N + 1 + 1) → S) (i : Fin (k + 1)) => w ⟨0 + (i : ℕ), by omega⟩ :=
          funext fun w => funext fun i => rfl
        rw [← hfac, ← Measure.map_map (hmeas N 0 (by omega)) (measurable_finInit (N + 1)),
          chainWindowLaw_map_init κ π N]
        exact ih 0 k (by omega)
      · have hkN : k = N + 1 := by omega
        subst hkN
        have hid : (fun (w : Fin (N + 1 + 1) → S) (i : Fin (N + 1 + 1)) =>
            w ⟨0 + (i : ℕ), by omega⟩) = id :=
          funext fun w => funext fun i => congrArg w (Fin.ext (by simp))
        rw [hid, Measure.map_id]

end SubWindow

section Assembly
variable (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π]

private lemma prod_compProd_measure {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) [SFinite μ] (ν : Measure B) [SFinite ν]
    (ζ : Kernel B C) [IsSFiniteKernel ζ] :
    (μ.prod ν) ⊗ₘ (ζ.comap Prod.snd measurable_snd)
      = (μ.prod (ν ⊗ₘ ζ)).map MeasurableEquiv.prodAssoc.symm := by
  have hconst : (Kernel.const A ν) ⊗ₖ (ζ.comap Prod.snd measurable_snd)
      = Kernel.const A (ν ⊗ₘ ζ) :=
    Kernel.ext fun a => by rw [kernel_compProd_apply, Kernel.const_apply]; rfl
  rw [← Measure.compProd_const, ← Measure.compProd_assoc, hconst, Measure.compProd_const]

private lemma prod_map_right {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (κ₁ : Kernel A B) [IsMarkovKernel κ₁]
    (κ₂ : Kernel A C) [IsMarkovKernel κ₂] {f : C → D} (hf : Measurable f) :
    κ₁ ×ₖ (κ₂.map f) = (κ₁ ×ₖ κ₂).map (Prod.map id f) :=
  Kernel.ext fun a => by
    rw [Kernel.prod_apply, Kernel.map_apply _ hf, Kernel.map_apply _ (measurable_id.prodMap hf),
      Kernel.prod_apply, ← Measure.map_prod_map _ _ measurable_id hf, Measure.map_id]

private lemma prod_compProd_kernel {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (κ₁ : Kernel A B) [IsMarkovKernel κ₁]
    (κ₂ : Kernel A C) [IsMarkovKernel κ₂] (η : Kernel (A × C) D) [IsMarkovKernel η]
    (η' : Kernel (A × (B × C)) D) [IsMarkovKernel η'] (hη' : ∀ p, η' p = η (p.1, p.2.2)) :
    κ₁ ×ₖ (κ₂ ⊗ₖ η) = ((κ₁ ×ₖ κ₂) ⊗ₖ η').map MeasurableEquiv.prodAssoc := by
  refine Kernel.ext fun a => ?_
  have hcc : η'.comap (Prod.mk a) measurable_prodMk_left
      = (η.comap (Prod.mk a) measurable_prodMk_left).comap Prod.snd measurable_snd :=
    Kernel.ext fun q => by
      rw [Kernel.comap_apply, Kernel.comap_apply, Kernel.comap_apply, hη']
  rw [Kernel.prod_apply, kernel_compProd_apply,
    Kernel.map_apply _ MeasurableEquiv.prodAssoc.measurable, kernel_compProd_apply,
    Kernel.prod_apply, hcc,
    prod_compProd_measure (κ₁ a) (κ₂ a) (η.comap (Prod.mk a) measurable_prodMk_left),
    Measure.map_map MeasurableEquiv.prodAssoc.measurable
      MeasurableEquiv.prodAssoc.symm.measurable]
  simp

/-- The two-sided window glue: past coordinates (reversed) then the time-`0` value then the
future coordinates. -/
private def twoSidedGlue (n : ℕ) :
    (m : ℕ) → (S × ((Fin n → S) × (Fin m → S))) → (Fin (n + m + 1) → S)
  | 0 => fun p => Fin.cons p.1 p.2.1
  | (m + 1) => fun p =>
      Fin.cons (p.2.2 (Fin.last m)) (twoSidedGlue n m (p.1, (p.2.1, Fin.init p.2.2)))

private lemma measurable_twoSidedGlue (n m : ℕ) : Measurable (twoSidedGlue (S := S) n m) := by
  induction m with
  | zero => exact (measurable_finCons n).comp (measurable_fst.prodMk measurable_snd.fst)
  | succ m ih =>
      exact (measurable_finCons (n + m + 1)).comp
        (((measurable_pi_apply _).comp measurable_snd.snd).prodMk
          (ih.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
            ((measurable_finInit m).comp measurable_snd.snd)))))

private lemma twoSidedGlue_zero (n m : ℕ) (p : S × ((Fin n → S) × (Fin m → S))) :
    twoSidedGlue n m p 0 = (Fin.cons p.1 p.2.2 : Fin (m + 1) → S) (Fin.last m) := by
  cases m with
  | zero => rfl
  | succ m =>
    change (Fin.cons (p.2.2 (Fin.last m))
        (twoSidedGlue n m (p.1, (p.2.1, Fin.init p.2.2))) : Fin (n + m + 1 + 1) → S) 0
      = (Fin.cons p.1 p.2.2 : Fin (m + 1 + 1) → S) (Fin.last (m + 1))
    rw [Fin.cons_zero, ← Fin.succ_last, Fin.cons_succ]

private lemma twoSidedGlue_snoc (n m : ℕ) (x : S) (f : Fin n → S) (b : Fin m → S) (z : S) :
    twoSidedGlue n (m + 1) (x, (f, Fin.snoc b z))
      = Fin.cons z (twoSidedGlue n m (x, (f, b))) := by
  rw [twoSidedGlue]
  simp

/-- (J) **Two-sided window law**: the forward and backward trajectory windows, glued through the
shared time-`0` value, carry the stationary chain window law. -/
private theorem twoSided_window_law (hinv : Kernel.Invariant κ π) (n : ℕ) :
    ∀ m : ℕ, (π ⊗ₘ (chainWindowKernel κ n ×ₖ chainWindowKernel (reverseKernel κ π) m)).map
        (twoSidedGlue n m) = chainWindowLaw κ π (n + m) := by
  intro m
  induction m with
  | zero =>
    have hfac : (twoSidedGlue (S := S) n 0)
        = (fun q : S × (Fin n → S) => (Fin.cons q.1 q.2 : Fin (n + 1) → S)) ∘
          (Prod.map id Prod.fst) := rfl
    rw [hfac, ← Measure.map_map (measurable_finCons n) (measurable_id.prodMap measurable_fst),
      ← Measure.compProd_map measurable_fst]
    rw [show (chainWindowKernel κ n ×ₖ chainWindowKernel (reverseKernel κ π) 0).map Prod.fst
        = chainWindowKernel κ n from by
      rw [← Kernel.fst_eq]; exact Kernel.fst_prod _ _]
    exact (chainWindowLaw_eq_compProd κ π n).symm
  | succ m ih =>
    set ρ := reverseKernel κ π with hρ
    set K1 := chainWindowKernel κ n with hK1
    set K2 := chainWindowKernel ρ m with hK2
    set ηm : Kernel (S × (Fin m → S)) S :=
      ρ.comap (fun q : S × (Fin m → S) => (Fin.cons q.1 q.2 : Fin (m + 1) → S) (Fin.last m))
        (measurable_consLast m) with hηm
    set ηm' : Kernel (S × ((Fin n → S) × (Fin m → S))) S :=
      ηm.comap (fun p : S × ((Fin n → S) × (Fin m → S)) => (p.1, p.2.2))
        (measurable_fst.prodMk measurable_snd.snd) with hηm'
    have hker : K1 ×ₖ chainWindowKernel ρ (m + 1)
        = ((K1 ×ₖ K2) ⊗ₖ ηm').map (fun q => (q.1.1, (Fin.snoc q.1.2 q.2 : Fin (m + 1) → S))) := by
      rw [show chainWindowKernel ρ (m + 1) = (K2 ⊗ₖ ηm).map
            (fun q => (Fin.snoc q.1 q.2 : Fin (m + 1) → S)) from rfl,
        prod_map_right K1 _ (measurable_finSnoc' m),
        prod_compProd_kernel K1 K2 ηm ηm' (fun p => rfl),
        ← Kernel.map_comp_right _ MeasurableEquiv.prodAssoc.measurable
          (measurable_id.prodMap (measurable_finSnoc' m))]
      rfl
    have hglue : ∀ r : S × (((Fin n → S) × (Fin m → S)) × S),
        twoSidedGlue n (m + 1) (r.1, (r.2.1.1, Fin.snoc r.2.1.2 r.2.2))
          = Fin.cons r.2.2 (twoSidedGlue n m (r.1, r.2.1)) := by
      rintro ⟨x, ⟨f, b⟩, z⟩
      exact twoSidedGlue_snoc n m x f b z
    have hcond : (ρ.comap (fun w : Fin (n + m + 1) → S => w 0) (measurable_pi_apply 0)).comap
        (twoSidedGlue n m) (measurable_twoSidedGlue n m) = ηm' :=
      Kernel.ext fun p => by
        rw [Kernel.comap_apply, Kernel.comap_apply, hηm', Kernel.comap_apply, hηm,
          Kernel.comap_apply, twoSidedGlue_zero]
    have hq : Measurable fun q : ((Fin n → S) × (Fin m → S)) × S =>
        (q.1.1, (Fin.snoc q.1.2 q.2 : Fin (m + 1) → S)) :=
      measurable_fst.fst.prodMk ((measurable_finSnoc' m).comp
        (measurable_fst.snd.prodMk measurable_snd))
    have hSC : Measurable fun t : (Fin (n + m + 1) → S) × S =>
        (Fin.cons t.2 t.1 : Fin (n + m + 1 + 1) → S) :=
      (measurable_finCons (n + m + 1)).comp (measurable_snd.prodMk measurable_fst)
    have hFR : Measurable fun r : S × (((Fin n → S) × (Fin m → S)) × S) =>
        (Fin.cons r.2.2 (twoSidedGlue n m (r.1, r.2.1)) : Fin (n + m + 1 + 1) → S) :=
      (measurable_finCons (n + m + 1)).comp
        (measurable_snd.snd.prodMk ((measurable_twoSidedGlue n m).comp
          (measurable_fst.prodMk measurable_snd.fst)))
    have hFC : Measurable fun s : (S × ((Fin n → S) × (Fin m → S))) × S =>
        (Fin.cons s.2 (twoSidedGlue n m s.1) : Fin (n + m + 1 + 1) → S) :=
      (measurable_finCons (n + m + 1)).comp
        (measurable_snd.prodMk ((measurable_twoSidedGlue n m).comp measurable_fst))
    calc (π ⊗ₘ (K1 ×ₖ chainWindowKernel ρ (m + 1))).map (twoSidedGlue n (m + 1))
        = ((π ⊗ₘ ((K1 ×ₖ K2) ⊗ₖ ηm')).map (Prod.map id
            (fun q : ((Fin n → S) × (Fin m → S)) × S =>
              (q.1.1, (Fin.snoc q.1.2 q.2 : Fin (m + 1) → S))))).map
            (twoSidedGlue n (m + 1)) := by
            rw [hker, ← Measure.compProd_map hq]
      _ = (π ⊗ₘ ((K1 ×ₖ K2) ⊗ₖ ηm')).map
            (fun r => Fin.cons r.2.2 (twoSidedGlue n m (r.1, r.2.1))) := by
            rw [Measure.map_map (measurable_twoSidedGlue n (m + 1))
              (measurable_id.prodMap hq)]
            exact congrArg (fun g => Measure.map g (π ⊗ₘ ((K1 ×ₖ K2) ⊗ₖ ηm')))
              (funext fun r => hglue r)
      _ = (((π ⊗ₘ (K1 ×ₖ K2)) ⊗ₘ ηm').map MeasurableEquiv.prodAssoc).map
            (fun r => Fin.cons r.2.2 (twoSidedGlue n m (r.1, r.2.1))) := by
            rw [← Measure.compProd_assoc, Measure.map_map
              MeasurableEquiv.prodAssoc.measurable MeasurableEquiv.prodAssoc.symm.measurable]
            simp
      _ = ((π ⊗ₘ (K1 ×ₖ K2)) ⊗ₘ ηm').map
            (fun s => (Fin.cons s.2 (twoSidedGlue n m s.1) : Fin (n + m + 1 + 1) → S)) := by
            rw [Measure.map_map hFR MeasurableEquiv.prodAssoc.measurable]; rfl
      _ = (((π ⊗ₘ (K1 ×ₖ K2)) ⊗ₘ ηm').map (Prod.map (twoSidedGlue n m) id)).map
            (fun t : (Fin (n + m + 1) → S) × S =>
              (Fin.cons t.2 t.1 : Fin (n + m + 1 + 1) → S)) := by
            rw [Measure.map_map hSC ((measurable_twoSidedGlue n m).prodMap measurable_id)]
            rfl
      _ = ((chainWindowLaw κ π (n + m)) ⊗ₘ (ρ.comap
            (fun w : Fin (n + m + 1) → S => w 0) (measurable_pi_apply 0))).map
            (fun t => (Fin.cons t.2 t.1 : Fin (n + m + 1 + 1) → S)) := by
            rw [← ih, compProd_map_left _ (measurable_twoSidedGlue n m), hcond]
      _ = chainWindowLaw κ π (n + m + 1) :=
            chainWindowLaw_cons_reverseKernel κ π hinv (n + m)

end Assembly

section Final
variable (κ : Kernel S S) [IsMarkovKernel κ] (π : Measure S) [IsProbabilityMeasure π]

private lemma prod_map_map {A B C B' C' : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace B'] [MeasurableSpace C'] (κ₁ : Kernel A B)
    [IsMarkovKernel κ₁] (κ₂ : Kernel A C) [IsMarkovKernel κ₂] {f : B → B'} (hf : Measurable f)
    {g : C → C'} (hg : Measurable g) :
    (κ₁.map f) ×ₖ (κ₂.map g) = (κ₁ ×ₖ κ₂).map (Prod.map f g) :=
  Kernel.ext fun a => by
    rw [Kernel.prod_apply, Kernel.map_apply _ hf, Kernel.map_apply _ hg,
      Kernel.map_apply _ (hf.prodMap hg), Kernel.prod_apply, Measure.map_prod_map _ _ hf hg]

/-- The two-sided process on the concrete model `S × (ℕ → S) × (ℕ → S)`. -/
private noncomputable def twoSidedProc (ω : S × ((ℕ → S) × (ℕ → S))) (t : ℤ) : S :=
  if t = 0 then ω.1 else if 0 < t then ω.2.1 t.toNat else ω.2.2 (-t).toNat

private lemma measurable_twoSidedProc (t : ℤ) :
    Measurable fun ω : S × ((ℕ → S) × (ℕ → S)) => twoSidedProc ω t := by
  unfold twoSidedProc
  split_ifs
  · exact measurable_fst
  · exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_snd)
  · exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_snd)

private lemma twoSidedProc_glue (n : ℕ) :
    ∀ (m : ℕ) (ω : S × ((ℕ → S) × (ℕ → S))) (j : Fin (n + m + 1)),
      twoSidedProc ω ((j : ℕ) - (m : ℤ))
        = twoSidedGlue n m (ω.1, ((fun i : Fin n => ω.2.1 ((i : ℕ) + 1)),
            (fun i : Fin m => ω.2.2 ((i : ℕ) + 1)))) j := by
  intro m
  induction m with
  | zero =>
    intro ω j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [twoSidedProc, twoSidedGlue]
    · have : ((i.succ : Fin (n + 1)) : ℕ) - ((0 : ℕ) : ℤ) = ((i : ℕ) + 1 : ℤ) := by
        simp
      rw [twoSidedGlue]
      simp only [Fin.cons_succ]
      rw [show ((i.succ : Fin (n + 1)) : ℕ) - ((0 : ℕ) : ℤ) = ((i : ℕ) + 1 : ℤ) from this]
      rw [twoSidedProc]
      have h1 : ((i : ℕ) + 1 : ℤ) ≠ 0 := by positivity
      have h2 : (0 : ℤ) < ((i : ℕ) + 1 : ℤ) := by positivity
      rw [if_neg h1, if_pos h2]
      congr 1
  | succ m ih =>
    intro ω j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [twoSidedGlue]
      simp only [Fin.cons_zero]
      rw [twoSidedProc]
      have h1 : ((0 : Fin (n + (m + 1) + 1)) : ℕ) - ((m + 1 : ℕ) : ℤ) ≠ 0 := by simp; omega
      have h2 : ¬ (0 : ℤ) < ((0 : Fin (n + (m + 1) + 1)) : ℕ) - ((m + 1 : ℕ) : ℤ) := by simp
      rw [if_neg h1, if_neg h2]
      congr 1
    · rw [twoSidedGlue]
      simp only [Fin.cons_succ]
      rw [show ((i.succ : Fin (n + (m + 1) + 1)) : ℕ) - ((m + 1 : ℕ) : ℤ)
          = ((i : ℕ) : ℤ) - (m : ℤ) by push_cast [Fin.val_succ]; ring]
      exact ih ω i

/-- (F) **Two-sided realization**, on the `S`-valued model. -/
private theorem twoSidedProc_window_law (hinv : Kernel.Invariant κ π) (n m : ℕ) :
    (π ⊗ₘ ((trajKernel κ) ×ₖ (trajKernel (reverseKernel κ π)))).map
        (fun ω (j : Fin (n + m + 1)) => twoSidedProc ω ((j : ℕ) - (m : ℤ)))
      = chainWindowLaw κ π (n + m) := by
  have hwinF : Measurable fun ω : ℕ → S => fun i : Fin n => ω ((i : ℕ) + 1) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hwinB : Measurable fun ω : ℕ → S => fun i : Fin m => ω ((i : ℕ) + 1) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hE : Measurable fun ω : S × ((ℕ → S) × (ℕ → S)) =>
      (ω.1, ((fun i : Fin n => ω.2.1 ((i : ℕ) + 1)), (fun i : Fin m => ω.2.2 ((i : ℕ) + 1)))) :=
    measurable_fst.prodMk ((hwinF.comp (measurable_fst.comp measurable_snd)).prodMk
      (hwinB.comp (measurable_snd.comp measurable_snd)))
  have hfac : (fun (ω : S × ((ℕ → S) × (ℕ → S))) (j : Fin (n + m + 1)) =>
        twoSidedProc ω ((j : ℕ) - (m : ℤ)))
      = (twoSidedGlue n m) ∘ (fun ω => (ω.1,
          ((fun i : Fin n => ω.2.1 ((i : ℕ) + 1)), (fun i : Fin m => ω.2.2 ((i : ℕ) + 1))))) :=
    funext fun ω => funext fun j => twoSidedProc_glue n m ω j
  rw [hfac, ← Measure.map_map (measurable_twoSidedGlue n m) hE,
    show (fun ω : S × ((ℕ → S) × (ℕ → S)) => (ω.1,
        ((fun i : Fin n => ω.2.1 ((i : ℕ) + 1)), (fun i : Fin m => ω.2.2 ((i : ℕ) + 1)))))
      = Prod.map id (Prod.map (fun ω : ℕ → S => fun i : Fin n => ω ((i : ℕ) + 1))
          (fun ω : ℕ → S => fun i : Fin m => ω ((i : ℕ) + 1))) from rfl,
    ← Measure.compProd_map (hwinF.prodMap hwinB), ← prod_map_map _ _ hwinF hwinB,
    trajKernel_map_window κ n, trajKernel_map_window (reverseKernel κ π) m]
  exact twoSided_window_law κ π hinv n m

end Final

/-- **Two-sided stationary realization** (natural extension, no Kolmogorov-over-`ℤ`).
Given an invariant probability `π` of a Markov kernel `κ` on a standard Borel space,
there is a probability space carrying a `ℤ`-indexed process every finite window of which
has the stationary chain law — uniformly in the starting time, which packages strict
stationarity, the Markov property and the marginals in one equality family.
-- USER-INPUT: κ-invariance of π; FY §2.1 stationary-solution setting -/
theorem exists_twoSided_stationary_chain
    (κ : ProbabilityTheory.Kernel S S) [ProbabilityTheory.IsMarkovKernel κ]
    (π : Measure S) [IsProbabilityMeasure π]
    (hinv : ProbabilityTheory.Kernel.Invariant κ π) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (Y : ℤ → Ω' → S),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (Y t)) ∧
      ∀ (t : ℤ) (k : ℕ),
        μ'.map (fun ω (i : Fin (k + 1)) => Y (t + (i : ℕ)) ω) = chainWindowLaw κ π k := by
  classical
  obtain ⟨F, hFmeas, hFe⟩ :=
    (MeasureTheory.measurableEmbedding_embeddingReal S).exists_measurable_extend
      (measurable_id : Measurable (id : S → S)) (fun _ => ⟨Classical.arbitrary S⟩)
  have hFe' : ∀ x, F (MeasureTheory.embeddingReal S x) = x := fun x => congrFun hFe x
  have hemeas : Measurable (MeasureTheory.embeddingReal S) :=
    MeasureTheory.measurable_embeddingReal S
  set μ0 : Measure (S × ((ℕ → S) × (ℕ → S))) :=
    π ⊗ₘ ((trajKernel κ) ×ₖ (trajKernel (reverseKernel κ π))) with hμ0
  haveI : IsProbabilityMeasure μ0 := by rw [hμ0]; infer_instance
  have hEnc : Measurable fun ω : S × ((ℕ → S) × (ℕ → S)) =>
      fun t : ℤ => MeasureTheory.embeddingReal S (twoSidedProc ω t) :=
    measurable_pi_lambda _ fun t => hemeas.comp (measurable_twoSidedProc t)
  refine ⟨ℤ → ℝ, inferInstance,
    μ0.map (fun ω t => MeasureTheory.embeddingReal S (twoSidedProc ω t)),
    fun t ω => F (ω t), Measure.isProbabilityMeasure_map hEnc.aemeasurable,
    fun t => hFmeas.comp (measurable_pi_apply t), ?_⟩
  intro t k
  have hsmall : Measurable fun ω' : ℤ → ℝ => fun i : Fin (k + 1) => F (ω' (t + (i : ℕ))) :=
    measurable_pi_lambda _ fun _ => hFmeas.comp (measurable_pi_apply _)
  rw [Measure.map_map hsmall hEnc]
  have hcomp : ((fun ω' : ℤ → ℝ => fun i : Fin (k + 1) => F (ω' (t + (i : ℕ)))) ∘
      (fun ω : S × ((ℕ → S) × (ℕ → S)) =>
        fun s : ℤ => MeasureTheory.embeddingReal S (twoSidedProc ω s)))
      = fun ω (i : Fin (k + 1)) => twoSidedProc ω (t + (i : ℕ)) :=
    funext fun ω => funext fun i => hFe' _
  rw [hcomp]
  set m := (-t).toNat with hm
  set n := (t + k).toNat with hn
  set j := (t + (m : ℤ)).toNat with hj
  have hjk : j + k ≤ n + m := by omega
  have hbig : Measurable fun ω : S × ((ℕ → S) × (ℕ → S)) =>
      fun jj : Fin (n + m + 1) => twoSidedProc ω ((jj : ℕ) - (m : ℤ)) :=
    measurable_pi_lambda _ fun _ => measurable_twoSidedProc _
  have hsub : Measurable fun w : Fin (n + m + 1) → S =>
      fun i : Fin (k + 1) => w ⟨j + (i : ℕ), by omega⟩ :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hfac2 : (fun (ω : S × ((ℕ → S) × (ℕ → S))) (i : Fin (k + 1)) =>
        twoSidedProc ω (t + (i : ℕ)))
      = (fun w : Fin (n + m + 1) → S => fun i : Fin (k + 1) => w ⟨j + (i : ℕ), by omega⟩) ∘
        (fun ω => fun jj : Fin (n + m + 1) => twoSidedProc ω ((jj : ℕ) - (m : ℤ))) := by
    refine funext fun ω => funext fun i => ?_
    change twoSidedProc ω (t + (i : ℕ)) = twoSidedProc ω ((↑(j + (i : ℕ)) : ℤ) - (m : ℤ))
    congr 1
    push_cast
    omega
  rw [hfac2, ← Measure.map_map hsub hbig, hμ0, twoSidedProc_window_law κ π hinv n m]
  exact chainWindowLaw_map_sub κ π hinv (n + m) j k hjk

end StatLean.TimeSeries
