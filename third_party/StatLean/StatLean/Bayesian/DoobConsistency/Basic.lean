module
public import StatLean.Bayesian.DoobConsistency.Defs

@[expose] public section

/-!
# Doob consistency: basic properties of the joint experiment

Elementary lemmas about the data model of `Defs.lean`: measurability of the
first-`n`-observations statistic and the filtration properties of the observation
σ-algebras.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.4, p. 149.

**Proof formalization notes.** Pure wiring: coordinate-projection measurability and
monotonicity of `MeasurableSpace.comap` along restriction maps.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

lemma measurable_doobData (n : ℕ) : Measurable (doobData (Θ := Θ) (𝓧 := 𝓧) n) :=
  measurable_pi_lambda _ fun i => (measurable_pi_apply i.val).comp measurable_fst

lemma doobSigma_mono {m n : ℕ} (hmn : m ≤ n) :
    doobSigma (Θ := Θ) (𝓧 := 𝓧) m ≤ doobSigma n := by
  have hr : Measurable (fun x : Fin n → 𝓧 => fun i : Fin m => x (Fin.castLE hmn i)) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hfac : (doobData (Θ := Θ) (𝓧 := 𝓧) m)
      = (fun x : Fin n → 𝓧 => fun i : Fin m => x (Fin.castLE hmn i)) ∘ doobData n := rfl
  change MeasurableSpace.comap _ _ ≤ MeasurableSpace.comap _ _
  rw [hfac, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hr.comap_le

lemma doobSigma_le (n : ℕ) :
    doobSigma (Θ := Θ) (𝓧 := 𝓧) n ≤ (inferInstance : MeasurableSpace ((ℕ → 𝓧) × Θ)) :=
  (measurable_doobData n).comap_le

end StatLean.Bayesian
