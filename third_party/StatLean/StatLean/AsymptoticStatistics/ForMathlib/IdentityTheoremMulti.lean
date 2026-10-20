module
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

/-!
# Multivariate identity theorem on `ℂᵐ`

Two entire functions `F, G : (Fin m → ℂ) → ℂ` that agree on a subset
`U ⊆ Fin m → ℝ` (viewed inside `Fin m → ℂ`) with nonempty interior in
`Fin m → ℝ` are equal everywhere on `Fin m → ℂ`. Mathlib has the
one-dimensional identity theorem (`AnalyticOnNhd.eq_of_frequently_eq`)
but not this multivariate version.

The proof is the classical coordinate induction on `m`: the base case
uses that `Fin 0 → ℂ` is a `Subsingleton`; the inductive step fixes a
real tail close to a point of `interior U`, applies the 1-D theorem on
the head slice to get equality for all complex heads, then applies the
inductive hypothesis on the tail.

The headline declaration is `identity_theorem_complex_pi`.
-/

open Complex Set Filter Topology Metric

namespace AsymptoticStatistics.ForMathlib.IdentityTheoremMulti

/-- The slice map `t ↦ Fin.cons t v` for a fixed tail `v : Fin m → ℂ`
is analytic at every point of `ℂ`. Each component is either the
identity (the `0`-component) or a constant. -/
private lemma analyticAt_cons_left {m : ℕ} (v : Fin m → ℂ) (t₀ : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => (Fin.cons t v : Fin (m + 1) → ℂ)) t₀ := by
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ ?_ i
  · -- 0-th component is the identity `t ↦ t`.
    simpa using! (analyticAt_id : AnalyticAt ℂ (fun t : ℂ => t) t₀)
  · -- `(j + 1)`-th component is the constant `v j`.
    intro j
    simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => v j) t₀)

/-- The slice map `v ↦ Fin.cons t v` for a fixed head `t : ℂ` is
analytic at every point of `Fin m → ℂ`. Each component is either a
constant (component `0`) or a coordinate projection. -/
private lemma analyticAt_cons_right {m : ℕ} (t : ℂ) (v₀ : Fin m → ℂ) :
    AnalyticAt ℂ (fun v : Fin m → ℂ => (Fin.cons t v : Fin (m + 1) → ℂ)) v₀ := by
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin m → ℂ => t) v₀)
  · intro j
    have hproj : AnalyticAt ℂ (fun v : Fin m → ℂ => v j) v₀ :=
      (ContinuousLinearMap.proj (R := ℂ) j).analyticAt v₀
    simpa using hproj

/-- *Multivariate identity theorem on `ℂᵐ`.*

Two entire functions `F, G : (Fin m → ℂ) → ℂ` that agree on a subset
`U ⊆ Fin m → ℝ` (viewed inside `Fin m → ℂ` via `Complex.ofReal`)
with **nonempty interior in `Fin m → ℝ`** are equal everywhere on
`Fin m → ℂ`.

Used for the semiparametric convolution theorem (vdV §25.20). -/
theorem identity_theorem_complex_pi
    {m : ℕ}
    {F G : (Fin m → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F univ)
    (hG : AnalyticOnNhd ℂ G univ)
    (U : Set (Fin m → ℝ))
    (hU : (interior U).Nonempty)
    (hFG : ∀ x ∈ U, F (fun i => (x i : ℂ)) = G (fun i => (x i : ℂ))) :
    ∀ z : Fin m → ℂ, F z = G z := by
  induction m with
  | zero =>
      -- `Fin 0 → ℂ` is a subsingleton; pull through the unique element of `U`.
      intro z
      obtain ⟨x, hx⟩ := hU
      have hxU : x ∈ U := interior_subset hx
      have hcoerce : (fun i => (x i : ℂ)) = z := Subsingleton.elim _ _
      have h := hFG x hxU
      rw [hcoerce] at h
      exact h
  | succ n ih =>
      -- Pick `x₀ ∈ interior U` together with a sup-distance ball
      -- `Metric.ball x₀ ε ⊆ U`.
      obtain ⟨x₀, hx₀⟩ := hU
      obtain ⟨ε, hε, hball⟩ : ∃ ε : ℝ, 0 < ε ∧ Metric.ball x₀ ε ⊆ U := by
        rcases Metric.isOpen_iff.mp isOpen_interior x₀ hx₀ with ⟨ε, hε, hball⟩
        exact ⟨ε, hε, hball.trans interior_subset⟩
      -- Step A. Head-slice equality. For each fixed real tail `v` whose every
      -- coordinate is within `ε` of the corresponding coordinate of `x₀`, and
      -- for every complex `t`, we have `F (Fin.cons t v) = G (Fin.cons t v)`.
      have head_slice : ∀ v : Fin n → ℝ,
          (∀ i, |v i - x₀ i.succ| < ε) →
          ∀ t : ℂ, F (Fin.cons t (fun i => (v i : ℂ))) =
                   G (Fin.cons t (fun i => (v i : ℂ))) := by
        intro v hv
        -- Fix `v`; package the head slice.
        let Fv : ℂ → ℂ := fun t => F (Fin.cons t (fun i => (v i : ℂ)))
        let Gv : ℂ → ℂ := fun t => G (Fin.cons t (fun i => (v i : ℂ)))
        have hFv_an : AnalyticOnNhd ℂ Fv univ := fun t _ =>
          (hF _ (mem_univ _)).comp (analyticAt_cons_left _ t)
        have hGv_an : AnalyticOnNhd ℂ Gv univ := fun t _ =>
          (hG _ (mem_univ _)).comp (analyticAt_cons_left _ t)
        -- They agree at every real `s` near `x₀ 0`. Let `δ` be the available
        -- slack on the head coordinate.
        have h_freq : ∃ᶠ t in 𝓝[≠] ((x₀ 0 : ℂ)), Fv t = Gv t := by
          -- Build the frequently statement via `Complex.ofReal` push.
          -- First, `∃ᶠ s in 𝓝[≠] (x₀ 0 : ℝ), |s - x₀ 0| < ε`.
          have h_real : ∃ᶠ s in 𝓝[≠] (x₀ 0 : ℝ), |s - x₀ 0| < ε := by
            have hev : ∀ᶠ s in 𝓝 (x₀ 0 : ℝ), |s - x₀ 0| < ε := by
              have h0 : |(x₀ 0 : ℝ) - x₀ 0| < ε := by simp [hε]
              exact (continuous_abs.comp
                (continuous_id.sub continuous_const)).continuousAt.eventually_lt
                continuousAt_const h0
            exact (hev.filter_mono nhdsWithin_le_nhds).frequently
          -- Push to ℂ via `Complex.ofReal`.
          have hpush :
              Tendsto (fun s : ℝ => ((s : ℂ))) (𝓝[≠] (x₀ 0 : ℝ))
                (𝓝[≠] (x₀ 0 : ℂ)) := by
            refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
              ((Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds) ?_
            refine eventually_nhdsWithin_of_forall ?_
            intro s hs hcontr
            apply hs
            have hcontr' : (s : ℂ) = ((x₀ 0 : ℝ) : ℂ) := by
              simpa using hcontr
            exact_mod_cast hcontr'
          -- Replace `s` with `ofReal s` in the property predicate, then push.
          have h_real' : ∃ᶠ s : ℝ in 𝓝[≠] (x₀ 0 : ℝ),
              (fun t : ℂ => ∃ s' : ℝ, t = (s' : ℂ) ∧ |s' - x₀ 0| < ε) (s : ℂ) :=
            h_real.mono (fun s hs => ⟨s, rfl, hs⟩)
          have hcomplex : ∃ᶠ t in 𝓝[≠] ((x₀ 0 : ℂ)),
              ∃ s : ℝ, t = (s : ℂ) ∧ |s - x₀ 0| < ε :=
            hpush.frequently h_real'
          refine hcomplex.mono ?_
          rintro t ⟨s, rfl, hs⟩
          -- Build the real point `Fin.cons s v ∈ U`.
          have hsv_in_ball : (Fin.cons s v : Fin (n + 1) → ℝ) ∈ Metric.ball x₀ ε := by
            rw [Metric.mem_ball, dist_pi_lt_iff hε]
            intro i
            refine Fin.cases ?_ ?_ i
            · -- coordinate 0
              simpa [Fin.cons, Real.dist_eq] using hs
            · -- coordinate j+1
              intro j
              simpa [Fin.cons, Real.dist_eq] using hv j
          have h_in_U : (Fin.cons s v : Fin (n + 1) → ℝ) ∈ U :=
            hball hsv_in_ball
          have hFGc := hFG _ h_in_U
          change Fv (s : ℂ) = Gv (s : ℂ)
          -- Rewrite the coercion-of-cons to cons-of-coercions.
          have hcons_eq :
              (fun i => ((Fin.cons s v : Fin (n + 1) → ℝ) i : ℂ)) =
                (Fin.cons (s : ℂ) (fun i => (v i : ℂ))) := by
            funext i
            refine Fin.cases ?_ ?_ i
            · simp [Fin.cons]
            · intro j
              simp [Fin.cons]
          rw [hcons_eq] at hFGc
          exact hFGc
        -- Apply the 1-D identity theorem on `ℂ`.
        have heq : Fv = Gv :=
          AnalyticOnNhd.eq_of_frequently_eq hFv_an hGv_an h_freq
        intro t
        exact congr_fun heq t
      -- Step B. Tail induction. For each fixed `t : ℂ`, define the tail slices
      -- and apply the inductive hypothesis on `n`.
      intro z
      -- Decompose `z = Fin.cons (z 0) (Fin.tail z)`.
      rw [show z = Fin.cons (z 0) (Fin.tail z) from (Fin.cons_self_tail z).symm]
      set t := z 0
      set vC := Fin.tail z with hvC
      -- Define tail slices `Ft, Gt : (Fin n → ℂ) → ℂ`.
      let Ft : (Fin n → ℂ) → ℂ := fun w => F (Fin.cons t w)
      let Gt : (Fin n → ℂ) → ℂ := fun w => G (Fin.cons t w)
      -- Both are entire on `Fin n → ℂ`.
      have hFt_an : AnalyticOnNhd ℂ Ft univ := fun w _ =>
        (hF _ (mem_univ _)).comp (analyticAt_cons_right t w)
      have hGt_an : AnalyticOnNhd ℂ Gt univ := fun w _ =>
        (hG _ (mem_univ _)).comp (analyticAt_cons_right t w)
      -- Build the real-cube hypothesis for the inductive call.
      let V : Set (Fin n → ℝ) :=
        {v | ∀ i, |v i - x₀ i.succ| < ε}
      have hV_open : IsOpen V := by
        -- `V = ⋂ i, {v | |v i - x₀ i.succ| < ε}`, each a preimage of an
        -- open ball under a continuous projection.
        have : V = ⋂ i, {v : Fin n → ℝ | |v i - x₀ i.succ| < ε} := by
          ext v
          simp [V]
        rw [this]
        refine isOpen_iInter_of_finite (fun i => ?_)
        have : Continuous (fun v : Fin n → ℝ => |v i - x₀ i.succ|) :=
          (continuous_abs.comp ((continuous_apply i).sub continuous_const))
        exact this.isOpen_preimage _ isOpen_Iio
      have hV_mem : (fun i => x₀ i.succ) ∈ V := by
        intro i; simp [hε]
      have hV_int : (interior V).Nonempty :=
        ⟨_, hV_open.interior_eq.symm ▸ hV_mem⟩
      -- For each `v ∈ V`, slices agree at the corresponding complex coercion.
      have hFGt : ∀ v ∈ V, Ft (fun i => (v i : ℂ)) = Gt (fun i => (v i : ℂ)) := by
        intro v hv
        exact head_slice v hv t
      -- Inductive call.
      have hpoint :=
        ih (F := Ft) (G := Gt) hFt_an hGt_an V hV_int hFGt vC
      -- Conclude.
      exact hpoint

end AsymptoticStatistics.ForMathlib.IdentityTheoremMulti
