module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.RandomFunctions
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw

@[expose] public section

/-!
# Random-index empirical-score replacement

An estimated score may be evaluated at the same product sample that selected it. The
results below treat this random-index empirical-process setting without an estimator,
parametric model, score equation, Taylor condition, Bartlett identity, bias condition,
or asymptotic-linearity conclusion.

The scalar result is the product-law form of vdV Lemma 19.24. The finite-dimensional
result assumes the scalar Donsker and
expected-`L²` inputs coordinatewise and concludes the native Euclidean residual from
the finitely many coordinate bounds; in particular, it introduces no vector-Donsker predicate.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

open AsymptoticStatistics.EmpiricalProcess

-- The `RandomFunctions` iid carrier lives in universe zero.
variable {Omega : Type} [MeasurableSpace Omega]

/-- Minimal scalar hypotheses for replacing a random estimated score by its fixed
reference score inside the centered empirical process under the product laws `P^n`.

This bundle records only the concrete inputs used by the product-law form of vdV
Lemma 19.24. In particular, membership of `score0` in `F` is unnecessary: the
random-function theorem extracts deterministic anchors in `F` from the `L²`
consistency premise. -/
structure RandomIndexScoreReplacementHyp
    (P : Measure Omega) [IsProbabilityMeasure P]
    (scoreHat : forall n, (Fin n -> Omega) -> (Omega -> Real))
    (score0 : Omega -> Real) (F : Set (Omega -> Real)) : Prop where
  /-- Constitutive (vdV Lemma 19.24): measurable representative of the
  fixed reference score. -/
  score0_meas : Measurable score0
  /-- Constitutive (vdV Lemma 19.24): fixed reference score in `L²(P)`. -/
  score0_memLp : MemLp score0 2 P
  /-- Constitutive (vdV Lemma 19.24): scalar `P`-Donsker class. -/
  is_donsker : IsPDonsker F P
  /-- Joint measurability of the
  sample-indexed score, used to transport expected `L²` consistency from `P^n` to the
  infinite iid product representation. -/
  scoreHat_meas : forall n,
    Measurable (fun p : (Fin n -> Omega) × Omega => scoreHat n p.1 p.2)
  /-- Constitutive (vdV Lemma 19.24): every realized estimated scalar score
  belongs to the Donsker class. -/
  scoreHat_mem : forall n (X : Fin n -> Omega), scoreHat n X ∈ F
  /-- Constitutive (vdV Lemma 19.24, expected-`L²` form): expected squared
  `L²(P)` distance of the estimated score from the fixed score tends to zero under the
  product sample law `P^n`. -/
  score_l2_consistency :
    Tendsto (fun n =>
      ∫ X, (∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P)
        ∂(Measure.pi (fun _ : Fin n => P))) atTop (nhds 0)
  /-- Integrability needed to convert
  expected `L²` consistency into the explicit outer-probability tail of Lemma 19.24. -/
  score_l2_int : forall n, Integrable
    (fun X : Fin n -> Omega => ∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P)
    (Measure.pi (fun _ : Fin n => P))

set_option maxHeartbeats 2000000 in
-- The infinite-product transport and empirical-process event normalization are heartbeat-heavy.
/-- The centered empirical-process residual obtained by replacing a random estimated
scalar score by its fixed reference score is `o_P(1)` under the product sample laws. -/
theorem randomIndex_empiricalScoreReplacement_oP
    {P : Measure Omega} [IsProbabilityMeasure P]
    {scoreHat : forall n, (Fin n -> Omega) -> (Omega -> Real)}
    {score0 : Omega -> Real} {F : Set (Omega -> Real)}
    -- the minimal scalar random-index replacement bundle above.
    (h : RandomIndexScoreReplacementHyp P scoreHat score0 F) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (Real.sqrt n)⁻¹ *
            (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
          - Real.sqrt n * (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
  intro ε hε
  let μ : Measure (ℕ → Omega) := Measure.infinitePi (fun _ : ℕ => P)
  let trunc (n : ℕ) (ξ : ℕ → Omega) : Fin n → Omega := fun i => ξ i.val
  have htrunc : ∀ n, Measurable (trunc n) := fun n =>
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hXmeas : ∀ i : ℕ, Measurable (fun ξ : ℕ → Omega => ξ i) := fun _ =>
    measurable_pi_apply _
  have hXindep : ProbabilityTheory.iIndepFun
      (fun (i : ℕ) (ξ : ℕ → Omega) => ξ i) μ := by
    simpa [μ] using ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : ℕ => P) (X := fun _ : ℕ => id) (mX := fun _ => measurable_id)
  have hXlaw : μ.map (fun ξ : ℕ → Omega => ξ 0) = P := by
    change (Measure.infinitePi (fun _ : ℕ => P)).map (Function.eval 0) = P
    rw [Measure.infinitePi_map_eval]
  have hXidem : ∀ i : ℕ, ProbabilityTheory.IdentDistrib
      (fun ξ : ℕ → Omega => ξ i) (fun ξ : ℕ → Omega => ξ 0) μ μ := by
    intro i
    refine ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, ?_⟩
    change μ.map (Function.eval i) = μ.map (Function.eval 0)
    simp [μ, Measure.infinitePi_map_eval]
  let fhat (n : ℕ) (ξ : ℕ → Omega) := scoreHat n (trunc n ξ)
  have hfhat_meas : ∀ n, Measurable (Function.uncurry (fhat n)) := by
    intro n
    exact (h.scoreHat_meas n).comp <| Measurable.prodMk
      ((htrunc n).comp measurable_fst) measurable_snd
  have hinner : ∀ n, StronglyMeasurable (fun X : Fin n → Omega =>
      ∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P) := by
    intro n
    exact ((h.scoreHat_meas n).sub (h.score0_meas.comp measurable_snd)).pow_const 2
      |>.stronglyMeasurable.integral_prod_right'
  have hl2 : Tendsto (fun n =>
      ∫ ξ, (∫ x, (fhat n ξ x - score0 x) ^ 2 ∂P) ∂μ) atTop (nhds 0) := by
    apply h.score_l2_consistency.congr'
    filter_upwards [] with n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n,
      integral_map (htrunc n).aemeasurable (hinner n).aestronglyMeasurable]
  have hl2int : ∀ n, Integrable
      (fun ξ => ∫ x, (fhat n ξ x - score0 x) ^ 2 ∂P) μ := by
    intro n
    simp only [μ]
    exact (integrable_map_measure (hinner n).aestronglyMeasurable
      (htrunc n).aemeasurable).mp (by
        rw [← AsymptoticStatistics.pi_const_eq_infinitePi_map P n]
        exact h.score_l2_int n)
  have htail : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      μ.outerMeasureStar {ξ | δ < distL2 P (fhat n ξ) score0}) atTop (nhds 0) := by
    intro δ hδ
    have hm : Tendsto (fun n => μ {ξ | δ ≤ distL2 P (fhat n ξ) score0})
        atTop (nhds 0) := markov_distL2_tail (F := F) (P := P)
      (Ξ := ℕ → Omega) μ fhat (fun _ _ => score0) hfhat_meas
      (fun _ => h.score0_meas.comp measurable_snd) hl2int (by simpa using hl2) hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hm
      (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
    exact (outerMeasureStar_mono μ fun (ξ : ℕ → Omega) hx =>
      show δ ≤ distL2 P (fhat n ξ) score0 from hx.le).trans
      (AsymptoticStatistics.outerMeasureStar_le_measure μ _)
  have hcore := donsker_random_function_consistency_core (F := F) (P := P)
    h.is_donsker score0 h.score0_memLp (Ξ := ℕ → Omega) (μ := μ)
    (X := fun i ξ => ξ i) hXmeas hXindep hXidem hXlaw (f_hat := fhat)
    (fun n ξ => h.scoreHat_mem n (trunc n ξ)) htail (ε / 2) (half_pos hε)
  have hstat : ∀ (n : ℕ) (ξ : ℕ → Omega),
      (Real.sqrt n)⁻¹ *
          (∑ i : Fin n, (scoreHat n (trunc n ξ) (ξ i) - score0 (ξ i)))
        - Real.sqrt n * (∫ x, (scoreHat n (trunc n ξ) x - score0 x) ∂P)
        = empiricalProcess P n (trunc n ξ) (fhat n ξ)
          - empiricalProcess P n (trunc n ξ) score0 := by
    intro n ξ
    have hfint : Integrable (fhat n ξ) P :=
      (h.is_donsker.marginalCLT.memLp _ (h.scoreHat_mem n _)).integrable (by norm_num)
    rw [integral_sub hfint (h.score0_memLp.integrable (by norm_num)),
      Finset.sum_sub_distrib]
    unfold empiricalProcess empiricalAvg
    simp only [fhat, trunc]
    by_cases hn : n = 0
    · subst n; simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hnpos)
      have hnR : (n : ℝ) ≠ 0 := ne_of_gt hnpos
      have hinv : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt n * (n : ℝ)⁻¹ := by
        field_simp
        exact (Real.sq_sqrt hnpos.le).symm
      rw [hinv]
      ring
  have hZmeas : ∀ n, Measurable (fun X : Fin n → Omega =>
      (Real.sqrt n)⁻¹ * (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
        - Real.sqrt n * (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
    intro n
    apply Measurable.sub (measurable_const.mul <| Finset.measurable_sum _ fun i _ =>
      ((h.scoreHat_meas n).comp (Measurable.prodMk measurable_id
        (measurable_pi_apply i))).sub (h.score0_meas.comp (measurable_pi_apply i)))
    exact measurable_const.mul <|
      ((h.scoreHat_meas n).sub (h.score0_meas.comp measurable_snd)).stronglyMeasurable
        |>.integral_prod_right'.measurable
  have hcoreR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hcore
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcoreR
    (Eventually.of_forall fun _ => measureReal_nonneg) (Eventually.of_forall fun n => ?_)
  rw [AsymptoticStatistics.pi_real_eq_infinitePi_real_of_truncate P n
    (measurableSet_le measurable_const (hZmeas n).norm)]
  refine measureReal_mono (μ := μ) (h₂ := measure_ne_top μ _) ?_
  intro ξ hξ
  change ε / 2 < |empiricalProcess P n (trunc n ξ) (fhat n ξ)
    - empiricalProcess P n (trunc n ξ) score0|
  rw [← hstat n ξ]
  change ε ≤ ‖(Real.sqrt n)⁻¹ *
      (∑ i : Fin n, (scoreHat n (trunc n ξ) (ξ i) - score0 (ξ i)))
    - Real.sqrt n * (∫ x, (scoreHat n (trunc n ξ) x - score0 x) ∂P)‖ at hξ
  rw [Real.norm_eq_abs] at hξ
  exact (half_lt_self hε).trans_le hξ

/-- Product-law hypotheses for vdV Lemma 19.24 with the asymptotic class
membership and in-probability `L²(P)` consistency used in Theorem 25.77.

The class anchor is a Lean localization witness.  It is scope-neutral:
w.p.a.1 membership already implies that the Donsker class is nonempty. -/
structure RandomIndexScoreReplacementWPAHyp
    (P : Measure Omega) [IsProbabilityMeasure P]
    (scoreHat : forall n, (Fin n -> Omega) -> (Omega -> Real))
    (score0 anchor : Omega -> Real) (F : Set (Omega -> Real)) : Prop where
  /-- measurable representative of the fixed score. -/
  score0_meas : Measurable score0
  /-- vdV Lemma 19.24: the fixed score is square-integrable. -/
  score0_memLp : MemLp score0 2 P
  /-- vdV Lemma 19.24: the fixed class is `P`-Donsker. -/
  is_donsker : IsPDonsker F P
  /-- joint measurability of the fitted score. -/
  scoreHat_meas : forall n,
    Measurable (fun p : (Fin n -> Omega) × Omega => scoreHat n p.1 p.2)
  /-- measurable event representing class membership. -/
  scoreHat_bad_meas : forall n, MeasurableSet
    {X : Fin n -> Omega | scoreHat n X ∉ F}
  /-- vdV Theorem 25.77: fitted scores belong to `F` with probability tending
  to one. -/
  scoreHat_mem_wpa : Tendsto (fun n =>
    (Measure.pi (fun _ : Fin n => P)) {X | scoreHat n X ∉ F}) atTop (nhds 0)
  /-- localization anchor in the fixed Donsker class, used only on
  the exceptional class-membership event. -/
  anchor_mem : anchor ∈ F
  /-- vdV equation (25.76a), scalar tail form: squared `L²(P)` distance
  converges to zero in probability. -/
  score_l2_consistency : forall delta : Real, 0 < delta -> Tendsto (fun n =>
    (Measure.pi (fun _ : Fin n => P))
      {X | delta ^ 2 <= ∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P})
    atTop (nhds 0)

set_option maxHeartbeats 2500000 in
-- The infinite-product transport and the w.p.a.1 localization are elaboration-heavy.
/-- Product-law random-index empirical replacement with literal w.p.a.1 class
membership and in-probability `L²(P)` consistency. -/
theorem randomIndex_empiricalScoreReplacement_oP_wpa
    {P : Measure Omega} [IsProbabilityMeasure P]
    {scoreHat : forall n, (Fin n -> Omega) -> (Omega -> Real)}
    {score0 anchor : Omega -> Real} {F : Set (Omega -> Real)}
    (h : RandomIndexScoreReplacementWPAHyp P scoreHat score0 anchor F) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (Real.sqrt n)⁻¹ *
            (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
          - Real.sqrt n * (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
  classical
  intro epsilon hepsilon
  let mu : Measure (Nat -> Omega) := Measure.infinitePi (fun _ : Nat => P)
  let trunc (n : Nat) (xi : Nat -> Omega) : Fin n -> Omega := fun i => xi i.val
  let fhat (n : Nat) (xi : Nat -> Omega) := scoreHat n (trunc n xi)
  have htrunc : forall n, Measurable (trunc n) := fun n =>
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have hXmeas : forall i : Nat, Measurable (fun xi : Nat -> Omega => xi i) :=
    fun _ => measurable_pi_apply _
  have hXindep : ProbabilityTheory.iIndepFun
      (fun (i : Nat) (xi : Nat -> Omega) => xi i) mu := by
    simpa [mu] using ProbabilityTheory.iIndepFun_infinitePi
      (P := fun _ : Nat => P) (X := fun _ : Nat => id) (mX := fun _ => measurable_id)
  have hXlaw : mu.map (fun xi : Nat -> Omega => xi 0) = P := by
    change (Measure.infinitePi (fun _ : Nat => P)).map (Function.eval 0) = P
    rw [Measure.infinitePi_map_eval]
  have hXidem : forall i : Nat, ProbabilityTheory.IdentDistrib
      (fun xi : Nat -> Omega => xi i) (fun xi : Nat -> Omega => xi 0) mu mu := by
    intro i
    refine ⟨(hXmeas i).aemeasurable, (hXmeas 0).aemeasurable, ?_⟩
    change mu.map (Function.eval i) = mu.map (Function.eval 0)
    simp [mu, Measure.infinitePi_map_eval]
  have hbad : Tendsto (fun n => mu {xi | fhat n xi ∉ F}) atTop (nhds 0) := by
    apply h.scoreHat_mem_wpa.congr'
    filter_upwards [] with n
    rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n,
      Measure.map_apply (htrunc n) (h.scoreHat_bad_meas n)]
    rfl
  have htail : forall delta : Real, 0 < delta -> Tendsto (fun n =>
      mu.outerMeasureStar {xi | delta < distL2 P (fhat n xi) score0})
      atTop (nhds 0) := by
    intro delta hdelta
    have ht := h.score_l2_consistency delta hdelta
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
      (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
    calc
      mu.outerMeasureStar {xi | delta < distL2 P (fhat n xi) score0}
          <= mu {xi | delta < distL2 P (fhat n xi) score0} :=
        AsymptoticStatistics.outerMeasureStar_le_measure mu _
      _ <= mu {xi | delta ^ 2 <=
          ∫ x, (fhat n xi x - score0 x) ^ 2 ∂P} := measure_mono (by
        intro xi hxi
        have hfmeas : Measurable (fhat n xi) := by
          exact (h.scoreHat_meas n).comp measurable_prodMk_left
        exact distL2_ge_imp_integral_ge
          hfmeas.aestronglyMeasurable
          h.score0_meas.aestronglyMeasurable hdelta hxi.le)
      _ = (Measure.pi (fun _ : Fin n => P))
          {X | delta ^ 2 <= ∫ x, (scoreHat n X x - score0 x) ^ 2 ∂P} := by
        rw [AsymptoticStatistics.pi_const_eq_infinitePi_map P n]
        rw [Measure.map_apply]
        · rfl
        · exact htrunc n
        · exact (((h.scoreHat_meas n).sub (h.score0_meas.comp measurable_snd)).pow_const 2
            |>.stronglyMeasurable.integral_prod_right').measurable measurableSet_Ici
  have hcore := donsker_random_function_consistency_wpa F P h.is_donsker score0
    h.score0_memLp mu (fun i xi => xi i) hXmeas hXindep hXidem hXlaw fhat
    anchor h.anchor_mem hbad htail (epsilon / 2) (half_pos hepsilon)
  have hstat : forall n (xi : Nat -> Omega), fhat n xi ∈ F ->
      (Real.sqrt n)⁻¹ *
          (∑ i : Fin n, (scoreHat n (trunc n xi) (xi i) - score0 (xi i)))
        - Real.sqrt n *
            (∫ x, (scoreHat n (trunc n xi) x - score0 x) ∂P)
        = empiricalProcess P n (trunc n xi) (fhat n xi) -
            empiricalProcess P n (trunc n xi) score0 := by
    intro n xi hmem
    have hfint : Integrable (fhat n xi) P :=
      (h.is_donsker.marginalCLT.memLp _ hmem).integrable (by norm_num)
    rw [integral_sub hfint (h.score0_memLp.integrable (by norm_num)),
      Finset.sum_sub_distrib]
    unfold empiricalProcess empiricalAvg
    simp only [fhat, trunc]
    by_cases hn : n = 0
    · subst n; simp
    · have hnpos : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hinv : (Real.sqrt (n : Real))⁻¹ = Real.sqrt n * (n : Real)⁻¹ := by
        field_simp
        exact (Real.sq_sqrt hnpos.le).symm
      rw [hinv]
      ring
  have hZmeas : forall n, Measurable (fun X : Fin n -> Omega =>
      (Real.sqrt n)⁻¹ * (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
        - Real.sqrt n * (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
    intro n
    apply Measurable.sub (measurable_const.mul <| Finset.measurable_sum _ fun i _ =>
      ((h.scoreHat_meas n).comp (Measurable.prodMk measurable_id
        (measurable_pi_apply i))).sub (h.score0_meas.comp (measurable_pi_apply i)))
    exact measurable_const.mul <|
      ((h.scoreHat_meas n).sub (h.score0_meas.comp measurable_snd)).stronglyMeasurable
        |>.integral_prod_right'.measurable
  have hsum : Tendsto (fun n =>
      mu {xi | epsilon / 2 <
          |empiricalProcess P n (fun i : Fin n => xi i.val) (fhat n xi) -
            empiricalProcess P n (fun i : Fin n => xi i.val) score0|} +
        mu {xi | fhat n xi ∉ F}) atTop (nhds 0) := by
    simpa using hcore.add hbad
  have hsumR := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumR
    (Eventually.of_forall fun _ => measureReal_nonneg) (Eventually.of_forall fun n => ?_)
  rw [AsymptoticStatistics.pi_real_eq_infinitePi_real_of_truncate P n
    (measurableSet_le measurable_const (hZmeas n).norm)]
  calc
    mu.real {xi | epsilon <= ‖
        (Real.sqrt n)⁻¹ *
            (∑ i : Fin n, (scoreHat n (trunc n xi) (xi i) - score0 (xi i)))
          - Real.sqrt n *
              (∫ x, (scoreHat n (trunc n xi) x - score0 x) ∂P)‖}
        <= mu.real ({xi | epsilon / 2 <
            |empiricalProcess P n (fun i : Fin n => xi i.val) (fhat n xi) -
              empiricalProcess P n (fun i : Fin n => xi i.val) score0|} ∪
            {xi | fhat n xi ∉ F}) := measureReal_mono (by
          intro xi hxi
          by_cases hmem : fhat n xi ∈ F
          · left
            have hident := hstat n xi hmem
            simp only [trunc] at hident
            change epsilon / 2 <
              |empiricalProcess P n (fun i : Fin n => xi i.val) (fhat n xi) -
                empiricalProcess P n (fun i : Fin n => xi i.val) score0|
            rw [← hident]
            have hxi' : epsilon ≤
                |(Real.sqrt n)⁻¹ *
                    (∑ i : Fin n,
                      (scoreHat n (fun i : Fin n => xi i.val) (xi i.val) -
                        score0 (xi i.val))) -
                  Real.sqrt n *
                    (∫ x, (scoreHat n (fun i : Fin n => xi i.val) x - score0 x) ∂P)| := by
              simpa only [Set.mem_setOf_eq, trunc, Real.norm_eq_abs] using hxi
            exact (half_lt_self hepsilon).trans_le hxi'
          · exact Or.inr hmem)
    _ <= mu.real {xi | epsilon / 2 <
          |empiricalProcess P n (fun i : Fin n => xi i.val) (fhat n xi) -
            empiricalProcess P n (fun i : Fin n => xi i.val) score0|} +
        mu.real {xi | fhat n xi ∉ F} := measureReal_union_le _ _
    _ <= (mu {xi | epsilon / 2 <
          |empiricalProcess P n (fun i : Fin n => xi i.val) (fhat n xi) -
            empiricalProcess P n (fun i : Fin n => xi i.val) score0|} +
        mu {xi | fhat n xi ∉ F}).toReal := by
      rw [ENNReal.toReal_add (measure_ne_top mu _) (measure_ne_top mu _)]
      rfl

/-- Coordinatewise scalar hypotheses for native finite-dimensional empirical-score
replacement.  Each coordinate may use its own scalar Donsker class; no Donsker
assumption is made on the vector-valued score class. -/
structure RandomIndexScoreReplacementHyp_vec
    (P : Measure Omega) [IsProbabilityMeasure P] (d : Nat)
    (scoreHat : forall n,
      (Fin n -> Omega) -> (Omega -> EuclideanSpace Real (Fin d)))
    (score0 : Omega -> EuclideanSpace Real (Fin d))
    (F : Fin d -> Set (Omega -> Real)) : Prop where
  /-- Constitutive (finite-dimensional coordinate lift): minimal scalar
  replacement hypotheses for every coordinate, possibly with coordinate-dependent
  Donsker classes. -/
  coord_hyp : forall j : Fin d,
    RandomIndexScoreReplacementHyp P
      (fun n X x => scoreHat n X x j) (fun x => score0 x j) (F j)

/-- Coordinatewise hypotheses for native finite-dimensional empirical-score
replacement with the w.p.a.1 class membership of vdV Theorem 25.77.  The
global fitted-score `L²(P)` condition permits Bochner integration to commute
with finite-dimensional coordinate evaluation, including on the exceptional
localization event. -/
structure RandomIndexScoreReplacementWPAHyp_vec
    (P : Measure Omega) [IsProbabilityMeasure P] (d : Nat)
    (scoreHat : forall n,
      (Fin n -> Omega) -> (Omega -> EuclideanSpace Real (Fin d)))
    (score0 anchor : Omega -> EuclideanSpace Real (Fin d))
    (F : Fin d -> Set (Omega -> Real)) : Prop where
  /-- Coordinatewise Donsker, w.p.a.1 membership, and equation (25.76a)
  hypotheses. -/
  coord_hyp : forall j : Fin d,
    RandomIndexScoreReplacementWPAHyp P
      (fun n X x => scoreHat n X x j) (fun x => score0 x j)
      (fun x => anchor x j) (F j)
  /-- square-integrable vector representative of every fitted
  score under the truth law. -/
  scoreHat_memLp : forall n X, MemLp (scoreHat n X) 2 P
  /-- square-integrable vector representative of the fixed score. -/
  score0_memLp : MemLp score0 2 P

/-- Native finite-dimensional empirical-score replacement with w.p.a.1
coordinatewise membership in fixed Donsker classes. -/
theorem randomIndex_empiricalScoreReplacement_oP_wpa_vec
    {P : Measure Omega} [IsProbabilityMeasure P] {d : Nat}
    {scoreHat : forall n,
      (Fin n -> Omega) -> (Omega -> EuclideanSpace Real (Fin d))}
    {score0 anchor : Omega -> EuclideanSpace Real (Fin d)}
    {F : Fin d -> Set (Omega -> Real)}
    (h : RandomIndexScoreReplacementWPAHyp_vec P d scoreHat score0 anchor F) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (Real.sqrt n)⁻¹ •
            (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
          - Real.sqrt n • (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
  classical
  let Z (n : Nat) (X : Fin n -> Omega) :=
    (Real.sqrt n)⁻¹ • (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
      - Real.sqrt n • (∫ x, (scoreHat n X x - score0 x) ∂P)
  change TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P)) Z
  have hint (n : Nat) (X : Fin n -> Omega) (j : Fin d) :
      (∫ x, (scoreHat n X x - score0 x) ∂P) j
        = ∫ x, (scoreHat n X x j - score0 x j) ∂P := by
    apply MeasureTheory.eval_integral_piLp
    intro k
    have hdiff : MemLp (fun x => scoreHat n X x - score0 x) 2 P :=
      (h.scoreHat_memLp n X).sub h.score0_memLp
    simpa only [PiLp.proj_apply, PiLp.sub_apply] using
      (hdiff.continuousLinearMap_comp
        (PiLp.proj (𝕜 := Real) (p := 2) (β := fun _ : Fin d => Real) k)).integrable
        (by norm_num)
  have hcoord : forall j : Fin d, TendstoInProbZero
      (fun n : Nat => Measure.pi (fun _ : Fin n => P)) (fun n X => Z n X j) := by
    intro j
    have hj := randomIndex_empiricalScoreReplacement_oP_wpa (h.coord_hyp j)
    convert hj using 1
    funext n X
    simp only [Z, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [show (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i))).ofLp j
        = ∑ i : Fin n, (scoreHat n X (X i) j - score0 (X i) j) by
          simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply], hint n X j]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro epsilon hepsilon
    have hz : forall n (X : Fin n -> Omega), Z n X = 0 :=
      fun _ _ => Subsingleton.elim _ _
    simp only [hz, norm_zero, not_le.mpr hepsilon, Set.setOf_false, measureReal_empty]
    exact tendsto_const_nhds
  · intro epsilon hepsilon
    have hdR : (0 : Real) < d := by exact_mod_cast hd
    have hlevel : 0 < epsilon / d := div_pos hepsilon hdR
    have hsum : Tendsto (fun n => ∑ j : Fin d,
        (Measure.pi (fun _ : Fin n => P)).real {X | epsilon / d <= ‖Z n X j‖})
        atTop (nhds 0) := by
      simpa using tendsto_finset_sum (Finset.univ : Finset (Fin d))
        (fun j _ => hcoord j (epsilon / d) hlevel)
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hsum
    refine (measureReal_mono (fun X hX => ?_)).trans (measureReal_iUnion_fintype_le _)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hall
    push Not at hall
    have hnorm : ‖Z n X‖ < epsilon := by
      calc
        ‖Z n X‖ = ‖∑ j : Fin d,
            PiLp.single (β := fun _ : Fin d => Real) 2 j (Z n X j)‖ := by
          congr 1
          ext j
          simp
        _ <= ∑ j : Fin d,
            ‖PiLp.single (β := fun _ : Fin d => Real) 2 j (Z n X j)‖ :=
          norm_sum_le _ _
        _ = ∑ j : Fin d, ‖Z n X j‖ := by simp
        _ < ∑ _j : Fin d, epsilon / d := Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd))
          (fun j _ => hall j)
        _ = epsilon := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
    exact (not_lt_of_ge hX) hnorm

/-- Native finite-dimensional empirical-score replacement from the scalar theorem in
each coordinate.  The conclusion is the Euclidean centered residual under `P^n`; it
uses only finiteness of `Fin d`, not a vector-Donsker assumption. -/
theorem randomIndex_empiricalScoreReplacement_oP_vec
    {P : Measure Omega} [IsProbabilityMeasure P] {d : Nat}
    {scoreHat : forall n,
      (Fin n -> Omega) -> (Omega -> EuclideanSpace Real (Fin d))}
    {score0 : Omega -> EuclideanSpace Real (Fin d)}
    {F : Fin d -> Set (Omega -> Real)}
    -- coordinatewise scalar random-index replacement hypotheses.
    (h : RandomIndexScoreReplacementHyp_vec P d scoreHat score0 F) :
    TendstoInProbZero (fun n : Nat => Measure.pi (fun _ : Fin n => P))
      (fun n X =>
        (Real.sqrt n)⁻¹ •
            (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
          - Real.sqrt n • (∫ x, (scoreHat n X x - score0 x) ∂P)) := by
  classical
  let Z (n : ℕ) (X : Fin n → Omega) :=
    (Real.sqrt n)⁻¹ • (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i)))
      - Real.sqrt n • (∫ x, (scoreHat n X x - score0 x) ∂P)
  change TendstoInProbZero (fun n : ℕ => Measure.pi (fun _ : Fin n => P)) Z
  have hint (n : ℕ) (X : Fin n → Omega) (j : Fin d) :
      (∫ x, (scoreHat n X x - score0 x) ∂P) j
        = ∫ x, (scoreHat n X x j - score0 x j) ∂P := by
    apply MeasureTheory.eval_integral_piLp
    intro k
    exact ((h.coord_hyp k).is_donsker.marginalCLT.memLp _
      ((h.coord_hyp k).scoreHat_mem n X)).integrable (by norm_num) |>.sub
        ((h.coord_hyp k).score0_memLp.integrable (by norm_num))
  have hcoord : ∀ j : Fin d, TendstoInProbZero
      (fun n : ℕ => Measure.pi (fun _ : Fin n => P)) (fun n X => Z n X j) := by
    intro j
    have hj := randomIndex_empiricalScoreReplacement_oP (h.coord_hyp j)
    convert hj using 1
    funext n X
    simp only [Z, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [show (∑ i : Fin n, (scoreHat n X (X i) - score0 (X i))).ofLp j
        = ∑ i : Fin n, (scoreHat n X (X i) j - score0 (X i) j) by
          simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.sub_apply], hint n X j]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro ε hε
    have hz : ∀ n (X : Fin n → Omega), Z n X = 0 := fun _ _ => Subsingleton.elim _ _
    simp only [hz, norm_zero, not_le.mpr hε, Set.setOf_false, measureReal_empty]
    exact tendsto_const_nhds
  · intro ε hε
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hlevel : 0 < ε / d := div_pos hε hdR
    have hsum : Tendsto (fun n => ∑ j : Fin d,
        (Measure.pi (fun _ : Fin n => P)).real {X | ε / d ≤ ‖Z n X j‖})
        atTop (nhds 0) := by
      simpa using tendsto_finset_sum (Finset.univ : Finset (Fin d))
        (fun j _ => hcoord j (ε / d) hlevel)
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hsum
    refine (measureReal_mono (fun X hX => ?_)).trans (measureReal_iUnion_fintype_le _)
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hall
    push Not at hall
    have hnorm : ‖Z n X‖ < ε := by
      calc
        ‖Z n X‖ = ‖∑ j : Fin d, PiLp.single (β := fun _ : Fin d => ℝ) 2 j (Z n X j)‖ := by
          congr 1; ext j; simp
        _ ≤ ∑ j : Fin d, ‖PiLp.single (β := fun _ : Fin d => ℝ) 2 j (Z n X j)‖ :=
          norm_sum_le _ _
        _ = ∑ j : Fin d, ‖Z n X j‖ := by simp
        _ < ∑ _j : Fin d, ε / d := Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)) (fun j _ => hall j)
        _ = ε := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
    exact (not_lt_of_ge hX) hnorm

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
