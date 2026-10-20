module
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.StrongLaw

@[expose] public section

/-!
# Sample-split empirical moments under product laws

Reusable probability lemmas for empirical means and Gram matrices whose summands use
an auxiliary function estimated from the opposite block of a deterministic two-block
split. The declarations make no reference to a numbered
statistical theorem or to asymptotic linearity.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Matrix.Norms.L2Operator

namespace AsymptoticStatistics

private theorem TendstoInProbZero.mono_norm
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    {P : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, S n → G} {W : ∀ n, S n → H}
    (hW : TendstoInProbZero P W) (h : ∀ n x, ‖Z n x‖ ≤ ‖W n x‖) :
    TendstoInProbZero P Z := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hW ε hε)
    (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono fun x hx => hx.trans (h n x))

private theorem TendstoInProbZero.add
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G] {P : ∀ n, Measure (S n)}
    [∀ n, IsProbabilityMeasure (P n)] {Z W : ∀ n, S n → G}
    (hZ : TendstoInProbZero P Z) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P (fun n x => Z n x + W n x) := by
  intro ε hε
  have hs : Tendsto (fun n => (P n).real {x | ε / 2 ≤ ‖Z n x‖} +
      (P n).real {x | ε / 2 ≤ ‖W n x‖}) atTop (nhds 0) := by
    simpa only [add_zero] using (hZ (ε / 2) (by positivity)).add
      (hW (ε / 2) (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Eventually.of_forall fun _ => measureReal_nonneg) (Eventually.of_forall fun n => ?_)
  refine (measureReal_mono (fun x hx => ?_)).trans (measureReal_union_le _ _)
  change ε ≤ ‖Z n x + W n x‖ at hx
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
  linarith [norm_add_le (Z n x) (W n x)]

private theorem TendstoInProbZero.finset_sum
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G] {P : ∀ n, Measure (S n)}
    [∀ n, IsProbabilityMeasure (P n)] {I : Type*} (s : Finset I)
    {Z : I → ∀ n, S n → G} (h : ∀ i ∈ s, TendstoInProbZero P (Z i)) :
    TendstoInProbZero P (fun n x => ∑ i ∈ s, Z i n x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      have he : ∀ n, {x : S n | ε ≤ ‖∑ i ∈ (∅ : Finset I), Z i n x‖} = ∅ := by
        intro n
        ext x
        simp [not_le.mpr hε]
      simp only [he, measureReal_empty]
      exact tendsto_const_nhds
  | @insert a s ha ih =>
      simpa [Finset.sum_insert ha] using TendstoInProbZero.add (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem TendstoInProbZero.euclidean_of_coordinate
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)] {d : ℕ}
    {P : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, S n → EuclideanSpace ℝ (Fin d)}
    (hZ : ∀ j, TendstoInProbZero P (fun n x => Z n x j)) :
    TendstoInProbZero P Z := by
  classical
  have hsingle (j : Fin d) : TendstoInProbZero P
      (fun n x => PiLp.single (β := fun _ : Fin d => Real) 2 j (Z n x j)) := by
    exact TendstoInProbZero.mono_norm (hZ j) (fun n x => by
      simp only [PiLp.norm_single, Real.norm_eq_abs]
      exact le_rfl)
  have hsum := TendstoInProbZero.finset_sum (Finset.univ : Finset (Fin d))
    (fun j _ => hsingle j)
  convert hsum using 1
  funext n x
  ext j
  simp

private theorem TendstoInProbZero.smul_const
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {P : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, S n → ℝ} (hZ : TendstoInProbZero P Z) (v : G) :
    TendstoInProbZero P (fun n x => Z n x • v) := by
  by_cases hv : v = 0
  · subst v
    simp only [smul_zero]
    intro ε hε
    simp only [norm_zero, not_le.mpr hε, Set.setOf_false, measureReal_empty]
    exact tendsto_const_nhds
  · have hvpos : 0 < ‖v‖ := (norm_pos_iff.mpr hv)
    intro ε hε
    have h := hZ (ε / ‖v‖) (div_pos hε hvpos)
    convert h using 1
    funext n
    apply measureReal_congr
    apply Filter.Eventually.of_forall
    intro x
    simp only [norm_smul, Real.norm_eq_abs]
    change (ε ≤ |Z n x| * ‖v‖) = (ε / ‖v‖ ≤ |Z n x|)
    rw [div_le_iff₀ hvpos, mul_comm]

private theorem TendstoInProbZero.matrix_of_entry
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)] {d : ℕ}
    {P : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, S n → Matrix (Fin d) (Fin d) ℝ}
    (hZ : ∀ j k, TendstoInProbZero P (fun n x => Z n x j k)) :
    TendstoInProbZero P Z := by
  classical
  have hsingle (j k : Fin d) : TendstoInProbZero P
      (fun n x => Matrix.single j k (Z n x j k)) := by
    have h := TendstoInProbZero.smul_const (hZ j k)
      (Matrix.single j k (1 : ℝ))
    convert h using 1
    funext n x
    ext a b
    simp [Matrix.single]
  have hsum := TendstoInProbZero.finset_sum (Finset.univ : Finset (Fin d))
    (fun j _ => TendstoInProbZero.finset_sum (Finset.univ : Finset (Fin d))
      (fun k _ => hsingle j k))
  convert hsum using 1
  funext n x
  exact Matrix.matrix_eq_sum_single (Z n x)

private theorem sqrt_mul_inv_sq_card_subtype_le (n : ℕ) (p : Fin n → Prop)
    [DecidablePred p] :
    (Real.sqrt n * (n : ℝ)⁻¹) ^ 2 * Fintype.card {i : Fin n // p i} ≤ 1 := by
  rcases n with _ | n
  · simp
  · have hn : (0 : ℝ) < n + 1 := by positivity
    have hcard : (Fintype.card {i : Fin (n + 1) // p i} : ℝ) ≤ n + 1 := by
      have h := Fintype.card_subtype_le (p := p)
      rw [Fintype.card_fin] at h
      exact_mod_cast h
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg (n + 1)), inv_pow]
    calc
      ((n + 1 : ℕ) : ℝ) * ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) *
          Fintype.card {i : Fin (n + 1) // p i} =
          (Fintype.card {i : Fin (n + 1) // p i} : ℝ) /
            ((n + 1 : ℕ) : ℝ) := by field_simp
      _ ≤ 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using (div_le_one hn).2 hcard

private theorem card_subtype_mul_inv_mem_Icc (n : ℕ) (p : Fin n → Prop)
    [DecidablePred p] :
    (Fintype.card {i : Fin n // p i} : ℝ) * (n : ℝ)⁻¹ ∈ Set.Icc 0 1 := by
  rcases n with _ | n
  · simp
  · have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hcard : (Fintype.card {i : Fin (n + 1) // p i} : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) := by
      have h := Fintype.card_subtype_le (p := p)
      rw [Fintype.card_fin] at h
      exact_mod_cast h
    constructor
    · positivity
    · rw [mul_inv_le_iff₀ hn]
      simpa only [one_mul] using hcard

private theorem splitBlock_centered_tail
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (block : I -> Prop) [DecidablePred block]
    (f : (I -> Omega) -> Omega -> Real)
    (hf : Measurable (fun p : (I -> Omega) × Omega => f p.1 p.2))
    (hlocal : forall X Y, (forall i, ¬ block i -> X i = Y i) -> f X = f Y)
    (hfL2 : forall X, MemLp (f X) 2 P)
    {a delta epsilon : Real} (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (ha_card : a ^ 2 * Fintype.card {i : I // block i} <= 1) :
    (Measure.pi (fun _ : I => P)).real
        {X | epsilon <= abs (a * ∑ i : {i : I // block i},
          (f X (X i.1) - ∫ x, f X x ∂P))} <=
      (Measure.pi (fun _ : I => P)).real
        {X | delta < ∫ x, (f X x) ^ 2 ∂P} + delta / epsilon ^ 2 := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => Omega) block
  let muS : Measure ({i : I // block i} -> Omega) := Measure.pi (fun _ => P)
  let muT : Measure ({i : I // ¬ block i} -> Omega) := Measure.pi (fun _ => P)
  let omega0 : Omega := Classical.choice (nonempty_of_isProbabilityMeasure P)
  let U0 : {i : I // block i} -> Omega := fun _ => omega0
  let combine : ({i : I // block i} -> Omega) ->
      ({i : I // ¬ block i} -> Omega) -> (I -> Omega) := fun U V => e.symm (U, V)
  let g : ({i : I // ¬ block i} -> Omega) -> Omega -> Real :=
    fun V x => f (combine U0 V) x
  let energy : ({i : I // ¬ block i} -> Omega) -> Real :=
    fun V => ∫ x, (g V x) ^ 2 ∂P
  let Z : (({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega)) -> Real := fun q =>
    a * ∑ i : {i : I // block i}, (g q.2 (q.1 i) - ∫ x, g q.2 x ∂P)
  have hcombine_meas : Measurable (fun q : ({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega) => combine q.1 q.2) := by
    simpa only [combine] using e.symm.measurable
  have hg_meas : Measurable (fun q :
      ({i : I // ¬ block i} -> Omega) × Omega => g q.1 q.2) := by
    simpa only [g, Function.comp_apply] using! hf.comp
      ((hcombine_meas.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have henergy_meas : Measurable energy := by
    exact (hg_meas.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  have hZ_meas : Measurable Z := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    have hgi : Measurable (fun q : (({i : I // block i} -> Omega) ×
        ({i : I // ¬ block i} -> Omega)) => g q.2 (q.1 i)) := by
      exact hg_meas.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
    have hint : Measurable (fun V : ({i : I // ¬ block i} -> Omega) =>
        ∫ x, g V x ∂P) :=
      hg_meas.stronglyMeasurable.integral_prod_right'.measurable
    exact hgi.sub (hint.comp measurable_snd)
  have henergy_combine (U : {i : I // block i} -> Omega)
      (V : {i : I // ¬ block i} -> Omega) :
      (∫ x, (f (combine U V) x) ^ 2 ∂P) = energy V := by
    have hfun : f (combine U V) = f (combine U0 V) := by
      apply hlocal
      intro i hi
      change (if h : block i then U ⟨i, h⟩ else V ⟨i, h⟩) =
        (if h : block i then U0 ⟨i, h⟩ else V ⟨i, h⟩)
      simp [hi]
    simp only [energy, g, hfun]
  have hf_combine (U : {i : I // block i} -> Omega)
      (V : {i : I // ¬ block i} -> Omega) :
      f (combine U V) = g V := by
    apply hlocal
    intro i hi
    change (if h : block i then U ⟨i, h⟩ else V ⟨i, h⟩) =
      (if h : block i then U0 ⟨i, h⟩ else V ⟨i, h⟩)
    simp [hi]
  have hZ_combine (U : {i : I // block i} -> Omega)
      (V : {i : I // ¬ block i} -> Omega) :
      a * ∑ i : {i : I // block i},
          (f (combine U V) ((combine U V) i.1) - ∫ x, f (combine U V) x ∂P) = Z (U, V) := by
    simp only [Z, hf_combine U V]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    change (if h : block i.1 then U ⟨i.1, h⟩ else V ⟨i.1, h⟩) = U i
    simp [i.2]
  have htarget_meas : MeasurableSet
      {q | epsilon <= abs (Z q)} :=
    measurableSet_le measurable_const hZ_meas.abs
  have hbad_meas : MeasurableSet {q : (({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega)) | delta < energy q.2} :=
    measurableSet_lt measurable_const (henergy_meas.comp measurable_snd)
  have hgood_meas : MeasurableSet {q : (({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega)) |
        epsilon <= abs (Z q) ∧ energy q.2 <= delta} :=
    htarget_meas.inter (measurableSet_le (henergy_meas.comp measurable_snd) measurable_const)
  have hcond (V : {i : I // ¬ block i} -> Omega) (hV : energy V <= delta) :
      muS {U | epsilon <= abs (Z (U, V))} <= ENNReal.ofReal (delta / epsilon ^ 2) := by
    let centered : {i : I // block i} -> Omega -> Real :=
      fun _ x => g V x - ∫ y, g V y ∂P
    have hgL2 : MemLp (g V) 2 P := by
      simpa only [g] using hfL2 (combine U0 V)
    have hcL2 : forall i, MemLp (centered i) 2 P := fun _ =>
      hgL2.sub (memLp_const (∫ y, g V y ∂P))
    have hsumL2 : MemLp (fun U => a * ∑ i, centered i (U i)) 2 muS := by
      apply MemLp.const_mul
      rw [show (fun U => ∑ i, centered i (U i)) =
          ∑ i, centered i ∘ Function.eval i by
        ext U
        simp [Function.comp_apply]]
      simpa only [muS] using memLp_finset_sum' Finset.univ (fun i _ =>
        (hcL2 i).comp_measurePreserving (measurePreserving_eval (fun _ => P) i))
    have hmean : ∫ U, a * ∑ i, centered i (U i) ∂muS = 0 := by
      rw [integral_const_mul]
      have hint : forall i, Integrable (fun U => centered i (U i)) muS := fun i =>
        ((hcL2 i).comp_measurePreserving
          (measurePreserving_eval (fun _ => P) i)).integrable one_le_two
      have hmean_i (i : {i : I // block i}) :
          ∫ U, centered i (U i) ∂muS = 0 := by
        simp only [muS]
        rw [MeasureTheory.integral_comp_eval (hcL2 i).aestronglyMeasurable]
        simp [centered, integral_sub (hgL2.integrable one_le_two)
          (integrable_const (∫ y, g V y ∂P))]
      rw [integral_finset_sum _ (fun i _ => hint i)]
      simp only [hmean_i, Finset.sum_const_zero, mul_zero]
    have hvar : ProbabilityTheory.variance (fun U => a * ∑ i, centered i (U i)) muS <=
        delta := by
      rw [ProbabilityTheory.variance_const_mul]
      have hvsum : ProbabilityTheory.variance (fun U => ∑ i, centered i (U i)) muS =
          ∑ i, ProbabilityTheory.variance (centered i) P := by
        have hfun : (fun U : ({i : I // block i} -> Omega) => ∑ i, centered i (U i)) =
            ∑ i : {i : I // block i}, fun U : ({i : I // block i} -> Omega) =>
              centered i (U i) := by
          funext U
          simp only [Finset.sum_apply]
        rw [hfun]
        simpa only [muS] using ProbabilityTheory.variance_sum_pi hcL2
      rw [hvsum]
      have hvar_each (i : {i : I // block i}) :
          ProbabilityTheory.variance (centered i) P <= energy V := by
        rw [show centered i = fun x => g V x - ∫ y, g V y ∂P by rfl,
          ProbabilityTheory.variance_sub_const hgL2.aestronglyMeasurable]
        exact (ProbabilityTheory.variance_le_expectation_sq hgL2.aestronglyMeasurable).trans_eq
          (by rfl)
      calc
        a ^ 2 * ∑ i, ProbabilityTheory.variance (centered i) P
            <= a ^ 2 * (Fintype.card {i : I // block i} * energy V) := by
              gcongr
              simpa [nsmul_eq_mul] using Finset.sum_le_sum
                (fun i (_ : i ∈ (Finset.univ : Finset {i : I // block i})) => hvar_each i)
        _ = (a ^ 2 * Fintype.card {i : I // block i}) * energy V := by ring
        _ <= energy V := by
          exact mul_le_of_le_one_left (by
            have hnonneg : 0 <= ∫ x, (g V x) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
            simpa only [energy] using hnonneg) ha_card
        _ <= delta := hV
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hsumL2 hepsilon
    simp only [hmean, sub_zero] at hcheb
    exact hcheb.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar (sq_nonneg _)))
  have hgood_bound : (muS.prod muT) {q | epsilon <= abs (Z q) ∧ energy q.2 <= delta}
      <= ENNReal.ofReal (delta / epsilon ^ 2) := by
    rw [Measure.prod_apply_symm hgood_meas]
    calc
      (∫⁻ V, muS ((fun U => (U, V)) ⁻¹' {q | epsilon <= abs (Z q) ∧
          energy q.2 <= delta}) ∂muT)
          <= ∫⁻ _V, ENNReal.ofReal (delta / epsilon ^ 2) ∂muT := by
            apply lintegral_mono
            intro V
            by_cases hV : energy V <= delta
            · simpa only [Set.preimage_setOf_eq, and_iff_left hV] using hcond V hV
            · simp only [Set.preimage_setOf_eq, hV, and_false, Set.setOf_false,
                measure_empty]
              exact bot_le
      _ = ENNReal.ofReal (delta / epsilon ^ 2) := by simp [muT]
  have hsplit : {q | epsilon <= abs (Z q)} ⊆
      {q | delta < energy q.2} ∪ {q | epsilon <= abs (Z q) ∧ energy q.2 <= delta} := by
    intro q hq
    by_cases hqE : delta < energy q.2
    · exact Or.inl hqE
    · exact Or.inr ⟨hq, not_lt.mp hqE⟩
  have hprod_bound : (muS.prod muT).real {q | epsilon <= abs (Z q)} <=
      (muS.prod muT).real {q | delta < energy q.2} + delta / epsilon ^ 2 := by
    calc
      (muS.prod muT).real {q | epsilon <= abs (Z q)}
          <= (muS.prod muT).real {q | delta < energy q.2} +
              (muS.prod muT).real {q | epsilon <= abs (Z q) ∧ energy q.2 <= delta} :=
            (measureReal_mono hsplit).trans (measureReal_union_le _ _)
      _ <= (muS.prod muT).real {q | delta < energy q.2} + delta / epsilon ^ 2 := by
        gcongr
        rw [measureReal_def]
        calc
          ((muS.prod muT) {q | epsilon <= abs (Z q) ∧ energy q.2 <= delta}).toReal
              <= (ENNReal.ofReal (delta / epsilon ^ 2)).toReal :=
                ENNReal.toReal_mono ENNReal.ofReal_ne_top hgood_bound
          _ = delta / epsilon ^ 2 := ENNReal.toReal_ofReal (div_nonneg hdelta.le (sq_nonneg _))
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => P) block
  have htarget_eq : e ⁻¹' {q | epsilon <= abs (Z q)} =
      {X | epsilon <= abs (a * ∑ i : {i : I // block i},
        (f X (X i.1) - ∫ x, f X x ∂P))} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hZ_combine (e X).1 (e X).2]
    simp only [combine, e.symm_apply_apply]
  have hbad_eq : e ⁻¹' {q | delta < energy q.2} =
      {X | delta < ∫ x, (f X x) ^ 2 ∂P} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← henergy_combine (e X).1 (e X).2]
    simp only [combine, e.symm_apply_apply]
  have htarget_real : (Measure.pi (fun _ : I => P)).real
      {X | epsilon <= abs (a * ∑ i : {i : I // block i},
        (f X (X i.1) - ∫ x, f X x ∂P))} =
      (muS.prod muT).real {q | epsilon <= abs (Z q)} := by
    rw [← htarget_eq, ← hmp.map_eq]
    change (Measure.pi (fun _ : I => P)).real (e ⁻¹' {q | epsilon <= abs (Z q)}) =
      (Measure.map e (Measure.pi (fun _ : I => P))).real {q | epsilon <= abs (Z q)}
    simp only [measureReal_def, e.map_apply]
  have hbad_real : (Measure.pi (fun _ : I => P)).real
      {X | delta < ∫ x, (f X x) ^ 2 ∂P} =
      (muS.prod muT).real {q | delta < energy q.2} := by
    rw [← hbad_eq, ← hmp.map_eq]
    change (Measure.pi (fun _ : I => P)).real (e ⁻¹' {q | delta < energy q.2}) =
      (Measure.map e (Measure.pi (fun _ : I => P))).real {q | delta < energy q.2}
    simp only [measureReal_def, e.map_apply]
  rw [htarget_real, hbad_real]
  exact hprod_bound

private theorem splitBlock_nonneg_tail
    {Omega I : Type*} [MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (block : I -> Prop) [DecidablePred block]
    (f : (I -> Omega) -> Omega -> Real)
    (hf : Measurable (fun p : (I -> Omega) × Omega => f p.1 p.2))
    (hlocal : forall X Y, (forall i, ¬ block i -> X i = Y i) -> f X = f Y)
    (hf_nonneg : forall X x, 0 <= f X x)
    (hf_int : forall X, Integrable (f X) P)
    {c delta epsilon : Real} (hc : 0 <= c) (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hc_card : c * Fintype.card {i : I // block i} <= 1) :
    (Measure.pi (fun _ : I => P)).real
        {X | epsilon <= c * ∑ i : {i : I // block i}, f X (X i.1)} <=
      (Measure.pi (fun _ : I => P)).real
        {X | delta < ∫ x, f X x ∂P} + delta / epsilon := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => Omega) block
  let muS : Measure ({i : I // block i} -> Omega) := Measure.pi (fun _ => P)
  let muT : Measure ({i : I // ¬ block i} -> Omega) := Measure.pi (fun _ => P)
  let omega0 : Omega := Classical.choice (nonempty_of_isProbabilityMeasure P)
  let U0 : {i : I // block i} -> Omega := fun _ => omega0
  let combine : ({i : I // block i} -> Omega) ->
      ({i : I // ¬ block i} -> Omega) -> (I -> Omega) := fun U V => e.symm (U, V)
  let g : ({i : I // ¬ block i} -> Omega) -> Omega -> Real :=
    fun V x => f (combine U0 V) x
  let energy : ({i : I // ¬ block i} -> Omega) -> Real := fun V => ∫ x, g V x ∂P
  let Z : (({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega)) -> Real := fun q =>
    c * ∑ i : {i : I // block i}, g q.2 (q.1 i)
  have hcombine_meas : Measurable (fun q : ({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega) => combine q.1 q.2) := by
    simpa only [combine] using e.symm.measurable
  have hg_meas : Measurable (fun q :
      ({i : I // ¬ block i} -> Omega) × Omega => g q.1 q.2) := by
    simpa only [g, Function.comp_apply] using! hf.comp
      ((hcombine_meas.comp (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  have henergy_meas : Measurable energy :=
    hg_meas.stronglyMeasurable.integral_prod_right'.measurable
  have hZ_meas : Measurable Z := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    exact hg_meas.comp (measurable_snd.prodMk ((measurable_pi_apply i).comp measurable_fst))
  have hf_combine (U : {i : I // block i} -> Omega)
      (V : {i : I // ¬ block i} -> Omega) : f (combine U V) = g V := by
    apply hlocal
    intro i hi
    change (if h : block i then U ⟨i, h⟩ else V ⟨i, h⟩) =
      (if h : block i then U0 ⟨i, h⟩ else V ⟨i, h⟩)
    simp [hi]
  have henergy_combine (U : {i : I // block i} -> Omega)
      (V : {i : I // ¬ block i} -> Omega) :
      (∫ x, f (combine U V) x ∂P) = energy V := by
    simp only [energy, hf_combine U V]
  have hZ_combine (U : {i : I // block i} -> Omega)
      (V : {i : I // ¬ block i} -> Omega) :
      c * ∑ i : {i : I // block i}, f (combine U V) ((combine U V) i.1) = Z (U, V) := by
    simp only [Z, hf_combine U V]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change (if h : block i.1 then U ⟨i.1, h⟩ else V ⟨i.1, h⟩) = U i
    simp [i.2]
  have htarget_meas : MeasurableSet {q | epsilon <= Z q} :=
    measurableSet_le measurable_const hZ_meas
  have hbad_meas : MeasurableSet {q : (({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega)) | delta < energy q.2} :=
    measurableSet_lt measurable_const (henergy_meas.comp measurable_snd)
  have hgood_meas : MeasurableSet {q : (({i : I // block i} -> Omega) ×
      ({i : I // ¬ block i} -> Omega)) | epsilon <= Z q ∧ energy q.2 <= delta} :=
    htarget_meas.inter (measurableSet_le (henergy_meas.comp measurable_snd) measurable_const)
  have hcond (V : {i : I // ¬ block i} -> Omega) (hV : energy V <= delta) :
      muS {U | epsilon <= Z (U, V)} <= ENNReal.ofReal (delta / epsilon) := by
    have hg_int : Integrable (g V) P := by simpa only [g] using hf_int (combine U0 V)
    have hsum_int : Integrable (fun U => c * ∑ i, g V (U i)) muS := by
      apply Integrable.const_mul
      rw [show (fun U => ∑ i, g V (U i)) =
          ∑ i, g V ∘ Function.eval i by
        ext U
        simp [Function.comp_apply]]
      simpa only [muS] using integrable_finset_sum' Finset.univ (fun i _ =>
        (measurePreserving_eval (fun _ => P) i).integrable_comp_of_integrable hg_int)
    have hsum_nonneg : 0 ≤ᵐ[muS] (fun U => c * ∑ i, g V (U i)) :=
      Eventually.of_forall fun U => mul_nonneg hc (Finset.sum_nonneg fun i _ =>
        hf_nonneg (combine U0 V) (U i))
    have h_int_sum : (∫ U, ∑ i, g V (U i) ∂muS) =
        ∑ i, ∫ U, g V (U i) ∂muS := by
      have hs := integral_finset_sum (μ := muS)
        (Finset.univ : Finset {i : I // block i}) (fun i _ =>
          (measurePreserving_eval (fun _ => P) i).integrable_comp_of_integrable hg_int)
      simpa only [Finset.sum_apply, Function.comp_apply] using hs
    have hint : ∫ U, c * ∑ i, g V (U i) ∂muS <= delta := by
      rw [integral_const_mul, h_int_sum]
      have heval (i : {i : I // block i}) : ∫ U, g V (U i) ∂muS = energy V := by
        simp only [muS]
        rw [MeasureTheory.integral_comp_eval hg_int.aestronglyMeasurable]
      simp_rw [heval]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        c * ((Fintype.card {i : I // block i} : ℕ) * energy V) =
            (c * Fintype.card {i : I // block i}) * energy V := by ring
        _ <= energy V := mul_le_of_le_one_left
          (integral_nonneg fun x => hf_nonneg (combine U0 V) x) hc_card
        _ <= delta := hV
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hsum_nonneg hsum_int epsilon
    have hreal : muS.real {U | epsilon <= Z (U, V)} <= delta / epsilon := by
      apply (le_div_iff₀ hepsilon).2
      rw [mul_comm]
      simpa only [Z] using hmarkov.trans hint
    rw [← ENNReal.ofReal_toReal (measure_ne_top muS _)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hgood_bound : (muS.prod muT) {q | epsilon <= Z q ∧ energy q.2 <= delta}
      <= ENNReal.ofReal (delta / epsilon) := by
    rw [Measure.prod_apply_symm hgood_meas]
    calc
      (∫⁻ V, muS ((fun U => (U, V)) ⁻¹' {q | epsilon <= Z q ∧
          energy q.2 <= delta}) ∂muT)
          <= ∫⁻ _V, ENNReal.ofReal (delta / epsilon) ∂muT := by
            apply lintegral_mono
            intro V
            by_cases hV : energy V <= delta
            · simpa only [Set.preimage_setOf_eq, and_iff_left hV] using hcond V hV
            · simp only [Set.preimage_setOf_eq, hV, and_false, Set.setOf_false,
                measure_empty]
              exact bot_le
      _ = ENNReal.ofReal (delta / epsilon) := by simp [muT]
  have hsplit : {q | epsilon <= Z q} ⊆
      {q | delta < energy q.2} ∪ {q | epsilon <= Z q ∧ energy q.2 <= delta} := by
    intro q hq
    by_cases hqE : delta < energy q.2
    · exact Or.inl hqE
    · exact Or.inr ⟨hq, not_lt.mp hqE⟩
  have hprod_bound : (muS.prod muT).real {q | epsilon <= Z q} <=
      (muS.prod muT).real {q | delta < energy q.2} + delta / epsilon := by
    calc
      (muS.prod muT).real {q | epsilon <= Z q} <=
          (muS.prod muT).real {q | delta < energy q.2} +
            (muS.prod muT).real {q | epsilon <= Z q ∧ energy q.2 <= delta} :=
        (measureReal_mono hsplit).trans (measureReal_union_le _ _)
      _ <= (muS.prod muT).real {q | delta < energy q.2} + delta / epsilon := by
        gcongr
        rw [measureReal_def]
        calc
          ((muS.prod muT) {q | epsilon <= Z q ∧ energy q.2 <= delta}).toReal <=
              (ENNReal.ofReal (delta / epsilon)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hgood_bound
          _ = delta / epsilon := ENNReal.toReal_ofReal (div_nonneg hdelta.le hepsilon.le)
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : I => P) block
  have htarget_eq : e ⁻¹' {q | epsilon <= Z q} =
      {X | epsilon <= c * ∑ i : {i : I // block i}, f X (X i.1)} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← hZ_combine (e X).1 (e X).2]
    simp only [combine, e.symm_apply_apply]
  have hbad_eq : e ⁻¹' {q | delta < energy q.2} =
      {X | delta < ∫ x, f X x ∂P} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [← henergy_combine (e X).1 (e X).2]
    simp only [combine, e.symm_apply_apply]
  have htarget_real : (Measure.pi (fun _ : I => P)).real
      {X | epsilon <= c * ∑ i : {i : I // block i}, f X (X i.1)} =
      (muS.prod muT).real {q | epsilon <= Z q} := by
    rw [← htarget_eq, ← hmp.map_eq]
    change (Measure.pi (fun _ : I => P)).real (e ⁻¹' {q | epsilon <= Z q}) =
      (Measure.map e (Measure.pi (fun _ : I => P))).real {q | epsilon <= Z q}
    simp only [measureReal_def, e.map_apply]
  have hbad_real : (Measure.pi (fun _ : I => P)).real
      {X | delta < ∫ x, f X x ∂P} =
      (muS.prod muT).real {q | delta < energy q.2} := by
    rw [← hbad_eq, ← hmp.map_eq]
    change (Measure.pi (fun _ : I => P)).real (e ⁻¹' {q | delta < energy q.2}) =
      (Measure.map e (Measure.pi (fun _ : I => P))).real {q | delta < energy q.2}
    simp only [measureReal_def, e.map_apply]
  rw [htarget_real, hbad_real]
  exact hprod_bound

/-- Empirical mean formed from a two-block sample-split function.  Observation `i`
is evaluated with the function selected by `side n i`; locality hypotheses on users
of this definition express that this function is estimated from the opposite block.
At `n = 0`, the empty sum and totalized inverse make the value zero. -/
noncomputable def splitMean {Ω : Type*} {d : ℕ}
    (side : ∀ n, Fin n → Bool)
    (half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, half n X (side n i) (X i)

/-- Ordinary empirical mean of a possibly row-varying vector-valued function.
At `n = 0`, the empty sum and totalized inverse make the value zero. -/
noncomputable def empMean {Ω : Type*} {d : ℕ}
    (base : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) : EuclideanSpace ℝ (Fin d) :=
  (n : ℝ)⁻¹ • ∑ i, base n (X i)

/-- Empirical Gram matrix formed from a two-block sample-split function.
The `(j,k)` entry averages the coordinate products of the same split summand.
At `n = 0`, the empty sum and totalized inverse make the matrix zero. -/
noncomputable def splitGram {Ω : Type*} {d : ℕ}
    (side : ∀ n, Fin n → Bool)
    (half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => (n : ℝ)⁻¹ * ∑ i, half n X (side n i) (X i) j * half n X (side n i) (X i) k

/-- Ordinary empirical Gram matrix of a possibly row-varying vector-valued function.
The `(j,k)` entry averages `base n x j * base n x k`.  At `n = 0`, the empty
sum and totalized inverse make the matrix zero. -/
noncomputable def empGram {Ω : Type*} {d : ℕ}
    (base : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (n : ℕ) (X : Fin n → Ω) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => (n : ℝ)⁻¹ * ∑ i, base n (X i) j * base n (X i) k

/-- Population Gram matrix of a vector-valued function under `P`. Bochner
integration is totalized by Mathlib; `MemLp` hypotheses ensure integrability of
the coordinate products whenever this definition is applied. -/
noncomputable def populationGram {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (f : Ω → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => ∫ x, f x j * f x k ∂P

/-- Opposite-block locality and conditional first/second-moment control replace a
sample-split empirical mean by the empirical mean of its deterministic row anchor.
No balance or asymptotic-size condition is imposed on the two blocks. -/
theorem splitMean_sub_empMean_tendstoInProbZero
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (side : ∀ n, Fin n → Bool)
    (half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d))
    (base : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    -- the function used on block `b` depends only on the opposite block.
    (h_local : ∀ n (X Y : Fin n → Ω) b,
      (∀ i, side n i ≠ b → X i = Y i) → half n X b = half n Y b)
    -- joint measurability supplies all sample and observation sections
    -- needed by product-measure conditioning and Fubini.
    (h_joint : ∀ n b, Measurable (fun p : (Fin n → Ω) × Ω => half n p.1 b p.2))
    -- the deterministic row anchor is square-integrable.
    (h_base_memLp : ∀ n, MemLp (base n) 2 (P n))
    -- each realized opposite-block estimate is square-integrable.
    (h_half_memLp : ∀ n X b, MemLp (half n X b) 2 (P n))
    -- the deterministic row anchor is centered under its row law.
    (h_base_centered : ∀ n, (∫ x, base n x ∂(P n)) = 0)
    -- each blockwise estimated function has root-n negligible mean.
    (h_mean : ∀ b : Bool,
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
        (fun n X => Real.sqrt n • ∫ x, half n X b x ∂(P n)))
    -- each blockwise estimate has negligible population L2 distance
    -- from the deterministic row anchor.
    (h_l2 : ∀ b : Bool,
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
        (fun n X => ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n))) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => Real.sqrt n • (splitMean side half n X - empMean base n X)) := by
  classical
  let base' : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n =>
    (h_base_memLp n).aestronglyMeasurable.mk (base n)
  have hbase'_meas (n : ℕ) : Measurable (base' n) := by
    exact (h_base_memLp n).aestronglyMeasurable.measurable_mk
  have hbase_ae (n : ℕ) : base n =ᵐ[P n] base' n := by
    exact (h_base_memLp n).aestronglyMeasurable.ae_eq_mk
  have hbase'_memLp (n : ℕ) : MemLp (base' n) 2 (P n) :=
    (h_base_memLp n).ae_eq (hbase_ae n)
  have hbase'_centered (n : ℕ) : ∫ x, base' n x ∂(P n) = 0 := by
    rw [integral_congr_ae (hbase_ae n).symm]
    exact h_base_centered n
  let diff : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d) :=
    fun n X b x => half n X b x - base' n x
  have hdiff_joint (n : ℕ) (b : Bool) :
      Measurable (fun p : (Fin n → Ω) × Ω => diff n p.1 b p.2) := by
    exact (h_joint n b).sub ((hbase'_meas n).comp measurable_snd)
  have hdiff_memLp (n : ℕ) (X : Fin n → Ω) (b : Bool) :
      MemLp (diff n X b) 2 (P n) :=
    (h_half_memLp n X b).sub (hbase'_memLp n)
  have hdiff_ae (n : ℕ) (X : Fin n → Ω) (b : Bool) :
      diff n X b =ᵐ[P n] fun x => half n X b x - base n x := by
    filter_upwards [hbase_ae n] with x hx
    simp only [diff]
    rw [← hx]
  have henergy (b : Bool) (j : Fin d) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
        (fun n X => ∫ x, (diff n X b x j) ^ 2 ∂(P n)) := by
    apply TendstoInProbZero.mono_norm (h_l2 b)
    intro n X
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _),
      abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    have hcoordL2 : MemLp (fun x => diff n X b x j) 2 (P n) :=
      by
        simpa using ((hdiff_memLp n X b).continuousLinearMap_comp
          (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    have hnorm_int : Integrable (fun x => ‖diff n X b x‖ ^ 2) (P n) :=
      (memLp_two_iff_integrable_sq_norm (hdiff_memLp n X b).aestronglyMeasurable).mp
        (hdiff_memLp n X b)
    calc
      (∫ x, (diff n X b x j) ^ 2 ∂(P n)) ≤
          ∫ x, ‖diff n X b x‖ ^ 2 ∂(P n) := by
        apply integral_mono hcoordL2.integrable_sq hnorm_int
        intro x
        have hj := PiLp.norm_apply_le (diff n X b x) j
        simp only [Real.norm_eq_abs] at hj
        change (diff n X b x j) ^ 2 ≤ ‖diff n X b x‖ ^ 2
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hj 2
      _ = ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n) := by
        apply integral_congr_ae
        filter_upwards [hdiff_ae n X b] with x hx
        rw [hx]
  have hcenter_coord (b : Bool) (j : Fin d) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
        (fun n X => (Real.sqrt n * (n : ℝ)⁻¹) *
          ∑ i : {i : Fin n // side n i = b},
            (diff n X b (X i.1) j - ∫ x, diff n X b x j ∂(P n))) := by
    intro epsilon hepsilon
    rw [Metric.tendsto_atTop]
    intro eta heta
    let delta := eta * epsilon ^ 2 / 4
    have hdelta : 0 < delta := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (henergy b j delta hdelta) (eta / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have htail := splitBlock_centered_tail (P n) (fun i : Fin n => side n i = b)
      (fun X x => diff n X b x j)
      ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp
        (hdiff_joint n b))
      (fun X Y hXY => by
        funext x
        simp only [diff]
        rw [h_local n X Y b (fun i hi => hXY i hi)])
      (fun X => by
        simpa using ((hdiff_memLp n X b).continuousLinearMap_comp
          (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)))
      hdelta hepsilon (sqrt_mul_inv_sq_card_subtype_le n (fun i => side n i = b))
    have hbad : (Measure.pi (fun _ : Fin n => P n)).real
        {X | delta < ∫ x, (diff n X b x j) ^ 2 ∂(P n)} < eta / 2 := by
      calc
        (Measure.pi (fun _ : Fin n => P n)).real
            {X | delta < ∫ x, (diff n X b x j) ^ 2 ∂(P n)}
            ≤ (Measure.pi (fun _ : Fin n => P n)).real
              {X | delta ≤ ‖∫ x, (diff n X b x j) ^ 2 ∂(P n)‖} := by
                refine measureReal_mono ?_ (measure_ne_top _ _)
                intro X hX
                change delta < ∫ x, (diff n X b x j) ^ 2 ∂(P n) at hX
                change delta ≤ ‖∫ x, (diff n X b x j) ^ 2 ∂(P n)‖
                simp only [Real.norm_eq_abs]
                rw [abs_of_nonneg (integral_nonneg fun x => sq_nonneg (diff n X b x j))]
                exact hX.le
        _ < eta / 2 := by
          have := hN n hn
          rwa [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] at this
    have hdelta_term : delta / epsilon ^ 2 = eta / 4 := by
      dsimp only [delta]
      field_simp
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    calc
      (Measure.pi (fun _ : Fin n => P n)).real
          {X | epsilon ≤ ‖(Real.sqrt n * (n : ℝ)⁻¹) *
            ∑ i : {i : Fin n // side n i = b},
              (diff n X b (X i.1) j - ∫ x, diff n X b x j ∂(P n))‖}
          = (Measure.pi (fun _ : Fin n => P n)).real
            {X | epsilon ≤ |(Real.sqrt n * (n : ℝ)⁻¹) *
              ∑ i : {i : Fin n // side n i = b},
                (diff n X b (X i.1) j - ∫ x, diff n X b x j ∂(P n))|} := by
                  simp only [Real.norm_eq_abs]
      _ ≤ (Measure.pi (fun _ : Fin n => P n)).real
            {X | delta < ∫ x, (diff n X b x j) ^ 2 ∂(P n)} +
          delta / epsilon ^ 2 := htail
      _ < eta := by rw [hdelta_term]; linarith
  let centered : Bool → ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) := fun b n X =>
    (WithLp.equiv 2 (Fin d → ℝ)).symm (fun j => (Real.sqrt n * (n : ℝ)⁻¹) *
      ∑ i : {i : Fin n // side n i = b},
        (diff n X b (X i.1) j - ∫ x, diff n X b x j ∂(P n)))
  have hcenter (b : Bool) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n)) (centered b) := by
    apply TendstoInProbZero.euclidean_of_coordinate
    intro j
    simpa only [centered] using! hcenter_coord b j
  let bias : Bool → ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d) := fun b n X =>
    ((Fintype.card {i : Fin n // side n i = b} : ℝ) * (n : ℝ)⁻¹) •
      (Real.sqrt n • ∫ x, half n X b x ∂(P n))
  have hbias (b : Bool) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n)) (bias b) := by
    apply TendstoInProbZero.mono_norm (h_mean b)
    intro n X
    have hc := card_subtype_mul_inv_mem_Icc n (fun i => side n i = b)
    simp only [bias, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc.1]
    exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (norm_nonneg _)) hc.2
  have hblocks : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => ∑ b : Bool, (centered b n X + bias b n X)) := by
    simpa using TendstoInProbZero.finset_sum (Finset.univ : Finset Bool)
      (fun b _ => TendstoInProbZero.add (hcenter b) (hbias b))
  have hbase_coord_centered (n : ℕ) (j : Fin d) :
      ∫ x, base' n x j ∂(P n) = 0 := by
    have hcoord (i : Fin d) : Integrable (fun x => base' n x i) (P n) :=
      ((hbase'_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) i :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).integrable one_le_two
    rw [← MeasureTheory.eval_integral_piLp hcoord j, hbase'_centered n]
    rfl
  have hdiff_integral (n : ℕ) (X : Fin n → Ω) (b : Bool) (j : Fin d) :
      ∫ x, diff n X b x j ∂(P n) = ∫ x, half n X b x j ∂(P n) := by
    have hh : Integrable (fun x => half n X b x j) (P n) :=
      ((h_half_memLp n X b).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).integrable one_le_two
    have hb : Integrable (fun x => base' n x j) (P n) :=
      ((hbase'_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).integrable one_le_two
    simp only [diff, PiLp.sub_apply]
    rw [integral_sub hh hb, hbase_coord_centered n j, sub_zero]
  have hdecomp (n : ℕ) (X : Fin n → Ω) :
      Real.sqrt n • (splitMean side half n X - empMean base' n X) =
        ∑ b : Bool, (centered b n X + bias b n X) := by
    ext j
    have hblock (b : Bool) :
        (centered b n X + bias b n X) j =
          (Real.sqrt n * (n : ℝ)⁻¹) *
            ∑ i : {i : Fin n // side n i = b}, diff n X b (X i.1) j := by
      simp only [centered, bias, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        WithLp.equiv_symm_apply]
      rw [Finset.sum_sub_distrib]
      simp_rw [hdiff_integral n X b j]
      have hhalf_coord (i : Fin d) : Integrable (fun x => half n X b x i) (P n) :=
        ((h_half_memLp n X b).continuousLinearMap_comp
          (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) i :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).integrable one_le_two
      rw [MeasureTheory.eval_integral_piLp hhalf_coord j, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    change _ = ∑ b : Bool, (centered b n X + bias b n X) j
    simp_rw [hblock]
    rw [← Finset.mul_sum]
    have hfiber : (∑ b : Bool, ∑ i : {i : Fin n // side n i = b},
        diff n X b (X i.1) j) = ∑ i : Fin n, diff n X (side n i) (X i) j := by
      calc
        (∑ b : Bool, ∑ i : {i : Fin n // side n i = b}, diff n X b (X i.1) j) =
            ∑ b : Bool, ∑ i : {i : Fin n // side n i = b},
              diff n X (side n i.1) (X i.1) j := by
                apply Finset.sum_congr rfl
                intro b _
                apply Finset.sum_congr rfl
                intro i _
                rw [i.2]
        _ = ∑ i : Fin n, diff n X (side n i) (X i) j :=
          Fintype.sum_fiberwise (side n) (fun i => diff n X (side n i) (X i) j)
    rw [hfiber]
    simp only [splitMean, empMean, PiLp.smul_apply, PiLp.sub_apply,
      diff, smul_eq_mul]
    have hsum_half : (∑ i, half n X (side n i) (X i)) j =
        ∑ i, half n X (side n i) (X i) j := by
      simp
    have hsum_base : (∑ i, base' n (X i)) j = ∑ i, base' n (X i) j := by
      simp
    rw [hsum_half, hsum_base]
    change Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i, half n X (side n i) (X i) j -
        (n : ℝ)⁻¹ * ∑ i, base' n (X i) j) =
      Real.sqrt n * (n : ℝ)⁻¹ *
        ∑ i, (half n X (side n i) (X i) j - base' n (X i) j)
    rw [Finset.sum_sub_distrib]
    ring
  have hrepresentative : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => Real.sqrt n • (splitMean side half n X - empMean base' n X)) := by
    convert hblocks using 1
    funext n X
    exact hdecomp n X
  intro epsilon hepsilon
  convert hrepresentative epsilon hepsilon using 1
  funext n
  apply measureReal_congr
  have hpi : (fun (X : Fin n → Ω) i => base n (X i)) =ᵐ[
      Measure.pi (fun _ : Fin n => P n)] fun X i => base' n (X i) :=
    MeasureTheory.Measure.ae_eq_pi (fun _ => hbase_ae n)
  filter_upwards [hpi] with X hX
  have hemp : empMean base n X = empMean base' n X := by
    unfold empMean
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun hX i
  change (epsilon ≤ ‖Real.sqrt n • (splitMean side half n X - empMean base n X)‖) =
    (epsilon ≤ ‖Real.sqrt n • (splitMean side half n X - empMean base' n X)‖)
  rw [hemp]

set_option maxHeartbeats 800000 in
-- The product-law conditioning and finite matrix-coordinate lift need the larger elaboration budget.
/-- Population L2 replacement and a uniform L2 anchor replace a sample-split Gram
matrix by the empirical Gram matrix of its deterministic row anchor.  No balance
or asymptotic-size condition is imposed on the two blocks. -/
theorem splitGram_sub_empGram_tendstoInProbZero
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : ℕ → Measure Ω) [∀ n, IsProbabilityMeasure (P n)]
    (side : ∀ n, Fin n → Bool)
    (half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d))
    (base : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    -- the function used on block `b` depends only on the opposite block.
    (h_local : ∀ n (X Y : Fin n → Ω) b,
      (∀ i, side n i ≠ b → X i = Y i) → half n X b = half n Y b)
    -- joint measurability supplies all sections used by product Fubini.
    (h_joint : ∀ n b, Measurable (fun p : (Fin n → Ω) × Ω => half n p.1 b p.2))
    -- the deterministic row anchor is square-integrable.
    (h_base_memLp : ∀ n, MemLp (base n) 2 (P n))
    -- each realized opposite-block estimate is square-integrable.
    (h_half_memLp : ∀ n X b, MemLp (half n X b) 2 (P n))
    -- each blockwise estimate has negligible population L2 distance
    -- from the deterministic row anchor.
    (h_l2 : ∀ b : Bool,
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
        (fun n X => ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n)))
    -- the anchor's rowwise L2 energies are uniformly bounded; this
    -- prevents the product replacement estimate from being vacuous.
    (h_base_l2_bdd : ∃ C : ℝ, ∀ n, ∫ x, ‖base n x‖ ^ 2 ∂(P n) ≤ C) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => splitGram side half n X - empGram base n X) := by
  classical
  rcases h_base_l2_bdd with ⟨C, hC⟩
  let base' : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n =>
    (h_base_memLp n).aestronglyMeasurable.mk (base n)
  have hbase'_meas (n : ℕ) : Measurable (base' n) :=
    (h_base_memLp n).aestronglyMeasurable.measurable_mk
  have hbase_ae (n : ℕ) : base n =ᵐ[P n] base' n :=
    (h_base_memLp n).aestronglyMeasurable.ae_eq_mk
  have hbase'_memLp (n : ℕ) : MemLp (base' n) 2 (P n) :=
    (h_base_memLp n).ae_eq (hbase_ae n)
  have hC' (n : ℕ) : ∫ x, ‖base' n x‖ ^ 2 ∂(P n) <= C := by
    calc
      (∫ x, ‖base' n x‖ ^ 2 ∂(P n)) = ∫ x, ‖base n x‖ ^ 2 ∂(P n) := by
        apply integral_congr_ae
        filter_upwards [hbase_ae n] with x hx
        rw [hx]
      _ <= C := hC n
  have hC_nonneg : 0 <= C :=
    (integral_nonneg fun x => sq_nonneg ‖base' 0 x‖).trans (hC' 0)
  let diff : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d) :=
    fun n X b x => half n X b x - base' n x
  have hdiff_memLp (n : ℕ) (X : Fin n → Ω) (b : Bool) :
      MemLp (diff n X b) 2 (P n) :=
    (h_half_memLp n X b).sub (hbase'_memLp n)
  have hdiff_energy (n : ℕ) (X : Fin n → Ω) (b : Bool) :
      (∫ x, ‖diff n X b x‖ ^ 2 ∂(P n)) =
        ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n) := by
    apply integral_congr_ae
    filter_upwards [hbase_ae n] with x hx
    simp only [diff]
    rw [← hx]
  let q : Bool → ∀ n, (Fin n → Ω) → Fin d → Fin d → Ω → ℝ :=
    fun b n X j k x =>
      |half n X b x j * half n X b x k - base' n x j * base' n x k|
  have hq_joint (b : Bool) (n : ℕ) (j k : Fin d) :
      Measurable (fun p : (Fin n → Ω) × Ω => q b n p.1 j k p.2) := by
    have hhj := ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (h_joint n b))
    have hhk := ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (h_joint n b))
    have hb : Measurable (fun p : (Fin n → Ω) × Ω => base' n p.2) :=
      (hbase'_meas n).comp measurable_snd
    have hbj : Measurable (fun p : (Fin n → Ω) × Ω => base' n p.2 j) :=
      (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
        EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hb
    have hbk : Measurable (fun p : (Fin n → Ω) × Ω => base' n p.2 k) :=
      (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
        EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hb
    exact (hhj.mul hhk |>.sub (hbj.mul hbk)).abs
  have hq_local (b : Bool) (n : ℕ) (j k : Fin d) (X Y : Fin n → Ω)
      (hXY : ∀ i, ¬side n i = b → X i = Y i) : q b n X j k = q b n Y j k := by
    have hh := h_local n X Y b (fun i hi => hXY i (by simpa using hi))
    funext x
    simp only [q, hh]
  have hq_int (b : Bool) (n : ℕ) (X : Fin n → Ω) (j k : Fin d) :
      Integrable (q b n X j k) (P n) := by
    have hhj : MemLp (fun x => half n X b x j) 2 (P n) := by
      simpa using ((h_half_memLp n X b).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    have hhk : MemLp (fun x => half n X b x k) 2 (P n) := by
      simpa using ((h_half_memLp n X b).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    have hbj : MemLp (fun x => base' n x j) 2 (P n) := by
      simpa using ((hbase'_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    have hbk : MemLp (fun x => base' n x k) 2 (P n) := by
      simpa using ((hbase'_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    simpa only [q, Real.norm_eq_abs] using!
      ((hhj.integrable_mul hhk).sub (hbj.integrable_mul hbk)).norm
  have hq_bound (b : Bool) (n : ℕ) (X : Fin n → Ω) (j k : Fin d)
      (A : ℝ) (hA : 0 < A) :
      (∫ x, q b n X j k x ∂(P n)) <=
        (1 + A) * (∫ x, ‖diff n X b x‖ ^ 2 ∂(P n)) +
          (∫ x, ‖base' n x‖ ^ 2 ∂(P n)) / A := by
    have hdiff_sq : Integrable (fun x => ‖diff n X b x‖ ^ 2) (P n) :=
      (memLp_two_iff_integrable_sq_norm (hdiff_memLp n X b).aestronglyMeasurable).mp
        (hdiff_memLp n X b)
    have hbase_sq : Integrable (fun x => ‖base' n x‖ ^ 2) (P n) :=
      (memLp_two_iff_integrable_sq_norm (hbase'_memLp n).aestronglyMeasurable).mp
        (hbase'_memLp n)
    rw [← integral_const_mul, ← integral_div,
      ← integral_add (hdiff_sq.const_mul (1 + A)) (hbase_sq.div_const A)]
    apply integral_mono (hq_int b n X j k)
      ((hdiff_sq.const_mul (1 + A)).add (hbase_sq.div_const A))
    intro x
    let D := ‖diff n X b x‖
    let B := ‖base' n x‖
    have hdj : |half n X b x j - base' n x j| <= D := by
      simpa only [diff, PiLp.sub_apply, Real.norm_eq_abs, D] using
        PiLp.norm_apply_le (diff n X b x) j
    have hdk : |half n X b x k - base' n x k| <= D := by
      simpa only [diff, PiLp.sub_apply, Real.norm_eq_abs, D] using
        PiLp.norm_apply_le (diff n X b x) k
    have hbj : |base' n x j| <= B := by
      simpa only [Real.norm_eq_abs, B] using PiLp.norm_apply_le (base' n x) j
    have hbk : |base' n x k| <= B := by
      simpa only [Real.norm_eq_abs, B] using PiLp.norm_apply_le (base' n x) k
    have hraw : q b n X j k x <= D ^ 2 + 2 * D * B := by
      change |half n X b x j * half n X b x k - base' n x j * base' n x k| <=
        D ^ 2 + 2 * D * B
      rw [show half n X b x j * half n X b x k - base' n x j * base' n x k =
        (half n X b x j - base' n x j) * (half n X b x k - base' n x k) +
        (half n X b x j - base' n x j) * base' n x k +
        base' n x j * (half n X b x k - base' n x k) by ring]
      calc
        |(half n X b x j - base' n x j) * (half n X b x k - base' n x k) +
            (half n X b x j - base' n x j) * base' n x k +
            base' n x j * (half n X b x k - base' n x k)| <=
            |(half n X b x j - base' n x j) * (half n X b x k - base' n x k) +
              (half n X b x j - base' n x j) * base' n x k| +
              |base' n x j * (half n X b x k - base' n x k)| := abs_add_le _ _
        _ <=
            |half n X b x j - base' n x j| * |half n X b x k - base' n x k| +
            |half n X b x j - base' n x j| * |base' n x k| +
            |base' n x j| * |half n X b x k - base' n x k| := by
              calc
                _ <= (|(half n X b x j - base' n x j) *
                    (half n X b x k - base' n x k)| +
                    |(half n X b x j - base' n x j) * base' n x k|) +
                    |base' n x j * (half n X b x k - base' n x k)| :=
                  add_le_add (abs_add_le _ _) le_rfl
                _ = _ := by simp only [abs_mul]
        _ <= D * D + D * B + B * D := by gcongr
        _ = D ^ 2 + 2 * D * B := by ring
    have hyoung : 2 * D * B <= A * D ^ 2 + B ^ 2 / A := by
      rw [show A * D ^ 2 + B ^ 2 / A = (A ^ 2 * D ^ 2 + B ^ 2) / A by
        field_simp]
      apply (le_div_iff₀ hA).2
      nlinarith [sq_nonneg (A * D - B)]
    change q b n X j k x <= (1 + A) * D ^ 2 + B ^ 2 / A
    dsimp only [D, B] at hraw hyoung ⊢
    exact hraw.trans (by nlinarith)
  have hq_energy (b : Bool) (j k : Fin d) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
        (fun n X => ∫ x, q b n X j k x ∂(P n)) := by
    intro epsilon hepsilon
    rw [Metric.tendsto_atTop]
    intro eta heta
    let A := 4 * (C + 1) / epsilon + 1
    have hA : 0 < A := by
      dsimp only [A]
      have : 0 < C + 1 := by linarith
      positivity
    have hCA : C / A < epsilon / 4 := by
      have hAe : 4 * C < epsilon * A := by
        dsimp only [A]
        field_simp
        nlinarith
      rw [div_lt_iff₀ hA]
      nlinarith
    let gamma := epsilon / (2 * (1 + A))
    have hgamma : 0 < gamma := by
      dsimp only [gamma]
      positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (h_l2 b gamma hgamma) eta heta
    refine ⟨N, fun n hn => ?_⟩
    have hsubset : {X : Fin n → Ω | epsilon <= ‖∫ x, q b n X j k x ∂(P n)‖} ⊆
        {X | gamma <= ‖∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n)‖} := by
      intro X hX
      change epsilon <= ‖∫ x, q b n X j k x ∂(P n)‖ at hX
      change gamma <= ‖∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n)‖
      have hX' : epsilon <= ∫ x, q b n X j k x ∂(P n) := by
        have hnonneg : 0 <= ∫ x, q b n X j k x ∂(P n) :=
          integral_nonneg fun x => abs_nonneg _
        simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hX
      have hraw_nonneg : 0 <= ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n) :=
        integral_nonneg fun x => sq_nonneg _
      by_contra hnot
      have hnot' : ¬ gamma <= ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂(P n) := by
        intro hg
        apply hnot
        simpa only [Real.norm_eq_abs, abs_of_nonneg hraw_nonneg] using hg
      have hD : (∫ x, ‖diff n X b x‖ ^ 2 ∂(P n)) < gamma := by
        rw [hdiff_energy n X b]
        exact lt_of_not_ge hnot'
      have hbound := hq_bound b n X j k A hA
      have hBC := hC' n
      have hsmall : (∫ x, q b n X j k x ∂(P n)) < epsilon := by
        calc
          (∫ x, q b n X j k x ∂(P n)) <=
              (1 + A) * (∫ x, ‖diff n X b x‖ ^ 2 ∂(P n)) +
                (∫ x, ‖base' n x‖ ^ 2 ∂(P n)) / A := hbound
          _ < (1 + A) * gamma + C / A := by
            exact add_lt_add_of_lt_of_le
              (mul_lt_mul_of_pos_left hD (by linarith))
              (div_le_div_of_nonneg_right hBC hA.le)
          _ < epsilon := by
            have hAgamma : (1 + A) * gamma = epsilon / 2 := by
              dsimp only [gamma]
              field_simp
            rw [hAgamma]
            linarith
      exact (not_lt_of_ge hX') hsmall
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (μ := Measure.pi (fun _ : Fin n => P n)) hsubset).trans_lt
      (by simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hN n hn)
  let Q : Bool → Fin d → Fin d → ∀ n, (Fin n → Ω) → ℝ := fun b j k n X =>
    (n : ℝ)⁻¹ * ∑ i : {i : Fin n // side n i = b}, q b n X j k (X i.1)
  have hQ (b : Bool) (j k : Fin d) :
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n)) (Q b j k) := by
    intro epsilon hepsilon
    rw [Metric.tendsto_atTop]
    intro eta heta
    let delta := eta * epsilon / 4
    have hdelta : 0 < delta := by positivity
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hq_energy b j k delta hdelta)
      (eta / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have htail := splitBlock_nonneg_tail (P n) (fun i : Fin n => side n i = b)
      (q b n · j k) (hq_joint b n j k)
      (fun X Y hXY => hq_local b n j k X Y hXY)
      (fun X x => abs_nonneg _) (fun X => hq_int b n X j k)
      (inv_nonneg.mpr (Nat.cast_nonneg n)) hdelta hepsilon
      (by simpa [mul_comm] using (card_subtype_mul_inv_mem_Icc n
        (fun i => side n i = b)).2)
    have hbad : (Measure.pi (fun _ : Fin n => P n)).real
        {X | delta < ∫ x, q b n X j k x ∂(P n)} < eta / 2 := by
      calc
        _ <= (Measure.pi (fun _ : Fin n => P n)).real
            {X | delta <= ‖∫ x, q b n X j k x ∂(P n)‖} := by
              apply measureReal_mono (μ := Measure.pi (fun _ : Fin n => P n))
              intro X hX
              change delta < ∫ x, q b n X j k x ∂(P n) at hX
              change delta <= ‖∫ x, q b n X j k x ∂(P n)‖
              have hnonneg : 0 <= ∫ x, q b n X j k x ∂(P n) :=
                integral_nonneg fun x => abs_nonneg _
              simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hX.le
        _ < eta / 2 := by
          simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hN n hn
    have hdelta_term : delta / epsilon = eta / 4 := by
      dsimp only [delta]
      field_simp
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    calc
      (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon <= ‖Q b j k n X‖} =
          (Measure.pi (fun _ : Fin n => P n)).real
            {X | epsilon <= (n : ℝ)⁻¹ * ∑ i : {i : Fin n // side n i = b},
              q b n X j k (X i.1)} := by
                apply measureReal_congr
                apply Filter.Eventually.of_forall
                intro X
                simp only [Q, Real.norm_eq_abs]
                change (epsilon <= |(n : ℝ)⁻¹ * ∑ i : {i : Fin n // side n i = b},
                  q b n X j k (X i.1)|) =
                  (epsilon <= (n : ℝ)⁻¹ * ∑ i : {i : Fin n // side n i = b},
                    q b n X j k (X i.1))
                rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
                  (Finset.sum_nonneg fun i _ => abs_nonneg _))]
      _ <= (Measure.pi (fun _ : Fin n => P n)).real
            {X | delta < ∫ x, q b n X j k x ∂(P n)} + delta / epsilon := htail
      _ < eta := by rw [hdelta_term]; linarith
  have hentry (j k : Fin d) : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => (splitGram side half n X - empGram base' n X) j k) := by
    have hsum := TendstoInProbZero.finset_sum (Finset.univ : Finset Bool)
      (fun b _ => hQ b j k)
    apply TendstoInProbZero.mono_norm hsum
    intro n X
    simp only [Real.norm_eq_abs]
    have hfiber : (∑ b : Bool, ∑ i : {i : Fin n // side n i = b},
        (half n X b (X i.1) j * half n X b (X i.1) k -
          base' n (X i.1) j * base' n (X i.1) k)) =
        ∑ i : Fin n, (half n X (side n i) (X i) j * half n X (side n i) (X i) k -
          base' n (X i) j * base' n (X i) k) := by
      calc
        _ = ∑ b : Bool, ∑ i : {i : Fin n // side n i = b},
            (half n X (side n i.1) (X i.1) j * half n X (side n i.1) (X i.1) k -
              base' n (X i.1) j * base' n (X i.1) k) := by
                apply Finset.sum_congr rfl
                intro b _
                apply Finset.sum_congr rfl
                intro i _
                rw [i.2]
        _ = _ := by
          simpa only using Fintype.sum_fiberwise (side n)
            (fun i => half n X (side n i) (X i) j * half n X (side n i) (X i) k -
              base' n (X i) j * base' n (X i) k)
    simp only [splitGram, empGram, Matrix.sub_apply]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [← hfiber, Finset.mul_sum]
    calc
      |∑ b : Bool, (n : ℝ)⁻¹ * ∑ i : {i : Fin n // side n i = b},
          (half n X b (X i.1) j * half n X b (X i.1) k -
            base' n (X i.1) j * base' n (X i.1) k)| <=
          ∑ b : Bool, |(n : ℝ)⁻¹ * ∑ i : {i : Fin n // side n i = b},
            (half n X b (X i.1) j * half n X b (X i.1) k -
              base' n (X i.1) j * base' n (X i.1) k)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ b : Bool, (n : ℝ)⁻¹ * ∑ i : {i : Fin n // side n i = b},
          q b n X j k (X i.1) := by
            apply Finset.sum_le_sum
            intro b _
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
            gcongr
            simpa only [q] using Finset.abs_sum_le_sum_abs
              (fun i : {i : Fin n // side n i = b} =>
                half n X b (X i.1) j * half n X b (X i.1) k -
                base' n (X i.1) j * base' n (X i.1) k)
              (Finset.univ : Finset {i : Fin n // side n i = b})
      _ = ‖∑ b : Bool, Q b j k n X‖ := by
        simp only [Q, Real.norm_eq_abs]
        rw [abs_of_nonneg (Finset.sum_nonneg fun b _ => mul_nonneg
          (inv_nonneg.mpr (Nat.cast_nonneg n))
          (Finset.sum_nonneg fun i _ => abs_nonneg _))]
  have hrepresentative : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => splitGram side half n X - empGram base' n X) :=
    TendstoInProbZero.matrix_of_entry hentry
  intro epsilon hepsilon
  convert hrepresentative epsilon hepsilon using 1
  funext n
  apply measureReal_congr
  have hpi : (fun (X : Fin n → Ω) i => base n (X i)) =ᵐ[
      Measure.pi (fun _ : Fin n => P n)] fun X i => base' n (X i) :=
    MeasureTheory.Measure.ae_eq_pi (fun _ => hbase_ae n)
  filter_upwards [hpi] with X hX
  have hemp : empGram base n X = empGram base' n X := by
    ext j k
    unfold empGram
    apply congrArg ((n : ℝ)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro i _
    rw [congrFun hX i]
  change (epsilon <= ‖splitGram side half n X - empGram base n X‖) =
    (epsilon <= ‖splitGram side half n X - empGram base' n X‖)
  rw [hemp]

set_option maxHeartbeats 800000 in
-- The fixed-anchor proof combines the preceding split argument with two entrywise LLN lifts.
/-- Under a fixed observation law, a deterministic L2 anchor identifies the limit
of a sample-split empirical Gram matrix.  The anchor is indispensable: rowwise
square-integrability alone does not control a triangular array. -/
theorem splitGram_tendstoInProbZero
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (side : ∀ n, Fin n → Bool)
    (half : ∀ n, (Fin n → Ω) → Bool → Ω → EuclideanSpace ℝ (Fin d))
    (base : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (base0 : Ω → EuclideanSpace ℝ (Fin d))
    -- the function used on block `b` depends only on the opposite block.
    (h_local : ∀ n (X Y : Fin n → Ω) b,
      (∀ i, side n i ≠ b → X i = Y i) → half n X b = half n Y b)
    -- joint measurability supplies all sections used by product Fubini.
    (h_joint : ∀ n b, Measurable (fun p : (Fin n → Ω) × Ω => half n p.1 b p.2))
    -- every deterministic row function is square-integrable.
    (h_base_memLp : ∀ n, MemLp (base n) 2 P)
    -- each realized opposite-block estimate is square-integrable.
    (h_half_memLp : ∀ n X b, MemLp (half n X b) 2 P)
    -- each blockwise estimate has negligible population L2 distance
    -- from its deterministic row function.
    (h_l2 : ∀ b : Bool,
      TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
        (fun n X => ∫ x, ‖half n X b x - base n x‖ ^ 2 ∂P))
    -- the fixed limiting anchor is square-integrable.
    (h_base0_memLp : MemLp base0 2 P)
    -- the deterministic rows converge to the fixed anchor in L2.
    (h_base_l2 : Tendsto (fun n => ∫ x, ‖base n x - base0 x‖ ^ 2 ∂P)
      atTop (nhds 0)) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => splitGram side half n X - populationGram P base0) := by
  classical
  let D : ℕ → ℝ := fun n => ∫ x, ‖base n x - base0 x‖ ^ 2 ∂P
  have hD : Tendsto D atTop (nhds 0) := h_base_l2
  have hdiff_memLp (n : ℕ) : MemLp (fun x => base n x - base0 x) 2 P :=
    (h_base_memLp n).sub h_base0_memLp
  have hD_nonneg (n : ℕ) : 0 <= D n := integral_nonneg fun x => sq_nonneg _
  have hbase0_sq : Integrable (fun x => ‖base0 x‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm h_base0_memLp.aestronglyMeasurable).mp h_base0_memLp
  let B0 := ∫ x, ‖base0 x‖ ^ 2 ∂P
  have hB0_nonneg : 0 <= B0 := integral_nonneg fun x => sq_nonneg _
  rcases hD.bddAbove_range with ⟨Dmax, hDmax⟩
  have hD_le (n : ℕ) : D n <= Dmax := hDmax ⟨n, rfl⟩
  have hbase_energy (n : ℕ) : ∫ x, ‖base n x‖ ^ 2 ∂P <= 2 * D n + 2 * B0 := by
    have hbase_sq : Integrable (fun x => ‖base n x‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm (h_base_memLp n).aestronglyMeasurable).mp
        (h_base_memLp n)
    have hdiff_sq : Integrable (fun x => ‖base n x - base0 x‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm (hdiff_memLp n).aestronglyMeasurable).mp
        (hdiff_memLp n)
    rw [show 2 * D n + 2 * B0 =
        ∫ x, (2 * ‖base n x - base0 x‖ ^ 2 + 2 * ‖base0 x‖ ^ 2) ∂P by
      simp only [D, B0, integral_add (hdiff_sq.const_mul 2) (hbase0_sq.const_mul 2),
        integral_const_mul]]
    apply integral_mono hbase_sq ((hdiff_sq.const_mul 2).add (hbase0_sq.const_mul 2))
    intro x
    have hn := norm_add_le (base n x - base0 x) (base0 x)
    rw [sub_add_cancel] at hn
    change ‖base n x‖ ^ 2 <=
      2 * ‖base n x - base0 x‖ ^ 2 + 2 * ‖base0 x‖ ^ 2
    nlinarith [sq_nonneg (‖base n x - base0 x‖ - ‖base0 x‖),
      norm_nonneg (base n x), norm_nonneg (base n x - base0 x), norm_nonneg (base0 x)]
  have hbase_bdd : ∃ C : ℝ, ∀ n, ∫ x, ‖base n x‖ ^ 2 ∂P <= C := by
    refine ⟨2 * Dmax + 2 * B0, fun n => (hbase_energy n).trans ?_⟩
    linarith [hD_le n]
  have hsplit := splitGram_sub_empGram_tendstoInProbZero
    (fun _ : ℕ => P) side half base h_local h_joint h_base_memLp h_half_memLp h_l2 hbase_bdd
  let base' : ℕ → Ω → EuclideanSpace ℝ (Fin d) := fun n =>
    (h_base_memLp n).aestronglyMeasurable.mk (base n)
  let base0' : Ω → EuclideanSpace ℝ (Fin d) :=
    h_base0_memLp.aestronglyMeasurable.mk base0
  have hbase'_meas (n : ℕ) : Measurable (base' n) :=
    (h_base_memLp n).aestronglyMeasurable.measurable_mk
  have hbase0'_meas : Measurable base0' :=
    h_base0_memLp.aestronglyMeasurable.measurable_mk
  have hbase_ae (n : ℕ) : base n =ᵐ[P] base' n :=
    (h_base_memLp n).aestronglyMeasurable.ae_eq_mk
  have hbase0_ae : base0 =ᵐ[P] base0' :=
    h_base0_memLp.aestronglyMeasurable.ae_eq_mk
  have hbase'_memLp (n : ℕ) : MemLp (base' n) 2 P :=
    (h_base_memLp n).ae_eq (hbase_ae n)
  have hbase0'_memLp : MemLp base0' 2 P :=
    h_base0_memLp.ae_eq hbase0_ae
  have hdiff'_memLp (n : ℕ) : MemLp (fun x => base' n x - base0' x) 2 P :=
    (hbase'_memLp n).sub hbase0'_memLp
  have hD' (n : ℕ) : (∫ x, ‖base' n x - base0' x‖ ^ 2 ∂P) = D n := by
    apply integral_congr_ae
    filter_upwards [hbase_ae n, hbase0_ae] with x hx hx0
    rw [← hx, ← hx0]
  have hB0' : (∫ x, ‖base0' x‖ ^ 2 ∂P) = B0 := by
    apply integral_congr_ae
    filter_upwards [hbase0_ae] with x hx
    rw [← hx]
  let q : ℕ → Fin d → Fin d → Ω → ℝ := fun n j k x =>
    |base' n x j * base' n x k - base0' x j * base0' x k|
  have hq_int (n : ℕ) (j k : Fin d) : Integrable (q n j k) P := by
    have hnj : MemLp (fun x => base' n x j) 2 P := by
      simpa using ((hbase'_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    have hnk : MemLp (fun x => base' n x k) 2 P := by
      simpa using ((hbase'_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    have h0j : MemLp (fun x => base0' x j) 2 P := by
      simpa using (hbase0'_memLp.continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    have h0k : MemLp (fun x => base0' x k) 2 P := by
      simpa using (hbase0'_memLp.continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    simpa only [q, Real.norm_eq_abs] using!
      ((hnj.integrable_mul hnk).sub (h0j.integrable_mul h0k)).norm
  have hq_bound (n : ℕ) (j k : Fin d) :
      (∫ x, q n j k x ∂P) <= D n + 2 * Real.sqrt (D n) * Real.sqrt B0 := by
    have hd_sq : Integrable (fun x => ‖base' n x - base0' x‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm (hdiff'_memLp n).aestronglyMeasurable).mp
        (hdiff'_memLp n)
    have hb_sq : Integrable (fun x => ‖base0' x‖ ^ 2) P :=
      (memLp_two_iff_integrable_sq_norm hbase0'_memLp.aestronglyMeasurable).mp
        hbase0'_memLp
    have hcross_int : Integrable (fun x => ‖base' n x - base0' x‖ * ‖base0' x‖) P :=
      (hdiff'_memLp n).norm.integrable_mul hbase0'_memLp.norm
    have hcross : (∫ x, ‖base' n x - base0' x‖ * ‖base0' x‖ ∂P) <=
        Real.sqrt (D n) * Real.sqrt B0 := by
      have hd2 : MemLp (fun x => base' n x - base0' x) (ENNReal.ofReal (2 : ℝ)) P := by
        norm_num
        exact hdiff'_memLp n
      have hb2 : MemLp base0' (ENNReal.ofReal (2 : ℝ)) P := by
        norm_num
        exact hbase0'_memLp
      have hh := integral_mul_norm_le_Lp_mul_Lq (μ := P) (p := (2 : ℝ)) (q := (2 : ℝ))
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hd2 hb2
      have hdint : (∫ x, ‖base' n x - base0' x‖ ^ (2 : ℝ) ∂P) = D n := by
        rw [show (fun x => ‖base' n x - base0' x‖ ^ (2 : ℝ)) =
            fun x => ‖base' n x - base0' x‖ ^ (2 : ℕ) by
          funext x
          rw [Real.rpow_two]]
        exact hD' n
      have hbint : (∫ x, ‖base0' x‖ ^ (2 : ℝ) ∂P) = B0 := by
        rw [show (fun x => ‖base0' x‖ ^ (2 : ℝ)) =
            fun x => ‖base0' x‖ ^ (2 : ℕ) by
          funext x
          rw [Real.rpow_two]]
        exact hB0'
      rw [hdint, hbint] at hh
      simpa only [one_div, Real.sqrt_eq_rpow] using hh
    have hraw_int : (∫ x, q n j k x ∂P) <=
        D n + 2 * (∫ x, ‖base' n x - base0' x‖ * ‖base0' x‖ ∂P) := by
      rw [show D n + 2 * (∫ x, ‖base' n x - base0' x‖ * ‖base0' x‖ ∂P) =
          ∫ x, (‖base' n x - base0' x‖ ^ 2 +
            2 * (‖base' n x - base0' x‖ * ‖base0' x‖)) ∂P by
        rw [integral_add hd_sq (hcross_int.const_mul 2), integral_const_mul, hD']]
      apply integral_mono (hq_int n j k) (hd_sq.add (hcross_int.const_mul 2))
      intro x
      let E := ‖base' n x - base0' x‖
      let A0 := ‖base0' x‖
      have hdj : |base' n x j - base0' x j| <= E := by
        simpa only [Real.norm_eq_abs, E] using! PiLp.norm_apply_le (base' n x - base0' x) j
      have hdk : |base' n x k - base0' x k| <= E := by
        simpa only [Real.norm_eq_abs, E] using! PiLp.norm_apply_le (base' n x - base0' x) k
      have h0j : |base0' x j| <= A0 := by
        simpa only [Real.norm_eq_abs, A0] using PiLp.norm_apply_le (base0' x) j
      have h0k : |base0' x k| <= A0 := by
        simpa only [Real.norm_eq_abs, A0] using PiLp.norm_apply_le (base0' x) k
      change |base' n x j * base' n x k - base0' x j * base0' x k| <=
        E ^ 2 + 2 * (E * A0)
      rw [show base' n x j * base' n x k - base0' x j * base0' x k =
        (base' n x j - base0' x j) * (base' n x k - base0' x k) +
        (base' n x j - base0' x j) * base0' x k +
        base0' x j * (base' n x k - base0' x k) by ring]
      calc
        |(base' n x j - base0' x j) * (base' n x k - base0' x k) +
            (base' n x j - base0' x j) * base0' x k +
            base0' x j * (base' n x k - base0' x k)| <=
          |(base' n x j - base0' x j) * (base' n x k - base0' x k) +
            (base' n x j - base0' x j) * base0' x k| +
          |base0' x j * (base' n x k - base0' x k)| := abs_add_le _ _
        _ <=
          |(base' n x j - base0' x j) * (base' n x k - base0' x k)| +
          |(base' n x j - base0' x j) * base0' x k| +
          |base0' x j * (base' n x k - base0' x k)| := by
            exact add_le_add (abs_add_le _ _) le_rfl
        _ <= E * E + E * A0 + A0 * E := by
          simp only [abs_mul]
          gcongr
        _ = E ^ 2 + 2 * (E * A0) := by ring
    exact hraw_int.trans (by linarith)
  have hq_zero (j k : Fin d) : Tendsto (fun n => ∫ x, q n j k x ∂P) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (D n)) atTop (nhds 0) := by
      simpa using hD.sqrt
    have hupper : Tendsto (fun n => D n + 2 * Real.sqrt (D n) * Real.sqrt B0)
        atTop (nhds 0) := by
      simpa only [zero_add, zero_mul, mul_zero, add_zero, mul_assoc, mul_comm] using
        hD.add ((hsqrt.const_mul 2).mul_const (Real.sqrt B0))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun n => integral_nonneg fun x => abs_nonneg _)
      (Eventually.of_forall fun n => hq_bound n j k)
  let R : Fin d → Fin d → ∀ n, (Fin n → Ω) → ℝ := fun j k n X =>
    (n : ℝ)⁻¹ * ∑ i, q n j k (X i)
  have hR (j k : Fin d) : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (R j k) := by
    intro epsilon hepsilon
    rw [Metric.tendsto_atTop]
    intro eta heta
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hq_zero j k) (epsilon * eta)
      (mul_pos hepsilon heta)
    refine ⟨N, fun n hn => ?_⟩
    have hq_meas : Measurable (q n j k) := by
      have hbn : Measurable (fun x => base' n x j * base' n x k) :=
        (((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (hbase'_meas n)).mul
        ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (hbase'_meas n)))
      have hb0 : Measurable (fun x => base0' x j * base0' x k) :=
        (((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hbase0'_meas).mul
        ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hbase0'_meas))
      exact (hbn.sub hb0).abs
    have hsum_int : Integrable (R j k n) (Measure.pi (fun _ : Fin n => P)) := by
      apply Integrable.const_mul
      rw [show (fun X => ∑ i, q n j k (X i)) =
          ∑ i, q n j k ∘ Function.eval i by
        ext X
        simp [Function.comp_apply]]
      exact integrable_finset_sum' Finset.univ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
          (hq_int n j k))
    have hsum_nonneg : 0 ≤ᵐ[Measure.pi (fun _ : Fin n => P)] R j k n :=
      Eventually.of_forall fun X => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
        (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hsum_nonneg hsum_int epsilon
    have hmean : ∫ X, R j k n X ∂(Measure.pi (fun _ : Fin n => P)) <=
        ∫ x, q n j k x ∂P := by
      have heval (i : Fin n) :
          ∫ X, q n j k (X i) ∂(Measure.pi (fun _ : Fin n => P)) =
            ∫ x, q n j k x ∂P := by
        rw [MeasureTheory.integral_comp_eval hq_meas.aestronglyMeasurable]
      rw [integral_const_mul]
      have hsum_eq : (∫ X, ∑ i, q n j k (X i) ∂(Measure.pi (fun _ : Fin n => P))) =
          ∑ i, ∫ X, q n j k (X i) ∂(Measure.pi (fun _ : Fin n => P)) := by
        simpa only [Finset.sum_apply, Function.comp_apply] using integral_finset_sum
          (μ := Measure.pi (fun _ : Fin n => P)) (Finset.univ : Finset (Fin n))
          (fun i _ => (measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp_of_integrable
            (hq_int n j k))
      rw [hsum_eq]
      simp_rw [heval]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hc : (n : ℝ)⁻¹ * (n : ℝ) <= 1 := by
        simpa [mul_comm] using
          (card_subtype_mul_inv_mem_Icc n (fun _ : Fin n => True)).2
      calc
        (n : ℝ)⁻¹ * ((n : ℝ) * ∫ x, q n j k x ∂P) =
            ((n : ℝ)⁻¹ * (n : ℝ)) * ∫ x, q n j k x ∂P := by ring
        _ <= ∫ x, q n j k x ∂P :=
          mul_le_of_le_one_left (integral_nonneg fun x => abs_nonneg _) hc
    have hqsmall : ∫ x, q n j k x ∂P < epsilon * eta := by
      have := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)] at this
      exact this
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hreal : (Measure.pi (fun _ : Fin n => P)).real
        {X | epsilon <= R j k n X} < eta := by
      apply (lt_of_mul_lt_mul_left (hmarkov.trans_lt (hmean.trans_lt hqsmall)) hepsilon.le)
    convert hreal using 1
    apply measureReal_congr
    apply Filter.Eventually.of_forall
    intro X
    change (epsilon <= ‖R j k n X‖) = (epsilon <= R j k n X)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun i _ => abs_nonneg _))]
  have hreplace_entry (j k : Fin d) : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => (empGram base' n X - empGram (fun _ => base0') n X) j k) := by
    apply TendstoInProbZero.mono_norm (hR j k)
    intro n X
    simp only [empGram, Matrix.sub_apply, R, Real.norm_eq_abs]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    calc
      |(n : ℝ)⁻¹ * ∑ i, (base' n (X i) j * base' n (X i) k -
          base0' (X i) j * base0' (X i) k)| =
          (n : ℝ)⁻¹ * |∑ i, (base' n (X i) j * base' n (X i) k -
            base0' (X i) j * base0' (X i) k)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
      _ <= (n : ℝ)⁻¹ * ∑ i, q n j k (X i) := by
        gcongr
        simpa only [q] using Finset.abs_sum_le_sum_abs
          (fun i : Fin n => base' n (X i) j * base' n (X i) k -
            base0' (X i) j * base0' (X i) k) (Finset.univ : Finset (Fin n))
      _ = |(n : ℝ)⁻¹ * ∑ i, q n j k (X i)| := by
        rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
          (Finset.sum_nonneg fun i _ => abs_nonneg _))]
  have hfixed_entry (j k : Fin d) : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => (empGram (fun _ => base0') n X - populationGram P base0') j k) := by
    let f0 : Ω → ℝ := fun x => base0' x j * base0' x k
    have hf0 : Integrable f0 P := by
      have hj : MemLp (fun x => base0' x j) 2 P := by
        simpa using (hbase0'_memLp.continuousLinearMap_comp
          (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
      have hk : MemLp (fun x => base0' x k) 2 P := by
        simpa using (hbase0'_memLp.continuousLinearMap_comp
          (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) k :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
      exact hj.integrable_mul hk
    intro epsilon hepsilon
    have h := iid_lln_in_prob_l1 f0 hf0 epsilon hepsilon
    have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
    simpa only [empGram, populationGram, Matrix.sub_apply, Real.norm_eq_abs,
      measureReal_def, f0] using! ht
  have hemp_rep : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => empGram base' n X - populationGram P base0') := by
    apply TendstoInProbZero.matrix_of_entry
    intro j k
    have h := TendstoInProbZero.add (hreplace_entry j k) (hfixed_entry j k)
    convert h using 1
    funext n X
    simp only [Matrix.sub_apply]
    ring
  have hemp : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P))
      (fun n X => empGram base n X - populationGram P base0) := by
    intro epsilon hepsilon
    convert hemp_rep epsilon hepsilon using 1
    funext n
    apply measureReal_congr
    have hpi : (fun (X : Fin n → Ω) i => base n (X i)) =ᵐ[
        Measure.pi (fun _ : Fin n => P)] fun X i => base' n (X i) :=
      MeasureTheory.Measure.ae_eq_pi (fun _ => hbase_ae n)
    filter_upwards [hpi] with X hX
    have he : empGram base n X = empGram base' n X := by
      ext j k
      unfold empGram
      apply congrArg ((n : ℝ)⁻¹ * ·)
      apply Finset.sum_congr rfl
      intro i _
      rw [congrFun hX i]
    have hp : populationGram P base0 = populationGram P base0' := by
      ext j k
      unfold populationGram
      apply integral_congr_ae
      filter_upwards [hbase0_ae] with x hx
      rw [hx]
    change (epsilon <= ‖empGram base n X - populationGram P base0‖) =
      (epsilon <= ‖empGram base' n X - populationGram P base0'‖)
    rw [he, hp]
  have hsum := TendstoInProbZero.add hsplit hemp
  convert hsum using 1
  funext n X
  abel

private theorem rootNGrid_code_mem_Icc {k n : ℕ} (hn : 0 < n)
    (theta0 theta : EuclideanSpace ℝ (Fin k)) (M : ℝ)
    (z : Fin k → ℤ) (hz : ∀ j, theta j = (z j : ℝ) / Real.sqrt n)
    (hlocal : Real.sqrt n * ‖theta - theta0‖ ≤ M) (j : Fin k) :
    z j - Int.floor (Real.sqrt n * theta0 j) ∈
      Finset.Icc (-Int.ceil (M + 1)) (Int.ceil (M + 1)) := by
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hscale : Real.sqrt n * theta j = (z j : ℝ) := by rw [hz j]; field_simp
  have hcoord : ‖(theta - theta0) j‖ ≤ ‖theta - theta0‖ := PiLp.norm_apply_le _ _
  simp only [PiLp.sub_apply, Real.norm_eq_abs] at hcoord
  have hzclose : |(z j : ℝ) - Real.sqrt n * theta0 j| ≤ M := by
    calc
      |(z j : ℝ) - Real.sqrt n * theta0 j| = Real.sqrt n * |theta j - theta0 j| := by
        rw [← hscale, ← mul_sub, abs_mul, abs_of_pos hsqrt]
      _ ≤ Real.sqrt n * ‖theta - theta0‖ := mul_le_mul_of_nonneg_left hcoord hsqrt.le
      _ ≤ M := hlocal
  have hceil : M + 1 ≤ ((Int.ceil (M + 1) : ℤ) : ℝ) := Int.le_ceil _
  simp only [Finset.mem_Icc]
  constructor
  · exact_mod_cast (show -((Int.ceil (M + 1) : ℤ) : ℝ) ≤
        (z j : ℝ) - ((Int.floor (Real.sqrt n * theta0 j) : ℤ) : ℝ) by
      rcases abs_le.mp hzclose with ⟨hzlo, _⟩
      linarith [Int.floor_le (Real.sqrt n * theta0 j)])
  · exact_mod_cast (show
        (z j : ℝ) - ((Int.floor (Real.sqrt n * theta0 j) : ℤ) : ℝ) ≤
          ((Int.ceil (M + 1) : ℤ) : ℝ) by
      rcases abs_le.mp hzclose with ⟨_, hzhi⟩
      linarith [Int.sub_one_lt_floor (Real.sqrt n * theta0 j)])

/-- A deterministic-sequence `o_P(1)` statement on every root-n-bounded path
extends to evaluation at a root-n-bounded random preliminary point lying on the
exact coordinate grid.  Both the sample spaces and their probability measures may
vary with `n`; no measurability beyond that already encoded in the two probabilistic
premises is required. -/
theorem rootNGrid_tendstoInProbZero_at_random
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    {k : ℕ} {G : Type*} [NormedAddCommGroup G]
    (P : ∀ n, Measure (Ξ n)) [∀ n, IsProbabilityMeasure (P n)]
    (R : ∀ n, Ξ n → EuclideanSpace ℝ (Fin k) → G)
    (preliminary : ∀ n, Ξ n → EuclideanSpace ℝ (Fin k))
    (theta0 : EuclideanSpace ℝ (Fin k))
    -- deterministic root-n-bounded paths have negligible residual.
    (h_det : ∀ thetaSeq : ℕ → EuclideanSpace ℝ (Fin k),
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        Real.sqrt n * ‖thetaSeq n - theta0‖ ≤ C) →
      TendstoInProbZero P (fun n ξ => R n ξ (thetaSeq n)))
    -- the random preliminary point is root-n bounded in probability.
    (h_preliminary : IsBoundedInProb P
      (fun n ξ => Real.sqrt n • (preliminary n ξ - theta0)))
    -- the preliminary point lies on the exact coordinatewise root-n grid.
    (h_grid : ∀ n, 0 < n → ∀ ξ, ∃ z : Fin k → ℤ, ∀ j,
      preliminary n ξ j = (z j : ℝ) / Real.sqrt n) :
    TendstoInProbZero P (fun n ξ => R n ξ (preliminary n ξ)) := by
  classical
  intro ε hε
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨M0, hM0⟩ := h_preliminary (η / 2) (by positivity)
  let M := max M0 0
  let A : ℤ := Int.ceil (M + 1)
  let codes := (Finset.univ : Finset (Fin k)).pi (fun _ => Finset.Icc (-A) A)
  let point : ℕ → (∀ j, j ∈ (Finset.univ : Finset (Fin k)) → ℤ) →
      EuclideanSpace ℝ (Fin k) := fun n z =>
    if n = 0 then theta0 else (WithLp.equiv 2 (Fin k → ℝ)).symm (fun j =>
      (((Int.floor (Real.sqrt n * theta0 j) : ℤ) + z j (Finset.mem_univ j) : ℤ) : ℝ) /
        Real.sqrt n)
  have hpoint_bdd (z : ∀ j, j ∈ (Finset.univ : Finset (Fin k)) → ℤ) :
      ∃ B : ℝ, ∀ᶠ n : ℕ in atTop, Real.sqrt n * ‖point n z - theta0‖ ≤ B := by
    let offset : EuclideanSpace ℝ (Fin k) := (WithLp.equiv 2 (Fin k → ℝ)).symm
      (fun j => (z j (Finset.mem_univ j) : ℝ))
    refine ⟨Real.sqrt k + ‖offset‖, eventually_atTop.2 ⟨1, fun n hn => ?_⟩⟩
    have hnpos : 0 < n := Nat.zero_lt_of_lt hn
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
    let rounded : EuclideanSpace ℝ (Fin k) := (WithLp.equiv 2 (Fin k → ℝ)).symm
      (fun j => ((Int.floor (Real.sqrt n * theta0 j) : ℤ) : ℝ) / Real.sqrt n)
    have hround : ‖rounded - theta0‖ ≤ Real.sqrt k / Real.sqrt n := by
      rw [← sq_le_sq₀ (norm_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hsqrt.le),
        EuclideanSpace.real_norm_sq_eq, div_pow, Real.sq_sqrt (by positivity)]
      calc
        ∑ j, (rounded - theta0) j ^ 2 ≤ ∑ _j : Fin k, (1 / Real.sqrt n) ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          change (((Int.floor (Real.sqrt n * theta0 j) : ℤ) : ℝ) / Real.sqrt n -
            theta0 j) ^ 2 ≤ (1 / Real.sqrt n) ^ 2
          rw [← sq_abs]
          apply pow_le_pow_left₀ (abs_nonneg _) _ 2
          rw [show ((Int.floor (Real.sqrt n * theta0 j) : ℤ) : ℝ) / Real.sqrt n -
              theta0 j = (((Int.floor (Real.sqrt n * theta0 j) : ℤ) : ℝ) -
                Real.sqrt n * theta0 j) / Real.sqrt n by field_simp, abs_div,
            abs_of_pos hsqrt]
          exact (div_le_div_iff_of_pos_right hsqrt).2 (by
            rw [abs_le]
            constructor
            · linarith [Int.sub_one_lt_floor (Real.sqrt n * theta0 j)]
            · linarith [Int.floor_le (Real.sqrt n * theta0 j)])
        _ = (k : ℝ) / Real.sqrt n ^ 2 := by simp [div_eq_mul_inv]
    have hp : point n z = rounded + (1 / Real.sqrt n) • offset := by
      ext j
      simp only [point, if_neg hnpos.ne', rounded, offset, PiLp.add_apply, PiLp.smul_apply]
      change (((((Int.floor (Real.sqrt n * theta0 j) : ℤ) +
        z j (Finset.mem_univ j) : ℤ) : ℝ) / Real.sqrt n)) =
          ((Int.floor (Real.sqrt n * theta0 j) : ℤ) : ℝ) / Real.sqrt n +
            (1 / Real.sqrt n) * (z j (Finset.mem_univ j) : ℝ)
      rw [Int.cast_add]
      ring
    rw [hp]
    calc
      Real.sqrt n * ‖rounded + (1 / Real.sqrt n) • offset - theta0‖
          ≤ Real.sqrt n * (‖rounded - theta0‖ + ‖(1 / Real.sqrt n) • offset‖) := by
            gcongr
            rw [show rounded + (1 / Real.sqrt n) • offset - theta0 =
              (rounded - theta0) + (1 / Real.sqrt n) • offset by abel]
            exact norm_add_le _ _
      _ ≤ Real.sqrt n * (Real.sqrt k / Real.sqrt n +
          (1 / Real.sqrt n) * ‖offset‖) := by
            gcongr
            simp [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt]
      _ = Real.sqrt k + ‖offset‖ := by field_simp
  have hcode (z : ∀ j, j ∈ (Finset.univ : Finset (Fin k)) → ℤ) :
      TendstoInProbZero P (fun n ξ => R n ξ (point n z)) :=
    h_det (fun n => point n z) (hpoint_bdd z)
  have hsum : Tendsto (fun n => ∑ z ∈ codes,
      (P n).real {ξ | ε ≤ ‖R n ξ (point n z)‖}) atTop (nhds 0) := by
    simpa using tendsto_finset_sum codes (fun z _ => hcode z ε hε)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hsum (η / 2) (by positivity)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le ((le_max_right N 1).trans hn)
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hnpos)
  have hcover : {ξ | ε ≤ ‖R n ξ (preliminary n ξ)‖} ⊆
      {ξ | M < ‖Real.sqrt n • (preliminary n ξ - theta0)‖} ∪
        ⋃ z ∈ codes, {ξ | ε ≤ ‖R n ξ (point n z)‖} := by
    intro ξ hξ
    by_cases hout : M < ‖Real.sqrt n • (preliminary n ξ - theta0)‖
    · exact Or.inl hout
    · right
      obtain ⟨w, hw⟩ := h_grid n hnpos ξ
      let z : ∀ j, j ∈ (Finset.univ : Finset (Fin k)) → ℤ := fun j _ =>
        w j - Int.floor (Real.sqrt n * theta0 j)
      have hz : z ∈ codes := by
        rw [Finset.mem_pi]
        intro j _
        have hlocal : Real.sqrt n * ‖preliminary n ξ - theta0‖ ≤ M := by
          simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hsqrt] using not_lt.mp hout
        simpa only [z, A] using rootNGrid_code_mem_Icc hnpos theta0 (preliminary n ξ)
          M w hw hlocal j
      have hp : point n z = preliminary n ξ := by
        ext j
        simp only [point, if_neg hnpos.ne', z]
        change ((((Int.floor (Real.sqrt n * theta0 j) : ℤ) +
          (w j - Int.floor (Real.sqrt n * theta0 j)) : ℤ) : ℝ) / Real.sqrt n) =
            preliminary n ξ j
        rw [hw j]
        congr 1
        push_cast
        ring
      change ε ≤ ‖R n ξ (preliminary n ξ)‖ at hξ
      rw [← hp] at hξ
      exact Set.mem_iUnion_of_mem z (Set.mem_iUnion_of_mem hz hξ)
  have hescape : (P n).real {ξ | M < ‖Real.sqrt n • (preliminary n ξ - theta0)‖} ≤
      η / 2 := (measureReal_mono (fun ξ hξ => lt_of_le_of_lt (le_max_left M0 0) hξ)).trans
        (hM0 n)
  have hunion := measureReal_biUnion_finset_le (μ := P n) codes
    (fun z => {ξ | ε ≤ ‖R n ξ (point n z)‖})
  have hsmall : ∑ z ∈ codes, (P n).real {ξ | ε ≤ ‖R n ξ (point n z)‖} < η / 2 := by
    have := hN n hnN
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => measureReal_nonneg)] at this
  have hfinal : (P n).real {ξ | ε ≤ ‖R n ξ (preliminary n ξ)‖} < η := calc
    (P n).real {ξ | ε ≤ ‖R n ξ (preliminary n ξ)‖}
        ≤ (P n).real {ξ | M < ‖Real.sqrt n • (preliminary n ξ - theta0)‖} +
          (P n).real (⋃ z ∈ codes, {ξ | ε ≤ ‖R n ξ (point n z)‖}) :=
      (measureReal_mono hcover).trans (measureReal_union_le _ _)
    _ ≤ η / 2 + ∑ z ∈ codes, (P n).real {ξ | ε ≤ ‖R n ξ (point n z)‖} :=
      add_le_add hescape hunion
    _ < η := by linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg] using hfinal

/-! Weighted-density and triangular-row lemmas. -/

private theorem memLp_sqrt_density_smul
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace Real E] [BorelSpace E]
    [SecondCountableTopology E]
    (mu Q : Measure Omega) (q : Omega -> Real)
    (hq_meas : Measurable q) (hq_nonneg : forall x, 0 <= q x)
    (hQ : Q = mu.withDensity (fun x => ENNReal.ofReal (q x)))
    (f : Omega -> E) (hf_meas : Measurable f) (hf : MemLp f 2 Q) :
    MemLp (fun x => Real.sqrt (q x) • f x) 2 mu := by
  have hweighted_meas : AEStronglyMeasurable
      (fun x => Real.sqrt (q x) • f x) mu :=
    hq_meas.sqrt.aestronglyMeasurable.smul hf_meas.aestronglyMeasurable
  have hi' : Integrable
      (fun x => ‖f x‖ ^ 2 * (ENNReal.ofReal (q x)).toReal) mu := by
    rw [← MeasureTheory.integrable_withDensity_iff hq_meas.ennreal_ofReal (by simp), ← hQ]
    convert (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf using 1
  have hi : Integrable (fun x => ‖f x‖ ^ 2 * q x) mu := by
    convert hi' using 1
    funext x
    rw [ENNReal.toReal_ofReal (hq_nonneg x)]
  rw [memLp_two_iff_integrable_sq_norm hweighted_meas]
  convert hi using 1
  funext x
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (hq_nonneg x)]
  ring

private theorem integral_tail_of_L1_anchor
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (z0 : Omega -> Real) (z : Nat -> Omega -> Real)
    (hz0_meas : Measurable z0) (hz_meas : forall n, Measurable (z n))
    (hz0_int : Integrable z0 mu) (hz_int : forall n, Integrable (z n) mu)
    (hz0_nonneg : forall x, 0 <= z0 x) (hz_nonneg : forall n x, 0 <= z n x)
    (hL1 : Tendsto (fun n => ∫ x, |z n x - z0 x| ∂mu) atTop (nhds 0))
    (A : Nat -> Real) (hA_nonneg : forall n, 0 <= A n) (hA : Tendsto A atTop atTop) :
    Tendsto (fun n => ∫ x in {x | A n < z n x}, z n x ∂mu) atTop (nhds 0) := by
  have hAhalf : Tendsto (fun n => A n / 2) atTop atTop :=
    hA.atTop_div_const (by positivity)
  have htail0 : Tendsto
      (fun n => ∫ x in {x | A n / 2 < z0 x}, z0 x ∂mu) atTop (nhds 0) := by
    have hpoint (x : Omega) : Tendsto
        (fun n => {x | A n / 2 < z0 x}.indicator z0 x) atTop (nhds 0) := by
      have heq : (fun _ : Nat => (0 : Real)) =ᶠ[atTop]
          (fun n => {x | A n / 2 < z0 x}.indicator z0 x) := by
        filter_upwards [hAhalf.eventually (eventually_gt_atTop (z0 x))] with n hn
        symm
        rw [Set.indicator_of_notMem]
        exact not_lt.mpr hn.le
      exact Filter.Tendsto.congr' heq tendsto_const_nhds
    have hdom := tendsto_integral_filter_of_dominated_convergence z0
      (Eventually.of_forall fun n => by
        change AEStronglyMeasurable ({x | A n / 2 < z0 x}.indicator z0) mu
        exact (hz0_meas.indicator (measurableSet_lt measurable_const hz0_meas))
          |>.aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun x => by
        change ‖{x | A n / 2 < z0 x}.indicator z0 x‖ <= z0 x
        by_cases hx : x ∈ {x | A n / 2 < z0 x}
        · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (hz0_nonneg x)]
        · rw [Set.indicator_of_notMem hx, norm_zero]
          exact hz0_nonneg x)
      hz0_int (Eventually.of_forall hpoint)
    simpa only [integral_indicator (measurableSet_lt measurable_const hz0_meas),
      integral_zero] using hdom
  have hupper : Tendsto
      (fun n => 2 * (∫ x, |z n x - z0 x| ∂mu) +
        2 * ∫ x in {x | A n / 2 < z0 x}, z0 x ∂mu) atTop (nhds 0) := by
    simpa using (hL1.const_mul 2).add (htail0.const_mul 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => setIntegral_nonneg
      (measurableSet_lt measurable_const (hz_meas n)) fun _ _ => hz_nonneg n _) ?_
  exact Eventually.of_forall fun n => by
    let high : Set Omega := {x | A n < z n x}
    have hhigh : MeasurableSet high := measurableSet_lt measurable_const (hz_meas n)
    rw [← integral_indicator hhigh]
    calc
      (∫ x, high.indicator (z n) x ∂mu) <=
          ∫ x, 2 * |z n x - z0 x| +
            2 * ({x | A n / 2 < z0 x}.indicator z0) x ∂mu := by
        refine integral_mono ((hz_int n).indicator hhigh)
          (((hz_int n).sub hz0_int).norm.const_mul 2 |>.add
            ((hz0_int.indicator (measurableSet_lt measurable_const hz0_meas)).const_mul 2)) ?_
        intro x
        by_cases hx : x ∈ high
        · rw [Set.indicator_of_mem hx]
          simp only [Set.indicator]
          split_ifs with hsmall
          · calc
              z n x = (z n x - z0 x) + z0 x := by ring
              _ <= |z n x - z0 x| + z0 x :=
                add_le_add (le_abs_self _) le_rfl
              _ <= 2 * |z n x - z0 x| + 2 * z0 x := by
                nlinarith [abs_nonneg (z n x - z0 x), hz0_nonneg x]
          · change ¬ A n / 2 < z0 x at hsmall
            have hz0small : z0 x <= A n / 2 := le_of_not_gt hsmall
            have hlarge : A n < z n x := hx
            have hdiffpos : 0 < z n x - z0 x := by
              nlinarith [hA_nonneg n]
            rw [abs_of_pos hdiffpos]
            linarith
        · rw [Set.indicator_of_notMem hx]
          exact add_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
            (mul_nonneg (by positivity) (Set.indicator_apply_nonneg fun _ => hz0_nonneg _))
      _ = 2 * (∫ x, |z n x - z0 x| ∂mu) +
            2 * ∫ x in {x | A n / 2 < z0 x}, z0 x ∂mu := by
        have h1 : Integrable (fun x => 2 * |z n x - z0 x|) mu :=
          ((hz_int n).sub hz0_int).norm.const_mul 2
        have h2 : Integrable
            (fun x => 2 * ({x | A n / 2 < z0 x}.indicator z0) x) mu :=
          (hz0_int.indicator (measurableSet_lt measurable_const hz0_meas)).const_mul 2
        rw [integral_add h1 h2, integral_const_mul, integral_const_mul,
          integral_indicator (measurableSet_lt measurable_const hz0_meas)]

/-- Triangular-row WLLN from a uniform first-moment bound and sqrt-n tail UI. -/
theorem triangular_empirical_mean_of_sqrt_tail
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Nat -> Measure Omega) [forall n, IsProbabilityMeasure (P n)]
    (Y : Nat -> Omega -> Real)
    (hY_meas : forall n, Measurable (Y n))
    (hY_int : forall n, Integrable (Y n) (P n))
    (C : Real) (hC : 0 <= C)
    (hfirst : ∀ᶠ n in atTop, ∫ x, |Y n x| ∂(P n) <= C)
    (htail : Tendsto
      (fun n => ∫ x in {x | Real.sqrt n < |Y n x|}, |Y n x| ∂(P n))
      atTop (nhds 0)) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => (n : Real)⁻¹ * ∑ i, Y n (X i) - ∫ x, Y n x ∂(P n)) := by
  classical
  let B : Nat -> Set Omega := fun n => {x | Real.sqrt n < |Y n x|}
  let T : Nat -> Omega -> Real := fun n x => if x ∈ B n then 0 else Y n x
  have hB_meas (n : Nat) : MeasurableSet (B n) :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hY_meas n))
  have hT_meas (n : Nat) : Measurable (T n) := by
    exact Measurable.piecewise (hB_meas n) measurable_const (hY_meas n)
  have hT_bound (n : Nat) : forall x, |T n x| <= Real.sqrt n := by
    intro x
    simp only [T]
    split_ifs with hx
    · simp [Real.sqrt_nonneg]
    · exact le_of_not_gt hx
  have hT_memLp (n : Nat) : MemLp (T n) 2 (P n) := by
    refine MemLp.of_bound (hT_meas n).aestronglyMeasurable (Real.sqrt n) ?_
    exact Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hT_bound n x
  have hT_int (n : Nat) : Integrable (T n) (P n) := (hT_memLp n).integrable one_le_two
  have hdiff_int (n : Nat) : Integrable (fun x => Y n x - T n x) (P n) :=
    (hY_int n).sub (hT_int n)
  have hdiff_abs (n : Nat) :
      (fun x => |Y n x - T n x|) = (B n).indicator (fun x => |Y n x|) := by
    funext x
    by_cases hx : x ∈ B n <;> simp [T, hx]
  have hdiff_mean (n : Nat) :
      (∫ x, |Y n x - T n x| ∂(P n)) =
        ∫ x in B n, |Y n x| ∂(P n) := by
    rw [hdiff_abs n, integral_indicator (hB_meas n)]
  have hrem : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => (n : Real)⁻¹ * ∑ i, (Y n (X i) - T n (X i))) := by
    intro epsilon hepsilon
    rw [Metric.tendsto_atTop]
    intro eta heta
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail (epsilon * eta)
      (mul_pos hepsilon heta)
    refine ⟨N, fun n hn => ?_⟩
    let R : (Fin n -> Omega) -> Real := fun X =>
      (n : Real)⁻¹ * ∑ i, |Y n (X i) - T n (X i)|
    have hR_int : Integrable R (Measure.pi (fun _ : Fin n => P n)) := by
      apply Integrable.const_mul
      rw [show (fun X => ∑ i, |Y n (X i) - T n (X i)|) =
          ∑ i, (fun x => |Y n x - T n x|) ∘ Function.eval i by
        ext X
        simp [Function.comp_apply]]
      exact integrable_finset_sum' Finset.univ (fun i _ =>
        (measurePreserving_eval (fun _ : Fin n => P n) i).integrable_comp_of_integrable
          (hdiff_int n).norm)
    have hR_nonneg : 0 ≤ᵐ[Measure.pi (fun _ : Fin n => P n)] R :=
      Eventually.of_forall fun X => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
        (Finset.sum_nonneg fun i _ => abs_nonneg _)
    have hmarkov := mul_meas_ge_le_integral_of_nonneg hR_nonneg hR_int epsilon
    have hR_mean : ∫ X, R X ∂(Measure.pi (fun _ : Fin n => P n)) <=
        ∫ x in B n, |Y n x| ∂(P n) := by
      rw [integral_const_mul]
      have hsum : (∫ X, ∑ i, |Y n (X i) - T n (X i)|
          ∂(Measure.pi (fun _ : Fin n => P n))) =
          ∑ i, ∫ X, |Y n (X i) - T n (X i)|
            ∂(Measure.pi (fun _ : Fin n => P n)) := by
        simpa only [Finset.sum_apply] using! integral_finset_sum
          (μ := Measure.pi (fun _ : Fin n => P n)) (Finset.univ : Finset (Fin n))
          (fun i _ =>
            (measurePreserving_eval (fun _ : Fin n => P n) i).integrable_comp_of_integrable
              (hdiff_int n).norm)
      rw [hsum]
      have heval (i : Fin n) :
          (∫ X, |Y n (X i) - T n (X i)| ∂(Measure.pi (fun _ : Fin n => P n))) =
            ∫ x, |Y n x - T n x| ∂(P n) := by
        change (∫ X, ((fun x => |Y n x - T n x|) ∘ Function.eval i) X
          ∂(Measure.pi (fun _ : Fin n => P n))) = _
        simpa only [Function.comp_apply] using!
          (MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => P n) (i := i)
            (hdiff_int n).norm.aestronglyMeasurable)
      simp_rw [heval]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        hdiff_mean n]
      have hc : (n : Real)⁻¹ * (n : Real) <= 1 := by
        simpa [mul_comm] using
          (card_subtype_mul_inv_mem_Icc n (fun _ : Fin n => True)).2
      rw [← mul_assoc]
      exact mul_le_of_le_one_left
        (setIntegral_nonneg (hB_meas n) fun _ _ => abs_nonneg _) hc
    have hsmall : ∫ x in B n, |Y n x| ∂(P n) < epsilon * eta := by
      simpa only [B, Real.dist_eq, sub_zero,
        abs_of_nonneg (setIntegral_nonneg (hB_meas n) fun _ _ => abs_nonneg _)]
        using hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hreal : (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon <= R X} < eta := by
      apply (lt_of_mul_lt_mul_left (hmarkov.trans_lt (hR_mean.trans_lt hsmall)) hepsilon.le)
    refine (measureReal_mono ?_).trans_lt hreal
    intro X hX
    change epsilon <= |(n : Real)⁻¹ * ∑ i, (Y n (X i) - T n (X i))| at hX
    change epsilon <= R X
    calc
      epsilon <= |(n : Real)⁻¹ * ∑ i, (Y n (X i) - T n (X i))| := hX
      _ <= (n : Real)⁻¹ * ∑ i, |Y n (X i) - T n (X i)| := by
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))]
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
  have hsqrt_inv : Tendsto (fun n : Nat => Real.sqrt n * (n : Real)⁻¹)
      atTop (nhds 0) := by
    have h : Tendsto (fun n : Nat => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hs : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
    have hn0 : (n : Real) ≠ 0 := ne_of_gt hnR
    field_simp [hs, hn0]
    exact (Real.sq_sqrt hnR.le).symm
  have hvar_bound : Tendsto (fun n : Nat => Real.sqrt n * (n : Real)⁻¹ * C)
      atTop (nhds 0) := by
    have h := Filter.Tendsto.mul_const C hsqrt_inv
    simpa only [zero_mul] using h
  have hcenter : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => (n : Real)⁻¹ * ∑ i, T n (X i) - ∫ x, T n x ∂(P n)) := by
    intro epsilon hepsilon
    rw [Metric.tendsto_atTop]
    intro eta heta
    obtain ⟨N1, hN1⟩ := eventually_atTop.mp hfirst
    obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hvar_bound (epsilon ^ 2 * eta)
      (mul_pos (sq_pos_of_pos hepsilon) heta)
    refine ⟨max (max N1 N2) 1, fun n hn => ?_⟩
    have hn1 : 1 <= n := (le_max_right (max N1 N2) 1).trans hn
    have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn1
    have hnN1 : N1 <= n := (le_max_left N1 N2).trans (le_max_left (max N1 N2) 1) |>.trans hn
    have hnN2 : N2 <= n := (le_max_right N1 N2).trans (le_max_left (max N1 N2) 1) |>.trans hn
    let centered : Fin n -> Omega -> Real := fun _ x => T n x - ∫ y, T n y ∂(P n)
    let S : (Fin n -> Omega) -> Real := fun X =>
      (n : Real)⁻¹ * ∑ i, centered i (X i)
    have hcL2 : forall i, MemLp (centered i) 2 (P n) := fun _ =>
      (hT_memLp n).sub (memLp_const (∫ y, T n y ∂(P n)))
    have hSL2 : MemLp S 2 (Measure.pi (fun _ : Fin n => P n)) := by
      apply MemLp.const_mul
      rw [show (fun X => ∑ i, centered i (X i)) =
          ∑ i, centered i ∘ Function.eval i by
        ext X
        simp [Function.comp_apply]]
      exact memLp_finset_sum' Finset.univ (fun i _ =>
        (hcL2 i).comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P n) i))
    have hmean : ∫ X, S X ∂(Measure.pi (fun _ : Fin n => P n)) = 0 := by
      rw [integral_const_mul]
      have heval (i : Fin n) :
          ∫ X, centered i (X i) ∂(Measure.pi (fun _ : Fin n => P n)) = 0 := by
        rw [MeasureTheory.integral_comp_eval (μ := fun _ : Fin n => P n) (i := i)
          (hcL2 i).aestronglyMeasurable]
        simp [centered, integral_sub (hT_int n)
          (integrable_const (∫ y, T n y ∂(P n)))]
      have hint : forall i, Integrable (fun X : Fin n -> Omega => centered i (X i))
          (Measure.pi (fun _ : Fin n => P n)) := fun i =>
        ((hcL2 i).comp_measurePreserving
          (measurePreserving_eval (fun _ : Fin n => P n) i)).integrable one_le_two
      rw [integral_finset_sum _ (fun i _ => hint i)]
      simp only [heval, Finset.sum_const_zero, mul_zero]
    have hvar : ProbabilityTheory.variance S (Measure.pi (fun _ : Fin n => P n)) <=
        Real.sqrt n * (n : Real)⁻¹ * C := by
      rw [ProbabilityTheory.variance_const_mul]
      have hvsum : ProbabilityTheory.variance
          (fun X : Fin n -> Omega => ∑ i, centered i (X i))
            (Measure.pi (fun _ : Fin n => P n)) =
          ∑ i, ProbabilityTheory.variance (centered i) (P n) := by
        have hfun : (fun X : Fin n -> Omega => ∑ i, centered i (X i)) =
            ∑ i, fun X : Fin n -> Omega => centered i (X i) := by
          funext X
          simp only [Finset.sum_apply]
        rw [hfun]
        exact ProbabilityTheory.variance_sum_pi hcL2
      rw [hvsum]
      have hvar_each (i : Fin n) :
          ProbabilityTheory.variance (centered i) (P n) <=
            ∫ x, (T n x) ^ 2 ∂(P n) := by
        rw [show centered i = fun x => T n x - ∫ y, T n y ∂(P n) by rfl,
          ProbabilityTheory.variance_sub_const (hT_memLp n).aestronglyMeasurable]
        exact ProbabilityTheory.variance_le_expectation_sq (hT_memLp n).aestronglyMeasurable
      have hsquare : ∫ x, (T n x) ^ 2 ∂(P n) <=
          Real.sqrt n * ∫ x, |Y n x| ∂(P n) := by
        rw [← integral_const_mul]
        refine integral_mono (hT_memLp n).integrable_sq
          ((hY_int n).norm.const_mul (Real.sqrt n)) ?_
        intro x
        calc
          T n x ^ 2 = |T n x| * |T n x| := by
            rw [← sq_abs, pow_two]
          _ <= Real.sqrt n * |T n x| := by
            gcongr
            exact hT_bound n x
          _ <= Real.sqrt n * |Y n x| := by
            by_cases hx : x ∈ B n
            · simp [T, hx, mul_nonneg, Real.sqrt_nonneg]
            · simp [T, hx]
      calc
        (n : Real)⁻¹ ^ 2 * ∑ i, ProbabilityTheory.variance (centered i) (P n)
            <= (n : Real)⁻¹ ^ 2 * ((n : Real) * ∫ x, (T n x) ^ 2 ∂(P n)) := by
              gcongr
              simpa [nsmul_eq_mul] using Finset.sum_le_sum
                (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hvar_each i)
        _ <= (n : Real)⁻¹ ^ 2 * ((n : Real) *
            (Real.sqrt n * ∫ x, |Y n x| ∂(P n))) := by gcongr
        _ <= (n : Real)⁻¹ ^ 2 * ((n : Real) * (Real.sqrt n * C)) := by
          gcongr
          exact hN1 n hnN1
        _ = Real.sqrt n * (n : Real)⁻¹ * C := by
          field_simp
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hSL2 hepsilon
    simp only [hmean, sub_zero] at hcheb
    have hbound_small : Real.sqrt n * (n : Real)⁻¹ * C < epsilon ^ 2 * eta := by
      have := hN2 n hnN2
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg n))) hC)] at this
    have hreal : (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon <= |S X|} < eta := by
      have hreal_le : (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon <= |S X|} <=
          ProbabilityTheory.variance S (Measure.pi (fun _ : Fin n => P n)) / epsilon ^ 2 := by
        rw [measureReal_def]
        calc
          ((Measure.pi (fun _ : Fin n => P n)) {X | epsilon <= |S X|}).toReal <=
              (ENNReal.ofReal (ProbabilityTheory.variance S
                (Measure.pi (fun _ : Fin n => P n)) / epsilon ^ 2)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
          _ = ProbabilityTheory.variance S
                (Measure.pi (fun _ : Fin n => P n)) / epsilon ^ 2 :=
            ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg _ _)
              (sq_nonneg _))
      exact hreal_le.trans_lt ((div_lt_iff₀ (sq_pos_of_pos hepsilon)).2 (by
        nlinarith [hvar, hbound_small]))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    convert hreal using 1
    apply measureReal_congr
    exact Eventually.of_forall fun X => by
      change (epsilon <= |(n : Real)⁻¹ * ∑ i, T n (X i) - ∫ x, T n x ∂(P n)|) =
        (epsilon <= |S X|)
      congr 2
      simp only [S, centered]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have hnR : (n : Real) ≠ 0 := by exact_mod_cast hnpos.ne'
      field_simp
  have hbias_real : Tendsto
      (fun n => (∫ x, T n x ∂(P n)) - ∫ x, Y n x ∂(P n)) atTop (nhds 0) := by
    have hnorm : Tendsto
        (fun n => |(∫ x, T n x ∂(P n)) - ∫ x, Y n x ∂(P n)|)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
        (Eventually.of_forall fun _ => abs_nonneg _) ?_
      exact Eventually.of_forall fun n => calc
        |(∫ x, T n x ∂(P n)) - ∫ x, Y n x ∂(P n)| =
            |∫ x, T n x - Y n x ∂(P n)| := by rw [integral_sub (hT_int n) (hY_int n)]
        _ <= ∫ x, |T n x - Y n x| ∂(P n) := by
          simpa only [Real.norm_eq_abs] using
            (norm_integral_le_integral_norm (fun x => T n x - Y n x))
        _ = ∫ x in B n, |Y n x| ∂(P n) := by
          rw [show (fun x => |T n x - Y n x|) = fun x => |Y n x - T n x| by
            funext x
            rw [abs_sub_comm], hdiff_mean n]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using hnorm
  have hbias : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n (_ : Fin n -> Omega) =>
        (∫ x, T n x ∂(P n)) - ∫ x, Y n x ∂(P n)) := by
    intro epsilon hepsilon
    have hevent : ∀ᶠ n in atTop,
        |(∫ x, T n x ∂(P n)) - ∫ x, Y n x ∂(P n)| < epsilon := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hbias_real epsilon hepsilon
      exact eventually_atTop.2 ⟨N, fun n hn => by
        simpa only [Real.dist_eq, sub_zero] using hN n hn⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    have hempty : {X : Fin n -> Omega |
        epsilon <= |(∫ x, T n x ∂(P n)) - ∫ x, Y n x ∂(P n)|} = ∅ := by
      ext X
      simp [not_le.mpr hn]
    simp [hempty]
  have hsum : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X =>
        ((n : Real)⁻¹ * ∑ i, (Y n (X i) - T n (X i))) +
          ((n : Real)⁻¹ * ∑ i, T n (X i) - ∫ x, T n x ∂(P n)) +
          ((∫ x, T n x ∂(P n)) - ∫ x, Y n x ∂(P n))) :=
    TendstoInProbZero.add (TendstoInProbZero.add hrem hcenter) hbias
  convert hsum using 1
  funext n X
  rw [Finset.sum_sub_distrib]
  ring

/-- Weighted L2 convergence relative to a common dominating measure identifies the
fixed-law limit of a triangular-array empirical Gram matrix.  The density Hellinger
anchor and the weighted-function anchor replace any fourth-moment or uniform-
integrability assumption; no common-support hypothesis is imposed. -/
theorem empGram_tendstoInProbZero_of_weightedAnchor
    {Omega : Type*} [MeasurableSpace Omega] {d : Nat}
    (mu : Measure Omega)
    (Q0 : Measure Omega) [IsProbabilityMeasure Q0]
    (Qn : Nat -> Measure Omega) [forall n, IsProbabilityMeasure (Qn n)]
    (q0 : Omega -> Real) (qn : Nat -> Omega -> Real)
    -- measurable density representatives are required by `withDensity`
    -- and by the weighted Bochner-integral arguments.
    (hq0_meas : Measurable q0) (hqn_meas : forall n, Measurable (qn n))
    -- the chosen real-valued density representatives are nonnegative.
    (hq0_nonneg : forall x, 0 <= q0 x) (hqn_nonneg : forall n x, 0 <= qn n x)
    -- `q0` and `qn` are densities of the fixed and row laws relative
    -- to the common dominating measure `mu`.
    (hQ0 : Q0 = mu.withDensity (fun x => ENNReal.ofReal (q0 x)))
    (hQn : forall n, Qn n = mu.withDensity (fun x => ENNReal.ofReal (qn n x)))
    (f0 : Omega -> EuclideanSpace Real (Fin d))
    (fn : Nat -> Omega -> EuclideanSpace Real (Fin d))
    -- measurable representatives make the empirical rows and weighted
    -- common-dominator functions measurable.
    (hf0_meas : Measurable f0) (hfn_meas : forall n, Measurable (fn n))
    -- the limiting and row functions are square-integrable under
    -- their own probability laws, ruling out totalized-integral fallback.
    (hf0_memLp : MemLp f0 2 Q0) (hfn_memLp : forall n, MemLp (fn n) 2 (Qn n))
    -- the row densities converge to the fixed density in Hellinger L2.
    (hDensityHell : Tendsto
      (fun n => ∫ x, (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2 ∂mu)
      atTop (nhds 0))
    -- the square-root-density weighted row functions converge in L2(mu).
    (hWeighted : Tendsto
      (fun n => ∫ x,
        norm (Real.sqrt (qn n x) • fn n x - Real.sqrt (q0 x) • f0 x) ^ 2 ∂mu)
      atTop (nhds 0)) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Qn n))
      (fun n X => empGram fn n X - populationGram Q0 f0) := by
  classical
  let g0 : Omega -> EuclideanSpace Real (Fin d) := fun x => Real.sqrt (q0 x) • f0 x
  let g : Nat -> Omega -> EuclideanSpace Real (Fin d) :=
    fun n x => Real.sqrt (qn n x) • fn n x
  let D : Nat -> Real := fun n => ∫ x, ‖g n x - g0 x‖ ^ 2 ∂mu
  let H : Nat -> Real := fun n =>
    ∫ x, (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2 ∂mu
  have hg0_meas : Measurable g0 := hq0_meas.sqrt.smul hf0_meas
  have hg_meas (n : Nat) : Measurable (g n) := (hqn_meas n).sqrt.smul (hfn_meas n)
  have hg0_memLp : MemLp g0 2 mu := by
    simpa only [g0] using memLp_sqrt_density_smul mu Q0 q0 hq0_meas hq0_nonneg hQ0
      f0 hf0_meas hf0_memLp
  have hg_memLp (n : Nat) : MemLp (g n) 2 mu := by
    simpa only [g] using memLp_sqrt_density_smul mu (Qn n) (qn n) (hqn_meas n)
      (hqn_nonneg n) (hQn n) (fn n) (hfn_meas n) (hfn_memLp n)
  have hdiff_memLp (n : Nat) : MemLp (fun x => g n x - g0 x) 2 mu :=
    (hg_memLp n).sub hg0_memLp
  have hD : Tendsto D atTop (nhds 0) := by simpa only [D, g, g0] using hWeighted
  have hD_nonneg (n : Nat) : 0 <= D n := integral_nonneg fun _ => sq_nonneg _
  have hs0_memLp : MemLp (fun x => Real.sqrt (q0 x)) 2 mu := by
    simpa using memLp_sqrt_density_smul mu Q0 q0 hq0_meas hq0_nonneg hQ0
      (fun _ : Omega => (1 : Real)) measurable_const (memLp_const 1)
  have hs_memLp (n : Nat) : MemLp (fun x => Real.sqrt (qn n x)) 2 mu := by
    simpa using memLp_sqrt_density_smul mu (Qn n) (qn n) (hqn_meas n) (hqn_nonneg n)
      (hQn n) (fun _ : Omega => (1 : Real)) measurable_const (memLp_const 1)
  have hsdiff_memLp (n : Nat) :
      MemLp (fun x => Real.sqrt (qn n x) - Real.sqrt (q0 x)) 2 mu :=
    (hs_memLp n).sub hs0_memLp
  have hH : Tendsto H atTop (nhds 0) := by simpa only [H] using hDensityHell
  have hH_nonneg (n : Nat) : 0 <= H n := integral_nonneg fun _ => sq_nonneg _
  have hz0_int : Integrable (fun x => ‖g0 x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm hg0_memLp.aestronglyMeasurable).mp hg0_memLp
  let B0 : Real := ∫ x, ‖g0 x‖ ^ 2 ∂mu
  have hB0_nonneg : 0 <= B0 := integral_nonneg fun _ => sq_nonneg _
  have hz_int (n : Nat) : Integrable (fun x => ‖g n x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (hg_memLp n).aestronglyMeasurable).mp (hg_memLp n)
  have henergy_diff_int (n : Nat) : Integrable
      (fun x => |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2|) mu := ((hz_int n).sub hz0_int).norm
  have hcross (n : Nat) :
      (∫ x, ‖g n x - g0 x‖ * ‖g0 x‖ ∂mu) <=
        Real.sqrt (D n) * Real.sqrt B0 := by
    have hd2 : MemLp (fun x => g n x - g0 x) (ENNReal.ofReal (2 : Real)) mu := by
      norm_num
      exact hdiff_memLp n
    have hb2 : MemLp g0 (ENNReal.ofReal (2 : Real)) mu := by
      norm_num
      exact hg0_memLp
    have hh := integral_mul_norm_le_Lp_mul_Lq (μ := mu) (p := (2 : Real)) (q := (2 : Real))
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hd2 hb2
    have hdint : (∫ x, ‖g n x - g0 x‖ ^ (2 : Real) ∂mu) = D n := by
      rw [show (fun x => ‖g n x - g0 x‖ ^ (2 : Real)) =
          fun x => ‖g n x - g0 x‖ ^ (2 : Nat) by
        funext x
        rw [Real.rpow_two]]
    have hbint : (∫ x, ‖g0 x‖ ^ (2 : Real) ∂mu) = B0 := by
      rw [show (fun x => ‖g0 x‖ ^ (2 : Real)) = fun x => ‖g0 x‖ ^ (2 : Nat) by
        funext x
        rw [Real.rpow_two]]
    rw [hdint, hbint] at hh
    simpa only [one_div, Real.sqrt_eq_rpow] using hh
  have henergy_l1_bound (n : Nat) :
      (∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) <=
        D n + 2 * Real.sqrt (D n) * Real.sqrt B0 := by
    have hd2 : Integrable (fun x => ‖g n x - g0 x‖ ^ 2) mu :=
      (memLp_two_iff_integrable_sq_norm (hdiff_memLp n).aestronglyMeasurable).mp
        (hdiff_memLp n)
    have hcross_int : Integrable (fun x => ‖g n x - g0 x‖ * ‖g0 x‖) mu :=
      (hdiff_memLp n).norm.integrable_mul hg0_memLp.norm
    have hraw : (∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) <=
        D n + 2 * ∫ x, ‖g n x - g0 x‖ * ‖g0 x‖ ∂mu := by
      rw [show D n + 2 * ∫ x, ‖g n x - g0 x‖ * ‖g0 x‖ ∂mu =
          ∫ x, ‖g n x - g0 x‖ ^ 2 +
            2 * (‖g n x - g0 x‖ * ‖g0 x‖) ∂mu by
        rw [integral_add hd2 (hcross_int.const_mul 2), integral_const_mul]
        ]
      refine integral_mono (henergy_diff_int n) (hd2.add (hcross_int.const_mul 2)) ?_
      intro x
      change |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| <=
        ‖g n x - g0 x‖ ^ 2 + 2 * (‖g n x - g0 x‖ * ‖g0 x‖)
      have htri := norm_add_le (g n x - g0 x) (g0 x)
      rw [sub_add_cancel] at htri
      have hrev := abs_norm_sub_norm_le (g n x) (g0 x)
      have hnonneg : 0 <= ‖g n x‖ + ‖g0 x‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [show ‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2 =
        (‖g n x‖ - ‖g0 x‖) * (‖g n x‖ + ‖g0 x‖) by ring, abs_mul]
      calc
        |‖g n x‖ - ‖g0 x‖| * |‖g n x‖ + ‖g0 x‖|
            <= ‖g n x - g0 x‖ * (‖g n x‖ + ‖g0 x‖) := by
              rw [abs_of_nonneg hnonneg]
              exact mul_le_mul_of_nonneg_right hrev hnonneg
        _ <= ‖g n x - g0 x‖ *
            (‖g n x - g0 x‖ + 2 * ‖g0 x‖) := by
              exact mul_le_mul_of_nonneg_left (by linarith [htri]) (norm_nonneg _)
        _ = ‖g n x - g0 x‖ ^ 2 +
            2 * (‖g n x - g0 x‖ * ‖g0 x‖) := by ring
    exact hraw.trans (by linarith [hcross n])
  have henergy_l1 : Tendsto
      (fun n => ∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (D n)) atTop (nhds 0) := by simpa using hD.sqrt
    have hu : Tendsto (fun n => D n + 2 * Real.sqrt (D n) * Real.sqrt B0)
        atTop (nhds 0) := by
      simpa only [zero_add, zero_mul, mul_zero, add_zero] using
        hD.add ((hsqrt.const_mul 2).mul_const (Real.sqrt B0))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
      (Eventually.of_forall henergy_l1_bound)
  let beta : Nat -> Real := fun n => (Real.sqrt (Real.sqrt n))⁻¹
  let alpha : Nat -> Real := fun n => max (beta n) (Real.sqrt (H n))
  let A : Nat -> Real := fun n => alpha n * Real.sqrt n
  have hrootroot : Tendsto (fun n : Nat => Real.sqrt (Real.sqrt n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hbeta : Tendsto beta atTop (nhds 0) := by
    simpa only [beta] using! tendsto_inv_atTop_zero.comp hrootroot
  have hsqrtH : Tendsto (fun n => Real.sqrt (H n)) atTop (nhds 0) := by simpa using hH.sqrt
  have halpha : Tendsto alpha atTop (nhds 0) := by
    simpa only [alpha, max_self] using hbeta.max hsqrtH
  have hbeta_nonneg (n : Nat) : 0 <= beta n := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have halpha_nonneg (n : Nat) : 0 <= alpha n :=
    hbeta_nonneg n |>.trans (le_max_left _ _)
  have halpha_pos : ∀ᶠ n in atTop, 0 < alpha n := by
    filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have : 0 < beta n := inv_pos.mpr (Real.sqrt_pos.2 (Real.sqrt_pos.2 hnR))
    exact this.trans_le (le_max_left _ _)
  have hA_nonneg (n : Nat) : 0 <= A n :=
    mul_nonneg (halpha_nonneg n) (Real.sqrt_nonneg _)
  have hrootroot_le_A : ∀ᶠ n : Nat in atTop,
      Real.sqrt (Real.sqrt n) <= A n := by
    filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    let r : Real := Real.sqrt (Real.sqrt n)
    have hr : r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (Real.sqrt_pos.2 hnR))
    have hsqrt_n : Real.sqrt n = r * r := by
      simpa only [r] using (Real.mul_self_sqrt (Real.sqrt_nonneg n)).symm
    calc
      Real.sqrt (Real.sqrt n) = beta n * Real.sqrt n := by
        change r = r⁻¹ * Real.sqrt n
        rw [hsqrt_n, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]
      _ <= alpha n * Real.sqrt n := by
        gcongr
        exact le_max_left _ _
      _ = A n := rfl
  have hA : Tendsto A atTop atTop := by
    exact tendsto_atTop_mono' atTop hrootroot_le_A hrootroot
  have hweighted_tail : Tendsto
      (fun n => ∫ x in {x | A n < ‖g n x‖ ^ 2}, ‖g n x‖ ^ 2 ∂mu)
      atTop (nhds 0) :=
    integral_tail_of_L1_anchor mu (fun x => ‖g0 x‖ ^ 2)
      (fun n x => ‖g n x‖ ^ 2) (hg0_meas.norm.pow_const 2)
      (fun n => (hg_meas n).norm.pow_const 2) hz0_int hz_int
      (fun _ => sq_nonneg _) (fun _ _ => sq_nonneg _) henergy_l1 A hA_nonneg hA
  let low0 : Nat -> Set Omega := fun n => {x | q0 x < 4 * alpha n}
  have hlow0_meas (n : Nat) : MeasurableSet (low0 n) :=
    measurableSet_lt hq0_meas measurable_const
  have hlow0 : Tendsto
      (fun n => ∫ x in low0 n, ‖g0 x‖ ^ 2 ∂mu) atTop (nhds 0) := by
    have hdom : Tendsto
        (fun n => ∫ x, (low0 n).indicator (fun x => ‖g0 x‖ ^ 2) x ∂mu)
        atTop (nhds (∫ x, (0 : Real) ∂mu)) :=
      tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖g0 x‖ ^ 2)
      (Eventually.of_forall fun n => (hg0_meas.norm.pow_const 2).indicator (hlow0_meas n)
        |>.aestronglyMeasurable)
      (Eventually.of_forall fun n => Eventually.of_forall fun x => by
        by_cases hx : x ∈ low0 n
        · simp [hx]
        · simp [hx])
      hz0_int (Eventually.of_forall fun x => ?_)
    · simpa only [integral_indicator (hlow0_meas _), integral_zero] using hdom
    · by_cases hq : q0 x = 0
      · have hgzero : g0 x = 0 := by simp [g0, hq]
        convert (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real)) atTop (nhds 0)) using 1
        funext n
        simp [hgzero]
      · have hqpos : 0 < q0 x := lt_of_le_of_ne (hq0_nonneg x) (Ne.symm hq)
        have hevent : ∀ᶠ n in atTop, 4 * alpha n < q0 x := by
          obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp halpha (q0 x / 4)
            (div_pos hqpos (by positivity))
          exact eventually_atTop.2 ⟨N, fun n hn => by
            have h := hN n hn
            rw [Real.dist_eq, sub_zero, abs_of_nonneg (halpha_nonneg n)] at h
            linarith⟩
        apply tendsto_const_nhds.congr'
        filter_upwards [hevent] with n hn
        simp [low0, not_lt.mpr hn.le]
  let M : Nat -> Real := fun n => (alpha n)⁻¹
  have halphaWithin : Tendsto alpha atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨halpha, halpha_pos⟩
  have hM : Tendsto M atTop atTop := by
    simpa only [M] using! halphaWithin.inv_tendsto_nhdsGT_zero
  have hM_nonneg (n : Nat) : 0 <= M n := inv_nonneg.mpr (halpha_nonneg n)
  have hf0_sq_int : Integrable (fun x => ‖f0 x‖ ^ 2) Q0 :=
    (memLp_two_iff_integrable_sq_norm hf0_memLp.aestronglyMeasurable).mp hf0_memLp
  have hf0_tail : Tendsto
      (fun n => ∫ x in {x | M n < ‖f0 x‖ ^ 2}, ‖f0 x‖ ^ 2 ∂Q0) atTop (nhds 0) := by
    apply integral_tail_of_L1_anchor Q0 (fun x => ‖f0 x‖ ^ 2)
      (fun _ x => ‖f0 x‖ ^ 2) (hf0_meas.norm.pow_const 2)
      (fun _ => hf0_meas.norm.pow_const 2) hf0_sq_int (fun _ => hf0_sq_int)
      (fun _ => sq_nonneg _) (fun _ _ => sq_nonneg _)
      (by simp) M hM_nonneg hM
  have hQ0_sq (s : Set Omega) (hs : MeasurableSet s) :
      (∫ x in s, ‖g0 x‖ ^ 2 ∂mu) = ∫ x in s, ‖f0 x‖ ^ 2 ∂Q0 := by
    rw [hQ0, setIntegral_withDensity_eq_setIntegral_toReal_smul
      hq0_meas.ennreal_ofReal (by simp) _ hs]
    apply setIntegral_congr_fun hs
    intro x _
    change ‖g0 x‖ ^ 2 = (ENNReal.ofReal (q0 x)).toReal * ‖f0 x‖ ^ 2
    rw [ENNReal.toReal_ofReal (hq0_nonneg x)]
    simp only [g0, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hq0_nonneg x)]
  let bad : Nat -> Set Omega := fun n =>
    {x | 4 * alpha n <= q0 x ∧ qn n x < alpha n}
  have hbad_meas (n : Nat) : MeasurableSet (bad n) :=
    (measurableSet_le measurable_const hq0_meas).inter
      (measurableSet_lt (hqn_meas n) measurable_const)
  have hhell_int (n : Nat) : Integrable
      (fun x => (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2) mu :=
    (hsdiff_memLp n).integrable_sq
  have hbad_density (n : Nat) (x : Omega) (hx : x ∈ bad n) :
      q0 x <= 4 * (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2 := by
    have hq0sq : (Real.sqrt (q0 x)) ^ 2 = q0 x := Real.sq_sqrt (hq0_nonneg x)
    have hqnsq : (Real.sqrt (qn n x)) ^ 2 = qn n x := Real.sq_sqrt (hqn_nonneg n x)
    have hsq : (2 * Real.sqrt (qn n x)) ^ 2 < (Real.sqrt (q0 x)) ^ 2 := by
      rw [mul_pow, hqnsq, hq0sq]
      linarith [hx.1, hx.2]
    have hsqrt : 2 * Real.sqrt (qn n x) < Real.sqrt (q0 x) :=
      (sq_lt_sq₀ (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)).mp hsq
    have hhalf : Real.sqrt (q0 x) <=
        2 * (Real.sqrt (q0 x) - Real.sqrt (qn n x)) := by linarith
    have hdiff_nonneg : 0 <= Real.sqrt (q0 x) - Real.sqrt (qn n x) := by
      linarith [Real.sqrt_nonneg (qn n x)]
    have hsq' : (Real.sqrt (q0 x)) ^ 2 <=
        (2 * (Real.sqrt (q0 x) - Real.sqrt (qn n x))) ^ 2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg (by positivity) hdiff_nonneg)).mpr hhalf
    rw [hq0sq, mul_pow] at hsq'
    nlinarith
  have hHM : Tendsto (fun n => 4 * M n * H n) atTop (nhds 0) := by
    have hbound : ∀ᶠ n in atTop, 4 * M n * H n <= 4 * Real.sqrt (H n) := by
      filter_upwards [halpha_pos] with n han
      have hsle : Real.sqrt (H n) <= alpha n := le_max_right _ _
      have hquot : M n * H n <= Real.sqrt (H n) := by
        change (alpha n)⁻¹ * H n <= Real.sqrt (H n)
        rw [inv_mul_eq_div]
        apply (div_le_iff₀ han).2
        calc
          H n = Real.sqrt (H n) * Real.sqrt (H n) := by
            symm
            exact Real.mul_self_sqrt (hH_nonneg n)
          _ <= Real.sqrt (H n) * alpha n :=
            mul_le_mul_of_nonneg_left hsle (Real.sqrt_nonneg _)
      linarith
    have hu : Tendsto (fun n => 4 * Real.sqrt (H n)) atTop (nhds 0) := by
      simpa using hsqrtH.const_mul 4
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun n => mul_nonneg
        (mul_nonneg (by positivity) (hM_nonneg n)) (hH_nonneg n)) hbound
  have hbad_bound (n : Nat) :
      (∫ x in bad n, ‖g0 x‖ ^ 2 ∂mu) <=
        4 * M n * H n + ∫ x in {x | M n < ‖f0 x‖ ^ 2}, ‖f0 x‖ ^ 2 ∂Q0 := by
    let tail : Set Omega := {x | M n < ‖f0 x‖ ^ 2}
    have htail_meas : MeasurableSet tail :=
      measurableSet_lt measurable_const (hf0_meas.norm.pow_const 2)
    calc
      (∫ x in bad n, ‖g0 x‖ ^ 2 ∂mu) <=
          ∫ x in bad n,
            (4 * M n * (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2 +
              tail.indicator (fun x => ‖g0 x‖ ^ 2) x) ∂mu := by
        refine setIntegral_mono_on hz0_int.integrableOn
          (((hhell_int n).const_mul (4 * M n)).add
            (hz0_int.indicator htail_meas) |>.integrableOn) (hbad_meas n) ?_
        intro x hx
        show ‖g0 x‖ ^ 2 <= 4 * M n *
          (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2 +
            tail.indicator (fun x => ‖g0 x‖ ^ 2) x
        by_cases ht : x ∈ tail
        · rw [Set.indicator_of_mem ht]
          exact le_add_of_nonneg_left (mul_nonneg
            (mul_nonneg (by positivity) (hM_nonneg n)) (sq_nonneg
              (Real.sqrt (qn n x) - Real.sqrt (q0 x))))
        · rw [Set.indicator_of_notMem ht, add_zero]
          have hfbd : ‖f0 x‖ ^ 2 <= M n := le_of_not_gt ht
          have hz0eq : ‖g0 x‖ ^ 2 = q0 x * ‖f0 x‖ ^ 2 := by
            simp only [g0, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hq0_nonneg x)]
          rw [hz0eq]
          calc
            q0 x * ‖f0 x‖ ^ 2 <=
                (4 * (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2) *
                  ‖f0 x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hbad_density n x hx) (sq_nonneg _)
            _ <= (4 * (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2) * M n :=
              mul_le_mul_of_nonneg_left hfbd
                (mul_nonneg (by positivity) (sq_nonneg _))
            _ = 4 * M n * (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2 := by ring
      _ <= ∫ x, 4 * M n * (Real.sqrt (qn n x) - Real.sqrt (q0 x)) ^ 2 +
              tail.indicator (fun x => ‖g0 x‖ ^ 2) x ∂mu := by
        exact setIntegral_le_integral
          (((hhell_int n).const_mul (4 * M n)).add (hz0_int.indicator htail_meas))
          (Eventually.of_forall fun x => add_nonneg
            (mul_nonneg (mul_nonneg (by positivity) (hM_nonneg n)) (sq_nonneg _))
            (Set.indicator_apply_nonneg fun _ => sq_nonneg _))
      _ = 4 * M n * H n + ∫ x in tail, ‖g0 x‖ ^ 2 ∂mu := by
        rw [integral_add ((hhell_int n).const_mul (4 * M n))
              (hz0_int.indicator htail_meas),
          integral_const_mul, integral_indicator htail_meas]
      _ = 4 * M n * H n + ∫ x in {x | M n < ‖f0 x‖ ^ 2}, ‖f0 x‖ ^ 2 ∂Q0 := by
        rw [hQ0_sq tail htail_meas]
  have hbad : Tendsto (fun n => ∫ x in bad n, ‖g0 x‖ ^ 2 ∂mu)
      atTop (nhds 0) := by
    have hu : Tendsto (fun n => 4 * M n * H n +
        ∫ x in {x | M n < ‖f0 x‖ ^ 2}, ‖f0 x‖ ^ 2 ∂Q0) atTop (nhds 0) := by
      simpa only [zero_add] using hHM.add hf0_tail
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun n => setIntegral_nonneg (hbad_meas n) fun _ _ => sq_nonneg _)
      (Eventually.of_forall hbad_bound)
  let low : Nat -> Set Omega := fun n => {x | qn n x < alpha n}
  have hlow_meas (n : Nat) : MeasurableSet (low n) :=
    measurableSet_lt (hqn_meas n) measurable_const
  have hlow_subset (n : Nat) : low n ⊆ low0 n ∪ bad n := by
    intro x hx
    by_cases h0 : q0 x < 4 * alpha n
    · exact Or.inl h0
    · exact Or.inr ⟨le_of_not_gt h0, hx⟩
  have hlow_z0_bound (n : Nat) :
      (∫ x in low n, ‖g0 x‖ ^ 2 ∂mu) <=
        (∫ x in low0 n, ‖g0 x‖ ^ 2 ∂mu) +
          ∫ x in bad n, ‖g0 x‖ ^ 2 ∂mu := by
    rw [← integral_indicator (hlow_meas n), ← integral_indicator (hlow0_meas n),
      ← integral_indicator (hbad_meas n), ← integral_add
        (hz0_int.indicator (hlow0_meas n)) (hz0_int.indicator (hbad_meas n))]
    refine integral_mono (hz0_int.indicator (hlow_meas n))
      ((hz0_int.indicator (hlow0_meas n)).add (hz0_int.indicator (hbad_meas n))) ?_
    intro x
    change (low n).indicator (fun x => ‖g0 x‖ ^ 2) x <=
      (low0 n).indicator (fun x => ‖g0 x‖ ^ 2) x +
        (bad n).indicator (fun x => ‖g0 x‖ ^ 2) x
    by_cases hx : x ∈ low n
    · rcases hlow_subset n hx with h0 | hb
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem h0]
        exact le_add_of_nonneg_right
          (Set.indicator_apply_nonneg (fun _ => sq_nonneg _) )
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hb]
        exact le_add_of_nonneg_left
          (Set.indicator_apply_nonneg (fun _ => sq_nonneg _) )
    · rw [Set.indicator_of_notMem hx]
      exact add_nonneg
        (Set.indicator_apply_nonneg (fun _ => sq_nonneg _))
        (Set.indicator_apply_nonneg (fun _ => sq_nonneg _))
  have hlow_z0 : Tendsto (fun n => ∫ x in low n, ‖g0 x‖ ^ 2 ∂mu)
      atTop (nhds 0) := by
    have hu : Tendsto (fun n => (∫ x in low0 n, ‖g0 x‖ ^ 2 ∂mu) +
        ∫ x in bad n, ‖g0 x‖ ^ 2 ∂mu) atTop (nhds 0) := by
      simpa only [zero_add] using hlow0.add hbad
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun n => setIntegral_nonneg (hlow_meas n) fun _ _ => sq_nonneg _)
      (Eventually.of_forall hlow_z0_bound)
  have hlow_energy_bound (n : Nat) :
      (∫ x in low n, ‖g n x‖ ^ 2 ∂mu) <=
        (∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) +
          ∫ x in low n, ‖g0 x‖ ^ 2 ∂mu := by
    calc
      (∫ x in low n, ‖g n x‖ ^ 2 ∂mu) <=
          ∫ x in low n, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| + ‖g0 x‖ ^ 2 ∂mu := by
        refine setIntegral_mono_on (hz_int n).integrableOn
          ((henergy_diff_int n).add hz0_int).integrableOn (hlow_meas n) ?_
        intro x _
        linarith [le_abs_self (‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2)]
      _ = (∫ x in low n, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) +
          ∫ x in low n, ‖g0 x‖ ^ 2 ∂mu := by
        rw [integral_add (henergy_diff_int n).integrableOn hz0_int.integrableOn]
      _ <= (∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) +
          ∫ x in low n, ‖g0 x‖ ^ 2 ∂mu := by
        exact add_le_add_left (setIntegral_le_integral (henergy_diff_int n)
          (Eventually.of_forall fun _ => abs_nonneg _)) _
  have hlow_energy : Tendsto
      (fun n => ∫ x in low n, ‖g n x‖ ^ 2 ∂mu) atTop (nhds 0) := by
    have hu : Tendsto (fun n => (∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) +
        ∫ x in low n, ‖g0 x‖ ^ 2 ∂mu) atTop (nhds 0) := by
      simpa only [zero_add] using henergy_l1.add hlow_z0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun n => setIntegral_nonneg (hlow_meas n) fun _ _ => sq_nonneg _)
      (Eventually.of_forall hlow_energy_bound)
  let Y : Nat -> Fin d -> Fin d -> Omega -> Real :=
    fun n j k x => fn n x j * fn n x k
  have hY_meas (n : Nat) (j k : Fin d) : Measurable (Y n j k) :=
    (((PiLp.proj (p := 2) (β := fun _ : Fin d => Real) j :
      EuclideanSpace Real (Fin d) →L[Real] Real).measurable.comp (hfn_meas n)).mul
      ((PiLp.proj (p := 2) (β := fun _ : Fin d => Real) k :
      EuclideanSpace Real (Fin d) →L[Real] Real).measurable.comp (hfn_meas n)))
  have hY_int (n : Nat) (j k : Fin d) : Integrable (Y n j k) (Qn n) := by
    have hj : MemLp (fun x => fn n x j) 2 (Qn n) := by
      simpa using ((hfn_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => Real) j :
          EuclideanSpace Real (Fin d) →L[Real] Real))
    have hk : MemLp (fun x => fn n x k) 2 (Qn n) := by
      simpa using ((hfn_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => Real) k :
          EuclideanSpace Real (Fin d) →L[Real] Real))
    exact hj.integrable_mul hk
  have hY_le_norm_sq (n : Nat) (j k : Fin d) (x : Omega) :
      |Y n j k x| <= ‖fn n x‖ ^ 2 := by
    have hj : |fn n x j| <= ‖fn n x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (fn n x) j
    have hk : |fn n x k| <= ‖fn n x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (fn n x) k
    simp only [Y, abs_mul, pow_two]
    exact mul_le_mul hj hk (abs_nonneg _) (norm_nonneg _)
  have hweighted_Y (n : Nat) (j k : Fin d) : Integrable
      (fun x => qn n x * |Y n j k x|) mu := by
    have hi' : Integrable
        (fun x => |Y n j k x| * (ENNReal.ofReal (qn n x)).toReal) mu := by
      rw [← MeasureTheory.integrable_withDensity_iff (hqn_meas n).ennreal_ofReal (by simp),
        ← hQn n]
      exact (hY_int n j k).norm
    have hi : Integrable (fun x => |Y n j k x| * qn n x) mu := by
      convert hi' using 1
      funext x
      rw [ENNReal.toReal_ofReal (hqn_nonneg n x)]
    simpa only [mul_comm] using hi
  have hrow_first_bound (n : Nat) (j k : Fin d) :
      (∫ x, |Y n j k x| ∂(Qn n)) <=
        ∫ x, ‖g n x‖ ^ 2 ∂mu := by
    rw [hQn n, integral_withDensity_eq_integral_toReal_smul
      (hqn_meas n).ennreal_ofReal (by simp)]
    have hrhs : (∫ x, ‖g n x‖ ^ 2 ∂mu) =
        ∫ x, qn n x * ‖fn n x‖ ^ 2 ∂mu := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [g, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hqn_nonneg n x)]
    rw [hrhs]
    refine integral_mono ?_ ?_ ?_
    · have heq : (fun x => (ENNReal.ofReal (qn n x)).toReal • |Y n j k x|) =
          fun x => qn n x * |Y n j k x| := by
        funext x
        rw [ENNReal.toReal_ofReal (hqn_nonneg n x), smul_eq_mul]
      rw [heq]
      exact hweighted_Y n j k
    · have heq : (fun x => qn n x * ‖fn n x‖ ^ 2) =
          fun x => ‖g n x‖ ^ 2 := by
        funext x
        simp only [g, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (hqn_nonneg n x)]
      rw [heq]
      exact hz_int n
    · intro x
      change (ENNReal.ofReal (qn n x)).toReal * |Y n j k x| <=
        qn n x * ‖fn n x‖ ^ 2
      rw [ENNReal.toReal_ofReal (hqn_nonneg n x)]
      exact mul_le_mul_of_nonneg_left (hY_le_norm_sq n j k x) (hqn_nonneg n x)
  have henergy_first : ∀ᶠ n in atTop, (∫ x, ‖g n x‖ ^ 2 ∂mu) <= B0 + 1 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp henergy_l1 1 zero_lt_one
    have hevent : ∀ᶠ n in atTop,
        dist (∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) 0 < 1 :=
      eventually_atTop.2 ⟨N, hN⟩
    filter_upwards [hevent] with n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at hn
    calc
      (∫ x, ‖g n x‖ ^ 2 ∂mu) <=
          (∫ x, |‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2| ∂mu) + B0 := by
        rw [show B0 = ∫ x, ‖g0 x‖ ^ 2 ∂mu by rfl, ← integral_add (henergy_diff_int n) hz0_int]
        refine integral_mono (hz_int n) ((henergy_diff_int n).add hz0_int) ?_
        intro x
        linarith [le_abs_self (‖g n x‖ ^ 2 - ‖g0 x‖ ^ 2)]
      _ <= B0 + 1 := by linarith
  have hY_first (j k : Fin d) : ∀ᶠ n in atTop,
      (∫ x, |Y n j k x| ∂(Qn n)) <= B0 + 1 := by
    filter_upwards [henergy_first] with n hn
    exact (hrow_first_bound n j k).trans hn
  have hC : 0 <= B0 + 1 := by linarith
  have hrow_tail_bound (n : Nat) (hn : 0 < n) (j k : Fin d) :
      (∫ x in {x | Real.sqrt n < |Y n j k x|}, |Y n j k x| ∂(Qn n)) <=
        (∫ x in {x | A n < ‖g n x‖ ^ 2}, ‖g n x‖ ^ 2 ∂mu) +
          ∫ x in low n, ‖g n x‖ ^ 2 ∂mu := by
    let rowTail : Set Omega := {x | Real.sqrt n < |Y n j k x|}
    let weightedTail : Set Omega := {x | A n < ‖g n x‖ ^ 2}
    have hrowTail_meas : MeasurableSet rowTail :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hY_meas n j k))
    have hweightedTail_meas : MeasurableSet weightedTail :=
      measurableSet_lt measurable_const ((hg_meas n).norm.pow_const 2)
    rw [hQn n, setIntegral_withDensity_eq_setIntegral_toReal_smul
      (hqn_meas n).ennreal_ofReal (by simp) _ hrowTail_meas]
    rw [← integral_indicator hrowTail_meas, ← integral_indicator hweightedTail_meas,
      ← integral_indicator (hlow_meas n), ← integral_add
        ((hz_int n).indicator hweightedTail_meas) ((hz_int n).indicator (hlow_meas n))]
    refine integral_mono ?_
      (((hz_int n).indicator hweightedTail_meas).add ((hz_int n).indicator (hlow_meas n)))
      ?_
    · have := hweighted_Y n j k
      convert this.indicator hrowTail_meas using 1
      on_goal 1 => exact rfl
      funext x
      simp only [Set.indicator]
      split_ifs <;> simp_all [ENNReal.toReal_ofReal (hqn_nonneg n x), smul_eq_mul]
    · intro x
      by_cases htail : x ∈ rowTail
      · have hqY : qn n x * |Y n j k x| <= ‖g n x‖ ^ 2 := by
          calc
            qn n x * |Y n j k x| <= qn n x * ‖fn n x‖ ^ 2 :=
              mul_le_mul_of_nonneg_left (hY_le_norm_sq n j k x) (hqn_nonneg n x)
            _ = ‖g n x‖ ^ 2 := by
              simp only [g, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
                Real.sq_sqrt (hqn_nonneg n x)]
        by_cases hlo : x ∈ low n
        · rw [Set.indicator_of_mem htail]
          change (ENNReal.ofReal (qn n x)).toReal * |Y n j k x| <=
            weightedTail.indicator (fun x => ‖g n x‖ ^ 2) x +
              (low n).indicator (fun x => ‖g n x‖ ^ 2) x
          rw [Set.indicator_of_mem hlo,
            ENNReal.toReal_ofReal (hqn_nonneg n x)]
          exact hqY.trans (le_add_of_nonneg_left
            (Set.indicator_apply_nonneg (fun _ => sq_nonneg _)))
        · have hqalpha : alpha n <= qn n x := le_of_not_gt hlo
          have hnR : (0 : Real) < n := by exact_mod_cast hn
          have halpha_n : 0 < alpha n :=
            (inv_pos.mpr (Real.sqrt_pos.2 (Real.sqrt_pos.2 hnR))).trans_le
              (le_max_left _ _)
          have hweighted : x ∈ weightedTail := by
            have hrow : Real.sqrt n < |Y n j k x| := htail
            have hA_lt : A n < qn n x * |Y n j k x| := by
              calc
                A n = alpha n * Real.sqrt n := rfl
                _ <= qn n x * Real.sqrt n :=
                  mul_le_mul_of_nonneg_right hqalpha (Real.sqrt_nonneg _)
                _ < qn n x * |Y n j k x| :=
                  mul_lt_mul_of_pos_left hrow (halpha_n.trans_le hqalpha)
            exact hA_lt.trans_le hqY
          simp [Set.indicator_of_mem htail, Set.indicator_of_mem hweighted,
            Set.indicator_of_notMem hlo, ENNReal.toReal_ofReal (hqn_nonneg n x),
            smul_eq_mul, hqY]
      · rw [Set.indicator_of_notMem htail]
        exact add_nonneg
          (Set.indicator_apply_nonneg (fun _ => sq_nonneg _))
          (Set.indicator_apply_nonneg (fun _ => sq_nonneg _))
  have hY_tail (j k : Fin d) : Tendsto
      (fun n => ∫ x in {x | Real.sqrt n < |Y n j k x|}, |Y n j k x| ∂(Qn n))
      atTop (nhds 0) := by
    have hu : Tendsto (fun n => (∫ x in {x | A n < ‖g n x‖ ^ 2},
        ‖g n x‖ ^ 2 ∂mu) + ∫ x in low n, ‖g n x‖ ^ 2 ∂mu) atTop (nhds 0) := by
      simpa only [zero_add] using hweighted_tail.add hlow_energy
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun n => setIntegral_nonneg
        (measurableSet_lt measurable_const (continuous_abs.measurable.comp (hY_meas n j k)))
        fun _ _ => abs_nonneg _)
      (by filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
          exact hrow_tail_bound n hn j k)
  have hmean_bridge (n : Nat) (j k : Fin d) :
      (∫ x, Y n j k x ∂(Qn n)) = ∫ x, g n x j * g n x k ∂mu := by
    rw [hQn n, integral_withDensity_eq_integral_toReal_smul
      (hqn_meas n).ennreal_ofReal (by simp)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (ENNReal.ofReal (qn n x)).toReal * Y n j k x =
        g n x j * g n x k
      rw [ENNReal.toReal_ofReal (hqn_nonneg n x)]
      simp only [Y, g, WithLp.ofLp_smul, Pi.smul_apply]
      calc
        qn n x * (fn n x j * fn n x k) =
            (Real.sqrt (qn n x) * Real.sqrt (qn n x)) *
              (fn n x j * fn n x k) := by rw [Real.mul_self_sqrt (hqn_nonneg n x)]
        _ = (Real.sqrt (qn n x) * fn n x j) *
              (Real.sqrt (qn n x) * fn n x k) := by ring
  have hpop_bridge (j k : Fin d) :
      populationGram Q0 f0 j k = ∫ x, g0 x j * g0 x k ∂mu := by
    rw [populationGram, hQ0, integral_withDensity_eq_integral_toReal_smul
      hq0_meas.ennreal_ofReal (by simp)]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (ENNReal.ofReal (q0 x)).toReal * (f0 x j * f0 x k) =
        g0 x j * g0 x k
      rw [ENNReal.toReal_ofReal (hq0_nonneg x)]
      simp only [g0, WithLp.ofLp_smul, Pi.smul_apply]
      calc
        q0 x * (f0 x j * f0 x k) =
            (Real.sqrt (q0 x) * Real.sqrt (q0 x)) * (f0 x j * f0 x k) := by
          rw [Real.mul_self_sqrt (hq0_nonneg x)]
        _ = (Real.sqrt (q0 x) * f0 x j) *
              (Real.sqrt (q0 x) * f0 x k) := by ring
  let qEntry : Nat -> Fin d -> Fin d -> Omega -> Real := fun n j k x =>
    |g n x j * g n x k - g0 x j * g0 x k|
  have hgprod_int (n : Nat) (j k : Fin d) :
      Integrable (fun x => g n x j * g n x k) mu := by
    have hnj : MemLp (fun x => g n x j) 2 mu := by
      simpa using ((hg_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => Real) j :
          EuclideanSpace Real (Fin d) →L[Real] Real))
    have hnk : MemLp (fun x => g n x k) 2 mu := by
      simpa using ((hg_memLp n).continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => Real) k :
          EuclideanSpace Real (Fin d) →L[Real] Real))
    exact hnj.integrable_mul hnk
  have hg0prod_int (j k : Fin d) : Integrable (fun x => g0 x j * g0 x k) mu := by
    have h0j : MemLp (fun x => g0 x j) 2 mu := by
      simpa using (hg0_memLp.continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => Real) j :
          EuclideanSpace Real (Fin d) →L[Real] Real))
    have h0k : MemLp (fun x => g0 x k) 2 mu := by
      simpa using (hg0_memLp.continuousLinearMap_comp
        (PiLp.proj (p := 2) (β := fun _ : Fin d => Real) k :
          EuclideanSpace Real (Fin d) →L[Real] Real))
    exact h0j.integrable_mul h0k
  have hqEntry_int (n : Nat) (j k : Fin d) : Integrable (qEntry n j k) mu := by
    simpa only [qEntry, Real.norm_eq_abs] using!
      ((hgprod_int n j k).sub (hg0prod_int j k)).norm
  have hqEntry_bound (n : Nat) (j k : Fin d) :
      (∫ x, qEntry n j k x ∂mu) <=
        D n + 2 * Real.sqrt (D n) * Real.sqrt B0 := by
    have hd2 : Integrable (fun x => ‖g n x - g0 x‖ ^ 2) mu :=
      (memLp_two_iff_integrable_sq_norm (hdiff_memLp n).aestronglyMeasurable).mp
        (hdiff_memLp n)
    have hcross_int : Integrable (fun x => ‖g n x - g0 x‖ * ‖g0 x‖) mu :=
      (hdiff_memLp n).norm.integrable_mul hg0_memLp.norm
    have hraw : (∫ x, qEntry n j k x ∂mu) <=
        D n + 2 * ∫ x, ‖g n x - g0 x‖ * ‖g0 x‖ ∂mu := by
      rw [show D n + 2 * ∫ x, ‖g n x - g0 x‖ * ‖g0 x‖ ∂mu =
          ∫ x, ‖g n x - g0 x‖ ^ 2 +
            2 * (‖g n x - g0 x‖ * ‖g0 x‖) ∂mu by
        rw [integral_add hd2 (hcross_int.const_mul 2), integral_const_mul]
        ]
      refine integral_mono (hqEntry_int n j k) (hd2.add (hcross_int.const_mul 2)) ?_
      intro x
      change |g n x j * g n x k - g0 x j * g0 x k| <=
        ‖g n x - g0 x‖ ^ 2 + 2 * (‖g n x - g0 x‖ * ‖g0 x‖)
      let E := ‖g n x - g0 x‖
      let A0 := ‖g0 x‖
      have hdj : |g n x j - g0 x j| <= E := by
        simpa only [Real.norm_eq_abs, E] using! PiLp.norm_apply_le (g n x - g0 x) j
      have hdk : |g n x k - g0 x k| <= E := by
        simpa only [Real.norm_eq_abs, E] using! PiLp.norm_apply_le (g n x - g0 x) k
      have h0j : |g0 x j| <= A0 := by
        simpa only [Real.norm_eq_abs, A0] using PiLp.norm_apply_le (g0 x) j
      have h0k : |g0 x k| <= A0 := by
        simpa only [Real.norm_eq_abs, A0] using PiLp.norm_apply_le (g0 x) k
      change |g n x j * g n x k - g0 x j * g0 x k| <= E ^ 2 + 2 * (E * A0)
      rw [show g n x j * g n x k - g0 x j * g0 x k =
        (g n x j - g0 x j) * (g n x k - g0 x k) +
        (g n x j - g0 x j) * g0 x k + g0 x j * (g n x k - g0 x k) by ring]
      calc
        |(g n x j - g0 x j) * (g n x k - g0 x k) +
            (g n x j - g0 x j) * g0 x k + g0 x j * (g n x k - g0 x k)| <=
          |(g n x j - g0 x j) * (g n x k - g0 x k)| +
            |(g n x j - g0 x j) * g0 x k| +
              |g0 x j * (g n x k - g0 x k)| := by
          linarith [abs_add_le
            ((g n x j - g0 x j) * (g n x k - g0 x k) +
              (g n x j - g0 x j) * g0 x k)
            (g0 x j * (g n x k - g0 x k)),
            abs_add_le ((g n x j - g0 x j) * (g n x k - g0 x k))
              ((g n x j - g0 x j) * g0 x k)]
        _ <= E * E + E * A0 + A0 * E := by
          simp only [abs_mul]
          gcongr
        _ = E ^ 2 + 2 * (E * A0) := by ring
    exact hraw.trans (by linarith [hcross n])
  have hqEntry_zero (j k : Fin d) : Tendsto
      (fun n => ∫ x, qEntry n j k x ∂mu) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun n => Real.sqrt (D n)) atTop (nhds 0) := by simpa using hD.sqrt
    have hu : Tendsto (fun n => D n + 2 * Real.sqrt (D n) * Real.sqrt B0)
        atTop (nhds 0) := by
      simpa only [zero_add, zero_mul, mul_zero, add_zero] using
        hD.add ((hsqrt.const_mul 2).mul_const (Real.sqrt B0))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
      (Eventually.of_forall fun n => hqEntry_bound n j k)
  have hmean_limit (j k : Fin d) : Tendsto
      (fun n => (∫ x, Y n j k x ∂(Qn n)) - populationGram Q0 f0 j k)
      atTop (nhds 0) := by
    have hnorm : Tendsto
        (fun n => |(∫ x, Y n j k x ∂(Qn n)) - populationGram Q0 f0 j k|)
        atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (hqEntry_zero j k) (Eventually.of_forall fun _ => abs_nonneg _) ?_
      exact Eventually.of_forall fun n => calc
        |(∫ x, Y n j k x ∂(Qn n)) - populationGram Q0 f0 j k| =
            |∫ x, (g n x j * g n x k - g0 x j * g0 x k) ∂mu| := by
          rw [hmean_bridge n j k, hpop_bridge j k, integral_sub
            (hgprod_int n j k) (hg0prod_int j k)]
        _ <= ∫ x, qEntry n j k x ∂mu := by
          simpa only [qEntry, Real.norm_eq_abs] using
            (norm_integral_le_integral_norm
              (fun x => g n x j * g n x k - g0 x j * g0 x k))
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa only [Real.norm_eq_abs] using hnorm
  have hcenter (j k : Fin d) : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => Qn n))
      (fun n X => (n : Real)⁻¹ * ∑ i, Y n j k (X i) -
        ∫ x, Y n j k x ∂(Qn n)) :=
    triangular_empirical_mean_of_sqrt_tail Qn (fun n => Y n j k)
      (fun n => hY_meas n j k) (fun n => hY_int n j k) (B0 + 1) hC
      (hY_first j k) (hY_tail j k)
  have hbias (j k : Fin d) : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => Qn n))
      (fun n (_ : Fin n -> Omega) =>
        (∫ x, Y n j k x ∂(Qn n)) - populationGram Q0 f0 j k) := by
    intro epsilon hepsilon
    have hevent : ∀ᶠ n in atTop,
        |(∫ x, Y n j k x ∂(Qn n)) - populationGram Q0 f0 j k| < epsilon := by
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hmean_limit j k) epsilon hepsilon
      exact eventually_atTop.2 ⟨N, fun n hn => by
        simpa only [Real.dist_eq, sub_zero] using hN n hn⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    have hempty : {X : Fin n -> Omega |
        epsilon <= |(∫ x, Y n j k x ∂(Qn n)) - populationGram Q0 f0 j k|} = ∅ := by
      ext X
      simp [not_le.mpr hn]
    simp [hempty]
  apply TendstoInProbZero.matrix_of_entry
  intro j k
  have hsum := TendstoInProbZero.add (hcenter j k) (hbias j k)
  convert hsum using 1
  funext n X
  simp only [empGram, Matrix.sub_apply, Y]
  ring

end AsymptoticStatistics
