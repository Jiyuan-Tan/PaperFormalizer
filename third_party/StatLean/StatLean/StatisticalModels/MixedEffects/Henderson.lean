module
public import StatLean.StatisticalModels.MixedEffects.Marginal

@[expose] public section

/-!
# Henderson's mixed-model equations

The computational heart of mixed-model practice, as exact matrix algebra:

* **`pushThrough` (M5i)** — the push-through identity
  `G Zᵀ (Z G Zᵀ + R)⁻¹ = (Zᵀ R⁻¹ Z + G⁻¹)⁻¹ Zᵀ R⁻¹`, the bridge between the
  covariance (BLUP) and precision (MME) forms;
* **`hendersonMME` (M5ii)** — Henderson's mixed-model equations: `(β̂, b̂)` solves the
  block system
  `[XᵀR⁻¹X, XᵀR⁻¹Z; ZᵀR⁻¹X, ZᵀR⁻¹Z + G⁻¹] (β̂, b̂) = (XᵀR⁻¹y, ZᵀR⁻¹y)`
  **iff** `b̂` is the BLUP at `β̂` and `β̂` solves the GLS normal equations in
  `V = Z G Zᵀ + R`;
* **`lmmLaw_dirac` (M4)** — the `G = δ₀` degeneration: the mixed model collapses to the
  fixed-effects linear model `Y = Xβ + ε` (the bridge to the library's existing
  linear-model treatments, stated against the explicit law — no cross-area import).

**Reference.** C. R. Henderson, O. Kempthorne, S. R. Searle, and C. M. von Krosigk, "The
estimation of environmental and genetic trends from records subject to culling,"
*Biometrics* **15** (1959), 192–218 (the equations); S. R. Searle, G. Casella, and C. E.
McCulloch, *Variance Components*, Wiley, 1992, §7.6 (verify §) (`SCM §7.6`); `Hen50`.

**Proof formalization notes.** The push-through identity is proved by multiplying both
sides by the invertible factors (`Matrix.nonsing_inv_mul`/`mul_nonsing_inv` under the
PosDef hypotheses) and normalizing — deliberately avoiding any Woodbury import. The MME
equivalence is `fromBlocks_mulVec` expansion + the push-through; all statements are pure
matrix/vector algebra (no measures). *Book vs Lean:* exact finite algebra; no estimation
theory claimed.

**Bibliographic comments.** The equations are Henderson's (1950, computational form in
Henderson et al. 1959); the push-through identity is matrix folklore (a Schur-complement
avatar), see SCM §7.6.
-/

open MeasureTheory Matrix

namespace StatLean.StatisticalModels.MixedEffects

variable {n p q : ℕ}

/-! ### LEAN-ONLY plumbing

Positive-definiteness of the two blocks that get inverted (`V = Z G Zᵀ + R` and the
precision block `P = Zᵀ R⁻¹ Z + G⁻¹`), the binomial inverse identity
`V⁻¹ = R⁻¹ − R⁻¹ Z P⁻¹ Zᵀ R⁻¹` (proved by `V · RHS = 1`, no Woodbury import), and
measurability of the LMM observation map.
-/

/-- LEAN-ONLY -/
private theorem posDef_marginalCov (Z : Matrix (Fin n) (Fin q) ℝ)
    (Gm : Matrix (Fin q) (Fin q) ℝ) (Rm : Matrix (Fin n) (Fin n) ℝ)
    (hG : Gm.PosDef) (hR : Rm.PosDef) : (Z * Gm * Zᵀ + Rm).PosDef := by
  refine Matrix.PosDef.posSemidef_add ?_ hR
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hG.posSemidef.mul_mul_conjTranspose_same Z

/-- LEAN-ONLY -/
private theorem posDef_precision (Z : Matrix (Fin n) (Fin q) ℝ)
    (Gm : Matrix (Fin q) (Fin q) ℝ) (Rm : Matrix (Fin n) (Fin n) ℝ)
    (hG : Gm.PosDef) (hR : Rm.PosDef) : (Zᵀ * Rm⁻¹ * Z + Gm⁻¹).PosDef := by
  refine Matrix.PosDef.posSemidef_add ?_ hG.inv
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    hR.inv.posSemidef.mul_mul_conjTranspose_same Zᵀ

/-- **M5i, the push-through identity** (`SCM §7.6`): the covariance form of the BLUP weight
equals its precision form. -/
theorem pushThrough (Z : Matrix (Fin n) (Fin q) ℝ) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: positive-definite variance components; SCM §7.6
    (hG : Gm.PosDef) (hR : Rm.PosDef) :
    Gm * Zᵀ * (Z * Gm * Zᵀ + Rm)⁻¹
      = (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹ := by
  have hV := posDef_marginalCov Z Gm Rm hG hR
  have hP := posDef_precision Z Gm Rm hG hR
  have hGd : IsUnit Gm.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hRd : IsUnit Rm.det := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  have hPd : IsUnit (Zᵀ * Rm⁻¹ * Z + Gm⁻¹).det := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hVd : IsUnit (Z * Gm * Zᵀ + Rm).det := (Matrix.isUnit_iff_isUnit_det _).mp hV.isUnit
  have hGinv : Gm⁻¹ * Gm = 1 := Matrix.nonsing_inv_mul _ hGd
  have hRinv : Rm⁻¹ * Rm = 1 := Matrix.nonsing_inv_mul _ hRd
  have hkey : (Zᵀ * Rm⁻¹ * Z + Gm⁻¹) * (Gm * Zᵀ)
      = Zᵀ * Rm⁻¹ * (Z * Gm * Zᵀ + Rm) := by
    have e1 : Gm⁻¹ * (Gm * Zᵀ) = Zᵀ := by
      rw [← Matrix.mul_assoc, hGinv, Matrix.one_mul]
    have e2 : Zᵀ * (Rm⁻¹ * Rm) = Zᵀ := by rw [hRinv, Matrix.mul_one]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, e1, e2]
  have h2 : Gm * Zᵀ
      = (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * (Zᵀ * Rm⁻¹ * (Z * Gm * Zᵀ + Rm)) := by
    rw [← hkey, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul]
  calc Gm * Zᵀ * (Z * Gm * Zᵀ + Rm)⁻¹
      = ((Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * (Zᵀ * Rm⁻¹ * (Z * Gm * Zᵀ + Rm)))
          * (Z * Gm * Zᵀ + Rm)⁻¹ := by rw [← h2]
    _ = (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹ := by
        rw [Matrix.mul_assoc _ (Zᵀ * Rm⁻¹ * (Z * Gm * Zᵀ + Rm)),
          Matrix.mul_assoc (Zᵀ * Rm⁻¹), Matrix.mul_nonsing_inv _ hVd, Matrix.mul_one,
          ← Matrix.mul_assoc]

/-- LEAN-ONLY: the binomial inverse identity. -/
private theorem inv_marginalCov (Z : Matrix (Fin n) (Fin q) ℝ)
    (Gm : Matrix (Fin q) (Fin q) ℝ) (Rm : Matrix (Fin n) (Fin n) ℝ)
    (hG : Gm.PosDef) (hR : Rm.PosDef) :
    (Z * Gm * Zᵀ + Rm)⁻¹
      = Rm⁻¹ - Rm⁻¹ * Z * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹ := by
  have hP := posDef_precision Z Gm Rm hG hR
  have hGd : IsUnit Gm.det := (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have hRd : IsUnit Rm.det := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  have hPd : IsUnit (Zᵀ * Rm⁻¹ * Z + Gm⁻¹).det := (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hRinv : Rm * Rm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRd
  have hGinv : Gm * Gm⁻¹ = 1 := Matrix.mul_nonsing_inv _ hGd
  have hPinv : (Zᵀ * Rm⁻¹ * Z + Gm⁻¹) * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hPd
  refine Matrix.inv_eq_right_inv ?_
  have e1 : (Z * Gm * Zᵀ + Rm) * Rm⁻¹ = Z * Gm * Zᵀ * Rm⁻¹ + 1 := by
    rw [Matrix.add_mul, hRinv]
  have hA : (Z * Gm * Zᵀ + Rm) * (Rm⁻¹ * Z) = Z * Gm * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹) := by
    have f1 : Rm * (Rm⁻¹ * Z) = Z := by rw [← Matrix.mul_assoc, hRinv, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, f1, hGinv, Matrix.mul_one]
  have e2 : (Z * Gm * Zᵀ + Rm)
        * (Rm⁻¹ * Z * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹)
      = Z * Gm * Zᵀ * Rm⁻¹ := by
    calc (Z * Gm * Zᵀ + Rm) * (Rm⁻¹ * Z * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹)
        = ((Z * Gm * Zᵀ + Rm) * (Rm⁻¹ * Z)) * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (Z * Gm * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)) * (Zᵀ * Rm⁻¹ * Z + Gm⁻¹)⁻¹ * Zᵀ * Rm⁻¹ := by
          rw [hA]
      _ = Z * Gm * Zᵀ * Rm⁻¹ := by
          rw [Matrix.mul_assoc (Z * Gm), hPinv, Matrix.mul_one]
  rw [Matrix.mul_sub, e1, e2]
  abel

/-- LEAN-ONLY -/
private theorem measurable_lmmMap (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p)) :
    Measurable fun be : EuclideanSpace ℝ (Fin q) × EuclideanSpace ℝ (Fin n) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) D.X β
        + Matrix.toEuclideanLin (𝕜 := ℝ) D.Z be.1 + be.2 := by
  have h : Measurable fun x : EuclideanSpace ℝ (Fin q) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) D.Z x :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) D.Z).continuous_of_finiteDimensional).measurable
  exact (((h.comp measurable_fst).const_add _).add measurable_snd)

/-- **M5ii, Henderson's mixed-model equations** (Henderson et al. 1959; `SCM §7.6`):
`(β̂, b̂)` solves the MME block system iff `b̂` is the BLUP at `β̂` and `β̂` solves the
GLS normal equations in `V = Z G Zᵀ + R`. -/
theorem hendersonMME (D : LMMDesign n p q) (Gm : Matrix (Fin q) (Fin q) ℝ)
    (Rm : Matrix (Fin n) (Fin n) ℝ)
    -- USER-INPUT: positive-definite variance components; SCM §7.6
    (hG : Gm.PosDef) (hR : Rm.PosDef)
    (βh : Fin p → ℝ) (bh : Fin q → ℝ) (y : Fin n → ℝ) :
    ((D.Xᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Xᵀ * Rm⁻¹ * D.Z) *ᵥ bh = (D.Xᵀ * Rm⁻¹) *ᵥ y
        ∧ (D.Zᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) *ᵥ bh
            = (D.Zᵀ * Rm⁻¹) *ᵥ y)
      ↔ (bh = (Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ (y - D.X *ᵥ βh)
          ∧ (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹ * D.X) *ᵥ βh
              = (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ y) := by
  have hP := posDef_precision D.Z Gm Rm hG hR
  have hPd : IsUnit (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit
  have hPl : (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹)⁻¹ * (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) = 1 :=
    Matrix.nonsing_inv_mul _ hPd
  have hPr : (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) * (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hPd
  have hpt := pushThrough D.Z Gm Rm hG hR
  -- the precision block is injective on vectors
  have hinj : ∀ v : Fin q → ℝ, (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) *ᵥ v = 0 → v = 0 := by
    intro v hv
    have h0 : (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹)⁻¹ *ᵥ ((D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) *ᵥ v) = 0 := by
      rw [hv, Matrix.mulVec_zero]
    rwa [Matrix.mulVec_mulVec, hPl, Matrix.one_mulVec] at h0
  -- the BLUP weight is a left inverse of the precision block against Zᵀ R⁻¹
  have hPW : (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) * (Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹)
      = D.Zᵀ * Rm⁻¹ := by
    rw [hpt, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPr, Matrix.one_mul]
  -- (E2) is exactly the BLUP equation
  have hE2 : ((D.Zᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) *ᵥ bh
          = (D.Zᵀ * Rm⁻¹) *ᵥ y)
      ↔ bh = (Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ (y - D.X *ᵥ βh) := by
    have hstep : ((D.Zᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) *ᵥ bh)
          - (D.Zᵀ * Rm⁻¹) *ᵥ y
        = (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹)
            *ᵥ (bh - (Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ (y - D.X *ᵥ βh)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPW, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec]
      abel
    rw [← sub_eq_zero (a := (D.Zᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Zᵀ * Rm⁻¹ * D.Z + Gm⁻¹) *ᵥ bh),
      hstep, ← sub_eq_zero (a := bh)]
    exact ⟨fun h => hinj _ h, fun h => by rw [h, Matrix.mulVec_zero]⟩
  -- the complement identity turns the `R`-form of the first equation into the `V`-form
  have hkey : D.Xᵀ * Rm⁻¹ * D.Z * (Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹)
      = D.Xᵀ * Rm⁻¹ - D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹ := by
    rw [hpt, inv_marginalCov D.Z Gm Rm hG hR]
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have main : bh = (Gm * D.Zᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ (y - D.X *ᵥ βh) →
      ((D.Xᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Xᵀ * Rm⁻¹ * D.Z) *ᵥ bh = (D.Xᵀ * Rm⁻¹) *ᵥ y
        ↔ (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹ * D.X) *ᵥ βh
            = (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ y) := by
    intro hT1
    have hshape : ((D.Xᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Xᵀ * Rm⁻¹ * D.Z) *ᵥ bh)
          - (D.Xᵀ * Rm⁻¹) *ᵥ y
        = (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹ * D.X) *ᵥ βh
            - (D.Xᵀ * (D.Z * Gm * D.Zᵀ + Rm)⁻¹) *ᵥ y := by
      rw [hT1, Matrix.mulVec_mulVec, hkey, Matrix.sub_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      abel
    rw [← sub_eq_zero (a := (D.Xᵀ * Rm⁻¹ * D.X) *ᵥ βh + (D.Xᵀ * Rm⁻¹ * D.Z) *ᵥ bh),
      hshape, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have hT1 := hE2.mp h2
    exact ⟨hT1, (main hT1).mp h1⟩
  · rintro ⟨hT1, hT2⟩
    exact ⟨(main hT1).mpr hT2, hE2.mpr hT1⟩

/-- **M4, the fixed-effects degeneration**: with a point mass at zero for the latent
effects, the mixed model is the fixed-effects linear model `Y = Xβ + ε` (`LW82`; the
bridge point to the library's linear-model treatments). -/
theorem lmmLaw_dirac (D : LMMDesign n p q) (β : EuclideanSpace ℝ (Fin p))
    (R : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure R] :
    lmmLaw D β (MeasureTheory.Measure.dirac 0) R
      = R.map fun ε => Matrix.toEuclideanLin (𝕜 := ℝ) D.X β + ε := by
  rw [lmmLaw, Measure.dirac_prod,
    Measure.map_map (measurable_lmmMap D β) measurable_prodMk_left]
  congr 1
  funext ε
  simp

end StatLean.StatisticalModels.MixedEffects
