import NLAlib.Matrix.Spectral.Core
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Loewner--Heinz and logarithm order on real matrices

Transport the complex C-star algebra results through the actual real matrix
functional calculus. Exponent zero uses the unital calculus and includes
singular matrices. Source: Bhatia, Theorem V.1.9 and Proposition V.1.6;
operator derivations, Section `root:heinz`. Atlas: `loewner-heinz-real`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {n : Type*}

/-- Increasing a positive definite matrix in Loewner order preserves positive
definiteness. Bhatia, Chapter V; supports `loewner-heinz-real`. -/
theorem posDef_of_posDef_le {A B : Matrix n n ℝ} (hA : A.PosDef) (hAB : A ≤ B) :
    B.PosDef := by
  have h := hA.add_posSemidef (Matrix.le_iff.mp hAB)
  have hEq : A + (B - A) = B := by abel
  rw [hEq] at h
  exact h

variable [Fintype n] [DecidableEq n]

/-- The Loewner--Heinz inequality for the actual real symmetric functional
calculus, including both exponents zero and one. Bhatia, Theorem V.1.9.
atlas: loewner-heinz-real (partial) -/
theorem cfc_rpow_le_cfc_rpow {A B : Matrix n n ℝ} (hA : A.PosSemidef)
    (hAB : A ≤ B) {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    cfc (fun x : ℝ => x ^ r) A ≤ cfc (fun x : ℝ => x ^ r) B := by
  have hB : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hA.nonneg.trans hAB)
  have hAc : 0 ≤ (realMatrixComplexification (𝕜 := ℂ)) A :=
    (((posSemidef_realMatrixComplexification_iff (𝕜 := ℂ)) A).mpr hA).nonneg
  have hBc : 0 ≤ (realMatrixComplexification (𝕜 := ℂ)) B :=
    (((posSemidef_realMatrixComplexification_iff (𝕜 := ℂ)) B).mpr hB).nonneg
  apply ((realMatrixComplexification_le_iff (𝕜 := ℂ)) _ _).mp
  rw [(realMatrixComplexification_cfc (𝕜 := ℂ)) _ hA.isHermitian,
    (realMatrixComplexification_cfc (𝕜 := ℂ)) _ hB.isHermitian]
  simpa only [CFC.rpow_eq_cfc_real hAc, CFC.rpow_eq_cfc_real hBc] using
    (CFC.rpow_le_rpow hr (((realMatrixComplexification_le_iff (𝕜 := ℂ)) A B).mpr hAB))

/-- Inversion reverses Loewner order on positive definite real matrices.
Bhatia, Proposition V.1.6.
atlas: loewner-heinz-real (partial) -/
theorem inv_le_inv_of_posDef {A B : Matrix n n ℝ} (hA : A.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hAc := (posDef_realMatrixComplexification (𝕜 := ℂ)) hA
  have hABc := ((realMatrixComplexification_le_iff (𝕜 := ℂ)) A B).mpr hAB
  have hB : IsUnit B := (posDef_of_posDef_le hA hAB).isUnit
  apply ((realMatrixComplexification_le_iff (𝕜 := ℂ)) _ _).mp
  rw [(realMatrixComplexification_inv (𝕜 := ℂ)) hB, (realMatrixComplexification_inv (𝕜 := ℂ)) hA.isUnit]
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    CStarAlgebra.ringInverse_le_ringInverse hABc hAc.isStrictlyPositive

/-- The logarithm is operator monotone for positive definite real matrices.
Bhatia, Proposition V.1.6.
atlas: loewner-heinz-real (partial) -/
theorem cfc_log_le_cfc_log {A B : Matrix n n ℝ} (hA : A.PosDef) (hAB : A ≤ B) :
    cfc Real.log A ≤ cfc Real.log B := by
  have hB : B.PosDef := posDef_of_posDef_le hA hAB
  apply ((realMatrixComplexification_le_iff (𝕜 := ℂ)) _ _).mp
  rw [(realMatrixComplexification_cfc (𝕜 := ℂ)) _ hA.isHermitian,
    (realMatrixComplexification_cfc (𝕜 := ℂ)) _ hB.isHermitian]
  exact CFC.log_le_log (((realMatrixComplexification_le_iff (𝕜 := ℂ)) A B).mpr hAB)
    ((posDef_realMatrixComplexification (𝕜 := ℂ)) hA).isStrictlyPositive

/-- Operator concavity of every real power between zero and one on the real
positive-semidefinite cone. Bhatia, Theorem V.1.9.
atlas: loewner-heinz-real (partial) -/
theorem concaveOn_cfc_rpow {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    ConcaveOn ℝ {A : Matrix n n ℝ | A.PosSemidef}
      (fun A => cfc (fun x : ℝ => x ^ r) A) := by
  constructor
  · intro A hA B hB a b ha hb _
    exact Matrix.nonneg_iff_posSemidef.mp
      (add_nonneg (smul_nonneg ha hA.nonneg) (smul_nonneg hb hB.nonneg))
  · intro A hA B hB a b ha hb hab
    have hAc : 0 ≤ (realMatrixComplexification (𝕜 := ℂ)) A :=
      (((posSemidef_realMatrixComplexification_iff (𝕜 := ℂ)) A).mpr hA).nonneg
    have hBc : 0 ≤ (realMatrixComplexification (𝕜 := ℂ)) B :=
      (((posSemidef_realMatrixComplexification_iff (𝕜 := ℂ)) B).mpr hB).nonneg
    have hC : (a • A + b • B).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
      (add_nonneg (smul_nonneg ha hA.nonneg) (smul_nonneg hb hB.nonneg))
    have hCC : 0 ≤ a • (realMatrixComplexification (𝕜 := ℂ)) A + b • (realMatrixComplexification (𝕜 := ℂ)) B :=
      add_nonneg (smul_nonneg ha hAc) (smul_nonneg hb hBc)
    have hEmbedding : (realMatrixComplexification (𝕜 := ℂ)) (a • A + b • B) =
        a • (realMatrixComplexification (𝕜 := ℂ)) A + b • (realMatrixComplexification (𝕜 := ℂ)) B := by
      rw [map_add, map_smul, map_smul]
    have h := (CFC.concaveOn_rpow (A := Matrix n n ℂ) hr).2 hAc hBc ha hb hab
    dsimp only at h
    rw [CFC.rpow_eq_cfc_real hAc, CFC.rpow_eq_cfc_real hBc,
      CFC.rpow_eq_cfc_real hCC, ← hEmbedding] at h
    apply ((realMatrixComplexification_le_iff (𝕜 := ℂ)) _ _).mp
    rw [map_add, map_smul, map_smul, (realMatrixComplexification_cfc (𝕜 := ℂ)) _ hA.isHermitian,
      (realMatrixComplexification_cfc (𝕜 := ℂ)) _ hB.isHermitian,
      (realMatrixComplexification_cfc (𝕜 := ℂ)) _ hC.isHermitian]
    exact h

/-- Full real Loewner--Heinz contract: monotonicity and concavity on the PSD
cone and inverse/log order on the positive-definite cone. Powers are the
actual real scalar functional calculus and exponent zero is unital.
Bhatia, Theorem V.1.9 and Proposition V.1.6.
atlas: loewner-heinz-real -/
theorem loewner_heinz_real {r : ℝ} (hr : r ∈ Set.Icc 0 1) :
    MonotoneOn (fun A : Matrix n n ℝ => cfc (fun x : ℝ => x ^ r) A)
      {A | A.PosSemidef} ∧
    ConcaveOn ℝ {A : Matrix n n ℝ | A.PosSemidef}
      (fun A => cfc (fun x : ℝ => x ^ r) A) ∧
    (∀ A B : Matrix n n ℝ, A.PosDef → A ≤ B →
      B⁻¹ ≤ A⁻¹ ∧ cfc Real.log A ≤ cfc Real.log B) := by
  refine ⟨fun A hA B _ hAB => cfc_rpow_le_cfc_rpow hA hAB hr,
    concaveOn_cfc_rpow hr, ?_⟩
  intro A B hA hAB
  exact ⟨inv_le_inv_of_posDef hA hAB, cfc_log_le_cfc_log hA hAB⟩

end NLAlib
