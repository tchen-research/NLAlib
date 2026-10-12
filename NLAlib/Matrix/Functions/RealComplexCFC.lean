import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Real matrix functional calculus through the complex embedding

The entrywise real-to-complex star algebra homomorphism preserves and reflects
Loewner order, and commutes with the continuous functional calculus on real
symmetric matrices. Dimensions are unchanged. Supports `loewner-heinz-real`;
source: operator derivations, Section `root:heinz`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Entrywise complexification as a real star algebra homomorphism.
Source: the canonical scalar embedding; supports `loewner-heinz-real`. -/
def realMatrixComplexification : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Complex.ofRealAm.mapMatrix with
    map_star' := by intro A; ext i j; simp }

/-- The embedding acts on each matrix entry by the canonical real scalar map.
Source: the canonical scalar embedding; supports `loewner-heinz-real`. -/
@[simp] theorem realMatrixComplexification_apply (A : Matrix n n ℝ) :
    realMatrixComplexification A = A.map Complex.ofReal := rfl

/-- Complexification preserves and reflects positive semidefiniteness.
Source: the quadratic form on embedded real vectors and star-order preservation;
supports `loewner-heinz-real`. -/
theorem posSemidef_realMatrixComplexification_iff (A : Matrix n n ℝ) :
    (realMatrixComplexification A).PosSemidef ↔ A.PosSemidef := by
  constructor
  · intro hA
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · exact (Matrix.isHermitian_map_iff (fun x => by simp)
        Complex.ofReal_injective).mp hA.isHermitian
    · intro x
      have h := hA.re_dotProduct_nonneg (fun i => (x i : ℂ))
      simpa [Matrix.mulVec, dotProduct, realMatrixComplexification_apply] using h
  · intro hA
    apply Matrix.nonneg_iff_posSemidef.mp
    have h : realMatrixComplexification (0 : Matrix n n ℝ) ≤ realMatrixComplexification A :=
      map_rel (realMatrixComplexification (n := n)) hA.nonneg
    rw [realMatrixComplexification_apply, realMatrixComplexification_apply] at h
    have hZero : (0 : Matrix n n ℝ).map Complex.ofReal = 0 := by ext i j; simp
    rw [hZero] at h
    exact h

/-- Complexification preserves and reflects Loewner inequalities.
Source: the positive-semidefinite difference criterion; supports `loewner-heinz-real`. -/
theorem realMatrixComplexification_le_iff (A B : Matrix n n ℝ) :
    realMatrixComplexification A ≤ realMatrixComplexification B ↔ A ≤ B := by
  rw [Matrix.le_iff, ← map_sub, posSemidef_realMatrixComplexification_iff, Matrix.le_iff]

/-- The entrywise complexification is continuous in the matrix norm.
Source: finite-dimensional real linearity; supports `loewner-heinz-real`. -/
theorem continuous_realMatrixComplexification :
    Continuous (realMatrixComplexification : Matrix n n ℝ → Matrix n n ℂ) :=
  realMatrixComplexification.toLinearMap.continuous_of_finiteDimensional

/-- Every scalar functional calculus of a real symmetric matrix commutes with
complexification. Its finite spectrum makes every scalar function continuous
on the spectrum. Source: Mathlib `StarAlgHom.map_cfc`; supports `loewner-heinz-real`. -/
theorem realMatrixComplexification_cfc (f : ℝ → ℝ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    realMatrixComplexification (cfc f A) = cfc f (realMatrixComplexification A) := by
  exact realMatrixComplexification.map_cfc f A
    (A.finite_real_spectrum.continuousOn f) continuous_realMatrixComplexification hA
    (hA.map Complex.ofReal (fun x => by simp))

/-- Complexification preserves positive definiteness, including empty dimensions.
Source: positivity and preservation of units; supports `loewner-heinz-real`. -/
theorem posDef_realMatrixComplexification {A : Matrix n n ℝ} (hA : A.PosDef) :
    (realMatrixComplexification A).PosDef := by
  apply (posSemidef_realMatrixComplexification_iff A).mpr hA.posSemidef |>.posDef_iff_isUnit.mpr
  exact hA.isUnit.map realMatrixComplexification

/-- Complexification commutes with the ordinary inverse on nonsingular matrices.
Source: preservation of the two inverse identities; supports `loewner-heinz-real`. -/
theorem realMatrixComplexification_inv {A : Matrix n n ℝ} (hA : IsUnit A) :
    realMatrixComplexification A⁻¹ = (realMatrixComplexification A)⁻¹ := by
  have hAc : IsUnit (realMatrixComplexification A) := hA.map realMatrixComplexification
  have hCancel : realMatrixComplexification A * realMatrixComplexification A⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA), map_one]
  calc
    realMatrixComplexification A⁻¹ =
        (realMatrixComplexification A)⁻¹ *
          (realMatrixComplexification A * realMatrixComplexification A⁻¹) := by
      rw [← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hAc), Matrix.one_mul]
    _ = (realMatrixComplexification A)⁻¹ := by rw [hCancel, Matrix.mul_one]

end NLAlib
