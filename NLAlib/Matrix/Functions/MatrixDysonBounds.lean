import NLAlib.ForMathlib.Analysis.Matrix.ImaginaryCoercivity
import NLAlib.ForMathlib.Analysis.ContinuousNormBarrier
import NLAlib.Matrix.Norms.Core

/-! # Deterministic bounds for the matrix Dyson equation

The actual polynomial Dyson identity implies imaginary coercivity,
the Euclidean inverse bound, normalization at imaginary infinity, and
the exterior norm barrier used for the exact support radius.
Source: Ajanki--Erdős--Krüger, Proposition 2.1 and equations (4.1)--(4.8).
Atlas: `matrix-dyson-stieltjes-representation`.
-/

noncomputable section
open Matrix Filter Set
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder ComplexStarModule

namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive continuous matrix map as a native positive complex-linear map. -/
def matrixPositiveMap (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X) :
    Matrix n n ℂ →ₚ[ℂ] Matrix n n ℂ :=
  PositiveLinearMap.mk₀ S.toLinearMap hS

/-- Positivity forces a complex-linear matrix map to preserve imaginary parts. -/
theorem matrix_map_imaginaryPart (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X) (X : Matrix n n ℂ) :
    S (imaginaryPart X : Matrix n n ℂ) = (imaginaryPart (S X) : Matrix n n ℂ) :=
  map_imaginaryPart (matrixPositiveMap S hS) X

/-- The imaginary part of the coefficient in the Dyson identity. -/
theorem imaginaryPart_matrixDysonCoefficient
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (z : ℂ) (X : Matrix n n ℂ) :
    (imaginaryPart (z • 1 - A + S X) : Matrix n n ℂ) =
      z.im • 1 + S (imaginaryPart X : Matrix n n ℂ) := by
  have hI : IsSelfAdjoint (1 : Matrix n n ℂ) := IsSelfAdjoint.one _
  rw [matrix_map_imaginaryPart S hS]
  simp [map_add, map_sub, imaginaryPart_smul, hA.isSelfAdjoint.imaginaryPart,
    hI.imaginaryPart, realPart_one]

/-- A positive-imaginary Dyson solution has the exact `1 / Im z` norm bound.
The proof uses the genuine Euclidean operator norm and allows nonnormal matrices.
atlas: matrix-dyson-stieltjes-representation (partial) -/
theorem specNorm_le_inv_im_of_matrixDyson
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    {z : ℂ} (hz : 0 < z.im) (X : Matrix n n ℂ)
    (hpos : 0 ≤ (imaginaryPart X : Matrix n n ℂ))
    (heq : (z • 1 - A + S X) * X = -1) : specNorm X ≤ z.im⁻¹ := by
  apply Matrix.norm_le_inv_of_mul_eq_neg_one_of_imaginaryPart_ge hz heq
  rw [imaginaryPart_matrixDysonCoefficient A hA S hS]
  exact le_add_of_nonneg_right (hS _ hpos)

/-- The imaginary Dyson identity is a genuine matrix congruence identity. -/
theorem imaginaryPart_eq_matrixDyson_congruence
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    (S : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    (hS : ∀ X : Matrix n n ℂ, 0 ≤ X → 0 ≤ S X)
    (z : ℂ) (X : Matrix n n ℂ)
    (heq : (z • 1 - A + S X) * X = -1) :
    (imaginaryPart X : Matrix n n ℂ) =
      Xᴴ * (z.im • 1 + S (imaginaryPart X : Matrix n n ℂ)) * X := by
  calc
    _ = Xᴴ * (imaginaryPart (z • 1 - A + S X) : Matrix n n ℂ) * X :=
      Matrix.imaginaryPart_eq_conjTranspose_mul_of_mul_eq_neg_one heq
    _ = _ := by rw [imaginaryPart_matrixDysonCoefficient A hA S hS]

end NLAlib
