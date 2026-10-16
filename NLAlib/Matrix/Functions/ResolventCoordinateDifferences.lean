import NLAlib.Matrix.Functions.ResolventCoordinateBounds

/-!
# Exact coordinate remainder for the squared resolvent

Affine increments extract one scalar from the first difference and a second
scalar from its derivative remainder. Pairing with normalized trace gives the
six ordered words used by the genuine resampling interpolation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "M" => Matrix n n ℂ
local notation "J" => (n×n) ⊕ (n×n)
local notation "L" => (hermitianMatrixFromRealCoordinates : (J → ℝ) →L[ℝ] M)

/-- Exact affine second remainder, paired with the actual normalized trace.
All reconstructed bases are Hermitian and every direction is an actual real
coordinate vector. Source: the supplied Cauchy-transform six-word identity.
atlas: cauchy-transform-gaussian-universality (partial) -/
theorem hermitianCoordinateTraceProduct_squaredResolvent_affine_remainder
    (ζ : ℂ) (hζ : ζ.im ≠ 0) (x₀ x₁ x₂ d e f : J → ℝ)
    (a : ℝ) (h₀₁ : x₀-x₁ = a • d) (h₁₂ : x₁-x₂ = a • e)
    (h₀₂ : x₀-x₂ = a • f) :
    hermitianCoordinateTraceProduct d
        (hermitianCoordinateSquaredResolvent ζ x₀ - hermitianCoordinateSquaredResolvent ζ x₁) =
      a • hermitianCoordinateTraceProduct d
        (hermitianCoordinateSquaredResolventDerivative ζ x₂ d) +
      a^2 • normalizedTrace (L d *
        (resolventSquareSecondDifference ζ (L x₀) (L x₁) (L x₂) (L d) (L e) +
          resolventSquareSecondDifference ζ (L x₀) (L x₂) (L x₂) (L f) (L d))) := by
  have hA := isHermitian_hermitianMatrixFromRealCoordinates x₀
  have hB := isHermitian_hermitianMatrixFromRealCoordinates x₁
  have hC := isHermitian_hermitianMatrixFromRealCoordinates x₂
  have hAB : L x₀-L x₁ = a • L d := by rw [← map_sub,h₀₁,map_smul]
  have hBC : L x₁-L x₂ = a • L e := by rw [← map_sub,h₁₂,map_smul]
  have hAC : L x₀-L x₂ = a • L f := by rw [← map_sub,h₀₂,map_smul]
  have hsec : hermitianCoordinateSquaredResolvent ζ x₀ - hermitianCoordinateSquaredResolvent ζ x₁ =
      a • resolventSquareDifference ζ (L x₀) (L x₁) (L d) :=
    resolvent_sq_sub_resolvent_sq_of_sub_eq_smul ζ (L x₀) (L x₁) (L d) hA hB hζ a hAB
  have hdiff := resolventSquareDifference_sub_self_of_sub_eq_smul ζ (L x₀) (L x₁) (L x₂)
    (L d) (L e) (L f) hA hB hC hζ a hBC hAC
  have hbase : resolventSquareDifference ζ (L x₀) (L x₁) (L d) =
      hermitianCoordinateSquaredResolventDerivative ζ x₂ d +
        a • (resolventSquareSecondDifference ζ (L x₀) (L x₁) (L x₂) (L d) (L e) +
          resolventSquareSecondDifference ζ (L x₀) (L x₂) (L x₂) (L f) (L d)) := by
    rw [hermitianCoordinateSquaredResolventDerivative_apply ζ hζ]
    exact sub_eq_iff_eq_add'.mp hdiff
  rw [hsec,hbase]
  simp only [map_smul,map_add,smul_add,smul_smul,pow_two,
    hermitianCoordinateTraceProduct_apply,Matrix.mul_add,normalizedTrace_add]

end NLAlib
