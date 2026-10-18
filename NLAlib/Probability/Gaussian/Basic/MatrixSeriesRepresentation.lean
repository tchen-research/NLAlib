import NLAlib.Probability.Gaussian.Basic.CovarianceRepresentation
import NLAlib.Matrix.Functions.HermitianCoordinates
import Mathlib.Algebra.BigOperators.Pi

/-!
# Real scalar series realization of Hermitian Gaussian laws

Every centered Hermitian Gaussian matrix law, including singular covariance,
is an actual finite linear image of independent standard real Gaussian
coordinates. The coefficient matrices are Hermitian by construction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

open scoped Matrix.Norms.L2Operator in
set_option backward.isDefEq.respectTransparency false in
/-- Every centered almost surely Hermitian Gaussian matrix law is the actual
pushforward of independent standard real Gaussians under a finite Hermitian
matrix series. The full real-entry coordinate index provides a canonical
finite dimension, without assuming a nonsingular covariance or nonempty matrix.
This realizes general Hermitian Gaussian laws in the scalar-series interface. -/
theorem exists_hermitian_gaussian_series_representation {n : Type*}
    [Fintype n] [DecidableEq n] (μ : Measure (Matrix n n ℂ)) [IsGaussian μ]
    (hmean : (∫ A, A ∂μ) = 0) (hHerm : ∀ᵐ A ∂μ, A.IsHermitian) :
    ∃ A : ((n × n) ⊕ (n × n)) → Matrix n n ℂ,
      (∀ i, (A i).IsHermitian) ∧
      μ = (gaussianVector ((n × n) ⊕ (n × n))).map
        (fun x => ∑ i, x i • A i) := by
  let C := matrixRealCoordinatesContinuousLinearEquiv (m := n) (n := n)
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : (n × n) ⊕ (n × n) => ℝ)
  let T := C.trans e.symm
  let μE := μ.map T
  have : IsGaussian μE := inferInstanceAs (IsGaussian (μ.map T.toContinuousLinearMap))
  have hμE : (∫ x, x ∂μE) = 0 := by
    rw [show (∫ x, x ∂μE) = T (∫ A, A ∂μ) from T.integral_id_map (μ := μ)]
    rw [hmean, map_zero]
  let S := CFC.sqrt (gaussianCovarianceMatrix μE)
  let P := hermitianMatrixFromRealCoordinates (n := n)
  let Q := P.comp e.toContinuousLinearMap
  have hback : μE.map Q = μ := by
    change (μ.map T).map Q = μ
    rw [Measure.map_map Q.continuous.measurable T.continuous.measurable]
    have heq : Q ∘ T =ᵐ[μ] id := by
      filter_upwards [hHerm] with A hA
      change P (e (e.symm (C A))) = A
      rw [e.apply_symm_apply]
      exact hermitianMatrixFromRealCoordinates_matrixRealCoordinates hA
    rw [Measure.map_congr heq, Measure.map_id]
  have hrep : μ = (gaussianVector ((n × n) ⊕ (n × n))).map
      (fun x => P (S *ᵥ x)) := by
    rw [← hback, gaussian_eq_map_gaussianVector_sqrt_covariance_of_centered μE hμE]
    rw [Measure.map_map Q.continuous.measurable (by fun_prop)]
    rfl
  let L := P.comp S.mulVecLin.toContinuousLinearMap
  let A : ((n × n) ⊕ (n × n)) → Matrix n n ℂ := fun i => L (Pi.single i 1)
  refine ⟨A, ?_, ?_⟩
  · intro i
    exact isHermitian_hermitianMatrixFromRealCoordinates _
  · rw [hrep]
    congr 1
    funext x
    change L x = ∑ i, x i • L (Pi.single i 1)
    simpa only [map_sum, map_smul] using congrArg L (pi_eq_sum_univ' x)

end NLAlib
