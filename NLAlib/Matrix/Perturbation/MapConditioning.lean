import NLAlib.ForMathlib.Analysis.Calculus.Conditioning
import NLAlib.Matrix.Perturbation.ConditionNumber
import NLAlib.Matrix.Perturbation.LeastSquaresGeometry

/-!
# Condition numbers of Euclidean maps

For a differentiable map `f : ℝᵐ → ℝⁿ` the absolute condition number `mapAbsCondition f x`
(`NLAlib.ForMathlib.Analysis.Calculus.Conditioning`) is the spectral norm of the Euclidean
Jacobian (`specNorm_euclideanJacobian`); the componentwise relative condition number is the
spectral norm of the Jacobian scaled by the input and output coordinates
(`mapComponentRelativeCondition`), and the normwise relative condition number of an invertible
linear map `x ↦ A x` is at most the matrix condition number `κ₂(A)`
(`mapNormRelativeCondition_toEuclideanCLM_le_conditionNumber`).
Source: Gautschi 2004, Definitions 2.3–2.6. Atlas: `condition-number-of-map-def`.
-/

noncomputable section

open Matrix

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The Jacobian of `f` at `x` in the standard orthonormal Euclidean bases, through Mathlib's
`Matrix.toEuclideanLin`. Gautschi 2004, Definition 2.3; supports
`condition-number-of-map-def`. -/
def euclideanJacobian (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n)
    (x : EuclideanSpace ℝ m) : Matrix n m ℝ :=
  Matrix.toEuclideanLin.symm (fderiv ℝ f x).toLinearMap

omit [Fintype n] [DecidableEq n] in
/-- The Euclidean Jacobian represents the Fréchet derivative. Gautschi 2004, Definition 2.3. -/
theorem toEuclideanLin_euclideanJacobian
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    (euclideanJacobian f x).toEuclideanLin = (fderiv ℝ f x).toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

omit [DecidableEq n] in
/-- The entries of the Jacobian are the coordinate directional derivatives.
Gautschi 2004, Definition 2.3. -/
theorem euclideanJacobian_apply
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m)
    (i : n) (j : m) :
    euclideanJacobian f x i j = (fderiv ℝ f x (EuclideanSpace.single j 1)) i := by
  change (Matrix.toLpLin (R := ℝ) 2 2).symm (fderiv ℝ f x).toLinearMap i j = _
  simp [Matrix.toLpLin_eq_toLin,
    Matrix.toLin_symm, LinearMap.toMatrix_apply, PiLp.basisFun_apply]

omit [DecidableEq n] in
open scoped Matrix.Norms.L2Operator in
/-- The absolute condition number of a differentiable map is the spectral norm of its
Euclidean Jacobian. Gautschi 2004, Definition 2.3.
atlas: condition-number-of-map-def -/
theorem specNorm_euclideanJacobian {f : EuclideanSpace ℝ m → EuclideanSpace ℝ n}
    {x : EuclideanSpace ℝ m} (hf : DifferentiableAt ℝ f x) :
    specNorm (euclideanJacobian f x) = mapAbsCondition f x := by
  rw [mapAbsCondition_eq_norm_of_hasFDerivAt hf.hasFDerivAt, specNorm, Matrix.l2_opNorm_def]
  simp only [LinearEquiv.trans_apply, toEuclideanLin_euclideanJacobian]
  congr 1

/-- The componentwise relative condition matrix scales the input coordinates by `x` and the
output coordinates by the reciprocal of `f x`. Gautschi 2004, Definition 2.4 (the relative
reading needs nonzero coordinates; the formula is total). -/
def componentRelativeConditionMatrix
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    Matrix n m ℝ :=
  diagonal (fun i => (f x i)⁻¹) * euclideanJacobian f x * diagonal (fun j => x j)

/-- The Euclidean componentwise relative condition number: the spectral norm of the relative
condition matrix. Gautschi 2004, Definition 2.4; its relative reading needs every input and
output coordinate nonzero, and `f` differentiable at `x` (the value is `0` otherwise).
atlas: condition-number-of-map-def -/
def mapComponentRelativeCondition
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) : ℝ :=
  specNorm (componentRelativeConditionMatrix f x)

/-- The local componentwise relative perturbation map: input and output perturbations measured
relative to the coordinates of the base point. Gautschi 2004, Definition 2.4. -/
def componentRelativeMap
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    EuclideanSpace ℝ m → EuclideanSpace ℝ n := fun u =>
  Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (diagonal (fun i => (f x i)⁻¹))
    (f (x + Matrix.toEuclideanCLM (n := m) (𝕜 := ℝ) (diagonal (fun j => x j)) u) - f x)

/-- The derivative at `0` of the scaled relative perturbation map is the componentwise relative
condition matrix. Gautschi 2004, Definition 2.4.
atlas: condition-number-of-map-def -/
theorem hasFDerivAt_componentRelativeMap
    {f : EuclideanSpace ℝ m → EuclideanSpace ℝ n} {x : EuclideanSpace ℝ m}
    (hf : DifferentiableAt ℝ f x) :
    HasFDerivAt (componentRelativeMap f x)
      ((Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
        (componentRelativeConditionMatrix f x)) 0 := by
  let dx := Matrix.toEuclideanCLM (n := m) (𝕜 := ℝ) (diagonal (fun j => x j))
  let dy := Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (diagonal (fun i => (f x i)⁻¹))
  have hin : HasFDerivAt (fun u => x + dx u) dx 0 := dx.hasFDerivAt.const_add x
  have hf₀ : HasFDerivAt f (fderiv ℝ f x) (x + dx 0) := by
    simpa only [map_zero, add_zero] using hf.hasFDerivAt
  have h := dy.hasFDerivAt.comp 0 ((hf₀.comp 0 hin).sub_const (f x))
  have heq : dy.comp ((fderiv ℝ f x).comp dx) =
      (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)
        (componentRelativeConditionMatrix f x) := by
    apply ContinuousLinearMap.coe_injective
    change dy.toLinearMap.comp ((fderiv ℝ f x).toLinearMap.comp dx.toLinearMap) =
      (componentRelativeConditionMatrix f x).toEuclideanLin
    change _ = Matrix.toLpLin 2 2
      (diagonal (fun i => (f x i)⁻¹) * euclideanJacobian f x * diagonal (fun j => x j))
    rw [Matrix.toLpLin_mul 2 2 2, Matrix.toLpLin_mul 2 2 2]
    rw [toEuclideanLin_euclideanJacobian]
    rfl
  rw [heq] at h
  exact h

open scoped Matrix.Norms.L2Operator in
/-- The componentwise relative condition number is the absolute condition number of the scaled
local map at `0`. Gautschi 2004, Definition 2.4.
atlas: condition-number-of-map-def -/
theorem mapComponentRelativeCondition_eq_mapAbsCondition
    {f : EuclideanSpace ℝ m → EuclideanSpace ℝ n} {x : EuclideanSpace ℝ m}
    (hf : DifferentiableAt ℝ f x) :
    mapComponentRelativeCondition f x = mapAbsCondition (componentRelativeMap f x) 0 := by
  rw [mapAbsCondition_eq_norm_of_hasFDerivAt (hasFDerivAt_componentRelativeMap hf),
    mapComponentRelativeCondition, specNorm, Matrix.l2_opNorm_def]

/-- The entries of the relative condition matrix: input coordinate times the partial derivative
divided by the output coordinate. Gautschi 2004, Definition 2.4. -/
theorem componentRelativeConditionMatrix_apply
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m)
    (i : n) (j : m) :
    componentRelativeConditionMatrix f x i j =
      x j * (fderiv ℝ f x (EuclideanSpace.single j 1)) i / f x i := by
  simp only [componentRelativeConditionMatrix, Matrix.mul_diagonal,
    Matrix.diagonal_mul, euclideanJacobian_apply, div_eq_mul_inv]
  ring

/-- The componentwise relative condition number of a differentiable map is bounded by the
diagonal scalings times the absolute condition number (it need not be bounded by the matrix
condition number alone). Gautschi 2004, Definition 2.4.
atlas: condition-number-of-map-def -/
theorem mapComponentRelativeCondition_le_diagonal_scaling
    {f : EuclideanSpace ℝ m → EuclideanSpace ℝ n} {x : EuclideanSpace ℝ m}
    (hf : DifferentiableAt ℝ f x) :
    mapComponentRelativeCondition f x ≤
      specNorm (diagonal (fun i => (f x i)⁻¹)) * mapAbsCondition f x *
        specNorm (diagonal (fun j => x j)) := by
  unfold mapComponentRelativeCondition componentRelativeConditionMatrix
  calc
    _ ≤ specNorm (diagonal (fun i => (f x i)⁻¹) * euclideanJacobian f x) *
        specNorm (diagonal (fun j => x j)) := specNorm_mul_le _ _
    _ ≤ _ := by
      rw [← specNorm_euclideanJacobian hf]
      exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)

/-- The matrix inverse cancels the Euclidean action of an invertible matrix. -/
theorem toEuclideanCLM_inv_apply_apply {A : Matrix n n ℝ} (hA : IsUnit A)
    (x : EuclideanSpace ℝ n) :
    Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A⁻¹ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x) =
      x := by
  have h := congrArg (fun M : Matrix n n ℝ => Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M x)
    (Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA))
  simpa only [map_mul, map_one, mul_apply_eq_comp, one_apply_eq_self] using h

/-- The absolute condition number of the Euclidean action of a matrix is its spectral norm.
Gautschi 2004, Definitions 2.3–2.4. -/
theorem mapAbsCondition_toEuclideanCLM (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    mapAbsCondition (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A) x = specNorm A := by
  rw [mapAbsCondition, ContinuousLinearMap.fderiv]
  rfl

/-- The normwise relative condition number of an invertible linear map `x ↦ A x` is at most the
matrix condition number `κ₂(A)`. Gautschi 2004, Definitions 2.3–2.4; Trefethen–Bau 1997,
Lecture 12.
atlas: condition-number-of-map-def -/
theorem mapNormRelativeCondition_toEuclideanCLM_le_conditionNumber
    {A : Matrix n n ℝ} (hA : IsUnit A) (x : EuclideanSpace ℝ n) :
    mapNormRelativeCondition (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A) x ≤
      (conditionNumber A).toReal := by
  rw [conditionNumber_toReal_of_isUnit hA]
  by_cases hx : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x = 0
  · simp only [mapNormRelativeCondition, hx, norm_zero, div_zero]
    exact mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)
  have hBound : ‖x‖ ≤ specNorm A⁻¹ *
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖ := by
    calc
      ‖x‖ = ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A⁻¹
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x)‖ := by
        rw [toEuclideanCLM_inv_apply_apply hA]
      _ ≤ _ := norm_toEuclideanLin_apply_le A⁻¹ _
  rw [mapNormRelativeCondition, mapAbsCondition_toEuclideanCLM]
  apply (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
  calc
    _ ≤ specNorm A * (specNorm A⁻¹ *
        ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖) :=
      mul_le_mul_of_nonneg_left hBound (specNorm_nonneg A)
    _ = _ := by ring

end NLAlib
