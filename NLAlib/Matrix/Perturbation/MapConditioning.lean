import NLAlib.Matrix.Perturbation.ConditionNumber
import NLAlib.Matrix.Perturbation.LinearSystemPerturbation
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Condition numbers of differentiable maps

Absolute, componentwise relative, and normwise relative condition numbers
use the derivative in their respective perturbation metrics. The matrix
condition number bounds the normwise relative condition of an invertible
linear map. Componentwise relative conditioning has a separate diagonal
scaling bound. Source: Gautschi (2004), Definitions 2.3--2.6;
frontier derivations, Section `psd:map-condition`.
Atlas: `condition-number-of-map-def`.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The absolute condition number is the operator norm of the Fréchet
derivative. Gautschi (2004), Definition 2.3. Mathlib's total derivative is
zero outside the differentiable branch.
atlas: condition-number-of-map-def (partial) -/
def mapAbsCondition (f : E → F) (x : E) : ℝ := ‖fderiv ℝ f x‖

/-- The normwise relative condition number scales absolute conditioning by
the ratio of the input and output norms. Gautschi (2004), Definition 2.4;
interpreted as relative conditioning when both norms are nonzero.
atlas: condition-number-of-map-def (partial) -/
def mapNormRelativeCondition (f : E → F) (x : E) : ℝ :=
  mapAbsCondition f x * ‖x‖ / ‖f x‖

/-- A specified Fréchet derivative computes the absolute condition number.
Gautschi (2004), Definition 2.3; supports `condition-number-of-map-def`. -/
theorem mapAbsCondition_eq_norm_of_hasFDerivAt {f : E → F} {x : E}
    {L : E →L[ℝ] F} (hf : HasFDerivAt f L x) : mapAbsCondition f x = ‖L‖ := by
  rw [mapAbsCondition, hf.fderiv]

/-- In one dimension absolute conditioning is the absolute scalar
derivative. Gautschi (2004), Definition 2.5.
atlas: condition-number-of-map-def (partial) -/
theorem mapAbsCondition_eq_abs_deriv (f : ℝ → ℝ) (x : ℝ) :
    mapAbsCondition f x = |deriv f x| := by
  rw [mapAbsCondition, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]

/-- In one dimension relative conditioning is the absolute logarithmic
derivative, with the usual nonzero input/output interpretation.
Gautschi (2004), Definition 2.6.
atlas: condition-number-of-map-def (partial) -/
theorem mapNormRelativeCondition_eq_abs_mul_deriv_div (f : ℝ → ℝ) (x : ℝ) :
    mapNormRelativeCondition f x = |x * deriv f x / f x| := by
  rw [mapNormRelativeCondition, mapAbsCondition_eq_abs_deriv]
  simp only [Real.norm_eq_abs, abs_div, abs_mul]
  ring

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The Jacobian in the standard orthonormal Euclidean bases, using
Mathlib's matrix/linear-map equivalence. Gautschi (2004), Definitions 2.3--2.6;
supports `condition-number-of-map-def`. -/
def euclideanJacobian (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n)
    (x : EuclideanSpace ℝ m) : Matrix n m ℝ :=
  Matrix.toEuclideanLin.symm (fderiv ℝ f x).toLinearMap

omit [Fintype n] [DecidableEq n] in
/-- The Euclidean Jacobian represents exactly the Fréchet derivative.
Gautschi (2004), Definition 2.3; supports `condition-number-of-map-def`. -/
theorem toEuclideanLin_euclideanJacobian
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    (euclideanJacobian f x).toEuclideanLin = (fderiv ℝ f x).toLinearMap :=
  Matrix.toEuclideanLin.apply_symm_apply _

omit [DecidableEq n] in
/-- Jacobian entries are the coordinate directional derivatives.
Gautschi (2004), Definitions 2.3--2.6;
supports `condition-number-of-map-def`. -/
theorem euclideanJacobian_apply
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m)
    (i : n) (j : m) :
    euclideanJacobian f x i j = (fderiv ℝ f x (EuclideanSpace.single j 1)) i := by
  change (Matrix.toLpLin (R := ℝ) 2 2).symm (fderiv ℝ f x).toLinearMap i j = _
  simp [Matrix.toLpLin_eq_toLin,
    Matrix.toLin_symm, LinearMap.toMatrix_apply, PiLp.basisFun_apply]

/-- The spectral norm of the Euclidean Jacobian is absolute conditioning.
Gautschi (2004), Definition 2.3.
atlas: condition-number-of-map-def (partial) -/
theorem specNorm_euclideanJacobian
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    specNorm (euclideanJacobian f x) = mapAbsCondition f x := by
  rw [specNorm, Matrix.l2_opNorm_def]
  simp only [LinearEquiv.trans_apply, toEuclideanLin_euclideanJacobian, mapAbsCondition]
  congr 1

/-- The componentwise relative condition matrix scales input coordinates by
`x` and output coordinates by the reciprocal of `f x`. Gautschi (2004),
Definition 2.4. The relative metric assumes nonzero coordinates.
atlas: condition-number-of-map-def (partial) -/
def componentRelativeConditionMatrix
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    Matrix n m ℝ :=
  diagonal (fun i => (f x i)⁻¹) * euclideanJacobian f x * diagonal (fun j => x j)

/-- The Euclidean componentwise relative condition number is the spectral
norm of the relative condition matrix. Gautschi (2004), Definition 2.4.
Its relative perturbation interpretation requires every input and output
coordinate to be nonzero; the formula itself is total.
atlas: condition-number-of-map-def (partial) -/
def mapComponentRelativeCondition
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) : ℝ :=
  specNorm (componentRelativeConditionMatrix f x)

/-- The local componentwise relative perturbation map measures changes in
input and output coordinates relative to the base point. Gautschi (2004),
Definition 2.4; supports `condition-number-of-map-def`. -/
def componentRelativeMap
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    EuclideanSpace ℝ m → EuclideanSpace ℝ n := fun u =>
  Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (diagonal (fun i => (f x i)⁻¹))
    (f (x + Matrix.toEuclideanCLM (n := m) (𝕜 := ℝ) (diagonal (fun j => x j)) u) - f x)

/-- The derivative of the scaled relative perturbation map is represented
by the componentwise relative condition matrix. Gautschi (2004), Definition
2.4; frontier derivations `psd:map-condition`.
atlas: condition-number-of-map-def (partial) -/
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

/-- Componentwise relative conditioning is absolute conditioning of the
scaled local map. Gautschi (2004), Definition 2.4;
frontier derivations `psd:map-condition`.
atlas: condition-number-of-map-def (partial) -/
theorem mapComponentRelativeCondition_eq_mapAbsCondition
    {f : EuclideanSpace ℝ m → EuclideanSpace ℝ n} {x : EuclideanSpace ℝ m}
    (hf : DifferentiableAt ℝ f x) :
    mapComponentRelativeCondition f x = mapAbsCondition (componentRelativeMap f x) 0 := by
  rw [mapAbsCondition_eq_norm_of_hasFDerivAt (hasFDerivAt_componentRelativeMap hf),
    mapComponentRelativeCondition, specNorm, Matrix.l2_opNorm_def]

/-- Relative condition entries are input coordinate times the partial
derivative divided by the output coordinate. Gautschi (2004), Definition 2.4.
atlas: condition-number-of-map-def (partial) -/
theorem componentRelativeConditionMatrix_apply
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m)
    (i : n) (j : m) :
    componentRelativeConditionMatrix f x i j =
      x j * (fderiv ℝ f x (EuclideanSpace.single j 1)) i / f x i := by
  simp only [componentRelativeConditionMatrix, Matrix.mul_diagonal,
    Matrix.diagonal_mul, euclideanJacobian_apply, div_eq_mul_inv]
  ring

/-- Componentwise relative conditioning has the direct diagonal scaling
bound, including empty input/output dimensions. Gautschi (2004), Definition
2.4; frontier derivations `psd:map-condition`. This metric need not be
bounded by the matrix condition number alone.
atlas: condition-number-of-map-def (partial) -/
theorem mapComponentRelativeCondition_le_diagonal_scaling
    (f : EuclideanSpace ℝ m → EuclideanSpace ℝ n) (x : EuclideanSpace ℝ m) :
    mapComponentRelativeCondition f x ≤
      specNorm (diagonal (fun i => (f x i)⁻¹)) * mapAbsCondition f x *
        specNorm (diagonal (fun j => x j)) := by
  unfold mapComponentRelativeCondition componentRelativeConditionMatrix
  calc
    _ ≤ specNorm (diagonal (fun i => (f x i)⁻¹) * euclideanJacobian f x) *
        specNorm (diagonal (fun j => x j)) := specNorm_mul_le _ _
    _ ≤ _ := by
      rw [← specNorm_euclideanJacobian]
      exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)

/-- The absolute condition number of a matrix's Euclidean action is its
spectral norm. Gautschi (2004), Definitions 2.3--2.4.
atlas: condition-number-of-map-def (partial) -/
theorem mapAbsCondition_toEuclideanCLM (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    mapAbsCondition (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A) x = specNorm A := by
  rw [mapAbsCondition, ContinuousLinearMap.fderiv]
  rfl

/-- Normwise relative conditioning of an invertible linear map is bounded
by its matrix condition number. Gautschi (2004), Definitions 2.3--2.4;
frontier derivations `psd:map-condition`.
atlas: condition-number-of-map-def (partial) -/
theorem mapNormRelativeCondition_toEuclideanCLM_le_conditionNumber
    (A : Matrix n n ℝ) (hA : IsUnit A) (x : EuclideanSpace ℝ n) :
    mapNormRelativeCondition (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A) x ≤
      conditionNumber A := by
  by_cases hx : Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x = 0
  · simp only [mapNormRelativeCondition, hx, norm_zero, div_zero]
    exact conditionNumber_nonneg A
  have hBound : ‖x‖ ≤ specNorm A⁻¹ *
      ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖ := by
    calc
      ‖x‖ = ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A⁻¹
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x)‖ := by
        rw [toEuclideanCLM_inv_apply_apply hA]
      _ ≤ _ := norm_toEuclideanCLM_apply_le _ _
  rw [mapNormRelativeCondition, mapAbsCondition_toEuclideanCLM,
    conditionNumber_eq_mul_specNorm_inv hA]
  apply (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr
  calc
    _ ≤ specNorm A * (specNorm A⁻¹ *
        ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A x‖) :=
      mul_le_mul_of_nonneg_left hBound (specNorm_nonneg A)
    _ = _ := by ring

/-- The map-conditioning contract combines derivative norms, coordinate
relative derivatives, scalar formulas, and the valid bounds for both
relative perturbation metrics. Gautschi (2004), Definitions 2.3--2.6;
frontier derivations `psd:map-condition`. The matrix-condition-number bound
applies to the normwise relative metric; the coordinate metric has the
displayed separate diagonal scaling bound.
atlas: condition-number-of-map-def -/
theorem map_conditioning_characterizations
    {f : EuclideanSpace ℝ m → EuclideanSpace ℝ n} {x : EuclideanSpace ℝ m}
    (hf : DifferentiableAt ℝ f x) :
    specNorm (euclideanJacobian f x) = ‖fderiv ℝ f x‖ ∧
    (∀ i j, componentRelativeConditionMatrix f x i j =
      x j * (fderiv ℝ f x (EuclideanSpace.single j 1)) i / f x i) ∧
    mapComponentRelativeCondition f x = mapAbsCondition (componentRelativeMap f x) 0 ∧
    mapComponentRelativeCondition f x ≤
      specNorm (diagonal (fun i => (f x i)⁻¹)) * mapAbsCondition f x *
        specNorm (diagonal (fun j => x j)) ∧
    (∀ g : ℝ → ℝ, ∀ y : ℝ, mapAbsCondition g y = |deriv g y| ∧
      mapNormRelativeCondition g y = |y * deriv g y / g y|) ∧
    (∀ A : Matrix n n ℝ, IsUnit A → ∀ y : EuclideanSpace ℝ n,
      mapNormRelativeCondition (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A) y ≤
        conditionNumber A) :=
  ⟨specNorm_euclideanJacobian f x, componentRelativeConditionMatrix_apply f x,
    mapComponentRelativeCondition_eq_mapAbsCondition hf,
    mapComponentRelativeCondition_le_diagonal_scaling f x,
    fun g y => ⟨mapAbsCondition_eq_abs_deriv g y,
      mapNormRelativeCondition_eq_abs_mul_deriv_div g y⟩,
    fun A hA y => mapNormRelativeCondition_toEuclideanCLM_le_conditionNumber A hA y⟩

end NLAlib
