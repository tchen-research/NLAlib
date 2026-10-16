import NLAlib.Matrix.Functions.KTransformCalculus
import NLAlib.Matrix.Functions.GeometricMeanIdentities

/-! # Whitening the actual K-transform resolvent -/
noncomputable section
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The actual Hermitian congruence variable in K-transform stability. -/
def matrixKWhitened (S T : Matrix n n ℂ) : Matrix n n ℂ :=
  cfc Real.sqrt S * T * cfc Real.sqrt S

/-- The source's actual rational Hermitian coefficient. -/
def matrixKCoefficient (S T : Matrix n n ℂ) : Matrix n n ℂ :=
  matrixKWhitened S T * (1 + matrixKWhitened S T)⁻¹

/-- The strict source gap makes the actual solved denominator invertible. -/
theorem isUnit_matrixKDenominator (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : (S⁻¹ + T).PosDef) : IsUnit (1 + S * T) := by
  have he : 1 + S * T = S * (S⁻¹ + T) := by
    rw [Matrix.mul_add, Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)]
  rw [he]
  exact hS.isUnit.mul hgap.isUnit

/-- Whitening turns the support gap into positivity of the actual `I+Z`. -/
theorem posDef_one_add_matrixKWhitened (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hgap : (S⁻¹ + T).PosDef) : (1 + matrixKWhitened S T).PosDef := by
  let Q := cfc Real.sqrt S
  let R := cfc (fun x => (Real.sqrt x)⁻¹) S
  have hQR : Q * R = 1 := cfc_sqrt_mul_inv_sqrt hS
  have hRQ : R * Q = 1 := cfc_inv_sqrt_mul_sqrt hS
  have hQi : IsUnit Q := ⟨⟨Q,R,hQR,hRQ⟩,rfl⟩
  have hQ : Q.IsHermitian := cfc_predicate _ _
  have hInv : S⁻¹ = R * R := inv_eq_cfc_inv_sqrt_mul_self hS
  have he : 1 + matrixKWhitened S T = Q * (S⁻¹ + T) * Qᴴ := by
    rw [hQ.eq, Matrix.mul_add, Matrix.add_mul, hInv]
    change 1 + Q * T * Q = Q * (R * R) * Q + Q * T * Q
    rw [← Matrix.mul_assoc, hQR, Matrix.one_mul, hRQ]
  rw [he]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hQi).mpr hgap

/-- The actual coefficient is Hermitian at every source-admissible Hermitian
sample, even when the sample is indefinite. -/
theorem isHermitian_matrixKCoefficient (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hT : T.IsHermitian) (hgap : (S⁻¹ + T).PosDef) : (matrixKCoefficient S T).IsHermitian := by
  have hZ : (matrixKWhitened S T).IsHermitian := by
    have hQ : (cfc Real.sqrt S).IsHermitian := cfc_predicate _ _
    simp only [matrixKWhitened, Matrix.IsHermitian, Matrix.conjTranspose_mul, hQ.eq, hT.eq,
      Matrix.mul_assoc]
  have hP := posDef_one_add_matrixKWhitened S T hS hgap
  have he : matrixKCoefficient S T = 1 - (1 + matrixKWhitened S T)⁻¹ := by
    unfold matrixKCoefficient
    have hZeq : matrixKWhitened S T = (1 + matrixKWhitened S T) - 1 := by abel
    calc
      _ = ((1 + matrixKWhitened S T) - 1) * (1 + matrixKWhitened S T)⁻¹ := by rw [← hZeq]
      _ = _ := by
        rw [Matrix.sub_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit), Matrix.one_mul]
  rw [he]
  exact Matrix.isHermitian_one.sub hP.inv.isHermitian

/-- The genuine resolvent equals the inverse-square-root congruence of the
source's actual coefficient. Source: user derivations, equation (F21).
atlas: matrix-k-transform-stability (partial) -/
theorem matrixKResolvent_eq_inv_sqrt_congruence (S T : Matrix n n ℂ) (hS : S.PosDef) :
    matrixKResolvent S T = cfc (fun x => (Real.sqrt x)⁻¹) S * matrixKCoefficient S T *
      cfc (fun x => (Real.sqrt x)⁻¹) S := by
  let Q := cfc Real.sqrt S
  let R := cfc (fun x => (Real.sqrt x)⁻¹) S
  let Z := matrixKWhitened S T
  have hQR : Q * R = 1 := cfc_sqrt_mul_inv_sqrt hS
  have hRQ : R * Q = 1 := cfc_inv_sqrt_mul_sqrt hS
  have hQQ : Q * Q = S := cfc_sqrt_mul_self hS
  have hden : 1 + S * T = Q * (1 + Z) * R := by
    dsimp only [Z, matrixKWhitened]
    change 1 + S * T = Q * (1 + Q * T * Q) * R
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
    have hz : Q * (Q * T * Q) * R = S * T := by
      calc
        _ = (Q * Q) * T * (Q * R) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQQ,hQR,Matrix.mul_one]
    rw [hQR,hz]
  have hQi : Q⁻¹ = R := Matrix.inv_eq_right_inv hQR
  have hRi : R⁻¹ = Q := Matrix.inv_eq_right_inv hRQ
  unfold matrixKResolvent
  rw [hden, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hQi,hRi]
  change T * (Q * ((1+Z)⁻¹ * R)) = R * (Z * (1+Z)⁻¹) * R
  have hRZ : R * Z = T * Q := by
    change R * (Q * T * Q) = T * Q
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRQ, Matrix.one_mul]
  rw [← Matrix.mul_assoc R Z, hRZ]
  simp only [Matrix.mul_assoc]

/-- The actual resolvent is Hermitian under precisely the source's support
gap, so its two push-through expressions agree. -/
theorem isHermitian_matrixKResolvent (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hT : T.IsHermitian) (hgap : (S⁻¹ + T).PosDef) : (matrixKResolvent S T).IsHermitian := by
  rw [matrixKResolvent_eq_inv_sqrt_congruence S T hS]
  have hR : (cfc (fun x => (Real.sqrt x)⁻¹) S).IsHermitian := cfc_predicate _ _
  have hC := isHermitian_matrixKCoefficient S T hS hT hgap
  simp only [Matrix.IsHermitian, Matrix.conjTranspose_mul, hR.eq,hC.eq,Matrix.mul_assoc]

/-- The right inverse expression in the source is the same actual resolvent. -/
theorem matrixKResolvent_eq_right (S T : Matrix n n ℂ) (hS : S.PosDef)
    (hT : T.IsHermitian) (hgap : (S⁻¹ + T).PosDef) :
    matrixKResolvent S T = (1 + T * S)⁻¹ * T := by
  have hR := (isHermitian_matrixKResolvent S T hS hT hgap).eq
  simpa only [matrixKResolvent, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.conjTranspose_add, Matrix.conjTranspose_one,hT.eq,hS.isHermitian.eq] using hR.symm

/-- The source's compactly supported Hermitian law and strict support-only
gaps give the actual Fréchet derivative. Uniform neighbourhood and domination
are proved from compactness, not added as hypotheses.
atlas: matrix-k-transform-stability (partial) -/
theorem hasFDerivAt_matrixKTransform_of_posDef
    (ν : MeasureTheory.Measure (selfAdjoint (Matrix n n ℂ))) [MeasureTheory.IsProbabilityMeasure ν]
    (hν : IsCompact ν.support) (α : ℝ) (S : selfAdjoint (Matrix n n ℂ))
    (hS : S.val.PosDef) (hgap : ∀ T ∈ ν.support, (S.val⁻¹ + T.val).PosDef) :
    HasFDerivAt (matrixKTransform ν α) (matrixKTransformDeriv ν α S.val) S.val :=
  hasFDerivAt_matrixKTransform ν hν α S.val hS.isUnit
    (fun T hT => isUnit_matrixKDenominator S.val T.val hS (hgap T hT))

end NLAlib
