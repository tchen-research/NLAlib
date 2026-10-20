import NLAlib.Matrix.Functions.KTransformCongruenceOrder

/-!
# Weighted inverse squares along positive rays

Whitening the positive direction reduces the actual inverse quadratic
comparison to scalar shifts of a positive matrix. Squaring before applying
inverse order avoids the false general operator-monotonicity of inverse
squares. Source: Montanari--Saeed (2026), Lemma 9, equations (149)--(151).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem invSquare_scalarShift_le (Q : Matrix n n ℂ) (hQ : Q.PosDef)
    {t : ℝ} (ht : 0 ≤ t) :
    (Q+t•1)⁻¹*(Q+t•1)⁻¹ ≤ Q⁻¹*Q⁻¹ := by
  have hQ2 : (Q*Q).PosDef := by
    apply (show (Q*Q).PosSemidef by
      simpa only [hQ.isHermitian.eq] using Matrix.posSemidef_conjTranspose_mul_self Q).posDef_iff_isUnit.mpr
    exact hQ.isUnit.mul hQ.isUnit
  have he : (Q+t•1)*(Q+t•1)-Q*Q = (2*t)•Q+(t*t)•(1 : Matrix n n ℂ) := by
    simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,Matrix.one_mul]
    module
  have hle : Q*Q ≤ (Q+t•1)*(Q+t•1) := by
    apply Matrix.le_iff.mpr
    rw [he]
    exact (hQ.posSemidef.smul (by positivity : 0 ≤ 2*t)).add
      (Matrix.PosSemidef.one.smul (mul_nonneg ht ht))
  simpa only [← Matrix.nonsing_inv_eq_ringInverse,Matrix.mul_inv_rev] using
    CStarAlgebra.ringInverse_le_ringInverse hle hQ2.isStrictlyPositive

/-- Along a positive definite direction, the actual weighted inverse square
decreases in Loewner order. The direction need not commute with the base.
Source: Montanari--Saeed (2026), Lemma 9, equations (149)--(151).
atlas: block-wishart-variational-edges (partial) -/
theorem inv_mul_weight_inv_add_smul_le (A B : Matrix n n ℂ)
    (hA : A.PosDef) (hB : B.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    (A+t•B)⁻¹*B*(A+t•B)⁻¹ ≤ A⁻¹*B*A⁻¹ := by
  let R := cfc (fun x => (Real.sqrt x)⁻¹) B
  let V := cfc Real.sqrt B
  let Q := R*A*R
  have hQ : Q.PosDef := (posDef_invSqrt_congruence_iff B hB A).mpr hA
  have hR : R.IsHermitian := cfc_predicate _ _
  have hRV : R*V=1 := cfc_inv_sqrt_mul_sqrt hB
  have hVR : V*R=1 := cfc_sqrt_mul_inv_sqrt hB
  have hVB : V*V=B := cfc_sqrt_mul_self hB
  have hVi : V⁻¹=R := Matrix.inv_eq_right_inv hVR
  have hback : V*Q*V=A := sqrt_invSqrt_congruence B hB A
  have hshift : V*(Q+t•1)*V=A+t•B := by
    rw [Matrix.mul_add,Matrix.add_mul,hback,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,hVB]
  have hInv : (A+t•B)⁻¹=R*(Q+t•1)⁻¹*R := by
    rw [← hshift,Matrix.mul_inv_rev,Matrix.mul_inv_rev,hVi]
    simp only [Matrix.mul_assoc]
  have hInv0 : A⁻¹=R*Q⁻¹*R := by
    rw [← hback,Matrix.mul_inv_rev,Matrix.mul_inv_rev,hVi]
    simp only [Matrix.mul_assoc]
  have hRB : R*B*R=1 := by
    rw [← hVB,← Matrix.mul_assoc,hRV,Matrix.one_mul,hVR]
  have hfactor (X : Matrix n n ℂ) :
      (R*X*R)*B*(R*X*R)=R*(X*X)*Rᴴ := by
    rw [hR.eq]
    calc
      _ = R*X*(R*B*R)*X*R := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hRB]; simp only [Matrix.mul_one,Matrix.mul_assoc]
  rw [hInv,hInv0,hfactor,hfactor]
  have hp := (Matrix.le_iff.mp (invSquare_scalarShift_le Q hQ ht)).mul_mul_conjTranspose_same R
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub,Matrix.sub_mul] using hp

end NLAlib
