import NLAlib.Matrix.PrincipalAngleDefinitions
import NLAlib.Matrix.Sylvester

/-!
# Davis–Kahan residual bounds

The mixed-gap theorem follows from the actual invariant-subspace equations
and the interval/complement Sylvester bound. It keeps the compressed residual
and both spectral and Frobenius norms. Source: Davis–Kahan §6;
atlas `davis-kahan-sin-theta`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {n k r : Type*} [Fintype n] [Fintype k] [Fintype r]
  [DecidableEq n] [DecidableEq k] [DecidableEq r]

omit [DecidableEq n] in
/-- A coefficient matrix of an invariant orthonormal frame is its
Hermitian compression. Davis–Kahan §6. -/
theorem isHermitian_of_invariant_orthonormal_frame {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {Q : Matrix n k ℝ} (hQ : HasOrthonormalCols Q)
    {L : Matrix k k ℝ} (hAQ : A*Q=Q*L) : L.IsHermitian := by
  have heq : Qᵀ*A*Q=L := by
    rw [Matrix.mul_assoc, hAQ, ← Matrix.mul_assoc Qᵀ Q, hQ, Matrix.one_mul]
  exact heq ▸ isHermitian_transpose_mul_mul hA Q

omit [DecidableEq n] [DecidableEq k] [DecidableEq r] in
/-- The complementary overlap satisfies the exact residual Sylvester
equation. Davis–Kahan §6; neither coefficient Hermiticity is assumed here. -/
theorem sylvester_complement_overlap_eq {A E : Matrix n n ℝ}
    (hA : A.IsHermitian) (hE : E.IsHermitian)
    {Q : Matrix n k ℝ} {R : Matrix n r ℝ}
    {L : Matrix k k ℝ} {M : Matrix r r ℝ}
    (hAQ : A*Q=Q*L) (hAR : (A+E)*R=R*M) (hM : M.IsHermitian) :
    M*(Rᵀ*Q)-(Rᵀ*Q)*L = Rᵀ*E*Q := by
  have hRT : Rᵀ*(A+E)=M*Rᵀ := by
    have hh := congrArg Matrix.transpose hAR
    simpa only [Matrix.transpose_mul, Matrix.transpose_add,
      Matrix.isHermitian_iff_isSymm.mp hA |>.eq,
      Matrix.isHermitian_iff_isSymm.mp hE |>.eq,
      Matrix.isHermitian_iff_isSymm.mp hM |>.eq] using hh
  have hQQ : (Rᵀ*Q)*L = Rᵀ*A*Q := by
    rw [Matrix.mul_assoc, ← hAQ, ← Matrix.mul_assoc]
  rw [hQQ, ← Matrix.mul_assoc M Rᵀ Q, ← hRT, Matrix.mul_add, Matrix.add_mul]
  abel

/-- Davis–Kahan with the full compressed residual and the spectral
interval/complement gap. Davis–Kahan §6; empty selected or complementary frames
are allowed. This is the constant-one mixed-gap form.
atlas: davis-kahan-sin-theta (partial) -/
theorem specNorm_sinePrincipalAngles_le_compressed_residual_div
    {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian)
    {Q Qhat : Matrix n k ℝ} {R : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (hQhat : HasOrthonormalCols Qhat)
    (hR : HasOrthonormalCols R) (hcomp : Qhat*Qhatᵀ+R*Rᵀ=1)
    {L : Matrix k k ℝ} {M : Matrix r r ℝ}
    (hAQ : A*Q=Q*L) (hAR : (A+E)*R=R*M)
    {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (hinterval : ∀ j, a ≤ (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ∧
      (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ≤ b)
    (hout : ∀ i, (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i ≤ a-δ ∨
      b+δ ≤ (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i) :
    specNorm (sinePrincipalAngles Q Qhat) ≤ specNorm (Rᵀ*E*Q)/δ := by
  let hL := isHermitian_of_invariant_orthonormal_frame hA hQ hAQ
  let hM := isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR
  have hh := specNorm_le_specNorm_sylvester_div hM hL hab hδ hinterval hout (Rᵀ*Q)
  rw [sylvester_complement_overlap_eq hA hE hAQ hAR hM] at hh
  have hangles : sinePrincipalAngles Q Qhat = sinePrincipalAngles Qhat Q := by
    rw [sinePrincipalAngles, principalAngles_comm]
    rfl
  rw [hangles, specNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp]
  exact hh

/-- Davis–Kahan's corresponding compressed Frobenius residual bound.
Davis–Kahan §6; the actual separation, not a desired norm bound, is assumed.
atlas: davis-kahan-sin-theta (partial) -/
theorem frobNorm_sinePrincipalAngles_le_compressed_residual_div
    {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian)
    {Q Qhat : Matrix n k ℝ} {R : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (hQhat : HasOrthonormalCols Qhat)
    (hR : HasOrthonormalCols R) (hcomp : Qhat*Qhatᵀ+R*Rᵀ=1)
    {L : Matrix k k ℝ} {M : Matrix r r ℝ}
    (hAQ : A*Q=Q*L) (hAR : (A+E)*R=R*M)
    {a b δ : ℝ} (_hab : a ≤ b) (hδ : 0 < δ)
    (hinterval : ∀ j, a ≤ (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ∧
      (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ≤ b)
    (hout : ∀ i, (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i ≤ a-δ ∨
      b+δ ≤ (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i) :
    frobNorm (sinePrincipalAngles Q Qhat) ≤ frobNorm (Rᵀ*E*Q)/δ := by
  let hL := isHermitian_of_invariant_orthonormal_frame hA hQ hAQ
  let hM := isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR
  have hsep := eigenvalue_separation_of_interval_complement hM hL hinterval hout
  have hh := frobNorm_le_frobNorm_sylvester_div hM hL hδ hsep (Rᵀ*Q)
  rw [sylvester_complement_overlap_eq hA hE hAQ hAR hM] at hh
  have hangles : sinePrincipalAngles Q Qhat = sinePrincipalAngles Qhat Q := by
    rw [sinePrincipalAngles, principalAngles_comm]
    rfl
  rw [hangles, frobNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp]
  exact hh

/-- Interval/complement separation gives both compressed residual bounds
without requiring an endpoint order in empty selected spaces. Davis–Kahan §6;
Hermitian coefficient matrices are derived from the actual invariant frames.
atlas: davis-kahan-sin-theta (partial) -/
theorem sinePrincipalAngles_le_compressed_residual_div_of_interval
    {A E : Matrix n n ℝ} (hA : A.IsHermitian) (hE : E.IsHermitian)
    {Q Qhat : Matrix n k ℝ} {R : Matrix n r ℝ}
    (hQ : HasOrthonormalCols Q) (hQhat : HasOrthonormalCols Qhat)
    (hR : HasOrthonormalCols R) (hcomp : Qhat*Qhatᵀ+R*Rᵀ=1)
    {L : Matrix k k ℝ} {M : Matrix r r ℝ}
    (hAQ : A*Q=Q*L) (hAR : (A+E)*R=R*M)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hinterval : ∀ j, a ≤ (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ∧
      (isHermitian_of_invariant_orthonormal_frame hA hQ hAQ).eigenvalues j ≤ b)
    (hout : ∀ i, (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i ≤ a-δ ∨
      b+δ ≤ (isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR).eigenvalues i) :
    specNorm (sinePrincipalAngles Q Qhat) ≤ specNorm (Rᵀ*E*Q)/δ ∧
      frobNorm (sinePrincipalAngles Q Qhat) ≤ frobNorm (Rᵀ*E*Q)/δ := by
  let hL := isHermitian_of_invariant_orthonormal_frame hA hQ hAQ
  let hM := isHermitian_of_invariant_orthonormal_frame (hA.add hE) hR hAR
  have hS := mul_specNorm_le_specNorm_sylvester_of_interval hM hL hδ hinterval hout (Rᵀ*Q)
  have hF := mul_frobNorm_le_frobNorm_sylvester hM hL hδ
    (eigenvalue_separation_of_interval_complement hM hL hinterval hout) (Rᵀ*Q)
  rw [sylvester_complement_overlap_eq hA hE hAQ hAR hM] at hS hF
  have hswap : sinePrincipalAngles Q Qhat=sinePrincipalAngles Qhat Q := by
    unfold sinePrincipalAngles
    rw [principalAngles_comm]
  rw [← specNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp, ← hswap] at hS
  rw [← frobNorm_sinePrincipalAngles_eq_complement_overlap hQhat hQ hR hcomp, ← hswap] at hF
  exact ⟨(le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hS),
    (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hF)⟩

end NLAlib
