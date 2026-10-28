import NLAlib.Matrix.Basic.GramSchurDiagonal
import NLAlib.Matrix.Basic.Pseudoinverse
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Inverse Gram matrices under an invertible right factor

These finite identities give the actual Haar top-Gram trace from a Gaussian
row split after canonical QR. Invertibility of the normalized Gram is proved
from the original full-rank block and its actual right factor.
-/

noncomputable section
open scoped Matrix
open Matrix
namespace NLAlib
variable {𝕜 m r s : Type*} [RCLike 𝕜] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq r]

/-- An invertible right factor gives the exact inverse normalized Gram and
proves its invertibility, rather than assuming that conclusion. -/
theorem inv_gram_of_mul_right_eq (Q Y : Matrix m r 𝕜) (R : Matrix r r 𝕜)
    (hR : IsUnit R) (hY : IsUnit (Yᴴ*Y)) (hQR : Q*R=Y) :
    (Qᴴ*Q)⁻¹ = R*(Yᴴ*Y)⁻¹*Rᴴ ∧ IsUnit (Qᴴ*Q) := by
  have hRd := (Matrix.isUnit_iff_isUnit_det _).mp hR
  have hYd := (Matrix.isUnit_iff_isUnit_det _).mp hY
  have hg : Rᴴ*(Qᴴ*Q)*R = Yᴴ*Y := by
    rw [← hQR,Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hrel : Rᴴ*(Qᴴ*Q) = (Yᴴ*Y)*R⁻¹ := by
    rw [← hg,Matrix.mul_assoc,Matrix.mul_nonsing_inv R hRd,Matrix.mul_one]
  have hi : (R*(Yᴴ*Y)⁻¹*Rᴴ)*(Qᴴ*Q)=1 := by
    calc
      _ = R*(Yᴴ*Y)⁻¹*(Rᴴ*(Qᴴ*Q)) := by simp only [Matrix.mul_assoc]
      _ = R*(Yᴴ*Y)⁻¹*((Yᴴ*Y)*R⁻¹) := by rw [hrel]
      _ = R*((Yᴴ*Y)⁻¹*(Yᴴ*Y))*R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.nonsing_inv_mul _ hYd,Matrix.mul_one,Matrix.mul_nonsing_inv R hRd]
  exact ⟨Matrix.inv_eq_left_inv hi,
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hi)⟩

/-- The inverse normalized top-Gram trace splits into the dimension plus the
independent lower-block contribution. Empty lower blocks are allowed.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem trace_inv_gram_of_mul_right_eq (Q Y : Matrix m r 𝕜) (Z : Matrix s r 𝕜)
    (R : Matrix r r 𝕜) (hR : IsUnit R) (hY : IsUnit (Yᴴ*Y)) (hQR : Q*R=Y)
    (hGram : Rᴴ*R=Yᴴ*Y+Zᴴ*Z) :
    Matrix.trace (Qᴴ*Q)⁻¹ = (Fintype.card r : 𝕜)+Matrix.trace ((Yᴴ*Y)⁻¹*(Zᴴ*Z)) := by
  rw [(inv_gram_of_mul_right_eq Q Y R hR hY hQR).1,
    Matrix.mul_assoc,Matrix.trace_mul_comm,Matrix.mul_assoc,hGram,
    Matrix.mul_add,Matrix.trace_add,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hY),Matrix.trace_one]

/-- The inverse-Gram lower-block trace is an actual squared Frobenius norm.
This identity supports integrability without assuming entrywise inverse moments. -/
theorem frobSq_mul_pinvR_adjoint_eq_re_trace (X : Matrix r m 𝕜) (Z : Matrix s r 𝕜)
    (hX : IsUnit (X*Xᴴ)) :
    frobSq (Z*(pinvR X)ᴴ) = RCLike.re (Matrix.trace ((X*Xᴴ)⁻¹*(Zᴴ*Z))) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hX
  have hHerm : ((X*Xᴴ)⁻¹)ᴴ=(X*Xᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have hP : (pinvR X)ᴴ*pinvR X=(X*Xᴴ)⁻¹ := by
    calc
      _ = (X*Xᴴ)⁻¹*(X*Xᴴ)*(X*Xᴴ)⁻¹ := by
        unfold pinvR
        rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hHerm]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hd,Matrix.one_mul]
  rw [frobSq_eq_re_trace_conjTranspose_mul_self,Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  calc
    _ = Matrix.trace (pinvR X*(Zᴴ*Z)*(pinvR X)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (((pinvR X)ᴴ*pinvR X)*(Zᴴ*Z)) := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hP]

end NLAlib
