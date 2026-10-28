import NLAlib.Matrix.Basic.QuadForm
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# A diagonal inverse Gram entry as a row residual

The identity is valid over both the real and complex fields, including a
singular full Gram matrix. Only the Gram matrix of the remaining rows must
be invertible. This is the Schur-complement input to inverse-Wishart moments.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Squared residual of a column against the row space, written using its
Hermitian Gram inverse. The value is a scalar in the ground field. -/
def gramRowResidual {n k : ℕ} (H : Matrix (Fin n) (Fin k) 𝕜) (g : Fin k → 𝕜) : 𝕜 :=
  star g ⬝ᵥ g - star (H*ᵥg) ⬝ᵥ ((H*Hᴴ)⁻¹*ᵥ(H*ᵥg))

/-- A diagonal inverse Hermitian-Gram entry is the reciprocal squared
residual of the corresponding conjugated row against the other rows. -/
theorem inv_self_mul_conjTranspose_apply_self {n k : ℕ}
    (G : Matrix (Fin (n+1)) (Fin k) 𝕜) (i : Fin (n+1))
    (hH : IsUnit (G.submatrix i.succAbove id * (G.submatrix i.succAbove id)ᴴ)) :
    (G*Gᴴ)⁻¹ i i = (gramRowResidual (G.submatrix i.succAbove id) (star (G i)))⁻¹ := by
  set H := G.submatrix i.succAbove id with hHdef
  set g := star (G i) with hg
  set M := H*Hᴴ with hM
  set c := M⁻¹*ᵥ(H*ᵥg) with hc
  set s := star g ⬝ᵥ g - star (H*ᵥg) ⬝ᵥ c with hs
  set A := G*Gᴴ with hA
  set w := g-Hᴴ*ᵥc with hw
  set x : Fin (n+1) → 𝕜 := Fin.insertNth i 1 (-c) with hx
  have hdet : M.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hH)
  have hHw : H*ᵥw=0 := by
    rw [hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← hM, hc, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec, sub_self]
  have hgw : G i ⬝ᵥ w=s := by
    have hgi : G i=star g := by simp [hg]
    rw [hgi, hw, dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
    simp only [hs, hg, star_star]
  have hGx : Gᴴ*ᵥx=w := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, hw, hx,
      Pi.sub_apply, hg, hHdef, Matrix.submatrix_apply, id, Pi.star_apply]
    rw [Fin.sum_univ_succAbove _ i]
    simp [sub_eq_add_neg, Finset.sum_neg_distrib]
  have hGw : G*ᵥw=Pi.single i s := by
    funext b
    induction b using Fin.succAboveCases i with
    | x =>
      simp only [Pi.single_eq_same]
      rw [← hgw]
      rfl
    | p a =>
      rw [Pi.single_eq_of_ne (Fin.succAbove_ne i a)]
      have h := congrFun hHw a
      simpa [Matrix.mulVec, hHdef] using h
  have hAx : A*ᵥx=Pi.single i s := by
    rw [hA, ← Matrix.mulVec_mulVec, hGx, hGw]
  have hadj : A.adjugate i i=M.det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have he : A.submatrix i.succAbove i.succAbove=M := by
      ext a b
      simp [hA, hM, hHdef, Matrix.mul_apply]
    rw [he, ← two_mul, pow_mul]
    norm_num
  have hdetA : A.det=s*M.det := by
    have h1 : A.adjugate*ᵥ(A*ᵥx)=A.det•x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hAx] at h1
    have h2 := congrFun h1 i
    have h3 : (A.adjugate*ᵥPi.single i s) i=A.adjugate i i*s := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h3, Pi.smul_apply, smul_eq_mul, hx, Fin.insertNth_apply_same, mul_one, hadj] at h2
    rw [← h2, mul_comm]
  change A⁻¹ i i=s⁻¹
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', hdetA, hadj,
    mul_inv, mul_assoc, inv_mul_cancel₀ hdet, mul_one]

end NLAlib
