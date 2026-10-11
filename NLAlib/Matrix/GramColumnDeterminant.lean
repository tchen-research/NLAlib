import NLAlib.Matrix.MoorePenrose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# One-column Gram determinant identity

Appending one column multiplies a Gram determinant by its squared orthogonal
projection error. A singular starting Gram has zero determinant on both sides.
Source: manuscript `sa:volume-column`.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Appending one column multiplies the Gram determinant by its squared distance
from the existing column range. Source: manuscript `sa:volume-column`;
Deshpande--Rademacher--Vempala--Wang (2006), determinant-weighted projection identity.
The Moore--Penrose projector includes dependent starting columns and empty shapes. -/
theorem det_gram_fromCols_eq_mul_frobSq_sub_projector
    {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (B : Matrix m k ℝ) (v : Matrix m (Fin 1) ℝ) :
    ((Matrix.fromCols B v)ᵀ * Matrix.fromCols B v).det =
      (Bᵀ * B).det * frobSq (v - B * moorePenroseInverse B * v) := by
  let G := Bᵀ * B
  let P := B * moorePenroseInverse B
  by_cases hG : IsUnit G
  · let := hG.nonempty_invertible.some
    have hP : Pᵀ = P := (mul_moorePenroseInverse_isSymm B).eq
    have hPP : P * P = P := mul_moorePenroseInverse_isIdempotentElem B
    have hcomp : (1 - P)ᵀ * (1 - P) = 1 - P := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, hP, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hPP]
      abel
    have hleft : v - P * v = (1 - P) * v := by
      rw [Matrix.sub_mul, Matrix.one_mul]
    have hf : frobSq (v - P * v) =
        (vᵀ * v - vᵀ * B * G⁻¹ * (Bᵀ * v)).trace := by
      rw [hleft, frobSq, frobInner_eq_trace, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (1 - P)ᵀ, hcomp]
      rw [← Matrix.mul_assoc vᵀ, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
      dsimp only [P, G]
      rw [moorePenroseInverse_eq_pinvL B hG]
      simp only [pinvL, Matrix.mul_assoc]
    have hdet : ((Matrix.fromCols B v)ᵀ * Matrix.fromCols B v).det =
        G.det * (vᵀ * v - vᵀ * B * G⁻¹ * (Bᵀ * v)).det := by
      rw [Matrix.transpose_fromCols, Matrix.fromRows_mul_fromCols,
        Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    rw [hdet]
    change G.det * (vᵀ * v - vᵀ * B * G⁻¹ * (Bᵀ * v)).det = G.det * frobSq (v - P * v)
    rw [hf]
    congr 1
    simp only [Matrix.det_fin_one, Matrix.trace, Matrix.diag, Fin.sum_univ_one]
  · have hdet : G.det = 0 := by
      by_contra hne
      exact hG ((Matrix.isUnit_iff_isUnit_det G).mpr (isUnit_iff_ne_zero.mpr hne))
    obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hBz : B *ᵥ z = 0 := by
      have hker : z ∈ LinearMap.ker G.mulVecLin := hGz
      change z ∈ LinearMap.ker (Bᵀ * B).mulVecLin at hker
      rw [Matrix.ker_mulVecLin_transpose_mul_self] at hker
      exact hker
    let x : k ⊕ Fin 1 → ℝ := Sum.elim z (fun _ => 0)
    have hx : x ≠ 0 := by
      intro hx
      apply hz
      funext i
      exact congrFun hx (Sum.inl i)
    have hWx : Matrix.fromCols B v *ᵥ x = 0 := by
      rw [Matrix.fromCols_mulVec_sumElim, hBz]
      ext a
      simp [Matrix.mulVec, dotProduct]
    have hgram : ((Matrix.fromCols B v)ᵀ * Matrix.fromCols B v) *ᵥ x = 0 := by
      rw [← Matrix.mulVec_mulVec, hWx, Matrix.mulVec_zero]
    have hdet' : ((Matrix.fromCols B v)ᵀ * Matrix.fromCols B v).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hgram⟩
    change _ = G.det * _
    rw [hdet', hdet, zero_mul]

end NLAlib
