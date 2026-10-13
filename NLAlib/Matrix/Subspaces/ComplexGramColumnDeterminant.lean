import NLAlib.Matrix.Subspaces.ComplexVolumeProjection
import NLAlib.Matrix.Norms.Frobenius
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.Matrix.PosDef

/-!
# The complex one-column Gram determinant identity

The actual Hilbert orthogonal projector agrees with the inverse Gram formula
on full-rank columns. Schur complementation then proves the insertion
identity, and singular columns make both determinants zero.
Source: operator re-derivation `sa:volume-column`.
-/

noncomputable section
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

/-- Appending a genuine complex column multiplies its Gram determinant by
the squared Frobenius projection residual. Dependent starting columns and
empty shapes are included. Source: `sa:volume-column`.
atlas: volume-sampling (partial) -/
theorem det_gram_fromCols_eq_mul_frobenius_norm_sq_sub_rangeProjector
    {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (B : Matrix m k ℂ) (v : Matrix m (Fin 1) ℂ) :
    ((Matrix.fromCols B v)ᴴ * Matrix.fromCols B v).det.re =
      (Bᴴ * B).det.re * ‖v - rangeProjector B * v‖ ^ 2 := by
  let G := Bᴴ * B
  let P := rangeProjector B
  by_cases hG : IsUnit G
  · let := hG.nonempty_invertible.some
    have hP : Pᴴ = P := (rangeProjector_isHermitian B).eq
    have hPP : P * P = P := rangeProjector_mul_self B
    have hcomp : (1 - P)ᴴ * (1 - P) = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hPP]
      abel
    have hleft : v - P * v = (1 - P) * v := by rw [Matrix.sub_mul, Matrix.one_mul]
    have hf : ‖v - P * v‖ ^ 2 =
        (vᴴ * v - vᴴ * B * G⁻¹ * (Bᴴ * v)).trace.re := by
      rw [hleft, ← frobNorm_eq_norm, frobNorm_sq, frobSq_eq_re_trace_conjTranspose_mul_self, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (1 - P)ᴴ, hcomp, ← Matrix.mul_assoc vᴴ,
        Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
      dsimp only [P]
      rw [rangeProjector_eq_mul_inv_gram_conjTranspose B hG]
      simp only [G, Matrix.mul_assoc, RCLike.re_to_complex]
    have hdet : ((Matrix.fromCols B v)ᴴ * Matrix.fromCols B v).det =
        G.det * (vᴴ * v - vᴴ * B * G⁻¹ * (Bᴴ * v)).det := by
      rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
        Matrix.fromRows_mul_fromCols, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    have hGim : G.det.im = 0 := by
      exact (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self B).det_nonneg).2
    rw [hdet, Complex.mul_re, hGim, zero_mul, sub_zero, hf]
    congr 1
    simp only [Matrix.det_fin_one, Matrix.trace, Matrix.diag, Fin.sum_univ_one]
  · have hdet : G.det = 0 := by
      by_contra hne
      exact hG ((Matrix.isUnit_iff_isUnit_det G).mpr (isUnit_iff_ne_zero.mpr hne))
    obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hBz : B *ᵥ z = 0 := by
      have hker : z ∈ LinearMap.ker G.mulVecLin := hGz
      change z ∈ LinearMap.ker (Bᴴ * B).mulVecLin at hker
      rw [Matrix.ker_mulVecLin_conjTranspose_mul_self] at hker
      exact hker
    let x : k ⊕ Fin 1 → ℂ := Sum.elim z (fun _ => 0)
    have hx : x ≠ 0 := by
      intro hx
      apply hz
      funext i
      exact congrFun hx (Sum.inl i)
    have hWx : Matrix.fromCols B v *ᵥ x = 0 := by
      rw [Matrix.fromCols_mulVec_sumElim, hBz]
      ext a
      simp [Matrix.mulVec, dotProduct]
    have hgram : ((Matrix.fromCols B v)ᴴ * Matrix.fromCols B v) *ᵥ x = 0 := by
      rw [← Matrix.mulVec_mulVec, hWx, Matrix.mulVec_zero]
    have hdet' : ((Matrix.fromCols B v)ᴴ * Matrix.fromCols B v).det = 0 :=
      Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hgram⟩
    change _ = G.det.re * _
    rw [hdet', hdet, Complex.zero_re, zero_mul]

end NLAlib
