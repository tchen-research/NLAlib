import NLAlib.Matrix.ComplexVolumeProjection
import NLAlib.Matrix.ComplexFrobeniusTrace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
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
set_option autoImplicit false
open scoped Classical Matrix Matrix.Norms.Frobenius ComplexOrder
namespace NLAlib

/-- The genuine Hilbert projector equals the inverse Gram formula when the
columns are independent. Source: `sa:volume-column`, actual projection bridge. -/
theorem complexColumnProjector_eq_mul_inv_gram_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (B : Matrix m n ℂ) (hG : IsUnit (Bᴴ * B)) :
    complexColumnProjector B = B * (Bᴴ * B)⁻¹ * Bᴴ := by
  let G := Bᴴ * B
  let Q := B * G⁻¹ * Bᴴ
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have hQB : Q * B = B := by
    change B * G⁻¹ * Bᴴ * B = B
    simp only [Matrix.mul_assoc]
    change B * (G⁻¹ * G) = B
    rw [Matrix.nonsing_inv_mul G hd, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    change Q * (B * G⁻¹ * Bᴴ) = Q
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hQB]
  have hQ : Q.IsHermitian := by
    simpa only [Q, G, Matrix.conjTranspose_conjTranspose] using
      Matrix.isHermitian_conjTranspose_mul_mul Bᴴ (Matrix.isHermitian_conjTranspose_mul_self B).inv
  have hRange : LinearMap.range (Matrix.toEuclideanLin Q) = complexColumnSpace B := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Matrix.toEuclideanLin (G⁻¹ * Bᴴ) x, ?_⟩
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
      exact congrArg (fun M : Matrix m m ℂ => Matrix.toEuclideanLin M x)
        (Matrix.mul_assoc B G⁻¹ Bᴴ).symm
    · rintro ⟨x, rfl⟩
      refine ⟨Matrix.toEuclideanLin B x, ?_⟩
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same]
      exact congrArg (fun M : Matrix m n ℂ => Matrix.toEuclideanLin M x) hQB
  have hProj : (Matrix.toEuclideanLin Q).IsSymmetricProjection := by
    refine ⟨?_, Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ⟩
    change (Matrix.toEuclideanLin Q).comp (Matrix.toEuclideanLin Q) = Matrix.toEuclideanLin Q
    have hh := congrArg Matrix.toEuclideanLin hQQ
    simpa only [Matrix.toLpLin_mul_same] using hh
  obtain ⟨_, hEq⟩ := LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hProj
  have hEq' : Matrix.toEuclideanLin Q = (complexColumnSpace B).starProjection.toLinearMap := by
    simpa only [hRange] using hEq
  apply Matrix.toEuclideanLin.injective
  rw [toEuclideanLin_complexColumnProjector]
  exact hEq'.symm

/-- Appending a genuine complex column multiplies its Gram determinant by
the squared Frobenius projection residual. Dependent starting columns and
empty shapes are included. Source: `sa:volume-column`.
atlas: volume-sampling (partial) -/
theorem det_gram_fromCols_eq_mul_frobenius_norm_sq_sub_complexColumnProjector
    {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    (B : Matrix m k ℂ) (v : Matrix m (Fin 1) ℂ) :
    ((Matrix.fromCols B v)ᴴ * Matrix.fromCols B v).det.re =
      (Bᴴ * B).det.re * ‖v - complexColumnProjector B * v‖ ^ 2 := by
  let G := Bᴴ * B
  let P := complexColumnProjector B
  by_cases hG : IsUnit G
  · let := hG.nonempty_invertible.some
    have hP : Pᴴ = P := (complexColumnProjector_isHermitian B).eq
    have hPP : P * P = P := complexColumnProjector_mul_self B
    have hcomp : (1 - P)ᴴ * (1 - P) = 1 - P := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP, Matrix.sub_mul,
        Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hPP]
      abel
    have hleft : v - P * v = (1 - P) * v := by rw [Matrix.sub_mul, Matrix.one_mul]
    have hf : ‖v - P * v‖ ^ 2 =
        (vᴴ * v - vᴴ * B * G⁻¹ * (Bᴴ * v)).trace.re := by
      rw [hleft, frobenius_norm_sq_eq_re_trace_conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (1 - P)ᴴ, hcomp, ← Matrix.mul_assoc vᴴ,
        Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
      dsimp only [P]
      rw [complexColumnProjector_eq_mul_inv_gram_conjTranspose B hG]
      simp only [G, Matrix.mul_assoc]
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
