import NLAlib.Matrix.Subspaces.PrincipalAngleMaximum
import NLAlib.Matrix.Subspaces.InverseOverlapGram
import NLAlib.Matrix.Basic.Gram
/-!
# The principal-angle tangent formula

An invertible overlap identifies the tangent norm with the residual times
the ordinary overlap inverse. The complementary-coordinate formulation and
the last-angle condition are linked to this algebraic statement.
Source: Stewart–Sun §I.5; atlas `principal-angles-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The diagonal tangent matrix of the principal angles. Stewart–Sun §I.5;
its finite geometric interpretation and the inverse formulas below require an
invertible overlap. At a right angle Mathlib's total `Real.tan` returns zero,
so this diagonal is an algebraic helper outside the transverse domain.
atlas: principal-angles-def (partial) -/
def tangentPrincipalAngles (P Q : Matrix m n ℝ) :
    Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
  Matrix.diagonal (fun i => Real.tan (principalAnglesFintype P Q i))

/-- The tangent square equals the complementary-to-overlap singular
ratio square. Stewart–Sun §I.5; total real division also handles cosine zero. -/
theorem tan_principalAngles_sq {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (i : Fin (Fintype.card n)) :
    Real.tan (principalAnglesFintype P Q i)^2 =
      (singularValues ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i)⁻¹^2*
        (1-singularValues ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i^2) := by
  have hb := overlap_singularValues_mem_Icc hP hQ i
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hb
  have hn : 0 ≤ 1-singularValues ((Pᵀ*Q).reindex (Fintype.equivFin n) (Fintype.equivFin n)) i^2 := by
    nlinarith [hb.1, hb.2]
  rw [Real.tan_eq_sin_div_cos, cos_principalAngles hP hQ, sin_principalAngles,
    Matrix.conjTranspose_eq_transpose_of_trivial, div_eq_mul_inv, mul_pow, Real.sq_sqrt hn, mul_comm]

/-- The actual tangent matrix has the residual-times-overlap-inverse norm.
Stewart–Sun §I.5; arbitrary finite indices and empty frames are included.
atlas: principal-angles-def (partial) -/
theorem specNorm_tangentPrincipalAngles_eq_residual_mul_inv {P Q : Matrix m n ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hC : IsUnit (Pᵀ*Q)) :
    specNorm (tangentPrincipalAngles P Q)=specNorm (projResidual P Q*(Pᵀ*Q)⁻¹) := by
  let e := Fintype.equivFin n
  let C := Pᵀ*Q
  let CF := C.reindex e e
  let R := projResidual P Q
  let RF := R.reindex (Equiv.refl m) e
  have hCF : IsUnit CF := hC.map (Matrix.reindexRingEquiv ℝ e).toMonoidHom
  have hinv : CF⁻¹=(C⁻¹).reindex e e := by
    rw [← moorePenroseInverse_eq_inv_of_isUnit CF hCF]
    change moorePenroseInverse (C.reindex e e) = _
    rw [moorePenroseInverse_reindex, moorePenroseInverse_eq_inv_of_isUnit C hC]
  have hgram : RFᵀ*RF=1-CFᵀ*CF := by
    simp only [RF, CF, Matrix.reindex_apply, Matrix.transpose_submatrix,
      Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_mul_equiv]
    have hh := conjTranspose_residual_mul_residual_eq_one_sub_overlap hP hQ
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
    change (Rᵀ*R).submatrix e.symm e.symm = 1-(Cᵀ*C).submatrix e.symm e.symm
    change Rᵀ*R=1-Cᵀ*C at hh
    rw [hh]
    change (1 : Matrix n n ℝ).submatrix e.symm e.symm - (Cᵀ*C).submatrix e.symm e.symm = _
    rw [Matrix.submatrix_one_equiv]
  have hprod : RF*CF⁻¹=(R*C⁻¹).reindex (Equiv.refl m) e := by
    rw [hinv]
    simp only [RF, Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl,
      Matrix.submatrix_mul_equiv]
  have hi := specNorm_mul_inv_sq_eq_norm_singular_ratio RF CF hCF hgram
  rw [hprod, specNorm_reindex] at hi
  have ht := specNorm_sq_eq_specNorm_transpose_mul_self (tangentPrincipalAngles P Q)
  have htg : (tangentPrincipalAngles P Q)ᵀ*tangentPrincipalAngles P Q =
      Matrix.diagonal (fun i : Fin (Fintype.card n) => (singularValues CF i)⁻¹^2*(1-singularValues CF i^2)) := by
    rw [tangentPrincipalAngles, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    change Real.tan (principalAnglesFintype P Q i)*Real.tan (principalAnglesFintype P Q i) = _
    rw [← sq]
    exact tan_principalAngles_sq hP hQ i
  rw [htg] at ht
  simp only [specNorm_eq_norm, Matrix.l2_opNorm_diagonal] at ht
  change specNorm (tangentPrincipalAngles P Q)^2 =
    ‖(fun i : Fin (Fintype.card n) => (singularValues CF i)⁻¹^2*(1-singularValues CF i^2))‖ at ht
  change specNorm (R*C⁻¹)^2 = _ at hi
  nlinarith [specNorm_nonneg (tangentPrincipalAngles P Q), specNorm_nonneg (R*C⁻¹)]

/-- The complementary-coordinate tangent formula. Stewart–Sun §I.5;
the complement may be empty, and the overlap is the ordinary inverse.
atlas: principal-angles-def (partial) -/
theorem specNorm_tangentPrincipalAngles_eq_complement_overlap_mul_inv {r : Type*}
    [Fintype r] [DecidableEq r] {P Q : Matrix m n ℝ} {R : Matrix m r ℝ}
    (hP : HasOrthonormalCols P) (hQ : HasOrthonormalCols Q) (hR : HasOrthonormalCols R)
    (hcomp : P*Pᵀ+R*Rᵀ=1) (hC : IsUnit (Pᵀ*Q)) :
    specNorm (tangentPrincipalAngles P Q)=specNorm ((Rᵀ*Q)*(Pᵀ*Q)⁻¹) := by
  rw [specNorm_tangentPrincipalAngles_eq_residual_mul_inv hP hQ hC,
    residual_eq_complement_mul_overlap hcomp, Matrix.mul_assoc,
    specNorm_mul_left_of_hasOrthonormalCols (show Rᵀ * R = 1 from hR)]

omit [DecidableEq m] in
/-- A last principal angle strictly below `π/2` makes the overlap
invertible. Stewart–Sun §I.5; positive frame width is explicit. -/
theorem isUnit_overlap_of_principalAngles_last_lt_pi_div_two {P Q : Matrix m n ℝ}
    (hn : 0 < Fintype.card n)
    (hangle : principalAnglesFintype P Q ⟨Fintype.card n-1, by omega⟩ < Real.pi/2) :
    IsUnit (Pᵀ*Q) := by
  let e := Fintype.equivFin n
  let C := (Pᵀ*Q).reindex e e
  have hs : 0 < singularValues C (Fintype.card n-1) := by
    simpa only [principalAnglesFintype, C, singularValues_reindex,
      Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Real.arccos_lt_pi_div_two.mp hangle)
  have hi := (singularValues_pos_iff C (Fintype.card n-1)).mp hs
  have hc := Matrix.rank_le_card_width C
  have hr : C.rank=Fintype.card n := by simp only [Fintype.card_fin] at hc; omega
  have hC : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr
    (isUnit_iff_ne_zero.mpr (det_ne_zero_of_rank_eq C (by simpa only [Fintype.card_fin] using hr)))
  have hh := hC.map (Matrix.reindexRingEquiv ℝ e.symm).toMonoidHom
  change IsUnit (C.reindex e.symm e.symm) at hh
  have hback : C.reindex e.symm e.symm=Pᵀ*Q := by
    ext i j
    simp [C, Matrix.reindex_apply]
  rw [hback] at hh
  exact hh

end NLAlib
