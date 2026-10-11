import NLAlib.Matrix.MoorePenroseTransformations
import NLAlib.Matrix.SpectralBounds

/-!
# The inverse overlap Gram formula

The SVD transforms a complementary Gram `I-CᵀC` after multiplication by
`C⁻¹` into the squared tangent coefficients. Stewart–Sun §I.5;
supports `principal-angles-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- A square rectangular diagonal is the ordinary diagonal matrix.
Horn–Johnson §2.6; bridge for the inverse-overlap SVD. -/
theorem rectDiag_square_eq_diagonal {k : ℕ} (s : ℕ → ℝ) :
    (rectDiag s : Matrix (Fin k) (Fin k) ℝ)=Matrix.diagonal (fun i : Fin k => s i) := by
  ext i j
  simp only [rectDiag_apply, Matrix.diagonal_apply]
  by_cases h : i=j
  · subst j; simp
  · have hh : i.val ≠ j.val := fun hc => h (Fin.ext hc)
    simp [h, hh]

/-- Any SVD computes the ordinary inverse of an invertible square matrix.
Stewart–Sun §I.5; zero-size matrices are included. -/
theorem IsSVD.inv_eq {k : ℕ} {C U V : Matrix (Fin k) (Fin k) ℝ}
    (h : IsSVD C U V) (hC : IsUnit C) :
    C⁻¹=V*Matrix.diagonal (fun i : Fin k => (singularValues C i)⁻¹)*Uᵀ := by
  rw [← moorePenroseInverse_eq_inv_of_isUnit C hC, h.moorePenroseInverse_eq,
    rectDiag_square_eq_diagonal]

/-- The centered overlap Gram is diagonal in the right singular basis.
Stewart–Sun §I.5. -/
theorem IsSVD.one_sub_transpose_mul_self {k : ℕ} {C U V : Matrix (Fin k) (Fin k) ℝ}
    (h : IsSVD C U V) :
    1-Cᵀ*C=V*Matrix.diagonal (fun i : Fin k => 1-singularValues C i^2)*Vᵀ := by
  have hd : Matrix.diagonal (fun i : Fin k => 1-singularValues C i^2) =
      (1 : Matrix (Fin k) (Fin k) ℝ)-Matrix.diagonal (fun i : Fin k => singularValues C i^2) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    h.mul_transpose_right, h.transpose_mul_self]

/-- The inverse-overlap Gram has precisely the squared tangent ratio
coefficients in the left singular basis. Stewart–Sun §I.5. -/
theorem IsSVD.transpose_inv_mul_one_sub_gram_mul_inv {k : ℕ}
    {C U V : Matrix (Fin k) (Fin k) ℝ} (h : IsSVD C U V) (hC : IsUnit C) :
    (C⁻¹)ᵀ*(1-Cᵀ*C)*C⁻¹ = U*Matrix.diagonal
      (fun i : Fin k => (singularValues C i)⁻¹^2*(1-singularValues C i^2))*Uᵀ := by
  let D := Matrix.diagonal (fun i : Fin k => (singularValues C i)⁻¹)
  let H := Matrix.diagonal (fun i : Fin k => 1-singularValues C i^2)
  have hi : C⁻¹=V*D*Uᵀ := h.inv_eq hC
  have hg : 1-Cᵀ*C=V*H*Vᵀ := h.one_sub_transpose_mul_self
  have hcancel (T : Matrix (Fin k) (Fin k) ℝ) : Vᵀ*(V*T)=T := by
    rw [← Matrix.mul_assoc, h.transpose_mul_right, Matrix.one_mul]
  have hd : D*H*D=Matrix.diagonal
      (fun i : Fin k => (singularValues C i)⁻¹^2*(1-singularValues C i^2)) := by
    dsimp only [D, H]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    ring
  rw [hi, hg]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, show Dᵀ=D by simp [D],
    Matrix.mul_assoc, hcancel]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc U D H, Matrix.mul_assoc U (D*H) D, hd]

/-- A complementary Gram followed by an invertible overlap has the norm
of the squared tangent ratios. Stewart–Sun §I.5, including empty index sets. -/
theorem specNorm_mul_inv_sq_eq_norm_singular_ratio {m : Type*} [Fintype m]
    [DecidableEq m] {k : ℕ} (R : Matrix m (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (hC : IsUnit C) (hR : Rᵀ*R=1-Cᵀ*C) :
    specNorm (R*C⁻¹)^2 = ‖(fun i : Fin k => (singularValues C i)⁻¹^2*(1-singularValues C i^2))‖ := by
  obtain ⟨U, V, h⟩ := exists_isSVD C
  rw [specNorm_sq_eq_specNorm_transpose_mul_self, Matrix.transpose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ R, hR, ← Matrix.mul_assoc,
    h.transpose_inv_mul_one_sub_gram_mul_inv hC,
    specNorm_mul_transpose_right_of_hasOrthonormalCols h.transpose_mul_left,
    specNorm_mul_left_of_hasOrthonormalCols h.transpose_mul_left,
    specNorm_eq_norm, Matrix.l2_opNorm_diagonal]

end NLAlib
