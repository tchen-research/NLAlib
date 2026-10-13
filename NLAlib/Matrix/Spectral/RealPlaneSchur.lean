import NLAlib.Matrix.Functions.PolynomialCalculus
import NLAlib.Matrix.Subspaces.OrthogonalProducts
/-!
# Equal-diagonal orthogonal forms in a real plane

Every real two by two matrix can be orthogonally conjugated to equal
diagonal entries. For a nonreal conjugate pair the off-diagonal product
is negative, giving the corrected real Schur block.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

/-- Every real two by two matrix has an orthogonal conjugate with equal
diagonal entries. Diagonalize its symmetric part and then rotate by 45 degrees.
Horn–Johnson 2013, Theorem 2.3.1; corrected real Schur block helper. -/
theorem exists_orthogonal_two_eq_diagonal (A : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℝ, HasOrthonormalCols U ∧
      (Uᵀ * A * U) 0 0 = (Uᵀ * A * U) 1 1 := by
  let H := A + Aᵀ
  have hH : H.IsHermitian := by
    change Hᵀ = H
    simp only [H, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  let V : Matrix (Fin 2) (Fin 2) ℝ := hH.eigenvectorUnitary
  have hV : HasOrthonormalCols V := transpose_eigenvectorUnitary_mul_self hH
  have hVH : Vᵀ * H * V = Matrix.diagonal hH.eigenvalues := by
    calc
      _ = Vᵀ * (V * Matrix.diagonal hH.eigenvalues * Vᵀ) * V :=
        congrArg (fun M => Vᵀ * M * V) (eq_eigenvectorUnitary_mul_diagonal_mul_transpose hH)
      _ = (Vᵀ * V) * Matrix.diagonal hH.eigenvalues * (Vᵀ * V) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [(show Vᵀ * V = 1 from hV), Matrix.one_mul, Matrix.mul_one]
  let B := Vᵀ * A * V
  have hB : B + Bᵀ = Matrix.diagonal hH.eigenvalues := by
    simpa only [H, B, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc] using hVH
  have hOff : B 0 1 + B 1 0 = 0 := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hB
    simpa using h
  let r : ℝ := (Real.sqrt 2)⁻¹
  have hr : r * r = 1 / 2 := by
    have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    dsimp [r]
    rw [← mul_inv_rev, hs]
    norm_num
  let R : Matrix (Fin 2) (Fin 2) ℝ := !![r, r; -r, r]
  have hR : HasOrthonormalCols R := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [R, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [hr]
  refine ⟨V * R, hV.mul hR, ?_⟩
  have hRB : (V * R)ᵀ * A * (V * R) = Rᵀ * B * R := by
    simp only [B, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hRB]
  simp only [R, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  nlinarith [hOff]

end NLAlib
