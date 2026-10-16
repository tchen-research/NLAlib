import NLAlib.Matrix.Structured.Realification
import NLAlib.Matrix.Norms.SchattenDiagonal

/-!
# Norms under complex realification

Realification duplicates singular values, so unnormalized finite Schatten
norms gain a factor `2^(1/p)`. Normalized Schatten norms and the spectral
norm therefore agree with their complex counterparts.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

private theorem rectDiag_square_eq_diagonal {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
    (σ : ℕ → ℝ) :
    (rectDiag σ : Matrix (Fin n) (Fin n) 𝕜) = Matrix.diagonal (fun i : Fin n => (σ i : 𝕜)) := by
  ext i j
  simp only [rectDiag_apply_ofReal, Matrix.diagonal_apply, Fin.ext_iff]

private theorem schattenNormReal_matrixRealification_fin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (p : ℝ) :
    schattenNormReal (matrixRealification A) p = 2^(1/p) * schattenNormReal A p := by
  obtain ⟨U,V,h⟩ := exists_isSVD A
  have hU : HasOrthonormalCols U := h.conjTranspose_mul_left
  have hVT : HasOrthonormalCols Vᴴ := by
    rw [hasOrthonormalCols_iff_conjTranspose_mul_self,Matrix.conjTranspose_conjTranspose]
    exact h.mul_conjTranspose_right
  have hRVT : HasOrthonormalCols (matrixRealification V)ᵀ := by
    simpa only [matrixRealification_conjTranspose] using hVT.realification
  have hc : schattenNormReal A p = (∑ i : Fin n, singularValues A i ^ p)^(1/p) := by
    conv_lhs => rw [h.eq]
    rw [schattenNormReal_mul_orthogonal _ hVT,
      schattenNormReal_orthogonal_mul _ h.conjTranspose_mul_left,
      rectDiag_square_eq_diagonal,schattenNormReal_diagonal_complex]
    simp only [RCLike.norm_ofReal,Real.norm_eq_abs,abs_of_nonneg (singularValues_nonneg _ _)]
  calc
    schattenNormReal (matrixRealification A) p
      = (∑ i : Fin n ⊕ Fin n, |Sum.elim (fun i : Fin n => singularValues A i)
          (fun i : Fin n => singularValues A i) i|^p)^(1/p) := by
        conv_lhs => rw [h.eq]
        rw [matrixRealification_mul,matrixRealification_mul,matrixRealification_conjTranspose,
          schattenNormReal_mul_orthogonal _ hRVT,
          schattenNormReal_orthogonal_mul _ hU.realification,
          rectDiag_square_eq_diagonal]
        have hd : matrixRealification (Matrix.diagonal (fun i : Fin n => (singularValues A i : ℂ)))
            = Matrix.diagonal (Sum.elim (fun i : Fin n => singularValues A i)
              (fun i : Fin n => singularValues A i)) :=
          matrixRealification_diagonal_ofReal (fun i : Fin n => singularValues A i)
        change schattenNormReal (matrixRealification
          (Matrix.diagonal (fun i : Fin n => (singularValues A i : ℂ)))) p = _
        rw [hd,schattenNormReal_diagonal_real]
    _ = (2 * ∑ i : Fin n, singularValues A i ^ p)^(1/p) := by
        rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl,Sum.elim_inr,abs_of_nonneg (singularValues_nonneg _ _)]
        congr 1
        ring
    _ = 2^(1/p) * schattenNormReal A p := by
        have hsum : 0 ≤ ∑ i : Fin n, singularValues A i ^ p :=
          Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg A i) p
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hsum,hc]

/-- Realification multiplies every finite Schatten power norm by the exact
factor `2^(1/p)`, including zero and repeated singular values. -/
theorem schattenNormReal_matrixRealification {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (p : ℝ) :
    schattenNormReal (matrixRealification A) p = 2^(1/p) * schattenNormReal A p := by
  have h := schattenNormReal_matrixRealification_fin
    (A.reindex (Fintype.equivFin n) (Fintype.equivFin n)) p
  rw [matrixRealification_reindex,schattenNormReal_reindex,schattenNormReal_reindex] at h
  exact h

end NLAlib
