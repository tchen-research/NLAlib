import NLAlib.Matrix.CompressionDeterminant
import NLAlib.Matrix.PolarFrame
import NLAlib.Matrix.ProductWeyl
import NLAlib.Matrix.KyFan
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Horn's multiplicative singular-value inequality

Orthogonal compression determinants and a polar normalization of the intermediate
image give every prefix-product inequality. A singular intermediate Gram matrix
is treated by its actual kernel, with no positivity or full-rank assumptions.
Source: Horn–Johnson 1991, Theorem 3.3.4, and the operator derivation manuscript,
Section 4. Atlas: `horn-product-inequality`.
-/

noncomputable section
open scoped Matrix

namespace NLAlib

/-- A singular column Gram matrix stays singular after left multiplication.
Horn product proof, singular intermediate-image case; all finite shapes are allowed.
-/
theorem det_gram_mul_eq_zero_of_det_gram_eq_zero {m p k : Type*}
    [Fintype m] [Fintype p] [Fintype k] [DecidableEq k]
    (A : Matrix m p ℝ) (Y : Matrix p k ℝ) (hY : (Yᵀ * Y).det = 0) :
    ((A * Y)ᵀ * (A * Y)).det = 0 := by
  obtain ⟨x, hx, hYx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hY
  have hnorm : (Y *ᵥ x) ⬝ᵥ (Y *ᵥ x) = 0 := by
    rw [← dotProduct_transpose_mul_mulVec, hYx]
    simp
  have hy : Y *ᵥ x = 0 := dotProduct_self_eq_zero.mp hnorm
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨x, hx, ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero,
    Matrix.mulVec_zero]

/-- A left image's Gram determinant is bounded by the original Gram determinant
times the product of the top squared singular values of the left multiplier.
Horn–Johnson 1991, Theorem 3.3.4, polar-compression step; singular inputs included.
-/
theorem det_gram_mul_le_det_gram_mul_prod_sq_singularValues {m p k : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (Y : Matrix (Fin p) (Fin k) ℝ) :
    ((A * Y)ᵀ * (A * Y)).det ≤ (Yᵀ * Y).det * ∏ i : Fin k, singularValues A i ^ 2 := by
  by_cases hY : IsUnit (Yᵀ * Y)
  · let U := polarFrame Y
    let R := Uᵀ * Y
    have hU : HasOrthonormalCols U := hasOrthonormalCols_polarFrame Y hY
    have hUR : U * R = Y := polarFrame_mul_transpose_mul_eq Y hY
    have hGram : Yᵀ * Y = Rᵀ * R := by
      calc
        Yᵀ * Y = (U * R)ᵀ * (U * R) := by rw [hUR]
        _ = Rᵀ * R := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Uᵀ U, show Uᵀ * U = 1 from hU, Matrix.one_mul]
    have hImage : (A * Y)ᵀ * (A * Y) = Rᵀ * (Uᵀ * (Aᵀ * A) * U) * R := by
      conv_lhs => rw [← hUR]
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    have hdet : ((A * Y)ᵀ * (A * Y)).det =
        (Yᵀ * Y).det * ((A * U)ᵀ * (A * U)).det := by
      rw [hImage, hGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
        Matrix.det_mul, Matrix.det_transpose, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
      ring
    rw [hdet]
    apply mul_le_mul_of_nonneg_left (det_gram_mul_le_prod_sq_singularValues A hU)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.posSemidef_conjTranspose_mul_self Y).det_nonneg
  · have hdet : (Yᵀ * Y).det = 0 := by
      simpa only [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not] using hY
    rw [hdet, zero_mul, det_gram_mul_eq_zero_of_det_gram_eq_zero A Y hdet]

/-- The top right singular frame attains the product of the first `k` squared
singular values as its image Gram determinant. Horn's product proof, SVD step.
-/
theorem IsSVD.det_gram_mul_submatrix_eq_prod_sq_singularValues {m n k : ℕ}
    {T : Matrix (Fin m) (Fin n) ℝ} {U : Matrix (Fin m) (Fin m) ℝ}
    {V : Matrix (Fin n) (Fin n) ℝ} (hT : IsSVD T U V) (hkn : k ≤ n) :
    ((T * V.submatrix id (Fin.castLE hkn))ᵀ *
      (T * V.submatrix id (Fin.castLE hkn))).det = ∏ i : Fin k, singularValues T i ^ 2 := by
  let E : Matrix (Fin n) (Fin k) ℝ := (1 : Matrix (Fin n) (Fin n) ℝ).submatrix id (Fin.castLE hkn)
  have hVE : Vᵀ * V.submatrix id (Fin.castLE hkn) = E := by
    have h := Matrix.submatrix_mul_equiv Vᵀ V id (Equiv.refl (Fin n)) (Fin.castLE hkn)
    simp only [Equiv.coe_refl, Matrix.submatrix_id_id] at h
    rw [h, hT.transpose_mul_right]
  have hEV : (V.submatrix id (Fin.castLE hkn))ᵀ * V = Eᵀ := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose hVE
  have hGram : ((T * V.submatrix id (Fin.castLE hkn))ᵀ *
      (T * V.submatrix id (Fin.castLE hkn))) =
      Eᵀ * Matrix.diagonal (fun i : Fin n => singularValues T i ^ 2) * E := by
    rw [Matrix.transpose_mul]
    calc
      _ = (V.submatrix id (Fin.castLE hkn))ᵀ * (Tᵀ * T) *
          V.submatrix id (Fin.castLE hkn) := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hT.transpose_mul_self]
        simp only [Matrix.mul_assoc]
        rw [hVE, ← Matrix.mul_assoc, hEV]
  have hDiag : Eᵀ * Matrix.diagonal (fun i : Fin n => singularValues T i ^ 2) * E =
      Matrix.diagonal (fun i : Fin k => singularValues T i ^ 2) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [E, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.submatrix_apply,
        Matrix.one_apply]
    · simp [E, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.submatrix_apply,
        Matrix.one_apply, hij]
  rw [hGram, hDiag, Matrix.det_diagonal]

/-- Horn's product inequality at every natural prefix length, with zero-indexed,
zero-padded singular values. Horn–Johnson 1991, Theorem 3.3.4. No positivity,
rank, or nonemptiness assumptions are imposed.
atlas: horn-product-inequality (partial) -/
theorem prod_singularValues_mul_le {m p n : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin p) (Fin n) ℝ) (k : ℕ) :
    (∏ i ∈ Finset.range k, singularValues (A * B) i) ≤
      ∏ i ∈ Finset.range k, singularValues A i * singularValues B i := by
  by_cases hk : k ≤ min m (min p n)
  · obtain ⟨U, V, hT⟩ := exists_isSVD (A * B)
    have hkn : k ≤ n := hk.trans ((min_le_right m (min p n)).trans (min_le_right p n))
    let Q := V.submatrix id (Fin.castLE hkn)
    have hQ : HasOrthonormalCols Q :=
      HasOrthonormalCols.submatrix_cols hT.transpose_mul_right
        ⟨Fin.castLE hkn, Fin.castLE_injective hkn⟩
    have hdetT := hT.det_gram_mul_submatrix_eq_prod_sq_singularValues hkn
    have hA := det_gram_mul_le_det_gram_mul_prod_sq_singularValues A (B * Q)
    have hB := det_gram_mul_le_prod_sq_singularValues B hQ
    have hsq : (∏ i : Fin k, singularValues (A * B) i) ^ 2 ≤
        (∏ i : Fin k, singularValues A i * singularValues B i) ^ 2 := by
      rw [← Finset.prod_pow, ← Finset.prod_pow]
      calc
        _ = ((A * (B * Q))ᵀ * (A * (B * Q))).det := by
          simpa only [Q, Matrix.mul_assoc] using hdetT.symm
        _ ≤ ((B * Q)ᵀ * (B * Q)).det * ∏ i : Fin k, singularValues A i ^ 2 := hA
        _ ≤ (∏ i : Fin k, singularValues B i ^ 2) * ∏ i : Fin k, singularValues A i ^ 2 :=
          mul_le_mul_of_nonneg_right hB (Finset.prod_nonneg fun i _ => sq_nonneg _)
        _ = _ := by rw [← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro i _; ring
    have h0 : 0 ≤ ∏ i : Fin k, singularValues A i * singularValues B i :=
      Finset.prod_nonneg fun i _ => mul_nonneg (singularValues_nonneg A i) (singularValues_nonneg B i)
    have h1 : 0 ≤ ∏ i : Fin k, singularValues (A * B) i :=
      Finset.prod_nonneg fun i _ => singularValues_nonneg _ _
    rw [← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
    nlinarith
  · have hbound : (A * B).rank ≤ min m (min p n) := by
      apply le_min (A * B).rank_le_height
      exact le_min ((Matrix.rank_mul_le_left A B).trans A.rank_le_width) (A * B).rank_le_width
    have hzero : (∏ i ∈ Finset.range k, singularValues (A * B) i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_of_not_ge hk))
      exact singularValues_eq_zero_of_rank_le _ hbound
    rw [hzero]
    exact Finset.prod_nonneg fun i _ => mul_nonneg (singularValues_nonneg A i) (singularValues_nonneg B i)

/-- Horn's prefix-product inequality for native singular values on arbitrary finite
real matrix indices. Horn–Johnson 1991, Theorem 3.3.4; every natural prefix,
empty types, rank deficient matrices, and all padded zeros are included.
atlas: horn-product-inequality (partial) -/
theorem prod_toEuclideanLin_singularValues_mul_le {m p n : Type*}
    [Fintype m] [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]
    (A : Matrix m p ℝ) (B : Matrix p n ℝ) (k : ℕ) :
    (∏ i ∈ Finset.range k, (A * B).toEuclideanLin.singularValues i) ≤
      ∏ i ∈ Finset.range k, A.toEuclideanLin.singularValues i * B.toEuclideanLin.singularValues i := by
  have h := prod_singularValues_mul_le
    (A.reindex (Fintype.equivFin m) (Fintype.equivFin p))
    (B.reindex (Fintype.equivFin p) (Fintype.equivFin n)) k
  have hAB : A.reindex (Fintype.equivFin m) (Fintype.equivFin p) *
      B.reindex (Fintype.equivFin p) (Fintype.equivFin n) =
      (A * B).reindex (Fintype.equivFin m) (Fintype.equivFin n) := by
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  rw [hAB] at h
  simpa only [singularValues_reindex_eq_toEuclideanLin_singularValues] using h

end NLAlib
