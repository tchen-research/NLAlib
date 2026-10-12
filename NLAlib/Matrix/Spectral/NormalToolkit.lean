import NLAlib.Matrix.Spectral.NormalSimilarity
import NLAlib.Matrix.Spectral.SchurFrobenius
import NLAlib.Matrix.Spectral.NormalBlocks
import NLAlib.Matrix.Spectral.NormalRectangularIntertwining
import NLAlib.Matrix.Spectral.RealNormalSpecializations
import NLAlib.Matrix.Spectral.SchurTriangularization
/-!
# The complex and real normal-matrix toolkit

Equivalent spectral descriptions, block reduction, unitary classification,
rectangular Fuglede–Putnam, and real scalar/rotation-dilation normal forms.
Source: Horn–Johnson (2013), §2.5.
-/

noncomputable section
open Polynomial
open scoped Matrix Matrix.Norms.Frobenius

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthonormal eigenbasis makes a complex matrix normal. Source:
Horn–Johnson (2013), Theorem 2.5.3; the change-of-basis matrix is unitary. -/
theorem normal_of_orthonormalBasis_eigenvectors
    (A : Matrix n n ℂ) (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (d : n → ℂ)
    (hb : ∀ j, A *ᵥ ⇑(b j) = d j • ⇑(b j)) : A * Aᴴ = Aᴴ * A := by
  let U : Matrix.unitaryGroup n ℂ :=
    ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hAU : A * (U : Matrix n n ℂ) = (U : Matrix n n ℂ) * Matrix.diagonal d := by
    ext i j
    have hcol : ∀ k, (U : Matrix n n ℂ) k j = (b j) k := fun _ => rfl
    rw [Matrix.mul_diagonal]
    have h := congrFun (hb j) i
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Matrix.mul_apply, hcol, mul_comm] using h
  have hUU : (U : Matrix n n ℂ) * (U : Matrix n n ℂ)ᴴ = 1 := Unitary.coe_mul_star_self U
  apply mul_conjTranspose_eq_conjTranspose_mul_of_unitary_diagonalization U d
  rw [← hAU, Matrix.mul_assoc, hUU, Matrix.mul_one]

/-- A complex matrix is normal exactly when it has an orthonormal eigenbasis.
Source: Horn–Johnson (2013), Theorem 2.5.3; empty dimensions are included.
atlas: normal-matrices (partial) -/
theorem normal_iff_exists_orthonormalBasis_eigenvectors (A : Matrix n n ℂ) :
    A * Aᴴ = Aᴴ * A ↔
      ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (d : n → ℂ),
        ∀ j, A *ᵥ ⇑(b j) = d j • ⇑(b j) :=
  ⟨exists_orthonormalBasis_eigenvectors_of_normal,
    fun ⟨b, d, hb⟩ => normal_of_orthonormalBasis_eigenvectors A b d hb⟩

/-- Equality of squared Frobenius mass with the squared magnitudes of any
complete characteristic-root list characterizes normality. Source:
Horn–Johnson (2013), Theorem 2.5.3; root order and multiplicities are explicit.
atlas: normal-matrices (partial) -/
theorem sum_norm_sq_characteristic_eq_iff_normal (A : Matrix n n ℂ) (d : n → ℂ)
    (hd : A.charpoly = ∏ i, (X - C (d i))) :
    (∑ i, ‖d i‖ ^ 2) = ‖A‖ ^ 2 ↔ A * Aᴴ = Aᴴ * A := by
  classical
  obtain ⟨U, T, hA, _, hchar⟩ := exists_unitary_schur_triangularization A (Fintype.equivFin n).symm
  have hsum := sum_norm_sq_eq_of_prod_X_sub_C_eq d (fun i => T i i) (hd.symm.trans hchar)
  rw [hsum]
  exact sum_norm_sq_schur_diagonal_eq_iff_normal U T hA hchar

/-- The full normal-matrix contract: unitary diagonalization, orthonormal
eigenbasis and Frobenius equality characterizations; block diagonal reduction;
unitary similarity classification by characteristic polynomial; rectangular
Fuglede–Putnam; real scalar/rotation-dilation forms and their skew-symmetric
and orthogonal specializations. Source: Horn–Johnson (2013), Theorems 2.5.3,
2.5.4, 2.5.8 and 2.5.15 and Lemma 2.5.2. All finite and empty shapes are allowed.
atlas: normal-matrices -/
theorem normal_matrix_properties
    {m : Type*} [Fintype m] [DecidableEq m]
    (A A₂ : Matrix n n ℂ) (B : Matrix m m ℂ) (Z : Matrix n m ℂ)
    (Ar : Matrix n n ℝ) (e : Fin (Fintype.card n) ≃ n) :
    (A * Aᴴ = Aᴴ * A ↔ ∃ (U : Matrix.unitaryGroup n ℂ) (d : n → ℂ),
      A = (U : Matrix n n ℂ) * Matrix.diagonal d * (U : Matrix n n ℂ)ᴴ) ∧
    (A * Aᴴ = Aᴴ * A ↔
      ∃ (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (d : n → ℂ),
        ∀ j, A *ᵥ ⇑(b j) = d j • ⇑(b j)) ∧
    (∀ d : n → ℂ, A.charpoly = ∏ i, (X - C (d i)) →
      ((∑ i, ‖d i‖ ^ 2) = ‖A‖ ^ 2 ↔ A * Aᴴ = Aᴴ * A)) ∧
    (Matrix.fromBlocks A Z 0 B * (Matrix.fromBlocks A Z 0 B)ᴴ =
      (Matrix.fromBlocks A Z 0 B)ᴴ * Matrix.fromBlocks A Z 0 B → Z = 0) ∧
    (A * Aᴴ = Aᴴ * A → A₂ * A₂ᴴ = A₂ᴴ * A₂ →
      ((∃ U : Matrix.unitaryGroup n ℂ, A = (U : Matrix n n ℂ) * A₂ * (U : Matrix n n ℂ)ᴴ) ↔
        A.charpoly = A₂.charpoly)) ∧
    (A * Aᴴ = Aᴴ * A → B * Bᴴ = Bᴴ * B →
      (A * Z = Z * B ↔ Aᴴ * Z = Z * Bᴴ)) ∧
    (Ar * Arᵀ = Arᵀ * Ar →
      ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ Ar = Q * T * Qᵀ ∧
        IsRealNormalForm (T.submatrix e e)) ∧
    (Arᵀ = -Ar → ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ Ar = Q * T * Qᵀ ∧
      IsRealNormalForm (T.submatrix e e) ∧ ∀ i, T i i = 0) ∧
    (HasOrthonormalCols Ar → ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ Ar = Q * T * Qᵀ ∧
      IsRealNormalForm (T.submatrix e e) ∧
      (∀ i, (∀ j, j ≠ i → T (e j) (e i) = 0) → T (e i) (e i) = -1 ∨ T (e i) (e i) = 1) ∧
      (∀ i j, j.val + 1 = i.val → T (e i) (e j) ≠ 0 →
        (T (e j) (e j)) ^ 2 + (T (e i) (e j)) ^ 2 = 1)) :=
  ⟨normal_iff_exists_unitary_diagonalization A,
    normal_iff_exists_orthonormalBasis_eigenvectors A,
    fun d hd => sum_norm_sq_characteristic_eq_iff_normal A d hd,
    eq_zero_of_normal_upper_fromBlocks,
    fun hA hC => exists_unitary_similarity_iff_charpoly_eq_of_normal hA hC,
    fun hA hB => mul_eq_mul_iff_conjTranspose_mul_eq_mul_conjTranspose_of_normal_rectangular hA hB,
    fun h => exists_orthogonal_real_normal_form Ar h e,
    fun h => exists_orthogonal_real_skew_normal_form Ar h e,
    fun h => exists_orthogonal_real_orthogonal_normal_form Ar h e⟩

end NLAlib
